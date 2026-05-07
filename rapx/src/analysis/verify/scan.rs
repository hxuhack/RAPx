use crate::analysis::Analysis;
use crate::analysis::senryx::contract::PropertyContract;
use crate::analysis::utils::fn_info::{
    ContractEntry, generate_contract_from_contract_entries,
    generate_requires_from_annotation_without_field_types, get_cleaned_def_path_name,
    get_unsafe_callees,
};
use rustc_hir::{
    BodyId, FnDecl,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor, walk_fn},
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::{Span, Symbol};
use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

pub type RequiresContracts<'tcx> = Vec<(usize, Vec<usize>, PropertyContract<'tcx>)>;
pub type CalleeRequiresMap<'tcx> = HashMap<DefId, RequiresContracts<'tcx>>;

/// Visitor that collects all functions annotated with `#[rapx::verify]`.
pub struct VerifyAttrVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    pub targets: Vec<DefId>,
    pub unsafe_callees: HashMap<DefId, HashSet<DefId>>,
    pub callee_requires: HashMap<DefId, CalleeRequiresMap<'tcx>>,
}

impl<'tcx> VerifyAttrVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        VerifyAttrVisitor {
            tcx,
            targets: Vec::new(),
            unsafe_callees: HashMap::new(),
            callee_requires: HashMap::new(),
        }
    }

    fn is_std_crate_def_id(&self, def_id: DefId) -> bool {
        matches!(
            self.tcx.crate_name(def_id.krate).as_str(),
            "core" | "std" | "alloc"
        )
    }

    fn get_requires_for_unsafe_callee(&self, callee_def_id: DefId) -> RequiresContracts<'tcx> {
        let mut requires =
            generate_requires_from_annotation_without_field_types(self.tcx, callee_def_id);
        if requires.is_empty() && self.is_std_crate_def_id(callee_def_id) {
            requires = generate_contract_from_contract_entries(
                self.tcx,
                callee_def_id,
                get_std_backup_contracts(self.tcx, callee_def_id),
            );
        }
        requires
    }

    fn has_rapx_verify_attr(&self, def_id: LocalDefId) -> bool {
        let hir_id = self.tcx.local_def_id_to_hir_id(def_id);

        let rapx = Symbol::intern("rapx");
        let verify = Symbol::intern("verify");

        let attrs = self.tcx.hir_attrs(hir_id);

        attrs.iter().any(|attr| {
            if attr.is_doc_comment().is_some() {
                return false;
            }

            let path = attr.path(); // SmallVec<Symbol>

            path.len() == 2 && path[0] == rapx && path[1] == verify
        })
    }
}

impl<'tcx> Visitor<'tcx> for VerifyAttrVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_fn(
        &mut self,
        fk: FnKind<'tcx>,
        fd: &'tcx FnDecl<'tcx>,
        b: BodyId,
        _span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        if self.has_rapx_verify_attr(id) {
            let def_id = id.to_def_id();
            let path = self.tcx.def_path_str(def_id);
            let unsafe_callees = get_unsafe_callees(self.tcx, def_id);
            let callee_requires = unsafe_callees
                .iter()
                .map(|callee_def_id| {
                    (
                        *callee_def_id,
                        self.get_requires_for_unsafe_callee(*callee_def_id),
                    )
                })
                .collect();
            rap_info!("[rapx::verify] found: {} (DefId: {:?})", path, def_id);
            rap_debug!(
                "[rapx::verify] unsafe callees of {:?}: {:?}",
                def_id,
                unsafe_callees
            );
            self.unsafe_callees.insert(def_id, unsafe_callees);
            self.callee_requires.insert(def_id, callee_requires);
            self.targets.push(def_id);
        }
        walk_fn(self, fk, fd, b, id);
    }
}

/// Scan Analysis - find all functions annotated with #[rapx::verify]
pub struct VerifyTargetsScanner<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Analysis for VerifyTargetsScanner<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Scan Analysis"
    }

    fn run(&mut self) {
        rap_info!("======== #[rapx::verify] scan ========");
        let mut visitor = VerifyAttrVisitor::new(self.tcx);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut visitor);
        rap_debug!(
            "[rapx::verify] target -> unsafe_callees: {:?}",
            visitor.unsafe_callees
        );
        rap_debug!(
            "[rapx::verify] target -> callee_requires: {:?}",
            visitor.callee_requires
        );
        rap_info!(
            "total: {} function(s) annotated with #[rapx::verify]",
            visitor.targets.len()
        );
        rap_info!("=====================================");
    }

    fn reset(&mut self) {}
}

impl<'tcx> VerifyTargetsScanner<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        VerifyTargetsScanner { tcx }
    }
}

fn get_verify_std_contracts_json() -> &'static HashMap<String, Vec<ContractEntry>> {
    static STD_CONTRACTS: OnceLock<HashMap<String, Vec<ContractEntry>>> = OnceLock::new();
    STD_CONTRACTS.get_or_init(|| {
        let raw = include_str!("assets/std-contracts.json");
        let normalized = normalize_json_trailing_commas(raw);
        serde_json::from_str(normalized.as_str())
            .expect("failed to parse verify std contracts backup")
    })
}

fn get_std_backup_contracts(tcx: TyCtxt<'_>, def_id: DefId) -> &'static [ContractEntry] {
    let cleaned_path_name = get_cleaned_def_path_name(tcx, def_id);
    get_verify_std_contracts_json()
        .get(&cleaned_path_name)
        .map(Vec::as_slice)
        .unwrap_or(&[])
}

fn normalize_json_trailing_commas(input: &str) -> String {
    let chars = input.chars().collect::<Vec<_>>();
    let mut normalized = String::with_capacity(input.len());
    let mut i = 0;

    while i < chars.len() {
        let ch = chars[i];
        if ch == ',' {
            let mut j = i + 1;
            while j < chars.len() && chars[j].is_whitespace() {
                j += 1;
            }
            if j < chars.len() && (chars[j] == '}' || chars[j] == ']') {
                i += 1;
                continue;
            }
        }
        normalized.push(ch);
        i += 1;
    }

    normalized
}

#[cfg(test)]
mod tests {
    use super::{get_verify_std_contracts_json, normalize_json_trailing_commas};

    #[test]
    fn std_contracts_backup_contains_core_ptr_read() {
        let std_contracts = get_verify_std_contracts_json();
        assert!(std_contracts.contains_key("core::ptr::read"));
    }

    #[test]
    fn normalize_json_trailing_commas_works() {
        let normalized = normalize_json_trailing_commas("{\"k\":[1,2,],}");
        let parsed: serde_json::Value = serde_json::from_str(normalized.as_str()).unwrap();
        assert_eq!(parsed["k"], serde_json::json!([1, 2]));
    }
}
