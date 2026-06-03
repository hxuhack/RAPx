//! Shared SCC-tree and SCC-path utilities.
//!
//! These helpers are graph-only building blocks: they do not encode
//! alias-analysis- or verification-specific state semantics.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use super::scc::{Scc, SccInfo, SccTree};

/// Collect all SCC components from a successor graph.
///
/// Each node is represented by its `usize` index and each edge by an index in
/// the corresponding successor list.
pub fn collect_scc_components(successors: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut collector = SccComponentCollector::new(successors.to_vec());
    collector.find_scc();
    collector.components
}

/// Build an SCC tree rooted at `scc` by repeatedly querying per-node SCC info.
///
/// `node_to_scc` should return the SCC that owns `node`.
pub fn build_scc_tree<F>(scc: &SccInfo, mut node_to_scc: F) -> SccTree
where
    F: FnMut(usize) -> Option<SccInfo>,
{
    build_scc_tree_inner(scc, &mut node_to_scc)
}

fn build_scc_tree_inner<F>(scc: &SccInfo, node_to_scc: &mut F) -> SccTree
where
    F: FnMut(usize) -> Option<SccInfo>,
{
    let mut child_sccs: FxHashMap<usize, SccInfo> = FxHashMap::default();

    for &node in scc.nodes.iter() {
        let Some(node_scc) = node_to_scc(node) else {
            continue;
        };

        if node_scc.enter != scc.enter && !node_scc.nodes.is_empty() {
            child_sccs.entry(node_scc.enter).or_insert(node_scc);
        }
    }

    let children = child_sccs
        .into_values()
        .map(|child_scc| build_scc_tree_inner(&child_scc, node_to_scc))
        .collect();

    SccTree {
        scc: scc.clone(),
        children,
    }
}

struct SccComponentCollector {
    successors: Vec<Vec<usize>>,
    components: Vec<Vec<usize>>,
}

impl SccComponentCollector {
    fn new(successors: Vec<Vec<usize>>) -> Self {
        Self {
            successors,
            components: Vec::new(),
        }
    }
}

impl Scc for SccComponentCollector {
    fn on_scc_found(&mut self, _root: usize, scc_components: &[usize]) {
        self.components.push(scc_components.to_vec());
    }

    fn get_next(&mut self, root: usize) -> FxHashSet<usize> {
        self.successors
            .get(root)
            .into_iter()
            .flat_map(|successors| successors.iter().copied())
            .collect()
    }

    fn get_size(&mut self) -> usize {
        self.successors.len()
    }
}
