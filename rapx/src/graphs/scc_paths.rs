//! Shared SCC-tree and SCC-path utilities.
//!
//! These helpers are graph-only building blocks: they do not encode
//! alias-analysis- or verification-specific state semantics.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use super::scc::{Scc, SccInfo, SccTree};

/// Stable key for deduplicating path + path-constraint combinations.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct PathKey {
    pub path: Vec<usize>,
    pub constraints: Vec<(usize, usize)>,
}

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
/// `node_to_scc` should return the **most specific/direct SCC owner** for `node`
/// under the current nesting model.
///
/// In other words, for a node that belongs to nested SCCs, return the SCC metadata
/// of the innermost SCC that currently contains that node. This allows this helper
/// to reconstruct nested SCC trees by repeatedly mapping each node to its direct
/// child SCC owner and recursing.
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

/// Convert unordered path constraints into a stable, hashable key.
pub fn constraints_key(constraints: &FxHashMap<usize, usize>) -> Vec<(usize, usize)> {
    let mut sorted_constraints: Vec<(usize, usize)> =
        constraints.iter().map(|(k, val)| (*k, *val)).collect();
    sorted_constraints.sort_unstable();
    sorted_constraints
}

/// Build a dedup key from a path and its associated constraints.
pub fn make_path_key(path: &[usize], constraints: &FxHashMap<usize, usize>) -> PathKey {
    PathKey {
        path: path.to_vec(),
        constraints: constraints_key(constraints),
    }
}

/// Insert `(path, constraints)` into `out` only if this combination is new.
pub fn record_unique_path(
    path: &[usize],
    constraints: &FxHashMap<usize, usize>,
    out: &mut Vec<(Vec<usize>, FxHashMap<usize, usize>)>,
    seen_paths: &mut FxHashSet<PathKey>,
) {
    let key = make_path_key(path, constraints);
    if seen_paths.insert(key) {
        out.push((path.to_vec(), constraints.clone()));
    }
}

/// Return true when `node` belongs to the SCC currently being enumerated.
pub fn node_is_in_current_scc(start: usize, scc: &SccInfo, node: usize) -> bool {
    node == start || scc.nodes.contains(&node)
}

/// Rebuild the per-segment recursion stack from the suffix after the latest
/// dominator (`start`) occurrence in `path`.
pub fn rebuild_segment_stack(path: &[usize], start: usize) -> FxHashSet<usize> {
    // `path` is expected to begin with `start` in our SCC DFS. If a caller provides
    // an unexpected path without `start`, we conservatively fall back to the full path.
    let last_start_pos = path.iter().rposition(|&node| node == start).unwrap_or(0);
    let mut segment_stack = FxHashSet::default();
    for node in &path[last_start_pos..] {
        segment_stack.insert(*node);
    }
    segment_stack
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constraints_key_is_stable() {
        let mut constraints = FxHashMap::default();
        constraints.insert(5, 2);
        constraints.insert(1, 7);

        assert_eq!(constraints_key(&constraints), vec![(1, 7), (5, 2)]);
    }

    #[test]
    fn record_unique_path_deduplicates() {
        let constraints = FxHashMap::default();
        let mut out = Vec::new();
        let mut seen = FxHashSet::default();

        record_unique_path(&[1, 2, 3], &constraints, &mut out, &mut seen);
        record_unique_path(&[1, 2, 3], &constraints, &mut out, &mut seen);

        assert_eq!(out.len(), 1);
        assert_eq!(out[0].0, vec![1, 2, 3]);
    }
}
