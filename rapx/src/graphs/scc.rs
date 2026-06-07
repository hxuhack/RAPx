//! Shared strongly-connected-component utilities.
//!
//! This module provides the small Tarjan SCC abstraction used by RAP analyses
//! and by the verification path extractor. The trait is intentionally graph
//! agnostic: clients provide successor queries and receive each discovered SCC
//! through `on_scc_found`.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use std::cmp;

/// An outgoing edge from an SCC body to a block outside the SCC.
#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct SccExit {
    pub exit: usize,
    pub to: usize,
}

impl SccExit {
    /// Create an SCC exit edge from `exit` to `to`.
    pub fn new(exit: usize, to: usize) -> Self {
        SccExit { exit, to }
    }
}

/// Per-header SCC metadata used by loop-aware analyses.
#[derive(Debug, Clone)]
pub struct SccInfo {
    /// Representative entry block of the SCC.
    pub enter: usize,
    /// Other blocks in the SCC, excluding `enter`.
    pub nodes: FxHashSet<usize>,
    /// Edges leaving the SCC.
    pub exits: FxHashSet<SccExit>,
    /// Blocks with back edges to the SCC representative.
    pub backnodes: FxHashSet<usize>,
    /// Representative `enter` nodes of nested child SCCs.
    pub child_sccs: Vec<usize>,
}

impl SccInfo {
    /// Create empty SCC metadata for `enter`.
    pub fn new(enter: usize) -> Self {
        SccInfo {
            enter,
            nodes: FxHashSet::default(),
            exits: FxHashSet::default(),
            backnodes: FxHashSet::default(),
            child_sccs: Vec::new(),
        }
    }

    /// Returns `true` when this SCC contains only its entry block (no member nodes).
    ///
    /// A trivial SCC has no loops and requires no special path enumeration.
    pub fn is_trivial(&self) -> bool {
        self.nodes.is_empty()
    }
}

/// SCC region metadata summarized from a plain successor graph.
#[derive(Debug, Clone)]
pub struct SccRegionSummary {
    /// Stable SCC representative (smallest node id in this SCC).
    pub representative: usize,
    /// All nodes inside the SCC, including `representative`.
    pub blocks: Vec<usize>,
    /// Edges leaving this SCC.
    pub exits: Vec<SccExit>,
    /// Internal edges considered as loop backedges.
    pub backedges: Vec<(usize, usize)>,
}

/// Reusable SCC analysis result for modules that only have successor lists.
#[derive(Debug, Clone, Default)]
pub struct SccAnalysis {
    /// Non-trivial SCC regions (multi-node SCCs or self-loop SCCs).
    pub regions: Vec<SccRegionSummary>,
    /// Map each SCC member node to its SCC representative.
    pub node_to_representative: FxHashMap<usize, usize>,
}

/// Analyze non-trivial SCC regions from a plain successor graph.
///
/// This keeps SCC region metadata in the shared graph layer so downstream
/// analyses (for example verification path extraction) can reuse it directly.
pub fn analyze_scc_regions(successors: &[Vec<usize>]) -> SccAnalysis {
    let components = collect_scc_components(successors);
    let mut regions = Vec::new();
    let mut node_to_representative = FxHashMap::default();

    for mut component in components {
        component.sort_unstable();
        let has_self_edge = component.len() == 1
            && successors[component[0]]
                .iter()
                .any(|&succ| succ == component[0]);
        if component.len() <= 1 && !has_self_edge {
            continue;
        }

        let representative = component[0];
        let block_set: FxHashSet<usize> = component.iter().copied().collect();
        let mut exits = Vec::new();
        let mut backedges = Vec::new();

        for &block in &component {
            for &succ in &successors[block] {
                if block_set.contains(&succ) {
                    if succ <= block || succ == representative {
                        backedges.push((block, succ));
                    }
                } else {
                    exits.push(SccExit::new(block, succ));
                }
            }
        }

        for &block in &component {
            node_to_representative.insert(block, representative);
        }

        regions.push(SccRegionSummary {
            representative,
            blocks: component,
            exits,
            backedges,
        });
    }

    SccAnalysis {
        regions,
        node_to_representative,
    }
}

/// Tarjan SCC callback trait.
pub trait Scc {
    /// Run SCC discovery from CFG entry block 0.
    fn find_scc(&mut self) {
        if self.get_size() == 0 {
            return;
        }
        self.find_scc_from(0);
    }

    /// Run SCC discovery from a specific start node.
    fn find_scc_from(&mut self, start: usize) {
        if start >= self.get_size() {
            return;
        }
        let mut stack = Vec::new();
        let mut instack = FxHashSet::<usize>::default();
        let mut dfn = vec![0; self.get_size()];
        let mut low = vec![0; self.get_size()];
        let mut time = 1;
        self.tarjan(
            start,
            &mut stack,
            &mut instack,
            &mut dfn,
            &mut low,
            &mut time,
        );
    }

    /// Callback invoked for each discovered SCC.
    fn on_scc_found(&mut self, root: usize, scc_components: &[usize]);

    /// Return outgoing successors of `root`.
    fn get_next(&mut self, root: usize) -> FxHashSet<usize>;

    /// Return the number of graph nodes.
    fn get_size(&mut self) -> usize;

    /// Recursive Tarjan traversal.
    fn tarjan(
        &mut self,
        index: usize,
        stack: &mut Vec<usize>,
        instack: &mut FxHashSet<usize>,
        dfn: &mut Vec<usize>,
        low: &mut Vec<usize>,
        time: &mut usize,
    ) {
        dfn[index] = *time;
        low[index] = *time;
        *time += 1;
        stack.push(index);
        instack.insert(index);

        let size = self.get_size();
        let nexts = self.get_next(index);
        for next in nexts {
            if next >= size {
                continue;
            }
            if dfn[next] == 0 {
                self.tarjan(next, stack, instack, dfn, low, time);
                low[index] = cmp::min(low[index], low[next]);
            } else if instack.contains(&next) {
                low[index] = cmp::min(low[index], dfn[next]);
            }
        }

        if dfn[index] == low[index] {
            let mut component = vec![index];
            while let Some(top) = stack.pop() {
                instack.remove(&top);
                if top == index {
                    break;
                }
                component.push(top);
            }
            self.on_scc_found(index, &component);
        }
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

fn collect_scc_components(successors: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut collector = SccComponentCollector::new(successors.to_vec());
    collector.find_scc();
    collector.components
}

#[cfg(test)]
mod tests {
    use super::{SccExit, analyze_scc_regions};

    #[test]
    fn analyze_scc_regions_collects_non_trivial_scc_metadata() {
        let successors = vec![vec![1], vec![2], vec![1, 3], vec![]];
        let analysis = analyze_scc_regions(&successors);

        assert_eq!(analysis.regions.len(), 1);
        let region = &analysis.regions[0];
        assert_eq!(region.representative, 1);
        assert_eq!(region.blocks, vec![1, 2]);
        assert_eq!(region.exits, vec![SccExit::new(2, 3)]);
        assert_eq!(region.backedges, vec![(2, 1)]);
        assert_eq!(analysis.node_to_representative.get(&1), Some(&1));
        assert_eq!(analysis.node_to_representative.get(&2), Some(&1));
    }

    #[test]
    fn analyze_scc_regions_keeps_self_loop_scc() {
        let successors = vec![vec![0]];
        let analysis = analyze_scc_regions(&successors);

        assert_eq!(analysis.regions.len(), 1);
        let region = &analysis.regions[0];
        assert_eq!(region.representative, 0);
        assert_eq!(region.blocks, vec![0]);
        assert!(region.exits.is_empty());
        assert_eq!(region.backedges, vec![(0, 0)]);
        assert_eq!(analysis.node_to_representative.get(&0), Some(&0));
    }
}
