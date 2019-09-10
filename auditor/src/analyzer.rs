extern crate petgraph;

use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;

use petgraph::dot::{Config, Dot};
use petgraph::stable_graph::{DefaultIx, EdgeIndex, NodeIndex, StableGraph};
use petgraph::{Directed, Direction};

use crate::summaries::*;

pub struct TaurusAnalyzer {
    marking_db: PersistentSummaryStore<SourceLocation>,
    calledge_db: PersistentSummaryStore<Vec<CallEdge>>,
}

pub type DepGraph = StableGraph<String, (), Directed, DefaultIx>;

impl TaurusAnalyzer {
    pub fn new(db_path: &Path) -> Self {
        Self {
            marking_db: PersistentSummaryStore::<SourceLocation>::new(&db_path.join("marking"))
                .expect("failed to access consistent storage"),
            calledge_db: PersistentSummaryStore::<Vec<CallEdge>>::new(&db_path.join("calledge"))
                .expect("failed to access consistent storage"),
        }
    }

    pub fn get_depgraph(&self) -> DepGraph {
        let mut ret = DepGraph::new();
        let mut nodeidx = HashMap::<String, NodeIndex<DefaultIx>>::new();

        let mut get_nodeidx = |graph: &mut DepGraph, weight: &String| match nodeidx.get(weight) {
            Some(idx) => *idx,
            None => {
                let idx = graph.add_node(weight.clone());
                nodeidx.insert(weight.clone(), idx);
                idx
            }
        };

        // construct the graph and record language items that should be pruned
        let mut lang_items = HashSet::<NodeIndex<DefaultIx>>::new();

        self.calledge_db.for_each(|(caller, call_edges)| {
            let caller_idx = get_nodeidx(&mut ret, &caller);
            for call_edge in call_edges {
                let callee_idx = get_nodeidx(&mut ret, &call_edge.callee_name);
                ret.add_edge(caller_idx, callee_idx, ());
                if call_edge.is_lang_item {
                    lang_items.insert(caller_idx);
                }
            }
        });

        // prune edges (and dangling nodes) reached from language items using bfs
        let mut edges_to_prune = HashSet::<EdgeIndex<DefaultIx>>::new();
        let mut worklist: Vec<NodeIndex<DefaultIx>> = lang_items.iter().map(|x| *x).collect();
        let mut nodes_to_prune = lang_items;

        while worklist.len() > 0 {
            use petgraph::visit::EdgeRef;

            let mut nodes_to_inspect = HashSet::<NodeIndex<DefaultIx>>::new();
            for node in &worklist {
                for out_edge in ret.edges(*node) {
                    nodes_to_inspect.insert(out_edge.target());
                    edges_to_prune.insert(out_edge.id());
                }
            }
            worklist.clear();
            for prune_candidate in nodes_to_inspect {
                if ret
                    .edges_directed(prune_candidate, Direction::Incoming)
                    .all(|edge_ref| edges_to_prune.contains(&edge_ref.id()))
                {
                    if nodes_to_prune.insert(prune_candidate) {
                        worklist.push(prune_candidate);
                    }
                }
            }
        }

        for edge in edges_to_prune {
            ret.remove_edge(edge);
        }

        for node in nodes_to_prune {
            ret.remove_node(node);
        }

        ret
    }

    pub fn get_depgraph_dot(&self) -> String {
        let dg = self.get_depgraph();
        format!("{:?}", Dot::with_config(&dg, &[Config::EdgeNoLabel]))
    }
}
