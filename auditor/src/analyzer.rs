extern crate petgraph;

use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;

use petgraph::dot::{Config, Dot};
use petgraph::stable_graph::{EdgeIndex, EdgeReference, NodeIndex, StableDiGraph};
use petgraph::visit::EdgeRef;
use petgraph::Direction;

use crate::summaries::*;

pub struct AuditReport {
    pub audited: Vec<(String, String, SourceLocation)>,
    pub unaudited: Vec<(String, SourceLocation)>,
}

fn without_type_param<'a>(mono_name: &'a str) -> &'a str {
    &mono_name[..mono_name.find('<').unwrap()]
}

pub struct TaurusAnalyzer {
    marking_db: PersistentSummaryStore<MarkedItem>,
    calledge_db: PersistentSummaryStore<Vec<DepEdge>>,
}

pub type DepGraph = StableDiGraph<String, SourceLocation>;

impl TaurusAnalyzer {
    pub fn new(db_path: &Path) -> Self {
        Self {
            marking_db: PersistentSummaryStore::<MarkedItem>::new(&db_path.join("marking"))
                .expect("failed to access consistent storage"),
            calledge_db: PersistentSummaryStore::<Vec<DepEdge>>::new(&db_path.join("calledge"))
                .expect("failed to access consistent storage"),
        }
    }

    pub fn get_depgraph(&self) -> (DepGraph, HashSet<NodeIndex>) {
        let db_size = self.calledge_db.len();
        let mut ret = DepGraph::with_capacity(db_size, 2 * db_size);
        let mut nodeidx = HashMap::<String, NodeIndex>::new();

        let mut get_nodeidx = |graph: &mut DepGraph, weight: &String| match nodeidx.get(weight) {
            Some(idx) => *idx,
            None => {
                let idx = graph.add_node(weight.clone());
                nodeidx.insert(weight.clone(), idx);
                idx
            }
        };

        // construct the graph and record language items that should be pruned
        let mut lang_items = HashSet::<NodeIndex>::new();

        self.calledge_db.for_each(|(caller, call_edges)| {
            let caller_idx = get_nodeidx(&mut ret, &caller);
            for call_edge in call_edges {
                let callee_idx = get_nodeidx(&mut ret, &call_edge.full_callee_name());
                ret.add_edge(caller_idx, callee_idx, call_edge.src_loc);
                if call_edge.is_lang_item {
                    lang_items.insert(caller_idx);
                }
            }
        });

        // prune edges (and dangling nodes) reached from language items using bfs
        let mut edges_to_prune = HashSet::<EdgeIndex>::new();
        let mut worklist: Vec<NodeIndex> = lang_items.iter().map(|x| *x).collect();
        let mut nodes_to_prune = lang_items;

        while worklist.len() > 0 {
            let mut nodes_to_inspect = HashSet::<NodeIndex>::new();
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

        let entry_points = ret
            .node_indices()
            .filter(|&node_idx| {
                let key = &ret.node_weight(node_idx).unwrap();
                if let Some(MarkedItem {
                    mark: Marking::EntryPoint,
                    ..
                }) = &self.marking_db.get(&key)
                {
                    true
                } else {
                    false
                }
            })
            .collect();

        (ret, entry_points)
    }

    pub fn audit(&self) -> AuditReport {
        let mut report = AuditReport {
            audited: Vec::new(),
            unaudited: Vec::new(),
        };

        let (dg, entry_points) = self.get_depgraph();

        let mut auditor = HashMap::new();
        let mut visited = HashSet::new();

        for entry in entry_points {
            for edge in dg.edges(entry) {
                if !visited.contains(&edge.id()) {
                    visited.insert(edge.id());
                    traverse(
                        &dg,
                        &self.marking_db,
                        edge,
                        &mut auditor,
                        &mut visited,
                        &mut report,
                    );
                }
            }
        }

        fn traverse<'a>(
            dg: &'a DepGraph,
            marking_db: &PersistentSummaryStore<MarkedItem>,
            current: EdgeReference<'a, SourceLocation>,
            auditor: &mut HashMap<String, NodeIndex>,
            visited: &mut HashSet<EdgeIndex>,
            report: &mut AuditReport,
        ) {
            let dep_edge = current.weight();
            let parent = current.source();
            let dependent = current.target();

            let parent_name = dg.node_weight(parent).unwrap();
            let dependent_name = dg.node_weight(dependent).unwrap();
            let original_auditor =
                if let Some(marked_item) = marking_db.get(without_type_param(parent_name)) {
                    match &marked_item.mark {
                        Marking::Audited(meta) => {
                            Some((meta.to_string(), auditor.insert(meta.to_string(), parent)))
                        }
                        _ => None,
                    }
                } else {
                    None
                };

            let mut skip_children = false;

            if let Some(marked_item) = marking_db.get(without_type_param(dependent_name)) {
                match &marked_item.mark {
                    Marking::RequireAudit(meta) => {
                        if let Some(&auditor_idx) = auditor.get(meta) {
                            report.audited.push((
                                dg.node_weight(auditor_idx).unwrap().to_string(),
                                dependent_name.to_string(),
                                dep_edge.clone(),
                            ));
                        } else {
                            report
                                .unaudited
                                .push((dependent_name.to_string(), dep_edge.clone()));
                            skip_children = true;
                        }
                    }
                    _ => (),
                }
            }

            if !skip_children {
                for edge in dg.edges(dependent) {
                    if !visited.contains(&edge.id()) {
                        visited.insert(edge.id());
                        traverse(dg, marking_db, edge, auditor, visited, report);
                    }
                }
            }

            if let Some((meta, auditor_node_opt)) = original_auditor {
                if let Some(auditor_node) = auditor_node_opt {
                    auditor.insert(meta, auditor_node);
                } else {
                    auditor.remove(&meta);
                }
            }
        }

        report
    }

    pub fn get_depgraph_dot(&self) -> String {
        let dg = self.get_depgraph().0;
        format!("{:?}", Dot::with_config(&dg, &[Config::EdgeNoLabel]))
    }
}
