extern crate petgraph;

use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;

use petgraph::dot::{Config, Dot};
use petgraph::stable_graph::{EdgeIndex, EdgeReference, NodeIndex, StableDiGraph};
use petgraph::visit::EdgeRef;
use petgraph::Direction;

use rustc_errors::emitter::{ColorConfig, Emitter, EmitterWriter};
use rustc_errors::{Diagnostic, Level};

use crate::summaries::*;

pub type DepGraph = StableDiGraph<String, SourceLocation>;

pub type ProgPoint = (String, SourceLocation);

pub struct DepPath {
    path: Vec<ProgPoint>,
}

impl DepPath {
    fn instantiate<'a>(
        abstract_path: &[EdgeReference<'a, SourceLocation>],
        dg: &'a DepGraph,
    ) -> Self {
        DepPath {
            path: abstract_path
                .iter()
                .map(|seg| {
                    let dependent = seg.target();
                    let dependent_name = dg.node_weight(dependent).unwrap();

                    (dependent_name.to_string(), seg.weight().clone())
                })
                .collect(),
        }
    }
}

impl std::fmt::Display for DepPath {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for pp in &self.path {
            write!(f, "-> {} at {}\n", pp.0, pp.1)?;
        }

        Ok(())
    }
}

pub struct AuditReport {
    pub audited: Vec<(String, DepPath)>,
    pub unaudited: Vec<DepPath>,
}

impl AuditReport {
    pub fn emit(&self) {
        let mut writer = EmitterWriter::stderr(ColorConfig::Auto, None, false, false, None, false);

        for to_warn in &self.unaudited {
            writer.emit_diagnostic(&Diagnostic::new(
                Level::Warning,
                &format!("Unaudited use of insecure functions:\n{}", to_warn),
            ));
        }

        for to_note in &self.audited {
            writer.emit_diagnostic(&Diagnostic::new(
                Level::Note,
                &format!(
                    "Audited use of insecure functions:\n   {}\n{}",
                    to_note.0, to_note.1
                ),
            ));
        }
    }
}

fn without_type_param<'a>(mono_name: &'a str) -> &'a str {
    &mono_name[..mono_name.find('<').unwrap()]
}

pub struct TaurusAnalyzer {
    marking_db: PersistentSummaryStore<MarkedItem>,
    calledge_db: PersistentSummaryStore<Vec<DepEdge>>,
}

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

        let entry_points: HashSet<NodeIndex> = ret
            .node_indices()
            .filter(|&node_idx| {
                let key = &ret.node_weight(node_idx).unwrap();
                self.marking_db
                    .get(without_type_param(&key))
                    .and_then(|marked_item| {
                        if marked_item.marking.is_entry_point {
                            Some(())
                        } else {
                            None
                        }
                    })
                    .is_some()
            })
            .collect();

        debug!("found {} entry points", entry_points.len());

        (ret, entry_points)
    }

    pub fn audit(&self) -> AuditReport {
        let mut report = AuditReport {
            audited: Vec::new(),
            unaudited: Vec::new(),
        };

        let (dg, entry_points) = self.get_depgraph();

        let mut auditor = HashMap::new();

        for entry in entry_points {
            debug!(
                "start traversal from entry point {}",
                dg.node_weight(entry).unwrap()
            );

            let mut visited = HashSet::new();
            for edge in dg.edges(entry) {
                let mut path = vec![edge];
                traverse(
                    &dg,
                    &self.marking_db,
                    edge,
                    &mut auditor,
                    &mut path,
                    &mut visited,
                    &mut report,
                );
            }
        }

        fn traverse<'a>(
            dg: &'a DepGraph,
            marking_db: &PersistentSummaryStore<MarkedItem>,
            current: EdgeReference<'a, SourceLocation>,
            auditor: &mut HashMap<String, NodeIndex>,
            path: &mut Vec<EdgeReference<'a, SourceLocation>>,
            visited: &mut HashSet<EdgeIndex>,
            report: &mut AuditReport,
        ) {
            let parent = current.source();
            let dependent = current.target();

            let parent_name = dg.node_weight(parent).unwrap();
            let dependent_name = dg.node_weight(dependent).unwrap();

            let original_auditor =
                marking_db
                    .get(without_type_param(parent_name))
                    .and_then(|marked_item| {
                        marked_item.marking.audited.map(|meta| {
                            (meta.to_string(), auditor.insert(meta.to_string(), parent))
                        })
                    });

            let mut skip_children = false;

            if let Some(marked_item) = marking_db.get(without_type_param(dependent_name)) {
                if let Some(meta) = &marked_item.marking.require_audit {
                    let dep_path = DepPath::instantiate(&path, dg);
                    if let Some(&auditor_idx) = auditor.get(meta) {
                        report
                            .audited
                            .push((dg.node_weight(auditor_idx).unwrap().to_string(), dep_path));
                    } else {
                        report.unaudited.push(dep_path);
                        skip_children = true;
                    }
                }
            }

            if !skip_children {
                for edge in dg.edges(dependent) {
                    if !visited.contains(&edge.id()) {
                        visited.insert(edge.id());
                        path.push(edge);
                        traverse(dg, marking_db, edge, auditor, path, visited, report);
                        path.pop();
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
