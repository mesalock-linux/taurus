extern crate seahash;

use rustc::hir::def_id::DefId;
use rustc::mir::mono::MonoItem;
use rustc::mir::TerminatorKind;
use rustc::ty::{Instance, InstanceDef, ParamEnv, TyCtxt, TyKind};
use rustc_interface::interface;
use rustc_mir::monomorphize::collector::{collect_crate_mono_items, MonoItemCollectionMode};

use std::collections::HashSet;
use std::path::PathBuf;

use crate::annotated::*;
use crate::summaries::*;

pub struct TaurusExtractor {
    file_name: String,
    output_dir: PathBuf,
    lang_items: HashSet<DefId>,
}

impl Default for TaurusExtractor {
    fn default() -> Self {
        Self {
            file_name: String::new(),
            output_dir: PathBuf::default(),
            lang_items: HashSet::new(),
        }
    }
}

impl rustc_driver::Callbacks for TaurusExtractor {
    /// Called before creating the compiler instance
    fn config(&mut self, config: &mut interface::Config) {
        config.crate_cfg.insert(("taurus".to_string(), None));
        self.file_name = config.input.source_name().to_string();
        match &config.output_dir {
            None => {
                self.output_dir = std::env::temp_dir();
                self.output_dir.pop();
            }
            Some(path_buf) => self.output_dir.push(path_buf.as_path()),
        };
    }

    /// Called after the compiler has completed all analysis passes and before
    /// it lowers MIR to LLVM IR. At this stage, generics have been instantiated
    /// and we should have everything we need for the audit analysis
    fn after_analysis(&mut self, compiler: &interface::Compiler) -> bool {
        // if !compiler.session().rust_2018() {
        //     compiler.session().fatal("taurus can only audit Rust 2018 projects");
        // }

        compiler.session().abort_if_errors();

        if self.output_dir.to_str().unwrap().contains("/build/") {
            // Build scripts do not need to be audited
            return true;
        }
        // We don't want to analyze our own stuff
        if self.file_name.contains("/taurus/annotation")
            || self.file_name.contains("/taurus/attributes")
        {
            return true;
        }
        info!("Processing input file: {}", self.file_name);
        compiler.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let lang_items = tcx.lang_items();
            for maybe_li in &lang_items.items {
                if let Some(li) = maybe_li {
                    self.lang_items.insert(*li);
                }
            }
            self.audit_analyze(compiler, tcx)
        });
        true // return true such that rustc can continue to emit LLVM bitcode
    }
}

impl TaurusExtractor {
    fn collect_call_edges<'tcx>(
        &mut self,
        canonical: &Canonical<'_, 'tcx, 'tcx, '_>,
        mono_instance: &Instance<'tcx>,
    ) -> (String, Vec<CallEdge>) {
        let tcx = canonical.tcx();
        let src_map = canonical.source_map();

        let mut call_edges: Vec<CallEdge> = Vec::new();
        let is_lang_item = self.lang_items.contains(&mono_instance.def_id()) || {
            if let Some(hir_id) = tcx.hir().as_local_hir_id(mono_instance.def_id()) {
                let parent_did = tcx.hir().get_parent_did_by_hir_id(hir_id);
                self.lang_items.contains(&parent_did)
            } else {
                // Not sure if the default case is correct. If we encounter something
                // that is non-local, there is something wrong. But should we just
                // assume it is related to built-in language items?
                true
            }
        };

        let mir = tcx.instance_mir(mono_instance.def);
        for bbd in mir.basic_blocks() {
            let term = bbd.terminator();
            if let TerminatorKind::Call { func, .. } = &term.kind {
                let callee_ty = func.ty(mir, *tcx);
                let callee_ty = tcx.subst_and_normalize_erasing_regions(
                    mono_instance.substs,
                    ParamEnv::reveal_all(),
                    &callee_ty,
                );
                let loc = src_map.lookup_char_pos(term.source_info.span.lo());

                if let TyKind::FnDef(callee_def_id, substs) = callee_ty.sty {
                    let callee_inst =
                        Instance::resolve(*tcx, ParamEnv::reveal_all(), callee_def_id, substs)
                            .unwrap();

                    let type_params: Vec<String> = substs
                        .into_iter()
                        .map(|ty| canonical.monoitem_name(ty))
                        .collect();

                    let val = CallEdge {
                        callee_name: canonical.monoitem_name(&callee_inst),
                        callee_def: canonical.def_name(callee_inst.def_id()),
                        is_lang_item,
                        type_params,
                        src_loc: (&loc).into(),
                    };

                    debug!(
                        "callgraph edge: {} -> {:#?}",
                        canonical.monoitem_name(mono_instance),
                        val,
                    );

                    call_edges.push(val);
                } else if let TyKind::FnPtr(..) = callee_ty.sty {
                    // An indirect call is encountered
                    let src_loc_pretty = format!("{:#?}", loc);
                    let encoded = seahash::hash(&src_loc_pretty.as_bytes());

                    let val = CallEdge {
                        callee_name: format!("@indirct#{}", encoded),
                        callee_def: FNPTR_DEF_NAME_CANONICAL.to_string(),
                        is_lang_item,
                        type_params: Vec::new(),
                        src_loc: (&loc).into(),
                    };

                    debug!(
                        "callgraph edge: {} -> {:#?}",
                        canonical.monoitem_name(mono_instance),
                        val,
                    );

                    call_edges.push(val);
                }
            }
        }

        (canonical.monoitem_name(mono_instance), call_edges)
    }

    fn audit_analyze<'tcx>(&mut self, compiler: &interface::Compiler, tcx: TyCtxt<'_, 'tcx, 'tcx>) {
        let db_path = self.output_dir.join("taurus.sled");
        info!(
            "storing results of compile unit {} at {}",
            self.file_name,
            db_path.to_str().unwrap()
        );

        let mut marking_db =
            PersistentSummaryStore::<SourceLocation>::new(&db_path.join("marking"))
                .expect("failed to access consistent storage");

        let mut calledge_db =
            PersistentSummaryStore::<Vec<CallEdge>>::new(&db_path.join("calledge"))
                .expect("failed to access consistent storage");

        let hir_map = tcx.hir();
        let funcs_to_audit = extract_functions_to_audit(&tcx);

        let canonical = Canonical::new(&tcx, compiler.source_map().clone());

        for hir_id in &funcs_to_audit {
            let def_id = hir_map.local_def_id_from_hir_id(*hir_id);
            let name = canonical.def_name(def_id);
            let span = tcx.def_span(def_id);
            let src_loc = canonical.source_map().lookup_char_pos(span.lo());

            debug!(
                "marking {}:\n{}",
                name,
                hir_map.hir_to_pretty_string(*hir_id)
            );
            marking_db.insert(name, (&src_loc).into());
        }

        let (mono_items, _) = collect_crate_mono_items(tcx, MonoItemCollectionMode::Eager);

        for mi in mono_items {
            if let MonoItem::Fn(inst) = mi {
                if let InstanceDef::Item(_) = inst.def {
                    let (caller_name, call_edges) = self.collect_call_edges(&canonical, &inst);
                    calledge_db.insert(caller_name, call_edges);
                }
            }
        }
    }
}
