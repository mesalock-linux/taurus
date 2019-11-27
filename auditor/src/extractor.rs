extern crate seahash;

use rustc::hir::def_id::DefId;
use rustc::mir::mono::MonoItem;
use rustc::mir::visit::Visitor;
use rustc::mir::{Body, Location, Operand, Terminator, TerminatorKind};
use rustc::ty::{Instance, InstanceDef, TyCtxt, TyKind};
use rustc_interface::interface;
use rustc_mir::monomorphize::collector::{collect_crate_mono_items, MonoItemCollectionMode};

use std::collections::HashSet;
use std::path::PathBuf;

use crate::annotated::*;
use crate::summaries::*;

struct MirScanner<'a, 'tcx: 'a> {
    pub canonical: &'a Canonical<'tcx, 'a>,
    pub result: Vec<DepEdge>,
    pub def_id: DefId,
    pub is_local: bool,
    pub body: &'a Body<'tcx>,
    pub is_lang_item: bool,
}

impl<'a, 'tcx: 'a> Visitor<'tcx> for MirScanner<'a, 'tcx> {
    fn visit_terminator(&mut self, term: &Terminator<'tcx>, mir_loc: Location) {
        if let TerminatorKind::Call { func, .. } = &term.kind {
            if let TyKind::FnPtr(..) = func.ty(self.body, *self.canonical.tcx()).sty {
                let loc = self
                    .canonical
                    .source_map()
                    .lookup_char_pos(self.body.source_info(mir_loc).span.lo());
                let src_loc_pretty = format!("{:#?}", loc);
                let encoded = seahash::hash(&src_loc_pretty.as_bytes());

                let val = DepEdge {
                    callee_def: format!("{}#{}", FNPTR_DEF_NAME_CANONICAL, encoded),
                    is_lang_item: self.is_lang_item,
                    type_params: Vec::new(),
                    src_loc: (&loc).into(),
                };

                self.result.push(val);
            }
        }

        self.super_terminator(term, mir_loc);
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>, mir_loc: Location) {
        if let TyKind::FnDef(callee_def_id, substs) =
            operand.ty(self.body, *self.canonical.tcx()).sty
        {
            let mut def_id = callee_def_id;
            let mut generic_args = substs;

            if !self.canonical.tcx().is_mir_available(def_id) {
                // We can only resolve trait functions for local crates. rustc may
                // crash if certain information is missing in the meta data of an
                // extern crate. There is no way for us to tell.
                if self.is_local {
                    let param_env = self.canonical.tcx().param_env(self.def_id);
                    if let Some(instance) =
                        Instance::resolve(*self.canonical.tcx(), param_env, def_id, generic_args)
                    {
                        def_id = instance.def.def_id();
                        generic_args = instance.substs;
                    }
                } else {
                    trace!(
                        "unresolved edge {} -> {}",
                        self.canonical.def_name(self.def_id),
                        self.canonical.def_name(def_id)
                    );
                }
            }

            let loc = self
                .canonical
                .source_map()
                .lookup_char_pos(self.body.source_info(mir_loc).span.lo());

            let type_params: Vec<String> = generic_args
                .types()
                .into_iter()
                .map(|ty| self.canonical.normalized_type_name(ty))
                .collect();

            let val = DepEdge {
                callee_def: self.canonical.def_name(def_id),
                is_lang_item: self.is_lang_item,
                type_params,
                src_loc: (&loc).into(),
            };

            self.result.push(val);
        }

        self.super_operand(operand, mir_loc);
    }
}

impl<'a, 'tcx: 'a> MirScanner<'a, 'tcx> {
    pub fn scan(
        def_id: DefId,
        mir_body: &'a Body<'tcx>,
        canonical: &'a Canonical<'tcx, 'a>,
        is_lang_item: bool,
    ) -> Vec<DepEdge> {
        let is_local = canonical.tcx().hir().as_local_hir_id(def_id).is_some();
        let mut mir_scanner = MirScanner {
            canonical,
            result: Vec::new(),
            def_id,
            is_local,
            body: &mir_body,
            is_lang_item,
        };

        mir_scanner.visit_body(mir_body);

        mir_scanner.result
    }
}

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
    fn after_analysis(&mut self, compiler: &interface::Compiler) -> rustc_driver::Compilation {
        // if !compiler.session().rust_2018() {
        //     compiler.session().fatal("taurus can only audit Rust 2018 projects");
        // }

        compiler.session().abort_if_errors();

        if self.output_dir.to_str().unwrap().contains("/build/") {
            // Build scripts do not need to be audited
            return rustc_driver::Compilation::Continue;
        }
        // We don't want to analyze our own stuff
        if self.file_name.contains("/taurus/annotation")
            || self.file_name.contains("/taurus/attributes")
        {
            return rustc_driver::Compilation::Continue;
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
        // return Continue such that rustc can continue to emit LLVM bitcode
        rustc_driver::Compilation::Continue
    }
}

impl TaurusExtractor {
    fn collect_call_edges<'tcx>(
        &mut self,
        canonical: &Canonical<'tcx, '_>,
        mono_instance: &Instance<'tcx>,
    ) -> (String, Vec<DepEdge>) {
        let tcx = canonical.tcx();

        let is_lang_item = self.lang_items.contains(&mono_instance.def_id()) || {
            if let Some(hir_id) = tcx.hir().as_local_hir_id(mono_instance.def_id()) {
                let parent_did = tcx.hir().get_parent_did(hir_id);
                self.lang_items.contains(&parent_did)
            } else {
                // By far, we know that (in the case of MesaTEE) some lang items and
                // things in std are non-local. It's hard to further distinguish the two
                // cases. So we just assume they should not be regarded as lang items
                false
            }
        };

        let def_id = mono_instance.def.def_id();
        let mir = tcx.instance_mir(mono_instance.def);

        let call_edges = MirScanner::scan(def_id, mir, canonical, is_lang_item);

        (
            canonical.monoitem_name(mono_instance.def.def_id(), mono_instance.substs),
            call_edges,
        )
    }

    fn audit_analyze<'tcx>(&mut self, compiler: &interface::Compiler, tcx: TyCtxt<'tcx>) {
        let db_path = self.output_dir.join("taurus.depstore");
        info!(
            "storing results of compile unit {} at {}",
            self.file_name,
            db_path.to_str().unwrap()
        );

        let mut marking_db = PersistentSummaryStore::<MarkedItem>::new(&db_path.join("marking"))
            .expect("failed to access consistent storage");

        let mut calledge_db =
            PersistentSummaryStore::<Vec<DepEdge>>::new(&db_path.join("calledge"))
                .expect("failed to access consistent storage");

        let hir_map = tcx.hir();
        let annotated_funcs = extract_annotated_functions(&taurus_attributes::Symbols::new(), &tcx);

        let canonical = Canonical::new(&tcx, compiler.source_map().clone());

        for (hir_id, marking) in annotated_funcs {
            let def_id = hir_map.local_def_id(hir_id);
            let name = canonical.def_name(def_id);
            let span = tcx.def_span(def_id);
            let src_loc = canonical.source_map().lookup_char_pos(span.lo());

            marking_db.insert(
                name,
                MarkedItem {
                    marking,
                    src_loc: (&src_loc).into(),
                },
            );
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
