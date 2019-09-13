extern crate seahash;

use rustc::hir::def_id::DefId;
use rustc::mir::mono::MonoItem;
use rustc::mir::visit::Visitor;
use rustc::mir::{Location, Mir, Operand, Terminator, TerminatorKind};
use rustc::ty::{Instance, InstanceDef, TyCtxt, TyKind};
use rustc_interface::interface;
use rustc_mir::monomorphize::collector::{collect_crate_mono_items, MonoItemCollectionMode};

use std::collections::HashSet;
use std::path::PathBuf;

use crate::annotated::*;
use crate::summaries::*;

struct MirScanner<'a, 'b, 'tcx: 'b> {
    pub canonical: &'a Canonical<'b, 'tcx, 'tcx, 'a>,
    pub result: Vec<DepEdge>,
    pub body: &'a Mir<'tcx>,
    pub is_lang_item: bool,
}

impl<'a, 'b: 'a, 'tcx: 'b> Visitor<'tcx> for MirScanner<'a, 'b, 'tcx> {
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
            let loc = self
                .canonical
                .source_map()
                .lookup_char_pos(self.body.source_info(mir_loc).span.lo());

            let type_params: Vec<String> = substs
                .types()
                .into_iter()
                .map(|ty| self.canonical.normalized_type_name(ty))
                .collect();

            let val = DepEdge {
                callee_def: self.canonical.def_name(callee_def_id),
                is_lang_item: self.is_lang_item,
                type_params,
                src_loc: (&loc).into(),
            };

            self.result.push(val);
        }

        self.super_operand(operand, mir_loc);
    }
}

impl<'a, 'b: 'a, 'tcx: 'b> MirScanner<'a, 'b, 'tcx> {
    pub fn scan(
        mir_body: &'a Mir<'tcx>,
        canonical: &'a Canonical<'b, 'tcx, 'tcx, 'a>,
        is_lang_item: bool,
    ) -> Vec<DepEdge> {
        let mut mir_scanner = MirScanner {
            canonical,
            result: Vec::new(),
            body: &mir_body,
            is_lang_item,
        };

        mir_scanner.visit_mir(mir_body);

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
    ) -> (String, Vec<DepEdge>) {
        let tcx = canonical.tcx();

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
        let call_edges = MirScanner::scan(mir, canonical, is_lang_item);

        (
            canonical.monoitem_name(mono_instance.def.def_id(), mono_instance.substs),
            call_edges,
        )
    }

    fn audit_analyze<'tcx>(&mut self, compiler: &interface::Compiler, tcx: TyCtxt<'_, 'tcx, 'tcx>) {
        let db_path = self.output_dir.join("taurus.depstore");
        info!(
            "storing results of compile unit {} at {}",
            self.file_name,
            db_path.to_str().unwrap()
        );

        let mut marking_db =
            PersistentSummaryStore::<SourceLocation>::new(&db_path.join("marking"))
                .expect("failed to access consistent storage");

        let mut calledge_db =
            PersistentSummaryStore::<Vec<DepEdge>>::new(&db_path.join("calledge"))
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
