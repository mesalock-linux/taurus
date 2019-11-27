use rustc::hir::*;
use rustc::ty::fast_reject;
use rustc::ty::TyCtxt;
use syntax::ast::Attribute;

use std::collections::HashMap;

use crate::summaries::Marking;

#[inline]
fn extract_meta_value(attr: &Attribute) -> String {
    attr.value_str()
        .unwrap_or_else(|| {
            panic!(
                "{} annotation require additional meta data",
                attr.name_or_empty()
            )
        })
        .to_string()
}

fn record_marking(result: &mut HashMap<HirId, Marking>, hir_id: HirId, marking: Marking) {
    if let Some(stored_marking) = result.get_mut(&hir_id) {
        if let Some(meta) = marking.require_audit {
            stored_marking.require_audit = Some(meta);
        }
        if let Some(meta) = marking.audited {
            stored_marking.audited = Some(meta);
        }
        stored_marking.is_entry_point = marking.is_entry_point || stored_marking.is_entry_point;
    } else {
        result.insert(hir_id, marking);
    }
}

pub fn extract_annotated_functions(
    taurus_annotations: &taurus_attributes::Symbols,
    tcx: &TyCtxt<'_>,
) -> HashMap<HirId, Marking> {
    let mut funcs: HashMap<HirId, Marking> = HashMap::new();
    let hir_map = tcx.hir();

    for (_, item) in &hir_map.krate().trait_items {
        let annotation = &taurus_annotations.entry_point;
        if let Some(_) = syntax::attr::find_by_name(&item.attrs, *annotation) {
            panic!("#[{}] can only annotate functions", annotation);
        }

        let mut marking = Marking {
            require_audit: None,
            audited: None,
            is_entry_point: false,
        };
        if let Some(attr) =
            syntax::attr::find_by_name(&item.attrs, taurus_annotations.require_audit)
        {
            marking.require_audit = Some(extract_meta_value(attr));
        }

        if let Some(attr) = syntax::attr::find_by_name(&item.attrs, taurus_annotations.audited) {
            marking.audited = Some(extract_meta_value(attr));
        }

        if marking.annotated() {
            if let TraitItemKind::Method(..) = item.node {
                record_marking(&mut funcs, item.hir_id, marking);
            } else {
                panic!(
                    "#[{}] and #[{}] can only annotate methods, functions, and ADTs",
                    taurus_annotations.require_audit, taurus_annotations.audited,
                );
            }
        }
    }

    for (_, item) in &hir_map.krate().impl_items {
        let annotation = &taurus_annotations.entry_point;
        if let Some(_) = syntax::attr::find_by_name(&item.attrs, *annotation) {
            panic!("#[{}] can only annotate functions", annotation);
        }

        let mut marking = Marking::default();
        if let Some(attr) =
            syntax::attr::find_by_name(&item.attrs, taurus_annotations.require_audit)
        {
            marking.require_audit = Some(extract_meta_value(attr));
        }

        if let Some(attr) = syntax::attr::find_by_name(&item.attrs, taurus_annotations.audited) {
            marking.audited = Some(extract_meta_value(attr));
        }

        if marking.annotated() {
            if let ImplItemKind::Method(..) = item.node {
                record_marking(&mut funcs, item.hir_id, marking);
            } else {
                panic!(
                    "#[{}] and #[{}] can only annotate methods, functions, and ADTs",
                    taurus_annotations.require_audit, taurus_annotations.audited,
                );
            }
        }
    }

    let mut marked_adts: HashMap<fast_reject::SimplifiedType, Marking> = HashMap::new();

    for (_, item) in &hir_map.krate().items {
        let mut marking = Marking::default();

        if let Some(attr) =
            syntax::attr::find_by_name(&item.attrs, taurus_annotations.require_audit)
        {
            marking.require_audit = Some(extract_meta_value(attr));
        }

        if let Some(attr) = syntax::attr::find_by_name(&item.attrs, taurus_annotations.audited) {
            marking.audited = Some(extract_meta_value(attr));
        }

        if marking.annotated() {
            match &item.node {
                ItemKind::Fn(_, _, _, body_id) => {
                    record_marking(&mut funcs, hir_map.body_owner(*body_id), marking);
                }
                ItemKind::Enum(..) | ItemKind::Struct(..) | ItemKind::Union(..) => {
                    let def_id = hir_map.local_def_id(item.hir_id);
                    let ty = tcx.type_of(def_id);
                    if let Some(simplified_self_ty) = fast_reject::simplify_type(*tcx, ty, false) {
                        if marking.require_audit.is_some() {
                            marked_adts.insert(simplified_self_ty, marking);
                        } else {
                            panic!(
                                "#[{}] can only annotate functions and methods",
                                taurus_annotations.audited,
                            );
                        }
                    } else {
                        panic!("marked ADT cannot be simplified");
                    }
                }
                // Marking a trait does not mean too much. Only the default
                // implementation (if there is any) of the trait items are
                // collected. We should consider completely banning marking
                // traits directly.
                ItemKind::Trait(_, _, _, _, trait_items) => {
                    for trait_item in trait_items {
                        if let AssocItemKind::Method { .. } = trait_item.kind {
                            if trait_item.defaultness.has_value() {
                                record_marking(&mut funcs, trait_item.id.hir_id, marking.clone());
                            }
                        }
                    }
                }
                ItemKind::Impl(_, ImplPolarity::Positive, _, _, _, _, impl_items) => {
                    for impl_item in impl_items {
                        if let AssocItemKind::Method { .. } = impl_item.kind {
                            record_marking(&mut funcs, impl_item.id.hir_id, marking.clone());
                        }
                    }
                }
                _ => panic!(
                    "#[{}] and #[{}] can only annotate functions, methods, and ADTs",
                    taurus_annotations.require_audit, taurus_annotations.audited,
                ),
            }
        }
    }

    // Collect entry points
    for (_, item) in &hir_map.krate().items {
        if let Some(_) = syntax::attr::find_by_name(&item.attrs, taurus_annotations.entry_point) {
            if let ItemKind::Fn(_, _, generics, body_id) = &item.node {
                if generics.params.len() == 0 {
                    record_marking(
                        &mut funcs,
                        hir_map.body_owner(*body_id),
                        Marking::entry_point(),
                    );
                    continue;
                }
            }

            panic!(
                "#[{}] can only annotate functions that are non-generic",
                taurus_annotations.entry_point,
            );
        }
    }

    // Propogate require_audit annotations to impl items associated with marked ADTs
    for (id, _) in &hir_map.krate().impl_items {
        let parent_hir_id = hir_map.get_parent_item(id.hir_id);
        let node = hir_map.get(parent_hir_id);

        match node {
            Node::Item(item) => {
                if let ItemKind::Impl(_, ImplPolarity::Positive, _, _, _, _, _) = &item.node {
                    let parent_did = hir_map.local_def_id(parent_hir_id);
                    let ty = tcx.type_of(parent_did);

                    // If the type cannot be simplified, it's likely a generic. We do not audit impls for pure
                    // generics since they are not specific to types we care about.
                    if let Some(simplified_self_ty) = fast_reject::simplify_type(*tcx, ty, false) {
                        if let Some(marking) = marked_adts.get(&simplified_self_ty) {
                            record_marking(&mut funcs, id.hir_id, marking.clone());
                        }
                    }
                }
            }
            _ => panic!("expecting item"),
        }
    }

    funcs
}
