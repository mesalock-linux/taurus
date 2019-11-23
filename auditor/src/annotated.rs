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

pub fn extract_functions_to_audit(
    taurus_annotations: &taurus_attributes::Symbols,
    tcx: &TyCtxt<'_>,
) -> HashMap<HirId, Marking> {
    let mut funcs: HashMap<HirId, Marking> = HashMap::new();
    let hir_map = tcx.hir();

    for (_, item) in &hir_map.krate().trait_items {
        let mark = &taurus_annotations.require_audit;
        if let Some(attr) = syntax::attr::find_by_name(&item.attrs, *mark) {
            if let TraitItemKind::Method(..) = item.node {
                funcs.insert(item.hir_id, Marking::RequireAudit(extract_meta_value(attr)));
            } else {
                panic!("#[{}] can only annotate methods, functions, and ADTs", mark);
            }
        }
        let mark = &taurus_annotations.audited;
        if let Some(attr) = syntax::attr::find_by_name(&item.attrs, *mark) {
            if let TraitItemKind::Method(..) = item.node {
                funcs.insert(item.hir_id, Marking::Audited(extract_meta_value(attr)));
            } else {
                panic!("#[{}] can only annotate methods, functions", mark);
            }
        }
        let mark = &taurus_annotations.entry_point;
        if let Some(_) = syntax::attr::find_by_name(&item.attrs, *mark) {
            panic!("#[{}] can only annotate functions", mark);
        }
    }

    for (_, item) in &hir_map.krate().impl_items {
        let mark = &taurus_annotations.require_audit;
        if let Some(attr) = syntax::attr::find_by_name(&item.attrs, *mark) {
            if let ImplItemKind::Method(..) = item.node {
                funcs.insert(item.hir_id, Marking::RequireAudit(extract_meta_value(attr)));
            } else {
                panic!("{} annotation can only mark methods", mark);
            }
        }
        let mark = &taurus_annotations.audited;
        if let Some(attr) = syntax::attr::find_by_name(&item.attrs, *mark) {
            if let ImplItemKind::Method(..) = item.node {
                funcs.insert(item.hir_id, Marking::Audited(extract_meta_value(attr)));
            } else {
                panic!("{} annotation can only mark methods", mark);
            }
        }
        let mark = &taurus_annotations.entry_point;
        if let Some(_) = syntax::attr::find_by_name(&item.attrs, *mark) {
            panic!("{} annotation can only mark functions", mark);
        }
    }

    let mut marked_adts: HashMap<fast_reject::SimplifiedType, Marking> = HashMap::new();

    for (_, item) in &hir_map.krate().items {
        if let Some(attr) =
            syntax::attr::find_by_name(&item.attrs, taurus_annotations.require_audit)
        {
            match &item.node {
                ItemKind::Fn(_, _, _, body_id) => {
                    funcs.insert(
                        hir_map.body_owner(*body_id),
                        Marking::RequireAudit(extract_meta_value(attr)),
                    );
                }
                ItemKind::Enum(..) | ItemKind::Struct(..) | ItemKind::Union(..) => {
                    let def_id = hir_map.local_def_id(item.hir_id);
                    let ty = tcx.type_of(def_id);
                    if let Some(simplified_self_ty) = fast_reject::simplify_type(*tcx, ty, false) {
                        marked_adts.insert(
                            simplified_self_ty,
                            Marking::RequireAudit(extract_meta_value(attr)),
                        );
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
                                funcs.insert(
                                    trait_item.id.hir_id,
                                    Marking::RequireAudit(extract_meta_value(attr)),
                                );
                            }
                        }
                    }
                }
                ItemKind::Impl(_, ImplPolarity::Positive, _, _, _, _, impl_items) => {
                    for impl_item in impl_items {
                        if let AssocItemKind::Method { .. } = impl_item.kind {
                            funcs.insert(
                                impl_item.id.hir_id,
                                Marking::RequireAudit(extract_meta_value(attr)),
                            );
                        }
                    }
                }
                _ => panic!(
                    "#[{}] can only annotate functions and methods",
                    taurus_annotations.require_audit,
                ),
            }
        }
    }

    // Collect entry points
    for (_, item) in &hir_map.krate().items {
        if let Some(_) = syntax::attr::find_by_name(&item.attrs, taurus_annotations.entry_point) {
            if let ItemKind::Fn(_, _, generics, body_id) = &item.node {
                if generics.params.len() == 0 {
                    funcs.insert(hir_map.body_owner(*body_id), Marking::EntryPoint);
                    continue;
                }
            }

            panic!(
                "#[{}] can only annotate functions that are non-generic",
                taurus_annotations.entry_point,
            );
        }
    }

    // Propogate require_audit annotations to items associated with marked ADTs
    for (_, trait_impls) in &hir_map.krate().trait_impls {
        for trait_impl in trait_impls {
            let impl_def_id = hir_map.local_def_id(*trait_impl);
            if let Some(Node::Item(item)) = hir_map.find(*trait_impl) {
                if let ItemKind::Impl(_, ImplPolarity::Positive, _, _, _, _, impl_items) =
                    &item.node
                {
                    let self_ty = tcx.type_of(impl_def_id);
                    if let Some(simplified_self_ty) =
                        fast_reject::simplify_type(*tcx, &self_ty, false)
                    {
                        if let Some(adt_marking) = marked_adts.get(&simplified_self_ty) {
                            for impl_item in impl_items {
                                if let AssocItemKind::Method { .. } = impl_item.kind {
                                    funcs.insert(impl_item.id.hir_id, adt_marking.clone());
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    funcs
}
