use rustc::hir::*;
use rustc::ty::TyCtxt;
use rustc::ty::fast_reject;

use std::collections::HashSet;

pub fn extract_functions_to_audit(tcx: &TyCtxt<'_, '_, '_>) -> HashSet<HirId> {
    let mut funcs: HashSet<HirId> = HashSet::new();
    let hir_map = tcx.hir();
    let symbols = taurus_attributes::Symbols::new();
    let mark = &symbols.require_audit;
    
    for (_, item) in &hir_map.krate().trait_items {
        if syntax::attr::contains_name(&item.attrs, *mark) {
            if let TraitItemKind::Method(..) = item.node {
                funcs.insert(item.hir_id);
            } else {
                panic!("{} annotation can only mark methods", mark);
            }
        }
    }

    for (_, item) in &hir_map.krate().impl_items {
        if syntax::attr::contains_name(&item.attrs, *mark) {
            if let ImplItemKind::Method(..) = item.node {
                funcs.insert(item.hir_id);
            } else {
                panic!("{} annotation can only mark methods", mark);
            }
        }
    }

    let mut marked_adts: HashSet<fast_reject::SimplifiedType> = HashSet::new();

    for (_, item) in &hir_map.krate().items {
        if syntax::attr::contains_name(&item.attrs, *mark) {
            match &item.node {
                ItemKind::Fn(_, _, _, body_id) => {
                    funcs.insert(body_id.hir_id);
                }
                ItemKind::Enum(..)
                | ItemKind::Struct(..)
                | ItemKind::Union(..) =>
                {
                    let def_id = hir_map.local_def_id_from_hir_id(item.hir_id);
                    let ty = tcx.type_of(def_id);
                    if let Some(simplified_self_ty) =
                        fast_reject::simplify_type(*tcx, ty, false)
                    {
                        marked_adts.insert(simplified_self_ty);
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
                        if let AssociatedItemKind::Method {..} = trait_item.kind {
                            if trait_item.defaultness.has_value() {
                                funcs.insert(trait_item.id.hir_id);
                            }
                        }
                    }
                }
                ItemKind::Impl(_, ImplPolarity::Positive, _, _, _, _, impl_items) => {
                    for impl_item in impl_items {
                        if let AssociatedItemKind::Method {..} = impl_item.kind {
                            funcs.insert(impl_item.id.hir_id);
                        }
                    }
                }
                _ => panic!("illegal use of #[{}] annotation", mark),
            }
        }
    }

    for (_, trait_impls) in &hir_map.krate().trait_impls {
        for trait_impl in trait_impls {
            let impl_def_id = hir_map.local_def_id_from_hir_id(*trait_impl);
            if let Some(Node::Item(item)) = hir_map.find_by_hir_id(*trait_impl) {
                if let ItemKind::Impl(_, ImplPolarity::Positive, _, _, _, _, impl_items) =
                    &item.node
                {
                    let self_ty = tcx.type_of(impl_def_id);
                    if let Some(simplified_self_ty) =
                        fast_reject::simplify_type(*tcx, &self_ty, false)
                    {
                        if marked_adts.contains(&simplified_self_ty) {
                            for impl_item in impl_items {
                                if let AssociatedItemKind::Method {..} = impl_item.kind {
                                    funcs.insert(impl_item.id.hir_id);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    return funcs
}

