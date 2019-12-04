use rustc::hir::*;
use rustc::ty::fast_reject;
use rustc::ty::TyCtxt;
use syntax::ast::{AttrKind, Attribute};

use std::collections::HashMap;

use crate::summaries::Marking;

struct TaurusAttr {
    string: &'static str,
}

impl std::fmt::Display for TaurusAttr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.string)
    }
}

impl TaurusAttr {
    pub fn match_attributes<'a>(&self, attrs: &'a [Attribute]) -> Option<&'a Attribute> {
        attrs.iter().find(|attr| match &attr.kind {
            AttrKind::Normal(attr_item) => {
                let seg = &attr_item.path.segments;
                seg.len() == 2
                    && seg[0].ident.name.as_str() == "taurus"
                    && seg[1].ident.name.as_str() == self.string
            }
            AttrKind::DocComment(_) => false,
        })
    }
}

const ATTR_REQUIRE_AUDIT: TaurusAttr = TaurusAttr {
    string: "require_audit",
};
const ATTR_AUDITED: TaurusAttr = TaurusAttr { string: "audited" };
const ATTR_ENTRY_POINT: TaurusAttr = TaurusAttr {
    string: "entry_point",
};

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

fn marking_from_attributes(attrs: &[Attribute]) -> Marking {
    Marking {
        require_audit: ATTR_REQUIRE_AUDIT
            .match_attributes(attrs)
            .map(extract_meta_value),
        audited: ATTR_AUDITED.match_attributes(attrs).map(extract_meta_value),
        is_entry_point: ATTR_ENTRY_POINT.match_attributes(attrs).is_some(),
    }
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

pub fn extract_annotated_functions(tcx: &TyCtxt<'_>) -> HashMap<HirId, Marking> {
    let mut funcs: HashMap<HirId, Marking> = HashMap::new();
    let hir_map = tcx.hir();

    for (_, item) in &hir_map.krate().trait_items {
        let marking = marking_from_attributes(&item.attrs);

        if marking.annotated() {
            if marking.is_entry_point {
                panic!("#[{}] can only annotate functions", ATTR_ENTRY_POINT);
            }

            if let TraitItemKind::Method(..) = item.kind {
                record_marking(&mut funcs, item.hir_id, marking);
            } else {
                panic!(
                    "#[{}] and #[{}] can only annotate methods, functions, and ADTs",
                    ATTR_REQUIRE_AUDIT, ATTR_AUDITED,
                );
            }
        }
    }

    for (_, item) in &hir_map.krate().impl_items {
        let marking = marking_from_attributes(&item.attrs);

        if marking.annotated() {
            if marking.is_entry_point {
                panic!("#[{}] can only annotate functions", ATTR_ENTRY_POINT);
            }

            if let ImplItemKind::Method(..) = item.kind {
                record_marking(&mut funcs, item.hir_id, marking);
            } else {
                panic!(
                    "#[{}] and #[{}] can only annotate methods, functions, and ADTs",
                    ATTR_REQUIRE_AUDIT, ATTR_AUDITED,
                );
            }
        }
    }

    let mut marked_adts: HashMap<fast_reject::SimplifiedType, Marking> = HashMap::new();

    for (_, item) in &hir_map.krate().items {
        let marking = marking_from_attributes(&item.attrs);

        if marking.annotated() {
            match &item.kind {
                ItemKind::Fn(_, _, body_id) => {
                    record_marking(&mut funcs, hir_map.body_owner(*body_id), marking);
                }
                ItemKind::Enum(..) | ItemKind::Struct(..) | ItemKind::Union(..) => {
                    let def_id = hir_map.local_def_id(item.hir_id);
                    let ty = tcx.type_of(def_id);
                    // For soundness, ignore generic parameters when simplifying the annotated ADTs
                    if let Some(simplified_self_ty) = fast_reject::simplify_type(*tcx, ty, true) {
                        if marking.require_audit.is_some() {
                            marked_adts.insert(simplified_self_ty, marking);
                        } else {
                            panic!(
                                "#[{}] can only annotate functions and methods",
                                ATTR_AUDITED,
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
                    ATTR_REQUIRE_AUDIT, ATTR_AUDITED,
                ),
            }
        }
    }

    // Collect entry points
    for (_, item) in &hir_map.krate().items {
        let marking = marking_from_attributes(&item.attrs);

        if marking.is_entry_point {
            if let ItemKind::Fn(_, generics, body_id) = &item.kind {
                if generics.params.len() == 0 {
                    record_marking(&mut funcs, hir_map.body_owner(*body_id), marking);
                    continue;
                }
            }

            panic!(
                "#[{}] can only annotate functions that are non-generic",
                ATTR_ENTRY_POINT,
            );
        }
    }

    // Propogate require_audit annotations to impl items associated with marked ADTs
    for (id, _) in &hir_map.krate().impl_items {
        let parent_hir_id = hir_map.get_parent_item(id.hir_id);
        let node = hir_map.get(parent_hir_id);

        match node {
            Node::Item(item) => {
                if let ItemKind::Impl(_, ImplPolarity::Positive, _, _, _, _, _) = &item.kind {
                    let parent_did = hir_map.local_def_id(parent_hir_id);
                    let ty = tcx.type_of(parent_did);

                    // If the type cannot be simplified, it's likely a generic. We do not audit impls for pure
                    // generics since they are not specific to types we care about.
                    if let Some(simplified_self_ty) = fast_reject::simplify_type(*tcx, ty, true) {
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
