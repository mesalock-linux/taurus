// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the same directory where this file resides.

// Modified by Pei Wang <wangpei10@baidu.com>

use rustc::hir::def_id::DefId;
use rustc::hir::map::DefPathData;
use rustc::ty::subst::{SubstsRef, UnpackedKind};
use rustc::ty::{Ty, TyCtxt, TyKind};

pub fn append_type_args_name<'tcx>(
    result: &mut String,
    tcx: &TyCtxt<'_, '_, 'tcx>,
    generic_args: SubstsRef<'tcx>,
) {
    result.push('>');
    for generic_ty_arg in generic_args.types() {
        result.push(',');
        append_mangled_type(result, generic_ty_arg, tcx);
    }
    result.push('>');
}

pub fn append_mangled_type<'tcx>(str: &mut String, ty: Ty<'tcx>, tcx: &TyCtxt<'_, '_, 'tcx>) {
    use syntax::ast;
    use TyKind::*;
    match ty.sty {
        Bool => str.push_str("bool"),
        Char => str.push_str("char"),
        Int(int_ty) => {
            str.push_str(match int_ty {
                ast::IntTy::Isize => "isize",
                ast::IntTy::I8 => "i8",
                ast::IntTy::I16 => "i16",
                ast::IntTy::I32 => "i32",
                ast::IntTy::I64 => "i64",
                ast::IntTy::I128 => "i128",
            });
        }
        Uint(uint_ty) => {
            str.push_str(match uint_ty {
                ast::UintTy::Usize => "usize",
                ast::UintTy::U8 => "u8",
                ast::UintTy::U16 => "u16",
                ast::UintTy::U32 => "u32",
                ast::UintTy::U64 => "u64",
                ast::UintTy::U128 => "u128",
            });
        }
        Float(float_ty) => {
            str.push_str(match float_ty {
                ast::FloatTy::F32 => "f32",
                ast::FloatTy::F64 => "f64",
            });
        }
        Adt(def, subs) => {
            str.push_str(qualified_type_name(tcx, def.did).as_str());
            for sub in subs {
                if let UnpackedKind::Type(ty) = sub.unpack() {
                    str.push('_');
                    append_mangled_type(str, ty, tcx);
                }
            }
        }
        Closure(def_id, subs) => {
            str.push_str("closure_");
            str.push_str(qualified_type_name(tcx, def_id).as_str());
            for sub in subs.substs {
                if let UnpackedKind::Type(ty) = sub.unpack() {
                    str.push('_');
                    append_mangled_type(str, ty, tcx);
                }
            }
        }
        Dynamic(..) => str.push_str(&format!("dyn_{:?}", ty)),
        Foreign(def_id) => {
            str.push_str("extern_type_");
            str.push_str(qualified_type_name(tcx, def_id).as_str());
        }
        FnDef(def_id, subs) => {
            str.push_str("fn_");
            str.push_str(qualified_type_name(tcx, def_id).as_str());
            for sub in subs {
                if let UnpackedKind::Type(ty) = sub.unpack() {
                    str.push('_');
                    append_mangled_type(str, ty, tcx);
                }
            }
        }
        Opaque(def_id, subs) => {
            str.push_str("impl_");
            str.push_str(qualified_type_name(tcx, def_id).as_str());
            for sub in subs {
                if let UnpackedKind::Type(ty) = sub.unpack() {
                    str.push('_');
                    append_mangled_type(str, ty, tcx);
                }
            }
        }
        Str => str.push_str("str"),
        Array(ty, _) => {
            str.push_str("array_");
            append_mangled_type(str, ty, tcx);
        }
        Slice(ty) => {
            str.push_str("slice_");
            append_mangled_type(str, ty, tcx);
        }
        RawPtr(ty_and_mut) => {
            str.push_str("pointer_");
            match ty_and_mut.mutbl {
                rustc::hir::MutMutable => str.push_str("mut_"),
                rustc::hir::MutImmutable => str.push_str("const_"),
            }
            append_mangled_type(str, ty_and_mut.ty, tcx);
        }
        Ref(_, ty, mutability) => {
            str.push_str("ref_");
            if mutability == rustc::hir::MutMutable {
                str.push_str("mut_");
            }
            append_mangled_type(str, ty, tcx);
        }
        FnPtr(psig) => {
            str.push_str(&format!("FnPtr {:?}", psig));
        }
        Tuple(types) => {
            str.push_str("tuple_");
            str.push_str(&format!("{}", types.len()));
            types.iter().for_each(|t| {
                str.push('_');
                append_mangled_type(str, t.expect_ty(), tcx);
            });
        }
        Param(param_ty) => {
            let pty: Ty<'tcx> = param_ty.to_ty(*tcx);
            if ty.eq(pty) {
                str.push_str(&format!("{:?}", ty));
            } else {
                append_mangled_type(str, pty, tcx);
            }
        }
        Projection(projection_ty) => {
            append_mangled_type(str, projection_ty.self_ty(), tcx);
            str.push_str("_as_");
            str.push_str(qualified_type_name(tcx, projection_ty.item_def_id).as_str());
        }
        _ => {
            //todo: add cases as the need arises, meanwhile make the need obvious.
            debug!("{:?}", ty);
            debug!("{:?}", ty.sty);
            str.push_str(&format!("default formatted {:?}", ty))
        }
    }
}

fn qualified_type_name(tcx: &TyCtxt<'_, '_, '_>, def_id: DefId) -> String {
    let mut name = if def_id.is_local() {
        tcx.crate_name.as_interned_str().as_str().to_string()
    } else {
        let cdata = tcx.crate_data_as_rc_any(def_id.krate);
        let cdata = cdata
            .downcast_ref::<rustc_metadata::cstore::CrateMetadata>()
            .unwrap();
        cdata.name.as_str().to_string()
    };
    for component in &tcx.def_path(def_id).data {
        name.push_str("::");
        push_component_name(&component.data, &mut name);
        name.push('[');
        let da = component.disambiguator.to_string();
        name.push_str(da.as_str());
        name.push(']');

    }
    name
}

fn push_component_name(component_data: &DefPathData, target: &mut String) {
    use DefPathData::*;
    match component_data {
        TypeNs(name) | ValueNs(name) | MacroNs(name) | LifetimeNs(name) | GlobalMetaData(name) => {
            target.push_str(name.as_str().get());
        }
        _ => target.push_str(match component_data {
            CrateRoot => "crate_root",
            Impl => "implement",
            Misc => "miscellaneous",
            ClosureExpr => "closure",
            Ctor => "ctor",
            AnonConst => "constant",
            ImplTrait => "implement_trait",
            _ => unreachable!(),
        }),
    };
}
