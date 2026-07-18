//! M-740 Stage 5 (M-1013 STEP 3, PR-1 + PR-2 + PR-2b; DN-26 §7.3 / §10.2) — the self-hosted
//! `compiler.semcore` port of checkty.rs's **register-family**: the constructor-resolution seam and
//! the type-registry builder that drives it, both a LIVE-ORACLE marshalling differential.
//!
//! Helpers ported into `lib/compiler/semcore.myc` and gated here:
//!   * `first_duplicate` (checkty.rs) — the first value appearing more than once, left to right.
//!   * `resolve_ctors` (checkty.rs) — resolve every surface `Ctor`'s field `TypeRef`s (the decl's
//!     type params in scope) into checked `CtorInfo`s, refusing a duplicate constructor name.
//!   * `register_types` (checkty.rs; **PR-2 + PR-2b**) — build the `Nodule`'s type registry: a shell
//!     per `Item::Type` (so recursive/forward field references resolve), then a `resolve_ctors` fill,
//!     preceded by the **FULL** M-826 tuple pre-pass — every leg the Rust oracle walks (type-decl
//!     ctor fields, fn/trait/impl signatures, `match` patterns, and fn-body expressions), closing
//!     **FLAG-semcore-30** (PR-2b). The never-silent floor is unchanged: any `Tuple$N` still missing
//!     at `resolve_ty` time surfaces as an explicit `Err`, exercised by
//!     `register_types_unreferenced_tuple_still_errs_never_silent`; the full-walk coverage is pinned
//!     by `collect_tuple_arities_cases` and `register_types_registers_leg_tuples`.
//!
//! **Differential method — harness MARSHALLING (DN-26 §10.2).** Each case runs the REAL Rust
//! `checkty::{resolve_ctors, first_duplicate}` oracle on a fixture, producing a genuine
//! `Result<Vec<CtorInfo>, _>` / `Option<&String>`. It then evaluates the `.myc` port *directly* (the
//! driver's `main` returns the mirror value) and DECODES that `L1Value` mirror ADT back into the real
//! Rust type (`decode_ty`/`decode_ctor_info`/`decode_data_info` — the never-silent inverse of the
//! mirror constructors, built on the shared `marshal_support` primitives). The two independently-
//! produced values are compared with **Rust's own trusted derived `==`**. A mis-lowering diverges the
//! decoded value from the oracle; `marshal_discriminates` proves each new decoder arm reads every
//! dimension it claims to (the migrated non-vacuity discipline). `Err` messages differ across the two
//! productions, so `decode_result`/`want.map_err(|_| ())` normalize both to `()` (any `Err` == any
//! `Err`; only the `Ok` payload is a meaningful differential).

use crate::ast::{
    Arm, BaseType, Ctor, DeriveDecl, Expr, FnDecl, FnSig, ImplDecl, InherentImplDecl, Item,
    Literal, LowerDecl, LowerRhs, Nodule, ObjectDecl, Paradigm, Param, ParamKind, Path, Pattern,
    Scalar, Sparsity, TraitDecl, TraitRef, TypeDecl, TypeParam, TypeRef, UsePath, ViaDecl, Vis,
    WidthRef,
};
use crate::checkty::{
    collect_tuple_arities, first_duplicate, prelude, register_instances, register_nodule_decls,
    register_traits, register_types, resolve_ctors, resolve_imports, type_head, CoherenceView,
    CtorInfo, DataInfo, Exports, InstanceInfo, NoduleImports, NoduleRegs, Phyla, TraitInfo, Ty,
    Width,
};
use crate::eval::L1Value;
use crate::tests::marshal_support::*;
use std::collections::{BTreeMap, BTreeSet};

// ── L1Value → checkty decoders (register-family output types; the marshalling inverse) ──────────────

fn decode_scalar(v: &L1Value) -> Scalar {
    match expect_data(v, "Scalar").0 {
        "SF16" => Scalar::F16,
        "SBf16" => Scalar::Bf16,
        "SF32" => Scalar::F32,
        "SF64" => Scalar::F64,
        c => panic!("marshal decode_scalar: unexpected ctor {c}"),
    }
}

fn decode_sparsity(v: &L1Value) -> Sparsity {
    let (ctor, fields) = expect_data(v, "Sparsity");
    match ctor {
        "SpDense" => Sparsity::Dense,
        "SpSparse" => Sparsity::Sparse(decode_u32(&fields[0])),
        c => panic!("marshal decode_sparsity: unexpected ctor {c}"),
    }
}

fn decode_width(v: &L1Value) -> Width {
    let (ctor, fields) = expect_data(v, "Width");
    match ctor {
        "WdLit" => Width::Lit(decode_u32(&fields[0])),
        "WdVar" => Width::Var(decode_string(&fields[0])),
        c => panic!("marshal decode_width: unexpected ctor {c}"),
    }
}

/// The checked `Ty` mirror (all 11 variants) → `checkty::Ty`. Recursive on `Data`/`Seq`/`Fn`.
fn decode_ty(v: &L1Value) -> Ty {
    let (ctor, fields) = expect_data(v, "Ty");
    match ctor {
        "TyBinary" => Ty::Binary(decode_width(&fields[0])),
        "TyTernary" => Ty::Ternary(decode_width(&fields[0])),
        "TyDense" => Ty::Dense(decode_u32(&fields[0]), decode_scalar(&fields[1])),
        "TyVsa" => Ty::Vsa {
            model: decode_string(&fields[0]),
            dim: decode_u32(&fields[1]),
            sparsity: decode_sparsity(&fields[2]),
        },
        "TyData" => Ty::Data(decode_string(&fields[0]), decode_vec(&fields[1], decode_ty)),
        "TySubstrate" => Ty::Substrate(decode_string(&fields[0])),
        "TySeq" => Ty::Seq(Box::new(decode_ty(&fields[0])), decode_u32(&fields[1])),
        "TyBytes" => Ty::Bytes,
        "TyFloat" => Ty::Float,
        "TyVar" => Ty::Var(decode_string(&fields[0])),
        "TyFn" => Ty::Fn(
            Box::new(decode_ty(&fields[0])),
            Box::new(decode_ty(&fields[1])),
        ),
        c => panic!("marshal decode_ty: unexpected ctor {c}"),
    }
}

/// `CI(name, fields)` → `checkty::CtorInfo`.
fn decode_ctor_info(v: &L1Value) -> CtorInfo {
    let (ctor, fields) = expect_data(v, "CtorInfo");
    match ctor {
        "CI" => CtorInfo {
            name: decode_string(&fields[0]),
            fields: decode_vec(&fields[1], decode_ty),
        },
        c => panic!("marshal decode_ctor_info: unexpected ctor {c}"),
    }
}

/// `DI(name, params, ctors)` → `checkty::DataInfo`. (`resolve_ctors` returns `Vec<CtorInfo>`; this
/// decoder is exercised by `marshal_discriminates` and pairs with `encode_data_info` on the input side
/// — it is the register-family's data-type mirror, ready for the later `register_types` increment.)
fn decode_data_info(v: &L1Value) -> DataInfo {
    let (ctor, fields) = expect_data(v, "DataInfo");
    match ctor {
        "DI" => DataInfo {
            name: decode_string(&fields[0]),
            // DN-112/M-1036: the `.myc` mirror does not yet encode `home` (DN-112 DoD item 8 — the
            // `.myc` enforcement/identity mirror is a flagged residual, riding the checkty
            // cross-nodule port); the differential normalizes both sides' `home` to bare before
            // comparing (see the `strip_home`/`normalize_want_types` call sites below).
            home: String::new(),
            params: decode_vec(&fields[1], decode_string),
            ctors: decode_vec(&fields[2], decode_ctor_info),
        },
        c => panic!("marshal decode_data_info: unexpected ctor {c}"),
    }
}

// ── L1Value → SURFACE decoders (register_traits output: TraitInfo carries surface FnSig/TypeRef) ─────
//
// register_traits' `Vec[TraitInfo]` output stores the traits' method sigs VERBATIM as SURFACE `FnSig`s
// (distinct from the KERNEL `KFnSig` the elab harness decodes), whose param/ret types are surface
// `TypeRef`s. So the differential needs a surface `FnSig` / `TypeRef` decoder family — the never-silent
// inverse of the mirror constructors, panicking on an unexpected ctor rather than mis-decoding (G2).

/// `WLit(u32)` / `WName(str)` → `ast::WidthRef`.
fn decode_widthref(v: &L1Value) -> WidthRef {
    let (ctor, fields) = expect_data(v, "WidthRef");
    match ctor {
        "WLit" => WidthRef::Lit(decode_u32(&fields[0])),
        "WName" => WidthRef::Name(decode_string(&fields[0])),
        c => panic!("marshal decode_widthref: unexpected ctor {c}"),
    }
}

/// The surface `BaseType` mirror (all encoded variants) → `ast::BaseType`. The never-silent inverse of
/// `encode_basetype`; recursive on `Seq`/`Named`/`Fn`/`Tuple` via `decode_typeref`. `Ambient` is never
/// encoded (its encoder panics), so it is not a decode arm — an unexpected ctor panics.
fn decode_basetype(v: &L1Value) -> BaseType {
    let (ctor, fields) = expect_data(v, "BaseType");
    match ctor {
        "KwBinary" => BaseType::Binary(decode_widthref(&fields[0])),
        "KwTernary" => BaseType::Ternary(decode_widthref(&fields[0])),
        "KwDense" => BaseType::Dense(decode_u32(&fields[0]), decode_scalar(&fields[1])),
        "Vsa" => BaseType::Vsa {
            model: decode_string(&fields[0]),
            dim: decode_u32(&fields[1]),
            sparsity: decode_sparsity(&fields[2]),
        },
        "KwSubstrate" => BaseType::Substrate(decode_string(&fields[0])),
        "KwSeq" => BaseType::Seq {
            elem: Box::new(decode_typeref(&fields[0])),
            len: decode_u32(&fields[1]),
        },
        "KwBytes" => BaseType::Bytes,
        "KwFloat" => BaseType::Float,
        "Named" => BaseType::Named(
            decode_string(&fields[0]),
            decode_vec(&fields[1], decode_typeref),
        ),
        "FnArrow" => BaseType::Fn(
            Box::new(decode_typeref(&fields[0])),
            Box::new(decode_typeref(&fields[1])),
        ),
        "Tuple" => BaseType::Tuple(decode_vec(&fields[0], decode_typeref)),
        c => panic!("marshal decode_basetype: unexpected ctor {c}"),
    }
}

/// `TR(base, guarantee)` → `ast::TypeRef`. `encode_typeref` always emits `None` for the guarantee slot
/// (every `resolve_ty` consumer discards it), so the fixtures' surface `TypeRef`s round-trip with
/// `guarantee: None`; a `Some(_)` would panic (never-silent — it is outside the encoded surface).
fn decode_typeref(v: &L1Value) -> TypeRef {
    let (ctor, fields) = expect_data(v, "TypeRef");
    match ctor {
        "TR" => TypeRef {
            base: decode_basetype(&fields[0]),
            guarantee: decode_option(&fields[1], |_| {
                panic!("marshal decode_typeref: guarantee slot is always None in this differential")
            }),
        },
        c => panic!("marshal decode_typeref: unexpected ctor {c}"),
    }
}

/// `Prm(name, ty)` → `ast::Param`.
fn decode_param(v: &L1Value) -> Param {
    let (ctor, fields) = expect_data(v, "Param");
    match ctor {
        "Prm" => Param {
            name: decode_string(&fields[0]),
            ty: decode_typeref(&fields[1]),
        },
        c => panic!("marshal decode_param: unexpected ctor {c}"),
    }
}

/// `PkType` / `PkWidth` → `ast::ParamKind`.
fn decode_param_kind(v: &L1Value) -> ParamKind {
    match expect_data(v, "ParamKind").0 {
        "PkType" => ParamKind::Type,
        "PkWidth" => ParamKind::Width,
        c => panic!("marshal decode_param_kind: unexpected ctor {c}"),
    }
}

/// `TRf(name, args)` → `ast::TraitRef`.
fn decode_trait_ref(v: &L1Value) -> TraitRef {
    let (ctor, fields) = expect_data(v, "TraitRef");
    match ctor {
        "TRf" => TraitRef {
            name: decode_string(&fields[0]),
            args: decode_vec(&fields[1], decode_typeref),
        },
        c => panic!("marshal decode_trait_ref: unexpected ctor {c}"),
    }
}

/// `TP(name, kind, bounds)` → `ast::TypeParam`.
fn decode_type_param(v: &L1Value) -> TypeParam {
    let (ctor, fields) = expect_data(v, "TypeParam");
    match ctor {
        "TP" => TypeParam {
            name: decode_string(&fields[0]),
            kind: decode_param_kind(&fields[1]),
            bounds: decode_vec(&fields[2], decode_trait_ref),
        },
        c => panic!("marshal decode_type_param: unexpected ctor {c}"),
    }
}

/// The SURFACE `FnSig` mirror `FS(name, type_params, value_params, ret, effects, budgets)` →
/// `ast::FnSig`. `effects` decodes from field 4 (empty in these fixtures); `effect_budgets` reads
/// field 5, which the fixtures keep `Nil` (`encode_fn_sig` asserts empty) — so the element decoder is
/// never invoked and the map is empty; a populated budget would panic (never-silent, outside surface).
fn decode_fn_sig(v: &L1Value) -> FnSig {
    let (ctor, fields) = expect_data(v, "FnSig");
    match ctor {
        "FS" => FnSig {
            name: decode_string(&fields[0]),
            params: decode_vec(&fields[1], decode_type_param),
            value_params: decode_vec(&fields[2], decode_param),
            ret: decode_typeref(&fields[3]),
            effects: decode_vec(&fields[4], decode_string),
            effect_budgets: decode_vec(&fields[5], |_| -> (String, u64) {
                panic!("marshal decode_fn_sig: effect budgets are empty in this differential")
            })
            .into_iter()
            .collect(),
        },
        c => panic!("marshal decode_fn_sig: unexpected ctor {c}"),
    }
}

/// `TrInfo(name, params, sigs)` → `checkty::TraitInfo` (the port's registry entry mirror).
fn decode_trait_info(v: &L1Value) -> TraitInfo {
    let (ctor, fields) = expect_data(v, "TraitInfo");
    match ctor {
        "TrInfo" => TraitInfo {
            name: decode_string(&fields[0]),
            params: decode_vec(&fields[1], decode_string),
            sigs: decode_vec(&fields[2], decode_fn_sig),
        },
        c => panic!("marshal decode_trait_info: unexpected ctor {c}"),
    }
}

/// Decode `register_traits`' returned registry (`Vec[TraitInfo]`) into a `BTreeMap` keyed by trait name
/// — the order-insensitive comparison surface against `checkty::register_traits`' `BTreeMap`. A
/// duplicate key panics (never-silent): the port maintains a one-entry-per-name invariant, so a dup is
/// a real port bug, surfaced rather than silently collapsed.
fn decode_traits_map(v: &L1Value) -> BTreeMap<String, TraitInfo> {
    let mut map = BTreeMap::new();
    for t in decode_vec(v, decode_trait_info) {
        assert!(
            map.insert(t.name.clone(), t).is_none(),
            "register_traits port produced a duplicate trait name (registry invariant broken)"
        );
    }
    map
}

// ── Rust → `.myc` fixture encoders (register-family INPUT types; built on shared primitives) ─────────

fn encode_vis(v: Vis) -> &'static str {
    match v {
        Vis::Private => "Private",
        Vis::Pub => "Pub",
    }
}

fn encode_names(names: &[String]) -> String {
    let mut s = String::from("Nil");
    for n in names.iter().rev() {
        s = format!("Cons({}, {})", encode_bytes(n), s);
    }
    s
}

fn encode_ctor(c: &Ctor) -> String {
    // M-1027 / DN-104: the semcore `Ct` mirror carries the `sealed` (`priv`) flag as its 3rd field.
    format!(
        "Ct({}, {}, {})",
        encode_bytes(&c.name),
        encode_typeref_list(&c.fields),
        if c.sealed { "True" } else { "False" }
    )
}

fn encode_ctor_list(cs: &[Ctor]) -> String {
    let mut s = String::from("Nil");
    for c in cs.iter().rev() {
        s = format!("Cons({}, {})", encode_ctor(c), s);
    }
    s
}

fn encode_type_decl(td: &TypeDecl) -> String {
    format!(
        "TD({}, {}, {}, {})",
        encode_vis(td.vis),
        encode_bytes(&td.name),
        encode_names(&td.params),
        encode_ctor_list(&td.ctors)
    )
}

fn encode_ctor_info(ci: &CtorInfo) -> String {
    format!(
        "CI({}, {})",
        encode_bytes(&ci.name),
        encode_ty_list(&ci.fields)
    )
}

fn encode_ctor_info_list(cis: &[CtorInfo]) -> String {
    let mut s = String::from("Nil");
    for ci in cis.iter().rev() {
        s = format!("Cons({}, {})", encode_ctor_info(ci), s);
    }
    s
}

fn encode_data_info(d: &DataInfo) -> String {
    format!(
        "DI({}, {}, {})",
        encode_bytes(&d.name),
        encode_names(&d.params),
        encode_ctor_info_list(&d.ctors)
    )
}

fn encode_data_info_list(ds: &[DataInfo]) -> String {
    let mut s = String::from("Nil");
    for d in ds.iter().rev() {
        s = format!("Cons({}, {})", encode_data_info(d), s);
    }
    s
}

// ── small fixture constructors (test bodies stay `assert over a case`) ──────────────────────────────

fn named(name: &str, args: Vec<TypeRef>) -> BaseType {
    BaseType::Named(name.to_owned(), args)
}

fn ctor(name: &str, fields: Vec<TypeRef>) -> Ctor {
    Ctor {
        name: name.to_owned(),
        fields,
        sealed: false,
    }
}

fn type_decl(name: &str, params: &[&str], ctors: Vec<Ctor>) -> TypeDecl {
    TypeDecl {
        vis: Vis::Private,
        name: name.to_owned(),
        params: params.iter().map(|s| (*s).to_owned()).collect(),
        ctors,
    }
}

/// A registered-type **shell** (empty ctors) — exactly what `register_types` inserts into `types`
/// before `resolve_ctors` runs, so a recursive field reference resolves.
fn shell(name: &str, params: &[&str]) -> DataInfo {
    DataInfo {
        home: String::new(), // DN-112/M-1036: test fixture, unqualified/bare identity
        name: name.to_owned(),
        params: params.iter().map(|s| (*s).to_owned()).collect(),
        ctors: vec![],
    }
}

fn types_map(types: &[DataInfo]) -> BTreeMap<String, DataInfo> {
    types.iter().map(|d| (d.name.clone(), d.clone())).collect()
}

// `decode_driver` shorthands (bare mirror-literal round-trips for the non-vacuity gate).
fn dd_ty(expr: &str) -> Ty {
    decode_driver("Ty", expr, decode_ty)
}
fn dd_ci(expr: &str) -> CtorInfo {
    decode_driver("CtorInfo", expr, decode_ctor_info)
}
fn dd_di(expr: &str) -> DataInfo {
    decode_driver("DataInfo", expr, decode_data_info)
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// Decoder non-vacuity: each new decoder arm must DISCRIMINATE on every dimension it reads (M-1013
// STEP 2 convention — decode two mirror literals differing in exactly one dimension, assert `!=`, so a
// decoder that dropped a dimension is caught rather than silently collapsing distinct values).
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn marshal_discriminates() {
    // decode_width (via TyBinary): variant tag, the WdLit u32, the WdVar string.
    assert_ne!(
        dd_ty(&format!("TyBinary(WdLit({}))", encode_u32(8))),
        dd_ty(&format!("TyBinary(WdVar({}))", encode_bytes("N")))
    );
    assert_ne!(
        dd_ty(&format!("TyBinary(WdLit({}))", encode_u32(8))),
        dd_ty(&format!("TyBinary(WdLit({}))", encode_u32(16)))
    );
    assert_ne!(
        dd_ty(&format!("TyBinary(WdVar({}))", encode_bytes("N"))),
        dd_ty(&format!("TyBinary(WdVar({}))", encode_bytes("M")))
    );

    // decode_ty variant tags.
    assert_ne!(
        dd_ty(&format!("TyBinary(WdLit({}))", encode_u32(8))),
        dd_ty(&format!("TyTernary(WdLit({}))", encode_u32(8)))
    );
    assert_ne!(dd_ty("TyBytes"), dd_ty("TyFloat"));
    assert_ne!(
        dd_ty(&format!("TyData({}, Nil)", encode_bytes("A"))),
        dd_ty(&format!("TyVar({})", encode_bytes("A")))
    );
    assert_ne!(
        dd_ty(&format!("TySubstrate({})", encode_bytes("a"))),
        dd_ty(&format!("TyVar({})", encode_bytes("a")))
    );

    // decode_scalar (via TyDense dtype): all four kinds distinct; plus the dim u32.
    assert_ne!(
        dd_ty(&format!("TyDense({}, SF16)", encode_u32(4))),
        dd_ty(&format!("TyDense({}, SBf16)", encode_u32(4)))
    );
    assert_ne!(
        dd_ty(&format!("TyDense({}, SBf16)", encode_u32(4))),
        dd_ty(&format!("TyDense({}, SF32)", encode_u32(4)))
    );
    assert_ne!(
        dd_ty(&format!("TyDense({}, SF32)", encode_u32(4))),
        dd_ty(&format!("TyDense({}, SF64)", encode_u32(4)))
    );
    assert_ne!(
        dd_ty(&format!("TyDense({}, SF16)", encode_u32(4))),
        dd_ty(&format!("TyDense({}, SF16)", encode_u32(8)))
    );

    // decode_sparsity + TyVsa fields (model, dim, sparsity).
    assert_ne!(
        dd_ty(&format!(
            "TyVsa({}, {}, SpDense)",
            encode_bytes("A"),
            encode_u32(4)
        )),
        dd_ty(&format!(
            "TyVsa({}, {}, SpSparse({}))",
            encode_bytes("A"),
            encode_u32(4),
            encode_u32(8)
        ))
    );
    assert_ne!(
        dd_ty(&format!(
            "TyVsa({}, {}, SpSparse({}))",
            encode_bytes("A"),
            encode_u32(4),
            encode_u32(8)
        )),
        dd_ty(&format!(
            "TyVsa({}, {}, SpSparse({}))",
            encode_bytes("A"),
            encode_u32(4),
            encode_u32(16)
        ))
    );
    assert_ne!(
        dd_ty(&format!(
            "TyVsa({}, {}, SpDense)",
            encode_bytes("A"),
            encode_u32(4)
        )),
        dd_ty(&format!(
            "TyVsa({}, {}, SpDense)",
            encode_bytes("B"),
            encode_u32(4)
        ))
    );
    assert_ne!(
        dd_ty(&format!(
            "TyVsa({}, {}, SpDense)",
            encode_bytes("A"),
            encode_u32(4)
        )),
        dd_ty(&format!(
            "TyVsa({}, {}, SpDense)",
            encode_bytes("A"),
            encode_u32(8)
        ))
    );

    // decode_ty TyData name + fields; TySeq elem + len; TyVar/TySubstrate string; TyFn param + ret.
    assert_ne!(
        dd_ty(&format!("TyData({}, Nil)", encode_bytes("A"))),
        dd_ty(&format!("TyData({}, Nil)", encode_bytes("B")))
    );
    assert_ne!(
        dd_ty(&format!("TyData({}, Nil)", encode_bytes("A"))),
        dd_ty(&format!(
            "TyData({}, Cons(TyBytes, Nil))",
            encode_bytes("A")
        ))
    );
    assert_ne!(
        dd_ty(&format!(
            "TyData({}, Cons(TyBytes, Nil))",
            encode_bytes("A")
        )),
        dd_ty(&format!(
            "TyData({}, Cons(TyFloat, Nil))",
            encode_bytes("A")
        ))
    );
    assert_ne!(
        dd_ty(&format!("TySeq(TyBytes, {})", encode_u32(2))),
        dd_ty(&format!("TySeq(TyFloat, {})", encode_u32(2)))
    );
    assert_ne!(
        dd_ty(&format!("TySeq(TyBytes, {})", encode_u32(2))),
        dd_ty(&format!("TySeq(TyBytes, {})", encode_u32(3)))
    );
    assert_ne!(
        dd_ty(&format!("TyVar({})", encode_bytes("A"))),
        dd_ty(&format!("TyVar({})", encode_bytes("B")))
    );
    assert_ne!(
        dd_ty(&format!("TySubstrate({})", encode_bytes("a"))),
        dd_ty(&format!("TySubstrate({})", encode_bytes("b")))
    );
    assert_ne!(
        dd_ty("TyFn(TyBytes, TyFloat)"),
        dd_ty("TyFn(TyFloat, TyFloat)")
    );
    assert_ne!(
        dd_ty("TyFn(TyBytes, TyFloat)"),
        dd_ty("TyFn(TyBytes, TyBytes)")
    );

    // decode_ctor_info (CI): name + fields.
    assert_ne!(
        dd_ci(&format!("CI({}, Nil)", encode_bytes("A"))),
        dd_ci(&format!("CI({}, Nil)", encode_bytes("B")))
    );
    assert_ne!(
        dd_ci(&format!("CI({}, Nil)", encode_bytes("A"))),
        dd_ci(&format!("CI({}, Cons(TyBytes, Nil))", encode_bytes("A")))
    );

    // decode_data_info (DI): name + params + ctors.
    assert_ne!(
        dd_di(&format!("DI({}, Nil, Nil)", encode_bytes("A"))),
        dd_di(&format!("DI({}, Nil, Nil)", encode_bytes("B")))
    );
    assert_ne!(
        dd_di(&format!("DI({}, Nil, Nil)", encode_bytes("A"))),
        dd_di(&format!(
            "DI({}, Cons({}, Nil), Nil)",
            encode_bytes("A"),
            encode_bytes("P")
        ))
    );
    assert_ne!(
        dd_di(&format!("DI({}, Nil, Nil)", encode_bytes("A"))),
        dd_di(&format!(
            "DI({}, Nil, Cons(CI({}, Nil), Nil))",
            encode_bytes("A"),
            encode_bytes("C")
        ))
    );
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// first_duplicate (LIVE — checkty::first_duplicate): None + the first-repeat cases (left to right).
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn first_duplicate_cases() {
    let cases: Vec<Vec<&str>> = vec![
        vec![],
        vec!["a"],
        vec!["a", "b", "c"],
        vec!["a", "b", "a"],      // → Some("a")
        vec!["x", "x"],           // → Some("x")
        vec!["a", "b", "b", "a"], // → Some("b") (first repeat)
    ];
    for (i, xs) in cases.iter().enumerate() {
        let owned: Vec<String> = xs.iter().map(|s| (*s).to_owned()).collect();
        let want: Option<String> = first_duplicate(&owned).cloned();
        assert_l1_marshal(
            &format!("first_duplicate_{i}"),
            &format!(
                "fn main() => Option[Bytes] = first_duplicate({});\n",
                encode_names(&owned)
            ),
            |v| decode_option(v, decode_string),
            want,
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// resolve_ctors (LIVE — checkty::resolve_ctors): monomorphic enum, generic recursive type, repr-typed
// fields, and the two refusals (unknown field type, duplicate ctor). Compared to the live oracle by
// Rust's derived `==` (Err normalized to `()`).
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn resolve_ctors_cases() {
    let cases: Vec<(&str, Vec<DataInfo>, TypeDecl)> = vec![
        // Monomorphic enum: Color = Red | Green | Blue.
        (
            "mono_enum",
            vec![],
            type_decl(
                "Color",
                &[],
                vec![
                    ctor("Red", vec![]),
                    ctor("Green", vec![]),
                    ctor("Blue", vec![]),
                ],
            ),
        ),
        // Generic recursive: List[A] = Nil | Cons(A, List[A]). The `List` shell (empty ctors) is in
        // `types`, exactly as `register_types` inserts it before calling `resolve_ctors`.
        (
            "generic_recursive",
            vec![shell("List", &["A"])],
            type_decl(
                "List",
                &["A"],
                vec![
                    ctor("Nil", vec![]),
                    ctor(
                        "Cons",
                        vec![
                            tref(named("A", vec![])),
                            tref(named("List", vec![tref(named("A", vec![]))])),
                        ],
                    ),
                ],
            ),
        ),
        // Repr-typed fields: Rec = Mk(Binary{8}, Bytes, Seq{Binary{8}, 4}).
        (
            "repr_fields",
            vec![],
            type_decl(
                "Rec",
                &[],
                vec![ctor(
                    "Mk",
                    vec![
                        tref(BaseType::Binary(WidthRef::Lit(8))),
                        tref(BaseType::Bytes),
                        tref(BaseType::Seq {
                            elem: Box::new(tref(BaseType::Binary(WidthRef::Lit(8)))),
                            len: 4,
                        }),
                    ],
                )],
            ),
        ),
        // Unknown type name in a field → Err (both sides).
        (
            "unknown_field",
            vec![],
            type_decl(
                "Bad",
                &[],
                vec![ctor("Mk", vec![tref(named("Nope", vec![]))])],
            ),
        ),
        // Duplicate constructor → Err (both sides).
        (
            "duplicate_ctor",
            vec![],
            type_decl("Dup", &[], vec![ctor("A", vec![]), ctor("A", vec![])]),
        ),
    ];
    for (label, types, td) in &cases {
        let map = types_map(types);
        let want = resolve_ctors(&map, td).map_err(|_| ());
        assert_l1_marshal(
            &format!("resolve_ctors_{label}"),
            &format!(
                "fn main() => Result[Vec[CtorInfo], Bytes] = resolve_ctors({}, {});\n",
                encode_data_info_list(types),
                encode_type_decl(td)
            ),
            |v| decode_result(v, |v| decode_vec(v, decode_ctor_info)),
            want,
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════════
// register_types (M-1013 STEP 3, PR-2/PR-2b) — the type-registry builder.
// ═══════════════════════════════════════════════════════════════════════════════════════════════════

// ── Nodule / Item mirror encoders (the FULL input surface — every item kind, PR-2b) ─────────────────

fn encode_path(p: &Path) -> String {
    format!("Pth({})", encode_names(&p.0))
}

/// `UP(path, glob)` — the `UsePath` mirror (M-1013 STEP 4).
fn encode_use_path(u: &crate::ast::UsePath) -> String {
    format!(
        "UP({}, {})",
        encode_path(&u.path),
        if u.glob { "True" } else { "False" }
    )
}

/// The FULL `Item` mirror (PR-2b + STEP 4's `ItUse`): every tuple-relevant item kind carries its data
/// field-for-field. `Item::Use` now carries its `UsePath` (M-1013 STEP 4 — `resolve_imports` reads it
/// directly; `collect_tuple_arities_item`'s `ItUse(_) => acc` arm keeps the tuple-walk a no-op, same
/// as before). `Default`/`DefaultPolicy`/`Derive` remain the tuple-free `ItOther` collapse (still
/// unread by both consumers — DN-142 §3.2's `DefaultPolicy` carries no tuple-relevant field either).
fn encode_item(it: &Item) -> String {
    match it {
        Item::Type(td) => format!("ItType({})", encode_type_decl(td)),
        Item::Fn(fd) => format!("ItFn({})", encode_fn_decl(fd)),
        Item::Trait(tr) => format!("ItTrait({})", encode_trait_decl(tr)),
        Item::Impl(id) => format!("ItImpl({})", encode_impl_decl(id)),
        Item::Object(od) => format!("ItObject({})", encode_object_decl(od)),
        Item::Lower(ld) => format!("ItLower({})", encode_lower_decl(ld)),
        Item::InherentImpl(iid) => format!("ItInherentImpl({})", encode_inherent_impl_decl(iid)),
        Item::Use(up) => format!("ItUse({})", encode_use_path(up)),
        Item::Default(_) | Item::DefaultPolicy(_) | Item::Derive(_) => "ItOther".to_owned(),
    }
}

// ── full-Item mirror encoders (PR-2b; the fn-body/pattern/signature legs' input surface) ─────────────

fn encode_paradigm(p: Paradigm) -> &'static str {
    match p {
        Paradigm::Binary => "PBinary",
        Paradigm::Ternary => "PTernary",
        Paradigm::Dense => "PDense",
        Paradigm::Vsa => "PVsa",
    }
}

/// A 64-bit MSB-first binary literal (the `Binary{64}` mirror leaf — the i64 in `Int`/`AmbientInt`).
fn encode_i64(n: i64) -> String {
    let bits = n as u64;
    let mut s = String::from("0b");
    for (count, i) in (0..64).rev().enumerate() {
        if count != 0 && count % 4 == 0 {
            s.push('_');
        }
        s.push(if (bits >> i) & 1 == 1 { '1' } else { '0' });
    }
    s
}

fn encode_expr_list(es: &[Expr]) -> String {
    let mut s = String::from("Nil");
    for e in es.iter().rev() {
        s = format!("Cons({}, {})", encode_expr(e), s);
    }
    s
}

fn encode_literal(l: &Literal) -> String {
    match l {
        Literal::Bin(s) => format!("Bin({})", encode_bytes(s)),
        Literal::Trit(s) => format!("Trit({})", encode_bytes(s)),
        Literal::Int(n) => format!("Int({})", encode_i64(*n)),
        Literal::AmbientInt(p, n) => {
            format!("AmbientInt({}, {})", encode_paradigm(*p), encode_i64(*n))
        }
        Literal::List(es) => format!("List({})", encode_expr_list(es)),
        Literal::Bytes(s) => format!("LBytes({})", encode_bytes(s)),
        Literal::Str(s) => format!("Str({})", encode_bytes(s)),
        Literal::Float(s) => format!("LFloat({})", encode_bytes(s)),
    }
}

fn encode_pattern(p: &Pattern) -> String {
    match p {
        Pattern::Wildcard => "PWildcard".to_owned(),
        Pattern::Lit(l) => format!("PLit({})", encode_literal(l)),
        Pattern::Ctor(n, subs) => {
            format!("PCtor({}, {})", encode_bytes(n), encode_pattern_list(subs))
        }
        Pattern::Ident(n) => format!("PIdent({})", encode_bytes(n)),
        Pattern::Tuple(subs) => format!("PTuple({})", encode_pattern_list(subs)),
        Pattern::Or(alts) => format!("POr({})", encode_pattern_list(alts)),
    }
}

fn encode_pattern_list(ps: &[Pattern]) -> String {
    let mut s = String::from("Nil");
    for p in ps.iter().rev() {
        s = format!("Cons({}, {})", encode_pattern(p), s);
    }
    s
}

fn encode_arm(a: &Arm) -> String {
    format!(
        "Ar({}, {})",
        encode_pattern(&a.pattern),
        encode_expr(&a.body)
    )
}

fn encode_arm_list(arms: &[Arm]) -> String {
    let mut s = String::from("Nil");
    for a in arms.iter().rev() {
        s = format!("Cons({}, {})", encode_arm(a), s);
    }
    s
}

fn encode_opt_typeref(t: &Option<TypeRef>) -> String {
    match t {
        None => "None".to_owned(),
        Some(t) => format!("Some({})", encode_typeref(t)),
    }
}

/// The FULL `Expr` mirror encoder, field-for-field with `semcore.myc`'s `Expr` (incl. the DN-102
/// `Try` variant — M-1025 ENB-2; represented-not-produced on the `.myc` side, like `Wrapping`).
fn encode_expr(e: &Expr) -> String {
    match e {
        Expr::Let {
            name,
            ty,
            bound,
            body,
        } => format!(
            "Let({}, {}, {}, {})",
            encode_bytes(name),
            encode_opt_typeref(ty),
            encode_expr(bound),
            encode_expr(body)
        ),
        Expr::If { cond, conseq, alt } => format!(
            "If({}, {}, {})",
            encode_expr(cond),
            encode_expr(conseq),
            encode_expr(alt)
        ),
        Expr::Match { scrutinee, arms } => {
            format!(
                "Match({}, {})",
                encode_expr(scrutinee),
                encode_arm_list(arms)
            )
        }
        Expr::For {
            x,
            xs,
            acc,
            init,
            body,
        } => format!(
            "For({}, {}, {}, {}, {})",
            encode_bytes(x),
            encode_expr(xs),
            encode_bytes(acc),
            encode_expr(init),
            encode_expr(body)
        ),
        Expr::Swap {
            value,
            target,
            policy,
        } => format!(
            "Swap({}, {}, {})",
            encode_expr(value),
            encode_typeref(target),
            encode_path(policy)
        ),
        Expr::WithParadigm { paradigm, body } => {
            format!(
                "WithParadigm({}, {})",
                encode_paradigm(*paradigm),
                encode_expr(body)
            )
        }
        Expr::Wild(b) => format!("Wild({})", encode_expr(b)),
        Expr::Spore(b) => format!("Spore({})", encode_expr(b)),
        Expr::Consume(b) => format!("Consume({})", encode_expr(b)),
        Expr::Wrapping(b) => format!("Wrapping({})", encode_expr(b)),
        Expr::Try(b) => format!("Try({})", encode_expr(b)),
        Expr::Colony(hs) => format!("Colony({})", encode_hypha_list(hs)),
        Expr::Lambda { params, body } => {
            format!(
                "Lambda({}, {})",
                encode_param_list(params),
                encode_expr(body)
            )
        }
        Expr::App { head, args } => {
            format!("App({}, {})", encode_expr(head), encode_expr_list(args))
        }
        Expr::Fuse { left, right } => {
            format!("Fuse({}, {})", encode_expr(left), encode_expr(right))
        }
        Expr::Reclaim { policy, body } => {
            format!("Reclaim({}, {})", encode_expr(policy), encode_expr(body))
        }
        Expr::Path(p) => format!("Path({})", encode_path(p)),
        Expr::Lit(l) => format!("Lit({})", encode_literal(l)),
        Expr::Ascribe(inner, t) => {
            format!("Ascribe({}, {})", encode_expr(inner), encode_typeref(t))
        }
        Expr::TupleLit(elems) => format!("TupleLit({})", encode_expr_list(elems)),
    }
}

fn encode_hypha_list(hs: &[crate::ast::Hypha]) -> String {
    let mut s = String::from("Nil");
    for h in hs.iter().rev() {
        let forage = match &h.forage {
            None => "None".to_owned(),
            Some(e) => format!("Some({})", encode_expr(e)),
        };
        s = format!("Cons(Hy({}, {}), {})", forage, encode_expr(&h.body), s);
    }
    s
}

fn encode_param(p: &Param) -> String {
    format!("Prm({}, {})", encode_bytes(&p.name), encode_typeref(&p.ty))
}

fn encode_param_list(ps: &[Param]) -> String {
    let mut s = String::from("Nil");
    for p in ps.iter().rev() {
        s = format!("Cons({}, {})", encode_param(p), s);
    }
    s
}

/// `FnSig` mirror. Type-params ARE encoded (the register_traits differential needs bounded method
/// type-params); `effects` / `effect_budgets` are never populated by these fixtures — those two slots
/// emit `Nil` (asserted empty below, so an encoder gap can never silently drop a populated one). The
/// tuple-walk fixtures keep `params` empty too, so `encode_type_param_list(&[])` = `Nil` — their
/// encoded text is unchanged.
fn encode_fn_sig(sig: &FnSig) -> String {
    assert!(
        sig.effects.is_empty() && sig.effect_budgets.is_empty(),
        "encode_fn_sig fixture invariant: effects / budgets must be empty (the register-family never \
         reads them; keep fixtures within the encoded surface)"
    );
    format!(
        "FS({}, {}, {}, {}, Nil, Nil)",
        encode_bytes(&sig.name),
        encode_type_param_list(&sig.params),
        encode_param_list(&sig.value_params),
        encode_typeref(&sig.ret)
    )
}

/// `ParamKind` mirror (ast.rs `Type` / `Width` → `PkType` / `PkWidth`).
fn encode_param_kind(k: &ParamKind) -> &'static str {
    match k {
        ParamKind::Type => "PkType",
        ParamKind::Width => "PkWidth",
    }
}

/// `TraitRef` mirror `TRf(name, args)` — a bound-position trait reference (ast.rs `TraitRef`).
fn encode_trait_ref(tr: &TraitRef) -> String {
    format!(
        "TRf({}, {})",
        encode_bytes(&tr.name),
        encode_typeref_list(&tr.args)
    )
}

fn encode_trait_ref_list(trs: &[TraitRef]) -> String {
    let mut s = String::from("Nil");
    for tr in trs.iter().rev() {
        s = format!("Cons({}, {})", encode_trait_ref(tr), s);
    }
    s
}

/// `TypeParam` mirror `TP(name, kind, bounds)` (ast.rs `TypeParam`).
fn encode_type_param(tp: &TypeParam) -> String {
    format!(
        "TP({}, {}, {})",
        encode_bytes(&tp.name),
        encode_param_kind(&tp.kind),
        encode_trait_ref_list(&tp.bounds)
    )
}

fn encode_type_param_list(tps: &[TypeParam]) -> String {
    let mut s = String::from("Nil");
    for tp in tps.iter().rev() {
        s = format!("Cons({}, {})", encode_type_param(tp), s);
    }
    s
}

fn encode_fn_decl(fd: &FnDecl) -> String {
    // vis / thaw / tier are not read by the tuple walk; fixtures keep them at the defaults.
    format!(
        "FD({}, {}, None, {}, {})",
        encode_vis(fd.vis),
        if fd.thaw { "True" } else { "False" },
        encode_fn_sig(&fd.sig),
        encode_expr(&fd.body)
    )
}

fn encode_fn_decl_list(fds: &[FnDecl]) -> String {
    let mut s = String::from("Nil");
    for fd in fds.iter().rev() {
        s = format!("Cons({}, {})", encode_fn_decl(fd), s);
    }
    s
}

fn encode_fn_sig_list(sigs: &[FnSig]) -> String {
    let mut s = String::from("Nil");
    for sig in sigs.iter().rev() {
        s = format!("Cons({}, {})", encode_fn_sig(sig), s);
    }
    s
}

fn encode_trait_decl(tr: &TraitDecl) -> String {
    format!(
        "TrD({}, {}, {}, {})",
        encode_vis(tr.vis),
        encode_bytes(&tr.name),
        encode_names(&tr.params),
        encode_fn_sig_list(&tr.sigs)
    )
}

fn encode_impl_decl(id: &ImplDecl) -> String {
    format!(
        "ImD({}, {}, {}, {})",
        encode_bytes(&id.trait_name),
        encode_typeref_list(&id.trait_args),
        encode_typeref(&id.for_ty),
        encode_fn_decl_list(&id.methods)
    )
}

fn encode_impl_decl_list(ids: &[ImplDecl]) -> String {
    let mut s = String::from("Nil");
    for id in ids.iter().rev() {
        s = format!("Cons({}, {})", encode_impl_decl(id), s);
    }
    s
}

fn encode_inherent_impl_decl(iid: &InherentImplDecl) -> String {
    // DN-103 / M-1026, bounded per DN-131 / M-1088: IID carries the impl-level type-parameter slot
    // (now bounded `TypeParam`s, via the same `encode_type_param_list` the `fn` slot uses) first.
    format!(
        "IID({}, {}, {})",
        encode_type_param_list(&iid.params),
        encode_typeref(&iid.for_ty),
        encode_fn_decl_list(&iid.methods)
    )
}

fn encode_via_decl(v: &ViaDecl) -> String {
    format!(
        "VD({}, {}, {})",
        encode_u32(v.field_idx),
        encode_bytes(&v.trait_name),
        encode_typeref_list(&v.trait_args)
    )
}

fn encode_via_decl_list(vs: &[ViaDecl]) -> String {
    let mut s = String::from("Nil");
    for v in vs.iter().rev() {
        s = format!("Cons({}, {})", encode_via_decl(v), s);
    }
    s
}

fn encode_object_decl(od: &ObjectDecl) -> String {
    format!(
        "OD({}, {}, {}, {}, {}, {}, {})",
        encode_vis(od.vis),
        encode_bytes(&od.name),
        encode_names(&od.params),
        encode_ctor(&od.ctor),
        encode_via_decl_list(&od.via_decls),
        encode_impl_decl_list(&od.impls),
        encode_fn_decl_list(&od.fns)
    )
}

fn encode_lower_decl(ld: &LowerDecl) -> String {
    let rhs = match &ld.rhs {
        LowerRhs::Expr(e) => format!("LrExpr({})", encode_expr(e)),
        LowerRhs::Impl(id) => format!("LrImpl({})", encode_impl_decl(id)),
    };
    format!(
        "LD({}, {}, {})",
        encode_bytes(&ld.name),
        encode_names(&ld.params),
        rhs
    )
}

fn encode_item_list(items: &[Item]) -> String {
    let mut s = String::from("Nil");
    for it in items.iter().rev() {
        s = format!("Cons({}, {})", encode_item(it), s);
    }
    s
}

fn encode_nodule(n: &Nodule) -> String {
    format!(
        "Nod({}, {}, {})",
        encode_path(&n.path),
        if n.std_sys { "True" } else { "False" },
        encode_item_list(&n.items)
    )
}

// ── L1Value decoder: the port's `Vec[DataInfo]` output → the oracle's `BTreeMap<String, DataInfo>` ───

/// Decode `register_types`' returned registry (`Vec[DataInfo]`) into a `BTreeMap` keyed by type name —
/// the order-insensitive comparison surface against `checkty::register_types`' mutated map. A duplicate
/// key panics (never-silent): `register_types` maintains a one-entry-per-name invariant, so a dup is a
/// real port bug, surfaced rather than silently collapsed by the `BTreeMap` insert.
fn decode_types_map(v: &L1Value) -> BTreeMap<String, DataInfo> {
    let mut map = BTreeMap::new();
    for d in decode_vec(v, decode_data_info) {
        assert!(
            map.insert(d.name.clone(), d).is_none(),
            "register_types port produced a duplicate type name (registry invariant broken)"
        );
    }
    map
}

// ── small fixture constructors (test bodies stay `assert over a case`) ──────────────────────────────

fn ty(td: TypeDecl) -> Item {
    Item::Type(td)
}

fn nodule(items: Vec<Item>) -> Nodule {
    Nodule {
        path: Path(vec!["d".to_owned()]),
        std_sys: false,
        items,
    }
}

/// The `Bool` prelude seed the real `register_nodule_decls` driver inserts before `register_types`
/// (checkty.rs) — matched on both sides so the port and oracle start from the identical registry.
fn seed_bool() -> BTreeMap<String, DataInfo> {
    let mut map = BTreeMap::new();
    map.insert("Bool".to_owned(), prelude());
    map
}

/// **DN-112 Rank 1 / M-1036, DoD item 8 (flagged `.myc`-parity residual).** The `.myc` self-hosted
/// mirror's `register_types`/`register_nodule_decls` port does not yet compute/encode nodule-
/// qualified identity at all (`DataInfo::home`, nor the qualified names embedded in a checked
/// `Ty::Data` field) — see `marshal_support::unqualify_types_map`'s doc comment for the full
/// rationale (DN-112 DoD item 8). Every `register_types`/`register_nodule_decls` oracle built here
/// is normalized through it before comparison.
use super::marshal_support::unqualify_types_map as strip_home_map;

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// register_types (LIVE — checkty::register_types): monomorphic, cross-referencing, generic, the two
// refusals (duplicate type name / duplicate type param), and a ctor-field TUPLE. Compared to the live
// oracle by Rust's derived `==` (Err normalized to `()`). The fn-body / pattern / signature tuple legs
// (FLAG-semcore-30, now CLOSED in PR-2b) get their own equality + closure witnesses in
// `collect_tuple_arities_cases` and `register_types_registers_leg_tuples` below.
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn register_types_cases() {
    let cases: Vec<(&str, Nodule)> = vec![
        // Single monomorphic type.
        (
            "mono",
            nodule(vec![ty(type_decl("A", &[], vec![ctor("MkA", vec![])]))]),
        ),
        // The second type's ctor field references the first (forward-resolved through the shells).
        (
            "cross_ref",
            nodule(vec![
                ty(type_decl("A", &[], vec![ctor("MkA", vec![])])),
                ty(type_decl(
                    "B",
                    &[],
                    vec![ctor("MkB", vec![tref(named("A", vec![]))])],
                )),
            ]),
        ),
        // Generic recursive type: List[A] = LNil | LCons(A, List[A]).
        (
            "generic",
            nodule(vec![ty(type_decl(
                "List",
                &["A"],
                vec![
                    ctor("LNil", vec![]),
                    ctor(
                        "LCons",
                        vec![
                            tref(named("A", vec![])),
                            tref(named("List", vec![tref(named("A", vec![]))])),
                        ],
                    ),
                ],
            ))]),
        ),
        // Duplicate type NAME → Err (both sides).
        (
            "dup_type_name",
            nodule(vec![
                ty(type_decl("A", &[], vec![ctor("MkA", vec![])])),
                ty(type_decl("A", &[], vec![ctor("MkA2", vec![])])),
            ]),
        ),
        // Duplicate type PARAM → Err (both sides).
        (
            "dup_type_param",
            nodule(vec![ty(type_decl(
                "P",
                &["X", "X"],
                vec![ctor("MkP", vec![])],
            ))]),
        ),
        // A ctor field that IS a tuple type `(A, B)` → the pre-pass registers Tuple$2 (the ctor-field
        // leg — the one leg present since PR-2, now part of the full walk).
        (
            "ctor_field_tuple",
            nodule(vec![
                ty(type_decl("A", &[], vec![ctor("MkA", vec![])])),
                ty(type_decl("B", &[], vec![ctor("MkB", vec![])])),
                ty(type_decl(
                    "C",
                    &[],
                    vec![ctor(
                        "MkC",
                        vec![tref(BaseType::Tuple(vec![
                            tref(named("A", vec![])),
                            tref(named("B", vec![])),
                        ]))],
                    )],
                )),
            ]),
        ),
    ];
    for (label, n) in &cases {
        let mut map = seed_bool();
        let res = register_types(&mut map, n);
        // DN-112/M-1036 DoD item 8: normalize `home` — see `strip_home`'s doc comment.
        let want = res.map(|()| strip_home_map(map)).map_err(|_| ());
        assert_l1_marshal(
            &format!("register_types_{label}"),
            &format!(
                "fn main() => Result[Vec[DataInfo], Bytes] = register_types({}, {});\n",
                encode_data_info_list(&[prelude()]),
                encode_nodule(n)
            ),
            |v| decode_result(v, decode_types_map),
            want,
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════════
// collect_tuple_arities (M-1013 STEP 3, PR-2b) — the FULL M-826 tuple pre-pass, now walking EVERY leg
// (type-decl ctor fields, fn bodies, `match` patterns, fn/trait/impl signatures, and the Object /
// InherentImpl / Lower item kinds). LIVE differential against `checkty::collect_tuple_arities` (the
// raw-nodule oracle), one fixture per leg. The port returns a `Vec[Binary{32}]` (order/dup-insensitive
// — `register_tuple_arities` presence-checks); both sides normalize to a `BTreeSet<u32>` before
// comparison. Closes FLAG-semcore-30.
// ═══════════════════════════════════════════════════════════════════════════════════════════════════

// ── fixture constructors (test bodies stay `assert over a case`) ────────────────────────────────────
fn param(name: &str, ty: TypeRef) -> Param {
    Param {
        name: name.to_owned(),
        ty,
    }
}
fn fn_sig(name: &str, value_params: Vec<Param>, ret: TypeRef) -> FnSig {
    FnSig {
        name: name.to_owned(),
        params: vec![],
        value_params,
        ret,
        effects: vec![],
        effect_budgets: BTreeMap::new(),
    }
}
fn fn_decl(sig: FnSig, body: Expr) -> FnDecl {
    FnDecl {
        vis: Vis::Private,
        thaw: false,
        tier: None,
        sig,
        body,
    }
}
/// A variable/path leaf expression (`a`).
fn var(name: &str) -> Expr {
    Expr::Path(Path(vec![name.to_owned()]))
}
/// A tuple `TypeRef` `(t0, t1, …)`.
fn tup_ty(elems: Vec<TypeRef>) -> TypeRef {
    tref(BaseType::Tuple(elems))
}
/// A bare named `TypeRef` `Name` (no args).
fn nm(name: &str) -> TypeRef {
    tref(named(name, vec![]))
}
/// The oracle's arities as a `BTreeSet<u32>` (order-insensitive comparison surface).
fn oracle_arities(n: &Nodule) -> BTreeSet<u32> {
    collect_tuple_arities(n)
        .into_iter()
        .map(|a| a as u32)
        .collect()
}

#[test]
fn collect_tuple_arities_cases() {
    let cases: Vec<(&str, Nodule)> = vec![
        ("empty", nodule(vec![])),
        // Type-decl ctor field `(A, B)` — the ItType leg (re-pinned from PR-2).
        (
            "ctor_field",
            nodule(vec![ty(type_decl(
                "C",
                &[],
                vec![ctor("MkC", vec![tup_ty(vec![nm("A"), nm("B")])])],
            ))]),
        ),
        // fn BODY: `let x = (a, b) in x` — the Expr leg (formerly deferred).
        (
            "fn_body_let",
            nodule(vec![Item::Fn(fn_decl(
                fn_sig("f", vec![], nm("A")),
                Expr::Let {
                    name: "x".to_owned(),
                    ty: None,
                    bound: Box::new(Expr::TupleLit(vec![var("a"), var("b")])),
                    body: Box::new(var("x")),
                },
            ))]),
        ),
        // fn body NESTED tuple `(a, (b, c, d))` — arities {2, 3}.
        (
            "fn_body_nested",
            nodule(vec![Item::Fn(fn_decl(
                fn_sig("f", vec![], nm("A")),
                Expr::TupleLit(vec![
                    var("a"),
                    Expr::TupleLit(vec![var("b"), var("c"), var("d")]),
                ]),
            ))]),
        ),
        // `match` PATTERN `(p, q) =>` — the Pattern leg (formerly deferred). Also exercises a literal
        // pattern element + a literal tuple element (encode_literal / encode_i64 coverage). {2}.
        (
            "match_pattern_and_literals",
            nodule(vec![Item::Fn(fn_decl(
                fn_sig("g", vec![param("s", nm("A"))], nm("A")),
                Expr::Match {
                    scrutinee: Box::new(Expr::TupleLit(vec![var("a"), Expr::Lit(Literal::Int(5))])),
                    arms: vec![Arm {
                        pattern: Pattern::Tuple(vec![
                            Pattern::Lit(Literal::Int(1)),
                            Pattern::Ident("q".to_owned()),
                        ]),
                        body: var("q"),
                    }],
                },
            ))]),
        ),
        // fn signature PARAM `x: (A, B, C)` — the sig leg, arity {3}.
        (
            "fn_sig_param",
            nodule(vec![Item::Fn(fn_decl(
                fn_sig(
                    "h",
                    vec![param("x", tup_ty(vec![nm("A"), nm("B"), nm("C")]))],
                    nm("A"),
                ),
                var("x"),
            ))]),
        ),
        // fn signature RETURN `=> (A, B)` — the sig leg, arity {2}.
        (
            "fn_ret",
            nodule(vec![Item::Fn(fn_decl(
                fn_sig("k", vec![], tup_ty(vec![nm("A"), nm("B")])),
                var("x"),
            ))]),
        ),
        // trait signature — the ItTrait leg, arity {2}.
        (
            "trait_sig",
            nodule(vec![Item::Trait(TraitDecl {
                vis: Vis::Private,
                name: "Tr".to_owned(),
                params: vec![],
                sigs: vec![fn_sig(
                    "t",
                    vec![param("x", tup_ty(vec![nm("A"), nm("B")]))],
                    nm("C"),
                )],
            })]),
        ),
        // impl — trait_args (A,B,C) {3}, for_ty (A,B) {2}, method sig (A,B,C,D) {4} ⇒ {2,3,4}.
        (
            "impl_leg",
            nodule(vec![Item::Impl(ImplDecl {
                trait_name: "Cmp".to_owned(),
                trait_args: vec![tup_ty(vec![nm("A"), nm("B"), nm("C")])],
                for_ty: tup_ty(vec![nm("A"), nm("B")]),
                methods: vec![fn_decl(
                    fn_sig(
                        "m",
                        vec![param("x", tup_ty(vec![nm("A"), nm("B"), nm("C"), nm("D")]))],
                        nm("A"),
                    ),
                    var("x"),
                )],
            })]),
        ),
        // object — ctor field (A,B) {2}, inherent fn body (a,b,c) {3}. A `via` clause carries a 5-tuple
        // trait-arg that the oracle DELIBERATELY skips (via_decls is not walked), so it must NOT appear
        // ⇒ {2,3} (the dead-field faithfulness witness).
        (
            "object_leg",
            nodule(vec![Item::Object(ObjectDecl {
                vis: Vis::Private,
                name: "O".to_owned(),
                params: vec![],
                ctor: ctor("MkO", vec![tup_ty(vec![nm("A"), nm("B")])]),
                via_decls: vec![ViaDecl {
                    field_idx: 0,
                    trait_name: "Cmp".to_owned(),
                    trait_args: vec![tup_ty(vec![nm("A"), nm("B"), nm("C"), nm("D"), nm("E")])],
                }],
                impls: vec![],
                fns: vec![fn_decl(
                    fn_sig("f", vec![], nm("A")),
                    Expr::TupleLit(vec![var("a"), var("b"), var("c")]),
                )],
            })]),
        ),
        // inherent impl — for_ty (A,B) {2}, method sig (A,B,C) {3} ⇒ {2,3}.
        (
            "inherent_impl_leg",
            nodule(vec![Item::InherentImpl(InherentImplDecl {
                params: vec![],
                for_ty: tup_ty(vec![nm("A"), nm("B")]),
                methods: vec![fn_decl(
                    fn_sig(
                        "m",
                        vec![param("x", tup_ty(vec![nm("A"), nm("B"), nm("C")]))],
                        nm("A"),
                    ),
                    var("x"),
                )],
            })]),
        ),
        // lower — Expr rhs `(a, b)` ⇒ {2}.
        (
            "lower_expr_leg",
            nodule(vec![Item::Lower(LowerDecl {
                name: "L".to_owned(),
                params: vec!["T".to_owned()],
                value_params: vec![],
                rhs: LowerRhs::Expr(Expr::TupleLit(vec![var("a"), var("b")])),
            })]),
        ),
        // lower — Impl rhs whose method sig is (A,B,C) ⇒ {3}.
        (
            "lower_impl_leg",
            nodule(vec![Item::Lower(LowerDecl {
                name: "L2".to_owned(),
                params: vec!["T".to_owned()],
                value_params: vec![],
                rhs: LowerRhs::Impl(ImplDecl {
                    trait_name: "Cmp".to_owned(),
                    trait_args: vec![],
                    for_ty: nm("T"),
                    methods: vec![fn_decl(
                        fn_sig(
                            "m",
                            vec![param("x", tup_ty(vec![nm("A"), nm("B"), nm("C")]))],
                            nm("A"),
                        ),
                        var("x"),
                    )],
                }),
            })]),
        ),
        // Use / Default / Derive — all three tuple-free for `collect_tuple_arities` (M-1013 STEP 4:
        // `Use` now carries its `UsePath` as `ItUse(..)` rather than collapsing to `ItOther`, but the
        // tuple-walk's `ItUse(_) => acc` arm is still a no-op, so this case's expectation is
        // unaffected). Derive's `for_ty` is a tuple `(A, B)` the ORACLE deliberately skips
        // (`Item::Derive(_) => {}`), so the result is {}.
        (
            "otherkinds_free",
            nodule(vec![
                Item::Use(crate::ast::UsePath {
                    phylum: None,
                    path: Path(vec!["m".to_owned(), "X".to_owned()]),
                    glob: false,
                }),
                Item::Default(Paradigm::Binary),
                Item::Derive(DeriveDecl {
                    name: "D".to_owned(),
                    for_ty: tup_ty(vec![nm("A"), nm("B")]),
                }),
            ]),
        ),
        // Mixed: ctor field {2}, fn body {3}, a 4-arm match pattern {4} — union {2,3,4}, deduped+sorted.
        (
            "mixed",
            nodule(vec![
                ty(type_decl(
                    "C",
                    &[],
                    vec![ctor("MkC", vec![tup_ty(vec![nm("A"), nm("B")])])],
                )),
                Item::Fn(fn_decl(
                    fn_sig("f", vec![], nm("A")),
                    Expr::TupleLit(vec![var("a"), var("b"), var("c")]),
                )),
                Item::Fn(fn_decl(
                    fn_sig("g", vec![param("s", nm("A"))], nm("A")),
                    Expr::Match {
                        scrutinee: Box::new(var("s")),
                        arms: vec![Arm {
                            pattern: Pattern::Tuple(vec![
                                Pattern::Ident("p".to_owned()),
                                Pattern::Ident("q".to_owned()),
                                Pattern::Ident("r".to_owned()),
                                Pattern::Ident("w".to_owned()),
                            ]),
                            body: var("p"),
                        }],
                    },
                )),
            ]),
        ),
    ];
    for (label, n) in &cases {
        let want = oracle_arities(n);
        assert_l1_marshal(
            &format!("collect_tuple_arities_{label}"),
            &format!(
                "fn main() => Vec[Binary{{32}}] = collect_tuple_arities({}, Nil);\n",
                encode_item_list(&n.items)
            ),
            |v| {
                decode_vec(v, decode_u32)
                    .into_iter()
                    .collect::<BTreeSet<u32>>()
            },
            want,
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// FLAG-semcore-30 CLOSED (M-1013 STEP 3, PR-2b). The formerly-deferred legs (fn body / `match` pattern
// / fn signature) are now walked by `register_types`' pre-pass, so a tuple appearing ONLY in such a
// leg IS pre-registered — matching the full Rust `register_types` byte-for-byte (Err normalized to
// `()`). This is the register_types-level closure witness; `collect_tuple_arities_cases` above is the
// per-leg detail.
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn register_types_registers_leg_tuples() {
    // A nodule whose ONLY tuple usages are in formerly-deferred legs: a fn body `(a, b)` {2} and a fn
    // signature param `x: (A, B, C)` {3} — no ctor-field tuple anywhere.
    let n = nodule(vec![
        Item::Fn(fn_decl(
            fn_sig("f", vec![], nm("A")),
            Expr::TupleLit(vec![var("a"), var("b")]),
        )),
        Item::Fn(fn_decl(
            fn_sig(
                "h",
                vec![param("x", tup_ty(vec![nm("A"), nm("B"), nm("C")]))],
                nm("A"),
            ),
            var("x"),
        )),
    ]);

    // (1) register_types port ↔ oracle: identical registry, INCLUDING the leg-derived Tuple$2/Tuple$3.
    // DN-112/M-1036 DoD item 8: normalize `home` — see `strip_home`'s doc comment.
    let mut map = seed_bool();
    let want = register_types(&mut map, &n)
        .map(|()| strip_home_map(map))
        .map_err(|_| ());
    assert_l1_marshal(
        "register_types_leg_tuples",
        &format!(
            "fn main() => Result[Vec[DataInfo], Bytes] = register_types({}, {});\n",
            encode_data_info_list(&[prelude()]),
            encode_nodule(&n)
        ),
        |v| decode_result(v, decode_types_map),
        want,
    );

    // (2) Direct closure witness: the fn-body tuple `(a, b)` — NOT registered under FLAG-30 — is now
    // present as Tuple$2 in the port's registry.
    let tuple2_present = decode_driver(
        "Option[Bytes]",
        &format!(
            "match register_types({}, {}) {{ Err(_) => None, \
             Ok(types) => match types_lookup(types, {}) {{ None => None, Some(d) => Some(di_name(d)) }} }}",
            encode_data_info_list(&[prelude()]),
            encode_nodule(&n),
            encode_bytes("Tuple$2")
        ),
        |v| decode_option(v, decode_string),
    );
    assert_eq!(
        tuple2_present,
        Some("Tuple$2".to_owned()),
        "PR-2b: a fn-body tuple must now be pre-registered (FLAG-semcore-30 closed)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// The never-silent FLOOR is unchanged by PR-2b: a tuple that appears NOWHERE in the nodule is still
// not registered, and resolving it Errs explicitly (never a silently-missing `Tuple$N` — G2/VR-5).
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn register_types_unreferenced_tuple_still_errs_never_silent() {
    // A, B: nullary types, NO tuple anywhere.
    let a = encode_type_decl(&type_decl("A", &[], vec![ctor("MkA", vec![])]));
    let b = encode_type_decl(&type_decl("B", &[], vec![ctor("MkB", vec![])]));
    let nod = format!("Nod(Pth(Nil), False, Cons(ItType({a}), Cons(ItType({b}), Nil)))");
    let seed = encode_data_info_list(&[prelude()]);

    let resolved = decode_driver(
        "Result[Pair[Ty, Option[Strength]], Bytes]",
        &format!(
            "match register_types({seed}, {nod}) {{ Err(e) => Err(e), \
             Ok(types) => resolve_ty(types, Nil, {}) }}",
            encode_typeref(&tref(BaseType::Tuple(vec![
                tref(named("A", vec![])),
                tref(named("B", vec![])),
            ])))
        ),
        |v| decode_result(v, |_| ()),
    );
    assert_eq!(
        resolved,
        Err(()),
        "an unreferenced tuple must surface as an explicit resolve_ty Err (never-silent, G2/VR-5)"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════════
// register_traits (M-1013 STEP 3) — the TRAIT pass. LIVE differential against `checkty::register_traits`
// (checkty.rs 3016-3083): the two-pass registration (per-trait checks + method-sig resolution, then the
// forward-reference-tolerant bound-validation pass). The port returns a `Vec[TraitInfo]`; both sides
// normalize to a name-keyed `BTreeMap<String, TraitInfo>` (order-insensitive), Err → `()`.
// ═══════════════════════════════════════════════════════════════════════════════════════════════════

// ── fixture constructors (test bodies stay `assert over a case`) ────────────────────────────────────
fn it_trait(td: TraitDecl) -> Item {
    Item::Trait(td)
}
fn trait_decl(name: &str, params: &[&str], sigs: Vec<FnSig>) -> TraitDecl {
    TraitDecl {
        vis: Vis::Private,
        name: name.to_owned(),
        params: params.iter().map(|s| (*s).to_owned()).collect(),
        sigs,
    }
}
/// An unbounded **type** parameter `T` (the §11 identity case).
fn tparam(name: &str) -> TypeParam {
    TypeParam {
        name: name.to_owned(),
        kind: ParamKind::Type,
        bounds: vec![],
    }
}
/// A **bounded** type parameter `T: b0 + b1 + …` (RFC-0019 §4.1 dictionary site).
fn tparam_bounded(name: &str, bounds: Vec<TraitRef>) -> TypeParam {
    TypeParam {
        name: name.to_owned(),
        kind: ParamKind::Type,
        bounds,
    }
}
/// A bare bound-position trait reference `Cmp` (no type args).
fn trait_ref(name: &str) -> TraitRef {
    TraitRef {
        name: name.to_owned(),
        args: vec![],
    }
}
/// A method `FnSig` carrying its own type-params (`fn_sig` above always leaves them empty).
fn fn_sig_tp(name: &str, params: Vec<TypeParam>, value_params: Vec<Param>, ret: TypeRef) -> FnSig {
    FnSig {
        name: name.to_owned(),
        params,
        value_params,
        ret,
        effects: vec![],
        effect_budgets: BTreeMap::new(),
    }
}

#[test]
fn register_traits_cases() {
    // `D`: a registered data type so a method value-param/return `D` resolves (the register_nodule_decls
    // driver would have registered it via `register_types` first; here it is seeded directly).
    let with_d = || vec![shell("D", &[])];
    let cases: Vec<(&str, Vec<DataInfo>, Nodule)> = vec![
        // No traits at all → an empty registry (both sides).
        ("empty", vec![], nodule(vec![])),
        // A non-trait item is skipped (mirror of `let Item::Trait(td) = item else { continue }`); the
        // one trait still registers. The Fn's body/sig are irrelevant to register_traits.
        (
            "skips_non_trait",
            with_d(),
            nodule(vec![
                Item::Fn(fn_decl(fn_sig("f", vec![], nm("D")), var("x"))),
                it_trait(trait_decl(
                    "Show",
                    &[],
                    vec![fn_sig("show", vec![param("x", nm("D"))], nm("D"))],
                )),
            ]),
        ),
        // Single trait, single method — the baseline Ok.
        (
            "single_ok",
            with_d(),
            nodule(vec![it_trait(trait_decl(
                "Show",
                &[],
                vec![fn_sig("show", vec![param("x", nm("D"))], nm("D"))],
            ))]),
        ),
        // Multi-method trait (distinct method names) — Ok.
        (
            "multi_method",
            with_d(),
            nodule(vec![it_trait(trait_decl(
                "Two",
                &[],
                vec![
                    fn_sig("a", vec![param("x", nm("D"))], nm("D")),
                    fn_sig("b", vec![param("y", nm("D"))], nm("D")),
                ],
            ))]),
        ),
        // A trait type-parameter `S` in scope over its method sig (`fn id(x: S) => S`) — Ok.
        (
            "trait_param_in_scope",
            vec![],
            nodule(vec![it_trait(trait_decl(
                "Id",
                &["S"],
                vec![fn_sig("id", vec![param("x", nm("S"))], nm("S"))],
            ))]),
        ),
        // A method whose OWN type-param `T` extends the tyvar scope so `x: T` / `=> T` resolve — Ok.
        // Without the `param_names()` extension (checkty.rs 3045-3046) `T` would be unknown ⇒ this
        // would Err; the Ok/Ok parity witnesses the port performs the extension.
        (
            "method_tyvar_extends_scope",
            vec![],
            nodule(vec![it_trait(trait_decl(
                "Gen",
                &[],
                vec![fn_sig_tp(
                    "f",
                    vec![tparam("T")],
                    vec![param("x", nm("T"))],
                    nm("T"),
                )],
            ))]),
        ),
        // Method type-param bound naming a KNOWN trait `A` (declared earlier) — Ok.
        (
            "bound_known_trait",
            vec![],
            nodule(vec![
                it_trait(trait_decl("A", &[], vec![])),
                it_trait(trait_decl(
                    "B",
                    &[],
                    vec![fn_sig_tp(
                        "f",
                        vec![tparam_bounded("T", vec![trait_ref("A")])],
                        vec![param("x", nm("T"))],
                        nm("T"),
                    )],
                )),
            ]),
        ),
        // Bound FORWARD-references a later-declared trait `Later` — Ok, precisely because bound
        // validation is a SECOND pass over the complete registry (checkty.rs 3058-3081).
        (
            "bound_forward_ref",
            vec![],
            nodule(vec![
                it_trait(trait_decl(
                    "Uses",
                    &[],
                    vec![fn_sig_tp(
                        "f",
                        vec![tparam_bounded("T", vec![trait_ref("Later")])],
                        vec![param("x", nm("T"))],
                        nm("T"),
                    )],
                )),
                it_trait(trait_decl("Later", &[], vec![])),
            ]),
        ),
        // Duplicate trait type-PARAMETER → Err (checkty.rs 3024).
        (
            "dup_type_param",
            vec![],
            nodule(vec![it_trait(trait_decl("Bad", &["X", "X"], vec![]))]),
        ),
        // Duplicate trait NAME → Err (checkty.rs 3030).
        (
            "dup_trait_name",
            with_d(),
            nodule(vec![
                it_trait(trait_decl(
                    "Dup",
                    &[],
                    vec![fn_sig("m", vec![param("x", nm("D"))], nm("D"))],
                )),
                it_trait(trait_decl(
                    "Dup",
                    &[],
                    vec![fn_sig("n", vec![param("y", nm("D"))], nm("D"))],
                )),
            ]),
        ),
        // Duplicate METHOD name within a trait → Err (checkty.rs 3036).
        (
            "dup_method",
            with_d(),
            nodule(vec![it_trait(trait_decl(
                "M",
                &[],
                vec![
                    fn_sig("m", vec![param("x", nm("D"))], nm("D")),
                    fn_sig("m", vec![param("y", nm("D"))], nm("D")),
                ],
            ))]),
        ),
        // Method value-param type does not resolve (`Nope` is neither a tyvar nor a registered type) →
        // Err (checkty.rs 3047 via check_sig_resolves / resolve_ty).
        (
            "unresolvable_method_type",
            with_d(),
            nodule(vec![it_trait(trait_decl(
                "U",
                &[],
                vec![fn_sig("f", vec![param("x", nm("Nope"))], nm("D"))],
            ))]),
        ),
        // Method type-param bound names an UNKNOWN trait `Nope` → Err (checkty.rs 3067, second pass).
        (
            "bound_unknown_trait",
            vec![],
            nodule(vec![it_trait(trait_decl(
                "V",
                &[],
                vec![fn_sig_tp(
                    "f",
                    vec![tparam_bounded("T", vec![trait_ref("Nope")])],
                    vec![param("x", nm("T"))],
                    nm("T"),
                )],
            ))]),
        ),
    ];
    for (label, types, n) in &cases {
        let map = types_map(types);
        let want = register_traits(&map, n).map_err(|_| ());
        assert_l1_marshal(
            &format!("register_traits_{label}"),
            &format!(
                "fn main() => Result[Vec[TraitInfo], Bytes] = register_traits({}, {});\n",
                encode_data_info_list(types),
                encode_nodule(n)
            ),
            |v| decode_result(v, decode_traits_map),
            want,
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// Decoder non-vacuity for the SURFACE-FnSig decoder family (M-1013 STEP 2 convention): each new
// decoder arm must DISCRIMINATE on every dimension it reads — two mirror literals differing in exactly
// one dimension must decode `!=`, so a decoder that dropped a dimension is caught, not silently
// collapsed. Covers decode_{trait_info, fn_sig, type_param, trait_ref, param, param_kind, typeref,
// basetype, widthref}.
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn marshal_discriminates_traits() {
    fn dd_trinfo(expr: &str) -> TraitInfo {
        decode_driver("TraitInfo", expr, decode_trait_info)
    }
    fn dd_fnsig(expr: &str) -> FnSig {
        decode_driver("FnSig", expr, decode_fn_sig)
    }
    fn dd_tp(expr: &str) -> TypeParam {
        decode_driver("TypeParam", expr, decode_type_param)
    }
    fn dd_tref(expr: &str) -> TypeRef {
        decode_driver("TypeRef", expr, decode_typeref)
    }

    let b_a = encode_bytes("A");
    let b_b = encode_bytes("B");
    let sig_m = format!(
        "FS({}, Nil, Nil, TR(KwBytes, None), Nil, Nil)",
        encode_bytes("m")
    );

    // decode_trait_info: name / params / sigs.
    assert_ne!(
        dd_trinfo(&format!("TrInfo({b_a}, Nil, Nil)")),
        dd_trinfo(&format!("TrInfo({b_b}, Nil, Nil)"))
    );
    assert_ne!(
        dd_trinfo(&format!("TrInfo({b_a}, Nil, Nil)")),
        dd_trinfo(&format!("TrInfo({b_a}, Cons({b_b}, Nil), Nil)"))
    );
    assert_ne!(
        dd_trinfo(&format!("TrInfo({b_a}, Nil, Nil)")),
        dd_trinfo(&format!("TrInfo({b_a}, Nil, Cons({sig_m}, Nil))"))
    );

    // decode_fn_sig: name / type_params / value_params / ret.
    assert_ne!(
        dd_fnsig(&format!(
            "FS({}, Nil, Nil, TR(KwBytes, None), Nil, Nil)",
            encode_bytes("m")
        )),
        dd_fnsig(&format!(
            "FS({}, Nil, Nil, TR(KwBytes, None), Nil, Nil)",
            encode_bytes("n")
        ))
    );
    assert_ne!(
        dd_fnsig(&format!(
            "FS({}, Nil, Nil, TR(KwBytes, None), Nil, Nil)",
            encode_bytes("m")
        )),
        dd_fnsig(&format!(
            "FS({}, Cons(TP({}, PkType, Nil), Nil), Nil, TR(KwBytes, None), Nil, Nil)",
            encode_bytes("m"),
            encode_bytes("T")
        ))
    );
    assert_ne!(
        dd_fnsig(&format!(
            "FS({}, Nil, Nil, TR(KwBytes, None), Nil, Nil)",
            encode_bytes("m")
        )),
        dd_fnsig(&format!(
            "FS({}, Nil, Cons(Prm({}, TR(KwBytes, None)), Nil), TR(KwBytes, None), Nil, Nil)",
            encode_bytes("m"),
            encode_bytes("x")
        ))
    );
    assert_ne!(
        dd_fnsig(&format!(
            "FS({}, Nil, Nil, TR(KwBytes, None), Nil, Nil)",
            encode_bytes("m")
        )),
        dd_fnsig(&format!(
            "FS({}, Nil, Nil, TR(KwFloat, None), Nil, Nil)",
            encode_bytes("m")
        ))
    );

    // decode_type_param: name / kind / bounds.
    assert_ne!(
        dd_tp(&format!("TP({}, PkType, Nil)", encode_bytes("T"))),
        dd_tp(&format!("TP({}, PkType, Nil)", encode_bytes("U")))
    );
    assert_ne!(
        dd_tp(&format!("TP({}, PkType, Nil)", encode_bytes("T"))),
        dd_tp(&format!("TP({}, PkWidth, Nil)", encode_bytes("T")))
    );
    assert_ne!(
        dd_tp(&format!("TP({}, PkType, Nil)", encode_bytes("T"))),
        dd_tp(&format!(
            "TP({}, PkType, Cons(TRf({}, Nil), Nil))",
            encode_bytes("T"),
            encode_bytes("C")
        ))
    );

    // decode_trait_ref: name / args (via the TypeParam bounds surface).
    assert_ne!(
        dd_tp(&format!(
            "TP({}, PkType, Cons(TRf({}, Nil), Nil))",
            encode_bytes("T"),
            encode_bytes("C")
        )),
        dd_tp(&format!(
            "TP({}, PkType, Cons(TRf({}, Nil), Nil))",
            encode_bytes("T"),
            encode_bytes("D")
        ))
    );
    assert_ne!(
        dd_tp(&format!(
            "TP({}, PkType, Cons(TRf({}, Nil), Nil))",
            encode_bytes("T"),
            encode_bytes("C")
        )),
        dd_tp(&format!(
            "TP({}, PkType, Cons(TRf({}, Cons(TR(KwBytes, None), Nil)), Nil))",
            encode_bytes("T"),
            encode_bytes("C")
        ))
    );

    // decode_typeref / decode_basetype: variant tags + the Named name/args + Tuple + widthref.
    assert_ne!(dd_tref("TR(KwBytes, None)"), dd_tref("TR(KwFloat, None)"));
    assert_ne!(
        dd_tref(&format!("TR(Named({b_a}, Nil), None)")),
        dd_tref(&format!("TR(Named({b_b}, Nil), None)"))
    );
    assert_ne!(
        dd_tref(&format!("TR(Named({b_a}, Nil), None)")),
        dd_tref(&format!(
            "TR(Named({b_a}, Cons(TR(KwBytes, None), Nil)), None)"
        ))
    );
    assert_ne!(
        dd_tref(&format!("TR(Named({b_a}, Nil), None)")),
        dd_tref(&format!(
            "TR(Tuple(Cons(TR(Named({b_a}, Nil), None), Cons(TR(Named({b_b}, Nil), None), Nil))), None)"
        ))
    );
    assert_ne!(
        dd_tref(&format!("TR(KwBinary(WLit({})), None)", encode_u32(8))),
        dd_tref(&format!("TR(KwBinary(WLit({})), None)", encode_u32(16)))
    );
    assert_ne!(
        dd_tref(&format!("TR(KwBinary(WLit({})), None)", encode_u32(8))),
        dd_tref(&format!("TR(KwBinary(WName({})), None)", encode_bytes("N")))
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════════
// register_instances (M-1013 STEP 3, PR-3) — the IMPL pass (registration + coherence). LIVE differential
// against `checkty::register_instances` (checkty.rs 3116-3238): the eight checks in the oracle's exact
// order (unknown-trait → concrete resolve → arity → head → orphan → uniqueness → method-set → insert).
// The port returns a `Vec[InstanceInfo]`; both sides normalize to a `BTreeMap<(String,String),
// InstanceInfo>` keyed by `(trait_name, type_head(for_ty))` (order-insensitive), `Err` → `()`.
//
// FLAG-semcore-33 RESOLVED: `checkty::CoherenceView.types` was widened to `pub(crate)` (matching
// `.traits`) in the same change, so the test module now constructs an oracle `CoherenceView` with a
// populated data-type set — the `type_local`-via-`Data` acceptance arm is a full LIVE differential
// (`register_instances_type_local_via_data`), not a port-side-only hand-built expectation. The eleven
// cases below drive acceptance via trait-locality or the primitive-repr arm; the Data-membership arm
// is its own live case. (The widening is the white-box in-crate-test pattern CLAUDE.md endorses — the
// same one PR-1 used for `resolve_ctors`/`first_duplicate`.)
// ═══════════════════════════════════════════════════════════════════════════════════════════════════

// ── fixture constructors (test bodies stay `assert over a case`) ────────────────────────────────────
fn bytes_ty() -> TypeRef {
    tref(BaseType::Bytes)
}
fn float_ty() -> TypeRef {
    tref(BaseType::Float)
}
fn bin_ty(width: u32) -> TypeRef {
    tref(BaseType::Binary(WidthRef::Lit(width)))
}
fn fn_ty(param_t: TypeRef, ret_t: TypeRef) -> TypeRef {
    tref(BaseType::Fn(Box::new(param_t), Box::new(ret_t)))
}
/// An impl method `fn <name>() => Bytes = x`. `register_instances` reads only the method NAME
/// (`m.sig.name`), so the value-params / return / body are inert filler, kept minimal + encodable.
fn method(name: &str) -> FnDecl {
    fn_decl(fn_sig(name, vec![], bytes_ty()), var("x"))
}
fn impl_decl(
    trait_name: &str,
    trait_args: Vec<TypeRef>,
    for_ty: TypeRef,
    methods: Vec<FnDecl>,
) -> ImplDecl {
    ImplDecl {
        trait_name: trait_name.to_owned(),
        trait_args,
        for_ty,
        methods,
    }
}
fn it_impl(id: ImplDecl) -> Item {
    Item::Impl(id)
}
/// A single-method trait `trait <name> { fn <m>(x: Bytes) => Bytes; }` — its method sig resolves against
/// the primitive `Bytes`, so `register_traits` registers it with no seeded data type needed.
fn trait1(name: &str, method_name: &str) -> Item {
    it_trait(trait_decl(
        name,
        &[],
        vec![fn_sig(
            method_name,
            vec![param("x", bytes_ty())],
            bytes_ty(),
        )],
    ))
}

// ── encode a checkty::TraitInfo as the port's `TrInfo(name, params, sigs)` registry entry ────────────
fn encode_trait_info(t: &TraitInfo) -> String {
    format!(
        "TrInfo({}, {}, {})",
        encode_bytes(&t.name),
        encode_names(&t.params),
        encode_fn_sig_list(&t.sigs)
    )
}
fn encode_trait_info_list(ts: &[TraitInfo]) -> String {
    let mut s = String::from("Nil");
    for t in ts.iter().rev() {
        s = format!("Cons({}, {})", encode_trait_info(t), s);
    }
    s
}
/// `CV(traits, types)` — the CoherenceView mirror; each field a `Vec[Bytes]` name-list.
fn encode_coherence(traits: &[&str], types: &[&str]) -> String {
    let owned_t: Vec<String> = traits.iter().map(|s| (*s).to_owned()).collect();
    let owned_ty: Vec<String> = types.iter().map(|s| (*s).to_owned()).collect();
    format!(
        "CV({}, {})",
        encode_names(&owned_t),
        encode_names(&owned_ty)
    )
}

// ── decode the port's `Vec[InstanceInfo]` → the oracle's `(trait, head)`-keyed BTreeMap ──────────────
fn decode_instance_info(v: &L1Value) -> InstanceInfo {
    let (ctor, fields) = expect_data(v, "InstanceInfo");
    match ctor {
        "InstInfo" => InstanceInfo {
            trait_name: decode_string(&fields[0]),
            trait_args: decode_vec(&fields[1], decode_ty),
            for_ty: decode_ty(&fields[2]),
            methods: decode_vec(&fields[3], decode_string),
        },
        c => panic!("marshal decode_instance_info: unexpected ctor {c}"),
    }
}
/// Decode `register_instances`' returned registry (`Vec[InstanceInfo]`) into a `BTreeMap` keyed by
/// `(trait_name, type_head(for_ty))` — the order-insensitive comparison surface against
/// `checkty::register_instances`' `BTreeMap`. A stored instance always has a `Some` head (it passed the
/// type_head check); a duplicate key panics (never-silent): the port's global-uniqueness check keeps one
/// entry per `(trait, head)`, so a dup is a real port bug, surfaced rather than silently collapsed.
fn decode_instances_map(v: &L1Value) -> BTreeMap<(String, String), InstanceInfo> {
    let mut map = BTreeMap::new();
    for inst in decode_vec(v, decode_instance_info) {
        let head = type_head(&inst.for_ty)
            .expect("a registered instance's for_ty has a Some type_head (the uniqueness key)");
        assert!(
            map.insert((inst.trait_name.clone(), head), inst).is_none(),
            "register_instances port produced a duplicate (trait, head) key (uniqueness invariant broken)"
        );
    }
    map
}

#[test]
fn register_instances_cases() {
    // A single-method trait `Show { show }` declared so `register_traits` registers its TraitInfo.
    let show = || trait1("Show", "show");
    // A 2-param trait `Pair2[A,B] { m }` for the arity + multi-arg cases.
    let pair2 = || {
        it_trait(trait_decl(
            "Pair2",
            &["A", "B"],
            vec![fn_sig("m", vec![param("x", bytes_ty())], bytes_ty())],
        ))
    };
    let cases: Vec<(&str, Vec<DataInfo>, Nodule, Vec<&str>)> = vec![
        // (1) Single valid impl (trait-local) → Ok, keyed ("Show","Binary").
        (
            "single_valid",
            vec![],
            nodule(vec![
                show(),
                it_impl(impl_decl("Show", vec![], bin_ty(8), vec![method("show")])),
            ]),
            vec!["Show"],
        ),
        // (2) Unknown trait `Nope` (never declared) → Err.
        (
            "unknown_trait",
            vec![],
            nodule(vec![it_impl(impl_decl("Nope", vec![], bin_ty(8), vec![]))]),
            vec![],
        ),
        // (3) Arity mismatch: `Pair2` takes 2 args, impl supplies 0 → Err.
        (
            "arity_mismatch",
            vec![],
            nodule(vec![
                pair2(),
                it_impl(impl_decl("Pair2", vec![], bin_ty(8), vec![method("m")])),
            ]),
            vec!["Pair2"],
        ),
        // (4) Bare non-concrete head: `for (Bytes -> Bytes)` → type_head None → Err.
        (
            "non_concrete_head",
            vec![],
            nodule(vec![
                show(),
                it_impl(impl_decl(
                    "Show",
                    vec![],
                    fn_ty(bytes_ty(), bytes_ty()),
                    vec![method("show")],
                )),
            ]),
            vec!["Show"],
        ),
        // (5) Orphan: trait NOT phylum-local (coh empty) and `for Foreign` NOT in coherence.types → Err.
        (
            "orphan",
            vec![shell("Foreign", &[])],
            nodule(vec![
                show(),
                it_impl(impl_decl(
                    "Show",
                    vec![],
                    nm("Foreign"),
                    vec![method("show")],
                )),
            ]),
            vec![],
        ),
        // (6) Trait-local only: trait in coherence.traits, `for Foreign` (a Data NOT in coherence.types)
        //     → Ok via the trait-locality arm, keyed ("Show","Data:Foreign").
        (
            "trait_local_only",
            vec![shell("Foreign", &[])],
            nodule(vec![
                show(),
                it_impl(impl_decl(
                    "Show",
                    vec![],
                    nm("Foreign"),
                    vec![method("show")],
                )),
            ]),
            vec!["Show"],
        ),
        // (7) Type-local via primitive repr: trait NOT local, `for Binary{8}` (primitive) → Ok via the
        //     primitive-repr arm, keyed ("Show","Binary").
        (
            "type_local_primitive",
            vec![],
            nodule(vec![
                show(),
                it_impl(impl_decl("Show", vec![], bin_ty(8), vec![method("show")])),
            ]),
            vec![],
        ),
        // (8) Overlapping: two impls on the same `(Show, Binary)` head (widths 8 and 16 erase) → Err.
        (
            "overlapping",
            vec![],
            nodule(vec![
                show(),
                it_impl(impl_decl("Show", vec![], bin_ty(8), vec![method("show")])),
                it_impl(impl_decl("Show", vec![], bin_ty(16), vec![method("show")])),
            ]),
            vec!["Show"],
        ),
        // (9) Missing method: `Two` requires {a,b}, impl provides {a} → Err.
        (
            "missing_method",
            vec![],
            nodule(vec![
                it_trait(trait_decl(
                    "Two",
                    &[],
                    vec![
                        fn_sig("a", vec![param("x", bytes_ty())], bytes_ty()),
                        fn_sig("b", vec![param("y", bytes_ty())], bytes_ty()),
                    ],
                )),
                it_impl(impl_decl("Two", vec![], bin_ty(8), vec![method("a")])),
            ]),
            vec!["Two"],
        ),
        // (10) Extra method: `Show` requires {show}, impl provides {show,extra} → Err.
        (
            "extra_method",
            vec![],
            nodule(vec![
                show(),
                it_impl(impl_decl(
                    "Show",
                    vec![],
                    bin_ty(8),
                    vec![method("show"), method("extra")],
                )),
            ]),
            vec!["Show"],
        ),
        // (11) Multi-arg trait Ok: `Pair2[A,B]` with trait_args [Bytes, Float] (arity 2) → Ok, keyed
        //      ("Pair2","Binary") with concrete trait_args [TyBytes, TyFloat].
        (
            "multi_arg_ok",
            vec![],
            nodule(vec![
                pair2(),
                it_impl(impl_decl(
                    "Pair2",
                    vec![bytes_ty(), float_ty()],
                    bin_ty(8),
                    vec![method("m")],
                )),
            ]),
            vec!["Pair2"],
        ),
        // (12) Duplicate method: `Show` requires {show}, impl provides {show, show} → Err. The set-based
        //      missing/extra checks both pass (provided set == required == {show}); the third arm —
        //      `first_duplicate` over the method-name list (checkty.rs:3268-3282) — catches the repeat.
        (
            "duplicate_method",
            vec![],
            nodule(vec![
                show(),
                it_impl(impl_decl(
                    "Show",
                    vec![],
                    bin_ty(8),
                    vec![method("show"), method("show")],
                )),
            ]),
            vec!["Show"],
        ),
    ];
    for (label, shells, nod, coh_traits) in &cases {
        let tmap = types_map(shells);
        let traits_map = register_traits(&tmap, nod).expect("fixture traits register");
        let traits: Vec<TraitInfo> = traits_map.values().cloned().collect();
        let mut coh = CoherenceView::default();
        for t in coh_traits {
            coh.traits.insert((*t).to_owned());
        }
        let want = register_instances(&tmap, &traits_map, &coh, nod).map_err(|_| ());
        assert_l1_marshal(
            &format!("register_instances_{label}"),
            &format!(
                "fn main() => Result[Vec[InstanceInfo], Bytes] = register_instances({}, {}, {}, {});\n",
                encode_data_info_list(shells),
                encode_trait_info_list(&traits),
                encode_coherence(coh_traits, &[]),
                encode_nodule(nod)
            ),
            |v| decode_result(v, decode_instances_map),
            want,
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// register_instances type_local-via-Data (FLAG-semcore-33 RESOLVED) — a full LIVE differential of the
// Data-membership orphan arm: trait NOT phylum-local, but `for Foreign` with `Foreign` IN
// coherence.types ⇒ Ok, keyed ("Show","Data:Foreign"). Now that `CoherenceView.types` is `pub(crate)`,
// the oracle `CoherenceView` is constructed with the populated types set and the expectation comes from
// the REAL `checkty::register_instances`, not a hand-built value — the one acceptance arm the eleven
// trait-locality/primitive-repr cases can't reach, now witnessed live like the rest.
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn register_instances_type_local_via_data() {
    let shells = vec![shell("Foreign", &[])];
    let nod = nodule(vec![
        trait1("Show", "show"),
        it_impl(impl_decl(
            "Show",
            vec![],
            nm("Foreign"),
            vec![method("show")],
        )),
    ]);
    let tmap = types_map(&shells);
    let traits_map = register_traits(&tmap, &nod).expect("fixture traits register");
    let traits: Vec<TraitInfo> = traits_map.values().cloned().collect();
    // Live oracle: trait NOT in coherence.traits, but `Foreign` IS in coherence.types ⇒ type_local ⇒ Ok.
    let mut coh = CoherenceView::default();
    coh.types.insert("Foreign".to_owned());
    let want = register_instances(&tmap, &traits_map, &coh, &nod).map_err(|_| ());
    assert_l1_marshal(
        "register_instances_type_local_via_data",
        &format!(
            "fn main() => Result[Vec[InstanceInfo], Bytes] = register_instances({}, {}, {}, {});\n",
            encode_data_info_list(&shells),
            encode_trait_info_list(&traits),
            encode_coherence(&[], &["Foreign"]),
            encode_nodule(&nod)
        ),
        |v| decode_result(v, decode_instances_map),
        want,
    );
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// Decoder non-vacuity for the InstanceInfo decoder (M-1013 STEP 2 convention): each field must
// DISCRIMINATE — two mirror literals differing in exactly one field decode `!=`, so a decoder that
// dropped a field is caught rather than silently collapsing distinct instances. Covers all four
// InstanceInfo fields independently (trait_name / trait_args / for_ty / methods).
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn marshal_discriminates_instances() {
    fn dd_inst(expr: &str) -> InstanceInfo {
        decode_driver("InstanceInfo", expr, decode_instance_info)
    }
    let a = encode_bytes("A");
    let b = encode_bytes("B");
    let base = format!("InstInfo({a}, Nil, TyBytes, Nil)");
    // field 0: trait_name.
    assert_ne!(
        dd_inst(&base),
        dd_inst(&format!("InstInfo({b}, Nil, TyBytes, Nil)"))
    );
    // field 1: trait_args.
    assert_ne!(
        dd_inst(&base),
        dd_inst(&format!("InstInfo({a}, Cons(TyBytes, Nil), TyBytes, Nil)"))
    );
    // field 2: for_ty.
    assert_ne!(
        dd_inst(&base),
        dd_inst(&format!("InstInfo({a}, Nil, TyFloat, Nil)"))
    );
    // field 3: methods.
    assert_ne!(
        dd_inst(&base),
        dd_inst(&format!(
            "InstInfo({a}, Nil, TyBytes, Cons({}, Nil))",
            encode_bytes("m")
        ))
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════════
// resolve_imports (M-1013 STEP 4) — cross-nodule import resolution, the "resolution" half of
// increment 8 (register_types/register_traits/register_instances above are its "registration" half).
// ═══════════════════════════════════════════════════════════════════════════════════════════════════
//
// Differential method: identical harness marshalling (DN-26 §10.2) — build an `Exports` fixture, run
// the REAL `checkty::resolve_imports` oracle, evaluate the `.myc` port's `resolve_imports` on the SAME
// fixture (encoded), decode its `NoduleImports` output, `assert_eq!` against the oracle's.
//
// FLAG-semcore-34 (scope narrowing, honestly flagged — G2/VR-5): every fixture here leaves
// `Exports.fns` EMPTY, so `NoduleImports.fns` is always the trivial `Nil`/`{}` case — decoding an
// arbitrary returned `FnDecl` (a full recursive `Expr` body) would need a new `decode_expr` this
// increment does not build (no other Stage-5 gate has needed to decode an `Expr` from `L1Value` output
// yet; every prior increment's `Expr`/`FnDecl` traffic has been INPUT-only). `insert_export`'s
// fn-branch is structurally IDENTICAL to its type/trait branches (checkty.rs 1560-1571: three
// independent `if let Some(x) = exports.KIND.get(qual) { imp.KIND.insert(...) }` arms, ported
// arm-for-arm in this port's own `insert_export`), so this narrowing is low-risk — but it is an
// honest, explicit scope cut, not a silent one.

// ── Exports / NoduleImports mirror encoders/decoders ──────────────────────────────────────────────────

fn encode_str_datainfo_map(m: &BTreeMap<String, DataInfo>) -> String {
    let mut s = String::from("Nil");
    for (k, v) in m.iter().rev() {
        s = format!(
            "Cons(Pr({}, {}), {})",
            encode_bytes(k),
            encode_data_info(v),
            s
        );
    }
    s
}

fn encode_str_traitinfo_map(m: &BTreeMap<String, TraitInfo>) -> String {
    let mut s = String::from("Nil");
    for (k, v) in m.iter().rev() {
        s = format!(
            "Cons(Pr({}, {}), {})",
            encode_bytes(k),
            encode_trait_info(v),
            s
        );
    }
    s
}

fn encode_declared_map(m: &BTreeMap<String, bool>) -> String {
    let mut s = String::from("Nil");
    for (k, v) in m.iter().rev() {
        s = format!(
            "Cons(Pr({}, {}), {})",
            encode_bytes(k),
            if *v { "True" } else { "False" },
            s
        );
    }
    s
}

/// `Ex(types, fns, traits, declared)` — the `Exports` mirror. `fns` is always `Nil` (FLAG-semcore-34).
fn encode_exports(e: &Exports) -> String {
    assert!(
        e.fns.is_empty(),
        "encode_exports: every fixture in this gate leaves Exports.fns empty (FLAG-semcore-34)"
    );
    format!(
        "Ex({}, Nil, {}, {})",
        encode_str_datainfo_map(&e.types),
        encode_str_traitinfo_map(&e.traits),
        encode_declared_map(&e.declared)
    )
}

/// `Pr(a, b)` decode: the shared two-field mirror pair.
fn decode_pair<A, B>(
    v: &L1Value,
    da: impl Fn(&L1Value) -> A,
    db: impl Fn(&L1Value) -> B,
) -> (A, B) {
    let (_, fields) = expect_data(v, "Pair");
    (da(&fields[0]), db(&fields[1]))
}

fn decode_str_datainfo_map(v: &L1Value) -> BTreeMap<String, DataInfo> {
    let mut map = BTreeMap::new();
    let mut cur = v;
    loop {
        let (ctor, fields) = expect_data(cur, "assoc-list<Bytes,DataInfo>");
        match ctor {
            "Nil" => return map,
            "Cons" => {
                let (k, val) = decode_pair(&fields[0], decode_string, decode_data_info);
                map.insert(k, val);
                cur = &fields[1];
            }
            other => panic!("decode_str_datainfo_map: unexpected ctor {other}"),
        }
    }
}

fn decode_str_traitinfo_map(v: &L1Value) -> BTreeMap<String, TraitInfo> {
    let mut map = BTreeMap::new();
    let mut cur = v;
    loop {
        let (ctor, fields) = expect_data(cur, "assoc-list<Bytes,TraitInfo>");
        match ctor {
            "Nil" => return map,
            "Cons" => {
                let (k, val) = decode_pair(&fields[0], decode_string, decode_trait_info);
                map.insert(k, val);
                cur = &fields[1];
            }
            other => panic!("decode_str_traitinfo_map: unexpected ctor {other}"),
        }
    }
}

/// FLAG-semcore-34: every fixture leaves `Exports.fns` empty, so the port's returned `NoduleImports`
/// `fns` field is always the empty `Nil` list — asserted here (never-silent: a future fixture that DID
/// populate `Exports.fns` would panic here, not silently mis-decode).
fn decode_empty_fndecl_map(v: &L1Value) -> BTreeMap<String, FnDecl> {
    let (ctor, _) = expect_data(v, "assoc-list<Bytes,FnDecl> (expected empty)");
    assert_eq!(
        ctor, "Nil",
        "decode_empty_fndecl_map: non-empty NoduleImports.fns -- FLAG-semcore-34's scope narrowing no \
         longer holds; a real decode_fn_decl/decode_expr is now needed"
    );
    BTreeMap::new()
}

fn decode_bytes_set(v: &L1Value) -> BTreeSet<String> {
    decode_vec(v, decode_string).into_iter().collect()
}

/// `NI(types, fns, traits, ambiguous)` — the `NoduleImports` mirror decoder.
fn decode_nodule_imports(v: &L1Value) -> NoduleImports {
    let (ctor, fields) = expect_data(v, "NoduleImports");
    assert_eq!(ctor, "NI", "decode_nodule_imports: unexpected ctor {ctor}");
    NoduleImports {
        types: decode_str_datainfo_map(&fields[0]),
        fns: decode_empty_fndecl_map(&fields[1]),
        traits: decode_str_traitinfo_map(&fields[2]),
        ambiguous: decode_bytes_set(&fields[3]),
        // M-1027 / DN-104 §6: the `.myc` mirror does not model the cross-nodule construction seal
        // (its `NoduleImports` `NI` carries 4 fields — the enforcement layer is Rust-only until the
        // checkty cross-nodule port), so the decoded value's withheld set is empty. FLAGGED residual.
        sealed: std::collections::BTreeSet::new(),
        // DN-112 Rank 1 / M-1036, DoD item 8: same flagged residual — the `.myc` mirror does not
        // yet bake/carry a resolved-signature mechanism at all.
        resolved_fn_sigs: BTreeMap::new(),
        // M-1060 fix-cycle-3: same flagged residual — the `.myc` mirror predates the cross-phylum
        // subsystem entirely (DN-113/M-1060), so it carries no cross-phylum marker at all; the
        // decoded value's cross-phylum sets are always empty.
        cross_phylum_traits: std::collections::BTreeSet::new(),
        cross_phylum_fns: std::collections::BTreeSet::new(),
    }
}

// ── fixture constructors (test bodies stay `assert over a case`) ──────────────────────────────────────

fn use_item(segs: &[&str], glob: bool) -> Item {
    Item::Use(UsePath {
        phylum: None,
        path: Path(segs.iter().map(|s| (*s).to_owned()).collect()),
        glob,
    })
}

fn data_info_leaf(name: &str) -> DataInfo {
    DataInfo {
        home: String::new(), // DN-112/M-1036: test fixture, unqualified/bare identity
        name: name.to_owned(),
        params: vec![],
        ctors: vec![],
    }
}

fn trait_info_leaf(name: &str) -> TraitInfo {
    TraitInfo {
        name: name.to_owned(),
        params: vec![],
        sigs: vec![],
    }
}

#[derive(Default)]
struct ExportsBuilder {
    types: Vec<(&'static str, DataInfo)>,
    traits: Vec<(&'static str, TraitInfo)>,
    declared: Vec<(&'static str, bool)>,
}

impl ExportsBuilder {
    fn ty(mut self, qual: &'static str, d: DataInfo) -> Self {
        self.types.push((qual, d));
        self
    }
    fn tr(mut self, qual: &'static str, t: TraitInfo) -> Self {
        self.traits.push((qual, t));
        self
    }
    fn decl(mut self, qual: &'static str, is_pub: bool) -> Self {
        self.declared.push((qual, is_pub));
        self
    }
    fn build(self) -> Exports {
        let mut e = Exports::default();
        for (k, v) in self.types {
            e.types.insert(k.to_owned(), v);
        }
        for (k, v) in self.traits {
            e.traits.insert(k.to_owned(), v);
        }
        for (k, v) in self.declared {
            e.declared.insert(k.to_owned(), v);
        }
        e
    }
}

fn run_resolve_imports_case(label: &str, nod: &Nodule, exports: &Exports) {
    // M-1060: this differential exercises intra-phylum resolution only (its self-hosted `.myc`
    // mirror predates cross-phylum `use`); the empty `Phyla` makes `resolve_imports` behave
    // byte-identically to its pre-M-1060 signature.
    let want = resolve_imports(nod, exports, &Phyla::default()).map_err(|_| ());
    assert_l1_marshal(
        label,
        &format!(
            "fn main() => Result[NoduleImports, Bytes] = resolve_imports({}, {});\n",
            encode_nodule(nod),
            encode_exports(exports)
        ),
        |v| decode_result(v, decode_nodule_imports),
        want,
    );
}

// ── cases: explicit imports ─────────────────────────────────────────────────────────────────────────

#[test]
fn resolve_imports_explicit_type_ok() {
    let exports = ExportsBuilder::default()
        .ty("m.List", data_info_leaf("List"))
        .decl("m.List", true)
        .build();
    let nod = nodule(vec![use_item(&["m", "List"], false)]);
    run_resolve_imports_case("resolve_imports_explicit_type_ok", &nod, &exports);
}

#[test]
fn resolve_imports_explicit_trait_ok() {
    let exports = ExportsBuilder::default()
        .tr("m.Eq", trait_info_leaf("Eq"))
        .decl("m.Eq", true)
        .build();
    let nod = nodule(vec![use_item(&["m", "Eq"], false)]);
    run_resolve_imports_case("resolve_imports_explicit_trait_ok", &nod, &exports);
}

#[test]
fn resolve_imports_explicit_unknown_err() {
    let exports = ExportsBuilder::default().build();
    let nod = nodule(vec![use_item(&["m", "Nope"], false)]);
    run_resolve_imports_case("resolve_imports_explicit_unknown_err", &nod, &exports);
}

#[test]
fn resolve_imports_explicit_private_err() {
    let exports = ExportsBuilder::default()
        .ty("m.Secret", data_info_leaf("Secret"))
        .decl("m.Secret", false)
        .build();
    let nod = nodule(vec![use_item(&["m", "Secret"], false)]);
    run_resolve_imports_case("resolve_imports_explicit_private_err", &nod, &exports);
}

#[test]
fn resolve_imports_explicit_duplicate_err() {
    let exports = ExportsBuilder::default()
        .ty("m.List", data_info_leaf("List"))
        .decl("m.List", true)
        .build();
    let nod = nodule(vec![
        use_item(&["m", "List"], false),
        use_item(&["m", "List"], false),
    ]);
    run_resolve_imports_case("resolve_imports_explicit_duplicate_err", &nod, &exports);
}

#[test]
fn resolve_imports_explicit_unqualified_err() {
    let exports = ExportsBuilder::default().build();
    let nod = nodule(vec![use_item(&["List"], false)]);
    run_resolve_imports_case("resolve_imports_explicit_unqualified_err", &nod, &exports);
}

// ── cases: globs ────────────────────────────────────────────────────────────────────────────────────

#[test]
fn resolve_imports_glob_pulls_pub_only() {
    let exports = ExportsBuilder::default()
        .ty("m.A", data_info_leaf("A"))
        .ty("m.C", data_info_leaf("C"))
        .decl("m.A", true)
        .decl("m.B", false)
        .decl("m.C", true)
        .build();
    let nod = nodule(vec![use_item(&["m"], true)]);
    run_resolve_imports_case("resolve_imports_glob_pulls_pub_only", &nod, &exports);
}

#[test]
fn resolve_imports_glob_glob_ambiguous() {
    let exports = ExportsBuilder::default()
        .ty("m.A", data_info_leaf("A1"))
        .ty("n.A", data_info_leaf("A2"))
        .decl("m.A", true)
        .decl("n.A", true)
        .build();
    let nod = nodule(vec![use_item(&["m"], true), use_item(&["n"], true)]);
    run_resolve_imports_case("resolve_imports_glob_glob_ambiguous", &nod, &exports);
}

#[test]
fn resolve_imports_explicit_shadows_glob() {
    let exports = ExportsBuilder::default()
        .ty("m.A", data_info_leaf("A1"))
        .ty("n.A", data_info_leaf("A2"))
        .decl("m.A", true)
        .decl("n.A", true)
        .build();
    let nod = nodule(vec![use_item(&["m"], true), use_item(&["n", "A"], false)]);
    run_resolve_imports_case("resolve_imports_explicit_shadows_glob", &nod, &exports);
}

// ── decoder non-vacuity (M-1013 STEP 2 convention) ──────────────────────────────────────────────────

#[test]
fn marshal_discriminates_nodule_imports() {
    fn dd(expr: &str) -> NoduleImports {
        decode_driver("NoduleImports", expr, decode_nodule_imports)
    }
    let a = encode_bytes("A");
    let di_a = encode_data_info(&data_info_leaf("A"));
    let ti_a = encode_trait_info(&trait_info_leaf("A"));
    let base = "NI(Nil, Nil, Nil, Nil)".to_owned();
    // field 0: types.
    assert_ne!(
        dd(&base),
        dd(&format!("NI(Cons(Pr({a}, {di_a}), Nil), Nil, Nil, Nil)"))
    );
    // field 2: traits.
    assert_ne!(
        dd(&base),
        dd(&format!("NI(Nil, Nil, Cons(Pr({a}, {ti_a}), Nil), Nil)"))
    );
    // field 3: ambiguous.
    assert_ne!(dd(&base), dd(&format!("NI(Nil, Nil, Nil, Cons({a}, Nil))")));
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════
// register_nodule_decls (M-1013 STEP 5) — the top-level declaration-registration entry point
// (checkty.rs 1340-1401), deferred at STEP 4 landing and now ported: it runs register_types (seeded
// with the `Bool` prelude), register_traits, the CONDITIONAL built-in `Fuse` trait seed (M-965 F-A1,
// via the newly-ported `fuse::prelude()` mirror — the fuse.rs slice that does NOT touch
// `eval::Evaluator`), and a fresh fn-signature registration pass, in that exact order.
// ═══════════════════════════════════════════════════════════════════════════════════════════════
//
// Differential method: identical harness marshalling (DN-26 §10.2) — run the REAL
// `checkty::register_nodule_decls` oracle on a `Nodule` fixture, evaluate the `.myc` port's mirror
// driver on the SAME fixture, decode its `NoduleRegs` output, compare against the oracle.
//
// FLAG-semcore-35 (scope narrowing, honestly flagged — G2/VR-5, the direct twin of FLAG-semcore-34
// above): the `fns` registry decodes to its NAME set only, not the full `FnDecl` payload — decoding an
// arbitrary registered `FnDecl.body` `Expr` needs a `decode_expr` no Stage-5 gate has built yet (every
// prior increment's `Expr`/`FnDecl` traffic has been INPUT-only). `register_nodule_decls`'s own
// fn-registration loop (checkty.rs 1392-1400) never inspects a body either — it is name-and-arity
// registration only — so the *classification* this differential compares (which names got registered,
// and the dup-type-param / dup-name refusals) is exactly the surface the ported loop's own logic
// touches.

/// `checkty::NoduleRegs.fns` → its NAME set (FLAG-semcore-35).
fn fn_names(fns: &BTreeMap<String, FnDecl>) -> BTreeSet<String> {
    fns.keys().cloned().collect()
}

/// `Pr(name, _)` → the name only, from a `Vec[Pair[Bytes, FnDecl]]` element (FLAG-semcore-35: the
/// `FnDecl` field is never decoded).
fn decode_nodule_regs_fn_names(v: &L1Value) -> BTreeSet<String> {
    decode_vec(v, |p| {
        let (ctor, fields) = expect_data(p, "Pair");
        assert_eq!(
            ctor, "Pr",
            "decode_nodule_regs_fn_names: unexpected ctor {ctor}"
        );
        decode_string(&fields[0])
    })
    .into_iter()
    .collect()
}

/// `NR(types, fns, traits)` — the `NoduleRegs` mirror decoder, into the SAME 3-tuple shape
/// `run_register_nodule_decls_case` builds from the live oracle's `NoduleRegs`.
fn decode_nodule_regs(
    v: &L1Value,
) -> (
    BTreeMap<String, DataInfo>,
    BTreeSet<String>,
    BTreeMap<String, TraitInfo>,
) {
    let (ctor, fields) = expect_data(v, "NoduleRegs");
    assert_eq!(ctor, "NR", "decode_nodule_regs: unexpected ctor {ctor}");
    (
        decode_types_map(&fields[0]),
        decode_nodule_regs_fn_names(&fields[1]),
        decode_traits_map(&fields[2]),
    )
}

fn run_register_nodule_decls_case(label: &str, nod: &Nodule) {
    // DN-112/M-1036 DoD item 8: normalize `home` — see `strip_home`'s doc comment.
    let want = register_nodule_decls(nod)
        .map(|regs: NoduleRegs| (strip_home_map(regs.types), fn_names(&regs.fns), regs.traits))
        .map_err(|_| ());
    assert_l1_marshal(
        label,
        &format!(
            "fn main() => Result[NoduleRegs, Bytes] = register_nodule_decls({});\n",
            encode_nodule(nod)
        ),
        |v| decode_result(v, decode_nodule_regs),
        want,
    );
}

// ── fixture constructors (test bodies stay `assert over a case`) ───────────────────────────────────

/// A `FnSig` with explicit type PARAMS (the `fn_sig` fixture above always leaves `params` empty —
/// the dup-type-param refusal needs a non-empty one).
fn fn_sig_with_type_params(name: &str, tps: Vec<TypeParam>, ret: TypeRef) -> FnSig {
    FnSig {
        name: name.to_owned(),
        params: tps,
        value_params: vec![],
        ret,
        effects: vec![],
        effect_budgets: BTreeMap::new(),
    }
}

fn type_param(name: &str) -> TypeParam {
    TypeParam {
        name: name.to_owned(),
        kind: ParamKind::Type,
        bounds: vec![],
    }
}

// ── cases ────────────────────────────────────────────────────────────────────────────────────────────

#[test]
fn register_nodule_decls_type_and_fn_ok() {
    let nod = nodule(vec![
        ty(type_decl("A", &[], vec![ctor("MkA", vec![])])),
        Item::Fn(fn_decl(fn_sig("f", vec![], nm("A")), var("x"))),
    ]);
    run_register_nodule_decls_case("register_nodule_decls_type_and_fn_ok", &nod);
}

#[test]
fn register_nodule_decls_dup_type_name_err() {
    let nod = nodule(vec![
        ty(type_decl("A", &[], vec![ctor("MkA", vec![])])),
        ty(type_decl("A", &[], vec![ctor("MkA2", vec![])])),
    ]);
    run_register_nodule_decls_case("register_nodule_decls_dup_type_name_err", &nod);
}

#[test]
fn register_nodule_decls_dup_fn_name_err() {
    let nod = nodule(vec![
        Item::Fn(fn_decl(fn_sig("f", vec![], nm("Bytes")), var("x"))),
        Item::Fn(fn_decl(fn_sig("f", vec![], nm("Bytes")), var("y"))),
    ]);
    run_register_nodule_decls_case("register_nodule_decls_dup_fn_name_err", &nod);
}

#[test]
fn register_nodule_decls_dup_fn_type_param_err() {
    let nod = nodule(vec![Item::Fn(fn_decl(
        fn_sig_with_type_params("f", vec![type_param("X"), type_param("X")], nm("X")),
        var("x"),
    ))]);
    run_register_nodule_decls_case("register_nodule_decls_dup_fn_type_param_err", &nod);
}

#[test]
fn register_nodule_decls_fuse_impl_seeds_trait() {
    // `register_nodule_decls` never resolves/checks the impl's trait_args/for_ty/methods (that is
    // `register_instances`' job, a later pass) -- registration only asks "is there an
    // `impl Fuse[...] for ...` item at all?", so a minimal, unresolved-looking impl is a faithful
    // fixture for THIS pass.
    let nod = nodule(vec![Item::Impl(impl_decl(
        "Fuse",
        vec![],
        nm("Unit"),
        vec![],
    ))]);
    run_register_nodule_decls_case("register_nodule_decls_fuse_impl_seeds_trait", &nod);
}

#[test]
fn register_nodule_decls_no_fuse_impl_no_trait_seeded() {
    let nod = nodule(vec![ty(type_decl("A", &[], vec![ctor("MkA", vec![])]))]);
    run_register_nodule_decls_case("register_nodule_decls_no_fuse_impl_no_trait_seeded", &nod);
}

#[test]
fn register_nodule_decls_user_redeclares_fuse_trait_err() {
    // A nodule that declares its OWN `trait Fuse { ... }` (no `impl Fuse[...] for ...` needed to
    // trip this -- checkty.rs's `else if traits.contains_key(TRAIT_NAME)` branch, 1381-1387).
    let nod = nodule(vec![trait1("Fuse", "join")]);
    run_register_nodule_decls_case("register_nodule_decls_user_redeclares_fuse_trait_err", &nod);
}

#[test]
fn register_nodule_decls_fuse_impl_plus_user_trait_redeclare_err() {
    // Both `fuse_used` (an `impl Fuse[...] for ...`) AND a pre-existing `traits["Fuse"]` (the
    // nodule's OWN `trait Fuse`) -- checkty.rs's OTHER redeclare branch, 1372-1378.
    let nod = nodule(vec![
        trait1("Fuse", "join"),
        Item::Impl(impl_decl("Fuse", vec![], nm("Unit"), vec![])),
    ]);
    run_register_nodule_decls_case(
        "register_nodule_decls_fuse_impl_plus_user_trait_redeclare_err",
        &nod,
    );
}

// ── decoder non-vacuity (M-1013 STEP 2 convention) ──────────────────────────────────────────────────

#[test]
fn marshal_discriminates_nodule_regs() {
    fn dd(
        expr: &str,
    ) -> (
        BTreeMap<String, DataInfo>,
        BTreeSet<String>,
        BTreeMap<String, TraitInfo>,
    ) {
        decode_driver("NoduleRegs", expr, decode_nodule_regs)
    }
    let a = encode_bytes("A");
    let di_a = encode_data_info(&data_info_leaf("A"));
    let ti_a = encode_trait_info(&trait_info_leaf("A"));
    // A real (inert) `FnDecl` mirror -- the `fns` field's type is `Vec[Pair[Bytes, FnDecl]]`, so the
    // filler value must actually type-check as `FnDecl`, unlike the untyped Rust-side comparison
    // (decode_nodule_regs_fn_names never reads it, but the `.myc` driver text still must check).
    let fd_a = encode_fn_decl(&fn_decl(fn_sig("g", vec![], nm("Bytes")), var("x")));
    let base = "NR(Nil, Nil, Nil)".to_owned();
    // field 0: types.
    assert_ne!(dd(&base), dd(&format!("NR(Cons({di_a}, Nil), Nil, Nil)")));
    // field 1: fns.
    assert_ne!(
        dd(&base),
        dd(&format!("NR(Nil, Cons(Pr({a}, {fd_a}), Nil), Nil)"))
    );
    // field 2: traits.
    assert_ne!(dd(&base), dd(&format!("NR(Nil, Nil, Cons({ti_a}, Nil))")));
}
