//! M-740 Stage 5 (M-1013 STEP 6; DN-26 §7.3 row 5 / §9 flag-1) — the self-hosted `compiler.semcore`
//! port of mono.rs's remaining PURE `Ty`/`TypeRef` round-trip family plus the monomorphization
//! work-item dedup key: the LIVE-ORACLE marshalling differential gate for FLAG-semcore-17's closure
//! (`mangle_ty_in_ty`, `item_key`) plus the natural extension (`closure_field_ty`,
//! `closure_param_ref`, `ty_to_source_ref`, `ty_to_ref`, `ty_to_ref_tagged`) ported into
//! `lib/compiler/semcore.myc`.
//!
//! **Live-oracle posture (VR-5).** Every case calls the REAL Rust `mono::{closure_field_ty,
//! closure_param_ref, mangle_ty_in_ty, ty_to_source_ref, ty_to_ref, ty_to_ref_tagged, item_key}` on
//! a fixture, producing a genuine `Ty`/`TypeRef`/`String`. It then evaluates the `.myc` port's
//! mirror driver and DECODES the returned `L1Value` back into the real Rust type (`decode_ty`/
//! `decode_typeref`, built on the shared `marshal_support` primitives plus this file's own
//! `TypeRef`/`BaseType`/`Strength` decoders — `decode_typeref` here additionally decodes a
//! `Some(Strength)` guarantee slot, unlike `compiler_stage5_register.rs`'s narrower decoder, because
//! `ty_to_ref_tagged` is exactly the fn that produces one). The two independently-produced values are
//! compared with Rust's own trusted derived `==`.
//!
//! Six of the seven exercised fns, plus mono's own `Item` work-item enum, were Rust MODULE-PRIVATE —
//! FLAG-semcore-17's original blocker. This leaf widens all seven to `pub(crate)` in `mono.rs` (zero
//! logic change — the STEP-3/4/5 visibility-widening precedent: `resolve_ctors`/`first_duplicate`,
//! commit 2bb06f88; `Exports`/`NoduleImports`/`CoherenceView`, commit 65351071) so this in-crate
//! `src/tests/` module can reach them directly.
//!
//! M-981 applies: only the L1-eval leg is exercised (small synthetic fixtures, not a corpus program).

use crate::ast::{BaseType, Scalar, Sparsity, Strength, TypeRef, WidthRef};
use crate::checkty::{check_nodule, subst_type_param_in_typeref, Ty, Width};
use crate::eval::{Evaluator, L1Value};
use crate::mono::{
    closure_field_ty, closure_param_ref, item_key, mangle_ty_in_ty, monomorphize, ty_to_ref,
    ty_to_ref_tagged, ty_to_source_ref, Item,
};
use crate::parse;
use crate::tests::marshal_support::*;

// ── local Ty/TypeRef/BaseType/Strength decoders (the marshalling inverse; the `Ty` decoder mirrors
// compiler_stage5_register.rs's `decode_ty` verbatim (module-local, not shared); the `TypeRef`
// decoder is a SUPERSET of that file's narrower one, which panics on `Some` because none of its
// oracles ever produce one — `ty_to_ref_tagged` here does) ─────────────────────────────────────────

/// The checked `Ty` mirror (all 11 variants) → `checkty::Ty`. Recursive on `Data`/`Seq`/`Fn`.
fn decode_ty(v: &L1Value) -> Ty {
    let (ctor, fields) = expect_data(v, "Ty");
    match ctor {
        "TyBinary" => Ty::Binary(decode_width_field(&fields[0])),
        "TyTernary" => Ty::Ternary(decode_width_field(&fields[0])),
        "TyDense" => Ty::Dense(decode_u32(&fields[0]), decode_scalar_field(&fields[1])),
        "TyVsa" => Ty::Vsa {
            model: decode_string(&fields[0]),
            dim: decode_u32(&fields[1]),
            sparsity: decode_sparsity_field(&fields[2]),
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

fn decode_width_field(v: &L1Value) -> Width {
    let (ctor, fields) = expect_data(v, "Width");
    match ctor {
        "WdLit" => Width::Lit(decode_u32(&fields[0])),
        "WdVar" => Width::Var(decode_string(&fields[0])),
        c => panic!("marshal decode_width_field: unexpected ctor {c}"),
    }
}

fn decode_strength(v: &L1Value) -> Strength {
    match expect_data(v, "Strength").0 {
        "GExact" => Strength::Exact,
        "GProven" => Strength::Proven,
        "GEmpirical" => Strength::Empirical,
        "GDeclared" => Strength::Declared,
        c => panic!("marshal decode_strength: unexpected ctor {c}"),
    }
}

fn decode_widthref(v: &L1Value) -> crate::ast::WidthRef {
    let (ctor, fields) = expect_data(v, "WidthRef");
    match ctor {
        "WLit" => crate::ast::WidthRef::Lit(decode_u32(&fields[0])),
        "WName" => crate::ast::WidthRef::Name(decode_string(&fields[0])),
        c => panic!("marshal decode_widthref: unexpected ctor {c}"),
    }
}

fn decode_basetype(v: &L1Value) -> BaseType {
    let (ctor, fields) = expect_data(v, "BaseType");
    match ctor {
        "KwBinary" => BaseType::Binary(decode_widthref(&fields[0])),
        "KwTernary" => BaseType::Ternary(decode_widthref(&fields[0])),
        "KwDense" => BaseType::Dense(decode_u32(&fields[0]), decode_scalar_field(&fields[1])),
        "Vsa" => BaseType::Vsa {
            model: decode_string(&fields[0]),
            dim: decode_u32(&fields[1]),
            sparsity: decode_sparsity_field(&fields[2]),
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

/// `TR(base, guarantee)` → `ast::TypeRef` — decodes BOTH `None` and `Some(Strength)` (the
/// `ty_to_ref_tagged` differential needs the latter; `register.rs`'s narrower decoder panics on it).
fn decode_typeref(v: &L1Value) -> crate::ast::TypeRef {
    let (ctor, fields) = expect_data(v, "TypeRef");
    match ctor {
        "TR" => crate::ast::TypeRef {
            base: decode_basetype(&fields[0]),
            guarantee: decode_option(&fields[1], decode_strength),
        },
        c => panic!("marshal decode_typeref: unexpected ctor {c}"),
    }
}

fn decode_scalar_field(v: &L1Value) -> crate::ast::Scalar {
    match expect_data(v, "Scalar").0 {
        "SF16" => crate::ast::Scalar::F16,
        "SBf16" => crate::ast::Scalar::Bf16,
        "SF32" => crate::ast::Scalar::F32,
        "SF64" => crate::ast::Scalar::F64,
        c => panic!("marshal decode_scalar_field: unexpected ctor {c}"),
    }
}

fn decode_sparsity_field(v: &L1Value) -> crate::ast::Sparsity {
    let (ctor, fields) = expect_data(v, "Sparsity");
    match ctor {
        "SpDense" => crate::ast::Sparsity::Dense,
        "SpSparse" => crate::ast::Sparsity::Sparse(decode_u32(&fields[0])),
        c => panic!("marshal decode_sparsity_field: unexpected ctor {c}"),
    }
}

// ── Rust → `.myc` fixture encoders (input side; reuses marshal_support::{encode_ty, encode_u32,
// encode_bytes} and adds the Strength/Option[Strength]/WorkItem encoders this file needs) ──────────

fn encode_strength(s: Strength) -> &'static str {
    match s {
        Strength::Exact => "GExact",
        Strength::Proven => "GProven",
        Strength::Empirical => "GEmpirical",
        Strength::Declared => "GDeclared",
    }
}

fn encode_guarantee(g: Option<Strength>) -> String {
    match g {
        None => "None".to_owned(),
        Some(s) => format!("Some({})", encode_strength(s)),
    }
}

fn encode_idx_name_pairs(ps: &[(usize, String)]) -> String {
    let mut s = String::from("Nil");
    for (idx, name) in ps.iter().rev() {
        s = format!(
            "Cons(Pr({}, {}), {})",
            encode_u32(u32::try_from(*idx).expect("index fits u32")),
            encode_bytes(name),
            s
        );
    }
    s
}

/// `mono::Item` → the `.myc` `WorkItem` mirror source text (FLAG-semcore-33: `WiFn`/`WiData`/
/// `WiMethod`, Rust's own per-variant field order preserved verbatim).
fn encode_workitem(item: &Item) -> String {
    match item {
        Item::Fn {
            name,
            targs,
            wargs,
            fn_args,
            dyn_fns,
        } => format!(
            "WiFn({}, {}, {}, {}, {})",
            encode_bytes(name),
            encode_ty_list(targs),
            encode_width_list_local(wargs),
            encode_idx_name_pairs(fn_args),
            encode_idx_name_pairs(dyn_fns)
        ),
        Item::Data { name, targs } => {
            format!("WiData({}, {})", encode_bytes(name), encode_ty_list(targs))
        }
        Item::Method {
            trait_name,
            method,
            for_ty,
        } => format!(
            "WiMethod({}, {}, {})",
            encode_bytes(trait_name),
            encode_bytes(method),
            encode_ty(for_ty)
        ),
    }
}

fn encode_width_list_local(ws: &[Width]) -> String {
    let mut s = String::from("Nil");
    for w in ws.iter().rev() {
        s = format!("Cons({}, {})", encode_width(w), s);
    }
    s
}

// Small fixture constructors keeping test bodies to `assert over a case`.
fn bin(n: u32) -> Ty {
    Ty::Binary(Width::Lit(n))
}
fn data(n: &str, args: Vec<Ty>) -> Ty {
    Ty::Data(n.to_owned(), args)
}
fn var(n: &str) -> Ty {
    Ty::Var(n.to_owned())
}
fn arrow(a: Ty, b: Ty) -> Ty {
    Ty::Fn(Box::new(a), Box::new(b))
}

/// Parse → check → monomorphize → eval `main` → DECODE the mirror `L1Value` → `assert_eq!` against
/// the LIVE Rust oracle value (the `marshal_support::assert_l1_marshal` runner, this file's own
/// `Ty`/`TypeRef` decoders).
fn assert_ty_marshal(label: &str, driver: &str, want: Ty) {
    assert_l1_marshal(label, driver, decode_ty, want);
}

fn assert_typeref_marshal(label: &str, driver: &str, want: crate::ast::TypeRef) {
    assert_l1_marshal(label, driver, decode_typeref, want);
}

fn assert_bytes_marshal(label: &str, driver: &str, want: String) {
    assert_l1_marshal(label, driver, decode_string, want);
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// Structural gate: `semcore.myc` (with the STEP-6 additions) parses and type-checks green.
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn semcore_tyref_parses_and_checks() {
    let nodule = parse(SEMCORE_SRC).unwrap_or_else(|e| panic!("semcore.myc: parse failed: {e}"));
    check_nodule(&nodule).unwrap_or_else(|e| panic!("semcore.myc: check failed: {e}"));
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// mangle_ty_in_ty (LIVE — mono::mangle_ty_in_ty): primitive reprs pass through; a nullary/applied
// data type rewrites; a `Seq` recurses into its element.
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn mangle_ty_in_ty_cases() {
    let cases: Vec<Ty> = vec![
        bin(8),
        Ty::Ternary(Width::Lit(6)),
        Ty::Dense(16, crate::ast::Scalar::F32),
        Ty::Bytes,
        Ty::Float,
        data("Bool", vec![]),
        data("List", vec![bin(8)]),
        Ty::Seq(Box::new(data("List", vec![bin(8)])), 4),
        var("N"),
    ];
    for t in cases {
        let want = mangle_ty_in_ty(&t);
        let driver = format!("fn main() => Ty = mangle_ty_in_ty({});\n", encode_ty(&t));
        assert_ty_marshal(&format!("mangle_ty_in_ty({t:?})"), &driver, want);
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// closure_field_ty / closure_param_ref (LIVE — RFC-0024 §4A.2/§4A.4): a `Ty::Fn` becomes the arrow
// tag-sum's nullary data type; everything else round-trips via mangle_ty_in_ty / ty_to_ref.
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn closure_field_ty_cases() {
    let cases: Vec<Ty> = vec![bin(8), data("List", vec![bin(16)]), arrow(bin(8), bin(1))];
    for t in cases {
        let want = closure_field_ty(&t);
        let driver = format!("fn main() => Ty = closure_field_ty({});\n", encode_ty(&t));
        assert_ty_marshal(&format!("closure_field_ty({t:?})"), &driver, want);
    }
}

#[test]
fn closure_param_ref_cases() {
    let cases: Vec<Ty> = vec![bin(8), data("List", vec![bin(16)]), arrow(bin(8), bin(1))];
    for t in cases {
        let want = closure_param_ref(&t);
        let driver = format!(
            "fn main() => TypeRef = closure_param_ref({});\n",
            encode_ty(&t)
        );
        assert_typeref_marshal(&format!("closure_param_ref({t:?})"), &driver, want);
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// ty_to_source_ref / ty_to_ref (LIVE): an applied data type keeps its SOURCE name (source_ref) vs.
// becomes mangled-nullary (ref) — the two round-trip conventions diverge exactly there.
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn ty_to_source_ref_cases() {
    let cases: Vec<Ty> = vec![
        bin(8),
        Ty::Ternary(Width::Var("M".to_owned())),
        Ty::Seq(Box::new(bin(8)), 4),
        data("Pair", vec![bin(8), data("List", vec![bin(1)])]),
        var("N"),
        arrow(bin(8), bin(1)),
    ];
    for t in cases {
        let want = ty_to_source_ref(&t);
        let driver = format!(
            "fn main() => TypeRef = ty_to_source_ref({});\n",
            encode_ty(&t)
        );
        assert_typeref_marshal(&format!("ty_to_source_ref({t:?})"), &driver, want);
    }
}

#[test]
fn ty_to_ref_cases() {
    let cases: Vec<Ty> = vec![
        bin(8),
        Ty::Ternary(Width::Var("M".to_owned())),
        Ty::Seq(Box::new(bin(8)), 4),
        data("Pair", vec![bin(8), data("List", vec![bin(1)])]),
        var("N"),
        arrow(bin(8), bin(1)),
    ];
    for t in cases {
        let want = ty_to_ref(&t);
        let driver = format!("fn main() => TypeRef = ty_to_ref({});\n", encode_ty(&t));
        assert_typeref_marshal(&format!("ty_to_ref({t:?})"), &driver, want);
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// ty_to_ref_tagged (LIVE): like ty_to_ref, but attaches the caller's OWN guarantee — never derived
// from `t`. Exercises BOTH `None` and every `Some(Strength)` level (the decoder's real target).
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn ty_to_ref_tagged_cases() {
    let cases: Vec<(Ty, Option<Strength>)> = vec![
        (bin(8), None),
        (bin(8), Some(Strength::Exact)),
        (data("List", vec![bin(8)]), Some(Strength::Proven)),
        (var("N"), Some(Strength::Empirical)),
        (arrow(bin(8), bin(1)), Some(Strength::Declared)),
    ];
    for (t, g) in cases {
        let want = ty_to_ref_tagged(&t, g);
        let driver = format!(
            "fn main() => TypeRef = ty_to_ref_tagged({}, {});\n",
            encode_ty(&t),
            encode_guarantee(g)
        );
        assert_typeref_marshal(&format!("ty_to_ref_tagged({t:?}, {g:?})"), &driver, want);
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// item_key (LIVE — mono::item_key): the canonical kind-tagged dedup key of a WorkItem, over all
// three variants.
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn item_key_cases() {
    let cases: Vec<Item> = vec![
        Item::Fn {
            name: "add".to_owned(),
            targs: vec![bin(8)],
            wargs: vec![],
            fn_args: vec![],
            dyn_fns: vec![],
        },
        Item::Fn {
            name: "apply_hof".to_owned(),
            targs: vec![],
            wargs: vec![Width::Lit(8)],
            fn_args: vec![(0, "callee$Binary8".to_owned())],
            dyn_fns: vec![(1, "Fn$Binary8$Binary1".to_owned())],
        },
        Item::Data {
            name: "List".to_owned(),
            targs: vec![bin(8)],
        },
        Item::Method {
            trait_name: "Cmp".to_owned(),
            method: "cmp".to_owned(),
            for_ty: bin(8),
        },
    ];
    for item in cases {
        let want = item_key(&item);
        let driver = format!(
            "fn main() => Bytes = item_key({});\n",
            encode_workitem(&item)
        );
        assert_bytes_marshal(&format!("item_key({item:?})"), &driver, want);
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// Non-vacuity probe: a `.myc` literal whose SHAPE differs from the oracle's must NOT decode equal —
// proves the decoder actually reads the dimension it claims to (the established non-vacuity twin).
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn tyref_marshal_discriminates() {
    // `ty_to_ref(Binary{8})` must NOT decode equal to `ty_to_ref(Binary{16})`'s oracle value.
    let want = ty_to_ref(&bin(8));
    let wrong_driver = "fn main() => TypeRef = ty_to_ref(TyBinary(WdLit(0b0000_0000_0000_0000_0000_0000_0001_0000)));\n";
    let src = program(wrong_driver);
    let env = check_nodule(&parse(&src).unwrap_or_else(|e| panic!("parse: {e}")))
        .unwrap_or_else(|e| panic!("check: {e}"));
    let mono = monomorphize(&env, "main").unwrap_or_else(|e| panic!("mono: {e}"));
    let l1_val = Evaluator::new(&mono)
        .call("main", vec![])
        .unwrap_or_else(|e| panic!("eval: {e}"));
    let got = decode_typeref(&l1_val);
    assert_ne!(
        got, want,
        "tyref_marshal_discriminates: Binary{{16}} decoded equal to the Binary{{8}} oracle value \
         -- the decoder is not reading the width dimension"
    );
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// subst_type_param_in_typeref (LIVE — checkty::subst_type_param_in_typeref; DN-54 §10 Model-A, M-973):
// the rule-parameter → concrete-type substitution over a `TypeRef`. This is the FIRST differential to
// need the guarantee slot on the INPUT side — the shared `marshal_support::encode_typeref` forces
// `None` (no prior oracle read it), but subst's subtlest behaviour is the `tr.guarantee.or(
// concrete.guarantee)` first-Some merge — so this file adds a guarantee-THREADING encoder (`enc_tr`);
// the output guarantee is already checked by the shared `decode_typeref` (l128).
// ─────────────────────────────────────────────────────────────────────────────────────────────────

/// A guarantee-threading `TypeRef` → `.myc` source encoder (the shared `encode_typeref` discards the
/// guarantee; `subst` preserves/merges it, so we must emit the REAL `Some(Strength)`/`None`). Atoms
/// carry no nested `TypeRef`, so the shared `encode_basetype` is exact for them.
fn enc_tr(t: &TypeRef) -> String {
    format!(
        "TR({}, {})",
        enc_base(&t.base),
        encode_guarantee(t.guarantee)
    )
}
fn enc_base(b: &BaseType) -> String {
    match b {
        BaseType::Named(n, args) => format!("Named({}, {})", encode_bytes(n), enc_tr_list(args)),
        BaseType::Seq { elem, len } => format!("KwSeq({}, {})", enc_tr(elem), encode_u32(*len)),
        BaseType::Fn(a, r) => format!("FnArrow({}, {})", enc_tr(a), enc_tr(r)),
        BaseType::Tuple(elems) => format!("Tuple({})", enc_tr_list(elems)),
        other => encode_basetype(other),
    }
}
fn enc_tr_list(ts: &[TypeRef]) -> String {
    let mut s = String::from("Nil");
    for t in ts.iter().rev() {
        s = format!("Cons({}, {})", enc_tr(t), s);
    }
    s
}

// Small `TypeRef` fixture constructors (test bodies stay `assert over a case`).
fn tref(base: BaseType) -> TypeRef {
    TypeRef {
        base,
        guarantee: None,
    }
}
fn tref_g(base: BaseType, g: Strength) -> TypeRef {
    TypeRef {
        base,
        guarantee: Some(g),
    }
}
fn bnamed(n: &str, args: Vec<TypeRef>) -> BaseType {
    BaseType::Named(n.to_owned(), args)
}

#[test]
fn subst_type_param_in_typeref_cases() {
    // (input `tr`, rule parameter, concrete replacement) — spanning EVERY BaseType arm plus the
    // guarantee-merge (`Option::or`, first-Some-wins) and the four corners of the Rust
    // `name == param && args.is_empty()` guard.
    let cases: Vec<(TypeRef, &str, TypeRef)> = vec![
        // ── the param hit + its guarantee-merge corners ──────────────────────────────────────────
        // both bare → base replaced, guarantee stays None
        (tref(bnamed("T", vec![])), "T", tref(bnamed("Bool", vec![]))),
        // the occurrence's own `@ Exact` wins over the concrete's (None)
        (
            tref_g(bnamed("T", vec![]), Strength::Exact),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        // a bare occurrence inherits the concrete's `@ Proven`
        (
            tref(bnamed("T", vec![])),
            "T",
            tref_g(bnamed("Bool", vec![]), Strength::Proven),
        ),
        // both tagged → the occurrence's `@ Empirical` wins (left-biased `or`)
        (
            tref_g(bnamed("T", vec![]), Strength::Empirical),
            "T",
            tref_g(bnamed("Bool", vec![]), Strength::Declared),
        ),
        // the concrete is itself a STRUCTURED type — the whole base replaces the parameter
        (
            tref(bnamed("T", vec![])),
            "T",
            tref(BaseType::Seq {
                elem: Box::new(tref(BaseType::Bytes)),
                len: 4,
            }),
        ),
        // ── the guard's negative corners ─────────────────────────────────────────────────────────
        // nullary name != param → returned verbatim (guarantee preserved)
        (
            tref_g(bnamed("U", vec![]), Strength::Declared),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        // name == param BUT applied (args non-empty) → keep the name, recurse the args (Rust arm 2)
        (
            tref(bnamed("T", vec![tref(bnamed("X", vec![]))])),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        // ── structural recursion ─────────────────────────────────────────────────────────────────
        // applied Named recurses into its args
        (
            tref(bnamed("List", vec![tref(bnamed("T", vec![]))])),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        // a nested occurrence's OWN guarantee is preserved through the recursion (List[T @ Empirical])
        (
            tref(bnamed(
                "List",
                vec![tref_g(bnamed("T", vec![]), Strength::Empirical)],
            )),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        // Seq recurses its element, keeps the outer guarantee + length
        (
            tref_g(
                BaseType::Seq {
                    elem: Box::new(tref(bnamed("T", vec![]))),
                    len: 8,
                },
                Strength::Proven,
            ),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        // Fn recurses both sides — only the parameter position substitutes
        (
            tref(BaseType::Fn(
                Box::new(tref(bnamed("T", vec![]))),
                Box::new(tref(bnamed("U", vec![]))),
            )),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        // Tuple recurses each element
        (
            tref(BaseType::Tuple(vec![
                tref(bnamed("T", vec![])),
                tref(BaseType::Bytes),
            ])),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        // ── the verbatim atoms (no nested type-name; whole `tr`, guarantee included, clones) ───────
        (
            tref_g(BaseType::Binary(WidthRef::Lit(8)), Strength::Exact),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        (
            tref(BaseType::Ternary(WidthRef::Name("M".to_owned()))),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        (
            tref(BaseType::Dense(16, Scalar::F32)),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        (
            tref(BaseType::Vsa {
                model: "HRR".to_owned(),
                dim: 1024,
                sparsity: Sparsity::Dense,
            }),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        (
            tref(BaseType::Substrate("gpu".to_owned())),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        (
            tref_g(BaseType::Bytes, Strength::Declared),
            "T",
            tref(bnamed("Bool", vec![])),
        ),
        (tref(BaseType::Float), "T", tref(bnamed("Bool", vec![]))),
    ];
    for (tr, param, concrete) in cases {
        let want = subst_type_param_in_typeref(&tr, param, &concrete);
        let driver = format!(
            "fn main() => TypeRef = subst_type_param_in_typeref({}, {}, {});\n",
            enc_tr(&tr),
            encode_bytes(param),
            enc_tr(&concrete)
        );
        assert_typeref_marshal(
            &format!("subst_type_param_in_typeref({tr:?}, {param}, {concrete:?})"),
            &driver,
            want,
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// Non-vacuity twin: a param hit MUST change the type — the port's output must NOT decode equal to the
// un-substituted input, and MUST equal the live oracle (guards against an identity/echo port).
// ─────────────────────────────────────────────────────────────────────────────────────────────────
#[test]
fn subst_marshal_discriminates() {
    let tr = tref(bnamed("T", vec![]));
    let concrete = tref(bnamed("Bool", vec![]));
    let driver = format!(
        "fn main() => TypeRef = subst_type_param_in_typeref({}, {}, {});\n",
        enc_tr(&tr),
        encode_bytes("T"),
        enc_tr(&concrete)
    );
    let src = program(&driver);
    let env = check_nodule(&parse(&src).unwrap_or_else(|e| panic!("parse: {e}")))
        .unwrap_or_else(|e| panic!("check: {e}"));
    let mono = monomorphize(&env, "main").unwrap_or_else(|e| panic!("mono: {e}"));
    let got = decode_typeref(
        &Evaluator::new(&mono)
            .call("main", vec![])
            .unwrap_or_else(|e| panic!("eval: {e}")),
    );
    assert_ne!(
        got, tr,
        "subst of the parameter itself must not be the identity (the port ignored the substitution)"
    );
    assert_eq!(
        got,
        subst_type_param_in_typeref(&tr, "T", &concrete),
        "port must match the live oracle"
    );
}
