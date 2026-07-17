//! M-740 Stage 5 (M-1013 checkty PR-2; DN-26 §7.3 row 5) — the self-hosted `compiler.semcore` port
//! of two PURE `checkty.rs` classifiers: `paradigm_name` (checkty.rs 7175-7197) and
//! `cons_list_ctors` (checkty.rs 3592-3624), ported as `paradigm_name` / `cons_list_ctors` (with the
//! `cons_list_scan` fold helper) in `lib/compiler/semcore.myc`.
//!
//! **Live-oracle posture (VR-5 / DN-26 §10.2 harness marshalling).** Each case calls the REAL Rust
//! oracle (both widened to `pub(crate)` this leaf — zero logic change) on a fixture, then evaluates
//! the `.myc` mirror driver through the established `check → monomorphize("main") → Evaluator::call`
//! pipeline (`marshal_support::assert_l1_marshal`), DECODES the returned `L1Value`, and compares with
//! Rust's own derived `==`. Neither function touches the CEK evaluator, the prim registry, or the
//! trusted kernel `Value`; both are pure structural computation over the already-ported `Ty` /
//! `DataInfo` vocabulary — which is exactly why they port cleanly with no new FLAG-semcore deviation
//! (`paradigm_name`: the established `&'static str → Bytes` idiom; `cons_list_ctors`: the
//! already-established FLAG-semcore-4 `Vec[DataInfo]` + `types_lookup` stand-in for `BTreeMap`).
//!
//! `DataInfo` fixtures are EXTRACTED from a parsed + checked nodule's `env.types` (never hand-built),
//! so a marshalling bug can never hide behind a hand-typed registry mismatch (the evalmatch
//! precedent). Both directions carry a non-vacuity `*_discriminates` twin.

use std::collections::BTreeMap;

use crate::ast::{Scalar, Sparsity};
use crate::checkty::{check_nodule, CtorInfo, DataInfo, Ty, Width};
use crate::eval::L1Value;
use crate::parse;
use crate::tests::marshal_support::*;

// ── DataInfo / CtorInfo registry encoders (module-local — the shared `marshal_support` carries only
// the type-agnostic primitives; each increment's ADT-mirror encoders stay in its own file, mirroring
// `compiler_stage5_evalmatch.rs` / `compiler_stage5_register.rs`) ─────────────────────────────────────

fn encode_names(ns: &[String]) -> String {
    let mut s = String::from("Nil");
    for n in ns.iter().rev() {
        s = format!("Cons({}, {})", encode_bytes(n), s);
    }
    s
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

/// The port returns `Option[Pair[Bytes, Bytes]]`; decode the `Pr(nil, cons)` payload.
fn decode_pair_bytes(v: &L1Value) -> (String, String) {
    let (ctor, fields) = expect_data(v, "Pair");
    match ctor {
        "Pr" => (decode_string(&fields[0]), decode_string(&fields[1])),
        c => panic!("marshal decode_pair_bytes: unexpected ctor {c}"),
    }
}

// ── the classify fixture: list / non-list / arity types, extracted from a checked `env.types` ────────
//
// MyList  — the canonical 2-ctor monomorphic linked list (nil + cons whose 2nd field is Self).
// PList   — a PARAMETRIC list: cons's 2nd field `PList[a]` is Self at arity 1 (exercises the
//           `fargs.len() == di.params.len()` arity guard).
// Pair2   — 2 ctors, but the binary ctor's 2nd field is a scalar, not the Self reference.
// Weird   — 2 ctors, but the binary ctor's 2nd field is a DIFFERENT data type (name mismatch).
// Triple  — 3 ctors (the `di.ctors.len() != 2` early-out).
// Single  — 1 ctor (also the `!= 2` early-out).
// TwoUnary— 2 ctors, both 1-field (exercises cons_list_scan's 1-field path AND the (None, None)
//           final combination — neither ctor is nullary or a 2-field self-ref).
// ThreeF  — 2 ctors: nullary + a 3-FIELD ctor (exercises cons_list_scan's 3+-field path).
// NoNil   — 2 ctors, NO nullary (a 1-field ctor + a 2-field self-ref cons); exercises the
//           (None, Some) final combination — cons is set, nil never is. Kept inhabited (NN1 has a
//           base, non-recursive form) so the checker accepts it.
const FIXTURE_SRC: &str = "nodule test.classify_fixture;\n\
     type MyList = LNil | LCons(Binary{8}, MyList);\n\
     type PList[a] = PNil | PCons(a, PList[a]);\n\
     type Pair2 = P0 | P2(Binary{8}, Binary{8});\n\
     type Weird = WNil | WCons(Binary{8}, Pair2);\n\
     type Triple = T0 | T1(Binary{8}) | T2(Binary{8}, MyList);\n\
     type Single = SOnly;\n\
     type TwoUnary = TU1(Binary{8}) | TU2(Binary{8});\n\
     type ThreeF = TFNil | TFCons(Binary{8}, Binary{8}, ThreeF);\n\
     type NoNil = NN1(Binary{8}) | NN2(Binary{8}, NoNil);\n\
     fn classify_probe() => Binary{1} = 0b1;\n";

fn fixture_registry() -> BTreeMap<String, DataInfo> {
    check_nodule(&parse(FIXTURE_SRC).unwrap_or_else(|e| panic!("fixture parse: {e}")))
        .unwrap_or_else(|e| panic!("fixture check: {e}"))
        .types
}

/// The oracle's `&BTreeMap` registry, as the `.myc` `Vec[DataInfo]` argument — encoded from the SAME
/// `DataInfo`s the oracle looks up (lookup is by name, so the flattened order is immaterial).
fn registry_vec(reg: &BTreeMap<String, DataInfo>) -> Vec<DataInfo> {
    reg.values().cloned().collect()
}

// ── structural gate ───────────────────────────────────────────────────────────────────────────────
#[test]
fn semcore_classify_parses_and_checks() {
    let nodule = parse(SEMCORE_SRC).unwrap_or_else(|e| panic!("semcore.myc: parse failed: {e}"));
    check_nodule(&nodule).unwrap_or_else(|e| panic!("semcore.myc: check failed: {e}"));
}

// ── paradigm_name differential ──────────────────────────────────────────────────────────────────────

fn assert_paradigm_name(label: &str, ty: &Ty) {
    let want: Option<String> = crate::checkty::paradigm_name(ty).map(str::to_owned);
    let driver = format!(
        "fn main() => Option[Bytes] = paradigm_name({});\n",
        encode_ty(ty)
    );
    assert_l1_marshal(label, &driver, |v| decode_option(v, decode_string), want);
}

#[test]
fn paradigm_name_all_arms() {
    // All 11 `Ty` arms: the four swap-paradigms name themselves; every other repr / non-repr is None.
    let cases: Vec<(&str, Ty)> = vec![
        ("Binary", Ty::Binary(Width::Lit(8))),
        (
            "Ternary (var width)",
            Ty::Ternary(Width::Var("m".to_owned())),
        ),
        ("Dense", Ty::Dense(4, Scalar::F32)),
        (
            "VSA",
            Ty::Vsa {
                model: "MAP-I".to_owned(),
                dim: 1024,
                sparsity: Sparsity::Dense,
            },
        ),
        ("Seq -> None", Ty::Seq(Box::new(Ty::Bytes), 3)),
        ("Bytes -> None", Ty::Bytes),
        ("Float -> None", Ty::Float),
        ("Data -> None", Ty::Data("Foo".to_owned(), vec![])),
        ("Substrate -> None", Ty::Substrate("s".to_owned())),
        ("Var -> None", Ty::Var("a".to_owned())),
        (
            "Fn -> None",
            Ty::Fn(Box::new(Ty::Bytes), Box::new(Ty::Bytes)),
        ),
    ];
    for (label, ty) in cases {
        assert_paradigm_name(label, &ty);
    }
}

// ── cons_list_ctors differential ──────────────────────────────────────────────────────────────────

fn assert_cons_list_ctors(label: &str, reg: &BTreeMap<String, DataInfo>, expected: &Ty) {
    let want: Option<(String, String)> = crate::checkty::cons_list_ctors(reg, expected);
    let driver = format!(
        "fn main() => Option[Pair[Bytes, Bytes]] = cons_list_ctors({}, {});\n",
        encode_data_info_list(&registry_vec(reg)),
        encode_ty(expected)
    );
    assert_l1_marshal(
        label,
        &driver,
        |v| decode_option(v, decode_pair_bytes),
        want,
    );
}

#[test]
fn cons_list_ctors_cases() {
    let reg = fixture_registry();
    // `expected`'s own type-args are irrelevant (`cons_list_ctors` reads only the *registered*
    // type's shape via `name`), so the PList case passes a 1-arg mention purely for realism.
    let cases: Vec<(&str, Ty)> = vec![
        (
            "MyList — 2-ctor monomorphic linked list",
            Ty::Data("MyList".to_owned(), vec![]),
        ),
        (
            "PList[Binary{8}] — parametric list, arity-1 self-ref",
            Ty::Data("PList".to_owned(), vec![Ty::Binary(Width::Lit(8))]),
        ),
        (
            "Pair2 — binary ctor's 2nd field is not the Self ref",
            Ty::Data("Pair2".to_owned(), vec![]),
        ),
        (
            "Weird — binary ctor's 2nd field is a DIFFERENT data type",
            Ty::Data("Weird".to_owned(), vec![]),
        ),
        ("Triple — 3 ctors", Ty::Data("Triple".to_owned(), vec![])),
        ("Single — 1 ctor", Ty::Data("Single".to_owned(), vec![])),
        (
            "Nonexistent — name not in the registry",
            Ty::Data("Nope".to_owned(), vec![]),
        ),
        ("Binary — not a Data type at all", Ty::Binary(Width::Lit(8))),
        // The next three isolate cons_list_scan / final-match branches the four cases above never
        // reach (each is structurally non-divergent from Rust, so these are silent-bug guards):
        (
            "TwoUnary — both ctors 1-field: exercises the 1-field scan path AND the (None,None) final",
            Ty::Data("TwoUnary".to_owned(), vec![]),
        ),
        (
            "ThreeF — cons candidate has 3 fields: exercises the 3+-field scan path",
            Ty::Data("ThreeF".to_owned(), vec![]),
        ),
        (
            "NoNil — two 2-field self-ref ctors, no nullary: exercises the (None,Some) final",
            Ty::Data("NoNil".to_owned(), vec![]),
        ),
    ];
    // NOTE (coverage — deliberately not isolated): the arity-guard's False sub-case (a ctor whose
    // 2nd field IS `Data(name, ..)` at the WRONG arity) is unreachable through a well-typed fixture —
    // the checker enforces type-mention arity, so a self-reference in a checked program always has the
    // matching arity. Exercising it would require a hand-built, ill-typed registry, which would forfeit
    // the "extracted from a checked env.types, never hand-built" robustness this file relies on; the
    // FAITHFULNESS review hand-traced this arm as equivalent to Rust's `fargs.len() == di.params.len()`.
    for (label, expected) in cases {
        assert_cons_list_ctors(label, &reg, &expected);
    }
}

// ── non-vacuity twins (prove each decoder actually reads what it claims) ──────────────────────────────

#[test]
fn paradigm_name_marshal_discriminates() {
    let got = decode_driver(
        "Option[Bytes]",
        &format!("paradigm_name({})", encode_ty(&Ty::Ternary(Width::Lit(8)))),
        |v| decode_option(v, decode_string),
    );
    assert_eq!(got, Some("Ternary".to_owned()));
    assert_ne!(
        got,
        Some("Binary".to_owned()),
        "paradigm_name decoder is not reading the paradigm string"
    );
}

#[test]
fn cons_list_ctors_marshal_discriminates() {
    // DN-112 Rank 1 / M-1036 (DoD item 8, flagged `.myc`-parity residual — see
    // `marshal_support::unqualify_types_map`): `MyList`'s self-recursive ctor field is nodule-
    // qualified on the Rust side (`FIXTURE_SRC`'s home is `test.classify_fixture`), but the `.myc`
    // mirror does not yet compare qualified names — strip qualification from the encoded registry
    // so this `.myc`-only structural test still exercises `cons_list_ctors`'s recursion-detection
    // shape (a bare query against a bare-recursion-encoded registry, exactly as before this fix).
    let reg = unqualify_types_map(fixture_registry());
    let got = decode_driver(
        "Option[Pair[Bytes, Bytes]]",
        &format!(
            "cons_list_ctors({}, TyData(\"MyList\", Nil))",
            encode_data_info_list(&registry_vec(&reg))
        ),
        |v| decode_option(v, decode_pair_bytes),
    );
    assert_eq!(got, Some(("LNil".to_owned(), "LCons".to_owned())));
    assert_ne!(
        got,
        Some(("LCons".to_owned(), "LNil".to_owned())),
        "cons_list_ctors decoder is not order-sensitive on the (nil, cons) pair"
    );
}
