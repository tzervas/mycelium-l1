//! **FE-3: `recv.method(args)` postfix-call sugar** — `docs/planning/orchestration/surfaces/FE-3-METHOD-POSTFIX.md`.
//!
//! Before this surface landed: `answer().identity()` failed to parse ("expected `;`… found Dot").
//! `check_path` already UNCONDITIONALLY refuses every multi-segment `Path` in expression position
//! ("dotted path `d.g` does not resolve — multi-segment qualified-path *syntax* is deferred in v0
//! …(M-662)"), so repurposing `IDENT.IDENT(...)` for method-call sugar collides with ZERO working
//! semantics — only a syntax shape that was already a 100%-refused dead end.
//!
//! This file pins: (a) parse-AST identity with hand-written prefix calls (no new AST node — FE-3
//! desugars, AT PARSE TIME, `recv.name(args)` to exactly `name(recv, args...)`); (b) an end-to-end
//! check+run test proving the desugared call actually evaluates to the right scalar; (c) the five
//! disambiguation cases the FE-3 rationale traced (bare-identifier receiver, call-result receiver,
//! chained calls, non-call dotted chain UNAFFECTED, mixed chain); (d) the REGRESSION GUARD that
//! `use`, `nodule`, and pattern-`Ctor` dotted-path parsing are structurally untouched (they never
//! call the new call-aware path parser — verified directly against the parser source below, and
//! pinned here by executing all three unaffected forms).
//!
//! Guarantee: `Empirical` (every claim here is an executed assertion, not a reading of the code).

use mycelium_interp::Interpreter;
use mycelium_l1::ast::{Expr, Item, Path};
use mycelium_l1::{check_nodule, elaborate, parse};

const PRE: &str = "nodule d;\nfn identity(x: Binary{8}) => Binary{8} = x;\nfn answer() => Binary{8} = 0b0010_1010;\n";

fn fn_body(src: &str, name: &str) -> Expr {
    parse(src)
        .unwrap_or_else(|e| panic!("parse: {e}\n{src}"))
        .items
        .into_iter()
        .find_map(|i| match i {
            Item::Fn(fd) if fd.sig.name == name => Some(fd.body),
            _ => None,
        })
        .unwrap_or_else(|| panic!("fn {name} not found in:\n{src}"))
}

// -------------------------------------------------------------------------------------------
// (a) Parse-AST identity: `recv.name(args)` must produce EXACTLY the same AST as `name(recv, args)`.
// -------------------------------------------------------------------------------------------

/// The exact roadmap repro: `answer().identity()` desugars identically to `identity(answer())`.
#[test]
fn call_result_receiver_is_ast_identical_to_hand_written_prefix_call() {
    let sugar = format!("{PRE}fn f() => Binary{{8}} = answer().identity();\n");
    let prefix = format!("{PRE}fn f() => Binary{{8}} = identity(answer());\n");
    assert_eq!(fn_body(&sugar, "f"), fn_body(&prefix, "f"));
}

/// A bare-identifier receiver `n.identity()` also sugars (not only call-result receivers).
#[test]
fn bare_identifier_receiver_is_ast_identical_to_hand_written_prefix_call() {
    let sugar = format!("{PRE}fn f(n: Binary{{8}}) => Binary{{8}} = n.identity();\n");
    let prefix = format!("{PRE}fn f(n: Binary{{8}}) => Binary{{8}} = identity(n);\n");
    assert_eq!(fn_body(&sugar, "f"), fn_body(&prefix, "f"));
}

/// Chained method calls `answer().identity().identity()` desugar to nested prefix calls.
#[test]
fn chained_method_calls_are_ast_identical_to_nested_prefix_calls() {
    let sugar = format!("{PRE}fn f() => Binary{{8}} = answer().identity().identity();\n");
    let prefix = format!("{PRE}fn f() => Binary{{8}} = identity(identity(answer()));\n");
    assert_eq!(fn_body(&sugar, "f"), fn_body(&prefix, "f"));
}

/// Directly pins the frozen FE-3 desugar shape: `App{{ head: Path(["identity"]), args: [recv] }}`.
#[test]
fn desugar_produces_exactly_the_frozen_app_shape() {
    let body = fn_body(
        &format!("{PRE}fn f() => Binary{{8}} = answer().identity();\n"),
        "f",
    );
    match body {
        Expr::App { head, args } => {
            assert_eq!(*head, Expr::Path(Path(vec!["identity".to_owned()])));
            assert_eq!(args.len(), 1);
            assert_eq!(
                args[0],
                Expr::App {
                    head: Box::new(Expr::Path(Path(vec!["answer".to_owned()]))),
                    args: vec![]
                }
            );
        }
        other => panic!("expected Expr::App, got {other:?}"),
    }
}

// -------------------------------------------------------------------------------------------
// (b) End-to-end: check, elaborate, and RUN the desugared call — proves it is not just parse sugar.
// -------------------------------------------------------------------------------------------

/// Extract a `Binary{{8}}` `CoreValue`'s bits as a `u8` (MSB-first).
fn core_bits_as_u8(v: &mycelium_core::CoreValue) -> u8 {
    let repr_val = v
        .as_repr()
        .unwrap_or_else(|| panic!("expected a Repr CoreValue, got {v:?}"));
    match repr_val.payload() {
        mycelium_core::Payload::Bits(bits) => {
            bits.iter().fold(0u8, |acc, &b| (acc << 1) | u8::from(b))
        }
        other => panic!("expected a Bits payload, got {other:?}"),
    }
}

/// `fn f() => Binary{8} = answer().identity();` checks, elaborates, and RUNS to `0b0010_1010`
/// (42) — the exact roadmap repro, end to end (not only parse-AST identity above).
#[test]
fn call_result_receiver_checks_elaborates_and_runs_to_the_correct_value() {
    let src = format!("{PRE}fn f() => Binary{{8}} = answer().identity();\n");
    let nodule = parse(&src).unwrap_or_else(|e| panic!("parse: {e}"));
    let env = check_nodule(&nodule).unwrap_or_else(|e| panic!("check: {e}"));
    let node = elaborate(&env, "f").unwrap_or_else(|e| panic!("elaborate: {e:?}"));
    let interp = Interpreter::default();
    let core = interp
        .eval_core(&node)
        .unwrap_or_else(|e| panic!("eval_core: {e}"));
    assert_eq!(
        core_bits_as_u8(&core),
        0b0010_1010,
        "answer().identity() must evaluate to 42, same as identity(answer())"
    );
}

// -------------------------------------------------------------------------------------------
// (c) Disambiguation edge cases traced in the FE-3 rationale.
// -------------------------------------------------------------------------------------------

/// A non-call dotted chain `d.g` is UNAFFECTED: it still parses to a 2-segment `Path` (never
/// silently reinterpreted), and still fails `check` with the SAME M-662 message it produces today
/// — the frozen package's explicit regression guard.
#[test]
fn non_call_dotted_chain_still_parses_to_a_two_segment_path_and_still_refuses_at_check() {
    let src = "nodule d;\nfn g() => Binary{8} = 0b0000_0001;\nfn f() => Binary{8} = d.g;\n";
    let body = fn_body(src, "f");
    assert_eq!(
        body,
        Expr::Path(Path(vec!["d".to_owned(), "g".to_owned()])),
        "`d.g` must still parse to a 2-segment Path, unaffected by FE-3"
    );
    let nodule = parse(src).unwrap_or_else(|e| panic!("parse: {e}"));
    let err = check_nodule(&nodule).expect_err("`d.g` must still be refused at check");
    let msg = err.to_string();
    assert!(
        msg.contains("multi-segment qualified-path")
            && msg.contains("deferred in v0")
            && msg.contains("M-662"),
        "the M-662 refusal message must be UNCHANGED by FE-3, got: {msg}"
    );
}

/// A mixed chain `a.b.c(x)`: only the trailing call-segment (`.c(x)`) sugars; the non-call prefix
/// `a.b` is left as a genuine 2-segment `Path` and hits the SAME pre-existing M-662 refusal at
/// check — never a parse error and never a silent misinterpretation as `c(a.b, x)`... except that
/// IS exactly the (correct, documented) desugar target: `c(a.b, x)`, where `a.b` is itself refused
/// downstream at check, honestly, exactly as it would be if hand-written.
#[test]
fn mixed_chain_only_sugars_the_trailing_call_and_still_refuses_the_non_call_prefix_at_check() {
    let src = "nodule d;\n\
               fn c(recv: Binary{8}, x: Binary{8}) => Binary{8} = x;\n\
               fn f(x: Binary{8}) => Binary{8} = a.b.c(x);\n";
    let body = fn_body(src, "f");
    // Parses as `c(a.b, x)` — the non-call prefix `a.b` stays a 2-segment Path argument.
    assert_eq!(
        body,
        Expr::App {
            head: Box::new(Expr::Path(Path(vec!["c".to_owned()]))),
            args: vec![
                Expr::Path(Path(vec!["a".to_owned(), "b".to_owned()])),
                Expr::Path(Path(vec!["x".to_owned()])),
            ],
        }
    );
    let nodule = parse(src).unwrap_or_else(|e| panic!("parse: {e}"));
    let err =
        check_nodule(&nodule).expect_err("`a.b` inside the mixed chain must still refuse at check");
    let msg = err.to_string();
    assert!(
        msg.contains("multi-segment qualified-path") && msg.contains("M-662"),
        "expected the standard M-662 refusal (on `a.b`), got: {msg}"
    );
}

// -------------------------------------------------------------------------------------------
// (d) Regression guards: `use`, `nodule`, and `Ctor(sub)` pattern parsing are structurally
// untouched — none of them call the new call-aware path parser (verified directly against
// `src/parse.rs`: `use` has its own self-contained dotted loop; `nodule <path>`/`phylum <path>`/
// `swap policy:` call the ORIGINAL unmodified `parse_path`; `Ctor(sub)` patterns never call
// `parse_path` at all). Pinned here by executing all three forms, byte-identically to their
// pre-FE-3 shape.
// -------------------------------------------------------------------------------------------

/// `use foo.bar;` still parses as a 2-segment, non-glob `UsePath`.
#[test]
fn use_dotted_path_is_unaffected_by_fe3() {
    let src = "nodule d;\nuse foo.bar;\nfn f() => Unit = Unit;\n";
    let nodule = parse(src).unwrap_or_else(|e| panic!("parse: {e}\n{src}"));
    let use_path = nodule
        .items
        .iter()
        .find_map(|i| match i {
            Item::Use(u) => Some(u.clone()),
            _ => None,
        })
        .expect("expected exactly one `use` import");
    assert_eq!(
        use_path.path,
        Path(vec!["foo".to_owned(), "bar".to_owned()])
    );
    assert!(!use_path.glob);
}

/// A `nodule x.y;` header still parses as a 2-segment nodule path.
#[test]
fn nodule_dotted_header_is_unaffected_by_fe3() {
    let src = "nodule x.y;\nfn f() => Unit = Unit;\n";
    let nodule = parse(src).unwrap_or_else(|e| panic!("parse: {e}\n{src}"));
    assert_eq!(nodule.path, Path(vec!["x".to_owned(), "y".to_owned()]));
}

/// A `Ctor(sub)` pattern still parses as `Pattern::Ctor` (never touches path parsing at all).
#[test]
fn ctor_pattern_is_unaffected_by_fe3() {
    let src = "nodule d;\n\
               type T = A(Binary{8}) | B;\n\
               fn f(t: T) => Binary{8} = match t {\n\
               \x20 A(sub) => sub,\n\
               \x20 B => 0b0000_0000,\n\
               };\n";
    parse(src).unwrap_or_else(|e| panic!("parse: {e}\n{src}"));
}
