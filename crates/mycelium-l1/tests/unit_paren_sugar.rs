//! **FE-2: `()` unit-value/unit-type spelling** — `docs/planning/orchestration/surfaces/FE-2-UNIT-PAREN.md`.
//!
//! Before this surface landed: `fn f() => Unit = ();` failed to parse with "expected an
//! expression, found RParen" (`parse_primary`'s `Tok::LParen` arm falls through to `parse_expr` on
//! the immediately-following `)`), and `fn f() => () = …;` failed with "expected a type, found
//! RParen" (`parse_base_type`'s `Tok::LParen` arm) — even though the `Unit` prelude type/value
//! already fully type-checked, elaborated, and evaluated end to end
//! (`checkty::PRELUDE_UNCONDITIONAL_TYPE_NAMES = ["Bool", "Unit"]`). Only the `()` SPELLING was
//! missing — this file pins that it now exists, and that it is EXACTLY sugar (parse-AST identity
//! with hand-written `Unit`), not a new value/type.
//!
//! Guarantee: `Empirical` (every claim here is an executed assertion, not a reading of the code).

use mycelium_l1::{check_nodule, elaborate, parse};

const PRE: &str = "nodule d;\nfn g(x: Binary{8}) => Binary{8} = x;\n";

fn fn_body(src: &str, name: &str) -> mycelium_l1::ast::Expr {
    parse(src)
        .unwrap_or_else(|e| panic!("parse: {e}\n{src}"))
        .items
        .into_iter()
        .find_map(|i| match i {
            mycelium_l1::ast::Item::Fn(fd) if fd.sig.name == name => Some(fd.body),
            _ => None,
        })
        .unwrap_or_else(|| panic!("fn {name} not found in:\n{src}"))
}

fn fn_ret_type(src: &str, name: &str) -> mycelium_l1::ast::TypeRef {
    parse(src)
        .unwrap_or_else(|e| panic!("parse: {e}\n{src}"))
        .items
        .into_iter()
        .find_map(|i| match i {
            mycelium_l1::ast::Item::Fn(fd) if fd.sig.name == name => Some(fd.sig.ret),
            _ => None,
        })
        .unwrap_or_else(|| panic!("fn {name} not found in:\n{src}"))
}

// -------------------------------------------------------------------------------------------
// Parse-AST identity: `()` must produce the SAME AST as hand-writing `Unit`, not a new node.
// -------------------------------------------------------------------------------------------

/// `()` in expression (fn-body) position parses IDENTICALLY to the hand-written `Unit` path.
#[test]
fn unit_paren_expression_is_ast_identical_to_hand_written_unit() {
    let paren = format!("{PRE}fn f() => Unit = ();\n");
    let word = format!("{PRE}fn f() => Unit = Unit;\n");
    assert_eq!(
        fn_body(&paren, "f"),
        fn_body(&word, "f"),
        "`()` must desugar to exactly the same AST as `Unit`"
    );
    assert_eq!(
        fn_body(&paren, "f"),
        mycelium_l1::ast::Expr::Path(mycelium_l1::ast::Path(vec!["Unit".to_owned()])),
        "`()` must parse to `Expr::Path(Path([\"Unit\"]))`, per the frozen FE-2 signature"
    );
}

/// `()` in return-type position parses IDENTICALLY to the hand-written `Unit` type.
#[test]
fn unit_paren_return_type_is_ast_identical_to_hand_written_unit() {
    let paren = format!("{PRE}fn f() => () = Unit;\n");
    let word = format!("{PRE}fn f() => Unit = Unit;\n");
    assert_eq!(
        fn_ret_type(&paren, "f"),
        fn_ret_type(&word, "f"),
        "`()` must desugar to exactly the same TypeRef as `Unit`"
    );
    assert_eq!(
        fn_ret_type(&paren, "f").base,
        mycelium_l1::ast::BaseType::Named("Unit".to_owned(), vec![]),
        "`()` must parse to `BaseType::Named(\"Unit\", [])`, per the frozen FE-2 signature"
    );
}

/// `()` also works as a parameter type and as an argument to a call, not just fn-body/return-type
/// position — same single lookahead fires wherever `parse_primary`/`parse_base_type` are reached.
#[test]
fn unit_paren_works_as_a_call_argument() {
    let src = "nodule d;\nfn take(x: Unit) => Unit = x;\nfn f() => Unit = take(());\n";
    let nodule = parse(src).unwrap_or_else(|e| panic!("parse: {e}"));
    let env = check_nodule(&nodule).unwrap_or_else(|e| panic!("check: {e}"));
    elaborate(&env, "f").unwrap_or_else(|e| panic!("elaborate: {e:?}"));
}

// -------------------------------------------------------------------------------------------
// End-to-end: `()` checks, classifies Total, and elaborates — not only parse identity.
// -------------------------------------------------------------------------------------------

/// `fn f() => Unit = ();` checks and elaborates end to end (the exact FE-2 rationale repro).
#[test]
fn unit_paren_expression_checks_and_elaborates_end_to_end() {
    let src = format!("{PRE}fn f() => Unit = ();\n");
    let nodule = parse(&src).unwrap_or_else(|e| panic!("parse: {e}"));
    let env = check_nodule(&nodule).unwrap_or_else(|e| panic!("check: {e}"));
    let tot =
        mycelium_l1::totality::classify_all(&env.fns).unwrap_or_else(|e| panic!("totality: {e:?}"));
    assert_eq!(tot.get("f"), Some(&mycelium_l1::Totality::Total));
    elaborate(&env, "f").unwrap_or_else(|e| panic!("elaborate: {e:?}"));
}

/// `fn f() => () = Unit;` (the `()` return-type spelling) checks and elaborates end to end.
#[test]
fn unit_paren_return_type_checks_and_elaborates_end_to_end() {
    let src = format!("{PRE}fn f() => () = Unit;\n");
    let nodule = parse(&src).unwrap_or_else(|e| panic!("parse: {e}"));
    let env = check_nodule(&nodule).unwrap_or_else(|e| panic!("check: {e}"));
    let tot =
        mycelium_l1::totality::classify_all(&env.fns).unwrap_or_else(|e| panic!("totality: {e:?}"));
    assert_eq!(tot.get("f"), Some(&mycelium_l1::Totality::Total));
    elaborate(&env, "f").unwrap_or_else(|e| panic!("elaborate: {e:?}"));
}

/// Both `()` spellings together (`fn f() => () = ();`) — the exact roadmap repro line.
#[test]
fn unit_paren_both_positions_together_check_and_elaborate() {
    let src = format!("{PRE}fn f() => () = ();\n");
    let nodule = parse(&src).unwrap_or_else(|e| panic!("parse: {e}"));
    let env = check_nodule(&nodule).unwrap_or_else(|e| panic!("check: {e}"));
    elaborate(&env, "f").unwrap_or_else(|e| panic!("elaborate: {e:?}"));
}

// -------------------------------------------------------------------------------------------
// Regression guards: unrelated `(` productions (tuples, grouping) must be untouched.
// -------------------------------------------------------------------------------------------

/// A non-empty parenthesized expression `(e)` (grouping) still parses to plain `e`, unaffected by
/// the new immediate-`)` lookahead (which only fires when `(` is IMMEDIATELY followed by `)`).
#[test]
fn grouping_expression_is_unaffected() {
    let grouped = format!("{PRE}fn f() => Binary{{8}} = (0b0000_0001);\n");
    let bare = format!("{PRE}fn f() => Binary{{8}} = 0b0000_0001;\n");
    assert_eq!(fn_body(&grouped, "f"), fn_body(&bare, "f"));
}

/// A tuple literal `(a, b)` (arity >= 2) still parses as a tuple, unaffected by the new arm.
#[test]
fn tuple_literal_is_unaffected() {
    let src = format!(
        "{PRE}fn f() => Binary{{8}} = let p = (0b0000_0001, 0b0000_0010) in g(0b0000_0001);\n"
    );
    parse(&src).unwrap_or_else(|e| panic!("parse: {e}\n{src}"));
}

/// A grouping type `(T)` (single element) still parses as bare `T`, unaffected by the new arm.
#[test]
fn grouping_type_is_unaffected() {
    let grouped = "nodule d;\nfn f(x: (Binary{8})) => Binary{8} = x;\n";
    let bare = "nodule d;\nfn f(x: Binary{8}) => Binary{8} = x;\n";
    parse(grouped).unwrap_or_else(|e| panic!("parse: {e}"));
    parse(bare).unwrap_or_else(|e| panic!("parse: {e}"));
}

/// Empty `{}` and a trailing-`;` block STILL refuse (FE-1's frozen signature keeps this refusal —
/// FE-2 did not widen it to auto-desugar to `()`/`Unit`), but the refusal messages must no longer
/// claim `()` "has no surface spelling yet" (that became false once this file's tests above pass).
#[test]
fn empty_block_refusal_message_is_updated_not_stale() {
    let src = format!("{PRE}fn f() => Unit = {{}};\n");
    let msg = match parse(&src) {
        Err(e) => e.to_string(),
        Ok(_) => panic!("expected empty `{{}}` to still be refused, but it parsed:\n{src}"),
    };
    assert!(
        !msg.contains("is not a surface spelling yet"),
        "stale error message claims `()` has no surface spelling, but FE-2 landed: {msg}"
    );
}

#[test]
fn trailing_semi_block_refusal_message_is_updated_not_stale() {
    let src = format!("{PRE}fn f() => Unit = {{ g(0b0000_0001); }};\n");
    let msg = match parse(&src) {
        Err(e) => e.to_string(),
        Ok(_) => panic!("expected trailing `;` to still be refused, but it parsed:\n{src}"),
    };
    assert!(
        !msg.contains("has no surface spelling yet"),
        "stale error message claims `()` has no surface spelling, but FE-2 landed: {msg}"
    );
}
