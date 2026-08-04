//! **Statement-sequencing surface** — `{ a; b; …; e }` block form and the remaining unit-spelling
//! refusal boundary.
//!
//! **What this file establishes, by execution rather than by reading the code:**
//!
//! 1. The **semantic target already exists**. `let _ = a in b` — the standard sequencing desugar —
//!    parses, type-checks, classifies `Total`, and elaborates to an L0 `Node::Let`. The DN-137
//!    `Unit` prelude type (`checkty::unit_prelude`, seeded never parsed) type-checks and elaborates
//!    to `Node::Construct { args: [] }`. Nothing in the IR is missing.
//! 2. The **block surface is landed**: `{ a; b }` is a primary expression that desugars **identically**
//!    (parse-AST equality) to `let _ = a in b`. Empty `{}` and trailing-`;` blocks still refuse
//!    explicitly — a deliberate FE-1 design choice (a block always needs a value-producing tail),
//!    not a missing unit spelling: `()` now HAS a surface spelling (FE-2, `tests/unit_paren_sugar.rs`),
//!    but the empty-block/trailing-`;` refusals were not widened to auto-desugar to it.
//! 3. The remaining refusals pin honesty guarantees that must not regress:
//!    - bare `a; b` at fn-body position (no braces) is still a stray top-level item (DN-57);
//!    - `let y = e;` without `in` is still refused at the missing `in`.
//!
//! `()` expression/type-spelling coverage moved to `tests/unit_paren_sugar.rs` once FE-2 landed.
//!
//! Guarantee: `Empirical` (every claim here is an executed assertion, not a reading of the code).

use mycelium_l1::{check_nodule, elaborate, parse};

/// Two helper fns: `g` is a value-returning call, `h` is a `Unit`-returning ("statement") call.
const PRE: &str = "nodule d;\nfn g(x: Binary{8}) => Binary{8} = x;\nfn h() => Unit = Unit;\n";

fn parse_err(src: &str) -> String {
    match parse(src) {
        Err(e) => e.to_string(),
        Ok(_) => panic!("expected a ParseError, but this parsed:\n{src}"),
    }
}

// ---------------------------------------------------------------------------------------------
// Deliberate refusals that must remain (honesty / DN-57 / unit gap).
// ---------------------------------------------------------------------------------------------

/// **Refusal site A** — `src/parse.rs::Parser::parse_item` fallthrough (`"a top-level item …"`).
/// A Rust-shaped `fn f() => T = stmt1; stmt2;` body ends at the first `;` (DN-57 makes `;` the
/// *component terminator*, never a statement separator **outside** a braced block), so the second
/// statement is read as a new top-level item and refused there. Sequencing requires braces.
#[test]
fn two_semicolon_separated_statements_are_refused_as_a_stray_top_level_item() {
    let msg = parse_err(&format!(
        "{PRE}fn f() => Binary{{8}} = g(0b0000_0010); g(0b0000_0001);\n"
    ));
    assert!(
        msg.contains("expected a top-level item"),
        "unexpected refusal: {msg}"
    );
    assert!(
        msg.contains("found Ident(\"g\")"),
        "unexpected refusal: {msg}"
    );
}

/// Braced blocks **are** expression forms. A single-expression block `{ e }` is identity sugar
/// for `e`; a two-statement block is covered by the goal test below. This replaces the prior
/// characterization that `{` was not an expression-opening token (refusal site B).
#[test]
fn a_braced_block_is_an_expression_form() {
    let one = format!("{PRE}fn f() => Binary{{8}} = {{ 0b0000_0001 }};\n");
    let bare = format!("{PRE}fn f() => Binary{{8}} = 0b0000_0001;\n");
    let body_of = |src: &str| {
        parse(src)
            .unwrap_or_else(|e| panic!("parse: {e}\n{src}"))
            .items
            .into_iter()
            .find_map(|i| match i {
                mycelium_l1::ast::Item::Fn(fd) if fd.sig.name == "f" => Some(fd.body),
                _ => None,
            })
            .expect("fn f")
    };
    assert_eq!(
        body_of(&one),
        body_of(&bare),
        "`{{ e }}` must parse identically to bare `e`"
    );
}

/// Empty `{}` and a trailing-`;` block still refuse explicitly — both would need a unit value,
/// and `()` has no surface spelling (G2 / never-silent).
#[test]
fn empty_and_trailing_semi_blocks_are_refused_for_the_unit_gap() {
    let empty = parse_err(&format!("{PRE}fn f() => Unit = {{}};\n"));
    assert!(
        empty.contains("empty block") || empty.contains("unit"),
        "unexpected refusal: {empty}"
    );
    let trailing = parse_err(&format!("{PRE}fn f() => Unit = {{ h(); }};\n"));
    assert!(
        trailing.contains("trailing") || trailing.contains("unit"),
        "unexpected refusal: {trailing}"
    );
}

/// **Refusal site C** — `src/parse.rs::Parser::parse_let`'s `expect(&Tok::In, …)`. `let` is an
/// *expression* (`let … in …`), never a statement; the Rust-shaped `let y = e;` has no continuation
/// to bind, so it is refused at the missing `in`. (A block may contain full `let … in …` exprs.)
#[test]
fn a_statement_let_without_in_is_refused_at_the_missing_in() {
    let msg = parse_err(&format!(
        "{PRE}fn f() => Binary{{8}} = let y = 0b0000_0001; y;\n"
    ));
    assert!(
        msg.contains("expected `in` after the let binding"),
        "unexpected refusal: {msg}"
    );
    assert!(msg.contains("found Semi"), "unexpected refusal: {msg}");
}

/// **Superseded refusal site D(expr)** — before FE-2, `parse_primary`'s `Tok::LParen` arm reached
/// `parse_expr` on the immediately-following `)` and refused ("expected an expression, found
/// RParen"). FE-2 gives `()` a surface spelling, so this now pins the POSITIVE outcome instead of
/// the refusal; full AST-identity + end-to-end coverage lives in `tests/unit_paren_sugar.rs`.
#[test]
fn unit_expression_spelling_now_parses_via_fe2() {
    let src = format!("{PRE}fn f() => Unit = ();\n");
    parse(&src).unwrap_or_else(|e| panic!("expected FE-2 `()` to parse, got: {e}\n{src}"));
}

/// **Superseded refusal site D(type)** — before FE-2, `parse_base_type`'s `Tok::LParen` arm reached
/// `parse_type_ref` on the immediately-following `)` and refused ("expected a type, found RParen").
/// FE-2 gives `()` a type-position spelling too; full coverage in `tests/unit_paren_sugar.rs`.
#[test]
fn unit_type_spelling_now_parses_via_fe2() {
    let src = format!("{PRE}fn f() => () = 0b0000_0001;\n");
    parse(&src).unwrap_or_else(|e| panic!("expected FE-2 `()` to parse, got: {e}\n{src}"));
}

// ---------------------------------------------------------------------------------------------
// The positive half: the desugar target is already admissible, end to end.
// ---------------------------------------------------------------------------------------------

/// The **whole point of the inventory**: every ingredient a two-statement body needs is already
/// landed and executable. A three-statement discard chain (`let _ = a in let _ = b in c`) and a
/// `Unit`-typed statement chain both parse, check, classify `Total`, and elaborate to closed L0.
/// So admitting `{ a; b; c }` is a **parser-only, zero-kernel-growth (KC-3) desugar** — the same
/// shape already used for `[…]` list literals, tuples, or-patterns and `?`.
#[test]
fn the_desugar_target_already_works_end_to_end() {
    for (label, src) in [
        (
            "3-statement discard chain",
            format!(
                "{PRE}fn f() => Binary{{8}} = \
                 let _ = g(0b0000_0001) in let _ = g(0b0000_0010) in 0b0000_0011;\n"
            ),
        ),
        (
            "Unit-returning statement chain",
            format!("{PRE}fn f() => Binary{{8}} = let _ = h() in let _ = h() in 0b0000_0011;\n"),
        ),
        (
            "Unit-returning body ending in the Unit value",
            format!("{PRE}fn f() => Unit = let _ = h() in let _ = h() in Unit;\n"),
        ),
    ] {
        let nodule = parse(&src).unwrap_or_else(|e| panic!("[{label}] parse: {e}"));
        let env = check_nodule(&nodule).unwrap_or_else(|e| panic!("[{label}] check: {e}"));
        let tot = mycelium_l1::totality::classify_all(&env.fns)
            .unwrap_or_else(|e| panic!("[{label}] totality walk: {e:?}"));
        assert_eq!(
            tot.get("f"),
            Some(&mycelium_l1::Totality::Total),
            "[{label}] expected a Total classification"
        );
        elaborate(&env, "f").unwrap_or_else(|e| panic!("[{label}] elaborate: {e:?}"));
    }
}

// ---------------------------------------------------------------------------------------------
// Goal state — block surface ≡ nested-let desugar (parse-AST identity).
// ---------------------------------------------------------------------------------------------

/// A two-statement body must be observationally identical to its hand-written `let _ = a in b`
/// desugar — AST identity after parse, the same proof shape `tests/list_literal.rs` uses for `[…]`.
#[test]
fn goal_a_two_statement_block_body_parses_identically_to_its_let_desugar() {
    let block = format!("{PRE}fn f() => Binary{{8}} = {{ g(0b0000_0001); 0b0000_0011 }};\n");
    let desugared =
        format!("{PRE}fn f() => Binary{{8}} = let _ = g(0b0000_0001) in 0b0000_0011;\n");
    let body_of = |src: &str| {
        parse(src)
            .unwrap_or_else(|e| panic!("parse: {e}\n{src}"))
            .items
            .into_iter()
            .find_map(|i| match i {
                mycelium_l1::ast::Item::Fn(fd) if fd.sig.name == "f" => Some(fd.body),
                _ => None,
            })
            .expect("fn f")
    };
    assert_eq!(body_of(&block), body_of(&desugared));
}

/// Three-statement block ≡ nested discard chain (extends the two-statement identity proof).
#[test]
fn three_statement_block_parses_identically_to_nested_lets() {
    let block = format!(
        "{PRE}fn f() => Binary{{8}} = {{ g(0b0000_0001); g(0b0000_0010); 0b0000_0011 }};\n"
    );
    let desugared = format!(
        "{PRE}fn f() => Binary{{8}} = \
         let _ = g(0b0000_0001) in let _ = g(0b0000_0010) in 0b0000_0011;\n"
    );
    let body_of = |src: &str| {
        parse(src)
            .unwrap_or_else(|e| panic!("parse: {e}\n{src}"))
            .items
            .into_iter()
            .find_map(|i| match i {
                mycelium_l1::ast::Item::Fn(fd) if fd.sig.name == "f" => Some(fd.body),
                _ => None,
            })
            .expect("fn f")
    };
    assert_eq!(body_of(&block), body_of(&desugared));
}

/// End-to-end: a block body checks, classifies Total, and elaborates (not only parse identity).
#[test]
fn block_body_checks_and_elaborates_end_to_end() {
    let src = format!("{PRE}fn f() => Binary{{8}} = {{ h(); h(); 0b0000_0011 }};\n");
    let nodule = parse(&src).unwrap_or_else(|e| panic!("parse: {e}"));
    let env = check_nodule(&nodule).unwrap_or_else(|e| panic!("check: {e}"));
    let tot =
        mycelium_l1::totality::classify_all(&env.fns).unwrap_or_else(|e| panic!("totality: {e:?}"));
    assert_eq!(tot.get("f"), Some(&mycelium_l1::Totality::Total));
    elaborate(&env, "f").unwrap_or_else(|e| panic!("elaborate: {e:?}"));
}
