//! **Statement-sequencing surface inventory** — the measured refusal boundary for multi-statement
//! `fn` bodies and the `()` unit spelling (the dominant expressibility gap: `MultiStmtBody` = 38 of
//! 196 recorded gaps in `mycelium-transpile/docs/vet-gha-runner-ctl-2026-07-22/summary.json`, plus
//! 13 `Other` gaps whose reason is "no unit value is representable in this grammar").
//!
//! **What this file establishes, by execution rather than by reading the code:**
//!
//! 1. The **semantic target already exists**. `let _ = a in b` — the standard sequencing desugar —
//!    parses, type-checks, classifies `Total`, and elaborates to an L0 `Node::Let`. The DN-137
//!    `Unit` prelude type (`checkty::unit_prelude`, seeded never parsed) type-checks and elaborates
//!    to `Node::Construct { args: [] }`. Nothing in the IR is missing.
//! 2. The gap is **purely surface syntax**: there is no `{ s1; s2 }` block form and no `()`
//!    spelling, so every refusal below is a `ParseError` from one of exactly four sites in
//!    `src/parse.rs` — *not* a typed `ElabError::Residual` / `CheckError`.
//!
//! Tests 1–5 are **characterization** tests: they pin the exact refusal site + message so a future
//! surface landing has a precise before/after witness. Test 6 is the **goal state**, `#[ignore]`d so
//! the suite stays green; run it with `cargo test --test multi_statement_body -- --ignored` to see
//! the refusal reproduce.
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
// 1..5 — the four refusal sites, characterized.
// ---------------------------------------------------------------------------------------------

/// **Refusal site A** — `src/parse.rs::Parser::parse_item` fallthrough (`"a top-level item …"`).
/// A Rust-shaped `fn f() => T = stmt1; stmt2;` body ends at the first `;` (DN-57 makes `;` the
/// *component terminator*, never a statement separator), so the second statement is read as a new
/// top-level item and refused there. The diagnostic never mentions statements.
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

/// **Refusal site B** — `src/parse.rs::Parser::parse_primary`'s `_ => self.err("an expression")`
/// arm (parse.rs:2459 at this revision). `{` is not an expression-opening token: there is **no
/// block form** in the expression grammar at all, so even a *single*-expression block `{ e }` is a
/// parse error. `docs/spec/grammar/mycelium.ebnf` confirms it: `block ::= '{' expr '}'` exists only
/// as the operand of `reclaim_expr`, and `expr` has no `block` alternative.
#[test]
fn a_braced_block_is_not_an_expression_form_at_all() {
    let two = parse_err(&format!(
        "{PRE}fn f() => Binary{{8}} = {{ g(0b0000_0010); g(0b0000_0001) }};\n"
    ));
    assert!(
        two.contains("expected an expression") && two.contains("found LBrace"),
        "unexpected refusal: {two}"
    );
    // …and the single-expression block is refused identically — the gap is the *block*, not the `;`.
    let one = parse_err(&format!(
        "{PRE}fn f() => Binary{{8}} = {{ 0b0000_0001 }};\n"
    ));
    assert!(
        one.contains("expected an expression") && one.contains("found LBrace"),
        "unexpected refusal: {one}"
    );
}

/// **Refusal site C** — `src/parse.rs::Parser::parse_let`'s `expect(&Tok::In, …)`. `let` is an
/// *expression* (`let … in …`), never a statement; the Rust-shaped `let y = e;` has no continuation
/// to bind, so it is refused at the missing `in`.
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

/// **Refusal site D(expr)** — `parse_primary`'s `Tok::LParen` arm reaches `parse_expr` on the
/// immediately-following `)`. `()` has no expression spelling, even though the `Unit` *value*
/// exists (see [`the_desugar_target_already_works_end_to_end`]). The arm carries the standing FLAG:
/// "unit `()` and 1-tuples are deferred surface decisions" (M-826).
#[test]
fn unit_has_no_expression_spelling() {
    let msg = parse_err(&format!("{PRE}fn f() => Unit = ();\n"));
    assert!(
        msg.contains("expected an expression") && msg.contains("found RParen"),
        "unexpected refusal: {msg}"
    );
}

/// **Refusal site D(type)** — `src/parse.rs::Parser::parse_base_type`'s `Tok::LParen` arm reaches
/// `parse_type_ref` on the immediately-following `)` and falls through to `_ => self.err("a type")`
/// (parse.rs:1734 at this revision). `() ` has no *type* spelling either, which is exactly the
/// transpiler's 13 "function has no return type (implicit `()`) — no unit value is representable in
/// this grammar" gaps.
#[test]
fn unit_has_no_type_spelling() {
    let msg = parse_err(&format!("{PRE}fn f() => () = 0b0000_0001;\n"));
    assert!(
        msg.contains("expected a type") && msg.contains("found RParen"),
        "unexpected refusal: {msg}"
    );
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
// The goal state — currently FAILS. Ignored so the suite stays green.
// ---------------------------------------------------------------------------------------------

/// **GOAL (currently refused).** The smallest program that needs statement sequencing: a two-
/// statement body. It must become observationally identical to its hand-written `let _ = a in b`
/// desugar — AST identity after parse, the same proof shape `tests/list_literal.rs` uses for `[…]`.
///
/// Run with `cargo test --test multi_statement_body -- --ignored`.
#[test]
#[ignore = "GOAL: `{ a; b }` block sequencing is not in the surface grammar yet — see this \
            file's module doc for the measured refusal sites"]
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
