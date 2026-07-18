//! In-crate white-box tests for the RFC-0034 §10/§10.1 (CU-5) `wrapping { <expr> }` surface — the
//! named, explicit Axis-B modular-arithmetic opt-out. Exercises the four surface layers end-to-end
//! (lexer/parser → checker → the L1 tree-walking evaluator) plus the never-silent refusals.
//!
//! Data-driven (test-layout rule): each test asserts over a case table, not bespoke per-case logic.
//! The central eval assertion compares a `wrapping { … }` block's result **byte-for-byte against the
//! landed runtime half** [`mycelium_interp::prims::eval_wrapping`] applied to the same operand values
//! — an encoding-agnostic witness that the surface actually reaches that path (not a hand-rolled
//! expected bit vector).

use crate::ast::{Expr, Item};
use crate::checkty::check_nodule;
use crate::eval::{Evaluator, L1Error, L1Value};
use crate::parse::parse;
use mycelium_core::GuaranteeStrength;

/// Wrap `body` as the single `main` of a `Binary{8}`-returning nodule (the common shape under test).
fn prog(body: &str) -> String {
    format!("nodule d;\nfn main() => Binary{{8}} = {body};")
}

/// Parse + check + evaluate `main`, surfacing the evaluator's `Result` (for the refusal cases).
fn try_run(src: &str) -> Result<L1Value, L1Error> {
    let env = check_nodule(&parse(src).expect("parses")).expect("checks");
    Evaluator::new(&env).call("main", vec![])
}

/// Parse + check + evaluate `main`, expecting success.
fn run(src: &str) -> L1Value {
    try_run(src).expect("evaluates")
}

/// Whether `src` type-checks (parse must already succeed — these are checker-level cases).
fn checks(src: &str) -> bool {
    check_nodule(&parse(src).expect("parses")).is_ok()
}

/// The first `fn` item's body expression, for AST-shape assertions.
fn fn_body(src: &str) -> Expr {
    parse(src)
        .expect("parses")
        .items
        .into_iter()
        .find_map(|i| match i {
            Item::Fn(fd) => Some(fd.body),
            _ => None,
        })
        .expect("a fn item")
}

#[test]
fn wrapping_block_parses_to_the_wrapping_node() {
    // The surface `wrapping { … }` reaches the parser as `Expr::Wrapping` (not a bare identifier —
    // `wrapping` is a reserved keyword, G2).
    assert!(
        matches!(
            fn_body(&prog("wrapping { add_s(0b0000_0001, 0b0000_0001) }")),
            Expr::Wrapping(_)
        ),
        "`wrapping {{ … }}` must parse to Expr::Wrapping",
    );
}

#[test]
fn wrapping_dispatches_the_enclosed_op_through_eval_wrapping() {
    // (surface op, kernel prim, a, b) — each pair OVERFLOWS Binary{8}: the non-wrapping op refuses,
    // and `wrapping { op(a, b) }` yields the modular result the landed `eval_wrapping` computes.
    const CASES: &[(&str, &str, &str, &str)] = &[
        ("add_s", "bin.add", "0b0111_1111", "0b0000_0001"), // 127 + 1  -> -128
        ("sub_s", "bin.sub", "0b1000_0000", "0b0000_0001"), // -128 - 1 ->  127
        ("mul_s", "bin.mul", "0b0001_0000", "0b0001_0000"), // 16 * 16  ->    0
    ];
    for (op, kernel, a, b) in CASES {
        let block = run(&prog(&format!("wrapping {{ {op}({a}, {b}) }}")));
        let av = run(&prog(a));
        let bv = run(&prog(b));
        let reference = mycelium_interp::prims::eval_wrapping(
            kernel,
            &[av.as_repr().expect("repr"), bv.as_repr().expect("repr")],
        )
        .expect("eval_wrapping never refuses on range");
        let rv = block.as_repr().expect("the block result is a repr value");

        // The block's payload IS the modular `eval_wrapping` result (reaches the landed path).
        assert_eq!(
            rv.payload(),
            reference.payload(),
            "{op}: `wrapping` block must equal eval_wrapping({kernel}, …)",
        );
        // Honesty: the opt-out is `Declared` and carries the inspectable `WrappingOpt` marker (VR-5).
        assert_eq!(
            rv.meta().guarantee(),
            GuaranteeStrength::Declared,
            "{op}: the wrapping result is Declared",
        );
        assert!(
            rv.meta().wrapping_opt().is_some(),
            "{op}: the WrappingOpt marker is attached (RFC-0034 §10; M-791)",
        );
        // The opt-out is doing real work: the *non-wrapping* op refuses the same overflow (G2).
        assert!(
            try_run(&prog(&format!("{op}({a}, {b})"))).is_err(),
            "{op}: the non-wrapping op refuses the overflow (never-silent)",
        );
    }
}

#[test]
fn wrapping_only_opts_out_of_the_range_refusal_not_the_arithmetic() {
    // In range (3 + 4 = 7): `wrapping` agrees with the non-wrapping op on the value, differing only
    // in the guarantee tag (Declared vs the non-wrapping Exact) — it relaxes the *range* refusal only.
    let block = run(&prog("wrapping { add_s(0b0000_0011, 0b0000_0100) }"));
    let plain = run(&prog("add_s(0b0000_0011, 0b0000_0100)"));
    assert_eq!(
        block.as_repr().expect("repr").payload(),
        plain.as_repr().expect("repr").payload(),
        "in-range: the wrapping value equals the non-wrapping value",
    );
    assert_eq!(
        block.as_repr().expect("repr").meta().guarantee(),
        GuaranteeStrength::Declared,
        "the wrapping result is still Declared, in range too",
    );
}

#[test]
fn wrapping_covers_a_nested_arithmetic_tree() {
    // The region is the whole lexical tree: `mul_s(16, 16)` wraps to 0, then `add_s(1, 0)` = 1 — every
    // enclosed op runs in wrapping mode. The result equals the literal 1, tagged Declared + WrappingOpt.
    let nested = run(&prog(
        "wrapping { add_s(0b0000_0001, mul_s(0b0001_0000, 0b0001_0000)) }",
    ));
    let one = run(&prog("0b0000_0001"));
    let rv = nested.as_repr().expect("repr");
    assert_eq!(
        rv.payload(),
        one.as_repr().expect("repr").payload(),
        "16*16 wraps to 0, then 1+0 = 1",
    );
    assert_eq!(rv.meta().guarantee(), GuaranteeStrength::Declared);
    assert!(rv.meta().wrapping_opt().is_some());
}

#[test]
fn wrapping_accepts_a_binary_add_sub_mul_tree() {
    // Positive check cases: the three eval_wrapping-eligible ops (surface `add_s`/`sub_s`/`mul_s`) and
    // a nested tree all type-check inside `wrapping { … }`.
    const ACCEPTS: &[&str] = &[
        "wrapping { add_s(0b0111_1111, 0b0000_0001) }",
        "wrapping { sub_s(0b1000_0000, 0b0000_0001) }",
        "wrapping { mul_s(0b0001_0000, 0b0001_0000) }",
        "wrapping { add_s(0b0000_0001, mul_s(0b0000_0010, 0b0000_0011)) }",
    ];
    for body in ACCEPTS {
        assert!(checks(&prog(body)), "must type-check: {body}");
    }
}

#[test]
fn wrapping_refuses_unsupported_enclosed_forms_never_silently() {
    // Each body is gate-isolated: it would type-check WITHOUT the wrapping gate (correct width/return
    // type / operand paradigm), so the refusal is `check_wrapping`/`gate_wrapping_body`'s doing — the
    // never-silent floor (G2). `eval_wrapping` supports exactly bin.add/bin.sub/bin.mul over equal-
    // width Binary operands; everything else refuses up front.
    const REJECTS: &[(&str, &str)] = &[
        // A different op the kernel *has* (bin.div is width-preserving Binary{8}->Binary{8}), so only
        // the gate stops it.
        (
            "division inside a wrapping region",
            "wrapping { div_u(0b0000_1000, 0b0000_0010) }",
        ),
        // A non-arithmetic body form (a `let`) — a modular *arithmetic* region, not a general scope.
        ("a `let` body", "wrapping { let x = 0b0000_0001 in x }"),
        // Structural: unequal operand widths (the normal-typing width check, surfaced through the
        // wrapping construct).
        (
            "unequal operand widths",
            "wrapping { add_s(0b0111_1111, 0b0001) }",
        ),
        // A non-Binary (ternary) operand — the prim's operand contract still binds.
        ("a non-Binary operand", "wrapping { add_s(0t+, 0t0) }"),
    ];
    for (label, body) in REJECTS {
        assert!(
            !checks(&prog(body)),
            "`wrapping` must refuse {label}: {body}"
        );
    }
}

#[test]
fn wrapping_refuses_a_function_call_inside_the_region() {
    // A call inside `wrapping { … }` is refused up front (G2): were it allowed, the dynamic wrapping
    // bracket could leak modular semantics into the callee (the opt-out must never be ambient). Without
    // the gate `add_s(id(x), y)` type-checks (`id` returns Binary{8}), so the gate is the sole refuser.
    let src = "nodule d;\n\
               fn id(x: Binary{8}) => Binary{8} = x;\n\
               fn main() => Binary{8} = wrapping { add_s(id(0b0000_0001), 0b0000_0001) };";
    assert!(
        !checks(src),
        "a function call inside a wrapping region must be refused (never ambient — G2)",
    );
}
