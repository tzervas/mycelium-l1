//! The **`?` try-operator differential** (DN-102 / M-1025 ENB-2). The Definition of Done is that
//! `let x = e? in body` behaves **identically** to the hand-written `match e { Ok(x) => body,
//! Err(f) => Err(f) }` (resp. the `Option` analog) — the desugar introduces no new observable, it is
//! pure surface + lowering over the existing `Result`/`Option` `match` bind (KC-3, no new L0 node).
//!
//! Each witness pairs a `?`-using function against its explicit-`match` twin and asserts they agree
//! on **both** the success and the propagation path, on **both** `Result` and `Option`, across the
//! evaluation paths (L1-eval, and — where the fragment closes — elaborate→L0-interp). It also pins
//! the never-silent **rejects** (a `?` outside a `let`-binder RHS, a repeated `e??`, an ascribed
//! try-let, and a `?` on a non-`Result`/`Option` operand — DN-102 §3/§5). Data-driven: each case is a
//! `(label, q_fn, m_fn)` row, so a body is `assert two callables agree`, not bespoke logic.

use mycelium_interp::Interpreter;
use mycelium_l1::elab::build_registry;
use mycelium_l1::{check_nodule, elaborate, monomorphize, parse, Evaluator};

/// A single-nodule program that defines local `Result`/`Option` mirrors (the M-925 single-nodule
/// harness — matching `lib/std/{result,option,error}.myc`'s self-containment), a `?`-using entry
/// `q`, its explicit-`match` twin `m`, and the two nullary drivers `main_q`/`main_m` the differential
/// evaluates. The two drivers must produce byte-identical L0 values.
struct Case {
    label: &'static str,
    src: String,
}

const PRELUDE: &str = "nodule d;\n\
    type Result[A, E] = Ok(A) | Err(E);\n\
    type Option[A] = Some(A) | None;\n";

/// The L1 evaluator result of a nullary `entry` (the trusted big-step base). `L1Value: PartialEq`, so
/// two results compare structurally (constructor identity + fields), discriminating Ok/Err/Some/None.
fn l1(env: &mycelium_l1::Env, entry: &str) -> mycelium_l1::L1Value {
    Evaluator::new(env)
        .call(entry, vec![])
        .unwrap_or_else(|e| panic!("L1-eval `{entry}` failed: {e}"))
}

/// The `?`-driver and the `match`-driver must agree. Two witnesses:
/// 1. **Primary (behavioral):** their **L1-eval** results are identical — the `?` desugar introduces
///    no new observable on either the success or the propagation path.
/// 2. **Second (three-way L0):** the `?`-driver **monomorphized → elaborated → L0-interp** agrees
///    with its own L1-eval `to_core` projection — pinning that the checker's `Try`→`match` rewrite is
///    what elaboration consumes (a `Try` never survives into elab; DN-102 §4), and that the lowered
///    `match` runs identically on the reference interpreter. Monomorphization registers the concrete
///    `Result[Binary{8}, …]`/`Option[Binary{8}]` instance so the L0 projection is defined.
fn assert_q_equiv_match(case: &Case) {
    let env = check_nodule(&parse(&case.src).expect("parses")).expect("checks");
    // 1. Primary: `?` ≡ hand-`match` on the L1 evaluator (both Ok/Err/Some/None paths).
    assert_eq!(
        l1(&env, "main_q"),
        l1(&env, "main_m"),
        "[{}] `?` and the hand-`match` desugar diverged on L1-eval",
        case.label
    );
    // 2. Three-way L0 leg for the `?`-driver (monomorphized so the concrete instance is registered).
    let menv = monomorphize(&env, "main_q")
        .unwrap_or_else(|e| panic!("[{}] `?` program monomorphizes: {e:?}", case.label));
    let reg = build_registry(&menv).expect("registry builds");
    let l1_core = l1(&menv, "main_q")
        .to_core(&menv, &reg)
        .unwrap_or_else(|| panic!("[{}] the `?` result has no L0 projection", case.label));
    let node = elaborate(&menv, "main_q")
        .unwrap_or_else(|e| panic!("[{}] `?` program elaborates: {e:?}", case.label));
    let l0 = Interpreter::default()
        .eval_core(&node)
        .unwrap_or_else(|e| panic!("[{}] L0-interp runs: {e:?}", case.label));
    assert_eq!(
        l1_core, l0,
        "[{}] L1-eval and elaborate→L0-interp diverged on the desugared `?`",
        case.label
    );
}

fn cases() -> Vec<Case> {
    vec![
        // ---- Result, success (Ok) path: `let x = r? in Ok(x)` ≡ `match r {Ok(x)=>Ok(x),Err(e)=>Err(e)}`.
        Case {
            label: "result-ok",
            src: format!(
                "{PRELUDE}\
                 fn q(r: Result[Binary{{8}}, Binary{{8}}]) => Result[Binary{{8}}, Binary{{8}}] = let x = r? in Ok(x);\n\
                 fn m(r: Result[Binary{{8}}, Binary{{8}}]) => Result[Binary{{8}}, Binary{{8}}] = match r {{ Ok(x) => Ok(x), Err(e) => Err(e) }};\n\
                 fn main_q() => Result[Binary{{8}}, Binary{{8}}] = q(Ok(0b0000_0101));\n\
                 fn main_m() => Result[Binary{{8}}, Binary{{8}}] = m(Ok(0b0000_0101));\n"
            ),
        },
        // ---- Result, propagation (Err) path: the `?` short-circuits with the same Err value.
        Case {
            label: "result-err",
            src: format!(
                "{PRELUDE}\
                 fn q(r: Result[Binary{{8}}, Binary{{8}}]) => Result[Binary{{8}}, Binary{{8}}] = let x = r? in Ok(x);\n\
                 fn m(r: Result[Binary{{8}}, Binary{{8}}]) => Result[Binary{{8}}, Binary{{8}}] = match r {{ Ok(x) => Ok(x), Err(e) => Err(e) }};\n\
                 fn main_q() => Result[Binary{{8}}, Binary{{8}}] = q(Err(0b1111_0000));\n\
                 fn main_m() => Result[Binary{{8}}, Binary{{8}}] = m(Err(0b1111_0000));\n"
            ),
        },
        // ---- Result, chained `?` (two propagating binds) — the continuation shape ports carry.
        Case {
            label: "result-chain-ok",
            src: format!(
                "{PRELUDE}\
                 fn q(r: Result[Binary{{8}}, Binary{{8}}], s: Result[Binary{{8}}, Binary{{8}}]) => Result[Binary{{8}}, Binary{{8}}] = let x = r? in let y = s? in Ok(xor(x, y));\n\
                 fn m(r: Result[Binary{{8}}, Binary{{8}}], s: Result[Binary{{8}}, Binary{{8}}]) => Result[Binary{{8}}, Binary{{8}}] = match r {{ Ok(x) => match s {{ Ok(y) => Ok(xor(x, y)), Err(e) => Err(e) }}, Err(e) => Err(e) }};\n\
                 fn main_q() => Result[Binary{{8}}, Binary{{8}}] = q(Ok(0b0000_1111), Ok(0b0101_0101));\n\
                 fn main_m() => Result[Binary{{8}}, Binary{{8}}] = m(Ok(0b0000_1111), Ok(0b0101_0101));\n"
            ),
        },
        // ---- Result, chained `?`, second step propagates Err (short-circuit past the first bind).
        Case {
            label: "result-chain-err2",
            src: format!(
                "{PRELUDE}\
                 fn q(r: Result[Binary{{8}}, Binary{{8}}], s: Result[Binary{{8}}, Binary{{8}}]) => Result[Binary{{8}}, Binary{{8}}] = let x = r? in let y = s? in Ok(xor(x, y));\n\
                 fn m(r: Result[Binary{{8}}, Binary{{8}}], s: Result[Binary{{8}}, Binary{{8}}]) => Result[Binary{{8}}, Binary{{8}}] = match r {{ Ok(x) => match s {{ Ok(y) => Ok(xor(x, y)), Err(e) => Err(e) }}, Err(e) => Err(e) }};\n\
                 fn main_q() => Result[Binary{{8}}, Binary{{8}}] = q(Ok(0b0000_1111), Err(0b1010_1010));\n\
                 fn main_m() => Result[Binary{{8}}, Binary{{8}}] = m(Ok(0b0000_1111), Err(0b1010_1010));\n"
            ),
        },
        // ---- Option, present (Some) path: `let x = o? in Some(x)` ≡ `match o {Some(x)=>Some(x),None=>None}`.
        Case {
            label: "option-some",
            src: format!(
                "{PRELUDE}\
                 fn q(o: Option[Binary{{8}}]) => Option[Binary{{8}}] = let x = o? in Some(x);\n\
                 fn m(o: Option[Binary{{8}}]) => Option[Binary{{8}}] = match o {{ Some(x) => Some(x), None => None }};\n\
                 fn main_q() => Option[Binary{{8}}] = q(Some(0b0011_0011));\n\
                 fn main_m() => Option[Binary{{8}}] = m(Some(0b0011_0011));\n"
            ),
        },
        // ---- Option, absent (None) path: the `?` short-circuits with None.
        Case {
            label: "option-none",
            src: format!(
                "{PRELUDE}\
                 fn q(o: Option[Binary{{8}}]) => Option[Binary{{8}}] = let x = o? in Some(x);\n\
                 fn m(o: Option[Binary{{8}}]) => Option[Binary{{8}}] = match o {{ Some(x) => Some(x), None => None }};\n\
                 fn main_q() => Option[Binary{{8}}] = q(None);\n\
                 fn main_m() => Option[Binary{{8}}] = m(None);\n"
            ),
        },
        // ---- Option, chained `?` (two propagating binds) — parity with the Result-chain cases.
        Case {
            label: "option-chain-some",
            src: format!(
                "{PRELUDE}\
                 fn q(o: Option[Binary{{8}}], p: Option[Binary{{8}}]) => Option[Binary{{8}}] = let x = o? in let y = p? in Some(xor(x, y));\n\
                 fn m(o: Option[Binary{{8}}], p: Option[Binary{{8}}]) => Option[Binary{{8}}] = match o {{ Some(x) => match p {{ Some(y) => Some(xor(x, y)), None => None }}, None => None }};\n\
                 fn main_q() => Option[Binary{{8}}] = q(Some(0b0000_1111), Some(0b0101_0101));\n\
                 fn main_m() => Option[Binary{{8}}] = m(Some(0b0000_1111), Some(0b0101_0101));\n"
            ),
        },
        // ---- Option, chained `?`, second step propagates None (short-circuit past the first bind).
        Case {
            label: "option-chain-none2",
            src: format!(
                "{PRELUDE}\
                 fn q(o: Option[Binary{{8}}], p: Option[Binary{{8}}]) => Option[Binary{{8}}] = let x = o? in let y = p? in Some(xor(x, y));\n\
                 fn m(o: Option[Binary{{8}}], p: Option[Binary{{8}}]) => Option[Binary{{8}}] = match o {{ Some(x) => match p {{ Some(y) => Some(xor(x, y)), None => None }}, None => None }};\n\
                 fn main_q() => Option[Binary{{8}}] = q(Some(0b0000_1111), None);\n\
                 fn main_m() => Option[Binary{{8}}] = m(Some(0b0000_1111), None);\n"
            ),
        },
    ]
}

#[test]
fn try_operator_is_identical_to_the_hand_match_desugar() {
    for case in cases() {
        assert_q_equiv_match(&case);
    }
}

// ---- Never-silent rejects (DN-102 §3/§5) — a `?` outside its supported shape is a `CheckError`,
// never a silent mis-desugar (G2). Data-driven: each row is `(label, src)` that must FAIL to check.

fn reject(src: &str) -> String {
    let nodule = parse(src)
        .expect("the reject cases are syntactically valid — the refusal is at check time");
    match check_nodule(&nodule) {
        Ok(_) => panic!("expected a never-silent CheckError, but it checked: {src}"),
        Err(e) => e.to_string(),
    }
}

#[test]
fn a_question_outside_a_let_binder_rhs_is_refused() {
    // A `?` in a call argument (a non-`let` position) needs the deferred CPS lift (FLAG-try-1).
    let msg = reject(
        "nodule d;\n\
         type Result[A, E] = Ok(A) | Err(E);\n\
         fn id(x: Binary{8}) => Result[Binary{8}, Binary{8}] = Ok(x);\n\
         fn f(r: Result[Binary{8}, Binary{8}]) => Result[Binary{8}, Binary{8}] = id(r?);\n",
    );
    assert!(
        msg.contains("try-operator") || msg.contains("let`-binder") || msg.contains("let-binder"),
        "the refusal must name the `let`-binder-RHS restriction, got: {msg}"
    );
}

#[test]
fn a_repeated_question_is_refused() {
    // `e??` — the inner `?`'s operand is itself a `Try`, so the inner `?` is in a non-`let` position.
    let msg = reject(
        "nodule d;\n\
         type Result[A, E] = Ok(A) | Err(E);\n\
         fn f(r: Result[Result[Binary{8}, Binary{8}], Binary{8}]) => Result[Binary{8}, Binary{8}] = let x = r?? in Ok(x);\n",
    );
    assert!(
        !msg.is_empty(),
        "a repeated `??` must be refused, got an empty message"
    );
}

#[test]
fn an_ascribed_try_let_is_refused() {
    // `let x: T = e? in body` — the ascription is never silently dropped (DN-102 §5).
    let msg = reject(
        "nodule d;\n\
         type Result[A, E] = Ok(A) | Err(E);\n\
         fn f(r: Result[Binary{8}, Binary{8}]) => Result[Binary{8}, Binary{8}] = let x: Binary{8} = r? in Ok(x);\n",
    );
    assert!(
        msg.contains("ascription") || msg.contains("`?`-binder"),
        "the refusal must name the ascription restriction, got: {msg}"
    );
}

#[test]
fn a_question_on_a_non_result_option_operand_is_refused() {
    // `?` on a plain `Binary{8}` has no error/absence channel to propagate (DN-102 §3).
    let msg = reject(
        "nodule d;\n\
         type Result[A, E] = Ok(A) | Err(E);\n\
         fn f(b: Binary{8}) => Result[Binary{8}, Binary{8}] = let x = b? in Ok(x);\n",
    );
    assert!(
        msg.contains("Result") && msg.contains("Option"),
        "the refusal must say the operand needs a Result/Option type, got: {msg}"
    );
}

#[test]
fn a_bare_tail_question_outside_a_let_is_refused() {
    // A tail `e?` (the whole function body is a `?`, no enclosing `let`-binder) is a non-`let`
    // position — refused never-silently, distinct from the call-argument position already covered.
    let msg = reject(
        "nodule d;\n\
         type Result[A, E] = Ok(A) | Err(E);\n\
         fn f(r: Result[Binary{8}, Binary{8}]) => Result[Binary{8}, Binary{8}] = r?;\n",
    );
    assert!(
        msg.contains("try-operator") || msg.contains("let`-binder") || msg.contains("let-binder"),
        "the tail-`?` refusal must name the `let`-binder-RHS restriction, got: {msg}"
    );
}

// ---- Regression (PR #1363 review, HIGH): the type-peek in `check_try_let` must not double-invoke
// the affine/linear tracker. An operand whose evaluation consumes an affine `Substrate` must be
// marked used EXACTLY once — before the fix the peek + `check_match` re-check counted the consume
// twice and rejected this well-typed program with a spurious `double-consume` (a false rejection on
// the dominant `let x = f(s)? in …` port shape). This is a check-time property, so a check-only
// witness suffices (the `Substrate` value has no L1/L0 literal to differential-evaluate).

#[test]
fn a_question_on_an_affine_substrate_operand_checks_exactly_once() {
    let src = "nodule d;\n\
        type Result[A, E] = Ok(A) | Err(E);\n\
        fn f(s: Substrate{Sock}) => Result[Substrate{Sock}, Binary{8}] = Ok(consume s);\n\
        fn g(s: Substrate{Sock}) => Result[Substrate{Sock}, Binary{8}] = let x = f(s)? in Ok(x);\n";
    let nodule = parse(src).expect("the affine `?` program parses");
    check_nodule(&nodule)
        .expect("an affine `?`-operand is consumed once, not double-counted by the type peek");
}
