//! DN-129 §3 (M-1091) — the `Init` prelude trait. Mirrors `tests/ord3.rs`'s structure (T-B1:
//! prelude-availability without a local declaration; the redeclare-refusal twin), plus a case
//! specific to `Init`'s zero-value-param shape: the trait parameter can only be determined from the
//! call's **expected** (return) type, never from an argument (DN-129 §3 has none) — RFC-0019 §4.4's
//! "seed from expected" path (`checkty.rs` `check_trait_method_call`).

use crate::checkty::*;
use crate::parse;

fn env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("checks")
}

fn check_err(src: &str) -> CheckError {
    check_nodule(&parse(src).expect("parses")).expect_err("must fail to check")
}

/// `Init` is available with **no** `trait Init` declaration in source — mirrors
/// `ord3_prelude_trait_is_builtin_and_an_instance_checks_with_no_local_declaration` exactly. A
/// single-param, param-only-sig, **zero-value-param** impl (DN-129 §3's shape) checks clean with
/// zero new checker work; the call site's declared return type (`Counter`) determines the trait
/// parameter (RFC-0019 §4.4's "seed from expected" path — `init()` has no argument to unify from).
#[test]
fn init_prelude_trait_is_builtin_and_an_instance_checks_with_no_local_declaration() {
    env("nodule d;\n\
         type Counter = Mk(Binary{8});\n\
         impl Init[Counter] for Counter {\n\
           fn init() => Counter = Mk(0b00000000);\n\
         };\n\
         fn zero() => Counter = init();");
}

/// A user cannot shadow the built-in `Init` trait with their own declaration (never a silent
/// shadow of the prelude — G2, mirrors `redeclaring_the_builtin_ord3_trait_is_refused`).
#[test]
fn redeclaring_the_builtin_init_trait_is_refused() {
    let err = check_err("nodule d;\ntrait Init[T] { fn init() => T; };");
    assert!(
        err.message.contains("Init") && err.message.contains("built-in"),
        "expected a built-in-redeclaration refusal, got: {}",
        err.message
    );
}

/// A call to `init()` whose trait parameter cannot be determined from either an argument (there is
/// none) or the expected/ascribed result type is an explicit refusal — never a guessed default
/// (RFC-0007 §11.3 / G2). `let x = init() in True` gives `init()`'s own check no expected type at
/// all (an unascribed `let` binder passes `None` down — `checkty.rs`'s `let` handling), so even
/// though a `Counter: Init` instance exists, nothing pins the trait parameter. Isolates the
/// zero-value-param dispatch boundary `Init` is the first prelude trait to exercise.
#[test]
fn init_call_with_no_determining_context_is_refused_never_guessed() {
    let err = check_err(
        "nodule d;\n\
         type Counter = Mk(Binary{8});\n\
         impl Init[Counter] for Counter { fn init() => Counter = Mk(0b00000000); };\n\
         fn bad() => Bool = let x = init() in True;",
    );
    assert!(
        err.message.contains("does not determine"),
        "expected an undetermined-trait-parameter refusal, got: {}",
        err.message
    );
}

/// `Init` is seeded independently of `Fuse`/`Ord3`/`Show`/`Fault` (DN-129 §5): a program using only
/// `Init` never pulls the others into its trait registry.
#[test]
fn init_prelude_trait_is_independently_conditional() {
    let init_only = env("nodule d;\n\
         type Counter = Mk(Binary{8});\n\
         impl Init[Counter] for Counter { fn init() => Counter = Mk(0b00000000); };");
    assert!(init_only.traits.contains_key("Init"));
    for other in ["Fuse", "Ord3", "Show", "Fault"] {
        assert!(
            !init_only.traits.contains_key(other),
            "an Init-only program must not also seed `{other}`"
        );
    }
}
