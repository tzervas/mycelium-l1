//! DN-129 §4 (M-1091; OQ-2 degrade path) — the `Fault` prelude trait, seeded as a **bare marker**
//! (`trait Fault[T] {}`, zero required methods — see `fault.rs`'s module doc for the honest
//! OQ-2/supertrait-bound degrade this records). Mirrors `tests/ord3.rs`'s structure (T-B1:
//! prelude-availability without a local declaration; the redeclare-refusal twin).

use crate::checkty::*;
use crate::parse;

fn env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("checks")
}

fn check_err(src: &str) -> CheckError {
    check_nodule(&parse(src).expect("parses")).expect_err("must fail to check")
}

/// `Fault` is available with **no** `trait Fault` declaration in source, and an **empty** impl
/// (the bare-marker shape — zero required methods) checks clean with zero new checker work.
#[test]
fn fault_prelude_trait_is_builtin_and_an_empty_instance_checks_with_no_local_declaration() {
    env("nodule d;\n\
         type MyError = Bad(Bytes);\n\
         impl Fault[MyError] for MyError {};");
}

/// A user cannot shadow the built-in `Fault` trait with their own declaration (never a silent
/// shadow of the prelude — G2, mirrors `redeclaring_the_builtin_ord3_trait_is_refused`).
#[test]
fn redeclaring_the_builtin_fault_trait_is_refused() {
    let err = check_err("nodule d;\ntrait Fault[T] {};");
    assert!(
        err.message.contains("Fault") && err.message.contains("built-in"),
        "expected a built-in-redeclaration refusal, got: {}",
        err.message
    );
}

/// A `Fault` impl that provides a method the (empty) trait never required is refused by the
/// ordinary impl-method-set-mismatch check — the bare marker shape gets no special leniency either
/// direction (never a silent partial match, G2).
#[test]
fn fault_instance_with_an_unexpected_method_is_refused() {
    let err = check_err(
        "nodule d;\n\
         type MyError = Bad(Bytes);\n\
         impl Fault[MyError] for MyError { fn extra(x: MyError) => Bytes = \"?\"; };",
    );
    assert!(
        err.message.contains("Fault"),
        "expected a Fault-related refusal, got: {}",
        err.message
    );
}

/// `Fault` is seeded independently of `Fuse`/`Ord3`/`Show`/`Init` (DN-129 §5): a program using only
/// `Fault` never pulls the others into its trait registry.
#[test]
fn fault_prelude_trait_is_independently_conditional() {
    let fault_only = env("nodule d;\n\
         type MyError = Bad(Bytes);\n\
         impl Fault[MyError] for MyError {};");
    assert!(fault_only.traits.contains_key("Fault"));
    for other in ["Fuse", "Ord3", "Show", "Init"] {
        assert!(
            !fault_only.traits.contains_key(other),
            "a Fault-only program must not also seed `{other}`"
        );
    }
}
