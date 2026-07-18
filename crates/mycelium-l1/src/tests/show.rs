//! DN-127 (M-1090; WU-2) — the `Show` prelude trait. Mirrors `tests/ord3.rs`'s structure (T-B1:
//! prelude-availability without a local declaration; the redeclare-refusal twin).

use crate::checkty::*;
use crate::parse;

fn env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("checks")
}

fn check_err(src: &str) -> CheckError {
    check_nodule(&parse(src).expect("parses")).expect_err("must fail to check")
}

/// `Show` is available with **no** `trait Show` declaration in source — mirrors
/// `ord3_prelude_trait_is_builtin_and_an_instance_checks_with_no_local_declaration` exactly. A
/// single-param, param-only-sig impl (DN-127 §5's shape) checks clean with zero new checker work.
#[test]
fn show_prelude_trait_is_builtin_and_an_instance_checks_with_no_local_declaration() {
    env("nodule d;\n\
         type Flag = Off | On;\n\
         impl Show[Flag] for Flag {\n\
           fn render(x: Flag) => Bytes =\n\
             match x { Off => \"Off\", On => \"On\" };\n\
         };\n\
         fn describe(x: Flag) => Bytes = render(x);");
}

/// A user cannot shadow the built-in `Show` trait with their own declaration (never a silent
/// shadow of the prelude — G2, mirrors `redeclaring_the_builtin_ord3_trait_is_refused`).
#[test]
fn redeclaring_the_builtin_show_trait_is_refused() {
    let err = check_err("nodule d;\ntrait Show[T] { fn render(x: T) => Bytes; };");
    assert!(
        err.message.contains("Show") && err.message.contains("built-in"),
        "expected a built-in-redeclaration refusal, got: {}",
        err.message
    );
}

/// A `Show` instance whose signature does not match the prelude's `render(x: T) => Bytes` shape is
/// refused by the ordinary impl-method-set-mismatch check — `Show` gets no special leniency (never
/// a silent partial match, G2).
#[test]
fn show_instance_with_a_mismatched_method_set_is_refused() {
    let err = check_err(
        "nodule d;\n\
         type Flag = Off | On;\n\
         impl Show[Flag] for Flag { fn not_render(x: Flag) => Bytes = \"?\"; };",
    );
    assert!(
        err.message.contains("Show"),
        "expected a Show-related refusal, got: {}",
        err.message
    );
}

/// `Show` is seeded independently of `Fuse`/`Ord3`/`Init`/`Fault` (DN-129 §5): a program using only
/// `Show` never pulls the others into its trait registry.
#[test]
fn show_prelude_trait_is_independently_conditional() {
    let show_only = env("nodule d;\n\
         type Flag = Off | On;\n\
         impl Show[Flag] for Flag { fn render(x: Flag) => Bytes = \"Flag\"; };");
    assert!(show_only.traits.contains_key("Show"));
    for other in ["Fuse", "Ord3", "Init", "Fault"] {
        assert!(
            !show_only.traits.contains_key(other),
            "a Show-only program must not also seed `{other}`"
        );
    }
}
