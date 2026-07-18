//! DN-122 §13 (M-1080; WU-B) — the `Ord3` prelude trait. Mirrors `tests/fuse.rs`'s structure
//! exactly (T-B1: prelude-availability without a local declaration; the redeclare-refusal
//! twin), minus the law-checker cases (`Ord3` carries no algebraic law — see `ord3.rs`'s doc).
//!
//! **T-B2 scope note (VR-5, never-silent about what is and isn't covered here).** DN-122 §13.2
//! also specs a std-phylum-declared (general cross-phylum) foreign-trait-impl witness — out of
//! WU-B's scope by the task's own instruction ("std-phylum-declare is deferred to M-1076/WU-C —
//! do NOT build it"). The underlying substrate for THAT case (a single-param, param-only-sig
//! foreign trait resolving through a `use dep::nodule.Trait` import) is not new: it is the
//! already-landed M-1060 `register_instances` admit-path DN-122 §13.1 cites as `Empirical,
//! confirmed by register_instances + the MED-closure doc (checkty.rs:4335-4338)`, and the
//! `foreign_trait_sig_names_a_concrete_type` HOLE A/A2/B guard already has its own regression
//! coverage. Building a fresh multi-phylum fixture harness for a std-phylum-declared witness is
//! WU-C's job (it needs the actual std-phylum-declare surface to be meaningful); asserted here,
//! not built (never guessed past what this leaf actually shipped).

use crate::checkty::*;
use crate::parse;

fn env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("checks")
}

fn check_err(src: &str) -> CheckError {
    check_nodule(&parse(src).expect("parses")).expect_err("must fail to check")
}

/// T-B1: `Ord3` is available with **no** `trait Ord3` declaration in source — mirrors
/// `fuse_prelude_trait_is_builtin_and_a_lawful_instance_checks` exactly. A single-param,
/// param-only-sig impl (the DN-122 §13.1 MVP shape) checks clean with zero new checker work.
#[test]
fn ord3_prelude_trait_is_builtin_and_an_instance_checks_with_no_local_declaration() {
    env("nodule d;\n\
         type Ordering = Lt | Eq | Gt;\n\
         impl Ord3[Ordering] for Ordering {\n\
           fn cmp(a: Ordering, b: Ordering) => Binary{8} =\n\
             match a {\n\
               Lt => match b { Lt => 0b00000000, Eq => 0b00000000, Gt => 0b00000000 },\n\
               Eq => match b { Lt => 0b00000001, Eq => 0b00000001, Gt => 0b00000001 },\n\
               Gt => match b { Lt => 0b00000010, Eq => 0b00000010, Gt => 0b00000010 },\n\
             };\n\
         };\n\
         fn order(x: Ordering, y: Ordering) => Binary{8} = cmp(x, y);");
}

/// A user cannot shadow the built-in `Ord3` trait with their own declaration (never a silent
/// shadow of the prelude — G2, mirrors `redeclaring_the_builtin_fuse_trait_is_refused`).
#[test]
fn redeclaring_the_builtin_ord3_trait_is_refused() {
    let err = check_err("nodule d;\ntrait Ord3[T] { fn cmp(a: T, b: T) => Binary{8}; };");
    assert!(
        err.message.contains("Ord3") && err.message.contains("built-in"),
        "expected a built-in-redeclaration refusal, got: {}",
        err.message
    );
}

/// `Ord3` and `Fuse` are independently seeded (M-965 F-A1 / DN-122 §13 WU-B): a program using only
/// `Ord3` never pulls `Fuse` into its trait registry, and vice versa — the two prelude traits do
/// not leak into each other's programs (each conditional gate is scoped to its own `TRAIT_NAME`).
#[test]
fn ord3_and_fuse_prelude_traits_are_independently_conditional() {
    let ord3_only = env("nodule d;\n\
         type Flag = Off | On;\n\
         impl Ord3[Flag] for Flag { fn cmp(a: Flag, b: Flag) => Binary{8} = 0b00000000; };");
    assert!(ord3_only.traits.contains_key("Ord3"));
    assert!(
        !ord3_only.traits.contains_key("Fuse"),
        "an Ord3-only program must not also seed Fuse"
    );

    let fuse_only = env("nodule d;\n\
         type Flag = Off | On;\n\
         impl Fuse[Flag] for Flag {\n\
           fn join(a: Flag, b: Flag) => Flag =\n\
             match a { Off => b, On => On };\n\
         };");
    assert!(fuse_only.traits.contains_key("Fuse"));
    assert!(
        !fuse_only.traits.contains_key("Ord3"),
        "a Fuse-only program must not also seed Ord3"
    );
}

/// A `Ord3` instance whose signature does not match the prelude's `cmp(a: T, b: T) => Binary{8}`
/// shape is refused by the ordinary impl-method-set-mismatch check — `Ord3` gets no special
/// leniency (never a silent partial match, G2).
#[test]
fn ord3_instance_with_a_mismatched_method_set_is_refused() {
    let err = check_err(
        "nodule d;\n\
         type Flag = Off | On;\n\
         impl Ord3[Flag] for Flag { fn not_cmp(a: Flag, b: Flag) => Binary{8} = 0b00000000; };",
    );
    // Exact wording is the ordinary impl-method-set-mismatch diagnostic; just confirm it is
    // refused (never a silent accept of the wrong method set) and names the trait.
    assert!(
        err.message.contains("Ord3"),
        "expected an Ord3-related refusal, got: {}",
        err.message
    );
}
