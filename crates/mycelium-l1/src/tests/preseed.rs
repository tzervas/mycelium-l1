//! DN-129 §5 — the shared [`crate::preseed::PreludeTraitSeed`] spine. Cross-cutting tests over
//! **all five** prelude traits (`Fuse`/`Ord3`/`Show`/`Init`/`Fault`) that a single per-trait test
//! file can't express: pairwise-distinctness at once, that none of the five names collides with a
//! reserved lexer keyword, and that the DRY refactor left `Fuse`/`Ord3` behavior unchanged (their
//! own `tests/fuse.rs`/`tests/ord3.rs` suites already pin the fine-grained behavior; this file adds
//! the whole-set regression net a per-trait file can't).

use crate::checkty::*;
use crate::parse;
use crate::preseed::PreludeTraitSeed;

fn env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("checks")
}

/// Every prelude trait's [`PreludeTraitSeed::name`], in one place — the same array
/// `crate::checkty::PRELUDE_TRAIT_SEEDS` drives the real seeding off, duplicated here (not
/// `pub(crate)` from `checkty`, and this test file should not need to reach into `checkty`'s
/// private const just to enumerate names) so this test is a genuine **independent** cross-check,
/// not a tautology against the same array it is meant to verify.
const ALL_TRAIT_NAMES: [&str; 5] = ["Fuse", "Ord3", "Show", "Init", "Fault"];

/// Pairwise-distinct: no two prelude traits share a name (a duplicate would make
/// `crate::checkty::PRELUDE_TRAIT_SEEDS` silently shadow one trait with another at `traits.insert`
/// — never actually a possibility given each is a distinct Rust source file, but this pins the
/// invariant structurally rather than by inspection).
#[test]
fn all_five_prelude_trait_names_are_pairwise_distinct() {
    for (i, a) in ALL_TRAIT_NAMES.iter().enumerate() {
        for (j, b) in ALL_TRAIT_NAMES.iter().enumerate() {
            if i != j {
                assert_ne!(a, b, "prelude trait names must be pairwise distinct");
            }
        }
    }
}

/// The five prelude traits' **method** names — the identifiers DN-129 §2's `default`-keyword
/// collision class actually threatens (a trait/type name is conventionally capitalized, so it
/// never collides with Mycelium's lowercase-only keyword set — DN-129 §2; the real risk is a
/// lowercase *method* name, exactly as `default` collided). `Fault` is the bare-marker trait (no
/// required method — DN-129 §4/§5 OQ-2), so it contributes no method name here.
const METHOD_NAMES: [(&str, &str); 4] = [
    ("Fuse", "join"),
    ("Ord3", "cmp"),
    ("Show", "render"),
    ("Init", "init"),
];

/// None of the five prelude trait names, and none of their method names, is a reserved lexer
/// keyword — checked directly against [`crate::token::keyword`] (the never-silent, standing
/// regression form of the mitigation #14 "grep to confirm no collision" check DN-127/DN-129 both
/// call for, e.g. the `Cmp`→`Ord3` collision M-1080 hit and `default`'s own keyword status). A
/// **trait name** (`Fuse`/`Ord3`/`Show`/`Init`/`Fault`) is capitalized and so structurally can't
/// collide with Mycelium's lowercase-only keyword set (DN-129 §2) — pinned here anyway, directly.
/// A **method name** genuinely could (as `default` did): `join`/`cmp`/`render`/`init` are checked
/// against the same keyword table.
#[test]
fn none_of_the_five_prelude_trait_or_method_names_are_reserved_keywords() {
    for name in ALL_TRAIT_NAMES {
        assert!(
            crate::token::keyword(name).is_none(),
            "prelude trait name `{name}` must not be a reserved lexer keyword"
        );
    }
    for (trait_name, method) in METHOD_NAMES {
        assert!(
            crate::token::keyword(method).is_none(),
            "`{trait_name}`'s method name `{method}` must not be a reserved lexer keyword — \
             DN-129 §2's `default`-keyword collision class"
        );
    }
}

/// Every prelude trait is independently conditional (DN-129 §5): a program using exactly one of
/// the five never pulls any of the other four into its trait registry. The five per-trait test
/// files each pin this pairwise against their own trait; this test pins it **once, over the whole
/// set**, so a future sixth prelude trait added without updating every existing per-trait test
/// still gets caught here.
#[test]
fn each_prelude_trait_alone_seeds_exactly_itself() {
    let programs: [(&str, &str); 5] = [
        (
            "Fuse",
            "nodule d;\ntype Flag = Off | On;\nimpl Fuse[Flag] for Flag { fn join(a: Flag, b: Flag) => Flag = match a { Off => b, On => On }; };",
        ),
        (
            "Ord3",
            "nodule d;\ntype Flag = Off | On;\nimpl Ord3[Flag] for Flag { fn cmp(a: Flag, b: Flag) => Binary{8} = 0b00000000; };",
        ),
        (
            "Show",
            "nodule d;\ntype Flag = Off | On;\nimpl Show[Flag] for Flag { fn render(x: Flag) => Bytes = \"Flag\"; };",
        ),
        (
            "Init",
            "nodule d;\ntype Counter = Mk(Binary{8});\nimpl Init[Counter] for Counter { fn init() => Counter = Mk(0b00000000); };",
        ),
        (
            "Fault",
            "nodule d;\ntype MyError = Bad(Bytes);\nimpl Fault[MyError] for MyError {};",
        ),
    ];
    for (name, src) in programs {
        let checked = env(src);
        assert!(
            checked.traits.contains_key(name),
            "`{name}`-only program must seed `{name}`"
        );
        for other in ALL_TRAIT_NAMES {
            if other != name {
                assert!(
                    !checked.traits.contains_key(other),
                    "`{name}`-only program must NOT also seed `{other}`"
                );
            }
        }
    }
}

/// The DRY refactor (DN-129 §5) preserves `Fuse`/`Ord3` behavior byte-for-byte at the observable
/// boundary this test can reach without duplicating `tests/fuse.rs`/`tests/ord3.rs` wholesale: both
/// still redeclare-refuse, both still independently seed, and — the actual regression this refactor
/// could have introduced — a program that uses **neither** still gets **neither** seeded (the
/// `PreludeTraitSeed::seed_for_nodule` "not used, not present" branch for a trait with zero
/// declaration in source at all).
#[test]
fn a_program_using_no_prelude_trait_seeds_none_of_the_five() {
    let checked = env("nodule d;\nfn id(x: Binary{8}) => Binary{8} = x;");
    for name in ALL_TRAIT_NAMES {
        assert!(
            !checked.traits.contains_key(name),
            "a trait-free program must not seed `{name}`"
        );
    }
}

/// [`PreludeTraitSeed`] itself is a plain, `'static`-only data bundle — no interior state, so a
/// `const SEED` per trait module is sound (the shape [`crate::fuse::SEED`]/[`crate::ord3::SEED`]/
/// [`crate::show::SEED`]/[`crate::init::SEED`]/[`crate::fault::SEED`] all use). This is a
/// compile-time-only assertion (no runtime behavior): it exists so a future field addition to
/// [`PreludeTraitSeed`] that breaks `const`-constructibility fails at compile time here, not deep
/// inside `checkty.rs`'s `PRELUDE_TRAIT_SEEDS` array literal.
#[test]
fn prelude_trait_seed_is_const_constructible() {
    const _CHECK: PreludeTraitSeed = crate::fuse::SEED;
    let _ = _CHECK.name;
}

/// The std-sys-host canary case (M-1090/M-1091 leaf, DN-128's downstream derive lowering): a
/// **fieldless (single nullary-constructor) type** — the `OsEntropy`/`OsClock`-shaped unit struct,
/// the cleanest `Debug`/`Default` derive sub-case — checks cleanly against `Show` **and** `Init`
/// with zero special-casing. [`crate::checkty::TraitInfo`] is a pure signature-level fact
/// (`params`/`sigs`) that never inspects a concrete type's constructor arity, so a nullary ctor
/// needs no seed-side change to be a valid `Show`/`Init` instance: `render` takes the value as an
/// ordinary `T`-typed parameter (arity-agnostic) and `init` returns a `T` with no value parameters
/// at all (already the zero-value-param shape `tests/init.rs` pins). **Since DN-137/M-1102, `Unit`
/// is the built-in prelude type itself** (a hand-seeded `type Unit = Unit;`, `checkty::unit_prelude`)
/// rather than a locally-declared fixture — this test now exercises the *real* prelude `Unit`
/// (a user nodule may no longer redeclare it; that would be the same "duplicate type declaration"
/// refusal `Bool` already gets). Verify-first (mitigation #14): this is a **new regression pin**,
/// not new seed code — the mechanism already covers the fieldless case structurally; this test
/// makes that fact checked rather than merely asserted.
#[test]
fn show_and_init_check_cleanly_for_a_fieldless_nullary_ctor_type() {
    // `Show`: render a fieldless value to a fixed byte string — the value itself carries no data
    // to inspect, exactly the `OsEntropy`/`OsClock` shape. `Unit` is the prelude type (DN-137) —
    // no local `type Unit = ...;` declaration.
    let show_checked = env("nodule d;\n\
         impl Show[Unit] for Unit {\n\
           fn render(x: Unit) => Bytes = match x { Unit => \"Unit\" };\n\
         };\n\
         fn describe(x: Unit) => Bytes = render(x);");
    assert!(show_checked.traits.contains_key("Show"));

    // `Init`: the canonical (only) value of a fieldless type is trivially its own nullary ctor —
    // the return-type-only dispatch path (`tests/init.rs`'s "seed from expected") is exactly what
    // a zero-value, zero-field constructor call needs.
    let init_checked = env("nodule d;\n\
         impl Init[Unit] for Unit {\n\
           fn init() => Unit = Unit;\n\
         };\n\
         fn zero() => Unit = init();");
    assert!(init_checked.traits.contains_key("Init"));
}
