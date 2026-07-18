//! **Cross-nodule runtime EXECUTION** integration tests (M-1024 / ENB-1; DN-99 register row #41;
//! the runtime dual of the check-time `resolve_imports`, M-662). Witnesses that a `use`d symbol
//! actually *evaluates* across nodules, via the phylum-wide runtime link [`PhylumEnv::link`].
//!
//! The oracle is a **semantically-equivalent single-nodule program**: a cross-nodule program that
//! `use`s a `pub` fn from a sibling nodule must produce the *same* value as the same logic inlined
//! into one nodule. Each case is checked on **two independent paths** — L1-eval(mono) and
//! elaborate→L0-interp — which must agree with each other and with the inlined oracle.
//!
//! # Honesty tags
//! - **`Empirical`** — the differential agreement (L1-eval ≡ L0-interp ≡ inlined oracle), by trial.
//! - **never-silent (G2)** — a cross-nodule name collision the flat v0 namespace cannot represent is
//!   an explicit refusal from `link`, never a silent winner; the transitive case *without* the link
//!   is an explicit `Stuck`, never a wrong answer.
//!
//! # Residual (flagged, not hidden — VR-5)
//! - **AOT parity** (the third differential leg) is NOT exercised here (the interpreter + L0 legs are
//!   the light, change-scoped witnesses; AOT is desktop-held) — M-1024 follow-up.
//! - **Qualified per-nodule scoping** that would *disambiguate* a collision rather than refuse it is
//!   the M-982 design residual (needs the ratifying DN).

use mycelium_core::CoreValue;
use mycelium_interp::{Interpreter, PrimRegistry};
use mycelium_l1::elab::build_registry;
use mycelium_l1::{
    check_nodule, check_phylum, elaborate, monomorphize, parse, parse_phylum, Env, Evaluator,
    L1Error,
};

/// L1-eval(mono) ≡ elaborate→L0-interp over one checked `Env`, asserting the two paths agree, and
/// returning the (shared) `CoreValue`. The whole-program cross-check that makes a returned value
/// trustworthy (a mutation that diverged the two paths would fail here).
fn eval_both(env: &Env, entry: &str) -> CoreValue {
    let mono = monomorphize(env, entry).expect("monomorphize");
    let registry = build_registry(&mono).expect("build_registry");
    let l1 = Evaluator::new(&mono).call(entry, vec![]).expect("L1-eval");
    let l1_core = l1
        .to_core(&mono, &registry)
        .expect("L1 result in the r3 data fragment");

    let node = elaborate(env, entry).expect("elaborate");
    let interp = Interpreter::new(
        PrimRegistry::with_builtins(),
        Box::new(mycelium_cert::BinaryTernarySwapEngine),
    );
    let l0_core = interp.eval_core(&node).expect("L0-interp");

    assert_eq!(l1_core, l0_core, "L1-eval and L0-interp must agree");
    l1_core
}

/// Run a **single-nodule** program (the inlined oracle).
fn run_single(src: &str) -> CoreValue {
    let env = check_nodule(&parse(src).expect("parse")).expect("check_nodule");
    eval_both(&env, "main")
}

/// Run a **phylum** program through the runtime link (`check_phylum` → `link` → eval).
fn run_phylum(src: &str) -> CoreValue {
    let penv = check_phylum(&parse_phylum(src).expect("parse_phylum")).expect("check_phylum");
    let linked = penv.link().expect("link");
    eval_both(&linked, "main")
}

// ---------------------------------------------------------------------------------------------
// Direct cross-nodule call: `a` imports `b`'s self-contained `pub` fn and calls it at runtime.
// ---------------------------------------------------------------------------------------------
#[test]
fn direct_cross_nodule_pub_fn_executes_equals_inlined_oracle() {
    let xnodule = "phylum p\n\
        nodule b;\n\
        pub fn flip(x: Binary{8}) => Binary{8} = not(x);\n\
        nodule a;\n\
        use b.flip;\n\
        fn main() => Binary{8} = flip(0b0000_0011);";
    let inlined = "nodule solo;\n\
        fn flip(x: Binary{8}) => Binary{8} = not(x);\n\
        fn main() => Binary{8} = flip(0b0000_0011);";
    // Mutant witness: dropping `flip` from `a`'s env (the direct-import seeding in `check_nodule_with`)
    // makes `main` a `Stuck "unknown function flip"`, failing `run_phylum`.
    assert_eq!(run_phylum(xnodule), run_single(inlined));
}

// ---------------------------------------------------------------------------------------------
// Transitive cross-nodule call: `b`'s `pub outer` calls `b`'s PRIVATE `inner`, which `a` never
// imports. Only the phylum-wide link makes `inner` reachable when `a` calls `outer`.
// ---------------------------------------------------------------------------------------------
#[test]
fn transitive_cross_nodule_private_helper_executes_via_link() {
    let xnodule = "phylum p\n\
        nodule b;\n\
        fn inner(x: Binary{8}) => Binary{8} = not(x);\n\
        pub fn outer(x: Binary{8}) => Binary{8} = inner(x);\n\
        nodule a;\n\
        use b.outer;\n\
        fn main() => Binary{8} = outer(0b0000_0011);";
    let inlined = "nodule solo;\n\
        fn inner(x: Binary{8}) => Binary{8} = not(x);\n\
        fn outer(x: Binary{8}) => Binary{8} = inner(x);\n\
        fn main() => Binary{8} = outer(0b0000_0011);";
    // Mutant witness: removing the `own.fns` merge in `PhylumEnv::link` drops `inner` from the linked
    // env, so `outer` becomes a `Stuck "unknown function inner"` — failing this assert.
    assert_eq!(run_phylum(xnodule), run_single(inlined));
}

// ---------------------------------------------------------------------------------------------
// Control: the transitive case WITHOUT the link is a never-silent `Stuck` (documents the exact gap
// the link closes — a private home-nodule name is not reachable from a consumer's per-nodule `Env`).
// ---------------------------------------------------------------------------------------------
#[test]
fn transitive_case_without_link_is_a_never_silent_stuck() {
    let src = "phylum p\n\
        nodule b;\n\
        fn inner(x: Binary{8}) => Binary{8} = not(x);\n\
        pub fn outer(x: Binary{8}) => Binary{8} = inner(x);\n\
        nodule a;\n\
        use b.outer;\n\
        fn main() => Binary{8} = outer(0b0000_0011);";
    let penv = check_phylum(&parse_phylum(src).expect("parse")).expect("check");
    let env_a = penv
        .nodule(&mycelium_l1::ast::Path(vec!["a".to_owned()]))
        .expect("nodule a");
    let mono = monomorphize(env_a, "main").expect("mono");
    let err = Evaluator::new(&mono)
        .call("main", vec![])
        .expect_err("without the link, the private transitive callee is unreachable");
    // Assert the SPECIFIC failure (guard 7): an explicit Stuck naming the unresolved private helper,
    // never a panic and never a wrong value. Mutant witness: linking `inner` in would make this Ok.
    match err {
        L1Error::Stuck { why, .. } => assert!(
            why.contains("inner"),
            "expected an unresolved-`inner` Stuck, got: {why}"
        ),
        other => panic!("expected L1Error::Stuck, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------------------------
// Control (positive twin of the Stuck control): DIRECT cross-nodule execution already works WITHOUT
// the phylum-wide link — a consumer nodule's checked `Env` retains its imported `pub` decls WITH
// their bodies, so a self-contained `use`d fn runs from the per-nodule `Env` alone. Isolates DN-101
// §2's "direct cross-nodule exec already worked" verify-first finding (mitigation #14) as a committed
// guard, rather than relying on it passing incidentally through `link` in test 1. Only the TRANSITIVE
// case (a private home-nodule callee) needs the link — this direct case does not.
// ---------------------------------------------------------------------------------------------
#[test]
fn direct_case_without_link_already_executes_from_per_nodule_env() {
    let src = "phylum p\n\
        nodule b;\n\
        pub fn flip(x: Binary{8}) => Binary{8} = not(x);\n\
        nodule a;\n\
        use b.flip;\n\
        fn main() => Binary{8} = flip(0b0000_0011);";
    let penv = check_phylum(&parse_phylum(src).expect("parse")).expect("check");
    let env_a = penv
        .nodule(&mycelium_l1::ast::Path(vec!["a".to_owned()]))
        .expect("nodule a");
    // Run `a`'s per-nodule env DIRECTLY (no `link()`): the self-contained imported `pub fn flip`
    // already executes. Mutant witness: dropping the direct-import seeding in `check_nodule_with`
    // (which retains imported `pub` bodies in the consumer `Env`) would make this a `Stuck`.
    let mono = monomorphize(env_a, "main").expect("mono");
    let registry = build_registry(&mono).expect("build_registry");
    let direct = Evaluator::new(&mono)
        .call("main", vec![])
        .expect("a self-contained imported `pub fn` runs from the per-nodule env, without the link")
        .to_core(&mono, &registry)
        .expect("L1 result in the r3 data fragment");
    // …and it equals the linked + inlined-oracle value (test 1's `run_phylum`), not merely `Ok`.
    assert_eq!(direct, run_phylum(src));
}

// ---------------------------------------------------------------------------------------------
// Cross-nodule name collision: two nodules each declare a `helper`. The flat v0 namespace cannot
// represent both, so `link` refuses never-silently (never a silent winner — G2).
// ---------------------------------------------------------------------------------------------
#[test]
fn cross_nodule_name_collision_is_a_never_silent_refusal() {
    let src = "phylum p\n\
        nodule b;\n\
        fn helper(x: Binary{8}) => Binary{8} = not(x);\n\
        pub fn outer(x: Binary{8}) => Binary{8} = helper(x);\n\
        nodule a;\n\
        use b.outer;\n\
        fn helper(x: Binary{8}) => Binary{8} = x;\n\
        fn main() => Binary{8} = outer(0b0000_0011);";
    let penv = check_phylum(&parse_phylum(src).expect("parse")).expect("check");
    // The two `helper`s type-check fine (each private to its own nodule); the RUNTIME link is what
    // cannot flatten them. Mutant witness: dropping the `fns.contains_key` guard in `link` would let
    // one silently win, so `link` would return Ok and this `expect_err` would fail.
    let err = penv
        .link()
        .expect_err("a flat-namespace collision must refuse");
    assert!(
        err.message.contains("collision") && err.message.contains("helper"),
        "expected a never-silent `helper` collision refusal, got: {}",
        err.message
    );
}

// ---------------------------------------------------------------------------------------------
// Backward-compat: a phylum-of-one links to an env that runs identically to the `check_nodule` path.
// ---------------------------------------------------------------------------------------------
#[test]
fn phylum_of_one_link_runs_identically_to_check_nodule() {
    let src = "nodule solo;\n\
        fn helper(x: Binary{8}) => Binary{8} = not(x);\n\
        fn main() => Binary{8} = helper(0b0000_1111);";
    let via_link = run_phylum(src); // parse_phylum accepts a header-less single nodule
    let via_nodule = run_single(src);
    assert_eq!(via_link, via_nodule);
}

// ---------------------------------------------------------------------------------------------
// DN-138 §8 WU-2 review finding: two DIFFERENT nodules each hand-declaring the SAME seeded
// primitive instance (`impl Show[Binary{64}] for Binary{64}`) with DIFFERENT bodies. Each nodule
// checks fine independently — `register_instances`' global-uniqueness check is per-nodule, and a
// seeded primitive instance is deliberately excluded from `OwnDecls`'s per-nodule collision set
// (the same reason a SINGLE nodule triggering the seed AND hand-declaring the identical instance is
// accepted, `prelude_instance_seed.rs::an_identical_self_provided_primitive_instance_is_not_a_redeclare_conflict`).
// Only `PhylumEnv::link`'s `impls` map merge (never the `instances` seed-skip loop, which this is
// NOT — the two bodies are DIFFERENT, hand-written impls, not a repeated seed fact) catches this:
// two conflicting method-body lists at the same `(trait, head)` key must never silently pick one.
// Pinned here so a future DRY refactor of the `impls` loop (see its warning comment in
// `PhylumEnv::link`) cannot silently reintroduce a two-nodule coherence-masking bug.
// ---------------------------------------------------------------------------------------------
#[test]
fn two_nodules_hand_declaring_the_same_seeded_instance_with_different_bodies_still_collide() {
    let zero64 = format!("0b{:064b}", 0u64);
    let src = format!(
        "phylum p\n\
         nodule b;\n\
         impl Show[Binary{{64}}] for Binary{{64}} {{\n\
           fn render(x: Binary{{64}}) => Bytes = \"b\";\n\
         }};\n\
         pub fn show_b() => Bytes = render({zero64});\n\
         nodule a;\n\
         impl Show[Binary{{64}}] for Binary{{64}} {{\n\
           fn render(x: Binary{{64}}) => Bytes = \"a\";\n\
         }};\n\
         fn main() => Bytes = render({zero64});"
    );
    let penv = check_phylum(&parse_phylum(&src).expect("parse"))
        .expect("each nodule's own hand-written Show[Binary{64}] impl is locally coherent");
    // Mutant witness: if the `impls` merge loop in `link` ever gained the same seed-skip pattern
    // the `instances` loop has, this would wrongly return `Ok` (first-wins), silently masking a
    // genuine two-nodule coherence conflict.
    let err = penv.link().expect_err(
        "two nodules hand-declaring the SAME seeded instance with DIFFERENT bodies must collide \
         at link time (the `impls` map merge), never silently pick one",
    );
    assert!(
        err.message.contains("collision") && err.message.contains("impl"),
        "expected a never-silent `impl` collision refusal, got: {}",
        err.message
    );
}
