//! DN-138 §4.1 Alt A / §8 WU-2 — the `PRELUDE_INSTANCE_SEEDS` primitive-instance-seed spine.
//!
//! **The load-bearing test in this file is [`every_seed_sig_pins_to_its_real_lib_std_body`]** (DN-138
//! §5 obligation 1 — the whole soundness argument for Alt A rests on it): each seeded
//! [`crate::checkty::InstanceInfo`] is diffed, byte-for-byte (`for_ty`/`trait_args`/`methods`),
//! against what the REAL `lib/std/fmt.myc` (`Show`) / `lib/std/derive_prelude.myc` (`Init`/`Ord3`)
//! body actually checks to. A seed whose `for_ty` names a width/type the real body does not provide
//! fails here (a `None` lookup); a seed whose method-name set diverges from the real impl's checked
//! method set ALSO fails here (`InstanceInfo`'s `PartialEq` compares the whole struct). Because
//! every one of `Show`/`Init`/`Ord3` is single-parameter and param-only-sig (DN-122 §13.1's admitted
//! shape), pinning `for_ty` exactly determines the substituted method signature too (the trait's own
//! `TraitInfo` is a fixed Rust constant) — so this `InstanceInfo` diff is not merely a name check,
//! it is the full signature pin DN-138 §5 obligation 1 demands. Instance EXISTENCE is subsumed: no
//! real body ⇒ `real_env.instances.get(&key)` is `None` ⇒ the test fails (never a false pass).
//!
//! **CRITICAL fix, take 2 (this leaf supersedes the thread-local-guard attempt).** The claim in the
//! previous paragraph was FALSE as originally implemented: the sig-pin test used to build its
//! oracle `Env`s via the ORDINARY `check_nodule` pipeline, which unconditionally re-runs the
//! [`crate::checkty::PRELUDE_INSTANCE_SEEDS`] seeding step on every nodule it checks — so a seed
//! naming a head the real body does NOT provide self-inserts into its own empty `instances` slot
//! while the "real" oracle is being built, and the comparison then diffs the seed against ITSELF
//! (a trivial, silent pass). Proof: mutating `seed_init_bool()`'s `for_ty` to a nonexistent head
//! still passed all 9 entries. Drift on an ALREADY-EXISTING head is still caught correctly (the
//! real declaration registers first, so the seed's `entry().or_insert()` is a no-op and the
//! comparison is genuine) — only a NOVEL nonexistent head was silently masked.
//!
//! **Attempt 1** (the bug above) built the oracle via ordinary `check_nodule` — contaminated by
//! the seeding step. **Attempt 2** tried a `cfg(test)` thread-local suppression flag
//! (`SuppressInstanceSeedingForTest`) set on the caller thread before calling `check_nodule` — but
//! this was a NO-OP: `check_nodule` → `check_and_resolve_matured` runs its body inside
//! [`mycelium_stack::with_deep_stack`], which spawns a **real OS worker thread**
//! (`std::thread::Builder::spawn_scoped`) to run the check. A `thread_local!` is per-thread by
//! definition, so the flag set on the caller thread was invisible to the worker thread that
//! actually ran the seeding loop — the oracle stayed contaminated exactly as before, just with
//! dead-looking guard machinery masking it.
//!
//! **The actual fix (this leaf):** stop going through `check_nodule`/`check_phylum` (and therefore
//! `with_deep_stack`'s thread boundary) for the oracle at all. [`fmt_real_instances`] /
//! [`derive_prelude_real_instances`] call the **direct registration passes**
//! ([`crate::checkty::register_nodule_decls`] then [`crate::checkty::register_instances`]) — the
//! exact same functions [`check_nodule`]'s pipeline itself uses to build the DECLARED-instance
//! table, *before* the `PRELUDE_INSTANCE_SEEDS` seeding step ever runs (see
//! `check_nodule_with`/`check_and_resolve_matured_inner` in `crate::checkty`: `register_instances`
//! is called first, seeding is a separate, later step over the same map). Since these are plain,
//! synchronous, non-thread-spawning functions, there is no thread boundary to cross and nothing to
//! suppress: the returned instance table reflects ONLY what `fmt.myc`/`derive_prelude.myc`
//! themselves declare via a real `impl` — a seed naming an absent head then has nothing to
//! self-insert into, so `real.get(&key)` is genuinely `None`. Proven non-vacuous by
//! [`a_seed_naming_a_head_absent_from_the_real_body_is_caught_by_the_clean_oracle`], which mutates a
//! REAL entry of `PRELUDE_INSTANCE_SEEDS` itself (a test-local copy of the real 9-entry array with
//! ONE entry's `instance` fn pointer swapped for a mutated variant — see
//! [`seeds_with_one_real_entry_mutated_to_an_absent_head`]) and runs it through the same
//! [`assert_every_seed_pins`] the real test above calls — not a decoy constant kept outside the
//! array (a prior attempt's mistake, which never round-trips through the real seed table and so
//! proves nothing about it).

use std::collections::BTreeMap;

use crate::checkty::*;
use crate::parse;

fn env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("checks")
}

fn check_err(src: &str) -> CheckError {
    check_nodule(&parse(src).expect("parses")).expect_err("must fail to check")
}

/// `Show`'s real primitive instances (DN-127, already landed) — `lib/std/fmt.myc`.
const FMT_SRC: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../lib/std/fmt.myc"
));

/// `Init`/`Ord3`'s real primitive instances (DN-138 WU-1, this leaf) — `lib/std/derive_prelude.myc`.
const DERIVE_PRELUDE_SRC: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../lib/std/derive_prelude.myc"
));

/// **THE sig-pin oracle builder (DN-138 §5 obligation 1, actual fix).** Builds the REAL declared-
/// instance table of one `lib/std` source nodule by calling the exact same **direct registration
/// passes** [`check_nodule`]'s own pipeline uses to populate `Env::instances` —
/// [`register_nodule_decls`] for the per-nodule type/trait registries, then [`register_instances`]
/// for the `impl`-block instance table — WITHOUT ever calling `check_nodule`/`check_phylum`
/// (and so without ever entering [`mycelium_stack::with_deep_stack`]'s worker-thread boundary) and
/// WITHOUT ever reaching the later, separate `PRELUDE_INSTANCE_SEEDS` seeding step (which lives in
/// `check_nodule_with`, a function this helper never calls). Since there is no seeding step in this
/// call path at all — not "suppressed", simply absent — the returned table is exactly (and only)
/// what the source's own `impl` blocks register: a seed naming a head absent from it has nothing to
/// have self-inserted, so `real.get(&key)` is genuinely `None`.
fn real_declared_instances(src: &str) -> BTreeMap<(String, String), InstanceInfo> {
    let parsed = parse(src).expect("parses");
    let resolved = crate::ambient::resolve(&parsed).expect("ambient-resolves");
    let regs = register_nodule_decls(&resolved).expect("registers declarations");
    // Mirrors `check_phylum_inner`'s own phylum-wide `CoherenceView` construction (`checkty.rs`) for
    // a phylum-of-one: every declared trait/type name, pub-blind, minus the unconditionally-seeded
    // prelude types — the identical view `register_instances`'s orphan-rule locality test consults
    // in the real pipeline.
    let mut coherence = CoherenceView::default();
    for name in regs.traits.keys() {
        coherence.traits.insert(name.clone());
    }
    for name in regs.types.keys() {
        if !PRELUDE_UNCONDITIONAL_TYPE_NAMES.contains(&name.as_str()) {
            coherence.types.insert(name.clone());
        }
    }
    register_instances(&regs.types, &regs.traits, &coherence, &resolved)
        .expect("registers instances")
}

/// `Show`'s real declared-instance table (DN-127, already landed) — `lib/std/fmt.myc`.
fn fmt_real_instances() -> BTreeMap<(String, String), InstanceInfo> {
    real_declared_instances(FMT_SRC)
}

/// `Init`/`Ord3`'s real declared-instance table (DN-138 WU-1) — `lib/std/derive_prelude.myc`.
fn derive_prelude_real_instances() -> BTreeMap<(String, String), InstanceInfo> {
    real_declared_instances(DERIVE_PRELUDE_SRC)
}

/// The sig-pin core check, factored out so both the real (9-seed, all-real-heads) test and the
/// adversarial (mutated-head) regression test below exercise the IDENTICAL comparison logic — the
/// only variable is which seed list and which real instance tables are passed in. Panics on the
/// first divergence, exactly like the original inline loop; the adversarial test observes that
/// with `std::panic::catch_unwind`.
fn assert_every_seed_pins(
    seeds: &[crate::preseed::PreludeInstanceSeed],
    fmt: &BTreeMap<(String, String), InstanceInfo>,
    prelude: &BTreeMap<(String, String), InstanceInfo>,
) {
    for seed in seeds {
        let seeded = (seed.instance)();
        let head = type_head(&seeded.for_ty)
            .unwrap_or_else(|| panic!("seed for `{}` has no concrete head", seed.trait_name));
        let key = (seed.trait_name.to_owned(), head.clone());
        let real_instances = if seed.trait_name == "Show" {
            fmt
        } else {
            prelude
        };
        let real = real_instances.get(&key).unwrap_or_else(|| {
            panic!(
                "no REAL `{}` instance at head `{head}` found in the lib/std oracle — the seed \
                 claims a resolution fact `lib/std` does not actually provide (DN-138 §5 obl. 1 \
                 sig-drift hazard). seeded={seeded:?}",
                seed.trait_name
            )
        });
        assert_eq!(
            real, &seeded,
            "seed/body divergence for `{}` at head `{head}` — the seeded fact and the real \
             `lib/std` instance must be byte-identical (for_ty/trait_args/methods); a mismatch \
             here is exactly the check-passes/eval-fails hazard DN-138 §5 obl. 1 exists to catch",
            seed.trait_name
        );
    }
}

/// **THE sig-pin differential (DN-138 §5 obligation 1).** Every entry of
/// [`crate::checkty::PRELUDE_INSTANCE_SEEDS`] is diffed against the real `lib/std` body it claims
/// to mirror, built via the direct-registration oracle above (never through `check_nodule`'s
/// seeding step — see the module doc). Non-vacuous: 9 entries, each independently looked up; a
/// drift in ANY one of them (wrong width, wrong method name, a body that stops existing) fails this
/// test at the specific failing entry, naming it — and, per the sibling adversarial test below, a
/// head absent from the real body is now genuinely caught, never silently masked by seed
/// self-insertion (there is no seeding step in this oracle's call path to self-insert with).
#[test]
fn every_seed_sig_pins_to_its_real_lib_std_body() {
    let fmt = fmt_real_instances();
    let prelude = derive_prelude_real_instances();
    assert_every_seed_pins(&PRELUDE_INSTANCE_SEEDS, &fmt, &prelude);
    assert_eq!(
        PRELUDE_INSTANCE_SEEDS.len(),
        9,
        "expected exactly the 9 DN-138 increment-1 seeds (Show/Init/Ord3 x Binary{{64}}/Bytes/Bool)"
    );
}

/// A mutated stand-in for [`crate::checkty`]'s private `seed_init_bool` builder, with `for_ty`/
/// `trait_args` swapped to a head neither `lib/std/fmt.myc` nor `lib/std/derive_prelude.myc` ever
/// declares an instance of — the EXACT mutation the strict-review mutation test found (mutating
/// `seed_init_bool()`'s `for_ty` to `Ty::Data("NotReal", vec![])` and observing all 9 entries still
/// pass under the old, contaminated oracle).
fn mutated_seed_init_bool_naming_an_absent_head() -> InstanceInfo {
    InstanceInfo {
        trait_name: "Init".to_owned(),
        trait_args: vec![Ty::Data("AdversarialNotReal".to_owned(), vec![])],
        for_ty: Ty::Data("AdversarialNotReal".to_owned(), vec![]),
        methods: vec!["init".to_owned()],
    }
}

/// A **test-local copy of the REAL `PRELUDE_INSTANCE_SEEDS` array** with exactly ONE entry's
/// `instance` fn pointer swapped for [`mutated_seed_init_bool_naming_an_absent_head`] — every other
/// field of every entry (including that entry's own `trait_name`/`impl_hint`) is untouched. This is
/// deliberately NOT a decoy object kept outside the array (the vacuous shape a prior attempt at
/// this fix used, which never round-trips through the real 9-entry table `assert_every_seed_pins`
/// is meant to validate — a decoy proves nothing about whether the REAL array's entries are
/// genuinely checked against the real body). `PRELUDE_INSTANCE_SEEDS` is a `const`, so each
/// reference re-materializes a fresh array value — copying it out here needs no `Clone`/`Copy` derive
/// on [`crate::preseed::PreludeInstanceSeed`].
///
/// Index 5 is `Init`/`Bool` (`seed_init_bool`) — see the field order in
/// [`crate::checkty::PRELUDE_INSTANCE_SEEDS`]'s definition (Show × 3, then Init × 3, then Ord3 × 3;
/// `Bool` is each trait's third/last primitive head).
fn seeds_with_one_real_entry_mutated_to_an_absent_head() -> [crate::preseed::PreludeInstanceSeed; 9]
{
    let mut seeds = PRELUDE_INSTANCE_SEEDS;
    assert_eq!(
        seeds[5].trait_name, "Init",
        "index 5 must be the `Init`/`Bool` entry — this test's index assumption has drifted from \
         `PRELUDE_INSTANCE_SEEDS`'s real layout; update the index (never silently mutate the wrong \
         entry)"
    );
    seeds[5].instance = mutated_seed_init_bool_naming_an_absent_head;
    seeds
}

/// **The real adversarial proof of the fix (DN-138 §5 obl. 1).** Mutates a REAL entry of
/// [`crate::checkty::PRELUDE_INSTANCE_SEEDS`] itself (via
/// [`seeds_with_one_real_entry_mutated_to_an_absent_head`], not a decoy kept outside the array) to
/// name a head absent from both real oracle files, then runs it through the exact same
/// [`assert_every_seed_pins`] the real, non-mutated test above calls — this must genuinely fail:
/// the mutated head is truly absent from what `fmt.myc`/`derive_prelude.myc` themselves declare
/// (the direct-registration oracle never seeds anything), so the lookup is `None` and the check
/// panics. This is the non-vacuous proof that DN-138 §5 obligation 1's guardrail now actually
/// catches a nonexistent-head seed — reproducing, and now genuinely closing, the strict-review
/// mutation-testing finding described in the module doc.
#[test]
fn a_seed_naming_a_head_absent_from_the_real_body_is_caught_by_the_clean_oracle() {
    let fmt = fmt_real_instances();
    let prelude = derive_prelude_real_instances();
    let mutated_seeds = seeds_with_one_real_entry_mutated_to_an_absent_head();
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        assert_every_seed_pins(&mutated_seeds, &fmt, &prelude);
    }));
    assert!(
        caught.is_err(),
        "a REAL PRELUDE_INSTANCE_SEEDS entry mutated to name a head absent from BOTH real oracle \
         files must make the sig-pin check FAIL — non-vacuous proof the guardrail actually catches \
         a nonexistent-head seed drawn from the real seed table, not merely a re-diff of a \
         self-inserted fact"
    );
}

/// A fabricated `InstanceInfo` at a head neither `lib/std/fmt.myc` nor
/// `lib/std/derive_prelude.myc` ever declares an instance of, and which `PRELUDE_INSTANCE_SEEDS`
/// itself never seeds — used only by
/// [`seed_instance_for_nodule_self_inserts_a_fact_at_an_otherwise_unoccupied_key`] below to pin the
/// self-insertion mechanism of [`crate::preseed::PreludeInstanceSeed::seed_instance_for_nodule`]
/// directly (a still-real, still-load-bearing production function — this is NOT used to build or
/// stand in for the sig-pin oracle above, which never calls it at all).
fn bogus_absent_head_instance() -> InstanceInfo {
    InstanceInfo {
        trait_name: "Init".to_owned(),
        trait_args: vec![Ty::Data("AdversarialNotReal".to_owned(), vec![])],
        for_ty: Ty::Data("AdversarialNotReal".to_owned(), vec![]),
        methods: vec!["init".to_owned()],
    }
}

const BOGUS_SEED: crate::preseed::PreludeInstanceSeed = crate::preseed::PreludeInstanceSeed {
    trait_name: "Init",
    impl_hint: "impl Init[AdversarialNotReal] for AdversarialNotReal { … } (test-only, fabricated \
                — never a real prelude seed)",
    instance: bogus_absent_head_instance,
};

/// **Mutation-witnessed proof of the bug this leaf fixes** (pinned so the contamination hole can
/// never silently return). Directly exercises the mechanism the strict review's mutation test
/// found: [`crate::preseed::PreludeInstanceSeed::seed_instance_for_nodule`] — the exact function
/// `check_nodule`'s per-nodule pass loops over `PRELUDE_INSTANCE_SEEDS` to call — self-inserts its
/// OWN fabricated fact into an otherwise-empty `instances` map for any nodule that merely triggers
/// the seed's trait, with no regard for whether a real declaration exists anywhere. This is a
/// standing regression test of that production mechanism, independent of the sig-pin oracle above
/// (which sidesteps `seed_instance_for_nodule`/`check_nodule` entirely and so never observes this
/// self-insertion at all — that is precisely why building the oracle via direct registration closes
/// the hole, rather than merely trying to suppress this call).
#[test]
fn seed_instance_for_nodule_self_inserts_a_fact_at_an_otherwise_unoccupied_key() {
    // A nodule that triggers `Init` (any `impl Init[...] for ...`) but declares NOTHING at the
    // bogus seed's own head — the real-world shape of "a seed whose head the real body doesn't
    // provide".
    let nodule = crate::parse(
        "nodule d;\n\
         type Wrap = Wrap(Bytes);\n\
         impl Init[Wrap] for Wrap {\n\
           fn init() => Wrap = Wrap(init());\n\
         };",
    )
    .expect("parses");
    let mut instances: BTreeMap<(String, String), InstanceInfo> = BTreeMap::new();
    BOGUS_SEED.seed_instance_for_nodule(&mut instances, &nodule);
    assert_eq!(
        instances.get(&("Init".to_owned(), "Data:AdversarialNotReal".to_owned())),
        Some(&bogus_absent_head_instance()),
        "seed_instance_for_nodule must have self-inserted its own fabricated fact at its own \
         empty key — this is the exact self-insertion mechanism that made the ORIGINAL (ordinary \
         check_nodule-based) sig-pin oracle vacuous; the fix works around it by building the \
         oracle via direct registration, which never calls this function at all"
    );
}

/// DN-138 §5 obligation 4 (conditional-on-need) / §2 fact 2 (the `mono` fast-path regression this
/// guards against): a program that uses NONE of `Show`/`Init`/`Ord3` gets NO seeded instance at
/// all — `env.instances` stays empty, preserving `crate::mono::is_already_monomorphic`'s
/// `env.instances.is_empty()` fast-path for every trait-free program.
#[test]
fn a_trait_free_program_seeds_no_primitive_instance() {
    let checked = env("nodule d;\nfn id(x: Binary{8}) => Binary{8} = x;");
    assert!(
        checked.instances.is_empty(),
        "a trait-free program must not seed any primitive instance, got {:?}",
        checked.instances.keys().collect::<Vec<_>>()
    );
}

/// The positive integration case: a nodule that declares its OWN `impl Show[Struct] for Struct`
/// whose body calls `render` on a `Binary{64}` field resolves the seeded `Show[Binary{64}]`
/// instance with no local declaration of it — this is the exact shape a transpiled
/// `derive(Debug)`-composed struct produces (DN-138 §1/§3).
#[test]
fn a_struct_impl_resolves_the_seeded_binary64_show_instance_with_no_local_declaration() {
    let checked = env(
        "nodule d;\n\
         type Pair = Pair(Binary{64}, Bytes);\n\
         impl Show[Pair] for Pair {\n\
           fn render(x: Pair) => Bytes =\n\
             match x { Pair(a, b) => bytes_concat(bytes_concat(\"Pair(\", render(a)), render(b)) };\n\
         };",
    );
    assert!(checked.traits.contains_key("Show"));
    assert!(checked
        .instances
        .contains_key(&("Show".to_owned(), "Binary".to_owned())));
    assert!(checked
        .instances
        .contains_key(&("Show".to_owned(), "Bytes".to_owned())));
    // The user's OWN instance is present too, distinct from the seeded primitive ones (DN-112
    // Rank 1: a nodule-qualified `Ty::Data` head, `"Data:<home>::Pair"` for `nodule d;`'s home `d`).
    assert!(checked
        .instances
        .contains_key(&("Show".to_owned(), "Data:d::Pair".to_owned())));
}

/// Same shape for `Init`/`Ord3` — a struct deriving `Default`/`PartialOrd`-equivalent composition
/// over a `Binary{64}` field resolves the seeded instances with no local declaration.
#[test]
fn a_struct_impl_resolves_the_seeded_binary64_init_and_ord3_instances() {
    let init_checked = env("nodule d;\n\
         type Wrap = Wrap(Binary{64});\n\
         impl Init[Wrap] for Wrap {\n\
           fn init() => Wrap =\n\
             Wrap(init());\n\
         };");
    assert!(init_checked
        .instances
        .contains_key(&("Init".to_owned(), "Binary".to_owned())));

    let ord_checked = env("nodule d;\n\
         type Wrap = Wrap(Binary{64});\n\
         impl Ord3[Wrap] for Wrap {\n\
           fn cmp(a: Wrap, b: Wrap) => Binary{8} =\n\
             match a { Wrap(p0) => match b { Wrap(q0) => cmp(p0, q0) } };\n\
         };");
    assert!(ord_checked
        .instances
        .contains_key(&("Ord3".to_owned(), "Binary".to_owned())));
}

/// **Verify-first correction (mitigation #14 / VR-5), pinned as its own regression:** an IDENTICAL
/// self-provision (a nodule that both triggers the `Show` seed and ALSO hand-declares the exact
/// SAME `Show[Binary{64}]` instance the seed provides) is NOT refused — it is exactly the
/// `lib/std/fmt.myc`/`lib/std/derive_prelude.myc` shape (the sig-pin test's own oracle files), and
/// must check clean. The real-hand-written instance simply wins; nothing is seeded on top of it.
#[test]
fn an_identical_self_provided_primitive_instance_is_not_a_redeclare_conflict() {
    let checked = env("nodule d;\n\
         type Pair = Pair(Binary{64});\n\
         impl Show[Pair] for Pair {\n\
           fn render(x: Pair) => Bytes = match x { Pair(a) => render(a) };\n\
         };\n\
         impl Show[Binary{64}] for Binary{64} {\n\
           fn render(x: Binary{64}) => Bytes = \"x\";\n\
         };");
    assert!(checked
        .instances
        .contains_key(&("Show".to_owned(), "Binary".to_owned())));
}

/// **Verify-first correction (mitigation #14 / VR-5), the SECOND independent disconfirmation of
/// DN-138 §5 obligation 5's literal wording:** a nodule that triggers the `Show` seed and ALSO
/// hand-declares a DIFFERENT concrete type at the SAME width-erased `"Binary"` head the seed
/// occupies (`Binary{32}` vs the seed's `Binary{64}`) is a real, already-shipped shape — the
/// pre-existing DN-122/M-1080 MVP foreign-trait-impl test hand-declares exactly this for `Ord3`
/// (`impl Ord3[Binary{8}] for Binary{8}` in complete isolation), and it must keep checking clean.
/// The corrected semantics: the nodule's OWN instance wins (registered exactly as declared,
/// `Binary{32}`, never silently swapped for the seed's `Binary{64}`), and the seed simply declines
/// to add anything on top — proven here by asserting the actually-registered `for_ty`.
#[test]
fn a_nodule_own_different_width_instance_at_the_seeded_head_wins_over_the_seed() {
    let checked = env("nodule d;\n\
         type Pair = Pair(Bool);\n\
         impl Show[Pair] for Pair {\n\
           fn render(x: Pair) => Bytes = match x { Pair(a) => render(a) };\n\
         };\n\
         impl Show[Binary{32}] for Binary{32} {\n\
           fn render(x: Binary{32}) => Bytes = \"x\";\n\
         };");
    let registered = checked
        .instances
        .get(&("Show".to_owned(), "Binary".to_owned()))
        .expect("some Show/Binary instance must be registered");
    assert_eq!(
        registered.for_ty,
        Ty::Binary(Width::Lit(32)),
        "the nodule's OWN Binary{{32}} instance must win over the seed's Binary{{64}} fact, got {registered:?}"
    );
}

/// DN-138 §2 fact 1 (width-erased coherence) / §5(b) (the "honest width-mismatch gap" the
/// adversarial stress-test names): a struct whose field is a NARROW `Binary{8}` (not the seeded
/// `Binary{64}`) still refuses to resolve `render` for it — the seed only covers the one width
/// increment 1 targets; a narrower width is an explicit, never-silent `myc check` refusal, never a
/// silently-reused mismatched instance (`require_instance`'s own `info.for_ty == *concrete` guard).
#[test]
fn a_narrow_width_scalar_field_does_not_silently_reuse_the_binary64_show_instance() {
    let err = check_err(
        "nodule d;\n\
         type Pair = Pair(Binary{8});\n\
         impl Show[Pair] for Pair {\n\
           fn render(x: Pair) => Bytes = match x { Pair(a) => render(a) };\n\
         };",
    );
    assert!(
        err.message.contains("Show") && err.message.contains("Binary{8}"),
        "expected an explicit no-instance-for-Binary{{8}} refusal, got: {}",
        err.message
    );
}

/// `Float` is never seeded (DN-138 §5 obligation 3 / ADR-040): no `(Show|Init|Ord3, "Float")` key
/// ever appears among the 9 increment-1 seeds.
#[test]
fn float_is_never_among_the_seeded_heads() {
    for seed in PRELUDE_INSTANCE_SEEDS {
        let info = (seed.instance)();
        assert_ne!(
            type_head(&info.for_ty),
            Some("Float".to_owned()),
            "`{}` must never seed a `Float` instance (ADR-040)",
            seed.trait_name
        );
    }
}
