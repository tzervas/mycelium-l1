//! DN-138 WU-4 — the conditionally-seeded `Vec[A]` prelude type ([`crate::checkty::vec_prelude`],
//! [`crate::checkty::seed_vec_type_if_used`], [`crate::checkty::nodule_mentions_named_type`]).
//! Mirrors `tests/preseed.rs`'s cross-cutting-spine test shape, but for a prelude TYPE seed rather
//! than a trait/instance seed — the conditional-on-need discipline extended one axis further
//! (DN-138 §2 fact 2 / `CONDITIONAL_PRELUDE_TYPE_NAMES`'s own doc).

use crate::ast::Phylum;
use crate::checkty::*;
use crate::parse::{parse, parse_phylum};

fn env(src: &str) -> Env {
    check_nodule(&parse(src).expect("parses")).expect("checks")
}

fn env_err(src: &str) -> CheckError {
    check_nodule(&parse(src).expect("parses")).expect_err("must fail to check")
}

/// A program that never mentions `Vec` gets no `Vec` entry in its type registry at all — the
/// conditional-on-need discipline, checked directly (not just "it still type-checks").
#[test]
fn a_vec_free_program_seeds_no_vec_type() {
    let e = env("nodule t;\nfn f() => Binary{8} = 0b0000_0000;");
    assert!(
        !e.types.contains_key("Vec"),
        "a program that never mentions `Vec` must not have it seeded, got {:?}",
        e.types.keys().collect::<Vec<_>>()
    );
}

/// **The mono-fast-path regression guard (DN-138 §2 fact 2, extended to a prelude TYPE).** Every
/// registered type in a `Vec`-free program has EMPTY `params` — the exact precondition
/// `mono::is_already_monomorphic`'s `env.types.values().all(|d| d.params.is_empty())` half checks.
/// An unconditionally-seeded `Vec` (non-empty `params`) would trip this for EVERY program; this
/// test pins that the conditional seed does NOT leak into a program that never asked for it.
#[test]
fn a_vec_free_program_has_only_empty_param_types() {
    let e =
        env("nodule t;\ntype Pair = Pair(Binary{8}, Bool);\nfn f() => Binary{8} = 0b0000_0000;");
    for (name, info) in &e.types {
        assert!(
            info.params.is_empty(),
            "a Vec-free program's type `{name}` must have empty params (mono fast-path \
             precondition), got {:?}",
            info.params
        );
    }
}

/// A field mentioning `Vec[...]` DOES seed it, with the exact `Nil | Cons(A, Vec[A])` shape, and
/// the struct type-checks clean.
#[test]
fn a_program_using_vec_seeds_it_with_the_cons_list_shape() {
    let e = env("nodule t;\ntype Rec = Rec(Vec[Binary{64}], Bytes);");
    let info = e
        .types
        .get("Vec")
        .expect("Vec must be seeded once a field mentions Vec[...]");
    assert_eq!(info.params, vec!["A".to_owned()]);
    assert_eq!(info.ctors.len(), 2, "expected exactly Nil + Cons");
    assert_eq!(info.ctors[0].name, "Nil");
    assert!(info.ctors[0].fields.is_empty());
    assert_eq!(info.ctors[1].name, "Cons");
    assert_eq!(info.ctors[1].fields.len(), 2);
}

/// `Vec` is seeded from a bare `fn` SIGNATURE mention too (not just a `type` field) —
/// [`crate::checkty::nodule_mentions_named_type`]'s signature-walk half.
#[test]
fn a_program_using_vec_only_in_a_fn_signature_seeds_it_too() {
    let e = env("nodule t;\nfn len_of(xs: Vec[Binary{64}]) => Binary{8} = 0b0000_0000;");
    assert!(e.types.contains_key("Vec"));
}

/// A nodule that hand-declares its OWN `type Vec[A] = ...` is never silently shadowed by the seed
/// — the seed checks `types.contains_key("Vec")`/an own `Item::Type` named `Vec` FIRST and simply
/// declines (mirrors why an unconditional prelude type collides via `register_types`'s own
/// duplicate-declaration check, but here there is no collision at all: the hand-written one wins
/// outright, since seeding is conditional in the first place).
#[test]
fn a_nodule_declaring_its_own_vec_wins_over_the_seed() {
    let e = env(
        "nodule t;\ntype Vec[A] = OnlyOne(A);\nfn f(x: Vec[Binary{8}]) => Binary{8} = 0b0000_0000;",
    );
    let info = e.types.get("Vec").expect("Vec is declared");
    assert_eq!(
        info.ctors.len(),
        1,
        "the hand-written single-ctor Vec must win, not the seeded Nil|Cons shape"
    );
    assert_eq!(info.ctors[0].name, "OnlyOne");
}

/// A `Vec` field at a width the corpus actually uses (`Binary{64}`) round-trips through a
/// recursive, plain-fn `Show` route with no coherence involvement — the live end-to-end shape
/// `crate::emit`'s derive rows compose (WU-4), pinned here at the L1-checker level directly (no
/// transpiler in the loop) so this test is independent evidence of the SAME mechanism.
#[test]
fn a_vec_field_recursive_show_route_checks_clean_with_no_trait_instance() {
    let src = "nodule t;\n\
               fn show_vec_Binary_64(xs: Vec[Binary{64}]) => Bytes =\n  \
               match xs { Nil => \"Nil\", Cons(h, t) => bytes_concat(\"Cons(\", bytes_concat(render(h), bytes_concat(\", \", bytes_concat(show_vec_Binary_64(t), \")\")))) };\n\
               impl Show[Binary{64}] for Binary{64} { fn render(x: Binary{64}) => Bytes = \"n\"; };\n\
               type Rec = Rec(Vec[Binary{64}], Bytes);\n\
               impl Show[Rec] for Rec { fn render(x: Rec) => Bytes = match x { Rec(v, s) => bytes_concat(show_vec_Binary_64(v), s) }; };";
    let _ = env(src);
}

/// An unresolvable `Vec` mention (a field with NO `Vec[...]` syntax elsewhere, just a raw `Vec`
/// bare name with no type args) is never silently accepted — G2. (`Vec` requires exactly one type
/// argument; a bare, argument-less mention is a genuine arity error, not a seed trigger bypass.)
#[test]
fn a_bare_vec_with_no_type_argument_is_an_arity_error_never_a_silent_accept() {
    let err = env_err("nodule t;\ntype Rec = Rec(Vec);");
    assert!(
        err.message.to_lowercase().contains("vec") || err.message.to_lowercase().contains("arity"),
        "expected an explicit arity/unknown-type error citing Vec, got: {}",
        err.message
    );
}

/// **Cross-nodule non-collision (the `link()` half).** Two DIFFERENT nodules of one phylum each
/// independently trigger the `Vec` seed — this must NOT be treated as a cross-nodule name
/// collision (mirrors why a `PRELUDE_TRAIT_SEEDS` entry is excluded from `OwnDecls.traits`'s
/// per-nodule collision set); the linked, phylum-wide `Env` ends up with exactly one `Vec` entry.
#[test]
fn two_nodules_each_independently_using_vec_do_not_collide_at_link() {
    let ph: Phylum = parse_phylum(
        "phylum app\n\
         nodule a;\n\
         type RecA = RecA(Vec[Binary{64}]);\n\
         nodule b;\n\
         type RecB = RecB(Vec[Bytes]);",
    )
    .expect("parses as a phylum");
    let penv = check_phylum(&ph).expect("phylum checks (Vec seeded independently per nodule)");
    let linked = penv
        .link()
        .expect("link succeeds -- no false cross-nodule Vec collision");
    assert!(linked.types.contains_key("Vec"));
}

/// **CRITICAL (post-landing review finding, fixed here): a nodule's GENUINE hand-written `Vec`
/// must never be SILENTLY overwritten by the seed's `Nil | Cons` shape just because some OTHER
/// nodule of the same phylum happens to trigger it.** Nodule `a` hand-declares its own
/// `type Vec[A] = OnlyOne(A);` (a single-ctor shape, nothing like the seed); nodule `b` mentions
/// `Vec[Binary{64}]` as a field and so triggers the CONDITIONAL seed in its OWN registration.
/// `check_phylum` succeeds (each nodule checks fine against its OWN registry — `a` against its
/// hand-written `Vec`, `b` against the seeded one). The unsound outcome this test forbids is
/// `link()` SUCCEEDING with `a`'s `Vec` silently replaced by the seed (or vice versa) — the v0
/// flat single-namespace model cannot represent both shapes at once, and `b`'s already-checked
/// functions rely on the seeded `Nil`/`Cons` constructors existing in the LINKED env, so
/// silently keeping `a`'s shape would ALSO be unsound (missing constructors at eval time), not
/// just "the hand-written one should always win". The only never-silent resolution is a loud
/// `collide()` refusal — asserted here directly (never a silent pick either way, G2/VR-5).
#[test]
fn a_hand_written_vec_in_one_nodule_never_silently_loses_or_wins_against_a_seed_in_another() {
    let ph: Phylum = parse_phylum(
        "phylum app\n\
         nodule a;\n\
         type Vec[A] = OnlyOne(A);\n\
         nodule b;\n\
         type RecB = RecB(Vec[Binary{64}]);",
    )
    .expect("parses as a phylum");
    let penv = check_phylum(&ph).expect(
        "each nodule checks fine independently -- a against its own hand-written Vec, b against \
         its own seeded Vec",
    );
    let err = penv.link().expect_err(
        "link MUST refuse loudly -- a hand-written Vec co-present with a nodule that \
                      needs the seeded shape is a real, irreconcilable phylum-wide conflict, never \
                      a silent pick either way",
    );
    assert!(
        err.message.to_lowercase().contains("vec"),
        "expected the collision error to name `Vec`, got: {}",
        err.message
    );
    assert!(
        err.message.to_lowercase().contains("collision")
            || err.message.to_lowercase().contains("collide"),
        "expected an explicit cross-nodule collision message, got: {}",
        err.message
    );
}

/// The companion control: if nodule `a` hand-declares a `Vec` that happens to be structurally
/// IDENTICAL to the seed's shape, there is no real conflict — but note this is expected to be
/// unreachable in practice for a HAND-WRITTEN declaration, since DN-112 Rank-1 home-qualification
/// stamps a hand-written type's identity with its OWN declaring nodule's home (never the
/// `PRELUDE_HOME` the seed uses) — so even a byte-for-byte textual duplicate never structurally
/// equals `vec_prelude()` and this path is not exercised by ordinary user code. Documented, not
/// silently assumed: a genuine collision (this test's sibling above) is the realistic outcome for
/// ANY hand-written `Vec`, not just a differently-shaped one.
#[test]
fn a_hand_written_vec_never_structurally_equals_the_seed_even_if_textually_identical() {
    let e = env(
        "nodule a;\ntype Vec[A] = Nil | Cons(A, Vec[A]);\nfn f(x: Vec[Binary{8}]) => Binary{8} = 0b0000_0000;",
    );
    let hand_written = e.types.get("Vec").expect("Vec is declared");
    assert_ne!(
        hand_written,
        &vec_prelude(),
        "a hand-written Vec's home is its OWN declaring nodule (DN-112 Rank 1), never \
         PRELUDE_HOME -- it must never structurally equal the seed's fact even when textually \
         identical"
    );
}
