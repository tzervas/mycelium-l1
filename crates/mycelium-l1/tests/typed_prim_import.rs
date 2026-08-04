//! **S-TYPED-PRIM-ENV / S-TYPED-PRIM-CALL-CHECK** (PKG-LINKAGE, mycelium-lang#44 — FROZEN,
//! mycelium-lang PR #49) integration tests: `TypedPrimEnv` as a second `use dep::a.b.fn` resolution
//! target beside `Phyla`, and the structural (arity + per-arg `Ty`, no coercion) call-check against a
//! registered `mycelium_interp::typed::PrimSig` before elaboration to `Node::Op{prim:"prim:…"}`.
//!
//! These fixtures hand-construct a `PrimSig` the way a real provider crate (`mycelium-std-io`,
//! `mycelium-std-net`) would via `TypedPrimEnv::register` — this package's own non-goals note that
//! porting those crates is separate work; the mechanism is what is under test here.

use mycelium_core::ContentHash;
use mycelium_core::{GuaranteeStrength, Node};
use mycelium_interp::typed::{PrimSig, TySpec, WidthSpec};
use mycelium_l1::{
    check_phylum_with_deps, check_phylum_with_deps_and_prims, elaborate, parse_phylum, CheckError,
    Phyla, Phylum, ResolvedPhylum, TypedPrimEnv,
};
use std::collections::BTreeMap;

fn phy(src: &str) -> Phylum {
    parse_phylum(src).expect("fixture parses as a phylum")
}

fn fixture_hash(discriminator: u8) -> ContentHash {
    let digest = format!("{discriminator:02x}").repeat(32);
    ContentHash::from_parts("blake3", &digest).expect("well-formed fixture digest")
}

fn resolved(src: &str, discriminator: u8) -> ResolvedPhylum {
    ResolvedPhylum::resolve(fixture_hash(discriminator), &phy(src), &Phyla::default())
        .expect("dependency fixture checks")
}

/// A pure (0-effect) typed-prim signature: `to_json(Binary{8}) -> Bytes`, mirroring
/// `mycelium-std-io`'s real `serialize::to_json` shape (PKG-LINKAGE's proof-of-mechanism target) —
/// a monomorphic instantiation, per the frozen surface's v0 scope note (one `PrimSig` per
/// concretely-instantiated width actually exercised, not a generic signature).
fn to_json_sig() -> PrimSig {
    PrimSig {
        name: "std.io.serialize.to_json".to_owned(),
        params: vec![TySpec::Binary(WidthSpec(8))],
        ret: TySpec::Bytes,
        effects: vec![],
        guarantee: GuaranteeStrength::Exact,
    }
}

/// An effectful typed-prim signature: `http_request(Bytes) -> Bytes`, `effects:["net"]` — mirroring
/// `mycelium-std-net`'s real `http_request` shape (S-STD-NET-SAFE-HTTP's proof-of-mechanism target).
fn http_request_sig() -> PrimSig {
    PrimSig {
        name: "std.net.http.http_request".to_owned(),
        params: vec![TySpec::Bytes],
        ret: TySpec::Bytes,
        effects: vec!["net".to_owned()],
        guarantee: GuaranteeStrength::Declared,
    }
}

fn prims_with(dep: &str, path_in_dep: &str, sig: PrimSig) -> TypedPrimEnv {
    let mut p = TypedPrimEnv::default();
    p.register(dep, path_in_dep, sig);
    p
}

fn check_err(src: &str, deps: &Phyla, prims: &TypedPrimEnv) -> CheckError {
    check_phylum_with_deps_and_prims(&phy(src), deps, prims)
        .expect_err("fixture is expected to fail `myc check`")
}

// ---------------------------------------------------------------------------------------------
// MEASURED BASELINE (kickoff brief): a real, tested Rust std function unreachable from `.myc`
// through the ordinary `App{head:Path([name])}` call-check path — the SAME "unknown
// function/constructor/prim" refusal a fabricated identifier gets, when no typed-prim `use`
// resolves the name. Reproduced here (not just narrated) so the fix below is provably additive.
// ---------------------------------------------------------------------------------------------

#[test]
fn baseline_an_unimported_std_fn_name_is_unknown_function_constructor_prim() {
    let src = "phylum p\nnodule demo;\nfn main() => Binary{8} = to_json(0b0010_1010);";
    let err = check_phylum_with_deps(&phy(src), &Phyla::default())
        .expect_err("an unimported name must refuse exactly like a fabricated one");
    assert!(
        err.message
            .contains("unknown function/constructor/prim `to_json`"),
        "baseline message shape changed unexpectedly: {}",
        err.message
    );
}

// ---------------------------------------------------------------------------------------------
// (a) A 0-effect typed-prim call needs no `!{}` annotation and checks + elaborates to
//     `Node::Op{prim:"prim:<qualified>"}` — never `wild`, never `@std-sys`-gated.
// ---------------------------------------------------------------------------------------------

#[test]
fn typed_prim_zero_effect_call_needs_no_effect_annotation_and_elaborates_to_prim_op() {
    let prims = prims_with("std_io", "serialize.to_json", to_json_sig());
    let src = "phylum p\nnodule demo;\nuse std_io::serialize.to_json;\n\
               fn main() => Bytes = to_json(0b0010_1010);";
    let penv = check_phylum_with_deps_and_prims(&phy(src), &Phyla::default(), &prims)
        .expect("a 0-effect typed-prim call needs no `!{}` annotation and must check clean");
    let env = penv.link().expect("phylum links");
    let node = elaborate(&env, "main").expect("a checked typed-prim call must elaborate");
    match &node {
        Node::Op { prim, args } => {
            assert_eq!(
                prim, "prim:std.io.serialize.to_json",
                "must dispatch under the disjoint `prim:` namespace, qualified by the \
                 registered PrimSig.name — never `wild:`"
            );
            assert_eq!(args.len(), 1, "arity must be preserved through elaboration");
        }
        other => panic!("expected Node::Op{{prim:\"prim:…\"}}, got {other:?}"),
    }
}

/// Same fixture, but `@std-sys` is explicitly OMITTED from the nodule header — a typed-prim call
/// must never require the `wild` FFI-floor context gate (it is never routed through `Expr::Wild`).
#[test]
fn typed_prim_call_needs_no_std_sys_nodule_header() {
    let prims = prims_with("std_io", "serialize.to_json", to_json_sig());
    // No `@std-sys` on the nodule header — would be mandatory for `wild`, never for a typed prim.
    let src = "phylum p\nnodule demo;\nuse std_io::serialize.to_json;\n\
               fn main() => Bytes = to_json(0b0010_1010);";
    check_phylum_with_deps_and_prims(&phy(src), &Phyla::default(), &prims)
        .expect("a typed-prim call must check clean with no `@std-sys` nodule header");
}

// ---------------------------------------------------------------------------------------------
// (b) A wrong-arity or wrong-`Ty` call at a typed-prim site is a `CheckError`, not a runtime
//     surprise — the structural, no-coercion verification this package's deliverable IS.
// ---------------------------------------------------------------------------------------------

#[test]
fn typed_prim_wrong_arity_is_a_check_error() {
    let prims = prims_with("std_io", "serialize.to_json", to_json_sig());
    let src = "phylum p\nnodule demo;\nuse std_io::serialize.to_json;\n\
               fn main() => Bytes = to_json(0b0010_1010, 0b0000_0001);";
    let err = check_err(src, &Phyla::default(), &prims);
    assert!(
        err.message.contains("takes 1 argument"),
        "wrong-arity typed-prim call must name the expected arity: {}",
        err.message
    );
}

#[test]
fn typed_prim_wrong_argument_ty_is_a_check_error_no_coercion() {
    let prims = prims_with("std_io", "serialize.to_json", to_json_sig());
    // The signature wants `Binary{8}`; `0x00` is `Bytes` (RFC-0032 D4) — a structural mismatch,
    // never silently coerced (this is the "ascription-on-faith" behavior this package replaces).
    let src = "phylum p\nnodule demo;\nuse std_io::serialize.to_json;\n\
               fn main() => Bytes = to_json(0x00);";
    let err = check_err(src, &Phyla::default(), &prims);
    assert!(
        err.message.contains("Binary") && err.message.contains("Bytes"),
        "wrong-Ty typed-prim argument must name both the expected and actual type: {}",
        err.message
    );
}

// ---------------------------------------------------------------------------------------------
// (c) An effectful typed prim (`effects:["net"]`) called without `!{net}` is refused by effect
//     coverage exactly like an undeclared `ffi` call today — and the effect name comes from the
//     registered `PrimSig`, never hardcoded (a caller declaring `!{ffi}` instead is ALSO refused).
// ---------------------------------------------------------------------------------------------

#[test]
fn typed_prim_effectful_call_without_declared_effect_is_refused() {
    let prims = prims_with("std_net", "http.http_request", http_request_sig());
    let src = "phylum p\nnodule demo;\nuse std_net::http.http_request;\n\
               fn main() => Bytes = http_request(0x00);";
    let err = check_err(src, &Phyla::default(), &prims);
    assert!(
        err.message.contains("net") && err.message.contains("does not declare it"),
        "an undeclared typed-prim effect must be refused, naming the missing effect: {}",
        err.message
    );
}

#[test]
fn typed_prim_effectful_call_declaring_ffi_instead_of_net_is_still_refused() {
    let prims = prims_with("std_net", "http.http_request", http_request_sig());
    // Declares `!{ffi}` (the effect `wild` would need) instead of the PrimSig's own `net` —
    // proves the effect name is taken from the registered signature, not hardcoded to `ffi`.
    let src = "phylum p\nnodule demo;\nuse std_net::http.http_request;\n\
               fn main() => Bytes !{ffi} = http_request(0x00);";
    let err = check_err(src, &Phyla::default(), &prims);
    assert!(
        err.message.contains("net"),
        "declaring the WRONG effect must still refuse, naming the real one: {}",
        err.message
    );
}

#[test]
fn typed_prim_effectful_call_with_the_declared_effect_checks_clean() {
    let prims = prims_with("std_net", "http.http_request", http_request_sig());
    let src = "phylum p\nnodule demo;\nuse std_net::http.http_request;\n\
               fn main() => Bytes !{net} = http_request(0x00);";
    check_phylum_with_deps_and_prims(&phy(src), &Phyla::default(), &prims)
        .expect("declaring the prim's own registered effect must check clean");
}

// ---------------------------------------------------------------------------------------------
// Ambiguous dependency-name registration (adversarial checklist item): a `dep` present in BOTH
// `Phyla` and `TypedPrimEnv` is refused as ambiguous, never a silent preference for one.
// ---------------------------------------------------------------------------------------------

#[test]
fn dep_registered_in_both_phyla_and_typed_prim_env_is_refused_as_ambiguous() {
    let dep = resolved(
        "phylum d\nnodule math;\npub fn add1(x: Binary{8}) => Binary{8} = x;",
        1,
    );
    let mut deps_map = BTreeMap::new();
    deps_map.insert("dual".to_owned(), dep);
    let phyla = Phyla::from_deps(deps_map);
    let prims = prims_with("dual", "math.add1", to_json_sig());

    let src = "phylum p\nnodule demo;\nuse dual::math.add1;\n\
               fn main() => Binary{8} = add1(0b0000_0001);";
    let err = check_err(src, &phyla, &prims);
    assert!(
        err.message.to_lowercase().contains("ambiguous"),
        "a dep registered in both Phyla and TypedPrimEnv must be refused as ambiguous, never a \
         silent preference for one: {}",
        err.message
    );
}

/// The neither-registered case stays a "no such dependency" refusal (distinctly worded from an
/// ordinary `.myc` "no such name" miss, and now honestly naming BOTH doors).
#[test]
fn dep_registered_in_neither_phyla_nor_typed_prim_env_is_no_such_dependency() {
    let src = "phylum p\nnodule demo;\nuse nobody::math.add1;\n\
               fn main() => Binary{8} = add1(0b0000_0001);";
    let err = check_err(src, &Phyla::default(), &TypedPrimEnv::default());
    assert!(
        err.message.contains("no such dependency"),
        "an unregistered dep must be the distinct 'no such dependency' refusal: {}",
        err.message
    );
}

// ---------------------------------------------------------------------------------------------
// Regression criterion (S-TYPED-PRIM-ENV freeze contract): `TypedPrimEnv::default()` must be
// byte-identical in behavior to today's `check_phylum_with_deps` — proved here by Debug-string
// equality over a real cross-phylum fixture (deterministic: every collection is a `BTreeMap`).
// ---------------------------------------------------------------------------------------------

#[test]
fn typed_prim_env_default_is_byte_identical_to_check_phylum_with_deps() {
    let dep = resolved(
        "phylum d\nnodule math;\npub fn add1(x: Binary{8}) => Binary{8} = x;",
        2,
    );
    let mut deps_map = BTreeMap::new();
    deps_map.insert("collections".to_owned(), dep);
    let phyla = Phyla::from_deps(deps_map);
    let src = "phylum p\nnodule use_it;\nuse collections::math.add1;\n\
               pub fn go(y: Binary{8}) => Binary{8} = add1(y);";

    let baseline =
        check_phylum_with_deps(&phy(src), &phyla).expect("pre-PKG-LINKAGE baseline checks");
    let with_default_prims =
        check_phylum_with_deps_and_prims(&phy(src), &phyla, &TypedPrimEnv::default())
            .expect("the additive entry point with an empty TypedPrimEnv must also check");
    assert_eq!(
        format!("{baseline:?}"),
        format!("{with_default_prims:?}"),
        "TypedPrimEnv::default() must be byte-identical to check_phylum_with_deps (the \
         S-TYPED-PRIM-ENV regression criterion)"
    );

    // And a phylum with NO cross-phylum `use` at all is unaffected too (the plain-`check_phylum`
    // byte-identity chain: check_phylum_with_deps_and_prims -> check_phylum_with_deps ->
    // check_phylum, all with Phyla::default()/TypedPrimEnv::default()).
    let solo = "phylum s\nnodule only;\npub fn id(x: Binary{8}) => Binary{8} = x;";
    let a = check_phylum_with_deps(&phy(solo), &Phyla::default()).expect("solo phylum checks");
    let b =
        check_phylum_with_deps_and_prims(&phy(solo), &Phyla::default(), &TypedPrimEnv::default())
            .expect("solo phylum checks under the new entry point too");
    assert_eq!(format!("{a:?}"), format!("{b:?}"));
}
