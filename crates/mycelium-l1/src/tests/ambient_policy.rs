//! Unit tests for the `policy: ambient` scoped resolution (DN-142 §3.2; `crate::ambient_policy`).

use crate::ambient_policy::*;
use crate::ast::Path;

fn path(name: &str) -> Path {
    Path(vec![name.to_owned()])
}

#[test]
fn nodule_declaration_resolves_with_declared_nodule_origin() {
    let decls = [PolicyDecl {
        scope: PolicyScope::Nodule,
        policy: path("rt"),
    }];
    let resolved = resolve_policy(&decls, None).expect("a nodule declaration resolves");
    assert_eq!(resolved.policy, path("rt"));
    assert_eq!(resolved.origin, PolicyOrigin::Declared(PolicyScope::Nodule));
    assert_eq!(explain_origin(&resolved), "policy: rt  [declared@nodule]");
}

#[test]
fn most_specific_wins_nodule_over_phylum() {
    // Mirrors `mycelium_proj::cert_scope::resolve_mode`'s precedence fold: the most-specific
    // declared scope wins, regardless of input order.
    let decls = [
        PolicyDecl {
            scope: PolicyScope::Phylum,
            policy: path("phylum_policy"),
        },
        PolicyDecl {
            scope: PolicyScope::Nodule,
            policy: path("nodule_policy"),
        },
    ];
    let resolved = resolve_policy(&decls, None).expect("resolves");
    assert_eq!(resolved.policy, path("nodule_policy"));
    assert_eq!(resolved.origin, PolicyOrigin::Declared(PolicyScope::Nodule));

    // Order-independence: the same result regardless of declaration order (a pure max-by-key fold,
    // not "last one wins").
    let decls_reordered = [decls[1].clone(), decls[0].clone()];
    let resolved2 = resolve_policy(&decls_reordered, None).expect("resolves");
    assert_eq!(resolved2, resolved);
}

#[test]
fn most_specific_wins_phylum_over_global() {
    let decls = [
        PolicyDecl {
            scope: PolicyScope::Global,
            policy: path("global_policy"),
        },
        PolicyDecl {
            scope: PolicyScope::Phylum,
            policy: path("phylum_policy"),
        },
    ];
    let resolved = resolve_policy(&decls, None).expect("resolves");
    assert_eq!(resolved.policy, path("phylum_policy"));
    assert_eq!(resolved.origin, PolicyOrigin::Declared(PolicyScope::Phylum));
    assert_eq!(
        explain_origin(&resolved),
        "policy: phylum_policy  [declared@phylum]"
    );
}

#[test]
fn no_declaration_falls_through_to_the_catalog() {
    let resolved = resolve_policy(&[], Some("rt")).expect("catalog default resolves");
    assert_eq!(resolved.policy, path("rt"));
    assert_eq!(resolved.origin, PolicyOrigin::Catalog);
    assert_eq!(explain_origin(&resolved), "policy: rt  [catalog]");
}

#[test]
fn a_declaration_takes_precedence_over_the_catalog_default() {
    let decls = [PolicyDecl {
        scope: PolicyScope::Nodule,
        policy: path("nodule_policy"),
    }];
    let resolved = resolve_policy(&decls, Some("rt")).expect("resolves");
    assert_eq!(resolved.policy, path("nodule_policy"));
    assert_eq!(resolved.origin, PolicyOrigin::Declared(PolicyScope::Nodule));
}

#[test]
fn no_declaration_and_no_catalog_default_is_a_hard_unresolved_error() {
    let err = resolve_policy(&[], None).expect_err("neither a decl nor a catalog default exists");
    let msg = err.to_string();
    assert!(
        msg.contains("no ambient policy declared for this pair in scope"),
        "got: {msg}"
    );
    assert!(
        msg.contains("no implicit fallback") && msg.contains("never-silent"),
        "must be explicit about no fallback — got: {msg}"
    );
}

#[test]
fn policy_scope_specificity_is_least_to_most_specific() {
    assert!(PolicyScope::Global.specificity() < PolicyScope::Phylum.specificity());
    assert!(PolicyScope::Phylum.specificity() < PolicyScope::Nodule.specificity());
    assert_eq!(PolicyScope::ALL.len(), 3);
}
