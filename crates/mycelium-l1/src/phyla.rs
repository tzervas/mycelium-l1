//! **DN-113 Rank 1 / M-1060 — the multi-phylum dependency-graph builder.** The acyclicity-enforcing
//! layer that sits *above* the single-phylum resolution mechanism in [`crate::checkty`] (`Phyla` /
//! `ResolvedPhylum` / `check_phylum_with_deps`): given a **named graph** of phyla and their declared
//! `[dependencies]` edges, resolve every node bottom-up into a checked, linked
//! [`crate::checkty::ResolvedPhylum`] — refusing a cyclic graph **before** checking anything
//! (DN-113 §9.3: content-addressing forbids a phylum from transitively depending on itself by
//! construction; a cycle is a never-silent refusal naming the offending path, never a partial or
//! best-effort resolution — G2).
//!
//! **Scope (v1 — DN-113 §5.2/§8):** this module is purely an **in-memory graph orchestrator** — it
//! takes an already-assembled `BTreeMap<String, PhylumNode>` (each node an already-parsed
//! [`Phylum`] AST + its content-address pin + its own `[dependencies]` edges) and resolves it. It
//! does **not** itself load a dependency's source from disk, fetch a registry artifact, or verify a
//! resolved tree's hash against a manifest pin (DN-113's B2 "verified source tree" loading model) —
//! that is the manifest/loader's job (`mycelium-proj`/`mycelium-cli` territory), out of this crate's
//! scope. A caller (the future loader) assembles the graph from its own resolved sources and calls
//! [`build_phyla_graph`] once per compilation.

use std::collections::BTreeMap;

use crate::ast::Phylum;
use crate::checkty::{
    check_phylum_matured_with_deps_and_exports, CheckError, Phyla, PhylumEnv, ResolvedPhylum,
};
use mycelium_core::ContentHash;

/// One phylum's node in a multi-phylum dependency graph (DN-113 §5.1/§9.3) — the input to
/// [`build_phyla_graph`]. `deps` maps THIS phylum's own `[dependencies]`-**local** name to the graph
/// key (in the same `BTreeMap<String, PhylumNode>`) of the phylum it resolves to — the graph-level
/// analogue of a manifest's `Dependency { name, phylum, hash, .. }` entries, already resolved to a
/// concrete graph node (loading/lookup is the caller's job, per this module's doc comment).
#[derive(Debug, Clone)]
pub struct PhylumNode {
    /// The content-addressed pin (ADR-003) this node's `phylum` AST resolved to.
    pub phylum_hash: ContentHash,
    /// The parsed (not yet checked) phylum.
    pub phylum: Phylum,
    /// `[dependencies]`-local name → the graph key (in the enclosing `BTreeMap`) of the depended-on
    /// phylum. Every value MUST be a key present in the same graph map passed to
    /// [`build_phyla_graph`] — an absent one is refused never-silently (DN-113 §9.5), not treated as
    /// "no dependencies".
    pub deps: BTreeMap<String, String>,
}

/// Build every phylum in `graph`, bottom-up, resolving each node's [`Phyla`] from its already-
/// resolved dependency nodes (DN-113 §5.1/§7/§9.3) — the layer over
/// [`check_phylum_matured_with_deps_and_exports`] (which itself layers over the canonical
/// [`crate::checkty::PhylumEnv::link`], DRY throughout).
///
/// Detects a dependency cycle **before** checking anything — a DFS-based topological sort that marks
/// each node `Visiting`/`Done`; hitting an already-`Visiting` node closes a cycle, refused
/// never-silently with the exact path (DN-113 §9.3 — content-addressing forbids a cycle by
/// construction: computing `A`'s hash would require `B`'s, which would require `A`'s). An edge whose
/// target is not a key of `graph` is refused the same way (DN-113 §9.5 — an "unknown dependency" is
/// a *graph-construction* error here, distinct from the *check-time* "no such dependency in
/// `[dependencies]`" [`crate::checkty::resolve_imports`] raises for a `use` that never got this far).
///
/// Returns one `(PhylumEnv, Phyla)` pair per graph node, keyed identically to `graph` — the checked
/// per-nodule environments plus the resolved dependency set that produced them (so a caller can, for
/// example, re-derive the DN-113 §6 `(phylum_hash, qualified_name)` def-site ref for anything the
/// checked phylum references).
///
/// # Errors
/// A never-silent [`CheckError`] on: a cyclic graph, an edge naming an absent graph node, or any
/// ordinary check-time refusal from resolving/checking a node (propagated verbatim).
pub fn build_phyla_graph(
    graph: &BTreeMap<String, PhylumNode>,
) -> Result<BTreeMap<String, (PhylumEnv, Phyla)>, CheckError> {
    let order = topo_order(graph)?;
    let mut linked: BTreeMap<String, ResolvedPhylum> = BTreeMap::new();
    let mut out: BTreeMap<String, (PhylumEnv, Phyla)> = BTreeMap::new();

    for key in order {
        // `graph.get` cannot miss: `topo_order` only ever emits keys it walked from `graph` itself.
        let node = graph
            .get(&key)
            .expect("topo_order only emits keys present in `graph`");
        let mut deps: BTreeMap<String, ResolvedPhylum> = BTreeMap::new();
        for (local_name, target_key) in &node.deps {
            // `topo_order` already refused any edge whose target is absent from `graph`, and the
            // bottom-up order guarantees every dependency was resolved before its dependent — so
            // this lookup cannot miss either.
            let resolved = linked
                .get(target_key)
                .expect("topo_order guarantees a dependency is resolved before its dependent")
                .clone();
            deps.insert(local_name.clone(), resolved);
        }
        let phyla = Phyla::from_deps(deps);
        let (penv, exports) =
            check_phylum_matured_with_deps_and_exports(&node.phylum, &phyla, false)?;
        let env = penv.link()?;
        linked.insert(
            key.clone(),
            ResolvedPhylum {
                phylum_hash: node.phylum_hash.clone(),
                exports,
                env,
            },
        );
        out.insert(key.clone(), (penv, phyla));
    }
    Ok(out)
}

/// DFS-based topological sort with cycle detection over `graph`'s `deps` edges (DN-113 §9.3/§9.5).
/// Returns a valid bottom-up build order (every dependency before its dependent) or the first
/// never-silent refusal encountered (a cycle, or an edge to an absent node).
fn topo_order(graph: &BTreeMap<String, PhylumNode>) -> Result<Vec<String>, CheckError> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Mark {
        Visiting,
        Done,
    }

    fn visit(
        key: &str,
        graph: &BTreeMap<String, PhylumNode>,
        marks: &mut BTreeMap<String, Mark>,
        order: &mut Vec<String>,
        path: &mut Vec<String>,
    ) -> Result<(), CheckError> {
        match marks.get(key) {
            Some(Mark::Done) => return Ok(()),
            Some(Mark::Visiting) => {
                path.push(key.to_owned());
                let cycle = path.join(" -> ");
                return Err(CheckError::new(
                    key,
                    format!(
                        "cyclic phyla dependency graph: {cycle} — a content-addressed phylum \
                         cannot transitively depend on itself (a cycle would require each phylum's \
                         hash to already know the other's — DN-113 §9.3; refused, never a silent \
                         pick — G2)"
                    ),
                ));
            }
            None => {}
        }
        let Some(node) = graph.get(key) else {
            return Err(CheckError::new(
                key,
                format!(
                    "internal: phylum graph node `{key}` is referenced as a dependency target but \
                     not present in the graph (DN-113 §9.5 — never a silent skip; G2)"
                ),
            ));
        };
        marks.insert(key.to_owned(), Mark::Visiting);
        path.push(key.to_owned());
        // Deterministic order (BTreeMap iteration is already sorted by key) so a cycle's reported
        // path is stable across runs — `Empirical`, matches the codebase's ordered-iteration
        // precedent for other never-silent diagnostics (e.g. `expand_object_via_decls`'s `via`
        // ambiguity refusal).
        for target in node.deps.values() {
            if !graph.contains_key(target) {
                return Err(CheckError::new(
                    key,
                    format!(
                        "unknown dependency `{target}` — no such phylum in the graph (DN-113 §9.5; \
                         never a silent skip — G2)"
                    ),
                ));
            }
            visit(target, graph, marks, order, path)?;
        }
        path.pop();
        marks.insert(key.to_owned(), Mark::Done);
        order.push(key.to_owned());
        Ok(())
    }

    let mut marks: BTreeMap<String, Mark> = BTreeMap::new();
    let mut order = Vec::with_capacity(graph.len());
    let mut path: Vec<String> = Vec::new();
    for key in graph.keys() {
        visit(key, graph, &mut marks, &mut order, &mut path)?;
    }
    Ok(order)
}
