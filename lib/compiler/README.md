# `lib/compiler/` — the self-hosted L1 frontend (Mycelium-in-Mycelium)

> **Status:** M-740 wave scaffold (2026-07-03). This phylum is the `.myc` port of the Rust L1
> frontend (`crates/mycelium-l1/src/`), per **DN-26** (bootstrap plan) and the maintainer's
> **DN-26 §9** flag decisions. The Rust frontend stays the **trusted differential oracle** until
> **M-741** ratifies the port canonical — nothing here overwrites `crates/mycelium-l1/src/`.

## Phylum layout (DN-26 §9 flag-1: the `compiler` phylum, SCC as one nodule)

`lib/compiler/` is a **phylum** (RFC-0006 §4.3). Nodules:

| Nodule | Ports (Rust) | Role | Stage |
|---|---|---|---|
| `compiler.token` | `token.rs`, `error.rs` | token kinds + lex errors (the small `token↔error` cycle) | 1 |
| `compiler.lex` | `lexer.rs` | source text → token stream | 1 |
| `compiler.nodule_header` | `nodule.rs` | `// nodule:` header parse (standalone) — DN-26 §7.3 named it `compiler.nodule`, which is unspellable (`nodule` is a reserved word; FLAG-nodule-5) | 2 |
| `compiler.ast` | `ast.rs` | surface AST data types (pure, no upward deps) | 3 |
| `compiler.parse` | `parse.rs` | token stream → AST / phylum | 3 |
| `compiler.ambient` | `ambient.rs` | ambient-representation resolution (leaf dep of the SCC) | 4 |
| `compiler.totality` | `totality.rs` | totality walk (leaf dep) | 4 |
| `compiler.substrate` | `substrate.rs` | substrate release events (leaf dep) | 4 |
| **`compiler.semcore`** | `checkty.rs` · `elab.rs` · `eval.rs` · `mono.rs` · `fuse.rs` · `decision.rs` · `usefulness.rs` · `grade.rs` · `affine.rs` | **the semantic-core SCC — one nodule** (nodule-wide `FixGroup` mutual recursion, DN-14 row 3) | 5 |

The **semantic core is one nodule** because those nine Rust modules form a single strongly-connected
component (they call each other cyclically — DN-26 §7.1); a single nodule gives them nodule-wide
mutual recursion for free. The leaves (`ambient`/`totality`/`substrate`) and the front stages
(`token`/`lex`/`nodule`/`ast`/`parse`) are **sibling nodules** exporting across nodule boundaries with
`pub` + cross-nodule `use` (DN-14 row 10).

## Frontend / kernel boundary (KC-3)

This phylum is `source text → closed L0`. The **L0 kernel stays Rust** (`mycelium-core`/`interp`/
`cert`/`select`) — it is **not** ported here (KC-3). The self-hosted frontend reaches L0 construction
and the prim registry through the `@std-sys` + `wild` FFI seam (DN-14 row 9, executes; RFC-0028). A
frontend port step that *appears* to need a `mycelium-core` change is a **FLAG-up**, not an in-wave
core edit.

## Verification per stage (DN-26 §7.3 + §9 flag-2)

Each stage lands as a **separate green-`just check` commit** with a **differential** against the Rust
oracle over the L1 conformance corpus (`docs/spec/grammar/conformance/accept|reject/`):

- **Stages 1–5:** `Rust-host ≡ self-host` on the same output for the corpus, graded **`Empirical`**
  (differential agreement across trials — never upgraded to `Proven`, VR-5).
- **Stage 6 (bootstrap gate, M-742):** per **DN-26 §9 flag-2** — **validate on the interpreted `myc`
  first**, then **AOT-compile the same `.myc` and validate that build too**. Both runtimes run the
  identical source and must agree: the stage-2 three-way `Rust-host ≡ self-host-interpreted ≡
  self-host-AOT`. The interpreted pass is the gate; the AOT pass is the never-skipped follow-on (G2).

Differential harnesses live in `crates/mycelium-l1/tests/` (the established `std_*.rs` pattern),
reading both the Rust output and the self-hosted output for the same input.

## Honesty / status discipline

- Nothing here is pre-declared done. Each stage's differential is `Empirical` **only after trials
  run** (VR-5). DN-26 stays **Draft** until **M-741** ratifies the full-toolchain gate.
- The full-language 1.0.0 capstone criterion is **never pre-declared** — this is the
  comprehensive-dogfooding track (ADR-036) that gates the *public-release* milestone, not the
  `lang 1.0.0` tag.

## Wave progress

- [x] **Stage 1** — `compiler.token` + `compiler.lex` (token-stream differential). Landed
      (`lib/compiler/token.myc`, `lib/compiler/lex.myc`; gate: `crates/mycelium-l1/tests/compiler_stage1.rs`).
      `compiler.token`: the full `Tok`/`Pos`/`Spanned`/`keyword` port, all 64 reserved words
      classification-differentialed against the Rust oracle (`token::keyword`) 1:1. `compiler.lex`:
      the full lexer (trivia, all punctuation/operators, identifiers+keywords, `0b`/`0x`/`0t`
      literals, decimal `Int`, `"…"` strings) token-COUNT-differentialed against the Rust oracle
      over **every file in the accept-corpus** (27/27), plus per-token kind/content spot-checks.
      Two real checker findings were surfaced by this port (reported, not silently worked around;
      full detail in the test file): (1) a combined two-level nested match pattern (e.g.
      `Some(Scalar(SF16))`, or `Some(Sp(Ctor, _))`) panics `usefulness::useful_budgeted` when the
      outer type has `Tok`'s ~80 variants — worked around in every test via a split-match idiom,
      never hit by `lex`'s own logic (which only constructs `Tok`, never destructures it); (2)
      `mycelium_interp::Interpreter::eval_core` (the L0 substitution interpreter) does not return
      within minutes for a `lex.myc`-scale elaborated program even though L1-eval finishes in
      well under a second, so the Stage-1 differential compares the **L1-eval** leg only (still a
      complete "Rust-lexer ≡ self-hosted-lexer" comparison; the L0-interp/AOT cross-check used by
      `std_*.rs`'s three-way harness is not currently feasible at this scale). Deliberate, flagged
      scope narrowings vs. the Rust oracle: no float-literal scanning (none in the accept-corpus),
      ASCII-only whitespace, `Int`/literal payloads carry verbatim `Bytes` rather than an eagerly
      converted value (mirrors the Rust lexer's own deferred-conversion precedent for every OTHER
      literal kind). `compiler.token`/`compiler.lex` are mutually self-contained (each redeclares
      the shared types) rather than cross-nodule `use`, because cross-nodule EXECUTION (not just
      type-checking) is still staged in `checkty.rs`'s `check_phylum` — a real, separate finding
      from this leaf, reported upstream for M-741/a future stage to lift.
- [x] **Stage 2** — `compiler.nodule_header` (header-parse differential). Landed
      (`lib/compiler/nodule.myc`; gate: `crates/mycelium-l1/tests/compiler_stage2.rs`). The full
      `nodule.rs` port: `parse_nodule_header` (first-non-blank-line scan, blank-line skipping with
      1-based line tracking), the `//`-comment / bare-`nodule` / `nodule:<dotted>` recogniser, the
      never-silent ill-formed-name errors (empty name, empty segment, non-identifier segment — G2),
      and the `dotted`/`canonical` accessors. Differential vs the live Rust oracle: a 4-way
      classification code (none/bare/named/error) plus the joined dotted name and `canonical`
      spelling (named case) plus the 1-based error line (error case), over a 26-case synthetic edge
      battery transcribed from the oracle's own unit tests AND every real `.myc` file in the
      conformance corpus (accept **and** reject) and `lib/std/` + `lib/compiler/` (66+ files). One
      THREE-WAY run (L1 ≡ L0-interp ≡ AOT) is kept at this stage's small scale; the per-file sweep
      is L1-eval-only (M-981, as in Stage 1). Honest narrowings (flagged in-file): ASCII-only trim
      vs Rust's Unicode `str::trim` (FLAG-nodule-2 — a real classification divergence: a
      non-ASCII-whitespace-only leading line hides a later marker from the port; PINNED as a
      known-divergence test in the gate, per the PR #1165 review finding); static error messages,
      line fidelity kept (FLAG-nodule-3). **One real finding: the DN-26 §7.3 nodule name
      `compiler.nodule` is unspellable** — `nodule` is a reserved word, so the surface declaration
      `nodule compiler.nodule;` cannot parse (the FLAG-token-3 keyword-collision class at the
      nodule-NAME level); renamed `compiler.nodule_header` (FLAG-nodule-5, reported up for DN-26's
      append-only changelog). Every source-length-bounded recursion is direct-tail (the RFC-0041
      §7 W7 amendment-11 TCO acceptance criterion); the non-tail recursions are bounded by a
      name's segment count, never by source length.
- [x] **Stage 3** — `compiler.ast` + `compiler.parse` (AST differential + full conformance corpus).
      Landed (`lib/compiler/ast.myc`, `lib/compiler/parse.myc`; gates:
      `crates/mycelium-l1/tests/compiler_stage3_ast.rs` 26/26 +
      `crates/mycelium-l1/tests/compiler_stage3.rs` 4/4). `compiler.ast`: the full `ast.rs`
      vocabulary — 36 types / 102 constructors + helper impls, FLAG-ast-1..8 (incl. FLAG-ast-5,
      the flat per-nodule constructor namespace: variant names reused across different enums
      collide even when not keywords — per-type prefixes, `collections.myc` precedent).
      `compiler.parse`: all ~91 `parse.rs` functions accounted for, **both `parse` and
      `parse_phylum`** end-to-end (source text → AST; self-contained token+lexer+AST copy per
      M-982, FLAG-parse-1); every match one constructor level deep (M-980 — zero checker panics);
      `MAX_EXPR_DEPTH`=4096 preserved; source-length-bounded list-building loops re-shaped to
      accumulator+reverse direct-tail in the PR #1166 review cycle after a Cons-after-return
      depth-ceiling finding (RFC-0041 §7 W7 amendment 11; the Stage-1 lexer's own twin is
      flagged as M-985, not silently carried). **Honest limit:** the depth benefit of that
      shape is dormant — the evaluator's TCO elides only bare-body self-calls (match/let tail
      calls never elided, M-986), so no in-language loop exceeds the 4096 depth budget today;
      L1-eval cost is also ~n³ in token count (M-987). Both pinned loudly in the gate.
      Differential: classification parity with the Rust oracle over the full
      corpus on both legs (accept 27/27, reject 30/30, zero divergences) + a preorder
      per-constructor-tag fingerprint (tags 1–109, `rotl(7)`-XOR, node count, leaf mixing;
      hand-locked Rust mirror) on every accepted leg + a 6-file real-stdlib subset leg (full-tree
      sweep → M-984). Harness: args-in/verdict-out — ONE elaboration, one `Evaluator::call` per
      file/leg (~8× cheaper than per-driver programs; Stage-1/2 retrofit → M-983). New finding
      FLAG-parse-2: lexer-keyword-ctor × AST-ctor flat-namespace collision (31 names) whenever
      two frontend stages share a nodule — bears on Stage-5 semcore packaging. L1-eval leg only
      (M-981); message/position fidelity not compared (FLAG-parse-8); lib-leg fuel sized to 200M
      (default 1M — flagged, maintainer call).
- [x] **Stage 4** — `compiler.substrate` + `compiler.totality` + `compiler.ambient` (leaf differentials).
      Landed (`lib/compiler/substrate.myc`, `totality.myc`, `ambient.myc`; gates
      `crates/mycelium-l1/tests/compiler_stage4_substrate.rs` 5/5, `_totality.rs` 6/6,
      `_ambient.rs` 4/4). All three are SCC dependency leaves (depend only on `ast`, or nothing).
      **Native-toolchain vet:** `myc check` (the real `mycelium-check` binary) reports `ok` on all
      three nodules — a second, independent witness alongside the Rust differential.
      `compiler.substrate` (DN-71 Model S): the deterministic surface of the affine handle
      (provenance / `explain` / `ReleaseEvent` / `SubstrateError` / a threaded-`id` acquire /
      value-threaded consume-once); **FLAG-substrate-1** is the honest limit — the Rust
      `Arc<AtomicBool>` cross-alias consume-once backstop is *not representable* in a pure-value
      port (it enforces use-once only along one threaded value, not across aliases), documented not
      faked; a hand-written `itoa` fills the still-absent decimal-format prim (ast.myc FLAG-ast-7).
      `compiler.totality` (RFC-0007 Foetus checker + the shared `walk_expr`): `classify_all`
      Total/Partial over synthetic `FnDecl` sets; FLAG-totality-1 `BTreeMap`/`BTreeSet`→sorted
      assoc-list (deterministic-order precondition), -2 the `&mut impl FnMut` traversals specialized
      (no HOF), -3 the 4096 `depth` budget standing in for `with_deep_stack`, -4 `Pattern::Or`'s
      `panic!` invariant→dead `Ok` fallback. `compiler.ambient` (RFC-0012 resolution +
      pretty-printer): `resolve`/`resolve_report`/`expand_to_source`/`expand_phylum_to_source`,
      `MAX_AMBIENT_DEPTH`=4096, the two mirror wide-enum traversals; **FLAG-ambient-6** scopes the
      differential honestly — 8 hand-built synthetic nodules (paradigm fills, nested override,
      object bodies, mixed bodies) + 4 refusal fixtures, byte-for-byte `expand_to_source` parity +
      AST-fingerprint on accepts, but **zero raw corpus files**: this is structural, not the M-987
      wall — `compiler.ambient` consumes an already-parsed `Nodule` and cannot reach
      `compiler.parse` (cross-nodule execution staged), so a source *file* can't be fed without an
      AST-serializer bridge (deferred, flagged). Differentials graded `Empirical`.
- [ ] **Stage 5** — `compiler.semcore` (L0-output differential; `cargo-mutants` witness).
      **Increment 1 landed** (`lib/compiler/semcore.myc`, partial; gate
      `crates/mycelium-l1/src/tests/compiler_stage5_semcore.rs` 17/17): the tractable sub-core —
      the `Ty`/`Width`/`DataInfo`/`CtorInfo`/`Pat` type vocabulary (data only) + the Maranget
      `usefulness`+`decision` pipeline + `affine` + `grade` (all four depend on checkty's *types*,
      not its logic or the evaluator). Native `myc check` reports `ok`. **The differential is a true
      live-oracle test** — an **in-crate** unit module (per the CLAUDE.md test-layout rule) with
      white-box access to the live Rust `usefulness`/`decision`/`affine`/`grade`, so each synthetic
      case is compared against the *actual oracle*, not a hand-derived expectation (this closed the
      first-cut FLAG-semcore-10 gap; the sole residual, **FLAG-semcore-10-b**, is that grade's exact
      `Strength` is recovered by probing the four-level lattice through the live `check_guarantees`,
      whose finer internals are private even in-crate). Flat-namespace prefixing `Ty-`/`Wd-`/`Mp-`/
      `Hd-` (FLAG-ast-5/FLAG-parse-2 discipline). **Deferred (feasibility-gated on M-986/M-987, not
      silently narrowed):** the heavy entangled core `checkty`/`elab`/`eval`/`mono` + `fuse` (which
      *runs* the evaluator) and the whole-program L0-output differential + `cargo-mutants` witness —
      a self-hosted checker/elaborator run inside the L1 evaluator over a whole program almost
      certainly can't complete under the current kernel; the lift (widen kernel TCO vs. reduce eval
      cost vs. lean on AOT) is a maintainer decision recorded in DN-26, not decided in-wave.

      **This entry is stale past increment 1 (flagged, not silently left wrong; mitigation #14).**
      `semcore.myc`/`compiler_stage5_semcore.rs`'s own headers + `git log -- lib/compiler/semcore.myc`
      show increments 2–7 (M-1007…M-1012: checkty's pure type-algebra leaves, unify/resolve_ty/tuple
      helpers, mono's name-mangling + free-var/binder analysis, checkty's literal/pattern typing,
      elab's L0 mirror + pure lowering helpers) and M-1013 STEP 3 (checkty's *registration* half of
      increment 8 — `register_types`/`register_traits`/`register_instances`, gate
      `crates/mycelium-l1/src/tests/compiler_stage5_register.rs`) already landed on `dev` without this
      wave-progress note being updated to match. **M-1013 STEP 4 (this change)** adds the
      *resolution* half of increment 8 — `resolve_imports` + its six helpers (`qualify`,
      `exports_has_pub`, `direct_child`, `split_last_seg`, `insert_export`, `remove_import`) and the
      `Exports`/`NoduleImports`/`UsePath` mirrors — gated by 9 new live-oracle cases in
      `compiler_stage5_register.rs` (explicit import ok/unknown/private/duplicate/unqualified-path,
      glob pub-only pull, glob-vs-glob ambiguity, explicit-shadows-glob, plus a
      `marshal_discriminates` non-vacuity case). `Item` gained an `ItUse(UsePath)` variant (previously
      folded into the tuple-free `ItOther`) so `resolve_imports` can read `use` items directly;
      `collect_tuple_arities_item`'s `ItUse(_) => acc` arm keeps the M-826 tuple pre-pass unaffected
      (`Use` carries no tuple-relevant content, matching the oracle). `register_nodule_decls`
      (checkty.rs 1340-1401, increment 8's remaining caller) is **not** ported — it seeds the built-in
      `Fuse` trait, entangling with the still-deferred `fuse.rs` (FLAG, not silently worked around).
      Native `myc check` reports `ok`; `pub(crate)` widened on `resolve_imports`/`Exports`/
      `NoduleImports` (zero logic change, the M-1013 STEP 3 precedent). **FLAG-semcore-34:** the
      differential leaves `Exports.fns`/`NoduleImports.fns` empty in every fixture (no `decode_expr`
      exists yet to marshal an arbitrary returned `FnDecl` body) — `insert_export`'s fn-branch is
      structurally identical to its type/trait branches, so this is a low-risk, explicitly flagged
      narrowing, not a silent one. A full increment 2–8 reconciliation of this wave-progress note is
      still owed (out of this change's scope — flagged up, not attempted here).

      **M-1013 checkty PR-2** ports two PURE `checkty.rs` classifiers into `semcore.myc`:
      `paradigm_name` (checkty.rs 7175-7197 — the swap-paradigm name of a representation type; all 11
      `Ty` arms enumerated, no wildcard) and `cons_list_ctors` (checkty.rs 3592-3624 — the two-ctor
      linked-list recognizer) with its `cons_list_scan` fold, gated by
      `crates/mycelium-l1/src/tests/compiler_stage5_classify.rs` (5 tests: all 11 `paradigm_name` arms;
      11 `cons_list_ctors` shapes including the one-field / three-plus-field scan paths and the
      no-nullary `(None, Some)` / `(None, None)` finals; two `marshal_discriminates` non-vacuity twins).
      No new FLAG (the `&'static str`→`Bytes` idiom and the FLAG-semcore-4 `Vec[DataInfo]` `BTreeMap`
      stand-in); both oracles `pub(crate)`-widened, zero logic change; native `myc check` reports `ok`.
      (STEP 5/6 and eval PR-1 also landed on `dev` between STEP 4 and this note; the full increment
      2–8+ reconciliation of this wave-progress note remains owed — flagged up, not attempted here.)

      **M-1013 checkty PR-3** ports `checkty.rs`'s `subst_type_param_in_typeref` (the DN-54 §10 Model-A
      rule-instantiation substitution, M-973) into `semcore.myc`: a bare nullary `Named(param, [])`
      becomes the concrete type's base with the `tr.guarantee.or(concrete.guarantee)` first-Some merge
      (`strength_or`); the structural forms recurse; the eight atoms clone verbatim. A complete
      wildcard-free 12-arm `BaseType` match (G2), unbudgeted like the `subst_ty` precedent. No new FLAG
      (`BaseType` is a field-for-field mirror; the `name == param && args.is_empty()` guard is expressed
      one level at a time; the arg-list recursion reuses the FLAG-semcore-5 direct-map idiom). Oracle
      `pub(crate)`-widened, zero logic change. Gated by the extended
      `crates/mycelium-l1/src/tests/compiler_stage5_tyref.rs` (now 11 tests): 19
      `subst_type_param_in_typeref_cases` (every `BaseType` arm; the four guarantee-merge corners; the
      guard's negative corners; nested-guarantee preservation) plus a `subst_marshal_discriminates`
      non-vacuity twin — the first Stage-5 differential to marshal a guarantee-bearing `TypeRef` on the
      input side (a guarantee-threading `enc_tr` encoder; the shared `encode_typeref` discards the
      slot). Native `myc check` reports `ok`. Unlocks the `subst_type_param_in_{sig,expr,impl}` family.
- [ ] **Stage 6 / M-742** — `just bootstrap`: interpreted-first then AOT, stage-2 three-way

*This README is the M-740 wave map; it is updated as each stage lands. Grounded in DN-26 §7/§9,
DN-14, RFC-0028, KC-3.*
