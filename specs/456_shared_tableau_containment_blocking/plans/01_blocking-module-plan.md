# Implementation Plan: Shared Tableau Containment-Blocking Module (Blocking.lean)

- **Task**: 456 - shared_tableau_containment_blocking
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: 574 (completed — settled the logic-specific side-condition shape)
- **Research Inputs**: reports/01_blocking-module-research.md (adversarially verified; three proof cores compiled green in research session)
- **Artifacts**: plans/01_blocking-module-plan.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/extensions/lean/context/contracts/reference-grounding.md (H3 lean4 Tier 1)
- **Type**: cslib

## Overview

Generalize the Sfor-containment / subset-blocking device recurring across tableau developments
into a single label-generic module `Cslib/Foundations/Logic/Tableau/Blocking.lean`. The module
carries exactly two layers: (a) a **definitional layer** — `Branch.typeAt`, `Branch.posTypeAt`,
`Branch.containmentBlocked` with spec lemmas — and (b) a **counting layer** — powerset-card
bound, eraseDups/toFinset bridge, the corrected `distinctTypes_le_pow`, a pigeonhole corollary,
and the GGN strict-chain bound `strictChain_le_card`. Side conditions stay logic-specific
(settled design). Temporal's `timeType`/`isSubsetBlocked` are redirected as defeq wrappers;
`references.bib` gains `DershowitzManna1979` and an enriched (never duplicated)
`GargGenoveseNegri2012`. Definition of done: all five phases green, zero sorry anywhere landed,
full CI gate set (mk_all barrel, checkInitImports, full build, lint-style, shake, lake test with
the 24 temporal conformance rows) passing.

**Downstream consumer**: task 317 (propositional tableau completeness) consumes
`Branch.posTypeAt` (the Sfor projection), `distinctTypes_le_pow`, and `strictChain_le_card`
next — the exponential bound is 317's only live world-bound route (its linear bound is refuted).
Nothing in this plan blocks on 317.

### Research Integration

- reports/01_blocking-module-research.md — module API (F3), corrected counting lemma (F2),
  dependency direction (F1), consumer map (F4), bib deliverable (F5), reuse check (F6). All
  load-bearing proof cores were compiled green via `lean_run_code` during research.

### Source-to-Implementation Mapping (H3 lean4 Tier 1, 5-column)

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|--------|---------------|-----------------|----------------|--------|
| Garg, Genovese & Negri 2012 | §III, Def. III.4, pp. 315-324 (web-verified quotes preserved in `specs/574_tableau_calculus_repair_ancestor_blocking/reports/01_phase6-blocker-resolution.md:93-94`; provenance-only citation — not in navigable corpus) | `Cslib.Logic.Tableau.Tableau.strictChain_le_card` | `∀ {β} [DecidableEq β] {k : Nat} (f : Nat → Finset β) (U : Finset β), (∀ i, i < k → f i ⊂ f (i+1)) → f k ⊆ U → k ≤ U.card` | pending (proof core compiled green in research session) |
| Garg, Genovese & Negri 2012 + Chagrov & Zakharyaschev 1997, Ch. 5 (FMP/filtration 2^n corroboration; CZ in corpus) | §III (distinct forced-sets ≤ 2^n) | `Cslib.Logic.Tableau.Tableau.distinctTypes_le_pow` | `(b.labels.toFinset.image fun l => (b.typeAt l).toFinset).card ≤ 2 ^ V.card` given `hV : ∀ sf ∈ b, (sf.sign, sf.formula) ∈ V` | pending (proof core compiled green in research session) |
| Massacci 2000 | Technique 8.1/8.2, Def. 8.2 (IN corpus: `sources/massacci_2000_single_step_tableaux_for_modal_logics`, chunks 0029-0031) | (scoping decision — per-obligation blocking is logic-specific, stays OUT of the generic module) | n/a | settled (574 D3/D4) |
| Fitting 1983, Ch. 4 | ancestor-directed loop check | (docstring provenance only in Blocking.lean References section) | n/a | pending |
| Dershowitz & Manna 1979 | CACM 22(8):465-476, doi 10.1145/359138.359142 | `references.bib` entry `DershowitzManna1979` | n/a | pending |

### Preserved Assets

The following work is complete and must not regress:

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| Settled 5-conjunct blocking shape `intFImpReuseWitnessAnc?` + spec | Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean:260-320 | [COMPLETED] (prior calculus-repair work) | 2026-07-28 (read-verified) |
| Temporal conformance corpus, 24 temporal rows | CslibTests/TableauConformance.lean | [COMPLETED] | 2026-07-28 (file present) |
| Tableau arithmetic extraction | Cslib/Foundations/Logic/Tableau/Measure.lean | [COMPLETED] | 2026-07-28 (file present) |
| `GargGenoveseNegri2012` bib entry | references.bib:228-234 | [COMPLETED] (enrich-only in Phase 4) | 2026-07-28 (grep-verified, key count 1) |

## Postmortem Constraints

Binding rules for all implementation dispatches. No prior failed attempts exist for this task;
rules derive from the adversarially-verified research report's refutations and risk factors.

**Do NOT**:
- State the counting lemma in the task-description form
  `(b.labels.map b.typeAt).eraseDups.length ≤ 2^U.length` — it is FALSE (research F2
  counterexample: sign doubling gives up to `4^|U|`, and `eraseDups` on `List (List _)` is
  list-order-sensitive, 65 > 16 over a 4-element signed universe). Use ONLY the corrected
  Finset-image statement over a signed universe `V : Finset (Sign × F)` with bound `2 ^ V.card`.
- Build `typeAt` on `Branch.formulasAt` (Branch.lean:81) — `formulasAt` discards the sign.
  Use filter-then-map keeping `(sf.sign, sf.formula)`.
- Add a second `GargGenoveseNegri2012` entry to references.bib — the key EXISTS at line 228.
  Enrich in place (pages, doi); a duplicate bibkey is the exact collision the prior research
  lineage warned about.
- Use `List.eraseDups_eq_dedup` or `List.toFinset_dedup` — neither exists. The available bridge
  route is membership: `List.mem_eraseDups` (stdlib, confirmed present) under `LawfulBEq`.
- Touch `intFImpReuseWitnessAnc?`, its spec lemma, or anything in
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/` — the side-condition shape is settled and
  consumed downstream as-is.
- Attempt a Bimodal instantiation — Bimodal uses its own local `SignedFormula` structure with
  compound labels (`Bimodal/Metalogic/Decidability/SignedFormula.lean:221,274,658-672`) and
  cannot instantiate without a migration that is out of scope.
- Attempt to discharge Temporal soundness obligations
  (`Temporal/Tableau/Soundness.lean:23-54`) — "bounded ⇒ countermodel" needs semantics that
  `Branch F L` does not carry; it is consumer work.
- Introduce any sorry — every lemma in scope has a verified or routine proof route; there is no
  legitimate strategic-sorry division point in this plan.

**MUST preserve**:
- Everything in the Preserved Assets table above.
- Executable behavior of Temporal `timeType`/`isSubsetBlocked` (defeq redirection only) — the
  24 temporal conformance rows are the acceptance check.
- Existing `references.bib` key names (enrich fields only, never rename or duplicate).

**Design decisions are SETTLED** (do not re-open without concrete counterexample):
- Side conditions (ancestor direction, `x ≤ w`, `ψ ∉ forced(x)`, explicit `F(ψ)@x` entry) stay
  logic-specific; the generic module exposes ONLY containment + counting. Rationale: Temporal's
  side conditions differ entirely (eventuality duplication) and Massacci Def. 8.2's
  per-obligation shape is logic-specific.
- The counting universe is SIGNED: `V : Finset (Sign × F)`, bound `2 ^ V.card`. Instantiations:
  `V = Sub(φ) ×ˢ {pos, neg}` recovers Temporal's `2^(2·|Sub(φ)|)`; the positive projection via
  `posTypeAt` over `U : Finset F` gives the `2^|Sub(φ)|` Sfor bound for downstream completeness
  work.
- Dependency direction: this task lands FIRST; the propositional-completeness task consumes it.
  Machine truth in state.json is authoritative; the task-description text claiming the reverse
  is stale.
- Module conventions: `module` header, `import Cslib.Init`, `@[expose] public section`,
  namespace `Cslib.Logic.Tableau`, References section — matching the `Branch.lean`/`Measure.lean`
  siblings.

## Goals & Non-Goals

- **Goals**:
  - New module `Cslib/Foundations/Logic/Tableau/Blocking.lean` with definitional + counting
    layers, zero sorry, wired into the barrel and CI-clean.
  - Temporal `timeType`/`isSubsetBlocked` redirected to the shared definitions (defeq), with
    `rfl` bridging lemmas and the 24 conformance rows re-verified.
  - `references.bib`: `DershowitzManna1979` added; `GargGenoveseNegri2012` enriched with
    pages/doi.
- **Non-Goals**:
  - No Temporal soundness discharge (obligations 1-2 of `Soundness.lean:23-54`).
  - No changes to the intuitionistic tableau (settled `intFImpReuseWitnessAnc?` shape).
  - No Bimodal migration (recorded follow-up opportunity, out of scope).
  - No `subsetOf` forced-refactor of the intuitionistic containment conjunct (prospective-world
    shape does not literally match `containmentBlocked`'s signature — do not force it).

## Risks & Mitigations

- **Risk**: The one untested defeq claim — Temporal `timeType` `rfl`-reduces to generic
  `typeAt` in-situ (confidence high, not compiled). **Mitigation**: Phase 3 fallback ladder:
  (1) `rfl`; (2) if `rfl` fails, prove equivalence via `simp`/`unfold` lemmas instead and keep
  the redirection as a definition change with a proved `_eq_` lemma; (3) after 3 failed
  attempts, STOP, leave Temporal untouched, mark Phase 3 [BLOCKED] with the exact goal state
  recorded — do not churn (H6).
- **Risk**: Minimal Mathlib import for the counting layer unknown until compile; `shake` may
  flag over-imports. **Mitigation**: start from the imports the research probes used
  (`Finset` powerset/card lemmas), let `lake shake` in Phase 5 confirm minimality; Scope
  Hypothesis on Phase 1.
- **Risk**: Lemma name or namespace collisions in the barrel (`lake exe mk_all`). **Mitigation**:
  `lean_local_search` for each new identifier before landing (research already found no
  collision for `typeAt`/`containmentBlocked` outside Temporal's namespaced versions).
- **Risk**: `List.mem_eraseDups` requires `LawfulBEq`; instance availability for `Sign × F`.
  **Mitigation**: `Sign` has explicit `ReflBEq`/`LawfulBEq` instances (Sign.lean:96-100);
  product instances derive; research compiled the bridge green already.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 4 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel. Territory (H7): Phase 1/2 own
`Cslib/Foundations/Logic/Tableau/Blocking.lean` exclusively; Phase 3 owns
`Cslib/Logics/Temporal/Tableau/Branch.lean` exclusively; Phase 4 owns `references.bib`
exclusively; Phase 5 owns barrel/CI files. Phase 3 is deliberately serialized after Phase 2 so
the Temporal build never sees a half-written Blocking.lean.

### Phase 1: Blocking.lean definitional layer (typeAt, posTypeAt, containmentBlocked + specs) [COMPLETED]

- **Goal:** Create `Cslib/Foundations/Logic/Tableau/Blocking.lean` with the three definitions
  and their spec lemmas, compiling green in isolation.
- **Tasks:**
  - [x] Create file with sibling conventions: `module` header, `import Cslib.Init`,
    `import Cslib.Foundations.Logic.Tableau.Branch`, minimal Mathlib import(s) needed by this
    phase (definitions are BEq-only; likely none beyond Branch's own), `@[expose] public
    section`, namespace `Cslib.Logic.Tableau`.
  - [x] `Branch.typeAt [BEq F] [BEq L] (b : Branch F L) (l : L) : List (Sign × F)` —
    filter-then-map keeping the sign, then `eraseDups` (exact definition from research F3; do
    NOT route through `formulasAt`).
  - [x] `Branch.posTypeAt [BEq F] [BEq L] (b : Branch F L) (l : L) : List F` — positive-only
    Sfor projection (research F3).
  - [x] `Branch.containmentBlocked [BEq F] [BEq L] (b : Branch F L) (l_new l_anc : L) : Bool` —
    `(b.typeAt l_new).all fun pair => (b.typeAt l_anc).any (pair == ·)`.
  - [x] Spec lemmas under `[LawfulBEq F] [LawfulBEq L]`: `mem_typeAt_iff` (membership
    characterization via filter/map/`List.mem_eraseDups`) and `containmentBlocked_iff`
    (`= true ↔ ∀ x ∈ b.typeAt l₁, x ∈ b.typeAt l₂`, via `List.all_eq_true`/`List.any_eq_true`).
  - [x] Docstrings + References section: `[Fitting1983]`, `[GargGenoveseNegri2012]` as
    provenance only; `[Massacci2000]` may be cited substantively (in corpus) for the
    per-obligation scoping remark.
- **Timing:** 1 hour
- **Depends on:** none
- **Verification Tier:** local
- **Estimated output:** ~110 lines
- **Scope Hypothesis:** definitional layer needs no Mathlib import beyond what
  `Branch.lean` transitively provides (BEq-only layer). Confirm at first scoped build; if a
  Mathlib import is needed for Phase 1 (not just Phase 2), record which and why.
  **CONFIRMED at implementation**: no Mathlib import needed; `List.eraseDups`,
  `List.mem_eraseDups`, `List.all_eq_true`, `List.any_eq_true` all resolve from Branch's
  transitive imports. One deviation from the phase sketch: `containmentBlocked_iff` closes by
  plain `simp [containmentBlocked, List.all_eq_true, List.any_eq_true]` — adding `eq_comm`
  (first attempt) made the two list lemmas loop.
- **Done when:** `lake build Cslib.Foundations.Logic.Tableau.Blocking` is green; zero `sorry`
  in the file; both spec lemmas stated and proved; commit per green substep.

### Phase 2: Blocking.lean counting layer (powerset bound, bridge, distinctTypes_le_pow, pigeonhole, strictChain_le_card) [NOT STARTED]

- **Goal:** Land the five counting-layer lemmas in Blocking.lean, all sorry-free. Every proof
  core was already compiled green during research — this phase is transcription into the
  module context, not proof discovery.
- **Tasks:**
  - [ ] Add minimal Mathlib import(s) for `Finset` powerset/card API (candidates:
    `Mathlib.Data.Finset.Powerset`; adjust to whatever the research probes used; shake
    confirms later).
  - [ ] `card_image_le_pow_of_forall_subset [DecidableEq β] (s : Finset α) (f : α → Finset β)
    (U : Finset β) (h : ∀ a ∈ s, f a ⊆ U) : (s.image f).card ≤ 2 ^ U.card` — via
    `Finset.card_le_card` into `U.powerset` (`Finset.mem_powerset`) + `Finset.card_powerset`.
    Projection-agnostic Branch-free helper shared by signed and Sfor instantiations.
  - [ ] Bridge lemma: `l.eraseDups.toFinset = l.toFinset` under `[DecidableEq α] [BEq α]
    [LawfulBEq α]` via `List.mem_eraseDups` membership extensionality (the ONLY available
    route — see Postmortem Constraints).
  - [ ] `Tableau.distinctTypes_le_pow` — the corrected F2 statement (signed universe
    `V : Finset (Sign × F)`, Finset-image count, bound `2 ^ V.card`); composition of the two
    lemmas above with `(b.typeAt l).toFinset ⊆ V` extracted from `hV` + filter/map membership.
  - [ ] `exists_typeAt_eq_of_card_lt` — pigeonhole corollary via
    `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`: `2 ^ V.card < b.labels.toFinset.card →
    ∃ l₁ ∈ b.labels, ∃ l₂ ∈ b.labels, l₁ ≠ l₂ ∧ (b.typeAt l₁).toFinset = (b.typeAt l₂).toFinset`.
  - [ ] `Tableau.strictChain_le_card [DecidableEq β] {k : Nat} (f : Nat → Finset β)
    (U : Finset β) (hchain : ∀ i, i < k → f i ⊂ f (i + 1)) (hU : f k ⊆ U) : k ≤ U.card` —
    induction + `Finset.card_lt_card` + `omega` (research's 13-line green proof).
- **Timing:** 1.5 hours
- **Depends on:** 1
- **Verification Tier:** local
- **Estimated output:** ~140 lines
- **Scope Hypothesis:** exactly five new lemmas complete the counting layer, and each research
  proof core transcribes without new helper lemmas beyond the listed bridge. Confirm during
  implementation; if a sixth helper is genuinely required, add it in this phase and record it
  in the summary (do not defer).
- **Done when:** scoped `lake build Cslib.Foundations.Logic.Tableau.Blocking` green; zero
  `sorry`; `lean_verify` axiom-check passes for `Tableau.distinctTypes_le_pow` and
  `Tableau.strictChain_le_card`; commit per green substep.

### Phase 3: Temporal redirection (timeType/isSubsetBlocked defeq wrappers + conformance re-run) [NOT STARTED]

- **Goal:** Redirect Temporal's `timeType` and `isSubsetBlocked`
  (`Cslib/Logics/Temporal/Tableau/Branch.lean:106-122`) to the shared definitions without any
  behavioral change, verified by the temporal conformance corpus.
- **Tasks:**
  - [ ] Add `import Cslib.Foundations.Logic.Tableau.Blocking` to
    `Cslib/Logics/Temporal/Tableau/Branch.lean`.
  - [ ] Redefine `timeType b t := Branch.typeAt b t` and
    `isSubsetBlocked b t t' := Branch.containmentBlocked b t t'` (the `TBranch Atom` →
    `Branch (Formula Atom) TimeIndex` abbrev chain via `TSF`/`SignedFormula`, Rules.lean:56-59,
    makes these type-correct).
  - [ ] Add `rfl` bridging lemmas (`timeType_eq_typeAt`, `isSubsetBlocked_eq_containmentBlocked`)
    locking the defeq. Fallback ladder if `rfl` does not close: see Risks & Mitigations (max 3
    attempts, then [BLOCKED], never churn).
  - [ ] Confirm consumers untouched: `isTemporallyBlocked`, `findBlockedTime`, and the
    eventuality side conditions stay local; call sites in `Rules.lean` (~:242,333,426),
    `Saturation.lean` (~:154-161,209), `Closure.lean` (~:90) require zero edits.
  - [ ] Re-run the temporal conformance rows in `CslibTests/TableauConformance.lean` — all 24
    temporal rows pass unchanged.
- **Timing:** 1 hour
- **Depends on:** 1, 2
- **Verification Tier:** interface
- **Estimated output:** ~30 changed lines (net near-zero; two defs replaced, two lemmas added)
- **Scope Hypothesis:** (a) the redirection is defeq and both bridging lemmas close by `rfl`
  (the one untested claim from research — high confidence, not compiled); (b) the consumer
  count is exactly the six call-site clusters listed and the conformance corpus has exactly 24
  temporal rows. Confirm both at implementation time; line numbers cited are hypotheses subject
  to drift.
- **Done when:** `lake build Cslib.Logics.Temporal.Tableau.Branch` plus its direct dependents
  (`Rules`, `Saturation`, `Closure`) green; conformance test rows pass; zero `sorry`; commit.

### Phase 4: references.bib — add DershowitzManna1979, enrich GargGenoveseNegri2012 [NOT STARTED]

- **Goal:** Bibliography deliverable, exactly two edits, no duplicate keys.
- **Tasks:**
  - [ ] Append the ready `@article{DershowitzManna1979, ...}` entry (Dershowitz & Manna,
    "Proving Termination with Multiset Orderings", CACM 22(8):465-476, 1979,
    doi 10.1145/359138.359142) in the file's existing key-ordering convention.
  - [ ] Enrich the EXISTING `GargGenoveseNegri2012` entry at references.bib:228: add
    `pages = {315--324}` and `doi = {10.1109/LICS.2012.42}`; change nothing else, never add a
    second entry with this key.
  - [ ] Verify: `grep -c '@.*{GargGenoveseNegri2012,' references.bib` == 1 and
    `grep -c '@.*{DershowitzManna1979,' references.bib` == 1.
- **Timing:** 15 minutes
- **Depends on:** none
- **Verification Tier:** prose
- **Estimated output:** ~12 lines
- **Done when:** both grep counts are exactly 1; diff read-through confirms edits confined to
  the two entries; commit.

### Phase 5: CI integration gate (barrel, checkInitImports, full build, lint-style, shake, test) [NOT STARTED]

- **Goal:** Wire the new module into the library barrel and pass the full repository gate set.
- **Tasks:**
  - [ ] `lake exe mk_all --module` — register Blocking.lean in the barrel.
  - [ ] `checkInitImports` passes.
  - [ ] Full `lake build` green.
  - [ ] `lake exe lint-style` clean (research probes hit one style-whitespace lint —
    trivially fixed; expect none after Phase 1/2 discipline).
  - [ ] `lake shake` — confirm import minimality for Blocking.lean and the Temporal import
    addition; remove any over-imports it flags.
  - [ ] `lake test` — full suite including all conformance rows.
  - [ ] Zero-sorry sweep: `grep -n "sorry" ` over all files touched by Phases 1-3 returns
    nothing.
- **Timing:** 1 hour (dominated by full build)
- **Depends on:** 1, 2, 3, 4
- **Verification Tier:** full
- **Estimated output:** ~10 changed lines (barrel + any shake-driven import trims)
- **Done when:** every gate in the task list is green in one final run; commit completes the
  implementation.

## Testing & Validation

- [ ] Scoped `lake build Cslib.Foundations.Logic.Tableau.Blocking` after Phases 1 and 2.
- [ ] `lean_verify` axiom checks on `Tableau.distinctTypes_le_pow` and
  `Tableau.strictChain_le_card` (no new axioms, no sorryAx).
- [ ] Interface build of Temporal `Branch` + `Rules` + `Saturation` + `Closure` after Phase 3.
- [ ] 24 temporal conformance rows in `CslibTests/TableauConformance.lean` pass unchanged.
- [ ] Duplicate-bibkey greps (Phase 4) both return exactly 1.
- [ ] Final gate set (Phase 5): mk_all barrel, checkInitImports, full `lake build`,
  `lake exe lint-style`, `lake shake`, `lake test`, zero-sorry sweep.

## Artifacts & Outputs

- plans/01_blocking-module-plan.md (this file)
- Cslib/Foundations/Logic/Tableau/Blocking.lean (new, ~250 lines, zero sorry)
- Cslib/Logics/Temporal/Tableau/Branch.lean (redirected defs + 2 bridging lemmas)
- references.bib (1 new entry, 1 enriched entry)
- Cslib.lean barrel (mk_all-regenerated)
- summaries/01_blocking-module-summary.md (written at implementation completion)

## Rollback/Contingency

- Phases commit per green substep on `main`; each phase is independently revertable by commit.
- If Phase 3's defeq claim fails beyond the 3-attempt ladder, revert only the Temporal edits
  (Blocking.lean stands alone and still fully serves the downstream consumer); mark Phase 3
  [BLOCKED] with the recorded goal state and leave Phases 1, 2, 4 landed — the module is
  valuable without the Temporal lift.
- If `lake shake` or `lint-style` flags churn against each other, prefer shake's minimal-import
  verdict and re-run lint-style once; never loop more than twice (H6).
- No destructive git operations; snapshot via `git-snapshot.sh` before any intentional revert.
