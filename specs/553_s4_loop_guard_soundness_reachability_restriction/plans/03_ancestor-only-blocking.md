# Implementation Plan: Ancestor-Only Blocking for the S4 Keyed Loop Guard (v3)

- **Task**: 553 - s4_loop_guard_soundness_reachability_restriction
- **Status**: [ABANDONED]
- **Superseded by**: `plans/04_subtractive-blocking-red-channel.md` (v4). Ancestor-only blocking is
  abandoned because this plan's own Phase 2 decision gate **refuted** it (see `#### Phase 2 Verdict`
  below, retained verbatim): `branchSatisfiableIn_s4FC_ancestor_redirect` cannot be discharged from
  standalone driver-independent hypotheses. Per a user-authorized route change on the evidence in
  `reports/04_massacci-subtractive-blocking-priced.md`, v4 implements route (3) — `Massacci2000`
  Technique 8.2 subtractive blocking with a completeness-only redirect channel — which never adds
  the redirect edge to `acc` and so has no edge-justification obligation at all. **Phase 1 of this
  plan remains `[COMPLETED]` and its four measurements (`#### Phase 1 Measurements`) are inherited
  by v4 as a preserved asset**, with the explicit caveat that Measurement D(iv)'s 1374/1374 result
  is not treated as evidence for any obligation in v4. Retained as a historical record; do not
  implement from this file.
- **Effort**: 26-34 hours (14 phases, two of which are decision gates that may terminate the route)
- **Dependencies**: None (no other task blocks this)
- **Research Inputs**:
  - `reports/02_redirect-inertness-divergence-audit.md` (primary; mandate basis)
  - `reports/01_s4-keyed-guard-soundness-falsified.md`
  - `.orchestrator-handoff.json` (cleanup dispatch `5ac7cbb7` orphan report)
  - Literature: `massacci_2000_single_step_tableaux_for_modal_logics` (per-repo sub-index; read
    directly in this planning run - see Source-to-Implementation Mapping)
- **Artifacts**: `plans/03_ancestor-only-blocking.md` (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/state-management.md`
  - `.claude/rules/plan-compliance.md`
  - `.claude/rules/cslib.md`
- **Type**: cslib
- **Plan version**: 3 (supersedes v1 `01_s4-settled-context-scheduling.md` and v2
  `02_origin-edge-invariant-revision.md`, both stamped **[ABANDONED]** with a `Superseded by`
  pointer to this file; itself superseded by v4 `04_subtractive-blocking-red-channel.md`)

---

## Overview

The keyed S4 loop guard `blockingWorldS4Keyed` (`LoopChecking.lean:506`) licenses a redirect edge
`src -> wBlock` with **no constraint that `wBlock` be reachable from `src`**, which makes
`modalTableauS4Keyed` unsound against a machine-checked countermodel (`CslibTests/
S4LoopGuardRegression.lean`). Route P (ordered scheduling + an origin-edge invariant) attempted to
prove the redirect edge *inert* instead of restricting it; the divergence audit machine-checked the
two load-bearing inertness lemmas as **FALSE at a reachable ordered-driver state**, and they have
since been removed (commit `5ac7cbb7`). Per the user-authorized mandate change, this plan
implements audit option **(c): abandon Route P's inertness argument in favour of restricting the
guard so a redirect edge may only target a world on the source's own **spine** (its mint-ancestor
chain).

**Definition of done**: `modalTableauS4KeyedAnc` (ancestor-restricted, ordered) is sorry-free and
proved sound against `s4FC`, `Cslib/Logics/Modal/Tableau/` still has **0** sorries, the axiom count
is still exactly **26**, and the full CI pipeline is green at every commit.

**Scope constraint**: file scope is `Cslib/Logics/Modal/Tableau/**` plus
`CslibTests/S4LoopGuardRegression.lean` plus this task's `specs/` directory.
`Cslib/Logics/Modal/Metalogic/Constructive/Nested/**` and `Cslib.lean` belong to a concurrent
session and are **out of scope in every phase**.

### The Single Load-Bearing Risk, Stated Up Front

Ancestor-only blocking **is** a guard restriction, and the audit's §6 replacement prediction says
any restriction that adds a conjunct to `blockingWorldS4Keyed`'s filter collapses this chain:

> guard filter -> `blockingWorldS4Keyed_none_fresh` (`:538`) -> `S4LoopInv.keysDistinct` (`:7073`)
> -> `modalKnownWorlds_length_le_worldBoundS4` (`:6463`) -> `modalStepBranchS4_worldBound`
> (`:6501`) -> `S4LoopInv.bClosure`'s minting cases -> `modalExpMeasure_entry_le_fuelS4` (`:8486`)
> -> fuel sufficiency.

**This plan's verdict on that risk, reached by reading the source (verified, see mapping table):
the chain does break, it cannot be repaired by key enrichment, and it must be re-derived on a
depth-times-branching basis. That re-derivation is Phases 5-7 and 10-11 of this plan, not a
footnote.** Concretely:

1. `blockingWorldS4Keyed_none_fresh` **does not survive** as stated. Its ancestor-restricted
   analogue `blockingWorldS4Anc_none_fresh_spine` **does** survive, with the same five-line
   `List.min?_eq_none_iff` proof (verified: the existing proof at `:544-555` uses nothing about
   which list is filtered). But it concludes only "the prospective birth content differs from every
   **spine-ancestor's** recorded key", not from every recorded key.
2. Therefore **global `keysDistinct` becomes false**: two worlds on different spine branches may be
   minted with equal keys. `keysUpdate_preserves_keysDistinct` (`:566`) consumes the global
   freshness fact and has no other feeder (verified by reading its proof), so it cannot be repaired.
3. Therefore `modalKnownWorlds_length_le_worldBoundS4`'s `hKD` hypothesis is unavailable and the
   pigeonhole bound on the **number of worlds** is lost.
4. **The ancestor restriction cannot be re-expressed as key enrichment** (the audit's
   chain-preserving alternative). Enrichment preserves the chain because the comparison stays plain
   key equality; the ancestor test is irreducibly *relational* in the pair `(src, wBlock)`, so no
   function of `wBlock`'s key alone can express it. Restricting the searched list rather than the
   predicate does not help either: `none` still means "no ancestor matched".
5. **What replaces it**: keys are pairwise distinct **along each spine**
   (`keysDistinctAlongSpine`, established by (1)), which bounds spine **depth** by
   `(signedSubfmls φ₀).powerset.card <= modalWorldBoundS4 φ₀`; out-degree is bounded by
   `S4LoopInv.outDegEq` (already a landed field, `:7061`) plus `eNodup`/`eClosure`; and world count
   is then bounded by a `geomCap`-shaped tree count. `geomCap` and `geomCap_le_pow` already exist
   (`Cslib/Foundations/Logic/Tableau/Measure.lean:57,94`), and K's own world bound is exactly this
   branching^depth shape (`modalWorldBound = (2C+1)^(C+1)`, `FmpMeasure.lean:144`) with a working
   generic proof template (`modalStepBranch_worldBound_gen`, `FmpMeasure.lean:2659`;
   `modalMaxWorld_lt_worldBound_of_phiBound`, `CompletenessLoop.lean:199`). So the re-derivation has
   an in-repo template rather than being invented from nothing — but it is genuinely 4-5 phases.

**A second, equally load-bearing risk that the audit understated and this plan front-loads.** The
audit's §5 states ancestor-only blocking "restores `branchSatisfiableIn` outright". **That claim is
marked NOT-YET-VERIFIED and this plan's own reading of the obligation suggests it is too
optimistic.** The edge added is `src -> wBlock` with `wBlock` an ancestor of `src`; soundness needs
`m.r (f src) (f wBlock)` — the **upward** relation. The reflexive-transitive closure of spine
(parent -> child) edges supplies only `m.r (f wBlock) (f src)`, the **downward** relation, and S4
gives neither symmetry nor a way to convert one into the other. The justification therefore requires
a **cluster** construction (S4 frames admit cycles, so the back-edge itself is frame-legal), and the
cluster's box-propagation obligation is exactly the shape that killed Route P. Massacci's
PROPOSITION 8.1 (verified, see mapping) supplies ancestor -> descendant box monotonicity, which is
the *wrong* direction for this obligation; the descendant -> ancestor direction has to come from
key equality via `S4LoopInv.keyLowerBd`, and `successorBirthContent`'s **unwrapped** box-context
(`:387`, `(pos, ψ)` recorded for `T(□ψ)@w`) yields only `T(ψ)@wBlock ∈ b`, not `T(□ψ)@wBlock ∈ b`.

Consequence for planning, stated plainly rather than sequenced around: **the ancestor route may
need the audit's boxed-birth-content refinement as a sub-component.** This is not a re-argument for
option (b) as a substitute for (c) — it is the observation that (b) and (c) are composable and (c)
may not close without (b)'s key change. Phase 2 is a hard decision gate that settles this before
any driver surgery, and it has an explicit branch for adopting boxed keys inside the ancestor route.

### Preserved Assets

The following landed work is sorry-free, axiom-clean and **must not regress**. Each row carries an
explicit disposition. Nothing here is deleted on an unverified premise: the one retirement
(Phase 9's weakened invariant) is gated behind Phase 2's verdict.

| Component | File | Status | Disposition under ancestor-only |
|---|---|---|---|
| P1: counterexample regression corpus | `CslibTests/S4LoopGuardRegression.lean` | [COMPLETED] | **KEEP unchanged.** The unordered keyed driver's documented unsoundness is unaffected by this route. Extended (not replaced) in Phase 13. |
| P2: documentation correction | `LoopChecking.lean` (guard docstring `:466-505`) | [COMPLETED] | **KEEP.** `:491-497`'s "no reachability restriction" defect is exactly what this plan repairs; update the docstring in Phase 4 to point at the repair. |
| P3: decidable mint-readiness predicate | `LoopChecking.lean` (`modalNonMintCandidates`) | [COMPLETED] | **KEEP, load-bearing.** The ordered stepper consumes it and the ancestor driver is built on the ordered stepper. |
| P4: ordered stepper + 2 structural lemmas | `LoopChecking.lean:1107` (`modalStepBranchS4KeyedOrdered`), `_cases` (`:1124`) | [COMPLETED] | **KEEP, extended.** `modalStepBranchS4KeyedAnc` (Phase 8) is a further refinement landing beside it; `_cases`'s split shape is the template every Phase 9 lemma factors through. |
| P5: termination measure re-verification | `LoopChecking.lean` / `FmpMeasure.lean` | [COMPLETED] | **KEEP.** Lean-level termination is structural on `fuel` and is not at risk (audit §6). |
| P6: loop invariant + fuel-sufficiency chain | `S4LoopInv` (`:7047`), `modalKnownWorlds_length_le_worldBoundS4` (`:6463`), `modalStepBranchS4_worldBound` (`:6501`), `modalExpMeasure_entry_le_fuelS4` (`:8486`) | [COMPLETED] | **MOSTLY KEEP; one field SUPERSEDED.** 9 of `S4LoopInv`'s 10 fields carry over verbatim. `keysDistinct` (`:7073`) is superseded by `keysDistinctAlongSpine`. `modalKnownWorlds_length_le_worldBoundS4` is **kept and reused**: its powerset-injection proof is re-instantiated in Phase 5 on a spine chain instead of on all known worlds. `modalExpMeasure_entry_le_fuelS4` is re-derived over the new bound in Phase 11. |
| P7: ordered driver + entry point | `LoopChecking.lean:7830` (`modalExpandBranchesS4KeyedOrdered`), entry point | [COMPLETED] | **KEEP as base.** The ancestor driver lands beside it (Phase 12); the ordered driver is not retired in this plan. |
| P8: empirical gate (measured result) | `specs/.../artifacts/`, plan v2 record | [COMPLETED] | **KEEP; methodology reused twice.** The measured facts stand: `modalExpandBranchesS4KeyedOrdered` does **not** close `cex` while the shipped unordered driver **does**; and the exhaustive size<=6 / 2-atom sweep (8532 formulas) is verdict-for-verdict identical between drivers (1650 closed, 6882 open, 0 fuel-exhausted). This harness is re-run in Phase 1 and Phase 13. |
| P9: `branchPropAdequateIn` + 3 `hready` consumers | `FrameSoundness.lean:1183, 1241, 1275, 1310, 1334` | [COMPLETED] | **RETIRE — but only after Phase 2 confirms `branchSatisfiableIn` survives.** If Phase 2 confirms, Phase 14 deletes them and the §5.1 disjunctive-edge-conjunct repair is never planned (it dissolves). If Phase 2 does **not** confirm, they stay and the route is escalated, not patched. Do not delete them earlier. |

### Orphan-Report Adjudication (cleanup dispatch `5ac7cbb7`)

The cleanup handoff left nine origin-edge declarations plus two conditional lemmas as orphan
candidates for this plan to adjudicate. **All are true and sorry-free. The adjudication is: retire
almost nothing; repurpose the origin-edge family as the spine.** `keysOriginS4` records, for each
recorded key, the world `u` that minted it, the witness that minted it, and the edge `u -> v ∈ acc`
— which is precisely a parent-pointer record, i.e. the invariant content this plan's `spine`
component needs. Re-deriving it from scratch would discard two phases of landed work.

| Declaration | Location | Disposition |
|---|---|---|
| `keysOriginS4` | `LoopChecking.lean:1279` | **REPURPOSE** as the spine's tying invariant (Phase 3). |
| `keysOriginS4_entry` | `:1294` | **REPURPOSE** (base case of the spine chain). |
| `keysOriginS4_mono_branch` | `:1306` | **KEEP** (preservation chain). |
| `keysOriginS4_mono_acc` | `:1327` | **KEEP** (preservation chain). |
| `keysRootEmpty` | `:2009` | **KEEP.** The root's empty key is the base case of Phase 5's depth chain. |
| `keysRootEmpty_entry` | `:2015` | **KEEP** (same). |
| `modalStepBranchS4Keyed_preserves_keysOriginS4` | `:4558` | **KEEP** (spine preservation, unordered driver). |
| `modalStepBranchS4KeyedOrdered_preserves_keysOriginS4` | `:4775` | **KEEP, load-bearing** for Phase 9. |
| `modalStepBranchS4Keyed_result_acc_eq` | `:2406` | **KEEP** (used inside the above). |
| 4th hypothesis/conjunct of `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` | `:7667-7688` | **KEEP.** This is the parent-record conjunct; Phase 9 extends rather than removes it. |
| `blockedRedirect_boxctx_mem_of_boxOrigin` | `:1466` | **REPURPOSE.** Its box-origin hypothesis is close to the *ancestor* case of the edge-justification obligation; Phase 2 evaluates it as a starting point rather than writing a fresh lemma. |
| `blockedRedirect_diaNeg_mem_of_diaOrigin` | `:1506` | **REPURPOSE** (dual, same reasoning). |

**Housekeeping (done in this planning run, not left to a dispatch)**: v1 and v2 are stamped
`[ABANDONED]` with a `Superseded by` line pointing here (`[ABANDONED]` is the plan-format's
whole-document marker; there is no `[SUPERSEDED]` marker in the vocabulary). The stray Phase 13
status flip in v2 (`[NOT STARTED]` -> `[IN PROGRESS]`, flagged by the cleanup handoff) is reverted.

### Source-to-Implementation Mapping (H3, Tier 1 + Tier 3)

Every load-bearing claim is marked **VERIFIED** (read in this planning run, with the citation) or
**NOT-YET-VERIFIED** (to be settled by the named phase). Nothing in this table is asserted from
memory.

| Claim | Source | Status |
|---|---|---|
| The guard filters `keys` globally by birth-content equality and takes `min?` | `LoopChecking.lean:506-511` | **VERIFIED** |
| `_none_fresh`'s proof uses nothing about which list is filtered, so the ancestor-restricted analogue has the same proof | `LoopChecking.lean:544-555` | **VERIFIED** |
| `keysUpdate_preserves_keysDistinct` has `_none_fresh` as its sole feeder | `LoopChecking.lean:566-593` | **VERIFIED** |
| `keysDistinct` is consumed as `hKD` by the pigeonhole, which feeds the strict world bound, which `bClosure`'s minting cases require | `:7073`, `:6463-6491`, `:6501-6520`, `:7089-7094` | **VERIFIED** |
| `outDegEq` is already an `S4LoopInv` field, giving the branching half of a tree bound | `LoopChecking.lean:7061` | **VERIFIED** |
| `geomCap` + `geomCap_le_pow` exist and are reusable | `Cslib/Foundations/Logic/Tableau/Measure.lean:57, 94` | **VERIFIED** |
| K's world bound is a branching^depth tree bound with a working generic proof, usable as the template | `FmpMeasure.lean:144`, `:2659`; `CompletenessLoop.lean:199-227` | **VERIFIED** |
| K's `rankEdge` is an **exact equality on all `acc` edges** (`rank w' + 1 = rank w`), hence incompatible with back-edges: any port must tie rank to spine edges only | `FmpMeasure.lean:2340` | **VERIFIED** |
| The loop-check discipline in the literature is "before reducing a π-formula, check the prefix is not a copy of a **shorter** prefix", sharpened for K4/S4 to **modal copy** (same ν-formulae) | Massacci 2000, Technique 8.2 + DEFINITION 8.2 (`chunk_0030.md:14-36`) | **VERIFIED** |
| **Correction to the audit's attribution**: Massacci's blocking discipline is *shorter (modal) copy*, **not** ancestor-only. Ancestry (initial subsequence, `Ftree`) enters via the **Pruning Lemma 8.2**, a different mechanism | `chunk_0030.md:39-43`, `chunk_0031.md:3-19` | **VERIFIED** |
| Ancestor-restriction *implies* shorter-prefix, so this route is a sound-edge **refinement** of Massacci's discipline, not a departure from it | derived from the two rows above | **VERIFIED** (derivation) |
| Box formulas propagate **ancestor -> descendant** in a saturated branch (the direction available for free) | Massacci PROPOSITION 8.1 (`chunk_0065.md:9-13`) | **VERIFIED** |
| Massacci's S4 prefix-length bound is `hbL - 1 = 1 + dp + p x n` — a *depth* bound, matching this plan's depth-times-branching strategy | `chunk_0065.md:48-49` | **VERIFIED** |
| An ancestor back-edge `src -> wBlock` is model-justifiable, i.e. `branchSatisfiableIn s4FC` survives adding it | audit §5 asserts it; this plan's reading finds the needed relation is **upward** while reflexive-transitivity gives only **downward** | **NOT-YET-VERIFIED — Phase 2 gate** |
| The ancestor route closes without the boxed-birth-content refinement | unresolved; `successorBirthContent`'s unwrapped box-context (`:387`) yields `T(ψ)@wBlock`, not `T(□ψ)@wBlock` | **NOT-YET-VERIFIED — Phase 2 gate** |
| Global `keysDistinct` empirically breaks (two worlds actually acquire equal keys) under ancestor-only | analytic argument above; no measurement yet | **NOT-YET-VERIFIED — Phase 1 gate** |
| The `geomCap` tree-count lemma is provable in bounded effort | template exists but is not a drop-in (see `rankEdge` row) | **NOT-YET-VERIFIED — Phase 7** |
| `Gore1999` corroborates the ancestor-only discipline | PDF not ingested (`references.bib:1023`, "paywalled") | **NOT VERIFIABLE — see Phase 2 escalation branch** |

---

## Postmortem Constraints

Binding on every implementation dispatch under this plan.

**Do NOT**:

- **Do NOT state a "Named difficulty", a driver-behaviour claim, or a "the invariant already gives
  us X" step that has not been checked against the actual definitions.** v1 blocked on a false
  premise about mint payloads; v2 blocked on the R1 witness-collision verdict. Both failures were
  the same shape: *a plan-level claim about the driver's behaviour that had not been checked against
  the source*. Every phase below that depends on such a claim carries its verification inside the
  phase.
- **Do NOT re-propose any of the following** (all eliminated on evidence): the three removed false
  lemmas (`blockedRedirect_boxctx_mem`, `blockedRedirect_diaNeg_mem`,
  `blockedRedirect_propAdequate`); **R2** (strengthen `keysOriginS4` to cover the witness pair — the
  target statement is false); **R3 as stated** (a side condition on `blockingWorldS4Keyed`'s filter
  while keeping global `keysDistinct` — breaks the pigeonhole); the origin-edge invariant *as a
  route to redirect-inertness* (as spine data it is repurposed, which is different).
- **Do NOT attempt to prove redirect-inertness for the sibling case.** It is false at a reachable
  state (audit §2.2, trace step [6]->[7]). Under this plan the sibling case does not arise, because
  the guard never returns a sibling.
- **Do NOT plan or land the §5.1 disjunctive-edge-conjunct repair.** Ancestor-only dissolves the
  `hready` discharge problem by removing the need for `branchPropAdequateIn` entirely. If Phase 2
  shows otherwise, escalate — do not patch `branchPropAdequateIn`.
- **Do NOT resurrect the retired central prediction** ("narrowing the guard may break TERMINATION
  rather than merely completeness"). Lean-level termination is structural on `fuel` (`:7830`, no
  `termination_by`), the `fuel = 0` arm returns `.closed` only from genuine closure checks, so a
  spurious `.closed` is impossible. Carry §6's replacement instead (quoted verbatim in the Overview).
- **Do NOT edit `Cslib/Logics/Modal/Tableau/Rules.lean`.** `modalApplyOne` is shared with K/T/B/S5
  and `FmpMeasure.lean`'s `_gen` lemmas. Any payload change belongs in the S4-keyed layer.
- **Do NOT touch `Cslib/Logics/Modal/Metalogic/Constructive/Nested/**` or `Cslib.lean`** — concurrent
  session territory.
- **Do NOT delete Phase 9's `branchPropAdequateIn` machinery before Phase 2's gate returns.**
- **Do NOT weaken, vacuously restate, or `True`-stub any landed statement.** `def X := True`,
  `theorem X := trivial` and friends are prohibited (`.claude/rules/cslib.md`).
- **Do NOT compress Phases 5-7 into one dispatch** to make the plan look cheaper. They are three
  distinct bounded units and the middle one is where the route most plausibly fails.

**MUST preserve**:

- Every row of the Preserved Assets table, at its stated disposition.
- Axiom count exactly **26**; zero new axioms.
- `Cslib/Logics/Modal/Tableau/` at **0** sorries. Repo census baseline is **40** (39 pre-session +
  1 belonging to the concurrent session's `Nested/Soundness.lean:1315`). A sorry is never a planned
  destination; a strategic-sorry skeleton remains a legitimate *mid-phase recovery* move that must
  be discharged before the phase is marked `[COMPLETED]`.
- Full CI green at every commit: `lake build`, `lake test`, `lake lint`, `lake exe
  checkInitImports`, `lake exe lint-style`, `lake exe mk_all --module`, scoped `lake shake
  --add-public --keep-implied --keep-prefix`. The single pre-existing `lake lint` error in
  `Cslib/Logics/Temporal/Tableau/Saturation.lean` is the known baseline and must remain the *only*
  one.
- The Phase 8 measured facts. Any dispatch that changes a driver re-runs the differential sweep
  rather than reasoning about what it would produce.

**Design decisions are SETTLED** (do not re-open without a concrete, machine-checked
counterexample):

1. **Option (c), ancestor-only blocking, is the route.** Options (a) and (d) are eliminated (the
   statements are false; a sorry for a false lemma is an unsound foundation). Option (b) alone is
   not the route; it may be adopted *inside* (c) as a sub-component if Phase 2 requires it.
2. **The guard restriction is by spine ancestry, not by "shorter key" or "smaller index".** Index
   order is not ancestry (the audit's step-[6] collision is between siblings, both with smaller
   index than the source).
3. **The spine is a new explicit data component**, not derived from `acc`. `acc` contains back-edges
   and is therefore cyclic; ancestry cannot be read off it.
4. **Global `keysDistinct` is abandoned, not repaired.** Its replacement is spine-local.
5. **The origin-edge family is repurposed as spine data, not deleted.**
6. **The ancestor driver lands beside the ordered driver**, as `modalStepBranchS4KeyedAnc` /
   `modalTableauS4KeyedAnc`. No landed driver is retired in this plan.

---

## Goals & Non-Goals

- **Goals**:
  - Settle, before any driver surgery, whether an ancestor back-edge is model-justifiable and
    whether boxed birth content is required (Phases 1-2).
  - Land a spine-tracking, ancestor-restricted, ordered S4 keyed driver that is sorry-free.
  - Re-derive the world bound and fuel sufficiency on a depth-times-branching basis.
  - Prove `modalTableauS4KeyedAnc` sound against `s4FC`.
  - Gate the new driver empirically with the proven 8532-formula differential harness.
- **Non-Goals**:
  - Completeness of the ancestor-restricted driver (the restriction can only lose completeness;
    that is a separate task if the sweep shows verdict changes).
  - Retiring `modalTableauS4Keyed` or `modalTableauS4KeyedOrdered`.
  - Any change to `Rules.lean`, to K/T/B/S5, or to the concurrent session's territory.
  - Acquiring `Gore1999` unless Phase 2 escalates (see its escalation branch).

## Risks & Mitigations

- **Risk (highest): the ancestor back-edge is not model-justifiable** — soundness needs the upward
  relation, reflexive-transitivity gives only downward. *Mitigation*: Phase 2 is a hard gate that
  proves a standalone, driver-independent cluster lemma before anything else is built. If it cannot
  be proved in one dispatch, the phase is marked `[BLOCKED]` and the route is escalated to the user
  with the exact goal state — **not** patched, and **not** deferred to a later phase.
- **Risk: the tree-count bound is not provable in bounded effort** (K's `rankEdge` is an exact
  equality on all `acc` edges, so the template is not a drop-in). *Mitigation*: Phase 5 and Phase 6
  land the two halves (depth, branching) as standalone lemmas with no driver dependency, so Phase 7
  starts from two proved facts and a `geomCap` skeleton. If Phase 7 stalls, Phases 1-6 are still
  independently valuable and the blocker is precisely localised.
- **Risk: threading a fifth state component through the driver re-opens the ten-field invariant
  preservation** (this is what made Phases 10-11 expensive). *Mitigation*: the spine is threaded in
  Phase 8 as a *separate* component whose preservation is proved once (Phase 9) by reusing
  `modalStepBranchS4KeyedOrdered_preserves_keysOriginS4`, which already proves the parent-record
  fact for the ordered stepper.
- **Risk: the restriction loses completeness on the corpus** (blocked worlds now sometimes mint,
  changing verdicts). *Mitigation*: Phase 1 measures this before any Lean proof work; the gate is
  `open -> closed` changes = 0 (a soundness regression, fatal) with `closed -> open` changes
  reported and evaluated (a completeness change, informative).
- **Risk: context exhaustion mid-phase.** *Mitigation*: every phase is one bounded unit with a
  stated done-criterion; commit at every green sub-step per
  `.claude/rules/git-workflow.md`'s commit-per-green-substep mandate.

---

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 5, 6 | 2 |
| 4 | 4, 7 | 3, 5, 6 |
| 5 | 8 | 4, 7 |
| 6 | 9 | 8 |
| 7 | 10 | 9 |
| 8 | 11 | 10 |
| 9 | 12 | 11 |
| 10 | 13, 14 | 12 |

Phases within the same wave can execute in parallel. Wave 3's three phases are genuinely
independent: Phase 3 touches only the spine defs, Phase 5 only `Finset` chain combinatorics, Phase 6
only the out-degree count. **Territory for parallel dispatch**: Phases 3 and 4 own
`LoopChecking.lean`'s guard/spine sections; Phases 5-7 own its bound sections; no two phases in the
same wave write the same section. Phase 14 owns `FrameSoundness.lean`; Phase 13 owns
`CslibTests/S4LoopGuardRegression.lean`.

**Note on phase count (H8 deviation, declared).** Fourteen phases exceeds the 8-phase ceiling the
hard-mode planner applies to "complex" tasks. The ceiling is not force-fit here for two reasons:
the dispatching mandate explicitly authorised 10+ phases for this route and instructed that it not
be compressed to look cheaper; and every phase below independently passes the bounded-unit test
(one definition, one lemma family, or one measurement, each with a concrete stopping condition).
A skeleton plan with strategic-sorry division points was considered and rejected: the two riskiest
obligations are the *first* two phases, so there is no long green prefix to skeletonise, and a
strategic sorry at either gate would be a sorry standing in for a possibly-false statement — the
exact failure this task has already suffered once.

---

### Phase 1: Executable ancestor-only probe and four measurements [COMPLETED]

- **Goal:** Settle empirically, with no Lean proof work and no `Cslib/**` change, whether the
  ancestor-only driver behaves acceptably and what the invariant damage actually is.
- **Tasks:**
  - [x] Write `specs/553_.../artifacts/s4ancestor.lean` in the style of the existing
        `s4witness.lean` / `s4boxed.lean` probes (definitions and `#eval` only — no proofs, no
        `sorry`, no axioms): an executable spine-tracking state, an ancestor-restricted guard
        `bwAnc`, and ordered + unordered stepper variants.
  - [x] **Measurement A (soundness)**: `cex` must be OPEN under the ancestor-ordered driver.
  - [x] **Measurement B (validity)**: the T, 4, and K axiom instances must be CLOSED.
  - [x] **Measurement C (differential sweep)**: rerun Phase 8's exhaustive harness — 2 atoms,
        size <= 6, 8532 formulas, fuel 100, both orderings — and report `open -> closed` (must be
        0) and `closed -> open` counts against the 1650-closed / 6882-open / 0-fuel-exhausted
        baseline.
  - [x] **Measurement D (invariant damage)**: instrument the probe to report, per formula,
        (i) whether any two recorded keys are ever equal (does global `keysDistinct` actually
        break?), (ii) max spine depth observed, (iii) max out-degree observed, and (iv) for every
        blocked redirect, whether `∀ψ, T(□ψ)@src ∈ b → T(□ψ)@wBlock ∈ b` holds — the upward
        box-propagation test.
  - [x] Record all four verdicts verbatim in this plan under a new `#### Phase 1 Measurements`
        subsection, and in the dispatch handoff.
- **Estimated output:** ~250 lines of probe Lean plus a ~40-line measurement record.
- **Done when:** `lake env lean specs/553_.../artifacts/s4ancestor.lean` runs to completion and all
  four measurements are recorded as numbers, not prose. Measurement C's `open -> closed` count is
  0; if it is not, the phase ends `[BLOCKED]` and the route is escalated immediately.
- **Timing:** 2-3 hours (the sweep alone runs ~20 minutes).
- **Depends on:** none

#### Phase 1 Measurements

Probe: `specs/553_.../artifacts/s4ancestor.lean`. `lake env lean` on it runs to completion, no
errors, no warnings, no sorries, no axioms. All four measurements below are verbatim `#eval`
output from that run.

- **Measurement A (soundness) — PASS.** `cex` (report 01's counterexample, node-size 19):
  baseline (shipped, unrestricted keyed driver) closes it (`some true`, confirming the known
  unsoundness); the ancestor-ordered driver leaves it **OPEN** (`some false`), fuel 400 both
  drivers. The soundness defect this route targets is fixed for this counterexample.
- **Measurement B (validity) — PASS.** T, 4, and K axiom instances all **CLOSE** under the
  ancestor-ordered driver, fuel 400: `some true`, `some true`, `some true`.
- **Measurement C (differential sweep) — PASS, gate satisfied.** 2 atoms, size <= 6, 8532
  formulas, fuel 100:
  - baseline (shipped unrestricted keyed driver): closed=1650, open=6882, fuelExhausted=0
    (reproduces the established baseline exactly).
  - ancestor-unordered: closed=1650, open=6873, fuelExhausted=**9**. `open -> closed` = 0,
    `closed -> open` = 0 against baseline (gate satisfied), but 9 formulas that terminated
    cleanly under the baseline now exhaust fuel 100 under the unordered ancestor stepper — a
    mild termination cost specific to the unordered variant.
  - ancestor-ordered: closed=1650, open=6882, fuelExhausted=0 — **identical** to baseline on
    every count. `open -> closed` = 0, `closed -> open` = 0 (gate satisfied) and no termination
    cost at all for the ordered variant at this size/fuel.
  - **Gate verdict**: `open -> closed` (the completeness-regression trigger) is 0 for both
    orderings — the phase is NOT `[BLOCKED]`.
- **Measurement D (invariant damage) — as predicted, with one reassuring result.**
  - (i) **Global `keysDistinct` is broken**: in **63 of 8532** formulas (0.74%), two distinct
    worlds are recorded with equal keys at some reachable state — confirming report 01/02's
    prediction that ancestor-only blocking does not preserve the global freshness invariant.
  - (ii) **Max spine depth observed**: 6 (across the whole corpus, ancestor-ordered driver,
    short-circuit-visited leaves only).
  - (iii) **Max out-degree observed**: 3.
  - (iv) **Upward box-propagation test** (`∀ψ, T(□ψ)@src ∈ b → T(□ψ)@wBlock ∈ b` for every
    blocked redirect): **1374 pass, 0 fail**, across every blocked redirect encountered on every
    visited leaf in the whole corpus. Every observed ancestor-restricted redirect satisfied the
    obligation Phase 2's decision-gate lemma needs — a positive empirical signal for that gate,
    though (per report 01's own caveat, repeated here) absence of failure at size <= 6 is not
    evidence of validity at any size: `cex` itself is size 19 and was excluded from this sweep.

**Overall verdict**: no `[BLOCKED]` trigger. The ancestor-only route is empirically viable to
continue past Phase 2's decision gate: soundness is restored on the known counterexample,
validity is preserved on the three control axioms, the differential sweep shows zero
completeness or soundness regressions (with a small, ordering-dependent termination cost that
disappears under settled-context scheduling), and the box-propagation obligation Phase 2 must
prove held in every one of 1374 observed instances.

### Phase 2: Decision gate — the ancestor back-edge justification lemma [BLOCKED]

- **Goal:** Prove, or fail to prove, the one obligation the whole route rests on, as a **standalone
  lemma with no driver dependency**: adding an edge `src -> a` where `a` is a spine ancestor of
  `src` and `a`'s recorded key equals the prospective successor's birth content preserves
  `branchSatisfiableIn s4FC`.
- **Tasks:**
  - [x] State the lemma in `FrameSoundness.lean` over abstract hypotheses (a spine chain from `a`
        to `src`, key equality, `keyLowerBd`), with **no** dependence on any driver definition.
        Landed as `branchSatisfiableIn_s4FC_ancestor_redirect` (`FrameSoundness.lean:1220`),
        single-hop case (`hanc : acc.hasEdge a src = true`; the general multi-hop spine case is a
        strict generalization and is foreclosed a fortiori by this base case's blocker).
  - [x] Attempt the cluster construction: S4 frames admit cycles, so take the model's relation to
        be the reflexive-transitive closure of the spine edges **plus** the back-edge, collapsing
        `a..src` into a cluster, and discharge the resulting box-propagation obligation.
        Attempted (case split on whether the ambient witness already relates `f src`/`f a`); see
        `#### Phase 2 Verdict` below for exactly where it breaks.
  - [x] Evaluate `blockedRedirect_boxctx_mem_of_boxOrigin` (`LoopChecking.lean:1466`) and
        `blockedRedirect_diaNeg_mem_of_diaOrigin` (`:1506`) as starting points before writing a
        fresh lemma — both are true, sorry-free, and conditional on exactly a box-origin fact.
        Evaluated (read in full): both require the edge `u → wBlock` to be **already recorded**
        in `acc` before they can fire, so they characterize *syntactic* branch-content transfer
        available *after* a redirect edge exists, not a route to justifying the edge's own
        addition to `acc` in the first place. Not reusable for this lemma's actual obligation.
  - [ ] **Not reached** — the predicted "unwrapped box-context" failure mode did not occur; the
        proof reached a **deeper, prior obstruction** (see verdict below) that boxed birth
        content does not fix, so no Phase 2b is added.
  - [x] Record the verdict in this plan under `#### Phase 2 Verdict`, resolving the two
        NOT-YET-VERIFIED rows of the mapping table.
- **Estimated output:** ~150-300 lines of Lean.
- **Done when:** the lemma is sorry-free and `lake build Cslib.Logics.Modal.Tableau.FrameSoundness`
  is clean, **or** the phase is marked `[BLOCKED]` with the exact goal state, the tactic attempts
  made, and the specific missing fact. A `[BLOCKED]` outcome here means the route does not close and
  must be escalated to the user before Phase 3 — **the plan must not be sequenced around it.**
- **Escalation branch:** if the blocker is that the ancestor discipline's literature basis is
  genuinely needed and Massacci's treatment (Technique 8.2 / Def 8.2 / Prop 8.1 / Pruning Lemma 8.2,
  all read and cited in the mapping table) is insufficient, **stop and make acquiring `Gore1999`
  an explicit new phase** rather than proceeding on a guess.
- **Timing:** 3-4 hours
- **Depends on:** 1

#### Phase 2 Verdict

**BLOCKED. The ancestor-only route does not close.** The decision-gate lemma
`branchSatisfiableIn_s4FC_ancestor_redirect` (`Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1220`)
is stated over abstract, driver-independent hypotheses (a recorded ancestor edge `a → src`, and
`hboxback`/`hdianeg`: `a` already contains, unwrapped, every box-positive/diamond-negative fact
recorded at `src` — the exact semantic content `S4LoopInv.keyLowerBd` composed with the guard's
key-equality check would hand a caller). It is **not sorry-free**; one `sorry` remains at
`FrameSoundness.lean:1244`, and `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` is
otherwise clean (this is the only new sorry; the file had zero before this dispatch).

**Exact goal state at the blocker** (`lean_goal` at `FrameSoundness.lean:1244`, case `hdirect :
¬m.r (f src) (f a)`, i.e. the ambient witness model does *not* already relate the two points):

```
case neg
Atom : Type v
b : List (SignedFormula (Proposition Atom) WorldIndex)
acc : Accessibility
src a : WorldIndex
hanc : acc.hasEdge a src = true
hboxback :
  ∀ (ψ : Proposition Atom),
    { sign := Sign.pos, formula := □ψ, label := src } ∈ b → { sign := Sign.pos, formula := ψ, label := a } ∈ b
hdianeg :
  ∀ (ψ : Proposition Atom),
    { sign := Sign.neg, formula := ◇ψ, label := src } ∈ b → { sign := Sign.neg, formula := ψ, label := a } ∈ b
W : Type
m : Model W Atom
f : WorldIndex → W
hrefl : Std.Refl m.r
htrans : IsTrans W m.r
hedges : ∀ (w w' : WorldIndex), acc.hasEdge w w' = true → m.r (f w) (f w')
hb :
  ∀ sf ∈ b,
    (sf.sign = Sign.pos → Satisfies m (f sf.label) sf.formula) ∧
      (sf.sign = Sign.neg → ¬Satisfies m (f sf.label) sf.formula)
hdirect : ¬m.r (f src) (f a)
⊢ branchSatisfiableIn (fun {World} => s4FC) b (acc.addEdge src a)
```

**Why this is not dischargeable, and why it is a deeper obstruction than the predicted
"unwrapped box-context" failure mode.** The predicted failure (boxed vs. unboxed `keyLowerBd`
content) never actually arises, because the proof gets stuck one step earlier:

1. `branchSatisfiableIn`'s witness `(W, m, f)` is **existentially arbitrary** — nothing in its
   definition constrains `m.r` to equal the transitive closure of `acc`. The `hdirect` case
   (the ambient model does not already relate `f src`/`f a`) is therefore not vacuous and must
   be handled by genuinely extending `m.r`.
2. `s4FC`'s `IsTrans` conjunct binds the **concrete relation** `m.r`, not some derived
   provability notion, so any extension of `m.r` that adds the pair `(f src, f a)` must be
   closed under transitivity to remain a valid witness. That closure is forced to include, for
   *every* `x` with `m.r x (f src)` (not just `x = f src` itself) and every `y` with
   `m.r (f a) y`, the new pair `(x, y)`.
3. Because `m.r` is unconstrained beyond the (one-directional) `hedges` lower bound, the set of
   such `x` is not limited to `src`'s recorded spine ancestors — the ambient model may relate
   `f src` to images of *other* worlds via relatedness `acc` never records. Discharging `hb` for
   the closure's new pairs would require box/diamond content transfer from *every* such `x` to
   `a`, and `hboxback`/`hdianeg` (the only hypotheses a standalone, no-driver lemma can carry)
   speak only about `src` itself. No enrichment of those two hypotheses closes this gap without
   either (a) a full Hintikka/canonical-model truth lemma built from the branch's own
   saturation invariants (driver-dependent, and exactly the scope this lemma was required to
   exclude), or (b) an assumption that the witness model is canonical/minimal, which
   `branchSatisfiableIn`'s existential definition does not provide.
4. **This is not a new phenomenon.** It is the same obstruction already documented in this file's
   own module comment introducing `branchPropAdequateIn` (`FrameSoundness.lean`, ~30 lines below
   the new lemma): a redirect edge to an **existing, reused** world "breaks
   `branchSatisfiableIn`'s edge conjunct... outright", which is precisely why `branchPropAdequateIn`
   (a strictly weaker invariant) was invented for Route P. Ancestor-only blocking redirects to an
   existing world in exactly the same shape Route P did; restricting the *target* to a spine
   ancestor changes nothing about *this* obstruction, which is about the existential looseness of
   the witness model, not about which world is targeted.

**Mapping table resolution** (the two `NOT-YET-VERIFIED — Phase 2 gate` rows, originally at
lines 178-179):

| Claim | Verdict |
|---|---|
| An ancestor back-edge `src -> wBlock` is model-justifiable, i.e. `branchSatisfiableIn s4FC` survives adding it | **REFUTED (as a standalone, driver-independent lemma).** `branchSatisfiableIn_s4FC_ancestor_redirect` reaches an unresolvable proof obligation (see goal state above); the "upward relation" gap the plan's overview flagged (§"The Single Load-Bearing Risk") is real and is not closed by the abstract hypotheses available. Measurement D(iv)'s 1374/1374 empirical pass (Phase 1) was correctly flagged there as non-binding at size <=6, and does not survive contact with the general proof obligation. |
| The ancestor route closes without the boxed-birth-content refinement | **MOOT.** The boxed-birth-content refinement (Phase 2b) was never reached: the proof does not get far enough for the boxed-vs-unboxed distinction to matter. Adopting boxed birth content would strengthen `hboxback`/`hdianeg` to already-boxed conclusions, but does nothing about the actual blocker (arbitrary ambient predecessors of `src` outside the recorded spine), so Phase 2b would not unblock this route either. |

**Consequence for the plan.** Per this phase's own "Done when" clause, `[BLOCKED]` here means
**the route does not close and must be escalated to the user before Phase 3.** Phases 3-14 (the
spine data component, guard, depth/branching bounds, driver, invariant, and cleanup) are **not
sequenced** — none of that work is scaffolded around this unresolved gate, consistent with the
instruction not to soften a `[BLOCKED]` verdict into a partial success. The `Gore1999` escalation
branch (missing paywalled reference) does **not** apply: the blocker is not that Massacci's
treatment is insufficient as a literature basis (Massacci's Prop 8.1 / Technique 8.2 / Pruning
Lemma 8.2 were read and are exactly what this plan's overview already correctly characterized as
supplying only the *free* ancestor->descendant direction); it is a structural fact about how
`branchSatisfiableIn` is encoded here (existentially arbitrary witness models), independent of
which paper is consulted. Escalating to the user is the appropriate next step, not a literature
acquisition phase.

### Phase 3: Spine data component, ancestor computation, and its tying invariant [NOT STARTED]

- **Goal:** Land `spine` as an explicit child -> parent record, a terminating decidable ancestor
  test, and the invariant tying it to `keys`/`acc` — reusing the `keysOriginS4` family rather than
  re-deriving it.
- **Tasks:**
  - [ ] `def spineParent : List (WorldIndex × WorldIndex)` (child, parent), plus
        `spineAncestors` computing the chain by following parent links, with termination from
        `parent < child`.
  - [ ] `def isSpineAncestor` (decidable) and its two basic lemmas: membership is transitive along
        the chain, and every ancestor has a strictly smaller index.
  - [ ] `def spineWellFormed` tying `spineParent` to `keysOriginS4` (`:1279`) and to `acc`: every
        recorded parent edge is an `acc` mint edge, and the root has no parent
        (`keysRootEmpty`, `:2009`).
  - [ ] Verify against source that `keysOriginS4`'s witness disjunct supplies exactly the parent
        datum needed; if it does not, record the gap rather than assuming it.
- **Estimated output:** ~200 lines.
- **Done when:** all new declarations are sorry-free, `lake build
  Cslib.Logics.Modal.Tableau.LoopChecking` is clean, and no existing declaration changed.
- **Timing:** 2-3 hours
- **Depends on:** 2

### Phase 4: Ancestor-restricted guard and its three contract lemmas [NOT STARTED]

- **Goal:** Land `blockingWorldS4Anc` beside `blockingWorldS4Keyed` with the three contract lemmas
  that the driver and the invariant consume.
- **Tasks:**
  - [ ] `def blockingWorldS4Anc φ₀ b keys spine s φ w` — as `blockingWorldS4Keyed` but filtering
        `keys` restricted to `w :: spineAncestors spine w`.
  - [ ] `blockingWorldS4Anc_eq_birthContent` (the `some` contract) and
        `blockingWorldS4Anc_mem_ancestors` (the returned world is on the source's spine — the fact
        Phase 14 consumes).
  - [ ] `blockingWorldS4Anc_none_fresh_spine`: `none` implies the prospective birth content differs
        from every **spine-ancestor's** recorded key. Transcribe `:544-555`'s proof.
  - [ ] Update the `blockingWorldS4Keyed` docstring's `:491-497` "no reachability restriction"
        passage to point at this repair (leave the defect description as historical record).
- **Estimated output:** ~180 lines.
- **Done when:** sorry-free, scoped build clean, and `blockingWorldS4Keyed` and all its lemmas are
  byte-for-byte unchanged.
- **Timing:** 2 hours
- **Depends on:** 3

### Phase 5: Spine depth bound from key distinctness along a chain [NOT STARTED]

- **Goal:** Prove `spineAncestors spine w` has length at most `modalWorldBoundS4 φ₀`, by
  re-instantiating `modalKnownWorlds_length_le_worldBoundS4`'s powerset injection on a chain.
- **Tasks:**
  - [ ] `def keysDistinctAlongSpine` — for `w` and any `w'` on `w`'s ancestor chain with recorded
        keys `k, k'`, `w ≠ w'` implies `k ≠ k'`.
  - [ ] `spineAncestors_nodup` (indices strictly decrease along the chain).
  - [ ] `spineDepth_le_worldBoundS4`: inject the chain's keys into `(signedSubfmls φ₀).powerset`
        via `keysInUniverse`, injectivity from `keysDistinctAlongSpine`, cardinality via
        `Finset.card_le_card_of_injOn` and `signedSubfmls_powerset_card_le` (`:323`) — the same
        four-step shape as `:6470-6491`.
- **Estimated output:** ~180 lines.
- **Done when:** sorry-free and scoped build clean. No driver change in this phase.
- **Timing:** 2-3 hours
- **Depends on:** 2

### Phase 6: Out-degree (branching) bound from `outDegEq` [NOT STARTED]

- **Goal:** Prove each world's number of spine children is at most `(signedSubfmls φ₀).card`,
  independently of any world bound (so the argument is not circular).
- **Tasks:**
  - [ ] `outDeg_le_signedSubfmls_card`: from `S4LoopInv.outDegEq` (`:7061`), `eNodup` and
        `eClosure`, the minting-shaped formulas of `e` at a given label are distinct elements of a
        set injecting into `signedSubfmls φ₀`.
  - [ ] `spineChildren_le_outDeg`: every spine child of `w` corresponds to a distinct minting-shaped
        formula at `w`, so the child count is bounded by `outDeg`.
  - [ ] Verify explicitly that neither lemma consumes any world bound — this non-circularity is the
        reason the phase exists separately.
- **Estimated output:** ~180 lines.
- **Done when:** sorry-free, scoped build clean, and a comment records the non-circularity check.
- **Timing:** 2-3 hours
- **Depends on:** 2

### Phase 7: Tree-count world bound `modalWorldBoundS4Tree` [NOT STARTED]

- **Goal:** Combine Phases 5 and 6 into a world-count bound and define the replacement universe and
  fuel constants over it.
- **Tasks:**
  - [ ] `def modalWorldBoundS4Tree φ₀ := geomCap ((signedSubfmls φ₀).card + 1) (modalWorldBoundS4 φ₀)`
        (exact shape to be fixed by what the counting lemma actually yields, using
        `Cslib/Foundations/Logic/Tableau/Measure.lean:57`).
  - [ ] `modalKnownWorlds_length_le_worldBoundS4Tree`: depth bound (Phase 5) plus branching bound
        (Phase 6) give the tree count. Use K's `modalMaxWorld_lt_worldBound_of_phiBound`
        (`CompletenessLoop.lean:199-227`) and `geomCap_le_pow` (`Measure.lean:94`) as the closing
        calc template. **Do not** attempt to reuse K's `rankEdge` (`FmpMeasure.lean:2340`)
        unmodified — it is an exact equality over all `acc` edges and is false for back-edges; tie
        any rank map to spine edges only.
  - [ ] `modalStepBranchS4Anc_worldBound`: the strict bound
        `modalMaxWorld b < modalWorldBoundS4Tree φ₀`, combining the above with `worldsContiguousS4`
        (`:6051`) exactly as `:6501-6520` does.
  - [ ] Re-derive `modalUniverseS4` and `modalFuelS4` over the new bound (both are parametric in it;
        `modalUniverseS4_length_le` at `:245` is mechanical).
- **Estimated output:** ~300 lines. **If the counting lemma alone exceeds this, split into 7.1
  (counting) and 7.2 (universe/fuel re-derivation) rather than growing the phase.**
- **Done when:** sorry-free and `lake build` clean project-wide (this phase changes constants that
  downstream files consume).
- **Timing:** 4 hours
- **Depends on:** 5, 6

### Phase 8: Spine-threading ancestor driver `modalStepBranchS4KeyedAnc` [NOT STARTED]

- **Goal:** Land the ordered, ancestor-restricted stepper beside `modalStepBranchS4KeyedOrdered`,
  threading `spine` as a fifth state component.
- **Tasks:**
  - [ ] `def modalStepBranchS4KeyedAncBody` and `def modalStepBranchS4KeyedAnc`, mirroring
        `:1107-1117`'s two-stage shape (`modalNonMintCandidates` scan, then fallback), with
        `blockingWorldS4Anc` at the two minting shapes and `spine` extended on every unblocked mint.
  - [ ] `modalStepBranchS4KeyedAnc_cases` — the structural split every Phase 9 lemma factors
        through, transcribing `:1124`.
  - [ ] `modalStepBranchS4KeyedAnc_selected_mem` and the result/`acc` relation lemma, reusing
        `modalStepBranchS4Keyed_result_acc_eq` (`:2406`).
- **Estimated output:** ~300 lines.
- **Done when:** sorry-free, scoped build clean, and the ordered stepper is unchanged.
- **Timing:** 3 hours
- **Depends on:** 4, 7

### Phase 9: `S4LoopInvAnc` and its per-step preservation [NOT STARTED]

- **Goal:** Land the ancestor invariant — nine `S4LoopInv` fields carried over, `keysDistinct`
  replaced by `keysDistinctAlongSpine`, plus `spineWellFormed` — and prove it is preserved by one
  `modalStepBranchS4KeyedAnc` step.
- **Tasks:**
  - [ ] `structure S4LoopInvAnc` over `(b, e, acc, keys, spine)`.
  - [ ] Per-field preservation, transcribing the landed ordered-driver lemmas
        (`modalStepBranchS4KeyedOrdered_preserves_*`) for the nine unchanged fields.
  - [ ] `keysDistinctAlongSpine` preservation from `blockingWorldS4Anc_none_fresh_spine` — the
        analogue of `keysUpdate_preserves_keysDistinct` (`:566`).
  - [ ] `spineWellFormed` preservation, reusing
        `modalStepBranchS4KeyedOrdered_preserves_keysOriginS4` (`:4775`) and the fourth conjunct of
        `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` (`:7667-7688`).
  - [ ] `bClosure`'s two minting cases via `modalStepBranchS4Anc_worldBound` (Phase 7).
- **Estimated output:** ~400 lines. **If the ten fields do not fit one dispatch, split into 9.1
  (the nine transcribed fields) and 9.2 (`keysDistinctAlongSpine` + `spineWellFormed` + `bClosure`)
  rather than growing the phase.**
- **Done when:** the full-invariant preservation theorem is sorry-free and scoped build is clean.
- **Timing:** 4 hours
- **Depends on:** 8

### Phase 10: Universe closure and the strict world bound on the new basis [NOT STARTED]

- **Goal:** Close the loop between Phase 7's bound and Phase 9's invariant, so every branch formula
  is in `modalUniverseS4` at every reachable state of the ancestor driver.
- **Tasks:**
  - [ ] `modalStepBranchS4KeyedAnc_preserves_bClosure` assembled over `modalWorldBoundS4Tree`.
  - [ ] The entry-state instance: the seed `([F(φ₀)@0], [], ∅, [(0,∅)], [])` satisfies
        `S4LoopInvAnc`.
  - [ ] Verify (do not assume) that no landed lemma consuming `modalUniverseS4` broke when its
        world range grew in Phase 7.
- **Estimated output:** ~200 lines.
- **Done when:** sorry-free and `lake build` clean project-wide.
- **Timing:** 2-3 hours
- **Depends on:** 9

### Phase 11: Fuel sufficiency for the ancestor driver [NOT STARTED]

- **Goal:** Re-derive the fuel bound over `modalWorldBoundS4Tree`.
- **Tasks:**
  - [ ] `modalExpMeasure_entry_le_fuelS4Anc`, transcribing `:8486` with the new constants.
  - [ ] The per-step measure-decrease lemma for `modalStepBranchS4KeyedAnc`.
  - [ ] Record explicitly that this is a **completeness** property, not a termination one
        (audit §6): Lean-level termination is structural on `fuel` and is not at risk.
- **Estimated output:** ~250 lines.
- **Done when:** sorry-free and scoped build clean.
- **Timing:** 3 hours
- **Depends on:** 10

### Phase 12: Driver and entry point `modalTableauS4KeyedAnc` [NOT STARTED]

- **Goal:** Land `modalExpandBranchesS4KeyedAnc` and the `modalTableauS4KeyedAnc` entry point.
- **Tasks:**
  - [ ] `def modalExpandBranchesS4KeyedAnc`, structural on `fuel`, transcribing `:7830`'s shape —
        no `termination_by` should be needed; if the checker complains, that is a finding to record,
        not a licence to add an axiom.
  - [ ] `def modalTableauS4KeyedAnc φ₀` at `modalFuelS4` over the new bound.
  - [ ] Confirm the `fuel = 0` arm returns `.closed` only from genuine closure checks.
- **Estimated output:** ~200 lines.
- **Done when:** sorry-free, `lake build` clean project-wide, `lake test` green.
- **Timing:** 2-3 hours
- **Depends on:** 11

### Phase 13: Empirical gate for the landed driver [NOT STARTED]

- **Goal:** Re-run Phase 1's four measurements against the **landed** driver (not the probe) and
  commit them as a regression test.
- **Tasks:**
  - [ ] Extend `CslibTests/S4LoopGuardRegression.lean` with: `modalTableauS4KeyedAnc cex` is OPEN;
        the T/4/K axiom instances are CLOSED; the shipped unordered driver still closes `cex`
        (documented unsoundness unchanged).
  - [ ] Re-run the 8532-formula differential sweep against the landed driver and record
        `open -> closed` (gate: 0) and `closed -> open` counts against the 1650/6882/0 baseline.
  - [ ] Record the measured numbers in the implementation summary. **Measure; do not reason about
        what the sweep would produce.**
- **Estimated output:** ~150 lines of test code plus a measurement record.
- **Done when:** `lake test` green and all measurements recorded as numbers. A non-zero
  `open -> closed` count is a soundness regression and blocks the phase.
- **Timing:** 2-3 hours
- **Depends on:** 12

### Phase 14: Soundness assembly and retirement of the weakened invariant [NOT STARTED]

- **Goal:** Prove `modalTableauS4KeyedAnc_sound` against `s4FC` using Phase 2's justification lemma,
  and retire `branchPropAdequateIn` now that `branchSatisfiableIn` suffices.
- **Tasks:**
  - [ ] `branchSatisfiableIn` preservation across an ancestor-restricted redirect step, consuming
        Phase 2's lemma and `blockingWorldS4Anc_mem_ancestors`.
  - [ ] `branchSatisfiableIn` preservation across a mint step and the twelve non-minting shapes
        (transcribe the landed `branchSatisfiableIn` machinery).
  - [ ] `modalTableauS4KeyedAnc_sound : modalTableauS4KeyedAnc φ₀ = .closed → s4Valid φ₀`.
  - [ ] **Gated on Phase 2's verdict having been positive**: delete `branchPropAdequateIn`
        (`FrameSoundness.lean:1183`) and its four `hready`-carrying consumers (`:1241`, `:1275`,
        `:1310`, `:1334`), plus `branchSatisfiableIn_imp_branchPropAdequateIn` (`:1203`), each
        removal site carrying an inline comment recording that ancestor-only blocking made the
        weakened invariant unnecessary. Run scoped `lake shake` afterwards.
  - [ ] If Phase 2's verdict was negative, this deletion does **not** happen and the phase reports
        the divergence instead.
- **Estimated output:** ~400 lines. **If the soundness assembly and the retirement do not fit one
  dispatch, split into 14.1 (assembly) and 14.2 (retirement) rather than growing the phase.**
- **Done when:** `modalTableauS4KeyedAnc_sound` is sorry-free, `lean_verify` reports no new axioms
  (count still 26), and the full CI pipeline is green.
- **Timing:** 4-5 hours
- **Depends on:** 12

---

## Testing & Validation

- [ ] `lake build` clean project-wide at every phase boundary.
- [ ] `lake test` green, including `CslibTests.S4LoopGuardRegression`.
- [ ] `lake lint` shows exactly one error (the `Cslib/Logics/Temporal/Tableau/Saturation.lean`
      baseline) and no others.
- [ ] `lake exe checkInitImports` clean.
- [ ] `lake exe lint-style` clean.
- [ ] `lake exe mk_all --module` reports no update necessary (`Cslib.lean` must stay untouched —
      concurrent session territory).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` on each touched file: zero findings.
- [ ] `grep -c '^axiom' ` over `Cslib/` returns **26**.
- [ ] Standalone `sorry` count in `Cslib/Logics/Modal/Tableau/` is **0**; repo census is **40**.
- [ ] Empirical gates: Phase 1 and Phase 13 both report `open -> closed = 0` on the 8532-formula
      sweep, `cex` OPEN, and the T/4/K axiom instances CLOSED.

## Artifacts & Outputs

- `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/03_ancestor-only-blocking.md`
  (this file)
- `specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4ancestor.lean` (Phase 1)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (Phases 3-12)
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (Phases 2, 14)
- `CslibTests/S4LoopGuardRegression.lean` (Phase 13)
- `specs/553_.../summaries/03_ancestor-only-blocking-summary.md` (on completion)
- `specs/553_.../.orchestrator-handoff.json` (per dispatch)

## Rollback/Contingency

- Every phase lands beside existing declarations rather than replacing them, so reverting any phase
  is a targeted deletion of new declarations plus a scoped `lake shake`. Phase 7 is the one
  exception (it changes `modalUniverseS4`/`modalFuelS4` constants) — snapshot via
  `bash .claude/scripts/git-snapshot.sh` before starting it.
- Phase 2 `[BLOCKED]` is a route-level stop, not a rollback: Phase 1's probe and measurements
  remain valuable, and the escalation is to the user with the exact goal state.
- Phase 14's retirement of `branchPropAdequateIn` is the only destructive step in the plan and it is
  gated on Phase 2's positive verdict. If it must be reverted, the declarations are recoverable from
  git history at the commit preceding Phase 14.
