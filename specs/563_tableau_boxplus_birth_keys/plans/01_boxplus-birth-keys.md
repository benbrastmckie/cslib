# Implementation Plan: Box-Plus Birth Keys for the Keyed S4 Loop Guard

- **Task**: 563 - Adopt Lemmon box-plus pairing at the birth-key level
- **Status**: [NOT STARTED]
- **Effort**: 10.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/563_tableau_boxplus_birth_keys/reports/01_boxplus-birth-keys.md`
- **Artifacts**: plans/01_boxplus-birth-keys.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Enrich the keyed S4 loop guard's birth keys so that every transmitted box-context pair records
BOTH members — `(pos, ψ)` *and* `(pos, □ψ)` for each `T(□ψ)@w` on the branch, dually `(neg, ψ)`
and `(neg, ◇ψ)` for each `F(◇ψ)@w`. The enrichment cannot land alone: `keyLowerBd`'s minting
obligation is a subset relation into `relevantSetFinset`, which is literal branch membership, so
adding `(pos, □ψ)` to a key requires `T(□ψ)@w'` to actually be on the branch at mint time. The
mint payload therefore changes in the same landing, additively, inside `modalApplyOneS4Keyed` —
never in `Rules.lean`. Definition of done: `lake build Cslib` green, Modal/Tableau sorry census
still exactly 1, zero axioms, and the two `blockedRedirect_boxed_*_mem` payoff lemmas landed
sorry-free.

### Research Integration

The plan is built on `reports/01_boxplus-birth-keys.md` and adopts its findings wholesale. The
five load-bearing ones, each of which shapes a phase below:

1. **The mint payload is load-bearing** (report §4). Enriching `successorBirthContent` alone makes
   `keyLowerBd`'s minting case FALSE, not merely hard. Phases 2-3 land the payload change *before*
   Phase 4 touches the key, with a green build between them.
2. **`Rules.lean` MUST NOT be edited** (report §4.2). `modalApplyOne` is shared by the K/T/B/S5
   drivers and by `FmpMeasure.lean`'s `_gen` lemmas; boxed transmission is not K-sound. The boxed
   arm replaces the two `| none => modalApplyOne sf b acc` fallthroughs inside
   `modalApplyOneS4Keyed` (`LoopChecking.lean`, `def modalApplyOneS4Keyed`).
3. **Both-members, not boxed-only** (report §3). The `specs/553_.../artifacts/s4boxed.lean`
   variant *replaces* `(pos, ψ)` with `(pos, □ψ)`, which would falsify the two landed sorry-free
   lemmas `blockedRedirect_unwrapped_boxPos_mem` and `blockedRedirect_unwrapped_diaNeg_mem`. The
   task's both-members reading is a strict superset and preserves them. Take the task's reading.
4. **`BoxPlusClosed` must be filter-scoped** (report §5.2). A universally quantified
   `∀ p ∈ k, boxPlusPair p ∈ k` is FALSE — the witness pair enters by `insert` and satisfies
   neither closure direction. Use the report §5.2 shape, scoped to the transmitted box-context.
5. **Additive mint shape** (report §5.3). Emit `modalApplyOne`'s own payload `++ boxPlusExtraS4`,
   never an interleaved rewrite. Existing membership proofs into the payload are
   `List.mem_append_left` / `List.mem_cons_of_mem` chains that survive with one extra wrapper
   under `old ++ extra` but must be re-derived under a rewrite. Worth ~20 proof bodies.

The report's empirical measurements are treated as evidence, not as a substitute for proof: the
8532-formula keyed sweep is verdict-neutral with 0 fuel exhaustion, and the live sweep is
strictly better (fuel exhaustion 893 -> 412, 0 verdict changes, 0 unsound `none`->closed). This
downgrades risk R2 to low but does not discharge any proof obligation.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `specs/ROADMAP.md` consulted for this task (no `roadmap_path` in the delegation context).

## Goals & Non-Goals

**Goals**:
- Add `boxPlusPair`, `BoxPlusClosed`, `boxPlusExtraS4`, and `modalApplyOneS4KeyedMint` with its
  two unblocked-shape lemmas.
- Switch `modalApplyOneS4Keyed`'s two unblocked arms to the additive boxed mint payload.
- Enrich `successorBirthContent` with two appended disjuncts recording the boxed members.
- Repair every downstream proof sorry-free, including both `_preserves_keyLowerBd` variants.
- Land `blockedRedirect_boxed_boxPos_mem` / `blockedRedirect_boxed_diaNeg_mem` — the payoff.
- Demonstrate (not assume) that `modalTableauS4Keyed_complete` transports, via a real build.

**Non-Goals**:
- Editing `Cslib/Logics/Modal/Tableau/Rules.lean` in any way. Hard prohibition.
- Lifting box-plus into `Foundations/`. Box-plus is S4-scoped: the Lemmon filtration and
  Chagrov-Zakharyaschev Proposition 3.6 are stated for transitive models only, satisfied by
  `s4FC`. (Report §10 flags that neither source is in the local literature corpus, so the
  attribution is carried forward rather than verified; the in-tree justification via
  `modalFourBoxProp` and `s4FC` transitivity is self-contained and sufficient.)
- Enlarging the filter `Σ`. That changes the codomain and is expensive. Enrich with box-plus,
  not with the filter.
- Adding `BoxPlusClosed` as an `S4LoopInv` / `S4KeyedHintikkaInv` *field* (see risk R3).
- Adding any `sorry` or vacuous definition. If Phase 5's gate cannot be repaired sorry-free the
  task exits `[BLOCKED]`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: `keyLowerBd`'s minting case is FALSE without the payload change (report §4) | H | H (certain if ordering inverted) | Phase ordering is the mitigation: payload (P2-P3) lands and builds green BEFORE the key changes (P4). Never reorder. |
| R2: live guard `blockingWorldS4` is collateral — enriching in place changes `modalApplyOneS4`, `modalTableauS4`, and the live row of `CslibTests/S4LoopGuardRegression.lean` | M | L (measured) | Measured closed: 0 verdict changes / 0 unsound closures across 8532 formulas, strictly fewer fuel exhaustions. Fallback retained but not expected: a separate `successorBirthContentPlus` consumed only by `blockingWorldS4Keyed`. |
| R3: field-count churn in `S4LoopInv`/`S4KeyedHintikkaInv` breaks `modalTableauS4Keyed_initial`'s positional `refine` in `FrameCompleteness.lean` | H | L (avoidable by design) | Do NOT add a `BoxPlusClosed` field. Keep it a derived lemma threaded as an extra hypothesis, the same treatment `keysOriginS4` and `keysRootEmpty` already receive. This keeps `FrameCompleteness.lean` at zero edits. |
| R4: regression-test verdict assertions in `CslibTests/S4LoopGuardRegression.lean` change | M | L (measured) | All six `#guard_msgs in #eval` rows are verdict-only and all keyed rows are measured preserved. The one live-driver row is R2's exposure. See the scope note below — this file is outside the declared `file_scope`. |
| R5: step count grows; `modalFuelS4` sufficiency | L | L | World bound is provably unchanged (`modalSubfmls (.box a) = .box a :: modalSubfmls a`), so the pigeonhole chain and `modalFuelS4` transport. Fuel exhaustion measured 0/8532 at fuel 100 in both orderings. |
| R6: `hintikka_congr_S4`'s `simp_all [modalApplyOneS4Keyed]` breaks under the new mint arm | M | M | Its argument does not change shape (`modalHintikkaSetGen`'s conjunct 2 is literal `True` at both mint shapes). Budgeted explicitly in Phase 6, not assumed free. |
| R7: the mandatory gate fails and cannot be repaired sorry-free | H | L | Phase 5 is a dedicated decision point with a stated blocked-exit. Do NOT add a sorry; do NOT substitute a vacuous definition. Record the goal state reached and mark `[BLOCKED]`. |

### Scope Note: files outside the declared `file_scope`

The task's declared `file_scope` is `LoopChecking.lean`, `FmpMeasure.lean`,
`FrameCompleteness.lean`. Research measured that the only file with *executable* dependency on
the changed declarations is `Cslib/Logics/Modal/Tableau/LoopChecking.lean`; the hits in
`FrameSoundness.lean` (1), `FrameCompleteness.lean` (2), and
`CslibTests/S4LoopGuardRegression.lean` (3) are all inside docstrings or module comments. So
`FmpMeasure.lean` and `FrameCompleteness.lean` are expected to need **zero** edits, and the plan
does not budget any.

Two out-of-scope files could nonetheless be forced open:

- **`CslibTests/S4LoopGuardRegression.lean`** — outside the declared `file_scope`. Its one
  live-driver row (`cex` asserted OPEN via `modalExpandBranchesS4`) is R2's exposure. Measurement
  says it holds. **If it does not**, do not silently edit the assertion to match new behaviour:
  stop, report the changed verdict, and take the R2 fallback (`successorBirthContentPlus`
  consumed only by `blockingWorldS4Keyed`, leaving the live track untouched) instead.
- **`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`** — outside the declared `file_scope`, and
  the home of the one pre-existing sorry (line 1227) that the census baseline counts. It is
  prose-only w.r.t. this change and must not be edited.

Any edit to a file outside `{LoopChecking.lean, FmpMeasure.lean, FrameCompleteness.lean}` is a
scope escalation to be reported, not absorbed. `Rules.lean` is forbidden outright regardless.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel. This plan is fully sequential by
construction: R1 makes the payload-before-key ordering a correctness requirement, not a
convenience.

---

### Phase 1: Additive Definitions, No Behaviour Change [NOT STARTED]

**Goal**: Land `boxPlusPair`, `boxPlusExtraS4`, `modalApplyOneS4KeyedMint` and its two
unblocked-shape lemmas, all unreferenced by any existing declaration. Build stays green by
construction because nothing existing changes.

**Tasks**:
- [ ] Add `def boxPlusPair (p : Sign × Proposition Atom) : Sign × Proposition Atom` —
      `(pos, ψ) ↦ (pos, □ψ)`, `(neg, ψ) ↦ (neg, ◇ψ)` — per report §5.1, with a docstring noting
      that the *existing* `successorBirthContent` filter is already exactly
      "`boxPlusPair p` instantiated at `w` is on `b`".
- [ ] Add `def boxPlusExtraS4 (b) (w : WorldIndex) : List (SignedFormula ...)` per report §5.3:
      boxed positives from `boxPositivesOf b` filtered to source `w`, plus diamond-negatives at
      `w`, each retargeted to `modalNextWorld b`.
- [ ] Retain the per-formula dedup guard `if b.any (· == sf') then none else some sf'` in both
      halves — the freshness half of `modalApplyOneS4Keyed_persistentFresh_S4` and the measure
      argument both key off it.
- [ ] Add `def modalApplyOneS4KeyedMint` emitting `modalApplyOne sf b acc`'s own payload
      `++ boxPlusExtraS4 b sf.label`, preserving the accessibility component verbatim.
- [ ] Add the two unblocked-shape lemmas for `modalApplyOneS4KeyedMint`, shaped as drop-in
      replacements for `modalApplyOne_boxNeg_mint_fst_S4` and its diamond dual.
- [ ] Do NOT reference any of the above from existing code yet.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - four new definitions plus two shape lemmas,
  placed near `def modalApplyOneS4Keyed`.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` exit 0.
- No new sorry: `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness 2>&1 | grep -c "uses 'sorry'"`
  still 1.
- `grep -n "boxPlusPair\|boxPlusExtraS4\|modalApplyOneS4KeyedMint" Cslib/Logics/Modal/Tableau/LoopChecking.lean`
  shows definitions and their own lemmas only — no call site inside a pre-existing declaration.

---

### Phase 2: Switch the Mint Payload [NOT STARTED]

**Goal**: Point `modalApplyOneS4Keyed`'s two `| none =>` fallthroughs at
`modalApplyOneS4KeyedMint`, restate the two `_unblocked_eq` equation lemmas accordingly, and
migrate the name-swap-only call sites. The key stays unenriched, so `keyLowerBd` remains
provable — the key is now a subset of a strictly larger relevant set.

**Tasks**:
- [ ] Replace both `| none => modalApplyOne sf b acc` arms in `def modalApplyOneS4Keyed` with
      the `modalApplyOneS4KeyedMint` call. `Rules.lean` is not touched.
- [ ] Restate `modalApplyOneS4Keyed_boxNeg_unblocked_eq` and
      `modalApplyOneS4Keyed_diaPos_unblocked_eq` to conclude equality with
      `modalApplyOneS4KeyedMint ...` rather than `modalApplyOne ...`. Both proof bodies are
      `unfold modalApplyOneS4Keyed; simp [hblock]` today and are expected to survive.
- [ ] Migrate the Class-A (name-swap-only) call sites. These need the equation only to pin
      `result` and `.snd`; the accessibility component `acc.addEdge w (modalNextWorld b)` is
      unchanged and they never inspect the payload list. The families, for both the
      `modalStepBranchS4_*` and `modalStepBranchS4KeyedOrdered_*` variants:
      `_preserves_accFresh`, `_preserves_accKnown`, `_preserves_outDegEq`,
      `modalApplyOneS4Keyed_hasEdge_mono`, `_branchingLength_S4`, `_boxNeg_ne_notApplicable`,
      `_diaPos_ne_notApplicable`, `_preserves_keysTotal`, `_preserves_keysWorldsKnown`,
      `_preserves_keysOriginS4`.
- [ ] Confirm `modalApplyOneS4Keyed_persistentFresh_S4` is Class A despite its name: it
      constrains only `.persistent` results and the mint is `.linear`, so its mint arms merely
      derive `.linear ≠ .persistent`. If it turns out to inspect the payload, reclassify it into
      Phase 3 and say so rather than forcing it here.
- [ ] Leave every Class-B declaration failing for now — Phase 3 owns them. Do not partially
      repair them.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: interface

**Commit Mode**: atomic-batch

**Scope Hypothesis**: Research measured **50 call sites of the two `_unblocked_eq` lemmas across
23 enclosing declarations**, split **9 Class-A families (18 sites, name-swap only)** and
**6 Class-B families (12 sites) plus 3 content lemmas**. Confirm at implementation time before
relying on the split:
`grep -c "modalApplyOneS4Keyed_\(boxNeg\|diaPos\)_unblocked_eq" Cslib/Logics/Modal/Tableau/LoopChecking.lean`
for the site count (measured 50), and enumerate enclosing declarations with the report §6 `awk`
recipe. If the actual counts differ, record the corrected figures in the phase notes and
re-derive the A/B split from the actual list — do not carry the hypothesis forward as fact.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - `def modalApplyOneS4Keyed`, the two
  `_unblocked_eq` lemma statements, and the Class-A call sites.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` exit 0 (Class-B failures must NOT remain
  at the end of this phase — if any persist, the phase is `[PARTIAL]`, not green).
- Sorry count unchanged at 1.
- `grep -n "modalApplyOne sf b acc" Cslib/Logics/Modal/Tableau/LoopChecking.lean` no longer
  matches inside `def modalApplyOneS4Keyed`.
- `git diff --stat Cslib/Logics/Modal/Tableau/Rules.lean` is empty.

---

### Phase 3: Re-Prove the Class-B Payload Lemmas [NOT STARTED]

**Goal**: Repair every proof that genuinely inspects the mint payload, so the enlarged payload is
fully justified before any key changes. Each repair is a `List.mem_append` split whose left half
is the verbatim old proof.

**Tasks**:
- [ ] `modalApplyOne_boxNeg_outputs_subset_S4` and `modalApplyOne_diamondPos_outputs_subset_S4`:
      `List.mem_append` split; left half is the old proof unchanged, right half handles
      `boxPlusExtraS4`.
- [ ] `modalApplyOneS4Keyed_outputsSubsetUniverse_S4`: new `.linear` case for `boxPlusExtraS4`.
      Needs `.box ψ ∈ modalSubfmls φ₀` — immediate from the branch hypothesis plus
      `mem_boxPositivesOf` — and the `w' ≤ modalWorldBoundS4 φ₀` bound the existing proof already
      carries.
- [ ] `modalStepBranchS4_preserves_bClosure` and
      `modalStepBranchS4KeyedOrdered_preserves_bClosure`: consume the two `_outputs_subset_S4`
      lemmas above.
- [ ] `modalStepBranchS4_preserves_worldsContiguousS4` and
      `modalStepBranchS4KeyedOrdered_preserves_worldsContiguousS4`: the new formulas all sit at
      `modalNextWorld b`, already introduced by the witness, so no new world label appears and the
      extra case closes the same way.
- [ ] `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`: `eBoxNegWitness`/`eDiamondPosWitness`
      still need the witness `⟨.neg, ψ, w'⟩`, which remains the payload head under the additive
      shape; `hintikkaInv` is literal `True` at the mint shapes.
- [ ] Do not touch `successorBirthContent` in this phase.

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Research enumerates **6 Class-B families (12 sites) plus 3
`successorBirthContent_*` content lemmas**, of which this phase owns the 6 families and defers
the 3 content lemmas to Phase 4. Confirm by building after each repair: if a declaration outside
the enumerated set breaks, it was mis-classified in Phase 2 — record it and repair it here rather
than deferring.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - the six Class-B proof bodies listed above.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` exit 0.
- Sorry count still exactly 1, still at `FrameSoundness.lean:1227`.
- Each repaired proof commits individually once green (per-substep mandate).

---

### Phase 4: Enrich the Birth Key [NOT STARTED]

**Goal**: Append the two boxed-member disjuncts to `successorBirthContent`, add the
filter-scoped `BoxPlusClosed`, and repair the three `successorBirthContent_*` lemmas plus both
`_preserves_keyLowerBd` variants. This is the substantive obligation of the task.

**Tasks**:
- [ ] Extend `def successorBirthContent`'s filter with two APPENDED disjuncts (report §5.1),
      keeping the existing two disjuncts **first and syntactically verbatim**. Use the
      `match`-on-`p.2` form so the predicate stays decidable without an existential. Do NOT
      rewrite the existing disjuncts into `boxPlusPair` form — the `Or.inl ⟨rfl, …⟩` /
      `Or.inr ⟨rfl, …⟩` steps in four existing proofs match the current syntactic shape. Note the
      `boxPlusPair` reformulation in the docstring instead.
- [ ] Add `def BoxPlusClosed (φ₀) (b) (w) (k)` using the report §5.2 shape, **scoped to the
      transmitted box-context filter, never to the whole key**. A universally quantified
      `∀ p ∈ k, boxPlusPair p ∈ k` is false: the witness pair enters by `insert` and satisfies
      neither closure direction (mint from `F(□(□χ))@w` has witness `(neg, □χ)` with neither
      `(neg, χ)` nor `(neg, ◇□χ)` on the branch at birth). If a different shape is preferred, the
      constraint to respect is filter-scoping.
- [ ] Add `BoxPlusClosed` as a **derived lemma about `successorBirthContent`**, threaded as an
      extra hypothesis where needed — the same treatment `keysOriginS4` and `keysRootEmpty`
      already receive. Do NOT add it as an `S4LoopInv` or `S4KeyedHintikkaInv` field (risk R3:
      `modalTableauS4Keyed_initial`'s `refine` in `FrameCompleteness.lean` is positional).
- [ ] `successorBirthContent_boxNeg_subset_relevantSetFinset`: two new `rcases` arms, each the
      box-positive arm with `modalSubfmls_trans` REMOVED (the boxed pair is already in `Σ` by the
      membership hypothesis) and the target inside `boxPlusExtraS4`.
- [ ] `successorBirthContent_diamondPos_subset_relevantSetFinset`: the dual.
- [ ] `successorBirthContent_subset_signedSubfmls`: unchanged in substance — the new disjuncts
      still land in the `⟨hpmem, -⟩` branch. Confirm rather than assume.
- [ ] `modalStepBranchS4_preserves_keyLowerBd` and
      `modalStepBranchS4KeyedOrdered_preserves_keyLowerBd`: consume the two subset lemmas above.
- [ ] Verify the blocked-case witnesses survive verbatim:
      `modalStepBranchS4Keyed_blocked_witness_mem` derives its membership from
      `Finset.mem_insert_self` on the `insert (s, φ)` head, which is untouched; and
      `blockedRedirect_unwrapped_boxPos_mem` / `blockedRedirect_unwrapped_diaNeg_mem` land in the
      two disjuncts kept first and verbatim. If either breaks, the "keep existing disjuncts
      verbatim" constraint was violated — fix the definition, not the proof.

**Timing**: 2 hours

**Depends on**: 3

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts that exactly **3 `successorBirthContent_*` lemmas plus 2
`_preserves_keyLowerBd` variants** need repair, and that the two `blockedRedirect_unwrapped_*`
lemmas need **zero** edits. Confirm by building: if any declaration outside this set breaks, or
if either `blockedRedirect_unwrapped_*` lemma breaks, record the discrepancy explicitly — a
broken `blockedRedirect_unwrapped_*` specifically indicates the both-members reading was not
implemented as a strict superset and must be corrected at the definition, not worked around.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - `def successorBirthContent`, new
  `BoxPlusClosed` def and derived lemma, three `successorBirthContent_*` lemmas, both
  `_preserves_keyLowerBd` lemmas.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` exit 0.
- `git diff` shows no `S4LoopInv` / `S4KeyedHintikkaInv` field added and no edit to
  `FrameCompleteness.lean`.
- `blockedRedirect_unwrapped_boxPos_mem` and `blockedRedirect_unwrapped_diaNeg_mem` unchanged in
  the diff.
- Sorry count still exactly 1.

---

### Phase 5: The Mandatory Completeness Gate — Explicit Decision Point [NOT STARTED]

**Goal**: Demonstrate, by a real build rather than by argument, that `modalTableauS4Keyed_complete`
transports across the enriched keys. This phase exists as a standalone decision point precisely
because the task forbids assuming the transport.

**Tasks**:
- [ ] Run the gate: `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`.
- [ ] **If exit 0**: record the job count and the sorry-warning count/location, confirm the
      structural argument held (`modalHintikkaSetS4`'s conjunct 2 is literal `True` at the two
      mint shapes `| .neg, .box _ => True` / `| .pos, .diamond _ => True`, so neither the guard
      nor the payload is visible to Hintikka-set-hood there), and proceed to Phase 6.
- [ ] **If it breaks**: the completeness proof is quantified over driver behaviour
      (`modalExpandBranchesS4Keyed_hintikka`) and *should* transport, but that must be
      DEMONSTRATED. Attempt a sorry-free repair, time-boxed to this phase. The expected failure
      mode is field-count churn in `S4LoopInv`/`S4KeyedHintikkaInv` breaking
      `modalTableauS4Keyed_initial`'s positional `refine` — if that is the cause, the fix is to
      remove the added field (risk R3), not to renumber the `refine`.
- [ ] **Blocked exit (stated in advance)**: if the gate cannot be repaired sorry-free within this
      phase, mark the phase `[BLOCKED]` and the task `[BLOCKED]`, record the exact goal state
      reached and the failing declaration, and STOP. Do NOT add a `sorry`. Do NOT substitute a
      vacuous definition. Do NOT weaken a statement to make it close.
- [ ] The R2 fallback (`successorBirthContentPlus` consumed only by `blockingWorldS4Keyed`) is the
      sanctioned narrowing if and only if the LIVE track is the obstruction. It is not a narrowing
      of this phase's own obligation and must not be used to route around a genuine completeness
      failure.

**Timing**: 1.5 hours

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - only if repair is needed.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` - expected ZERO edits; any edit here is a
  signal that risk R3 materialized and should be reported explicitly.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` exit 0 at ~900 jobs.
- Exactly 1 `declaration uses 'sorry'` warning, at `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1227`.
- The gate outcome is recorded in the phase notes either way — a pass is stated with its
  evidence, a failure with its goal state.

---

### Phase 6: Payoff Lemmas and Full Gate Suite [NOT STARTED]

**Goal**: Land the two box-plus transfer lemmas the enrichment exists to enable, re-check
`hintikka_congr_S4`, and run the complete verification baseline.

**Tasks**:
- [ ] Add `blockedRedirect_boxed_boxPos_mem` and `blockedRedirect_boxed_diaNeg_mem` — each a
      short consequence of `keyLowerBd` plus the guard match, mirroring the derivation the
      existing `blockedRedirect_unwrapped_*` pair uses.
- [ ] Re-check `hintikka_congr_S4`: its body is `simp_all [modalApplyOneS4Keyed]` and the
      argument does not change shape, but the proof may need re-checking under the new mint arm.
- [ ] Run the full gate suite (below) and record every measurement against the baseline.
- [ ] Confirm no file outside `{LoopChecking.lean}` was modified; if
      `CslibTests/S4LoopGuardRegression.lean` needed an edit, report it as a scope escalation
      per the Scope Note rather than absorbing it.

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - two new payoff lemmas, `hintikka_congr_S4`
  proof body if needed.

**Verification**:
- `lake build Cslib` exit 0 at ~3313 jobs.
- Modal/Tableau sorry census exactly 1.
- Zero axioms in the subsystem (`lean_verify` / `#print axioms` on the touched theorems shows
  standard axioms only).
- `lake test` passes; all six `#guard_msgs in #eval` rows in
  `CslibTests/S4LoopGuardRegression.lean` hold unedited.
- `lake shake`: exit 1 with 9 findings, **none in Modal/Tableau**. Gate on "no Modal/Tableau
  findings AND count stays 9", never on shake exit 0.
- `checkInitImports` exit 0; `lint-style` exit 0.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Tableau.LoopChecking` exit 0 after Phases 1, 2, 3, 4.
- [ ] `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` exit 0 at ~900 jobs (Phase 5, the
      mandatory gate).
- [ ] `lake build Cslib` exit 0 at ~3313 jobs (Phase 6).
- [ ] Sorry census: exactly 1 across Modal/Tableau, at `FrameSoundness.lean:1227`, at every
      checkpoint. Any increase fails the phase.
- [ ] Zero axioms introduced in the subsystem.
- [ ] `lake test` green; the six regression verdict rows unedited.
- [ ] `lake shake` exit 1, 9 findings, none in Modal/Tableau.
- [ ] `checkInitImports` exit 0, `lint-style` exit 0.
- [ ] `git diff Cslib/Logics/Modal/Tableau/Rules.lean` empty at every phase.

## Artifacts & Outputs

- `specs/563_tableau_boxplus_birth_keys/plans/01_boxplus-birth-keys.md` (this file)
- `specs/563_tableau_boxplus_birth_keys/summaries/01_boxplus-birth-keys-summary.md`
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — new: `boxPlusPair`, `BoxPlusClosed`,
  `boxPlusExtraS4`, `modalApplyOneS4KeyedMint` + 2 shape lemmas,
  `blockedRedirect_boxed_boxPos_mem`, `blockedRedirect_boxed_diaNeg_mem`; modified:
  `modalApplyOneS4Keyed`, `successorBirthContent`, and the enumerated downstream proofs.

## Rollback/Contingency

- Each phase commits independently, so `git revert` of a phase's commit restores the previous
  green state. Phases 2 and 4 are `atomic-batch`, so each is a single revertible commit covering
  its whole file set.
- If Phase 5's gate fails irrecoverably: mark `[BLOCKED]`, leave the last green commit
  (end of Phase 4) in place, and record the failing declaration plus goal state. No sorry, no
  vacuous definition, no weakened statement.
- If the LIVE track (`blockingWorldS4` / `modalTableauS4` / the regression file's live row) is
  the obstruction rather than the keyed track: revert Phase 4's in-place enrichment of
  `successorBirthContent` and take the R2 fallback — a separate `successorBirthContentPlus`
  consumed only by `blockingWorldS4Keyed`. Cost: a duplicated definition and `Plus` twins for the
  two `blockedRedirect_unwrapped_*` lemmas; benefit: zero live-track risk. This narrows the
  blast radius, not the task's own obligation.
