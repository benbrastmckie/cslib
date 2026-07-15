# Implementation Plan: S5 Universal-Rule Termination Machinery

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Status**: [IMPLEMENTING]
- **Effort**: 8-12 hours
- **Dependencies**: Task 514 (literature grounding, anchor), Task 504 (parent; Phases 1/3 + partial 7 landed CI-green), Task 511 (`LoopChecking.lean` S4 scaffolding)
- **Research Inputs**: reports/01_s5-termination-implementation-blueprint.md
- **Artifacts**: plans/01_s5-termination-machinery.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/git-workflow.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Task 504 proved the per-edge rank measure inapplicable to S5's universal rule (mechanized, sorry-free: `modalApplyOneS5_rankStep_not_dischargeable`, `S5Simplification.lean:342`), permanently abandoning the `RuleApplicationSpec modalApplyOneS5` route. This plan implements the blueprint's Decision D1: **path (b) bespoke loop-checking termination** — a world-bounded guard + `S5LoopInv` invariant + pigeonhole bound + spec-free Hintikka lift replacing the rank machinery. Scope is the S5 termination/decidability spec, the generic Hintikka lift over the universal relation, S5 soundness, `s5Valid`/`Decidable (s5Valid φ)` against `Cube.S5`, and 5/KB5 validity + completeness via `Satisfies.five` and `Euclidean.lean`'s `RightEuclidean` API. **Definition of done**: P1-P3 + P5 landed sorry-free and CI-green (concrete progress), with the frontier phases (P4 pigeonhole, P6 completeness/decidability, P7) pursued and, if they resist within budget, honestly `[BLOCKED]` with the exact open goal — never a `sorry`, never a re-added rank axiom (blueprint D2/D5). Strategy 2 (semantic bounded-model FMP via the landed `extractModelS5`) is the pre-authorized decidability fallback for P6.

### Research Integration

This plan is grounded in `reports/01_s5-termination-implementation-blueprint.md` (the authoritative technical source, verified read-only against the Lean sources). Key integrated findings:

- **F1/D1**: path (a) rank-compatible restricted rule is RULED OUT (any equivalence-closure-reaching rule inherits the `rankStep` obstruction, exactly as S4's 4-rule does, `GenericDriver.lean:126`). Only path (b) is viable.
- **F2 (CRITICAL CORRECTION to the 514 anchor)**: S4's `LoopChecking.lean` is scaffolding-only — it ends at the `S4LoopInv` structure (`LoopChecking.lean:1127`). The preservation lemmas, pigeonhole bound `modalKnownWorlds_length_le_worldBoundS4`, fuel-sufficiency lemma, and any `Decidable (s4Valid …)` **do not exist**. S4 is blocked at the same wall. Task 515 transposes the scaffolding but must *invent* the termination capstone.
- **F4 (the wall)**: `modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean:876`) is hard-wired to `RuleApplicationSpec` + `ModalLoopInvGen` (rank). No spec-free / loop-parametrized lift exists (grep-verified). P6 must build `modalExpandBranchesS5_hintikka` parametrized on `S5LoopInv`, with no template.
- **F5 (good news)**: `modalTableauT_sound` (`FrameCompleteness.lean:1182`) consumes only `spec.freshLocal` + per-shape `soundIn` lemmas + the agreement lemma, **never `rankStep`**. S5 supplies `freshLocal` trivially, so `modalTableauS5_sound` (P5) is achievable now, independent of the termination chain.
- **F6 (fuel)**: `modalTableauGen` hardwires K's `modalFuel φ` (`Saturation.lean:363/366`). P6 must either prove `modalFuel` dominates the S5 world-bounded measure, or define a new `modalFuelS5`-parametrized entry.
- **F7/F8**: Phase 7 semantic assets (`Satisfies.five` `Basic.lean:471`, `extractModelS5_rightEuclidean` `FrameCompleteness.lean`) are landed. Strategy 2 (semantic FMP) is the honest fallback for the decidability capstone.

Cross-checked against `specs/504_*/summaries/01_*.md` and `specs/504_*/plans/01_*.md`: the blueprint's reuse verdicts (Phases 1/3 CI-green; Phase 2 obstruction mechanized; `extractModelS5*` landed sorry-free; `s5FC`/`s5Valid`/`fiveValid`/`kb5Valid` deliberately not landed and must be authored) are confirmed.

### Prior Plan Reference

No prior plan for task 515. The parent task 504 plan (`specs/504_*/plans/01_s5-kb5-euclidean-decidability.md`) is consulted read-only for effort calibration and reuse verdicts only — its rank-route phases are superseded by this plan's path (b). Learned calibration: task 504 stopped at the same wall S5 must now cross, so the frontier phases (P4/P6/P7) are genuinely novel and must be budgeted generously and isolated for zero-debt fallback.

### Roadmap Alignment

No ROADMAP.md consulted for this task (not provided in delegation context). This plan advances the parent task 504's blocked Phases 4/5/6/7 (S5/KB5 Euclidean decidability).

## Goals & Non-Goals

**Goals**:
- Deliver the S5 termination/decidability spec **replacing** `modalApplyOneS5_spec` (permanently abandoned, D2): a guarded rule + `S5LoopInv` termination bundle + spec-free Hintikka lift.
- Author the missing frame surface: `s5FC`, `s5Valid`, `fiveValid`, `kb5Valid` (blueprint D3).
- Land `modalTableauS5_sound` (Phase 5 soundness) — achievable now, independent of termination.
- Deliver the generic Hintikka lift + truth lemma over the universal relation (`modalExpandBranchesS5_hintikka`), `modalTableauS5_complete`, and `Decidable (s5Valid φ)` against `Cube.S5`.
- Deliver 5/KB5 validity + completeness via `Satisfies.five` and `Euclidean.lean`'s `RightEuclidean` API.
- REUSE the CI-green task-504 assets (`S5Simplification.lean` rule + driver, `FrameCompleteness.lean` `extractModelS5*`) and the φ₀-parametric engine (`signedSubfmls`, `relevantSetFinset`, `modalUniverse`, `modalExpMeasure`).
- Zero sorry, zero new axiom; full CSLib CI at every milestone; incremental commit at each green milestone; narrow `git add`.

**Non-Goals**:
- Path (a) restricted rank-compatible rule; re-attempting the B/T rank mirror; any `RuleApplicationSpec modalApplyOneS5` witness (proven false, D2).
- Genuine pure-K5 / pure-5 (Euclidean-without-equivalence) completeness — explicitly OUT OF SCOPE (`S5Simplification.lean:365-384`; no Mathlib `EuclGen` closure operator exists).
- Building S4's missing capstone (`Decidable (s4Valid …)`); this plan may factor a shared interface but does not owe S4 decidability.
- Any edit to K/T/B declarations, `GenericDriver.lean`'s `RuleApplicationSpec` core, or `FmpMeasure.lean` (zero regression, F9).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **R1** — The spec-free lift `modalExpandBranchesS5_hintikka` (P6) has NO template; S4 never built it. The 514 report's "transpose a finished template" framing understated this (F2/F4). | H | H | Sequence P6 last and isolated. Attempt by generalizing `modalExpandBranchesGen_hintikka`'s induction over `S5LoopInv` instead of `ModalLoopInvGen`. If it resists, land `[BLOCKED]` with the exact open goal and pivot decidability to Strategy 2 (F8). Do not duplicate any S4 `LoopTermination` effort. |
| **R2** — `modalExpandBranchesGen_hintikka` / `modalTableauT_complete` are hard-wired to `RuleApplicationSpec` + rank (`ModalLoopInvGen`); S5 can supply neither (F4). | H | H | P6 builds a *new* `S5LoopInv`-parametrized lemma, not a reuse. `freshLocal`/Hintikka-forcing fields survive as standalone lemmas re-targeted at `modalUniverseS5` (D2), NOT as a spec instance. |
| **R3** — `modalTableauGen` hardwires K's `modalFuel φ` (`Saturation.lean:363/366`); K's depth-based fuel may not dominate the S5 world-bounded re-broadcast (F3/F6). | H | M | P6 first attempt: prove `modalExpMeasureS5 (modalUniverseS5 φ) … ≤ modalFuel φ` (Option i, keeps `modalTableauS5` surface). Fallback: define `modalTableauS5g` with `modalFuelS5` derived from `modalWorldBoundS5` (Option ii). Choice is downstream of the P4 pigeonhole. |
| **R4** — Pigeonhole `modalKnownWorlds_length_le_worldBoundS5` (P4) is genuinely new proof work S4 also never landed (F2). | M | M | Reuse the Mathlib lemmas task 511 already imported: `Finset.card_powerset`, `Finset.card_le_card_of_injOn`, `List.Nodup.length_le_card`. `S5LoopInv`'s key fields (`keysDistinct`/`keysInUniverse`) are designed to feed exactly this argument. |
| **R5** — Soundness reachability invariant (P5): the universal rule's `soundIn` needs "every known world `acc`-reachable from 0" + `s5FC` cluster collapse; K/T/B proofs never needed this (F5). | M | M | Prove the "known-worlds reachable-from-0" invariant as a standalone driver-level branch lemma BEFORE the per-shape `soundIn` lemmas. Isolated in P5, which forks after P1 and does not block the termination chain. |
| **R6** — Scope realism: landing all of P1-P7 sorry-free in one task is optimistic given the S4 precedent (F2/R5). | M | H | Define task success as P1-P3 + P5 green (concrete, sorry-free). Front-load achievable phases; keep P4/P6/P7 isolated so a blockage there does not strand P1-P3/P5. Honest `[BLOCKED]`-with-open-goal, never `sorry`. |

## Testing & Validation

Run the full CSLib CI pipeline at **every** phase milestone (zero-debt contract) before committing:

- [ ] `lake build` — full project green (task 504 baseline: 3236/3236 jobs)
- [ ] `lake exe checkInitImports` — clean (files import `Cslib.Init` transitively)
- [ ] `lake exe lint-style` — clean
- [ ] `lake exe lint` — 0 new errors on task-touched files (1 pre-existing unrelated `unusedArguments` error in `PrimeExclusion.lean` predates this task; do not action)
- [ ] `lake test` — `CslibTests` suite exit 0
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — clean for task-touched files (pre-existing `Cslib.Init`-removal noise on sibling `Branch/Rules/GenericDriver/TDriver/BDriver.lean` is an accepted pattern; not actioned)
- [ ] `grep -c 'sorry' <touched files>` — 0 (prose mentions excepted)
- [ ] `grep -c '^axiom ' <touched files>` — 0 new axioms

Per-milestone commit discipline: narrow `git add` (only the specific `.lean` file(s) touched by the phase + this plan/state), commit message `task 515 phase {P}: {name}`.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 5 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 6 | 4 |
| 6 | 7 | 6 |

Phases within the same wave can run in parallel. **Phase 5 (soundness) forks after Phase 1 and runs parallel to the P2 -> P3 -> P4 termination chain** (F5: it consumes only `freshLocal`, never `rankStep`, so a blockage in the termination chain does not strand it). The decidability capstone (P6) depends on the pigeonhole (P4) and the `S5LoopInv` structure (P3); P7 depends on P6.

### Phase 1: Frame surface + S5 world bound + universe [COMPLETED]

_Started: 2026-07-15T00:05:00Z_ -- _Completed: 2026-07-15T00:40:00Z_

Landed sorry-free: `s5FC`, `s5Valid`, `fiveFC`, `fiveValid`, `kb5FC`, `kb5Valid`
(`FrameSoundness.lean`, mirroring `s4FC`/`symmFC`); `modalWorldBoundS5`, `modalUniverseS5`,
`modalUniverseS5_length_le` (`S5Simplification.lean`, mirroring `modalWorldBoundS4`/
`modalUniverseS4`/`modalUniverseS4_length_le`, `LoopChecking.lean:229/235/245`, verbatim).
Note: plan text said `fiveValid := frameValid (Cube.Five)` / `kb5Valid` "per the Cube classes"
-- `Cube.Five`/`Cube.KB5` are `Set (Proposition Atom)` logic objects, not `FrameCondition`
values, so (matching the `s4FC`/`symmFC` precedent already in the file) new `fiveFC`/`kb5FC`
`FrameCondition` predicates were authored (`Relation.RightEuclidean` alone; `Std.Symm ∧
Relation.RightEuclidean`) and `fiveValid`/`kb5Valid` defined via `frameValid fiveFC`/
`frameValid kb5FC`, matching every other `*Valid` definition's shape in this file.
Scoped builds (`lake build Cslib.Logics.Modal.Tableau.FrameSoundness` /
`...S5Simplification`), `lake exe checkInitImports`, `lake exe lint-style`, and a full-project
`lake lint` (12098 declarations, only the pre-existing unrelated `PrimeExclusion.lean`
`unusedArguments` error, nothing in the touched files) all green. Full-project `lake build`/
`lake test`/`lake shake` were intermittently blocked during this phase by an unrelated,
concurrent, uncommitted in-progress edit to `Cslib/Logics/Modal/Metalogic/Constructive/
CS5Canonical.lean` (task 512, a different active session, outside task 515's file scope) --
re-verified at the end-of-run full pipeline pass (see final metadata) once that file
stabilized.

**Goal**: Author the missing frame-class definitions and the world-bound/universe scaffolding, reusing the φ₀-parametric engine verbatim. Lowest-risk phase; establishes the surface all later phases consume.

**Tasks**:
- [ ] Define `s5FC := fun r => Std.Refl r ∧ Relation.RightEuclidean r` (reflexive + euclidean = equivalence) in `FrameSoundness.lean`, mirroring `s4FC` (`FrameSoundness.lean:1044`).
- [ ] Define `s5Valid := frameValid s5FC`, `fiveValid := frameValid (Cube.Five)`, `kb5Valid` per the `Cube` classes (`Cube.S5`/`Cube.Five`, `Cube.lean:45/85`) in `FrameSoundness.lean`.
- [ ] Define `modalWorldBoundS5 := 2^(2·|modalSubfmls φ₀|)` in `S5Simplification.lean`, mirroring `modalWorldBoundS4` (`LoopChecking.lean:229`).
- [ ] Define `modalUniverseS5` + prove `modalUniverseS5_length_le`, mirroring `modalUniverseS4` / `modalUniverseS4_length_le` (`LoopChecking.lean:235/245`).
- [ ] Reuse `signedSubfmls` (+ card lemmas, `LoopChecking.lean:290/298/313`) and `relevantSetFinset` (+ `_mono`/`_subset`, `LoopChecking.lean:323/333/344`) **verbatim** (φ₀-parametric, rule-independent — no re-derivation).

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — frame surface defs (`s5FC`, `s5Valid`, `fiveValid`, `kb5Valid`)
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — `modalWorldBoundS5`, `modalUniverseS5`, `modalUniverseS5_length_le`

**Verification**: full CI pipeline green; the four frame defs typecheck against `Cube.S5`/`Cube.Five`; `modalUniverseS5_length_le` closes sorry-free.

---

### Phase 2: Guard + guarded rule [NOT STARTED]

**Goal**: Transpose the S4 blocking guard to S5: define the birth-content function, the blocking-world guard (with its 3 guard lemmas), and the guarded rule `modalApplyOneS5g` that routes the K-minting shapes through the guard while leaving the universal arms unchanged. Establish agreement lemmas against the landed `modalApplyOneS5` and K.

**Tasks**:
- [ ] Define `successorBirthContentS5`, mirroring `successorBirthContent` (`LoopChecking.lean:374`).
- [ ] Define `blockingWorldS5` + its 3 guard lemmas, mirroring `blockingWorldS4` (`LoopChecking.lean:391/399/413/426`).
- [ ] Define `modalApplyOneS5g`: route the K minting shapes (`boxNeg`/`diaPos`, the mint source per F3) through the guard; leave the universal arms (`modalS5BoxAll`/`modalS5DiaNegAll`) unchanged. Mirror `modalApplyOneS4` (`LoopChecking.lean:461`).
- [ ] Prove the agreement/eq lemmas relating `modalApplyOneS5g` to the landed `modalApplyOneS5` and to K's `modalApplyOne` outside the two S5 shapes, mirroring `LoopChecking.lean:479-522` and reusing `modalApplyOneS5_eq_of_not_boxPos_diaNeg` (`S5Simplification.lean:181`).

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — `successorBirthContentS5`, `blockingWorldS5` (+3 guard lemmas), `modalApplyOneS5g`, agreement lemmas

**Verification**: full CI pipeline green; `modalApplyOneS5g` agreement lemmas close sorry-free; guard interaction with the universal arms typechecks (medium risk — the universal broadcast must survive the guard on minting shapes).

---

### Phase 3: `S5LoopInv` + preservation lemmas [NOT STARTED]

**Goal**: Define the loop invariant structure and prove the four preservation lemmas across a driver step. **This is the S4-unbuilt crux (F2): no template exists past the structure definition.** Budget generously.

**Tasks**:
- [ ] Define `S5LoopInv` structure (fields for `keysLowerBd`, `keysDistinct`, `keysTotal`, `keysInUniverse`), mirroring the `S4LoopInv` structure (`LoopChecking.lean:1127`) — the last thing S4 landed.
- [ ] Prove `modalStepBranchS5_preserves_keyLowerBd` (mirror `modalStepBranchS4` step target `LoopChecking.lean:538`). **No template — author from scratch.**
- [ ] Prove `modalStepBranchS5_preserves_keyDistinct`. **No template.**
- [ ] Prove `modalStepBranchS5_preserves_keyTotal`. **No template.**
- [ ] Prove `modalStepBranchS5_preserves_keyInUniverse` (consumes `modalUniverseS5_length_le` from P1). **No template.**

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — `S5LoopInv` structure + four `modalStepBranchS5_preserves_key*` lemmas

**Verification**: full CI pipeline green; all four preservation lemmas close sorry-free.

**Blocked-branch**: if a preservation lemma (most likely `_preserves_keyDistinct` under the universal re-broadcast, F3) cannot close within budget, mark this phase `[BLOCKED]` with the exact `lean_goal` open state at the failing preservation step, land P1-P2 (green) and P5 (independent), and stop the termination chain here without introducing debt. P4/P6/P7 become transitively `[BLOCKED]`; report the open goal verbatim.

---

### Phase 4: Pigeonhole world bound [NOT STARTED]

**Goal**: Prove the finite world bound `modalKnownWorlds_length_le_worldBoundS5` via the Mathlib pigeonhole lemmas, consuming the `S5LoopInv` key fields. **No template — this is the pigeonhole S4 also never landed (F2).** High risk.

**Tasks**:
- [ ] Prove `modalKnownWorlds_length_le_worldBoundS5` using `Finset.card_powerset` + `Finset.card_le_card_of_injOn` + `List.Nodup.length_le_card` (Mathlib lemmas confirmed imported by task 511, R4).
- [ ] Consume `S5LoopInv.keysDistinct` (nodup) and `S5LoopInv.keysInUniverse` (subset of `modalUniverseS5`) from P3 to bound `|modalKnownWorlds| ≤ modalWorldBoundS5`.

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — `modalKnownWorlds_length_le_worldBoundS5`

**Verification**: full CI pipeline green; the pigeonhole bound closes sorry-free against `modalWorldBoundS5`.

**Blocked-branch**: if the injectivity/subset feed from `S5LoopInv` to the Mathlib pigeonhole cannot close within budget, mark `[BLOCKED]` with the exact open goal (the un-discharged `Finset.card_le_card_of_injOn` obligation), preserve P1-P3 + P5 green, and defer P6/P7. No `sorry`.

---

### Phase 5: Soundness `modalTableauS5_sound` [NOT STARTED]

**Goal**: Land S5 soundness. **Independent of the termination chain (F5): uses only `freshLocal` + per-shape `soundIn` lemmas + the agreement lemma, never `rankStep`.** Forks after P1 and runs parallel to P2/P3/P4.

**Tasks**:
- [ ] Prove the standalone driver-level branch invariant "every known world is `acc`-reachable from world 0" (R5/R3 — a driver-level fact, not S5-specific; prove first).
- [ ] Prove per-shape `modalS5BoxAll_soundIn`: under `s5FC` (equivalence frame), `T(□φ)@w` satisfied ⇒ `T(φ)@w'` for every known `w'`, using the reachability invariant + `s5FC`'s `Std.Refl`/`RightEuclidean` cluster-collapse projections to establish `m.r (f w) (f w')` (F5).
- [ ] Prove per-shape `modalS5DiaNegAll_soundIn` (the dual universal dia-negative arm).
- [ ] Assemble `modalTableauS5_sound` via `modalExpandBranchesGen_closed_unsatIn` fed `modalApplyOneS5g`'s `freshLocal` (world-creation confinement is exactly K's, F5) + the agreement lemma + the two `soundIn` lemmas, mirroring `modalTableauT_sound` (`FrameCompleteness.lean:1182`).

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — reachability invariant, `modalS5BoxAll_soundIn`, `modalS5DiaNegAll_soundIn`, `modalTableauS5_sound` (template `modalTableauT_sound` lives in `FrameCompleteness.lean:1182`; author the S5 analogue in `FrameSoundness.lean`)

**Verification**: full CI pipeline green; `modalTableauS5_sound` closes sorry-free with the `soundIn` lemmas and reachability invariant.

---

### Phase 6: Spec-free Hintikka lift + fuel + completeness + decidability [NOT STARTED]

**Goal**: Build the frontier capstone: the `S5LoopInv`-parametrized Hintikka lift replacing the rank-bound generic lift, the fuel bridge, completeness, and the `Decidable (s5Valid φ)` instance against `Cube.S5`. **No template; the hard frontier (F4). HIGH risk — the primary `[BLOCKED]`/Strategy-2 candidate.**

**Tasks**:
- [ ] Author `modalExpandBranchesS5_hintikka`: the `S5LoopInv`-parametrized analogue of `modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean:876`), generalizing its induction over `S5LoopInv` (world bound, from P3/P4) instead of `ModalLoopInvGen` (rank). The Hintikka-forcing fields survive as standalone lemmas re-targeted at `modalUniverseS5` (D2), NOT as a `RuleApplicationSpec` instance.
- [ ] Fuel bridge (F6), Option (i) first: prove `modalExpMeasureS5 (modalUniverseS5 φ) … ≤ modalFuel φ` to keep the existing `modalTableauS5` surface (`Saturation.lean:363/366`). If domination is false (R3), Option (ii): define `modalTableauS5g` with `modalFuelS5` derived from `modalWorldBoundS5` (P1) + a new driver entry.
- [ ] Prove `modalTableauS5_complete` from the spec-free lift + fuel bridge.
- [ ] Prove `s5Valid_decides` and build `instDecidableS5Valid : Decidable (s5Valid φ)`, mirroring `instDecidableTValid` (`FrameCompleteness.lean:1281`) — but routed through the loop-checking lift, not the rank spec.

**Timing**: 2.5 hours

**Depends on**: 4 (pigeonhole world bound) and 3 (`S5LoopInv` structure)

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `modalExpandBranchesS5_hintikka`, fuel bridge, `modalTableauS5_complete`, `s5Valid_decides`, `instDecidableS5Valid`
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — ONLY if a spec-free `LoopTermination` interface extension is required (F4/F9); otherwise untouched (do not edit the `RuleApplicationSpec` core)

**Verification**: full CI pipeline green; `instDecidableS5Valid` typechecks and evaluates; no `RuleApplicationSpec modalApplyOneS5` witness reintroduced; no rank axiom.

**Blocked-branch**: if `modalExpandBranchesS5_hintikka` cannot close within budget (R1/R2), take the pre-authorized contingency in this order: (1) mark P6 `[BLOCKED]` recording the exact `lean_goal` open state at the failing induction step of the spec-free lift; then (2) **Strategy 2 pivot (F8, pre-authorized, not an afterthought)**: build `instDecidableS5Valid` via semantic bounded-model FMP instead — enumerate equivalence-relation models of size ≤ `2^(2|Sf|)` over a `Fintype` and check refutation using the already-landed `extractModelS5` countermodel + a filtration truth lemma, bypassing the generic driver's termination entirely (Massacci Fact 9.1: S5 has polynomial single-cluster models). Strategy 2 does not depend on the spec-free lift. If neither closes sorry-free within budget, leave P6 `[BLOCKED]` with the open goal — never a `sorry`, never a re-added rank axiom (D2/D5).

---

### Phase 7: 5/KB5 validity + completeness [NOT STARTED]

**Goal**: Complete task 504 Phase 7: `fiveValid`/`kb5Valid` completeness via the landed semantic bridge. Low risk *given* P6.

**Tasks**:
- [ ] Prove `fiveValid` completeness via `Satisfies.five` (`Basic.lean:471`) + `extractModelS5_rightEuclidean` (`FrameCompleteness.lean`, landed sorry-free by task 504 Phase 3/7).
- [ ] Prove `kb5Valid` completeness via `modalTableauS5_complete` (P6) + `extractModelS5_rightEuclidean` + the `Cube.Five` / `RightEuclidean` bridges (`Euclidean.lean:236` `symm_rightEuclidean_iff_trans`, `refl_cod`/`equiv_cod`).
- [ ] Confirm the pure-K5/pure-5 (Euclidean-without-equivalence) case remains explicitly OUT OF SCOPE with the existing in-file scope note (`S5Simplification.lean:365-384`).

**Timing**: 1 hour

**Depends on**: 6

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `fiveValid`/`kb5Valid` completeness theorems

**Verification**: full CI pipeline green; both completeness theorems close sorry-free against `Cube.Five`/`Cube.S5`.

**Blocked-branch**: P7 is gated on P6. If P6 landed `[BLOCKED]` (or only Strategy-2 decidability without a full `modalTableauS5_complete`), mark P7 `[BLOCKED]` with the specific missing prerequisite (`modalTableauS5_complete`), or deliver only the `Satisfies.five`-direct `fiveValid` fragment that does not route through the tableau engine. No `sorry`.

## Artifacts & Outputs

Expected sorry-free, axiom-free Lean outputs (per phase):
- **P1**: `s5FC`, `s5Valid`, `fiveValid`, `kb5Valid` (`FrameSoundness.lean`); `modalWorldBoundS5`, `modalUniverseS5`, `modalUniverseS5_length_le` (`S5Simplification.lean`).
- **P2**: `successorBirthContentS5`, `blockingWorldS5` (+3 guard lemmas), `modalApplyOneS5g`, agreement lemmas (`S5Simplification.lean`).
- **P3**: `S5LoopInv` structure + four `modalStepBranchS5_preserves_key*` lemmas (`S5Simplification.lean`).
- **P4**: `modalKnownWorlds_length_le_worldBoundS5` (`S5Simplification.lean`).
- **P5**: reachability invariant, `modalS5BoxAll_soundIn`, `modalS5DiaNegAll_soundIn`, `modalTableauS5_sound` (`FrameSoundness.lean`).
- **P6**: `modalExpandBranchesS5_hintikka`, fuel bridge, `modalTableauS5_complete`, `s5Valid_decides`, `instDecidableS5Valid` (`FrameCompleteness.lean`; possibly `GenericDriver.lean` interface extension) — OR Strategy-2 semantic `instDecidableS5Valid`.
- **P7**: `fiveValid`/`kb5Valid` completeness theorems (`FrameCompleteness.lean`).
- Implementation summary at `specs/515_*/summaries/01_*-summary.md` on completion, with an honest per-phase status ledger (including any `[BLOCKED]`-with-open-goal entries).

## Rollback/Contingency

- **Per-phase revert**: each phase commits narrowly and independently; a failing phase is reverted with `git revert` of that phase's single commit without disturbing earlier green phases. Never `git reset --hard` without explicit user request.
- **Zero-debt contract (D2/D5)**: no phase lands a `sorry`, a re-added rank axiom, or a `RuleApplicationSpec modalApplyOneS5` witness. If a sub-piece cannot close sorry-free, its phase is marked `[BLOCKED]` with the exact `lean_goal` open state, earlier green phases are preserved, and downstream phases are transitively `[BLOCKED]`.
- **Frontier isolation**: P5 (soundness) forks after P1 and is independent of P2-P4, so a termination-chain blockage still leaves P1-P3 + P5 as concrete sorry-free progress (definition of task success, R6).
- **Strategy 2 fallback (F8, pre-authorized)**: if the P6 loop-checking capstone resists, pivot `instDecidableS5Valid` to semantic bounded-model FMP over `extractModelS5` (equivalence-relation model enumeration ≤ `2^(2|Sf|)` + filtration truth lemma), which bypasses the generic driver's termination and the unbuilt spec-free lift entirely. This is the sorry-free escape hatch, not a `sorry`.
- **Escalation**: if both the loop-checking lift and Strategy 2 resist within budget, land the task `[PARTIAL]` with P1-P3 + P5 green and P4/P6/P7 `[BLOCKED]`-with-open-goal, and recommend a shared S4/S5 `LoopTermination` interface follow-up (blueprint Context Extension Recommendation) — coordinating with any S4 effort to avoid duplication.
