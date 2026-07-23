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

### Phase 2: Guard + guarded rule [COMPLETED]

_Started/Completed: 2026-07-15T00:45:00Z_

Landed sorry-free in `S5Simplification.lean`: `successorBirthContentS5`/`blockingWorldS5` (+3
guard lemmas `blockingWorldS5_mem_modalKnownWorlds`/`blockingWorldS5_eq_birthContent`/
`blockingWorldS5_none_fresh`) reusing `successorBirthContent` from `LoopChecking.lean`
verbatim (rule-independent: purely a function of `b`'s box-context at `w`); `modalApplyOneS5g`
(guarded rule, mirrors `modalApplyOneS4`); 4 agreement lemmas
(`modalApplyOneS5g_boxNeg_blocked_eq`/`_boxNeg_unblocked_eq`/`_diaPos_blocked_eq`/
`_diaPos_unblocked_eq`) plus `modalApplyOneS5g_eq_of_not_boxNeg_diaPos` and a new composed
lemma `modalApplyOneS5g_eq_of_not_minting_not_universal` (agreement with K's `modalApplyOne`
outside all four guard/universal shapes, composing the new guard-agreement lemma with the
already-landed `modalApplyOneS5_eq_of_not_boxPos_diaNeg`, per the plan's explicit reuse
instruction). Added `public import Cslib.Logics.Modal.Tableau.LoopChecking` to
`S5Simplification.lean` (read-only reuse of `signedSubfmls`/`relevantSetFinset`/
`successorBirthContent`; no edit to `LoopChecking.lean` itself, zero regression to S4/K/T/B).
Unblocked-case agreement lemmas are direct (`unfold; simp`), simpler than S4's chained
`modalApplyOneS4Rules`-through-T proof, since S5 has no intermediate K+T+4-style rule layer.
Full CSLib CI green: `lake build` (3236/3236), `lake exe checkInitImports`, `lake exe
lint-style`, `lake lint` (only the pre-existing unrelated `PrimeExclusion.lean` error), `lake
shake --add-public --keep-implied --keep-prefix` (no import-diff for the touched files), `lake
test` (9227/9227). Zero sorries, zero new axioms in touched files.

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

### Phase 3: `S5LoopInv` + preservation lemmas [BLOCKED]

_Started: 2026-07-15T01:00:00Z_ -- _Blocked: 2026-07-15T02:15:00Z_

**Landed sorry-free (genuine partial progress, in `S5Simplification.lean`)**: the `S5LoopInv`
structure (exactly the plan's four fields `keysTotal`/`keyLowerBd`/`keysDistinct`/
`keysInUniverse`); `modalStepBranchS5gKeyed` (the key-threaded guarded step, mirroring
`modalStepBranchS4Keyed`); three local re-derivations of `FmpMeasure.lean`'s `private`
`modalKnownWorlds` lemmas (`modalKnownWorlds_fold_spec_S5`/`mem_modalKnownWorlds_S5`/
`modalKnownWorlds_mono_append_S5`), mirroring `BDriver.lean`'s established `_B`-suffixed
re-derivation pattern. All compile, zero sorries, zero new axioms.

**BLOCKER**: the four `modalStepBranchS5_preserves_key*` preservation lemmas could not be
closed sorry-free within budget. Two distinct, concrete obstructions were identified by
reading the actual dependency chain (not assumed abstractly):

1. **Infrastructure gap (`keysTotal`/`keyLowerBd`/`keysInUniverse`)**: the only public
   lemma that lets a non-`RuleApplicationSpec` step reason "which labels can newly appear on
   the branch" is `modalApplyOne_knownWorlds_step` (`FmpMeasure.lean:2042`), whose dichotomy
   (no mint, all new labels `∈ modalKnownWorlds b`; OR mint, all new labels `= modalNextWorld
   b`) requires `accTargetsKnown b acc` as a standing hypothesis. Discharging `keysInUniverse`
   for the S5-universal-arm shapes additionally needs a subformula-closure fact (`φ ∈
   modalSubfmls φ₀`, i.e. a `bClosure`-style invariant) to place a newly-inserted birth-key
   pair `(s, φ)` inside `signedSubfmls φ₀`. Neither is present in the plan's literal four-field
   `S5LoopInv`. This is exactly why `S4LoopInv` (`LoopChecking.lean:1127`, which `S5LoopInv`
   mirrors) carries **six additional** generic fields (`bClosure`/`eNodup`/`eClosure`/
   `accFresh`/`accKnown`/`outDegEq`) beyond the four birth-key fields the plan asked for --
   S4 needed them too, it just never got far enough to state the preservation lemmas that would
   expose the need (blueprint F2: `LoopChecking.lean` ends at the `S4LoopInv` **structure**).
   Closing this gap requires either extending `S5LoopInv` with these six fields (adding their
   own preservation obligations, none scoped by the plan) or threading `accTargetsKnown b acc`
   and a subformula-closure fact as extra explicit hypotheses through all four lemmas.
2. **Design-level gap (`keysDistinct`), the deeper issue**: `blockingWorldS5_none_fresh`
   (Phase 2) guarantees the prospective birth content differs from every known world's
   **current** `relevantSetFinset`. But `S5LoopInv.keyLowerBd` only records that a *stored* key
   is a **lower bound** (`⊆`, not `=`) of its world's current relevant set -- by design, so the
   invariant survives monotonic branch growth (this was precisely task 511's Gap-1 fix). A
   newly-minted key could therefore coincide with an *older* world's frozen, historical key even
   though it differs from that older world's now-larger *current* relevant set -- nothing in
   the four-field invariant (or the guard, which only ever compares against current relevant
   sets) rules this out. This is a genuine open design question, not a proof-search failure: the
   guard would need to compare the prospective birth content against every *stored key*, not
   every world's *current relevant set*, for `blockingWorldS5_none_fresh` to directly discharge
   `keysDistinct`'s new-vs-old case. S4 never encountered this either, for the same reason as
   above (`S4LoopInv` is the last thing S4 landed, per blueprint F2).

**What was tried**: read `RuleApplicationSpec`'s `freshLocal`/`outputsSubsetUniverse` fields and
their K witnesses (`modalApplyOne_fresh_local`, `modalApplyOne_diamondPos_outputs_subset`,
`modalApplyOne_boxNeg_outputs_subset`) to source a mint-confinement fact without threading a
full spec (unavailable, D2); found and read `modalApplyOne_knownWorlds_step`
(`FmpMeasure.lean:2042`), the closest-fitting public lemma, and traced its `accTargetsKnown`
dependency; re-derived the three `modalKnownWorlds` private helpers locally (successfully); then
attempted to state `modalStepBranchS5_preserves_keyTotal` and found the guard-unblocked-mint
case requires exactly the gap-1 infrastructure above before the lemma can even be fully stated
with the right side hypotheses, let alone proved.

**What is needed to unblock**: (a) decide whether to extend `S5LoopInv` to the full ten-field
shape (mirroring `S4LoopInv` verbatim, absorbing the six generic fields and their own
preservation lemmas) or thread the missing hypotheses explicitly per-lemma; (b) resolve the
`keysDistinct` design gap, most plausibly by redesigning `blockingWorldS5` to compare the
prospective birth content against the threaded `keys` list directly (`∃ (w', k) ∈ keys, k =
successorBirthContentS5 φ₀ b s φ w`) rather than against `relevantSetFinset`'s current value --
a change to Phase 2's guard, which would need to be re-verified against Phase 2's
already-landed, already-committed agreement lemmas (or superseded by a new guard variant).

**Prohibited workarounds not used**: no `sorry`, no `def S5LoopInv := True`-style placeholder,
no re-added rank axiom (D2/D5).

P4/P6/P7 are transitively `[BLOCKED]` on this (P4's pigeonhole consumes exactly
`S5LoopInv.keysDistinct`/`keysInUniverse`, both open). P5 (soundness) is independent (F5) and
was pursued separately regardless of this block (see Phase 5 below).

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

### Phase 4: Pigeonhole world bound [BLOCKED]

_Transitively blocked_: not independently attempted. Depends on Phase 3's `S5LoopInv.keysDistinct`/`keysInUniverse`, both open (Phase 3 [BLOCKED]).

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

### Phase 5: Soundness `modalTableauS5_sound` [BLOCKED]

_Attempted: 2026-07-15T02:20:00Z -- 2026-07-15T02:45:00Z_

**Clarification of the plan text vs. dependency table**: the phase's task list says
"fed `modalApplyOneS5g`'s `freshLocal`" but the Dependency Analysis table lists Phase 5 as
depending on Phase 1 only (forking after it, parallel to 2/3/4). Since `(modalApplyOneS5 sf b
acc).snd = (modalApplyOne sf b acc).snd` unconditionally (verified by inspection of
`modalApplyOneS5`'s definition: every match arm returns the K-computed `kAcc` as its second
component, regardless of shape), soundness is fully expressible against the **already-landed,
unguarded** `modalApplyOneS5`/`modalTableauS5` (task 504), matching the dependency table and
F5's blueprint framing (soundness is independent of the guard/termination chain). This plan
targets the unguarded declarations; no `modalApplyOneS5g`-specific freshLocal fact was needed.

**BLOCKER**: `modalExpandBranchesGen_closed_unsatIn` (`FrameSoundness.lean:728`), the only
existing generic soundness bridge, threads a *single* invariant (`accFreshInv`) across its
fuel-induction and hands `hBoxPos`/`hDiaNeg` only `hacc : ∀ w w', acc.hasEdge w w' → m.r (f w)
(f w')` (direct-edge relatedness) at each single step -- **no reachability-closure fact is
available inside those per-step hypotheses**. S5's universal box-positive/diamond-negative arms
(`modalS5BoxAll`/`modalS5DiaNegAll`) propagate to **every** known world `w'`, not just
`acc.hasEdge`-successors of the trigger `lbl`, so proving `RuleResultSat` there needs `m.r (f
lbl) (f w')` for a `w'` that may be many mint-tree edges away from `lbl` -- direct-edge `hacc`
alone is insufficient (confirmed by inspection: `modalApplyOne_boxPos_sound`/
`modalApplyOne_diaNeg_sound`, `SoundnessStep.lean:446/490`, the K per-shape soundness lemmas
`hBoxPos`/`hDiaNeg` normally discharge from, only ever use `hacc` at the *trigger's own* direct
edges -- exactly what T's `reflFC` self-propagation and B's predecessor-propagation need, and
exactly what S5's *whole-known-world* propagation does not have available). This is the R5/F5
"genuinely new content" the plan flagged, but the actual shape of the gap is sharper than "new
per-shape lemmas": it requires a **new top-level fuel-induction bridge** (a
`modalExpandBranchesGen_closed_unsatIn`-style wrapper additionally threading a "every known
world is `acc`-reachable from world 0" invariant alongside `accFreshInv`), not merely two new
per-shape `soundIn` lemmas plugged into the *existing* bridge.

**What was tried / established (not committed -- no file changes from this phase, to keep the
zero-debt/no-partial-file-edit discipline clean; findings only)**: (1) confirmed
`(modalApplyOneS5 sf b acc).snd = (modalApplyOne sf b acc).snd` holds unconditionally by
inspection of the definition (all three match arms return `kAcc`), so `modalApplyOneS5`'s
`freshLocal`-style dichotomy reduces directly to `modalApplyOne_fresh_local`
(`FmpMeasure.lean:802`) -- this piece is genuinely easy and was NOT the blocker; (2) traced
`modalExpandBranchesGen_closed_unsatIn`'s signature and its single-step callee
`modalStepBranchGen_preserves_satIn` (`FrameSoundness.lean:193`, the "K monolith", 300+ lines)
and confirmed neither threads reachability; (3) sketched (not written) a *scoped* single-step
reachability-preservation argument specific to `modalApplyOneS5` (not the full generic K
monolith): using the already-landed `modalS5BoxAll_mem`/`modalS5DiaNegAll_mem` (Phase 1, giving
target labels `∈ modalKnownWorlds b` directly for the universal arms) plus
`modalApplyOne_fresh_local`'s dichotomy for the mint case, a "known worlds reachable from 0"
invariant should be provable as its own standalone lemma without re-deriving the K monolith --
but assembling a full replacement top-level fuel-induction bridge (combining this with
`modalStepBranchGen_preserves_satIn` as a black box) was not completed within budget.

**What is needed to unblock**: author a new generic lemma
`modalExpandBranchesGen_closed_unsatIn_reachable` (or an S5-specialized variant) that threads
`∀ w ∈ modalKnownWorlds b, Relation.ReflTransGen (fun a c => acc.hasEdge a c) 0 w` alongside
`accFreshInv` through the fuel induction, reusing `modalStepBranchGen_preserves_satIn` as a
black box for the satisfiability half and a new (sketched-but-unwritten) single-step
reachability-preservation lemma for the second half; then re-derive `hBoxPos`/`hDiaNeg` for
S5's universal arms using the equivalence-closure projections (`Std.Refl`/
`Relation.RightEuclidean` from `s5FC`) applied to the reachability witness, not direct `hacc`.

**Prohibited workarounds not used**: no `sorry`, no vacuous placeholder, no re-added rank axiom.

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

### Phase 6: Spec-free Hintikka lift + fuel + completeness + decidability [BLOCKED]

_Transitively blocked_: not independently attempted. Depends on Phase 4 (pigeonhole) and Phase 3 (`S5LoopInv`), both open. Strategy 2 (semantic bounded-model FMP over `extractModelS5`) was not attempted either -- it was not reached given the upstream blocks and remaining budget; it remains the pre-authorized fallback for a follow-up task.

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

### Phase 7: 5/KB5 validity + completeness [BLOCKED]

_Transitively blocked_: not independently attempted. Depends on Phase 6's `modalTableauS5_complete`, which is blocked. The `Satisfies.five`-direct `fiveValid`-completeness fragment (not routed through the tableau engine) was not separately attempted within budget.

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
