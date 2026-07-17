# Implementation Plan: KB5 Full-Cluster Propagation Rule and Direct Soundness

- **Task**: 524 - kb5_full_cluster_rule_and_soundness
- **Status**: [IMPLEMENTING]
- **Effort**: 8 hours
- **Dependencies**: None (task 511's LoopChecking.lean edit is a CI-gating check only, see Phase 6)
- **Research Inputs**: specs/515_s5_universal_rule_termination_unblock_504/reports/02_spawn-analysis.md
- **Artifacts**: plans/01_kb5-full-cluster-rule-soundness.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; plan-compliance.md; lean4.md; cslib.md
- **Type**: cslib

## Overview

Task 515 Phase 22 landed `modalApplyOneKb5 := modalApplyOneFive` as a literal alias
(`Cslib/Logics/Modal/Tableau/FiveSimplification.lean:1436`), sound for KB5 only by the "factor,
not clone" frame-class-monotonicity shortcut (`fiveValid_imp_kb5Valid`,
`FrameSoundness.lean:3808`). That alias only propagates root box/diamond content to **direct**
`acc.hasEdge` successors, because Five's own soundness requires exactly that restriction (Five's
root is not reflexive). But `extractModelKb5`'s forced relation
`Relation.EuclGen (Relation.SymmGen acc.hasEdge)` (`FrameCompleteness.lean:3230`) relates the root
to **indirect** chain targets too — machine-checked by the sorry-free
`extractModelKb5_root_reach_scout` (`FrameCompleteness.lean:3294`). This task delivers a
genuinely new KB5-specific rule whose root trigger propagates to the **full known non-root
cluster** and back onto world `0` itself (justified by `Relation.symm_rightEuclidean_root_refl`,
`Cslib/Foundations/Relation/Euclidean.lean:362`), re-derives its termination bound, lands its
`RuleApplicationSpecCore` instance, and proves a new soundness theorem **directly against
`kb5FC`** — the frame-class-monotonicity shortcut is unavailable here because the new rule's
unrestricted root propagation is unsound for the strictly larger `fiveFC` class (Phase 23 blocker
note, `FrameCompleteness.lean:3300-3339`).

Definition of done: a new rule + driver chain + rfl bridges, a re-derived termination invariant,
a nine-field `RuleApplicationSpecCore` instance, and a `kb5FC`-direct soundness theorem — every
new public declaration sorry-free, axiom-clean (`lean_verify` shows only the standard
`[propext, Classical.choice, Quot.sound]` subset, several needing none), with full CSLib CI green
(subject to the task-511 LoopChecking.lean gate).

### Research Integration

The parent spawn analysis (`reports/02_spawn-analysis.md`) established: (1) the obstruction is a
genuine missing-prerequisite, not an impossibility — K5/KB5 completeness via rooted Euclidean
tableaux is standard (Blackburn-de Rijke-Venema §4.8-4.9); (2) the required propagation shape
(full non-root cluster dump + root self-reflexive propagation) is pinned down exactly by the
scout lemma; (3) soundness must be proved directly, not borrowed from Five. This plan sequences
the rule + termination + specCore + soundness deliverables of "New Task 1" from that analysis.
Completeness and `Decidable (kb5Valid φ)` ("New Task 2") are explicitly out of scope here.

### Prior Plan Reference

No prior plan for task 524. Effort calibration is taken from the spawn analysis, which sized this
deliverable at 6-10 hours and compared its scope to Phases 15-21 of task 515's Five construction
(rule design, termination bound, soundness assembly). The green S5/Five rule-design pattern in
`FiveSimplification.lean` (mint-arm guards, witness reuse, source-split termination tagging) is
the structural template throughout.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap flag not set). This task advances the KB5 tableau
metatheory line: it is the load-bearing prerequisite for the follow-on KB5-completeness /
decidability task.

## Goals & Non-Goals

**Goals**:
- Land a new KB5-specific tableau rule (default name `modalApplyOneKb5'`) whose root
  box-positive/diamond-negative trigger propagates to the full known non-root cluster AND to
  world `0` itself.
- Land its driver chain (`modalStepBranchKb5'`, `modalExpandBranchesKb5'`, `modalTableauKb5'`)
  with `rfl` bridge lemmas mirroring the existing alias bridges (`FiveSimplification.lean:1465-1486`).
- Re-derive the termination bound for the new rule's root-arm shape (Phase 19a's bound does not
  transfer definitionally).
- Land the nine-field `RuleApplicationSpecCore` instance mirroring `modalApplyOneFive_specCore`
  (`FiveSimplification.lean:1389-1442`).
- Land a new soundness theorem in `FrameSoundness.lean` proved directly against `kb5FC`, using
  `Relation.symm_rightEuclidean_root_refl` and the rooted-cluster lemmas.
- Zero `sorry`, zero new `axiom`, every new public declaration `lean_verify`-clean.

**Non-Goals**:
- KB5 completeness (`modalTableauKb5_complete`), the Euclidean-symmetric truth lemma, and
  `instDecidableKb5Valid` — deferred to the follow-on task.
- Modifying, removing, or re-deriving `extractModelKb5` and its extraction lemmas
  (`FrameCompleteness.lean:3230-3270`), the scout lemma (`:3294`), `EuclGen.symm_of_symm`,
  `Relation.EuclGen`/`Relation.SymmGen`, or `symm_rightEuclidean_root_refl` — all reused verbatim.
- Retiring or renaming the existing `modalApplyOneKb5` alias unless required; if changed, document
  as a plan deviation and raise as a blocker first per plan-compliance.md.
- Touching `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (see Phase 6 gate) or
  `FrameCompleteness.lean` (that is the follow-on task's territory).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Full-cluster root propagation turns out unsound for some `kb5FC` satisfying model (a non-root branch world disconnected from root) | H | M | Phase 5 does the mandatory pre-code satisfiability analysis (plan-compliance.md) before writing proof code; if the naive shape is unsound, restrict the dump to the root's actual reachable cluster and mark [BLOCKED] with the exact goal state rather than papering over with a placeholder |
| Re-derived termination bound fails because the root arm now dumps to many worlds at once | M | M | Root-arm full-cluster dump propagates to **existing** known worlds + world `0` (no fresh mint at root), which should not grow `modalMaxWorld`; Phase 3 confirms against the source-split invariant (`FiveSimplification.lean:1488+`) and re-tags only the changed arm |
| One of the nine `RuleApplicationSpecCore` fields (e.g. `boxNegWitness'`/`diaPosWitness'`) no longer holds for the new root arm | M | M | Phase 4 discharges field-by-field mirroring `modalApplyOneFive_specCore`; a genuinely unprovable field is a [BLOCKED] escalation, not a `sorry` or vacuous instance |
| New axiom accidentally introduced via a Mathlib import or `Classical` misuse | H | L | Phase 6 runs `lean_verify` on every new public declaration; only `[propext, Classical.choice, Quot.sound]` (or a subset) permitted |
| Full CI blocked by task 511's mid-edit of LoopChecking.lean | L | M | Phase 6 checks task 511 status first; if unresolved, land the scoped `lake build` of the touched modules and defer the full-project `lake test`/`shake` sweep, noting the transient gate — do not edit LoopChecking.lean |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 5 | 2 |
| 4 | 4 | 3 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel. Phases 3 and 5 are genuinely parallel:
Phase 3 edits `FiveSimplification.lean` (termination), Phase 5 edits `FrameSoundness.lean`
(soundness); neither writes the other's file, and soundness (`closed ⟹ valid`) does not consume
the termination bound.

### Phase 1: New KB5 rule definition and full-cluster propagation helper [COMPLETED]

**Grounding note (recorded before writing code)**: cross-checking this phase's task bullets
against the Overview, the Risks table, and the actual `FrameCompleteness.lean:3327-3332` Phase 23
blocker note (the plan's own grounding source) shows the "root arm... for `.pos .diamond φ` and
`.neg .box φ`" phrase in this phase's task list names the **mint** (existential/witness-reuse)
shapes, whereas all three other sources describe the change as "root box/diamond **triggers**...
matching the non-root arm's own unconditional propagation" -- i.e. the **propagation**
(universal) shapes `.pos .box φ` / `.neg .diamond φ`, exactly `modalFiveBoxAll`/
`modalFiveDiaNegAll`'s existing root arm. A semantic check confirms only the propagation-shape
reading is soundness-compatible: asserting a diamond/box-negative witness formula at *every*
known world would turn an existential mint into a universal claim, which is not validity
preserving in general, while relaxing the box-positive/diamond-negative root arm's target set
(full non-root cluster, unconditional, plus self) is exactly what `extractModelKb5`'s forced
relation (the Phase-23 scout lemma) already forces semantically. Implemented against
`.pos .box φ` / `.neg .diamond φ` (propagation shapes) per the dominant, 3-of-4-source grounding;
the mint shapes (`.pos .diamond` / `.neg .box`) are left **untouched**, verbatim
`modalApplyOneFive` witness-reuse behavior, matching this phase's own "non-root arms match
Five's witness-reuse behavior verbatim" instruction generalized to all triggers of those shapes.
*(deviation: clarified -- see above; not a scope change, an internal-inconsistency resolution
grounded in the plan's own majority text)*.

**Goal**: Land the new rule `modalApplyOneKb5'` and whatever known-non-root-cluster enumeration
helper it needs, with the file-location decision recorded.

**Tasks**:
- [ ] Decide and record the file location. **Default**: land in `FiveSimplification.lean`'s KB5
  section (immediately after the existing `modalApplyOneKb5` alias at :1436), because every reused
  helper (`witnessWorldFive` :458, `modalApplyOneFiveProp` :319, the known-worlds enumeration, and
  the source-split termination invariant machinery :1488+) already lives there; a sibling
  `Kb5Simplification.lean` would require re-importing all of it. If the implementer chooses the
  sibling file, document the import surface as a deviation annotation.
- [ ] Locate the "known non-root worlds" enumeration used by the non-root propagation arm (search
  `modalKnownWorlds`/`modalKnownWorldsFive` near `witnessWorldFive`); reuse it, do not re-derive.
- [ ] Define `modalApplyOneKb5' : RuleApply Atom`. The non-root arms (`sf.label ≠ 0`) match
  `modalApplyOneFive`'s witness-reuse behavior verbatim (`FiveSimplification.lean:486-500`). The
  **root arm** (`sf.label == 0`) for `.pos .diamond φ` and `.neg .box φ` must, instead of falling
  through to `modalApplyOneFiveProp`, emit a `.linear` output propagating the signed body to
  **every** known non-root world AND to world `0` itself (the root-self-reflexive arm justified
  by `Relation.symm_rightEuclidean_root_refl`). Match the non-root propagation arm's unconditional
  cluster behavior for the shape of each propagated signed formula.
- [ ] Add a docstring on `modalApplyOneKb5'` stating it is NOT an alias of `modalApplyOneFive`,
  why the root arm differs, and that its soundness is `kb5FC`-specific (not transferable to
  `fiveFC`).

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` — new rule + helper in the KB5 section
  (or `Cslib/Logics/Modal/Tableau/Kb5Simplification.lean` if the sibling-file option is chosen)

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` succeeds (or the new module).
- `lean_verify` on `modalApplyOneKb5'` shows no `sorry`, no new axiom.
- The root arm is demonstrably not definitionally equal to `modalApplyOneFive`'s root arm (they
  produce different `RuleResult`s on a root box/diamond trigger).

---

### Phase 2: Driver chain and rfl bridge lemmas [COMPLETED]

**Goal**: Instantiate the generic driver at the new rule and land the `rfl` bridges.

**Tasks**:
- [ ] Define `modalStepBranchKb5'` via `modalStepBranchGen modalApplyOneKb5'`, mirroring
  `modalStepBranchKb5` (`FiveSimplification.lean:1446-1451`).
- [ ] Define `modalExpandBranchesKb5'` via `modalExpandBranchesGen modalApplyOneKb5'`
  (mirror :1454-1457).
- [ ] Define `modalTableauKb5'` via `modalTableauGen modalApplyOneKb5'` (mirror :1462-1463).
- [ ] Land the `rfl` bridge lemmas `modalStepBranchKb5'_eq`, `modalExpandBranchesKb5'_eq`,
  `modalTableauKb5'_eq` (mirror :1465-1480).
- [ ] Do NOT land a `modalTableauKb5'_eq_modalTableauFive`-style bridge — that equality is false
  by design (the whole point is the rule differs). If a downstream consumer expects the old alias,
  leave the old `modalApplyOneKb5`/`modalTableauKb5` chain in place untouched alongside the new one.

**Timing**: 0.75 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (or the new module)

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` succeeds.
- Each `_eq` bridge closes by `rfl`.
- `lean_verify` clean on all four new declarations.

---

### Phase 3: Termination bound re-derivation [NOT STARTED]

**Goal**: Re-derive (or re-confirm) the source-split termination invariant for the new rule's
root arm, since it is no longer definitionally `modalApplyOneFive`.

**Tasks**:
- [ ] Read the "Source-Split Termination Invariant" section
  (`FiveSimplification.lean:1488+`, `mintTags`/`S5wTagInv` and tag-membership corollaries) and the
  Phase 19a bound it establishes ("≤1 mint per tag PER SOURCE-CLASS {root, non-root}").
- [ ] Establish that the new root arm does NOT mint a fresh world (it dumps to existing known
  worlds + world `0`), so the world-count-vs-`modalWorldBound` bound is preserved — or, if the
  chosen shape does mint, re-derive the tag/source-class bound for it explicitly.
- [ ] Land the termination lemma(s) the generic driver's fuel/termination argument consumes for
  `modalApplyOneKb5'`, mirroring the Five tags' membership corollaries. Prove them as their own
  named lemmas (do not inline into a later result) per plan-compliance.md.

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (or the new module)

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` succeeds.
- The termination lemma(s) are stated against `modalApplyOneKb5'` (not the Five alias) and are
  sorry-free, axiom-clean.

---

### Phase 4: RuleApplicationSpecCore instance (nine-field discharge) [NOT STARTED]

**Goal**: Land `modalApplyOneKb5'_specCore : RuleApplicationSpecCore modalApplyOneKb5'`,
discharging all nine fields.

**Tasks**:
- [ ] Mirror `modalApplyOneFive_specCore`'s nine-field structure
  (`FiveSimplification.lean:1393-1403`): `freshLocal`, `outputsSubsetUniverse`,
  `persistentFresh`, `branchingLength`, `localShapeInvariance`, `boxPosNotExpanding`,
  `diaNegNotExpanding`, `boxNegWitness'`, `diaPosWitness'`.
- [ ] For fields where the new root arm behaves identically to Five (all non-root arms, and the
  `.pos .box`/`.neg .diamond` non-expanding arms), reuse the Five field proofs' structure.
- [ ] For fields touching the changed root arm (`boxNegWitness'`, `diaPosWitness'`,
  `outputsSubsetUniverse`, `persistentFresh`), re-prove against the full-cluster-dump shape,
  using the Phase 3 termination lemmas where world-membership/universe reasoning is needed.
- [ ] Each field is its own supporting lemma (mirroring the `modalApplyOneFive_*` helper lemmas)
  before assembly into the instance — do not inline.
- [ ] If a field is genuinely not provable for the new root arm, STOP: mark this phase [BLOCKED],
  record the exact field, the goal state reached, and what is missing. Do NOT emit a vacuous
  instance or `sorry`.

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (or the new module)

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` succeeds.
- `lean_verify Cslib.Logic.Modal.Tableau.modalApplyOneKb5'_specCore` shows only the standard axiom
  subset, no `sorry`.

---

### Phase 5: Direct KB5 soundness theorem against kb5FC [NOT STARTED]

**Goal**: Land a new soundness theorem in `FrameSoundness.lean` proving `modalTableauKb5' φ =
.closed → kb5Valid φ`, argued **directly** against `kb5FC` — NOT via `fiveValid_imp_kb5Valid`.

**Tasks**:
- [ ] Pre-code analysis (MANDATORY, plan-compliance.md): on paper, confirm the full-cluster +
  root-self propagation is validity-preserving on every `kb5FC` frame. Key facts available:
  `Relation.symm_rightEuclidean_root_refl` (`Euclidean.lean:362`, root reflexive once it has a
  successor), `rooted_cluster_isEquiv`/`RightEuclidean.equiv_cod` (`Euclidean.lean:342`, successor
  cluster is an equivalence relation), `rooted_mem_cod` (`Euclidean.lean:349`, every root successor
  lies in `cod r`). Verify the root's box content is forced at every propagated target for any
  satisfying `kb5FC` model; if a branch world can be satisfiably disconnected from the root, the
  naive dump is unsound — restrict the propagation target set accordingly (and, if that forces a
  Phase 1 rule change, raise a [BLOCKED] escalation rather than diverging silently).
- [ ] Identify the generic driver's per-rule soundness obligation (the meta-theorem
  `modalTableauFive_sound` at `FrameSoundness.lean:3763` instantiates) and discharge it for
  `modalApplyOneKb5'`'s root arm using the cluster facts above.
- [ ] Land `theorem modalTableauKb5_sound'` (or a documented rename of `modalTableauKb5_sound`
  :3817 to depend on the new rule — implementer's call, flagged as a plan deviation and raised as
  a blocker first if it changes the existing declaration's statement). It must NOT route through
  `fiveValid_imp_kb5Valid` (:3808) / `kb5FC_imp_fiveFC` (:3802).
- [ ] Add a docstring contrasting this with the retired Phase 22 monotonicity shortcut and citing
  the Phase 23 blocker note (`FrameCompleteness.lean:3300-3339`) for why the shortcut is
  unavailable.

**Timing**: 2.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` succeeds.
- `lean_verify` on the new soundness theorem shows only the standard axiom subset, no `sorry`,
  and its dependency graph does NOT include `fiveValid_imp_kb5Valid`.

---

### Phase 6: Verification, axiom audit, CI, and docstring reconciliation [NOT STARTED]

**Goal**: Prove the whole task green and axiom-clean; reconcile the KB5 module notes.

**Tasks**:
- [ ] Run `lean_verify` (fully-qualified names) on EVERY new public declaration from Phases 1-5;
  confirm each shows only a subset of `[propext, Classical.choice, Quot.sound]` and no `sorry`.
- [ ] `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` and
  `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` both green.
- [ ] Check task 511's status re `Cslib/Logics/Modal/Tableau/LoopChecking.lean`. If task 511 has
  resolved its mid-edit, run the full CSLib CI order (`lake build`, `lake exe checkInitImports`,
  `lake lint`, `lake exe lint-style`, `lake test`, and — only if a new file was added —
  `lake exe mk_all --module`, `lake shake`). If task 511 is still mid-edit, run the scoped module
  builds only and record the deferred full-CI sweep as a transient gate. Do NOT touch
  LoopChecking.lean.
- [ ] Update the KB5-instantiation module note (`FiveSimplification.lean:1405-1432`) to state that
  a genuine KB5-specific rule now exists alongside the soundness-only alias, with a one-line
  pointer to `modalApplyOneKb5'`. Do NOT edit `FrameCompleteness.lean` (follow-on task territory).

**Timing**: 1 hour

**Depends on**: 4, 5

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (docstring reconciliation only)

**Verification**:
- All `lean_verify` audits clean.
- Scoped module builds green; full CI green if the task-511 gate is clear, else deferred sweep
  documented.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` — green.
- [ ] `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` — green.
- [ ] `lean_verify` on `modalApplyOneKb5'`, its driver chain, termination lemmas,
  `modalApplyOneKb5'_specCore`, and the new soundness theorem — each only the standard axiom
  subset, zero `sorry`.
- [ ] New soundness theorem's dependency graph excludes `fiveValid_imp_kb5Valid`/`kb5FC_imp_fiveFC`.
- [ ] Full CSLib CI pipeline green (subject to the task-511 LoopChecking.lean gate in Phase 6).
- [ ] Zero new `axiom` declarations anywhere; zero vacuous placeholders.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` — `modalApplyOneKb5'`, driver chain,
  rfl bridges, termination lemmas, `modalApplyOneKb5'_specCore`, updated module note.
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — new `kb5FC`-direct soundness theorem.
- `Cslib/Logics/Modal/Tableau/Kb5Simplification.lean` — only if the sibling-file option is chosen
  in Phase 1 (default is the same-file KB5 section).
- `specs/524_kb5_full_cluster_rule_and_soundness/summaries/01_*-summary.md` — execution summary.

## Rollback/Contingency

- All new declarations are additive; the existing `modalApplyOneKb5` alias and
  `modalTableauKb5_sound` corollary stay in place, so reverting is deleting the new declarations
  and the Phase 6 docstring edit. If any phase blocks, mark it [BLOCKED] with the exact goal
  state and preserve the sorry-free earlier phases (they are independently verifiable and
  committable). Never discard uncommitted green work to reach a passing build — fix forward or
  escalate per `.claude/rules/error-handling.md`.
