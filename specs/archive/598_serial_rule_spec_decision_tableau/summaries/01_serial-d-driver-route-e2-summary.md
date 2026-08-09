# Implementation Summary: Serial (D) Driver via Route E2

- **Task**: 598 — serial_rule_spec_decision_tableau
- **Plan**: `specs/598_serial_rule_spec_decision_tableau/plans/01_serial-d-driver-route-e2.md`
- **Status**: [PARTIAL] — Phases 1-8 landed green, fully sorry-free (the twelve-field
  `RuleApplicationSpecAt` witness for D is complete and machine-checked); Phase 9 is
  [BLOCKED] on `modalExpandBranchesD_hintikka`, with a precisely measured cascade and a decision
  point recorded for the orchestrator/user rather than absorbed silently
- **Files changed**: `Cslib/Logics/Modal/Tableau/FrameRules.lean` (additive, 92 lines),
  `Cslib/Logics/Modal/Tableau/GenericDriver.lean` (additive, 200 lines),
  `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (19 lines, F2 hypothesis narrowing),
  `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (9 lines, F2 call-site updates),
  `Cslib/Logics/Modal/Tableau/DDriver.lean` (new file, ~1,326 lines), `Cslib.lean` (barrel
  registration, 1 line), `specs/state.json` (`file_scope` widening record)
- **Zero-debt**: zero `sorry`, zero new `axiom`, zero vacuous placeholders across every dispatch;
  `#print axioms` on `modalApplyOneD_specAt` (the twelve-field bundle) and every phase's
  top-level lemma reports only `propext`/`Classical.choice`/`Quot.sound`

## What Landed (Phases 1-8, all green, independently CI-verified, zero sorry)

1. **Phase 1 — D rules in `FrameRules.lean`**: `modalDBoxDual`/`modalDDiaNegDual` (the two
   PERSISTENT dual arms, `T(□ψ)@w ⊢ T(◇ψ)@w` / `F(◇ψ)@w ⊢ F(□ψ)@w`), `modalApplyOneD`, and
   `modalApplyOneD_eq_of_not_boxPos_diaNeg`, lifted from the preserved prototype. 92 lines,
   purely additive.

2. **Phase 2 — Additive `RuleApplicationSpecAt` sibling in `GenericDriver.lean`**:
   `RuleApplicationSpecCoreAt φ0 apply` / `RuleApplicationSpecAt φ0 apply`, narrowing F2
   (`outputsSubsetUniverse`) from `∀ φ0, …` to a single fixed `φ0`, plus
   `RuleApplicationSpecCore.toAt`/`RuleApplicationSpec.toAt` projections. `RuleApplicationSpec`/
   `RuleApplicationSpecCore` and all seven existing discharge sites (K, T, B, TB, Five, Kb5'',
   S5w) are byte-identical to HEAD. 200 lines, purely additive.

3. **Phase 3 — F2 hypothesis narrowing (`file_scope` widened)**: narrowed
   `modalExpMeasure_step_lt_gen`'s `hOutputsSubsetUniverse` parameter to the lemma's own
   already-bound `φ0`, fixed the single interior application and two consumption call sites in
   `CompletenessLoop.lean`, added `modalStepBranchGenAt_expMeasure_step_lt` (the `…At`-typed
   sibling of `modalStepBranchGen_expMeasure_step_lt`). **Measured against the plan's own Scope
   Hypothesis**: only 2 of the 4 named `CompletenessLoop.lean` sites (`:1347`, `:1644`
   equivalents) actually needed edits — the other 2 (`:458`, `:984` equivalents) call the
   `RuleApplicationSpec`/`RuleApplicationSpecCore` **field** directly, not the narrowed `_gen`
   lemma, and the field type itself is untouched, exactly as the plan's own hint flagged as worth
   confirming. **`file_scope` widened** to add `FmpMeasure.lean` and `CompletenessLoop.lean`,
   recorded in `specs/state.json`, per the plan's SCOPE DECISION block.

4. **Phase 4 — `modalDualAugment` and its lemmas**: the dual-closed universe seed (`φ` conjoined,
   via a right-nested `.and` fold, with the dual of every box/diamond subformula of `φ`);
   `modalDualAugment_self_mem`; both dual-closure directions
   (`modalDualAugment_box_dual`/`_dia_dual`) — confirming the plan's "one round suffices"
   hypothesis; `modalDualAugment_depth_eq` (depth preservation); and
   `modalExpMeasure_entry_le_fuel_at` (the entry-measure bound generalized to a separate universe
   seed). 406 lines — well above the ~110-line estimate, because the fold-based construction
   needed more supporting membership/elimination lemmas than a straight lift from the prototype
   would have suggested.

5. **Phase 5 — D driver triple and shape lemmas**: `modalStepBranchD`/`modalExpandBranchesD`/
   `modalTableauD` (the last fuelled at `modalFuel (modalDualAugment φ)`, not plain `φ`, since
   D's outputs are only universe-closed at the dual-closed seed — **not** literally
   `modalTableauGen modalApplyOneD φ` for this reason, a deliberate divergence from T's byte-
   identical instantiation), plus the box-positive/diamond-negative shape-dispatch lemmas
   mirroring `TDriver.lean:87-260`. `modalApplyOneD_boxPos_snd`/`_diaNeg_snd` lifted from the
   preserved prototype (machine-checked there). Built clean on first attempt.

6. **Phase 6 — Field discharges F1-F4**: `freshLocal` (F1, lifted), `outputsSubsetUniverse` at
   the fixed seed `modalDualAugment φ` (F2 — the field that genuinely fails at a plain seed, per
   `modalApplyOneD_outputsSubsetUniverse_fails`, proved here via new dual-closure membership
   helpers `modalUniverse_dualAugment_mem_box_dual`/`_dia_dual`), `persistentFresh` (F3), and
   `rankStep` (F4, using `modalDepth_diamond_eq_box` in place of T's strict depth decrease — D's
   dual emits an equally-deep formula, not a strictly shallower one, but both satisfy the `≤`
   this field needs).

7. **Phase 7 — Field discharges F5-F7**: `outDegStep`, `knownWorldsStep`, `branchingLength`. D
   never touches `acc` or produces `.branching` at the two D-relevant shapes, so K's own proofs
   transport with the dual formula's known-world membership as the only new content. Built clean
   on first attempt.

8. **Phase 8 — F8-F12 and the `RuleApplicationSpecAt` bundle**: `localShapeInvariance` (F8),
   `boxNegWitness'`/`diaPosWitness'` (F11'/F12') lifted from the preserved prototype essentially
   verbatim; `boxPosNotExpanding`/`diaNegNotExpanding` (F9/F10) derived fresh as quick corollaries
   of phase 5's fst-dispatch lemmas — **the prototype's own module docstring claimed F9/F10 were
   machine-checked, but its body never actually contained them as separate lemmas** (a
   documentation/content mismatch discovered during this task, corrected by deriving them here).
   Assembled `modalApplyOneD_specAt : RuleApplicationSpecAt (modalDualAugment φ) modalApplyOneD`,
   the complete twelve-field witness — `#print axioms` reports only the three standard axioms.

## Phase 9 — [BLOCKED]: `modalExpandBranchesD_hintikka` requires an unplanned ~755-line twin chain

**What landed in Phase 9**: the three `_eq` bridges (`modalStepBranchD_eq`,
`modalExpandBranchesD_eq`, `modalTableauD_eq`, all `rfl`), and `DDriver.lean`'s registration in
`Cslib.lean` (via `mk_all`). The full repository build (3324 jobs), `checkInitImports`, and
`lint-style` are all green with zero new findings; `lake lint` shows zero new findings in any of
the five touched files (its two pre-existing findings, in `FmpMeasure.lean` and unrelated
`Temporal/Metalogic/DenseSoundness.lean`, both predate this task).

**What is blocked**: `modalExpandBranchesD_hintikka`, mirroring `TDriver.lean:792-806`'s
one-liner, cannot be written as a one-liner. `TDriver.lean`'s version works because it hands a
full `RuleApplicationSpec modalApplyOneT` to the generic top-loop engine
`modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean:1874`), which internally narrows to
`RuleApplicationSpecCore` via `.toCore` and calls the induction engine
`modalExpandBranchesHintikka` (`CompletenessLoop.lean:1433`). D can only ever supply
`RuleApplicationSpecCoreAt (modalDualAugment φ) modalApplyOneD` — a **different, non-coercible
type** from `RuleApplicationSpecCore apply` (F2 genuinely fails at a universal `φ0` for D). No
existing declaration accepts the `…At`-narrowed interface at the level
`modalExpandBranchesHintikka` needs it.

**Measured cascade** (full detail in the plan's Phase 9 BLOCKER block): closing this requires
purely-mechanical (type-swap-only) additive `…At`-typed twins of seven declarations in
`CompletenessLoop.lean`, totalling **~755 lines**:

| Declaration | Lines | Twin needed because |
|---|---|---|
| `modalLoopGen_bClosure_core` | 49 | uses `outputsSubsetUniverse` directly |
| `modalLoopGen_eBoxOnlyNeg_core` | 58 | nominal typing only |
| `modalLoopGen_eDiamondOnlyPos_core` | 58 | nominal typing only |
| `modalLoopGen_eBoxNegWitness_core` | 73 | nominal typing only |
| `modalLoopGen_eDiamondPosWitness_core` | 80 | nominal typing only |
| `modalStepHintikka_preserves_inv` | 64 | threads the above five |
| `ModalLoopAuxK_stepPreserved` | 49 | threads `spec`-typed calls |
| `modalExpandBranchesHintikka` | **324** | the big fuel-induction engine |

`AuxStepPreserved`/`AuxBounds`/`ModalLoopInvHintikka`/`ModalLoopAuxK`/`ModalLoopAuxK_bounds` are
apply/`φ0`-generic (no spec type embedded) and transport to D for free, with zero new code —
only the seven declarations above are actually blocked.

This is not the "mechanically forced ~10 line" edit phase 3's narrowing was; it is a second major
undertaking, comparable in size to phases 4-8 combined, landing entirely in
`CompletenessLoop.lean` (2302 lines before this task — the twin chain would add roughly a third
more to that file). This is exactly the scenario the plan's own Rollback/Contingency section
named in advance: *"A `CompletenessLoop.lean` refactor is outside both the declared `file_scope`
and Route E2's additivity claim, and would justify re-opening the route decision rather than
absorbing the cost silently."* Per the Escalation Protocol and `plan-compliance.md`, this blocker
is recorded rather than silently absorbed or worked around with a placeholder.

**Decision needed** (orchestrator/user level, not the implementing agent), between:

1. **Widen `file_scope` further and spawn a successor task** for the `…At`-typed twin chain
   (~755 lines, `CompletenessLoop.lean`), depending on this task — the natural sibling of the
   plan's own out-of-scope-follow-up decision for the soundness/completeness arm below.
2. **Generalize the seven declarations in place** to take raw, unbundled hypotheses (the pattern
   `FmpMeasure.lean`'s `_gen` lemmas and phase 3's own narrowing already use) instead of a
   bundled `RuleApplicationSpecCore`-typed parameter — a bigger, cross-cutting refactor
   `CompletenessLoop.lean`'s own docstring names as future work (`CompletenessLoop.lean:965-966`)
   but does not commit to for the `…At` case specifically.

## Out-of-Scope Follow-Up (unchanged from the plan): The `Decidable` Instance

Untouched by this task, exactly as the plan specifies: `instDecidableDValid`,
`modalTableauD_sound`, `modalTableauD_complete`, `serialGen`, and `extractModelD`, requiring
`FrameSoundness.lean`/`FrameCompleteness.lean` (both outside the declared `file_scope`). The
plan's recommendation stands unchanged: spawn a successor task once phase 9's blocker (above) is
resolved, rather than widening this task further.

## Scope-Estimate Reconciliation

The plan's cumulative in-scope estimate was ~1,150 lines across phases 1-9 (minus the
soundness/completeness arm). Measured delivery: phases 1-8 total **1,264 lines** in
`DDriver.lean` alone, plus 92 (`FrameRules.lean`) + 200 (`GenericDriver.lean`) + 19
(`FmpMeasure.lean`) + 9 (`CompletenessLoop.lean`) = ~1,584 lines delivered and green, before
phase 9's blocked ~755-line remainder. The overrun is concentrated in phase 4 (406 vs. ~110
estimated: the fold-membership machinery for `modalDualAugment`) and phase 9's discovery (the
~755-line Hintikka-chain cascade the plan's own scope hypothesis for phase 3 flagged as a risk,
which materialized one phase later than anticipated).

## Testing & Validation

- [x] `lake build` green at the end of every phase (1-8), not only at the end of the task
- [x] Zero `sorry` in `DDriver.lean` and in every file this task's diff touches
- [x] Zero new axioms: `#print axioms` on `modalApplyOneD_specAt` and every phase's top-level
      lemma reports only `propext`, `Classical.choice`, `Quot.sound`
- [x] `RuleApplicationSpec` is byte-identical to HEAD, and all seven of its discharge sites still
      elaborate untouched (verified via `git diff` showing no deletion/modification in
      `GenericDriver.lean`, `TDriver.lean`, `BDriver.lean`, `TBDriver.lean`,
      `FiveSimplification.lean`, `S5Simplification.lean`)
- [x] No definition change to `modalSubfmls`, `isMintingShaped`, `outDeg`, `modalPotential`,
      `modalWorldBound`, or `modalFuel`
- [x] `modalApplyOneD_specAt` elaborates as a complete `RuleApplicationSpecAt` witness
- [x] The phase-3 `file_scope` widening is recorded in `specs/state.json` and named here
- [ ] Full repository gate (all 9 phases) — blocked at phase 9; phases 1-8's gate is green

## Plan Deviations

1. **Phase 3 Scope Hypothesis correction**: only 2 of the 4 hypothesized `CompletenessLoop.lean`
   consumption sites needed edits (the other 2 call the untouched struct field directly, not the
   narrowed `_gen` lemma) — the plan's own hint flagged this as worth confirming, and it resolved
   in the direction of less work, not a cascade.
2. **Phase 4 line-count overrun** (406 vs. ~110 lines estimated): the right-nested-conjunction
   fold construction needed more supporting membership/elimination lemmas
   (`mem_modalSubfmls_foldrAnd_of_base`/`_of_mem`/`_elim_of_not_and`) than a straight lift from
   the prototype's list-based `modalSubfmlsDual` would have suggested, since `modalDualAugment`
   needed to be an actual `Proposition Atom` (a universe-sizing formula), not a list.
3. **Phase 8 F9/F10 discovery**: the preserved prototype's docstring claimed F9
   (`boxPosNotExpanding`)/F10 (`diaNegNotExpanding`) were machine-checked, but its body never
   actually stated them as separate lemmas. Derived fresh (short corollaries of phase 5's
   fst-dispatch lemmas); this is a documentation defect in the prototype, not a research finding
   that needed re-litigating.
4. **Phase 9 BLOCKED** (see above): `modalExpandBranchesD_hintikka` cannot be the one-liner the
   plan estimated. Documented per the Escalation Protocol; a decision is requested rather than
   the refactor being silently absorbed or worked around.

## Files Changed (Absolute Paths)

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameRules.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/GenericDriver.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/DDriver.lean` (new)
- `/home/benjamin/Projects/cslib/Cslib.lean`
- `/home/benjamin/Projects/cslib/specs/state.json` (`file_scope` widening)
- `/home/benjamin/Projects/cslib/specs/598_serial_rule_spec_decision_tableau/plans/01_serial-d-driver-route-e2.md`
