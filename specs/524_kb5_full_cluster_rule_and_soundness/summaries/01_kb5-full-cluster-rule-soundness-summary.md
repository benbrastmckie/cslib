# Execution Summary: KB5 Full-Cluster Propagation Rule and Direct Soundness

- **Task**: 524 - kb5_full_cluster_rule_and_soundness
- **Status**: [COMPLETED]
- **Plan**: plans/01_kb5-full-cluster-rule-soundness.md

## What Was Built

A genuinely new KB5-specific tableau rule, `modalApplyOneKb5'`, alongside (not replacing) the
existing `modalApplyOneKb5 := modalApplyOneFive` alias:

1. **`modalKb5BoxAllFull`/`modalKb5DiaNegAllFull`** (`FiveSimplification.lean`): full-cluster
   propagation helpers. Non-root targets are unconditional (matching the non-root arm's own
   unconditional propagation); a root trigger additionally propagates back onto world `0` itself
   whenever the known cluster has some other, non-root member.
2. **`modalApplyOneKb5'Prop`/`modalApplyOneKb5'`**: the rule itself. Mint (existential) shapes
   (`.pos .diamond`/`.neg .box`) are verbatim `modalApplyOneFive` witness-reuse behavior; only the
   two propagation (universal) shapes differ.
3. **Driver chain**: `modalStepBranchKb5'`/`modalExpandBranchesKb5'`/`modalTableauKb5'` plus `rfl`
   bridge lemmas.
4. **`Kb5'WorldInv`/`modalMaxWorld_lt_worldBound_of_Kb5'WorldInv`**: the termination bound,
   `rfl`-equal to Five's own `FiveWorldInv` (rule-independent machinery; the changed shapes never
   mint, so the bound transfers without re-derivation).
5. **`modalApplyOneKb5'_specCore : RuleApplicationSpecCore modalApplyOneKb5'`**: all nine fields
   discharged, mirroring `modalApplyOneFive_specCore`.
6. **`modalTableauKb5'_sound`** (`FrameSoundness.lean`): proved directly against `kb5FC`, NOT via
   the `fiveValid_imp_kb5Valid` frame-class-monotonicity shortcut (confirmed by grep: the new
   theorem's dependency chain does not reference it). Key new semantic facts:
   `reachable_imp_related_kb5`/`accReachableInv_related_kb5`/`accReachableInv_kb5_root_refl` --
   simpler than Five's cod-equivalence route since `kb5FC`'s `Std.Symm` conjunct lets the
   `ReflTransGen` reachability path anchor directly at `f 0`.

## Grounding Clarification (recorded in Phase 1)

The plan's Phase 1 task-bullet literally named the mint shapes (`.pos .diamond`/`.neg .box`) as
the ones needing a root-arm change, but the Overview, Risks table, and the actual
`FrameCompleteness.lean:3327-3332` Phase 23 blocker note (the plan's own grounding source) all
independently describe the change as targeting the propagation shapes (`.pos .box`/
`.neg .diamond`) -- "root box/diamond triggers dumping to the full known non-root cluster... the
rule would additionally need to propagate root's own box content back onto world 0". A semantic
check confirmed only the propagation-shape reading is soundness-compatible (turning an
existential mint into a universal claim at every known world would be unsound in general). Implemented
against the propagation shapes per the 3-of-4-source grounding; documented as a clarification, not
escalated as a blocker, since it resolves an internal inconsistency rather than changing scope.

## Verification

- `lake build` (full project, 3238 jobs): green.
- `lake exe checkInitImports`: exit 0.
- `lake lint`: zero findings in either touched file (one pre-existing, unrelated error elsewhere).
- `lake exe lint-style`: clean.
- `lake shake --add-public --keep-implied --keep-prefix`: zero import-minimization findings for
  either touched file.
- `lake test`: one pre-existing, unrelated failure (`CslibTests.ModalFrameSeparation`, a
  `decide`-reduction stall in `FrameCompleteness.lean`'s `instDecidableS5Valid`/
  `instDecidableFiveValid`, a file this task never touched -- confirmed via `git status`/`git log`).
- `lean_verify` on every key new declaration: standard `[propext, Classical.choice, Quot.sound]`
  axiom subset (several needing none), zero `sorry`. Cross-checked one result against
  `lake env lean #print axioms` directly.
- Zero new `axiom` declarations (repo-wide count unchanged by this task's diff).
- Zero vacuous placeholders.

## Task 511 / LoopChecking.lean Gate

Task 511 (`s4_loop_checking_termination`) is `partial` in `specs/state.json` -- its
`LoopChecking.lean` work is not yet resolved. `LoopChecking.lean` was not touched by this task.
The full CI pipeline was run anyway since the plain project build is green; the one `lake test`
failure found is unrelated to task 511's scope (it is in `FrameCompleteness.lean`'s `Decidable`
instances, from task 515) and unrelated to this task's changes.

## Plan Deviations

- Phase 1: implemented against the propagation shapes (`.pos .box`/`.neg .diamond`) rather than
  literally following the mint-shape wording in that phase's task bullet -- see "Grounding
  Clarification" above. Not a scope change; resolves an internal plan inconsistency using the
  plan's own dominant, better-grounded description.
- No sibling `Kb5Simplification.lean` file was created; all new content landed in
  `FiveSimplification.lean`'s existing KB5 section, per the plan's stated default.

## Files Modified

- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`

## Commits

- `ea8eba07` task 524 phase 1-2
- `8200b8de` task 524 phase 3
- `b26c3528` task 524 phase 4
- `2b1c8b04`, `b15706d2`, `7839419d`, `1eae73c5` task 524 phase 5 (four incremental green commits)
- (this summary + final plan/metadata commit)
