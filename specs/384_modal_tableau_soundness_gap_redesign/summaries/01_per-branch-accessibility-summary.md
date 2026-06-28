# Implementation Summary: Task #384 — Per-Branch Accessibility Soundness-Gap Redesign

- **Task**: 384 - modal_tableau_soundness_gap_redesign
- **Status**: [COMPLETED]
- **Completed**: 2026-06-28
- **Phases**: 1 [COMPLETED], 2 [COMPLETED], 3 [COMPLETED], 4 [COMPLETED], 5 [COMPLETED], 6 [COMPLETED]

## What Was Done

Task 384 closed the soundness-proof gap that blocked task 364. The gap originated from a false
proof obligation in `modalExpandBranches_closed_unsat`: the old single-`acc` design required
showing that `branchSatisfiable` is anti-monotone under edge addition, which is false. The fix
(Option A from the research report) threads a parallel `accs : List Accessibility` (one per
worklist branch) through `modalExpandBranches`/`processNext`, so each branch carries its own
local accessibility relation and no edge fired on one branch can pollute a sibling.

### Phase 4: `modalExpandBranches_closed_unsat` reformulation (Soundness.lean)

The core soundness lemma was reformulated with the new signature:

```lean
theorem modalExpandBranches_closed_unsat (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      List.Forall₂ (fun b acc => accFreshInv b acc) branches accs →
      modalExpandBranches branches expandedSets accs fuel = .closed →
      List.Forall₂ (fun b acc => ¬branchSatisfiable.{v, u} b acc) branches accs
```

Key implementation decisions:

1. **Private helper lemmas added** (replacing unavailable Mathlib imports):
   - `forall₂_append_aux`: `List.Forall₂ R l1 m1 → List.Forall₂ R l2 m2 → List.Forall₂ R (l1++l2) (m1++m2)` (replaces `List.rel_append` which is in `Mathlib.Data.List.Forall2`, not imported)
   - `forall₂_drop_aux`: `List.Forall₂ R l1 l2 → List.Forall₂ R (l1.drop n) (l2.drop n)` (replaces `List.forall₂_drop`)
   - `forall₂_take_aux`: analogous for `take` (replaces `List.forall₂_take`)

2. **`forall₂_of_zip_mem` fix**: Changed `exact h (List.mem_cons_self _ _)` to `apply h; simp` to avoid a Lean 4.31.0 elaboration issue where the argument wasn't reducible at application time.

3. **Fuel-0 case**: Replaced `simp only at hfn; split_ifs at hfn with hcl` (which produced "no goals" for the second bullet) with `cases h : isModalClosed b` — cleaner and avoids the split_ifs issue.

4. **`List.length_replicate` usage fix**: The original code wrote `List.drop_left' (List.length_replicate newBs.length newAcc)` which incorrectly tries to apply the theorem (a Prop) to explicit args. Fixed to `List.drop_left' List.length_replicate` (letting Lean infer implicit args from context).

5. **Freshness threading**: Done via `modalStepBranch_preserves_accFreshInv` (Phase 3) + `forall₂_replicate_right` for the expanded branch slot; sibling branches keep their original `accs[j]` unchanged. The two false anti-monotonicity obligations from the old design never arise.

### Phase 5: `modalTableau_sound` call site

The call site was already correctly updated (by the previous Phase 3/4 agent) to pass:
- `branches = [[⟨.neg, φ, 0⟩]]`, `expandedSets = [[]]`, `accs = [Accessibility.empty]`
- Length proofs via `rfl rfl`
- Freshness via `List.Forall₂.cons (accFreshInv_empty _) List.Forall₂.nil`
- Result extraction via `cases hunsat with | cons h_unsat _ => exact h_unsat hsat`

## Plan Deviations

1. **`List.rel_append` / `forall₂_drop` / `forall₂_take`**: The plan referenced using Mathlib lemmas with those names. They exist in `Mathlib.Data.List.Forall2` but that module is NOT transitively imported by `Cslib.Init` → `Saturation.lean` → `Soundness.lean`. Replaced with private local lemmas `forall₂_append_aux`, `forall₂_drop_aux`, `forall₂_take_aux` (proved inline, ~20 lines).

2. **`forall₂_of_zip_mem` elaboration fix**: Not anticipated in the plan. The `exact h (List.mem_cons_self _ _)` pattern fails in Lean 4.31.0 for this usage; replaced with `apply h; simp` which is equivalent.

3. **`List.length_replicate` argument error**: Not anticipated. The original code incorrectly applied the theorem to explicit arguments; fixed to let Lean infer.

## CI Results

- `lake build Cslib.Logics.Modal.Tableau.Soundness`: **green** (480 jobs)
- `lake lint`: **no warnings in Soundness.lean** (pre-existing SoundnessStep.lean warnings unchanged)
- `lake exe lint-style`: **clean** for Soundness.lean
- `lake shake --add-public --keep-implied --keep-prefix`: **no issues** in Soundness.lean
- Zero `sorry` in all modal tableau files
- Zero new axioms introduced
- Full `lake build`: fails only on pre-existing `Propositional.Tableau` `module` keyword issue (unrelated to this task, present before task 384)

## Key Files Modified

- `/home/benjamin/Projects/cslib-364/Cslib/Logics/Modal/Tableau/Soundness.lean` — phases 3+4+5
- `/home/benjamin/Projects/cslib-364/specs/384_modal_tableau_soundness_gap_redesign/plans/01_per-branch-accessibility.md` — phases 4+5 marked [COMPLETED]
