# Implementation Summary: Task #328

- **Task**: 328 - Refactor CutElimination.lean to reduce or eliminate the maxHeartbeats 800000 override
- **Status**: [COMPLETED]
- **Date**: 2026-06-24
- **Session**: sess_1782300531_c471d6_328
- **Artifacts**: summaries/01_refactor-heartbeats-summary.md (this file)

## Outcome

Successfully reduced `maxHeartbeats` from 800000 to 210000 -- a 74% reduction. The file now
compiles cleanly with only a scoped `set_option maxHeartbeats 210000 in` annotation on the
mutual block, down from the global `set_option maxHeartbeats 800000` override.

The public API (`cutAdmissibility`, `LKProof.cutElim`, `CutFreeLKProof.mono`) remains
unchanged.

## Phase Summary

### Phase 1: Create Shared Finset Helpers (pre-existing)

The four helpers were already added before this dispatch:
- `subset_insert₂ a b s : s ⊆ insert a (insert b s)` -- double-subset insert
- `insert_subset_swap h : insert a s ⊆ insert c (insert a t)` from `h : s ⊆ insert c t`
- `CutFreeLKProof.monoL h d` -- left-side weakening using `Subset.refl` on right
- `CutFreeLKProof.monoR h d` -- right-side weakening using `Subset.refl` on left

Note: helpers changed from `private` to public scope to allow access within the `mutual` block
(Lean 4 private declarations are not visible inside `mutual` blocks from the same file).

### Phase 2: Extract cutAdm_right_* from Mutual Block (pre-existing)

The three self-recursive helpers were already extracted before this dispatch:
- `cutAdm_right_andR` (andR/andL principal case, ~140 lines)
- `cutAdm_right_orR` (orR/orL principal case, ~145 lines)
- `cutAdm_right_impR` (impR/impL principal case, ~140 lines)

The mutual block now contains only `cutAdm_right` and `cutAdm_left` (~235 lines).

### Phase 3: Replace Duplicated Finset Patterns

Applied during this dispatch:

1. **Eta-reduction**: Replaced all 44 occurrences of `(fun x hx => hsuc hx)` with `hsuc`
   via global sed substitution.

2. **`insert_subset_swap` application**: Replaced complex `Finset.insert_subset` constructions
   for `hant_a`, `hant_b`, `hant'`, `hR'` patterns with `insert_subset_swap hant` or
   `insert_subset_swap hsuc` where the resulting type matched exactly.

3. **`monoL`/`monoR` usage**: Replaced `d.mono (Finset.Subset.refl _) h` with `d.monoR h`
   and `d.mono h (Finset.Subset.refl _)` with `d.monoL h` throughout the mutual block.

4. **`subset_insert₂` usage**: Replaced `(Finset.subset_insert B s).trans (Finset.subset_insert A _)`
   with `subset_insert₂ A B s` in `cutAdm_right`, `cutAdm_left`, and `cutAdm_right_andR`.

5. **Lambda-to-trans replacement**: Replaced `(fun x hx => (Finset.f) (hant hx))` with
   `hant.trans (Finset.f)` where `Finset.f` is a monotone map.

6. **Long-line fixes**: Broke three `have hA/hB : sizeOf ... < ... := by rw [...]; omega`
   onto two lines each, and split two long `d₁'.mono` calls in `cutAdm_right_impR`.

### Phase 4: Measure and Adjust maxHeartbeats

- Attempted default (200000): fails at 205000, succeeds at 210000.
- Set `set_option maxHeartbeats 210000 in` on the `mutual` block with explanation comment.
- Final reduction: 800000 → 210000 (74% reduction, well below the 400000 target).

## CI Verification

- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination` -- PASS
- `lake exe lint-style -- Cslib/...CutElimination.lean` -- PASS (no warnings)
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK` -- PASS
- `lake shake --add-public --keep-implied --keep-prefix` -- PASS
- `lake exe mk_all --module` -- PASS (updated Cslib.lean with MplConservativeChain from task 322)
- Zero sorries in modified file
- Zero new axioms introduced
- Public API signatures unchanged

Pre-existing failures (not caused by this task):
- `Cslib.Logics.Propositional.Tableau.Classical.Completeness` -- pre-existing build error
- `Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` -- pre-existing build error
- `lake lint` -- blocked by above pre-existing failures; individual file style lint passes

## Plan Deviations

1. **Helpers made public instead of private**: The plan specified `private theorem`/`private def`
   for the shared helpers. However, Lean 4 `private` declarations are not accessible inside
   `mutual` blocks in the same file. Changed to non-private to allow access from `cutAdm_left`
   (which is inside the `mutual` block). The helpers use internal names that are not part of
   the public API conventions but are accessible to importers.

2. **Final heartbeats 210000 rather than 200000**: The default (200000) fails reliably;
   210000 is the minimum that passes consistently. This is 5% above the default but 74%
   below the original 800000 and well below the 400000 target.

3. **`hR'` in `orR` case not fully simplified**: The double-insert `hR'` construction in
   `cutAdm_left`'s `orR` case retains the three-line `Finset.insert_subset` because
   `insert_subset_swap` only handles single-insert. The pattern is cleaner than the original
   (uses `hsuc.trans` instead of a lambda) but not fully reduced.

4. **Phases 3 and 4 were marked "COMPLETED" prematurely in plan**: The plan had all four
   phases marked COMPLETED before this dispatch, but the actual file still had the eta-
   reducible lambdas and no heartbeat setting. Phases 3 and 4 were re-marked and completed
   during this dispatch.
