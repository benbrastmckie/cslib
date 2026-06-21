/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

# Task 254: Revise LTL Conventions — Implementation Summary

## Status

IMPLEMENTED (all phases complete, CI passing)

## Phases Completed

All 6 phases complete:

1. **Phase 1**: Rewrote `Satisfies.lean` to use `ωSequence State` with valuation `v : Atom → State → Prop`
2. **Phase 2**: Updated `Formula.lean` syntax and notation
3. **Phase 3**: Updated `Connectives.lean`
4. **Phase 4**: Updated `OmegaExecutionSatisfies.lean`
5. **Phase 5**: Updated `OmegaRegular.lean` (including `omegaLanguage_next` and `omegaLanguage_untl` proofs)
6. **Phase 6**: Fixed all remaining build errors in `GNBA.lean` and `OmegaRegular.lean`

## Files Modified

- `Cslib/Logics/LTL/Semantics/Satisfies.lean` — new ωSequence-based API
- `Cslib/Logics/LTL/Syntax/Formula.lean` — updated syntax
- `Cslib/Foundations/Logic/Connectives.lean` — updated
- `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` — updated
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` — fixed proofs
- `Cslib/Logics/LTL/Semantics/GNBA.lean` — fixed all 10 build errors

## Key Fixes in Phase 6

### GNBA.lean fixes

1. **Atom case in `canonicalAtom_gnbaTr`** (line 769): Changed
   `simp only [Formula.canonicalAtom_mem_iff, Satisfies, ωSequence.drop, ωSequence.head, Nat.add_zero]`
   to `simp only [Formula.canonicalAtom_mem_iff, Satisfies, ωSequence.head_drop]`.
   Root cause: `ωSequence.drop` + `Nat.add_zero` simplified `(v.drop i).head` to `v (0 + i)` but not `v i`; `head_drop` lemma directly gives `(v.drop i).head = v i`.

2. **Next case in `canonicalAtom_gnbaTr`** (lines 780-789): Replaced broken `convert hsat using 1; ext n; simp [ωSequence.drop, ωSequence.tail]; ring` with `simp only [Satisfies] at hsat; rwa [ωSequence.tail_drop'] at hsat`.
   Root cause: `convert` created false equality goals; `tail_drop'` directly rewrites `(v.drop i).tail` to `v.drop (i+1)`.

3. **Atom case in `hkey`** (line 1065): Added `ωSequence.head_drop` to simp set.

4. **Next case in `hkey`** (line 1111): Changed `ωSequence.drop_succ, ωSequence.drop_tail'` to `ωSequence.tail_drop'`.
   Root cause: `drop_tail'` says `drop i (tail s) = s.drop (i+1)` but the goal had `tail (drop i s)`, which needs `tail_drop'`.

### OmegaRegular.lean fixes

5. **`omegaLanguage_next`** (line 264): Changed simp set from `[ωLanguage.mem_def, Set.mem_setOf_eq, mem_omegaLanguage, Satisfies]` to `[Formula.omegaLanguage, ωLanguage.mem_def, Set.mem_setOf_eq, Satisfies]`.

6. **`omegaLanguage_untl`** (line 294): Same fix.
   Root cause: `mem_omegaLanguage` was being applied before the def of `omegaLanguage` was unfolded; the `.toSet` accessor blocked `Set.mem_setOf_eq`.

## CI Results

- `lake build Cslib.Logics.LTL.Semantics.GNBA` — PASS
- `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` — PASS
- `lake build Cslib.Logics.LTL.Semantics.OmegaExecutionSatisfies` — PASS
- `lake exe checkInitImports` — PASS
- `lake exe lint-style` — PASS
- `lake test` — pre-existing failure in `CslibTests.Bisimulation` (unrelated to this task)

## Plan Deviations

None. All fixes follow the patterns suggested by the delegation context and the `ωSequence` API.
