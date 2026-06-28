# Phase 1 Handoff — Closed-Branch Lemma Cluster Fixed

**Session**: sess_1782538677_f01f15_364
**Phase**: 1 (COMPLETED)
**Date**: 2026-06-27

## What Was Done

Phase 1 is complete. The closed-branch lemma cluster (lines ~63-200 in Soundness.lean) now
builds cleanly. All errors at lines < 228 are eliminated.

### Fixes Applied

1. **Line 124-126** (`modalClosed_unsat`, T(⊥) case, Family 2+bot):
   - Changed `simp only [Satisfies] at hsat` to `change False at hsat; exact hsat`
   - Root cause: `HasBot.bot : Proposition Atom` is a typeclass method `@Bot.bot _`,
     not syntactically `.bot`. `simp [Satisfies]` cannot reduce it. `change False`
     works because Lean's definitional checker handles `HasBot.bot = .bot`.

2. **Line 154** (`modalClosed_unsat`, contradiction case neg branch, Family 1):
   - Changed `simp only [hsf, Sign.isPos, ite_false] at hsfcond` to
     `simp [hsf, Sign.isPos] at hsfcond`
   - Root cause: `ite_false` is a Prop-level lemma; the if-expression uses Bool
     branching. Dropping `only` and `ite_false` lets simp use the Bool reduction lemmas.

3. **Lines 157-183** (`extendBranchSat` lemma — DELETED):
   - This private lemma was never called anywhere in the file.
   - It had a Lean 4.31.0 universe polymorphism elaboration issue: `⟨W, ...⟩` for
     `∃ (W : Type*)` fails when W comes from an implicit argument `{W : Type*}` because
     the two `Type*` universe metavariables (`u_2` for the argument, `u_3` for the
     existential) are not unified by Lean 4.31.0's elaborator.
   - Multiple approaches failed: `.{v}` explicit universe, `unfold branchSatisfiable`,
     `use W, m, f, hacc`, changing signature to take packed `hsat : branchSatisfiable b acc`.
   - Resolution: Deleted the dead lemma entirely. Zero impact on any other proof.

4. **Lines 195-199** (`accFreshInv_empty`, accessibility empty base case):
   - Added `exact absurd hedge (by decide)` after the simp.
   - Root cause: `simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil]`
     reduces `hedge : acc.hasEdge w w'` to `hedge : false = true` but leaves the
     original goal unsolved. Need explicit contradiction discharge.

## Current Build State

- **Phase 1 errors**: 0 (lines < 228 all clean)
- **Remaining errors** (Phase 2 territory, lines 228+):
  - Line 228-229: unsolved goals / no goals to be solved (Family-3 `hnewBs` cascade start)
  - Line 276: `cases` failed (Family-1 in T-side of `modalStepBranch_preserves_sat`)
  - Lines 304, 336, 363, 403: `Unknown identifier 'hnewBs'` (Family-3 T-side cascade)
  - Line 625: `cases` failed (Family-1 in F-side)
  - Lines 650, 706, 730: `Unknown identifier 'hnewBs'` (Family-3 F-side cascade)
  - Line 747: `Duplicate alternative name 'imp'` (drift issue in F-side)
  - Lines 804+: `List.bind`, `List.mem_zip` unknown, `b` unknown (Phase 4 territory)

## Next Phase Instructions (Phase 2)

Phase 2: Fix the T-side (positive-sign) cases of `modalStepBranch_preserves_sat`.

The theorem starts around line 175 (after the Phase 1 deletions shifted line numbers).
Key tasks:
1. Read lines ~228-250 to understand the context before the first hnewBs error
2. Use `lean_goal` at line ~228 to see the post-simp state of `hsf`
3. The `obtain ⟨⟨hnewBs,_⟩,hnewAcc⟩ := hsf` pattern fails because the simp
   at `simp only [modalApplyOne]` + `simp [tryAllPropRules, ...]` changed the
   shape of `hsf`. The `hnewBs` no longer binds correctly.
4. Fix: extend the simp set at the `simp [tryAllPropRules, ...]` call to include
   `Option.some.injEq`, `Prod.mk.injEq`, and recognizer unfolds so `hsf` normalizes
   to a nested conjunction that the original `obtain` can match.
5. Alternative: change the `obtain` pattern to match the new shape of `hsf`.
6. Also fix the `cases sf.sign` drift (Family-1) at line 276.

The T-side cases to fix (approximate lines after Phase 1 shift):
- box case: ~228 (first `hnewBs` failure)
- negPos case: ~276 + ~304
- orPos case: ~336
- impPos cases: ~363, ~403

Note the line numbers have shifted approximately 25 lines earlier due to deleting
`extendBranchSat` (27 lines). Original plan referred to lines 185-400, so actual
lines are now approximately 160-375.

## File State

`Cslib/Logics/Modal/Tableau/Soundness.lean` — modified from WIP commit plus Phase 1 fixes.
Key changes vs pre-drift:
- Line ~124: `change False at hsat; exact hsat` (was `simp only [Satisfies]`)
- Line ~154: `simp [hsf, Sign.isPos]` (was `simp only [hsf, Sign.isPos, ite_false]`)
- Lines 157-183: DELETED (extendBranchSat — was dead code)
- Line ~198: Added `exact absurd hedge (by decide)` after simp
