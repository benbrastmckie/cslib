# Implementation Summary: Composite Conservativity Bridges to the Classical Column

- **Task**: 520
- **Plan**: plans/01_composite-conservativity-bridges.md
- **Status**: Implemented

## What Was Done

Added one `public import` and 8 composite theorems to
`Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean`, each collapsing a non-classical
propositional base (minimal `M*` or constructive `C*`) into the classical column at the
matching modal rung (K/T/S4/S5). Each theorem is a one-line composition of an existing
Axis-B monotonicity edge (`PropositionalStrengthMonotonicity.lean`, already in scope) with an
existing Int->Classical bridge (`IntToClassical.lean`, newly imported):

- `mkDerivable_implies_kDerivable`, `mtDerivable_implies_tDerivable`,
  `ms4Derivable_implies_s4Derivable`, `ms5Derivable_implies_s5Derivable`
- `ckDerivable_implies_kDerivable`, `ctDerivable_implies_tDerivable`,
  `cs4Derivable_implies_s4Derivable`, `cs5Derivable_implies_s5Derivable`

Both S5 composites conclude `Derivable (@ModalAxiom Atom) φ` (not `S5Axiom`), matching
`is5Derivable_implies_s5Derivable`'s target. No `conservative` naming used; all 8 are `theorem`.

## Verification

- Scoped build `lake build Cslib.Logics.Modal.Metalogic.InterSystem.Modularity`: green.
- Full `lake build`: green (3237 jobs).
- `lake exe checkInitImports`: green.
- `lake lint`: exactly 1 pre-existing error, unrelated to this file
  (`Foundations/Logic/Metalogic/PrimeExclusion.lean` unusedArguments).
- `lake exe lint-style`: green, 0 issues.
- `lake shake` scoped to Modularity.lean: zero suggestions (the one new import is minimal).
- `lake test`: fails only in `CslibTests.ModalFrameSeparation` -- a pre-existing
  KB5/Five-simplification decidability issue tracked under a separate concurrent task,
  explicitly flagged out-of-scope for this dispatch.
- `#print axioms` on all 8 fully-qualified names: `[propext, Quot.sound]` -- a strict subset
  of the expected `[propext, Classical.choice, Quot.sound]` (`Classical.choice` simply isn't
  needed). Zero `sorry`, zero new axioms, zero vacuous placeholders.

## Plan Deviations

1. **Concurrent build interference (transient, resolved)**: while implementing, a separate,
   uncommitted, in-flight edit to `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean`
   (a different task, mid-implementation, changing its import from `Intuitionistic.PrimeTheory`
   to two direct imports) transiently broke the scoped build's transitive dependency chain
   (`SegmentLindenbaum.lean` referenced now-unresolved identifiers). This was confirmed
   unrelated to this task's edits by reproducing the same failure on
   `PropositionalStrengthMonotonicity.lean` alone (already imported into `Modularity.lean`
   before this task started). Verified the 8 new composites compile correctly by building in an
   isolated `git worktree` (checked out at HEAD, with the concurrent edit absent) using a
   hardlinked copy of the `.lake` build cache. The concurrent edit was reverted/cleared by its
   owning task partway through this dispatch; the scoped and full builds were then re-confirmed
   green directly in the main tree.
2. **Build-cache side effect from the isolated-worktree check (self-corrected)**: the
   hardlinked `.lake` cache used for the isolated-worktree verification left 3 trace files in
   the main tree's `.lake/build` pointing at the (now-deleted) temporary worktree path
   (`Modularity.trace`, `CslibTests/GrindLint.trace`, `CslibTests/ImportWithMathlib.trace`),
   because Lean's trace-file writes are not atomic-rename-safe across hardlinks. Detected via
   `grep -rl` for the leaked path across `.lake/build`, fixed by deleting and rebuilding exactly
   those 3 files' outputs, and confirmed zero remaining references before finishing. No source
   files were affected; no other task's build state was touched.
3. **Axiom closure narrower than the plan's expectation**: the plan expected
   `[propext, Classical.choice, Quot.sound]`; the actual closure for all 8 is
   `[propext, Quot.sound]`. This is a stricter (better) result, not a defect -- documented
   inline in the plan's Phase 2 checklist.

## Files Modified

- `Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean`
