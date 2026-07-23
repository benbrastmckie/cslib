# Implementation Summary: Task #502

- **Task**: 502 - Fix Segment.lean import minimization (replace transitive PrimeTheory import
  with two direct imports), consumer-first
- **Plan**: plans/02_segment-import-minimization.md
- **Status**: implemented

## What Changed

Two files, import lines only:

1. `Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean` (Phase 1): added two
   direct `public import`s -- `Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory`
   (`modalDeductiveClosure`) and `Cslib.Logics.Modal.Metalogic.DeductionTheorem`
   (`deductionTheorem`) -- so this file no longer depends on Segment.lean's transitive
   re-export for these two symbols.
2. `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean` (Phase 2): replaced the single
   `public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory` line with two direct
   `public import`s -- `Cslib.Foundations.Logic.Metalogic.PrimeExclusion` and
   `Cslib.Logics.Modal.Metalogic.DerivationTree` -- matching what Segment.lean itself directly
   consumes.

`import Cslib.Init` is unchanged in both files.

## Plan Deviations

1. **`public` vs plain import choice (Phase 1)**: the plan allowed starting with plain `import`
   when a symbol is used only in proof bodies (which is what a grep of
   `modalDeductiveClosure`/`deductionTheorem` in SegmentLindenbaum.lean showed -- always inside
   `have`s or term-mode proof arguments, never in a declaration's public *type* signature).
   Plain import was tried first and built successfully in isolation (Phase 1 verification, with
   Segment.lean untouched). After Phase 2's edit to Segment.lean, `lake build` on
   SegmentLindenbaum.lean failed: `Unknown identifier 'deductionTheorem'` with a compiler note
   that a public declaration exists but was imported privately. Root cause: `deductionTheorem`
   is used in the *body* (not just the type) of public `noncomputable def`s
   (`unpackConjPartial`, `derivImpBigAndOfAppend`) under `@[expose] public section` --
   Lean's module system requires `public import` whenever a privately-imported symbol appears in
   an exposed definition's body, not only its signature. Upgraded both `PrimeTheory` and
   `DeductionTheorem` imports on SegmentLindenbaum.lean to `public import`; rebuild succeeded.
   This is the plan's own build-feedback contingency, triggered one step earlier (at Phase 2's
   verification) than the Phase-3 shake reconciliation the plan anticipated.
2. **Phase 3 dependent-chain module names**: the plan named
   `Cslib.Logics.Modal.Metalogic.Constructive.MinExtension`/`MinPrimeTheory` as cheap dependent
   targets to spot-check. Neither file exists in the current codebase (no `Min*.lean` files
   under `Constructive/`; distinct `Metalogic.Minimal.MinExtension` etc. exist but are unrelated
   to the CK/Segment chain). Ran the full-project `lake build` instead, which is strictly more
   authoritative: 3238/3238 jobs green.

## Verification (CSLib CI Pipeline)

0. `lake exe cache get` -- cache already warm (skipped re-fetch; build proceeded fast).
1. `lake build` (full project) -- 3238/3238 jobs, zero errors.
2. `lake exe checkInitImports` -- clean, no output (all files, including both edited ones,
   import `Cslib.Init`).
3. `lake lint` -- one pre-existing error, `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean:324`
   (`unusedArguments` on `DerivExcludes` argument `_D`). This is in a file this task did not
   touch and is unrelated to the import-only change (an unused-argument lint on a declaration's
   own signature is independent of which files import it). Out of scope per the plan's
   Non-Goals (no edits to a third file).
4. `lake exe lint-style` -- clean, no output.
5. `lake shake --add-public --keep-implied --keep-prefix` -- both edited files now show only
   `remove #[import Cslib.Init]` (the known systemic false positive, shared by many other files
   in the tree, e.g. `Forcing.lean`, `CKTruthLemma.lean`). The PrimeTheory line is no longer
   flagged on Segment.lean; neither Phase-1 addition on SegmentLindenbaum.lean is flagged as
   redundant/unjustified.
6. `lake exe mk_all --module` -- "No update necessary"; `Cslib.lean` unchanged (no new files).
7. `lake test` -- one pre-existing failure: `CslibTests/ModalFrameSeparation.lean` (`decide`
   tactic stuck on `s5Valid`/`fiveValid` `Decidable` instances, lines 32/37). **Verified
   unrelated to this task**: isolated by `git stash push` on only the two edited files
   (SegmentLindenbaum.lean, Segment.lean back to HEAD) and rebuilding
   `CslibTests.ModalFrameSeparation` in isolation -- the identical two `decide` failures
   reproduce with this task's changes fully reverted, confirming a pre-existing issue unrelated
   to the Segment/SegmentLindenbaum import restructuring (a completely different logic system:
   S5/Five frame-validity decidability vs. this task's CK/constructive segment imports). Changes
   were restored (`git stash pop`) immediately after, and both edited files rebuilt green again.

8. `grep -rn '\bsorry\b'` on both edited files -- zero matches.
9. Vacuous-definition check -- none introduced (import-only change).
10. New-axiom check -- `grep -n '^axiom '` on both edited files -- zero matches.

## Files Modified

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean`
- `/home/benjamin/Projects/cslib/specs/502_fix_segment_import_minimization/plans/02_segment-import-minimization.md`
  (phase status markers + deviation annotations)

## Known Out-of-Scope Residuals (not this task's responsibility)

- `lake lint`'s one `unusedArguments` error in `PrimeExclusion.lean:324` -- pre-existing,
  unrelated file.
- `lake test`'s `CslibTests/ModalFrameSeparation.lean` `decide` failures -- pre-existing,
  reproduces identically with this task's changes reverted; unrelated logic system (S5/Five vs.
  CK/constructive).
- shake's project-wide `import Cslib.Init` flag on both edited files -- the known systemic false
  positive; `Cslib.Init` is retained per CONTRIBUTING.md and `checkInitImports` passes.
