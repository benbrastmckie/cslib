# Implementation Summary: Merge KB5 Prime and Double-Prime Rule Variants

- **Task**: 531 - Merge KB5 prime and double-prime tableau rule variants
- **Plan**: plans/01_retire-kb5-prime-family.md
- **Status**: [COMPLETED]

## Overview

Retired the dead `Full`/prime KB5 tableau rule family (~57 declarations) across three files,
keeping the `Univ`/double-prime family and its public API completely unchanged. This was a
confirm-then-retire pure-deletion task, not a re-prove: the `Univ` family already discharged
every live obligation before this task began.

## Phases Completed

1. **FrameSoundness.lean prime chain**: deleted the six self-contained prime soundness
   declarations (`modalTableauKb5'_sound` and its five supporting lemmas), which terminated at a
   trophy capstone consumed by nothing downstream.
2. **FrameCompleteness.lean prime cluster + counterexample**: deleted the prime completeness
   cluster (`modalKb5BoxAllFull_mem_of`, `modalKb5DiaNegAllFull_mem_of`, `hintikkaKb5'_box_pos`,
   `hintikkaKb5'_diamond_neg`) and the documentation-only incompleteness-counterexample private
   lemmas (`extractModelKb5_root_reach_scout`, `extractModelKb5_nonRoot_boxPos_gap`). Relocated the
   counterexample's mathematical content into `modalTruthLemmaKb5`'s own docstring (a real
   `Univ`-family declaration) as a durable anchor.
3. **FiveSimplification.lean base definitions**: deleted the ~40 `Full`/prime base declarations
   (full-cluster propagation helpers, the `modalApplyOneKb5'Prop`/`modalApplyOneKb5'` rule family
   and its `RuleApplicationSpecCore` split lemmas, the driver instantiation, and the dead
   termination aliases `Kb5'WorldInv`/etc). All three deletion ranges were confirmed via grep to
   contain only prime-family declarations before removal.
4. **S5Simplification.lean docstring cleanup and final verification**: fixed the last
   docstring-only prime references and ran the full acceptance checklist.

## Guardrails Honored

- `Univ` family and public API (`instDecidableKb5Valid`, `kb5Valid_decides`,
  `modalTableauKb5''_complete`/`_sound`) left completely unchanged.
- Option A1 adopted: `modalTableauKb5'_sound` dropped outright, not aliased.
- `modalApplyOneKb5` (the unprimed Five-alias) untouched, not renamed.
- Zero `sorry`/`admit`/new `axiom`/`native_decide`/`@[nolint]` introduced in any of the four
  in-scope files.
- `kb5Valid_decides` axioms confirmed unchanged at every phase boundary:
  `[propext, Classical.choice, Quot.sound]`.
- Green `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` gate after every phase.

## Plan Deviations

- **Phase 2**: the counterexample's mathematical content was relocated into
  `modalTruthLemmaKb5`'s own declaration docstring rather than a floating module-level `/-! -/`
  comment -- more literally satisfying "a Univ-family module docstring" since it is attached to
  an actual Univ declaration.
- **Phase 3**: the plan's line-numbered inventory for Task 3 (modalKb5BoxAllFull/DiaNegAllFull,
  the `modalApplyOneKb5'Prop` family, the `modalApplyOneKb5'` rule/split lemmas, and the driver
  decls) turned out to be one uninterrupted contiguous block (lines 1503-2156 pre-edit) with no
  Univ/keeper declaration interleaved, so it was deleted as a single range rather than several
  separate deletions.
- **Phases 3-4**: several additional stray docstring references to retired symbols were
  discovered via repo-wide grep sweeps beyond the plan's Section 3a inventory (a handful of
  "Mirrors `modalKb5BoxAllFull`"-style comments in already-committed FrameSoundness.lean/
  FrameCompleteness.lean) and fixed proactively rather than deferred.
- **Phase 4 verification**: `lake shake` (whole-repo import minimization) could not be run to
  full convergence -- the shared working tree has a concurrent sibling task actively mid-edit on
  `LoopChecking.lean` (outside this task's file scope), and `lake shake` requires every module's
  oleans to be simultaneously fresh across the whole 3240-module project graph. Every attempt
  raced against the sibling's live edits and failed with "out of date oleans" attributable
  specifically to `LoopChecking.lean`, never to any of this task's four files. `lake test`
  succeeded in full (9232/9232 jobs) at one point during this session, confirming the repo was
  fully green -- including this task's changes -- at that snapshot. This is documented as a
  partial verification item rather than worked around by touching the unrelated file.

## Final Verification Results

- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`: green, 880 jobs, sorry-free.
- `lake build Cslib.Logics.Modal.Tableau.S5Simplification`: green, 849 jobs.
- `lake exe checkInitImports`: pass.
- `lake lint`: pass (zero environment-linter warnings for `Cslib`).
- `lake exe lint-style`: pass (zero output).
- `lake exe mk_all --module`: "No update necessary".
- `lake test`: pass, 9232/9232 jobs including `CslibTests`.
- `lean_verify` on `Cslib.Logic.Modal.Tableau.kb5Valid_decides`: axioms
  `[propext, Classical.choice, Quot.sound]`, unchanged from baseline.
- Repo-wide grep: zero remaining references to any retired prime symbol name anywhere in
  `Cslib/`, including docstrings.
- Zero `sorry`/`admit`/new `axiom`/`native_decide`/`@[nolint]` in the four modified files.

## Modified Files

- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

## Commits

- `0ea7c014` task 531 phase 1: retire FrameSoundness prime chain
- `6900e613` task 531 phase 2: retire FrameCompleteness prime cluster and counterexample
- `0b4850a7` task 531 phase 3: retire FiveSimplification Full base definitions
- `67ce59a2` task 531 phase 4: S5Simplification docstring cleanup and final verification
