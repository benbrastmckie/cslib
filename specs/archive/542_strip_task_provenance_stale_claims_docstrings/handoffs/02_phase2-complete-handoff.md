# Handoff: Task 542 — Strip Provenance Sweep (Phase 2 Complete)

**Date**: 2026-07-24
**Session**: sess_1784866674_c9da04_542
**Status at handoff**: Phase 1 complete; Phase 2 complete. Phases 3-8 remain.

## What Was Completed This Session

### Phase 2 remainder — COMPLETE
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (2,302 lines, 69 hits) — task/phase
  provenance stripped throughout. The recurring "task 515 Phase N" cross-references were either
  dropped (when the sibling declaration name already made the tag redundant) or rewritten to
  "above"/"below" positional anchors. Two references to an ephemeral audit report filename
  (`06_k-aux-unprovability-audit.md`, from `specs/archive/515_.../reports/`) were rewritten to
  describe the audit's finding directly without citing the file. Bare task-number citations with
  no "task" prefix ("503 (T), 505 (B), 506 (S4)") were reworded to name the systems directly.
  Fixed two lines that exceeded the 100-char style limit as a side effect of merging sentences.
  `lake build` green, zero live `sorry`. Commit `2f93962a`.
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (4,658 lines, 72 hits — the heaviest remaining
  file) — pervasive "task 511 Phase N" section-header and inline citations stripped. Two
  "dispatch"-narrative blocks needed full rewrites rather than tag deletion: the `bClosure`/
  `eClosure` closure-status section (which said "this corrects an earlier dispatch's
  continuation note") and the `modalStepBranchS4_preserves_S4LoopInv` docstring (which said
  "closed across dispatches 2-5... closed dispatch 6... closed this dispatch") — both rewritten
  to describe the current, fully-closed state without dispatch-history narrative. Also found and
  removed one literal `[COMPLETED]` phase-status marker embedded in a proof comment ("the
  already-`[COMPLETED]` Phase 4 struct design") and one "a literal reading of the plan" reference
  (a design-deviation note that didn't need the plan citation to stand on its own). `lake build`
  green, zero live `sorry`. Commit `8d1d66ac`.
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (1,031 lines, Modal — distinct from the Temporal
  file already done in Phase 1, 32 hits) — task/phase provenance stripped, including bare
  "for 505/506" reworded to "for the B and S4 systems". `lake build` green, zero live `sorry`.
  Commit `bb979e4c`.
- `Cslib/Logics/Modal/Tableau/LoopInduction.lean` (2 hits) — small completeness/loop-themed file,
  grouped into Phase 2 per the prior handoff's own recommendation. Dropped a `(task 404)`
  citation from an otherwise-legitimate design note describing superseded helper lemmas. `lake
  build` green.

**Phase 2 is now marked `[COMPLETED]`** in the plan file, with per-task checklist annotations.

## Phase 2 File-Ownership Note for Phase 3

Per the prior handoff's recommendation (driver/infrastructure files grouped with Phase 3), the
following small Modal/Tableau files were deliberately **not** touched this session and remain
available for Phase 3:
- `TDriver.lean` (~15 hits), `BDriver.lean` (3 hits) — driver files
- `Defs.lean` (7 hits), `Rules.lean` (8 hits), `SoundnessStep.lean` (6 hits), `Soundness.lean`
  (4 hits), `Saturation.lean` (4 hits) — infrastructure files
- `FrameRules.lean`, `Closure.lean`, `Branch.lean` — zero provenance hits, no action needed

Phase 3's plan text already lists "the remaining lighter Modal/Tableau files not claimed by
Phase 2" as in scope, so this list is exactly what a Phase 3 dispatch should pick up alongside
`FrameSoundness.lean`/`FmpMeasure.lean`/`S5Simplification.lean`/`FiveSimplification.lean`/
`GenericDriver.lean`.

## What Remains

- **Phase 3**: Modal/Tableau soundness/measure/simplification cluster (`FrameSoundness.lean` 56
  hits, `FmpMeasure.lean` 52, `S5Simplification.lean` 41, `FiveSimplification.lean` 39,
  `GenericDriver.lean` 36, plus the small driver/infrastructure files listed above). Note:
  `FrameSoundness.lean` has "Mirrors the separation probe's ..." phrases referencing the same
  `specs/515_.../probes/five-s5-separation.lean` probe file already cleaned up in
  `FrameCompleteness.lean` (Phase 2 predecessor commit) — apply the same "point at
  `FrameSoundness.lean`'s own lemmas instead of the probe" treatment there.
- **Phase 4**: Modal/Metalogic/Constructive (253 hits/15 files).
- **Phase 5**: Modal/Metalogic remainder + ProofSystem (~179 hits).
- **Phase 6**: Propositional + Temporal remainder (~156 hits).
- **Phase 7**: Bimodal + Foundations/Logic + the §4.3 judgment review (~120 hits plus ~93
  `no longer`/`used to`/`previously`/`bypassed`/`refactor`/`migration` lines).
- **Phase 8**: Full CI gate. Not yet run at the whole-tree level.

## Methodology Notes Reconfirmed This Session

1. **"task NNN Phase M" as internal section-numbering** is pervasive across the entire Modal
   tree, not just `FrameCompleteness.lean`. Expect the same density in Phase 3's remaining
   driver/infrastructure files and the Phase 4 Constructive subtree.
2. **Bare task-number citations without the word "task"** occur (e.g. "503 (T), 505 (B), 506
   (S4)", "needed by 503 for its own T-system truth lemma") — grep for `task [0-9]`/`Phase [0-9]`
   alone will miss these; read every numbered cross-reference in context and check whether it's
   actually a task number for a sibling logic system (T/B/S4/S5/Five), which should be reworded
   to name the system directly.
3. **"dispatch"-history narrative** ("this dispatch's budget", "closed across dispatches 2-5",
   "an earlier dispatch's continuation note") is a distinct but related pattern to "task N" — it
   describes development history across separate implementation sessions without ever using the
   word "task". These need full-paragraph rewrites to describe the current state, not just tag
   deletion. Grep for `dispatch` in addition to the standard patterns when scanning a new file.
4. **Literal phase-status markers embedded in prose** (e.g. `` the already-`[COMPLETED]` Phase 4
   struct design ``) are a rare but real variant — grep for `` `[COMPLETED]` `` / `` `[BLOCKED]` ``
   etc. inside backticks within prose, not just as plan-file phase headings.
5. Continue the per-file rhythm: grep the file's provenance hits (plus `dispatch`/`this plan`/
   `blocker` as supplementary greps), read surrounding context, edit in-place, grep again to
   confirm zero remain, `lake build Module.Name`, `grep -c sorry` sanity check, commit as a
   `task 542 phase {P}.{O}: {file}` sub-step.

## Files Touched So Far (cumulative, this task)

- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` (Phase 1)
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` (Phase 1)
- `Cslib/Logics/Propositional/Semantics/Bool.lean` (Phase 1)
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (Phase 2)
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (Phase 2)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (Phase 2)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (Phase 2)
- `Cslib/Logics/Modal/Tableau/LoopInduction.lean` (Phase 2)
- `specs/542_strip_task_provenance_stale_claims_docstrings/plans/01_strip-provenance-docstrings.md`
  (phase status markers + task checklist annotations)

## Verification State

- `lake build` (scoped, per touched module): green for all touched `.lean` files this session.
- `lake build` (full project): NOT yet run this session — Phase 8 gate.
- Zero live `sorry` in all touched files (confirmed via `grep -n '\bsorry\b'`, each hit manually
  checked to be prose, e.g. "**All ten fields are now fully closed, zero sorry**").
- Zero new axioms (comment/docstring-only edits, no declarations touched).
- `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake shake`, `lake test`: NOT
  yet run this session (Phase 8 gate, deferred until all content phases are done).

## Recommended Next Steps

1. Start Phase 3 with `FrameSoundness.lean` (56 hits, includes the probe-file cross-reference
   that needs the same treatment as `FrameCompleteness.lean`'s prior fix), then `FmpMeasure.lean`,
   `S5Simplification.lean`, `FiveSimplification.lean`, `GenericDriver.lean`, then the small
   driver/infrastructure files listed above under "Phase 2 File-Ownership Note for Phase 3".
2. Mark Phase 3 `[COMPLETED]` once done, then proceed through Phases 4-7 in any order (disjoint
   ownership per the plan's dependency table).
3. Run the full Phase 8 CI gate only after Phases 1-7 are all complete.
4. Given the scale (~1,299 total provenance lines across ~163 files; two sessions have now
   covered Phases 1-2 in full, roughly 280/1299 hits), expect several more `/implement 542`
   dispatches to reach full completion.
