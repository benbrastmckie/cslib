# Handoff: Task 542 — Strip Provenance Sweep (Phase 2 Partial)

**Date**: 2026-07-24
**Session**: sess_1784866674_c9da04_542
**Status at handoff**: Phase 1 complete; Phase 2 in progress (1 of ~5-6 files done)

## What Was Completed

### Phase 1: Four Specific Items — COMPLETE (commit 040d47e3)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`:
  rewrote the stale "one remaining sorry" / "with sorry, like the discrete case" claims to
  describe the completed, sorry-free construction (verified zero live `sorry` tokens); dropped
  an incidental "in Phase 4" phrase; deleted the `Task 117 plan: specs/117_.../...` reference
  line from `## References`, keeping the Burgess 1982 citation.
- `Cslib/Logics/Temporal/Tableau/Completeness.lean`: replaced the entire
  `/-! ### Remaining FMP-Blocked Obligations ... -/` carcass block (four commented-out
  lemma/instance sketches plus `task 439`/`task 426 Phase 3` citations) with a one-line PTL-FMP
  mathematical pointer (no task numbers). Also stripped task/phase provenance from the module
  docstring's "Main Results"/"Blocked Obligations"/"Remaining Work" sections and the
  "Time-Ordering Invariant: InstantStrict" section, since this file is solely owned by Phase 1.
- `Cslib/Logics/Propositional/Semantics/Bool.lean`: dropped the "(Matthew Doty's forthcoming
  work — not yet in-tree)" parenthetical, keeping the durable DPLL/Tseitin/CNF design contract.
- `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean`: confirming read only — zero
  residual provenance found, no change needed (task 543's prior rewrite is already truthful).
- All four modules: `lake build` green, zero live `sorry`.

### Phase 2: Modal/Tableau — Completeness/Loop Cluster — IN PROGRESS (commit 3a0d6552)
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (4,172 lines, the single heaviest file in
  the whole task, 103 provenance hits) — DONE. Stripped task/phase provenance from every
  section (K/T/B/S5/Five/KB5 completeness). This file's prose used "Phase N" pervasively as an
  internal, de facto section-numbering scheme (not just external task citations) — cross-references
  were rewritten to positional anchors ("above"/"below") or direct lemma-name references instead
  of numeric phase tags. The embedded `specs/515_.../probes/five-s5-separation.lean` link (the
  frame-class-inclusion separation argument) was replaced with a pointer to the equivalent
  in-tree lemmas in `FrameSoundness.lean` (`fiveValid_ssubset_s5Valid` etc., verified to actually
  exist there). The "retired frozen root-gated rule" counterexample documentation in the KB5
  section was preserved verbatim (explicitly valuable design documentation, not provenance).
  `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green; zero live `sorry` (one
  "sorry-free" prose mention retained, correctly).

## What Remains (Continuation Context)

**Phases remaining**: 2 (rest), 3, 4, 5, 6, 7, 8 — i.e. essentially the entire Modal tree
(the dominant ~971-hit / 86-file tree) plus Propositional/Temporal remainder, Bimodal,
Foundations/Logic, and the final CI gate.

### Phase 2 remainder (same phase, continue in place)
Still owned by Phase 2, not yet touched:
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (~69-73 provenance hits, 2,302 lines)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (~72 hits)
- `Cslib/Logics/Modal/Tableau/Completeness.lean` (Modal, distinct from the Temporal file already
  done in Phase 1; ~32 hits)
- Small remaining Tableau files not yet assigned between Phase 2/Phase 3 (see
  `Cslib/Logics/Modal/Tableau/*.lean` — `TDriver.lean`, `Defs.lean`, `Rules.lean`,
  `SoundnessStep.lean`, `Soundness.lean`, `Saturation.lean`, `BDriver.lean`, `LoopInduction.lean`,
  `FrameRules.lean`, `Closure.lean`, `Branch.lean` — some have 0 hits, `TDriver.lean` has ~15,
  the rest are light or zero; recommend grouping completeness/loop-themed files (`LoopInduction`)
  with Phase 2 and driver/infrastructure files with Phase 3 per the plan's own suggested split).

### Phase 3-8 (untouched)
- Phase 3: Modal/Tableau soundness/measure/simplification cluster (`FrameSoundness.lean` 56,
  `FmpMeasure.lean` 52, `S5Simplification.lean` 41, `FiveSimplification.lean` 39,
  `GenericDriver.lean` 36, plus remainder). Note: `FrameSoundness.lean` also has at least two
  "Mirrors the separation probe's ..." phrases at lines ~4914/4920 (post-Phase-1-edit line
  numbers may have shifted) referencing the same probe file already cleaned up in
  `FrameCompleteness.lean` — apply the same "point at `FrameSoundness.lean`'s own lemmas instead
  of the probe" treatment there, or simply drop "the separation probe's" since the lemma names
  are already fully qualified.
- Phase 4: Modal/Metalogic/Constructive (253 hits/15 files, `specs/NNN` links in CS4/CS5/
  CS5Canonical/CKExtension/Labelled/{Completeness,Soundness,PrimeLemma}, plus `renamed from`/
  `formerly` narrative documenting task 544's already-landed renames).
- Phase 5: Modal/Metalogic remainder (Intuitionistic/InterSystem/Systems/Minimal) + ProofSystem
  (~179 hits).
- Phase 6: Propositional + Temporal remainder, excluding the three Phase-1-owned files
  (~156 hits).
- Phase 7: Bimodal + Foundations/Logic + the concentrated §4.3 judgment-required review (~120
  hits plus ~93 `no longer`/`used to`/`previously`/`bypassed`/`refactor`/`migration` lines
  requiring per-line contextual reading across all five trees).
- Phase 8: Full CI gate (`lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake`, repo-wide grep sanity for zero remaining provenance and
  zero live sorry). Not yet run at the whole-tree level (only scoped per-module builds have been
  run so far, all green).

## Methodology Notes for Continuation

1. **The internal "Phase N" cross-reference problem is pervasive across the Modal/Tableau tree.**
   `FrameCompleteness.lean` alone had ~50+ bare `(Phase N)` cross-references used as an informal
   section-numbering scheme (not always external task citations — often referring to another
   section *within the same file*, or to a section in a sibling file). Expect the same density
   in `CompletenessLoop.lean`/`LoopChecking.lean`/the Constructive subtree. The working
   transform: replace `(Phase N)` with `(above)`/`(below)` when positional, or drop it entirely
   when the lemma name already given makes the tag redundant, or substitute the actual heading
   text as a durable anchor when the cross-reference points at another file's section.
2. **Do not conflate internal Phase-N section numbering with task-number provenance** — both must
   go, but the fix differs: task numbers (`task NNN`) are simply deleted; internal Phase-N labels
   need a positional or named replacement to preserve navigability.
3. **Preserve explicitly-flagged design documentation** even when phrased historically (e.g. the
   KB5 section's "retired frozen root-gated rule ... preserved here as documentation" — this is
   genuine mathematical content the file's own author chose to keep, not development-history
   clutter to strip).
4. **Verify referenced probe/spec files before restating their claims** — `grep` for the lemma
   names a `specs/NNN` link cites; if they exist in-tree (as they did for the five-s5-separation
   probe → `FrameSoundness.lean`), point at the in-tree file instead of inventing vague prose.
5. Continue the per-file rhythm: grep the file's provenance hits, read the surrounding context,
   edit in-place, `grep` again to confirm zero remain, `lake build Module.Name`, `grep -c sorry`
   sanity check, commit as a `task 542 phase {P}.{O}: {file}` sub-step.

## Files Touched So Far (this session)

- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`
- `Cslib/Logics/Temporal/Tableau/Completeness.lean`
- `Cslib/Logics/Propositional/Semantics/Bool.lean`
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `specs/542_strip_task_provenance_stale_claims_docstrings/plans/01_strip-provenance-docstrings.md`
  (phase status markers + task checklist annotations)

## Verification State

- `lake build` (scoped, per touched module): green for all five touched `.lean` files.
- `lake build` (full project): NOT yet run this session — recommend running at the next
  natural per-phase checkpoint, and mandatorily before returning `implemented` status (Phase 8).
- Zero live `sorry` in all touched files (confirmed via `grep -c '\bsorry\b'`, manually checked
  each hit is prose).
- Zero new axioms (no axiom declarations touched or added — comment/docstring-only edits).
- `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake shake`, `lake test`: NOT
  yet run this session (Phase 8 gate, deferred until all content phases are done).

## Recommended Next Steps

1. Resume Phase 2 with `CompletenessLoop.lean`, then `LoopChecking.lean`, then Modal
   `Completeness.lean`, then the small remaining Tableau files.
2. Mark Phase 2 `[COMPLETED]` in the plan once all its files are clean, then proceed through
   Phases 3-7 in any order (they are disjoint-ownership per the plan's dependency table).
3. Run the full Phase 8 CI gate only after Phases 1-7 are all complete.
4. Given the scale (~1,299 total provenance lines across ~163 files; this session covered
   Phase 1 fully plus ~103 of Phase 2's ~280 hits), expect this task to require several more
   `/implement 542` dispatches to reach full completion.
