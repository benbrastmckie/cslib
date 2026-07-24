# Implementation Summary: Strip Task/Phase Provenance and Stale Claims from Logic-Tree Docstrings

- **Task**: 542 - strip_task_provenance_stale_claims_docstrings
- **Status**: [PARTIAL] — Phases 1-2 complete, Phases 3-8 not started
- **Plan**: plans/01_strip-provenance-docstrings.md
- **Handoff**: handoffs/02_phase2-complete-handoff.md

## What Was Done

### Phase 1: Four Specific Items — COMPLETE
1. **Bimodal Chronicle stale-sorry claims** (`ChronicleToCountermodelBasic.lean`): the file has
   zero live `sorry` tokens, but its docstrings claimed the `IsSuccArchimedean` discrete case
   "has one remaining sorry" and the non-dense branch was handled "(with sorry, like the
   discrete case)". Both rewritten to describe the completed, sorry-free construction. Also
   dropped an incidental "in Phase 4" phrase and deleted the `Task 117 plan: specs/117_.../...`
   provenance line from `## References`, keeping the Burgess 1982 literature citation.
2. **Temporal `Completeness.lean` FMP-blocked carcass** (item c): the
   `/-! ### Remaining FMP-Blocked Obligations ... -/` block (~90 lines of commented-out
   lemma/instance sketches citing `task 439`/`task 426 Phase 3`) replaced with the one-line
   mathematical pointer specified by the plan (PTL Finite Model Property, no task numbers).
   Also stripped task/phase provenance from the module's "Main Results"/"Blocked
   Obligations"/"Time-Ordering Invariant" sections, since this file is solely owned by Phase 1
   and no other phase touches it.
3. **`Bool.lean` Doty forward-reference** (item d): dropped the "(Matthew Doty's forthcoming
   work — not yet in-tree)" parenthetical, keeping the durable DPLL/Tseitin/CNF design contract
   verbatim.
4. **`Algebra/Bridge.lean`** (item b): confirming read only. Grep found zero residual
   task/phase/specs provenance — task 543's earlier rewrite is already truthful. No change.

All four modules build clean (`lake build`); zero live `sorry` tokens confirmed by grep +
manual inspection of every hit.

### Phase 2: Modal/Tableau — Completeness/Loop Cluster — COMPLETE
Completed `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (4,172 lines, 103 provenance
hits — the single heaviest file in the entire task scope). This file used "Phase N" pervasively
as an internal, de facto section-numbering device (not just external task citations), so the
fix required per-reference judgment: numeric cross-references were rewritten to positional
anchors ("above"/"below") or direct lemma-name references. The embedded
`specs/515_.../probes/five-s5-separation.lean` docstring link was replaced with a pointer to the
equivalent in-tree lemmas in `FrameSoundness.lean` (verified to actually exist there via grep
before rewriting). The KB5 section's "retired frozen root-gated rule" counterexample
documentation was preserved verbatim — it is genuine, explicitly-flagged design documentation,
not development-history clutter.

Also completed this session:
- `CompletenessLoop.lean` (2,302 lines, 69 hits): recurring "task 515 Phase N" cross-references
  dropped or rewritten to "above"/"below"; two ephemeral audit-report-filename citations
  (`06_k-aux-unprovability-audit.md`) rewritten to describe the audit's finding directly; bare
  task-number citations without the word "task" ("503 (T), 505 (B), 506 (S4)") reworded to name
  the systems directly.
- `LoopChecking.lean` (4,658 lines, 72 hits — the heaviest remaining file in the task):
  pervasive "task 511 Phase N" citations stripped; two "dispatch"-narrative blocks (describing
  progress "across dispatches 2-5"/"an earlier dispatch's continuation note") rewritten as
  current-state descriptions rather than development history; one literal `` `[COMPLETED]` ``
  phase-status marker embedded in a proof comment, and one "a literal reading of the plan"
  reference, both removed.
- `Completeness.lean` (Modal, 1,031 lines, 32 hits, distinct from the Temporal file done in
  Phase 1): task/phase provenance stripped, including a bare "for 505/506" reworded to "for the
  B and S4 systems".
- `LoopInduction.lean` (2 hits): dropped a `(task 404)` citation from an otherwise-legitimate
  design note about superseded helper lemmas.

All five files build clean (`lake build`, scoped per module); zero live `sorry` (one correct
"zero sorry" prose mention retained in `LoopChecking.lean`). The small driver/infrastructure
files `TDriver.lean`/`BDriver.lean`/`Defs.lean`/`Rules.lean`/`SoundnessStep.lean`/
`Soundness.lean`/`Saturation.lean` were deliberately left unclaimed for Phase 3 per the
continuation handoff's own file-ownership recommendation.

## What Remains

Phases 3, 4, 5, 6, 7, 8 are outstanding. This covers the bulk of the ~1,299-line,
~163-file provenance sweep: the rest of Modal/Tableau (soundness/measure/simplification
cluster), all of Modal/Metalogic/Constructive, the Modal/Metalogic remainder + ProofSystem,
Propositional/Temporal remainder, Bimodal + Foundations/Logic + the concentrated §4.3 judgment
review, and the final whole-tree CI gate (Phase 8). See
`handoffs/02_phase2-complete-handoff.md` for full continuation context, including methodology
notes for the pervasive internal "Phase N" cross-reference pattern, bare task-number citations
without the word "task", and "dispatch"-history narrative — all three patterns are expected to
recur in the remaining Modal/Tableau and Modal/Metalogic/Constructive files.

## Plan Deviations

- **Phase 1 scope widened slightly**: within the Temporal `Completeness.lean` file (solely owned
  by Phase 1), stripped task/phase provenance from the module docstring's "Main
  Results"/"Blocked Obligations"/"Time-Ordering Invariant" sections in addition to the
  plan-specified carcass-block replacement, since this file has no other owning phase and
  leaving residual provenance there would have gone unaddressed by any later phase.
- **No other deviations.** All Phase 1 and Phase 2 checklist items were completed exactly as
  specified. Phase 2's plan heading is now marked `[COMPLETED]`, with every checklist item
  annotated with what was done and which commit landed it.

## Verification

- `lake build` (scoped): green for all nine touched `.lean` files across Phases 1-2
  (`ChronicleToCountermodelBasic.lean`, Temporal `Completeness.lean`, `Bool.lean`,
  `FrameCompleteness.lean`, `CompletenessLoop.lean`, `LoopChecking.lean`, Modal
  `Completeness.lean`, `LoopInduction.lean`).
- `lake build` (full project): not run this session; deferred to Phase 8 per the plan's own
  dependency table (Phase 8 depends on all of Phases 1-7).
- Zero live `sorry` in all touched files.
- Zero new axioms (comment/docstring-only edits; no axiom/definition/theorem statements changed).
- Zero remaining `task N`/`Phase N`/`specs/NNN` provenance in the touched files (grep confirmed
  after each edit), plus the two newly-identified patterns (bare task-number citations without
  the word "task"; "dispatch"-history narrative) also swept.
- `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake shake`, `lake test`: not
  yet run (Phase 8 gate, deferred until all content phases complete).

## Artifacts

- Plan: `specs/542_strip_task_provenance_stale_claims_docstrings/plans/01_strip-provenance-docstrings.md`
  (phase status markers and per-task checklist annotations updated; Phases 1-2 now `[COMPLETED]`)
- Handoff: `specs/542_strip_task_provenance_stale_claims_docstrings/handoffs/01_phase2-partial-handoff.md`
  (Phase 2 partial, superseded)
- Handoff: `specs/542_strip_task_provenance_stale_claims_docstrings/handoffs/02_phase2-complete-handoff.md`
  (Phase 2 complete, current)
- This summary
