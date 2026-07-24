# Handoff: Task 542 — Strip Provenance Sweep (Phase 3 Complete)

**Date**: 2026-07-24
**Session**: sess_1784866674_c9da04_542
**Status at handoff**: Phases 1-3 complete. Phases 4-8 remain.

## What Was Completed This Session

### FrameSoundness.lean reconciliation (interrupted-session cleanup)
The previous dispatch was terminated mid-edit by an API session limit, leaving uncommitted
partial edits in `FrameSoundness.lean` and the plan file. Reviewed the uncommitted diff (it was
internally consistent and correctly stripped through most of the file), found and fixed the four
remaining hits the interruption had missed (`task 524`, `task 515 Phase 22` x2, and an embedded
`specs/515_.../probes/` path), verified `lake build` green and zero live `sorry`, then committed.
Commit `7fa923cd`.

### Phase 3 — Modal/Tableau Soundness/Measure/Simplification Cluster — COMPLETE
All files in Phase 3's scope, plus the "remaining lighter Modal/Tableau files" Phase 2's handoff
deferred here:

- `FrameSoundness.lean` (finish) — commit `7fa923cd`
- `FmpMeasure.lean` (52 hits) — task 441/503/507 citations, "see the plan's Architectural Note",
  "research §2.2/§3.4" report citations, one dispatch-history sentence about a "since-corrected
  docstring". Commit `4378ecc7`.
- `S5Simplification.lean` (41 hits) — pervasive "Termination Machinery Plan v5, Phase N"
  citations throughout section headers and cross-references, replaced with durable section-name
  anchors ("the tag invariant", "the linear-budget argument", "the counting crux below"); an
  embedded `specs/515_.../archive/` link; a stale `**[BLOCKED]** (Phase 2)` status marker and
  "COMPILED IN RESEARCH" annotation on what are actually completed, sorry-free obstruction
  proofs (the `rankStep` non-dischargeability counterexample and the R7 fuel-domination
  refutation — both proofs stay verbatim, only the stale status framing was reworded). Commit
  `03057474`.
- `FiveSimplification.lean` (39 hits) — task 515/528 citations, Phase
  19/19a/19b/20/21/21b/22/23, bare "task 2"/"Task 3" labels, and
  `reports/07_.../08_mint-arm-reuse-route-decision.md` citations (more of these than the
  original grep caught — a supplementary `grep -n "reports/"` found four additional hits at
  lines 451/455/458/478 in the file's own witness-search docstrings). Commit `27316733`.
- `GenericDriver.lean` (36 hits) — task 503/504/505/506/507/510/515 citations throughout the
  module docstring and `RuleApplicationSpec`/`RuleApplicationSpecCore` field docstrings; also
  fixed a mislabeled "documented in the plan's Architectural Note" citation (five occurrences)
  to correctly point at this file's own module-docstring "Architectural note" subsection
  instead — the phrase "the plan's" was itself provenance contamination bleeding into what
  should describe the file's own content. Commit `70121234`.
- `Defs.lean`, `Rules.lean` — task 441/510 citations about the native `and`/`or`/`diamond`
  constructor migration; "pre-441 encoded" reworded to "historical Lukasiewicz-encoded" where
  the contrast with the old encoding is still load-bearing math (a lemma that's false under the
  old encoding). Commit `d842d08b`.
- `SoundnessStep.lean`, `Soundness.lean`, `Saturation.lean`, `TDriver.lean`, `BDriver.lean` —
  task 441/503/505/510/513 citations, "Convenience bridge for 503" trailers, and (in
  `BDriver.lean`) a stale claim: a module note said a `grep` for `openBranch_accTargetsKnown`
  "returned zero hits... before this phase" and that `FrameCompleteness.lean`'s "scope note...
  says it is not yet built" — both false today (`FrameCompleteness.lean` now uses
  `modalExpandBranchesGen_openBranch_accTargetsKnown` in multiple places); reworded to state the
  current true fact instead of the historical gap. `FrameRules.lean`/`Closure.lean`/`Branch.lean`
  confirmed zero provenance hits, no action needed. Commit `2a135eae`.

**Phase 3 is now marked `[COMPLETED]`** in the plan file, with per-task checklist annotations.

## Methodology Notes Reconfirmed / Added This Session

1. Section headers of the form `## Title (Some Named Plan v5, Phase N)` or
   `## Title (task NNN Phase M)` should drop the entire parenthetical, keeping just `## Title`.
   When OTHER text in the same file cross-references that phase number (e.g. "needed by Phase
   4's accFresh preservation lemmas"), replace the bare phase number with a durable anchor
   describing the section by name (e.g. "the linear-budget argument's accFresh preservation
   lemmas") — do NOT leave a dangling numeric reference after the heading that named it is
   stripped.
2. Research-report citations (`research §N.M`, `` `reports/NN_slug.md` ``,
   `` `reports/NN_*` ``) are provenance exactly like task/phase citations and must be dropped
   the same way — grep for `research §` and `reports/` in addition to the standard
   `task N`/`Phase N`/`specs/N` patterns; a plain `task [0-9]` grep will NOT catch these.
3. Literal `**[BLOCKED]**`/`**[COMPLETED]**` style-markers in bold (not just backticks, as the
   Phase 2 handoff noted) also occur — grep for `\[BLOCKED\]`/`\[COMPLETED\]` broadly, not only
   inside backticks. When the surrounding content is a completed, sorry-free proof (as in
   `S5Simplification.lean`'s `rankStep` obstruction section), the status framing is simply wrong
   today and should be reworded to describe the actual (proven) result, not "reworded to remove
   the tag" — read the proof to confirm it is genuinely complete before rewording.
4. "Mirrors the plan's X" / "see the plan's Y" citations sometimes turn out to be **mislabeled**
   — the content actually being referenced is the current file's own module docstring, not an
   external plan document (`GenericDriver.lean`'s five "documented in the plan's Architectural
   Note" instances were all self-references to that same file's "Architectural note"
   subsection). Read the referent before deciding whether to drop the clause or fix the label.
5. Stale "gap" claims (e.g. "X returned zero hits", "not yet built", "still missing") should be
   verified against the current tree with a quick `grep` before editing — if the described gap
   has since been closed (a lemma with that exact name now exists and is used), the claim is
   simply false today and must be corrected to state the current fact, not just have its task
   number stripped.

## Files Touched So Far (cumulative, this task)

Phase 1 (prior sessions):
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`
- `Cslib/Logics/Temporal/Tableau/Completeness.lean`
- `Cslib/Logics/Propositional/Semantics/Bool.lean`

Phase 2 (prior sessions):
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib/Logics/Modal/Tableau/Completeness.lean`
- `Cslib/Logics/Modal/Tableau/LoopInduction.lean`

Phase 3 (this session):
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean`
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean`
- `Cslib/Logics/Modal/Tableau/Defs.lean`
- `Cslib/Logics/Modal/Tableau/Rules.lean`
- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean`
- `Cslib/Logics/Modal/Tableau/Soundness.lean`
- `Cslib/Logics/Modal/Tableau/Saturation.lean`
- `Cslib/Logics/Modal/Tableau/TDriver.lean`
- `Cslib/Logics/Modal/Tableau/BDriver.lean`

Plus (all sessions):
- `specs/542_strip_task_provenance_stale_claims_docstrings/plans/01_strip-provenance-docstrings.md`
  (phase status markers + task checklist annotations)

## Verification State

- `lake build` (scoped, per touched module): green for all touched `.lean` files across all
  three phases.
- `lake build` (full project): NOT yet run this session — Phase 8 gate.
- Zero live `sorry` in all touched files (confirmed via `grep -n '\bsorry\b'`, each hit manually
  checked to be prose).
- Zero new axioms (comment/docstring-only edits, no declarations touched).
- `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake shake`, `lake test`: NOT
  yet run this session (Phase 8 gate, deferred until all content phases are done).

## What Remains

- **Phase 4**: Modal/Metalogic/Constructive (253 hits/15 files), including the `Labelled/`
  subtree. Holds the majority of the remaining 24 `specs/NNN` links. Also: "delete
  `renamed from`/`formerly` narrative documenting task 544's renames" per the plan's own task
  list.
- **Phase 5**: Modal/Metalogic remainder + ProofSystem (~179 hits).
- **Phase 6**: Propositional + Temporal remainder (~156 hits).
- **Phase 7**: Bimodal + Foundations/Logic + the §4.3 judgment review (~120 hits plus ~93
  `no longer`/`used to`/`previously`/`bypassed`/`refactor`/`migration` lines).
- **Phase 8**: Full CI gate. Not yet run at the whole-tree level.

## Recommended Next Steps

1. Start Phase 4 with the biggest Constructive files first (`CS5Canonical.lean` 64 hits,
   `CS5.lean` 47, `Labelled/Soundness.lean` 58, `Labelled/PrimeLemma.lean` 45), deleting the
   embedded `specs/NNN` links as top priority per the plan.
2. Apply the same per-file rhythm established in Phase 3: grep provenance hits + `research §`/
   `reports/`/`dispatch`/`this plan`/`blocker`/`\[BLOCKED\]`/`\[COMPLETED\]` supplementary
   greps, read surrounding context, edit in-place, grep again to confirm zero remain,
   `lake build Module.Name`, `grep -c sorry` sanity check, commit as a
   `task 542 phase {P}.{O}: {file}` sub-step.
3. Mark Phase 4 `[COMPLETED]` once done, then proceed through Phases 5-7 in any order (disjoint
   ownership per the plan's dependency table).
4. Run the full Phase 8 CI gate only after Phases 1-7 are all complete.
5. Given the scale (~1,299 total provenance lines across ~163 files; three sessions have now
   covered Phases 1-3 in full, roughly 610/1299 hits, ~47%), expect several more
   `/implement 542` dispatches to reach full completion.
