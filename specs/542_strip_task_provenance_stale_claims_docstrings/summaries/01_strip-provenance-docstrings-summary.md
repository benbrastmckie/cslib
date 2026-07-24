# Implementation Summary: Strip Task/Phase Provenance and Stale Claims from Logic-Tree Docstrings

- **Task**: 542 - strip_task_provenance_stale_claims_docstrings
- **Status**: [COMPLETED]
- **Plan**: plans/01_strip-provenance-docstrings.md
- **Handoffs**: handoffs/{01_phase2-partial,02_phase2-complete,03_phase3-complete,04_phase4-7-partial}-handoff.md

## What Was Done

All 8 plan phases are complete. The sweep stripped task/phase/plan/`specs/NNN`/rollout/
`renamed from`/`formerly` provenance narrative from shipped docstrings and comments across
`Cslib/Logics/{Modal,Propositional,Temporal,Bimodal}` and `Cslib/Foundations/Logic` (~163 files
in scope), while preserving every mathematical contract and literature reference. All edits are
comment/docstring-only — no proof, definition, or `import` line was changed.

### Phase 1: Four Specific Items
Resolved all four verified stale items: the Bimodal Chronicle file's stale "one remaining sorry"
claims (file is sorry-free), the Temporal `Completeness.lean` FMP-blocked commented-out carcass
(replaced with a one-line PTL Finite Model Property pointer, no task numbers), the `Bool.lean`
Doty forward-reference (dropped, design contract kept), and a confirming read of
`Algebra/Bridge.lean` (already truthful from task 543's earlier rewrite).

### Phase 2-3: Modal/Tableau (Completeness/Loop and Soundness/Measure/Simplification clusters)
Stripped provenance from the heaviest files in the entire scope: `FrameCompleteness.lean`
(4,172 lines, 103 hits), `CompletenessLoop.lean` (69 hits), `LoopChecking.lean` (72 hits),
`FrameSoundness.lean` (56 hits, embedded `specs/NNN` link deleted), `FmpMeasure.lean`,
`S5Simplification.lean`/`FiveSimplification.lean` (embedded `specs/NNN` links deleted), and the
remaining driver/infrastructure files. Internal "Phase N" cross-references (used as a de facto
section-numbering device in several of these files) were rewritten to positional anchors
("above"/"below") or direct lemma-name references.

### Phase 4-5: Modal/Metalogic (Constructive, Intuitionistic, InterSystem, Systems, Minimal,
ProofSystem)
Stripped provenance from all of `Modal/Metalogic/Constructive` (including `Labelled/`, holding
the majority of the 24 embedded `specs/NNN` links) and the remainder of `Modal/Metalogic` plus
`ProofSystem`. Corrected two stale claims found along the way: `IntToClassical.lean` described
already-proved-sorry-free schemata as "deferred to Phase 7"; `SchemaUnion.lean` described
already-landed `abbrev` redefinitions as "future bridge equivalences".

### Phase 6: Propositional + Temporal (remainder)
Stripped provenance from all Propositional and Temporal files except those carrying live
continuation/blocker documentation for still-open tasks (see Deviations below). Corrected two
stale claims: `Embedding.lean` said Modal/Temporal/Bimodal lacked native and/or (Modal has since
gained `HasAnd`/`HasOr`); `LK/Interpolation.lean` said the hard Maehara cases were "deferred to
Phase 3" though all cases are fully proved sorry-free.

### Phase 7: Bimodal + Foundations/Logic + §4.3 Judgment Review
Stripped provenance from Bimodal and `Foundations/Logic` except files owning live blockers for
still-open tasks. Corrected a stale claim in `SinceSeedConsistency.lean`'s "## Status" section
(said only early phases were done in future tense, though the file is already complete and
sorry-free).

Completed the deferred §4.3 judgment-phrase sweep: re-grepped `no longer`/`used to`/`previously`/
`bypassed`/`refactor`/`migration` across all five trees (41 files, 95 hits, excluding the 18
deliberately-skipped live-blocker files). The large majority were purpose clauses ("used to
VERB", e.g. "used to bound the size of...") or genuine mathematical/proof-architecture facts
(e.g. "no longer definitionally", "bypassed S5 rule-discharge obstruction") and were kept
unchanged per the plan's contract-vs-provenance rule. Nine genuine development-history hits were
rewritten to drop historical framing while preserving the surviving technical content — most
notably a stale `K/Completeness.lean` module docstring whose "Main Results" section described
three declarations (`k_derive_box_from_inconsistency`, `k_mcs_box_witness`, bare `k_truth_lemma`)
that no longer exist anywhere in the file (the generic machinery was promoted to
`Metalogic.Completeness`); the docstring was rewritten to describe the file's actual current
declarations.

A follow-up full-tree grep for `task N`/`Task N`/`specs/NNN`/`wip/task-`/`renamed from`/
`formerly` (excluding the skip-list) caught six additional stragglers missed by earlier phases'
per-file sweeps: `Modal/FromPropositional.lean` and `Modal/Tableau/Completeness.lean` (three
`Task 441:` citations), `Modal/Semantics/Birelational.lean` (`tasks 492-494`/`task 495`
citations), and `Modal/Tableau/{GenericDriver,TDriver,LoopInduction}.lean` (`formerly private`/
`formerly inlined`/`formerly declared` phrasing) — all now clean.

### Phase 8: Full CI Verification
Ran the complete CSLib CI pipeline:
- `lake build` (full): 3253/3253 jobs, green.
- `lake test`: exit 0.
- `lake exe checkInitImports`: exit 0, clean.
- `lake exe lint-style`: exit 0, clean.
- `lake lint` (carries `docBlame`): zero warnings of any kind — confirms no declaration was left
  docstring-less by the sweep.
- `lake shake --add-public --keep-implied --keep-prefix`: reported a pre-existing
  import-minimization backlog (~2958 lines, mostly Propositional/Temporal); confirmed via full
  diff against this task's pre-first-commit state that zero import lines were touched by any
  task-542 commit, so this backlog predates and is out of scope for a comment-only sweep (the
  plan's own Non-Goals explicitly exclude import changes).
- `lake exe mk_all --module`: "No update necessary".
- Repo-wide grep sanity for `task N`/`Phase N`/`specs/NNN`/`renamed from`/`formerly`: zero hits
  outside the 18 deliberately-skipped files.
- `sorry`/`axiom`/vacuous-def counts: unchanged from the pre-task baseline (verified via full
  diff — every "sorry"/"axiom" string added across all task-542 commits is prose inside a
  docstring, never a code declaration; the one vacuous-def regex hit is a pre-existing,
  out-of-scope theorem in `Computability/URM/Basic.lean` with proof term `trivial`, not a
  placeholder).

## The 18 Deliberately-Skipped Files (Intentional, Final Exclusions)

These files carry live continuation/blocker documentation for still-open tasks and were
correctly left untouched. Their task/phase provenance is not stale — it is active project state.
They should be revisited once their owning tasks land or are otherwise resolved, at which point
the provenance becomes genuinely stale and safe to strip. This exclusion is final for this task;
it is not deferred work.

- **Propositional/Tableau** (task 317, `implementing`, 4 live open `sorry`s in this cluster):
  `Tableau/Intuitionistic/{Scheme,Expansion,Completeness}.lean`,
  `Tableau/Minimal/Completeness.lean`
- **Temporal** (task 425, `not_started`, cross-referenced by file:line from that task's own
  description): `Tableau/{Soundness,TimeOrdering}.lean`
- **Temporal/Bimodal Chronicle** (task 530, `blocked`, live `specs/530_.../plans/` directory
  whose phase numbering these files' own "## Status (task 530, Phase N)" headers mirror):
  `Temporal/Metalogic/Chronicle/{ChronicleTypes,RRelation}.lean`,
  `Temporal/Metalogic/Chronicle/CounterexampleElimination/Structures.lean`,
  `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`,
  `Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/BurgessHelpers.lean`,
  `Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean`,
  `Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Structures.lean`,
  `Foundations/Logic/Metalogic/Chronicle/{ChronicleInterface,RRelation}.lean`,
  `Foundations/Logic/Metalogic/Chronicle/CounterexampleElimination/Structures.lean`
- **Bimodal** (task 36, `blocked`, 12+ live sorries):
  `Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean`,
  `Metalogic/BXCanonical/Frame.lean`, `Metalogic/BXCanonical/Completeness.lean`
- **Bimodal** (task 37, `blocked`, 9 live sorries):
  `Metalogic/Bundle/{SuccRelation,UntilSinceCoherence}.lean`
- **Bimodal** (task 450, `not_started`, own description states "This task OWNS
  TemporalConservativity.lean"): `Metalogic/ConservativeExtension/TemporalConservativity.lean`
- **Bimodal** (caution-skip, no live sorry but unattributable open-scope note):
  `Syntax/SubformulaClosure/TemporalFormulas.lean`

## Plan Deviations

- **Phase 1**: scope widened slightly to strip provenance from the Temporal `Completeness.lean`
  module docstring's "Main Results"/"Blocked Obligations"/"Time-Ordering Invariant" sections
  beyond the plan-specified carcass-block replacement, since the file has no other owning phase.
- **Phase 6**: skipped 9 files (task 317, task 425 clusters) as live continuation/blocker
  documentation for open tasks — see the 18-file list above.
- **Phase 7**: skipped 13 files (tasks 36, 37, 450, 530) for the same reason, plus one
  caution-skip (`TemporalFormulas.lean`) — see the 18-file list above.
- **Phase 7 §4.3 judgment pass**: initially deferred in a prior dispatch, completed in this
  final dispatch (see Phase 7 notes above).
- **No other deviations.** Every other plan checklist item across all 8 phases was completed
  exactly as specified.

## Verification

- `lake build` (full project): 3253/3253 jobs, green.
- `lake test`: exit 0 (pre-existing task-317 `sorry` warnings only, unrelated to this task).
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake lint` (`docBlame` etc.): zero warnings.
- `lake shake`/`mk_all --module`: pre-existing import backlog confirmed untouched by this task;
  module listing up to date.
- Zero live `sorry` introduced; zero new axioms; zero vacuous definitions introduced.
- Zero remaining `task N`/`Phase N`/`specs/NNN`/`renamed from`/`formerly` provenance in the five
  trees outside the 18 deliberately-skipped files.
- All diffs across all 8 phases are comment/docstring-only.

## Artifacts

- Plan: `specs/542_strip_task_provenance_stale_claims_docstrings/plans/01_strip-provenance-docstrings.md`
  (all 8 phases marked `[COMPLETED]`, plan-level Status `[COMPLETED]`)
- Report: `specs/542_strip_task_provenance_stale_claims_docstrings/reports/01_docstring-provenance-sweep.md`
- Handoffs: `specs/542_strip_task_provenance_stale_claims_docstrings/handoffs/{01_phase2-partial,02_phase2-complete,03_phase3-complete,04_phase4-7-partial}-handoff.md`
- This summary
