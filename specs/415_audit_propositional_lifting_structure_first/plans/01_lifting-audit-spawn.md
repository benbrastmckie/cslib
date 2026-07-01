# Implementation Plan: Task #415 — Propositional Lifting Audit Finalization + Spawn Manifest

- **Task**: 415 - Audit propositional->modal/temporal/bimodal lifting vs structure-first vision
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: None (research complete; report exists)
- **Research Inputs**: specs/415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md
- **Artifacts**: plans/01_lifting-audit-spawn.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Task 415 is an infrastructure-verification (research/review) task: it produces a report and
SPAWNS concrete follow-on implementation tasks. It does NOT refactor Lean proofs — **no code
changes** are made in this task. The research report (`reports/01_lifting-audit.md`) is complete
and confirms all three seed findings (CPL-only Łukasiewicz embedding; conservativity asymmetry;
GenericLindenbaum debt). This plan therefore has two orientations: (a) final report polish and
re-verification of the file:line evidence underpinning the three seed findings and the sharpened
claims, and (b) authoring the concrete, prioritized set of spawnable follow-on tasks with effort
estimates, dependencies, and cross-references (especially the overlap with task 393). The
definition of done is a verified report plus a ready-to-execute spawn manifest, with every
artifact explicitly classified as internal (AI-authored OK) or upstream-facing (must be
human-authored per the Zulip AI policy).

### Research Integration

The report (`01_lifting-audit.md`) supplies the full evidence base: an architecture map with a
file:line anchor table (§2), per-finding verification (§3-§5), an InterSystem/structural-metatheory
assessment (§6), a met/partial/open matrix vs the Zulip structure-first vision (§7), and a
prioritized list of five spawnable follow-on tasks (§8, Ranks 1-5). This plan consumes those
findings directly: Phase 1 re-verifies the anchor table and the corrections the report itself
flagged (bimodal theorem at `:118` not `:60`; stale `Syntax/` base-layer paths); Phase 3 lifts
§8's Ranks 1-5 into fully-specified spawn task entries.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in delegation context and no ROADMAP.md consulted. The task's `topic`
is "Foundations"; the spawn tasks (parametric conservativity lift, GenericLindenbaum Phase-6,
shared embedding typeclass) advance the Foundations-level fragment-genericity direction. Roadmap
annotation, if any, is deferred to `/todo` at completion.

## Goals & Non-Goals

**Goals**:
- Re-verify the file:line evidence for the three seed findings and the report's flagged
  corrections, so the audit's citations are trustworthy for downstream task authors.
- Finalize the report and classify every artifact/prose block as internal vs upstream-facing,
  honoring the Zulip AI policy (upstream prose must be human-authored).
- Produce a concrete, prioritized spawn manifest: the five follow-on tasks (structure-preserving
  embedding; Foundations-level parametric conservativity lift; GenericLindenbaum Phase-6
  consolidation; cross-logic derivation-lifting spike; documentation-only design note) with
  scope, effort, dependencies, priority, and 393 cross-reference.
- Create (or stage for creation, with user confirmation) the selected follow-on tasks and wire
  their dependencies and the 393 cross-reference.

**Non-Goals**:
- No Lean source modification (no edits to any `Cslib/` file); this task is verification + spawn.
- Not executing any of the follow-on implementation work (embedding refactor, conservativity
  lift, Lindenbaum consolidation) — those are the spawned tasks' scope.
- Not authoring any upstream Zulip post; the report's `[SCAFFOLD]` block remains a draft for a
  human to rewrite.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line numbers drift as `Cslib/` evolves before spawn tasks run | M | M | Phase 1 re-verifies anchors and records symbol names (not just line numbers) so downstream tasks can relocate by grep |
| AI-authored prose leaks into an upstream-facing artifact (Zulip policy violation) | H | L | Phase 2 explicitly tags each block internal/upstream; the `[SCAFFOLD]` remains marked "human rewrite before posting" |
| Spawned GenericLindenbaum task collides with task 393 scope | M | M | Phase 3 records the sibling relationship (deductive-closure vs quotient/algebraic axis) and scopes Phase-6 as the smaller task landing first with an explicit 393 cross-reference |
| Multi-task creation done without user confirmation | M | L | Phase 4 follows the multi-task creation standard: interactive selection + explicit user confirmation before writing state.json |
| Structure-preserving embedding under-scoped (it is XL, multi-logic) | M | L | Phase 3 marks it gated on a future intuitionistic modal logic and splits out the tractable S-M shared-`Embedding`-typeclass refactor as a separate spawn |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Evidence Re-Verification Pass [COMPLETED]

**Goal**: Confirm the file:line anchor table (report §2) and the per-finding citations still
resolve, recording symbol names alongside line numbers so downstream tasks are robust to drift.
Read-only; no source edits.

**Tasks**:
- [x] Re-verify Finding 1 anchors: `Modal/FromPropositional.lean:58-63,106,162`,
      `Temporal/FromPropositional.lean:57-62`, `Temporal/ConservativeExtension.lean:45`,
      `Bimodal/Embedding/PropositionalEmbedding.lean:59-118,116`; confirm the Łukasiewicz
      `and`/`or` arms and the `PL.Evaluate` bridge conclusion. *(deviation: drift found —
      `modal_satisfies_toModal_iff_evaluate` now `:85`, `tautology_iff_toModal_valid` now `:141`,
      `embedding_commutes` now `:105`; caused by task 418's shared `PropositionalEmbedding`
      typeclass, which also relocated the Łukasiewicz and/or definitions out of the per-logic
      files into `Cslib/Logics/Propositional/Embedding.lean`. See report §9.)*
- [x] Re-verify Finding 2 anchors: `Modal/Metalogic/ConservativeExtension.lean:54`, the 15
      per-system `Systems/{...}/ConservativeExtension.lean` files, `Temporal/ConservativeExtension.lean:87`,
      `Bimodal/.../PropositionalConservativity.lean:118` (theorem) vs `:60` (bridge lemma).
      *(deviation: drift found — `temporal_conservative_extension` now `:61`,
      `bimodal_conservative_extension` now `:97`; caused by task 417's `ConservativityLift.lean`
      thinning both files into instances. `ConservativeExtension.lean:54` and the 15/16-file
      counts confirmed exact. See report §9.)*
- [x] Re-verify Finding 3 anchors and line counts: `GenericLindenbaum.lean:47-49` deferral note,
      `wc -l` on the 9 files in the §5 table (MinLindenbaum 247, IntLindenbaum 318, etc.).
      *(deviation: major correction, not mere drift — the deferral-note text is gone (task 416
      rewrote it); line counts for the 9 files confirmed exactly unchanged; and task 416's own
      investigation established the Finding-3 debt was already closed by task 407 phase 6
      (pre-dating this audit) — the "additive/deferred" claim was stale documentation, not an
      open duplication. See report §10.)*
- [x] Re-verify base-layer/InterSystem anchors: `Defs.lean:85`, `NaturalDeduction/Basic.lean:182`,
      `SequentCalculus/LJ/Basic.lean:100`, `InterSystem/Lifting.lean:47,66`,
      `Bimodal/.../Lifting.lean:636,691`; confirm the stale `Syntax/` path note.
      *(all confirmed exact, no drift.)*
- [x] Record any drifted line numbers as an errata note appended to the report (symbol name +
      corrected line); if all anchors hold, note "anchors verified, no drift". *(done: report §9
      "Errata / Re-Verification"; also added §10 "Post-Audit Update" documenting that all five
      §8 spawn candidates already exist as completed child tasks 416-420 — an unplanned but
      load-bearing discovery that reshapes Phase 3/4 below.)*

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `specs/415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md` — append an
  "Errata / Re-verification" note only (no restructuring); no `Cslib/` files touched.

**Verification**:
- Every anchor in the §2 table either resolves at the cited line or has a recorded correction.
- Line counts in §5 reproduced via `wc -l`.
- No `Cslib/` source file modified (`git status` shows only the report changed).

---

### Phase 2: Report Finalization & Artifact Classification [COMPLETED]

**Goal**: Finalize the report and classify every artifact and prose block as internal
(AI-authored acceptable) or upstream-facing (must be human-authored per Zulip AI policy).

**Tasks**:
- [x] Confirm the `[SCAFFOLD — human rewrite before posting]` blocks (report §1 note and §8
      upstream draft) are unambiguously marked and not presented as post-ready. *(confirmed:
      both markers intact and unmodified.)*
- [x] Add an explicit "Artifact Classification" subsection (or table) to the report:
      internal = report body, spawn manifest, this plan; upstream-facing = any Zulip summary
      prose (flagged, human-authored only). *(done: report §11.)*
- [x] Verify the met/partial/open matrix (§7) and the "where CSLib can SURPASS" statement are
      internally consistent with the re-verified anchors from Phase 1. *(done in §11: two rows
      upgraded in light of task 417/416 completions — conservativity-uniformity PARTIAL->MET,
      GenericLindenbaum "MET (defined)" clarified as "defined AND instantiated". OPEN rows
      (native and/or, structure-preserving embedding) confirmed still open.)*
- [x] Ensure the report's verdict and effort estimates (S/M/L/XL) are consistent with the spawn
      manifest that Phase 3 will produce. *(done in §11: all five landed at/near their estimated
      efforts.)*

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `specs/415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md` — add the
  artifact-classification subsection; light consistency edits only.

**Verification**:
- Report contains an explicit internal-vs-upstream classification.
- Every upstream-facing block carries a "human rewrite before posting" marker.
- No AI-authored prose is presented as upstream-ready.

---

### Phase 3: Spawn Manifest — Follow-On Task Specifications [COMPLETED]

**Goal**: Lift report §8 Ranks 1-5 into fully-specified, ready-to-create task entries with
scope, effort, dependencies, priority, internal/upstream classification, and the 393
cross-reference. Written as a standalone manifest artifact.

**Tasks**:
- [x] Specify **Spawn A (Rank 1)** — Instantiate GenericLindenbaum (Phase-6 debt, closes Finding
      3): scope (re-derive `MinTheory`/`IntDCCS` off `GenericTheory`), effort M, deps none-hard,
      coordinate-only with 393, not Zulip-gated (confirm with 393 owner), CI-green requirement.
      *(deviation: already exists as completed task 416; manifest §1-2 documents actual outcome
      — code debt was pre-closed by task 407 phase 6, task 416 delivered a doc-only fix instead.)*
- [x] Specify **Spawn B (Rank 2)** — Foundations-level parametric conservativity lift (closes
      Finding 2): scope (`Foundations/Logic/Metalogic/ConservativityLift.lean`, `conservative_over_cpl`),
      effort M, deps none-hard, synergistic with Spawn A, direct Zulip-ask hit.
      *(deviation: already exists as completed task 417; manifest §1-2 documents delivery.)*
- [x] Specify **Spawn C (Rank 3)** — Shared `PropositionalEmbedding` typeclass + single
      limitation note (supports Finding 1): scope, effort S-M, deps none, note that it does NOT
      itself enable the intuitionistic lift. *(deviation: already exists as completed task 418;
      manifest §1-2 documents delivery.)*
- [x] Specify **Spawn D (Rank 4)** — Cross-logic derivation-lifting spike (InterSystem): scope
      (hoist `liftDerivation`/`liftDerivationWith` onto `InferenceSystem`), effort L, flagged as
      spike (commit only if constructor variance abstracts cleanly), benefits from Spawn B.
      *(deviation: already exists as completed task 419 (forward direction); backward direction
      spun off to completed study task 448, verdict NO-GO. Manifest §1-2 documents delivery.)*
- [x] Specify **Spawn E (Rank 5)** — Documentation-only structure-preserving-embedding
      requirement note (closes Finding 1 design question): the four prerequisites for a native
      intuitionistic-faithful embedding; effort S; no Lean change; XL native embedding itself
      deferred (gated on a future intuitionistic modal logic). *(deviation: already exists as
      completed task 420; manifest §1-2 documents delivery.)*
- [x] Record the task-393 relationship explicitly: Spawn A (deductive-closure Min/Int axis) is a
      sibling of 393's (a)/(b) (quotient/algebraic + Classical-completeness axis) sharing
      `GenericMCSBridge`; recommend Spawn A lands first; 393's "(c)" folds in Spawn B.
      *(done: manifest §4 — 393 remains not_started, unaffected in scope/deps, informational
      cross-reference only.)*
- [x] Draw the spawn dependency/priority ordering (A and B first, highest debt with ready
      substrates; C light-touch; D spike; E doc). *(moot — all five already landed; manifest §1
      records actual execution order/effort instead of a prospective ordering.)*

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `specs/415_audit_propositional_lifting_structure_first/reports/02_spawn-manifest.md` — NEW;
  the ready-to-create task specifications (internal artifact).

**Verification**:
- All five spawns have scope, effort, dependencies, priority, and internal/upstream tag.
- 393 cross-reference is explicit and non-conflicting (sibling axes, shared `GenericMCSBridge`).
- Effort estimates match the report §8 ranks (M, M, S-M, L, S).

---

### Phase 4: Follow-On Task Creation & Dependency Wiring [COMPLETED]

**Goal**: Create the selected follow-on tasks per the multi-task creation standard (interactive
selection + explicit user confirmation), wiring dependencies and the 393 cross-reference into
their descriptions. This phase is executed via `/task` with confirmation, not by direct
state.json edits without consent.

**Tasks**:
- [x] Present the five spawn candidates for interactive selection (multiSelect); user chooses
      which to create (default recommendation: A and B now; C, E soon; D as spike).
      *(deviation: skipped -- Phase 1's re-verification discovered all five candidates already
      exist as completed child tasks 416-420 (parent_task 415), created by a prior orchestration
      pass before this implementation dispatch began. There is nothing left to select or create;
      presenting the five candidates for selection would offer to re-create already-completed
      work. See report §10 and manifest §0/§1.)*
- [ ] On explicit user confirmation ("Yes, create tasks"), create the selected tasks via the
      standard task-creation path (state.json + `generate-todo.sh`), each `task_type: cslib`,
      `topic: Foundations`, with the report path referenced in the description.
      *(deviation: skipped -- no new tasks to create; all five already exist and are completed.
      Creating duplicates would violate the "no task created without explicit user confirmation"
      verification bar in spirit, since there is nothing genuinely new to confirm. Flagged in the
      orchestrator handoff for explicit user visibility rather than silently closed.)*
- [x] Wire dependencies: Spawn D references Spawn B; all reference the 415 report; Spawn A and
      the 393 cross-reference recorded in Spawn A's description.
      *(confirmed already true of the existing tasks 416-420: each description cites
      `specs/415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md` and the
      relevant report section/rank; task 416's description records the 393 cross-reference; task
      419's description records the 417 soft-dependency. No further wiring needed.)*
- [x] Confirm no upstream Zulip action is taken; any upstream coordination (393 owner, Zulip
      thread) is flagged as a human-authored follow-up, not performed here.
      *(confirmed: no Zulip action taken by this task; report §8's `[SCAFFOLD]` block remains
      unmodified and flagged for human rewrite; task 393 itself remains Zulip-first per
      CONTRIBUTING and is untouched by this task.)*

**Disposition**: Phase 4 is marked `[COMPLETED]` on the basis that its verifiable objective —
"the follow-on tasks from this audit exist, are correctly scoped/wired, and no unconfirmed task
creation occurs" — is satisfied by the pre-existing state of tasks 416-420, not by new action
taken in this dispatch. No `specs/state.json`/`specs/TODO.md` task-creation edits were made by
this task. This is flagged explicitly in the orchestrator handoff (`next_action_hint`) so the
user/orchestrator is aware no confirmation prompt occurred (none was needed).

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `specs/state.json` — new task entries (only on user confirmation).
- `specs/TODO.md` — regenerated via `bash .claude/scripts/generate-todo.sh` (never hand-edited).

**Verification**:
- Selected tasks appear in TODO.md with correct type/topic and report cross-reference.
- Task dependencies and the 393 cross-reference are recorded in descriptions.
- No task created without explicit user confirmation; no `Cslib/` source modified.

---

## Testing & Validation

- [ ] `git status` after Phases 1-3 shows only `specs/415_.../` artifacts changed — zero
      `Cslib/` source edits (the task's hard "no code changes" constraint).
- [ ] Every file:line anchor in report §2 resolves or has a recorded errata correction (Phase 1).
- [ ] Report contains an explicit internal-vs-upstream artifact classification (Phase 2).
- [ ] Spawn manifest lists all five follow-ons with scope/effort/deps/priority (Phase 3).
- [ ] Any created tasks match the manifest and were created only after user confirmation (Phase 4).
- [ ] No upstream Zulip prose is presented as post-ready (AI-policy honored throughout).

## Artifacts & Outputs

- `specs/415_audit_propositional_lifting_structure_first/plans/01_lifting-audit-spawn.md` (this plan)
- `specs/415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md` (finalized: errata note + artifact classification)
- `specs/415_audit_propositional_lifting_structure_first/reports/02_spawn-manifest.md` (NEW — spawn task specifications, internal)
- `specs/state.json` + `specs/TODO.md` (new follow-on task entries, on user confirmation)
- `specs/415_audit_propositional_lifting_structure_first/summaries/01_lifting-audit-spawn-summary.md` (implementation summary)

## Rollback/Contingency

All changes are confined to `specs/` (report edits, a new manifest, and state.json task
entries) — no `Cslib/` source is touched, so there is nothing to revert in the library. If the
spawn manifest or created tasks prove misscoped, revert the report/manifest edits via git and
remove the erroneous task entries from state.json (then regenerate TODO.md). Because Phase 4
requires explicit user confirmation before any task is created, the default failure mode is
"manifest produced, no tasks created" — safe and fully recoverable.
