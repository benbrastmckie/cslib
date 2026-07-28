# Implementation Summary: Consolidate Bimodal & Temporal Chronicle Trees (Descoped, Phase 5 Close)

- **Task**: 530 - Consolidate chronicle construction (Bimodal/Temporal)
- **Plan**: plans/02_chronicle-consolidation-descoped.md
- **Status**: Phase 5 (the plan's sole remaining actionable phase) COMPLETED and committed.
- **Started**: 2026-07-18
- **Completed**: 2026-07-28 (partial consolidation; see Overview)
- **Artifacts**: `plans/02_chronicle-consolidation-descoped.md`,
  `summaries/02_chronicle-consolidation-descoped-summary.md`,
  `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean`
- **Standards**: CONTRIBUTING.md, NOTATION.md, ORGANISATION.md; `scripts/pre-pr-check.sh`

## Overview

This task consolidated the duplicated Chronicle construction shared by the Bimodal and
Temporal trees. It closes as a **partial consolidation** by design: the generic lifts that
were structurally achievable landed sorry-free, and the remainder was formally descoped
after two independent investigations established that the obstacle is structural rather
than incidental.

The task-level closing gate (`bash scripts/pre-pr-check.sh`) currently FAILS, but the
failure is entirely attributable to pre-existing, unrelated repository state (baseline
`sorry` instances in files outside this task's scope, already present in `HEAD~1` before
this dispatch and owned by other in-flight tasks) — not to anything Phase 5 touched or
introduced. See "Closing Gate Result" below for the full breakdown.

## What Changed

Per the `[USER SCOPING DECISION 2026-07-26 -- path (B), descope]` recorded in the task
description, Phases 3b, 3c, 4a, and 4b were confirmed DESCOPED (not attempted, per the
plan's DO-NOT-IMPLEMENT banners) and Phase 5 cleanup was executed as the only actionable
work:

- **5.1 — Doc-comment accuracy sweep**: confirmed (grep) no stale "INVALID/sorry stub"
  doc-comment residue anywhere in either tree's Chronicle files. No edit needed.
- **5.2 — Consolidation-boundary docstring**: added a "Consolidation Boundary: What Is
  Generic and What Stays Per-Logic" subsection to
  `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean`'s module docstring,
  naming exactly which layers are generic (interface, `Types`, `RRelation` shared core, CEE
  `Structures`) and which stay per-logic (recursive walks, elimination driver,
  `ChronicleConstruction`), with the structural reason: those declarations are indexed by
  each logic's own local `Chronicle Atom` type, and a bridging projection defeats
  `rcases`/`simp` on Finset-membership subterms nested inside chronicle conditions. Prose
  only; the module builds clean.
- **5.3 — Barrel audit**: confirmed `Cslib.lean` imports exactly the five Foundations
  Chronicle modules on disk, and both trees' `CounterexampleElimination.lean` sub-barrels
  list exactly the modules on disk (bimodal 4/4, temporal 4/4) with accurate docstring
  prose. Confirmed `Cslib/Logics/Bimodal/Metalogic.lean` does not exist (per the plan's
  correction to the superseded plan) and was not created. No discrepancy; no edit.
- **5.4 — Containment check**: `grep -rn "ChronicleToCountermodel" Cslib/Foundations/`
  returned nothing. Re-confirmed all four Scope Hypothesis counts unchanged from baseline
  (bimodal `ChronicleToCountermodel.lean`: 23, `...Basic.lean`: 2; temporal Chronicle tree:
  fully sorry-free; Foundations Chronicle tree: exactly one prose `sorry` mention in
  `SinceSeedConsistency.lean`).
- **5.5 — Explicit skip**: confirmed `SinceSeedInterface`/`ChronicleInterface`
  reconciliation was not attempted and `SinceSeedConsistency.lean` is untouched
  (`git status` clean on that file).

Only one Lean source file was modified: `ChronicleInterface.lean` (docstring-only, +48
lines). No proof body anywhere was touched, per the plan's Non-Goals.

## Closing Gate Result (`bash scripts/pre-pr-check.sh`)

Ran the full 9-step pipeline. **Result: FAILED overall** (steps 1 and 5 report FAIL; steps
2, 3, 4, 6, 7, 8, 9 report OK).

**Steps that failed, and why they are out of this task's scope**:
- **Step 1** (sorry scan across `Cslib/Foundations/Logic/`, `Cslib/Logics/Modal/`,
  `Cslib/Logics/Temporal/`, `Cslib/Logics/Bimodal/`) and **Step 5** (`lake build --wfail
  --iofail`) both flag `sorry` in files this task never touches:
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`,
  `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean`,
  `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean`,
  `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean`,
  `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean`,
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`,
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`,
  `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` — plus the expected,
  in-scope, unchanged baseline in `ChronicleToCountermodel.lean` (23) /
  `ChronicleToCountermodelBasic.lean` (2).
- Verified each non-Chronicle file above is fully committed at `HEAD` with `git status
  --short` clean, and that the same `sorry` content already existed at `HEAD~1` (i.e.
  before this dispatch's own commit) — confirming these are pre-existing repository debt
  from other, currently in-flight tasks, not a regression introduced here. This task's hard
  guardrails explicitly forbid touching unrelated proof work or the bimodal
  discrete-completeness sorries, so no attempt was made to fix them.
- **Steps 6-9** (the ratchet checks that specifically measure whether *this* work added
  debt — blanket-suppression count, shake-flagged-file set, sorry/suppression count, and
  axiom census) all report **OK, matching baseline exactly**: `19`/`19` suppressions,
  `9`/`9` shake-flagged files, `18`/`18` markers and `28`/`28` sorries, `43`/`43`
  sorryAx-tainted declarations. Task 530 introduced zero new debt by any of these measures.

**Conclusion**: Phase 5's own scope is clean and green; the plan's literal completion-bar
item "`bash scripts/pre-pr-check.sh` passes end to end" is not met, but only because of
unrelated, pre-existing repository state outside this task's control and explicitly outside
this task's permitted scope to fix.

## Decisions

- **Descope Phases 3b, 3c, 4a, 4b** (recorded user scoping decision, path (B)). Two
  independent investigations established that generically bridging types indexed by each
  tree's *local* `Chronicle Atom` structure defeats `rcases`/`simp` on Finset-membership
  subterms nested inside chronicle conditions. Repairing that would be a proof change,
  exceeding this task's own "structural dedup, not a proof change" mandate. The four phases
  carry `[DESCOPED]` markers with DO-NOT-IMPLEMENT banners and their task checklists were
  deleted, so no future dispatch can read them as pending work.
- **Treat the consolidation boundary as stable, not provisional.** The boundary is now
  documented in `ChronicleInterface.lean`'s module docstring rather than left implicit, so a
  later reader does not mistake the partial lift for an unfinished one.
- **Close as PARTIAL rather than COMPLETED.** Phase 5 and the plan's completion bar are met,
  but the repo-wide closing gate is not green due to external debt, so the honest terminus is
  partial pending that debt clearing.
- **Resolve the Phase 3a deferral permanently.** `burgessR3Maximal_from_h_content_sub` had
  been deferred pending "the Phase 4b duality-theorem decision"; with 4b descoped, it stays
  logic-local permanently.

## Impacts

- **Net structural gain**: the interface, generic `Types`, the ~38-lemma `RRelation` shared
  core, and the CEE `Structures` + Burgess helpers are now shared, all sorry-free.
- **No proof-surface change**: exactly one Lean file was modified in this phase, docstring-only.
  Zero new sorries, axioms, suppressions, or shake debt by every ratchet the CI pipeline
  measures.
- **Duplication remains** in the recursive walks, the elimination driver, and
  `ChronicleConstruction` across both trees — deliberately, and now documented as such.
- **Bimodal discrete-completeness sorries untouched**, as required; they remain blocked on an
  external port and were never entangled with this work.

## Plan Deviations

None beyond what is already recorded inline in the plan file's Phase 5 task checklist
(5.1 and 5.3 both found their respective hypotheses already true and made no edit, which
the plan anticipated as the expected outcome, not a deviation).

## Verification

- `lake build Cslib.Foundations.Logic.Metalogic.Chronicle.ChronicleInterface`: succeeded.
- All four Scope Hypothesis greps re-run and unchanged from baseline (see above).
- `grep -rn "ChronicleToCountermodel" Cslib/Foundations/`: empty (containment holds).
- `Logics/Temporal/Metalogic/DenseCompleteness.lean` (`completeness_dense`): confirmed
  sorry-free.
- `bash scripts/pre-pr-check.sh`: FAILED overall; root cause is pre-existing, out-of-scope
  repository debt (see above); all task-530-relevant ratchets and containment checks passed.
- Zero new sorries, zero new axioms introduced by this dispatch.

## Artifacts

- `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean` (docstring addition)
- `plans/02_chronicle-consolidation-descoped.md` (Phase 5 checklist marked complete, phase
  heading `[COMPLETED]`, dependency table updated)
- `summaries/02_chronicle-consolidation-descoped-summary.md` (this file)

## Follow-ups

This task's own scope (Chronicle consolidation, Phase 5 cleanup) is complete. The
outstanding blocker to a fully green `pre-pr-check.sh` is unrelated pre-existing debt in
`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, `Cslib/Logics/Bimodal/Metalogic/...`
(`ConservativeExtension/TemporalConservativity.lean`, `BXCanonical/Frame.lean`,
`Bundle/UntilSinceCoherence.lean`, `Bundle/SuccRelation.lean`), and
`Cslib/Logics/Propositional/Tableau/...` (`Intuitionistic/Scheme.lean`,
`Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`) — all owned by other,
currently in-flight tasks. Recommend the user re-run `bash scripts/pre-pr-check.sh` once
those tasks land, to confirm a fully green gate before any `/pr` submission touching this
area of the repo.

## References

- Plan: `plans/02_chronicle-consolidation-descoped.md` (current, authoritative)
- Superseded plan: `plans/01_chronicle-consolidation.md` (historical record only)
- Research: `reports/01_chronicle-dedup-research.md`
- Consolidation boundary rationale: the "Consolidation Boundary: What Is Generic and What
  Stays Per-Logic" subsection of
  `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean`'s module docstring
- Closing gate: `scripts/pre-pr-check.sh`
- Repository standards: `CONTRIBUTING.md`, `NOTATION.md`, `ORGANISATION.md`
