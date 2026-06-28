# Implementation Plan: Task #364 - Modal Tableau Soundness Drift Repair

- **Task**: 364 - modal_tableau_soundness_drift_repair
- **Status**: [NOT STARTED]
- **Effort**: 7 hours
- **Dependencies**: None
- **Research Inputs**: reports/03_verified-fix-mapping.md (AUTHORITATIVE, build-grounded); reports/01_drift-diagnosis.md and reports/02_refactor-strategy.md (supplementary; key claims refuted by 03)
- **Artifacts**: plans/03_soundness-drift-repair.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Repair the Mathlib/toolchain-drift build failure in `Cslib/Logics/Modal/Tableau/Soundness.lean`
(948 lines, sorry-free, broke under `leanprover/lean4:v4.31.0`). The file has ~68 build errors
that collapse to ~16 distinct clusters (C1-C16 in report 03) spanning THREE lemmas, not one:
`modalStepBranch_preserves_sat` (186-787), `modalExpandBranches_closed_unsat` (798-900), and
`modalTableau_sound` (917-945). This plan executes the report-03 build-log-driven, in-place,
commit-per-cluster repair, explicitly **rejecting** the report-02 10-sub-lemma refactor as
over-engineered. Definition of done: scoped `lake build Cslib.Logics.Modal.Tableau.Soundness`
clean, full `lake build` clean, `lake exe lint-style` clean, zero `sorry`, zero new axioms, and
every public theorem statement byte-for-byte unchanged (verified via `git diff`).

### Research Integration

Report 03 (`reports/03_verified-fix-mapping.md`) is the authoritative source — its mapping is
grounded in the actual scoped `lake build` error log (1607 lines captured) and an adversarial
self-verification pass. This plan encodes its core findings:

- **Keystone first**: line 804 `branches.bind id` -> `branches.flatMap id` (`List.bind` removed
  from core). This poisons the IH `ih`/`hInv` with `accFreshInv sorry acc` and cascades into the
  HAppend/`unsolved goals` errors at 869/870/882/899/900. Fix it before anything else.
- **Mechanical sweep**: `List.mem_cons_self _ _` is now all-implicit (`{a}{l} : a ∈ a :: l`) at
  14 sites (233, 279, 311, 322, 341, 350, 368, 377, 433, 627, 651, 709, 732, 875) — drop the `_ _`.
- **Zip block**: `List.mem_zip` removed (823); reconstruct membership without it; fix the
  over-destructured `obtain` (2 binders, not 3) at 821-828; re-derive 858.
- **`Bool.or_eq_true` is `Eq` not `Iff`** (892) — `.mp` invalid; use `rw`/`simp only` then `rcases`.
- **`Family-3` `hnewBs` failure has TWO sub-modes**: (a) flat-vs-nested conjunction (boxPos,
  the positive cases) -> flat `obtain ⟨rfl, _, rfl⟩`; (b) recognizer-no-longer-reduces (negPos
  276, negNeg 625) -> strengthen simp set so `modalNegOf?/modalImpOf?/modalOrOf?` recognizers reduce.
- **Genuine structural bug at 747**: `Duplicate alternative name imp` — not drift; fix regardless.
- All recommended lemmas (`Satisfies.neg_iff/diamond_iff/box_iff_forall`, `Proposition.neg_def`,
  `Sign.isPos`, `Proposition.beqToEq`) exist and are correctly named; reuse in-file, no new abstractions.

### Prior Plan Reference

A prior plan exists at `plans/01_soundness-drift-repair.md`. Per report 03's decision, its
report-02-derived 10-sub-lemma refactor strategy (Phase 0 introducing 10 intermediate `sorry`s)
is **rejected**: the distinct roots are few and mostly mechanical, and the `lake build` log
already exposes the goal/term shapes needed — dissolving the `lean_goal` overflow catch-22 the
refactor was designed to solve. Lessons retained from the prior plan/handoff: the boxNeg case
(N1, 396-616) is the long pole and carries all fix-families; `Proposition.beqToEq` is the reuse
point for Family-4; `hInv` is used only by boxNeg. This new plan does an in-place repair with
NO intermediate scaffolding `sorry`s.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; roadmap consultation skipped. This task
restores a previously-passing module to green after a toolchain bump — it advances CI health for
the Modal Logic topic area.

## Goals & Non-Goals

**Goals**:
- Restore `Cslib/Logics/Modal/Tableau/Soundness.lean` to a clean scoped + full `lake build`.
- Preserve every theorem statement byte-for-byte (no signature change; `git diff` shows only proof bodies + the C7 `cases`-arm internals).
- Keep the file zero-`sorry` and add zero new axioms at every commit boundary (no intermediate `sorry`).
- Pass `lake exe lint-style` and `lake exe checkInitImports`.
- Land the repair as a sequence of independently committable, strictly-error-reducing chunks.

**Non-Goals**:
- The report-02 10-sub-lemma extraction refactor (explicitly rejected; retained only as a scoped boxNeg-only fallback).
- Any change to public APIs, theorem statements, or definitions outside this file.
- Performance tuning, restructuring, or stylistic rewrites beyond what the drift repair requires.
- Touching the already-clean Phase-1 work (lines 80-156: `Proposition.beqToEq`, `modalClosed_unsat`).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `lean_diagnostic_messages` hangs this repo | H | H (if called) | **NEVER** call it. Use the `lake build` error log as ground truth for all goal/term shapes. |
| `lean_goal` returns huge contexts -> agent overflow (defeated 3 prior agents) | H | M | Use `lean_goal` **sparingly**, only on small skeleton/zip goals. Prefer the build log; use `lean_multi_attempt` at exact `obtain` lines for shape discovery. Read file in <=120-line slices. |
| C11/C14 are not pure cascades and persist after C8 (keystone) | M | M | Chunk A ends with a build; if HAppend errors remain, probe 869/882/899 with `lean_multi_attempt` and adjust the `++`/`.map` chain. |
| C9 zip block needs an unidentified replacement lemma | M | M | Budget the most search time here. Candidates: `List.of_mem_zip` (reverse), `List.mem_iff_getElem`, `List.getElem_zip`, `List.mk_mem_zip_iff`. Worst case, restructure to avoid proving zip-membership (goal only feeds `findSome?_eq_none_iff`). |
| Family-3 recognizer simp (C2/C5) resists reduction | M | M | Recognizers are decidable pattern-matches; add `decide := true` to simp config or unfold `modalNegOf?/modalImpOf?/modalOrOf?` explicitly. Re-read `Tableau/Rules.lean` for defs if needed. |
| boxNeg (Phase 6) mid-proof context overflows | M | M | Invoke the report-02 helper-extraction (`…_boxNeg_boxProps_sat` / `…_boxNeg_diaNegProps_sat`) as a **scoped fallback for boxNeg only**, if and only if needed. |
| A statement gets altered during repair | H | L | After each chunk, `git diff` the public signature lines (186-196, 798-812, 917-919) to confirm no theorem type changed. |
| One giant pass loses progress / overflows | H | M | Strictly one chunk per agent run (~100-300 lines of change). Commit per cluster. Never one giant pass. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |

This plan is fully sequential: each phase reduces the error count and de-poisons cascades that
the next phase relies on. Do NOT parallelize — the keystone (Phase 1) must clear first to surface
the real residual errors, and later phases reuse idioms transcribed in earlier ones. Each phase is
one agent run.

**Global discipline (applies to every phase)**:
- NEVER call `lean_diagnostic_messages` (it HANGS in this repo).
- Use `lean_goal` sparingly; prefer the `lake build` error log for goal/term shapes; use
  `lean_multi_attempt` at exact `obtain` lines for destructuring shape discovery.
- Read the file in <=120-line slices.
- Each phase ends green-or-strictly-fewer-errors and is committed. No intermediate `sorry`.
- Regenerate the error log at phase start with `lake build Cslib.Logics.Modal.Tableau.Soundness 2>&1`.

### Phase 1: Downstream keystone + mechanical sweep [IN PROGRESS]

- **Goal:** Fix the `List.bind` keystone (804) and the pervasive mechanical drift sites so the
  largest downstream cascade collapses and the real residual errors surface.
- **Tasks:**
  - [ ] C8 (KEYSTONE): line 804 `branches.bind id` -> `branches.flatMap id`.
  - [ ] C12: replace all 14 `List.mem_cons_self _ _` -> `List.mem_cons_self` (sites 233, 279, 311, 322, 341, 350, 368, 377, 433, 627, 651, 709, 732, 875).
  - [ ] C13: line 892 `rcases Bool.or_eq_true.mp hedge …` -> `rw [Bool.or_eq_true] at hedge; rcases hedge with h' | h'` (or `simp only [Bool.or_eq_true] at hedge`).
  - [ ] C15: line 925 append `exact absurd hedge (by simp)` (or change to `simp at hedge`) to close from `hedge : false = true`.
  - [ ] Rebuild; expect C11/C14/C16 (HAppend / `hstep2` / `modalExpandBranches_closed_unsat`-unknown) to largely clear once C8 de-poisons `ih`. Note any residual HAppend errors for Phase 2.
- **Timing:** ~1 hour
- **Depends on:** none
- **Verification:**
  - `lake build Cslib.Logics.Modal.Tableau.Soundness 2>&1` shows strictly fewer errors than baseline (~68); C8/C12/C13/C15 sites gone.
  - `git diff` confirms no theorem signature changed.
  - Commit: `task 364 phase 1: repair downstream Mathlib drift (List.bind, mem_cons_self, Bool.or_eq_true)`.

---

### Phase 2: Zero-fuel zip-membership block (C9/C10) [NOT STARTED]

- **Goal:** Repair the messiest block — the `List.mem_zip`-removed zero-fuel case and its cascade at 858.
- **Tasks:**
  - [ ] Fix `obtain` arity at 821-828: `∃ i, branches.get i = b` has 2 components, not 3 — use 2 binders.
  - [ ] Replace the `List.mem_zip` `rw` with a reconstruction of `(b, expandedSets.get …) ∈ branches.zip expandedSets`. Probe with `lean_multi_attempt` over candidates: `List.mem_iff_getElem`, `List.getElem_zip`, `List.mk_mem_zip_iff`, `List.of_mem_zip` (reverse direction only).
  - [ ] Re-derive line 858: `modalClosed_unsat bp hcl acc` has type `¬branchSatisfiable bp acc` — drop the spurious `hsat` arg or thread the correct satisfiability hyp (C10, likely a C9 cascade).
  - [ ] If zip-membership resists, restructure to avoid proving it (the goal only feeds `findSome?_eq_none_iff`).
- **Timing:** ~1.5 hours (budget the most search time here)
- **Depends on:** 1
- **Verification:**
  - Scoped `lake build` shows the 820-828 and 858 cluster cleared (or strictly fewer errors with the zip block resolved).
  - `git diff` confirms no theorem signature changed.
  - Commit: `task 364 phase 2: repair zero-fuel zip-membership block`.

---

### Phase 3: boxPos positive-structure case (C1) [NOT STARTED]

- **Goal:** Repair the boxPos case where `simp` now normalizes `hsf` to a flat right-associated conjunction.
- **Tasks:**
  - [ ] Collapse the `split_ifs`/double-bullet structure at 227-231.
  - [ ] After `simp only [Option.some.injEq, Prod.mk.injEq] at hsf`, use flat `obtain ⟨rfl, _, rfl⟩ := hsf` (build log at 228 already dumps the flat shape `[boxPropagation … ++ b] = newBs ∧ [e] = newExps ∧ acc = newAcc`).
  - [ ] Handle the empty-`boxPropagation` case via `hemp`/`simp` separately.
  - [ ] Verify the `simp only [Satisfies] at hpos` at ~262 fires (Family-2; reorder after `rw` or use `Satisfies.neg_iff/diamond_iff`/`Proposition.neg_def` if it no-ops).
- **Timing:** ~1 hour
- **Depends on:** 2
- **Verification:**
  - Scoped `lake build` shows the boxPos cluster (220-266) cleared.
  - `git diff` confirms no theorem signature changed.
  - Commit: `task 364 phase 3: repair boxPos conjunction-shape drift`.

---

### Phase 4: Positive propositional cases (C2/C3) [NOT STARTED]

- **Goal:** Repair the four positive propositional rule-cases by transcribing one working flat-obtain idiom across all four.
- **Tasks:**
  - [ ] negPos (270-290): C2 sub-mode — strengthen the simp set so `modalNegOf?/modalImpOf?/modalOrOf?` recognizers + `if` reduce to a `RuleResult` (add `decide := true` or explicit recognizer-unfold; diagnose the un-reduced `match`/`if` term from the build dump at 276), then flat `obtain ⟨rfl, _, rfl⟩ := hsf`.
  - [ ] orPos (297-328): flat `obtain ⟨hnewBs, _, hnewAcc⟩` (replace nested `⟨⟨hnewBs,_⟩,hnewAcc⟩`); fix upstream `simp` shape if a `match` persists.
  - [ ] impPos (329-356): same flat-obtain idiom.
  - [ ] impPosGen (357-383): same flat-obtain idiom.
  - [ ] These are near-identical; once one builds, transcribe across the others.
- **Timing:** ~1 hour
- **Depends on:** 3
- **Verification:**
  - Scoped `lake build` shows the pos propositional cluster (sites 276, 304, 336, 363) cleared.
  - `git diff` confirms no theorem signature changed.
  - Commit: `task 364 phase 4: repair positive propositional rule-cases`.

---

### Phase 5: Negative propositional cases + structural fix (C5/C6 + C7) [NOT STARTED]

- **Goal:** Mirror Phase 4 for the negative branch and fix the genuine structural duplicate-`imp` bug.
- **Tasks:**
  - [ ] negNeg (620-638): C5 (mirror of C2) — strengthen simp set for recognizer reduction, then flat `obtain`.
  - [ ] orNeg (644-699): flat-obtain idiom (mirror of C3).
  - [ ] impNeg (700-723): flat-obtain idiom.
  - [ ] impNegGen (724-746): flat-obtain idiom.
  - [ ] C7 (STRUCTURAL): line 747 `Duplicate alternative name imp` — the degenerate second `imp` arm. Rename/merge so the second `| imp …` arm does not duplicate the earlier `| imp a c =>` (restructure as nested `cases` or guard). This touches only `cases`-arm internals, NOT the statement.
- **Timing:** ~1 hour
- **Depends on:** 4
- **Verification:**
  - Scoped `lake build` shows the neg propositional cluster (sites 625, 650, 706, 730) and 747 cleared.
  - `git diff` confirms no theorem signature changed (only `cases`-arm internals for C7).
  - Commit: `task 364 phase 5: repair negative propositional rule-cases and duplicate-imp structural fix`.

---

### Phase 6: boxNeg case + zero-debt verification (C4 + Families 1/2/4) [NOT STARTED]

- **Goal:** Repair the long-pole boxNeg case, then run the full zero-debt verification gate to close the task.
- **Tasks:**
  - [ ] C4: fix the boxNeg `obtain` entry at 403 (flat-obtain idiom from Phases 4-5).
  - [ ] In-case Family-4 `beqToEq` sites (441, 499, 506, 534, 560) — use `Proposition.beqToEq` for `Proposition`, `LawfulBEq.eq_of_beq` only for `WorldIndex`/`Nat`.
  - [ ] Family-1 sign idioms (509-512, 553-557): `cases h : … <;> simp_all [Sign.isPos]`.
  - [ ] Family-2 `Satisfies` simp ordering inside boxNeg, if it no-ops after the obtain clears: reorder after `rw` or use `Satisfies.neg_iff/diamond_iff/box_iff_forall`/`Proposition.neg_def`.
  - [ ] **Fallback (only if mid-case context overflows)**: extract `modalStepBranch_preserves_sat_boxNeg_boxProps_sat` / `…_diaNegProps_sat` private helpers per report 02 §5 — boxNeg only, never the full 10-lemma refactor.
  - [ ] Zero-debt gate (BLOCKING): scoped `lake build Cslib.Logics.Modal.Tableau.Soundness` clean; full `lake build` clean; `lean_verify Cslib.Logic.Modal.Tableau.modalStepBranch_preserves_sat` and `…modalTableau_sound` show zero `sorry`/zero new axioms; `lake exe lint-style`; `lake exe checkInitImports`.
  - [ ] Final `git diff` confirms every public theorem statement is byte-for-byte unchanged.
- **Timing:** ~1.5 hours (boxNeg is the long pole)
- **Depends on:** 5
- **Verification:**
  - Scoped + full `lake build` clean; `lake exe lint-style` clean; `lake exe checkInitImports` clean.
  - `grep -n "sorry\|admit" Cslib/Logics/Modal/Tableau/Soundness.lean` returns nothing; `lean_verify` shows no new axioms.
  - `git diff` shows zero statement changes.
  - Commit: `task 364: complete implementation`.

---

### Phase 7: Full-build regression + handoff [NOT STARTED]

- **Goal:** Confirm the repair has not regressed any dependent module and finalize the wrap-up.
- **Tasks:**
  - [ ] Full `lake build` (whole library) clean — confirms `modalExpandBranches_closed_unsat` and `modalTableau_sound` consumers (e.g. call site 941) still compile.
  - [ ] `lake test` (CslibTests suite) passes.
  - [ ] Update `.orchestrator-handoff.json` with final status, sorry_inventory (empty), and CI results.
  - [ ] Confirm no orphaned scaffolding remains (no leftover private helpers unless the boxNeg fallback was genuinely needed).
- **Timing:** ~0.5 hour
- **Depends on:** 6
- **Verification:**
  - Full `lake build` + `lake test` green.
  - Handoff JSON updated.
  - Commit (if any handoff/metadata changes): `task 364: finalize verification and handoff`.

## Testing & Validation

- [ ] Scoped: `lake build Cslib.Logics.Modal.Tableau.Soundness` exits clean (0 errors).
- [ ] Full: `lake build` exits clean across the whole library.
- [ ] Lint: `lake exe lint-style` clean.
- [ ] Init imports: `lake exe checkInitImports` clean.
- [ ] Tests: `lake test` (CslibTests) green.
- [ ] Zero sorry: `grep -n "sorry\|admit" Cslib/Logics/Modal/Tableau/Soundness.lean` empty.
- [ ] Zero new axioms: `lean_verify` on `modalStepBranch_preserves_sat` and `modalTableau_sound`.
- [ ] Statement preservation: `git diff` shows no public theorem type changed (signature lines 186-196, 798-812, 917-919).

## Artifacts & Outputs

- `plans/03_soundness-drift-repair.md` (this file).
- Repaired `Cslib/Logics/Modal/Tableau/Soundness.lean` (sorry-free, all statements preserved).
- `summaries/03_soundness-drift-repair-summary.md` (on implementation completion).
- Updated `.orchestrator-handoff.json`.
- One git commit per phase (7 commits), final commit `task 364: complete implementation`.

## Rollback/Contingency

- Each phase is an independent commit; revert any single phase with `git revert <sha>` without losing earlier chunks.
- If a phase fails to reduce errors, mark it `[PARTIAL]`, commit progress only if the file still builds with strictly fewer errors and zero `sorry`; otherwise leave the working tree uncommitted for the next `/implement` to resume.
- The file's last known-good task-364 state is commit `396c9435` ("restore to best-known state, 68 errors"); hard reset to it only on explicit user request.
- If the in-place repair stalls on boxNeg, fall back to the report-02 boxNeg-only helper extraction (Phase 6 fallback) — never escalate to the full 10-sub-lemma refactor.
- NEVER introduce an intermediate `sorry`; if a chunk cannot be completed sorry-free, stop and leave it uncommitted rather than scaffolding.
