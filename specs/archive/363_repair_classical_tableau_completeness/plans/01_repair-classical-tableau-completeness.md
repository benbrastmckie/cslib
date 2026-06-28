# Implementation Plan: Task #363 - Repair Classical Tableau Completeness

- **Task**: 363 - Repair Classical/Tableau/Completeness.lean proof gaps and bad lemma ref
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: None (parent task 360, no blocking active tasks)
- **Research Inputs**: specs/363_repair_classical_tableau_completeness/.orchestrator-handoff.json
- **Artifacts**: plans/01_repair-classical-tableau-completeness.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

`Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` was left mid-refactor and fails its scoped build (`lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness`) with 60+ errors PLUS a genuine unfilled `sorry` at line 462 (`classicalExpandBranches_hintikka`). The original task description ("lines 110, 111, 117") drastically understates the scope: the entire `classicalTruthLemma` proof script (lines 84-399) is broken against the current `classicalApplyOne`/`tryAllPropRules` definition, and several auxiliary lemmas (`classicalStepBranch_mem_preserved`, `classicalOpenBranch_countermodel`, `classicalTableau_complete`) also break. Definition of done: the module builds green with zero debt (no `sorry`, no `axiom`) and passes lint. The research handoff supplies concrete, project-verified fixes for every mechanical error; the only genuine open obligation is filling the line-462 `sorry` (~80-150 lines), which mirrors the already-proven companion lemma `classicalExpandBranches_openBranch_initial_mem`.

### Research Integration

The research report (`.orchestrator-handoff.json`) root-caused all failures and validated each mechanical fix via project-linked scratch builds. Key integrated findings:

- **Root cause**: `classicalApplyOne sf` now routes through `tryAllPropRules ... sf` (Expansion.lean:66), pattern-matching on `sf.sign`/`sf.formula` of an opaque `sf`. The old `rw [hsign, hform, hbot]; rfl` cannot rewrite projections that do not syntactically appear, so every `hca` computation fails. Fix: destructure `sf` (`obtain ⟨s, fm, l⟩ := sf; subst ...; rfl`) so `classicalApplyOne` reduces by `rfl`.
- **Sign extraction**: replace `cases sf.sign <;> simp_all [SignedFormula.sign]` with `eq_of_beq hsfcond.1` (mirrors working `eq_of_beq hsfcond.2`), all 8 sites.
- **API drift**: `List.mem_cons_self` is now fully implicit — drop the `_ _` arguments (or use `by simp`).
- **Non-existent lemmas**: `List.findSome?_of_mem` and `List.find?_of_mem` do not exist. Replace `hasContradiction` proof with `List.findSome?_eq_none_iff`; replace `botPos` closure with case-split on `b.find? ...` using `List.find?_eq_none` / `List.isSome_find?`.
- **Dead bullet**: `split_ifs at hfound` now yields one goal; delete the dead `Option.noConfusion` bullet (line ~481).
- **Misc**: line 656 `simp` -> `simp only [List.mem_singleton]`; line 675 `exact hnt rfl` -> `exact hnt htab`.
- **Reuse check confirmed**: all supporting abstractions already exist in `Cslib.Foundations.Logic.Tableau`; no new definitions are needed, and all replacement lemmas are Lean-core/Mathlib.

### Prior Plan Reference

No prior plan. This is the first plan for task 363. (Parent task 360 was a build-repair effort that blocked on this WIP file; its findings are subsumed by the research handoff.)

### Roadmap Alignment

No `roadmap_path` provided and `roadmap_flag` not set; ROADMAP alignment not evaluated for this plan.

## Goals & Non-Goals

**Goals**:
- Repair the `classicalTruthLemma` proof script (lines 84-399) against the current `classicalApplyOne`/`tryAllPropRules` definition using the verified mechanical fixes.
- Repair the auxiliary lemmas `classicalStepBranch_mem_preserved`, `classicalOpenBranch_countermodel`, and `classicalTableau_complete`.
- Fill the line-462 `sorry` in `classicalExpandBranches_hintikka` with a genuine proof.
- Achieve a green scoped build (`lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness`) with zero debt: no `sorry`, no `axiom`.
- Pass the CSLib lint/CI checks (`lake exe lint-style`, `lake exe checkInitImports`, shake).

**Non-Goals**:
- Refactoring or redesigning `classicalApplyOne`, `tryAllPropRules`, or any `Cslib.Foundations.Logic.Tableau` abstraction (reuse check confirmed they are correct; only the proof script consuming them is stale).
- Introducing new definitions or lemmas into the Foundations layer.
- Touching unrelated modules in `Cslib/Logics/Propositional/Tableau/`.
- Leaving any `sorry` or `axiom` as a deferral; if line 462 proves intractable within budget, the task is marked [BLOCKED], not [PARTIAL] with debt.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line-462 `sorry` (`classicalExpandBranches_hintikka`) proves intractable within budget | H | M | Sequence it as its own dedicated phase (Phase 3) AFTER mechanical repairs land green. Pattern directly after the fully-proven companion `classicalExpandBranches_openBranch_initial_mem` (lines 511-634). If still intractable, mark task [BLOCKED] per zero-debt policy — do NOT leave the sorry. |
| Mechanical fixes interact (fixing one site reveals a hidden error at another) | M | M | Apply fixes site-by-site within a phase; run scoped `lake build` after each phase to localize regressions. All fixes were individually scratch-build verified in research. |
| `lean_diagnostic_messages` misuse causes wasted cycles / context bloat | L | M | EXPLICIT PROHIBITION: do NOT call `lean_diagnostic_messages`. Use scoped `lake build` for error discovery and `lean_goal`/`lean_multi_attempt`/`lean_hover_info` for targeted goal inspection. |
| `HasBot.bot` namespace resolution differs outside scratch context | L | L | Research notes it already resolves in-file; verify with `lean_hover_info` before committing botPos fix. |
| Lint failures after green build (unused vars, style) | L | M | Phase 4 runs the full lint suite and repairs any style/unused-binding warnings before completion. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: all phases edit the same file and each later phase builds on the green state established by the prior phase.

---

### Phase 1: Mechanical repair of classicalTruthLemma (lines 84-399) [COMPLETED]
<!-- Phase 1 started -->
<!-- IMPLEMENTATION NOTE: Using List.isSome_findSome? approach for hcont, List.find?_eq_none approach for botPos -->

**Goal**: Eliminate the 60+ mechanical errors in the `classicalTruthLemma` proof script by applying the research-verified fixes, leaving only the line-462 `sorry` and any line 481/656/675 errors (addressed in Phase 2) outstanding.

**Tasks**:
- [ ] Sign extraction (8 sites: lines ~110, 111, 160, 254, 326, 343, 366, 387): replace `by cases sf.sign <;> simp_all [SignedFormula.sign]` with `eq_of_beq hsfcond.1` (mirroring the working `eq_of_beq hsfcond.2` on the adjacent formula line).
- [ ] `hca` reduction (sites: lines ~169, 183, 202, 219, 236, 263, 275, 287, 299, 311, 330, 347, 370, 391): replace `by rw [hsign, hform, hbot]; rfl` with `by obtain ⟨s, fm, l⟩ := sf; subst hsign hform hbot; rfl`. Drop `hbot` from the `subst` for the and/or cases that do not split on `c`.
- [ ] Membership API (sites: lines ~173, 190, 195, 208, 212, 225, 229, 242, 246, 266, 352, 356, 375, 379): replace `List.mem_cons_self _ _` with bare `List.mem_cons_self` (or `by simp`).
- [ ] `hasContradiction` (line ~117): replace the `apply List.findSome?_of_mem ...` block with the verified proof using `rw [Branch.hasContradiction, Option.isSome_iff_ne_none]; intro hnone; rw [Branch.findContradiction, List.findSome?_eq_none_iff] at hnone; ...` then `rw [if_pos ...]` and derive the contradiction (discharge the `==` label goal by `simp`, since labels are `Unit`).
- [ ] `botPos` closure (lines ~146, 147): replace `use sf; apply List.find?_of_mem ...` with a case-split on `b.find? (fun sf => sf.isPos && sf.formula == HasBot.bot)`: `some` -> `⟨_, rfl⟩`; `none` -> `rw [List.find?_eq_none] at hf` and contradict using the known `T(bot)` member. Verify `HasBot.bot` resolves in-file with `lean_hover_info` first.
- [ ] Run scoped build `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` and confirm the only remaining failures are the line-462 `sorry` warning and the Phase-2 sites (481/656/675).
- [ ] Commit: `task 363 phase 1: repair classicalTruthLemma proof script`.

**Timing**: ~2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - lines 84-399 (`classicalTruthLemma` proof script).

**Verification**:
- Scoped `lake build` shows zero errors in lines 84-399 (the `classicalTruthLemma` block).
- Remaining diagnostics are limited to the known line-462 `sorry` and the Phase-2 sites.
- Do NOT call `lean_diagnostic_messages`; use scoped `lake build` output plus `lean_goal` for any residual goal.

---

### Phase 2: Repair stepBranch, countermodel, and complete lemmas [COMPLETED]

**Goal**: Repair the three auxiliary lemmas that break independently of `classicalTruthLemma`, leaving only the line-462 `sorry` outstanding.

**Tasks**:
- [ ] `classicalStepBranch_mem_preserved` (line ~481): delete the dead `· exact Option.noConfusion hfound` bullet and its comment (~lines 480-482); `split_ifs at hfound with hexp` now produces a single goal.
- [ ] `classicalOpenBranch_countermodel` (line ~656): replace `simp at hb₀` with `simp only [List.mem_singleton] at hb₀`, then `subst hb₀; exact List.mem_cons_self`.
- [ ] `classicalTableau_complete` (line ~675): replace `exact hnt rfl` with `exact hnt htab`.
- [ ] Run scoped build and confirm the ONLY remaining failure is the line-462 `sorry` (`classicalExpandBranches_hintikka`).
- [ ] Commit: `task 363 phase 2: repair stepBranch/countermodel/complete lemmas`.

**Timing**: ~0.75 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - lines ~480-482, ~656, ~675.

**Verification**:
- Scoped `lake build` reports zero errors except the single `sorry` warning at line 462.
- Each repaired lemma's goal is closed (spot-check with `lean_goal` at the lemma tail showing "no goals").

---

### Phase 3: Fill the classicalExpandBranches_hintikka sorry (line 462) [BLOCKED] — ZERO-DEBT RISK PHASE

**Goal**: Replace the line-462 `sorry` in `classicalExpandBranches_hintikka` with a genuine proof, achieving zero debt. This is the primary risk phase.

**Tasks**:
- [ ] Study the fully-proven companion lemma `classicalExpandBranches_openBranch_initial_mem` (lines 511-634): it uses the same fuel + nested-pending-list induction skeleton and demonstrates the loop-invariant approach works.
- [ ] Reproduce the loop-invariant skeleton for the Hintikka property: every formula's rule outputs are on the returned open branch.
- [ ] Add the SATURATION argument: when `classicalStepBranch b e = none`, every `sf ∈ b` is either (a) already in `expanded` — so its outputs are on `b` by the maintained invariant — or (b) has `classicalApplyOne sf = .notApplicable` — so the Hintikka condition holds vacuously. The loop returns `.openBranch b` only via that saturated branch.
- [ ] Use `lean_goal` / `lean_multi_attempt` / `lean_hover_info` to drive the proof; do NOT call `lean_diagnostic_messages`.
- [ ] Run scoped build and confirm zero errors AND zero `sorry`/`axiom` warnings.
- [ ] Verify zero debt explicitly: `grep -n "sorry\|admit" ` on the file returns nothing in proof bodies, and `lean_verify Cslib.Logics.Propositional.Tableau.Classical.classicalExpandBranches_hintikka` shows no `sorryAx` in the axiom list.
- [ ] Commit: `task 363 phase 3: fill classicalExpandBranches_hintikka (zero sorry)`.

**BLOCKED fallback**: If the proof proves intractable within the phase budget (substantial over-run with no convergence on the saturation argument), STOP and mark the task [BLOCKED] with a precise description of the remaining obligation (the saturation step that resists closure) and the partial proof state. Do NOT leave the `sorry` in place and do NOT mark the task complete/partial with debt. Preserve Phases 1-2 green state via their commits.

**Timing**: ~1.5-2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - lines ~448-462 (`classicalExpandBranches_hintikka` body), patterned after lines 511-634.

**Verification**:
- Scoped `lake build` is fully green (zero errors, zero warnings about `sorry`).
- `lean_verify` on `classicalExpandBranches_hintikka` confirms no `sorryAx` dependency.
- `grep -rn "sorry" Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` finds no live `sorry`.

---

### Phase 4: Full green build and lint [NOT STARTED]

**Goal**: Confirm the module builds green with zero debt across the full CI pipeline and passes lint.

**Tasks**:
- [ ] Run scoped build: `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` — must be fully green.
- [ ] Run `lake exe checkInitImports` and confirm no init-import violations introduced.
- [ ] Run `lake exe lint-style` and repair any style violations in the edited file.
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` (if applicable to this module) and address unused-import findings limited to this file.
- [ ] Repair any lint warnings (unused variables, unused binders) introduced by the proof edits.
- [ ] Final zero-debt check: no `sorry`, no `axiom`, no `admit` in the file.
- [ ] Commit: `task 363: complete implementation` (or `task 363 phase 4: green build + lint`).

**Timing**: ~0.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - lint/style touch-ups only.

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` exits 0 with no warnings.
- `lake exe lint-style` and `lake exe checkInitImports` pass.
- Module contains zero `sorry`/`axiom`/`admit`.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` is fully green (zero errors, zero warnings).
- [ ] No `sorry`, `axiom`, or `admit` remains in `Completeness.lean` (verified by grep and `lean_verify`).
- [ ] `lake exe lint-style` passes for the edited file.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake shake` reports no new unused-import issues for the module.
- [ ] Each repaired lemma's goal closes ("no goals" at lemma tail).

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - repaired, building green with zero debt.
- `specs/363_repair_classical_tableau_completeness/plans/01_repair-classical-tableau-completeness.md` (this plan).
- `specs/363_repair_classical_tableau_completeness/summaries/01_repair-classical-tableau-completeness-summary.md` (on implementation completion).
- Incremental git commits per phase (Phases 1-4).

## Rollback/Contingency

- **Per-phase commits** allow reverting any single phase via `git revert` while preserving earlier green states.
- **Phase 3 intractable**: mark task [BLOCKED] (NOT [PARTIAL] with debt) with a precise description of the unclosed saturation obligation; Phases 1-2 commits remain as preserved progress for a future attempt.
- **Regression in a later phase**: scoped `lake build` after each phase localizes the failure; revert the offending phase commit and re-attempt with the prior green state intact.
- **Full abort**: `git checkout -- Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` restores the original WIP file (which is already non-building, so no working state is lost).
