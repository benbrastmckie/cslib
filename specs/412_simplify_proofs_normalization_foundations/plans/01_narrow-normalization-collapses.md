# Implementation Plan: Simplify Normalization Proof Sites (Narrowed Scope)

- **Task**: 412 - simplify_proofs_normalization_foundations
- **Status**: [COMPLETED]
- **Effort**: 1 hour
- **Dependencies**: 41 (`abstract_completeness_infrastructure`, not started) — deferred sites excluded from this plan so no hard block remains
- **Research Inputs**: reports/01_simplify-normalization-proof-sites.md
- **Artifacts**: plans/01_narrow-normalization-collapses.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib

## Overview

The task's original premise — verbose multi-lemma `simp only [listImp_nil, listImp_cons,
bigconj_*, ...]` lists that the `@[simp, scoped grind =]` co-tags render redundant — is **stale**:
research confirmed zero such verbose lists remain. Every current call site is already a
single-lemma `simp only [X]`. The only remaining, empirically-confirmed wins are two tactic-chain
collapses in files that the unstarted, code-relocating dependency (task 41) is least likely to
move. This plan is deliberately narrowed to exactly those two edits plus the full CSLib CI gate.

Definition of done: the two collapses are applied, all now-dead follow-on tactic lines are
deleted, the tree is `sorry`-free, and `lake build`, `lake test`, `lake exe checkInitImports`,
`lake exe lint-style`, and `lake shake` all pass.

### Research Integration

From `reports/01_simplify-normalization-proof-sites.md`:
- **CONFIRMED collapse** at `Cslib/Foundations/Logic/Theorems/BigConj.lean:111-113` — the
  singleton branch of `bigconj_mem_derivable`. `grind` closes the whole branch; the follow-on
  `simp only [List.mem_singleton] at hmem` and `rw [hmem]; exact hconj` become dead
  ("No goals to be solved") and must be deleted.
- **CONFIRMED collapse** at `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean:77-78` —
  `simp only [listImp_cons]; exact listImp_axiom_k φ Ψ` collapses to `grind [listImp_axiom_k]`
  (bare `grind` fails; the explicit `[listImp_axiom_k]` premise is required).
- Every successful `grind` collapse leaves the *following* tactic lines as dead code, so each
  rewrite is a **multi-line deletion**, not a one-line swap.
- Zero new declarations, no docstrings, no `sorry`, no axioms — no lint categories are implicated.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided; ROADMAP.md not consulted. Topic per state.json: "Code Hygiene".

## Goals & Non-Goals

**Goals**:
- Collapse `BigConj.lean:111-113` (singleton branch) to a single `grind`, deleting the two dead
  follow-on lines.
- Collapse `ListDeduction.lean:77-78` to `grind [listImp_axiom_k]`, deleting the dead `exact` line.
- Keep the tree `sorry`-free and pass the full CSLib CI gate.

**Non-Goals**:
- **Excluded — deferred until task 41 lands** (task 41 will likely relocate these files):
  `Metalogic/MCSProperties.lean` (sites :110, :125) and `Metalogic/GenericMCS.lean` (sites :242,
  :244). Do NOT touch these files.
- **Excluded — out of stated scope** (`Logics/`, not `Foundations/Logic/`): all
  `Logics/*/Metalogic/**/GenericMCSBridge.lean` sites (Bimodal, Modal, Temporal). Do NOT touch.
- **Not attempted** — the `ListDeduction.lean:82-83` collapse (`grind [HasAxiomImplyK.implyK]`)
  is left as-is; research flagged it as needing verification and it offers marginal value. Keep it.
- Normalization-then-manual-ModusPonens sites (`BigConj.lean:115, 128, 133, 136`) stay as-is.
- No new lemmas, abstractions, notation, or docstring changes.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `grind` collapse leaves undeleted dead follow-on lines ("No goals to be solved" build error) | M | M | Treat each collapse as a multi-line deletion; after each edit run scoped `lake build` on the module and confirm no "No goals" diagnostic before proceeding. |
| A `grind` variant that passed under `lean_multi_attempt` behaves differently in-file | L | L | Re-verify each site with `lean_goal`/`lean_multi_attempt` at the exact source position before editing; fall back to the research-confirmed alternative (`simp_all` for BigConj:111; `exact listImp_axiom_k φ Ψ` after the existing `simp only` for ListDeduction:77). |
| Task-41 relocation later re-sweeps these files | L | L | Scope is restricted to the two files research judged least likely to move; deferred sites are explicitly out of scope. |
| Editing shifts line numbers for the second target | L | M | Edit files independently; re-locate the ListDeduction target by its surrounding context (`unfold ListDeriv` / `listImp_axiom_k`), not by absolute line number. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Apply the two confirmed collapses [COMPLETED]

- **Goal:** Replace the two confirmed tactic chains with `grind` forms and delete all now-dead
  follow-on lines, verifying each site before and after editing.
- **Tasks:**
  - [x] `Cslib/Foundations/Logic/Theorems/BigConj.lean`: in the `nil` sub-branch of
    `bigconj_mem_derivable` (the `| nil =>` arm under `cases rest`, currently lines 110-113),
    replace the three lines
    `simp only [bigconj_singleton] at hconj` / `simp only [List.mem_singleton] at hmem` /
    `rw [hmem]; exact hconj` with a single `grind`. Delete the two follow-on lines that `grind`
    makes dead.
  - [x] `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean`: in the `φ = ψ` branch (currently
    lines 76-78, after `unfold ListDeriv`), replace `simp only [listImp_cons]` /
    `exact listImp_axiom_k φ Ψ` with `grind [listImp_axiom_k]`. Delete the now-dead `exact` line.
    Keep the preceding `unfold ListDeriv` only if `grind [listImp_axiom_k]` still requires it;
    verify with `lean_multi_attempt` whether `unfold ListDeriv; grind [listImp_axiom_k]` or bare
    `grind [listImp_axiom_k]` is needed, and keep the minimal form that closes the goal.
    *(confirmed: bare `grind [listImp_axiom_k]` fails without `unfold ListDeriv`; kept
    `unfold ListDeriv` and collapsed the two follow-on lines to `grind [listImp_axiom_k]`.)*
  - [x] Before each edit, confirm the goal state at the target with `lean_goal`; use
    `lean_multi_attempt` at the exact source position to re-confirm the `grind` form closes the
    branch (fallbacks: `simp_all` for BigConj; `exact listImp_axiom_k φ Ψ` after the existing
    `simp only` for ListDeduction).
  - [x] After each edit, run a scoped build of the affected module and confirm there is no
    "No goals to be solved" / unused-tactic diagnostic left behind.
- **Timing:** ~40 minutes
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Foundations/Logic/Theorems/BigConj.lean` — collapse singleton branch to `grind`,
    delete two dead lines.
  - `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean` — collapse to `grind [listImp_axiom_k]`,
    delete dead `exact` line.
- **Verification:**
  - `lake build Cslib.Foundations.Logic.Theorems.BigConj` passes with no warnings.
  - `lake build Cslib.Foundations.Logic.Metalogic.ListDeduction` passes with no warnings.
  - `lean_verify` (or grep) confirms no `sorry` introduced in either file.

### Phase 2: Full CSLib CI verification gate [COMPLETED]

- **Goal:** Confirm the two edits pass the complete CSLib CI pipeline.
- **Tasks:**
  - [x] `lake build` (full project) — passes (3255/3255 jobs).
  - [x] `lake test` — passes (9247/9247 jobs).
  - [x] `lake exe checkInitImports` — passes (no output, exit 0).
  - [x] `lake exe lint-style` — passes (no output, exit 0).
  - [x] `lake lint` — "Linting passed for Cslib."
  - [x] `lake shake` — no findings for either modified file (pre-existing
    findings/warnings/sorries in unrelated `Tableau/*` files only; matches the
    established precedent of ignoring out-of-scope shake/build noise, see
    `specs/550_remove_bimodal_temporal_linter_suppressions/summaries/01_drop-linter-suppressions-summary.md`).
  - [x] Confirm the working tree is `sorry`-free in the two modified files (repo-wide
    pre-existing sorry count of 144 is unrelated, entirely outside `Foundations/Logic/`).
- **Timing:** ~20 minutes (assumes Mathlib cache present; run `lake exe cache get` first if not)
- **Depends on:** 1
- **Verification:**
  - All five CI commands exit zero.
  - `git diff` shows only the two intended files changed, with net line reductions (dead lines
    removed), no new declarations.

## Testing & Validation

- [x] `lake build` passes (full project).
- [x] `lake test` passes.
- [x] `lake exe checkInitImports` passes.
- [x] `lake exe lint-style` passes.
- [x] `lake shake` passes (no findings for either modified file).
- [x] No `sorry`, no new axioms, no new declarations introduced.
- [x] Only `BigConj.lean` and `ListDeduction.lean` are modified.

## Artifacts & Outputs

- `plans/01_narrow-normalization-collapses.md` (this file)
- `summaries/01_narrow-normalization-collapses-summary.md` (on implementation)
- Modified: `Cslib/Foundations/Logic/Theorems/BigConj.lean`,
  `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean`

## Rollback/Contingency

- Each collapse is an isolated, independent edit inside a single proven declaration. If either
  fails to build after the collapse, revert that one file to the pre-edit tactic chain
  (`git checkout` the single file — clean-tree exemption applies once the other edit is committed)
  and leave that site untouched; the other collapse still stands on its own.
- If `grind` proves non-reproducible in-file for a site, fall back to the research-confirmed
  alternative for that site (`simp_all` for BigConj:111; retain `simp only [listImp_cons]; exact
  listImp_axiom_k φ Ψ` for ListDeduction:77). Reverting to the original chain is always a valid
  no-op outcome for a site given the low reward.
