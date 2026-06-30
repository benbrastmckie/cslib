# Implementation Plan: Task #388

- **Task**: 388 - Remove dead normalization track and heartbeat/simp debt in Termination.lean
- **Status**: [IN PROGRESS]
- **Effort**: 2.5 hours
- **Dependencies**: 398 (completed — added efq arms to normalize/normalizeAux; sequence after it)
- **Research Inputs**: specs/388_termination_deadcode_and_heartbeat_cleanup/reports/01_termination-deadcode-cleanup.md
- **Artifacts**: plans/01_termination-deadcode-cleanup.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This is a pure deletion-plus-lint cleanup of
`Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean`. Research confirmed
two cascading groups of dead private/public declarations (~405 lines total, all with 0 external
callers) plus a light residual lint sweep. The work is sequenced into small, independently
build-verifiable phases: each deletion group is removed and immediately validated with a scoped
`lake build`, then a lint sweep surfaces and fixes any env-linter debt the deletions expose, and
a final full-CI pass confirms zero-debt. No new definitions are introduced.

### Research Integration

Key findings driving this plan (from `01_termination-deadcode-cleanup.md`):
- **Group A** (lines 204–308, ~105 lines): `normalizeAux_fixpoint` (line 305, a public `theorem`
  with 0 callers) orphans its private support chain — `normalizeAux_ax` (204, `@[simp]`),
  `normalizeAux_ass` (210, `@[simp]`), `normalizeAux_fixpoint_aux` (216). Delete as a unit and
  update the module docstring at lines 18–19 (which references `normalizeAux_fixpoint`); review the
  section header `/-! ## Normalization Termination Lemmas -/` near line 202.
- **Group B** (lines 492–794, ~300 lines): `subs_maximalFormulas_mem` (492) and its sole caller
  `subsOne_new_redex_complexity_lt` (775) are jointly dead — delete both together (next live decl
  is `commutingSum` at 796).
- **DO NOT DELETE** `normalize`/`normalizeAux` — LIVE public defs in `Reduction.lean` (84, 105),
  including task-398 efq arms. They have 0 downstream theorem callers but are public API; public
  defs with 0 callers do not trip dead-code linters.
- **Regression risk** is limited to the two `@[simp]` lemmas `normalizeAux_ax`/`normalizeAux_ass`:
  a scoped `lake build` after Group A deletion confirms no unrelated `simp`/`simp_all` depended on
  them. (Verified: their only references are at lines 259/284, inside `normalizeAux_fixpoint_aux`,
  which is itself deleted in Group A.)
- **Lint debt is light**: no long lines, `lake exe lint-style` clean, no sorries. Most bare/flexible
  `simp` (508, 555, 593, 666, 731, 781) lives inside the Group B deletion region and vanishes.
- **maxHeartbeats override** at line 1195 is ALREADY comment-justified (1196–1198) — satisfies the
  task's "comment-justify" requirement. No mandatory action.
- Residual env-linter items (unused-simp-arg, no-op-tactic, flexible-simp) must be surfaced by
  running `lake lint` AFTER deletion, not pre-enumerated, since the deletions change the surface.

Line numbers were re-verified live at planning time and remain current
(204/210/216/305/308/492/775/796).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no roadmap_path / roadmap_flag in delegation context). Topic
is PL-Hygiene; the cleanup advances the Normalization track's lint-debt reduction.

## Goals & Non-Goals

**Goals**:
- Delete Group A (the `normalizeAux_fixpoint` cascade, lines 204–308) and update the module
  docstring (18–19) / section header (~202).
- Delete Group B (`subs_maximalFormulas_mem` + `subsOne_new_redex_complexity_lt`, lines 492–794).
- Clear any residual env-linter debt surfaced by `lake lint` after the deletions.
- Confirm the module passes the full CI pipeline (build, checkInitImports, lint, lint-style, test)
  with zero new debt (no sorries, no new axioms).

**Non-Goals**:
- Deleting `normalize`/`normalizeAux` in `Reduction.lean` or `Termination.lean` (explicitly LIVE).
- Decomposing the heavy `snImpEForm`/`snOrEForm`/`snSubst` mutual block (line 1199) — high-risk,
  out of scope unless trivially cheap (deferred to optional Phase 4).
- Removing the line-1195 `maxHeartbeats` override — already comment-justified; no action.
- Introducing any new definitions, lemmas, or abstractions.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| An unrelated `simp`/`simp_all` silently depended on `@[simp]` `normalizeAux_ax`/`normalizeAux_ass` | M | L | Phase 1 ends with a scoped `lake build` of the module; a break surfaces immediately and is isolated to Group A. |
| Line numbers shifted by a late task-398 edit | M | L | Phase 1/2 begin with `grep -n` re-verification of decl boundaries before any deletion. |
| Deleting only one of the jointly-dead Group B decls leaves a dead decl or broken reference | M | L | Delete 492–794 as a single unit (both decls together); verify next live decl `commutingSum` (796) is untouched. |
| `lake lint` surfaces more env-linter debt than expected | L | M | Phase 3 is scoped to "fix only what remains after deletion"; non-trivial findings are logged, and anything requiring redesign is deferred rather than forced. |
| Docstring/section-header edit leaves a dangling cross-reference | L | M | Phase 1 greps the file for residual `normalizeAux_fixpoint` mentions after the docstring edit. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 (optional) | 3 |

Phases are strictly sequential (each edits the same file and depends on the prior build being
green); there is no intra-wave parallelism.

### Phase 1: Delete Group A (normalizeAux_fixpoint cascade) + docstring [COMPLETED]

**Goal**: Remove the entire dead `normalizeAux_fixpoint` chain and its docstring references, then
confirm the `@[simp]` removals broke nothing.

**Tasks**:
- [ ] Re-verify boundaries with `grep -n` for `normalizeAux_ax` (~204), `normalizeAux_ass` (~210),
      `normalizeAux_fixpoint_aux` (~216), `normalizeAux_fixpoint` (~305, ends ~308).
- [ ] Delete the block lines 204–308 as a unit (all four decls).
- [ ] Update the module docstring at lines 18–19 to remove the "Strongly normal derivations are
      fixpoints of `normalizeAux`" reference (rewrite or delete the bullet).
- [ ] Review the section header `/-! ## Normalization Termination Lemmas -/` (~line 202): remove it
      if it no longer describes remaining content, otherwise leave it.
- [ ] Grep the file for any residual `normalizeAux_fixpoint` mentions; remove dangling references.
- [ ] Confirm `normalize`/`normalizeAux` defs in `Reduction.lean` are untouched.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean` — delete lines
  204–308; edit docstring 18–19; optionally remove section header ~202.

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization.Termination` succeeds
  (this is the scoped build that confirms the `@[simp]` ax/ass removals broke no unrelated simp).
- `grep -n "normalizeAux_fixpoint\|normalizeAux_ax\|normalizeAux_ass" Termination.lean` returns no
  hits.

---

### Phase 2: Delete Group B (subs/subsOne redex pair) [COMPLETED]

**Goal**: Remove the jointly-dead `subs_maximalFormulas_mem` + `subsOne_new_redex_complexity_lt`
pair and confirm the module still builds.

**Tasks**:
- [ ] Re-verify boundaries with `grep -n` for `subs_maximalFormulas_mem` (~492), its docstring
      (~768), `subsOne_new_redex_complexity_lt` (~775), and the next live decl `commutingSum`
      (~796). (Note: line numbers shift down by ~105 after Phase 1; re-grep.)
- [ ] Delete the block from `subs_maximalFormulas_mem` start through the end of
      `subsOne_new_redex_complexity_lt` (research range 492–794, pre-Phase-1 numbering) as a single
      unit, including the `subsOne` docstring.
- [ ] Confirm `commutingSum` (the next live decl) and everything after it is untouched.

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean` — delete the
  `subs_maximalFormulas_mem` … `subsOne_new_redex_complexity_lt` block as a unit.

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization.Termination` succeeds.
- `grep -n "subs_maximalFormulas_mem\|subsOne_new_redex_complexity_lt" Termination.lean` returns no
  hits.

---

### Phase 3: Lint sweep + residual debt fixes + CI verify [COMPLETED]

**Goal**: Surface and fix any env-linter debt exposed by the deletions, confirm the heartbeat
override remains justified, and pass the full CI pipeline.

**Tasks**:
- [ ] Run `lake lint` and inspect findings scoped to Termination.lean (unused-simp-arg,
      no-op-tactic, flexible-simp, dead-code).
- [ ] Fix only the residual warnings that survive the deletions; do not introduce new abstractions.
      Log (do not force) anything that would require redesign.
- [ ] Run `lake exe lint-style` and confirm no Termination/Reduction findings.
- [ ] Confirm the line-1195 `maxHeartbeats` override still carries its justifying comment
      (1196–1198); take no action on it unless Phase 4 is attempted.
- [ ] Confirm zero sorries / no new axioms in the modified files.

**Timing**: 1 hour (mostly build/lint wall time)

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean` — only if `lake lint`
  surfaces residual warnings.

**Verification** (full CI pipeline, in order):
- `lake build` succeeds (whole library).
- `lake exe checkInitImports` passes.
- `lake lint` clean for Termination.lean (no new warnings).
- `lake exe lint-style` clean.
- `lake test` passes (CslibTests suite).

---

### Phase 4 (OPTIONAL, low-priority): Heavy mutual-block decomposition [NOT STARTED] *(deviation: skipped -- high-risk, not trivially cheap; maxHeartbeats override already comment-justified)*

**Goal**: Only if trivially cheap, attempt to decompose the `snImpEForm`/`snOrEForm`/`snSubst`
mutual well-founded recursion (line 1199) to allow lowering/removing the line-1195 heartbeat
override.

**Tasks**:
- [ ] Assess whether the mutual block can be split without breaking termination inference (the
      equation compiler treats it as one unit; splitting risks termination-inference failure).
- [ ] If and only if a clean split is found that lets the heartbeat override drop, apply it;
      otherwise SKIP and leave the already-justified override in place.

**Timing**: 0 hours if skipped (default); up to 1 hour if attempted.

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean` — only if a clean
  decomposition is found.

**Verification**:
- If attempted: `lake build` + `lake test` succeed AND the heartbeat override is demonstrably
  reduced/removed. If not cleanly achievable, revert and skip (override stays comment-justified).

## Testing & Validation

- [ ] `lake build` succeeds with both deletion groups removed.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake lint` is clean for Termination.lean (no new env-linter warnings post-deletion).
- [ ] `lake exe lint-style` is clean.
- [ ] `lake test` passes.
- [ ] No `normalizeAux_fixpoint` / `normalizeAux_ax` / `normalizeAux_ass` /
      `subs_maximalFormulas_mem` / `subsOne_new_redex_complexity_lt` references remain.
- [ ] `normalize`/`normalizeAux` defs in `Reduction.lean` are intact (untouched).
- [ ] Zero sorries / no new axioms in modified files.

## Artifacts & Outputs

- Modified `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean`
  (~405 lines removed, docstring updated, optional lint fixes).
- Execution summary at `specs/388_termination_deadcode_and_heartbeat_cleanup/summaries/01_*.md`
  (produced by /implement).

## Rollback/Contingency

- Each phase ends with a build/CI gate; if any phase's `lake build` fails, `git checkout --
  Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean` reverts that phase's
  edits and the failure is diagnosed before retrying.
- If Phase 1's scoped build reveals an unrelated `simp` depended on the `@[simp]` ax/ass lemmas,
  isolate the dependent proof and either supply the needed rewrite locally or restore the minimal
  `@[simp]` lemma — but the research expects this not to occur (their only refs are inside the
  deleted `_aux`).
- Phase 4 is fully optional; skipping it leaves the module in a clean, CI-green state with the
  heartbeat override comment-justified.
