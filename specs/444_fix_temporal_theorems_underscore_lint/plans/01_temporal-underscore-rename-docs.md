# Implementation Plan: Task #444

- **Task**: 444 - Uniformity pass: mathlib-conformant naming, style, and docstrings across the task-180 Temporal diff (narrowed for this run to the live in-scope lint findings)
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None actionable now (449, 450 not_started -> their decls out of scope; 454 completed/settled; report already delivered)
- **Research Inputs**: specs/444_fix_temporal_theorems_underscore_lint/reports/01_temporal-naming-lint-uniformity.md
- **Artifacts**: plans/01_temporal-underscore-rename-docs.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Rename the two `defsWithUnderscore`-flagged data-carrying `def`s in `Temporal/Theorems.lean`
to mathlib-conformant lowerCamelCase and update their three docstring references (one of which
also carries a wrong namespace prefix). This is a renames-and-docs-only change with ZERO
behavioural impact: no proof bodies change, no `def` becomes a `theorem`/`lemma`, no sorries or
axioms are introduced or removed. Grep (per research) confirms the two defs have no code call
sites, so the rename is local. A single mandatory implementation phase suffices given the tiny,
precise scope; an optional droppable phase applies the same lowerCamelCase convention to the
private (lint-exempt) `hyp_syl` helper for uniformity.

### Research Integration

Report `01_temporal-naming-lint-uniformity.md` narrowed the elevated task-180 uniformity mandate
to the only live, actionable work for this run:
- Live `lake lint` in scope yields **exactly two** findings, both `defsWithUnderscore`:
  `allFuture_iff_neg_someFuture_neg` (Theorems.lean def line 58) and
  `allPast_iff_neg_somePast_neg` (Theorems.lean def line 70).
- Both return `DerivationTree ...` (data, not `Prop`) -> correctly `def`; the fix is the rename,
  keeping `def`. They must NOT be converted to `theorem`/`lemma`.
- Recommended names: `allFutureIffNegSomeFutureNeg`, `allPastIffNegSomePastNeg` (direct
  camelCase of the descriptive names).
- The distinct **semantic** theorem `sat_allFuture_iff_neg_someFuture_neg` (a `Prop`/`theorem`)
  correctly stays snake_case and is NOT renamed.
- Three docstring references need updating (Theorems.lean:69, TemporalEmbedding.lean:34,
  Formula.lean:97); the TemporalEmbedding reference also has a wrong `Theorems.` module prefix
  that must become `Metalogic.` (the decl's real namespace is `Cslib.Logic.Temporal.Metalogic`).
- Other lint categories named in the task mandate (`defLemma`, `docBlame`, `dupNamespace`,
  `topNamespace`, `simpNF`, `unusedSectionVars`) are confirmed NOT firing in scope.
- Optional (non-blocking): `hyp_syl` -> `hypSyl` in Instances.lean (private, lint-exempt, 6
  internal call sites + 1 comment) for convention uniformity.

Live source lines were re-verified against the working tree during planning: Theorems.lean def
keywords at lines 58 and 70; docstring cross-ref at line 69; TemporalEmbedding.lean:34;
Formula.lean:97; Instances.lean `private def hyp_syl` at line 83.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no roadmap_path / roadmap_flag provided). Task advances
the task-180 code-hygiene line (parent_task 180) by clearing the two blocking lint findings.

## Goals & Non-Goals

**Goals**:
- Rename `allFuture_iff_neg_someFuture_neg` -> `allFutureIffNegSomeFutureNeg` (keep `def`).
- Rename `allPast_iff_neg_somePast_neg` -> `allPastIffNegSomePastNeg` (keep `def`).
- Update the 3 docstring references to the new names, fixing the wrong `Theorems.` -> `Metalogic.`
  prefix in TemporalEmbedding.lean:34.
- Clear both `defsWithUnderscore` lint findings on the touched files.
- Preserve zero behavioural change: no proof-body edits, no `def`->`theorem` conversion, no new
  sorries/axioms.

**Non-Goals**:
- Do NOT rename the distinct semantic theorem `sat_allFuture_iff_neg_someFuture_neg` /
  `sat_allPast_iff_neg_somePast_neg` (they are `Prop`/`theorem`s, correct in snake_case).
- Do NOT touch task 449 declarations (BX+ / FrameClass.Metric axioms) — not_started, do not exist.
- Do NOT touch task 450 declarations (`eraseBox`, restated conservativity) — not_started.
- Do NOT touch `Metalogic/ConservativeExtension/TemporalConservativity.lean` — deferred until
  task 450 rewrites it.
- Do NOT touch `Cslib/Logics/Temporal/Tableau/**` — owned by the task-301 line (426/439/425).
- Do NOT modify task 454's settled Chronicle/PointInsertion/Since files.
- Do NOT rename `DerivationTree` constructors (`modus_ponens`, `axiom`) — cross-cutting, ripples
  into out-of-scope Tableau; not lint-flagged.
- Do NOT remove `set_option linter.style.*` suppressions — legitimate, not dev-only.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A hidden code call site breaks the build after rename | H | L | Research grep-verified no code call sites; `lake build` in verification catches any missed reference before PR |
| Accidentally renaming the distinct `sat_*` semantic theorem | M | L | Explicit Non-Goal; edits target only the exact `def` names and their docstrings; distinct decls live in different files (Satisfies.lean) |
| Missing a docstring reference leaves a stale name | L | L | Post-edit `grep -rn` for the two old identifiers across in-scope files must return zero outside history |
| Optional `hyp_syl` rename misses one of 6 call sites -> build break | M | L | Keep optional phase self-contained; use `grep -n hyp_syl` before/after; drop phase entirely if any doubt (it is non-blocking) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 (optional) | 1 |

Phase 2 is optional and droppable (not lint-required). It is sequenced after Phase 1 so the
final `lake lint` / `lake build` verification observes the combined state; it touches a different
file (Instances.lean) and carries no behavioural dependency on Phase 1.

### Phase 1: Rename flagged defs and update docstring references [COMPLETED]

**Goal**: Clear the two `defsWithUnderscore` findings via lowerCamelCase renames and fix all
three docstring references (including the wrong namespace prefix), with zero behavioural change.

**Tasks**:
- [ ] `Cslib/Logics/Temporal/Theorems.lean:58` — rename `def allFuture_iff_neg_someFuture_neg`
      -> `def allFutureIffNegSomeFutureNeg` (keep `def`; do not alter the body).
- [ ] `Cslib/Logics/Temporal/Theorems.lean:70` — rename `def allPast_iff_neg_somePast_neg`
      -> `def allPastIffNegSomePastNeg` (keep `def`; do not alter the body).
- [ ] `Cslib/Logics/Temporal/Theorems.lean:69` — in the `allPast` docstring cross-ref, update
      `allFuture_iff_neg_someFuture_neg` -> `allFutureIffNegSomeFutureNeg`.
- [ ] `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean:34` — update
      `Theorems.allFuture_iff_neg_someFuture_neg` -> `Metalogic.allFutureIffNegSomeFutureNeg`
      (corrects both the name and the wrong `Theorems.` module prefix).
- [ ] `Cslib/Logics/Temporal/Syntax/Formula.lean:97` — update `allFuture_iff_neg_someFuture_neg`
      -> `allFutureIffNegSomeFutureNeg`.
- [ ] Sanity grep: `grep -rn "allFuture_iff_neg_someFuture_neg\|allPast_iff_neg_somePast_neg"
      Cslib/Logics/Temporal Cslib/Logics/Bimodal` returns ONLY the distinct `sat_*` theorem
      occurrences (Satisfies.lean and its consumers) — no `def`/docstring hits remain.

**Timing**: 0.3 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Theorems.lean` — 2 def renames + 1 docstring cross-ref.
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` — 1 docstring ref (name + namespace prefix).
- `Cslib/Logics/Temporal/Syntax/Formula.lean` — 1 docstring ref.

**Verification**:
- `lake build Cslib.Logics.Temporal.Theorems` — green.
- `lake build Cslib.Logics.Bimodal.Embedding.TemporalEmbedding` — green.
- `lake lint 2>&1 | grep -E "Temporal/(Syntax|Semantics|ProofSystem|Metalogic|Theorems)|TemporalEmbedding"`
  — expect ZERO lines (both `defsWithUnderscore` cleared).
- `git diff` shows only identifier renames + doc-comment text (no proof-body / keyword changes,
  no new sorries or axioms).

---

### Phase 2: Optional uniformity rename `hyp_syl` -> `hypSyl` [COMPLETED]

**Goal**: Apply the same "data-returning def = lowerCamelCase" convention to the private helper
`hyp_syl` for uniformity. NON-BLOCKING and DROPPABLE — `hyp_syl` is `private`, so
`defsWithUnderscore` does not fire; skipping this phase does not affect the PR gate. The reviewer
may accept or drop it.

**Tasks**:
- [ ] `Cslib/Logics/Temporal/ProofSystem/Instances.lean:83` — rename `private def hyp_syl`
      -> `private def hypSyl`.
- [ ] Update all 6 internal call sites (lines ~159, 169, 179, 189, 202, 215: `⟨hyp_syl ...⟩`)
      and the comment reference at line ~150 (`... then chain via hyp_syl.`).
- [ ] Sanity grep: `grep -n "hyp_syl" Cslib/Logics/Temporal/ProofSystem/Instances.lean` returns
      zero after the rename.

**Timing**: 0.2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` — 1 def rename + 6 call sites + 1 comment.

**Verification**:
- `lake build Cslib.Logics.Temporal.ProofSystem.Instances` — green.
- `git diff` shows only `hyp_syl` -> `hypSyl` identifier substitutions.

## Testing & Validation

- [x] `lake build` — full build green (no broken references from renames).
- [x] `lake exe checkInitImports` — clean.
- [x] `lake lint` — the two in-scope `defsWithUnderscore` findings gone; no new findings
      (`lake lint` reports "Linting passed for Cslib.").
- [x] `lake exe lint-style` — clean on touched files.
- [x] `lake test` — CslibTests suite green (9180/9180 jobs).
- [x] Zero behavioural change confirmed: no proof-body edits, no `def`->`theorem` conversion,
      no sorries/axioms added (`git diff` is renames + doc text only, verified above).

## Artifacts & Outputs

- Edited: `Cslib/Logics/Temporal/Theorems.lean`,
  `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean`,
  `Cslib/Logics/Temporal/Syntax/Formula.lean`
  (plus, if Phase 2 kept, `Cslib/Logics/Temporal/ProofSystem/Instances.lean`).
- Implementation summary at `summaries/01_*.md` on completion.

## Rollback/Contingency

Pure rename + docs change, fully local. To revert: `git checkout --
Cslib/Logics/Temporal/Theorems.lean Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean
Cslib/Logics/Temporal/Syntax/Formula.lean Cslib/Logics/Temporal/ProofSystem/Instances.lean`.
If `lake build` surfaces an unexpected call site (contradicting the grep verification), add the
corresponding identifier update in the failing file rather than reverting — the rename remains
correct; only an additional reference was missed. Phase 2 can be dropped independently at any
time without affecting the mandatory Phase 1 result.
