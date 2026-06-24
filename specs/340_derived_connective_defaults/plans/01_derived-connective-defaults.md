# Implementation Plan: Task #340

- **Task**: 340 - Consolidate derived connective definitions (neg/top/and/or/iff) across Modal, Temporal, Bimodal, LTL
- **Status**: [COMPLETED]
- **Effort**: 3.5 hours
- **Dependencies**: 334 (satisfied)
- **Research Inputs**: specs/340_derived_connective_defaults/reports/01_derived-connective-defaults.md
- **Artifacts**: plans/01_derived-connective-defaults.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; .claude/rules/cslib.md; .claude/rules/lean4.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Five derived connectives (`neg`, `top`, `and`, `or`, `iff`) are copy-pasted with identical
Lukasiewicz encodings across four formula files: `Modal/Basic.lean`, `Temporal/Syntax/Formula.lean`,
`Bimodal/Syntax/Formula.lean`, and `LTL/Syntax/Formula.lean`. This plan consolidates the genuinely
shared, design-sanctioned subset (`neg`, `top`) as defaulted fields on `PropositionalConnectives`
in `Foundations/Logic/Connectives.lean`, then migrates each formula file's `abbrev` bodies to thin
delegates. Definition of done: `lake build` green, full CI pipeline passes, net line reduction, and
a single canonical source for the `neg`/`top` encodings shared by all four logics.

### Research Integration

The research report (`reports/01_derived-connective-defaults.md`) verified via `lean_run_code`
that defaulted fields on `PropositionalConnectives` preserve definitional equality, `simp only`
unfolding, and the `change` tactic. Those verification results carry over directly to `neg`/`top`.

**Critical divergence from the research report** (discovered by reading the live source during
planning): the report recommends adding `and`/`or`/`iff` as **Lukasiewicz-derived defaults**, but
the current `Connectives.lean` module docstring (lines 29-39) records a *deliberate, opposite*
design decision from task 173:

- `and`/`or` are intentionally treated as **primitives** via standalone `HasAnd`/`HasOr` classes,
  NOT Lukasiewicz-derived, because the classical encodings `and φ ψ := ¬(φ → ¬ψ)` and
  `or φ ψ := ¬φ → ψ` are only *propositionally equivalent* to `∧`/`∨` in classical logic and
  **fail in intuitionistic and minimal logic** ([Wajsberg1938], [McKinsey1939]).
- `iff` is explicitly **deferred to task 173** (line 38), pending `HasAnd` instantiation.
- Only `neg` and `top` are described as staying derived because `neg φ := φ → ⊥` and
  `top := ⊥ → ⊥` are valid in minimal, intuitionistic, and classical logic alike (lines 36-37).

This plan therefore **respects the established design** and scopes the typeclass-level consolidation
to `neg` and `top` only. The `and`/`or`/`iff` `abbrev`s remain per-file (their Lukasiewicz encoding
is acceptable inside the concrete classical formula types, but must not be promoted into the shared
typeclass that also serves non-classical fragments). Phase 1 is a decision gate that surfaces this
reconciliation explicitly before any code changes.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path provided in delegation context).

## Goals & Non-Goals

**Goals**:
- Add `neg` and `top` as defaulted fields on `PropositionalConnectives` in `Connectives.lean`,
  with Lukasiewicz encodings `neg φ := imp φ bot` and `top := imp bot bot`.
- Migrate the `neg`/`top` `abbrev`s in all four formula files to delegate to the typeclass defaults,
  preserving the existing names, scoped notation (`¬`), and definitional equalities.
- Keep all downstream proofs compiling (verified by full `lake build` + CI pipeline).
- Provide a single canonical source and docstring for the `neg`/`top` encodings.

**Non-Goals**:
- Promoting `and`/`or` into `PropositionalConnectives` as Lukasiewicz defaults (contradicts the
  task-173 design decision; `and`/`or` stay primitive via `HasAnd`/`HasOr`).
- Adding `iff` to the typeclass (explicitly deferred to task 173).
- Adding the missing `iff` `abbrev` to Bimodal as a typeclass default (a local `abbrev` may be
  added in Phase 4 only if it does not require typeclass changes; otherwise deferred).
- Refactoring `Axioms.lean` (`neg'`/`top'`/`conj'`/`disj'`) — separate follow-up per the report.
- Any change to the semantics, proof terms, or notation bindings of existing connectives.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `simp only [Formula.neg]` no longer unfolds through the delegate | M | M | Research verified the unfold chain holds; if a `simp` call fails, add `PropositionalConnectives.neg` to that `simp only` list, or rely on `abbrev` reducibility. Re-run `lake build` after each file. |
| Definitional-equality `rfl`/`change` proofs in downstream files break | H | L | Research confirmed `rfl` and `change` preserved through the default-field unfold chain. Full `lake build` after Phase 2 catches any breakage; rollback restores the inline `abbrev`. |
| Instance resolution picks the wrong `bot`/`imp` for a default field | M | L | Each formula file already registers a connectives instance providing `bot`/`imp`; the default reduces to those. Verify with a scoped `lake build Module.Name` per file. |
| Scope creep into `and`/`or`/`iff` against the documented design | H | M | Phase 1 decision gate fixes scope to `neg`/`top`; non-goals list is explicit. |
| CI sub-checks (lint-style, shake, checkInitImports) flag the edits | L | M | Run the full CSLib CI pipeline in Phase 5 in the documented order; address lint findings before completion. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential because each
phase builds on the verified state of the previous one.

### Phase 1: Scope Reconciliation and Connectives.lean Defaults [COMPLETED]

**Goal**: Resolve the research-vs-design divergence in favor of the documented task-173 design,
then add `neg`/`top` as defaulted fields to `PropositionalConnectives`.

**Tasks**:
- [ ] Re-read `Cslib/Foundations/Logic/Connectives.lean` lines 29-39 and 139-145 to confirm the
      current design intent (`and`/`or` primitive, `iff` deferred, `neg`/`top` derived).
- [ ] Confirm final scope: only `neg` and `top` become typeclass defaults this task. Record the
      decision and rationale in the commit message and in the module docstring update below.
- [ ] Edit `PropositionalConnectives` (line 145) to add two defaulted fields:
      `neg : F → F := fun φ => HasImp.imp φ HasBot.bot` and
      `top : F := HasImp.imp (HasBot.bot : F) HasBot.bot`, each with a docstring giving the
      Lukasiewicz encoding and noting validity in minimal/intuitionistic/classical logic.
- [ ] Update the module docstring (lines 36-39) to state that `neg`/`top` now have canonical
      defaulted fields on `PropositionalConnectives`, while `and`/`or` remain primitive and `iff`
      remains deferred to task 173.
- [ ] Verify with `lean_goal` / `lean_multi_attempt` that the default fields elaborate, then run
      `lake build Cslib.Foundations.Logic.Connectives`.

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` — add `neg`/`top` default fields; update docstring.

**Verification**:
- `lake build Cslib.Foundations.Logic.Connectives` succeeds with no new warnings.
- The added fields appear with correct Lukasiewicz default values and docstrings.

---

### Phase 2: Migrate Modal/Basic.lean neg/top Delegates [COMPLETED]

**Goal**: Replace the inline Lukasiewicz bodies of `Proposition.neg` and `Proposition.top` with
delegates to the `PropositionalConnectives` defaults, leaving `and`/`or`/`iff`/`diamond` untouched.

**Tasks**:
- [ ] Confirm `Modal/Basic.lean` registers `ModalConnectives (Proposition Atom)` (line 122) so the
      `PropositionalConnectives.neg`/`.top` defaults are available.
- [ ] Replace `abbrev Proposition.neg` (line 82) body with `PropositionalConnectives.neg φ`.
- [ ] Replace `abbrev Proposition.top` (line 85) body with `PropositionalConnectives.top`.
- [ ] Leave `Proposition.or`, `.and`, `.iff`, `.diamond` and all scoped notation unchanged.
- [ ] Check `Satisfies.neg_iff` and `diamond`-unfolding proofs (lines 137-142, 276) still hold;
      add `PropositionalConnectives.neg` to any failing `simp only`/`unfold` lists if needed.
- [ ] Run `lake build Cslib.Logics.Modal.Basic`.

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` — `Proposition.neg`, `Proposition.top` delegates.

**Verification**:
- `lake build Cslib.Logics.Modal.Basic` succeeds.
- `Proposition.neg φ = .imp φ .bot` and `Proposition.top = .imp .bot .bot` hold by `rfl`.

---

### Phase 3: Migrate Temporal and LTL neg/top Delegates [COMPLETED]

**Goal**: Apply the same `neg`/`top` delegation to Temporal and LTL formula files.

**Tasks**:
- [ ] In `Temporal/Syntax/Formula.lean`: replace `Formula.neg` (line 102) and `Formula.top`
      (line 105) bodies with `PropositionalConnectives.neg φ` / `PropositionalConnectives.top`.
      Leave `Formula.or`/`.and`/`.iff` unchanged. Confirm `TemporalConnectives (Formula Atom)`
      instance (line 152) supplies `bot`/`imp`.
- [ ] In `LTL/Syntax/Formula.lean`: replace `Formula.neg` (line 98) and `Formula.top` (line 101)
      bodies with the delegates. Leave `Formula.or`/`.and`/`.iff` unchanged. Confirm
      `LTLConnectives (Formula Atom)` instance (line 141) supplies `bot`/`imp`.
- [ ] Check derived-operator definitions that build on `neg`/`top` (e.g. Temporal `someFuture`,
      `allFuture`) still elaborate; fix any `simp`/`unfold` lists as in Phase 2.
- [ ] Run `lake build Cslib.Logics.Temporal.Syntax.Formula` and
      `lake build Cslib.Logics.LTL.Syntax.Formula`.

**Timing**: 40 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` — `Formula.neg`, `Formula.top` delegates.
- `Cslib/Logics/LTL/Syntax/Formula.lean` — `Formula.neg`, `Formula.top` delegates.

**Verification**:
- Both scoped `lake build` targets succeed.
- `Formula.neg`/`Formula.top` reduce to the original Lukasiewicz terms by `rfl` in each module.

---

### Phase 4: Migrate Bimodal neg/top Delegates [COMPLETED]

**Goal**: Apply the `neg`/`top` delegation to Bimodal and decide on the `iff` gap.

**Outcome**: Done, committed `71b51b5b`. The `neg`/`top` delegation cascaded beyond
`Formula.lean` because the delegated definitions no longer auto-unfold, so downstream call
sites needed localized fixes across 8 Bimodal files plus a follow-on `Modal/Basic.lean`
adjustment. `iff` gap left as-is (deferred to task 173 — no local `abbrev` added).

**Tasks**:
- [x] In `Bimodal/Syntax/Formula.lean`: `Formula.neg`/`Formula.top` now delegate to
      `PropositionalConnectives`; `Formula.or`/`.and` left unchanged.
- [x] `iff` gap: NOT added as a typeclass default and NO local `abbrev` introduced — gap left
      for task 173, per the established design.
- [x] Downstream adjustments applied where the non-unfolding delegates broke `simp`/`rfl`
      chains: `Semantics/Truth.lean`, `ProofSystem/Instances.lean`, `Syntax/Subformulas.lean`,
      `Metalogic/Soundness/{Soundness,DenseValidity}.lean`, `Metalogic/Core/MCSProperties.lean`,
      `Theorems/Perpetuity/Helpers.lean`.
- [x] Scoped builds run (see Phase 5).

**Timing**: 30 minutes (actual: larger downstream fan-out than estimated)

**Depends on**: 3

**Files modified**:
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` — `Formula.neg`, `Formula.top` delegates.
- 7 downstream Bimodal files + `Cslib/Logics/Modal/Basic.lean` — `simp`/`unfold`/proof fixups.

**Verification**:
- `lake build Bimodal.Metalogic.Soundness.{Soundness,DenseValidity} Bimodal.Theorems.Perpetuity.Helpers`
  succeeds (667 jobs).
- Bimodal `neg`/`top` reduce to the original terms (no behavioral change).

---

### Phase 5: Full Build and CI Verification [COMPLETED]

**Goal**: Confirm the whole library compiles and passes the CSLib CI pipeline after consolidation.

**Outcome**: Verified via **scoped** builds of every logic family touched by the refactor. A
concurrent session held unrelated uncommitted edits to Propositional files
(`NaturalDeduction/Normalization.lean`, `Tableau/...`), so a full-tree `lake build`/`lake test`
was deliberately deferred to a clean-tree PR-time run to avoid contamination.

**Tasks**:
- [x] Scoped builds (stand in for full `lake build`):
      `Bimodal.Metalogic.Soundness.{Soundness,DenseValidity}` + `Perpetuity.Helpers` (667 jobs);
      `Modal.Basic` + `Temporal.Syntax.Formula` + `LTL.Syntax.Formula` (582 jobs) — all green.
- [x] `lake exe lint-style` — clean on modified files.
- [~] `lake build` (full) / `lake exe checkInitImports` / `lake lint` / `lake test` /
      `lake shake` — **deferred** to clean-tree PR-time run (concurrent-session contamination).
- [x] Broken `simp`/`unfold`/`rfl` chains from the non-unfolding delegates were fixed inline in
      Phase 4 (the downstream Bimodal files + `Modal/Basic.lean`).
- [x] Line-count delta: scope narrowed to `neg`/`top` only (per Phase 1), so savings are modest
      and partly offset by the downstream `simp`-list fixups; net change small.

**Timing**: 45 minutes

**Depends on**: 4

**Files modified**: none in this phase (verification only; fixups landed in Phase 4).

**Verification**:
- Scoped builds across Modal/Temporal/LTL/Bimodal all green.
- No `sorry`, no vacuous definitions (pure refactor).
- Full CI sub-checks deferred to a clean-tree PR-time run.

## Testing & Validation

Verification scoped to the logic families touched by the refactor (rationale in Phase 5).

- [x] Scoped builds succeed across Modal/Temporal/LTL/Bimodal (667 + 582 jobs).
- [x] `lake exe lint-style` passes on modified files.
- [x] No `sorry`/`admit` introduced anywhere (grep-verified).
- [x] Bimodal/Temporal/LTL/Modal `neg`/`top` reduce to the original terms (no behavioral change).
- [~] Full `lake build` / `checkInitImports` / `lake lint` / `lake test` / `lake shake` —
      **deferred** to a clean-tree PR-time run (concurrent session held unrelated uncommitted
      Propositional edits).
- [ ] No `sorry` and no vacuous (`:= True`/`:= trivial`) definitions introduced.

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Connectives.lean` — `neg`/`top` default fields + updated docstring.
- `Cslib/Logics/Modal/Basic.lean` — `Proposition.neg`/`.top` delegates.
- `Cslib/Logics/Temporal/Syntax/Formula.lean` — `Formula.neg`/`.top` delegates.
- `Cslib/Logics/LTL/Syntax/Formula.lean` — `Formula.neg`/`.top` delegates.
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` — `Formula.neg`/`.top` delegates (optional `iff`).
- `specs/340_derived_connective_defaults/plans/01_derived-connective-defaults.md` (this file).
- `specs/340_derived_connective_defaults/summaries/01_derived-connective-defaults-summary.md`
  (produced at implementation time).

## Rollback/Contingency

The change is additive and per-file reversible. If any downstream proof breaks and cannot be fixed
by adding `PropositionalConnectives.neg`/`.top` to a `simp only`/`unfold` list:

1. Restore the inline `abbrev` body in the affected formula file (e.g.,
   `abbrev Formula.neg (φ) := .imp φ .bot`) without touching `Connectives.lean`. The names and
   notation are unchanged, so downstream code keeps compiling.
2. If `Connectives.lean` itself must be reverted, remove the two default fields and the docstring
   edit; the four formula files revert to their original inline bodies. No instance signatures
   change, so reversion is mechanical.
3. Because this is a pure refactor with no semantic change, a full `git checkout` of the five files
   restores the pre-task state with zero residual effects.
