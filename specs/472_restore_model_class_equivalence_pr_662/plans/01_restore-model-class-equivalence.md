# Implementation Plan: Restore model-class-parametric Proposition.Equiv and LogicalEquivalence framework integration (PR #662)

- **Task**: 472 - Restore model-class-parametric Proposition.Equiv and LogicalEquivalence framework integration (PR #662)
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None (single-file logic change; open PR #662 context)
- **Research Inputs**: reports/01_restore-model-class-equivalence.md
- **Artifacts**: plans/01_restore-model-class-equivalence.md (this file)
- **Standards**: .claude/rules/artifact-formats.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

PR #662 refactored the Modal formula primitives to `{atom, bot, imp, box}` and, as an incidental
side effect in `Cslib/Logics/Modal/LogicalEquivalence.lean`, replaced Fabrizio Montesi's
model-class-parametric `Proposition.Equiv (S : Set (Model World Atom))` and its integration with
the shared `Cslib.Logic.Modal` `LogicalEquivalence` framework with a standalone,
all-models-hardwired `LogicallyEquivalent` definition (landed on local `main` via task 137,
commit `a084f9f2`). This plan restores the parametric equivalence and framework integration in
**hybrid form** (Option A): keep #662's `{atom, bot, imp, box}` primitives and its
`{hole, impL, impR, box}` `Proposition.Context`/`fill`, and re-add the parametric `Equiv S`,
notation, lemmas, `IsEquiv`/`Congruence` instances, judgemental contexts, and the
`LogicalEquivalence` framework instance. The definition of done: the single file compiles with
zero debt (no `sorry`, no new axioms), `LogicallyEquivalent` is dropped in favor of `≡`/`≡[S]`,
the full CSLib CI pipeline passes, and downstream users of the file still compile.

### Research Integration

This plan integrates `reports/01_restore-model-class-equivalence.md` (cslib-research-agent,
2026-07-02), which supplies the complete API sketch, a reuse check confirming HML and CLL still
instantiate the framework, an Option Evaluation, and a Mathematical Elegance & Consistency
Rationale. All three design decisions are locked by the user: (1) Option A hybrid restore over
the existing `{atom,bot,imp,box}` primitives and `{hole,impL,impR,box}` Context; (2) drop
`LogicallyEquivalent` entirely (no abbrev), standardize on `≡`/`≡[S]`; (3) fix `World` as a
section variable, dropping the standalone's `∀ (World : Type v)` universe-polymorphic quantifier.
These are NOT re-litigated here.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (roadmap_flag=false).

## Goals & Non-Goals

**Goals**:
- Re-add `public import Cslib.Foundations.Logic.LogicalEquivalence` (removed by #662).
- Define parametric `Proposition.Equiv (S : Set (Model World Atom))` over a fixed `World` section variable, with scoped notation `≡[S]` and `≡ := Equiv Set.univ`.
- Restore `equiv_def`, `equiv_iff` (`@[scoped grind =]`), and the `equiv_valid` bridge.
- Restore `HasContext`, `IsEquiv`, and `Congruence` instances, porting the existing standalone congruence proof content into the `Congruence.elim`/`CovariantClass` shape for cases `hole`/`impL`/`impR`/`box`.
- Restore `Satisfies.Context` + `Satisfies.Context.fill` + `HasHContext` judgemental-context instance.
- Restore the `LogicalEquivalence (Proposition Atom) (Judgement World Atom) Satisfies.Bundled` framework instance with `eqv := Equiv Set.univ` and `eqvFillValid`.
- Remove `LogicallyEquivalent` entirely; update any in-file references.
- Pass the full CSLib CI pipeline with zero debt.

**Non-Goals**:
- Re-litigating the locked design decisions (Option A, drop `LogicallyEquivalent`, fixed `World`).
- Changing the `{atom, bot, imp, box}` primitives or the `{hole, impL, impR, box}` Context introduced by #662.
- Modifying files other than `Cslib/Logics/Modal/LogicalEquivalence.lean` (except as forced by downstream compile fixes, which are unexpected per the no-external-users finding).
- Retaining a `LogicallyEquivalent` abbrev.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Target branch/working state ambiguity (edits touch open PR #662 branch `feat/modal-formula-primitives`; local `main` already has the standalone) | H | M | Phase 1 explicitly confirms the target branch/working tree via `git status`/`git branch` and user/context intent before any edit; do not assume |
| Hidden external users of `LogicallyEquivalent` break on removal | M | L | Phase 1 re-runs `git grep LogicallyEquivalent` to confirm no external users (research already showed none) |
| `equivalence_iff_isEquiv` Mathlib lemma name/signature drift since fork point | M | L | Phase 3 verifies with `lean_local_search`/`lean_hover_info` before relying on it |
| `Congruence.elim` box case proof does not port cleanly to new `box` constructor | M | M | Proof content already solved in standalone `congruence` (lines 63-81); use `Satisfies.box_iff_forall` (`Basic.lean:116`) and `Satisfies.iff_iff_iff`; test tactics with `lean_multi_attempt` |
| Universe handling of `Equiv S` over fixed `World` conflicts with downstream expecting universe-polymorphic form | M | L | Fixed `World` is the locked, standard framing; downstream has no external `LogicallyEquivalent` users |
| Notation policy / docBlame violations (missing docstrings, unscoped notation) | L | M | Phase 5 checks docstrings on all restored declarations (port verbatim from diff `-` side) and confirms all notation is `scoped` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is a linear chain: each phase
depends on the prior because the restored declarations build on one another (notation and lemmas
need the definition; instances need the notation/lemmas; the framework instance needs the
instances; CI needs the complete file).

### Phase 1: Confirm target state and re-verify anchors [NOT STARTED]

**Goal**: Establish the correct branch/working tree to edit, confirm no external
`LogicallyEquivalent` users, and read the current file plus all verify-at-implementation anchors
so subsequent phases edit from ground truth.

**Tasks**:
- [ ] Run `git status` and `git branch --show-current` to record the working state.
- [ ] Determine whether implementation happens on `main` (which already holds the standalone version from commit `a084f9f2`) or requires checking out PR branch `feat/modal-formula-primitives`. Do NOT assume; confirm the target explicitly from working-tree state and task intent, and record the decision.
- [ ] Re-run `git grep -n "LogicallyEquivalent"` to confirm there are no external users outside `Cslib/Logics/Modal/LogicalEquivalence.lean` (research reported none).
- [ ] Read the current `Cslib/Logics/Modal/LogicalEquivalence.lean` in full (standalone: Context lines 39-47, fill 50-54, `LogicallyEquivalent` 58-59, congruence 63-81).
- [ ] Confirm anchors via lean-lsp (`lean_hover_info`/`lean_local_search`): `Cslib/Foundations/Logic/LogicalEquivalence.lean:20` (framework class), `:33` (`≡` notation); `Cslib/Foundations/Syntax/Context.lean` and `Congruence.lean` (`HasContext`/`HasHContext`/`Congruence`); `Cslib/Logics/Modal/Basic.lean:205` (`Satisfies.Bundled`), `:209` (`HasInferenceSystem`), `:443` (parametric `Proposition.valid`), `:116` (`Satisfies.box_iff_forall`).
- [ ] Skim the two surviving framework instances as reference patterns: `Cslib/Logics/HML/LogicalEquivalence.lean:105` and `Cslib/Logics/LinearLogic/CLL/Basic.lean:653`.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- None (read-only investigation phase).

**Verification**:
- Target branch/working-tree decision recorded with rationale.
- `git grep` output confirms no external `LogicallyEquivalent` users (or lists any found for handling in Phase 4).
- All anchor line references confirmed to match current sources (note any drift).

---

### Phase 2: Add parametric Equiv S, notation, and core lemmas [NOT STARTED]

**Goal**: Re-add the framework import, the parametric `Proposition.Equiv S` definition over the
fixed `World` section variable, the scoped notation, and the `equiv_def`/`equiv_iff`/`equiv_valid`
lemmas.

**Tasks**:
- [ ] Add `public import Cslib.Foundations.Logic.LogicalEquivalence` at the top of the file (removed by #662).
- [ ] Add `def Proposition.Equiv (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom) : Prop := ∀ m ∈ S, ∀ w : World, ⇓Modal[m,w ⊨ φ₁ ↔ φ₂]` over the ambient `World` section variable (do NOT quantify `∀ World : Type v`).
- [ ] Add scoped notation `≡[S]` (`Proposition.Equiv S`) and `≡` (`Proposition.Equiv Set.univ`), both `scoped` under `namespace Cslib.Logic.Modal`, with `@[inherit_doc]`.
- [ ] Add `@[scoped grind =] theorem Proposition.equiv_def` (by `rfl`) and `@[scoped grind =] theorem Proposition.equiv_iff` (via `Proposition.equiv_def` + `Satisfies.iff_iff_iff`).
- [ ] Add `theorem Proposition.equiv_valid (S) (φ₁ φ₂) (h : φ₁ ≡[S] φ₂) : φ₁.valid S ↔ φ₂.valid S` (bridge to parametric `Proposition.valid`).
- [ ] Port docstrings verbatim from the PR #662 diff `-` side for each restored declaration.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/LogicalEquivalence.lean` - add import, `Equiv` def, notation, `equiv_def`/`equiv_iff`/`equiv_valid`.

**Verification**:
- `lean_diagnostic_messages` shows no errors on the added declarations.
- `equiv_valid` typechecks against `Proposition.valid` (`Basic.lean:443`).
- No `sorry`, no new axioms introduced.

---

### Phase 3: Restore HasContext, IsEquiv, and Congruence instances [NOT STARTED]

**Goal**: Re-add the `HasContext` instance and the `IsEquiv` and `Congruence` instances, porting
the already-solved standalone congruence proof content into the `Congruence.elim`/`CovariantClass`
shape for the `{hole, impL, impR, box}` context constructors.

**Tasks**:
- [ ] Add `instance : HasContext (Proposition Atom) := ⟨Proposition.Context Atom, Proposition.Context.fill⟩` (reuse the existing `{hole, impL, impR, box}` Context/fill from #662).
- [ ] Verify `equivalence_iff_isEquiv` exists and its signature via `lean_local_search`/`lean_hover_info`.
- [ ] Add `instance (S : Set (Model World Atom)) : IsEquiv (Proposition Atom) (Proposition.Equiv S)` using `rw [← equivalence_iff_isEquiv]; grind [Equivalence]`.
- [ ] Add `instance (S : Set (Model World Atom)) : Congruence (Proposition Atom) (Proposition.Equiv S)` with `elim` doing induction on the context: `case hole`, `case impL`/`case impR` (via IH), `case box` (via `Satisfies.box_iff_forall` `Basic.lean:116` + `Satisfies.iff_iff_iff`).
- [ ] Port the congruence proof content from the current standalone `LogicallyEquivalent.congruence` (lines 63-81), re-expressing it under the `Congruence.elim` shape; test tactic candidates with `lean_multi_attempt` before writing.

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/LogicalEquivalence.lean` - add `HasContext`, `IsEquiv`, `Congruence` instances.

**Verification**:
- `lean_diagnostic_messages` shows no errors; `lean_goal` confirms "no goals" at end of `Congruence.elim` for all four cases.
- `IsEquiv` instance resolves (enables `≡` as an equivalence relation).
- No `sorry`, no new axioms.

---

### Phase 4: Restore judgemental context and framework instance; remove LogicallyEquivalent [NOT STARTED]

**Goal**: Re-add `Satisfies.Context`/`fill` + `HasHContext` judgemental-context instance and the
`LogicalEquivalence` framework instance, then remove `LogicallyEquivalent` and update any in-file
references to `≡`/`≡[S]`.

**Tasks**:
- [ ] Add `structure Satisfies.Context (World Atom : Type*)` with fields `m : Model World Atom`, `w : World`.
- [ ] Add `def Satisfies.Context.fill (c) (φ) : Judgement World Atom := Modal[c.m, c.w ⊨ φ]`.
- [ ] Add `instance judgementalContext : HasHContext (Judgement World Atom) (Proposition Atom)` wiring `Satisfies.Context`/`fill`.
- [ ] Add `instance : LogicalEquivalence (Proposition Atom) (Judgement World Atom) Satisfies.Bundled` with `eqv := Proposition.Equiv Set.univ` and `eqvFillValid heqv c h := by specialize heqv c.m; grind`.
- [ ] Remove the standalone `def LogicallyEquivalent` and `theorem LogicallyEquivalent.congruence` (superseded by the `Congruence` instance).
- [ ] Update any remaining in-file references from `LogicallyEquivalent` to `≡`/`≡[S]`; handle any external references found in Phase 1 (research indicates none).
- [ ] Port docstrings verbatim for the restored declarations.

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/LogicalEquivalence.lean` - add `Satisfies.Context`/`fill`/`HasHContext`/`LogicalEquivalence` instance; remove `LogicallyEquivalent` and its congruence theorem.

**Verification**:
- `lean_diagnostic_messages` shows no errors; the `LogicalEquivalence` instance resolves against `Satisfies.Bundled` (`Basic.lean:205`).
- `git grep "LogicallyEquivalent"` returns no matches anywhere in the tree.
- No `sorry`, no new axioms.

---

### Phase 5: Full CI pipeline, downstream compile, and zero-debt/standards check [NOT STARTED]

**Goal**: Run the complete CSLib CI pipeline, confirm downstream users compile, and verify
zero-debt and standards (docstrings, notation policy) compliance.

**Tasks**:
- [ ] Run `lake build` (whole-tree build; confirms the changed file and all downstream users compile, including `Modal/Cube` and anything importing `Modal/LogicalEquivalence`).
- [ ] Run `lake test` (CslibTests suite).
- [ ] Run `lake exe checkInitImports`.
- [ ] Run `lake exe lint-style`.
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Confirm zero debt: `git grep -n "sorry"` in the file returns nothing; run `lean_verify` on the framework instance and key theorems to confirm no new axioms.
- [ ] Confirm every restored declaration has a docstring (docBlame) and that all notation is `scoped` under `Cslib.Logic.Modal` (Notation Policy).
- [ ] Explicitly verify downstream files that import `Modal/LogicalEquivalence` (notably `Cslib/Logics/Modal/Cube.lean`) build.

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- None expected (verification phase; fix-forward only if CI surfaces issues).

**Verification**:
- All five CI pipeline commands exit successfully.
- No `sorry`, no new axioms (confirmed by `lean_verify`).
- All restored declarations carry docstrings; all notation scoped.
- Downstream users (`Modal/Cube`, importers) compile.

---

## Testing & Validation

The CSLib CI pipeline (all must pass):
- [ ] `lake build` - whole-tree build including downstream users of `Modal/LogicalEquivalence`.
- [ ] `lake test` - CslibTests suite.
- [ ] `lake exe checkInitImports` - verify `Cslib.Init` imports.
- [ ] `lake exe lint-style` - style linting.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` - dependency analysis.

Additional validation:
- [ ] Zero debt: no `sorry`, no new axioms (`lean_verify` on the framework instance and theorems).
- [ ] Standards: docstrings on all restored declarations; all notation `scoped`; `≡`/`≡[S]` only (no `LogicallyEquivalent`).
- [ ] Downstream compile: `Cslib/Logics/Modal/Cube.lean` and any importer of `Modal/LogicalEquivalence` build.

## Artifacts & Outputs

- `Cslib/Logics/Modal/LogicalEquivalence.lean` - restored parametric `Proposition.Equiv S`, notation, lemmas, `HasContext`/`IsEquiv`/`Congruence`/`HasHContext`/`LogicalEquivalence` instances; `LogicallyEquivalent` removed.
- `specs/472_restore_model_class_equivalence_pr_662/plans/01_restore-model-class-equivalence.md` - this plan.
- Execution summary (produced by `/implement`): `specs/472_restore_model_class_equivalence_pr_662/summaries/01_restore-model-class-equivalence-summary.md`.

## Rollback/Contingency

The change is confined to a single file, `Cslib/Logics/Modal/LogicalEquivalence.lean`. If
implementation fails or CI cannot be made green with zero debt, revert the file with
`git checkout -- Cslib/Logics/Modal/LogicalEquivalence.lean` (or `git restore` to the pre-task
state) to return to the standalone `LogicallyEquivalent` version currently on `main`. Because no
external files are modified (no external `LogicallyEquivalent` users), reverting the single file
fully restores the prior working state. If a specific phase blocks (e.g., the `Congruence.elim`
box case or `equivalence_iff_isEquiv` drift), mark the phase [PARTIAL] with notes and preserve the
completed earlier phases; the linear dependency chain means later phases simply wait.
