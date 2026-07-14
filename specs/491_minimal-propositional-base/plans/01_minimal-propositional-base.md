# Implementation Plan: Task #491

- **Task**: 491 - Minimal propositional base (efq-optional)
- **Status**: [NOT STARTED]
- **Effort**: 0.75 hours
- **Dependencies**: None
- **Research Inputs**: specs/491_minimal-propositional-base/reports/01_minimal-propositional-base.md
- **Artifacts**: plans/01_minimal-propositional-base.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is a **VERIFICATION-ONLY** plan. The research report (`01_minimal-propositional-base.md`)
established that the requested deliverable — an efq-optional propositional base with a clean
`minimal ⊂ intuitionistic ⊂ classical` strength hierarchy — **already exists in full on `main`**
and builds green (638 jobs). efq is already optional in BOTH propositional proof systems: the
Natural Deduction layer gates the `efq` constructor on `[IsIntuitionistic T]`, and the Hilbert
layer parameterizes `DerivationTree` over an axiom predicate (`MinPropAxiom ⊂ IntPropAxiom ⊂
PropositionalAxiom`). The `IsMinimal`/`IsIntuitionistic`/`IsClassical` markers and the
`MinimalHilbert ⊂ IntuitionisticHilbert ⊂ ClassicalHilbert` typeclass chain are all present.

Therefore this plan introduces **zero new proof obligations and zero new definitions**. It
confirms that the existing minimal-base regression (`min_consistent : ¬ Derivable MinPropAxiom ⊥`)
and the efq-gating infrastructure compile, and optionally records a short cross-reference doc note.
Per the zero-debt / reuse-first policy, the implementer MUST NOT create a new `IsMinimal` marker,
an efq-free `Derivation` clone, or any duplicate definition — the research explicitly warns this
would violate reuse-first and there is no implementation gap to close.

### Research Integration

Key findings driving this plan (from the report):
- **No implementation gap** (report Section 5–6). The design is realized three independent,
  green ways: Hilbert axiom predicate, bundled typeclass, and ND theory + gated rule.
- **Operational efq-free witness**: `min_consistent : ¬ Derivable MinPropAxiom ⊥` at
  `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean:219` is the existing lemma proving the
  minimal base is genuinely explosion-free. It builds today.
- **`requires_user_review: true`** was flagged in the research metadata. This plan is the
  "verification + documentation only" deliverable described in report Section 6, option 2; it does
  not resolve the open question of whether task 491 should ultimately be closed as
  already-satisfied — that remains a user decision noted in Rollback/Contingency.
- **No Mathlib lemmas needed** (report Section 5): nothing new is imported or proved.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path provided). Task 491 is noted in TODO.md as a
PREREQUISITE for the minimal modal track (task referencing 491/480/490); confirming the minimal
base compiles green protects that downstream track.

## Goals & Non-Goals

**Goals**:
- Confirm the existing minimal-base infrastructure compiles green (no regression).
- Confirm the existing regression lemma `min_consistent` (efq-free consistency of `MinPropAxiom`)
  builds.
- Optionally record a short doc note cross-linking the three existing encodings, and confirm the
  full CSLib CI pipeline stays green.

**Non-Goals**:
- Creating any new `IsMinimal` marker, `IsMinimal`-style typeclass, or strength predicate
  (already exists at `Equivalence.lean:189`).
- Creating an efq-free `Derivation`/`DerivationTree` clone or any duplicate inductive.
- Adding any new axiom, constructor, instance, or lemma with proof content.
- Any change to proof logic anywhere in `Cslib/Logics/Propositional/`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Implementer manufactures redundant `IsMinimal`/efq-free clone despite instructions | H | L | Non-Goals + explicit prohibition; verification-only phase tasks contain no "create" step |
| A dependency drift since research makes a target module fail to build | M | L | Phase 1 build is the detector; if it fails, treat as a genuine (separate) regression and report, do not "fix" by adding new definitions |
| Doc note edits introduce a doc-build/style-lint failure | L | L | Phase 2 re-runs the CI pipeline after the note; keep note to comment/docstring text only |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Verify Existing Minimal-Base Infrastructure Compiles [COMPLETED]

**Goal**: Confirm, with no source changes, that the existing efq-optional minimal-base
infrastructure and its efq-free regression lemma build green.

**Tasks**:
- [x] Build the minimal-base modules and their key dependents:
      `lake build Cslib.Logics.Propositional.Metalogic.MinLindenbaum Cslib.Logics.Propositional.ProofSystem.IntMinInstances Cslib.Logics.Propositional.NaturalDeduction.Basic Cslib.Logics.Propositional.NaturalDeduction.Equivalence`
      -- Result: "Build completed successfully (729 jobs)."
- [x] Confirm the regression lemma exists and type-checks: `min_consistent`
      (`¬ Derivable MinPropAxiom ⊥`) at
      `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean:219`. Use `lean_verify` /
      `lean_goal` or a targeted build; do NOT edit the file.
      -- Confirmed via `lean_verify Cslib.Logic.PL.min_consistent`: axioms = `propext`,
      `Classical.choice`, `Quot.sound` (standard Mathlib set, no `sorryAx`); no `sorry` in file
      (grep confirmed).
- [x] Spot-confirm efq gating is intact (read-only): the ND `efq` constructor carries
      `[IsIntuitionistic T]` at `NaturalDeduction/Basic.lean:182`, and no `HasAxiomEFQ` instance is
      registered for `HilbertMin` in `ProofSystem/IntMinInstances.lean`.
      -- Confirmed by direct read: line 182 has `[IsIntuitionistic T]` on `efq`; grep of
      `IntMinInstances.lean` shows `HasAxiomEFQ Propositional.HilbertInt` (line 67) only --
      the `HilbertMin` instance block (lines 107-164) has no EFQ instance.
- [x] Record the observed build result (job count, success/fail) for the summary.
      -- 729 jobs, success.

**Timing**: 0.5 hours (dominated by `lake build` on already-cached modules)

**Depends on**: none

**Files to modify**:
- None. This phase is read-only / build-only.

**Verification**:
- All four `lake build` targets report success.
- `min_consistent` type-checks without `sorry` and without new axioms
  (`lean_verify Cslib.Logics.Propositional.Metalogic.min_consistent` shows no unexpected axioms).
- efq gating observations match the research report (`[IsIntuitionistic T]` present; no
  `HilbertMin` EFQ instance).

---

### Phase 2: Documentation Note and Full CI Confirmation [NOT STARTED]

**Goal**: Optionally record a brief cross-reference note pointing at the three existing encodings,
and confirm the full CSLib CI pipeline stays green. This phase is OPTIONAL — if the implementer
judges a doc note redundant with existing module docstrings, it may add nothing and simply run CI.

**Tasks**:
- [ ] (Optional) Add a short doc/comment note — in the module docstring of
      `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (which already hosts the
      `minimal`/`IsMinimal` API) or `Defs.lean` header — cross-linking the three encodings of the
      strength hierarchy: Hilbert axiom predicate (`ProofSystem/Axioms.lean`), bundled typeclass
      (`Foundations/Logic/ProofSystem.lean`), and ND gated rule (`NaturalDeduction/Basic.lean`).
      Docstring/comment text only; no code, no new declarations.
- [ ] Run the CSLib CI pipeline and confirm green:
      `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
      `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] If the doc note was added, confirm `lint-style` and `checkInitImports` still pass with the
      edited file.

**Timing**: 0.25 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (docstring only, OPTIONAL) -
  add cross-reference note to the three encodings. No code changes.

**Verification**:
- Full CI pipeline is green (all five commands succeed).
- Any doc note is comment/docstring text only; `git diff` shows zero changes to declarations,
  tactics, or proof terms.

---

## Testing & Validation

- [ ] `lake build` of all four Phase 1 targets succeeds.
- [ ] `min_consistent` type-checks (no `sorry`, no unexpected axioms).
- [ ] Full CI pipeline green: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
      `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] `git diff` confirms zero new declarations and zero proof-logic changes (docstring-only diff,
      or empty diff if Phase 2 note is skipped).

## Artifacts & Outputs

- Verification summary (build results, confirmation that `min_consistent` and efq-gating compile).
- (Optional) A docstring cross-reference note in `Equivalence.lean`.
- No new Lean definitions, lemmas, or instances.

## Rollback/Contingency

- This plan makes at most a docstring-only edit. If the optional Phase 2 note causes any CI
  failure, revert that single edit (`git checkout -- <file>`); Phase 1 alone then satisfies the
  verification goal with a zero-diff outcome.
- **User-review flag**: Research set `requires_user_review: true` and recommended (option 1)
  marking task 491 `[BLOCKED]` for user review as an outdated tracking task, since its objective
  was completed by prior tasks (185/187/191/367/409) on the #648 lineage. This plan implements the
  alternative verification-only deliverable (option 2). If, after Phase 1 confirms the base is
  green, the user prefers to close 491 as already-satisfied rather than land a doc note, Phase 2
  may be skipped entirely and the task routed to user review instead of `/implement`.
- If Phase 1 build unexpectedly fails, do NOT close the gap by adding new definitions — capture it
  as a distinct regression for a separate fix task and stop.
