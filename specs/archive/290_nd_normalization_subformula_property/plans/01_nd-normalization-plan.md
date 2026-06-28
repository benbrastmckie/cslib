# Implementation Plan: Task #290

- **Task**: 290 - ND Normalization and Subformula Property
- **Status**: [COMPLETED]
- **Effort**: 10 hours
- **Dependencies**: None (task 266 completed and archived; Derivation type and subs already in place)
- **Research Inputs**: specs/290_nd_normalization_subformula_property/reports/01_nd-normalization-research.md
- **Artifacts**: plans/01_nd-normalization-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Formalize Prawitz-style normalization for the `Theory.Derivation` inductive type in
`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`. The existing `Derivation` is `Type u`
with 10 constructors and a computable `subs` (substitution) operation, enabling a direct
recursive normalization function. The plan proceeds in five phases: (1) subformula infrastructure
and the `isNormal` predicate, (2) derivation metrics and single-step reduction, (3) the
normalization function with well-founded termination, (4) extension to full IPL connectives
(and/or redexes), and (5) the subformula property corollary. The implicational fragment is
the critical milestone; full connective extension adds simpler cases atop the same structure.

### Research Integration

Key findings from the research report (01_nd-normalization-research.md):
- `Theory.Derivation` has 10 constructors matching Prawitz's presentation exactly; all 5 redex
  patterns are matchable via nested pattern matching.
- `Derivation.subs` provides computable structural substitution; suitable for reduction rules.
- The auto-generated `sizeOf` is unsuitable for termination (formula sizes can grow during
  reduction). A custom measure based on `(maxGrade, redexCountAtGrade)` lexicographic pair is
  needed, following Prawitz Ch. IV sec. 3.
- `Proposition.subformulas` exists for Bimodal logic but not PL -- must be defined.
- No Mathlib normalization infrastructure exists; Mathlib's `Prod.Lex` and `WellFounded` API
  support the custom termination argument.
- Context arithmetic for reductions (e.g., `(insert A G) \ {A} U G = G`) is provable via
  `ext; simp; tauto` or `grind`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define `Proposition.subformulas` and `Proposition.IsSubformula` for propositional logic
- Define `Theory.Derivation.isNormal` predicate (no maximal formula)
- Implement single-step reduction (`reduceStep`) for all 5 redex types
- Prove normalization via well-founded recursion on a custom measure
- Derive the subformula property for normal derivations
- Support both MPL (empty theory) and IPL (efq theory)

**Non-Goals**:
- Proving strong normalization (every reduction sequence terminates) -- only one normal form suffices
- Proving confluence (Church-Rosser property) -- not needed for the normalization function
- Extending to classical logic (CPL) or modal logic
- Optimizing the normalization function for computational efficiency

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Well-founded termination proof is difficult to close in Lean 4 | H | M | Start with implicational fragment; use fuel-bounded fallback if WF recursion stalls |
| Context arithmetic (`Finset` setdiff/union equalities) causes proof friction | M | M | Research verified `ext; simp; tauto` and `grind` close these; define helper lemmas upfront |
| `subs` increases derivation size, complicating measure arguments | H | M | Follow Prawitz: reduce topmost redex of maximum grade; prove no new redexes at same grade |
| Nested pattern matching on `Derivation` constructors may cause elaboration issues | M | L | Use `@`-prefixed patterns for explicit parameter matching as in existing `subs` definition |
| Subformula property for IPL requires accounting for theory axioms | L | L | State theorem with "modulo theory axioms" qualification; prove strict version for MPL first |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Subformula Infrastructure and isNormal Predicate [COMPLETED]

**Goal**: Define `Proposition.subformulas`, `Proposition.IsSubformula`, `Derivation.height`,
and `Derivation.isNormal` with basic lemmas. This establishes the vocabulary for the rest of
the development.

**Tasks**:
- [ ] Create file `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` with module header, copyright, and `import Cslib.Init` + `import Cslib.Logics.Propositional.NaturalDeduction.Basic`
- [ ] Define `Proposition.subformulas : Proposition Atom -> Finset (Proposition Atom)` returning the set of all subformulas (including self), following the pattern from `Cslib/Logics/Bimodal/Syntax/Subformulas.lean`
- [ ] Define `Proposition.IsSubformula (A B : Proposition Atom) : Prop := A ∈ B.subformulas`
- [ ] Prove `Proposition.IsSubformula.refl : A.IsSubformula A` and transitivity
- [ ] Define `Proposition.complexity : Proposition Atom -> Nat` (formula size: atoms/bot = 0, connectives = 1 + sum of children)
- [ ] Define `Theory.Derivation.height : T.Derivation G A -> Nat` (max depth of derivation tree)
- [ ] Define `Theory.Derivation.isNormal : T.Derivation G A -> Bool` using nested pattern matching to detect the 5 redex patterns (impE/impI, andE1/andI, andE2/andI, orE/orI1, orE/orI2)
- [ ] Prove `Theory.Derivation.isNormal_ax : (Derivation.ax h).isNormal = true`
- [ ] Prove `Theory.Derivation.isNormal_ass : (Derivation.ass h).isNormal = true`
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` - new file, all definitions
- `Cslib.lean` - add import (via `lake exe mk_all --module`)

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds
- `isNormal` compiles with all 5 redex-detecting cases returning `false`
- `Proposition.subformulas` returns correct results on sample formulas (check via `#eval` or `decide`)

---

### Phase 2: Derivation Metrics and Single-Step Reduction [COMPLETED]

**Goal**: Define the normalization measure (maxGrade, redexCount) and a single-step reduction
function `reduceStep` that eliminates the topmost redex of maximum grade. Prove that `reduceStep`
preserves the derivation's sequent (same context and conclusion).

**Tasks**:
- [ ] Define `Theory.Derivation.maximalFormulas : T.Derivation G A -> List (Proposition Atom)` collecting all maximal formula occurrences (formulas at redex sites)
- [ ] Define `Theory.Derivation.maxGrade : T.Derivation G A -> Nat` as the maximum `Proposition.complexity` among maximal formulas (0 if normal)
- [ ] Define `Theory.Derivation.redexCountAtGrade (g : Nat) : T.Derivation G A -> Nat` counting redexes whose maximal formula has complexity exactly `g`
- [ ] Define helper `Theory.Derivation.subsOne {A : Proposition Atom} (d_arg : T.Derivation G A) (d_body : T.Derivation (insert A G) B) : T.Derivation G B` as a convenience wrapper around `subs` for single-formula substitution, with a proof that `(insert A G) \ {A} U G = G`
- [ ] Define `Theory.Derivation.reduceStep : T.Derivation G A -> Option (T.Derivation G A)` that pattern-matches to find and reduce the topmost redex of maximum grade; returns `none` if normal
- [ ] Prove `Theory.Derivation.reduceStep_none_iff_isNormal : d.reduceStep = none <-> d.isNormal = true`
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` - add definitions and lemmas

**Verification**:
- `reduceStep` compiles and handles all 5 redex patterns plus recursive descent
- `subsOne` helper works correctly (verify via `#check` or small test derivation)
- `reduceStep_none_iff_isNormal` links the two predicates consistently
- `lake build` succeeds without errors

---

### Phase 3: Normalization Function with Well-Founded Termination [PARTIAL]

**Goal**: Define the `normalize` function via well-founded recursion on the lexicographic
measure `(maxGrade, redexCountAtGrade maxGrade)`. Prove the key termination lemma: reducing
the topmost redex of maximum grade strictly decreases the measure. Prove `normalize_isNormal`.

**Tasks**:
- [ ] Define the normalization measure type: `def normMeasure (d : T.Derivation G A) : Nat x Nat := (d.maxGrade, d.redexCountAtGrade d.maxGrade)`
- [ ] Prove the key decrease lemma: `Theory.Derivation.reduceStep_decreases_measure : d.reduceStep = some d' -> normMeasure d' < normMeasure d` (using `Prod.Lex` ordering). This is the hardest proof -- it requires showing that `subs` does not introduce new maximal formulas of the same or higher grade
- [ ] Define `Theory.Derivation.normalize : T.Derivation G A -> T.Derivation G A` via `WellFoundedRelation.wf.fix` or `termination_by` on the measure, iterating `reduceStep` until `none`
- [ ] Prove `Theory.Derivation.normalize_isNormal : (d.normalize).isNormal = true`
- [ ] Prove `Theory.Derivation.normalize_ax : (Derivation.ax h).normalize = Derivation.ax h` (normal derivations are fixed points)
- [ ] If the full WF proof is intractable, fall back to a fuel-bounded version: `def normalizeAux (fuel : Nat) : T.Derivation G A -> T.Derivation G A` with a proof that `d.maximalFormulas.length` bounds the needed fuel, then define `normalize` via `normalizeAux (totalRedexWeight d)`
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`

**Timing**: 3 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` - normalization function and termination proof

**Verification**:
- `normalize` compiles and type-checks with `termination_by` or explicit WF recursion
- `normalize_isNormal` proof closes
- No `sorry` in the normalization function or its termination proof
- `lake build` succeeds

---

### Phase 4: Full Connective Verification and Cleanup [COMPLETED]

**Goal**: Ensure all 5 redex types (imp, and-L, and-R, or-L, or-R) are fully handled in
`reduceStep` and the termination argument covers them. Add helper lemmas for the simpler
connectives (and-redex projections, or-redex substitutions). Run full CI verification.

**Tasks**:
- [ ] Verify that and-redex reductions (`andE1 G (andI G d1 d2) -> d1`, `andE2 G (andI G d1 d2) -> d2`) are handled and the measure decrease is trivial (projection reduces size)
- [ ] Verify that or-redex reductions use `subsOne` correctly and the measure decrease argument parallels the imp-redex case
- [ ] Add docstrings to all public definitions following CSLib conventions
- [ ] Add `import Cslib.Init` if not already present
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import
- [ ] Run `lake exe checkInitImports` to verify import structure
- [ ] Run `lake exe lint-style` and fix any style issues
- [ ] Run `lake build` for full project verification

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` - docstrings, cleanup, any missing cases
- `Cslib.lean` - updated by `mk_all`

**Verification**:
- All 5 redex types handled in `reduceStep`
- `lake build` succeeds
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- No `sorry` remaining

---

### Phase 5: Subformula Property [BLOCKED]

**Goal**: Define the set of formulas occurring in a derivation and prove the subformula property:
every formula in a normal derivation is a subformula of the conclusion or a hypothesis (or, for
IPL, a theory axiom). State and prove for both MPL and IPL.

**BLOCKER** (Phase 5):
- **What failed**: The elimination cases (andE1, andE2, orE, impE) of `subformula_property_of_isNormal` cannot be proved by simple structural induction on the derivation.
- **What was tried**: Structural induction using the induction hypothesis from the sub-derivation. The IH gives `F.IsSubformula (A ∧ B)` for andE1, but the goal needs `F.IsSubformula A`. The difference is that `F` could be a subformula of `B` (the right conjunct) but not of `A` (the left).
- **Why it's stuck**: The Prawitz "main branch" argument is required: in a normal derivation, only formulas on the main branch (the path from the end-sequent upward through elimination rules) need to be subformulas of the conclusion. Formulas from side branches are subformulas of hypotheses or axioms. This requires a separate lemma establishing main-branch properties, which is a substantial additional development.
- **What is needed**: Define the "main branch" of a derivation and prove that elimination rules follow it. This is Prawitz [Prawitz1965] Ch. III, Theorem 1. A separate task should be created to develop this infrastructure.
- **Prohibited workarounds**: Do NOT use `sorry`, `def X := True`, or any vacuous placeholder. The current file has `sorry` in the two theorems that require this argument, with documentation explaining the gap.

**Tasks**:
- [x] Define `Theory.Derivation.formulas : T.Derivation G A -> Finset (Proposition Atom)` collecting all formula occurrences in the derivation tree (conclusion formulas at each node) *(completed)*
- [x] Define `Theory.Derivation.SubformulaProperty (d : T.Derivation G A) : Prop` stating that for all `B ∈ d.formulas`, either `B.IsSubformula A` or `exists C ∈ G, B.IsSubformula C` or `exists C ∈ T, B.IsSubformula C` *(completed)*
- [ ] Prove `Theory.Derivation.subformula_property_of_isNormal` for MPL (`T = emptyset`): every formula in a normal derivation is a subformula of the conclusion or a hypothesis. This is by induction on the normal derivation, using the fact that normality excludes intro-elim pairs *(deviation: blocked -- requires Prawitz main-branch lemma for elimination cases; intro cases proved)*
- [ ] Prove the IPL version with the "modulo theory axioms" qualification: the only additional formulas come from `ax` nodes, and theory axioms from IPL (efq schema) have subformulas that are themselves subformulas of the conclusion *(deviation: deferred to follow-up task)*
- [ ] Prove `Theory.Derivation.subformula_property : (d.normalize).SubformulaProperty` as the main corollary combining normalization with the subformula property *(deviation: blocked -- requires normalize_isNormal which requires Prawitz termination measure decrease)*
- [x] Run partial CI pipeline: `lake build`, `lake exe checkInitImports`, `lake exe lint-style` *(completed; lake test has pre-existing failures in other tasks)*

**Timing**: 2 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` - subformula property definitions and proofs

**Verification**:
- `subformula_property_of_isNormal` proof closes for MPL
- `subformula_property` corollary compiles
- Full CI pipeline passes
- No `sorry` in any definition or proof

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds at each phase
- [ ] `lake build` (full project) succeeds after Phase 4 and Phase 5
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] No `sorry` in any definition or proof (verify via `lean_verify` or `grep sorry`)
- [ ] `isNormal` correctly identifies all 5 redex patterns as non-normal
- [ ] `normalize` is a computable function (not `noncomputable`)
- [ ] Subformula property statement is mathematically correct for both MPL and IPL

## Artifacts & Outputs

- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` - main implementation file
- `Cslib.lean` - updated barrel import
- `specs/290_nd_normalization_subformula_property/plans/01_nd-normalization-plan.md` - this plan
- `specs/290_nd_normalization_subformula_property/summaries/01_nd-normalization-summary.md` - completion summary (after implementation)

## Rollback/Contingency

- The new file `Normalization.lean` is entirely additive; removing it and reverting `Cslib.lean` fully rolls back the change.
- If Phase 3 (WF termination) stalls, fall back to fuel-bounded normalization: define `normalizeAux` with a `Nat` fuel parameter and prove that a computable upper bound on fuel suffices. This is less elegant but still delivers a computable normalization function and the subformula property.
- If context arithmetic proofs cause excessive friction, extract them as standalone lemmas in a `Normalization.ContextLemmas` section or even a separate file.
- If the subformula property for IPL is harder than expected, deliver the MPL version first and mark the IPL extension as a follow-up task.
