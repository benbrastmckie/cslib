# Implementation Plan: Propositional Sequent Calculus LK/LJ

- **Task**: 279 - Propositional Sequent Calculus LK/LJ
- **Status**: [NOT STARTED]
- **Effort**: 18 hours
- **Dependencies**: None (tasks 280, 297 are completed; existing ND and Hilbert systems are stable)
- **Research Inputs**: specs/279_propositional_sequent_calculus_lk_lj/reports/01_team-research.md
- **Artifacts**: plans/02_sequent-calculus-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Implement two-sided Gentzen-style sequent calculi (LK for classical, LJ for intuitionistic propositional logic) with cut elimination, soundness, completeness, and equivalence bridges to the existing Hilbert and natural deduction systems. The implementation uses an all-additive Finset-based presentation (shared contexts, no splitting) for LK and single-conclusion Finset-based sequents for LJ, following the existing ND system as primary template. Bridge proofs compose via ND to reuse the existing ~400-line Hilbert-ND equivalence. This would be the first LK/LJ formalization in Lean 4 and unblocks downstream tasks 291 (three-way equivalence), 292 (IPL decidability), and 293 (Curry-Howard). Definition of done: all files compile, `lake build` passes, CI pipeline green, and all stated theorems (soundness, completeness, cut elimination, four bridge equivalences) are proved without sorry.

### Research Integration

Key findings from the team research report (01_team-research.md):
- All-additive Finset-based presentation confirmed as optimal: exchange and contraction are definitionally free, weakening needs explicit constructors, and the cut rule has the cleanest form
- LJ should use `Finset x Proposition Atom` (single conclusion) matching ND's `Sequent` type for near-definitional bridges
- Cut elimination via syntactic Gentzen method with lexicographic induction on `(formula_complexity, left_height + right_height)`, reusing `Proposition.complexity` from `Tableau/Defs.lean`
- CLL template transfers structural patterns only (HasInferenceSystem, cutFree predicate); its one-sided design and stub cut elimination are not reusable
- Completeness ordering: soundness first, then Hilbert simulation, then completeness as corollary (avoids circularity)
- Bridge composition: `hilbert_iff_lk := hilbert_iff_nd.trans nd_iff_lk` saves ~400 lines of deduction theorem duplication

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the proof-system triad for propositional logic (Hilbert + ND + SC) and supports the "triple decidability certification" goal (algebraic, tableau, cut-free proof search). The Propositional module is a shared sub-logic for Modal, Temporal, and Bimodal. LK generalizes cleanly to G3K/G3S4/G3S5 for future modal sequent calculi.

## Goals & Non-Goals

**Goals**:
- Define `LKSequent` (two-sided Finset-based) and `LKProof` inductive with all-additive rules
- Define `LJProof` inductive with single-conclusion (Finset x Proposition) matching ND
- Prove LK and LJ soundness by induction on derivations
- Prove LK and LJ cut elimination (Hauptsatz) via syntactic Gentzen method
- Prove LK and LJ completeness via bridge composition with existing Hilbert completeness
- Prove four equivalence bridges: `nd_iff_lk`, `hilbert_iff_lk`, `nd_iff_lj`, `hilbert_iff_lj`
- Register `HasInferenceSystem` instances for both LK and LJ
- Pass full CI pipeline (`lake build`, `lake test`, `checkInitImports`, `lint-style`)

**Non-Goals**:
- Modal sequent calculi (G3K, G3S4) -- future task
- Craig interpolation or Herbrand's theorem via SC -- future task
- Glivenko's theorem via LK/LJ connection -- can be added later
- Multiset-based alternative formulation
- Automated decision procedures via cut-free proof search (task 292)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Cut elimination termination checker issues | H | H | Define explicit `height` function and prove all size lemmas before main theorem; use `termination_by` with lexicographic measure |
| Cut elimination proof size exceeds phase budget | H | M | Allow sorry stubs in Phase 3/5 if needed, fill in Phase 6; each connective pair case is short and follows a pattern |
| Notation conflict with existing `⊢` in PL namespace | M | H | Use scoped notation `⊢ₛ` for LK sequents, namespace isolation via `SequentCalculus.LK` |
| Bridge proof complexity higher than estimated | M | L | Composing via ND (not direct Hilbert-LK) keeps each direction a straightforward structural translation |
| Lean 4 `decreasing_by` obligations for nested recursion | M | M | Prepare arithmetic lemmas for height sums; use `omega` tactic where possible |
| File count impacts build times | L | L | 8 files is well within normal range for CSLib modules |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 4 | 1 |
| 3 | 3, 5 | 2, 4 |
| 4 | 6 | 2, 3, 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Shared Definitions and LK Core [NOT STARTED]

**Goal**: Create the shared `Defs.lean` file with `LKSequent` type and notation, plus the `LK/Basic.lean` file with the `LKProof` inductive type, structural admissibility lemmas (weakening, monotone context), height function, and `HasInferenceSystem` instance.

**Tasks**:
- [ ] Create directory structure `Cslib/Logics/Propositional/SequentCalculus/` with `LK/` and `LJ/` subdirectories
- [ ] Define `LKSequent` structure in `Defs.lean` with `ant : Finset (Proposition Atom)` and `suc : Finset (Proposition Atom)`, plus scoped notation `⊢ₛ`
- [ ] Define `LKProof` inductive in `LK/Basic.lean` with all-additive rules: `ax`, `cut`, `weakL`, `weakR`, `botL`, `andL`, `andR`, `orL`, `orR`, `impL`, `impR`
- [ ] Define `LKProof.height : LKProof seq -> Nat` recursive function
- [ ] Prove height-preserving weakening admissibility: `weakenL_admissible` and `weakenR_admissible` for monotone Finset contexts (`Gamma ⊆ Gamma' -> LKProof (Gamma ⊢ₛ Delta) -> LKProof (Gamma' ⊢ₛ Delta)`)
- [ ] Define `LKProof.cutFree` predicate (proof contains no `cut` constructor)
- [ ] Define `CutFreeLKProof` subtype
- [ ] Register `HasInferenceSystem` instance for LK
- [ ] Update `Cslib.lean` barrel file with new imports
- [ ] Verify `lake build` compiles successfully

**Timing**: 2.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/Defs.lean` - Create: LKSequent type, notation
- `Cslib/Logics/Propositional/SequentCalculus/LK/Basic.lean` - Create: LKProof inductive, structural lemmas, height, InferenceSystem
- `Cslib.lean` - Add: new import lines

**Verification**:
- `lake build` succeeds with no errors
- `LKProof` type is well-formed with all 11 constructors
- Height function computes correctly on sample proofs
- Weakening admissibility lemmas type-check

---

### Phase 2: LK Soundness and Hilbert-to-LK Bridge [NOT STARTED]

**Goal**: Prove LK soundness (every LK-derivable sequent is semantically valid) and the Hilbert-to-LK simulation (every Hilbert axiom is LK-derivable, MP maps to cut), establishing LK completeness as a corollary via the existing Hilbert completeness.

**Tasks**:
- [ ] Define semantic validity for LK sequents: `LKSequent.valid` (for all valuations, if all antecedent formulas are true then some succedent formula is true)
- [ ] Prove `LKProof.soundness : LKProof seq -> seq.valid` by induction on derivation in `LK/Soundness.lean`
- [ ] Prove each Hilbert axiom is LK-derivable (K, S, DN, conjunction, disjunction, implication axioms) as helper lemmas
- [ ] Prove modus ponens simulation: given `LKProof (Gamma ⊢ₛ {A → B})` and `LKProof (Gamma ⊢ₛ {A})`, derive `LKProof (Gamma ⊢ₛ {B})` via cut
- [ ] Prove `hilbert_to_lk : DerivationTree Gamma A -> LKProof (Gamma ⊢ₛ {A})` by induction on Hilbert derivation
- [ ] Prove `lk_to_hilbert` via composition: `lk_to_nd` then existing `nd_to_hilbert`
- [ ] State and prove `hilbert_iff_lk` as an Iff combining the two directions
- [ ] Derive LK completeness as corollary: `LKSequent.valid seq -> LKProof seq` (using existing Hilbert completeness + hilbert_to_lk)
- [ ] Verify all files build

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/Soundness.lean` - Create: soundness theorem
- `Cslib/Logics/Propositional/SequentCalculus/LK/Completeness.lean` - Create: completeness via bridge, hilbert_to_lk
- `Cslib.lean` - Add: new import lines

**Verification**:
- `LKProof.soundness` type-checks without sorry
- `hilbert_to_lk` and `lk_to_hilbert` type-check without sorry
- `hilbert_iff_lk` is an Iff
- LK completeness theorem type-checks

---

### Phase 3: LK Cut Elimination (Hauptsatz) [NOT STARTED]

**Goal**: Prove the cut elimination theorem for LK: every LK proof can be transformed into a cut-free LK proof. This is the highest-risk phase due to the complexity of the termination argument and the number of case combinations.

**Tasks**:
- [ ] Define `Proposition.complexity` import or alias from `Tableau/Defs.lean` (cut-rank measure)
- [ ] Prove auxiliary height arithmetic lemmas: height of subproofs is strictly less than height of parent
- [ ] Prove `cutElim_principal` for each connective pair (and/and, or/or, imp/imp, bot): when both premises introduce the cut formula, reduce to cuts on smaller formulas
- [ ] Prove `cutElim_commutative_left`: when the left premise introduces the cut formula via a rule other than the principal one, push the cut inward (height decreases)
- [ ] Prove `cutElim_commutative_right`: symmetric case for right premise
- [ ] Define the main `cutElim : LKProof seq -> CutFreeLKProof seq` theorem using well-founded recursion on `(Proposition.complexity A, left.height + right.height)` lexicographic order
- [ ] Verify `termination_by` obligation discharges cleanly (use `decreasing_by` with `omega` and height lemmas)
- [ ] If termination issues arise, use `sorry` stubs for specific cases and document which cases remain

**Timing**: 4 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - Create: Hauptsatz for LK
- `Cslib.lean` - Add: new import line

**Verification**:
- `cutElim` type-checks (ideally without sorry; document any remaining stubs)
- Cut-free proofs produced by `cutElim` satisfy `LKProof.cutFree` predicate
- `lake build` succeeds

---

### Phase 4: LJ Core, Structural Lemmas, and Soundness [NOT STARTED]

**Goal**: Define the LJ proof system (single-conclusion, Finset-based antecedent), prove structural admissibility and soundness. This phase parallels Phase 1+2 for LJ.

**Tasks**:
- [ ] Define `LJProof : Finset (Proposition Atom) -> Proposition Atom -> Type` inductive in `LJ/Basic.lean` with rules: `ax`, `cut`, `weakL`, `botL`, `andL`, `andR`, `orL`, `orR1`, `orR2`, `impL`, `impR`
- [ ] Define `LJProof.height` recursive function
- [ ] Prove monotone weakening admissibility for LJ: `Gamma ⊆ Gamma' -> LJProof Gamma A -> LJProof Gamma' A`
- [ ] Define `LJProof.cutFree` predicate and `CutFreeLJProof` subtype
- [ ] Register `HasInferenceSystem` instance for LJ
- [ ] Define Kripke validity for LJ sequents (using existing IPL Kripke semantics if available, or Boolean for CPL fragment)
- [ ] Prove `LJProof.soundness` by induction on derivation in `LJ/Soundness.lean`
- [ ] Update `Cslib.lean` barrel file with LJ imports
- [ ] Verify `lake build` compiles

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean` - Create: LJProof inductive, structural lemmas, InferenceSystem
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Soundness.lean` - Create: LJ soundness
- `Cslib.lean` - Add: new import lines

**Verification**:
- `LJProof` has all 11 constructors (note `orR1`/`orR2` instead of single `orR`)
- Weakening admissibility type-checks without sorry
- `LJProof.soundness` type-checks without sorry
- `lake build` succeeds

---

### Phase 5: LJ Cut Elimination [NOT STARTED]

**Goal**: Prove cut elimination for LJ. The structure mirrors Phase 3 but with simpler right-side cases (single conclusion instead of Finset) and different commutative cases for `orR1`/`orR2`.

**Tasks**:
- [ ] Prove auxiliary height arithmetic lemmas for LJ
- [ ] Prove `cutElim_principal` for each LJ connective pair
- [ ] Prove `cutElim_commutative` cases (simpler than LK due to single conclusion)
- [ ] Define `cutElim : LJProof Gamma A -> CutFreeLJProof Gamma A` with well-founded recursion on `(Proposition.complexity, left.height + right.height)`
- [ ] Verify termination obligations
- [ ] Document any sorry stubs if termination issues arise

**Timing**: 3.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` - Create: Hauptsatz for LJ
- `Cslib.lean` - Add: new import line

**Verification**:
- `cutElim` type-checks (document any remaining sorry stubs)
- `lake build` succeeds

---

### Phase 6: Equivalence Bridges and Final Integration [NOT STARTED]

**Goal**: Prove all four bridge equivalences (nd_iff_lk, nd_iff_lj, hilbert_iff_lk, hilbert_iff_lj), fill any remaining sorry stubs from Phases 3/5, run full CI, and verify the complete module compiles.

**Tasks**:
- [ ] Prove `nd_to_lk : Theory.Derivation CPL Gamma A -> LKProof (Gamma ⊢ₛ {A})` by induction on ND derivation (structural translation: each ND rule maps to 1-2 LK rules)
- [ ] Prove `lk_to_nd : LKProof (Gamma ⊢ₛ {A}) -> Theory.Derivation CPL Gamma A` (requires classical reasoning for multi-succedent to single-conclusion)
- [ ] Prove `nd_iff_lk` as Iff combining the two directions
- [ ] Derive `hilbert_iff_lk := hilbert_iff_nd_ctx.trans nd_iff_lk` (or manual composition)
- [ ] Prove `nd_to_lj : Theory.Derivation IPL Gamma A -> LJProof Gamma A` by induction
- [ ] Prove `lj_to_nd : LJProof Gamma A -> Theory.Derivation IPL Gamma A` by induction
- [ ] Prove `nd_iff_lj` as Iff
- [ ] Derive `hilbert_iff_lj` via composition with existing intuitionistic Hilbert-ND bridge
- [ ] Fill any remaining sorry stubs in cut elimination files
- [ ] Run `lake build` to verify full compilation
- [ ] Run `lake test` to verify test suite
- [ ] Run `lake exe checkInitImports` and `lake exe lint-style`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` for import analysis

**Timing**: 2.5 hours

**Depends on**: 2, 3, 4, 5

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/Equivalence.lean` - Create: all bridge proofs
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - Edit: fill sorry stubs if any
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` - Edit: fill sorry stubs if any
- `Cslib.lean` - Add: Equivalence import

**Verification**:
- All four bridge equivalences (`nd_iff_lk`, `hilbert_iff_lk`, `nd_iff_lj`, `hilbert_iff_lj`) type-check without sorry
- Zero sorry stubs remain across all files
- `lake build` succeeds
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake shake` reports no issues

## Testing & Validation

- [ ] `lake build` compiles all 8 new files without errors or sorry
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes with new Cslib.Init entries
- [ ] `lake exe lint-style` passes on all new files
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports clean imports
- [ ] `LKProof.soundness` and `LJProof.soundness` are sorry-free
- [ ] `cutElim` for both LK and LJ are sorry-free
- [ ] All four bridge equivalences are sorry-free
- [ ] Notation `⊢ₛ` does not conflict with existing `⊢` notation in PL namespace

## Artifacts & Outputs

- `Cslib/Logics/Propositional/SequentCalculus/Defs.lean` - Shared types, LKSequent, notation
- `Cslib/Logics/Propositional/SequentCalculus/LK/Basic.lean` - LKProof, structural lemmas, InferenceSystem
- `Cslib/Logics/Propositional/SequentCalculus/LK/Soundness.lean` - LK soundness
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` - LK Hauptsatz
- `Cslib/Logics/Propositional/SequentCalculus/LK/Completeness.lean` - LK completeness via bridge
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean` - LJProof, structural lemmas
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Soundness.lean` - LJ soundness
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` - LJ Hauptsatz
- `Cslib/Logics/Propositional/SequentCalculus/Equivalence.lean` - All bridge proofs
- `specs/279_propositional_sequent_calculus_lk_lj/plans/02_sequent-calculus-plan.md` - This plan

## Rollback/Contingency

All changes are in new files under `Cslib/Logics/Propositional/SequentCalculus/`. No existing files are modified except `Cslib.lean` (barrel imports). Rollback consists of:
1. Remove the `SequentCalculus/` directory
2. Revert `Cslib.lean` import additions
3. Revert `Cslib/Init.lean` if modified

If cut elimination proves intractable within the time budget, the remaining sorry stubs can be documented and addressed in a follow-up task. The soundness, completeness (via bridge), and equivalence bridges are independently valuable without cut elimination.
