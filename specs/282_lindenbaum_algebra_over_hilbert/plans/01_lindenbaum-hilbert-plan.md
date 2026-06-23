# Implementation Plan: Hilbert Lindenbaum Algebra

- **Task**: 282 - Rebuild the Lindenbaum algebra construction over Hilbert derivations
- **Status**: [COMPLETED]
- **Effort**: 6 hours
- **Dependencies**: Task 281 (Hilbert derived rules -- done)
- **Research Inputs**: specs/282_lindenbaum_algebra_over_hilbert/reports/01_lindenbaum-hilbert.md
- **Artifacts**: plans/01_lindenbaum-hilbert-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Construct a new `HilbertLindenbaumAlgebra Axioms` quotient type parameterized over a Hilbert axiom predicate with `[MinimalAxioms Axioms]`, replacing the ND-based `LindenbaumAlgebra T`. The new construction defines the equivalence relation, ordering, lattice operations (sup/inf/himp/top/bot), and typeclass instances (GHA/HA/BA) entirely in terms of `Deriv Axioms [A] B` using the `hilbert*Deriv` rules from task 281. The existing ND Lindenbaum.lean is preserved for downstream consumers (Completeness.lean). A new file `HilbertLindenbaum.lean` is created.

### Research Integration

Key findings from the research report (01_lindenbaum-hilbert.md):

- **Option A (pure Hilbert from scratch)** is the recommended approach. The bridge theorems only connect `Deriv Axioms Gamma.toList phi` to `DerivableIn (AxiomTheory Axioms) (Gamma ⊢ phi)` and do not generalize to arbitrary theories T, making a wrapper approach insufficient.
- `MinimalAxioms` typeclass bundles K, S, andI, andE1, andE2, orI1, orI2, orE -- instances exist for `MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom`.
- All `hilbert*Deriv` rules are available at `Deriv` level (Prop-level `Nonempty` wrappers).
- `hilbertCutDeriv` signature: `Deriv Axioms Gamma A -> Deriv Axioms (A :: Delta) B -> Deriv Axioms (Gamma ++ Delta) B` (requires K, S).
- `hilbertWeakeningDeriv` signature: `Deriv Axioms Gamma phi -> (forall x in Gamma, x in Delta) -> Deriv Axioms Delta phi`.
- `hilbertImpIDeriv` and `hilbertOrEDeriv` are noncomputable (use deduction theorem).
- The hardest proof is `le_himp_iff` (deduction theorem + cut + and-intro/elim).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the "Logics/Propositional" module area in the roadmap. It is part of the chain 281->282->283->284->285 that standardizes propositional logic on Hilbert derivations.

## Goals & Non-Goals

**Goals**:
- Define `HilbertLindenbaumAlgebra Axioms` as a quotient of propositions by Hilbert equivalence
- Prove `GeneralizedHeytingAlgebra` instance for any `[MinimalAxioms Axioms]`
- Prove `HeytingAlgebra` instance when EFQ axiom is available
- Prove `BooleanAlgebra` instance when Peirce axiom is available
- Provide simp lemmas: `hilbertLindenbaumMk_le_mk`, `_sup`, `_inf`, `_himp`
- Register the new file in `Cslib.lean` and verify CI

**Non-Goals**:
- Migrating downstream consumers (Completeness.lean) from ND Lindenbaum to Hilbert -- that is task 283+
- Deleting the existing ND Lindenbaum.lean
- Proving a bridge isomorphism between HilbertLindenbaumAlgebra and LindenbaumAlgebra
- Defining `SetDerivable`-based ordering (the `Deriv` singleton-list approach is sufficient)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `hilbertCutDeriv` context append `(Gamma ++ Delta)` does not simplify to singleton for `le_trans` | H | M | Use `hilbertWeakeningDeriv` after cut to collapse `[A] ++ [] = [A]` back to singleton; prove helper lemma `hilbertCutSingletonDeriv` |
| `noncomputable` propagation from `hilbertImpIDeriv`/`hilbertOrEDeriv` makes too many definitions noncomputable | M | H | Accept noncomputability -- the existing ND Lindenbaum uses `Classical.choice` extensively; mark the whole `HilbertLindenbaum.lean` as `noncomputable section` |
| Axiom parameter threading is verbose | M | M | Define `MinimalAxioms`-aware convenience wrappers that extract axiom witnesses via typeclass fields |
| `le_himp_iff` proof is complex with Hilbert structural rules | H | M | Follow the existing ND proof structure closely; use `hilbertCutDeriv` in place of `DerivableIn.cut_away` |
| Congruence lemmas for or/and/imp well-definedness are nontrivial | M | M | Prove `HilbertEquiv.or_congr`, `and_congr`, `imp_congr` as standalone lemmas before defining quotient operations |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Foundation -- Equivalence Relation and Quotient Type [IN PROGRESS]

**Goal**: Create `HilbertLindenbaum.lean` with the Hilbert equivalence relation, setoid, quotient type, quotient map, and ordering.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` with module header, copyright, imports
- [ ] Import `Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` and `Mathlib.Order.Heyting.Regular`
- [ ] Define `HilbertEquiv Axioms A B : Prop := Deriv Axioms [A] B ∧ Deriv Axioms [B] A`
- [ ] Prove `HilbertEquiv` is an equivalence relation: reflexivity via `assumption_deriv`, symmetry by swapping, transitivity via `hilbertCutDeriv` + `hilbertWeakeningDeriv` (collapsing `[A] ++ [] = [A]`)
- [ ] Define `hilbertPropositionSetoid` as `Setoid (Proposition Atom)` from `HilbertEquiv`
- [ ] Define `HilbertLindenbaumAlgebra Axioms := Quotient (hilbertPropositionSetoid Axioms)`
- [ ] Define `hilbertLindenbaumMk Axioms A := Quotient.mk ... A`
- [ ] Define `hilbertLindenbaumLe Axioms x y` via `Quotient.liftOn₂` using `Deriv Axioms [A] B`
- [ ] Prove well-definedness of `hilbertLindenbaumLe` (needs `hilbertCutDeriv` + `hilbertWeakeningDeriv`)
- [ ] Prove `hilbertLindenbaumLe_mk` simp lemma

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` -- new file

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum` compiles
- `lean_goal` confirms `hilbertLindenbaumLe_mk` has type `... ↔ Deriv Axioms [A] B`

---

### Phase 2: Lattice Operations and Congruence [NOT STARTED]

**Goal**: Define sup (or), inf (and), himp (imp), top operations on the quotient, with well-definedness proofs via congruence lemmas.

**Tasks**:
- [ ] Prove `HilbertEquiv.or_congr [MinimalAxioms Axioms]`: if `HilbertEquiv Axioms A A'` and `HilbertEquiv Axioms B B'` then `HilbertEquiv Axioms (A ∨ B) (A' ∨ B')`. Uses `hilbertOrEDeriv` to case-split on `A ∨ B`, then `hilbertOrI1Deriv`/`hilbertOrI2Deriv` with weakened hypothesis derivations via `hilbertCutDeriv`.
- [ ] Prove `HilbertEquiv.and_congr [MinimalAxioms Axioms]`: uses `hilbertAndE1Deriv`/`hilbertAndE2Deriv` to extract components, `hilbertCutDeriv` to apply equivalences, `hilbertAndIDeriv` to reconstruct.
- [ ] Prove `HilbertEquiv.imp_congr [MinimalAxioms Axioms]`: uses `hilbertImpIDeriv` + `hilbertImpEDeriv` + `hilbertCutDeriv` to transform `A → B` into `A' → B'`.
- [ ] Define `hilbertLindenbaumSup Axioms x y` via `Quotient.lift₂` using `.or`, well-def by `or_congr`
- [ ] Define `hilbertLindenbaumInf Axioms x y` via `Quotient.lift₂` using `.and`, well-def by `and_congr`
- [ ] Define `hilbertLindenbaumHimp Axioms x y` via `Quotient.lift₂` using `.imp`, well-def by `imp_congr`
- [ ] Prove simp lemmas: `hilbertLindenbaumSup_mk`, `hilbertLindenbaumInf_mk`, `hilbertLindenbaumHimp_mk`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` -- append

**Key Hilbert rules used**:
- `hilbertOrEDeriv` (K, S, orE), `hilbertOrI1Deriv` (orI1), `hilbertOrI2Deriv` (orI2)
- `hilbertAndIDeriv` (andI), `hilbertAndE1Deriv` (andE1), `hilbertAndE2Deriv` (andE2)
- `hilbertImpIDeriv` (K, S), `hilbertImpEDeriv` (none)
- `hilbertCutDeriv` (K, S), `hilbertWeakeningDeriv` (none)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum` compiles
- All three simp lemmas reduce to `rfl`

---

### Phase 3: GHA Instance [NOT STARTED]

**Goal**: Prove all axioms for `GeneralizedHeytingAlgebra (HilbertLindenbaumAlgebra Axioms)`.

**Tasks**:
- [ ] Prove `hilbertLindenbaumLe_refl`: `assumption_deriv (List.mem_cons_self A [])`
- [ ] Prove `hilbertLindenbaumLe_trans`: cut `[A] ⊢ B` with `[B] ⊢ C` via `hilbertCutDeriv`, then weaken `[A] ++ [] ⊢ C` to `[A] ⊢ C`
- [ ] Prove `hilbertLindenbaumLe_antisymm`: extract both directions, apply `Quotient.sound`
- [ ] Prove `hilbertLindenbaumLe_sup_left`: `hilbertOrI1Deriv` applied to `assumption_deriv`
- [ ] Prove `hilbertLindenbaumLe_sup_right`: `hilbertOrI2Deriv` applied to `assumption_deriv`
- [ ] Prove `hilbertLindenbaumSup_le`: `hilbertOrEDeriv` with `hilbertWeakeningDeriv` on both branches
- [ ] Prove `hilbertLindenbaumInf_le_left`: `hilbertAndE1Deriv` applied to `assumption_deriv`
- [ ] Prove `hilbertLindenbaumInf_le_right`: `hilbertAndE2Deriv` applied to `assumption_deriv`
- [ ] Prove `hilbertLindenbaumLe_inf`: `hilbertAndIDeriv` applied to both hypotheses (may need `Classical.choice` to extract from `Nonempty`)
- [ ] Prove `hilbertLindenbaumLe_himp_iff` (hardest):
  - Forward (`[A] ⊢ B → C` implies `[A ∧ B] ⊢ C`): Use `hilbertAndE1Deriv`/`hilbertAndE2Deriv` on assumption, `hilbertCutDeriv` to chain with the hypothesis, `hilbertImpEDeriv` to apply
  - Backward (`[A ∧ B] ⊢ C` implies `[A] ⊢ B → C`): Use `hilbertImpIDeriv` to abstract B, build `[B, A] ⊢ A ∧ B` via `hilbertAndIDeriv` with assumptions, `hilbertCutDeriv` with hypothesis
- [ ] Prove `hilbertLindenbaumLe_top`: `hilbertImpIDeriv` producing `[A] ⊢ ⊥ → ⊥` from `assumption_deriv`
- [ ] Assemble `GeneralizedHeytingAlgebra` instance

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` -- append

**Key Hilbert rules used**:
- All Deriv-level rules from `HilbertDerivedRules.lean`
- `hilbertCutDeriv` (K, S) for transitivity and himp proofs
- `hilbertImpIDeriv` (K, S) for himp backward direction and top
- `assumption_deriv` for reflexivity and simple lemmas

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum` compiles
- `lean_verify` on the GHA instance confirms no `sorry`

---

### Phase 4: HA Instance (Intuitionistic) [NOT STARTED]

**Goal**: Add `HeytingAlgebra` instance when the axiom predicate includes EFQ.

**Tasks**:
- [ ] Define `Bot` instance on `HilbertLindenbaumAlgebra Axioms` as `hilbertLindenbaumMk Axioms .bot`, gated by an EFQ hypothesis `(h_EFQ : forall phi, Axioms (Proposition.bot.imp phi))`
- [ ] Prove `hilbertLindenbaumBot_le`: `hilbertBotEDeriv h_EFQ (assumption_deriv ...)`
- [ ] Prove `hilbertLindenbaumBot`: `(bot : HilbertLindenbaumAlgebra Axioms) = hilbertLindenbaumMk Axioms .bot`
- [ ] Assemble `HeytingAlgebra` instance with `bot_le`, `compl x := x ⇨ bot`, `himp_bot _ := rfl`
- [ ] Provide instances for `IntPropAxiom` and `PropositionalAxiom` (both have EFQ)

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` -- append

**Key Hilbert rules used**:
- `hilbertBotEDeriv` (EFQ)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum` compiles
- Confirm HeytingAlgebra typeclass resolves for `HilbertLindenbaumAlgebra IntPropAxiom`

---

### Phase 5: BA Instance (Classical) [NOT STARTED]

**Goal**: Add `BooleanAlgebra` instance when axioms include both EFQ and Peirce.

**Tasks**:
- [ ] Prove `hilbertLindenbaumEM`: for classical axioms, `hilbertLindenbaumMk Axioms A ⊔ (hilbertLindenbaumMk Axioms A ⇨ bot) = top`. Strategy: build `[⊥ → ⊥] ⊢ A ∨ (A → ⊥)` using `hilbertDneDeriv` (following the ND Lindenbaum pattern -- DNE applied to double-negation of EM)
- [ ] Prove `hilbertLindenbaumRegular`: `IsRegular (x ⊔ xᶜ)` using `lindenbaumEM` and `isRegular_top`
- [ ] Apply `BooleanAlgebra.ofRegular hilbertLindenbaumRegular` for the noncomputable instance
- [ ] Gate on both EFQ hypothesis and Peirce hypothesis `(h_Peirce : forall phi psi, Axioms (((phi.imp psi).imp phi).imp phi))`

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` -- append

**Key Hilbert rules used**:
- `hilbertDneDeriv` (K, S, EFQ, Peirce) for excluded middle
- `hilbertImpIDeriv` (K, S), `hilbertImpEDeriv`, `hilbertOrI1Deriv`, `hilbertOrI2Deriv`
- `hilbertNegIDeriv` (K, S) for building negation terms

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum` compiles
- Confirm BooleanAlgebra resolves for `HilbertLindenbaumAlgebra PropositionalAxiom`

---

### Phase 6: Integration and CI [NOT STARTED]

**Goal**: Register the new file in `Cslib.lean`, verify full CI pipeline, add remaining simp lemmas and API surface.

**Tasks**:
- [ ] Add `import Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum` to `Cslib.lean` via `lake exe mk_all --module`
- [ ] Add simp lemmas: `hilbertLindenbaumMk_le_mk`, `hilbertLindenbaumMk_sup`, `hilbertLindenbaumMk_inf`, `hilbertLindenbaumMk_himp`
- [ ] Add `hilbertLindenbaumTop` theorem: `(top : HilbertLindenbaumAlgebra Axioms) = hilbertLindenbaumMk Axioms (.imp .bot .bot)`
- [ ] Verify `lake build` (full project)
- [ ] Verify `lake exe checkInitImports`
- [ ] Verify `lake exe lint-style`
- [ ] Verify `lake test`

**Timing**: 0.5 hours

**Depends on**: 4, 5

**Files to modify**:
- `Cslib.lean` -- add import line (via `mk_all`)
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` -- final polish

**Verification**:
- All CI checks pass: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake test`
- `lean_verify` on all public definitions confirms no `sorry`

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum` compiles without errors or warnings
- [ ] `lake build` (full project) succeeds -- no regressions in existing files
- [ ] `lake exe checkInitImports` passes -- new file imports `Cslib.Init`
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] No `sorry` in the new file (`lean_verify` on each key definition)
- [ ] GHA instance resolves for `HilbertLindenbaumAlgebra MinPropAxiom`
- [ ] HA instance resolves for `HilbertLindenbaumAlgebra IntPropAxiom`
- [ ] BA instance resolves for `HilbertLindenbaumAlgebra PropositionalAxiom`
- [ ] Existing `Lindenbaum.lean` and all downstream files still compile

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` -- new file (~420 lines)
- `Cslib.lean` -- updated barrel import
- `specs/282_lindenbaum_algebra_over_hilbert/plans/01_lindenbaum-hilbert-plan.md` -- this plan

## Rollback/Contingency

The new file `HilbertLindenbaum.lean` is additive -- it does not modify any existing files except `Cslib.lean` (barrel import). If the implementation fails:

1. Delete `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean`
2. Regenerate `Cslib.lean` via `lake exe mk_all --module`
3. All existing functionality is preserved since the ND Lindenbaum.lean is untouched

If individual phases are blocked (e.g., `le_himp_iff` proof is intractable):
- Mark the phase `[BLOCKED]` with the specific goal state
- The GHA instance cannot be assembled without `le_himp_iff`, so all downstream phases are also blocked
- Consider falling back to Option B (bridge-based) for the blocked proof only
