/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Metalogic.GenericMCS

/-! # Deduction Theorem Characterization

Formalizes the converse of the deduction-theorem characterization:
any derivation system with the deduction theorem yields the K and S axioms,
hence an instance of `MinimalHilbert` (IPL⟨→,⊤⟩).

The forward direction (every `MinimalHilbert` system admits a deduction theorem)
is already in `GenericMCS` via `algebraic_has_deduction_theorem`.
This module proves the converse and closes the characterization loop.

## Main results

- `dt_implies_implyK`: From `HasDeductionTheorem D`, derive `⊢ φ → (ψ → φ)`.
- `dt_implies_implyS`: From `HasDeductionTheorem D`, derive the S axiom.
- `DtSystem`: Tag type for the inference system induced by a DT-system.
- `dt_inference_system`: Inference system instance from `(D, hdt)`.
- `DtSystem.dt_minimal_hilbert`: `MinimalHilbert` instance from any DT-system.
- `dt_implies_minimal_hilbert`: DT-systems instance MinimalHilbert.
- `minimal_hilbert_has_deduction_theorem`: MinimalHilbert implies DT (restates
  `algebraic_has_deduction_theorem`).

## References

* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 2.
* B. Doty, CSLib Zulip Temporal Logic thread, 2026-06-25.
-/

@[expose] public section

open Cslib.Logic
open Cslib.Logic.Metalogic
open Cslib.Logic.Metalogic.GenericMCS

namespace Cslib.Logic.Metalogic.DeductionCharacterization

variable {F : Type*} [HasBot F] [HasImp F]

/-! ## Converse Heart: K and S Axioms from the Deduction Theorem -/

omit [HasBot F] in
/-- From the deduction theorem, derive the K axiom: `⊢ A → (B → A)`.

Given any derivation system `D` satisfying the deduction theorem, the K
(weakening) axiom holds. The proof uses two applications of `hdt`:

1. `[B, A] ⊢ A` by assumption (`A ∈ [B, A]`).
2. Strip `B`: `[A] ⊢ B → A` by `hdt`.
3. Strip `A`: `[] ⊢ A → (B → A)` by `hdt`.

This yields the K axiom `Axioms.ImplyK A B = A → (B → A)`. -/
theorem dt_implies_implyK (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
    (A B : F) : D.Deriv [] (Axioms.ImplyK A B) := by
  have h1 : D.Deriv [B, A] A := D.assumption (by simp)          -- A ∈ [B, A]
  have h2 : D.Deriv [A] (HasImp.imp B A) := hdt h1              -- strip B
  exact hdt h2                                                  -- strip A : ⊢ A → (B → A)

omit [HasBot F] in
/-- From the deduction theorem, derive the S axiom:
`⊢ (A → (B → C)) → ((A → B) → (A → C))`.

Given any derivation system `D` satisfying the deduction theorem, the S
(distribution) axiom holds. The proof uses three applications of `hdt` and
three applications of modus ponens.

Setting `p := A → (B → C)` and `q := A → B`:

1. `[A, q, p] ⊢ A`, `[A, q, p] ⊢ q`, `[A, q, p] ⊢ p` by assumption.
2. `[A, q, p] ⊢ B` by `mp(q, A)` (from `A → B` and `A`).
3. `[A, q, p] ⊢ B → C` by `mp(p, A)` (from `A → (B → C)` and `A`).
4. `[A, q, p] ⊢ C` by `mp(B → C, B)`.
5. Strip `A`: `[q, p] ⊢ A → C` by `hdt`.
6. Strip `q`: `[p] ⊢ q → (A → C)` by `hdt`.
7. Strip `p`: `[] ⊢ p → (q → (A → C))` = `Axioms.ImplyS A B C` by `hdt`. -/
theorem dt_implies_implyS (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
    (A B C : F) : D.Deriv [] (Axioms.ImplyS A B C) := by
  set p := HasImp.imp A (HasImp.imp B C)                        -- A → (B → C)
  set q := HasImp.imp A B                                       -- A → B
  have hA  : D.Deriv [A, q, p] A := D.assumption (by simp)
  have hqd : D.Deriv [A, q, p] q := D.assumption (by simp)
  have hpd : D.Deriv [A, q, p] p := D.assumption (by simp)
  have hB  : D.Deriv [A, q, p] B := D.mp hqd hA                 -- B   from (A→B), A
  have hBC : D.Deriv [A, q, p] (HasImp.imp B C) := D.mp hpd hA  -- B→C from (A→(B→C)), A
  have hC  : D.Deriv [A, q, p] C := D.mp hBC hB                 -- C
  have s3  : D.Deriv [q, p] (HasImp.imp A C) := hdt hC          -- strip A
  have s2  : D.Deriv [p] (HasImp.imp q (HasImp.imp A C)) := hdt s3   -- strip q
  exact hdt s2                                                  -- strip p : the S axiom

/-! ## Inference System Bridge -/

/-- Tag type for the inference system induced by a derivation system with
the deduction theorem.

`DtSystem D hdt` serves as the system index `S` in
`InferenceSystem (DtSystem D hdt) F`. The fields `D` and `hdt` are carried
as type indices so the instance is determined uniquely. -/
structure DtSystem (D : DerivationSystem F) (hdt : HasDeductionTheorem D) : Type where

/-- The inference system induced by a DT-system `(D, hdt)`.

A derivation of `φ` in `DtSystem D hdt` is a proof of `D.Deriv [] φ`,
lifted to `Type 0` via `PLift`. This makes
`InferenceSystem.DerivableIn (DtSystem D hdt) φ ↔ D.Deriv [] φ`. -/
instance dt_inference_system (D : DerivationSystem F) (hdt : HasDeductionTheorem D) :
    InferenceSystem (DtSystem D hdt) F where
  derivation φ := PLift (D.Deriv [] φ)

namespace DtSystem

/-- Every derivation system with the deduction theorem instances `MinimalHilbert`.

The three required components are:
- `ModusPonens`: modus ponens at the empty context, lifted via `PLift`.
- `HasAxiomImplyK`: `dt_implies_implyK` lifted to `DerivableIn`.
- `HasAxiomImplyS`: `dt_implies_implyS` lifted to `DerivableIn`.

Together these show that any DT-system is at least as strong as the minimal
implicational Hilbert calculus IPL⟨→,⊤⟩. -/
instance dt_minimal_hilbert (D : DerivationSystem F) (hdt : HasDeductionTheorem D) :
    MinimalHilbert (DtSystem D hdt) (F := F) where
  mp h1 h2 :=
    ⟨PLift.up (D.mp h1.some.down h2.some.down)⟩
  implyK {φ ψ} := ⟨PLift.up (dt_implies_implyK D hdt φ ψ)⟩
  implyS {φ ψ χ} := ⟨PLift.up (dt_implies_implyS D hdt φ ψ χ)⟩

end DtSystem

/-! ## Characterization Theorems -/

/-- **Converse**: Any derivation system with the deduction theorem yields a
`MinimalHilbert` instance.

This is the main new contribution: `DtSystem D hdt` witnesses that any
DT-system is at least as strong as IPL⟨→,⊤⟩. -/
theorem dt_implies_minimal_hilbert
    (D : DerivationSystem F) (hdt : HasDeductionTheorem D) :
    MinimalHilbert (DtSystem D hdt) (F := F) :=
  inferInstance

/-- **Forward direction**: Every `MinimalHilbert` system has the deduction theorem.

This restates `algebraic_has_deduction_theorem` from `GenericMCS`. The
algebraic derivation system built from any `MinimalHilbert` instance
automatically has the deduction theorem. -/
theorem minimal_hilbert_has_deduction_theorem
    (S : Type*) [InferenceSystem S F] [MinimalHilbert S (F := F)] :
    HasDeductionTheorem (algebraicDerivationSystem (S := S) (F := F)) :=
  algebraic_has_deduction_theorem

end Cslib.Logic.Metalogic.DeductionCharacterization
