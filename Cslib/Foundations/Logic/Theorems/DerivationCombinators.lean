/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Theorems.Combinators
public import Cslib.Foundations.Logic.Theorems.Propositional.Core
public import Cslib.Foundations.Logic.Theorems.Propositional.Connectives

/-! # Raw-Derivation-Typed Combinator Layer

This module provides a single, once-proved layer of propositional reasoning combinators
typed directly at the raw derivation `S⇓·` (`InferenceSystem.derivation S ·`), rather than
at the `Prop`-valued `InferenceSystem.DerivableIn S ·`. Every per-target Hilbert proof system
(Temporal, Bimodal, ...) works natively with raw derivation trees (e.g. `DerivationTree fc [] φ`,
which is definitionally `S⇓φ` under the system's `InferenceSystem` instance), so a raw-typed
combinator can be applied directly by per-target consumers without any local bridging code.

## No New Bridge Typeclass

This module introduces **no new typeclass**. It delegates to the already-proved
`Theorems.Combinators` / `Theorems.Propositional.{Core,Connectives}` results (which are stated
at `InferenceSystem.DerivableIn`) via the *existing* bidirectional bridge already provided by
`InferenceSystem`:
- `InferenceSystem.DerivableIn.fromDerivation : S⇓a → DerivableIn S a` (also a `Coe` instance)
- `InferenceSystem.DerivableIn.toDerivation : DerivableIn S a → S⇓a` (noncomputable, also a
  `Coe` instance, via `Classical.choice`)

Previously, each of the three per-target helper files (`Temporal/Metalogic/PropositionalHelpers`,
`Bimodal/Theorems/Perpetuity/Helpers`, and `Bimodal/Theorems/Propositional/Connectives`)
independently redefined this exact same `wrap`/`unwrap` bridge pattern. This module collapses
that duplication into one generic, once-proved layer; per-target files now call these
combinators directly.

## Naming

Combinators generally reuse the generic theorem's name in lowerCamelCase (e.g. `identity`,
`doubleNegation`, `lceImp`). `impTransD` is named with a `D` suffix (for "Derivation") to avoid
shadowing `Theorems.Combinators.imp_trans` when both are open in the same scope.
-/

@[expose] public section

namespace Cslib.Logic.Theorems.DerivationCombinators

open Cslib.Logic
open Cslib.Logic.InferenceSystem

/-! ## Minimal (`[MinimalHilbert S]`) -/

section Minimal

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [MinimalHilbert S (F := F)]

/-- Identity combinator: `S⇓(φ → φ)`. -/
noncomputable def identity (φ : F) : S⇓(HasImp.imp φ φ) :=
  (Theorems.Combinators.identity (S := S) φ).toDerivation

/-- Transitivity of implication: from `S⇓(φ → ψ)` and `S⇓(ψ → χ)`, derive `S⇓(φ → χ)`. -/
noncomputable def impTransD {φ ψ χ : F}
    (d1 : S⇓(HasImp.imp φ ψ)) (d2 : S⇓(HasImp.imp ψ χ)) :
    S⇓(HasImp.imp φ χ) :=
  (Theorems.Combinators.imp_trans (S := S)
    (DerivableIn.fromDerivation d1) (DerivableIn.fromDerivation d2)).toDerivation

/-- Double negation introduction: `S⇓(φ → ¬¬φ)`. -/
noncomputable def dni (φ : F) :
    S⇓(HasImp.imp φ (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)) :=
  (Theorems.Combinators.dni (S := S) φ).toDerivation

/-- Pairing combinator: `S⇓(φ → ψ → ¬(φ → ¬ψ))` (conjunction introduction). -/
noncomputable def pairing (φ ψ : F) :
    S⇓(HasImp.imp φ (HasImp.imp ψ
      (HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot))) :=
  (Theorems.Combinators.pairing (S := S) φ ψ).toDerivation

/-- Combine two implications into conjunction: from `S⇓(P → A)` and `S⇓(P → B)`,
    derive `S⇓(P → ¬(A → ¬B))`. -/
noncomputable def combineImpConj {P A₁ B₁ : F}
    (hA : S⇓(HasImp.imp P A₁)) (hB : S⇓(HasImp.imp P B₁)) :
    S⇓(HasImp.imp P
      (HasImp.imp (HasImp.imp A₁ (HasImp.imp B₁ HasBot.bot)) HasBot.bot)) :=
  (Theorems.Combinators.combine_imp_conj (S := S)
    (DerivableIn.fromDerivation hA) (DerivableIn.fromDerivation hB)).toDerivation

/-- Combine three implications into nested conjunction: from `S⇓(P → A)`, `S⇓(P → B)`,
    `S⇓(P → C)`, derive `S⇓(P → ¬(A → ¬(¬(B → ¬C))))`. -/
noncomputable def combineImpConj3 {P A₁ B₁ C₁ : F}
    (hA : S⇓(HasImp.imp P A₁)) (hB : S⇓(HasImp.imp P B₁)) (hC : S⇓(HasImp.imp P C₁)) :
    S⇓(HasImp.imp P
      (HasImp.imp (HasImp.imp A₁
        (HasImp.imp (HasImp.imp (HasImp.imp B₁ (HasImp.imp C₁ HasBot.bot)) HasBot.bot)
          HasBot.bot))
        HasBot.bot)) :=
  (Theorems.Combinators.combine_imp_conj_3 (S := S)
    (DerivableIn.fromDerivation hA) (DerivableIn.fromDerivation hB)
    (DerivableIn.fromDerivation hC)).toDerivation

/-- Law of excluded middle (Lukasiewicz form): `S⇓(¬φ → ¬φ)`.
    Delegates to `neg_identity`, the identity combinator instantiated at `¬φ`. -/
noncomputable def lem (φ : F) :
    S⇓(HasImp.imp (HasImp.imp φ HasBot.bot) (HasImp.imp φ HasBot.bot)) :=
  (Theorems.Propositional.Core.neg_identity (S := S) (φ := φ)).toDerivation

/-- Contraposition (implication form): `S⇓((φ → ψ) → (¬ψ → ¬φ))`. -/
noncomputable def contraposeImp {φ ψ : F} :
    S⇓(HasImp.imp (HasImp.imp φ ψ)
      (HasImp.imp (HasImp.imp ψ HasBot.bot) (HasImp.imp φ HasBot.bot))) :=
  (Theorems.Propositional.Connectives.contrapose_imp (S := S) (φ := φ) (ψ := ψ)).toDerivation

/-- Contraposition (meta): from `S⇓(φ → ψ)`, derive `S⇓(¬ψ → ¬φ)`. -/
noncomputable def contraposition {φ ψ : F}
    (h : S⇓(HasImp.imp φ ψ)) :
    S⇓(HasImp.imp (HasImp.imp ψ HasBot.bot) (HasImp.imp φ HasBot.bot)) :=
  (Theorems.Propositional.Connectives.contraposition (S := S)
    (DerivableIn.fromDerivation h)).toDerivation

/-- Iff introduction: from `S⇓(φ → ψ)` and `S⇓(ψ → φ)`, derive `S⇓(φ ↔ ψ)`
    (Lukasiewicz-encoded conjunction of the two implications). -/
noncomputable def iffIntro {φ ψ : F}
    (h1 : S⇓(HasImp.imp φ ψ)) (h2 : S⇓(HasImp.imp ψ φ)) :
    S⇓(HasImp.imp
      (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp (HasImp.imp ψ φ) HasBot.bot))
      HasBot.bot) :=
  (Theorems.Propositional.Connectives.iff_intro (S := S)
    (DerivableIn.fromDerivation h1) (DerivableIn.fromDerivation h2)).toDerivation

/-- Iff neg intro: from `S⇓(¬φ → ¬ψ)` and `S⇓(¬ψ → ¬φ)`, derive `S⇓(¬φ ↔ ¬ψ)`. -/
noncomputable def iffNegIntro {φ ψ : F}
    (h1 : S⇓(HasImp.imp (HasImp.imp φ HasBot.bot) (HasImp.imp ψ HasBot.bot)))
    (h2 : S⇓(HasImp.imp (HasImp.imp ψ HasBot.bot) (HasImp.imp φ HasBot.bot))) :
    S⇓(HasImp.imp
      (HasImp.imp (HasImp.imp (HasImp.imp φ HasBot.bot) (HasImp.imp ψ HasBot.bot))
        (HasImp.imp (HasImp.imp (HasImp.imp ψ HasBot.bot) (HasImp.imp φ HasBot.bot))
          HasBot.bot))
      HasBot.bot) :=
  (Theorems.Propositional.Connectives.iff_neg_intro (S := S)
    (DerivableIn.fromDerivation h1) (DerivableIn.fromDerivation h2)).toDerivation

end Minimal

/-! ## Intuitionistic (`[IntuitionisticHilbert S]`) -/

section Intuitionistic

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [IntuitionisticHilbert S (F := F)]

/-- EFQ wrapper: `S⇓(⊥ → φ)`. -/
noncomputable def efqAxiom (φ : F) : S⇓(HasImp.imp HasBot.bot φ) :=
  (Theorems.Propositional.Core.efq_axiom (S := S) (φ := φ)).toDerivation

/-- Reductio ad absurdum: `S⇓(φ → (¬φ → ψ))`. -/
noncomputable def raa (φ ψ : F) :
    S⇓(HasImp.imp φ (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)) :=
  (Theorems.Propositional.Core.raa (S := S) (φ := φ) (ψ := ψ)).toDerivation

/-- Ex falso for negation: `S⇓(¬φ → (φ → ψ))`. -/
noncomputable def efqNeg (φ ψ : F) :
    S⇓(HasImp.imp (HasImp.imp φ HasBot.bot) (HasImp.imp φ ψ)) :=
  (Theorems.Propositional.Core.efq_neg (S := S) (φ := φ) (ψ := ψ)).toDerivation

end Intuitionistic

/-! ## Classical (`[ClassicalHilbert S]`) -/

section Classical

variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [ClassicalHilbert S (F := F)]

/-- Peirce's law wrapper: `S⇓(((φ → ψ) → φ) → φ)`. -/
noncomputable def peirceAxiom (φ ψ : F) :
    S⇓(HasImp.imp (HasImp.imp (HasImp.imp φ ψ) φ) φ) :=
  (Theorems.Propositional.Core.peirce_axiom (S := S) (φ := φ) (ψ := ψ)).toDerivation

/-- Double negation elimination: `S⇓(¬¬φ → φ)`. -/
noncomputable def doubleNegation (φ : F) :
    S⇓(HasImp.imp (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot) φ) :=
  (Theorems.Propositional.Core.double_negation (S := S) (φ := φ)).toDerivation

/-- Left conjunction elimination (DT-free): `S⇓((φ ∧ ψ) → φ)`. -/
noncomputable def lceImp (φ ψ : F) :
    S⇓(HasImp.imp
      (HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot) φ) :=
  (Theorems.Propositional.Core.lce_imp (S := S) (φ := φ) (ψ := ψ)).toDerivation

/-- Right conjunction elimination (DT-free): `S⇓((φ ∧ ψ) → ψ)`. -/
noncomputable def rceImp (φ ψ : F) :
    S⇓(HasImp.imp
      (HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot) ψ) :=
  (Theorems.Propositional.Core.rce_imp (S := S) (φ := φ) (ψ := ψ)).toDerivation

/-- Classical merge (DT-free): `S⇓((P → Q) → ((¬P → Q) → Q))`. -/
noncomputable def classicalMerge (P Q : F) :
    S⇓(HasImp.imp (HasImp.imp P Q)
      (HasImp.imp (HasImp.imp (HasImp.imp P HasBot.bot) Q) Q)) :=
  (Theorems.Propositional.Connectives.classical_merge (S := S) (φ := P) (ψ := Q)).toDerivation

/-- Contrapose iff: from `S⇓(φ ↔ ψ)`, derive `S⇓(¬φ ↔ ¬ψ)`. -/
noncomputable def contraposeIff {φ ψ : F}
    (h : S⇓(HasImp.imp
      (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp (HasImp.imp ψ φ) HasBot.bot))
      HasBot.bot)) :
    S⇓(HasImp.imp
      (HasImp.imp (HasImp.imp (HasImp.imp φ HasBot.bot) (HasImp.imp ψ HasBot.bot))
        (HasImp.imp (HasImp.imp (HasImp.imp ψ HasBot.bot) (HasImp.imp φ HasBot.bot))
          HasBot.bot))
      HasBot.bot) :=
  (Theorems.Propositional.Connectives.contrapose_iff (S := S)
    (DerivableIn.fromDerivation h)).toDerivation

/-- De Morgan 1 forward: `S⇓(¬(φ ∧ ψ) → (¬φ ∨ ¬ψ))`. -/
noncomputable def demorganConjNegForward (φ ψ : F) :
    S⇓(HasImp.imp
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot)
        HasBot.bot)
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
        (HasImp.imp ψ HasBot.bot))) :=
  (Theorems.Propositional.Connectives.demorgan_conj_neg_forward
    (S := S) (φ := φ) (ψ := ψ)).toDerivation

/-- De Morgan 1 backward: `S⇓((¬φ ∨ ¬ψ) → ¬(φ ∧ ψ))`. -/
noncomputable def demorganConjNegBackward (φ ψ : F) :
    S⇓(HasImp.imp
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot)
        (HasImp.imp ψ HasBot.bot))
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ (HasImp.imp ψ HasBot.bot)) HasBot.bot)
        HasBot.bot)) :=
  (Theorems.Propositional.Connectives.demorgan_conj_neg_backward
    (S := S) (φ := φ) (ψ := ψ)).toDerivation

/-- De Morgan 2 forward: `S⇓(¬(φ ∨ ψ) → (¬φ ∧ ¬ψ))`. -/
noncomputable def demorganDisjNegForward (φ ψ : F) :
    S⇓(HasImp.imp
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
        HasBot.bot)
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot)
          (HasImp.imp (HasImp.imp ψ HasBot.bot) HasBot.bot))
        HasBot.bot)) :=
  (Theorems.Propositional.Connectives.demorgan_disj_neg_forward
    (S := S) (φ := φ) (ψ := ψ)).toDerivation

/-- De Morgan 2 backward: `S⇓((¬φ ∧ ¬ψ) → ¬(φ ∨ ψ))`. -/
noncomputable def demorganDisjNegBackward (φ ψ : F) :
    S⇓(HasImp.imp
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot)
          (HasImp.imp (HasImp.imp ψ HasBot.bot) HasBot.bot))
        HasBot.bot)
      (HasImp.imp
        (HasImp.imp (HasImp.imp φ HasBot.bot) ψ)
        HasBot.bot)) :=
  (Theorems.Propositional.Connectives.demorgan_disj_neg_backward
    (S := S) (φ := φ) (ψ := ψ)).toDerivation

end Classical

end Cslib.Logic.Theorems.DerivationCombinators
