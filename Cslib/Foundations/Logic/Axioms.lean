/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Connectives

/-! # Polymorphic Axiom Definitions

This module defines axiom formulas as polymorphic `abbrev`s parameterized over the connective
typeclasses. Each axiom is defined once and can be instantiated at any formula type with the
appropriate connectives.

## Organization

- **Propositional axioms**: `ImplyK`, `ImplyS`, `EFQ`, `Peirce`
  (require `HasBot`, `HasImp`)
- **Modal axioms**: `AxiomK`, `AxiomT`, `Axiom4`, `AxiomB`, `Axiom5`, `AxiomD`
  (require additionally `HasBox`)
- **Temporal axioms**: `SerialFuture`, `ConnectFuture`, etc.
  (require `HasUntil`, `HasSince`)
- **Interaction axiom**: `ModalFuture`
  (requires both `HasBox` and `HasUntil`)
-/

@[expose] public section

namespace Cslib.Logic.Axioms

variable {F : Type*}

/-! ### Shared Abbreviations -/

section Abbreviations
variable [HasBot F] [HasImp F]

/-- Top formula: ⊥ → ⊥ -/
abbrev top' : F := HasImp.imp (HasBot.bot : F) HasBot.bot

/-- Negation: φ → ⊥ -/
abbrev neg' (x : F) : F := HasImp.imp x HasBot.bot

/-- Lukasiewicz conjunction encoding: `¬(φ → ¬ψ)` = `(φ → (ψ → ⊥)) → ⊥`.

This is an **embedding-layer helper**, not a primary connective definition. It is used
specifically for formula types that lack a native `HasAnd` constructor (Modal, Temporal,
Bimodal formula types only have `{atom, bot, imp, box/until/since}`). The propositional
formula type `PL.Proposition` has a primitive `and` constructor and uses `HasAnd`/`HasOr`
directly. The Lukasiewicz encoding is classically equivalent to `∧`, but not
intuitionistically ([Wajsberg1938], [McKinsey1939]). -/
abbrev conj' (a b : F) : F :=
  HasImp.imp (HasImp.imp a (neg' b)) HasBot.bot

/-- Lukasiewicz disjunction encoding: `¬φ → ψ` = `(φ → ⊥) → ψ`.

This is an **embedding-layer helper**, not a primary connective definition. It is used
specifically for formula types that lack a native `HasOr` constructor (Modal, Temporal,
Bimodal formula types). The propositional formula type `PL.Proposition` has a primitive
`or` constructor and uses `HasOr` directly. The Lukasiewicz encoding is classically
equivalent to `∨`, but not intuitionistically ([Wajsberg1938], [McKinsey1939]). -/
abbrev disj' (a b : F) : F :=
  HasImp.imp (neg' a) b

end Abbreviations

/-! ### Propositional Axioms -/

section Propositional
variable [HasBot F] [HasImp F]

/-- K axiom for implication: φ → (ψ → φ) -/
protected abbrev ImplyK (φ ψ : F) : F :=
  HasImp.imp φ (HasImp.imp ψ φ)

/-- S axiom for implication: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)) -/
protected abbrev ImplyS (φ ψ χ : F) : F :=
  HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
    (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ))

/-- Ex falso quodlibet: ⊥ → φ -/
protected abbrev EFQ (φ : F) : F :=
  HasImp.imp HasBot.bot φ

/-- Peirce's law (classical): ((φ → ψ) → φ) → φ -/
protected abbrev Peirce (φ ψ : F) : F :=
  HasImp.imp (HasImp.imp (HasImp.imp φ ψ) φ) φ

/-- Double negation elimination: ¬¬φ → φ
    where ¬φ = φ → ⊥.

    Note: `DNE` is defined here as a formula for completeness of the axiom inventory.
    However, it is not separately axiomatized in `ClassicalHilbert`: it is derived from
    Peirce's law via modus ponens. That is, `ClassicalHilbert` takes Peirce as the classical
    axiom, and DNE follows as a theorem rather than an additional axiom. -/
protected abbrev DNE (φ : F) : F :=
  HasImp.imp (HasImp.imp (HasImp.imp φ HasBot.bot) HasBot.bot) φ

end Propositional

/-! ### And/Or Axioms -/

section AndOrAxioms
variable [HasAnd F] [HasOr F] [HasBot F] [HasImp F]

/-- Conjunction introduction: φ → (ψ → φ ∧ ψ) -/
protected abbrev AndI (φ ψ : F) : F :=
  HasImp.imp φ (HasImp.imp ψ (HasAnd.and φ ψ))

/-- Left conjunction elimination: φ ∧ ψ → φ -/
protected abbrev AndE1 (φ ψ : F) : F :=
  HasImp.imp (HasAnd.and φ ψ) φ

/-- Right conjunction elimination: φ ∧ ψ → ψ -/
protected abbrev AndE2 (φ ψ : F) : F :=
  HasImp.imp (HasAnd.and φ ψ) ψ

/-- Left disjunction introduction: φ → φ ∨ ψ -/
protected abbrev OrI1 (φ ψ : F) : F :=
  HasImp.imp φ (HasOr.or φ ψ)

/-- Right disjunction introduction: ψ → φ ∨ ψ -/
protected abbrev OrI2 (φ ψ : F) : F :=
  HasImp.imp ψ (HasOr.or φ ψ)

/-- Disjunction elimination: (φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ)) -/
protected abbrev OrE (φ ψ χ : F) : F :=
  HasImp.imp (HasImp.imp φ χ)
    (HasImp.imp (HasImp.imp ψ χ)
      (HasImp.imp (HasOr.or φ ψ) χ))

end AndOrAxioms

/-! ### Modal Axioms -/

section Modal
variable [HasBot F] [HasImp F] [HasBox F]

/-- Distribution axiom K: □(φ → ψ) → (□φ → □ψ) -/
protected abbrev AxiomK (φ ψ : F) : F :=
  HasImp.imp (HasBox.box (HasImp.imp φ ψ))
    (HasImp.imp (HasBox.box φ) (HasBox.box ψ))

/-- Reflexivity axiom T: □φ → φ -/
protected abbrev AxiomT (φ : F) : F :=
  HasImp.imp (HasBox.box φ) φ

/-- Transitivity axiom 4: □φ → □□φ -/
protected abbrev Axiom4 (φ : F) : F :=
  HasImp.imp (HasBox.box φ) (HasBox.box (HasBox.box φ))

/-- Symmetry axiom B: `φ → □◇φ`.

Diamond is encoded classically as `◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`, since `ModalConnectives`
does not include `HasDiamond`. For proof systems with a primitive `HasDiamond`, the conjunction of
`AxiomDiaDualityFwd` and `AxiomDiaDualityBack` establishes the duality. The encoding here
relies on excluded middle and is equivalent to the standard `φ → □◇φ` only in classical logic.
Corresponds to symmetry of the accessibility relation: `r w v → r v w`. See [Blackburn2001]
Section 1.4, [ChagrovZakharyaschev1997] Section 3.2. -/
protected abbrev AxiomB (φ : F) : F :=
  HasImp.imp φ (HasBox.box
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))

/-- Euclidean axiom 5: `◇φ → □◇φ`.

Diamond is encoded classically as `◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`, since `ModalConnectives`
does not include `HasDiamond`. For proof systems with a primitive `HasDiamond`, the conjunction of
`AxiomDiaDualityFwd` and `AxiomDiaDualityBack` establishes the duality. The encoding here
relies on excluded middle and is equivalent to the standard `◇φ → □◇φ` only in classical logic.
Corresponds to right-Euclideanness of the accessibility relation: `r w v → r w u → r v u`.
See [Blackburn2001] Section 1.4, [ChagrovZakharyaschev1997] Section 3.2. -/
protected abbrev Axiom5 (φ : F) : F :=
  HasImp.imp
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
    (HasBox.box (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot))

/-- Seriality axiom D: `□φ → ◇φ`.

Diamond is encoded classically as `◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`, since `ModalConnectives`
does not include `HasDiamond`. For proof systems with a primitive `HasDiamond`, the conjunction of
`AxiomDiaDualityFwd` and `AxiomDiaDualityBack` establishes the duality. The encoding here
relies on excluded middle and is equivalent to the standard `□φ → ◇φ` only in classical logic.
Corresponds to seriality of the accessibility relation: `∀ w, ∃ v, r w v`. See [Blackburn2001]
Section 1.4, [ChagrovZakharyaschev1997] Section 3.2. -/
protected abbrev AxiomD (φ : F) : F :=
  HasImp.imp (HasBox.box φ)
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)

end Modal

/-! ### Diamond Duality Axiom -/

section DiaDuality
variable [HasBot F] [HasImp F] [HasBox F] [HasDiamond F]

/-- Diamond duality, forward direction: `◇φ → ¬□¬φ`.

In classical modal logic, possibility is defined as `◇φ := ¬□¬φ`. When `HasDiamond` is a
separate primitive, this axiom asserts that `◇φ` implies the classical encoding.
Together with `AxiomDiaDualityBack`, it establishes full duality. See `AxiomDiaDualityBack`
for the converse. -/
protected abbrev AxiomDiaDualityFwd (φ : F) : F :=
  HasImp.imp (HasDiamond.diamond φ)
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)

/-- Diamond duality, backward direction: `¬□¬φ → ◇φ`.

Together with `AxiomDiaDualityFwd`, establishes that `◇φ ↔ ¬□¬φ`. In classical systems
the two axioms are needed to reduce a primitive diamond to the derived classical encoding.
See [Blackburn2001] Section 1.1 for discussion of diamond-first vs box-first presentations. -/
protected abbrev AxiomDiaDualityBack (φ : F) : F :=
  HasImp.imp
    (HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot)
    (HasDiamond.diamond φ)

end DiaDuality

/-! ### Temporal Axioms -/

section Temporal
variable [HasBot F] [HasImp F] [HasUntil F] [HasSince F]

/-- Serial future (BX1): ⊤ → F ⊤
    where ⊤ = ⊥ → ⊥, F φ = ⊤ U φ -/
protected abbrev SerialFuture : F :=
  HasImp.imp top' (HasUntil.untl top' top')

/-- Serial past (BX1'): ⊤ → P ⊤
    where P φ = ⊤ S φ -/
protected abbrev SerialPast : F :=
  HasImp.imp top' (HasSince.snce top' top')

/-- Guard monotonicity of Until under G (BX2G):
    G(φ → ψ) → (χ U φ → χ U ψ)
    where G(α) = ¬(⊤ U ¬α) -/
protected abbrev LeftMonoUntilG (φ ψ χ : F) : F :=
  let G_imp := HasImp.imp (HasUntil.untl top' (neg' (HasImp.imp φ ψ))) HasBot.bot
  HasImp.imp G_imp
    (HasImp.imp (HasUntil.untl φ χ) (HasUntil.untl ψ χ))

/-- Guard monotonicity of Since under H (BX2H):
    H(φ → ψ) → (χ S φ → χ S ψ)
    where H(α) = ¬(⊤ S ¬α) -/
protected abbrev LeftMonoSinceH (φ ψ χ : F) : F :=
  let H_imp := HasImp.imp (HasSince.snce top' (neg' (HasImp.imp φ ψ))) HasBot.bot
  HasImp.imp H_imp
    (HasImp.imp (HasSince.snce φ χ) (HasSince.snce ψ χ))

/-- Event monotonicity of Until (BX3):
    G(φ → ψ) → (φ U χ → ψ U χ)
    where G(α) = ¬(⊤ U ¬α) -/
protected abbrev RightMonoUntil (φ ψ χ : F) : F :=
  let G_imp := HasImp.imp (HasUntil.untl top' (neg' (HasImp.imp φ ψ))) HasBot.bot
  HasImp.imp G_imp
    (HasImp.imp (HasUntil.untl χ φ) (HasUntil.untl χ ψ))

/-- Event monotonicity of Since (BX3'):
    H(φ → ψ) → (φ S χ → ψ S χ)
    where H(α) = ¬(⊤ S ¬α) -/
protected abbrev RightMonoSince (φ ψ χ : F) : F :=
  let H_imp := HasImp.imp (HasSince.snce top' (neg' (HasImp.imp φ ψ))) HasBot.bot
  HasImp.imp H_imp
    (HasImp.imp (HasSince.snce χ φ) (HasSince.snce χ ψ))

/-- Temporal connectedness future (BX4): φ → G(P(φ))
    where P(α) = ⊤ S α, G(α) = ¬(⊤ U ¬α) -/
protected abbrev ConnectFuture (φ : F) : F :=
  let P_φ := HasSince.snce top' φ
  let G_P_φ := HasImp.imp (HasUntil.untl top' (neg' P_φ)) HasBot.bot
  HasImp.imp φ G_P_φ

/-- Temporal connectedness past (BX4'): φ → H(F(φ))
    where F(α) = ⊤ U α, H(α) = ¬(⊤ S ¬α) -/
protected abbrev ConnectPast (φ : F) : F :=
  let F_φ := HasUntil.untl top' φ
  let H_F_φ := HasImp.imp (HasSince.snce top' (neg' F_φ)) HasBot.bot
  HasImp.imp φ H_F_φ

/-- Until-Since enrichment (BX13):
    p ∧ (ψ U φ) → (ψ ∧ S(p, φ)) U φ
    where ∧ is Lukasiewicz conjunction -/
protected abbrev EnrichmentUntil (φ ψ p : F) : F :=
  HasImp.imp (conj' p (HasUntil.untl φ ψ))
    (HasUntil.untl φ (conj' ψ (HasSince.snce φ p)))

/-- Since-Until enrichment (BX13'):
    p ∧ (ψ S φ) → (ψ ∧ U(p, φ)) S φ -/
protected abbrev EnrichmentSince (φ ψ p : F) : F :=
  HasImp.imp (conj' p (HasSince.snce φ ψ))
    (HasSince.snce φ (conj' ψ (HasUntil.untl φ p)))

/-- Self-accumulation of Until (BX5):
    U(ψ, φ) → U(ψ, φ ∧ U(ψ, φ)) -/
protected abbrev SelfAccumUntil (φ ψ : F) : F :=
  HasImp.imp (HasUntil.untl φ ψ)
    (HasUntil.untl (conj' φ (HasUntil.untl φ ψ)) ψ)

/-- Self-accumulation of Since (BX5'):
    S(ψ, φ) → S(ψ, φ ∧ S(ψ, φ)) -/
protected abbrev SelfAccumSince (φ ψ : F) : F :=
  HasImp.imp (HasSince.snce φ ψ)
    (HasSince.snce (conj' φ (HasSince.snce φ ψ)) ψ)

/-- Absorption of Until (BX6):
    U(φ ∧ U(ψ, φ), φ) → U(ψ, φ) -/
protected abbrev AbsorbUntil (φ ψ : F) : F :=
  HasImp.imp (HasUntil.untl φ (conj' φ (HasUntil.untl φ ψ)))
    (HasUntil.untl φ ψ)

/-- Absorption of Since (BX6'):
    S(φ ∧ S(ψ, φ), φ) → S(ψ, φ) -/
protected abbrev AbsorbSince (φ ψ : F) : F :=
  HasImp.imp (HasSince.snce φ (conj' φ (HasSince.snce φ ψ)))
    (HasSince.snce φ ψ)

/-- Linearity of Until (BX7):
    U(ψ,φ) ∧ U(θ,χ) → U(ψ∧θ, φ∧χ) ∨ U(ψ∧χ, φ∧χ) ∨ U(φ∧θ, φ∧χ) -/
protected abbrev LinearUntil (φ ψ χ θ : F) : F :=
  HasImp.imp (conj' (HasUntil.untl φ ψ) (HasUntil.untl χ θ))
    (disj' (disj' (HasUntil.untl (conj' φ χ) (conj' ψ θ))
                  (HasUntil.untl (conj' φ χ) (conj' ψ χ)))
           (HasUntil.untl (conj' φ χ) (conj' φ θ)))

/-- Linearity of Since (BX7'):
    S(ψ,φ) ∧ S(θ,χ) → S(ψ∧θ, φ∧χ) ∨ S(ψ∧χ, φ∧χ) ∨ S(φ∧θ, φ∧χ) -/
protected abbrev LinearSince (φ ψ χ θ : F) : F :=
  HasImp.imp (conj' (HasSince.snce φ ψ) (HasSince.snce χ θ))
    (disj' (disj' (HasSince.snce (conj' φ χ) (conj' ψ θ))
                  (HasSince.snce (conj' φ χ) (conj' ψ χ)))
           (HasSince.snce (conj' φ χ) (conj' φ θ)))

/-- Until implies eventuality (BX10):
    U(ψ, φ) → F(ψ)
    where F(α) = ⊤ U α -/
protected abbrev UntilF (φ ψ : F) : F :=
  HasImp.imp (HasUntil.untl φ ψ) (HasUntil.untl top' ψ)

/-- Since implies past eventuality (BX10'):
    S(ψ, φ) → P(ψ)
    where P(α) = α S ⊤ -/
protected abbrev SinceP (φ ψ : F) : F :=
  HasImp.imp (HasSince.snce φ ψ) (HasSince.snce top' ψ)

/-- Temporal linearity (BX11):
    F(φ) ∧ F(ψ) → F(φ ∧ ψ) ∨ F(φ ∧ F(ψ)) ∨ F(F(φ) ∧ ψ) -/
protected abbrev TempLinearity (φ ψ : F) : F :=
  let F' := fun (x : F) => HasUntil.untl top' x
  HasImp.imp (conj' (F' φ) (F' ψ))
    (disj' (F' (conj' φ ψ))
      (disj' (F' (conj' φ (F' ψ)))
             (F' (conj' (F' φ) ψ))))

/-- Temporal linearity past (BX11'):
    P(φ) ∧ P(ψ) → P(φ ∧ ψ) ∨ P(φ ∧ P(ψ)) ∨ P(P(φ) ∧ ψ) -/
protected abbrev TempLinearityPast (φ ψ : F) : F :=
  let P' := fun (x : F) => HasSince.snce top' x
  HasImp.imp (conj' (P' φ) (P' ψ))
    (disj' (P' (conj' φ ψ))
      (disj' (P' (conj' φ (P' ψ)))
             (P' (conj' (P' φ) ψ))))

/-- F-Until equivalence (BX12):
    F(φ) → U(φ, ⊤)
    where F(α) = ⊤ U α.
    Note: Under the Burgess 1982 convention, this is trivially F(φ) → F(φ). -/
protected abbrev FUntilEquiv (φ : F) : F :=
  HasImp.imp (HasUntil.untl top' φ) (HasUntil.untl top' φ)

/-- P-Since equivalence (BX12'):
    P(φ) → S(φ, ⊤)
    Note: Under the Burgess 1982 convention, this is trivially P(φ) → P(φ). -/
protected abbrev PSinceEquiv (φ : F) : F :=
  HasImp.imp (HasSince.snce top' φ) (HasSince.snce top' φ)

end Temporal

/-! ### Interaction Axioms -/

section Interaction
variable [HasBot F] [HasImp F] [HasBox F] [HasUntil F]

/-- Modal-future interaction axiom MF: □φ → □(Gφ)
    where G φ = ¬F(¬φ) = ¬(⊤ U ¬φ)
    Necessary truths remain necessary in the future. -/
protected abbrev ModalFuture (φ : F) : F :=
  let G_φ := HasImp.imp (HasUntil.untl top' (neg' φ)) HasBot.bot
  HasImp.imp (HasBox.box φ) (HasBox.box G_φ)

end Interaction

end Cslib.Logic.Axioms
