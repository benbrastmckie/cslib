/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Temporal.Syntax.Formula

/-! # Temporal Axiom Schemata (BX System)

This module defines the concrete axiom inductive type for temporal logic under the
Burgess-Xu (BX) axiom system. Each constructor maps directly to an axiom schema of the
BX temporal proof system.

## Organization

- `FrameClass`: Classification for axiom validity (Base, Dense, Discrete, Metric)
- `Axiom`: Inductive type with 26 constructors (4 propositional + 22 temporal), plus 2 density
  and 4 metric-uniformity constructors gated by `minFrameClass`
- `minFrameClass`: Minimum frame class for each axiom
-/

set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Temporal

open Cslib.Logic.Temporal

variable {Atom : Type u}

/--
Frame class classification for axiom validity.

- `Base`: all base axioms are valid on all linear orders
- `Dense`: extends Base with density axioms
- `Discrete`: extends Base with discreteness axioms
- `Metric`: extends Base with metric uniformity axioms, valid on ordered-abelian-group time
  (incomparable to `Dense`/`Discrete`)
-/
inductive FrameClass where
  | Base
  | Dense
  | Discrete
  | Metric
  deriving Repr, DecidableEq, Inhabited, BEq, Hashable

instance : LE FrameClass where
  le a b := match a, b with
    | .Base, _ => True
    | .Dense, .Dense => True
    | .Discrete, .Discrete => True
    | .Metric, .Metric => True
    | _, _ => False

instance : DecidableRel (LE.le : FrameClass → FrameClass → Prop) :=
  fun a b => by cases a <;> cases b <;> simp only [LE.le] <;> infer_instance

instance : PartialOrder FrameClass where
  le := (· ≤ ·)
  le_refl := by intro a; cases a <;> simp [LE.le]
  le_trans := by intro a b c hab hbc; cases a <;> cases b <;> cases c <;> simp_all [LE.le]
  le_antisymm := by intro a b hab hba; cases a <;> cases b <;> simp_all [LE.le]

/-- Base is the minimum frame class. -/
theorem FrameClass.base_le (fc : FrameClass) : FrameClass.Base ≤ fc := by
  cases fc <;> trivial

/--
Axiom schemata for temporal logic under the Burgess-Xu (BX) system.

Organized into layers:
- **Propositional** (4): Classical propositional tautologies
- **BX Temporal** (22): Burgess-Xu axioms for Until/Since on linear orders
- **Density** (2): Axioms valid on dense linear orders
- **Metric Uniformity** (4): Axioms valid on ordered-abelian-group time (`FrameClass.Metric`)
-/
inductive Axiom : Formula Atom → Type u where
  -- Layer 1: Propositional (4)

  /-- Propositional K (distribution): (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)) -/
  | imp_k (φ ψ χ : Formula Atom) :
      Axiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))

  /-- Propositional S (weakening): φ → (ψ → φ) -/
  | imp_s (φ ψ : Formula Atom) : Axiom (φ.imp (ψ.imp φ))

  /-- Ex Falso Quodlibet: ⊥ → φ -/
  | efq (φ : Formula Atom) : Axiom (Formula.bot.imp φ)

  /-- Peirce's Law: ((φ → ψ) → φ) → φ -/
  | peirce (φ ψ : Formula Atom) : Axiom (((φ.imp ψ).imp φ).imp φ)

  -- Layer 2: BX Temporal (22)

  /-- BX1: Serial future: ⊤ → F(⊤) -/
  | serial_future :
      Axiom (Formula.top.imp (Formula.someFuture Formula.top))

  /-- BX1': Serial past: ⊤ → P(⊤) -/
  | serial_past :
      Axiom (Formula.top.imp (Formula.somePast Formula.top))

  /-- BX2G: Guard monotonicity of Until under G:
      G(φ → ψ) → (φ U χ → ψ U χ) -/
  | left_mono_until_G (φ ψ χ : Formula Atom) :
      Axiom ((φ.imp ψ).allFuture.imp ((Formula.untl φ χ).imp (Formula.untl ψ χ)))

  /-- BX2H: Guard monotonicity of Since under H:
      H(φ → ψ) → (φ S χ → ψ S χ) -/
  | left_mono_since_H (φ ψ χ : Formula Atom) :
      Axiom ((φ.imp ψ).allPast.imp ((Formula.snce φ χ).imp (Formula.snce ψ χ)))

  /-- BX3: Event monotonicity of Until:
      G(φ → ψ) → (χ U φ → χ U ψ) -/
  | right_mono_until (φ ψ χ : Formula Atom) :
      Axiom ((φ.imp ψ).allFuture.imp ((Formula.untl χ φ).imp (Formula.untl χ ψ)))

  /-- BX3': Event monotonicity of Since:
      H(φ → ψ) → (χ S φ → χ S ψ) -/
  | right_mono_since (φ ψ χ : Formula Atom) :
      Axiom ((φ.imp ψ).allPast.imp ((Formula.snce χ φ).imp (Formula.snce χ ψ)))

  /-- BX4: Temporal connectedness future: φ → G(P(φ)) -/
  | connect_future (φ : Formula Atom) :
      Axiom (φ.imp (φ.somePast.allFuture))

  /-- BX4': Temporal connectedness past: φ → H(F(φ)) -/
  | connect_past (φ : Formula Atom) :
      Axiom (φ.imp (φ.someFuture.allPast))

  /-- BX13: Until-Since enrichment:
      p ∧ (φ U ψ) → φ U (ψ ∧ (φ S p)) -/
  | enrichment_until (φ ψ p : Formula Atom) :
      Axiom (Formula.and p (Formula.untl φ ψ) |>.imp
        (Formula.untl φ (Formula.and ψ (Formula.snce φ p))))

  /-- BX13': Since-Until enrichment:
      p ∧ (φ S ψ) → φ S (ψ ∧ (φ U p)) -/
  | enrichment_since (φ ψ p : Formula Atom) :
      Axiom (Formula.and p (Formula.snce φ ψ) |>.imp
        (Formula.snce φ (Formula.and ψ (Formula.untl φ p))))

  /-- BX5: Self-accumulation of Until:
      φ U ψ → (φ ∧ (φ U ψ)) U ψ -/
  | self_accum_until (φ ψ : Formula Atom) :
      Axiom ((Formula.untl φ ψ).imp
        (Formula.untl (Formula.and φ (Formula.untl φ ψ)) ψ))

  /-- BX5': Self-accumulation of Since:
      φ S ψ → (φ ∧ (φ S ψ)) S ψ -/
  | self_accum_since (φ ψ : Formula Atom) :
      Axiom ((Formula.snce φ ψ).imp
        (Formula.snce (Formula.and φ (Formula.snce φ ψ)) ψ))

  /-- BX6: Absorption of Until:
      φ U (φ ∧ (φ U ψ)) → φ U ψ -/
  | absorb_until (φ ψ : Formula Atom) :
      Axiom ((Formula.untl φ (Formula.and φ (Formula.untl φ ψ))).imp (Formula.untl φ ψ))

  /-- BX6': Absorption of Since:
      φ S (φ ∧ (φ S ψ)) → φ S ψ -/
  | absorb_since (φ ψ : Formula Atom) :
      Axiom ((Formula.snce φ (Formula.and φ (Formula.snce φ ψ))).imp (Formula.snce φ ψ))

  /-- BX7: Linearity of Until:
      U(φ,ψ) ∧ U(χ,θ) → U(φ∧χ,ψ∧θ) ∨ U(φ∧χ,ψ∧χ) ∨ U(φ∧χ,φ∧θ) -/
  | linear_until (φ ψ χ θ : Formula Atom) :
      Axiom (Formula.and (Formula.untl φ ψ) (Formula.untl χ θ)
        |>.imp (Formula.or
          (Formula.or
            (Formula.untl (Formula.and φ χ) (Formula.and ψ θ))
            (Formula.untl (Formula.and φ χ) (Formula.and ψ χ)))
          (Formula.untl (Formula.and φ χ) (Formula.and φ θ))))

  /-- BX7': Linearity of Since:
      S(φ,ψ) ∧ S(χ,θ) → S(φ∧χ,ψ∧θ) ∨ S(φ∧χ,ψ∧χ) ∨ S(φ∧χ,φ∧θ) -/
  | linear_since (φ ψ χ θ : Formula Atom) :
      Axiom (Formula.and (Formula.snce φ ψ) (Formula.snce χ θ)
        |>.imp (Formula.or
          (Formula.or
            (Formula.snce (Formula.and φ χ) (Formula.and ψ θ))
            (Formula.snce (Formula.and φ χ) (Formula.and ψ χ)))
          (Formula.snce (Formula.and φ χ) (Formula.and φ θ))))

  /-- BX10: Until implies eventuality: U(φ, ψ) → F(ψ) -/
  | until_F (φ ψ : Formula Atom) :
      Axiom ((Formula.untl φ ψ).imp (Formula.someFuture ψ))

  /-- BX10': Since implies past eventuality: S(φ, ψ) → P(ψ) -/
  | since_P (φ ψ : Formula Atom) :
      Axiom ((Formula.snce φ ψ).imp (Formula.somePast ψ))

  /-- BX11: Temporal linearity:
      F(φ) ∧ F(ψ) → F(φ ∧ ψ) ∨ F(φ ∧ F(ψ)) ∨ F(F(φ) ∧ ψ) -/
  | temp_linearity (φ ψ : Formula Atom) :
      Axiom (Formula.and (Formula.someFuture φ) (Formula.someFuture ψ) |>.imp
        (Formula.or (Formula.someFuture (Formula.and φ ψ))
          (Formula.or (Formula.someFuture (Formula.and φ (Formula.someFuture ψ)))
            (Formula.someFuture (Formula.and (Formula.someFuture φ) ψ)))))

  /-- BX11': Temporal linearity past:
      P(φ) ∧ P(ψ) → P(φ ∧ ψ) ∨ P(φ ∧ P(ψ)) ∨ P(P(φ) ∧ ψ) -/
  | temp_linearity_past (φ ψ : Formula Atom) :
      Axiom (Formula.and (Formula.somePast φ) (Formula.somePast ψ) |>.imp
        (Formula.or (Formula.somePast (Formula.and φ ψ))
          (Formula.or (Formula.somePast (Formula.and φ (Formula.somePast ψ)))
            (Formula.somePast (Formula.and (Formula.somePast φ) ψ)))))

  /-- BX12: F-Until equivalence: F(φ) → U(⊤, φ) -/
  | F_until_equiv (φ : Formula Atom) :
      Axiom ((Formula.someFuture φ).imp (Formula.untl Formula.top φ))

  /-- BX12': P-Since equivalence: P(φ) → S(⊤, φ) -/
  | P_since_equiv (φ : Formula Atom) :
      Axiom ((Formula.somePast φ).imp (Formula.snce Formula.top φ))

  -- Layer 3: Density (2)

  /-- Density axiom: G(G(φ)) → G(φ). Valid on densely ordered frames. -/
  | density (φ : Formula Atom) :
      Axiom (φ.allFuture.allFuture.imp φ.allFuture)

  /-- Dense indicator: ¬U(⊥, ⊤). Asserts no immediate successor exists.
      Valid on densely ordered frames. -/
  | dense_indicator :
      Axiom (Formula.untl Formula.bot Formula.top).neg

  -- Layer: Metric Uniformity (4)

  /-- Metric symmetry (fwd): U(⊥,⊤) → S(⊥,⊤). Immediate successor ⇒ immediate predecessor.
      Metric uniformity / homogeneity of ordered-abelian-group time (negation symmetry). -/
  | discrete_symm_fwd :
      Axiom ((Formula.untl Formula.bot Formula.top).imp
        (Formula.snce Formula.bot Formula.top))

  /-- Metric symmetry (bwd): S(⊥,⊤) → U(⊥,⊤). Immediate predecessor ⇒ immediate successor.
      Metric uniformity / homogeneity of ordered-abelian-group time (negation symmetry). -/
  | discrete_symm_bwd :
      Axiom ((Formula.snce Formula.bot Formula.top).imp
        (Formula.untl Formula.bot Formula.top))

  /-- Metric propagation (fwd): U(⊥,⊤) → G(U(⊥,⊤)). Metric uniformity / homogeneity of
      ordered-abelian-group time: translation-invariance forwards. -/
  | discrete_propagate_fwd :
      Axiom ((Formula.untl Formula.bot Formula.top).imp
        (Formula.allFuture (Formula.untl Formula.bot Formula.top)))

  /-- Metric propagation (bwd): U(⊥,⊤) → H(U(⊥,⊤)). Metric uniformity / homogeneity of
      ordered-abelian-group time: translation-invariance backwards. -/
  | discrete_propagate_bwd :
      Axiom ((Formula.untl Formula.bot Formula.top).imp
        (Formula.allPast (Formula.untl Formula.bot Formula.top)))

  -- Layer 4: G/H classical-equivalence bridge axioms (4)
  -- These connect the primitive `allFuture`/`allPast` constructors
  -- to the Foundation-level derived encodings `¬F¬φ` / `¬P¬φ`.

  /-- G-to-¬F¬ (bridge): allFuture φ → ¬(someFuture (¬φ)).
      Holds constructively: if φ holds at all future times, then
      there is no future time where ¬φ holds. -/
  | allFuture_to_classic (φ : Formula Atom) :
      Axiom (φ.allFuture.imp (Formula.neg (Formula.someFuture (Formula.neg φ))))

  /-- ¬F¬-to-G (bridge): ¬(someFuture (¬φ)) → allFuture φ.
      Requires classical logic (double-negation elimination);
      justified by Peirce's law in the BX axiom system. -/
  | classic_to_allFuture (φ : Formula Atom) :
      Axiom ((Formula.neg (Formula.someFuture (Formula.neg φ))).imp φ.allFuture)

  /-- H-to-¬P¬ (bridge): allPast φ → ¬(somePast (¬φ)).
      Holds constructively: if φ held at all past times, then
      there is no past time where ¬φ held. -/
  | allPast_to_classic (φ : Formula Atom) :
      Axiom (φ.allPast.imp (Formula.neg (Formula.somePast (Formula.neg φ))))

  /-- ¬P¬-to-H (bridge): ¬(somePast (¬φ)) → allPast φ.
      Requires classical logic; justified by Peirce's law in the BX system. -/
  | classic_to_allPast (φ : Formula Atom) :
      Axiom ((Formula.neg (Formula.somePast (Formula.neg φ))).imp φ.allPast)

set_option linter.dupNamespace false in
/-- Minimum frame class for each axiom constructor. Base BX axioms
    are valid on all linear temporal orders. Density axioms require
    densely ordered frames. -/
def Axiom.minFrameClass {φ : Formula Atom} :
    Cslib.Logic.Temporal.Axiom φ → FrameClass
  | .density _ => .Dense
  | .dense_indicator => .Dense
  | .discrete_symm_fwd => .Metric
  | .discrete_symm_bwd => .Metric
  | .discrete_propagate_fwd => .Metric
  | .discrete_propagate_bwd => .Metric
  | _ => .Base

end Cslib.Logic.Temporal
