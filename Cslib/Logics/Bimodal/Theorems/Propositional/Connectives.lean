/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.ProofSystem.Instances
public import Cslib.Logics.Bimodal.Theorems.Propositional.Core
public import Cslib.Foundations.Logic.Theorems.Propositional.Connectives

/-!
# Derived Connective Reasoning

Classical merge, iff introduction/elimination, contraposition, and De Morgan laws
for the Hilbert-style proof system.

Theorems involving only imp/neg/bot delegate to the generic Foundations equivalents
via the wrap/unwrap bridge pattern.  Theorems involving primitive `Formula.and` or
`Formula.or` constructors are proved directly from the Bimodal axioms, since
`Formula.and`/`Formula.or` are primitive constructors (not Lukasiewicz encodings).

Ported from BimodalLogic/Theories/Bimodal/Theorems/Propositional/Connectives.lean
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Theorems.Propositional

open Cslib.Logic
open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.Perpetuity (wrap unwrap)

variable {Atom : Type*}

noncomputable section

-- wrap' and unwrap' are aliases for the canonical wrap/unwrap from Perpetuity.Helpers
abbrev wrap' {φ : Formula Atom}
    (d : DerivationTree FrameClass.Base [] φ) :
    InferenceSystem.DerivableIn Bimodal.HilbertTM φ := wrap d

abbrev unwrap' {φ : Formula Atom}
    (h : InferenceSystem.DerivableIn Bimodal.HilbertTM φ) :
    DerivationTree FrameClass.Base [] φ := unwrap h

def classicalMerge (Q R : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Q.imp R).imp ((Q.neg.imp R).imp R)) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.classical_merge
    _ _ _ Bimodal.HilbertTM _ _ (φ := Q) (ψ := R))

/-- Iff introduction: from `⊢ A → B` and `⊢ B → A`, derive `⊢ (A → B) ∧ (B → A)`.
    Uses the primitive `Formula.and` constructor directly via `HasAxiomAndI`. -/
def iffIntro (A B : Formula Atom)
    (h1 : DerivationTree FrameClass.Base [] (A.imp B))
    (h2 : DerivationTree FrameClass.Base [] (B.imp A)) :
    DerivationTree FrameClass.Base [] ((A.imp B).and (B.imp A)) :=
  -- andI_ax : ⊢ (A→B) → ((B→A) → (A→B) ∧ (B→A))
  let andI_ax := DerivationTree.lift (FrameClass.base_le FrameClass.Base)
    (unwrap (HasAxiomAndI.andI (φ := A.imp B) (ψ := B.imp A) :
      InferenceSystem.DerivableIn Bimodal.HilbertTM _))
  let step1 := DerivationTree.modus_ponens [] _ _ andI_ax h1
  DerivationTree.modus_ponens [] _ _ step1 h2

def iffElimLeft (A B : Formula Atom) :
    DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] B := by
  have h_a : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] A := by
    apply DerivationTree.assumption; simp
  have h_imp : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] (A.imp B) := by
    have lce_inst := lce (A.imp B) (B.imp A)
    exact DerivationTree.weakening [(A.imp B).and (B.imp A)] _ _ lce_inst
      (by intro x; simp; intro h; left; exact h)
  exact DerivationTree.modus_ponens _ _ _ h_imp h_a

def iffElimRight (A B : Formula Atom) :
    DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] A := by
  have h_b : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] B := by
    apply DerivationTree.assumption; simp
  have h_imp : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] (B.imp A) := by
    have rce_inst := rce (A.imp B) (B.imp A)
    exact DerivationTree.weakening [(A.imp B).and (B.imp A)] _ _ rce_inst
      (by intro x; simp; intro h; left; exact h)
  exact DerivationTree.modus_ponens _ _ _ h_imp h_b

def contraposeImp (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.contrapose_imp
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B))

def contraposition {A B : Formula Atom}
    (h : DerivationTree FrameClass.Base [] (A.imp B)) :
    DerivationTree FrameClass.Base [] (B.neg.imp A.neg) :=
  unwrap' (@_root_.Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    _ _ _ Bimodal.HilbertTM _ _ (φ := A) (ψ := B) (wrap' h))

/-- Contrapose iff: from `⊢ (A → B) ∧ (B → A)`, derive `⊢ (¬A → ¬B) ∧ (¬B → ¬A)`.
    Uses lceImp/rceImp to extract components, then contraposition, then iffIntro. -/
def contraposeIff (A B : Formula Atom)
    (h : DerivationTree FrameClass.Base [] ((A.imp B).and (B.imp A))) :
    DerivationTree FrameClass.Base [] ((A.neg.imp B.neg).and (B.neg.imp A.neg)) :=
  let h1 := DerivationTree.modus_ponens [] _ _ (lceImp (A.imp B) (B.imp A)) h
  let h2 := DerivationTree.modus_ponens [] _ _ (rceImp (A.imp B) (B.imp A)) h
  -- h1 : ⊢ A → B,  h2 : ⊢ B → A
  -- contraposition h1 : ⊢ ¬B → ¬A,  contraposition h2 : ⊢ ¬A → ¬B
  iffIntro A.neg B.neg (contraposition h2) (contraposition h1)

/-- Iff neg intro: from `⊢ ¬A → ¬B` and `⊢ ¬B → ¬A`, derive `⊢ (¬A → ¬B) ∧ (¬B → ¬A)`. -/
def iffNegIntro (A B : Formula Atom)
    (h1 : DerivationTree FrameClass.Base [] (A.neg.imp B.neg))
    (h2 : DerivationTree FrameClass.Base [] (B.neg.imp A.neg)) :
    DerivationTree FrameClass.Base [] ((A.neg.imp B.neg).and (B.neg.imp A.neg)) :=
  iffIntro A.neg B.neg h1 h2

/-! ## De Morgan Laws

These are proved directly from the Bimodal axioms because `Formula.and`/`Formula.or`
are primitive constructors (not Lukasiewicz encodings). -/

/-- De Morgan 1 forward: `⊢ ¬(A ∧ B) → (¬A ∨ ¬B)`.

Proof strategy:
1. Prove `⊢ ¬(A∧B) → A → ¬B` using the andI axiom and B/flip combinators.
2. Compose with `¬B → ¬A∨¬B` (orI2) to get `⊢ ¬(A∧B) → A → ¬A∨¬B`.
3. Also derive `⊢ ¬A → ¬A∨¬B` (orI1).
4. Use classicalMerge on A to combine both cases. -/
def demorganConjNegForward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.and B).neg.imp (A.neg.or B.neg)) := by
  -- Step 1a: bCombinator B (A∧B) ⊥ : ⊢ (A∧B→⊥) → (B→A∧B) → B→⊥
  have bC_1 : DerivationTree FrameClass.Base []
      ((A.and B |>.imp Formula.bot).imp ((B.imp (A.and B)).imp (B.imp Formula.bot))) :=
    @bCombinator Atom FrameClass.Base B (A.and B) Formula.bot
  -- Step 1b: flip_bC_1 : ⊢ (B→A∧B) → (A∧B→⊥) → B→⊥
  have flip_inst1 : DerivationTree FrameClass.Base []
      (((A.and B |>.imp Formula.bot).imp ((B.imp (A.and B)).imp (B.imp Formula.bot))).imp
        ((B.imp (A.and B)).imp ((A.and B |>.imp Formula.bot).imp (B.imp Formula.bot)))) :=
    @flip Atom FrameClass.Base (A.and B |>.imp Formula.bot) (B.imp (A.and B))
      (B.imp Formula.bot)
  have flip_bC_1 : DerivationTree FrameClass.Base []
      ((B.imp (A.and B)).imp ((A.and B |>.imp Formula.bot).imp (B.imp Formula.bot))) :=
    DerivationTree.modus_ponens [] _ _ flip_inst1 bC_1
  -- Step 1c: bCombinator A (B→A∧B) ((A∧B→⊥)→B→⊥):
  --   ⊢ ((B→A∧B)→(A∧B→⊥)→B→⊥) → (A→B→A∧B) → (A→(A∧B→⊥)→B→⊥)
  have bC_2 : DerivationTree FrameClass.Base []
      (((B.imp (A.and B)).imp ((A.and B |>.imp Formula.bot).imp (B.imp Formula.bot))).imp
        ((A.imp (B.imp (A.and B))).imp (A.imp ((A.and B |>.imp Formula.bot).imp (B.imp Formula.bot))))) :=
    @bCombinator Atom FrameClass.Base A (B.imp (A.and B))
      ((A.and B |>.imp Formula.bot).imp (B.imp Formula.bot))
  have step_bC_2 : DerivationTree FrameClass.Base []
      ((A.imp (B.imp (A.and B))).imp (A.imp ((A.and B |>.imp Formula.bot).imp (B.imp Formula.bot)))) :=
    DerivationTree.modus_ponens [] _ _ bC_2 flip_bC_1
  -- pairing A B : ⊢ A → B → A∧B
  have pairing_AB : DerivationTree FrameClass.Base [] (A.imp (B.imp (A.and B))) :=
    pairing A B
  -- step2 : ⊢ A → (A∧B→⊥) → B→⊥
  have step2 : DerivationTree FrameClass.Base []
      (A.imp ((A.and B |>.imp Formula.bot).imp (B.imp Formula.bot))) :=
    DerivationTree.modus_ponens [] _ _ step_bC_2 pairing_AB
  -- Step 1 result: nconj_a_nb : ⊢ (A∧B→⊥) → A → B→⊥
  have flip_inst2 : DerivationTree FrameClass.Base []
      ((A.imp ((A.and B |>.imp Formula.bot).imp (B.imp Formula.bot))).imp
        ((A.and B |>.imp Formula.bot).imp (A.imp (B.imp Formula.bot)))) :=
    @flip Atom FrameClass.Base A (A.and B |>.imp Formula.bot) (B.imp Formula.bot)
  have nconj_a_nb : DerivationTree FrameClass.Base []
      ((A.and B).neg.imp (A.imp B.neg)) :=
    DerivationTree.modus_ponens [] _ _ flip_inst2 step2
  -- Step 2: nb_to_res : ⊢ ¬B → ¬A∨¬B  (orI2)
  have nb_to_res : DerivationTree FrameClass.Base [] (B.neg.imp (A.neg.or B.neg)) :=
    DerivationTree.axiom [] _ (Axiom.orI2 A.neg B.neg) trivial
  -- Step 3: nconj_a_res : ⊢ ¬(A∧B) → A → ¬A∨¬B
  --   = bCombinator A B.neg (¬A∨¬B) applied to nb_to_res, then compose with nconj_a_nb
  have bC_3 : DerivationTree FrameClass.Base []
      ((B.neg.imp (A.neg.or B.neg)).imp
        ((A.imp B.neg).imp (A.imp (A.neg.or B.neg)))) :=
    @bCombinator Atom FrameClass.Base A B.neg (A.neg.or B.neg)
  have a_nb_to_res : DerivationTree FrameClass.Base []
      ((A.imp B.neg).imp (A.imp (A.neg.or B.neg))) :=
    DerivationTree.modus_ponens [] _ _ bC_3 nb_to_res
  have nconj_a_res : DerivationTree FrameClass.Base []
      ((A.and B).neg.imp (A.imp (A.neg.or B.neg))) :=
    impTrans nconj_a_nb a_nb_to_res
  -- Step 4: na_to_res : ⊢ ¬A → ¬A∨¬B  (orI1)
  have na_to_res : DerivationTree FrameClass.Base [] (A.neg.imp (A.neg.or B.neg)) :=
    DerivationTree.axiom [] _ (Axiom.orI1 A.neg B.neg) trivial
  -- Step 5: na_to_res_const : ⊢ ¬(A∧B) → ¬A → ¬A∨¬B
  --   (weaken na_to_res with K-axiom under ¬(A∧B))
  have k_ax : DerivationTree FrameClass.Base []
      ((A.neg.imp (A.neg.or B.neg)).imp
        ((A.and B).neg.imp (A.neg.imp (A.neg.or B.neg)))) :=
    DerivationTree.axiom [] _ (Axiom.imp_s (A.neg.imp (A.neg.or B.neg)) (A.and B).neg) trivial
  have na_to_res_const : DerivationTree FrameClass.Base []
      ((A.and B).neg.imp (A.neg.imp (A.neg.or B.neg))) :=
    DerivationTree.modus_ponens [] _ _ k_ax na_to_res
  -- Step 6: use classicalMerge A (¬A∨¬B) to combine case A and case ¬A
  -- cm : ⊢ (A → ¬A∨¬B) → ((¬A → ¬A∨¬B) → ¬A∨¬B)
  have cm : DerivationTree FrameClass.Base []
      ((A.imp (A.neg.or B.neg)).imp ((A.neg.imp (A.neg.or B.neg)).imp (A.neg.or B.neg))) :=
    classicalMerge A (A.neg.or B.neg)
  -- bCombinator ¬(A∧B) (A→¬A∨¬B) ((¬A→¬A∨¬B)→¬A∨¬B):
  -- ⊢ ((A→¬A∨¬B)→(¬A→¬A∨¬B)→¬A∨¬B) → (¬(A∧B)→A→¬A∨¬B) → (¬(A∧B)→(¬A→¬A∨¬B)→¬A∨¬B)
  have bC_4 : DerivationTree FrameClass.Base []
      (((A.imp (A.neg.or B.neg)).imp ((A.neg.imp (A.neg.or B.neg)).imp (A.neg.or B.neg))).imp
        (((A.and B).neg.imp (A.imp (A.neg.or B.neg))).imp
          ((A.and B).neg.imp ((A.neg.imp (A.neg.or B.neg)).imp (A.neg.or B.neg))))) :=
    @bCombinator Atom FrameClass.Base (A.and B).neg (A.imp (A.neg.or B.neg))
      ((A.neg.imp (A.neg.or B.neg)).imp (A.neg.or B.neg))
  have cm_lifted : DerivationTree FrameClass.Base []
      (((A.and B).neg.imp (A.imp (A.neg.or B.neg))).imp
        ((A.and B).neg.imp ((A.neg.imp (A.neg.or B.neg)).imp (A.neg.or B.neg)))) :=
    DerivationTree.modus_ponens [] _ _ bC_4 cm
  have cm_applied : DerivationTree FrameClass.Base []
      ((A.and B).neg.imp ((A.neg.imp (A.neg.or B.neg)).imp (A.neg.or B.neg))) :=
    DerivationTree.modus_ponens [] _ _ cm_lifted nconj_a_res
  -- Final: imp_k (¬(A∧B)) (¬A→¬A∨¬B) (¬A∨¬B) applied to cm_applied and na_to_res_const
  have s_ax : DerivationTree FrameClass.Base []
      (((A.and B).neg.imp ((A.neg.imp (A.neg.or B.neg)).imp (A.neg.or B.neg))).imp
        (((A.and B).neg.imp (A.neg.imp (A.neg.or B.neg))).imp
          ((A.and B).neg.imp (A.neg.or B.neg)))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_k (A.and B).neg (A.neg.imp (A.neg.or B.neg)) (A.neg.or B.neg)) trivial
  have step_final : DerivationTree FrameClass.Base []
      (((A.and B).neg.imp (A.neg.imp (A.neg.or B.neg))).imp
        ((A.and B).neg.imp (A.neg.or B.neg))) :=
    DerivationTree.modus_ponens [] _ _ s_ax cm_applied
  exact DerivationTree.modus_ponens [] _ _ step_final na_to_res_const

/-- De Morgan 1 backward: `⊢ (¬A ∨ ¬B) → ¬(A ∧ B)`.

Uses contraposition of andE1/andE2 to get `¬A → ¬(A∧B)` and `¬B → ¬(A∧B)`,
then orE to combine. -/
def demorganConjNegBackward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.neg.or B.neg).imp (A.and B).neg) := by
  -- andE1_ax : ⊢ A∧B → A
  have andE1_ax : DerivationTree FrameClass.Base [] ((A.and B).imp A) :=
    DerivationTree.lift (FrameClass.base_le FrameClass.Base)
      (unwrap (HasAxiomAndE1.andE1 (φ := A) (ψ := B) :
        InferenceSystem.DerivableIn Bimodal.HilbertTM _))
  -- na_to_nconj : ⊢ ¬A → ¬(A∧B)   (contraposition of andE1)
  have na_to_nconj : DerivationTree FrameClass.Base []
      (A.neg.imp (A.and B).neg) :=
    contraposition andE1_ax
  -- andE2_ax : ⊢ A∧B → B
  have andE2_ax : DerivationTree FrameClass.Base [] ((A.and B).imp B) :=
    DerivationTree.lift (FrameClass.base_le FrameClass.Base)
      (unwrap (HasAxiomAndE2.andE2 (φ := A) (ψ := B) :
        InferenceSystem.DerivableIn Bimodal.HilbertTM _))
  -- nb_to_nconj : ⊢ ¬B → ¬(A∧B)   (contraposition of andE2)
  have nb_to_nconj : DerivationTree FrameClass.Base []
      (B.neg.imp (A.and B).neg) :=
    contraposition andE2_ax
  -- orE_ax : ⊢ (¬A→¬(A∧B)) → ((¬B→¬(A∧B)) → (¬A∨¬B → ¬(A∧B)))
  have orE_ax : DerivationTree FrameClass.Base []
      ((A.neg.imp (A.and B).neg).imp
        ((B.neg.imp (A.and B).neg).imp
          ((A.neg.or B.neg).imp (A.and B).neg))) :=
    DerivationTree.axiom [] _ (Axiom.orE A.neg B.neg (A.and B).neg) trivial
  exact DerivationTree.modus_ponens [] _ _
    (DerivationTree.modus_ponens [] _ _ orE_ax na_to_nconj)
    nb_to_nconj

/-- De Morgan 1 iff: `⊢ (¬(A ∧ B) → ¬A ∨ ¬B) ∧ (¬A ∨ ¬B → ¬(A ∧ B))`. -/
def demorganConjNeg (A B : Formula Atom) :
    DerivationTree FrameClass.Base []
      (((A.and B).neg.imp (A.neg.or B.neg)).and ((A.neg.or B.neg).imp (A.and B).neg)) :=
  iffIntro (A.and B).neg (A.neg.or B.neg)
    (demorganConjNegForward A B) (demorganConjNegBackward A B)

/-- De Morgan 2 forward: `⊢ ¬(A ∨ B) → (¬A ∧ ¬B)`.

Uses bCombinator+flip with orI1/orI2 to derive `¬(A∨B) → ¬A` and `¬(A∨B) → ¬B`,
then combineImpConj. -/
def demorganDisjNegForward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.or B).neg.imp (A.neg.and B.neg)) := by
  -- norAB_to_nA : ⊢ ¬(A∨B) → ¬A
  -- bC A (A∨B) ⊥ : ⊢ (A∨B→⊥) → (A→A∨B) → A→⊥
  -- flip: (A→A∨B) → (A∨B→⊥) → A→⊥
  -- apply orI1: ⊢ (A∨B→⊥) → A→⊥ = ¬(A∨B) → ¬A
  have orI1_ax : DerivationTree FrameClass.Base [] (A.imp (A.or B)) :=
    DerivationTree.axiom [] _ (Axiom.orI1 A B) trivial
  have bC_nA : DerivationTree FrameClass.Base []
      ((A.or B |>.imp Formula.bot).imp ((A.imp (A.or B)).imp (A.imp Formula.bot))) :=
    @bCombinator Atom FrameClass.Base A (A.or B) Formula.bot
  have flip_nA : DerivationTree FrameClass.Base []
      (((A.or B |>.imp Formula.bot).imp ((A.imp (A.or B)).imp (A.imp Formula.bot))).imp
        ((A.imp (A.or B)).imp ((A.or B |>.imp Formula.bot).imp (A.imp Formula.bot)))) :=
    @flip Atom FrameClass.Base (A.or B |>.imp Formula.bot) (A.imp (A.or B)) (A.imp Formula.bot)
  have flip_bC_nA : DerivationTree FrameClass.Base []
      ((A.imp (A.or B)).imp ((A.or B |>.imp Formula.bot).imp (A.imp Formula.bot))) :=
    DerivationTree.modus_ponens [] _ _ flip_nA bC_nA
  have norAB_to_nA : DerivationTree FrameClass.Base []
      ((A.or B |>.imp Formula.bot).imp (A.imp Formula.bot)) :=
    DerivationTree.modus_ponens [] _ _ flip_bC_nA orI1_ax
  -- norAB_to_nB : ⊢ ¬(A∨B) → ¬B  (using orI2)
  have orI2_ax : DerivationTree FrameClass.Base [] (B.imp (A.or B)) :=
    DerivationTree.axiom [] _ (Axiom.orI2 A B) trivial
  have bC_nB : DerivationTree FrameClass.Base []
      ((A.or B |>.imp Formula.bot).imp ((B.imp (A.or B)).imp (B.imp Formula.bot))) :=
    @bCombinator Atom FrameClass.Base B (A.or B) Formula.bot
  have flip_nB : DerivationTree FrameClass.Base []
      (((A.or B |>.imp Formula.bot).imp ((B.imp (A.or B)).imp (B.imp Formula.bot))).imp
        ((B.imp (A.or B)).imp ((A.or B |>.imp Formula.bot).imp (B.imp Formula.bot)))) :=
    @flip Atom FrameClass.Base (A.or B |>.imp Formula.bot) (B.imp (A.or B)) (B.imp Formula.bot)
  have flip_bC_nB : DerivationTree FrameClass.Base []
      ((B.imp (A.or B)).imp ((A.or B |>.imp Formula.bot).imp (B.imp Formula.bot))) :=
    DerivationTree.modus_ponens [] _ _ flip_nB bC_nB
  have norAB_to_nB : DerivationTree FrameClass.Base []
      ((A.or B |>.imp Formula.bot).imp (B.imp Formula.bot)) :=
    DerivationTree.modus_ponens [] _ _ flip_bC_nB orI2_ax
  -- combineImpConj norAB_to_nA norAB_to_nB : ⊢ ¬(A∨B) → ¬A∧¬B
  exact combineImpConj norAB_to_nA norAB_to_nB

/-- De Morgan 2 backward: `⊢ (¬A ∧ ¬B) → ¬(A ∨ B)`.

Uses lceImp/rceImp to extract ¬A and ¬B, then orE to combine. -/
def demorganDisjNegBackward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.neg.and B.neg).imp (A.or B).neg) := by
  -- orE_ax : ⊢ (A→⊥) → ((B→⊥) → (A∨B→⊥))
  have orE_ax : DerivationTree FrameClass.Base []
      ((A.imp Formula.bot).imp ((B.imp Formula.bot).imp ((A.or B).imp Formula.bot))) :=
    DerivationTree.axiom [] _ (Axiom.orE A B Formula.bot) trivial
  -- lce_nA : ⊢ (¬A∧¬B) → ¬A  (from andE1)
  have lce_nA : DerivationTree FrameClass.Base []
      ((A.neg.and B.neg).imp A.neg) :=
    DerivationTree.lift (FrameClass.base_le FrameClass.Base)
      (unwrap (HasAxiomAndE1.andE1 (φ := A.neg) (ψ := B.neg) :
        InferenceSystem.DerivableIn Bimodal.HilbertTM _))
  -- rce_nB : ⊢ (¬A∧¬B) → ¬B  (from andE2)
  have rce_nB : DerivationTree FrameClass.Base []
      ((A.neg.and B.neg).imp B.neg) :=
    DerivationTree.lift (FrameClass.base_le FrameClass.Base)
      (unwrap (HasAxiomAndE2.andE2 (φ := A.neg) (ψ := B.neg) :
        InferenceSystem.DerivableIn Bimodal.HilbertTM _))
  -- step1 : ⊢ (¬A∧¬B) → (¬B → ¬(A∨B))
  --   = impTrans lce_nA orE_ax
  have step1 : DerivationTree FrameClass.Base []
      ((A.neg.and B.neg).imp (B.neg.imp (A.or B).neg)) :=
    impTrans lce_nA orE_ax
  -- Use S/distribution to derive ⊢ (¬A∧¬B) → ¬(A∨B):
  -- imp_k (¬A∧¬B) ¬B ¬(A∨B) : ⊢ ((¬A∧¬B)→¬B→¬(A∨B)) → ((¬A∧¬B)→¬B) → ((¬A∧¬B)→¬(A∨B))
  have s_ax : DerivationTree FrameClass.Base []
      (((A.neg.and B.neg).imp (B.neg.imp (A.or B).neg)).imp
        (((A.neg.and B.neg).imp B.neg).imp
          ((A.neg.and B.neg).imp (A.or B).neg))) :=
    DerivationTree.axiom [] _
      (Axiom.imp_k (A.neg.and B.neg) B.neg (A.or B).neg) trivial
  have step2 : DerivationTree FrameClass.Base []
      (((A.neg.and B.neg).imp B.neg).imp ((A.neg.and B.neg).imp (A.or B).neg)) :=
    DerivationTree.modus_ponens [] _ _ s_ax step1
  exact DerivationTree.modus_ponens [] _ _ step2 rce_nB

/-- De Morgan 2 iff: `⊢ (¬(A ∨ B) → ¬A ∧ ¬B) ∧ (¬A ∧ ¬B → ¬(A ∨ B))`. -/
def demorganDisjNeg (A B : Formula Atom) :
    DerivationTree FrameClass.Base []
      (((A.or B).neg.imp (A.neg.and B.neg)).and ((A.neg.and B.neg).imp (A.or B).neg)) :=
  iffIntro (A.or B).neg (A.neg.and B.neg)
    (demorganDisjNegForward A B) (demorganDisjNegBackward A B)

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.Propositional
