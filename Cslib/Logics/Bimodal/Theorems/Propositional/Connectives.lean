/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.ProofSystem.Instances
public import Cslib.Logics.Bimodal.Theorems.Propositional.Core
public import Cslib.Foundations.Logic.Theorems.DerivationCombinators

/-!
# Derived Connective Reasoning

Classical merge, iff introduction/elimination, contraposition, and De Morgan laws
for the Hilbert-style proof system.

Most theorems delegate to the generic `Cslib.Logic.Theorems.DerivationCombinators` raw-typed
layer, which is directly applicable since `Bimodal.HilbertTM⇓φ` is definitionally
`DerivationTree .Base [] φ` -- no local `wrap`/`unwrap` bridge is needed.

Ported from BimodalLogic/Theories/Bimodal/Theorems/Propositional/Connectives.lean
-/

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Theorems.Propositional

open Cslib.Logic
open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Combinators

variable {Atom : Type*}

noncomputable section

-- NOTE: `Bimodal` is open in this file, and `S` is scoped infix notation for the "Since"
-- temporal operator (`Bimodal/Syntax/Formula.lean`), so the generic layer's `S` type-tag
-- argument must be supplied positionally via `@` rather than as `(S := Bimodal.HilbertTM)`.

/-- `⊢ (Q → R) → ((¬Q → R) → R)`: classical merge by case analysis. -/
def classicalMerge (Q R : Formula Atom) :
    DerivationTree FrameClass.Base [] ((Q.imp R).imp ((Q.neg.imp R).imp R)) :=
  @Theorems.DerivationCombinators.classicalMerge _ _ _ Bimodal.HilbertTM _ _ Q R

/-- `⊢ (A → B) → ((B → A) → (A ↔ B))`: iff introduction from two implications. -/
def iffIntro (A B : Formula Atom)
    (h1 : DerivationTree FrameClass.Base [] (A.imp B))
    (h2 : DerivationTree FrameClass.Base [] (B.imp A)) :
    DerivationTree FrameClass.Base [] ((A.imp B).and (B.imp A)) :=
  @Theorems.DerivationCombinators.iffIntro _ _ _ Bimodal.HilbertTM _ _ A B h1 h2

/-- `{A ↔ B, A} ⊢ B`: iff elimination left (forward direction) from context. -/
def iffElimLeft (A B : Formula Atom) :
    DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] B := by
  have h_a : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] A := by
    apply DerivationTree.assumption; simp
  have h_imp : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), A] (A.imp B) := by
    have lce_inst := lce (A.imp B) (B.imp A)
    exact DerivationTree.weakening [(A.imp B).and (B.imp A)] _ _ lce_inst
      (by intro x; simp; intro h; left; exact h)
  exact DerivationTree.modus_ponens _ _ _ h_imp h_a

/-- `{A ↔ B, B} ⊢ A`: iff elimination right (backward direction) from context. -/
def iffElimRight (A B : Formula Atom) :
    DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] A := by
  have h_b : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] B := by
    apply DerivationTree.assumption; simp
  have h_imp : DerivationTree FrameClass.Base [((A.imp B).and (B.imp A)), B] (B.imp A) := by
    have rce_inst := rce (A.imp B) (B.imp A)
    exact DerivationTree.weakening [(A.imp B).and (B.imp A)] _ _ rce_inst
      (by intro x; simp; intro h; left; exact h)
  exact DerivationTree.modus_ponens _ _ _ h_imp h_b

/-- `⊢ (A → B) → (¬B → ¬A)`: contrapositive of an implication as a derivation. -/
def contraposeImp (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) :=
  @Theorems.DerivationCombinators.contraposeImp _ _ _ Bimodal.HilbertTM _ _ A B

/-- Given `⊢ A → B`, derive `⊢ ¬B → ¬A` by contraposition. -/
def contraposition {A B : Formula Atom}
    (h : DerivationTree FrameClass.Base [] (A.imp B)) :
    DerivationTree FrameClass.Base [] (B.neg.imp A.neg) :=
  @Theorems.DerivationCombinators.contraposition _ _ _ Bimodal.HilbertTM _ _ A B h

/-- Given `⊢ A ↔ B`, derive `⊢ ¬A ↔ ¬B`. -/
def contraposeIff (A B : Formula Atom)
    (h : DerivationTree FrameClass.Base [] ((A.imp B).and (B.imp A))) :
    DerivationTree FrameClass.Base [] ((A.neg.imp B.neg).and (B.neg.imp A.neg)) :=
  @Theorems.DerivationCombinators.contraposeIff _ _ _ Bimodal.HilbertTM _ _ A B h

/-- `⊢ (¬A ↔ ¬B)` from `⊢ ¬A → ¬B` and `⊢ ¬B → ¬A`. -/
def iffNegIntro (A B : Formula Atom)
    (h1 : DerivationTree FrameClass.Base [] (A.neg.imp B.neg))
    (h2 : DerivationTree FrameClass.Base [] (B.neg.imp A.neg)) :
    DerivationTree FrameClass.Base [] ((A.neg.imp B.neg).and (B.neg.imp A.neg)) :=
  @Theorems.DerivationCombinators.iffNegIntro _ _ _ Bimodal.HilbertTM _ _ A B h1 h2

/-- `⊢ ¬(A ∧ B) → (¬A ∨ ¬B)`: De Morgan's law for negated conjunction (forward). -/
def demorganConjNegForward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.and B).neg.imp (A.neg.or B.neg)) :=
  @Theorems.DerivationCombinators.demorganConjNegForward _ _ _ Bimodal.HilbertTM _ _ A B

/-- `⊢ (¬A ∨ ¬B) → ¬(A ∧ B)`: De Morgan's law for negated conjunction (backward). -/
def demorganConjNegBackward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.neg.or B.neg).imp (A.and B).neg) :=
  @Theorems.DerivationCombinators.demorganConjNegBackward _ _ _ Bimodal.HilbertTM _ _ A B

/-- `⊢ ¬(A ∧ B) ↔ (¬A ∨ ¬B)`: De Morgan's law for negated conjunction (both directions). -/
def demorganConjNeg (A B : Formula Atom) :
    DerivationTree FrameClass.Base []
      (((A.and B).neg.imp (A.neg.or B.neg)).and ((A.neg.or B.neg).imp (A.and B).neg)) :=
  iffIntro (A.and B).neg (A.neg.or B.neg)
    (demorganConjNegForward A B) (demorganConjNegBackward A B)

/-- `⊢ ¬(A ∨ B) → (¬A ∧ ¬B)`: De Morgan's law for negated disjunction (forward). -/
def demorganDisjNegForward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.or B).neg.imp (A.neg.and B.neg)) :=
  @Theorems.DerivationCombinators.demorganDisjNegForward _ _ _ Bimodal.HilbertTM _ _ A B

/-- `⊢ (¬A ∧ ¬B) → ¬(A ∨ B)`: De Morgan's law for negated disjunction (backward). -/
def demorganDisjNegBackward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.neg.and B.neg).imp (A.or B).neg) :=
  @Theorems.DerivationCombinators.demorganDisjNegBackward _ _ _ Bimodal.HilbertTM _ _ A B

/-- `⊢ ¬(A ∨ B) ↔ (¬A ∧ ¬B)`: De Morgan's law for negated disjunction (both directions). -/
def demorganDisjNeg (A B : Formula Atom) :
    DerivationTree FrameClass.Base []
      (((A.or B).neg.imp (A.neg.and B.neg)).and ((A.neg.and B.neg).imp (A.or B).neg)) :=
  iffIntro (A.or B).neg (A.neg.and B.neg)
    (demorganDisjNegForward A B) (demorganDisjNegBackward A B)

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.Propositional
