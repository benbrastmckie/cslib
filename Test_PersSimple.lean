import Cslib.Logics.Propositional.Tableau.Minimal.Soundness
import Cslib.Logics.Propositional.Semantics.Kripke

namespace Cslib.Logic.PL
open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

private lemma prop_beq_eq5 :
    ∀ (a b : Proposition Atom), (a == b) = true → a = b := by
  intro a b h
  induction a generalizing b with
  | bot =>
    cases b <;> first
      | rfl
      | (simp [BEq.beq, instBEqProposition.beq] at h)
  | atom x => cases b with
    | atom y =>
      simp only [BEq.beq, instBEqProposition.beq] at h
      exact congrArg _ (eq_of_beq h)
    | _ => simp [BEq.beq, instBEqProposition.beq] at h
  | imp φ ψ ih_φ ih_ψ => cases b with
    | imp φ' ψ' =>
      change (instBEqProposition.beq (φ.imp ψ) (φ'.imp ψ')) = true at h
      rw [show instBEqProposition.beq (φ.imp ψ) (φ'.imp ψ') =
          (instBEqProposition.beq φ φ' && instBEqProposition.beq ψ ψ') from rfl] at h
      simp only [Bool.and_eq_true] at h
      exact congrArg₂ Proposition.imp (ih_φ φ' h.1) (ih_ψ ψ' h.2)
    | _ => simp [BEq.beq, instBEqProposition.beq] at h
  | and φ ψ ih_φ ih_ψ => cases b with
    | and φ' ψ' =>
      change (instBEqProposition.beq (φ.and ψ) (φ'.and ψ')) = true at h
      rw [show instBEqProposition.beq (φ.and ψ) (φ'.and ψ') =
          (instBEqProposition.beq φ φ' && instBEqProposition.beq ψ ψ') from rfl] at h
      simp only [Bool.and_eq_true] at h
      exact congrArg₂ Proposition.and (ih_φ φ' h.1) (ih_ψ ψ' h.2)
    | _ => simp [BEq.beq, instBEqProposition.beq] at h
  | or φ ψ ih_φ ih_ψ => cases b with
    | or φ' ψ' =>
      change (instBEqProposition.beq (φ.or ψ) (φ'.or ψ')) = true at h
      rw [show instBEqProposition.beq (φ.or ψ) (φ'.or ψ') =
          (instBEqProposition.beq φ φ' && instBEqProposition.beq ψ ψ') from rfl] at h
      simp only [Bool.and_eq_true] at h
      exact congrArg₂ Proposition.or (ih_φ φ' h.1) (ih_ψ ψ' h.2)
    | _ => simp [BEq.beq, instBEqProposition.beq] at h

#check @prop_beq_eq5

end Cslib.Logic.PL
