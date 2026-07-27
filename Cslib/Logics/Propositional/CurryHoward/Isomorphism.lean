/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.CurryHoward.Defs

/-! # Curry-Howard Isomorphism: Forward and Backward Maps

This file establishes the formal Curry-Howard isomorphism between
`Theory.Derivation G A` (propositional natural deduction proofs) and
`Theory.Term G A` (intrinsically-typed simply-typed lambda terms).

## Main definitions

- `Theory.curryHowardForward` : extract a well-typed term from a derivation.
  Defined by structural recursion on the derivation, mapping each Derivation
  constructor to its corresponding Term constructor.
- `Theory.curryHowardBackward` : extract a derivation from a well-typed term.
  Defined by structural recursion on the term, mapping each Term constructor
  back to its corresponding Derivation constructor.
- `Theory.curryHoward_forward_backward` : `curryHowardForward (curryHowardBackward t) = t`
  for all `t : Term G A`. Proved by structural induction on `t`; each case reduces to `rfl`.
- `Theory.curryHoward_backward_forward` : `curryHowardBackward (curryHowardForward d) = d`
  for all `d : Derivation G A`. Proved by structural induction on `d`; each case reduces to `rfl`.
- `Theory.curryHowardEquiv` : the equivalence `Derivation G A ≃ Term G A` bundling the
  above maps and roundtrip proofs.

## References

* [M. H. B. Sørensen, P. Urzyczyn,
  *Lectures on the Curry-Howard Isomorphism*][SorensenUrzyczyn2006], Section 2.2
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

/-! ### Forward map: Derivation → Term -/

/-- The Curry-Howard forward map, extracting a well-typed lambda term from a natural deduction
derivation. This is a constructor-renaming bijection: each `Derivation` constructor is mapped
to its corresponding `Term` constructor. -/
def Theory.curryHowardForward {G : Ctx Atom} {A : Proposition Atom} :
    T.Derivation G A → Theory.Term (T := T) G A
  | .ax h      => .const h
  | .ass h     => .var h
  | .andI G d₁ d₂  => .pair G (curryHowardForward d₁) (curryHowardForward d₂)
  | .andE1 G d     => .fst G (curryHowardForward d)
  | .andE2 G d     => .snd G (curryHowardForward d)
  | .orI1 G d      => .inl G (curryHowardForward d)
  | .orI2 G d      => .inr G (curryHowardForward d)
  | .orE G d dA dB =>
      .case_ G (curryHowardForward d) (curryHowardForward dA) (curryHowardForward dB)
  | .impI Γ d      => .lam Γ (curryHowardForward d)
  | .impE d d'     => .app (curryHowardForward d) (curryHowardForward d')
  | @Derivation.efq _ _ _ _ _ i d => @Term.efq _ _ _ _ _ i (curryHowardForward d)

/-! ### Backward map: Term → Derivation -/

/-- The Curry-Howard backward map, extracting a natural deduction derivation from a well-typed
lambda term. This is the inverse constructor-renaming: each `Term` constructor is mapped
to its corresponding `Derivation` constructor. -/
def Theory.curryHowardBackward {G : Ctx Atom} {A : Proposition Atom} :
    Theory.Term (T := T) G A → T.Derivation G A
  | .const h      => .ax h
  | .var h        => .ass h
  | .pair G t₁ t₂  => .andI G (curryHowardBackward t₁) (curryHowardBackward t₂)
  | .fst G t      => .andE1 G (curryHowardBackward t)
  | .snd G t      => .andE2 G (curryHowardBackward t)
  | .inl G t      => .orI1 G (curryHowardBackward t)
  | .inr G t      => .orI2 G (curryHowardBackward t)
  | .case_ G t tA tB =>
      .orE G (curryHowardBackward t) (curryHowardBackward tA) (curryHowardBackward tB)
  | .lam Γ t      => .impI Γ (curryHowardBackward t)
  | .app t t'     => .impE (curryHowardBackward t) (curryHowardBackward t')
  | @Term.efq _ _ _ _ _ i t => @Derivation.efq _ _ _ _ _ i (curryHowardBackward t)

/-! ### Roundtrip properties -/

/-- The composition `curryHowardForward ∘ curryHowardBackward` is the identity on `Term`.
Proved by structural induction on the term; each of the 11 cases reduces to `rfl` since
the maps are constructor-for-constructor inverses. -/
theorem Theory.curryHoward_forward_backward {G : Ctx Atom} {A : Proposition Atom}
    (t : Theory.Term (T := T) G A) :
    curryHowardForward (curryHowardBackward t) = t := by
  induction t with
  | const _ => rfl
  | var _ => rfl
  | pair _ _ _ ih₁ ih₂ => simp [curryHowardBackward, curryHowardForward, ih₁, ih₂]
  | fst _ _ ih => simp [curryHowardBackward, curryHowardForward, ih]
  | snd _ _ ih => simp [curryHowardBackward, curryHowardForward, ih]
  | inl _ _ ih => simp [curryHowardBackward, curryHowardForward, ih]
  | inr _ _ ih => simp [curryHowardBackward, curryHowardForward, ih]
  | case_ _ _ _ _ ih ih₁ ih₂ => simp [curryHowardBackward, curryHowardForward, ih, ih₁, ih₂]
  | lam _ _ ih => simp [curryHowardBackward, curryHowardForward, ih]
  | app _ _ ih₁ ih₂ => simp [curryHowardBackward, curryHowardForward, ih₁, ih₂]
  | efq _ ih => simp [curryHowardBackward, curryHowardForward, ih]

/-- The composition `curryHowardBackward ∘ curryHowardForward` is the identity on `Derivation`.
Proved by structural induction on the derivation; each of the 11 cases reduces to `rfl`. -/
theorem Theory.curryHoward_backward_forward {G : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation G A) :
    curryHowardBackward (curryHowardForward d) = d := by
  induction d with
  | ax _ => rfl
  | ass _ => rfl
  | andI _ _ _ ih₁ ih₂ => simp [curryHowardForward, curryHowardBackward, ih₁, ih₂]
  | andE1 _ _ ih => simp [curryHowardForward, curryHowardBackward, ih]
  | andE2 _ _ ih => simp [curryHowardForward, curryHowardBackward, ih]
  | orI1 _ _ ih => simp [curryHowardForward, curryHowardBackward, ih]
  | orI2 _ _ ih => simp [curryHowardForward, curryHowardBackward, ih]
  | orE _ _ _ _ ih ih₁ ih₂ => simp [curryHowardForward, curryHowardBackward, ih, ih₁, ih₂]
  | impI _ _ ih => simp [curryHowardForward, curryHowardBackward, ih]
  | impE _ _ ih₁ ih₂ => simp [curryHowardForward, curryHowardBackward, ih₁, ih₂]
  | efq _ ih => simp [curryHowardForward, curryHowardBackward, ih]

/-! ### Equivalence -/

/-- The Curry-Howard isomorphism: a formal equivalence between natural deduction derivations
`T.Derivation G A` and well-typed simply-typed lambda terms `Theory.Term (T := T) G A`.
The isomorphism is witnessed by a pair of constructor-renaming maps that are mutually inverse. -/
def Theory.curryHowardEquiv {G : Ctx Atom} {A : Proposition Atom} :
    T.Derivation G A ≃ Theory.Term (T := T) G A where
  toFun := curryHowardForward
  invFun := curryHowardBackward
  left_inv d := curryHoward_backward_forward d
  right_inv t := curryHoward_forward_backward t

end Cslib.Logic.PL
