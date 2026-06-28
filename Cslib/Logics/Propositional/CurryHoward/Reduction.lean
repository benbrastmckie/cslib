/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.CurryHoward.Isomorphism
public import Cslib.Logics.Propositional.NaturalDeduction.Normalization.Termination

/-! # Curry-Howard Reduction Correspondence

This file extends the Curry-Howard isomorphism to a computational correspondence:
reductions on `Theory.Derivation` are mirrored by a native reduction on `Theory.Term`, and
term-level strong normalization is transported across the isomorphism.

## Main definitions

- `Theory.Term.subsOne`: Single-hypothesis substitution on terms, defined by transport through
  the Curry-Howard isomorphism. Used in the β-reduction cases of `Term.reduceRoot`.
- `Theory.Term.weakCtx`: Context weakening on terms, defined by transport. Used in the
  commuting conversion case of `Term.reduceRoot`.
- `Theory.subsOne_fwd`: Compatibility of `Derivation.subsOne` with the forward map:
  `curryHowardForward (D.subsOne E) = (curryHowardForward D).subsOne (curryHowardForward E)`.
- `Theory.weakCtx_fwd`: Compatibility of `Derivation.weakCtx` with the forward map:
  `curryHowardForward (D.weakCtx h) = (curryHowardForward D).weakCtx h`.
- `Theory.Term.reduceRoot`: Native single-step root reduction on `Term`, mirroring
  `Derivation.reduceRoot`'s 8 redex cases (5 proper β-redexes + 3 commuting conversions).

## References

* [M. H. B. Sørensen, P. Urzyczyn,
  *Lectures on the Curry-Howard Isomorphism*][SorensenUrzyczyn2006], Section 2.2
* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965], Ch. III–IV.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem

variable {Atom : Type u} [DecidableEq Atom] {T : Theory Atom}

/-! ## Term substitution and weakening by transport -/

/-- Single-hypothesis substitution on terms, defined by transport through the
Curry-Howard isomorphism. Given `t : Term (insert A Γ) B` and `s : Term Γ A`,
produces `Term Γ B` by routing through `Derivation.subsOne` via the roundtrip maps.
This is the term-side counterpart of `Derivation.subsOne`, used in `Term.reduceRoot`'s
β-reduction cases. See [SorensenUrzyczyn2006] §2.2. -/
def Theory.Term.subsOne {A B : Proposition Atom} {Γ : Ctx Atom}
    (t : Theory.Term (T := T) (insert A Γ) B)
    (s : Theory.Term (T := T) Γ A) : Theory.Term (T := T) Γ B :=
  curryHowardForward ((curryHowardBackward t).subsOne (curryHowardBackward s))

/-- Context weakening on terms, defined by transport through the Curry-Howard isomorphism.
Given `t : Term Γ A` and `h : Γ ⊆ Δ`, produces `Term Δ A` by routing through
`Derivation.weakCtx` via the roundtrip maps. This is the term-side counterpart of
`Derivation.weakCtx`, used in `Term.reduceRoot`'s commuting conversion for
`app (case_ ...) s`. See [SorensenUrzyczyn2006] §2.2. -/
def Theory.Term.weakCtx {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (t : Theory.Term (T := T) Γ A) (h : Γ ⊆ Δ) : Theory.Term (T := T) Δ A :=
  curryHowardForward ((curryHowardBackward t).weakCtx h)

/-! ## Forward compatibility lemmas -/

/-- Compatibility of `subsOne` with the Curry-Howard forward map:
`curryHowardForward (D.subsOne E) = (curryHowardForward D).subsOne (curryHowardForward E)`.
Proved by unfolding `Term.subsOne` on the right-hand side and applying the
`curryHoward_backward_forward` roundtrip identity twice. See [SorensenUrzyczyn2006] §2.2. -/
lemma Theory.subsOne_fwd {A B : Proposition Atom} {Γ : Ctx Atom}
    (D : T.Derivation (insert A Γ) B)
    (E : T.Derivation Γ A) :
    curryHowardForward (D.subsOne E) =
    (curryHowardForward D).subsOne (curryHowardForward E) := by
  unfold Term.subsOne
  rw [curryHoward_backward_forward, curryHoward_backward_forward]

/-- Compatibility of `weakCtx` with the Curry-Howard forward map:
`curryHowardForward (D.weakCtx h) = (curryHowardForward D).weakCtx h`.
Proved by unfolding `Term.weakCtx` on the right-hand side and applying the
`curryHoward_backward_forward` roundtrip identity. See [SorensenUrzyczyn2006] §2.2. -/
lemma Theory.weakCtx_fwd {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (D : T.Derivation Γ A) (h : Γ ⊆ Δ) :
    curryHowardForward (D.weakCtx h) =
    (curryHowardForward D).weakCtx h := by
  unfold Term.weakCtx
  rw [curryHoward_backward_forward]

/-! ## Native root reduction on terms -/

/-- Single-step outermost (root) reduction on simply-typed lambda terms.
Returns `some t'` if the term has an outermost proper redex or commuting conversion,
or `none` otherwise. This is the term-side mirror of `Derivation.reduceRoot`, with
constructor correspondence `impI↔lam, impE↔app, andI↔pair, andE1↔fst, andE2↔snd,
orI1↔inl, orI2↔inr, orE↔case_`. The substitution and weakening operations
`subsOne` and `weakCtx` are defined by transport.

Proper redexes (β-reductions):
- `app (lam _ t) s`: function application β-redex; contracts to `t.subsOne s`
- `fst _ (pair _ t₁ _)`: left projection β-redex; contracts to `t₁`
- `snd _ (pair _ _ t₂)`: right projection β-redex; contracts to `t₂`
- `case_ _ (inl _ t) tA _`: left case branch β-redex; contracts to `tA.subsOne t`
- `case_ _ (inr _ t) _ tB`: right case branch β-redex; contracts to `tB.subsOne t`

Commuting conversions (permutative reductions pushing elimination inside `case_`):
- `fst G (case_ _ t tA tB)`: push `fst` inside `case_` branches
- `snd G (case_ _ t tA tB)`: push `snd` inside `case_` branches
- `app (case_ G t tA tB) s`: push `app` inside `case_` branches (using `weakCtx`)

See [Prawitz1965] Ch. III–IV and [SorensenUrzyczyn2006] §2.2. -/
def Theory.Term.reduceRoot {G : Ctx Atom} {A : Proposition Atom} :
    Theory.Term (T := T) G A → Option (Theory.Term (T := T) G A)
  -- Proper redexes (β-reductions)
  | .app (.lam _ t) s               => some (t.subsOne s)
  | .fst _ (.pair _ t₁ _)           => some t₁
  | .snd _ (.pair _ _ t₂)           => some t₂
  | .case_ _ (.inl _ t) tA _        => some (tA.subsOne t)
  | .case_ _ (.inr _ t) _ tB        => some (tB.subsOne t)
  -- Commuting conversions: push elimination inside case_ branches
  | .fst G (.case_ _ t tA tB)       =>
      some (.case_ G t (.fst _ tA) (.fst _ tB))
  | .snd G (.case_ _ t tA tB)       =>
      some (.case_ G t (.snd _ tA) (.snd _ tB))
  | .app (.case_ G t tA tB) s       =>
      some (.case_ G t (.app tA (s.weakCtx (Finset.subset_insert _ _)))
                       (.app tB (s.weakCtx (Finset.subset_insert _ _))))
  | _ => none

/-! ## Forward reduction correspondence -/

/-- The Curry-Howard forward map commutes with root reduction: for any derivation `d`,
the term `curryHowardForward d` reduces at its root if and only if `d` does, and the
reduction step is transported through the isomorphism. Formally,
`(curryHowardForward d).reduceRoot = d.reduceRoot.map curryHowardForward`.
Proved by `cases d` with nested `cases` on the subderivation being eliminated; proper
β-redex cases are discharged using `subsOne_fwd`, and the `impE (orE ...)` commuting
conversion uses `weakCtx_fwd`. See [SorensenUrzyczyn2006] §2.2. -/
lemma Theory.reduceRoot_forward {G : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation G A) :
    (curryHowardForward d).reduceRoot = d.reduceRoot.map curryHowardForward := by
  cases d with
  | ax _ => rfl
  | ass _ => rfl
  | andI _ _ _ => simp [curryHowardForward, Term.reduceRoot, Derivation.reduceRoot]
  | orI1 _ _ => simp [curryHowardForward, Term.reduceRoot, Derivation.reduceRoot]
  | orI2 _ _ => simp [curryHowardForward, Term.reduceRoot, Derivation.reduceRoot]
  | impI _ _ => simp [curryHowardForward, Term.reduceRoot, Derivation.reduceRoot]
  | andE1 G d =>
      cases d <;>
        simp [curryHowardForward, Term.reduceRoot, Derivation.reduceRoot]
  | andE2 G d =>
      cases d <;>
        simp [curryHowardForward, Term.reduceRoot, Derivation.reduceRoot]
  | orE G d dA dB =>
      cases d <;>
        simp [curryHowardForward, Term.reduceRoot, Derivation.reduceRoot, subsOne_fwd]
  | impE d d' =>
      cases d <;>
        simp [curryHowardForward, Term.reduceRoot, Derivation.reduceRoot, subsOne_fwd, weakCtx_fwd]

/-- Corollary of `reduceRoot_forward`: if derivation `d` reduces at its root to `d'`,
then `curryHowardForward d` reduces at its root to `curryHowardForward d'`. This is the
direct "forward reduction step" compatibility used to transport normalization arguments
through the Curry-Howard isomorphism. See [SorensenUrzyczyn2006] §2.2. -/
lemma Theory.reduceRoot_forward_some {G : Ctx Atom} {A : Proposition Atom}
    (d d' : T.Derivation G A) (h : d.reduceRoot = some d') :
    (curryHowardForward d).reduceRoot = some (curryHowardForward d') := by
  rw [reduceRoot_forward, h, Option.map_some]

/-! ## Backward compatibility lemmas -/

/-- Compatibility of `subsOne` with the Curry-Howard backward map:
`curryHowardBackward (t.subsOne s) = (curryHowardBackward t).subsOne (curryHowardBackward s)`.
Proved by unfolding `Term.subsOne` on the left-hand side and applying the
`curryHoward_backward_forward` roundtrip identity. Dual to `subsOne_fwd`.
See [SorensenUrzyczyn2006] §2.2. -/
lemma Theory.subsOne_bwd {A B : Proposition Atom} {Γ : Ctx Atom}
    (t : Theory.Term (T := T) (insert A Γ) B)
    (s : Theory.Term (T := T) Γ A) :
    curryHowardBackward (t.subsOne s) =
    (curryHowardBackward t).subsOne (curryHowardBackward s) := by
  unfold Term.subsOne
  rw [curryHoward_backward_forward]

/-- Compatibility of `weakCtx` with the Curry-Howard backward map:
`curryHowardBackward (t.weakCtx h) = (curryHowardBackward t).weakCtx h`.
Proved by unfolding `Term.weakCtx` on the left-hand side and applying the
`curryHoward_backward_forward` roundtrip identity. Dual to `weakCtx_fwd`.
See [SorensenUrzyczyn2006] §2.2. -/
lemma Theory.weakCtx_bwd {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (t : Theory.Term (T := T) Γ A) (h : Γ ⊆ Δ) :
    curryHowardBackward (t.weakCtx h) = (curryHowardBackward t).weakCtx h := by
  unfold Term.weakCtx
  rw [curryHoward_backward_forward]

/-! ## Backward reduction correspondence -/

/-- The Curry-Howard backward map commutes with root reduction: for any term `t`,
the derivation `curryHowardBackward t` reduces at its root if and only if `t` does, and the
reduction step is transported through the isomorphism. Formally,
`(curryHowardBackward t).reduceRoot = t.reduceRoot.map curryHowardBackward`.
Proved by `cases t` with nested `cases` on the subterm being eliminated; proper
β-redex cases are discharged using `subsOne_bwd`, and the `app (case_ ...) s` commuting
conversion uses `weakCtx_bwd`. See [SorensenUrzyczyn2006] §2.2. -/
lemma Theory.reduceRoot_backward {G : Ctx Atom} {A : Proposition Atom}
    (t : Theory.Term (T := T) G A) :
    (curryHowardBackward t).reduceRoot = t.reduceRoot.map curryHowardBackward := by
  cases t with
  | const _ => rfl
  | var _ => rfl
  | pair _ _ _ => simp [curryHowardBackward, Term.reduceRoot, Derivation.reduceRoot]
  | lam _ _ => simp [curryHowardBackward, Term.reduceRoot, Derivation.reduceRoot]
  | inl _ _ => simp [curryHowardBackward, Term.reduceRoot, Derivation.reduceRoot]
  | inr _ _ => simp [curryHowardBackward, Term.reduceRoot, Derivation.reduceRoot]
  | fst G t =>
      cases t <;>
        simp [curryHowardBackward, Term.reduceRoot, Derivation.reduceRoot]
  | snd G t =>
      cases t <;>
        simp [curryHowardBackward, Term.reduceRoot, Derivation.reduceRoot]
  | app t s =>
      cases t <;>
        simp [curryHowardBackward, Term.reduceRoot, Derivation.reduceRoot, subsOne_bwd, weakCtx_bwd]
  | case_ G t tA tB =>
      cases t <;>
        simp [curryHowardBackward, Term.reduceRoot, Derivation.reduceRoot, subsOne_bwd]

/-! ## Term-level strong normalization -/

/-- Strong normalization predicate on terms, defined by transport through the
Curry-Howard isomorphism: a term is strongly normal if and only if the derivation
it corresponds to under `curryHowardBackward` is strongly normal.
See [Prawitz1965] Ch. IV. Note: this asserts that `t` is itself in normal form
(single-tree predicate), not that all reduction sequences from `t` terminate. -/
def Theory.Term.isStronglyNormal {G : Ctx Atom} {A : Proposition Atom}
    (t : Theory.Term (T := T) G A) : Bool :=
  (curryHowardBackward t).isStronglyNormal

/-- Every term has a strongly-normal form: there exists a term `t'` with
`t'.isStronglyNormal = true`. Proved by transporting `Derivation.exists_stronglyNormal_form`
through the Curry-Howard isomorphism: apply it to `curryHowardBackward t` to obtain a
strongly-normal derivation `d'`, then map forward to `curryHowardForward d'` and use the
`curryHoward_backward_forward` roundtrip identity to verify the `isStronglyNormal` predicate.
See [Prawitz1965] Ch. IV. -/
theorem Theory.Term.exists_stronglyNormal_form {G : Ctx Atom} {A : Proposition Atom}
    (t : Theory.Term (T := T) G A) :
    ∃ t' : Theory.Term (T := T) G A, t'.isStronglyNormal = true := by
  obtain ⟨d', hd'⟩ := (curryHowardBackward t).exists_stronglyNormal_form
  refine ⟨curryHowardForward d', ?_⟩
  unfold Theory.Term.isStronglyNormal
  rw [curryHoward_backward_forward]
  exact hd'

/-- The Curry-Howard forward map preserves strong normality: a derivation `d` is
strongly normal if and only if its corresponding term `curryHowardForward d` is.
Proved via `curryHoward_backward_forward`, which collapses `backward ∘ forward` to the
identity. See [SorensenUrzyczyn2006] §2.2. -/
lemma Theory.isStronglyNormal_fwd {G : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation G A) :
    (curryHowardForward d).isStronglyNormal = d.isStronglyNormal := by
  unfold Theory.Term.isStronglyNormal
  rw [curryHoward_backward_forward]

end Cslib.Logic.PL
