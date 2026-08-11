/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Foundations.Logic.InferenceSystem

/-! # Intuitionistic Propositional Sequent Calculus LJ

We define the LJ proof system for intuitionistic propositional logic using an all-additive
Finset-based presentation following Negri and von Plato (2001). In this style every rule
conclusion has an explicit context `Γ` (antecedent) and a single conclusion formula; structural
rules (weakening, contraction) are admissible, with weakening proved here as a derived rule.

LJ sequents reuse the ND `Sequent` type: `Ctx Atom × Proposition Atom`, notated `Γ ⊢ A`.
Unlike LK, LJ has a single-conclusion succedent, which eliminates `weakR` and splits the
right disjunction rule into `orR1` and `orR2`.

## Main Definitions

- `LJProof`: An inductive type of LJ proofs with 11 constructors:
  `ax`, `botL`, `andL`, `andR`, `orL`, `orR1`, `orR2`, `impL`, `impR`,
  `weakL`, `cut`.
- `LJProof.height`: The height (depth) of an LJ proof tree.
- `LJProof.mono`: Monotonicity — weakening the antecedent (left side only).
- `CutFree`: A predicate on `LJProof` asserting the proof tree contains no `cut` steps.
- `CutFreeLJProof`: A subtype of `LJProof` restricted to cut-free proofs.

## Implementation Notes

Contexts are `Finset (Proposition Atom)`. The `insert` of a formula into a set is used
throughout, with `Finset.insert_comm` enabling commutativity when needed.

The `ax` rule requires `A ∈ Γ`, matching the all-additive presentation where the antecedent
explicitly contains the principal formula.

Unlike LK, LJ has no succedent Finset: the conclusion is always a single `Proposition Atom`.
This means:
- No `weakR` constructor (no succedent to weaken)
- `orR` is split into `orR1` and `orR2` (no succedent membership needed)
- `andR` and `impR` take no membership proof for the conclusion
- `LJProof.mono` takes only one subset argument (left side)

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
* [A. S. Troelstra, H. Schwichtenberg,
  *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory

variable {Atom : Type u} [DecidableEq Atom]

/-- Single-conclusion sequent-calculus proof trees parameterized by a theory `T : Theory Atom`.
The presentation is all-additive: every rule has an explicit context set `Γ` (antecedent) and a
single conclusion formula. Principal formulas appear in both premise and conclusion contexts.

`SeqProof` uses single-conclusion sequents (`Γ ⊢ A` where `A : Proposition Atom`) rather than
two-sided multi-conclusion sequents as in LK. This means there is no `weakR` constructor,
and right disjunction splits into `orR1` and `orR2`.

The ten connective/structural rules (`ax`, `andL`, `andR`, `orL`, `orR1`, `orR2`, `impL`, `impR`,
`weakL`, `cut`) form the **minimal** base (MPL strength). The explosion rule `botL` is *gated* by
`[IsIntuitionistic T]`, the exact analogue of the gated `efq` in `Theory.Derivation`: it is
constructible only when the theory `T` validates ex falso quodlibet. Hence `SeqProof MPL`
(`MPL = ∅` admits no `IsIntuitionistic` instance) is the `botL`-free minimal calculus, while
`SeqProof IPL` (= `LJProof`) recovers full intuitionistic LJ. Structural metatheory that is
already generic over `T`: `height`, `mono`, `CutFree`, `CutFreeSeqProof`, `IsBotRuleFree`,
`SeqProof.formulas`, and now also cut elimination (`ljCutAdmissibility`, re-exported at `IPL`
with `LJProof.cutElim`'s signature unchanged, per `SequentCalculus/LJ/CutElimination.lean`). The
subformula property, by contrast, is currently proved concretely at `IPL` only
(`LJProof.subformula_property`), not yet generically over `T`.

Constructors:
- `ax`: identity axiom — `A` appears in the antecedent.
- `botL`: left falsum — `⊥` in the antecedent derives anything (gated by `[IsIntuitionistic T]`).
- `andL`: left conjunction — from `A, B, Γ ⊢ C` derive `A ∧ B, Γ ⊢ C`.
- `andR`: right conjunction — from `Γ ⊢ A` and `Γ ⊢ B` derive `Γ ⊢ A ∧ B`.
- `orL`: left disjunction — from `A, Γ ⊢ C` and `B, Γ ⊢ C` derive `A ∨ B, Γ ⊢ C`.
- `orR1`: right disjunction left — from `Γ ⊢ A` derive `Γ ⊢ A ∨ B`.
- `orR2`: right disjunction right — from `Γ ⊢ B` derive `Γ ⊢ A ∨ B`.
- `impL`: left implication — from `Γ ⊢ A` and `B, Γ ⊢ C` derive `(A → B), Γ ⊢ C`.
- `impR`: right implication — from `A, Γ ⊢ B` derive `Γ ⊢ A → B`.
- `weakL`: left weakening — add a formula to the antecedent.
- `cut`: cut rule — eliminate a formula `A` using a left and right proof. -/
inductive SeqProof (T : Theory Atom) : @Sequent Atom → Type u where
  /-- Identity axiom: formula `A` appears in the antecedent. -/
  | ax (A : Proposition Atom) (Γ : Ctx Atom) (_ : A ∈ Γ) :
      SeqProof T (Γ ⊢ A)
  /-- Left falsum: bottom in the antecedent derives anything. Gated by `[IsIntuitionistic T]`,
  so this rule is unconstructible at minimal (`MPL`) strength. -/
  | botL (Γ : Ctx Atom) (C : Proposition Atom) [IsIntuitionistic T]
      (_ : (⊥ : Proposition Atom) ∈ Γ) :
      SeqProof T (Γ ⊢ C)
  /-- Left conjunction: from `A, B, Γ ⊢ C` derive `A ∧ B, Γ ⊢ C`. -/
  | andL {Γ : Ctx Atom} {C : Proposition Atom} (A B : Proposition Atom)
      (_ : (A ∧ B) ∈ Γ)
      (_ : SeqProof T (insert A (insert B Γ) ⊢ C)) :
      SeqProof T (Γ ⊢ C)
  /-- Right conjunction: from `Γ ⊢ A` and `Γ ⊢ B` derive `Γ ⊢ A ∧ B`. -/
  | andR {Γ : Ctx Atom} (A B : Proposition Atom)
      (_ : SeqProof T (Γ ⊢ A))
      (_ : SeqProof T (Γ ⊢ B)) :
      SeqProof T (Γ ⊢ A ∧ B)
  /-- Left disjunction: from `A, Γ ⊢ C` and `B, Γ ⊢ C` derive `A ∨ B, Γ ⊢ C`. -/
  | orL {Γ : Ctx Atom} {C : Proposition Atom} (A B : Proposition Atom)
      (_ : (A ∨ B) ∈ Γ)
      (_ : SeqProof T (insert A Γ ⊢ C))
      (_ : SeqProof T (insert B Γ ⊢ C)) :
      SeqProof T (Γ ⊢ C)
  /-- Right disjunction left: from `Γ ⊢ A` derive `Γ ⊢ A ∨ B`. -/
  | orR1 {Γ : Ctx Atom} (A B : Proposition Atom)
      (_ : SeqProof T (Γ ⊢ A)) :
      SeqProof T (Γ ⊢ A ∨ B)
  /-- Right disjunction right: from `Γ ⊢ B` derive `Γ ⊢ A ∨ B`. -/
  | orR2 {Γ : Ctx Atom} (A B : Proposition Atom)
      (_ : SeqProof T (Γ ⊢ B)) :
      SeqProof T (Γ ⊢ A ∨ B)
  /-- Left implication: from `Γ ⊢ A` and `B, Γ ⊢ C` derive `(A → B), Γ ⊢ C`. -/
  | impL {Γ : Ctx Atom} {C : Proposition Atom} (A B : Proposition Atom)
      (_ : (A → B) ∈ Γ)
      (_ : SeqProof T (Γ ⊢ A))
      (_ : SeqProof T (insert B Γ ⊢ C)) :
      SeqProof T (Γ ⊢ C)
  /-- Right implication: from `A, Γ ⊢ B` derive `Γ ⊢ A → B`. -/
  | impR {Γ : Ctx Atom} (A B : Proposition Atom)
      (_ : SeqProof T (insert A Γ ⊢ B)) :
      SeqProof T (Γ ⊢ A → B)
  /-- Left weakening: add a formula to the antecedent. -/
  | weakL {Γ : Ctx Atom} {C : Proposition Atom} (A : Proposition Atom)
      (_ : SeqProof T (Γ ⊢ C)) :
      SeqProof T (insert A Γ ⊢ C)
  /-- Cut rule: cut on formula `A`. -/
  | cut {Γ : Ctx Atom} {C : Proposition Atom} (A : Proposition Atom)
      (_ : SeqProof T (Γ ⊢ A))
      (_ : SeqProof T (insert A Γ ⊢ C)) :
      SeqProof T (Γ ⊢ C)

/-- LJ proof trees for intuitionistic propositional logic: `SeqProof` at theory `IPL`. Since
`IsIntuitionistic IPL` holds, the gated `botL` rule is available, recovering full LJ. -/
abbrev LJProof (seq : @Sequent Atom) : Type u := SeqProof IPL seq

/-- Minimal-strength single-conclusion proof trees: `SeqProof` at theory `MPL = ∅`. Since `MPL`
admits no `IsIntuitionistic` instance, the gated `botL` rule is structurally unconstructible, so
`SeqProofMinimal` is the `botL`-free minimal calculus. -/
abbrev SeqProofMinimal (seq : @Sequent Atom) : Type u := SeqProof MPL seq

/-- The height of a proof tree (maximum rule depth), generic over the theory `T`. -/
def SeqProof.height {T : Theory Atom} {seq : @Sequent Atom} : SeqProof T seq → Nat
  | .ax _ _ _ => 0
  | @SeqProof.botL _ _ _ _ _ _ _ => 0
  | .andL _ _ _ d => d.height + 1
  | .andR _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | .orL _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | .orR1 _ _ d => d.height + 1
  | .orR2 _ _ d => d.height + 1
  | .impL _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | .impR _ _ d => d.height + 1
  | .weakL _ d => d.height + 1
  | .cut _ d₁ d₂ => max d₁.height d₂.height + 1

/-- The height of an LJ proof tree (maximum rule depth). Re-export of `SeqProof.height` at `IPL`. -/
@[reducible] def LJProof.height {seq : @Sequent Atom} (d : LJProof seq) : Nat :=
  SeqProof.height d

/-- Left-side monotonicity (weakening): if `Γ ⊆ Γ'` then any proof of `Γ ⊢ C` yields
a proof of `Γ' ⊢ C`. Generic over the theory `T`.

Unlike LK's two-sided `mono`, this single-conclusion calculus weakens only the antecedent.
This follows by structural induction on the proof, inserting additional weakening steps at
axiom and `botL` leaves and propagating context extensions upward through the rules. The gated
`botL` arm rebinds its stored `[IsIntuitionistic T]` instance via `letI` before reconstruction. -/
def SeqProof.mono {T : Theory Atom} : ∀ {seq : @Sequent Atom}, SeqProof T seq →
    ∀ {Γ' : Ctx Atom}, seq.1 ⊆ Γ' → SeqProof T (Γ' ⊢ seq.2)
  | _, .ax A _ hA, Γ', hL =>
      ax A Γ' (hL hA)
  | _, @SeqProof.botL _ _ _ _ _ inst hbot, Γ', hL =>
      letI := inst
      botL Γ' _ (hL hbot)
  | _, .andL A B hAB d, _, hL =>
      andL A B (hL hAB)
        (d.mono (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hL)))
  | _, .andR A B d₁ d₂, _, hL =>
      andR A B
        (d₁.mono hL)
        (d₂.mono hL)
  | _, .orL A B hAB d₁ d₂, _, hL =>
      orL A B (hL hAB)
        (d₁.mono (Finset.insert_subset_insert _ hL))
        (d₂.mono (Finset.insert_subset_insert _ hL))
  | _, .orR1 A B d, _, hL =>
      orR1 A B (d.mono hL)
  | _, .orR2 A B d, _, hL =>
      orR2 A B (d.mono hL)
  | _, .impL A B hAB d₁ d₂, _, hL =>
      impL A B (hL hAB)
        (d₁.mono hL)
        (d₂.mono (Finset.insert_subset_insert _ hL))
  | _, .impR A B d, _, hL =>
      impR A B (d.mono (Finset.insert_subset_insert _ hL))
  | _, .weakL A d, _, hL =>
      d.mono ((Finset.subset_insert A _).trans hL)
  | _, .cut A d₁ d₂, _, hL =>
      cut A
        (d₁.mono hL)
        (d₂.mono (Finset.insert_subset_insert _ hL))

/-- Left-side monotonicity for LJ proofs. Re-export of `SeqProof.mono` at `IPL`. -/
@[reducible] def LJProof.mono {Γ Γ' : Ctx Atom} {C : Proposition Atom}
    (hL : Γ ⊆ Γ') (d : LJProof (Γ ⊢ C)) : LJProof (Γ' ⊢ C) :=
  SeqProof.mono d hL

/-- A predicate asserting that a proof is cut-free (contains no `cut` steps). Generic over `T`. -/
def SeqProof.CutFree {T : Theory Atom} : SeqProof T seq → Prop
  | .ax _ _ _ => True
  | @SeqProof.botL _ _ _ _ _ _ _ => True
  | .andL _ _ _ d => SeqProof.CutFree d
  | .andR _ _ d₁ d₂ => SeqProof.CutFree d₁ ∧ SeqProof.CutFree d₂
  | .orL _ _ _ d₁ d₂ => SeqProof.CutFree d₁ ∧ SeqProof.CutFree d₂
  | .orR1 _ _ d => SeqProof.CutFree d
  | .orR2 _ _ d => SeqProof.CutFree d
  | .impL _ _ _ d₁ d₂ => SeqProof.CutFree d₁ ∧ SeqProof.CutFree d₂
  | .impR _ _ d => SeqProof.CutFree d
  | .weakL _ d => SeqProof.CutFree d
  | .cut _ _ _ => False

/-- A predicate asserting that a proof does not use the gated `botL` rule. Generic over `T`.
At minimal strength (`SeqProofMinimal = SeqProof MPL`) every proof satisfies this, since `botL`
is unconstructible there. -/
def SeqProof.IsBotRuleFree {T : Theory Atom} : ∀ {seq : @Sequent Atom}, SeqProof T seq → Prop
  | _, .ax _ _ _ => True
  | _, @SeqProof.botL _ _ _ _ _ _ _ => False
  | _, .andL _ _ _ d => SeqProof.IsBotRuleFree d
  | _, .andR _ _ d₁ d₂ => SeqProof.IsBotRuleFree d₁ ∧ SeqProof.IsBotRuleFree d₂
  | _, .orL _ _ _ d₁ d₂ => SeqProof.IsBotRuleFree d₁ ∧ SeqProof.IsBotRuleFree d₂
  | _, .orR1 _ _ d => SeqProof.IsBotRuleFree d
  | _, .orR2 _ _ d => SeqProof.IsBotRuleFree d
  | _, .impL _ _ _ d₁ d₂ => SeqProof.IsBotRuleFree d₁ ∧ SeqProof.IsBotRuleFree d₂
  | _, .impR _ _ d => SeqProof.IsBotRuleFree d
  | _, .weakL _ d => SeqProof.IsBotRuleFree d
  | _, .cut _ d₁ d₂ => SeqProof.IsBotRuleFree d₁ ∧ SeqProof.IsBotRuleFree d₂

/-- A predicate asserting that an LJ proof is cut-free (contains no `cut` steps). Re-export of
`SeqProof.CutFree` at `IPL`. -/
@[reducible] def LJCutFree {seq : @Sequent Atom} (d : LJProof seq) : Prop :=
  SeqProof.CutFree d

/-- A `SeqProof T` that is cut-free, generic over the theory `T`. -/
def CutFreeSeqProof (T : Theory Atom) (seq : @Sequent Atom) : Type u :=
  { d : SeqProof T seq // SeqProof.CutFree d }

/-- An `LJProof` that is cut-free. Re-export of `CutFreeSeqProof` at `IPL`. -/
@[reducible] def CutFreeLJProof (seq : @Sequent Atom) : Type u :=
  CutFreeSeqProof IPL seq

/-- LJ inference system instance for `@Sequent Atom`. -/
instance : InferenceSystem InferenceSystem.Default (@Sequent (Atom := Atom)) where
  derivation seq := LJProof seq

end Cslib.Logic.PL
