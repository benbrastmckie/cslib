/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory

/-! # Segments: Canonical Worlds for Constructive Modal Logic

This module defines the *segment* world type for the canonical model of bare constructive
modal logic `CK`, transliterated from ianshil/CK `Completeness_seg/general_seg_completeness.v`
(`segment`, `cexpl`, `cireach`, `cmreach`, `cval`).

A segment is a pair `⟨head, tail⟩` of a theory (set of formulas) and a set of "successor
theories", subject to: `head` and every member of `tail` are *quasi-prime* (deductively
closed with the disjunction property, but **not** required consistent — the exploding theory
`Set.univ` is admitted), every boxed formula in `head` is reflected into every tail member,
and every diamond formula in `head` is witnessed by some tail member. Quasi-primality (not
primality) is exactly what admits the exploding segment `cexpl`, which forces `⊥` — bare `CK`
does not prove `◇⊥ → ⊥`, so its canonical model *must* contain a fallible world.

## Main Definitions

- `QuasiPrime`: deductively closed + disjunction property (no consistency requirement);
  equivalently `Metalogic.PrimeAdmissible` at the trivially-true consistency predicate.
- `boxInv`/`diaInv`: the box/diamond inverse images of a theory.
- `CKSegment`: the segment world type, parametric over `Axioms` (so task 501's CT/CS4/CS5
  extensions can reuse it).
- `cexpl`: the exploding segment (`head = tail-member = Set.univ`).
- `CKSegment.ofHead`: every quasi-prime theory is the head of a segment (with the *maximal*
  tail `{t | QuasiPrime t ∧ boxInv H ⊆ t}`; diamonds are witnessed by `Set.univ ∈ tail`).
- `Preorder (CKSegment Axioms)` (`cireach` = head inclusion), `cmreach` (tail membership),
  `cval` (atom membership), `cbotForces` (`⊥ ∈ head` — the canonical fallibility predicate).
- Explosion conditions for the canonical model (`cbotForces_val`/`cbotForces_mreach`/
  `cbotForces_mreach_wit`), matching `CKValid`'s three explosion hypotheses.

## References

* [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990] — fallible worlds.
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5 —
  the underlying prime-extension machinery.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Quasi-Prime Theories -/

/-- A quasi-prime theory: deductively closed with the disjunction property, with **no**
consistency requirement — `Metalogic.PrimeAdmissible` at the trivially-true consistency
predicate. With `efq` among the axioms, a quasi-prime theory is either a consistent prime
theory or the exploding theory `Set.univ`; admitting the latter is what lets the `CK`
canonical model contain fallible worlds (ianshil `general_seg_completeness.v`, `quasi-prime`).
-/
abbrev QuasiPrime (Axioms : Proposition Atom → Prop) (S : Set (Proposition Atom)) : Prop :=
  Metalogic.PrimeAdmissible (modalDerivationSystem Axioms) (fun _ => True) S

/-- A quasi-prime theory is deductively closed. -/
theorem QuasiPrime.closed {Axioms : Proposition Atom → Prop} {S : Set (Proposition Atom)}
    (h : QuasiPrime Axioms S) :
    Metalogic.DeductivelyClosed (modalDerivationSystem Axioms) S :=
  h.1.2

/-- A quasi-prime theory has the disjunction property. -/
theorem QuasiPrime.disj {Axioms : Proposition Atom → Prop} {S : Set (Proposition Atom)}
    (h : QuasiPrime Axioms S) {A B : Proposition Atom} (hmem : A.or B ∈ S) :
    A ∈ S ∨ B ∈ S :=
  h.2 A B hmem

/-- The exploding theory `Set.univ` is quasi-prime. -/
theorem quasiPrime_univ {Axioms : Proposition Atom → Prop} :
    QuasiPrime Axioms (Set.univ : Set (Proposition Atom)) :=
  ⟨⟨trivial, fun _ _ _ _ => Set.mem_univ _⟩, fun _ _ _ => Or.inl (Set.mem_univ _)⟩

/-- If `⊥` belongs to a deductively closed theory, every formula does (by `efq`): the only
quasi-prime theory containing `⊥` is the exploding theory. -/
theorem mem_of_bot_mem {Axioms : Proposition Atom → Prop}
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    {S : Set (Proposition Atom)}
    (h_closed : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms) S)
    (h_bot : (Proposition.bot : Proposition Atom) ∈ S) (φ : Proposition Atom) : φ ∈ S := by
  refine h_closed [Proposition.bot] φ ?_ ?_
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx ▸ h_bot
  · exact ⟨DerivationTree.modus_ponens _ _ _
      (DerivationTree.weakening [] _ _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h))
      (DerivationTree.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩

/-! ## Box/Diamond Inverse Images -/

/-- The box inverse image of a theory: `{B | □B ∈ H}`. -/
def boxInv (H : Set (Proposition Atom)) : Set (Proposition Atom) :=
  {B | Proposition.box B ∈ H}

/-- The diamond inverse image of a theory: `{B | ◇B ∈ H}`. -/
def diaInv (H : Set (Proposition Atom)) : Set (Proposition Atom) :=
  {B | (◇B) ∈ H}

/-! ## Segments -/

/-- A `CK` canonical world: a *segment* `⟨head, tail⟩` (ianshil
`general_seg_completeness.v`, `segment`). `head` is the theory of the world itself; `tail`
collects the theories of its modal successors. Fallible worlds (`⊥ ∈ head`) are permitted:
quasi-primality does not require consistency. -/
structure CKSegment (Axioms : Proposition Atom → Prop) where
  /-- The theory of the world. -/
  head : Set (Proposition Atom)
  /-- The theories of the world's modal successors. -/
  tail : Set (Set (Proposition Atom))
  /-- The head is quasi-prime (deductively closed + disjunction property). -/
  head_qprime : QuasiPrime Axioms head
  /-- Every tail member is quasi-prime. -/
  tail_qprime : ∀ t ∈ tail, QuasiPrime Axioms t
  /-- Box reflection: `□A ∈ head → A` holds in every tail member. -/
  box_reflect : ∀ A, Proposition.box A ∈ head → ∀ t ∈ tail, A ∈ t
  /-- Diamond witness: `◇A ∈ head → A` holds in some tail member. -/
  diam_witness : ∀ A, (◇A) ∈ head → ∃ t ∈ tail, A ∈ t

/-- The exploding segment: everything holds (including `⊥`), and its unique successor theory
is again the exploding theory (ianshil `cexpl`). -/
def cexpl {Axioms : Proposition Atom → Prop} : CKSegment Axioms where
  head := Set.univ
  tail := {Set.univ}
  head_qprime := quasiPrime_univ
  tail_qprime := fun _ ht => Set.mem_singleton_iff.mp ht ▸ quasiPrime_univ
  box_reflect := fun _ _ _ ht => Set.mem_singleton_iff.mp ht ▸ Set.mem_univ _
  diam_witness := fun _ _ => ⟨Set.univ, Set.mem_singleton _, Set.mem_univ _⟩

/-- Every quasi-prime theory `H` is the head of a segment, with the *maximal* tail
`{t | QuasiPrime t ∧ boxInv H ⊆ t}`: box reflection holds by construction, and every diamond
is witnessed by the exploding theory `Set.univ ∈ tail`. -/
def CKSegment.ofHead {Axioms : Proposition Atom → Prop} {H : Set (Proposition Atom)}
    (hH : QuasiPrime Axioms H) : CKSegment Axioms where
  head := H
  tail := {t | QuasiPrime Axioms t ∧ boxInv H ⊆ t}
  head_qprime := hH
  tail_qprime := fun _ ht => ht.1
  box_reflect := fun _ hA _ ht => ht.2 hA
  diam_witness := fun _ _ =>
    ⟨Set.univ, ⟨quasiPrime_univ, Set.subset_univ _⟩, Set.mem_univ _⟩

@[simp] theorem CKSegment.ofHead_head {Axioms : Proposition Atom → Prop}
    {H : Set (Proposition Atom)} (hH : QuasiPrime Axioms H) :
    (CKSegment.ofHead hH).head = H := rfl

/-! ## Canonical Frame Data -/

/-- The canonical preorder on segments (`cireach`): head inclusion. Segments with the same
head but different tails are `≤`-equivalent — this freedom is what powers the box/diamond
truth-lemma cases without any Fischer-Servi axiom. -/
instance {Axioms : Proposition Atom → Prop} : Preorder (CKSegment Axioms) where
  le P Q := P.head ⊆ Q.head
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂

/-- `≤` on segments is head inclusion (definitional unfolding lemma). -/
theorem CKSegment.le_iff {Axioms : Proposition Atom → Prop} {P Q : CKSegment Axioms} :
    P ≤ Q ↔ P.head ⊆ Q.head := Iff.rfl

/-- The canonical modal accessibility (`cmreach`): `P` reaches exactly the segments whose
head is a member of `P`'s tail. The diamond witnesses are *structural* (read off the tail),
which is why `CK` needs neither `Cd` nor `Idb`. -/
def cmreach {Axioms : Proposition Atom → Prop} (P Q : CKSegment Axioms) : Prop :=
  Q.head ∈ P.tail

/-- The canonical valuation (`cval`): atom membership in the head. -/
def cval {Axioms : Proposition Atom → Prop} (s : CKSegment Axioms) (p : Atom) : Prop :=
  Proposition.atom p ∈ s.head

/-- The canonical fallibility predicate: a segment forces `⊥` iff `⊥` belongs to its head.
Non-trivially true exactly at the exploding segments. -/
def cbotForces {Axioms : Proposition Atom → Prop} (s : CKSegment Axioms) : Prop :=
  (Proposition.bot : Proposition Atom) ∈ s.head

/-- The canonical valuation is upward-closed under `cireach`. -/
theorem cval_upward_closed {Axioms : Proposition Atom → Prop}
    {P Q : CKSegment Axioms} (p : Atom) (h : P ≤ Q) (hv : cval P p) : cval Q p :=
  h hv

/-- The canonical fallibility predicate is upward-closed under `cireach`. -/
theorem cbotForces_upward_closed {Axioms : Proposition Atom → Prop}
    {P Q : CKSegment Axioms} (h : P ≤ Q) (hb : cbotForces P) : cbotForces Q :=
  h hb

/-! ## Explosion Conditions for the Canonical Model

The three explosion hypotheses of `CKValid`, verified for the canonical segment model with
`botForces := cbotForces`. -/

/-- Exploding segments force all atoms: `⊥ ∈ head` and heads are deductively closed, so by
`efq` every formula (in particular every atom) is in the head. -/
theorem cbotForces_val {Axioms : Proposition Atom → Prop}
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    {s : CKSegment Axioms} (p : Atom) (hb : cbotForces s) : cval s p :=
  mem_of_bot_mem h_efq s.head_qprime.closed hb _

/-- Modal successors of exploding segments explode: `⊥ ∈ head` gives `□⊥ ∈ head` (by `efq`
and closure), and box reflection places `⊥` in every tail member. -/
theorem cbotForces_mreach {Axioms : Proposition Atom → Prop}
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    {s Q : CKSegment Axioms} (hb : cbotForces s) (hr : cmreach s Q) : cbotForces Q :=
  s.box_reflect _ (mem_of_bot_mem h_efq s.head_qprime.closed hb (Proposition.box .bot))
    Q.head hr

/-- Every exploding segment has an exploding modal successor: `◇⊥ ∈ head` (by `efq` and
closure), so the diamond-witness field yields a tail member containing `⊥`; realize it as a
segment via `CKSegment.ofHead`. -/
theorem cbotForces_mreach_wit {Axioms : Proposition Atom → Prop}
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    {s : CKSegment Axioms} (hb : cbotForces s) :
    ∃ Q : CKSegment Axioms, cmreach s Q ∧ cbotForces Q := by
  obtain ⟨t, ht_mem, ht_bot⟩ :=
    s.diam_witness _ (mem_of_bot_mem h_efq s.head_qprime.closed hb (◇Proposition.bot))
  exact ⟨CKSegment.ofHead (s.tail_qprime t ht_mem), ht_mem, ht_bot⟩

end Cslib.Logic.Modal
