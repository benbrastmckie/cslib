/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Powerset
public import Cslib.Foundations.Logic.Tableau.Branch

/-! # Containment Blocking

This module provides the label-generic containment-blocking device shared by tableau
termination arguments: the *type* of a label (its deduplicated list of signed formulas)
and the Boolean containment test between the types of two labels.

Containment blocking (also called subset blocking or ancestor blocking) stops tableau
expansion at a label whose signed type is contained in that of another label: any model
fragment the new label could contribute is already represented. The device here is purely
structural. Side conditions governing *when* blocking may fire — ancestor direction,
freshness of the trigger formula, eventuality duplication — differ between logics and
deliberately stay logic-specific; this module exposes only containment (and, in the
counting layer, the cardinality bounds that make blocking terminate). See
[Massacci2000], Technique 8.1/8.2, for why per-obligation blocking conditions are
logic-specific.

## Main Definitions

- `Branch.typeAt`: The signed type of a label — the deduplicated `(Sign, formula)` pairs
  occurring at that label on the branch.
- `Branch.posTypeAt`: The positive projection of the type — deduplicated formulas signed
  positively at the label.
- `Branch.containmentBlocked`: `true` when every signed pair at the first label also
  occurs at the second.

## Main Statements

- `Branch.mem_typeAt_iff`: Membership in `typeAt` is membership of the corresponding
  signed formula on the branch.
- `Branch.containmentBlocked_iff`: `containmentBlocked` decides type containment.
- `distinctTypes_le_pow`: A branch over a signed universe `V` exhibits at most
  `2 ^ V.card` distinct types.
- `exists_typeAt_eq_of_card_lt`: Pigeonhole — more than `2 ^ V.card` labels force two
  labels with the same type.
- `strictChain_le_card`: A strictly growing chain of finsets inside `U` has at most
  `U.card` steps.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
* [D. Garg, V. Genovese, S. Negri, *Countermodels from sequent calculi in multi-modal
  logics*][GargGenoveseNegri2012]
* [F. Massacci, *Single Step Tableaux for Modal Logics*][Massacci2000]
-/

@[expose] public section

namespace Cslib.Logic.Tableau

namespace Branch

/-- The *signed type* of label `l` on branch `b`: the deduplicated list of
`(sign, formula)` pairs occurring at `l`.

The sign is kept — two labels with the same positive formulas but different negative
formulas have different types. For the positive-only (Sfor) projection, see
`posTypeAt`. -/
def typeAt [BEq F] [BEq L] (b : Branch F L) (l : L) : List (Sign × F) :=
  ((b.filter fun sf => sf.label == l).map fun sf => (sf.sign, sf.formula)).eraseDups

/-- The *positive type* of label `l` on branch `b`: the deduplicated list of formulas
signed positively at `l` (the Sfor projection of `typeAt`). -/
def posTypeAt [BEq F] [BEq L] (b : Branch F L) (l : L) : List F :=
  ((b.filter fun sf => sf.sign == .pos && sf.label == l).map (·.formula)).eraseDups

/-- `true` when the signed type of `l_new` is contained in the signed type of `l_anc`:
every `(sign, formula)` pair at `l_new` also occurs at `l_anc`.

This is the structural containment test only. Side conditions (ancestor direction,
trigger-formula freshness, eventuality handling) are logic-specific and are supplied by
each calculus at its call site. -/
def containmentBlocked [BEq F] [BEq L] (b : Branch F L) (l_new l_anc : L) : Bool :=
  (b.typeAt l_new).all fun pair => (b.typeAt l_anc).any (pair == ·)

/-- Membership characterization of `typeAt`: the pair `(s, φ)` is in the signed type of
`l` exactly when the signed formula `⟨s, φ, l⟩` occurs on the branch. -/
lemma mem_typeAt_iff [BEq F] [BEq L] [LawfulBEq F] [LawfulBEq L] {b : Branch F L} {l : L}
    {s : Sign} {φ : F} :
    (s, φ) ∈ b.typeAt l ↔ (⟨s, φ, l⟩ : SignedFormula F L) ∈ b := by
  simp only [typeAt, List.mem_eraseDups, List.mem_map, List.mem_filter, beq_iff_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨sf, ⟨hmem, hl⟩, hs, hφ⟩
    obtain ⟨s', φ', l'⟩ := sf
    cases hl; cases hs; cases hφ
    exact hmem
  · intro hmem
    exact ⟨⟨s, φ, l⟩, ⟨hmem, rfl⟩, rfl, rfl⟩

/-- `containmentBlocked` decides containment of signed types: it is `true` exactly when
every pair in the type of `l₁` is also in the type of `l₂`. -/
lemma containmentBlocked_iff [BEq F] [BEq L] [LawfulBEq F] {b : Branch F L}
    {l₁ l₂ : L} :
    b.containmentBlocked l₁ l₂ = true ↔ ∀ x ∈ b.typeAt l₁, x ∈ b.typeAt l₂ := by
  simp [containmentBlocked, List.all_eq_true, List.any_eq_true]

end Branch

/-! ## Counting layer

The lemmas below bound the number of distinct types a branch can exhibit, which is what
makes containment blocking terminate: over a signed universe `V` there are at most
`2 ^ V.card` distinct types (`distinctTypes_le_pow`), so a branch with more labels than
that must repeat a type (`exists_typeAt_eq_of_card_lt`), and a strictly growing chain of
types has length at most `V.card` (`strictChain_le_card`, the chain bound of
[GargGenoveseNegri2012]).

The universe is *signed*: types range over subsets of `Sign × F`, so the count is
`2 ^ V.card` over `V : Finset (Sign × F)` — instantiating `V = S ×ˢ {pos, neg}` for a
subformula universe `S` yields a `2 ^ (2 · S.card)` bound, and the positive projection
(`Branch.posTypeAt`) over `U : Finset F` yields `2 ^ U.card`. -/

/-- Powerset counting: if `f` maps every element of `s` into a subset of `U`, then `f`
takes at most `2 ^ U.card` distinct values on `s`. Projection-agnostic helper shared by
the signed (`Branch.typeAt`) and positive (`Branch.posTypeAt`) instantiations. -/
theorem card_image_le_pow_of_forall_subset [DecidableEq β] (s : Finset α)
    (f : α → Finset β) (U : Finset β) (h : ∀ a ∈ s, f a ⊆ U) :
    (s.image f).card ≤ 2 ^ U.card := by
  calc (s.image f).card ≤ U.powerset.card := by
        refine Finset.card_le_card fun t ht => ?_
        rw [Finset.mem_powerset]
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
        exact h a ha
    _ = 2 ^ U.card := Finset.card_powerset U

/-- `eraseDups` does not change the set of elements of a list: the `Finset` bridge
between the `List`-valued types and the counting layer. -/
theorem toFinset_eraseDups [DecidableEq α] [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.toFinset = l.toFinset := by
  ext a
  simp [List.mem_eraseDups]

/-- A branch whose signed formulas all lie in the signed universe `V` exhibits at most
`2 ^ V.card` distinct types. See [GargGenoveseNegri2012], §III, for the corresponding
count of distinct forced sets. -/
theorem distinctTypes_le_pow [DecidableEq F] [DecidableEq L] [BEq F] [LawfulBEq F]
    [BEq L] [LawfulBEq L] (b : Branch F L) (V : Finset (Sign × F))
    (hV : ∀ sf ∈ b, (sf.sign, sf.formula) ∈ V) :
    (b.labels.toFinset.image fun l => (b.typeAt l).toFinset).card ≤ 2 ^ V.card := by
  refine card_image_le_pow_of_forall_subset _ _ _ fun l _ => ?_
  intro x hx
  obtain ⟨s, φ⟩ := x
  rw [List.mem_toFinset, Branch.mem_typeAt_iff] at hx
  exact hV _ hx

/-- Pigeonhole: a branch over the signed universe `V` with more than `2 ^ V.card`
distinct labels has two distinct labels with the same type. This is the loop-detection
core behind containment blocking. -/
theorem exists_typeAt_eq_of_card_lt [DecidableEq F] [DecidableEq L] [BEq F] [LawfulBEq F]
    [BEq L] [LawfulBEq L] (b : Branch F L) (V : Finset (Sign × F))
    (hV : ∀ sf ∈ b, (sf.sign, sf.formula) ∈ V)
    (hcard : 2 ^ V.card < b.labels.toFinset.card) :
    ∃ l₁ ∈ b.labels, ∃ l₂ ∈ b.labels, l₁ ≠ l₂ ∧
      (b.typeAt l₁).toFinset = (b.typeAt l₂).toFinset := by
  have hmaps : ∀ l ∈ b.labels.toFinset, (b.typeAt l).toFinset ∈ V.powerset := by
    intro l _
    rw [Finset.mem_powerset]
    intro x hx
    obtain ⟨s, φ⟩ := x
    rw [List.mem_toFinset, Branch.mem_typeAt_iff] at hx
    exact hV _ hx
  have hlt : V.powerset.card < b.labels.toFinset.card := by
    rwa [Finset.card_powerset]
  obtain ⟨l₁, hl₁, l₂, hl₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  exact ⟨l₁, List.mem_toFinset.mp hl₁, l₂, List.mem_toFinset.mp hl₂, hne, heq⟩

/-- Strict-chain bound: a chain of finsets growing strictly at each of `k` steps and
ending inside `U` has at most `U.card` steps. This is the chain argument of
[GargGenoveseNegri2012] behind termination of blocking tableau constructions. -/
theorem strictChain_le_card {k : Nat} (f : Nat → Finset β) (U : Finset β)
    (hchain : ∀ i, i < k → f i ⊂ f (i + 1)) (hU : f k ⊆ U) : k ≤ U.card := by
  have key : ∀ i, i ≤ k → i ≤ (f i).card := by
    intro i
    induction i with
    | zero => exact fun _ => Nat.zero_le _
    | succ n ih =>
      intro hn
      have h1 : n ≤ (f n).card := ih (Nat.le_of_succ_le hn)
      have h2 : (f n).card < (f (n + 1)).card := Finset.card_lt_card (hchain n hn)
      omega
  have h1 := key k le_rfl
  have h2 := Finset.card_le_card hU
  omega

end Cslib.Logic.Tableau

end
