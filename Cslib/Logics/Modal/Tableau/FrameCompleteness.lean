/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Completeness
public import Cslib.Logics.Modal.Tableau.LoopChecking
public import Cslib.Logics.Modal.Tableau.FrameSoundness
public import Cslib.Logics.Modal.Tableau.TDriver
public import Cslib.Logics.Modal.Tableau.BDriver

/-! # Frame-Relativized Modal Tableau Completeness (Shared Extractor Skeleton)

This module fixes the shared **closure-at-extraction** helper used by every frame-specific
completeness proof (T, S4, S5, B, 5): given an open saturated branch `b` and accessibility
relation `acc`, extract a Kripke model whose relation is a *closure* `Cl acc.hasEdge` of the
raw tableau accessibility relation, rather than `acc.hasEdge` itself (as `extractModel` does
for K, `Completeness.lean:59`).

## Strategy (Strategy B, closure-at-extraction)

Per-system phases instantiate `Cl` with a Mathlib closure operator so the frame-condition
instance comes free:

| System | Closure operator `Cl` | Frame instance (free) |
|--------|------------------------|------------------------|
| T      | `Relation.ReflGen`     | `Std.Refl` |
| S4     | `Relation.ReflTransGen`| `Std.Refl`, `IsTrans` |
| B      | `Relation.SymmGen`     | `Std.Symm` |
| S5     | universal (`fun _ _ => True`) or `Relation.EqvGen` | `IsEquiv` |

No new frame predicates are defined here — the per-system files reuse the `Cube.lean` frame
classes (`Std.Refl`, `IsTrans`, `Std.Symm`, `Relation.RightEuclidean`) and the
`Satisfies.t`/`Satisfies.b`/`Satisfies.four`/`Satisfies.five` semantic validity theorems for
their soundness arms.

## Main Definitions

- `extractModelWith`: parameterized model extractor over a closure operator `Cl`, mirroring
  `extractModel` (`Completeness.lean:59`) but with `r := Cl acc.hasEdge` instead of
  `r := acc.hasEdge`. The valuation clause is preserved verbatim.

## Notes

This file intentionally does **not** commit to a truth lemma or Hintikka-set characterization:
those are frame-specific (each system's saturation rules determine what Hintikka property the
open branch enjoys, hence what the truth lemma needs to bridge across the closure's extra
edges). Per-system phases add their own `extractModel{T,S4,B,...}` (specialized instances of
`extractModelWith`) and truth lemmas in `FrameCompleteness.lean` / their own dedicated file
(`S5Simplification.lean`, `LoopChecking.lean`), reusing this module's docstring conventions.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

universe v
variable {Atom : Type v} [DecidableEq Atom] [Hashable Atom]

/-! ## Shared Closure-at-Extraction Helper -/

/-- Extract a Kripke model from an open saturated branch `b` and accessibility relation `acc`,
using the closure `Cl acc.hasEdge` as the model's relation instead of `acc.hasEdge` itself
(Strategy B, closure-at-extraction). The world type is `WorldIndex` (= `Nat`), matching
`extractModel` (`Completeness.lean:59`); the valuation clause is preserved verbatim: atom `p`
holds at world `w` iff `T(atom p)@w ∈ b`.

Per-system phases instantiate `Cl` with a Mathlib closure operator
(`Relation.ReflGen`/`ReflTransGen`/`SymmGen`, or the universal relation for S5) so that the
frame-condition instance (`Std.Refl`, `IsTrans`, `Std.Symm`, `IsEquiv`) comes free off the
closure operator — see the module docstring table. -/
def extractModelWith
    (Cl : (WorldIndex → WorldIndex → Prop) → (WorldIndex → WorldIndex → Prop))
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom where
  r := Cl (fun w w' => acc.hasEdge w w' = true)
  v w p := b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w) = true

omit [Hashable Atom] in
/-- `extractModelWith` with the identity closure operator is exactly `extractModel` (K). -/
lemma extractModelWith_id (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    extractModelWith (Atom := Atom) id b acc = extractModel b acc := rfl

/-! ## T (Reflexive Frame) Extraction -/

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*reflexive closure* `Relation.ReflGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.ReflGen`). The frame instance
`Std.Refl` comes free off `Relation.reflexive_reflGen` (see `extractModelT_refl` below); no
new frame predicate is defined. -/
def extractModelT
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (Relation.ReflGen) b acc

omit [Hashable Atom] in
/-- `extractModelT`'s relation is exactly the reflexive closure of `acc.hasEdge`. -/
lemma extractModelT_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelT b acc).r = Relation.ReflGen (fun w w' => acc.hasEdge w w' = true) := rfl

omit [Hashable Atom] in
/-- The reflexive frame condition holds of `extractModelT b acc` "for free": `Relation.ReflGen`
is always reflexive (`Relation.reflexive_reflGen`), regardless of the underlying raw edge
relation `acc.hasEdge`. Discharges the `reflFC` witness (`FrameSoundness.lean`) for the T
countermodel. -/
lemma extractModelT_refl (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Std.Refl (extractModelT b acc).r := by
  rw [extractModelT_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelT`'s
(reflexive-closure) relation via `Relation.ReflGen.single`. Needed to reuse the K bridge
lemmas (`hintikka_box_pos`, `hintikka_diamond_pos`, etc.), which are stated in terms of
`acc.hasEdge`, when relating them to `extractModelT`'s closed relation. -/
lemma extractModelT_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelT b acc).r w w' := by
  rw [extractModelT_r]
  exact Relation.ReflGen.single h

/-! ## S4 (Reflexive-Transitive Frame) Extraction -/

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*reflexive-transitive closure* `Relation.ReflTransGen` of `acc.hasEdge` as the model's relation
(Strategy B, closure-at-extraction, instantiated with `Cl := Relation.ReflTransGen`). Both the
`Std.Refl` and `IsTrans` frame instances come free off `Relation.ReflTransGen`
(`extractModelS4_refl`, `extractModelS4_trans` below); no new frame predicate is defined. -/
def extractModelS4
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (Relation.ReflTransGen) b acc

omit [Hashable Atom] in
/-- `extractModelS4`'s relation is exactly the reflexive-transitive closure of `acc.hasEdge`. -/
lemma extractModelS4_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelS4 b acc).r =
      Relation.ReflTransGen (fun w w' => acc.hasEdge w w' = true) := rfl

omit [Hashable Atom] in
/-- The reflexive frame condition holds of `extractModelS4 b acc` "for free":
`Relation.ReflTransGen` is always reflexive (`Relation.reflexive_reflTransGen`), regardless of
the underlying raw edge relation `acc.hasEdge`. Discharges half of the `s4FC` witness
(`FrameSoundness.lean`) for the S4 countermodel. -/
lemma extractModelS4_refl (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Std.Refl (extractModelS4 b acc).r := by
  rw [extractModelS4_r]
  infer_instance

omit [Hashable Atom] in
/-- The transitive frame condition holds of `extractModelS4 b acc` "for free":
`Relation.ReflTransGen` is always transitive (`Relation.transitive_reflTransGen`), regardless
of the underlying raw edge relation `acc.hasEdge`. Discharges the other half of the `s4FC`
witness (`FrameSoundness.lean`) for the S4 countermodel. Note this is Mathlib's `IsTrans`
class (matching the `Cube.lean` spelling of S4's transitivity), while `extractModelT_refl`
above uses `Std.Refl` -- the two frame instances have different (mixed) provenance in
Mathlib, and both are picked up here unchanged. -/
lemma extractModelS4_trans (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    IsTrans WorldIndex (extractModelS4 b acc).r := by
  rw [extractModelS4_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelS4`'s
(reflexive-transitive-closure) relation via `Relation.ReflTransGen.single`. Needed to lift the
S4 bridge lemmas' single-edge hypotheses (`LoopChecking.lean`) into the closure whenever a raw
edge (rather than a whole `ReflTransGen` path) is at hand. -/
lemma extractModelS4_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelS4 b acc).r w w' := by
  rw [extractModelS4_r]
  exact Relation.ReflTransGen.single h

/-! ## S4 Modal Truth Lemma -/

/-- `modalApplyOneS4 φ₀` agrees with the plain K dispatch `modalApplyOne` on every
non-modal-shaped signed formula (i.e. neither `box`- nor `diamond`-shaped, regardless of
sign): none of the guard's two minting shapes (`F(□·)`, `T(◇·)`) or the 4-rule/T-self
shapes (`T(□·)`, `F(◇·)`) apply, so the three-layer dispatch
(`modalApplyOneS4` → `modalApplyOneS4Rules` → `modalApplyOneT` → `modalApplyOne`) collapses
via `modalApplyOneS4_eq_of_not_boxNeg_diaPos`, `modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg`,
and `modalApplyOneT_eq_of_not_boxPos_diaNeg` chained together. This is exactly what lets the
S4 truth lemma's propositional cases (`imp`/`and`/`or`/`atom`/`bot`) reuse K's
`modalApplyOne_imp_pos` etc. bridge lemmas verbatim. -/
private lemma modalApplyOneS4_eq_of_not_modal_shaped
    (φ₀ : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hnb : ∀ φ, sf.formula ≠ .box φ) (hnd : ∀ φ, sf.formula ≠ .diamond φ) :
    modalApplyOneS4 φ₀ sf b acc = modalApplyOne sf b acc := by
  have hguard : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
      ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
    ⟨fun ⟨_, φ, h⟩ => hnb φ h, fun ⟨_, φ, h⟩ => hnd φ h⟩
  have hfour : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
      ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
    ⟨fun ⟨_, φ, h⟩ => hnb φ h, fun ⟨_, φ, h⟩ => hnd φ h⟩
  rw [modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc hguard,
    modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc hfour,
    modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc hfour]

/-- Modal Truth Lemma for S4: membership in an S4 Hintikka branch tracks satisfaction in the
extracted reflexive-transitive Kripke model `extractModelS4 b acc`.

For every formula `φ` and world `w`, `T(φ)@w ∈ b` implies `φ` is satisfied at `w` in
`extractModelS4 b acc`, and `F(φ)@w ∈ b` implies it is not. Proof by strong induction on
`modalComplexity φ`, mirroring `modalTruthLemma` (`Completeness.lean`): the propositional
cases (`atom`/`bot`/`imp`/`and`/`or`) reuse the public, apply-agnostic consistency kit
(`openBranch_noTBot`/`openBranch_noContradiction`) and K's `modalApplyOne_*` bridge lemmas
verbatim, routed through `modalApplyOneS4_eq_of_not_modal_shaped`; the box/diamond cases
consume the S4-specific `hintikkaS4_box_pos_reflTransGen`/`hintikkaS4_box_neg`/
`hintikkaS4_diamond_pos`/`hintikkaS4_dia_neg_reflTransGen` bridges (`LoopChecking.lean`),
with the model's `r w w'` unfolding to exactly the `ReflTransGen` hypothesis those bridges
want (`extractModelS4_r`). This is a genuinely new induction, not a reuse of
`modalTruthLemma`: that lemma is pinned to `extractModel` (`r := acc.hasEdge`), whereas
`extractModelS4`'s `r` is the reflexive-transitive closure -- different propositions. -/
lemma modalTruthLemmaS4
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelS4 b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelS4 b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelS4 b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelS4 b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelS4 b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelS4 b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelS4, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelS4, extractModelWith, List.any_eq_true] at hsat
        obtain ⟨sf, hsf_mem, hcond⟩ := hsat
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨hsign, hform⟩, hlab⟩ := hcond
        have hsign_eq : sf.sign = .pos := eq_of_beq hsign
        have hform_eq : sf.formula = .atom p := eq_of_beq hform
        have hlab_eq : sf.label = w := eq_of_beq hlab
        have hpos : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
          convert hsf_mem using 1; rcases sf with ⟨s, f, l⟩; simp_all
        exact openBranch_noContradiction b hHopen (.atom p) w hpos hmem
    | bot =>
      refine ⟨fun hmem => absurd hmem (openBranch_noTBot b hHopen w), ?_⟩
      intro _ hsat
      exact hsat
    | imp a c =>
      rcases eq_or_ne c Proposition.bot with rfl | hne
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          intro hna
          have hlt : modalComplexity a < n := by
            rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega
          exact hna ((IH a hlt w).1 hxmem)
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_imp hne] at hcond
          intro hsa
          obtain ⟨br, hbr_mem, hbr⟩ := hcond
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · exact absurd hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2
              (hbr ⟨.neg, a, w⟩ (by simp)))
          · exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1
              (hbr ⟨.pos, c, w⟩ (by simp))
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_imp hne] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          have hymem : (⟨.neg, c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, c, w⟩ (by simp)
          intro hsa
          exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2 hymem
            (hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1 hxmem))
    | and φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_neg] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rintro ⟨hsφ, hsψ⟩
        rcases hbr_mem with rfl | rfl
        · exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, φ', w⟩ (by simp)))
        · exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, ψ', w⟩ (by simp)))
    | or φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_pos] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · exact Or.inl ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, φ', w⟩ (by simp)))
        · exact Or.inr ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, ψ', w⟩ (by simp)))
      · intro hmem
        have hcond := hHrule ⟨.neg, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_neg] at hcond
        intro hs
        cases hs with
        | inl hsφ => exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, φ', w⟩ (by simp)))
        | inr hsψ => exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, ψ', w⟩ (by simp)))
    | box ψ =>
      constructor
      · intro hmem w' hr
        have hpath : Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelS4_r b acc ▸ hr
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1
          (hintikkaS4_box_pos_reflTransGen φ₀ b acc hH ψ w w' hmem hpath)
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikkaS4_box_neg φ₀ b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelS4_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikkaS4_diamond_pos φ₀ b acc hH ψ w hmem
        exact ⟨w', extractModelS4_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath : Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelS4_r b acc ▸ hw'
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2
          (hintikkaS4_dia_neg_reflTransGen φ₀ b acc hH ψ w w' hmem hpath) hsψ

/-- An open S4 Hintikka branch with `F(φ₀)@0 ∈ b` yields a reflexive-transitive Kripke
countermodel to `φ₀`. The extracted model `extractModelS4 b acc` falsifies `φ₀` at world
`0`, and its relation satisfies `s4FC` "for free" (`extractModelS4_refl`/
`extractModelS4_trans`, both discharged with no manual frame reasoning). Mirrors
`modalOpenBranch_countermodel` (`Completeness.lean`). -/
theorem modalOpenBranchS4_countermodel
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility)
    (hH : modalHintikkaSetS4 φ₀ b acc)
    (hF : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (¬ Satisfies (extractModelS4 b acc) 0 φ₀) ∧ s4FC (extractModelS4 b acc).r :=
  ⟨(modalTruthLemmaS4 φ₀ b acc hH φ₀ 0).2 hF,
    ⟨extractModelS4_refl b acc, extractModelS4_trans b acc⟩⟩

/-! ## B (Symmetric Frame) Extraction (task 505 Phase 5)

Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*symmetric closure* `Relation.SymmGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.SymmGen`). The frame instance
`Std.Symm` comes free off `Relation.SymmGen`'s own unnamed `instance : Std.Symm (SymmGen r)`
(`Mathlib.Logic.Relation`); no new frame predicate is defined. Unlike `Relation.ReflGen`/
`Relation.ReflTransGen` (inductive types with named constructors `.refl`/`.single`/`.tail`),
`Relation.SymmGen r a b` is literally `r a b ∨ r b a` (a `def`, not an inductive), so case
analysis on a `SymmGen` hypothesis is a plain `Or` split -- the forward direction reduces to
K's own successor argument, the backward direction to B's own predecessor argument
(`hintikkaB_box_pos`/`hintikkaB_diamond_neg`, Phase 6 below). -/

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*symmetric closure* `Relation.SymmGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.SymmGen`). -/
def extractModelB
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (Relation.SymmGen) b acc

omit [Hashable Atom] in
/-- `extractModelB`'s relation is exactly the symmetric closure of `acc.hasEdge`. -/
lemma extractModelB_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelB b acc).r = Relation.SymmGen (fun w w' => acc.hasEdge w w' = true) := rfl

omit [Hashable Atom] in
/-- The symmetric frame condition holds of `extractModelB b acc` "for free": `Relation.SymmGen`
is always symmetric (its own unnamed `instance : Std.Symm (SymmGen r)`, `Mathlib.Logic.
Relation`), regardless of the underlying raw edge relation `acc.hasEdge`. Discharges the
`symmFC` witness (`FrameSoundness.lean`) for the B countermodel. -/
lemma extractModelB_symm (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Std.Symm (extractModelB b acc).r := by
  rw [extractModelB_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelB`'s
(symmetric-closure) relation via `Relation.SymmGen.of_rel` (`Or.inl`). Needed to reuse the K
bridge lemmas (`hintikka_box_neg`, `hintikka_diamond_pos`, etc.), which are stated in terms of
`acc.hasEdge`, when relating them to `extractModelB`'s closed relation. -/
lemma extractModelB_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelB b acc).r w w' := by
  rw [extractModelB_r]
  exact Relation.SymmGen.of_rel h

omit [Hashable Atom] in
/-- The *backward* direction survives into `extractModelB`'s relation too, via
`Relation.SymmGen.of_rel_symm` (`Or.inr`): a raw edge `v → w` (`acc.hasEdge v w`) gives
`(extractModelB b acc).r w v` (the reversed pair) directly -- the symmetric-closure analogue of
`extractModelB_hasEdge_imp_r` for the predecessor direction B's own rule reads. -/
lemma extractModelB_hasEdge_symm_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {v w : WorldIndex} (h : acc.hasEdge v w = true) :
    (extractModelB b acc).r w v := by
  rw [extractModelB_r]
  exact Relation.SymmGen.of_rel_symm h

/-! ## T Modal Truth Lemma (task 503 Phase 5)

`modalExpandBranchesT_hintikka` (`TDriver.lean`, delivered by task 510) produces a
`modalHintikkaSetGen modalApplyOneT bR aR` witness from an open `modalExpandBranchesT` result.
This section closes the remaining gap: the T truth lemma against `extractModelT` and `tValid`
completeness.

`modalApplyOneT` agrees with `modalApplyOne` outside the box-positive/diamond-negative shapes
(`modalApplyOneT_eq_of_not_boxPos_diaNeg`, `FrameRules.lean`), so every propositional case and
the box-negative/diamond-positive modal cases reduce to exactly the K argument (the latter two
via the free generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`,
`Completeness.lean`, task 510). The box-positive and diamond-negative cases are genuinely new:
`hintikkaT_box_pos`/`hintikkaT_diamond_neg` below combine the K argument (raw recorded edge,
`Relation.ReflGen.single`) with the T self-propagation conjunct (reflexive self-edge,
`Relation.ReflGen.refl`), as task 510's own research anticipated
(`hintikka_box_pos`/`hintikka_diamond_neg` are payload-reading and irreducibly K-specific). -/

omit [Hashable Atom] in
/-- `modalApplyOneT` agrees with `modalApplyOne` on every signed formula whose formula
component is neither `box`- nor `diamond`-shaped (regardless of sign) -- specialization of
`modalApplyOneT_eq_of_not_boxPos_diaNeg` (`FrameRules.lean`) used by the propositional cases of
`modalTruthLemmaT` below (mirrors `FrameSoundness.lean`'s S4 analog
`modalApplyOneS4_eq_of_not_modal_shaped`, simplified to T's single-layer dispatch). -/
private lemma modalApplyOneT_eq_of_not_box_diamond
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hnb : ∀ φ, sf.formula ≠ .box φ) (hnd : ∀ φ, sf.formula ≠ .diamond φ) :
    modalApplyOneT sf b acc = modalApplyOne sf b acc :=
  modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc
    ⟨fun ⟨_, φ, h⟩ => hnb φ h, fun ⟨_, φ, h⟩ => hnd φ h⟩

omit [Hashable Atom] in
/-- Local re-derivation of `TDriver.lean`'s `private lemma modalApplyOneT_boxPos_fst` (that
lemma is `private` to its own file, hence unavailable here): direct unfolding of
`modalApplyOneT`'s `.fst` component at a box-positive shaped signed formula, in terms of the
underlying `modalApplyOne` (K) result. Proof reproduced verbatim (three lines), not
re-designed. -/
private lemma modalApplyOneT_boxPos_fst'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOne (⟨.pos, .box φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            .persistent (kForms ++
              (modalTBoxSelf b φ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTBoxSelf b φ w).isEmpty then .notApplicable
            else .persistent (modalTBoxSelf b φ w)
          | other => other) := by
  simp only [modalApplyOneT]
  cases (modalApplyOne (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Symmetric to `modalApplyOneT_boxPos_fst'` for the diamond-negative shape. -/
private lemma modalApplyOneT_diamondNeg_fst'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            .persistent (kForms ++
              (modalTDiaNegSelf b φ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTDiaNegSelf b φ w).isEmpty then .notApplicable
            else .persistent (modalTDiaNegSelf b φ w)
          | other => other) := by
  simp only [modalApplyOneT]
  cases (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- `modalTBoxSelf b φ w = []` iff `T(φ)@w` is already on the branch (direct unfolding of
`modalTBoxSelf`'s `if`-guard). -/
private lemma modalTBoxSelf_eq_nil_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) :
    modalTBoxSelf b φ w = [] ↔
      (⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  simp only [modalTBoxSelf]
  split_ifs with h
  · simpa using h
  · simp only [false_iff]
    simpa using h

omit [Hashable Atom] in
/-- Symmetric to `modalTBoxSelf_eq_nil_iff` for `modalTDiaNegSelf`. -/
private lemma modalTDiaNegSelf_eq_nil_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) :
    modalTDiaNegSelf b φ w = [] ↔
      (⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  simp only [modalTDiaNegSelf]
  split_ifs with h
  · simpa using h
  · simp only [false_iff]
    simpa using h

omit [Hashable Atom] in
/-- If `modalTBoxSelf b φ w ≠ []`, it is exactly the singleton `[T(φ)@w]`, with `T(φ)@w ∉ b`
(the negation of `modalTBoxSelf_eq_nil_iff`, unfolded to expose the singleton payload). -/
private lemma modalTBoxSelf_cases_of_ne_nil
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {φ : Proposition Atom}
    {w : WorldIndex} (hself : modalTBoxSelf b φ w ≠ []) :
    modalTBoxSelf b φ w = [(⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)] ∧
      (⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b := by
  simp only [modalTBoxSelf] at hself ⊢
  split_ifs at hself ⊢ with h
  · exact absurd rfl hself
  · exact ⟨rfl, by simpa using h⟩

omit [Hashable Atom] in
/-- Symmetric to `modalTBoxSelf_cases_of_ne_nil` for `modalTDiaNegSelf`. -/
private lemma modalTDiaNegSelf_cases_of_ne_nil
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {φ : Proposition Atom}
    {w : WorldIndex} (hself : modalTDiaNegSelf b φ w ≠ []) :
    modalTDiaNegSelf b φ w = [(⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)] ∧
      (⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b := by
  simp only [modalTDiaNegSelf] at hself ⊢
  split_ifs at hself ⊢ with h
  · exact absurd rfl hself
  · exact ⟨rfl, by simpa using h⟩

/-- **T-analog of `hintikka_box_pos`** (`Completeness.lean`, genuinely new content -- not
inherited from K, per task 510's research note that this bridge is payload-reading and
irreducibly K-specific): `T(□ψ)@w ∈ b` together with the reflexive closure
`Relation.ReflGen acc.hasEdge w w'` (i.e. `w' = w` or a raw recorded edge `w → w'`) and
`modalHintikkaSetGen modalApplyOneT b acc` imply `T(ψ)@w' ∈ b`.

The `.refl` case (`w' = w`) is the genuinely-new T box-positive self-propagation conjunct: either
`modalTBoxSelf b ψ w = []` (meaning `T(ψ)@w` is already on the branch,
`modalTBoxSelf_eq_nil_iff`) or `modalApplyOneT`'s merged persistent output forces it in
(`modalApplyOneT_boxPos_fst'`). The `.single` case (raw edge) reduces to the same
`boxPropagation`-membership argument `hintikka_box_pos` inlines, since T's persistent output at
this shape is K's own `kForms` merged with the self-conjunct at a possibly-different world, so
`kForms` (hence the K successor witness) survives into T's merged forcing list unchanged. -/
lemma hintikkaT_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneT b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : Relation.ReflGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hcond := hH.2.1 (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  cases hr with
  | refl =>
    rcases eq_or_ne (modalTBoxSelf b ψ w) [] with hself | hself
    · exact (modalTBoxSelf_eq_nil_iff b ψ w).mp hself
    · rw [modalApplyOneT_boxPos_fst'] at hcond
      rcases modalApplyOne_boxPos_eq (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
      · rw [hk] at hcond
        simp only [List.isEmpty_iff, hself, if_false] at hcond
        obtain ⟨heq, -⟩ := modalTBoxSelf_cases_of_ne_nil hself
        exact hcond (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) (by rw [heq]; simp)
      · rw [hk] at hcond
        obtain ⟨heq, hnotin⟩ := modalTBoxSelf_cases_of_ne_nil hself
        by_cases hkf : (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ kForms
        · exact hcond _ (List.mem_append_left _ hkf)
        · refine hcond (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (List.mem_append_right kForms ?_)
          rw [heq]
          simp only [List.mem_filter, List.mem_singleton, true_and]
          simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
          intro x hx heq
          exact hkf (heq ▸ hx)
  | single hedge =>
    by_contra hnotin
    have hw'_succ : w' ∈ acc.successorsOf w := by
      simp only [Accessibility.successorsOf, List.mem_filterMap]
      simp only [Accessibility.hasEdge, List.any_eq_true] at hedge
      obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hedge
      simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
      exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
    have hmemBP : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        boxPropagation b acc ψ w := by
      simp only [boxPropagation, List.mem_filterMap]
      refine ⟨w', hw'_succ, ?_⟩
      rw [if_neg]
      simp only [List.any_eq_true, not_exists]
      rintro x ⟨hx, heq⟩
      rw [beq_iff_eq] at heq
      exact hnotin (heq ▸ hx)
    have hne : boxPropagation b acc ψ w ≠ [] := fun h => by simp [h] at hmemBP
    have hk : (modalApplyOne (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).fst = .persistent (boxPropagation b acc ψ w) := by
      simp only [modalApplyOne]
      have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
          (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
          = false := by
        rw [tryAllPropRules_pos]
        simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
      rw [if_neg (by simp [htry]), if_neg (by simpa using hne)]
    rw [modalApplyOneT_boxPos_fst', hk] at hcond
    exact hnotin (hcond (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
      (List.mem_append_left _ hmemBP))

/-- **T-analog of `hintikka_diamond_neg`** (`Completeness.lean`, genuinely new content, dual of
`hintikkaT_box_pos`): `F(◇ψ)@w ∈ b` together with `Relation.ReflGen acc.hasEdge w w'` imply
`F(ψ)@w' ∈ b`. -/
lemma hintikkaT_diamond_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneT b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : Relation.ReflGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hcond := hH.2.1 (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  cases hr with
  | refl =>
    rcases eq_or_ne (modalTDiaNegSelf b ψ w) [] with hself | hself
    · exact (modalTDiaNegSelf_eq_nil_iff b ψ w).mp hself
    · rw [modalApplyOneT_diamondNeg_fst'] at hcond
      rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
      · rw [hk] at hcond
        simp only [List.isEmpty_iff, hself, if_false] at hcond
        obtain ⟨heq, -⟩ := modalTDiaNegSelf_cases_of_ne_nil hself
        exact hcond (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) (by rw [heq]; simp)
      · rw [hk] at hcond
        obtain ⟨heq, hnotin⟩ := modalTDiaNegSelf_cases_of_ne_nil hself
        by_cases hkf : (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ kForms
        · exact hcond _ (List.mem_append_left _ hkf)
        · refine hcond (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (List.mem_append_right kForms ?_)
          rw [heq]
          simp only [List.mem_filter, List.mem_singleton, true_and]
          simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
          intro x hx heq
          exact hkf (heq ▸ hx)
  | single hedge =>
    by_contra hnotin
    have hw'_succ : w' ∈ acc.successorsOf w := by
      simp only [Accessibility.successorsOf, List.mem_filterMap]
      simp only [Accessibility.hasEdge, List.any_eq_true] at hedge
      obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hedge
      simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
      exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
    have hmemDN : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        (acc.successorsOf w).filterMap (fun w'' =>
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
          if b.any (· == sf') then none else some sf') := by
      simp only [List.mem_filterMap]
      refine ⟨w', hw'_succ, ?_⟩
      rw [if_neg]
      simp only [List.any_eq_true, not_exists]
      rintro x ⟨hx, heq⟩
      rw [beq_iff_eq] at heq
      exact hnotin (heq ▸ hx)
    have hne : (acc.successorsOf w).filterMap (fun w'' =>
        let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
        if b.any (· == sf') then none else some sf') ≠ [] :=
      fun h => by rw [h] at hmemDN; exact absurd hmemDN (List.not_mem_nil)
    have hk : (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        .persistent ((acc.successorsOf w).filterMap (fun w'' =>
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
          if b.any (· == sf') then none else some sf')) := by
      simp only [modalApplyOne]
      have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
          (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
          = false := by
        rw [tryAllPropRules_neg]
        simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
      rw [if_neg (by simp [htry]), if_neg (by simpa using hne)]
    rw [modalApplyOneT_diamondNeg_fst', hk] at hcond
    exact hnotin (hcond (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
      (List.mem_append_left _ hmemDN))

/-- **T Modal Truth Lemma**: membership in a T Hintikka branch tracks satisfaction in the
extracted reflexive Kripke model `extractModelT b acc`.

Proof by strong induction on `modalComplexity φ`, mirroring `modalTruthLemma` (`Completeness.lean`):
the propositional cases (`atom`/`bot`/`imp`/`and`/`or`) reuse the public, apply-agnostic
consistency kit and K's `modalApplyOne_*` bridge lemmas verbatim, routed through
`modalApplyOneT_eq_of_not_box_diamond`; the box-negative/diamond-positive cases reuse the free
generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` (task 510) directly
(unaffected minting shapes); the box-positive/diamond-negative cases consume the genuinely-new
`hintikkaT_box_pos`/`hintikkaT_diamond_neg` bridges above, with the model's `r w w'` unfolding to
exactly the `Relation.ReflGen` hypothesis those bridges want (`extractModelT_r`). -/
lemma modalTruthLemmaT
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneT b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelT b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelT b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelT b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelT b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelT b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelT b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelT, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelT, extractModelWith, List.any_eq_true] at hsat
        obtain ⟨sf, hsf_mem, hcond⟩ := hsat
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨hsign, hform⟩, hlab⟩ := hcond
        have hsign_eq : sf.sign = .pos := eq_of_beq hsign
        have hform_eq : sf.formula = .atom p := eq_of_beq hform
        have hlab_eq : sf.label = w := eq_of_beq hlab
        have hpos : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
          convert hsf_mem using 1; rcases sf with ⟨s, f, l⟩; simp_all
        exact openBranch_noContradiction b hHopen (.atom p) w hpos hmem
    | bot =>
      refine ⟨fun hmem => absurd hmem (openBranch_noTBot b hHopen w), ?_⟩
      intro _ hsat
      exact hsat
    | imp a c =>
      rcases eq_or_ne c Proposition.bot with rfl | hne
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          intro hna
          have hlt : modalComplexity a < n := by
            rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega
          exact hna ((IH a hlt w).1 hxmem)
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_imp hne] at hcond
          intro hsa
          obtain ⟨br, hbr_mem, hbr⟩ := hcond
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · exact absurd hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2
              (hbr ⟨.neg, a, w⟩ (by simp)))
          · exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1
              (hbr ⟨.pos, c, w⟩ (by simp))
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_imp hne] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          have hymem : (⟨.neg, c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, c, w⟩ (by simp)
          intro hsa
          exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2 hymem
            (hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1 hxmem))
    | and φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_neg] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rintro ⟨hsφ, hsψ⟩
        rcases hbr_mem with rfl | rfl
        · exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, φ', w⟩ (by simp)))
        · exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, ψ', w⟩ (by simp)))
    | or φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_pos] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · exact Or.inl ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, φ', w⟩ (by simp)))
        · exact Or.inr ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, ψ', w⟩ (by simp)))
      · intro hmem
        have hcond := hHrule ⟨.neg, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_neg] at hcond
        intro hs
        cases hs with
        | inl hsφ => exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, φ', w⟩ (by simp)))
        | inr hsψ => exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, ψ', w⟩ (by simp)))
    | box ψ =>
      constructor
      · intro hmem w' hr
        have hpath : Relation.ReflGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelT_r b acc ▸ hr
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1
          (hintikkaT_box_pos b acc hH ψ w w' hmem hpath)
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg_gen modalApplyOneT b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelT_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikka_diamond_pos_gen modalApplyOneT b acc hH ψ w hmem
        exact ⟨w', extractModelT_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath : Relation.ReflGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelT_r b acc ▸ hw'
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2
          (hintikkaT_diamond_neg b acc hH ψ w w' hmem hpath) hsψ

/-- An open T Hintikka branch with `F(φ)@0 ∈ b` yields a reflexive Kripke countermodel to `φ`.
Mirrors `modalOpenBranch_countermodel` (`Completeness.lean`). -/
theorem modalOpenBranchT_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom)
    (hH : modalHintikkaSetGen modalApplyOneT b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModelT b acc) 0 φ :=
  (modalTruthLemmaT b acc hH φ 0).2 hF

/-! ## Task 513 Phase 5: T Soundness Discharges + `modalTableauT_sound` -/

omit [Hashable Atom] in
/-- **Task 513 (Phase 5, S-agree for T)**: `modalApplyOneT` agrees with `modalApplyOne` off
the two propagating shapes -- exactly `modalApplyOneT_eq_of_not_boxPos_diaNeg`
(`FrameRules.lean`) verbatim; zero new proof content. Discharges
`modalStepBranchGen_preserves_satIn`/`modalExpandBranchesGen_closed_unsatIn`'s `hAgree`
hypothesis at `apply := modalApplyOneT`. -/
theorem hAgreeT
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneT sf b acc = modalApplyOne sf b acc :=
  modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc h

/-- **Task 513 (Phase 5, S-boxPos for T)**: frame-relativized semantic soundness of
`modalApplyOneT`'s box-positive output at `FC := reflFC`. Splits `RuleResultSat` over the
`kForms ++ selfNew.filter …` append (`modalApplyOneT_boxPos_fst`, `TDriver.lean`): the
`kForms` half is Phase 1's `modalApplyOne_boxPos_sound` (K, `FC` unused); the `selfNew` half
(at most one extra formula, `T(φ)@lbl` from `T(□φ)@lbl` at the *same* world) is justified
directly by reflexivity (`hFC.refl (f lbl) : m.r (f lbl) (f lbl)`), mirroring
`branchSatisfiableIn_reflFC_boxPos_mem`/`modalTBoxSelf_sound`
(`FrameSoundness.lean`) inline (those lemmas existentially quantify their own witnessing model,
so cannot be applied as black boxes to the caller's specific `(m, f)`; the reflexivity
insight is the same). -/
theorem modalApplyOneT_boxPos_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : reflFC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneT
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc ∧
    RuleResultSat m f (modalApplyOneT
      (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨hsndeqK, hRRSK⟩ := modalApplyOne_boxPos_sound m f φ lbl b acc hacc hb hmem
  have hselfSat : Satisfies m (f lbl) φ := by
    have hbox : Satisfies m (f lbl) (.box φ) := (hb _ hmem).1 rfl
    simp only [Satisfies] at hbox
    exact hbox (f lbl) (hFC.refl (f lbl))
  refine ⟨?_, ?_⟩
  · rw [modalApplyOneT_boxPos_snd]; exact hsndeqK
  · rw [modalApplyOneT_boxPos_fst]
    rcases modalApplyOne_boxPos_eq
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc with
        hk | ⟨kForms, hk⟩
    · rw [hk] at hRRSK ⊢
      split_ifs with hemp
      · trivial
      · intro sf' hmem'
        simp only [modalTBoxSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_pos m f φ lbl hselfSat
    · rw [hk] at hRRSK ⊢
      intro sf' hmem'
      simp only [List.mem_append, List.mem_filter] at hmem'
      rcases hmem' with hmem' | ⟨hmem', -⟩
      · exact hRRSK sf' hmem'
      · simp only [modalTBoxSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_pos m f φ lbl hselfSat

/-- **Task 513 (Phase 5, S-diaNeg for T)**: dual of `modalApplyOneT_boxPos_soundIn` for the
diamond-negative shape. -/
theorem modalApplyOneT_diaNeg_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : reflFC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem :
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneT
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc ∧
    RuleResultSat m f (modalApplyOneT
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨hsndeqK, hRRSK⟩ := modalApplyOne_diaNeg_sound m f φ lbl b acc hacc hb hmem
  have hselfSat : ¬ Satisfies m (f lbl) φ := by
    have hdia : ¬ Satisfies m (f lbl) (.diamond φ) := (hb _ hmem).2 rfl
    rw [Satisfies.diamond_iff] at hdia
    push Not at hdia
    exact hdia (f lbl) (hFC.refl (f lbl))
  refine ⟨?_, ?_⟩
  · rw [modalApplyOneT_diamondNeg_snd]; exact hsndeqK
  · rw [modalApplyOneT_diamondNeg_fst]
    rcases modalApplyOne_diamondNeg_eq
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
        with hk | ⟨kForms, hk⟩
    · rw [hk] at hRRSK ⊢
      split_ifs with hemp
      · trivial
      · intro sf' hmem'
        simp only [modalTDiaNegSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_neg m f φ lbl hselfSat
    · rw [hk] at hRRSK ⊢
      intro sf' hmem'
      simp only [List.mem_append, List.mem_filter] at hmem'
      rcases hmem' with hmem' | ⟨hmem', -⟩
      · exact hRRSK sf' hmem'
      · simp only [modalTDiaNegSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_neg m f φ lbl hselfSat

/-- **Task 513 (Phase 5)**: `modalTableauT` is sound: if the T tableau closes on `F(φ)`, then
`φ` is `tValid`. Contrapositive over `reflFC`, mirroring `modalTableau_sound`
(`Soundness.lean`) and the K zero-regression derivation `modalTableau_sound_frame_gen`
(`FrameSoundness.lean`, Phase 4): feeds `modalExpandBranchesGen_closed_unsatIn reflFC
modalApplyOneT` at the initial configuration `[[F(φ)@0]] [[]] [Accessibility.empty]`. The
initial `branchSatisfiableIn reflFC` witness uses the reflexive falsifying model directly
(available since `tValid = frameValid reflFC` quantifies only reflexive models, so the
`by_contra` model is reflexive by hypothesis). -/
theorem modalTableauT_sound (φ : Proposition Atom) (h : modalTableauT φ = .closed) :
    tValid φ := by
  intro World m hrefl w
  by_contra hnotsat
  have hsat : branchSatisfiableIn reflFC [⟨.neg, φ, 0⟩] Accessibility.empty :=
    ⟨World, m, fun _ => w, hrefl,
      fun w1 w2 hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge]),
      fun sf hmem => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst hmem
        exact ⟨fun h => by simp at h, fun _ => hnotsat⟩⟩
  have hunsat := modalExpandBranchesGen_closed_unsatIn reflFC modalApplyOneT
    modalApplyOneT_spec.freshLocal
    hAgreeT
    (fun m f φ lbl b acc hFC hacc hb hmem =>
      modalApplyOneT_boxPos_soundIn m f φ lbl b acc hFC hacc hb hmem)
    (fun m f φ lbl b acc hFC hacc hb hmem =>
      modalApplyOneT_diaNeg_soundIn m f φ lbl b acc hFC hacc hb hmem)
    (modalFuel φ)
    [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty]
    rfl rfl
    (List.Forall₂.cons (accFreshInv_empty _) List.Forall₂.nil)
    (by
      have h' : modalExpandBranchesT
          [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
          [Accessibility.empty] (modalFuel φ) = .closed := h
      exact h')
  cases hunsat with
  | cons h_unsat _ => exact h_unsat hsat

/-! ## `tValid` Completeness -/

/-- **T-completeness of the modal tableau** (task 503 Phase 5): if the T tableau on `φ0` returns
an open branch, `φ0` is not T-valid. Mirrors `modalTableau_complete`
(`CompletenessLoop.lean`): combines `modalExpandBranchesT_hintikka` (task 510, `TDriver.lean`)
instantiated at the initial configuration (via `modalLoopInvGen_initial` and the fuel bridge
`modalExpMeasure_entry_le_fuel`, both un-privatized for this purpose per their own docstrings),
the generic initial-branch membership persistence lemma
(`modalExpandBranchesGen_openBranch_initial_mem`, likewise), and the T countermodel extraction
above. -/
theorem modalTableauT_complete (φ0 : Proposition Atom)
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {a : Accessibility}
    (h : modalTableauT φ0 = .openBranch b a) :
    ¬ tValid φ0 := by
  have h' : modalExpandBranchesT
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      [Accessibility.empty] (modalFuel φ0) = .openBranch b a := h
  have hmeas := modalExpMeasure_entry_le_fuel φ0
  have hInv : ∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
      (ai : Accessibility),
      ([[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]])[i]? = some bi →
      (([[]] : List (List (SignedFormula (Proposition Atom) WorldIndex))))[i]? = some ei →
      ([Accessibility.empty])[i]? = some ai →
      ∃ rank, ModalLoopInvGen modalApplyOneT φ0 bi ei ai rank := by
    intro i bi ei ai hib hie hia
    match i with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia
      subst hib; subst hie; subst hia
      exact ⟨fun _ => modalDepth φ0, modalLoopInvGen_initial modalApplyOneT φ0⟩
    | n + 1 => simp at hib
  have hH : modalHintikkaSetGen modalApplyOneT b a :=
    modalExpandBranchesT_hintikka φ0 (modalFuel φ0)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl hmeas hInv b a h'
  have hmemInit : (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
    modalExpandBranchesGen_openBranch_initial_mem modalApplyOneT (modalFuel φ0)
      (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl
      (fun b₀ hb₀ => by
        simp only [List.mem_singleton] at hb₀
        subst hb₀
        simp)
      b a h'
  have hnot := modalOpenBranchT_countermodel b a φ0 hH hmemInit
  intro htv
  exact hnot (htv WorldIndex (extractModelT b a) (extractModelT_refl b a) 0)

/-! ## Task 513 Phase 6: `tValid` Decidability -/

/-- **The modal T tableau decides T-validity** (task 513 Phase 6 / task 503 Phase 6 target):
`modalTableauT φ0` closes exactly when `φ0` is T-valid. Combines soundness
(`modalTableauT_sound`, Phase 5) with completeness (`modalTableauT_complete`, above) via the
two-constructor dichotomy of `ModalTableauResult`. Mirrors `modalTableau_decides`
(`CompletenessLoop.lean`) line-for-line. -/
theorem tValid_decides (φ0 : Proposition Atom) :
    modalTableauT φ0 = .closed ↔ tValid φ0 := by
  constructor
  · exact modalTableauT_sound φ0
  · intro htv
    cases htab : modalTableauT φ0 with
    | closed => rfl
    | openBranch b a => exact absurd htv (modalTableauT_complete φ0 htab)

/-- **T-validity is decidable** (task 513 Phase 6 / task 503 Phase 6 target): decide by running
the modal T tableau and consulting `tValid_decides`. No `Fintype Atom` assumption is needed,
since the tableau computation itself is the decision procedure. Mirrors `instDecidableKValid`
(`CompletenessLoop.lean`) line-for-line. -/
instance instDecidableTValid (φ0 : Proposition Atom) : Decidable (tValid φ0) :=
  match h : modalTableauT φ0 with
  | .closed => .isTrue ((tValid_decides φ0).mp h)
  | .openBranch _ _ => .isFalse (modalTableauT_complete φ0 h)

/-! ## B Modal Truth Lemma (task 505 Phase 6)

`modalExpandBranchesB_hintikka` (`BDriver.lean`) produces a `modalHintikkaSetGen modalApplyOneB
bR aR` witness from an open `modalExpandBranchesB` result. This section closes the remaining
gap: the B truth lemma against `extractModelB` and `bValid` completeness.

`modalApplyOneB` agrees with `modalApplyOne` outside the box-positive/diamond-negative shapes
(`modalApplyOneB_eq_of_not_boxPos_diaNeg`, `FrameRules.lean`), so every propositional case and
the box-negative/diamond-positive modal cases reduce to exactly the K argument (the latter two
via the free generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`,
`Completeness.lean`, task 510) -- these only need a *forward* raw edge witness, which survives
into the symmetric closure via `extractModelB_hasEdge_imp_r` (`Or.inl`), so no B-specific content
is needed there. The box-positive and diamond-negative cases are genuinely new:
`hintikkaB_box_pos`/`hintikkaB_diamond_neg` below case-split `Relation.SymmGen`'s two disjuncts --
the *forward* disjunct reduces to the same `boxPropagation`-membership argument
`hintikka_box_pos`/`hintikkaT_box_pos` inline (K's own successor forcing, unaffected by B's
merged output since `modalApplyOneB`'s persistent output is K's own `kForms` merged with the
backward conjunct); the *backward* disjunct is B's own genuinely new content, forcing via
`modalBBoxBack`/`modalBDiaNegBack`'s known-worlds-filtered predecessor propagation
(`FrameRules.lean`), with the known-worlds side condition discharged by `accSourcesKnown`
(`BDriver.lean`) -- the source-side twin of `accTargetsKnown` this development introduces
precisely because B propagates to edge *sources*. -/

omit [Hashable Atom] in
/-- `modalApplyOneB` agrees with `modalApplyOne` on every signed formula whose formula
component is neither `box`- nor `diamond`-shaped (regardless of sign) -- specialization of
`modalApplyOneB_eq_of_not_boxPos_diaNeg` (`FrameRules.lean`) used by the propositional cases of
`modalTruthLemmaB` below. -/
private lemma modalApplyOneB_eq_of_not_box_diamond
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hnb : ∀ φ, sf.formula ≠ .box φ) (hnd : ∀ φ, sf.formula ≠ .diamond φ) :
    modalApplyOneB sf b acc = modalApplyOne sf b acc :=
  modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc
    ⟨fun ⟨_, φ, h⟩ => hnb φ h, fun ⟨_, φ, h⟩ => hnd φ h⟩

/-- **B-analog of `hintikka_box_pos`/`hintikkaT_box_pos`** (genuinely new content per task 510's
research note that this bridge is payload-reading and irreducibly per-system): `T(□ψ)@w ∈ b`
together with the symmetric closure `Relation.SymmGen acc.hasEdge w w'` and `accSourcesKnown b
acc` imply `T(ψ)@w' ∈ b`.

The forward disjunct (`acc.hasEdge w w'`) reduces to the same `boxPropagation`-membership
argument `hintikkaT_box_pos`'s `.single` case inlines, since B's persistent output at this shape
is K's own `kForms` merged with the backward conjunct at possibly-different worlds, so `kForms`
(hence the K successor witness) survives into B's merged forcing list unchanged. The backward
disjunct (`acc.hasEdge w' w`, i.e. `w'` is a recorded *predecessor* of `w`) is B's own content:
`w'` is known (`accSourcesKnown`), so `modalBBoxBack_mem_of` witnesses `T(ψ)@w' ∈ modalBBoxBack
b acc ψ w`, which the saturation forcing property (`hH.2.1`) then places on `b`. -/
lemma hintikkaB_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneB b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : Relation.SymmGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hcond := hH.2.1 (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  rcases hr with hfwd | hbwd
  · by_contra hnotin
    have hw'_succ : w' ∈ acc.successorsOf w := by
      simp only [Accessibility.successorsOf, List.mem_filterMap]
      simp only [Accessibility.hasEdge, List.any_eq_true] at hfwd
      obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hfwd
      simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
      exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
    have hmemBP : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        boxPropagation b acc ψ w := by
      simp only [boxPropagation, List.mem_filterMap]
      refine ⟨w', hw'_succ, ?_⟩
      rw [if_neg]
      simp only [List.any_eq_true, not_exists]
      rintro x ⟨hx, heq⟩
      rw [beq_iff_eq] at heq
      exact hnotin (heq ▸ hx)
    have hne : boxPropagation b acc ψ w ≠ [] := fun h => by simp [h] at hmemBP
    have hk : (modalApplyOne (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).fst = .persistent (boxPropagation b acc ψ w) := by
      simp only [modalApplyOne]
      have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
          (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
          = false := by
        rw [tryAllPropRules_pos]
        simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
      rw [if_neg (by simp [htry]), if_neg (by simpa using hne)]
    rw [modalApplyOneB_boxPos_fst, hk] at hcond
    exact hnotin (hcond (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
      (List.mem_append_left _ hmemBP))
  · by_contra hnotin
    have hpred : w' ∈ modalBPredecessorsOf acc w := modalBPredecessorsOf_mem_of_hasEdge hbwd
    have hknown : w' ∈ modalKnownWorlds b := hSrc w' w hbwd
    have hmemBack : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        modalBBoxBack b acc ψ w := modalBBoxBack_mem_of hpred hknown hnotin
    rw [modalApplyOneB_boxPos_fst] at hcond
    rcases modalApplyOne_boxPos_eq (⟨.pos, .box ψ, w⟩) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
    · rw [hk] at hcond
      have hne : ¬ (modalBBoxBack b acc ψ w).isEmpty := by
        simp only [List.isEmpty_iff]
        intro hcontra
        rw [hcontra] at hmemBack
        exact List.not_mem_nil hmemBack
      simp only [hne] at hcond
      exact hnotin (hcond _ hmemBack)
    · rw [hk] at hcond
      by_cases hkf : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ kForms
      · exact hnotin (hcond _ (List.mem_append_left _ hkf))
      · apply hnotin
        apply hcond
        apply List.mem_append_right
        rw [List.mem_filter]
        refine ⟨hmemBack, ?_⟩
        simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
        intro x hx heqx
        exact hkf (heqx ▸ hx)

/-- **B-analog of `hintikka_diamond_neg`/`hintikkaT_diamond_neg`**, dual of `hintikkaB_box_pos`:
`F(◇ψ)@w ∈ b` together with `Relation.SymmGen acc.hasEdge w w'` and `accSourcesKnown b acc`
imply `F(ψ)@w' ∈ b`. -/
lemma hintikkaB_diamond_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneB b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : Relation.SymmGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hcond := hH.2.1 (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  rcases hr with hfwd | hbwd
  · by_contra hnotin
    have hw'_succ : w' ∈ acc.successorsOf w := by
      simp only [Accessibility.successorsOf, List.mem_filterMap]
      simp only [Accessibility.hasEdge, List.any_eq_true] at hfwd
      obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hfwd
      simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
      exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
    have hmemDN : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        (acc.successorsOf w).filterMap (fun w'' =>
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
          if b.any (· == sf') then none else some sf') := by
      simp only [List.mem_filterMap]
      refine ⟨w', hw'_succ, ?_⟩
      rw [if_neg]
      simp only [List.any_eq_true, not_exists]
      rintro x ⟨hx, heq⟩
      rw [beq_iff_eq] at heq
      exact hnotin (heq ▸ hx)
    have hne : (acc.successorsOf w).filterMap (fun w'' =>
        let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
        if b.any (· == sf') then none else some sf') ≠ [] :=
      fun h => by rw [h] at hmemDN; exact absurd hmemDN (List.not_mem_nil)
    have hk : (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        .persistent ((acc.successorsOf w).filterMap (fun w'' =>
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
          if b.any (· == sf') then none else some sf')) := by
      simp only [modalApplyOne]
      have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
          (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
          = false := by
        rw [tryAllPropRules_neg]
        simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
      rw [if_neg (by simp [htry]), if_neg (by simpa using hne)]
    rw [modalApplyOneB_diamondNeg_fst, hk] at hcond
    exact hnotin (hcond (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
      (List.mem_append_left _ hmemDN))
  · by_contra hnotin
    have hpred : w' ∈ modalBPredecessorsOf acc w := modalBPredecessorsOf_mem_of_hasEdge hbwd
    have hknown : w' ∈ modalKnownWorlds b := hSrc w' w hbwd
    have hmemBack : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        modalBDiaNegBack b acc ψ w := modalBDiaNegBack_mem_of hpred hknown hnotin
    rw [modalApplyOneB_diamondNeg_fst] at hcond
    rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond ψ, w⟩) rfl ψ rfl b acc with
        hk | ⟨kForms, hk⟩
    · rw [hk] at hcond
      have hne : ¬ (modalBDiaNegBack b acc ψ w).isEmpty := by
        simp only [List.isEmpty_iff]
        intro hcontra
        rw [hcontra] at hmemBack
        exact List.not_mem_nil hmemBack
      simp only [hne] at hcond
      exact hnotin (hcond _ hmemBack)
    · rw [hk] at hcond
      by_cases hkf : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ kForms
      · exact hnotin (hcond _ (List.mem_append_left _ hkf))
      · apply hnotin
        apply hcond
        apply List.mem_append_right
        rw [List.mem_filter]
        refine ⟨hmemBack, ?_⟩
        simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
        intro x hx heqx
        exact hkf (heqx ▸ hx)

/-- **B Modal Truth Lemma**: membership in a B Hintikka branch tracks satisfaction in the
extracted symmetric Kripke model `extractModelB b acc`, given `accSourcesKnown b acc`.

Proof by strong induction on `modalComplexity φ`, mirroring `modalTruthLemmaT`: the
propositional cases reuse the public, apply-agnostic consistency kit and K's `modalApplyOne_*`
bridge lemmas verbatim, routed through `modalApplyOneB_eq_of_not_box_diamond`; the
box-negative/diamond-positive cases reuse the free generic projection bridges
`hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` directly; the box-positive/diamond-negative
cases consume the genuinely-new `hintikkaB_box_pos`/`hintikkaB_diamond_neg` bridges above, with
the model's `r w w'` unfolding to exactly the `Relation.SymmGen` hypothesis those bridges
want (`extractModelB_r`). -/
lemma modalTruthLemmaB
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneB b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelB b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelB b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelB b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelB b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelB b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelB b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelB, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelB, extractModelWith, List.any_eq_true] at hsat
        obtain ⟨sf, hsf_mem, hcond⟩ := hsat
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨hsign, hform⟩, hlab⟩ := hcond
        have hsign_eq : sf.sign = .pos := eq_of_beq hsign
        have hform_eq : sf.formula = .atom p := eq_of_beq hform
        have hlab_eq : sf.label = w := eq_of_beq hlab
        have hpos : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
          convert hsf_mem using 1; rcases sf with ⟨s, f, l⟩; simp_all
        exact openBranch_noContradiction b hHopen (.atom p) w hpos hmem
    | bot =>
      refine ⟨fun hmem => absurd hmem (openBranch_noTBot b hHopen w), ?_⟩
      intro _ hsat
      exact hsat
    | imp a c =>
      rcases eq_or_ne c Proposition.bot with rfl | hne
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          intro hna
          have hlt : modalComplexity a < n := by
            rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega
          exact hna ((IH a hlt w).1 hxmem)
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_imp hne] at hcond
          intro hsa
          obtain ⟨br, hbr_mem, hbr⟩ := hcond
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · exact absurd hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2
              (hbr ⟨.neg, a, w⟩ (by simp)))
          · exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1
              (hbr ⟨.pos, c, w⟩ (by simp))
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_imp hne] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          have hymem : (⟨.neg, c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, c, w⟩ (by simp)
          intro hsa
          exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2 hymem
            (hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1 hxmem))
    | and φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_neg] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rintro ⟨hsφ, hsψ⟩
        rcases hbr_mem with rfl | rfl
        · exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, φ', w⟩ (by simp)))
        · exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, ψ', w⟩ (by simp)))
    | or φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_pos] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · exact Or.inl ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, φ', w⟩ (by simp)))
        · exact Or.inr ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, ψ', w⟩ (by simp)))
      · intro hmem
        have hcond := hHrule ⟨.neg, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_neg] at hcond
        intro hs
        cases hs with
        | inl hsφ => exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, φ', w⟩ (by simp)))
        | inr hsψ => exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, ψ', w⟩ (by simp)))
    | box ψ =>
      constructor
      · intro hmem w' hr
        have hpath : Relation.SymmGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelB_r b acc ▸ hr
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1
          (hintikkaB_box_pos b acc hSrc hH ψ w w' hmem hpath)
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg_gen modalApplyOneB b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelB_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikka_diamond_pos_gen modalApplyOneB b acc hH ψ w hmem
        exact ⟨w', extractModelB_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath : Relation.SymmGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelB_r b acc ▸ hw'
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2
          (hintikkaB_diamond_neg b acc hSrc hH ψ w w' hmem hpath) hsψ

end Cslib.Logic.Modal.Tableau

end
