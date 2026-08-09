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
public import Cslib.Logics.Modal.Tableau.TBDriver
public import Cslib.Logics.Modal.Tableau.Support.Accessibility
public import Cslib.Logics.Modal.Tableau.Support.KnownWorlds
public import Cslib.Foundations.Relation.Euclidean
public import Cslib.Foundations.Relation.Confluence

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
          (hintikkaS4_box_pos_reflTransGen φ₀ b acc (modalHintikkaSetS4_saturated φ₀ b acc hH)
            ψ w w' hmem hpath)
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
          (hintikkaS4_dia_neg_reflTransGen φ₀ b acc (modalHintikkaSetS4_saturated φ₀ b acc hH)
            ψ w w' hmem hpath) hsψ

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

/-! ## B (Symmetric Frame) Extraction

Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*symmetric closure* `Relation.SymmGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.SymmGen`). The frame instance
`Std.Symm` comes free off `Relation.SymmGen`'s own unnamed `instance : Std.Symm (SymmGen r)`
(`Mathlib.Logic.Relation`); no new frame predicate is defined. Unlike `Relation.ReflGen`/
`Relation.ReflTransGen` (inductive types with named constructors `.refl`/`.single`/`.tail`),
`Relation.SymmGen r a b` is literally `r a b ∨ r b a` (a `def`, not an inductive), so case
analysis on a `SymmGen` hypothesis is a plain `Or` split -- the forward direction reduces to
K's own successor argument, the backward direction to B's own predecessor argument
(`hintikkaB_box_pos`/`hintikkaB_diamond_neg`, below). -/

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

/-! ## TB (Reflexive-Symmetric Frame) Extraction

Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*reflexive closure of the symmetric closure* `Relation.ReflGen (Relation.SymmGen ·)` of
`acc.hasEdge` as the model's relation (Strategy B, closure-at-extraction, instantiated with
`Cl := fun r => Relation.ReflGen (Relation.SymmGen r)`). Both the `Std.Refl` and `Std.Symm`
frame instances come free off this composite closure: reflexivity off `Relation.ReflGen` itself
(`extractModelTB_refl`, mirroring `extractModelT_refl`), symmetry off
`Relation.ReflGen.compRel_symm` (`Cslib/Foundations/Relation/Confluence.lean`), which states
exactly `ReflGen (SymmGen r) a b → ReflGen (SymmGen r) b a` (`extractModelTB_symm`, below). -/

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*reflexive closure of the symmetric closure* of `acc.hasEdge` as the model's relation. -/
def extractModelTB
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (fun r => Relation.ReflGen (Relation.SymmGen r)) b acc

omit [Hashable Atom] in
/-- `extractModelTB`'s relation is exactly the reflexive closure of the symmetric closure of
`acc.hasEdge`. -/
lemma extractModelTB_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelTB b acc).r =
      Relation.ReflGen (Relation.SymmGen (fun w w' => acc.hasEdge w w' = true)) := rfl

omit [Hashable Atom] in
/-- The reflexive frame condition holds of `extractModelTB b acc` "for free": `Relation.ReflGen`
is always reflexive (`Relation.reflexive_reflGen`), regardless of the underlying raw edge
relation `acc.hasEdge`. Discharges half of the `tbFC` witness (`FrameSoundness.lean`) for the
TB countermodel. -/
lemma extractModelTB_refl (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Std.Refl (extractModelTB b acc).r := by
  rw [extractModelTB_r]
  infer_instance

omit [Hashable Atom] in
/-- The symmetric frame condition holds of `extractModelTB b acc` "for free", via
`Relation.ReflGen.compRel_symm`, which states exactly `ReflGen (SymmGen r) a b → ReflGen
(SymmGen r) b a`. Discharges the other half of the `tbFC` witness (`FrameSoundness.lean`) for
the TB countermodel. -/
lemma extractModelTB_symm (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Std.Symm (extractModelTB b acc).r := by
  rw [extractModelTB_r]
  exact ⟨fun _ _ h => Relation.ReflGen.compRel_symm h⟩

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelTB`'s
(reflexive-of-symmetric-closure) relation via `Relation.ReflGen.single (Or.inl h)`: the forward
direction, needed to reuse the K bridge lemmas the same way `extractModelT_hasEdge_imp_r` and
`extractModelB_hasEdge_imp_r` do. -/
lemma extractModelTB_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelTB b acc).r w w' := by
  rw [extractModelTB_r]
  exact Relation.ReflGen.single (Or.inl h)

omit [Hashable Atom] in
/-- The *backward* direction survives into `extractModelTB`'s relation too, via
`Relation.ReflGen.single (Or.inr h)`: a raw edge `v → w` (`acc.hasEdge v w`) gives
`(extractModelTB b acc).r w v` (the reversed pair) directly -- the reflexive-of-symmetric-
closure analogue of `extractModelB_hasEdge_symm_imp_r` for the predecessor direction TB's B arm
reads. -/
lemma extractModelTB_hasEdge_symm_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {v w : WorldIndex} (h : acc.hasEdge v w = true) :
    (extractModelTB b acc).r w v := by
  rw [extractModelTB_r]
  exact Relation.ReflGen.single (Or.inr h)

/-! ## S5 (Equivalence Frame) Extraction

Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*equivalence closure* `Relation.EqvGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.EqvGen`). This extraction is
**independent of the tableau rule** -- a pure closure-model construction over any branch/
accessibility pair -- and is delivered here regardless of the bypassed S5 rule-discharge
obstruction (superseded by the witness-reuse rule `modalApplyOneS5w`, `S5Simplification.lean`;
see that file's rule-discharge-obstruction discussion).

Note: `Relation.EqvGen.instIsEquiv` does not exist in Mathlib (confirmed: `infer_instance` fails
for `IsEquiv _ (Relation.EqvGen r)`; only `Relation.EqvGen.is_equivalence : Equivalence (EqvGen
r)` and the individual constructors `.refl`/`.symm`/`.trans` are provided). `instIsEquivEqvGen`
below builds the instance directly from those constructors -- three one-line proofs, no new
mathematical content, assembled by hand from Mathlib's primitives rather than found
pre-packaged. -/

/-- `IsEquiv` for `Relation.EqvGen`: built directly from the closure's own constructors
(`.refl`/`.symm`/`.trans`), since Mathlib ships no unconditional instance for this combination
(unlike `Relation.SymmGen`'s `Std.Symm` instance, reused verbatim by `extractModelB_symm` above).
Generic over any type/relation, not modal-tableau-specific; kept in this namespace since it is
needed only here. -/
instance instIsEquivEqvGen {α : Type*} (r : α → α → Prop) : IsEquiv α (Relation.EqvGen r) where
  refl := Relation.EqvGen.refl
  trans := fun _ _ _ h1 h2 => Relation.EqvGen.trans _ _ _ h1 h2
  symm := fun _ _ h => Relation.EqvGen.symm _ _ h

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*equivalence closure* `Relation.EqvGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.EqvGen`). -/
def extractModelS5
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (Relation.EqvGen) b acc

omit [Hashable Atom] in
/-- `extractModelS5`'s relation is exactly the equivalence closure of `acc.hasEdge`. -/
lemma extractModelS5_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelS5 b acc).r = Relation.EqvGen (fun w w' => acc.hasEdge w w' = true) := rfl

omit [Hashable Atom] in
/-- The equivalence frame condition holds of `extractModelS5 b acc` "for free": `Relation.EqvGen`
is always an equivalence relation (`instIsEquivEqvGen` above), regardless of the underlying raw
edge relation `acc.hasEdge`. Discharges the `s5FC` witness (`FrameSoundness.lean`) for the S5
countermodel; its `Std.Refl`/`Std.Symm`/`IsTrans` projections are obtained downstream via
`IsEquiv`'s own field projections. -/
lemma extractModelS5_equiv (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    IsEquiv WorldIndex (extractModelS5 b acc).r := by
  rw [extractModelS5_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelS5`'s
(equivalence-closure) relation via `Relation.EqvGen.rel`. Needed to reuse the K bridge lemmas
(`hintikka_box_neg`, `hintikka_diamond_pos`, etc.), which are stated in terms of `acc.hasEdge`,
when relating them to `extractModelS5`'s closed relation. -/
lemma extractModelS5_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelS5 b acc).r w w' := by
  rw [extractModelS5_r]
  exact Relation.EqvGen.rel _ _ h

omit [Hashable Atom] in
/-- Every known world of `b` is `extractModelS5`-related to every other known world of `b`,
*provided* both are connected to a common recorded-edge chain -- in particular, `Relation.EqvGen`
being symmetric+transitive means any two worlds reachable from a shared ancestor via raw edges
are related, regardless of direction. Stated here as the reflexivity instance specialized to a
single world (the trivial case of the cluster property: every world is related to itself),
since the general "any two known worlds are related" fact requires connectivity of the
underlying tree (established per-branch, not by the extractor alone). -/
lemma extractModelS5_refl (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) :
    (extractModelS5 b acc).r w w :=
  Relation.EqvGen.refl w

omit [Hashable Atom] in
/-- `extractModelS5`'s relation satisfies `Relation.RightEuclidean`, obtained directly from
`IsEquiv`'s `symm` + `trans` projections: `r a b → r a c → r b c` follows by symmetry (`r a b`
gives `r b a`) then transitivity (`r b a` with `r a c` gives `r b c`). This is a free 5/KB5
(Euclidean) exposure -- delivered here since it depends only on `extractModelS5_equiv` above,
independent of the bypassed S5 rule-discharge obstruction (superseded by the witness-reuse rule
`modalApplyOneS5w`, `S5Simplification.lean`). There is **no** `RightEuclidean.symm` lemma
(confirmed against `Defs.lean:49`); an alternative route via
`Relation.symm_rightEuclidean_iff_trans`
(`Cslib/Foundations/Relation/Euclidean.lean:236`) requires a `[Std.Symm r]` instance that is not
available generically for `Relation.EqvGen`, so this lemma instead builds the `RightEuclidean`
witness directly from `IsEquiv`'s own `symm`/`trans` fields (both routes are mathematically
equivalent; the direct route avoids an extra typeclass search). -/
lemma extractModelS5_rightEuclidean (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Relation.RightEuclidean (extractModelS5 b acc).r := by
  have hequiv := extractModelS5_equiv b acc
  exact ⟨fun hab hac => hequiv.trans _ _ _ (hequiv.symm _ _ hab) hac⟩

/-! ## 5 / KB5 (Euclidean) Coverage via the S5 Route: Status

`extractModelS5_rightEuclidean` above delivers a free Euclidean exposure:
`Relation.RightEuclidean (extractModelS5 b acc).r` holds unconditionally, since every
equivalence relation is right-Euclidean. This is genuinely independent of the bypassed S5
rule-discharge obstruction (it only needs `extractModelS5_equiv` above).

**What is actually true: 5/KB5 is not deliverable *via the S5 tableau route*, at all, regardless
of whether `modalTableauS5_complete`/`modalTableauS5_sound` exist.** This is a **frame-class
inclusion obstruction**, proven (not argued) in `FrameSoundness.lean`
(sorry-free, **zero axioms**): `s5FC = Std.Refl r ∧ Relation.RightEuclidean r`
(`FrameSoundness.lean:1273`), but `fiveFC = Relation.RightEuclidean r` **alone** (:1282,
reflexivity absent) and `kb5FC = Std.Symm r ∧ Relation.RightEuclidean r` (:1291, reflexivity
absent) are **strictly larger** frame classes. `□p → p` on the one-world **empty** frame
separates them: `RightEuclidean` and `Std.Symm` are both vacuous with no edges, so `□p` holds
vacuously while `p` is false, and reflexivity -- exactly what `fiveFC`/`kb5FC` drop -- is exactly
what this validity depends on. Hence `fiveValid ⊊ s5Valid` and `kb5Valid ⊊ s5Valid`
(`fiveValid_ssubset_s5Valid`, `kb5Valid_ssubset_s5Valid`, with supporting `boxImp_s5Valid`,
`boxImp_not_fiveValid`, `boxImp_not_kb5Valid`, `fiveValid_imp_s5Valid`, `kb5Valid_imp_s5Valid`,
`s5FC_imp_fiveFC`, `s5FC_imp_kb5FC`, all in `FrameSoundness.lean`): **no sound+complete decision
procedure for `s5Valid` composes into one for `fiveValid`/`kb5Valid`**, no matter how the S5
tableau itself is built or proven.

**This is a route obstruction, NOT an impossibility of the deliverable.** 5 (Euclidean) validity
and completeness ARE delivered -- by a dedicated Euclidean route built on top of the S5 cluster
machinery (`modalTableauFive`, consuming a new `Relation.EuclGen` least-closure operator in
`Cslib/Foundations/Relation/Euclidean.lean`): rooted Euclidean frames are exactly "root + universal
cluster" (`Relation.RightEuclidean.equiv_cod`, `Euclidean.lean:124`), so the cluster half is the S5
machinery this file's neighbours already build, and only the closure operator and a root-aware
rule are genuinely new. KB5's **rule and soundness** are delivered too (`modalApplyOneKb5`,
`modalTableauKb5_sound`, by a "factor, not clone" frame-class-monotonicity argument: the
unmodified Five rule is already sound for the strictly stronger `kb5FC` class). **KB5
completeness is now fully delivered too**, via a corrected-gate full-cluster rule
(`modalApplyOneKb5''`, `modalTableauKb5''_complete`, `kb5Valid_decides`, `instDecidableKb5Valid`
below): `modalApplyOneFive`'s root-restricted propagation, essential to Five's own soundness, is
provably insufficient once the frame is required to be symmetric too (see `modalTruthLemmaKb5`'s
docstring below, which retains the counterexample documenting exactly why the naive
root-restricted gate was unrepairable for the retired frozen rule) -- the fix drops the
trigger-identity conjunct from the self-target gate (`modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv`),
firing the cluster-dump arm whenever the known cluster has any non-root member, regardless of which
world triggered it. This confirms K5/KB5 completeness via a rooted Euclidean tableau is exactly as
standard here as in the literature (Blackburn–de Rijke–Venema §4.8-4.9), once the propagation gate
matches the closure relation's actual totality on the cluster.

**Genuine pure-K5 / pure-5** (Euclidean *without* full equivalence -- i.e. a frame satisfying only
`RightEuclidean`, and for KB5 additionally `Std.Symm`, but not necessarily `Std.Refl`/`IsTrans` as
freestanding properties) is no longer missing library infrastructure. The bespoke `Relation.EuclGen`
closure operator (`Cslib/Foundations/Relation/Euclidean.lean`) -- the least right-Euclidean relation
containing a given relation, built exactly because Mathlib ships no such "Euclidean closure"
analogous to `Relation.EqvGen`/`Relation.SymmGen` -- lands the countermodel extractor
`extractModelFive` (5, via `EuclGen acc.hasEdge`, complete) and `extractModelKb5` (KB5, via a
symmetric variant of the same closure, now also complete -- `modalTruthLemmaKb5`,
`modalTableauKb5''_complete` below) together with `modalTruthLemmaFive` and the completeness
theorem `modalTableauFive_complete`. `extractModelS5` itself remains untouched and is not the route
pure-K5/5 uses. -/

/-! ## T Modal Truth Lemma

`modalExpandBranchesT_hintikka` (`TDriver.lean`) produces a
`modalHintikkaSetGen modalApplyOneT bR aR` witness from an open `modalExpandBranchesT` result.
This section closes the remaining gap: the T truth lemma against `extractModelT` and `tValid`
completeness.

`modalApplyOneT` agrees with `modalApplyOne` outside the box-positive/diamond-negative shapes
(`modalApplyOneT_eq_of_not_boxPos_diaNeg`, `FrameRules.lean`), so every propositional case and
the box-negative/diamond-positive modal cases reduce to exactly the K argument (the latter two
via the free generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`,
`Completeness.lean`). The box-positive and diamond-negative cases are genuinely new:
`hintikkaT_box_pos`/`hintikkaT_diamond_neg` below combine the K argument (raw recorded edge,
`Relation.ReflGen.single`) with the T self-propagation conjunct (reflexive self-edge,
`Relation.ReflGen.refl`)
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
inherited from K, since this bridge is payload-reading and irreducibly K-specific):
`T(□ψ)@w ∈ b` together with the reflexive closure
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
generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` directly
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

/-! ## T Soundness Discharges + `modalTableauT_sound` -/

omit [Hashable Atom] in
/-- **S-agree for T**: `modalApplyOneT` agrees with `modalApplyOne` off
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

omit [Hashable Atom] in
/-- **S-boxPos for T**: frame-relativized semantic soundness of
`modalApplyOneT`'s box-positive output at `FC := reflFC`. Splits `RuleResultSat` over the
`kForms ++ selfNew.filter …` append (`modalApplyOneT_boxPos_fst`, `TDriver.lean`): the
`kForms` half is `modalApplyOne_boxPos_sound` (K, `FC` unused); the `selfNew` half
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

omit [Hashable Atom] in
/-- **S-diaNeg for T**: dual of `modalApplyOneT_boxPos_soundIn` for the
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

/-- `modalTableauT` is sound: if the T tableau closes on `F(φ)`, then
`φ` is `tValid`. Contrapositive over `reflFC`, mirroring `modalTableau_sound`
(`Soundness.lean`) and the K zero-regression derivation `modalTableau_sound_frame_gen`
(`FrameSoundness.lean`): feeds `modalExpandBranchesGen_closed_unsatIn reflFC
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

/-- **T-completeness of the modal tableau**: if the T tableau on `φ0` returns
an open branch, `φ0` is not T-valid. Mirrors `modalTableau_complete`
(`CompletenessLoop.lean`): combines `modalExpandBranchesT_hintikka` (`TDriver.lean`)
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

/-! ## `tValid` Decidability -/

/-- **The modal T tableau decides T-validity**:
`modalTableauT φ0` closes exactly when `φ0` is T-valid. Combines soundness
(`modalTableauT_sound`, above) with completeness (`modalTableauT_complete`, above) via the
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

/-- **T-validity is decidable**: decide by running
the modal T tableau and consulting `tValid_decides`. No `Fintype Atom` assumption is needed,
since the tableau computation itself is the decision procedure. Mirrors `instDecidableKValid`
(`CompletenessLoop.lean`) line-for-line. -/
instance instDecidableTValid (φ0 : Proposition Atom) : Decidable (tValid φ0) :=
  match h : modalTableauT φ0 with
  | .closed => .isTrue ((tValid_decides φ0).mp h)
  | .openBranch _ _ => .isFalse (modalTableauT_complete φ0 h)

/-! ## B Modal Truth Lemma

`modalExpandBranchesB_hintikka` (`BDriver.lean`) produces a `modalHintikkaSetGen modalApplyOneB
bR aR` witness from an open `modalExpandBranchesB` result. This section closes the remaining
gap: the B truth lemma against `extractModelB` and `bValid` completeness.

`modalApplyOneB` agrees with `modalApplyOne` outside the box-positive/diamond-negative shapes
(`modalApplyOneB_eq_of_not_boxPos_diaNeg`, `FrameRules.lean`), so every propositional case and
the box-negative/diamond-positive modal cases reduce to exactly the K argument (the latter two
via the free generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`,
`Completeness.lean`) -- these only need a *forward* raw edge witness, which survives
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

/-- **B-analog of `hintikka_box_pos`/`hintikkaT_box_pos`** (genuinely new content, since this
bridge is payload-reading and irreducibly per-system): `T(□ψ)@w ∈ b`
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

/-- An open B Hintikka branch with `F(φ)@0 ∈ b` (and `accSourcesKnown b acc`) yields a
symmetric Kripke countermodel to `φ`. Mirrors `modalOpenBranchT_countermodel`. -/
theorem modalOpenBranchB_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneB b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModelB b acc) 0 φ :=
  (modalTruthLemmaB b acc hSrc hH φ 0).2 hF

/-! ## TB Modal Truth Lemma

`modalExpandBranchesTB_hintikka` (`TBDriver.lean`) produces a `modalHintikkaSetGen
modalApplyOneTB bR aR` witness from an open `modalExpandBranchesTB` result. This section closes
the remaining gap: the TB truth lemma against `extractModelTB` and `tbValid` completeness.

`modalApplyOneTB` agrees with `modalApplyOneB` outside the box-positive/diamond-negative shapes
(`modalApplyOneTB_eq_of_not_boxPos_diaNeg`, `FrameRules.lean`), so every propositional case and
the box-negative/diamond-positive modal cases reduce to exactly the K argument via the free
generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`, exactly as for T
and B. The box-positive and diamond-negative cases are genuinely new: `hintikkaTB_box_pos`/
`hintikkaTB_diamond_neg` below case-split the model relation's three-way structure
`Relation.ReflGen (Relation.SymmGen (acc.hasEdge · ·))` -- `.refl` (same world, T's self conjunct,
`modalTBoxSelf`/`modalTDiaNegSelf`), `.single (.inl h)` (forward raw edge, K's own
`boxPropagation` witness), and `.single (.inr h)` (backward raw edge, B's own predecessor
conjunct, `modalBBoxBack`/`modalBDiaNegBack`, with the known-worlds side condition discharged by
`accSourcesKnown`). Each subcase places its witness through `modalApplyOneTB_boxPos_fst`/
`_diamondNeg_fst` (`TBDriver.lean`) -- the T self-list layer wrapping `modalApplyOneB`'s own
persistent output -- so a witness already known to survive into `modalApplyOneB`'s merged list
(the same K/B argument `hintikkaB_box_pos`/`hintikkaB_diamond_neg` make) survives one further
`List.mem_append_left` into TB's outer merged list, and the T self-conjunct survives via the same
argument `hintikkaT_box_pos`/`hintikkaT_diamond_neg` make against T's own `modalTBoxSelf`/
`modalTDiaNegSelf` dichotomy, transported through `modalApplyOneB_spec.boxPosNotExpanding`/
`diaNegNotExpanding` in place of the raw K dichotomy `modalApplyOne_boxPos_eq`/
`modalApplyOne_diamondNeg_eq`. -/

omit [Hashable Atom] in
/-- `modalApplyOneTB` agrees with `modalApplyOne` on every signed formula whose formula
component is neither `box`- nor `diamond`-shaped (regardless of sign) -- specialization of
`modalApplyOneTB_eq_of_not_boxPos_diaNeg` (`FrameRules.lean`) used by the propositional cases of
`modalTruthLemmaTB` below. Note this reduces all the way to `modalApplyOneB` (not `modalApplyOne`
directly); the propositional cases separately route through `modalApplyOneB_eq_of_not_box_diamond`
to reach K. -/
private lemma modalApplyOneTB_eq_of_not_box_diamond
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hnb : ∀ φ, sf.formula ≠ .box φ) (hnd : ∀ φ, sf.formula ≠ .diamond φ) :
    modalApplyOneTB sf b acc = modalApplyOneB sf b acc :=
  modalApplyOneTB_eq_of_not_boxPos_diaNeg sf b acc
    ⟨fun ⟨_, φ, h⟩ => hnb φ h, fun ⟨_, φ, h⟩ => hnd φ h⟩

/-- **TB-analog of `hintikkaT_box_pos`/`hintikkaB_box_pos`** (genuinely new content, since this
bridge is payload-reading and irreducibly per-system): `T(□ψ)@w ∈ b` together with the
reflexive-of-symmetric closure `Relation.ReflGen (Relation.SymmGen acc.hasEdge) w w'` and
`accSourcesKnown b acc` imply `T(ψ)@w' ∈ b`.

Three-way case split on the closure structure: `.refl` (`w = w'`) is T's self-propagation
conjunct, transported through `modalApplyOneB_spec.boxPosNotExpanding` in place of the raw K
dichotomy; `.single (.inl hfwd)` (forward raw edge) is K's own `boxPropagation` witness, placed
through *both* merge layers (`modalApplyOneB`'s backward layer, then `modalApplyOneTB`'s self
layer); `.single (.inr hbwd)` (backward raw edge) is B's own `modalBBoxBack` predecessor witness,
placed through the outer self layer only (it is already inside `modalApplyOneB`'s own persistent
output by construction). -/
lemma hintikkaTB_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneTB b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : Relation.ReflGen (Relation.SymmGen (fun a c => acc.hasEdge a c = true)) w w') :
    (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hcond := hH.2.1 (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  cases hr with
  | refl =>
    rcases eq_or_ne (modalTBoxSelf b ψ w) [] with hself | hself
    · exact (modalTBoxSelf_eq_nil_iff b ψ w).mp hself
    · rw [modalApplyOneTB_boxPos_fst] at hcond
      rcases modalApplyOneB_spec.boxPosNotExpanding (⟨.pos, .box ψ, w⟩) rfl ψ rfl b acc with
          hk | ⟨bForms, hk⟩
      · rw [hk] at hcond
        simp only [List.isEmpty_iff, hself, if_false] at hcond
        obtain ⟨heq, -⟩ := modalTBoxSelf_cases_of_ne_nil hself
        exact hcond (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) (by rw [heq]; simp)
      · rw [hk] at hcond
        obtain ⟨heq, hnotinb⟩ := modalTBoxSelf_cases_of_ne_nil hself
        by_cases hbf : (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ bForms
        · exact hcond _ (List.mem_append_left _ hbf)
        · refine hcond (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (List.mem_append_right bForms ?_)
          rw [heq]
          simp only [List.mem_filter, List.mem_singleton, true_and]
          simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
          intro x hx heq2
          exact hbf (heq2 ▸ hx)
  | single hsymm =>
    rcases hsymm with hfwd | hbwd
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
      have hkeq : (modalApplyOne (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          b acc).fst = .persistent (boxPropagation b acc ψ w) := by
        simp only [modalApplyOne]
        have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
            (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
            = false := by
          rw [tryAllPropRules_pos]
          simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
        rw [if_neg (by simp [htry]), if_neg (by simpa using hne)]
      have hBeq : (modalApplyOneB (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          b acc).fst = .persistent (boxPropagation b acc ψ w ++
            (modalBBoxBack b acc ψ w).filter
              (fun x => !((boxPropagation b acc ψ w).any (· == x)))) := by
        rw [modalApplyOneB_boxPos_fst, hkeq]
      rw [modalApplyOneTB_boxPos_fst, hBeq] at hcond
      exact hnotin (hcond (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
        (List.mem_append_left _ (List.mem_append_left _ hmemBP)))
    · by_contra hnotin
      have hpred : w' ∈ modalBPredecessorsOf acc w := modalBPredecessorsOf_mem_of_hasEdge hbwd
      have hknown : w' ∈ modalKnownWorlds b := hSrc w' w hbwd
      have hmemBack : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          modalBBoxBack b acc ψ w := modalBBoxBack_mem_of hpred hknown hnotin
      rcases modalApplyOne_boxPos_eq (⟨.pos, .box ψ, w⟩) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
      · have hBeq : (modalApplyOneB (⟨.pos, .box ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst
            = .persistent (modalBBoxBack b acc ψ w) := by
          have hne : ¬ (modalBBoxBack b acc ψ w).isEmpty := by
            simp only [List.isEmpty_iff]
            intro hcontra
            rw [hcontra] at hmemBack
            exact List.not_mem_nil hmemBack
          simp only [modalApplyOneB_boxPos_fst, hk]
          rw [if_neg hne]
        rw [modalApplyOneTB_boxPos_fst, hBeq] at hcond
        exact hnotin (hcond (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
          (List.mem_append_left _ hmemBack))
      · have hBeq : (modalApplyOneB (⟨.pos, .box ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst
            = .persistent (kForms ++
                (modalBBoxBack b acc ψ w).filter (fun x => !(kForms.any (· == x)))) := by
          rw [modalApplyOneB_boxPos_fst, hk]
        rw [modalApplyOneTB_boxPos_fst, hBeq] at hcond
        apply hnotin
        apply hcond
        by_cases hkf : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ kForms
        · exact List.mem_append_left _ (List.mem_append_left _ hkf)
        · refine List.mem_append_left _ (List.mem_append_right kForms ?_)
          rw [List.mem_filter]
          refine ⟨hmemBack, ?_⟩
          simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
          intro x hx heqx
          exact hkf (heqx ▸ hx)

/-- **TB-analog of `hintikkaT_diamond_neg`/`hintikkaB_diamond_neg`**, dual of `hintikkaTB_box_pos`:
`F(◇ψ)@w ∈ b` together with `Relation.ReflGen (Relation.SymmGen acc.hasEdge) w w'` and
`accSourcesKnown b acc` imply `F(ψ)@w' ∈ b`. -/
lemma hintikkaTB_diamond_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneTB b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : Relation.ReflGen (Relation.SymmGen (fun a c => acc.hasEdge a c = true)) w w') :
    (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hcond := hH.2.1 (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  cases hr with
  | refl =>
    rcases eq_or_ne (modalTDiaNegSelf b ψ w) [] with hself | hself
    · exact (modalTDiaNegSelf_eq_nil_iff b ψ w).mp hself
    · rw [modalApplyOneTB_diamondNeg_fst] at hcond
      rcases modalApplyOneB_spec.diaNegNotExpanding (⟨.neg, .diamond ψ, w⟩) rfl ψ rfl b acc with
          hk | ⟨bForms, hk⟩
      · rw [hk] at hcond
        simp only [List.isEmpty_iff, hself, if_false] at hcond
        obtain ⟨heq, -⟩ := modalTDiaNegSelf_cases_of_ne_nil hself
        exact hcond (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) (by rw [heq]; simp)
      · rw [hk] at hcond
        obtain ⟨heq, hnotinb⟩ := modalTDiaNegSelf_cases_of_ne_nil hself
        by_cases hbf : (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ bForms
        · exact hcond _ (List.mem_append_left _ hbf)
        · refine hcond (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (List.mem_append_right bForms ?_)
          rw [heq]
          simp only [List.mem_filter, List.mem_singleton, true_and]
          simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
          intro x hx heq2
          exact hbf (heq2 ▸ hx)
  | single hsymm =>
    rcases hsymm with hfwd | hbwd
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
      have hkeq : (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
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
      have hBeq : (modalApplyOneB (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst
          = .persistent (((acc.successorsOf w).filterMap (fun w'' =>
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
              if b.any (· == sf') then none else some sf')) ++
            (modalBDiaNegBack b acc ψ w).filter
              (fun x => !(((acc.successorsOf w).filterMap (fun w'' =>
                let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
                if b.any (· == sf') then none else some sf')).any (· == x)))) := by
        rw [modalApplyOneB_diamondNeg_fst, hkeq]
      rw [modalApplyOneTB_diamondNeg_fst, hBeq] at hcond
      exact hnotin (hcond (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
        (List.mem_append_left _ (List.mem_append_left _ hmemDN)))
    · by_contra hnotin
      have hpred : w' ∈ modalBPredecessorsOf acc w := modalBPredecessorsOf_mem_of_hasEdge hbwd
      have hknown : w' ∈ modalKnownWorlds b := hSrc w' w hbwd
      have hmemBack : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          modalBDiaNegBack b acc ψ w := modalBDiaNegBack_mem_of hpred hknown hnotin
      rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond ψ, w⟩) rfl ψ rfl b acc with
          hk | ⟨kForms, hk⟩
      · have hBeq : (modalApplyOneB (⟨.neg, .diamond ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst
            = .persistent (modalBDiaNegBack b acc ψ w) := by
          have hne : ¬ (modalBDiaNegBack b acc ψ w).isEmpty := by
            simp only [List.isEmpty_iff]
            intro hcontra
            rw [hcontra] at hmemBack
            exact List.not_mem_nil hmemBack
          simp only [modalApplyOneB_diamondNeg_fst, hk]
          rw [if_neg hne]
        rw [modalApplyOneTB_diamondNeg_fst, hBeq] at hcond
        exact hnotin (hcond (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
          (List.mem_append_left _ hmemBack))
      · have hBeq : (modalApplyOneB (⟨.neg, .diamond ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst
            = .persistent (kForms ++
                (modalBDiaNegBack b acc ψ w).filter (fun x => !(kForms.any (· == x)))) := by
          rw [modalApplyOneB_diamondNeg_fst, hk]
        rw [modalApplyOneTB_diamondNeg_fst, hBeq] at hcond
        apply hnotin
        apply hcond
        by_cases hkf : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ kForms
        · exact List.mem_append_left _ (List.mem_append_left _ hkf)
        · refine List.mem_append_left _ (List.mem_append_right kForms ?_)
          rw [List.mem_filter]
          refine ⟨hmemBack, ?_⟩
          simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
          intro x hx heqx
          exact hkf (heqx ▸ hx)

/-- **TB Modal Truth Lemma**: membership in a TB Hintikka branch tracks satisfaction in the
extracted reflexive-symmetric Kripke model `extractModelTB b acc`, given `accSourcesKnown b acc`.

Proof by strong induction on `modalComplexity φ`, mirroring `modalTruthLemmaT`/`modalTruthLemmaB`:
the propositional cases reuse the public, apply-agnostic consistency kit and K's `modalApplyOne_*`
bridge lemmas verbatim, routed through `modalApplyOneTB_eq_of_not_box_diamond` (through
`modalApplyOneB_eq_of_not_box_diamond` to reach K); the box-negative/diamond-positive cases reuse
the free generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` directly;
the box-positive/diamond-negative cases consume the genuinely-new `hintikkaTB_box_pos`/
`hintikkaTB_diamond_neg` bridges above, with the model's `r w w'` unfolding to exactly the
`Relation.ReflGen (Relation.SymmGen ·)` hypothesis those bridges want (`extractModelTB_r`). -/
lemma modalTruthLemmaTB
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneTB b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelTB b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelTB b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelTB b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelTB b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelTB b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelTB b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelTB, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelTB, extractModelWith, List.any_eq_true] at hsat
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
          rw [modalApplyOneTB_eq_of_not_box_diamond _ b acc (by simp) (by simp),
            modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneTB_eq_of_not_box_diamond _ b acc (by simp) (by simp),
            modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
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
          rw [modalApplyOneTB_eq_of_not_box_diamond _ b acc (by simp) (by simp),
            modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
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
          rw [modalApplyOneTB_eq_of_not_box_diamond _ b acc (by simp) (by simp),
            modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
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
        rw [modalApplyOneTB_eq_of_not_box_diamond _ b acc (by simp) (by simp),
          modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneTB_eq_of_not_box_diamond _ b acc (by simp) (by simp),
          modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
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
        rw [modalApplyOneTB_eq_of_not_box_diamond _ b acc (by simp) (by simp),
          modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
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
        rw [modalApplyOneTB_eq_of_not_box_diamond _ b acc (by simp) (by simp),
          modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
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
        have hpath : Relation.ReflGen (Relation.SymmGen (fun a c => acc.hasEdge a c = true)) w w' :=
          extractModelTB_r b acc ▸ hr
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1
          (hintikkaTB_box_pos b acc hSrc hH ψ w w' hmem hpath)
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg_gen modalApplyOneTB b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelTB_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikka_diamond_pos_gen modalApplyOneTB b acc hH ψ w hmem
        exact ⟨w', extractModelTB_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath : Relation.ReflGen (Relation.SymmGen (fun a c => acc.hasEdge a c = true)) w w' :=
          extractModelTB_r b acc ▸ hw'
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2
          (hintikkaTB_diamond_neg b acc hSrc hH ψ w w' hmem hpath) hsψ

/-- An open TB Hintikka branch with `F(φ)@0 ∈ b` (and `accSourcesKnown b acc`) yields a
reflexive-symmetric Kripke countermodel to `φ`. Mirrors `modalOpenBranchT_countermodel`/
`modalOpenBranchB_countermodel`. -/
theorem modalOpenBranchTB_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneTB b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModelTB b acc) 0 φ :=
  (modalTruthLemmaTB b acc hSrc hH φ 0).2 hF

/-! ## `bValid` Completeness -/

/-- **B-completeness of the modal tableau**: if the B tableau on `φ0` returns an open branch,
`φ0` is not B-valid. Mirrors `modalTableauT_complete`: combines `modalExpandBranchesB_hintikka`
instantiated at the initial configuration, the generic initial-branch membership persistence
lemma (`modalExpandBranchesGen_openBranch_initial_mem`), the `accSourcesKnown` top-loop
propagation lemma (`modalExpandBranchesGen_openBranch_accSourcesKnown`, `BDriver.lean` --
the piece with no T analogue, since T never needs known-worlds reasoning), and the
B countermodel extraction above. This direction is fully generic and does **not** depend on
the generalized soundness-chain machinery below. -/
theorem modalTableauB_complete (φ0 : Proposition Atom)
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {a : Accessibility}
    (h : modalTableauB φ0 = .openBranch b a) :
    ¬ bValid φ0 := by
  have h' : modalExpandBranchesB
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      [Accessibility.empty] (modalFuel φ0) = .openBranch b a := h
  have hmeas := modalExpMeasure_entry_le_fuel φ0
  have hInv : ∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
      (ai : Accessibility),
      ([[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]])[i]? = some bi →
      (([[]] : List (List (SignedFormula (Proposition Atom) WorldIndex))))[i]? = some ei →
      ([Accessibility.empty])[i]? = some ai →
      ∃ rank, ModalLoopInvGen modalApplyOneB φ0 bi ei ai rank := by
    intro i bi ei ai hib hie hia
    match i with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia
      subst hib; subst hie; subst hia
      exact ⟨fun _ => modalDepth φ0, modalLoopInvGen_initial modalApplyOneB φ0⟩
    | n + 1 => simp at hib
  have hH : modalHintikkaSetGen modalApplyOneB b a :=
    modalExpandBranchesB_hintikka φ0 (modalFuel φ0)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl hmeas hInv b a h'
  have hSrc : accSourcesKnown b a :=
    modalExpandBranchesGen_openBranch_accSourcesKnown modalApplyOneB modalApplyOneB_spec.freshLocal
      (modalFuel φ0)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl
      (by
        intro p hp
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
        subst hp
        exact accSourcesKnown_empty _)
      b a h'
  have hmemInit : (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
    modalExpandBranchesGen_openBranch_initial_mem modalApplyOneB (modalFuel φ0)
      (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl
      (fun b₀ hb₀ => by
        simp only [List.mem_singleton] at hb₀
        subst hb₀
        simp)
      b a h'
  have hnot := modalOpenBranchB_countermodel b a φ0 hSrc hH hmemInit
  intro htv
  exact hnot (htv WorldIndex (extractModelB b a) (extractModelB_symm b a) 0)

/-! ## B Soundness Discharges + `modalTableauB_sound`

The generalized frame-relativized soundness chain
(`modalStepBranchGen_preserves_satIn`/`modalExpandBranchesGen_closed_unsatIn`,
`FrameSoundness.lean`) takes three raw hypotheses (`hAgree`/`hBoxPos`/`hDiaNeg`) rather than
a hard-coded `modalApplyOne`. B's soundness side therefore only needs to supply its own
`hAgree`/`hBoxPos`/`hDiaNeg` triple and instantiate -- mirroring exactly how T is
instantiated (`hAgreeT`, `modalApplyOneT_boxPos_soundIn`, `modalApplyOneT_diaNeg_soundIn`,
`modalTableauT_sound`). -/

omit [Hashable Atom] in
/-- **S-agree for B**: `modalApplyOneB` agrees with `modalApplyOne` off the two propagating
shapes -- exactly `modalApplyOneB_eq_of_not_boxPos_diaNeg` (`FrameRules.lean`) verbatim; zero
new proof content. Discharges `modalStepBranchGen_preserves_satIn`/
`modalExpandBranchesGen_closed_unsatIn`'s `hAgree` hypothesis at `apply := modalApplyOneB`. -/
theorem hAgreeB
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneB sf b acc = modalApplyOne sf b acc :=
  modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc h

omit [Hashable Atom] in
/-- **S-boxPos for B**: frame-relativized semantic soundness of `modalApplyOneB`'s box-positive
output at `FC := symmFC`. Splits `RuleResultSat` over the `kForms ++ backNew.filter …` append
(`modalApplyOneB_boxPos_fst`, `BDriver.lean`): the `kForms` half is K's own
`modalApplyOne_boxPos_sound` (`FC` unused); the `backNew` half (backward-propagated formulas at
recorded predecessors) is justified by symmetry -- each `x ∈ modalBBoxBack b acc φ lbl` has
`x.label` a predecessor `v` (edge `v → lbl`), so `hacc` gives `m.r (f v) (f lbl)`, symmetry
(`hFC.symm`) gives `m.r (f lbl) (f v)`, and `T(□φ)@lbl`'s box unfolding then places `φ` at
`f v`. -/
theorem modalApplyOneB_boxPos_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : symmFC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneB
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc ∧
    RuleResultSat m f (modalApplyOneB
      (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨hsndeqK, hRRSK⟩ := modalApplyOne_boxPos_sound m f φ lbl b acc hacc hb hmem
  have hbox : Satisfies m (f lbl) (.box φ) := (hb _ hmem).1 rfl
  have hback : ∀ sf' ∈ modalBBoxBack b acc φ lbl, sfSat m f sf' := by
    intro sf' hmem'
    obtain ⟨hxeq, hpred, -, -⟩ := modalBBoxBack_mem hmem'
    have hedge : acc.hasEdge sf'.label lbl = true := modalBPredecessorsOf_hasEdge hpred
    have hmvw : m.r (f sf'.label) (f lbl) := hacc _ _ hedge
    have hmwv : m.r (f lbl) (f sf'.label) := hFC.symm (f sf'.label) (f lbl) hmvw
    rw [hxeq]
    exact sfSat_pos m f φ sf'.label (hbox (f sf'.label) hmwv)
  refine ⟨?_, ?_⟩
  · rw [modalApplyOneB_boxPos_snd]; exact hsndeqK
  · rw [modalApplyOneB_boxPos_fst]
    rcases modalApplyOne_boxPos_eq
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc with
        hk | ⟨kForms, hk⟩
    · rw [hk] at hRRSK ⊢
      split_ifs with hemp
      · trivial
      · exact hback
    · rw [hk] at hRRSK ⊢
      intro sf' hmem'
      simp only [List.mem_append, List.mem_filter] at hmem'
      rcases hmem' with hmem' | ⟨hmem', -⟩
      · exact hRRSK sf' hmem'
      · exact hback sf' hmem'

omit [Hashable Atom] in
/-- **S-diaNeg for B**: dual of `modalApplyOneB_boxPos_soundIn` for the diamond-negative
shape. -/
theorem modalApplyOneB_diaNeg_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : symmFC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem :
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneB
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc ∧
    RuleResultSat m f (modalApplyOneB
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨hsndeqK, hRRSK⟩ := modalApplyOne_diaNeg_sound m f φ lbl b acc hacc hb hmem
  have hdia : ¬ Satisfies m (f lbl) (.diamond φ) := (hb _ hmem).2 rfl
  have hback : ∀ sf' ∈ modalBDiaNegBack b acc φ lbl, sfSat m f sf' := by
    intro sf' hmem'
    obtain ⟨hxeq, hpred, -, -⟩ := modalBDiaNegBack_mem hmem'
    have hedge : acc.hasEdge sf'.label lbl = true := modalBPredecessorsOf_hasEdge hpred
    have hmvw : m.r (f sf'.label) (f lbl) := hacc _ _ hedge
    have hmwv : m.r (f lbl) (f sf'.label) := hFC.symm (f sf'.label) (f lbl) hmvw
    have hnotsat : ¬ Satisfies m (f sf'.label) φ := fun hφ =>
      hdia (Satisfies.diamond_iff.mpr ⟨f sf'.label, hmwv, hφ⟩)
    rw [hxeq]
    exact sfSat_neg m f φ sf'.label hnotsat
  refine ⟨?_, ?_⟩
  · rw [modalApplyOneB_diamondNeg_snd]; exact hsndeqK
  · rw [modalApplyOneB_diamondNeg_fst]
    rcases modalApplyOne_diamondNeg_eq
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
        with hk | ⟨kForms, hk⟩
    · rw [hk] at hRRSK ⊢
      split_ifs with hemp
      · trivial
      · exact hback
    · rw [hk] at hRRSK ⊢
      intro sf' hmem'
      simp only [List.mem_append, List.mem_filter] at hmem'
      rcases hmem' with hmem' | ⟨hmem', -⟩
      · exact hRRSK sf' hmem'
      · exact hback sf' hmem'

/-- **`modalTableauB` is sound**: if the B tableau closes on `F(φ)`, then `φ` is `bValid`.
Contrapositive over `symmFC`, mirroring `modalTableauT_sound`: feeds
`modalExpandBranchesGen_closed_unsatIn symmFC modalApplyOneB` at the initial configuration
`[[F(φ)@0]] [[]] [Accessibility.empty]`. The initial `branchSatisfiableIn symmFC` witness uses
the symmetric falsifying model directly (available since `bValid = frameValid symmFC`
quantifies only symmetric models, so the `by_contra` model is symmetric by hypothesis). -/
theorem modalTableauB_sound (φ : Proposition Atom) (h : modalTableauB φ = .closed) :
    bValid φ := by
  intro World m hsymm w
  by_contra hnotsat
  have hsat : branchSatisfiableIn symmFC [⟨.neg, φ, 0⟩] Accessibility.empty :=
    ⟨World, m, fun _ => w, hsymm,
      fun w1 w2 hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge]),
      fun sf hmem => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst hmem
        exact ⟨fun h => by simp at h, fun _ => hnotsat⟩⟩
  have hunsat := modalExpandBranchesGen_closed_unsatIn symmFC modalApplyOneB
    modalApplyOneB_spec.freshLocal
    hAgreeB
    (fun m f φ lbl b acc hFC hacc hb hmem =>
      modalApplyOneB_boxPos_soundIn m f φ lbl b acc hFC hacc hb hmem)
    (fun m f φ lbl b acc hFC hacc hb hmem =>
      modalApplyOneB_diaNeg_soundIn m f φ lbl b acc hFC hacc hb hmem)
    (modalFuel φ)
    [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty]
    rfl rfl
    (List.Forall₂.cons (accFreshInv_empty _) List.Forall₂.nil)
    (by
      have h' : modalExpandBranchesB
          [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
          [Accessibility.empty] (modalFuel φ) = .closed := h
      exact h')
  cases hunsat with
  | cons h_unsat _ => exact h_unsat hsat

/-! ## `bValid` Decidability -/

/-- **The modal B tableau decides B-validity**: `modalTableauB φ0` closes exactly when `φ0` is
B-valid. Combines soundness (`modalTableauB_sound`) with completeness
(`modalTableauB_complete`, above) via the two-constructor dichotomy of
`ModalTableauResult`. Mirrors `tValid_decides` line-for-line. -/
theorem bValid_decides (φ0 : Proposition Atom) :
    modalTableauB φ0 = .closed ↔ bValid φ0 := by
  constructor
  · exact modalTableauB_sound φ0
  · intro htv
    cases htab : modalTableauB φ0 with
    | closed => rfl
    | openBranch b a => exact absurd htv (modalTableauB_complete φ0 htab)

/-- **B-validity is decidable**: decide by running the modal B tableau and consulting
`bValid_decides`. No `Fintype Atom` assumption is needed, since the tableau computation itself
is the decision procedure. Mirrors `instDecidableTValid` line-for-line. -/
instance instDecidableBValid (φ0 : Proposition Atom) : Decidable (bValid φ0) :=
  match h : modalTableauB φ0 with
  | .closed => .isTrue ((bValid_decides φ0).mp h)
  | .openBranch _ _ => .isFalse (modalTableauB_complete φ0 h)

/-! ## TB Soundness Discharges + `modalTableauTB_sound`

The generalized frame-relativized soundness chain
(`modalStepBranchGen_preserves_satIn`/`modalExpandBranchesGen_closed_unsatIn`,
`FrameSoundness.lean`) takes three raw hypotheses (`hAgree`/`hBoxPos`/`hDiaNeg`) rather than a
hard-coded `modalApplyOne`, so TB's soundness side only needs its own `hAgree`/`hBoxPos`/
`hDiaNeg` triple -- mirroring exactly how T and B are instantiated (`hAgreeT`/`hAgreeB`,
`modalApplyOneT_boxPos_soundIn`/`modalApplyOneB_boxPos_soundIn`, `modalTableauT_sound`/
`modalTableauB_sound`). `modalApplyOneTB_boxPos_soundIn`/`_diaNeg_soundIn` treat
`modalApplyOneB_boxPos_soundIn`/`_diaNeg_soundIn` as a black box for the *entire* B-merged output
(supplying `tbFC_imp_symmFC hFC`), then layer T's self-conjunct soundness on top using
`tbFC_imp_reflFC hFC`'s reflexivity, exactly as `modalApplyOneT_boxPos_soundIn` layers T's
self-conjunct over K.

The `branchSatisfiableIn`-relative semantic lemmas landed in `FrameSoundness.lean`'s TB section
(`branchSatisfiableIn_tbFC_boxPos_self_mem`/`_diaNeg_self_mem`/`_boxPos_pred_mem`/
`_diaNeg_pred_mem`, `modalTBoxSelf_tbFC_sound`/`modalTDiaNegSelf_tbFC_sound`/
`modalBBoxBack_tbFC_sound`/`modalBDiaNegBack_tbFC_sound`) are the TB analogues of T's own
`branchSatisfiableIn_reflFC_boxPos_mem`/`modalTBoxSelf_sound` and B's
`branchSatisfiableIn_symmFC_boxPos_pred_mem`/`modalBBoxBack_sound` -- genuine in-tree semantic
soundness infrastructure, but (matching the T/B precedent exactly: `modalApplyOneT_boxPos_soundIn`
does not call `branchSatisfiableIn_reflFC_boxPos_mem`/`modalTBoxSelf_sound` as black boxes either,
per that theorem's own docstring, which mirrors them "inline" instead) not directly invoked by
the `sfSat`/`RuleResultSat`-based chain below, which is the one `modalTableauTB_sound` actually
needs. -/

omit [Hashable Atom] in
/-- **S-agree for TB**: `modalApplyOneTB` agrees with `modalApplyOne` (K) off the two
propagating shapes -- required by `modalStepBranchGen_preserves_satIn`/
`modalExpandBranchesGen_closed_unsatIn`'s `hAgree` parameter, which is hard-coded against
`modalApplyOne` specifically (not an arbitrary intermediate rule). Chains
`modalApplyOneTB_eq_of_not_boxPos_diaNeg` (`FrameRules.lean`, TB agrees with B) with
`modalApplyOneB_eq_of_not_boxPos_diaNeg` (`FrameRules.lean`, B agrees with K); zero new proof
content. -/
theorem hAgreeTB
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneTB sf b acc = modalApplyOne sf b acc := by
  rw [modalApplyOneTB_eq_of_not_boxPos_diaNeg sf b acc h,
    modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc h]

/-- **S-boxPos for TB**: frame-relativized semantic soundness of `modalApplyOneTB`'s
box-positive output at `FC := tbFC`. Splits `RuleResultSat` over the `bForms ++
selfNew.filter …` append (`modalApplyOneTB_boxPos_fst`, `TBDriver.lean`): the `bForms` half is
`modalApplyOneB_boxPos_soundIn`'s own conclusion (treated as a black box, supplying
`tbFC_imp_symmFC hFC`); the `selfNew` half (at most one extra formula, `T(φ)@lbl` from
`T(□φ)@lbl` at the *same* world) is justified directly by reflexivity
(`(tbFC_imp_reflFC hFC).refl (f lbl)`), mirroring `modalApplyOneT_boxPos_soundIn`'s own
self-conjunct argument. -/
theorem modalApplyOneTB_boxPos_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : tbFC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneTB
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc ∧
    RuleResultSat m f (modalApplyOneTB
      (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨hsndeqB, hRRSB⟩ :=
    modalApplyOneB_boxPos_soundIn m f φ lbl b acc (tbFC_imp_symmFC hFC) hacc hb hmem
  have hselfSat : Satisfies m (f lbl) φ := by
    have hbox : Satisfies m (f lbl) (.box φ) := (hb _ hmem).1 rfl
    simp only [Satisfies] at hbox
    exact hbox (f lbl) ((tbFC_imp_reflFC hFC).refl (f lbl))
  refine ⟨?_, ?_⟩
  · rw [modalApplyOneTB_boxPos_snd]; exact hsndeqB
  · rw [modalApplyOneTB_boxPos_fst]
    rcases modalApplyOneB_spec.boxPosNotExpanding
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc with
        hk | ⟨bForms, hk⟩
    · rw [hk] at hRRSB ⊢
      split_ifs with hemp
      · trivial
      · intro sf' hmem'
        simp only [modalTBoxSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_pos m f φ lbl hselfSat
    · rw [hk] at hRRSB ⊢
      intro sf' hmem'
      simp only [List.mem_append, List.mem_filter] at hmem'
      rcases hmem' with hmem' | ⟨hmem', -⟩
      · exact hRRSB sf' hmem'
      · simp only [modalTBoxSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_pos m f φ lbl hselfSat

/-- **S-diaNeg for TB**: dual of `modalApplyOneTB_boxPos_soundIn` for the diamond-negative
shape. -/
theorem modalApplyOneTB_diaNeg_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : tbFC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem :
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneTB
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc ∧
    RuleResultSat m f (modalApplyOneTB
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨hsndeqB, hRRSB⟩ :=
    modalApplyOneB_diaNeg_soundIn m f φ lbl b acc (tbFC_imp_symmFC hFC) hacc hb hmem
  have hselfSat : ¬ Satisfies m (f lbl) φ := by
    have hdia : ¬ Satisfies m (f lbl) (.diamond φ) := (hb _ hmem).2 rfl
    rw [Satisfies.diamond_iff] at hdia
    push Not at hdia
    exact hdia (f lbl) ((tbFC_imp_reflFC hFC).refl (f lbl))
  refine ⟨?_, ?_⟩
  · rw [modalApplyOneTB_diamondNeg_snd]; exact hsndeqB
  · rw [modalApplyOneTB_diamondNeg_fst]
    rcases modalApplyOneB_spec.diaNegNotExpanding
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
        with hk | ⟨bForms, hk⟩
    · rw [hk] at hRRSB ⊢
      split_ifs with hemp
      · trivial
      · intro sf' hmem'
        simp only [modalTDiaNegSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_neg m f φ lbl hselfSat
    · rw [hk] at hRRSB ⊢
      intro sf' hmem'
      simp only [List.mem_append, List.mem_filter] at hmem'
      rcases hmem' with hmem' | ⟨hmem', -⟩
      · exact hRRSB sf' hmem'
      · simp only [modalTDiaNegSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_neg m f φ lbl hselfSat

/-- **`modalTableauTB` is sound**: if the TB tableau closes on `F(φ)`, then `φ` is `tbValid`.
Contrapositive over `tbFC`, mirroring `modalTableauT_sound`/`modalTableauB_sound`: feeds
`modalExpandBranchesGen_closed_unsatIn tbFC modalApplyOneTB` at the initial configuration
`[[F(φ)@0]] [[]] [Accessibility.empty]`. The initial `branchSatisfiableIn tbFC` witness uses the
reflexive-symmetric falsifying model directly (available since `tbValid = frameValid tbFC`
quantifies only reflexive-symmetric models, so the `by_contra` model satisfies `tbFC` by
hypothesis). -/
theorem modalTableauTB_sound (φ : Proposition Atom) (h : modalTableauTB φ = .closed) :
    tbValid φ := by
  intro World m hfc w
  by_contra hnotsat
  have hsat : branchSatisfiableIn tbFC [⟨.neg, φ, 0⟩] Accessibility.empty :=
    ⟨World, m, fun _ => w, hfc,
      fun w1 w2 hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge]),
      fun sf hmem => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst hmem
        exact ⟨fun h => by simp at h, fun _ => hnotsat⟩⟩
  have hunsat := modalExpandBranchesGen_closed_unsatIn tbFC modalApplyOneTB
    modalApplyOneTB_spec.freshLocal
    hAgreeTB
    (fun m f φ lbl b acc hFC hacc hb hmem =>
      modalApplyOneTB_boxPos_soundIn m f φ lbl b acc hFC hacc hb hmem)
    (fun m f φ lbl b acc hFC hacc hb hmem =>
      modalApplyOneTB_diaNeg_soundIn m f φ lbl b acc hFC hacc hb hmem)
    (modalFuel φ)
    [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty]
    rfl rfl
    (List.Forall₂.cons (accFreshInv_empty _) List.Forall₂.nil)
    (by
      have h' : modalExpandBranchesTB
          [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
          [Accessibility.empty] (modalFuel φ) = .closed := h
      exact h')
  cases hunsat with
  | cons h_unsat _ => exact h_unsat hsat

/-! ## `tbValid` Completeness -/

/-- **TB-completeness of the modal tableau**: if the TB tableau on `φ0` returns an open branch,
`φ0` is not TB-valid. Mirrors `modalTableauB_complete`: combines `modalExpandBranchesTB_hintikka`
(`TBDriver.lean`) instantiated at the initial configuration, the generic initial-branch
membership persistence lemma (`modalExpandBranchesGen_openBranch_initial_mem`), the
`accSourcesKnown` top-loop propagation lemma (`modalExpandBranchesGen_openBranch_accSourcesKnown`,
`BDriver.lean`) instantiated at `modalApplyOneTB_spec.freshLocal`, and the TB countermodel
extraction above (`modalOpenBranchTB_countermodel`, Phase 8), discharging the `tbFC` frame
condition on the open-branch countermodel with `⟨extractModelTB_refl b a, extractModelTB_symm b
a⟩`. This direction is fully generic and does **not** depend on the generalized soundness-chain
machinery above. -/
theorem modalTableauTB_complete (φ0 : Proposition Atom)
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {a : Accessibility}
    (h : modalTableauTB φ0 = .openBranch b a) :
    ¬ tbValid φ0 := by
  have h' : modalExpandBranchesTB
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      [Accessibility.empty] (modalFuel φ0) = .openBranch b a := h
  have hmeas := modalExpMeasure_entry_le_fuel φ0
  have hInv : ∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
      (ai : Accessibility),
      ([[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]])[i]? = some bi →
      (([[]] : List (List (SignedFormula (Proposition Atom) WorldIndex))))[i]? = some ei →
      ([Accessibility.empty])[i]? = some ai →
      ∃ rank, ModalLoopInvGen modalApplyOneTB φ0 bi ei ai rank := by
    intro i bi ei ai hib hie hia
    match i with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia
      subst hib; subst hie; subst hia
      exact ⟨fun _ => modalDepth φ0, modalLoopInvGen_initial modalApplyOneTB φ0⟩
    | n + 1 => simp at hib
  have hH : modalHintikkaSetGen modalApplyOneTB b a :=
    modalExpandBranchesTB_hintikka φ0 (modalFuel φ0)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl hmeas hInv b a h'
  have hSrc : accSourcesKnown b a :=
    modalExpandBranchesGen_openBranch_accSourcesKnown modalApplyOneTB
      modalApplyOneTB_spec.freshLocal
      (modalFuel φ0)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl
      (by
        intro p hp
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
        subst hp
        exact accSourcesKnown_empty _)
      b a h'
  have hmemInit : (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
    modalExpandBranchesGen_openBranch_initial_mem modalApplyOneTB (modalFuel φ0)
      (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl
      (fun b₀ hb₀ => by
        simp only [List.mem_singleton] at hb₀
        subst hb₀
        simp)
      b a h'
  have hnot := modalOpenBranchTB_countermodel b a φ0 hSrc hH hmemInit
  intro htv
  exact hnot (htv WorldIndex (extractModelTB b a)
    ⟨extractModelTB_refl b a, extractModelTB_symm b a⟩ 0)

/-! ## `tbValid` Decidability -/

/-- **The modal TB tableau decides TB-validity**: `modalTableauTB φ0` closes exactly when `φ0`
is TB-valid. Combines soundness (`modalTableauTB_sound`, above) with completeness
(`modalTableauTB_complete`, above) via the two-constructor dichotomy of `ModalTableauResult`.
Mirrors `tValid_decides`/`bValid_decides` line-for-line. -/
theorem tbValid_decides (φ0 : Proposition Atom) :
    modalTableauTB φ0 = .closed ↔ tbValid φ0 := by
  constructor
  · exact modalTableauTB_sound φ0
  · intro htv
    cases htab : modalTableauTB φ0 with
    | closed => rfl
    | openBranch b a => exact absurd htv (modalTableauTB_complete φ0 htab)

/-- **TB-validity is decidable**: decide by running the modal TB tableau
(`modalTableauTB`) and consulting `tbValid_decides`. No `Fintype Atom` assumption is needed,
since the tableau computation itself is the decision procedure. TB is a Tier A corner
discharging the full `RuleApplicationSpec` (`modalApplyOneTB_spec`, `TBDriver.lean`). Mirrors
`instDecidableTValid`/`instDecidableBValid` line-for-line. -/
instance instDecidableTBValid (φ0 : Proposition Atom) : Decidable (tbValid φ0) :=
  match h : modalTableauTB φ0 with
  | .closed => .isTrue ((tbValid_decides φ0).mp h)
  | .openBranch _ _ => .isFalse (modalTableauTB_complete φ0 h)

/-! ## S5 Modal Truth Lemma

`extractModelS5`'s relation is the *equivalence closure* `Relation.EqvGen acc.hasEdge`
(`extractModelS5_r`) -- worlds an arbitrary alternating chain of recorded edges apart are
related, far more than the single raw edge K's box-positive bridge consumes, and more even than
B's `Relation.SymmGen`. The S5 universal rule is exactly what pays for this: `modalApplyOneS5`'s
`T(□φ)@w` arm emits `modalS5BoxAll b φ w`, i.e. `T(φ)@w'` for **every** known world `w'` of the
branch, so a saturated branch already carries a box's payload at every known world. No path
reasoning is needed at all -- the S5 bridges below take a bare `w' ∈ modalKnownWorlds b` where
T's/B's take a `ReflGen`/`SymmGen` path. This is the sense in which S5's universal rule
"trivialises" the truth lemma, and it is why the truth lemma is reachable even though the S5
*termination* chain needs the whole keys-aware pigeonhole apparatus.

The only remaining obligation is that `Relation.EqvGen acc.hasEdge` never leaves the known-world
set, supplied by `eqvGen_mem_modalKnownWorlds_iff` below.

This section is **independent of the S5 termination chain** (`S5LoopInv`) and of the
still-unbuilt spec-free Hintikka lift: like `modalTruthLemmaT`/`modalTruthLemmaB`, it consumes a
`modalHintikkaSetGen modalApplyOneS5 b acc` witness as a *hypothesis*. It is therefore the half
of S5 completeness that does not route through `RuleApplicationSpec` -- see this file's "5 / KB5
Coverage" note and `S5Simplification.lean`'s `modalApplyOneS5_rankStep_not_dischargeable`. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- The equivalence closure of `acc.hasEdge` never leaves `b`'s known-world set, in **both**
directions.

Stated as an `Iff` rather than the one-directional implication the box-positive case literally
consumes, because `Relation.EqvGen`'s `symm` constructor is otherwise not dischargeable by
induction: at `symm` the induction hypothesis supplies `x known → y known` while the goal needs
`y known → x known`, so the two directions must be carried together. The `rel` case is where
both `accSourcesKnown` and `accTargetsKnown` are spent, one per endpoint of a raw edge -- B's
truth lemma already needs `accSourcesKnown` for exactly this reason on the narrower
`Relation.SymmGen` (`modalOpenBranchB_countermodel`'s `hSrc` parameter). -/
lemma eqvGen_mem_modalKnownWorlds_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    {w w' : WorldIndex}
    (h : Relation.EqvGen (fun a c => acc.hasEdge a c = true) w w') :
    w ∈ modalKnownWorlds b ↔ w' ∈ modalKnownWorlds b := by
  induction h with
  | rel x y hxy => exact iff_of_true (hSrc x y hxy) (hTgt x y hxy)
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **S5-analogue of `hintikkaT_box_pos`/`hintikkaB_box_pos`** (genuinely new content): on an
`modalApplyOneS5`-saturated branch, `T(□ψ)@w ∈ b` forces `T(ψ)@v ∈ b` at **every** known world
`v` -- no accessibility path from `w` to `v` is required, which is precisely the S5 universal
rule's contribution.

The proof is a `by_contra`: if `T(ψ)@v ∉ b` then `modalS5BoxAll_mem_of` places `T(ψ)@v` in
`modalS5BoxAll b ψ w` (the dedup filter only removes formulas already on `b`), and the Hintikka
set's conjunct 2 at `T(□ψ)@w` then forces it onto `b`. The `.linear`/`.branching` arms of
`modalApplyOneS5`'s `T(□φ)` dispatch are ruled out by `modalApplyOne_boxPos_eq`, whose
existentially-quantified persistent payload exists for exactly this purpose. -/
lemma hintikkaS5_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneS5 b acc)
    (ψ : Proposition Atom) (w v : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hv : v ∈ modalKnownWorlds b) :
    (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hnotin
  have hall : (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalS5BoxAll b ψ w := modalS5BoxAll_mem_of hv hnotin
  have hcond := hH.2.1 (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  have hK := modalApplyOne_boxPos_eq
    (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc
  unfold modalApplyOneS5 at hcond
  rcases hp : modalApplyOne
      (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hcond hK
  simp only at hcond hK
  rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
  · dsimp only at hcond
    split_ifs at hcond with hemp
    · rw [List.isEmpty_iff] at hemp
      rw [hemp] at hall
      simp at hall
    · exact hnotin (hcond _ hall)
  · dsimp only at hcond
    by_cases hkf : (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ out0
    · exact hnotin (hcond _ (List.mem_append_left _ hkf))
    · refine hnotin (hcond _ (List.mem_append_right out0 ?_))
      simp only [List.mem_filter]
      refine ⟨hall, ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro x hx heq
      exact hkf (heq ▸ hx)

/-- **S5-analogue of `hintikkaT_diamond_neg`**, dual of `hintikkaS5_box_pos`: `F(◇ψ)@w ∈ b`
forces `F(ψ)@v ∈ b` at every known world `v`, via `modalS5DiaNegAll`. -/
lemma hintikkaS5_diamond_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneS5 b acc)
    (ψ : Proposition Atom) (w v : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hv : v ∈ modalKnownWorlds b) :
    (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hnotin
  have hall : (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalS5DiaNegAll b ψ w := modalS5DiaNegAll_mem_of hv hnotin
  have hcond := hH.2.1 (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  have hK := modalApplyOne_diamondNeg_eq
    (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc
  unfold modalApplyOneS5 at hcond
  rcases hp : modalApplyOne
      (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hcond hK
  simp only at hcond hK
  rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
  · dsimp only at hcond
    split_ifs at hcond with hemp
    · rw [List.isEmpty_iff] at hemp
      rw [hemp] at hall
      simp at hall
    · exact hnotin (hcond _ hall)
  · dsimp only at hcond
    by_cases hkf : (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ out0
    · exact hnotin (hcond _ (List.mem_append_left _ hkf))
    · refine hnotin (hcond _ (List.mem_append_right out0 ?_))
      simp only [List.mem_filter]
      refine ⟨hall, ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro x hx heq
      exact hkf (heq ▸ hx)

/-- **The S5 modal truth lemma**: on an
`modalApplyOneS5`-saturated open branch whose recorded edges stay inside the known-world set,
branch membership and `extractModelS5`-satisfaction agree, at every world and both signs.

Mirrors `modalTruthLemmaT`/`modalTruthLemmaB` structurally: the propositional cases
(`atom`/`bot`/`imp`/`and`/`or`) reuse the apply-agnostic consistency kit and K's
`modalApplyOne_*` bridge lemmas verbatim, routed through
`modalApplyOneS5_eq_of_not_boxPos_diaNeg`; the box-negative/diamond-positive (minting) cases
reuse the free generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`
directly, since a raw recorded edge survives into the equivalence closure via
`extractModelS5_hasEdge_imp_r`.

The box-positive/diamond-negative cases are where S5 differs from every other system in the
file: rather than following a path, they observe that `extractModelS5`'s `EqvGen` relation
cannot escape `modalKnownWorlds b` (`eqvGen_mem_modalKnownWorlds_iff`), and then read off the
payload from the universal-rule bridges `hintikkaS5_box_pos`/`hintikkaS5_diamond_neg`. -/
lemma modalTruthLemmaS5
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneS5 b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelS5 b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelS5 b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelS5 b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelS5 b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelS5 b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelS5 b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelS5, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelS5, extractModelWith, List.any_eq_true] at hsat
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
          rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
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
          rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
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
          rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
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
        rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
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
        rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
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
        rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
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
        have hpath : Relation.EqvGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelS5_r b acc ▸ hr
        have hw : w ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hmem
        have hw' : w' ∈ modalKnownWorlds b :=
          (eqvGen_mem_modalKnownWorlds_iff b acc hSrc hTgt hpath).mp hw
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1
          (hintikkaS5_box_pos b acc hH ψ w w' hmem hw')
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg_gen modalApplyOneS5 b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelS5_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikka_diamond_pos_gen modalApplyOneS5 b acc hH ψ w hmem
        exact ⟨w', extractModelS5_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath : Relation.EqvGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelS5_r b acc ▸ hw'
        have hw : w ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hmem
        have hw' : w' ∈ modalKnownWorlds b :=
          (eqvGen_mem_modalKnownWorlds_iff b acc hSrc hTgt hpath).mp hw
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2
          (hintikkaS5_diamond_neg b acc hH ψ w w' hmem hw') hsψ

/-- **Top-loop propagation of `accSourcesKnown`, at `modalApplyOneS5`**: an open
`modalExpandBranchesS5` run started from `accSourcesKnown`-respecting branches returns an
`accSourcesKnown`-respecting branch.

This is a direct instantiation of the generic
`modalExpandBranchesGen_openBranch_accSourcesKnown` at `apply := modalApplyOneS5`, made possible
by that lemma's hypothesis having been *generalized* from the bundled
`spec : RuleApplicationSpec apply` to the raw `freshLocal` dichotomy it actually consumed. The
bundled form was unusable for S5 on principle -- `RuleApplicationSpec modalApplyOneS5` is
mathematically false at `rankStep` (`modalApplyOneS5_rankStep_not_dischargeable`) -- but the
`freshLocal` fact itself holds of `modalApplyOneS5` unconditionally
(`modalApplyOneS5_fresh_local`), since the S5 arms never touch accessibility.
Generalizing cost B nothing: its call site now passes `modalApplyOneB_spec.freshLocal`. -/
theorem modalExpandBranchesS5_openBranch_accSourcesKnown (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      (∀ p ∈ branches.zip accs, accSourcesKnown p.1 p.2) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesGen modalApplyOneS5 branches expandedSets accs fuel =
          .openBranch bR aR →
        accSourcesKnown bR aR :=
  modalExpandBranchesGen_openBranch_accSourcesKnown modalApplyOneS5 modalApplyOneS5_fresh_local
    fuel

/-! ### How the four completeness ingredients are supplied

`modalTableauS5_complete` (below) needs four things at the open branch
`(b, a)` returned by `modalTableauS5 φ0`, all supplied via the witness-reuse rule
`modalApplyOneS5w` (`S5Simplification.lean`), which terminates at K's own `modalFuel`:

1. `F(φ0)@0 ∈ b` -- `modalExpandBranchesGen_openBranch_initial_mem` (fully generic).
2. `accSourcesKnown b a` -- `modalExpandBranchesGen_openBranch_accSourcesKnown` at
   `modalApplyOneS5w` (its only hypothesis is `modalApplyOneS5w_fresh_local`).
3. `accTargetsKnown b a` -- `modalExpandBranchesGen_openBranch_accTargetsKnown` (`BDriver.lean`),
   the top-loop propagation of the generic step-level fact, at `modalApplyOneS5w`.
4. `modalHintikkaSetGen modalApplyOneS5w b a` -- supplied by
   `modalExpandBranchesHintikka` (`CompletenessLoop.lean`) at `Aux := ModalLoopAuxS5w φ0`. That
   parametric lift reaches the a-priori world bound through an opaque `Aux`, and S5w's
   instantiation discharges it by tag-cardinality counting (`S5wTagInv`/`S5wWorldInv`,
   `modalMaxWorld_lt_worldBound_of_S5w`) with **no rank map** needed. `hintikka_congr`
   (`S5Simplification.lean`) then converts this into the `modalHintikkaSetGen modalApplyOneS5`
   witness `modalOpenBranchS5_countermodel` consumes.

Note that fuel insufficiency is a *completeness*-only hazard, never a soundness one:
`modalExpandBranchesGen` at `fuel = 0` returns `.openBranch` whenever any branch is open
(`Saturation.lean`), never a premature `.closed`. This is why `modalTableauS5_sound` held
unconditionally at K's fuel even while the surface still ran the non-terminating rule. -/

/-- An open S5 Hintikka branch with `F(φ)@0 ∈ b` (and the known-world edge closure
`accSourcesKnown`/`accTargetsKnown`) yields an **equivalence-frame** Kripke countermodel to `φ`.
Mirrors `modalOpenBranchT_countermodel`/`modalOpenBranchB_countermodel`.

Together with `extractModelS5_equiv` (which discharges `s5FC` for free), this is the countermodel
half of S5 completeness: it is exactly the input `modalTableauS5_complete` would consume, and it
is available *now*, independent of the still-unbuilt spec-free Hintikka lift that would supply
the `modalHintikkaSetGen modalApplyOneS5 b acc` witness from an open tableau run. -/
theorem modalOpenBranchS5_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneS5 b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModelS5 b acc) 0 φ :=
  (modalTruthLemmaS5 b acc hSrc hTgt hH φ 0).2 hF

/-! ## S5 Completeness and `s5Valid` Decidability

`modalTableauS5` now runs the witness-reuse rule `modalApplyOneS5w` (`S5Simplification.lean`),
which terminates at K's own `modalFuel`. That closes the four-item gap the scope note above
recorded: items 1-3 are supplied by the generic top-loop lemmas at `modalApplyOneS5w`
(`modalApplyOneS5w_fresh_local` is the only hypothesis they take), and item 4 -- "the wall" -- is
supplied by `modalExpandBranchesHintikka` (`CompletenessLoop.lean`) at
`Aux := ModalLoopAuxS5w φ₀`, whose world bound comes from tag-cardinality counting rather than a
rank map. `hintikka_congr` then converts the resulting `modalHintikkaSetGen modalApplyOneS5w`
witness into the `modalHintikkaSetGen modalApplyOneS5` witness `modalOpenBranchS5_countermodel`
consumes, so the entire landed countermodel half above is reused verbatim. -/

/-- **S5-completeness of the modal tableau**: if `φ₀` is `s5Valid`, the S5 tableau closes on it.
Contrapositively: an open branch is a genuine equivalence-frame countermodel.

Assembled from four landed pieces at `apply := modalApplyOneS5w` --
`modalExpandBranchesHintikka` (the spec-free Hintikka lift, at `ModalLoopAuxS5w`),
`modalExpandBranchesGen_openBranch_accSourcesKnown`/`_accTargetsKnown` (`BDriver.lean`),
`modalExpandBranchesGen_openBranch_initial_mem`, and `modalOpenBranchS5_countermodel` above --
with `hintikka_congr` (`S5Simplification.lean`) bridging the two rules' Hintikka sets and
`extractModelS5_equiv` discharging `s5FC` for free. Mirrors `modalTableauB_complete`. -/
theorem modalTableauS5_complete (φ₀ : Proposition Atom) (h : s5Valid φ₀) :
    modalTableauS5 φ₀ = .closed := by
  cases htab : modalTableauS5 φ₀ with
  | closed => rfl
  | openBranch b a =>
    exfalso
    have h' : modalExpandBranchesGen modalApplyOneS5w
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] (modalFuel φ₀) = .openBranch b a := htab
    have hH5w : modalHintikkaSetGen modalApplyOneS5w b a :=
      modalExpandBranchesHintikka modalApplyOneS5w φ₀ (modalApplyOneS5w_specCore.toAt φ₀)
        (ModalLoopAuxS5w φ₀) (ModalLoopAuxS5w_stepPreserved φ₀) (ModalLoopAuxS5w_bounds φ₀)
        (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl (modalExpMeasure_entry_le_fuel φ₀)
        (by
          intro i bi ei ai hib hie hia
          match i with
          | 0 =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia
            subst hib; subst hie; subst hia
            exact modalLoopInvHintikkaS5w_initial φ₀
          | n + 1 => simp at hib)
        b a h'
    have hH : modalHintikkaSetGen modalApplyOneS5 b a := (hintikka_congr b a).mp hH5w
    have hSrc : accSourcesKnown b a :=
      modalExpandBranchesGen_openBranch_accSourcesKnown modalApplyOneS5w
        modalApplyOneS5w_fresh_local (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (by
          intro p hp
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
          subst hp
          exact accSourcesKnown_empty _)
        b a h'
    have hTgt : accTargetsKnown b a :=
      modalExpandBranchesGen_openBranch_accTargetsKnown modalApplyOneS5w
        modalApplyOneS5w_fresh_local (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (by
          intro p hp
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
          subst hp
          intro w w' hedge
          simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
          exact absurd hedge (by decide))
        b a h'
    have hmemInit : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
      modalExpandBranchesGen_openBranch_initial_mem modalApplyOneS5w (modalFuel φ₀)
        (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (fun b₀ hb₀ => by
          simp only [List.mem_singleton] at hb₀
          subst hb₀
          simp)
        b a h'
    have hFC : s5FC (extractModelS5 b a).r :=
      ⟨⟨extractModelS5_refl b a⟩, extractModelS5_rightEuclidean b a⟩
    exact modalOpenBranchS5_countermodel b a φ₀ hSrc hTgt hH hmemInit
      (h WorldIndex (extractModelS5 b a) hFC 0)

/-- **The modal S5 tableau decides S5-validity**: `modalTableauS5 φ₀` closes exactly when `φ₀` is
`s5Valid`. Combines soundness (`modalTableauS5_sound`, `FrameSoundness.lean`) with completeness
(above). Mirrors `tValid_decides`. -/
theorem s5Valid_decides (φ₀ : Proposition Atom) :
    modalTableauS5 φ₀ = .closed ↔ s5Valid φ₀ :=
  ⟨modalTableauS5_sound φ₀, modalTableauS5_complete φ₀⟩

/-- **S5-validity is decidable**: decide by running the modal S5 tableau and consulting
`s5Valid_decides`. No `Fintype Atom` assumption is needed, since the tableau computation itself
is the decision procedure. Mirrors `instDecidableTValid`.

This is the constructive witness to S5's decidability ([Blackburn-de Rijke-Venema][Blackburn2001],
§6.6 p.382, which also records S5's NP-completeness); the terminating witness-reuse rule
`modalApplyOneS5w` supplies the finite-search half. -/
instance instDecidableS5Valid (φ₀ : Proposition Atom) : Decidable (s5Valid φ₀) :=
  match h : modalTableauS5 φ₀ with
  | .closed => .isTrue ((s5Valid_decides φ₀).mp h)
  | .openBranch _ _ => .isFalse (fun hv => by rw [modalTableauS5_complete φ₀ hv] at h; cases h)

/-! ## 5 (Euclidean Frame) Extraction

`extractModelS5_rightEuclidean` above already delivers *some* Euclidean coverage, but only for the
S5 route's `EqvGen`-closed model, which is unconditionally reflexive -- strictly narrower than a
genuine (non-reflexive) rooted Euclidean frame. This section instantiates Strategy B's
closure-at-extraction skeleton (`extractModelWith`) with `Relation.EuclGen`, the bespoke
right-Euclidean least-closure operator (`Cslib/Foundations/Relation/Euclidean.lean`), giving the
model relation genuine Euclidean-but-not-necessarily-reflexive structure. `extractModelS5*` and
`modalTruthLemmaS5` above are **untouched** -- this is a new, independent extraction, not a
modification of the S5 route. -/

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*right-Euclidean closure* `Relation.EuclGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.EuclGen`). Mirrors `extractModelS5`,
substituting `Relation.EuclGen` for `Relation.EqvGen` -- the one-word change the Euclidean route
was built for. -/
def extractModelFive
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (Relation.EuclGen) b acc

omit [Hashable Atom] in
/-- `extractModelFive`'s relation is exactly the right-Euclidean closure of `acc.hasEdge`. -/
lemma extractModelFive_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelFive b acc).r = Relation.EuclGen (fun w w' => acc.hasEdge w w' = true) := rfl

omit [Hashable Atom] in
/-- `extractModelFive`'s relation satisfies `Relation.RightEuclidean` unconditionally: immediate
from the generic instance `RightEuclidean (EuclGen r)` (`Euclidean.lean:147`). Discharges the
`fiveFC` witness (`FrameSoundness.lean`) for the Five countermodel. -/
lemma extractModelFive_rightEuclidean (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Relation.RightEuclidean (extractModelFive b acc).r := by
  rw [extractModelFive_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelFive`'s
(right-Euclidean-closure) relation via `Relation.EuclGen.base`. Needed to reuse the K bridge
lemmas (`hintikka_box_neg_gen`, `hintikka_diamond_pos_gen`), stated in terms of `acc.hasEdge`,
against `extractModelFive`'s closed relation. Mirrors `extractModelS5_hasEdge_imp_r`. -/
lemma extractModelFive_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelFive b acc).r w w' := by
  rw [extractModelFive_r]
  exact Relation.EuclGen.base h

/-! ### Raw Edge Root-Isolation and the Euclidean Closure's Root Behaviour

`modalFiveBoxAll`/`modalFiveDiaNegAll` (`FiveSimplification.lean`) structurally never place
propagated content at world `0`: a rooted (non-necessarily-reflexive) Euclidean frame need not
relate the root to itself, so universal propagation is unsound as a target there. This means the
Euclidean truth lemma's universal-propagation direction genuinely needs the tableau's accessibility
edges to never *target* the root -- true of every edge a real `modalTableauFive` run ever records
(mint arms always target a strictly fresh, hence positive, world; Route (a)'s reuse arm only ever
reuses a non-root witness, `modalApplyOneFive_agree_or_reuse_ne_root`) -- but, exactly
like `accSourcesKnown`/`accTargetsKnown`, this section takes it as an **abstract hypothesis** of
the truth lemma rather than re-deriving the top-loop preservation argument that would discharge it
for an actual tableau run. That discharge (alongside the existing `accSourcesKnown`/
`accTargetsKnown` witnesses) is the obligation of the "Top-Loop Propagation" section below, when
it instantiates `modalTableauFive_complete` from a genuine open branch.

This hypothesis is **not** a mere convenience: without it, the universal-propagation direction is
false in general. A raw edge `acc.hasEdge w 0` would witness a model relation `r w 0` that
`modalFiveBoxAll`'s root exclusion can never certify a matching branch formula `T(ψ)@0` for, so
`T(□ψ)@w ∈ b` would not entail `Satisfies M w (□ψ)`. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Raw edge root-isolation**: every recorded accessibility edge's *target* is a non-root world.
See the section note above for why this is a genuinely new, necessary hypothesis (not derivable
from `accSourcesKnown`/`accTargetsKnown` alone) and why discharging it for a real tableau run is
handled by the "Top-Loop Propagation" section below. -/
def accTargetsNeRoot (acc : Accessibility) : Prop :=
  ∀ w w', acc.hasEdge w w' → w' ≠ (0 : WorldIndex)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every target reachable via the right-Euclidean closure of a root-isolated raw relation is
itself non-root: the `eucl` constructor's conclusion `EuclGen r b c` inherits its target `c`
directly from the second premise's own target, so induction reduces immediately to the raw
`accTargetsNeRoot` hypothesis at the `base` case and to the inner induction hypothesis (no use of
the first premise at all) at the `eucl` case. -/
lemma euclGen_ne_root_of_hasEdge_ne_root {acc : Accessibility} (hRoot : accTargetsNeRoot acc)
    {w w' : WorldIndex}
    (h : Relation.EuclGen (fun a c => acc.hasEdge a c = true) w w') :
    w' ≠ (0 : WorldIndex) := by
  induction h with
  | base hab => exact hRoot _ _ hab
  | eucl _ _ _ ihac => exact ihac

omit [DecidableEq Atom] [Hashable Atom] in
/-- **The root, as a *source* of the Euclidean closure, can only reach a target via a genuine
direct edge.** This is the fact `modalFiveBoxAll`'s root-trigger arm (Route (1)) is built to
match: `EuclGen r 0 w'` cannot arise from the `eucl` constructor, since that would require a
sub-derivation `EuclGen r a 0` reaching *target* `0` -- impossible by
`euclGen_ne_root_of_hasEdge_ne_root`. Hence the only remaining constructor, `base`, applies. -/
lemma euclGen_root_imp_hasEdge {acc : Accessibility} (hRoot : accTargetsNeRoot acc)
    {w' : WorldIndex}
    (h : Relation.EuclGen (fun a c => acc.hasEdge a c = true) (0 : WorldIndex) w') :
    acc.hasEdge 0 w' = true := by
  cases h with
  | base hab => exact hab
  | eucl hab _ => exact absurd rfl (euclGen_ne_root_of_hasEdge_ne_root hRoot hab)

omit [DecidableEq Atom] [Hashable Atom] in
/-- The right-Euclidean closure of `acc.hasEdge` never leaves `b`'s known-world set, in **both**
directions. Five analogue of `eqvGen_mem_modalKnownWorlds_iff`: `EuclGen`'s two constructors
(`base`/`eucl`) replace `EqvGen`'s four (`rel`/`refl`/`symm`/`trans`), but the argument is the
same shape -- the `base` case spends `accSourcesKnown`/`accTargetsKnown` on the one raw edge, and
the `eucl` case chains two `Iff`s sharing a common anchor (the shared first argument `a` of
`EuclGen r a b`/`EuclGen r a c`) via `Iff.symm`/`Iff.trans` instead of an explicit `trans` case. -/
lemma euclGen_mem_modalKnownWorlds_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    {w w' : WorldIndex}
    (h : Relation.EuclGen (fun a c => acc.hasEdge a c = true) w w') :
    w ∈ modalKnownWorlds b ↔ w' ∈ modalKnownWorlds b := by
  induction h with
  | base hab => exact iff_of_true (hSrc _ _ hab) (hTgt _ _ hab)
  | eucl _ _ ihab ihac => exact ihab.symm.trans ihac

/-! ## Five Modal Truth Lemma

`modalFiveBoxAll`/`modalFiveDiaNegAll` (`FiveSimplification.lean`) are **root/non-root
asymmetric**: a non-root trigger propagates to the full non-root cluster (sound via the codomain
equivalence `Relation.rooted_cluster_isEquiv`, exactly the S5 argument transplanted onto
`cod (extractModelFive b acc).r`), while a root trigger propagates only to genuine direct
successors (sound via `hasEdge` alone, no closure reasoning needed). The bridge lemmas below
(`hintikkaFive_box_pos`/`hintikkaFive_diamond_neg`) package this root/non-root dichotomy; the
truth lemma's box/diamond cases then select the matching arm via `euclGen_root_imp_hasEdge`
(root trigger) or plain known-world membership (non-root trigger, via
`euclGen_mem_modalKnownWorlds_iff`). Every other case (propositional, and the box-negative/
diamond-positive mint directions) is unchanged in shape from `modalTruthLemmaS5`. -/

/-- `modalApplyOneFive` agrees with K's `modalApplyOne` at every purely propositional shape
(`atom`/`bot`/`imp`/`and`/`or`): chains `modalApplyOneFive_eq_of_not_mint_shape` (Five's own mint
shapes, diamond-positive/box-negative, are excluded) with
`modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg` (Five's own propagation shapes, box-positive/
diamond-negative, are excluded). Two-step where `modalApplyOneS5_eq_of_not_boxPos_diaNeg` is one
step, since Five (unlike plain S5) stages its rule through the guarded witness-reuse layer. -/
lemma modalApplyOneFive_eq_of_prop_shape
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h1 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ))
    (h2 : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ))
    (h3 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ))
    (h4 : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)) :
    modalApplyOneFive sf b acc = modalApplyOne sf b acc := by
  rw [modalApplyOneFive_eq_of_not_mint_shape sf b acc ⟨h3, h4⟩,
    modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg sf b acc ⟨h1, h2⟩]

/-- **Five-analogue of `hintikkaS5_box_pos`**, root/non-root split: on an
`modalApplyOneFive`-saturated branch, `T(□ψ)@w ∈ b` forces `T(ψ)@v ∈ b` at any known, non-root
world `v`, PROVIDED that whenever the trigger `w` is itself the root, `v` is additionally a
genuine direct root successor (`acc.hasEdge 0 v`) -- exactly the root/non-root dichotomy
`modalFiveBoxAll` itself enforces. The proof is a `by_contra` mirroring `hintikkaS5_box_pos`
exactly once `hall`'s membership is established (via `modalFiveBoxAll_mem_of_root`/
`_mem_of_ne_root`), substituting the two-step `modalApplyOneFive_boxPos_eq` +
`modalApplyOneFiveProp` unfolding for S5's direct `modalApplyOneS5` unfolding. -/
lemma hintikkaFive_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneFive b acc)
    (ψ : Proposition Atom) (w v : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hv : v ∈ modalKnownWorlds b) (hvne : v ≠ (0 : WorldIndex))
    (hedge : w = (0 : WorldIndex) → acc.hasEdge 0 v = true) :
    (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hnotin
  have hall : (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalFiveBoxAll b acc ψ w := by
    by_cases hw0 : w = (0 : WorldIndex)
    · subst hw0
      exact modalFiveBoxAll_mem_of_root hv hvne (hedge rfl) hnotin
    · exact modalFiveBoxAll_mem_of_ne_root hw0 hv hvne hnotin
  have hcond := hH.2.1 (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  have hK := modalApplyOne_boxPos_eq
    (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc
  rw [modalApplyOneFive_boxPos_eq] at hcond
  unfold modalApplyOneFiveProp at hcond
  rcases hp : modalApplyOne
      (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hcond hK
  simp only at hcond hK
  rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
  · dsimp only at hcond
    split_ifs at hcond with hemp
    · rw [List.isEmpty_iff] at hemp
      rw [hemp] at hall
      simp at hall
    · exact hnotin (hcond _ hall)
  · dsimp only at hcond
    by_cases hkf : (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ out0
    · exact hnotin (hcond _ (List.mem_append_left _ hkf))
    · refine hnotin (hcond _ (List.mem_append_right out0 ?_))
      simp only [List.mem_filter]
      refine ⟨hall, ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro x hx heq
      exact hkf (heq ▸ hx)

/-- **Five-analogue of `hintikkaS5_diamond_neg`**, dual of `hintikkaFive_box_pos`: `F(◇ψ)@w ∈ b`
forces `F(ψ)@v ∈ b` at any known, non-root world `v`, subject to the same root/non-root
dichotomy, via `modalFiveDiaNegAll`. -/
lemma hintikkaFive_diamond_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneFive b acc)
    (ψ : Proposition Atom) (w v : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hv : v ∈ modalKnownWorlds b) (hvne : v ≠ (0 : WorldIndex))
    (hedge : w = (0 : WorldIndex) → acc.hasEdge 0 v = true) :
    (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hnotin
  have hall : (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalFiveDiaNegAll b acc ψ w := by
    by_cases hw0 : w = (0 : WorldIndex)
    · subst hw0
      exact modalFiveDiaNegAll_mem_of_root hv hvne (hedge rfl) hnotin
    · exact modalFiveDiaNegAll_mem_of_ne_root hw0 hv hvne hnotin
  have hcond := hH.2.1 (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  have hK := modalApplyOne_diamondNeg_eq
    (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc
  rw [modalApplyOneFive_diaNeg_eq] at hcond
  unfold modalApplyOneFiveProp at hcond
  rcases hp : modalApplyOne
      (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hcond hK
  simp only at hcond hK
  rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
  · dsimp only at hcond
    split_ifs at hcond with hemp
    · rw [List.isEmpty_iff] at hemp
      rw [hemp] at hall
      simp at hall
    · exact hnotin (hcond _ hall)
  · dsimp only at hcond
    by_cases hkf : (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ out0
    · exact hnotin (hcond _ (List.mem_append_left _ hkf))
    · refine hnotin (hcond _ (List.mem_append_right out0 ?_))
      simp only [List.mem_filter]
      refine ⟨hall, ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro x hx heq
      exact hkf (heq ▸ hx)

/-- **The Five modal truth lemma**: on an `modalApplyOneFive`-saturated open
branch whose recorded edges stay inside the known-world set (`hSrc`/`hTgt`) and never target the
root (`hRoot`), branch membership and `extractModelFive`-satisfaction agree, at every world and
both signs.

Mirrors `modalTruthLemmaS5` structurally: the propositional cases reuse the apply-agnostic
consistency kit and K's `modalApplyOne_*` bridge lemmas verbatim, routed through
`modalApplyOneFive_eq_of_prop_shape`; the box-negative/diamond-positive (minting) cases reuse the
free generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` directly, since a
raw recorded edge survives into the right-Euclidean closure via `extractModelFive_hasEdge_imp_r`.

The box-positive/diamond-negative cases are where Five differs from S5: rather than a single
uniform closure argument, they split on whether the trigger `w` is the root -- a root trigger
reads its edge witness off `euclGen_root_imp_hasEdge` directly (no closure detour), while a
non-root trigger reads known-world membership off `euclGen_mem_modalKnownWorlds_iff` (the
non-root cluster case, structurally the S5 argument transplanted via
`Relation.rooted_cluster_isEquiv`) -- and then read off the payload from
`hintikkaFive_box_pos`/`hintikkaFive_diamond_neg`. -/
lemma modalTruthLemmaFive
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (hRoot : accTargetsNeRoot acc)
    (hH : modalHintikkaSetGen modalApplyOneFive b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelFive b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelFive b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelFive b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelFive b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelFive b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelFive b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelFive, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelFive, extractModelWith, List.any_eq_true] at hsat
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
          rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
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
          rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
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
          rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
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
        rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
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
        rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
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
        rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
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
        have hpath : Relation.EuclGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelFive_r b acc ▸ hr
        have hw : w ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hmem
        have hw'ne : w' ≠ (0 : WorldIndex) := euclGen_ne_root_of_hasEdge_ne_root hRoot hpath
        have hw' : w' ∈ modalKnownWorlds b :=
          (euclGen_mem_modalKnownWorlds_iff b acc hSrc hTgt hpath).mp hw
        have hT : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
          hintikkaFive_box_pos b acc hH ψ w w' hmem hw' hw'ne
            (fun hz => euclGen_root_imp_hasEdge hRoot (hz ▸ hpath))
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1 hT
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg_gen modalApplyOneFive b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelFive_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikka_diamond_pos_gen modalApplyOneFive b acc hH ψ w hmem
        exact ⟨w', extractModelFive_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath : Relation.EuclGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelFive_r b acc ▸ hw'
        have hw : w ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hmem
        have hw'ne : w' ≠ (0 : WorldIndex) := euclGen_ne_root_of_hasEdge_ne_root hRoot hpath
        have hw'known : w' ∈ modalKnownWorlds b :=
          (euclGen_mem_modalKnownWorlds_iff b acc hSrc hTgt hpath).mp hw
        have hF : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
          hintikkaFive_diamond_neg b acc hH ψ w w' hmem hw'known hw'ne
            (fun hz => euclGen_root_imp_hasEdge hRoot (hz ▸ hpath))
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2 hF hsψ

/-- An open Five Hintikka branch with `F(φ)@0 ∈ b` (and the known-world edge closure
`accSourcesKnown`/`accTargetsKnown`/`accTargetsNeRoot`) yields a **right-Euclidean-frame** Kripke
countermodel to `φ`. Mirrors `modalOpenBranchS5_countermodel`.

Together with `extractModelFive_rightEuclidean` (which discharges `fiveFC` for free), this is the
countermodel half of Five completeness: it is exactly the input `modalTableauFive_complete`
below consumes. -/
theorem modalOpenBranchFive_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (hRoot : accTargetsNeRoot acc)
    (hH : modalHintikkaSetGen modalApplyOneFive b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModelFive b acc) 0 φ :=
  (modalTruthLemmaFive b acc hSrc hTgt hRoot hH φ 0).2 hF

/-! ## Top-Loop Propagation of `accTargetsNeRoot`

`modalOpenBranchFive_countermodel` takes `accTargetsNeRoot acc` as an abstract hypothesis
(the universal-propagation direction of the truth lemma is false in
general without it). This section discharges it for a **real** `modalTableauFive`/
`modalExpandBranchesFive` run, exactly as `modalExpandBranchesGen_openBranch_accSourcesKnown`/
`_accTargetsKnown` (`BDriver.lean`) already discharge `hSrc`/`hTgt`, so `modalTableauFive_complete`
below can supply all three ingredients at once.

Unlike `accSourcesKnown`/`accTargetsKnown` (which are preserved by *any* rule satisfying the
generic `hFreshLocal` dichotomy), root-isolation is a fact specific to `modalApplyOneFive`'s own
guard shape (`FiveSimplification.lean`): a genuine mint targets `modalNextWorld b`, always
positive since `WorldIndex := Nat`; a Route (a) reuse targets a witness that
`modalApplyOneFive_agree_or_reuse_ne_root` already certifies non-root. Also unlike
`accSourcesKnown`/`accTargetsKnown` individually, `accTargetsNeRoot`'s single-step preservation
needs `accTargetsKnown` as an ambient invariant (to invoke
`modalApplyOneFiveProp_knownWorlds_step`'s own `hknown` hypothesis) -- the same "necessary THIRD
hypothesis beyond the plan's literal signature" pattern `S5Simplification.lean`'s
`modalStepBranchS5w_preserves_worldInv` documents for `S5wWorldInv`. The top-loop lemma below
therefore re-derives `accTargetsKnown` and `accTargetsNeRoot` together, in one induction, rather
than assuming the former has already been established by a separate run. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- A fresh world is never the root: `modalNextWorld b = modalMaxWorld b + 1 ≥ 1`
unconditionally, since `WorldIndex := Nat`. -/
private lemma modalNextWorld_ne_zero_Five
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    modalNextWorld b ≠ (0 : WorldIndex) :=
  Nat.succ_ne_zero (modalMaxWorld b)

/-- **`modalApplyOneFive`'s edge-target root-isolation, per call**: whenever a step of
`modalApplyOneFive` records a new accessibility edge, that edge's target is non-root. Combines
`modalApplyOneFive_agree_or_reuse_ne_root` (a reuse edge's target is the witness
`sf'.label`, already known non-root there) with `modalApplyOneFiveProp_knownWorlds_step` (a
genuine mint edge's target is `modalNextWorld b`, non-root since `WorldIndex := Nat` gives
`modalNextWorld b = modalMaxWorld b + 1 ≥ 1` unconditionally). The per-call companion
`modalStepBranchFive_preserves_accTargetsNeRoot` below needs. -/
lemma modalApplyOneFive_edge_target_ne_root
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc) :
    (modalApplyOneFive sf b acc).snd = acc ∨
      ∃ w', (modalApplyOneFive sf b acc).snd = acc.addEdge sf.label w' ∧
        w' ≠ (0 : WorldIndex) := by
  rcases modalApplyOneFive_agree_or_reuse_ne_root sf b acc with heq | ⟨sf', -, -, hsf'ne, heq⟩
  · rw [heq]
    rcases modalApplyOneFiveProp_knownWorlds_step sf b acc hsfmem hknown with
      ⟨hsnd, -⟩ | ⟨hsnd, -⟩
    · exact Or.inl hsnd
    · exact Or.inr ⟨modalNextWorld b, hsnd, modalNextWorld_ne_zero_Five b⟩
  · rw [heq]
    exact Or.inr ⟨sf'.label, rfl, hsf'ne⟩

/-- **Single-step preservation of `accTargetsNeRoot` at `modalApplyOneFive`**, given
`accTargetsKnown` as an ambient invariant. Mirrors `FmpMeasure.lean`'s
`modalStepBranch_preserves_accTargetsKnown_gen`'s edge-decomposition shape, substituting
`modalApplyOneFive_edge_target_ne_root` for the generic `hFreshLocal` dichotomy. -/
theorem modalStepBranchFive_preserves_accTargetsNeRoot
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneFive b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) (hroot : accTargetsNeRoot acc) :
    accTargetsNeRoot newAcc := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hnewAcc : newAcc = (modalApplyOneFive sf b acc).snd := by
    rcases hfstc : (modalApplyOneFive sf b acc).fst with nf | brs | nf | _
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp at hsf
  rw [hnewAcc]
  rcases modalApplyOneFive_edge_target_ne_root sf b acc hsfmem hknown with
    hsame | ⟨w', hsnd, hw'ne⟩
  · rw [hsame]; exact hroot
  · rw [hsnd]
    intro w1 w1' hedge
    rcases hasEdge_addEdge_cases hedge with ⟨-, rfl⟩ | hold
    · exact hw'ne
    · exact hroot _ _ hold

/-- **Joint single-step preservation of `accTargetsKnown` and `accTargetsNeRoot`** at
`modalApplyOneFive`: bundles `modalStepBranch_preserves_accTargetsKnown_gen` (generic, at
`modalApplyOneFive_fresh_local`) with `modalStepBranchFive_preserves_accTargetsNeRoot` above, so
the top-loop induction below can maintain both invariants together without assuming either has
already been separately established. -/
theorem modalStepBranchFive_preserves_accTargetsKnown_and_NeRoot
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneFive b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) (hroot : accTargetsNeRoot acc) :
    (∀ b' ∈ newBs, accTargetsKnown b' newAcc) ∧ accTargetsNeRoot newAcc :=
  ⟨modalStepBranch_preserves_accTargetsKnown_gen modalApplyOneFive modalApplyOneFive_fresh_local
      b e acc newBs newExps newAcc hstep hknown,
    modalStepBranchFive_preserves_accTargetsNeRoot b e acc newBs newExps newAcc hstep hknown hroot⟩

/-- **Top-loop propagation of `accTargetsKnown` and `accTargetsNeRoot`, together, at
`modalApplyOneFive`**: instantiates the generic `modalExpandBranchesGen_openBranch_gen`
(`BDriver.lean`) at the conjoined predicate `P := fun b acc => accTargetsKnown b acc ∧
accTargetsNeRoot acc`. This is the new top-loop ingredient `modalTableauFive_complete` (below)
needs alongside `accSourcesKnown`'s own top-loop lemma
(`modalExpandBranchesS5_openBranch_accSourcesKnown`'s Five analogue, applied directly at
`modalApplyOneFive_fresh_local`) to supply all of `hSrc`/`hTgt`/`hRoot` from a single real open
branch. -/
theorem modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      (∀ p ∈ branches.zip accs, accTargetsKnown p.1 p.2 ∧ accTargetsNeRoot p.2) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesGen modalApplyOneFive branches expandedSets accs fuel =
          .openBranch bR aR →
        accTargetsKnown bR aR ∧ accTargetsNeRoot aR :=
  modalExpandBranchesGen_openBranch_gen modalApplyOneFive
    (fun b acc => accTargetsKnown b acc ∧ accTargetsNeRoot acc)
    (by
      intro b e acc newBs newExps newAcc hstep hp b' hb'
      have hboth := modalStepBranchFive_preserves_accTargetsKnown_and_NeRoot b e acc newBs newExps
        newAcc hstep hp.1 hp.2
      exact ⟨hboth.1 b' hb', hboth.2⟩)
    fuel

/-! ## `ModalLoopAuxFive`: the Hintikka Wall's `Aux` Instantiation (recipe step 3)

Assembles `modalStepBranchFive_preserves_worldInv` (`FiveSimplification.lean`) into the
`AuxStepPreserved`/`AuxBounds` pair `modalExpandBranchesHintikka` (`CompletenessLoop.lean`) needs
to supply the fourth completeness ingredient -- the Hintikka "wall" -- for a real
`modalTableauFive` run. Mirrors `ModalLoopAuxS5w`/`ModalLoopAuxS5w_bounds`/
`ModalLoopAuxS5w_stepPreserved`/`modalLoopInvHintikkaS5w_initial` (`CompletenessLoop.lean`).
Unlike `ModalLoopAuxS5w` (which ignores its `e` argument entirely), `ModalLoopAuxFive` genuinely
depends on `e` through `FiveWorldInvE`'s `expandedRootTagsFive` bookkeeping -- see
`FiveSimplification.lean`'s module note above `modalStepBranchFive_preserves_worldInv` for why
the root-triggered mint case needs this refinement over the plain, `e`-independent
`FiveWorldInv`. -/

/-- **Five's instantiation of `Aux`**: the `modalUniverse`-closure conjunct (needed since
`AuxStepPreserved`'s signature does not thread `ModalLoopInvHintikka.bClosure` as an ambient
hypothesis the way it threads `accFreshInv`/`accTargetsKnown`) paired with the `e`-aware
world-bound invariant `FiveWorldInvE`. The trailing `Accessibility` argument is required by
`Aux`'s shared signature (`AuxStepPreserved`/`AuxBounds`/`ModalLoopInvHintikka` all expect
`List (SignedFormula …) → List (SignedFormula …) → Accessibility → Prop`) but genuinely unused
here, mirroring `ModalLoopAuxS5w`. -/
@[nolint unusedArguments]
def ModalLoopAuxFive (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (_acc : Accessibility) : Prop :=
  (∀ x ∈ b, x ∈ modalUniverse φ₀) ∧ FiveWorldInvE φ₀ b e

omit [Hashable Atom] in
/-- **`ModalLoopAuxFive` entails the world bound**: the pointwise `AuxBounds` obligation,
discharged by routing `FiveWorldInvE` back to the already-landed, `e`-independent `FiveWorldInv`
(`FiveWorldInvE_imp_FiveWorldInv`) and then `modalMaxWorld_lt_worldBound_of_FiveWorldInv`. -/
theorem ModalLoopAuxFive_bounds (φ₀ : Proposition Atom) :
    AuxBounds φ₀ (ModalLoopAuxFive φ₀) := by
  rintro b e acc ⟨-, hWE⟩
  exact modalMaxWorld_lt_worldBound_of_FiveWorldInv (FiveWorldInvE_imp_FiveWorldInv hWE)

/-- **`ModalLoopAuxFive` is step-preserved**: the `AuxStepPreserved` obligation, discharged
directly by the already-landed `modalStepBranchFive_preserves_worldInv`
(`FiveSimplification.lean`), which is exactly this statement's conclusion under the same
hypotheses (`hb`/`hWE` packaged as `Aux`, `hFresh`/`hKnown` the ambient bookkeeping facts). -/
theorem ModalLoopAuxFive_stepPreserved (φ₀ : Proposition Atom) :
    AuxStepPreserved modalApplyOneFive (ModalLoopAuxFive φ₀) := by
  rintro b e acc newBs newExps newAcc hstep hFresh hKnown ⟨hb, hWE⟩ p hp
  exact modalStepBranchFive_preserves_worldInv hb hWE hFresh hKnown hstep p hp

/-- **Five's initial-configuration rank-free loop invariant**: `ModalLoopInvHintikka` holds of
the starting worklist entry `([F(φ₀)@0], [], ∅)`. Mirrors `modalLoopInvHintikkaS5w_initial`: the
five expanded-set conjuncts are all vacuous over `e = []`, `accFresh`/`accKnown` hold of the
empty relation, and the `aux` field reduces to two one-line facts -- `modalUniverse` membership
(the sole branch formula is `(.neg, φ₀)@0`) and `FiveWorldInvE`, because
`modalMaxWorld [F(φ₀)@0] = 0`, which bounds any sum of cardinalities. -/
lemma modalLoopInvHintikkaFive_initial (φ₀ : Proposition Atom) :
    ModalLoopInvHintikka modalApplyOneFive φ₀ (ModalLoopAuxFive φ₀)
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      Accessibility.empty := by
  have hmemU : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalUniverse φ₀ := by
    simp only [modalUniverse, List.mem_flatMap, List.mem_range]
    exact ⟨0, Nat.succ_pos _, φ₀, modalSubfmls_self_mem φ₀, by simp⟩
  refine ⟨?_, by simp, List.nodup_nil, accFreshInv_empty _, ?_, ⟨?_, ?_⟩,
    by simp, by simp, by simp, by simp, by simp⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact hmemU
  · intro w w' hedge
    simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
    exact absurd hedge (by decide)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact hmemU
  · simp only [FiveWorldInvE, modalMaxWorld, List.foldl_cons, List.foldl_nil]
    exact Nat.zero_le _

/-! ## Five Completeness and `fiveValid` Decidability (recipe step 4)

`modalTableauFive` runs the witness-reuse, root-aware rule `modalApplyOneFive`
(`FiveSimplification.lean`), which terminates at K's own `modalFuel`. Items 1-3 of the
completeness ingredients are supplied by the generic top-loop lemmas at `modalApplyOneFive`
(`modalApplyOneFive_fresh_local` is the only hypothesis they take) plus the bespoke
`accTargetsNeRoot` top-loop pair above, and item 4 -- "the wall" -- is supplied by
`modalExpandBranchesHintikka` (`CompletenessLoop.lean`) at `Aux := ModalLoopAuxFive φ₀` (recipe
steps 1-3 above). Unlike the S5 chain, no `hintikka_congr`-style bridge is needed:
`modalTableauFive` already runs `modalApplyOneFive` directly --
`modalOpenBranchFive_countermodel` above already takes `modalHintikkaSetGen modalApplyOneFive`
as its witness. -/

/-- **Five-completeness of the modal tableau**: if `φ₀` is `fiveValid`, the Five tableau closes
on it. Contrapositively: an open branch is a genuine right-Euclidean-frame countermodel.

Assembled from the four landed pieces at `apply := modalApplyOneFive` --
`modalExpandBranchesHintikka` (the spec-free Hintikka lift, at `ModalLoopAuxFive`),
`modalExpandBranchesGen_openBranch_accSourcesKnown` (`BDriver.lean`),
`modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot` (above),
`modalExpandBranchesGen_openBranch_initial_mem`, and `modalOpenBranchFive_countermodel` above --
with `extractModelFive_rightEuclidean` discharging `fiveFC` for free. Mirrors
`modalTableauS5_complete`. -/
theorem modalTableauFive_complete (φ₀ : Proposition Atom) (h : fiveValid φ₀) :
    modalTableauFive φ₀ = .closed := by
  cases htab : modalTableauFive φ₀ with
  | closed => rfl
  | openBranch b a =>
    exfalso
    have h' : modalExpandBranchesGen modalApplyOneFive
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] (modalFuel φ₀) = .openBranch b a := htab
    have hH : modalHintikkaSetGen modalApplyOneFive b a :=
      modalExpandBranchesHintikka modalApplyOneFive φ₀ (modalApplyOneFive_specCore.toAt φ₀)
        (ModalLoopAuxFive φ₀) (ModalLoopAuxFive_stepPreserved φ₀) (ModalLoopAuxFive_bounds φ₀)
        (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl (modalExpMeasure_entry_le_fuel φ₀)
        (by
          intro i bi ei ai hib hie hia
          match i with
          | 0 =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia
            subst hib; subst hie; subst hia
            exact modalLoopInvHintikkaFive_initial φ₀
          | n + 1 => simp at hib)
        b a h'
    have hSrc : accSourcesKnown b a :=
      modalExpandBranchesGen_openBranch_accSourcesKnown modalApplyOneFive
        modalApplyOneFive_fresh_local (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (by
          intro p hp
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
          subst hp
          exact accSourcesKnown_empty _)
        b a h'
    have hTgtRoot : accTargetsKnown b a ∧ accTargetsNeRoot a :=
      modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (by
          intro p hp
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
          subst hp
          refine ⟨?_, ?_⟩
          · intro w w' hedge
            simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
            exact absurd hedge (by decide)
          · intro w w' hedge
            simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
            exact absurd hedge (by decide))
        b a h'
    have hmemInit : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
      modalExpandBranchesGen_openBranch_initial_mem modalApplyOneFive (modalFuel φ₀)
        (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (fun b₀ hb₀ => by
          simp only [List.mem_singleton] at hb₀
          subst hb₀
          simp)
        b a h'
    have hFC : fiveFC (extractModelFive b a).r := extractModelFive_rightEuclidean b a
    exact modalOpenBranchFive_countermodel b a φ₀ hSrc hTgtRoot.1 hTgtRoot.2 hH hmemInit
      (h WorldIndex (extractModelFive b a) hFC 0)

/-- **The modal Five tableau decides Five-validity**: `modalTableauFive φ₀` closes exactly when
`φ₀` is `fiveValid`. Combines soundness (`modalTableauFive_sound`, `FrameSoundness.lean`) with
completeness (above). Mirrors `s5Valid_decides`. -/
theorem fiveValid_decides (φ₀ : Proposition Atom) :
    modalTableauFive φ₀ = .closed ↔ fiveValid φ₀ :=
  ⟨modalTableauFive_sound φ₀, modalTableauFive_complete φ₀⟩

/-- **Five-validity is decidable**: decide by running the modal Five tableau and consulting
`fiveValid_decides`. No `Fintype Atom` assumption is needed, since the tableau computation itself
is the decision procedure. Mirrors `instDecidableS5Valid`.

This is the constructive witness to the Euclidean logic K5's decidability -- the terminating
witness-reuse, root-aware rule `modalApplyOneFive` supplies the finite-search half. -/
instance instDecidableFiveValid (φ₀ : Proposition Atom) : Decidable (fiveValid φ₀) :=
  match h : modalTableauFive φ₀ with
  | .closed => .isTrue ((fiveValid_decides φ₀).mp h)
  | .openBranch _ _ => .isFalse (fun hv => by rw [modalTableauFive_complete φ₀ hv] at h; cases h)

/-! ## KB5 (Symmetric-Euclidean/PER Frame) Extraction

Extract a Kripke model using the *symmetric right-Euclidean closure*
`Relation.EuclGen (Relation.SymmGen acc.hasEdge)` as the model's relation: right-Euclidean
unconditionally (the generic `RightEuclidean (EuclGen r)` instance, regardless of base) and
symmetric because its base `Relation.SymmGen acc.hasEdge` is symmetric
(`EuclGen.symm_of_symm`/its packaged `Std.Symm` instance, `Euclidean.lean`). This is the *least*
`kb5FC`-satisfying relation containing every raw edge, hence forced, not merely convenient: see
the phase note below the extraction lemmas for why no other choice is available. -/

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*symmetric right-Euclidean closure* of `acc.hasEdge` as the model's relation. -/
def extractModelKb5
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (fun r => Relation.EuclGen (Relation.SymmGen r)) b acc

omit [Hashable Atom] in
/-- `extractModelKb5`'s relation is exactly the symmetric right-Euclidean closure of
`acc.hasEdge`. -/
lemma extractModelKb5_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelKb5 b acc).r =
      Relation.EuclGen (Relation.SymmGen (fun w w' => acc.hasEdge w w' = true)) := rfl

omit [Hashable Atom] in
/-- `extractModelKb5`'s relation satisfies `Relation.RightEuclidean` unconditionally: immediate
from the generic instance `RightEuclidean (EuclGen r)` (`Euclidean.lean:147`), regardless of the
base relation. -/
lemma extractModelKb5_rightEuclidean (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Relation.RightEuclidean (extractModelKb5 b acc).r := by
  rw [extractModelKb5_r]
  infer_instance

omit [Hashable Atom] in
/-- `extractModelKb5`'s relation satisfies `Std.Symm`: its base `Relation.SymmGen acc.hasEdge` is
symmetric (Mathlib's own unnamed instance), so `EuclGen`'s symmetry-preservation instance
(`Euclidean.lean`) applies. Discharges the `Std.Symm` half of `kb5FC` for the KB5 countermodel. -/
lemma extractModelKb5_symm (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Std.Symm (extractModelKb5 b acc).r := by
  rw [extractModelKb5_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelKb5`'s relation
via `Relation.SymmGen.of_rel` then `Relation.EuclGen.base`. -/
lemma extractModelKb5_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelKb5 b acc).r w w' := by
  rw [extractModelKb5_r]
  exact Relation.EuclGen.base (Relation.SymmGen.of_rel h)

/-! ### KB5 Reachability & Known-Worlds Infrastructure

The symmetrized base means the closure's `base` case is now `Relation.SymmGen acc.hasEdge`
(either `acc.hasEdge a c` or `acc.hasEdge c a`) rather than a single raw direction, so both the
known-worlds bridge and any root-reach argument must spend both `accSourcesKnown` and
`accTargetsKnown` at the `base` case (Five's `euclGen_mem_modalKnownWorlds_iff` only ever needed
one direction at a time, matching the raw relation's single direction). -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- The symmetric right-Euclidean closure of `acc.hasEdge` never leaves `b`'s known-world set, in
**both** directions. KB5 analogue of `euclGen_mem_modalKnownWorlds_iff`: the `base` case now
case-splits on which side of the symmetrization the raw edge came from (spending `accSourcesKnown`
then `accTargetsKnown`, or the reverse), while the `eucl` case is identical in shape. -/
lemma symmEuclGen_mem_modalKnownWorlds_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    {w w' : WorldIndex}
    (h : Relation.EuclGen (Relation.SymmGen (fun a c => acc.hasEdge a c = true)) w w') :
    w ∈ modalKnownWorlds b ↔ w' ∈ modalKnownWorlds b := by
  induction h with
  | base hab =>
    rcases hab with hab | hab
    · exact iff_of_true (hSrc _ _ hab) (hTgt _ _ hab)
    · exact iff_of_true (hTgt _ _ hab) (hSrc _ _ hab)
  | eucl _ _ ihab ihac => exact ihab.symm.trans ihac

omit [Hashable Atom] in
/-- **Root-reach membership**: whenever the root `0` reaches `w'` via `extractModelKb5`'s
relation, `w'` is a known world of `b`. Immediate corollary of
`symmEuclGen_mem_modalKnownWorlds_iff` at the always-known root (`label_mem_modalKnownWorlds`
applied to the branch's own initial formula is not needed here -- the root is known whenever the
closure relates it to anything, since `modalKnownWorlds` is populated from every label mentioned
in `b`, and a `base`/`eucl` derivation witnesses at least one raw edge touching `0`). This is the
*positive* direction the KB5 truth lemma's root case consumes: unlike Five's
`euclGen_root_imp_hasEdge` (which restricts the root to its **direct** successors only), this
lemma places every closure-reachable `w'` in the full known non-root cluster **without** asserting
a direct recorded edge -- exactly matching `modalKb5BoxAllUniv`'s unconditional non-root cluster
dump. -/
lemma extractModelKb5_root_reach_mem_modalKnownWorlds
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)
    {w' : WorldIndex} (h : (extractModelKb5 b acc).r (0 : WorldIndex) w') :
    w' ∈ modalKnownWorlds b :=
  (symmEuclGen_mem_modalKnownWorlds_iff b acc hSrc hTgt (extractModelKb5_r b acc ▸ h)).mp h0

omit [Hashable Atom] in
/-- **The ∃-raw-edge-in-derivation witness for the corrected rule's self-target arm**: any world
`w` (other than the root) that reaches the root under
`extractModelKb5`'s relation is itself a known non-root world -- exactly the `clusterNonempty`
witness `hintikkaKb5''_box_pos`/`hintikkaKb5''_diamond_neg`'s `v = 0` arm needs. Immediate from
`symmEuclGen_mem_modalKnownWorlds_iff`'s `.mpr` direction at `(w, 0)`, given the root is known
(`h0`, the same "root always known" invariant `FrameSoundness.lean`'s fuel induction already
threads) -- no new closure-structural argument is needed beyond what
`symmEuclGen_mem_modalKnownWorlds_iff` already supplies; `w` itself is always a valid non-root
witness whenever it is related to the root at all. -/
lemma extractModelKb5_clusterNonempty_of_reach_root
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)
    {w : WorldIndex} (hwne : w ≠ (0 : WorldIndex))
    (hr : (extractModelKb5 b acc).r w (0 : WorldIndex)) :
    ∃ u ∈ modalKnownWorlds b, u ≠ (0 : WorldIndex) :=
  ⟨w, (symmEuclGen_mem_modalKnownWorlds_iff b acc hSrc hTgt (extractModelKb5_r b acc ▸ hr)).mpr h0,
    hwne⟩

/-! ### Re-Derived Hintikka Insertion Lemmas for the Corrected-Gate Rule

`hintikkaKb5''_box_pos`/`hintikkaKb5''_diamond_neg` are the trigger-free analogues of the
retired frozen rule's insertion lemmas: the dichotomy `hcond` they consume drops the `w = 0`
conjunct entirely, since `modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv`'s self-target arm fires for
any trigger `w`. This is precisely the extra case the frozen rule's dichotomy could never cover --
and precisely what the retired frozen-rule counterexample (preserved in `modalTruthLemmaKb5`'s
docstring) shows is REQUIRED for the truth lemma: a non-root world `w`'s box-positive content must
reach the root regardless of whether `w` happens to be the FIRST world to raise `T(□ψ)`. -/

/-- **Trigger-free KB5-analogue of `hintikkaFive_box_pos`**: on a `modalApplyOneKb5''`-saturated
branch, `T(□ψ)@w ∈ b` forces `T(ψ)@v ∈ b` at any target `v` matching `modalKb5BoxAllUniv`'s
dichotomy -- either `v` is known and non-root (unconditional in the trigger `w`), or `v = 0` with
the known cluster nonempty (unconditional in `w` too, unlike the frozen rule). Proof is
`by_contra` mirroring the retired frozen rule's own insertion-lemma proof, substituting
`modalKb5BoxAllUniv_mem_of` for the root/non-root split lemma pair and
`modalApplyOneKb5''_boxPos_eq`/`modalApplyOneKb5''Prop` for their frozen counterparts. -/
lemma hintikkaKb5''_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneKb5'' b acc)
    (ψ : Proposition Atom) (w v : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hcond : (v ∈ modalKnownWorlds b ∧ v ≠ (0 : WorldIndex)) ∨
      (v = (0 : WorldIndex) ∧ ∃ u ∈ modalKnownWorlds b, u ≠ (0 : WorldIndex))) :
    (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hnotin
  have hall : (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalKb5BoxAllUniv b ψ w := modalKb5BoxAllUniv_mem_of hnotin hcond
  have hcond2 := hH.2.1 (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond2
  have hK := modalApplyOne_boxPos_eq
    (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc
  rw [modalApplyOneKb5''_boxPos_eq] at hcond2
  unfold modalApplyOneKb5''Prop at hcond2
  rcases hp : modalApplyOne
      (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hcond2 hK
  simp only at hcond2 hK
  rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
  · dsimp only at hcond2
    split_ifs at hcond2 with hemp
    · rw [List.isEmpty_iff] at hemp
      rw [hemp] at hall
      simp at hall
    · exact hnotin (hcond2 _ hall)
  · dsimp only at hcond2
    by_cases hkf : (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ out0
    · exact hnotin (hcond2 _ (List.mem_append_left _ hkf))
    · refine hnotin (hcond2 _ (List.mem_append_right out0 ?_))
      simp only [List.mem_filter]
      refine ⟨hall, ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro x hx heq
      exact hkf (heq ▸ hx)

/-- **Trigger-free KB5-analogue of `hintikkaFive_diamond_neg`**, dual of
`hintikkaKb5''_box_pos`: `F(◇ψ)@w ∈ b` forces `F(ψ)@v ∈ b` at any target `v` matching
`modalKb5DiaNegAllUniv`'s dichotomy. -/
lemma hintikkaKb5''_diamond_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneKb5'' b acc)
    (ψ : Proposition Atom) (w v : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hcond : (v ∈ modalKnownWorlds b ∧ v ≠ (0 : WorldIndex)) ∨
      (v = (0 : WorldIndex) ∧ ∃ u ∈ modalKnownWorlds b, u ≠ (0 : WorldIndex))) :
    (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hnotin
  have hall : (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalKb5DiaNegAllUniv b ψ w := modalKb5DiaNegAllUniv_mem_of hnotin hcond
  have hcond2 := hH.2.1 (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond2
  have hK := modalApplyOne_diamondNeg_eq
    (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc
  rw [modalApplyOneKb5''_diaNeg_eq] at hcond2
  unfold modalApplyOneKb5''Prop at hcond2
  rcases hp : modalApplyOne
      (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hcond2 hK
  simp only at hcond2 hK
  rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
  · dsimp only at hcond2
    split_ifs at hcond2 with hemp
    · rw [List.isEmpty_iff] at hemp
      rw [hemp] at hall
      simp at hall
    · exact hnotin (hcond2 _ hall)
  · dsimp only at hcond2
    by_cases hkf : (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ out0
    · exact hnotin (hcond2 _ (List.mem_append_left _ hkf))
    · refine hnotin (hcond2 _ (List.mem_append_right out0 ?_))
      simp only [List.mem_filter]
      refine ⟨hall, ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro x hx heq
      exact hkf (heq ▸ hx)

/-! ### The KB5 Truth Lemma

`modalTruthLemmaKb5` is the lemma that was mathematically FALSE for the retired frozen root-gated
rule (see `modalTruthLemmaKb5`'s docstring for the retained counterexample) and is now TRUE for the
corrected-gate `modalApplyOneKb5''` rule: the trigger-free dichotomy
(`modalKb5BoxAllUniv_mem`/`modalKb5DiaNegAllUniv_mem`) lets `hintikkaKb5''_box_pos`/
`hintikkaKb5''_diamond_neg` certify the self-target `v = 0` case regardless of which world
triggered the rule. Structurally mirrors `modalTruthLemmaFive` (above): strong induction on
`modalComplexity`, propositional cases via the apply-agnostic consistency kit routed through
`modalApplyOneKb5''_eq_of_prop_shape`, box-negative/diamond-positive (minting) cases via the free
generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`, and
box-positive/diamond-negative (propagation) cases via the trigger-free dichotomy instead of
Five's root/non-root split. -/

/-- `modalApplyOneKb5''` agrees with K's `modalApplyOne` at every purely propositional shape
(`atom`/`bot`/`imp`/`and`/`or`): chains `modalApplyOneKb5''_eq_of_not_mint_shape`
(`FiveSimplification.lean`, Kb5''s own mint shapes, diamond-positive/box-negative, excluded) with
`modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg` (Kb5''s own propagation shapes, box-positive/
diamond-negative, excluded). Mirrors `modalApplyOneFive_eq_of_prop_shape`. -/
lemma modalApplyOneKb5''_eq_of_prop_shape
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h1 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ))
    (h2 : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ))
    (h3 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ))
    (h4 : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)) :
    modalApplyOneKb5'' sf b acc = modalApplyOne sf b acc := by
  rw [modalApplyOneKb5''_eq_of_not_mint_shape sf b acc ⟨h3, h4⟩,
    modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg sf b acc ⟨h1, h2⟩]

/-- **Any `EuclGen (SymmGen r)` derivation contains a genuine base edge somewhere**: trivial
induction, propagating through the `eucl` case via `ih1` alone (mirrors
`euclGen_ne_root_of_hasEdge_ne_root`'s single-premise-use shape). No side conditions on `r`
needed -- unlike an earlier draft of this fact, this does NOT require `r` irreflexive (which is
not actually true of a real tableau-derived `Accessibility` once witness-reuse is taken into
account: a reused witness world could coincide with its own trigger). -/
private lemma euclGen_symmGen_exists_base {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.EuclGen (Relation.SymmGen r) a b) :
    ∃ p q, Relation.SymmGen r p q := by
  induction h with
  | base hab => exact ⟨_, _, hab⟩
  | eucl _ _ ih1 _ => exact ih1

omit [Hashable Atom] in
/-- **Cluster-nonempty witness for the root-self-relate case**: complements
`extractModelKb5_clusterNonempty_of_reach_root` (above), which handles a non-root world
reaching the root; this covers the residual case where the closure relates the root to itself
(`(extractModelKb5 b acc).r 0 0`), which the box-positive/diamond-negative truth-lemma cases need
regardless of whether the trigger `w` is itself `0`. Only needs `hTgt`/`hRoot`
(`accTargetsNeRoot`, one-sided: raw edges never TARGET the root) -- `euclGen_symmGen_exists_base`
extracts SOME genuine base edge (in either symmetrized direction), and whichever direction
actually fired has its target both known (`hTgt`) and non-root (`hRoot`) for free. -/
lemma extractModelKb5_clusterNonempty_of_root_selfRelate
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hTgt : accTargetsKnown b acc) (hRoot : accTargetsNeRoot acc)
    (hr : (extractModelKb5 b acc).r (0 : WorldIndex) (0 : WorldIndex)) :
    ∃ u ∈ modalKnownWorlds b, u ≠ (0 : WorldIndex) := by
  rw [extractModelKb5_r] at hr
  obtain ⟨p, q, hpq⟩ := euclGen_symmGen_exists_base hr
  rcases hpq with hpq | hpq
  · exact ⟨q, hTgt _ _ hpq, hRoot _ _ hpq⟩
  · exact ⟨p, hTgt _ _ hpq, hRoot _ _ hpq⟩

/-- **The KB5 modal truth lemma**: on a `modalApplyOneKb5''`-saturated open
branch whose recorded edges stay inside the known-world set (`hSrc`/`hTgt`), never target the root
(`hRoot`), and whose root is always known (`h0`), branch membership and
`extractModelKb5`-satisfaction agree, at every world and both signs. This is the lemma that is
mathematically FALSE for the retired frozen root-gated rule and TRUE for the corrected-gate rule:
the trigger-free dichotomy lets the box-positive/diamond-negative cases discharge their `v = 0`
sub-case unconditionally in the trigger `w`, via `extractModelKb5_clusterNonempty_of_reach_root`
(above, `w ≠ 0`) and `extractModelKb5_clusterNonempty_of_root_selfRelate` (above, `w = 0`).

**Why the retired rule could never prove this (counterexample, preserved here as documentation)**:
the retired rule's box-positive/diamond-negative propagation dumped a self-target `0` only when
the *trigger itself* was the root (`w = 0`); it excluded target `0` unconditionally for any
non-root trigger. But `extractModelKb5`'s relation is the symmetrized-then-Euclidean closure of
the raw edges, so a non-root world `w` reachable from the root by a two-hop raw chain `0 → a → w`
(`a` non-root, e.g. an ordinary witness-reuse mint chain) is placed *adjacent to the root* in the
extracted model (`.r w 0`) regardless of which world triggered the rule: raw-edge survival gives
`r 0 a` and `r a w`, `Std.Symm` (`kb5FC`) turns `r 0 a` into `r a 0`, and `RightEuclidean`
(`kb5FC`) chains `r a 0`/`r a w` into `r w 0`. So a box-positive formula `T(□ψ)@w` at such a `w`
could never force `T(ψ)@0 ∈ b` through the retired rule, no matter how saturated the branch
became -- the rule's own definition ruled this out, not merely a proof strategy failing to find
the argument. A concrete Lean-checked witness existed for `φ₀ := ¬(◇◇□p)`: the retired tableau
produced an open branch with raw edges `0 → 1 → 2`, `T(□p)@2 ∈ b`, and `T(p)@0 ∉ b`, while
`(extractModelKb5 b acc).r 2 0` held by exactly the two-hop construction above -- a genuine,
checked failure of this lemma's would-be statement for that rule, not a proof search that had
not yet succeeded. This is not "KB5 completeness is impossible" (Blackburn–de Rijke–Venema
§4.8-4.9 confirms it is achievable via a rooted Euclidean tableau in general); it is specifically
the retired `extractModelKb5`/frozen-rule pairing that could not reach it without a rule change.
The corrected-gate rule `modalApplyOneKb5''` (`modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv`) fixes
this by dropping the trigger-identity conjunct from the self-target gate, so it fires whenever the
known cluster has any non-root member, regardless of which world triggered it -- which is exactly
what this lemma proves TRUE. -/
lemma modalTruthLemmaKb5
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (hRoot : accTargetsNeRoot acc) (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)
    (hH : modalHintikkaSetGen modalApplyOneKb5'' b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelKb5 b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelKb5 b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelKb5 b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelKb5 b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelKb5 b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelKb5 b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelKb5, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelKb5, extractModelWith, List.any_eq_true] at hsat
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
          rw [modalApplyOneKb5''_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneKb5''_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
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
          rw [modalApplyOneKb5''_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
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
          rw [modalApplyOneKb5''_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
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
        rw [modalApplyOneKb5''_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneKb5''_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
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
        rw [modalApplyOneKb5''_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
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
        rw [modalApplyOneKb5''_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
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
        have hpath :
            Relation.EuclGen (Relation.SymmGen (fun a c => acc.hasEdge a c = true)) w w' :=
          extractModelKb5_r b acc ▸ hr
        have hw : w ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hmem
        have hcond : (w' ∈ modalKnownWorlds b ∧ w' ≠ (0 : WorldIndex)) ∨
            (w' = (0 : WorldIndex) ∧ ∃ u ∈ modalKnownWorlds b, u ≠ (0 : WorldIndex)) := by
          rcases eq_or_ne w' (0 : WorldIndex) with rfl | hw'ne
          · refine Or.inr ⟨rfl, ?_⟩
            rcases eq_or_ne w (0 : WorldIndex) with rfl | hwne
            · exact extractModelKb5_clusterNonempty_of_root_selfRelate b acc hTgt hRoot hr
            · exact extractModelKb5_clusterNonempty_of_reach_root b acc hSrc hTgt h0 hwne hr
          · exact Or.inl ⟨(symmEuclGen_mem_modalKnownWorlds_iff b acc hSrc hTgt hpath).mp hw,
              hw'ne⟩
        have hT : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
          hintikkaKb5''_box_pos b acc hH ψ w w' hmem hcond
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1 hT
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg_gen modalApplyOneKb5'' b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelKb5_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikka_diamond_pos_gen modalApplyOneKb5'' b acc hH ψ w hmem
        exact ⟨w', extractModelKb5_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath :
            Relation.EuclGen (Relation.SymmGen (fun a c => acc.hasEdge a c = true)) w w' :=
          extractModelKb5_r b acc ▸ hw'
        have hw : w ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hmem
        have hcond : (w' ∈ modalKnownWorlds b ∧ w' ≠ (0 : WorldIndex)) ∨
            (w' = (0 : WorldIndex) ∧ ∃ u ∈ modalKnownWorlds b, u ≠ (0 : WorldIndex)) := by
          rcases eq_or_ne w' (0 : WorldIndex) with rfl | hw'ne
          · refine Or.inr ⟨rfl, ?_⟩
            rcases eq_or_ne w (0 : WorldIndex) with rfl | hwne
            · exact extractModelKb5_clusterNonempty_of_root_selfRelate b acc hTgt hRoot hw'
            · exact extractModelKb5_clusterNonempty_of_reach_root b acc hSrc hTgt h0 hwne hw'
          · exact Or.inl ⟨(symmEuclGen_mem_modalKnownWorlds_iff b acc hSrc hTgt hpath).mp hw,
              hw'ne⟩
        have hF : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
          hintikkaKb5''_diamond_neg b acc hH ψ w w' hmem hcond
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2 hF hsψ

/-! ### Top-Loop Propagation of `accTargetsNeRoot` and Root-Known-ness
for `modalApplyOneKb5''`

`modalTruthLemmaKb5` (above) takes `accTargetsNeRoot acc` and `(0 : WorldIndex) ∈
modalKnownWorlds b` as abstract hypotheses, exactly as `modalOpenBranchFive_countermodel` took
`accTargetsNeRoot acc` for Five. This section discharges both for a **real**
`modalTableauKb5''`/`modalExpandBranchesKb5''` run, mirroring Five's own
`modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot` with one addition: the KB5''
per-call root-isolation fact (`modalApplyOneKb5''_edge_target_ne_root` below) routes through
`modalApplyOneKb5''Prop_knownWorlds_step` (`FiveSimplification.lean`), which -- unlike Five's
analogue -- ALSO needs `(0 : WorldIndex) ∈ modalKnownWorlds b` as an ambient hypothesis (the
"root always known" invariant that lemma's own development already threads through the soundness
side). So the top-loop induction below bundles THREE invariants together (`accTargetsKnown`,
`accTargetsNeRoot`, and root-known-ness), not Five's two -- `accSourcesKnown`/`accTargetsKnown`
individually remain free via the fully generic
`modalExpandBranchesGen_openBranch_accSourcesKnown`/`_accTargetsKnown` (`BDriver.lean`), consuming
only `modalApplyOneKb5''_fresh_local` (`FiveSimplification.lean`); those generic bridges are used
directly at the assembly site below and are NOT re-derived here. -/

/-- **Every new branch a step produces is the old branch with formulas prepended**, hence
`modalKnownWorlds`-monotone over it. Rule-generic (any `apply`); mirrors the `hbsub` fact inside
`FmpMeasure.lean`'s `modalStepBranch_preserves_accTargetsKnown_gen` proof, exposed here as its own
lemma since this section needs it for root-known-ness preservation, not just `accTargetsKnown`. -/
private lemma modalStepBranchGen_knownWorlds_mono_C
    (apply : RuleApply Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc)) :
    ∀ b' ∈ newBs, modalKnownWorlds b ⊆ modalKnownWorlds b' := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    exact modalKnownWorlds_mono_append nf b
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
    exact modalKnownWorlds_mono_append br b
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    exact modalKnownWorlds_mono_append nf b
  · rw [hfstc] at hsf; simp at hsf

omit [DecidableEq Atom] [Hashable Atom] in
/-- A fresh world is never the root: `modalNextWorld b = modalMaxWorld b + 1 ≥ 1`
unconditionally, since `WorldIndex := Nat`. Mirrors `modalNextWorld_ne_zero_Five`. -/
private lemma modalNextWorld_ne_zero_C
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    modalNextWorld b ≠ (0 : WorldIndex) :=
  Nat.succ_ne_zero (modalMaxWorld b)

/-- **`modalApplyOneKb5''`'s edge-target root-isolation, per call**: whenever a step of
`modalApplyOneKb5''` records a new accessibility edge, that edge's target is non-root. Combines
`modalApplyOneKb5''_agree_or_reuse_ne_root` (reuse edges target a witness already known non-root
there) with `modalApplyOneKb5''Prop_knownWorlds_step` (a genuine mint edge's target is
`modalNextWorld b`, non-root since `WorldIndex := Nat`). Unlike Five's analogue
(`modalApplyOneFive_edge_target_ne_root`), also takes `h0` --
`modalApplyOneKb5''Prop_knownWorlds_step` needs the root-known invariant that lemma's own
development discovered. Mirrors `modalApplyOneFive_edge_target_ne_root`. -/
lemma modalApplyOneKb5''_edge_target_ne_root
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b) :
    (modalApplyOneKb5'' sf b acc).snd = acc ∨
      ∃ w', (modalApplyOneKb5'' sf b acc).snd = acc.addEdge sf.label w' ∧
        w' ≠ (0 : WorldIndex) := by
  rcases modalApplyOneKb5''_agree_or_reuse_ne_root sf b acc with heq | ⟨sf', -, -, hsf'ne, heq⟩
  · rw [heq]
    rcases modalApplyOneKb5''Prop_knownWorlds_step sf b acc hsfmem hknown h0 with
      ⟨hsnd, -⟩ | ⟨hsnd, -⟩
    · exact Or.inl hsnd
    · exact Or.inr ⟨modalNextWorld b, hsnd, modalNextWorld_ne_zero_C b⟩
  · rw [heq]
    exact Or.inr ⟨sf'.label, rfl, hsf'ne⟩

/-- **Single-step preservation of `accTargetsNeRoot` at `modalApplyOneKb5''`**, given
`accTargetsKnown` and root-known-ness as ambient invariants. Mirrors
`modalStepBranchFive_preserves_accTargetsNeRoot`. -/
theorem modalStepBranchKb5''_preserves_accTargetsNeRoot
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneKb5'' b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)
    (hroot : accTargetsNeRoot acc) :
    accTargetsNeRoot newAcc := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hnewAcc : newAcc = (modalApplyOneKb5'' sf b acc).snd := by
    rcases hfstc : (modalApplyOneKb5'' sf b acc).fst with nf | brs | nf | _
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp at hsf
  rw [hnewAcc]
  rcases modalApplyOneKb5''_edge_target_ne_root sf b acc hsfmem hknown h0 with
    hsame | ⟨w', hsnd, hw'ne⟩
  · rw [hsame]; exact hroot
  · rw [hsnd]
    intro w1 w1' hedge
    rcases hasEdge_addEdge_cases hedge with ⟨-, rfl⟩ | hold
    · exact hw'ne
    · exact hroot _ _ hold

/-- **Joint single-step preservation of `accTargetsKnown`, `accTargetsNeRoot`, and root-known-ness**
at `modalApplyOneKb5''`: bundles the generic `modalStepBranch_preserves_accTargetsKnown_gen` (at
`modalApplyOneKb5''_fresh_local`) with `modalStepBranchKb5''_preserves_accTargetsNeRoot` above and
`modalStepBranchGen_knownWorlds_mono_C` (for root-known-ness), so the top-loop induction below can
maintain all three together. Mirrors `modalStepBranchFive_preserves_accTargetsKnown_and_NeRoot`,
extended with the third conjunct. -/
theorem modalStepBranchKb5''_preserves_accTargetsKnown_and_NeRoot_and_rootKnown
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneKb5'' b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)
    (hroot : accTargetsNeRoot acc) :
    (∀ b' ∈ newBs, accTargetsKnown b' newAcc ∧ (0 : WorldIndex) ∈ modalKnownWorlds b') ∧
      accTargetsNeRoot newAcc :=
  ⟨fun b' hb' =>
      ⟨modalStepBranch_preserves_accTargetsKnown_gen modalApplyOneKb5''
        modalApplyOneKb5''_fresh_local b e acc newBs newExps newAcc hstep hknown b' hb',
       modalStepBranchGen_knownWorlds_mono_C modalApplyOneKb5'' b e acc newBs newExps newAcc
         hstep b' hb' h0⟩,
    modalStepBranchKb5''_preserves_accTargetsNeRoot b e acc newBs newExps newAcc hstep hknown h0
      hroot⟩

/-- **Top-loop propagation of `accTargetsKnown`, `accTargetsNeRoot`, and root-known-ness, together,
at `modalApplyOneKb5''`**: instantiates the generic `modalExpandBranchesGen_openBranch_gen`
(`BDriver.lean`) at the conjoined predicate `P := fun b acc => accTargetsKnown b acc ∧
(0 ∈ modalKnownWorlds b) ∧ accTargetsNeRoot acc`. Mirrors
`modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot`, extended with the third conjunct
`modalTruthLemmaKb5` (above) needs. -/
theorem modalExpandBranchesKb5''_openBranch_accTargetsKnown_and_NeRoot_and_rootKnown (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      (∀ p ∈ branches.zip accs, accTargetsKnown p.1 p.2 ∧
        (0 : WorldIndex) ∈ modalKnownWorlds p.1 ∧ accTargetsNeRoot p.2) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesGen modalApplyOneKb5'' branches expandedSets accs fuel =
          .openBranch bR aR →
        accTargetsKnown bR aR ∧ (0 : WorldIndex) ∈ modalKnownWorlds bR ∧ accTargetsNeRoot aR :=
  modalExpandBranchesGen_openBranch_gen modalApplyOneKb5''
    (fun b acc => accTargetsKnown b acc ∧ (0 : WorldIndex) ∈ modalKnownWorlds b ∧
      accTargetsNeRoot acc)
    (by
      intro b e acc newBs newExps newAcc hstep hp b' hb'
      have hboth := modalStepBranchKb5''_preserves_accTargetsKnown_and_NeRoot_and_rootKnown b e acc
        newBs newExps newAcc hstep hp.1 hp.2.1 hp.2.2
      exact ⟨(hboth.1 b' hb').1, (hboth.1 b' hb').2, hboth.2⟩)
    fuel

/-! ## `ModalLoopAuxKb5''`: the Hintikka Wall's `Aux` Instantiation

Assembles `modalStepBranchKb5''_preserves_worldInv` (`FiveSimplification.lean`) into the
`AuxStepPreserved`/`AuxBounds` pair `modalExpandBranchesHintikka` (`CompletenessLoop.lean`) needs
to supply the fourth completeness ingredient -- the Hintikka "wall" -- for a real
`modalTableauKb5''` run. Mirrors `ModalLoopAuxFive`/`_bounds`/`_stepPreserved`/
`modalLoopInvHintikkaFive_initial` above, extended with a THIRD bundled conjunct (root-known-ness)
`AuxStepPreserved`'s ambient hypotheses (`accFreshInv`/`accTargetsKnown`) do not supply but
`modalApplyOneKb5''_worldGrowth`'s propagation-shape case needs -- the same pattern this file's
top-loop propagation section above already established for `accTargetsKnown ∧ accTargetsNeRoot ∧
rootKnown`. `FiveWorldInvE`/`expandedRootTagsFive` are reused directly (no `Kb5''`-named fork --
per `FiveSimplification.lean`'s own Kb5''-termination-bound precedent, these are already
rule-independent, so aliasing would only add surface area with no new content). -/

/-- **Kb5'''s instantiation of `Aux`**: the `modalUniverse`-closure conjunct, the `e`-aware
world-bound invariant `FiveWorldInvE` (reused directly), and root-known-ness (the extra conjunct
`modalApplyOneKb5''`'s corrected propagation gate needs that Five's own instantiation does not).
Mirrors `ModalLoopAuxFive`. -/
@[nolint unusedArguments]
def ModalLoopAuxKb5'' (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (_acc : Accessibility) : Prop :=
  (∀ x ∈ b, x ∈ modalUniverse φ₀) ∧ FiveWorldInvE φ₀ b e ∧ (0 : WorldIndex) ∈ modalKnownWorlds b

omit [Hashable Atom] in
/-- **`ModalLoopAuxKb5''` entails the world bound**: the pointwise `AuxBounds` obligation,
discharged exactly as `ModalLoopAuxFive_bounds` (routes through the shared, rule-independent
`FiveWorldInvE`/`FiveWorldInv` machinery; the extra root-known-ness conjunct is simply unused
here). -/
theorem ModalLoopAuxKb5''_bounds (φ₀ : Proposition Atom) :
    AuxBounds φ₀ (ModalLoopAuxKb5'' φ₀) := by
  rintro b e acc ⟨-, hWE, -⟩
  exact modalMaxWorld_lt_worldBound_of_FiveWorldInv (FiveWorldInvE_imp_FiveWorldInv hWE)

/-- **`ModalLoopAuxKb5''` is step-preserved**: the `AuxStepPreserved` obligation. The
`modalUniverse`-closure and `FiveWorldInvE` conjuncts are discharged together by
`modalStepBranchKb5''_preserves_worldInv` (`FiveSimplification.lean`), fed the root-known-ness
conjunct as its extra `h0` hypothesis; root-known-ness itself is preserved for every child branch
by `modalStepBranchGen_knownWorlds_mono_C` (this file's top-loop propagation section above). -/
theorem ModalLoopAuxKb5''_stepPreserved (φ₀ : Proposition Atom) :
    AuxStepPreserved modalApplyOneKb5'' (ModalLoopAuxKb5'' φ₀) := by
  rintro b e acc newBs newExps newAcc hstep hFresh hKnown ⟨hb, hWE, h0⟩ p hp
  obtain ⟨hbClosure, hWE'⟩ :=
    modalStepBranchKb5''_preserves_worldInv hb hWE hFresh hKnown h0 hstep p hp
  refine ⟨hbClosure, hWE', ?_⟩
  have hp1 : p.1 ∈ newBs := (List.of_mem_zip hp).1
  exact modalStepBranchGen_knownWorlds_mono_C modalApplyOneKb5'' b e acc newBs newExps newAcc
    hstep p.1 hp1 h0

/-- **Kb5'''s initial-configuration rank-free loop invariant**: `ModalLoopInvHintikka` holds of
the starting worklist entry `([F(φ₀)@0], [], ∅)`. Mirrors `modalLoopInvHintikkaFive_initial`,
extended with the trivial root-known-ness fact (`0 ∈ modalKnownWorlds [F(φ₀)@0]`, immediate since
the sole branch formula's own label is `0`). -/
lemma modalLoopInvHintikkaKb5''_initial (φ₀ : Proposition Atom) :
    ModalLoopInvHintikka modalApplyOneKb5'' φ₀ (ModalLoopAuxKb5'' φ₀)
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      Accessibility.empty := by
  have hmemU : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalUniverse φ₀ := by
    simp only [modalUniverse, List.mem_flatMap, List.mem_range]
    exact ⟨0, Nat.succ_pos _, φ₀, modalSubfmls_self_mem φ₀, by simp⟩
  refine ⟨?_, by simp, List.nodup_nil, accFreshInv_empty _, ?_, ⟨?_, ?_, ?_⟩,
    by simp, by simp, by simp, by simp, by simp⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact hmemU
  · intro w w' hedge
    simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
    exact absurd hedge (by decide)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact hmemU
  · simp only [FiveWorldInvE, modalMaxWorld, List.foldl_cons, List.foldl_nil]
    exact Nat.zero_le _
  · exact label_mem_modalKnownWorlds (List.mem_singleton_self _)

/-! ## Kb5'' Completeness and `kb5Valid` Decidability

Mirrors Five's own assembly (`modalOpenBranchFive_countermodel`/`modalTableauFive_
complete`/`fiveValid_decides`/`instDecidableFiveValid` above) at the corrected-gate rule, threading
the extra `h0`/root-known-ness ingredient `modalTruthLemmaKb5` (above) and `ModalLoopAuxKb5''`
(above) both need beyond Five's own two-hypothesis shape. -/

/-- An open Kb5'' Hintikka branch with `F(φ)@0 ∈ b` (and the known-world edge closure
`accSourcesKnown`/`accTargetsKnown`/`accTargetsNeRoot`/root-known-ness) yields a **symmetric
right-Euclidean-frame** Kripke countermodel to `φ`. Mirrors `modalOpenBranchFive_countermodel`,
threading the extra `h0` hypothesis `modalTruthLemmaKb5` (above) needs. -/
theorem modalOpenBranchKb5''_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (hRoot : accTargetsNeRoot acc) (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)
    (hH : modalHintikkaSetGen modalApplyOneKb5'' b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModelKb5 b acc) 0 φ :=
  (modalTruthLemmaKb5 b acc hSrc hTgt hRoot h0 hH φ 0).2 hF

/-- **Kb5''-completeness of the modal tableau**: if `φ₀` is `kb5Valid`, the corrected-gate KB5
tableau closes on it. Contrapositively: an open branch is a genuine symmetric right-Euclidean-frame
countermodel. Assembled from the four landed pieces at `apply := modalApplyOneKb5''` --
`modalExpandBranchesHintikka` (the spec-free Hintikka lift, at `ModalLoopAuxKb5''`, above),
`modalExpandBranchesGen_openBranch_accSourcesKnown` (`BDriver.lean`),
`modalExpandBranchesKb5''_openBranch_accTargetsKnown_and_NeRoot_and_rootKnown` (above),
`modalExpandBranchesGen_openBranch_initial_mem`, and `modalOpenBranchKb5''_countermodel` above --
with `extractModelKb5_rightEuclidean`/`extractModelKb5_symm` discharging `kb5FC` for free. Mirrors
`modalTableauFive_complete`. -/
theorem modalTableauKb5''_complete (φ₀ : Proposition Atom) (h : kb5Valid φ₀) :
    modalTableauKb5'' φ₀ = .closed := by
  cases htab : modalTableauKb5'' φ₀ with
  | closed => rfl
  | openBranch b a =>
    exfalso
    have h' : modalExpandBranchesGen modalApplyOneKb5''
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] (modalFuel φ₀) = .openBranch b a := htab
    have hH : modalHintikkaSetGen modalApplyOneKb5'' b a :=
      modalExpandBranchesHintikka modalApplyOneKb5'' φ₀ (modalApplyOneKb5''_specCore.toAt φ₀)
        (ModalLoopAuxKb5'' φ₀) (ModalLoopAuxKb5''_stepPreserved φ₀) (ModalLoopAuxKb5''_bounds φ₀)
        (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl (modalExpMeasure_entry_le_fuel φ₀)
        (by
          intro i bi ei ai hib hie hia
          match i with
          | 0 =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia
            subst hib; subst hie; subst hia
            exact modalLoopInvHintikkaKb5''_initial φ₀
          | n + 1 => simp at hib)
        b a h'
    have hSrc : accSourcesKnown b a :=
      modalExpandBranchesGen_openBranch_accSourcesKnown modalApplyOneKb5''
        modalApplyOneKb5''_fresh_local (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (by
          intro p hp
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
          subst hp
          exact accSourcesKnown_empty _)
        b a h'
    have hTgtRootKnown : accTargetsKnown b a ∧ (0 : WorldIndex) ∈ modalKnownWorlds b ∧
        accTargetsNeRoot a :=
      modalExpandBranchesKb5''_openBranch_accTargetsKnown_and_NeRoot_and_rootKnown (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (by
          intro p hp
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
          subst hp
          refine ⟨?_, ?_, ?_⟩
          · intro w w' hedge
            simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
            exact absurd hedge (by decide)
          · exact label_mem_modalKnownWorlds (List.mem_singleton_self _)
          · intro w w' hedge
            simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
            exact absurd hedge (by decide))
        b a h'
    have hmemInit : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
      modalExpandBranchesGen_openBranch_initial_mem modalApplyOneKb5'' (modalFuel φ₀)
        (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (fun b₀ hb₀ => by
          simp only [List.mem_singleton] at hb₀
          subst hb₀
          simp)
        b a h'
    have hFC : kb5FC (extractModelKb5 b a).r :=
      ⟨extractModelKb5_symm b a, extractModelKb5_rightEuclidean b a⟩
    exact modalOpenBranchKb5''_countermodel b a φ₀ hSrc hTgtRootKnown.1 hTgtRootKnown.2.2
      hTgtRootKnown.2.1 hH hmemInit (h WorldIndex (extractModelKb5 b a) hFC 0)

/-- **The modal Kb5'' tableau decides KB5-validity**: `modalTableauKb5'' φ₀` closes exactly when
`φ₀` is `kb5Valid`. Combines soundness (`modalTableauKb5''_sound`, `FrameSoundness.lean`) with
completeness (above). Mirrors `fiveValid_decides`. -/
theorem kb5Valid_decides (φ₀ : Proposition Atom) :
    modalTableauKb5'' φ₀ = .closed ↔ kb5Valid φ₀ :=
  ⟨modalTableauKb5''_sound φ₀, modalTableauKb5''_complete φ₀⟩

/-- **KB5-validity is decidable**: decide by running the modal Kb5'' tableau and consulting
`kb5Valid_decides`. No `Fintype Atom` assumption is needed, since the tableau computation itself
is the decision procedure. Mirrors `instDecidableFiveValid`.

This is the constructive witness to KB5's decidability -- the terminating, corrected-gate
full-cluster rule `modalApplyOneKb5''` supplies the finite-search half. -/
instance instDecidableKb5Valid (φ₀ : Proposition Atom) : Decidable (kb5Valid φ₀) :=
  match h : modalTableauKb5'' φ₀ with
  | .closed => .isTrue ((kb5Valid_decides φ₀).mp h)
  | .openBranch _ _ => .isFalse (fun hv => by rw [modalTableauKb5''_complete φ₀ hv] at h; cases h)

/-! ## S4Keyed Completeness (`modalTableauS4Keyed_complete`)

This is the completeness half of the keyed S4 loop-checking driver. **The soundness half is
FALSE AS STATED, not merely unproven or deferred.** `blockingWorldS4Keyed`'s docstring
(`LoopChecking.lean`) carries a machine-checked counterexample:
`CslibTests/S4LoopGuardRegression.lean` witnesses a formula that closes under
`modalExpandBranchesS4Keyed` while having an explicit 3-world reflexive-transitive
countermodel, so it is not `s4Valid`. Do not attempt to prove `modalTableauS4Keyed_sound` for
the driver below; it cannot be proved, because it is not true. Two independent defects are
responsible -- comparing prospective minting content against each world's *recorded* birth key
rather than its *live* content ("staleness"), and admitting a redirect edge with no restriction
that the target be reachable from the source at all ("no reachability restriction") -- and
repairing the first does not repair the second. The repair changes *when* a minting shape may
fire rather than the guard's comparison predicate, landing as a parallel "ordered" driver
(`modalTableauS4KeyedOrdered`) before this one is retired; consult `blockingWorldS4Keyed`'s
docstring for the full account. **Correction**: the decidability half (`s4Valid_decides` /
`instDecidableS4Valid`) is no longer out of scope -- both a genuine soundness theorem
(`modalTableauS4KeyedOrdered_sound`, below) and a completeness theorem
(`modalTableauS4KeyedOrdered_complete`, below) now exist for the *ordered* driver, and the
decidability instance is built from that pair. It is NOT built from the unordered driver's
theorems below, which pair a real completeness result with no valid soundness theorem.

`modalTableauS4Keyed_complete` below is assembled from `modalExpandBranchesS4Keyed_hintikka`
(`LoopChecking.lean`, the keyed top-loop Hintikka lemma, already bridged to the concrete
`modalHintikkaSetS4` form via `hintikka_congr_S4`/`modalHintikkaSetS4_eq` internally) plus
`modalOpenBranchS4_countermodel` above. Mirrors `modalTableauS5_complete`, but needs its own
initial-membership lemma (the `F(φ0)@0 ∈ b` fact) since `modalExpandBranchesS4Keyed` is a
bespoke driver, not an instance of `modalExpandBranchesGen`, so
`modalExpandBranchesGen_openBranch_initial_mem` does not apply. This completeness result itself
remains correct and is not weakened by the soundness defect above -- it says nothing about
which formulas close, only that every valid formula does. -/

private lemma modalTableauS4Keyed_initial (φ₀ : Proposition Atom) :
    S4LoopInv φ₀ [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
        Accessibility.empty [(0, (∅ : Finset (Sign × Proposition Atom)))] ∧
      S4KeyedHintikkaInv φ₀ [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
        Accessibility.empty [(0, (∅ : Finset (Sign × Proposition Atom)))] ∧
      (∀ w k, (w, k) ∈ [((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))] →
        w ∈ modalKnownWorlds
          [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]) ∧
      worldsContiguousS4 [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] := by
  have hmemU : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalUniverseS4 φ₀ := by
    simp only [modalUniverseS4, List.mem_flatMap, List.mem_range]
    exact ⟨0, Nat.succ_pos _, φ₀, modalSubfmls_self_mem φ₀, by simp⟩
  have hknownW : modalKnownWorlds
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] = [0] := by
    simp [modalKnownWorlds]
  refine ⟨⟨?_, List.nodup_nil, ?_, accFreshInv_empty _, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact hmemU
  · intro x hx
    simp at hx
  · intro w w' hedge
    simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
    exact absurd hedge (by decide)
  · intro w hw
    rw [hknownW] at hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨∅, by simp⟩
  · intro w k hwk
    simp only [List.mem_singleton, Prod.mk.injEq] at hwk
    obtain ⟨-, hk⟩ := hwk
    subst hk
    exact Finset.empty_subset _
  · intro w w' k k' hwk hwk' hne
    simp only [List.mem_singleton, Prod.mk.injEq] at hwk hwk'
    exact absurd (hwk.1.trans hwk'.1.symm) hne
  · intro w k hwk
    simp only [List.mem_singleton, Prod.mk.injEq] at hwk
    obtain ⟨-, hk⟩ := hwk
    subst hk
    exact Finset.empty_subset _
  · intro sf hsf
    simp at hsf
  · intro sf hsf
    simp at hsf
  · intro sf hsf
    simp at hsf
  · intro sf hsf
    simp at hsf
  · intro sf hsf
    simp at hsf
  · intro w k hwk
    simp only [List.mem_singleton, Prod.mk.injEq] at hwk
    rw [hknownW]
    simp only [List.mem_singleton]
    exact hwk.1
  · intro w hw
    have hmax : modalMaxWorld
        [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] = 0 := by
      simp [modalMaxWorld]
    rw [hmax] at hw
    rw [hknownW]
    simp only [List.mem_singleton]
    exact Nat.le_zero.mp hw

/-- **S4-completeness of the keyed modal tableau**: if `φ₀` is `s4Valid`, `modalTableauS4Keyed`
closes on it. Contrapositively: an open branch is a genuine reflexive-transitive-frame
countermodel. Assembled from `modalExpandBranchesS4Keyed_hintikka` (`LoopChecking.lean`, fed the
corrected entry invariant `modalTableauS4Keyed_initial` above),
`modalExpandBranchesS4Keyed_openBranch_initial_mem` (`LoopChecking.lean`), and
`modalOpenBranchS4_countermodel` above. Mirrors `modalTableauS5_complete`. -/
theorem modalTableauS4Keyed_complete (φ₀ : Proposition Atom) (h : s4Valid φ₀) :
    modalTableauS4Keyed φ₀ = .closed := by
  cases htab : modalTableauS4Keyed φ₀ with
  | closed => rfl
  | openBranch b a =>
    exfalso
    have h' : modalExpandBranchesS4Keyed φ₀
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))]]
        (modalFuelS4 φ₀) = .openBranch b a := htab
    have hH : modalHintikkaSetS4 φ₀ b a :=
      modalExpandBranchesS4Keyed_hintikka φ₀ (modalFuelS4 φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))]]
        rfl rfl rfl (modalExpMeasure_entry_le_fuelS4 φ₀)
        (by
          intro i bi ei ai keysi hib hie hia hik
          match i with
          | 0 =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia hik
            subst hib; subst hie; subst hia; subst hik
            exact modalTableauS4Keyed_initial φ₀
          | n + 1 => simp at hib)
        b a h'
    have hmemInit : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
      modalExpandBranchesS4Keyed_openBranch_initial_mem φ₀ (modalFuelS4 φ₀)
        (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))]]
        rfl rfl rfl
        (fun b₀ hb₀ => by
          simp only [List.mem_singleton] at hb₀
          subst hb₀
          simp)
        b a h'
    obtain ⟨hnsat, hFC⟩ := modalOpenBranchS4_countermodel φ₀ b a hH hmemInit
    exact hnsat (h WorldIndex (extractModelS4 b a) hFC 0)

/-! ### GATE 0 -- Canonical-Witness Truth-Lemma Micro-Probe

Front-loaded kill gate for the canonical-witness redirect-preservation programme: decides,
before any construction, whether the truth lemma's box-positive semantic-to-syntactic direction
is obtainable at the canonical model, and at what price. Two sub-probes:

- `reflTransGen_addEdge_iff` (Sub-probe 0.A): a mechanical `addEdge`/`ReflTransGen`
  decomposition identity. If this closes, `extractModelS4 b (acc.addEdge src wBlock)` IS
  definitionally the redirect-extended `extractModelS4 b acc`, and the entire agreement-lemma
  workstream collapses into an `rfl`-adjacent identity plus `modalTruthLemmaS4` applied at the
  extended accessibility.
- Sub-probe 0.B (the named residual risk, the converse truth-lemma direction from
  `modalHintikkaSetS4` alone) is not needed once 0.A closes -- see the Phase 1 Verdict below. -/

/-- Local mono step for the probe: every recorded edge of `acc` survives into
`acc.addEdge w w'` (adding an edge only prepends, never removes, list entries). -/
private lemma hasEdge_addEdge_mono_gate0 {acc : Accessibility} {w w' a c : WorldIndex}
    (h : acc.hasEdge a c = true) : (acc.addEdge w w').hasEdge a c = true := by
  simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, Bool.or_eq_true]
  exact Or.inr h

/-- Local self-edge fact for the probe: the newly added edge `w → w'` is recorded in
`acc.addEdge w w'`. -/
private lemma hasEdge_addEdge_self_gate0 (acc : Accessibility) (w w' : WorldIndex) :
    (acc.addEdge w w').hasEdge w w' = true := by
  simp [Accessibility.addEdge, Accessibility.hasEdge]

/-- **Sub-probe 0.A.** The `addEdge`/`ReflTransGen` decomposition identity: a path in the
redirect-extended accessibility relation is either a path in the original relation, or a path
that routes through the new edge `src → wBlock` (an original path into `src`, the new edge, then
an original path out of `wBlock`). Forward direction is tail-induction on the `ReflTransGen`
witness, splitting each edge via `hasEdge_addEdge_cases`; backward direction is `.mono` lifting
plus one `.tail`/`.trans` assembly through the new edge. -/
lemma reflTransGen_addEdge_iff (acc : Accessibility) (src wBlock x y : WorldIndex) :
    Relation.ReflTransGen (fun a c => (acc.addEdge src wBlock).hasEdge a c = true) x y ↔
      Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) x y ∨
      (Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) x src ∧
       Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) wBlock y) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      rcases hasEdge_addEdge_cases hbc with ⟨rfl, rfl⟩ | hbc'
      · rcases ih with ih | ⟨ihsrc, -⟩
        · exact Or.inr ⟨ih, Relation.ReflTransGen.refl⟩
        · exact Or.inr ⟨ihsrc, Relation.ReflTransGen.refl⟩
      · rcases ih with ih | ⟨ihsrc, ihwB⟩
        · exact Or.inl (ih.tail hbc')
        · exact Or.inr ⟨ihsrc, ihwB.tail hbc'⟩
  · rintro (h | ⟨hxsrc, hwBy⟩)
    · exact Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_gate0) x y h
    · exact ((Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_gate0) x src hxsrc).tail
        (hasEdge_addEdge_self_gate0 acc src wBlock)).trans
        (Relation.ReflTransGen.mono (fun a c => hasEdge_addEdge_mono_gate0) wBlock y hwBy)

/-! ## Re-scoped Phase 3 (Plan v6) -- `modalHintikkaSetS4` Preservation Under the Keyed Redirect

Per the `#### Phase 1 Verdict` in `plans/07_canonical-witness-truth-lemma.md`
(`specs/553_s4_loop_guard_soundness_reachability_restriction/`), outcome (i) collapses the
canonical-witness/pinned-witness apparatus entirely: `extractModelS4 b acc` is the witness at
EVERY accessibility state, original and redirected alike, and the sole remaining obligation for
the S4 keyed loop guard's redirect-preservation argument is `modalHintikkaSetS4` preservation
under the specific `addEdge src wBlock` the guard's redirect performs.

Three of `modalHintikkaSetS4`'s four conjuncts collapse mechanically and are discharged below:
the branch-openness conjunct (`isModalClosed`) does not mention `acc` at all, and the two
existential witness conjuncts (box-negative, diamond-positive) are monotone in `acc` --
`hasEdge_addEdge_mono_gate0` (GATE 0 section above) lifts an existing witness edge into the
extended accessibility unchanged. The fourth conjunct, `modalS4Saturated` at the extended
accessibility, is the genuinely hard content (it must additionally account for `src`'s new
successor `wBlock`); `modalHintikkaSetS4_addEdge_of_saturated` below takes it as an explicit
hypothesis, and `modalHintikkaSetS4_addEdge_of_blocked` (also below) discharges that hypothesis
in full via `modalS4Saturated_addEdge_of_blocked` (`LoopChecking.lean`) -- the hard saturation
lemma consuming the `blockedRedirect_boxed_boxPos_mem`/`blockedRedirect_boxed_diaNeg_mem` free
transfers together with the T-rule self-propagation bridges `hintikkaS4_box_pos_self`/
`hintikkaS4_dia_neg_self`, closing re-scoped Phases 3-5 (per the Phase 1 Verdict) as a single
unconditional result: `modalHintikkaSetS4` preservation under the keyed redirect, with no
`modalS4Saturated` hypothesis left outstanding. -/

/-- `modalHintikkaSetS4` preservation under the keyed redirect's `addEdge`, GIVEN the hard
saturation conjunct at the extended accessibility (`hSatExt`, this task's single remaining
obligation -- see the module note above). The other three conjuncts are discharged here
unconditionally. -/
lemma modalHintikkaSetS4_addEdge_of_saturated (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (src wBlock : WorldIndex)
    (hH : modalHintikkaSetS4 φ₀ b acc)
    (hSatExt : modalS4Saturated φ₀ b (acc.addEdge src wBlock)) :
    modalHintikkaSetS4 φ₀ b (acc.addEdge src wBlock) := by
  obtain ⟨hclosed, -, hboxNeg, hdiaPos⟩ := hH
  refine ⟨hclosed, hSatExt, ?_, ?_⟩
  · intro φ w hmem
    obtain ⟨w', hedge, hwit⟩ := hboxNeg φ w hmem
    exact ⟨w', hasEdge_addEdge_mono_gate0 hedge, hwit⟩
  · intro φ w hmem
    obtain ⟨w', hedge, hwit⟩ := hdiaPos φ w hmem
    exact ⟨w', hasEdge_addEdge_mono_gate0 hedge, hwit⟩

/-- **Full assembly, re-scoped Phases 3-5 complete** (per the plan's `#### Phase 1 Verdict`):
`modalHintikkaSetS4` preservation under the keyed redirect's `addEdge`, UNCONDITIONALLY. Combines
`modalHintikkaSetS4_addEdge_of_saturated` (the three mechanical conjuncts, above) with
`modalS4Saturated_addEdge_of_blocked` (`LoopChecking.lean`, the hard saturation conjunct) applied
to the saturation fact `modalHintikkaSetS4_saturated hH` already carried by `hH` itself. No
`modalS4Saturated` hypothesis remains outstanding: `hUniv`/`hkL`/`hblock` are exactly
`S4LoopInv.bClosure`/`S4LoopInv.keyLowerBd`/the keyed guard's own block decision, all available
at any call site holding an `S4LoopInv`. -/
lemma modalHintikkaSetS4_addEdge_of_blocked (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hH : modalHintikkaSetS4 φ₀ b acc)
    (hUniv : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock) :
    modalHintikkaSetS4 φ₀ b (acc.addEdge src wBlock) :=
  modalHintikkaSetS4_addEdge_of_saturated φ₀ b acc src wBlock hH
    (modalS4Saturated_addEdge_of_blocked φ₀ b acc keys s φ src wBlock
      (modalHintikkaSetS4_saturated φ₀ b acc hH) hUniv hkL hblock)

/-- **Redirect-preservation capstone** (re-scoped Phase 6, per the plan's `#### Phase 1
Verdict`): `branchSatisfiableIn s4FC b acc'` at the keyed guard's redirect-extended
accessibility `acc' := acc.addEdge src wBlock`, built directly from `modalHintikkaSetS4 φ₀ b
acc` via `modalHintikkaSetS4_addEdge_of_blocked` and `modalTruthLemmaS4` applied at `acc'` with
`extractModelS4 b acc'` (identity world-assignment) as the witness -- `s4FC` and the edge
conjunct come free from `extractModelS4_refl`/`extractModelS4_trans`/
`extractModelS4_hasEdge_imp_r`, regardless of `acc`, exactly as they already do for the
unredirected case. This is the actual redirect-preservation result the S4 keyed loop guard's
soundness argument needs; re-scoped Phase 7 wires it into the per-step preservation argument. -/
lemma branchSatisfiableIn_s4FC_addEdge_of_blocked (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hH : modalHintikkaSetS4 φ₀ b acc)
    (hUniv : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock) :
    branchSatisfiableIn s4FC b (acc.addEdge src wBlock) := by
  have hH' := modalHintikkaSetS4_addEdge_of_blocked φ₀ b acc keys s φ src wBlock hH hUniv hkL
    hblock
  have htruth := modalTruthLemmaS4 φ₀ b (acc.addEdge src wBlock) hH'
  refine ⟨WorldIndex, extractModelS4 b (acc.addEdge src wBlock), id,
    ⟨extractModelS4_refl b _, extractModelS4_trans b _⟩, ?_, ?_⟩
  · intro w w' hedge
    exact extractModelS4_hasEdge_imp_r b _ hedge
  · intro sf hsfmem
    refine ⟨fun hsign => ?_, fun hsign => ?_⟩
    · have hsfeq : sf = (⟨.pos, sf.formula, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by
        rcases sf with ⟨s', f', w'⟩; simp_all
      rw [hsfeq] at hsfmem
      exact (htruth sf.formula sf.label).1 hsfmem
    · have hsfeq : sf = (⟨.neg, sf.formula, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by
        rcases sf with ⟨s', f', w'⟩; simp_all
      rw [hsfeq] at hsfmem
      exact (htruth sf.formula sf.label).2 hsfmem

/-! ## Re-scoped Phase 7 (Plan v6) -- Wiring the Redirect-Preservation Capstone Into the Keyed
Ordered Driver's Per-Step Soundness Argument

**Layering note.** Soundness content for `modalStepBranchS4KeyedOrdered`
(`LoopChecking.lean`) necessarily lives here rather than in `FrameSoundness.lean` or
`LoopChecking.lean` directly: it needs both `LoopChecking.lean`'s keyed driver definitions
(`modalApplyOneS4Keyed`, `modalStepBranchS4KeyedOrdered`, `S4LoopInv`, `blockingWorldS4Keyed`,
`boxPlusExtraS4`) and `FrameSoundness.lean`'s frame-relativized semantic apparatus (`s4FC`,
`branchSatisfiableIn`, `sfSat`, `modalFourBoxProp_sound`/`modalFourDiaNegProp_sound`); this file
is the only one importing both.

`modalStepBranchS4KeyedOrdered` is **not** an instance of the generic
`modalStepBranchGen_preserves_satIn` (`FrameSoundness.lean`): that generic lemma's `hAgree`
hypothesis requires `apply` to agree with `modalApplyOne` off the two T/4-rule-relevant shapes,
but the keyed guard's BLOCKED arm departs from `modalApplyOne` precisely at the two MINTING
shapes (`F(□φ)@w`, `T(◇φ)@w`), which `hAgree`'s domain does not exclude. A bespoke step lemma is
needed, case-splitting on `modalStepBranchS4KeyedOrdered_cases`'s two branches and, within the
per-formula body, on the same four-way shape split `modalStepBranchS4Keyed_preserves_
S4KeyedHintikkaInv` already uses: propositional/non-modal, the two 4-rule shapes
(`T(□φ)@w`/`F(◇φ)@w`), and the two minting shapes (`F(□φ)@w`/`T(◇φ)@w`, sub-split on
`blockingWorldS4Keyed`'s blocked/unblocked decision). -/

omit [Hashable Atom] in
/-- **Box-plus transitivity bridge.** Every element of `boxPlusExtraS4 b w`
(`LoopChecking.lean`) -- the S4-keyed mint's additional BOXED transmission (`T(□ψ)@w'`/
`F(◇ψ)@w'` for every `T(□ψ)@w`/`F(◇ψ)@w` already on the branch, retargeted to the fresh witness
`w' := modalNextWorld b`) -- is satisfied at the pointwise-extended world-assignment (`f`
everywhere except `w'`, where it takes the fresh witness value `ww`), given `IsTrans W m.r` and
the mint edge `m.r (f w) ww`. Both halves reduce to a single hop of transitivity: a `T(□ψ)@w`
fact gives `∀ v, m.r (f w) v → Satisfies m v ψ`; any `m.r`-successor `v` of `ww` is also an
`m.r`-successor of `f w` (`IsTrans.trans (f w) ww v`), so the same universal fact transfers
unchanged to `w'` -- literally `T(□ψ)@w'`, not merely the unwrapped `T(ψ)@w'` K's own minting
already transmits. The diamond-negative half is the direct contrapositive dual. This is the one
piece of genuinely new semantic content Phase 7's mint-unblocked case needs beyond what
`modalApplyOneS4KeyedMint_boxNeg_witness`/`_diaPos_witness` (`LoopChecking.lean`, structural
only) already supply. -/
lemma boxPlusExtraS4_sat {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (htrans : IsTrans W m.r)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (ww : W) (hwwr : m.r (f w) ww) :
    ∀ sf ∈ boxPlusExtraS4 b w,
      sfSat m (fun n => if n = modalNextWorld b then ww else f n) sf := by
  intro sf hsf
  simp only [boxPlusExtraS4, List.mem_append, List.mem_filterMap] at hsf
  rcases hsf with hsf | hsf
  · obtain ⟨⟨ψ, src⟩, hpairMem, heq⟩ := hsf
    split_ifs at heq with hsrceq hinb
    · simp only [Option.some.injEq] at heq
      subst heq
      simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
      obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
      split_ifs at hbsfeq with hbsfpos
      cases hbf : bsf.formula with
      | box ψ' =>
        rw [hbf] at hbsfeq
        simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
        obtain ⟨hψ, hsrc⟩ := hbsfeq
        have hsrc_w : bsf.label = w := by rw [hsrc]; simpa using hsrceq
        have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
        rw [hbf, hsrc_w] at hbox_sat
        simp only [Satisfies] at hbox_sat
        refine sfSat_pos m _ (.box ψ) (modalNextWorld b) ?_
        simp only [Satisfies, ite_true]
        intro v hv
        rw [← hψ]
        exact hbox_sat v (htrans.trans (f w) ww v hwwr hv)
      | _ => simp [hbf] at hbsfeq
  · obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hsf
    by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == w) = true
    · rw [if_pos hbsfsign] at hbsfprop
      cases hbf : bsf.formula with
      | diamond ψ' =>
        simp only [hbf] at hbsfprop
        by_cases hinb :
            (b.any (· == (⟨.neg, .diamond ψ', modalNextWorld b⟩ :
              SignedFormula (Proposition Atom) WorldIndex))) = true
        · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
        · rw [if_neg hinb] at hbsfprop
          simp only [Option.some.injEq] at hbsfprop
          subst hbsfprop
          have hsign : bsf.sign = .neg ∧ bsf.label = w := by
            simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
            exact hbsfsign
          have hdianeg := (hb bsf hbsfMem).2 hsign.1
          rw [hbf, hsign.2] at hdianeg
          simp only [Satisfies] at hdianeg
          refine sfSat_neg m _ (.diamond ψ') (modalNextWorld b) ?_
          simp only [Satisfies, ite_true]
          intro hdia'
          apply hdianeg
          obtain ⟨u, hu, hφu⟩ := Satisfies.diamond_iff.mp hdia'
          exact Satisfies.diamond_iff.mpr ⟨u, htrans.trans (f w) ww u hwwr hu, hφu⟩
      | _ => simp [hbf] at hbsfprop
    · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop

/-- **Propositional/non-modal step soundness for the S4-keyed guard.** At a signed formula whose
top-level connective is neither `box` nor `diamond`, `modalApplyOneS4Keyed` coincides with plain
K's `modalApplyOne` (`modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box`, `LoopChecking.lean`),
and `modalApplyOne` itself never touches `acc` at this shape either -- all four `box`/`diamond`
match arms of its own internal K-rule fallback are excluded by `hnb`/`hnd`, so that match always
falls through to `_, _ => (.notApplicable, acc)`, and the propositional branch it tries first
(`tryAllPropRules`) never inspects `acc` at all. This makes the propositional/non-modal case the
cheapest of the whole bespoke case-split: `tryAllPropRules_sat` (`SoundnessStep.lean`) already
discharges satisfiability preservation for every propositional shape (`and`/`or`/`imp`, and
`atom`/`bot`/`box`/`diamond` vacuously via `notApplicable`) in one call, in place of the
~350-line inline case-by-case duplication `modalStepBranchGen_preserves_satIn`
(`FrameSoundness.lean`) uses for the analogous plain-K arm. -/
lemma modalApplyOneS4Keyed_notBoxDia_sat (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (hsf : sfSat m f (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)) :
    (modalApplyOneS4Keyed φ₀ keys ⟨s, φ, w⟩ b acc).snd = acc ∧
      RuleResultSat m f (modalApplyOneS4Keyed φ₀ keys ⟨s, φ, w⟩ b acc).fst := by
  rw [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys s φ w hnb hnd b acc]
  unfold modalApplyOne
  simp only
  split_ifs with hpa
  · exact ⟨rfl, tryAllPropRules_sat m f ⟨s, φ, w⟩ hsf⟩
  · rcases s with _ | _ <;> rcases φ with _ | _ | _ | _ | _ | ψ | ψ <;>
      first
        | exact ⟨rfl, trivial⟩
        | exact absurd rfl (hnb ψ)
        | exact absurd rfl (hnd ψ)

/-- **Mint-unblocked, box-negative shape: step soundness.** Mirrors the plain-K box-negative
mint arm inline in the historical monolith's ported body (`FrameSoundness.lean`, the
`neg`/`box φ` case of the "every other shape" branch of `modalStepBranchGen_preserves_satIn`)
verbatim for the fresh-witness pointwise extension `f'` and the base witness/`boxProps`/
`diaNegProps` satisfiability, with one addition: the S4-keyed mint's extra `boxPlusExtraS4 b w`
chunk, closed via `boxPlusExtraS4_sat` (landed earlier this phase) rather than re-derived. -/
lemma modalApplyOneS4Keyed_boxNeg_mint_sat (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ w = none)
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (hFC : s4FC m.r)
    (hInv : accFreshInv b acc)
    (hsfmem : (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hacc : ∀ u v, acc.hasEdge u v → m.r (f u) (f v))
    (hb : ∀ sf ∈ b, sfSat m f sf) :
    ∃ nf, modalApplyOneS4Keyed φ₀ keys (⟨.neg, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear nf, acc.addEdge w (modalNextWorld b)) ∧
      branchSatisfiableIn s4FC (nf ++ b) (acc.addEdge w (modalNextWorld b)) := by
  have hAOeq := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ w hblock
  rw [hAOeq, modalApplyOneS4KeyedMint_boxNeg_eq_S4]
  refine ⟨_, rfl, ?_⟩
  have htrans := hFC.2
  have hnegbox : ¬ Satisfies m (f w) (Proposition.box ψ) := (hb _ hsfmem).2 rfl
  simp only [Satisfies] at hnegbox
  push Not at hnegbox
  obtain ⟨ww, hwwr, hwwψ⟩ := hnegbox
  set w' := modalNextWorld b with hw'def
  let f' : WorldIndex → W := fun n => if n = w' then ww else f n
  refine ⟨W, m, f', hFC, ?_, ?_⟩
  · intro u v hedge
    simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
      Bool.or_eq_true] at hedge
    rcases hedge with hedge | hedge
    · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
      obtain ⟨rfl, rfl⟩ := hedge
      have hw_ne : w ≠ w' := Nat.ne_of_lt (modalNextWorld_gt b _ hsfmem)
      rw [show f' w = f w from if_neg hw_ne, show f' w' = ww from if_pos rfl]
      exact hwwr
    · have huw' : u ≠ w' := by
        intro heq'
        have hfresh := (hInv u v hedge).1
        rw [heq'] at hfresh
        exact Nat.lt_irrefl _ hfresh
      have hvw' : v ≠ w' := by
        intro heq'
        have hfresh := (hInv u v hedge).2
        rw [heq'] at hfresh
        exact Nat.lt_irrefl _ hfresh
      simp only [f', if_neg huw', if_neg hvw']
      exact hacc u v hedge
  · intro sf' hmem'
    simp only [List.mem_append, List.mem_cons] at hmem'
    rcases hmem' with (((rfl | hmem_bp) | hmem_dn) | hmem_bpe) | hmem_old
    · refine ⟨fun h => by simp at h, fun _ => ?_⟩
      simp only [f', if_pos rfl]
      exact hwwψ
    · simp only [List.mem_filterMap] at hmem_bp
      obtain ⟨⟨ψ', src⟩, hpairMem, hsf'_from⟩ := hmem_bp
      split_ifs at hsf'_from with hsrceq hinb
      simp only [Option.some.injEq] at hsf'_from
      subst hsf'_from
      simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
      obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
      split_ifs at hbsfeq with hbsfpos
      cases hbf : bsf.formula with
      | box ψ'' =>
        rw [hbf] at hbsfeq
        simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
        obtain ⟨hψeq, hsrc⟩ := hbsfeq
        have hsrc_w : bsf.label = w := by rw [hsrc]; simpa using hsrceq
        have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
        rw [hbf, hsrc_w] at hbox_sat
        simp only [Satisfies] at hbox_sat
        refine ⟨fun _ => ?_, fun h => by simp at h⟩
        simp only [f', if_pos rfl]
        rw [← hψeq]
        exact hbox_sat ww hwwr
      | _ => simp [hbf] at hbsfeq
    · simp only [List.mem_filterMap] at hmem_dn
      obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
      by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == w) = true
      · rw [if_pos hbsfsign] at hbsfprop
        cases hbf : bsf.formula with
        | diamond ψ'' =>
          simp only [hbf] at hbsfprop
          by_cases hinb :
              (b.any (· == (⟨.neg, ψ'', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                = true
          · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
          · rw [if_neg hinb] at hbsfprop
            simp only [Option.some.injEq] at hbsfprop
            subst hbsfprop
            have hsign : bsf.sign = .neg ∧ bsf.label = w := by
              simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
              exact hbsfsign
            have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
            rw [hbf, hsign.2] at hdiaNeg
            simp only [Satisfies] at hdiaNeg
            push Not at hdiaNeg
            refine ⟨fun h => by simp at h, fun _ => ?_⟩
            simp only [f', if_pos rfl]
            exact hdiaNeg ww hwwr
        | _ => simp [hbf] at hbsfprop
      · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
    · exact boxPlusExtraS4_sat m f htrans b w hb ww hwwr sf' hmem_bpe
    · have hlabel_ne : sf'.label ≠ w' := Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
      have hf'_eq : f' sf'.label = f sf'.label := by simp only [f', if_neg hlabel_ne]
      constructor
      · intro hsign; rw [hf'_eq]; exact (hb sf' hmem_old).1 hsign
      · intro hsign; rw [hf'_eq]; exact (hb sf' hmem_old).2 hsign

/-- **Mint-unblocked, diamond-positive shape: step soundness.** Dual of
`modalApplyOneS4Keyed_boxNeg_mint_sat` -- mirrors the plain-K diamond-positive mint arm inline
in the historical monolith's ported body (`FrameSoundness.lean`, the `pos`/`diamond φ` case),
with the same `boxPlusExtraS4_sat` addition. -/
lemma modalApplyOneS4Keyed_diaPos_mint_sat (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ w = none)
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (hFC : s4FC m.r)
    (hInv : accFreshInv b acc)
    (hsfmem : (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hacc : ∀ u v, acc.hasEdge u v → m.r (f u) (f v))
    (hb : ∀ sf ∈ b, sfSat m f sf) :
    ∃ nf, modalApplyOneS4Keyed φ₀ keys (⟨.pos, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear nf, acc.addEdge w (modalNextWorld b)) ∧
      branchSatisfiableIn s4FC (nf ++ b) (acc.addEdge w (modalNextWorld b)) := by
  have hAOeq := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ w hblock
  rw [hAOeq, modalApplyOneS4KeyedMint_diaPos_eq_S4]
  refine ⟨_, rfl, ?_⟩
  have htrans := hFC.2
  have hposdia : Satisfies m (f w) (Proposition.diamond ψ) := (hb _ hsfmem).1 rfl
  simp only [Satisfies] at hposdia
  obtain ⟨ww, hwwr, hwwψ⟩ := hposdia
  set w' := modalNextWorld b with hw'def
  let f' : WorldIndex → W := fun n => if n = w' then ww else f n
  refine ⟨W, m, f', hFC, ?_, ?_⟩
  · intro u v hedge
    simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
      Bool.or_eq_true] at hedge
    rcases hedge with hedge | hedge
    · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
      obtain ⟨rfl, rfl⟩ := hedge
      have hw_ne : w ≠ w' := Nat.ne_of_lt (modalNextWorld_gt b _ hsfmem)
      rw [show f' w = f w from if_neg hw_ne, show f' w' = ww from if_pos rfl]
      exact hwwr
    · have huw' : u ≠ w' := by
        intro heq'
        have hfresh := (hInv u v hedge).1
        rw [heq'] at hfresh
        exact Nat.lt_irrefl _ hfresh
      have hvw' : v ≠ w' := by
        intro heq'
        have hfresh := (hInv u v hedge).2
        rw [heq'] at hfresh
        exact Nat.lt_irrefl _ hfresh
      simp only [f', if_neg huw', if_neg hvw']
      exact hacc u v hedge
  · intro sf' hmem'
    simp only [List.mem_append, List.mem_cons] at hmem'
    rcases hmem' with (((rfl | hmem_bp) | hmem_dn) | hmem_bpe) | hmem_old
    · refine ⟨fun _ => ?_, fun h => by simp at h⟩
      simp only [f', if_pos rfl]
      exact hwwψ
    · simp only [List.mem_filterMap] at hmem_bp
      obtain ⟨⟨ψ', src⟩, hpairMem, hsf'_from⟩ := hmem_bp
      split_ifs at hsf'_from with hsrceq hinb
      simp only [Option.some.injEq] at hsf'_from
      subst hsf'_from
      simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
      obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
      split_ifs at hbsfeq with hbsfpos
      cases hbf : bsf.formula with
      | box ψ'' =>
        rw [hbf] at hbsfeq
        simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
        obtain ⟨hψeq, hsrc⟩ := hbsfeq
        have hsrc_w : bsf.label = w := by rw [hsrc]; simpa using hsrceq
        have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
        rw [hbf, hsrc_w] at hbox_sat
        simp only [Satisfies] at hbox_sat
        refine ⟨fun _ => ?_, fun h => by simp at h⟩
        simp only [f', if_pos rfl]
        rw [← hψeq]
        exact hbox_sat ww hwwr
      | _ => simp [hbf] at hbsfeq
    · simp only [List.mem_filterMap] at hmem_dn
      obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
      by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == w) = true
      · rw [if_pos hbsfsign] at hbsfprop
        cases hbf : bsf.formula with
        | diamond ψ'' =>
          simp only [hbf] at hbsfprop
          by_cases hinb :
              (b.any (· == (⟨.neg, ψ'', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                = true
          · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
          · rw [if_neg hinb] at hbsfprop
            simp only [Option.some.injEq] at hbsfprop
            subst hbsfprop
            have hsign : bsf.sign = .neg ∧ bsf.label = w := by
              simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
              exact hbsfsign
            have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
            rw [hbf, hsign.2] at hdiaNeg
            simp only [Satisfies] at hdiaNeg
            push Not at hdiaNeg
            refine ⟨fun h => by simp at h, fun _ => ?_⟩
            simp only [f', if_pos rfl]
            exact hdiaNeg ww hwwr
        | _ => simp [hbf] at hbsfprop
      · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
    · exact boxPlusExtraS4_sat m f htrans b w hb ww hwwr sf' hmem_bpe
    · have hlabel_ne : sf'.label ≠ w' := Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
      have hf'_eq : f' sf'.label = f sf'.label := by simp only [f', if_neg hlabel_ne]
      constructor
      · intro hsign; rw [hf'_eq]; exact (hb sf' hmem_old).1 hsign
      · intro hsign; rw [hf'_eq]; exact (hb sf' hmem_old).2 hsign

omit [Hashable Atom] in
/-- `modalApplyOneT`'s own `.fst` at the box-positive shape is always `.notApplicable` or
`.persistent`, never `.linear`/`.branching` -- one layer up from `modalApplyOne_boxPos_eq`
(`Rules.lean`), needed as the outer case-split for `modalApplyOneS4Rules_boxPos_soundIn`'s K+T+4
merge. Lives here (not `LoopChecking.lean`) because it needs `modalApplyOneT_boxPos_fst`
(`TDriver.lean`), which `LoopChecking.lean` does not import. -/
lemma modalApplyOneT_boxPos_eq
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst = .notApplicable ∨
    ∃ out, (modalApplyOneT (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst = .persistent out := by
  rw [modalApplyOneT_boxPos_fst]
  rcases modalApplyOne_boxPos_eq (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
  · rw [hk]
    dsimp only
    split_ifs with hemp
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · rw [hk]
    exact Or.inr ⟨_, rfl⟩

omit [Hashable Atom] in
/-- Dual of `modalApplyOneT_boxPos_eq` for the diamond-negative shape. -/
lemma modalApplyOneT_diaNeg_eq
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst = .notApplicable ∨
    ∃ out, (modalApplyOneT (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst = .persistent out := by
  rw [modalApplyOneT_diamondNeg_fst]
  rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc with hk | ⟨kForms, hk⟩
  · rw [hk]
    dsimp only
    split_ifs with hemp
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · rw [hk]
    exact Or.inr ⟨_, rfl⟩

omit [Hashable Atom] in
/-- **S-boxPos for the S4-keyed guard's 4-rule case, K+T+4 merge.** Frame-relativized semantic
soundness of `modalApplyOneS4Rules`'s box-positive output at `FC := s4FC`. Reuses
`modalApplyOneT_boxPos_soundIn` (above) as a black box for the K+T layers (`hFC.1 : reflFC m.r`
from `s4FC`'s reflexivity conjunct), then splits `RuleResultSat` over the 4-rule's own
`tForms ++ fourNew.filter …` append (`modalApplyOneS4Rules_boxPos_fst`, `LoopChecking.lean`) the
same way `modalApplyOneT_boxPos_soundIn` splits over the T layer's own append: `fourNew`'s
elements (`T(□φ)@w'` for each recorded successor `w'` of `lbl`) are justified by one hop of
`IsTrans` (`hFC.2`) off the recorded edge, mirroring
`branchSatisfiableIn_s4FC_boxPos_trans_mem`/`modalFourBoxProp_sound` (`FrameSoundness.lean`)
inline (those existentially quantify their own witnessing model). -/
theorem modalApplyOneS4Rules_boxPos_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : s4FC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneS4Rules
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc ∧
    RuleResultSat m f (modalApplyOneS4Rules
      (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨-, hRRST⟩ := modalApplyOneT_boxPos_soundIn m f φ lbl b acc hFC.1 hacc hb hmem
  have hFourSat : ∀ x ∈ modalFourBoxProp b acc φ lbl, sfSat m f x := by
    intro x hx
    unfold modalFourBoxProp at hx
    simp only [List.mem_filterMap] at hx
    obtain ⟨w', hw', hxeq⟩ := hx
    by_cases hcase :
        b.any (· == (⟨.pos, .box φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
    · simp [hcase] at hxeq
    · simp only [hcase, Bool.false_eq_true, if_false, Option.some.injEq] at hxeq
      subst hxeq
      have hbox : Satisfies m (f lbl) (.box φ) := (hb _ hmem).1 rfl
      simp only [Satisfies] at hbox
      refine sfSat_pos m f (.box φ) w' ?_
      simp only [Satisfies]
      intro v hv
      exact hbox v (hFC.2.trans (f lbl) (f w') v (hacc lbl w' (mem_successorsOf_hasEdge hw')) hv)
  refine ⟨modalApplyOneS4Rules_boxPos_snd_eq_acc b acc φ lbl, ?_⟩
  rw [modalApplyOneS4Rules_boxPos_fst]
  rcases modalApplyOneT_boxPos_eq b acc φ lbl with ht | ⟨tForms, ht⟩
  · rw [ht] at hRRST ⊢
    dsimp only
    split_ifs with hemp
    · trivial
    · exact hFourSat
  · rw [ht] at hRRST ⊢
    dsimp only
    intro x hx
    simp only [List.mem_append, List.mem_filter] at hx
    rcases hx with hx | ⟨hx, -⟩
    · exact hRRST x hx
    · exact hFourSat x hx

omit [Hashable Atom] in
/-- Dual of `modalApplyOneS4Rules_boxPos_soundIn` for the diamond-negative shape. -/
theorem modalApplyOneS4Rules_diaNeg_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : s4FC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem : (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneS4Rules
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc ∧
    RuleResultSat m f (modalApplyOneS4Rules
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨-, hRRST⟩ := modalApplyOneT_diaNeg_soundIn m f φ lbl b acc hFC.1 hacc hb hmem
  have hFourSat : ∀ x ∈ modalFourDiaNegProp b acc φ lbl, sfSat m f x := by
    intro x hx
    unfold modalFourDiaNegProp at hx
    simp only [List.mem_filterMap] at hx
    obtain ⟨w', hw', hxeq⟩ := hx
    by_cases hcase :
        b.any (· == (⟨.neg, .diamond φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
    · simp [hcase] at hxeq
    · simp only [hcase, Bool.false_eq_true, if_false, Option.some.injEq] at hxeq
      subst hxeq
      have hdianeg : ¬ Satisfies m (f lbl) (.diamond φ) := (hb _ hmem).2 rfl
      refine sfSat_neg m f (.diamond φ) w' ?_
      intro hdia'
      apply hdianeg
      obtain ⟨u, hu, hφu⟩ := Satisfies.diamond_iff.mp hdia'
      exact Satisfies.diamond_iff.mpr
        ⟨u, hFC.2.trans (f lbl) (f w') u (hacc lbl w' (mem_successorsOf_hasEdge hw')) hu, hφu⟩
  refine ⟨modalApplyOneS4Rules_diaNeg_snd_eq_acc b acc φ lbl, ?_⟩
  rw [modalApplyOneS4Rules_diaNeg_fst]
  rcases modalApplyOneT_diaNeg_eq b acc φ lbl with ht | ⟨tForms, ht⟩
  · rw [ht] at hRRST ⊢
    dsimp only
    split_ifs with hemp
    · trivial
    · exact hFourSat
  · rw [ht] at hRRST ⊢
    dsimp only
    intro x hx
    simp only [List.mem_append, List.mem_filter] at hx
    rcases hx with hx | ⟨hx, -⟩
    · exact hRRST x hx
    · exact hFourSat x hx

/-- **4-rule, box-positive shape: step soundness for the S4-keyed guard.** `T(□ψ)@w` never mints
and never touches `acc` (`modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding`, `LoopChecking.lean`).
Bridges `modalApplyOneS4Keyed` down to `modalApplyOneS4Rules` at this shape
(`modalApplyOneS4Keyed_boxPos_eq_S4Rules`, `LoopChecking.lean`, a direct `rfl` since both
`modalApplyOneS4Keyed`'s and `modalApplyOneS4`'s own guard-consulting match arms fail to fire at
`.pos, .box`) and discharges the resulting obligation with `modalApplyOneS4Rules_boxPos_soundIn`
above. The single largest remaining case-split arm of the bespoke S4-keyed step-preservation
lemma. -/
lemma modalApplyOneS4Keyed_boxPos_sat (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex)
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (hFC : s4FC m.r)
    (hacc : ∀ u v, acc.hasEdge u v → m.r (f u) (f v))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneS4Keyed φ₀ keys (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc ∧
    RuleResultSat m f (modalApplyOneS4Keyed φ₀ keys (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  rw [modalApplyOneS4Keyed_boxPos_eq_S4Rules]
  exact modalApplyOneS4Rules_boxPos_soundIn m f ψ w b acc hFC hacc hb hmem

/-- Dual of `modalApplyOneS4Keyed_boxPos_sat` for the diamond-negative shape (`F(◇ψ)@w`). -/
lemma modalApplyOneS4Keyed_diaNeg_sat (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex)
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (hFC : s4FC m.r)
    (hacc : ∀ u v, acc.hasEdge u v → m.r (f u) (f v))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneS4Keyed φ₀ keys (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc ∧
    RuleResultSat m f (modalApplyOneS4Keyed φ₀ keys (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  rw [modalApplyOneS4Keyed_diaNeg_eq_S4Rules]
  exact modalApplyOneS4Rules_diaNeg_soundIn m f ψ w b acc hFC hacc hb hmem

/-! ## Probe P1/P2 (CONDITIONAL-GO Preconditions) -- The Reformulated Redirect-Sound Invariant

Per report `reports/06_mint-blocked-redirect-verdict.md`
(`specs/553_s4_loop_guard_soundness_reachability_restriction/`), the literal per-step statement
of redirect preservation (demanding the model realize the redirect edge itself, as
`branchSatisfiableIn_s4FC_addEdge_of_blocked` above does at the capstone level) is not closable
as a PER-STEP obligation: the capstone needs `modalHintikkaSetS4`, whose conjuncts 3/4
(unwitnessed sibling mint shapes) are not available before the tableau closes. `S4RedirectSoundInv`
below is the report's reformulated conserved predicate: it quarantines redirect edges from the
semantic edge-realization conjunct (weakened to "every recorded edge is either a ghost redirect
edge or genuinely realized") and justifies each ghost edge purely syntactically (payload
absorption, via the already-landed free transfers) plus a frozenness/exhaustion conjunct.

This section closes probe P1 (state the predicate, close the mint-blocked arm alone) using ONLY
already-landed sorry-free lemmas from this file and `LoopChecking.lean`, plus the two small NEW
lemmas below (`modalApplyOneS4Rules_{boxPos,diaNeg}_notApplicable_of_saturated`) --
`modalS4Saturated`'s own filtered-construction argument, needed for conjunct (d) at the redirect
source, which the report names as the arm's one open piece ("persistent applicability is
unchanged by adding an edge whose payload is already present"). -/

/-- **New lemma (probe P1).** Every candidate output element `boxPropagation`/`modalTBoxSelf`/
`modalFourBoxProp` could still contribute at a box-positive persistent shape is, BY CONSTRUCTION,
NOT already on `b` (each of the three layers filters its own output against `b` before emitting
it, and merging/deduplication only ever removes elements, never introduces new ones). Combined
with `modalS4Saturated`'s demand that every output of an applicable (`.persistent`) rule is
already on `b`, an applicable result is self-contradictory (its list is provably both nonempty
and, elementwise, both `∈ b` and `∉ b`), so the result must be `.notApplicable`. -/
lemma modalApplyOneS4Rules_boxPos_notApplicable_of_saturated (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSat : modalS4Saturated φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneS4Rules (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst = .notApplicable := by
  have hcond := hSat _ hmem
  have hshape : modalApplyOneS4 φ₀ (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc =
      modalApplyOneS4Rules (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond ⊢
  simp only at hcond ⊢
  have hK : (modalApplyOne (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      if (boxPropagation b acc ψ w).isEmpty then RuleResult.notApplicable
      else RuleResult.persistent (boxPropagation b acc ψ w) := by
    unfold modalApplyOne
    simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
      modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
    split_ifs <;> simp_all
  have htR : (modalApplyOneT (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOne (⟨.pos, .box ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | .persistent kForms =>
          RuleResult.persistent
            (kForms ++ (modalTBoxSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
        | .notApplicable =>
          if (modalTBoxSelf b ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalTBoxSelf b ψ w)
        | other => other) := by
    unfold modalApplyOneT
    obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases kResult <;> first | rfl | (simp only []; split <;> rfl)
  rw [htR, hK] at hcond ⊢
  have hBoxNotMem : ∀ x ∈ boxPropagation b acc ψ w, x ∉ b := by
    intro x hx
    unfold boxPropagation at hx
    simp only [List.mem_filterMap] at hx
    obtain ⟨w', -, heq⟩ := hx
    split_ifs at heq with hin
    simp only [Option.some.injEq] at heq
    subst heq
    simpa using hin
  have hSelfNotMem : ∀ x ∈ modalTBoxSelf b ψ w, x ∉ b := by
    intro x hx
    by_cases hin : ((b.any fun y => y == (⟨.pos, ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex)) = true)
    · rw [modalTBoxSelf, if_pos hin] at hx
      simp at hx
    · rw [modalTBoxSelf, if_neg hin] at hx
      simp only [List.mem_singleton] at hx
      subst hx
      simpa using hin
  have hFourNotMem : ∀ x ∈ modalFourBoxProp b acc ψ w, x ∉ b := by
    intro x hx
    unfold modalFourBoxProp at hx
    simp only [List.mem_filterMap] at hx
    obtain ⟨w', -, heq⟩ := hx
    split_ifs at heq with hin
    simp only [Option.some.injEq] at heq
    subst heq
    simpa using hin
  split_ifs at hcond ⊢ with h1 h2 h3 <;> simp only [] at hcond ⊢ <;>
    first
    | rfl
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h1)
       exact hBoxNotMem x hx (hcond x (by simp [hx])))
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h2)
       exact hSelfNotMem x hx (hcond x (by simp [hx])))
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h3)
       exact hFourNotMem x hx (hcond x (by simp [hx])))

/-- Dual of `modalApplyOneS4Rules_boxPos_notApplicable_of_saturated` for the diamond-negative
shape. -/
lemma modalApplyOneS4Rules_diaNeg_notApplicable_of_saturated (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSat : modalS4Saturated φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneS4Rules (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst = .notApplicable := by
  have hcond := hSat _ hmem
  have hshape : modalApplyOneS4 φ₀ (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc =
      modalApplyOneS4Rules (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond ⊢
  simp only at hcond ⊢
  set diaPropagation : List (SignedFormula (Proposition Atom) WorldIndex) :=
    (acc.successorsOf w).filterMap (fun w' =>
      let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
      if b.any (· == sf') then none else some sf') with hDiaPropDef
  have hK : (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      if diaPropagation.isEmpty
      then RuleResult.notApplicable
      else RuleResult.persistent diaPropagation := by
    unfold modalApplyOne
    simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
      modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none, hDiaPropDef]
    split_ifs <;> simp_all
  have htR : (modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | .persistent kForms =>
          RuleResult.persistent
            (kForms ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
        | .notApplicable =>
          if (modalTDiaNegSelf b ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalTDiaNegSelf b ψ w)
        | other => other) := by
    unfold modalApplyOneT
    obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases kResult <;> first | rfl | (simp only []; split <;> rfl)
  rw [htR, hK] at hcond ⊢
  have hDiaNotMem : ∀ x ∈ diaPropagation, x ∉ b := by
    intro x hx
    rw [hDiaPropDef] at hx
    simp only [List.mem_filterMap] at hx
    obtain ⟨w', -, heq⟩ := hx
    split_ifs at heq with hin
    simp only [Option.some.injEq] at heq
    subst heq
    simpa using hin
  have hSelfNotMem : ∀ x ∈ modalTDiaNegSelf b ψ w, x ∉ b := by
    intro x hx
    by_cases hin : ((b.any fun y => y == (⟨.neg, ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex)) = true)
    · rw [modalTDiaNegSelf, if_pos hin] at hx
      simp at hx
    · rw [modalTDiaNegSelf, if_neg hin] at hx
      simp only [List.mem_singleton] at hx
      subst hx
      simpa using hin
  have hFourNotMem : ∀ x ∈ modalFourDiaNegProp b acc ψ w, x ∉ b := by
    intro x hx
    unfold modalFourDiaNegProp at hx
    simp only [List.mem_filterMap] at hx
    obtain ⟨w', -, heq⟩ := hx
    split_ifs at heq with hin
    simp only [Option.some.injEq] at heq
    subst heq
    simpa using hin
  split_ifs at hcond ⊢ with h1 h2 h3 <;> simp only [] at hcond ⊢ <;>
    first
    | rfl
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h1)
       exact hDiaNotMem x hx (hcond x (by simp [hx])))
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h2)
       exact hSelfNotMem x hx (hcond x (by simp [hx])))
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h3)
       exact hFourNotMem x hx (hcond x (by simp [hx])))

/-! ## Probe P1 -- The Reformulated Conserved Predicate and the Mint-Blocked Arm

Report §3.2's `S4RedirectSoundInv`, transcribed against this file's actual vocabulary
(`s4FC`, `branchSatisfiableIn`'s edge/satisfaction conjuncts, `sfSat`). `Er` is a proof-level
ghost list of redirect-created edges: never computed by the driver, only threaded through the
soundness induction that will eventually consume this predicate. -/

/-- **Reformulated conserved predicate (probe P1, report §3.2).** Conjunct (a): every ghost
edge is recorded in `acc`. Conjunct (b): a model witness exists that satisfies the frame
condition and every branch formula, and realizes every recorded edge EXCEPT possibly the ghost
ones (the semantic conjunct, weakened relative to `branchSatisfiableIn`). Conjunct (c): every
ghost edge's payload is already syntactically absorbed at the target (one-hop, both unwrapped
and boxed forms -- the report's payload-absorption conjunct). Conjunct (d): every out-edged,
non-mint-shaped branch formula is either already expanded or has no applicable rule --
frozenness/exhaustion, protecting (c)'s absorption from being invalidated by a later step. -/
def S4RedirectSoundInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (Er : List (WorldIndex × WorldIndex)) : Prop :=
  (∀ p ∈ Er, acc.hasEdge p.1 p.2 = true) ∧
  (∃ (W : Type) (m : Model W Atom) (f : WorldIndex → W),
     s4FC m.r ∧
     (∀ w w', acc.hasEdge w w' → (w, w') ∈ Er ∨ m.r (f w) (f w')) ∧
     ∀ sf ∈ b, sfSat m f sf) ∧
  (∀ p ∈ Er, ∀ χ : Proposition Atom,
     ((⟨.pos, .box χ, p.1⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
       (⟨.pos, χ, p.2⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b ∧
       (⟨.pos, .box χ, p.2⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) ∧
     ((⟨.neg, .diamond χ, p.1⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
       (⟨.neg, χ, p.2⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b ∧
       (⟨.neg, .diamond χ, p.2⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)) ∧
  (∀ sf ∈ b, modalMintShape sf = false → outDeg acc sf.label ≠ 0 →
     sf ∈ e ∨ (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable)

/-- **Probe P1: the mint-blocked (box-negative) arm closes.** Given `S4RedirectSoundInv` at
`(b, e, acc, keys, Er)`, `modalS4Saturated` at `acc` (obtainable from mint-readiness via
`modalS4Saturated_of_ordered_settled`, not re-derived here -- this arm lemma is stated the same
way the file's other Phase 7 arms are, taking their local hypotheses directly rather than
re-deriving the whole driver induction), settledness `hmint` (mint-readiness, obtainable via
`modalStepBranchS4KeyedOrdered_mintReady` at the real driver call site), and a keyed-guard block
decision at the box-negative mint shape, extending `Er` with the new redirect edge
`(src, wBlock)` and `acc` with `acc.addEdge src wBlock` preserves `S4RedirectSoundInv`.

Closes (a) mechanically, (b) with the SAME model witness (no surgery -- the new edge is exempted
by the `Er'` disjunct), (c) via the already-landed free transfer `blockedRedirect_boxed_
{boxPos,diaNeg}_mem` plus the T-self bridges `hintikkaS4_{box_pos,dia_neg}_self` (avoiding the
unwrapped free transfer's own separate relevance side condition), and (d) via the already-landed
`modalS4Saturated_addEdge_of_blocked` composed with the two new lemmas
`modalApplyOneS4Rules_{boxPos,diaNeg}_notApplicable_of_saturated` above -- NO new semantic
content is needed for (d) beyond those two small lemmas, confirming the report's "one small new
lemma" estimate (probe verdict: P1 PASS). -/
theorem S4RedirectSoundInv_boxNeg_blocked (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (Er : List (WorldIndex × WorldIndex))
    (src wBlock : WorldIndex) (φ : Proposition Atom)
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er)
    (hUniv : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hSat : modalS4Saturated φ₀ b acc)
    (hmint : modalNonMintCandidates φ₀ keys b e acc = [])
    (hblock : blockingWorldS4Keyed φ₀ b keys .neg φ src = some wBlock) :
    S4RedirectSoundInv φ₀ b e (acc.addEdge src wBlock) keys ((src, wBlock) :: Er) := by
  obtain ⟨ha, hbSem, hc, -⟩ := hinv
  have hSat' : modalS4Saturated φ₀ b (acc.addEdge src wBlock) :=
    modalS4Saturated_addEdge_of_blocked φ₀ b acc keys .neg φ src wBlock hSat hUniv hkL hblock
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a) every ghost edge is a recorded edge in the extended `acc`.
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hasEdge_addEdge_self_gate0 acc src wBlock
    · exact hasEdge_addEdge_mono_gate0 (ha p hp)
  · -- (b) semantic conjunct: the SAME model witnesses it, no extension needed.
    obtain ⟨W, m, f, hFC, hrel, hb⟩ := hbSem
    refine ⟨W, m, f, hFC, ?_, hb⟩
    intro w w' hedge
    rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
    · exact Or.inl (by simp)
    · rcases hrel w w' hold with hmem | hr
      · exact Or.inl (by simp [hmem])
      · exact Or.inr hr
  · -- (c) syntactic absorption at the new ghost edge, plus inherited old edges.
    intro p hp χ
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · refine ⟨?_, ?_⟩
      · intro hmemBox
        have hsigsub : (Sign.pos, .box χ) ∈ signedSubfmls φ₀ :=
          mem_signedSubfmls_of_formula_s4loop .pos (modalUniverseS4_mem_formula (hUniv _ hmemBox))
        have hboxedWB : (⟨.pos, .box χ, wBlock⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
          blockedRedirect_boxed_boxPos_mem φ₀ b keys .neg φ src wBlock hkL hblock χ hsigsub
            hmemBox
        exact ⟨hintikkaS4_box_pos_self φ₀ b acc hSat χ wBlock hboxedWB, hboxedWB⟩
      · intro hmemDia
        have hsigsub : (Sign.neg, .diamond χ) ∈ signedSubfmls φ₀ :=
          mem_signedSubfmls_of_formula_s4loop .neg
            (modalUniverseS4_mem_formula (hUniv _ hmemDia))
        have hboxedWB : (⟨.neg, .diamond χ, wBlock⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
          blockedRedirect_boxed_diaNeg_mem φ₀ b keys .neg φ src wBlock hkL hblock χ hsigsub
            hmemDia
        exact ⟨hintikkaS4_dia_neg_self φ₀ b acc hSat χ wBlock hboxedWB, hboxedWB⟩
    · exact hc p hp χ
  · -- (d) frozenness/exhaustion, at the extended `acc`.
    intro sf hsfmem hshape _houtdeg
    have hOld := (modalNonMintCandidates_eq_nil_iff φ₀ keys b e acc).mp hmint sf hsfmem
    rcases hOld with hms | he | hna
    · exact absurd hms (by simp [hshape])
    · exact Or.inl he
    · right
      by_cases hbd : (sf.sign = .pos ∧ ∃ χ, sf.formula = .box χ) ∨
          (sf.sign = .neg ∧ ∃ χ, sf.formula = .diamond χ)
      · rcases hbd with ⟨hs, χ, hf⟩ | ⟨hs, χ, hf⟩
        · have hsfeq : sf = (⟨.pos, .box χ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) := by
            rcases sf with ⟨s', f', w'⟩; simp_all
          rw [hsfeq, modalApplyOneS4Keyed_boxPos_eq_S4Rules]
          exact modalApplyOneS4Rules_boxPos_notApplicable_of_saturated φ₀ b
            (acc.addEdge src wBlock) hSat' χ sf.label (hsfeq ▸ hsfmem)
        · have hsfeq : sf = (⟨.neg, .diamond χ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) := by
            rcases sf with ⟨s', f', w'⟩; simp_all
          rw [hsfeq, modalApplyOneS4Keyed_diaNeg_eq_S4Rules]
          exact modalApplyOneS4Rules_diaNeg_notApplicable_of_saturated φ₀ b
            (acc.addEdge src wBlock) hSat' χ sf.label (hsfeq ▸ hsfmem)
      · have hnb : ∀ χ, sf.formula ≠ .box χ := by
          intro χ hfeq
          apply hbd
          rcases hs : sf.sign with _ | _
          · exact Or.inl ⟨rfl, χ, hfeq⟩
          · exact absurd hshape (by
              rcases sf with ⟨s', f', w'⟩
              simp_all [modalMintShape])
        have hnd : ∀ χ, sf.formula ≠ .diamond χ := by
          intro χ hfeq
          apply hbd
          rcases hs : sf.sign with _ | _
          · exact absurd hshape (by
              rcases sf with ⟨s', f', w'⟩
              simp_all [modalMintShape])
          · exact Or.inr ⟨rfl, χ, hfeq⟩
        have hna' : (modalApplyOne sf b acc).1 = .notApplicable := by
          rwa [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf.sign sf.formula
            sf.label hnb hnd b acc, show (⟨sf.sign, sf.formula, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) = sf from rfl] at hna
        have hfsteq : (modalApplyOne sf b (acc.addEdge src wBlock)).fst =
            (modalApplyOne sf b acc).fst :=
          modalApplyOne_fst_eq_of_not_boxPos_diaNeg sf b (acc.addEdge src wBlock) acc
            (not_or.mp hbd)
        rw [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf.sign sf.formula sf.label
          hnb hnd b (acc.addEdge src wBlock), show (⟨sf.sign, sf.formula, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) = sf from rfl, hfsteq]
        exact hna'

/-- **Phase 7.3: the diamond-positive mint-blocked arm.** Literal mirror of
`S4RedirectSoundInv_boxNeg_blocked`, for a keyed-guard block decision triggered by a
diamond-positive mint attempt (`T(◇φ)@src` blocked, guard call
`blockingWorldS4Keyed φ₀ b keys .pos φ src`). Every discharge is the same argument as the
box-negative theorem: (a) mechanical; (b) the SAME model witness, no surgery; (c) via the
identical free transfers `blockedRedirect_boxed_{boxPos,diaNeg}_mem` plus the T-self bridges
`hintikkaS4_{box_pos,dia_neg}_self` -- conjunct (c) quantifies over BOTH payload shapes
regardless of which mint shape triggered the block, so the same two calls appear here as in the
box-negative theorem; (d) via `modalS4Saturated_addEdge_of_blocked` (already stated for a
general guard sign `s`, confirmed by inspection: it accepts `s := .pos` with no additional
hypothesis) composed with the same two `notApplicable_of_saturated` lemmas. The only textual
delta from `S4RedirectSoundInv_boxNeg_blocked` is `hblock`'s sign argument and the sign passed to
`modalS4Saturated_addEdge_of_blocked`. -/
theorem S4RedirectSoundInv_diaPos_blocked (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (Er : List (WorldIndex × WorldIndex))
    (src wBlock : WorldIndex) (φ : Proposition Atom)
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er)
    (hUniv : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hSat : modalS4Saturated φ₀ b acc)
    (hmint : modalNonMintCandidates φ₀ keys b e acc = [])
    (hblock : blockingWorldS4Keyed φ₀ b keys .pos φ src = some wBlock) :
    S4RedirectSoundInv φ₀ b e (acc.addEdge src wBlock) keys ((src, wBlock) :: Er) := by
  obtain ⟨ha, hbSem, hc, -⟩ := hinv
  have hSat' : modalS4Saturated φ₀ b (acc.addEdge src wBlock) :=
    modalS4Saturated_addEdge_of_blocked φ₀ b acc keys .pos φ src wBlock hSat hUniv hkL hblock
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a) every ghost edge is a recorded edge in the extended `acc`.
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hasEdge_addEdge_self_gate0 acc src wBlock
    · exact hasEdge_addEdge_mono_gate0 (ha p hp)
  · -- (b) semantic conjunct: the SAME model witnesses it, no extension needed.
    obtain ⟨W, m, f, hFC, hrel, hb⟩ := hbSem
    refine ⟨W, m, f, hFC, ?_, hb⟩
    intro w w' hedge
    rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
    · exact Or.inl (by simp)
    · rcases hrel w w' hold with hmem | hr
      · exact Or.inl (by simp [hmem])
      · exact Or.inr hr
  · -- (c) syntactic absorption at the new ghost edge, plus inherited old edges.
    intro p hp χ
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · refine ⟨?_, ?_⟩
      · intro hmemBox
        have hsigsub : (Sign.pos, .box χ) ∈ signedSubfmls φ₀ :=
          mem_signedSubfmls_of_formula_s4loop .pos (modalUniverseS4_mem_formula (hUniv _ hmemBox))
        have hboxedWB : (⟨.pos, .box χ, wBlock⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
          blockedRedirect_boxed_boxPos_mem φ₀ b keys .pos φ src wBlock hkL hblock χ hsigsub
            hmemBox
        exact ⟨hintikkaS4_box_pos_self φ₀ b acc hSat χ wBlock hboxedWB, hboxedWB⟩
      · intro hmemDia
        have hsigsub : (Sign.neg, .diamond χ) ∈ signedSubfmls φ₀ :=
          mem_signedSubfmls_of_formula_s4loop .neg
            (modalUniverseS4_mem_formula (hUniv _ hmemDia))
        have hboxedWB : (⟨.neg, .diamond χ, wBlock⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
          blockedRedirect_boxed_diaNeg_mem φ₀ b keys .pos φ src wBlock hkL hblock χ hsigsub
            hmemDia
        exact ⟨hintikkaS4_dia_neg_self φ₀ b acc hSat χ wBlock hboxedWB, hboxedWB⟩
    · exact hc p hp χ
  · -- (d) frozenness/exhaustion, at the extended `acc`.
    intro sf hsfmem hshape _houtdeg
    have hOld := (modalNonMintCandidates_eq_nil_iff φ₀ keys b e acc).mp hmint sf hsfmem
    rcases hOld with hms | he | hna
    · exact absurd hms (by simp [hshape])
    · exact Or.inl he
    · right
      by_cases hbd : (sf.sign = .pos ∧ ∃ χ, sf.formula = .box χ) ∨
          (sf.sign = .neg ∧ ∃ χ, sf.formula = .diamond χ)
      · rcases hbd with ⟨hs, χ, hf⟩ | ⟨hs, χ, hf⟩
        · have hsfeq : sf = (⟨.pos, .box χ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) := by
            rcases sf with ⟨s', f', w'⟩; simp_all
          rw [hsfeq, modalApplyOneS4Keyed_boxPos_eq_S4Rules]
          exact modalApplyOneS4Rules_boxPos_notApplicable_of_saturated φ₀ b
            (acc.addEdge src wBlock) hSat' χ sf.label (hsfeq ▸ hsfmem)
        · have hsfeq : sf = (⟨.neg, .diamond χ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) := by
            rcases sf with ⟨s', f', w'⟩; simp_all
          rw [hsfeq, modalApplyOneS4Keyed_diaNeg_eq_S4Rules]
          exact modalApplyOneS4Rules_diaNeg_notApplicable_of_saturated φ₀ b
            (acc.addEdge src wBlock) hSat' χ sf.label (hsfeq ▸ hsfmem)
      · have hnb : ∀ χ, sf.formula ≠ .box χ := by
          intro χ hfeq
          apply hbd
          rcases hs : sf.sign with _ | _
          · exact Or.inl ⟨rfl, χ, hfeq⟩
          · exact absurd hshape (by
              rcases sf with ⟨s', f', w'⟩
              simp_all [modalMintShape])
        have hnd : ∀ χ, sf.formula ≠ .diamond χ := by
          intro χ hfeq
          apply hbd
          rcases hs : sf.sign with _ | _
          · exact absurd hshape (by
              rcases sf with ⟨s', f', w'⟩
              simp_all [modalMintShape])
          · exact Or.inr ⟨rfl, χ, hfeq⟩
        have hna' : (modalApplyOne sf b acc).1 = .notApplicable := by
          rwa [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf.sign sf.formula
            sf.label hnb hnd b acc, show (⟨sf.sign, sf.formula, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) = sf from rfl] at hna
        have hfsteq : (modalApplyOne sf b (acc.addEdge src wBlock)).fst =
            (modalApplyOne sf b acc).fst :=
          modalApplyOne_fst_eq_of_not_boxPos_diaNeg sf b (acc.addEdge src wBlock) acc
            (not_or.mp hbd)
        rw [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf.sign sf.formula sf.label
          hnb hnd b (acc.addEdge src wBlock), show (⟨sf.sign, sf.formula, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) = sf from rfl, hfsteq]
        exact hna'

/-! ## Phase 7.4: Antitone-Applicability Lemma Family (P2 Formalized)

Conjunct (d) of `S4RedirectSoundInv` needs `(modalApplyOneS4Keyed φ₀ keys sf b acc).1 =
.notApplicable` to survive a primary-scan step's branch growth (`b ↦ nf ++ b`), where
`hmint`/mint-readiness (the hypothesis `S4RedirectSoundInv_boxNeg_blocked`/`_diaPos_blocked`
use) is unavailable. Every rule layer (propositional, K, T-self, S4 4-rule) filters its own
output against the CURRENT branch `b` before emitting anything, so growing `b` can only filter
out MORE candidates, never fewer -- this is the antitone-applicability property, formalized
below as a small family culminating in `modalApplyOneS4Keyed_notApplicable_growth`. -/

omit [Hashable Atom] in
/-- **Generic branch-growth antitone fact** for the `filterMap`-over-successors shape shared by
`boxPropagation`, the diamond-negative K rule's inline propagation, and the two S4 4-rule
helpers `modalFourBoxProp`/`modalFourDiaNegProp`: if every element of `l` is filtered out
against the guard list `b` (producing `[]`), it stays filtered out against any branch
extension `nf ++ b`. `List.any_append` is the load-bearing fact: the guard can only become MORE
true as the branch grows, never less. -/
lemma filterMap_any_guard_isEmpty_growth
    (l : List WorldIndex) (g : WorldIndex → SignedFormula (Proposition Atom) WorldIndex)
    (nf b : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : l.filterMap (fun w' => if b.any (· == g w') then none else some (g w')) = []) :
    l.filterMap (fun w' => if (nf ++ b).any (· == g w') then none else some (g w')) = [] := by
  rw [List.filterMap_eq_nil_iff] at h ⊢
  intro w' hw'
  have hguard := h w' hw'
  by_cases hcond : b.any (· == g w') = true
  · rw [List.any_append, hcond]; simp
  · rw [if_neg hcond] at hguard
    exact absurd hguard (by simp)

omit [Hashable Atom] in
/-- Branch-growth antitone fact for the T self-propagation helpers `modalTBoxSelf`/
`modalTDiaNegSelf`: a single-element `if b.any (· == sf) then [] else [sf]` guard, which shares
the same monotone-guard argument as `filterMap_any_guard_isEmpty_growth` but does not need
`filterMap` at all. -/
lemma modalTSelf_isEmpty_growth
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (nf b : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : (if b.any (· == sf) then ([] : List (SignedFormula (Proposition Atom) WorldIndex))
          else [sf]) = []) :
    (if (nf ++ b).any (· == sf) then ([] : List (SignedFormula (Proposition Atom) WorldIndex))
     else [sf]) = [] := by
  by_cases hcond : b.any (· == sf) = true
  · rw [List.any_append, hcond]; simp
  · rw [if_neg hcond] at h
    exact absurd h (by simp)

/-- **Branch-growth antitone, box-positive shape.** If `modalApplyOneS4Rules` is
`.notApplicable` at `⟨.pos, .box ψ, w⟩` given `(b, acc)`, it stays `.notApplicable` at any
branch extension `nf ++ b` (same `acc`): all three layers' candidate lists
(`boxPropagation`/`modalTBoxSelf`/`modalFourBoxProp`) can only shrink as `b` grows. Any
`φ₀`-witness works in the intermediate `modalApplyOneS4` bridge -- box-positive never consults
the guard, so the choice is immaterial; `ψ` itself is reused for convenience. -/
lemma modalApplyOneS4Rules_boxPos_notApplicable_growth
    (b nf : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex)
    (h : (modalApplyOneS4Rules (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).1 = .notApplicable) :
    (modalApplyOneS4Rules (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) (nf ++ b) acc).1 = .notApplicable := by
  have hshape : ∀ β : List (SignedFormula (Proposition Atom) WorldIndex),
      modalApplyOneS4 ψ (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) β acc =
      modalApplyOneS4Rules (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) β acc := fun β =>
    modalApplyOneS4_eq_of_not_boxNeg_diaPos ψ _ β acc ⟨by simp, by simp⟩
  have hbig_b := modalApplyOneS4_boxPos_fst_eq ψ b acc ψ w
  have hbig_nf := modalApplyOneS4_boxPos_fst_eq ψ (nf ++ b) acc ψ w
  rw [hshape b] at hbig_b
  rw [hshape (nf ++ b)] at hbig_nf
  rw [hbig_b] at h
  rw [hbig_nf]
  by_cases h1 : (boxPropagation b acc ψ w).isEmpty = true
  · by_cases h2 : (modalTBoxSelf b ψ w).isEmpty = true
    · by_cases h3 : (modalFourBoxProp b acc ψ w).isEmpty = true
      · have hnil1 : boxPropagation (nf ++ b) acc ψ w = [] :=
          filterMap_any_guard_isEmpty_growth (acc.successorsOf w)
            (fun w' => (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)) nf b
            (List.isEmpty_iff.mp h1)
        have hnil2 : modalTBoxSelf (nf ++ b) ψ w = [] :=
          modalTSelf_isEmpty_growth (⟨.pos, ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) nf b (List.isEmpty_iff.mp h2)
        have hnil3 : modalFourBoxProp (nf ++ b) acc ψ w = [] :=
          filterMap_any_guard_isEmpty_growth (acc.successorsOf w)
            (fun w' => (⟨.pos, .box ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)) nf b
            (List.isEmpty_iff.mp h3)
        simp [hnil1, hnil2, hnil3]
      · simp [h1, h2, h3] at h
    · simp [h1, h2] at h
  · simp [h1] at h

/-- Dual of `modalApplyOneS4Rules_boxPos_notApplicable_growth` for the diamond-negative shape
`F(◇ψ)@w`. The K layer's candidate list has no separately-named `def` (unlike `boxPropagation`,
matching `modalApplyOneS4_diaNeg_fst_eq`'s own inline spelling), so it is written out directly
here rather than via a helper `def`. -/
lemma modalApplyOneS4Rules_diaNeg_notApplicable_growth
    (b nf : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex)
    (h : (modalApplyOneS4Rules (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).1 = .notApplicable) :
    (modalApplyOneS4Rules (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) (nf ++ b) acc).1 = .notApplicable := by
  have hshape : ∀ β : List (SignedFormula (Proposition Atom) WorldIndex),
      modalApplyOneS4 ψ (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) β acc =
      modalApplyOneS4Rules (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) β acc := fun β =>
    modalApplyOneS4_eq_of_not_boxNeg_diaPos ψ _ β acc ⟨by simp, by simp⟩
  have hbig_b := modalApplyOneS4_diaNeg_fst_eq ψ b acc ψ w
  have hbig_nf := modalApplyOneS4_diaNeg_fst_eq ψ (nf ++ b) acc ψ w
  rw [hshape b] at hbig_b
  rw [hshape (nf ++ b)] at hbig_nf
  rw [hbig_b] at h
  rw [hbig_nf]
  by_cases h1 : ((acc.successorsOf w).filterMap fun u =>
      let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
      if b.any (· == sf') then none else some sf').isEmpty = true
  · by_cases h2 : (modalTDiaNegSelf b ψ w).isEmpty = true
    · by_cases h3 : (modalFourDiaNegProp b acc ψ w).isEmpty = true
      · have hnil1e : ((acc.successorsOf w).filterMap fun u =>
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
            if (nf ++ b).any (· == sf') then none else some sf').isEmpty = true :=
          List.isEmpty_iff.mpr (filterMap_any_guard_isEmpty_growth (acc.successorsOf w)
            (fun u => (⟨.neg, ψ, u⟩ : SignedFormula (Proposition Atom) WorldIndex)) nf b
            (List.isEmpty_iff.mp h1))
        have hnil2e : (modalTDiaNegSelf (nf ++ b) ψ w).isEmpty = true :=
          List.isEmpty_iff.mpr (modalTSelf_isEmpty_growth (⟨.neg, ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) nf b (List.isEmpty_iff.mp h2))
        have hnil3e : (modalFourDiaNegProp (nf ++ b) acc ψ w).isEmpty = true :=
          List.isEmpty_iff.mpr (filterMap_any_guard_isEmpty_growth (acc.successorsOf w)
            (fun w' => (⟨.neg, .diamond ψ, w'⟩ :
              SignedFormula (Proposition Atom) WorldIndex)) nf b (List.isEmpty_iff.mp h3))
        simp only [hnil1e, hnil2e, hnil3e, if_true]
      · rw [if_pos h1, if_pos h2, if_neg h3] at h; simp at h
    · rw [if_pos h1, if_neg h2] at h; simp at h
  · rw [if_neg h1] at h; simp at h

omit [Hashable Atom] in
/-- **Branch-independence for non-box/non-diamond formulas.** `modalApplyOne`'s `.fst` is
entirely independent of `b` when `sf`'s formula is neither `.box` nor `.diamond`: the
propositional-rule branch depends only on `sf`, and the K modal match's catch-all arm
(`| _, _ => .notApplicable`) is a literal constant. Companion to
`modalApplyOne_fst_eq_of_not_boxPos_diaNeg` (which varies `acc` at the two 4-rule/T-relevant
shapes); this one varies `b` at every shape except the four box/diamond arms (mint and
persistent alike), since the two MINT shapes' `.fst` payload (fresh-world witness content) does
genuinely depend on `b`. -/
lemma modalApplyOne_fst_eq_of_not_box_diamond
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b1 b2 : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hnb : ∀ ψ, sf.formula ≠ .box ψ) (hnd : ∀ ψ, sf.formula ≠ .diamond ψ) :
    (modalApplyOne sf b1 acc).fst = (modalApplyOne sf b2 acc).fst := by
  unfold modalApplyOne
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp_all [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?,
      List.map, List.find?, RuleResult.isApplicable, Option.getD_none]

/-- **The assembled branch-growth antitone statement (Phase 7.4's target, report §6/P2).**
`(modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable` survives any branch extension
`b ↦ nf ++ b` (same `acc`), for EVERY signed-formula shape `sf`, not only the non-mint
candidates `S4RedirectSoundInv`'s conjunct (d) actually needs. The two mint shapes
(`F(□χ)@w`, `T(◇χ)@w`) are closed vacuously -- `modalApplyOneS4Keyed` always returns `.linear`
there (blocked: `.linear []`; unblocked:
`modalApplyOneS4KeyedMint`, whose `.fst` is `modalApplyOne`'s own `.linear` result with
`boxPlusExtraS4` appended, per `modalApplyOneS4KeyedMint_fst_eq_or_linear`), so the hypothesis
`.1 = .notApplicable` never holds there in the first place. The two persistent modal shapes
(box-positive, diamond-negative) route through `modalApplyOneS4Rules_boxPos_notApplicable_growth`
/`_diaNeg_notApplicable_growth`; every other shape (propositional/atomic) routes through
`modalApplyOne_fst_eq_of_not_box_diamond`, which is branch-INDEPENDENT there, a fortiori
antitone. -/
lemma modalApplyOneS4Keyed_notApplicable_growth (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b nf : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable) :
    (modalApplyOneS4Keyed φ₀ keys sf (nf ++ b) acc).1 = .notApplicable := by
  by_cases hbd : (sf.sign = .pos ∧ ∃ χ, sf.formula = .box χ) ∨
      (sf.sign = .neg ∧ ∃ χ, sf.formula = .diamond χ)
  · rcases hbd with ⟨hs, χ, hf⟩ | ⟨hs, χ, hf⟩
    · have hsfeq : sf = (⟨.pos, .box χ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by
        rcases sf with ⟨s', f', w'⟩; simp_all
      rw [hsfeq, modalApplyOneS4Keyed_boxPos_eq_S4Rules] at h ⊢
      exact modalApplyOneS4Rules_boxPos_notApplicable_growth b nf acc χ sf.label h
    · have hsfeq : sf = (⟨.neg, .diamond χ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by
        rcases sf with ⟨s', f', w'⟩; simp_all
      rw [hsfeq, modalApplyOneS4Keyed_diaNeg_eq_S4Rules] at h ⊢
      exact modalApplyOneS4Rules_diaNeg_notApplicable_growth b nf acc χ sf.label h
  · by_cases hmintshape : (sf.sign = .neg ∧ ∃ χ, sf.formula = .box χ) ∨
        (sf.sign = .pos ∧ ∃ χ, sf.formula = .diamond χ)
    · exfalso
      rcases hmintshape with ⟨hs, χ, hf⟩ | ⟨hs, χ, hf⟩
      · have hsfeq : sf = (⟨.neg, .box χ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) := by
          rcases sf with ⟨s', f', w'⟩; simp_all
        rw [hsfeq] at h
        simp only [modalApplyOneS4Keyed] at h
        rcases hblk : blockingWorldS4Keyed φ₀ b keys .neg χ sf.label with _ | wBlock
        · rw [hblk] at h
          have hklin : (modalApplyOne (⟨.neg, .box χ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
              RuleResult.linear _ := rfl
          rcases modalApplyOneS4KeyedMint_fst_eq_or_linear (⟨.neg, .box χ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc with heq | ⟨forms, hraw, hkeyed⟩
          · rw [heq, hklin] at h; simp at h
          · rw [hkeyed] at h; simp at h
        · rw [hblk] at h; simp at h
      · have hsfeq : sf = (⟨.pos, .diamond χ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) := by
          rcases sf with ⟨s', f', w'⟩; simp_all
        rw [hsfeq] at h
        simp only [modalApplyOneS4Keyed] at h
        rcases hblk : blockingWorldS4Keyed φ₀ b keys .pos χ sf.label with _ | wBlock
        · rw [hblk] at h
          have hklin : (modalApplyOne (⟨.pos, .diamond χ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
              RuleResult.linear _ := rfl
          rcases modalApplyOneS4KeyedMint_fst_eq_or_linear (⟨.pos, .diamond χ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc with heq | ⟨forms, hraw, hkeyed⟩
          · rw [heq, hklin] at h; simp at h
          · rw [hkeyed] at h; simp at h
        · rw [hblk] at h; simp at h
    · have hbd' := not_or.mp hbd
      have hms' := not_or.mp hmintshape
      have hnb : ∀ χ, sf.formula ≠ .box χ := by
        intro χ hfeq
        rcases hs : sf.sign with _ | _
        · exact hbd'.1 ⟨hs, χ, hfeq⟩
        · exact hms'.1 ⟨hs, χ, hfeq⟩
      have hnd : ∀ χ, sf.formula ≠ .diamond χ := by
        intro χ hfeq
        rcases hs : sf.sign with _ | _
        · exact hms'.2 ⟨hs, χ, hfeq⟩
        · exact hbd'.2 ⟨hs, χ, hfeq⟩
      rw [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf.sign sf.formula sf.label
        hnb hnd b acc, show (⟨sf.sign, sf.formula, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) = sf from rfl] at h
      rw [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf.sign sf.formula sf.label
        hnb hnd (nf ++ b) acc, show (⟨sf.sign, sf.formula, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) = sf from rfl]
      rw [modalApplyOne_fst_eq_of_not_box_diamond sf (nf ++ b) b acc hnb hnd]
      exact h

/-! ## Phase 7.5: Propositional / Non-Mint Arm Restated Against `S4RedirectSoundInv`

Re-wraps `modalApplyOneS4Keyed_notBoxDia_sat` (above) into an `S4RedirectSoundInv`-preservation
step, discharging conjuncts (a)-(d) at a primary-scan step. `acc`/`Er` are unchanged (a
non-mint step creates no edge); the load-bearing argument is shared by (c) and (d): the fired
candidate `sf` has `outDeg acc sf.label = 0` (forced by conjunct (d) at the OLD state, since
`sf` is applicable and unexpanded), so every newly-produced formula -- all at label `sf.label`
-- lands at a world with no out-edge, hence cannot be a ghost-edge source. -/

omit [Hashable Atom] in
/-- **Bridging fact.** A world with a recorded out-edge has nonzero `outDeg`; contrapositive of
the fact Phase 7.5's (c)/(d) discharge actually consumes (`outDeg = 0 → no out-edge`). -/
lemma outDeg_ne_zero_of_hasEdge (acc : Accessibility) (w w' : WorldIndex)
    (h : acc.hasEdge w w' = true) : outDeg acc w ≠ 0 := by
  unfold outDeg
  unfold Accessibility.hasEdge at h
  rw [List.any_eq_true] at h
  obtain ⟨⟨src, tgt⟩, hmem, heq⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at heq
  obtain ⟨hs, ht⟩ := heq
  have hmemSucc : w' ∈ acc.successorsOf w := by
    unfold Accessibility.successorsOf
    rw [List.mem_filterMap]
    refine ⟨(src, tgt), hmem, ?_⟩
    simp [hs, ht]
  intro hlen
  rw [List.length_eq_zero_iff] at hlen
  rw [hlen] at hmemSucc
  simp at hmemSucc

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Output-label preservation for `tryAllPropRules`.** Every signed formula produced by any
propositional rule shares the label of the input formula: immediate from
`tryAllPropRules_pos`/`_neg`'s explicit `l` binding in every match arm. Stated over the
match-shaped membership predicate (`.linear`/`.persistent` list membership, or membership in
SOME `.branching` branch) so it covers whichever result shape the caller's rule actually
produces. -/
lemma tryAllPropRules_output_label_eq
    (s : Sign) (φ : Proposition Atom) (l : WorldIndex)
    (sf' : SignedFormula (Proposition Atom) WorldIndex)
    (hmem : match tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
        (⟨s, φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) with
      | .linear fs => sf' ∈ fs
      | .branching brs => ∃ br ∈ brs, sf' ∈ br
      | .persistent fs => sf' ∈ fs
      | .notApplicable => False) :
    sf'.label = l := by
  rcases s with _ | _
  · rw [tryAllPropRules_pos] at hmem
    rcases hA : modalAndOf? φ with _ | ⟨x, y⟩ <;> rcases hO : modalOrOf? φ with _ | ⟨x, y⟩ <;>
      rcases hI : modalImpOf? φ with _ | ⟨x, y⟩ <;> rcases hN : modalNegOf? φ with _ | x <;>
      simp_all
    all_goals (rcases hmem with rfl | rfl <;> rfl)
  · rw [tryAllPropRules_neg] at hmem
    rcases hA : modalAndOf? φ with _ | ⟨x, y⟩ <;> rcases hO : modalOrOf? φ with _ | ⟨x, y⟩ <;>
      rcases hI : modalImpOf? φ with _ | ⟨x, y⟩ <;> rcases hN : modalNegOf? φ with _ | x <;>
      simp_all
    all_goals (rcases hmem with rfl | rfl <;> rfl)

/-- **Propositional/non-mint arm restated against `S4RedirectSoundInv` (Phase 7.5).** At a
primary-scan step firing a non-mint-shaped candidate `sf` (neither box nor diamond), some
output `nf` of `modalApplyOneS4Keyed`'s result (the list itself for `.linear`/`.persistent`, or
a satisfied branch for `.branching`) extends `S4RedirectSoundInv`: appending `nf` to `b` and
marking `sf` expanded preserves all four conjuncts, with `acc`/`Er` unchanged.

- (a): unchanged (`acc' = acc`, `Er' = Er`).
- (b): `modalApplyOneS4Keyed_notBoxDia_sat` reused verbatim on the SAME model witness `(m, f)`
  hypotheses (b) already supplies -- the disjunction in (b)'s edge clause is untouched since
  `acc' = acc`.
- (c)/(d): the shared load-bearing fact -- `sf` is applicable and unexpanded (candidate), so
  (d) at the OLD state forces `outDeg acc sf.label = 0`; every formula in `nf` is at label
  `sf.label` (`tryAllPropRules_output_label_eq`), so no ghost edge (whose source has nonzero
  `outDeg` by `outDeg_ne_zero_of_hasEdge` plus conjunct (a)) can be sourced at `sf.label`. Hence
  (c) inherits from the old state (the new formulas never trigger a ghost-source obligation),
  and (d) at the new state holds either because the formula is old (old (d) plus
  `modalApplyOneS4Keyed_notApplicable_growth`, Phase 7.4) or because it is new (vacuous, by the
  same zero-outDeg fact). -/
theorem S4RedirectSoundInv_notBoxDia_step (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (Er : List (WorldIndex × WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hnb : ∀ ψ, sf.formula ≠ .box ψ) (hnd : ∀ ψ, sf.formula ≠ .diamond ψ)
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er)
    (hcand : sf ∈ modalNonMintCandidates φ₀ keys b e acc) :
    ∃ nf : List (SignedFormula (Proposition Atom) WorldIndex),
      (match (modalApplyOneS4Keyed φ₀ keys sf b acc).1 with
        | .linear fs => nf = fs
        | .branching brs => nf ∈ brs
        | .persistent fs => nf = fs
        | .notApplicable => False) ∧
      S4RedirectSoundInv φ₀ (nf ++ b) (sf :: e) acc keys Er := by
  obtain ⟨hEr, hSat, hAbs, hFroz⟩ := hinv
  obtain ⟨W, m, f, hFC, hacc, hbsat⟩ := hSat
  have hmemb : sf ∈ b := modalNonMintCandidates_subset φ₀ keys b e acc hcand
  have hnotexp : sf ∉ e := modalNonMintCandidates_not_mem_expanded φ₀ keys b e acc sf hcand
  have hsfe : (⟨sf.sign, sf.formula, sf.label⟩ :
      SignedFormula (Proposition Atom) WorldIndex) = sf := rfl
  have hmintapp : modalMintShape sf = false ∧
      (modalApplyOneS4Keyed φ₀ keys sf b acc).1.isApplicable = true := by
    unfold modalNonMintCandidates at hcand
    have hpred := (List.mem_filter.mp hcand).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpred
    exact ⟨hpred.1.1, hpred.2⟩
  obtain ⟨hmshape, happ⟩ := hmintapp
  -- Old conjunct (d), instantiated at the fired candidate `sf`: forces `outDeg acc sf.label = 0`.
  have houtdeg0 : outDeg acc sf.label = 0 := by
    by_contra hne
    rcases hFroz sf hmemb hmshape hne with h1 | h2
    · exact hnotexp h1
    · rw [h2] at happ
      simp [RuleResult.isApplicable] at happ
  -- No ghost edge is sourced at `sf.label` (bridging fact plus the zero-outDeg fact).
  have hnoghost : ∀ p ∈ Er, p.1 ≠ sf.label := by
    intro p hp heq
    exact outDeg_ne_zero_of_hasEdge acc p.1 p.2 (hEr p hp) (heq ▸ houtdeg0)
  -- The candidate's own semantic soundness, verbatim -- reused on the SAME model witness.
  have hsfsat : sfSat m f sf := hbsat sf hmemb
  obtain ⟨-, hRRS⟩ := modalApplyOneS4Keyed_notBoxDia_sat φ₀ keys b acc sf.sign sf.formula
    sf.label hnb hnd m f (hsfe ▸ hsfsat)
  -- Reduce the candidate's rule result to `tryAllPropRules`, so the label-preservation fact
  -- (`tryAllPropRules_output_label_eq`) applies to whatever branch is actually produced.
  have heqTry : (modalApplyOneS4Keyed φ₀ keys sf b acc).1 =
      tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf := by
    have hred := modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf.sign sf.formula
      sf.label hnb hnd b acc
    rw [hsfe] at hred
    rw [hred] at happ ⊢
    unfold modalApplyOne at happ ⊢
    simp only at happ ⊢
    split_ifs at happ ⊢ with hpa
    · rfl
    · exfalso
      rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
        simp_all [RuleResult.isApplicable]
  -- The load-bearing label fact: every new formula lands at `sf.label`, which (c)/(d) need.
  have hnflabel : ∀ nf' : List (SignedFormula (Proposition Atom) WorldIndex),
      (match (modalApplyOneS4Keyed φ₀ keys sf b acc).1 with
        | .linear fs => nf' = fs
        | .branching brs => nf' ∈ brs
        | .persistent fs => nf' = fs
        | .notApplicable => False) →
      ∀ sf' ∈ nf', sf'.label = sf.label := by
    intro nf' hnf' sf' hsf'mem
    apply tryAllPropRules_output_label_eq sf.sign sf.formula sf.label sf'
    rw [← heqTry]
    rcases hshape : (modalApplyOneS4Keyed φ₀ keys sf b acc).1 with fs | brs | fs | -
    · rw [hshape] at hnf'; exact hnf' ▸ hsf'mem
    · rw [hshape] at hnf'; exact ⟨nf', hnf', hsf'mem⟩
    · rw [hshape] at hnf'; exact hnf' ▸ hsf'mem
    · rw [hshape] at hnf'; exact hnf'.elim
  -- Assemble the arm, per output shape.
  rcases hres : (modalApplyOneS4Keyed φ₀ keys sf b acc).1 with nf | brs | nf | -
  · -- `.linear nf`
    rw [hres] at hRRS
    refine ⟨nf, rfl, hEr, ⟨W, m, f, hFC, hacc, ?_⟩, ?_, ?_⟩
    · intro sf' hmem'
      rcases List.mem_append.mp hmem' with hnew | hold
      · exact hRRS sf' hnew
      · exact hbsat sf' hold
    · intro p hp χ
      have hne := hnoghost p hp
      have hsub : ∀ sf' ∈ (nf ++ b), sf' ∈ b ∨ sf'.label = sf.label := fun sf' hmem' =>
        (List.mem_append.mp hmem').elim
          (fun h => Or.inr (hnflabel nf (by rw [hres]) sf' h))
          Or.inl
      have hAbs' := hAbs p hp χ
      refine ⟨fun hmem1 => ?_, fun hmem2 => ?_⟩
      · rcases hsub _ hmem1 with hin | hlbl
        · obtain ⟨h1, h2⟩ := hAbs'.1 hin
          exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
        · exact absurd hlbl hne
      · rcases hsub _ hmem2 with hin | hlbl
        · obtain ⟨h1, h2⟩ := hAbs'.2 hin
          exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
        · exact absurd hlbl hne
    · intro sf' hmem' hmshape' houtdeg'
      rcases List.mem_append.mp hmem' with hnew | hold
      · exfalso
        have hlbl := hnflabel nf (by rw [hres]) sf' hnew
        rw [hlbl, houtdeg0] at houtdeg'
        exact houtdeg' rfl
      · rcases eq_or_ne sf' sf with rfl | hne'
        · exact Or.inl List.mem_cons_self
        · rcases hFroz sf' hold hmshape' houtdeg' with h1 | h2
          · exact Or.inl (List.mem_cons_of_mem _ h1)
          · exact Or.inr (modalApplyOneS4Keyed_notApplicable_growth φ₀ keys sf' b nf acc h2)
  · -- `.branching brs`
    rw [hres] at hRRS
    obtain ⟨br, hbrmem, hbrsat⟩ := hRRS
    refine ⟨br, hbrmem, hEr, ⟨W, m, f, hFC, hacc, ?_⟩, ?_, ?_⟩
    · intro sf' hmem'
      rcases List.mem_append.mp hmem' with hnew | hold
      · exact hbrsat sf' hnew
      · exact hbsat sf' hold
    · intro p hp χ
      have hne := hnoghost p hp
      have hsub : ∀ sf' ∈ (br ++ b), sf' ∈ b ∨ sf'.label = sf.label := fun sf' hmem' =>
        (List.mem_append.mp hmem').elim
          (fun h => Or.inr (hnflabel br (by rw [hres]; exact hbrmem) sf' h))
          Or.inl
      have hAbs' := hAbs p hp χ
      refine ⟨fun hmem1 => ?_, fun hmem2 => ?_⟩
      · rcases hsub _ hmem1 with hin | hlbl
        · obtain ⟨h1, h2⟩ := hAbs'.1 hin
          exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
        · exact absurd hlbl hne
      · rcases hsub _ hmem2 with hin | hlbl
        · obtain ⟨h1, h2⟩ := hAbs'.2 hin
          exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
        · exact absurd hlbl hne
    · intro sf' hmem' hmshape' houtdeg'
      rcases List.mem_append.mp hmem' with hnew | hold
      · exfalso
        have hlbl := hnflabel br (by rw [hres]; exact hbrmem) sf' hnew
        rw [hlbl, houtdeg0] at houtdeg'
        exact houtdeg' rfl
      · rcases eq_or_ne sf' sf with rfl | hne'
        · exact Or.inl List.mem_cons_self
        · rcases hFroz sf' hold hmshape' houtdeg' with h1 | h2
          · exact Or.inl (List.mem_cons_of_mem _ h1)
          · exact Or.inr (modalApplyOneS4Keyed_notApplicable_growth φ₀ keys sf' b br acc h2)
  · -- `.persistent nf`
    rw [hres] at hRRS
    refine ⟨nf, rfl, hEr, ⟨W, m, f, hFC, hacc, ?_⟩, ?_, ?_⟩
    · intro sf' hmem'
      rcases List.mem_append.mp hmem' with hnew | hold
      · exact hRRS sf' hnew
      · exact hbsat sf' hold
    · intro p hp χ
      have hne := hnoghost p hp
      have hsub : ∀ sf' ∈ (nf ++ b), sf' ∈ b ∨ sf'.label = sf.label := fun sf' hmem' =>
        (List.mem_append.mp hmem').elim
          (fun h => Or.inr (hnflabel nf (by rw [hres]) sf' h))
          Or.inl
      have hAbs' := hAbs p hp χ
      refine ⟨fun hmem1 => ?_, fun hmem2 => ?_⟩
      · rcases hsub _ hmem1 with hin | hlbl
        · obtain ⟨h1, h2⟩ := hAbs'.1 hin
          exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
        · exact absurd hlbl hne
      · rcases hsub _ hmem2 with hin | hlbl
        · obtain ⟨h1, h2⟩ := hAbs'.2 hin
          exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
        · exact absurd hlbl hne
    · intro sf' hmem' hmshape' houtdeg'
      rcases List.mem_append.mp hmem' with hnew | hold
      · exfalso
        have hlbl := hnflabel nf (by rw [hres]) sf' hnew
        rw [hlbl, houtdeg0] at houtdeg'
        exact houtdeg' rfl
      · rcases eq_or_ne sf' sf with rfl | hne'
        · exact Or.inl List.mem_cons_self
        · rcases hFroz sf' hold hmshape' houtdeg' with h1 | h2
          · exact Or.inl (List.mem_cons_of_mem _ h1)
          · exact Or.inr (modalApplyOneS4Keyed_notApplicable_growth φ₀ keys sf' b nf acc h2)
  · -- `.notApplicable`: contradicts `happ`.
    exfalso
    rw [hres] at happ
    simp [RuleResult.isApplicable] at happ

/-! ## Phase 7.6: Mint-Unblocked Arms Restated, and P3

P3 ("mint seed covers the 4-payload"): tested directly rather than assumed. The claim is
load-bearing, not moot -- a same-world persistent formula (e.g. `T(□ψ)@w` sitting on the branch
next to the minting formula) picks up a genuinely NEW candidate from the 4-rule/K-rule once the
fresh successor `w'` is recorded (`modalFourBoxProp`/`boxPropagation` scan `acc.successorsOf w`,
which now includes `w'`), and nothing makes that candidate vanish except the mint step's OWN
`boxProps`/`diaNegProps` payload landing in `nf` at exactly that fresh label. The two lemmas
below extract, from `modalS4Saturated`, that every one of the three per-layer candidate lists
(K/T/4) is *individually* empty at the OLD successors -- not just that the packaged `.fst` value
is `.notApplicable` -- which is exactly what P3 needs to transfer this fact across the new edge:
combined with the mint payload's own construction (`boxProps`/`diaNegProps`, which duplicates
the fresh-successor case of K's rule verbatim), the K/4-rule scans against the NEW state
(`nf ++ b`, `acc.addEdge w w'`) are empty at every successor, old and new alike. -/

/-- **P3, box-positive layer.** Under saturation, EVERY per-layer candidate list for a
box-positive persistent formula `T(□ψ)@w ∈ b` is individually empty -- not merely that their
combination is `.notApplicable`. Reuses the exact internal decomposition
`modalApplyOneS4Rules_boxPos_notApplicable_of_saturated` already performs, stopping one step
earlier to expose each layer rather than only the packaged conclusion. -/
lemma modalApplyOneS4Rules_boxPos_layers_eq_nil_of_saturated (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSat : modalS4Saturated φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    boxPropagation b acc ψ w = [] ∧ modalTBoxSelf b ψ w = [] ∧
      modalFourBoxProp b acc ψ w = [] := by
  have hcond := hSat _ hmem
  have hshape : modalApplyOneS4 φ₀ (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc =
      modalApplyOneS4Rules (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond
  simp only at hcond
  have hK : (modalApplyOne (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      if (boxPropagation b acc ψ w).isEmpty then RuleResult.notApplicable
      else RuleResult.persistent (boxPropagation b acc ψ w) := by
    unfold modalApplyOne
    simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
      modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
    split_ifs <;> simp_all
  have htR : (modalApplyOneT (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOne (⟨.pos, .box ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | .persistent kForms =>
          RuleResult.persistent
            (kForms ++ (modalTBoxSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
        | .notApplicable =>
          if (modalTBoxSelf b ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalTBoxSelf b ψ w)
        | other => other) := by
    unfold modalApplyOneT
    obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases kResult <;> first | rfl | (simp only []; split <;> rfl)
  rw [htR, hK] at hcond
  have hBoxNotMem : ∀ x ∈ boxPropagation b acc ψ w, x ∉ b := by
    intro x hx
    unfold boxPropagation at hx
    simp only [List.mem_filterMap] at hx
    obtain ⟨w', -, heq⟩ := hx
    split_ifs at heq with hin
    simp only [Option.some.injEq] at heq
    subst heq
    simpa using hin
  have hSelfNotMem : ∀ x ∈ modalTBoxSelf b ψ w, x ∉ b := by
    intro x hx
    by_cases hin : ((b.any fun y => y == (⟨.pos, ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex)) = true)
    · rw [modalTBoxSelf, if_pos hin] at hx
      simp at hx
    · rw [modalTBoxSelf, if_neg hin] at hx
      simp only [List.mem_singleton] at hx
      subst hx
      simpa using hin
  have hFourNotMem : ∀ x ∈ modalFourBoxProp b acc ψ w, x ∉ b := by
    intro x hx
    unfold modalFourBoxProp at hx
    simp only [List.mem_filterMap] at hx
    obtain ⟨w', -, heq⟩ := hx
    split_ifs at heq with hin
    simp only [Option.some.injEq] at heq
    subst heq
    simpa using hin
  split_ifs at hcond with h1 h2 h3 <;> simp only [] at hcond <;>
    first
    | exact ⟨List.isEmpty_iff.mp (by simpa using h1), List.isEmpty_iff.mp (by simpa using h2),
        List.isEmpty_iff.mp (by simpa using h3)⟩
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h1)
       exact hBoxNotMem x hx (hcond x (by simp [hx])))
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h2)
       exact hSelfNotMem x hx (hcond x (by simp [hx])))
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h3)
       exact hFourNotMem x hx (hcond x (by simp [hx])))

/-- **P3, diamond-negative layer.** Dual of
`modalApplyOneS4Rules_boxPos_layers_eq_nil_of_saturated`. -/
lemma modalApplyOneS4Rules_diaNeg_layers_eq_nil_of_saturated (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSat : modalS4Saturated φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ((acc.successorsOf w).filterMap (fun w' =>
        let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
        if b.any (· == sf') then none else some sf')) = [] ∧
      modalTDiaNegSelf b ψ w = [] ∧ modalFourDiaNegProp b acc ψ w = [] := by
  have hcond := hSat _ hmem
  have hshape : modalApplyOneS4 φ₀ (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc =
      modalApplyOneS4Rules (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond
  simp only at hcond
  set diaPropagation : List (SignedFormula (Proposition Atom) WorldIndex) :=
    (acc.successorsOf w).filterMap (fun w' =>
      let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
      if b.any (· == sf') then none else some sf') with hDiaPropDef
  have hK : (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      if diaPropagation.isEmpty
      then RuleResult.notApplicable
      else RuleResult.persistent diaPropagation := by
    unfold modalApplyOne
    simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
      modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none, hDiaPropDef]
    split_ifs <;> simp_all
  have htR : (modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | .persistent kForms =>
          RuleResult.persistent
            (kForms ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
        | .notApplicable =>
          if (modalTDiaNegSelf b ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalTDiaNegSelf b ψ w)
        | other => other) := by
    unfold modalApplyOneT
    obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases kResult <;> first | rfl | (simp only []; split <;> rfl)
  rw [htR, hK] at hcond
  have hDiaNotMem : ∀ x ∈ diaPropagation, x ∉ b := by
    intro x hx
    rw [hDiaPropDef] at hx
    simp only [List.mem_filterMap] at hx
    obtain ⟨w', -, heq⟩ := hx
    split_ifs at heq with hin
    simp only [Option.some.injEq] at heq
    subst heq
    simpa using hin
  have hSelfNotMem : ∀ x ∈ modalTDiaNegSelf b ψ w, x ∉ b := by
    intro x hx
    by_cases hin : ((b.any fun y => y == (⟨.neg, ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex)) = true)
    · rw [modalTDiaNegSelf, if_pos hin] at hx
      simp at hx
    · rw [modalTDiaNegSelf, if_neg hin] at hx
      simp only [List.mem_singleton] at hx
      subst hx
      simpa using hin
  have hFourNotMem : ∀ x ∈ modalFourDiaNegProp b acc ψ w, x ∉ b := by
    intro x hx
    unfold modalFourDiaNegProp at hx
    simp only [List.mem_filterMap] at hx
    obtain ⟨w', -, heq⟩ := hx
    split_ifs at heq with hin
    simp only [Option.some.injEq] at heq
    subst heq
    simpa using hin
  split_ifs at hcond with h1 h2 h3 <;> simp only [] at hcond <;>
    first
    | exact ⟨List.isEmpty_iff.mp (by simpa using h1), List.isEmpty_iff.mp (by simpa using h2),
        List.isEmpty_iff.mp (by simpa using h3)⟩
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h1)
       exact hDiaNotMem x hx (hcond x (by simp [hx])))
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h2)
       exact hSelfNotMem x hx (hcond x (by simp [hx])))
    | (exfalso
       obtain ⟨x, hx⟩ := List.isEmpty_eq_false_iff_exists_mem.mp (by simpa using h3)
       exact hFourNotMem x hx (hcond x (by simp [hx])))

omit [Hashable Atom] in
/-- `boxPropagation` at a world other than the redirect source is unaffected by `addEdge`:
immediate from `successorsOf_addEdge_of_ne`. -/
lemma boxPropagation_addEdge_of_ne
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (src wBlock w'' : WorldIndex) (hne : w'' ≠ src) :
    boxPropagation b (acc.addEdge src wBlock) ψ w'' = boxPropagation b acc ψ w'' := by
  unfold boxPropagation
  rw [successorsOf_addEdge_of_ne acc src wBlock w'' hne]

omit [Hashable Atom] in
/-- `modalFourBoxProp` at a world other than the redirect source is unaffected by `addEdge`. -/
lemma modalFourBoxProp_addEdge_of_ne
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (src wBlock w'' : WorldIndex) (hne : w'' ≠ src) :
    modalFourBoxProp b (acc.addEdge src wBlock) ψ w'' = modalFourBoxProp b acc ψ w'' := by
  unfold modalFourBoxProp
  rw [successorsOf_addEdge_of_ne acc src wBlock w'' hne]

omit [Hashable Atom] in
/-- `modalFourDiaNegProp` at a world other than the redirect source is unaffected by
`addEdge`. -/
lemma modalFourDiaNegProp_addEdge_of_ne
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (src wBlock w'' : WorldIndex) (hne : w'' ≠ src) :
    modalFourDiaNegProp b (acc.addEdge src wBlock) ψ w'' = modalFourDiaNegProp b acc ψ w'' := by
  unfold modalFourDiaNegProp
  rw [successorsOf_addEdge_of_ne acc src wBlock w'' hne]

/-- **Box-positive, acc-independence off the redirect source.** At any world other than `src`,
`modalApplyOneS4Rules`'s box-positive `.fst` is unaffected by `addEdge src wBlock`: both the
K-layer (`boxPropagation`) and the 4-rule layer (`modalFourBoxProp`) only consult
`acc.successorsOf w''`, unaffected off `src`; the T-layer (`modalTBoxSelf`) never consults `acc`
at all. -/
lemma modalApplyOneS4Rules_boxPos_fst_addEdge_of_ne (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ'' : Proposition Atom) (src wBlock w'' : WorldIndex) (hne : w'' ≠ src) :
    (modalApplyOneS4Rules (⟨.pos, .box ψ'', w''⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b (acc.addEdge src wBlock)).fst =
      (modalApplyOneS4Rules (⟨.pos, .box ψ'', w''⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  have h1 := modalApplyOneS4_boxPos_fst_eq φ₀ b acc ψ'' w''
  have h2 := modalApplyOneS4_boxPos_fst_eq φ₀ b (acc.addEdge src wBlock) ψ'' w''
  have hshape1 := modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀
    (⟨.pos, .box ψ'', w''⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc ⟨by simp, by simp⟩
  have hshape2 := modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀
    (⟨.pos, .box ψ'', w''⟩ : SignedFormula (Proposition Atom) WorldIndex) b
    (acc.addEdge src wBlock) ⟨by simp, by simp⟩
  rw [hshape1] at h1
  rw [hshape2] at h2
  rw [h1, h2, boxPropagation_addEdge_of_ne b acc ψ'' src wBlock w'' hne,
    modalFourBoxProp_addEdge_of_ne b acc ψ'' src wBlock w'' hne]

/-- **Diamond-negative, acc-independence off the redirect source.** Dual of
`modalApplyOneS4Rules_boxPos_fst_addEdge_of_ne`. -/
lemma modalApplyOneS4Rules_diaNeg_fst_addEdge_of_ne (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ'' : Proposition Atom) (src wBlock w'' : WorldIndex) (hne : w'' ≠ src) :
    (modalApplyOneS4Rules (⟨.neg, .diamond ψ'', w''⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b (acc.addEdge src wBlock)).fst =
      (modalApplyOneS4Rules (⟨.neg, .diamond ψ'', w''⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  have h1 := modalApplyOneS4_diaNeg_fst_eq φ₀ b acc ψ'' w''
  have h2 := modalApplyOneS4_diaNeg_fst_eq φ₀ b (acc.addEdge src wBlock) ψ'' w''
  have hshape1 := modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀
    (⟨.neg, .diamond ψ'', w''⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
    ⟨by simp, by simp⟩
  have hshape2 := modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀
    (⟨.neg, .diamond ψ'', w''⟩ : SignedFormula (Proposition Atom) WorldIndex) b
    (acc.addEdge src wBlock) ⟨by simp, by simp⟩
  rw [hshape1] at h1
  rw [hshape2] at h2
  have hsucc : (acc.addEdge src wBlock).successorsOf w'' = acc.successorsOf w'' :=
    successorsOf_addEdge_of_ne acc src wBlock w'' hne
  rw [h1, h2, hsucc, modalFourDiaNegProp_addEdge_of_ne b acc ψ'' src wBlock w'' hne]

/-! ## Phase 7.6 continued: the two mint-unblocked arm theorems

The remaining Phase 7.6 assembly (per the plan's Progress Record): the same-world sub-case of
conjunct (d) (P3 proper, items 1/3 of the record), the mint-payload compensation facts feeding
it, the weakened conjunct (b) re-derivation (item 4), and the two arm theorems themselves
(items 4-6). -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Forward direction of `mem_boxPositivesOf` (`Support/KnownWorlds.lean`, which only supplies
the inverse direction): a box-positive branch member yields a `boxPositivesOf` pair. -/
lemma mem_boxPositivesOf_of_mem {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {ψ : Proposition Atom} {w : WorldIndex}
    (h : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (ψ, w) ∈ boxPositivesOf b := by
  unfold boxPositivesOf
  rw [List.mem_filterMap]
  exact ⟨⟨.pos, .box ψ, w⟩, h, by simp⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- `outDeg` at the freshly-minted target world, after recording the one mint edge into it, is
still zero: by freshness (`accFreshInv`), no OLD edge is sourced at `w' := modalNextWorld b`
(else `hInv` would give `w' < w'`, absurd), and `outDeg_addEdge_ne` rules out the new edge
contributing to `w'`'s own out-successors (its source is `w ≠ w'`). Needed for conjunct (d)'s
`sf' ∈ nf` case of the mint-unblocked arms: the freshly-minted world is a graph sink, so no
ghost edge can ever be sourced there. -/
lemma outDeg_addEdge_freshTarget_eq_zero
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (w : WorldIndex) (hInv : accFreshInv b acc) (hne : w ≠ modalNextWorld b) :
    outDeg (acc.addEdge w (modalNextWorld b)) (modalNextWorld b) = 0 := by
  rw [outDeg_addEdge_ne acc w (modalNextWorld b) (modalNextWorld b) (Ne.symm hne)]
  have h0 : outDeg acc (modalNextWorld b) = 0 := by
    by_contra hne0
    have hlenne : acc.successorsOf (modalNextWorld b) ≠ [] := by
      intro hnil
      apply hne0
      unfold outDeg
      simp [hnil]
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hlenne
    have hedge := mem_successorsOf_hasEdge hv
    exact Nat.lt_irrefl _ (hInv _ _ hedge).1
  exact h0

omit [Hashable Atom] in
/-- **Mint-payload compensation, box-positive half.** A box-positive persistent formula
`T(□χ)@w` co-located with a firing mint (any `χ`, possibly unrelated to the mint's own
witness) has BOTH its K-layer transmission (`T(χ)@w'`) and its box-plus 4-layer transmission
(`T(□χ)@w'`) already present in the mint payload's own construction, at the fresh successor
`w' := modalNextWorld b` -- unconditionally, since `w'` is fresh and neither compensating
formula could already have been filtered out as "already on the branch". Stated against the
literal filterMap shape shared verbatim by `modalApplyOneS4KeyedMint_boxNeg_eq_S4`/
`_diaPos_eq_S4` (the K-layer piece) and `boxPlusExtraS4`'s own definition (the box-plus piece),
so this lemma applies to either mint arm's payload unchanged. -/
lemma mem_mintPayload_boxPos_compensation
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (χ : Proposition Atom)
    (w : WorldIndex)
    (hmem : (⟨.pos, .box χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.pos, χ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      (boxPositivesOf b).filterMap (fun (ψ, src) =>
        if src == w then
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
          if b.any (· == sf') then none else some sf'
        else none) ∧
    (⟨.pos, .box χ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      boxPlusExtraS4 b w := by
  have hpair : (χ, w) ∈ boxPositivesOf b := mem_boxPositivesOf_of_mem hmem
  have hnotmemK : (⟨.pos, χ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex)
      ∉ b := fun hc => Nat.lt_irrefl _ (modalNextWorld_gt b _ hc)
  have hnotmemBoxed : (⟨.pos, .box χ, modalNextWorld b⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∉ b := fun hc =>
    Nat.lt_irrefl _ (modalNextWorld_gt b _ hc)
  refine ⟨?_, ?_⟩
  · rw [List.mem_filterMap]
    exact ⟨(χ, w), hpair, by simp [hnotmemK]⟩
  · unfold boxPlusExtraS4
    rw [List.mem_append]
    left
    rw [List.mem_filterMap]
    exact ⟨(χ, w), hpair, by simp [hnotmemBoxed]⟩

omit [Hashable Atom] in
/-- **Mint-payload compensation, diamond-negative half.** Dual of
`mem_mintPayload_boxPos_compensation` for a diamond-negative persistent formula `F(◇χ)@w`
co-located with a firing mint. -/
lemma mem_mintPayload_diaNeg_compensation
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (χ : Proposition Atom)
    (w : WorldIndex)
    (hmem : (⟨.neg, .diamond χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, χ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .diamond ψ =>
            let pr : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, modalNextWorld b⟩
            if b.any (· == pr) then none else some pr
          | _ => none
        else none) ∧
    (⟨.neg, .diamond χ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      boxPlusExtraS4 b w := by
  have hnotmemK : (⟨.neg, χ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex)
      ∉ b := fun hc => Nat.lt_irrefl _ (modalNextWorld_gt b _ hc)
  have hnotmemBoxed : (⟨.neg, .diamond χ, modalNextWorld b⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∉ b := fun hc =>
    Nat.lt_irrefl _ (modalNextWorld_gt b _ hc)
  refine ⟨?_, ?_⟩
  · rw [List.mem_filterMap]
    exact ⟨(⟨.neg, .diamond χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex), hmem,
      by simp [hnotmemK]⟩
  · unfold boxPlusExtraS4
    rw [List.mem_append]
    right
    rw [List.mem_filterMap]
    exact ⟨(⟨.neg, .diamond χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex), hmem,
      by simp [hnotmemBoxed]⟩

/-- **Conjunct (d), same-world sub-case, box-positive persistent formula (P3 proper, item 1 of
the Phase 7.6 Progress Record).** After a mint step fires at `w` creating a fresh successor
`w' := modalNextWorld b`, a co-located box-positive persistent formula `T(□χ)@w` (any `χ`,
possibly unrelated to the minting formula) is `.notApplicable` at the extended state
`(nf ++ b, acc.addEdge w w')` for ANY payload `nf` containing both compensation members: P3
(`modalApplyOneS4Rules_boxPos_layers_eq_nil_of_saturated`) empties every OLD-successor
candidate, and `hunwrapped`/`hboxed` empty the one NEW-successor (`w'`) candidate. -/
lemma modalApplyOneS4Rules_boxPos_fst_notApplicable_of_mint (φ₀ : Proposition Atom)
    (b nf : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (χ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hSat : modalS4Saturated φ₀ b acc)
    (hunwrapped : (⟨.pos, χ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ nf)
    (hboxed : (⟨.pos, .box χ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ nf) :
    (modalApplyOneS4Rules (⟨.pos, .box χ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) (nf ++ b) (acc.addEdge w w')).fst =
      RuleResult.notApplicable := by
  obtain ⟨hK, hT, hFour⟩ :=
    modalApplyOneS4Rules_boxPos_layers_eq_nil_of_saturated φ₀ b acc hSat χ w hmem
  have hsucc : (acc.addEdge w w').successorsOf w = w' :: acc.successorsOf w :=
    successorsOf_addEdge_self acc w w'
  have hshape := modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀
    (⟨.pos, .box χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) (nf ++ b)
    (acc.addEdge w w') ⟨by simp, by simp⟩
  have hbig := modalApplyOneS4_boxPos_fst_eq φ₀ (nf ++ b) (acc.addEdge w w') χ w
  rw [hshape] at hbig
  have hKnew : boxPropagation (nf ++ b) (acc.addEdge w w') χ w = [] := by
    unfold boxPropagation
    rw [hsucc, List.filterMap_eq_nil_iff]
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · simp [show ((nf ++ b).any fun x => x == (⟨Sign.pos, χ, v⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = true from
        List.any_eq_true.mpr ⟨_, List.mem_append.mpr (Or.inl hunwrapped), by simp⟩]
    · have hvb : (⟨.pos, χ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        by_contra hnot
        have hcontra : (⟨.pos, χ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
            boxPropagation b acc χ w := by
          unfold boxPropagation
          rw [List.mem_filterMap]
          exact ⟨v, hv, by simp [hnot]⟩
        rw [hK] at hcontra
        simp at hcontra
      simp [show ((nf ++ b).any fun x => x == (⟨Sign.pos, χ, v⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = true from
        List.any_eq_true.mpr ⟨_, List.mem_append.mpr (Or.inr hvb), by simp⟩]
  have hTnew : modalTBoxSelf (nf ++ b) χ w = [] := by
    unfold modalTBoxSelf at hT ⊢
    by_cases hbin : (b.any (· == (⟨.pos, χ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex))) = true
    · have hmemb : (⟨.pos, χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        rw [List.any_eq_true] at hbin
        obtain ⟨x, hx, hxeq⟩ := hbin
        rw [beq_iff_eq] at hxeq
        rwa [hxeq] at hx
      have hbin' : ((nf ++ b).any (· == (⟨.pos, χ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex))) = true := by
        rw [List.any_eq_true]
        exact ⟨_, List.mem_append.mpr (Or.inr hmemb), by simp⟩
      rw [if_pos hbin']
    · rw [if_neg hbin] at hT
      simp at hT
  have hFournew : modalFourBoxProp (nf ++ b) (acc.addEdge w w') χ w = [] := by
    unfold modalFourBoxProp
    rw [hsucc, List.filterMap_eq_nil_iff]
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · simp [show ((nf ++ b).any fun x => x == (⟨Sign.pos, .box χ, v⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = true from
        List.any_eq_true.mpr ⟨_, List.mem_append.mpr (Or.inl hboxed), by simp⟩]
    · have hvb : (⟨.pos, .box χ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        by_contra hnot
        have hcontra : (⟨.pos, .box χ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
            modalFourBoxProp b acc χ w := by
          unfold modalFourBoxProp
          rw [List.mem_filterMap]
          exact ⟨v, hv, by simp [hnot]⟩
        rw [hFour] at hcontra
        simp at hcontra
      simp [show ((nf ++ b).any fun x => x == (⟨Sign.pos, .box χ, v⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = true from
        List.any_eq_true.mpr ⟨_, List.mem_append.mpr (Or.inr hvb), by simp⟩]
  rw [hbig, hKnew, hTnew, hFournew]
  simp

/-- **Conjunct (d), same-world sub-case, diamond-negative persistent formula.** Dual of
`modalApplyOneS4Rules_boxPos_fst_notApplicable_of_mint`. -/
lemma modalApplyOneS4Rules_diaNeg_fst_notApplicable_of_mint (φ₀ : Proposition Atom)
    (b nf : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (χ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.neg, .diamond χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hSat : modalS4Saturated φ₀ b acc)
    (hunwrapped : (⟨.neg, χ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ nf)
    (hboxed : (⟨.neg, .diamond χ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ nf) :
    (modalApplyOneS4Rules (⟨.neg, .diamond χ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) (nf ++ b) (acc.addEdge w w')).fst =
      RuleResult.notApplicable := by
  obtain ⟨hK, hT, hFour⟩ :=
    modalApplyOneS4Rules_diaNeg_layers_eq_nil_of_saturated φ₀ b acc hSat χ w hmem
  have hsucc : (acc.addEdge w w').successorsOf w = w' :: acc.successorsOf w :=
    successorsOf_addEdge_self acc w w'
  have hshape := modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀
    (⟨.neg, .diamond χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) (nf ++ b)
    (acc.addEdge w w') ⟨by simp, by simp⟩
  have hbig := modalApplyOneS4_diaNeg_fst_eq φ₀ (nf ++ b) (acc.addEdge w w') χ w
  rw [hshape] at hbig
  have hKnew : ((acc.addEdge w w').successorsOf w).filterMap (fun u =>
      let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, χ, u⟩
      if (nf ++ b).any (· == sf') then none else some sf') = [] := by
    rw [hsucc, List.filterMap_eq_nil_iff]
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · simp [show ((nf ++ b).any fun x => x == (⟨Sign.neg, χ, v⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = true from
        List.any_eq_true.mpr ⟨_, List.mem_append.mpr (Or.inl hunwrapped), by simp⟩]
    · have hvb : (⟨.neg, χ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        by_contra hnot
        have hcontra : (⟨.neg, χ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
            (acc.successorsOf w).filterMap (fun u =>
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, χ, u⟩
              if b.any (· == sf') then none else some sf') := by
          rw [List.mem_filterMap]
          exact ⟨v, hv, by simp [hnot]⟩
        rw [hK] at hcontra
        simp at hcontra
      simp [show ((nf ++ b).any fun x => x == (⟨Sign.neg, χ, v⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = true from
        List.any_eq_true.mpr ⟨_, List.mem_append.mpr (Or.inr hvb), by simp⟩]
  have hTnew : modalTDiaNegSelf (nf ++ b) χ w = [] := by
    unfold modalTDiaNegSelf at hT ⊢
    by_cases hbin : (b.any (· == (⟨.neg, χ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex))) = true
    · have hmemb : (⟨.neg, χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        rw [List.any_eq_true] at hbin
        obtain ⟨x, hx, hxeq⟩ := hbin
        rw [beq_iff_eq] at hxeq
        rwa [hxeq] at hx
      have hbin' : ((nf ++ b).any (· == (⟨.neg, χ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex))) = true := by
        rw [List.any_eq_true]
        exact ⟨_, List.mem_append.mpr (Or.inr hmemb), by simp⟩
      rw [if_pos hbin']
    · rw [if_neg hbin] at hT
      simp at hT
  have hFournew : modalFourDiaNegProp (nf ++ b) (acc.addEdge w w') χ w = [] := by
    unfold modalFourDiaNegProp
    rw [hsucc, List.filterMap_eq_nil_iff]
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · simp [show ((nf ++ b).any fun x => x == (⟨Sign.neg, .diamond χ, v⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = true from
        List.any_eq_true.mpr ⟨_, List.mem_append.mpr (Or.inl hboxed), by simp⟩]
    · have hvb : (⟨.neg, .diamond χ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        by_contra hnot
        have hcontra : (⟨.neg, .diamond χ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
            modalFourDiaNegProp b acc χ w := by
          unfold modalFourDiaNegProp
          rw [List.mem_filterMap]
          exact ⟨v, hv, by simp [hnot]⟩
        rw [hFour] at hcontra
        simp at hcontra
      simp [show ((nf ++ b).any fun x => x == (⟨Sign.neg, .diamond χ, v⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = true from
        List.any_eq_true.mpr ⟨_, List.mem_append.mpr (Or.inr hvb), by simp⟩]
  rw [hbig, hKnew, hTnew, hFournew]
  simp

/-- **Mint-unblocked, box-negative arm: `S4RedirectSoundInv` preservation (Phase 7.6).**
Re-wraps `modalApplyOneS4Keyed_boxNeg_mint_sat` against the weakened invariant. `Er` and `e` are
UNCHANGED (the new mint edge is realized directly by the extended witness `f'`, not recorded as
a ghost edge; a mint-shaped formula is exempt from `e`-tracking by conjunct (d)'s own
`modalMintShape sf = false` guard). Conjunct (a) is mechanical; (b) reuses the landed
pointwise-extension construction verbatim, generalizing only the one `hacc u v hedge` call site
to case on the weakened disjunction; (c) transfers via `mintGroup_label_eq_freshWorld`/
`boxPlusExtraS4_label_eq_freshWorld` plus `accFreshInv`; (d) splits into the vacuous new-formula
case (`outDeg_addEdge_freshTarget_eq_zero`), the same-world box/diamond case (P3, the two
`_fst_notApplicable_of_mint` lemmas above), the other-world box/diamond case (the acc-independence
lemmas landed earlier this phase plus Phase 7.4's branch-growth family), and the
propositional/atomic case (acc- and branch-independence, mirroring Phase 7.5). -/
theorem S4RedirectSoundInv_boxNeg_mint (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (Er : List (WorldIndex × WorldIndex))
    (ψ : Proposition Atom) (w : WorldIndex)
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er)
    (hSat : modalS4Saturated φ₀ b acc)
    (hmint : modalNonMintCandidates φ₀ keys b e acc = [])
    (hInv : accFreshInv b acc)
    (hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ w = none)
    (hsfmem : (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ nf, modalApplyOneS4Keyed φ₀ keys (⟨.neg, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear nf, acc.addEdge w (modalNextWorld b)) ∧
      S4RedirectSoundInv φ₀ (nf ++ b) e (acc.addEdge w (modalNextWorld b)) keys Er := by
  obtain ⟨hEr, hbSem, hAbs, -⟩ := hinv
  have hAOeq := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ w hblock
  rw [hAOeq, modalApplyOneS4KeyedMint_boxNeg_eq_S4]
  set w' := modalNextWorld b with hw'def
  set nf : List (SignedFormula (Proposition Atom) WorldIndex) :=
    (((⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
        (boxPositivesOf b).filterMap (fun (ψ', src) =>
          if src == w then
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ', w'⟩
            if b.any (· == sf') then none else some sf'
          else none) ++
        b.filterMap (fun sf' =>
          if sf'.sign == .neg && sf'.label == w then
            match sf'.formula with
            | .diamond ψ' =>
              let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ', w'⟩
              if b.any (· == prop) then none else some prop
            | _ => none
          else none)) ++ boxPlusExtraS4 b w) with hnfdef
  have hw_ne : w ≠ w' := Nat.ne_of_lt (modalNextWorld_gt b _ hsfmem)
  have hnflabel : ∀ x ∈ nf, x.label = w' := by
    rw [hnfdef]
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact mintGroup_label_eq_freshWorld b w .neg ψ x hx1
    · exact boxPlusExtraS4_label_eq_freshWorld b w x hx2
  refine ⟨nf, rfl, ?_, ?_, ?_, ?_⟩
  · -- (a) every ghost edge is a recorded edge in the extended `acc`; `Er` unchanged.
    intro p hp
    exact hasEdge_addEdge_mono_gate0 (hEr p hp)
  · -- (b) semantic conjunct: the SAME pointwise-extension construction, weakened edge clause.
    obtain ⟨W, m, f, hFC, hrel, hb⟩ := hbSem
    have htrans := hFC.2
    have hnegbox : ¬ Satisfies m (f w) (Proposition.box ψ) := (hb _ hsfmem).2 rfl
    simp only [Satisfies] at hnegbox
    push Not at hnegbox
    obtain ⟨ww, hwwr, hwwψ⟩ := hnegbox
    let f' : WorldIndex → W := fun n => if n = w' then ww else f n
    refine ⟨W, m, f', hFC, ?_, ?_⟩
    · intro u v hedge
      simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
        Bool.or_eq_true] at hedge
      rcases hedge with hedge | hedge
      · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
        obtain ⟨rfl, rfl⟩ := hedge
        right
        rw [show f' w = f w from if_neg hw_ne, show f' w' = ww from if_pos rfl]
        exact hwwr
      · have huw' : u ≠ w' := by
          intro heq'
          have hfresh := (hInv u v hedge).1
          rw [heq'] at hfresh
          exact Nat.lt_irrefl _ hfresh
        have hvw' : v ≠ w' := by
          intro heq'
          have hfresh := (hInv u v hedge).2
          rw [heq'] at hfresh
          exact Nat.lt_irrefl _ hfresh
        rcases hrel u v hedge with hErmem | hr
        · exact Or.inl hErmem
        · right
          simp only [f', if_neg huw', if_neg hvw']
          exact hr
    · intro sf' hmem'
      rw [hnfdef] at hmem'
      simp only [List.mem_append, List.mem_cons] at hmem'
      rcases hmem' with (((rfl | hmem_bp) | hmem_dn) | hmem_bpe) | hmem_old
      · refine ⟨fun h => by simp at h, fun _ => ?_⟩
        simp only [f', if_pos rfl]
        exact hwwψ
      · simp only [List.mem_filterMap] at hmem_bp
        obtain ⟨⟨ψ'', src⟩, hpairMem, hsf'_from⟩ := hmem_bp
        split_ifs at hsf'_from with hsrceq hinb
        simp only [Option.some.injEq] at hsf'_from
        subst hsf'_from
        simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
        obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
        split_ifs at hbsfeq with hbsfpos
        cases hbf : bsf.formula with
        | box ψ''' =>
          rw [hbf] at hbsfeq
          simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
          obtain ⟨hψeq, hsrc⟩ := hbsfeq
          have hsrc_w : bsf.label = w := by rw [hsrc]; simpa using hsrceq
          have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
          rw [hbf, hsrc_w] at hbox_sat
          simp only [Satisfies] at hbox_sat
          refine ⟨fun _ => ?_, fun h => by simp at h⟩
          simp only [f', if_pos rfl]
          rw [← hψeq]
          exact hbox_sat ww hwwr
        | _ => simp [hbf] at hbsfeq
      · simp only [List.mem_filterMap] at hmem_dn
        obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
        by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == w) = true
        · rw [if_pos hbsfsign] at hbsfprop
          cases hbf : bsf.formula with
          | diamond ψ''' =>
            simp only [hbf] at hbsfprop
            by_cases hinb :
                (b.any (· == (⟨.neg, ψ''', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                  = true
            · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
            · rw [if_neg hinb] at hbsfprop
              simp only [Option.some.injEq] at hbsfprop
              subst hbsfprop
              have hsign : bsf.sign = .neg ∧ bsf.label = w := by
                simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
                exact hbsfsign
              have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
              rw [hbf, hsign.2] at hdiaNeg
              simp only [Satisfies] at hdiaNeg
              push Not at hdiaNeg
              refine ⟨fun h => by simp at h, fun _ => ?_⟩
              simp only [f', if_pos rfl]
              exact hdiaNeg ww hwwr
          | _ => simp [hbf] at hbsfprop
        · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
      · exact boxPlusExtraS4_sat m f htrans b w hb ww hwwr sf' hmem_bpe
      · have hlabel_ne : sf'.label ≠ w' := Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
        have hf'_eq : f' sf'.label = f sf'.label := by simp only [f', if_neg hlabel_ne]
        constructor
        · intro hsign; rw [hf'_eq]; exact (hb sf' hmem_old).1 hsign
        · intro hsign; rw [hf'_eq]; exact (hb sf' hmem_old).2 hsign
  · -- (c) syntactic absorption: old ghost edges (`Er` unchanged) inherit from `hAbs`, since every
    -- ghost-edge endpoint is `< w'` (freshness) while every `nf`-formula's label is exactly `w'`.
    intro p hp χ
    have hne1 : p.1 ≠ w' := Nat.ne_of_lt (hInv p.1 p.2 (hEr p hp)).1
    have hAbs' := hAbs p hp χ
    refine ⟨fun hmem1 => ?_, fun hmem2 => ?_⟩
    · have hin : (⟨.pos, .box χ, p.1⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        rcases List.mem_append.mp hmem1 with hin' | hin'
        · exact absurd (hnflabel _ hin') hne1
        · exact hin'
      obtain ⟨h1, h2⟩ := hAbs'.1 hin
      exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
    · have hin : (⟨.neg, .diamond χ, p.1⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        rcases List.mem_append.mp hmem2 with hin' | hin'
        · exact absurd (hnflabel _ hin') hne1
        · exact hin'
      obtain ⟨h1, h2⟩ := hAbs'.2 hin
      exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
  · -- (d) frozenness/exhaustion at the extended state.
    intro sf' hsfmem' hshape' houtdeg'
    rcases List.mem_append.mp hsfmem' with hnew | hold
    · exfalso
      have hlbl := hnflabel sf' hnew
      have hzero : outDeg (acc.addEdge w w') w' = 0 :=
        outDeg_addEdge_freshTarget_eq_zero b acc w hInv hw_ne
      rw [hlbl, hzero] at houtdeg'
      exact houtdeg' rfl
    · have hOld := (modalNonMintCandidates_eq_nil_iff φ₀ keys b e acc).mp hmint sf' hold
      rcases hOld with hms' | he' | hna'
      · exact absurd hms' (by simp [hshape'])
      · exact Or.inl he'
      · right
        by_cases hbd : (sf'.sign = .pos ∧ ∃ χ, sf'.formula = .box χ) ∨
            (sf'.sign = .neg ∧ ∃ χ, sf'.formula = .diamond χ)
        · rcases hbd with ⟨hs, χ, hf⟩ | ⟨hs, χ, hf⟩
          · have hsfeq : sf' = (⟨.pos, .box χ, sf'.label⟩ :
                SignedFormula (Proposition Atom) WorldIndex) := by
              rcases sf' with ⟨s', f', l'⟩; simp_all
            by_cases hlw : sf'.label = w
            · rw [hsfeq, modalApplyOneS4Keyed_boxPos_eq_S4Rules, hlw]
              have hmemb : (⟨.pos, .box χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
                  ∈ b := by rw [← hlw, ← hsfeq]; exact hold
              obtain ⟨hcompK, hcompFour⟩ := mem_mintPayload_boxPos_compensation b χ w hmemb
              refine modalApplyOneS4Rules_boxPos_fst_notApplicable_of_mint φ₀ b nf acc χ w w'
                hmemb hSat ?_ ?_
              · rw [hnfdef]; simp only [List.mem_append, List.mem_cons]
                exact Or.inl (Or.inl (Or.inr hcompK))
              · rw [hnfdef]; simp only [List.mem_append, List.mem_cons]
                exact Or.inr hcompFour
            · rw [hsfeq, modalApplyOneS4Keyed_boxPos_eq_S4Rules]
              rw [hsfeq, modalApplyOneS4Keyed_boxPos_eq_S4Rules] at hna'
              rw [modalApplyOneS4Rules_boxPos_fst_addEdge_of_ne φ₀ (nf ++ b) acc χ w w'
                sf'.label hlw]
              exact modalApplyOneS4Rules_boxPos_notApplicable_growth b nf acc χ sf'.label hna'
          · have hsfeq : sf' = (⟨.neg, .diamond χ, sf'.label⟩ :
                SignedFormula (Proposition Atom) WorldIndex) := by
              rcases sf' with ⟨s', f', l'⟩; simp_all
            by_cases hlw : sf'.label = w
            · rw [hsfeq, modalApplyOneS4Keyed_diaNeg_eq_S4Rules, hlw]
              have hmemb : (⟨.neg, .diamond χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
                  ∈ b := by rw [← hlw, ← hsfeq]; exact hold
              obtain ⟨hcompK, hcompFour⟩ := mem_mintPayload_diaNeg_compensation b χ w hmemb
              refine modalApplyOneS4Rules_diaNeg_fst_notApplicable_of_mint φ₀ b nf acc χ w w'
                hmemb hSat ?_ ?_
              · rw [hnfdef]; simp only [List.mem_append, List.mem_cons]
                exact Or.inl (Or.inr hcompK)
              · rw [hnfdef]; simp only [List.mem_append, List.mem_cons]
                exact Or.inr hcompFour
            · rw [hsfeq, modalApplyOneS4Keyed_diaNeg_eq_S4Rules]
              rw [hsfeq, modalApplyOneS4Keyed_diaNeg_eq_S4Rules] at hna'
              rw [modalApplyOneS4Rules_diaNeg_fst_addEdge_of_ne φ₀ (nf ++ b) acc χ w w'
                sf'.label hlw]
              exact modalApplyOneS4Rules_diaNeg_notApplicable_growth b nf acc χ sf'.label hna'
        · have hnb : ∀ χ, sf'.formula ≠ .box χ := by
            intro χ hfeq
            apply hbd
            rcases hs : sf'.sign with _ | _
            · exact Or.inl ⟨rfl, χ, hfeq⟩
            · exact absurd hshape' (by
                rcases sf' with ⟨s', f', l'⟩
                simp_all [modalMintShape])
          have hnd : ∀ χ, sf'.formula ≠ .diamond χ := by
            intro χ hfeq
            apply hbd
            rcases hs : sf'.sign with _ | _
            · exact absurd hshape' (by
                rcases sf' with ⟨s', f', l'⟩
                simp_all [modalMintShape])
            · exact Or.inr ⟨rfl, χ, hfeq⟩
          have hna'' : (modalApplyOne sf' b acc).1 = .notApplicable := by
            rwa [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf'.sign sf'.formula
              sf'.label hnb hnd b acc, show (⟨sf'.sign, sf'.formula, sf'.label⟩ :
                SignedFormula (Proposition Atom) WorldIndex) = sf' from rfl] at hna'
          have hbranch : (modalApplyOne sf' (nf ++ b) acc).fst = (modalApplyOne sf' b acc).fst :=
            modalApplyOne_fst_eq_of_not_box_diamond sf' (nf ++ b) b acc hnb hnd
          have haccindep : (modalApplyOne sf' (nf ++ b) (acc.addEdge w w')).fst =
              (modalApplyOne sf' (nf ++ b) acc).fst :=
            modalApplyOne_fst_eq_of_not_boxPos_diaNeg sf' (nf ++ b) (acc.addEdge w w') acc
              (not_or.mp hbd)
          rw [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf'.sign sf'.formula
            sf'.label hnb hnd (nf ++ b) (acc.addEdge w w'), show (⟨sf'.sign, sf'.formula,
              sf'.label⟩ : SignedFormula (Proposition Atom) WorldIndex) = sf' from rfl,
            haccindep, hbranch]
          exact hna''

/-- **Mint-unblocked, diamond-positive arm: `S4RedirectSoundInv` preservation (Phase 7.6).**
Direct dual of `S4RedirectSoundInv_boxNeg_mint`, for a keyed-guard unblocked diamond-positive
mint (`T(◇ψ)@w`). Reuses `modalApplyOneS4Keyed_diaPos_mint_sat`'s pointwise-extension
construction for (b), and the SAME `mem_mintPayload_{boxPos,diaNeg}_compensation`/
`modalApplyOneS4Rules_{boxPos,diaNeg}_fst_notApplicable_of_mint` lemmas for (d)'s same-world
sub-case, since a co-located persistent formula's compensation does not depend on which mint
shape triggered the fresh successor. -/
theorem S4RedirectSoundInv_diaPos_mint (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (Er : List (WorldIndex × WorldIndex))
    (ψ : Proposition Atom) (w : WorldIndex)
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er)
    (hSat : modalS4Saturated φ₀ b acc)
    (hmint : modalNonMintCandidates φ₀ keys b e acc = [])
    (hInv : accFreshInv b acc)
    (hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ w = none)
    (hsfmem : (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ nf, modalApplyOneS4Keyed φ₀ keys (⟨.pos, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear nf, acc.addEdge w (modalNextWorld b)) ∧
      S4RedirectSoundInv φ₀ (nf ++ b) e (acc.addEdge w (modalNextWorld b)) keys Er := by
  obtain ⟨hEr, hbSem, hAbs, -⟩ := hinv
  have hAOeq := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ w hblock
  rw [hAOeq, modalApplyOneS4KeyedMint_diaPos_eq_S4]
  set w' := modalNextWorld b with hw'def
  set nf : List (SignedFormula (Proposition Atom) WorldIndex) :=
    (((⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
        (boxPositivesOf b).filterMap (fun (ψ', src) =>
          if src == w then
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ', w'⟩
            if b.any (· == sf') then none else some sf'
          else none) ++
        b.filterMap (fun sf' =>
          if sf'.sign == .neg && sf'.label == w then
            match sf'.formula with
            | .diamond ψ' =>
              let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ', w'⟩
              if b.any (· == prop) then none else some prop
            | _ => none
          else none)) ++ boxPlusExtraS4 b w) with hnfdef
  have hw_ne : w ≠ w' := Nat.ne_of_lt (modalNextWorld_gt b _ hsfmem)
  have hnflabel : ∀ x ∈ nf, x.label = w' := by
    rw [hnfdef]
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact mintGroup_label_eq_freshWorld b w .pos ψ x hx1
    · exact boxPlusExtraS4_label_eq_freshWorld b w x hx2
  refine ⟨nf, rfl, ?_, ?_, ?_, ?_⟩
  · -- (a) every ghost edge is a recorded edge in the extended `acc`; `Er` unchanged.
    intro p hp
    exact hasEdge_addEdge_mono_gate0 (hEr p hp)
  · -- (b) semantic conjunct: the SAME pointwise-extension construction, weakened edge clause.
    obtain ⟨W, m, f, hFC, hrel, hb⟩ := hbSem
    have htrans := hFC.2
    have hposdia : Satisfies m (f w) (Proposition.diamond ψ) := (hb _ hsfmem).1 rfl
    simp only [Satisfies] at hposdia
    obtain ⟨ww, hwwr, hwwψ⟩ := hposdia
    let f' : WorldIndex → W := fun n => if n = w' then ww else f n
    refine ⟨W, m, f', hFC, ?_, ?_⟩
    · intro u v hedge
      simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
        Bool.or_eq_true] at hedge
      rcases hedge with hedge | hedge
      · simp only [Bool.and_eq_true, beq_iff_eq] at hedge
        obtain ⟨rfl, rfl⟩ := hedge
        right
        rw [show f' w = f w from if_neg hw_ne, show f' w' = ww from if_pos rfl]
        exact hwwr
      · have huw' : u ≠ w' := by
          intro heq'
          have hfresh := (hInv u v hedge).1
          rw [heq'] at hfresh
          exact Nat.lt_irrefl _ hfresh
        have hvw' : v ≠ w' := by
          intro heq'
          have hfresh := (hInv u v hedge).2
          rw [heq'] at hfresh
          exact Nat.lt_irrefl _ hfresh
        rcases hrel u v hedge with hErmem | hr
        · exact Or.inl hErmem
        · right
          simp only [f', if_neg huw', if_neg hvw']
          exact hr
    · intro sf' hmem'
      rw [hnfdef] at hmem'
      simp only [List.mem_append, List.mem_cons] at hmem'
      rcases hmem' with (((rfl | hmem_bp) | hmem_dn) | hmem_bpe) | hmem_old
      · refine ⟨fun _ => ?_, fun h => by simp at h⟩
        simp only [f', if_pos rfl]
        exact hwwψ
      · simp only [List.mem_filterMap] at hmem_bp
        obtain ⟨⟨ψ'', src⟩, hpairMem, hsf'_from⟩ := hmem_bp
        split_ifs at hsf'_from with hsrceq hinb
        simp only [Option.some.injEq] at hsf'_from
        subst hsf'_from
        simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
        obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
        split_ifs at hbsfeq with hbsfpos
        cases hbf : bsf.formula with
        | box ψ''' =>
          rw [hbf] at hbsfeq
          simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
          obtain ⟨hψeq, hsrc⟩ := hbsfeq
          have hsrc_w : bsf.label = w := by rw [hsrc]; simpa using hsrceq
          have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
          rw [hbf, hsrc_w] at hbox_sat
          simp only [Satisfies] at hbox_sat
          refine ⟨fun _ => ?_, fun h => by simp at h⟩
          simp only [f', if_pos rfl]
          rw [← hψeq]
          exact hbox_sat ww hwwr
        | _ => simp [hbf] at hbsfeq
      · simp only [List.mem_filterMap] at hmem_dn
        obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
        by_cases hbsfsign : (bsf.sign == Sign.neg && bsf.label == w) = true
        · rw [if_pos hbsfsign] at hbsfprop
          cases hbf : bsf.formula with
          | diamond ψ''' =>
            simp only [hbf] at hbsfprop
            by_cases hinb :
                (b.any (· == (⟨.neg, ψ''', w'⟩ : SignedFormula (Proposition Atom) WorldIndex)))
                  = true
            · rw [if_pos hinb] at hbsfprop; simp at hbsfprop
            · rw [if_neg hinb] at hbsfprop
              simp only [Option.some.injEq] at hbsfprop
              subst hbsfprop
              have hsign : bsf.sign = .neg ∧ bsf.label = w := by
                simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
                exact hbsfsign
              have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
              rw [hbf, hsign.2] at hdiaNeg
              simp only [Satisfies] at hdiaNeg
              push Not at hdiaNeg
              refine ⟨fun h => by simp at h, fun _ => ?_⟩
              simp only [f', if_pos rfl]
              exact hdiaNeg ww hwwr
          | _ => simp [hbf] at hbsfprop
        · rw [if_neg hbsfsign] at hbsfprop; simp at hbsfprop
      · exact boxPlusExtraS4_sat m f htrans b w hb ww hwwr sf' hmem_bpe
      · have hlabel_ne : sf'.label ≠ w' := Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
        have hf'_eq : f' sf'.label = f sf'.label := by simp only [f', if_neg hlabel_ne]
        constructor
        · intro hsign; rw [hf'_eq]; exact (hb sf' hmem_old).1 hsign
        · intro hsign; rw [hf'_eq]; exact (hb sf' hmem_old).2 hsign
  · -- (c) syntactic absorption: old ghost edges (`Er` unchanged) inherit from `hAbs`, since every
    -- ghost-edge endpoint is `< w'` (freshness) while every `nf`-formula's label is exactly `w'`.
    intro p hp χ
    have hne1 : p.1 ≠ w' := Nat.ne_of_lt (hInv p.1 p.2 (hEr p hp)).1
    have hAbs' := hAbs p hp χ
    refine ⟨fun hmem1 => ?_, fun hmem2 => ?_⟩
    · have hin : (⟨.pos, .box χ, p.1⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        rcases List.mem_append.mp hmem1 with hin' | hin'
        · exact absurd (hnflabel _ hin') hne1
        · exact hin'
      obtain ⟨h1, h2⟩ := hAbs'.1 hin
      exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
    · have hin : (⟨.neg, .diamond χ, p.1⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        rcases List.mem_append.mp hmem2 with hin' | hin'
        · exact absurd (hnflabel _ hin') hne1
        · exact hin'
      obtain ⟨h1, h2⟩ := hAbs'.2 hin
      exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
  · -- (d) frozenness/exhaustion at the extended state.
    intro sf' hsfmem' hshape' houtdeg'
    rcases List.mem_append.mp hsfmem' with hnew | hold
    · exfalso
      have hlbl := hnflabel sf' hnew
      have hzero : outDeg (acc.addEdge w w') w' = 0 :=
        outDeg_addEdge_freshTarget_eq_zero b acc w hInv hw_ne
      rw [hlbl, hzero] at houtdeg'
      exact houtdeg' rfl
    · have hOld := (modalNonMintCandidates_eq_nil_iff φ₀ keys b e acc).mp hmint sf' hold
      rcases hOld with hms' | he' | hna'
      · exact absurd hms' (by simp [hshape'])
      · exact Or.inl he'
      · right
        by_cases hbd : (sf'.sign = .pos ∧ ∃ χ, sf'.formula = .box χ) ∨
            (sf'.sign = .neg ∧ ∃ χ, sf'.formula = .diamond χ)
        · rcases hbd with ⟨hs, χ, hf⟩ | ⟨hs, χ, hf⟩
          · have hsfeq : sf' = (⟨.pos, .box χ, sf'.label⟩ :
                SignedFormula (Proposition Atom) WorldIndex) := by
              rcases sf' with ⟨s', f', l'⟩; simp_all
            by_cases hlw : sf'.label = w
            · rw [hsfeq, modalApplyOneS4Keyed_boxPos_eq_S4Rules, hlw]
              have hmemb : (⟨.pos, .box χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
                  ∈ b := by rw [← hlw, ← hsfeq]; exact hold
              obtain ⟨hcompK, hcompFour⟩ := mem_mintPayload_boxPos_compensation b χ w hmemb
              refine modalApplyOneS4Rules_boxPos_fst_notApplicable_of_mint φ₀ b nf acc χ w w'
                hmemb hSat ?_ ?_
              · rw [hnfdef]; simp only [List.mem_append, List.mem_cons]
                exact Or.inl (Or.inl (Or.inr hcompK))
              · rw [hnfdef]; simp only [List.mem_append, List.mem_cons]
                exact Or.inr hcompFour
            · rw [hsfeq, modalApplyOneS4Keyed_boxPos_eq_S4Rules]
              rw [hsfeq, modalApplyOneS4Keyed_boxPos_eq_S4Rules] at hna'
              rw [modalApplyOneS4Rules_boxPos_fst_addEdge_of_ne φ₀ (nf ++ b) acc χ w w'
                sf'.label hlw]
              exact modalApplyOneS4Rules_boxPos_notApplicable_growth b nf acc χ sf'.label hna'
          · have hsfeq : sf' = (⟨.neg, .diamond χ, sf'.label⟩ :
                SignedFormula (Proposition Atom) WorldIndex) := by
              rcases sf' with ⟨s', f', l'⟩; simp_all
            by_cases hlw : sf'.label = w
            · rw [hsfeq, modalApplyOneS4Keyed_diaNeg_eq_S4Rules, hlw]
              have hmemb : (⟨.neg, .diamond χ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
                  ∈ b := by rw [← hlw, ← hsfeq]; exact hold
              obtain ⟨hcompK, hcompFour⟩ := mem_mintPayload_diaNeg_compensation b χ w hmemb
              refine modalApplyOneS4Rules_diaNeg_fst_notApplicable_of_mint φ₀ b nf acc χ w w'
                hmemb hSat ?_ ?_
              · rw [hnfdef]; simp only [List.mem_append, List.mem_cons]
                exact Or.inl (Or.inr hcompK)
              · rw [hnfdef]; simp only [List.mem_append, List.mem_cons]
                exact Or.inr hcompFour
            · rw [hsfeq, modalApplyOneS4Keyed_diaNeg_eq_S4Rules]
              rw [hsfeq, modalApplyOneS4Keyed_diaNeg_eq_S4Rules] at hna'
              rw [modalApplyOneS4Rules_diaNeg_fst_addEdge_of_ne φ₀ (nf ++ b) acc χ w w'
                sf'.label hlw]
              exact modalApplyOneS4Rules_diaNeg_notApplicable_growth b nf acc χ sf'.label hna'
        · have hnb : ∀ χ, sf'.formula ≠ .box χ := by
            intro χ hfeq
            apply hbd
            rcases hs : sf'.sign with _ | _
            · exact Or.inl ⟨rfl, χ, hfeq⟩
            · exact absurd hshape' (by
                rcases sf' with ⟨s', f', l'⟩
                simp_all [modalMintShape])
          have hnd : ∀ χ, sf'.formula ≠ .diamond χ := by
            intro χ hfeq
            apply hbd
            rcases hs : sf'.sign with _ | _
            · exact absurd hshape' (by
                rcases sf' with ⟨s', f', l'⟩
                simp_all [modalMintShape])
            · exact Or.inr ⟨rfl, χ, hfeq⟩
          have hna'' : (modalApplyOne sf' b acc).1 = .notApplicable := by
            rwa [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf'.sign sf'.formula
              sf'.label hnb hnd b acc, show (⟨sf'.sign, sf'.formula, sf'.label⟩ :
                SignedFormula (Proposition Atom) WorldIndex) = sf' from rfl] at hna'
          have hbranch : (modalApplyOne sf' (nf ++ b) acc).fst = (modalApplyOne sf' b acc).fst :=
            modalApplyOne_fst_eq_of_not_box_diamond sf' (nf ++ b) b acc hnb hnd
          have haccindep : (modalApplyOne sf' (nf ++ b) (acc.addEdge w w')).fst =
              (modalApplyOne sf' (nf ++ b) acc).fst :=
            modalApplyOne_fst_eq_of_not_boxPos_diaNeg sf' (nf ++ b) (acc.addEdge w w') acc
              (not_or.mp hbd)
          rw [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf'.sign sf'.formula
            sf'.label hnb hnd (nf ++ b) (acc.addEdge w w'), show (⟨sf'.sign, sf'.formula,
              sf'.label⟩ : SignedFormula (Proposition Atom) WorldIndex) = sf' from rfl,
            haccindep, hbranch]
          exact hna''

/-! ## Phase 7.7: 4-Rule Arms Restated Against `S4RedirectSoundInv`

Closes the "genuine open question" left by the Phase 7.7 first/second dispatches (see the plan
file's `#### Phase 7.7 Progress Record` subsections): neither route considered there (a new
per-world saturation invariant tracking `outDeg` at a recorded successor, or weakening conjunct
(d)) is needed. Old conjunct (d), applied directly to the firing box-positive/diamond-negative
candidate itself -- exactly the way `S4RedirectSoundInv_notBoxDia_step` (Phase 7.5) already uses
it via `hFroz`, and unaffected by the candidate's shape -- forces `outDeg acc lbl = 0`: `lbl`
(the candidate's own world) has NO recorded successor at the moment the candidate fires. Since
both the K-layer (`boxPropagation`/its diamond-negative dual) and the 4-layer
(`modalFourBoxProp`/`modalFourDiaNegProp`) range over `acc.successorsOf lbl`, zero out-degree
makes both vacuously empty, so `modalApplyOneS4Rules` at these two shapes reduces to *exactly*
the T-self layer (`modalTBoxSelf`/`modalTDiaNegSelf`) -- unconditional on `acc`, landing its (at
most one) output formula at `lbl` itself, the SAME world as the firing candidate. This is
exactly the shape Phase 7.5 already discharges (c)/(d) for. `S4RedirectSoundInv` itself is
untouched by this argument, so Phases 7.2, 7.3, 7.5, 7.6 need no re-verification. -/

omit [Hashable Atom] in
/-- Zero out-degree collapses the successor list to `[]` (restates `outDeg`'s own definition,
`FmpMeasure.lean:768`, `(acc.successorsOf w).length`). -/
lemma successorsOf_eq_nil_of_outDeg_eq_zero (acc : Accessibility) (w : WorldIndex)
    (h : outDeg acc w = 0) : acc.successorsOf w = [] :=
  List.length_eq_zero_iff.mp h

omit [Hashable Atom] in
/-- At zero out-degree, `modalApplyOneS4Rules` at a box-positive shape collapses to exactly the
T-self layer: the K-layer (`boxPropagation`) and the 4-layer (`modalFourBoxProp`) both range
over `acc.successorsOf lbl`, forced empty by `h`. -/
lemma modalApplyOneS4Rules_boxPos_eq_of_outDeg_zero
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (lbl : WorldIndex) (h : outDeg acc lbl = 0) :
    (modalApplyOneS4Rules (⟨.pos, .box φ, lbl⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (if (modalTBoxSelf b φ lbl).isEmpty then .notApplicable
        else .persistent (modalTBoxSelf b φ lbl)) := by
  have hsucc : acc.successorsOf lbl = [] := successorsOf_eq_nil_of_outDeg_eq_zero acc lbl h
  have hbp : boxPropagation b acc φ lbl = [] := by unfold boxPropagation; rw [hsucc]; rfl
  have hfour : modalFourBoxProp b acc φ lbl = [] := by unfold modalFourBoxProp; rw [hsucc]; rfl
  have hK : (modalApplyOne (⟨.pos, .box φ, lbl⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst = .notApplicable := by
    have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
        = false := by
      rw [tryAllPropRules_pos]
      simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
    simp only [modalApplyOne, htry, Bool.false_eq_true, if_false, hbp, List.isEmpty_nil, if_true]
  rw [modalApplyOneS4Rules_boxPos_fst, modalApplyOneT_boxPos_fst, hK]
  split_ifs with hemp <;> simp_all

omit [Hashable Atom] in
/-- Dual of `modalApplyOneS4Rules_boxPos_eq_of_outDeg_zero` for the diamond-negative shape. -/
lemma modalApplyOneS4Rules_diaNeg_eq_of_outDeg_zero
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (lbl : WorldIndex) (h : outDeg acc lbl = 0) :
    (modalApplyOneS4Rules (⟨.neg, .diamond φ, lbl⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (if (modalTDiaNegSelf b φ lbl).isEmpty then .notApplicable
        else .persistent (modalTDiaNegSelf b φ lbl)) := by
  have hsucc : acc.successorsOf lbl = [] := successorsOf_eq_nil_of_outDeg_eq_zero acc lbl h
  have hdp : (acc.successorsOf lbl).filterMap (fun w' =>
      let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
      if b.any (· == sf') then none else some sf') = [] := by rw [hsucc]; rfl
  have hfour : modalFourDiaNegProp b acc φ lbl = [] := by
    unfold modalFourDiaNegProp; rw [hsucc]; rfl
  have hK : (modalApplyOne (⟨.neg, .diamond φ, lbl⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst = .notApplicable := by
    have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
        = false := by
      rw [tryAllPropRules_neg]
      simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
    simp only [modalApplyOne, htry, Bool.false_eq_true, if_false, hdp, List.isEmpty_nil, if_true]
  rw [modalApplyOneS4Rules_diaNeg_fst, modalApplyOneT_diamondNeg_fst, hK]
  split_ifs with hemp <;> simp_all

/-- **4-rule, box-positive arm restated against `S4RedirectSoundInv` (Phase 7.7).** At a
primary-scan step firing a box-positive candidate `⟨.pos, .box φ, lbl⟩ ∈
modalNonMintCandidates`, old conjunct (d) applied directly to the candidate forces
`outDeg acc lbl = 0` (`houtdeg0`, the identical argument to `S4RedirectSoundInv_notBoxDia_step`'s
own, Phase 7.5). Zero out-degree collapses the K-layer and 4-layer
(`modalApplyOneS4Rules_boxPos_eq_of_outDeg_zero`), so the only possible output is the T-self
content `modalTBoxSelf b φ lbl`, landing at `lbl` itself -- the SAME world as the firing
candidate. This arm needs no ghost-edge reasoning at all: `acc`/`Er` are untouched, and the
semantic witness needs only reflexivity (`hFC.1.refl`), not `hacc`. -/
theorem S4RedirectSoundInv_boxPos_step (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (Er : List (WorldIndex × WorldIndex))
    (φ : Proposition Atom) (lbl : WorldIndex)
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er)
    (hcand : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalNonMintCandidates φ₀ keys b e acc) :
    ∃ nf : List (SignedFormula (Proposition Atom) WorldIndex),
      (match (modalApplyOneS4Keyed φ₀ keys
          (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).1 with
        | .linear fs => nf = fs
        | .branching brs => nf ∈ brs
        | .persistent fs => nf = fs
        | .notApplicable => False) ∧
      S4RedirectSoundInv φ₀ (nf ++ b)
        ((⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) :: e) acc keys Er
    := by
  obtain ⟨hEr, hSat, hAbs, hFroz⟩ := hinv
  obtain ⟨W, m, f, hFC, hacc, hbsat⟩ := hSat
  have hmemb : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
    modalNonMintCandidates_subset φ₀ keys b e acc hcand
  have hnotexp : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ e :=
    modalNonMintCandidates_not_mem_expanded φ₀ keys b e acc _ hcand
  have hmintapp : modalMintShape (⟨.pos, .box φ, lbl⟩ :
        SignedFormula (Proposition Atom) WorldIndex) = false ∧
      (modalApplyOneS4Keyed φ₀ keys (⟨.pos, .box φ, lbl⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).1.isApplicable = true := by
    unfold modalNonMintCandidates at hcand
    have hpred := (List.mem_filter.mp hcand).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpred
    exact ⟨hpred.1.1, hpred.2⟩
  obtain ⟨hmshape, happ⟩ := hmintapp
  -- Old conjunct (d), instantiated at the fired candidate: forces `outDeg acc lbl = 0`.
  have houtdeg0 : outDeg acc lbl = 0 := by
    by_contra hne
    rcases hFroz (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex)
        hmemb hmshape hne with h1 | h2
    · exact hnotexp h1
    · rw [h2] at happ
      simp [RuleResult.isApplicable] at happ
  -- No ghost edge is sourced at `lbl`.
  have hnoghostsrc : ∀ p ∈ Er, p.1 ≠ lbl := by
    intro p hp heq
    exact outDeg_ne_zero_of_hasEdge acc p.1 p.2 (hEr p hp) (heq ▸ houtdeg0)
  -- The rule's own output, at zero out-degree, is exactly the T-self layer.
  have hred : (modalApplyOneS4Keyed φ₀ keys (⟨.pos, .box φ, lbl⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).1 =
      (if (modalTBoxSelf b φ lbl).isEmpty then .notApplicable
        else .persistent (modalTBoxSelf b φ lbl)) := by
    rw [modalApplyOneS4Keyed_boxPos_eq_S4Rules]
    exact modalApplyOneS4Rules_boxPos_eq_of_outDeg_zero b acc φ lbl houtdeg0
  -- `modalTBoxSelf b φ lbl` is nonempty (else the candidate is not applicable).
  have hnonempty : ¬ (modalTBoxSelf b φ lbl).isEmpty := by
    intro hemp
    rw [hred, if_pos hemp] at happ
    simp [RuleResult.isApplicable] at happ
  have hres : (modalApplyOneS4Keyed φ₀ keys (⟨.pos, .box φ, lbl⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).1 =
      .persistent (modalTBoxSelf b φ lbl) := by rw [hred, if_neg hnonempty]
  -- Every element of the new content lands at `lbl`, the SAME world as the firing candidate.
  have hnflabel : ∀ sf' ∈ modalTBoxSelf b φ lbl, sf'.label = lbl := by
    intro sf' hsf'
    simp only [modalTBoxSelf] at hsf'
    split_ifs at hsf' with hcase
    · simp at hsf'
    · simp only [List.mem_singleton] at hsf'; subst hsf'; rfl
  -- The T-self content's own semantic soundness: reflexivity, no `hacc` needed.
  have hnfsat : ∀ sf' ∈ modalTBoxSelf b φ lbl, sfSat m f sf' := by
    intro sf' hsf'
    simp only [modalTBoxSelf] at hsf'
    split_ifs at hsf' with hcase
    · simp at hsf'
    · simp only [List.mem_singleton] at hsf'
      subst hsf'
      have hbox : Satisfies m (f lbl) (.box φ) := (hbsat _ hmemb).1 rfl
      simp only [Satisfies] at hbox
      exact sfSat_pos m f φ lbl (hbox (f lbl) (hFC.1.refl (f lbl)))
  refine ⟨modalTBoxSelf b φ lbl, by rw [hres], hEr, ⟨W, m, f, hFC, hacc, ?_⟩, ?_, ?_⟩
  · intro sf' hmem'
    rcases List.mem_append.mp hmem' with hnew | hold
    · exact hnfsat sf' hnew
    · exact hbsat sf' hold
  · intro p hp χ
    have hnesrc := hnoghostsrc p hp
    have hsub : ∀ sf' ∈ (modalTBoxSelf b φ lbl ++ b), sf' ∈ b ∨ sf'.label = lbl :=
      fun sf' hmem' => (List.mem_append.mp hmem').elim (fun h => Or.inr (hnflabel sf' h)) Or.inl
    have hAbs' := hAbs p hp χ
    refine ⟨fun hmem1 => ?_, fun hmem2 => ?_⟩
    · rcases hsub _ hmem1 with hin | hlbl
      · obtain ⟨h1, h2⟩ := hAbs'.1 hin
        exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
      · exact absurd hlbl hnesrc
    · rcases hsub _ hmem2 with hin | hlbl
      · obtain ⟨h1, h2⟩ := hAbs'.2 hin
        exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
      · exact absurd hlbl hnesrc
  · intro sf' hmem' hmshape' houtdeg'
    rcases List.mem_append.mp hmem' with hnew | hold
    · exfalso
      have hlbl' := hnflabel sf' hnew
      rw [hlbl', houtdeg0] at houtdeg'
      exact houtdeg' rfl
    · rcases eq_or_ne sf' (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex)
          with rfl | hne'
      · exact Or.inl List.mem_cons_self
      · rcases hFroz sf' hold hmshape' houtdeg' with h1 | h2
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr
            (modalApplyOneS4Keyed_notApplicable_growth φ₀ keys sf' b (modalTBoxSelf b φ lbl) acc
              h2)

/-- Dual of `S4RedirectSoundInv_boxPos_step` for the diamond-negative shape. -/
theorem S4RedirectSoundInv_diaNeg_step (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (Er : List (WorldIndex × WorldIndex))
    (φ : Proposition Atom) (lbl : WorldIndex)
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er)
    (hcand : (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalNonMintCandidates φ₀ keys b e acc) :
    ∃ nf : List (SignedFormula (Proposition Atom) WorldIndex),
      (match (modalApplyOneS4Keyed φ₀ keys
          (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).1 with
        | .linear fs => nf = fs
        | .branching brs => nf ∈ brs
        | .persistent fs => nf = fs
        | .notApplicable => False) ∧
      S4RedirectSoundInv φ₀ (nf ++ b)
        ((⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) :: e) acc keys Er
    := by
  obtain ⟨hEr, hSat, hAbs, hFroz⟩ := hinv
  obtain ⟨W, m, f, hFC, hacc, hbsat⟩ := hSat
  have hmemb : (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
    modalNonMintCandidates_subset φ₀ keys b e acc hcand
  have hnotexp : (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ e :=
    modalNonMintCandidates_not_mem_expanded φ₀ keys b e acc _ hcand
  have hmintapp : modalMintShape (⟨.neg, .diamond φ, lbl⟩ :
        SignedFormula (Proposition Atom) WorldIndex) = false ∧
      (modalApplyOneS4Keyed φ₀ keys (⟨.neg, .diamond φ, lbl⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).1.isApplicable = true := by
    unfold modalNonMintCandidates at hcand
    have hpred := (List.mem_filter.mp hcand).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpred
    exact ⟨hpred.1.1, hpred.2⟩
  obtain ⟨hmshape, happ⟩ := hmintapp
  have houtdeg0 : outDeg acc lbl = 0 := by
    by_contra hne
    rcases hFroz (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex)
        hmemb hmshape hne with h1 | h2
    · exact hnotexp h1
    · rw [h2] at happ
      simp [RuleResult.isApplicable] at happ
  have hnoghostsrc : ∀ p ∈ Er, p.1 ≠ lbl := by
    intro p hp heq
    exact outDeg_ne_zero_of_hasEdge acc p.1 p.2 (hEr p hp) (heq ▸ houtdeg0)
  have hred : (modalApplyOneS4Keyed φ₀ keys (⟨.neg, .diamond φ, lbl⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).1 =
      (if (modalTDiaNegSelf b φ lbl).isEmpty then .notApplicable
        else .persistent (modalTDiaNegSelf b φ lbl)) := by
    rw [modalApplyOneS4Keyed_diaNeg_eq_S4Rules]
    exact modalApplyOneS4Rules_diaNeg_eq_of_outDeg_zero b acc φ lbl houtdeg0
  have hnonempty : ¬ (modalTDiaNegSelf b φ lbl).isEmpty := by
    intro hemp
    rw [hred, if_pos hemp] at happ
    simp [RuleResult.isApplicable] at happ
  have hres : (modalApplyOneS4Keyed φ₀ keys (⟨.neg, .diamond φ, lbl⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).1 =
      .persistent (modalTDiaNegSelf b φ lbl) := by rw [hred, if_neg hnonempty]
  have hnflabel : ∀ sf' ∈ modalTDiaNegSelf b φ lbl, sf'.label = lbl := by
    intro sf' hsf'
    simp only [modalTDiaNegSelf] at hsf'
    split_ifs at hsf' with hcase
    · simp at hsf'
    · simp only [List.mem_singleton] at hsf'; subst hsf'; rfl
  have hnfsat : ∀ sf' ∈ modalTDiaNegSelf b φ lbl, sfSat m f sf' := by
    intro sf' hsf'
    simp only [modalTDiaNegSelf] at hsf'
    split_ifs at hsf' with hcase
    · simp at hsf'
    · simp only [List.mem_singleton] at hsf'
      subst hsf'
      have hdia : ¬ Satisfies m (f lbl) (.diamond φ) := (hbsat _ hmemb).2 rfl
      rw [Satisfies.diamond_iff] at hdia
      push Not at hdia
      exact sfSat_neg m f φ lbl (hdia (f lbl) (hFC.1.refl (f lbl)))
  refine ⟨modalTDiaNegSelf b φ lbl, by rw [hres], hEr, ⟨W, m, f, hFC, hacc, ?_⟩, ?_, ?_⟩
  · intro sf' hmem'
    rcases List.mem_append.mp hmem' with hnew | hold
    · exact hnfsat sf' hnew
    · exact hbsat sf' hold
  · intro p hp χ
    have hnesrc := hnoghostsrc p hp
    have hsub : ∀ sf' ∈ (modalTDiaNegSelf b φ lbl ++ b), sf' ∈ b ∨ sf'.label = lbl :=
      fun sf' hmem' => (List.mem_append.mp hmem').elim (fun h => Or.inr (hnflabel sf' h)) Or.inl
    have hAbs' := hAbs p hp χ
    refine ⟨fun hmem1 => ?_, fun hmem2 => ?_⟩
    · rcases hsub _ hmem1 with hin | hlbl
      · obtain ⟨h1, h2⟩ := hAbs'.1 hin
        exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
      · exact absurd hlbl hnesrc
    · rcases hsub _ hmem2 with hin | hlbl
      · obtain ⟨h1, h2⟩ := hAbs'.2 hin
        exact ⟨List.mem_append.mpr (Or.inr h1), List.mem_append.mpr (Or.inr h2)⟩
      · exact absurd hlbl hnesrc
  · intro sf' hmem' hmshape' houtdeg'
    rcases List.mem_append.mp hmem' with hnew | hold
    · exfalso
      have hlbl' := hnflabel sf' hnew
      rw [hlbl', houtdeg0] at houtdeg'
      exact houtdeg' rfl
    · rcases eq_or_ne sf' (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex)
          with rfl | hne'
      · exact Or.inl List.mem_cons_self
      · rcases hFroz sf' hold hmshape' houtdeg' with h1 | h2
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr
            (modalApplyOneS4Keyed_notApplicable_growth φ₀ keys sf' b (modalTDiaNegSelf b φ lbl)
              acc h2)

/-! ## Phase 7.8: The Dispatcher Theorem Over `modalStepBranchS4KeyedOrdered`

Assembles the five re-wrapped arms (Phases 7.2/7.3, 7.5, 7.6, 7.7) into a single
step-preservation theorem for `S4RedirectSoundInv` against the real driver
`modalStepBranchS4KeyedOrdered`. Three small bridging facts reconcile each arm's own
convenient `(e, keys)` choice with what `modalStepBranchS4KeyedBody` actually threads through:
`S4RedirectSoundInv` is monotone under `e`-growth (only conjunct (d) mentions `e`, and only via
membership), a formula with zero out-degree can be DROPPED from `e` for free (its own (d)
hypothesis is then vacuous), and conjunct (d) is fully independent of `keys` whenever quantified
over a non-mint-shaped formula (`modalApplyOneS4Keyed`'s only `keys`-consulting arms are the two
minting shapes). -/

/-- `S4RedirectSoundInv` is monotone under `e`-growth: only conjunct (d) mentions `e`, and only
via membership (`sf' ∈ e`), so widening `e` to any superset preserves the invariant. Reconciles
a re-wrapped arm's own convenient `e'` (e.g. `sf :: e`) with whichever exact list
`modalStepBranchS4KeyedBody` actually produces (`e ++ [sf]`) -- same elements, different order. -/
lemma S4RedirectSoundInv_weaken_e (φ₀ : Proposition Atom)
    (b e e' : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (Er : List (WorldIndex × WorldIndex))
    (hsub : ∀ x ∈ e, x ∈ e')
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er) :
    S4RedirectSoundInv φ₀ b e' acc keys Er := by
  obtain ⟨ha, hb, hc, hd⟩ := hinv
  refine ⟨ha, hb, hc, ?_⟩
  intro sf hsf hshape houtdeg
  rcases hd sf hsf hshape houtdeg with hin | hna
  · exact Or.inl (hsub _ hin)
  · exact Or.inr hna

/-- `S4RedirectSoundInv`'s conjunct (d) drops a formula from `e` for free once its own
out-degree is zero at the SAME accessibility: (d)'s hypothesis `outDeg acc sf.label ≠ 0` is then
false for `sf` itself, so whether `sf ∈ e` holds is irrelevant to (d)'s conclusion at `sf`.
Reconciles the two 4-rule arms (Phase 7.7), whose real driver output leaves `e` UNCHANGED
(`.persistent` results never mark their firing formula expanded), against their own stated
conclusion at the bigger `sf :: e`. -/
lemma S4RedirectSoundInv_drop_e_of_outDeg_zero (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (Er : List (WorldIndex × WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (houtdeg0 : outDeg acc sf.label = 0)
    (hinv : S4RedirectSoundInv φ₀ b (sf :: e) acc keys Er) :
    S4RedirectSoundInv φ₀ b e acc keys Er := by
  obtain ⟨ha, hb, hc, hd⟩ := hinv
  refine ⟨ha, hb, hc, ?_⟩
  intro sf' hsf' hshape houtdeg'
  rcases hd sf' hsf' hshape houtdeg' with hin | hna
  · rcases List.mem_cons.mp hin with heq | hin'
    · exact absurd houtdeg' (by rw [heq, houtdeg0]; simp)
    · exact Or.inl hin'
  · exact Or.inr hna

/-- `modalApplyOneS4Keyed` at a non-mint-shaped formula is independent of `keys`:
`modalApplyOneS4Keyed`'s only `keys`-consulting match arms are the two MINT shapes
(`.neg,.box`/`.pos,.diamond`), which `hmshape` already excludes, so both sides reduce to the
SAME `keys`-independent call. -/
lemma modalApplyOneS4Keyed_notApplicable_keys_indep (φ₀ : Proposition Atom)
    (keys keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hmshape : modalMintShape sf = false)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4Keyed φ₀ keys' sf b acc := by
  rcases sf with ⟨s, φ, w⟩
  unfold modalMintShape at hmshape
  rcases s with _ | _ <;> rcases φ with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ψ | ψ <;>
    simp_all [modalApplyOneS4Keyed]

/-- Corollary of `modalApplyOneS4Keyed_notApplicable_keys_indep`: `S4RedirectSoundInv`'s
conjunct (d) transports across ANY two `keys` lists, since it only ever quantifies over
non-mint-shaped formulas. Transports the mint-unblocked arms (Phase 7.6, stated at the OLD
`keys`) to the real driver's extended `keys ++ [...]`. -/
lemma S4RedirectSoundInv_keys_transport (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (Er : List (WorldIndex × WorldIndex))
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er) :
    S4RedirectSoundInv φ₀ b e acc keys' Er := by
  obtain ⟨ha, hb, hc, hd⟩ := hinv
  refine ⟨ha, hb, hc, ?_⟩
  intro sf hsf hshape houtdeg
  rcases hd sf hsf hshape houtdeg with hin | hna
  · exact Or.inl hin
  · exact Or.inr (by
      rw [← modalApplyOneS4Keyed_notApplicable_keys_indep φ₀ keys keys' sf hshape b acc]
      exact hna)

/-- **Phase 7.8: the dispatcher theorem.** Assembles the five re-wrapped arms into a single
step-preservation theorem for `S4RedirectSoundInv` over the real driver
`modalStepBranchS4KeyedOrdered`. Threads `modalStepBranchS4KeyedOrdered_cases`'s structural
split: a primary-candidate-scan hit dispatches to the non-mint arms (Phase 7.5's
`S4RedirectSoundInv_notBoxDia_step`, or Phase 7.7's `S4RedirectSoundInv_{boxPos,diaNeg}_step`);
the settled fallback (`modalNonMintCandidates = []`) supplies `modalS4Saturated` via
`modalS4Saturated_of_ordered_settled` and sub-splits on `blockingWorldS4Keyed` into the blocked
mint arms (Phases 7.2/7.3) or the unblocked mint arms (Phase 7.6). `Er` grows only at a blocked
mint step (the new redirect edge); every other arm leaves it untouched. -/
theorem S4RedirectSoundInv_step (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (Er : List (WorldIndex × WorldIndex))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er)
    (hUniv : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hHinv : S4KeyedHintikkaInv φ₀ b e acc keys)
    (hFresh : accFreshInv b acc)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∃ b' ∈ newBs, ∃ e' ∈ newExps, ∃ Er' ⊇ Er, S4RedirectSoundInv φ₀ b' e' newAcc keys' Er' := by
  rcases modalStepBranchS4KeyedOrdered_cases φ₀ b e acc keys newBs newExps newAcc keys' hstep with
    ⟨sf, hcand, hbody⟩ | ⟨hmintEmpty, hfallback⟩
  · -- Primary-scan hit: `sf` is non-mint-shaped.
    have hsfmemb := modalNonMintCandidates_subset φ₀ keys b e acc hcand
    have hsfnote := modalNonMintCandidates_not_mem_expanded φ₀ keys b e acc sf hcand
    have hmintapp : modalMintShape sf = false ∧
        (modalApplyOneS4Keyed φ₀ keys sf b acc).1.isApplicable = true := by
      unfold modalNonMintCandidates at hcand
      have hpred := (List.mem_filter.mp hcand).2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpred
      exact ⟨hpred.1.1, hpred.2⟩
    obtain ⟨hmshape, happ⟩ := hmintapp
    have hany : e.any (· == sf) = false := by
      rw [List.any_eq_false]
      intro x hx heq
      rw [beq_iff_eq] at heq
      subst heq
      exact hsfnote hx
    unfold modalStepBranchS4KeyedBody at hbody
    rw [if_neg (by simp [hany])] at hbody
    rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
    rw [hpair] at hbody
    dsimp only at hbody
    by_cases hbx : ∃ ψ, sf.formula = .box ψ ∧ sf.sign = .pos
    · obtain ⟨ψ, hfeq, hseq⟩ := hbx
      rw [hfeq, hseq] at hbody
      dsimp only at hbody
      have hsfeq : sf = (⟨.pos, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by
        have h : sf = (⟨sf.sign, sf.formula, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) := rfl
        rw [h, hseq, hfeq]
      have hcand' : (⟨.pos, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ∈
          modalNonMintCandidates φ₀ keys b e acc := hsfeq ▸ hcand
      obtain ⟨nf, hshape, hinv'⟩ := S4RedirectSoundInv_boxPos_step φ₀ keys b e acc Er ψ
        sf.label hinv hcand'
      rw [← hsfeq] at hinv'
      rw [← hsfeq, hpair] at hshape
      have hnewAcc0eq : newAcc0 = acc := by
        have := congrArg Prod.snd hpair
        rw [hsfeq, modalApplyOneS4Keyed_boxPos_eq_S4Rules,
          modalApplyOneS4Rules_boxPos_snd_eq_acc] at this
        exact this.symm
      have hsube : ∀ x ∈ (sf :: e), x ∈ e ++ [sf] := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · simp
        · simp [hx']
      rcases hresult : result with fs | brs | fs | -
      · rw [hresult] at hbody hshape
        subst hshape
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
        refine ⟨nf ++ b, ?_, e ++ [sf], ?_, Er, List.Subset.refl Er, ?_⟩
        · rw [← hnewBs]; exact List.mem_singleton_self _
        · rw [← hnewExps]; exact List.mem_singleton_self _
        · rw [← hnewAcc, ← hnewKeys, hnewAcc0eq]
          exact S4RedirectSoundInv_weaken_e φ₀ (nf ++ b) (sf :: e) (e ++ [sf]) acc keys Er hsube
            hinv'
      · rw [hresult] at hbody hshape
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
        refine ⟨nf ++ b, ?_, e ++ [sf], ?_, Er, List.Subset.refl Er, ?_⟩
        · rw [← hnewBs]; exact List.mem_map.mpr ⟨nf, hshape, rfl⟩
        · rw [← hnewExps]; exact List.mem_map.mpr ⟨nf, hshape, rfl⟩
        · rw [← hnewAcc, ← hnewKeys, hnewAcc0eq]
          exact S4RedirectSoundInv_weaken_e φ₀ (nf ++ b) (sf :: e) (e ++ [sf]) acc keys Er hsube
            hinv'
      · rw [hresult] at hbody hshape
        subst hshape
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
        have houtdeg0 : outDeg acc sf.label = 0 := by
          by_contra hne
          obtain ⟨-, -, -, hFroz⟩ := hinv
          rcases hFroz sf hsfmemb hmshape hne with h1 | h2
          · exact hsfnote h1
          · rw [h2] at happ
            simp [RuleResult.isApplicable] at happ
        refine ⟨nf ++ b, ?_, e, ?_, Er, List.Subset.refl Er, ?_⟩
        · rw [← hnewBs]; exact List.mem_singleton_self _
        · rw [← hnewExps]; exact List.mem_singleton_self _
        · rw [← hnewAcc, ← hnewKeys, hnewAcc0eq]
          exact S4RedirectSoundInv_drop_e_of_outDeg_zero φ₀ (nf ++ b) e acc keys Er sf houtdeg0
            hinv'
      · rw [hresult] at hshape
        exact hshape.elim
    · by_cases hdn : ∃ ψ, sf.formula = .diamond ψ ∧ sf.sign = .neg
      · obtain ⟨ψ, hfeq, hseq⟩ := hdn
        rw [hfeq, hseq] at hbody
        dsimp only at hbody
        have hsfeq : sf = (⟨.neg, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) := by
          have h : sf = (⟨sf.sign, sf.formula, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) := rfl
          rw [h, hseq, hfeq]
        have hcand' : (⟨.neg, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈
            modalNonMintCandidates φ₀ keys b e acc := hsfeq ▸ hcand
        obtain ⟨nf, hshape, hinv'⟩ := S4RedirectSoundInv_diaNeg_step φ₀ keys b e acc Er ψ
          sf.label hinv hcand'
        rw [← hsfeq] at hinv'
        rw [← hsfeq, hpair] at hshape
        have hnewAcc0eq : newAcc0 = acc := by
          have := congrArg Prod.snd hpair
          rw [hsfeq, modalApplyOneS4Keyed_diaNeg_eq_S4Rules,
            modalApplyOneS4Rules_diaNeg_snd_eq_acc] at this
          exact this.symm
        have hsube : ∀ x ∈ (sf :: e), x ∈ e ++ [sf] := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · simp
          · simp [hx']
        rcases hresult : result with fs | brs | fs | -
        · rw [hresult] at hbody hshape
          subst hshape
          simp only [Option.some.injEq, Prod.mk.injEq] at hbody
          obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
          refine ⟨nf ++ b, ?_, e ++ [sf], ?_, Er, List.Subset.refl Er, ?_⟩
          · rw [← hnewBs]; exact List.mem_singleton_self _
          · rw [← hnewExps]; exact List.mem_singleton_self _
          · rw [← hnewAcc, ← hnewKeys, hnewAcc0eq]
            exact S4RedirectSoundInv_weaken_e φ₀ (nf ++ b) (sf :: e) (e ++ [sf]) acc keys Er
              hsube hinv'
        · rw [hresult] at hbody hshape
          simp only [Option.some.injEq, Prod.mk.injEq] at hbody
          obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
          refine ⟨nf ++ b, ?_, e ++ [sf], ?_, Er, List.Subset.refl Er, ?_⟩
          · rw [← hnewBs]; exact List.mem_map.mpr ⟨nf, hshape, rfl⟩
          · rw [← hnewExps]; exact List.mem_map.mpr ⟨nf, hshape, rfl⟩
          · rw [← hnewAcc, ← hnewKeys, hnewAcc0eq]
            exact S4RedirectSoundInv_weaken_e φ₀ (nf ++ b) (sf :: e) (e ++ [sf]) acc keys Er
              hsube hinv'
        · rw [hresult] at hbody hshape
          subst hshape
          simp only [Option.some.injEq, Prod.mk.injEq] at hbody
          obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
          have houtdeg0 : outDeg acc sf.label = 0 := by
            by_contra hne
            obtain ⟨-, -, -, hFroz⟩ := hinv
            rcases hFroz sf hsfmemb hmshape hne with h1 | h2
            · exact hsfnote h1
            · rw [h2] at happ
              simp [RuleResult.isApplicable] at happ
          refine ⟨nf ++ b, ?_, e, ?_, Er, List.Subset.refl Er, ?_⟩
          · rw [← hnewBs]; exact List.mem_singleton_self _
          · rw [← hnewExps]; exact List.mem_singleton_self _
          · rw [← hnewAcc, ← hnewKeys, hnewAcc0eq]
            exact S4RedirectSoundInv_drop_e_of_outDeg_zero φ₀ (nf ++ b) e acc keys Er sf houtdeg0
              hinv'
        · rw [hresult] at hshape
          exact hshape.elim
      · -- Propositional / non-mint: `S4RedirectSoundInv_notBoxDia_step` (Phase 7.5).
        have hnb : ∀ ψ, sf.formula ≠ .box ψ := by
          intro ψ hfeq
          by_cases hs : sf.sign = .pos
          · exact hbx ⟨ψ, hfeq, hs⟩
          · have hsn : sf.sign = .neg := by
              cases h : sf.sign with
              | pos => exact absurd h hs
              | neg => rfl
            exact absurd hmshape (by simp [modalMintShape, hsn, hfeq])
        have hnd : ∀ ψ, sf.formula ≠ .diamond ψ := by
          intro ψ hfeq
          by_cases hs : sf.sign = .neg
          · exact hdn ⟨ψ, hfeq, hs⟩
          · have hsp : sf.sign = .pos := by
              cases h : sf.sign with
              | pos => rfl
              | neg => exact absurd h hs
            exact absurd hmshape (by simp [modalMintShape, hsp, hfeq])
        obtain ⟨nf, hshape, hinv'⟩ := S4RedirectSoundInv_notBoxDia_step φ₀ keys b e acc Er sf
          hnb hnd hinv hcand
        rw [hpair] at hshape
        have hnewAcc0eq : newAcc0 = acc := by
          have heq : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOne sf b acc :=
            modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys sf.sign sf.formula sf.label
              hnb hnd b acc
          have hndsnd : (modalApplyOne sf b acc).snd = acc := by
            unfold modalApplyOne
            simp only
            split_ifs with hpa
            · rfl
            · rcases hsg : sf.sign with _ | _ <;>
                rcases hff : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
                first
                  | rfl
                  | exact absurd hff (hnb ψ)
                  | exact absurd hff (hnd ψ)
          have hsnd := congrArg Prod.snd (heq.symm.trans hpair)
          rw [hndsnd] at hsnd
          exact hsnd.symm
        have hsube : ∀ x ∈ (sf :: e), x ∈ e ++ [sf] := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · simp
          · simp [hx']
        -- Reduce `hbody`'s `keys'`-submatch by fixing `sf`'s concrete (formula, sign), then
        -- finish identically in every one of the ten resulting non-mint shapes.
        rcases hff : sf.formula with p | c | ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ <;>
          first
          | exact absurd hff (hnb _)
          | exact absurd hff (hnd _)
          | (rcases hsg : sf.sign with _ | _ <;>
             (rw [hff, hsg] at hbody
              dsimp only at hbody
              rcases hresult : result with fs | brs | fs | -
              · rw [hresult] at hbody hshape
                subst hshape
                simp only [Option.some.injEq, Prod.mk.injEq] at hbody
                obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
                refine ⟨nf ++ b, ?_, e ++ [sf], ?_, Er, List.Subset.refl Er, ?_⟩
                · rw [← hnewBs]; exact List.mem_singleton_self _
                · rw [← hnewExps]; exact List.mem_singleton_self _
                · rw [← hnewAcc, ← hnewKeys, hnewAcc0eq]
                  exact S4RedirectSoundInv_weaken_e φ₀ (nf ++ b) (sf :: e) (e ++ [sf]) acc keys
                    Er hsube hinv'
              · rw [hresult] at hbody hshape
                simp only [Option.some.injEq, Prod.mk.injEq] at hbody
                obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
                refine ⟨nf ++ b, ?_, e ++ [sf], ?_, Er, List.Subset.refl Er, ?_⟩
                · rw [← hnewBs]; exact List.mem_map.mpr ⟨nf, hshape, rfl⟩
                · rw [← hnewExps]; exact List.mem_map.mpr ⟨nf, hshape, rfl⟩
                · rw [← hnewAcc, ← hnewKeys, hnewAcc0eq]
                  exact S4RedirectSoundInv_weaken_e φ₀ (nf ++ b) (sf :: e) (e ++ [sf]) acc keys
                    Er hsube hinv'
              · rw [hresult] at hbody hshape
                subst hshape
                simp only [Option.some.injEq, Prod.mk.injEq] at hbody
                obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
                have houtdeg0 : outDeg acc sf.label = 0 := by
                  by_contra hne
                  obtain ⟨-, -, -, hFroz⟩ := hinv
                  rcases hFroz sf hsfmemb hmshape hne with h1 | h2
                  · exact hsfnote h1
                  · rw [h2] at happ
                    simp [RuleResult.isApplicable] at happ
                refine ⟨nf ++ b, ?_, e, ?_, Er, List.Subset.refl Er, ?_⟩
                · rw [← hnewBs]; exact List.mem_singleton_self _
                · rw [← hnewExps]; exact List.mem_singleton_self _
                · rw [← hnewAcc, ← hnewKeys, hnewAcc0eq]
                  exact S4RedirectSoundInv_drop_e_of_outDeg_zero φ₀ (nf ++ b) e acc keys Er sf
                    houtdeg0 hinv'
              · rw [hresult] at hshape
                exact hshape.elim))
  · -- Settled fallback: `modalNonMintCandidates = []`, so the selected `sf` is mint-shaped.
    have hSat := modalS4Saturated_of_ordered_settled φ₀ b e acc keys hmintEmpty hHinv
    have hfallback0 := hfallback
    unfold modalStepBranchS4Keyed at hfallback0
    obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hfallback0
    split_ifs at hsf with hexp
    rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
    rw [hpair] at hsf
    dsimp only at hsf
    by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
    · rcases hmint with ⟨hseq, ψ, hfeq⟩ | ⟨hseq, ψ, hfeq⟩
      · -- Mint box-negative shape: Phases 7.2 (blocked) / 7.6 (unblocked).
        have hsfeq : sf = (⟨.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) := by
          have h : sf = (⟨sf.sign, sf.formula, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) := rfl
          rw [h, hseq, hfeq]
        have hsfmem' : (⟨.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        rw [hfeq, hseq] at hsf
        dsimp only at hsf
        rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
        · -- Unblocked mint (Phase 7.6).
          rw [hblock] at hsf
          dsimp only at hsf
          obtain ⟨nf, hAOeq, hinv'⟩ := S4RedirectSoundInv_boxNeg_mint φ₀ keys b e acc Er ψ
            sf.label hinv hSat hmintEmpty hFresh hblock hsfmem'
          have heq2 : (result, newAcc0) =
              (RuleResult.linear nf, acc.addEdge sf.label (modalNextWorld b)) :=
            hpair.symm.trans (hsfeq ▸ hAOeq)
          simp only [Prod.mk.injEq] at heq2
          obtain ⟨hreq, hnaeq⟩ := heq2
          rw [hreq] at hsf
          dsimp only at hsf
          simp only [Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
          refine ⟨nf ++ b, ?_, e ++ [sf], ?_, Er, List.Subset.refl Er, ?_⟩
          · rw [← hnewBs]; exact List.mem_singleton_self _
          · rw [← hnewExps]; exact List.mem_singleton_self _
          · rw [← hnewAcc, ← hnewKeys, hnaeq]
            refine S4RedirectSoundInv_keys_transport φ₀ (nf ++ b) (e ++ [sf])
              (acc.addEdge sf.label (modalNextWorld b)) keys
              (keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg ψ sf.label)]) Er ?_
            exact S4RedirectSoundInv_weaken_e φ₀ (nf ++ b) e (e ++ [sf])
              (acc.addEdge sf.label (modalNextWorld b)) keys Er
              (fun x hx => List.mem_append_left _ hx) hinv'
        · -- Blocked redirect (Phase 7.2).
          rw [hblock] at hsf
          dsimp only at hsf
          have hAOeq := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock
            hblock
          have heq2 : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
            hpair.symm.trans (hsfeq ▸ hAOeq)
          simp only [Prod.mk.injEq] at heq2
          obtain ⟨hreq, hnaeq⟩ := heq2
          rw [hreq] at hsf
          dsimp only at hsf
          simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
          have hinv' := S4RedirectSoundInv_boxNeg_blocked φ₀ b e acc keys Er sf.label wBlock ψ
            hinv hUniv hkL hSat hmintEmpty hblock
          refine ⟨b, ?_, e ++ [sf], ?_, (sf.label, wBlock) :: Er, ?_, ?_⟩
          · rw [← hnewBs]; exact List.mem_singleton_self _
          · rw [← hnewExps]; exact List.mem_singleton_self _
          · intro p hp; exact List.mem_cons_of_mem _ hp
          · rw [← hnewAcc, ← hnewKeys, hnaeq]
            exact S4RedirectSoundInv_weaken_e φ₀ b e (e ++ [sf]) (acc.addEdge sf.label wBlock)
              keys ((sf.label, wBlock) :: Er) (fun x hx => List.mem_append_left _ hx) hinv'
      · -- Mint diamond-positive shape: Phases 7.3 (blocked) / 7.6 (unblocked).
        have hsfeq : sf = (⟨.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) := by
          have h : sf = (⟨sf.sign, sf.formula, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) := rfl
          rw [h, hseq, hfeq]
        have hsfmem' : (⟨.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        rw [hfeq, hseq] at hsf
        dsimp only at hsf
        rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
        · -- Unblocked mint (Phase 7.6).
          rw [hblock] at hsf
          dsimp only at hsf
          obtain ⟨nf, hAOeq, hinv'⟩ := S4RedirectSoundInv_diaPos_mint φ₀ keys b e acc Er ψ
            sf.label hinv hSat hmintEmpty hFresh hblock hsfmem'
          have heq2 : (result, newAcc0) =
              (RuleResult.linear nf, acc.addEdge sf.label (modalNextWorld b)) :=
            hpair.symm.trans (hsfeq ▸ hAOeq)
          simp only [Prod.mk.injEq] at heq2
          obtain ⟨hreq, hnaeq⟩ := heq2
          rw [hreq] at hsf
          dsimp only at hsf
          simp only [Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
          refine ⟨nf ++ b, ?_, e ++ [sf], ?_, Er, List.Subset.refl Er, ?_⟩
          · rw [← hnewBs]; exact List.mem_singleton_self _
          · rw [← hnewExps]; exact List.mem_singleton_self _
          · rw [← hnewAcc, ← hnewKeys, hnaeq]
            refine S4RedirectSoundInv_keys_transport φ₀ (nf ++ b) (e ++ [sf])
              (acc.addEdge sf.label (modalNextWorld b)) keys
              (keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos ψ sf.label)]) Er ?_
            exact S4RedirectSoundInv_weaken_e φ₀ (nf ++ b) e (e ++ [sf])
              (acc.addEdge sf.label (modalNextWorld b)) keys Er
              (fun x hx => List.mem_append_left _ hx) hinv'
        · -- Blocked redirect (Phase 7.3).
          rw [hblock] at hsf
          dsimp only at hsf
          have hAOeq := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock
            hblock
          have heq2 : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
            hpair.symm.trans (hsfeq ▸ hAOeq)
          simp only [Prod.mk.injEq] at heq2
          obtain ⟨hreq, hnaeq⟩ := heq2
          rw [hreq] at hsf
          dsimp only at hsf
          simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
          have hinv' := S4RedirectSoundInv_diaPos_blocked φ₀ b e acc keys Er sf.label wBlock ψ
            hinv hUniv hkL hSat hmintEmpty hblock
          refine ⟨b, ?_, e ++ [sf], ?_, (sf.label, wBlock) :: Er, ?_, ?_⟩
          · rw [← hnewBs]; exact List.mem_singleton_self _
          · rw [← hnewExps]; exact List.mem_singleton_self _
          · intro p hp; exact List.mem_cons_of_mem _ hp
          · rw [← hnewAcc, ← hnewKeys, hnaeq]
            exact S4RedirectSoundInv_weaken_e φ₀ b e (e ++ [sf]) (acc.addEdge sf.label wBlock)
              keys ((sf.label, wBlock) :: Er) (fun x hx => List.mem_append_left _ hx) hinv'
    · -- Contradiction: settled fallback selected a non-mint `sf`, contradicting
      -- `hmintEmpty` (a non-mint applicable, unexpanded formula would be a candidate).
      exfalso
      have hmshape : modalMintShape sf = false := by
        unfold modalMintShape
        rcases hsg : sf.sign with _ | _ <;>
          rcases hff : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
          simp_all
      have happ' : (modalApplyOneS4Keyed φ₀ keys sf b acc).1.isApplicable = true := by
        rw [hpair]
        rcases hresult : result with fs | brs | fs | -
        · simp [RuleResult.isApplicable]
        · simp [RuleResult.isApplicable]
        · simp [RuleResult.isApplicable]
        · rw [hresult] at hsf; simp at hsf
      have hmem : sf ∈ modalNonMintCandidates φ₀ keys b e acc :=
        List.mem_filter.mpr ⟨hsfmem, by simp [hmshape, hexp, happ']⟩
      rw [hmintEmpty] at hmem
      simp at hmem

/-! ## Phase 8: Terminal Payoff — Closed-Branch Contradiction Under the Weakened Predicate

A classically closed branch contradicts `S4RedirectSoundInv`, so the weakening of conjunct (b)
costs nothing at the terminal step of the soundness argument. `modalClosed_unsat`
(`SoundnessStep.lean:92`) needs a `branchSatisfiable b acc'` witness -- an existential model
`(W, m, f)` with BOTH an edge-realization clause (`∀ w w', acc'.hasEdge w w' → m.r (f w) (f
w')`) AND the per-formula `sfSat` clause -- but its own proof body destructures that witness as
`⟨W, m, f, _, hb⟩`, discarding the edge clause immediately and never touching it again. Rather
than reconstructing a *true* edge-realization witness from `S4RedirectSoundInv`'s WEAKENED
conjunct (b) (which only covers non-ghost edges, exactly the obligation this task's whole
reformulation exists to avoid), this phase supplies the edge slot with an unconditionally
vacuous one at `Accessibility.empty` -- no edge, so the implication holds for free -- and reuses
conjunct (b)'s `(W, m, f, hb)` untouched. `isModalClosed b` does not mention `acc` at all, so
`hclosed` transfers to the `Accessibility.empty` call site without any adjustment. This is the
same `Accessibility.empty`-witness idiom already used at several call sites in this file cluster
(e.g. `Soundness.lean:363`, `FrameSoundness.lean:941,3274,4456,4464`). -/

/-- **Phase 8: the terminal payoff.** A classically closed branch contradicts
`S4RedirectSoundInv` at any `(e, acc, keys, Er)`: the weakened edge conjunct (b) still supplies
enough model witness to invoke `modalClosed_unsat`, since that lemma's own proof never consumes
its edge-realization hypothesis. -/
theorem S4RedirectSoundInv_not_isModalClosed (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (Er : List (WorldIndex × WorldIndex))
    (hinv : S4RedirectSoundInv φ₀ b e acc keys Er) :
    isModalClosed b = false := by
  obtain ⟨-, ⟨W, m, f, -, -, hb⟩, -, -⟩ := hinv
  by_contra hclosed
  simp only [Bool.not_eq_false] at hclosed
  exact modalClosed_unsat b hclosed Accessibility.empty
    ⟨W, m, f, fun w w' hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge]),
      hb⟩

/-! ## Phase 9.1: Initialization at the Seed State

The seed state of `modalTableauS4KeyedOrdered` (`b = [F(φ₀)@0]`, `e = []`,
`acc = Accessibility.empty`, `keys = [(0, ∅)]`) satisfies `S4RedirectSoundInv` at `Er = []`
whenever a countermodel of `φ₀` exists: conjuncts (a) and (c) are vacuous over the empty ghost
list, conjunct (d) is vacuous since `Accessibility.empty` gives every world `outDeg = 0`
(no recorded edges at all), and conjunct (b) reduces to the plain, undiluted edge-realization
clause -- the `(w, w') ∈ Er` disjunct never fires since `Er = []`. So at the seed state
`S4RedirectSoundInv` carries EXACTLY the standard undiluted soundness hypothesis, not a diluted
form; this is what licenses Phase 9.2's capstone to conclude genuine `s4Valid`, not a weakened
statement. -/

/-- The seed state's `S4RedirectSoundInv` witness, built from an assumed countermodel of `φ₀`
(a world `f 0` at which `φ₀` fails, in a model satisfying `s4FC`). -/
theorem S4RedirectSoundInv_initial (φ₀ : Proposition Atom)
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (hFC : s4FC m.r) (hnotsat : ¬ Satisfies m (f 0) φ₀) :
    S4RedirectSoundInv φ₀
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      Accessibility.empty
      [((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))] [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp; simp at hp
  · refine ⟨W, m, f, hFC, ?_, ?_⟩
    · intro w w' hedge
      exact absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge])
    · intro sf hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      exact sfSat_neg m f φ₀ 0 hnotsat
  · intro p hp; simp at hp
  · intro sf hsfmem hshape houtdeg
    exact absurd houtdeg (by simp [outDeg, Accessibility.successorsOf, Accessibility.empty])

/-! ## Phase 9.1: The Outer Fuel Induction

The final prerequisite for Phase 9.2's capstone: wrapping Phase 7.8's step theorem
(`S4RedirectSoundInv_step`) and Phase 8's terminal payoff (`S4RedirectSoundInv_not_isModalClosed`)
in an induction over `modalExpandBranchesS4KeyedOrdered`'s fuel-bounded recursion, mirroring
`modalExpandBranchesGen_closed_unsatIn` (`FrameSoundness.lean:740-909`). The genuine new
difficulty relative to that generic proof is that `e` (the expanded set) and `keys` (birth keys)
are not bookkeeping-only here -- `S4RedirectSoundInv`/`S4OrderedFuelInv` both depend on them --
so they must be threaded pointwise alongside `acc`, not just length-checked. Resolved via a
4-column EXISTENTIAL witness (`Ex4Inv` below) rather than the zip-triple design an earlier
dispatch found awkward: `Ex4Inv` tracks "some ONE position across the four parallel worklists
carries an `S4KOFullInv` witness". This suffices because `S4RedirectSoundInv_step`'s own
conclusion is already existential (only ONE child branch is guaranteed to inherit the witness,
not all of them), so no universal per-position bookkeeping is needed; and because a witness's
exact index never needs to be pinned down (only its existence), transporting it across a step is
licensed by the structural fact (`_newExps_eq_map` below) that a stepper output's `newExps`
column, and the replicated `newAcc`/`keys'` columns, are all CONSTANT across `newBs`. -/

/-- **The per-branch invariant payload threaded by the outer fuel induction.** Bundles
`S4OrderedFuelInv` (driver-level structural invariant) with an existential `S4RedirectSoundInv`
witness, at one `(b, e, acc, keys)` quadruple. -/
def S4KOFullInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop :=
  S4OrderedFuelInv φ₀ b e acc keys ∧ ∃ Er, S4RedirectSoundInv φ₀ b e acc keys Er

/-- Nested-pair nesting of `List.zip` across four parallel lists: `A × B × C × D` is already
right-associated as `A × (B × (C × D))`, so no reshuffling is needed after the two nested
`List.zip` calls. -/
def zip4 {A B C D : Type*} (as : List A) (bs : List B) (cs : List C) (ds : List D) :
    List (A × B × C × D) :=
  as.zip (bs.zip (cs.zip ds))

/-- **The 4-column existential threading relation.** Holds when SOME position across the four
parallel worklists carries an `S4KOFullInv` witness. Deliberately existential (not the universal
`List.Forall₂`-style relation an earlier dispatch attempted): `S4RedirectSoundInv_step`'s own
conclusion only ever guarantees ONE child inherits the invariant, so a universal relation would
be both harder to establish and stronger than what the argument actually needs. -/
def Ex4Inv (φ₀ : Proposition Atom)
    (bs es : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility)
    (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))) : Prop :=
  ∃ q ∈ zip4 bs es accs keyss, S4KOFullInv φ₀ q.1 q.2.1 q.2.2.1 q.2.2.2

/-- If `a ∈ l` and `l'` is the constant map `l.map (fun _ => c)`, then `(a, c)` is a member of
`l.zip l'` -- the index of `a` in `l` never needs to be pinned down, since `l'`'s value is the
same at every position. -/
private lemma mem_zip_of_mem_map_const {α β : Type*} (c : β) :
    ∀ (l : List α) {a : α}, a ∈ l → (a, c) ∈ l.zip (l.map (fun _ => c))
  | [], _, hmem => absurd hmem (List.not_mem_nil)
  | x :: xs, a, hmem => by
    rw [List.map_cons, List.zip_cons_cons]
    rcases List.mem_cons.mp hmem with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_zip_of_mem_map_const c xs h)

/-- **Construction**: a membership witness in `bs` plus three constant-map descriptions of
`es`/`accs`/`keyss` (relative to `bs`) plus an `S4KOFullInv` fact at the constant values gives
`Ex4Inv`. This is how a step's output (whose `newExps`/replicated `newAcc`/`keys'` columns are
all constant across `newBs`, per `modalStepBranchS4KeyedOrdered_newExps_eq_map` and
`List.map_const'`) inherits an `Ex4Inv` witness from `S4RedirectSoundInv_step`'s existential
output without ever pinning down an index. -/
private lemma Ex4Inv_of_mem_const (φ₀ : Proposition Atom)
    {bs : List (List (SignedFormula (Proposition Atom) WorldIndex))}
    {b' : List (SignedFormula (Proposition Atom) WorldIndex)} (hmem : b' ∈ bs)
    {es : List (List (SignedFormula (Proposition Atom) WorldIndex))}
    {e0 : List (SignedFormula (Proposition Atom) WorldIndex)}
    (hes : es = bs.map (fun _ => e0))
    {accs : List Accessibility} {a0 : Accessibility} (haccs : accs = bs.map (fun _ => a0))
    {keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))}
    {k0 : List (WorldIndex × Finset (Sign × Proposition Atom))}
    (hkeyss : keyss = bs.map (fun _ => k0))
    (hinv : S4KOFullInv φ₀ b' e0 a0 k0) :
    Ex4Inv φ₀ bs es accs keyss := by
  subst hes haccs hkeyss
  refine ⟨(b', e0, a0, k0), ?_, hinv⟩
  unfold zip4
  rw [List.zip_map', List.zip_map']
  exact mem_zip_of_mem_map_const (e0, a0, k0) bs hmem

/-- **Length-preserving append.** `zip4` distributes over pointwise append, given the three
non-first columns match the first column's length -- three applications of `List.zip_append`,
innermost first. -/
private lemma zip4_append {A B C D : Type*}
    (as as' : List A) (bs bs' : List B) (cs cs' : List C) (ds ds' : List D)
    (h1 : bs.length = as.length) (h2 : cs.length = as.length) (h3 : ds.length = as.length) :
    zip4 (as ++ as') (bs ++ bs') (cs ++ cs') (ds ++ ds') =
      zip4 as bs cs ds ++ zip4 as' bs' cs' ds' := by
  unfold zip4
  have hcd : (cs ++ cs').zip (ds ++ ds') = cs.zip ds ++ cs'.zip ds' :=
    List.zip_append (h2.trans h3.symm)
  have hbcd : (bs ++ bs').zip ((cs ++ cs').zip (ds ++ ds')) =
      bs.zip (cs.zip ds) ++ bs'.zip (cs'.zip ds') := by
    rw [hcd]
    refine List.zip_append ?_
    simp only [List.length_zip]
    omega
  rw [hbcd]
  refine List.zip_append ?_
  simp only [List.length_zip]
  omega

/-- Prepending a length-matched (against the FIRST/`bs`-shaped column) but otherwise arbitrary
quadruple of lists preserves `Ex4Inv` membership -- the witness's position shifts into the
suffix, its existence is untouched. -/
private lemma Ex4Inv_embedLeft (φ₀ : Proposition Atom)
    {bs es : List (List (SignedFormula (Proposition Atom) WorldIndex))}
    {accs : List Accessibility}
    {keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))}
    (h : Ex4Inv φ₀ bs es accs keyss)
    (pbs pes : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (paccs : List Accessibility)
    (pkeyss : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
    (hlen1 : pes.length = pbs.length) (hlen2 : paccs.length = pbs.length)
    (hlen3 : pkeyss.length = pbs.length) :
    Ex4Inv φ₀ (pbs ++ bs) (pes ++ es) (paccs ++ accs) (pkeyss ++ keyss) := by
  obtain ⟨q, hq, hinv⟩ := h
  refine ⟨q, ?_, hinv⟩
  rw [zip4_append pbs bs pes es paccs accs pkeyss keyss hlen1 hlen2 hlen3]
  exact List.mem_append_right _ hq

/-- Appending a length-matched (against the FIRST/`bs`-shaped column) but otherwise arbitrary
quadruple of lists preserves `Ex4Inv` membership -- the witness stays in the prefix. -/
private lemma Ex4Inv_embedRight (φ₀ : Proposition Atom)
    {bs es : List (List (SignedFormula (Proposition Atom) WorldIndex))}
    {accs : List Accessibility}
    {keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))}
    (h : Ex4Inv φ₀ bs es accs keyss)
    (hlen1 : es.length = bs.length) (hlen2 : accs.length = bs.length)
    (hlen3 : keyss.length = bs.length)
    (sbs ses : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (saccs : List Accessibility)
    (skeyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))) :
    Ex4Inv φ₀ (bs ++ sbs) (es ++ ses) (accs ++ saccs) (keyss ++ skeyss) := by
  obtain ⟨q, hq, hinv⟩ := h
  refine ⟨q, ?_, hinv⟩
  rw [zip4_append bs sbs es ses accs saccs keyss skeyss hlen1 hlen2 hlen3]
  exact List.mem_append_left _ hq

/-- **Projection**: a `zip4` membership projects to a membership in the "1st/3rd column" 2-way
zip, at the SAME underlying position -- unlike `List.of_mem_zip`, which only gives independent
membership of each component in its own list, this preserves the positional correspondence
`zip4` was built to carry. Needed for the outer induction's base case, which only inspects
`branches.zip accs` (not `expandedSets`/`keyss` at all). -/
private lemma mem_zip4_proj13 {A B C D : Type*} :
    ∀ (as : List A) (bs : List B) (cs : List C) (ds : List D) (q : A × B × C × D),
      q ∈ zip4 as bs cs ds → (q.1, q.2.2.1) ∈ as.zip cs
  | a :: as, b :: bs, c :: cs, d :: ds, q, hq => by
    unfold zip4 at hq
    rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons] at hq
    rcases List.mem_cons.mp hq with rfl | h
    · simp [List.zip_cons_cons]
    · exact List.mem_cons_of_mem _
        (mem_zip4_proj13 as bs cs ds q (by unfold zip4; exact h))
  | [], _, _, _, q, hq => absurd hq (by simp [zip4])
  | _ :: _, [], _, _, q, hq => absurd hq (by simp [zip4])
  | _ :: _, _ :: _, [], _, q, hq => absurd hq (by simp [zip4])
  | _ :: _, _ :: _, _ :: _, [], q, hq => absurd hq (by simp [zip4])

/-- **Cons case-split**: membership in a `zip4` of four cons-headed lists is either the head
quadruple or a membership in the four tails -- mirrors the case split
`modalExpandBranchesS4KeyedOrdered.processNext` itself performs when it pattern-matches
`pending, pendingExp, pendingAccs, pendingKeys` simultaneously. -/
private lemma zip4_cons_mem_cases {A B C D : Type*}
    (a : A) (as : List A) (b : B) (bs : List B) (c : C) (cs : List C) (d : D) (ds : List D)
    {q : A × B × C × D} (hq : q ∈ zip4 (a :: as) (b :: bs) (c :: cs) (d :: ds)) :
    q = (a, b, c, d) ∨ q ∈ zip4 as bs cs ds := by
  unfold zip4 at hq ⊢
  rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons] at hq
  exact List.mem_cons.mp hq

/-- **Phase 9.1: the outer fuel induction.** Wraps Phase 7.8's step theorem
(`S4RedirectSoundInv_step`) and Phase 8's terminal payoff
(`S4RedirectSoundInv_not_isModalClosed`) in an induction over
`modalExpandBranchesS4KeyedOrdered`'s fuel-bounded recursion, mirroring
`modalExpandBranchesGen_closed_unsatIn` (`FrameSoundness.lean:740-909`). Concludes `False`
directly (rather than a per-branch `¬branchSatisfiableIn`-style fact, as the generic proof
does) because `Ex4Inv` already IS a satisfiability witness (via `S4RedirectSoundInv`'s conjunct
(b)): once the driver closes, the ONE tracked witness branch is necessarily among the closed
branches, and Phase 8 turns that into a direct contradiction -- no universal per-branch
bookkeeping is needed. -/
theorem modalExpandBranchesS4KeyedOrdered_closed_False (φ₀ : Proposition Atom) :
    ∀ (fuel : Nat)
      (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility)
      (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
      Ex4Inv φ₀ branches expandedSets accs keyss →
      modalExpandBranchesS4KeyedOrdered φ₀ branches expandedSets accs keyss fuel = .closed →
      False := by
  intro fuel
  induction fuel with
  | zero =>
    intro branches expandedSets accs keyss hEx h
    unfold modalExpandBranchesS4KeyedOrdered at h
    split at h
    · simp at h
    · rename_i hfind
      obtain ⟨q, hq, hinv⟩ := hEx
      have hzip13 := mem_zip4_proj13 branches expandedSets accs keyss q hq
      have hfn := List.findSome?_eq_none_iff.mp hfind (q.1, q.2.2.1) hzip13
      have hclosed : isModalClosed q.1 = true := by
        rcases hc : isModalClosed q.1 with _ | _
        · simp [hc] at hfn
        · rfl
      obtain ⟨Er, hRS⟩ := hinv.2
      have hnc := S4RedirectSoundInv_not_isModalClosed φ₀ q.1 q.2.1 q.2.2.1 q.2.2.2 Er hRS
      rw [hclosed] at hnc
      simp at hnc
  | succ fuel' ih =>
    intro branches expandedSets accs keyss hEx h
    suffices key : ∀ (pending
        pendingExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
        doneExp.length = done.length → doneAccs.length = done.length →
        doneKeys.length = done.length →
        Ex4Inv φ₀ pending pendingExp pendingAccs pendingKeys →
        modalExpandBranchesS4KeyedOrdered.processNext φ₀
          fuel' pending pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys =
          .closed →
        False from
      key branches expandedSets accs keyss [] [] [] [] rfl rfl rfl hEx
        (by simpa [modalExpandBranchesS4KeyedOrdered] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys _ _ _ hEx _
      obtain ⟨q, hq, -⟩ := hEx
      simp [zip4] at hq
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        hdoneExpLen hdoneAccsLen hdoneKeysLen hEx hinner
      cases pendingExp with
      | nil => obtain ⟨q, hq, -⟩ := hEx; simp [zip4] at hq
      | cons eh et =>
        cases pendingAccs with
        | nil => obtain ⟨q, hq, -⟩ := hEx; simp [zip4] at hq
        | cons ah at' =>
          cases pendingKeys with
          | nil => obtain ⟨q, hq, -⟩ := hEx; simp [zip4] at hq
          | cons kh kt =>
            obtain ⟨q, hq, hinvq⟩ := hEx
            unfold modalExpandBranchesS4KeyedOrdered.processNext at hinner
            by_cases hcl : isModalClosed bh = true
            · rw [if_pos hcl] at hinner
              rcases zip4_cons_mem_cases bh bt eh et ah at' kh kt hq with heq | htail
              · exfalso
                rw [heq] at hinvq
                obtain ⟨Er, hRS⟩ := hinvq.2
                have hnc := S4RedirectSoundInv_not_isModalClosed φ₀ bh eh ah kh Er hRS
                rw [hcl] at hnc
                simp at hnc
              · refine ih_inner et at' kt (done ++ [bh]) (doneExp ++ [eh]) (doneAccs ++ [ah])
                  (doneKeys ++ [kh]) ?_ ?_ ?_ ⟨q, htail, hinvq⟩ hinner
                · simp only [List.length_append, List.length_singleton]; omega
                · simp only [List.length_append, List.length_singleton]; omega
                · simp only [List.length_append, List.length_singleton]; omega
            · rw [if_neg hcl] at hinner
              cases hstep : modalStepBranchS4KeyedOrdered φ₀ bh eh ah kh with
              | none => rw [hstep] at hinner; simp at hinner
              | some val =>
                obtain ⟨newBs, newExps, newAcc, keys'⟩ := val
                rw [hstep] at hinner
                obtain ⟨e'0, he'0⟩ :=
                  modalStepBranchS4KeyedOrdered_newExps_eq_map φ₀ bh eh ah kh newBs newExps
                    newAcc keys' hstep
                have hlenNB : newExps.length = newBs.length := by
                  rw [he'0, List.length_map]
                have haccs_eq : List.replicate newBs.length newAcc = newBs.map (fun _ => newAcc) :=
                  (List.map_const' (l := newBs) (b := newAcc)).symm
                have hkeyss_eq : List.replicate newBs.length keys' = newBs.map (fun _ => keys') :=
                  (List.map_const' (l := newBs) (b := keys')).symm
                rcases zip4_cons_mem_cases bh bt eh et ah at' kh kt hq with heq | htail
                · -- our witness is `bh` itself: expand it, land the child witness in `newBs`.
                  rw [heq] at hinvq
                  obtain ⟨hOF, Er, hRS⟩ := hinvq
                  obtain ⟨b', hb', e', he', Er', -, hRS'⟩ :=
                    S4RedirectSoundInv_step φ₀ bh eh ah kh Er newBs newExps newAcc keys' hRS
                      hOF.1.bClosure hOF.1.keyLowerBd hOF.2.1 hOF.1.accFresh hstep
                  have hOF' := modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv φ₀ bh eh
                    ah kh newBs newExps newAcc keys' hOF hstep b' hb' e' he'
                  have he'eq : e' = e'0 := by
                    rw [he'0] at he'
                    obtain ⟨x, -, hx⟩ := List.mem_map.mp he'
                    exact hx.symm
                  have hFull' : S4KOFullInv φ₀ b' e'0 newAcc keys' := by
                    rw [← he'eq]; exact ⟨hOF', Er', hRS'⟩
                  have hExNB : Ex4Inv φ₀ newBs newExps
                      (List.replicate newBs.length newAcc) (List.replicate newBs.length keys') :=
                    Ex4Inv_of_mem_const φ₀ hb' he'0 haccs_eq hkeyss_eq hFull'
                  refine ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ et)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ at')
                    (doneKeys ++ List.replicate newBs.length keys' ++ kt) ?_ hinner
                  refine Ex4Inv_embedRight φ₀
                    (Ex4Inv_embedLeft φ₀ hExNB done doneExp doneAccs doneKeys
                      hdoneExpLen hdoneAccsLen hdoneKeysLen)
                    ?_ ?_ ?_ bt et at' kt
                  · simp only [List.length_append]; omega
                  · simp only [List.length_append, List.length_replicate]; omega
                  · simp only [List.length_append, List.length_replicate]; omega
                · -- our witness is in the tail `bt`: `bh`'s fate does not matter, embed forward.
                  have hEx_tail : Ex4Inv φ₀ bt et at' kt := ⟨q, htail, hinvq⟩
                  refine ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ et)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ at')
                    (doneKeys ++ List.replicate newBs.length keys' ++ kt) ?_ hinner
                  refine Ex4Inv_embedLeft φ₀ hEx_tail (done ++ newBs) (doneExp ++ newExps)
                    (doneAccs ++ List.replicate newBs.length newAcc)
                    (doneKeys ++ List.replicate newBs.length keys') ?_ ?_ ?_
                  · simp only [List.length_append]; omega
                  · simp only [List.length_append, List.length_replicate]; omega
                  · simp only [List.length_append, List.length_replicate]; omega

/-! ## Scope of `modalExpandBranchesS4KeyedOrdered_closed_False`

This result establishes soundness of the KEYED ORDERED driver via `S4RedirectSoundInv`, a
predicate that quarantines redirect (loop-guard-blocked) edges from the semantic
edge-realization obligation rather than discharging that obligation directly. At the seed state
(`Er = []`, `acc = Accessibility.empty`) this weakening is definitionally absent -- conjunct (b)
reduces to the plain, undiluted edge-realization clause -- which is what licenses Phase 9.2's
capstone to conclude genuine, unweakened `s4Valid`. This result does **not** remove or discharge
the standing `sorry` in `FrameSoundness.lean`, whose statement is the *unweakened* per-step form
this task established is not provable for the keyed S4 guard in general (see the Phase 7.4
Verdict above): that sorry documents a standing, deliberate scope decision and is left untouched.
-/

/-- **Phase 9.2: the end-to-end soundness capstone.** If the ordered keyed driver closes on
`F(φ₀)@0`, then `φ₀` is `s4Valid`. Mirrors `modalTableauS5Gen_sound`'s own countermodel/by-contra
argument in shape: assumes a countermodel, builds the seed-state `S4KOFullInv` witness (the
`S4RedirectSoundInv` half from `S4RedirectSoundInv_initial`, the `S4OrderedFuelInv` half from
`modalTableauS4Keyed_initial` plus `keysOriginS4_entry`), and derives the contradiction directly
from the outer fuel induction `modalExpandBranchesS4KeyedOrdered_closed_False`. Per that
theorem's own scope note: this establishes genuine, unweakened `s4Valid`, not a diluted form,
because `S4RedirectSoundInv` at the seed state (`Er = []`) is definitionally the plain
edge-realization clause. -/
theorem modalTableauS4KeyedOrdered_sound (φ₀ : Proposition Atom)
    (h : modalTableauS4KeyedOrdered φ₀ = .closed) : s4Valid φ₀ := by
  intro World m hFC w
  by_contra hnotsat
  have hRS := S4RedirectSoundInv_initial φ₀ m (fun _ => w) hFC hnotsat
  obtain ⟨hLoop, hHintikka, hKW, hWC⟩ := modalTableauS4Keyed_initial φ₀
  have hKO := keysOriginS4_entry φ₀
  have hOF : S4OrderedFuelInv φ₀
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      Accessibility.empty [((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))] :=
    ⟨hLoop, hHintikka, hKW, hWC, hKO⟩
  have hFull : S4KOFullInv φ₀
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      Accessibility.empty [((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))] :=
    ⟨hOF, [], hRS⟩
  have hEx : Ex4Inv φ₀
      [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      [Accessibility.empty]
      [[((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))]] :=
    Ex4Inv_of_mem_const φ₀ (List.mem_singleton_self _) rfl rfl rfl hFull
  have h' : modalExpandBranchesS4KeyedOrdered φ₀
      [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))]]
      (modalFuelS4 φ₀) = .closed := h
  exact modalExpandBranchesS4KeyedOrdered_closed_False φ₀ (modalFuelS4 φ₀)
    [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
    [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))]] hEx h'

/-! ## S4KeyedOrdered Completeness and the Decidability Capstone

The completeness half for the *ordered* driver, paired with `modalTableauS4KeyedOrdered_sound`
above to close S4 decidability. Near-verbatim copy of `modalTableauS4Keyed_complete`
(S4Keyed Completeness section above), fed by `modalExpandBranchesS4KeyedOrdered_hintikka` and
`modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem` (`LoopChecking.lean`) in place of
their unordered analogues. The seed-state `S4OrderedFuelInv` witness is assembled from the same
ingredients `modalTableauS4KeyedOrdered_sound` already uses verbatim: the four conjuncts of
`modalTableauS4Keyed_initial` plus the fifth, `keysOriginS4_entry`. -/

/-- **S4-completeness of the ordered keyed modal tableau**: if `φ₀` is `s4Valid`,
`modalTableauS4KeyedOrdered` closes on it. Contrapositively: an open branch is a genuine
reflexive-transitive-frame countermodel. Assembled from
`modalExpandBranchesS4KeyedOrdered_hintikka` (`LoopChecking.lean`, fed the corrected entry
invariant `modalTableauS4Keyed_initial` plus `keysOriginS4_entry`, bundled as `S4OrderedFuelInv`),
`modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem` (`LoopChecking.lean`), and
`modalOpenBranchS4_countermodel` above. Mirrors `modalTableauS4Keyed_complete`. -/
theorem modalTableauS4KeyedOrdered_complete (φ₀ : Proposition Atom) (h : s4Valid φ₀) :
    modalTableauS4KeyedOrdered φ₀ = .closed := by
  cases htab : modalTableauS4KeyedOrdered φ₀ with
  | closed => rfl
  | openBranch b a =>
    exfalso
    have h' : modalExpandBranchesS4KeyedOrdered φ₀
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))]]
        (modalFuelS4 φ₀) = .openBranch b a := htab
    obtain ⟨hLoop, hHintikka, hKW, hWC⟩ := modalTableauS4Keyed_initial φ₀
    have hKO := keysOriginS4_entry φ₀
    have hOF : S4OrderedFuelInv φ₀
        [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
        Accessibility.empty [((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))] :=
      ⟨hLoop, hHintikka, hKW, hWC, hKO⟩
    have hH : modalHintikkaSetS4 φ₀ b a :=
      modalExpandBranchesS4KeyedOrdered_hintikka φ₀ (modalFuelS4 φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))]]
        rfl rfl rfl (modalExpMeasure_entry_le_fuelS4 φ₀)
        (by
          intro i bi ei ai keysi hib hie hia hik
          match i with
          | 0 =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia hik
            subst hib; subst hie; subst hia; subst hik
            exact hOF
          | n + 1 => simp at hib)
        b a h'
    have hmemInit : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
      modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem φ₀ (modalFuelS4 φ₀)
        (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] [[((0 : WorldIndex), (∅ : Finset (Sign × Proposition Atom)))]]
        rfl rfl rfl
        (fun b₀ hb₀ => by
          simp only [List.mem_singleton] at hb₀
          subst hb₀
          simp)
        b a h'
    obtain ⟨hnsat, hFC⟩ := modalOpenBranchS4_countermodel φ₀ b a hH hmemInit
    exact hnsat (h WorldIndex (extractModelS4 b a) hFC 0)

/-- **The ordered keyed modal tableau decides S4-validity**: `modalTableauS4KeyedOrdered φ₀`
closes exactly when `φ₀` is `s4Valid`. Combines soundness (`modalTableauS4KeyedOrdered_sound`
above) with completeness (`modalTableauS4KeyedOrdered_complete` above). Mirrors
`kb5Valid_decides`. -/
theorem s4Valid_decides (φ₀ : Proposition Atom) :
    modalTableauS4KeyedOrdered φ₀ = .closed ↔ s4Valid φ₀ :=
  ⟨modalTableauS4KeyedOrdered_sound φ₀, modalTableauS4KeyedOrdered_complete φ₀⟩

/-- **S4-validity is decidable**: decide by running the ordered keyed modal tableau and consulting
`s4Valid_decides`. No `Fintype Atom` assumption is needed, since the tableau computation itself is
the decision procedure. Mirrors `instDecidableKb5Valid`.

This is the constructive witness to S4's decidability -- the last classical-cube decidability
corner, closed by the settled-context-scheduling ordered driver `modalTableauS4KeyedOrdered`
(NOT the unordered `modalTableauS4Keyed`, whose soundness is false, and NOT the live-guard
`modalTableauS4`, which has no completeness proof of its own). -/
instance instDecidableS4Valid (φ₀ : Proposition Atom) : Decidable (s4Valid φ₀) :=
  match h : modalTableauS4KeyedOrdered φ₀ with
  | .closed => .isTrue ((s4Valid_decides φ₀).mp h)
  | .openBranch _ _ =>
    .isFalse (fun hv => by rw [modalTableauS4KeyedOrdered_complete φ₀ hv] at h; cases h)

/-! ## Modal-Cube Decidability Matrix: Coverage and Intentional Out-of-Scope Notes

The modal cube (`Cslib/Logics/Modal/Cube.lean`) names fifteen systems: `K`, `T`, `B`, `Four`
(K4), `Five` (K5), `K45`, `D`, `D4`, `D5`, `D45`, `DB`, `TB`, `KB5`, `S4`, `S5`. Eight of the
fifteen are decidable in this tableau development; the remaining seven are documented here
rather than implemented, each with its frame condition, assessed tier, named blocking gate, and
a rough cost estimate, so the matrix is *intentionally* incomplete rather than accidentally
ragged.

### Covered (8/15)

| System | Frame condition | `Decidable` instance | Driver |
|--------|------------------|------------------------|--------|
| K | none (`Set.univ`) | `instDecidableKValid` | `modalTableau` |
| T | `Std.Refl` | `instDecidableTValid` | `modalTableauT` |
| B | `Std.Symm` | `instDecidableBValid` | `modalTableauB` |
| TB | `Std.Refl ∧ Std.Symm` | `instDecidableTBValid` | `modalTableauTB` |
| K5 (`Five`) | `Relation.RightEuclidean` | `instDecidableFiveValid` | `modalTableauFive` |
| KB5 | `Std.Symm ∧ Relation.RightEuclidean` | `instDecidableKb5Valid` | `modalTableauKb5''` |
| S4 | `Std.Refl ∧ IsTrans` | `instDecidableS4Valid` | `modalTableauS4KeyedOrdered` (the
  ordered, settled-context-scheduling driver -- see its own docstring above for why the
  unordered keyed variant is unsound and is not used here) |
| S5 | `Std.Refl ∧ IsTrans ∧ Relation.RightEuclidean` | `instDecidableS5Valid` | `modalTableauS5` |

### Out of scope, with named gates (7/15)

Each entry below is deliberately unimplemented. Every gate is a settled architectural
obstruction, not an oversight -- discharging it is the sanctioned starting point for a future
corner, not a re-litigation of the per-regime driver split (see "Settled decisions" below). Gate
ownership by successor task is tracked in this task's own plan file, not restated here -- Lean
source is not the place to cite task-tracker identifiers.

- **D** -- frame condition `Relation.Serial`; no closure operator suffices; **Tier A**; gate:
  serial-rule spec shape -- no known rule discharges
  `RuleApplicationSpec.boxPosNotExpanding` for a seriality witness without either being unsound
  or non-terminating (see "Refuted alternatives for D" below); cost estimate ~1,700 lines once
  ungated.
- **DB** -- frame condition `Relation.Serial ∧ Std.Symm`; closure `SymmGen` plus a serial
  repair; **Tier A/B**; gate: serial-rule spec shape (same gate as D); cost estimate
  ~1,700–3,600 lines.
- **K4** -- frame condition `IsTrans`; closure `Relation.TransGen`; **Tier C**; gate: the
  unordered S4 stepper-stack retirement, together with removing the T arm from the S4 rule
  chain; cost estimate ~13,500 lines.
- **D4** -- frame condition `Relation.Serial ∧ IsTrans`; closure `TransGen` plus a serial
  repair; **Tier C**; gates: both of K4's gates, plus the serial-rule spec shape; cost estimate
  ~13,500 lines.
- **K45** -- frame condition `IsTrans ∧ Relation.RightEuclidean`; closure `EuclGen` (plus
  transitivity); **Tier B**; gate: the universal-cluster rule-combinator prototype; cost
  estimate ~3,600 lines.
- **D5** -- frame condition `Relation.Serial ∧ Relation.RightEuclidean`; closure `EuclGen` plus
  a serial repair; **Tier B**; gates: the rule-combinator prototype, plus the serial-rule spec
  shape; cost estimate ~3,600 lines.
- **D45** -- frame condition `Relation.Serial ∧ IsTrans ∧ Relation.RightEuclidean`; closure as
  K45, plus a serial repair; **Tier B**; gates: the rule-combinator prototype, plus the
  serial-rule spec shape; cost estimate ~3,600 lines.

### Refuted mint-avoiding alternatives for D

Three approaches to a seriality rule that avoids minting a fresh witness world were considered
and refuted; recorded here so the refutations live in-tree rather than only in a task tracker:

- **Self-loop-at-dead-ends closure**: unsound -- it licenses the T inference (reflexivity) at
  worlds that are not actually reflexive, collapsing D into T.
- **Fresh sink world**: relocates the minting problem rather than discharging it -- the rule
  still mints, just at a world with no further obligations, which does not satisfy
  `RuleApplicationSpec.boxPosNotExpanding` any more than a direct mint would.
- **`F(□⊥)` seeding**: sound, but non-terminating under `rankStep` -- nothing bounds how many
  times the seed can be re-applied along a branch.

### Settled decisions

- **Per-regime drivers are settled.** Each corner gets its own bespoke driver file
  (`TDriver.lean`, `BDriver.lean`, `TBDriver.lean`, ...) rather than a generic traversal rung
  parameterised over frame conditions. This decision was made deliberately and is not
  reopened by adding a new corner; a future corner should add another sibling driver file, not
  a generic abstraction.
- **The ordered S4 driver, not the unordered keyed one, is the sound one.** See
  `instDecidableS4Valid`'s own docstring above for the full account; it is not restated here.

-/

end Cslib.Logic.Modal.Tableau

end
