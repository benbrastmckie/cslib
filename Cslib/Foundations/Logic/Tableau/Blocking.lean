/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
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
lemma containmentBlocked_iff [BEq F] [BEq L] [LawfulBEq F] [LawfulBEq L] {b : Branch F L}
    {l₁ l₂ : L} :
    b.containmentBlocked l₁ l₂ = true ↔ ∀ x ∈ b.typeAt l₁, x ∈ b.typeAt l₂ := by
  simp [containmentBlocked, List.all_eq_true, List.any_eq_true]

end Branch

end Cslib.Logic.Tableau

end
