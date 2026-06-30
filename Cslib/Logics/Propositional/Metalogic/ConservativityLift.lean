/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Init
public import Cslib.Logics.Propositional.Semantics.Bool
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Parametric Conservativity Lift

Generic declarations factoring out the proof pattern shared by the Modal, Temporal,
and Bimodal propositional conservativity results.

## Main Declarations

- `evaluate_iff_of_classicalBridge`: Given an abstract `sat : Tgt → Prop` and five
  per-connective `Iff` / `¬` hypotheses recording how `emb` translates each PL connective
  into `Tgt`, proves `sat (emb ψ) ↔ PL.Evaluate v ψ` for every formula `ψ` by structural
  induction.

- `conservative_over_cpl`: Given a valuation-parameterized bridge and a per-logic
  satisfaction callback from soundness, derives `Derivable PropositionalAxiom φ` via
  `prop_completeness`.

## Placement Rationale

Both theorems are parametric over an embedding target `Tgt` but their subject is the concrete
CSLib propositional logic: `evaluate_iff_of_classicalBridge` recurses over `PL.Proposition`
and unfolds `PL.Evaluate`; `conservative_over_cpl` invokes `prop_completeness`. Generic over
the target type does not mean logic-agnostic: the file's imports (`Propositional.Semantics.Bool`,
`Propositional.Metalogic.StrongCompleteness`) are both intra-layer here. `Propositional/Metalogic`
is the lowest-common-ancestor module visible to all three clients (Modal, Temporal, Bimodal) that
already import `Logics/Propositional`, so this is the natural home for the shared bridge lemmas.
-/

@[expose] public section

namespace Cslib.Logic

open PL

/-- **Parametric Bridge Lemma**: Given any embedding `emb : PL.Proposition Atom → Tgt`,
a satisfaction predicate `sat : Tgt → Prop`, a propositional valuation `v : Atom → Prop`,
and five per-connective compatibility hypotheses, establishes
`sat (emb ψ) ↔ PL.Evaluate v ψ` for every propositional formula `ψ` by structural induction.

The `h_and` and `h_or` hypotheses use the Lukasiewicz encoding (negation-of-negation for
`and`, implication-from-negation for `or`), matching the concrete embeddings in
`Temporal.FromPropositional` and `Bimodal.Embedding.PropositionalEmbedding`. The `h_atom`
hypothesis is an explicit `Iff` rather than `rfl` to accommodate the Bimodal case, where
atoms are wrapped in an existential over world-history domain membership. -/
theorem evaluate_iff_of_classicalBridge
    {Atom : Type*} {Tgt : Type*}
    (emb : PL.Proposition Atom → Tgt) (sat : Tgt → Prop) (v : Atom → Prop)
    (h_atom : ∀ p, sat (emb (.atom p)) ↔ v p)
    (h_bot  : ¬ sat (emb .bot))
    (h_imp  : ∀ a b, sat (emb (.imp a b)) ↔ (sat (emb a) → sat (emb b)))
    (h_and  : ∀ a b, sat (emb (.and a b)) ↔ ((sat (emb a) → sat (emb b) → False) → False))
    (h_or   : ∀ a b, sat (emb (.or a b))  ↔ ((sat (emb a) → False) → sat (emb b))) :
    ∀ ψ, sat (emb ψ) ↔ PL.Evaluate v ψ := by
  intro ψ
  induction ψ with
  | atom p =>
    simp only [PL.Evaluate]
    exact h_atom p
  | bot =>
    simp only [PL.Evaluate]
    exact iff_false_intro h_bot
  | imp a b ih1 ih2 =>
    rw [h_imp a b]
    simp only [PL.Evaluate]
    exact ⟨fun h he => ih2.mp (h (ih1.mpr he)),
           fun h hm => ih2.mpr (h (ih1.mp hm))⟩
  | and a b ih1 ih2 =>
    rw [h_and a b]
    simp only [PL.Evaluate]
    constructor
    · intro h
      constructor
      · by_contra hna; exact h (fun ha _ => hna (ih1.mp ha))
      · by_contra hnb; exact h (fun _ hb => hnb (ih2.mp hb))
    · intro ⟨ha, hb⟩ h
      exact h (ih1.mpr ha) (ih2.mpr hb)
  | or a b ih1 ih2 =>
    rw [h_or a b]
    simp only [PL.Evaluate]
    constructor
    · intro h
      by_cases ha : PL.Evaluate v a
      · exact Or.inl ha
      · exact Or.inr (ih2.mp (h (fun hma => ha (ih1.mp hma))))
    · intro h hna
      cases h with
      | inl ha => exact absurd (ih1.mpr ha) hna
      | inr hb => exact ih2.mpr hb

/-- **Parametric Conservativity over CPL**: Given a valuation-parameterized bridge
`bridge : ∀ v, sat v (emb φ) ↔ PL.Evaluate v φ` and a per-logic satisfaction callback
`h_sat : ∀ v, sat v (emb φ)` (typically from a soundness theorem), derives
`Derivable PropositionalAxiom φ` via `prop_completeness`.

This factors out the three-line proof pattern that is copy-equal across the Modal,
Temporal, and Bimodal conservativity results. -/
theorem conservative_over_cpl
    {Atom : Type*} {Tgt : Type*} {φ : PL.Proposition Atom}
    {emb : PL.Proposition Atom → Tgt} {sat : (Atom → Prop) → Tgt → Prop}
    (bridge : ∀ v, sat v (emb φ) ↔ PL.Evaluate v φ)
    (h_sat  : ∀ v, sat v (emb φ)) :
    Derivable PropositionalAxiom φ := by
  apply prop_completeness
  intro v
  exact (bridge v).mp (h_sat v)

end Cslib.Logic

end
