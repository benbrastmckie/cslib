/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Separation.Defs

set_option linter.style.emptyLine false

/-!
# Distributivity Laws (GHR94 Lemma 10.2.1)

U and S distribute over boolean connectives. These are valid over ALL
linear flows of time (not just integers).

## Key Results

- `until_distrib_or_left`: U(A v B, C) <-> U(A,C) v U(B,C)
- `since_distrib_or_left`: S(A v B, C) <-> S(A,C) v S(B,C)
- `until_distrib_and_right`: U(A, B ^ C) <-> U(A,B) ^ U(A,C)
- `since_distrib_and_right`: S(A, B ^ C) <-> S(A,B) ^ S(A,C)

## References

- GHR94, Lemma 10.2.1, p. 571
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.Separation

open Cslib.Logic.Bimodal

variable {Atom : Type*}

/-! ## Left Distributivity (Event over Disjunction) -/

/-- U distributes over disjunction in the event argument.
    U(A v B, C) <-> U(A,C) v U(B,C). -/
theorem until_distrib_or_left
    (A B C : Formula Atom) :
    intEquiv (.untl (Formula.or A B) C)
      (Formula.or (.untl A C) (.untl B C)) := by
  intro M t
  simp only [intTruth]
  constructor
  · rintro ⟨s, hts, hAB | hAB, hguard⟩
    · exact Or.inl ⟨s, hts, hAB, hguard⟩
    · exact Or.inr ⟨s, hts, hAB, hguard⟩
  · rintro (⟨s, hts, hA, hguard⟩ | ⟨s, hts, hB, hguard⟩)
    · exact ⟨s, hts, Or.inl hA, hguard⟩
    · exact ⟨s, hts, Or.inr hB, hguard⟩

/-- S distributes over disjunction in the event argument.
    S(A v B, C) <-> S(A,C) v S(B,C). -/
theorem since_distrib_or_left
    (A B C : Formula Atom) :
    intEquiv (.snce (Formula.or A B) C)
      (Formula.or (.snce A C) (.snce B C)) := by
  intro M t
  simp only [intTruth]
  constructor
  · rintro ⟨s, hst, hAB | hAB, hguard⟩
    · exact Or.inl ⟨s, hst, hAB, hguard⟩
    · exact Or.inr ⟨s, hst, hAB, hguard⟩
  · rintro (⟨s, hst, hA, hguard⟩ | ⟨s, hst, hB, hguard⟩)
    · exact ⟨s, hst, Or.inl hA, hguard⟩
    · exact ⟨s, hst, Or.inr hB, hguard⟩

/-! ## Right Distributivity (Guard over Conjunction) -/

/-- U distributes over conjunction in the guard argument.
    U(A, B ^ C) <-> U(A,B) ^ U(A,C).
    Uses linearity of the time order. -/
theorem until_distrib_and_right
    (A B C : Formula Atom) :
    intEquiv (.untl A (Formula.and B C))
      (Formula.and (.untl A B) (.untl A C)) := by
  intro M t
  simp only [intTruth]
  constructor
  · rintro ⟨s, hts, hA, hBC⟩
    exact ⟨⟨s, hts, hA, fun r hr1 hr2 => (hBC r hr1 hr2).1⟩,
           ⟨s, hts, hA, fun r hr1 hr2 => (hBC r hr1 hr2).2⟩⟩
  · rintro ⟨⟨s1, hts1, hA1, hB⟩, ⟨s2, hts2, hA2, hC⟩⟩
    by_cases hle : s1 ≤ s2
    · exact ⟨s1, hts1, hA1,
        fun r hr1 hr2 =>
          ⟨hB r hr1 hr2, hC r hr1 (lt_of_lt_of_le hr2 hle)⟩⟩
    · push_neg at hle
      exact ⟨s2, hts2, hA2,
        fun r hr1 hr2 =>
          ⟨hB r hr1 (lt_trans hr2 hle), hC r hr1 hr2⟩⟩

/-- S distributes over conjunction in the guard argument.
    S(A, B ^ C) <-> S(A,B) ^ S(A,C). -/
theorem since_distrib_and_right
    (A B C : Formula Atom) :
    intEquiv (.snce A (Formula.and B C))
      (Formula.and (.snce A B) (.snce A C)) := by
  intro M t
  simp only [intTruth]
  constructor
  · rintro ⟨s, hst, hA, hBC⟩
    exact ⟨⟨s, hst, hA, fun r hr1 hr2 => (hBC r hr1 hr2).1⟩,
           ⟨s, hst, hA, fun r hr1 hr2 => (hBC r hr1 hr2).2⟩⟩
  · rintro ⟨⟨s1, hst1, hA1, hB⟩, ⟨s2, hst2, hA2, hC⟩⟩
    by_cases hle : s2 ≤ s1
    · exact ⟨s1, hst1, hA1,
        fun r hr1 hr2 =>
          ⟨hB r hr1 hr2, hC r (lt_of_le_of_lt hle hr1) hr2⟩⟩
    · push_neg at hle
      exact ⟨s2, hst2, hA2,
        fun r hr1 hr2 =>
          ⟨hB r (lt_trans hle hr1) hr2, hC r hr1 hr2⟩⟩

end Cslib.Logic.Bimodal.Metalogic.Separation
