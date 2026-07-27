/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.DA.Rabin

/-! # Deterministic parity automata

This file defines deterministic parity automata (DPA) and proves a language-preserving
conversion to deterministic Rabin automata (DRA).

## Main definitions

* `DA.Parity` — a `DA` extended with a *priority function* `color : State → ℕ`.
  A run is accepting iff the minimum priority among states visited infinitely often is even,
  i.e., `Even (sInf (a.color '' (a.run xs).infOcc))`.

## Main theorems

* `DA.Parity.toRabin_language_eq` — the DPA-to-DRA conversion is language-preserving
  (requires `[Finite State]` to ensure infOcc is nonempty and the minimum is well-defined).

## Proof outline for `toRabin_language_eq`

The Rabin pairs are `{(color⁻¹({m | m < 2n}), color⁻¹{2n}) | n : ℕ}`.
Pair `n` is Rabin-satisfied iff:
- No state with priority `< 2n` appears in infOcc.
- Some state with priority `2n` appears in infOcc.

This is equivalent to `sInf (color '' infOcc) = 2n`, which is even.

## References

* [W. Thomas, *Infinite Words*, Chapter 3][Thomas2003]
* [E. Grädel, W. Thomas, T. Wilke, *Automata Logics and Infinite Games*][GradelThomasWilke2002]
-/

@[expose] public section

namespace Cslib.Automata.DA

open Set Filter Cslib.ωSequence ωLanguage ωAcceptor Acceptor
open scoped Cslib.FLTS

variable {State Symbol : Type*}

/-! ## Parity acceptance -/

/-- A deterministic parity automaton (`DA.Parity`) extends a `DA` with a priority function
`color : State → ℕ` assigning a natural number (priority) to each state.

A run on an ω-word `xs` is accepting if the minimum priority among states that appear
infinitely often is even:
```
Even (sInf (a.color '' (a.run xs).infOcc))
```

By convention `sInf ∅ = 0` (even in `ℕ`), so the condition is well-defined even when `infOcc`
is empty. In practice, `[Finite State]` guarantees `infOcc` is nonempty, making the minimum
always meaningful.

This *min-even parity* acceptance is the most common convention in the automata-theory
literature. Alternative conventions (max-even, min-odd, max-odd) yield equivalent expressive
power via simple color-shift transformations. -/
structure Parity (State Symbol : Type*) extends DA State Symbol where
  /-- The priority function assigning a natural number (priority) to each state. -/
  color : State → ℕ

namespace Parity

/-- A run is parity-accepting iff the minimum priority among states visited infinitely
often is even. Requires `[Finite State]` to ensure the minimum is well-defined (infOcc
is nonempty in finite state spaces, by the pigeonhole principle). -/
@[simp, scoped grind =, nolint unusedArguments]
instance [Finite State] : ωAcceptor (Parity State Symbol) Symbol where
  Accepts (a : Parity State Symbol) (xs : ωSequence Symbol) :=
    Even (sInf (a.color '' (a.run xs).infOcc))

end Parity

/-! ## DPA → DRA conversion -/

/-- Convert a deterministic parity automaton to a deterministic Rabin automaton with the
same language (requires `[Finite State]`).

The Rabin acceptance pairs are indexed by `n : ℕ`. Pair `n` is
`(color⁻¹{m | m < 2n}, color⁻¹{2n})`:
- Avoidance set: states with priority strictly less than `2n`.
- Visit set: states with priority exactly `2n`.

Pair `n` is satisfied iff no state with priority `< 2n` appears infinitely often,
but some state with priority `2n` appears infinitely often — equivalently,
`sInf (color '' infOcc) = 2n` (which is even). -/
@[scoped grind =, nolint unusedArguments]
def Parity.toRabin [Finite State] (a : Parity State Symbol) : Rabin State Symbol where
  toDA := a.toDA
  pairs := {pair | ∃ n : ℕ, pair = (a.color ⁻¹' {m | m < 2 * n}, a.color ⁻¹' {2 * n})}

/-- A helper lemma: given that `2 * n ∈ color '' infOcc` and no `m < 2 * n` is in
`color '' infOcc`, the minimum of `color '' infOcc` is `2 * n`. -/
private lemma sInf_eq_of_min {State : Type*} {a : Parity State Symbol}
    {xs : ωSequence Symbol} (n : ℕ)
    (h_img_ne : (a.color '' (a.run xs).infOcc).Nonempty)
    (h_2n_in : 2 * n ∈ a.color '' (a.run xs).infOcc)
    (h_lt_not_in : ∀ m < 2 * n, m ∉ a.color '' (a.run xs).infOcc) :
    sInf (a.color '' (a.run xs).infOcc) = 2 * n := by
  apply le_antisymm (Nat.sInf_le h_2n_in)
  apply le_csInf h_img_ne
  intro m hm
  by_contra h_not_le
  simp only [not_le] at h_not_le
  exact h_lt_not_in m h_not_le hm

/-- The DPA-to-DRA conversion preserves the language.

**Proof strategy**: We show `DPA accepts xs ↔ DRA accepts xs`.

**(→)** If `Even (sInf (color '' infOcc))`, write `sInf (color '' infOcc) = 2n` for some `n`
(using that `sInf` in `ℕ` equals a specific element when the set is nonempty). Then:
- `color '' infOcc` is nonempty (since `[Finite State]` implies `infOcc` is nonempty).
- `2n ∈ color '' infOcc` (since `sInf` of a nonempty set of naturals is a member).
- `∀ m < 2n, m ∉ color '' infOcc` (since `2n` is the minimum).
- So pair `n` is satisfied.

**(←)** If some Rabin pair `n` is satisfied:
- `infOcc ∩ color⁻¹{m | m < 2n} = ∅` means no state with color `< 2n` is in infOcc.
- `(infOcc ∩ color⁻¹{2n}).Nonempty` means some state with color `2n` is in infOcc.
- So `sInf (color '' infOcc) = 2n` (the minimum color is `2n`, which is even). -/
@[simp, scoped grind =]
theorem Parity.toRabin_language_eq [Finite State] (a : Parity State Symbol) :
    language a.toRabin = language a := by
  apply mem_ext
  intro xs
  rw [ωAcceptor.mem_language, ωAcceptor.mem_language]
  simp only [ωAcceptor.Accepts, Parity.toRabin, Set.mem_ofPred_eq]
  -- Abbreviations
  set R := (a.run xs).infOcc with h_R_def
  set C := a.color '' R with h_C_def
  have h_R_ne : R.Nonempty := infOcc_nonempty (a.run xs)
  have h_C_ne : C.Nonempty := h_R_ne.image a.color
  constructor
  · -- DRA accepts → DPA accepts
    rintro ⟨pair, ⟨n, rfl⟩, h_avoid, h_visit⟩
    -- Unpack the visit witness
    simp only at h_visit
    obtain ⟨q, hq_R, hq_color⟩ := h_visit
    -- 2n is in C
    have h_2n_in : 2 * n ∈ C := ⟨q, hq_R, hq_color⟩
    -- No m < 2n is in C
    have h_lt_not_in : ∀ m < 2 * n, m ∉ C := by
      intro m hm ⟨s, hs_R, hs_color⟩
      -- s ∈ R ∩ color⁻¹{k | k < 2n}
      have hs_in_avoid : s ∈ R ∩ a.color ⁻¹' {k | k < 2 * n} := by
        simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
        exact ⟨hs_R, hs_color ▸ hm⟩
      rw [h_avoid] at hs_in_avoid
      exact hs_in_avoid
    -- sInf C = 2n
    have h_sInf : sInf C = 2 * n := sInf_eq_of_min n h_C_ne h_2n_in h_lt_not_in
    -- 2n is even
    rw [h_sInf]
    exact ⟨n, by simp [Nat.two_mul]⟩
  · -- DPA accepts → DRA accepts
    intro h_parity
    -- The minimum color is even; write sInf C = k + k
    obtain ⟨k, hk⟩ := h_parity
    -- sInf C is in C
    have h_sInf_in : sInf C ∈ C := Nat.sInf_mem h_C_ne
    -- sInf C ≤ every element of C
    have h_sInf_min : ∀ m ∈ C, sInf C ≤ m := fun m hm => Nat.sInf_le hm
    -- Note: hk : sInf C = k + k, and 2*k = k + k (we work with k + k directly)
    -- Get a witness state with color sInf C = k + k
    obtain ⟨q, hq_R, hq_color⟩ := h_sInf_in
    -- hq_color : a.color q = sInf C = k + k
    -- Use pair k (i.e., 2 * k but as k + k)
    refine ⟨(a.color ⁻¹' {m | m < k + k}, a.color ⁻¹' {k + k}),
            ⟨k, by simp [Nat.two_mul]⟩, ?_, ⟨q, hq_R, ?_⟩⟩
    · -- Avoidance: R ∩ color⁻¹{m | m < k+k} = ∅
      apply Set.Subset.antisymm _ (Set.empty_subset _)
      intro s ⟨hs_R, hs_lt⟩
      simp only [mem_preimage, mem_ofPred_eq] at hs_lt
      have h_le : sInf C ≤ a.color s := h_sInf_min (a.color s) ⟨s, hs_R, rfl⟩
      rw [hk] at h_le
      exact absurd hs_lt (Nat.not_lt.mpr h_le)
    · -- Visit: q has color k + k
      simp only [mem_preimage, mem_singleton_iff]
      rw [hq_color, hk]

end Cslib.Automata.DA
