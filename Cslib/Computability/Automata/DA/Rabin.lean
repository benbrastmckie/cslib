/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.DA.Basic

/-! # Deterministic Rabin and Streett automata

This file defines deterministic Rabin automata (DRA), deterministic Streett automata (DSA),
and proves classical language-preserving conversions.

## Main definitions

* `DA.Rabin` — a `DA` extended with a set of acceptance pairs `(E, F) : Set State × Set State`.
  A run is accepting iff some pair has `E ∩ infOcc = ∅` and `F ∩ infOcc ≠ ∅`.
* `DA.Streett` — a `DA` extended with a set of guarantee pairs `(E, F) : Set State × Set State`.
  A run is accepting iff for all pairs, `F ∩ infOcc ≠ ∅ → E ∩ infOcc ≠ ∅`.
  This is the dual (complement) of Rabin acceptance.

## Main theorems

* `DA.Buchi.toRabin_language_eq` — the DBA-to-DRA conversion is language-preserving.
* `DA.Rabin.toMuller_language_eq` — the DRA-to-DMA conversion is language-preserving.
* `DA.Rabin.toStreett_language_eq` — Rabin-Streett duality (complement).
* `DA.Streett.toRabin_language_eq` — Streett-Rabin duality (complement).

## References

* [W. Thomas, *Infinite Words*, Chapter 3][Thomas2003]
* [C. Baier, J.-P. Katoen, *Principles of Model Checking*, Chapter 4][BaierKatoen2008]
-/

@[expose] public section

namespace Cslib.Automata.DA

open Set Filter Cslib.ωSequence ωLanguage ωAcceptor Acceptor
open scoped Cslib.FLTS

variable {State Symbol : Type*}

/-! ## Rabin acceptance -/

/-- A deterministic Rabin automaton (`DA.Rabin`) extends a `DA` with a set of
*acceptance pairs*. Each pair consists of two sets of states `(E, F)`.

A run on an ω-word `xs` is accepting if there exists a pair `(E, F) ∈ pairs` such that:
- The set `E` is *avoided infinitely often*: `infOcc(run xs) ∩ E = ∅`
- The set `F` is *visited infinitely often*: `infOcc(run xs) ∩ F ≠ ∅`

This is the Rabin acceptance condition, a strictly more expressive acceptance condition than
Büchi acceptance. -/
structure Rabin (State Symbol : Type*) extends DA State Symbol where
  /-- The set of Rabin acceptance pairs. Each pair `(E, F)` specifies an avoidance set `E`
  and an infinitely-visited set `F`. -/
  pairs : Set (Set State × Set State)

namespace Rabin

/-- A run is Rabin-accepting iff some pair `(E, F) ∈ pairs` has `infOcc ∩ E = ∅` and
`(infOcc ∩ F).Nonempty`. -/
@[simp, scoped grind =]
instance : ωAcceptor (Rabin State Symbol) Symbol where
  Accepts (a : Rabin State Symbol) (xs : ωSequence Symbol) :=
    ∃ pair ∈ a.pairs,
      (a.run xs).infOcc ∩ pair.1 = ∅ ∧
      ((a.run xs).infOcc ∩ pair.2).Nonempty

end Rabin

/-! ## Streett acceptance -/

/-- A deterministic Streett automaton (`DA.Streett`) extends a `DA` with a set of
*guarantee pairs*. Each pair consists of two sets of states `(E, F)`.

A run on an ω-word `xs` is accepting if for every pair `(E, F) ∈ pairs`:
- If `F` is *visited infinitely often* (`infOcc ∩ F ≠ ∅`), then `E` is also visited infinitely
  often (`infOcc ∩ E ≠ ∅`).

Streett acceptance is the *dual* of Rabin acceptance: an ω-word is Streett-accepted iff it is
*not* Rabin-rejected (and vice versa). This duality makes Streett automata the complement
type for Rabin automata. -/
structure Streett (State Symbol : Type*) extends DA State Symbol where
  /-- The set of Streett guarantee pairs. Each pair `(E, F)` specifies: whenever `F` is visited
  infinitely often, `E` must also be visited infinitely often. -/
  pairs : Set (Set State × Set State)

namespace Streett

/-- A run is Streett-accepting iff for every pair `(E, F) ∈ pairs`, the condition
`(infOcc ∩ F).Nonempty → (infOcc ∩ E).Nonempty` holds. -/
@[simp, scoped grind =]
instance : ωAcceptor (Streett State Symbol) Symbol where
  Accepts (a : Streett State Symbol) (xs : ωSequence Symbol) :=
    ∀ pair ∈ a.pairs,
      ((a.run xs).infOcc ∩ pair.2).Nonempty →
      ((a.run xs).infOcc ∩ pair.1).Nonempty

end Streett

/-! ## DBA → DRA conversion -/

/-- Convert a deterministic Büchi automaton to a deterministic Rabin automaton with the
same language. The DRA uses a single acceptance pair `(∅, accept)`, encoding the
Büchi condition "accept states occur infinitely often" as "no state in ∅ occurs infinitely
often, and some state in `accept` does". -/
@[scoped grind =]
def Buchi.toRabin (a : Buchi State Symbol) : Rabin State Symbol where
  toDA := a.toDA
  pairs := {(∅, a.accept)}

/-- The DBA-to-DRA conversion preserves the language.

**Proof**: The DRA accepts `xs` iff `∃ (E, F) ∈ {(∅, accept)}, infOcc ∩ E = ∅ ∧
(infOcc ∩ F).Nonempty`, which simplifies to `(infOcc ∩ accept).Nonempty`.
The DBA accepts `xs` iff `∃ᶠ k, run xs k ∈ accept`, which by `frequently_in_finite_type`
is equivalent to `∃ q ∈ accept, ∃ᶠ k, run xs k = q`, i.e., `(infOcc ∩ accept).Nonempty`. -/
@[simp, scoped grind =]
theorem Buchi.toRabin_language_eq [Finite State] (a : Buchi State Symbol) :
    language a.toRabin = language a := by
  apply mem_ext
  intro xs
  rw [ωAcceptor.mem_language, ωAcceptor.mem_language]
  simp only [ωAcceptor.Accepts, Buchi.toRabin, mem_singleton_iff]
  constructor
  · -- DRA accepts → DBA accepts
    rintro ⟨pair, h_pair, h_avoid, h_visit⟩
    subst h_pair
    obtain ⟨q, h_infOcc, h_acc⟩ := h_visit
    rw [mem_infOcc] at h_infOcc
    exact Frequently.mono h_infOcc (fun k hk => hk ▸ h_acc)
  · -- DBA accepts → DRA accepts
    intro h_buchi
    rw [frequently_in_finite_type] at h_buchi
    obtain ⟨q, h_acc, h_freq⟩ := h_buchi
    refine ⟨(∅, a.accept), rfl, ?_, ⟨q, ?_, h_acc⟩⟩
    · simp
    · rw [mem_infOcc]; exact h_freq

/-! ## DRA → DMA conversion -/

/-- Convert a deterministic Rabin automaton to a deterministic Muller automaton with the
same language. The DMA acceptance family consists of all sets `S` of states such that
some Rabin pair `(E, F) ∈ pairs` has `S ∩ E = ∅` and `(S ∩ F).Nonempty`.

This conversion shows every DRA-recognizable language is DMA-recognizable, with the same
state space. Note that the converse (DMA-to-DRA) requires exponentially many pairs and
a different state space; it is not a same-state-space conversion. -/
@[scoped grind =]
def Rabin.toMuller (a : Rabin State Symbol) : Muller State Symbol where
  toDA := a.toDA
  accept := {S | ∃ pair ∈ a.pairs, S ∩ pair.1 = ∅ ∧ (S ∩ pair.2).Nonempty}

/-- The DRA-to-DMA conversion preserves the language.

**Proof**: The DMA accepts `xs` iff `infOcc(run xs) ∈ accept`, i.e., `∃ (E, F) ∈ pairs,
infOcc ∩ E = ∅ ∧ (infOcc ∩ F).Nonempty`. This is exactly the Rabin acceptance condition. -/
@[simp, scoped grind =]
theorem Rabin.toMuller_language_eq (a : Rabin State Symbol) :
    language a.toMuller = language a := by
  apply mem_ext
  intro xs
  rw [ωAcceptor.mem_language, ωAcceptor.mem_language]
  simp only [ωAcceptor.Accepts, Rabin.toMuller, Set.mem_setOf_eq]

/-! ## Rabin–Streett duality -/

/-- Convert a deterministic Rabin automaton to a deterministic Streett automaton by using
the same pairs. The resulting DSA accepts exactly the complement of the DRA's language:
an ω-word is Streett-accepted iff it is not Rabin-accepted.

This construction witnesses the Rabin–Streett duality: the Streett condition with pair set
`P` is the complement of the Rabin condition with the same pair set `P`. -/
@[scoped grind =]
def Rabin.toStreett (a : Rabin State Symbol) : Streett State Symbol where
  toDA := a.toDA
  pairs := a.pairs

/-- The DRA-to-DSA conversion produces the complementary language.

**Proof**: `xs` is Rabin-rejected iff `∀ (E, F) ∈ pairs, infOcc ∩ E ≠ ∅ ∨ (infOcc ∩ F) = ∅`.
This is the Streett acceptance condition: for all pairs, `(infOcc ∩ F).Nonempty →
(infOcc ∩ E).Nonempty` (equivalently, `infOcc ∩ F = ∅ ∨ infOcc ∩ E ≠ ∅`). -/
@[simp, scoped grind =]
theorem Rabin.toStreett_language_eq (a : Rabin State Symbol) :
    language a.toStreett = (language a)ᶜ := by
  apply mem_ext
  intro xs
  simp only [ωAcceptor.mem_language, ωAcceptor.Accepts, Rabin.toStreett]
  rw [Cslib.ωLanguage.mem_compl, ωAcceptor.mem_language, ωAcceptor.Accepts]
  constructor
  · -- Streett accepts → Rabin rejects
    intro h_streett h_rabin
    obtain ⟨pair, h_pair, h_avoid, h_visit⟩ := h_rabin
    have h_e := h_streett pair h_pair h_visit
    rw [h_avoid] at h_e
    exact Set.not_nonempty_empty h_e
  · -- Rabin rejects → Streett accepts
    intro h_not_rabin pair h_pair h_visit
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty] at h_empty
    exact h_not_rabin ⟨pair, h_pair, h_empty, h_visit⟩

/-- Convert a deterministic Streett automaton to a deterministic Rabin automaton by using
the same pairs. The resulting DRA accepts exactly the complement of the DSA's language. -/
@[scoped grind =]
def Streett.toRabin (a : Streett State Symbol) : Rabin State Symbol where
  toDA := a.toDA
  pairs := a.pairs

/-- The DSA-to-DRA conversion produces the complementary language. -/
@[simp, scoped grind =]
theorem Streett.toRabin_language_eq (a : Streett State Symbol) :
    language a.toRabin = (language a)ᶜ := by
  apply mem_ext
  intro xs
  simp only [ωAcceptor.mem_language, ωAcceptor.Accepts, Streett.toRabin]
  rw [Cslib.ωLanguage.mem_compl, ωAcceptor.mem_language, ωAcceptor.Accepts]
  constructor
  · -- Rabin accepts → Streett rejects
    rintro ⟨pair, h_pair, h_avoid, h_visit⟩ h_streett
    have h_e := h_streett pair h_pair h_visit
    rw [h_avoid] at h_e
    exact Set.not_nonempty_empty h_e
  · -- Streett rejects → Rabin accepts
    intro h_not_streett
    simp only [Streett.instωAcceptor, not_forall] at h_not_streett
    obtain ⟨pair, h_pair, h_visit, h_empty⟩ := h_not_streett
    exact ⟨pair, h_pair, Set.not_nonempty_iff_eq_empty.mp h_empty, h_visit⟩

end Cslib.Automata.DA
