/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Automata.DA.Prod

/-! # Closure properties of deterministic Muller automata

This file establishes closure of deterministic Muller automata (DMAs) under finite union
(`DA.Muller.union`), mirroring the DBA union construction in `DA.BuchiClosure` over the
product automaton `DA.prod`. This closure lemma is used by task 241 (McNaughton's theorem,
Choueka route) to fold a finite family of DMAs into a single DMA.

## References

* [W. Thomas, *Automata on Infinite Objects*, Chapter 1][Thomas1990]
-/

@[expose] public section

namespace Cslib.Automata.DA

open Set Filter Cslib.ωSequence ωLanguage ωAcceptor

variable {State1 State2 Symbol : Type*}

/-! ## `infOcc` of a product run projects to the `infOcc` of each component run -/

/-- The image of the product run's `infOcc` under `Prod.fst` equals the `infOcc` of the
first component's run, provided both state spaces are finite. The finiteness of the product
state space is what makes the pigeonhole argument (`frequently_in_finite_type`) apply: a
state `a : State1` recurs in the `da1`-run infinitely often iff *some* pair `(a, b)` recurs
infinitely often in the product run. -/
theorem prod_run_infOcc_fst [Finite State1] [Finite State2]
    (da1 : DA State1 Symbol) (da2 : DA State2 Symbol) (xs : ωSequence Symbol) :
    Prod.fst '' ((da1.prod da2).run xs).infOcc = (da1.run xs).infOcc := by
  ext a
  simp only [Set.mem_image, mem_infOcc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.mono (fun k hk => by rw [← hk, prod_run_eq])
  · intro ha
    have hmem : ∃ᶠ k in atTop, (da1.prod da2).run xs k ∈ {p : State1 × State2 | p.1 = a} := by
      apply ha.mono
      intro k hk
      simp [prod_run_eq, hk]
    rw [ωSequence.frequently_in_finite_type] at hmem
    obtain ⟨x, hx1, hx2⟩ := hmem
    exact ⟨x, hx2, hx1⟩

/-- The image of the product run's `infOcc` under `Prod.snd` equals the `infOcc` of the
second component's run, provided both state spaces are finite. -/
theorem prod_run_infOcc_snd [Finite State1] [Finite State2]
    (da1 : DA State1 Symbol) (da2 : DA State2 Symbol) (xs : ωSequence Symbol) :
    Prod.snd '' ((da1.prod da2).run xs).infOcc = (da2.run xs).infOcc := by
  ext a
  simp only [Set.mem_image, mem_infOcc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.mono (fun k hk => by rw [← hk, prod_run_eq])
  · intro ha
    have hmem : ∃ᶠ k in atTop, (da1.prod da2).run xs k ∈ {p : State1 × State2 | p.2 = a} := by
      apply ha.mono
      intro k hk
      simp [prod_run_eq, hk]
    rw [ωSequence.frequently_in_finite_type] at hmem
    obtain ⟨x, hx1, hx2⟩ := hmem
    exact ⟨x, hx2, hx1⟩

/-! ## DMA Union -/

/-- The DMA union of two deterministic Muller automata, constructed via the product
automaton. The union automaton's accept family consists of the sets `S` whose projection
onto the first (resp. second) component lies in `a1`'s (resp. `a2`'s) accept family. -/
@[scoped grind =]
def Muller.union (a1 : Muller State1 Symbol) (a2 : Muller State2 Symbol) :
    Muller (State1 × State2) Symbol where
  toDA := a1.toDA.prod a2.toDA
  accept := {S : Set (State1 × State2) | Prod.fst '' S ∈ a1.accept ∨ Prod.snd '' S ∈ a2.accept}

/-- The language of the DMA union equals the union of the component languages, provided
both state spaces are finite (needed for the `infOcc`/image pigeonhole argument). -/
@[simp, scoped grind =]
theorem Muller.union_language_eq [Finite State1] [Finite State2]
    (a1 : Muller State1 Symbol) (a2 : Muller State2 Symbol) :
    language (a1.union a2) = language a1 ⊔ language a2 := by
  apply mem_ext
  intro xs
  rw [Cslib.ωLanguage.mem_sup, mem_language, mem_language, mem_language]
  simp only [ωAcceptor.Accepts, Muller.union, Set.mem_setOf_eq]
  rw [prod_run_infOcc_fst, prod_run_infOcc_snd]

end Cslib.Automata.DA
