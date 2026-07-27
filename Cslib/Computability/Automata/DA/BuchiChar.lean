/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Flatten
public import Cslib.Computability.Automata.DA.Basic

/-! # Landweber's theorem and DBA-to-DMA conversion

This file establishes Landweber's characterization of DBA-recognizable languages
and provides a canonical conversion from DBA to DMA.

## Main definitions

* `DA.IsLoop` — a set `S` of states is a *loop* if it is nonempty and every state in `S`
  can reach every other state in `S` via a nonempty word.
* `DA.Muller.ClosedUnderSuperloops` — the Muller acceptance family is closed under
  superloops: if `F ∈ accept` is a loop and `F ⊆ F'` where `F'` is also a loop, then
  `F' ∈ accept`.
* `DA.Buchi.toMuller` — conversion from a DBA to a DMA with the same language.

## Main theorems

* `DA.Buchi.toMuller_language_eq` — the DBA-to-DMA conversion is language-preserving.
* `DA.Muller.dba_recognizable_iff_closedUnderSuperloops` — Landweber's theorem: a DMA
  language is DBA-recognizable iff its acceptance family is closed under superloops.
  **Note**: Both directions are stated as `proof_wanted`; see the respective declarations.

## References

* [W. Thomas, *Infinite Words*, Chapter 3][Thomas2003]
* [C. Baier, J.-P. Katoen, *Principles of Model Checking*, Exercises 4.22-4.23][BaierKatoen2008]
-/

@[expose] public section

namespace Cslib.Automata.DA

open Set Filter Cslib.ωSequence ωLanguage ωAcceptor Acceptor
open scoped Cslib.FLTS Automata.DA.Buchi Automata.DA.FinAcc

variable {State Symbol : Type*}

/-! ## Loop predicate -/

/-- A set `S` of states of a `DA` is a *loop* if it is nonempty and for every pair of
states `s s' ∈ S`, there exists a nonempty word `w` such that `da.mtr s w = s'`.

Defined on the base `DA` type (not `DA.Muller`) so the predicate is reusable for future
Rabin characterizations. -/
def IsLoop (da : DA State Symbol) (S : Set State) : Prop :=
  S.Nonempty ∧ ∀ s ∈ S, ∀ s' ∈ S, ∃ w : List Symbol, w ≠ [] ∧ da.mtr s w = s'

/-! ## Closed under superloops -/

/-- A Muller automaton's acceptance family is *closed under superloops* if, whenever
`F ∈ accept` is a loop and `F ⊆ F'` where `F'` is also a loop, then `F' ∈ accept`.

This is the key structural property that characterizes DBA-recognizable Muller languages
(Landweber's theorem, Thomas 2003 Theorem 3.32). -/
def Muller.ClosedUnderSuperloops (a : Muller State Symbol) : Prop :=
  ∀ F ∈ a.accept, ∀ F' : Set State, a.toDA.IsLoop F' → F ⊆ F' → F' ∈ a.accept

/-! ## DBA → DMA conversion -/

/-- Convert a deterministic Büchi automaton to a deterministic Muller automaton with the
same language. The Muller acceptance family consists of all sets that have nonempty
intersection with the DBA's accepting set: `{S | (S ∩ a.accept).Nonempty}`.

This conversion shows every DBA-recognizable language is also DMA-recognizable. -/
@[scoped grind =]
def Buchi.toMuller (a : Buchi State Symbol) : Muller State Symbol where
  toDA := a.toDA
  accept := {S | (S ∩ a.accept).Nonempty}

/-- The DBA-to-DMA conversion preserves the language: the Muller language of `a.toMuller`
equals the Büchi language of `a`.

**Proof**: The Muller automaton accepts `xs` iff `infOcc(run xs) ∩ a.accept ≠ ∅`, i.e.,
some accepting state appears infinitely often in the run, which is exactly the DBA acceptance
condition. The key step uses `frequently_in_finite_type` to convert between "some element of
`a.accept` appears infinitely often" and "`∃ᶠ k, run xs k ∈ a.accept`". -/
@[simp, scoped grind =]
theorem Buchi.toMuller_language_eq [Finite State] (a : Buchi State Symbol) :
    language a.toMuller = language a := by
  apply mem_ext
  intro xs
  rw [ωAcceptor.mem_language, ωAcceptor.mem_language]
  simp only [ωAcceptor.Accepts, Buchi.toMuller]
  constructor
  · -- Muller accepts (infOcc ∩ accept nonempty) → DBA accepts (∃ᶠ k, run xs k ∈ accept)
    intro hM
    simp only [Set.mem_setOf_eq] at hM
    obtain ⟨q, hq_infOcc, hq_acc⟩ := hM
    rw [mem_infOcc] at hq_infOcc
    exact Frequently.mono hq_infOcc (fun k hk => hk ▸ hq_acc)
  · -- DBA accepts (∃ᶠ k, run xs k ∈ accept) → Muller accepts (infOcc ∩ accept nonempty)
    intro hB
    simp only [Set.mem_setOf_eq]
    rw [frequently_in_finite_type] at hB
    obtain ⟨q, hq_acc, hq_freq⟩ := hB
    exact ⟨q, hq_freq, hq_acc⟩

/-! ## Landweber's theorem (proof_wanted) -/

/-- **Backward direction of Landweber's theorem**:
If the Muller language of `a` is DBA-recognizable, then `a.ClosedUnderSuperloops`.

**Proof sketch** (Thomas 2003 Theorem 3.32, backward direction):
Given `B : Buchi State Symbol` with `language B = language a`, take `F ∈ a.accept` and
a superloop `F' ⊇ F`. We must show `F' ∈ a.accept`.

Construct an ω-word `xs` such that:
1. The `a`-run has `infOcc(run_a xs) = F'` (so `a` accepts via `F'`).
2. The word is in `language a`, hence in `language B` (so `B` accepts `xs`).

For (2): since `B` accepts `xs` and `language B = language a`, we have `xs ∈ language a`,
i.e., the `a`-run has infOcc ∈ accept. Since we built `xs` to have infOcc = `F'`, we get
`F' ∈ accept`.

Construction of `xs`: Use `ωSequence.flatten` to interleave:
- A prefix `w₀` reaching some `q₀ ∈ F`;
- Repeated cycles through `F` (using the `F`-loop connectivity);
- Interleaved traversals of `F'` (using the `F'`-loop connectivity).

This ensures infOcc = `F'` and the word is in `language a` (since `F ∈ accept` and the
run visits `F` infinitely often). -/
proof_wanted Muller.dba_recognizable_implies_closedUnderSuperloops
    {State Symbol : Type*} [Fintype State] [DecidableEq State]
    (a : Muller State Symbol)
    (B : Buchi State Symbol) (hB : language B = language a) :
    a.ClosedUnderSuperloops

/-- **Forward direction of Landweber's theorem**:
If `a.ClosedUnderSuperloops`, then the Muller language of `a` is DBA-recognizable.

**Construction** (Thomas 2003 Theorem 3.32, forward direction; gap filled per Thomas 2003
research note — the "outnumbered" condition is interpreted as containment of an accepting set):

Define DBA `B` over state space `State × Finset State`:
- First component: current state of `a`.
- Second component: accumulated `a`-states since the last reset, as `Finset State`.
- **Transition**: `(q, R) →[σ] (q', R')` where `q' = a.tr q σ`, and:
  - `R' = ∅` (reset) if `∃ F ∈ a.accept, F.toSet ⊆ insert q' R.toSet`;
  - `R' = insert q' R` (accumulate) otherwise.
- **Accepting states of `B`**: `{(q, ∅)}`, i.e., just-reset states.

**Key lemma**: Resets occur infinitely often iff `infOcc(run_a xs) ∈ a.accept`.
  - Forward (resets → infOcc ∈ accept): Each reset requires the accumulated set to contain
    some `F ∈ accept`. As resets pile up, the accumulated infOcc must contain some F, so
    by `ClosedUnderSuperloops`, infOcc ∈ accept.
  - Backward (infOcc ∈ accept → resets): Since infOcc ⊆ F' ∈ accept for some F', and the
    run visits all elements of F' infinitely often, each element of F' accumulates infinitely
    often, triggering resets. -/
proof_wanted Muller.closedUnderSuperloops_implies_dba_recognizable
    {State Symbol : Type*} [Fintype State] [DecidableEq State]
    (a : Muller State Symbol) (h : a.ClosedUnderSuperloops) :
    ∃ (B : Buchi State Symbol), language B = language a

/-- **Landweber's theorem**: A Muller language is DBA-recognizable if and only if the
acceptance family is closed under superloops (Thomas 2003, Theorem 3.32).

This characterization shows that DBA-recognizable languages are exactly those whose Muller
acceptance families are *locally closed*: whenever a loop `F` is accepted, every superloop
of `F` is also accepted. This contrasts with general Muller languages, which can have
arbitrary (finite Boolean combinations of) acceptance conditions.

**Status of proof**: Both directions are deferred. See:
- `DA.Muller.dba_recognizable_implies_closedUnderSuperloops` for the backward direction;
- `DA.Muller.closedUnderSuperloops_implies_dba_recognizable` for the forward direction. -/
proof_wanted Muller.dba_recognizable_iff_closedUnderSuperloops
    {State Symbol : Type*} [Fintype State] [DecidableEq State]
    (a : Muller State Symbol) :
    (∃ (B : Buchi State Symbol), language B = language a) ↔
    a.ClosedUnderSuperloops

end Cslib.Automata.DA
