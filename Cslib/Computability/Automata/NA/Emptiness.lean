/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.NA.Basic

/-! # NBA Emptiness Checking

Characterization of when a nondeterministic Büchi automaton (NBA) accepts at least
one ω-word. The key result (Baier-Katoen Lemma 4.41) states that the language is
non-empty if and only if there exists a reachable accepting cycle: a state reachable
from a start state that is accepting and lies on a non-trivial cycle.

## Main definitions

* `NA.Buchi.HasReachableAcceptingCycle` -- the NBA has a reachable non-trivial cycle
  through an accepting state

## Main theorems

* `NA.Buchi.hasReachableAcceptingCycle_of_nonempty` -- non-empty language implies
  reachable accepting cycle (requires `[Finite State]`)
* `NA.Buchi.nonempty_of_hasReachableAcceptingCycle` -- reachable accepting cycle implies
  non-empty language (requires `[Inhabited Symbol]`)
* `NA.Buchi.language_nonempty_iff` -- language non-emptiness iff reachable accepting cycle
  (requires both `[Finite State]` and `[Inhabited Symbol]`)
* `NA.Buchi.language_eq_bot_iff` -- language equals bottom iff no reachable accepting cycle

## References

* [C. Baier, J.-P. Katoen, *Principles of Model Checking*][BaierKatoen2008],
  Lemma 4.41 (Criterion for Nonemptiness of an NBA)
-/

@[expose] public section

namespace Cslib.Automata.NA.Buchi

open Set Filter ωSequence ωLanguage ωAcceptor
open scoped LTS

variable {State Symbol : Type*}

/-- An NBA has a reachable accepting cycle if there exists a start state from which
an accepting state is reachable and from which that accepting state can reach itself
via a non-trivial (non-empty) cycle. This is the key semantic criterion for language
non-emptiness (Baier-Katoen Lemma 4.41). -/
def HasReachableAcceptingCycle (a : Buchi State Symbol) : Prop :=
  ∃ s₀ ∈ a.start, ∃ q ∈ a.accept,
    a.toLTS.CanReach s₀ q ∧ ∃ μs, μs ≠ [] ∧ a.toLTS.MTr q μs q

/-- Forward direction of Baier-Katoen Lemma 4.41: if an NBA has a non-empty language,
then it has a reachable accepting cycle. The proof uses the pigeonhole principle
(`frequently_in_finite_type`) to extract an accepting state visited infinitely often,
and then `OmegaExecution.extract_mTr` to produce the reachability path and cycle. -/
theorem hasReachableAcceptingCycle_of_nonempty [Finite State]
    (a : Buchi State Symbol) (h : (ωAcceptor.language a).toSet.Nonempty) :
    a.HasReachableAcceptingCycle := by
  -- Unpack the nonemptiness: get an accepting run
  obtain ⟨xs, ⟨ss, h_run, h_freq⟩⟩ := h
  -- By pigeonhole (finite type), some accepting state q is visited infinitely often
  rw [frequently_in_finite_type] at h_freq
  obtain ⟨q, h_q_acc, h_q_freq⟩ := h_freq
  -- Extract a strictly monotonic function f with ss (f m) = q for all m
  rw [frequently_iff_strictMono] at h_q_freq
  obtain ⟨f, h_f_mono, h_f_q⟩ := h_q_freq
  -- Use f 0 and f 1 as the two witnessing indices (f 0 < f 1 by strict monotonicity)
  have h_f01 : f 0 < f 1 := h_f_mono (by omega)
  -- Witness: s₀ = ss 0, q = q
  refine ⟨ss 0, h_run.start, q, h_q_acc, ?_, ?_⟩
  · -- Reachability: ss 0 can reach q via the finite path extracted from [0, f 0]
    exact ⟨xs.extract 0 (f 0),
      (h_f_q 0) ▸ LTS.OmegaExecution.extract_mTr h_run.trans (by omega)⟩
  · -- Cycle: q can reach itself via the finite path extracted from [f 0, f 1]
    refine ⟨xs.extract (f 0) (f 1), ?_, ?_⟩
    · -- The extract is non-empty since f 0 < f 1
      rw [List.ne_nil_iff_length_pos, ωSequence.length_extract]
      omega
    · -- The MTr witness for q reaching q
      have hmtr := LTS.OmegaExecution.extract_mTr h_run.trans (le_of_lt h_f01)
      rw [h_f_q 0, h_f_q 1] at hmtr
      exact hmtr

/-- Backward direction of Baier-Katoen Lemma 4.41: if an NBA has a reachable accepting
cycle, then its language is non-empty. The proof constructs an explicit accepting ω-word
by prepending the reachability path to infinitely many repetitions of the cycle. The
accepting state `q` then appears at positions `|μs_reach| + k * |μs_cycle|` for all `k`,
witnessing infinite acceptance. -/
theorem nonempty_of_hasReachableAcceptingCycle [Inhabited Symbol]
    (a : Buchi State Symbol) (h : a.HasReachableAcceptingCycle) :
    (ωAcceptor.language a).toSet.Nonempty := by
  -- Unpack the reachable accepting cycle
  obtain ⟨s₀, h_s₀, q, h_q_acc, ⟨μs_reach, h_reach⟩, μs_cycle, h_ne, h_cycle⟩ := h
  -- Build the infinite sequence of cycle labels: const μs_cycle (repeated forever)
  let μls : ωSequence (List Symbol) := ωSequence.const μs_cycle
  -- Each chunk has positive length (cycle is non-trivial)
  have h_pos : ∀ k, (μls k).length > 0 :=
    fun k => by simp [μls, ωSequence.const, List.length_pos_iff.mpr h_ne]
  -- Build the infinite state sequence from the repeated MTr transitions
  have h_mtr : ∀ k, a.toLTS.MTr (ωSequence.const q k) (μls k) (ωSequence.const q (k + 1)) :=
    fun k => by simp [μls, ωSequence.const]; exact h_cycle
  obtain ⟨ss_cycle, h_ωexec_cycle, h_cycle_pos⟩ :=
    LTS.OmegaExecution.flatten_mTr h_mtr h_pos
  -- Compute cumLen for const μs_cycle: cumLen k = k * |μs_cycle|
  have h_cumLen : ∀ k, μls.cumLen k = k * μs_cycle.length := by
    intro k
    induction k with
    | zero => simp [ωSequence.cumLen_zero]
    | succ n ih =>
      change μls.cumLen n + (const μs_cycle n).length = (n + 1) * μs_cycle.length
      simp [ωSequence.const, ih, Nat.succ_mul]
  -- At position cumLen k, ss_cycle visits q
  have h_cycle_q : ∀ k, ss_cycle (μls.cumLen k) = q :=
    fun k => by simp [h_cycle_pos k, ωSequence.const]
  -- Build the infinite label sequence: μs_reach ++ω μls.flatten
  -- and the corresponding state sequence starting at s₀
  have h_cycle_start : ss_cycle 0 = q := by
    have := h_cycle_q 0
    simp [ωSequence.cumLen_zero] at this
    exact this
  obtain ⟨ss, h_ωexec, h_ss0, h_ss_reach, h_drop⟩ :=
    LTS.OmegaExecution.append h_reach h_ωexec_cycle h_cycle_start
  -- The run is valid: starts at s₀
  have h_run : a.Run (μs_reach ++ω μls.flatten) ss :=
    ⟨h_ss0 ▸ h_s₀, h_ωexec⟩
  -- At position |μs_reach| + cumLen k, the state is q
  have h_at_pos : ∀ k, ss (μs_reach.length + μls.cumLen k) = q := by
    intro k
    rw [show ss (μs_reach.length + μls.cumLen k) =
          (ss.drop μs_reach.length) (μls.cumLen k) from by simp [ωSequence.drop, Nat.add_comm],
        h_drop, h_cycle_q k]
  -- Show q appears infinitely often in the state sequence via a linear witness function
  have h_freq : ∃ᶠ k in atTop, ss k ∈ a.accept := by
    rw [frequently_iff_strictMono]
    exact ⟨fun k => μs_reach.length + μls.cumLen k,
      fun a b hab => Nat.add_lt_add_left (ωSequence.cumLen_strictMono h_pos hab) _,
      fun k => h_at_pos k ▸ h_q_acc⟩
  -- Package everything as an element of the language
  exact ⟨μs_reach ++ω μls.flatten, ⟨ss, h_run, h_freq⟩⟩

/-- Baier-Katoen Lemma 4.41: The language of an NBA is non-empty if and only if it has
a reachable accepting cycle. This is the central theorem for NBA emptiness checking. -/
theorem language_nonempty_iff [Finite State] [Inhabited Symbol] (a : Buchi State Symbol) :
    (ωAcceptor.language a).toSet.Nonempty ↔ a.HasReachableAcceptingCycle :=
  ⟨hasReachableAcceptingCycle_of_nonempty a, nonempty_of_hasReachableAcceptingCycle a⟩

/-- The language of an NBA equals bottom (is empty) if and only if the NBA has no reachable
accepting cycle. This is the emptiness decision criterion dual to `language_nonempty_iff`. -/
theorem language_eq_bot_iff [Finite State] [Inhabited Symbol] (a : Buchi State Symbol) :
    ωAcceptor.language a = ⊥ ↔ ¬a.HasReachableAcceptingCycle := by
  constructor
  · intro h hrac
    have hne : (ωAcceptor.language a).toSet.Nonempty :=
      nonempty_of_hasReachableAcceptingCycle a hrac
    simp [ωLanguage.bot_def] at h
    exact hne.ne_empty (by simp [h])
  · intro h
    by_contra hbot
    have hne : (ωAcceptor.language a).toSet.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro heq
      apply hbot
      apply ωLanguage.ext
      simp [ωLanguage.bot_def, heq]
    exact h (hasReachableAcceptingCycle_of_nonempty a hne)

end Cslib.Automata.NA.Buchi
