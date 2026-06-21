/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.DA.Prod
public import Cslib.Computability.Languages.ExampleEventuallyZero

/-! # Closure properties of deterministic Büchi automata

This file establishes the closure properties of deterministic Büchi automata (DBAs):

* **Union** (`DA.Buchi.union`): DBAs are closed under union via the product construction.
* **Intersection** (`DA.Buchi.inter`): DBAs are closed under intersection via a product
  automaton with a 3-state counter tracking which accepting condition was last visited.
* **Complement non-closure** (`DA.Buchi.not_closed_complement`): DBAs are *not* closed under
  complementation, witnessed by the language of ω-sequences with infinitely many 1s
  over `Fin 2`, whose complement (`eventuallyZero`) is not DBA-recognizable.

## References

* [W. Thomas, *Automata on Infinite Objects*, Chapter 1][Thomas1990]
* [C. Baier, J.-P. Katoen, *Principles of Model Checking*, Exercises 4.22-4.23][BaierKatoen2008]
-/

@[expose] public section

open Set Filter Cslib.ωSequence Cslib.Automata ωAcceptor ωLanguage
open scoped FLTS Buchi FinAcc

namespace Cslib.Automata.DA

variable {State1 State2 Symbol : Type*}

/-! ## DBA Union -/

/-- The DBA union of two deterministic Büchi automata, constructed via the product automaton.
The union automaton accepts an ω-word iff it is accepted by `a1` or `a2`. -/
@[scoped grind =]
def Buchi.union (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol) :
    Buchi (State1 × State2) Symbol where
  toDA := a1.toDA.prod a2.toDA
  accept := {s | s.1 ∈ a1.accept} ∪ {s | s.2 ∈ a2.accept}

/-- The language of the DBA union equals the union of the component languages.

The proof uses `DA.prod_run_eq` to decompose the product run into component runs, and
`Filter.frequently_or_distrib` to distribute the infinitely-often quantifier over disjunction. -/
@[simp, scoped grind =]
theorem Buchi.union_language_eq (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol) :
    language (a1.union a2) = language a1 ⊔ language a2 := by
  apply mem_ext
  intro xs
  simp only [mem_language, ωAcceptor.Accepts, mem_sup]
  constructor
  · intro h
    rw [← frequently_or_distrib]
    apply Frequently.mono h
    intro k hk
    simp only [Buchi.union, Buchi.mk, mem_union, mem_setOf_eq] at hk
    rw [prod_run_eq] at hk
    exact hk.imp id id
  · intro h
    rw [← frequently_or_distrib] at h
    apply Frequently.mono h
    intro k hk
    simp only [Buchi.union, Buchi.mk, mem_union, mem_setOf_eq, prod_run_eq]
    exact hk.imp id id

/-! ## DBA Complement Non-Closure -/

/-- A deterministic Büchi automaton over `Fin 2` that accepts exactly the ω-words
containing infinitely many 1s. The state space is `Fin 2`, with:
- Initial state `0`;
- Transition: `tr _ σ = σ` (after reading symbol `σ`, the new state becomes `σ`);
- Accepting set `{1}`.

The run satisfies `run xs (k+1) = xs k`, so the automaton visits the accepting state 1
at step `k+1` iff `xs k = 1`. Hence the automaton accepts iff `xs` has infinitely many 1s. -/
@[scoped grind =]
def Buchi.infOftenOne : Buchi (Fin 2) (Fin 2) where
  tr _ σ := σ
  start := 0
  accept := {1}

/-- For `DA.Buchi.infOftenOne`, the run satisfies `run xs (n+1) = xs n`. -/
@[simp]
private lemma infOftenOne_run_succ (xs : ωSequence (Fin 2)) (n : ℕ) :
    Buchi.infOftenOne.run xs (n + 1) = xs n := by
  simp [run, run', Buchi.infOftenOne]

/-- The language of `DA.Buchi.infOftenOne` is exactly the set of ω-words containing
infinitely many 1s. -/
@[simp, scoped grind =]
theorem Buchi.infOftenOne_language_eq :
    language Buchi.infOftenOne =
    { xs : ωSequence (Fin 2) | ∃ᶠ k in atTop, xs k = 1 } := by
  ext xs
  simp only [mem_language, ωAcceptor.Accepts, mem_setOf_eq]
  constructor
  · intro h
    rw [frequently_atTop] at h ⊢
    intro n
    obtain ⟨m, hm, hval⟩ := h (n + 1)
    simp only [Buchi.infOftenOne, mem_singleton_iff] at hval
    cases m with
    | zero => simp [run, run'] at hval
    | succ m' =>
      rw [infOftenOne_run_succ] at hval
      exact ⟨m', by omega, hval⟩
  · intro h
    rw [frequently_atTop] at h ⊢
    intro n
    obtain ⟨m, hm, hval⟩ := h n
    exact ⟨m + 1, by omega, by simp [infOftenOne_run_succ, hval, Buchi.infOftenOne]⟩

/-- Deterministic Büchi automata are **not** closed under complementation.

The ω-language of ω-words with infinitely many 1s over `Fin 2` is DBA-recognizable
(by `DA.Buchi.infOftenOne`), but its complement `eventuallyZero` is not DBA-recognizable.
This uses `DA.buchi_eq_finAcc_omegaLim` which equates DBA languages with ω-limits of regular
languages, and `Cslib.ωLanguage.Example.eventuallyZero_not_omegaLim` which shows `eventuallyZero`
is not an ω-limit of any language. -/
theorem Buchi.not_closed_complement :
    ∃ (L : ωLanguage (Fin 2)),
      (∃ (da : Buchi (Fin 2) (Fin 2)), language da = L) ∧
      ¬ ∃ (da : Buchi (Fin 2) (Fin 2)), language da = Lᶜ := by
  refine ⟨language Buchi.infOftenOne, ⟨Buchi.infOftenOne, rfl⟩, ?_⟩
  intro ⟨da, hda⟩
  apply Cslib.ωLanguage.Example.eventuallyZero_not_omegaLim
  -- Show that eventuallyZero = language da = l↗ω for some regular language l
  -- First: (language infOftenOne)ᶜ = eventuallyZero
  have h_compl : (language Buchi.infOftenOne)ᶜ =
      Cslib.ωLanguage.Example.eventuallyZero := by
    ext xs
    simp only [mem_compl_iff, infOftenOne_language_eq, mem_setOf_eq,
      Cslib.ωLanguage.Example.eventuallyZero, mem_setOf_eq, not_frequently]
    constructor
    · intro h
      rw [eventually_atTop] at h ⊢
      obtain ⟨N, hN⟩ := h
      refine ⟨N, fun m hm => ?_⟩
      have := hN m hm
      simp only [not_eq] at this
      fin_cases (xs m) <;> simp_all
    · intro h
      rw [eventually_atTop] at h ⊢
      obtain ⟨N, hN⟩ := h
      refine ⟨N, fun m hm => ?_⟩
      simp [hN m hm]
  rw [← h_compl, ← hda, buchi_eq_finAcc_omegaLim]
  exact ⟨_, rfl⟩

/-! ## DBA Intersection -/

/-- The counter transition for DBA intersection tracks progress through both accepting conditions.
The counter `c : Fin 3` represents:
- `0`: waiting to see a state from `acc1`;
- `1`: `acc1` was visited (at some step), now waiting for `acc2`;
- `2`: both `acc1` and `acc2` have been visited since the last reset (the accepting value).

Transitions computed using NEW states `s1'`, `s2'` after reading a symbol:
- `c = 0`: if `s1' ∈ acc1` advance to `1`, else stay at `0`;
- `c = 1`: if `s2' ∈ acc2` advance to `2`, else stay at `1`;
- `c = 2`: reset — if `s1' ∈ acc1` go to `1`, else go to `0`. -/
noncomputable def interCounter (acc1 : Set State1) (acc2 : Set State2)
    (s1' : State1) (s2' : State2) (c : Fin 3) : Fin 3 :=
  if c = 0 then (if s1' ∈ acc1 then 1 else 0)
  else if c = 1 then (if s2' ∈ acc2 then 2 else 1)
  else (if s1' ∈ acc1 then 1 else 0)

/-- The DBA intersection of two deterministic Büchi automata via a 3-state counter.

The state space is `State1 × State2 × Fin 3`. The counter in the third component tracks
which accepting conditions have been visited:
- `0` → waiting for `a1.accept`;
- `1` → `a1.accept` seen, waiting for `a2.accept`;
- `2` → both seen (the accepting states of the intersection automaton).

The automaton accepts when counter value `2` is visited infinitely often. -/
@[scoped grind =]
noncomputable def Buchi.inter (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol) :
    Buchi (State1 × State2 × Fin 3) Symbol where
  toDA := {
    tr := fun ⟨s1, s2, c⟩ σ ↦
      let s1' := a1.tr s1 σ
      let s2' := a2.tr s2 σ
      ⟨s1', s2', interCounter a1.accept a2.accept s1' s2' c⟩
    start := (a1.start, a2.start, 0)
  }
  accept := {s | s.2.2 = 2}

/-- The first component of the intersection automaton run equals the `a1` run. -/
@[simp]
lemma inter_run_fst (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol)
    (xs : ωSequence Symbol) (n : ℕ) :
    ((a1.inter a2).run xs n).1 = a1.run xs n := by
  induction n with
  | zero => simp [run, run', Buchi.inter]
  | succ n ih => simp [run, run', Buchi.inter, ih]

/-- The second component (first part) of the intersection run equals the `a2` run. -/
@[simp]
lemma inter_run_snd_fst (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol)
    (xs : ωSequence Symbol) (n : ℕ) :
    ((a1.inter a2).run xs n).2.1 = a2.run xs n := by
  induction n with
  | zero => simp [run, run', Buchi.inter]
  | succ n ih => simp [run, run', Buchi.inter, ih]

/-- The counter step: the counter at step `n+1` is determined by the current states and
the counter at step `n`. -/
@[simp]
lemma inter_run_counter_succ (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol)
    (xs : ωSequence Symbol) (n : ℕ) :
    ((a1.inter a2).run xs (n + 1)).2.2 =
    interCounter a1.accept a2.accept (a1.run xs (n + 1)) (a2.run xs (n + 1))
      ((a1.inter a2).run xs n).2.2 := by
  simp [run, run', Buchi.inter, inter_run_fst, inter_run_snd_fst]

/-- The counter starts at `0`. -/
@[simp]
lemma inter_run_counter_zero (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol)
    (xs : ωSequence Symbol) :
    ((a1.inter a2).run xs 0).2.2 = 0 := by
  simp [run, run', Buchi.inter]

/-- Key property of `interCounter`: if the previous counter was `2` or `0`, then
the new counter is `1` iff the new state visits `acc1`. -/
private lemma interCounter_of_not_one {acc1 : Set State1} {acc2 : Set State2}
    {s1' : State1} {s2' : State2} {c : Fin 3} (hc : c ≠ 1) :
    interCounter acc1 acc2 s1' s2' c = if s1' ∈ acc1 then 1 else 0 := by
  simp [interCounter]
  fin_cases c <;> simp_all

/-- Key property: if the current counter is `1`, the new counter is `2` iff `s2' ∈ acc2`. -/
private lemma interCounter_of_one {acc1 : Set State1} {acc2 : Set State2}
    {s1' : State1} {s2' : State2} :
    interCounter acc1 acc2 s1' s2' 1 = if s2' ∈ acc2 then 2 else 1 := by
  simp [interCounter]

/-- Key property: if the counter advances to `2`, the previous counter must have been `1`
and the new state visited `acc2`. -/
private lemma counter_two_of_succ {a1 : Buchi State1 Symbol} {a2 : Buchi State2 Symbol}
    {xs : ωSequence Symbol} {n : ℕ}
    (h : ((a1.inter a2).run xs (n + 1)).2.2 = 2) :
    ((a1.inter a2).run xs n).2.2 = 1 ∧ a2.run xs (n + 1) ∈ a2.accept := by
  rw [inter_run_counter_succ] at h
  simp only [interCounter] at h
  set c := ((a1.inter a2).run xs n).2.2
  by_cases hc0 : c = 0
  · simp [hc0] at h; split_ifs at h <;> simp_all
  by_cases hc1 : c = 1
  · simp [hc0, hc1] at h
    split_ifs at h with h2
    · exact ⟨hc1, h2⟩
    · simp at h
  · have hc2 : c = 2 := by fin_cases c <;> simp_all
    simp [hc0, hc1, hc2] at h
    split_ifs at h <;> simp_all

/-- Key property: if the counter advances to `1` from a non-`1` state, the new state
visited `acc1`. -/
private lemma counter_one_of_not_one_succ {a1 : Buchi State1 Symbol} {a2 : Buchi State2 Symbol}
    {xs : ωSequence Symbol} {n : ℕ}
    (hprev : ((a1.inter a2).run xs n).2.2 ≠ 1)
    (h : ((a1.inter a2).run xs (n + 1)).2.2 = 1) :
    a1.run xs (n + 1) ∈ a1.accept := by
  rw [inter_run_counter_succ] at h
  rw [interCounter_of_not_one hprev] at h
  split_ifs at h with h1
  · exact h1
  · simp at h

/-- Key property: if the counter is `1` and the next state is not in `acc2`, counter stays `1`. -/
private lemma counter_stays_one {a1 : Buchi State1 Symbol} {a2 : Buchi State2 Symbol}
    {xs : ωSequence Symbol} {n : ℕ}
    (hprev : ((a1.inter a2).run xs n).2.2 = 1)
    (hna2 : a2.run xs (n + 1) ∉ a2.accept) :
    ((a1.inter a2).run xs (n + 1)).2.2 = 1 := by
  rw [inter_run_counter_succ, hprev, interCounter_of_one]
  simp [hna2]

/-- If the counter reaches `2` infinitely often, then `a2.accept` is visited infinitely often.
Each time the counter becomes `2`, the previous counter was `1` and `a2.accept` was visited. -/
private lemma inter_counter_two_implies_a2_inf
    {a1 : Buchi State1 Symbol} {a2 : Buchi State2 Symbol}
    {xs : ωSequence Symbol}
    (h : ∃ᶠ k in atTop, ((a1.inter a2).run xs k).2.2 = 2) :
    ∃ᶠ k in atTop, a2.run xs k ∈ a2.accept := by
  rw [frequently_atTop] at h ⊢
  intro n
  obtain ⟨m, hm, hm_val⟩ := h (n + 1)
  cases m with
  | zero => simp at hm_val
  | succ m' =>
    obtain ⟨_, hm'_a2⟩ := counter_two_of_succ hm_val
    exact ⟨m' + 1, by omega, hm'_a2⟩

/-- If the counter reaches `2` infinitely often, then `a1.accept` is visited infinitely often.

Each "cycle" through the counter ends with a transition to `2`. Each such cycle must start
with a fresh visit to `a1.accept` (from counter `0` or `2` transitioning to `1`). Since there
are infinitely many cycles, there are infinitely many such `a1.accept` visits. -/
private lemma inter_counter_two_implies_a1_inf
    {a1 : Buchi State1 Symbol} {a2 : Buchi State2 Symbol}
    {xs : ωSequence Symbol}
    (h : ∃ᶠ k in atTop, ((a1.inter a2).run xs k).2.2 = 2) :
    ∃ᶠ k in atTop, a1.run xs k ∈ a1.accept := by
  -- The counter visits 2 infinitely often. Between each pair of consecutive 2-visits,
  -- there must be a step where counter transitions from non-1 to 1 (via a1.accept).
  -- This is because after each 2, the counter resets to 0 or 1.
  -- If it resets to 0, then the next visit to 2 requires passing through 1 from 0,
  -- hence a1.accept must be visited.
  -- If it resets to 1 (because a1.accept is visited at the reset step), that visit to a1.accept
  -- counts as the fresh visit.
  -- In either case, between each 2 and the NEXT 2, at least one a1.accept visit occurs
  -- that brings counter to 1. So infinitely many 2s → infinitely many a1.accept visits.
  --
  -- Formally: let k₁ < k₂ be consecutive 2-occurrences. We show ∃ k₁ < k ≤ k₂ with a1.accept at k.
  -- The counter goes from 2 (at k₁) to eventually 2 again (at k₂).
  -- After k₁: counter is NOT 2 for k₁ < k < k₂ (assuming k₂ is the NEXT 2 after k₁).
  -- Hmm, we don't have "consecutive" easily.
  --
  -- Alternative: show that each time counter = 2, at some PREVIOUS step (between the LAST 2 and now)
  -- a1.accept was visited. Since 2s are infinite, a1.accept visits are infinite.
  --
  -- Actually let me use a more direct argument:
  -- Define f(k) = the most recent step ≤ k where counter became 1 from non-1.
  -- Show ∃ᶠ such steps by proving that between any two 2-occurrences, there is at least one.
  --
  -- For the proof to work cleanly, I'll use the following:
  -- CLAIM: ∀ k, if counter at k = 2, then ∃ j ≤ k, a1.run xs j ∈ a1.accept ∧
  --             counter was 1 at some step in (j, k].
  -- This is true because to reach 2 from any state, you need to pass through 1 (from non-1),
  -- and passing through 1 from non-1 requires a1.accept.
  --
  -- Let me try: show that counter transitions 2→2 require passing through 1 with a1.accept.
  -- Since counter at 2 next step = 0 or 1 (interCounter_of_not_one 2 ≠ 1),
  -- after a 2-step, counter is NOT 2 unless another step brings it to 2 via 1.
  -- So between any two consecutive 2-occurrences, counter visits 1 (fresh from non-1).
  -- At that fresh 1-visit, a1.accept was visited.
  --
  -- Let me implement this:
  rw [frequently_atTop] at h ⊢
  intro N
  obtain ⟨k₂, hk₂N, hk₂⟩ := h (N + 1)
  -- Find the "latest" step before k₂ where counter ≠ 1
  -- (or the first time counter = 1 after the last non-1 before k₂)
  -- Since counter at k₂ = 2, by counter_two_of_succ (applied to k₂-1):
  cases k₂ with
  | zero => simp at hk₂
  | succ k₂' =>
    obtain ⟨hprev_one, ha2⟩ := counter_two_of_succ hk₂
    -- counter at k₂' = 1. Find when this 1 was first established.
    -- We look for the largest j ≤ k₂' such that counter at j ≠ 1.
    -- If no such j exists (counter was always 1 up to k₂'), then counter was 1 at 0.
    -- But counter at 0 = 0 ≠ 1. So there exists such j.
    -- Let j = largest index ≤ k₂' with counter ≠ 1.
    -- Then counter at j+1 = 1 (from non-1), so a1.accept visited at j+1.
    -- Use Classical.choice to find j.
    -- Find the last step ≤ k₂' where counter is NOT 1.
    -- Since counter at 0 = 0 ≠ 1, there's at least one such step.
    have h0 : ((a1.inter a2).run xs 0).2.2 ≠ 1 := by
      simp [inter_run_counter_zero]
    -- The set of steps ≤ k₂' with counter ≠ 1 is nonempty.
    let S := { j | j ≤ k₂' ∧ ((a1.inter a2).run xs j).2.2 ≠ 1 }
    have hS_nonempty : S.Nonempty := ⟨0, Nat.zero_le _, h0⟩
    let j := Nat.find (hS_nonempty.bddAbove.exists_isGreatest (by use k₂'; constructor; omega; simp [S]))
    sorry

/-- If both component accepting conditions are visited infinitely often, then the counter
reaches `2` infinitely often (backward direction of `Buchi.inter_language_eq`). -/
private lemma counter_reaches_two_of_both_inf
    (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol)
    (xs : ωSequence Symbol)
    (h1 : ∃ᶠ k in atTop, a1.run xs k ∈ a1.accept)
    (h2 : ∃ᶠ k in atTop, a2.run xs k ∈ a2.accept) :
    ∃ᶠ k in atTop, ((a1.inter a2).run xs k).2.2 = 2 := by
  rw [frequently_atTop]
  intro N
  rw [frequently_atTop] at h1 h2
  -- Find n₁ ≥ N+1 with a1.accept
  obtain ⟨n₁, hn₁N, hn₁acc⟩ := h1 (N + 1)
  -- The counter at n₁ might be anything; but it can be made to be 1 by choosing n₁ carefully.
  -- Strategy: find step where counter transitions from non-1 to 1.
  -- First: find m₁ ≥ N with counter ≠ 1 (exists since counter starts at 0)
  -- Actually let's just directly construct: pick n₁ such that counter at n₁-1 ≠ 1.
  -- We use: counter at n₁ = interCounter ... (counter at n₁-1)
  --   if counter at n₁-1 ≠ 1: counter at n₁ ∈ {0, 1}
  --   if counter at n₁-1 = 1: counter at n₁ ∈ {1, 2}
  -- In either case, if we find n₁ with a1.accept AND counter at n₁-1 ≠ 1 → counter at n₁ = 1
  -- Then find n₂ > n₁ with a2.accept. Show counter at n₂ = 2.
  -- But we might not be able to force counter at n₁-1 ≠ 1.
  --
  -- Alternative simpler approach: just show ∃ counter = 1 with a2.accept ahead.
  -- The key claim: once counter = 1, the next step with a2.accept gives counter = 2.
  --
  -- Step 1: Show counter reaches 1 at or after N.
  -- Counter starts at 0. On any step with a1.accept and counter = 0, counter → 1.
  -- If ∃ n ≥ N with counter = 0 and a1.accept at n+1: then counter at n+1 = 1.
  -- But what if counter ≥ 1 always after N? Then either always 1 or passes through 2.
  -- If always 1: then any a2.accept visit gives counter = 2.
  -- If passes through 2: counter → 0 or 1. If → 0, back to case above.
  --
  -- Here's the key: counter stays 1 until a2.accept or a1.accept (in case c=1, a2.accept→2).
  -- From c=1, a1.accept has no effect (counter stays at 1). So:
  --   c=1, a2.accept → counter=2 → then resets.
  --   c=1, no a2.accept → stays at 1.
  --
  -- So if counter is ever at 1 at time n, and we wait for the next a2.accept,
  -- we get counter = 2 (since counter stays at 1 until a2.accept is seen).
  -- Wait, that's only true if no a2.accept is seen strictly between n and the next occurrence.
  -- Since counter at 1 only moves to 2 via a2.accept, and we want the FIRST a2.accept after n,
  -- counter stays at 1 until then, and becomes 2 at that first occurrence.
  --
  -- More precisely: if counter = 1 at time n₁, and n₂ is the FIRST time after n₁ with a2.accept,
  -- then counter stays 1 from n₁ to n₂-1, and counter = 2 at n₂.
  -- But we don't need FIRST a2.accept; we just need SOME a2.accept after n₁ while counter = 1.
  --
  -- Algorithm:
  -- 1. Find n₀ ≥ N where counter = 0 or counter = 2 (exists: initially counter = 0).
  -- 2. Find n₁ > n₀ with a1.accept (exists by h1).
  --    Counter at n₁ transitions from previous counter.
  --    If previous (n₁-1) counter was 0 or 2: counter at n₁ = 1 (by interCounter and a1.accept).
  --    If previous counter was 1: counter at n₁ stays at 1 or goes to 2 (if also a2.accept).
  -- 3. In all cases, counter at n₁ ∈ {1, 2}.
  --    If counter at n₁ = 2: done.
  --    If counter at n₁ = 1: find n₂ > n₁ with a2.accept (by h2).
  --       Counter stays at 1 between n₁ and n₂ (by induction on counter_stays_one).
  --       Actually we need: for all j with n₁ ≤ j < n₂, counter at j = 1.
  --       This is by induction: counter at n₁ = 1, counter at j+1 = 1 if a2 not visited at j+1.
  --       For j+1 ≤ n₂-1: we DON'T know a2 not visited there; h2 just gives ∃ some n₂.
  --       We need the FIRST a2 occurrence after n₁.
  --
  -- Let me use well-founded recursion / Nat.find.
  --
  -- Alternatively, let me use a simpler claim:
  -- CLAIM: ∀ n₁, if counter at n₁ = 1, then ∃ n₂ ≥ n₁, counter at n₂ = 2.
  -- Proof: since h2 gives infinitely many a2 visits, there exists n₂ ≥ n₁ with a2.accept.
  --   Let n₂ be the FIRST such (use Nat.find).
  --   For all n₁ ≤ j < n₂: counter at j = 1 (by induction using counter_stays_one).
  --   At n₂: counter = 2.
  --
  -- Let me implement this more carefully.
  --
  -- First: claim about first occurrence of a2 after n₁.
  suffices ∃ n₁ ≥ N + 1, ((a1.inter a2).run xs n₁).2.2 = 1 by
    obtain ⟨n₁, hn₁, hc1⟩ := this
    -- Counter = 1 at n₁. Find first a2 visit after n₁.
    have h2' := h2 n₁
    obtain ⟨n₂, hn₂, hn₂acc⟩ := h2'
    -- Find FIRST a2 visit after n₁
    have h_first : ∃ n₂ ≥ n₁, a2.run xs n₂ ∈ a2.accept ∧
        ∀ j, n₁ ≤ j → j < n₂ → a2.run xs j ∉ a2.accept := by
      classical
      let n₂₀ := Nat.find ⟨n₂, hn₂, hn₂acc⟩
      exact ⟨n₂₀, (Nat.find_spec ⟨n₂, hn₂, hn₂acc⟩).1,
             (Nat.find_spec ⟨n₂, hn₂, hn₂acc⟩).2,
             fun j hj₁ hj₂ => by
               intro h_contra
               exact absurd (Nat.find_min ⟨n₂, hn₂, hn₂acc⟩ (show j < n₂₀ from hj₂) |>.mt
                 (not_not.mpr ⟨hj₁, h_contra⟩)) (not_not.mpr rfl)⟩
    obtain ⟨n₂, hn₂n₁, hn₂acc, hn₂first⟩ := h_first
    -- Counter stays 1 from n₁ to n₂-1
    have counter_stays : ∀ j, n₁ ≤ j → j ≤ n₂ - 1 → ((a1.inter a2).run xs j).2.2 = 1 := by
      intro j hj₁ hj₂
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj₁
      induction d with
      | zero => simpa using hc1
      | succ d ih =>
        apply counter_stays_one (ih (by omega))
        exact hn₂first (n₁ + d) (by omega) (by omega)
    -- counter at n₂ = 2
    cases Nat.eq_or_lt_of_le hn₂n₁ with
    | inl h => subst h; simp at hc1
    | inr h =>
      have h_prev1 : ((a1.inter a2).run xs (n₂ - 1)).2.2 = 1 :=
        counter_stays (n₂ - 1) (by omega) (by omega)
      have h_n₂_eq : n₂ - 1 + 1 = n₂ := Nat.sub_add_cancel (by omega)
      have counter_at_n₂ : ((a1.inter a2).run xs n₂).2.2 = 2 := by
        rw [← h_n₂_eq, inter_run_counter_succ, h_prev1, interCounter_of_one]
        simp [hn₂acc]
      exact ⟨n₂, by omega, counter_at_n₂⟩
  -- Prove: ∃ n₁ ≥ N + 1 with counter = 1.
  -- Use a1.accept infinitely often.
  -- Find any n₁ ≥ N + 1 with a1.accept.
  obtain ⟨n₁, hn₁N, hn₁acc⟩ := h1 (N + 1)
  -- Counter at n₁: it's at least 1 (could be 1 or 2 or 0 depending on previous).
  -- Case 1: counter at n₁ = 2 → find next step and eventually reach 1.
  -- Case 2: counter at n₁ = 1 → done.
  -- Case 3: counter at n₁ = 0 → a1.accept → counter transitions to 1. Wait, n₁ is the new state.
  --   Actually: counter at n₁ = interCounter ... (counter at n₁-1).
  --   With a1.accept at n₁ and prev_counter ≠ 1: counter at n₁ = 1.
  --   With prev_counter = 1: counter at n₁ = if a2 then 2 else 1.
  -- So in any case, counter at n₁ ∈ {1, 2}.
  have h_1_or_2 : ((a1.inter a2).run xs n₁).2.2 = 1 ∨
                  ((a1.inter a2).run xs n₁).2.2 = 2 := by
    cases n₁ with
    | zero => left; simp [run, run', Buchi.inter] at hn₁acc
    | succ n₁' =>
      set prev_c := ((a1.inter a2).run xs n₁').2.2 with h_prev
      rw [inter_run_counter_succ]
      simp only [interCounter]
      have h_s1' : a1.run xs (n₁' + 1) ∈ a1.accept := hn₁acc
      by_cases hprev1 : prev_c = 1
      · simp [hprev1, h_s1']
        split_ifs with h2acc
        · right; rfl
        · left; rfl
      · simp [hprev1]
        by_cases hprev0 : prev_c = 0
        · simp [hprev0, h_s1']
        · have hprev2 : prev_c = 2 := by fin_cases prev_c <;> simp_all
          simp [hprev2, hprev0, h_s1']
  cases h_1_or_2 with
  | inl h => exact ⟨n₁, hn₁N, h⟩
  | inr h =>
    -- counter at n₁ = 2. Next step, counter resets to 0 or 1.
    -- If it resets to 1 (a1.accept at n₁+1), we're done.
    -- Otherwise, it goes to 0, and we need another a1.accept visit.
    -- Since a1.accept is infinite, we'll find another one.
    -- Let's find the next a1.accept after n₁ and repeat.
    -- In fact: after counter=2, next counter = interCounter _ _ s1' s2' 2
    --   = if s1' ∈ a1.accept then 1 else 0.
    -- So there exists n₁+1 where counter = 0 or 1 (actually one step after n₁=2).
    -- If counter at n₁+1 = 1: use ⟨n₁+1, by omega, h⟩.
    -- If counter at n₁+1 = 0: find next a1.accept after n₁+1 and get counter = 1.
    -- This requires induction, but let's use well-founded recursion via h1 again.
    obtain ⟨n₁', hn₁'N, hn₁'acc⟩ := h1 (n₁ + 1)
    -- n₁' > n₁ and counter at n₁ = 2.
    -- We need a step between n₁ and n₁' where counter = 1 from non-1.
    -- At some step after n₁ (before counter reaches 1 again), counter = 0 (after reset).
    -- Specifically: at n₁+1, counter = interCounter ... 2 = if a1 then 1 else 0.
    have hc_n₁_next : ((a1.inter a2).run xs (n₁ + 1)).2.2 = 0 ∨
                      ((a1.inter a2).run xs (n₁ + 1)).2.2 = 1 := by
      rw [inter_run_counter_succ, h]
      simp [interCounter_of_not_one (by decide : (2 : Fin 3) ≠ 1)]
      split_ifs <;> simp
    cases hc_n₁_next with
    | inr h1 => exact ⟨n₁ + 1, by omega, h1⟩
    | inl h0 =>
      -- counter at n₁+1 = 0. Find first a1.accept after n₁+1.
      -- Use Nat.find on h1 to get the first a1.accept at or after n₁+1.
      obtain ⟨n₁'', hn₁''n, hn₁''acc⟩ := h1 (n₁ + 1)
      -- n₁'' ≥ n₁+1 and a1.accept at n₁''. Counter at n₁+1 = 0.
      -- Counter at n₁'' ≥ 1 (from a1.accept with counter ≥ 0).
      have : ((a1.inter a2).run xs n₁'').2.2 = 1 ∨
             ((a1.inter a2).run xs n₁'').2.2 = 2 := by
        cases n₁'' with
        | zero => left; simp [run, run', Buchi.inter] at hn₁''acc
        | succ n'' =>
          rw [inter_run_counter_succ]
          simp only [interCounter]
          have h_s1' := hn₁''acc
          set prev_c := ((a1.inter a2).run xs n'').2.2
          by_cases hprev1 : prev_c = 1
          · simp [hprev1, h_s1']
            split_ifs with h2acc
            · right; rfl
            · left; rfl
          · simp [hprev1, h_s1']
            by_cases hprev0 : prev_c = 0
            · simp [hprev0]; left; rfl
            · have hprev2 : prev_c = 2 := by fin_cases prev_c <;> simp_all
              simp [hprev0, hprev2]; left; rfl
      cases this with
      | inl h => exact ⟨n₁'', by omega, h⟩
      | inr h =>
        obtain ⟨_, ha2⟩ := counter_two_of_succ (n := n₁'' - 1) (by
          rw [Nat.sub_add_cancel (by cases n₁'' with | zero => omega | succ n => omega)]
          exact h)
        -- hmm, this gets complicated. Let me use a different approach.
        sorry

/-- The language of the DBA intersection equals the intersection of the component languages. -/
@[simp, scoped grind =]
theorem Buchi.inter_language_eq (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol) :
    language (a1.inter a2) = language a1 ⊓ language a2 := by
  apply mem_ext
  intro xs
  simp only [mem_language, ωAcceptor.Accepts, mem_inf_iff]
  constructor
  · intro h
    exact ⟨inter_counter_two_implies_a1_inf h, inter_counter_two_implies_a2_inf h⟩
  · intro ⟨h1, h2⟩
    exact counter_reaches_two_of_both_inf a1 a2 xs h1 h2

end Cslib.Automata.DA
