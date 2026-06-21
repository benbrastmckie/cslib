/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.DA.Buchi
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

namespace Cslib.Automata.DA

open Set Filter Cslib.ωSequence ωLanguage ωAcceptor
open scoped Cslib.FLTS Automata.DA.Buchi Automata.DA.FinAcc

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
  rw [Cslib.ωLanguage.mem_sup, mem_language, mem_language, mem_language]
  simp only [ωAcceptor.Accepts, Buchi.union]
  rw [← frequently_or_distrib]
  constructor
  · intro h
    apply Frequently.mono h
    intro k hk
    simp only [mem_union, mem_setOf_eq, prod_run_eq] at hk
    exact hk
  · intro h
    apply Frequently.mono h
    intro k hk
    simp only [mem_union, mem_setOf_eq, prod_run_eq]
    exact hk

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

/-- Membership in the language of `DA.Buchi.infOftenOne`: accepts iff infinitely many 1s. -/
@[simp, scoped grind =]
theorem Buchi.mem_infOftenOne_language (xs : ωSequence (Fin 2)) :
    xs ∈ language Buchi.infOftenOne ↔ ∃ᶠ k in atTop, xs k = 1 := by
  simp only [mem_language, ωAcceptor.Accepts]
  constructor
  · intro h
    rw [frequently_atTop] at h ⊢
    intro n
    obtain ⟨m, hm, hval⟩ := h (n + 1)
    simp only [Buchi.infOftenOne, mem_singleton_iff] at hval
    cases m with
    | zero => simp [run, run'] at hval
    | succ m' =>
      change xs m' = 1 at hval
      exact ⟨m', by omega, hval⟩
  · intro h
    rw [frequently_atTop] at h ⊢
    intro n
    obtain ⟨m, hm, hval⟩ := h n
    exact ⟨m + 1, by omega, by rw [infOftenOne_run_succ]; simp [Buchi.infOftenOne, hval]⟩

/-- The language of `DA.Buchi.infOftenOne` is exactly the set of ω-words containing
infinitely many 1s. -/
@[simp, scoped grind =]
theorem Buchi.infOftenOne_language_eq :
    language Buchi.infOftenOne =
    { xs : ωSequence (Fin 2) | ∃ᶠ k in atTop, xs k = 1 } := by
  apply mem_ext
  intro xs
  rw [Buchi.mem_infOftenOne_language]
  rfl

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
  -- (language infOftenOne)ᶜ = eventuallyZero
  have h_compl : (language Buchi.infOftenOne)ᶜ =
      Cslib.ωLanguage.Example.eventuallyZero := by
    apply mem_ext
    intro xs
    rw [Cslib.ωLanguage.mem_compl, mem_infOftenOne_language,
      Cslib.ωLanguage.mem_def]
    simp only [Cslib.ωLanguage.Example.eventuallyZero, Set.mem_setOf_eq]
    rw [not_frequently]
    constructor
    · intro h
      exact h.mono (fun k hk => by simp_all; omega)
    · intro h
      exact h.mono (fun k hk => by omega)
  -- eventuallyZero = language da = finAcc l↗ω for some l
  rw [← h_compl, ← hda]
  open Acceptor ωAcceptor ωLanguage in
  rw [buchi_eq_finAcc_omegaLim]
  exact ⟨_, rfl⟩

/-! ## DBA Intersection -/

/-- The counter transition for DBA intersection tracks progress through both accepting conditions.
The counter `c : Fin 3` represents:
- `0`: waiting to see a state from `acc1`;
- `1`: `acc1` was visited, now waiting for `acc2`;
- `2`: both `acc1` and `acc2` have been visited since last reset (accepting value).

Transitions computed using NEW states `s1'`, `s2'` after reading a symbol:
- `c = 0`: if `s1' ∈ acc1` advance to `1`, else stay at `0`;
- `c = 1`: if `s2' ∈ acc2` advance to `2`, else stay at `1`;
- `c = 2`: reset — if `s1' ∈ acc1` go to `1`, else go to `0`. -/
noncomputable def interCounter (acc1 : Set State1) (acc2 : Set State2)
    (s1' : State1) (s2' : State2) (c : Fin 3) : Fin 3 :=
  open Classical in
  if c = 0 then (if s1' ∈ acc1 then 1 else 0)
  else if c = 1 then (if s2' ∈ acc2 then 2 else 1)
  else (if s1' ∈ acc1 then 1 else 0)

/-- The DBA intersection of two deterministic Büchi automata via a 3-state counter.

The state space is `State1 × State2 × Fin 3`. The counter in the third component tracks
which accepting conditions have been visited:
- `0` → waiting for `a1.accept`;
- `1` → `a1.accept` seen, waiting for `a2.accept`;
- `2` → both seen (accepting states of the intersection automaton). -/
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
  | succ n ih => simp [run, run', Buchi.inter]; congr 1

/-- The second.first component of the intersection run equals the `a2` run. -/
@[simp]
lemma inter_run_snd_fst (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol)
    (xs : ωSequence Symbol) (n : ℕ) :
    ((a1.inter a2).run xs n).2.1 = a2.run xs n := by
  induction n with
  | zero => simp [run, run', Buchi.inter]
  | succ n ih => simp [run, run', Buchi.inter]; congr 1

/-- The counter at step `n+1` is computed from the new states and old counter. -/
@[simp]
lemma inter_run_counter_succ (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol)
    (xs : ωSequence Symbol) (n : ℕ) :
    ((a1.inter a2).run xs (n + 1)).2.2 =
    interCounter a1.accept a2.accept (a1.run xs (n + 1)) (a2.run xs (n + 1))
      ((a1.inter a2).run xs n).2.2 := by
  change interCounter a1.accept a2.accept
    (a1.tr ((a1.inter a2).run xs n).1 (xs n))
    (a2.tr ((a1.inter a2).run xs n).2.1 (xs n))
    ((a1.inter a2).run xs n).2.2 = _
  simp only [inter_run_fst, inter_run_snd_fst, run_succ]

/-- The initial counter is `0`. -/
@[simp]
lemma inter_run_counter_zero (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol)
    (xs : ωSequence Symbol) :
    ((a1.inter a2).run xs 0).2.2 = 0 := by
  simp [run, run', Buchi.inter]

open Classical in
/-- `interCounter` from non-1 state: result depends only on whether `s1' ∈ acc1`. -/
private lemma interCounter_ne_one {acc1 : Set State1} {acc2 : Set State2}
    {s1' : State1} {s2' : State2} {c : Fin 3} (hc : c ≠ 1) :
    interCounter acc1 acc2 s1' s2' c = if s1' ∈ acc1 then 1 else 0 := by
  simp only [interCounter]; split_ifs <;> simp_all

open Classical in
/-- `interCounter` from state 1: result depends only on whether `s2' ∈ acc2`. -/
private lemma interCounter_eq_one {acc1 : Set State1} {acc2 : Set State2}
    {s1' : State1} {s2' : State2} :
    interCounter acc1 acc2 s1' s2' 1 = if s2' ∈ acc2 then 2 else 1 := by
  simp [interCounter]

/-- If counter becomes 2 at step n+1, then counter was 1 at step n and a2.accept visited. -/
private lemma counter_two_of_succ {a1 : Buchi State1 Symbol} {a2 : Buchi State2 Symbol}
    {xs : ωSequence Symbol} {n : ℕ}
    (h : ((a1.inter a2).run xs (n + 1)).2.2 = 2) :
    ((a1.inter a2).run xs n).2.2 = 1 ∧ a2.run xs (n + 1) ∈ a2.accept := by
  rw [inter_run_counter_succ] at h
  set c := ((a1.inter a2).run xs n).2.2 with hc_def
  by_cases hc1 : c = 1
  · rw [hc1, interCounter_eq_one] at h
    split_ifs at h with h2
    · exact ⟨hc1, h2⟩
    · exact absurd h (by decide)
  · rw [interCounter_ne_one hc1] at h
    split_ifs at h <;> exact absurd h (by decide)

/-- Counter transitions from a non-1 state to 1 iff a1.accept was visited. -/
private lemma counter_one_via_ne_one {a1 : Buchi State1 Symbol} {a2 : Buchi State2 Symbol}
    {xs : ωSequence Symbol} {n : ℕ}
    (hprev : ((a1.inter a2).run xs n).2.2 ≠ 1)
    (hnext : ((a1.inter a2).run xs (n + 1)).2.2 = 1) :
    a1.run xs (n + 1) ∈ a1.accept := by
  rw [inter_run_counter_succ, interCounter_ne_one hprev] at hnext
  split_ifs at hnext with h1
  · exact h1
  · exact absurd hnext (by decide)

/-- Counter stays at 1 when a2.accept is not visited. -/
private lemma counter_stays_one {a1 : Buchi State1 Symbol} {a2 : Buchi State2 Symbol}
    {xs : ωSequence Symbol} {n : ℕ}
    (h1 : ((a1.inter a2).run xs n).2.2 = 1)
    (h2 : a2.run xs (n + 1) ∉ a2.accept) :
    ((a1.inter a2).run xs (n + 1)).2.2 = 1 := by
  rw [inter_run_counter_succ, h1, interCounter_eq_one]; split_ifs; simp_all

/-- If counter = 2 at step k, then there exists j < k with counter[j] ≠ 1 and counter[j+1] = 1
and a1.accept visited at j+1. -/
private lemma counter_two_implies_fresh_one {a1 : Buchi State1 Symbol} {a2 : Buchi State2 Symbol}
    {xs : ωSequence Symbol} (k : ℕ)
    (hk : ((a1.inter a2).run xs k).2.2 = 2) :
    ∃ j, j < k ∧ ((a1.inter a2).run xs j).2.2 ≠ 1 ∧
         ((a1.inter a2).run xs (j + 1)).2.2 = 1 ∧
         a1.run xs (j + 1) ∈ a1.accept ∧
         ∀ m, j < m → m < k → ((a1.inter a2).run xs m).2.2 = 1 := by
  cases k with
  | zero => simp [Buchi.inter] at hk
  | succ k' =>
    obtain ⟨hprev_one, _⟩ := counter_two_of_succ hk
    classical
    set j := Nat.findGreatest (fun j => ((a1.inter a2).run xs j).2.2 ≠ 1) k' with hj_def
    have hj_le : j ≤ k' := Nat.findGreatest_le k'
    have h0_ne_one : ((a1.inter a2).run xs 0).2.2 ≠ 1 := by
      simp [Buchi.inter, run_zero]
    have hj_ne_one : ((a1.inter a2).run xs j).2.2 ≠ 1 := by
      by_cases hj0 : j = 0
      · rw [hj0]; exact h0_ne_one
      · exact Nat.findGreatest_spec
          (P := fun j => ((a1.inter a2).run xs j).2.2 ≠ 1) (Nat.zero_le k') h0_ne_one
    have hafter : ∀ m, j < m → m ≤ k' → ((a1.inter a2).run xs m).2.2 = 1 := by
      intro m hjm hmk'
      by_contra hm_ne1
      have := Nat.le_findGreatest (P := fun j => ((a1.inter a2).run xs j).2.2 ≠ 1)
        hmk' hm_ne1
      omega
    have hjk' : j < k' := by
      by_contra h
      push Not at h
      have : j = k' := Nat.le_antisymm hj_le h
      rw [this] at hj_ne_one
      exact hj_ne_one hprev_one
    have hjnext : ((a1.inter a2).run xs (j + 1)).2.2 = 1 :=
      hafter (j + 1) (by omega) hjk'
    have ha1 := counter_one_via_ne_one hj_ne_one hjnext
    exact ⟨j, by omega, hj_ne_one, hjnext, ha1, fun m hjm hmk => hafter m hjm (by omega)⟩

/-- If the counter reaches `2` infinitely often, then `a2.accept` is visited infinitely often. -/
private lemma inter_counter_two_implies_a2_inf
    {a1 : Buchi State1 Symbol} {a2 : Buchi State2 Symbol}
    {xs : ωSequence Symbol}
    (h : ∃ᶠ k in atTop, ((a1.inter a2).run xs k).2.2 = 2) :
    ∃ᶠ k in atTop, a2.run xs k ∈ a2.accept := by
  rw [frequently_atTop] at h ⊢
  intro n
  obtain ⟨m, hm, hm_val⟩ := h (n + 1)
  cases m with
  | zero => omega
  | succ m' =>
    obtain ⟨_, hm'_a2⟩ := counter_two_of_succ hm_val
    exact ⟨m' + 1, by omega, hm'_a2⟩

/-- If the counter reaches `2` infinitely often, then `a1.accept` is visited infinitely often.

Each occurrence of counter=2 at step `k` produces a "fresh" step `j < k` where the counter
transitions from ≠1 to 1, requiring an `a1.accept` visit at `j+1`. For two distinct counter=2
occurrences at `k₁ < k₂`, the respective fresh steps satisfy `j₂ ≥ k₁` (since `counter(k₁) = 2 ≠ 1`
is the last non-1 step before `k₂`). Hence the sequence of fresh steps is unbounded, giving
infinitely many `a1.accept` visits. -/
private lemma inter_counter_two_implies_a1_inf
    {a1 : Buchi State1 Symbol} {a2 : Buchi State2 Symbol}
    {xs : ωSequence Symbol}
    (h : ∃ᶠ k in atTop, ((a1.inter a2).run xs k).2.2 = 2) :
    ∃ᶠ k in atTop, a1.run xs k ∈ a1.accept := by
  rw [frequently_atTop] at h ⊢
  intro N
  obtain ⟨k₁, hk₁, hk₁_val⟩ := h (N + 2)
  obtain ⟨k₂, hk₂, hk₂_val⟩ := h (k₁ + 1)
  obtain ⟨j₂, hj₂k₂, hj₂_ne1, -, hj₂_a1, hj₂_max⟩ := counter_two_implies_fresh_one k₂ hk₂_val
  have hj₂_ge_k₁ : j₂ ≥ k₁ := by
    by_contra h
    push Not at h
    have hk₁_one := hj₂_max k₁ (by omega) (by omega)
    rw [hk₁_val] at hk₁_one
    exact absurd hk₁_one (by decide)
  exact ⟨j₂ + 1, by omega, hj₂_a1⟩

/-- If both component accepting conditions are visited infinitely often, then the counter
reaches `2` infinitely often. -/
private lemma counter_reaches_two_of_both_inf
    (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol)
    (xs : ωSequence Symbol)
    (h1 : ∃ᶠ k in atTop, a1.run xs k ∈ a1.accept)
    (h2 : ∃ᶠ k in atTop, a2.run xs k ∈ a2.accept) :
    ∃ᶠ k in atTop, ((a1.inter a2).run xs k).2.2 = 2 := by
  rw [frequently_atTop]
  intro N
  rw [frequently_atTop] at h1 h2
  -- The counter is not eventually always 1: if it were, a2.accept visits would give counter=2.
  have h_inf_ne_one : ∃ᶠ k in atTop, ((a1.inter a2).run xs k).2.2 ≠ 1 := by
    by_contra h_ev_one
    rw [not_frequently, eventually_atTop] at h_ev_one
    obtain ⟨N₀, hN₀⟩ := h_ev_one
    obtain ⟨m, hm, hm_a2⟩ := h2 (N₀ + 1)
    cases m with
    | zero => omega
    | succ m' =>
      have hm_prev_one : ((a1.inter a2).run xs m').2.2 = 1 :=
        not_not.mp (hN₀ m' (by omega))
      have hm_two : ((a1.inter a2).run xs (m' + 1)).2.2 = 2 := by
        rw [inter_run_counter_succ, hm_prev_one, interCounter_eq_one]
        exact if_pos hm_a2
      exact absurd (hN₀ (m' + 1) (by omega)) (hm_two ▸ by decide)
  rw [frequently_atTop] at h_inf_ne_one
  obtain ⟨n₀, hn₀, hn₀_ne1⟩ := h_inf_ne_one (N + 1)
  obtain ⟨n₁, hn₁, hn₁_a1⟩ := h1 (n₀ + 1)
  -- Counter at n₁ ∈ {1, 2} (since a1.accept visited)
  cases n₁ with
  | zero => omega
  | succ n₁' =>
    have hc_n₁ : ((a1.inter a2).run xs (n₁' + 1)).2.2 = 1 ∨
                 ((a1.inter a2).run xs (n₁' + 1)).2.2 = 2 := by
      rw [inter_run_counter_succ]
      set prev_c := ((a1.inter a2).run xs n₁').2.2
      by_cases hprev1 : prev_c = 1
      · rw [hprev1, interCounter_eq_one]
        split_ifs with h2acc
        · right; rfl
        · left; rfl
      · rw [interCounter_ne_one hprev1, if_pos hn₁_a1]; left; rfl
    cases hc_n₁ with
    | inr h2 => exact ⟨n₁' + 1, by omega, h2⟩
    | inl h1' =>
      obtain ⟨n₂_cand, hn₂_ge, hn₂_a2⟩ := h2 (n₁' + 2)
      classical
      let hex : ∃ m, m ≥ n₁' + 2 ∧ a2.run xs m ∈ a2.accept :=
        ⟨n₂_cand, hn₂_ge, hn₂_a2⟩
      let n₂ := Nat.find hex
      have hn₂_spec : n₂ ≥ n₁' + 2 ∧ a2.run xs n₂ ∈ a2.accept :=
        Nat.find_spec hex
      have hn₂_min :
          ∀ m, m < n₂ → ¬(m ≥ n₁' + 2 ∧ a2.run xs m ∈ a2.accept) :=
        fun m hm => Nat.find_min hex hm
      have counter_stays : ∀ j, n₁' + 1 ≤ j → j ≤ n₂ - 1 →
          ((a1.inter a2).run xs j).2.2 = 1 := by
        intro j hj₁ hj₂
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj₁
        induction d with
        | zero => simpa using h1'
        | succ d ih =>
          exact counter_stays_one (ih (by omega) (by omega))
            (fun h_a2 =>
              absurd ⟨(by omega : n₁' + 1 + d + 1 ≥ n₁' + 2), h_a2⟩
                (hn₂_min (n₁' + 1 + d + 1) (by omega)))
      have h_prev : ((a1.inter a2).run xs (n₂ - 1)).2.2 = 1 :=
        counter_stays (n₂ - 1) (by omega) (by omega)
      have hn₂_two : ((a1.inter a2).run xs n₂).2.2 = 2 := by
        conv_lhs => rw [show n₂ = n₂ - 1 + 1 from by omega]
        rw [inter_run_counter_succ, h_prev, interCounter_eq_one,
          show n₂ - 1 + 1 = n₂ from by omega]
        exact if_pos hn₂_spec.2
      exact ⟨n₂, by omega, hn₂_two⟩

/-- The language of the DBA intersection equals the intersection of the component languages. -/
@[simp, scoped grind =]
theorem Buchi.inter_language_eq (a1 : Buchi State1 Symbol) (a2 : Buchi State2 Symbol) :
    language (a1.inter a2) = language a1 ⊓ language a2 := by
  apply mem_ext
  intro xs
  simp only [mem_language, ωAcceptor.Accepts]
  constructor
  · intro h
    exact ⟨inter_counter_two_implies_a1_inf h, inter_counter_two_implies_a2_inf h⟩
  · intro ⟨h1, h2⟩
    exact counter_reaches_two_of_both_inf a1 a2 xs h1 h2

end Cslib.Automata.DA
