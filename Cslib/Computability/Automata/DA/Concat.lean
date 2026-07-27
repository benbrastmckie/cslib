/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Foundations.Data.OmegaSequence.InfOcc
public import Cslib.Foundations.Data.OmegaSequence.Init
public import Cslib.Computability.Languages.OmegaLanguage
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Defs

/-! # Concatenation of deterministic automata (Choueka flag construction)

This file defines the flag-construction deterministic concat automaton for Muller-accept
ω-languages following Choueka's approach. The key construction produces a DMA recognizing
the product `L₁ · L₂` of a regular language `L₁` and a Muller language `L₂`.

## Main definitions

* `DA.concat` — the flag-construction concat automaton
* `mullerAccConcat` — the Muller acceptance family for the concat automaton

## References

* Ching-Tsun Chou, `ctchou/AutomataTheory`, `AutomataTheory/Automata/DetConcat.lean`
  (Apache-2.0, 2024). Ported to CSLib by Benjamin Brast-McKie, 2026.
-/

@[expose] public section

namespace Cslib.Automata.DA

open Set Filter Cslib.ωSequence ωLanguage ωAcceptor Acceptor
open scoped Cslib.FLTS Automata.DA.Buchi Automata.DA.FinAcc

variable {State1 State2 Symbol : Type*}

/-! ## Private helper lemmas -/

/-- Pigeonhole for optional slot functions: if more than `Nat.card X` slots of
`f : Fin n → Option X` are `some`-valued, two distinct slots hold the same value. -/
private lemma option_some_pigeonhole {X : Type*} [Finite X] {n : ℕ}
    (f : Fin n → Option X)
    (h : {j | (f j).isSome}.ncard > Nat.card X) :
    ∃ j1 j2, j1 ≠ j2 ∧ ∃ x, f j1 = some x ∧ f j2 = some x := by
  haveI : Fintype X := Fintype.ofFinite X
  haveI : DecidableEq X := Classical.decEq X
  let S : Finset (Fin n) := Finset.univ.filter (fun j => (f j).isSome)
  have hScard : Fintype.card X < S.card := by
    rw [Nat.card_eq_fintype_card] at h
    have hset : {j : Fin n | (f j).isSome} = ↑S := by ext j; simp [S]
    rw [hset, Set.ncard_coe_finset] at h
    exact h
  haveI hne : Nonempty X := by
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j, hj⟩ := hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hj
    exact ⟨x⟩
  let g : Fin n → X := fun j => (f j).getD (Classical.arbitrary X)
  obtain ⟨j1, hj1, j2, hj2, hne, hgeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hScard (f := g) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
  obtain ⟨x1, hx1⟩ := Option.isSome_iff_exists.mp hj1
  obtain ⟨x2, hx2⟩ := Option.isSome_iff_exists.mp hj2
  simp only [g, hx1, hx2, Option.getD_some] at hgeq
  exact ⟨j1, j2, hne, x1, hx1, by rw [hx2, hgeq]⟩

/-- An antitone sequence in a finite linearly ordered type eventually becomes constant. -/
private lemma antitone_fin_eventually {n : ℕ} {f : ℕ → Fin n} (h : Antitone f) :
    ∃ i : Fin n, ∃ m, ∀ k ≥ m, f k = i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (f 0).elim0
  by_contra hall
  push Not at hall
  -- hall : ∀ (i : Fin n) (m : ℕ), ∃ k ≥ m, f k ≠ i
  -- Build a strictly decreasing subsequence to derive a contradiction
  have hstrict : ∀ m : ℕ, ∃ k > m, f k < f m := by
    intro m
    obtain ⟨k, hkm, hne⟩ := hall (f m) m
    exact ⟨k, lt_of_le_of_ne hkm (fun heq => hne (heq ▸ rfl)), lt_of_le_of_ne (h hkm) hne⟩
  -- φ : ℕ → ℕ such that f ∘ φ is strictly decreasing
  let φ : ℕ → ℕ := Nat.rec 0 (fun k φk => (hstrict φk).choose)
  have hφsucc : ∀ k, φ (k + 1) = (hstrict (φ k)).choose := fun _ => rfl
  have hφ_strict : ∀ k, f (φ (k + 1)) < f (φ k) :=
    fun k => hφsucc k ▸ (hstrict (φ k)).choose_spec.2
  -- After n strict decreases from a value < n, we exceed bounds
  have hvals : ∀ k, (f (φ k)).val + k ≤ (f (φ 0)).val := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hlt : (f (φ (k + 1))).val < (f (φ k)).val := hφ_strict k
      omega
  exact absurd (hvals n) (by have := (f (φ 0)).isLt; omega)

/-! ## Pre-dedup intermediate array -/

/-- The pre-deduplication intermediate flag array used inside the concat transition.
Step 1 advances all active copies; step 2 adds a fresh copy — immediately advanced by the
current symbol `a` — when M1's *current* (pre-transition) state `s1` is in `acc1`. Checking
`s1` (rather than the post-transition `da1.tr s1 a`) and immediately advancing the fresh copy
are both necessary so that the empty-prefix case (`da1.start ∈ acc1`, i.e. `acc1` entered with
zero symbols consumed) is witnessed: activation triggered by the state *before* step `m` fires
a fresh copy that is live from step `m + 1` onward, exactly tracking `da2`'s run on the symbols
consumed from step `m` on. -/
private noncomputable def concatF2 (_da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (s1 : State1)
    (f : Fin (Nat.card State2 + 2) → Option State2) (a : Symbol) :
    Fin (Nat.card State2 + 2) → Option State2 :=
  open Classical in
  let f1 : Fin (Nat.card State2 + 2) → Option State2 := fun j => (f j).map (da2.tr · a)
  if s1 ∈ acc1 then
    if h : ∃ j0 : Fin (Nat.card State2 + 2), f1 j0 = none then
      Function.update f1 (Classical.choose h) (some (da2.tr da2.start a))
    else f1
  else f1

/-! ## Flag-construction concat automaton -/

/-- The Choueka flag-construction concat automaton. The state is the M1 state paired with
a flag array of `Nat.card State2 + 2` optional M2 copies. On each step:

1. All active copies advance by one M2 transition.
2. If M1's *current* (pre-transition) state is in `acc1`, a fresh copy is started in a free
   slot, immediately advanced by the current symbol (see `concatF2`'s docstring for why the
   check is on the pre-transition state and the fresh copy is pre-advanced).
3. Copies with the same M2 state are deduplicated (lowest index wins). -/
noncomputable def concat (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) :
    DA (State1 × (Fin (Nat.card State2 + 2) → Option State2)) Symbol where
  start := (da1.start, fun _ => none)
  tr := open Classical in fun ⟨s1, f⟩ a =>
    let s1' := da1.tr s1 a
    -- Step 1: Advance all active copies
    let f1 : Fin (Nat.card State2 + 2) → Option State2 :=
      fun j => (f j).map (da2.tr · a)
    -- Step 2: If M1's pre-transition state is in acc1, activate a fresh copy (already
    -- advanced by the current symbol) in the first free slot
    let f2 : Fin (Nat.card State2 + 2) → Option State2 :=
      if s1 ∈ acc1 then
        if h : ∃ j : Fin (Nat.card State2 + 2), f1 j = none then
          Function.update f1 (Classical.choose h) (some (da2.tr da2.start a))
        else f1
      else f1
    -- Step 3: Dedup — zero out any slot whose value also appears at a lower index
    (s1', fun j =>
      if ∃ j' : Fin (Nat.card State2 + 2), j' < j ∧ f2 j' = f2 j ∧ (f2 j).isSome then
        none
      else f2 j)

/-- The Muller acceptance family for the concat automaton. A set `acc` of concat states
is in this family if there exists slot `i` persistently active across `acc` whose M2 states
across `acc` form a set in `accSet2`. -/
@[nolint unusedArguments]
noncomputable def mullerAccConcat (_ : DA State1 Symbol) (_ : Set State1)
    (_ : DA State2 Symbol) (accSet2 : Set (Set State2)) :
    Set (Set (State1 × (Fin (Nat.card State2 + 2) → Option State2))) :=
  {acc | ∃ i : Fin (Nat.card State2 + 2),
    {s2 | ∃ s ∈ acc, s.2 i = some s2} ∈ accSet2 ∧
    ∀ s ∈ acc, (s.2 i).isSome}

/-! ## Run decomposition lemmas -/

/-- The first component of the concat run equals the M1 run. -/
lemma concat_run_fst (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ) :
    ((concat da1 acc1 da2).run xs n).1 = da1.run xs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ]
    change da1.tr ((concat da1 acc1 da2).run xs n).1 (xs n) = da1.run xs (n + 1)
    rw [ih, ← run_succ]

/-- The second component of the concat transition unfolded at each slot `j`. -/
lemma concat_tr_snd (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (s1 : State1)
    (f : Fin (Nat.card State2 + 2) → Option State2) (a : Symbol)
    (j : Fin (Nat.card State2 + 2)) :
    ((concat da1 acc1 da2).tr (s1, f) a).2 j =
      open Classical in
      let f1 : Fin (Nat.card State2 + 2) → Option State2 :=
        fun j => (f j).map (da2.tr · a)
      let f2 : Fin (Nat.card State2 + 2) → Option State2 :=
        if s1 ∈ acc1 then
          if h : ∃ j0 : Fin (Nat.card State2 + 2), f1 j0 = none then
            Function.update f1 (Classical.choose h) (some (da2.tr da2.start a))
          else f1
        else f1
      if ∃ j' : Fin (Nat.card State2 + 2), j' < j ∧ f2 j' = f2 j ∧ (f2 j).isSome then
        none
      else f2 j := rfl

/-- The second component of the concat transition in terms of `concatF2`: slot `j` is
zeroed when an earlier slot shares the same pre-dedup value; otherwise it keeps `concatF2 j`. -/
private lemma concat_tr_snd' (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (s1 : State1)
    (f : Fin (Nat.card State2 + 2) → Option State2) (a : Symbol)
    (j : Fin (Nat.card State2 + 2)) :
    ((concat da1 acc1 da2).tr (s1, f) a).2 j =
    open Classical in
    if ∃ j' : Fin (Nat.card State2 + 2), j' < j ∧
        concatF2 da1 acc1 da2 s1 f a j' = concatF2 da1 acc1 da2 s1 f a j ∧
        (concatF2 da1 acc1 da2 s1 f a j).isSome then
      none
    else concatF2 da1 acc1 da2 s1 f a j := rfl

/-! ## Stabilization and free-slot lemmas -/

/-- The second component of the concat run at step `n+1` is the second component
of the `concat.tr` applied to the state at step `n`. -/
lemma concat_run_stabilizes (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ) :
    ((concat da1 acc1 da2).run xs (n + 1)).2 =
      ((concat da1 acc1 da2).tr ((concat da1 acc1 da2).run xs n) (xs n)).2 := by
  rw [run_succ]

/-- The deduplication in `concat.tr` ensures no two active slots share the same M2 state.
If two active slots `j1 < j2` both hold the same `some v`, this is a contradiction. -/
private lemma concat_tr_nodup (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (s1 : State1)
    (f : Fin (Nat.card State2 + 2) → Option State2) (a : Symbol)
    (j1 j2 : Fin (Nat.card State2 + 2)) (hlt : j1 < j2) (v : State2)
    (h1 : ((concat da1 acc1 da2).tr (s1, f) a).2 j1 = some v)
    (h2 : ((concat da1 acc1 da2).tr (s1, f) a).2 j2 = some v) : False := by
  -- Rewrite using the named concatF2 so we can case-split on exactly the dedup condition.
  -- Output = none if dedup condition holds; else output = concatF2 j.
  -- Both outputs = some v → dedup conditions are both false → concatF2 j1 = concatF2 j2 = some v
  -- → j1 witnesses dedup condition at j2 → contradiction.
  rw [concat_tr_snd'] at h1 h2
  by_cases c1 : ∃ j' : Fin (Nat.card State2 + 2), j' < j1 ∧
      concatF2 da1 acc1 da2 s1 f a j' = concatF2 da1 acc1 da2 s1 f a j1 ∧
      (concatF2 da1 acc1 da2 s1 f a j1).isSome
  · rw [if_pos c1] at h1; simp at h1
  · rw [if_neg c1] at h1
    by_cases c2 : ∃ j' : Fin (Nat.card State2 + 2), j' < j2 ∧
        concatF2 da1 acc1 da2 s1 f a j' = concatF2 da1 acc1 da2 s1 f a j2 ∧
        (concatF2 da1 acc1 da2 s1 f a j2).isSome
    · rw [if_pos c2] at h2; simp at h2
    · rw [if_neg c2] at h2
      -- h1 : concatF2 ... j1 = some v, h2 : concatF2 ... j2 = some v
      -- j1 < j2, concatF2 j1 = concatF2 j2 = some v → dedup condition at j2 holds → ¬c2
      exact c2 ⟨j1, hlt, h1.trans h2.symm, by simp [h2]⟩

/-- There is always a free slot in the concat flag array: the deduplication ensures
at most `Nat.card State2` distinct active copies at any step. -/
lemma concat_freeSlot [Finite State2] (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ) :
    ∃ j : Fin (Nat.card State2 + 2),
      ((concat da1 acc1 da2).run xs n).2 j = none := by
  induction n with
  | zero => exact ⟨⟨0, by omega⟩, rfl⟩
  | succ n _ =>
    rw [run_succ]
    by_contra hall
    push Not at hall
    -- All Nat.card State2 + 2 slots are active
    have h_isSome : ∀ j : Fin (Nat.card State2 + 2),
        (((concat da1 acc1 da2).tr ((concat da1 acc1 da2).run xs n) (xs n)).2 j).isSome :=
      fun j => Option.isSome_iff_ne_none.mpr (hall j)
    have h_ncard : {j : Fin (Nat.card State2 + 2) |
        (((concat da1 acc1 da2).tr ((concat da1 acc1 da2).run xs n) (xs n)).2 j).isSome}.ncard >
        Nat.card State2 := by
      have heq : {j : Fin (Nat.card State2 + 2) |
          (((concat da1 acc1 da2).tr ((concat da1 acc1 da2).run xs n) (xs n)).2 j).isSome} =
          Set.univ := Set.eq_univ_iff_forall.mpr h_isSome
      rw [heq, Set.ncard_univ, Nat.card_fin]; omega
    -- Two slots have the same some value
    obtain ⟨j1, j2, hne, v, hj1, hj2⟩ := option_some_pigeonhole
        (fun j => ((concat da1 acc1 da2).tr ((concat da1 acc1 da2).run xs n) (xs n)).2 j) h_ncard
    -- But dedup ensures distinct values — contradiction
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact concat_tr_nodup da1 acc1 da2 _ _ _ j1 j2 hlt v hj1 hj2
    · exact concat_tr_nodup da1 acc1 da2 _ _ _ j2 j1 hlt v hj2 hj1

/-! ## Per-slot characterization of `some`-valued outputs -/

/-- If slot `i` is active (holding `v0`) before the transition, its pre-dedup value is exactly
the `da2`-advance of `v0` — unconditionally, since an already-active slot can never be the
slot freshly chosen for activation (that slot's pre-dedup value must start `none`). -/
private lemma concatF2_of_some (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (s1 : State1)
    (f : Fin (Nat.card State2 + 2) → Option State2) (a : Symbol)
    (i : Fin (Nat.card State2 + 2)) (v0 : State2) (hf : f i = some v0) :
    concatF2 da1 acc1 da2 s1 f a i = some (da2.tr v0 a) := by
  unfold concatF2
  split_ifs with h1 h2
  · rw [Function.update_apply]
    split_ifs with heq
    · exfalso
      have hchoose := h2.choose_spec
      simp only [← heq, hf, Option.map_some, reduceCtorEq] at hchoose
    · simp [hf]
  · simp [hf]
  · simp [hf]

/-- If slot `i` was already active (holding `v0`) before the transition and remains `some`
after it (i.e. survives dedup), its new value is exactly the `da2`-advance of `v0`. -/
private lemma concat_tr_snd_of_some (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (s1 : State1)
    (f : Fin (Nat.card State2 + 2) → Option State2) (a : Symbol)
    (i : Fin (Nat.card State2 + 2)) (v0 v : State2)
    (hf : f i = some v0)
    (hout : ((concat da1 acc1 da2).tr (s1, f) a).2 i = some v) :
    v = da2.tr v0 a := by
  rw [concat_tr_snd'] at hout
  by_cases hdedup : ∃ j' : Fin (Nat.card State2 + 2), j' < i ∧
      concatF2 da1 acc1 da2 s1 f a j' = concatF2 da1 acc1 da2 s1 f a i ∧
      (concatF2 da1 acc1 da2 s1 f a i).isSome
  · rw [if_pos hdedup] at hout
    simp at hout
  · rw [if_neg hdedup] at hout
    unfold concatF2 at hout
    split_ifs at hout with h1 h2
    · rw [Function.update_apply] at hout
      split_ifs at hout with heq
      · exfalso
        have hchoose := h2.choose_spec
        simp only [← heq, hf, Option.map_some, reduceCtorEq] at hchoose
      · simp only [hf, Option.map_some] at hout
        exact (Option.some.inj hout).symm
    · simp only [hf, Option.map_some] at hout
      exact (Option.some.inj hout).symm
    · simp only [hf, Option.map_some] at hout
      exact (Option.some.inj hout).symm

/-- If slot `i` was inactive before the transition and becomes `some v` after it, the slot
was freshly activated: `s1 ∈ acc1` and `v` is `da2.start` advanced by the current symbol. -/
private lemma concat_tr_snd_of_none (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (s1 : State1)
    (f : Fin (Nat.card State2 + 2) → Option State2) (a : Symbol)
    (i : Fin (Nat.card State2 + 2)) (v : State2)
    (hf : f i = none)
    (hout : ((concat da1 acc1 da2).tr (s1, f) a).2 i = some v) :
    s1 ∈ acc1 ∧ v = da2.tr da2.start a := by
  rw [concat_tr_snd'] at hout
  by_cases hdedup : ∃ j' : Fin (Nat.card State2 + 2), j' < i ∧
      concatF2 da1 acc1 da2 s1 f a j' = concatF2 da1 acc1 da2 s1 f a i ∧
      (concatF2 da1 acc1 da2 s1 f a i).isSome
  · rw [if_pos hdedup] at hout
    simp at hout
  · rw [if_neg hdedup] at hout
    unfold concatF2 at hout
    split_ifs at hout with h1 h2
    · rw [Function.update_apply] at hout
      split_ifs at hout with heq
      · exact ⟨h1, (Option.some.inj hout).symm⟩
      · exfalso
        simp only [hf, Option.map_none] at hout
        exact absurd hout (by simp)
    · exfalso
      simp only [hf, Option.map_none] at hout
      exact absurd hout (by simp)
    · exfalso
      simp only [hf, Option.map_none] at hout
      exact absurd hout (by simp)

/-- If the pre-dedup array `concatF2 …` attains value `some v` somewhere, the post-dedup
transition output also attains `some v` at some index `≤ j0` (the least index with this
pre-dedup value, which survives dedup unconditionally). Used to show a tracked value is never
lost across a transition, even if the specific slot holding it changes; the `≤ j0` bound is
used to show the witness sequence is antitone (`concat_ptr_antitone`). -/
private lemma concat_dedup_exists_of_f2 (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (s1 : State1)
    (f : Fin (Nat.card State2 + 2) → Option State2) (a : Symbol) (v : State2)
    (j0 : Fin (Nat.card State2 + 2)) (hj0 : concatF2 da1 acc1 da2 s1 f a j0 = some v) :
    ∃ j ≤ j0, ((concat da1 acc1 da2).tr (s1, f) a).2 j = some v := by
  classical
  have hSne : {j : Fin (Nat.card State2 + 2) | concatF2 da1 acc1 da2 s1 f a j = some v}.Nonempty :=
    ⟨j0, hj0⟩
  have hSfin : {j : Fin (Nat.card State2 + 2) | concatF2 da1 acc1 da2 s1 f a j = some v}.Finite :=
    Set.toFinite _
  obtain ⟨j, hjMin⟩ := hSfin.exists_minimal hSne
  rw [minimal_iff_isLeast] at hjMin
  obtain ⟨hjS, hjLB⟩ := hjMin
  refine ⟨j, hjLB hj0, ?_⟩
  rw [concat_tr_snd', if_neg]
  · exact hjS
  · rintro ⟨j', hj'lt, hj'eq, -⟩
    have hj'val : concatF2 da1 acc1 da2 s1 f a j' = some v := by rw [hj'eq, hjS]
    exact absurd (hjLB hj'val) (not_le.mpr hj'lt)

/-! ## Run-level persistence: tracking `da2`'s run from a breakpoint -/

/-- Run-level form of `concat_tr_snd_of_none`: if slot `i` is inactive at time `n` and active
at time `n + 1`, then `da1` entered `acc1` at time `n` and the fresh value is `da2.start`
advanced by the symbol read at time `n`. -/
private lemma concat_run_activate (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ)
    (i : Fin (Nat.card State2 + 2)) (v : State2)
    (hnone : ((concat da1 acc1 da2).run xs n).2 i = none)
    (hsome : ((concat da1 acc1 da2).run xs (n + 1)).2 i = some v) :
    da1.run xs n ∈ acc1 ∧ v = da2.tr da2.start (xs n) := by
  rw [concat_run_stabilizes] at hsome
  have := concat_tr_snd_of_none da1 acc1 da2 ((concat da1 acc1 da2).run xs n).1
    ((concat da1 acc1 da2).run xs n).2 (xs n) i v hnone hsome
  rwa [concat_run_fst] at this

/-- Run-level form of `concat_tr_snd_of_some`: if slot `i` holds `v0` at time `n` and holds
`some v` at time `n + 1`, then `v` is `v0` advanced by the symbol read at time `n`. -/
private lemma concat_run_advance (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ)
    (i : Fin (Nat.card State2 + 2)) (v0 v : State2)
    (hsome0 : ((concat da1 acc1 da2).run xs n).2 i = some v0)
    (hsome1 : ((concat da1 acc1 da2).run xs (n + 1)).2 i = some v) :
    v = da2.tr v0 (xs n) := by
  rw [concat_run_stabilizes] at hsome1
  exact concat_tr_snd_of_some da1 acc1 da2 ((concat da1 acc1 da2).run xs n).1
    ((concat da1 acc1 da2).run xs n).2 (xs n) i v0 v hsome0 hsome1

/-- If `da1` enters `acc1` at time `n`, some slot is activated (holds `da2.start` advanced by
the symbol read at time `n`) at time `n + 1`. Unlike `concat_run_activate`, this does not
require knowing in advance which slot was free — any free slot certifies the activation
branch fires, and `concat_dedup_exists_of_f2` shows the resulting value survives dedup
somewhere. -/
private lemma concat_run_activate_exists [Finite State2] (da1 : DA State1 Symbol)
    (acc1 : Set State1) (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ)
    (hacc : da1.run xs n ∈ acc1) :
    ∃ j, ((concat da1 acc1 da2).run xs (n + 1)).2 j = some (da2.tr da2.start (xs n)) := by
  classical
  have hs1acc : ((concat da1 acc1 da2).run xs n).1 ∈ acc1 := by
    rw [concat_run_fst]; exact hacc
  obtain ⟨j0, hj0⟩ := concat_freeSlot da1 acc1 da2 xs n
  have hex : ∃ j' : Fin (Nat.card State2 + 2),
      (((concat da1 acc1 da2).run xs n).2 j').map (da2.tr · (xs n)) = none :=
    ⟨j0, by rw [hj0, Option.map_none]⟩
  have hval : concatF2 da1 acc1 da2 ((concat da1 acc1 da2).run xs n).1
      ((concat da1 acc1 da2).run xs n).2 (xs n) (Classical.choose hex) =
      some (da2.tr da2.start (xs n)) := by
    unfold concatF2
    rw [if_pos hs1acc, dif_pos hex, Function.update_self]
  obtain ⟨j, -, hj⟩ := concat_dedup_exists_of_f2 da1 acc1 da2
    ((concat da1 acc1 da2).run xs n).1 ((concat da1 acc1 da2).run xs n).2 (xs n)
    (da2.tr da2.start (xs n)) (Classical.choose hex) hval
  exact ⟨j, concat_run_stabilizes .. ▸ hj⟩

/-- For every `k`, some slot holds `da2.run (xs.drop n) (k + 1)` at time `n + 1 + k`, given
`da1` entered `acc1` at time `n`. The witness slot may differ across `k` (dedup can retarget
which slot carries the value); `ConcatPtr` below picks a canonical (least) witness at each `k`
and shows it eventually stabilizes. -/
private lemma concat_ptr_exists [Finite State2] (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ) (hacc : da1.run xs n ∈ acc1) :
    ∀ k, ∃ j : Fin (Nat.card State2 + 2),
      ((concat da1 acc1 da2).run xs (n + 1 + k)).2 j = some (da2.run (xs.drop n) (k + 1)) := by
  intro k
  induction k with
  | zero =>
    obtain ⟨j, hj⟩ := concat_run_activate_exists da1 acc1 da2 xs n hacc
    refine ⟨j, ?_⟩
    have hrun1 : da2.run (xs.drop n) 1 = da2.tr da2.start (xs n) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero, ωSequence.get_drop, Nat.add_zero]
    simpa [hrun1] using hj
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih
    have hj1 : concatF2 da1 acc1 da2 ((concat da1 acc1 da2).run xs (n + 1 + k)).1
        ((concat da1 acc1 da2).run xs (n + 1 + k)).2 (xs (n + 1 + k)) j =
        some (da2.run (xs.drop n) (k + 1 + 1)) := by
      have hj' : ((concat da1 acc1 da2).run xs (n + 1 + k)).2 j =
          some (da2.run (xs.drop n) (k + 1)) := hj
      have hadv := concatF2_of_some da1 acc1 da2 ((concat da1 acc1 da2).run xs (n + 1 + k)).1
        ((concat da1 acc1 da2).run xs (n + 1 + k)).2 (xs (n + 1 + k)) j
        (da2.run (xs.drop n) (k + 1)) hj'
      have hrun : da2.run (xs.drop n) (k + 1 + 1) =
          da2.tr (da2.run (xs.drop n) (k + 1)) (xs (n + 1 + k)) := by
        rw [run_succ]
        congr 1
        rw [ωSequence.get_drop]
        congr 1
        omega
      rw [hadv, hrun]
    obtain ⟨j', -, hj'⟩ := concat_dedup_exists_of_f2 da1 acc1 da2
      ((concat da1 acc1 da2).run xs (n + 1 + k)).1 ((concat da1 acc1 da2).run xs (n + 1 + k)).2
      (xs (n + 1 + k)) (da2.run (xs.drop n) (k + 1 + 1)) j hj1
    refine ⟨j', ?_⟩
    exact (concat_run_stabilizes .. ▸ hj' : _)

/-- At any given run time, at most one slot can hold a given value: this is the dedup
invariant (`concat_tr_nodup`) transported to the `run` level. -/
private lemma concat_run_unique_of_some [Finite State2] (da1 : DA State1 Symbol)
    (acc1 : Set State1) (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (m : ℕ)
    (i1 i2 : Fin (Nat.card State2 + 2)) (v : State2)
    (h1 : ((concat da1 acc1 da2).run xs m).2 i1 = some v)
    (h2 : ((concat da1 acc1 da2).run xs m).2 i2 = some v) : i1 = i2 := by
  cases m with
  | zero => simp [concat] at h1
  | succ m =>
    rw [concat_run_stabilizes] at h1 h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact concat_tr_nodup da1 acc1 da2 _ _ _ i1 i2 hlt v h1 h2
    · exact concat_tr_nodup da1 acc1 da2 _ _ _ i2 i1 hlt v h2 h1

/-- The canonical (least, at each time) witness slot tracking `da2`'s run on `xs.drop n` from
breakpoint `n`, defined by choice from `concat_ptr_exists`. Its identity may shift across `k`
(dedup can retarget which slot survives), but `concat_ptr_antitone` shows the sequence of
indices is non-increasing, hence eventually constant. -/
private noncomputable def ConcatPtr [Finite State2] (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ) (hacc : da1.run xs n ∈ acc1)
    (k : ℕ) : Fin (Nat.card State2 + 2) :=
  Classical.choose (concat_ptr_exists da1 acc1 da2 xs n hacc k)

/-- Defining property of `ConcatPtr`: it tracks the target value at each time. -/
private lemma concat_ptr_spec [Finite State2] (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ) (hacc : da1.run xs n ∈ acc1)
    (k : ℕ) :
    ((concat da1 acc1 da2).run xs (n + 1 + k)).2 (ConcatPtr da1 acc1 da2 xs n hacc k) =
      some (da2.run (xs.drop n) (k + 1)) :=
  Classical.choose_spec (concat_ptr_exists da1 acc1 da2 xs n hacc k)

/-- `ConcatPtr` is antitone: the witness slot's index never increases. The slot at step `k`
survives (via `concatF2_of_some`) as a valid pre-dedup candidate at step `k + 1`, so
`concat_dedup_exists_of_f2` produces a survivor `≤` it; uniqueness of the value-to-slot
correspondence at each time identifies that survivor with `ConcatPtr (k + 1)`. -/
private lemma concat_ptr_antitone [Finite State2] (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ) (hacc : da1.run xs n ∈ acc1) :
    Antitone (ConcatPtr da1 acc1 da2 xs n hacc) := by
  apply antitone_nat_of_succ_le
  intro k
  set jk := ConcatPtr da1 acc1 da2 xs n hacc k with hjk
  have hjkspec := concat_ptr_spec da1 acc1 da2 xs n hacc k
  have hj1 : concatF2 da1 acc1 da2 ((concat da1 acc1 da2).run xs (n + 1 + k)).1
      ((concat da1 acc1 da2).run xs (n + 1 + k)).2 (xs (n + 1 + k)) jk =
      some (da2.run (xs.drop n) (k + 1 + 1)) := by
    have hadv := concatF2_of_some da1 acc1 da2 ((concat da1 acc1 da2).run xs (n + 1 + k)).1
      ((concat da1 acc1 da2).run xs (n + 1 + k)).2 (xs (n + 1 + k)) jk
      (da2.run (xs.drop n) (k + 1)) hjkspec
    have hrun : da2.run (xs.drop n) (k + 1 + 1) =
        da2.tr (da2.run (xs.drop n) (k + 1)) (xs (n + 1 + k)) := by
      rw [run_succ]
      congr 1
      rw [ωSequence.get_drop]
      congr 1
      omega
    rw [hadv, hrun]
  obtain ⟨j', hj'le, hj'⟩ := concat_dedup_exists_of_f2 da1 acc1 da2
    ((concat da1 acc1 da2).run xs (n + 1 + k)).1 ((concat da1 acc1 da2).run xs (n + 1 + k)).2
    (xs (n + 1 + k)) (da2.run (xs.drop n) (k + 1 + 1)) jk hj1
  have hj'run : ((concat da1 acc1 da2).run xs (n + 1 + (k + 1))).2 j' =
      some (da2.run (xs.drop n) (k + 1 + 1)) := concat_run_stabilizes .. ▸ hj'
  have hspec1 := concat_ptr_spec da1 acc1 da2 xs n hacc (k + 1)
  have heq : j' = ConcatPtr da1 acc1 da2 xs n hacc (k + 1) :=
    concat_run_unique_of_some da1 acc1 da2 xs (n + 1 + (k + 1)) j'
      (ConcatPtr da1 acc1 da2 xs n hacc (k + 1)) (da2.run (xs.drop n) (k + 1 + 1))
      hj'run hspec1
  rwa [heq] at hj'le

/-- `ConcatPtr` eventually stabilizes at some value `i`, since it is an antitone sequence
valued in a finite type. -/
private lemma concat_ptr_eventually [Finite State2] (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ) (hacc : da1.run xs n ∈ acc1) :
    ∃ i : Fin (Nat.card State2 + 2), ∃ m,
      ∀ k ≥ m, ConcatPtr da1 acc1 da2 xs n hacc k = i :=
  antitone_fin_eventually (concat_ptr_antitone da1 acc1 da2 xs n hacc)

/-- If slot `i` is activated (holds `da2.start` advanced by one symbol) at time `n + 1` and
never becomes inactive afterward, it exactly tracks `da2`'s run on `xs.drop n`, offset by one
step, from then on: at time `n + 1 + k` it holds `da2.run (xs.drop n) (k + 1)`. -/
private lemma concat_run_tracks (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (n : ℕ)
    (i : Fin (Nat.card State2 + 2))
    (hact : ((concat da1 acc1 da2).run xs (n + 1)).2 i = some (da2.tr da2.start (xs n)))
    (hpersist : ∀ k, ((concat da1 acc1 da2).run xs (n + 1 + k)).2 i ≠ none) :
    ∀ k, ((concat da1 acc1 da2).run xs (n + 1 + k)).2 i =
      some (da2.run (xs.drop n) (k + 1)) := by
  intro k
  induction k with
  | zero =>
    have hrun1 : da2.run (xs.drop n) 1 = da2.tr da2.start (xs n) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ, run_zero, ωSequence.get_drop, Nat.add_zero]
    simpa [hrun1] using hact
  | succ k ih =>
    have hne : ((concat da1 acc1 da2).run xs (n + 1 + (k + 1))).2 i ≠ none :=
      hpersist (k + 1)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Option.isSome_iff_ne_none.mpr hne)
    have hstep : v = da2.tr (da2.run (xs.drop n) (k + 1)) (xs (n + 1 + k)) :=
      concat_run_advance da1 acc1 da2 xs (n + 1 + k) i (da2.run (xs.drop n) (k + 1)) v ih hv
    have hrun : da2.run (xs.drop n) (k + 1 + 1) =
        da2.tr (da2.run (xs.drop n) (k + 1)) (xs (n + 1 + k)) := by
      rw [run_succ]
      congr 1
      rw [ωSequence.get_drop]
      congr 1
      omega
    exact hv.trans (congrArg some (hstep.trans hrun.symm))

/-- If slot `i` is active (`isSome`) at every time `≥ N`, there is a breakpoint `n` at which
`da1` entered `acc1` and slot `i` tracks `da2`'s run on `xs.drop n` (offset by one) forever
after. Found via `Nat.findGreatest` of "slot `i` is inactive", using that slot `i` starts
inactive at time `0`. -/
private lemma concat_persist_from_activity (da1 : DA State1 Symbol) (acc1 : Set State1)
    (da2 : DA State2 Symbol) (xs : ωSequence Symbol) (i : Fin (Nat.card State2 + 2)) (N : ℕ)
    (h : ∀ k ≥ N, (((concat da1 acc1 da2).run xs k).2 i).isSome) :
    ∃ n, da1.run xs n ∈ acc1 ∧
      ∀ k, ((concat da1 acc1 da2).run xs (n + 1 + k)).2 i = some (da2.run (xs.drop n) (k + 1)) := by
  classical
  have hP0 : ((concat da1 acc1 da2).run xs 0).2 i = none := by simp [concat]
  set m := Nat.findGreatest (fun k => ((concat da1 acc1 da2).run xs k).2 i = none) N with hmdef
  have hPm : ((concat da1 acc1 da2).run xs m).2 i = none :=
    Nat.findGreatest_spec (P := fun k => ((concat da1 acc1 da2).run xs k).2 i = none)
      (Nat.zero_le N) hP0
  have hmN : m ≤ N := Nat.findGreatest_le N
  have hmlt : m < N := by
    rcases lt_or_eq_of_le hmN with hlt | heq
    · exact hlt
    · exact absurd (heq ▸ hPm) (Option.isSome_iff_ne_none.mp (h N le_rfl))
  have hact_ne : ((concat da1 acc1 da2).run xs (m + 1)).2 i ≠ none :=
    Nat.findGreatest_is_greatest (P := fun k => ((concat da1 acc1 da2).run xs k).2 i = none)
      (k := m + 1) (n := N) (by omega) (by omega)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Option.isSome_iff_ne_none.mpr hact_ne)
  obtain ⟨hacc, hveq⟩ := concat_run_activate da1 acc1 da2 xs m i v hPm hv
  refine ⟨m, hacc, ?_⟩
  have hpersist : ∀ k, ((concat da1 acc1 da2).run xs (m + 1 + k)).2 i ≠ none := by
    intro k
    by_cases hle : m + 1 + k ≤ N
    · exact Nat.findGreatest_is_greatest
        (P := fun k => ((concat da1 acc1 da2).run xs k).2 i = none)
        (k := m + 1 + k) (n := N) (by omega) hle
    · exact Option.isSome_iff_ne_none.mp (h (m + 1 + k) (by omega))
  exact concat_run_tracks da1 acc1 da2 xs m i (hveq ▸ hv) hpersist

/-! ## Finite instance -/

/-- The state type of the concat automaton is finite whenever both component state types
are finite. This enables Muller acceptance decidability and the `infOcc` finiteness
results used by the direction lemmas. -/
instance [Finite State1] [Finite State2] :
    Finite (State1 × (Fin (Nat.card State2 + 2) → Option State2)) :=
  inferInstance

/-! ## Backward-direction assembly: `infOcc` and eventual membership -/

/-- In a finite-state run, the current state is eventually always one that occurs infinitely
often: all states that occur only finitely many times have a last occurrence, and the state
space being finite makes their maximum last-occurrence time well-defined. -/
private lemma eventually_mem_infOcc {α : Type*} [Finite α] (ys : ωSequence α) :
    ∀ᶠ k in atTop, ys k ∈ ys.infOcc := by
  have hfin : {x : α | ¬ ∃ᶠ k in atTop, ys k = x}.Finite := Set.toFinite _
  have heach : ∀ x ∈ {x : α | ¬ ∃ᶠ k in atTop, ys k = x}, ∀ᶠ k in atTop, ys k ≠ x := by
    intro x hx
    exact Filter.not_frequently.mp hx
  have hall : ∀ᶠ k in atTop, ∀ x ∈ {x : α | ¬ ∃ᶠ k in atTop, ys k = x}, ys k ≠ x :=
    (Set.Finite.eventually_all hfin).mpr heach
  filter_upwards [hall] with k hk
  by_contra hcon
  exact hk (ys k) hcon rfl

/-- The set of values `s2` such that some slot-`i`-tagged concat state recurs infinitely often
equals `infOcc` of `da2`'s run on `xs.drop n`, whenever slot `i` tracks that run (offset by
one) forever after some time `n + 1 + m0`. The bound `m0` lets this serve both the backward
direction (`m0 = 0`, tracking holds from the very start) and the forward direction (`m0` = the
time a possibly-shifting witness slot stabilizes). Both state spaces must be finite for the
pigeonhole argument `frequently_in_finite_type` to apply. -/
private lemma concat_slot_infOcc_eq [Finite State1] [Finite State2]
    (da1 : DA State1 Symbol) (acc1 : Set State1) (da2 : DA State2 Symbol)
    (xs : ωSequence Symbol) (n m0 : ℕ) (i : Fin (Nat.card State2 + 2))
    (hpersist : ∀ k ≥ m0, ((concat da1 acc1 da2).run xs (n + 1 + k)).2 i =
      some (da2.run (xs.drop n) (k + 1))) :
    {s2 | ∃ s ∈ ((concat da1 acc1 da2).run xs).infOcc, s.2 i = some s2} =
      (da2.run (xs.drop n)).infOcc := by
  ext s2
  simp only [Set.mem_ofPred_eq, mem_infOcc]
  constructor
  · rintro ⟨s, hs_inf, hs_i⟩
    apply frequently_atTop.mpr
    intro l
    obtain ⟨k, hk, hkeq⟩ := frequently_atTop.mp hs_inf (n + 1 + max l m0)
    obtain ⟨j, rfl⟩ : ∃ j, k = n + 1 + j := ⟨k - (n + 1), by omega⟩
    refine ⟨j + 1, by omega, ?_⟩
    have := hpersist j (by omega)
    rw [hkeq] at this
    rw [hs_i] at this
    exact (Option.some.inj this).symm
  · intro hfreq
    have hfreq' : ∃ᶠ k in atTop,
        (concat da1 acc1 da2).run xs k ∈
          {s : State1 × (Fin (Nat.card State2 + 2) → Option State2) | s.2 i = some s2} := by
      apply frequently_atTop.mpr
      intro l
      obtain ⟨j, hj, hjeq⟩ := frequently_atTop.mp hfreq (max l (m0 + 1))
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      refine ⟨n + 1 + j', by omega, ?_⟩
      simp only [Set.mem_ofPred_eq]
      rw [hpersist j' (by omega), hjeq]
    rw [ωSequence.frequently_in_finite_type] at hfreq'
    obtain ⟨s, hs_mem, hs_freq⟩ := hfreq'
    exact ⟨s, mem_infOcc.mpr hs_freq, hs_mem⟩

/-! ## Top-level language correctness -/

/-- If a slot tracks `da2`'s run (offset by one) from some time `n + 1 + m0` onward, every
recurring state of the concat run is active at that slot: any state occurring infinitely
often occurs at some time `≥ n + 1 + m0`, where the slot is `isSome` by the tracking formula. -/
private lemma concat_slot_isSome_of_infOcc [Finite State1] [Finite State2]
    (da1 : DA State1 Symbol) (acc1 : Set State1) (da2 : DA State2 Symbol)
    (xs : ωSequence Symbol) (n m0 : ℕ) (i : Fin (Nat.card State2 + 2))
    (hpersist : ∀ k ≥ m0, ((concat da1 acc1 da2).run xs (n + 1 + k)).2 i =
      some (da2.run (xs.drop n) (k + 1)))
    (s : State1 × (Fin (Nat.card State2 + 2) → Option State2))
    (hs : s ∈ ((concat da1 acc1 da2).run xs).infOcc) :
    (s.2 i).isSome := by
  rw [mem_infOcc] at hs
  obtain ⟨t, ht, hteq⟩ := frequently_atTop.mp hs (n + 1 + m0)
  obtain ⟨j, rfl⟩ : ∃ j, t = n + 1 + j := ⟨t - (n + 1), by omega⟩
  rw [← hteq, hpersist j (by omega)]
  exact Option.isSome_some

/-- Top-level language correctness of the Choueka flag-construction concat automaton:
`concat da1 acc1 da2`, accepted under `mullerAccConcat`, recognizes exactly the concatenation
of `da1`'s finite-string language with `da2`'s Muller ω-language. This is the key correctness
theorem enabling the forward (ω-regular ⊆ DMA) direction of McNaughton's theorem via the
Choueka decomposition route (task 241). -/
theorem concat_language_eq [Finite State1] [Finite State2]
    (da1 : DA State1 Symbol) (acc1 : Set State1) (da2 : DA State2 Symbol)
    (accSet2 : Set (Set State2)) :
    language (Muller.mk (concat da1 acc1 da2) (mullerAccConcat da1 acc1 da2 accSet2)) =
      language (FinAcc.mk da1 acc1) * language (Muller.mk da2 accSet2) := by
  apply mem_ext
  intro xs
  rw [Cslib.ωLanguage.mem_hmul]
  simp only [ωAcceptor.mem_language, mullerAccConcat]
  constructor
  · rintro ⟨i, hAccSet, hAllSome⟩
    obtain ⟨N, hN⟩ := (eventually_mem_infOcc ((concat da1 acc1 da2).run xs)).exists_forall_of_atTop
    have hSomeAt : ∀ k ≥ N, (((concat da1 acc1 da2).run xs k).2 i).isSome := by
      intro k hk
      exact hAllSome _ (hN k hk)
    obtain ⟨n, hacc, hpersist⟩ :=
      concat_persist_from_activity da1 acc1 da2 xs i N hSomeAt
    refine ⟨xs.extract 0 n, ?_, xs.drop n, ?_, by simp⟩
    · change da1.mtr da1.start (xs.extract 0 n) ∈ acc1
      rwa [mtr_extract_eq_run]
    · change (da2.run (xs.drop n)).infOcc ∈ accSet2
      rw [← concat_slot_infOcc_eq da1 acc1 da2 xs n 0 i (fun k _ => hpersist k)]
      exact hAccSet
  · rintro ⟨u, hu, ys, hys, rfl⟩
    have hextract : (u ++ω ys).extract 0 u.length = u := by
      rw [extract_append_zero_right (le_refl _)]
      simp
    have hn : da1.run (u ++ω ys) u.length ∈ acc1 := by
      rw [← mtr_extract_eq_run, hextract]
      exact hu
    have hys' : (da2.run ((u ++ω ys).drop u.length)).infOcc ∈ accSet2 := by
      rwa [drop_append_ωSequence]
    obtain ⟨i, m, hi⟩ := concat_ptr_eventually da1 acc1 da2 (u ++ω ys) u.length hn
    have hpersist : ∀ k ≥ m, ((concat da1 acc1 da2).run (u ++ω ys)
        (u.length + 1 + k)).2 i = some (da2.run ((u ++ω ys).drop u.length) (k + 1)) := by
      intro k hk
      rw [← hi k hk]
      exact concat_ptr_spec da1 acc1 da2 (u ++ω ys) u.length hn k
    refine ⟨i, ?_, ?_⟩
    · rwa [concat_slot_infOcc_eq da1 acc1 da2 (u ++ω ys) u.length m i hpersist]
    · exact concat_slot_isSome_of_infOcc da1 acc1 da2 (u ++ω ys) u.length m i hpersist

end Cslib.Automata.DA
