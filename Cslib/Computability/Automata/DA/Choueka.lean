/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.DA.Basic
public import Cslib.Computability.Languages.RegularLanguage
public import Cslib.Computability.Languages.OmegaLanguage
public import Cslib.Foundations.Combinatorics.InfiniteGraphRamsey
public import Cslib.Foundations.Data.OmegaSequence.InfOcc
public import Mathlib.Data.Set.Card

/-! # The Choueka language of a deterministic automaton

This file defines the *Choueka language* of a deterministic automaton `da` with respect to an
accept set `acc`, following section 5 of Choueka's paper (via Ching-Tsun Chou's
`ctchou/AutomataTheory` port). If `da` (with accept set `acc`) recognizes `l∗` for a regular
language `l`, the Choueka language `U` of `(da, acc)` is regular and satisfies the identity
`l^ω = l∗ * U↗ω`. This is the key remaining lemma needed by task 241 (McNaughton's theorem,
Phase 3) to show that the ω-power of a regular language is recognized by a finite-state
deterministic Muller automaton.

## Main definitions

* `DA.chouekaLang` — the Choueka language of a deterministic automaton and accept set.

## Main theorems

* `DA.chouekaLang_regular` — the Choueka language of a finite-state deterministic automaton
  is regular.
* `DA.chouekaLang_omega_power_eq_omega_limit` — the Choueka identity
  `l^ω = l∗ * (chouekaLang da acc)↗ω`.

## References

* Ching-Tsun Chou, `ctchou/AutomataTheory`, `AutomataTheory/Languages/ChouekaLemma.lean`
  (Apache-2.0, 2025). Ported to CSLib by Benjamin Brast-McKie, 2026.
-/

@[expose] public section

namespace Cslib.Automata.DA

open Set Filter Cslib.ωSequence Cslib.ωLanguage Cslib.Language Acceptor
open scoped Cslib.FLTS Automata.DA.FinAcc

-- `State` is restricted to `Type` (not `Type*`) to match `Language.IsRegular.iff_dfa`,
-- the universe at which Mathlib's `Language.IsRegular` DFA characterization is stated.
variable {State : Type} {Symbol : Type*}

/-! ## The Choueka language -/

/-- The Choueka language of a deterministic automaton `da` with an accept set `acc`. Intended
to satisfy: if `language (FinAcc.mk da acc) = l∗` for a regular language `l`, then
`l^ω = l∗ * (chouekaLang da acc)↗ω` (`chouekaLang_omega_power_eq_omega_limit`). A word `al`
belongs to the Choueka language iff it has a breakpoint `m` such that:
1. the run on the prefix `al.take m` (from the automaton's start) lands in `acc`;
2. the run on the suffix `al.drop m` (again from the automaton's start) agrees with the run
   on the whole word `al`;
3. `m` is the *earliest* such breakpoint: no `k` strictly between `m` and `al.length` gives a
   matching "restart" run on the corresponding sub-suffix. -/
def chouekaLang (da : DA State Symbol) (acc : Set State) : Language Symbol :=
  { al | ∃ m, 0 < m ∧ m < al.length ∧
      da.mtr da.start (al.take m) ∈ acc ∧
      da.mtr da.start (al.drop m) = da.mtr da.start al ∧
      ∀ k, m < k → k < al.length →
        da.mtr da.start ((al.drop m).take (k - m)) ≠ da.mtr da.start (al.take k) }

/-! ## Composition of the multistep transition function -/

/-- The multistep transition function composes over list append: running `a ++ b` from `s`
equals running `b` from the state reached by running `a` from `s`. -/
private lemma mtr_append (da : DA State Symbol) (s : State) (a b : List Symbol) :
    da.mtr s (a ++ b) = da.mtr (da.mtr s a) b := by
  simp [FLTS.mtr, List.foldl_append]

/-! ## Regularity helper languages -/

/-- The language of words whose run from the automaton's start lands exactly in state `s`. -/
private def eqState (da : DA State Symbol) (s : State) : Language Symbol :=
  { al | da.mtr da.start al = s }

/-- The language of words whose run from state `s` lands exactly in state `t`. -/
private def eqFromState (da : DA State Symbol) (s t : State) : Language Symbol :=
  { al | da.mtr s al = t }

/-- `eqState da s` is regular: it is recognized by the DFA `(da, {s})`. -/
private lemma eqState_regular [Finite State] (da : DA State Symbol) (s : State) :
    (eqState da s).IsRegular := by
  rw [Language.IsRegular.iff_dfa]
  refine ⟨State, ‹Finite State›, FinAcc.mk da {s}, ?_⟩
  ext al
  simp [Acceptor.language, Acceptor.Accepts, eqState]

/-- `eqFromState da s t` is regular: it is recognized by the DFA `(da, {t})` restarted at `s`. -/
private lemma eqFromState_regular [Finite State] (da : DA State Symbol) (s t : State) :
    (eqFromState da s t).IsRegular := by
  rw [Language.IsRegular.iff_dfa]
  refine ⟨State, ‹Finite State›, FinAcc.mk (DA.mk da.toFLTS s) {t}, ?_⟩
  ext al
  simp [Acceptor.language, Acceptor.Accepts, eqFromState]

/-- The language of nonempty words whose run from the automaton's start lands in state `s`. -/
private def chouekaA (da : DA State Symbol) (s : State) : Language Symbol :=
  { al | al ≠ [] ∧ da.mtr da.start al = s }

/-- The language of nonempty words on which running from the automaton's start agrees with
running from state `s`. Membership records that `s` "behaves like the start state" on `al`. -/
private def chouekaB (da : DA State Symbol) (s : State) : Language Symbol :=
  { al | al ≠ [] ∧ da.mtr da.start al = da.mtr s al }

private lemma chouekaA_regular [Finite State] (da : DA State Symbol) (s : State) :
    (chouekaA da s).IsRegular := by
  have h : chouekaA da s = (1 : Language Symbol)ᶜ ⊓ eqState da s := rfl
  rw [h]
  exact Language.IsRegular.inf (Language.IsRegular.compl Language.IsRegular.one)
    (eqState_regular da s)

private lemma chouekaB_regular [Finite State] (da : DA State Symbol) (s : State) :
    (chouekaB da s).IsRegular := by
  have h : chouekaB da s = (1 : Language Symbol)ᶜ ⊓
      ⨆ t : State, (eqState da t ⊓ eqFromState da s t) := by
    ext al
    rw [Language.mem_inf, Language.mem_iSup]
    change (al ≠ [] ∧ da.mtr da.start al = da.mtr s al) ↔
      al ≠ [] ∧ ∃ t, da.mtr da.start al = t ∧ da.mtr s al = t
    constructor
    · rintro ⟨hne, heq⟩
      exact ⟨hne, da.mtr da.start al, rfl, heq.symm⟩
    · rintro ⟨hne, t, ht1, ht2⟩
      exact ⟨hne, ht1.trans ht2.symm⟩
  rw [h, ← iSup_univ]
  exact Language.IsRegular.inf (Language.IsRegular.compl Language.IsRegular.one)
    (Language.IsRegular.iSup
      (fun t _ => Language.IsRegular.inf (eqState_regular da t) (eqFromState_regular da s t)))

/-! ## Decomposition of the Choueka language -/

/-- The Choueka language decomposes as a finite union, over accepting states `s`, of the
concatenation of the "reach `s`" language with the "restart-agreement, no earlier breakpoint"
language. This algebraic reformulation removes the existential/universal quantifiers over
breakpoints from `chouekaLang`'s definition, expressing it via finitary regular-language
operations (union, concatenation, intersection, complementation) so that regularity follows
from CSLib's closure lemmas for `Language.IsRegular`. -/
private lemma chouekaLang_decomp (da : DA State Symbol) (acc : Set State) :
    chouekaLang da acc =
      ⨆ s ∈ acc, chouekaA da s * (chouekaB da s ⊓ (chouekaB da s * (1 : Language Symbol)ᶜ)ᶜ) := by
  ext al
  simp only [chouekaLang, Language.mem_iSup]
  constructor
  · rintro ⟨m, hm0, hm1, hacc, heq, hno⟩
    have hlen_al1 : (al.take m).length = m := by
      rw [List.length_take]; omega
    have hlen_al2 : (al.drop m).length = al.length - m := by
      rw [List.length_drop]
    refine ⟨da.mtr da.start (al.take m), hacc, al.take m, ⟨?_, rfl⟩, al.drop m,
      ⟨⟨?_, ?_⟩, ?_⟩, List.take_append_drop m al⟩
    · exact List.ne_nil_of_length_pos (by omega)
    · exact List.ne_nil_of_length_pos (by omega)
    · -- al.drop m ∈ chouekaB da (mtr da.start (al.take m)): the "restart-agreement" property
      rw [← mtr_append, List.take_append_drop, heq]
    · -- al.drop m ∉ chouekaB da (mtr da.start (al.take m)) * {[]}ᶜ
      rintro ⟨b1, ⟨hb1_ne, hb1_eq⟩, b2, hb2_ne, hb12⟩
      have hk : m < m + b1.length ∧ m + b1.length < al.length := by
        have hb1_pos : 0 < b1.length := List.length_pos_iff.mpr hb1_ne
        have hb2_pos : 0 < b2.length := List.length_pos_iff.mpr hb2_ne
        have hb12_len : b1.length + b2.length = al.length - m := by
          have := congrArg List.length hb12
          simp only [List.length_append, hlen_al2] at this
          omega
        omega
      have h1 : (al.drop m).take (m + b1.length - m) = b1 := by
        have : m + b1.length - m = b1.length := by omega
        rw [this, ← hb12, List.take_left]
      have h2 : al.take (m + b1.length) = al.take m ++ b1 := by
        rw [List.take_add]
        congr 1
        rw [← hb12, List.take_left]
      have := hno (m + b1.length) hk.1 hk.2
      rw [h1, h2, mtr_append] at this
      exact this hb1_eq
  · rintro ⟨s, hacc, al1, ⟨hal1_ne, hal1_eq⟩, al2, ⟨⟨hal2_ne, hal2_eq⟩, hal2_ns⟩, rfl⟩
    refine ⟨al1.length, List.length_pos_iff.mpr hal1_ne, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append]
      have := List.length_pos_iff.mpr hal2_ne
      omega
    · rw [List.take_left, hal1_eq]
      exact hacc
    · rw [List.drop_left, mtr_append, hal1_eq]
      exact hal2_eq
    · intro k hk1 hk2
      simp only [List.length_append] at hk2
      rw [List.drop_left]
      have hj_pos : 0 < k - al1.length := by omega
      have hj_lt : k - al1.length < al2.length := by omega
      have hk_eq : al1.length + (k - al1.length) = k := by omega
      have hlen_take : (al2.take (k - al1.length)).length = k - al1.length := by
        rw [List.length_take]; omega
      have hlen_drop : (al2.drop (k - al1.length)).length = al2.length - (k - al1.length) := by
        rw [List.length_drop]
      have htake : (al1 ++ al2).take k = al1 ++ al2.take (k - al1.length) := by
        have hta : (al1 ++ al2).take (al1.length + (k - al1.length)) =
            (al1 ++ al2).take al1.length ++ ((al1 ++ al2).drop al1.length).take (k - al1.length) :=
          List.take_add
        rw [hk_eq, List.take_left, List.drop_left] at hta
        exact hta
      rw [htake, mtr_append, hal1_eq]
      intro hcontra
      apply hal2_ns
      exact ⟨al2.take (k - al1.length),
        ⟨List.ne_nil_of_length_pos (by omega), hcontra⟩,
        al2.drop (k - al1.length), List.ne_nil_of_length_pos (by omega),
        List.take_append_drop _ al2⟩

/-! ## Regularity of the Choueka language -/

/-- The Choueka language of a finite-state deterministic automaton is regular. -/
theorem chouekaLang_regular [Inhabited Symbol] [Finite State]
    (da : DA State Symbol) (acc : Set State) :
    (chouekaLang da acc).IsRegular := by
  rw [chouekaLang_decomp]
  apply Language.IsRegular.iSup
  intro s _
  apply Language.IsRegular.mul (chouekaA_regular da s)
  apply Language.IsRegular.inf (chouekaB_regular da s)
  apply Language.IsRegular.compl
  apply Language.IsRegular.mul (chouekaB_regular da s)
  exact Language.IsRegular.compl Language.IsRegular.one

/-! ## The Choueka identity -/

/-- Technical lemma: given a strictly monotone `φ` and an injective `φ'`, there is a
strictly monotone `σ` interleaving the two: `φ (σ n) < φ' (σ (n + 1))` for all `n`. Used to
build the ω-power decomposition points from the Choueka-language breakpoints. -/
private lemma greater_subseq (φ φ' : ℕ → ℕ) (hi : Function.Injective φ') :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n, φ (σ n) < φ' (σ (n + 1)) := by
  have h_step : ∀ n, ∃ m > n, φ n < φ' m := by
    intro n
    have h_inf : {m : ℕ | n < m}.Infinite := by
      apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => n + 1 + k)
      · intro a b h; dsimp only at h; omega
      · intro k; simp only [Set.mem_setOf_eq]; omega
    have h_fin : {m : ℕ | φ' m ≤ φ n}.Finite := by
      have heq : {m : ℕ | φ' m ≤ φ n} = φ' ⁻¹' {x | x ≤ φ n} := rfl
      rw [heq]
      exact Set.Finite.preimage hi.injOn (Set.finite_le_nat (φ n))
    obtain ⟨m, hm⟩ := (h_inf.sdiff h_fin).nonempty
    simp only [Set.mem_sdiff, Set.mem_setOf_eq, not_le] at hm
    exact ⟨m, hm.1, hm.2⟩
  choose f h_f h_φ using h_step
  refine ⟨fun k => f^[k] 0, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    change f^[n] 0 < f^[n + 1] 0
    rw [Function.iterate_succ_apply']
    exact h_f _
  · intro n
    change φ (f^[n] 0) < φ' (f^[n + 1] 0)
    rw [Function.iterate_succ_apply']
    exact h_φ _

/-- The ω-limit of the Choueka language of `da` (with accept set `acc`) is a subset of the
ω-power of `da`'s (finite-word) accepted language. Does not require `da` to be finite-state. -/
theorem chouekaLang_omega_limit_subset_omega_power [Inhabited Symbol]
    (da : DA State Symbol) (acc : Set State) :
    (chouekaLang da acc)↗ω ⊆ (language (FinAcc.mk da acc))^ω := by
  intro xs hxs
  have hxs' : ∃ᶠ m in Filter.atTop, xs.extract 0 m ∈ chouekaLang da acc := hxs
  rw [frequently_iff_strictMono] at hxs'
  obtain ⟨φ, h_φ_mono, h_prefix⟩ := hxs'
  have h_m_ex : ∀ n, ∃ m, 0 < m ∧ m < φ n ∧
      da.mtr da.start (xs.extract 0 m) ∈ acc ∧
      da.mtr da.start (xs.extract m (φ n)) = da.mtr da.start (xs.extract 0 (φ n)) ∧
      ∀ k, m < k → k < φ n →
        da.mtr da.start (xs.extract m k) ≠ da.mtr da.start (xs.extract 0 k) := by
    intro n
    obtain ⟨m, h_m0, h_m1, h_acc, h_run, h_run'⟩ := h_prefix n
    rw [length_extract, Nat.sub_zero] at h_m1
    refine ⟨m, h_m0, h_m1, ?_, ?_, ?_⟩
    · rwa [take_extract (by omega : m ≤ φ n - 0), Nat.zero_add] at h_acc
    · rwa [drop_extract (by omega : m ≤ φ n - 0), Nat.zero_add] at h_run
    · intro k h_k1 h_k2
      have h_len : k < (xs.extract 0 (φ n)).length := by
        rw [length_extract, Nat.sub_zero]; omega
      have h_run'' := h_run' k h_k1 h_len
      rw [drop_extract (by omega : m ≤ φ n - 0), Nat.zero_add,
        take_extract (by omega : k - m ≤ φ n - m),
        show m + (k - m) = k by omega,
        take_extract (by omega : k ≤ φ n - 0), Nat.zero_add] at h_run''
      exact h_run''
  choose φ' h_φ'_0 h_φ'_n h_acc h_run h_run' using h_m_ex
  have key : ∀ n1 n2, n1 < n2 → φ' n1 ≠ φ' n2 := by
    intro n1 n2 h heq
    have h1 := h_φ_mono h
    have h2 := h_φ'_n n1
    have h3 := h_run n1
    rw [heq] at h3
    exact (h_run' n2 (φ n1) (by omega) (by omega)) h3
  have h_inj : Function.Injective φ' := by
    intro n1 n2 heq
    rcases lt_trichotomy n1 n2 with h | h | h
    · exact absurd heq (key n1 n2 h)
    · exact h
    · exact absurd heq.symm (key n2 n1 h)
  obtain ⟨σ, h_σ_mono, h_φ_φ'⟩ := greater_subseq φ φ' h_inj
  rw [omegaPow_seq_prop]
  refine ⟨fun k => match k with | 0 => 0 | (n + 1) => φ' (σ n), ?_, rfl, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    cases n with
    | zero => exact h_φ'_0 (σ 0)
    | succ k =>
      have h1 := h_φ'_n (σ k)
      have h2 := h_φ_φ' k
      change φ' (σ k) < φ' (σ (k + 1))
      omega
  · intro m
    cases m with
    | zero =>
      change da.mtr da.start (xs.extract 0 (φ' (σ 0))) ∈ acc
      exact h_acc (σ 0)
    | succ k =>
      change da.mtr da.start (xs.extract (φ' (σ k)) (φ' (σ (k + 1)))) ∈ acc
      have hle1 : φ' (σ k) ≤ φ (σ k) := le_of_lt (h_φ'_n (σ k))
      have hle2 : φ (σ k) ≤ φ' (σ (k + 1)) := le_of_lt (h_φ_φ' k)
      rw [← append_extract_extract hle1 hle2, mtr_append, h_run (σ k),
        ← mtr_append, append_extract_extract (Nat.zero_le _) hle2]
      exact h_acc (σ (k + 1))

end Cslib.Automata.DA
