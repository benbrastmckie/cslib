/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Semantics.GNBA.Construction

/-! # GNBA Correctness — Language Equality

This module proves the main correctness theorem: the NBA built from the GNBA construction
accepts exactly the ω-words satisfying the formula.

## Main theorem

- `Formula.gnba_language_eq`: `language (gnbaNBA φ) = gnbaOmegaLanguage φ`
-/

@[expose] public section

namespace Cslib.Logic.LTL

variable {Atom : Type*}

open Cslib.Automata NA

/-! ## GNBA Correctness -/

/-- The omega-language of a formula `φ`: the set of omega-sequences over `Set Atom` satisfying
`φ` at position 0.

This is defined here to state `gnba_language_eq` within `GNBA.Correctness` without importing
`OmegaRegular.lean` (which would create a circular dependency in Phase 5 when
`OmegaRegular.lean` imports `GNBA.lean`). The definition is equivalent to
`Formula.omegaLanguage` in `OmegaRegular.lean`. -/
def Formula.gnbaOmegaLanguage (φ : Formula Atom) : ωLanguage (Set Atom) :=
  ⟨{ v | Satisfies (fun p s => p ∈ s) v φ }⟩

/-! ### Canonical run transitions -/

/-- Helper: if `next ψ ∈ φ.subformulas` then `ψ ∈ φ.subformulas`.

Subformulas are downward closed: the argument of `next` is itself a subformula. -/
private lemma Formula.subformulas_next_sub {φ ψ : Formula Atom}
    (h : Formula.next ψ ∈ Formula.subformulas φ) : ψ ∈ Formula.subformulas φ :=
  Formula.subformulas_trans (Set.mem_union_right _ (Formula.self_mem_subformulas _)) h

/-- A helper lemma: `ψ` is in the closure of `φ` whenever `next ψ` is.

If `next ψ ∈ φ.closure`, then by `mem_closure_cases`, either:
- `next ψ ∈ subformulas φ`, so `ψ ∈ subformulas φ` (via `subformulas_next_sub`),
- `next ψ = imp χ bot` for some χ (impossible),
- `next ψ = next (untl χ₁ χ₂)` for some until subformula (so `ψ = untl χ₁ χ₂ ∈ subformulas φ`).
In all valid cases, `ψ ∈ φ.closure`. -/
private lemma Formula.next_sub_mem_closure {φ ψ : Formula Atom}
    (hnext : Formula.next ψ ∈ Formula.closure φ) : ψ ∈ Formula.closure φ := by
  rcases Formula.mem_closure_cases hnext with hsub | ⟨χ, _, heq⟩ | ⟨χ₁, χ₂, huntl_sub, heq⟩
  · exact Formula.subformula_mem_closure (Formula.subformulas_next_sub hsub)
  · simp at heq
  · simp only [Formula.next.injEq] at heq
    exact Formula.subformula_mem_closure (heq ▸ huntl_sub)

/-- The canonical run `i ↦ canonicalAtom v i φ` satisfies the GNBA transition relation
at every step.

At each step `i`, the canonical atom at `i` transitions to the canonical atom at `i+1`
via the input letter `v i`. The three transition conditions follow from:
1. Letter consistency: `Satisfies val (v.drop i) (atom p) ↔ p ∈ v.head` (by `Satisfies`)
2. Next-step consistency: `Satisfies val (v.drop i) (next ψ) ↔ Satisfies val (v.drop (i+1)) ψ`
3. Until expansion: the expansion law for `Satisfies val (v.drop i) (untl ψ₁ ψ₂)` -/
private lemma Formula.canonicalAtom_gnbaTr (v : ωSequence (Set Atom)) (i : ℕ) (φ : Formula Atom) :
    Formula.gnbaTr φ
      ⟨Formula.canonicalAtom v i φ,
       Formula.canonicalAtom_isAtom v i φ⟩
      (v i)
      ⟨Formula.canonicalAtom v (i + 1) φ,
       Formula.canonicalAtom_isAtom v (i + 1) φ⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · -- Letter consistency: atom p ∈ B_i ↔ p ∈ v i
    -- `Satisfies val (v.drop i) (atom p) = p ∈ (v.drop i).head = p ∈ v i`
    intro p _hpAtom
    simp only [Formula.canonicalAtom_mem_iff, Satisfies, ωSequence.head_drop]
    constructor
    · rintro ⟨_, hp⟩; exact hp
    · intro hp; exact ⟨_hpAtom, hp⟩
  · -- Next-step consistency: next ψ ∈ B_i ↔ ψ ∈ B_{i+1}
    -- Satisfies val (v.drop i) (next ψ) = Satisfies val (v.drop i).tail ψ
    --   = Satisfies val (v.drop (i+1)) ψ
    intro ψ hnext
    simp only [Formula.canonicalAtom_mem_iff]
    constructor
    · rintro ⟨_, hsat⟩
      refine ⟨Formula.next_sub_mem_closure hnext, ?_⟩
      -- hsat : Satisfies (fun p s => p ∈ s) (v.drop i) (next ψ) = Satisfies ... (v.drop i).tail ψ
      -- (v.drop i).tail = v.drop (i+1) by tail_drop'
      simp only [Satisfies] at hsat
      rwa [ωSequence.tail_drop'] at hsat
    · rintro ⟨_hψcl, hsat⟩
      refine ⟨hnext, ?_⟩
      simp only [Satisfies]
      rwa [ωSequence.tail_drop']
  · -- Until expansion: untl ψ₁ ψ₂ ∈ B_i ↔ (ψ₂ ∈ B_i ∨ (ψ₁ ∈ B_i ∧ untl ψ₁ ψ₂ ∈ B_{i+1}))
    -- New untl: ∃ j', Satisfies val (v.drop (i+j')) ψ₂ ∧ ∀ k < j', Satisfies val (v.drop (i+k)) ψ₁
    intro ψ₁ ψ₂ huntl
    simp only [Formula.canonicalAtom_mem_iff, Satisfies, ωSequence.drop_drop]
    constructor
    · -- untl ψ₁ ψ₂ ∈ B_i → ψ₂ ∈ B_i ∨ (ψ₁ ∈ B_i ∧ untl ψ₁ ψ₂ ∈ B_{i+1})
      rintro ⟨_, j', hjψ₂, hguard⟩
      by_cases hj'0 : j' = 0
      · -- j' = 0: ψ₂ ∈ B_i (since v.drop (i+0) = v.drop i)
        left
        simp only [hj'0, Nat.add_zero] at hjψ₂
        exact ⟨Formula.untl_right_mem_closure huntl, hjψ₂⟩
      · -- j' > 0: ψ₁ ∈ B_i and untl ψ₁ ψ₂ ∈ B_{i+1}
        right
        have hj'_pos : 0 < j' := Nat.pos_of_ne_zero hj'0
        -- ψ₁ ∈ B_i: guard at k=0 gives Satisfies val (v.drop (i+0)) ψ₁
        have hψ₁_at_i : Satisfies (fun p s => p ∈ s) (v.drop (i + 0)) ψ₁ :=
          hguard 0 hj'_pos
        simp only [Nat.add_zero] at hψ₁_at_i
        refine ⟨⟨Formula.untl_left_mem_closure huntl, hψ₁_at_i⟩, huntl, ?_⟩
        -- untl ψ₁ ψ₂ ∈ B_{i+1}: use j' - 1 as the witness
        -- v.drop ((i+1) + (j'-1)) = v.drop (i + j') by omega
        have hj'_pred : j' - 1 + 1 = j' := Nat.sub_add_cancel hj'_pos
        refine ⟨j' - 1, ?_, ?_⟩
        · -- Satisfies val (v.drop ((i+1) + (j'-1))) ψ₂
          convert hjψ₂ using 2; omega
        · -- ∀ k < j'-1, Satisfies val (v.drop ((i+1)+k)) ψ₁
          intro k hk
          have := hguard (k + 1) (by omega)
          convert this using 2; omega
    · -- ψ₂ ∈ B_i ∨ (ψ₁ ∈ B_i ∧ untl ψ₁ ψ₂ ∈ B_{i+1}) → untl ψ₁ ψ₂ ∈ B_i
      rintro (⟨_, hψ₂sat⟩ | ⟨⟨_, hψ₁sat⟩, _, j', hjψ₂, hguard⟩)
      · -- ψ₂ ∈ B_i: take j' = 0, v.drop (i+0) = v.drop i
        exact ⟨huntl, 0, by simpa, fun k hk => absurd hk (Nat.not_lt.mpr (Nat.zero_le k))⟩
      · -- ψ₁ ∈ B_i and untl ψ₁ ψ₂ ∈ B_{i+1}: combine with j' + 1
        -- v.drop (i + (j'+1)) = v.drop ((i+1) + j')
        refine ⟨huntl, j' + 1, ?_, ?_⟩
        · convert hjψ₂ using 2; omega
        · intro k hk
          by_cases hk0 : k = 0
          · simp only [hk0, Nat.add_zero]; exact hψ₁sat
          · have := hguard (k - 1) (by omega)
            convert this using 2; omega

/-! ### Counter step function -/

open Classical in
private noncomputable def Formula.gnbaCtrStep (φ : Formula Atom)
    (B : ℕ → Formula.GNBAState φ) (n : ℕ) (prev : Fin (Formula.gnbaK φ).succ) :
    Fin (Formula.gnbaK φ).succ :=
  if hK : Formula.gnbaK φ = 0 then ⟨0, by omega⟩
  else if hlt : prev.val < Formula.gnbaK φ then
    if B n ∈ Formula.gnbaAcceptSet φ ((Formula.untlFinset φ).toList.get
        ⟨prev.val, by rwa [Finset.length_toList, ← Formula.gnbaK]⟩) then
      ⟨prev.val + 1, by omega⟩
    else prev
  else ⟨0, Nat.succ_pos _⟩

private noncomputable def Formula.gnbaCtrSeq (φ : Formula Atom)
    (B : ℕ → Formula.GNBAState φ) : ℕ → Fin (Formula.gnbaK φ).succ
  | 0 => ⟨0, Nat.succ_pos _⟩
  | n + 1 => Formula.gnbaCtrStep φ B n (Formula.gnbaCtrSeq φ B n)

private lemma Formula.gnbaCtrStep_not_mem (φ : Formula Atom) (B : ℕ → Formula.GNBAState φ)
    (n : ℕ) (prev : Fin (Formula.gnbaK φ).succ) (hK : ¬Formula.gnbaK φ = 0)
    (hlt : prev.val < Formula.gnbaK φ) (hnotmem : B n ∉ Formula.gnbaAcceptSet φ
      ((Formula.untlFinset φ).toList.get ⟨prev.val,
        by rwa [Finset.length_toList, ← Formula.gnbaK]⟩)) :
    Formula.gnbaCtrStep φ B n prev = prev := by
  unfold gnbaCtrStep
  exact (dif_neg hK).trans ((dif_pos hlt).trans (if_neg hnotmem))

private lemma Formula.gnbaCtrStep_mem (φ : Formula Atom) (B : ℕ → Formula.GNBAState φ)
    (n : ℕ) (prev : Fin (Formula.gnbaK φ).succ) (hK : ¬Formula.gnbaK φ = 0)
    (hlt : prev.val < Formula.gnbaK φ) (hmem : B n ∈ Formula.gnbaAcceptSet φ
      ((Formula.untlFinset φ).toList.get ⟨prev.val,
        by rwa [Finset.length_toList, ← Formula.gnbaK]⟩)) :
    Formula.gnbaCtrStep φ B n prev = ⟨prev.val + 1, by omega⟩ := by
  unfold gnbaCtrStep
  exact (dif_neg hK).trans ((dif_pos hlt).trans (if_pos hmem))

/-! ### GNBA language equality -/

/-- The language of the NBA built from the GNBA equals the omega-language of `φ`.

This is the key correctness theorem (Baier-Katoen Theorem 5.39). The proof proceeds via
`gnba_completeness` (satisfaction implies NBA accepting run via the canonical run) and
`gnba_soundness` (NBA accepting run implies satisfaction via structural induction). -/
theorem Formula.gnba_language_eq (φ : Formula Atom) :
    Cslib.Automata.ωAcceptor.language (Formula.gnbaNBA φ) =
      Formula.gnbaOmegaLanguage φ := by
  apply Cslib.ωLanguage.mem_ext
  intro v
  simp only [Formula.gnbaOmegaLanguage, Cslib.ωLanguage.mem_def, Set.mem_setOf_eq]
  constructor
  · -- Soundness: NBA accepting run → satisfaction
    -- Use Classical for Decidability of B ∈ gnbaAcceptSet throughout
    classical
    rintro ⟨ss, ⟨hstart, htrans⟩, hacc⟩
    -- Extract the GNBA run and counter from the NBA run
    let B : ℕ → Formula.GNBAState φ := fun i => (ss i).1
    let ctr : ℕ → Fin (Formula.gnbaK φ).succ := fun i => (ss i).2
    -- At each step, the GNBA transition holds
    have hgnbaTr : ∀ i, Formula.gnbaTr φ (B i) (v i) (B (i + 1)) := by
      intro i
      have := htrans i
      simp only [Formula.gnbaNBA] at this
      exact this.1
    -- NBA acceptance means counter = gnbaK φ infinitely often
    have haccK : ∃ᶠ k in Filter.atTop, (ctr k).val = Formula.gnbaK φ := by
      rw [Filter.frequently_atTop] at hacc ⊢
      intro n
      obtain ⟨k, hk, hk_acc⟩ := hacc n
      simp only [Formula.gnbaNBA, Set.mem_setOf_eq] at hk_acc
      exact ⟨k, hk, hk_acc⟩
    -- Counter transition lemma: extract the counter condition from the NBA transition
    have hctr_trans : ∀ i,
        if h : Formula.gnbaK φ = 0 then (ctr (i + 1)).val = 0
        else if hi : (ctr i).val < Formula.gnbaK φ then
          let idx : Fin (Formula.gnbaK φ) := ⟨(ctr i).val, hi⟩
          let hlen_i : idx.val < (Formula.untlFinset φ).toList.length :=
            Finset.length_toList (Formula.untlFinset φ) ▸ idx.isLt
          let χ_i := (Formula.untlFinset φ).toList.get ⟨idx.val, hlen_i⟩
          if B i ∈ Formula.gnbaAcceptSet φ χ_i then
            (ctr (i + 1)).val = (ctr i).val + 1
          else ctr (i + 1) = ctr i
        else (ctr (i + 1)).val = 0 := by
      intro i
      -- Extract Tr at i without destructuring ss i, so B/ctr remain definitionally aligned.
      have htransi := htrans i
      simp only [Formula.gnbaNBA] at htransi
      -- The counter condition uses classical if, so open Classical here
      classical
      exact htransi.2
    -- Key: between two consecutive counter-K-visits, the counter cycles 0 → 1 → ... → K.
    -- Single-step counter lemma: when ctr t < K, the counter either stays or advances by 1.
    have hctr_step : ∀ t, (ctr t).val < Formula.gnbaK φ →
        (ctr (t + 1)).val = (ctr t).val ∨ (ctr (t + 1)).val = (ctr t).val + 1 := by
      intro t hlt
      have htrans_t := hctr_trans t
      have hK_ne : Formula.gnbaK φ ≠ 0 :=
          Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
      simp only [dif_neg hK_ne, dif_pos hlt] at htrans_t
      split_ifs at htrans_t with hacc
      · right; exact htrans_t
      · left; exact congrArg Fin.val htrans_t
    -- When ctr t = K, counter resets to 0.
    have hctr_reset : ∀ t, (ctr t).val = Formula.gnbaK φ → (ctr (t + 1)).val = 0 := by
      intro t heqK
      have htrans_t := hctr_trans t
      by_cases hK : Formula.gnbaK φ = 0
      · simp only [hK] at htrans_t; exact htrans_t
      · have hlt_false : ¬ (ctr t).val < Formula.gnbaK φ := by omega
        simp only [dif_neg hK, dif_neg hlt_false] at htrans_t
        exact htrans_t
    -- hgnbaAcc: between two K-visits, every acceptance set is visited.
    -- Key argument: the counter starts at 0 after a K-reset and reaches K again,
    -- so it must pass through every value 0..K-1, including the index m of χ.
    -- When the counter advances from m to m+1, B t ∈ gnbaAcceptSet φ χ.
    have hgnbaAcc : ∀ χ ∈ Formula.untlSubformulas φ, ∃ᶠ k in Filter.atTop,
        B k ∈ Formula.gnbaAcceptSet φ χ := by
      intro χ hχ
      have hχ_mem : χ ∈ Formula.untlFinset φ := by
        simp only [Formula.untlFinset]; rwa [Set.Finite.mem_toFinset]
      have hK_pos : 0 < Formula.gnbaK φ := by
        simp only [Formula.gnbaK]; exact Finset.card_pos.mpr ⟨χ, hχ_mem⟩
      rw [Filter.frequently_atTop]
      intro N
      rw [Filter.frequently_atTop] at haccK
      obtain ⟨t₀, ht₀N, ht₀K⟩ := haccK N
      -- At t₀+1, counter resets to 0
      have ht₀_reset : (ctr (t₀ + 1)).val = 0 := hctr_reset t₀ ht₀K
      -- Find t₁ ≥ t₀+1 with ctr t₁ = K
      obtain ⟨t₁, ht₁t₀, ht₁K⟩ := haccK (t₀ + 1)
      -- Get index m of χ in untlFinset via the list.
      have hχ_in_list : χ ∈ (Formula.untlFinset φ).toList := Finset.mem_toList.mpr hχ_mem
      obtain ⟨m, hm_lt_len, hm_eq⟩ := List.mem_iff_getElem.mp hχ_in_list
      -- m < gnbaK φ since the list has card = gnbaK φ elements.
      have hm_lt : m < Formula.gnbaK φ := by
        simp only [Formula.gnbaK, ← Finset.length_toList]; exact hm_lt_len
      -- The list element at index m is χ.
      -- hm_eq : (Formula.untlFinset φ).toList[m]'hm_lt_len = χ
      -- Convert: List.get and list[i]' are the same (List.get_eq_getElem)
      have hm_list_get : (Formula.untlFinset φ).toList.get ⟨m, hm_lt_len⟩ = χ := by
        rw [List.get_eq_getElem]; exact hm_eq
      -- Between t₀+1 and t₁, counter goes from 0 to K passing through m.
      -- Use Nat.find to locate the first time ctr exceeds m after t₀+1.
      -- The predicate: t₀+1 ≤ t ∧ (ctr t).val ≥ m+1.
      -- t₁ witnesses this since (ctr t₁).val = K > m.
      have hwitness : t₀ + 1 ≤ t₁ ∧ (ctr t₁).val ≥ m + 1 := ⟨ht₁t₀, by omega⟩
      -- Define the predicate using the gap from t₀+1
      -- Let gap = t₁ - (t₀+1); we work within [t₀+1, t₁].
      -- Find smallest d such that (ctr (t₀+1+d)).val ≥ m+1.
      -- Since (ctr (t₀+1)).val = 0 ≤ m, we have d ≥ 1.
      -- Let gap = t₁ - (t₀+1) ≥ 0.
      set gap := t₁ - (t₀ + 1) with hgap_def
      have ht₁_eq : t₁ = t₀ + 1 + gap := by omega
      -- The counter at t₀+1+gap = t₁ is K.
      have ht₁_gap : (ctr (t₀ + 1 + gap)).val = Formula.gnbaK φ := ht₁_eq ▸ ht₁K
      -- Since (ctr (t₀+1)).val = 0 ≤ m < m+1 ≤ K, gap ≥ 1.
      -- Find the smallest d_first with (ctr (t₀+1+d_first)).val ≥ m+1
      have hd_exists : ∃ d, d ≤ gap ∧ (ctr (t₀ + 1 + d)).val ≥ m + 1 :=
        ⟨gap, le_refl _, by omega⟩
      -- Use Nat.find to get the minimal such d
      -- Need DecidablePred for Nat.find
      haveI hd_dec : DecidablePred (fun d : ℕ => d ≤ gap ∧ (ctr (t₀ + 1 + d)).val ≥ m + 1) :=
        fun d => Classical.propDecidable _
      let d_first := Nat.find hd_exists
      have hd_first_bound : d_first ≤ gap :=
        (Nat.find_spec hd_exists).1
      have hd_first_ge : (ctr (t₀ + 1 + d_first)).val ≥ m + 1 :=
        (Nat.find_spec hd_exists).2
      -- d_first ≥ 1 since (ctr (t₀+1)).val = 0 < m+1
      have hd_first_pos : 0 < d_first := by
        by_contra h0
        push Not at h0
        have hd0 : d_first = 0 := Nat.le_zero.mp h0
        simp only [hd0, Nat.add_zero] at hd_first_ge
        omega
      -- At t₀+1+(d_first-1): counter ≤ m (by minimality of d_first)
      have hprev_lt : (ctr (t₀ + 1 + (d_first - 1))).val ≤ m := by
        by_contra hcontra
        push Not at hcontra
        have hd_pred_lt : d_first - 1 < d_first := Nat.sub_lt hd_first_pos Nat.one_pos
        have hd_pred_gap : d_first - 1 ≤ gap := by omega
        exact absurd ⟨hd_pred_gap, by omega⟩ (Nat.find_min hd_exists hd_pred_lt)
      -- At t₀+1+(d_first-1): counter < K (since ≤ m < K)
      have hprev_lt_K : (ctr (t₀ + 1 + (d_first - 1))).val < Formula.gnbaK φ := by omega
      -- d_first-1+1 = d_first, so t₀+1+(d_first-1)+1 = t₀+1+d_first
      have hsucc_eq : t₀ + 1 + (d_first - 1) + 1 = t₀ + 1 + d_first := by omega
      -- From hctr_step at t₀+1+(d_first-1), counter either stays or advances by 1
      have hstep := hctr_step (t₀ + 1 + (d_first - 1)) hprev_lt_K
      rw [hsucc_eq] at hstep
      -- Counter advances: must be prev+1 = (ctr t).val at d_first position
      -- Since prev ≤ m < m+1 ≤ ctr at d_first, must have ctr at d_first = prev+1 ≥ m+1
      have hprev_advance :
          (ctr (t₀ + 1 + d_first)).val = (ctr (t₀ + 1 + (d_first - 1))).val + 1 := by
        rcases hstep with hstay | hadvance
        · -- Stay: contradiction since ctr at d_first ≥ m+1 > prev ≤ m
          omega
        · exact hadvance
      -- So (ctr (t₀+1+(d_first-1))).val = m (since ≤ m and +1 gives ≥ m+1)
      have hprev_eq_m : (ctr (t₀ + 1 + (d_first - 1))).val = m := by omega
      -- The advance condition: B (t₀+1+(d_first-1)) ∈ gnbaAcceptSet φ χ
      -- From hctr_trans: since ctr advanced, B t ∈ gnbaAcceptSet φ (list.get[m]) = χ
      have hmem_acc : B (t₀ + 1 + (d_first - 1)) ∈ Formula.gnbaAcceptSet φ χ := by
        classical
        have htrans_prev := hctr_trans (t₀ + 1 + (d_first - 1))
        have hK_ne : Formula.gnbaK φ ≠ 0 := Nat.pos_iff_ne_zero.mp hK_pos
        simp only [dif_neg hK_ne, dif_pos hprev_lt_K] at htrans_prev
        -- The Fin index at this step has val = m
        have hprev_idx_val : (⟨(ctr (t₀ + 1 + (d_first - 1))).val,
            Finset.length_toList (Formula.untlFinset φ) ▸ hprev_lt_K⟩ :
            Fin (Formula.untlFinset φ).toList.length).val = m := hprev_eq_m
        -- The list element at this index equals χ
        have hget_eq : (Formula.untlFinset φ).toList.get ⟨(ctr (t₀ + 1 + (d_first - 1))).val,
            Finset.length_toList (Formula.untlFinset φ) ▸ hprev_lt_K⟩ = χ := by
          conv_lhs => rw [show (⟨(ctr (t₀ + 1 + (d_first - 1))).val,
            Finset.length_toList (Formula.untlFinset φ) ▸ hprev_lt_K⟩ :
            Fin (Formula.untlFinset φ).toList.length) =
            ⟨m, hm_lt_len⟩ from by ext; exact hprev_eq_m]
          exact hm_list_get
        rw [hsucc_eq] at htrans_prev
        -- If acceptance set satisfied: ctr advanced (which we know)
        split_ifs at htrans_prev with hacc
        · rwa [hget_eq] at hacc
        · -- Counter stayed: contradiction with hprev_advance
          have heq := congrArg Fin.val htrans_prev
          omega
      -- Conclude: t₀+1+(d_first-1) ≥ N (since t₀ ≥ N and d_first-1 ≥ 0)
      exact ⟨t₀ + 1 + (d_first - 1), by omega, hmem_acc⟩
    -- Key biconditional lemma: ψ ∈ B_i ↔ Satisfies val (v.drop i) ψ (for all ψ ∈ closure φ)
    have hkey : ∀ (ψ : Formula Atom), ψ ∈ Formula.closure φ →
        ∀ i, (ψ ∈ (B i).val ↔ Satisfies (fun p s => p ∈ s) (v.drop i) ψ) := by
      intro ψ hψcl
      induction ψ with
      | atom p =>
        intro i
        simp only [Satisfies, ωSequence.head_drop]
        exact ⟨fun hmem => (hgnbaTr i).1 p hψcl |>.mp hmem,
               fun hp => (hgnbaTr i).1 p hψcl |>.mpr hp⟩
      | bot =>
        intro i
        simp only [Satisfies]
        exact ⟨fun hmem => absurd hmem (B i).property.botConsistent, False.elim⟩
      | imp ψ₁ ψ₂ ih₁ ih₂ =>
        intro i
        simp only [Satisfies]
        have hψ₁cl : ψ₁ ∈ Formula.closure φ := Formula.imp_sub_left_mem_closure hψcl
        rw [(B i).property.impClosure ψ₁ ψ₂ hψcl]
        constructor
        · intro hor
          rcases hor with hnotψ₁ | hψ₂mem
          · -- ψ₁ ∉ B_i: by biconditional IH, ¬Satisfies ψ₁
            intro hsat1
            exact (hnotψ₁ ((ih₁ hψ₁cl i).mpr hsat1)).elim
          · -- ψ₂ ∈ B_i: need Satisfies ψ₂
            intro _
            rcases Formula.mem_closure_cases hψcl with hsub | ⟨χ, _, heq⟩ | ⟨_, _, _, heq⟩
            · -- imp ψ₁ ψ₂ ∈ subformulas
              have hψ₂ne : ψ₂ ≠ Formula.bot :=
                fun h => absurd (h ▸ hψ₂mem) (B i).property.botConsistent
              exact (ih₂ (Formula.imp_sub_right_mem_closure hψcl hψ₂ne) i).mp hψ₂mem
            · -- imp ψ₁ ψ₂ = imp χ bot, so ψ₂ = bot: ψ₂ ∈ B_i contradicts botConsistent
              simp only [Formula.imp.injEq] at heq
              exact absurd (heq.2 ▸ hψ₂mem) (B i).property.botConsistent
            · simp at heq
        · intro hsat
          by_cases h : ψ₁ ∈ (B i).val
          · right
            have hψ₁sat := (ih₁ hψ₁cl i).mp h
            rcases Formula.mem_closure_cases hψcl with hsub | ⟨χ, _, heq⟩ | ⟨_, _, _, heq⟩
            · have hψ₂ne : ψ₂ ≠ Formula.bot := by
                intro hbot
                simp only [hbot, Satisfies] at hsat
                exact absurd (hsat hψ₁sat) id
              exact (ih₂ (Formula.imp_sub_right_mem_closure hψcl hψ₂ne) i).mpr (hsat hψ₁sat)
            · simp only [Formula.imp.injEq] at heq
              simp only [heq.2, Satisfies] at hsat
              exact absurd (hsat hψ₁sat) id
            · simp at heq
          · exact Or.inl h
      | next ψ ih =>
        intro i
        simp only [Satisfies, ωSequence.tail_drop']
        have hψcl' : ψ ∈ Formula.closure φ := Formula.next_sub_mem_closure hψcl
        constructor
        · intro hmem
          exact (ih hψcl' (i + 1)).mp ((hgnbaTr i).2.1 ψ hψcl |>.mp hmem)
        · intro hsat
          exact (hgnbaTr i).2.1 ψ hψcl |>.mpr ((ih hψcl' (i + 1)).mpr hsat)
      | untl ψ₁ ψ₂ ih₁ ih₂ =>
        intro i
        simp only [Satisfies, ωSequence.drop_drop]
        have hψ₁cl : ψ₁ ∈ Formula.closure φ := Formula.untl_left_mem_closure hψcl
        have hψ₂cl : ψ₂ ∈ Formula.closure φ := Formula.untl_right_mem_closure hψcl
        constructor
        · -- Forward: untl ψ₁ ψ₂ ∈ B_i → ∃ j', Satisfies val (v.drop (i+j')) ψ₂ ∧ ...
          intro hmem
          -- Use hgnbaAcc to find acceptance set visit after i
          have huntl_sub : Formula.untl ψ₁ ψ₂ ∈ Formula.untlSubformulas φ :=
            ⟨hψcl, ψ₁, ψ₂, rfl⟩
          have hgnbaAcc_untl := hgnbaAcc (Formula.untl ψ₁ ψ₂) huntl_sub
          rw [Filter.frequently_atTop] at hgnbaAcc_untl
          obtain ⟨j₀, hj₀i, hj₀acc⟩ := hgnbaAcc_untl i
          simp only [Formula.gnbaAcceptSet, Set.mem_setOf_eq] at hj₀acc
          -- Simplify hj₀acc: the existential in the inr case collapses to ψ₂ ∈ B j₀
          have hj₀acc' : Formula.untl ψ₁ ψ₂ ∉ (B j₀).val ∨ ψ₂ ∈ (B j₀).val := by
            rcases hj₀acc with h | ⟨ψ₁', ψ₂', heq, hmem⟩
            · exact Or.inl h
            · simp only [Formula.untl.injEq] at heq
              exact Or.inr (heq.2 ▸ hmem)
          -- Find minimum j ≥ i where untl ψ₁ ψ₂ ∉ B_j or ψ₂ ∈ B_j
          haveI hP_dec : DecidablePred (fun k =>
              k ≥ i ∧ (Formula.untl ψ₁ ψ₂ ∉ (B k).val ∨ ψ₂ ∈ (B k).val)) :=
            fun k => Classical.dec _
          let P : ℕ → Prop := fun k => k ≥ i ∧ (Formula.untl ψ₁ ψ₂ ∉ (B k).val ∨ ψ₂ ∈ (B k).val)
          have hP_ex : ∃ k, P k := ⟨j₀, hj₀i, hj₀acc'⟩
          let j := Nat.find hP_ex
          have hj_spec : P j := Nat.find_spec hP_ex
          have hj_min : ∀ m < j, ¬P m := fun m hm => Nat.find_min hP_ex hm
          obtain ⟨hji, hjacc⟩ := hj_spec
          -- For k ∈ [i, j): untl ψ₁ ψ₂ ∈ B_k and ψ₂ ∉ B_k
          have hpath : ∀ k, i ≤ k → k < j →
              Formula.untl ψ₁ ψ₂ ∈ (B k).val ∧ ψ₂ ∉ (B k).val := by
            intro k hik hkj
            by_contra hc
            push Not at hc
            have hPk : P k := ⟨hik, by
              by_cases hmemk : (Formula.untl ψ₁ ψ₂) ∈ (B k).val
              · exact Or.inr (hc hmemk)
              · exact Or.inl hmemk⟩
            exact absurd hPk (hj_min k hkj)
          rcases hjacc with huntl_not | hψ₂j
          · -- untl ψ₁ ψ₂ ∉ B_j
            by_cases hji_eq : j = i
            · exact absurd (hji_eq ▸ hmem) huntl_not
            · -- j > i: use GNBA transition at j-1
              have hj_pos : 0 < j := by omega
              have hjm1_ge : i ≤ j - 1 := by omega
              have hjm1_lt : j - 1 < j := Nat.sub_lt hj_pos one_pos
              obtain ⟨huntl_jm1, hnotψ₂_jm1⟩ := hpath (j - 1) hjm1_ge hjm1_lt
              have hexp := (hgnbaTr (j - 1)).2.2 ψ₁ ψ₂ hψcl |>.mp huntl_jm1
              rcases hexp with hψ₂ | ⟨_, huntl_j⟩
              · exact absurd hψ₂ hnotψ₂_jm1
              · have : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hj_pos
                exact absurd (this ▸ huntl_j) huntl_not
          · -- ψ₂ ∈ B_j: build the Until witness with offset j' = j - i
            have hψ₁_path : ∀ k, i ≤ k → k < j → ψ₁ ∈ (B k).val := by
              intro k hik hkj
              obtain ⟨huntl_k, hnotψ₂_k⟩ := hpath k hik hkj
              exact (B k).property.untlLeft ψ₁ ψ₂ hψcl huntl_k hnotψ₂_k
            -- Use j' = j - i as witness
            refine ⟨j - i, ?_, ?_⟩
            · -- Satisfies val (v.drop (i + (j-i))) ψ₂ = Satisfies val (v.drop j) ψ₂
              have hconv : i + (j - i) = j := Nat.add_sub_cancel' hji
              rw [hconv]
              exact (ih₂ hψ₂cl j).mp hψ₂j
            · -- ∀ k < j-i, Satisfies val (v.drop (i+k)) ψ₁
              intro k hk
              exact (ih₁ hψ₁cl (i + k)).mp (hψ₁_path (i + k) (Nat.le_add_right i k) (by omega))
        · -- Backward: ∃ j', Satisfies val (v.drop (i+j')) ψ₂ ∧ ... → untl ψ₁ ψ₂ ∈ B_i
          intro ⟨j', hj'ψ₂, hψ₁k⟩
          -- Induction on j'
          suffices aux_back : ∀ (d : ℕ) (start : ℕ),
              Satisfies (fun p s => p ∈ s) (v.drop (start + d)) ψ₂ →
              (∀ k < d, Satisfies (fun p s => p ∈ s) (v.drop (start + k)) ψ₁) →
              Formula.untl ψ₁ ψ₂ ∈ (B start).val from by
            exact aux_back j' i hj'ψ₂ hψ₁k
          intro d
          induction d with
          | zero =>
            intro start hψ₂ _
            simp only [Nat.add_zero] at hψ₂
            have hψ₂_mem : ψ₂ ∈ (B start).val := (ih₂ hψ₂cl start).mpr hψ₂
            exact (B start).property.untlRight ψ₁ ψ₂ hψcl hψ₂_mem
          | succ d' ihd' =>
            intro start hψ₂ hψ₁k'
            -- hψ₂ : Satisfies val (v.drop (start + (d'+1))) ψ₂
            -- hψ₁k' : ∀ k < d'+1, Satisfies val (v.drop (start + k)) ψ₁
            have hψ₁start : Satisfies (fun p s => p ∈ s) (v.drop (start + 0)) ψ₁ :=
              hψ₁k' 0 (Nat.succ_pos d')
            simp only [Nat.add_zero] at hψ₁start
            have huntl_succ : Formula.untl ψ₁ ψ₂ ∈ (B (start + 1)).val := by
              apply ihd' (start + 1)
              · convert hψ₂ using 2; omega
              · intro k hk
                have := hψ₁k' (k + 1) (by omega)
                convert this using 2; omega
            have hψ₁mem : ψ₁ ∈ (B start).val := (ih₁ hψ₁cl start).mpr hψ₁start
            exact ((hgnbaTr start).2.2 ψ₁ ψ₂ hψcl).mpr (Or.inr ⟨hψ₁mem, huntl_succ⟩)
    -- Conclude: φ ∈ B_0 (from start condition) → Satisfies val v φ
    have hstart_gnba : (ss 0).1 ∈ Formula.gnbaStart φ := hstart.1
    simp only [Formula.gnbaStart, Set.mem_setOf_eq] at hstart_gnba
    have hphi_sat := (hkey φ (Formula.self_mem_closure φ) 0).mp hstart_gnba
    simpa using hphi_sat
  · -- Completeness: satisfaction → NBA accepting run
    classical
    intro hsat
    -- Construct the canonical GNBA run
    -- `v : ωSequence (Set Atom)`, use directly as the sequence for canonicalAtom
    let B : ℕ → Formula.GNBAState φ := fun i =>
      ⟨Formula.canonicalAtom v i φ, Formula.canonicalAtom_isAtom v i φ⟩
    -- B transitions satisfy gnbaTr
    have hgnbaTr : ∀ i, Formula.gnbaTr φ (B i) (v i) (B (i + 1)) :=
      fun i => Formula.canonicalAtom_gnbaTr v i φ
    -- φ ∈ B 0 (start state)
    have hstart : φ ∈ (B 0).val := by
      apply Formula.canonicalAtom_mem_iff.mpr
      exact ⟨Formula.self_mem_closure φ, by simpa using hsat⟩
    -- B visits each GNBA acceptance set infinitely often
    have hgnbaAcc : ∀ χ ∈ Formula.untlSubformulas φ, ∃ᶠ k in Filter.atTop,
        B k ∈ Formula.gnbaAcceptSet φ χ := by
      intro χ hχ
      obtain ⟨hχcl, ψ₁, ψ₂, hχeq⟩ := hχ
      subst hχeq
      rw [Filter.frequently_atTop]
      intro N
      by_contra hall
      push Not at hall
      simp only [Formula.gnbaAcceptSet, Set.mem_setOf_eq, not_or, not_not,
        not_exists, not_and] at hall
      -- hall : ∀ b ≥ N, (ψ₁ U ψ₂) ∈ B_b ∧ ∀ x x', (ψ₁ U ψ₂) = (x U x') → x' ∉ B_b
      -- From hall N: (ψ₁ U ψ₂) ∈ B_N
      obtain ⟨huntl_N, hnotψ₂_N⟩ := hall N (le_refl N)
      -- B_N = canonicalAtom, so Satisfies val (v.drop N) (ψ₁ U ψ₂)
      have huntl_N_sat : Satisfies (fun p s => p ∈ s) (v.drop N) (Formula.untl ψ₁ ψ₂) :=
        (Formula.canonicalAtom_mem_iff.mp huntl_N).2
      -- Get witness j' with Satisfies val (v.drop (N+j')) ψ₂
      simp only [Satisfies, ωSequence.drop_drop] at huntl_N_sat
      obtain ⟨j', hj'ψ₂, _⟩ := huntl_N_sat
      -- ψ₂ ∈ closure φ
      have hψ₂cl : ψ₂ ∈ Formula.closure φ := Formula.untl_right_mem_closure hχcl
      -- ψ₂ ∈ B (N + j')
      have hψ₂_in_Bj : ψ₂ ∈ (B (N + j')).val :=
        Formula.canonicalAtom_mem_iff.mpr ⟨hψ₂cl, hj'ψ₂⟩
      -- But hall (N + j') (by omega) says ψ₂ ∉ B (N + j')
      obtain ⟨_, hnotψ₂_j⟩ := hall (N + j') (Nat.le_add_right N j')
      exact absurd hψ₂_in_Bj (hnotψ₂_j ψ₁ ψ₂ rfl)
    -- Define the cycling counter sequence for the NBA run.
    -- Counter starts at 0 and advances through {0, ..., K-1, K} where K = gnbaK φ.
    -- When counter = i < K: advance to i+1 if B i ∈ gnbaAcceptSet χ_i, else stay.
    -- When counter = K: reset to 0.
    -- This gives a valid NBA run where counter = K infinitely often.
    let K := Formula.gnbaK φ
    let ctr : ℕ → Fin K.succ := Formula.gnbaCtrSeq φ B
    let ss : ℕ → Formula.GNBANBAState φ := fun k => (B k, ctr k)
    have hss_start : ss 0 ∈ (Formula.gnbaNBA φ).start := by
      simp only [Formula.gnbaNBA, ss, Set.mem_setOf_eq]
      exact ⟨hstart, rfl⟩
    have hss_trans : (Formula.gnbaNBA φ).OmegaExecution ss v := by
      intro n
      constructor
      · exact hgnbaTr n
      · -- ctr (n+1) = gnbaCtrStep φ B n (ctr n) by definition, matching gnbaNBA.Tr
        have hctr_succ : ctr (n + 1) = Formula.gnbaCtrStep φ B n (ctr n) := rfl
        rw [hctr_succ]
        unfold Formula.gnbaCtrStep
        split_ifs <;> first | rfl | simp_all
    -- Acceptance: ctr visits K infinitely often
    -- Proof: for any N, we find k ≥ N with ctr k = K by iterating through all K acceptance
    -- conditions. hgnbaAcc guarantees each acceptance set is visited infinitely often.
    -- The counter is monotone between resets: from ctr = m < K, it stays at m until
    -- B visits acc(untl[m]), then advances to m+1. After K such advances, ctr = K.
    have hss_acc : ∃ᶠ k in Filter.atTop, ss k ∈ (Formula.gnbaNBA φ).accept := by
      simp only [Formula.gnbaNBA, Set.mem_setOf_eq, ss]
      -- Goal: ∃ᶠ k in Filter.atTop, (ctr k).val = K
      -- First handle the trivial K = 0 case
      by_cases hK : K = 0
      · -- K = 0: ctr k ∈ Fin 1, so val = 0 = K for all k
        simp only [Filter.frequently_atTop]
        intro N
        refine ⟨N, le_refl _, ?_⟩
        have : (ctr N).val < K.succ := (ctr N).isLt
        omega
      · -- K > 0: the key cycling argument
        have hK_pos : 0 < K := Nat.pos_of_ne_zero hK
        -- Counter step lemma: ctr (n+1) is obtained by advancing ctr n (or staying)
        -- This follows from the definitional equality of ctr and the Tr counter clause.
        -- Key: from ctr t = m < K, the counter stays at m until B visits acc(untl[m]),
        -- then advances to m+1. So from any t with ctr t = m, ∃ t' ≥ t with ctr t' = m+1.
        -- Progress lemma: from ctr t = m < K, ∃ t' ≥ t with ctr t' = m+1.
        have hprogress : ∀ (m : ℕ) (hm : m < K) (t : ℕ),
            (ctr t).val = m →
            ∃ t' ≥ t, (ctr t').val = m + 1 := by
          intro m hm t hctr_t_eq_m
          -- Get the list element at position m
          have hm_lt_len : m < (Formula.untlFinset φ).toList.length := by
            rw [Finset.length_toList]
            exact hm
          let χ_m := (Formula.untlFinset φ).toList.get ⟨m, hm_lt_len⟩
          -- χ_m ∈ untlSubformulas φ
          have hχ_m_mem : χ_m ∈ Formula.untlSubformulas φ := by
            have hχ_in_finset : χ_m ∈ Formula.untlFinset φ :=
              Finset.mem_toList.mp (List.get_mem _ ⟨m, hm_lt_len⟩)
            rwa [Formula.untlFinset, Set.Finite.mem_toFinset] at hχ_in_finset
          -- B visits acc(χ_m) infinitely often
          have hχ_m_acc := hgnbaAcc χ_m hχ_m_mem
          rw [Filter.frequently_atTop] at hχ_m_acc
          -- Among those visits ≥ t, find the FIRST one (using Nat.find)
          obtain ⟨t_acc, ht_acc_ge, ht_acc_mem⟩ := hχ_m_acc t
          -- Key: ctr t_acc = m (counter hasn't advanced past m before the first visit to acc_m)
          -- We prove: ctr stays at m from t until the first visit to acc(χ_m) after t.
          -- Define: P s = s ≥ t ∧ B s ∈ gnbaAcceptSet φ χ_m
          have hP_inh : ∃ s, s ≥ t ∧ B s ∈ Formula.gnbaAcceptSet φ χ_m :=
            ⟨t_acc, ht_acc_ge, ht_acc_mem⟩
          -- Use Nat.find to get the first such s ≥ t
          -- We use a slightly different characterization: find the min s with s ≥ t ∧ B s ∈ acc
          -- First prove that ∀ s < t_first, s ≥ t → B s ∉ acc(χ_m) is false
          -- Instead: first visit to acc(χ_m) after t means ctr = m there
          -- Sub-claim: ctr s = m for all s ∈ [t, first_visit)
          -- and at first_visit, ctr = m, so ctr (first_visit+1) = m+1
          -- Define first_visit := Nat.find hP_inh
          -- But Nat.find needs (s ≥ t ∧ B s ∈ acc) to be decidable
          -- Use a different approach: induction on (t_acc - t)
          -- Claim: ctr t_acc = m follows from (1) ctr t = m, (2) counter is non-decreasing
          -- on [t, t_acc] within the [0, K] range, (3) counter only advances past m when
          -- B visits acc(χ_m), (4) t_acc is the first such visit.
          -- Instead of finding first visit, just use t_acc directly:
          -- We show ctr s ≤ m for all s ∈ [t, t_acc] → ctr t_acc = m → advance at t_acc.
          -- Actually, let's use a simpler argument via the fact that the counter only jumps
          -- at acc visits: if (ctr t_acc > m), then the counter advanced from m to m+1 at
          -- some step s' ∈ [t, t_acc), which required B s' ∈ acc(χ_m) with ctr s' = m.
          -- But t_acc was supposed to be the first visit! So we need minimality.
          -- Use the minimal such t_acc:
          have hP_min_exists :
              ∃ t_min : ℕ, t_min ≥ t ∧ B t_min ∈ Formula.gnbaAcceptSet φ χ_m := by
            exact ⟨t_acc, ht_acc_ge, ht_acc_mem⟩
          -- Lean doesn't automatically give a Decidable instance for B s ∈ gnbaAcceptSet
          -- So we use a different approach: prove ctr t_acc ≥ m and ctr t_acc ≤ m
          -- Lower bound: ctr s ≥ m for all s ≥ t (as long as counter hasn't reset)
          -- This is not true in general (counter resets from K to 0).
          -- Better: find the period where ctr ≥ m holds.
          -- Actually the simplest correct argument:
          -- From ctr t = m and the counter transition rules:
          -- If ctr s = m and B s ∉ acc(χ_m): ctr (s+1) = m (stays)
          -- If ctr s = m and B s ∈ acc(χ_m): ctr (s+1) = m+1 (advances)
          -- If ctr s > m (< K): ctr (s+1) ∈ {ctr s, ctr s + 1} ≥ m+1 > m
          -- If ctr s = K: ctr (s+1) = 0 ≤ m (possible reset)
          -- So we can't say ctr t_acc = m without knowing ctr didn't reset.
          -- For the acceptance proof, we just need SOME t' with ctr t' = m+1.
          -- Key insight: use t as the starting witness. If B t ∈ acc(χ_m): then ctr (t+1) = m+1.
          -- If not: ctr (t+1) = m. Then recurse.
          -- This gives an induction on the "distance" until first acc visit.
          -- But this doesn't terminate definitionally.
          -- CORRECT APPROACH: Induction on (t_acc - t).
          -- We prove: ∀ d, ctr t = m → B s ∉ acc(χ_m) for all s ∈ [t, t+d) →
          --           ctr (t+d) = m.
          have hctr_stays : ∀ d : ℕ,
              (∀ s, s < d → B (t + s) ∉ Formula.gnbaAcceptSet φ χ_m) →
              (ctr (t + d)).val = m := by
            intro d
            induction d with
            | zero => intro _; simpa using hctr_t_eq_m
            | succ d' ihd' =>
              intro hno_acc
              have ihd'_hyp : ∀ s, s < d' → B (t + s) ∉ Formula.gnbaAcceptSet φ χ_m :=
                fun s hs => hno_acc s (Nat.lt_succ_of_lt hs)
              have hctr_d' : (ctr (t + d')).val = m := ihd' ihd'_hyp
              -- Now: ctr (t + d' + 1) = ?
              -- B (t + d') ∉ acc(χ_m) by hno_acc d' (lt_succ_self d')
              have hno_acc_d' : B (t + d') ∉ Formula.gnbaAcceptSet φ χ_m :=
                hno_acc d' (Nat.lt_succ_self d')
              -- Counter transition at (t + d'):
              -- ctr (t + d' + 1) obtained from step function at n = (t+d'), prev = ctr (t+d')
              change (ctr (t + d' + 1)).val = m
              rw [show t + d' + 1 = t + (d' + 1) from by omega]
              -- The counter at t + d' has val = m, and since B(t+d') ∉ acc(χ_m),
              -- the counter stays at m.
              -- We need: (ctr (t + d' + 1)).val = m
              -- Since ctr is defined as step(t+d')(ctr(t+d')), and ctr(t+d').val = m < K,
              -- and χ_m = list.get[m], B(t+d') ∉ acc(χ_m): counter stays.
              -- This is definitional but we need to unfold the ctr def.
              -- Use the same counter transition structure as in hss_trans:
              -- The counter at (t+d'+1) satisfies: if ctr(t+d').val < K and
              -- B(t+d') ∉ acc(χ_m), then ctr(t+d'+1) = ctr(t+d').
              have hctr_stay_step : (ctr (t + d' + 1)).val = (ctr (t + d')).val := by
                have hfin_eq : ctr (t + d') = ⟨m, by omega⟩ := Fin.ext hctr_d'
                change (Formula.gnbaCtrStep φ B (t + d') (ctr (t + d'))).val = _
                rw [hfin_eq, gnbaCtrStep_not_mem φ B (t + d') ⟨m, by omega⟩ hK hm hno_acc_d']
              rw [show t + (d' + 1) = t + d' + 1 from by omega]
              omega
          -- Now use Nat.find to get the first t_acc ≥ t with B t_acc ∈ acc(χ_m)
          -- We know t_acc exists: ⟨t_acc, ht_acc_ge, ht_acc_mem⟩
          -- Let d_acc = t_acc - t; then B (t + d_acc) ∈ acc(χ_m)
          set d_acc := t_acc - t with hd_acc_def
          have ht_acc_eq : t_acc = t + d_acc := by omega
          -- We want the minimal d with B(t+d) ∈ acc(χ_m)
          -- Use hctr_stays with the minimal d:
          -- For ANY d_acc witnessing B(t+d_acc) ∈ acc, we can find d_min ≤ d_acc with
          -- B(t+d_min) ∈ acc(χ_m) and ∀ s < d_min, B(t+s) ∉ acc(χ_m).
          -- Then ctr(t+d_min) = m by hctr_stays, so ctr(t+d_min+1) = m+1.
          -- Get the minimal d:
          have hd_P : ∃ d : ℕ, d ≤ d_acc ∧ B (t + d) ∈ Formula.gnbaAcceptSet φ χ_m :=
            ⟨d_acc, le_refl _, ht_acc_eq ▸ ht_acc_mem⟩
          haveI hd_P_dec :
              DecidablePred (fun d : ℕ => d ≤ d_acc ∧ B (t + d) ∈ Formula.gnbaAcceptSet φ χ_m) :=
            fun d => Classical.propDecidable _
          let d_min := Nat.find hd_P
          have hd_min_spec := Nat.find_spec hd_P
          have hd_min_bound : d_min ≤ d_acc := hd_min_spec.1
          have hd_min_mem : B (t + d_min) ∈ Formula.gnbaAcceptSet φ χ_m := hd_min_spec.2
          have hd_min_minimal :
              ∀ d' < d_min, ¬(d' ≤ d_acc ∧ B (t + d') ∈ Formula.gnbaAcceptSet φ χ_m) :=
            fun d' hd' => Nat.find_min hd_P hd'
          -- At t + d_min, ctr = m (by minimality: no earlier visit to acc(χ_m))
          have hctr_t_d_min : (ctr (t + d_min)).val = m := by
            apply hctr_stays
            intro s hs hmem
            exact absurd
              ⟨Nat.le_of_lt_succ
                (Nat.lt_succ_of_le (le_trans (Nat.le_of_lt hs) hd_min_bound)), hmem⟩
              (hd_min_minimal s hs)
          -- At t + d_min, B(t+d_min) ∈ acc(χ_m), so ctr(t+d_min+1) = m+1
          have hctr_advance : (ctr (t + d_min + 1)).val = m + 1 := by
            have hfin_eq : ctr (t + d_min) = ⟨m, by omega⟩ := Fin.ext hctr_t_d_min
            change (Formula.gnbaCtrStep φ B (t + d_min) (ctr (t + d_min))).val = m + 1
            rw [hfin_eq, gnbaCtrStep_mem φ B (t + d_min) ⟨m, by omega⟩ hK hm hd_min_mem]
          exact ⟨t + d_min + 1, by omega, hctr_advance⟩
        -- Now use hprogress to iterate K times from ctr = 0 to ctr = K
        -- Claim: from any t with ctr t = m, ∃ t' ≥ t with ctr t' = K.
        have hreach_K : ∀ (r : ℕ) (hr : r ≤ K) (t : ℕ),
            (ctr t).val = K - r →
            ∃ t' ≥ t, (ctr t').val = K := by
          intro r
          induction r with
          | zero =>
            intro _ t hctr
            exact ⟨t, le_refl _, by omega⟩
          | succ r' ihr' =>
            intro hr t hctr
            -- From ctr t = K - (r'+1) = K - r' - 1 < K
            have hval : (ctr t).val = K - r' - 1 := by omega
            have hlt : K - r' - 1 < K := by omega
            have hval' : (ctr t).val = K - r' - 1 := hval
            -- Use hprogress to advance to K - r' - 1 + 1 = K - r'
            obtain ⟨t', ht'_ge, ht'_val⟩ := hprogress (K - r' - 1) hlt t hval'
            -- Now ctr t' = K - r' = K - r' - 1 + 1
            have hctr_t' : (ctr t').val = K - r' := by omega
            -- Apply IH with r = r'
            obtain ⟨t'', ht''_ge, ht''_val⟩ := ihr' (Nat.le_of_succ_le hr) t' hctr_t'
            exact ⟨t'', le_trans ht'_ge ht''_ge, ht''_val⟩
        -- Now prove the frequently_atTop condition
        rw [Filter.frequently_atTop]
        intro N
        -- ctr 0 = 0 (start)
        -- We need: starting from N, find k ≥ N with ctr k = K
        -- Use hgnbaAcc to find a time t₀ ≥ N, then apply hreach_K from t₀ with ctr t₀ = 0
        -- But ctr at N may not be 0. We use hreach_K from N directly.
        -- Case: ctr N = K? Then reset to 0, then apply hreach_K from N+1 with ctr(N+1) = 0.
        -- Case: ctr N = m ≤ K? Apply hreach_K.
        have hctr_val_le_K : (ctr N).val ≤ K := Nat.lt_succ_iff.mp (ctr N).isLt
        -- Apply hreach_K with r = K - (ctr N).val
        obtain ⟨t', ht'_ge, ht'_val⟩ := hreach_K (K - (ctr N).val) (by omega) N (by omega)
        exact ⟨t', ht'_ge, ht'_val⟩
    exact ⟨ss, ⟨hss_start, hss_trans⟩, hss_acc⟩

end Cslib.Logic.LTL

end
