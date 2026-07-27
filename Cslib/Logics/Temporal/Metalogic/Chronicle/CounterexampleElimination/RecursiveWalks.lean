/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination.Elimination

/-! # Recursive Walks for C5 Forward and Backward Counterexample Elimination

The recursive walk functions `c5ForwardWalk` and `c5BackwardWalk` that eliminate
C5/C5' counterexamples by inserting new witness points.
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic

/-! ## Recursive Walks -/

/-- Recursive walk that eliminates a C5 forward (Until) counterexample by inserting a new
witness point. -/
noncomputable def c5ForwardWalk
    (χ : Chronicle Atom) (h_c0 : χ.c0) (h_c2' : χ.c2')
    (ξ η : Formula Atom) (pt : Rat)
    (h_start_mem : pt ∈ χ.dom)
    (h_until_start : (ξ U η) ∈ χ.f pt)
    (h_no_wit : ¬∃ y ∈ χ.dom, pt < y ∧ η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → pt ≤ a → b ≤ y → ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, pt < w → w < y → ξ ∈ χ.f w)) :
    C5ForwardWalkResult χ ξ η pt := by
  -- Set up domain facts
  have h_dom_ne : χ.dom.Nonempty := ⟨pt, h_start_mem⟩
  set max_old := χ.dom.max' h_dom_ne with max_old_def
  have h_max_mem : max_old ∈ χ.dom := Finset.max'_mem χ.dom h_dom_ne
  have h_max_le : ∀ s ∈ χ.dom, s ≤ max_old := fun s hs => Finset.le_max' χ.dom s hs
  have h_mcs_start := h_c0 pt h_start_mem
  by_cases h_eq_max : pt = max_old
  · -- **BASE CASE**: pt = max(dom). Insert witness y beyond max_old.
    have h_fresh := exists_rat_gt_finset χ.dom
    let y := h_fresh.choose
    have hy_gt : ∀ s ∈ χ.dom, s < y := h_fresh.choose_spec.1
    have hy_notin : y ∉ χ.dom := h_fresh.choose_spec.2
    have h_l24 := lemma24WithGuard h_mcs_start ξ η h_until_start
    let B := h_l24.choose
    let C := h_l24.choose_spec.choose
    have h_l24_prop := h_l24.choose_spec.choose_spec
    have h_C_mcs : Temporal.SetMaximalConsistent C := h_l24_prop.1
    have h_η_C : η ∈ C := h_l24_prop.2.1
    have h_ξ_B : ξ ∈ B := h_l24_prop.2.2.2.2
    have h_r3m : BurgessR3Maximal (χ.f pt) B C := h_l24_prop.2.2.2.1
    have h_max_lt_y : max_old < y := hy_gt max_old h_max_mem
    let g' := fun a b =>
      if a = max_old ∧ b = y then B
      else χ.g a b
    let χ' : Chronicle Atom := ⟨fun q => if q = y then C else χ.f q, g', insert y χ.dom⟩
    have h_c2'_new : χ'.c2' := by
      intro a b h_adj_new
      obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
      simp only [χ', Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd hab (lt_irrefl _)
      · exact absurd hab (not_lt.mpr (le_of_lt (hy_gt b hb)))
      · have ha_eq : a = max_old := by
          by_contra ha_ne
          have ha_le : a ≤ max_old := h_max_le a ha
          have ha_lt : a < max_old := lt_of_le_of_ne ha_le ha_ne
          exact h_no_between max_old (Finset.mem_insert_of_mem h_max_mem) ⟨ha_lt, h_max_lt_y⟩
        subst ha_eq
        change BurgessR3Maximal
          (if max_old = y then C else χ.f max_old)
          (g' max_old y)
          (if y = y then C else χ.f y)
        have hmax_ne_y : max_old ≠ y := ne_of_lt h_max_lt_y
        simp only [hmax_ne_y, ite_false, ite_true, g']
        simp only [and_self, ite_true]
        rw [← h_eq_max]; exact h_r3m
      · have ha_ne : a ≠ y := fun h => hy_notin (h ▸ ha)
        have hb_ne : b ≠ y := fun h => hy_notin (h ▸ hb)
        change BurgessR3Maximal
          (if a = y then C else χ.f a)
          (g' a b)
          (if b = y then C else χ.f b)
        simp only [ha_ne, hb_ne, ite_false]
        change BurgessR3Maximal (χ.f a)
          (if a = max_old ∧ b = y then B else χ.g a b) (χ.f b)
        rw [if_neg (fun ⟨_, hby⟩ => hb_ne hby)]
        have h_adj_old : Adjacent χ.dom a b := by
          refine ⟨ha, hb, hab, ?_⟩
          intro u hu ⟨hau, hub⟩
          exact h_no_between u (Finset.mem_insert_of_mem hu) ⟨hau, hub⟩
        exact h_c2' a b h_adj_old
    exact { val := χ'
            dom_sub := Finset.subset_insert y χ.dom
            c0 := by
              intro q hq
              change Temporal.SetMaximalConsistent (if q = y then C else χ.f q)
              change q ∈ insert y χ.dom at hq
              simp only [Finset.mem_insert] at hq
              rcases hq with rfl | hq
              · simp only [ite_true]; exact h_C_mcs
              · have h_ne : q ≠ y := fun h => hy_notin (h ▸ hq)
                simp only [h_ne, ite_false]; exact h_c0 q hq
            c2' := h_c2'_new
            f_agrees := by
              intro x hx
              have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
              exact if_neg h_ne
            g_agrees := by
              intro a b ha hb
              change g' a b = χ.g a b
              simp only [g']
              have hb_ne : b ≠ y := fun h => hy_notin (h ▸ hb)
              simp only [hb_ne, and_false, ite_false]
            witness := y
            witness_mem := Finset.mem_insert_self y χ.dom
            witness_gt := hy_gt pt h_start_mem
            witness_event := by simp only [χ', ite_true]; exact h_η_C
            witness_guard := by
              intro a b h_adj_ab h_le_a h_le_b
              have ha_dom : a ∈ insert y χ.dom := h_adj_ab.1
              have hb_dom : b ∈ insert y χ.dom := h_adj_ab.2.1
              simp only [Finset.mem_insert] at ha_dom hb_dom
              have hb_eq : b = y := by
                rcases hb_dom with rfl | hb_old
                · rfl
                · have : b ≤ max_old := h_max_le b hb_old
                  linarith [h_adj_ab.2.2.1]
              subst hb_eq
              have ha_ne_y : a ≠ y := ne_of_lt h_adj_ab.2.2.1
              have ha_old : a ∈ χ.dom := by
                rcases ha_dom with rfl | h
                · exact absurd rfl ha_ne_y
                · exact h
              have ha_eq : a = max_old := by
                have ha_le_max : a ≤ max_old := h_max_le a ha_old
                have hmax_le_a : max_old ≤ a := by
                  by_contra hlt; push Not at hlt
                  exact h_adj_ab.2.2.2 max_old
                    (Finset.mem_insert_of_mem h_max_mem) ⟨hlt, h_max_lt_y⟩
                exact le_antisymm ha_le_max hmax_le_a
              subst ha_eq
              change ξ ∈ g' max_old y
              simp only [g', and_self, ite_true]
              exact h_ξ_B
            g_sub_f_insert := by
              intro a b h_adj w hw hw_not haw hwb
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact absurd hwb (not_lt.mpr (le_of_lt (hy_gt b h_adj.2.1)))
              · exact absurd hw hw_not
            g_sub_g_new := by
              intro a b h_adj w hw hw_not haw hwb
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact absurd hwb (not_lt.mpr (le_of_lt (hy_gt b h_adj.2.1)))
              · exact absurd hw hw_not
            dom_new_unique := by
              intro u v hu hu_not hv hv_not
              simp only [χ', Finset.mem_insert] at hu hv
              rcases hu with rfl | hu <;> rcases hv with rfl | hv
              · rfl
              · exact absurd hv hv_not
              · exact absurd hu hu_not
              · exact absurd hu hu_not
            new_point_after := by
              intro w hw hw_not
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact hy_gt pt h_start_mem
              · exact absurd hw hw_not
            domain_guard := by
              -- Base case: pt = max(dom), witness = y > max(dom).
              -- No w ∈ χ.dom with pt < w exists (pt is max).
              intro w hw hsw _
              exact absurd (h_max_le w hw) (not_le.mpr (h_eq_max ▸ hsw))
            witness_not_old := hy_notin }
  · -- **RECURSIVE CASE**: pt < max_old. Find successor x'.
    have h_start_lt_max : pt < max_old := lt_of_le_of_ne (h_max_le pt h_start_mem) h_eq_max
    let T_succ := χ.dom.filter (fun v => v > pt)
    have hT_ne : T_succ.Nonempty :=
      ⟨max_old, Finset.mem_filter.mpr ⟨h_max_mem, h_start_lt_max⟩⟩
    let x' := T_succ.min' hT_ne
    have hx'_mem_T := Finset.min'_mem T_succ hT_ne
    have hx'_dom : x' ∈ χ.dom := (Finset.mem_filter.mp hx'_mem_T).1
    have hstart_lt_x' : pt < x' := (Finset.mem_filter.mp hx'_mem_T).2
    have h_adj_sx' : Adjacent χ.dom pt x' := by
      refine ⟨h_start_mem, hx'_dom, hstart_lt_x', ?_⟩
      intro u hu ⟨hsu, hux⟩
      have hu_T : u ∈ T_succ := Finset.mem_filter.mpr ⟨hu, hsu⟩
      have := Finset.min'_le T_succ u hu_T
      linarith
    have h_mcs_x' := h_c0 x' hx'_dom
    -- Derive: xi ∈ g(pt, x') → eta ∉ f(x')
    have h_guard_implies_no_event : ξ ∈ χ.g pt x' → η ∉ χ.f x' :=
      fun h_guard h_event => h_no_wit ⟨x', hx'_dom, hstart_lt_x', h_event,
        ⟨fun a b h_adj_ab h_le_a h_le_b => by
          have ha_eq : a = pt := by
            by_contra ha_ne
            have ha_gt : pt < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
            exact h_adj_sx'.2.2.2 a h_adj_ab.1 ⟨ha_gt, lt_of_lt_of_le h_adj_ab.2.2.1 h_le_b⟩
          have hb_eq : b = x' := by
            rw [ha_eq] at h_adj_ab
            by_contra hb_ne
            have hb_lt : b < x' := lt_of_le_of_ne h_le_b hb_ne
            exact h_adj_sx'.2.2.2 b h_adj_ab.2.1 ⟨h_adj_ab.2.2.1, hb_lt⟩
          rw [ha_eq, hb_eq]; exact h_guard,
        fun w hw hsw hwx' => absurd ⟨hsw, hwx'⟩ (h_adj_sx'.2.2.2 w hw)⟩⟩
    -- Get BurgessR3Maximal facts for (pt, x')
    have h_r3m_adj := h_c2' pt x' h_adj_sx'
    have h_gc_adj := BurgessR3Maximal_g_content_sub h_r3m_adj h_mcs_start h_mcs_x'
    -- Check condition (i): conj ∈ f(x') AND ξ ∈ g(pt, x')
    by_cases h_cond_i : Formula.and ξ (Formula.untl ξ η) ∈ χ.f x' ∧ ξ ∈ χ.g pt x'
    · -- **Condition (i)**: recurse at x'
      have h_untl_x' : (ξ U η) ∈ χ.f x' :=
        conj_right_mcs h_mcs_x' ξ (Formula.untl ξ η) h_cond_i.1
      -- Derive: h_no_wit at x'
      have h_no_wit_x' : ¬∃ y ∈ χ.dom, x' < y ∧ η ∈ χ.f y ∧
          (∀ a b, Adjacent χ.dom a b → x' ≤ a → b ≤ y → ξ ∈ χ.g a b) ∧
          (∀ w ∈ χ.dom, x' < w → w < y → ξ ∈ χ.f w) := by
        intro ⟨y, hy_dom, hx'y, hη_y, h_guard_y, h_dom_guard_y⟩
        exact h_no_wit ⟨y, hy_dom, lt_trans hstart_lt_x' hx'y, hη_y,
          ⟨fun a b h_adj_ab h_le_a h_le_b => by
            by_cases h_a_lt_x' : a < x'
            · -- a < x', so a = pt and b = x' (since x' is successor of pt)
              have ha_eq : a = pt := by
                have : pt ≤ a := h_le_a
                by_contra ha_ne
                have ha_gt : pt < a := lt_of_le_of_ne this (Ne.symm ha_ne)
                exact h_adj_sx'.2.2.2 a h_adj_ab.1 ⟨ha_gt, h_a_lt_x'⟩
              have hb_eq : b = x' := by
                rw [ha_eq] at h_adj_ab
                have hb_le : b ≤ x' := by
                  by_contra hgt; push Not at hgt
                  exact h_adj_ab.2.2.2 x' hx'_dom ⟨hstart_lt_x', hgt⟩
                exact le_antisymm hb_le (by
                  by_contra hlt; push Not at hlt
                  exact h_adj_sx'.2.2.2 b h_adj_ab.2.1 ⟨h_adj_ab.2.2.1, hlt⟩)
              rw [ha_eq, hb_eq]; exact h_cond_i.2
            · -- a ≥ x'
              push Not at h_a_lt_x'
              exact h_guard_y a b h_adj_ab h_a_lt_x' h_le_b,
          fun w hw hsw hwy => by
            -- w ∈ χ.dom with pt < w < y. Case split on w vs x'.
            rcases lt_or_eq_of_le (not_lt.mp fun h =>
              h_adj_sx'.2.2.2 w hw ⟨hsw, h⟩) with hwx' | hwx'
            · -- w > x': use h_dom_guard_y from hypothesis
              exact h_dom_guard_y w hw hwx' hwy
            · -- w = x': ξ ∈ f(x') from condition (i) via conj_left_mcs
              rw [← hwx']
              exact conj_left_mcs h_mcs_x' ξ (Formula.untl ξ η) h_cond_i.1⟩⟩
      -- Termination: (dom.filter (· > x')).card < (dom.filter (· > pt)).card
      have h_term : (χ.dom.filter (fun v => v > x')).card <
          (χ.dom.filter (fun v => v > pt)).card := by
        apply Finset.card_lt_card
        constructor
        · intro v hv
          have hv_dom := (Finset.mem_filter.mp hv).1
          have hv_gt : v > x' := (Finset.mem_filter.mp hv).2
          exact Finset.mem_filter.mpr ⟨hv_dom, lt_trans hstart_lt_x' hv_gt⟩
        · simp only [Finset.not_subset]
          exact ⟨x', Finset.mem_filter.mpr ⟨hx'_dom, hstart_lt_x'⟩,
            fun h => absurd (Finset.mem_filter.mp h).2 (lt_irrefl _)⟩
      -- Recurse
      have r := c5ForwardWalk χ h_c0 h_c2' ξ η x' hx'_dom h_untl_x' h_no_wit_x'
      -- Compose: guard at (pt, x') from condition (i) + recursive guard from x'
      exact { val := r.val
              dom_sub := r.dom_sub
              c0 := r.c0
              c2' := r.c2'
              f_agrees := r.f_agrees
              g_agrees := r.g_agrees
              witness := r.witness
              witness_mem := r.witness_mem
              witness_gt := lt_trans hstart_lt_x' r.witness_gt
              witness_event := r.witness_event
              witness_guard := by
                intro a b h_adj_ab h_le_a h_le_b
                by_cases h_a_ge_x' : x' ≤ a
                · exact r.witness_guard a b h_adj_ab h_a_ge_x' h_le_b
                · -- a < x'. Show a = pt and b = x', then use condition (i) guard.
                  push Not at h_a_ge_x'
                  have ha_eq : a = pt := by
                    by_contra ha_ne
                    have ha_gt : pt < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
                    by_cases ha_old : a ∈ χ.dom
                    · exact h_adj_sx'.2.2.2 a ha_old ⟨ha_gt, h_a_ge_x'⟩
                    · -- a is new from recursion at x', so x' < a by new_point_after.
                      -- Contradicts a < x'.
                      exact absurd (r.new_point_after a h_adj_ab.1 ha_old)
                        (not_lt.mpr (le_of_lt h_a_ge_x'))
                  subst ha_eq
                  -- b must be x': x' in val.dom, pt < x', no new point between
                  have hb_eq : b = x' := by
                    have hx'_val : x' ∈ r.val.dom := r.dom_sub hx'_dom
                    by_contra hb_ne
                    rcases lt_or_gt_of_ne hb_ne with hb_lt | hb_gt
                    · by_cases hb_old : b ∈ χ.dom
                      · exact h_adj_sx'.2.2.2 b hb_old ⟨h_adj_ab.2.2.1, hb_lt⟩
                      · exact absurd (r.new_point_after b h_adj_ab.2.1 hb_old)
                          (not_lt.mpr (le_of_lt hb_lt))
                    · exact h_adj_ab.2.2.2 x' hx'_val ⟨hstart_lt_x', hb_gt⟩
                  subst hb_eq
                  rw [r.g_agrees _ x' h_start_mem hx'_dom]
                  exact h_cond_i.2
              g_sub_f_insert := r.g_sub_f_insert
              g_sub_g_new := r.g_sub_g_new
              dom_new_unique := r.dom_new_unique
              new_point_after := by
                intro w hw hw_not
                exact lt_trans hstart_lt_x' (r.new_point_after w hw hw_not)
              domain_guard := by
                -- Condition (i): ξ ∧ (ξ U η) ∈ f(x'), so ξ ∈ f(x') by conj_left_mcs.
                -- For w between start and x': vacuous (x' is immediate successor).
                -- For w between x' and witness: from recursive domain_guard.
                intro w hw hsw hwr
                rcases lt_or_eq_of_le (not_lt.mp fun h =>
                  h_adj_sx'.2.2.2 w hw ⟨hsw, h⟩) with hwx' | hwx'
                · -- w > x', use recursive domain_guard
                  exact r.domain_guard w hw hwx' hwr
                · -- w = x', use condition (i)
                  rw [← hwx', r.f_agrees x' hx'_dom]
                  exact conj_left_mcs h_mcs_x' ξ (Formula.untl ξ η) h_cond_i.1
              witness_not_old := r.witness_not_old }
    · -- **Not condition (i)**: split at (pt, x')
      have h_split_result : ∃ B' D B'' : Set (Formula Atom),
          BurgessR3Maximal (χ.f pt) B' D ∧
          BurgessR3Maximal D B'' (χ.f x') ∧
          Temporal.SetMaximalConsistent D ∧
          η ∈ D ∧
          χ.g pt x' ⊆ D ∧
          χ.g pt x' ⊆ B' ∧
          χ.g pt x' ⊆ B'' ∧
          ξ ∈ B' := by
        by_cases h_eta_g : η ∈ χ.g pt x'
        · by_cases h_xi_g : ξ ∈ χ.g pt x'
          · -- η ∈ g, ξ ∈ g: use lemma_2_8 (avoids needing SetConsistent g)
            -- Derive h_neg_disj: ¬(η ∨ (ξ ∧ U(ξ,η))) ∈ f(x')
            have h_conj_not_f : Formula.and ξ (Formula.untl ξ η) ∉ χ.f x' :=
              fun h => h_cond_i ⟨h, h_xi_g⟩
            have h_neg_disj :
                (Formula.or η (Formula.and ξ (Formula.untl ξ η))).neg ∈ χ.f x' := by
              have h1 : (¬η) ∈ χ.f x' := by
                rcases temporal_negation_complete h_mcs_x' η with h | h
                · exact absurd h (h_guard_implies_no_event h_xi_g)
                · exact h
              have h2 : (Formula.and ξ (Formula.untl ξ η)).neg ∈ χ.f x' := by
                rcases temporal_negation_complete h_mcs_x'
                  (Formula.and ξ (Formula.untl ξ η)) with h | h
                · exact absurd h h_conj_not_f
                · exact h
              exact temporal_implication_property h_mcs_x'
                (theoremInMcs h_mcs_x'
                  (demorganDisjNegBackward η
                    (Formula.and ξ (Formula.untl ξ η))))
                (conj_mcs h_mcs_x' η.neg (Formula.and ξ (Formula.untl ξ η)).neg h1 h2)
            obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
              lemma_2_8 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η
                h_until_start h_neg_disj
            exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB' h_xi_g⟩
          · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B'⟩ :=
              lemma_2_7 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η
                h_until_start h_xi_g
            exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B'⟩
        · by_cases h_eta_neg_g : (¬η) ∈ χ.g pt x'
          · by_cases h_xi_g : ξ ∈ χ.g pt x'
            · by_cases h_conj_g : Formula.and ξ (Formula.untl ξ η) ∈ χ.g pt x'
              · -- conj in g but not-condition(i): conj not in f(x')
                have h_conj_not_f : Formula.and ξ (Formula.untl ξ η) ∉ χ.f x' :=
                  fun h => h_cond_i ⟨h, h_xi_g⟩
                have h_neg_disj :
                    (Formula.or η (Formula.and ξ (Formula.untl ξ η))).neg ∈ χ.f x' := by
                  have h1 : (¬η) ∈ χ.f x' := by
                    rcases temporal_negation_complete h_mcs_x' η with h | h
                    · exact absurd h (h_guard_implies_no_event h_xi_g)
                    · exact h
                  have h2 : (Formula.and ξ (Formula.untl ξ η)).neg ∈ χ.f x' := by
                    rcases temporal_negation_complete h_mcs_x'
                      (Formula.and ξ (Formula.untl ξ η)) with h | h
                    · exact absurd h h_conj_not_f
                    · exact h
                  exact temporal_implication_property h_mcs_x'
                    (theoremInMcs h_mcs_x'
                      (demorganDisjNegBackward η
                        (Formula.and ξ (Formula.untl ξ η))))
                    (conj_mcs h_mcs_x' η.neg (Formula.and ξ (Formula.untl ξ η)).neg h1 h2)
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
                  lemma_2_8 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η
                    h_until_start h_neg_disj
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB' h_xi_g⟩
              · have h_bx5 := self_accum_until_mcs h_mcs_start ξ η h_until_start
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, hBB', h_B_sub_D, hBB'', _⟩ :=
                  lemma_2_7 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj
                    (Formula.and ξ (Formula.untl ξ η)) η h_bx5 h_conj_g
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB' h_xi_g⟩
            · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B'⟩ :=
                lemma_2_7 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η
                  h_until_start h_xi_g
              exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B'⟩
          · by_cases h_xi_g2 : ξ ∈ χ.g pt x'
            · have h_sp := lemma_2_6_splitting h_mcs_start h_mcs_x' h_r3m_adj
                η.neg h_eta_neg_g
              obtain ⟨B', D, B'', hB', hB'', hD_mcs, h_dne_D, h_B_sub_D, hBB', hBB''⟩ := h_sp
              exact ⟨B', D, B'', hB', hB'', hD_mcs,
                temporal_implication_property hD_mcs
                  (theoremInMcs hD_mcs (doubleNegation η)) h_dne_D,
                h_B_sub_D, hBB', hBB'', hBB' h_xi_g2⟩
            · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B'⟩ :=
                lemma_2_7 h_mcs_start h_mcs_x' h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η
                  h_until_start h_xi_g2
              exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B'⟩
      let B' := h_split_result.choose
      let D := h_split_result.choose_spec.choose
      let B'' := h_split_result.choose_spec.choose_spec.choose
      have h_split_prop := h_split_result.choose_spec.choose_spec.choose_spec
      have h_B'_max : BurgessR3Maximal (χ.f pt) B' D := h_split_prop.1
      have h_B''_max : BurgessR3Maximal D B'' (χ.f x') := h_split_prop.2.1
      have h_D_mcs : Temporal.SetMaximalConsistent D := h_split_prop.2.2.1
      have h_eta_D : η ∈ D := h_split_prop.2.2.2.1
      have h_g_sub_D : χ.g pt x' ⊆ D := h_split_prop.2.2.2.2.1
      have h_g_sub_B' : χ.g pt x' ⊆ B' := h_split_prop.2.2.2.2.2.1
      have h_g_sub_B'' : χ.g pt x' ⊆ B'' := h_split_prop.2.2.2.2.2.2.1
      have h_xi_B' : ξ ∈ B' := h_split_prop.2.2.2.2.2.2.2
      set z := (pt + x') / 2 with hz_def
      have hz_lt_x' : z < x' := by linarith
      have hstart_lt_z : pt < z := by linarith
      have hz_notin : z ∉ χ.dom := by
        intro h_mem_z; exact h_adj_sx'.2.2.2 z h_mem_z ⟨hstart_lt_z, hz_lt_x'⟩
      let g' := fun a b =>
        if a = pt ∧ b = z then B'
        else if a = z ∧ b = x' then B''
        else χ.g a b
      let val : Chronicle Atom := ⟨fun q => if q = z then D else χ.f q, g', insert z χ.dom⟩
      have h_c2'_new : val.c2' := by
        intro a b h_adj_new
        obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
        simp only [val, Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd hab (lt_irrefl _)
        · have hb_eq : b = x' := by
            by_contra hb_ne
            have hb_ge : x' ≤ b := by
              by_contra hlt; push Not at hlt
              exact h_adj_sx'.2.2.2 b hb ⟨lt_trans hstart_lt_z hab, hlt⟩
            exact h_no_between x' (Finset.mem_insert_of_mem hx'_dom)
              ⟨hz_lt_x', lt_of_le_of_ne hb_ge (Ne.symm hb_ne)⟩
          subst hb_eq
          have hz_ne_pt : z ≠ pt := ne_of_gt hstart_lt_z
          have hx'_ne_z : x' ≠ z := ne_of_gt hz_lt_x'
          simp only [val, g', if_true, hx'_ne_z, if_false, hz_ne_pt, and_self, if_true]
          exact h_B''_max
        · -- a is in old domain, a < z. Show a = pt.
          have ha_le_start : a ≤ pt := by
            by_contra hgt; push Not at hgt
            exact h_adj_sx'.2.2.2 a ha ⟨hgt, lt_trans hab hz_lt_x'⟩
          have ha_eq_start : a = pt := by
            by_contra ha_ne
            exact h_no_between pt (Finset.mem_insert_of_mem h_start_mem)
              ⟨lt_of_le_of_ne ha_le_start ha_ne, hstart_lt_z⟩
          subst ha_eq_start
          dsimp only [val, g']
          simp only [ne_of_lt hstart_lt_z, if_false, if_true, and_self, if_true]
          exact h_B'_max
        · have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
          have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
          change BurgessR3Maximal (if a = z then D else χ.f a) (g' a b) (if b = z then D else χ.f b)
          simp only [ha_ne, hb_ne, ite_false, g', and_false, false_and]
          exact h_c2' a b
            ⟨ha, hb, hab, fun u hu huab => h_no_between u (Finset.mem_insert_of_mem hu) huab⟩
      exact { val := val
              dom_sub := Finset.subset_insert z χ.dom
              c0 := by
                intro q hq; change Temporal.SetMaximalConsistent (if q = z then D else χ.f q)
                simp only [val, Finset.mem_insert] at hq
                rcases hq with rfl | hq
                · simp only [ite_true]; exact h_D_mcs
                · simp only [show q ≠ z from fun h => hz_notin (h ▸ hq), ite_false]; exact h_c0 q hq
              c2' := h_c2'_new
              f_agrees := by
                intro x hx; dsimp only [val]
                have hx_ne_z : x ≠ z := by intro h; exact hz_notin (h ▸ hx)
                simp only [hx_ne_z, if_false]
              g_agrees := by
                intro a b ha hb; change g' a b = χ.g a b; simp only [g']
                simp only [show a ≠ z from fun h => hz_notin (h ▸ ha),
                  show b ≠ z from fun h => hz_notin (h ▸ hb), false_and, and_false, ite_false]
              witness := z
              witness_mem := Finset.mem_insert_self z χ.dom
              witness_gt := hstart_lt_z
              witness_event := by
                change η ∈ (if z = z then D else χ.f z); simp only [ite_true]; exact h_eta_D
              witness_guard := by
                intro a b h_adj_ab h_le_a h_le_b
                obtain ⟨ha_dom, hb_dom, hab_lt, h_no_btw⟩ := h_adj_ab
                simp only [val, Finset.mem_insert] at ha_dom hb_dom
                have ha_eq : a = pt := by
                  by_contra ha_ne
                  have ha_gt := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
                  rcases ha_dom with rfl | ha_mem
                  · exact absurd h_le_b (not_le.mpr hab_lt)
                  · exact h_adj_sx'.2.2.2 a ha_mem
                      ⟨ha_gt, lt_trans (lt_of_lt_of_le hab_lt h_le_b) hz_lt_x'⟩
                subst ha_eq
                have hb_eq : b = z := by
                  by_contra hb_ne
                  have hb_lt : b < z := lt_of_le_of_ne h_le_b hb_ne
                  rcases hb_dom with rfl | hb_mem
                  · exact absurd (le_refl z) (not_le.mpr hb_lt)
                  · exact h_adj_sx'.2.2.2 b hb_mem ⟨hab_lt, lt_trans hb_lt hz_lt_x'⟩
                subst hb_eq
                dsimp only [val, g']
                simp only [and_self, if_true]; exact h_xi_B'
              g_sub_f_insert := by
                intro a b h_adj w hw hw_not haw hwb
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · change χ.g a b ⊆ (if z = z then D else χ.f z); simp only [ite_true]
                  have hab : a = pt ∧ b = x' := by
                    constructor
                    · by_contra ha_ne
                      rcases lt_or_gt_of_ne ha_ne with h | h
                      · exact h_adj.2.2.2 pt h_start_mem ⟨h, lt_trans hstart_lt_z hwb⟩
                      · exact h_adj_sx'.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_x'⟩
                    · by_contra hb_ne
                      rcases lt_or_gt_of_ne hb_ne with h | h
                      · exact h_adj_sx'.2.2.2 b h_adj.2.1 ⟨lt_trans hstart_lt_z hwb, h⟩
                      · exact h_adj.2.2.2 x' hx'_dom ⟨lt_trans haw hz_lt_x', h⟩
                  rw [hab.1, hab.2]; exact h_g_sub_D
                · exact absurd hw hw_not
              g_sub_g_new := by
                intro a b h_adj w hw hw_not haw hwb
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · have ha_eq : a = pt := by
                    by_contra ha_ne
                    rcases lt_or_gt_of_ne ha_ne with h | h
                    · exact h_adj.2.2.2 pt h_start_mem ⟨h, lt_trans hstart_lt_z hwb⟩
                    · exact h_adj_sx'.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_x'⟩
                  have hb_eq : b = x' := by
                    by_contra hb_ne
                    rcases lt_or_gt_of_ne hb_ne with h | h
                    · exact h_adj_sx'.2.2.2 b h_adj.2.1 ⟨lt_trans hstart_lt_z hwb, h⟩
                    · exact h_adj.2.2.2 x' hx'_dom ⟨lt_trans haw hz_lt_x', h⟩
                  subst ha_eq; subst hb_eq; constructor
                  · dsimp only [val, g']; simp only [and_self, if_true]; exact h_g_sub_B'
                  · dsimp only [val, g']
                    simp only [ne_of_gt hstart_lt_z, false_and, if_false, and_self, if_true]
                    exact h_g_sub_B''
                · exact absurd hw hw_not
              dom_new_unique := by
                intro u v hu hu_not hv hv_not
                simp only [val, Finset.mem_insert] at hu hv
                rcases hu with rfl | hu <;> rcases hv with rfl | hv
                · rfl
                · exact absurd hv hv_not
                · exact absurd hu hu_not
                · exact absurd hu hu_not
              new_point_after := by
                intro w hw hw_not
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · exact hstart_lt_z
                · exact absurd hw hw_not
              domain_guard := by
                -- Split case: witness = z (midpoint between start and x').
                -- No w ∈ χ.dom with start < w < z exists (adjacency of (start, x')).
                intro w hw hsw hwz
                exact absurd ⟨hsw, lt_trans hwz hz_lt_x'⟩
                  (h_adj_sx'.2.2.2 w hw)
              witness_not_old := hz_notin }
termination_by (χ.dom.filter (fun v => v > pt)).card
decreasing_by
  /- Using `have r` (not `let r`) makes the recursive result opaque,
     preventing the WF elaborator from duplicating context with daggers.
     This yields a single WF goal closed by simp_all + exact h_term. -/
  all_goals simp_all only [gt_iff_lt]
  all_goals exact h_term
/-- Recursive walk that eliminates a C5 backward (Since) counterexample by inserting a new
witness point. -/
noncomputable def c5BackwardWalk
    (χ : Chronicle Atom) (h_c0 : χ.c0) (h_c2' : χ.c2')
    (ξ η : Formula Atom) (pt : Rat)
    (h_start_mem : pt ∈ χ.dom)
    (h_since_start : (ξ S η) ∈ χ.f pt)
    (h_no_wit : ¬∃ y ∈ χ.dom, y < pt ∧ η ∈ χ.f y ∧
      (∀ a b, Adjacent χ.dom a b → y ≤ a → b ≤ pt → ξ ∈ χ.g a b) ∧
      (∀ w ∈ χ.dom, y < w → w < pt → ξ ∈ χ.f w)) :
    C5BackwardWalkResult χ ξ η pt := by
  -- Set up domain facts
  have h_dom_ne : χ.dom.Nonempty := ⟨pt, h_start_mem⟩
  set min_old := χ.dom.min' h_dom_ne with min_old_def
  have h_min_mem : min_old ∈ χ.dom := Finset.min'_mem χ.dom h_dom_ne
  have h_min_le : ∀ s ∈ χ.dom, min_old ≤ s := fun s hs => Finset.min'_le χ.dom s hs
  have h_mcs_start := h_c0 pt h_start_mem
  by_cases h_eq_min : pt = min_old
  · -- **BASE CASE**: pt = min(dom). Insert witness y below min_old.
    have h_fresh := exists_rat_lt_finset χ.dom
    let y := h_fresh.choose
    have hy_lt : ∀ s ∈ χ.dom, y < s := h_fresh.choose_spec.1
    have hy_notin : y ∉ χ.dom := h_fresh.choose_spec.2
    -- Use lemma24SinceWithGuard: from snce(ξ,η) ∈ f(pt), get B,C with
    -- η ∈ C, ξ ∈ B, BurgessR3Maximal(C, B, f(pt))
    have h_l24s := lemma24SinceWithGuard h_mcs_start ξ η h_since_start
    let B := h_l24s.choose
    let C := h_l24s.choose_spec.choose
    have h_l24s_prop := h_l24s.choose_spec.choose_spec
    have h_C_mcs : Temporal.SetMaximalConsistent C := h_l24s_prop.1
    have h_η_C : η ∈ C := h_l24s_prop.2.1
    have h_ξ_B : ξ ∈ B := h_l24s_prop.2.2.2
    have h_r3m : BurgessR3Maximal C B (χ.f pt) := h_l24s_prop.2.2.1
    have h_min_lt_y : y < min_old := hy_lt min_old h_min_mem
    let g' := fun a b =>
      if a = y ∧ b = min_old then B
      else χ.g a b
    let χ' : Chronicle Atom := ⟨fun q => if q = y then C else χ.f q, g', insert y χ.dom⟩
    have h_c2'_new : χ'.c2' := by
      intro a b h_adj_new
      obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
      simp only [χ', Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd hab (lt_irrefl _)
      · have hb_eq : b = min_old := by
          by_contra hb_ne
          have hb_ge : min_old ≤ b := h_min_le b hb
          have hb_gt : min_old < b := lt_of_le_of_ne hb_ge (Ne.symm hb_ne)
          exact h_no_between min_old (Finset.mem_insert_of_mem h_min_mem) ⟨h_min_lt_y, hb_gt⟩
        subst hb_eq
        change BurgessR3Maximal
          (if y = y then C else χ.f y)
          (g' y min_old)
          (if min_old = y then C else χ.f min_old)
        have hmin_ne_y : min_old ≠ y := ne_of_gt h_min_lt_y
        simp only [ite_true, hmin_ne_y, ite_false, g', and_self]
        rw [← h_eq_min]; exact h_r3m
      · exact absurd hab (not_lt.mpr (le_of_lt (hy_lt a ha)))
      · have ha_ne : a ≠ y := fun h => hy_notin (h ▸ ha)
        have hb_ne : b ≠ y := fun h => hy_notin (h ▸ hb)
        change BurgessR3Maximal
          (if a = y then C else χ.f a)
          (g' a b)
          (if b = y then C else χ.f b)
        simp only [ha_ne, hb_ne, ite_false, g', false_and, ite_false]
        exact h_c2' a b
          ⟨ha, hb, hab, fun u hu huab => h_no_between u (Finset.mem_insert_of_mem hu) huab⟩
    exact { val := χ'
            dom_sub := Finset.subset_insert y χ.dom
            c0 := by
              intro q hq
              change Temporal.SetMaximalConsistent (if q = y then C else χ.f q)
              change q ∈ insert y χ.dom at hq
              simp only [Finset.mem_insert] at hq
              rcases hq with rfl | hq
              · simp only [ite_true]; exact h_C_mcs
              · have h_ne : q ≠ y := fun h => hy_notin (h ▸ hq)
                simp only [h_ne, ite_false]; exact h_c0 q hq
            c2' := h_c2'_new
            f_agrees := by
              intro x hx
              have h_ne : x ≠ y := fun h => hy_notin (h ▸ hx)
              exact if_neg h_ne
            g_agrees := by
              intro a b ha hb
              change g' a b = χ.g a b
              simp only [g']
              have ha_ne : a ≠ y := fun h => hy_notin (h ▸ ha)
              simp only [ha_ne, false_and, ite_false]
            witness := y
            witness_mem := Finset.mem_insert_self y χ.dom
            witness_lt := hy_lt pt h_start_mem
            witness_event := by simp only [χ', ite_true]; exact h_η_C
            witness_guard := by
              intro a b h_adj_ab h_le_a h_le_b
              have ha_dom : a ∈ insert y χ.dom := h_adj_ab.1
              have hb_dom : b ∈ insert y χ.dom := h_adj_ab.2.1
              simp only [Finset.mem_insert] at ha_dom hb_dom
              -- a must be y (a ≥ y and a < b ≤ pt = min_old ≤ all old)
              have ha_eq : a = y := by
                rcases ha_dom with rfl | ha_old
                · rfl
                · -- a is old, so min_old ≤ a; but b ≤ pt = min_old, a < b
                  have : min_old ≤ a := h_min_le a ha_old
                  linarith [h_adj_ab.2.2.1]
              subst ha_eq
              -- b must be min_old
              have hb_ne_y : b ≠ y := ne_of_gt h_adj_ab.2.2.1
              have hb_old : b ∈ χ.dom := by
                rcases hb_dom with rfl | h
                · exact absurd rfl hb_ne_y
                · exact h
              have hb_eq : b = min_old := by
                have hb_le_min : b ≤ min_old := by
                  rw [← h_eq_min]; exact h_le_b
                have hmin_le_b : min_old ≤ b := h_min_le b hb_old
                exact le_antisymm hb_le_min hmin_le_b
              subst hb_eq
              change ξ ∈ g' y min_old
              simp only [g', and_self, ite_true]
              exact h_ξ_B
            g_sub_f_insert := by
              intro a b h_adj w hw hw_not haw hwb
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact absurd haw (not_lt.mpr (le_of_lt (hy_lt a h_adj.1)))
              · exact absurd hw hw_not
            g_sub_g_new := by
              intro a b h_adj w hw hw_not haw hwb
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact absurd haw (not_lt.mpr (le_of_lt (hy_lt a h_adj.1)))
              · exact absurd hw hw_not
            dom_new_unique := by
              intro u v hu hu_not hv hv_not
              simp only [χ', Finset.mem_insert] at hu hv
              rcases hu with rfl | hu <;> rcases hv with rfl | hv
              · rfl
              · exact absurd hv hv_not
              · exact absurd hu hu_not
              · exact absurd hu hu_not
            new_point_before := by
              intro w hw hw_not
              simp only [χ', Finset.mem_insert] at hw
              rcases hw with rfl | hw
              · exact hy_lt pt h_start_mem
              · exact absurd hw hw_not
            domain_guard := by
              -- Base case: pt = min(dom), witness = y < min(dom).
              -- No w ∈ χ.dom with w < pt exists (pt is min).
              intro w hw _ hws
              exact absurd (h_min_le w hw) (not_le.mpr (h_eq_min ▸ hws))
            witness_not_old := hy_notin }
  · -- **RECURSIVE CASE**: pt > min_old. Find predecessor x''.
    have h_start_gt_min : min_old < pt :=
      lt_of_le_of_ne (h_min_le pt h_start_mem) (Ne.symm h_eq_min)
    let T_pred := χ.dom.filter (fun v => v < pt)
    have hT_ne : T_pred.Nonempty :=
      ⟨min_old, Finset.mem_filter.mpr ⟨h_min_mem, h_start_gt_min⟩⟩
    let x'' := T_pred.max' hT_ne
    have hx''_mem_T := Finset.max'_mem T_pred hT_ne
    have hx''_dom : x'' ∈ χ.dom := (Finset.mem_filter.mp hx''_mem_T).1
    have hx''_lt_start : x'' < pt := (Finset.mem_filter.mp hx''_mem_T).2
    have h_adj_x''s : Adjacent χ.dom x'' pt := by
      refine ⟨hx''_dom, h_start_mem, hx''_lt_start, ?_⟩
      intro u hu ⟨hx''u, hus⟩
      have hu_T : u ∈ T_pred := Finset.mem_filter.mpr ⟨hu, hus⟩
      have := Finset.le_max' T_pred u hu_T
      linarith
    have h_mcs_x'' := h_c0 x'' hx''_dom
    -- Derive: xi ∈ g(x'', pt) → eta ∉ f(x'')
    have h_guard_implies_no_event : ξ ∈ χ.g x'' pt → η ∉ χ.f x'' :=
      fun h_guard h_event => h_no_wit ⟨x'', hx''_dom, hx''_lt_start, h_event,
        ⟨fun a b h_adj_ab h_le_a h_le_b => by
          have ha_eq : a = x'' := by
            by_contra ha_ne
            have ha_gt : x'' < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
            exact h_adj_x''s.2.2.2 a h_adj_ab.1 ⟨ha_gt, lt_of_lt_of_le h_adj_ab.2.2.1 h_le_b⟩
          have hb_eq : b = pt := by
            rw [ha_eq] at h_adj_ab
            by_contra hb_ne
            have hb_lt : b < pt := lt_of_le_of_ne h_le_b hb_ne
            exact h_adj_x''s.2.2.2 b h_adj_ab.2.1 ⟨h_adj_ab.2.2.1, hb_lt⟩
          rw [ha_eq, hb_eq]; exact h_guard,
        fun w hw hx''w hws => absurd ⟨hx''w, hws⟩ (h_adj_x''s.2.2.2 w hw)⟩⟩
    -- Get BurgessR3Maximal facts for (x'', pt)
    have h_r3m_adj := h_c2' x'' pt h_adj_x''s
    have h_gc_adj := BurgessR3Maximal_g_content_sub h_r3m_adj h_mcs_x'' h_mcs_start
    -- Check condition (i): conj ∈ f(x'') AND ξ ∈ g(x'', pt)
    by_cases h_cond_i : Formula.and ξ (Formula.snce ξ η) ∈ χ.f x'' ∧ ξ ∈ χ.g x'' pt
    · -- **Condition (i)**: recurse at x''
      have h_snce_x'' : (ξ S η) ∈ χ.f x'' :=
        conj_right_mcs h_mcs_x'' ξ (Formula.snce ξ η) h_cond_i.1
      -- Derive: h_no_wit at x''
      have h_no_wit_x'' : ¬∃ y ∈ χ.dom, y < x'' ∧ η ∈ χ.f y ∧
          (∀ a b, Adjacent χ.dom a b → y ≤ a → b ≤ x'' → ξ ∈ χ.g a b) ∧
          (∀ w ∈ χ.dom, y < w → w < x'' → ξ ∈ χ.f w) := by
        intro ⟨y, hy_dom, hy_lt_x'', hη_y, h_guard_y, h_dom_guard_y⟩
        exact h_no_wit ⟨y, hy_dom, lt_trans hy_lt_x'' hx''_lt_start, hη_y,
          ⟨fun a b h_adj_ab h_le_a h_le_b => by
            by_cases h_b_gt_x'' : x'' < b
            · -- b > x'', so b = pt and a = x'' (since x'' is predecessor of pt)
              have hb_eq : b = pt := by
                have : b ≤ pt := h_le_b
                by_contra hb_ne
                have hb_lt : b < pt := lt_of_le_of_ne this hb_ne
                exact h_adj_x''s.2.2.2 b h_adj_ab.2.1 ⟨h_b_gt_x'', hb_lt⟩
              have ha_eq : a = x'' := by
                rw [hb_eq] at h_adj_ab
                have ha_le : a ≤ x'' := by
                  by_contra hgt; push Not at hgt
                  exact h_adj_x''s.2.2.2 a h_adj_ab.1 ⟨hgt, h_adj_ab.2.2.1⟩
                exact le_antisymm ha_le (by
                  by_contra hlt; push Not at hlt
                  exact h_adj_ab.2.2.2 x'' hx''_dom ⟨hlt, hx''_lt_start⟩)
              rw [ha_eq, hb_eq]; exact h_cond_i.2
            · -- b ≤ x''
              push Not at h_b_gt_x''
              exact h_guard_y a b h_adj_ab h_le_a h_b_gt_x'',
          fun w hw hyw hws => by
            -- w ∈ χ.dom with y < w < pt. Case split on w vs x''.
            rcases lt_or_eq_of_le (not_lt.mp fun h =>
              h_adj_x''s.2.2.2 w hw ⟨h, hws⟩) with hwx'' | hwx''
            · -- w < x'': use h_dom_guard_y from hypothesis
              exact h_dom_guard_y w hw hyw hwx''
            · -- w = x'': ξ ∈ f(x'') from condition (i) via conj_left_mcs
              rw [hwx'']
              exact conj_left_mcs h_mcs_x'' ξ (Formula.snce ξ η) h_cond_i.1⟩⟩
      -- Termination: (dom.filter (· < x'')).card < (dom.filter (· < pt)).card
      have h_term : (χ.dom.filter (fun v => v < x'')).card <
          (χ.dom.filter (fun v => v < pt)).card := by
        apply Finset.card_lt_card
        constructor
        · intro v hv
          have hv_dom := (Finset.mem_filter.mp hv).1
          have hv_lt : v < x'' := (Finset.mem_filter.mp hv).2
          exact Finset.mem_filter.mpr ⟨hv_dom, lt_trans hv_lt hx''_lt_start⟩
        · simp only [Finset.not_subset]
          exact ⟨x'', Finset.mem_filter.mpr ⟨hx''_dom, hx''_lt_start⟩,
            fun h => absurd (Finset.mem_filter.mp h).2 (lt_irrefl _)⟩
      -- Recurse
      have r := c5BackwardWalk χ h_c0 h_c2' ξ η x'' hx''_dom h_snce_x'' h_no_wit_x''
      -- Compose: guard at (x'', pt) from condition (i) + recursive guard from x''
      exact { val := r.val
              dom_sub := r.dom_sub
              c0 := r.c0
              c2' := r.c2'
              f_agrees := r.f_agrees
              g_agrees := r.g_agrees
              witness := r.witness
              witness_mem := r.witness_mem
              witness_lt := lt_trans r.witness_lt hx''_lt_start
              witness_event := r.witness_event
              witness_guard := by
                intro a b h_adj_ab h_le_a h_le_b
                by_cases h_b_le_x'' : b ≤ x''
                · exact r.witness_guard a b h_adj_ab h_le_a h_b_le_x''
                · -- b > x''. Show a = x'' and b = pt, then use condition (i) guard.
                  push Not at h_b_le_x''
                  have hb_eq : b = pt := by
                    by_contra hb_ne
                    have hb_lt : b < pt := lt_of_le_of_ne h_le_b hb_ne
                    by_cases hb_old : b ∈ χ.dom
                    · exact h_adj_x''s.2.2.2 b hb_old ⟨h_b_le_x'', hb_lt⟩
                    · -- b is new from recursion at x'', so b < x'' by new_point_before.
                      -- Contradicts b > x''.
                      exact absurd (r.new_point_before b h_adj_ab.2.1 hb_old)
                        (not_lt.mpr (le_of_lt h_b_le_x''))
                  subst hb_eq
                  -- a must be x'': x'' in val.dom, a < pt, nothing between a and pt
                  have ha_eq : a = x'' := by
                    have hx''_val : x'' ∈ r.val.dom := r.dom_sub hx''_dom
                    by_contra ha_ne
                    rcases lt_or_gt_of_ne ha_ne with ha_lt | ha_gt
                    · -- a < x'': then x'' is between a and pt=b, contradicting adjacency
                      exact h_adj_ab.2.2.2 x'' hx''_val ⟨ha_lt, hx''_lt_start⟩
                    · -- a > x'': a ∈ r.val.dom, x'' < a < pt. If old, contradicts h_adj_x''s.
                      -- If new, new_point_before gives a < x'', contradiction.
                      by_cases ha_old : a ∈ χ.dom
                      · exact h_adj_x''s.2.2.2 a ha_old ⟨ha_gt, h_adj_ab.2.2.1⟩
                      · exact absurd (r.new_point_before a h_adj_ab.1 ha_old)
                          (not_lt.mpr (le_of_lt ha_gt))
                  rw [ha_eq, r.g_agrees x'' _ hx''_dom h_start_mem]
                  exact h_cond_i.2
              g_sub_f_insert := r.g_sub_f_insert
              g_sub_g_new := r.g_sub_g_new
              dom_new_unique := r.dom_new_unique
              new_point_before := by
                intro w hw hw_not
                exact lt_trans (r.new_point_before w hw hw_not) hx''_lt_start
              domain_guard := by
                -- Condition (i): ξ ∧ (ξ S η) ∈ f(x''), so ξ ∈ f(x'') by conj_left_mcs.
                -- For w between x'' and start: vacuous (x'' is immediate predecessor).
                -- For w between witness and x'': from recursive domain_guard.
                intro w hw hwr hws
                rcases lt_or_eq_of_le (not_lt.mp fun h =>
                  h_adj_x''s.2.2.2 w hw ⟨h, hws⟩) with hwx'' | hwx''
                · -- w < x'', use recursive domain_guard
                  exact r.domain_guard w hw hwr hwx''
                · -- w = x'', use condition (i)
                  rw [hwx'', r.f_agrees x'' hx''_dom]
                  exact conj_left_mcs h_mcs_x'' ξ (Formula.snce ξ η) h_cond_i.1
              witness_not_old := r.witness_not_old }
    · -- **Not condition (i)**: split at (x'', pt)
      have h_split_result : ∃ B' D B'' : Set (Formula Atom),
          BurgessR3Maximal (χ.f x'') B' D ∧
          BurgessR3Maximal D B'' (χ.f pt) ∧
          Temporal.SetMaximalConsistent D ∧
          η ∈ D ∧
          χ.g x'' pt ⊆ D ∧
          χ.g x'' pt ⊆ B' ∧
          χ.g x'' pt ⊆ B'' ∧
          ξ ∈ B'' := by
        by_cases h_eta_g : η ∈ χ.g x'' pt
        · by_cases h_xi_g : ξ ∈ χ.g x'' pt
          · -- η ∈ g, ξ ∈ g: use lemma_2_8_since (avoids needing SetConsistent g)
            have h_conj_not_f : Formula.and ξ (Formula.snce ξ η) ∉ χ.f x'' :=
              fun h => h_cond_i ⟨h, h_xi_g⟩
            have h_neg_disj :
                (Formula.or η (Formula.and ξ (Formula.snce ξ η))).neg ∈ χ.f x'' := by
              have h1 : (¬η) ∈ χ.f x'' := by
                rcases temporal_negation_complete h_mcs_x'' η with h | h
                · exact absurd h (h_guard_implies_no_event h_xi_g)
                · exact h
              have h2 : (Formula.and ξ (Formula.snce ξ η)).neg ∈ χ.f x'' := by
                rcases temporal_negation_complete h_mcs_x''
                  (Formula.and ξ (Formula.snce ξ η)) with h | h
                · exact absurd h h_conj_not_f
                · exact h
              exact temporal_implication_property h_mcs_x''
                (theoremInMcs h_mcs_x''
                  (demorganDisjNegBackward η
                    (Formula.and ξ (Formula.snce ξ η))))
                (conj_mcs h_mcs_x'' η.neg (Formula.and ξ (Formula.snce ξ η)).neg h1 h2)
            obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
              lemma_2_8_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η
                h_since_start h_neg_disj
            exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB'' h_xi_g⟩
          · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B''⟩ :=
              lemma_2_7_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η
                h_since_start h_xi_g
            exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B''⟩
        · by_cases h_eta_neg_g : (¬η) ∈ χ.g x'' pt
          · by_cases h_xi_g : ξ ∈ χ.g x'' pt
            · by_cases h_conj_g : Formula.and ξ (Formula.snce ξ η) ∈ χ.g x'' pt
              · -- conj in g but not-condition(i): conj not in f(x'')
                have h_conj_not_f : Formula.and ξ (Formula.snce ξ η) ∉ χ.f x'' :=
                  fun h => h_cond_i ⟨h, h_xi_g⟩
                have h_neg_disj :
                    (Formula.or η (Formula.and ξ (Formula.snce ξ η))).neg ∈ χ.f x'' := by
                  have h1 : (¬η) ∈ χ.f x'' := by
                    rcases temporal_negation_complete h_mcs_x'' η with h | h
                    · exact absurd h (h_guard_implies_no_event h_xi_g)
                    · exact h
                  have h2 : (Formula.and ξ (Formula.snce ξ η)).neg ∈ χ.f x'' := by
                    rcases temporal_negation_complete h_mcs_x''
                      (Formula.and ξ (Formula.snce ξ η)) with h | h
                    · exact absurd h h_conj_not_f
                    · exact h
                  exact temporal_implication_property h_mcs_x''
                    (theoremInMcs h_mcs_x''
                      (demorganDisjNegBackward η
                        (Formula.and ξ (Formula.snce ξ η))))
                    (conj_mcs h_mcs_x'' η.neg (Formula.and ξ (Formula.snce ξ η)).neg h1 h2)
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', _⟩ :=
                  lemma_2_8_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η
                    h_since_start h_neg_disj
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB'' h_xi_g⟩
              · have h_bx5 := self_accum_since_mcs h_mcs_start ξ η h_since_start
                obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, hBB', h_B_sub_D, hBB'', _⟩ :=
                  lemma_2_7_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj
                    (Formula.and ξ (Formula.snce ξ η)) η h_bx5 h_conj_g
                exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', hBB'' h_xi_g⟩
            · obtain ⟨B', D, B'', hB', hB'', hD, hη, hBB', h_B_sub_D, hBB'', h_xi_B''⟩ :=
                lemma_2_7_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η
                  h_since_start h_xi_g
              exact ⟨B', D, B'', hB', hB'', hD, hη, h_B_sub_D, hBB', hBB'', h_xi_B''⟩
          · by_cases h_xi_g2 : ξ ∈ χ.g x'' pt
            · have h_sp := lemma_2_6_splitting h_mcs_x'' h_mcs_start h_r3m_adj
                η.neg h_eta_neg_g
              obtain ⟨B', D, B'', hB', hB'', hD_mcs, h_dne_D, h_B_sub_D, hBB', hBB''⟩ := h_sp
              exact ⟨B', D, B'', hB', hB'', hD_mcs,
                temporal_implication_property hD_mcs
                  (theoremInMcs hD_mcs (doubleNegation η)) h_dne_D,
                h_B_sub_D, hBB', hBB'', hBB'' h_xi_g2⟩
            · obtain ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, hBB', h_B_sub_D, hBB'', h_xi_B''⟩ :=
                lemma_2_7_since h_mcs_x'' h_mcs_start h_r3m_adj h_r3m_adj.1 h_gc_adj ξ η
                  h_since_start h_xi_g2
              exact ⟨B', D, B'', hB', hB'', hD_mcs, hη_D, h_B_sub_D, hBB', hBB'', h_xi_B''⟩
      let B' := h_split_result.choose
      let D := h_split_result.choose_spec.choose
      let B'' := h_split_result.choose_spec.choose_spec.choose
      have h_split_prop := h_split_result.choose_spec.choose_spec.choose_spec
      have h_B'_max : BurgessR3Maximal (χ.f x'') B' D := h_split_prop.1
      have h_B''_max : BurgessR3Maximal D B'' (χ.f pt) := h_split_prop.2.1
      have h_D_mcs : Temporal.SetMaximalConsistent D := h_split_prop.2.2.1
      have h_eta_D : η ∈ D := h_split_prop.2.2.2.1
      have h_g_sub_D : χ.g x'' pt ⊆ D := h_split_prop.2.2.2.2.1
      have h_g_sub_B' : χ.g x'' pt ⊆ B' := h_split_prop.2.2.2.2.2.1
      have h_g_sub_B'' : χ.g x'' pt ⊆ B'' := h_split_prop.2.2.2.2.2.2.1
      have h_xi_B'' : ξ ∈ B'' := h_split_prop.2.2.2.2.2.2.2
      set z := (x'' + pt) / 2 with hz_def
      have hz_lt_pt : z < pt := by linarith
      have hx''_lt_z : x'' < z := by linarith
      have hz_notin : z ∉ χ.dom := by
        intro h_mem_z; exact h_adj_x''s.2.2.2 z h_mem_z ⟨hx''_lt_z, hz_lt_pt⟩
      let g' := fun a b =>
        if a = x'' ∧ b = z then B'
        else if a = z ∧ b = pt then B''
        else χ.g a b
      let val : Chronicle Atom := ⟨fun q => if q = z then D else χ.f q, g', insert z χ.dom⟩
      have h_c2'_new : val.c2' := by
        intro a b h_adj_new
        obtain ⟨ha, hb, hab, h_no_between⟩ := h_adj_new
        simp only [val, Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd hab (lt_irrefl _)
        · have hb_eq : b = pt := by
            by_contra hb_ne
            have hb_ge : pt ≤ b := by
              by_contra hlt; push Not at hlt
              exact h_adj_x''s.2.2.2 b hb ⟨lt_trans hx''_lt_z hab, hlt⟩
            exact h_no_between pt (Finset.mem_insert_of_mem h_start_mem)
              ⟨hz_lt_pt, lt_of_le_of_ne hb_ge (Ne.symm hb_ne)⟩
          subst hb_eq
          change BurgessR3Maximal (if z = z then D else χ.f z) (g' z b) (if b = z then D else χ.f b)
          have hz_ne_x'' : z ≠ x'' := ne_of_gt hx''_lt_z
          have hb_ne_z : b ≠ z := ne_of_gt hz_lt_pt
          simp only [ite_true, hb_ne_z, ite_false, g', hz_ne_x'', ite_false, and_self, ite_true]
          exact h_B''_max
        · -- a is in old domain, a < z. Show a = x''.
          have ha_le_x'' : a ≤ x'' := by
            by_contra hgt; push Not at hgt
            exact h_adj_x''s.2.2.2 a ha ⟨hgt, lt_trans hab hz_lt_pt⟩
          have ha_eq_x'' : a = x'' := by
            by_contra ha_ne
            exact h_no_between x'' (Finset.mem_insert_of_mem hx''_dom)
              ⟨lt_of_le_of_ne ha_le_x'' ha_ne, hx''_lt_z⟩
          subst ha_eq_x''
          dsimp only [val, g']
          simp only [ne_of_lt hx''_lt_z, if_false, if_true, and_self, if_true]
          exact h_B'_max
        · have ha_ne : a ≠ z := fun h => hz_notin (h ▸ ha)
          have hb_ne : b ≠ z := fun h => hz_notin (h ▸ hb)
          change BurgessR3Maximal (if a = z then D else χ.f a) (g' a b) (if b = z then D else χ.f b)
          simp only [ha_ne, hb_ne, ite_false, g', and_false, false_and]
          exact h_c2' a b
            ⟨ha, hb, hab, fun u hu huab => h_no_between u (Finset.mem_insert_of_mem hu) huab⟩
      exact { val := val
              dom_sub := Finset.subset_insert z χ.dom
              c0 := by
                intro q hq; change Temporal.SetMaximalConsistent (if q = z then D else χ.f q)
                simp only [val, Finset.mem_insert] at hq
                rcases hq with rfl | hq
                · simp only [ite_true]; exact h_D_mcs
                · simp only [show q ≠ z from fun h => hz_notin (h ▸ hq), ite_false]; exact h_c0 q hq
              c2' := h_c2'_new
              f_agrees := by
                intro x hx; dsimp only [val]
                have hx_ne_z : x ≠ z := by intro h; exact hz_notin (h ▸ hx)
                simp only [hx_ne_z, if_false]
              g_agrees := by
                intro a b ha hb; change g' a b = χ.g a b; simp only [g']
                simp only [show a ≠ z from fun h => hz_notin (h ▸ ha),
                  show b ≠ z from fun h => hz_notin (h ▸ hb), false_and, and_false, ite_false]
              witness := z
              witness_mem := Finset.mem_insert_self z χ.dom
              witness_lt := hz_lt_pt
              witness_event := by
                change η ∈ (if z = z then D else χ.f z); simp only [ite_true]; exact h_eta_D
              witness_guard := by
                intro a b h_adj_ab h_le_a h_le_b
                obtain ⟨ha_dom, hb_dom, hab_lt, h_no_btw⟩ := h_adj_ab
                simp only [val, Finset.mem_insert] at ha_dom hb_dom
                have hb_eq : b = pt := by
                  by_contra hb_ne
                  have hb_lt : b < pt := lt_of_le_of_ne h_le_b hb_ne
                  rcases hb_dom with rfl | hb_mem
                  · -- b = z: then a < z and z ≤ a, contradiction
                    exact absurd h_le_a (not_le.mpr hab_lt)
                  · -- b ∈ old dom, b < pt, and z ≤ a < b so x'' < z ≤ a < b < pt
                    exact h_adj_x''s.2.2.2 b hb_mem
                      ⟨lt_of_lt_of_le hx''_lt_z (le_trans h_le_a (le_of_lt hab_lt)), hb_lt⟩
                subst hb_eq
                have ha_eq : a = z := by
                  by_contra ha_ne
                  -- z ≤ a and a ≠ z gives z < a
                  have ha_gt : z < a := lt_of_le_of_ne h_le_a (Ne.symm ha_ne)
                  rcases ha_dom with rfl | ha_mem
                  · exact absurd (le_refl z) (not_le.mpr ha_gt)
                  · -- a ∈ χ.dom, z < a, and a < b = pt. So x'' < z < a < pt,
                    -- contradicts h_adj_x''s.
                    exact h_adj_x''s.2.2.2 a ha_mem ⟨lt_trans hx''_lt_z ha_gt, hab_lt⟩
                subst ha_eq
                -- Need: ξ ∈ g'(z, b) where b = pt (after subst). g' checks:
                -- z = x'' ∧ b = z? No (z ≠ x''). Then z = z ∧ b = pt? Yes. Result: B''.
                change ξ ∈ g' z b
                simp only [g', show z ≠ x'' from ne_of_gt hx''_lt_z, false_and, ite_false,
                  and_self, ite_true]
                exact h_xi_B''
              g_sub_f_insert := by
                intro a b h_adj w hw hw_not haw hwb
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · change χ.g a b ⊆ (if z = z then D else χ.f z); simp only [ite_true]
                  have hab : a = x'' ∧ b = pt := by
                    constructor
                    · by_contra ha_ne
                      rcases lt_or_gt_of_ne ha_ne with h | h
                      · exact h_adj.2.2.2 x'' hx''_dom ⟨h, lt_trans hx''_lt_z hwb⟩
                      · exact h_adj_x''s.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_pt⟩
                    · by_contra hb_ne
                      rcases lt_or_gt_of_ne hb_ne with h | h
                      · exact h_adj_x''s.2.2.2 b h_adj.2.1 ⟨lt_trans hx''_lt_z hwb, h⟩
                      · exact h_adj.2.2.2 pt h_start_mem ⟨lt_trans haw hz_lt_pt, h⟩
                  rw [hab.1, hab.2]; exact h_g_sub_D
                · exact absurd hw hw_not
              g_sub_g_new := by
                intro a b h_adj w hw hw_not haw hwb
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · have ha_eq : a = x'' := by
                    by_contra ha_ne
                    rcases lt_or_gt_of_ne ha_ne with h | h
                    · exact h_adj.2.2.2 x'' hx''_dom ⟨h, lt_trans hx''_lt_z hwb⟩
                    · exact h_adj_x''s.2.2.2 a h_adj.1 ⟨h, lt_trans haw hz_lt_pt⟩
                  have hb_eq : b = pt := by
                    by_contra hb_ne
                    rcases lt_or_gt_of_ne hb_ne with h | h
                    · exact h_adj_x''s.2.2.2 b h_adj.2.1 ⟨lt_trans hx''_lt_z hwb, h⟩
                    · exact h_adj.2.2.2 pt h_start_mem ⟨lt_trans haw hz_lt_pt, h⟩
                  subst ha_eq; subst hb_eq; constructor
                  · dsimp only [val, g']; simp only [and_self, if_true]; exact h_g_sub_B'
                  · dsimp only [val, g']
                    simp only [ne_of_gt hx''_lt_z, false_and, if_false, and_self, if_true]
                    exact h_g_sub_B''
                · exact absurd hw hw_not
              dom_new_unique := by
                intro u v hu hu_not hv hv_not
                simp only [val, Finset.mem_insert] at hu hv
                rcases hu with rfl | hu <;> rcases hv with rfl | hv
                · rfl
                · exact absurd hv hv_not
                · exact absurd hu hu_not
                · exact absurd hu hu_not
              new_point_before := by
                intro w hw hw_not
                simp only [val, Finset.mem_insert] at hw
                rcases hw with rfl | hw
                · exact hz_lt_pt
                · exact absurd hw hw_not
              domain_guard := by
                -- Split case: witness = z (midpoint between x'' and start).
                -- No w ∈ χ.dom with z < w < pt exists (adjacency of (x'', pt)).
                intro w hw hwz hws
                exact absurd ⟨lt_trans hx''_lt_z hwz, hws⟩
                  (h_adj_x''s.2.2.2 w hw)
              witness_not_old := hz_notin }
termination_by (χ.dom.filter (fun v => v < pt)).card
decreasing_by
  all_goals simp_all only []
  all_goals exact h_term




end Cslib.Logic.Temporal.Metalogic.Chronicle

end
