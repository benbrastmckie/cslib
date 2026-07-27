/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.PointInsertion.Burgess

/-! # XuGuard — Xu Lemma 3.2.1 Full Guard Strengthening

Xu 1988 Lemma 3.2.1: For transitive frames, if R(A, B, C) then
- `untl(γ, β) ∈ B` for every `β ∈ B` and `γ ∈ C`
- `snce(α, β) ∈ B` for every `β ∈ B` and `α ∈ A`

This strengthens Xu Lemma 2.3 from top-guard to arbitrary guards.
Also includes Lemma 2.7, Lemma 2.8, and their seed-consistency proofs.

## Main Results

- `xu_lemma_3_2_1_until`: Full until-guard strengthening
- `xu_lemma_3_2_1_since`: Full since-guard strengthening
- `lemma_2_6_splitting`: Burgess Lemma 2.6 splitting (also in this range)
- `lemma_2_7`, `lemma_2_8`: Until/since splitting lemmas
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.BXCanonical
open Cslib.Logic.Bimodal.Metalogic.BXCanonical.CanonicalModel
open Cslib.Logic.Bimodal.Theorems.Propositional
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.TemporalDerived

/-! ## Xu Lemma 3.2.1: Full Guard Strengthening for Transitive Frames

Xu 1988 Lemma 3.2.1 (Section 3, transitive frames): If R(A, B, C), then
  (i)  untl(gamma, beta) ∈ B for every beta ∈ B and gamma ∈ C
  (ii) snce(alpha, beta) ∈ B for every beta ∈ B and alpha ∈ A

This strengthens Xu Lemma 2.3 from top-guard (untl(gamma, top)) to arbitrary
guards (untl(gamma, beta) for all beta ∈ B). The proof uses BX5 (self_accum_until)
for the key self-accumulation step, then BX2G+BX3 monotonicity for the
contradiction. No BX14 (separation_until) is needed.

The proof follows the same contradiction pattern as xu_lemma_2_3:
if the formula is not in B, BurgessR3Maximal_extension_fails gives
¬burgessR3(A, DC(delta ∪ B), C). We extract a neg-until witness and derive
a contradiction using BX5 + monotonicity.
-/

/-- Xu Lemma 3.2.1 (i): If R(A, B, C) then untl(gamma, beta) ∈ B for all
beta ∈ B and gamma ∈ C.

Proof by contradiction: suppose untl(gamma, beta) ∉ B. By maximality,
¬burgessR3(A, DC({untl(gamma,beta)} ∪ B), C). Extract witnesses beta' ∈ B,
gamma' ∈ C with ¬untl(gamma', beta' ∧ untl(gamma, beta)) ∈ A.
Let gamma'' = gamma ∧ gamma', beta'' = beta ∧ beta'. From burgessR3:
untl(gamma'', beta'') ∈ A. By BX5: untl(gamma'', beta'' ∧ untl(gamma'', beta'')) ∈ A.
By BX3+BX2G monotonicity: untl(gamma', beta' ∧ untl(gamma, beta)) ∈ A. Contradiction. -/
theorem xu_lemma_3_2_1_until (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    {beta : Formula Atom} (h_beta : beta ∈ B)
    {gamma : Formula Atom} (h_gamma : gamma ∈ C) :
    Formula.untl beta gamma ∈ B := by
  have h_dcs : ClosedUnderDerivation fc B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Suppose untl(gamma, beta) ∉ B, derive contradiction
  by_contra h_not_in_B
  -- Step 1: BurgessR3Maximal_extension_fails gives ¬burgessR3 for extension
  have h_fails := BurgessR3Maximal_extension_fails fc h_r3m h_not_in_B
  -- Step 2: Extract neg-until witness
  -- If ∀ beta' ∈ B, ∀ gamma' ∈ C, untl(gamma', beta' ∧ untl(gamma, beta)) ∈ A,
  -- then burgessR3(A, DC({untl(gamma,beta)} ∪ B), C) would hold, contradiction.
  have h_neg_until_exists : ∃ beta' ∈ B, ∃ gamma' ∈ C,
      Formula.untl (Formula.and beta' (Formula.untl beta gamma)) gamma' ∉ A := by
    by_contra h_all
    push Not at h_all
    -- Show burgessRSet(A, DC({untl(gamma,beta)} ∪ B), C)
    have h_rset : burgessRSet A (deductiveClosure fc ({Formula.untl beta gamma} ∪ B)) C := by
      intro phi hphi gamma' hgamma'
      obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta', hbeta', ⟨hImpl⟩⟩
      · exact h_r3.1 phi h_B gamma' hgamma'
      · exact untl_left_mono_thm fc h_mcs_A hImpl (h_all beta' hbeta' gamma' hgamma')
    -- Show burgessRSetSince(C, DC({untl(gamma,beta)} ∪ B), A)
    have h_rsince : burgessRSetSince C (deductiveClosure fc ({Formula.untl beta gamma} ∪ B)) A := by
      intro phi hphi alpha halpha
      obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta', hbeta', ⟨hImpl⟩⟩
      · exact h_r3.2 phi h_B alpha halpha
      · have h_burgessR_ext : burgessR A (Formula.and beta' (Formula.untl beta gamma)) C :=
          fun gamma' hgamma' => h_all beta' hbeta' gamma' hgamma'
        have h_snce_ext :=
          burgessR_implies_burgessRSince fc h_mcs_A h_mcs_C h_burgessR_ext alpha halpha
        exact snce_left_mono_thm fc h_mcs_C hImpl h_snce_ext
    exact h_fails ⟨h_rset, h_rsince⟩
  obtain ⟨beta', h_beta', gamma', h_gamma', h_not_in_A⟩ := h_neg_until_exists
  -- Convert to neg formula in A
  have h_neg_until_in_A :
      (Formula.untl (Formula.and beta' (Formula.untl beta gamma)) gamma').neg ∈ A := by
    rcases SetMaximalConsistent.negation_complete h_mcs_A
      (Formula.untl (Formula.and beta' (Formula.untl beta gamma)) gamma') with h | h
    · exact absurd h h_not_in_A
    · exact h
  -- Step 3: Conjunctions
  -- beta'' = beta ∧ beta' ∈ B (CUD closed under conjunction)
  set beta'' := Formula.and beta beta' with beta''_def
  have h_beta'' : beta'' ∈ B := cud_conj_closed h_dcs h_beta h_beta'
  -- gamma'' = gamma ∧ gamma' ∈ C (MCS closed under conjunction)
  set gamma'' := Formula.and gamma gamma' with gamma''_def
  have h_gamma'' : gamma'' ∈ C := conj_mcs fc h_mcs_C gamma gamma' h_gamma h_gamma'
  -- Step 4: From burgessR3: untl(gamma'', beta'') ∈ A
  have h_untl_gg_bb : Formula.untl beta'' gamma'' ∈ A :=
    h_r3.1 beta'' h_beta'' gamma'' h_gamma''
  -- Step 5: BX5 (self_accum_until): untl(gamma'', beta'' ∧ untl(gamma'', beta'')) ∈ A
  have h_bx5 : Formula.untl (Formula.and beta'' (Formula.untl beta'' gamma'')) gamma'' ∈ A :=
    self_accum_until_mcs fc h_mcs_A beta'' gamma'' h_untl_gg_bb
  -- Step 6: Monotonicity chain to derive contradiction
  -- We need untl(gamma', beta' ∧ untl(gamma, beta)) ∈ A.
  -- From h_bx5: untl(gamma'', beta'' ∧ untl(gamma'', beta'')) ∈ A
  -- Step 6a: Build ⊢ (beta'' ∧ untl(gamma'', beta'')) → (beta' ∧ untl(gamma, beta))
  -- Component 1: ⊢ beta'' → beta' (right projection since beta'' = beta ∧ beta')
  -- Component 2: ⊢ untl(gamma'', beta'') → untl(gamma, beta)
  --   = ⊢ untl(gamma'', beta'') → untl(gamma, beta'') (BX3: event γ∧γ' → γ)
  --     composed with ⊢ untl(gamma, beta'') → untl(gamma, beta) (BX2G: guard β∧β' → β)
  -- Event monotonicity: G(gamma'' → gamma) → untl(gamma'', beta'') → untl(gamma, beta'')
  -- Since ⊢ gamma'' → gamma (lceImp), ⊢ G(gamma'' → gamma) by temporal_necessitation
  have h_event_impl : DerivationTree fc [] (gamma''.imp gamma) := lceImp gamma gamma'
  have h_G_event : DerivationTree fc [] (gamma''.imp gamma).allFuture :=
    DerivationTree.temporal_necessitation _ h_event_impl
  have h_bx3_ax :=
    DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until gamma'' gamma beta'') trivial
  -- ⊢ untl(gamma'', beta'') → untl(gamma, beta'')
  have h_event_mono :
      DerivationTree fc [] ((Formula.untl beta'' gamma'').imp (Formula.untl beta'' gamma)) :=
    DerivationTree.modus_ponens [] _ _ h_bx3_ax h_G_event
  -- Guard monotonicity: ⊢ untl(gamma, beta'') → untl(gamma, beta) via untlLeftMonoDeriv
  have h_guard_impl : DerivationTree fc [] (beta''.imp beta) := lceImp beta beta'
  have h_guard_mono :
      DerivationTree fc [] ((Formula.untl beta'' gamma).imp (Formula.untl beta gamma)) :=
    untlLeftMonoDeriv fc beta'' gamma beta h_guard_impl
  -- Compose: ⊢ untl(gamma'', beta'') → untl(gamma, beta)
  have h_untl_mono :
      DerivationTree fc [] ((Formula.untl beta'' gamma'').imp (Formula.untl beta gamma)) :=
    impTrans h_event_mono h_guard_mono
  -- Step 6b: Build the full guard implication
  -- ⊢ (beta'' ∧ untl(gamma'', beta'')) → (beta' ∧ untl(gamma, beta))
  -- By extracting components and re-pairing
  have h_full_guard_impl : DerivationTree fc []
      ((Formula.and beta'' (Formula.untl beta'' gamma'')).imp
       (Formula.and beta' (Formula.untl beta gamma))) := by
    -- Derivation in context [beta'' ∧ untl(gamma'', beta'')]
    set ctx := Formula.and beta'' (Formula.untl beta'' gamma'')
    -- From ctx, extract beta' via beta'' → beta' (right projection)
    have h_get_beta' : DerivationTree fc [ctx] beta' := by
      have h1 : DerivationTree fc [ctx] beta'' :=
        DerivationTree.modus_ponens [ctx] ctx beta''
          (DerivationTree.weakening [] [ctx] _
            (lceImp beta'' (Formula.untl beta'' gamma'')) (List.nil_subset _))
          (DerivationTree.assumption _ ctx (by simp))
      exact DerivationTree.modus_ponens [ctx] beta'' beta'
        (DerivationTree.weakening [] [ctx] _ (rceImp beta beta') (List.nil_subset _))
        h1
    -- From ctx, extract untl(gamma, beta) via monotonicity
    have h_get_untl : DerivationTree fc [ctx] (Formula.untl beta gamma) := by
      have h1 : DerivationTree fc [ctx] (Formula.untl beta'' gamma'') :=
        DerivationTree.modus_ponens [ctx] ctx (Formula.untl beta'' gamma'')
          (DerivationTree.weakening [] [ctx] _
            (rceImp beta'' (Formula.untl beta'' gamma'')) (List.nil_subset _))
          (DerivationTree.assumption _ ctx (by simp))
      exact DerivationTree.modus_ponens [ctx]
        (Formula.untl beta'' gamma'') (Formula.untl beta gamma)
        (DerivationTree.weakening [] [ctx] _ h_untl_mono (List.nil_subset _))
        h1
    -- Pair them
    have h_paired : DerivationTree fc [ctx] (Formula.and beta' (Formula.untl beta gamma)) :=
      DerivationTree.modus_ponens [ctx] (Formula.untl beta gamma) _
        (DerivationTree.modus_ponens [ctx] beta' _
          (DerivationTree.weakening [] [ctx] _
            (pairing beta' (Formula.untl beta gamma)) (List.nil_subset _))
          h_get_beta')
        h_get_untl
    exact deductionTheorem [] ctx (Formula.and beta' (Formula.untl beta gamma)) h_paired
  -- Step 6c: Apply guard monotonicity to BX5 result
  -- untl_left_mono_thm: ⊢ guard_old → guard_new and
  -- untl(event, guard_old) ∈ A → untl(event, guard_new) ∈ A
  have h_step1 : Formula.untl (Formula.and beta' (Formula.untl beta gamma)) gamma'' ∈ A :=
    untl_left_mono_thm fc h_mcs_A h_full_guard_impl h_bx5
  -- Step 6d: Apply event monotonicity to change gamma'' → gamma'
  -- right_mono_until_mcs: ⊢ event_old → event_new and
  -- untl(event_old, guard) ∈ A → untl(event_new, guard) ∈ A
  have h_event_impl' : DerivationTree fc [] (gamma''.imp gamma') := rceImp gamma gamma'
  have h_final : Formula.untl (Formula.and beta' (Formula.untl beta gamma)) gamma' ∈ A :=
    right_mono_until_mcs fc h_mcs_A h_event_impl' h_step1
  -- Step 7: Contradiction
  exact absurd h_final (SetMaximalConsistent.neg_excludes h_mcs_A _ h_neg_until_in_A)

/-- Xu Lemma 3.2.1 (ii): If R(A, B, C) then snce(alpha, beta) ∈ B for all
beta ∈ B and alpha ∈ A.

Dual of xu_lemma_3_2_1_until: uses BX5' (self_accum_since), BX3' (right_mono_since),
and BX2H (left_mono_since_H) for the guard strengthening and contradiction. -/
theorem xu_lemma_3_2_1_since (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A) (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    {beta : Formula Atom} (h_beta : beta ∈ B)
    {alpha : Formula Atom} (h_alpha : alpha ∈ A) :
    Formula.snce beta alpha ∈ B := by
  have h_dcs : ClosedUnderDerivation fc B := h_r3m.1
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Suppose snce(alpha, beta) ∉ B, derive contradiction
  by_contra h_not_in_B
  -- Step 1: BurgessR3Maximal_extension_fails gives ¬burgessR3 for extension
  have h_fails := BurgessR3Maximal_extension_fails fc h_r3m h_not_in_B
  -- Step 2: Extract neg-since witness
  -- Since condition in burgessR3: ∀ beta' ∈ B, ∀ alpha' ∈ A, snce(alpha', beta') ∈ C
  -- If ∀ beta' ∈ B, ∀ alpha' ∈ A, snce(alpha', beta' ∧ snce(alpha, beta)) ∈ C,
  -- then burgessR3(A, DC({snce(alpha,beta)} ∪ B), C) would hold, contradiction.
  have h_neg_since_exists : ∃ beta' ∈ B, ∃ alpha' ∈ A,
      Formula.snce (Formula.and beta' (Formula.snce beta alpha)) alpha' ∉ C := by
    by_contra h_all
    push Not at h_all
    -- Show burgessRSetSince(C, DC({snce(alpha,beta)} ∪ B), A)
    have h_rsince :
        burgessRSetSince C (deductiveClosure fc ({Formula.snce beta alpha} ∪ B)) A := by
      intro phi hphi alpha' halpha'
      obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta', hbeta', ⟨hImpl⟩⟩
      · exact h_r3.2 phi h_B alpha' halpha'
      · exact snce_left_mono_thm fc h_mcs_C hImpl (h_all beta' hbeta' alpha' halpha')
    -- Show burgessRSet(A, DC({snce(alpha,beta)} ∪ B), C)
    have h_rset : burgessRSet A (deductiveClosure fc ({Formula.snce beta alpha} ∪ B)) C := by
      intro phi hphi gamma hgamma
      obtain ⟨L, hL_sub, ⟨d⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_dcs hL_sub d with h_B | ⟨beta', hbeta', ⟨hImpl⟩⟩
      · exact h_r3.1 phi h_B gamma hgamma
      · have h_burgessRSince_ext :
            burgessRSince C (Formula.and beta' (Formula.snce beta alpha)) A :=
          fun alpha' halpha' => h_all beta' hbeta' alpha' halpha'
        have h_untl_ext :=
          burgessRSince_implies_burgessR fc h_mcs_A h_mcs_C h_burgessRSince_ext gamma hgamma
        exact untl_left_mono_thm fc h_mcs_A hImpl h_untl_ext
    exact h_fails ⟨h_rset, h_rsince⟩
  obtain ⟨beta', h_beta', alpha', h_alpha', h_not_in_C⟩ := h_neg_since_exists
  -- Convert to neg formula in C
  have h_neg_since_in_C :
      (Formula.snce (Formula.and beta' (Formula.snce beta alpha)) alpha').neg ∈ C := by
    rcases SetMaximalConsistent.negation_complete h_mcs_C
      (Formula.snce (Formula.and beta' (Formula.snce beta alpha)) alpha') with h | h
    · exact absurd h h_not_in_C
    · exact h
  -- Step 3: Conjunctions
  set beta'' := Formula.and beta beta' with beta''_def
  have h_beta'' : beta'' ∈ B := cud_conj_closed h_dcs h_beta h_beta'
  set alpha'' := Formula.and alpha alpha' with alpha''_def
  have h_alpha'' : alpha'' ∈ A := conj_mcs fc h_mcs_A alpha alpha' h_alpha h_alpha'
  -- Step 4: From burgessR3: snce(alpha'', beta'') ∈ C
  have h_snce_aa_bb : Formula.snce beta'' alpha'' ∈ C :=
    h_r3.2 beta'' h_beta'' alpha'' h_alpha''
  -- Step 5: BX5' (self_accum_since): snce(alpha'', beta'' ∧ snce(alpha'', beta'')) ∈ C
  have h_bx5 : Formula.snce (Formula.and beta'' (Formula.snce beta'' alpha'')) alpha'' ∈ C :=
    self_accum_since_mcs fc h_mcs_C beta'' alpha'' h_snce_aa_bb
  -- Step 6: Monotonicity chain to derive contradiction
  -- Event monotonicity for Since: H(alpha'' → alpha') → snce(alpha'', guard) → snce(alpha', guard)
  have h_event_impl : DerivationTree fc [] (alpha''.imp alpha') := rceImp alpha alpha'
  have h_H_event : DerivationTree fc [] (alpha''.imp alpha').allPast :=
    Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_event_impl
  have h_bx3'_ax :=
    DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since alpha'' alpha' beta'') trivial
  -- ⊢ snce(alpha'', beta'') → snce(alpha', beta'')
  have h_event_mono :
      DerivationTree fc [] ((Formula.snce beta'' alpha'').imp (Formula.snce beta'' alpha')) :=
    DerivationTree.modus_ponens [] _ _ h_bx3'_ax h_H_event
  -- Guard monotonicity: ⊢ snce(alpha', beta'') → snce(alpha', beta) via snceLeftMonoDeriv
  have h_guard_impl : DerivationTree fc [] (beta''.imp beta) := lceImp beta beta'
  have h_guard_mono :
      DerivationTree fc [] ((Formula.snce beta'' alpha').imp (Formula.snce beta alpha')) :=
    snceLeftMonoDeriv fc beta'' alpha' beta h_guard_impl
  -- Compose: ⊢ snce(alpha'', beta'') → snce(alpha', beta)
  have h_snce_mono :
      DerivationTree fc [] ((Formula.snce beta'' alpha'').imp (Formula.snce beta alpha')) :=
    impTrans h_event_mono h_guard_mono
  -- Build the full guard implication
  -- ⊢ (beta'' ∧ snce(alpha'', beta'')) → (beta' ∧ snce(alpha, beta))
  have h_full_guard_impl : DerivationTree fc []
      ((Formula.and beta'' (Formula.snce beta'' alpha'')).imp
       (Formula.and beta' (Formula.snce beta alpha))) := by
    set ctx := Formula.and beta'' (Formula.snce beta'' alpha'')
    have h_get_beta' : DerivationTree fc [ctx] beta' := by
      have h1 : DerivationTree fc [ctx] beta'' :=
        DerivationTree.modus_ponens [ctx] ctx beta''
          (DerivationTree.weakening [] [ctx] _
            (lceImp beta'' (Formula.snce beta'' alpha'')) (List.nil_subset _))
          (DerivationTree.assumption _ ctx (by simp))
      exact DerivationTree.modus_ponens [ctx] beta'' beta'
        (DerivationTree.weakening [] [ctx] _ (rceImp beta beta') (List.nil_subset _))
        h1
    have h_get_snce : DerivationTree fc [ctx] (Formula.snce beta alpha) := by
      have h1 : DerivationTree fc [ctx] (Formula.snce beta'' alpha'') :=
        DerivationTree.modus_ponens [ctx] ctx (Formula.snce beta'' alpha'')
          (DerivationTree.weakening [] [ctx] _
            (rceImp beta'' (Formula.snce beta'' alpha'')) (List.nil_subset _))
          (DerivationTree.assumption _ ctx (by simp))
      -- snce(alpha'', beta'') → snce(alpha, beta) via event + guard mono
      -- Event: alpha'' → alpha (lceImp)
      have h_ev : DerivationTree fc [] (alpha''.imp alpha) := lceImp alpha alpha'
      have h_H_ev : DerivationTree fc [] (alpha''.imp alpha).allPast :=
        Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_ev
      have h_bx3'_ev :=
        DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since alpha'' alpha beta'') trivial
      have h_ev_mono :
          DerivationTree fc [] ((Formula.snce beta'' alpha'').imp (Formula.snce beta'' alpha)) :=
        DerivationTree.modus_ponens [] _ _ h_bx3'_ev h_H_ev
      -- Guard: beta'' → beta (lceImp)
      have h_gd_mono :
          DerivationTree fc [] ((Formula.snce beta'' alpha).imp (Formula.snce beta alpha)) :=
        snceLeftMonoDeriv fc beta'' alpha beta (lceImp beta beta')
      have h_full_snce_mono :
          DerivationTree fc [] ((Formula.snce beta'' alpha'').imp (Formula.snce beta alpha)) :=
        impTrans h_ev_mono h_gd_mono
      exact DerivationTree.modus_ponens [ctx]
        (Formula.snce beta'' alpha'') (Formula.snce beta alpha)
        (DerivationTree.weakening [] [ctx] _ h_full_snce_mono (List.nil_subset _))
        h1
    have h_paired : DerivationTree fc [ctx] (Formula.and beta' (Formula.snce beta alpha)) :=
      DerivationTree.modus_ponens [ctx] (Formula.snce beta alpha) _
        (DerivationTree.modus_ponens [ctx] beta' _
          (DerivationTree.weakening [] [ctx] _
            (pairing beta' (Formula.snce beta alpha)) (List.nil_subset _))
          h_get_beta')
        h_get_snce
    exact deductionTheorem [] ctx (Formula.and beta' (Formula.snce beta alpha)) h_paired
  -- Apply guard monotonicity to BX5 result
  have h_step1 : Formula.snce (Formula.and beta' (Formula.snce beta alpha)) alpha'' ∈ C :=
    snce_left_mono_thm fc h_mcs_C h_full_guard_impl h_bx5
  -- Apply event monotonicity to change alpha'' → alpha'
  have h_event_impl' : DerivationTree fc [] (alpha''.imp alpha') := rceImp alpha alpha'
  have h_final : Formula.snce (Formula.and beta' (Formula.snce beta alpha)) alpha' ∈ C :=
    right_mono_since_mcs fc h_mcs_C h_event_impl' h_step1
  -- Step 7: Contradiction
  exact absurd h_final (SetMaximalConsistent.neg_excludes h_mcs_C _ h_neg_since_in_C)

/-- **Lemma 2.6 Splitting** (Burgess 1982, Lemma 2.6): Given BurgessR3Maximal(A, B, C)
with β ∉ B, construct MCS D with β.neg ∈ D and decomposed BurgessR3Maximal relations:
BurgessR3Maximal(A, B', D) and BurgessR3Maximal(D, B'', C).

Uses Xu 1988 Lemma 3.2.2 (transitive frames): trivial seed {β.neg} ∪ B (consistent
by dcs_neg_union_consistent since B is SDC and β ∉ B). The Until/Since formulas
needed for burgessR3 follow from Xu 3.2.1 (guard strengthening), which proves
untl(γ, β') ∈ B and snce(α, β') ∈ B for all β' ∈ B, γ ∈ C, α ∈ A.
No BX14 (separation_until) is needed. -/
theorem lemma_2_6_splitting (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (_h_gc : gContent A ⊆ C)
    (β : Formula Atom)
    (h_β_not_B : β ∉ B) :
    ∃ B' D B'', BurgessR3Maximal fc A B' D ∧ BurgessR3Maximal fc D B'' C ∧
      SetMaximalConsistent fc D ∧ β.neg ∈ D ∧ B ⊆ D ∧ B ⊆ B' ∧ B ⊆ B'' := by
  -- Step 1: Trivial seed {β.neg} ∪ B is consistent
  -- B is CUD (from BurgessR3Maximal) and β ∉ B, so B is SDC (cud_not_mem_is_sdc).
  -- dcs_neg_union_consistent then gives SetConsistent fc ({β.neg} ∪ B).
  have h_sdc : SetDeductivelyClosed fc B := cud_not_mem_is_sdc h_B_dcs h_β_not_B
  have h_seed_cons : SetConsistent fc ({β.neg} ∪ B) := dcs_neg_union_consistent fc h_sdc h_β_not_B
  -- Step 2: Lindenbaum-extend to MCS D
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  -- Step 3: Extract seed memberships
  have h_β_neg_D : β.neg ∈ D := h_sup (Set.mem_union_left _ (Set.mem_singleton β.neg))
  have h_B_sub_D : B ⊆ D := fun φ hφ => h_sup (Set.mem_union_right _ hφ)
  -- Step 4: Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  -- Xu 3.2.1(i): untl(γ, β') ∈ B for all β' ∈ B, γ ∈ C. Since B ⊆ D: untl(γ, β') ∈ D.
  have h_untl_D : ∀ β' ∈ B, ∀ γ ∈ C, Formula.untl β' γ ∈ D := by
    intro β' hβ' γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until fc h_mcs_A h_mcs_C h_r3m hβ' hγ)
  -- Xu 3.2.1(ii): snce(α, β') ∈ B for all β' ∈ B, α ∈ A. Since B ⊆ D: snce(α, β') ∈ D.
  have h_snce_D : ∀ β' ∈ B, ∀ α ∈ A, Formula.snce β' α ∈ D := by
    intro β' hβ' α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since fc h_mcs_A h_mcs_C h_r3m hβ' hα)
  -- Step 5: Establish burgessR3(D, B, C) from Until formulas
  have h_rSet_D : burgessRSet D B C := fun β' hβ' γ hγ => h_untl_D β' hβ' γ hγ
  -- burgessRSetSince(C, B, D) follows from burgessR via standard conversion
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β' hβ'
    exact burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C (h_rSet_D β' hβ')
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  -- Step 6: Establish burgessR3(A, B, D) from Since formulas
  -- snce(α, β') ∈ D for all β' ∈ B, α ∈ A gives burgessRSetSince(D, B, A)
  have h_rSetSince_A : burgessRSetSince D B A := fun β' hβ' α hα => h_snce_D β' hβ' α hα
  -- burgessR(A, β', D) follows from burgessRSince via standard conversion
  have h_rSet_A : burgessRSet A B D := by
    intro β' hβ'
    exact burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs (h_rSetSince_A β' hβ')
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Step 7: BurgessR3Maximal via Zorn (burgessR3Maximal_extension_exists)
  obtain ⟨B', h_B_sub_B', _, h_B'_max⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_B_sub_B'', _, h_B''_max⟩ := burgessR3Maximal_extension_exists fc h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_β_neg_D, h_B_sub_D, h_B_sub_B', h_B_sub_B''⟩

/-- The D0 seed for Lemma 2.7 (Burgess 1982 p.372), simplified via Xu 3.2.1:
  B ∪ {eta} ∪ {snce(α, β ∧ xi) : β ∈ B, α ∈ A}.

The original 5-component seed included {untl(γ, β)} and {snce(α, β)} but these
are redundant: Xu 3.2.1 proves untl(γ, β) ∈ B and snce(α, β) ∈ B for all
β ∈ B, γ ∈ C, α ∈ A when BurgessR3Maximal(A, B, C). Since B ⊆ D (from
the seed's first component), these formulas are already in D.

The 3rd component snce(α, β∧xi) cannot be dropped because xi ∉ B prevents
Xu 3.2.1 from applying.

Convention alignment with Burgess:
  untl(xi, eta) ∈ A where xi = guard (Burgess η), eta = event (Burgess ξ).
  The condition is xi ∉ B (guard not in B, matching Burgess η ∉ B).
  The seed contains {eta} (event, Burgess ξ) → eta ∈ D.
  The 3rd component snce(β∧xi, α) (Burgess S(α, β∧η)) → xi ∈ B'. -/
@[nolint unusedArguments]
def lemma27Seed (_fc : FrameClass) (A B _C : Set (Formula Atom)) (xi eta : Formula Atom) :
    Set (Formula Atom) :=
  B ∪ {eta} ∪ {φ | ∃ β ∈ B, ∃ α ∈ A, φ = Formula.snce (Formula.and β xi) α}

/-- Extract a B-guard from a single element of the lemma27Seed.
For each of the 3 cases:
1. φ ∈ B: guard = φ
2. φ = eta: guard = ⊤ (any theorem)
3. φ = snce(β'∧xi, α'): guard = β' -/
@[nolint unusedArguments]
noncomputable def l27Guard (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B)
    (xi eta : Formula Atom) (φ : Formula Atom) (_h : φ ∈ lemma27Seed fc A B C xi eta) :
    { g : Formula Atom // g ∈ B } := by
  classical
  by_cases h1 : φ ∈ B
  · exact ⟨φ, h1⟩
  · by_cases h5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce (Formula.and β' xi) α
    · exact ⟨Classical.choose h5, (Classical.choose_spec h5).1⟩
    · -- Must be eta
      exact ⟨Formula.bot.imp Formula.bot,
        cud_contains_theorems h_dcs (identity (Formula.bot : Formula Atom))⟩

/-- Recursively extract B-guards from L ⊆ lemma27Seed.
Includes β₀ (maximality witness guard) to ensure guard→β₀ via conjunction elimination. -/
noncomputable def l27CollectGuards (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B)
    (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma27Seed fc A B C xi eta) →
    { gs : List (Formula Atom) // ∀ g ∈ gs, g ∈ B }
  | [], _ => ⟨[], fun _ h => (by simp at h)⟩
  | φ :: rest, hL =>
    let ⟨g, hg⟩ := l27Guard fc h_dcs xi eta φ (hL φ (List.mem_cons.mpr (Or.inl rfl)))
    let ⟨gs, hgs⟩ := l27CollectGuards fc h_dcs xi eta rest
      (fun ψ hψ => hL ψ (List.mem_cons.mpr (Or.inr hψ)))
    ⟨g :: gs, fun g' hg' => by
      rcases List.mem_cons.mp hg' with rfl | h
      · exact hg
      · exact hgs g' h⟩

/-- For each element of L ⊆ lemma27Seed, extract the A-event
(if snce(β'∧xi, α') formula from component 3). -/
@[nolint unusedArguments]
noncomputable def l27AEventList (fc : FrameClass) {A B C : Set (Formula Atom)}
    (xi eta : Formula Atom) (L : List (Formula Atom))
    (_hL : ∀ φ ∈ L, φ ∈ lemma27Seed fc A B C xi eta) : List (Formula Atom) :=
  L.filterMap (fun φ => by
    classical
    exact if h : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce (Formula.and β' xi) α then
      some (Classical.choose (Classical.choose_spec h).2)
    else none)

set_option linter.flexible false in
/-- Elements of l27AEventList are in A. -/
theorem l27_a_event_list_mem (fc : FrameClass) {A B C : Set (Formula Atom)}
    {xi eta : Formula Atom} {L : List (Formula Atom)}
    {hL : ∀ φ ∈ L, φ ∈ lemma27Seed fc A B C xi eta}
    {α : Formula Atom} (hα : α ∈ l27AEventList fc xi eta L hL) : α ∈ A := by
  unfold l27AEventList at hα
  rcases List.mem_filterMap.mp hα with ⟨φ, _, h_eq⟩
  split at h_eq
  · next h_snce5 =>
    simp at h_eq
    rw [← h_eq]
    exact (Classical.choose_spec ((Classical.choose_spec h_snce5).2)).1
  · simp at h_eq

set_option linter.flexible false in
/-- If φ ∈ L ∩ B then φ is in l27CollectGuards output. -/
theorem l27_collect_guards_mem_of_B (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B) (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma27Seed fc A B C xi eta) →
    ∀ φ ∈ L, φ ∈ B → φ ∈ (l27CollectGuards fc h_dcs xi eta L hL).val
  | [], _, φ, hφ, _ => (by simp at hφ)
  | ψ :: rest, hL, φ, hφ, h_B => by
    simp [l27CollectGuards]
    rcases List.mem_cons.mp hφ with rfl | h_rest
    · left
      unfold l27Guard; simp [h_B]
    · right; exact l27_collect_guards_mem_of_B fc h_dcs xi eta rest _ φ h_rest h_B

/-- Formula.and is injective in the first argument. -/
theorem formula_and_left_cancel (_fc : FrameClass) {a b c : Formula Atom}
    (h : Formula.and a c = Formula.and b c) : a = b := by
  simp only [Formula.and] at h
  exact (Formula.imp.injEq _ _ _ _ |>.mp (Formula.imp.injEq _ _ _ _ |>.mp h).1).1

set_option linter.flexible false in
/-- l27Guard for snce(β'∧xi,α') when snce(β'∧xi,α') ∉ B returns β'. -/
theorem l27_guard_snce_xi_val (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B) (xi eta β' α' : Formula Atom)
    (h_seed : Formula.snce (Formula.and β' xi) α' ∈ lemma27Seed fc A B C xi eta)
    (h_not_B : Formula.snce (Formula.and β' xi) α' ∉ B)
    (hβ' : β' ∈ B) (hα' : α' ∈ A) :
    (l27Guard fc h_dcs xi eta (Formula.snce (Formula.and β' xi) α') h_seed).val = β' := by
  unfold l27Guard; simp [h_not_B]
  split
  · next h =>
    -- h : β' ∈ B ∧ α' ∈ A (after simp simplified the existential)
    -- The Classical.choose was applied to the original ∃ form.
    -- After simp, the ∃ was resolved. We need to recover the original spec.
    have h_exists : ∃ β'' ∈ B, ∃ α'' ∈ A,
        Formula.snce (Formula.and β' xi) α' = Formula.snce (Formula.and β'' xi) α'' :=
      ⟨β', h.1, α', h.2, rfl⟩
    have h_spec := Classical.choose_spec h_exists
    obtain ⟨hβ_B, α'', hα'', h_eq⟩ := h_spec
    rw [Formula.snce.injEq] at h_eq
    have h_β_eq := (formula_and_left_cancel fc h_eq.1).symm
    convert h_β_eq using 1; simp
  · next h =>
    exfalso; exact h ⟨hβ', hα'⟩

set_option linter.flexible false in
/-- If snce(β'∧xi,α') ∈ L with β'∈B, α'∈A, snce(β'∧xi,α') ∉ B,
then β' is in the guard list. -/
theorem l27_collect_guards_mem_of_snce_xi (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_dcs : ClosedUnderDerivation fc B) (xi eta : Formula Atom) :
    (L : List (Formula Atom)) →
    (hL : ∀ φ ∈ L, φ ∈ lemma27Seed fc A B C xi eta) →
    ∀ β' α', Formula.snce (Formula.and β' xi) α' ∈ L → β' ∈ B → α' ∈ A →
      Formula.snce (Formula.and β' xi) α' ∉ B →
      β' ∈ (l27CollectGuards fc h_dcs xi eta L hL).val
  | [], _, β', α', hφ, _, _, _ => (by simp at hφ)
  | ψ :: rest, hL, β', α', hφ, hβ', hα', h_not_B => by
    simp [l27CollectGuards]
    rcases List.mem_cons.mp hφ with rfl | h_rest
    · left
      exact (l27_guard_snce_xi_val fc h_dcs xi eta β' α'
        (hL (Formula.snce (Formula.and β' xi) α') (List.mem_cons.mpr (Or.inl rfl)))
        h_not_B hβ' hα').symm
    · right
      exact l27_collect_guards_mem_of_snce_xi fc h_dcs xi eta rest _ β' α' h_rest hβ' hα' h_not_B

/-- If snce(β'∧xi,α') ∈ L with β'∈B, α'∈A, and appropriate conditions,
then α' ∈ l27AEventList. -/
theorem l27_a_event_list_α_mem_xi (fc : FrameClass) {A B C : Set (Formula Atom)}
    {xi eta : Formula Atom} {L : List (Formula Atom)}
    {hL : ∀ φ ∈ L, φ ∈ lemma27Seed fc A B C xi eta}
    {β' α' : Formula Atom} (hφ : Formula.snce (Formula.and β' xi) α' ∈ L)
    (hβ' : β' ∈ B) (hα' : α' ∈ A) :
    α' ∈ l27AEventList fc xi eta L hL := by
  unfold l27AEventList
  apply List.mem_filterMap.mpr
  refine ⟨Formula.snce (Formula.and β' xi) α', hφ, ?_⟩
  have h_ex : ∃ β'' ∈ B, ∃ α'' ∈ A,
      Formula.snce (Formula.and β' xi) α' = Formula.snce (Formula.and β'' xi) α'' :=
    ⟨β', hβ', α', hα', rfl⟩
  rw [dif_pos h_ex]
  congr 1
  have h_spec := Classical.choose_spec (Classical.choose_spec h_ex).2
  rw [Formula.snce.injEq] at h_spec
  exact h_spec.2.2.symm


/-- Consistency of the Lemma 2.7 D0 seed (Burgess 1982 p.372), simplified via Xu 3.2.1.

The simplified seed has 3 components: B ∪ {eta} ∪ {snce(α, β∧xi)}.
Uses BX5 (self-accumulation) + BX7 (linearity) + BX13 (enrichment) to derive
F(event) ∈ A, which ensures the seed is consistent. -/
theorem lemma_2_7_seed_consistent (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (_h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : Formula.untl xi eta ∈ A)
    (h_xi_not_B : xi ∉ B) :
    SetConsistent fc (lemma27Seed fc A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  -- Step 1: Extract neg-until witness from xi ∉ B + BurgessR3Maximal
  have h_not_r3_xi := BurgessR3Maximal_extension_fails fc h_r3m h_xi_not_B
  have h_neg_until_exists : ∃ beta0 ∈ B, ∃ gamma0 ∈ C,
      Formula.untl (Formula.and beta0 xi) gamma0 ∉ A := by
    by_contra h_all_until
    push Not at h_all_until
    have h_rset : burgessRSet A (deductiveClosure fc ({xi} ∪ B)) C := by
      intro phi hphi gamma hgamma
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨hImpl⟩⟩
      · exact h_r3.1 phi h_B_case gamma hgamma
      · exact untl_left_mono_thm fc h_mcs_A hImpl (h_all_until beta_w hbeta_w gamma hgamma)
    have h_rsince : burgessRSetSince C (deductiveClosure fc ({xi} ∪ B)) A := by
      intro phi hphi alpha halpha
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases dc_delta_B_controlled fc h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨hImpl⟩⟩
      · exact h_r3.2 phi h_B_case alpha halpha
      · have h_burgessR_ext : burgessR A (Formula.and beta_w xi) C :=
          fun gamma hgamma => h_all_until beta_w hbeta_w gamma hgamma
        have h_snce_ext :=
          burgessR_implies_burgessRSince fc h_mcs_A h_mcs_C h_burgessR_ext alpha halpha
        exact snce_left_mono_thm fc h_mcs_C hImpl h_snce_ext
    exact h_not_r3_xi ⟨h_rset, h_rsince⟩
  obtain ⟨beta0, h_beta0, gamma0, h_gamma0, h_not_in_A⟩ := h_neg_until_exists
  have h_neg_until_in_A : (Formula.untl (Formula.and beta0 xi) gamma0).neg ∈ A := by
    rcases SetMaximalConsistent.negation_complete h_mcs_A
      (Formula.untl (Formula.and beta0 xi) gamma0) with h | h
    · exfalso; exact h_not_in_A h
    · exact h
  -- Step 2: Suppose for contradiction some finite L ⊆ seed derives ⊥.
  intro L hL ⟨d⟩
  have h_bx5_xe := self_accum_until_mcs fc h_mcs_A xi eta h_until
  -- h_key: For any b∈B (with ⊢ b→beta0), γ_hat∈C (with ⊢ γ_hat→gamma0), and alpha_list⊆A,
  -- produce event with F(event)∈A and event implies b, eta, untl(γ_hat, b),
  -- and snce(b∧χ_gen, α) for each α∈alpha_list where χ_gen = xi∧untl(xi,eta).
  suffices h_key :
      ∀ (b : Formula Atom) (hb : b ∈ B) (h_b_beta0 : DerivationTree fc [] (b.imp beta0))
      (γ_hat : Formula Atom) (hγ : γ_hat ∈ C) (h_γ_gamma0 : DerivationTree fc [] (γ_hat.imp gamma0))
      (alpha_list : List (Formula Atom)) (h_alphas : ∀ α ∈ alpha_list, α ∈ A),
      Σ' (event : Formula Atom),
        Formula.someFuture event ∈ A ×'
        DerivationTree fc [] (event.imp b) ×'
        DerivationTree fc [] (event.imp eta) ×'
        DerivationTree fc [] (event.imp (Formula.untl b γ_hat)) ×'
        (∀ α ∈ alpha_list, DerivationTree fc []
          (event.imp (Formula.snce (Formula.and b (Formula.and xi (Formula.untl xi eta))) α))) by
    -- Extract B-guards and A-events from L
    let b_list_raw := (l27CollectGuards fc h_B_dcs xi eta L hL).val
    have hb_list : ∀ g ∈ b_list_raw, g ∈ B := (l27CollectGuards fc h_B_dcs xi eta L hL).property
    let b_list := beta0 :: b_list_raw
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact h_beta0
      · exact hb_list g h
    let a_list := l27AEventList fc xi eta L hL
    have ha_list : ∀ α ∈ a_list, α ∈ A := fun α hα => l27_a_event_list_mem fc hα
    -- Form compressed formulas (gamma0 alone suffices since no untl in seed)
    let b := listConj fc b_list
    let γ_hat := gamma0
    have hb_B : b ∈ B := list_conj_mem_dcs fc h_B_dcs b_list hb_list'
    have hγ_C : γ_hat ∈ C := h_gamma0
    have h_b_to_beta0 : DerivationTree fc [] (b.imp beta0) :=
      listConjImpliesElem fc b_list beta0 (List.mem_cons.mpr (Or.inl rfl))
    have h_γ_to_gamma0 : DerivationTree fc [] (γ_hat.imp gamma0) := identity gamma0
    -- Apply h_key
    obtain ⟨event, h_F_event, h_ev_b, h_ev_eta, _h_ev_untl, h_ev_snce⟩ :=
      h_key b hb_B h_b_to_beta0 γ_hat hγ_C h_γ_to_gamma0 a_list ha_list
    -- Show event implies each element of L (3-way case split)
    let χ_gen := Formula.and xi (Formula.untl xi eta)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree fc [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      -- Case 1: φ ∈ B
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_raw : φ ∈ b_list_raw :=
          l27_collect_guards_mem_of_B fc h_B_dcs xi eta L hL φ hφ h_B_case
        have h_φ_in_b : φ ∈ b_list := List.mem_cons.mpr (Or.inr h_φ_in_raw)
        have h_b_to_φ : DerivationTree fc [] (b.imp φ) := listConjImpliesElem fc b_list φ h_φ_in_b
        have h_ev_to_φ : DerivationTree fc [] (event.imp φ) := impTrans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · -- Case 2: φ = eta
        by_cases h_eta : φ = eta
        · subst h_eta
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · -- Case 3: φ = snce(β'∧xi, α') with β' ∈ B
          by_cases h_snce5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce (Formula.and β' xi) α
          · let β' := Classical.choose h_snce5
            have hβ' : β' ∈ B := (Classical.choose_spec h_snce5).1
            let α' := Classical.choose (Classical.choose_spec h_snce5).2
            have hα' : α' ∈ A := (Classical.choose_spec (Classical.choose_spec h_snce5).2).1
            have h_eq : φ = Formula.snce (Formula.and β' xi) α' :=
              (Classical.choose_spec (Classical.choose_spec h_snce5).2).2
            have h_φ_eq_snce5 : Formula.snce (Formula.and β' xi) α' ∈ L := by rw [←h_eq]; exact hφ
            rw [h_eq]
            by_cases h_snce5_B : Formula.snce (Formula.and β' xi) α' ∈ B
            · -- In B: treat as B-element
              have h_in_raw := l27_collect_guards_mem_of_B fc h_B_dcs xi eta L hL
                (Formula.snce (Formula.and β' xi) α') h_φ_eq_snce5 h_snce5_B
              have h_in_b : Formula.snce (Formula.and β' xi) α' ∈ b_list :=
                List.mem_cons.mpr (Or.inr h_in_raw)
              have h_b_imp : DerivationTree fc [] (b.imp (Formula.snce (Formula.and β' xi) α')) :=
                listConjImpliesElem fc b_list (Formula.snce (Formula.and β' xi) α') h_in_b
              have h_ev_imp := impTrans h_ev_b h_b_imp
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_ev_imp (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
            · -- Not in B: use monotonicity
              have h_α'_in_a :=
                @l27_a_event_list_α_mem_xi _ fc A B C xi eta L hL β' α' h_φ_eq_snce5 hβ' hα'
              have h_ev_snce_α' := h_ev_snce α' h_α'_in_a
              have h_β'_in_raw := l27_collect_guards_mem_of_snce_xi fc h_B_dcs xi eta L hL
                β' α' h_φ_eq_snce5 hβ' hα' h_snce5_B
              have h_β'_in_b : β' ∈ b_list := List.mem_cons.mpr (Or.inr h_β'_in_raw)
              have h_b_to_β' : DerivationTree fc [] (b.imp β') :=
                listConjImpliesElem fc b_list β' h_β'_in_b
              have h_bχ_to_β'xi :
                  DerivationTree fc [] ((Formula.and b χ_gen).imp (Formula.and β' xi)) := by
                have h1 : DerivationTree fc [] _ := impTrans (lceImp b χ_gen) h_b_to_β'
                have h2 : DerivationTree fc [] _ :=
                  impTrans (rceImp b χ_gen) (lceImp xi (Formula.untl xi eta))
                exact combineImpConj h1 h2
              have h_mono :=
                snceLeftMonoDeriv fc (Formula.and b χ_gen) α' (Formula.and β' xi) h_bχ_to_β'xi
              have h_chain := impTrans h_ev_snce_α' h_mono
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · -- Contradiction: φ must be in one of the three sets
            exfalso
            simp [lemma27Seed, h_B_case, h_eta, h_snce5] at h_φ_seed
    -- Derive contradiction.
    have d_event : DerivationTree fc [event] Formula.bot :=
      derivationFromImplied fc [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_F_mem fc h_mcs_A event h_F_event
    exact inconsistent_singleton_false fc h_event_cons d_event
  -- Prove h_key: the generalized BX5+BX7+BX13 chain helper.
  intro b hb h_b_beta0 γ_hat hγ h_γ_gamma0 alpha_list h_alphas
  have h_untl_bg : Formula.untl b γ_hat ∈ A := h_r3.1 b hb γ_hat hγ
  have h_bx5_bg := self_accum_until_mcs fc h_mcs_A b γ_hat h_untl_bg
  let φ_gen := Formula.and b (Formula.untl b γ_hat)
  let χ_gen := Formula.and xi (Formula.untl xi eta)
  have h_bx7_gen := linear_until_mcs fc h_mcs_A φ_gen γ_hat χ_gen eta h_bx5_bg h_bx5_xe
  have h_guard_to_b0xi :
      DerivationTree fc [] ((Formula.and φ_gen χ_gen).imp (Formula.and beta0 xi)) := by
    have h1 : DerivationTree fc [] _ :=
      impTrans (impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.untl b γ_hat))) h_b_beta0
    have h2 : DerivationTree fc [] _ :=
      impTrans (rceImp φ_gen χ_gen) (lceImp xi (Formula.untl xi eta))
    exact combineImpConj h1 h2
  have h_D3_gen : Formula.untl (Formula.and φ_gen χ_gen) (Formula.and φ_gen eta) ∈ A := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_rm : DerivationTree fc [] ((Formula.and γ_hat eta).imp gamma0) :=
        impTrans (lceImp γ_hat eta) h_γ_gamma0
      have h_contra := right_mono_until_mcs fc h_mcs_A h_rm
        (untl_left_mono_thm fc h_mcs_A h_guard_to_b0xi h_D1)
      exact SetMaximalConsistent.neg_excludes h_mcs_A _ h_neg_until_in_A h_contra
    · exfalso
      have h_rm : DerivationTree fc [] ((Formula.and γ_hat χ_gen).imp gamma0) :=
        impTrans (lceImp γ_hat χ_gen) h_γ_gamma0
      have h_contra := right_mono_until_mcs fc h_mcs_A h_rm
        (untl_left_mono_thm fc h_mcs_A h_guard_to_b0xi h_D2)
      exact SetMaximalConsistent.neg_excludes h_mcs_A _ h_neg_until_in_A h_contra
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iteratedEnrichment fc h_mcs_A guard alpha_list h_alphas base_event h_D3_gen
  let event := evt.event'
  have h_F_event : Formula.someFuture event ∈ A := until_implies_F_mcs fc h_mcs_A evt.hUntl
  have h_ev_base := evt.hImpl
  have h_ev_b : DerivationTree fc [] (event.imp b) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (lceImp b (Formula.untl b γ_hat)))
  have h_ev_eta : DerivationTree fc [] (event.imp eta) :=
    impTrans h_ev_base (rceImp φ_gen eta)
  have h_ev_untl : DerivationTree fc [] (event.imp (Formula.untl b γ_hat)) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (rceImp b (Formula.untl b γ_hat)))
  have h_ev_snce : ∀ α ∈ alpha_list,
      DerivationTree fc [] (event.imp (Formula.snce (Formula.and b χ_gen) α)) := by
    intro α hα
    have h_snce_guard := evt.hSnce α hα
    have h_guard_to_bχ : DerivationTree fc [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree fc [] _ :=
        impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.untl b γ_hat))
      have h2 : DerivationTree fc [] _ := rceImp φ_gen χ_gen
      exact combineImpConj h1 h2
    exact impTrans h_snce_guard (snceLeftMonoDeriv fc guard α (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_F_event, h_ev_b, h_ev_eta, h_ev_untl, h_ev_snce⟩


/-- **Lemma 2.7** (Burgess 1982 p.372): Given BurgessR3Maximal(A, B, C) with
untl(xi, eta) ∈ A and xi ∉ B (guard not in B), construct MCS D with eta ∈ D
(event in D) and B' with B ⊆ B' and xi ∈ B' (guard in B').

The Zorn seed for B' is DC(B ∪ {xi}) (not just B), which ensures xi ∈ B'.
This requires the guard conjunction theorem (burgessR_conj) to derive
burgessR3(A, DC(B ∪ {xi}), D) via dc_delta_B_burgessR3.

Convention: untl(xi, eta) = U(eta, xi) in Burgess.
  xi = guard (Burgess η), eta = event (Burgess ξ).
  Burgess: U(ξ,η) ∈ A, η ∉ B, ξ ∈ D, η ∈ B', B ⊆ B'. -/
theorem lemma_2_7 (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : Formula.untl xi eta ∈ A)
    (h_xi_not_B : xi ∉ B) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal fc A B' D ∧
      BurgessR3Maximal fc D B'' C ∧
      SetMaximalConsistent fc D ∧
      eta ∈ D ∧
      B ⊆ B' ∧
      B ⊆ D ∧
      B ⊆ B'' ∧
      xi ∈ B' := by
  -- Step 1: The D0 seed is consistent
  have h_seed_cons :=
    lemma_2_7_seed_consistent fc h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc xi eta h_until h_xi_not_B
  -- Step 2: Lindenbaum-extend to MCS D
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  -- Step 3: Extract key memberships from seed
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma27Seed fc A B C xi eta; simp [lemma27Seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma27Seed fc A B C xi eta; simp [lemma27Seed, hφ]
  -- Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  -- Xu 3.2.1(i): untl(γ, β) ∈ B for all β ∈ B, γ ∈ C. Since B ⊆ D: untl(γ, β) ∈ D.
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl β γ ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until fc h_mcs_A h_mcs_C h_r3m hβ hγ)
  -- Xu 3.2.1(ii): snce(α, β) ∈ B for all β ∈ B, α ∈ A. Since B ⊆ D: snce(α, β) ∈ D.
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce β α ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since fc h_mcs_A h_mcs_C h_r3m hβ hα)
  -- Step 4: Establish burgessR3(D, B, C) from Until formulas
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  -- burgessRSince(C, B, D) follows from burgessR via Lemma 2.3
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  -- Step 5: Establish burgessR3(A, B, D) from seed Since formulas
  -- snce(β, α) ∈ D for all β ∈ B, α ∈ A gives burgessRSetSince(D, B, A)
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  -- burgessR(A, β, D) follows from burgessRSince via Lemma 2.3 backward
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Step 5b: Extract snce(β∧xi, α) ∈ D from the 5th seed component
  -- (xi = guard = Burgess η; the 5th component is S(α, β∧η) in Burgess)
  have h_snce_conj_xi_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce (Formula.and β xi) α ∈ D := by
    intro β hβ α hα; apply h_sup
    show Formula.snce (Formula.and β xi) α ∈ lemma27Seed fc A B C xi eta
    simp only [lemma27Seed, Set.mem_union, Set.mem_ofPred_eq]; right; exact ⟨β, hβ, α, hα, rfl⟩
  -- Step 5c: Derive snce(xi, α) ∈ D for all α ∈ A (via left_mono_since_H)
  -- From snce(β∧xi, α) ∈ D and ⊢ (β∧xi) → xi: snce(xi, α) ∈ D
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_snce_xi_D : ∀ α ∈ A, Formula.snce xi α ∈ D := by
    intro α hα
    have hImpl : DerivationTree fc [] ((Formula.and β₀ xi).imp xi) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.rceImp β₀ xi
    exact snce_left_mono_thm fc h_D_mcs hImpl (h_snce_conj_xi_D β₀ hβ₀ α hα)
  -- Step 5d: Derive untl(xi, δ) ∈ A for all δ ∈ D (via burgessRSince_implies_burgessR)
  -- snce(xi, α) ∈ D for all α ∈ A gives burgessRSince(D, xi, A)
  have h_burgessRSince_xi : burgessRSince D xi A := h_snce_xi_D
  have h_burgessR_xi : burgessR A xi D :=
    burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs h_burgessRSince_xi
  -- Step 6: Derive burgessR(A, β∧xi, D) for all β ∈ B using guard conjunction
  have h_burgessR_conj : ∀ β ∈ B, burgessR A (Formula.and β xi) D := by
    intro β hβ
    exact burgessR_conj fc h_mcs_A (h_rSet_A β hβ) h_burgessR_xi
  -- Step 6b: Derive untl(β∧xi, δ) ∈ A for all β ∈ B, δ ∈ D
  have h_until_conj : ∀ β ∈ B, ∀ δ ∈ D, Formula.untl (Formula.and β xi) δ ∈ A := by
    intro β hβ δ hδ
    exact h_burgessR_conj β hβ δ hδ
  -- Step 6c: Apply dc_delta_B_burgessR3 to get burgessR3(A, DC({xi} ∪ B), D)
  have h_r3_DC_ABD : burgessR3 A (deductiveClosure fc ({xi} ∪ B)) D :=
    dc_delta_B_burgessR3 fc h_mcs_A h_D_mcs h_B_dcs h_r3_ABD h_until_conj h_snce_conj_xi_D
  -- Step 6d: DC({xi} ∪ B) is CUD (always true, no consistency needed)
  have h_DC_cud : ClosedUnderDerivation fc (deductiveClosure fc ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation fc _
  -- Step 6e: BurgessR3Maximal via Zorn from DC({xi} ∪ B) — gives xi ∈ B'
  obtain ⟨B', h_DC_sub_B', _, h_B'_max⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_D_mcs
    h_DC_cud h_r3_DC_ABD
  obtain ⟨B'', h_B_sub_B'', _, h_B''_max⟩ := burgessR3Maximal_extension_exists fc h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  -- Extract B ⊆ B' from B ⊆ {xi} ∪ B ⊆ DC({xi} ∪ B) ⊆ B'
  have h_B_sub_DC : B ⊆ deductiveClosure fc ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure fc _ (Set.mem_union_right _ hφ)
  have h_B_sub_B' : B ⊆ B' := Set.Subset.trans h_B_sub_DC h_DC_sub_B'
  -- Extract xi ∈ B' from {xi} ⊆ DC({xi} ∪ B) ⊆ B'
  have h_xi_in_DC : xi ∈ deductiveClosure fc ({xi} ∪ B) :=
    subset_deductiveClosure fc _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B' : xi ∈ B' := h_DC_sub_B' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_B', h_B_sub_D,
    h_B_sub_B'', h_xi_in_B'⟩


/-- **Lemma 2.8 seed consistency** (Burgess 1982 p.372):
The same seed as Lemma 2.7 (3 components after Xu 3.2.1 simplification), but
consistency proved using ¬(eta ∨ (xi ∧ untl(xi, eta))) ∈ C instead of xi ∉ B. -/
theorem lemma_2_8_seed_consistent (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (_h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (_h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : Formula.untl xi eta ∈ A)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.untl xi eta))).neg ∈ C) :
    SetConsistent fc (lemma27Seed fc A B C xi eta) := by
  have h_r3 : burgessR3 A B C := h_r3m.2.1
  set γ' := (Formula.or eta (Formula.and xi (Formula.untl xi eta))).neg with γ'_def
  have h_γ'_to_neg_eta : DerivationTree fc [] (γ'.imp eta.neg) :=
    impTrans (liftBase fc (demorganDisjNegForward eta (Formula.and xi (Formula.untl xi eta))))
      (lceImp eta.neg (Formula.and xi (Formula.untl xi eta)).neg)
  have h_γ'_to_neg_chi : DerivationTree fc [] (γ'.imp (Formula.and xi (Formula.untl xi eta)).neg) :=
    impTrans (liftBase fc (demorganDisjNegForward eta (Formula.and xi (Formula.untl xi eta))))
      (rceImp eta.neg (Formula.and xi (Formula.untl xi eta)).neg)
  have h_bx5_xe := self_accum_until_mcs fc h_mcs_A xi eta h_until
  suffices h_key : ∀ (b : Formula Atom) (hb : b ∈ B)
      (γ_hat : Formula Atom) (hγ : γ_hat ∈ C) (h_γ_to_γ' : DerivationTree fc [] (γ_hat.imp γ'))
      (alpha_list : List (Formula Atom)) (h_alphas : ∀ α ∈ alpha_list, α ∈ A),
      Σ' (event : Formula Atom),
        Formula.someFuture event ∈ A ×'
        DerivationTree fc [] (event.imp b) ×'
        DerivationTree fc [] (event.imp eta) ×'
        DerivationTree fc [] (event.imp (Formula.untl b γ_hat)) ×'
        (∀ α ∈ alpha_list, DerivationTree fc []
          (event.imp (Formula.snce (Formula.and b (Formula.and xi (Formula.untl xi eta))) α))) by
    intro L hL ⟨d⟩
    let b_list_raw := (l27CollectGuards fc h_B_dcs xi eta L hL).val
    have hb_list : ∀ g ∈ b_list_raw, g ∈ B := (l27CollectGuards fc h_B_dcs xi eta L hL).property
    let a_list := l27AEventList fc xi eta L hL
    have ha_list : ∀ α ∈ a_list, α ∈ A := fun α hα => l27_a_event_list_mem fc hα
    -- b_list with ⊤ prefix for nonemptiness
    let b_list_full := (Formula.bot.imp Formula.bot) :: b_list_raw
    have hb_list_full : ∀ g ∈ b_list_full, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact cud_contains_theorems h_B_dcs (identity (Formula.bot : Formula Atom))
      · exact hb_list g h
    let b := listConj fc b_list_full
    -- γ_hat = γ' (the neg-disjunction witness)
    let γ_hat := γ'
    have hb_B : b ∈ B := list_conj_mem_dcs fc h_B_dcs b_list_full hb_list_full
    have hγ_C : γ_hat ∈ C := h_neg_disj
    have h_γhat_to_γ' : DerivationTree fc [] (γ_hat.imp γ') := identity γ'
    obtain ⟨event, h_F_event, h_ev_b, h_ev_eta, _h_ev_untl, h_ev_snce⟩ :=
      h_key b hb_B γ_hat hγ_C h_γhat_to_γ' a_list ha_list
    -- Show event implies each element of L (3-way case split)
    let χ_gen := Formula.and xi (Formula.untl xi eta)
    have h_event_implies_L : ∀ φ ∈ L, DerivationTree fc [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_raw : φ ∈ b_list_raw :=
          l27_collect_guards_mem_of_B fc h_B_dcs xi eta L hL φ hφ h_B_case
        have h_φ_in_b : φ ∈ b_list_full := List.mem_cons.mpr (Or.inr h_φ_in_raw)
        have h_b_to_φ : DerivationTree fc [] (b.imp φ) :=
          listConjImpliesElem fc b_list_full φ h_φ_in_b
        have h_ev_to_φ : DerivationTree fc [] (event.imp φ) := impTrans h_ev_b h_b_to_φ
        exact DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta : φ = eta
        · subst h_eta
          exact DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
        · by_cases h_snce5 : ∃ β' ∈ B, ∃ α ∈ A, φ = Formula.snce (Formula.and β' xi) α
          · let β' := Classical.choose h_snce5
            have hβ' : β' ∈ B := (Classical.choose_spec h_snce5).1
            let α' := Classical.choose (Classical.choose_spec h_snce5).2
            have hα' : α' ∈ A := (Classical.choose_spec (Classical.choose_spec h_snce5).2).1
            have h_eq : φ = Formula.snce (Formula.and β' xi) α' :=
              (Classical.choose_spec (Classical.choose_spec h_snce5).2).2
            have h_φ_eq_snce5 : Formula.snce (Formula.and β' xi) α' ∈ L := by rw [←h_eq]; exact hφ
            rw [h_eq]
            by_cases h_snce5_B : Formula.snce (Formula.and β' xi) α' ∈ B
            · have h_in_raw := l27_collect_guards_mem_of_B fc h_B_dcs xi eta L hL
                (Formula.snce (Formula.and β' xi) α') h_φ_eq_snce5 h_snce5_B
              have h_in_b : Formula.snce (Formula.and β' xi) α' ∈ b_list_full :=
                List.mem_cons.mpr (Or.inr h_in_raw)
              have h_b_imp : DerivationTree fc [] (b.imp (Formula.snce (Formula.and β' xi) α')) :=
                listConjImpliesElem fc b_list_full (Formula.snce (Formula.and β' xi) α') h_in_b
              have h_ev_imp := impTrans h_ev_b h_b_imp
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_ev_imp (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
            · have h_α'_in_a :=
                @l27_a_event_list_α_mem_xi _ fc A B C xi eta L hL β' α' h_φ_eq_snce5 hβ' hα'
              have h_ev_snce_α' := h_ev_snce α' h_α'_in_a
              have h_β'_in_raw := l27_collect_guards_mem_of_snce_xi fc h_B_dcs xi eta L hL
                β' α' h_φ_eq_snce5 hβ' hα' h_snce5_B
              have h_β'_in_b : β' ∈ b_list_full := List.mem_cons.mpr (Or.inr h_β'_in_raw)
              have h_b_to_β' : DerivationTree fc [] (b.imp β') :=
                listConjImpliesElem fc b_list_full β' h_β'_in_b
              have h_bχ_to_β'xi :
                  DerivationTree fc [] ((Formula.and b χ_gen).imp (Formula.and β' xi)) := by
                have h1 : DerivationTree fc [] _ := impTrans (lceImp b χ_gen) h_b_to_β'
                have h2 : DerivationTree fc [] _ :=
                  impTrans (rceImp b χ_gen) (lceImp xi (Formula.untl xi eta))
                exact combineImpConj h1 h2
              have h_mono :=
                snceLeftMonoDeriv fc (Formula.and b χ_gen) α' (Formula.and β' xi) h_bχ_to_β'xi
              have h_chain := impTrans h_ev_snce_α' h_mono
              exact DerivationTree.modus_ponens _ _ _
                (DerivationTree.weakening [] _ _ h_chain (List.nil_subset _))
                (DerivationTree.assumption _ _ (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp [lemma27Seed, h_B_case, h_eta, h_snce5] at h_φ_seed
    have d_event : DerivationTree fc [event] Formula.bot :=
      derivationFromImplied fc [event] L Formula.bot h_event_implies_L d
    have h_event_cons := consistent_of_F_mem fc h_mcs_A event h_F_event
    exact inconsistent_singleton_false fc h_event_cons d_event
  -- Prove h_key: BX5+BX7+BX13 chain with D1/D2 eliminated via γ'
  intro b hb γ_hat hγ h_γ_to_γ' alpha_list h_alphas
  have h_untl_bg : Formula.untl b γ_hat ∈ A := h_r3.1 b hb γ_hat hγ
  have h_bx5_bg := self_accum_until_mcs fc h_mcs_A b γ_hat h_untl_bg
  let φ_gen := Formula.and b (Formula.untl b γ_hat)
  let χ_gen := Formula.and xi (Formula.untl xi eta)
  have h_bx7_gen := linear_until_mcs fc h_mcs_A φ_gen γ_hat χ_gen eta h_bx5_bg h_bx5_xe
  have h_D3_gen : Formula.untl (Formula.and φ_gen χ_gen) (Formula.and φ_gen eta) ∈ A := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_event_to_bot : DerivationTree fc [] ((Formula.and γ_hat eta).imp Formula.bot) := by
        have h1 : DerivationTree fc [] ((Formula.and γ_hat eta).imp eta.neg) :=
          impTrans (lceImp γ_hat eta) (impTrans h_γ_to_γ' h_γ'_to_neg_eta)
        have h2 : DerivationTree fc [] _ := rceImp γ_hat eta
        let PConj := Formula.and γ_hat eta
        have d1 : DerivationTree fc [PConj] eta.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree fc [PConj] eta := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_F_bot := F_mono_mcs fc h_mcs_A h_event_to_bot
        (until_implies_F_mcs fc h_mcs_A h_D1)
      have h_G_top : Formula.allFuture (Formula.bot.imp Formula.bot) ∈ A :=
        theoremInMcsFc h_mcs_A (DerivationTree.temporal_necessitation _
          (identity (Formula.bot : Formula Atom)))
      exact someFuture_allFuture_neg_absurd h_mcs_A Formula.bot h_F_bot h_G_top
    · exfalso
      have h_event_to_bot : DerivationTree fc [] ((Formula.and γ_hat χ_gen).imp Formula.bot) := by
        have h1 : DerivationTree fc [] ((Formula.and γ_hat χ_gen).imp χ_gen.neg) :=
          impTrans (lceImp γ_hat χ_gen) (impTrans h_γ_to_γ' h_γ'_to_neg_chi)
        have h2 : DerivationTree fc [] _ := rceImp γ_hat χ_gen
        let PConj := Formula.and γ_hat χ_gen
        have d1 : DerivationTree fc [PConj] χ_gen.neg := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h1 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        have d2 : DerivationTree fc [PConj] χ_gen := DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ h2 (List.nil_subset _))
          (DerivationTree.assumption _ PConj (by simp))
        exact deductionTheorem [] PConj Formula.bot (DerivationTree.modus_ponens _ _ _ d1 d2)
      have h_F_bot := F_mono_mcs fc h_mcs_A h_event_to_bot
        (until_implies_F_mcs fc h_mcs_A h_D2)
      have h_G_top : Formula.allFuture (Formula.bot.imp Formula.bot) ∈ A :=
        theoremInMcsFc h_mcs_A (DerivationTree.temporal_necessitation _
          (identity (Formula.bot : Formula Atom)))
      exact someFuture_allFuture_neg_absurd h_mcs_A Formula.bot h_F_bot h_G_top
    · exact h_D3
  let guard := Formula.and φ_gen χ_gen
  let base_event := Formula.and φ_gen eta
  let evt := iteratedEnrichment fc h_mcs_A guard alpha_list h_alphas base_event h_D3_gen
  let event := evt.event'
  have h_F_event : Formula.someFuture event ∈ A := until_implies_F_mcs fc h_mcs_A evt.hUntl
  have h_ev_base := evt.hImpl
  have h_ev_b : DerivationTree fc [] (event.imp b) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (lceImp b (Formula.untl b γ_hat)))
  have h_ev_eta : DerivationTree fc [] (event.imp eta) :=
    impTrans h_ev_base (rceImp φ_gen eta)
  have h_ev_untl : DerivationTree fc [] (event.imp (Formula.untl b γ_hat)) :=
    impTrans h_ev_base (impTrans (lceImp φ_gen eta) (rceImp b (Formula.untl b γ_hat)))
  have h_ev_snce : ∀ α ∈ alpha_list,
      DerivationTree fc [] (event.imp (Formula.snce (Formula.and b χ_gen) α)) := by
    intro α hα
    have h_snce_guard := evt.hSnce α hα
    have h_guard_to_bχ : DerivationTree fc [] (guard.imp (Formula.and b χ_gen)) := by
      have h1 : DerivationTree fc [] _ :=
        impTrans (lceImp φ_gen χ_gen) (lceImp b (Formula.untl b γ_hat))
      have h2 : DerivationTree fc [] _ := rceImp φ_gen χ_gen
      exact combineImpConj h1 h2
    exact impTrans h_snce_guard (snceLeftMonoDeriv fc guard α (Formula.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_F_event, h_ev_b, h_ev_eta, h_ev_untl, h_ev_snce⟩

/-- **Lemma 2.8** (Burgess 1982 p.372): Given BurgessR3Maximal(A, B, C) with
untl(xi, eta) ∈ A and ¬(eta ∨ (xi ∧ untl(xi, eta))) ∈ C, construct MCS D
with eta ∈ D splitting the R3 pair. Also returns xi ∈ B' (guard in B')
via DC(B ∪ {xi}) Zorn seed, matching lemma_2_7's strengthening.

Convention: untl(xi, eta) = U(eta, xi) in Burgess.
  xi = guard (Burgess η), eta = event (Burgess ξ). -/
theorem lemma_2_8 (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_r3m : BurgessR3Maximal fc A B C)
    (h_B_dcs : ClosedUnderDerivation fc B)
    (h_gc : gContent A ⊆ C)
    (xi eta : Formula Atom)
    (h_until : Formula.untl xi eta ∈ A)
    (h_neg_disj : (Formula.or eta (Formula.and xi (Formula.untl xi eta))).neg ∈ C) :
    ∃ B' D B'' : Set (Formula Atom),
      BurgessR3Maximal fc A B' D ∧
      BurgessR3Maximal fc D B'' C ∧
      SetMaximalConsistent fc D ∧
      eta ∈ D ∧
      B ⊆ D ∧
      B ⊆ B' ∧
      B ⊆ B'' ∧
      xi ∈ B' := by
  -- Step 1: Seed consistency (Lemma 2.8 variant)
  have h_seed_cons := lemma_2_8_seed_consistent fc h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_until h_neg_disj
  -- Step 2: Lindenbaum-extend to MCS D (same as 2.7)
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  -- Step 3: Extract key memberships from seed
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma27Seed fc A B C xi eta; simp [lemma27Seed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma27Seed fc A B C xi eta; simp [lemma27Seed, hφ]
  -- Until/Since formulas in D via Xu 3.2.1 + B ⊆ D
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, Formula.untl β γ ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (xu_lemma_3_2_1_until fc h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce β α ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (xu_lemma_3_2_1_since fc h_mcs_A h_mcs_C h_r3m hβ hα)
  -- Step 4: burgessR3(D, B, C) from Until formulas
  have h_rSet_D : burgessRSet D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince C B D := by
    intro β hβ
    exact burgessR_implies_burgessRSince fc h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  -- Step 5: burgessR3(A, B, D) from Since formulas
  have h_rSetSince_A : burgessRSetSince D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet A B D := by
    intro β hβ
    exact burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  -- Step 5b: Extract snce(β∧xi, α) ∈ D from the 5th seed component (same as lemma_2_7)
  have h_snce_conj_xi_D : ∀ β ∈ B, ∀ α ∈ A, Formula.snce (Formula.and β xi) α ∈ D := by
    intro β hβ α hα; apply h_sup
    show Formula.snce (Formula.and β xi) α ∈ lemma27Seed fc A B C xi eta
    simp only [lemma27Seed, Set.mem_union, Set.mem_ofPred_eq]; right; exact ⟨β, hβ, α, hα, rfl⟩
  -- Step 5c: Derive snce(xi, α) ∈ D for all α ∈ A
  have h_B_nonempty : ∃ β₀ : Formula Atom, β₀ ∈ B := by
    exact ⟨Formula.bot.imp Formula.bot, cud_contains_theorems h_r3m.1
      (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_snce_xi_D : ∀ α ∈ A, Formula.snce xi α ∈ D := by
    intro α hα
    have hImpl : DerivationTree fc [] ((Formula.and β₀ xi).imp xi) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.rceImp β₀ xi
    exact snce_left_mono_thm fc h_D_mcs hImpl (h_snce_conj_xi_D β₀ hβ₀ α hα)
  -- Step 5d: Derive burgessR(A, xi, D)
  have h_burgessRSince_xi : burgessRSince D xi A := h_snce_xi_D
  have h_burgessR_xi : burgessR A xi D :=
    burgessRSince_implies_burgessR fc h_mcs_A h_D_mcs h_burgessRSince_xi
  -- Step 6: Guard conjunction + DC(B ∪ {xi}) Zorn seed (same as lemma_2_7)
  have h_burgessR_conj : ∀ β ∈ B, burgessR A (Formula.and β xi) D := by
    intro β hβ
    exact burgessR_conj fc h_mcs_A (h_rSet_A β hβ) h_burgessR_xi
  have h_until_conj : ∀ β ∈ B, ∀ δ ∈ D, Formula.untl (Formula.and β xi) δ ∈ A := by
    intro β hβ δ hδ
    exact h_burgessR_conj β hβ δ hδ
  have h_r3_DC_ABD : burgessR3 A (deductiveClosure fc ({xi} ∪ B)) D :=
    dc_delta_B_burgessR3 fc h_mcs_A h_D_mcs h_B_dcs h_r3_ABD h_until_conj h_snce_conj_xi_D
  -- DC({xi} ∪ B) is CUD (always true, no consistency needed)
  have h_DC_cud : ClosedUnderDerivation fc (deductiveClosure fc ({xi} ∪ B)) :=
    deductiveClosure_closed_under_derivation fc _
  obtain ⟨B', h_DC_sub_B', _, h_B'_max⟩ := burgessR3Maximal_extension_exists fc h_mcs_A h_D_mcs
    h_DC_cud h_r3_DC_ABD
  obtain ⟨B'', h_B_sub_B'', _, h_B''_max⟩ := burgessR3Maximal_extension_exists fc h_D_mcs h_mcs_C
    h_B_dcs h_r3_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure fc ({xi} ∪ B) :=
    fun φ hφ => subset_deductiveClosure fc _ (Set.mem_union_right _ hφ)
  have h_B_sub_B' : B ⊆ B' := Set.Subset.trans h_B_sub_DC h_DC_sub_B'
  have h_xi_in_DC : xi ∈ deductiveClosure fc ({xi} ∪ B) :=
    subset_deductiveClosure fc _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B' : xi ∈ B' := h_DC_sub_B' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_D, h_B_sub_B',
    h_B_sub_B'', h_xi_in_B'⟩


end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

end
