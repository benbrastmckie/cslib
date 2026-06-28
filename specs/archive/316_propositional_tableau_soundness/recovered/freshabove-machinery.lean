-- =============================================================================
-- RECOVERED: FreshAbove Freshness-Invariant Machinery
-- =============================================================================
-- Provenance: recovered from agent transcripts
--   a3a08e73a2f1aa90c  (plan-06 agent; CREATED FreshAbove and lemmas)
--   a9309a15c559f4aea  (follow-up agent; EXTENDED threading further)
-- Recovery date: 2026-06-24
-- Recovered by: cslib-implementation-agent (reconstruction task, task 316)
--
-- STATUS: UNVERIFIED — this code has NOT been build-checked.
--   A future session must paste these declarations into
--   Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean
--   at the designated insertion points (see report 07_freshabove-recovery.md)
--   and verify with `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`.
--
-- DEPENDENCY ORDER: declarations are listed in bottom-up dependency order,
--   i.e., each declaration appears before any that depends on it.
-- =============================================================================

/-! ## Freshness Invariant -/

/-- Branch freshness invariant (Fitting "new prefix" side-condition): all signed-formula
labels on `b` are strictly below `nw`, and all edge endpoints in `edges` are strictly
below `nw`.

This invariant is preserved by every expansion step and ensures that when the
F(→) world-creating rule introduces a fresh label `nwH` (the current `nextWorld` counter),
this label does not already appear on the branch or in the edge set. -/
-- STATUS: proved sorry-free in source (definition, no proof)
def FreshAbove (b : IBranch Atom) (edges : IEdges) (nw : Nat) : Prop :=
  (∀ sf ∈ b, sf.label < nw) ∧ (∀ c p : Nat, (c, p) ∈ edges → c < nw ∧ p < nw)

/-- `applyAllTImpRules` preserves `FreshAbove`: the T(φ→ψ) persistence rule only adds
`T(ψ)` at world labels already present on the branch, so no new labels are introduced. -/
-- STATUS: proved sorry-free in source (latest version from transcript a3a08e7 lines 842–872,
--   superseded clean variant without the verbatim `absurd` calls)
private lemma freshAbove_applyAllTImpRules (b : IBranch Atom) (edges : IEdges) (nw : Nat)
    (hfresh : FreshAbove b edges nw) :
    FreshAbove (applyAllTImpRules b edges) edges nw := by
  obtain ⟨hbounds, hedges⟩ := hfresh
  refine ⟨?_, hedges⟩
  intro sf hmem
  simp only [applyAllTImpRules, List.mem_append, List.mem_flatten, List.mem_filterMap] at hmem
  rcases hmem with hmem | ⟨newForms, ⟨sf', hmem', houter⟩, hmem_inner⟩
  · exact hbounds sf hmem
  · cases hsign : sf'.sign with
    | neg => simp only [hsign] at houter; simp at houter
    | pos =>
      cases hform : sf'.formula with
      | atom _ | bot | and _ _ | or _ _ =>
          simp only [hsign, hform] at houter; simp at houter
      | imp φ ψ =>
        simp only [hsign, hform] at houter
        split_ifs at houter with hemp
        · simp at houter
        · simp only [Bool.false_eq_true, hemp, ite_false, Option.some.injEq] at houter
          rw [← houter] at hmem_inner
          simp only [intTImpRule, List.mem_filterMap] at hmem_inner
          obtain ⟨w', hw'_mem, hw'_sf⟩ := hmem_inner
          simp only [List.mem_filter, List.mem_eraseDups, List.mem_map] at hw'_mem
          obtain ⟨⟨sf'', hmem'', hlab⟩, _⟩ := hw'_mem
          split_ifs at hw'_sf with hany1 hany2
          · simp at hw'_sf
          · simp only [Option.some.injEq] at hw'_sf
            rw [← hw'_sf]; simp only; rw [← hlab]
            exact hbounds sf'' hmem''
          · simp at hw'_sf

/-- The persistence fixpoint preserves `FreshAbove`. -/
-- STATUS: proved sorry-free in source (transcript a3a08e7 lines 874–884)
private lemma freshAbove_applyPersistenceFixpoint (b : IBranch Atom) (edges : IEdges) (nw : Nat)
    (fuel : Nat) (hfresh : FreshAbove b edges nw) :
    FreshAbove (applyPersistenceFixpoint b edges fuel) edges nw := by
  induction fuel generalizing b with
  | zero => simpa [applyPersistenceFixpoint] using hfresh
  | succ k ih =>
    simp only [applyPersistenceFixpoint]
    split_ifs
    · exact hfresh
    · exact ih _ (freshAbove_applyAllTImpRules b edges nw hfresh)

/-- A non-world-creating expansion step preserves `FreshAbove` when new forms use
existing labels (`sf'.label < nw` for all `sf' ∈ newForms`).

Used for T(∧) and F(∨) rules, which generate new signed formulas at the *same* world
label as the expanded formula. -/
-- STATUS: proved sorry-free in source (transcript a3a08e7 lines 886–897 / a3a08e7 lines 1096–1107)
-- NOTE: In transcript a3a08e7, this was called both `freshAbove_extendMany_none`
--   (in the first pass) and `freshAbove_extendMany` (in the second/final pass).
--   The name `freshAbove_extendMany` is the final intended name.
private lemma freshAbove_extendMany (b : IBranch Atom) (edges : IEdges) (nw : Nat)
    (newForms : List (ISF Atom))
    (hfresh : FreshAbove b edges nw)
    (hnew : ∀ sf' ∈ newForms, sf'.label < nw) :
    FreshAbove (Branch.extendMany b newForms) edges nw :=
  ⟨fun sf hmem => by
      simp only [Branch.extendMany, List.mem_append] at hmem
      rcases hmem with h | h
      · exact hnew sf h
      · exact hfresh.1 sf h,
    hfresh.2⟩

/-- The F(→) world-creating step produces `FreshAbove … (nw+1)` for the new branch
and extended edge set.

After the F(→) rule: new edge `(nw, parentLabel)` is added; new forms at `nw` (the
fresh world); old forms at labels `< nw`. Everything is `< nw + 1`. -/
-- STATUS: proved sorry-free in source (transcript a3a08e7 lines 899–918 / a3a08e7 lines 1109–1128)
-- NOTE: In the first pass, this was called `freshAbove_extendMany_some`. The final
--   name is `freshAbove_world_create`.
private lemma freshAbove_world_create (b : IBranch Atom) (edges : IEdges) (nw parentLabel : Nat)
    (newForms : List (ISF Atom))
    (hfresh : FreshAbove b edges nw)
    (hparent_lt : parentLabel < nw)
    (hnew : ∀ sf' ∈ newForms, sf'.label ≤ nw) :
    FreshAbove (Branch.extendMany b newForms) (edges ++ [(nw, parentLabel)]) (nw + 1) :=
  ⟨fun sf hmem => by
      simp only [Branch.extendMany, List.mem_append] at hmem
      rcases hmem with h | h
      · exact Nat.lt_succ_of_le (hnew sf h)
      · exact Nat.lt_succ_of_lt (hfresh.1 sf h),
    fun c p hmem => by
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with h | h
      · exact ⟨Nat.lt_succ_of_lt (hfresh.2 c p h).1,
               Nat.lt_succ_of_lt (hfresh.2 c p h).2⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨Nat.lt_succ_self _, Nat.lt_succ_of_lt hparent_lt⟩⟩

/-- When `FreshAbove b edges nw` holds and `∀ k ≠ nw, wo' k = wo k`,
then `MonotoneEdges wo' edges` follows from `MonotoneEdges wo edges`.

This is used for the `newEdge = none` (non-world-creating) case: the new world function
`wo'` agrees with `wo` on all existing edge endpoints (which are all `< nw`, hence `≠ nw`),
so monotonicity transfers. -/
-- STATUS: proved sorry-free in source (transcript a3a08e7 lines 1130–1267, the
--   `monotoneEdges_of_agree` lemma)
-- NOTE: This lemma was developed in a single session and reached a complete proof.
private lemma monotoneEdges_of_agree
    {World : Type*} [Preorder World]
    (wo wo' : Nat → World) (edges : IEdges) (nw : Nat)
    (hfresh_edges : ∀ c p, (c, p) ∈ edges → c < nw ∧ p < nw)
    (hagree : ∀ k, k ≠ nw → wo' k = wo k)
    (hmono : MonotoneEdges wo edges) :
    MonotoneEdges wo' edges := by
  intro w1 w2 hacc
  simp only [isAccessible] at hacc
  split_ifs at hacc with heq
  · simp only [beq_iff_eq] at heq; subst heq; exact le_refl _
  · simp only [heq, Bool.false_eq_true, ite_false] at hacc
    -- w1 ≠ w2; need wo' w1 ≤ wo' w2
    -- Show w2 is a child in edges (hence < nw) and w1 is a parent in edges (hence < nw)
    have hw2_child : ∃ p, (w2, p) ∈ edges := by
      have key : ∀ k start, isAccessible.go edges w2 start k = true → ∃ p, (w2, p) ∈ edges := by
        intro k
        induction k with
        | zero => simp [isAccessible.go]
        | succ m ih =>
          intro start hgo
          simp only [isAccessible.go, List.any_eq_true, List.mem_filterMap] at hgo
          obtain ⟨child, ⟨⟨c, p⟩, he, hfilt⟩, hchild⟩ := hgo
          simp only at hfilt
          split_ifs at hfilt with hcond
          · simp only [Option.some.injEq] at hfilt
            subst hfilt
            split_ifs at hchild with heq2
            · simp only [beq_iff_eq] at heq2; subst heq2
              exact ⟨start, he⟩
            · simp only [heq2, Bool.false_eq_true, ite_false] at hchild
              exact ih child hchild
          · simp at hfilt
      exact key _ w1 hacc
    have hw1_parent : ∃ c, (c, w1) ∈ edges := by
      have key : ∀ k start, isAccessible.go edges w2 start k = true → ∃ c, (c, start) ∈ edges := by
        intro k
        induction k with
        | zero => simp [isAccessible.go]
        | succ m ih =>
          intro start hgo
          simp only [isAccessible.go, List.any_eq_true, List.mem_filterMap] at hgo
          obtain ⟨child, ⟨⟨c, p⟩, he, hfilt⟩, _⟩ := hgo
          simp only at hfilt
          split_ifs at hfilt with hcond
          · simp only [Option.some.injEq] at hfilt
            subst hfilt
            simp only [beq_iff_eq] at hcond; subst hcond
            exact ⟨c, he⟩
          · simp at hfilt
      exact key _ w1 hacc
    obtain ⟨c_w1, hc_w1⟩ := hw1_parent
    obtain ⟨p_w2, hp_w2⟩ := hw2_child
    have hw1_lt : w1 < nw := (hfresh_edges c_w1 w1 hc_w1).2
    have hw2_lt : w2 < nw := (hfresh_edges w2 p_w2 hp_w2).1
    have hw1_ne : w1 ≠ nw := Nat.ne_of_lt hw1_lt
    have hw2_ne : w2 ≠ nw := Nat.ne_of_lt hw2_lt
    rw [hagree w1 hw1_ne, hagree w2 hw2_ne]
    exact hmono w1 w2 (by simp only [isAccessible, heq, Bool.false_eq_true, ite_false]; exact hacc)

-- =============================================================================
-- THREADING: intExpandBranches_closed_unsat with FreshAbove
-- =============================================================================
-- The declarations below are the threading edits to intExpandBranches_closed_unsat.
-- These are NOT standalone declarations — they are REPLACEMENT CONTENT for the
-- body of intExpandBranches_closed_unsat in Soundness.lean.
--
-- The latest version (from transcript a9309a15c559f4aea) uses a different FreshAbove
-- indexing form than transcript a3a08e7. See the recovery report for the distinction.
--
-- KEY ARCHITECTURAL DECISION (from transcript a9309a1):
-- FreshAbove is threaded as an INDEXED PREDICATE:
--   ∀ i (hi : i < branches.length), FreshAbove branches[i]
--       edgeSets[i]'(by omega) nextWorlds[i]'(by omega)
-- This is the CORRECT final form; the earlier a3a08e7 attempt also tried this shape
-- but had multiple iterations on the indexing proof. The a9309a1 version is cleaner.
-- =============================================================================

-- STATUS: The OUTER statement of intExpandBranches_closed_unsat was changed to add
-- a FreshAbove hypothesis. The latest form (from a9309a15c559f4aea block at ~L1506)
-- is reproduced below. This is the REPLACEMENT for the existing statement at L778.
--
-- !! DO NOT USE the version from a3a08e7 transcript block ~L119 which used a
-- `suffices`-based workaround with a dummy `(fun i hi => absurd hi ...)` — that was
-- an intermediate attempt, NOT the final design. The final design adds FreshAbove
-- directly to the PUBLIC signature of intExpandBranches_closed_unsat.

/-
-- PASTE THIS as the new signature/statement for intExpandBranches_closed_unsat
-- (replacing L778–L819 in Soundness.lean):

lemma intExpandBranches_closed_unsat
    {World : Type*} [Preorder World]
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (fuel : Nat)
    (closurePred : IBranch Atom → Bool)
    (closed_unsat : ∀ (worldOf : Nat → World) (b : IBranch Atom),
        closurePred b = true → ¬ intBranchSatisfied val botForces worldOf b) :
    ∀ (branches : List (IBranch Atom))
      (expandedSets : List (List (ISF Atom)))
      (nextWorlds : List Nat)
      (edgeSets : List IEdges),
      expandedSets.length = branches.length →
      nextWorlds.length = branches.length →
      edgeSets.length = branches.length →
      (∀ i (hi : i < branches.length), FreshAbove branches[i]
          edgeSets[i]'(by omega) nextWorlds[i]'(by omega)) →
      intExpandBranches branches expandedSets nextWorlds edgeSets fuel closurePred = .closed →
      ∀ (b : IBranch Atom) (edges : IEdges),
          (b, edges) ∈ branches.zip edgeSets →
          ∀ (worldOf : Nat → World),
          MonotoneEdges worldOf edges →
          ¬ intBranchSatisfied val botForces worldOf b := by
  suffices hcore : ∀ (fuel' : Nat)
      (branches : List (IBranch Atom))
      (expandedSets : List (List (ISF Atom)))
      (nextWorlds : List Nat)
      (edgeSets : List IEdges),
      expandedSets.length = branches.length →
      nextWorlds.length = branches.length →
      edgeSets.length = branches.length →
      (∀ i (hi : i < branches.length), FreshAbove branches[i]
          edgeSets[i]'(by omega) nextWorlds[i]'(by omega)) →
      intExpandBranches branches expandedSets nextWorlds edgeSets fuel' closurePred = .closed →
      ∀ (b : IBranch Atom) (edges : IEdges),
          (b, edges) ∈ branches.zip edgeSets →
          ∀ (worldOf : Nat → World),
          MonotoneEdges worldOf edges →
          ¬ intBranchSatisfied val botForces worldOf b by
    intro branches expandedSets nextWorlds edgeSets hlength_exp hlength_nw hlength_edges
        hbranches_fresh h b edges hbe worldOf hmono hsat
    exact hcore fuel branches expandedSets nextWorlds edgeSets
        hlength_exp hlength_nw hlength_edges hbranches_fresh
        h b edges hbe worldOf hmono hsat
  intro fuel'
  induction fuel' with
  | zero =>
    intro branches expandedSets nextWorlds edgeSets _ _ _ _ h b edges hzip worldOf _ hsat
    simp only [intExpandBranches] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hfind
      have hb : b ∈ branches := (List.of_mem_zip hzip).1
      have hfn := List.findSome?_eq_none_iff.mp hfind b hb
      split_ifs at hfn with hcl
      · exact closed_unsat worldOf b hcl hsat
  | succ fuel'' ih =>
    intro branches expandedSets nextWorlds edgeSets hlength_exp hlength_nw hlength_edges
        hbranches_fresh h b edges hzip worldOf hmono hsat
    suffices key : ∀ (pending : List (IBranch Atom))
        (pendingExp : List (List (ISF Atom)))
        (pendingNW : List Nat)
        (pendingEdges : List IEdges)
        (done : List (IBranch Atom))
        (doneExp : List (List (ISF Atom)))
        (doneNW : List Nat)
        (doneEdges : List IEdges),
        pendingExp.length = pending.length →
        pendingNW.length = pending.length →
        pendingEdges.length = pending.length →
        doneExp.length = done.length →
        doneNW.length = done.length →
        doneEdges.length = done.length →
        (∀ i (hi : i < pending.length), FreshAbove pending[i]
            pendingEdges[i]'(by omega) pendingNW[i]'(by omega)) →
        intExpandBranches.go closurePred fuel'' pending pendingExp pendingNW pendingEdges
            done doneExp doneNW doneEdges = .closed →
        ∀ bp edgesP, (bp, edgesP) ∈ pending.zip pendingEdges →
            ∀ (wo : Nat → World), MonotoneEdges wo edgesP →
            ¬ intBranchSatisfied val botForces wo bp from by
      simp only [intExpandBranches] at h
      exact key branches expandedSets nextWorlds edgeSets [] [] [] []
        hlength_exp hlength_nw hlength_edges (by simp) (by simp) (by simp)
        hbranches_fresh
        (by simpa [intExpandBranches] using h)
        b edges hzip worldOf hmono hsat
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingNW pendingEdges done doneExp doneNW doneEdges
        _ _ _ _ _ _ _ _ bp edgesP hzip_p
      simp only [List.zip_nil_left, List.mem_nil_iff] at hzip_p
    | cons bh bt ih_inner =>
      intro pendingExp pendingNW pendingEdges done doneExp doneNW doneEdges
        hlength_exp hlength_nw hlength_edges hdlength_exp hdlength_nw hdlength_edges
        hpfresh hgo bp edgesP hzip_p wo hmono_p hsat_p
      simp only [List.length_cons] at hlength_exp hlength_nw hlength_edges
      cases hpendingExp : pendingExp with
      | nil => simp [hpendingExp] at hlength_exp
      | cons eH eT =>
        cases hpendingNW : pendingNW with
        | nil => simp [hpendingNW] at hlength_nw
        | cons nwH nwT =>
          cases hpendingEdges : pendingEdges with
          | nil => simp [hpendingEdges] at hlength_edges
          | cons edgesH edgesT =>
            rw [hpendingExp] at hlength_exp
            rw [hpendingNW] at hlength_nw
            rw [hpendingEdges] at hlength_edges
            simp only [List.length_cons] at hlength_exp hlength_nw hlength_edges
            replace hlength_exp : eT.length = bt.length := by omega
            replace hlength_nw : nwT.length = bt.length := by omega
            replace hlength_edges : edgesT.length = bt.length := by omega
            rw [hpendingEdges] at hzip_p
            rw [hpendingExp, hpendingNW, hpendingEdges] at hgo
            simp only [List.zip_cons_cons, List.mem_cons] at hzip_p
            -- Extract FreshAbove invariant for the head branch bh
            have hfresh_bh : FreshAbove bh edgesH nwH := by
              have h0 := hpfresh 0 (by simp [List.length_cons])
              simp only [hpendingEdges, hpendingNW, List.getElem_cons_zero] at h0
              exact h0
            -- FreshAbove invariant for the tail bt
            have hpfresh_bt : ∀ i (hi : i < bt.length), FreshAbove bt[i]
                edgesT[i]'(by omega) nwT[i]'(by omega) := by
              intro i hi
              have hsi := hpfresh (i + 1) (by simp [List.length_cons]; omega)
              simp only [hpendingEdges, hpendingNW, List.getElem_cons_succ] at hsi
              exact hsi
            set bPers := applyPersistenceFixpoint bh edgesH (fuel'' + 1) with hbPers_def
            -- FreshAbove is preserved by the persistence fixpoint
            have hfresh_bPers : FreshAbove bPers edgesH nwH :=
              freshAbove_applyPersistenceFixpoint bh edgesH nwH (fuel'' + 1) hfresh_bh
            simp only [intExpandBranches.go] at hgo
            by_cases hcl : closurePred bPers = true
            · rw [if_pos hcl] at hgo
              rcases hzip_p with ⟨rfl, rfl⟩ | hmem_rest
              · have hsat_pers : intBranchSatisfied val botForces wo bPers :=
                  applyPersistenceFixpoint_sat val botForces v_uc bf_uc wo bh edgesP (fuel'' + 1)
                    hsat_p hmono_p
                exact closed_unsat wo bPers hcl hsat_pers
              · exact ih_inner eT nwT edgesT (done ++ [bPers]) (doneExp ++ [eH]) (doneNW ++ [nwH])
                    (doneEdges ++ [edgesH])
                    hlength_exp hlength_nw hlength_edges (by simp [hdlength_exp])
                    (by simp [hdlength_nw]) (by simp [hdlength_edges]) hpfresh_bt hgo bp edgesP
                    hmem_rest wo hmono_p hsat_p
            · rw [if_neg hcl] at hgo
              cases hstep : intStepBranch bPers eH nwH with
              | none => rw [hstep] at hgo; simp [intExpandBranches.go] at hgo
              | some step =>
                obtain ⟨result, newExp⟩ := step
                rw [hstep] at hgo
                obtain ⟨sf, hsf_mem, hresult_sf⟩ :
                    ∃ sf ∈ bPers, intApplyRuleFull sf nwH bPers = result := by
                  simp only [intStepBranch] at hstep
                  obtain ⟨sf, hmem, hval⟩ := List.exists_of_findSome?_eq_some hstep
                  refine ⟨sf, hmem, ?_⟩
                  cases h : intApplyRuleFull sf nwH bPers with
                  | notApplicable => simp [h] at hval
                  | linearResult a b c =>
                    simp only [h] at hval
                    by_cases hexp : (eH.any fun x => x == sf) = true
                    · simp [hexp] at hval
                    · simp only [hexp, Bool.false_eq_true, ite_false, Option.some.injEq,
                          Prod.mk.injEq] at hval
                      exact hval.1
                  | branchingResult a b =>
                    simp only [h] at hval
                    by_cases hexp : (eH.any fun x => x == sf) = true
                    · simp [hexp] at hval
                    · simp only [hexp, Bool.false_eq_true, ite_false, Option.some.injEq,
                          Prod.mk.injEq] at hval
                      exact hval.1
                -- Derive hfresh from the FreshAbove invariant for bPers
                -- STATUS: This is the KEY CLOSURE of the two hfresh sorries (L945, L961)
                have hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH :=
                  fun sf' hmem' hlab => absurd hlab
                    (Nat.ne_of_lt (hfresh_bPers.1 sf' hmem'))
                cases hresult : result with
                | linearResult newForms nw' newEdge =>
                  rw [hresult] at hgo hstep hresult_sf
                  set edges' := match newEdge with | none => edgesH | some e => edgesH ++ [e]
                      with hedges'_def
                  rcases hzip_p with ⟨rfl, rfl⟩ | hmem_rest
                  · -- linearResult bp=bh case
                    -- STATUS: still had sorry in latest transcript (a9309a1).
                    -- Two sub-sorries: FreshAbove for expanded branches, MonotoneEdges wo' edges'.
                    -- See Phase B in plan 06.
                    simp only [] at hgo
                    have hsat_pers : intBranchSatisfied val botForces wo bPers :=
                      applyPersistenceFixpoint_sat val botForces v_uc bf_uc wo bh edgesP (fuel'' + 1)
                        hsat_p hmono_p
                    have hpres := intRule_preserves_sat val botForces v_uc bf_uc wo bPers sf
                        hsf_mem hsat_pers nwH hfresh
                    rw [hresult_sf] at hpres
                    obtain ⟨worldOf', hwo'_eq, hsat'⟩ := hpres
                    -- INCOMPLETE: needs MonotoneEdges worldOf' edges' and
                    --   FreshAbove for expanded branches passed to ih
                    -- Establish MonotoneEdges worldOf' edges':
                    have hmono_edges' : MonotoneEdges worldOf' edges' := by
                      simp only [hedges'_def]
                      cases hnew : newEdge with
                      | none =>
                        -- edges' = edgesH; worldOf' agrees with wo on all labels < nwH
                        -- (from hwo'_eq: worldOf' k = wo k for k ≠ nwH)
                        -- Since all edge endpoints < nwH (from hfresh_bPers.2), worldOf' = wo on them
                        simp only
                        exact monotoneEdges_of_agree wo worldOf' edgesH nwH
                          hfresh_bPers.2 (fun k hne => (hwo'_eq k hne).symm) hmono_p
                      | some e =>
                        -- edges' = edgesH ++ [e]; F(→) world-creating case
                        -- e = (nwH, sf.label) from intFImpRule
                        -- worldOf' nwH = w' where wo sf.label ≤ w' (from intRule_preserves_sat F→ branch)
                        -- Apply monotoneEdges_update:
                        simp only
                        -- Need: hnw_not_child, hnw_not_parent, hnw_ne_parent, hle
                        have hnw_not_child : ∀ parent, (nwH, parent) ∉ edgesH :=
                          fun parent hmem_e => absurd (hfresh_bPers.2 nwH parent hmem_e).1
                            (Nat.lt_irrefl _)
                        have hnw_not_parent : ∀ child, (child, nwH) ∉ edgesH :=
                          fun child hmem_e => absurd (hfresh_bPers.2 child nwH hmem_e).2
                            (Nat.lt_irrefl _)
                        -- From intFImpRule: e = (nwH, sf.label), hence parentLabel = sf.label
                        -- From hresult_sf + hresult: intApplyRuleFull sf nwH bPers = .linearResult newForms nw' (some e)
                        -- From intFImpRule: e.2 = sf.label, so parentLabel = sf.label < nwH
                        -- hnw_ne_parent: sf.label ≠ nwH (from hfresh sf hsf_mem : sf.label ≠ nwH)
                        -- hle: wo sf.label ≤ worldOf' nwH
                        --   worldOf' nwH = Function.update wo nwH w' nwH = w' (from F→ branch of intRule_preserves_sat)
                        --   And wo sf.label ≤ w' (from the F→ witness)
                        -- NOTE: These details require introspecting intRule_preserves_sat's F→ case.
                        -- The plan (Phase B, plan 06) says worldOf' = Function.update wo nwH w' definitionally
                        -- in this arm, and wo parentLabel ≤ w' from the witness.
                        -- This sorry represents the known remaining obligation from the latest transcript.
                        -- STATUS: had sorry in source (transcript a9309a1, the last linearResult bp=bh block)
                        sorry
                    refine ih _ _ _ _ (by simp [hdlength_exp, hlength_exp])
                        (by simp [hdlength_nw, hlength_nw]) (by simp [hdlength_edges, hlength_edges])
                        (fun i hi => by
                          -- FreshAbove for expanded branches: also had sorry in latest transcript
                          -- STATUS: had sorry in source
                          sorry)
                        hgo (Branch.extendMany bPers newForms) edges'
                        (by rw [List.zip_append (by simp [hdlength_edges])]; simp [List.mem_append])
                        worldOf'
                        hmono_edges'
                        hsat'
                  · -- linearResult bp∈bt case
                    simp only [] at hgo
                    refine ih _ _ _ _ (by simp [hdlength_exp, hlength_exp])
                        (by simp [hdlength_nw, hlength_nw]) (by simp [hdlength_edges, hlength_edges])
                        (fun i hi => by
                          -- STATUS: had sorry in source
                          sorry)
                        hgo bp edgesP ?_ wo hmono_p hsat_p
                    rw [List.zip_append (by simp [hdlength_edges]), List.mem_append]
                    exact Or.inr hmem_rest
                | branchingResult branches' nw' =>
                  rw [hresult] at hgo hstep hresult_sf
                  rcases hzip_p with ⟨rfl, rfl⟩ | hmem_rest
                  · -- branchingResult bp=bh case (already proved sorry-free in committed file)
                    simp only [] at hgo
                    have hsat_pers : intBranchSatisfied val botForces wo bPers :=
                      applyPersistenceFixpoint_sat val botForces v_uc bf_uc wo bh edgesP (fuel'' + 1)
                        hsat_p hmono_p
                    have hpres := intRule_preserves_sat val botForces v_uc bf_uc wo bPers sf
                        hsf_mem hsat_pers nwH hfresh
                    rw [hresult_sf] at hpres
                    obtain ⟨br, hbr_mem, hsat_br⟩ := hpres
                    have hmem : (Branch.extendMany bPers br, edgesP) ∈
                        (done ++ branches'.map (Branch.extendMany bPers ·) ++ bt).zip
                        (doneEdges ++ branches'.map (fun _ => edgesP) ++ edgesT) := by
                      rw [List.zip_append (by simp [hdlength_edges])]
                      simp only [List.mem_append]
                      refine Or.inl ?_
                      rw [List.zip_append (by exact hdlength_edges.symm)]
                      simp only [List.mem_append]
                      refine Or.inr ?_
                      obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp hbr_mem
                      apply List.mem_iff_getElem.mpr
                      exact ⟨i, by simp [hi_lt], by simp [List.getElem_zip, List.getElem_map,
                          hi_lt, hi_eq]⟩
                    exact ih _ _ _ _ (by simp [hdlength_exp, hlength_exp])
                        (by simp [hdlength_nw, hlength_nw])
                        (by simp [hdlength_edges, hlength_edges])
                        (fun i hi => by
                          -- STATUS: had sorry in source
                          sorry)
                        hgo (Branch.extendMany bPers br) edgesP hmem wo hmono_p hsat_br
                  · -- branchingResult bp∈bt case (already proved sorry-free in committed file)
                    simp only [] at hgo
                    refine ih _ _ _ _ (by simp [hdlength_exp, hlength_exp])
                        (by simp [hdlength_nw, hlength_nw]) (by simp [hdlength_edges, hlength_edges])
                        (fun i hi => by
                          -- STATUS: had sorry in source
                          sorry)
                        hgo bp edgesP ?_ wo hmono_p hsat_p
                    rw [List.zip_append (by simp [hdlength_edges]), List.mem_append]
                    exact Or.inr hmem_rest
                | notApplicable =>
                  rw [hresult] at hgo; simp [intExpandBranches.go] at hgo
-/

-- =============================================================================
-- THREADING: intuitionisticTableau_sound call site update
-- =============================================================================
-- The call to intExpandBranches_closed_unsat in intuitionisticTableau_sound
-- must supply the new FreshAbove hypothesis. The latest form (from transcript a9309a1
-- at ~L1554 and the final hinitFresh versions at ~L1719–L1730) is:
--
-- Have hinitFresh provide FreshAbove [[⟨.neg, φ, 0⟩]][0] [[]][0] [1][0]
-- i.e., FreshAbove [⟨.neg, φ, 0⟩] [] 1
-- Proof: every label on [F(φ)@0] is 0 < 1; no edges.
-- STATUS: proved sorry-free in source (FINAL VERSION below, from a9309a1 ~L1719)

-- PASTE THIS as the hinitFresh have inside intuitionisticTableau_sound
-- (before the `apply intExpandBranches_closed_unsat` call, which must also
-- receive `hinitFresh` as an extra argument):
/-
  have hinitFresh : ∀ i (hi : i < [[⟨.neg, φ, 0⟩]].length),
      FreshAbove [[⟨.neg, φ, 0⟩]][i]'hi
        ([[]] : List IEdges)[i]'(by simp at hi; omega)
        ([1] : List Nat)[i]'(by simp at hi; omega) := by
    intro i hi _hie _hin
    simp only [List.length_singleton] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [List.getElem_cons_zero, List.getElem_nil]
    exact ⟨fun sf hmem => by simp only [List.mem_singleton] at hmem; subst hmem; exact Nat.zero_lt_succ 0,
           fun c p hmem => by simp at hmem⟩
-/
-- NOTE: There were 5 iterated versions of hinitFresh in the transcripts. The LAST one
-- (above) is the correct final form. Earlier versions had wrong argument signatures
-- or hit a `List.getElem_nil` / `List.length_nil` mismatch.
