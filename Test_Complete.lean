import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
import Cslib.Logics.Propositional.Semantics.Kripke

namespace Cslib.Logic.PL
open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]
variable {World : Type*} [Preorder World]
variable (val : World → Atom → Prop) (botForces : World → Prop)
variable (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
variable (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
variable (closurePred : IBranch Atom → Bool)
variable (closed_unsat : ∀ (worldOf : Nat → World) (b : IBranch Atom),
    closurePred b = true → ¬ intBranchSatisfied val botForces worldOf b)

-- The main loop invariant with monotone worldOf
private lemma intExpandBranches_closed_unsat_test
    (fuel : Nat) :
    ∀ (branches : List (IBranch Atom))
      (expandedSets : List (List (ISF Atom)))
      (nextWorlds : List Nat),
      expandedSets.length = branches.length →
      nextWorlds.length = branches.length →
      intExpandBranches branches expandedSets nextWorlds fuel closurePred = .closed →
      ∀ b ∈ branches, ∀ (worldOf : Nat → World),
          (∀ n m : Nat, n ≤ m → worldOf n ≤ worldOf m) →
          ¬ intBranchSatisfied val botForces worldOf b := by
  induction fuel with
  | zero =>
    intro branches expandedSets nextWorlds _ _ h b hb worldOf _ hsat
    simp only [intExpandBranches] at h
    split at h with hopen
    · simp at h
    · rename_i hfind
      have hfn := List.findSome?_eq_none_iff.mp hfind b hb
      split_ifs at hfn with hcl
      exact closed_unsat worldOf b hcl hsat
  | succ fuel' ih =>
    intro branches expandedSets nextWorlds hlength hnwlen h b hb worldOf h_mono hsat
    -- Translate succ case to go
    suffices key : ∀ (pending : List (IBranch Atom))
        (pendingExp : List (List (ISF Atom)))
        (pendingNW : List Nat)
        (done : List (IBranch Atom))
        (doneExp : List (List (ISF Atom)))
        (doneNW : List Nat),
        pendingExp.length = pending.length →
        pendingNW.length = pending.length →
        doneExp.length = done.length →
        doneNW.length = done.length →
        intExpandBranches.go closurePred fuel' pending pendingExp pendingNW done doneExp doneNW = .closed →
        ∀ bp ∈ pending, ∀ (wof : Nat → World),
            (∀ n m : Nat, n ≤ m → wof n ≤ wof m) →
            ¬ intBranchSatisfied val botForces wof bp from
      key branches expandedSets nextWorlds [] [] [] hlength hnwlen rfl rfl
        (by simpa [intExpandBranches] using h) b hb worldOf h_mono hsat
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingNW done doneExp doneNW _ _ _ _ _ bp hmem
      simp at hmem
    | cons bh bt ih_inner =>
      intro pendingExp pendingNW done doneExp doneNW hlen hnwlen2 hdlen hdnwlen hinner bp hbp wof hwof_mono
      simp only [List.length_cons] at hlen hnwlen2
      cases hpendingExp : pendingExp with
      | nil => simp [hpendingExp] at hlen
      | cons e es =>
        simp only [hpendingExp, List.length_cons, Nat.add_right_cancel_iff] at hlen
        cases hpendingNW : pendingNW with
        | nil => simp [hpendingNW] at hnwlen2
        | cons nw nws =>
          simp only [hpendingNW, List.length_cons, Nat.add_right_cancel_iff] at hnwlen2
          rw [hpendingExp, hpendingNW] at hinner
          simp only [intExpandBranches.go] at hinner
          simp only [List.mem_cons] at hbp
          -- Compute bPers
          set bPers := applyPersistenceFixpoint bh (fuel' + 1) with hbPers_def
          by_cases hcl : closurePred bPers = true
          · -- Branch is closed after persistence
            rw [if_pos hcl] at hinner
            rcases hbp with rfl | hmem_rest
            · -- bp = bh: use closed_unsat... but we need bPers to be unsat, not bh
              -- KEY SORRY: If bh is satisfiable with monotone worldOf, then bPers is satisfiable
              -- and closurePred bPers = false. So closurePred bPers = true implies bh unsat.
              -- For now: sorry
              intro hbp_sat
              -- bh is a sub-branch of bPers (actually bPers extends bh)
              -- We know closurePred bPers = true → bPers is unsat (by closed_unsat)
              -- If bh is sat with wof, is bPers sat with wof?
              -- This requires monotonicity: sorry
              sorry
            · exact ih_inner es nws (done ++ [bPers]) (doneExp ++ [e]) (doneNW ++ [nw]) hlen hnwlen2
                (by simp [hdlen]) (by simp [hdnwlen]) hinner bp hmem_rest wof hwof_mono
          · simp only [Bool.not_eq_true] at hcl
            rw [if_neg (by simp [hcl])] at hinner
            cases hstep : intStepBranch bPers e nw with
            | none =>
              rw [hstep] at hinner; simp at hinner
            | some step =>
              obtain ⟨rres, newExp⟩ := step
              rw [hstep] at hinner
              -- Case on rule result
              cases rres with
              | notApplicable =>
                simp only [intExpandBranches.go] at hinner
              | linearResult newForms nw' =>
                -- IntExpandBranches called with done ++ [bPers ++ newForms] ++ bt
                simp only [Branch.extendMany] at hinner
                rcases hbp with rfl | hmem_rest
                · -- bp = bh: bh satisfiable → bPers satisfiable → extended satisfiable
                  intro hbp_sat
                  -- Step 1: bPers is satisfiable (same wof, monotone)
                  -- Need applyPersistenceFixpoint_preserves_sat (requires monotone wof) - use sorry for now
                  have hsat_pers : intBranchSatisfied val botForces wof bPers := by
                    sorry -- need applyPersistenceFixpoint_preserves_sat
                  -- Step 2: apply intRule_preserves_sat to get worldOf'
                  -- Find the formula sf that was expanded
                  simp only [intStepBranch] at hstep
                  obtain ⟨sf, hsfmem, hsf_cond⟩ := List.exists_of_findSome?_eq_some hstep
                  split at hsf_cond with h_exp
                  · simp at hsf_cond
                  · -- sf ∈ bPers and it's not already expanded
                    rw [hca : intApplyRuleFull sf nw bPers = .linearResult newForms nw'] at hsf_cond
                      <;> sorry -- need to extract from hsf_cond
                    sorry
                · -- bp ∈ bt: apply IH
                  sorry
              | branchingResult branches' nw' =>
                rcases hbp with rfl | hmem_rest
                · -- bp = bh
                  intro hbp_sat
                  sorry
                · sorry

#check @intExpandBranches_closed_unsat_test

end Cslib.Logic.PL
