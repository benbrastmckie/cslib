/-- BLOCKER EVIDENCE (task 364): the satisfiability-lifting obligation that the `key`
fuel-induction needs for carried-over worklist branches is mathematically FALSE.
A branch satisfiable at `acc` need not be satisfiable after a single edge is added to `acc`
(here `□p ∧ □¬p @ 0` is satisfiable at a dead-end world 0, but not once world 0 gains a
successor 1). Since `modalExpandBranches` accumulates such edges into a SHARED `acc` while
sibling branches remain in the worklist, the per-branch invariant required by
`modalStepBranch_preserves_sat` is not maintainable. -/
example :
    ∃ (bp : List (SignedFormula (Proposition Unit) WorldIndex)) (src tgt : WorldIndex),
      branchSatisfiable.{0, 0} bp Accessibility.empty ∧
      ¬ branchSatisfiable.{0, 0} bp (Accessibility.empty.addEdge src tgt) := by
  refine ⟨[⟨.pos, .box (.atom ()), 0⟩, (⟨.pos, .box ((Proposition.atom () : Proposition Unit).imp .bot), 0⟩ : SignedFormula (Proposition Unit) WorldIndex)], 0, 1, ?_, ?_⟩
  · refine ⟨Unit, ⟨fun _ _ => False, fun _ _ => True⟩, fun _ => (), ?_, ?_⟩
    · intro w w' h
      simp [Accessibility.empty, Accessibility.hasEdge] at h
    · intro sf hmem
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact ⟨fun _ w' hr => hr.elim, fun h => by simp at h⟩
      · exact ⟨fun _ w' hr => hr.elim, fun h => by simp at h⟩
  · rintro ⟨W, m, f, hacc, hb⟩
    have hedge : (Accessibility.empty.addEdge 0 1).hasEdge 0 1 = true := by
      simp [Accessibility.addEdge, Accessibility.empty, Accessibility.hasEdge]
    have hr : m.r (f 0) (f 1) := hacc 0 1 hedge
    have hbox1 := (hb ⟨.pos, .box (.atom ()), 0⟩ (by simp)).1 rfl
    have hbox2 := (hb (⟨.pos, .box ((Proposition.atom () : Proposition Unit).imp .bot), 0⟩ : SignedFormula (Proposition Unit) WorldIndex) (by simp)).1 rfl
    exact (hbox2 (f 1) hr) (hbox1 (f 1) hr)
