-- VERIFIED IN-FILE against Cslib/Logics/Modal/Tableau/Saturation.lean (Lean v4.33.0-rc1).
-- Inserted immediately before `end Cslib.Logic.Modal.Tableau`; full `lake build Cslib` green
-- at 3313 jobs, lake test exit 0, lake lint delta 0, shake 9 findings (none in Modal/Tableau).
-- Docstrings here are PLACEHOLDERS: expand them before landing (see report section 7).

/-! ## State-Threading Ladder (ADDITIVE PROBE) -/

/-- State-threading rule-application shape. -/
@[nolint unusedArguments]
abbrev RuleApplySt (Atom : Type*) [DecidableEq Atom] [Hashable Atom] (σ : Type*) : Type _ :=
  SignedFormula (Proposition Atom) WorldIndex →
  List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → σ →
  RuleResult (Proposition Atom) WorldIndex × Accessibility × σ

/-- Lift a stateless rule into the trivial state-threading rule at `σ := Unit`. -/
def liftRuleApply (apply : RuleApply Atom) : RuleApplySt Atom Unit :=
  fun sf b acc _ => ((apply sf b acc).1, (apply sf b acc).2, ())

/-- State-threading one-step branch expansion. -/
def modalStepBranchGenSt {σ : Type*} (apply : RuleApplySt Atom σ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (expanded : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (st : σ) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility × σ) :=
  b.findSome? fun sf =>
    if expanded.any (· == sf) then none
    else
      let (result, newAcc, newSt) := apply sf b acc st
      match result with
      | .linear newForms =>
        some ([newForms ++ b], [expanded ++ [sf]], newAcc, newSt)
      | .branching branches =>
        some (branches.map (· ++ b), branches.map (fun _ => expanded ++ [sf]), newAcc, newSt)
      | .persistent newForms =>
        some ([newForms ++ b], [expanded], newAcc, newSt)
      | .notApplicable => none

/-- `Option.map` commutes out of `List.findSome?`. -/
theorem findSome?_map_comm {α β γ : Type*} (f : α → Option β) (g : β → γ) (l : List α) :
    l.findSome? (fun x => (f x).map g) = (l.findSome? f).map g := by
  induction l with
  | nil => simp
  | cons a t ih => cases h : f a <;> simp [h, ih]

/-- Step-level bridge. -/
theorem modalStepBranchGen_eq_St (apply : RuleApply Atom)
    (b expanded : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalStepBranchGenSt (liftRuleApply apply) b expanded acc () =
      (modalStepBranchGen apply b expanded acc).map
        (fun x => (x.1, x.2.1, x.2.2, ())) := by
  rw [modalStepBranchGenSt, modalStepBranchGen, ← findSome?_map_comm]
  congr 1
  funext sf
  by_cases h : expanded.any (· == sf)
  · simp [h]
  · simp only [h, Bool.false_eq_true, if_false, liftRuleApply]
    cases hr : apply sf b acc with
    | mk result newAcc => cases result <;> simp

/-- State-threading fuel-based expansion. -/
def modalExpandBranchesGenSt {σ : Type*} (apply : RuleApplySt Atom σ)
    (branches : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility)
    (sts : List σ)
    (fuel : Nat) : ModalTableauResult Atom :=
  match fuel with
  | 0 =>
    match (branches.zip accs) |>.findSome? (fun (b, a) =>
        if isModalClosed b then none else some (b, a)) with
    | some (b, a) => .openBranch b a
    | none => .closed
  | fuel' + 1 =>
    let rec @[nolint docBlame] processNext
        (pending : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingSts : List σ)
        (done : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneSts : List σ)
        : ModalTableauResult Atom :=
      match pending, pendingExp, pendingAccs, pendingSts with
      | [], _, _, _ => .closed
      | b :: restBs, e :: restEs, a :: restAs, s :: restSs =>
        if isModalClosed b then
          processNext restBs restEs restAs restSs (done ++ [b]) (doneExp ++ [e])
            (doneAccs ++ [a]) (doneSts ++ [s])
        else
          match modalStepBranchGenSt apply b e a s with
          | none => .openBranch b a
          | some (newBs, newExps, newAcc, newSt) =>
            modalExpandBranchesGenSt apply
              (done ++ newBs ++ restBs)
              (doneExp ++ newExps ++ restEs)
              (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
              (doneSts ++ List.replicate newBs.length newSt ++ restSs)
              fuel'
      | _, _, _, _ => .closed
    processNext branches expandedSets accs sts [] [] [] []

/-- Loop-level bridge. -/
theorem modalExpandBranchesGen_eq_St (apply : RuleApply Atom)
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) :
    modalExpandBranchesGen apply branches expandedSets accs fuel =
      modalExpandBranchesGenSt (liftRuleApply apply) branches expandedSets accs
        (accs.map fun _ => ()) fuel := by
  induction fuel generalizing branches expandedSets accs with
  | zero =>
    simp only [modalExpandBranchesGen, modalExpandBranchesGenSt]
  | succ fuel' ih =>
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        modalExpandBranchesGen.processNext apply fuel' pending pendingExp pendingAccs done doneExp
            doneAccs =
          modalExpandBranchesGenSt.processNext (liftRuleApply apply) fuel' pending pendingExp
            pendingAccs (pendingAccs.map fun _ => ()) done doneExp doneAccs
            (doneAccs.map fun _ => ()) by
      have hkey := key branches expandedSets accs [] [] []
      simpa [modalExpandBranchesGen, modalExpandBranchesGenSt] using hkey
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs done doneExp doneAccs
      simp [modalExpandBranchesGen.processNext, modalExpandBranchesGenSt.processNext]
    | cons b restBs ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
      cases pendingExp with
      | nil => simp [modalExpandBranchesGen.processNext, modalExpandBranchesGenSt.processNext]
      | cons e restEs =>
        cases pendingAccs with
        | nil => simp [modalExpandBranchesGen.processNext, modalExpandBranchesGenSt.processNext]
        | cons a restAs =>
          simp only [modalExpandBranchesGen.processNext, modalExpandBranchesGenSt.processNext,
            List.map_cons]
          by_cases hc : isModalClosed b
          · simp only [hc, if_true]
            have := ih_inner restEs restAs (done ++ [b]) (doneExp ++ [e]) (doneAccs ++ [a])
            simpa using this
          · simp only [hc]
            rw [modalStepBranchGen_eq_St]
            cases hs : modalStepBranchGen apply b e a with
            | none => rfl
            | some x =>
              obtain ⟨newBs, newExps, newAcc⟩ := x
              simp only [Option.map_some]
              have := ih (done ++ newBs ++ restBs) (doneExp ++ newExps ++ restEs)
                (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
              simpa using this

/-- State-threading entry point. -/
def modalTableauGenSt {σ : Type*} (apply : RuleApplySt Atom σ) (st0 : σ)
    (φ : Proposition Atom) : ModalTableauResult Atom :=
  let initialBranch : List (SignedFormula (Proposition Atom) WorldIndex) := [⟨.neg, φ, 0⟩]
  modalExpandBranchesGenSt apply [initialBranch] [[]] [Accessibility.empty] [st0] (modalFuel φ)

/-- Entry-point bridge. -/
theorem modalTableauGen_eq_St (apply : RuleApply Atom) (φ : Proposition Atom) :
    modalTableauGen apply φ = modalTableauGenSt (liftRuleApply apply) () φ := by
  simp only [modalTableauGen, modalTableauGenSt]
  exact modalExpandBranchesGen_eq_St _ _ _ _ _


