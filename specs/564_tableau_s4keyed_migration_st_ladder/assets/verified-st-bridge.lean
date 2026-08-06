module

import Cslib.Init
public import Cslib.Logics.Modal.Tableau.LoopChecking

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-- State-threaded keyed S4 rule: makes the `blockingWorldS4Keyed` decision ONCE. -/
public def modalApplyOneS4KeyedSt (φ₀ : Proposition Atom) :
    RuleApplySt Atom (List (WorldIndex × Finset (Sign × Proposition Atom))) :=
  fun sf b acc keys =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock, keys)
      | none =>
        ((modalApplyOneS4KeyedMint sf b acc).1, (modalApplyOneS4KeyedMint sf b acc).2,
          keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)])
    | .pos, .diamond φ =>
      match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock, keys)
      | none =>
        ((modalApplyOneS4KeyedMint sf b acc).1, (modalApplyOneS4KeyedMint sf b acc).2,
          keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos φ sf.label)])
    | _, _ => ((modalApplyOneS4 φ₀ sf b acc).1, (modalApplyOneS4 φ₀ sf b acc).2, keys)

/-- EXPERIMENT 1: the state-threaded rule projects onto the stateless keyed rule. -/
public theorem modalApplyOneS4KeyedSt_proj (φ₀ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    ((modalApplyOneS4KeyedSt φ₀ sf b acc keys).1,
       (modalApplyOneS4KeyedSt φ₀ sf b acc keys).2.1)
      = modalApplyOneS4Keyed φ₀ keys sf b acc := by
  unfold modalApplyOneS4KeyedSt modalApplyOneS4Keyed
  rcases sf with ⟨s, f, w⟩
  cases s <;> cases f <;>
    simp_all <;>
    (try split) <;> simp_all

/-- EXPERIMENT 1b: the state-threaded rule is componentwise the stateless rule plus the
stepper's own `keys'` expression. -/
public theorem modalApplyOneS4KeyedSt_eq (φ₀ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    modalApplyOneS4KeyedSt φ₀ sf b acc keys =
      ((modalApplyOneS4Keyed φ₀ keys sf b acc).1, (modalApplyOneS4Keyed φ₀ keys sf b acc).2,
        (match sf.sign, sf.formula with
          | .neg, .box φ =>
            match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
            | some _ => keys
            | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)]
          | .pos, .diamond φ =>
            match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
            | some _ => keys
            | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos φ sf.label)]
          | _, _ => keys)) := by
  unfold modalApplyOneS4KeyedSt modalApplyOneS4Keyed
  rcases sf with ⟨s, f, w⟩
  cases s <;> cases f <;> dsimp only <;>
    (split <;> rename_i h <;> simp only [h])

/-- EXPERIMENT 2: the state-threaded generic stepper computes the bespoke keyed stepper. -/
public theorem modalStepBranchGenSt_eq_S4Keyed (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    modalStepBranchGenSt (modalApplyOneS4KeyedSt φ₀) b e acc keys
      = modalStepBranchS4Keyed φ₀ b e acc keys := by
  unfold modalStepBranchGenSt modalStepBranchS4Keyed
  congr 1
  funext sf
  by_cases hexp : e.any (· == sf)
  · simp [hexp]
  · simp only [hexp, Bool.false_eq_true, if_false]
    rw [modalApplyOneS4KeyedSt_eq]
    rfl

/-- EXPERIMENT 3: the state-threaded generic loop computes the bespoke keyed loop. -/
public theorem modalExpandBranchesGenSt_eq_S4Keyed (φ₀ : Proposition Atom)
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility)
    (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
    (fuel : Nat) :
    modalExpandBranchesGenSt (modalApplyOneS4KeyedSt φ₀) branches expandedSets accs keyss fuel
      = modalExpandBranchesS4Keyed φ₀ branches expandedSets accs keyss fuel := by
  induction fuel generalizing branches expandedSets accs keyss with
  | zero => simp only [modalExpandBranchesGenSt, modalExpandBranchesS4Keyed]; rfl
  | succ fuel' ih =>
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
        modalExpandBranchesGenSt.processNext (modalApplyOneS4KeyedSt φ₀) fuel' pending pendingExp
            pendingAccs pendingKeys done doneExp doneAccs doneKeys =
          modalExpandBranchesS4Keyed.processNext φ₀ fuel' pending pendingExp pendingAccs
            pendingKeys done doneExp doneAccs doneKeys by
      have hkey := key branches expandedSets accs keyss [] [] [] []
      simpa [modalExpandBranchesGenSt, modalExpandBranchesS4Keyed] using hkey
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
      simp [modalExpandBranchesGenSt.processNext, modalExpandBranchesS4Keyed.processNext]
    | cons b restBs ih_inner =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
      cases pendingExp with
      | nil => simp [modalExpandBranchesGenSt.processNext, modalExpandBranchesS4Keyed.processNext]
      | cons e restEs =>
        cases pendingAccs with
        | nil => simp [modalExpandBranchesGenSt.processNext, modalExpandBranchesS4Keyed.processNext]
        | cons a restAs =>
          cases pendingKeys with
          | nil =>
            simp [modalExpandBranchesGenSt.processNext, modalExpandBranchesS4Keyed.processNext]
          | cons k restKs =>
            simp only [modalExpandBranchesGenSt.processNext,
              modalExpandBranchesS4Keyed.processNext]
            by_cases hc : isModalClosed b
            · simp only [hc, if_true]
              exact ih_inner restEs restAs restKs (done ++ [b]) (doneExp ++ [e])
                (doneAccs ++ [a]) (doneKeys ++ [k])
            · simp only [hc, Bool.false_eq_true, if_false]
              rw [modalStepBranchGenSt_eq_S4Keyed]
              cases hs : modalStepBranchS4Keyed φ₀ b e a k with
              | none => rfl
              | some x =>
                obtain ⟨newBs, newExps, newAcc, keys'⟩ := x
                exact ih (done ++ newBs ++ restBs) (doneExp ++ newExps ++ restEs)
                  (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                  (doneKeys ++ List.replicate newBs.length keys' ++ restKs)

end Cslib.Logic.Modal.Tableau
