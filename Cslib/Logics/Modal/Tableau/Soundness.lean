/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Saturation
public import Cslib.Logics.Modal.Tableau.SoundnessStep
public import Cslib.Logics.Modal.Tableau.LoopInduction
import Mathlib.Data.List.Forall2

/-! # Modal K Tableau Soundness

This module proves soundness of the modal K tableau: if the tableau closes on `φ`
(starting from `F(φ)` at world 0), then `φ` is K-valid (satisfied in all Kripke models).

## Main Results

- `branchSatisfiable`: Satisfiability of a branch via a Kripke model with a world assignment.
- `modalClosed_unsat`: A classically closed modal branch is unsatisfiable.
- `modalExpandBranches_closed_unsat`: Key loop soundness (fuel induction).
- `kValid`: K-validity: true in all Kripke models at all worlds.
- `modalTableau_sound`: `modalTableau φ = .closed → kValid φ`.

## Strategy

Soundness follows from two sub-lemmas:
1. `modalStepBranch_preserves_sat`: Each rule application preserves branch satisfiability
   (stated with an explicit freshness hypothesis `hInv`; proved in `SoundnessStep.lean`).
2. `modalClosed_unsat`: A classically closed branch is unsatisfiable.

Together these imply: if the tableau closes, the initial branch `[F(φ)@0]` was
unsatisfiable, so `φ` holds in all models at all worlds.

## Notes on the Freshness Invariant

`modalStepBranch_preserves_sat` requires the invariant `hInv` that all world indices in
`acc.edges` are labels already in the branch (so the fresh world created by modal rules
has a strictly larger index than any world in `acc`). This invariant holds at the initial
call (empty acc, one-element branch) and is maintained by the loop; it is passed as an
explicit hypothesis to avoid the need for a separate invariant induction.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

universe v u
variable {Atom : Type v} [DecidableEq Atom] [Hashable Atom]

/-! ## Freshness Invariant Maintenance -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Prepending formulas to a branch preserves `accFreshInv`: the next-world bound only grows. -/
private lemma accFreshInv_append
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (hInv : accFreshInv b acc)
    (xs : List (SignedFormula (Proposition Atom) WorldIndex)) :
    accFreshInv (xs ++ b) acc := by
  intro w w' hedge
  obtain ⟨hw, hw'⟩ := hInv w w' hedge
  exact ⟨Nat.lt_of_lt_of_le hw (modalNextWorld_le_append xs b),
         Nat.lt_of_lt_of_le hw' (modalNextWorld_le_append xs b)⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- Decompose membership of an edge in `acc.addEdge w w'`: it is either the new edge or old. -/
private lemma hasEdge_addEdge_cases {acc : Accessibility} {w w' a a' : WorldIndex}
    (h : (acc.addEdge w w').hasEdge a a' = true) :
    (a = w ∧ a' = w') ∨ acc.hasEdge a a' = true := by
  simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hw, hw'⟩ | h
  · exact Or.inl ⟨hw.symm, hw'.symm⟩
  · exact Or.inr h

omit [Hashable Atom] in
/-- The accessibility relation returned by `modalApplyOne` is either unchanged, or it adds a single
fresh edge `sf.label → modalNextWorld b`; in the latter case the result is `.linear` with a head
witness whose label is exactly the fresh world `modalNextWorld b`.

De-privatized so `FrameSoundness.lean`'s K zero-regression re-derivation
(`modalTableau_sound_frame`) can discharge its `hFreshLocal` hypothesis directly,
without importing `FmpMeasure.lean`'s public `modalApplyOne_fresh_local` (which would pull the
completeness/`GenericDriver` import branch into the soundness-parallel branch). -/
lemma modalApplyOne_fresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (modalApplyOne sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOne sf b acc).fst = RuleResult.linear (wsf :: rest)
      ∧ (modalApplyOne sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  -- `modalApplyOne` first tries propositional rules (accessibility unchanged), then dispatches
  -- on the modal rule. Split the outer `if` and the rule `match`; the two existential arms
  -- (◇⁺, □⁻) add a fresh edge (right disjunct), every other arm leaves `acc` untouched (left).
  unfold modalApplyOne
  extract_lets
  split
  · exact Or.inl rfl
  · split <;>
      first
        | exact Or.inl rfl
        | exact Or.inr ⟨_, _, rfl, rfl⟩
        | (left; simp only [apply_ite Prod.snd, ite_self])

/-- **Freshness maintenance, generic form**: `modalStepBranchGen apply` preserves the
per-branch freshness invariant `accFreshInv`, given the raw `freshLocal`-shaped hypothesis
`hFreshLocal` for `apply` (`RuleApplicationSpec`'s F1 field, `GenericDriver.lean`). Kept as a raw
hypothesis rather than a bundled `spec : RuleApplicationSpec apply` argument: `RuleApplicationSpec`
is defined in `GenericDriver.lean`, which this file must stay upstream of (`Soundness.lean`'s own
import surface is `Saturation`/`SoundnessStep`/`LoopInduction` only) -- mirrors the
"Architectural note" pattern in `GenericDriver.lean`. Body is `modalStepBranch_preserves_
accFreshInv`'s exact proof with `modalApplyOne ↦ apply` and `modalApplyOne_fresh sf b acc ↦
hFreshLocal sf b acc`. -/
lemma modalStepBranch_preserves_accFreshInv_gen
    (apply : RuleApply Atom)
    (hFreshLocal : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hInv : accFreshInv b acc) :
    ∀ b' ∈ newBs, accFreshInv b' newAcc := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hFreshLocal sf b acc with hacc | ⟨wsf, rest, hfst, hacc⟩
  · -- accessibility unchanged: every child branch has the form `xs ++ b`
    rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
    · rw [hfstc, hacc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, _, rfl⟩ := hsf
      intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
      exact accFreshInv_append hInv nf
    · rw [hfstc, hacc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, _, rfl⟩ := hsf
      intro b' hb'; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb'
      exact accFreshInv_append hInv x
    · rw [hfstc, hacc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, _, rfl⟩ := hsf
      intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
      exact accFreshInv_append hInv nf
    · rw [hfstc] at hsf; simp at hsf
  · -- a fresh edge `sf.label → modalNextWorld b` was added; single linear child headed by `wsf`
    rw [hfst, hacc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, _, rfl⟩ := hsf
    intro b' hb'; simp only [List.mem_singleton] at hb'; subst hb'
    intro a a' hedge
    rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
    · exact ⟨Nat.lt_of_lt_of_le (modalNextWorld_gt b sf hsfmem)
              (modalNextWorld_le_append (wsf :: rest) b),
            Nat.lt_succ_of_le (label_le_modalMaxWorld (by simp))⟩
    · obtain ⟨ha, ha'⟩ := hInv a a' hold
      exact ⟨Nat.lt_of_lt_of_le ha (modalNextWorld_le_append (wsf :: rest) b),
             Nat.lt_of_lt_of_le ha' (modalNextWorld_le_append (wsf :: rest) b)⟩

/-- **Freshness maintenance**: `modalStepBranch` preserves the per-branch
freshness invariant `accFreshInv`. Every child branch produced satisfies `accFreshInv` against the
post-step accessibility relation. This is the only genuinely new semantic obligation; the
anti-monotonicity obligations of the original design are eliminated structurally by the per-branch
`accs` scheme.

Byte-identical-statement corollary of `modalStepBranch_preserves_accFreshInv_gen`,
recovered via `modalStepBranch_eq` and K's own `modalApplyOne_fresh` (which is exactly the
`freshLocal`-shaped hypothesis the generic lemma needs). -/
lemma modalStepBranch_preserves_accFreshInv
    (b e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hInv : accFreshInv b acc) :
    ∀ b' ∈ newBs, accFreshInv b' newAcc :=
  modalStepBranch_preserves_accFreshInv_gen modalApplyOne modalApplyOne_fresh b e acc newBs
    newExps newAcc (modalStepBranch_eq b e acc ▸ hstep) hInv

/-! ## Main Fuel-Induction Soundness Lemma -/


/-- **Modal expansion closed implies all branches unsatisfiable**: If
`modalExpandBranches branches expandedSets accs fuel = .closed`, the length invariants hold,
and the per-branch freshness invariant `accFreshInv` holds for each `(branches[i], accs[i])`
pair, then every branch is unsatisfiable against its corresponding accessibility relation.

Proved by induction on `fuel` with inner induction on the `pending` list for `processNext`.
The per-branch `accs` design eliminates the anti-monotonicity obligations of earlier designs. -/
theorem modalExpandBranches_closed_unsat (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      List.Forall₂ (fun b acc => accFreshInv b acc) branches accs →
      modalExpandBranches branches expandedSets accs fuel = .closed →
      List.Forall₂ (fun b acc => ¬branchSatisfiable.{v, u} b acc) branches accs := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs hlength hlength_accs hFresh h
    simp only [modalExpandBranches] at h
    split at h
    · simp at h
    · rename_i hfind
      refine List.forall₂_iff_zip.mpr ⟨hlength_accs.symm, ?_⟩
      intro b a hmem
      have hfn := (List.findSome?_eq_none_iff.mp hfind) _ hmem
      have hcl : isModalClosed b = true := by
        cases h : isModalClosed b with
        | true => rfl
        | false => simp [h] at hfn
      exact modalClosed_unsat b hcl a
  | succ fuel' ih =>
    intro branches expandedSets accs hlength hlength_accs hFresh h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        List.Forall₂ (fun b a => accFreshInv b a) pending pendingAccs →
        List.Forall₂ (fun b a => accFreshInv b a) done doneAccs →
        modalExpandBranches.processNext
          fuel' pending pendingExp pendingAccs done doneExp doneAccs = .closed →
        List.Forall₂ (fun b a => ¬branchSatisfiable.{v, u} b a) pending pendingAccs from
      key branches expandedSets accs [] [] []
        hlength hlength_accs rfl rfl hFresh List.Forall₂.nil
        (by simpa [modalExpandBranches] using h)
    intro pending
    induction pending with
    | nil =>
      intro _ _ _ _ _ _ _ _ _ hFresh_pending _ _
      cases hFresh_pending
      exact List.Forall₂.nil
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
        hpendingExpLen hpendingAccsLen hdoneExpLen hdoneAccsLen
        hFresh_pending hFresh_done hinner
      cases pendingAccs with
      | nil => simp at hpendingAccsLen
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hpendingExpLen
        | cons e es =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hpendingExpLen hpendingAccsLen
          cases hFresh_pending with
          | cons hInv_bh hFresh_rest =>
            simp only [modalExpandBranches.processNext] at hinner
            by_cases hcl : isModalClosed bh = true
            · -- Branch is closed: skip it and recurse
              rw [if_pos hcl] at hinner
              apply List.Forall₂.cons
              · exact modalClosed_unsat bh hcl a
              · exact ih_inner es restAs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
                    (by simp [hpendingExpLen])
                    (by simp [hpendingAccsLen])
                    (by simp [hdoneExpLen])
                    (by simp [hdoneAccsLen])
                    hFresh_rest
                    (List.rel_append hFresh_done
                      (List.Forall₂.cons hInv_bh List.Forall₂.nil))
                    hinner
            · -- Branch is open: expand it
              simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [hcl])] at hinner
              cases hstep_eq : modalStepBranch bh e a with
              | none => rw [hstep_eq] at hinner; simp at hinner
              | some step =>
                obtain ⟨newBs, newExps, newAcc⟩ := step
                rw [hstep_eq] at hinner
                have hnewExpLen : newExps.length = newBs.length := by
                  unfold modalStepBranch at hstep_eq
                  obtain ⟨sf, _, hf⟩ := List.exists_of_findSome?_eq_some hstep_eq
                  rcases h_apply : (modalApplyOne sf bh a) with ⟨result, _⟩
                  simp only [h_apply] at hf
                  -- Every applicable rule sets `newExps := List.replicate newBs.length e`,
                  -- so the lengths agree; only `.notApplicable` is impossible here.
                  cases result with
                  | notApplicable => simp at hf
                  | _ =>
                    split_ifs at hf
                    simp only [Option.some.injEq, Prod.mk.injEq] at hf
                    obtain ⟨rfl, rfl, _⟩ := hf; simp [List.length_map]
                -- Build freshness invariant for all child branches
                have hFreshNew : List.Forall₂ (fun b a => accFreshInv b a)
                    newBs (List.replicate newBs.length newAcc) :=
                  forall₂_replicate_right.mpr
                    (modalStepBranch_preserves_accFreshInv bh e a newBs newExps newAcc
                      hstep_eq hInv_bh)
                have hFreshAll : List.Forall₂ (fun b a => accFreshInv b a)
                    (done ++ newBs ++ bt)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs) :=
                  List.rel_append (List.rel_append hFresh_done hFreshNew) hFresh_rest
                -- Apply the fuel induction hypothesis
                have hunsat_all :
                    List.Forall₂ (fun b a => ¬branchSatisfiable.{v, u} b a)
                    (done ++ newBs ++ bt)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs) :=
                  ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ es)
                    (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                    (by simp only [List.length_append]; omega)
                    (by simp only [List.length_append, List.length_replicate]; omega)
                    hFreshAll hinner
                -- Extract: newBs ++ bt part (drop the done prefix)
                have hunsat_newBs_bt :
                    List.Forall₂ (fun b a => ¬branchSatisfiable.{v, u} b a)
                    (newBs ++ bt) (List.replicate newBs.length newAcc ++ restAs) := by
                  have h := List.forall₂_drop done.length hunsat_all
                  rw [List.append_assoc done newBs bt, List.drop_left,
                      List.append_assoc doneAccs (List.replicate newBs.length newAcc) restAs,
                      List.drop_left' hdoneAccsLen] at h
                  exact h
                -- Extract: bt part (drop the newBs prefix)
                have hunsat_bt :
                    List.Forall₂ (fun b a => ¬branchSatisfiable.{v, u} b a)
                    bt restAs := by
                  have h := List.forall₂_drop newBs.length hunsat_newBs_bt
                  rw [List.drop_left,
                      List.drop_left' List.length_replicate] at h
                  exact h
                -- Extract: newBs part (take the newBs prefix)
                have hunsat_newBs :
                    List.Forall₂ (fun b a => ¬branchSatisfiable.{v, u} b a)
                    newBs (List.replicate newBs.length newAcc) := by
                  have h := List.forall₂_take newBs.length hunsat_newBs_bt
                  rw [List.take_left,
                      List.take_left' List.length_replicate] at h
                  exact h
                -- Show bh is unsatisfiable (contrapositive via sat preservation)
                have hbh_unsat : ¬branchSatisfiable.{v, u} bh a := by
                  intro hbh_sat
                  obtain ⟨b', hb'_mem, hb'_sat⟩ :=
                    modalStepBranch_preserves_sat bh e a newBs newExps newAcc
                      hstep_eq hbh_sat hInv_bh
                  exact (forall₂_replicate_right.mp hunsat_newBs b' hb'_mem) hb'_sat
                -- Combine head and tail
                exact List.Forall₂.cons hbh_unsat hunsat_bt

/-! ## K-Validity and Soundness -/

/-- K-validity: a proposition is K-valid if it is satisfied in all Kripke models at all worlds. -/
def kValid (φ : Proposition Atom) : Prop :=
  ∀ (World : Type) (m : Model World Atom) (w : World), Satisfies m w φ

/-- The modal K tableau is sound: if the tableau closes on `F(φ)`, then `φ` is K-valid.

Proof by contrapositive: if `φ` is falsified at some world `w` in model `m`, then
the initial branch `[F(φ)@0]` is satisfiable (use constant world assignment `_ ↦ w`).
But if the tableau closes, all initial branches are unsatisfiable by
`modalExpandBranches_closed_unsat` (per-branch accessibility design). -/
theorem modalTableau_sound (φ : Proposition Atom)
    (h : modalTableau φ = .closed) :
    kValid φ := by
  intro World m w
  by_contra hnotsat
  have hsat : branchSatisfiable [⟨.neg, φ, 0⟩] Accessibility.empty :=
    ⟨World, m, fun _ => w,
      fun w1 w2 hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge]),
      fun sf hmem => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst hmem
        exact ⟨fun h => by simp at h, fun _ => hnotsat⟩⟩
  have hunsat := modalExpandBranches_closed_unsat (modalFuel φ)
    [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty]
    rfl rfl
    (List.Forall₂.cons (accFreshInv_empty _) List.Forall₂.nil)
    (by simp only [modalTableau] at h; exact h)
  cases hunsat with
  | cons h_unsat _ => exact h_unsat hsat

end Cslib.Logic.Modal.Tableau

end
