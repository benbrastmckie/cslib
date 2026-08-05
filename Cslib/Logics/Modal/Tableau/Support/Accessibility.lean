/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Branch

/-! # Support Facts: Accessibility

Publishes a handful of elementary facts about `Accessibility`, `Accessibility.addEdge`,
`Accessibility.hasEdge`, and `Accessibility.successorsOf` that several driver files across this
subsystem had each re-derived privately, in-file, because the original statement of the fact was
`private` (or otherwise unreachable) to them.

## Why a separate `Support/` module, rather than `Branch.lean`

`Branch.lean`, which declares `Accessibility` and these three operations, is the architecturally
natural home for these facts: they are elementary consequences of the definitions it already
contains, and every consumer already imports `Branch.lean` transitively. `Branch.lean` is,
however, under a project-level constraint that forbids editing it as part of this
de-duplication effort. That constraint is exactly why this separate module exists: it sits
directly above `Branch.lean` (importing nothing else in this subsystem) so every consumer that
could reach the original in `Branch.lean` can reach this module just as easily, without
requiring `Branch.lean` itself to change. A later reader should not "simplify" this back into
`Branch.lean` -- the split is deliberate, not an oversight.

## Why de-privatization alone does not suffice

Some of this subsystem's driver files (`FiveSimplification.lean`, `LoopChecking.lean`,
`S5Simplification.lean`) do not import `Soundness.lean`, where `hasEdge_addEdge_cases` was
originally declared `private`. Simply removing `private` from the `Soundness.lean` copy would
not help those three files, since they cannot reach `Soundness.lean` at all. Lowering the fact
to a module that sits below every consumer -- as low as `Branch.lean` itself, short of editing
it -- is the only fix that reaches all of them.

## Main Results

- `hasEdge_addEdge_cases`: decomposes membership of an edge in `acc.addEdge w w'`.
- `mem_successorsOf_hasEdge`: `Accessibility.successorsOf` membership implies `hasEdge`.
- `hasEdge_mem_successorsOf`: the converse, `hasEdge` implies `Accessibility.successorsOf`
  membership. This is a distinct fact from `mem_successorsOf_hasEdge`, not merely its restatement
  -- the two form a converse pair.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

/-- Decompose membership of an edge in `acc.addEdge w w'`: it is either the new edge or old. -/
lemma hasEdge_addEdge_cases {acc : Accessibility} {w w' a a' : WorldIndex}
    (h : (acc.addEdge w w').hasEdge a a' = true) :
    (a = w ∧ a' = w') ∨ acc.hasEdge a a' = true := by
  simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hw, hw'⟩ | h
  · exact Or.inl ⟨hw.symm, hw'.symm⟩
  · exact Or.inr h

/-- Bridge from `Accessibility.successorsOf` membership to `hasEdge`: if `w'` is returned by
`successorsOf acc w`, the edge `w → w'` is recorded in `acc`. -/
lemma mem_successorsOf_hasEdge {acc : Accessibility} {w w' : WorldIndex}
    (h : w' ∈ acc.successorsOf w) : acc.hasEdge w w' = true := by
  simp only [Accessibility.successorsOf, List.mem_filterMap] at h
  obtain ⟨⟨src, tgt⟩, hmem, heq⟩ := h
  split at heq
  · rename_i hsrc
    simp only [Option.some.injEq] at heq
    simp only [Accessibility.hasEdge, List.any_eq_true, Bool.and_eq_true]
    exact ⟨(src, tgt), hmem, hsrc, by rw [beq_iff_eq]; exact heq⟩
  · simp at heq

/-- Bridge from `acc.hasEdge` to `Accessibility.successorsOf` membership: the converse of
`mem_successorsOf_hasEdge`. -/
lemma hasEdge_mem_successorsOf {acc : Accessibility} {w w' : WorldIndex}
    (hr : acc.hasEdge w w' = true) : w' ∈ acc.successorsOf w := by
  simp only [Accessibility.successorsOf, List.mem_filterMap]
  simp only [Accessibility.hasEdge, List.any_eq_true] at hr
  obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hr
  simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
  exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩

end Cslib.Logic.Modal.Tableau

end
