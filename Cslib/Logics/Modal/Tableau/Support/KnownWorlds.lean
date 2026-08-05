/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Branch

/-! # Support Facts: Known Worlds

Publishes the `modalKnownWorlds`/`modalMaxWorld`/`boxPositivesOf` bookkeeping facts that several
driver files across this subsystem had each re-derived privately, in-file, because the original
statement of the fact was `private` to whichever file first needed it.

## Why a separate `Support/` module, rather than `Branch.lean`

`Branch.lean`, which declares `modalKnownWorlds`, `modalMaxWorld`, and `boxPositivesOf`, is the
architecturally natural home for these facts: they are elementary consequences of the
definitions it already contains, and every consumer already imports `Branch.lean` transitively.
`Branch.lean` is, however, under a project-level constraint that forbids editing it as part of
this de-duplication effort. That constraint is exactly why this separate module exists: it sits
directly above `Branch.lean` (importing nothing else in this subsystem) so every consumer that
could reach the original in `Branch.lean` can reach this module just as easily, without
requiring `Branch.lean` itself to change. A later reader should not "simplify" this back into
`Branch.lean` -- the split is deliberate, not an oversight.

## Why de-privatization alone does not suffice

Some of this subsystem's driver files (`FiveSimplification.lean`, `LoopChecking.lean`,
`S5Simplification.lean`) do not import `FmpMeasure.lean`, where most of these facts were
originally declared `private`. Simply removing `private` from the `FmpMeasure.lean` copies would
not help those files, since they cannot reach `FmpMeasure.lean` at all. Lowering the facts to a
module that sits below every consumer -- as low as `Branch.lean` itself, short of editing it --
is the only fix that reaches all of them.

## Publication order

`mem_modalKnownWorlds` is published here specifically so that a later migration of its six
duplicate `mem_modalKnownWorlds_*` copies can proceed first (before the `modalKnownWorlds_fold_spec`
family is migrated): once every consumer routes through this module's `mem_modalKnownWorlds`,
the six weaker `modalKnownWorlds_fold_spec_*` copies (missing this fact's `Nodup` conjunct) lose
their sole call site each and become deletable outright, with no `Nodup` proof obligation and no
signature-mismatch migration needed. `modalKnownWorlds_fold_spec` is published here in its
**strong** form (carrying the `Nodup` hypothesis and conjunct, matching the `FmpMeasure.lean`
original) because `modalKnownWorlds_nodup` needs it, not as a migration target for the six weaker
copies -- no consumer of the weak copies is ever routed through this strong form.

`modalKnownWorlds_mono_append` is published in the `∀ x ∈ …` form, not the `⊆` form the
`FmpMeasure.lean` original states it in: `List.Subset` unfolds to a strict-implicit binder
`⦃a⦄`, while every external call-site population found in this subsystem binds its element
explicitly. The `∀ x ∈ …` form minimises call-site churn at migration time.

`modalMaxWorld_le_of_forall_label_le` is published in the **implicit-binder** wrapper form
(`{l} {M} (h) : modalMaxWorld l ≤ M`), matching the majority of this subsystem's existing copies,
rather than the sole all-explicit-binder variant.

## Main Results

- `mem_modalKnownWorlds`: membership characterization of `modalKnownWorlds`.
- `modalKnownWorlds_fold_spec`: the underlying `foldl` accumulator's `Nodup` and membership
  specification, strong form.
- `modalKnownWorlds_nodup`: `modalKnownWorlds` never produces a list with duplicates.
- `modalKnownWorlds_mono_append`: prepending formulas to a branch only grows its known-worlds
  set.
- `mem_boxPositivesOf`: inversion for `boxPositivesOf`.
- `modalMaxWorld_le_of_forall_label_le`: `modalMaxWorld l ≤ M` whenever every label in `l` is.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

universe v
variable {Atom : Type v}

/-- The `modalKnownWorlds` `foldl` accumulator's specification: it stays `Nodup`, and its
membership is exactly "in the initial accumulator, or the label of some element of `l`". -/
lemma modalKnownWorlds_fold_spec
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (ws0 : List WorldIndex)
    (hws0 : ws0.Nodup) :
    (l.foldl (fun ws sf => if ws.any (· == sf.label) then ws else sf.label :: ws) ws0).Nodup ∧
    ∀ x, x ∈ l.foldl (fun ws sf => if ws.any (· == sf.label) then ws else sf.label :: ws) ws0 ↔
      x ∈ ws0 ∨ ∃ sf ∈ l, sf.label = x := by
  induction l generalizing ws0 with
  | nil => exact ⟨hws0, by simp⟩
  | cons sf rest ih =>
    by_cases hc : ws0.any (· == sf.label)
    · simp only [List.foldl_cons, if_pos hc]
      have hmemws0 : sf.label ∈ ws0 := by simpa [List.any_eq_true] using hc
      obtain ⟨hnodup, hmem⟩ := ih ws0 hws0
      refine ⟨hnodup, fun x => ?_⟩
      rw [hmem]
      constructor
      · rintro (h | ⟨sf', hsf', rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨sf', List.mem_cons_of_mem _ hsf', rfl⟩
      · rintro (h | ⟨sf', hsf', hfeq⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hsf' with rfl | hsf'
          · exact Or.inl (hfeq ▸ hmemws0)
          · exact Or.inr ⟨sf', hsf', hfeq⟩
    · simp only [List.foldl_cons, if_neg hc]
      have hnotmem : sf.label ∉ ws0 := by simpa [List.any_eq_true] using hc
      have hws0' : (sf.label :: ws0).Nodup := List.nodup_cons.mpr ⟨hnotmem, hws0⟩
      obtain ⟨hnodup, hmem⟩ := ih (sf.label :: ws0) hws0'
      refine ⟨hnodup, fun x => ?_⟩
      rw [hmem]
      constructor
      · rintro (h | ⟨sf', hsf', rfl⟩)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr ⟨sf, List.mem_cons_self, rfl⟩
          · exact Or.inl h
        · exact Or.inr ⟨sf', List.mem_cons_of_mem _ hsf', rfl⟩
      · rintro (h | ⟨sf', hsf', hfeq⟩)
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp hsf' with rfl | hsf'
          · exact Or.inl (hfeq ▸ List.mem_cons_self)
          · exact Or.inr ⟨sf', hsf', hfeq⟩

/-- `modalKnownWorlds` never produces a list with duplicates. -/
lemma modalKnownWorlds_nodup
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) : (modalKnownWorlds l).Nodup :=
  (modalKnownWorlds_fold_spec l [] List.nodup_nil).1

/-- Membership characterization of `modalKnownWorlds`: `x` is a known world of `l` iff `x` is the
label of some element of `l`. -/
lemma mem_modalKnownWorlds
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (x : WorldIndex) :
    x ∈ modalKnownWorlds l ↔ ∃ sf ∈ l, sf.label = x := by
  unfold modalKnownWorlds
  have h := (modalKnownWorlds_fold_spec l [] List.nodup_nil).2 x
  simpa using h

/-- Prepending formulas to a branch only grows its known-worlds set. Stated in the `∀ x ∈ …` form
(see the module docstring for why this form, not `⊆`, is canonical here). -/
lemma modalKnownWorlds_mono_append
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    ∀ x ∈ modalKnownWorlds b, x ∈ modalKnownWorlds (xs ++ b) := by
  intro x hx
  rw [mem_modalKnownWorlds] at hx ⊢
  obtain ⟨sf, hsf, rfl⟩ := hx
  exact ⟨sf, List.mem_append_right _ hsf, rfl⟩

/-- Inversion for `boxPositivesOf`: every `(ψ, src)` pair it returns came from an actual
`T(□ψ)@src` member of the branch. -/
lemma mem_boxPositivesOf {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {ψ : Proposition Atom} {src : WorldIndex} (h : (ψ, src) ∈ boxPositivesOf b) :
    (⟨.pos, .box ψ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  simp only [boxPositivesOf, List.mem_filterMap] at h
  obtain ⟨sf, hsfmem, hsfeq⟩ := h
  split at hsfeq
  · rename_i hsign
    split at hsfeq
    · rename_i φ' hform
      simp only [Option.some.injEq, Prod.mk.injEq] at hsfeq
      obtain ⟨rfl, rfl⟩ := hsfeq
      rw [beq_iff_eq] at hsign
      obtain ⟨s, φ, l⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact hsfmem
    · simp at hsfeq
  · simp at hsfeq

/-- Internal scaffolding for `modalMaxWorld_le_of_forall_label_le`: a bound on a `max`-fold with
an arbitrary accumulator, needed to support induction. -/
private lemma modalMaxWorld_foldl_le_of_forall
    {l : List (SignedFormula (Proposition Atom) WorldIndex)} {M init : WorldIndex}
    (hinit : init ≤ M) (h : ∀ z ∈ l, z.label ≤ M) :
    l.foldl (fun mx sf => max mx sf.label) init ≤ M := by
  induction l generalizing init with
  | nil => simpa using hinit
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (Nat.max_le.mpr ⟨hinit, h hd List.mem_cons_self⟩)
      (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- `modalMaxWorld l` is bounded by `M` whenever every label in `l` is bounded by `M`. Published
in the implicit-binder form (see the module docstring for why this form, not the all-explicit
variant, is canonical here). -/
lemma modalMaxWorld_le_of_forall_label_le
    {l : List (SignedFormula (Proposition Atom) WorldIndex)} {M : WorldIndex}
    (h : ∀ z ∈ l, z.label ≤ M) : modalMaxWorld l ≤ M :=
  modalMaxWorld_foldl_le_of_forall (Nat.zero_le M) h

end Cslib.Logic.Modal.Tableau

end
