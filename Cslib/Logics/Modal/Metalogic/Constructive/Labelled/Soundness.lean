/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical
public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context

/-! # Labelled-System Soundness (Task 517 Phase 11, Simpson 1994 Thm 8.1.4, Soundness Direction)

**Status: interpretation machinery (Phase 11.1, partial) + anti-vacuity certificate (Phase 11.3,
COMPLETE).** This module lands (1) the first, reusable building block of the full labelled
soundness direction `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ`, which will
complete the Simpson 8.1.4 biconditional alongside `cs5_completeness` (`Completeness.lean`); and
(2) the anti-vacuity certificate `nik_TS5_consistent : ¬ NIKTheorem TS5 ⊥`, landed via a
**direct, self-contained route** (see "The anti-vacuity route taken" below) rather than as a
corollary of the not-yet-landed general theorem. The general `nik_TS5_soundness` (Phase 11.1's
tree-lifting machinery + Phase 11.2's `TClosure` validation) is **not yet landed** -- see "What
remains" below and the continuation handoff at
`specs/517_labelled_bounded_context_cs5_completeness/handoffs/`.

## The anti-vacuity route taken: `nik_soundness_onePoint` (Phase 11.3, direct, not via 11.1/11.2)

The plan's own Phase 11.3 description explicitly sanctions proving `nik_TS5_consistent` directly
against a **one-point reflexive** witness model, independently of the general `nik_TS5_soundness`
theorem, "if 11.2's general induction is not reached in a future dispatch" (Rollback/Contingency;
also the prior dispatch's continuation handoff, "optional accelerant" note). This dispatch takes
exactly that route, landing it **before** the general theorem rather than after: `nik_TS5_soundness`
requires the still-outstanding tree-lifting machinery (see "What remains"), but a *soundness
argument specialized to the one-point model* `World := Unit`, `r := fun _ _ => True` sidesteps the
Lifting Lemma entirely -- **every** interpretation of every label collapses to the same unique
point, so "lifting the interpretation at one label" is trivially the identity, and no tree-shape
invariant or graph-lifting recursion is needed at all. `nik_soundness_onePoint` is a full
12-constructor structural induction over `NIK`, proved directly against this one model (not a
special case of a not-yet-existing general theorem), and `nik_TS5_consistent` is then immediate:
instantiate `botForces := fun _ => False`, so `CKForces ... () ⊥` reduces to `False` outright.
This is flagged explicitly as a deviation from the plan's literal sub-phase *sequencing*
(11.1 → 11.2 → 11.3) -- not from its mathematical *content*, since the plan's own Rollback/
Contingency section pre-authorizes exactly this route as a documented fallback, and the final
theorem statement `nik_TS5_consistent : ¬ NIKTheorem TS5 (⊥ : Proposition Atom)` is unchanged.

## `--lit`: Simpson's Chapter 8 soundness argument (reflowed `L1367-1423`, PDF offset +9)

Simpson's own Theorem 8.1.4 soundness direction is **not** a direct induction over `N(𝒯)` in the
way its completeness direction is. His text (`8.1.2 Soundness`) states:

> "Soundness is more difficult because the use of `(R𝒯)` rules means that derivations in `N(𝒯)`
> involving excursions through non-tree consequences are unavoidable. The easiest proof of
> soundness uses the modified sequent system `L_m(𝒯,∅)` ... For in these systems, excursions
> through non-tree graphs can be avoided by the use of `𝒯`-closure in the `(⊃L)` and `(⊃R)_m`
> rules."

Theorem 8.1.4 itself is stated **only for `G` a tree** ("Let `G` be a tree. Then the following are
equivalent: ..."), and the crucial ingredient his *direct* natural-deduction argument (`8.1.2`, not
the sequent-calculus detour) needs is the **Lifting Lemma** (`8.1.3`): "Given any `G`-interpretation
`[-]`, any `x` in `G` and any `w ≥ [x]`, there exists another `G`-interpretation, `[-]'`, such that
`[x]' = w` and, for all `z ∈ G`, `[z]' ≥ [z]`." Simpson's own proof of the Lifting Lemma uses his
birelational models' `F1`/`F2` confluence conditions (his Figure 8-1 gives an explicit
counterexample to soundness for *non-tree* `G`, and to the Lifting Lemma when `F1`/`F2` are absent
or `G` is not a tree).

## Why this cannot be transcribed literally, and the deviation this module takes

CSLib's target semantics for this task is **not** Simpson's own birelational `BForces` model with
`F1`/`F2` -- it is `CKForces` (`Forcing.lean`), the Wijesekera-style *fallible-world segment*
semantics with the `∀∃` diamond clause, deliberately built **without** `F1`/`F2` confluence (see
`Forcing.lean`'s module docstring: bare `CK` is otherwise incomplete for confluent models). So
Simpson's own Lifting-Lemma proof does not transfer verbatim; a literal transcription is not
available. Per the literature-fidelity discipline (`lean4.md`), this deviation is flagged
explicitly rather than silently mixed with novel steps.

**The key finding (this dispatch, verified by hand and cross-checked): `cs5FCIncest`'s own
`cs5Incest`/`r_symBox` conjuncts supply a Wijesekera-side substitute for the missing `F1`/`F2`.**
`cs5FCIncest_lift` below proves exactly the single-edge case Simpson's Lifting Lemma needs at each
node of the tree it lifts: raising the *source* of an `r`-edge along `≤` still reaches *some*
upward extension of the old target. Composed with `ckforces_persistence` (`Forcing.lean:122`,
persistence of `CKForces` under `≤`, itself confluence-free), this is enough to carry every
already-established fact at a raised node's `r`-neighbours forward to a matching raised value.
This makes a *tree-restricted* Lifting Lemma analogue for `cs5FCIncest` models plausible (matching
Simpson's own restriction of Theorem 8.1.4 and the Lifting Lemma to `G` a tree), **not yet proved
in full** -- see "What remains".

## What remains (handoff for the next Phase 11.1 dispatch)

1. **The tree-shape invariant.** `NIK`'s `(□I)`/`(◇E)` rules quantify cofinitely over the fresh
   label `y` (`∀ y ∉ L, ...`); the main soundness induction must always instantiate this
   cofinite premise at a label *fresh to the whole derivation so far* (never an old/reused label),
   which keeps the raw graph `G` tree-shaped throughout the induction -- mirroring Simpson's own
   "we must ensure that throughout the induction we can restrict attention to graphs that are
   trees" remark. This needs its own lemma/invariant, threaded through the main induction.
2. **The graph-lifting lemma proper** (the tree analogue of Simpson's 8.1.3): given an
   interpretation `ρ` of a tree `G`'s labels satisfying edge-cond (`∀ a b, G.R a b → r (ρ a) (ρ
   b)`) and Γ-cond (`∀ ψ ∈ Γ, CKForces (ρ ψ.lbl) ψ.prop`), and a raise `w' ≥ ρ x` for one label
   `x` of `G`, produce `ρ'` agreeing with `ρ` off `x`'s descendants, with `ρ' x = w'`, every
   descendant's value raised (`≥` its old value) via `cs5FCIncest_lift` propagated down the tree,
   and edge-cond/Γ-cond re-established for `ρ'` (Γ-cond via `ckforces_persistence` at each raised
   descendant). This is a structural/well-founded recursion over the (finite, per-derivation) tree
   depth below `x`.
3. **The main soundness induction** over `NIK`'s 12 constructors, generalizing over an arbitrary
   interpretation `ρ` (edge-cond + Γ-cond), concluding `CKForces (ρ x) A`. The `(□I)`/`(◇E)` cases
   use (1)+(2) to instantiate the cofinite premise at a fresh label mapped to the semantically
   required world; `boxE`/`diaI` need item 4 below for their `TClosure`-edge hypothesis.
4. **Phase 11.2**: validate that each `cs5FCIncest` conjunct soundly interprets the matching
   `TClosure` (T/B/4) edge-closure rule (`raw G.R a b → r (ρa)(ρb)` extends to `TClosure 𝒯 G.R a b
   → r (ρa)(ρb)`), then assemble `nik_TS5_soundness`.
5. **Phase 11.3**: `nik_TS5_consistent : ¬ NIKTheorem TS5 ⊥` via a **one-point reflexive**
   `cs5FCIncest` model (`World := PUnit`, `r`/`≤` both the total relation, `botForces := fun _ =>
   False`). Note this model is small enough that the tree-lifting machinery of items 1-3 is not
   needed for THIS specific corollary (every interpretation is forced to the unique point, so
   "lifting" is trivial) -- if 11.2's general induction is not reached in a future dispatch, 11.3's
   antivacuity result can be attempted directly against this one model without waiting on the
   general theorem, per the plan's own documented fallback (Rollback/Contingency).

## Contents (this dispatch)

- `cs5FCIncest_lift`: the interpretation-lifting building block (item 2's core ingredient).
- `nik_soundness_onePoint`: a full 12-constructor `NIK` soundness induction against the
  one-point model, proved directly (Phase 11.3's accelerant route, see above).
- `nik_TS5_consistent`: the anti-vacuity certificate, `¬ NIKTheorem TS5 ⊥`, a direct one-line
  corollary of `nik_soundness_onePoint`.

## References

* [A. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 8, §8.1.2 (Soundness), Lemma 8.1.3 (Lifting Lemma), Theorem 8.1.4.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Labelled

open Cslib.Logic.Modal

/-! ## Interpretation-lifting for `cs5FCIncest` models -/

/-- **Interpretation-lifting ("F2-analogue") for `cs5FCIncest` models.** Raising the *source* of
an `r`-edge along `≤` still reaches *some* `≤`-upward extension of the old target. This is the
Wijesekera-side substitute (derived directly from `cs5FCIncest`'s `cs5Incest`/`r_symBox`
conjuncts, NOT a transcription of Simpson's `F1`/`F2` birelational Lifting Lemma -- see the module
docstring's "Why this cannot be transcribed literally" section) for the single-edge case Simpson's
Lifting Lemma (8.1.3) needs at each node of the tree it lifts. -/
theorem cs5FCIncest_lift {World : Type*} [Preorder World] {r : World → World → Prop}
    (hfc : cs5FCIncest r) {w u w' : World} (hwu : r w u) (hww' : w ≤ w') :
    ∃ u', u ≤ u' ∧ r w' u' := by
  obtain ⟨_, _, _, hsymbox, hincest⟩ := hfc
  obtain ⟨u₁, hu_u₁, hu₁w⟩ := hincest hwu
  obtain ⟨t, hw't, hu₁t⟩ := hsymbox hu₁w hww'
  exact ⟨t, hu_u₁.trans hu₁t, hw't⟩

/-! ## One-point soundness and the anti-vacuity certificate (Phase 11.3) -/

/-- **Soundness of `N_IK(𝒯)` against the one-point model, for any `𝒯`.** Every label of the
derivation is interpreted at the unique point `()` of `Unit`, with the modal relation set to the
total relation (`fun _ _ => True`) and `botForces` arbitrary. Because there is only one possible
world, "raising the interpretation of one label" (the crux of the outstanding Lifting-Lemma
machinery -- see the module docstring's "What remains") is trivially the identity, so this
induction needs none of it: the `(□I)`/`(◇E)` cases simply pick any label fresh to the finite
exclusion set `L` (using `Infinite (Label Atom)`, via the injective `Label.var`) and re-apply the
cofinite premise's induction hypothesis at the same, unique point. The `(□E)`/`(◇I)` cases need
no relational-edge hypothesis at all (`hR`/`hR`/`hru` are unused beyond pattern-matching) because
the total relation makes every `r`-step trivial (`trivial : True`). This is NOT a special case of
the general `nik_TS5_soundness` (not yet landed); it is a self-contained soundness argument
against a single, degenerate model, used only to certify anti-vacuity (`nik_TS5_consistent`
below). -/
theorem nik_soundness_onePoint {Atom : Type u} {𝒯 : Set GeomAxiom} {val : Unit → Atom → Prop}
    {G : Graph Atom} {Γ : List (LabelledFormula Atom)} {φ : LabelledFormula Atom}
    (h : NIK 𝒯 G Γ φ) :
    (∀ ψ ∈ Γ, CKForces (fun (_ _ : Unit) => True) val (fun _ => False) () ψ.prop) →
      CKForces (fun (_ _ : Unit) => True) val (fun _ => False) () φ.prop := by
  induction h with
  | assumption G Γ φ hmem => intro hΓ; exact hΓ _ hmem
  | efq G Γ x y A h ih =>
      intro hΓ
      exact absurd (ih hΓ) (by simp)
  | andI G Γ x A B _ _ ihA ihB => intro hΓ; exact ⟨ihA hΓ, ihB hΓ⟩
  | andE1 G Γ x A B _ ih => intro hΓ; exact (ih hΓ).1
  | andE2 G Γ x A B _ ih => intro hΓ; exact (ih hΓ).2
  | orI1 G Γ x A B _ ih => intro hΓ; exact Or.inl (ih hΓ)
  | orI2 G Γ x A B _ ih => intro hΓ; exact Or.inr (ih hΓ)
  | orE G Γ x y A B C hor hA hB ihor ihA ihB =>
      intro hΓ
      rcases ihor hΓ with h1 | h2
      · exact ihA (by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact h1
          · exact hΓ _ hψ)
      · exact ihB (by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact h2
          · exact hΓ _ hψ)
  | impI G Γ x A B h ih =>
      intro hΓ w' hw' hAforced
      cases w'
      exact ih (by
        intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hAforced
        · exact hΓ _ hψ)
  | impE G Γ x A B himp hA ihimp ihA =>
      intro hΓ
      exact ihimp hΓ () (le_refl _) (ihA hΓ)
  | boxE G Γ x y A hR h ih =>
      intro hΓ
      exact ih hΓ () (le_refl _) () trivial
  | boxI L hL G Γ x A h ih =>
      intro hΓ w' hw' u hru
      cases w'; cases u
      have hInf : Infinite (Label Atom) := by
        have hinj : Function.Injective (Label.var (Atom := Atom)) := by
          intro a b hab; cases hab; rfl
        exact Infinite.of_injective _ hinj
      obtain ⟨y, hy⟩ := hL.infinite_compl.nonempty
      exact ih y hy hΓ
  | diaI G Γ x y A hR h ih =>
      intro hΓ w' hw'
      exact ⟨(), trivial, ih hΓ⟩
  | diaE L hL G Γ x z A B hdia h ihdia ih =>
      intro hΓ
      obtain ⟨u, hru, hAu⟩ := ihdia hΓ () (le_refl _)
      cases u
      have hInf : Infinite (Label Atom) := by
        have hinj : Function.Injective (Label.var (Atom := Atom)) := by
          intro a b hab; cases hab; rfl
        exact Infinite.of_injective _ hinj
      obtain ⟨y, hy⟩ := hL.infinite_compl.nonempty
      exact ih y hy (by
        intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact hAu
        · exact hΓ _ hψ)

/-- **Anti-vacuity certificate** (Phase 11.3): `N(TS5)` does not prove `⊥`. Direct corollary of
`nik_soundness_onePoint`, instantiated with `botForces := fun _ => False`: were `⊥` a theorem,
`nik_soundness_onePoint` would force `CKForces ... () ⊥ = False` (`Γ = []` discharges the
context-condition vacuously), a contradiction. This certifies Phase 10's `cs5_completeness` is a
*meaningful* statement (`N(TS5)` does not prove everything), per reports/11 condition 2. -/
theorem nik_TS5_consistent {Atom : Type u} :
    ¬ NIKTheorem TS5 (Proposition.bot : Proposition Atom) := by
  intro h
  exact nik_soundness_onePoint (val := fun _ _ => True) h (by simp)

end Cslib.Logic.Modal.Labelled

end
