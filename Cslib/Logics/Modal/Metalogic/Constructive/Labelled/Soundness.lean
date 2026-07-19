/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical

/-! # Labelled-System Soundness (Task 517 Phase 11, Simpson 1994 Thm 8.1.4, Soundness Direction)

**Status: interpretation machinery only (Phase 11.1, partial).** This module lands the first,
reusable building block of the full labelled soundness direction `nik_TS5_soundness : NIKTheorem
TS5 φ → CKValidFC cs5FCIncest φ`, which will complete the Simpson 8.1.4 biconditional alongside
`cs5_completeness` (`Completeness.lean`). The main soundness induction and the anti-vacuity
corollary `nik_TS5_consistent` are **not yet landed** -- see "What remains" below and the
continuation handoff at `specs/517_labelled_bounded_context_cs5_completeness/handoffs/`.

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

end Cslib.Logic.Modal.Labelled

end
