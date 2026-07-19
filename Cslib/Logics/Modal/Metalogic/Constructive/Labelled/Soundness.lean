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
COMPLETE). General `nik_TS5_soundness` assessed INTRACTABLE at standard single-dispatch
implementation effort after three dispatches (see "Third dispatch" section below) -- recommend a
dedicated re-plan/research pass, not a fourth direct-implementation attempt.** This module lands
(1) the first, reusable building block of the full labelled soundness direction
`nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ`, which will complete the Simpson
8.1.4 biconditional alongside `cs5_completeness` (`Completeness.lean`); and (2) the anti-vacuity
certificate `nik_TS5_consistent : ¬ NIKTheorem TS5 ⊥`, landed via a **direct, self-contained
route** (see "The anti-vacuity route taken" below) rather than as a corollary of the
not-yet-landed general theorem. The general `nik_TS5_soundness` (Phase 11.1's tree-lifting
machinery + Phase 11.2's `TClosure` validation) is **not yet landed** -- see "What remains" below,
"Third dispatch" below (the current, sharpest assessment), and the continuation handoffs at
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
5. **Phase 11.3, `nik_TS5_consistent` -- LANDED**, via the plan's own pre-authorized direct route
   (Rollback/Contingency), **before** items 1-4 rather than as their corollary: a one-point model
   (`World := Unit`, `r := fun _ _ => True`) makes "lifting" trivially the identity, so none of
   items 1-4's machinery is needed for this specific corollary. See `nik_soundness_onePoint` below.

## Refined analysis of items 1-4 (this dispatch, NOT yet reduced to code -- for the next dispatch)

A second, deeper look at items 1-4 this dispatch (attempting an actual Lean encoding of the
`(□I)` case, not merely re-stating the architecture) surfaced a sharper obstruction than either
this module's or the continuation handoff's prior framing captured, recorded here so the next
attempt does not re-discover it from scratch:

- **`TS5 = {T, B, Four}` makes `TClosure TS5 G.R` an equivalence relation**, and `G` is *always
  connected* (every `Graph.addEdge` attaches a brand-new label to an already-present one, starting
  from `Graph.trivial`'s single node -- `G` is literally a tree as an undirected graph). An
  equivalence closure of a connected graph's edge relation is the **total relation on the vertex
  set**: `TClosure TS5 G.R a b` holds for **every** `a, b ∈ G.X`, not just tree-adjacent pairs.
  Consequently edge-cond (`∀ a b, TClosure TS5 G.R a b → r (ρ a) (ρ b)`) is not a "propagate along
  tree edges" condition as items 1-2's original framing suggested -- it demands `r` hold between
  `ρ` of **every pair of labels used so far in the derivation**, i.e. the interpreted image of
  `G.X` under `ρ` must be an `r`-clique. Introducing one new label (`(□I)`/`(◇E)`'s fresh `y`)
  therefore requires relating `ρ' y` to **every** existing label's image, not merely to its
  immediate parent -- a materially larger obligation than a single-edge lift.
- **`cs5FCIncest_lift`'s raised witness is not exact**, and edge-cond as stated needs exactness.
  Attempting `ρ' y := u` (the semantically-required successor from `hru : r w' u`, `w' ≥ ρ x`) to
  close the new label's clique-membership against some *other*, already-present label `a` needs
  `r (ρ a) u` from `r (ρ a) (ρ x)` (known) and `r w' u`, `ρ x ≤ w'` (known) -- this is exactly
  `hfour`'s shape (`r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t`, `w := ρ a`, `u := ρ x`,
  `u' := w'`, `t := u`), but `hfour` only delivers `r v u` for **some** `v ≥ ρ a`, not `r (ρ a) u`
  exactly -- so satisfying the clique condition for label `a` forces **also** raising `a`'s own
  interpreted value to that `v`, cascading the obligation to `a`'s own clique-neighbours in turn.
- **The resolution is not symmetric between edge-cond and Γ-cond.** Γ-cond survives raising `ρ`
  pointwise for free, via `ckforces_persistence` (`CKForces` is upward-closed, so if `ψ ∈ Γ` was
  forced at the old `ρ ψ.lbl` and the new value is `≥` the old, Γ-cond still holds at the new
  value). Edge-cond has no such slack -- it is a flat fact about `r`, not about `CKForces`, so it
  cannot be "topped up" after the fact the way Γ-cond can. This asymmetry is why only edge-cond
  needs a genuine lifting lemma: **not** a tree-path propagation (items 1-2's original framing),
  but a lemma of the shape "given a *finite* set `S` of labels already `r`-clique-related under
  `ρ`, and one member `x ∈ S` raised to `w' ≥ ρ x`, produce `ρ' ≥ ρ` pointwise on `S` (raised, not
  merely at `x`) that is *again* an `r`-clique" -- a finite-induction argument over `S` using
  `hfour`/`hsymbox`/`hincest` pairwise, not a tree-depth recursion. This lemma is not yet attempted
  in Lean; it is the concrete next step for items 1-2, and should supersede their original
  "propagate down the tree" phrasing above (kept for historical context, not as the target shape).

## Third dispatch: why the direct-induction route is now assessed INTRACTABLE at standard effort
(NOT yet reduced to code; this is a decisive tractability finding, not a missing-lemma gap)

This dispatch (the third to touch general `nik_TS5_soundness`) attempted to actually close the
finite-clique-relift lemma the second dispatch's "Refined analysis" section above targets, both
for the `(□I)` producer side (a fresh label's exact image) and, independently, for the `(□E)`
consumer side (an *already-fixed*, non-fresh label reached via a `TClosure.symm`-derived edge).
Both sides hit the same root obstruction, confirmed by direct Lean-level proof attempts (not just
re-stated architecture), and a battery of finite hand-constructed candidate models was used to
probe whether the obstruction is real or just unexplored. The finding:

1. **A type-level observation.** Of `cs5FCIncest`'s five conjuncts, only `hrefl` and `htrans`
   have a *non-existential* (`∀`-only) conclusion; `hfour`, `hsymbox`, and `hincest` all conclude
   `∃ v/t/u', ... ∧ r ...` — a *raised* witness, never the exact original point. Consequently the
   only way to derive an EXACT fact `r a b` for two independently-fixed points `a`, `b` is a chain
   of `hrefl`/`htrans` composed from already-exact "seed" facts — `hfour`/`hsymbox`/`hincest` can
   only ever *introduce* a fresh raised point into the chain, never pin one down to a
   pre-specified target. This directly blocks the `(□I)` producer side: `CKForces`'s `box` clause
   (`Forcing.lean:75`) universally quantifies its successor `u` (`∀ w' ≥ w, ∀ u, r w' u → ...`) --
   `u` is handed to the proof adversarially, not chosen by it -- so the fresh label `y`'s
   interpretation must be *exactly* `u` (persistence only goes upward, so a raised substitute
   `u' ≥ u` cannot be "rounded back down"), yet the edge-cond fact `r (ρ a) u` this exactness
   demands, for every other already-used label `a`, is exactly the kind of fact `hfour`
   cannot produce without also raising `a`'s own image -- as the second dispatch found -- and
   THIS dispatch additionally traced that raising `a` does not itself terminate in an exact fact
   either, for the same reason one level up.
2. **The `(□E)`-consumer side needs the same exactness, independently of freshness.** `boxE`
   consumes an *arbitrary* `TClosure`-derived edge `hR : TClosure 𝒯 G.R x y`, including one
   derived via `.symm` (`B ∈ TS5`) from a *raw, one-directional* edge `G.R y x` (`Graph.addEdge`
   only ever adds a directed `a = x ∧ b = y` disjunct, never both directions). If the "natural"
   invariant only interprets raw edges directly (`r (ρ y) (ρ x)` from `G.R y x`), soundly using
   `boxE` at the `TClosure.symm`-reversed edge needs `r (ρ x) (ρ y)` -- i.e. *exact* symmetry of
   `r` on this specific already-fixed pair, where `x`/`y` are NOT necessarily fresh (they may
   already be pinned by other uses in `Γ` or earlier subderivations, so their images cannot be
   freely raised without invalidating those other uses). `cs5Incest` supplies only the raised
   substitute (`r w u → ∃ u' ≥ u, r u' w`), not exact symmetry.
3. **Finite hand-constructed models could not exhibit a stable asymmetric example.** Several
   candidate finite relations on `Fin n`/`ℕ` (with the standard linear `≤`) satisfying
   `hincest`+`hfour` kept being forced, by exact `htrans` composing the newly-introduced raised
   witnesses back around, into satisfying full symmetric (indeed often total/clique) closure on
   the finitely-generated substructure anyway -- e.g. a 3-point "cycle + backward witnesses"
   attempt (`0 → 1`, a `hincest`-mandated back-witness `2 → 0`, forcing `2 → 1` by `htrans`)
   remained genuinely asymmetric (`r 0 1` without `r 1 0`) only until `hsymbox` was patched by
   adding an outgoing edge from `1`, at which point `htrans` immediately chained it back into
   `r 1 0`, collapsing the intended asymmetry. This was reproduced under several variations and
   never escaped: **no finite countermodel refuting `cs5FCIncest → ` symmetry-on-generated-points
   was found**, but a full formal proof of the positive direction (`cs5FCIncest` DOES force
   symmetric/clique closure on any finitely-generated substructure) was also not completed --
   direct proof attempts chaining `hincest`/`hfour`/`hsymbox` pairwise did not close either. This
   is genuinely unresolved, not merely unattempted: it is the single largest scope unknown left in
   this proof direction, and resolving it (either direction) would decisively settle whether the
   clique-relift lemma is provable by finite induction, or needs different machinery entirely.
4. **A concrete, actionable recommendation for whoever picks this up next**, given (3)'s
   "finite models keep collapsing into full closure" pattern: this looks structurally like a
   FIXPOINT/closure-completion problem (build the smallest `r`-clique containing a given finite
   seed and closed under `hincest`/`hfour`/`hsymbox`'s raised witnesses), not a simple
   induction-over-a-fixed-finite-set problem -- which is exactly the shape of the `FLO`
   maximal-extension machinery already landed for the completeness direction (Phases 1-7,
   `PrimeLemma.lean`/probes). **Investigating whether the landed `FLO`/chain-union machinery can
   be reused or adapted for this closure construction is the single most promising concrete next
   step**, ahead of either of the two heavier alternatives below.
5. **Escalation-protocol assessment (per the task's anti-churn directive): this direction is NOT
   tractable at standard single-dispatch implementation effort.** Three dispatches have each
   materially sharpened the obstruction (not thrashed or repeated prior work), converging on a
   genuine open mathematical question (item 3 above), not a missing Mathlib lemma or a
   straightforward-but-long proof. Recommended next steps, in order of estimated cost:
   - (a) **Cheapest, try first**: a focused (few-hour) investigation of whether `cs5FCIncest`
     provably forces symmetric/clique closure on finitely-generated substructures (item 3's open
     question), reusing/adapting the `FLO` closure machinery (item 4) if it resolves positively.
   - (b) **Simpson's own recommended route** (`8.1.2`, quoted above): formalize the modified
     sequent system `L_m(𝒯, ∅)` with `𝒯`-closure baked into `(⊃L)`/`(⊃R)_m`, which Simpson states
     is needed *specifically* to avoid the non-tree-excursion problem this dispatch keeps hitting.
     Substantial new proof-theoretic infrastructure (a new derivation system + translation lemmas
     + its own soundness proof) -- re-plan scale (likely 300-600+ lines), not a dispatch
     continuation.
   - (c) Build the Hilbert-labelled equivalence bridge (Ch. 6, already flagged as deferred future
     work in this plan's Phase 12 notes) and obtain labelled soundness as a corollary of the
     *already-proven*, sorry-free `cs5_soundness_derivable_incest` (`CS5Canonical.lean:373`) --
     this is exactly the large Ch. 6 gap Option B of this plan deliberately deferred, so reopening
     it is itself a scope decision for the user/orchestrator, not this dispatch.
   None of (a)-(c) is attempted in this dispatch; each is genuinely re-plan/research-pass scale,
   not a direct continuation. No `sorry`, no new axiom, and no vacuous placeholder was introduced
   to force a result -- per the anti-churn directive, this finding is landed as documentation only.

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
