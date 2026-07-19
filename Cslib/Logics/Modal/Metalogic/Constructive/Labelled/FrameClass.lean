/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.CanonicalModel
public import Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical

/-! # Frame-Class Match: `CanonWorld.r` satisfies `cs5FCIncest` (Task 517 Phase 9)

This module discharges the frame-class conditions `cs5FCIncest` (`CS5Canonical.lean:255`) needs,
for the **labelled/bounded-context** canonical model `CanonWorld TS5 Atom` (`CanonicalModel.lean`)
built from `primeLemma`'s output. This is the frame-class match Phase 10's `cs5_completeness`
assembly consumes, matching `cs5_axiom_sound_incest`'s target (`CS5Canonical.lean:279`), NOT the
older `cs5FC''` (`CKExtension.lean:184`, task 509) that `cs5FCIncest` corrects (see
`CS5Canonical.lean`'s module docstring, "`cs5FCIncest` is therefore `cs5FC''` with ONLY its plain
symmetry conjunct replaced").

## The design nuance this module resolves

`CanonWorld.le` (context extension at a fixed label) is **not literally `cs5FCIncest`'s `≤`** --
it is the `Preorder` CSLib already builds on `CanonWorld TS5 Atom` via the `CKForces`
instantiation. `cs5FCIncest`'s five conjuncts are stated abstractly over `{World} [Preorder World]
(r : World → World → Prop)`; this module instantiates `World := CanonWorld TS5 Atom`,
`r := CanonWorld.r` DIRECTLY against the **general** `CanonWorld` (ranging over every `TPrime TS5
Atom`, matching Simpson's `𝒦^𝒯`) -- no restricted world-type subtype is introduced. This works,
where the analogous match FAILED for `CS5Canonical.lean`'s `CS5CanonSegment`/`CS5PrimeSegment`
world types (`cs5Incest_cs5CanonMreach_false`, `cs5Incest_cs5PrimeMreach_false`), because of a
structural difference in what the two canonical relations are built from:

- `CS5CanonSegment`/`CS5PrimeSegment`'s relation is **box-based**: `r w u := boxInv w.head ⊆
  u.head`, a one-sided containment with no witness that the *reverse* containment holds. The
  failure proof (`cs5Incest_forces_symm`) shows this forces `cs5Incest`'s mediating witness to be
  `u' := u` and then requires PLAIN symmetry of `r`, which fails concretely at the universally
  reachable exploding world `Ω` (`head = Set.univ`).
- `CanonWorld.r w u := w.ctx = u.ctx ∧ w.ctx.G.R w.lbl u.lbl` is the **raw graph relation**, and
  `TPrime.clModel : ClassicalModelOn TS5 G.X G.R` supplies genuine, already-landed
  reflexivity/symmetry/transitivity **on `G.X`** (`equivalence_of_classicalModelOn_TS5`,
  `Context.lean:399`) -- not a one-sided containment. So the same `u' := u` witness `cs5Incest`
  needs is available directly from `EquivalenceOn.symm`, with no monotonicity-collapse argument
  to defeat it. There is no `CanonWorld` analogue of `Ω`: `TPrime`'s Consistency clause bans any
  exploding node from every context in the type (see the point-of-use notes on
  `cs5Incest_forces_symm`/`cs5TwoSidedR_iff_cs5Tail` below), so the guardrail that sank the
  `CS5Canonical.lean` route simply has no target here.

No relation is swapped and no frame condition is weakened to make this go through -- every
conjunct of `cs5FCIncest` is proved for the literal `CanonWorld.r`/`CanonWorld.le` pair.

## Point-of-use notes on the two landed guardrails (task 517 Phase 9, item 3)

- **`cs5Incest_forces_symm` (`CS5Canonical.lean:643`) does not trip here.** That theorem is a
  conditional: IF a box-based relation (`hbox : r w u → boxInv (head w) ⊆ head u`) satisfies
  `cs5Incest`, THEN it is forced into plain symmetry. `CanonWorld.r` is not box-based (no `head`/
  `boxInv` anywhere in its definition), so the theorem's hypotheses do not even parse against it;
  it is simply inapplicable, not falsified. (Coincidentally, `CanonWorld.r` DOES turn out to be
  plain-symmetric on same-context pairs -- `CanonWorld.r_incest` below -- which is exactly the
  "true, harmless theorem" outcome `cs5Incest_forces_symm`'s own docstring anticipates for a
  relation with no reachable `Ω`; see `Context.lean`'s module docstring, guardrail 2.)
- **`cs5TwoSidedR_iff_cs5Tail` (`CS5Canonical.lean:511`) does not trip here.** That theorem
  equates Simpson's diamond-clause relation `cs5TwoSidedR` with the old `cs5Tail` wall **over
  `CS5` quasi-prime theories** (`QuasiPrime CS5ModalAxiom -`). `CanonWorld.r` is not built from
  `cs5TwoSidedR`/theory membership at all -- it is the raw graph relation `H.G.R` on `TPrime`
  contexts, which are graph-node structures, not quasi-prime theories. The `iff`'s hypotheses
  have no instance here. (`Context.lean`'s module docstring, guardrail 3, already recorded this
  for `TPrime` generally; this note confirms it holds specifically at the point where `cs5Incest`
  is discharged.)

## Contents

- `TPrime.equivOn`: the domain-relative `EquivalenceOn G.X G.R`, read off `TPrime.clModel` at
  `TS5` via `equivalence_of_classicalModelOn_TS5` (near-immediate, per the plan).
- `CanonWorld.r_refl`/`CanonWorld.r_trans`: the plain reflexivity/transitivity conjuncts.
- `CanonWorld.r_rebase`: the `fourBox`-style re-basing conjunct (needs only transitivity).
- `CanonWorld.r_symBox`: the `bBox`-style re-basing conjunct (needs symmetry).
- `CanonWorld.r_incest`: `cs5Incest CanonWorld.r` (the `bDia`-instance; witness `u' := u`, plain
  symmetry).
- `cs5FCIncest_canonWorld_r`: the bundled frame-class match, consumed by Phase 10.

## References

* [A. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994]
* [S. Marin, D. Morales and L. Straßburger, *A Fully Labelled Proof System for Intuitionistic
  Modal Logics*][MarinMoralesStrassburger2021]
-/

@[expose] public section

namespace Cslib.Logic.Modal.Labelled

open Cslib.Logic.Modal

universe u
variable {Atom : Type u}

/-! ## The domain-relative equivalence, at `TS5` -/

/-- The domain-relative equivalence `TPrime.clModel` supplies at `TS5`: near-immediate from
`equivalence_of_classicalModelOn_TS5` (`Context.lean:399`), a direct projection of `H`'s
clause 0. -/
theorem TPrime.equivOn (H : TPrime TS5 Atom) : EquivalenceOn H.G.X H.G.R :=
  equivalence_of_classicalModelOn_TS5 H.clModel

/-! ## The five `cs5FCIncest` conjuncts for `CanonWorld.r` -/

/-- `CanonWorld.r` is reflexive: same context (`rfl`), and `w.ctx.G.R w.lbl w.lbl` from
`EquivalenceOn.refl` at `w.lbl ∈ w.ctx.G.X` (`w.mem`). -/
theorem CanonWorld.r_refl (w : CanonWorld TS5 Atom) : CanonWorld.r w w :=
  ⟨rfl, w.ctx.equivOn.refl w.lbl w.mem⟩

/-- `CanonWorld.r` is transitive: contexts agree (`Eq.trans`), and the two `G.R` facts compose
via `EquivalenceOn.trans` once rewritten into the shared context `w.ctx`. -/
theorem CanonWorld.r_trans {w u t : CanonWorld TS5 Atom}
    (hwu : CanonWorld.r w u) (hut : CanonWorld.r u t) : CanonWorld.r w t := by
  obtain ⟨hctx1, hR1⟩ := hwu
  obtain ⟨hctx2, hR2⟩ := hut
  refine ⟨hctx1.trans hctx2, ?_⟩
  rw [← hctx1] at hR2
  have hmemU : u.lbl ∈ w.ctx.G.X := by
    have h := u.mem; rw [hctx1]; exact h
  have hmemT : t.lbl ∈ w.ctx.G.X := by
    have h := t.mem; rw [hctx1, hctx2]; exact h
  exact w.ctx.equivOn.trans w.lbl w.mem u.lbl hmemU t.lbl hmemT hR1 hR2

/-- **The `fourBox`-style re-basing conjunct** (`cs5FCIncest`'s third conjunct,
`CS5Canonical.lean:258`). Only needs transitivity, no symmetry: the mediating world `v` is built
at `t`'s context with `w`'s label, and `t.ctx.G.R w.lbl t.lbl` is assembled by transporting
`r w u`'s edge forward along `u ≤ u'`'s monotonicity and composing with `r u' t`'s edge, both
inside the shared context `t.ctx`. -/
theorem CanonWorld.r_rebase {w u u' t : CanonWorld TS5 Atom}
    (hwu : CanonWorld.r w u) (hle : u ≤ u') (hu't : CanonWorld.r u' t) :
    ∃ v, w ≤ v ∧ CanonWorld.r v t := by
  obtain ⟨hctx1, hR1⟩ := hwu
  obtain ⟨hleCtx, hlbl⟩ := hle
  obtain ⟨hctx2, hR2⟩ := hu't
  have hleWU' : w.ctx.toContext ≤ u'.ctx.toContext := by rw [hctx1]; exact hleCtx
  have hleWT : w.ctx.toContext ≤ t.ctx.toContext := by rw [hctx2] at hleWU'; exact hleWU'
  have hmemV : w.lbl ∈ t.ctx.G.X := hleWT.1.1 w.mem
  refine ⟨⟨t.ctx, w.lbl, hmemV⟩, ⟨hleWT, rfl⟩, ⟨rfl, ?_⟩⟩
  have hRu : u.ctx.G.R w.lbl u.lbl := by rw [hctx1] at hR1; exact hR1
  have hRu' : u'.ctx.G.R w.lbl u.lbl := hleCtx.1.2 _ _ hRu
  rw [hlbl] at hRu'
  rw [hctx2] at hRu'
  have hRu't : t.ctx.G.R u'.lbl t.lbl := by rw [hctx2] at hR2; exact hR2
  have hmemU' : u'.lbl ∈ t.ctx.G.X := by
    have h := u'.mem; rw [hctx2] at h; exact h
  exact t.ctx.equivOn.trans w.lbl hmemV u'.lbl hmemU' t.lbl t.mem hRu' hRu't

/-- **The `bBox`-style re-basing conjunct** (`cs5FCIncest`'s fourth conjunct,
`CS5Canonical.lean:259`, the `FCsym_box`-shaped clause). This one genuinely needs symmetry: the
mediating world `t` is built at `u'`'s context with `w`'s label, and `u'.ctx.G.R u'.lbl w.lbl` is
obtained by transporting `r w u`'s edge forward along `u ≤ u'` and then reversing it via
`EquivalenceOn.symm`. -/
theorem CanonWorld.r_symBox {w u u' : CanonWorld TS5 Atom}
    (hwu : CanonWorld.r w u) (hle : u ≤ u') :
    ∃ t, CanonWorld.r u' t ∧ w ≤ t := by
  obtain ⟨hctx1, hR1⟩ := hwu
  obtain ⟨hleCtx, hlbl⟩ := hle
  have hleWU' : w.ctx.toContext ≤ u'.ctx.toContext := by rw [hctx1]; exact hleCtx
  have hmemT : w.lbl ∈ u'.ctx.G.X := hleWU'.1.1 w.mem
  refine ⟨⟨u'.ctx, w.lbl, hmemT⟩, ⟨rfl, ?_⟩, ⟨hleWU', rfl⟩⟩
  have hRu : u.ctx.G.R w.lbl u.lbl := by rw [hctx1] at hR1; exact hR1
  have hRu' : u'.ctx.G.R w.lbl u.lbl := hleCtx.1.2 _ _ hRu
  rw [hlbl] at hRu'
  exact u'.ctx.equivOn.symm w.lbl hmemT u'.lbl u'.mem hRu'

/-- **`cs5Incest` for `CanonWorld.r`** (the `bDia`-instance, `cs5FCIncest`'s fifth conjunct,
`CS5Canonical.lean:234`). The witness is `u' := u` itself (`le_refl`) -- plain symmetry on the
shared context, via `EquivalenceOn.symm`. See the module docstring's point-of-use note on
`cs5Incest_forces_symm` for why this landing on plain symmetry is expected here (no reachable
`Ω`), not a contradiction of that guardrail. -/
theorem CanonWorld.r_incest : cs5Incest (@CanonWorld.r Atom TS5) := by
  intro w u hwu
  obtain ⟨hctx1, hR1⟩ := hwu
  refine ⟨u, le_refl u, hctx1.symm, ?_⟩
  have hmemW : w.lbl ∈ u.ctx.G.X := by
    have h := w.mem; rw [hctx1] at h; exact h
  rw [hctx1] at hR1
  exact u.ctx.equivOn.symm w.lbl hmemW u.lbl u.mem hR1

/-! ## The bundled frame-class match -/

/-- **`CanonWorld.r` (over `TS5`) satisfies `cs5FCIncest`.** This is the frame-class match Phase
10's `cs5_completeness` assembly consumes: combined with `canon_truth_lemma`
(`CanonicalModel.lean:267`) and `cs5_soundness_derivable_incest`
(`CS5Canonical.lean:373`)/`cs5_axiom_sound_incest` (`CS5Canonical.lean:279`), it lets the
contrapositive assembly instantiate `CKValidFC cs5FCIncest` at the labelled canonical model built
from `primeLemma`'s refuting context. -/
theorem cs5FCIncest_canonWorld_r : cs5FCIncest (@CanonWorld.r Atom TS5) :=
  ⟨CanonWorld.r_refl, CanonWorld.r_trans, CanonWorld.r_rebase, CanonWorld.r_symBox,
    CanonWorld.r_incest⟩

end Cslib.Logic.Modal.Labelled

end
