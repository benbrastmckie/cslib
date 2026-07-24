/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.FrameClass

/-! # Labelled-System Completeness (Simpson 1994 Thm 8.1.4, Option B)

This module assembles the prior results into `cs5_completeness`, the **completeness** direction
of A. K. Simpson's Theorem 8.1.4 [Simpson1994] (reflowed `L1367-1425`) for the graph-**labelled**
natural-deduction system `N_IK(𝒯_S5)` (`NIK`/`Deriv`, `Deduction.lean`/`Context.lean`) against
`cs5FCIncest` birelation models (`CS5Canonical.lean:255`).

## Scope: labelled-system completeness, NOT Hilbert completeness

**This is completeness of the graph-labelled `NIK`/`Deriv` system, not the Hilbert axiomatization
`CS5ModalAxiom`/`Derivable`.** Simpson's Theorem 8.1.4 itself targets his labelled system `N(𝒯)`;
the Hilbert reading (`CKValidFC cs5FCIncest φ → Derivable CS5ModalAxiom φ`) is a *separate*
composite result, `Thm 6.2.1 ∘ Thm 8.1.4`, that additionally needs Simpson's Chapter 6 adequacy
bridge (`NIKDerivable TS5 φ → Derivable CS5ModalAxiom φ`). That bridge is **deliberately not built**
here — it is a substantial separate research undertaking, with no mechanization anywhere in this
repository. Option B (this file's target) is a faithful, non-vacuous mechanization of Simpson's
completeness theorem in its own right; the Hilbert identification is explicitly deferred future
work.
`cs5_completeness` below is never a silent Hilbert relabelling: its type is exactly `CKValidFC
cs5FCIncest φ → NIKDerivable TS5 φ`, and every identifier it composes (`primeLemma`,
`canon_truth_lemma`, `cs5FCIncest_canonWorld_r`, the five `canon*` side-conditions) is already
landed sorry-free — this is a genuine *composition*, with no new hard lemma.

## Proof shape (Simpson `L1367-1425`, the standard contrapositive canonical-model argument)

Assume `¬ NIKDerivable TS5 φ`, i.e. `¬ NIK TS5 (Graph.trivial Atom) [] (x₀ ∶ φ)` for the trivial
graph's distinguished node `x₀`. This is exactly the refutation seed `primeLemma` consumes
directly (`Context.trivialBase`, below) -- no Hilbert bridge is needed to produce it, which is the
whole point of Option B:

1. `primeLemma` (Lemma 8.2.4 / 5.3.1, **landed** `PrimeLemma.lean:1703`) extends the trivial base
   context to a `TS5`-prime bounded context `P` with `(x₀ ∶ φ) ∉ P.Γ`.
2. `canon_truth_lemma` (Lemma 5.3.2/8.2.6, **landed** `CanonicalModel.lean:267`) transports this to
   `¬ CKForces CanonWorld.r canonVal canonBotForces w φ` at the pointed world `w := ⟨P, x₀, _⟩`.
3. `cs5FCIncest_canonWorld_r` (Lemma 8.2.5, **landed** `FrameClass.lean:192`) supplies the
   `cs5FCIncest` frame condition on `CanonWorld.r`.
4. The five fallible-world side-conditions `CKValidFC` demands are the **landed** `canonVal_mono`,
   `canonBotForces_mono`, `canonBotForces_val`, `canonBotForces_r`, `canonBotForces_r_wit`
   (`CanonicalModel.lean:224-242`).
5. Instantiating a hypothetical `CKValidFC cs5FCIncest φ` at this canonical model and at `w`
   contradicts step 2, giving `¬ CKValidFC cs5FCIncest φ`. Contrapositive complete.

## Universe instantiation

`CKValidFC` (`CKExtension.lean:86`) is polymorphic in a second universe `v` for its quantified
`World`. Completeness necessarily instantiates `World` at the *specific* canonical model
`CanonWorld TS5 Atom : Type u` (the same universe as `Atom`), so -- exactly as the segment-based
analogue `ckvalidFC_completeness` does (`CKExtension.lean:248`, `CKValidFC.{u, u} FC φ`) -- this
module states `cs5_completeness` at `CKValidFC.{u, u}`, not an independently-quantified `v`.

## Contents

- `Context.trivialBase`: the base context underlying `NIKDerivable` (the trivial graph, empty
  assumption set), packaged as a `Context TS5 Atom` so `primeLemma` can consume it.
- `deriv_trivialBase_iff`: `Deriv` against the trivial base's empty `Γ` is exactly `NIK` against
  the empty list -- the bridge between `NIKDerivable`'s `NIK`-shape and `primeLemma`'s `Deriv`-shape
  hypothesis.
- `cs5_completeness`: the assembled labelled-system completeness theorem.

## References

* [A. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 8, Theorem 8.1.4 (completeness direction).
-/

@[expose] public section

namespace Cslib.Logic.Modal.Labelled

open Cslib.Logic.Modal

universe u
variable {Atom : Type u}

/-! ## The trivial base context -/

/-- The base context underlying `NIKDerivable` (`Deduction.lean:316`): the trivial graph (a single
node, no edges), paired with the empty assumption set. Packaged as a `Context 𝒯 Atom` so
`primeLemma` can be seeded directly from `¬ NIKDerivable 𝒯 φ`. -/
def Context.trivialBase (𝒯 : Set GeomAxiom) (Atom : Type u) : Context 𝒯 Atom where
  G := Graph.trivial Atom
  Γ := ∅
  ctxSubset := fun _ h => h.elim
  coinfinite := ⟨{0}, (Set.finite_singleton 0).infinite_compl, fun x hx => by
    rcases hx with rfl
    exact Set.mem_singleton 0⟩
  dwitnessMem := fun x A h => absurd h (by simp [Graph.trivial])

/-- The trivial base context's domain element (the trivial graph's distinguished node) lies in
its own domain -- the `hx₀` hypothesis `primeLemma` needs. -/
theorem Context.mem_trivialBase (𝒯 : Set GeomAxiom) (Atom : Type u) :
    (Graph.trivial Atom).nonempty.choose ∈ (Context.trivialBase 𝒯 Atom).G.X :=
  (Graph.trivial Atom).nonempty.choose_spec

/-- `Deriv` against the trivial base context's empty `Γ` is exactly `NIK` against the empty
assumption list: the only list every one of whose members lies in `∅` is `[]` itself. This bridges
`NIKDerivable`'s `NIK`-shaped statement to `primeLemma`'s `Deriv`-shaped hypothesis. -/
theorem deriv_trivialBase_iff {𝒯 : Set GeomAxiom} {φ : LabelledFormula Atom} :
    Deriv 𝒯 (Context.trivialBase 𝒯 Atom).G (Context.trivialBase 𝒯 Atom).Γ φ ↔
      NIK 𝒯 (Graph.trivial Atom) [] φ := by
  constructor
  · rintro ⟨Γ₀, hΓ₀, hNIK⟩
    match Γ₀, hΓ₀ with
    | [], _ => exact hNIK
    | ψ :: rest, hΓ₀ => exact (hΓ₀ ψ (List.mem_cons_self)).elim
  · intro h
    exact ⟨[], fun ψ hψ => absurd hψ (List.not_mem_nil), h⟩

/-! ## The completeness theorem -/

/-- **Constructive labelled completeness of `N_IK(𝒯_S5)` w.r.t. `cs5FCIncest` birelation models**
(A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic* [Simpson1994],
Theorem 8.1.4, completeness direction). This is completeness of the graph-**labelled** `NIK`/
`Deriv` natural-deduction system -- **NOT** the Hilbert axiomatization `CS5ModalAxiom`/
`Derivable`. It coincides with Hilbert completeness (`Derivable CS5ModalAxiom φ`) only via
Simpson's Chapter 6 adequacy bridge (Thm 6.2.1), which is **deliberately not built here** (see the
module docstring's "Scope" section). A genuine composition of the prior results (`primeLemma`,
`canon_truth_lemma`, `cs5FCIncest_canonWorld_r`, and the five `canon*` side-conditions), all
already landed sorry-free -- no new hard lemma. -/
theorem cs5_completeness {Atom : Type u} (φ : Proposition Atom) :
    CKValidFC.{u, u} cs5FCIncest φ → NIKDerivable TS5 φ := by
  intro hvalid
  by_contra hn
  set x₀ : Label Atom := (Graph.trivial Atom).nonempty.choose with hx₀def
  have hx₀ : x₀ ∈ (Context.trivialBase TS5 Atom).G.X := Context.mem_trivialBase TS5 Atom
  have h0 : ¬ Deriv TS5 (Context.trivialBase TS5 Atom).G (Context.trivialBase TS5 Atom).Γ
      (x₀ ∶ φ) := by
    rw [deriv_trivialBase_iff]
    exact hn
  obtain ⟨P, hle, hnd⟩ := primeLemma (Context.trivialBase TS5 Atom) x₀ φ hx₀ h0
  have hxP : x₀ ∈ P.G.X := hle.1.1 hx₀
  set w : CanonWorld TS5 Atom := ⟨P, x₀, hxP⟩ with hwdef
  have hnf : ¬ CKForces CanonWorld.r canonVal canonBotForces w φ := by
    rw [canon_truth_lemma]
    intro hmem
    exact hnd (Deriv.of_mem hmem)
  exact hnf (hvalid (CanonWorld TS5 Atom) CanonWorld.r cs5FCIncest_canonWorld_r canonVal
    canonBotForces (fun p h hv => canonVal_mono p h hv) (fun h hb => canonBotForces_mono h hb)
    (fun p hb => canonBotForces_val p hb) (fun hb hr => canonBotForces_r hb hr)
    (fun hb => canonBotForces_r_wit hb) w)

end Cslib.Logic.Modal.Labelled

end
