/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IK

/-! # Frame-Condition-Parametrized Extensions of the Birelational Canonical Model

This module is the shared scaffold for task 494 (intuitionistic modal extensions `IT`/`IS4`/`IS5`
of `IK`, [Simpson1994] Ch. 3). It generalizes the task-480/492 birelational canonical-model
framework (`IValid`, `ivalid_completeness`, `Completeness.lean`) to validity/completeness over
a restricted *class* of birelational frames, cut out by an arbitrary frame condition `FC` on the
modal relation `r` (e.g. `Reflexive`, `Transitive`, `Symmetric`). This lets each per-system file
(`IT.lean`, `IS4.lean`, `IS5.lean`) bolt its frame condition onto validity/completeness without
touching any task-480/492 asset.

The three new declarations here are:

- `IValidFC`: a copy of `IValid` (`Birelational.lean:193`) with one extra hypothesis `FC r`
  threaded in alongside the up/down-confluence conditions `f1`/`f2`. `IValid` itself is
  untouched; `IValidFC` coexists with it.
- `ivalidFC_completeness`: a ~2-line generalization of `ivalid_completeness`
  (`Completeness.lean:187`) that additionally takes `h_canonFC : FC (@canonicalR Atom Axioms)`
  and threads it into the `h_valid` application, concluding completeness over `FC`-frames. All
  other axiom dischargers, `canonicalBModel`/`canonical_truth_lemma`/`modal_prime_exclusion`
  machinery, and the consistent/inconsistent case split are reused from `ivalid_completeness`
  verbatim.
- `axiom_mem`: a one-line helper (`Axioms φ → φ ∈ w.val` for a `CanonicalPrimeWorld`) used by
  every per-extension canonical-closure proof to place an axiom instance into a prime theory via
  the theory's deductive closure.

No new frame-condition predicates are defined here: per the plan's Non-Goals, `IT`/`IS4`/`IS5`
reuse Mathlib's `Reflexive`/`Transitive`/`Symmetric` (already polymorphic over `α → α → Prop`)
directly as `FC` instantiations, rather than introducing bespoke predicates or a generic
"extension typeclass" (the latter's payoff is small and would obscure the three concrete
instantiations reviewers expect, mirroring how classical `Systems/{T,S4,S5}` stay separate).

## Main Definitions

- `IValidFC`: frame-condition-parametrized birelational validity.
- `ivalidFC_completeness`: parametric completeness over `FC`-frames.
- `axiom_mem`: axiom-instance membership in a canonical prime world.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational frame classes for `T`/`S4`/`S5`, `IValid`).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43, Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## Frame-Condition-Parametrized Validity -/

/-- A formula is `FC`-frame-valid (`IValidFC`) if it is forced at every world in every
birelational model whose modal relation `r` additionally satisfies the frame condition `FC`
(e.g. `Reflexive`, `Transitive`, `Symmetric`), on top of the usual up/down-confluence conditions
`f1`/`f2` and `botForces := fun _ => False` (the intuitionistic convention, as in `IValid`).
`IValid` itself (`Birelational.lean:193`) is the special case `FC := fun _ => True`; it is left
untouched, and `IValidFC`/`IValid` coexist. -/
def IValidFC (FC : {World : Type v} → (World → World → Prop) → Prop)
    (φ : Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (r : World → World → Prop) (_fc : FC r)
    (_f1 : ∀ {w w' u : World}, w ≤ w' → r w u → ∃ u', r w' u' ∧ u ≤ u')
    (_f2 : ∀ {w u u' : World}, r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u')
    (val : World → Atom → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    ∀ w, BForces r val (fun _ => False) w φ

/-! ## Parametric Completeness over `FC`-Frames -/

section ParametricFCCompleteness

variable {Axioms : Proposition Atom → Prop}

/-- **Parametric completeness over `FC`-frames**: any formula `φ` that is `IValidFC FC` (forced
at every world of every birelational model whose relation satisfies `FC`, with
`botForces := fun _ => False`) is derivable from `Axioms`, given that the canonical relation
`canonicalR` itself satisfies `FC` (`h_canonFC`). This is the ~2-line generalization of
`ivalid_completeness` (`Completeness.lean:187`): identical statement and proof, except for the
extra `FC`/`h_canonFC` parameters and threading `h_canonFC` into the `h_valid` application (the
consistent case builds the same canonical prime world `w0` excluding `φ` via
`modal_prime_exclusion`, and the inconsistent case is the same EFQ argument). -/
theorem ivalidFC_completeness
    (FC : {World : Type u} → (World → World → Prop) → Prop)
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_Kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_Idb : ∀ (φ ψ : Proposition Atom),
      Axioms (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))))
    (h_Cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_dbot : Axioms ((◇Proposition.bot).imp Proposition.bot))
    (h_canonFC : FC (@canonicalR Atom Axioms))
    {φ : Proposition Atom} (h_valid : IValidFC.{u, u} FC φ) :
    Derivable Axioms φ := by
  by_contra h_not_deriv
  have h_not_mem : φ ∉ modalDeductiveClosure Axioms (∅ : Set (Proposition Atom)) := by
    rintro ⟨L, hL_sub, hd⟩
    have hL_nil : L = [] := by
      by_contra hne
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L hne
      exact absurd (hL_sub a ha) ((Set.mem_empty_iff_false a).mp)
    rw [hL_nil] at hd
    exact h_not_deriv hd
  by_cases h_cons :
      ModalSetConsistent Axioms (modalDeductiveClosure Axioms (∅ : Set (Proposition Atom)))
  · -- Consistent case: build the canonical prime world excluding `φ`, apply `IValidFC`.
    have h_adm : Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms)
        (modalDeductiveClosure Axioms (∅ : Set (Proposition Atom))) :=
      ⟨h_cons, fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd⟩
    obtain ⟨Tval, _, hprimeT, hexclT⟩ :=
      modal_prime_exclusion h_implyK h_implyS h_efq h_orE h_adm h_not_mem
    let w0 : CanonicalPrimeWorld Axioms := ⟨Tval, hprimeT⟩
    have h_bot_bridge : ∀ w : CanonicalPrimeWorld Axioms,
        (fun _ => False) w ↔ (Proposition.bot : Proposition Atom) ∈ w.val :=
      fun w => ⟨fun h => h.elim, fun h => absurd h (canonical_bot_not_mem w)⟩
    have h_forces : BForces canonicalR canonicalVal (fun _ => False) w0 φ :=
      h_valid (CanonicalPrimeWorld Axioms) canonicalR h_canonFC
        (canonical_f1 h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
          h_andI h_andE1 h_andE2 h_K h_Kdia h_Cd h_dbot)
        (canonical_f2 h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
          h_andI h_andE1 h_andE2 h_K h_Kdia h_Idb)
        canonicalVal canonicalVal_upward_closed w0
    have h_phi_mem : φ ∈ w0.val :=
      (canonical_truth_lemma h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
        h_andI h_andE1 h_andE2 h_K h_Kdia h_Idb h_Cd h_dbot
        (fun _ => False) h_bot_bridge φ w0).mp h_forces
    exact hexclT h_phi_mem
  · -- Inconsistent case: EFQ produces `Derivable Axioms φ`, contradicting `h_not_deriv`.
    simp only [ModalSetConsistent, Metalogic.SetConsistent, Metalogic.Consistent,
      not_forall, not_not] at h_cons
    obtain ⟨L', hL'_sub, hL'_bot⟩ := h_cons
    obtain ⟨L'', hL''_sub, hL''_deriv⟩ :=
      modal_deriv_from_closure_to_S h_implyK h_implyS L' hL'_sub Proposition.bot hL'_bot
    have hL''_nil : L'' = [] := by
      by_contra hne
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L'' hne
      exact absurd (hL''_sub a ha) ((Set.mem_empty_iff_false a).mp)
    rw [hL''_nil] at hL''_deriv
    obtain ⟨d_bot⟩ := hL''_deriv
    have d_efq : DerivationTree Axioms [] (Proposition.bot.imp φ) := .ax [] _ (h_efq φ)
    exact h_not_deriv ⟨.modus_ponens [] _ _ d_efq d_bot⟩

end ParametricFCCompleteness

/-! ## Axiom Membership Helper -/

section AxiomMem

variable {Axioms : Proposition Atom → Prop}

/-- **Axiom membership**: any axiom instance `Axioms φ` belongs to every canonical prime world's
underlying theory. Used by every per-extension canonical-closure proof (`IT`/`IS4`/`IS5`) to
place an axiom instance (e.g. `tBox`, `fourDia`, `bBox`) into a prime theory, via the theory's
deductive closure (`w.property.1.2`) applied to the empty context and the one-step
`DerivationTree.ax` derivation. -/
theorem axiom_mem {w : CanonicalPrimeWorld Axioms} {φ : Proposition Atom} (h : Axioms φ) :
    φ ∈ w.val :=
  w.property.1.2 [] φ (fun _ h => nomatch h) ⟨.ax [] _ h⟩

end AxiomMem

end Cslib.Logic.Modal
