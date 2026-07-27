/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Intuitionistic.TruthLemma

/-! # Completeness for Intuitionistic Modal Logic (Birelational Canonical Model)

This module is the final assembly step of the birelational canonical-model construction for
intuitionistic modal logic. It packages the canonical worlds/`Preorder`/`canonicalR`/
`canonicalVal` and the frame conditions `canonical_f1`/`canonical_f2` (`CanonicalModel.lean`)
into a concrete `BModel` term (`canonicalBModel`), and combines `canonical_truth_lemma`
(`TruthLemma.lean`) with `modal_prime_exclusion` (`PrimeTheory.lean`) on the target (underivable)
formula to obtain the two parametric weak-completeness statements
`ivalid_completeness`/`mvalid_completeness`.

Both statements carry the union of the five modal-axiom hypotheses `{ h_K, h_Kdia, h_Idb, h_Cd,
h_dbot }` established as the definitive minimal set, plus the intuitionistic base hypotheses, as
loose parametric hypotheses -- never global `axiom`s. `h_efq` is threaded separately (used, via
`canonical_truth_lemma`, by both statements' `imp`/`box` cases) and `botForces` remains a
truth-lemma parameter throughout: `ivalid_completeness` instantiates it to `fun _ => False` (the
intuitionistic convention), `mvalid_completeness` instantiates it to an arbitrary upward-closed
predicate (membership of `⊥` in the world's underlying theory), matching [Simpson1994]'s
`IValid`/`MValid` distinction. This framework is a sound completeness witness only for logics
containing `Cd + Idb`; bare CK cannot reuse the box/diamond witnesses and must build a separate
segment/fallible-world construction -- out of scope here.

A parametric **consistency hook** (`canonical_prime_world_nonempty_of_consistent`) is also
exposed: given that the axiom system `Axioms` is consistent (`⊥` is not a theorem), the canonical
model is inhabited by at least one prime world. No concrete axiom system's consistency is
discharged here.

## Main Definitions

- `canonicalBModel`: the assembled canonical `BModel (CanonicalPrimeWorld Axioms) Atom`, threading
  `canonicalR`/`canonicalVal`/`canonical_f1`/`canonical_f2` and a parametric `botForces`.
- `canonical_prime_world_nonempty_of_consistent`: the consistency hook.
- `ivalid_completeness`: `IValid φ → Derivable Axioms φ`, the intuitionistic instantiation
  (`botForces := fun _ => False`).
- `mvalid_completeness`: `MValid φ → Derivable Axioms φ`, the minimal instantiation (arbitrary
  upward-closed `botForces`).

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational canonical model, `IValid`/`MValid`).
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43, Lemma 5.5.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## Canonical Birelational Model Assembly -/

section CanonicalBModelAssembly

variable {Axioms : Proposition Atom → Prop}

/-- **The canonical birelational model**: assembles `CanonicalPrimeWorld`, the canonical
`Preorder` instance (set inclusion), `canonicalR`, `canonicalVal`, and the frame conditions
`canonical_f1`/`canonical_f2` (all `CanonicalModel.lean`) into a concrete
`BModel (CanonicalPrimeWorld Axioms) Atom` term, confirming the birelational canonical frame/model
data (`Cslib.Logic.Modal.BModel`, `Birelational.lean`) is fully instantiated by this framework's
witnesses. `botForces` is threaded as a **parameter** (never hard-coded), together with its
upward-closure proof, so both the intuitionistic (`ivalid_completeness`,
`botForces := fun _ => False`) and minimal (`mvalid_completeness`,
`botForces := fun w => ⊥ ∈ w.val`) instantiations below reuse this single assembly. -/
def canonicalBModel
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
    (botForces : CanonicalPrimeWorld Axioms → Prop)
    (bf_upward_closed : ∀ {w w' : CanonicalPrimeWorld Axioms},
      w ≤ w' → botForces w → botForces w') :
    BModel (CanonicalPrimeWorld Axioms) Atom where
  r := canonicalR
  f1 := canonical_f1 h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
    h_andI h_andE1 h_andE2 h_K h_Kdia h_Cd h_dbot
  f2 := canonical_f2 h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
    h_andI h_andE1 h_andE2 h_K h_Kdia h_Idb
  v := canonicalVal
  botForces := botForces
  v_upward_closed := fun p hw hv => canonicalVal_upward_closed p hw hv
  bf_upward_closed := bf_upward_closed

end CanonicalBModelAssembly

/-! ## Consistency Hook -/

section ConsistencyHook

variable {Axioms : Proposition Atom → Prop}

/-- **Consistency hook**: if the axiom system `Axioms` is consistent (`⊥` is not derivable from
the empty context), the canonical model is inhabited by at least one prime world. This is a
*parametric* statement -- concrete consistency of a specific axiom system (IK, CK, ...) is
discharged downstream by whichever module instantiates this framework, not here: this framework
exposes the hook only. Proved via `modal_prime_exclusion` (`PrimeTheory.lean`) excluding `⊥` from
the deductive closure of `∅`: any finite sublist of the closure of `∅` reduces
(`modal_deriv_from_closure_to_S`) to a derivation from `∅` itself, i.e. from `[]`, so consistency
of the closure follows directly from `h_cons`. -/
theorem canonical_prime_world_nonempty_of_consistent
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_cons : ¬ Derivable Axioms (Proposition.bot : Proposition Atom)) :
    Nonempty (CanonicalPrimeWorld Axioms) := by
  have h_cons_closure : ModalSetConsistent Axioms
      (modalDeductiveClosure Axioms (∅ : Set (Proposition Atom))) := by
    intro L hL hd
    obtain ⟨L', hL'_sub, hL'_deriv⟩ :=
      modal_deriv_from_closure_to_S h_implyK h_implyS L hL Proposition.bot hd
    have hL'_nil : L' = [] := by
      by_contra hne
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L' hne
      exact absurd (hL'_sub a ha) ((Set.mem_empty_iff_false a).mp)
    rw [hL'_nil] at hL'_deriv
    exact h_cons hL'_deriv
  have h_adm : Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms)
      (modalDeductiveClosure Axioms (∅ : Set (Proposition Atom))) :=
    ⟨h_cons_closure, fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd⟩
  have h_bot_not_mem : (Proposition.bot : Proposition Atom) ∉
      modalDeductiveClosure Axioms (∅ : Set (Proposition Atom)) := by
    rintro ⟨L, hL_sub, hd⟩
    have hL_nil : L = [] := by
      by_contra hne
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L hne
      exact absurd (hL_sub a ha) ((Set.mem_empty_iff_false a).mp)
    rw [hL_nil] at hd
    exact h_cons hd
  obtain ⟨Tval, _, hprimeT, _⟩ :=
    modal_prime_exclusion h_implyK h_implyS h_efq h_orE h_adm h_bot_not_mem
  exact ⟨⟨Tval, hprimeT⟩⟩

end ConsistencyHook

/-! ## Parametric Completeness -/

section ParametricCompleteness

variable {Axioms : Proposition Atom → Prop}

/-- **Parametric intuitionistic completeness**: any formula `φ` that is `IValid` (forced at every
world of every birelational model with `botForces := fun _ => False`) is derivable from
`Axioms`. Carries the union of the five modal-axiom hypotheses `{ h_K, h_Kdia, h_Idb, h_Cd,
h_dbot }` plus the intuitionistic base.

Proof by contrapositive on `Derivable Axioms φ`, case-splitting on consistency of the deductive
closure of `∅` (mirroring `Cslib.Logic.PL.int_strong_completeness`'s Γ = ∅ instantiation):
- **Consistent case**: `modal_prime_exclusion` builds a canonical prime world `w₀` excluding `φ`;
  instantiating `IValid` at the canonical model (via `canonical_f1`/`canonical_f2`) and applying
  `canonical_truth_lemma` (with the `botForces := fun _ => False` bridge discharged by
  `canonical_bot_not_mem`) forces `φ ∈ w₀.val`, contradicting the exclusion.
- **Inconsistent case**: the closure of `∅` deriving `⊥` reduces (via
  `modal_deriv_from_closure_to_S`) to `Derivable Axioms ⊥` directly; EFQ (`h_efq`) then derives
  `φ`, contradicting the contrapositive hypothesis. -/
theorem ivalid_completeness
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
    {φ : Proposition Atom} (h_valid : IValid.{u, u} φ) :
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
  · -- Consistent case: build the canonical prime world excluding `φ`, apply `IValid`.
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
      h_valid (CanonicalPrimeWorld Axioms) canonicalR
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

/-- **Parametric minimal completeness**: any formula `φ` that is `MValid` (forced at every world
of every birelational model with an *arbitrary* upward-closed `botForces`) is derivable from
`Axioms`. Same axiom hypotheses and proof structure as `ivalid_completeness`, but instantiates
`MValid`'s arbitrary `botForces` parameter to `fun w => ⊥ ∈ w.val` (membership of `⊥` in the
canonical world's underlying theory), which is upward-closed for free via the canonical
`Preorder`'s set-inclusion `≤` -- no `h_dbot`-style bridging hypothesis is needed for this
direction, unlike the box/diamond witnesses. -/
theorem mvalid_completeness
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
    {φ : Proposition Atom} (h_valid : MValid.{u, u} φ) :
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
  · -- Consistent case: build the canonical prime world excluding `φ`, apply `MValid`.
    have h_adm : Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms)
        (modalDeductiveClosure Axioms (∅ : Set (Proposition Atom))) :=
      ⟨h_cons, fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd⟩
    obtain ⟨Tval, _, hprimeT, hexclT⟩ :=
      modal_prime_exclusion h_implyK h_implyS h_efq h_orE h_adm h_not_mem
    let w0 : CanonicalPrimeWorld Axioms := ⟨Tval, hprimeT⟩
    have h_forces : BForces canonicalR canonicalVal
        (fun w => (Proposition.bot : Proposition Atom) ∈ w.val) w0 φ :=
      h_valid (CanonicalPrimeWorld Axioms) canonicalR
        (canonical_f1 h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
          h_andI h_andE1 h_andE2 h_K h_Kdia h_Cd h_dbot)
        (canonical_f2 h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
          h_andI h_andE1 h_andE2 h_K h_Kdia h_Idb)
        canonicalVal (fun w => (Proposition.bot : Proposition Atom) ∈ w.val)
        canonicalVal_upward_closed (fun hle hmem => hle hmem) w0
    have h_phi_mem : φ ∈ w0.val :=
      (canonical_truth_lemma h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
        h_andI h_andE1 h_andE2 h_K h_Kdia h_Idb h_Cd h_dbot
        (fun w => (Proposition.bot : Proposition Atom) ∈ w.val) (fun _ => Iff.rfl)
        φ w0).mp h_forces
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

end ParametricCompleteness

end Cslib.Logic.Modal
