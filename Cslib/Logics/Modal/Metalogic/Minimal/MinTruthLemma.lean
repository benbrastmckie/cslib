/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Minimal.MinCanonicalModel

/-! # Truth Lemma for `MK`

This module proves `min_canonical_truth_lemma`, the canonical truth lemma over quasi-prime `MK`
worlds, by structural induction on `Proposition`. It mirrors
`Intuitionistic/TruthLemma.lean`'s `canonical_truth_lemma`, but:

- the `bot` case is `Iff.rfl` directly (`minBotForces w := ⊥ ∈ w.val`, matching `BForces`'s
  `.bot` clause definitionally) -- no `canonical_bot_not_mem`, no consistency, no `efq`;
- the `imp` case uses `imp_refuting_theory` (`Constructive/SegmentLindenbaum.lean:142`,
  efq-free) directly -- since `MinCanonicalPrimeWorld` worlds are already quasi-prime, no
  separate "witness, then extend to prime" two-step is needed (unlike `IK`'s
  `modal_imp_witness` + `modal_prime_exclusion`);
- the `box`/`diamond` cases consume `min_canonical_box_witness`/`min_canonical_diamond_witness`
  (`MinCanonicalModel.lean`, this task's Phase 3) instead of `canonical_box_witness`/
  `canonical_diamond_witness`.

## Main Definitions

- `min_canonical_truth_lemma`: `BForces canonicalR canonicalVal minBotForces w φ ↔ φ ∈ w.val`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3.
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Modus-Ponens Closure Helper -/

/-- Modus ponens closure for `MinCanonicalPrimeWorld`: if `(φ → ψ) ∈ w.val` and `φ ∈ w.val`,
then `ψ ∈ w.val`. Modal analogue of `canonical_imp_property`
(`Intuitionistic/TruthLemma.lean:99-111`), via `w`'s deductive closure. -/
theorem min_canonical_imp_property {w : MinCanonicalPrimeWorld Atom} {φ ψ : Proposition Atom}
    (h_imp : (φ.imp ψ) ∈ w.val) (h_phi : φ ∈ w.val) : ψ ∈ w.val := by
  apply w.property.closed [φ.imp ψ, φ] ψ
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h_imp
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · exact h_phi
      · nomatch hx''
  · exact ⟨.modus_ponens _ _ _
      (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
      (.assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩

/-! ## Non-Modal Truth-Lemma Cases -/

/-- **Atom case**: forcing of an atom at a canonical world coincides with membership, by
definition of `canonicalVal`. -/
theorem min_truth_atom_case (w : MinCanonicalPrimeWorld Atom) (p : Atom) :
    BForces canonicalR canonicalVal minBotForces w (Proposition.atom p) ↔
      (Proposition.atom p) ∈ w.val :=
  Iff.rfl

/-- **Bot case**: `BForces … w ⊥ ↔ ⊥ ∈ w.val` is `Iff.rfl` directly, since `BForces`'s `.bot`
clause is definitionally `botForces w` and `minBotForces w := ⊥ ∈ w.val`. No consistency
argument, no `efq` -- the key simplification over `IK`'s `canonical_bot_not_mem`-based `.bot`
case (`Intuitionistic/TruthLemma.lean:132-148`), matching `min_truth_lemma`'s `.bot` case
(`MinStrongCompleteness.lean:128`). -/
theorem min_truth_bot_case (w : MinCanonicalPrimeWorld Atom) :
    BForces canonicalR canonicalVal minBotForces w Proposition.bot ↔
      (Proposition.bot : Proposition Atom) ∈ w.val :=
  Iff.rfl

/-- **Conjunction case**, taking the two sub-formula truth-lemma instances as explicit
induction-hypothesis parameters. Transliterated from `truth_and_case`
(`Intuitionistic/TruthLemma.lean:157-201`), `CanonicalPrimeWorld` → `MinCanonicalPrimeWorld`,
`w.property.1.2` → `w.property.closed`. -/
theorem min_truth_and_case
    {w : MinCanonicalPrimeWorld Atom} {φ ψ : Proposition Atom}
    (ihφ : BForces canonicalR canonicalVal minBotForces w φ ↔ φ ∈ w.val)
    (ihψ : BForces canonicalR canonicalVal minBotForces w ψ ↔ ψ ∈ w.val) :
    BForces canonicalR canonicalVal minBotForces w (φ.and ψ) ↔ (φ.and ψ) ∈ w.val := by
  constructor
  · intro ⟨hφ, hψ⟩
    have h_phi_w := ihφ.mp hφ
    have h_psi_w := ihψ.mp hψ
    apply w.property.closed [φ, ψ] (φ.and ψ)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h_phi_w
      · rcases List.mem_cons.mp hx' with rfl | hx''
        · exact h_psi_w
        · nomatch hx''
    · exact ⟨.modus_ponens _ _ _
        (.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (MKModalAxiom.andI φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))))
        (.assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩
  · intro h_mem
    have hφ_mem : φ ∈ w.val := by
      apply w.property.closed [φ.and ψ] φ
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_mem
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (MKModalAxiom.andE1 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
    have hψ_mem : ψ ∈ w.val := by
      apply w.property.closed [φ.and ψ] ψ
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_mem
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (MKModalAxiom.andE2 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
    exact ⟨ihφ.mpr hφ_mem, ihψ.mpr hψ_mem⟩

/-- **Disjunction case**, taking the two sub-formula truth-lemma instances as explicit
induction-hypothesis parameters. The backward direction uses the quasi-prime world's disjunction
property (`w.property.disj`). Transliterated from `truth_or_case`
(`Intuitionistic/TruthLemma.lean:211-243`). -/
theorem min_truth_or_case
    {w : MinCanonicalPrimeWorld Atom} {φ ψ : Proposition Atom}
    (ihφ : BForces canonicalR canonicalVal minBotForces w φ ↔ φ ∈ w.val)
    (ihψ : BForces canonicalR canonicalVal minBotForces w ψ ↔ ψ ∈ w.val) :
    BForces canonicalR canonicalVal minBotForces w (φ.or ψ) ↔ (φ.or ψ) ∈ w.val := by
  constructor
  · intro h_or
    rcases h_or with hφ | hψ
    · have h_phi_w := ihφ.mp hφ
      apply w.property.closed [φ] (φ.or ψ)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_phi_w
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (MKModalAxiom.orI1 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
    · have h_psi_w := ihψ.mp hψ
      apply w.property.closed [ψ] (φ.or ψ)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_psi_w
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (MKModalAxiom.orI2 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
  · intro h_mem
    rcases w.property.disj h_mem with h | h
    · exact Or.inl (ihφ.mpr h)
    · exact Or.inr (ihψ.mpr h)

/-- **Implication case**, taking the two sub-formula truth-lemma instances as explicit
induction-hypothesis parameters, **universally quantified over all canonical worlds** (needed
because the forward direction constructs a fresh successor world). Uses `imp_refuting_theory`
(efq-free, single-step -- `MinCanonicalPrimeWorld` worlds are already quasi-prime, so no
separate "witness then extend to prime" is needed, unlike `truth_imp_case`'s
`modal_imp_witness` + `modal_prime_exclusion`). -/
theorem min_truth_imp_case
    {w : MinCanonicalPrimeWorld Atom} {φ ψ : Proposition Atom}
    (ihφ : ∀ T : MinCanonicalPrimeWorld Atom,
      BForces canonicalR canonicalVal minBotForces T φ ↔ φ ∈ T.val)
    (ihψ : ∀ T : MinCanonicalPrimeWorld Atom,
      BForces canonicalR canonicalVal minBotForces T ψ ↔ ψ ∈ T.val) :
    BForces canonicalR canonicalVal minBotForces w (φ.imp ψ) ↔ (φ.imp ψ) ∈ w.val := by
  constructor
  · intro h_forces
    by_contra h_not_mem
    obtain ⟨T_set, hwT, hT_qp, hφT, hψT⟩ :=
      imp_refuting_theory (fun φ ψ => MKModalAxiom.implyK φ ψ)
        (fun φ ψ χ => MKModalAxiom.implyS φ ψ χ) (fun A B χ => MKModalAxiom.orE A B χ)
        w.property h_not_mem
    let T : MinCanonicalPrimeWorld Atom := ⟨T_set, hT_qp⟩
    have hle : w ≤ T := hwT
    have hf_φ := (ihφ T).mpr hφT
    have hf_ψ := h_forces T hle hf_φ
    exact hψT ((ihψ T).mp hf_ψ)
  · intro h_mem T hle hf_φ
    have h_imp_T : (φ.imp ψ) ∈ T.val := hle h_mem
    have h_φ_T : φ ∈ T.val := (ihφ T).mp hf_φ
    have h_ψ_T : ψ ∈ T.val := min_canonical_imp_property h_imp_T h_φ_T
    exact (ihψ T).mpr h_ψ_T

/-! ## Modal Truth-Lemma Cases -/

/-- **Box case**: forcing of `□φ` coincides with `□φ ∈ w.val`, given the induction hypothesis
for `φ` universally quantified over all canonical worlds. Forward direction (contrapositive) via
`min_canonical_box_witness`; backward direction is heredity over `≤ ∘ canonicalR`. -/
theorem min_truth_box_case
    {w : MinCanonicalPrimeWorld Atom} {φ : Proposition Atom}
    (ih : ∀ T : MinCanonicalPrimeWorld Atom,
      BForces canonicalR canonicalVal minBotForces T φ ↔ φ ∈ T.val) :
    BForces canonicalR canonicalVal minBotForces w (Proposition.box φ) ↔
      (Proposition.box φ) ∈ w.val := by
  simp only [BForces_box]
  constructor
  · intro h_forces
    by_contra h_notbox
    obtain ⟨w', u, hww', hRw'u, hphi_notU⟩ := min_canonical_box_witness h_notbox
    exact hphi_notU ((ih u).mp (h_forces w' hww' u hRw'u))
  · intro h_mem w' hww' u hRw'u
    have hbox_w' : (Proposition.box φ) ∈ w'.val := hww' h_mem
    have hphi_u : φ ∈ u.val := hRw'u.1 φ hbox_w'
    exact (ih u).mpr hphi_u

/-- **Diamond case**: forcing of `◇φ` coincides with `◇φ ∈ w.val`, given the induction
hypothesis for `φ` universally quantified over all canonical worlds. Forward direction uses
`canonicalR`'s diamond clause directly (no modal axiom needed); backward direction via
`min_canonical_diamond_witness`. -/
theorem min_truth_diamond_case
    {w : MinCanonicalPrimeWorld Atom} {φ : Proposition Atom}
    (ih : ∀ T : MinCanonicalPrimeWorld Atom,
      BForces canonicalR canonicalVal minBotForces T φ ↔ φ ∈ T.val) :
    BForces canonicalR canonicalVal minBotForces w (Proposition.diamond φ) ↔
      (Proposition.diamond φ) ∈ w.val := by
  simp only [BForces_diamond]
  constructor
  · rintro ⟨u, hRwu, hforces_u⟩
    exact hRwu.2 φ ((ih u).mp hforces_u)
  · intro h_mem
    obtain ⟨v, hRwv, hphi_v⟩ := min_canonical_diamond_witness h_mem
    exact ⟨v, hRwv, (ih v).mpr hphi_v⟩

/-! ## Assembled Truth Lemma -/

/-- **The canonical truth lemma for `MK`**: forcing of any proposition `φ` at any canonical
quasi-prime world `w` coincides with membership `φ ∈ w.val`. Assembled by structural induction
on `φ`, dispatching each of the seven `Proposition` constructors to its helper. Mirrors
`canonical_truth_lemma` (`Intuitionistic/TruthLemma.lean:465-501`) but `botForces` is hard-coded
to `minBotForces` (not a loose parameter -- the `.bot` case is `Iff.rfl`), and no `efq`/`h_dbot`
hypothesis is threaded anywhere. -/
theorem min_canonical_truth_lemma (φ : Proposition Atom) (w : MinCanonicalPrimeWorld Atom) :
    BForces canonicalR canonicalVal minBotForces w φ ↔ φ ∈ w.val := by
  induction φ generalizing w with
  | atom p => exact min_truth_atom_case w p
  | bot => exact min_truth_bot_case w
  | and φ ψ ihφ ihψ => exact min_truth_and_case (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ => exact min_truth_or_case (ihφ w) (ihψ w)
  | imp φ ψ ihφ ihψ => exact min_truth_imp_case ihφ ihψ
  | box φ ihφ => exact min_truth_box_case ihφ
  | diamond φ ihφ => exact min_truth_diamond_case ihφ

end Cslib.Logic.Modal
