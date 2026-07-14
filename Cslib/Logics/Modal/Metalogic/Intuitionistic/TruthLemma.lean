/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel

/-! # Truth Lemma for Intuitionistic Modal Logic (Non-Modal Cases)

This module contains Phase 3a and Phase 3b of the birelational canonical-model truth lemma
(task 480 plan v4). Phase 3a proves the **five non-modal cases** (`atom`, `bot`, `and`, `or`,
`imp`) as standalone named helper lemmas, transliterated line-for-line from
`Cslib.Logic.PL.int_truth_lemma`
(`Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean:108-214`,
`PL.Proposition Atom` → `Proposition Atom`, `IntPropAxiom` → `Axioms`). Phase 3b adds
`truth_box_case`, the `.box` constructor case, consuming the pair-shaped
`canonical_box_witness` (Phase 2b) and heredity over `≤ ∘ R`.

Each case is a **named helper lemma** taking the induction hypothesis (for the `and`/`or`/`imp`
cases, which recurse on strict subformulas) as an explicit hypothesis parameter, rather than
being folded into a single recursive definition. This lets Phase 3a build sorry-free
independently of the `.box`/`.diamond` cases (Phase 3b/3c), which are assembled together with
these helpers into the full `canonical_truth_lemma` in Phase 3c.

None of the four modal axiom hypotheses (`h_K`, `h_Kdia`, `h_Idb`, `h_Cd`) are threaded here:
the non-modal cases require no modal axiom (report 03 §4 row 8). `h_efq` is threaded only by
the `imp` case (via `modal_imp_witness`/`modal_prime_exclusion`), kept separate from the base
intuitionistic hypotheses so the minimal (task 495) instantiation can omit it.

`botForces` is kept a **parameter** throughout (never hard-coded to `fun _ => False`), per the
plan's Goals/Postmortem: this lets the minimal (495) and CK (493) fallible-world
instantiations reuse `truth_bot_case` without editing this framework. `truth_bot_case` takes an
explicit bridging hypothesis `h_bot` identifying `botForces w` with `⊥ ∈ w.val`; the
intuitionistic instantiation (`botForces := fun _ => False`) discharges it using
`canonical_bot_not_mem` below.

## Main Definitions

- `canonical_bot_not_mem`: `⊥` is never a member of a canonical prime world's theory
  (consistency argument, modal analogue of `Cslib.Logic.PL.int_dccs_bot_not_mem`).
- `canonical_imp_property`: modus-ponens closure for canonical prime worlds (modal analogue of
  `Cslib.Logic.PL.int_dccs_imp_property`).
- `truth_atom_case`, `truth_bot_case`, `truth_and_case`, `truth_or_case`, `truth_imp_case`: the
  five non-modal truth-lemma case helpers (Phase 3a).
- `truth_box_case`: the `.box` truth-lemma case helper (Phase 3b).

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43
  (propositional template, transliterated).
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational truth lemma, non-modal clauses coincide with the intuitionistic
  propositional ones).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Consistency and Deductive-Closure Helpers -/

section TruthLemmaHelpers

variable {Axioms : Proposition Atom → Prop}

/-- `⊥` is never a member of a canonical prime world's underlying theory: if it were, `[⊥]`
would be a length-one sublist witnessing an assumption-only derivation of `⊥`, contradicting
`ModalSetConsistent`. Modal analogue of `Cslib.Logic.PL.int_dccs_bot_not_mem`
(`IntLindenbaum.lean:46`). -/
theorem canonical_bot_not_mem (w : CanonicalPrimeWorld Axioms) :
    (Proposition.bot : Proposition Atom) ∉ w.val := by
  intro h_bot
  have hmem : ∀ x ∈ [(Proposition.bot : Proposition Atom)], x ∈ w.val := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h_bot
    · nomatch hx'
  exact w.property.1.1 [Proposition.bot] hmem
    ((modalDerivationSystem Axioms).assumption (List.mem_cons.mpr (Or.inl rfl)))

/-- Modus ponens closure for canonical prime worlds: if `(φ → ψ) ∈ w.val` and `φ ∈ w.val`, then
`ψ ∈ w.val`. Modal analogue of `Cslib.Logic.PL.int_dccs_imp_property`
(`IntLindenbaum.lean:54`), via `w`'s deductive closure. -/
theorem canonical_imp_property {w : CanonicalPrimeWorld Axioms} {φ ψ : Proposition Atom}
    (h_imp : (φ.imp ψ) ∈ w.val) (h_phi : φ ∈ w.val) : ψ ∈ w.val := by
  apply w.property.1.2 [φ.imp ψ, φ] ψ
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h_imp
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · exact h_phi
      · nomatch hx''
  · exact (modalDerivationSystem Axioms).mp
      ((modalDerivationSystem Axioms).assumption (List.mem_cons.mpr (Or.inl rfl)))
      ((modalDerivationSystem Axioms).assumption
        (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

end TruthLemmaHelpers

/-! ## Non-Modal Truth-Lemma Cases (Phase 3a) -/

section TruthLemmaCases

variable {Axioms : Proposition Atom → Prop}

/-- **Atom case** of the (to-be-assembled) `canonical_truth_lemma`: forcing of an atom at a
canonical world coincides with membership, by definition of `canonicalVal`. `botForces` is kept
a loose parameter (unused in this case, since `BForces`'s `.atom` clause never inspects it).
Transliterated from `Cslib.Logic.PL.int_truth_lemma`'s `.atom` case
(`IntStrongCompleteness.lean:112`). -/
theorem truth_atom_case (botForces : CanonicalPrimeWorld Axioms → Prop)
    (w : CanonicalPrimeWorld Axioms) (p : Atom) :
    BForces canonicalR canonicalVal botForces w (Proposition.atom p) ↔
      (Proposition.atom p) ∈ w.val :=
  Iff.rfl

/-- **Bot case** of the (to-be-assembled) `canonical_truth_lemma`, parametric in `botForces`
(task 480 Goals/Postmortem: `botForces` must remain a hypothesis-supplied parameter, not a
hard-coded `fun _ => False`, so the minimal (495) / CK (493) fallible-world instantiations can
reuse this helper without editing the framework). The bridging hypothesis `h_bot` identifies
`botForces w` with `⊥ ∈ w.val`; for the intuitionistic instantiation (`botForces := fun _ =>
False`) it is discharged using `canonical_bot_not_mem` above (Phase 4 packages this). Structural
analogue of `Cslib.Logic.PL.int_truth_lemma`'s `.bot` case
(`IntStrongCompleteness.lean:113-116`), generalized from the hard-coded `IForces`
`.bot`-forces-`False` convention to a parametric `botForces`. -/
theorem truth_bot_case
    (botForces : CanonicalPrimeWorld Axioms → Prop)
    (h_bot : ∀ w : CanonicalPrimeWorld Axioms,
      botForces w ↔ (Proposition.bot : Proposition Atom) ∈ w.val)
    (w : CanonicalPrimeWorld Axioms) :
    BForces canonicalR canonicalVal botForces w Proposition.bot ↔
      (Proposition.bot : Proposition Atom) ∈ w.val :=
  h_bot w

/-- **Conjunction case** of the (to-be-assembled) `canonical_truth_lemma`, taking the two
sub-formula truth-lemma instances (`ihφ`, `ihψ`) as explicit induction-hypothesis parameters
(task 480 Phase 3a design note: this lets the case build sorry-free before
`canonical_truth_lemma` itself is assembled in Phase 3c). Transliterated from
`Cslib.Logic.PL.int_truth_lemma`'s `.and` case (`IntStrongCompleteness.lean:117-159`,
`PL.Proposition` → `Proposition`, `IntPropAxiom` → `Axioms`; explicit `DerivationTree`
term-mode, no `simp`/`aesop`). -/
theorem truth_and_case
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    {botForces : CanonicalPrimeWorld Axioms → Prop}
    {w : CanonicalPrimeWorld Axioms} {φ ψ : Proposition Atom}
    (ihφ : BForces canonicalR canonicalVal botForces w φ ↔ φ ∈ w.val)
    (ihψ : BForces canonicalR canonicalVal botForces w ψ ↔ ψ ∈ w.val) :
    BForces canonicalR canonicalVal botForces w (φ.and ψ) ↔ (φ.and ψ) ∈ w.val := by
  constructor
  · intro ⟨hφ, hψ⟩
    have h_phi_w := ihφ.mp hφ
    have h_psi_w := ihψ.mp hψ
    apply w.property.1.2 [φ, ψ] (φ.and ψ)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h_phi_w
      · rcases List.mem_cons.mp hx' with rfl | hx''
        · exact h_psi_w
        · nomatch hx''
    · exact ⟨.modus_ponens _ _ _
        (.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (h_andI φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))))
        (.assumption _ _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩
  · intro h_mem
    have hφ_mem : φ ∈ w.val := by
      apply w.property.1.2 [φ.and ψ] φ
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_mem
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (h_andE1 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
    have hψ_mem : ψ ∈ w.val := by
      apply w.property.1.2 [φ.and ψ] ψ
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_mem
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (h_andE2 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
    exact ⟨ihφ.mpr hφ_mem, ihψ.mpr hψ_mem⟩

/-- **Disjunction case** of the (to-be-assembled) `canonical_truth_lemma`, taking the two
sub-formula truth-lemma instances (`ihφ`, `ihψ`) as explicit induction-hypothesis parameters
(same Phase 3a design note as `truth_and_case`). The backward direction uses the canonical
prime world's disjunction property (`w.property.2`), the payoff of choosing prime theories
(rather than maximal consistent sets) as canonical worlds. Transliterated from
`Cslib.Logic.PL.int_truth_lemma`'s `.or` case (`IntStrongCompleteness.lean:160-191`,
`PL.Proposition` → `Proposition`, `IntPropAxiom` → `Axioms`; explicit `DerivationTree`
term-mode, no `simp`/`aesop`). -/
theorem truth_or_case
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    {botForces : CanonicalPrimeWorld Axioms → Prop}
    {w : CanonicalPrimeWorld Axioms} {φ ψ : Proposition Atom}
    (ihφ : BForces canonicalR canonicalVal botForces w φ ↔ φ ∈ w.val)
    (ihψ : BForces canonicalR canonicalVal botForces w ψ ↔ ψ ∈ w.val) :
    BForces canonicalR canonicalVal botForces w (φ.or ψ) ↔ (φ.or ψ) ∈ w.val := by
  constructor
  · intro h_or
    rcases h_or with hφ | hψ
    · have h_phi_w := ihφ.mp hφ
      apply w.property.1.2 [φ] (φ.or ψ)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_phi_w
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (h_orI1 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
    · have h_psi_w := ihψ.mp hψ
      apply w.property.1.2 [ψ] (φ.or ψ)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_psi_w
        · nomatch hx'
      · exact ⟨.modus_ponens _ _ _
          (.weakening [] _ _ (.ax [] _ (h_orI2 φ ψ)) (fun _ h => nomatch h))
          (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))⟩
  · intro h_mem
    rcases w.property.2 φ ψ h_mem with h | h
    · exact Or.inl (ihφ.mpr h)
    · exact Or.inr (ihψ.mpr h)

/-- **Implication case** of the (to-be-assembled) `canonical_truth_lemma`, taking the two
sub-formula truth-lemma instances (`ihφ`, `ihψ`) as explicit induction-hypothesis parameters,
**universally quantified over all canonical worlds** (unlike `truth_and_case`/`truth_or_case`,
this case's forward direction constructs a fresh successor world `T ≥ w` and needs the
induction hypothesis there, matching exactly what the assembled recursive
`canonical_truth_lemma` will supply at any world in Phase 3c). Uses `modal_imp_witness`
(`PrimeTheory.lean`) to build a theory forcing `φ` but not `ψ`, then `modal_prime_exclusion`
to make it prime while still excluding `ψ`. No modal axiom (`h_K`/`h_Kdia`/`h_Idb`/`h_Cd`) is
threaded -- only the base intuitionistic hypotheses plus `h_efq` (kept separate, task 495).
Transliterated from `Cslib.Logic.PL.int_truth_lemma`'s `.imp` case
(`IntStrongCompleteness.lean:192-214`, `PL.Proposition` → `Proposition`,
`IntPropAxiom` → `Axioms`, `int_imp_witness`/`int_prime_exclusion` →
`modal_imp_witness`/`modal_prime_exclusion`). -/
theorem truth_imp_case
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    {botForces : CanonicalPrimeWorld Axioms → Prop}
    {w : CanonicalPrimeWorld Axioms} {φ ψ : Proposition Atom}
    (ihφ : ∀ T : CanonicalPrimeWorld Axioms,
      BForces canonicalR canonicalVal botForces T φ ↔ φ ∈ T.val)
    (ihψ : ∀ T : CanonicalPrimeWorld Axioms,
      BForces canonicalR canonicalVal botForces T ψ ↔ ψ ∈ T.val) :
    BForces canonicalR canonicalVal botForces w (φ.imp ψ) ↔ (φ.imp ψ) ∈ w.val := by
  constructor
  · -- Forward: BForces w (φ → ψ) → (φ → ψ) ∈ w.val
    intro h_forces
    by_contra h_not_mem
    -- Get an admissible T' with w.val ⊆ T', φ ∈ T', ψ ∉ T' (using modal_imp_witness)
    obtain ⟨T'_set, hwT', hT'_adm, hφT', hψT'⟩ :=
      modal_imp_witness h_implyK h_implyS h_efq w.property.1 h_not_mem
    -- Extend T' to a prime theory T that still excludes ψ
    obtain ⟨T_set, hT'T, hT_prime, hψT⟩ :=
      modal_prime_exclusion h_implyK h_implyS h_efq h_orE hT'_adm hψT'
    let T : CanonicalPrimeWorld Axioms := ⟨T_set, hT_prime⟩
    have hle : w ≤ T := Set.Subset.trans hwT' hT'T
    have hφT : φ ∈ T.val := hT'T hφT'
    have hf_φ := (ihφ T).mpr hφT
    have hf_ψ := h_forces T hle hf_φ
    exact hψT ((ihψ T).mp hf_ψ)
  · -- Backward: (φ → ψ) ∈ w.val → BForces w (φ → ψ)
    intro h_mem T hle hf_φ
    have h_imp_T : (φ.imp ψ) ∈ T.val := hle h_mem
    have h_φ_T : φ ∈ T.val := (ihφ T).mp hf_φ
    have h_ψ_T : ψ ∈ T.val := canonical_imp_property h_imp_T h_φ_T
    exact (ihψ T).mpr h_ψ_T

end TruthLemmaCases

/-! ## Box Truth-Lemma Case (Phase 3b) -/

section TruthLemmaBoxCase

variable {Axioms : Proposition Atom → Prop}

/-- **Box case** of the (to-be-assembled) `canonical_truth_lemma`: forcing of `□φ` at a
canonical world coincides with `□φ ∈ w.val`, given the induction hypothesis for `φ`
**universally quantified over all canonical worlds** (task 480 Phase 3a design note, reused
here exactly as in `truth_imp_case`: this lets the case build sorry-free before
`canonical_truth_lemma` itself is assembled in Phase 3c).

Unfolds via `BForces_box` (`∀ w' ≥ w, ∀ u, r w' u → BForces … u φ`, [Simpson1994] clause 3.2).

**Forward direction** (contrapositive): if `□φ ∉ w.val`, `canonical_box_witness` (Phase 2b)
produces `w' ≥ w` and a prime `u` with `canonicalR w' u` and `φ ∉ u.val`; instantiating the
forcing hypothesis at this `w'`/`u` and applying `ih u` yields `φ ∈ u.val`, contradicting
`φ ∉ u.val`.

**Backward direction** (heredity over `≤ ∘ R`): given `□φ ∈ w.val`, any `w' ≥ w` inherits
`□φ ∈ w'.val` by set inclusion; `canonicalR w' u`'s box clause then gives `φ ∈ u.val` for any
`u` with `canonicalR w' u`, and `ih u` transports this to forcing.

Threads `h_K`, `h_Kdia`, `h_Idb` (report 03 §4 row 6) -- together with the base intuitionistic
hypotheses `h_implyK`/`h_implyS`/`h_efq`/`h_orI1`/`h_orI2`/`h_orE`/`h_andI`/`h_andE1`/`h_andE2`
that `canonical_box_witness` itself requires -- **solely via the call to
`canonical_box_witness`**; no new axiom is introduced in this phase.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3, clause 3.2.
* ianshil/CK `general_th_completeness.v`, box case (~L211-249). -/
theorem truth_box_case
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
    {botForces : CanonicalPrimeWorld Axioms → Prop}
    {w : CanonicalPrimeWorld Axioms} {φ : Proposition Atom}
    (ih : ∀ T : CanonicalPrimeWorld Axioms,
      BForces canonicalR canonicalVal botForces T φ ↔ φ ∈ T.val) :
    BForces canonicalR canonicalVal botForces w (Proposition.box φ) ↔
      (Proposition.box φ) ∈ w.val := by
  simp only [BForces_box]
  constructor
  · -- Forward: (∀ w' ≥ w, ∀ u, canonicalR w' u → BForces … u φ) → □φ ∈ w.val
    intro h_forces
    by_contra h_notbox
    obtain ⟨w', u, hww', hRw'u, hphi_notU⟩ :=
      canonical_box_witness h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE h_andI h_andE1 h_andE2
        h_K h_Kdia h_Idb (w := w) (φ := φ) h_notbox
    exact hphi_notU ((ih u).mp (h_forces w' hww' u hRw'u))
  · -- Backward: □φ ∈ w.val → ∀ w' ≥ w, ∀ u, canonicalR w' u → BForces … u φ
    intro h_mem w' hww' u hRw'u
    have hbox_w' : (Proposition.box φ) ∈ w'.val := hww' h_mem
    have hphi_u : φ ∈ u.val := hRw'u.1 φ hbox_w'
    exact (ih u).mpr hphi_u

end TruthLemmaBoxCase

end Cslib.Logic.Modal
