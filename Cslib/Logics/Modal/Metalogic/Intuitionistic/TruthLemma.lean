/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel
public import Cslib.Logics.Modal.Semantics.Birelational

/-! # Truth Lemma for Intuitionistic Modal Logic

This module builds the birelational canonical-model truth lemma. It first proves the **five
non-modal cases** (`atom`, `bot`, `and`, `or`, `imp`) as standalone named helper lemmas,
transliterated line-for-line from `Cslib.Logic.PL.int_truth_lemma`
(`Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean:108-214`,
`PL.Proposition Atom` → `Proposition Atom`, `IntPropAxiom` → `Axioms`). It then adds
`truth_box_case`, the `.box` constructor case, consuming the pair-shaped
`canonical_box_witness` and heredity over `≤ ∘ R`, and `truth_diamond_case`, the `.diamond`
constructor case, consuming the single-witness `canonical_diamond_witness`, and finally
assembles all seven cases into the full recursive `canonical_truth_lemma` by structural
induction on `Proposition`.

Each case is a **named helper lemma** taking the induction hypothesis (for the `and`/`or`/`imp`/
`box`/`diamond` cases, which recurse on strict subformulas) as an explicit hypothesis parameter,
rather than being folded directly into a single recursive definition. This lets each case build
sorry-free independently before assembly. `canonical_truth_lemma` is the payoff: it dispatches
each constructor to its helper, threading the induction hypothesis obtained from
`induction φ generalizing w`.

None of the four modal axiom hypotheses (`h_K`, `h_Kdia`, `h_Idb`, `h_Cd`) are threaded here:
the non-modal cases require no modal axiom. `h_efq` is threaded only by the `imp` case (via
`modal_imp_witness`/`modal_prime_exclusion`), kept separate from the base intuitionistic
hypotheses so a minimal instantiation can omit it.

`botForces` is kept a **parameter** throughout (never hard-coded to `fun _ => False`): this lets
the minimal and `CK` fallible-world instantiations reuse `truth_bot_case` without editing this
framework. `truth_bot_case` takes an explicit bridging hypothesis `h_bot` identifying
`botForces w` with `⊥ ∈ w.val`; the intuitionistic instantiation (`botForces := fun _ => False`)
discharges it using `canonical_bot_not_mem` below.

## Main Definitions

- `canonical_bot_not_mem`: `⊥` is never a member of a canonical prime world's theory
  (consistency argument, modal analogue of `Cslib.Logic.PL.int_dccs_bot_not_mem`).
- `canonical_imp_property`: modus-ponens closure for canonical prime worlds (modal analogue of
  `Cslib.Logic.PL.int_dccs_imp_property`).
- `truth_atom_case`, `truth_bot_case`, `truth_and_case`, `truth_or_case`, `truth_imp_case`: the
  five non-modal truth-lemma case helpers.
- `truth_box_case`: the `.box` truth-lemma case helper.
- `truth_diamond_case`: the `.diamond` truth-lemma case helper.
- `canonical_truth_lemma`: the assembled truth lemma over all seven `Proposition` constructors,
  the payoff `Completeness.lean` consumes.

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

/-! ## Non-Modal Truth-Lemma Cases -/

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
(`botForces` must remain a hypothesis-supplied parameter, not a hard-coded `fun _ => False`, so
the minimal / `CK` fallible-world instantiations can reuse this helper without editing the
framework). The bridging hypothesis `h_bot` identifies `botForces w` with `⊥ ∈ w.val`; for the
intuitionistic instantiation (`botForces := fun _ => False`) it is discharged using
`canonical_bot_not_mem` above (`Completeness.lean` packages this). Structural
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
(this lets the case build sorry-free before `canonical_truth_lemma` itself is assembled).
Transliterated from
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
(same design note as `truth_and_case`). The backward direction uses the canonical
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
`canonical_truth_lemma` will supply at any world). Uses `modal_imp_witness`
(`PrimeTheory.lean`) to build a theory forcing `φ` but not `ψ`, then `modal_prime_exclusion`
to make it prime while still excluding `ψ`. No modal axiom (`h_K`/`h_Kdia`/`h_Idb`/`h_Cd`) is
threaded -- only the base intuitionistic hypotheses plus `h_efq` (kept separate). Transliterated
from `Cslib.Logic.PL.int_truth_lemma`'s `.imp` case
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

/-! ## Box Truth-Lemma Case -/

section TruthLemmaBoxCase

variable {Axioms : Proposition Atom → Prop}

/-- **Box case** of the (to-be-assembled) `canonical_truth_lemma`: forcing of `□φ` at a
canonical world coincides with `□φ ∈ w.val`, given the induction hypothesis for `φ`
**universally quantified over all canonical worlds** (the same design note as `truth_imp_case`:
this lets the case build sorry-free before `canonical_truth_lemma` itself is assembled).

Unfolds via `BForces_box` (`∀ w' ≥ w, ∀ u, r w' u → BForces … u φ`, [Simpson1994] clause 3.2).

**Forward direction** (contrapositive): if `□φ ∉ w.val`, `canonical_box_witness` produces
`w' ≥ w` and a prime `u` with `canonicalR w' u` and `φ ∉ u.val`; instantiating the forcing
hypothesis at this `w'`/`u` and applying `ih u` yields `φ ∈ u.val`, contradicting `φ ∉ u.val`.

**Backward direction** (heredity over `≤ ∘ R`): given `□φ ∈ w.val`, any `w' ≥ w` inherits
`□φ ∈ w'.val` by set inclusion; `canonicalR w' u`'s box clause then gives `φ ∈ u.val` for any
`u` with `canonicalR w' u`, and `ih u` transports this to forcing.

Threads `h_K`, `h_Kdia`, `h_Idb` -- together with the base intuitionistic hypotheses
`h_implyK`/`h_implyS`/`h_efq`/`h_orI1`/`h_orI2`/`h_orE`/`h_andI`/`h_andE1`/`h_andE2` that
`canonical_box_witness` itself requires -- **solely via the call to
`canonical_box_witness`**; no new axiom is introduced here.

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

/-! ## Diamond Truth-Lemma Case -/

section TruthLemmaDiamondCase

variable {Axioms : Proposition Atom → Prop}

/-- **Diamond case** of the (to-be-assembled) `canonical_truth_lemma`: forcing of `◇φ` at a
canonical world coincides with `◇φ ∈ w.val`, given the induction hypothesis for `φ`
**universally quantified over all canonical worlds** (the same design note reused for
`truth_imp_case`/`truth_box_case`).

Unfolds via `BForces_diamond` (`∃ u, r w u ∧ BForces … u φ`, [Simpson1994] clause 3.5). Unlike
`truth_box_case`, `canonicalR w v` is a **single witness**, not a pair `⟨w', u⟩` --
`BForces_diamond` is a bare existential over successors of `w` itself, so no outer `∀ w' ≥ w`
quantifier appears.

**Forward direction**: given `u` with `canonicalR w u` and `φ` forced at `u`, `ih u` transports
forcing to `φ ∈ u.val`; `canonicalR w u`'s diamond clause (`.2`, `∀ ψ, ψ ∈ u.val → (◇ψ) ∈ w.val`)
then gives `◇φ ∈ w.val` directly -- **no modal axiom is needed for this direction**.

**Backward direction**: given `◇φ ∈ w.val`, `canonical_diamond_witness` produces a single prime
`v` with `canonicalR w v` and `φ ∈ v.val`; `ih v` transports this to forcing, witnessing the
existential.

Threads `h_Kdia`, `h_Cd` (and `h_dbot`, `h_K` via `diamond_witness_underivable`) **solely via
the call to `canonical_diamond_witness`**; no new axiom is introduced here. `h_Idb` is **not**
threaded (confirmed not consumed by the diamond side).

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3, clause 3.5.
* ianshil/CK `general_th_completeness.v`, diamond case. -/
theorem truth_diamond_case
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_Kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (h_Cd : ∀ (φ ψ : Proposition Atom), Axioms ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))))
    (h_dbot : Axioms ((◇Proposition.bot).imp Proposition.bot))
    {botForces : CanonicalPrimeWorld Axioms → Prop}
    {w : CanonicalPrimeWorld Axioms} {φ : Proposition Atom}
    (ih : ∀ T : CanonicalPrimeWorld Axioms,
      BForces canonicalR canonicalVal botForces T φ ↔ φ ∈ T.val) :
    BForces canonicalR canonicalVal botForces w (Proposition.diamond φ) ↔
      (Proposition.diamond φ) ∈ w.val := by
  simp only [BForces_diamond]
  constructor
  · -- Forward: (∃ u, canonicalR w u ∧ BForces … u φ) → ◇φ ∈ w.val
    rintro ⟨u, hRwu, hforces_u⟩
    exact hRwu.2 φ ((ih u).mp hforces_u)
  · -- Backward: ◇φ ∈ w.val → ∃ u, canonicalR w u ∧ BForces … u φ
    intro h_mem
    obtain ⟨v, hRwv, hphi_v⟩ :=
      canonical_diamond_witness h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
        h_K h_Kdia h_Cd h_dbot (w := w) (φ := φ) h_mem
    exact ⟨v, hRwv, (ih v).mpr hphi_v⟩

end TruthLemmaDiamondCase

/-! ## Assembled Truth Lemma -/

section TruthLemmaAssembly

variable {Axioms : Proposition Atom → Prop}

/-- **The canonical truth lemma**: forcing of any proposition `φ` at any canonical prime world
`w` coincides with membership `φ ∈ w.val`. Assembled by structural induction on `φ`, dispatching
each of the seven `Proposition` constructors to its helper (above), threading the induction
hypothesis (generalized over all worlds, matching the `imp`/`box`/`diamond` cases'
universally-quantified IH requirement) at the point of use.

Carries the **union of the four modal axioms** `{ h_K, h_Kdia, h_Idb, h_Cd }` (plus `h_dbot`,
needed transitively by the diamond witness) as parametric hypotheses: `h_K`/`h_Kdia`/`h_Idb` are
used only by the `box` case (via `truth_box_case`), `h_Kdia`/`h_Cd`/`h_dbot` only by the
`diamond` case (via `truth_diamond_case`); the non-modal cases (`atom`, `bot`, `and`, `or`,
`imp`) use none of the four. `botForces` remains a loose parameter throughout (bridged by the
explicit `h_bot` hypothesis), so the minimal and `CK` fallible-world instantiations can reuse
this lemma unmodified.

This is the payoff lemma `Completeness.lean` consumes to build `ivalid_completeness`/
`mvalid_completeness`.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43.
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational truth lemma, assembled statement). -/
theorem canonical_truth_lemma
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
    (h_bot : ∀ w : CanonicalPrimeWorld Axioms,
      botForces w ↔ (Proposition.bot : Proposition Atom) ∈ w.val)
    (φ : Proposition Atom) (w : CanonicalPrimeWorld Axioms) :
    BForces canonicalR canonicalVal botForces w φ ↔ φ ∈ w.val := by
  induction φ generalizing w with
  | atom p => exact truth_atom_case botForces w p
  | bot => exact truth_bot_case botForces h_bot w
  | and φ ψ ihφ ihψ => exact truth_and_case h_andI h_andE1 h_andE2 (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ => exact truth_or_case h_orI1 h_orI2 (ihφ w) (ihψ w)
  | imp φ ψ ihφ ihψ => exact truth_imp_case h_implyK h_implyS h_efq h_orE ihφ ihψ
  | box φ ihφ =>
      exact truth_box_case h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE h_andI h_andE1 h_andE2
        h_K h_Kdia h_Idb ihφ
  | diamond φ ihφ =>
      exact truth_diamond_case h_implyK h_implyS h_efq h_orI1 h_orI2 h_orE
        h_K h_Kdia h_Cd h_dbot ihφ

end TruthLemmaAssembly

end Cslib.Logic.Modal
