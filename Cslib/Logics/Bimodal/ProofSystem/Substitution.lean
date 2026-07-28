/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.ProofSystem.Derivation
public import Mathlib.Data.Finset.Image

/-! # Atom Substitution in Derivations

This module defines atom substitution for formulas and proves that derivations
are preserved under atom substitution.

## Main Definitions

- `Formula.subst`: Substitute atom q with atom r in a formula
- `Context.subst`: Apply substitution to all formulas in a context
- `atomsOfContext`: All atoms appearing in a context

## Main Results

- `subst_fresh_eq`: Substituting a fresh atom leaves the formula unchanged
- `axiomSubst`: Axiom instances are preserved under substitution (42 cases)
- `derivationSubst`: Derivations are preserved under atom substitution
-/

@[expose] public section

namespace Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal

variable {Atom : Type u} [DecidableEq Atom]

/-! ## Formula Substitution -/

namespace Formula

/-- Substitute atom `q` with atom `r` in a formula. -/
def subst (q r : Atom) : Formula Atom -> Formula Atom
  | .atom s => if s = q then .atom r else .atom s
  | .bot => .bot
  | .imp phi psi => .imp (phi.subst q r) (psi.subst q r)
  | .box phi => .box (phi.subst q r)
  | .untl psi phi => .untl (psi.subst q r) (phi.subst q r)
  | .snce psi phi => .snce (psi.subst q r) (phi.subst q r)

/-! ### Structural simp lemmas -/

@[simp]
theorem subst_atom_eq (q r : Atom) :
    (Formula.atom q).subst q r = .atom r := by
  simp [subst]

@[simp]
theorem subst_atom_ne (q r s : Atom) (h : s ≠ q) :
    (Formula.atom s).subst q r = .atom s := by
  simp [subst, h]

@[simp]
theorem subst_bot (q r : Atom) :
    (Formula.bot : Formula Atom).subst q r = .bot := rfl

@[simp]
theorem subst_imp (q r : Atom) (phi psi : Formula Atom) :
    (Formula.imp phi psi).subst q r =
      .imp (phi.subst q r) (psi.subst q r) := rfl

@[simp]
theorem subst_box (q r : Atom) (phi : Formula Atom) :
    (Formula.box phi).subst q r = .box (phi.subst q r) := rfl

@[simp]
theorem subst_untl (q r : Atom) (phi psi : Formula Atom) :
    (Formula.untl psi phi).subst q r =
      .untl (psi.subst q r) (phi.subst q r) := rfl

@[simp]
theorem subst_snce (q r : Atom) (phi psi : Formula Atom) :
    (Formula.snce psi phi).subst q r =
      .snce (psi.subst q r) (phi.subst q r) := rfl

/-! ### Derived operator substitution lemmas -/

-- Concrete-form helpers: `PropositionalConnectives.neg/top` reduce to constructors
-- for `Formula Atom` (the instance sets `bot := .bot`, `imp := .imp`).
omit [DecidableEq Atom] in
private theorem neg_constructor (phi : Formula Atom) :
    PropositionalConnectives.neg phi = phi.imp .bot := rfl

omit [DecidableEq Atom] in
private theorem top_constructor :
    (PropositionalConnectives.top : Formula Atom) = .imp .bot .bot := rfl

theorem subst_neg (q r : Atom) (phi : Formula Atom) :
    (Formula.neg phi).subst q r = Formula.neg (phi.subst q r) := by
  simp only [Formula.neg, neg_constructor, subst_imp, subst_bot]

theorem subst_and (q r : Atom) (phi psi : Formula Atom) :
    (Formula.and phi psi).subst q r =
      Formula.and (phi.subst q r) (psi.subst q r) := by
  simp only [Formula.and, subst_imp, subst_bot]

theorem subst_or (q r : Atom) (phi psi : Formula Atom) :
    (Formula.or phi psi).subst q r =
      Formula.or (phi.subst q r) (psi.subst q r) := by
  simp only [Formula.or, subst_imp, subst_bot]

theorem subst_diamond (q r : Atom) (phi : Formula Atom) :
    (Formula.diamond phi).subst q r =
      Formula.diamond (phi.subst q r) := by
  simp only [Formula.diamond, subst_neg, subst_box]

theorem subst_someFuture (q r : Atom) (phi : Formula Atom) :
    (Formula.someFuture phi).subst q r =
      Formula.someFuture (phi.subst q r) := by
  simp only [Formula.someFuture, Formula.top, top_constructor, subst_untl, subst_imp, subst_bot]

theorem subst_somePast (q r : Atom) (phi : Formula Atom) :
    (Formula.somePast phi).subst q r =
      Formula.somePast (phi.subst q r) := by
  simp only [Formula.somePast, Formula.top, top_constructor, subst_snce, subst_imp, subst_bot]

theorem subst_allFuture (q r : Atom) (phi : Formula Atom) :
    (Formula.allFuture phi).subst q r =
      Formula.allFuture (phi.subst q r) := by
  simp only [Formula.allFuture, Formula.neg, neg_constructor,
    Formula.someFuture, Formula.top, top_constructor,
    subst_imp, subst_bot, subst_untl]

theorem subst_allPast (q r : Atom) (phi : Formula Atom) :
    (Formula.allPast phi).subst q r =
      Formula.allPast (phi.subst q r) := by
  simp only [Formula.allPast, Formula.neg, neg_constructor,
    Formula.somePast, Formula.top, top_constructor,
    subst_imp, subst_bot, subst_snce]

/-! ### Freshness and substitution -/

/-- If q is not in the atoms of phi, substituting q with r
    leaves phi unchanged. -/
theorem subst_fresh_eq (q r : Atom) (phi : Formula Atom)
    (h : q ∉ phi.atoms) : phi.subst q r = phi := by
  induction phi with
  | atom s =>
    simp only [atoms, Finset.mem_singleton] at h
    simp only [subst]
    simp only [if_neg (Ne.symm h)]
  | bot => rfl
  | imp phi psi ih1 ih2 =>
    simp only [atoms, Finset.mem_union, not_or] at h
    simp [subst, ih1 h.1, ih2 h.2]
  | box phi ih =>
    simp only [atoms] at h
    simp [subst, ih h]
  | untl psi phi ih2 ih1 =>
    simp only [atoms, Finset.mem_union, not_or] at h
    simp [subst, ih1 h.1, ih2 h.2]
  | snce psi phi ih2 ih1 =>
    simp only [atoms, Finset.mem_union, not_or] at h
    simp [subst, ih1 h.1, ih2 h.2]

/-- Atoms of substituted formula. -/
theorem subst_atoms (q r : Atom) (phi : Formula Atom) :
    (phi.subst q r).atoms =
      phi.atoms.image (fun a => if a = q then r else a) := by
  induction phi with
  | atom s =>
    simp only [subst, atoms]
    by_cases hs : s = q
    · simp only [hs, ↓reduceIte, atoms,
        Finset.image_singleton, ↓reduceIte]
    · simp only [if_neg hs, atoms, Finset.image_singleton]
  | bot => simp [subst, atoms, Finset.image_empty]
  | imp phi psi ih1 ih2 =>
    simp only [subst, atoms, Finset.image_union, ih1, ih2]
  | box phi ih =>
    simp only [subst, atoms, ih]
  | untl psi phi ih2 ih1 =>
    simp only [subst, atoms, Finset.image_union, ih1, ih2]
  | snce psi phi ih2 ih1 =>
    simp only [subst, atoms, Finset.image_union, ih1, ih2]

end Formula

/-! ## Context substitution -/

/-- Apply atom substitution to all formulas in a context. -/
def Context.subst (q r : Atom) (Gamma : Context Atom) :
    Context Atom :=
  Gamma.map (Formula.subst q r)

/-- All atoms appearing in formulas of a context. -/
def atomsOfContext (Gamma : Context Atom) : Finset Atom :=
  Gamma.foldr (fun phi acc => phi.atoms ∪ acc) ∅

@[simp]
theorem atoms_of_context_nil :
    atomsOfContext ([] : Context Atom) = ∅ := rfl

@[simp]
theorem atoms_of_context_cons (phi : Formula Atom)
    (Gamma : Context Atom) :
    atomsOfContext (phi :: Gamma) =
      phi.atoms ∪ atomsOfContext Gamma := rfl

theorem mem_atoms_of_context_iff {q : Atom}
    {Gamma : Context Atom} :
    q ∈ atomsOfContext Gamma ↔
      ∃ phi ∈ Gamma, q ∈ phi.atoms := by
  induction Gamma with
  | nil => simp [atomsOfContext]
  | cons hd tl ih =>
    simp only [atoms_of_context_cons, Finset.mem_union,
      ih, List.mem_cons]
    constructor
    · intro h
      cases h with
      | inl h => exact ⟨hd, Or.inl rfl, h⟩
      | inr h =>
        obtain ⟨phi, hphi, hq⟩ := h
        exact ⟨phi, Or.inr hphi, hq⟩
    · intro ⟨phi, hphi, hq⟩
      cases hphi with
      | inl h => left; subst h; exact hq
      | inr h => right; exact ⟨phi, h, hq⟩

/-- Membership in substituted context. -/
theorem mem_context_subst_iff {q r : Atom}
    {phi : Formula Atom} {Gamma : Context Atom} :
    phi ∈ Context.subst q r Gamma ↔
      ∃ psi ∈ Gamma, phi = psi.subst q r := by
  unfold Context.subst
  constructor
  · intro h
    have h' := List.mem_map.mp h
    obtain ⟨psi, hpsi, heq⟩ := h'
    exact ⟨psi, hpsi, heq.symm⟩
  · intro ⟨psi, hpsi, heq⟩
    apply List.mem_map.mpr
    exact ⟨psi, hpsi, heq.symm⟩

/-! ## Axiom substitution -/

/-- Axiom instances are preserved under atom substitution.

All derived subst operations (`subst_neg`, `subst_diamond`, etc.) reduce definitionally to
`rfl` because `Formula.neg`, `Formula.top`, etc. are `abbrev`s over the `PropositionalConnectives`
defaults, which in turn expand to the base constructors `imp`/`bot`. The `exact` calls therefore
typecheck without any `simp only` rewrite prelude. -/
def axiomSubst (q r : Atom) {phi : Formula Atom}
    (h : Axiom phi) : Axiom (phi.subst q r) := by
  cases h with
  | imp_k a b c => exact Axiom.imp_k (a.subst q r) (b.subst q r) (c.subst q r)
  | imp_s a b => exact Axiom.imp_s (a.subst q r) (b.subst q r)
  | efq a => exact Axiom.efq (a.subst q r)
  | peirce a b => exact Axiom.peirce (a.subst q r) (b.subst q r)
  | modal_t a => exact Axiom.modal_t (a.subst q r)
  | modal_4 a => exact Axiom.modal_4 (a.subst q r)
  | modal_b a => exact Axiom.modal_b (a.subst q r)
  | modal_5_collapse a => exact Axiom.modal_5_collapse (a.subst q r)
  | modal_k_dist a b => exact Axiom.modal_k_dist (a.subst q r) (b.subst q r)
  | serial_future => exact Axiom.serial_future
  | serial_past => exact Axiom.serial_past
  | left_mono_until_G a b c =>
    exact Axiom.left_mono_until_G (a.subst q r) (b.subst q r) (c.subst q r)
  | left_mono_since_H a b c =>
    exact Axiom.left_mono_since_H (a.subst q r) (b.subst q r) (c.subst q r)
  | right_mono_until a b c =>
    exact Axiom.right_mono_until (a.subst q r) (b.subst q r) (c.subst q r)
  | right_mono_since a b c =>
    exact Axiom.right_mono_since (a.subst q r) (b.subst q r) (c.subst q r)
  | connect_future a => exact Axiom.connect_future (a.subst q r)
  | connect_past a => exact Axiom.connect_past (a.subst q r)
  | enrichment_until a b c =>
    exact Axiom.enrichment_until (a.subst q r) (b.subst q r) (c.subst q r)
  | enrichment_since a b c =>
    exact Axiom.enrichment_since (a.subst q r) (b.subst q r) (c.subst q r)
  | self_accum_until a b => exact Axiom.self_accum_until (a.subst q r) (b.subst q r)
  | self_accum_since a b => exact Axiom.self_accum_since (a.subst q r) (b.subst q r)
  | absorb_until a b => exact Axiom.absorb_until (a.subst q r) (b.subst q r)
  | absorb_since a b => exact Axiom.absorb_since (a.subst q r) (b.subst q r)
  | linear_until a b c d =>
    exact Axiom.linear_until (a.subst q r) (b.subst q r) (c.subst q r) (d.subst q r)
  | linear_since a b c d =>
    exact Axiom.linear_since (a.subst q r) (b.subst q r) (c.subst q r) (d.subst q r)
  | until_F a b => exact Axiom.until_F (a.subst q r) (b.subst q r)
  | since_P a b => exact Axiom.since_P (a.subst q r) (b.subst q r)
  | temp_linearity a b => exact Axiom.temp_linearity (a.subst q r) (b.subst q r)
  | temp_linearity_past a b => exact Axiom.temp_linearity_past (a.subst q r) (b.subst q r)
  | F_until_equiv a => exact Axiom.F_until_equiv (a.subst q r)
  | P_since_equiv a => exact Axiom.P_since_equiv (a.subst q r)
  | modal_future a => exact Axiom.modal_future (a.subst q r)
  | discrete_symm_fwd => exact Axiom.discrete_symm_fwd
  | discrete_symm_bwd => exact Axiom.discrete_symm_bwd
  | discrete_propagate_fwd => exact Axiom.discrete_propagate_fwd
  | discrete_propagate_bwd => exact Axiom.discrete_propagate_bwd
  | discrete_box_necessity => exact Axiom.discrete_box_necessity
  | prior_UZ a => exact Axiom.prior_UZ (a.subst q r)
  | prior_SZ a => exact Axiom.prior_SZ (a.subst q r)
  | z1 a => exact Axiom.z1 (a.subst q r)
  | density a => exact Axiom.density (a.subst q r)
  | dense_indicator => exact Axiom.dense_indicator

/-! ## swapTemporal commutes with substitution -/

/-- swapTemporal commutes with substitution. -/
theorem swapTemporal_subst (q r : Atom)
    (phi : Formula Atom) :
    (phi.swapTemporal).subst q r =
      (phi.subst q r).swapTemporal := by
  induction phi with
  | atom s =>
    simp only [Formula.swapTemporal, Formula.subst]
    by_cases hs : s = q <;>
      simp [hs, Formula.swapTemporal]
  | bot => simp [Formula.swapTemporal, Formula.subst]
  | imp a b iha ihb =>
    simp [Formula.swapTemporal, Formula.subst, iha, ihb]
  | box a ih =>
    simp [Formula.swapTemporal, Formula.subst, ih]
  | untl b a ihb iha =>
    simp [Formula.swapTemporal, Formula.subst, iha, ihb]
  | snce b a ihb iha =>
    simp [Formula.swapTemporal, Formula.subst, iha, ihb]

/-- Axiom substitution preserves `minFrameClass`. -/
theorem axiom_subst_minFrameClass (q r : Atom)
    {phi : Formula Atom} (h : Axiom phi) :
    (axiomSubst q r h).minFrameClass =
      h.minFrameClass := by
  cases h <;> rfl

/-! ## Main theorem: derivation substitution -/

/-- Derivations are preserved under atom substitution.

If `Gamma |-[fc] phi`, then
`Gamma.subst q r |-[fc] phi.subst q r`. -/
def derivationSubst (q r : Atom) {fc : FrameClass} :
    {Gamma : Context Atom} -> {phi : Formula Atom} ->
    DerivationTree fc Gamma phi ->
    DerivationTree fc (Context.subst q r Gamma)
      (phi.subst q r)
  | Gamma, phi, DerivationTree.axiom _ _ h h_fc =>
    DerivationTree.axiom (Context.subst q r Gamma)
      (phi.subst q r) (axiomSubst q r h)
      (axiom_subst_minFrameClass q r h ▸ h_fc)
  | _, phi, DerivationTree.assumption _ _ h => by
    apply DerivationTree.assumption
    rw [mem_context_subst_iff]
    exact ⟨phi, h, rfl⟩
  | _, _, DerivationTree.modus_ponens _ psi _ d1 d2 => by
    have d1' := derivationSubst q r d1
    have d2' := derivationSubst q r d2
    simp only [Formula.subst_imp] at d1'
    exact DerivationTree.modus_ponens _ _ _ d1' d2'
  | _, _, DerivationTree.necessitation psi d => by
    have d' := derivationSubst q r d
    simp only [Context.subst] at d'
    simp only [Formula.subst_box]
    exact DerivationTree.necessitation
      (psi.subst q r) d'
  | _, _, DerivationTree.temporal_necessitation psi d => by
    have d' := derivationSubst q r d
    simp only [Context.subst] at d'
    simp only [Formula.subst_allFuture]
    exact DerivationTree.temporal_necessitation
      (psi.subst q r) d'
  | _, _, DerivationTree.temporal_duality psi d => by
    have d' := derivationSubst q r d
    simp only [Context.subst] at d'
    rw [swapTemporal_subst]
    exact DerivationTree.temporal_duality
      (psi.subst q r) d'
  | Gamma, _, DerivationTree.weakening Gamma' _ _ d h => by
    have d' := derivationSubst q r d
    apply DerivationTree.weakening
      (Context.subst q r Gamma') _ _ d'
    intro psi hpsi
    rw [mem_context_subst_iff] at hpsi ⊢
    obtain ⟨chi, hchi, heq⟩ := hpsi
    exact ⟨chi, h hchi, heq⟩

end Cslib.Logic.Bimodal
