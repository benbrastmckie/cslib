/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Connectives

/-! # Morphisms of Proof Systems

This module provides a generic "morphism of proof systems" abstraction that exhibits the four
CSLib derivation-lifting lemmas as instances of a single functorial action `Deriv.map`.

## Overview

Every derivation-lifting lemma in CSLib has the form: "given a subsumption or formula-map
condition, transport a derivation tree from one proof system to another." The four instances are:

| Existing lift | Formula map `g` | Axiom map |
|---|---|---|
| Modal `liftDerivation` | `id` | predicate subsumption `h_sub` |
| PL `liftDerivationTree` | `id` | predicate subsumption `h_sub` |
| Bimodal `DerivationTree.lift` | `id` | `le_trans` on `minFrameClass` gate |
| Bimodal `liftDerivationWith` | `liftFormula a` | `liftAxiom a` |

The abstraction: a **morphism of proof systems** `H : ProofSigHom σ₁ σ₂` consists of a formula
map `g : F₁ → F₂`, an implication homomorphism, a Type-valued axiom-family map, and a
closure-coherence condition. Its **functorial action** `Deriv.map H` transports any derivation
tree along `H`.

## Design Notes

- `ProofSig.Ax : F → Type` is Type-valued (not `Prop`) to preserve computational data. The
  Bimodal `Axiom : Formula → Type u` already fits; `liftAxiom` depends on constructors.
- `closures` is a `List` of unary operators so generic recursion can iterate over them.
- Closest Mathlib analogues: `FirstOrder.Language.LHom` (signature morphism half);
  `CategoryTheory.Cat.freeMap` (free path-category, the unary/linear analogue of this
  branching-derivation construction). No free-multicategory library exists in Mathlib. -/

@[expose] public section

namespace Cslib.Logic.Metalogic

/-! ## Proof-System Signatures -/

/-- A Hilbert-style proof-system signature over formula type `F` with implication.

- `Ax φ` is the Type-valued family of axiom instances for `φ`. Using `Type` (not `Prop`)
  preserves computational constructor data; Bimodal's `Axiom : Formula → Type u` fits as-is.
- `closures` is the list of unary empty-context closure operators (box, allFuture, swapTemporal).
  The list structure enables generic iteration in `Deriv.map`. -/
structure ProofSig (F : Type*) [HasImp F] where
  /-- Type-valued axiom family: `Ax φ` is the type of proofs that `φ` is an axiom. -/
  Ax : F → Type
  /-- Unary empty-context closure operators (necessitation-style rules). -/
  closures : List (F → F)

/-! ## Free Derivation Algebra -/

/-- The free derivation algebra over a proof-system signature.

`Deriv σ Γ φ` is the type of derivation trees proving `φ` from context `Γ` using the rules
in `σ`. This is the initial object of the rule system.

The five constructors mirror the four existing CSLib derivation inductives:
- `ax` / `assum` / `mp` / `weak` appear in all four existing inductives;
- `close` is the generic closure rule covering `necessitation`, `temporal_necessitation`, and
  `temporal_duality`, parameterised by the closure operator `m ∈ σ.closures`. -/
inductive Deriv {F : Type*} [HasImp F] (σ : ProofSig F) : List F → F → Type _
  /-- Axiom rule: any axiom instance (in `σ.Ax φ`) is derivable from any context. -/
  | ax (Γ : List F) (φ : F) (h : σ.Ax φ) : Deriv σ Γ φ
  /-- Assumption rule: formulas in the context are derivable. -/
  | assum (Γ : List F) (φ : F) (h : φ ∈ Γ) : Deriv σ Γ φ
  /-- Modus ponens: from `Γ ⊢ φ → ψ` and `Γ ⊢ φ`, derive `Γ ⊢ ψ`. -/
  | mp (Γ : List F) (φ ψ : F)
      (d₁ : Deriv σ Γ (HasImp.imp φ ψ))
      (d₂ : Deriv σ Γ φ) : Deriv σ Γ ψ
  /-- Closure rule (empty context only): if `m ∈ σ.closures` and `⊢ φ`, then `⊢ m φ`. -/
  | close (m : F → F) (hm : m ∈ σ.closures) (φ : F)
      (d : Deriv σ [] φ) : Deriv σ [] (m φ)
  /-- Weakening: from `Γ ⊢ φ` and `Γ ⊆ Δ`, derive `Δ ⊢ φ`. -/
  | weak (Γ Δ : List F) (φ : F)
      (d : Deriv σ Γ φ)
      (h : Γ ⊆ Δ) : Deriv σ Δ φ

namespace Deriv

/-- Computable height of a derivation tree. Used for well-founded recursion. -/
def height {F : Type*} [HasImp F] {σ : ProofSig F} :
    ∀ {Γ : List F} {φ : F}, Deriv σ Γ φ → Nat
  | _, _, .ax _ _ _ => 0
  | _, _, .assum _ _ _ => 0
  | _, _, .mp _ _ _ d₁ d₂ => 1 + max d₁.height d₂.height
  | _, _, .close _ _ _ d => 1 + d.height
  | _, _, .weak _ _ _ d _ => 1 + d.height

/-- Height is invariant under formula-index transport.

When `Deriv.map` rewrites a formula index via `▸`, height is preserved since the cast
is a type-theoretic artifact that does not change the derivation structure. -/
lemma height_cast_formula {F : Type*} [HasImp F] {σ : ProofSig F}
    {Γ : List F} {φ₁ φ₂ : F} (h : φ₁ = φ₂) (d : Deriv σ Γ φ₁) :
    (h ▸ d : Deriv σ Γ φ₂).height = d.height := by
  subst h; rfl

end Deriv

/-! ## Proof-System Morphisms -/

/-- A morphism of proof-system signatures from `σ₁ : ProofSig F₁` to `σ₂ : ProofSig F₂`.

Fields:
- `g`: formula map `F₁ → F₂`
- `g_imp`: `g` preserves implication: `g (φ → ψ) = g φ → g ψ`
- `axMap`: axiom-family morphism `σ₁.Ax φ → σ₂.Ax (g φ)` for each `φ`
- `clMap`: closure coherence — each `m ∈ σ₁.closures` maps to some `m' ∈ σ₂.closures`
  with `g (m φ) = m' (g φ)` for all `φ` (the naturality square for each closure)

This is the CSLib analogue of `FirstOrder.Language.LHom` (signature-morphism half) combined with
the derivation-transport functor `Deriv.map` below. -/
structure ProofSigHom {F₁ F₂ : Type*} [HasImp F₁] [HasImp F₂]
    (σ₁ : ProofSig F₁) (σ₂ : ProofSig F₂) where
  /-- Formula map. -/
  g : F₁ → F₂
  /-- Implication homomorphism: `g` preserves `HasImp.imp`. -/
  g_imp : ∀ φ ψ : F₁, g (HasImp.imp φ ψ) = HasImp.imp (g φ) (g ψ)
  /-- Axiom-family morphism: transports axiom instances from `σ₁` to `σ₂` over `g`. -/
  axMap : ∀ φ : F₁, σ₁.Ax φ → σ₂.Ax (g φ)
  /-- Closure coherence: each `m ∈ σ₁.closures` maps **constructively** to a chosen
  `m' ∈ σ₂.closures` with `g ∘ m = m' ∘ g`. The choice of `m'` is `Type`-valued data (a
  `Subtype`, not a `Prop` existential) because `Deriv.map`'s `close` case must use the witness
  `m'` to build a derivation tree — extracting it from a `Prop` existential is barred by
  large elimination. This parallels the `Type`-valued axiom family `Ax`. -/
  clMap : ∀ m ∈ σ₁.closures,
    { m' : F₂ → F₂ // m' ∈ σ₂.closures ∧ ∀ φ : F₁, g (m φ) = m' (g φ) }

namespace ProofSigHom

/-- The identity proof-system morphism for a signature `σ`. -/
def id {F : Type*} [HasImp F] (σ : ProofSig F) : ProofSigHom σ σ where
  g := _root_.id
  g_imp := fun _ _ => rfl
  axMap := fun _ h => h
  clMap := fun m hm => ⟨m, hm, fun _ => rfl⟩

/-- Composition of proof-system morphisms.

`comp H₂ H₁` composes `H₁ : ProofSigHom σ₁ σ₂` and `H₂ : ProofSigHom σ₂ σ₃`. -/
def comp {F₁ F₂ F₃ : Type*} [HasImp F₁] [HasImp F₂] [HasImp F₃]
    {σ₁ : ProofSig F₁} {σ₂ : ProofSig F₂} {σ₃ : ProofSig F₃}
    (H₂ : ProofSigHom σ₂ σ₃) (H₁ : ProofSigHom σ₁ σ₂) : ProofSigHom σ₁ σ₃ where
  g := H₂.g ∘ H₁.g
  g_imp := fun φ ψ => by
    simp only [Function.comp, H₁.g_imp φ ψ, H₂.g_imp (H₁.g φ) (H₁.g ψ)]
  axMap := fun φ h => H₂.axMap _ (H₁.axMap φ h)
  -- Projection form (not `obtain`/`exact`) keeps `(comp …).clMap.val` definitionally equal to
  -- `(H₂.clMap …).val`, which `Deriv.map_comp`'s `close` case relies on.
  clMap := fun m hm =>
    ⟨(H₂.clMap (H₁.clMap m hm).1 (H₁.clMap m hm).2.1).1,
     (H₂.clMap (H₁.clMap m hm).1 (H₁.clMap m hm).2.1).2.1,
     fun φ => by
       simp only [Function.comp, (H₁.clMap m hm).2.2 φ,
         (H₂.clMap (H₁.clMap m hm).1 (H₁.clMap m hm).2.1).2.2 (H₁.g φ)]⟩

end ProofSigHom

/-! ## Functorial Action -/

namespace Deriv

/-- **The universal lift**: the functorial action of a proof-system morphism on derivation trees.

`Deriv.map H d` transports `d : Deriv σ₁ Γ φ` along `H : ProofSigHom σ₁ σ₂`, yielding a
derivation tree in `σ₂` with context `Γ.map H.g` and conclusion `H.g φ`.

The four existing CSLib lift functions are instances (up to constructor-preserving equivalence
built in Phases 2–5):
- Modal `liftDerivation h_sub` ↔ `Deriv.map ⟨id, rfl, h_sub, {box}⟩`
- PL `liftDerivationTree h_sub` ↔ `Deriv.map ⟨id, rfl, h_sub, ∅⟩`
- Bimodal `DerivationTree.lift h_le` ↔ `Deriv.map ⟨id, rfl, fun ⟨h, hfc⟩ => ⟨h, le_trans hfc h_le⟩, …⟩`
- Bimodal `liftDerivationWith a` ↔ `Deriv.map ⟨liftFormula a, liftFormula_imp, liftAxiom a, …⟩` -/
def map {F₁ F₂ : Type*} [HasImp F₁] [HasImp F₂]
    {σ₁ : ProofSig F₁} {σ₂ : ProofSig F₂}
    (H : ProofSigHom σ₁ σ₂) :
    ∀ {Γ : List F₁} {φ : F₁}, Deriv σ₁ Γ φ → Deriv σ₂ (Γ.map H.g) (H.g φ)
  | _, _, .ax _ φ h =>
      .ax _ _ (H.axMap φ h)
  | _, _, .assum _ _ h =>
      .assum _ _ (List.mem_map_of_mem h)
  | _, _, .mp _ φ ψ d₁ d₂ =>
      -- `H.g_imp φ ψ ▸` rewrites the type of `map H d₁` from `... (H.g (imp φ ψ))` to
      -- `... (imp (H.g φ) (H.g ψ))`, matching the `mp` constructor's first premise type.
      .mp _ (H.g φ) (H.g ψ) (H.g_imp φ ψ ▸ map H d₁) (map H d₂)
  | _, _, .close m hm φ d =>
      -- clMap gives a chosen `m' ∈ σ₂.closures` with `g (m φ) = m' (g φ)`; the `▸` rewrites the
      -- conclusion. Projections (not a `let`-match) keep the body definitionally transparent so
      -- the functor laws below reduce through this case.
      (H.clMap m hm).2.2 φ ▸ .close (H.clMap m hm).1 (H.clMap m hm).2.1 _ (map H d)
  | _, _, .weak _ Δ _ d h =>
      .weak _ _ _ (map H d) (List.map_subset H.g h)

/-! ## Functor Laws -/

/-- `Deriv.map` preserves derivation height. -/
theorem map_height {F₁ F₂ : Type*} [HasImp F₁] [HasImp F₂]
    {σ₁ : ProofSig F₁} {σ₂ : ProofSig F₂}
    (H : ProofSigHom σ₁ σ₂)
    {Γ : List F₁} {φ : F₁} (d : Deriv σ₁ Γ φ) :
    (map H d).height = d.height := by
  induction d with
  | ax _ _ _ => rfl
  | assum _ _ _ => rfl
  | mp _ φ ψ d₁ d₂ ih₁ ih₂ =>
    simp only [map, height, height_cast_formula (H.g_imp φ ψ), ih₁, ih₂]
  | close m hm φ d ih =>
    simp only [map, height, height_cast_formula]; exact congrArg (1 + ·) ih
  | weak _ _ _ _ _ ih =>
    simp only [map, height, ih]

/-- `map` commutes with formula-index transport: mapping a cast derivation is heterogeneously
equal to casting the mapped derivation. Used to push `map H₂` past the `g_imp ▸` casts that
`Deriv.map`'s `mp` case introduces, when proving the composition law. -/
lemma map_eqRec_heq {F₁ F₂ : Type*} [HasImp F₁] [HasImp F₂]
    {σ₁ : ProofSig F₁} {σ₂ : ProofSig F₂} (H : ProofSigHom σ₁ σ₂)
    {Γ : List F₁} {φ φ' : F₁} (e : φ = φ') (d : Deriv σ₁ Γ φ) :
    HEq (map H (e ▸ d)) (map H d) := by subst e; rfl

/-- **Functor identity law** (heterogeneous equality form).

`Deriv.map` of the identity morphism is heterogeneously equal to the identity. The use of `HEq`
accounts for the fact that `List.map id Γ = Γ` is propositional rather than definitional, so
the result type `Deriv σ (Γ.map id) φ` differs from `Deriv σ Γ φ` as types. -/
theorem map_id {F : Type*} [HasImp F] (σ : ProofSig F)
    {Γ : List F} {φ : F} (d : Deriv σ Γ φ) :
    HEq (map (ProofSigHom.id σ) d) d := by
  induction d with
  | ax Γ φ h => simp only [map, ProofSigHom.id, id_eq]; rw [List.map_id]
  | assum Γ φ h =>
    simp only [map, ProofSigHom.id, id_eq]
    congr 1 <;> first | rw [List.map_id] | exact proof_irrel_heq _ _
  | mp Γ φ ψ d₁ d₂ ih₁ ih₂ =>
    simp only [map, ProofSigHom.id, id_eq]
    congr 1 <;> first | rw [List.map_id] | assumption
  | close m hm φ d ih =>
    -- Empty context: `[].map id = []`, so no context transport needed; `id` fixes the
    -- chosen closure `m` pointwise, so the formula index is `m φ` on both sides.
    simp only [map, ProofSigHom.id, id_eq]
    congr 1 <;> first | rw [List.map_id] | assumption | exact eq_of_heq (by assumption) | exact proof_irrel_heq _ _ | rfl
  | weak Γ Δ φ d h ih =>
    simp only [map, ProofSigHom.id, id_eq]
    congr 1 <;> first | rw [List.map_id] | assumption | exact eq_of_heq (by assumption) | exact proof_irrel_heq _ _ | rfl

/-- **Functor composition law** (heterogeneous equality form).

`Deriv.map` distributes over composition: `map (comp H₂ H₁) d == map H₂ (map H₁ d)`.
The `HEq` accounts for the fact that `(Γ.map H₁.g).map H₂.g` and `Γ.map (H₂.g ∘ H₁.g)` are
propositionally (not definitionally) equal via `List.map_map`. -/
theorem map_comp {F₁ F₂ F₃ : Type*} [HasImp F₁] [HasImp F₂] [HasImp F₃]
    {σ₁ : ProofSig F₁} {σ₂ : ProofSig F₂} {σ₃ : ProofSig F₃}
    (H₂ : ProofSigHom σ₂ σ₃) (H₁ : ProofSigHom σ₁ σ₂)
    {Γ : List F₁} {φ : F₁} (d : Deriv σ₁ Γ φ) :
    HEq (map (H₂.comp H₁) d) (map H₂ (map H₁ d)) := by
  -- Each constructor commutes with `map`; the indices differ only by
  -- `(Γ.map H₁.g).map H₂.g = Γ.map (H₂.g ∘ H₁.g)` (`List.map_map`). `congr 1` splits the
  -- heterogeneous goal into that index equality, the per-subderivation IHs, and
  -- proof-irrelevant membership/subset side conditions.
  induction d with
  | ax Γ φ h =>
    simp only [map, ProofSigHom.comp]
    congr 1 <;> first | rw [List.map_map] | exact proof_irrel_heq _ _ | rfl
  | assum Γ φ h =>
    simp only [map, ProofSigHom.comp]
    congr 1 <;> first | rw [List.map_map] | exact proof_irrel_heq _ _ | rfl
  | mp Γ φ ψ d₁ d₂ ih₁ ih₂ =>
    -- `congr 1` exposes the `g_imp ▸` casts on the `mp` premises; the first premise is closed
    -- by chaining `eqRec_heq` (strip both casts) with the IH and `map_eqRec_heq` (push `map H₂`
    -- past the inner cast); the second premise is exactly the IH.
    simp only [map, ProofSigHom.comp]
    congr 1 <;>
      first
        | rw [List.map_map]
        | exact (eqRec_heq _ _).trans
            (ih₁.trans ((map_eqRec_heq H₂ _ _).symm.trans (eqRec_heq _ _).symm))
        | assumption
        | exact proof_irrel_heq _ _
        | rfl
  | close m hm φ d ih =>
    -- The `close` conclusion carries a `clMap`-coherence cast on each side, and the RHS applies
    -- `map H₂` to a cast `close`. Strip the LHS cast (`eqRec_heq`), push `map H₂` past the inner
    -- cast (`map_eqRec_heq`) and reduce it (`simp [map]`), strip the resulting cast, then match
    -- the two `close` nodes: the chosen closures agree definitionally, the membership proofs by
    -- irrelevance, and the subderivations by the IH.
    simp only [map, ProofSigHom.comp]
    refine (eqRec_heq _ _).trans (HEq.trans ?_ (map_eqRec_heq H₂ _ _).symm)
    simp only [map]
    refine HEq.trans ?_ (eqRec_heq _ _).symm
    congr 1 <;> first | exact eq_of_heq ih | exact ih | exact proof_irrel_heq _ _ | rfl
  | weak Γ Δ φ d h ih =>
    simp only [map, ProofSigHom.comp]
    congr 1 <;>
      first | rw [List.map_map] | assumption | exact eq_of_heq (by assumption) | exact proof_irrel_heq _ _ | rfl

end Deriv

end Cslib.Logic.Metalogic

end
