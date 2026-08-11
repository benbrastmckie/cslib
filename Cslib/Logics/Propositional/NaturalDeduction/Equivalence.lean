/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Logics.Propositional.NaturalDeduction.FromHilbert
public import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules

/-! # Equivalence between Hilbert and Natural Deduction Systems

This module proves the extensional equivalence between the Hilbert-style proof system
(`DerivationTree`, `Deriv`, `Derivable`) and the standalone natural deduction system
(`Theory.Derivation`, `DerivableIn`).

The equivalence is parameterized over any axiom predicate `Axioms` that includes K, S,
and the 6 conjunction/disjunction schemata. The primary form is context-based
(`hilbert_iff_nd_ctx`); closed-context forms are corollaries at `Γ = ∅`.

## Main Definitions

- `AxiomTheory` : Generic ND theory for any axiom predicate.
- `HilbertAxiomTheory` : Classical specialization (backward compatibility).
- `MinimalAxioms` : Typeclass bundling 8 axiom witnesses
    (K, S, andI, andE1, andE2, orI1, orI2, orE).
- `hilbertToND` : Translation from Hilbert derivation trees to ND derivations (structural).
- `ndToHilbert` : Translation from ND derivations to Hilbert derivation trees
    (uses `[MinimalAxioms]`).
- `hilbert_iff_nd_ctx` : Generic context-based equivalence (primary form, uses `[MinimalAxioms]`).
- `hilbert_iff_nd_ctx_min` : Minimal logic context-based instantiation.
- `hilbert_iff_nd_ctx_int` : Intuitionistic context-based instantiation.
- `hilbert_iff_nd_ctx_cl` : Classical context-based instantiation.
- `hilbert_iff_nd` : Generic closed-context equivalence (uses `[MinimalAxioms]`).
- `hilbert_iff_nd_min` : Minimal logic closed-context corollary.
- `hilbert_iff_nd_int` : Intuitionistic closed-context corollary.
- `hilbert_iff_nd_cl` : Classical closed-context corollary.

## Design

The two systems differ in context representation (List vs Finset) and axiom handling
(baked-in vs parameterized). The bridge uses `List.toFinset` / `Finset.toList` for
context conversion (with `Finset.toList_toFinset` as the key bridge lemma) and wraps
Hilbert axiom schemata into an ND `Theory` via `AxiomTheory`.

The `MinimalAxioms` typeclass bundles the 8 axiom witnesses needed for the ND-to-Hilbert
direction. Instances are provided for `MinPropAxiom`, `IntPropAxiom`, and `PropositionalAxiom`,
allowing the 6 concrete corollaries to be stated as one-line calls to the generic theorems.

Note: `AxiomTheory Axioms` is not the same as `MPL`, `IPL`, or `CPL` (which are defined
by specific axiom sets). The equivalence bridges two parameterized systems sharing the
same axiom predicate; it is not a statement about pure logic strength.

The `ndToHilbert` direction is `noncomputable` because it uses `deductionTheorem`,
which relies on `Classical.propDecidable`. The `hilbertToND` direction is computable.

The `h_EFQ` parameter was removed from `ndToHilbert` and all downstream signatures
because `bot` elimination does not appear as a ND constructor; EFQ in the Hilbert sense
is an axiom schema instance (`ax` constructor), handled uniformly without a special witness.

## No Direct ND Soundness/Completeness

This module deliberately does not state ND-side soundness or completeness theorems against
semantic validity. Both directions are reached instead by composing the Hilbert/ND
equivalence proved here (`hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`,
`hilbert_iff_nd_ctx_cl`) with the corresponding Hilbert-side soundness/completeness results —
there is no gap, only a routing choice: ND soundness/completeness for a given axiom set is
`hilbert_iff_nd_ctx_*` chained with that axiom set's Hilbert soundness/completeness theorem.

## References

* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965], Ch. I, §1.2
  -- primary reference for the Hilbert/ND equivalence
* [A. S. Troelstra and D. van Dalen, *Constructivism in Mathematics*][TroelstraVanDalen1988],
  Vol. I, §10.4 -- intuitionistic case
* `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- Hilbert system
* `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` -- ND system
* `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` -- deduction theorem
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open InferenceSystem

/-! ## Theory Definitions -/

/-- Generic ND theory for any axiom predicate.
A proposition belongs to `AxiomTheory Axioms` iff `Axioms φ` holds. -/
def AxiomTheory {Atom : Type*} (Axioms : PL.Proposition Atom → Prop) : Theory Atom :=
  { φ | Axioms φ }

/-- Membership in `AxiomTheory Axioms` is equivalent to the axiom predicate holding. -/
@[simp]
theorem mem_axiomTheory {Atom : Type*} {Axioms : PL.Proposition Atom → Prop}
    {φ : PL.Proposition Atom} :
    φ ∈ (AxiomTheory Axioms : Theory Atom) ↔ Axioms φ :=
  Iff.rfl

/-- The ND theory corresponding to the classical Hilbert axiom schemata.
Backward-compatible abbreviation for `AxiomTheory PropositionalAxiom`. -/
abbrev HilbertAxiomTheory {Atom : Type*} : Theory Atom :=
  AxiomTheory (@PropositionalAxiom Atom)

/-- Membership in `HilbertAxiomTheory` is equivalent to being a propositional axiom. -/
theorem mem_hilbertAxiomTheory {Atom : Type*} {φ : PL.Proposition Atom} :
    φ ∈ (HilbertAxiomTheory : Theory Atom) ↔ PropositionalAxiom φ :=
  mem_axiomTheory

variable {Atom : Type*} [DecidableEq Atom]

/-! ## MinimalAxioms Typeclass -/

/-- Typeclass bundling the 8 axiom witnesses required for the ND-to-Hilbert translation.

Extends `ConjImpAxioms` with the three or-axiom witnesses (orI1, orI2, orE). Any axiom
predicate that includes K, S, andI, andE1, andE2, orI1, orI2, and orE can provide an
instance, enabling the generic `ndToHilbert`, `hilbert_iff_nd_ctx`, and `hilbert_iff_nd`
to operate without 8 explicit parameters. -/
class MinimalAxioms {Atom : Type*} (Axioms : PL.Proposition Atom → Prop) : Prop
    extends ConjImpAxioms Axioms where
  /-- Or-introduction1 schema: φ → (φ ∨ ψ) -/
  h_orI1 : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (φ.or ψ))
  /-- Or-introduction2 schema: ψ → (φ ∨ ψ) -/
  h_orI2 : ∀ (φ ψ : PL.Proposition Atom), Axioms (ψ.imp (φ.or ψ))
  /-- Or-elimination schema: (φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ)) -/
  h_orE : ∀ (φ ψ χ : PL.Proposition Atom),
    Axioms ((φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ)))

/-- `MinPropAxiom` satisfies `MinimalAxioms`. -/
instance : MinimalAxioms (@MinPropAxiom Atom) where
  h_K := fun φ ψ => .implyK φ ψ
  h_S := fun φ ψ χ => .implyS φ ψ χ
  h_andI := fun φ ψ => .andI φ ψ
  h_andE1 := fun φ ψ => .andE1 φ ψ
  h_andE2 := fun φ ψ => .andE2 φ ψ
  h_orI1 := fun φ ψ => .orI1 φ ψ
  h_orI2 := fun φ ψ => .orI2 φ ψ
  h_orE := fun φ ψ χ => .orE φ ψ χ

/-- `IntPropAxiom` satisfies `MinimalAxioms`. -/
instance : MinimalAxioms (@IntPropAxiom Atom) where
  h_K := fun φ ψ => .implyK φ ψ
  h_S := fun φ ψ χ => .implyS φ ψ χ
  h_andI := fun φ ψ => .andI φ ψ
  h_andE1 := fun φ ψ => .andE1 φ ψ
  h_andE2 := fun φ ψ => .andE2 φ ψ
  h_orI1 := fun φ ψ => .orI1 φ ψ
  h_orI2 := fun φ ψ => .orI2 φ ψ
  h_orE := fun φ ψ χ => .orE φ ψ χ

/-- `PropositionalAxiom` satisfies `MinimalAxioms`. -/
instance : MinimalAxioms (@PropositionalAxiom Atom) where
  h_K := fun φ ψ => .implyK φ ψ
  h_S := fun φ ψ χ => .implyS φ ψ χ
  h_andI := fun φ ψ => .andI φ ψ
  h_andE1 := fun φ ψ => .andE1 φ ψ
  h_andE2 := fun φ ψ => .andE2 φ ψ
  h_orI1 := fun φ ψ => .orI1 φ ψ
  h_orI2 := fun φ ψ => .orI2 φ ψ
  h_orE := fun φ ψ χ => .orE φ ψ χ

/-! ## Minimal Logic Inclusion View

The definitions and theorems in this section provide the "strength by inclusion" view that
reconciles the two encodings of minimal propositional strength on the Hilbert substrate:
the `MinimalAxioms` typeclass (8-field class) and the set-inclusion characterization
`minimal ⊆ T`. -/

omit [DecidableEq Atom] in
/-- The Hilbert axiom set for the 8 connective axiom schemas of minimal propositional logic
(K, S, andI, andE1, andE2, orI1, orI2, orE).

**Warning**: `minimal ≠ MPL`. In CSLib, `MPL = ∅` is the *theory* (set of propositions
derivable by modus ponens with no axioms). In contrast, `minimal` is the *axiom set*: the
8 Hilbert schemas that generate MPL when rules are added. `IsMinimal` is therefore a
Hilbert-substrate notion: a theory "carries the 8 connective axiom schemas", distinct from
natural-deduction minimal logic whose content lives in rule constructors, not in a theory set.

The bridge `MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms` is non-vacuous precisely
because `minimal ≠ ∅`. -/
abbrev minimal : Theory Atom := AxiomTheory (@MinPropAxiom Atom)

omit [DecidableEq Atom] in
/-- A theory carries the minimal Hilbert axiom schemas if it contains all 8 connective schemas
(K, S, andI, andE1, andE2, orI1, orI2, orE).

This is defined as `MinimalAxioms (fun φ => φ ∈ T)` — reusing the existing 8-field typeclass
rather than introducing a duplicate class. Since `IsMinimal` is an `abbrev`, `[IsMinimal T]`
in a type signature reduces to `[MinimalAxioms (fun φ => φ ∈ T)]` during typeclass resolution.

Note: `IsMinimal` is a Hilbert-substrate notion. See `minimal` for why `IsMinimal T` differs
from `MPL ⊆ T` (which is trivially `True` since `MPL = ∅`). -/
abbrev IsMinimal (T : Theory Atom) : Prop := MinimalAxioms (fun φ => φ ∈ T)

omit [DecidableEq Atom] in
/-- The core bridge lemma **(★)**: `MinimalAxioms P` if and only if `P` holds for every
formula satisfying `MinPropAxiom`.

Both `isMinimalIff` and `minimalAxioms_iff_subset` reduce to this lemma via the definitional
equivalence `φ ∈ AxiomTheory P ↔ P φ` (`mem_axiomTheory`). -/
theorem minimalAxioms_iff_forall_minPropAxiom
    (P : PL.Proposition Atom → Prop) :
    MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ := by
  constructor
  · intro h φ hφ
    cases hφ with
    | implyK a b => exact h.h_K a b
    | implyS a b c => exact h.h_S a b c
    | andI a b => exact h.h_andI a b
    | andE1 a b => exact h.h_andE1 a b
    | andE2 a b => exact h.h_andE2 a b
    | orI1 a b => exact h.h_orI1 a b
    | orI2 a b => exact h.h_orI2 a b
    | orE a b c => exact h.h_orE a b c
  · intro h
    exact { h_K := fun a b => h _ (.implyK a b),
             h_S := fun a b c => h _ (.implyS a b c),
             h_andI := fun a b => h _ (.andI a b),
             h_andE1 := fun a b => h _ (.andE1 a b),
             h_andE2 := fun a b => h _ (.andE2 a b),
             h_orI1 := fun a b => h _ (.orI1 a b),
             h_orI2 := fun a b => h _ (.orI2 a b),
             h_orE := fun a b c => h _ (.orE a b c) }

omit [DecidableEq Atom] in
/-- A theory is minimal (carries all 8 connective schemas) iff it contains `minimal`.

This is the "strength by inclusion" characterization: `IsMinimal T ↔ minimal ⊆ T`. The proof
reduces via **(★)** (`minimalAxioms_iff_forall_minPropAxiom`) and `mem_axiomTheory`. -/
theorem isMinimalIff (T : Theory Atom) : IsMinimal T ↔ minimal ⊆ T := by
  constructor
  · intro h x hx
    exact (minimalAxioms_iff_forall_minPropAxiom _).mp h x (mem_axiomTheory.mp hx)
  · intro h
    apply (minimalAxioms_iff_forall_minPropAxiom _).mpr
    intro x hx
    exact h (mem_axiomTheory.mpr hx)

omit [DecidableEq Atom] in
/-- `MinimalAxioms Axioms` iff `minimal ⊆ AxiomTheory Axioms`.

This is the key bridge between the typeclass encoding and the inclusion encoding.
Both sides reduce to `∀ φ, MinPropAxiom φ → Axioms φ` via **(★)** and `mem_axiomTheory`. -/
theorem minimalAxioms_iff_subset
    (Axioms : PL.Proposition Atom → Prop) :
    MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms := by
  constructor
  · intro h x hx
    exact mem_axiomTheory.mpr ((minimalAxioms_iff_forall_minPropAxiom _).mp h x
      (mem_axiomTheory.mp hx))
  · intro h
    apply (minimalAxioms_iff_forall_minPropAxiom _).mpr
    intro x hx
    exact mem_axiomTheory.mp (h (mem_axiomTheory.mpr hx))

omit [DecidableEq Atom] in
/-- If a theory is minimal and is contained in a larger theory, the larger theory is also minimal.

This is the monotone propagation of the `IsMinimal` predicate, mirroring
`instIsIntuitionisticExtension` and `instIsClassicalExtension`. -/
theorem instIsMinimalExtension {T T' : Theory Atom} [h : IsMinimal T]
    (hsub : T ⊆ T') : IsMinimal T' :=
  (minimalAxioms_iff_forall_minPropAxiom _).mpr fun φ hφ =>
    hsub ((minimalAxioms_iff_forall_minPropAxiom _).mp h φ hφ)

omit [DecidableEq Atom] in
/-- The theory `minimal` is itself minimal (i.e., contains all 8 connective schemas).

This is the base instance: `minimal ⊆ minimal` witnesses `IsMinimal minimal`. -/
instance instIsMinimalMinimal : IsMinimal (Atom := Atom) minimal :=
  (isMinimalIff minimal).mpr (fun _ hx => hx)

/-! ## Context Membership Bridge Lemmas -/

/-- Elements of `(insert A Γ).toList` belong to `A :: Γ.toList`. -/
theorem finset_insert_toList_mem_cons (A : PL.Proposition Atom) (Γ : Ctx Atom)
    {x : PL.Proposition Atom} :
    x ∈ (Insert.insert A Γ : Ctx Atom).toList → x ∈ A :: Γ.toList := by
  simp [Finset.mem_toList, List.mem_cons]

/-! ## Hilbert to ND Translation -/

/-- Translate a Hilbert derivation tree into an ND derivation under `AxiomTheory Axioms`.

This direction is purely structural (no axiom parameters needed).
Each constructor maps to its ND counterpart:
- `ax`: axiom schema instance -> ND axiom rule
- `assumption`: context membership -> ND assumption (via `List.mem_toFinset`)
- `modusPonens`: -> ND implication elimination
- `weakening`: -> ND context weakening (via `Finset` subset from `List` subset) -/
def hilbertToND
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    DerivationTree Axioms Γ φ →
    @Theory.Derivation Atom _ (AxiomTheory Axioms : Theory Atom) Γ.toFinset φ
  | .ax _ _ h_ax =>
    Theory.Derivation.ax (mem_axiomTheory.mpr h_ax)
  | .assumption _ _ h_mem =>
    Theory.Derivation.ass (List.mem_toFinset.mpr h_mem)
  | .modusPonens _ _ _ d₁ d₂ =>
    Theory.Derivation.impE (hilbertToND d₁) (hilbertToND d₂)
  | .weakening _ _ _ d h_sub =>
    Theory.Derivation.weakCtx
      (fun x hx => List.mem_toFinset.mpr (h_sub x (List.mem_toFinset.mp hx)))
      (hilbertToND d)

/-- Prop-level wrapper: if `Γ ⊢ φ` in the Hilbert system, then `φ` is derivable
in ND under `AxiomTheory Axioms` with context `Γ.toFinset`. -/
theorem hilbert_to_nd_deriv
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : Deriv Axioms Γ φ) :
    DerivableIn (AxiomTheory Axioms : Theory Atom)
      ((Γ.toFinset : Ctx Atom) ⊢ φ) := by
  obtain ⟨d⟩ := h
  exact ⟨hilbertToND d⟩

/-! ## ND to Hilbert Translation -/

/-- Translate an ND derivation under `AxiomTheory Axioms` into a Hilbert derivation tree.

Requires a `MinimalAxioms Axioms` instance bundling K, S, andI, andE1, andE2, orI1, orI2,
and orE axiom witnesses. Each constructor maps to its Hilbert counterpart:
- `ax`: theory membership -> Hilbert axiom rule
- `ass`: context membership -> Hilbert assumption (via `Finset.mem_toList`)
- `andI`: -> AndI axiom + two modus ponens
- `andE1`: -> AndE1 axiom + modus ponens
- `andE2`: -> AndE2 axiom + modus ponens
- `orI1`: -> OrI1 axiom + modus ponens
- `orI2`: -> OrI2 axiom + modus ponens
- `orE`: -> deduction theorem on branches, then OrE axiom + three modus ponens
- `impE`: -> Hilbert modus ponens
- `impI`: -> deduction theorem (uses K, S witnesses from instance, and context bridge lemmas) -/
noncomputable def ndToHilbert
    {Axioms : PL.Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    @Theory.Derivation Atom _ (AxiomTheory Axioms : Theory Atom) Γ φ →
    DerivationTree Axioms Γ.toList φ
  | .ax h_mem =>
    .ax Γ.toList φ (mem_axiomTheory.mp h_mem)
  | .ass h_mem =>
    .assumption Γ.toList φ (Finset.mem_toList.mpr h_mem)
  | @Theory.Derivation.andI _ _ _ A B G d₁ d₂ => by
    have ih₁ := ndToHilbert d₁
    have ih₂ := ndToHilbert d₂
    exact hilbertAndI inst.h_andI ih₁ ih₂
  | @Theory.Derivation.andE1 _ _ _ A B G d => by
    have ih := ndToHilbert d
    exact hilbertAndE1 inst.h_andE1 ih
  | @Theory.Derivation.andE2 _ _ _ A B G d => by
    have ih := ndToHilbert d
    exact hilbertAndE2 inst.h_andE2 ih
  | @Theory.Derivation.orI1 _ _ _ A B G d => by
    have ih := ndToHilbert d
    exact hilbertOrI1 inst.h_orI1 ih
  | @Theory.Derivation.orI2 _ _ _ A B G d => by
    have ih := ndToHilbert d
    exact hilbertOrI2 inst.h_orI2 ih
  | @Theory.Derivation.orE _ _ _ A B C G d dA dB => by
    have ihd := ndToHilbert d
    have ihA := ndToHilbert dA
    have ihB := ndToHilbert dB
    -- ihA : DerivationTree (insert A G).toList C -- weaken to A :: G.toList
    have ihA' := DerivationTree.weakening _ (A :: G.toList) C ihA
      (fun x hx => finset_insert_toList_mem_cons A G hx)
    -- ihB : DerivationTree (insert B G).toList C -- weaken to B :: G.toList
    have ihB' := DerivationTree.weakening _ (B :: G.toList) C ihB
      (fun x hx => finset_insert_toList_mem_cons B G hx)
    exact hilbertOrE inst.h_K inst.h_S inst.h_orE ihd ihA' ihB'
  | .impE d₁ d₂ =>
    .modusPonens Γ.toList _ φ
      (ndToHilbert d₁)
      (ndToHilbert d₂)
  | @Theory.Derivation.impI _ _ _ A B Γ' d => by
    -- Recursive call gives: DerivationTree (insert A Γ').toList B
    have ih := ndToHilbert d
    -- Weaken to A :: Γ'.toList using the bridge lemma
    have ih' := DerivationTree.weakening _ (A :: Γ'.toList) B ih
      (fun x hx => finset_insert_toList_mem_cons A Γ' hx)
    -- Apply deduction theorem to get Γ'.toList ⊢ A → B
    exact deductionTheorem inst.h_K inst.h_S Γ'.toList A B ih'
  | Theory.Derivation.efq d => by
    -- d : Derivation Γ ⊥; [IsIntuitionistic (AxiomTheory Axioms)] recovered from constructor
    -- Use modus ponens: efq φ gives (⊥ → φ) ∈ theory, then apply to ih : ⊥ derivation
    have ih := ndToHilbert d
    have hinst : Theory.IsIntuitionistic (AxiomTheory Axioms) := inferInstance
    have hax := mem_axiomTheory.mp (hinst.efq φ)
    exact .modusPonens Γ.toList ⊥ φ (.ax Γ.toList _ hax) ih

/-- Prop-level wrapper: if `φ` is derivable in ND under `AxiomTheory Axioms` with
context `Γ`, then `Γ.toList ⊢ φ` in the Hilbert system. -/
theorem nd_to_hilbert_deriv
    {Axioms : PL.Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Ctx Atom} {φ : PL.Proposition Atom}
    (h : DerivableIn (AxiomTheory Axioms : Theory Atom) ((Γ : Ctx Atom) ⊢ φ)) :
    Deriv Axioms Γ.toList φ := by
  obtain ⟨d⟩ := h
  exact ⟨ndToHilbert d⟩

/-! ## Top-Level Equivalence -/

/-- **Generic extensional equivalence**: A formula is derivable in the Hilbert system
(from the empty context) if and only if it is derivable in natural deduction
under `AxiomTheory Axioms` (from the empty context).

This bridges the two proof systems for any axiom predicate that satisfies `MinimalAxioms`. -/
theorem hilbert_iff_nd
    {Axioms : PL.Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {φ : PL.Proposition Atom} :
    Derivable Axioms φ ↔
    DerivableIn (AxiomTheory Axioms : Theory Atom)
      ((∅ : Ctx Atom) ⊢ φ) := by
  constructor
  · intro h
    have := hilbert_to_nd_deriv h
    rwa [List.toFinset_nil] at this
  · intro h
    have hd := nd_to_hilbert_deriv h
    exact weakening_deriv hd (fun x hx => by simp [Finset.mem_toList] at hx)

/-! ## Context-Based Equivalence -/

/-- **Generic context-based extensional equivalence**: Hilbert derivability from a context
`Γ.toList` is equivalent to ND derivability from `Γ` under `AxiomTheory Axioms`.

This is the primary generic form of the equivalence, parameterized over any axiom predicate
that satisfies `MinimalAxioms`. The closed-context versions
(`hilbert_iff_nd`, `hilbert_iff_nd_min`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`) are
corollaries at `Γ = ∅`.

The forward direction uses `Finset.toList_toFinset` to bridge
`Γ.toList.toFinset = Γ`. The backward direction applies `nd_to_hilbert_deriv` directly. -/
theorem hilbert_iff_nd_ctx
    {Axioms : PL.Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv Axioms Γ.toList φ ↔
    DerivableIn (AxiomTheory Axioms : Theory Atom) (Γ ⊢ φ) := by
  constructor
  · intro h
    have := hilbert_to_nd_deriv h
    rwa [Finset.toList_toFinset] at this
  · intro h
    exact nd_to_hilbert_deriv h

/-- Minimal context-based equivalence: Hilbert derivability with `MinPropAxiom` from
context `Γ.toList` is equivalent to ND derivability under `AxiomTheory MinPropAxiom`
from context `Γ`. Typeclass resolution supplies the `MinimalAxioms` witnesses. -/
theorem hilbert_iff_nd_ctx_min {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv MinPropAxiom Γ.toList φ ↔
    DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) (Γ ⊢ φ) :=
  hilbert_iff_nd_ctx

/-- Intuitionistic context-based equivalence: Hilbert derivability with `IntPropAxiom` from
context `Γ.toList` is equivalent to ND derivability under `AxiomTheory IntPropAxiom`
from context `Γ`. Typeclass resolution supplies the `MinimalAxioms` witnesses. -/
theorem hilbert_iff_nd_ctx_int {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv IntPropAxiom Γ.toList φ ↔
    DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom) (Γ ⊢ φ) :=
  hilbert_iff_nd_ctx

/-- Classical context-based equivalence: Hilbert derivability with `PropositionalAxiom` from
context `Γ.toList` is equivalent to ND derivability under `AxiomTheory PropositionalAxiom`
from context `Γ`. Typeclass resolution supplies the `MinimalAxioms` witnesses. -/
theorem hilbert_iff_nd_ctx_cl {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv PropositionalAxiom Γ.toList φ ↔
    DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom) (Γ ⊢ φ) :=
  hilbert_iff_nd_ctx

/-! ## Corollaries -/

/-- Minimal equivalence: Hilbert derivability with `MinPropAxiom` (from empty context) is
equivalent to ND derivability under `AxiomTheory MinPropAxiom` (from empty context).

This is the minimal logic corollary of `hilbert_iff_nd_ctx_min` at `Γ = ∅`.
Typeclass resolution supplies the `MinimalAxioms` witnesses. -/
theorem hilbert_iff_nd_min {φ : PL.Proposition Atom} :
    Derivable MinPropAxiom φ ↔
    DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom)
      ((∅ : Ctx Atom) ⊢ φ) :=
  hilbert_iff_nd

/-- Intuitionistic equivalence: Hilbert derivability with `IntPropAxiom` is equivalent
to ND derivability under `AxiomTheory IntPropAxiom`.
Typeclass resolution supplies the `MinimalAxioms` witnesses. -/
theorem hilbert_iff_nd_int {φ : PL.Proposition Atom} :
    Derivable IntPropAxiom φ ↔
    DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom)
      ((∅ : Ctx Atom) ⊢ φ) :=
  hilbert_iff_nd

/-- Classical equivalence: Hilbert derivability with `PropositionalAxiom` is equivalent
to ND derivability under `AxiomTheory PropositionalAxiom`.
Typeclass resolution supplies the `MinimalAxioms` witnesses. -/
theorem hilbert_iff_nd_cl {φ : PL.Proposition Atom} :
    Derivable PropositionalAxiom φ ↔
    DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom)
      ((∅ : Ctx Atom) ⊢ φ) :=
  hilbert_iff_nd

end Cslib.Logic.PL
