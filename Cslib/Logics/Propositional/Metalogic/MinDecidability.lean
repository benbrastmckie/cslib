/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Metalogic.MinStrongCompleteness
public import Cslib.Logics.Propositional.Subformula
public import Mathlib.Data.Finset.Powerset

/-! # Finite Model Property and Decidability for Minimal Propositional Logic

This module establishes sorry-free decidability of `Derivable MinPropAxiom φ` via the
finite model property (FMP). The key insight is a direct finite canonical Kripke model
construction: worlds are `Σ`-bounded prime MinTheory worlds where `Σ := φ.subformulas`.

## Main Results

- `MinFinWorld φ`: The type of `Σ`-bounded prime minimal worlds.
- `instFintypeMinFinWorld`: `MinFinWorld φ` is a `Fintype` (worlds embed injectively into
  the finite powerset `2^Σ`).
- `min_fin_imp_witness`: Finite Lindenbaum implication witness, constructed by lifting to
  the infinite canonical model and restricting back to `Σ`.
- `min_fin_truth_lemma`: Truth lemma for the finite canonical model.
- `min_fmp`: `Derivable MinPropAxiom φ ↔ ∀ w : MinFinWorld φ, φ ∈ w.carrier`.
- `decidableDerivableMinPropAxiomFMP`: A sorry-free `noncomputable def` (not a registered
  instance) for `Derivable MinPropAxiom φ` via the FMP, independent of any tableau completeness
  witnesses. The canonical registered `Decidable` instance is in
  `Tableau/Minimal/DecisionProcedure.lean` (`instDecidableDerivableMinPropAxiom`).

## Design Decisions

- The `closed` field references `SetDerivable` (a Prop over unbounded derivations). To keep
  `Fintype` we do NOT decide `SetDerivable`; instead, worlds embed injectively into the
  finite powerset via the carrier map.
- The finite Lindenbaum witness uses the **infinite** canonical model: lift to an infinite
  prime MinTheory via `min_imp_witness` + `min_prime_exclusion`, then restrict back to `Σ`.
  This avoids Zorn's lemma for finite models entirely.
- Unlike the intuitionistic version, `MinFinWorld` has **no consistency field**: MinTheory
  worlds may contain `⊥`, so `minFinBotForces w := (⊥ ∈ w.carrier)` is a genuine predicate.

## Two Decision Routes — Distinct Roles

CSLib contains **two independent decision procedures** for `Derivable MinPropAxiom φ`:

### Route 1 (FMP — this module)
- **Module**: `Metalogic/MinDecidability.lean`
- **Mechanism**: Finite model property via a `Σ`-bounded finite canonical Kripke model
  (`MinFinWorld φ`). Decides by checking `∀ w : MinFinWorld φ, φ ∈ w.carrier`.
- **Axiom profile**: `{propext, Classical.choice, Quot.sound}` — **sorry-free**.
- **Exposed as**: `decidableDerivableMinPropAxiomFMP` (`noncomputable def`, not a registered
  instance). Also see `min_fmp` (the FMP biconditional) and `min_fin_truth_lemma`.
- **Role**: Independent theoretical result; the FMP route does not use tableaux or
  branch-saturation. Useful as a correctness witness for the tableau approach.
- **Companion**: `decidableDerivableIntPropAxiomFMP` in `Metalogic/IntDecidability.lean`.
- **Note**: Unlike the intuitionistic FMP, `MinFinWorld` has no consistency field: `⊥` may
  hold in a minimal world, so `minFinBotForces w := (⊥ ∈ w.carrier)` is a genuine predicate.

### Route 2 (Tableau — canonical registered instance)
- **Module**: `Tableau/Minimal/DecisionProcedure.lean`
- **Mechanism**: Constructive signed-tableau proof-search with countermodel extraction.
  Decides via `instDecidableMValid` composed with `min_soundness_completeness`.
- **Axiom profile**: `{propext, Classical.choice, Quot.sound}` — **sorry-free**. The completeness
  chain this route rests on (`openBranch_countermodel`'s existential in `Scheme.lean` and
  `minimalTableau_complete` in `Minimal/Completeness.lean`) is fully discharged. (Minimal reuses
  the shared parametric `truthLemma minScheme` from `Scheme.lean`, likewise sorry-free.)
- **Exposed as**: `instDecidableDerivableMinPropAxiom` (the **sole registered `Decidable`
  instance** for `Derivable MinPropAxiom φ`).
- **Role**: Canonical extension-facing instance for minimal propositional logic.

The two routes have **disjoint carrier types** (`MinFinWorld` vs signed-branch world machinery)
and independent proof lineages. Factoring a common truth-lemma abstraction is explicitly
deferred (high risk, low payoff while 317 is open). See `min_fin_truth_lemma` vs the
parametric `truthLemma` in `Tableau/Intuitionistic/Scheme.lean` for the parallel statements.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

universe u

variable {Atom : Type u} [DecidableEq Atom]

attribute [local instance] Classical.propDecidable

/-! ## Σ-Bounded Finite World Type -/

/-- A `Σ`-bounded prime minimal world, where `Σ := φ.subformulas`.

Fields:
- `carrier`: a finset of formulas from `Σ`
- `sub`: carrier ⊆ Σ
- `closed`: deductively closed within Σ — if ψ is Min-derivable from the carrier and ψ ∈ Σ,
  then ψ ∈ carrier
- `prime`: the disjunction property within Σ

Unlike `IntFinWorld`, there is no `consistent` field: MinTheory worlds may contain `⊥`,
so bot-forcing is a genuine predicate (`minFinBotForces`). Two worlds with the same carrier
are equal by propext; this makes the carrier map injective and enables the `Fintype` instance
via `Fintype.ofInjective`. -/
structure MinFinWorld (φ : PL.Proposition Atom) where
  /-- The world's carrier: a finset of Σ-subformulas. -/
  carrier : Finset (PL.Proposition Atom)
  /-- The carrier is a subset of the subformulas of φ. -/
  sub : carrier ⊆ φ.subformulas
  /-- Deductive closure within Σ: if ψ is Min-derivable from the carrier and ψ ∈ Σ,
  then ψ ∈ carrier. -/
  closed : ∀ ψ ∈ φ.subformulas,
      SetDerivable MinPropAxiom (↑carrier : Set (PL.Proposition Atom)) ψ → ψ ∈ carrier
  /-- Primality: the disjunction property. -/
  prime : ∀ a b : PL.Proposition Atom, (.or a b) ∈ carrier → a ∈ carrier ∨ b ∈ carrier

/-! ## Extensionality -/

/-- Two `MinFinWorld` structures with the same carrier are equal.

All fields other than `carrier` are Props, hence equal by propositional extensionality. -/
theorem MinFinWorld.ext {φ : PL.Proposition Atom} {w₁ w₂ : MinFinWorld φ}
    (h : w₁.carrier = w₂.carrier) : w₁ = w₂ := by
  cases w₁; cases w₂; congr

/-! ## Preorder -/

/-- The preorder on `MinFinWorld φ` is carrier inclusion. -/
instance instPreorderMinFinWorld (φ : PL.Proposition Atom) :
    Preorder (MinFinWorld φ) where
  le w₁ w₂ := w₁.carrier ⊆ w₂.carrier
  le_refl w := Finset.Subset.refl w.carrier
  le_trans _ _ _ h₁₂ h₂₃ := Finset.Subset.trans h₁₂ h₂₃

/-! ## Fintype Instance -/

/-- The carrier map `MinFinWorld φ → ↑(φ.subformulas.powerset)` is injective. -/
theorem minFinWorld_carrier_injective (φ : PL.Proposition Atom) :
    Function.Injective
      (fun w : MinFinWorld φ =>
        (⟨w.carrier, Finset.mem_powerset.mpr w.sub⟩ :
          ↑(φ.subformulas.powerset))) :=
  fun _ _ h => MinFinWorld.ext (congrArg Subtype.val h)

/-- `MinFinWorld φ` is a `Fintype`: worlds embed injectively into the finite powerset `2^Σ`.

The powerset `φ.subformulas.powerset : Finset (Finset _)` has a canonical `Fintype` for its
subtype, and the carrier map is injective (by `MinFinWorld.ext`). No decidability of
`SetDerivable` is required. -/
noncomputable instance instFintypeMinFinWorld (φ : PL.Proposition Atom) :
    Fintype (MinFinWorld φ) :=
  Fintype.ofInjective _ (minFinWorld_carrier_injective φ)

/-! ## Finite Canonical Valuation -/

/-- The canonical valuation for `MinFinWorld φ`: atom `p` is true at world `w` iff
`Proposition.atom p ∈ w.carrier`. -/
def minFinVal {φ : PL.Proposition Atom} (w : MinFinWorld φ) (p : Atom) : Prop :=
  (.atom p) ∈ w.carrier

/-- The finite canonical valuation is upward-closed with respect to the carrier inclusion
preorder. -/
theorem minFinVal_upward_closed {φ : PL.Proposition Atom}
    {w w' : MinFinWorld φ} (p : Atom) (hw : w ≤ w') (hv : minFinVal w p) :
    minFinVal w' p :=
  hw hv

/-! ## Finite Bot Forces -/

/-- The bot-forcing predicate for `MinFinWorld φ`: `⊥` is forced at world `w` iff
`⊥ ∈ w.carrier`.

This mirrors `minBotForces` for the infinite canonical model (`MinStrongCompleteness`).
Unlike the intuitionistic case (where `bot_forces = fun _ => False`), minimal worlds may
contain `⊥`, so this predicate is genuinely non-trivial. -/
def minFinBotForces {φ : PL.Proposition Atom} (w : MinFinWorld φ) : Prop :=
  (⊥ : PL.Proposition Atom) ∈ w.carrier

/-- The finite bot-forcing predicate is upward-closed with respect to the carrier inclusion
preorder. -/
theorem minFinBotForces_upward_closed {φ : PL.Proposition Atom}
    {w w' : MinFinWorld φ} (hw : w ≤ w') (hbf : minFinBotForces w) :
    minFinBotForces w' :=
  hw hbf

/-! ## Finite Implication Witness -/

/-- **Finite Implication Witness**.

Given a world `w : MinFinWorld φ` with `ψ → χ ∈ φ.subformulas` but `ψ → χ ∉ w.carrier`,
there exists `w' : MinFinWorld φ` with `w ≤ w'`, `ψ ∈ w'.carrier`, `χ ∉ w'.carrier`.

**Proof strategy** (via the infinite canonical model):
1. From `w.closed`: `¬ SetDerivable MinPropAxiom ↑w.carrier (ψ → χ)`.
2. The deductive closure of `↑w.carrier` is a MinTheory (no consistency requirement needed).
3. `min_imp_witness` gives a MinTheory T ⊇ DC(w) with ψ ∈ T, χ ∉ T.
4. `min_prime_exclusion` gives a prime MinTheory T'' ⊇ T with χ ∉ T''.
5. Restrict T'' to Σ: `w'.carrier := {ξ ∈ φ.subformulas | ξ ∈ T''}`.
6. Verify w' satisfies all `MinFinWorld` conditions and w ≤ w', ψ ∈ w'.carrier, χ ∉ w'.carrier.

This sidesteps Zorn's lemma for finite models. -/
theorem min_fin_imp_witness {φ : PL.Proposition Atom}
    (w : MinFinWorld φ) {ψ χ : PL.Proposition Atom}
    (hmem : (.imp ψ χ) ∈ φ.subformulas)
    (hnot : (.imp ψ χ) ∉ w.carrier) :
    ∃ w' : MinFinWorld φ, w ≤ w' ∧ ψ ∈ w'.carrier ∧ χ ∉ w'.carrier := by
  -- Step 1: ψ → χ is not derivable from w.carrier
  have h_not_sd : ¬ SetDerivable MinPropAxiom (↑w.carrier : Set (PL.Proposition Atom)) (ψ.imp χ) :=
    fun h_sd => hnot (w.closed (ψ.imp χ) hmem h_sd)
  -- Step 2: Form the MinTheory from the deductive closure (no consistency required)
  have h_theory : MinTheory (minDeductiveClosure (↑w.carrier : Set (PL.Proposition Atom))) :=
    minDeductiveClosure_is_theory _
  -- Step 3: ψ → χ ∉ minDeductiveClosure ↑w.carrier (= SetDerivable condition)
  have h_not_dc : (ψ.imp χ) ∉ minDeductiveClosure (↑w.carrier : Set (PL.Proposition Atom)) :=
    h_not_sd
  -- Step 4: Apply min_imp_witness to get T ⊇ DC(w) with ψ ∈ T, χ ∉ T
  obtain ⟨T, hDCT, hT_theory, hψT, hχT⟩ := min_imp_witness h_theory h_not_dc
  -- Step 5: Apply min_prime_exclusion to get prime T'' ⊇ T with χ ∉ T''
  obtain ⟨T'', hTT'', hT''_prime, hχT''⟩ := min_prime_exclusion hT_theory hχT
  -- Step 6: Restrict T'' to Σ = φ.subformulas
  let carrier' : Finset (PL.Proposition Atom) :=
    φ.subformulas.filter (fun ξ => ξ ∈ T'')
  have sub' : carrier' ⊆ φ.subformulas := Finset.filter_subset _ _
  have h_sub_set : (↑carrier' : Set _) ⊆ (T'' : Set _) := by
    intro ξ hξ
    have := Finset.mem_coe.mp hξ
    simp only [carrier', Finset.mem_filter] at this
    exact this.2
  have closed' : ∀ ψ' ∈ φ.subformulas,
      SetDerivable MinPropAxiom (↑carrier' : Set _) ψ' → ψ' ∈ carrier' := by
    intro ψ' hψ'mem h_sd'
    simp only [carrier', Finset.mem_filter]
    refine ⟨hψ'mem, ?_⟩
    obtain ⟨L, hLsub, hLderiv⟩ := SetDerivable_weakening h_sub_set h_sd'
    exact hT''_prime.1 L ψ' hLsub hLderiv
  have prime' : ∀ a b : PL.Proposition Atom,
      (.or a b) ∈ carrier' → a ∈ carrier' ∨ b ∈ carrier' := by
    intro a b hab
    simp only [carrier', Finset.mem_filter] at hab ⊢
    rcases hT''_prime.2 a b hab.2 with ha | hb
    · exact Or.inl ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hab.1, ha⟩
    · exact Or.inr ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.or_right hab.1, hb⟩
  let w' : MinFinWorld φ := ⟨carrier', sub', closed', prime'⟩
  -- Step 7: w ≤ w' (w.carrier ⊆ carrier')
  have h_le : w ≤ w' := fun ξ hξ => by
    simp only [w', carrier', Finset.mem_filter]
    exact ⟨w.sub hξ, hTT'' (hDCT (min_subset_deductive_closure _ (by exact_mod_cast hξ)))⟩
  -- Step 8: ψ ∈ w'.carrier
  have hψ : ψ ∈ w'.carrier := by
    simp only [w', carrier', Finset.mem_filter]
    exact ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.imp_left hmem,
           hTT'' hψT⟩
  -- Step 9: χ ∉ w'.carrier
  have hχ : χ ∉ w'.carrier := by
    simp only [w', carrier', Finset.mem_filter, not_and]
    intro _; exact hχT''
  exact ⟨w', h_le, hψ, hχ⟩

/-! ## Finite Truth Lemma -/

/-- **Finite Truth Lemma (FMP route)**: For any `w : MinFinWorld φ` and formula
`ψ ∈ φ.subformulas`, `IForces minFinVal minFinBotForces w ψ ↔ ψ ∈ w.carrier`.

Proof by structural induction on `ψ` with `w` fixed:
- **atom**: `IForces ... w (.atom p) = minFinVal w p = (.atom p) ∈ w.carrier`. `Iff.rfl`.
- **bot**: `IForces ... w ⊥ = minFinBotForces w = (⊥ ∈ w.carrier)`. `Iff.rfl`.
- **imp**: backward direction uses `min_fin_imp_witness`; forward direction uses the `closed`
  field with modus ponens.
- **and**, **or**: direct from IHs + deductive closure field / primality field.

**Infrastructure relationship** (factoring deferred):
This lemma is the Minimal FMP analogue of the parametric `truthLemma S b …` in
`Tableau/Intuitionistic/Scheme.lean` (declaration `truthLemma`, also used by the minimal
tableau via `truthLemma minScheme`). Both prove "forcing ↔ membership" statements, but over
**disjoint carrier types**:
- `min_fin_truth_lemma`: world type `MinFinWorld φ` (Finset-carrier `Σ`-bounded prime
  MinTheory worlds, resting on the minimal Lindenbaum substrate: `min_imp_witness`,
  `min_prime_exclusion`). Unlike the intuitionistic FMP, `⊥` may be forced at some worlds
  (`minFinBotForces w := (⊥ ∈ w.carrier)`). Carrier is a `Finset (Proposition Atom)`.
  **Sorry-free.**
- `truthLemma minScheme`: world type `Nat` (tableau branch labels). `modelBot` is the
  minimal-closure predicate applied to branch labels. **Sorry-free** (takes an explicit
  `hpers` positive-persistence hypothesis).

Factoring a common truth-lemma or world-type abstraction is **explicitly deferred**: the
carriers remain structurally incompatible regardless of either lemma's sorry status, and the
payoff is low. This is unrelated to completeness: both `truthLemma` and
`openBranch_countermodel` (`Tableau/Intuitionistic/Scheme.lean`) are sorry-free and
axiom-clean; nothing in this dependency chain remains open.
Cross-reference: `int_fin_truth_lemma` for the analogous intuitionistic FMP lemma. -/
theorem min_fin_truth_lemma {φ : PL.Proposition Atom}
    (w : MinFinWorld φ) :
    ∀ {ψ : PL.Proposition Atom}, ψ ∈ φ.subformulas →
    (IForces minFinVal minFinBotForces w ψ ↔ ψ ∈ w.carrier) := by
  intro ψ hψ
  cases ψ with
  | atom p => exact Iff.rfl
  | bot => exact Iff.rfl
  | imp a b =>
    have ha_sub : a ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.imp_left hψ
    have hb_sub : b ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.imp_right hψ
    constructor
    · -- Forward: IForces ... w (a → b) → (a → b) ∈ w.carrier
      intro h_forces
      by_contra h_not_mem
      obtain ⟨v, hle, ha_v, hb_v⟩ := min_fin_imp_witness w hψ h_not_mem
      have hfa := (min_fin_truth_lemma v ha_sub).mpr ha_v
      exact hb_v ((min_fin_truth_lemma v hb_sub).mp (h_forces v hle hfa))
    · -- Backward: (a → b) ∈ w.carrier → IForces ... w (a → b)
      intro h_mem v hle hfa
      have ha_v := (min_fin_truth_lemma v ha_sub).mp hfa
      have hab_v := hle h_mem
      have hb_v := v.closed b hb_sub
        (SetDerivable_mp
          (SetDerivable_of_mem (Finset.mem_coe.mpr hab_v))
          (SetDerivable_of_mem (Finset.mem_coe.mpr ha_v)))
      exact (min_fin_truth_lemma v hb_sub).mpr hb_v
  | and a b =>
    have ha_sub : a ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.and_left hψ
    have hb_sub : b ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.and_right hψ
    constructor
    · -- Forward: IForces ... w (a ∧ b) → (a ∧ b) ∈ w.carrier
      intro ⟨hfa, hfb⟩
      have ha_mem := (min_fin_truth_lemma w ha_sub).mp hfa
      have hb_mem := (min_fin_truth_lemma w hb_sub).mp hfb
      apply w.closed (a.and b) hψ
      exact SetDerivable_mp
        (SetDerivable_mp
          (SetDerivable_of_Derivable ⟨.ax [] _ (MinPropAxiom.andI a b)⟩ (↑w.carrier))
          (SetDerivable_of_mem (Finset.mem_coe.mpr ha_mem)))
        (SetDerivable_of_mem (Finset.mem_coe.mpr hb_mem))
    · -- Backward: (a ∧ b) ∈ w.carrier → IForces ... w (a ∧ b)
      intro h_mem
      exact ⟨(min_fin_truth_lemma w ha_sub).mpr
          (w.closed a ha_sub
            (SetDerivable_mp
              (SetDerivable_of_Derivable ⟨.ax [] _ (MinPropAxiom.andE1 a b)⟩ (↑w.carrier))
              (SetDerivable_of_mem (Finset.mem_coe.mpr h_mem)))),
        (min_fin_truth_lemma w hb_sub).mpr
          (w.closed b hb_sub
            (SetDerivable_mp
              (SetDerivable_of_Derivable ⟨.ax [] _ (MinPropAxiom.andE2 a b)⟩ (↑w.carrier))
              (SetDerivable_of_mem (Finset.mem_coe.mpr h_mem))))⟩
  | or a b =>
    have ha_sub : a ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hψ
    have hb_sub : b ∈ φ.subformulas :=
      Proposition.IsSubformula.trans Proposition.IsSubformula.or_right hψ
    constructor
    · -- Forward: IForces ... w (a ∨ b) → (a ∨ b) ∈ w.carrier
      intro h_or
      rcases h_or with hfa | hfb
      · exact w.closed (a.or b) hψ
          (SetDerivable_mp
            (SetDerivable_of_Derivable ⟨.ax [] _ (MinPropAxiom.orI1 a b)⟩ (↑w.carrier))
            (SetDerivable_of_mem (Finset.mem_coe.mpr ((min_fin_truth_lemma w ha_sub).mp hfa))))
      · exact w.closed (a.or b) hψ
          (SetDerivable_mp
            (SetDerivable_of_Derivable ⟨.ax [] _ (MinPropAxiom.orI2 a b)⟩ (↑w.carrier))
            (SetDerivable_of_mem (Finset.mem_coe.mpr ((min_fin_truth_lemma w hb_sub).mp hfb))))
    · -- Backward: (a ∨ b) ∈ w.carrier → IForces ... w (a ∨ b)
      intro h_mem
      rcases w.prime a b h_mem with ha | hb
      · exact Or.inl ((min_fin_truth_lemma w ha_sub).mpr ha)
      · exact Or.inr ((min_fin_truth_lemma w hb_sub).mpr hb)

/-! ## Finite Model Property -/

/-- Helper: the set `{ξ ∈ φ.subformulas | ξ ∈ T}` forms a `MinFinWorld φ` when
`T` is a prime MinTheory. -/
private noncomputable def minFinWorldOfPrimeTheory {φ : PL.Proposition Atom}
    {T : Set (PL.Proposition Atom)} (hT : MinPrimeTheory T) : MinFinWorld φ where
  carrier := φ.subformulas.filter (fun ξ => ξ ∈ T)
  sub := Finset.filter_subset _ _
  closed ψ' hψ'mem h_sd' := by
    simp only [Finset.mem_filter]
    refine ⟨hψ'mem, ?_⟩
    have h_sub_set : (↑(φ.subformulas.filter (fun ξ => ξ ∈ T)) : Set _) ⊆ T := by
      intro ξ hξ
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hξ
      exact hξ.2
    obtain ⟨L, hLsub, hLderiv⟩ := SetDerivable_weakening h_sub_set h_sd'
    exact hT.1 L ψ' hLsub hLderiv
  prime a b hab := by
    simp only [Finset.mem_filter] at hab ⊢
    rcases hT.2 a b hab.2 with ha | hb
    · exact Or.inl ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hab.1, ha⟩
    · exact Or.inr ⟨Proposition.IsSubformula.trans Proposition.IsSubformula.or_right hab.1, hb⟩

/-- **Finite Model Property for Minimal Propositional Logic**:
`φ` is derivable iff `φ` is in the carrier of every `Σ`-bounded prime minimal world.

- **(→) Soundness**: Any derivable formula is valid in every Min Kripke model; the finite
  canonical model (`MinFinWorld φ`) is a valid Min model.
- **(←) Completeness**: If `φ` is not derivable, we construct a countermodel in `MinFinWorld φ`
  using the prime exclusion lemma to build a prime MinTheory omitting `φ`, then restrict to Σ. -/
theorem min_fmp (φ : PL.Proposition Atom) :
    Derivable MinPropAxiom φ ↔ ∀ w : MinFinWorld φ, φ ∈ w.carrier := by
  constructor
  · -- Forward: soundness
    intro h w
    rw [← min_fin_truth_lemma w (Proposition.self_mem_subformulas φ)]
    exact min_soundness_derivable h (MinFinWorld φ) minFinVal minFinBotForces
      minFinVal_upward_closed minFinBotForces_upward_closed w
  · -- Backward: contrapositive; build a counterworld when φ is not derivable
    intro h_all
    by_contra h_not
    -- φ ∉ minDeductiveClosure ∅
    have h_not_mem : φ ∉ minDeductiveClosure ∅ := by
      rw [minDeductiveClosure_iff_SetDerivable, SetDerivable_empty_iff]
      exact h_not
    -- Build a prime MinPrimeTheory T with φ ∉ T
    obtain ⟨T, _, hT_prime, hφT⟩ :=
      min_prime_exclusion (minDeductiveClosure_is_theory ∅) h_not_mem
    -- The finite world built from T omits φ
    have hφ : φ ∉ (minFinWorldOfPrimeTheory hT_prime (φ := φ)).carrier := by
      simp only [minFinWorldOfPrimeTheory, Finset.mem_filter, not_and]
      intro _; exact hφT
    exact hφ (h_all (minFinWorldOfPrimeTheory hT_prime))

/-! ## Decidability Instance -/

/-- **Sorry-free `Decidable` decision procedure for `Derivable MinPropAxiom φ`** via the
finite model property (FMP route).

The decision procedure checks `∀ w : MinFinWorld φ, φ ∈ w.carrier` by enumerating all
worlds in the finite type `MinFinWorld φ` (which is a `Fintype` via `instFintypeMinFinWorld`).
This definition is independent of any tableau completeness witnesses and carries no `sorryAx`
(axiom profile: `{propext, Classical.choice, Quot.sound}`).

This is a **named `noncomputable def`**, not a registered `instance`. The canonical registered
`Decidable` instance for `Derivable MinPropAxiom φ` is `instDecidableDerivableMinPropAxiom` in
`Tableau/Minimal/DecisionProcedure.lean` (tableau route). See also
`decidableDerivableIntPropAxiomFMP` in `Metalogic/IntDecidability.lean` for the analogous Int
FMP decision procedure. -/
noncomputable def decidableDerivableMinPropAxiomFMP (φ : PL.Proposition Atom) :
    Decidable (Derivable MinPropAxiom φ) :=
  decidable_of_iff (∀ w : MinFinWorld φ, φ ∈ w.carrier) (min_fmp φ).symm

end Cslib.Logic.PL

end
