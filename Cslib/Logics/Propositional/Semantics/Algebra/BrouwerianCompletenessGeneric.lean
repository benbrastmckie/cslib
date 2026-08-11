/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module


public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianBot
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates

/-! # Generic Brouwerian Completeness over `ConjImpAxioms`

This module provides the shared completeness machinery for all three Brouwerian fragment tiers:
`ConjImpAxiom` (Brouwerian), `ConjImpBotAxiom` (pointed Brouwerian), and `ConjImpBotMinAxiom`
(free-bot Brouwerian). All three tiers are instances of `ConjImpAxioms` (the 5-field
conj-imp typeclass), so the Lindenbaum quotient, truth lemma, and completeness theorem can be
stated and proved once, with each tier recovered as a corollary.

## Proof Strategy

**Soundness schema lemmas** (5 lemmas, one per `ConjImpAxioms` witness): These capture the
shared soundness argument for implyK, implyS, andI, andE1, andE2.  Per-tier soundness is a
`cases` dispatch onto these plus any tier-specific axioms (e.g., efq for the pointed tier).

**Truth lemma** (`brouwerianBotCanonicalV_spec`): For any `[ConjImpAxioms Axioms]` system,
`BrouwerianBotEvaluate (canonicalV Axioms) (canonicalBotVal Axioms) A = hilbertLindenbaumMk A`
when `A` is `IsOrFree`.  The proof is structural induction using the generic Lindenbaum simp
lemmas `hilbertLindenbaumMk_himp` and `hilbertLindenbaumMk_inf`.

**Generic completeness** (`brouwerianBot_completeness`): Instantiate `BrouwerianBotValid` at the
Lindenbaum algebra, rewrite with the truth lemma, then close with `hilbertLindenbaumMk_eq_top_iff`.

**Brouwerian-tier truth lemma** (`brouwerianCanonicalV_spec_generic`): For `IsOrBotFree`
formulas, `BrouwerianEvaluate (canonicalV Axioms) A = hilbertLindenbaumMk A`. Used to recover
`conjImp_brouwerian_completeness` from `BrouwerianValid`.

## Main Results

- `brouwerianBot_implyK_sound` / `implyS_sound` / `andI_sound` / `andE1_sound` / `andE2_sound`:
  the 5 shared soundness schema lemmas.
- `brouwerianBotCanonicalV_spec`: generic truth lemma for `IsOrFree` formulas.
- `brouwerianCanonicalV_spec_generic`: truth lemma for `BrouwerianEvaluate` on
  `IsOrBotFree` formulas.
- `brouwerianBot_soundness_tree`: generic derivation-tree soundness (parametric over axiom-sound).
- `brouwerianBot_soundness_derivable`: generic derivable-level soundness.
- `brouwerianBot_completeness`: generic completeness for `IsOrFree` formulas.

## References

* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

noncomputable section

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type*}

/-! ## Soundness Schema Lemmas (5 shared axiom cases) -/

/-- The implyK schema `φ → (ψ → φ)` evaluates to `⊤` in any Brouwerian semilattice under any
valuation and any `bot_val`. -/
theorem brouwerianBot_implyK_sound {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) (φ ψ : PL.Proposition Atom) :
    BrouwerianBotEvaluate v bot_val (φ.imp (ψ.imp φ)) = ⊤ := by
  simp only [BrouwerianBotEvaluate_imp]
  rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff]
  exact inf_le_left

/-- The implyS schema `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` evaluates to `⊤` in any
Brouwerian semilattice under any valuation and any `bot_val`. -/
theorem brouwerianBot_implyS_sound {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) (φ ψ χ : PL.Proposition Atom) :
    BrouwerianBotEvaluate v bot_val
      ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) = ⊤ := by
  simp only [BrouwerianBotEvaluate_imp]
  rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff,
      BrouwerianSemilattice.le_himp_iff]
  have hb : (BrouwerianBotEvaluate v bot_val φ ⇨ BrouwerianBotEvaluate v bot_val ψ ⇨
              BrouwerianBotEvaluate v bot_val χ) ⊓
            (BrouwerianBotEvaluate v bot_val φ ⇨ BrouwerianBotEvaluate v bot_val ψ) ⊓
            BrouwerianBotEvaluate v bot_val φ ≤ BrouwerianBotEvaluate v bot_val ψ :=
    (inf_le_inf_right _ inf_le_right).trans BrouwerianSemilattice.himp_inf_le
  have hbc : (BrouwerianBotEvaluate v bot_val φ ⇨ BrouwerianBotEvaluate v bot_val ψ ⇨
               BrouwerianBotEvaluate v bot_val χ) ⊓
             (BrouwerianBotEvaluate v bot_val φ ⇨ BrouwerianBotEvaluate v bot_val ψ) ⊓
             BrouwerianBotEvaluate v bot_val φ ≤
             BrouwerianBotEvaluate v bot_val ψ ⇨ BrouwerianBotEvaluate v bot_val χ :=
    (inf_le_inf_right _ inf_le_left).trans BrouwerianSemilattice.himp_inf_le
  exact (le_inf hbc hb).trans BrouwerianSemilattice.himp_inf_le

/-- The andI schema `φ → (ψ → φ ∧ ψ)` evaluates to `⊤` in any Brouwerian semilattice under
any valuation and any `bot_val`. -/
theorem brouwerianBot_andI_sound {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) (φ ψ : PL.Proposition Atom) :
    BrouwerianBotEvaluate v bot_val (φ.imp (ψ.imp (φ.and ψ))) = ⊤ := by
  simp only [BrouwerianBotEvaluate_imp, BrouwerianBotEvaluate_and]
  rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff]

/-- The andE1 schema `(φ ∧ ψ) → φ` evaluates to `⊤` in any Brouwerian semilattice under any
valuation and any `bot_val`. -/
theorem brouwerianBot_andE1_sound {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) (φ ψ : PL.Proposition Atom) :
    BrouwerianBotEvaluate v bot_val ((φ.and ψ).imp φ) = ⊤ := by
  simp only [BrouwerianBotEvaluate_imp, BrouwerianBotEvaluate_and]
  rw [BrouwerianSemilattice.himp_eq_top_iff]
  exact inf_le_left

/-- The andE2 schema `(φ ∧ ψ) → ψ` evaluates to `⊤` in any Brouwerian semilattice under any
valuation and any `bot_val`. -/
theorem brouwerianBot_andE2_sound {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) (φ ψ : PL.Proposition Atom) :
    BrouwerianBotEvaluate v bot_val ((φ.and ψ).imp ψ) = ⊤ := by
  simp only [BrouwerianBotEvaluate_imp, BrouwerianBotEvaluate_and]
  rw [BrouwerianSemilattice.himp_eq_top_iff]
  exact inf_le_right

/-! ## Generic Derivation-Tree Soundness -/

/-- **Generic derivation-tree soundness**: if every axiom in `Axioms` evaluates to `⊤` under
the current semilattice `H`, valuation `v`, and bottom element `bot_val`, and every formula in
the context evaluates to `⊤`, then the conclusion evaluates to `⊤`.

This is the monomorphic inner lemma: `h_ax_sound` is specialized to the current `H`, `v`,
`bot_val` to avoid universe-polymorphism issues when passing `BrouwerianBotValid` through a
local hypothesis. Per-tier soundness wraps this by introducing `H`, `v`, `bot_val` first. -/
private theorem brouwerianBot_soundness_tree
    {Axioms : PL.Proposition Atom → Prop}
    {H : Type*} [BrouwerianSemilattice H]
    {v : Atom → H} {bot_val : H}
    (h_ax_sound : ∀ ψ, Axioms ψ → BrouwerianBotEvaluate v bot_val ψ = ⊤)
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ φ)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BrouwerianBotEvaluate v bot_val ψ = ⊤) :
    BrouwerianBotEvaluate v bot_val φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact h_ax_sound ψ h_ax
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modusPonens _ ψ χ d₁ d₂ =>
    have h1 := brouwerianBot_soundness_tree h_ax_sound d₁ h_ctx
    have h2 := brouwerianBot_soundness_tree h_ax_sound d₂ h_ctx
    simp only [← Proposition.imp_def, BrouwerianBotEvaluate_imp] at h1
    rw [BrouwerianSemilattice.himp_eq_top_iff] at h1
    rw [h2, top_le_iff] at h1
    exact h1
  | .weakening _ _ ψ d' h_sub =>
    exact brouwerianBot_soundness_tree h_ax_sound d'
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Generic derivable-level soundness**: if every axiom is `BrouwerianBotValid.{u, u}`, then
so is every derivable formula.

The explicit universe annotation `.{u, u}` avoids Lean 4 universe-metavariable mismatches that
arise when `BrouwerianBotValid` is passed through a local hypothesis with a fixed universe and
then applied to an introduced `H` at a different universe level. This follows the pattern of
`conjImpBotMin_brouwerianBot_soundness_derivable` in `MplPointedConservative.lean`. -/
theorem brouwerianBot_soundness_derivable {Atom : Type u}
    {Axioms : PL.Proposition Atom → Prop}
    (h_ax_sound : ∀ ψ, Axioms ψ → BrouwerianBotValid.{u, u} ψ)
    {φ : PL.Proposition Atom}
    (h : Derivable Axioms φ) : BrouwerianBotValid.{u, u} φ := by
  intro H _ v bot_val
  obtain ⟨d⟩ := h
  exact brouwerianBot_soundness_tree (fun ψ hψ => h_ax_sound ψ hψ H v bot_val) d
    (fun _ h => nomatch h)

/-! ## Generic Truth Lemma -/

/-- **Generic truth lemma** (for `IsOrFree` formulas): evaluating an or-free proposition under
the canonical valuation and canonical bottom value gives exactly its Lindenbaum quotient class.

`BrouwerianBotEvaluate (canonicalV Axioms) (canonicalBotVal Axioms) A = hilbertLindenbaumMk A`

The `bot` case works because `canonicalBotVal Axioms = hilbertLindenbaumMk .bot` by definition.
The `or` case is excluded by `IsOrFree`. -/
theorem brouwerianBotCanonicalV_spec
    {Axioms : PL.Proposition Atom → Prop} [ConjImpAxioms Axioms]
    (A : PL.Proposition Atom) (hA : A.IsOrFree = true) :
    BrouwerianBotEvaluate (canonicalV Axioms) (canonicalBotVal Axioms) A =
    hilbertLindenbaumMk (Axioms := Axioms) A := by
  induction A with
  | atom x => rfl
  | bot => rfl
  | imp a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hA
    simp only [BrouwerianBotEvaluate_imp, iha hA.1, ihb hA.2, hilbertLindenbaumMk_himp]
  | and a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hA
    simp only [BrouwerianBotEvaluate_and, iha hA.1, ihb hA.2, hilbertLindenbaumMk_inf]
  | or _ _ _ _ => simp [Proposition.IsOrFree] at hA

/-- **Truth lemma for `BrouwerianEvaluate`** (for `IsOrBotFree` formulas): evaluating an
or-bot-free proposition under the canonical valuation gives exactly its Lindenbaum quotient class.

`BrouwerianEvaluate (canonicalV Axioms) A = hilbertLindenbaumMk A`

This is the counterpart of `brouwerianBotCanonicalV_spec` for the evaluator with `bot ↦ ⊤`
and `IsOrBotFree` guard (which excludes both `bot` and `or`). -/
theorem brouwerianCanonicalV_spec_generic
    {Axioms : PL.Proposition Atom → Prop} [ConjImpAxioms Axioms]
    (A : PL.Proposition Atom) (hA : A.IsOrBotFree = true) :
    BrouwerianEvaluate (canonicalV Axioms) A =
    hilbertLindenbaumMk (Axioms := Axioms) A := by
  induction A with
  | atom x => rfl
  | bot => simp [Proposition.IsOrBotFree] at hA
  | imp a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at hA
    simp only [BrouwerianEvaluate_imp, iha hA.1, ihb hA.2, hilbertLindenbaumMk_himp]
  | and a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at hA
    simp only [BrouwerianEvaluate_and, iha hA.1, ihb hA.2, hilbertLindenbaumMk_inf]
  | or _ _ _ _ => simp [Proposition.IsOrBotFree] at hA

/-! ## Generic Completeness -/

/-- **Generic Brouwerian completeness** (for `IsOrFree` formulas): if an or-free formula is
`BrouwerianBotValid` (valid in every Brouwerian semilattice for every `bot_val`), then it is
`Axioms`-derivable for any `[ConjImpAxioms Axioms]` system.

The proof instantiates `BrouwerianBotValid` at the Hilbert Lindenbaum algebra, rewrites via the
truth lemma `brouwerianBotCanonicalV_spec`, and closes with `hilbertLindenbaumMk_eq_top_iff`.

The explicit universe annotation `.{u, u}` follows the pattern of
`conjImpBotMin_brouwerianBot_completeness` in `MplPointedConservative.lean`: both the atom type
and the algebra type live in universe `u`, ensuring universe-safe instantiation. -/
theorem brouwerianBot_completeness {Atom : Type u}
    {Axioms : PL.Proposition Atom → Prop} [ConjImpAxioms Axioms]
    {φ : PL.Proposition Atom} (hfrag : φ.IsOrFree = true)
    (h : BrouwerianBotValid.{u, u} φ) : Derivable Axioms φ := by
  have hLind : BrouwerianBotEvaluate (canonicalV Axioms) (canonicalBotVal Axioms) φ = ⊤ :=
    h (HilbertLindenbaumAlgebra Axioms) (canonicalV Axioms) (canonicalBotVal Axioms)
  rw [brouwerianBotCanonicalV_spec φ hfrag] at hLind
  exact hilbertLindenbaumMk_eq_top_iff.mp hLind

end Cslib.Logic.PL

end

end
