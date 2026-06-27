/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.ProofSystem.Axioms
public import Cslib.Logics.Propositional.ProofSystem.Derivation
public import Cslib.Logics.Propositional.Metalogic.DeductionTheorem
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates

/-! # Fragment Axiom Predicates for Propositional Logic

This module defines two fragment-specific Hilbert axiom predicates:

- `ConjImpAxiom`: Axiom schemata for IPL⟨∧,→,⊤⟩ — the conjunctive-implicational fragment,
  with K, S, and the three conjunction axioms (intro/elim).
- `ImpAxiom`: Axiom schemata for IPL⟨→,⊤⟩ — the implicational fragment, with only K and S.

For each predicate we establish:
1. **Subsumption**: `ImpAxiom → ConjImpAxiom → MinPropAxiom`
2. **Implication witnesses**: `mem_implyK` and `mem_implyS` for instantiating the deduction
   theorem and `MinimalHilbert` instances.
3. **Substitution closure**: each predicate is preserved under atom substitution.
4. **Fragment predicate compatibility**: applying a `ConjImpAxiom` (resp. `ImpAxiom`)
   constructor to or-bot-free (resp. imp-top-only) propositions yields an or-bot-free
   (resp. imp-top-only) formula.
5. **Deduction theorem instances** via `hasDeductionTheorem` with the explicit witnesses.

## References

* Cslib/Logics/Propositional/ProofSystem/Axioms.lean -- `MinPropAxiom` pattern
* Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean -- substitution closure pattern
* Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean -- `hasDeductionTheorem`
* Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean -- closure lemmas
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Fragment Axiom Predicates -/

/-- Axiom schemata for the conjunctive-implicational fragment IPL⟨∧,→,⊤⟩.

The 5 axiom constructors are:
- **implyK** (weakening): `φ → (ψ → φ)`
- **implyS** (distribution): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
- **andI** (conjunction introduction): `φ → (ψ → φ ∧ ψ)`
- **andE1** (left conjunction elimination): `φ ∧ ψ → φ`
- **andE2** (right conjunction elimination): `φ ∧ ψ → ψ`

Together with modus ponens, these axioms characterize the conjunctive-implicational
fragment of minimal propositional logic. -/
inductive ConjImpAxiom : PL.Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : PL.Proposition Atom) :
      ConjImpAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : PL.Proposition Atom) :
      ConjImpAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)` -/
  | andI (φ ψ : PL.Proposition Atom) :
      ConjImpAxiom (φ.imp (ψ.imp (φ.and ψ)))
  /-- Left conjunction elimination: `φ ∧ ψ → φ` -/
  | andE1 (φ ψ : PL.Proposition Atom) :
      ConjImpAxiom ((φ.and ψ).imp φ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ` -/
  | andE2 (φ ψ : PL.Proposition Atom) :
      ConjImpAxiom ((φ.and ψ).imp ψ)

/-- Axiom schemata for the implicational fragment IPL⟨→,⊤⟩.

The 2 axiom constructors are:
- **implyK** (weakening): `φ → (ψ → φ)`
- **implyS** (distribution): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`

Together with modus ponens, these axioms characterize the purely implicational fragment
of propositional logic (the Hilbert–Bernays system). -/
inductive ImpAxiom : PL.Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : PL.Proposition Atom) :
      ImpAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : PL.Proposition Atom) :
      ImpAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))

/-! ## Axiom Subsumption -/

/-- Every implicational axiom is a conjunctive-implicational axiom. -/
theorem ImpAxiom.toConjImpAxiom {φ : PL.Proposition Atom}
    (h : ImpAxiom φ) : ConjImpAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c

/-- Every conjunctive-implicational axiom is a minimal propositional axiom. -/
theorem ConjImpAxiom.toMinPropAxiom {φ : PL.Proposition Atom}
    (h : ConjImpAxiom φ) : MinPropAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c
  | andI a b => exact .andI a b
  | andE1 a b => exact .andE1 a b
  | andE2 a b => exact .andE2 a b

/-! ## Implication Axiom Witnesses -/

namespace ConjImpAxiom

/-- `ConjImpAxiom` includes implyK: witness for deduction theorem arguments. -/
theorem mem_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    ConjImpAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

/-- `ConjImpAxiom` includes implyS: witness for deduction theorem arguments. -/
theorem mem_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    ConjImpAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

end ConjImpAxiom

namespace ImpAxiom

/-- `ImpAxiom` includes implyK: witness for deduction theorem arguments. -/
theorem mem_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    ImpAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

/-- `ImpAxiom` includes implyS: witness for deduction theorem arguments. -/
theorem mem_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    ImpAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

end ImpAxiom

/-! ## Substitution Closure -/

/-- Conjunctive-implicational axiom schemata are preserved under substitution. -/
theorem subst_preserves_conjImpAxiom
    {Atom : Type u} {Atom' : Type u}
    {φ : PL.Proposition Atom}
    (h : ConjImpAxiom φ) (f : Atom → PL.Proposition Atom') :
    ConjImpAxiom (φ.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)
  | andI a b => exact .andI (a.subst f) (b.subst f)
  | andE1 a b => exact .andE1 (a.subst f) (b.subst f)
  | andE2 a b => exact .andE2 (a.subst f) (b.subst f)

/-- Implicational axiom schemata are preserved under substitution. -/
theorem subst_preserves_impAxiom
    {Atom : Type u} {Atom' : Type u}
    {φ : PL.Proposition Atom}
    (h : ImpAxiom φ) (f : Atom → PL.Proposition Atom') :
    ImpAxiom (φ.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)

/-! ## Fragment Predicate Compatibility -/

/-- Applying the `implyK` constructor to or-bot-free propositions yields an or-bot-free formula.

This is `φ → (ψ → φ)`, which is or-bot-free when `φ` and `ψ` are. -/
lemma conjImpAxiom_implyK_isOrBotFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrBotFree = true) (hψ : ψ.IsOrBotFree = true) :
    (φ.imp (ψ.imp φ)).IsOrBotFree = true :=
  imp_isOrBotFree hφ (imp_isOrBotFree hψ hφ)

/-- Applying the `implyS` constructor to or-bot-free propositions yields an or-bot-free formula.

This is `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`, or-bot-free when `φ`, `ψ`, `χ` are. -/
lemma conjImpAxiom_implyS_isOrBotFree {φ ψ χ : PL.Proposition Atom}
    (hφ : φ.IsOrBotFree = true) (hψ : ψ.IsOrBotFree = true) (hχ : χ.IsOrBotFree = true) :
    ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))).IsOrBotFree = true :=
  imp_isOrBotFree
    (imp_isOrBotFree hφ (imp_isOrBotFree hψ hχ))
    (imp_isOrBotFree (imp_isOrBotFree hφ hψ) (imp_isOrBotFree hφ hχ))

/-- Applying the `andI` constructor to or-bot-free propositions yields an or-bot-free formula.

This is `φ → (ψ → φ ∧ ψ)`, or-bot-free when `φ` and `ψ` are. -/
lemma conjImpAxiom_andI_isOrBotFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrBotFree = true) (hψ : ψ.IsOrBotFree = true) :
    (φ.imp (ψ.imp (φ.and ψ))).IsOrBotFree = true :=
  imp_isOrBotFree hφ (imp_isOrBotFree hψ (and_isOrBotFree hφ hψ))

/-- Applying the `andE1` constructor to or-bot-free propositions yields an or-bot-free formula.

This is `φ ∧ ψ → φ`, or-bot-free when `φ` and `ψ` are. -/
lemma conjImpAxiom_andE1_isOrBotFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrBotFree = true) (hψ : ψ.IsOrBotFree = true) :
    ((φ.and ψ).imp φ).IsOrBotFree = true :=
  imp_isOrBotFree (and_isOrBotFree hφ hψ) hφ

/-- Applying the `andE2` constructor to or-bot-free propositions yields an or-bot-free formula.

This is `φ ∧ ψ → ψ`, or-bot-free when `φ` and `ψ` are. -/
lemma conjImpAxiom_andE2_isOrBotFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrBotFree = true) (hψ : ψ.IsOrBotFree = true) :
    ((φ.and ψ).imp ψ).IsOrBotFree = true :=
  imp_isOrBotFree (and_isOrBotFree hφ hψ) hψ

/-- Applying the `implyK` constructor to imp-top-only propositions yields an imp-top-only formula.

This is `φ → (ψ → φ)`, imp-top-only when `φ` and `ψ` are. -/
lemma impAxiom_implyK_isImpTopOnly {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsImpTopOnly = true) (hψ : ψ.IsImpTopOnly = true) :
    (φ.imp (ψ.imp φ)).IsImpTopOnly = true :=
  imp_isImpTopOnly hφ (imp_isImpTopOnly hψ hφ)

/-- Applying the `implyS` constructor to imp-top-only propositions yields an imp-top-only formula.

This is `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`, imp-top-only when `φ`, `ψ`, `χ` are. -/
lemma impAxiom_implyS_isImpTopOnly {φ ψ χ : PL.Proposition Atom}
    (hφ : φ.IsImpTopOnly = true) (hψ : ψ.IsImpTopOnly = true) (hχ : χ.IsImpTopOnly = true) :
    ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))).IsImpTopOnly = true :=
  imp_isImpTopOnly
    (imp_isImpTopOnly hφ (imp_isImpTopOnly hψ hχ))
    (imp_isImpTopOnly (imp_isImpTopOnly hφ hψ) (imp_isImpTopOnly hφ hχ))

/-! ## Deduction Theorem Instances -/

/-- The deduction theorem holds for `ConjImpAxiom`. -/
theorem conjImpAxiom_hasDeductionTheorem :
    Metalogic.HasDeductionTheorem (propDerivationSystem (@ConjImpAxiom Atom)) :=
  hasDeductionTheorem ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS

/-- The deduction theorem holds for `ImpAxiom`. -/
theorem impAxiom_hasDeductionTheorem :
    Metalogic.HasDeductionTheorem (propDerivationSystem (@ImpAxiom Atom)) :=
  hasDeductionTheorem ImpAxiom.mem_implyK ImpAxiom.mem_implyS

/-! ## ConjImpBot Axiom System -/

/-- Axiom schemata for the conjunctive-implicational-bot fragment IPL⟨∧,→,⊥,⊤⟩.

The 6 axiom constructors are:
- **implyK** (weakening): `φ → (ψ → φ)`
- **implyS** (distribution): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
- **andI** (conjunction introduction): `φ → (ψ → φ ∧ ψ)`
- **andE1** (left conjunction elimination): `φ ∧ ψ → φ`
- **andE2** (right conjunction elimination): `φ ∧ ψ → ψ`
- **efq** (ex falso quodlibet / explosion): `⊥ → φ`

Together with modus ponens, these axioms characterize the conjunctive-implicational-bot
fragment of intuitionistic propositional logic (IPL with conjunction, implication, and
falsum but without disjunction). -/
inductive ConjImpBotAxiom : PL.Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : PL.Proposition Atom) :
      ConjImpBotAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : PL.Proposition Atom) :
      ConjImpBotAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)` -/
  | andI (φ ψ : PL.Proposition Atom) :
      ConjImpBotAxiom (φ.imp (ψ.imp (φ.and ψ)))
  /-- Left conjunction elimination: `φ ∧ ψ → φ` -/
  | andE1 (φ ψ : PL.Proposition Atom) :
      ConjImpBotAxiom ((φ.and ψ).imp φ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ` -/
  | andE2 (φ ψ : PL.Proposition Atom) :
      ConjImpBotAxiom ((φ.and ψ).imp ψ)
  /-- Ex falso quodlibet (explosion): `⊥ → φ` -/
  | efq (φ : PL.Proposition Atom) :
      ConjImpBotAxiom (Proposition.bot.imp φ)

/-! ## ConjImpBot Axiom Subsumption -/

/-- Every conjunctive-implicational axiom is a conjunctive-implicational-bot axiom. -/
theorem ConjImpAxiom.toConjImpBotAxiom {φ : PL.Proposition Atom}
    (h : ConjImpAxiom φ) : ConjImpBotAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c
  | andI a b => exact .andI a b
  | andE1 a b => exact .andE1 a b
  | andE2 a b => exact .andE2 a b

/-- Every conjunctive-implicational-bot axiom is a minimal propositional axiom
(and hence an intuitionistic propositional axiom). -/
theorem ConjImpBotAxiom.toIntPropAxiom {φ : PL.Proposition Atom}
    (h : ConjImpBotAxiom φ) : IntPropAxiom φ := by
  cases h with
  | implyK a b => exact (MinPropAxiom.implyK a b).toIntPropAxiom
  | implyS a b c => exact (MinPropAxiom.implyS a b c).toIntPropAxiom
  | andI a b => exact (MinPropAxiom.andI a b).toIntPropAxiom
  | andE1 a b => exact (MinPropAxiom.andE1 a b).toIntPropAxiom
  | andE2 a b => exact (MinPropAxiom.andE2 a b).toIntPropAxiom
  | efq a => exact IntPropAxiom.efq a

/-! ## ConjImpBot Implication Axiom Witnesses -/

namespace ConjImpBotAxiom

/-- `ConjImpBotAxiom` includes implyK: witness for deduction theorem arguments. -/
theorem mem_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    ConjImpBotAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

/-- `ConjImpBotAxiom` includes implyS: witness for deduction theorem arguments. -/
theorem mem_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    ConjImpBotAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

end ConjImpBotAxiom

/-! ## ConjImpBot Substitution Closure -/

/-- Conjunctive-implicational-bot axiom schemata are preserved under substitution. -/
theorem subst_preserves_conjImpBotAxiom
    {Atom : Type u} {Atom' : Type u}
    {φ : PL.Proposition Atom}
    (h : ConjImpBotAxiom φ) (f : Atom → PL.Proposition Atom') :
    ConjImpBotAxiom (φ.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)
  | andI a b => exact .andI (a.subst f) (b.subst f)
  | andE1 a b => exact .andE1 (a.subst f) (b.subst f)
  | andE2 a b => exact .andE2 (a.subst f) (b.subst f)
  | efq a => exact .efq (a.subst f)

/-! ## ConjImpBot Fragment Predicate Compatibility -/

/-- Applying the `implyK` constructor to or-free propositions yields an or-free formula.

This is `φ → (ψ → φ)`, which is or-free when `φ` and `ψ` are. -/
lemma conjImpBotAxiom_implyK_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    (φ.imp (ψ.imp φ)).IsOrFree = true :=
  imp_isOrFree hφ (imp_isOrFree hψ hφ)

/-- Applying the `implyS` constructor to or-free propositions yields an or-free formula.

This is `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`, or-free when `φ`, `ψ`, `χ` are. -/
lemma conjImpBotAxiom_implyS_isOrFree {φ ψ χ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) (hχ : χ.IsOrFree = true) :
    ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))).IsOrFree = true :=
  imp_isOrFree
    (imp_isOrFree hφ (imp_isOrFree hψ hχ))
    (imp_isOrFree (imp_isOrFree hφ hψ) (imp_isOrFree hφ hχ))

/-- Applying the `andI` constructor to or-free propositions yields an or-free formula.

This is `φ → (ψ → φ ∧ ψ)`, or-free when `φ` and `ψ` are. -/
lemma conjImpBotAxiom_andI_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    (φ.imp (ψ.imp (φ.and ψ))).IsOrFree = true :=
  imp_isOrFree hφ (imp_isOrFree hψ (and_isOrFree hφ hψ))

/-- Applying the `andE1` constructor to or-free propositions yields an or-free formula.

This is `φ ∧ ψ → φ`, or-free when `φ` and `ψ` are. -/
lemma conjImpBotAxiom_andE1_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    ((φ.and ψ).imp φ).IsOrFree = true :=
  imp_isOrFree (and_isOrFree hφ hψ) hφ

/-- Applying the `andE2` constructor to or-free propositions yields an or-free formula.

This is `φ ∧ ψ → ψ`, or-free when `φ` and `ψ` are. -/
lemma conjImpBotAxiom_andE2_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    ((φ.and ψ).imp ψ).IsOrFree = true :=
  imp_isOrFree (and_isOrFree hφ hψ) hψ

/-- Applying the `efq` constructor to an or-free proposition yields an or-free formula.

This is `⊥ → φ`, which is or-free when `φ` is. -/
lemma conjImpBotAxiom_efq_isOrFree {φ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) :
    (Proposition.bot.imp φ).IsOrFree = true :=
  imp_isOrFree (by simp [Proposition.IsOrFree]) hφ

/-! ## ConjImpBot Deduction Theorem Instance -/

/-- The deduction theorem holds for `ConjImpBotAxiom`. -/
theorem conjImpBotAxiom_hasDeductionTheorem :
    Metalogic.HasDeductionTheorem (propDerivationSystem (@ConjImpBotAxiom Atom)) :=
  hasDeductionTheorem ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS

/-! ## ConjImpBotMin Axiom System -/

/-- Axiom schemata for the MPL conjunctive-implicational-bot fragment MPL⟨∧,→,⊥,⊤⟩.

Identical to `ConjImpBotAxiom` except that it omits ex falso quodlibet (`⊥ → φ`). This is the
point at which the minimal-logic (MPL) tower diverges from the intuitionistic tower: `⊥` is a
free constant rather than the least element with explosion.

The 5 axiom constructors are:
- **implyK** (weakening): `φ → (ψ → φ)`
- **implyS** (distribution): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
- **andI** (conjunction introduction): `φ → (ψ → φ ∧ ψ)`
- **andE1** (left conjunction elimination): `φ ∧ ψ → φ`
- **andE2** (right conjunction elimination): `φ ∧ ψ → ψ`

Together with modus ponens, these axioms characterize the conjunctive-implicational-bot fragment
of minimal propositional logic (no ex falso). -/
inductive ConjImpBotMinAxiom : PL.Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : PL.Proposition Atom) :
      ConjImpBotMinAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : PL.Proposition Atom) :
      ConjImpBotMinAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)` -/
  | andI (φ ψ : PL.Proposition Atom) :
      ConjImpBotMinAxiom (φ.imp (ψ.imp (φ.and ψ)))
  /-- Left conjunction elimination: `φ ∧ ψ → φ` -/
  | andE1 (φ ψ : PL.Proposition Atom) :
      ConjImpBotMinAxiom ((φ.and ψ).imp φ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ` -/
  | andE2 (φ ψ : PL.Proposition Atom) :
      ConjImpBotMinAxiom ((φ.and ψ).imp ψ)

/-! ## ConjImpBotMin Axiom Subsumption -/

/-- Every conjunctive-implicational axiom is a conjunctive-implicational-bot-min axiom. -/
theorem ConjImpAxiom.toConjImpBotMinAxiom {φ : PL.Proposition Atom}
    (h : ConjImpAxiom φ) : ConjImpBotMinAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c
  | andI a b => exact .andI a b
  | andE1 a b => exact .andE1 a b
  | andE2 a b => exact .andE2 a b

/-- Every conjunctive-implicational-bot-min axiom is a minimal propositional axiom.

Note: the target is `MinPropAxiom` (which has no ex falso), **not** `IntPropAxiom`. Staying inside
minimal logic is the defining feature of this fragment. -/
theorem ConjImpBotMinAxiom.toMinPropAxiom {φ : PL.Proposition Atom}
    (h : ConjImpBotMinAxiom φ) : MinPropAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c
  | andI a b => exact .andI a b
  | andE1 a b => exact .andE1 a b
  | andE2 a b => exact .andE2 a b

/-! ## ConjImpBotMin Implication Axiom Witnesses -/

namespace ConjImpBotMinAxiom

/-- `ConjImpBotMinAxiom` includes implyK: witness for deduction theorem arguments. -/
theorem mem_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    ConjImpBotMinAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

/-- `ConjImpBotMinAxiom` includes implyS: witness for deduction theorem arguments. -/
theorem mem_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    ConjImpBotMinAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

end ConjImpBotMinAxiom

/-! ## ConjImpBotMin Substitution Closure -/

/-- Conjunctive-implicational-bot-min axiom schemata are preserved under substitution. -/
theorem subst_preserves_conjImpBotMinAxiom
    {Atom : Type u} {Atom' : Type u}
    {φ : PL.Proposition Atom}
    (h : ConjImpBotMinAxiom φ) (f : Atom → PL.Proposition Atom') :
    ConjImpBotMinAxiom (φ.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)
  | andI a b => exact .andI (a.subst f) (b.subst f)
  | andE1 a b => exact .andE1 (a.subst f) (b.subst f)
  | andE2 a b => exact .andE2 (a.subst f) (b.subst f)

/-! ## ConjImpBotMin Fragment Predicate Compatibility -/

/-- Applying the `implyK` constructor to or-free propositions yields an or-free formula.

This is `φ → (ψ → φ)`, which is or-free when `φ` and `ψ` are. -/
lemma conjImpBotMinAxiom_implyK_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    (φ.imp (ψ.imp φ)).IsOrFree = true :=
  imp_isOrFree hφ (imp_isOrFree hψ hφ)

/-- Applying the `implyS` constructor to or-free propositions yields an or-free formula.

This is `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`, or-free when `φ`, `ψ`, `χ` are. -/
lemma conjImpBotMinAxiom_implyS_isOrFree {φ ψ χ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) (hχ : χ.IsOrFree = true) :
    ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))).IsOrFree = true :=
  imp_isOrFree
    (imp_isOrFree hφ (imp_isOrFree hψ hχ))
    (imp_isOrFree (imp_isOrFree hφ hψ) (imp_isOrFree hφ hχ))

/-- Applying the `andI` constructor to or-free propositions yields an or-free formula.

This is `φ → (ψ → φ ∧ ψ)`, or-free when `φ` and `ψ` are. -/
lemma conjImpBotMinAxiom_andI_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    (φ.imp (ψ.imp (φ.and ψ))).IsOrFree = true :=
  imp_isOrFree hφ (imp_isOrFree hψ (and_isOrFree hφ hψ))

/-- Applying the `andE1` constructor to or-free propositions yields an or-free formula.

This is `φ ∧ ψ → φ`, or-free when `φ` and `ψ` are. -/
lemma conjImpBotMinAxiom_andE1_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    ((φ.and ψ).imp φ).IsOrFree = true :=
  imp_isOrFree (and_isOrFree hφ hψ) hφ

/-- Applying the `andE2` constructor to or-free propositions yields an or-free formula.

This is `φ ∧ ψ → ψ`, or-free when `φ` and `ψ` are. -/
lemma conjImpBotMinAxiom_andE2_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    ((φ.and ψ).imp ψ).IsOrFree = true :=
  imp_isOrFree (and_isOrFree hφ hψ) hψ

/-! ## ConjImpBotMin Deduction Theorem Instance -/

/-- The deduction theorem holds for `ConjImpBotMinAxiom`. -/
theorem conjImpBotMinAxiom_hasDeductionTheorem :
    Metalogic.HasDeductionTheorem (propDerivationSystem (@ConjImpBotMinAxiom Atom)) :=
  hasDeductionTheorem ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS

/-! ## ClassicalImp Axiom System -/

/-- Axiom schemata for the classical implicational fragment CPL⟨→,⊤⟩.

The 3 axiom constructors are:
- **implyK** (weakening): `φ → (ψ → φ)`
- **implyS** (distribution): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
- **peirce** (Peirce's law): `((φ → ψ) → φ) → φ`

Together with modus ponens, these axioms characterize the purely implicational fragment
of classical propositional logic (the Tarski–Bernays axiomatization). Peirce's law
distinguishes this system from the intuitionistic implicational fragment IPL⟨→,⊤⟩. -/
inductive ClassicalImpAxiom : PL.Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : PL.Proposition Atom) :
      ClassicalImpAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : PL.Proposition Atom) :
      ClassicalImpAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Peirce's law: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : PL.Proposition Atom) :
      ClassicalImpAxiom (((φ.imp ψ).imp φ).imp φ)

/-! ## ClassicalImp Axiom Subsumption -/

/-- Every implicational axiom is a classical implicational axiom. -/
theorem ImpAxiom.toClassicalImpAxiom {φ : PL.Proposition Atom}
    (h : ImpAxiom φ) : ClassicalImpAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c

/-- Every classical implicational axiom is a classical propositional axiom. -/
theorem ClassicalImpAxiom.toPropAxiom {φ : PL.Proposition Atom}
    (h : ClassicalImpAxiom φ) : PropositionalAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c
  | peirce a b => exact .peirce a b

/-! ## ClassicalImp Implication Axiom Witnesses -/

namespace ClassicalImpAxiom

/-- `ClassicalImpAxiom` includes implyK: witness for deduction theorem arguments. -/
theorem mem_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    ClassicalImpAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

/-- `ClassicalImpAxiom` includes implyS: witness for deduction theorem arguments. -/
theorem mem_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    ClassicalImpAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

end ClassicalImpAxiom

/-! ## ClassicalImp Substitution Closure -/

/-- Classical implicational axiom schemata are preserved under substitution. -/
theorem subst_preserves_classicalImpAxiom
    {Atom : Type u} {Atom' : Type u}
    {φ : PL.Proposition Atom}
    (h : ClassicalImpAxiom φ) (f : Atom → PL.Proposition Atom') :
    ClassicalImpAxiom (φ.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)
  | peirce a b => exact .peirce (a.subst f) (b.subst f)

/-! ## ClassicalImp Fragment Predicate Compatibility -/

/-- Applying the `implyK` constructor to imp-top-only propositions yields an imp-top-only formula.

This is `φ → (ψ → φ)`, imp-top-only when `φ` and `ψ` are. -/
lemma classicalImpAxiom_implyK_isImpTopOnly {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsImpTopOnly = true) (hψ : ψ.IsImpTopOnly = true) :
    (φ.imp (ψ.imp φ)).IsImpTopOnly = true :=
  imp_isImpTopOnly hφ (imp_isImpTopOnly hψ hφ)

/-- Applying the `implyS` constructor to imp-top-only propositions yields an imp-top-only formula.

This is `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`, imp-top-only when `φ`, `ψ`, `χ` are. -/
lemma classicalImpAxiom_implyS_isImpTopOnly {φ ψ χ : PL.Proposition Atom}
    (hφ : φ.IsImpTopOnly = true) (hψ : ψ.IsImpTopOnly = true) (hχ : χ.IsImpTopOnly = true) :
    ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))).IsImpTopOnly = true :=
  imp_isImpTopOnly
    (imp_isImpTopOnly hφ (imp_isImpTopOnly hψ hχ))
    (imp_isImpTopOnly (imp_isImpTopOnly hφ hψ) (imp_isImpTopOnly hφ hχ))

/-- Applying the `peirce` constructor to imp-top-only propositions yields an imp-top-only formula.

This is `((φ → ψ) → φ) → φ`, imp-top-only when `φ` and `ψ` are. -/
lemma classicalImpAxiom_peirce_isImpTopOnly {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsImpTopOnly = true) (hψ : ψ.IsImpTopOnly = true) :
    (((φ.imp ψ).imp φ).imp φ).IsImpTopOnly = true :=
  imp_isImpTopOnly
    (imp_isImpTopOnly (imp_isImpTopOnly hφ hψ) hφ)
    hφ

/-! ## ClassicalImp Deduction Theorem Instance -/

/-- The deduction theorem holds for `ClassicalImpAxiom`. -/
theorem classicalImpAxiom_hasDeductionTheorem :
    Metalogic.HasDeductionTheorem (propDerivationSystem (@ClassicalImpAxiom Atom)) :=
  hasDeductionTheorem ClassicalImpAxiom.mem_implyK ClassicalImpAxiom.mem_implyS

/-! ## ConjImpAxioms Instances for Fragment Axiom Families -/

/-- `ConjImpAxiom` satisfies `ConjImpAxioms`. -/
instance conjImpAxiomConjImpAxioms : ConjImpAxioms (@ConjImpAxiom Atom) where
  h_K := fun φ ψ => .implyK φ ψ
  h_S := fun φ ψ χ => .implyS φ ψ χ
  h_andI := fun φ ψ => .andI φ ψ
  h_andE1 := fun φ ψ => .andE1 φ ψ
  h_andE2 := fun φ ψ => .andE2 φ ψ

/-- `ConjImpBotAxiom` satisfies `ConjImpAxioms`. -/
instance conjImpBotAxiomConjImpAxioms : ConjImpAxioms (@ConjImpBotAxiom Atom) where
  h_K := fun φ ψ => .implyK φ ψ
  h_S := fun φ ψ χ => .implyS φ ψ χ
  h_andI := fun φ ψ => .andI φ ψ
  h_andE1 := fun φ ψ => .andE1 φ ψ
  h_andE2 := fun φ ψ => .andE2 φ ψ

/-- `ConjImpBotMinAxiom` satisfies `ConjImpAxioms`. -/
instance conjImpBotMinAxiomConjImpAxioms : ConjImpAxioms (@ConjImpBotMinAxiom Atom) where
  h_K := fun φ ψ => .implyK φ ψ
  h_S := fun φ ψ χ => .implyS φ ψ χ
  h_andI := fun φ ψ => .andI φ ψ
  h_andE1 := fun φ ψ => .andE1 φ ψ
  h_andE2 := fun φ ψ => .andE2 φ ψ

end Cslib.Logic.PL
