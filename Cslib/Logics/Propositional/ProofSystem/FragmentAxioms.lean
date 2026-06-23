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

end Cslib.Logic.PL
