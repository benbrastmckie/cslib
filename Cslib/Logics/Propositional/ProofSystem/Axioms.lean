/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs

/-! # Axiom Schemata for Propositional Logic

This module defines the axiom schemata for the propositional Hilbert-style proof system.

## Main Definition

- `PropositionalAxiom`: An inductive type enumerating the 10 axiom schemata of classical
  propositional logic: `implyK` (weakening), `implyS` (distribution), `efq` (ex falso),
  `peirce` (Peirce's law), and 6 conjunction/disjunction axioms.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 1.1
* Cslib/Logics/Modal/Metalogic/DerivationTree.lean -- modal axiom pattern (first 4 constructors)
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-- Axiom schemata for classical propositional logic.

The 10 axiom constructors are:
- **implyK** (weakening): `φ → (ψ → φ)`
- **implyS** (distribution): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
- **efq** (ex falso quodlibet): `⊥ → φ`
- **peirce** (Peirce's law): `((φ → ψ) → φ) → φ`
- **andI** (conjunction introduction): `φ → (ψ → φ ∧ ψ)`
- **andE1** (left conjunction elimination): `φ ∧ ψ → φ`
- **andE2** (right conjunction elimination): `φ ∧ ψ → ψ`
- **orI1** (left disjunction introduction): `φ → φ ∨ ψ`
- **orI2** (right disjunction introduction): `ψ → φ ∨ ψ`
- **orE** (disjunction elimination): `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`

Together with modus ponens, these axioms characterize classical propositional logic. -/
inductive PropositionalAxiom : PL.Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : PL.Proposition Atom) :
      PropositionalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : PL.Proposition Atom) :
      PropositionalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : PL.Proposition Atom) :
      PropositionalAxiom (Proposition.bot.imp φ)
  /-- Peirce's law / DNE: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : PL.Proposition Atom) :
      PropositionalAxiom (((φ.imp ψ).imp φ).imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)` -/
  | andI (φ ψ : PL.Proposition Atom) :
      PropositionalAxiom (φ.imp (ψ.imp (φ.and ψ)))
  /-- Left conjunction elimination: `φ ∧ ψ → φ` -/
  | andE1 (φ ψ : PL.Proposition Atom) :
      PropositionalAxiom ((φ.and ψ).imp φ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ` -/
  | andE2 (φ ψ : PL.Proposition Atom) :
      PropositionalAxiom ((φ.and ψ).imp ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ` -/
  | orI1 (φ ψ : PL.Proposition Atom) :
      PropositionalAxiom (φ.imp (φ.or ψ))
  /-- Right disjunction introduction: `ψ → φ ∨ ψ` -/
  | orI2 (φ ψ : PL.Proposition Atom) :
      PropositionalAxiom (ψ.imp (φ.or ψ))
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))` -/
  | orE (φ ψ χ : PL.Proposition Atom) :
      PropositionalAxiom ((φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ)))

/-- Axiom schemata for intuitionistic propositional logic.

The 9 axiom constructors are:
- **implyK** (weakening): `φ → (ψ → φ)`
- **implyS** (distribution): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
- **efq** (ex falso quodlibet): `⊥ → φ`
- **andI**, **andE1**, **andE2**, **orI1**, **orI2**, **orE** (conjunction/disjunction axioms)

Together with modus ponens, these axioms characterize intuitionistic propositional logic. -/
inductive IntPropAxiom : PL.Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : PL.Proposition Atom) :
      IntPropAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : PL.Proposition Atom) :
      IntPropAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ` -/
  | efq (φ : PL.Proposition Atom) :
      IntPropAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)` -/
  | andI (φ ψ : PL.Proposition Atom) :
      IntPropAxiom (φ.imp (ψ.imp (φ.and ψ)))
  /-- Left conjunction elimination: `φ ∧ ψ → φ` -/
  | andE1 (φ ψ : PL.Proposition Atom) :
      IntPropAxiom ((φ.and ψ).imp φ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ` -/
  | andE2 (φ ψ : PL.Proposition Atom) :
      IntPropAxiom ((φ.and ψ).imp ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ` -/
  | orI1 (φ ψ : PL.Proposition Atom) :
      IntPropAxiom (φ.imp (φ.or ψ))
  /-- Right disjunction introduction: `ψ → φ ∨ ψ` -/
  | orI2 (φ ψ : PL.Proposition Atom) :
      IntPropAxiom (ψ.imp (φ.or ψ))
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))` -/
  | orE (φ ψ χ : PL.Proposition Atom) :
      IntPropAxiom ((φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ)))

/-- Axiom schemata for minimal propositional logic.

The 8 axiom constructors are:
- **implyK** (weakening): `φ → (ψ → φ)`
- **implyS** (distribution): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
- **andI**, **andE1**, **andE2**, **orI1**, **orI2**, **orE** (conjunction/disjunction axioms)

Together with modus ponens, these axioms characterize minimal propositional logic. -/
inductive MinPropAxiom : PL.Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : PL.Proposition Atom) :
      MinPropAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : PL.Proposition Atom) :
      MinPropAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)` -/
  | andI (φ ψ : PL.Proposition Atom) :
      MinPropAxiom (φ.imp (ψ.imp (φ.and ψ)))
  /-- Left conjunction elimination: `φ ∧ ψ → φ` -/
  | andE1 (φ ψ : PL.Proposition Atom) :
      MinPropAxiom ((φ.and ψ).imp φ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ` -/
  | andE2 (φ ψ : PL.Proposition Atom) :
      MinPropAxiom ((φ.and ψ).imp ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ` -/
  | orI1 (φ ψ : PL.Proposition Atom) :
      MinPropAxiom (φ.imp (φ.or ψ))
  /-- Right disjunction introduction: `ψ → φ ∨ ψ` -/
  | orI2 (φ ψ : PL.Proposition Atom) :
      MinPropAxiom (ψ.imp (φ.or ψ))
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))` -/
  | orE (φ ψ χ : PL.Proposition Atom) :
      MinPropAxiom ((φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ)))

/-! ## Axiom Subsumption -/

/-- Every minimal propositional axiom is an intuitionistic propositional axiom. -/
theorem MinPropAxiom.toIntProp {φ : PL.Proposition Atom}
    (h : MinPropAxiom φ) : IntPropAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c
  | andI a b => exact .andI a b
  | andE1 a b => exact .andE1 a b
  | andE2 a b => exact .andE2 a b
  | orI1 a b => exact .orI1 a b
  | orI2 a b => exact .orI2 a b
  | orE a b c => exact .orE a b c

/-- Every intuitionistic propositional axiom is a classical propositional axiom. -/
theorem IntPropAxiom.toProp {φ : PL.Proposition Atom}
    (h : IntPropAxiom φ) : PropositionalAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c
  | efq a => exact .efq a
  | andI a b => exact .andI a b
  | andE1 a b => exact .andE1 a b
  | andE2 a b => exact .andE2 a b
  | orI1 a b => exact .orI1 a b
  | orI2 a b => exact .orI2 a b
  | orE a b c => exact .orE a b c

/-! ## Implication Axiom Witnesses -/

/-- `PropositionalAxiom` includes implyK: witness for deduction theorem arguments. -/
theorem prop_h_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    PropositionalAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

/-- `PropositionalAxiom` includes implyS: witness for deduction theorem arguments. -/
theorem prop_h_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    PropositionalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

/-- `IntPropAxiom` includes implyK: witness for deduction theorem arguments. -/
theorem int_h_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    IntPropAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

/-- `IntPropAxiom` includes implyS: witness for deduction theorem arguments. -/
theorem int_h_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    IntPropAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

/-- `MinPropAxiom` includes implyK: witness for deduction theorem arguments. -/
theorem min_h_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    MinPropAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

/-- `MinPropAxiom` includes implyS: witness for deduction theorem arguments. -/
theorem min_h_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    MinPropAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

end Cslib.Logic.PL
