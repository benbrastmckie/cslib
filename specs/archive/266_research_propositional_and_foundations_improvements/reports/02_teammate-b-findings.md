# Teammate B Findings: Mathlib Patterns, Sequent Calculus Design, and Alternative Proof Systems

**Task**: 266 - Research Propositional/ and Foundations/ improvements
**Role**: Teammate B - Alternative Approaches and Prior Art
**Date**: 2026-06-22
**Agent**: formal-research-agent (Teammate B context)

---

## Executive Summary

CSLib's `Propositional/` and `Foundations/` already contain a rich multi-system proof framework
(Hilbert style + natural deduction, with an equivalence bridge). The main gaps identified by
this research are:

1. **No sequent calculus** for propositional logic (though CLL has a sequent calculus that could
   serve as a design template).
2. **No `HasDia` primitive** -- diamond (◇) is encoded classically via negation, which breaks
   in non-classical settings.
3. **No automated decision procedure** integrated into the proof system hierarchy (no `decide`
   tactic for propositional validity).
4. **No cut-elimination theorem** or normalization result for the existing systems.
5. **Mathlib's `itauto` (G4ip)** is the closest prior art and is already a dependency -- its
   reified proof pattern could be adapted for a standalone sequent calculus.
6. **FormalizedFormalLogic/Foundation** is the leading Lean 4 prior art project for
   propositional + sequent calculus + modal proof theory, and is architecturally distinct from
   CSLib's approach.

---

## Key Findings

### Finding 1: Mathlib Has No Standalone Propositional Logic Formalization

**Confidence: High**

A systematic search via LeanSearch, Loogle, and LeanFinder reveals that Mathlib does not
formalize propositional logic as a standalone object-level system. Mathlib's propositional logic
infrastructure is entirely at the meta-level:

- `Prop` carries `CompleteBooleanAlgebra` structure (classical tautologies via `decide`)
- `Mathlib.Tactic.ITauto` implements G4ip for intuitionistic tautology search
- `Mathlib.Tactic.Tauto` implements classical tautology search
- `Mathlib.Tactic.Sat.FromLRAT` implements LRAT proof verification (SAT-based)
- `Sat.Fmla` is a CNF clause list, not a general propositional formula

No Mathlib module defines `inductive Proposition` as an object-level syntax, nor does Mathlib
prove soundness/completeness for a formalized Hilbert or natural deduction system. CSLib's
`Propositional/` is therefore providing unique value not present in Mathlib.

**Implication**: CSLib should not expect to borrow or reuse a Mathlib propositional logic module.
However, Mathlib's **`itauto` implementation of G4ip** is directly relevant as an architecture
reference for a future CSLib sequent calculus or decision procedure.

### Finding 2: Mathlib's `itauto` (G4ip) as a Design Pattern

**Confidence: High**

`Mathlib.Tactic.ITauto` implements the G4ip sequent calculus (Dyckhoff 1992) as a Lean 4
tactic. The key design patterns are:

**Three-level rule stratification** (directly applicable to a CSLib sequent calculus):
- Level 1 (`Context.add`): Non-splitting validity-preserving rules applied eagerly
  (e.g., `andE1`, `andE2`, `impI` when atom-headed)
- Level 2 (`prove`): Validity-preserving splitting rules (e.g., `andI`)
- Level 3 (`search`): Non-validity-preserving rules requiring backtracking (e.g., `impE`)

**`IProp` reification**: Propositional formulas are reified from `Expr` to a domain-specific
inductive type for proof search. This is analogous to CSLib's `Proposition Atom`.

**`StateM Nat` for name generation**: Used for fresh variable allocation during proof search.

**`Proof` inductive type**: Reified proofs with explicit constructors for each inference rule.
This is structurally similar to what a CSLib sequent calculus derivation type would look like.

The key limitation: Mathlib's `itauto` is a tactic, not a standalone sequent calculus
formalization. It does not produce an `inductive Proof : Sequent → Sequent → Type` that
can be studied metatheoretically. A CSLib sequent calculus would need both.

### Finding 3: FormalizedFormalLogic/Foundation is the Leading Lean 4 Prior Art

**Confidence: High**

The `FormalizedFormalLogic/Foundation` repository (referenced in Lean 4 formalization
literature) is the most comprehensive prior art for propositional + sequent calculus in Lean 4.
Key features relevant to CSLib:

- **Tait-style calculus** for propositional logic with completeness
- **First-order sequent calculus** with cut-elimination (Gentzen's Hauptsatz)
- **Modal logic** with Kripke and neighborhood semantics
- **Zoo system**: automated diagrams showing interrelationships among proof systems

The Tait-style calculus differs from the CSLib/BimodalLogic approach:
- Tait calculus uses **sets of signed formulas** (all on one "side"), proving disjunctions
  of literals
- CSLib's natural deduction uses **Finset contexts with single conclusions**
- A two-sided sequent calculus `Γ ⊢ Δ` would sit between these: left context, right context

The Foundation project is MIT-licensed and provides direct Lean 4 reference implementations
that CSLib could study for architecture decisions.

### Finding 4: CLL Already Provides a Sequent Calculus Template in CSLib

**Confidence: High**

CSLib already contains a complete sequent calculus in `Cslib/Logics/LinearLogic/CLL/Basic.lean`.
The CLL sequent calculus has:

```lean
abbrev Sequent Atom := Multiset (Proposition Atom)

inductive Proof : Sequent Atom → Type u where
  | ax : Proof {a, a⫠}
  | cut : Proof (a ::ₘ Γ) → Proof (a⫠ ::ₘ Δ) → Proof (Γ + Δ)
  | parr : Proof (a ::ₘ b ::ₘ Γ) → Proof ((a ⅋ b) ::ₘ Γ)
  | tensor : Proof (a ::ₘ Γ) → Proof (b ::ₘ Δ) → Proof ((a ⊗ b) ::ₘ (Γ + Δ))
  -- ... etc
```

This one-sided sequent calculus pattern (using `Multiset` for exchange/weakening/contraction
by construction) is directly adaptable to propositional logic. A two-sided sequent calculus
for propositional logic would use:

```lean
-- Two-sided: Γ ⊢ Δ where both sides are multisets
structure Sequent (Atom) where
  left  : Finset (Proposition Atom)
  right : Finset (Proposition Atom)

inductive LK : Sequent Atom → Type _ where
  | ax  {φ} : LK ⟨{φ}, {φ}⟩
  | cut {Γ Δ Σ Π φ} : LK ⟨Γ, insert φ Δ⟩ → LK ⟨insert φ Σ, Π⟩ → LK ⟨Γ ∪ Σ, Δ ∪ Π⟩
  | andR : LK ⟨Γ, insert φ Δ⟩ → LK ⟨Γ, insert ψ Δ⟩ → LK ⟨Γ, insert (φ ∧ ψ) Δ⟩
  | andL1 : LK ⟨insert φ Γ, Δ⟩ → LK ⟨insert (φ ∧ ψ) Γ, Δ⟩
  | andL2 : LK ⟨insert ψ Γ, Δ⟩ → LK ⟨insert (φ ∧ ψ) Γ, Δ⟩
  -- ... etc
```

Using `Finset` on both sides automatically handles exchange and contraction.

### Finding 5: The BimodalLogic Tableau System Shows the Signed-Formula Approach

**Confidence: High**

The `BimodalLogic` project in `/home/benjamin/Projects/BimodalLogic/` contains a tableau
system (`Theories/Bimodal/Metalogic/Decidability/Tableau.lean`) with:

- **Signed formulas** `T(φ)` / `F(φ)` (true/false marked)
- **30 tableau expansion rules** including propositional, modal S5, and temporal rules
- **Three result types**: `linear`, `branching`, `persistent`
- **Fuel-bounded saturation** with soundness proof

The tableau design encodes derived connectives (and, or via implication encodings):
```lean
def asAnd? : Formula → Option (Formula × Formula)
  | .imp (.imp φ (.imp ψ .bot)) .bot => some (φ, ψ)
```

This Lukasiewicz encoding approach is a design choice that **complicates** the tableau rules
compared to having primitive `and` and `or` constructors. CSLib's `Proposition` type already
uses primitive `and`/`or`, which would make a propositional tableau cleaner.

For CSLib propositional logic specifically, signed-formula tableau rules would be:
- `T(φ ∧ ψ)` → `T(φ)`, `T(ψ)` (linear)
- `F(φ ∧ ψ)` → `F(φ)` | `F(ψ)` (branching)
- etc.

The BimodalLogic tableau's `ProofExtraction.lean` (proof extraction from closed tableaux) would
be the most challenging part to formalize in a metatheoretically verified setting.

### Finding 6: Current Architecture Has Three Proof Systems, Two Gaps

**Confidence: High**

CSLib's propositional logic currently has:

| System | File | Status |
|--------|------|--------|
| Hilbert-style (parameterized) | `ProofSystem/Derivation.lean` | Complete |
| Natural deduction (10 constructors) | `NaturalDeduction/Basic.lean` | Complete |
| Hilbert-ND bridge | `NaturalDeduction/Equivalence.lean` | Complete |
| Sequent calculus (LK) | -- | **Missing** |
| Tableau system | -- | **Missing** |
| Decision procedure (`decide`) | -- | **Missing** |
| Cut elimination | -- | **Missing** |
| Normalization for ND | -- | **Missing** |

The Hilbert system uses `List`-based contexts; the natural deduction system uses `Finset`-based
contexts. This context-representation split is bridged by `Finset.toList` / `List.toFinset` in
`Equivalence.lean`.

A sequent calculus could use `Finset × Finset` (for LK with implicit exchange/contraction)
or `List × List` (if exchange/contraction are explicit rules). Using `Finset` on both sides
is cleaner and matches the ND style.

### Finding 7: `HasDia` Primitive is Missing from `Connectives.lean`

**Confidence: High**

In `Cslib/Foundations/Logic/Connectives.lean`, the connective hierarchy has:
- `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`, `HasUntil`, `HasSince`

But there is **no `HasDia` class**. Diamond (◇) is encoded in `Axioms.lean` classically as
`◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`. The docstring for `AxiomB` explicitly notes:

> "Diamond is encoded classically as `◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`, since `HasDia` is not
> yet a primitive in `ModalConnectives`."

This means axioms B and 5 and D are **only correct in classical logic**. Adding `HasDia` as
a primitive with `[HasBox F] [HasDia F]` and a duality axiom `□φ ↔ ¬◇¬φ` would:
- Enable intuitionistic modal logic formalization
- Make B/5/D axioms correct for both classical and non-classical settings
- Require updating `ModalConnectives`, `AxiomB`, `Axiom5`, `AxiomD`

This is noted as "task 173" in `Connectives.lean` comments.

### Finding 8: No Biconditional Primitive

**Confidence: Medium**

`Proposition.iff` is defined as `abbrev` (A ∧ B := (A → B) ∧ (B → A)). This is semantically
correct but means there is no `HasIff` typeclass and no `iff` constructor in the `Proposition`
inductive. For CSLib's use cases (embedding propositional into modal logic via
`FromPropositional.lean`), the absence of a primitive `iff` may be acceptable. However, for
completeness as a standalone logic library, adding `HasIff` would allow sharing biconditional
axioms across formula types (as is done for other connectives).

---

## Recommended Approach

### Priority 1: Sequent Calculus (LK) for Propositional Logic

**Rationale**: This is the most impactful missing proof system, needed for cut-elimination
and as a stepping stone to tableau and decision procedures.

**Design recommendation**: Two-sided LK sequent calculus using `Finset` on both sides:

```lean
-- In Cslib/Logics/Propositional/SequentCalculus/Basic.lean
structure LKSequent (Atom) where
  left  : Finset (Proposition Atom)
  right : Finset (Proposition Atom)

notation Γ:60 " ⊢ₛ " Δ => (⟨Γ, Δ⟩ : LKSequent _)

inductive LK : LKSequent Atom → Type _ where
  | ax   : LK ({φ} ⊢ₛ {φ})
  | cut  : LK (Γ ⊢ₛ insert φ Δ) → LK (insert φ Σ ⊢ₛ Π) → LK (Γ ∪ Σ ⊢ₛ Δ ∪ Π)
  | botL : LK (insert ⊥ Γ ⊢ₛ Δ)
  | topR : LK (Γ ⊢ₛ insert ⊤ Δ)
  | andR : LK (Γ ⊢ₛ insert φ Δ) → LK (Γ ⊢ₛ insert ψ Δ) → LK (Γ ⊢ₛ insert (φ ∧ ψ) Δ)
  | andL : LK (insert φ (insert ψ Γ) ⊢ₛ Δ) → LK (insert (φ ∧ ψ) Γ ⊢ₛ Δ)
  | orL  : LK (insert φ Γ ⊢ₛ Δ) → LK (insert ψ Γ ⊢ₛ Δ) → LK (insert (φ ∨ ψ) Γ ⊢ₛ Δ)
  | orR  : LK (Γ ⊢ₛ insert φ (insert ψ Δ)) → LK (Γ ⊢ₛ insert (φ ∨ ψ) Δ)
  | impR : LK (insert φ Γ ⊢ₛ insert ψ Δ) → LK (Γ ⊢ₛ insert (φ → ψ) Δ)
  | impL : LK (Γ ⊢ₛ insert φ Δ) → LK (insert ψ Σ ⊢ₛ Π) → LK (insert (φ → ψ) (Γ ∪ Σ) ⊢ₛ Δ ∪ Π)
```

**Key metatheoretic results to prove**:
1. Soundness: LK-derivable sequents are semantically valid
2. Completeness: Semantically valid sequents are LK-derivable
3. Cut-elimination: Cut rule is admissible (Hauptsatz)
4. Bridge to existing systems: `hilbert_iff_lk`, `nd_iff_lk`

**Template**: Adapt from `CLL/Basic.lean` (one-sided multiset) → two-sided Finset.

### Priority 2: `HasDia` Primitive

**Rationale**: Low effort, high correctness value. The current classical encoding breaks in
non-classical settings.

**Design**: Add `class HasDia (F : Type*) where dia : F → F` with `instance : HasDia
(Modal.Formula Atom) where dia φ := ...` and a duality axiom `□φ ↔ ¬◇¬φ`.

### Priority 3: Decidability / Tautology Checker

**Rationale**: CSLib already has `BoolEvaluate` in `Semantics/Bool.lean` with
`instDecidableBoolEvaluate`. This is almost all the infrastructure needed for a `decide`
tactic that checks propositional tautologies by exhaustive Boolean evaluation over `Fintype`
atom sets.

**Design**:
```lean
-- Given Atom : Type* [Fintype Atom] [DecidableEq Atom]
instance : Decidable (Tautology φ) := ...
-- connects BoolEvaluate to Evaluate, then uses Fintype.complete
```

The `BoolEvaluate_eq_iff` bridge lemma in `Bool.lean` is already set up for this.

### Priority 4: Intuitionistic Sequent Calculus (G4ip)

**Rationale**: For completeness of the logic hierarchy. G4ip is the terminating sequent
calculus for intuitionistic propositional logic (Dyckhoff 1992).

**Design**: Adapt Mathlib's `itauto` G4ip algorithm as a standalone formalized calculus
(not just a tactic). The key modification from LK is the left-implication rule splits into
4 cases to ensure termination without cut.

---

## Evidence and Examples

### CLL Sequent Calculus as Template (Direct Evidence)

File: `/home/benjamin/Projects/cslib/Cslib/Logics/LinearLogic/CLL/Basic.lean`

Lines 172-210 show the exact pattern CSLib already uses for sequent calculi:
- `Sequent Atom := Multiset (Proposition Atom)` (one-sided)
- `inductive Proof : Sequent Atom → Type u where` (inference rules as constructors)
- `instance : HasInferenceSystem (Sequent Atom) := ⟨Proof⟩` (plugs into InferenceSystem)

A propositional LK would use the same pattern with `LKSequent = Finset × Finset`.

### Existing ND System as Bridge Target (Direct Evidence)

File: `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`

The ND system uses `Finset`-based contexts (lines 108-155), which makes it directly
compatible with a `Finset`-based LK formulation. The context representation choices are:
- Hilbert: `List (PL.Proposition Atom)`
- ND: `Finset (PL.Proposition Atom)`
- Proposed LK: `Finset × Finset`

Bridge lemmas would need `List.toFinset` / `Finset.toList` (already used in Equivalence.lean).

### Mathlib `itauto` G4ip Source (Web Evidence)

Documented at `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/ITauto.html`

The G4ip implementation uses `IProp` + `Proof` inductive types and a three-level rule
stratification. The `prove : Context → IProp → StateM Nat (Bool × Proof)` function is the
main entry point. This architecture directly informs how a CSLib G4ip formalization should
be structured.

### FormalizedFormalLogic/Foundation (Web Evidence)

Repository: `https://github.com/FormalizedFormalLogic/Foundation`

Contains:
- Propositional Tait calculus with completeness
- First-order sequent calculus with cut-elimination (Hauptsatz)
- Modal logic with Kripke/neighborhood semantics

The "Zoo" visualization of interrelationships between proof systems is a particularly useful
model for CSLib's own proof system hierarchy documentation.

### Missing `HasDia` (Direct Code Evidence)

File: `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Axioms.lean`, lines 147-183

Comments on `AxiomB`, `Axiom5`, `AxiomD` explicitly state:
> "Diamond is encoded classically as `◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`, since `HasDia` is not
> yet a primitive in `ModalConnectives`."

This is a known gap explicitly documented in the source code.

---

## Alternative Architectures Considered

### Alternative 1: Tait Calculus Instead of Two-Sided LK

**Description**: Use a one-sided calculus with signed formulas (like Tait 1968), where a
sequent is a set of "positive" and "negative" formulas equivalent to their disjunction being
true.

**Pros**: Avoids explicit left-right context management; natural for resolution-based methods.

**Cons**: Less familiar; does not match CSLib's ND style with left context + right conclusion.

**Verdict**: Two-sided LK is more appropriate for CSLib given the existing Hilbert + ND style.

### Alternative 2: Proof Terms as Lean Terms (Curry-Howard)

**Description**: Instead of a standalone `inductive Proof`, use Lean's own term language as
the proof system (the "propositions as types" approach).

**Pros**: Avoids reinventing proof theory; decidability follows from Lean kernel.

**Cons**: Does not give a metatheoretically studied proof system; cannot reason about proof
normalization as a property of the formalized system.

**Verdict**: Not appropriate for CSLib which needs standalone proof system formalization for
metalogic (soundness, completeness, cut-elimination).

### Alternative 3: Extend `Foundations/Logic/Metalogic/` with Generic Sequent Calculus

**Description**: Define a generic sequent calculus typeclass in `Foundations/` that can be
instantiated for propositional, modal, temporal, and bimodal logics.

**Pros**: Maximizes reuse across the logic hierarchy.

**Cons**: Generic enough to be hard to instantiate correctly; different logics have different
sequent rules (classical vs intuitionistic vs modal).

**Verdict**: Partially good. The `InferenceSystem` abstraction already handles the "plug in
your proof" layer. A generic `SequentCalculus` typeclass could handle structural rules
(weakening, contraction, exchange) but the logical rules must be per-logic.

### Alternative 4: Resolution Calculus

**Description**: Implement a resolution-based refutation system for classical propositional
logic (CNF + resolvent rule).

**Pros**: Directly yields a SAT solver framework; connects to Mathlib's LRAT infrastructure.

**Cons**: Resolution is not presented in terms of the `Proposition` syntax; requires
a CNF-normalization step; less educational value than LK.

**Verdict**: Lower priority than LK. Could be valuable as an automation backend (like Mathlib's
`Sat.FromLRAT`) rather than as a standalone proof system to study metalogically.

---

## Confidence Levels

| Claim | Confidence |
|-------|-----------|
| Mathlib has no standalone propositional logic formalization | High |
| Mathlib's `itauto` implements G4ip and is directly relevant | High |
| FormalizedFormalLogic/Foundation is the leading Lean 4 prior art | High |
| CLL's sequent calculus is a direct template for propositional LK | High |
| `HasDia` is missing and documented as a gap | High |
| Two-sided `Finset × Finset` LK is the best fit for CSLib style | High |
| Cut-elimination proof would require significant work (~500-800 lines) | Medium |
| G4ip (LJT) would enable a decidability tactic | Medium |
| Biconditional primitive `HasIff` should be added | Medium |
| Resolution calculus would be useful as automation backend | Low |

---

## Summary of Gaps Not Addressed by Teammate A

This research focused on **what could be borrowed or adapted** from outside CSLib:

1. **Mathlib G4ip architecture**: Proven design for a terminating propositional sequent calculus
   in Lean 4 -- the three-level stratification (`eager non-splitting` / `eager splitting` /
   `backtracking`) is directly applicable.

2. **CLL as internal template**: The CLL one-sided sequent calculus in CSLib itself is the
   cleanest starting point for a propositional sequent calculus -- same namespace conventions,
   same `InferenceSystem` abstraction, same multiset/finset context patterns.

3. **FormalizedFormalLogic/Foundation**: External reference for Lean 4 Tait calculus and
   first-order sequent calculus with cut-elimination -- can be studied but not directly imported
   (different library, different conventions).

4. **HasDia gap**: Not a structural absence but a documented TODO in the source code -- low
   effort fix with high correctness payoff for non-classical modal logics.

5. **Decidability**: The `BoolEvaluate` infrastructure in `Semantics/Bool.lean` is already
   90% of the way to `instance : Decidable (Tautology φ)` for finite atom types.
