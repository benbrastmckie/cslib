# Implementation Plan: Task #281

- **Task**: 281 - Complete the set of Hilbert derived structural rules
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/281_hilbert_derived_structural_rules/reports/01_hilbert-derived-rules.md
- **Artifacts**: plans/01_hilbert-derived-rules-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

All 10 required Hilbert derived rules (andI, andE1, andE2, orI1, orI2, orE, impI, impE, botE, dne) already exist across two files: `HilbertDerivedRules.lean` (14 rules) and `FromHilbert.lean` (7 rules). The gap is a naming inconsistency: `impI`, `impE`, and `botE` in `FromHilbert.lean` lack the `hilbert` prefix used by all rules in `HilbertDerivedRules.lean`. This plan adds 5 thin `hilbert`-prefixed wrappers to `HilbertDerivedRules.lean` for a uniform API surface, plus documents the existing `botEDeriv` in FromHilbert under the consistent name `hilbertBotEDeriv`.

### Research Integration

Key findings from `reports/01_hilbert-derived-rules.md`:
- All rules listed in the task description already exist as generic Hilbert derivations parameterized over arbitrary `Axioms` predicates
- The naming split between `FromHilbert.lean` (unprefixed: `impI`, `impE`, `botE`) and `HilbertDerivedRules.lean` (prefixed: `hilbertAndI`, `hilbertOrE`, etc.) creates an inconsistent API
- Option B (consolidation wrappers) is the right scope -- zero proof risk, all wrappers are 1-2 line delegations
- Tier-specific specializations (Option C) deferred to when Lindenbaum rebuild (tasks 282-285) reveals actual need

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Hilbert-primary Lindenbaum algebra rebuild (tasks 281-285), which supports the overall propositional logic infrastructure for all downstream modal, temporal, and bimodal metalogic.

## Goals & Non-Goals

**Goals**:
- Add `hilbertImpI` and `hilbertImpE` DerivationTree-level wrappers to `HilbertDerivedRules.lean`
- Add `hilbertImpIDeriv`, `hilbertImpEDeriv`, and `hilbertBotEDeriv` Deriv-level wrappers to `HilbertDerivedRules.lean`
- Verify all definitions compile with `lake build`
- Pass full CI pipeline (build, checkInitImports, lint-style, test)

**Non-Goals**:
- Tier-specific convenience lemmas (e.g., `MinPropAxiom.hilbertImpI`) -- deferred to task 282+
- Moving or refactoring definitions out of `FromHilbert.lean` -- the originals stay, wrappers alias them
- Adding `hilbertAssume` or `hilbertAxiomRule` wrappers -- these are primitive operations, not derived rules

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Name collision with existing definitions | L | L | Grep for `hilbertImpI` etc. before adding; research confirmed no conflicts |
| `noncomputable` propagation from `impI` | L | L | `hilbertImpI` wrapper marked `noncomputable` to match `impI` |
| Lint failures on new definitions | L | L | Add docstrings to all new definitions |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Add naming-consistency wrappers [NOT STARTED]

**Goal**: Add 5 `hilbert`-prefixed wrapper definitions to `HilbertDerivedRules.lean` that delegate to the existing unprefixed definitions in `FromHilbert.lean`.

**Tasks**:
- [ ] Add `hilbertImpI` (noncomputable, wraps `impI` from FromHilbert)
- [ ] Add `hilbertImpE` (wraps `impE` from FromHilbert)
- [ ] Add `hilbertImpIDeriv` (wraps `impIDeriv` from FromHilbert)
- [ ] Add `hilbertImpEDeriv` (wraps `impEDeriv` from FromHilbert)
- [ ] Add `hilbertBotEDeriv` (wraps `botEDeriv` from FromHilbert -- note: `hilbertBotE` already exists at DerivationTree level)
- [ ] Add docstrings to all 5 new definitions
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules`
- [ ] Run `lake test`
- [ ] Run `lake exe checkInitImports`
- [ ] Run `lake exe lint-style`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` - Add 5 new wrapper definitions before the `end` statement, in a new `/-! ## Naming Consistency Wrappers -/` section

**Exact definitions to add**:

```lean
/-! ## Naming Consistency Wrappers

The following definitions provide `hilbert`-prefixed aliases for rules
originally defined in `FromHilbert.lean` (`impI`, `impE`, `botEDeriv`),
ensuring a uniform naming convention across the Hilbert derived rules API. -/

/-- **Implication Introduction** (→I): From `A :: Γ ⊢ B`, derive `Γ ⊢ A → B`.
Alias for `impI` (the deduction theorem). -/
noncomputable def hilbertImpI
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms (A :: Γ) B) :
    DerivationTree Axioms Γ (A → B) :=
  impI h_K h_S d

/-- **Implication Elimination** (→E / Modus Ponens):
From `Γ ⊢ A → B` and `Γ ⊢ A`, derive `Γ ⊢ B`.
Alias for `impE`. -/
def hilbertImpE
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d₁ : DerivationTree Axioms Γ (A → B))
    (d₂ : DerivationTree Axioms Γ A) :
    DerivationTree Axioms Γ B :=
  impE d₁ d₂

/-- Implication introduction at the `Deriv` level.
Alias for `impIDeriv`. -/
theorem hilbertImpIDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h : Deriv Axioms (A :: Γ) B) :
    Deriv Axioms Γ (A → B) :=
  impIDeriv h_K h_S h

/-- Implication elimination at the `Deriv` level.
Alias for `impEDeriv`. -/
theorem hilbertImpEDeriv
    {Axioms : PL.Proposition Atom → Prop}
    {Γ : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (h₁ : Deriv Axioms Γ (A → B))
    (h₂ : Deriv Axioms Γ A) :
    Deriv Axioms Γ B :=
  impEDeriv h₁ h₂

/-- Ex falso quodlibet at the `Deriv` level.
Alias for `botEDeriv`. -/
theorem hilbertBotEDeriv
    {Axioms : PL.Proposition Atom → Prop}
    (h_EFQ : ∀ (φ : PL.Proposition Atom), Axioms (Proposition.bot.imp φ))
    {Γ : List (PL.Proposition Atom)}
    {A : PL.Proposition Atom}
    (h : Deriv Axioms Γ ⊥) :
    Deriv Axioms Γ A :=
  botEDeriv h_EFQ h
```

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` succeeds with no errors
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- All 5 new definitions have docstrings (no `docBlame` lint warnings)

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` compiles without errors
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes (Cslib.Init import check)
- [ ] `lake exe lint-style` passes (style linting)
- [ ] No `sorry` in any new definition (`lean_verify` or grep)
- [ ] Each new wrapper delegates to its FromHilbert counterpart (no reimplementation)

## Artifacts & Outputs

- `specs/281_hilbert_derived_structural_rules/plans/01_hilbert-derived-rules-plan.md` (this file)
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` (modified: 5 new definitions)

## Rollback/Contingency

Delete the added wrapper section from `HilbertDerivedRules.lean`. Since all additions are pure aliases with no downstream dependents yet, removal has zero impact on the existing codebase. If lint or build issues arise, check that `FromHilbert.lean` is properly imported (it already is via `public import`).
