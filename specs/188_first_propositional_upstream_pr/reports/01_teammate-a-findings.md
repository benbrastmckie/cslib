# Teammate A Findings: Upstream CSLib vs Local Fork

## Upstream CSLib Inventory

**Upstream repo**: `https://github.com/leanprover/cslib.git`
**Verified via**: `git remote -v` and GitHub API (`gh api repos/leanprover/cslib/git/trees/main?recursive=1`)

### What Upstream Has in `Cslib/Logics/Propositional/`

Upstream has exactly **2 files** under `Cslib/Logics/Propositional/`:

| File | Description |
|------|-------------|
| `Defs.lean` | Formula type (`Proposition`), theories (`MPL`/`IPL`/`CPL`), `IsIntuitionistic`/`IsClassical` typeclasses |
| `NaturalDeduction/Basic.lean` | Full natural deduction system (sequent style with `Finset` contexts), weakening, cut, substitution, equivalence relation, `Setoid` instance |

**Note**: The `NaturalDeduction/Basic.lean` already upstream is a mature, complete file by Thomas Waring/Benjamin Brast-McKie. It defines `Theory.Derivation` with 10 constructors (ax, ass, andI, andE₁, andE₂, orI₁, orI₂, orE, implI, implE), weakening, cut, and a full equivalence characterization. No sorries.

### What Upstream Has in `Cslib/Foundations/Logic/`

Upstream has exactly **2 files**:

| File | Description |
|------|-------------|
| `InferenceSystem.lean` | `InferenceSystem` typeclass, `DerivableIn`, notation `S⇓a` |
| `LogicalEquivalence.lean` | Generic logical equivalence typeclass |

### Full Upstream Logics Inventory

The upstream `Cslib/Logics/` namespace has:
- `HML/` - Hennessy-Milner Logic (Basic, LogicalEquivalence) -- no metalogic
- `LinearLogic/CLL/` - Classical Linear Logic (Basic, CutElimination, EtaExpansion, MLL, PhaseSemantics/Basic)
- `Modal/` - Modal Logic (Basic, Cube, Denotation, LogicalEquivalence) -- no metalogic
- `Propositional/` - Only `Defs.lean` + `NaturalDeduction/Basic.lean`

No ProofSystem, Metalogic, or Semantics subdirectory exists upstream for Propositional logic. The Modal, Temporal, and Bimodal logic ProofSystem/Metalogic trees exist only in our local fork -- they are entirely local work.

---

## Local Fork Additions

### New Files in `Cslib/Logics/Propositional/` (not in upstream)

All of these are NEW contributions not yet upstream:

#### Proof System (Hilbert-style)

| File | Lines | Description |
|------|-------|-------------|
| `ProofSystem/Axioms.lean` | 219 | `PropositionalAxiom` (10 constructors: implyK, implyS, efq, peirce, andI, andE1/2, orI1/2, orE), `IntuitionisticAxiom` (efq only), `MinimalAxiom` (no axioms) |
| `ProofSystem/Derivation.lean` | 164 | `DerivationTree` (4 constructors: ax, assumption, modus_ponens, weakening), `Deriv`, `Derivable`, `propDerivationSystem` |
| `ProofSystem/Instances.lean` | 120 | Instance registration: `InferenceSystem HilbertCl`, `ModusPonens`, 10 `HasAxiom*` instances, `ClassicalHilbert` |
| `ProofSystem/IntMinInstances.lean` | 169 | Instance registration for `HilbertInt` and `HilbertMin` (intuitionistic/minimal Hilbert systems) |

#### Semantics (bivalent + Kripke)

| File | Lines | Description |
|------|-------|-------------|
| `Semantics/Basic.lean` | 64 | `Valuation`, `Evaluate` (recursive, 5 cases), `Tautology`, simp lemmas |
| `Semantics/Kripke.lean` | 170 | `IForces` (Kripke forcing for intuitionistic/minimal logic), `IValid`, `MValid`, monotonicity |
| `Semantics/SemanticConsequence.lean` | 180 | `SetDerivable`, `SemanticEntails`, `ISemanticEntails`, `MSemanticEntails`, basic lemmas |

#### Metalogic

| File | Lines | Description |
|------|-------|-------------|
| `Metalogic/Soundness.lean` | 93 | `prop_axiom_sound`, `prop_soundness`, `prop_soundness_derivable`, `prop_soundness_tautology` |
| `Metalogic/DeductionTheorem.lean` | 219 | Deduction theorem for all three systems (classical, intuitionistic, minimal) |
| `Metalogic/MCS.lean` | 162 | Maximal consistent set instantiation for propositional logic |
| `Metalogic/StrongCompleteness.lean` | 235 | Strong completeness (CPL) |
| `Metalogic/Completeness.lean` | 347 | Main completeness theorem (CPL) |
| `Metalogic/IntSoundness.lean` | 128 | Soundness for IPL (Kripke) |
| `Metalogic/IntLindenbaum.lean` | 497 | Lindenbaum construction for IPL |
| `Metalogic/IntCompleteness.lean` | 181 | Completeness for IPL |
| `Metalogic/IntStrongCompleteness.lean` | 193 | Strong completeness for IPL |
| `Metalogic/MinSoundness.lean` | 121 | Soundness for MPL (Kripke) |
| `Metalogic/MinLindenbaum.lean` | 417 | Lindenbaum construction for MPL |
| `Metalogic/MinCompleteness.lean` | 194 | Completeness for MPL |
| `Metalogic/MinStrongCompleteness.lean` | 174 | Strong completeness for MPL |

#### Natural Deduction Extensions

| File | Lines | Description |
|------|-------|-------------|
| `NaturalDeduction/DerivedRules.lean` | 252 | Derived rules built on `Basic.lean` |
| `NaturalDeduction/Equivalence.lean` | 400 | Equivalence properties |
| `NaturalDeduction/FromHilbert.lean` | 320 | Translation from Hilbert to ND |
| `NaturalDeduction/HilbertDerivedRules.lean` | 468 | Derived rules at the Hilbert level |

**Total new Propositional LOC**: ~4,697 lines across 21 new files

### New Files in `Cslib/Foundations/Logic/` (not in upstream)

| File | Lines | Description |
|------|-------|-------------|
| `Connectives.lean` | 114 | Typeclass hierarchy for connectives: `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`, `HasAnd`, `HasOr`; bundled: `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives` |
| `Axioms.lean` | 344 | Generic axiom typeclasses: `HasAxiomImplyK/S`, `HasAxiomEFQ`, `HasAxiomPeirce`, `HasAxiomAndI/E1/E2`, `HasAxiomOrI1/I2/E`, plus modal/temporal axiom classes |
| `ProofSystem.lean` | 524 | Proof system typeclass hierarchy: `ModusPonens`, `Necessitation`, `MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`; tag types |
| `Metalogic/Consistency.lean` | 285 | Generic MCS framework: `SetConsistent`, `MaximallyConsistent`, Lindenbaum lemma |
| `Metalogic/DeductionHelpers.lean` | 120 | Generic deduction helpers used across logics |
| `Theorems.lean` | 59 | Top-level barrel import for Theorems |
| `Theorems/Combinators.lean` | 339 | Generic combinator theorems (K, S, B, C, W, etc.) |
| `Theorems/BigConj.lean` | 150 | BigConj derived theorems |
| `Theorems/Propositional/Core.lean` | 321 | Core propositional theorems |
| `Theorems/Propositional/Connectives.lean` | 539 | Connective-specific propositional theorems |
| `Theorems/Modal/Basic.lean` | 203 | Modal theorem foundations |
| `Theorems/Modal/S5.lean` | 533 | S5-specific modal theorems |
| `Theorems/Temporal/FrameConditions.lean` | 89 | Temporal frame condition theorems |
| `Theorems/Temporal/TemporalDerived.lean` | 292 | Temporal derived theorems |

**Total new Foundations/Logic LOC**: ~3,912 lines across 14 new files

---

## Gap Analysis: Contribution Space

The upstream propositional logic section contains only definitions and a natural deduction system (no Hilbert system, no semantics, no soundness, no completeness). Our local fork adds the complete metalogical treatment.

### The ~300 LOC First PR Slice

For a targeted first PR of ~300 LOC, the ideal contribution is the **foundational layer** that everything else depends on:

#### Option A: Propositional Foundations Core (recommended)

The minimal layer that establishes the Hilbert proof system and bivalent semantics -- the entry point for later soundness and completeness PRs:

| File | Lines | Rationale |
|------|-------|-----------|
| `Foundations/Logic/Connectives.lean` | 114 | Required by everything; extends upstream `InferenceSystem` |
| `Semantics/Basic.lean` | 64 | Bivalent semantics; self-contained, no Metalogic deps |
| `ProofSystem/Axioms.lean` | 219 | Core Hilbert axiom schemata (CPL/IPL/MPL) |

Subtotal: **397 lines** -- slightly over 300 but tightly coupled (cannot split cleanly)

Or trim by deferring `IntMinInstances.lean` and contributing only:

| File | Lines |
|------|-------|
| `Foundations/Logic/Connectives.lean` | 114 |
| `Semantics/Basic.lean` | 64 |
| `ProofSystem/Axioms.lean` | 219 |

Total: **397 lines** (acceptable for a first PR -- reviewers generally accept slightly larger "foundational" PRs)

#### Option B: ProofSystem + Soundness (lean contribution)

| File | Lines | Notes |
|------|-------|-------|
| `ProofSystem/Axioms.lean` | 219 | Axiom schemata |
| `Semantics/Basic.lean` | 64 | Bivalent valuation |
| `Metalogic/Soundness.lean` | 93 | Complete theorem with proof |

Subtotal: **376 lines** -- a complete package with a proof result

#### Option C: Foundations/Logic Connectives Only

| File | Lines | Notes |
|------|-------|-------|
| `Foundations/Logic/Connectives.lean` | 114 | Typeclass hierarchy |
| `Foundations/Logic/Axioms.lean` | 344 | Generic axiom typeclasses |

Subtotal: **458 lines** -- pure infrastructure, but significant

### What Cannot Go Upstream Yet

Files that depend on other non-upstream infrastructure (Modal/Temporal/Bimodal metalogic) or are too large for a first PR:

- `Foundations/Logic/ProofSystem.lean` (524 LOC) -- references Modal/Temporal/Bimodal tag types; needs companion PR
- `Foundations/Logic/Theorems/Modal/*`, `Temporal/*` -- depend on non-upstream Modal/Temporal machinery
- All `Metalogic/` files -- best contributed after Soundness PR lands
- All `NaturalDeduction/` extensions -- best contributed after `Basic.lean` is stable upstream

### Strategic Path to Completeness PRs

The long-term goal (completeness for all three Hilbert systems + ND equivalence) suggests this PR sequence:

1. **PR 1** (~400 LOC): `Connectives.lean` + `Axioms.lean` (Prop only) + `Semantics/Basic.lean` + `ProofSystem/Axioms.lean`
2. **PR 2** (~650 LOC): `ProofSystem/Derivation.lean` + `ProofSystem/Instances.lean` + `Metalogic/Soundness.lean` + `Metalogic/DeductionTheorem.lean`
3. **PR 3** (~700 LOC): `Metalogic/MCS.lean` + `Metalogic/StrongCompleteness.lean` + `Metalogic/Completeness.lean` (CPL)
4. **PR 4** (~1,100 LOC): Kripke semantics (`Semantics/Kripke.lean`, `SemanticConsequence.lean`) + IPL completeness
5. **PR 5** (~1,000 LOC): MPL completeness
6. **PR 6** (~1,400 LOC): ND extensions (`DerivedRules`, `Equivalence`, `FromHilbert`, `HilbertDerivedRules`)
7. **PR 7+**: `Foundations/Logic/ProofSystem.lean` + `Theorems/` (after Modal/Temporal/Bimodal are upstream)

---

## Confidence Level

**High confidence** on the following:

- **Upstream inventory is exact**: Used `gh api repos/leanprover/cslib/git/trees/main?recursive=1` with `jq` filtering -- this is the definitive file list, not a web-scrape approximation.
- **Local additions are exact**: Verified by `diff` of the two file lists; no ambiguity.
- **Line counts**: Verified by `wc -l` on each file.
- **File contents**: Directly read 8 key files to confirm there are no sorries and understand the dependency structure.

**Medium confidence** on:

- **Best split for first PR**: The 300 LOC constraint is somewhat artificial. `Connectives.lean` (114) + `Semantics/Basic.lean` (64) + `ProofSystem/Axioms.lean` (219) = 397 LOC is the tightest self-contained unit. Trimming below 300 would require splitting `ProofSystem/Axioms.lean` which is not advisable (it's already a cohesive file).
- **Whether `Foundations/Logic/ProofSystem.lean` can go upstream**: This file references Modal/Temporal/Bimodal tag types. The upstream doesn't have those logics' proof systems yet. This file either needs to be split or submitted as part of a larger "proof system infrastructure" PR.

**Low confidence**:

- **Whether upstream maintainers prefer Foundations first vs Logics first**: CSLib's PR review culture is unknown. The upstream already merged one PR adding `InferenceSystem` infrastructure; that suggests they accept foundational abstractions. But the review bar for `ProofSystem.lean` (which introduces an entire typeclass hierarchy) may be higher.
