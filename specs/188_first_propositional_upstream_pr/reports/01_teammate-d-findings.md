# Teammate D (Horizons) Findings: PR Strategy and Contribution Roadmap

## Overview

This report designs a multi-PR roadmap for contributing propositional logic foundations to CSLib
upstream. It studies the contribution model, analyzes the dependency structure, and recommends
a staged sequence of PRs from a ~300 LOC first PR through the full contribution.

---

## Context: What Upstream Has vs. What We Have

### Upstream CSLib State (as of `upstream/main`)

Upstream contains only two propositional files:
- `Cslib/Logics/Propositional/Defs.lean` (154 lines, Thomas Waring, original)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (partial, upstream version)

And in `Foundations/Logic/`:
- `Cslib/Foundations/Logic/InferenceSystem.lean` (Fabrizio Montesi, upstream)
- `Cslib/Foundations/Logic/LogicalEquivalence.lean` (Fabrizio Montesi, upstream)

### What We Have Added (not in upstream)

The local fork adds approximately **10,100 LOC** across two subsystems:

**Foundations/Logic additions** (~2,795 LOC in 10 new files):
| File | LOC |
|------|-----|
| `Connectives.lean` | 114 |
| `Axioms.lean` | 344 |
| `ProofSystem.lean` | 524 |
| `Theorems.lean` (barrel) | 59 |
| `Theorems/Combinators.lean` | 339 |
| `Theorems/Propositional/Core.lean` | 321 |
| `Theorems/Propositional/Connectives.lean` | 539 |
| `Theorems/BigConj.lean` | 150 |
| `Metalogic/Consistency.lean` | 285 |
| `Metalogic/DeductionHelpers.lean` | 120 |

**Logics/Propositional additions** (~6,086 LOC across 26 files, including modifications to 3 upstream files):
| File | LOC |
|------|-----|
| `Defs.lean` (modified, +85 lines) | 204 |
| `ProofSystem/Axioms.lean` | 219 |
| `ProofSystem/Derivation.lean` | 164 |
| `ProofSystem/Instances.lean` | 120 |
| `ProofSystem/IntMinInstances.lean` | 169 |
| `Semantics/Basic.lean` | 64 |
| `Semantics/Kripke.lean` | 170 |
| `Semantics/SemanticConsequence.lean` | 180 |
| `NaturalDeduction/Basic.lean` (modified, +83 lines) | 395 |
| `NaturalDeduction/DerivedRules.lean` | 252 |
| `NaturalDeduction/FromHilbert.lean` | 320 |
| `NaturalDeduction/HilbertDerivedRules.lean` | 468 |
| `NaturalDeduction/Equivalence.lean` | 400 |
| `Metalogic/DeductionTheorem.lean` | 219 |
| `Metalogic/MCS.lean` | 162 |
| `Metalogic/Soundness.lean` | 93 |
| `Metalogic/StrongCompleteness.lean` | 235 |
| `Metalogic/Completeness.lean` | 347 |
| `Metalogic/MinSoundness.lean` | 121 |
| `Metalogic/MinLindenbaum.lean` | 417 |
| `Metalogic/MinStrongCompleteness.lean` | 174 |
| `Metalogic/MinCompleteness.lean` | 194 |
| `Metalogic/IntSoundness.lean` | 128 |
| `Metalogic/IntLindenbaum.lean` | 497 |
| `Metalogic/IntStrongCompleteness.lean` | 193 |
| `Metalogic/IntCompleteness.lean` | 181 |

### Key Architectural Change vs. Upstream

Our `Defs.lean` makes a significant change to the upstream `Proposition` type. Upstream uses:
```
{atom, and, or, impl}  -- no primitive bot; negation requires a Bot Atom instance
```

We use:
```
{atom, bot, imp, and, or}  -- primitive bot; uniform 5-primitive system
```

This change — adding `bot` and `imp` as primitives, renaming `impl` to `imp`, removing the
`Bot Atom` instance dependency — is the central design decision that must be discussed with
upstream maintainers (fmontesi, arademaker) before any PR can land. PR #635 (per task 171
research) apparently proposed a 3-primitive version `{atom, bot, imp}` which was rejected
due to ctchou's objection that and/or are not definable intuitionistically from {imp, bot}.
Our current architecture with `{atom, bot, imp, and, or}` is the resolution of that debate.

---

## CSLib Contribution Model

### What CONTRIBUTING.md Says

Key requirements:
1. **PRs need at least one maintainer approval** — logic area reviewers are `@arademaker` and `@fmontesi`
2. **PR titles** must start with: `feat|fix|doc|style|refactor|test|chore|perf[(<area>)]: <description>`
3. **For major development**, discussion on Zulip or via GitHub issue is **strongly recommended first**
4. **CI pipeline** must pass: `lake test`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`, `lake exe mk_all --module`
5. **AI disclosure** is required in the PR description (following Mathlib policy)
6. **Reuse focus**: new definitions should instantiate existing abstractions

### Comparison with Mathlib

CSLib does NOT have a formal RFC process. The model is:
- For small/medium contributions: submit PR directly
- For major new frameworks: post on Zulip first
- "Working groups" are informal; can be proposed with a short Zulip message

This means our contribution does NOT require a formal RFC, but a **Zulip post** before the
first PR is strongly advisable given that we are:
(a) modifying an existing upstream file (`Defs.lean`) in a breaking way
(b) adding a completely new infrastructure layer (`Foundations/Logic/`)

### Existing PR Context: PR #635 and PR #607

From task 171 research:
- **PR #635**: An earlier attempt to add propositional logic with `{atom, bot, imp}` as the
  three-primitive basis. Rejected/stalled because ctchou (a reviewer) correctly pointed out
  that `{imp, bot}` is not functionally complete for intuitionistic logic. Our current five-
  primitive `{atom, bot, imp, and, or}` architecture resolves this objection.
- **PR #607**: Fabrizio Montesi's own PR proposing per-operator typeclass files (Operators/
  directory). This inspired our `Connectives.lean` design. The PR may set expectations about
  the typeclass approach.
- **Reviewer chenson2018's concern** (from PR #607 review): simp/grind lemmas being "backwards"
  in direction — needs attention when writing lemmas.

The CODEOWNERS file confirms: `@arademaker @fmontesi` for both `Foundations/Logic/` and
`Logics/`. Both must approve.

---

## Foundations/Logic Dependency Analysis

### The Dependency Question

A critical question: should the `Foundations/Logic/` infrastructure (Connectives, Axioms,
ProofSystem, Theorems, Metalogic) be a **separate PR** that lands first, or should it be
included inline with the first Propositional PR?

### Analysis

The `Foundations/Logic/` files are designed to be shared across:
- Propositional logic (immediately)
- Modal logic (Theorems/Modal/ already exists in our fork)
- Temporal logic (Theorems/Temporal/ already exists in our fork)
- Bimodal logic (downstream)

This is the entire rationale for the `Foundations/` level: it is infrastructure, not logic-specific.
Submitting `Foundations/Logic/` inline with Propositional would:
1. Make PR #1 harder to review (two separate concerns in one PR)
2. Miss the opportunity to get Foundations reviewed independently
3. Make subsequent Modal/Temporal PRs awkward (they would depend on our earlier Propositional PR
   even though Foundations is conceptually independent)

**Recommendation**: Submit `Foundations/Logic/` as **PR 0** (a prerequisite PR), separate from
the propositional contribution. This also gives fmontesi/arademaker a chance to review the
typeclass hierarchy (which relates directly to PR #607's design) before it becomes load-bearing.

### However: The `Defs.lean` Change Complicates This

The central complication is that our change to `Defs.lean` (adding `bot` and `imp` as primitives,
removing the `Bot Atom` instance dependency for `neg`) is a **breaking change to an existing upstream
file**. It affects the `Proposition` inductive type, which is already used in upstream
`NaturalDeduction/Basic.lean`.

This means PR 1 cannot simply add new files — it must also modify two existing upstream files.
The logical sequence is:

- Discuss on Zulip first (describe the 5-primitive design and its rationale)
- PR 0: `Foundations/Logic/Connectives.lean` (the typeclass hierarchy — directly related to PR #607)
- PR 1: Modified `Defs.lean` + `NaturalDeduction/Basic.lean` changes + first new files

---

## Contribution Roadmap

### Pre-PR: Zulip Discussion (Required)

Before any PR, post to the CSLib Zulip (#logic channel) describing:
1. The proposed 5-primitive formula type `{atom, bot, imp, and, or}` (resolving PR #635 concern)
2. The `Foundations/Logic/` typeclass infrastructure (building on PR #607 direction)
3. The full roadmap (3 logics, soundness/completeness for all three)
4. Ask for Zulip feedback before submitting

This is "strongly recommended" per CONTRIBUTING.md for major new frameworks.

### PR 0: Connective Typeclass Infrastructure (~115 LOC)

**Files**: `Cslib/Foundations/Logic/Connectives.lean` (new, 114 lines)

**Content**:
- `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`, `HasUntil`, `HasSince` — per-operator classes
- `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives` — bundled classes
- References to Johansson 1937, Wajsberg 1938, McKinsey 1939

**Why separate**: This is the typeclass hierarchy that Montesi's PR #607 was building toward.
Submitting it first invites his feedback on the design before it is used in downstream files.

**Enables**: Everything downstream that uses `HasBot`, `HasImp`, etc.

**Approximate review difficulty**: Low-medium (pure typeclasses, no proofs, easy to review)

### PR 1: Core Proposition Type Revision (~300 LOC)

**Files**:
- Modified `Cslib/Logics/Propositional/Defs.lean` (+85 lines of additions, total 204 lines)
- Modified `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (+83 lines of additions, total 395 lines)
- New `Cslib/Foundations/Logic/Axioms.lean` (344 lines — but only first ~100 lines may be needed)

Actually let's count what makes sense for a ~300 LOC scope:
- `Defs.lean` additions: ~85 lines (five primitives, prop instances, MPL/IPL/CPL abbreviations, architecture docstring)
- `NaturalDeduction/Basic.lean` additions: ~83 lines (updated constructors for 5-primitive type, theory-parametric ND)
- Totaling ~168 lines of modifications to existing files

To reach ~300 LOC, add the most foundational new file:
- `Cslib/Foundations/Logic/Axioms.lean` (first ~130 lines covering `ImplyK`, `ImplyS`, `EFQ`, `Peirce` axiom definitions)

**Total: ~300 LOC**

**Content**:
- Updated `Proposition` type with 5 primitives `{atom, bot, imp, and, or}`
- Updated `NaturalDeduction/Basic.lean` with 10 primitive rules (and/or intro/elim + imp intro/elim, theory-parametric)
- Foundational axiom definitions (`ImplyK`, `ImplyS`, `EFQ`, `Peirce` and connective axioms) at typeclass level

**Why this scope**: The `Proposition` type change is the central breaking change that enables
everything downstream. The reviewers (fmontesi, arademaker) need to evaluate this design
decision first. Keeping this PR small and focused gives them something easy to review that
establishes the architectural foundation.

**Key reviewer messages**:
- This resolves ctchou's PR #635 objection by making `and`/`or` primitive constructors
- The 5-primitive system supports genuine minimal, intuitionistic, and classical ND without any `[IsClassical T]` constraints on and/or rules
- The `NaturalDeduction/Basic.lean` ND is fully parametric: theory controls logic strength (MPL=∅, IPL=EFQ, CPL=DNE)

**Dependencies**: PR 0 (Connectives.lean) should land first.

### PR 2: Hilbert Proof System + Bivalent Semantics (~600 LOC)

**Files**:
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` (219 lines)
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` (164 lines)
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` (120 lines)
- `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean` (169 lines)
- `Cslib/Logics/Propositional/Semantics/Basic.lean` (64 lines)
- `Cslib/Foundations/Logic/ProofSystem.lean` (first ~100 lines: `MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert`)

**Total: ~836 LOC** (too large for one PR; split as needed)

**Content**:
- `PropositionalAxiom` inductive type (10 schemata)
- `MinPropAxiom`, `IntPropAxiom`, `ClassicalPropAxiom` hierarchy  
- `DerivationTree` and `Derivable` predicates
- Proof system instances (`HilbertMin`, `HilbertInt`, `HilbertCl`)
- Bivalent `Valuation`, `Evaluate`, `Tautology`

**Enables**: Soundness theorems, completeness theorems, semantic consequence.

**Approximate review difficulty**: Medium (many definitions, clear hierarchy)

### PR 3: Classical Soundness and Completeness (~600 LOC)

**Files**:
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` (339 lines)
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` (285 lines)
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` (93 lines)
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` (219 lines)
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` (162 lines)

**Total: ~1,098 LOC** (split across two PRs as needed)

**Content**:
- Hilbert combinator theorems (K, S, etc.) at typeclass level
- Generic `SetConsistent`, `SetMaximalConsistent`, `SetLindenbaum` (Zorn's lemma)
- Classical soundness: `prop_axiom_sound`, `prop_sound`
- Deduction theorem for all three logic strengths
- MCS theory: `mcs_complete`, `mcs_maximal`, `mcs_lindenbaum`

**Enables**: The completeness PRs.

### PR 4: Classical Strong Completeness (~600 LOC)

**Files**:
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` (235 lines)
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` (347 lines)
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` (321 lines)
- `Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` (539 lines, partial)

**Total: ~1,442 LOC** (needs splitting)

**Content**:
- Strong completeness: every consistent set is satisfiable (`strongly_complete`)
- Completeness theorem: every tautology is derivable in HilbertCl
- Core propositional theorems (weakening, transitivity, deduction, etc.) at typeclass level
- Connective-specific theorems (and/or rules, De Morgan, etc.)

**Enables**: Strong completeness is the capstone of classical propositional logic.

### PR 5: Natural Deduction Extensions + ND/Hilbert Equivalence (~1,500 LOC)

**Files**:
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` (252 lines)
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` (468 lines)
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` (320 lines)
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (400 lines)
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` (120 lines)

**Total: ~1,560 LOC**

**Content**:
- Derived ND rules (weakening, cut, contraction, etc.)
- Hilbert-derived rules via ND intermediate
- ND → Hilbert translation (each ND constructor maps to a Hilbert derivation)
- Hilbert → ND translation
- Equivalence theorems: `hilbert_iff_nd` for all three logic strengths (minimal, intuitionistic, classical)
  in both closed-context and context-based forms

**Enables**: Seamless interop between proof styles; foundation for cut-elimination direction.

### PR 6: Kripke Semantics + Minimal/Intuitionistic Soundness and Completeness (~2,500 LOC)

**Files**:
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` (170 lines)
- `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` (180 lines)
- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` (121 lines)
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` (417 lines)
- `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` (174 lines)
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` (194 lines)
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` (128 lines)
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` (497 lines)
- `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` (193 lines)
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` (181 lines)

**Total: ~2,255 LOC**

**Content**:
- `KripkeFrame`, `KripkeModel`, `IForces` (persistent forcing relation on preorders)
- `SemanticConsequence` for all three logics
- Minimal soundness: every HilbertMin theorem is forced in all Kripke models
- Minimal Lindenbaum: MCS extension theorem for minimal logic
- Minimal strong completeness and completeness
- Intuitionistic soundness (forced ↔ in-IPL)
- Intuitionistic Lindenbaum (more complex: requires IPL-specific MCS properties)
- Intuitionistic strong completeness and completeness

**Enables**: Completes the three-logic metatheory.

---

## PR Sequence Summary

| PR | Title | Files | LOC | Enables |
|----|-------|-------|-----|---------|
| Pre | Zulip discussion | — | — | Maintainer alignment |
| 0 | `feat(Foundations/Logic): connective typeclass hierarchy` | 1 new | ~115 | Downstream imports |
| 1 | `feat(Logics/Propositional): five-primitive formula type and theory-parametric natural deduction` | 2 modified | ~300 | Everything propositional |
| 2 | `feat(Logics/Propositional): Hilbert proof system and bivalent semantics` | ~6 new | ~500 | Soundness/completeness |
| 3 | `feat(Logics/Propositional): classical soundness, deduction theorem, and MCS foundations` | ~5 new | ~600 | Completeness |
| 4 | `feat(Logics/Propositional): classical strong completeness` | ~3 new | ~600 | Capstone classical |
| 5 | `feat(Logics/Propositional): natural deduction extensions and Hilbert-ND equivalence` | ~5 new | ~1,500 | ND/Hilbert bridge |
| 6 | `feat(Logics/Propositional): Kripke semantics and minimal/intuitionistic completeness` | ~10 new | ~2,255 | Capstone Int/Min |

**Total LOC across all PRs**: ~5,870 LOC for propositional, ~2,795 LOC for Foundations.
(Foundations/Logic PRs can interleave with Propositional PRs as they become needed.)

---

## PR Description Strategy

### PR 1 Description Template

```
feat(Logics/Propositional): five-primitive formula type and theory-parametric natural deduction

This PR revises the `Proposition` type to use five primitives `{atom, bot, imp, and, or}`,
following the standard Gentzen/Prawitz/Troelstra-van Dalen tradition, and updates the
natural deduction system to be fully theory-parametric over three logic strengths.

## Changes

### `Cslib/Logics/Propositional/Defs.lean`

- Adds `bot` (falsum) and `imp` (implication) as primitive constructors.
  `and` and `or` were already primitive (Thomas Waring's original design).
  This resolves the limitation noted in [#635] where ctchou pointed out that `{imp, bot}`
  alone is not functionally complete for intuitionistic logic — `and`/`or` are
  genuinely independent connectives intuitionistically (Wajsberg 1938, McKinsey 1939).
- `neg`, `top`, and `iff` remain `abbrev`s rather than constructors:
  `neg φ := φ → ⊥`, `top := ⊥ → ⊥`, `iff φ ψ := (φ → ψ) ∧ (ψ → φ)`.
- Adds `Theory.MPL`/`IPL`/`CPL` abbreviations for the three logic strengths.
- Adds `IsIntuitionistic` and `IsClassical` typeclasses.
- Registers `Proposition` as an instance of `PropositionalConnectives` (from `Foundations/Logic/Connectives.lean`, PR [#XXX]).

### `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`

- 10 primitive constructors: axiom, assumption, conjunction intro/elim ×2, disjunction
  intro ×2 and elimination, implication intro/elim. Ex falso quodlibet (`botE`) is a *derived*
  rule requiring `[IsIntuitionistic T]`.
- Logic strength is controlled by the `Theory T` parameter:
  `MPL` (Johansson's minimal logic [Johansson1937]), `IPL` (intuitionistic), `CPL` (classical).
- Renames upstream `implI`/`implE` to `impI`/`impE` for consistency with `imp` constructor name.

### `Cslib/Foundations/Logic/Axioms.lean` (partial, first N lines)

- Polymorphic axiom `abbrev`s (`ImplyK`, `ImplyS`, `EFQ`, `Peirce`) at `HasBot`/`HasImp` typeclass level.

## Design Notes

The five-primitive type enables:
1. Genuine minimal logic ND (botE is not available without `[IsIntuitionistic T]`)
2. Genuine intuitionistic ND (all and/or rules are primitive, not classical abbreviations)
3. Classical ND adds DNE via theory parameter

This is the standard approach in Gentzen 1935, Prawitz 1965, and Troelstra & van Dalen 1988.
The natural deduction style follows §10.4 of Troelstra & van Dalen (sequent-style with
explicit hypotheses), as in Thomas Waring's original design.

## Roadmap

This PR is the first in a series contributing propositional logic foundations:

- PR 1 (this): Formula type and theory-parametric ND (foundation)
- PR 2: Hilbert proof system (`PropositionalAxiom`, `Derivable`) and bivalent semantics
- PR 3: Classical soundness, deduction theorem, and MCS foundations
- PR 4: Classical strong completeness
- PR 5: Natural deduction derived rules and Hilbert-ND equivalence for all three logics
- PR 6: Kripke semantics and soundness/completeness for minimal and intuitionistic logics

## AI Disclosure

This formalization was developed with assistance from Claude (Anthropic) as a pair-programming
tool for proof search and code generation. The mathematical content, proofs, and design decisions
were verified and approved by the author. The AI was used to speed up the mechanical parts of
proof writing (tactic search, boilerplate). Claude's tool-specific tendencies (preferring certain
tactic combinations, sometimes generating suboptimal term structure) have been reviewed and
corrected where identified.

## References

- [Johansson1937]: I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*
- [Gentzen1935]: G. Gentzen, *Untersuchungen über das logische Schließen*
- [Prawitz1965]: D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*
- [TroelstraVanDalen1988]: A. S. Troelstra, D. van Dalen, *Constructivism in Mathematics*, Vol. 1
- [McKinsey1939]: J. C. C. McKinsey, *Proof of the Independence of the Primitive Symbols of Heyting's Calculus*
- [Wajsberg1938]: M. Wajsberg, *Untersuchungen über den Aussagenkalkül von A. Heyting*
```

### Key Points for the Description

1. **Acknowledge PR #635** explicitly — show awareness of the prior review and explain how this
   design resolves ctchou's objection. This demonstrates continuity and responsiveness.

2. **Reference PR #607 direction** — fmontesi's PR #607 proposed per-operator typeclass files.
   Our `Connectives.lean` builds on that direction. Framing our work as aligned with, not
   competing with, his approach is strategically important.

3. **Include the roadmap in every PR** — reviewers need to understand what they are accepting
   and what follows. A clear 6-PR roadmap shows planning and gives them a way to evaluate
   each PR's scope.

4. **AI disclosure is mandatory** — CONTRIBUTING.md follows Mathlib's AI policy. Must include
   which tools and how they were used. Reviewers can then look for specific error patterns.

5. **Cite literature in each PR** — CSLib requires documentation referencing published resources.
   Every PR should have a References section in the PR description, not just in the files.

---

## What the First PR Must NOT Include

Given the ~300 LOC constraint and the need to get PR 0 and PR 1 through review:

- Do NOT include `ProofSystem.lean`, `Axioms.lean` (beyond minimal), or `Theorems/`
- Do NOT include any completeness or soundness proofs
- Do NOT include the Kripke semantics or semantic consequence
- Do NOT include the `NaturalDeduction/Equivalence.lean` or `FromHilbert.lean`
- Do NOT include the `Metalogic/` files
- Do NOT include `Foundations/Logic/` beyond `Connectives.lean` (PR 0) and minimal `Axioms.lean`

The first PR should be just coherent enough to demonstrate the design and invite discussion,
not large enough to overwhelm reviewers with review burden.

---

## Risk Analysis

### Risk 1: Maintainer Rejects 5-Primitive Type

The upstream `Defs.lean` uses 4 constructors `{atom, and, or, impl}` (no primitive `bot`).
Our change adds `bot` and `imp` while keeping `and`/`or` as primitives. If fmontesi prefers
reverting to 4 primitives or a different naming convention (`impl` vs `imp`), that would
require reworking downstream files.

**Mitigation**: Zulip discussion first. Explicitly reference task 171 research findings and
the ctchou/PR #635 debate. The 5-primitive case has strong literature backing.

### Risk 2: PR #607 Lands With Incompatible Design

If Montesi's PR #607 (Operators/ approach) is merged before our PRs, our `Connectives.lean`
design may need adjustment.

**Mitigation**: Submit PR 0 (`Connectives.lean`) early and reference PR #607 direction explicitly.
The two approaches (our bundled classes vs his per-operator files) are complementary, not competing.

### Risk 3: Review Queue Delay

With only fmontesi and arademaker as logic area maintainers, review timelines may be slow.

**Mitigation**: Post on Zulip to gauge interest and establish timeline expectations. Small PR sizes
(~300 LOC for PR 1) reduce review burden.

### Risk 4: CI Failures on Our Modifications

Our changes to `Defs.lean` and `NaturalDeduction/Basic.lean` may break CI for existing
modal logic files that import from propositional (the modal `Proposition` type is separate,
but the ND type is used by `LogicalEquivalence.lean` which Montesi maintains).

**Mitigation**: Verify full `lake build` passes before PR submission. The most recent upstream
commit (d6c0b903) is `chore: bump mathlib to 8589236`. We need to ensure our fork is rebased
on that commit and CI is green.

---

## Confidence Level

| Finding | Confidence |
|---------|------------|
| PR 0 (`Connectives.lean`) should be separate | High |
| Zulip discussion needed before any PR | High |
| ~300 LOC scope for PR 1 is right | High |
| PR 1 = `Defs.lean` + `NaturalDeduction/Basic.lean` + minimal `Axioms.lean` | High |
| 6-PR roadmap sequence is correct | Medium (depends on review feedback, may merge PRs) |
| fmontesi/arademaker are the relevant reviewers | High (confirmed by CODEOWNERS) |
| AI disclosure is mandatory | High (CONTRIBUTING.md is explicit) |
| PR description should reference PR #635 resolution | High |
| Risk of breaking `Modal/LogicalEquivalence.lean` is low | Medium |

---

## Alignment with specs/ROADMAP.md

The existing ROADMAP describes the full formalization goal:

```
Foundations at top → Propositional as shared sub-logic → Modal + Temporal as peers → Bimodal at bottom
```

The contribution roadmap in this report follows the same dependency order, submitting
Foundations first, then Propositional, then (in future tasks) Modal and Temporal.

The ROADMAP lists our completed work accurately. This PR strategy makes that completed
work available to upstream one layer at a time, consistent with the ROADMAP's philosophy
of "every component lives at the most general level it can compile at."
