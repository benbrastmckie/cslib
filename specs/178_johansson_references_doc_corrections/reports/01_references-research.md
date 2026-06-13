# Research Report: Task 178 -- Documentation and Citation Corrections

**Task**: Documentation and citation corrections from task 171 research
**Date**: 2026-06-12
**Session**: sess_1781317385_e83d59_178
**Status**: Research complete

---

## Executive Summary

Task 173 (five-primitive refactor) has already resolved the most critical architectural issue
identified in task 171: the `Proposition` inductive now has 5 constructors
`{atom, bot, imp, and, or}` instead of 3, and the ND system has 10 primitive constructors
including conjunction and disjunction rules. This means many of the original task 171
recommendations about incorrect functional-completeness claims are **partially resolved** --
but documentation, citations, and PR #635 corrections remain outstanding.

PR #635 was **closed** (not merged) after ctchou's review pointed out the problems with
the `{imp, bot}` basis for intuitionistic logic. The five-primitive architecture on `main`
is the resolution. However, residual documentation from the old PR description and some
file headers still reference the old `{imp, bot}` basis narrative.

---

## Finding 1: references.bib -- Existing Entries and Missing Entries

### Existing Entries (Confirmed Present)

The following entries already exist in `references.bib`:

| BibKey | Status | Notes |
|--------|--------|-------|
| `Church1956` | Present (line 126-134) | Correct entry |
| `ChagrovZakharyaschev1997` | Present (line 52-61) | Correct entry |
| `Gentzen1935` | Present (line 173-182) | Correct entry |
| `Prawitz1965` | Present (line 340-347) | Correct entry |
| `TroelstraVanDalen1988` | Present (line 390-400) | Correct entry |
| `Heyting1930` | Present (line 239-246) | Correct entry |

### Missing Entries (Must Add)

**Johansson1937** -- CONFIRMED MISSING. Required for citing the origin of minimal logic,
which CSLib formalizes via `MinPropAxiom`, `MinimalHilbert`, `Theory.MPL`,
`Propositional.HilbertMin`, `MinSoundness`, `MinCompleteness`, and `MinLindenbaum`.

Recommended BibTeX entry (following existing format conventions):
```bibtex
@article{Johansson1937,
  author       = {Johansson, Ingebrigt},
  title        = {Der Minimalkalk{\"u}l, ein reduzierter intuitionistischer Formalismus},
  journal      = {Compositio Mathematica},
  volume       = {4},
  pages        = {119--136},
  year         = {1937}
}
```

**Wajsberg1938 and McKinsey1939** -- Whether these should be added depends on whether the
implementation chooses to cite them. They are relevant for explaining why `and` and `or`
are primitives (non-interdefinability of intuitionistic connectives). The `Connectives.lean`
module header already mentions "Wajsberg 1938, McKinsey 1939" in prose but does NOT have
corresponding BibTeX entries. Either:
- (a) Add the entries and convert to proper BibKey citations, or
- (b) Leave as prose citations (acceptable for well-known results)

If option (a), the entries would be:
```bibtex
@article{Wajsberg1938,
  author       = {Wajsberg, Mordchaj},
  title        = {{Untersuchungen {\"u}ber den Aussagenkalk{\"u}l von A. Heyting}},
  journal      = {Wiadomo{\'s}ci Matematyczne},
  volume       = {46},
  pages        = {45--101},
  year         = {1938}
}

@article{McKinsey1939,
  author       = {McKinsey, J. C. C.},
  title        = {Proof of the Independence of the Primitive Symbols of {Heyting's} Calculus of Propositions},
  journal      = {The Journal of Symbolic Logic},
  volume       = {4},
  number       = {4},
  pages        = {155--158},
  year         = {1939},
  doi          = {10.2307/2268715}
}
```

---

## Finding 2: Connectives.lean -- Documentation Status (Post-Task-173)

**File**: `Cslib/Foundations/Logic/Connectives.lean`

The current module header (lines 12-47) is **already substantially corrected** compared to
the pre-task-173 state. Key observations:

### Already Correct

1. The header correctly describes the "hybrid five-primitive propositional signature
   `{atom, bot, imp, and, or}`" (line 20).

2. The explanation of why `and` and `or` are primitives is correct: "The classical encodings
   `and phi psi := neg(phi -> neg psi)` and `or phi psi := neg phi -> psi` are only
   propositionally equivalent to `and` and `or` in classical logic (Wajsberg 1938,
   McKinsey 1939); they fail in intuitionistic and minimal logic." (lines 29-34)

3. The derived connectives `neg` and `top` are correctly described as valid across all
   three logic strengths (line 37).

### Remaining Issue

The References section (lines 42-47) lists Church 1956, Heyting 1930, Gentzen 1935,
and Chagrov & Zakharyaschev 1997 but does NOT cite:
- **Johansson 1937** -- should be added since `MinimalHilbert` is named for his system
  and `HasBot`/`HasImp` reflect the minimal logic tradition.
- **Troelstra & van Dalen 1988** -- should be added as a reference for full-connective ND.
- **Prawitz 1965** -- should be added as a reference for full-connective ND.

Heyting 1930, Gentzen 1935 are now appropriate citations here because the module
acknowledges the full-connective approach (these authors used full connective sets).

No functional-completeness overclaim exists in this file after task 173.

---

## Finding 3: Defs.lean -- Residual Functional-Completeness Claim

**File**: `Cslib/Logics/Propositional/Defs.lean`

**Line 20-21**: The module docstring still contains:
```
  `bot` (falsum), and `imp` (implication); since `{imp, bot}` is functionally complete for
  classical logic, conjunction, disjunction, negation, and verum are derived connectives
```

This is **outdated and incorrect** after task 173. The `Proposition` inductive now has
5 constructors (`atom`, `bot`, `imp`, `and`, `or`), so conjunction and disjunction are
**primitive constructors**, not derived connectives. The docstring must be updated to
match the actual inductive definition.

The `Proposition` docstring on line 53 is also inconsistent:
```
/-- Propositions. Primitives are atoms, falsum, implication, conjunction, and disjunction. -/
```
This line is **correct** (it reflects 5 constructors), but it contradicts the module
docstring above it that says conjunction/disjunction are derived.

### Recommended Fix

Replace lines 19-22 with text reflecting the actual 5-constructor design:
- Document that `{atom, bot, imp, and, or}` are the primitives
- State that `neg`, `top`, and `iff` are derived connectives (as `abbrev`s)
- The five-primitive approach follows the standard Gentzen/Prawitz/Troelstra-van Dalen
  tradition
- Cite Johansson 1937 for minimal logic (Theory.MPL)

### References Section

Lines 40-43 cite Church 1956 and Chagrov & Zakharyaschev 1997 only. These are appropriate
for classical logic but the module now covers minimal and intuitionistic logic via
`Theory.MPL` and `Theory.IPL`. Add:
- Johansson 1937 for minimal logic
- Gentzen 1935 for the ND tradition with full connectives
- Prawitz 1965 for ND reference
- Troelstra & van Dalen 1988 for constructive mathematics reference

---

## Finding 4: NaturalDeduction/Basic.lean -- Documentation Status

**File**: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`

The module header (lines 44-57) contains a stale "Implementation notes" section:

```
The primitive inference rules are: axiom (from theory), assumption (from context),
implication introduction and elimination, and ex falso quodlibet (bottom elimination).
Conjunction and disjunction rules are derivable from these primitives together with
the definitions of `and` and `or` in terms of `->` and `bot`, so they need not be postulated.
```

This is **completely incorrect** after task 173. The `Theory.Derivation` inductive now has
10 primitive constructors: `ax`, `ass`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`,
`impI`, `impE`. Conjunction and disjunction rules ARE postulated as primitives.

The `Derivation` docstring (lines 82-85) is also inconsistent:
```
/-- A `T`-derivation ... Primitives: axiom, assumption, conjunction intro/elim,
disjunction intro/elim, and implication intro/elim.
Ex falso quodlibet (bottom elimination) is a derived rule requiring `[IsIntuitionistic T]`. -/
```
This docstring IS correct (it reflects the current 10-constructor design with `botE` as
derived). The "Implementation notes" section contradicts it.

### Two-Layer Architecture Documentation

The task description asks to "document the two-layer proof-system architecture." The current
state already has this architecture:
1. **Natural Deduction** (`NaturalDeduction/Basic.lean`): 10 primitive rules, `botE` derived
   (requires `[IsIntuitionistic T]`), theory parameterization via `MPL`/`IPL`/`CPL`
2. **Hilbert System** (`ProofSystem/`): Axiom predicate hierarchy with
   `MinPropAxiom` (8 axioms), `IntPropAxiom` (9 axioms), `PropositionalAxiom` (10 axioms)

The module docstring should document this architecture explicitly, noting:
- ND uses theory parameterization (empty = minimal, IPL = intuitionistic, CPL = classical)
- Hilbert uses axiom predicate hierarchy
- The `NaturalDeduction/Equivalence.lean` bridges the two systems
- Both share the same 5-constructor `Proposition` type

### References

Lines 51-57 cite Prawitz 1965, Troelstra & van Dalen 1988, and Gentzen 1935. These are
now **correctly cited** (the full-connective ND system matches what these authors described).
Add Johansson 1937 since the minimal logic theory `MPL := emptyset` formalizes his system.

---

## Finding 5: DerivedRules.lean -- Documentation Status

**File**: `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean`

The module header (lines 17-59) is **correct** after task 173. It accurately documents:
- The ND system has 10 primitive constructors
- `botE` is derived (requires `[IsIntuitionistic T]`)
- `dne` is derived (requires `[IsClassical T]`)
- Conjunction/disjunction rules are "primitive wrappers, no classicality required"

No corrections needed in this file.

---

## Finding 6: Other Files -- Documentation Status

### ProofSystem/Axioms.lean
Correct after task 173. Documents all three axiom sets (8 minimal, 9 intuitionistic,
10 classical) with and/or axioms at all levels.

### Semantics/Kripke.lean
**Line 37**: States "`PL.Proposition` has five constructors `atom | bot | imp | and | or`" --
this is correct.
**Line 74**: IForces definition correctly handles all 5 cases including `and` and `or` --
correct.

### Semantics/Basic.lean
`Evaluate` function correctly handles all 5 cases including `and` and `or` -- correct.

### Metalogic files
`MinSoundness.lean`, `IntSoundness.lean`, `MinCompleteness.lean`, `IntCompleteness.lean`,
`Completeness.lean` -- all correctly handle the 5-constructor formula type with full and/or
axiom soundness proofs.

### ProofSystem.lean (Foundations)
The `MinimalHilbert` class (line 316) requires only K, S, and MP -- does NOT include
and/or axiom requirements at the typeclass level. However, the concrete instance
`Propositional.HilbertMin` in `IntMinInstances.lean` does register all and/or axiom
instances. This is intentional: the abstract typeclass is minimal, concrete instances
provide more.

---

## Finding 7: PR #635 Status and Response

**PR #635 is CLOSED** (not merged). State: `CLOSED`.

ctchou's review raised three comments:
1. Referenced PR #607 (fmontesi's one-class-per-operator design)
2. Questioned whether connectives can be reduced to `{imp, bot}` in intuitionistic logic
3. Pointed out that Gentzen 1935 and Heyting 1930 used full connective sets

benbrastmckie responded: "That's helpful. I think it may be best to close this and I'll
think through the set up again."

**The PR was closed, and task 173 subsequently implemented the five-primitive refactor
on main.** This resolves the architectural issue but means there is no PR to rewrite --
the PR description is now historical. If a new PR is opened for the documentation
corrections from this task, a new PR description will be needed.

### PR #635 Description -- No Rewrite Needed

Since PR #635 is closed and will not be reopened, rewriting its description is unnecessary.
The five-primitive architecture is already on `main`. If task 178 results in a new PR for
documentation corrections, it should have its own fresh description.

---

## Finding 8: Exact List of Files Requiring Changes

### Files with incorrect/stale documentation:

| File | Issue | Severity |
|------|-------|----------|
| `Cslib/Logics/Propositional/Defs.lean` | Module docstring lines 19-22 reference `{imp, bot}` functional completeness; claims and/or are derived; contradicts actual 5-constructor inductive | HIGH |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | "Implementation notes" section lines 44-49 claims and/or rules are derivable, not postulated | HIGH |
| `Cslib/Foundations/Logic/Connectives.lean` | References section missing Johansson 1937, Prawitz 1965, Troelstra & van Dalen 1988 | MEDIUM |
| `Cslib/Logics/Propositional/Defs.lean` | References section missing Johansson 1937, Gentzen 1935, Prawitz 1965 | MEDIUM |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | References section should add Johansson 1937 | LOW |
| `references.bib` | Missing Johansson1937 entry | MEDIUM |
| `references.bib` | Optional: add Wajsberg1938, McKinsey1939 entries to match prose citations in Connectives.lean | LOW |

### Files already correct (no changes needed):

- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean`
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean`
- `Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean`
- `Cslib/Logics/Propositional/Semantics/Basic.lean`
- `Cslib/Logics/Propositional/Semantics/Kripke.lean`
- `Cslib/Logics/Propositional/Metalogic/*` (all metalogic files)
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean`
- `Cslib/Foundations/Logic/ProofSystem.lean`

---

## Finding 9: Two-Layer Architecture Documentation Recommendations

The Propositional module should have a clear module-level docstring documenting:

### Layer 1: Natural Deduction (NaturalDeduction/)
- `Theory.Derivation`: 10 primitive constructors (ax, ass, andI, andE1, andE2, orI1, orI2,
  orE, impI, impE)
- Logic stratification via theory parameter: `MPL := emptyset` (minimal), `IPL` (intuitionistic
  with EFQ), `CPL` (classical with DNE)
- `botE` derived from theory membership (requires `[IsIntuitionistic T]`)
- Uses `Finset` contexts; sequent notation `Gamma |- A`

### Layer 2: Hilbert System (ProofSystem/)
- `DerivationTree Axioms`: 4 constructors (ax, assumption, modus_ponens, weakening)
- Logic stratification via axiom predicate: `MinPropAxiom` (8 axioms), `IntPropAxiom`
  (9 axioms + EFQ), `PropositionalAxiom` (10 axioms + Peirce)
- Uses `List` contexts
- Typeclass hierarchy: `MinimalHilbert -> IntuitionisticHilbert -> ClassicalHilbert`

### Bridge (NaturalDeduction/Equivalence.lean)
- `hilbertToND`: structural translation (all axiom predicates)
- `ndToHilbert`: requires K, S, EFQ + and/or axiom witnesses
- `hilbert_iff_nd`: extensional equivalence for closed derivability

This architecture should be documented in the `Defs.lean` module docstring or in a
separate `README` section of the `Basic.lean` module header.

---

## Recommended Implementation Plan

### Phase 1: references.bib additions
- Add `Johansson1937` entry
- Optionally add `Wajsberg1938` and `McKinsey1939` entries
- No code changes, just BibTeX

### Phase 2: Defs.lean documentation correction
- Rewrite module docstring to reflect 5-constructor design
- Update references section with Johansson, Gentzen, Prawitz citations
- Add two-layer architecture overview
- No code changes (all code is correct)

### Phase 3: NaturalDeduction/Basic.lean documentation correction
- Remove or rewrite "Implementation notes" section to match 10-constructor design
- Add Johansson 1937 to references
- Document the two-layer architecture bridge
- No code changes

### Phase 4: Connectives.lean reference additions
- Add Johansson 1937, Prawitz 1965, Troelstra & van Dalen 1988 to References section
- No code changes

### Phase 5: CI verification
- `lake build` to confirm no regressions from docstring changes
- `lake exe checkInitImports` and `lake exe lint-style`

All phases are documentation-only. No Lean code changes are needed.

---

## References

- Task 171 team research report: `specs/171_research_connective_basis_min_int_classical/reports/01_team-research.md`
- Task 173 implementation commits: 8b2a470d, db2a83bc, 9e83b68b, 4dde21ed, d211d9ed
- PR #635: https://github.com/leanprover/cslib/pull/635 (CLOSED)
