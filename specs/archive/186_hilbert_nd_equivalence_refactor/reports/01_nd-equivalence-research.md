# Research Report: Hilbert/ND Extensional Equivalence Refactor

**Task**: 186 -- Refactor the Hilbert / natural deduction extensional equivalence
**Date**: 2026-06-13
**Agent**: cslib-research-agent

## 1. Current State of the ND Files

### 1.1 File Inventory

The directory `Cslib/Logics/Propositional/NaturalDeduction/` contains 5 files:

| File | Lines | Purpose |
|------|-------|---------|
| `Basic.lean` | 396 | ND proof system: `Theory.Derivation` inductive (10 constructors), `Sequent` type, weakening, cut, substitution, equivalence relation |
| `DerivedRules.lean` | 253 | Derived ND rules: `botE` (requires `[IsIntuitionistic T]`), `negI`, `negE`, `topI`, `dne`, `iffI`, `iffE1`, `iffE2`, plus `DerivableIn`-level wrappers |
| `Equivalence.lean` | 414 | Main equivalence: `AxiomTheory`, `hilbertToND`, `ndToHilbert`, generic and corollary theorems |
| `FromHilbert.lean` | 321 | ND rules as Hilbert wrappers: `impI`, `impE`, `botE` for `DerivationTree`, plus cut, weakening, substitution |
| `HilbertDerivedRules.lean` | 469 | Derived Hilbert rules: conjunction, disjunction, negation, biconditional rules organized by logic strength (minimal/intuitionistic/classical) |

### 1.2 Architecture Summary

Two proof systems coexist:

- **ND System** (`Theory.Derivation`): 10 primitive constructors operating on `Finset`-based contexts (`Ctx Atom`), parameterized by a `Theory Atom` (set of propositions). Logic strength controlled by the theory: `MPL = {}`, `IPL = {bot -> A | A}`, `CPL = {~~A -> A | A}`.

- **Hilbert System** (`DerivationTree`): 4 constructors (ax, assumption, modus_ponens, weakening) operating on `List`-based contexts, parameterized by an `Axioms : Proposition Atom -> Prop` predicate. Three axiom predicates: `MinPropAxiom` (8 axioms: K, S, and/or), `IntPropAxiom` (9: adds EFQ), `PropositionalAxiom` (10: adds Peirce).

### 1.3 Key Design Decisions Already Made

1. **`botE` is a derived rule, not a primitive**: The ND inductive has NO `exfalso` constructor. Bottom elimination requires `[IsIntuitionistic T]` and uses the `ax` constructor with the EFQ axiom from the theory. This is the critical decision that makes the minimal equivalence work.

2. **`AxiomTheory` bridges the two parameterizations**: `AxiomTheory Axioms := { phi | Axioms phi }` converts a Hilbert axiom predicate into an ND theory. This is NOT the same as `MPL`/`IPL`/`CPL`.

3. **Context bridge**: `Finset.toList_toFinset` (Mathlib) provides `s.toList.toFinset = s` for the forward direction. The backward direction uses `Finset.mem_toList` directly.

## 2. The EFQ Problem for Minimal Logic -- RESOLVED

The task description states: "no minimal logic instantiation (hilbert_iff_nd_min) -- the generic theorem requires EFQ which MinPropAxiom lacks."

**This is no longer accurate.** The codebase has already resolved this issue. Key evidence:

1. The `h_EFQ` parameter was removed from `ndToHilbert` (docstring line 54: "The h_EFQ parameter was removed from ndToHilbert and all downstream signatures because bot elimination does not appear as a ND constructor").

2. `hilbert_iff_nd_min` exists and compiles successfully (verified by `lake build`).

3. The `ndToHilbert` function only needs to handle the 10 primitive ND constructors. None of them is `botE`. The function requires 8 axiom witnesses (K, S, andI, andE1, andE2, orI1, orI2, orE) which are exactly the 8 axioms in `MinPropAxiom`.

4. Similarly, `hilbert_iff_nd_ctx_min` exists and compiles.

**Conclusion**: No further work is needed on the EFQ/minimal logic issue. The equivalence at all three logic levels (minimal, intuitionistic, classical) is already established, in both closed-context and context-based forms.

## 3. Context-Based Equivalence -- ALREADY IMPLEMENTED

The task description states: "equivalence is only for closed derivability (empty context Derivable <-> DerivableIn emptyset) -- extend to full context-based equivalence."

**This is also already implemented.** The `hilbert_iff_nd_ctx` generic theorem and its three corollaries (`hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl`) provide the full context-based equivalence:

```lean
theorem hilbert_iff_nd_ctx
    {Axioms : PL.Proposition Atom -> Prop}
    (h_K : ...) (h_S : ...) (h_andI : ...) (h_andE1 : ...) (h_andE2 : ...)
    (h_orI1 : ...) (h_orI2 : ...) (h_orE : ...)
    {Gamma : Ctx Atom} {phi : PL.Proposition Atom} :
    Deriv Axioms Gamma.toList phi <->
    DerivableIn (AxiomTheory Axioms : Theory Atom) (Gamma |- phi)
```

The closed-context forms (`hilbert_iff_nd`, `hilbert_iff_nd_min`, etc.) are corollaries at `Gamma = emptyset`.

**Note on context representation**: The equivalence bridges `Deriv Axioms Gamma.toList phi` (List-based) with `DerivableIn (AxiomTheory Axioms) (Gamma |- phi)` (Finset-based). The `Gamma` is a `Finset`, so the Hilbert side uses `Gamma.toList`. This is the most natural formulation given the two systems' different context representations.

## 4. Proof Quality Analysis

### 4.1 `hilbertToND` (Equivalence.lean, lines 118-132)

**Quality: Good**. This is a clean structural recursion over `DerivationTree` with 4 cases:
- `ax` -> `Theory.Derivation.ax` (via `mem_axiomTheory`)
- `assumption` -> `Theory.Derivation.ass` (via `List.mem_toFinset`)
- `modus_ponens` -> `Theory.Derivation.impE` (recursive)
- `weakening` -> `Theory.Derivation.weakCtx` (via finset subset proof from list subset)

No redundancy, clear case decomposition. The only improvement would be minor: the weakening case could potentially use a more concise finset subset proof, but the current version is readable.

### 4.2 `ndToHilbert` (Equivalence.lean, lines 170-227)

**Quality: Adequate but verbose**. This is a structural recursion over `Theory.Derivation` with 10 cases:
- `ax` -> `DerivationTree.ax` (1 line)
- `ass` -> `DerivationTree.assumption` (1 line)
- `andI` -> `hilbertAndI` helper (3 lines per case)
- `andE1` -> `hilbertAndE1` helper (2 lines)
- `andE2` -> `hilbertAndE2` helper (2 lines)
- `orI1` -> `hilbertOrI1` helper (2 lines)
- `orI2` -> `hilbertOrI2` helper (2 lines)
- `orE` -> `hilbertOrE` helper + deduction theorem (8 lines)
- `impE` -> `DerivationTree.modus_ponens` (3 lines)
- `impI` -> `deductionTheorem` + weakening bridge (5 lines)

**Issues**:
1. **Repetitive recursive calls**: Every conjunction/disjunction case repeats the full 8-argument recursive call `ndToHilbert h_K h_S h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE`. This appears 12 times. A `where` clause or local abbreviation could reduce this.
2. **Noncomputable**: The function is `noncomputable` due to the `deductionTheorem` dependency (which uses `Classical.propDecidable`). This is inherent to the approach and cannot be avoided.
3. **8 explicit axiom parameters**: The function takes 8 explicit axiom witnesses. This is the correct generic design but makes the signature verbose.

### 4.3 Corollary Boilerplate (Equivalence.lean, lines 317-413)

**Quality: Highly repetitive**. All 6 corollaries (3 context-based + 3 closed-context) have identical proof bodies. Each passes 8 lambda-wrapped axiom constructors. For example:

```lean
theorem hilbert_iff_nd_ctx_min ... :=
  hilbert_iff_nd_ctx
    (fun phi psi => .implyK phi psi)
    (fun phi psi chi => .implyS phi psi chi)
    (fun phi psi => .andI phi psi)
    (fun phi psi => .andE1 phi psi)
    (fun phi psi => .andE2 phi psi)
    (fun phi psi => .orI1 phi psi)
    (fun phi psi => .orI2 phi psi)
    (fun phi psi chi => .orE phi psi chi)
```

The three context-based corollaries are identical except for the axiom predicate name. The three closed-context corollaries are also identical except for the axiom predicate name. This is 96 lines of boilerplate that could be reduced.

**Refactoring option**: Extract a helper that provides the 8 witnesses from any axiom predicate that has them. Since `MinPropAxiom`, `IntPropAxiom`, and `PropositionalAxiom` all share the same 8 constructors, a typeclass or structure bundling these witnesses could eliminate the repetition. However, this must be weighed against the added abstraction complexity.

### 4.4 `FromHilbert.lean` -- ND Rules as Hilbert Wrappers

**Quality: Clean**. Well-organized into core rules, derived rules, and Prop-level wrappers. The substitution section (lines 229-318) is necessary for the proof system to be complete.

### 4.5 `HilbertDerivedRules.lean` -- Derived Hilbert Rules

**Quality: Good organization**. Cleanly layered into minimal (K, S only), intuitionistic (K, S, EFQ), and classical (K, S, EFQ, Peirce) sections. Each rule has both Type-level and Deriv-level versions with consistent naming.

## 5. Corollary Instantiation Quality

### 5.1 Current State

The equivalence now covers all three systems in both closed-context and context-based forms:

| Theorem | Status | Axiom Predicate |
|---------|--------|-----------------|
| `hilbert_iff_nd` | Generic | any Axioms with K, S, and/or |
| `hilbert_iff_nd_min` | Corollary | `MinPropAxiom` |
| `hilbert_iff_nd_int` | Corollary | `IntPropAxiom` |
| `hilbert_iff_nd_cl` | Corollary | `PropositionalAxiom` |
| `hilbert_iff_nd_ctx` | Generic | any Axioms with K, S, and/or |
| `hilbert_iff_nd_ctx_min` | Corollary | `MinPropAxiom` |
| `hilbert_iff_nd_ctx_int` | Corollary | `IntPropAxiom` |
| `hilbert_iff_nd_ctx_cl` | Corollary | `PropositionalAxiom` |

All 8 theorems compile and build successfully.

### 5.2 Relationship Between Systems

A subtle but important point that should be documented more clearly:

- `AxiomTheory MinPropAxiom` is NOT `MPL` (empty theory). It contains 8 axiom schemata as theory members.
- `AxiomTheory IntPropAxiom` is NOT `IPL`. It contains 9 axiom schemata.
- `AxiomTheory PropositionalAxiom` is NOT `CPL`. It contains 10 axiom schemata.

The equivalence bridges `Deriv MinPropAxiom` with `DerivableIn (AxiomTheory MinPropAxiom)`, not with `DerivableIn MPL`. This is logically correct: both sides are parameterized by the same axiom predicate, just in different packaging.

To bridge to `MPL`/`IPL`/`CPL` would require additional work showing that `AxiomTheory MinPropAxiom` and `MPL` yield the same derivability (which is true because `MPL`'s ND system has the same primitive rules that the axioms encode, but the theory membership differs).

## 6. Literature References

### 6.1 Prawitz 1965

Already cited in `Basic.lean` (line 59) and `Equivalence.lean` (line 59). The [Prawitz1965] BibKey exists in `references.bib`. Prawitz's Chapter I, Section 1.2 covers the relationship between "H-systems" (Hilbert) and "I-systems" (natural deduction). The current formalization faithfully follows this structure.

### 6.2 Troelstra and van Dalen 1988

Already cited in `Basic.lean` (line 60-61) and `Equivalence.lean` (line 61). The [TroelstraVanDalen1988] BibKey exists in `references.bib`. Volume I, Section 10.4 covers the intuitionistic case.

### 6.3 Additional References

- [Johansson1937] is cited in `Basic.lean` (line 58) for minimal logic -- already in `references.bib`.
- [Gentzen1935] is cited in `Basic.lean` (line 63) -- already in `references.bib`.

**Conclusion**: All required literature references are already present and properly cited.

## 7. Downstream Impact

### 7.1 No Code Dependencies Outside ND Directory

A grep search confirms that `hilbert_iff_nd*`, `ndToHilbert`, `hilbertToND`, `AxiomTheory`, and `HilbertAxiomTheory` are referenced ONLY within `Cslib/Logics/Propositional/NaturalDeduction/`. The only external reference is in `Defs.lean` docstrings (lines 49-52) which list the theorem names for documentation.

Renaming or restructuring the equivalence theorems will have NO breaking effect on code outside the 5 ND files, as long as the docstring references in `Defs.lean` are updated.

### 7.2 Internal Dependencies

The import chain is:
```
Basic.lean  (imports Defs.lean, InferenceSystem, Finset)
  |
DerivedRules.lean  (imports Basic.lean)
  |
FromHilbert.lean  (imports DeductionTheorem.lean -- which is in Metalogic/)
  |
HilbertDerivedRules.lean  (imports FromHilbert.lean)
  |
Equivalence.lean  (imports Basic.lean, FromHilbert.lean, HilbertDerivedRules.lean)
```

## 8. Naming Convention Review

### 8.1 Current Names vs Mathlib Conventions

| Current Name | Convention | Notes |
|--------------|-----------|-------|
| `hilbertToND` | camelCase function | OK -- follows Lean 4 conventions |
| `ndToHilbert` | camelCase function | OK |
| `hilbert_iff_nd` | snake_case theorem | OK -- follows Mathlib conventions for theorems |
| `hilbert_iff_nd_ctx` | snake_case theorem | OK |
| `hilbert_iff_nd_min` | snake_case theorem | OK |
| `hilbert_to_nd_deriv` | snake_case theorem | OK |
| `nd_to_hilbert_deriv` | snake_case theorem | OK |
| `AxiomTheory` | CamelCase definition | OK |
| `HilbertAxiomTheory` | CamelCase abbreviation | OK |
| `mem_axiomTheory` | Mathlib `mem_*` convention | OK |
| `finset_insert_toList_mem_cons` | Descriptive | OK but long |

All names follow Lean 4/Mathlib conventions. No naming issues detected.

### 8.2 Docstring Coverage

All major definitions and theorems have docstrings. The module-level docstrings in each file are comprehensive, listing main definitions, design notes, and references. No gaps detected.

## 9. Refactoring Recommendations

### 9.1 High Priority: Reduce Corollary Boilerplate

**Problem**: 6 corollaries repeat identical 8-lambda bodies (96 lines of boilerplate).

**Option A -- Helper structure**: Define a structure bundling the 8 axiom witnesses, with instances for each axiom predicate:

```lean
/-- Bundle of the 8 axiom witnesses needed for the Hilbert/ND equivalence. -/
structure AxiomWitnesses (Axioms : PL.Proposition Atom -> Prop) where
  h_K : forall (phi psi), Axioms (phi.imp (psi.imp phi))
  h_S : forall (phi psi chi), Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))
  h_andI : forall (phi psi), Axioms (phi.imp (psi.imp (phi.and psi)))
  h_andE1 : forall (phi psi), Axioms ((phi.and psi).imp phi)
  h_andE2 : forall (phi psi), Axioms ((phi.and psi).imp psi)
  h_orI1 : forall (phi psi), Axioms (phi.imp (phi.or psi))
  h_orI2 : forall (phi psi), Axioms (psi.imp (phi.or psi))
  h_orE : forall (phi psi chi), Axioms ((phi.imp chi).imp ((psi.imp chi).imp ((phi.or psi).imp chi)))

instance : AxiomWitnesses (@MinPropAxiom Atom) := ...
instance : AxiomWitnesses (@IntPropAxiom Atom) := ...
instance : AxiomWitnesses (@PropositionalAxiom Atom) := ...
```

Then the generic theorems take `[AxiomWitnesses Axioms]` and each corollary becomes a one-liner.

**Option B -- Typeclass on Axioms**: Add a typeclass `HasMinimalAxioms` with the 8 witnesses. This integrates better with Lean's typeclass resolution.

**Option C -- Keep explicit but extract the axiom list**: Define a `minAxiomArgs` that packages the 8 arguments, then each corollary uses it. Less clean but simpler.

**Recommendation**: Option A (helper structure) or Option B (typeclass). Both reduce the 96 lines to approximately 30 lines of structure definition + 3 instances + 6 one-line corollaries.

### 9.2 Medium Priority: Reduce Recursive Call Verbosity in `ndToHilbert`

**Problem**: The 8-argument recursive call pattern `ndToHilbert h_K h_S h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE` appears 12 times.

**Solution**: If the structure/typeclass approach from 9.1 is adopted, `ndToHilbert` can take a single `[AxiomWitnesses Axioms]` parameter instead of 8 explicit ones, and the recursive calls become simply `ndToHilbert d`.

### 9.3 Low Priority: Documentation Clarification

1. **Clarify AxiomTheory vs MPL/IPL/CPL relationship** in module docstrings. The current note (Equivalence.lean line 45-47) is good but could be more prominent.

2. **Update Defs.lean docstring** (lines 49-52) to reflect the context-based equivalence forms.

3. **Add a note about the EFQ resolution**: Document that the h_EFQ parameter removal (done in a prior task) resolved the minimal logic instantiation issue.

### 9.4 Items NOT Needing Work

1. **Minimal logic instantiation (hilbert_iff_nd_min)**: Already resolved and working.
2. **Context-based equivalence**: Already implemented as `hilbert_iff_nd_ctx` and corollaries.
3. **Literature references**: All present and correctly cited.
4. **Naming conventions**: All follow Lean 4/Mathlib standards.

## 10. Tactic Survey

The proofs in this module primarily use:
- **Structural recursion** (pattern matching on inductive types) -- the main proof technique
- **`rwa`/`rfl`** -- for type rewriting in the bridge lemmas
- **`simp`** -- with `List.mem_toFinset`, `Finset.mem_toList`, `mem_axiomTheory`
- **`grind`** -- in `Basic.lean` for finset subset reasoning

No opportunities for tactic improvement were identified. The proofs are appropriately structured.

## 11. Summary of Findings

### What's Already Done (No Work Needed)

1. Minimal logic instantiation `hilbert_iff_nd_min` -- works correctly
2. Context-based equivalence `hilbert_iff_nd_ctx` -- fully implemented
3. All three logic levels (min/int/cl) have both closed and context-based corollaries
4. Literature references (Prawitz, Troelstra-van Dalen, Johansson, Gentzen) -- all present
5. Naming conventions -- all follow standards
6. Docstrings -- comprehensive

### What Needs Refactoring

1. **Corollary boilerplate reduction** (HIGH): Extract axiom witness bundle to eliminate 96 lines of repetitive code across 6 corollaries
2. **`ndToHilbert` verbosity** (MEDIUM): 12 repetitions of 8-argument recursive call pattern
3. **Documentation updates** (LOW): Clarify AxiomTheory vs MPL/IPL/CPL relationship more prominently

### Estimated Scope

The refactoring is primarily in `Equivalence.lean`. Changes to other files would be:
- `FromHilbert.lean`: If `ndToHilbert` signature changes to use the witness bundle
- `Defs.lean`: Docstring update only
- Other files: No changes needed
