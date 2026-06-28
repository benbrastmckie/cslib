# Research Report: Remove ND-Level Metalogic Superseded by Hilbert-Primary Results

Session: sess_1750723200_orchestrate_batch_320
Task: 320

## Executive Summary

The task requests removing ND-level algebraic completeness theorems that have been superseded by Hilbert-primary results. After thorough investigation, I find that the ND completeness theorems are **NOT redundant** -- they serve a critical structural role in the algebraic bridge theorems that connect the two proof systems. The task as described requires a more nuanced approach: rather than deleting the ND completeness machinery, the refactoring should either (a) rewrite the bridge theorems to bypass ND completeness, or (b) retain the ND completeness with updated documentation reflecting its bridge-infrastructure role.

## 1. File Inventory and Architecture

### 1.1 ND Completeness Theorems (Candidates for Removal)

**File**: `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` (277 lines)

Contains:
- `Theory.alg_complete` (line 208): General ND completeness over any theory T
- `MPL.alg_complete` (line 227): MPL completeness w.r.t. GHA
- `IPL.alg_complete` (line 242): IPL completeness w.r.t. HA
- `alg_complete_classical` (line 263): Classical completeness w.r.t. BA
- `nd_alg_sound` (line 171): ND soundness (meet formulation)
- `nd_alg_sound_aux` (line 96): Auxiliary soundness
- `lindenbaumMk_eq_top_iff` (line 187): Lindenbaum characterization
- `Theory.canonicalV`, `Theory.canonicalBotVal`, `Theory.canonicalV_spec`, `Theory.tValid_canonicalV`: Canonical valuation infrastructure

### 1.2 Hilbert-Primary Completeness Theorems (Replacements)

**File**: `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` (122 lines)

Contains:
- `MPL.hilbert_alg_complete` (line 57): `Derivable MinPropAxiom phi <-> GHAValid phi`
- `IPL.hilbert_alg_complete` (line 80): `Derivable IntPropAxiom phi <-> HAValid phi`
- `CPL.hilbert_alg_complete` (line 105): `Derivable PropositionalAxiom phi <-> BAValid phi`

These are self-contained via `HilbertLindenbaum.lean` and do NOT depend on the ND Lindenbaum.

### 1.3 ND Lindenbaum Algebra (Infrastructure for ND Completeness)

**File**: `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean` (425 lines)

Constructs the quotient `Proposition Atom / Theory.propositionSetoid` with:
- `LindenbaumAlgebra T`: quotient type
- `GeneralizedHeytingAlgebra` instance (for any T)
- `HeytingAlgebra` instance (for `IsIntuitionistic T`)
- `BooleanAlgebra` instance (for `IsIntuitionistic T`, `IsClassical T`)
- `nontrivialOfConsistent`: consistency implies nontriviality

### 1.4 Lindenbaum Named Instances

**File**: `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean` (145 lines)

Named abbreviations:
- `MPL.LindenbaumAlgebra`, `IPL.LindenbaumAlgebra`, `CPL.LindenbaumAlgebra`
- `MPL.instGHA`, `IPL.instHA`, `CPL.instBA`
- Union theory instances: `instIsIntuitionisticIPLUnionCPL`, `instIsClassicalIPLUnionCPL`

### 1.5 Algebraic Bridge Theorems (Critical Consumers)

**File**: `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` (206 lines)

Contains the **algebraic bridges** that connect ND (DerivableIn) to Hilbert (Derivable):
- `derivableInMplIffDerivableMin` (line 121): Uses `MPL.alg_complete` in both directions
- `derivableInIplIffDerivableInt` (line 139): Uses `IPL.alg_complete` in both directions
- `derivableInCplIffDerivableProp` (line 160): Uses `alg_complete_classical` in both directions

Also contains:
- `hilbertIplConservativeOverMpl` (line 81): Uses only Hilbert completeness (INDEPENDENT)
- `hilbertGlivenko` (line 102): Uses only Hilbert completeness (INDEPENDENT)
- `ipl_conservative_over_mpl` (line 188): ND corollary via bridges
- `glivenko` (line 200): ND corollary via bridges

### 1.6 Hilbert-ND Equivalence (Proof-Theoretic Bridge)

**File**: `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`

Contains `hilbert_iff_nd_ctx` and its corollaries:
```
Deriv Axioms Gamma.toList phi  <->  DerivableIn (AxiomTheory Axioms) (Gamma |- phi)
```

Critical distinction: `AxiomTheory MinPropAxiom` is NOT `Theory.MPL = emptyset`. The Hilbert-ND equivalence connects `Derivable Axioms` with `DerivableIn (AxiomTheory Axioms)`, not with `DerivableIn MPL`/`DerivableIn IPL`/`DerivableIn (IPL union CPL)`.

## 2. Dependency Analysis

### 2.1 Import Graph (Relevant Chain)

```
Lindenbaum.lean
  <- Completeness.lean (imports Lindenbaum)
  <- HilbertConservativeGlivenko.lean (imports Completeness)
  <- ConjImpConservative.lean (imports HilbertConservativeGlivenko)
  <- ConjImpBotConservative.lean (imports HilbertConservativeGlivenko + ConjImpConservative)
  <- LindenbaumInstances.lean (imports Lindenbaum)
```

### 2.2 Direct Consumers of ND Completeness Theorems

| Theorem | Used In | How Used |
|---------|---------|----------|
| `Theory.alg_complete` | `Completeness.lean` (self) | Defines MPL.alg_complete |
| `MPL.alg_complete` | `HilbertConservativeGlivenko.lean:127,129` | Bridge theorem proof (both .mp and .mpr) |
| `IPL.alg_complete` | `HilbertConservativeGlivenko.lean:145,147` | Bridge theorem proof (both .mp and .mpr) |
| `alg_complete_classical` | `HilbertConservativeGlivenko.lean:165,176` | Bridge theorem proof (both .mp and .mpr) |

No consumers exist OUTSIDE the Algebra subtree. Sequent calculus, tableau, modal, temporal modules use `hilbert_iff_nd_ctx` bridges directly and do NOT reference the ND completeness.

### 2.3 Consumers of Bridge Theorems

| Bridge | Used In | How Used |
|--------|---------|----------|
| `derivableInIplIffDerivableInt` | `ConjImpConservative.lean:133,137` | ND corollary proof |
| `derivableInIplIffDerivableInt` | `ConjImpBotConservative.lean:133,137` | ND corollary proof |
| `derivableInMplIffDerivableMin` | `HilbertConservativeGlivenko.lean:191` | `ipl_conservative_over_mpl` proof |
| `derivableInIplIffDerivableInt` | `HilbertConservativeGlivenko.lean:191,203` | `ipl_conservative_over_mpl` + `glivenko` proofs |
| `derivableInCplIffDerivableProp` | `HilbertConservativeGlivenko.lean:203` | `glivenko` proof |

### 2.4 Consumers of ND Lindenbaum (Outside Completeness)

| Consumer | What It Uses |
|----------|-------------|
| `LindenbaumInstances.lean` | `LindenbaumAlgebra`, algebra instances |

LindenbaumInstances provides named instances that are NOT consumed by any downstream module (no imports found). The Brouwerian and pointed Brouwerian Lindenbaum algebras are independent constructions.

### 2.5 Summary: What Has Zero External Consumers

1. `LindenbaumInstances.lean` -- no downstream imports
2. `Theory.alg_complete` -- only consumed by tier-specific variants in same file
3. `MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical` -- only consumed by bridges in `HilbertConservativeGlivenko.lean`
4. `nd_alg_sound`, `nd_alg_sound_aux` -- only consumed within `Completeness.lean`

## 3. Critical Structural Finding

### 3.1 The Bridge Problem

The algebraic bridges (`derivableInMplIffDerivableMin`, etc.) connect TWO DIFFERENT ND theories:

- `DerivableIn (emptyset : Theory Atom) phi` -- ND with the empty theory (MPL)
- `DerivableIn (AxiomTheory MinPropAxiom) phi` -- ND with MinPropAxiom as theory

The `hilbert_iff_nd` equivalences only bridge:
- `Derivable MinPropAxiom phi <-> DerivableIn (AxiomTheory MinPropAxiom) (emptyset |- phi)`

There is NO existing direct bridge from `DerivableIn (emptyset : Theory Atom) phi` to `DerivableIn (AxiomTheory MinPropAxiom) (emptyset |- phi)`, because:
- In `Theory.MPL = emptyset`, there are no axioms. Rules are: structural (impI/impE/andI/andE/orI/orE) + theory axioms (none).
- In `AxiomTheory MinPropAxiom`, axioms are the 8 MinPropAxiom schemata (K, S, andI, andE1, andE2, orI1, orI2, orE).

The current bridges go through algebraic completeness as the semantic meeting point: both proof systems are complete w.r.t. the same class of algebras, so a formula derivable in one is derivable in the other.

### 3.2 Alternative Bridge Strategy

To eliminate the ND completeness dependency, the bridges would need to be reproved using a SYNTACTIC rather than semantic route. This would require:

**Option A**: Show `DerivableIn (emptyset : Theory Atom) phi <-> DerivableIn (AxiomTheory MinPropAxiom) (emptyset |- phi)` directly by proving:
- Forward: The 8 MinPropAxiom schemata are admissible in pure ND (derivable from structural rules alone). This IS true but requires proving each schema as an ND theorem.
- Backward: ND structural rules are admissible in the MinPropAxiom Hilbert system. This is already established by `hilbert_iff_nd`.

**Option B**: Rewrite the bridges to compose `hilbert_iff_nd` with an admissibility lemma connecting `Theory.MPL` to `AxiomTheory MinPropAxiom`.

**Option C**: Keep the ND completeness but mark it as bridge infrastructure, remove only the standalone completeness CLAIMS (i.e., remove the standalone exports and update docstrings).

### 3.3 Feasibility Assessment

**Option A** is the cleanest but requires new proof work: demonstrating each MinPropAxiom schema is derivable in pure ND from the empty context. For `IPL.alg_complete` -> `derivableInIplIffDerivableInt`, we'd similarly need `DerivableIn IPL phi <-> DerivableIn (AxiomTheory IntPropAxiom) (emptyset |- phi)`.

**Option C** is the most conservative and lowest-risk: keep the ND completeness proofs as internal infrastructure, deprecate their public API surface, update docstrings.

## 4. Recommended Refactoring Plan

### Phase 1: Remove `LindenbaumInstances.lean` (Safe Delete)

This file has NO downstream imports. The named instances (`MPL.instGHA`, etc.) are unused.

**Files affected**: `LindenbaumInstances.lean` (delete), `Cslib.lean` (remove barrel entry)

### Phase 2: Rewrite Bridge Theorems Without ND Completeness

Replace the current algebraic-completeness-based bridges with proof-theoretic bridges:

1. Create a small lemma showing `DerivableIn (emptyset : Theory Atom) phi -> DerivableIn (AxiomTheory MinPropAxiom) (emptyset |- phi)` by weakening (any ND derivation in the empty theory is valid in a theory that includes axioms).

2. Create the reverse: `DerivableIn (AxiomTheory MinPropAxiom) (emptyset |- phi) -> DerivableIn (emptyset : Theory Atom) phi` by proving each MinPropAxiom schema is derivable in pure ND.

Compose with `hilbert_iff_nd` to get:
```
DerivableIn (emptyset : Theory Atom) phi
  <-> DerivableIn (AxiomTheory MinPropAxiom) (emptyset |- phi)  [new syntactic bridge]
  <-> Derivable MinPropAxiom phi                                  [hilbert_iff_nd_min]
```

Similarly for IPL and CPL.

**Key insight for the reverse direction**: The MinPropAxiom schemata (K, S, andI, etc.) are all derivable as ND theorems from the empty theory! This is because ND has structural rules for implication intro/elim, conjunction, disjunction, etc. that directly validate these axioms.

For IPL: additionally need `bot -> A` (efq), which is the botE rule in ND.
For CPL: additionally need `((not not A) -> A)` (DNE), which is the dne rule in ND.

These are already available as ND rules (`Derivation.botE`, `Derivation.dne`).

### Phase 3: Remove `Completeness.lean` (After Phase 2)

Once the bridges no longer depend on ND completeness, `Completeness.lean` can be deleted entirely.

**Files affected**: `Completeness.lean` (delete), `HilbertConservativeGlivenko.lean` (remove import, rewrite bridges)

### Phase 4: Simplify or Remove Lindenbaum.lean

After `Completeness.lean` is deleted, `Lindenbaum.lean` has only one consumer: `LindenbaumInstances.lean` (already deleted in Phase 1). So `Lindenbaum.lean` can also be deleted.

**Note**: The ND Lindenbaum algebra is an independent mathematical artifact. If the project wishes to retain it for pedagogical or future use, it can be kept with updated docstrings noting it is no longer on the critical dependency path.

### Phase 5: Update `HilbertConservativeGlivenko.lean`

- Remove the `derivableInMplIffDerivableMin`, `derivableInIplIffDerivableInt`, `derivableInCplIffDerivableProp` bridges (or replace with `hilbert_iff_nd`-based versions)
- Keep `hilbertIplConservativeOverMpl`, `hilbertGlivenko` (already Hilbert-primary)
- Keep `ipl_conservative_over_mpl`, `glivenko` (rewrite to use new bridges)
- Potentially rename file to reflect its new scope

### Phase 6: Update Docstrings

Files needing docstring updates:
- `Semantics/Algebra.lean` (barrel): Remove references to `Theory.alg_complete`, update architecture description
- `HilbertConservativeGlivenko.lean`: Update bridge section documentation
- `Foundations/Logic/ProofSystem.lean`: Update references to completeness theorems

### Phase 7: Fix Imports and Build Verification

- Remove deleted files from `Cslib.lean` barrel
- Run `lake exe mk_all --module` to regenerate
- Run `lake build` to verify
- Run `lake exe checkInitImports` and `lake lint`

## 5. Risk Assessment

### Low Risk
- Deleting `LindenbaumInstances.lean` (zero consumers)
- Docstring updates

### Medium Risk
- Rewriting bridge theorems (requires proving MinPropAxiom schema admissibility in ND; these proofs SHOULD be straightforward since ND has all the structural rules)
- Deleting `Completeness.lean` after bridge rewrite

### High Risk
- None identified, IF the bridge rewrite in Phase 2 is done correctly

### Build Breakage Scope
- **Sequent calculus** (LJ, LK): Uses `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl` -- NOT affected
- **Tableau**: Uses `Metalogic.StrongCompleteness` -- NOT affected (independent Hilbert-level infrastructure)
- **Modal/Temporal**: Uses `ModalSetDerivable` -- NOT affected
- **ConjImpConservative, ConjImpBotConservative**: Uses `derivableInIplIffDerivableInt` -- WILL need updates if bridge API changes
- **ProofSystemEquivalence**: Uses `hilbert_iff_nd_ctx` -- NOT affected

## 6. Scope Estimate

| Phase | Effort | Lines Changed |
|-------|--------|--------------|
| Phase 1: Delete LindenbaumInstances | Trivial | -145 lines |
| Phase 2: Rewrite bridges | Medium | ~100 lines new, ~60 lines removed |
| Phase 3: Delete Completeness.lean | Trivial (after Phase 2) | -277 lines |
| Phase 4: Consider Lindenbaum.lean | Low | -425 lines (if deleted) |
| Phase 5: Update HilbertConservativeGlivenko | Medium | ~80 lines modified |
| Phase 6: Update docstrings | Low | ~30 lines modified |
| Phase 7: Fix imports + build | Low | ~10 lines |

**Total**: Net removal of 700-850 lines, with ~100 lines of new bridge proofs.

## 7. Key Finding: The "DerivableIn Theory vs AxiomTheory" Gap

The most important finding is that the bridge theorems are NOT trivially replaceable. They bridge TWO DIFFERENT formulations of the same logic:

1. `DerivableIn (emptyset : Theory Atom) phi` -- ND with structural rules only, theory is empty
2. `Derivable MinPropAxiom phi` -- Hilbert system with MinPropAxiom schemata

The existing `hilbert_iff_nd` only reaches `DerivableIn (AxiomTheory MinPropAxiom) phi`, not `DerivableIn (emptyset) phi`. The gap is: showing the MinPropAxiom schemata are admissible as pure ND theorems. This is true but not trivially stated -- it requires 8 separate ND derivation constructions.

The simplest approach for Phase 2 may be to note that `DerivableIn (emptyset) phi -> DerivableIn (AxiomTheory MinPropAxiom) phi` is trivial (empty theory has fewer axioms), and the reverse requires showing each MinPropAxiom is an ND theorem. But actually, this reverse direction is NOT obviously true: `DerivableIn (AxiomTheory MinPropAxiom) phi` means ND derivable with access to the MinPropAxiom formulas as non-logical axioms. This is STRONGER than `DerivableIn emptyset phi`.

Wait -- this means the bridge `derivableInMplIffDerivableMin` is saying that `DerivableIn (emptyset) phi <-> Derivable MinPropAxiom phi`. The forward direction says: if phi is derivable in pure ND (no axioms), then phi is Hilbert-derivable. The backward direction says: if phi is Hilbert-derivable, then phi is derivable in pure ND. Both of these go through algebraic completeness.

The proof-theoretic replacement would be:
- Forward: `hilbert_iff_nd_min.mpr` composed with a weakening from empty theory to AxiomTheory
  - BUT this gives `DerivableIn (emptyset) phi -> DerivableIn (AxiomTheory MinPropAxiom) phi` (by weakening) `-> Derivable MinPropAxiom phi` (by hilbert_iff_nd). This works!
- Backward: `Derivable MinPropAxiom phi -> DerivableIn (AxiomTheory MinPropAxiom) phi` (by hilbert_iff_nd) `-> DerivableIn (emptyset) phi` (requires showing AxiomTheory axioms are derivable in empty theory). Each MinPropAxiom schema (K, S, andI, andE1, andE2, orI1, orI2, orE) is indeed derivable in pure ND from the empty theory using structural rules.

So the Phase 2 plan is feasible. The forward direction is trivial (weakening); the backward direction requires 8 small ND derivations (one per axiom schema).

For IPL: The `DerivableIn IPL phi` direction needs a bridge to `DerivableIn (AxiomTheory IntPropAxiom) phi`. Forward: IPL axioms are a subset of IntPropAxiom axioms (once wrapped in AxiomTheory); backward: IntPropAxiom axioms are derivable in the IPL ND system.

This is slightly more complex because `Theory.IPL = Set.range (Proposition.imp bot .)` while `AxiomTheory IntPropAxiom = { phi | IntPropAxiom phi }` which includes all 9 schema instances. Need to show:
- Each IntPropAxiom instance (K, S, andI, etc., EFQ) is ND-derivable in IPL
- Each IPL axiom (`bot -> A`) is in AxiomTheory IntPropAxiom (yes, as the EFQ case)

This is doable but requires careful proof construction.
