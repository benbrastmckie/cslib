# Task 208: Missing Docstring Lint Research

## Summary

The `lake lint` command reports exactly **327 `docBlame` errors** ("definition missing documentation string") across **35 files** in two directories:
- **Bimodal/**: 252 declarations across 28 files
- **Temporal/**: 75 declarations across 7 files
- **Modal/**: 0 declarations (contrary to the task description estimate of 57)

The task description estimated 190/80/57 for Bimodal/Temporal/Modal. The actual distribution is 252/75/0. All 327 errors come from the `docBlame` linter which requires `/-- ... -/` docstrings on public declarations.

## Declaration Type Breakdown

| Type | Count | Notes |
|------|-------|-------|
| Top-level definitions | 269 | `def`, `noncomputable def`, `abbrev` at column 1 |
| Structure/inductive fields | 58 | Fields at column 3 (e.g., `.formulas`, `.x`, `.val`) |
| Inductive types | 11 | `inductive` declarations |
| Notation terms | 3 | `term_...` notation declarations |

Many "definitions" are actually proof-bearing terms (derivation trees, witnesses) that function as theorems but are declared with `def` rather than `theorem`. These need docstrings describing the proven statement.

## Per-File Breakdown

### Bimodal/ (252 declarations, 28 files)

| File | Count | Category |
|------|-------|----------|
| `Theorems/TemporalDerived.lean` | 41 | Temporal derived theorems (G/H/F/P distribution, monotonicity, duality) |
| `Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` | 30 | Chronicle data structures, r-relations, Burgess relations |
| `Syntax/SubformulaClosure/TemporalFormulas.lean` | 26 | Deferral closure, seriality formulas, blocking sets, abbreviations |
| `Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` | 16 | Counterexample structure fields and elimination procedures |
| `Metalogic/BXCanonical/CanonicalModel.lean` | 16 | Canonical model construction (schedule, chains, FMCS) |
| `Theorems/Propositional/Connectives.lean` | 16 | Propositional connective combinators (iff, contraposition, De Morgan) |
| `Metalogic/BXCanonical/Frame.lean` | 14 | BX frame points, ordering, witnesses, content-closed derivation |
| `Theorems/Propositional/Core.lean` | 14 | Core propositional theorems (LEM, DNE, RAA, ECQ, disjunction) |
| `Metalogic/Bundle/TemporalCoherence.lean` | 10 | Temporal coherence family, G/H DNE theorems, until/since coherence |
| `Syntax/SubformulaClosure/NestingDepth.lean` | 8 | Nesting depth functions, extractors, formula predicates |
| `Theorems/GeneralizedNecessitation.lean` | 7 | Generalized modal/temporal K, past necessitation |
| `Metalogic/Bundle/ModalSaturation.lean` | 7 | Modal saturation, DNE theorems, SaturatedBFMCS inductive |
| `Metalogic/BXCanonical/Chronicle/PointInsertion.lean` | 6 | EnrichedEvent/EnrichedEventSince structure fields |
| `Metalogic/Bundle/TemporalContent.lean` | 6 | g/h/f/p/u/s content set definitions |
| `Metalogic/Bundle/Construction.lean` | 5 | Context utilities, Lindenbaum MCS, context consistency |
| `FrameConditions/Validity.lean` | 5 | Parameterized validity definitions (linear, dense, discrete, Int) |
| `Metalogic/BXCanonical/Quasimodel/HintikkaPoint.lean` | 4 | Hintikka point inductive, signature formulas |
| `Metalogic/Separation/Defs.lean` | 3 | IntStructure field, junction depth functions |
| `Metalogic/BXCanonical/Quasimodel/SubformulaClosure.lean` | 3 | Subformulas, GH enrichment, subformula closure |
| `Metalogic/BXCanonical/Quasimodel/Construction.lean` | 3 | QuasimodelChain inductive, sinceDefectCount, HintikkaRawChain field |
| `Metalogic/BXCanonical/Filtration/DefectChain.lean` | 3 | Until/since defect predicates and counts |
| `Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` | 2 | negImpImplies helper lemmas |
| `Metalogic/Algebraic/LindenbaumQuotient.lean` | 2 | Notation terms for provable equivalence and quotient |
| `Theorems/Perpetuity/Principles.lean` | 1 | Perpetuity axiom helper |
| `Metalogic/Decidability/AxiomMatcher.lean` | 1 | Identity definition |
| `Metalogic/Bundle/FMCSDef.lean` | 1 | FMCS.mcs field |
| `Metalogic/Algebraic/UltrafilterMCS.lean` | 1 | BoolAlgUltrafilter.carrier field |
| `FrameConditions/Soundness.lean` | 1 | soundnessOver definition |

### Temporal/ (75 declarations, 7 files)

| File | Count | Category |
|------|-------|----------|
| `Metalogic/Chronicle/ChronicleTypes.lean` | 30 | Chronicle types, r-relations, Burgess relations (parallel to Bimodal) |
| `Metalogic/Chronicle/CounterexampleElimination.lean` | 19 | Counterexample structures, walk results, elimination procedures |
| `Metalogic/Chronicle/Frame.lean` | 9 | TPoint fields, content-closed derivation, witnesses |
| `Metalogic/TemporalContent.lean` | 6 | g/h/f/p/u/s content set definitions |
| `Metalogic/Chronicle/PointInsertion.lean` | 6 | EnrichedEvent/EnrichedEventSince structure fields |
| `Metalogic/Chronicle/RRelation.lean` | 3 | Deductive closure, r/r3 DCS extensions |
| `Metalogic/WitnessSeed.lean` | 2 | Forward/past temporal witness seeds |

## Docstring Style Guide (from Existing Examples)

### Pattern 1: Theorem-like definitions (derivation trees, proofs)

Existing style uses backtick-quoted formal statement:
```lean
/-- `⊢ G(φ → ψ) → (Gφ → Gψ)`: temporal K-distribution derived from BX axioms. -/
noncomputable def tempKDistDerived ...

/-- `⊢ φ → G(Pφ)`: future connection axiom. -/
def connectFutureThm ...

/-- `⊢ ¬(¬ψ → ¬φ) → ¬(φ → ψ)`: negation of contrapositive implies negation of implication. -/
noncomputable def negContrapositiveImpNeg ...
```

**Convention**: Start with the formal statement in backticks, then a colon and brief English description. Single line preferred.

### Pattern 2: Semantic/structural definitions

```lean
/-- A formula is valid over temporal domain D. -/
def validOver ...

/-- A set is closed under derivation. -/
def ClosedUnderDerivation ...

/-- A set is deductively closed (consistent + closed under derivation). -/
def SetDeductivelyClosed ...
```

**Convention**: Brief English description of what the definition captures. Parenthetical clarification when helpful.

### Pattern 3: Content-extraction/utility definitions

```lean
/-- Substitution sigma[q -> bot]: replace the fresh atom `Sum.inr ()` with `bot`. -/
def substFormula ...

/-- If the fresh atom is not in a formula's atoms, substitution is the identity. -/
theorem noFreshAtom_substFormula_id ...
```

**Convention**: Describe the computation or property in plain English.

### Pattern 4: Structure/inductive declarations

```lean
/-- A set is deductively closed (consistent + closed under derivation). -/
def SetDeductivelyClosed ...
```

For structures and inductives, describe what the data type represents and its role.

### Pattern 5: Structure fields

```lean
/-- The underlying set of formulas. -/
formulas : Set (Formula Atom)
```

Structure fields get very brief descriptions of what the field represents.

### Pattern 6: Notation terms

```lean
/-- Notation `⊨[D] φ` for validity of `φ` over temporal domain `D`. -/
notation:50 "⊨[" D "] " φ:50 => validOver D φ
```

Describe the notation syntax and what it denotes.

## Semantic Categories for Docstring Content

Understanding what each declaration does is essential for writing meaningful docstrings. The 327 declarations fall into these semantic categories:

### 1. Hilbert-style derivation trees (largest group, ~120)
Definitions like `F_mono`, `G_distribution`, `contrapositiveThm` that produce `DerivationTree fc Gamma phi` values. The docstring should state the derived formula using Unicode temporal operators (G, H, F, P, U, S).

### 2. Canonical model components (~50)
Definitions like `schedule`, `fwdSucc`, `bwdPred`, `fwdChain`, `bxFmcs` that build parts of the canonical/chronicle model construction. Docstrings should describe the component's role in the construction.

### 3. Formula-level predicates and functions (~40)
Definitions like `IsFutureFormula`, `fNestingDepth`, `toFutureDeferral`, `deferralClosure` that operate on the formula datatype. Docstrings should describe the computation.

### 4. Set-theoretic constructions (~30)
Definitions like `gContent`, `hContent`, `temporalBlockingSet`, `serialityFormulas` that define sets of formulas. Docstrings should describe what's in the set.

### 5. Structure fields (~58)
Fields like `.formulas`, `.x`, `.val`, `.event'`. Very brief descriptions of the field's role.

### 6. Inductive types (~11)
Types like `Chronicle`, `ValidChronicle`, `ChronicleInvariant`, `BXPoint`, `HintikkaPoint`. Describe the data structure and its purpose.

### 7. Relations and predicates (~20)
Definitions like `rRelation`, `rMaximal`, `burgessR`, `Adjacent`. Describe the binary relation or predicate.

## Effort Estimate

- **Trivial docstrings** (structure fields, abbreviations, notation): ~70 declarations -- can be generated mechanically from the type signature
- **Medium docstrings** (utility defs, set definitions, predicates): ~100 declarations -- require reading the definition body
- **Careful docstrings** (proof-bearing defs, semantic constructions): ~157 declarations -- require understanding the mathematical content

**Total estimated effort**: The work is repetitive but requires domain knowledge. Each file needs:
1. Read the file to understand context
2. For each declaration, write a 1-line `/-- ... -/` docstring
3. Verify with `lake lint` that warnings are resolved

**Parallel structure**: Many Temporal/ declarations mirror Bimodal/ declarations (e.g., both have `Chronicle`, `rRelation`, `burgessR`, `gContent`). Docstrings can be written for Bimodal first, then adapted for Temporal with minimal changes.

## Risks and Considerations

1. **Build verification**: Adding docstrings should not break the build, but verifying after each batch is prudent.
2. **Existing linter suppression**: Some files have `set_option linter.unusedSimpArgs false` etc. The `docBlame` linter is NOT suppressed in any of these files, which is why the warnings appear.
3. **No code changes**: This task only adds docstring comments. No functional changes needed.
4. **Bimodal/Temporal parallel**: The Temporal/ files were ported from Bimodal/. Docstrings should be consistent across the parallel structures.

## Recommended Plan Structure

**Phase 1**: Bimodal/Theorems/ (78 declarations across 5 files) -- all proof-bearing defs with clear formal statements
**Phase 2**: Bimodal/Syntax/ (34 declarations across 2 files) -- formula infrastructure
**Phase 3**: Bimodal/Metalogic/Bundle/ (29 declarations across 5 files) -- bundle constructions
**Phase 4**: Bimodal/Metalogic/BXCanonical/ (82 declarations across 10 files) -- canonical model
**Phase 5**: Bimodal/FrameConditions/ + Bimodal/Metalogic/Algebraic/ + remaining (14 declarations across 6 files)
**Phase 6**: Temporal/ (75 declarations across 7 files) -- parallels Bimodal, can reuse docstring patterns

Each phase targets a coherent subdirectory and can be verified independently with `lake lint`.
