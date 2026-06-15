# Research Report: First Temporal/ PR -- Classical Propositional Foundations

## What PR #648 Establishes

PR #648 (feat(Logics/Propositional): five-primitive formula type with connective typeclasses) introduces:

1. **`Cslib/Foundations/Logic/Connectives.lean`** (79 lines): A typeclass hierarchy for logical connectives:
   - Atomic classes: `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`, `HasUntil`, `HasSince`
   - Bundled classes: `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`

2. **Modified `Cslib/Logics/Propositional/Defs.lean`**: Five-primitive `Proposition` type `{atom, bot, imp, and, or}` with constraint-free derived connectives.

3. **Modified `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`**: Updated constructors.

**Critical dependency**: The `TemporalConnectives` class defined in PR #648's `Connectives.lean` is what `Temporal.Formula` registers as an instance of. Therefore, the first Temporal PR MUST be based on PR #648 (or submitted after it merges).

## Current State of Upstream vs. Local

### Upstream (`leanprover/cslib` main)
- `Foundations/Logic/`: Only `InferenceSystem.lean` and `LogicalEquivalence.lean`
- `Logics/`: `HML/`, `LinearLogic/`, `Modal/`, `Propositional/` (no Temporal)
- No `Connectives.lean`, `Axioms.lean`, `ProofSystem.lean`, or `Theorems/` directory

### Local (this branch)
- Full Temporal development: 14,793 LOC across 39 files
- Includes soundness, completeness (base + dense), conservative extension
- Depends on `Foundations/Logic/ProofSystem.lean` (524 LOC), `Axioms.lean` (359 LOC), `Theorems/` (1,580 LOC)

## Recommended ~300 LOC PR Subset

### Approach: "Temporal Formula Type with Propositional Structure"

Submit a single new file containing the temporal formula type definition and its propositional-level structural properties. This is the natural follow-up to PR #648 because it instantiates `TemporalConnectives` for a concrete formula type.

### File: `Cslib/Logics/Temporal/Syntax/Formula.lean` (~310 LOC)

Content (lines 1-310 of current file):

| Section | Lines | Content |
|---------|-------|---------|
| Header + imports | 1-14 | Copyright, module, imports (`Cslib.Init`, `Connectives`, `Encodable`, `Denumerable`, `Finset`) |
| Module docstring | 15-39 | Documentation of formula type and Burgess convention |
| Inductive type | 45-57 | `Formula Atom` with 5 constructors: `atom`, `bot`, `imp`, `untl`, `snce` |
| Derived connectives | 59-75 | `neg`, `top`, `or`, `and`, `iff` as `abbrev`s |
| Derived temporal ops | 77-95 | `someFuture`, `allFuture`, `somePast`, `allPast` |
| Notation | 97-107 | Scoped notation for all operators |
| Typeclass instances | 109-118 | `TemporalConnectives`, `Bot`, `Top` instances |
| Countability | 138-233 | `atom_injective`, `encodeNat`, `encodeNat_injective`, `Countable`, `Infinite`, `Denumerable` |
| BEq laws | 236-310 | `beq_refl`, `eq_of_beq`, `ReflBEq`, `LawfulBEq` instances |

### What Is Excluded (future PRs)

| Future PR | Content | LOC |
|-----------|---------|-----|
| PR 2 | Complexity measure, temporal depth, implication count | ~70 |
| PR 3 | Derived temporal operators (next, prev, release, trigger, weakUntil, etc.) | ~90 |
| PR 4 | swapTemporal duality transformation + theorems | ~80 |
| PR 5 | needsPositiveHypotheses, atoms collection | ~50 |
| PR 6 | Context.lean (contexts for derivations) | 131 |
| PR 7 | ProofSystem (Axioms + Derivation + Derivable + Instances) | ~650 |
| PR 8 | Semantics (Model + Satisfies + Validity) | ~435 |
| PR 9+ | Metalogic (Soundness, Completeness, etc.) | ~12,500 |

### Why This Scoping Works

1. **Self-contained**: Only depends on `Cslib.Init` + `Cslib.Foundations.Logic.Connectives` (from PR #648) + Mathlib (`Encodable`, `Denumerable`, `Finset`)
2. **Natural boundary**: Line 310 is `end BEqLaws` -- a clean section boundary
3. **Meaningful contribution**: Establishes the temporal formula type that ALL future temporal work builds on
4. **Classical propositional content**: The derived connectives (neg, top, and, or, iff) are classical propositional logic concepts; countability and BEq are structural properties any formula type needs
5. **~310 LOC**: Within the target budget

## Dependencies and Import Structure

```
Cslib.Init
  |
  v
Cslib.Foundations.Logic.Connectives  [from PR #648]
  |
  v
Cslib.Logics.Temporal.Syntax.Formula  [THIS PR]
  (also imports: Mathlib.Logic.Encodable.Basic,
                 Mathlib.Logic.Denumerable,
                 Mathlib.Data.Finset.Basic)
```

### Mathlib Dependencies

The current `Formula.lean` imports:
- `Mathlib.Logic.Encodable.Basic` -- for `Encodable` class
- `Mathlib.Logic.Denumerable` -- for `Denumerable` class  
- `Mathlib.Data.Finset.Basic` -- for `Finset` (used in `atoms` function on line 559)

For the truncated ~310 LOC version, `Finset` is NOT needed (the `atoms` function is in the excluded temporal-specific section). We can remove that import:

**Required imports for 310-line version:**
```lean
public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Logic.Denumerable
```

## PR Metadata

### Title
`feat(Logics/Temporal): temporal formula type with propositional structure`

### Description Structure
- Five-primitive formula type `{atom, bot, imp, untl, snce}`
- Derived propositional connectives (neg, top, and, or, iff)
- `TemporalConnectives` instance (connecting to PR #648)
- `Countable`, `Infinite`, `Denumerable` instances
- `ReflBEq`, `LawfulBEq` instances

### Relationship to Other PRs
- **Depends on PR #648**: Uses `TemporalConnectives` from `Connectives.lean`
- **Independent of PR #607** (fmontesi's Operators/): Both can coexist

## Risks and Issues

### 1. PR #648 Must Merge First
The temporal formula file imports `Cslib.Foundations.Logic.Connectives` which PR #648 introduces. This PR cannot be submitted until #648 merges, OR it must be based on the `feat/propositional-v2` branch.

**Mitigation**: Base the PR branch on `feat/propositional-v2` or wait for merge.

### 2. `module` Keyword
The current file uses `module` (Lean 4 vNext feature). The upstream cslib may or may not support this. Need to verify if the upstream CI Lean toolchain supports `module`.

**Mitigation**: Check upstream `lean-toolchain` version. If `module` is not supported, replace with `namespace` + explicit imports.

### 3. `@[expose] public section`
This is a CSLib-specific attribute (defined in `Cslib.Init`). It should work fine since the file imports `Cslib.Init`.

### 4. Scope Creep
The full `Formula.lean` (582 lines) is tempting to submit as one file, but the temporal-specific content (swapTemporal, derived operators, complexity) would mix propositional and temporal concerns in a single PR.

**Mitigation**: Strict 310-line boundary. Temporal content goes in follow-up PRs.

### 5. Mathlib Import Minimization
`lake shake` may flag that some Mathlib imports can be reduced. The `Encodable.Basic` and `Denumerable` imports should be verified as minimal.

### 6. Naming Convention Review
The Burgess convention (untl event guard vs. standard LTL untl guard event) may draw reviewer questions. The module doc explains this thoroughly.

## Contribution Roadmap (Temporal)

Following the pattern established in PR #648's roadmap for Propositional:

1. **This PR**: Temporal formula type + propositional structure (310 LOC)
2. **PR 2**: Temporal operators + swapTemporal duality (240 LOC)
3. **PR 3**: Context + BigConj (183 LOC)
4. **PR 4**: Subformulas (218 LOC)  
5. **PR 5**: Axioms + Derivation + Derivable (432 LOC) -- requires Foundations/Logic/ProofSystem first
6. **PR 6**: Instances (connects to Foundations/Logic/ProofSystem) (214 LOC)
7. **PR 7**: Semantics (Model + Satisfies + Validity) (435 LOC)
8. **PR 8**: FromPropositional + ConservativeExtension (192 LOC)
9. **PR 9+**: Soundness, Completeness (multi-PR, 12,500 LOC)

**Blocker**: PRs 5-6 require `Foundations/Logic/ProofSystem.lean` and `Foundations/Logic/Axioms.lean` to be submitted upstream as separate Foundations PRs first.

## CI Verification Checklist

For the first Temporal PR:
- [ ] `lake build Cslib.Logics.Temporal.Syntax.Formula`
- [ ] `lake exe checkInitImports` (verify `Cslib.Init` import)
- [ ] `lake exe lint-style`
- [ ] `lake test`
- [ ] `lake exe mk_all --module` (update `Cslib.lean`)
- [ ] `lake shake --add-public --keep-implied --keep-prefix`
