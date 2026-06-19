# Research Report: Revise `untl`/`snce` Convention from Burgess to Standard LTL

## Task 234

## Executive Summary

The CSLib codebase currently uses the **Burgess 1982 convention** for `untl` and `snce`:
the first argument is the **event** (holds at the witness point) and the second is the **guard**
(holds at all intermediate points). The task is to swap to the **standard LTL convention**
where the first argument is the **guard** and the second is the **event**.

This is a **mechanical but large-scale refactoring** affecting **74 files** with approximately
**2,530 lines** referencing `.untl` or `.snce` constructors. The change is purely syntactic at
the definition level and propagates uniformly through all downstream code. No semantic changes
are needed -- the satisfaction relations, axiom schemas, and proofs all remain logically
identical once the argument positions are swapped consistently.

## 1. Current Convention (Burgess 1982)

### Definition

In the current codebase, `untl` and `snce` follow the Burgess convention:

```
untl(event, guard)   -- arg1 = EVENT (holds at witness point s)
                     -- arg2 = GUARD (holds at all points between t and s)

snce(event, guard)   -- arg1 = EVENT (holds at witness point s)
                     -- arg2 = GUARD (holds at all points between s and t)
```

### Semantics (current)

From `Cslib/Logics/Temporal/Semantics/Satisfies.lean`:
```lean
| .untl phi psi =>
    exists s, t < s /\ Satisfies M s phi /\        -- phi = EVENT at witness s
      forall r, t < r -> r < s -> Satisfies M r psi  -- psi = GUARD between
| .snce phi psi =>
    exists s, s < t /\ Satisfies M s phi /\        -- phi = EVENT at witness s
      forall r, s < r -> r < t -> Satisfies M r psi  -- psi = GUARD between
```

### Derived Operators (current)

```lean
-- someFuture phi = untl phi top  (phi is event, top is trivial guard)
-- somePast phi = snce phi top    (phi is event, top is trivial guard)
-- next phi = untl phi bot        (phi is event, bot forces immediate step)
-- prev phi = snce phi bot        (phi is event, bot forces immediate step)
-- G(phi) = neg(untl (neg phi) top)  -- neg phi is event
-- H(phi) = neg(snce (neg phi) top)  -- neg phi is event
```

## 2. Target Convention (Standard LTL)

### Definition

The standard temporal logic convention (Pnueli 1977, Emerson 1990, Baier & Katoen):

```
untl(guard, event)   -- arg1 = GUARD (holds at all intermediate points)
                     -- arg2 = EVENT (holds at witness point)

snce(guard, event)   -- arg1 = GUARD (holds at all intermediate points)
                     -- arg2 = EVENT (holds at witness point)
```

### Semantics (target)

After the change:
```lean
| .untl phi psi =>
    exists s, t < s /\ Satisfies M s psi /\        -- psi = EVENT at witness s
      forall r, t < r -> r < s -> Satisfies M r phi  -- phi = GUARD between
| .snce phi psi =>
    exists s, s < t /\ Satisfies M s psi /\        -- psi = EVENT at witness s
      forall r, s < r -> r < t -> Satisfies M r phi  -- phi = GUARD between
```

### Derived Operators (target)

```lean
-- someFuture phi = untl top phi  (top is trivial guard, phi is event)
-- somePast phi = snce top phi    (top is trivial guard, phi is event)
-- next phi = untl bot phi        (bot forces immediate step, phi is event)
-- prev phi = snce bot phi        (bot forces immediate step, phi is event)
-- G(phi) = neg(untl top (neg phi))  -- top is trivial guard, neg phi is event
-- H(phi) = neg(snce top (neg phi))  -- top is trivial guard, neg phi is event
```

## 3. Scope of Changes

### 3.1 Foundations Layer (3 files)

These define the typeclass-level operators and polymorphic axioms:

| File | Changes Needed |
|------|---------------|
| `Cslib/Foundations/Logic/Connectives.lean` | Docstrings only -- `HasUntil`, `HasSince` docstrings should clarify new convention |
| `Cslib/Foundations/Logic/Axioms.lean` | **All 22 temporal axiom `abbrev`s** must swap arg order in every `HasUntil.untl` and `HasSince.snce` call. Also update all `-- where G(alpha) = ...` comments. |
| `Cslib/Foundations/Logic/ProofSystem.lean` | `TemporalNecessitation` class: swap args in `tempNec` and `tempNecPast` (G and H definitions use `untl`/`snce` directly) |

### 3.2 Foundations Theorems (2 files)

| File | Changes Needed |
|------|---------------|
| `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` | `someFuture`/`somePast` abbrevs swap args; docstrings updated; convention comment updated |
| `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` | Only if it references `untl`/`snce` (minor) |

### 3.3 Temporal Logic (12 files)

| File | Changes Needed |
|------|---------------|
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | **Core swap site**: `Formula.someFuture`, `somePast`, `next`, `prev`, `release`, `trigger`, `weakUntil`, `weakSince`, `strongRelease`, `strongTrigger`, `reflexiveUntl`, `reflexiveSnce`, `complexity` pattern matches, `weakFuture`/`weakPast` -- plus all docstrings/comments |
| `Cslib/Logics/Temporal/Syntax/Subformulas.lean` | Minor -- no arg-order dependency in subformula collection |
| `Cslib/Logics/Temporal/Semantics/Satisfies.lean` | Swap semantic definition for `untl`/`snce` cases; update `untl_iff`, `snce_iff`, `someFuture_iff`, `somePast_iff`, `allFuture_iff`, `allPast_iff` |
| `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` | All 26 axiom constructors that reference `Formula.untl`/`Formula.snce` swap args |
| `Cslib/Logics/Temporal/ProofSystem/Instances.lean` | Instance registrations -- may need swap if they reference `untl`/`snce` directly |
| `Cslib/Logics/Temporal/FromPropositional.lean` | Embedding -- minor |
| `Cslib/Logics/Temporal/Metalogic/*.lean` | 8 files: `WitnessSeed`, `DenseCompleteness`, `DenseSoundness`, `DenseMCS`, `TemporalContent`, `Soundness`, `Completeness`, `Chronicle/*` (6 sub-files) |

### 3.4 Bimodal Logic (47+ files)

The largest area of impact. The Bimodal logic uses `untl`/`snce` extensively in:

| Subsystem | File Count | Complexity |
|-----------|-----------|------------|
| `Syntax/` | 5 files | Formula definition, subformulas, subformula closure, nesting depth, temporal formulas |
| `Semantics/` | 1 file | `Truth.lean` -- swap truthAt definition |
| `ProofSystem/` | 3 files | Axioms, instances, substitution |
| `Theorems/` | 2 files | TemporalDerived, Perpetuity helpers |
| `Embedding/` | 2 files | Propositional and temporal embedding |
| `Metalogic/Soundness/` | 4 files | Core, DenseValidity, FrameClassVariants, Soundness |
| `Metalogic/Bundle/` | 6 files | CanonicalFrame, SuccRelation, TemporalCoherence, TemporalContent, UntilSinceCoherence, WitnessSeed |
| `Metalogic/BXCanonical/` | 10 files | TruthLemma, Frame, CanonicalChain, Filtration, Chronicle (6 files), Quasimodel (2 files), Completeness |
| `Metalogic/Separation/` | 12 files | Defs, NormalForm, Eliminations, DualEliminations, Distributivity, FormulaOps, IntHelpers, NegationEquiv, TemporalClosure, SeparationThm, Hierarchy (4 files), DedekindZ (2 files) |
| `Metalogic/ConservativeExtension/` | 4 files | ExtFormula, ExtDerivation, Lifting, Substitution |
| `Metalogic/Decidability/` | 7 files | SignedFormula, Tableau, Saturation, AxiomMatcher, CountermodelExtraction, TraceCertificate, FMP (2 files) |
| `Metalogic/Algebraic/` | 3 files | ParametricCompleteness, ParametricTruthLemma, RestrictedParametricTruthLemma |

### 3.5 LTL Logic (2 files)

| File | Changes Needed |
|------|---------------|
| `Cslib/Logics/LTL/Syntax/Formula.lean` | `someFuture` abbrev swap; `toTemporal` embedding swap; docstrings |
| `Cslib/Logics/LTL/Semantics/Satisfies.lean` | `Satisfies` definition for `.untl` case swap args in existential |

### 3.6 Other Files (3 files)

| File | Changes Needed |
|------|---------------|
| `Cslib/Computability/Languages/OmegaLanguage.lean` | If it references `untl`/`snce` directly (check) |
| `Cslib/Logics/Propositional/*.lean` | No `untl`/`snce` references |
| `Cslib/Logics/Modal/*.lean` | No `untl`/`snce` references |

## 4. Nature of Changes

### 4.1 Mechanical Swap Pattern

The core transformation is a **positional argument swap** applied uniformly:

```
BEFORE: .untl phi psi   -- phi=event, psi=guard
AFTER:  .untl psi phi   -- psi=guard, phi=event (i.e., first arg is now guard)

BEFORE: .snce phi psi   -- phi=event, psi=guard
AFTER:  .snce psi phi   -- psi=guard, phi=event
```

This applies to:
- Inductive constructor patterns (e.g., `| .untl phi psi => ...`)
- Constructor applications (e.g., `Formula.untl expr1 expr2`)
- HasUntil/HasSince typeclass calls (e.g., `HasUntil.untl expr1 expr2`)
- Notation uses (e.g., `phi U psi` becomes `psi U phi` when the notation binds `U` to `untl`)

**CRITICAL NOTE on notation**: The infix notation `phi U psi` desugars to `Formula.untl phi psi`.
After the swap, if `U` still desugars to `Formula.untl`, then `phi U psi` would mean
"phi is guard, psi is event" which matches standard LTL (`phi U psi` = "phi holds until psi").
This is the correct behavior -- **the notation itself does NOT need to change**, only the
underlying constructor semantics.

### 4.2 What Does NOT Change

- The **inductive type definitions** themselves (constructor names `untl`, `snce` stay the same)
- The **notation declarations** (`U`, `S` infix operators)
- The **import structure** and file organization
- The **proof strategies** -- only argument positions in pattern matches change
- The **typeclass hierarchy** (`HasUntil`, `HasSince`, etc.)

### 4.3 Semantic Definition Change

The `Satisfies` definitions in both Temporal and Bimodal semantics swap which argument is
checked at the witness vs. intermediate points. This is the **semantic anchor** of the change --
all other changes are driven by maintaining consistency with this swap.

### 4.4 Pattern Match Changes

Files with `match`/`fun` pattern matching on `.untl phi psi` or `.snce phi psi` need the
body logic adjusted so that `phi` (now guard) and `psi` (now event) are used correctly.
This is the **highest-risk area** because the variable names may stay the same but their
semantic role changes.

### 4.5 Comment and Docstring Updates

Approximately **557 lines** across **33 files** reference "Burgess" in comments/docstrings.
These fall into two categories:

1. **Convention documentation** (must update): References to "Burgess convention" explaining
   arg order. Change to "standard LTL convention" or simply remove the convention notes.
2. **Citation references** (keep as-is): References to "Burgess 1982", "Burgess 1984" as
   literature citations for the BX axiom system. These stay -- the axiom system itself is
   still the Burgess-Xu system; only the arg order convention changes.

## 5. Risk Assessment

### 5.1 Low Risk

- **Foundations layer**: Small number of files (3), highly regular changes
- **Notation**: Does not change -- `phi U psi` naturally reads as standard LTL after the swap
- **Import structure**: No changes needed
- **Type signatures**: No changes to theorem types (only to how formulas are constructed)

### 5.2 Medium Risk

- **Pattern match bodies**: In complex proofs (Separation, Decidability), pattern-matched
  variables named `phi`/`psi` or `h_event`/`h_guard` must have their roles swapped correctly
  in the proof body. Variable naming like `h_event` and `h_guard` helps -- these should be
  re-bound to match the new positions.
- **Complexity function**: The `complexity` function in `Temporal/Syntax/Formula.lean` has
  specialized pattern matches for derived operators (e.g., `F(phi) = untl phi top` becomes
  `untl top phi`). All 12+ patterns must be updated.

### 5.3 Higher Risk

- **Bimodal Metalogic (47+ files)**: The sheer volume of changes in the Bimodal metalogic
  subsystem creates risk of missed swaps. The `Separation/` and `BXCanonical/` directories
  are particularly dense with `untl`/`snce` usage.
- **Proof consistency**: After swapping args, all proofs must still type-check. Since the
  semantics swap correspondingly, proofs should still work with the same logic, but any
  proof that destructures an until/since existential (e.g., `obtain <s, hlt, h_event, h_guard>`)
  needs the event and guard components to match the new positions.

## 6. Implementation Strategy

### Recommended Approach: Bottom-Up Mechanical Swap

**Phase 1: Foundations** (3 files)
1. `Cslib/Foundations/Logic/Connectives.lean` -- docstrings only
2. `Cslib/Foundations/Logic/Axioms.lean` -- swap all `HasUntil.untl`/`HasSince.snce` args
3. `Cslib/Foundations/Logic/ProofSystem.lean` -- swap `TemporalNecessitation` args
4. `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` -- swap abbrevs

**Phase 2: Temporal Logic** (12 files)
1. `Temporal/Syntax/Formula.lean` -- core swap site
2. `Temporal/Semantics/Satisfies.lean` -- semantic definition
3. `Temporal/ProofSystem/Axioms.lean` -- axiom schemas
4. Remaining Temporal files

**Phase 3: LTL** (2 files)
1. `LTL/Syntax/Formula.lean`
2. `LTL/Semantics/Satisfies.lean`

**Phase 4: Bimodal Syntax/Semantics/ProofSystem** (9 files)
1. `Bimodal/Syntax/Formula.lean` -- core swap
2. `Bimodal/Semantics/Truth.lean` -- semantic definition
3. `Bimodal/ProofSystem/Axioms.lean` -- axiom schemas
4. Remaining syntax/semantics/proof system files

**Phase 5: Bimodal Metalogic** (40+ files)
Subdivide by subsystem:
- 5a: Soundness (4 files)
- 5b: Bundle (6 files)
- 5c: BXCanonical (10 files)
- 5d: Separation (12 files)
- 5e: ConservativeExtension (4 files)
- 5f: Decidability (7 files)
- 5g: Algebraic (3 files)

**Phase 6: Remaining files** (embeddings, other)

**Phase 7: Verification**
- `lake build` full project
- `lake test`
- `lake lint`
- Verify no remaining "Burgess convention" references (unless citing the paper itself)

### Key Invariant

At every phase boundary, the project should still build (`lake build`). This means each phase
must be done as a complete, self-consistent unit. Since the Foundations layer defines the
typeclasses that all other layers instantiate, Phase 1 changes will cause downstream build
failures until the corresponding formula types and instances are updated. Therefore, **Phases
1-4 should be done as a single atomic commit** or in rapid succession.

## 7. Verification Checklist

After implementation, verify:

- [ ] All `HasUntil.untl` calls have arg1=guard, arg2=event
- [ ] All `HasSince.snce` calls have arg1=guard, arg2=event
- [ ] All `Formula.untl` constructor uses have arg1=guard, arg2=event
- [ ] All `Formula.snce` constructor uses have arg1=guard, arg2=event
- [ ] `someFuture phi = untl top phi` (not `untl phi top`)
- [ ] `somePast phi = snce top phi` (not `snce phi top`)
- [ ] Satisfaction relation: `untl phi psi` at t = exists s > t, psi at s AND phi between
- [ ] No remaining "Burgess convention" documentation for arg order
- [ ] Burgess paper citations preserved (literature references stay)
- [ ] `lake build` passes
- [ ] `lake test` passes
- [ ] `lake lint` passes
- [ ] `lake exe checkInitImports` passes

## 8. File Impact Summary

| Category | File Count | Line Estimate |
|----------|-----------|---------------|
| Foundations | 4 | ~120 lines |
| Temporal Logic | 12 | ~300 lines |
| LTL | 2 | ~30 lines |
| Bimodal Syntax/Semantics/ProofSystem | 9 | ~200 lines |
| Bimodal Metalogic | 40+ | ~1,800 lines |
| Other | 3 | ~30 lines |
| Docstrings/Comments | 33 files | ~557 Burgess references to review |
| **Total** | **~74 files** | **~2,530 lines** |
