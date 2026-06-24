# Research Report: MCS Generic Migration (Task 338)

## Problem Statement

Migrate `Propositional/Metalogic/MCS.lean` and `Temporal/Metalogic/MCS.lean` to use
`Foundations/Logic/Metalogic/GenericMCS.lean` (and `MCSProperties.lean`), following the
pattern established by `Modal/Metalogic/GenericMCSBridge.lean`. The goal is to eliminate
~160 lines of MCS wrapper boilerplate while preserving all downstream API.

## Architecture Gap: Two Derivation Systems

CSLib has two parallel derivation system architectures:

1. **Tree-based** (`propDerivationSystem`, `temporalDerivationSystem`, `modalDerivationSystem`):
   Each wraps a logic-specific `DerivationTree` inductive with explicit constructors
   (axiom, modus_ponens, weakening, assumption, and for temporal: `temporal_necessitation`,
   `temporal_duality`).

2. **Algebraic** (`algebraicDerivationSystem` from `GenericMCS.lean`): Uses `ListDeriv`
   (provability of list-implication) via `MinimalHilbert` typeclass. No necessitation or
   duality rules.

`GenericMCSBridge.lean` (lines 46-60) documents this gap for Modal logics:
`algebraicDerivationSystem` has NO necessitation rule, so the two systems are NOT equivalent
on the full modal/temporal fragment. They ARE equivalent on the propositional fragment, but
this equivalence has not been proved.

## File Analysis

### Propositional MCS (163 lines)

**File**: `Cslib/Logics/Propositional/Metalogic/MCS.lean`

| Region | Lines | Content |
|--------|-------|---------|
| Abbreviations | 47-54 (8 lines) | `PropSetConsistent`, `PropSetMaximalConsistent` |
| Generic wrappers | 60-106 (46 lines) | lindenbaum, closed_under_derivation, implication_property, negation_complete |
| Propositional-specific | 110-161 (52 lines) | bot_not_mem, neg_of_not_mem, not_mem_of_neg, mem_iff_neg_not_mem |

**Key complication**: Propositional MCS is parameterized over arbitrary
`Axioms : PL.Proposition Atom -> Prop`, not tied to a specific tag type like `HilbertCl`.
The `algebraicDerivationSystem` requires a specific `S` with `MinimalHilbert S` instance.
There is no `MinimalHilbert` instance for arbitrary axiom predicates -- only for concrete
tag types (`HilbertCl`, `HilbertMin`, `HilbertInt`).

**Downstream consumers**: `StrongCompleteness.lean` uses `prop_closed_under_derivation`,
`prop_mcs_bot_not_mem`, `prop_negation_complete`, `PropSetMaximalConsistent`,
`propDerivationSystem`. `IntStrongCompleteness.lean` and `IntLindenbaum.lean` use
`PropSetConsistent`, `propDerivationSystem` directly with `IntPropAxiom`.

### Temporal MCS (485 lines)

**File**: `Cslib/Logics/Temporal/Metalogic/MCS.lean`

| Region | Lines | Content |
|--------|-------|---------|
| Abbreviations | 50-58 (9 lines) | `Temporal.SetConsistent`, `Temporal.SetMaximalConsistent` |
| Generic wrappers | 62-95 (34 lines) | lindenbaum, closed_under_derivation, implication_property, negation_complete, theoremInMcs |
| Basic MCS properties | 99-140 (42 lines) | mcs_mp_axiom, bot_not_mem, neg_of_not_mem, not_mem_of_neg, mem_iff_neg_not_mem |
| Temporal-specific | 142-484 (342 lines) | deriveContrapositive, mcs_g_mp, mcs_h_mp, futureSet/pastSet, derive_g/h_contradiction, mcs_g/h_witness |

**Key structural issue**: Temporal-specific properties (lines 142-484) use
`DerivationTree.temporal_necessitation` and `DerivationTree.temporal_duality` extensively
(8+ call sites). These constructors exist only in the tree-based system. The algebraic
system cannot express necessitation. These 342 lines are NOT boilerplate and MUST remain.

**Positive factor**: Unlike Propositional, `temporalDerivationSystem` is NOT parameterized --
it uses fixed temporal axioms at `FrameClass.Base`. Temporal has
`ClassicalHilbert HilbertBX` (which extends `MinimalHilbert`). So the generic wrappers
COULD theoretically be replaced by `MCSProperties.lean` instantiated with `S := HilbertBX`.

**Downstream consumers**: `DenseCompleteness.lean`, `DenseMCS.lean`,
`Chronicle/OrderedSeedConsistency.lean` use `temporal_lindenbaum`,
`temporal_closed_under_derivation`, `temporal_implication_property`,
`temporal_negation_complete`, `mcs_bot_not_mem`, `mcs_neg_of_not_mem`,
`mcs_mem_iff_neg_not_mem`, `mcs_mp_axiom`, `theoremInMcs`,
`Temporal.SetMaximalConsistent`, `Temporal.SetConsistent`.

### GenericMCS and MCSProperties (Already Available)

**`GenericMCS.lean`** (95 lines): Provides `algebraicDerivationSystem`,
`algebraic_has_deduction_theorem`, `algebraic_mcs_closed_under_derivation`,
`algebraic_mcs_implication_property`, `algebraic_mcs_negation_complete`.

**`MCSProperties.lean`** (127 lines): Provides `AlgebraicMCS`, `mcs_bot_not_mem`,
`mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem`,
`mcs_mp_axiom`, `mcs_theorem_in_mcs`. All parameterized over `MinimalHilbert S`.

### Modal GenericMCSBridge (Reference Pattern)

**`GenericMCSBridge.lean`** (122 lines): Documentation-only file. Documents the gap
between the two derivation systems. Contains NO Lean code -- no bridge theorem is proved.
The "pattern established by GenericMCSBridge" is actually just gap documentation,
not a working migration template.

## Blocking Issue

The migration requires answering: can `SetMaximalConsistent temporalDerivationSystem Ω`
be used interchangeably with `SetMaximalConsistent (algebraicDerivationSystem (S := HilbertBX)) Ω`?

This requires proving equivalence of the two derivation systems on the propositional fragment:

```
∀ Γ φ, temporalDerivationSystem.Deriv Γ φ ↔ algebraicDerivationSystem (S := HilbertBX).Deriv Γ φ
```

This equivalence is precisely the **unresolved future work** identified in GenericMCSBridge.lean
(lines 89-95). Without it, changing the abbreviation type breaks all downstream consumers.

## Recommended Approach

### Phase 1: Propositional Fragment Equivalence (Prerequisite)

Prove that for any logic with `ClassicalHilbert S`, the `algebraicDerivationSystem` and
tree-based derivation systems agree on the propositional fragment. This is:

- (→) Induction on `DerivationTree`: axiom/assumption/mp/weakening cases map to
  corresponding `ListDeriv` constructions.
- (←) Induction on `ListDeriv`: each constructor maps to a `DerivationTree` constructor
  via the Hilbert instance's axiom witnesses.

The necessitation/duality cases are excluded (only propositional fragment). This proof
is straightforward but has not been written yet.

### Phase 2: Temporal Migration (~76 lines saved)

1. Prove `Temporal.Deriv Γ φ → ListDeriv (S := HilbertBX) Γ φ` (propositional fragment
   direction -- exclude temporal_necessitation/duality cases).
2. Prove `ListDeriv (S := HilbertBX) Γ φ → Temporal.Deriv Γ φ` (backward direction).
3. Use these to define `Temporal.SetConsistent`/`Temporal.SetMaximalConsistent` as aliases
   to `AlgebraicMCS (S := HilbertBX)`, preserving downstream types.
4. Replace generic wrappers (lines 62-95) with direct calls to `MCSProperties`.
5. Replace basic MCS properties (lines 99-140) with direct calls to `MCSProperties`.
6. Keep all temporal-specific properties (lines 142-484) unchanged.

### Phase 3: Propositional Migration (~98 lines saved, higher risk)

This is more complex because `propDerivationSystem` is parameterized over arbitrary `Axioms`.
Options:

- **Option A**: Prove equivalence per-axiom-set (`PropositionalAxiom`, `IntPropAxiom`,
  `MinPropAxiom`) and replace wrappers for each.
- **Option B**: Prove a generic equivalence theorem parameterized over axiom predicates that
  satisfy certain closure properties matching `MinimalHilbert`.
- **Option C**: Keep the Propositional MCS as-is and only migrate Temporal.

### Recommendation

Start with Phase 1 + Phase 2 (Temporal only). This gives ~76 lines of boilerplate
eliminated with moderate risk. Phase 3 (Propositional) should be a follow-up task due to
the parameterization complexity.

If the equivalence proof in Phase 1 is deemed out of scope for this task, the task should
be marked [BLOCKED] -- without it, no migration is possible without breaking downstream types.

## Line Count Summary

| Category | Propositional | Temporal | Total |
|----------|--------------|----------|-------|
| Theoretically replaceable | ~98 lines | ~76 lines | ~174 lines |
| Must remain (temporal-specific) | N/A | ~342 lines | ~342 lines |
| Prerequisite (equiv proof) | ~30-50 lines | (included) | ~30-50 lines |

## Key Files

| File | Role |
|------|------|
| `Cslib/Logics/Propositional/Metalogic/MCS.lean` | Migration target |
| `Cslib/Logics/Temporal/Metalogic/MCS.lean` | Migration target |
| `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` | Generic algebraic derivation system |
| `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` | Generic MCS bot/neg/membership lemmas |
| `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` | Gap analysis (documentation only) |
| `Cslib/Logics/Temporal/ProofSystem/Instances.lean` | `ClassicalHilbert HilbertBX` instance |
| `Cslib/Logics/Propositional/ProofSystem/Instances.lean` | `ClassicalHilbert HilbertCl` instance |
| `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` | Downstream consumer |
| `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` | Downstream consumer |
| `Cslib/Logics/Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean` | Downstream consumer |

## Risks

1. **Equivalence proof complexity**: The propositional fragment equivalence should be
   straightforward but has not been attempted. Unknown unknowns may exist.
2. **Downstream breakage**: Changing abbreviation definitions changes the type of `h_mcs`
   arguments throughout downstream files. Even if logically equivalent, Lean may not
   unfold the new definitions automatically.
3. **Definitional vs propositional equality**: If the equivalence is only propositional
   (not definitional), downstream proofs may need `rw` or `convert` calls, partially
   negating the line savings.
4. **Propositional parameterization**: The arbitrary `Axioms` parameter in Propositional
   MCS has no direct analog in the `MinimalHilbert` typeclass world.
