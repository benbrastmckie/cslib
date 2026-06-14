# Teammate B Findings: File Structure, Standards, and Documentation

## 1. Proposed Merged File Layout

### Section Order (consistent across all 3 files)

After merging Completeness.lean into each StrongCompleteness.lean, each file should follow this canonical section order:

```
1. Module header (copyright, imports, module docstring)
2. Namespace + universe declarations
3. Canonical Model / Valuation definitions
4. Truth Lemma helpers (per-connective, if applicable)
5. Truth Lemma (main)
6. Strong Soundness
7. Consistency / DNE helpers
8. Strong Completeness
9. Biconditional wrapper (strong completeness iff)
10. Compactness Corollary
11. Weak Completeness Corollary
12. Weak Completeness biconditional
13. End namespace
```

### Rationale

- Canonical model and truth lemma form the **infrastructure** used by the completeness theorems, so they must come first.
- Strong soundness is logically independent of the canonical model (it does not use the truth lemma), but placing it before strong completeness matches the reader's expectation: soundness before completeness.
- Weak completeness and compactness are corollaries of strong completeness, so they come last.

### Per-File Specifics

**StrongCompleteness.lean** (Classical):
1. Imports: SemanticConsequence, Soundness, MCS (replaces current Completeness import)
2. `canonicalValuation` definition
3. `prop_truth_lemma_atom`, `prop_truth_lemma_bot`, `prop_truth_lemma_and`, `prop_truth_lemma_or`, `prop_truth_lemma_imp`
4. `prop_truth_lemma`
5. `prop_strong_soundness`
6. `dne_from_neg_neg` (private helper)
7. `prop_not_SetDerivable_union_neg_consistent`
8. `prop_strong_completeness`
9. `prop_strong_completeness_iff`
10. `prop_compactness`
11. `prop_completeness`
12. `prop_completeness_iff_tautology`

**IntStrongCompleteness.lean** (Intuitionistic):
1. Imports: SemanticConsequence, IntSoundness, IntLindenbaum, Kripke (replaces current IntCompleteness import)
2. `IntCanonicalWorld` definition
3. `Preorder` instance for `IntCanonicalWorld`
4. `intCanonicalVal` definition
5. `intCanonicalVal_upward_closed`
6. `int_truth_lemma`
7. `int_strong_soundness`
8. `intDeductiveClosure_iff_SetDerivable`
9. `SetDerivable_efq_int`
10. `int_strong_completeness`
11. `int_strong_completeness_iff`
12. `int_compactness`
13. `int_completeness`
14. `int_soundness_completeness`

**MinStrongCompleteness.lean** (Minimal):
1. Imports: SemanticConsequence, MinSoundness, MinLindenbaum, Kripke (replaces current MinCompleteness import)
2. `MinCanonicalWorld` definition
3. `Preorder` instance for `MinCanonicalWorld`
4. `minCanonicalVal` + `minCanonicalVal_upward_closed`
5. `minBotForces` + `minBotForces_upward_closed`
6. `min_truth_lemma`
7. `min_strong_soundness`
8. `minDeductiveClosure_iff_SetDerivable`
9. `min_strong_completeness`
10. `min_strong_completeness_iff`
11. `min_compactness`
12. `min_completeness`
13. `min_soundness_completeness`

## 2. Convention Check: Comparison with Modal and Temporal

### Modal K Completeness Pattern

The Modal logic system uses a **2-level structure**:
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- shared canonical model infrastructure (CanonicalWorld, CanonicalModel, truth_lemma, frame properties)
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` -- K-specific completeness theorem + K-specific truth lemma variant

Key observation: **Modal K's Completeness.lean already combines canonical model + truth lemma + completeness theorem in a single file** (K/Completeness.lean is 301 lines with all three). The base Completeness.lean is shared infrastructure for T/S4/S5 variants. System-specific files (K, B, D, etc.) are self-contained for their logic.

**Convention**: Per-system completeness files are self-contained. The shared base exists only because the modal hierarchy has many variants that share a common truth lemma.

### Temporal Completeness Pattern

Temporal logic uses a **multi-file decomposition** due to complexity:
- `Chronicle/TruthLemma.lean` (232 lines) -- truth lemma
- `Chronicle/ChronicleConstruction.lean` -- model construction
- `Completeness.lean` (129 lines) -- final theorem assembly

**Convention**: Temporal splits because the chronicle construction is extremely complex (8+ files). This is the exception, not the norm.

### Propositional Pattern After Merge

The propositional logics have no shared parameterized infrastructure (unlike Modal's shared `Completeness.lean`). Each of the three propositional logics (Classical, Intuitionistic, Minimal) is fully independent with its own canonical model, truth lemma, and axiom system. This makes the 2-file split (Completeness + StrongCompleteness) an unnecessary indirection.

**Conclusion**: Merging into single files per logic is **consistent with CSLib conventions**. Modal K already does this. The propositional merge follows the same pattern -- self-contained completeness file per logic system.

## 3. Proposed Module Docstrings

### StrongCompleteness.lean

```lean
/-! # Completeness for Classical Propositional Logic

This module proves soundness and completeness for classical propositional logic
via the canonical valuation (MCS) construction.

## Main Definitions

- `canonicalValuation`: The canonical valuation from a maximally consistent set.

## Main Results

- `prop_truth_lemma`: `Evaluate (canonicalValuation S) φ ↔ φ ∈ S` for MCS `S`.
- `prop_strong_soundness`: `SetDerivable PropositionalAxiom Γ φ → SemanticEntails Γ φ`
- `prop_strong_completeness`: `SemanticEntails Γ φ → SetDerivable PropositionalAxiom Γ φ`
- `prop_strong_completeness_iff`: Biconditional combining both directions.
- `prop_compactness`: Semantic compactness from strong completeness.
- `prop_completeness`: `Tautology φ → Derivable PropositionalAxiom φ` (weak completeness).
- `prop_completeness_iff_tautology`: Weak soundness and completeness biconditional.

## Strategy

The canonical valuation assigns `atom p ↦ (atom p ∈ S)` for an MCS `S`.
The truth lemma is proved by structural recursion, dispatching to per-connective
helpers for atom, bot, and, or, and imp.

Strong soundness unfolds `SetDerivable` to get `L ⊆ Γ` and applies `prop_soundness`.

Strong completeness proceeds by contrapositive: if `φ` is not set-derivable from `Γ`,
then `Γ ∪ {¬φ}` is consistent, extends to an MCS via Lindenbaum, and the truth lemma
provides a countermodel.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16
-/
```

### IntStrongCompleteness.lean

```lean
/-! # Completeness for Intuitionistic Propositional Logic

This module proves soundness and completeness for intuitionistic propositional logic
via the canonical Kripke model construction using prime DCCS worlds.

## Main Definitions

- `IntCanonicalWorld`: Canonical world type (prime DCCS for `IntPropAxiom`).
- `intCanonicalVal`: Canonical Kripke valuation (`atom p ∈ w.val`).

## Main Results

- `int_truth_lemma`: `IForces intCanonicalVal (fun _ => False) S φ ↔ φ ∈ S.val`
- `int_strong_soundness`: `SetDerivable IntPropAxiom Γ φ → ISemanticEntails Γ φ`
- `int_strong_completeness`: `ISemanticEntails Γ φ → SetDerivable IntPropAxiom Γ φ`
- `int_strong_completeness_iff`: Biconditional combining both directions.
- `int_compactness`: Semantic compactness for intuitionistic Kripke semantics.
- `int_completeness`: `IValid φ → Derivable IntPropAxiom φ` (weak completeness).
- `int_soundness_completeness`: Weak soundness and completeness biconditional.

## Strategy

Canonical worlds are prime deductively closed consistent sets (IntDCCS). The
preorder is set inclusion. Primeness ensures the backward direction of the
truth lemma for disjunction; the imp case uses `int_imp_witness` and
`int_prime_exclusion`.

Strong completeness by contrapositive, with case split on consistency of
`intDeductiveClosure Γ`: inconsistent => EFQ; consistent => prime exclusion.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43
-/
```

### MinStrongCompleteness.lean

```lean
/-! # Completeness for Minimal Propositional Logic

This module proves soundness and completeness for minimal propositional logic
via the canonical Kripke model construction using prime MinTheory worlds.

## Main Definitions

- `MinCanonicalWorld`: Canonical world type (prime MinTheory for `MinPropAxiom`).
- `minCanonicalVal`: Canonical Kripke valuation (`atom p ∈ w.val`).
- `minBotForces`: Canonical bottom-forcing predicate (`⊥ ∈ w.val`).

## Main Results

- `min_truth_lemma`: `IForces minCanonicalVal minBotForces S φ ↔ φ ∈ S.val`
- `min_strong_soundness`: `SetDerivable MinPropAxiom Γ φ → MSemanticEntails Γ φ`
- `min_strong_completeness`: `MSemanticEntails Γ φ → SetDerivable MinPropAxiom Γ φ`
- `min_strong_completeness_iff`: Biconditional combining both directions.
- `min_compactness`: Semantic compactness for minimal Kripke semantics.
- `min_completeness`: `MValid φ → Derivable MinPropAxiom φ` (weak completeness).
- `min_soundness_completeness`: Weak soundness and completeness biconditional.

## Key Differences from Intuitionistic

- Worlds are MinTheory (no consistency requirement) instead of IntDCCS.
- `bot_forces w = (⊥ ∈ w.val)` is a genuine predicate, not trivially `False`.
- Bot case of truth lemma is `Iff.rfl` (trivial) instead of multi-step reasoning.
- `MValid` quantifies over arbitrary upward-closed `bot_forces`, not just `fun _ => False`.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43
-/
```

## 4. Naming Convention Review

### Current Naming Patterns

All three logics use consistent prefixes:
- Classical: `prop_` prefix (`prop_truth_lemma`, `prop_strong_completeness`, `prop_compactness`)
- Intuitionistic: `int_` prefix (`int_truth_lemma`, `int_strong_completeness`, `int_compactness`)
- Minimal: `min_` prefix (`min_truth_lemma`, `min_strong_completeness`, `min_compactness`)

### Assessment

The naming is already consistent. No renames needed. Specifically:

| Declaration | Prefix matches file? | Convention-compliant? |
|---|---|---|
| `canonicalValuation` | No prefix (generic classical) | Acceptable -- unique to classical |
| `prop_truth_lemma` | `prop_` matches classical | Yes |
| `prop_truth_lemma_atom/bot/and/or/imp` | `prop_` | Yes |
| `prop_strong_soundness` | `prop_` | Yes |
| `prop_strong_completeness` | `prop_` | Yes |
| `prop_completeness` | `prop_` | Yes |
| `prop_compactness` | `prop_` | Yes |
| `IntCanonicalWorld` | `Int` CamelCase for types | Yes (Lean convention) |
| `intCanonicalVal` | `int` camelCase for defs | Yes |
| `int_truth_lemma` | `int_` | Yes |
| `MinCanonicalWorld` | `Min` CamelCase for types | Yes |
| `minCanonicalVal` | `min` camelCase for defs | Yes |
| `min_truth_lemma` | `min_` | Yes |

### One Optional Rename

`canonicalValuation` (classical) lacks a prefix, while the Kripke variants use `intCanonicalVal` and `minCanonicalVal`. For consistency, it could be renamed to `propCanonicalValuation`. However, since it is the only classical canonical valuation and the `prop_` prefix on all its associated theorems makes the context clear, this is **optional and low priority**. The merge should not block on this.

### Private Helper Naming

`dne_from_neg_neg` (in StrongCompleteness.lean) is `private` and uses a descriptive name without prefix. This is fine per CSLib conventions -- private helpers do not need the logic-prefix.

## 5. Line Count Estimates

### Raw Addition (Before Deduplication)

| Merged File | Source A (Completeness) | Source B (StrongCompleteness) | Raw Total |
|---|---|---|---|
| StrongCompleteness.lean | 347 | 235 | 582 |
| IntStrongCompleteness.lean | 181 | 193 | 374 |
| MinStrongCompleteness.lean | 194 | 174 | 368 |

### After Deduplication

Each merge eliminates:
- Duplicate copyright headers (~5 lines each)
- Duplicate namespace/universe/variable blocks (~8-10 lines each)
- Duplicate import statements (replaced by union of imports, saves ~2-3 lines)
- Duplicate module docstrings (merged into one, saves ~15-25 lines of the old docstring)

Estimated savings per file: ~30-40 lines.

| Merged File | Estimated Final Size | Comparable Files |
|---|---|---|
| StrongCompleteness.lean | ~545 lines | Modal Completeness.lean (475), Modal K/Completeness.lean (301) |
| IntStrongCompleteness.lean | ~340 lines | Modal K/Completeness.lean (301) |
| MinStrongCompleteness.lean | ~335 lines | Modal K/Completeness.lean (301) |

### Acceptability Assessment

- **545 lines for StrongCompleteness.lean**: This is larger than any single Modal system completeness file but comparable to the shared Modal Completeness.lean (475 lines). The classical truth lemma has 5 per-connective helpers that inflate it. This is acceptable -- the file is self-contained and topically cohesive.
- **340 lines for IntStrongCompleteness.lean**: Well within norms. Similar to Modal K/Completeness.lean.
- **335 lines for MinStrongCompleteness.lean**: Well within norms.
- **No file exceeds 600 lines**, which would be the threshold where splitting should be reconsidered.
- **Verdict**: All three merged sizes are acceptable. No further splitting is needed.

### Splitting Consideration

The only file that might warrant future splitting is StrongCompleteness.lean, and only if the classical truth lemma helpers grew significantly. Currently, the per-connective helpers (atom, bot, and, or, imp) are 280 of the 347 lines in Completeness.lean. If a future change doubles those helpers, extracting them into a `TruthLemmaHelpers.lean` would be reasonable. But at current size, this is unnecessary.

## 6. Import Change Summary

### StrongCompleteness.lean
- **Remove**: `public import Cslib.Logics.Propositional.Metalogic.Completeness`
- **Add**: `public import Cslib.Logics.Propositional.Semantics.Basic` and `public import Cslib.Logics.Propositional.Metalogic.MCS`
- **Keep**: `public import Cslib.Logics.Propositional.Semantics.SemanticConsequence` and `public import Cslib.Logics.Propositional.Metalogic.Soundness`

Note: SemanticConsequence likely already transitively imports Semantics.Basic. Check whether removing the explicit Basic import still compiles. If so, only MCS is needed as a new explicit import.

### IntStrongCompleteness.lean
- **Remove**: `public import Cslib.Logics.Propositional.Metalogic.IntCompleteness`
- **Add**: `public import Cslib.Logics.Propositional.Semantics.Kripke` and `public import Cslib.Logics.Propositional.Metalogic.IntLindenbaum`
- **Keep**: `public import Cslib.Logics.Propositional.Semantics.SemanticConsequence` and `public import Cslib.Logics.Propositional.Metalogic.IntSoundness`

### MinStrongCompleteness.lean
- **Remove**: `public import Cslib.Logics.Propositional.Metalogic.MinCompleteness`
- **Add**: `public import Cslib.Logics.Propositional.Semantics.Kripke` and `public import Cslib.Logics.Propositional.Metalogic.MinLindenbaum`
- **Keep**: `public import Cslib.Logics.Propositional.Semantics.SemanticConsequence` and `public import Cslib.Logics.Propositional.Metalogic.MinSoundness`

Note: IntLindenbaum and MinLindenbaum were previously imported by IntCompleteness and MinCompleteness respectively. When those files are deleted, the StrongCompleteness files need the direct import.
