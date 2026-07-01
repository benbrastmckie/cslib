# Research Report: Task #275

**Task**: Bimodal TM conservative over Temporal BX
**Date**: 2026-06-22
**Mode**: Team Research (4 teammates)

## Summary

The conservativity result (TM conservative over BX for temporal formulas) is mathematically correct — all four teammates confirm this independently. The sorry in `temporal_valid_of_bimodal_derivable` (TemporalConservativity.lean:263) represents an infrastructure gap, not a mathematical error. The gap is precisely: bridging from validity on `AddCommGroup` serial linear orders (already proven via `temporal_valid_on_addcommgroup`) to validity on ALL serial linear orders (required by temporal BX completeness).

The correct approach is **semantic transfer via order isomorphism**: prove `satisfies_orderIso` (temporal satisfaction preserved by order isomorphisms), then use Cantor's theorem (`Order.iso_of_countable_dense`) to isomorphize the `ChronicleSubtype` countermodel domain to `ℚ`, which has `AddCommGroup`.

The **single remaining obstacle** is proving `DenselyOrdered (ChronicleSubtype A h_base_mcs)` for base BX. The codebase comments in `ChronicleConstruction.lean` (lines 268, 830-831) assert density informally but no formal proof exists. The formal `DenselyOrdered` instance (`chronicleDenselyOrderedDense`) requires Dense-class MCS input.

## Key Findings

### 1. The sorry and what's already proven (Teammate A)

The sorry is in `temporal_valid_of_bimodal_derivable` (lines 255-263). Already proven sorry-free:
- `bimodal_truthAt_toBimodal_iff_temporal_satisfies` — structural induction proving bimodal truthAt equals temporal Satisfies in the temporal task model
- `temporal_valid_on_addcommgroup` — if `φ.toBimodal` is TM-derivable, then `φ` is satisfied in every temporal model on any `AddCommGroup` serial linear order

The gap: extending from AddCommGroup domains to ALL serial linear orders.

### 2. Ruled-out approaches (Teammate B, confirmed by all)

| Approach | Verdict | Reason |
|----------|---------|--------|
| Syntactic lifting (`liftDerivationQfree`) | BLOCKED | Operates within bimodal language only; cross-language translation requires cut-elimination which IS the conservativity theorem |
| S5 Kripke adapter (task 274 pattern) | NOT APPLICABLE | Addresses a different problem (Omega/accessibility); temporal proof already has correct model construction |
| Algebraic (Lindenbaum) | NO SHORTCUT | Reduces to the same semantic/syntactic gap |
| Direct `AddCommGroup` on `ChronicleSubtype` | FALSE | `limitDom` is not closed under addition; subtypes of ℚ are not automatically subgroups |
| Order embeddings (not isomorphisms) | INSUFFICIENT | Until/Since quantifiers range over full target domain, introducing spurious witnesses |

### 3. The correct approach: order isomorphism via Cantor's theorem (All teammates)

**Step 1**: Prove `satisfies_orderIso` — temporal satisfaction preserved by order isomorphisms. This is a 5-case structural induction (~25 lines). The `untl`/`snce` cases use `OrderIso.lt_iff_lt` and bijectivity. Straightforward, HIGH confidence.

**Step 2**: In the contrapositive of `bimodal_conservative_over_temporal`:
- Assume `φ` is not BX-derivable → build MCS `A` containing `¬φ` → construct `ChronicleSubtype` countermodel
- `ChronicleSubtype` is countable (subtype of ℚ), has `NoMaxOrder`, `NoMinOrder`, `Nontrivial`
- If `DenselyOrdered`: apply `Order.iso_of_countable_dense` to get `ChronicleSubtype ≃o ℚ`
- Transfer countermodel to ℚ via `satisfies_orderIso`
- Apply `temporal_valid_on_addcommgroup` at `D = ℚ` → contradiction

### 4. The critical obstacle: base BX density (Teammate C, key finding)

The Critic identified that the prior team's "dense/discrete case split" recommendation has a significant subtlety for temporal BX:

- **Dense path**: Requires `DenselyOrdered (ChronicleSubtype A h_base_mcs)` for base BX. Only proven for Dense-class MCS (via `chronicleDenselyOrderedDense` in `DenseCompleteness.lean`). No formal base BX density proof exists.
- **Discrete path**: Teammate B proposed a ℤ isomorphism when `ChronicleSubtype` is discrete. This is theoretically possible (subtypes of ℚ can be discrete, e.g. ℤ ↪ ℚ), but requires `IsSuccArchimedean` on `ChronicleSubtype`, which is unproven for the base temporal chronicle.

**Whether base BX `ChronicleSubtype` is always dense**: The C4 condition inserts midpoints between pairs `x < y` only when specific Until/Since formulas are in `limitF(x)` and `limitF(y)`. Without the dense indicator (`neg U(bot, top)`) being universally present, density is not automatic. The code comments claim density but this may reflect the author's informal reasoning rather than a proven fact.

### 5. Strategic assessment (Teammate D)

- This is the **only sorry** preventing a full `Cslib.lean` build
- The conservativity program (tasks 272-277) is otherwise complete: 14 CPL conservativity results, 24 inter-modal edges, S5 conservativity
- The sorry is well-localized (1 theorem, 3 adjacent sorry-free proofs)
- Effort is proportional to value: smallest remaining item, unblocks full build
- NOT worth weakening to Dense-only or marking as `proof_wanted`

## Synthesis

### Conflicts Resolved

| Conflict | Resolution |
|----------|------------|
| Syntactic vs semantic approach | **Semantic wins**. Teammate B (HIGH confidence) showed syntactic lifting requires cut-elimination which is circular. Teammate D's recommendation of syntactic approach is overruled by this analysis. |
| Dense/discrete case split viability | **Dense-only path is most likely sufficient**. Teammate C correctly identified the discrete path needs `IsSuccArchimedean`, which is unverified. But proving base BX density directly may be possible using seriality formulas that are in all MCSs — this needs investigation. |
| Approach from prior team research | **Partially corrected**. The prior team's dense/discrete case split was directionally correct but the discrete case for temporal ChronicleSubtype (a subtype of ℚ) requires more careful analysis than the bimodal analog. |

### Gaps Identified

1. **`DenselyOrdered (ChronicleSubtype A h_base_mcs)` for base BX** — This is THE critical missing lemma. If provable, the sorry is closeable in ~50-80 additional lines. Research needed: can C4 midpoint insertion be shown to produce density using only seriality formulas (in every MCS) rather than the dense indicator?

2. **If density is NOT provable for base BX**: A dense/discrete case split IS needed, requiring `IsSuccArchimedean` proof for the discrete case. This follows the bimodal `ChronicleToCountermodelBasic.lean` pattern but has not been verified for temporal chronicles.

### Recommendations

**Phase 1** (implementation-ready, ~25 lines): Prove `satisfies_orderIso` in `Temporal/Semantics/` or `ConservativeExtension/TemporalConservativity.lean`.

**Phase 2** (research-then-implement): Investigate whether `DenselyOrdered (ChronicleSubtype A h_base_mcs)` holds for base BX by examining the C4 construction in `PointInsertion.lean` and `ChronicleConstruction.lean`. Key question: do seriality formulas (which are in every MCS) trigger C4 for every pair `x < y`?

**Phase 3** (contingent on Phase 2 outcome):
- If density holds: apply Cantor's theorem + `satisfies_orderIso` + `temporal_valid_on_addcommgroup` to close the sorry (~50 lines)
- If density does NOT hold: implement the full dense/discrete case split following the bimodal pattern (~150-200 lines)

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary approach | completed | high |
| B | Alternative approaches | completed | high |
| C | Critic | completed | high |
| D | Strategic horizons | completed | medium-high |

## References

- Burgess (1982) "Axioms for tense logic II" — BX completeness for serial linear orders
- GHR94 (Gabbay, Hodkinson, Reynolds 1994) "Temporal Logic: Mathematical Foundations" — conservative extension in combined temporal-modal systems
- Mathlib `Order.iso_of_countable_dense` — Cantor's theorem for countable dense linear orders
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/ChronicleToCountermodelBasic.lean` — bimodal dense/discrete case split pattern
