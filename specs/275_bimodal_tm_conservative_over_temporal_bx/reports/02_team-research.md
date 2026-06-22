# Research Report: Task #275

**Task**: 275 - bimodal_tm_conservative_over_temporal_bx
**Date**: 2026-06-22
**Mode**: Team Research (4 teammates)
**Session**: sess_1782164778_60175c

## Summary

This team research investigated the blocking `sorry` in `temporal_valid_of_bimodal_derivable`
(line 263 of `TemporalConservativity.lean`). All four teammates confirm the domain mismatch
is a **genuine mathematical obstacle**: bimodal soundness requires `AddCommGroup D` while
temporal completeness quantifies over all serial linear orders. The `ChronicleSubtype`
(countermodel domain from completeness proof) inherits `LinearOrder` from `ℚ` but NOT
`AddCommGroup` (not a subgroup). Order embeddings do not preserve temporal satisfaction
(new witnesses in `untl`/`snce` quantifiers). The team identified two viable resolution
paths: (1) **semantic via order isomorphism + dense/discrete case split** following the
existing `ChronicleToCountermodelBasic.lean` pattern, and (2) **syntactic derivation
translation** avoiding domain constraints entirely.

## Key Findings

### 1. The Sorry is Well-Localized and the Only Blocker

The existing file has three sorry-free proofs:
- `temporalTaskFrame` + `temporalWorldHistory` + `temporalTaskModel` (constructions)
- `bimodal_truthAt_toBimodal_iff_temporal_satisfies` (semantic bridge, lines 149-183)
- `temporal_valid_on_addcommgroup` (validity on AddCommGroup domains, lines 196-206)

The single `sorry` is in `temporal_valid_of_bimodal_derivable` (line 263). This is the
**only remaining sorry in the entire conservativity program** (tasks 272-276). Resolving
it unblocks full `Cslib.lean` build and completes the program.

### 2. Why Standard Approaches Fail

| Approach | Why it Fails |
|----------|-------------|
| `AddCommGroup` on `ChronicleSubtype` | Not a subgroup of `ℚ` — `limitDom` not closed under `+` or `-` |
| Order embedding `ChronicleSubtype ↪o ℚ` | Introduces new witnesses in `untl`/`snce` quantifiers |
| Extending model from `ChronicleSubtype` to `ℚ` | Extended model has different quantifier ranges, breaks truth preservation |
| `Order.iso_of_countable_dense` | Requires `DenselyOrdered` on `ChronicleSubtype` — unknown for Base BX |
| `orderIsoIntOfLinearSuccPredArch` to `ℤ` | Requires `SuccOrder`, `PredOrder`, `IsSuccArchimedean` — not available |
| Hardcoding `D = ℤ` (as ModalConservativity does) | Temporal model's domain IS the time domain; cannot separate them |

### 3. `Satisfies_orderIso` is Provable and Foundational

All four teammates agree: `Temporal.Satisfies` is defined purely in terms of `<` on
the domain, so an order isomorphism `e : D₁ ≃o D₂` preserves satisfaction:

```lean
theorem Satisfies_orderIso (e : D₁ ≃o D₂) (M : TemporalModel D₁ Atom) (t : D₁)
    (φ : Temporal.Formula Atom) :
    Satisfies M t φ ↔ Satisfies (M.transport e) (e t) φ
```

This is provable by structural induction on `φ` (~20-30 lines). The `untl`/`snce` cases
use that `e` is a bijection preserving strict order: witnesses correspond bijectively,
and the guard quantifier over intermediate points is preserved since `e` maps open
intervals onto open intervals. This lemma does not exist in CSLib and should be added
to `Temporal/Semantics/`.

### 4. The Dense/Discrete Case Split Pattern Exists

`ChronicleToCountermodelBasic.lean` (bimodal) implements a dense/discrete case split:
- **Dense case**: Uses `cantorIsoDense` (Cantor's theorem) to get `ChronicleSubtype ≃o ℚ`
- **Discrete case**: Uses `orderIsoIntOfLinearSuccPredArch` to get `ChronicleSubtype ≃o ℤ`

Both `ℚ` and `ℤ` have `AddCommGroup`. If the temporal `ChronicleSubtype` can be shown
to fall into one of these two categories, `Satisfies_orderIso` + the isomorphism +
`temporal_valid_on_addcommgroup` closes the sorry.

**Critical unknown**: Whether the base BX `ChronicleSubtype` is densely ordered.
- The existence of `DenseCompleteness.lean` as a separate file suggests base BX
  countermodels may NOT always be dense.
- The omega-chain construction inserts C4/C5 witnesses but may not insert midpoints
  between all pairs.
- The Dense BX completeness proof uses the "dense indicator" formula `¬(⊥ U ⊤)` to
  guarantee density; base BX does not.
- However, the bimodal `ChronicleToCountermodelBasic.lean` handles this case split
  for the bimodal analogue — the temporal version should follow the same pattern.

### 5. The Syntactic Approach is an Independent Alternative

The syntactic derivation translation would bypass domain constraints entirely:
1. Prove `φ.toBimodal` is always box-free (induction on `Temporal.Formula`)
2. Prove modal axioms always produce box-containing conclusions (by inspection)
3. Prove `necessitation` rule produces `Formula.box` (definitional)
4. By induction on derivation tree height: any TM-derivation of a box-free formula
   uses only BX-compatible rules and can be projected to a BX-derivation

**Obstacle**: The derivation tree may use `necessitation` and modal axioms for
INTERMEDIATE steps even when the conclusion is box-free. Eliminating these requires
showing that box-free conclusions cannot depend on modal detours — essentially a
cut-elimination or admissibility result. This is non-trivial proof-theoretically.

## Synthesis

### Conflicts Resolved

| Conflict | Teammate A/D | Teammate C | Resolution |
|----------|-------------|------------|------------|
| Primary approach | Semantic (order iso + case split) | Syntactic (derivation translation) | **Semantic first**: follows existing codebase pattern (`ChronicleToCountermodelBasic.lean`), creates reusable infrastructure (`Satisfies_orderIso`). Syntactic is fallback if density/discreteness cannot be established. |
| Density of ChronicleSubtype | A: NO (base BX lacks density); D: MAYBE YES (omega-chain inserts points) | Not investigated | **Needs investigation**: read `PointInsertion.lean` and `ChronicleConstruction.lean` to determine whether base BX chronicle is dense, discrete, or mixed. |
| Feasibility of resolution | A: sorry may be permanent | B, D: solvable via iso transfer | **Solvable**: the bimodal version handles this exact pattern; the temporal version should follow it. The key is whether `ChronicleSubtype` admits the same dense/discrete case split. |

### Gaps Identified

1. **ChronicleSubtype density status**: Must be determined before choosing between
   Cantor iso (dense → ℚ) and Z-iso (discrete → ℤ). Check `PointInsertion.lean`.

2. **No `Satisfies_orderIso` in CSLib**: Must be proved. Straightforward but doesn't
   exist yet.

3. **Bimodal `ChronicleToCountermodelBasic.lean` pattern not studied for temporal**:
   The bimodal version handles the case split; the temporal version should replicate it.

4. **Lint issues**: `[DecidableEq Atom]` is unused in type signatures of both
   `temporal_valid_of_bimodal_derivable` and `bimodal_conservative_over_temporal`.
   Line 250 exceeds 100 characters.

### Recommendations

**Primary path (semantic, ~2-4 hours)**:
1. Prove `Satisfies_orderIso` in `Temporal/Semantics/` (~20-30 lines)
2. Study `ChronicleToCountermodelBasic.lean` to understand the dense/discrete case split
3. Replicate the pattern for temporal `ChronicleSubtype`:
   - Prove `Countable (ChronicleSubtype A h_mcs)` (subtype of ℚ)
   - Case split on `DenselyOrdered`:
     - Dense: `Order.iso_of_countable_dense` → `ChronicleSubtype ≃o ℚ`
     - Discrete: `orderIsoIntOfLinearSuccPredArch` → `ChronicleSubtype ≃o ℤ`
   - Use `Satisfies_orderIso` + iso + `temporal_valid_on_addcommgroup` on ℚ or ℤ
4. Restructure `temporal_valid_of_bimodal_derivable` to use contrapositive:
   - If `φ` not BX-derivable → ChronicleSubtype countermodel exists
   - Transfer via iso to ℚ or ℤ → `temporal_valid_on_addcommgroup` gives contradiction
5. Fix lint issues (`[DecidableEq Atom]` removal, line length)

**Fallback path (syntactic, ~4-6 hours)**:
1. Define `boxFree : Bimodal.Formula Atom → Prop` (or use `toBimodal` image characterization)
2. Prove `toBimodal` always produces box-free formulas
3. Prove modal axioms produce box-containing formulas
4. Prove by induction on derivation: box-free conclusions use only BX rules
5. Construct BX derivation tree from projected TM derivation tree
6. Completely avoids domain constraints

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Insight |
|----------|-------|--------|------------|-------------|
| A | Completeness internals / contrapositive | completed | high | ChronicleSubtype lacks AddCommGroup; Cantor iso requires density; density fails for base BX |
| B | Alternative approaches / model transfer | completed | high | `satisfies_orderIso` is the core mechanism; `ChronicleToCountermodelBasic.lean` is the template |
| C | Critic / gap analysis | completed | high | Syntactic approach avoids domain constraints; modal axioms produce box-containing conclusions |
| D | Strategic horizons / roadmap alignment | completed | medium-high | Only sorry in conservativity program; resolving unblocks full Cslib.lean build; `Satisfies_orderIso` broadly reusable |

## References

### Codebase Files (Examined)
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` — partial impl with sorry
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean` — sidesteps via D=ℤ
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean` — CPL bridge pattern
- `Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean` — requires AddCommGroup D
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean` — builds countermodel on ChronicleSubtype
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` — Dense-BX variant with density
- `Cslib/Logics/Temporal/Semantics/Satisfies.lean` — Satisfies definition (uses only <)
- `Cslib/Logics/Temporal/Semantics/Model.lean` — TemporalModel definition
- `Cslib/Logics/Bimodal/Semantics/Truth.lean` — truthAt definition, Set.univ_shift_closed

### Mathlib Theorems (Relevant)
- `Order.iso_of_countable_dense` — Cantor's theorem for countable dense linear orders
- `Order.embedding_from_countable_to_dense` — order embedding from countable to dense
- `orderIsoIntOfLinearSuccPredArch` — iso to ℤ for discrete orders
