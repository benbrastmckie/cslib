# Research Report: Propagate Hybrid Five-Primitive Design to Temporal Layer

## Task 176 -- Session sess_1781317385_e83d59_176

## 1. Executive Summary

This report analyzes the changes needed to upgrade `Cslib.Logic.Temporal.Formula` from a
three-primitive inductive `{atom, bot, imp, untl, snce}` to a seven-primitive
`{atom, bot, imp, and, or, untl, snce}` design, mirroring what task 173 accomplished for
`Cslib.Logic.PL.Proposition`.

Currently, `and` and `or` are `abbrev` definitions encoding through `imp`/`bot`:
- `and phi psi := imp (imp phi (imp psi bot)) bot`  (i.e., `neg (phi -> neg psi)`)
- `or phi psi := imp (imp phi bot) psi`  (i.e., `neg phi -> psi`)

Making them primitive constructors requires touching **37 files** across the Temporal layer
(the entire directory). However, the magnitude of changes per file varies dramatically: some
files need only trivial case additions, while the Chronicle metalogic files (12,500+ lines
total) require careful case-by-case analysis.

## 2. Current Formula Type

```lean
-- Cslib/Logics/Temporal/Syntax/Formula.lean (lines 46-57)
inductive Formula (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (phi1 phi2 : Formula Atom)
  | untl (phi1 phi2 : Formula Atom)
  | snce (phi1 phi2 : Formula Atom)
deriving DecidableEq, BEq
```

After the change:
```lean
inductive Formula (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (phi1 phi2 : Formula Atom)
  | and (phi1 phi2 : Formula Atom)   -- NEW
  | or (phi1 phi2 : Formula Atom)    -- NEW
  | untl (phi1 phi2 : Formula Atom)
  | snce (phi1 phi2 : Formula Atom)
deriving DecidableEq, BEq
```

The derived `neg`, `top`, `iff`, `someFuture`, `allFuture`, `somePast`, `allPast` remain
as `abbrev` definitions -- they are valid in this primitive set.

## 3. Reference Pattern: Propositional (Task 173)

Task 173 upgraded `PL.Proposition` from `{atom, bot, imp}` to `{atom, bot, imp, and, or}`.
The current `PL.Proposition` at `Cslib/Logics/Propositional/Defs.lean` lines 54-65:

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | bot
  | imp (a b : Proposition Atom)
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
deriving DecidableEq, BEq
```

Key pattern from task 173:
- `neg` and `top` remained as derived `abbrev`s (not promoted to constructors)
- `iff` remained derived via `(A -> B) and (B -> A)`
- `HasAnd` and `HasOr` typeclass instances were registered
- The proof system gained axioms for `and`/`or` introduction and elimination

## 4. File-by-File Change Scope

### 4.1 Syntax Layer (4 files)

| File | Lines | Change Type | Estimated Effort |
|------|-------|-------------|-----------------|
| `Syntax/Formula.lean` | 583 | HEAVY: Add constructors, update all pattern matches (encodeNat, complexity, temporalDepth, countImplications, swapTemporal, needsPositiveHypotheses, atoms, beq_refl, eq_of_beq), update notation instances, add BEq helpers | High |
| `Syntax/Context.lean` | 132 | NONE: No pattern matching on Formula | None |
| `Syntax/BigConj.lean` | 53 | LIGHT: Uses `Formula.and` as abbrev; after promotion to constructor, `bigconj` still calls `.and` -- may work without changes. Verify. | Low |
| `Syntax/Subformulas.lean` | 219 | MEDIUM: Add `and`/`or` cases to `subformulas`, `subformulaCount`, and membership lemmas (`subformulas_trans` + all constructor lemmas) | Medium |

**Detail on Formula.lean changes:**

1. **`encodeNat`**: Add cases for `.and` (pair 5) and `.or` (pair 6). Update `encodeNat_injective` with new discrimination cases (each existing case needs 2 new absurd arms for and/or, plus 2 new primary cases).

2. **`complexity`**: Add `| .and phi psi => 1 + complexity phi + complexity psi` and `| .or phi psi => 1 + complexity phi + complexity psi`. Must be positioned AFTER the derived-pattern cases (G, H, R, T which match through imp).

3. **`temporalDepth`**: Add `| .and phi psi => max phi.temporalDepth psi.temporalDepth` and `| .or phi psi => max phi.temporalDepth psi.temporalDepth`.

4. **`countImplications`**: Add and/or cases (both return sum of children, no +1).

5. **`swapTemporal`**: Add `| .and phi psi => .and (swapTemporal phi) (swapTemporal psi)` and `| .or phi psi => .or (swapTemporal phi) (swapTemporal psi)`.

6. **`needsPositiveHypotheses`**: Add `| .and _ _ => true` and `| .or _ _ => true` plus simp lemmas.

7. **`atoms`**: Add `| .and phi psi => atoms phi U atoms psi` and `| .or phi psi => atoms phi U atoms psi`.

8. **`beq_refl`/`eq_of_beq`**: Add and/or cases mirroring imp/untl/snce pattern.

9. **`swapTemporal_involution`**: Add `| and _ _ ih1 ih2 => ...` and `| or _ _ ih1 ih2 => ...` cases.

10. **`atoms_swapTemporal`**: Add cases.

11. **Notation and instances**: Add `instance : HasAnd (Formula Atom) where and := .and` and `instance : HasOr (Formula Atom) where or := .or`. Update `TemporalConnectives` instance if it extends `HasAnd`/`HasOr`.

12. **`Formula.and`/`Formula.or`**: Change from `abbrev` to removed (or kept as deprecated aliases). The constructor `.and` replaces the abbrev. Notation `" ∧ "` and `" ∨ "` remain.

### 4.2 Semantics Layer (3 files)

| File | Lines | Change Type | Estimated Effort |
|------|-------|-------------|-----------------|
| `Semantics/Model.lean` | 61 | NONE: No Formula pattern matching | None |
| `Semantics/Satisfies.lean` | 178 | MEDIUM: Add `and`/`or` clauses to `Satisfies`, add simp lemmas `and_iff`, `or_iff`. Existing `sat_and_iff`/`sat_or_iff` in Soundness.lean move here or become trivial. | Medium |
| `Semantics/Validity.lean` | 199 | NONE: No Formula pattern matching | None |

**Detail on Satisfies.lean:**

Add two new cases to the `Satisfies` definition:
```lean
| .and phi psi => Satisfies M t phi /\ Satisfies M t psi
| .or phi psi => Satisfies M t phi \/ Satisfies M t psi
```

Add simp lemmas:
```lean
@[simp] theorem and_iff ... : Satisfies M t (.and phi psi) <-> (Satisfies M t phi /\ Satisfies M t psi)
@[simp] theorem or_iff ... : Satisfies M t (.or phi psi) <-> (Satisfies M t phi \/ Satisfies M t psi)
```

### 4.3 ProofSystem Layer (4 files)

| File | Lines | Change Type | Estimated Effort |
|------|-------|-------------|-----------------|
| `ProofSystem/Axioms.lean` | 236 | MEDIUM: Add and/or axioms (and_intro, and_elim_left, and_elim_right, or_intro_left, or_intro_right, or_elim). Update axiom count in docstring. | Medium |
| `ProofSystem/Derivation.lean` | 99 | NONE: Generic over axioms, no Formula pattern matching | None |
| `ProofSystem/Derivable.lean` | 100 | NONE: Generic wrapper, no Formula pattern matching | None |
| `ProofSystem/Instances.lean` | 214 | MEDIUM: Register HasAxiom instances for new and/or axioms. Update TemporalBXHilbert bundle. | Medium |

**New axioms needed (6):**

```lean
| and_intro (phi psi : Formula Atom) :
    Axiom (phi.imp (psi.imp (Formula.and phi psi)))
| and_elim_left (phi psi : Formula Atom) :
    Axiom ((Formula.and phi psi).imp phi)
| and_elim_right (phi psi : Formula Atom) :
    Axiom ((Formula.and phi psi).imp psi)
| or_intro_left (phi psi : Formula Atom) :
    Axiom (phi.imp (Formula.or phi psi))
| or_intro_right (phi psi : Formula Atom) :
    Axiom (psi.imp (Formula.or phi psi))
| or_elim (phi psi chi : Formula Atom) :
    Axiom ((phi.imp chi).imp ((psi.imp chi).imp ((Formula.or phi psi).imp chi)))
```

All with `minFrameClass = .Base`.

### 4.4 Metalogic Layer (21 files, ~12,500 lines)

| File | Lines | Change Type | Estimated Effort |
|------|-------|-------------|-----------------|
| `Metalogic/DerivationTree.lean` | 134 | NONE: height function dispatches on DerivationTree constructors (not Formula) | None |
| `Metalogic/DeductionTheorem.lean` | 175 | NONE: Dispatches on DerivationTree constructors only | None |
| `Metalogic/MCS.lean` | 483 | LOW: MCS lemmas are formula-generic; no Formula pattern matching. However, `and`/`or` membership lemmas might be useful additions. | Low |
| `Metalogic/DenseMCS.lean` | 400 | NONE: FC-parameterized MCS; no Formula pattern matching | None |
| `Metalogic/Soundness.lean` | 421 | MEDIUM: `axiom_sound` needs cases for new axioms (6). `swapTemporal_dual` needs and/or cases. `sat_and_iff`/`sat_or_iff` become trivial (can be removed or kept as wrappers). `soundness` dispatches on DerivationTree (no change). | Medium |
| `Metalogic/DenseSoundness.lean` | 183 | LOW: `axiom_sound_dense` calls `axiom_sound`; needs and/or cases (trivial since all new axioms are Base). | Low |
| `Metalogic/Completeness.lean` | 129 | NONE: Uses MCS generically | None |
| `Metalogic/DenseCompleteness.lean` | 268 | NONE: Uses chronicle construction generically | None |
| `Metalogic/PropositionalHelpers.lean` | 117 | NONE: Delegates to Foundations | None |
| `Metalogic/GeneralizedNecessitation.lean` | 157 | NONE: No Formula pattern matching | None |
| `Metalogic/TemporalContent.lean` | 220 | NONE: Uses derived operators (G, H, F, P); no direct Formula matching | None |
| `Metalogic/WitnessSeed.lean` | 252 | NONE: Uses Formula.and/or as terms but does not pattern-match | None |
| `Metalogic/CompletenessHelpers.lean` | 310 | NONE: Uses Formula.and/or as terms but does not pattern-match | None |
| `Chronicle/ChronicleTypes.lean` | 323 | NONE: Type definitions; no Formula matching | None |
| `Chronicle/CanonicalChain.lean` | 76 | NONE: Chain construction; no Formula matching | None |
| `Chronicle/Frame.lean` | 248 | NONE: Frame properties; no Formula matching | None |
| `Chronicle/RRelation.lean` | 710 | NONE*: Uses `Formula.and`/`Formula.or` as terms (not pattern matching). After promotion to constructors, these become constructor calls -- which is exactly what we want. No changes needed. | None |
| `Chronicle/OrderedSeedConsistency.lean` | 135 | NONE*: Same as above | None |
| `Chronicle/PointInsertion.lean` | 2717 | NONE*: Same as above | None |
| `Chronicle/CounterexampleElimination.lean` | 3234 | NONE*: Same as above | None |
| `Chronicle/ChronicleToCountermodel.lean` | 138 | NONE: Model construction; no Formula matching | None |
| `Chronicle/TruthLemma.lean` | 232 | MEDIUM: `chronicle_truth_lemma` has structural induction on Formula with 5 cases; needs 2 new cases (and, or). Requires new helper lemmas `truth_lemma_and` and `truth_lemma_or`. | Medium |

**Critical observation about Chronicle files (RRelation, PointInsertion, CounterexampleElimination):**

These files contain ~6,800 lines total and use `Formula.and`/`Formula.or` extensively.
However, they use them as **term constructors** (building formulas), not as **pattern matches**
(destructing formulas). When `and`/`or` become primitive constructors instead of abbrevs, all
these call sites continue to work because `Formula.and phi psi` becomes the constructor `.and phi psi`
instead of expanding to `.imp (.imp phi (.imp psi .bot)) .bot`. The existing code will typecheck
correctly because:

1. Axiom references like `Axiom.enrichment_until` still take `Formula.and` terms -- the axiom
   inductive's type signatures use `Formula.and` which will resolve to the constructor.
2. MCS membership proofs (`temporal_implication_property`, `mcs_mp_axiom`) are formula-generic.
3. The only structural induction on Formula in the entire Chronicle directory is in `TruthLemma.lean`.

**However**, there is a subtle semantic shift: when `and`/`or` were abbrevs expanding to `imp`/`bot`
combinations, the axioms like `enrichment_until` that mention `Formula.and` in their conclusion
were actually axioms about specific `imp`/`bot` patterns. After promotion, they become axioms
about the new `and` constructor. This is semantically correct (the axioms state the same
logical truth) but the **old proofs using these axioms may need adjustment** if they relied
on definitional unfolding of `Formula.and` to `imp`/`bot`. This requires careful verification.

### 4.5 FromPropositional.lean (1 file)

| File | Lines | Change Type | Estimated Effort |
|------|-------|-------------|-----------------|
| `FromPropositional.lean` | 75 | MEDIUM: Update `toTemporal` to map `PL.Proposition.and` to `Temporal.Formula.and` (homomorphic, replacing Lukasiewicz encoding). Update simp lemmas. | Medium |

Currently `toTemporal` encodes:
```lean
| .and phi1 phi2 => .imp (.imp phi1.toTemporal (.imp phi2.toTemporal .bot)) .bot
| .or phi1 phi2 => .imp (.imp phi1.toTemporal .bot) phi2.toTemporal
```

After change:
```lean
| .and phi1 phi2 => .and phi1.toTemporal phi2.toTemporal
| .or phi1 phi2 => .or phi1.toTemporal phi2.toTemporal
```

## 5. Key Design Decisions

### 5.1 Derived Connectives That Stay Derived

The following remain `abbrev` (not promoted):
- `neg phi := imp phi bot` -- valid in minimal logic
- `top := imp bot bot` -- valid in minimal logic
- `iff phi psi := and (imp phi psi) (imp psi phi)` -- uses primitive `and` now
- `someFuture phi := untl phi top`
- `allFuture phi := neg (someFuture (neg phi))`
- `somePast phi := snce phi top`
- `allPast phi := neg (somePast (neg phi))`

### 5.2 Complexity Function Ordering

The `complexity` function uses deep pattern matching for derived temporal operators (G, H, R, T,
F, P, next, prev). These patterns match through `imp`/`untl`/`snce` combinations. Adding `and`/`or`
constructors does NOT interfere because `and`/`or` were previously abbrevs expanding to `imp`/`bot`.
After promotion, formulas built with `and`/`or` will no longer match the old imp/bot patterns
(which is correct -- they should match generic and/or cases instead).

The `complexity` function needs new generic cases:
```lean
| .and phi psi => 1 + complexity phi + complexity psi
| .or phi psi => 1 + complexity phi + complexity psi
```

These should be placed after the derived-pattern cases and before (or among) the generic binary cases.

### 5.3 Axiom Set Changes

The BX temporal axioms extensively use `Formula.and` and `Formula.or` in their conclusions
(e.g., `enrichment_until`, `self_accum_until`, `linear_until`). After promotion:

- These axiom constructors now produce formulas with primitive `and`/`or` constructors
  instead of `imp`/`bot` encodings.
- The **axiom soundness proofs** in `Soundness.lean` currently use `sat_and_iff`/`sat_or_iff`
  to bridge between the satisfaction of `imp`/`bot` encodings and logical `And`/`Or`. After
  promotion, `Satisfies` will have direct `and`/`or` cases, making these bridges trivial
  (or unnecessary).
- The new and/or axioms (6 total) are standard and sound over all linear orders.

### 5.4 TruthLemma Extension

The truth lemma (`chronicle_truth_lemma` in `TruthLemma.lean`) performs structural induction
on Formula with 5 cases. Two new cases are needed:

**And case**: Forward: `phi in f(t)` and `psi in f(t)` iff `and phi psi in f(t)` (MCS and-property).
Backward: by MCS properties (conjunction in MCS iff both conjuncts in MCS -- derivable from
new axioms + MCS closed-under-derivation).

**Or case**: Forward: `or phi psi in f(t)` iff `phi in f(t)` or `psi in f(t)` (MCS or-property).
Backward: by MCS properties + new or-axioms.

The key helper lemmas needed:
```lean
-- MCS conjunction property: (phi and psi) in M iff phi in M and psi in M
theorem mcs_and_iff (h_mcs : SetMaximalConsistent M) :
    Formula.and phi psi in M <-> phi in M /\ psi in M

-- MCS disjunction property: (phi or psi) in M iff phi in M or psi in M
theorem mcs_or_iff (h_mcs : SetMaximalConsistent M) :
    Formula.or phi psi in M <-> phi in M \/ psi in M
```

These follow from the new axioms (and_intro, and_elim_left, and_elim_right, or_intro_left,
or_intro_right, or_elim) + MCS closed-under-derivation.

## 6. PR #642 Coordination

PR #642 (task 170, branch `pr3/temporal-syntax`) was submitted and appears to have been
merged into main based on the commit history (`727b7a42 task 170: complete implementation -
submit PR #642 temporal syntax`). The current `main` branch has the 5-primitive formula type
that task 170 established. No coordination issues -- task 176 builds on top of the merged PR.

## 7. Estimated Impact and Phasing

### File Change Summary

| Category | Files Needing Changes | Files No Changes | Total Lines Changed (est.) |
|----------|----------------------|------------------|---------------------------|
| Syntax | 3 | 1 | ~300 |
| Semantics | 1 | 2 | ~40 |
| ProofSystem | 2 | 2 | ~100 |
| Metalogic (non-Chronicle) | 2 (Soundness, DenseSoundness) | 11 | ~100 |
| Metalogic (Chronicle) | 1 (TruthLemma) | 9 | ~80 |
| Top-level | 1 (FromPropositional) | 0 | ~20 |
| **Total** | **10** | **25** | **~640** |

### Recommended Phase Structure

**Phase 1: Syntax Foundation** (~300 lines)
- `Formula.lean`: Add constructors, update all structural functions, update typeclass instances
- `Subformulas.lean`: Add cases for and/or
- `BigConj.lean`: Verify no changes needed (or minor fixes)

**Phase 2: Semantics + ProofSystem** (~140 lines)
- `Satisfies.lean`: Add and/or cases, simp lemmas
- `Axioms.lean`: Add 6 new axiom constructors
- `Instances.lean`: Register HasAxiom instances

**Phase 3: Soundness** (~100 lines)
- `Soundness.lean`: Add axiom soundness proofs, update `swapTemporal_dual`, simplify `sat_and_iff`/`sat_or_iff`
- `DenseSoundness.lean`: Propagate new axiom cases

**Phase 4: TruthLemma + MCS Helpers** (~80 lines)
- Add `mcs_and_iff`/`mcs_or_iff` to `MCS.lean`
- `TruthLemma.lean`: Add and/or induction cases

**Phase 5: FromPropositional + CI** (~20 lines)
- `FromPropositional.lean`: Switch to homomorphic embedding
- Run full CI verification pipeline

## 8. Risk Assessment

### Low Risk
- Syntax changes (mechanical, well-understood pattern)
- Semantics changes (direct satisfaction clauses)
- New axiom soundness (standard propositional axioms)
- FromPropositional (simplification, not complexification)

### Medium Risk
- **Existing axiom proofs in Soundness.lean**: Many axiom soundness proofs use `sat_and_iff`/
  `sat_or_iff` which bridge `imp`/`bot` encodings to `And`/`Or`. After promotion, these become
  trivial `Iff.rfl`, but the proof structure may need to change.
- **Chronicle files and definitional equality**: Code that built `Formula.and` terms previously
  got `imp`/`bot` terms after unfolding. After promotion, they get genuine `and` constructors.
  If any proof relied on definitional equality with the `imp`/`bot` expansion (e.g., pattern
  matching on the expanded form), it would break. **Searched for this pattern -- found none**
  in the Chronicle files. They all use `Formula.and`/`Formula.or` by name.

### High Risk
- **`encodeNat_injective`**: This proof has ~100 lines of case-by-case discrimination. Adding
  2 new constructors means 7 constructors total, requiring 7x7 = 49 case pairs instead of
  5x5 = 25. This is the single most labor-intensive proof to update (~150 new lines).

## 9. Blockers

None identified. All prerequisites are met:
- Task 173 (Propositional five-primitive) is complete and merged
- PR #642 (Temporal syntax) is merged
- Foundations connective typeclasses (`HasAnd`, `HasOr`) already exist
- No circular dependencies in the change path

## 10. Tactic Survey

For the new proofs needed:

| Proof Area | Recommended Tactics |
|-----------|-------------------|
| `encodeNat_injective` new cases | `injection h` + `decide` (existing pattern) |
| Axiom soundness (and/or) | Direct `intro`/`constructor`/`exact` (simple propositional) |
| `swapTemporal_involution` new cases | `simp only [swapTemporal, ih1, ih2]` (existing pattern) |
| TruthLemma and/or cases | `constructor` + MCS property lemmas |
| MCS and/or properties | `temporal_closed_under_derivation` + new axiom trees |
