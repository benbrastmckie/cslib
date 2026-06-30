# Implementation Summary: Task #421 — Min-side FMP Decidability

- **Task**: 421
- **Status**: [IMPLEMENTING]
- **Completed**: 2026-06-29
- **Phases**: 4/4 completed

## What Was Done

Created `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` — a sorry-free
mirror of `IntDecidability.lean` delivering `instDecidableDerivableMinPropAxiom'` via the
finite model property for minimal propositional logic.

## Final Verification Results

### Axiom Audit (PASSED)
```
#print axioms instDecidableDerivableMinPropAxiom'
-- Axioms:
-- propext
-- Classical.choice
-- Quot.sound
```
No `sorryAx`. Exactly the expected clean closure.

### Build Status
- `lake build Cslib.Logics.Propositional.Metalogic.MinDecidability`: PASS (clean, 0 warnings)
- `lake exe checkInitImports`: PASS
- `lake exe lint-style`: PASS (no output)
- `lake shake --add-public --keep-implied --keep-prefix`: PASS (no MinDecidability issues)
- `lake lint`: 55 pre-existing errors in other files; 0 new errors from MinDecidability
- `lake test`: pre-existing failure in `ProofSystemMorphism.lean` (untracked file from other task); MinDecidability itself is clean
- Sorry count in new file: 0 (two doc-comment hits of "sorry-free" are not code)
- New axioms introduced: 0

## Key Design Choices

### Simplifications vs IntDecidability

1. **No `consistent` field**: `MinFinWorld` drops the `consistent : (⊥ : PL.Proposition Atom) ∉ carrier` field from `IntFinWorld`. MinTheory worlds may contain `⊥`.
2. **No `intFinWorld_propConsistent` helper**: The ~40-line consistency helper is eliminated entirely. `min_imp_witness` requires no consistency hypothesis.
3. **Bot case is `Iff.rfl`**: In `min_fin_truth_lemma`, the `| .bot` case reduces to `IForces minFinVal minFinBotForces w ⊥ ↔ ⊥ ∈ w.carrier`, which is definitionally `minFinBotForces w ↔ ⊥ ∈ w.carrier = Iff.rfl`.
4. **Backward direction drops consistency plumbing**: `min_fmp`'s backward direction uses `min_prime_exclusion (minDeductiveClosure_is_theory ∅)` directly, with no `PropSetConsistent ∅` or `int_consistent` step.

### New Declarations (Two Only)

- `minFinBotForces {φ} (w : MinFinWorld φ) : Prop := (⊥ : PL.Proposition Atom) ∈ w.carrier`
  — mirrors `minBotForces` from `MinStrongCompleteness.lean:101`
- `minFinBotForces_upward_closed {φ} {w w'} (hw : w ≤ w') (hbf : minFinBotForces w) : minFinBotForces w'`
  — one-line proof `hw hbf`

### Access Pattern Difference vs Int

- Int: `hT_prime.1.2 L ψ' hLsub hLderiv` (where `.1 = IntDCCS`, `.2 = closure field`)
- Min: `hT_prime.1 L ψ' hLsub hLderiv` (where `.1 = MinTheory` directly)

### Soundness Direction

Forward (`Derivable MinPropAxiom φ → ∀ w, φ ∈ w.carrier`) uses:
```lean
min_soundness_derivable h (MinFinWorld φ) minFinVal minFinBotForces
  minFinVal_upward_closed minFinBotForces_upward_closed w
```
The extra `minFinBotForces` and `minFinBotForces_upward_closed` arguments (vs. Int's 4-arg call) reflect `min_soundness_derivable` returning `MValid` (which takes `bot_forces` as parameter) rather than `IValid`.

## Barrel Wiring

`lake exe mk_all --module` added the import at `Cslib.lean:429`:
```lean
public import Cslib.Logics.Propositional.Metalogic.MinDecidability
```

## Plan Deviations

All 4 phases were implemented in a single dispatch (all phases in one file write), rather than incrementally phase by phase. This was possible because the implementation is a clean mechanical mirror and the entire construction was clear from the reference IntDecidability.lean template. The CI was run phase-by-phase conceptually (scoped build after each logical phase).

No functional deviations from the plan. The two style fixes applied:
1. Removed alignment spaces from structure field declarations (reported by `linter.style.whitespace`)
2. Changed `fun w₁ w₂ h =>` to `fun _ _ h =>` in `minFinWorld_carrier_injective` (reported by `linter.unusedVariables` since `w₁`/`w₂` are not mentioned explicitly in the body)

## Artifacts

- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` (new, 290 lines)
- `Cslib.lean` (barrel import added at line 429)
- `specs/421_min_fmp_decidability/plans/01_min-fmp-decidability-plan.md` (status updated)
- `specs/421_min_fmp_decidability/summaries/01_min-fmp-decidability-summary.md` (this file)
