# Implementation Summary: Conservative Extension of IPL over MPL

- **Task**: 265 - track_conservative_lean_sorry
- **Session**: sess_1782158218_753573
- **Status**: implemented
- **Date**: 2026-06-22

## Outcome

Filled the `sorry` in `Cslib.Logic.PL.ipl_conservative_over_mpl` (Conservative.lean:99) with a
complete, axiom-clean proof. The theorem states that IPL is a conservative extension of MPL for
bot-free formulas: any bot-free formula derivable in IPL is already derivable in MPL.

## Proof Strategy

Used the WithBot embedding approach (Approach A from the research report):

1. **`withBotHimp`** (new): Defines Heyting implication on `WithBot G` by case analysis --
   `⊥ ⇨ y = ⊤`, `↑a ⇨ ⊥ = ⊥`, `↑a ⇨ ↑b = ↑(a ⇨ b)`.

2. **`instHeytingAlgebraWithBot`** (new): Constructs `HeytingAlgebra (WithBot G)` for any
   `GeneralizedHeytingAlgebra G` using `HeytingAlgebra.ofHImp`. The adjunction proof proceeds
   by case analysis on `a`, `b`, `c ∈ WithBot G`.

3. **`coe_AlgEvaluate`** (new): Proves that for bot-free formulas, evaluation in `WithBot G`
   via the lifted valuation `↑∘v` equals the coercion of evaluation in `G`. Proved by
   structural induction on the formula. The `imp` case uses definitional equality of `↑a ⇨ ↑b`
   with `↑(a ⇨ b)` in `WithBot G`.

4. **`ipl_conservative_over_mpl`** (sorry filled): Using algebraic completeness for both MPL
   and IPL. Given an arbitrary GHA `G` and valuation `v`, instantiate IPL completeness at
   `WithBot G` with the lifted valuation. Apply `coe_AlgEvaluate` to translate back to `G`,
   then use `WithBot.coe_eq_coe` (injectivity) to conclude.

## Deviations from Plan

- **Phase 1 merge**: All three phases were implemented in a single edit pass because the
  dependencies were entirely local and the lean_run_code testing allowed pre-validation.

- **Import added**: Added `public import Mathlib.Order.WithBot` (needed for `WithBot.*`
  instances not transitively available) and `public import
  Cslib.Logics.Propositional.Semantics.Algebra.Completeness` (needed to access
  `MPL.alg_complete` and `IPL.alg_complete`; these are in a file not imported by the original
  Conservative.lean).

- **MPL.alg_complete access**: The plan assumed `rw [MPL.alg_complete]` would work, but due to
  a namespace conflict (`open Theory` makes `MPL` resolve to `Theory.MPL = ∅`, not the theorem
  namespace), the proof instead uses `simp only [MPL]` to unfold the abbreviation and then
  accesses `IPL.alg_complete` and the general completeness chain via a more explicit path. The
  final proof actually uses `MPL.alg_complete` with a preceding `simp only [MPL]` to produce
  goal `DerivableIn (↑∅) A`, which is what `MPL.alg_complete.mpr` expects.

- **Bot case in HA instance**: The `bot` cases use `simp [withBotHimp]` rather than manual
  case splits, which is cleaner and was verified in standalone tests.

## Verification Results

| Check | Result |
|-------|--------|
| `lake build` (Conservative module) | Passed |
| `lake exe checkInitImports` | Passed |
| `lake lint` (Conservative.lean) | No warnings |
| `lake exe lint-style` | Passed |
| `lake shake --add-public --keep-implied --keep-prefix` | No issues |
| `lean_verify ipl_conservative_over_mpl` | `{propext, Classical.choice, Quot.sound}` (no sorryAx) |
| `lean_verify coe_AlgEvaluate` | `{propext, Quot.sound}` (no sorryAx) |
| `lean_verify instHeytingAlgebraWithBot` | `{propext, Quot.sound}` (no sorryAx) |
| Sorry count in Conservative.lean | 0 |
| Axioms introduced | 0 (none beyond standard) |

## Files Modified

- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`
  - Added `public import Mathlib.Order.WithBot`
  - Added `public import Cslib.Logics.Propositional.Semantics.Algebra.Completeness`
  - Updated module docstring to describe the WithBot approach
  - Added `withBotHimp` definition (~5 lines)
  - Added `instHeytingAlgebraWithBot` instance (~20 lines)
  - Added `coe_AlgEvaluate` theorem (~15 lines)
  - Replaced `sorry` in `ipl_conservative_over_mpl` with complete proof (~6 lines)
  - Total new lines: ~66
