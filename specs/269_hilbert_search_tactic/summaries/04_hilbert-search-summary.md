# Implementation Summary: Generic Hilbert Proof-Search Tactic

- **Task**: 269 - hilbert_search_tactic
- **Plan**: plans/04_hilbert-search-plan-v2.md
- **Status**: [COMPLETED]
- **Session**: sess_1782213029_bff826

## What Was Implemented

A generic bounded depth-first proof-search tactic `hilbert_search` for CSLib's
`InferenceSystem` typeclass, enabling automated Hilbert-style derivations across
all registered proof systems.

### Phase 1: MetaM Search Core and Tactic Wrapper [COMPLETED]

Created `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` with:

- **`hilbertSearchCore`**: A `partial def` MetaM function implementing bounded DFS with
  four-priority rule stratification:
  1. Assumption lookup (scan local context for matching `DerivableIn S phi` hypotheses)
  2. Zero-subgoal axioms: 40+ axiom/theorem names including all propositional, modal,
     temporal (22 BX axioms), and bimodal interaction axioms
  3. One-subgoal rules: `Necessitation.nec`, `TemporalNecessitation.tempNec/tempNecPast`,
     `box_mono`
  4. Two-subgoal rules: `imp_trans`, `ModusPonens.mp` (tried last to prevent explosion)

- **`hilbert_search` tactic**: Elab syntax with optional fuel parameter (default 30)
  and informative error messages on exhaustion

- **Cycle detection**: Uses `Lean.ExprSet` to track visited goal types per search path

- **Backtracking**: Uses `MetaContext.setMCtx` to restore MetaM state on failed branches

- **Trace class**: `trace.Cslib.Logic.hilbertSearch` for debugging

- **`tryApplyName`**: Helper using `mkConstWithFreshMVarLevels` + `MVarId.apply` with
  `ApplyConfig { newGoals := .nonDependentOnly }` for universe-polymorphic matching

### Phase 2: Comprehensive Test Suite [COMPLETED]

Created `CslibTests/HilbertSearch.lean` with 21 test cases:

- **Tier 1 (depth 1-3, default fuel)**: ImplyK, identity, MP+assumptions, box_mono,
  nec(identity), EFQ, Peirce, b_combinator, ImplyS, axiom K, axiom T, axiom 4
- **Propositional system tests**: Tests on concrete `HilbertCl` tag type with
  `PL.Proposition Nat` formula type
- **Tier 2 (deeper)**: Multi-step MP chaining, `imp_trans`, nested box via nec+nec
- **Negative tests**: `fail_if_success` with `hilbert_search 0` and low-fuel on deep goals

### Phase 3: Temporal and Extended Axiom Coverage [COMPLETED]

Added temporal axiom coverage:
- All 22 BX temporal axioms in `zeroSubgoalAxioms`
- `TemporalNecessitation.tempNec` and `tempNecPast` in `oneSubgoalRules`
- 4 temporal test cases: serial future, identity, MP from hypotheses, G-necessitation

### Phase 4: CI Verification and Cleanup [COMPLETED]

CI results:
- `lake build Cslib.Foundations.Logic.Automation.HilbertSearch`: PASSED
- `lake build CslibTests.HilbertSearch`: PASSED
- `lake exe checkInitImports`: Blocked by pre-existing `OmegaRegularLanguage` build failure
- `lake lint`: Blocked by same pre-existing issue
- `lake exe lint-style Cslib/Foundations/Logic/Automation/HilbertSearch.lean CslibTests/HilbertSearch.lean`: PASSED
- `lake exe mk_all --module`: PASSED (Cslib.lean and CslibTests.lean updated)
- No `sorry` in any new file
- No new axioms introduced
- `Cslib.Init` imported transitively via ProofSystem → InferenceSystem → Init

**Pre-existing CI failure**: `Cslib.Computability.Languages.OmegaRegularLanguage` has a
pre-existing build error (unrelated to this task). This blocks `lake lint`, `lake test`,
`lake exe checkInitImports`, and `lake shake` at the global level. Confirmed pre-existing
by checking that the module failed before my changes were applied.

## Plan Deviations

1. **`matchDerivableIn` helper removed**: The plan called for an `Option (Expr × Expr)` 
   helper to decompose `DerivableIn S phi` expressions. This was unnecessary in the
   MetaM approach — `apply` handles goal matching implicitly. *(deviation: skipped)*

2. **`identity` moved to `zeroSubgoalAxioms`**: Originally planned in `oneSubgoalRules`,
   but `identity` takes no derivability hypotheses and closes goals directly via `apply`.
   Same for `b_combinator`. *(deviation: altered)*

3. **`@[expose] public section` not used**: The `public meta section` pattern is used
   instead (appropriate for tactic code). *(deviation: altered -- tactic files use
   `public meta section`, not `@[expose] public section`)*

## Artifacts

- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Automation/HilbertSearch.lean`
- `/home/benjamin/Projects/cslib/CslibTests/HilbertSearch.lean`
- `/home/benjamin/Projects/cslib/Cslib.lean` (updated via `mk_all`)
- `/home/benjamin/Projects/cslib/CslibTests.lean` (updated via `mk_all`)
