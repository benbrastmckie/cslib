# Implementation Plan: Conservative Extension of IPL over MPL

- **Task**: 265 - track_conservative_lean_sorry
- **Status**: [IMPLEMENTING]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/265_track_conservative_lean_sorry/reports/01_conservative-extension-proof.md
- **Artifacts**: plans/01_conservative-extension-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Fill the `sorry` in `ipl_conservative_over_mpl` (Conservative.lean:99) using the WithBot embedding strategy identified in research. The proof adjoins a bottom element to any GeneralizedHeytingAlgebra G to produce a HeytingAlgebra (WithBot G), proves an embedding lemma that bot-free evaluation commutes with the coe embedding, then chains IPL/MPL algebraic completeness to close the theorem. All code goes in a single file. Estimated 55-70 lines of new Lean 4 code.

### Research Integration

The research report (`01_conservative-extension-proof.md`) identified four alternative approaches and recommended the WithBot embedding (Approach A) as the cleanest:

- **WithBot embedding (chosen)**: Adjoin bottom to any GHA via `WithBot G`, define Heyting implication by case analysis, prove embedding lemma by structural induction, chain completeness theorems. ~55-70 lines, all Mathlib prerequisites available, verified in standalone tests.
- **Syntactic proof transformation (rejected)**: 100+ lines, requires unformalized normalization theorem.
- **Kripke semantics (rejected)**: Requires unformalized Kripke completeness for both MPL and IPL.
- **Dedekind-MacNeille completion (rejected)**: Incorrect in general (does not preserve Heyting implication) and unavailable in Mathlib.

Key Mathlib APIs: `WithBot.distribLattice`, `WithBot.coe_inf`, `WithBot.coe_sup`, `WithBot.coe_eq_coe`, `HeytingAlgebra.ofHImp`, `le_himp_iff`, `WithBot.not_coe_le_bot`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly correspond to this propositional-level conservative extension result. The task resolves the last untracked sorry in the codebase, improving overall proof hygiene.

## Goals & Non-Goals

**Goals**:
- Define `withBotHimp` (Heyting implication on `WithBot G`) for any GHA `G`
- Construct `HeytingAlgebra (WithBot G)` instance using `HeytingAlgebra.ofHImp`
- Prove `coe_AlgEvaluate` embedding lemma for bot-free formulas
- Fill the `sorry` in `ipl_conservative_over_mpl` with a complete proof
- Update the module docstring to remove the "deferred" language

**Non-Goals**:
- Contributing `HeytingAlgebra (WithBot G)` upstream to Mathlib (local definition suffices)
- Proving non-bot-free variants of the conservative extension
- Formalizing syntactic or Kripke-based alternative proofs
- Adding new test cases (the existing `lake test` suite covers regression)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `HeytingAlgebra.ofHImp` adjunction proof requires unexpected case splits | M | L | Research verified the instance compiles; use `lean_goal` to inspect proof state incrementally |
| Universe level mismatch between `WithBot G` and completeness theorems | H | L | Research confirmed `WithBot G : Type u` when `G : Type u`; verify with `lean_hover_info` |
| `WithBot.coe_top` or related simp lemma missing or renamed in current Mathlib | M | L | Use `lean_loogle` to search for the correct lemma name; fall back to manual proof |
| Existing `AlgEvaluate` simp lemmas interfere with embedding lemma proof | L | L | Use `simp only` with explicit lemma lists rather than bare `simp` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: WithBot HeytingAlgebra Instance [IN PROGRESS]

**Goal**: Define `withBotHimp` and prove the `HeytingAlgebra (WithBot G)` instance for any GeneralizedHeytingAlgebra G.

**Tasks**:
- [ ] Add `import Mathlib.Order.WithBot` to Conservative.lean (if not already transitively available)
- [ ] Update module docstring: remove "deferred" and "Dedekind-MacNeille" references, describe the WithBot approach
- [ ] Define `noncomputable def withBotHimp` with three cases: `none => _ => top`, `some a => none => none`, `some a => some b => some (a => b)`
- [ ] Construct `noncomputable instance : HeytingAlgebra (WithBot G)` using `HeytingAlgebra.ofHImp` with adjunction proof by case analysis on `a`, `b`, `c`
- [ ] Verify with `lean_goal` at key case-split points
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Algebra.Conservative` to confirm compilation

**Timing**: 25 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` - Add withBotHimp definition and HA instance (insert between line 88 and line 90, i.e., after the section comment and before the `variable` declaration)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Conservative` succeeds with no errors
- `lean_goal` shows no sorry in the new instance

---

### Phase 2: Embedding Lemma [NOT STARTED]

**Goal**: Prove `coe_AlgEvaluate`: for bot-free formulas, evaluation in `WithBot G` via the lifted valuation equals the coe of evaluation in G.

**Tasks**:
- [ ] Define `theorem coe_AlgEvaluate` with signature matching: `AlgEvaluate (fun x => (v x : WithBot G)) (bot : WithBot G) A = ((AlgEvaluate v bot_val A : G) : WithBot G)` for bot-free A
- [ ] Prove by structural induction on A with cases: `atom` (rfl), `bot` (contradiction from IsBotFree), `imp` (uses withBotHimp definition), `and` (uses `WithBot.coe_inf`), `or` (uses `WithBot.coe_sup`)
- [ ] Verify each inductive case with `lean_goal`
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Algebra.Conservative` to confirm

**Timing**: 20 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` - Add coe_AlgEvaluate theorem after the HA instance

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Conservative` succeeds
- `lean_verify` on `coe_AlgEvaluate` shows no sorry

---

### Phase 3: Main Theorem and Cleanup [NOT STARTED]

**Goal**: Fill the `sorry` in `ipl_conservative_over_mpl` and verify the entire file.

**Tasks**:
- [ ] Replace `sorry` in `ipl_conservative_over_mpl` with the proof: rewrite with `MPL.alg_complete`, intro GHA and valuation, instantiate `IPL.alg_complete.mp h` at `WithBot G` with lifted valuation, rewrite using `coe_AlgEvaluate`, conclude via `WithBot.coe_eq_coe`
- [ ] Update the theorem docstring to remove "deferred" reference and describe the proof strategy
- [ ] Verify with `lean_goal` that no goals remain after proof
- [ ] Run `lean_verify` on `Cslib.Logic.PL.ipl_conservative_over_mpl` to confirm no sorry/axioms
- [ ] Run full CI verification:
  - `lake build Cslib.Logics.Propositional.Semantics.Algebra.Conservative`
  - `lake exe checkInitImports`
  - `lake exe lint-style`

**Timing**: 15 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` - Replace sorry with proof, update docstrings

**Verification**:
- `lean_verify Cslib.Logic.PL.ipl_conservative_over_mpl` reports no sorry or non-standard axioms
- `lake build` succeeds on the module
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.Conservative` compiles without errors
- [ ] `lean_verify Cslib.Logic.PL.ipl_conservative_over_mpl` shows no sorry
- [ ] `lake exe checkInitImports` passes (Cslib.Init import present)
- [ ] `lake exe lint-style` passes (no style violations)
- [ ] `lake test` passes (no regression in CslibTests)

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` - Modified with ~55-70 new lines
- `specs/265_track_conservative_lean_sorry/plans/01_conservative-extension-plan.md` - This plan
- `specs/265_track_conservative_lean_sorry/summaries/01_conservative-extension-summary.md` - Post-implementation summary

## Rollback/Contingency

All changes are confined to a single file (`Conservative.lean`). If the implementation fails:
- `git checkout -- Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` restores the sorry state
- No other files are affected; no imports or module structure changes are required
- If `HeytingAlgebra.ofHImp` proves unexpectedly difficult, fall back to defining the instance manually with all fields, which is more verbose but avoids the adjunction proof format
