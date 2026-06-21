# Implementation Plan: NBA Emptiness Checking

- **Task**: 248 - NBA emptiness checking
- **Status**: [NOT STARTED]
- **Effort**: 2.5 hours
- **Dependencies**: None (all infrastructure already exists in CSLib)
- **Research Inputs**: specs/248_nba_emptiness_checking/reports/02_emptiness-research.md
- **Artifacts**: plans/01_emptiness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Formalize NBA emptiness checking as a semantic/declarative characterization theorem (Baier-Katoen Lemma 4.41) in `Cslib/Computability/Automata/NA/Emptiness.lean`. The central result states that an NBA's language is non-empty if and only if there exists a reachable accepting cycle: a state reachable from a start state that is accepting and lies on a non-trivial cycle. The implementation uses the existing `MTr`, `CanReach`, `OmegaExecution`, and `Filter.Frequently/atTop` infrastructure with no new algorithmic machinery needed.

### Research Integration

The research report (02_emptiness-research.md) established:
- Semantic/declarative approach is the right fit (no nested DFS or SCC algorithms needed)
- All building blocks exist: `frequently_in_finite_type` (pigeonhole), `frequently_iff_strictMono` (subsequence extraction), `OmegaExecution.extract_mTr`/`flatten_mTr`/`append` (run construction)
- Single import (`Cslib.Computability.Automata.NA.Basic`) provides all transitive dependencies
- Estimated 100-150 lines, zero sorry risk given well-understood proof techniques

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Temporal Logic / automata-theoretic model checking pipeline. The ROADMAP.md focuses on logic porting; this task extends CSLib's Computability/Automata module which is orthogonal to the porting roadmap. No specific ROADMAP.md items are advanced.

## Goals & Non-Goals

**Goals**:
- Define `Buchi.HasReachableAcceptingCycle` predicate
- Prove forward direction: non-empty language implies reachable accepting cycle (requires `[Finite State]`)
- Prove backward direction: reachable accepting cycle implies non-empty language (requires `[Inhabited Symbol]`)
- Prove combined iff characterization and emptiness-as-bot characterization
- Pass full CSLib CI pipeline

**Non-Goals**:
- Algorithmic emptiness checking (nested DFS, Tarjan SCC) -- deferred to executable verification tasks
- Decidability instance for `HasReachableAcceptingCycle` -- can be added later
- GNBA emptiness (follows trivially from NBA emptiness + existing GNBA-to-NBA translation)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `extract_mTr` API mismatch (name or signature differs from research assumption) | M | L | Use `lean_local_search` / `lean_hover_info` to verify exact API before coding |
| `frequently_in_finite_type` requires different universe or typeclass assumptions | M | L | Check exact signature; may need `Fintype` vs `Finite` coercion |
| Backward direction omega-word construction more complex than anticipated | M | M | Use `sorry` as placeholder, fill incrementally; research report provides clear strategy |
| Lint or style failures on new file | L | M | Run `lake exe lint-style` before committing; follow existing NA files as template |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: File Scaffolding, Definition, and Forward Direction [COMPLETED]

**Goal**: Create the `Emptiness.lean` file with module header, imports, the `HasReachableAcceptingCycle` definition, and prove the forward direction (non-empty language implies reachable accepting cycle).

**Tasks**:
- [ ] Create `Cslib/Computability/Automata/NA/Emptiness.lean` with copyright header, module docstring, and `public import Cslib.Computability.Automata.NA.Basic`
- [ ] Define `Buchi.HasReachableAcceptingCycle` as an existential over start state, accepting state, reachability via `CanReach`, and non-trivial self-loop via `MTr`
- [ ] Prove `Buchi.hasReachableAcceptingCycle_of_nonempty_language` (forward direction, requires `[Finite State]`):
  - Unfold `ωAcceptor.language` and `Accepts` to obtain `Run` and `∃ᶠ k in atTop, ss k ∈ a.accept`
  - Apply `frequently_in_finite_type` to extract a specific accepting state `q` visited infinitely often
  - Apply `frequently_iff_strictMono` to get strictly monotonic witnessing function `f`
  - Use `OmegaExecution.extract_mTr` at indices `(0, f 0)` and `(f 0, f 1)` to produce the reachability path and cycle
  - Show `f 0 < f 1` ensures the cycle label list is non-empty
- [ ] Register `Emptiness.lean` in the `Cslib/Computability/Automata/NA.lean` import hub (add `import Cslib.Computability.Automata.NA.Emptiness`)
- [ ] Run `lake build Cslib.Computability.Automata.NA.Emptiness` to verify compilation
- [ ] Run `lean_verify` on the forward direction theorem to check for axiom usage

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Computability/Automata/NA/Emptiness.lean` - new file (definition + forward direction)
- `Cslib/Computability/Automata/NA.lean` - add import line

**Verification**:
- `lake build Cslib.Computability.Automata.NA.Emptiness` succeeds
- `lean_verify` confirms no sorry usage in forward direction
- `lean_goal` at end of forward proof shows no remaining goals

---

### Phase 2: Backward Direction and Combined Characterization [COMPLETED]

**Goal**: Prove the backward direction (reachable accepting cycle implies non-empty language), the combined iff characterization, and the emptiness-as-bot theorem. Run full CI verification.

**Tasks**:
- [ ] Prove `Buchi.nonempty_language_of_hasReachableAcceptingCycle` (backward direction, requires `[Inhabited Symbol]`):
  - Unfold `HasReachableAcceptingCycle` to obtain `s0`, `q`, reachability path `μs_reach`, and cycle `μs_cycle` with `μs_cycle.length > 0`
  - Construct the omega-word by concatenating `μs_reach` with infinitely repeated `μs_cycle` (using `OmegaExecution.flatten_mTr` with `ωSequence.const` or equivalent)
  - Prepend the reachability prefix using `OmegaExecution.append` or `MTr.comp`
  - Show `q` appears at positions `|μs_reach| + k * |μs_cycle|` for all `k`, which is infinitely often (via `frequently_iff_strictMono` with a linear witness function)
  - Package into `ωAcceptor.language` membership
- [ ] Prove `Buchi.language_nonempty_iff_hasReachableAcceptingCycle` (combined iff, requires `[Finite State]` and `[Inhabited Symbol]`):
  - Forward: apply Phase 1 theorem
  - Backward: apply backward direction theorem
- [ ] Prove `Buchi.language_eq_bot_iff` (emptiness characterization):
  - Rewrite using `language_nonempty_iff_hasReachableAcceptingCycle` and set complement logic
- [ ] Add docstrings to all public declarations (required by docBlame linter)
- [ ] Run full CI verification:
  - `lake build` (full project build)
  - `lake test` (CslibTests suite)
  - `lake exe checkInitImports` (import verification)
  - `lake exe lint-style` (style linting)
- [ ] Run `lean_verify` on all theorems in the file to confirm no sorry usage

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Computability/Automata/NA/Emptiness.lean` - add backward direction, iff, bot theorems

**Verification**:
- `lake build` succeeds with no errors
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lean_verify` confirms all theorems are sorry-free and axiom-clean
- No warnings or errors in `lean_diagnostic_messages` for the file

## Testing & Validation

- [ ] `lake build Cslib.Computability.Automata.NA.Emptiness` compiles successfully
- [ ] `lake build` (full project) succeeds
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lean_verify` on all four public theorems shows no sorry usage
- [ ] All public declarations have docstrings (docBlame linter)

## Artifacts & Outputs

- `Cslib/Computability/Automata/NA/Emptiness.lean` - new file (~100-150 lines)
- `Cslib/Computability/Automata/NA.lean` - updated import hub
- `specs/248_nba_emptiness_checking/plans/01_emptiness-plan.md` - this plan
- `specs/248_nba_emptiness_checking/summaries/01_emptiness-summary.md` - implementation summary (created at completion)

## Rollback/Contingency

Remove the new file and revert the import line addition:
```bash
git checkout -- Cslib/Computability/Automata/NA.lean
rm Cslib/Computability/Automata/NA/Emptiness.lean
```
No other files are modified, so rollback is clean and trivial.
