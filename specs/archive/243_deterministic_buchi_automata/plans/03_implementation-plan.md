# Implementation Plan: Task #243

- **Task**: 243 - Implement deterministic Buchi automata constructions and related results
- **Status**: [IMPLEMENTING]
- **Effort**: 10 hours
- **Dependencies**: None (builds on existing DA/ infrastructure)
- **Research Inputs**: reports/01_dba-constructions-survey.md, reports/02_team-research.md
- **Artifacts**: plans/03_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This plan adds DBA closure properties, the Landweber characterization theorem, and a DBA-to-DMA
conversion to CSLib's existing deterministic automata infrastructure. The existing DA/ directory
provides `DA`, `DA.Buchi`, `DA.Muller`, `DA.prod`, and `buchi_eq_finAcc_omegaLim`. Two new files
are created: `BuchiClosure.lean` (closure under union/intersection, non-closure under complement)
and `BuchiChar.lean` (Landweber's theorem and DBA-to-DMA conversion). A prerequisite lemma
`DA.prod_run_eq` is added to the existing `Prod.lean`. The implementation follows Thomas 2003
Ch. 1 and Ch. 3 as primary references, supplemented by Baier and Katoen 2008 Exercises 4.22-4.23.

### Research Integration

Two research reports inform this plan:
- **Report 01** (DBA constructions survey): Identified existing CSLib infrastructure, scoped
  the work to closure properties + Landweber + DBA-to-DMA, and mapped literature sources.
- **Report 02** (team synthesis, 4 teammates): Corrected effort estimates (Landweber 500-700
  lines, not 300-400), identified the critical missing prerequisite `DA.prod_run_eq`, confirmed
  `Filter.frequently_or_distrib` suffices for union proof, established that DBA intersection
  requires fresh construction (no `DA.addHist`), and identified Landweber forward-direction
  source gap (Thomas 2003 "outnumbered" term undefined). Corrected type signature for Landweber
  to require `[Fintype State] [DecidableEq State]`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

The ROADMAP focuses on logic porting (BimodalLogic to CSLib). Task 243 is in the Computability/
Automata layer, not directly listed in the ROADMAP. However, it supports task 241 (McNaughton's
theorem) which is needed for the automata-theoretic model checking pipeline.

## Goals & Non-Goals

**Goals**:
- Prove DBA closure under union via product construction
- Prove DBA closure under intersection via product with 3-state counter
- Prove DBA non-closure under complement (concrete witness)
- Prove Landweber's theorem: DBA-recognizable iff acceptance family closed under superloops
- Implement DBA-to-DMA conversion (`DA.Buchi.toMuller`)
- All proofs sorry-free with clean CI

**Non-Goals**:
- DBA minimization (NP-complete; Loding 2001 behind paywall)
- Classification hierarchy (E < Buchi < co-Buchi < Muller) -- future task
- DBA-to-DPA conversion (deferred to task 252, acceptance conditions zoo)
- Complement construction (DBA cannot be complemented; NBA complement is task 250)
- SCC infrastructure for DBA (define `IsLoop` directly instead)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Landweber forward direction exceeds 700 lines due to `Finset State` accumulation | H | M | Split into sub-phases; if Phase 4 exceeds budget, mark forward direction `proof_wanted` and complete backward direction |
| `infOcc` interaction with product runs needs unexpected helper lemmas | M | M | Validate `infOcc` API early in Phase 1 prerequisites; add helpers to InfOcc.lean as needed |
| DBA intersection counter proof more complex than NBA template suggests | M | L | Follow Thomas 2003 Ch. 1 counter trick; use `Temporal.lean` lemmas already imported by `BuchiInter.lean` |
| `[DecidableEq State]` propagation issues in Landweber construction | L | L | Use `open scoped Classical` at construction site, matching CSLib convention in `BuchiCompl.lean` |
| Thomas 2003 forward direction "outnumbered" gap requires independent derivation | M | H | Define reset predicate explicitly; document in docstring that this goes beyond the text |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Prerequisites and Product Run Lemma [COMPLETED]

**Goal**: Add `DA.prod_run_eq` to `Prod.lean` and any needed `infOcc` helper lemmas to
`InfOcc.lean`, establishing the foundation for all subsequent phases.

**Tasks**:
- [ ] Add `DA.prod_run_eq` to `Cslib/Computability/Automata/DA/Prod.lean`: prove
  `(da1.prod da2).run xs n = (da1.run xs n, da2.run xs n)` by induction on `n`
- [ ] Add `@[simp]` and `@[scoped grind =]` annotations matching existing `prod_mtr_eq` style
- [ ] Verify the lemma works with `simp` in a test proof
- [ ] Assess whether `infOcc` helpers (`infOcc_finite`, `mem_infOcc`, `infOcc_nonempty_of_finite`)
  are needed now or can be deferred to Phase 4; add to `InfOcc.lean` if needed by Phase 2

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Computability/Automata/DA/Prod.lean` -- add `prod_run_eq` (~10 lines)
- `Cslib/Foundations/Data/OmegaSequence/InfOcc.lean` -- possibly add helper lemmas (~20-30 lines)

**Verification**:
- `lake build Cslib.Computability.Automata.DA.Prod` passes
- `lean_verify` on `DA.prod_run_eq` shows no sorry, no non-standard axioms

---

### Phase 2: DBA Union and Complement Non-Closure [IN PROGRESS]

**Goal**: Create `BuchiClosure.lean` with DBA union construction (product automaton with
`accept = F1 x univ union univ x F2`) and DBA complement non-closure witness (2-state DBA
for "infinitely many 1s").

**Tasks**:
- [ ] Create `Cslib/Computability/Automata/DA/BuchiClosure.lean` with module header, imports,
  copyright, and CSLib namespace structure
- [ ] Define `DA.Buchi.union` using `DA.prod` with accept set `(a1.accept xS Set.univ) union (Set.univ xS a2.accept)`
- [ ] Prove `DA.Buchi.union_language_eq`: language equality using `DA.prod_run_eq` and
  `Filter.frequently_or_distrib`
- [ ] Define `DA.Buchi.infOftenOne`: concrete 2-state DBA over `Fin 2` accepting "infinitely many 1s"
- [ ] Prove `DA.Buchi.infOftenOne_language_eq`: language correctness for the witness DBA
- [ ] Prove `DA.Buchi.not_closed_complement`: exhibit `infOftenOne` as DBA-recognizable language
  whose complement is not DBA-recognizable (using existing `eventuallyZero_not_omegaLim`)

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Computability/Automata/DA/BuchiClosure.lean` -- new file (~140-180 lines)

**Verification**:
- `lake build Cslib.Computability.Automata.DA.BuchiClosure` passes
- `lean_verify` on all new theorems shows no sorry
- `lake exe checkInitImports` passes (file imports `Cslib.Init`)

---

### Phase 3: DBA Intersection [NOT STARTED]

**Goal**: Add DBA intersection with 3-state counter to `BuchiClosure.lean`. The counter tracks
which accepting set was last visited (wait for F1, wait for F2, reset).

**Tasks**:
- [ ] Define `DA.Buchi.interCounterTr`: counter transition function (`Fin 3`) that cycles
  0 -> 1 when F1 visited, 1 -> 2 when F2 visited, 2 -> 0/1 based on F1
- [ ] Define `DA.Buchi.inter` as `noncomputable def` (requires Classical for membership check):
  state space `State1 x State2 x Fin 3`, accept set `univ x univ x {2}`
- [ ] Prove forward direction of `inter_language_eq`: counter reaching 2 infinitely often implies
  both F1 and F2 visited infinitely often (counter cycle argument)
- [ ] Prove backward direction: both F1 and F2 visited infinitely often implies counter cycles
  through all states infinitely often
- [ ] Combine into `DA.Buchi.inter_language_eq` iff theorem

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Computability/Automata/DA/BuchiClosure.lean` -- extend existing file (~150-200 lines)

**Verification**:
- `lake build Cslib.Computability.Automata.DA.BuchiClosure` passes
- `lean_verify` on `DA.Buchi.inter_language_eq` shows no sorry
- All three closure results (union, complement non-closure, intersection) are sorry-free

---

### Phase 4: Landweber's Theorem [COMPLETED]

**Goal**: Create `BuchiChar.lean` with the Landweber characterization: a DMA language is
DBA-recognizable iff its acceptance family is closed under superloops (Thomas 2003 Thm 3.32).

**Tasks**:
- [ ] Create `Cslib/Computability/Automata/DA/BuchiChar.lean` with module header and imports
- [ ] Define `DA.IsLoop` on the base `DA` type (not `DA.Muller`): a set S is a loop if it is
  nonempty and every state in S can reach every other state in S via a nonempty word
- [ ] Define `DA.Muller.ClosedUnderSuperloops`: for every F in accept that is a loop, every
  superloop F' containing F is also in accept
- [ ] Add any needed `infOcc` helper lemmas to `InfOcc.lean` if not added in Phase 1
- [ ] Prove backward direction (DBA-recognizable -> ClosedUnderSuperloops): given DBA recognizing
  L, take F in accept and superloop F' containing F; construct omega-word interleaving F and
  F' states using `omegaSequence.flatten`; show infOcc = F' and word is accepted; conclude
  F' in accept
- [ ] Prove forward direction (ClosedUnderSuperloops -> DBA-recognizable): construct DBA with
  state space `State x Finset State`, accumulate visited states, reset when accumulated set
  contains some F in accept as subset; prove resets happen infinitely often iff infOcc is in accept
- [ ] Combine into `DA.Muller.dba_recognizable_iff_closedUnderSuperloops` with constraints
  `[Fintype State] [DecidableEq State]`

**Timing**: 4 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Computability/Automata/DA/BuchiChar.lean` -- new file (~500-700 lines)
- `Cslib/Foundations/Data/OmegaSequence/InfOcc.lean` -- possibly add helper lemmas

**Verification**:
- `lake build Cslib.Computability.Automata.DA.BuchiChar` passes
- `lean_verify` on `DA.Muller.dba_recognizable_iff_closedUnderSuperloops` shows no sorry
- If forward direction proves intractable within budget, mark it `proof_wanted` and document
  the gap; the backward direction alone is still valuable

---

### Phase 5: DBA-to-DMA Conversion and CI Verification [COMPLETED]

**Goal**: Add `DA.Buchi.toMuller` conversion and run full CI verification pipeline.

**Tasks**:
- [ ] Define `DA.Buchi.toMuller`: Muller automaton with accept family `{S | S inter a.accept ne empty}`
- [ ] Prove `DA.Buchi.toMuller_language_eq`: Muller language equals Buchi language, connecting
  via `infOcc` membership characterization
- [ ] Update `Cslib.lean` barrel import with `lake exe mk_all --module` to register new files
- [ ] Run full CI: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake test`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` for import minimization
- [ ] Add docstring cross-references: BuchiChar.lean -> BuchiCompl.lean (noting Landweber
  explains why rank-based NBA complementation is necessary)

**Timing**: 1 hour

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Computability/Automata/DA/BuchiChar.lean` -- extend with toMuller (~20-30 lines)
- `Cslib.lean` -- regenerated barrel import

**Verification**:
- Full CI pipeline passes: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake test`, `lake shake`
- `lean_verify` on all new definitions shows no sorry, no non-standard axioms
- All new files import `Cslib.Init`

## Testing & Validation

- [ ] `lake build` compiles all new files without errors or warnings
- [ ] `lake exe checkInitImports` passes (all new files import `Cslib.Init`)
- [ ] `lake exe lint-style` passes (no style violations)
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lean_verify` on every new theorem/def shows no `sorry` and no non-standard axioms
- [ ] `DA.Buchi.union_language_eq` -- DBA union language correctness
- [ ] `DA.Buchi.inter_language_eq` -- DBA intersection language correctness
- [ ] `DA.Buchi.not_closed_complement` -- DBA complement non-closure
- [ ] `DA.Muller.dba_recognizable_iff_closedUnderSuperloops` -- Landweber characterization
- [ ] `DA.Buchi.toMuller_language_eq` -- DBA-to-DMA conversion correctness

## Artifacts & Outputs

- `Cslib/Computability/Automata/DA/Prod.lean` -- extended with `prod_run_eq`
- `Cslib/Computability/Automata/DA/BuchiClosure.lean` -- new file (union, intersection, complement non-closure)
- `Cslib/Computability/Automata/DA/BuchiChar.lean` -- new file (Landweber theorem, DBA-to-DMA)
- `Cslib/Foundations/Data/OmegaSequence/InfOcc.lean` -- possibly extended with helper lemmas
- `specs/243_deterministic_buchi_automata/plans/03_implementation-plan.md` -- this plan

## Rollback/Contingency

All new code is in new files (`BuchiClosure.lean`, `BuchiChar.lean`) plus small additions to
existing files (`Prod.lean`, `InfOcc.lean`). Rollback is straightforward: delete the new files
and revert the additions to existing files. The existing DA/ infrastructure is not modified in
any breaking way.

If the Landweber forward direction proves intractable (exceeds budget or encounters unexpected
blockers with `Finset State` accumulation), the backward direction and all closure properties
can still be submitted as a valuable self-contained PR. The forward direction can be marked
`proof_wanted` for future completion.
