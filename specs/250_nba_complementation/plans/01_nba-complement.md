# Implementation Plan: Task #250

- **Task**: 250 - NBA Complementation
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Dependencies**: None (standalone rank-based construction; does not depend on task 241)
- **Research Inputs**: specs/250_nba_complementation/reports/03_team-research.md
- **Artifacts**: plans/01_nba-complement.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Implement NBA (nondeterministic Buchi automaton) complementation using the Kupferman-Vardi 2001 Section 5.2 direct rank-based construction. Given an NBA A with state space Q, the complement NBA has states of the form (level ranking, obligation set), where a level ranking is a function Q -> Option (Fin (2n+1)) and an obligation set P is a Finset of states. The complement accepts when P cycles through empty infinitely often, ensuring no accepting run exists in the original automaton. This construction avoids full determinization (blocked by task 241) and provides an explicit automaton witness that the existing language-theoretic `IsRegular.compl` cannot produce.

### Research Integration

The team research report (4 teammates, all HIGH confidence) unanimously recommends the KV2001 Section 5.2 direct rank-based construction. Key findings integrated:

- The construction state space is `(State -> WithBot (Fin (2 * n + 1))) x Finset State` where `n = Fintype.card State`
- Central correctness hinge is the ranking lemma (KV2001 Lemma 5.2): "A rejects w iff the run DAG of A on w has an odd ranking"
- Forward direction (soundness: odd ranking implies rejection) is direct
- Backward direction (completeness: rejection implies odd ranking exists) requires an inductive removal procedure and is rated Very High difficulty
- No existing Lean 4 or Coq formalization of this construction exists
- Reusable infrastructure: `NA.Buchi`, `NA.addHist`, `frequently_in_finite_type`, `frequently_iff_strictMono`, `OmegaExecution.extract_mTr`

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Define the complement NBA construction `NA.Buchi.complementNA` with explicit state type
- Prove soundness: `language (complementNA a) <= (language a)^c` (complement accepts implies original rejects)
- Prove completeness: `(language a)^c <= language (complementNA a)` (original rejects implies complement accepts)
- State the combined theorem `complement_language_eq : language (complementNA a) = (language a)^c`
- Add corollaries: language universality (`language_univ_iff`) and language inclusion (`language_le_iff`) via complement + emptiness/intersection

**Non-Goals**:
- Schewe 2009 tight-bound optimizations (follow-up task)
- Alternating automata pipeline (KV2001 Section 5.1)
- McNaughton/Safra determinization (task 241)
- Extraction of constructive witness from existing `IsRegular.compl`
- Concrete test automata (useful but out of scope for this plan)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Ranking lemma backward direction intractable | H | H | Accept Phases 1-3 as minimum viable; Phase 4 may use `proof_wanted` |
| Konig's Lemma bridge from Mathlib | M | M | Consider custom finite-width DAG lemma instead of bridging Mathlib's abstract version |
| `Fintype` vs `Finite` constraint mismatch | M | L | Require `[Fintype State]` explicitly; CSLib NBA infrastructure uses `[Finite State]` in emptiness but `Fintype` is strictly stronger |
| Dependent-type complexity in `Fin (2*n+1)` | M | M | Use `Nat`-valued rankings with separate boundedness proofs as fallback |
| Large proof size exceeds single-phase budget | M | M | Each phase scoped to 1.5-2 hours; split further if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 2 |
| 5 | 5 | 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Complement Construction and Infrastructure [IN PROGRESS]

**Goal**: Define the complement NBA state type, transition relation, acceptance condition, and the top-level `complementNA` definition. Establish the run DAG and level ranking vocabulary needed for correctness proofs.

**Tasks**:
- [ ] Create file `Cslib/Computability/Automata/NA/BuchiCompl.lean` with module header and imports
- [ ] Define `RunDAG`: the run DAG of an NBA on an input word (nodes are (State, Nat) pairs reachable via valid transitions from start states)
- [ ] Define `LevelRanking`: a function `State -> WithBot (Fin (2 * Fintype.card State + 1))` assigning ranks to states (or bottom for unreachable states)
- [ ] Define `covers`: the relation that a level ranking g' sigma-covers g (for each transition s -sigma-> t, if g(s) is defined then g'(t) is defined and g'(t) <= g(s), with accepting states getting strictly odd rank)
- [ ] Define `OddRanking`: a sequence of level rankings where consecutive rankings cover each other
- [ ] Define complement state type: `(State -> WithBot (Fin (2 * n + 1))) x Finset State` where n = `Fintype.card State`
- [ ] Define complement transitions: non-deterministically choose g' that covers current g, update obligation set P
- [ ] Define complement acceptance: `P = emptyset`
- [ ] Define `complementNA : Buchi State Symbol -> Buchi _ Symbol` assembling the above
- [ ] Add the file to `Cslib.lean` barrel import via `lake exe mk_all --module`
- [ ] Verify the file compiles with `lake build Cslib.Computability.Automata.NA.BuchiCompl`

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Computability/Automata/NA/BuchiCompl.lean` - new file with all definitions
- `Cslib.lean` - barrel import update (via `mk_all`)

**Verification**:
- File compiles without errors
- `complementNA` has the expected type signature
- All definitions are `noncomputable` where needed (complement transition involves classical choice)

---

### Phase 2: Soundness Helper Lemmas [NOT STARTED]

**Goal**: Prove helper lemmas relating the complement automaton's behavior to run DAG properties, and establish the forward direction of the ranking lemma: if an odd ranking exists, the original NBA rejects the word.

**Tasks**:
- [ ] Prove that an accepting run of the complement NBA yields a sequence of level rankings that mutually cover
- [ ] Prove that such a covering sequence implies that no run of the original NBA visits accepting states infinitely often (the ranking decreases argument)
- [ ] Prove the forward direction of the ranking lemma: odd ranking on run DAG implies no accepting run
- [ ] Prove monotonicity/finiteness lemmas for level rankings (ranks are bounded, decreasing on accepting states ensures finite visits)
- [ ] Add `@[simp]` and `@[scoped grind =]` attributes where appropriate

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Computability/Automata/NA/BuchiCompl.lean` - add lemmas after definitions

**Verification**:
- All lemmas compile without `sorry`
- Forward direction of ranking lemma is stated and proved

---

### Phase 3: Soundness Theorem [NOT STARTED]

**Goal**: Prove the soundness direction of complement correctness: if the complement NBA accepts a word, then the original NBA rejects that word. This combines the helper lemmas from Phase 2 into the inclusion `language (complementNA a) <= (language a)^c`.

**Tasks**:
- [ ] State `complement_language_sub : language (complementNA a) <= (language a)^c`
- [ ] Prove by showing: complement accepts w -> extract level ranking sequence -> forward ranking lemma -> original rejects w
- [ ] Verify the proof compiles and is sorry-free
- [ ] Run `lake build Cslib.Computability.Automata.NA.BuchiCompl` to verify

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Computability/Automata/NA/BuchiCompl.lean` - add soundness theorem

**Verification**:
- `complement_language_sub` compiles without `sorry`
- `lean_verify` confirms no axiom usage beyond standard

---

### Phase 4: Completeness Theorem [NOT STARTED]

**Goal**: Prove the completeness direction: if the original NBA rejects a word, then the complement NBA accepts it. This is the hard direction requiring construction of an odd ranking from the rejection hypothesis, potentially using Konig's Lemma or an inductive removal argument.

**Tasks**:
- [ ] Prove the backward direction of the ranking lemma: if no run of the original NBA is accepting, then the run DAG has an odd ranking
  - [ ] Attempt the inductive removal procedure: iteratively remove nodes from the run DAG whose sub-DAGs have infinitely many paths, showing each removal strictly decreases width
  - [ ] If the Konig's Lemma bridge from Mathlib is needed, prove the bridging lemma
  - [ ] If intractable, mark with `proof_wanted` and document the blocker
- [ ] Construct the accepting run of the complement NBA from the odd ranking
- [ ] State and prove `complement_language_sup : (language a)^c <= language (complementNA a)`
- [ ] If the backward ranking lemma is blocked, use `proof_wanted` for `complement_language_sup` as well

**Timing**: 2 hours (may extend or result in `proof_wanted`)

**Depends on**: 2

**Files to modify**:
- `Cslib/Computability/Automata/NA/BuchiCompl.lean` - add completeness theorem and supporting lemmas

**Verification**:
- Either `complement_language_sup` compiles sorry-free, OR
- A clear `proof_wanted` is placed with documented blocker and the phase is marked `[BLOCKED]`

---

### Phase 5: Main Theorem and Corollaries [NOT STARTED]

**Goal**: Combine soundness and completeness into the main complement language equality theorem, and derive immediate corollaries for language universality and inclusion checking.

**Tasks**:
- [ ] State and prove `complement_language_eq : language (complementNA a) = (language a)^c` (combining sub and sup directions)
  - [ ] If Phase 4 resulted in `proof_wanted`, use `proof_wanted` here as well
- [ ] Derive `language_univ_iff : language a = top <-> not (HasReachableAcceptingCycle (complementNA a))` using complement + emptiness (task 248)
- [ ] Derive `language_le_iff` for language inclusion via complement + intersection (BuchiInter)
- [ ] Add module docstring summarizing the file's contents and references
- [ ] Run full CI verification: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake test`

**Timing**: 1 hour

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Computability/Automata/NA/BuchiCompl.lean` - add main theorem, corollaries, and docstring

**Verification**:
- Full CI pipeline passes
- `complement_language_eq` is stated (proved or `proof_wanted`)
- Corollary theorems compile
- No lint warnings in the new file

## Testing & Validation

- [ ] `lake build Cslib.Computability.Automata.NA.BuchiCompl` compiles without errors at each phase
- [ ] `lake exe checkInitImports` passes (file imports `Cslib.Init`)
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lean_verify` on key theorems confirms no unexpected axiom usage
- [ ] `lake exe mk_all --module` updates barrel import correctly

## Artifacts & Outputs

- `Cslib/Computability/Automata/NA/BuchiCompl.lean` - new file with complement construction and correctness
- `specs/250_nba_complementation/plans/01_nba-complement.md` - this plan
- `specs/250_nba_complementation/summaries/01_nba-complement-summary.md` - post-implementation summary

## Rollback/Contingency

- If Phase 4 (completeness) proves intractable, the task delivers Phases 1-3 as a partial result with `proof_wanted` on the completeness direction. The soundness direction alone is useful: it guarantees that any word accepted by the complement is genuinely rejected by the original, which suffices for sound (but incomplete) language inclusion checking.
- If dependent-type issues with `Fin (2*n+1)` are severe, fall back to `Nat`-valued rankings with a separate `h_bounded : forall s, ranking s <= 2*n` hypothesis.
- If the file grows beyond ~500 lines, extract run DAG definitions and lemmas into a separate `NA/RunDAG.lean` file.
- Git revert to the commit before Phase 1 if the entire approach needs rethinking.
