# Implementation Plan: Task #251

- **Task**: 251 - Product Construction and Model Checking Reduction
- **Status**: [NOT STARTED]
- **Effort**: 8 hours
- **Dependencies**: Task 248 (completed)
- **Research Inputs**: specs/251_product_construction_model_checking/reports/03_team-research.md
- **Artifacts**: plans/01_product-model-checking.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Implement the synchronous product of an LTS with an NBA and prove the LTL model checking reduction theorem. The product construction takes an arbitrary LTS, a labeling function, and an NBA, producing a new NBA whose language is non-empty iff the LTS has an execution satisfying the NBA's language. The model checking corollary instantiates this with `gnbaNBA (neg phi)` to connect LTL satisfaction (via `SatisfiesExec`) to NBA emptiness (via task 248's `language_nonempty_iff`). Two files are created: a generic product in `Cslib/Foundations/Semantics/LTS/NAProd.lean` (no LTL imports) and the LTL model checking theorem in `Cslib/Logics/LTL/ModelChecking.lean`.

### Research Integration

The team research report (4 teammates) established:

1. **Product definition**: The product `NA.Buchi (S x Q) (Set Atom)` uses "reads source" convention: `Tr (s, q) a (s', q') := (exists mu, lts.Tr s mu s') and nba.Tr q a q'` with `start := init times nba.start`. This convention aligns with `SatisfiesExec` evaluating at `ss.head` (position 0).
2. **Existing products cannot be reused**: Both `iProd` and `FLTS.prod` have structural mismatches (confirmed by Teammate B). A new standalone definition is required.
3. **No task 242 blocking**: `gnbaNBA` and `gnba_language_eq` already exist sorry-free in `GNBA.lean`. The model checking theorem can parameterize over any NBA with the right language hypothesis.
4. **Type bridge needed**: `SatisfiesExec` uses `Atom -> Prop` while `gnbaNBA` uses `Set Atom`. A bridge lemma converting between representations is required.
5. **`[Finite State]` required**: Task 248's `language_nonempty_iff` requires `[Finite State]`, limiting model checking to finite-state systems (standard for algorithmic model checking).
6. **LTS has no initial states**: The `LTS` type has no `start` field; initial states must be parameterized as `init : Set State`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

The ROADMAP.md covers porting BimodalLogic to CSLib and does not contain items related to automata, model checking, or product constructions. No roadmap alignment applies.

## Goals & Non-Goals

**Goals**:
- Define the LTS x NBA synchronous product construction as `NA.Buchi`
- Prove run characterization: product run iff synchronized LTS execution + NBA run
- Prove the model checking reduction: LTS satisfies LTL formula phi iff the product with NBA for neg phi has empty language
- Provide both a generic (parameterized by any NBA) and an LTL-specific (using `gnbaNBA`) version

**Non-Goals**:
- On-the-fly model checking algorithms (separate future task)
- Counterexample extraction from accepting product runs
- `KripkeModel` wrapper type (use explicit parameters instead)
- Categorical abstraction of the product (CSLib uses set-theoretic style)
- CTL* or other temporal logic variants

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `Set Atom` vs `Atom -> Prop` bridge lemmas are non-trivial | M | M | Use `Set.mem_def` and extensionality; research found these are propositionally equal |
| Completeness direction threading through `gnba_language_eq` is complex | H | M | Factor into separate lemma; budget 2 hours for this direction; can leave parameterized version sorry-free and mark unconditional corollary partial |
| `[Finite (S x Q)]` instance may require explicit derivation | L | L | Use `Finite.instProd` from Mathlib (same pattern as `gnbaNBAStateFinite`) |
| Existential quantification over LTS labels in product transition | M | L | Standard pattern; use `exists mu, lts.Tr s mu s'` as in research report |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Product Definition and Basic Infrastructure [IN PROGRESS]

**Goal**: Define the LTS x NBA synchronous product in `NAProd.lean` with run characterization lemmas.

**Tasks**:
- [ ] Create `Cslib/Foundations/Semantics/LTS/NAProd.lean` with module header and imports
- [ ] Define `LTS.naProd`: the product of an LTS with labeling and NBA, producing `NA.Buchi (S x Q) Sigma`
  - Product transition: `Tr (s, q) a (s', q') := (exists mu, lts.Tr s mu s') and nba.Tr q a q'`
  - Start states: `init times nba.start` (Cartesian product of initial LTS states and NBA start states)
  - Accept states: `Set.univ times nba.accept`
  - "Reads source" convention: NBA reads label of source state (`labeling s`)
- [ ] Prove `naProd_run_iff`: product run characterization
  - `(naProd lts labeling init nba).Run xs ss iff exists ss_lts ss_nba, ss = fun n => (ss_lts n, ss_nba n) and (forall n, exists mu, lts.Tr (ss_lts n) mu (ss_lts (n+1))) and nba.Run (fun n => labeling (ss_lts n)) ss_nba and ss_lts 0 in init`
- [ ] Prove `naProd_start_iff`: start state characterization
- [ ] Prove `naProd_accept_iff`: accept state characterization
- [ ] Register the file in `Cslib.lean` via `lake exe mk_all --module`

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Semantics/LTS/NAProd.lean` - New file: product definition and basic lemmas
- `Cslib.lean` - Updated by `lake exe mk_all --module`

**Verification**:
- `lake build Cslib.Foundations.Semantics.LTS.NAProd` succeeds
- No sorries in the file

---

### Phase 2: Soundness Direction (Product to LTL) [NOT STARTED]

**Goal**: Prove the soundness (forward) direction: if the product language is non-empty, then there exists an LTS execution not satisfying phi.

**Tasks**:
- [ ] Prove `naProd_language_nonempty_of_exec`: if there is an LTS omega-execution from `init` whose labeling sequence is accepted by the NBA, then the product language is non-empty
  - Construct: given LTS execution `ss_lts` with `lts.OmegaExecution ss_lts mus` and NBA accepting run on `fun n => labeling (ss_lts n)`, build a product run
  - The product run state sequence is `fun n => (ss_lts n, ss_nba n)`
  - The product input sequence is `fun n => labeling (ss_lts n)`
- [ ] Prove `exec_of_naProd_language_nonempty`: if the product language is non-empty, then there is an LTS omega-execution from `init` whose labeling sequence is in the NBA language
  - Extract: given product accepting run, project onto LTS and NBA components
  - Show projected LTS sequence has valid transitions (from existential in product transition)
  - Show projected NBA sequence is an accepting run
- [ ] Combine into biconditional `naProd_language_nonempty_iff_exec`: product language non-empty iff exists such execution

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Semantics/LTS/NAProd.lean` - Add soundness/completeness lemmas

**Verification**:
- `lake build Cslib.Foundations.Semantics.LTS.NAProd` succeeds
- `naProd_language_nonempty_iff_exec` is sorry-free

---

### Phase 3: LTL Model Checking Reduction [NOT STARTED]

**Goal**: Prove the LTL model checking theorem connecting product emptiness to LTL satisfaction, in `ModelChecking.lean`.

**Tasks**:
- [ ] Create `Cslib/Logics/LTL/ModelChecking.lean` with module header and imports
  - Import `NAProd.lean`, `OmegaExecutionSatisfies.lean`, `GNBA.lean` (for `gnbaNBA`), `Emptiness.lean`
- [ ] Define/prove bridge lemma `satisfiesExec_iff_mem_omegaLanguage`: connect `SatisfiesExec labeling ss phi` to membership in `phi.omegaLanguage` via the `Set Atom` representation
  - Key insight: `labeling : State -> (Atom -> Prop)` can be reinterpreted as `labeling' : State -> Set Atom` via `labeling' s = {p | labeling s p}`
  - Then `SatisfiesExec labeling ss phi iff Satisfies (fun p s => p in s) (fun n => labeling' (ss n)) phi`
- [ ] Prove `ltl_modelChecking_of_nba` (generic, parameterized):
  - Hypotheses: `lts : LTS State Label`, `init : Set State`, `labeling : State -> Set Atom`, `nba : NA.Buchi Q (Set Atom)`, `h_lang : language nba = (Formula.neg phi).omegaLanguage`, `[Finite State]`, `[Finite Q]`, `[Inhabited (Set Atom)]`
  - Conclusion: `(forall s0 in init, forall ss mus, lts.OmegaExecution ss mus -> ss 0 = s0 -> SatisfiesExec (fun s p => p in labeling s) ss phi) iff language (naProd lts labeling init nba) = bot`
  - Strategy: chain `naProd_language_nonempty_iff_exec` with `language_eq_bot_iff` (from Emptiness.lean) and the bridge lemma
- [ ] Register the file in `Cslib.lean`

**Timing**: 2.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/LTL/ModelChecking.lean` - New file: bridge lemmas and model checking theorem
- `Cslib.lean` - Updated by `lake exe mk_all --module`

**Verification**:
- `lake build Cslib.Logics.LTL.ModelChecking` succeeds
- `ltl_modelChecking_of_nba` is sorry-free

---

### Phase 4: LTL Corollary and CI Verification [NOT STARTED]

**Goal**: Prove the unconditional LTL model checking corollary using `gnbaNBA` and pass full CI.

**Tasks**:
- [ ] Prove `ltl_modelChecking` (unconditional corollary):
  - Instantiate `ltl_modelChecking_of_nba` with `nba := gnbaNBA (Formula.neg phi)`
  - Use `gnba_language_eq` to discharge the language hypothesis
  - Requires `[Finite Atom]` (for `gnbaNBAStateFinite`) and `[Finite State]`
  - Statement: `(forall s0 in init, ...) iff language (naProd lts labeling init (gnbaNBA (neg phi))) = bot`
- [ ] Add module docstring to both `NAProd.lean` and `ModelChecking.lean`
- [ ] Run `lake exe checkInitImports` and fix if needed
- [ ] Run `lake exe lint-style` and fix style issues
- [ ] Run `lake test` and verify pass
- [ ] Run `lake build` (full project) for final verification

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/LTL/ModelChecking.lean` - Add unconditional corollary and docstrings
- `Cslib/Foundations/Semantics/LTS/NAProd.lean` - Add docstring

**Verification**:
- `lake build` succeeds (full project)
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes
- No sorries in either file (verified via `lean_verify`)

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Semantics.LTS.NAProd` compiles without errors
- [ ] `lake build Cslib.Logics.LTL.ModelChecking` compiles without errors
- [ ] `lake build` (full project) compiles without errors
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] `lean_verify` confirms no `sorry` axioms in key theorems: `naProd_language_nonempty_iff_exec`, `ltl_modelChecking_of_nba`, `ltl_modelChecking`

## Artifacts & Outputs

- `Cslib/Foundations/Semantics/LTS/NAProd.lean` - Generic LTS x NBA product construction
- `Cslib/Logics/LTL/ModelChecking.lean` - LTL model checking reduction theorem
- `specs/251_product_construction_model_checking/plans/01_product-model-checking.md` - This plan
- `specs/251_product_construction_model_checking/summaries/01_product-model-checking-summary.md` - Implementation summary (upon completion)

## Rollback/Contingency

Both new files (`NAProd.lean`, `ModelChecking.lean`) are additive -- they do not modify any existing files. Rollback consists of deleting these two files and re-running `lake exe mk_all --module` to remove their entries from `Cslib.lean`. No existing proofs depend on these files, so removal has zero impact on the rest of the codebase.

If the completeness direction (Phase 3) proves too complex, the generic parameterized theorem `ltl_modelChecking_of_nba` can be stated and the proof of the NBA-language hypothesis deferred to a follow-up task. The product definition and run characterization (Phases 1-2) have standalone value regardless.
