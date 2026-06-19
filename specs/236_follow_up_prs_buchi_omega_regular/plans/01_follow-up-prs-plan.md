# Implementation Plan: Task #236

- **Task**: 236 - Complete follow-up PRs from PR #649 for Buchi automata and closure of omega-regular languages under boolean operations
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: None (PR #649 content is already on main)
- **Research Inputs**: specs/236_follow_up_prs_buchi_omega_regular/reports/01_follow-up-prs-research.md
- **Artifacts**: plans/01_follow-up-prs-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This task implements three follow-up PRs identified in the PR #649 review discussion. PR 1 decouples the LTL module from the Temporal module by moving `Formula.toTemporal` to a dedicated embedding file. PR 2 bridges LTL satisfaction to the existing `LTS.OmegaExecution` infrastructure via a labeling function. PR 3 proves the main theorem: every LTL formula defines an omega-regular language (the Vardi-Wolper direction), using structural induction and the existing boolean closure results in `OmegaRegularLanguage.lean`.

### Research Integration

The research report identified that:
- Boolean closure results for omega-regular languages are already complete in CSLib (`IsRegular.sup`, `IsRegular.compl`, etc.)
- The Buchi automata library (NBA intersection, union, concatenation, loop) is mature
- The `toTemporal` embedding is the sole source of the `LTL -> Temporal` import dependency
- `ωLanguage.IsRegular` is defined as the existence of a finite-state NBA accepting the language
- The alphabet type mismatch between `Satisfies` (uses `v : N -> (Atom -> Prop)`) and `IsRegular` (uses `ωSequence Symbol`) must be bridged using `Set Atom` with `[Fintype Atom]`
- The `until` case can leverage existing closure results via a fixed-point characterization rather than requiring the full Vardi-Wolper tableau construction
- McNaughton's theorem and Encodable/Countable instances are out of scope

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task does not directly advance the BimodalLogic porting roadmap. It extends the LTL module (introduced via PR #649) toward the automata-theoretic framework in `Cslib/Computability/`.

## Goals & Non-Goals

**Goals**:
- Decouple `LTL/Syntax/Formula.lean` from `Temporal/Syntax/Formula.lean` by extracting the embedding
- Bridge LTL satisfaction to `LTS.OmegaExecution` via a labeling function
- Prove that the language of every LTL formula (with finite atom set) is omega-regular
- Each phase produces a self-contained, separately submittable PR

**Non-Goals**:
- McNaughton's theorem (`proof_wanted IsRegular.iff_da_muller`) -- separate task
- Encodable/Countable/Denumerable instances for `Formula` -- deferred to completeness work
- Full Vardi-Wolper tableau construction (use fixed-point approach instead)
- Deterministic Buchi automata constructions

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `until` case requires complex NBA construction beyond closure results | H | M | Use fixed-point characterization: `phi U psi = psi or (phi and X(phi U psi))`; if this fails, mark Phase 3 as PARTIAL and defer the `until` case |
| Alphabet type bridging between `Atom -> Prop` and `Set Atom` introduces universe issues | M | M | Use `[Fintype Atom]` assumption and explicit `Set.indicator`/membership conversion; follow pattern from existing `IsRegular` proofs |
| `next` operator shift construction may need new NBA primitives | M | L | The shift of an omega-regular language by 1 step is omega-regular; construct a 2-state NBA that reads and discards the first symbol |
| `toTemporal` extraction breaks downstream imports | L | L | Only `Satisfies.lean` imports `Formula.lean`; no other file uses `toTemporal` directly; verify with `lake build` after extraction |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: LTL/Temporal Decoupling [COMPLETED]

**Goal**: Move `Formula.toTemporal` from `LTL/Syntax/Formula.lean` to a new `LTL/Embedding.lean`, removing the transitive dependency of `LTL/` on `Temporal/`.

**Tasks**:
- [ ] Create `Cslib/Logics/LTL/Embedding.lean` with the copyright header and module declaration
- [ ] Move the `Formula.toTemporal` definition (lines 129-140 of `Formula.lean`) and its docstring to `Embedding.lean`
- [ ] Add `import Cslib.Logics.LTL.Syntax.Formula` and `import Cslib.Logics.Temporal.Syntax.Formula` to `Embedding.lean`
- [ ] Remove `public import Cslib.Logics.Temporal.Syntax.Formula` from `LTL/Syntax/Formula.lean`
- [ ] Remove the `toTemporal` definition and docstring from `LTL/Syntax/Formula.lean`
- [ ] Remove the `toTemporal` mention from the module docstring in `Formula.lean`
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean` barrel import
- [ ] Run `lake build Cslib.Logics.LTL.Embedding` to verify
- [ ] Run `lake build` for full project verification
- [ ] Run `lake exe checkInitImports` to verify all files import `Cslib.Init`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Syntax/Formula.lean` -- remove `toTemporal` definition and Temporal import
- `Cslib/Logics/LTL/Embedding.lean` -- new file with `toTemporal` embedding

**Files to update (generated)**:
- `Cslib.lean` -- add `Cslib.Logics.LTL.Embedding` entry

**Verification**:
- `lake build Cslib.Logics.LTL.Syntax.Formula` compiles without Temporal import
- `lake build Cslib.Logics.LTL.Embedding` compiles with `toTemporal` definition
- `lake build` succeeds (no downstream breakage)
- `lake exe checkInitImports` passes

---

### Phase 2: LTL Satisfaction over OmegaExecution [COMPLETED]

**Goal**: Define LTL satisfaction over `LTS.OmegaExecution` pairs via a labeling function, and prove equivalence with the existing `Satisfies` definition.

**Tasks**:
- [ ] Create `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` with copyright header
- [ ] Import `Cslib.Logics.LTL.Semantics.Satisfies` and `Cslib.Foundations.Semantics.LTS.OmegaExecution`
- [ ] Define `SatisfiesExec` that lifts `Satisfies` through a labeling function:
  ```lean
  def SatisfiesExec (labeling : State -> (Atom -> Prop))
      (ss : ωSequence State) (i : ℕ) (φ : Formula Atom) : Prop :=
    Satisfies (fun n => labeling (ss n)) i φ
  ```
- [ ] Prove `satisfiesExec_iff`: `SatisfiesExec` agrees with `Satisfies` when `v = labeling . ss`
- [ ] Prove basic structural lemmas:
  - `satisfiesExec_atom`: atom case unfolds to `labeling (ss i) p`
  - `satisfiesExec_next`: next case unfolds to `SatisfiesExec labeling ss (i+1) φ`
  - `satisfiesExec_untl`: until case unfolds correctly
- [ ] Prove that if `lts.OmegaExecution ss μs` holds, the satisfaction can be stated in terms of the execution
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean`
- [ ] Run `lake build Cslib.Logics.LTL.Semantics.OmegaExecutionSatisfies` to verify
- [ ] Run `lake build` for full project verification
- [ ] Run `lake exe checkInitImports` and `lake exe lint-style`

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` -- new file

**Files to update (generated)**:
- `Cslib.lean` -- add `Cslib.Logics.LTL.Semantics.OmegaExecutionSatisfies` entry

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.OmegaExecutionSatisfies` compiles
- All `SatisfiesExec` lemmas are sorry-free (`lean_verify`)
- `lake build` succeeds
- `lake exe checkInitImports` and `lake exe lint-style` pass

---

### Phase 3: LTL-to-Buchi Translation (Omega-Regularity of LTL) [NOT STARTED]

**Goal**: Prove the main theorem: for every LTL formula `φ` over a finite atom set, the set of omega-words satisfying `φ` is an omega-regular language. This is done by structural induction on `φ`, using existing boolean closure results for the propositional cases and new NBA constructions for `atom`, `next`, and `until`.

**Tasks**:
- [ ] Create `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` with copyright header
- [ ] Import `Cslib.Logics.LTL.Semantics.Satisfies` and `Cslib.Computability.Languages.OmegaRegularLanguage`
- [ ] Define the "LTL language" as an omega-language over `Set Atom`:
  ```lean
  def Formula.omegaLanguage [Fintype Atom] (φ : Formula Atom) : ωLanguage (Set Atom) :=
    ⟨{ v | Satisfies (fun n p => p ∈ v n) 0 φ }⟩
  ```
- [ ] **Atom case**: Prove `(Formula.atom p).omegaLanguage.IsRegular`
  - [ ] Construct a 1-state NBA that accepts `v` iff `p ∈ v 0` at the first step (then accepts everything)
  - [ ] Actually: the atom language is `{v | p ∈ v.head}` which is omega-regular (single letter check followed by arbitrary continuation)
- [ ] **Bot case**: Prove `Formula.bot.omegaLanguage.IsRegular`
  - [ ] The empty language is omega-regular (use `IsRegular.bot`)
- [ ] **Imp case**: Prove `(Formula.imp φ ψ).omegaLanguage.IsRegular` assuming IH
  - [ ] `L(φ -> ψ) = L(φ)^c ∪ L(ψ)`, use `IsRegular.compl` + `IsRegular.sup`
- [ ] **Next case**: Prove `(Formula.next φ).omegaLanguage.IsRegular` assuming IH
  - [ ] `L(Xφ)` is the set of words whose tail (shift by 1) satisfies `φ`
  - [ ] Construct an NBA for "read one symbol, then simulate the NBA for `φ`"
  - [ ] Alternatively: prove that shifting an omega-regular language by 1 yields an omega-regular language
- [ ] **Until case**: Prove `(Formula.untl ψ φ).omegaLanguage.IsRegular` assuming IH
  - [ ] Use the fixed-point characterization or direct NBA construction
  - [ ] The key insight: `φ U ψ` at position 0 means `∃ j ≥ 0, ψ(j) ∧ ∀ k < j, φ(k)`
  - [ ] This can be expressed using the finite union over "ψ holds at position j, φ holds at positions 0..j-1"
  - [ ] The NBA has states tracking whether we are still in the "guard" phase or have reached the "event"
- [ ] State and prove the main theorem:
  ```lean
  theorem Formula.isRegular [Fintype Atom] (φ : Formula Atom) :
      φ.omegaLanguage.IsRegular
  ```
- [ ] Run `lake exe mk_all --module` to update `Cslib.lean`
- [ ] Run `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` to verify
- [ ] Run full CI pipeline: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`

**Timing**: 7 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` -- new file with main theorem

**Files to update (generated)**:
- `Cslib.lean` -- add `Cslib.Logics.LTL.Semantics.OmegaRegular` entry

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` compiles
- Main theorem `Formula.isRegular` is sorry-free (`lean_verify`)
- All case lemmas (atom, bot, imp, next, until) are sorry-free
- `lake build` succeeds
- Full CI pipeline passes: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`

## Testing & Validation

- [ ] `lake build` succeeds after each phase
- [ ] `lake exe checkInitImports` passes (all new files import `Cslib.Init`)
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes (CslibTests suite)
- [ ] No `sorry` in any new file (`lean_verify` on each new theorem)
- [ ] `LTL/Syntax/Formula.lean` no longer imports `Temporal/Syntax/Formula.lean` (Phase 1)
- [ ] `SatisfiesExec` equivalence with `Satisfies` is proved, not assumed (Phase 2)
- [ ] `Formula.isRegular` covers all five constructors of `Formula` (Phase 3)

## Artifacts & Outputs

- `Cslib/Logics/LTL/Embedding.lean` -- LTL-to-Temporal embedding (Phase 1)
- `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` -- OmegaExecution bridge (Phase 2)
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` -- LTL omega-regularity theorem (Phase 3)
- `specs/236_follow_up_prs_buchi_omega_regular/plans/01_follow-up-prs-plan.md` -- this plan

## Rollback/Contingency

Each phase creates new files only (except Phase 1 which modifies `Formula.lean`). Rollback:
- Phase 1: Restore `toTemporal` and Temporal import to `Formula.lean`, delete `Embedding.lean`
- Phase 2: Delete `OmegaExecutionSatisfies.lean`
- Phase 3: If the `until` case proves too complex, mark `Formula.isRegular` with `sorry` for the `untl` case, document the gap as a `proof_wanted`, and submit the partial result as a PR with the remaining cases complete. The `atom`, `bot`, `imp`, and `next` cases are independently valuable.
