# Implementation Plan: Task #236 (Revised -- untl Case Focus)

- **Task**: 236 - Complete follow-up PRs from PR #649 for Buchi automata and closure of omega-regular languages under boolean operations
- **Status**: [IN PROGRESS]
- **Effort**: 14 hours (2h completed + 12h remaining)
- **Dependencies**: None (PR #649 content is already on main)
- **Research Inputs**:
  - specs/236_follow_up_prs_buchi_omega_regular/reports/01_follow-up-prs-research.md
  - specs/236_follow_up_prs_buchi_omega_regular/reports/02_untl-case-research.md
- **Artifacts**: plans/02_untl-case-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This revised plan incorporates findings from the untl case research (report 02). Phases 1 and 2 are complete: LTL/Temporal decoupling and LTL satisfaction over OmegaExecution. Phase 3 (LTL-to-Buchi translation) has 4 of 5 cases proved (atom, bot, imp, next) with the `untl` case remaining as `proof_wanted`. The revised plan decomposes the `untl` case into three focused sub-phases based on research recommendations: proving the semantic equation, constructing a custom NBA, and deriving the final regularity result.

### Research Integration

Reports integrated:
- `01_follow-up-prs-research.md` -- Original research on three follow-up PRs (integrated in plan v01)
- `02_untl-case-research.md` -- Research on the `untl` case, analyzing four proof approaches and recommending direct NBA construction (Approach A) with a phased decomposition via the semantic equation

### Prior Plan Reference

plans/01_follow-up-prs-plan.md (original 3-phase plan; Phases 1-2 completed, Phase 3 partially completed with atom/bot/imp/next done)

### Convention Note

The code uses **standard LTL convention** (not Burgess):
- `untl phi psi` = `phi U psi` where `phi` = guard (intermediate), `psi` = event (witness)
- In the Lean pattern match: `.untl psi phi => exists j >= i, Satisfies v j phi /\ forall k, i <= k -> k < j -> Satisfies v k psi` (binders shadow: `psi` = first arg = guard, `phi` = second arg = event)
- Reflexive: `j >= i` (j = i is allowed, meaning the event can hold immediately with vacuous guard)
- `someFuture phi = .untl .top phi` confirms: guard = top, event = phi

## Goals & Non-Goals

**Goals**:
- Prove the semantic equation `omegaLanguage_untl` expressing the untl language in terms of `drop` and sub-formula languages
- Construct `untlNBA` whose language equals the until language
- Prove `isRegular_untl` and remove the `sorry` from `Formula.isRegular`

**Non-Goals**:
- McNaughton's theorem (`proof_wanted IsRegular.iff_da_muller`) -- separate task
- Encodable/Countable/Denumerable instances for `Formula` -- deferred
- Full Vardi-Wolper tableau construction (use direct NBA construction instead)
- Deterministic Buchi automata constructions
- Optimizing NBA state space (correctness over minimality)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Guard verification in NBA requires tracking acceptance of multiple simultaneous runs | H | M | Use the concat-based approach (Sub-approach A2 from research): reduce to FinAcc for guard prefixes + concat with na_psi; alternatively use interNA toggle mechanism for dual acceptance |
| NBA correctness proof is lengthy (hundreds of lines) | M | H | Decompose into small lemmas; prove semantic equation first (Phase 3a) as independent value; accept sorry for NBA language_eq if needed |
| State space complexity (exponential in guard NBA states) | M | M | Accept exponential state space for correctness; the construction only needs finiteness, not efficiency |
| Type universe issues with Finset/Set conversions | L | M | Follow existing patterns from atomNBA and nextNBA; use `[Finite Atom]` and `[Fintype S]` consistently |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3a | 2 |
| 4 | 3b | 3a |
| 5 | 3c | 3a, 3b |

Phases within the same wave can execute in parallel.

---

### Phase 1: LTL/Temporal Decoupling [COMPLETED]

**Goal**: Move `Formula.toTemporal` from `LTL/Syntax/Formula.lean` to a new `LTL/Embedding.lean`, removing the transitive dependency of `LTL/` on `Temporal/`.

**Tasks**:
- [x] Create `Cslib/Logics/LTL/Embedding.lean` with `toTemporal` embedding
- [x] Remove `toTemporal` and Temporal import from `LTL/Syntax/Formula.lean`
- [x] Verify `lake build` and `lake exe checkInitImports`

**Timing**: 1 hour

**Depends on**: none

**Files modified**:
- `Cslib/Logics/LTL/Syntax/Formula.lean`
- `Cslib/Logics/LTL/Embedding.lean` (new)

---

### Phase 2: LTL Satisfaction over OmegaExecution [COMPLETED]

**Goal**: Define LTL satisfaction over `LTS.OmegaExecution` pairs via a labeling function, and prove equivalence with the existing `Satisfies` definition.

**Tasks**:
- [x] Create `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean`
- [x] Define `SatisfiesExec` and prove equivalence with `Satisfies`
- [x] Verify `lake build`, `lake exe checkInitImports`, `lake exe lint-style`

**Timing**: 2 hours

**Depends on**: 1

**Files modified**:
- `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` (new)

---

### Phase 3: LTL-to-Buchi Translation -- Completed Cases [COMPLETED]

The following cases of `Formula.isRegular` are proved in `Cslib/Logics/LTL/Semantics/OmegaRegular.lean`:

- **atom**: `isRegular_atom` via `atomNBA` (1-state NBA checking `p in v 0`)
- **bot**: `isRegular_bot` via `IsRegular.bot` (empty language)
- **imp**: `isRegular_imp` via `IsRegular.compl` + `IsRegular.sup` (boolean closure)
- **next**: `isRegular_next` via `nextNBA` (shift-by-1 construction)

The main theorem `Formula.isRegular` uses `sorry` only for the `untl` case (via `proof_wanted Formula.isRegular_untl`).

**Files modified**:
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` (new, with `proof_wanted` for untl)

---

### Phase 3a: Semantic Equation for untl [IN PROGRESS]

**Goal**: Prove `omegaLanguage_untl` expressing the until language in terms of `Stream.drop` and sub-formula omega-languages. This establishes the mathematical foundation for the NBA construction.

**Tasks**:
- [ ] Prove the semantic equation:
  ```lean
  theorem omegaLanguage_untl [Finite Atom] (phi psi : Formula Atom) :
      (Formula.untl phi psi).omegaLanguage =
        ⟨{ v | ∃ j, v.drop j ∈ psi.omegaLanguage ∧
          ∀ k, k < j → v.drop k ∈ phi.omegaLanguage }⟩
  ```
  Note: `phi` = guard (first arg), `psi` = event (second arg) in `untl phi psi`. The existential `j` is the witness position where the event `psi` holds. For `j = 0`, the guard condition is vacuously true.
- [ ] The proof should use `satisfies_shift` to convert between positional satisfaction (`Satisfies v j psi`) and suffix-based membership (`v.drop j in psi.omegaLanguage`)
- [ ] Key steps: unfold `omegaLanguage` and `Satisfies` for the untl pattern, apply `ext` for set equality, use `satisfies_shift` in both directions
- [ ] Verify the lemma compiles: `lean_verify` on `omegaLanguage_untl`

**Timing**: 2 hours

**Depends on**: 2 (requires `satisfies_shift` and `omegaLanguage` definitions from Phase 3 completed work)

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` -- add `omegaLanguage_untl` theorem

**Verification**:
- `lean_goal` at proof site shows no remaining goals
- `lean_verify` on `omegaLanguage_untl` passes (no sorry)
- `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` compiles

---

### Phase 3b: Construct untlNBA and Prove Language Equality [NOT STARTED]

**Goal**: Build a nondeterministic Buchi automaton `untlNBA` whose accepted language equals the until language `(Formula.untl phi psi).omegaLanguage`, following the direct NBA construction approach recommended by the research.

**Tasks**:
- [ ] Define `untlNBA` given NBAs `na_phi` (for guard language) and `na_psi` (for event language)
- [ ] Choose construction approach (ordered by preference):
  1. **Concat-based (Sub-approach A2)**: Use existing `NA.concat` to combine a finite acceptor for guard prefixes with `na_psi`; leverages `concat_language_eq`
  2. **Product with mode flag**: States = `S_phi x S_psi x Bool` (guard/event mode); nondeterministic switch from guard to event; accept in event mode via `na_psi` acceptance; use `interNA` for dual acceptance checking
  3. **Power-set tracking**: States = `Finset (S_phi x Bool) x Option S_psi`; tracks multiple simultaneous guard runs with acceptance flags
- [ ] Prove `untlNBA_language_eq`:
  ```lean
  theorem untlNBA_language_eq [Finite Atom] {na_phi na_psi : NA (Set Atom) S_phi S_psi}
      (h_phi : na_phi.Buchi.language = phi.omegaLanguage)
      (h_psi : na_psi.Buchi.language = psi.omegaLanguage) :
      (untlNBA na_phi na_psi).Buchi.language = (Formula.untl phi psi).omegaLanguage
  ```
  The proof has two directions:
  - **Soundness** (NBA accepts => word satisfies untl): Extract the nondeterministic guess of event position `j` from the accepting run; show guard holds at each `k < j` and event holds at `j`
  - **Completeness** (word satisfies untl => NBA accepts): Given witness `j`, construct an accepting run that simulates `na_phi` in guard mode for steps `0..j-1` and `na_psi` in event mode from step `j` onward
- [ ] The language equality may use `omegaLanguage_untl` from Phase 3a to rewrite the right-hand side
- [ ] Follow the pattern of `atomNBA_language_eq` and `nextNBA_language_eq` in the existing file
- [ ] Verify: `lean_verify` on `untlNBA_language_eq` passes

**Timing**: 8 hours

**Depends on**: 3a

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` -- add `untlNBA` definition and `untlNBA_language_eq`

**Existing primitives to consider**:
- `NA.concat` / `concat_language_eq` (from `NA/Concat.lean`)
- `interNA` / `inter_language_eq` (from `NA/BuchiInter.lean`) for dual acceptance
- `NA.addHist` (from `NA/Hist.lean`) for state tracking
- `NA.Buchi.reindex` (from `NA/BuchiEquiv.lean`) for state space transformations
- `frequently_atTop` for Buchi acceptance conditions

**Verification**:
- `lean_goal` at proof site shows no remaining goals
- `lean_verify` on `untlNBA_language_eq` passes (no sorry)
- `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` compiles

---

### Phase 3c: Derive isRegular_untl and Remove sorry [NOT STARTED]

**Goal**: Prove `Formula.isRegular_untl` using the NBA from Phase 3b, then remove the `sorry` from the main `Formula.isRegular` theorem.

**Tasks**:
- [ ] Prove `isRegular_untl`:
  ```lean
  theorem Formula.isRegular_untl [Finite Atom] {phi psi : Formula Atom}
      (h_phi : phi.omegaLanguage.IsRegular) (h_psi : psi.omegaLanguage.IsRegular) :
      (Formula.untl phi psi).omegaLanguage.IsRegular
  ```
  The proof extracts NBAs from `h_phi` and `h_psi` (via `IsRegular` definition = existence of finite-state NBA), constructs `untlNBA`, and uses `untlNBA_language_eq` to show the constructed NBA accepts the correct language.
- [ ] Replace `proof_wanted Formula.isRegular_untl` with the actual theorem
- [ ] Update `Formula.isRegular` to use `isRegular_untl` instead of `sorry` in the `untl` case
- [ ] Run full CI pipeline:
  - `lake build Cslib.Logics.LTL.Semantics.OmegaRegular`
  - `lake build` (full project)
  - `lake test`
  - `lake exe checkInitImports`
  - `lake exe lint-style`
- [ ] Verify `Formula.isRegular` is sorry-free: `lean_verify` on `Formula.isRegular`

**Timing**: 2 hours

**Depends on**: 3a, 3b

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` -- replace `proof_wanted` with theorem, update `isRegular`

**Verification**:
- `lean_verify` on `Formula.isRegular_untl` passes (no sorry)
- `lean_verify` on `Formula.isRegular` passes (no sorry, all five cases covered)
- Full CI pipeline passes: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`

## Testing & Validation

- [ ] `lake build` succeeds after each sub-phase
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes (CslibTests suite)
- [ ] No `sorry` in `OmegaRegular.lean` after Phase 3c (`lean_verify` on all theorems)
- [ ] `Formula.isRegular` covers all five constructors: atom, bot, imp, next, untl
- [ ] `omegaLanguage_untl` correctly reflects standard convention (phi = guard, psi = event)

## Artifacts & Outputs

- `Cslib/Logics/LTL/Embedding.lean` -- LTL-to-Temporal embedding (Phase 1, completed)
- `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` -- OmegaExecution bridge (Phase 2, completed)
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` -- LTL omega-regularity theorem (Phases 3/3a/3b/3c)
- `specs/236_follow_up_prs_buchi_omega_regular/plans/01_follow-up-prs-plan.md` -- original plan (v01)
- `specs/236_follow_up_prs_buchi_omega_regular/plans/02_untl-case-plan.md` -- this revised plan (v02)

## Rollback/Contingency

- **Phase 3a**: If `omegaLanguage_untl` cannot be proved, check whether `satisfies_shift` requires additional hypotheses not currently available. The equation is standard and should follow from the definitions.
- **Phase 3b**: If the full NBA construction + language equality proof exceeds scope:
  - Mark `untlNBA_language_eq` with `sorry` and document the gap
  - The semantic equation from Phase 3a is independently valuable
  - Consider deferring to `proof_wanted` with a more specific statement
- **Phase 3c**: Depends entirely on 3a + 3b; if those succeed, this phase is mechanical
- **Overall fallback**: Keep `proof_wanted Formula.isRegular_untl` with the existing `sorry`. The four completed cases (atom, bot, imp, next) plus the semantic equation are independently valuable contributions.
