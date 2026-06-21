# Implementation Plan: Task #254

- **Task**: 254 - Revise LTL conventions to standard semantics
- **Status**: [COMPLETED]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: specs/254_revise_ltl_conventions_standard_semantics/reports/01_team-research.md
- **Artifacts**: plans/01_revise-ltl-conventions.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Revise LTL files on main to conform to the standard semantic definitions adopted in
feat/temporal-formula-propositional (commit 3e147123). The changes span three files
directly modified by the reference commit plus one file requiring docstring-only updates and
three downstream files that depend on the old Satisfies API. Research confirmed that the
`untl` argument order is identical across branches (first=guard, second=event); only
docstrings and notation symbols change in Formula.lean. Connectives.lean changes are
**additive only** -- existing classes (HasSince, HasBox, ModalConnectives,
TemporalConnectives, BimodalConnectives) must be preserved because they are used by
Modal, Temporal, and Bimodal modules. The Satisfies.lean rewrite to `ωSequence State`
is the highest-risk change, cascading into OmegaExecutionSatisfies.lean (108 lines),
OmegaRegular.lean (404 lines), and GNBA.lean (1423 lines).

### Research Integration

Key findings from team research (01_team-research.md):
1. The `untl` argument order does NOT change in code -- only docstrings are corrected
2. Connectives.lean must be additive, not subtractive -- removing HasSince/TemporalConnectives/BimodalConnectives would break Modal, Temporal, and Bimodal modules
3. Satisfies.lean rewrite cascades into 3 downstream files totaling ~1935 lines
4. Notation changes (U->𝓤, X->◯, 𝐅->◇, 𝐆->□) are safe with scoped declarations but 𝓤 has latent risk with Mathlib's uniformity symbol
5. Scope is LTL-only -- must not touch Modal, Temporal, or Bimodal modules

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task aligns with the CSLib modular architecture roadmap: it standardizes LTL notation and semantics independently of the Temporal/Bimodal/Modal hierarchy, maintaining clean module boundaries.

## Goals & Non-Goals

**Goals**:
- Update Formula.lean notation symbols from Burgess convention (X/U/𝐅/𝐆) to standard convention (◯/𝓤/◇/□)
- Add leadsto (⇝) abbreviation and update all docstrings to standard convention labels
- Update Connectives.lean docstrings to remove forward references; keep all existing classes
- Rewrite Satisfies.lean to use `ωSequence State` with valuation `v : Atom → State → Prop`
- Update OmegaExecutionSatisfies.lean bridge definitions for new Satisfies API
- Update OmegaRegular.lean and GNBA.lean for new Satisfies API
- Update Embedding.lean docstrings
- Verify full build passes after all changes

**Non-Goals**:
- Removing HasSince, HasBox, ModalConnectives, TemporalConnectives, or BimodalConnectives from Connectives.lean
- Modifying Modal, Temporal, or Bimodal modules
- Changing ProofSystem.lean or Axioms.lean
- Adding BaierKatoen2008 to references.bib (deferred)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Satisfies API change breaks GNBA.lean (41 refs, 1423 lines) | H | H | Phase 3 is dedicated to GNBA; incremental build verification after each file |
| OmegaRegular.lean satisfies_shift lemma requires major rewrite | M | H | The ωSequence `drop` operation may simplify the shift lemma; incremental approach |
| 𝓤 notation conflicts with Mathlib uniformity | L | L | Both are scoped; only matters if both namespaces opened simultaneously |
| Embedding.lean untl mapping breaks with new convention | M | L | Embedding maps LTL untl to Temporal reflexiveUntl; argument positions unchanged |
| OmegaExecutionSatisfies bridge breaks with new API | M | H | Bridge must be redesigned; may simplify since ωSequence is already used |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |
| 3 | 4 | 3 |
| 4 | 5 | 3 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Formula.lean notation + docstrings + leadsto [COMPLETED]

**Goal**: Update Formula.lean to match feature branch: standard notation symbols, corrected docstrings, leadsto abbreviation.

**Tasks**:
- [ ] Update module docstring: remove Burgess references, change notation table (U->𝓤, X->◯, 𝐅->◇, 𝐆->□), add ⇝ entry, update someFuture description to `⊤ U φ`
- [ ] Update Derived Operators section: change from Burgess convention description to standard convention (first=guard, second=event)
- [ ] Remove Burgess references from References section (keep Pnueli, Kamp, Vardi-Wolper)
- [ ] Update untl constructor docstring from `(Burgess: event U guard)` to `(guard U event: φ₁ holds until φ₂)`
- [ ] Update someFuture docstring from `F φ := φ U ⊤` to `◇φ := ⊤ U φ` with standard explanation
- [ ] Update allFuture docstring to use □ symbol
- [ ] Add `Formula.leadsto` abbreviation: `p ⇝ q := □(p → ◇q)`
- [ ] Replace notation declarations: `U` -> `𝓤`, `X` -> `◯`, `𝐅` -> `◇`, `𝐆` -> `□`
- [ ] Add `⇝` notation declaration (infix, priority 20)
- [ ] Build verification: `lake build Cslib.Logics.LTL.Syntax.Formula`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Syntax/Formula.lean` - notation symbols, docstrings, leadsto abbreviation

**Verification**:
- `lake build Cslib.Logics.LTL.Syntax.Formula` succeeds
- All notation symbols match feature branch (◯/𝓤/◇/□/⇝)
- No Burgess convention references remain in docstrings

---

### Phase 2: Connectives.lean docstring update [COMPLETED]

**Goal**: Update FutureTemporalConnectives docstring to remove forward reference to nonexistent TemporalConnectives, matching feature branch commit.

**Tasks**:
- [ ] Update FutureTemporalConnectives docstring: replace three-line description referencing TemporalConnectives with two-line version from feature branch
- [ ] Update module-level docstring: remove references to HasSince, ModalConnectives, TemporalConnectives, BimodalConnectives from the Atomic/Bundled classes lists (since these are NOT in the feature branch's simplified hierarchy, but they still exist in the file -- only update the docstring for FutureTemporalConnectives)
- [ ] Build verification: `lake build Cslib.Foundations.Logic.Connectives`

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - FutureTemporalConnectives docstring only

**Verification**:
- `lake build Cslib.Foundations.Logic.Connectives` succeeds
- FutureTemporalConnectives docstring no longer references TemporalConnectives
- All existing classes (HasSince, HasBox, ModalConnectives, TemporalConnectives, BimodalConnectives) are preserved unchanged

---

### Phase 3: Satisfies.lean rewrite to ωSequence State [COMPLETED]

**Goal**: Rewrite Satisfies.lean to use `ωSequence State` with valuation `v : Atom → State → Prop` instead of `ℕ → (Atom → Prop)` with parameter `i`, matching the feature branch exactly.

**Tasks**:
- [ ] Add `public import Cslib.Foundations.Data.OmegaSequence.Init` to imports
- [ ] Update module docstring: replace `ℕ → (Atom → Prop)` description with `ωSequence State` + valuation description
- [ ] Update main definitions section: `Satisfies v w φ`, `Valid v φ`, `Satisfiable φ` signatures
- [ ] Update variable declaration from `{Atom : Type*}` to `{Atom State : Type*}`
- [ ] Rewrite `Satisfies` definition:
  - Type: `(v : Atom → State → Prop) (w : ωSequence State) : Formula Atom → Prop`
  - `.atom p => v p w.head`
  - `.bot => False`
  - `.imp φ ψ => Satisfies v w φ → Satisfies v w ψ`
  - `.next φ => Satisfies v w.tail φ`
  - `.untl φ ψ => ∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ`
- [ ] Update `Satisfies` docstring: remove Burgess references, use standard convention labels
- [ ] Rewrite `Valid` definition to use `∀ (w : ωSequence State), Satisfies v w φ`
- [ ] Rewrite `Satisfiable` definition to use `∃ (v : ...) (w : ωSequence State), Satisfies v w φ`
- [ ] Build verification: `lake build Cslib.Logics.LTL.Semantics.Satisfies`

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` - complete rewrite of Satisfies/Valid/Satisfiable

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.Satisfies` succeeds
- Satisfies uses `ωSequence State` with `v : Atom → State → Prop`
- No ℕ-indexed valuation remains

---

### Phase 4: OmegaExecutionSatisfies.lean update [COMPLETED]

**Goal**: Update the OmegaExecutionSatisfies bridge module to work with the new ωSequence-based Satisfies API.

**Tasks**:
- [ ] Analyze how `SatisfiesExec` currently wraps old `Satisfies (fun n => labeling (ss n)) i φ`
- [ ] Redesign `SatisfiesExec` for new API: the labeling function `labeling : State → (Atom → Prop)` combined with `ss : ωSequence State` should produce valuation `v : Atom → State → Prop` where `v p s = labeling s p`
- [ ] Rewrite `SatisfiesExec` definition: `SatisfiesExec labeling ss φ := Satisfies (fun p s => labeling s p) ss φ` (no `i` parameter since new Satisfies evaluates at head)
- [ ] Update all unfolding theorems: `satisfiesExec_iff`, `satisfiesExec_atom`, `satisfiesExec_bot`, `satisfiesExec_imp`, `satisfiesExec_next`, `satisfiesExec_untl`
- [ ] Update `satisfiesExec_of_val_eq` bridge theorem
- [ ] Update module docstring to reflect ωSequence-based API
- [ ] Build verification: `lake build Cslib.Logics.LTL.Semantics.OmegaExecutionSatisfies`

**Timing**: 1.0 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` - bridge definition and theorems

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.OmegaExecutionSatisfies` succeeds
- SatisfiesExec works with new ωSequence-based Satisfies
- All unfolding theorems type-check

---

### Phase 5: OmegaRegular.lean + GNBA.lean update [IN PROGRESS]

**Goal**: Update OmegaRegular.lean and GNBA.lean to work with the new ωSequence-based Satisfies API. This is the highest-risk phase due to the volume of references (22 in OmegaRegular, 41 in GNBA).

**Tasks**:
- [ ] Update `Formula.omegaLanguage` definition in OmegaRegular.lean to use new Satisfies API
- [ ] Rewrite `satisfies_shift` lemma for ωSequence (may simplify: shifting an ωSequence by `drop k` is more natural than index arithmetic)
- [ ] Update `mem_omegaLanguage` simp lemma
- [ ] Update all `isRegular_*` proofs that reference Satisfies
- [ ] Update `omegaLanguage_drop` and related helper lemmas
- [ ] Update GNBA.lean `canonicalAtom` definition: currently `{ ψ ∈ cl(φ) | Satisfies v i ψ }` -- adapt to ωSequence API
- [ ] Update all GNBA proof references to Satisfies (41 occurrences)
- [ ] Build verification: `lake build Cslib.Logics.LTL.Semantics.OmegaRegular`

**Timing**: 2.0 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` - omega language definitions and shift lemma
- `Cslib/Logics/LTL/Semantics/GNBA.lean` - canonicalAtom and all Satisfies references

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` succeeds
- `lake build Cslib.Logics.LTL.Semantics.GNBA` succeeds
- All omega-regularity proofs pass with new Satisfies API

---

### Phase 6: Embedding.lean docstrings + full build + CI [IN PROGRESS]

**Goal**: Update Embedding.lean docstrings and run full project build and CI pipeline.

**Tasks**:
- [ ] Update Embedding.lean module docstring: replace Burgess convention references with standard convention labels
- [ ] Update `satisfiesExec_untl` theorem docstring if it references Burgess
- [ ] Update `Formula.toTemporal` docstring: describe mapping in terms of standard convention
- [ ] Run `lake build` (full project build)
- [ ] Run `lake exe checkInitImports`
- [ ] Run `lake exe lint-style`
- [ ] Run `lake test`

**Timing**: 0.75 hours

**Depends on**: 4, 5

**Files to modify**:
- `Cslib/Logics/LTL/Embedding.lean` - docstring updates only

**Verification**:
- Full `lake build` succeeds
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes
- No Burgess convention references remain in LTL module docstrings

## Testing & Validation

- [ ] `lake build Cslib.Logics.LTL.Syntax.Formula` succeeds after Phase 1
- [ ] `lake build Cslib.Foundations.Logic.Connectives` succeeds after Phase 2
- [ ] `lake build Cslib.Logics.LTL.Semantics.Satisfies` succeeds after Phase 3
- [ ] `lake build Cslib.Logics.LTL.Semantics.OmegaExecutionSatisfies` succeeds after Phase 4
- [ ] `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` succeeds after Phase 5
- [ ] Full `lake build` succeeds after Phase 6
- [ ] All CI checks pass: checkInitImports, lint-style, test

## Artifacts & Outputs

- `specs/254_revise_ltl_conventions_standard_semantics/plans/01_revise-ltl-conventions.md` (this plan)
- `specs/254_revise_ltl_conventions_standard_semantics/summaries/01_execution-summary.md` (after implementation)
- Modified files: Formula.lean, Connectives.lean, Satisfies.lean, OmegaExecutionSatisfies.lean, OmegaRegular.lean, GNBA.lean, Embedding.lean

## Rollback/Contingency

All changes are on main branch with git commits per phase. If any phase fails:
- `git revert` the failing phase commit to restore previous state
- If Phase 5 (GNBA/OmegaRegular) proves intractable, fallback option: remove those three downstream files from `Cslib.lean` barrel imports (matching the feature branch approach) and create follow-up tasks for their ωSequence port
- If the notation change 𝓤 causes Mathlib conflicts in downstream code, revert to `U` notation and document the conflict
