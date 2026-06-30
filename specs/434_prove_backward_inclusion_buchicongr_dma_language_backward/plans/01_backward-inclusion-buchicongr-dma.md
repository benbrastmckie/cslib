# Implementation Plan: Task #434

- **Task**: 434 - prove_backward_inclusion_buchicongr_dma_language_backward
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: None (independent of forward direction; parent task 241)
- **Research Inputs**: Task description (self-contained API map); spawn analysis `specs/241_mcnaughton_theorem/reports/03_spawn-analysis.md`; orchestrator handoff `specs/241_mcnaughton_theorem/.orchestrator-handoff.json`
- **Artifacts**: plans/01_backward-inclusion-buchicongr-dma.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, cslib.md, lean4.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Prove the backward inclusion `buchiCongr_DMA_language_backward : language (buchiCongr_DMA na) ⊆ language na` as a new `private lemma` in `Cslib/Computability/Languages/OmegaRegularLanguage.lean`, placed immediately after `buchiCongr_DMA_language_forward` (~line 446) and before `proof_wanted buchiCongr_DMA_language_eq` (line 460). The proof unfolds the Muller acceptance condition into accept-set membership, destructures the accept witness `(b ∈ infOcc, a, ys)`, establishes that `xs` itself lies in `buchiFamily (a, b)`, and then applies `buchiFamily_saturation` to conclude `xs ∈ language na`. This direction is independent of the Ramsey/recurrence argument used by the forward lemma and can land in its own committed dispatch.

### Research Integration

The task description is the research artifact and supplies the complete API map. The parent task 241 orchestrator handoff (`.orchestrator-handoff.json`) corroborates every anchor used here:

- **DA.Muller language**: `language da xs ↔ (da.run xs).infOcc ∈ da.accept` (DA/Basic.lean:117); unfolded in the file via `rw [ωAcceptor.mem_language]` + `simp only [DA.Muller.instωAcceptor]` (see forward lemma, OmegaRegularLanguage.lean:438-441).
- **accept set** of `buchiCongr_DMA` (OmegaRegularLanguage.lean:394-396): `{S | ∃ b ∈ S, ∃ a : Q, ((na.buchiFamily (a, b) ⊓ language na).toSet).Nonempty}`.
- **buchiFamily_saturation** (BuchiCongruence.lean:181): `Saturates (fun i ↦ (na.buchiFamily i).toSet) (language na).toSet`, where `Saturates f s := ∀ i, (f i ∩ s).Nonempty → f i ⊆ s` (Foundations/Data/Set/Saturation.lean:25).
- **mem_buchiFamily** (BuchiCongruence.lean:107): characterizes `xs ∈ na.buchiFamily (a, b)` as a prefix in `eqvCls a` followed by a flatten of segments each in `eqvCls b - 1`.
- **buchiCongr_DMA_run_eq** (OmegaRegularLanguage.lean:405): `(buchiCongr_DMA na).run xs n = ⟦xs.extract 0 n⟧`.
- **mem_infOcc** (InfOcc.lean:88) and **frequently_in_finite_type** (InfOcc.lean:46) for reasoning about `b ∈ infOcc(run xs)`.
- **buchiFamily_cover** (BuchiCongruence.lean:118): `⨆ i, na.buchiFamily i = ⊤` — fallback for obtaining a decomposition of `xs` if the witness's `a` does not directly match `xs`'s prefix class.

### Prior Plan Reference

No prior plan for task 434. The parent task 241 handoff classifies this backward lemma (SUB-C) as one of the "small" follow-ups once infrastructure landed — in contrast to the forward lemma which overflowed three monolithic dispatches. Effort is calibrated accordingly (single dispatch, ~1.5h).

### Roadmap Alignment

No ROADMAP.md consultation requested (roadmap flag not set). This lemma is a sub-goal of the McNaughton theorem effort (parent task 241): it is one of the two inclusions whose antisymmetry yields `buchiCongr_DMA_language_eq`, which in turn unblocks `IsRegular.iff_da_muller`.

## Goals & Non-Goals

**Goals**:
- Add `private lemma buchiCongr_DMA_language_backward` proving `language (buchiCongr_DMA na) ⊆ language na`, mirroring the signature shape of `buchiCongr_DMA_language_forward` (`[Inhabited Symbol] {State : Type} [Finite State] (na : NA.Buchi State Symbol)`, under `open NA.Buchi in`).
- Zero `sorry` and zero new axioms in the new lemma (verified by `lean_verify`).
- `lake build` green for the module.
- Public-facing docstring on the new lemma (CSLib `docBlame` compliance).

**Non-Goals**:
- Do NOT prove or modify `buchiCongr_DMA_language_forward` (task index 1 / SUB-B).
- Do NOT close `buchiCongr_DMA_language_eq`, `to_da_muller_scaffold`, or `IsRegular.iff_da_muller` (task 435 / SUB-D).
- Do NOT alter the `buchiCongr_DMA` definition, its accept set, or any BuchiCongruence.lean API.
- Do NOT run the full PR pipeline (`lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`, `lake shake`) — only `lake build` + `lean_verify` are in scope per the task's CI requirement. (Full pipeline is task 435's responsibility.)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Witness's `a` from the accept set does not match `xs`'s actual prefix class, so `xs ∈ buchiFamily (a, b)` is not directly true | H | M | The accept condition only fixes `b ∈ infOcc(run xs)`; `a` is existential. If a direct decomposition into `eqvCls a` fails, obtain `xs ∈ buchiFamily (a₀, b₀)` via `buchiFamily_cover`, identify `xs`'s own classes via `buchiCongr_DMA_run_eq` + `mem_infOcc`, and reconcile with the accepting witness through `Saturates`. Escalate via `lean_state_search`/`lean_leansearch` before changing the lemma statement. |
| `⊓`/`.toSet`/`.Nonempty` unfolding on `ωLanguage` does not match expected destructuring shape | M | M | Use `lean_hover_info` on `accept`, `lean_goal` after `simp only [...]`; the `⊓` is the lattice meet on `ωLanguage`, so `inf_def`/`Set.mem_inter_iff` patterns apply (compare `IsRegular.fin_cover_saturates`, OmegaRegularLanguage.lean:238-246). |
| Muller acceptance unfolding differs in the `at hxs` direction vs. the forward lemma's goal-side use | L | M | Mirror lines 438-441 but apply `rw [ωAcceptor.mem_language] at hxs` and `simp only [DA.Muller.instωAcceptor] at hxs`; confirm hypothesis shape with `lean_goal`. |
| `[Finite State]` instance unexpectedly unnecessary or insufficient | L | L | Keep `[Finite State]` to match the forward lemma and `buchiCongr_DMA_language_eq`; `buchiFamily_saturation` does not require it but the surrounding eq statement does. |
| `lean_diagnostic_messages` / `lean_file_outline` hang | M | L | Per cslib.md/lean4.md: do NOT call these; use `lean_goal` + `lake build` instead. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This is a single-lemma proof, so all phases are strictly sequential.

### Phase 1: Lemma scaffold and accept-set unfolding [NOT STARTED]

**Goal**: Introduce the lemma with the correct signature, reduce the goal to proving `xs ∈ language na` from a destructured accept witness.

**Tasks**:
- [ ] Add the lemma skeleton after `buchiCongr_DMA_language_forward` (~line 446), before `proof_wanted buchiCongr_DMA_language_eq` (line 460):
  ```lean
  open NA.Buchi in
  private lemma buchiCongr_DMA_language_backward [Inhabited Symbol] {State : Type} [Finite State]
      (na : NA.Buchi State Symbol) :
      language (buchiCongr_DMA na) ⊆ language na := by
    intro xs hxs
    sorry
  ```
- [ ] Unfold the Muller acceptance hypothesis: `rw [ωAcceptor.mem_language] at hxs` then `simp only [DA.Muller.instωAcceptor] at hxs` so that `hxs : ((buchiCongr_DMA na).run xs).infOcc ∈ (buchiCongr_DMA na).accept`. Confirm shape with `lean_goal`.
- [ ] Unfold the accept set (`simp only [buchiCongr_DMA] at hxs` or `change`/`Set.mem_setOf_eq`) and destructure: `obtain ⟨b, hb_inf, a, hys⟩ := hxs` then split the `(... ⊓ language na).toSet.Nonempty` witness into `ys`, `hys_fam : ys ∈ na.buchiFamily (a, b)`, `hys_lang : ys ∈ language na`. Verify the destructuring with `lean_goal`.

**Timing**: 0.4 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - add new private lemma stub with `sorry`, perform acceptance + accept-set unfolding.

**Verification**:
- `lean_goal` shows hypotheses `b`, `hb_inf : b ∈ ((buchiCongr_DMA na).run xs).infOcc`, `a`, `hys_fam`, `hys_lang`, and goal `xs ∈ language na` (a single `sorry` remaining).

### Phase 2: Establish `xs ∈ buchiFamily (a, b)` [NOT STARTED]

**Goal**: Prove the membership `xs ∈ na.buchiFamily (a, b)` (the index whose family intersects `language na`), which is the substantive step of the proof.

**Tasks**:
- [ ] Translate `hb_inf : b ∈ infOcc(run xs)` into prefix-class recurrence using `buchiCongr_DMA_run_eq` and `mem_infOcc` (InfOcc.lean:88): infinitely many `n` satisfy `⟦xs.extract 0 n⟧ = b`.
- [ ] Build the decomposition required by `mem_buchiFamily` (BuchiCongruence.lean:107): a prefix in `eqvCls a` and a flatten of segments each in `eqvCls b - 1`, with concatenation equal to `xs`. Use `mem_buchiFamily.mpr ⟨xl, xls, ...⟩`.
- [ ] **Decision point / escalation**: if the witness's existential `a` does not coincide with `xs`'s prefix class, do NOT change the lemma statement. Instead obtain `xs ∈ na.buchiFamily (a₀, b₀)` via `buchiFamily_cover` (BuchiCongruence.lean:118), identify `xs`'s classes via `buchiCongr_DMA_run_eq` + `mem_infOcc`/`frequently_in_finite_type` (InfOcc.lean:46), and carry whichever index `(a', b')` makes `(buchiFamily (a', b') ⊓ language na).Nonempty` hold so that Phase 3's saturation step closes the goal. Probe candidate lemmas with `lean_state_search` / `lean_leansearch` / `lean_loogle` before committing.
- [ ] Use `lean_multi_attempt` to test tactic fragments before editing; keep `lean_goal` open at each rewrite.

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - fill in the membership proof producing `hxs_fam : xs ∈ na.buchiFamily (a, b)` (or the reconciled index).

**Verification**:
- `lean_goal` shows a proven hypothesis `xs ∈ na.buchiFamily (a, b)` (or reconciled index) with the remaining goal still `xs ∈ language na`.

### Phase 3: Apply `buchiFamily_saturation` and assemble proof [NOT STARTED]

**Goal**: Conclude `xs ∈ language na` from `xs ∈ buchiFamily (a, b)` and the accept witness, removing the final `sorry`.

**Tasks**:
- [ ] Instantiate `buchiFamily_saturation (na := na)` at index `(a, b)`: from `(na.buchiFamily (a, b) ⊓ language na).toSet.Nonempty` (the accept witness `ys`, reshaped to `(buchiFamily (a,b)).toSet ∩ (language na).toSet`) derive `(na.buchiFamily (a, b)).toSet ⊆ (language na).toSet`. Reconcile `⊓`/`.toSet` with `∩` via `inf_def`/`Set.mem_inter_iff` (cf. OmegaRegularLanguage.lean:246).
- [ ] Apply the subset to `hxs_fam` to obtain `xs ∈ language na`; close the goal (`exact`/`apply`).
- [ ] Remove the `sorry`; confirm "no goals" via `lean_goal`.
- [ ] Add a docstring to the lemma describing the backward inclusion and its proof strategy (accept-set unfold → family membership → saturation), satisfying `docBlame`.

**Timing**: 0.3 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` - finalize the saturation application, close the goal, add docstring.

**Verification**:
- `lean_goal` at end of proof reports "no goals".

### Phase 4: CI verification [NOT STARTED]

**Goal**: Confirm the proof compiles green with zero sorries and zero new axioms.

**Tasks**:
- [ ] Run scoped build: `lake build Cslib.Computability.Languages.OmegaRegularLanguage` (fall back to `lake build` if the scoped module path errors).
- [ ] Run `lean_verify Cslib.ωLanguage.buchiCongr_DMA_language_backward` (resolve the exact fully-qualified name via `lean_hover_info` if the namespace prefix differs) — confirm zero sorries and no new axioms beyond the standard set.
- [ ] If any error surfaces, return to the relevant phase; do not leave a partial `sorry`.

**Timing**: 0.3 hours

**Depends on**: 3

**Files to modify**:
- None (verification only).

**Verification**:
- `lake build` exits 0 for the module.
- `lean_verify` on `buchiCongr_DMA_language_backward` reports zero sorries and no new axioms.

## Testing & Validation

- [ ] `lake build` green for `Cslib/Computability/Languages/OmegaRegularLanguage.lean`.
- [ ] `lean_verify` on `buchiCongr_DMA_language_backward`: zero sorries, zero new axioms.
- [ ] New lemma carries a docstring (no `docBlame` regression on the new declaration).
- [ ] No edits to `buchiCongr_DMA`, its accept set, the forward lemma, or BuchiCongruence.lean.

## Artifacts & Outputs

- New `private lemma buchiCongr_DMA_language_backward` in `Cslib/Computability/Languages/OmegaRegularLanguage.lean` (with docstring, sorry-free).
- Updated task metadata (`.return-meta.json`) and orchestrator handoff (`.orchestrator-handoff.json`).

## Rollback/Contingency

The change is additive and confined to a single new lemma. To revert: delete the `buchiCongr_DMA_language_backward` lemma block (the file returns to its prior state — `buchiCongr_DMA_language_forward` and `proof_wanted buchiCongr_DMA_language_eq` are untouched). If the witness-index reconciliation (Phase 2 decision point) proves to require recurrence machinery not yet available, mark Phase 2 [BLOCKED], document the exact goal state reached and the missing lemma, return `status: partial` with `requires_user_review: true`, and leave a single clearly-marked `sorry` rather than any vacuous placeholder.
