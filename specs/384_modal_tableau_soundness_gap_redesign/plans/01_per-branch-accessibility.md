# Implementation Plan: Task #384 — Per-Branch Accessibility Soundness-Gap Redesign

- **Task**: 384 - modal_tableau_soundness_gap_redesign
- **Status**: [NOT STARTED]
- **Effort**: 7 hours
- **Dependencies**: None (blocks completion of task 364)
- **Research Inputs**: specs/384_modal_tableau_soundness_gap_redesign/reports/01_soundness-gap-redesign.md
- **Artifacts**: plans/01_per-branch-accessibility.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Close the build-verified soundness-proof gap in `Cslib/Logics/Modal/Tableau/Soundness.lean`
(errors 1744/1749/1770 in `modalExpandBranches_closed_unsat`'s fuel-induction succ-case) by
adopting research Option A: **per-branch `Accessibility`**. `modalExpandBranches`/`processNext`
will thread a parallel `accs : List Accessibility` (one per worklist branch) instead of a single
shared `acc`, so an existential-rule edge fired on one branch can never pollute a sibling branch.
This removes the two FALSE proof obligations (anti-monotonicity of `branchSatisfiable` under edge
addition) by construction, leaving only provable obligations.

Definition of done: `lake build` (scoped `Cslib.Logics.Modal.Tableau.Soundness` and full repo)
and `lake exe lint-style` pass; zero `sorry`; zero new axioms; public statements
`modalTableau`, `kValid`, `modalTableau_sound`, `ModalTableauResult`, `openBranch` unchanged.

### Research Integration

Integrates report `01_soundness-gap-redesign.md` in full:
- **D1**: Adopt Option A (parallel `accs : List Accessibility`); reject Option B (global counter
  does not fix the shared-source-world pollution, F1/F3) and Option C (major redesign, F4).
- **F2.1**: Exact signature changes to `modalExpandBranches`/`processNext`/`modalTableau`.
- **F2.2**: New helper lemmas (`modalMaxWorld_le_append`, `modalNextWorld_le_append`,
  `label_le_modalMaxWorld`) plus the maintenance lemma `modalStepBranch_preserves_accFreshInv`
  (task-364 "obligation 1", classified provable) with a per-rule proof sketch.
- **F2.3**: Reformulated loop lemma using `List.Forall₂` (Mathlib reuse, D4) with an index-form
  fallback; `modalStepBranch_preserves_sat` (~1450 lines) reused verbatim.
- **H4 adversarial verification**: confirms Option A eliminates pollution by construction and that
  no public statement changes.
- **Appendix / H3**: `[Fitting1983]` and `[Smullyan1968]` BibKeys are cited by the tableau files
  but absent from `references.bib`; add them (independent, parallelizable).

### Prior Plan Reference

No prior plan for task 384. This task is itself the redesign spawned from task 364's blocker;
task 364's committed drift repairs (recognizer arms in `modalApplyOne`, `.{v,u}` universe pins,
the Root-A `boxPos` `split_ifs` fix) all live in defs/theorems untouched by Option A and survive
unchanged (report F2.4).

### Roadmap Alignment

No `roadmap_flag` set and no ROADMAP.md consulted for this task. The implicit roadmap impact is
unblocking task 364 (and transitively task 360's repo-wide green build).

## Goals & Non-Goals

**Goals**:
- Refactor `modalExpandBranches`/`processNext` to the per-branch `accs : List Accessibility` scheme.
- Reformulate the loop invariant of `modalExpandBranches_closed_unsat` as a per-branch
  (`List.Forall₂`) freshness + non-satisfiability statement.
- Prove the missing freshness-maintenance lemma `modalStepBranch_preserves_accFreshInv` and its
  supporting `Branch.lean` monotonicity helpers.
- Close errors 1744/1749/1770 with zero `sorry` and zero new axioms.
- Add the missing `Fitting1983`/`Smullyan1968` entries to `references.bib`.

**Non-Goals**:
- Changing any public API (`modalTableau`, `kValid`, `modalTableau_sound`, `ModalTableauResult`,
  `openBranch` signatures stay verbatim).
- Touching `modalStepBranch_preserves_sat`, `modalApplyOne`, `branchSatisfiable`, `accFreshInv`,
  `modalNextWorld`, or `modalMaxWorld` definitions (reused unchanged).
- Building a full closing-tableau soundness counterexample (`modalTableau φ = .closed ∧ ¬kValid φ`);
  not required for the proof fix (report residual caveat).
- Writing `Tableau/Completeness.lean` or any downstream consumer.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Phase 4 induction bookkeeping over 3 parallel lists (`branches`∥`expandedSets`∥`accs`) is fiddly | H | M | Use `List.Forall₂` length/append/cons lemmas; index-form `∀ i (h : i < n), …` fallback (report D4); obligations 2 & 3 are gone so the proof is strictly simpler than the current broken one |
| `List.Forall₂` append-splitting across `done ++ newBs ++ restBs` awkward | M | M | Fall back to index form; split via `List.forall₂_append` / length-matched `List.Forall₂.append` lemmas |
| Scoped builds on 1817-line `Soundness.lean` are slow | M | H | Prove Phase 2 helpers in the small `Branch.lean`; use `lean_goal`/`lean_multi_attempt` over repeated full builds; avoid `lean_diagnostic_messages` |
| Accidental public-API signature drift | H | L | Phase 5 explicitly diffs `modalTableau`/`kValid`/`modalTableau_sound`/`openBranch`/`ModalTableauResult` types against baseline before final build |
| Fuel-0 zip case mishandles per-branch acc on `.openBranch` return | M | M | Zip `branches.zip accs`; return `.openBranch b a` with the branch-local `a` (report F2.1 item 2) |
| New `sorry`/axiom slips in | H | L | `lake build` rejects `sorry`; run `#print axioms modalTableau_sound` / `lean_verify` to confirm no new axioms |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 6 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel. Phases 1 (Saturation.lean), 2 (Branch.lean),
and 6 (references.bib) touch disjoint files and have no inter-dependencies.

### Phase 1: Definitional plumbing — per-branch `accs` (`Saturation.lean`) [COMPLETED]

**Goal**: Replace the single shared `acc` in `modalExpandBranches`/`processNext` with a parallel
`accs : List Accessibility` (length-matched to `branches`); update the entry point. The file
elaborates; `Soundness.lean`'s `modalExpandBranches_closed_unsat` and `modalTableau_sound` will
break (expected, repaired in Phases 4–5).

**Tasks**:
- [ ] Add `(accs : List Accessibility)` parameter to `modalExpandBranches` (`Saturation.lean:131`);
      drop the single `(acc : Accessibility)` (report F2.1 item 1).
- [ ] Add `pendingAccs`/`doneAccs` to `processNext` (`:145`); match `pending, pendingExp,
      pendingAccs`; carry per-branch acc on the `isModalClosed` (done) lane via
      `doneAccs ++ [a]` (F2.1 item 2).
- [ ] In the step lane, call `modalStepBranch b e a` with the branch's own acc `a`; on `none`
      return `.openBranch b a`; on `some (newBs, newExps, newAcc)` recurse with
      `doneAccs ++ List.replicate newBs.length newAcc ++ restAs`.
- [ ] Update the fuel-0 case (`:137`–`142`) to zip `branches.zip accs` for the openness test and
      return `.openBranch b a` with the branch-local acc.
- [ ] Update `modalTableau` (`:185`) entry call to pass `[Accessibility.empty]` as the singleton
      `accs` (public type unchanged, F2.1 item 3).
- [ ] Confirm `ModalTableauResult`/`openBranch` (`:76`–`81`) and `modalStepBranch` (`:99`) are
      left unchanged.

**Timing**: ~1.5 hours (~100–150 lines changed).

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Saturation.lean` — `modalExpandBranches`, `processNext`,
  fuel-0 case, `modalTableau` entry.

**Verification**:
- `Saturation.lean` elaborates (scoped build of the module succeeds).
- The only new breakage is downstream in `Soundness.lean` at `modalExpandBranches_closed_unsat`
  / `modalTableau_sound` (arity mismatch), confirming the signature change propagated.
- No change to `modalTableau`/`ModalTableauResult`/`openBranch` types.

---

### Phase 2: Freshness monotonicity helpers (`Branch.lean`) [COMPLETED]

**Goal**: Add the small list-monotonicity helper lemmas the maintenance lemma needs. `Branch.lean`
is upstream of `Saturation.lean`, has no dependency on Phase 1, and builds fast.

**Tasks**:
- [ ] Prove `modalMaxWorld_le_append (xs b : List (SignedFormula …)) :
      modalMaxWorld b ≤ modalMaxWorld (xs ++ b)` (routine `List.foldl` induction paralleling the
      existing `key`/`key2` inside `modalNextWorld_gt`, `Branch.lean:108`–`130`).
- [ ] Prove corollary `modalNextWorld_le_append (xs b : …) :
      modalNextWorld b ≤ modalNextWorld (xs ++ b)`.
- [ ] Prove `label_le_modalMaxWorld {sf} (h : sf ∈ b) : sf.label ≤ modalMaxWorld b`
      (membership bound; essentially `key2` from `modalNextWorld_gt`).
- [ ] Keep `modalNextWorld`, `modalMaxWorld`, `modalNextWorld_gt`, `Accessibility` definitions
      unchanged.

**Timing**: ~1 hour (~40–80 lines).

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Branch.lean` — add three helper lemmas.

**Verification**:
- Scoped build of `Cslib.Logics.Modal.Tableau.Branch` succeeds, zero `sorry`.
- `lean_goal` confirms each helper closes; `lean_verify` shows no new axioms.

---

### Phase 3: Maintenance lemma `modalStepBranch_preserves_accFreshInv` (`Soundness.lean`) [COMPLETED]

**Goal**: Prove the freshness-maintenance lemma (task-364 obligation 1) that every child branch
produced by `modalStepBranch` satisfies `accFreshInv` against the post-step acc. This is the only
genuinely new semantic obligation; obligations 2 and 3 are eliminated structurally by Phase 1.

**Tasks**:
- [ ] State `modalStepBranch_preserves_accFreshInv (b e : …) (acc : Accessibility)
      (newBs newExps : …) (newAcc : Accessibility)
      (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
      (hInv : accFreshInv b acc) : ∀ b' ∈ newBs, accFreshInv b' newAcc` (report F2.2).
- [ ] Unfold `modalStepBranch`/`modalApplyOne`; case on the fired rule.
- [ ] Prop rules / `boxPos` / `diamondNeg` case (`newAcc = acc`): each `b' = newForms ++ b` (or a
      `.branching` child `br ++ b`); discharge via `hInv` + `modalNextWorld_le_append` (Phase 2).
- [ ] `diamondPos` / `boxNeg` case (`newAcc = acc.addEdge w w'`, `w = sf.label`,
      `w' = modalNextWorld b`, single child `b'` with `witness.label = w'`): old edges stay
      `< modalNextWorld b ≤ modalNextWorld b'`; new edge source `w = sf.label < modalNextWorld b`
      via `modalNextWorld_gt` + `sf ∈ b`; new edge target `w' < modalNextWorld b'` via
      `label_le_modalMaxWorld` on `witness ∈ b'` (Phase 2 helpers).
- [ ] Verify zero `sorry`.

**Timing**: ~1.5 hours (~60–100 lines).

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — add the maintenance lemma (place near
  `accFreshInv_empty`, `:172`).

**Verification**:
- The lemma elaborates sorry-free in isolation (use `lean_goal`/`lean_multi_attempt`; the rest of
  the file may still be red at `modalExpandBranches_closed_unsat` until Phase 4 — that breakage is
  the expected Phase-1 artifact, not from this lemma).
- `lean_verify` on the new lemma shows no new axioms.

---

### Phase 4: Reformulate `modalExpandBranches_closed_unsat` (`Soundness.lean`) [COMPLETED]

**Goal**: Replace the single-`acc` loop invariant and the unthreadable fixed-`acc` `hstep`
hypothesis with a zipped per-branch invariant, then discharge the fuel + pending inductions —
closing errors 1744/1749/1770. Highest-risk phase.

**Tasks**:
- [ ] Restate the theorem (report F2.3):
      `∀ branches expandedSets accs, expandedSets.length = branches.length →
       accs.length = branches.length →
       List.Forall₂ (fun b acc => accFreshInv b acc) branches accs →
       modalExpandBranches branches expandedSets accs fuel = .closed →
       List.Forall₂ (fun b acc => ¬ branchSatisfiable.{v,u} b acc) branches accs`
      (migrate the `.{v,u}` universe pin from the old statement, F2.4).
- [ ] Drop the fixed-`acc` `hstep` hypothesis; call `modalStepBranch_preserves_sat` directly
      (it is ∀-closed over `acc`) for the expanded branch.
- [ ] Thread freshness for the expanded slot via Phase 3's
      `modalStepBranch_preserves_accFreshInv`; carried siblings keep their `accs[j]` unchanged
      (no `acc → newAcc` lifting — obligations 2 & 3 never arise).
- [ ] Handle `done ++ newBs ++ restBs` / `doneAccs ++ replicate … ++ restAs` splits with
      `List.Forall₂` append/cons lemmas (`List.forall₂_append`, `List.Forall₂.length_eq`);
      fall back to index form `∀ i (h : i < n), …` if append-splitting is awkward (R1/D4).
- [ ] Handle the fuel-0 / `.closed` base cases under the new zipped form.
- [ ] Confirm zero `sorry`; errors 1744/1749/1770 resolved.

**Timing**: ~2.5 hours (~150–250 lines; the core, but strictly simpler than the current broken
attempt because the two false obligations are removed).

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — `modalExpandBranches_closed_unsat`
  (`:1646`–`:1770`).

**Verification**:
- The reformulated theorem elaborates sorry-free; `lean_goal` at the former error lines
  (1744/1749/1770 region) shows "no goals".
- `modalStepBranch_preserves_sat`, `branchSatisfiable`, `accFreshInv`, `accFreshInv_empty`,
  `modalClosed_unsat`, `kValid` remain textually unchanged (diff-checked).

---

### Phase 5: `modalTableau_sound` call site + full CI build (`Soundness.lean`) [COMPLETED]

**Goal**: Adapt the single `modalTableau_sound` call site to the per-branch entry, then run the
full CI pipeline and confirm the public API is unchanged.

**Tasks**:
- [ ] In `modalTableau_sound` (`:1787`–`:1813`) pass `accs := [Accessibility.empty]`; discharge
      `List.Forall₂ accFreshInv [F(φ)@0] [empty]` from `accFreshInv_empty` (`:1801`–`:1802`);
      reuse the `hsat` construction (`:1793`–`:1799`) verbatim.
- [ ] Diff public statements `modalTableau` / `kValid` / `modalTableau_sound` /
      `ModalTableauResult` / `openBranch` against baseline — must be byte-identical types (R3, H4).
- [ ] Run scoped `lake build Cslib.Logics.Modal.Tableau.Soundness`.
- [ ] Run full `lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
      `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Confirm no new axioms (`#print axioms modalTableau_sound` / `lean_verify`).

**Timing**: ~0.5 hours (~10–30 lines).

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — `modalTableau_sound` call site only.

**Verification**:
- Full `lake build` green; `lake exe lint-style` clean; `checkInitImports`/`shake` pass.
- Zero `sorry`, zero new axioms across the four tableau files.
- Public API types unchanged.

---

### Phase 6: Citation hygiene (`references.bib`) [COMPLETED]

**Goal**: Add the two BibKeys cited by the tableau files but absent from `references.bib`
(report H3 / Appendix). Independent of the proof work.

**Tasks**:
- [ ] Add `@book{Fitting1983, author={Fitting, Melvin}, title={Proof Methods for Modal and
      Intuitionistic Logics}, publisher={Reidel}, year={1983}}`.
- [ ] Add `@book{Smullyan1968, author={Smullyan, Raymond M.}, title={First-Order Logic},
      publisher={Springer}, year={1968}}`.
- [ ] Confirm metadata (publisher/year) against canonical entries before committing; do NOT
      reuse the unrelated `Fitting1969` entry (`references.bib:196`).

**Timing**: ~0.25 hours.

**Depends on**: none

**Files to modify**:
- `references.bib` — two new `@book` entries.

**Verification**:
- `[Fitting1983]` and `[Smullyan1968]` resolve for the citing files
  (`Branch.lean:37`, `Rules.lean:42,43`, `Saturation.lean:57,58`, `Soundness.lean:45`).
- No duplicate/clashing BibKeys introduced.

## Testing & Validation

- [ ] Scoped `lake build Cslib.Logics.Modal.Tableau.Branch` (after Phase 2).
- [ ] Scoped `lake build Cslib.Logics.Modal.Tableau.Soundness` (after Phases 3, 4, 5).
- [ ] Full `lake build` green (Phase 5).
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` clean.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes.
- [ ] Zero `sorry` in all four tableau files (`grep -rn "sorry"`).
- [ ] Zero new axioms: `#print axioms modalTableau_sound` shows only standard axioms.
- [ ] Public API types (`modalTableau`, `kValid`, `modalTableau_sound`, `ModalTableauResult`,
      `openBranch`) diff-identical to baseline.
- [ ] Errors 1744/1749/1770 in `modalExpandBranches_closed_unsat` no longer present.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/Saturation.lean` — per-branch `accs` threading.
- `Cslib/Logics/Modal/Tableau/Branch.lean` — three monotonicity helper lemmas.
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — maintenance lemma + reformulated loop lemma +
  adapted `modalTableau_sound` call site.
- `references.bib` — `Fitting1983`, `Smullyan1968` entries.
- `specs/384_modal_tableau_soundness_gap_redesign/summaries/01_per-branch-accessibility-summary.md`
  (on implementation completion).

## Rollback/Contingency

- All changes are confined to four files; revert via `git checkout` on
  `Cslib/Logics/Modal/Tableau/{Branch,Saturation,Soundness}.lean` and `references.bib`.
- If Phase 4's `List.Forall₂` reformulation stalls, fall back to the index-form invariant
  `∀ i (h : i < branches.length), accFreshInv branches[i] accs[i]` / `¬ branchSatisfiable …`
  (report D4) — the proof obligations are identical, only the bookkeeping changes.
- Phases 1–3 produce no `sorry` and leave the public API intact; if Phase 4 cannot be completed
  in one run, commit Phases 1–3 (Branch.lean green, maintenance lemma green) and resume Phase 4
  with the scaffolding in place. The task remains blocked (task 364 stays blocked) but no
  regression is introduced beyond the pre-existing gap.
- Option B / Option C are explicitly rejected (report F3/F4); do not pivot to them — Option B does
  not fix the shared-source-world pollution.
