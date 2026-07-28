# Implementation Plan: Remove Redundant listImp/bigconj Normalization Rewrites

- **Task**: 413 - simplify_proofs_normalization_propositional
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/413_simplify_proofs_normalization_propositional/reports/01_redundant-normalization-rewrites.md`
- **Artifacts**: plans/01_remove-redundant-normalization-rewrites.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Every `simp only [listImp_*|bigconj_*]` invocation in the repository rewrites with a lemma
proved by `rfl`, standing in front of an `exact` that already elaborates up to defeq. The
research report verified empirically that deleting all of them (plus the accompanying
`unfold ListDeriv` / `simp only [<algDS-alias>]` unfolds) leaves the project green under a full
`lake build` and clean under `lake lint`. This plan applies that change set in small,
independently-verifiable slices, preserving the explanatory comments the deleted tactic blocks
carried and adding a defeq-reliance note where the simplification now depends on
`ListDeriv` transparency. Definition of done: zero residual `simp only [...listImp|bigconj...]`
sites, full `lake build` green, CSLib 7-step CI green, and no change to the repository's
pre-existing `sorry` baseline.

### Research Integration

- Report `reports/01_redundant-normalization-rewrites.md` supplies the full verified inventory
  (20 rewrite sites plus 15 accompanying unfolds across 8 files) and the root-cause argument:
  `listImp_nil`/`listImp_cons`/`bigconj_nil`/`bigconj_singleton`/`bigconj_cons_cons` are all
  `:= rfl`; `ListDeriv` is a transparent `def`; `DerivationSystem.Deriv` is a plain structure
  field. All three collapse the rewrite chains to no-ops.
- The report also supplies a pre-verified diff at
  `specs/413_simplify_proofs_normalization_propositional/verified-simplification.patch`.
  **Confirmed at planning time**: `git apply --check` succeeds against current HEAD and
  `git status --porcelain Cslib/` is empty, so the patch is a valid starting point, not stale.
- The report's tactic survey rejects `simp`, `grind`, and `aesop` for these sites in favour of
  bare `exact`. This plan adopts that verdict; it introduces no new tactic, no new lemma, and no
  attribute change.
- Scope reconciliation carried forward from the report: 7 of the 8 affected files are outside
  `Logics/Propositional/`. The task description must be updated (Phase 7), not silently widened.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` names "elegance and non-redundancy" as the current emphasis, driving the
metalogic grid toward "a single shared abstraction per concern rather than per-system copies"
(see the **Abstraction & Redundancy Cleanup** agenda). This change set removes four
copy-pasted instances of an identical redundant tactic prologue from the four
`GenericMCSBridge` files, which is directly on that agenda. No roadmap item is completed by
this work and `ROADMAP.md` is not modified by this plan.

## Goals & Non-Goals

**Goals**:
- Delete every `simp only [listImp_*|bigconj_*|negBigconj_*]` invocation and every accompanying
  `unfold ListDeriv` / `simp only [<algDS alias>, treeAlgDS, algebraicDerivationSystem]` that is
  a provable no-op, replacing each with the bare `exact` that already discharges the goal.
- Preserve every explanatory comment the deleted tactic blocks carried, re-sited as a standalone
  comment.
- Add a one-line defeq-reliance note at each `derivTreeToList*` so the new proofs document why
  the bare `exact` typechecks.
- Keep the repository's `sorry`/axiom baseline unchanged and the full CI pipeline green.
- Reconcile the task description with the verified repo-wide scope.

**Non-Goals**:
- No repo-wide sweep for the same anti-pattern with *other* `rfl`-simp lemmas. The report
  explicitly declines to bound that set; it belongs to a separate task with its own detection
  recipe.
- No change to `grind [listImp_axiom_k]` at `ListDeduction.lean:78` — that `grind` is doing real
  work and is explicitly out of scope.
- No new definitions, lemmas, abstractions, notation, or `@[simp]` set changes.
- No discharge of the four pre-existing `sorry`s in `Logics/Propositional/Tableau/`.
- No PR creation and no push. Implementation ends at the task's normal terminus.

## The "Do Not Simplify" Criterion

A shorter proof that is more fragile or slower is not an improvement. Before committing each
site, the implementer applies this criterion. **Any site failing any test below is left exactly
as it is, and the reason is recorded as a `#### Reasoned Exclusions` subsection inside the
phase, which then closes as `[COMPLETED WITH EXCLUSIONS]`.**

1. **Compiles bare.** The module builds green with the tactic block deleted. A site that needs
   the rewrite reinstated to compile is not redundant and stays.
2. **No new `sorry` or axiom.** `lean_verify` on the affected declaration reports the same
   axiom set as before the edit.
3. **No elaboration-time regression.** The module's build time does not regress materially
   against the Phase 1 baseline. If a bare `exact` forces expensive defeq unification where the
   rewrite had cheaply normalized the goal first, revert that site.
4. **No term-level change to a data-producing declaration that is not full-build verified.**
   `unfoldListImp` returns `D Γ φ` (data, not `Prop`); dropping `simpa only [listImp_nil]`
   removes an `Eq.mpr` from the produced term. This site is only acceptable under a *full*
   `lake build`, never a module-scoped one.
5. **Fragility is documented, not merely accepted.** Where the simplified proof relies on
   `ListDeriv` being a transparent `def` and `Deriv` being a plain field, that reliance gets a
   source comment. A site whose defeq reliance cannot be stated in one line is a signal the
   simplification is too clever; leave it.
6. **Readability is not reduced.** If deleting the tactics also deletes the only explanation of
   what the arm is doing, the comment is preserved standalone. Losing the comment is not an
   acceptable cost of losing the tactic.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `unfoldListImp` term change alters downstream reduction (data, not `Prop`) | H | L | Isolated in its own phase (Phase 3) with mandatory **full** `lake build`, never module-scoped |
| Explanatory comments deleted along with the tactics they annotated | M | H | Comment preservation is an explicit task bullet in Phases 4 and 5; Phase 6 audits diff for comment loss |
| Simplified bridge proofs break if `ListDeriv` is later made `irreducible`/`structure` | M | L | Phase 6 adds an explicit defeq-reliance comment at each `derivTreeToList*`; the bridges' `listDerivToTree` already depends on the same defeq, so the commitment is pre-existing, not new |
| Patch is stale relative to HEAD | M | L | Phase 1 re-runs `git apply --check`; confirmed passing at planning time but must be re-confirmed at implementation time |
| Scope silently widens beyond `Propositional/` without user visibility | M | M | Phase 7 updates the task description in `specs/state.json`; the widening is stated, never silent |
| Bare `exact` slower to elaborate than the rewrite it replaced | L | L | Criterion 3 above; Phase 1 captures per-module build-time baseline for comparison |
| Residual sites missed | L | M | Phase 7 re-runs the detection grep and requires a zero count |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 4, 5 |
| 6 | 7 | 6 |

Phases within the same wave can execute in parallel. Note for Wave 4: Phases 4 and 5 are
file-disjoint and may be edited in parallel, but `lake` holds a build lock, so their
verification builds serialize even when the edits do not.

---

### Phase 1: Baseline capture and patch re-verification [COMPLETED]

**Goal**: Establish the pre-change ground truth — residual-site count, `sorry`/axiom baseline,
and per-module build timings — so every later phase has something to compare against, and
confirm the pre-verified patch still applies to current HEAD.

**Tasks**:
- [ ] Confirm `git status --porcelain Cslib/` is empty before starting.
- [ ] Run `git apply --check specs/413_simplify_proofs_normalization_propositional/verified-simplification.patch`
      and record the result. If it fails, the patch is stale: fall back to applying the edits by
      hand per the report's §4.1/§4.2 tables and record that the patch was not used.
- [ ] Record the residual-site count:
      `grep -rn "simp only \[.*\(listImp\|bigconj\|negBigconj\)" Cslib/ | wc -l`
- [ ] Record the accompanying-unfold count: `grep -rn "unfold ListDeriv" Cslib/ | wc -l`
- [ ] Run a full `lake build` on the clean tree and record: job count, wall time, and the exact
      set of `sorry` warnings emitted (file:line for each).
- [ ] Record per-module baseline build times for the 8 target modules
      (`lake build <Module>` after `lake clean`-free incremental touch, or capture from the full
      build's profile output) for use by criterion 3.
- [ ] Write all of the above to
      `specs/413_simplify_proofs_normalization_propositional/baseline.md`.

**Timing**: 45 minutes (dominated by the full build)

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: The report asserts 20 `simp only [listImp_*|bigconj_*]` sites, 15
accompanying unfolds, 8 affected files, and exactly 4 pre-existing `sorry` warnings (in
`Tableau/Intuitionistic/Scheme.lean`, `Tableau/Intuitionistic/Completeness.lean`,
`Tableau/Minimal/Completeness.lean`). These are hypotheses. Confirm each by running the greps
and the full build in this phase and recording the *observed* numbers in `baseline.md`. Every
later phase compares against the observed numbers, not against the report's numbers. If the
observed counts differ, do not proceed to Phase 2 — mark this phase `[BLOCKED]` and report the
discrepancy.

**Files to modify**:
- `specs/413_simplify_proofs_normalization_propositional/baseline.md` - new; the measurement record. No `.lean` file is touched in this phase.

**Verification**:
- `baseline.md` exists, is non-empty, and contains a numeric value for every recorded metric.
- `git status --porcelain Cslib/` is still empty at phase end (no source edit leaked in).
- Full `lake build` completed green.

---

### Phase 2: Foundations Tier-B proof-body edits [COMPLETED]

**Goal**: Remove the redundant rewrites from the three Foundations sites whose enclosing
declarations are `theorem`s (proof-irrelevant, no term-level downstream exposure), leaving the
one data-level site for Phase 3.

**Tasks**:
- [ ] `Foundations/Logic/Metalogic/MCSProperties.lean:110` — replace
      `unfold ListDeriv; simp only [listImp_nil]; exact h_ax` with `exact h_ax`.
- [ ] `Foundations/Logic/Metalogic/MCSProperties.lean:125` — replace
      `unfold ListDeriv; simp only [listImp_nil]; exact h_thm` with `exact h_thm`.
- [ ] `Foundations/Logic/Metalogic/ListDeduction.lean:80-84` — collapse the four-line
      `have ih' := ih h` / `unfold ListDeriv at ih' ⊢` / `simp only [listImp_cons]` / `exact ...`
      block to `exact ModusPonens.mp HasAxiomImplyK.implyK (ih h)`. Preserve the
      `-- φ ∈ Ψ, use ih and then weaken` comment.
- [ ] `Foundations/Logic/Theorems/BigConj.lean:114` — delete
      `simp only [bigconj_cons_cons] at hconj` from `bigconj_mem_derivable`.
- [ ] `Foundations/Logic/Theorems/BigConj.lean:127,132,135` — delete the `simp only [bigconj_nil]`,
      `simp only [bigconj_singleton]`, and `simp only [bigconj_cons_cons]` lines from
      `bigconj_derivable_intro`.
- [ ] Leave `grind [listImp_axiom_k]` at `ListDeduction.lean:78` untouched.
- [ ] Apply the "Do Not Simplify" criterion to each of the 7 sites before committing.

**Timing**: 45 minutes

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts exactly 7 edit sites across exactly 3 files
(`MCSProperties.lean` ×2, `ListDeduction.lean` ×1 block, `BigConj.lean` ×4), and asserts that
all enclosing declarations are `Prop`-valued `theorem`s so the edits carry no term-level
downstream exposure. Confirm at implementation time by (a) re-grepping the three files for
residual target sites and expecting zero, and (b) checking each enclosing declaration's keyword
is `theorem`/`lemma` and its result type is a `Prop` — if any turns out to be a `def` returning
data, move that site to Phase 3's `full`-tier treatment instead of handling it here.

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` - drop 2 no-op rewrite chains
- `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean` - collapse 4-line block to 1 line
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` - drop 4 no-op rewrites

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.MCSProperties`,
  `lake build Cslib.Foundations.Logic.Metalogic.ListDeduction`, and
  `lake build Cslib.Foundations.Logic.Theorems.BigConj` each green.
- Sorry-freeness: `grep -n "sorry" ` on the three changed files returns nothing, and
  `lean_verify` on `mcs_mp_axiom`, `mcs_theorem_in_mcs`, `list_deriv_reflection`,
  `bigconj_mem_derivable`, `bigconj_derivable_intro` reports no `sorryAx` and an axiom set
  matching the pre-edit set.
- Build times for the three modules within the Phase 1 baseline envelope (criterion 3).

---

### Phase 3: `unfoldListImp` data-level edit [NOT STARTED]

**Goal**: Apply the single edit that changes a produced *term* rather than a proof, under
full-project verification, isolated so that any downstream reduction breakage is unambiguously
attributable.

**Tasks**:
- [ ] `Foundations/Logic/Metalogic/GenericMCS.lean:242` — replace
      `| [], d, _ => by simpa only [listImp_nil] using d` with `| [], d, _ => d`.
- [ ] `Foundations/Logic/Metalogic/GenericMCS.lean:244` — delete
      `simp only [listImp_cons] at d`.
- [ ] Add a short source comment at `unfoldListImp` noting that the `[]` case is closed by defeq
      (`listImp [] φ` reduces to `φ`), since the tactic that used to say so is gone.
- [ ] Apply criterion 4 explicitly: this phase is *only* acceptable under a full `lake build`.

**Timing**: 45 minutes (dominated by the full build)

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts exactly 2 edit sites in one file, and asserts that
`unfoldListImp` is the *only* data-producing (non-`Prop`) declaration in the whole change set.
Confirm at implementation time by grepping the 8 target files for `def`/`noncomputable def`
declarations that enclose any remaining target site; the expected result is that
`unfoldListImp` is the sole hit. If a second data-producing site exists, it must be brought
into this phase (not left in a `local`-tier phase).

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` - `unfoldListImp` term-level simplification

**Verification**:
- **Full** `lake build` green (module-scoped build is explicitly insufficient here).
- Sorry-freeness: full-build `sorry` warning set identical to the Phase 1 baseline set —
  same files, same line numbers, same count. Any new warning fails the phase.
- `lean_verify` on `Cslib.Logic.Metalogic.GenericMCS.unfoldListImp` and on at least one
  downstream consumer (`GenericMCS.listDerivToTree`) reports no `sorryAx`.
- Full-build wall time within the Phase 1 baseline envelope.

---

### Phase 4: Propositional and Modal bridge forward proofs [NOT STARTED]

**Goal**: Strip the redundant per-arm prologues from `derivTreeToList` in the Propositional and
Modal bridges, preserving their explanatory comments.

**Tasks**:
- [ ] `Logics/Propositional/Metalogic/GenericMCSBridge.lean` (`derivTreeToList`, around L116-133)
      — delete the `simp only [propAlgDS, treeAlgDS, algebraicDerivationSystem]` (and `... at *`)
      lines from the `axiom`, `assumption`, `modusPonens`, and `weakening` arms, and the
      `unfold ListDeriv` in the `axiom` arm.
- [ ] Preserve the `-- Lift to the algebraic system via K-weakening: ⊢ ψ → listImp Γ ψ, then MP`
      comment as a standalone comment.
- [ ] `Logics/Modal/Metalogic/GenericMCSBridge.lean` (`derivTreeToList`, around L117-146) — same
      deletions for `ax`, `assumption`, `modus_ponens`, `weakening`; additionally collapse the
      `necessitation` arm's `have h_thm := by unfold ListDeriv at ih; simp only [listImp_nil] at ih; exact ih`
      restatement so `ih` is used directly:
      `exact ⟨DerivationTree.necessitation ψ ih.toDerivation⟩`.
- [ ] Preserve the Modal `necessitation` arm's
      `-- ih : modalAlgDS.Deriv [] ψ = ListDeriv [] ψ = DerivableIn (ClosedHilbert ...) ψ`
      comment and the `-- Box-necessitation: ⊢ ψ → ⊢ □ψ ...` comment as standalone comments —
      these become *more* load-bearing once the tactics are gone.
- [ ] Apply the "Do Not Simplify" criterion, especially criteria 5 and 6, to every arm.
- [ ] Do not introduce any task-number reference into `Cslib/` source comments.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts 4 redundant-prologue arms in the Propositional bridge
and 5 in the Modal bridge (plus one `have h_thm` restatement block in Modal), all inside
`Prop`-valued `lemma`s with unchanged signatures. Confirm by re-grepping both files for
residual target sites (expect zero) and by checking `derivTreeToList`'s declared signature is
byte-identical before and after (`git diff` on the two files must show no change to any line
containing `lemma derivTreeToList` or its type ascription).

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` - remove no-op prologues from `derivTreeToList`
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` - remove no-op prologues and the `h_thm` restatement

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.GenericMCSBridge` green.
- `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` green.
- Sorry-freeness: neither file contains `sorry`; `lean_verify` on both `derivTreeToList`
  declarations (fully qualified) reports no `sorryAx` and an unchanged axiom set.
- `git diff` on both files shows every deleted comment either retained in place or re-sited —
  net comment-line count must not decrease except where a comment described only a deleted
  tactic mechanic.

---

### Phase 5: Temporal and Bimodal bridge forward proofs [NOT STARTED]

**Goal**: Same treatment for `derivTreeToListFc` in the Temporal and Bimodal bridges, which
carry the extra `temporal_necessitation` and `temporal_duality` arms (the largest single win).

**Tasks**:
- [ ] `Logics/Temporal/Metalogic/GenericMCSBridge.lean` (`derivTreeToListFc`, around L152-181) —
      delete the `simp only [temporalAlgDSFc, algebraicDerivationSystem]` (and `... at *`) lines
      and the `unfold ListDeriv` from all arms; collapse the `temporal_necessitation` and
      `temporal_duality` arms to
      `exact ⟨DerivationTree.temporal_necessitation ψ ih.toDerivation⟩` and
      `exact ⟨DerivationTree.temporal_duality ψ ih.toDerivation⟩` respectively, dropping the
      intermediate `h_thm` / `h_dual` restatements.
- [ ] `Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` (`derivTreeToListFc`, around
      L168-205) — same for the `axiom`, `assumption`, `modus_ponens`, `necessitation`,
      `temporal_necessitation`, `temporal_duality`, and `weakening` arms.
- [ ] Preserve every explanatory comment in both files, re-sited standalone where its tactic is
      deleted.
- [ ] Apply the "Do Not Simplify" criterion to every arm.
- [ ] Do not introduce any task-number reference into `Cslib/` source comments.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts 6 redundant-prologue arms in the Temporal bridge and 7
in the Bimodal bridge, with 2 and 3 `h_thm`/`h_dual` restatement blocks respectively, all inside
`Prop`-valued `lemma`s with unchanged signatures. Confirm by re-grepping both files for residual
target sites (expect zero) and by confirming `git diff` shows no change to either
`derivTreeToListFc` signature line. If an arm's `ih` cannot be used directly (i.e. the bare
`exact` fails), that arm falls under criterion 1 and is left unchanged as a Reasoned Exclusion.

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` - remove no-op prologues and restatements from `derivTreeToListFc`
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` - same, largest arm count

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.GenericMCSBridge` green.
- `lake build Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge` green.
- Sorry-freeness: neither file contains `sorry`; `lean_verify` on both `derivTreeToListFc`
  declarations reports no `sorryAx` and an unchanged axiom set.
- Comment-preservation check as in Phase 4.

---

### Phase 6: Fragility adjudication and defeq documentation [NOT STARTED]

**Goal**: Decide, on evidence rather than by default, which simplifications to keep; document the
defeq reliance the kept ones now depend on; and revert any site that fails the "Do Not Simplify"
criterion.

**Tasks**:
- [ ] Re-read the accumulated diff (`git diff` across all 8 files) as a single review pass.
- [ ] For each of the four `derivTreeToList*` lemmas, add one line of doc/source comment stating
      the defeq reliance explicitly — that `(<logic>AlgDS ...).Deriv Γ φ`, `ListDeriv Γ φ`, and
      `InferenceSystem.DerivableIn S (listImp Γ φ)` are definitionally equal, so the arms close
      by `exact` without rewriting, and that this mirrors the reliance `listDerivToTree` already
      has.
- [ ] Compare each changed module's build time against the Phase 1 per-module baseline. Any
      material regression triggers criterion 3: revert that site.
- [ ] Audit for comment loss across the whole diff; restore anything dropped.
- [ ] For any site reverted under any criterion, record it in a `#### Reasoned Exclusions`
      subsection under this phase (Item / Reason / Evidence) and set this phase's heading to
      `[COMPLETED WITH EXCLUSIONS]`. If nothing is reverted, close as `[COMPLETED]` with no
      exclusions subsection.
- [ ] Do not introduce any task-number reference into `Cslib/` source comments.

**Timing**: 45 minutes

**Depends on**: 4, 5

**Verification Tier**: full

**Scope Hypothesis**: This phase assumes zero reverts will be needed, on the strength of the
report's full-build verification. That assumption is a hypothesis, not a fact: confirm it by
actually running the per-module timing comparison and the full build in this phase. A non-zero
revert count is a valid outcome, not a failure — it is recorded as Reasoned Exclusions.

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` - defeq-reliance comment
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` - defeq-reliance comment
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` - defeq-reliance comment
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` - defeq-reliance comment
- any file where a site is reverted under the criterion

**Verification**:
- **Full** `lake build` green.
- Full-build `sorry` warning set identical to the Phase 1 baseline (same 4 files/lines, or
  whatever Phase 1 actually observed).
- Each of the four `derivTreeToList*` lemmas carries a defeq-reliance comment.
- Every criterion decision is recorded — either the site is simplified, or it appears in
  Reasoned Exclusions with evidence.

---

### Phase 7: Full CI pipeline and scope reconciliation [NOT STARTED]

**Goal**: Run the complete CSLib CI order, confirm zero residual sites, and update the task
description so the repo-wide scope is explicit rather than silently expanded.

**Tasks**:
- [ ] Run the CSLib CI order in sequence, recording each result:
      `lake build` -> `lake exe checkInitImports` -> `lake lint` -> `lake exe lint-style` ->
      `lake test` -> `lake shake --add-public --keep-implied --keep-prefix`.
      (`lake exe mk_all --module` is not needed — no files are added.)
- [ ] Confirm zero residual sites:
      `grep -rc "simp only \[.*\(listImp\|bigconj\|negBigconj\)" Cslib/` returns no non-zero
      counts, modulo any Reasoned Exclusions recorded in Phase 6.
- [ ] Confirm `lake lint` produces no output attributable to any of the 8 changed files.
- [ ] Confirm `lake shake` proposes no import removal for the changed files (the `ListDeriv`
      *statement* still needs `listImp`, so no import should become removable).
- [ ] Update the task description in `specs/state.json` to state the corrected scope: repo-wide
      removal of redundant `listImp`/`bigconj` normalization rewrites across Foundations, Modal,
      Temporal, Bimodal, and Propositional — not `Propositional/`-only. Then run
      `bash .claude/scripts/generate-todo.sh`.
- [ ] Record the final diffstat (files changed, insertions, deletions) for comparison against the
      report's predicted 8 files / 10 insertions / 72 deletions.

**Timing**: 1 hour (dominated by `lake build` + `lake test` + `lake shake`)

**Depends on**: 6

**Verification Tier**: full

**Scope Hypothesis**: The report predicts a final diffstat of 8 files changed, 10 insertions,
72 deletions (62 net lines removed). Confirm by running `git diff --stat` at phase end; the
actual figure will differ because this plan *adds* comments (defeq-reliance notes, re-sited
explanations) that the report's raw patch did not. Record the observed figure; do not treat the
report's number as a target to hit.

**Files to modify**:
- `specs/state.json` - corrected task description
- `specs/TODO.md` - regenerated from state.json (never hand-edited)

**Verification**:
- All six CI steps pass.
- Residual-site grep returns zero (or exactly the recorded exclusions).
- `sorry` baseline unchanged from Phase 1.
- `specs/state.json` description reflects repo-wide scope; `TODO.md` regenerated.

---

## Testing & Validation

- [ ] Full `lake build` green with the same job count as the Phase 1 baseline.
- [ ] `lake exe checkInitImports` passes — no import changes were made, so this must be a no-op.
- [ ] `lake lint` emits nothing for any of the 8 changed files.
- [ ] `lake exe lint-style` passes.
- [ ] `lake test` (`CslibTests/`) passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` proposes no removals for the changed
      files.
- [ ] `sorry` warning set at the end is byte-identical to the Phase 1 baseline set — no new
      `sorry`, and none of the four pre-existing ones accidentally "fixed" or moved.
- [ ] `lean_verify` reports no `sorryAx` and unchanged axiom sets for: `unfoldListImp`,
      `listDerivToTree`, `mcs_mp_axiom`, `mcs_theorem_in_mcs`, `list_deriv_reflection`,
      `bigconj_mem_derivable`, `bigconj_derivable_intro`, and all four `derivTreeToList*`.
- [ ] Residual-site grep returns zero across `Cslib/`.
- [ ] No task-number reference appears anywhere under `Cslib/`.

## Artifacts & Outputs

- `specs/413_simplify_proofs_normalization_propositional/plans/01_remove-redundant-normalization-rewrites.md` (this file)
- `specs/413_simplify_proofs_normalization_propositional/baseline.md` (Phase 1 measurement record)
- `specs/413_simplify_proofs_normalization_propositional/summaries/01_remove-redundant-normalization-rewrites-summary.md`
- Modified sources (8 files):
  - `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`
  - `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean`
  - `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean`
  - `Cslib/Foundations/Logic/Theorems/BigConj.lean`
  - `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean`
  - `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`
  - `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`
  - `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`
- Updated `specs/state.json` task description and regenerated `specs/TODO.md`

## Rollback/Contingency

- Every phase commits independently (`Commit Mode: per-substep` throughout), so any single phase
  can be reverted with `git revert` of its commit without disturbing the others.
- The pre-change state is recoverable at any point:
  `git checkout <baseline-sha> -- Cslib/` restores all 8 files, and
  `specs/413_simplify_proofs_normalization_propositional/verified-simplification.patch`
  preserves the forward diff independently of git history.
- If Phase 3 (`unfoldListImp`) breaks the full build, revert that phase alone. Phases 2, 4, and 5
  are `Prop`-only and remain valid without it; the task can complete as
  `[COMPLETED WITH EXCLUSIONS]` with `unfoldListImp` recorded as an exclusion.
- If a bridge phase regresses build time, revert only the offending arm per criterion 3 — arm
  reverts are line-local and do not require reverting the whole phase.
- Before any destructive git operation on a dirty tree, run
  `bash .claude/scripts/git-snapshot.sh 413` first.
