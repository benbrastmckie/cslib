# Implementation Plan: Simplify Modal/Temporal/Bimodal Proofs via Existing Normalization Lemmas

- **Task**: 414 - simplify_proofs_normalization_modal_family
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: Territory overlap with the sibling proof-golf task covering `Propositional/`
  and `Foundations/` (see "Sibling-Task Territory Split" below). No hard blocking dependency;
  Phase 2 carries an idempotency guard.
- **Research Inputs**: `specs/414_simplify_proofs_normalization_modal_family/reports/01_simplify-modal-family-proofs.md`
- **Artifacts**: plans/01_modal-family-proof-golf.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md;
  `.claude/rules/cslib.md`; `.claude/rules/lean4.md`; `.claude/rules/plan-compliance.md`
- **Type**: cslib
- **Lean Intent**: true

## Overview

Remove redundant normalization tactics and hand-rolled classical reasoning from proofs in
`Cslib/Logics/{Modal,Temporal,Bimodal}/`, using only lemmas and definitional equalities that
already exist. Two verified change families are in scope: (F1) `unfold ListDeriv; simp only
[listImp_nil]` sequences that are entirely redundant because `ListDeriv [] φ` is *definitionally*
`InferenceSystem.DerivableIn S φ`, and (F2) the `and`/`or` arms of
`bimodal_truthAt_toBimodal_iff_satisfies` in `ModalConservativity.lean`, where a backward rewrite
by the induction hypotheses reduces each case to a propositional tautology that `tauto` closes.
No new declarations, no signature changes, no attribute changes, no new axioms. Definition of
done: every touched module builds, the full project builds, the CSLib CI order passes, and every
touched declaration is confirmed sorry-free and axiom-clean.

### Research Integration

The research report empirically verified every recommended replacement with `lean_multi_attempt`
against the live LSP. Key integrated results:

- `exact ih` closes the `ListDeriv [] ψ` goals across the defeq; `simpa using ih` **fails** with a
  type mismatch and must not be substituted.
- `simp only [Modal.Proposition.toBimodal, Bimodal.Formula.and, truthAt, Modal.Satisfies,
  ← ih1 w, ← ih2 w]; tauto` closes the entire `and` case (verified zero goals).
- `rw [← ih1 w, ← ih2 w]` **fails** — the induction hypotheses are `let`-bound, so `simp only [← …]`
  is required, not `rw`.
- The `box` and `diamond` arms are a **verified dead end** (`simp only [← ih w]` reports "simp made
  no progress"); their `kripkeAdapterOmega_eq_of_accessible` transport steps are load-bearing.
- A new `listDeriv_nil` lemma is explicitly recommended against (no consumers after F1; plausible
  `simpNF` offender).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only. This is lower-priority proof-golf maintenance work
that advances no dedicated roadmap milestone; it reduces tactic-line count and removes a
copy-pasted anti-pattern from the modal-family metalogic bridges.

### Sibling-Task Territory Split

A sibling proof-golf task nominally scoped to `Propositional/` produced a research report that was
**retargeted repo-wide** and whose verified change set includes all four `GenericMCSBridge` files —
i.e. it claims the same `Modal/`, `Temporal/`, and `Bimodal/` F1 sites this plan targets, plus the
`Foundations/` sites (`GenericMCS.lean`, `ListDeduction.lean`, `MCSProperties.lean`,
`BigConj.lean`). This is a genuine collision, not a duplication of description.

**Declared split for this plan** (recorded so neither task silently redoes the other's work):

| Territory | Owner |
|---|---|
| `Cslib/Logics/{Modal,Temporal,Bimodal}/**` | This task |
| `Cslib/Logics/Propositional/**`, `Cslib/Foundations/**` | Sibling proof-golf task |

Consequences, both enforced below:

1. The `Foundations/Logic/Metalogic/MCSProperties.lean:110,125` sites the research report flagged
   as "optional, strictly outside directory scope" are a **Non-Goal** here.
2. Phase 2 opens with an idempotency guard: if the sibling task has already landed the F1 edits in
   the modal-family bridges, the affected phases close as `[COMPLETED WITH EXCLUSIONS]` with a
   Reasoned Exclusions table rather than re-applying or reverting anything.

## Goals & Non-Goals

**Goals**:

- Remove the redundant `unfold ListDeriv` / `simp only [listImp_nil]` normalization pairs from the
  `necessitation`, `temporal_necessitation`, and `temporal_duality` arms of the `derivTreeToList*`
  proofs in the Bimodal, Temporal, and Modal `GenericMCSBridge.lean` files.
- Collapse the `and` and `or` arms of `bimodal_truthAt_toBimodal_iff_satisfies` in
  `ModalConservativity.lean` to the verified one-line `simp only [… ← ih1 w, ← ih2 w]; tauto` form.
- Keep every touched proof sorry-free and axiom-clean, verified per phase and again at the end.
- Preserve every explanatory comment whose content survives the edit, re-sited to the surviving
  tactic line.

**Non-Goals**:

- The `box` and `diamond` arms of `bimodal_truthAt_toBimodal_iff_satisfies`
  (`ModalConservativity.lean:186-229`) — verified dead end; leave all 44 lines alone.
- Adding a `listDeriv_nil` lemma to `Foundations/Logic/Metalogic/ListDeduction.lean`.
- Any edit under `Cslib/Foundations/**` or `Cslib/Logics/Propositional/**` (sibling territory).
- Unifying the two coexisting `bigconj` definitions (`Foundations/Logic/Theorems/BigConj.lean:60`
  vs `Logics/Temporal/Syntax/BigConj.lean:32`) — a real semantic refactor, not proof golf.
- Rewriting `simp only [Modal.Proposition.toBimodal, …]` sites to use the named `toBimodal_*`
  equation lemmas — behaviourally equivalent, zero line-count change, no action recommended.
- Any change to `bimodal_deriv_iff_algebraic` (`Bimodal/Metalogic/Core/GenericMCSBridge.lean:270-275`),
  which carries a maintainer note documenting why the generic assembler route fails.
- Adding or changing any `@[simp]` attribute anywhere — a simp-set change has global blast radius
  and needs its own task with its own gate.
- The large-scale duplication catalogued in the research appendix (cloned tableau soundness
  mega-proofs, `LoopChecking.lean` motifs, Bimodal soundness axiom-case clones, untagged `truthAt`
  characterisation lemmas, cross-directory clones, repeated hypothesis bundles). Each is a
  multi-hundred-line refactor with real regression risk and belongs in a separate task.

### When NOT to Simplify (mandatory acceptance criterion)

A shorter proof is not automatically a better proof. **Revert any individual site and keep the
original proof** if any of the following holds after the edit:

1. **It does not compile.** The original proofs are all sorry-free today and are the fallback. A
   failing site is reverted, not patched with `sorry`, not escalated to `[BLOCKED]`.
2. **Elaboration gets measurably slower.** If a replacement introduces a general search tactic
   where a defeq or a targeted rewrite sufficed, or if `lake build` of the module regresses
   noticeably, keep the original. Specifically: do **not** substitute `grind` or `aesop` at these
   sites — the normalization lemmas carry `scoped grind =`, so `grind` would close them, but
   invoking a search procedure where `exact` succeeds by defeq is a regression in both build time
   and reviewability.
3. **It becomes more fragile.** A replacement that depends on the ambient default `simp` set, on
   unification succeeding at a particular elaboration order, or on a `simp only [← …]` matching a
   `let`-bound hypothesis in a way that is not locally evident, is more brittle than the explicit
   original. Prefer `exact` and explicit `simp only` lemma lists over anything implicit.
4. **It destroys load-bearing explanation.** If deleting the line also deletes the only place a
   non-obvious defeq is documented, keep a one-line comment recording it (e.g. that
   `ListDeriv [] φ` is definitionally `DerivableIn S φ`) rather than leaving the reader with an
   unexplained `exact ih`.

Record every reverted site in the phase's Reasoned Exclusions table.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Sibling proof-golf task lands the same F1 edits first, causing merge conflicts or double work | M | H | Phase 2 idempotency guard: grep for `listImp_nil` in the three modal-family bridge files before editing; if absent, close the phase `[COMPLETED WITH EXCLUSIONS]` |
| Sibling task edits `Foundations/` in a way that changes what the modal-family bridges need | M | M | Phase 4 runs a **full** `lake build`, not a scoped one; the plan's Foundations Non-Goal means this task never races the sibling on the same file |
| `simpa using ih` substituted for `exact ih` out of habit | M | M | Research verified `simpa` fails with a type mismatch; the plan states `exact`, never `simpa`, at every F1 site. Plan-compliance rule applies |
| Implementer golfs the `box`/`diamond` arms | M | M | Explicit Non-Goal plus a verified negative result recorded in this plan; any attempt wastes a phase budget |
| Merged single-`simp only` form fails for the `or` case (verified only for `and`) | L | M | Phase 1 falls back to the verified two-step form (`simp only [← ih1 w, ← ih2 w]; tauto` after the existing line-176 `simp only`), which is confirmed working |
| Deleting a tactic line leaves "No goals to be solved" on the following line | L | M | Each F1 deletion is a paired edit: remove the normalization line *and* fold the `have h_thm` into the `exact`; verify per-site with `lean_goal` before committing |
| Comment loss during line deletion | L | M | Explicit task item in each edit phase to re-site surviving comments |
| A proof silently gains a `sorry` or an unexpected axiom | H | L | Per-phase `grep -n sorry` on touched files plus `lean_verify` on each touched declaration; repeated project-wide in Phase 4 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 2 |
| 3 | 4 | 1, 3 |

Phases within the same wave can execute in parallel. Phases 1 and 2 touch disjoint files with no
signature change in either, so they are genuinely independent. Phase 3 follows Phase 2 so the F1
edit shape is validated on one file before being replicated across two more.

---

### Phase 1: ModalConservativity `and` and `or` arms [NOT STARTED]

**Goal**: Replace the hand-rolled classical reasoning in the `and` and `or` arms of
`bimodal_truthAt_toBimodal_iff_satisfies` with the verified backward-IH-rewrite plus `tauto`,
leaving the `box` and `diamond` arms untouched.

**Tasks**:
- [ ] Record a baseline: `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity`
      must be green before any edit.
- [ ] Confirm the arm boundaries still match the plan (`and` at lines 164-174, `or` at 175-185,
      `box` starting at 186) — line numbers may have drifted.
- [ ] Replace the `and` arm body (currently lines 165-174) with the verified single line:
      `simp only [Modal.Proposition.toBimodal, Bimodal.Formula.and, truthAt, Modal.Satisfies,
      ← ih1 w, ← ih2 w]; tauto`
- [ ] Replace the `or` arm body with the merged single-`simp only` form matching the `and` shape
      (first attempt). If that fails, fall back to the verified two-step form: retain the existing
      `simp only [Modal.Proposition.toBimodal, Bimodal.Formula.or, truthAt, Modal.Satisfies]` line
      and replace the remainder with `simp only [← ih1 w, ← ih2 w]; tauto`.
- [ ] Use `lean_goal` after each replacement to confirm zero remaining goals in that arm and no
      "No goals to be solved" error on the following line.
- [ ] Do **not** touch the `box` (186-210) or `diamond` (211-229) arms.
- [ ] Apply the "When NOT to Simplify" criteria; revert any arm that fails and record it in a
      Reasoned Exclusions table under this phase.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: The research report asserts exactly two golfable arms in this file
(`and` at 164-174, `or` at 175-185, ~18 tactic lines removed) and asserts the `box`/`diamond` arms
are not golfable. Confirm at implementation time by reading
`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean:143-235` and
matching the `| and`, `| or`, `| box`, `| diamond` arm headers against these line ranges before
editing. If the arms have moved or an additional arm has appeared, re-derive the range from the
arm headers rather than trusting the numbers here.

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean` — proof bodies of
  the `and` and `or` arms of `bimodal_truthAt_toBimodal_iff_satisfies` only; no statement change.

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity` exits 0
  with no warnings introduced.
- `grep -n "sorry" Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean`
  returns nothing.
- `lean_verify` on the fully-qualified `bimodal_truthAt_toBimodal_iff_satisfies` (namespace
  `Cslib.Logic`; confirm the exact qualified name with `lean_local_search` first) reports no
  `sorryAx` and no unexpected axioms.
- The file's net line count decreases and the `box`/`diamond` arms are byte-identical to their
  pre-edit content (`git diff` shows no hunk in lines 186-229).

---

### Phase 2: Bimodal `GenericMCSBridge` redundant normalization [NOT STARTED]

**Goal**: Remove the redundant `unfold ListDeriv` / `simp only [listImp_nil]` pairs from the three
`necessitation`-family arms of `derivTreeToListFc` in the Bimodal core bridge, folding each
`have h_thm := by …` into the final `exact` where that reads better.

**Tasks**:
- [ ] **Idempotency guard (run first)**: `grep -n "listImp_nil"
      Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`. If it returns nothing, the
      sibling proof-golf task has already landed this change — close this phase
      `[COMPLETED WITH EXCLUSIONS]` with the guard result as evidence, make no edits, and proceed
      to Phase 3 (which carries the same guard for its own files).
- [ ] Baseline: `lake build Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge` green before
      editing.
- [ ] `necessitation` arm (lines 185-190): delete the `unfold ListDeriv; simp only [listImp_nil]`
      line entirely (verified: `exact ⟨Bimodal.DerivationTree.necessitation ψ h_thm.toDerivation⟩`
      closes the goal on its own), and replace the `have h_thm : … := by unfold ListDeriv at ih;
      simp only [listImp_nil] at ih; exact ih` block with `have h_thm : … := ih` — or inline `ih`
      into the `exact` if the `.toDerivation` projection still elaborates without the type
      ascription. Test both forms with `lean_multi_attempt`; keep whichever reads better and
      elaborates no slower.
- [ ] `temporal_necessitation` arm (lines 191-196): same treatment.
- [ ] `temporal_duality` arm (lines 197-204): same treatment, preserving the intermediate
      `have h_dual` which carries the `swapTemporal` type.
- [ ] Use `exact`, never `simpa` — `simpa using ih` is a verified failure at these sites.
- [ ] Re-site any surviving explanatory comment; if the defeq (`ListDeriv [] φ` is definitionally
      `DerivableIn S φ`) is no longer documented anywhere in the file, add a single-line comment
      recording it.
- [ ] Apply the "When NOT to Simplify" criteria per site; revert failures individually.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The research report enumerates six `listImp_nil` occurrences in this file
(lines 188, 189, 194, 195, 200, 203) across three arms, and reports 24 `unfold ListDeriv`
occurrences repo-wide of which only the enumerated modal-family ones are redundant (the rest
operate on non-empty contexts). Confirm at implementation time with
`grep -rn "listImp_nil\|unfold ListDeriv" Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`
and, for each hit, check with `lean_goal` that the context is literally `[]` before deleting.
Never delete an `unfold ListDeriv` on a non-empty context.

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — proof body of `derivTreeToListFc`
  only; no statement change, no change to `bimodal_deriv_iff_algebraic`.

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge` exits 0.
- `grep -n "sorry" Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` returns nothing.
- `lean_verify` on `derivTreeToListFc` and `derivTreeToList` in this module reports no `sorryAx`.
- `git diff --stat` shows a net line reduction confined to this one file.

---

### Phase 3: Temporal and Modal `GenericMCSBridge` redundant normalization [NOT STARTED]

**Goal**: Replicate the Phase 2 edit shape in the Temporal and Modal bridges, whose arms use the
same copy-pasted idiom with fewer sites.

**Tasks**:
- [ ] **Idempotency guard**: `grep -n "listImp_nil"` on both files. Close as
      `[COMPLETED WITH EXCLUSIONS]` for any file where the change has already landed.
- [ ] Baseline: `lake build Cslib.Logics.Temporal.Metalogic.GenericMCSBridge` and
      `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` green before editing.
- [ ] `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — `temporal_necessitation` arm
      (lines 166-171) and `temporal_duality` arm (172-179): apply the Phase 2 shape.
- [ ] `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` — `necessitation` arm (lines 132-143):
      apply the Phase 2 shape. This arm spreads the idiom over five separate lines
      (136, 137, 138, 140, 141) rather than two, so confirm each deletion individually.
- [ ] Preserve the explanatory comments at `Modal/…/GenericMCSBridge.lean:133, 139, 142`, re-sited
      to the surviving tactic lines where they still apply.
- [ ] Leave the `unfold ListDeriv` at `Temporal/…:158` alone — it precedes
      `exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm` on a **non-empty** context `Γ` and is not
      part of the redundant idiom. The same holds for the corresponding site in the Bimodal file
      (line 177).
- [ ] Apply the "When NOT to Simplify" criteria per site.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The research report enumerates four `listImp_nil` sites in the Temporal
bridge (169, 170, 175, 178) and two in the Modal bridge (137, 141), for six sites across two
files, and asserts that the non-empty-context `unfold ListDeriv` sites (e.g. `Temporal/…:158`)
must be preserved. Confirm at implementation time by grepping both files and checking each hit's
context with `lean_goal`. Do not assume the Modal file's arm structure mirrors the Temporal one —
the Modal bridge has no `temporal_duality` arm.

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — proof body of `derivTreeToListFc` only.
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` — proof body of `derivTreeToList` only.

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.GenericMCSBridge` and
  `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` both exit 0.
- `grep -n "sorry"` on both files returns nothing.
- `lean_verify` on `derivTreeToListFc` / `derivTreeToList` in each module reports no `sorryAx`.
- `grep -rn "unfold ListDeriv" Cslib/Logics/` shows only non-empty-context sites remaining.

---

### Phase 4: Project-wide gate and sorry-freeness audit [NOT STARTED]

**Goal**: Confirm the accumulated proof-body edits break nothing anywhere in the project and that
no touched declaration acquired a `sorry` or an unexpected axiom.

**Tasks**:
- [ ] `lake exe cache get` if the Mathlib cache is cold.
- [ ] Full `lake build` — green, with no new warnings relative to the pre-task baseline.
- [ ] `lake exe checkInitImports`.
- [ ] `lake lint`.
- [ ] `lake exe lint-style`.
- [ ] `lake test`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — expect no import removals (the
      *statements* still depend on `listImp`, so no import becomes redundant); investigate if it
      reports any.
- [ ] Sorry/axiom audit: `grep -rn "sorry" ` over the four touched files, plus `lean_verify` on
      every touched declaration (`bimodal_truthAt_toBimodal_iff_satisfies`, and the
      `derivTreeToList*` lemmas in the three bridges), confirming no `sorryAx`.
- [ ] Diff review: `git diff` must contain only proof-body hunks. Any hunk touching a `theorem`/
      `lemma`/`def` statement line, an attribute, or an import is a scope violation and must be
      reverted.
- [ ] Confirm no file under `Cslib/Foundations/` or `Cslib/Logics/Propositional/` appears in the
      diff (sibling territory).
- [ ] Record the total tactic-line reduction and any reverted sites for the task summary.

**Timing**: 1 hour

**Depends on**: 1, 3

**Verification Tier**: full

**Scope Hypothesis**: This plan asserts exactly four modified files
(`ModalConservativity.lean` plus the three `GenericMCSBridge.lean` files) and roughly 30 tactic
lines removed. Confirm with `git diff --stat` at phase start; a fifth modified file or a
statement-line hunk indicates scope drift and must be reconciled before the gate is declared
passing.

**Files to modify**: none (verification only; any edit here is a revert of a Phase 1-3 site that
failed the gate).

**Verification**:
- All seven CI steps exit 0.
- `git diff --stat` lists at most the four expected files, all under `Cslib/Logics/{Modal,Temporal,Bimodal}/`.
- Zero `sorry` occurrences and zero `sorryAx` axioms in the touched declarations.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity` green.
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge` green.
- [ ] `lake build Cslib.Logics.Temporal.Metalogic.GenericMCSBridge` green.
- [ ] `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` green.
- [ ] Full `lake build` green.
- [ ] `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`,
      `lake shake --add-public --keep-implied --keep-prefix` all pass.
- [ ] Every touched declaration confirmed sorry-free and axiom-clean via `lean_verify`.
- [ ] `git diff` contains proof-body hunks only — no statement, attribute, or import changes.
- [ ] `ModalConservativity.lean` lines 186-229 (`box`/`diamond` arms) unchanged.
- [ ] No file under `Cslib/Foundations/` or `Cslib/Logics/Propositional/` modified.

## Artifacts & Outputs

- `specs/414_simplify_proofs_normalization_modal_family/plans/01_modal-family-proof-golf.md` (this file)
- `specs/414_simplify_proofs_normalization_modal_family/summaries/01_modal-family-proof-golf-summary.md`
  (produced by `/implement`)
- Modified: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean`
- Modified: `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`
- Modified: `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`
- Modified: `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`

## Rollback/Contingency

Every change is a proof-body edit with a binary outcome: the site compiles or it does not. There
is no partial-completion failure mode and no site warrants a `[BLOCKED]` escalation.

- **Per-site failure**: revert that one site with `git checkout -p` (or re-type the original from
  the diff) and record it in the phase's Reasoned Exclusions table. The original proof is
  sorry-free today and is always the fallback.
- **Per-phase failure**: `git revert` the phase's commit(s). Because each phase is scoped to
  disjoint files, reverting one phase never disturbs another.
- **Whole-task rollback**: revert all phase commits. The repository returns to a state that is
  known green, with zero semantic change — no declaration, statement, attribute, or import was
  altered at any point.
- **Sibling-task conflict**: if the sibling proof-golf task lands the same F1 edits mid-flight,
  prefer whichever landed first and close the affected phase `[COMPLETED WITH EXCLUSIONS]`. Do not
  revert the sibling's work to re-apply this task's version — the edits are textually equivalent.
