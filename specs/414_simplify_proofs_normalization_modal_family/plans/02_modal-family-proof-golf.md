# Implementation Plan: Simplify Modal/Temporal/Bimodal Proofs via Existing Normalization Lemmas (v2)

- **Task**: 414 - simplify_proofs_normalization_modal_family
- **Status**: [NOT STARTED]
- **Effort**: 2 hours
- **Dependencies**: None blocking. The task entry in `specs/state.json` declares
  `depends_on: [180, 181, 215, 241, 275, 299, 300, 301, 321]`; see "Dependency Reassessment"
  below for the per-entry assessment and why none of them gates the remaining work. This plan
  does not edit `state.json`. The only live constraint is a **concurrency** constraint against
  an in-flight tableau task -- see "Concurrency Constraint" below.
- **Research Inputs**: `specs/414_simplify_proofs_normalization_modal_family/reports/01_simplify-modal-family-proofs.md`
  (no new research reports since v1; this revision is driven by an external ground-truth change,
  see "Research Integration")
- **Artifacts**: plans/02_modal-family-proof-golf.md (this file);
  plans/01_modal-family-proof-golf.md (superseded, preserved unchanged as history)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md;
  `.claude/rules/cslib.md`; `.claude/rules/lean4.md`; `.claude/rules/plan-compliance.md`
- **Type**: cslib
- **Lean Intent**: true

## Overview

Plan v1 targeted two independent change families in `Cslib/Logics/{Modal,Temporal,Bimodal}/`:
(F1) redundant `unfold ListDeriv` / `simp only [listImp_nil]` normalization pairs in the three
`GenericMCSBridge.lean` files, and (F2) the hand-rolled classical reasoning in the `and`/`or`
arms of `bimodal_truthAt_toBimodal_iff_satisfies` in `ModalConservativity.lean`. **F1 has since
been fully landed by the sibling proof-golf task, whose scope turned out to be repo-wide rather
than `Propositional/`-only.** This revision retires the F1 phases as
`[COMPLETED WITH EXCLUSIONS]` on verified evidence and narrows the task to F2 plus a final gate.
No new declarations, no signature changes, no attribute changes, no new axioms. Definition of
done: the one touched module builds, the repo-wide gate set passes (with concurrent-activity
attribution, below), and every touched declaration is confirmed sorry-free and axiom-clean.

### Research Integration

No research reports have been produced since plan v1. `reports/01_simplify-modal-family-proofs.md`
remains the sole research input and is carried forward unchanged. This revision is instead driven
by an **external ground-truth change**: the sibling proof-golf task landed its change set in
commits `8e6d10ad`..`7d0c2313` (phases 1-7), removing all 20 redundant
`simp only [listImp_*|bigconj_*]` rewrite invocations plus 19 accompanying `unfold ListDeriv`
lines across 8 files and adding four defeq-reliance doc comments to the `derivTreeToList*` bridge
lemmas. Final diffstat of that change set: 8 files changed, 35(+), 74(-).

Three of this plan's four target files were among the sibling's 8 modified files:

| File | v1 phase | In sibling's diffstat |
|---|---|---|
| `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` | Phase 2 | yes (32 lines changed) |
| `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` | Phase 3 | yes (22 lines changed) |
| `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` | Phase 3 | yes (26 lines changed) |
| `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean` | Phase 1 | **no** |

Direct verification performed at revision time (not inherited from the delegation context):

- `grep -nE 'simp only \[[^]]*(listImp_|bigconj_|toTemporal_|toBimodal_)'` over all four target
  files returns **zero** matches.
- `grep -n 'unfold ListDeriv'` over all four target files returns **zero** matches.
- `grep -n 'listImp_nil'` over all four target files returns **zero** matches.
- The embedding-lemma family (`toTemporal_*` / `toBimodal_*`) was inspected directly, not only
  by the combined grep. The only surviving `toBimodal_*` `simp only` sites anywhere in the modal
  family are `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean:185,188`
  (`Temporal.Formula.toBimodal_allFuture` / `toBimodal_allPast`). These are already in the
  **named equation-lemma** form that v1's Non-Goals identified as the target form, not a golfable
  antipattern -- so there is no residual `toTemporal_*`/`toBimodal_*` work in scope.
- Surviving `listImp` references in the three bridge files are docstring prose plus the
  `listImp_axiom_k` non-empty-context sites (Bimodal:181, Modal:128, Temporal:162), which v1
  explicitly designated as must-preserve real work, and the `unfold bimodalDerivationSystem`
  / `unfold temporalDerivationSystem` lines inside `bimodal_deriv_iff_algebraic` and its Temporal
  counterpart, which v1 designated an explicit Non-Goal.

Consequence: **v1 Phases 2 and 3 have no remaining work**, and are closed as
`[COMPLETED WITH EXCLUSIONS]` rather than deleted, so the record of what was in scope and why it
is now out of scope survives. **v1 Phase 1 (F2) is unaffected** -- its file was not in the
sibling's diffstat, and its concern (hand-rolled classical reasoning) is a different concern from
the `simp only` normalization lists the sibling removed.

### Line-Range Re-Verification (Phase 1)

`ModalConservativity.lean` was re-read at revision time to confirm the sibling task did not shift
its line numbers. It did not -- the file is unmodified since `d5b6da26` (an upstream merge), and
every v1 arm range still holds exactly:

| Arm | Range | Confirmed anchor |
|---|---|---|
| `and φ ψ ih1 ih2` | 164-174 | `\| and φ ψ ih1 ih2 =>` at line 164 |
| `or φ ψ ih1 ih2` | 175-185 | `\| or φ ψ ih1 ih2 =>` at line 175 |
| `box φ ih` | 186-210 | `\| box φ ih =>` at line 186 |
| `diamond φ ih` | 211-229 | `\| diamond φ ih =>` at line 211 |

The theorem statement spans lines 143-153; the induction opens at 154. The arm-header
re-derivation instruction from v1 is retained in Phase 1 anyway, because these numbers are a
hypothesis about a file another session could still touch, not a fact frozen at revision time.

### Prior Plan Reference

`plans/01_modal-family-proof-golf.md` (v1). Superseded by this file; preserved unchanged. This
revision preserves v1's Phase 1 substantively intact, retires v1 Phases 2 and 3 on evidence, and
narrows v1 Phase 4's gate to a single-file diff surface with an added concurrency-attribution
protocol.

### Sibling-Task Territory Split (resolved)

v1 declared a territory split against the sibling proof-golf task, anticipating a collision on
the three `GenericMCSBridge` files. **That collision resolved in the sibling's favor**: it landed
first and its scope was repo-wide, so it took the F1 sites in all four bridges including the three
modal-family ones. v1's Phase 2 idempotency guard is exactly the mechanism that was supposed to
detect this, and it has now fired -- at revision time rather than implementation time. The split
is recorded here as history; it constrains nothing further, because this plan's remaining edit
surface (`ModalConservativity.lean`) was never contested.

The `Cslib/Foundations/**` and `Cslib/Logics/Propositional/**` Non-Goals from v1 are retained
below, now doubly justified: they were sibling territory then, and the sibling has since
completed them.

### Concurrency Constraint

**An orchestrated hard-mode run for the tableau/blocking task is live in another session at the
time of writing.** It holds a task lock, works under `Cslib/Logics/*/Tableau/*`, and commits to
`main` as it goes (most recent observed commits: `6aab037a`, `0a1cea04`, `c5f108e5`, `178cd446`,
`659c713c`). This imposes two hard constraints on this plan:

1. **Territory**: this plan MUST NOT touch any file under any `Tableau/` directory. Its entire
   remaining edit surface is one file under `Bimodal/Metalogic/ConservativeExtension/`, which is
   disjoint from tableau territory. Any diff hunk landing under `Tableau/` is a territory
   violation and must be reverted immediately, not reconciled.

2. **Attribution before blame**: `lake build`, `lake test`, `lake lint`, `lake exe lint-style`,
   and `lake shake` are repo-wide and will compile the other session's in-flight tableau code. A
   repo-wide failure is therefore **not** evidence that this task's edit broke something. Before
   treating any gate failure as caused by this task, run the attribution protocol in Phase 4.

   Concretely: the other session has already introduced at least one new `sorry` under
   `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (its phase 4.3 commit
   `178cd446` records "track temporary sorry at Scheme.lean reuse-site discharge"), so the
   repo-wide `sorry`-warning count is a **moving target owned by another session** and is not a
   valid pass/fail signal for this task.

### Sorry Baseline (corrected)

v1 assumed the repo's pre-existing `sorry` baseline was 4 warnings across 3 files. **That is
wrong.** The sibling task's Phase 1 baseline capture
(`specs/413_simplify_proofs_normalization_propositional/baseline.md`) measured the observed
full-build baseline as **5 warnings across 4 files**:

| File:line:col |
|---|
| `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1252:6` |
| `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:570:6` |
| `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:2583:14` |
| `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:124:8` |
| `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:118:8` |

The fifth (`FrameSoundness.lean:1252`) is documented in-source as retained by explicit user
decision. **Any audit in this plan compares against 5, not 4.**

Two further cautions, both consequences of the concurrency constraint:

- Every one of those five sites is under a `Tableau/` directory -- i.e. entirely inside the other
  session's territory and entirely outside this task's.
- The line numbers above have already drifted (`Scheme.lean` now carries `sorry` occurrences at
  different lines than 570/2583) and the count may exceed 5 while the other session is running.
  **Therefore the plan's binding sorry-freeness criterion is file-scoped, not repo-scoped**: the
  four files this task ever claimed must contain zero `sorry`, and the touched declaration must
  be `lean_verify`-clean. The repo-wide count is recorded for attribution only, never as a gate.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only. Unchanged from v1: this is lower-priority proof-golf
maintenance advancing no dedicated roadmap milestone. Its scope is now roughly half of v1's, since
the sibling task delivered the F1 half.

### Dependency Reassessment

The task entry declares `depends_on: [180, 181, 215, 241, 275, 299, 300, 301, 321]`. Observed
statuses at revision time:

| Task | Status | Bears on remaining Phase-1 work? |
|---|---|---|
| 180 | not present in `specs/state.json` (completed/archived or removed) | no |
| 181 | `not_started` | no |
| 215 | `blocked` | no |
| 241 | not present in `specs/state.json` | no |
| 275 | not present in `specs/state.json` | no |
| 299 | not present in `specs/state.json` | no |
| 300 | `blocked` | no |
| 301 | `blocked` | no |
| 321 | not present in `specs/state.json` | no |

**Assessment**: none of these gates the remaining work. Phase 1 is a proof-body-only edit to
`bimodal_truthAt_toBimodal_iff_satisfies`, a theorem that is sorry-free and green in the tree
today; the replacement tactic was LSP-verified by the research report against this same tree. No
blocked task's deliverable is an input to the `and`/`or` arms, and no unblocking is required for
the edit to elaborate. The three `blocked` entries (215, 300, 301) concern filling Bimodal
sorries, modal extension systems, and the temporal tableau respectively -- none of which appears
in the target theorem's dependency cone.

**Recommendation**: the `depends_on` array is stale and over-broad for what remains of this task.
It should be narrowed or cleared. **This plan does not edit `state.json`** -- that is the calling
skill's or a maintainer's decision, recorded here rather than silently applied.

## Goals & Non-Goals

**Goals**:

- Collapse the `and` and `or` arms of `bimodal_truthAt_toBimodal_iff_satisfies` in
  `ModalConservativity.lean` to the verified one-line `simp only [… ← ih1 w, ← ih2 w]; tauto` form.
- Keep every touched proof sorry-free and axiom-clean, verified per phase and again at the end.
- Preserve every explanatory comment whose content survives the edit, re-sited to the surviving
  tactic line.
- Close the retired F1 phases with an auditable evidence record rather than deleting them.

**Non-Goals**:

- The three `GenericMCSBridge.lean` files. The sibling proof-golf task landed every F1 edit this
  plan ever claimed in them; verified zero residual sites (see Research Integration).
- The `box` and `diamond` arms of `bimodal_truthAt_toBimodal_iff_satisfies`
  (`ModalConservativity.lean:186-229`) -- verified dead end in the research report
  (`simp only [← ih w]` reports "simp made no progress"; the
  `kripkeAdapterOmega_eq_of_accessible` transport steps are load-bearing). Leave all 44 lines
  alone.
- **Any file under any `Tableau/` directory.** Held by a concurrent session; see Concurrency
  Constraint.
- Adding a `listDeriv_nil` lemma to `Foundations/Logic/Metalogic/ListDeduction.lean` -- explicitly
  recommended against by the research report (no consumers after F1; plausible `simpNF` offender).
- Any edit under `Cslib/Foundations/**` or `Cslib/Logics/Propositional/**`.
- The two `toBimodal_*` sites at `TemporalConservativity.lean:185,188` -- already in the named
  equation-lemma form; rewriting them is a no-op.
- Unifying the two coexisting `bigconj` definitions (`Foundations/Logic/Theorems/BigConj.lean:60`
  vs `Logics/Temporal/Syntax/BigConj.lean:32`) -- a semantic refactor, not proof golf.
- Any change to `bimodal_deriv_iff_algebraic` or its Temporal counterpart, both of which carry
  maintainer notes documenting why the generic assembler route fails.
- Adding or changing any `@[simp]` attribute anywhere -- global blast radius; needs its own task
  and its own gate.
- The large-scale duplication catalogued in the research appendix (cloned tableau soundness
  mega-proofs, `LoopChecking.lean` motifs, Bimodal soundness axiom-case clones, untagged
  `truthAt` characterisation lemmas, cross-directory clones, repeated hypothesis bundles). Each is
  a multi-hundred-line refactor with real regression risk and belongs in a separate task -- and
  the tableau ones are additionally in another session's territory right now.

### When NOT to Simplify (mandatory acceptance criterion)

Carried forward from v1 unchanged. A shorter proof is not automatically a better proof.
**Revert the site and keep the original proof** if any of the following holds after the edit:

1. **It does not compile.** The original proof is sorry-free today and is the fallback. A failing
   site is reverted, not patched with `sorry`, not escalated to `[BLOCKED]`.
2. **Elaboration gets measurably slower.** Do **not** substitute `grind` or `aesop` -- the
   normalization lemmas carry `scoped grind =`, so `grind` would close them, but invoking a search
   procedure where a targeted rewrite suffices is a regression in both build time and
   reviewability.
3. **It becomes more fragile.** A replacement depending on the ambient default `simp` set, on
   unification succeeding at a particular elaboration order, or on a `simp only [← …]` matching a
   `let`-bound hypothesis in a way that is not locally evident, is more brittle than the explicit
   original.
4. **It destroys load-bearing explanation.** If deleting a line also deletes the only place a
   non-obvious fact is documented, keep a one-line comment recording it.

Record every reverted site in the phase's Reasoned Exclusions table.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Repo-wide gate fails because of the concurrent tableau session, and the failure is misattributed to this task | H | H | Phase 4 attribution protocol: `git diff --stat` this task's own hunks first; check whether the failing module is under `Tableau/`; re-run the failing gate at the last commit that predates the other session's newest commit if needed. Never revert a Phase-1 edit on an unattributed repo-wide failure |
| Repo-wide `sorry` count exceeds the 5-warning baseline because the other session added one | M | H | The binding sorry criterion is file-scoped (four named files must be `sorry`-free) plus `lean_verify` on the touched declaration. The repo-wide count is recorded, never gated on. The known drift (`Scheme.lean`, commit `178cd446`) is pre-attributed |
| Implementer treats the retired Phases 2-3 as work to redo, re-applying or reverting sibling edits | M | M | Phases 2 and 3 carry `[COMPLETED WITH EXCLUSIONS]` headings with Reasoned Exclusions tables citing the sibling's commit range and the zero-match grep evidence. Their Tasks lists are empty by construction |
| Merged single-`simp only` form fails for the `or` case (research verified only the `and` case) | L | M | Phase 1 falls back to the verified two-step form: retain the existing line-176 `simp only` and replace the remainder with `simp only [← ih1 w, ← ih2 w]; tauto` |
| `rw [← ih1 w, ← ih2 w]` substituted for `simp only [← …]` out of habit | M | M | Research verified `rw` **fails** -- the induction hypotheses are `let`-bound. The plan states `simp only [← …]`, never `rw`, at both sites. Plan-compliance rule applies |
| Implementer golfs the `box`/`diamond` arms | M | M | Explicit Non-Goal plus a verified negative result recorded in v1 and carried forward. Phase 1 verification requires `git diff` to show no hunk in lines 186-229 |
| Line numbers drift because another session touches `ModalConservativity.lean` mid-flight | L | L | Phase 1 opens by re-deriving arm ranges from the `\| and` / `\| or` / `\| box` arm headers rather than trusting the table above. The file is outside the concurrent session's declared territory, so this is unlikely but cheap to guard |
| Comment loss during line deletion | L | M | Explicit task item to re-site surviving comments |
| A proof silently gains a `sorry` or an unexpected axiom | H | L | Per-phase `grep -n sorry` on the touched file plus `lean_verify` on the touched declaration; repeated in Phase 4 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1 |

Phases within the same wave can execute in parallel. Phases 2 and 3 are already closed
(`[COMPLETED WITH EXCLUSIONS]`) at plan-revision time and carry no executable work, so Wave 1 is
in practice Phase 1 alone. Phase 4's `Depends on` was narrowed from v1's `1, 3` to `1`, because
Phase 3 no longer produces anything for the gate to check.

Phase numbering is preserved from v1 so the two plan versions are diffable arm-for-arm.

---

### Phase 1: ModalConservativity `and` and `or` arms [NOT STARTED]

**Goal**: Replace the hand-rolled classical reasoning in the `and` and `or` arms of
`bimodal_truthAt_toBimodal_iff_satisfies` with the verified backward-IH-rewrite plus `tauto`,
leaving the `box` and `diamond` arms untouched.

**Tasks**:
- [ ] Record a baseline: `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity`
      must be green before any edit.
- [ ] Re-derive the arm boundaries from the arm headers (`| and`, `| or`, `| box`, `| diamond`),
      not from the line numbers in this document. The revision-time reading has `and` at 164-174,
      `or` at 175-185, `box` starting at 186, `diamond` at 211 -- confirm, do not assume.
- [ ] Replace the `and` arm body (currently lines 165-174, i.e. everything after the arm header)
      with the verified single line:
      `simp only [Modal.Proposition.toBimodal, Bimodal.Formula.and, truthAt, Modal.Satisfies,
      ← ih1 w, ← ih2 w]; tauto`
- [ ] Replace the `or` arm body with the merged single-`simp only` form matching the `and` shape
      (first attempt), substituting `Bimodal.Formula.or` for `Bimodal.Formula.and`. If that
      fails, fall back to the verified two-step form: retain the existing
      `simp only [Modal.Proposition.toBimodal, Bimodal.Formula.or, truthAt, Modal.Satisfies]`
      line and replace the remainder with `simp only [← ih1 w, ← ih2 w]; tauto`.
- [ ] Use `simp only [← …]`, never `rw [← …]` -- `rw` is a verified failure here because the
      induction hypotheses are `let`-bound.
- [ ] Use `lean_multi_attempt` before applying each edit, then `lean_goal` after each replacement,
      to confirm zero remaining goals in that arm and no "No goals to be solved" error on the
      following line.
- [ ] Do **not** touch the `box` or `diamond` arms.
- [ ] Do **not** touch any file under a `Tableau/` directory (concurrent-session territory).
- [ ] Apply the "When NOT to Simplify" criteria; revert any arm that fails and record it in a
      `#### Reasoned Exclusions` table under this phase.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts exactly two golfable arms in exactly one file
(`and` at 164-174, `or` at 175-185; ~18 tactic lines removed) and asserts the `box`/`diamond`
arms are not golfable. These ranges were re-verified at plan-revision time against the current
file and matched exactly; the file is unmodified since the upstream-merge commit `d5b6da26`.
Re-confirm at implementation time by reading
`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean:143-235` and
matching the `| and`, `| or`, `| box`, `| diamond` arm headers before editing. If the arms have
moved or an additional arm has appeared, re-derive the ranges from the arm headers rather than
trusting the numbers here.

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean` — proof bodies of
  the `and` and `or` arms of `bimodal_truthAt_toBimodal_iff_satisfies` only; no statement change.

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity` exits 0
  with no warnings introduced. This scoped build is the phase's binding signal -- it is unaffected
  by the concurrent tableau session, since `ModalConservativity` does not import tableau code.
- `grep -n "sorry" Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean`
  returns nothing.
- `lean_verify` on the fully-qualified `bimodal_truthAt_toBimodal_iff_satisfies` (confirm the
  exact qualified name with `lean_local_search` first) reports no `sorryAx` and no unexpected
  axioms.
- The file's net line count decreases and the `box`/`diamond` arms are byte-identical to their
  pre-edit content (`git diff` shows no hunk in the `box`/`diamond` range).
- `git diff --stat` lists exactly one file.

---

### Phase 2: Bimodal `GenericMCSBridge` redundant normalization [COMPLETED WITH EXCLUSIONS]

**Goal** (original): Remove the redundant `unfold ListDeriv` / `simp only [listImp_nil]` pairs
from the three `necessitation`-family arms of `derivTreeToListFc` in the Bimodal core bridge.

**Outcome**: No work remains. The sibling proof-golf task landed this exact change set in
`Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` (32 lines changed) as part of its
phases 4-6. v1's own idempotency guard is what closes this phase -- it fired at plan-revision
time rather than at implementation time. Every item v1 enumerated for this file was verified
absent from the current tree. **Make no edits to this file.** In particular, do not re-apply
this plan's version of the edit and do not revert the sibling's -- the results are textually
equivalent and the sibling's landed first.

**Tasks**: none (all items closed by the Reasoned Exclusions below).

#### Reasoned Exclusions

| Item | Reason | Evidence |
|------|--------|----------|
| `listImp_nil` sites (v1 enumerated lines 188, 189, 194, 195, 200, 203) | Already removed by the sibling proof-golf task; nothing left to delete | `grep -n 'listImp_nil' Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` -> zero matches. Sibling commits `8e6d10ad`..`7d0c2313`; file appears in that range's diffstat with 32 lines changed |
| Redundant `unfold ListDeriv` lines in the `necessitation` / `temporal_necessitation` / `temporal_duality` arms | Already removed by the sibling task, which deleted 19 such lines repo-wide | `grep -n 'unfold ListDeriv' Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` -> zero matches |
| Any residual `simp only [listImp_*\|bigconj_*\|toTemporal_*\|toBimodal_*]` normalization site in this file | None exists | `grep -nE 'simp only \[[^]]*(listImp_\|bigconj_\|toTemporal_\|toBimodal_)'` on this file -> zero matches |
| Documenting the `ListDeriv [] φ` = `DerivableIn S φ` defeq (v1 task item: add a comment if the defeq is no longer documented) | Already done by the sibling task, which added four defeq-reliance doc comments to the `derivTreeToList*` bridge lemmas | Sibling commit `c89839e9` ("fragility adjudication and defeq documentation"); surviving prose at this file's lines 34-49, 167-170 documents the definitional-equality chain |
| Non-empty-context `unfold ListDeriv` at v1's cited line 177 (`listImp_axiom_k` site) | Deliberately preserved by v1 as real work, not the redundant idiom; the surviving site is now `exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm` at line 181 with the `unfold` no longer needed | Line 181 of the current file; no `unfold ListDeriv` remains anywhere in the file |
| `bimodal_deriv_iff_algebraic` | Explicit v1 Non-Goal (carries a maintainer note on why the generic assembler route fails); untouched by the sibling task's proof-body edits | `unfold bimodalDerivationSystem Bimodal.Deriv` still present at line 266, unchanged |

**Timing**: 0 (closed at plan revision)

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts **zero** remaining golfable sites in
`Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`. Confirmed at plan-revision time by
the three zero-match greps in the Evidence column above. Re-confirm cheaply at implementation
time by re-running
`grep -nE 'listImp_nil|unfold ListDeriv|simp only \[[^]]*(listImp_|bigconj_|toTemporal_|toBimodal_)' Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`.
A non-empty result means the tree changed after this revision and the phase must be reopened
rather than trusted closed.

**Files to modify**: none.

**Verification**:
- The three greps in the Scope Hypothesis return zero matches.
- `git diff --stat` shows no hunk in this file attributable to this task.

---

### Phase 3: Temporal and Modal `GenericMCSBridge` redundant normalization [COMPLETED WITH EXCLUSIONS]

**Goal** (original): Replicate the Phase 2 edit shape in the Temporal and Modal bridges.

**Outcome**: No work remains. Both files were in the sibling proof-golf task's diffstat
(Modal: 22 lines changed; Temporal: 26 lines changed) and both were verified free of every site
v1 enumerated. **Make no edits to either file.**

**Tasks**: none (all items closed by the Reasoned Exclusions below).

#### Reasoned Exclusions

| Item | Reason | Evidence |
|------|--------|----------|
| Temporal bridge `listImp_nil` sites (v1 enumerated lines 169, 170, 175, 178) | Already removed by the sibling task | `grep -n 'listImp_nil' Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` -> zero matches; file in sibling diffstat with 26 lines changed (commit `a1972cc1`) |
| Modal bridge `listImp_nil` sites (v1 enumerated lines 137, 141) | Already removed by the sibling task | `grep -n 'listImp_nil' Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` -> zero matches; file in sibling diffstat with 22 lines changed (commit `a3e8a6b3`) |
| Redundant `unfold ListDeriv` in both files (v1: Temporal `temporal_necessitation` 166-171 and `temporal_duality` 172-179; Modal `necessitation` 132-143 spread over lines 136-141) | Already removed by the sibling task | `grep -n 'unfold ListDeriv'` on both files -> zero matches |
| Any residual `simp only [listImp_*\|bigconj_*\|toTemporal_*\|toBimodal_*]` in either file | None exists. The `toTemporal_*`/`toBimodal_*` embedding-lemma family was inspected directly, not only via the combined grep | `grep -nE 'simp only \[[^]]*(listImp_\|bigconj_\|toTemporal_\|toBimodal_)'` on both files -> zero matches. Repo-wide, the only surviving `toBimodal_*` `simp only` sites are `TemporalConservativity.lean:185,188`, which are already in the named-equation-lemma form v1 designated as the target, not a golfable antipattern |
| Preserving the explanatory comments v1 cited at `Modal/…/GenericMCSBridge.lean:133, 139, 142` | Preserved and re-sited by the sibling task as part of its defeq-documentation work | Current Modal bridge lines 115 and 127-128 carry the surviving defeq prose and the K-weakening comment; sibling commit `c89839e9` |
| Non-empty-context sites v1 required be left alone (`Temporal/…:158`, and the Modal analogue) | Deliberately preserved; the sibling task's scope was likewise limited to the empty-context idiom | `listImp_axiom_k` sites survive at `Temporal/…:162` and `Modal/…:128`; no `unfold ListDeriv` remains in either file |

**Timing**: 0 (closed at plan revision)

**Depends on**: 2

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts **zero** remaining golfable sites across exactly two
files (`Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`,
`Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`). Confirmed at plan-revision time by the
zero-match greps in the Evidence column. Re-confirm at implementation time by re-running the same
greps over both files; a non-empty result means the tree changed after this revision and the
phase must be reopened.

**Files to modify**: none.

**Verification**:
- The greps in the Scope Hypothesis return zero matches on both files.
- `git diff --stat` shows no hunk in either file attributable to this task.

---

### Phase 4: Gate and sorry-freeness audit [NOT STARTED]

**Goal**: Confirm the Phase 1 proof-body edit breaks nothing, that no touched declaration acquired
a `sorry` or an unexpected axiom, and that any repo-wide gate failure is correctly attributed
between this task and the concurrent tableau session before any revert decision is taken.

**Tasks**:

*File-scoped audit (binding):*
- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity` green.
- [ ] `grep -n "sorry"` returns nothing on all four files this task ever claimed:
      `ModalConservativity.lean` and the three `GenericMCSBridge.lean` files.
- [ ] `lean_verify` on `bimodal_truthAt_toBimodal_iff_satisfies` reports no `sorryAx` and no
      unexpected axioms.
- [ ] `git diff --stat` lists exactly one modified source file
      (`ModalConservativity.lean`). Any second source file is scope drift and must be reconciled
      before the gate is declared passing.
- [ ] `git diff` contains proof-body hunks only. Any hunk touching a `theorem`/`lemma`/`def`
      statement line, an attribute, or an import is a scope violation and must be reverted.
- [ ] Confirm no hunk under any `Tableau/` directory, under `Cslib/Foundations/`, or under
      `Cslib/Logics/Propositional/`.
- [ ] Confirm the `box`/`diamond` arms of `bimodal_truthAt_toBimodal_iff_satisfies` are
      byte-identical to their pre-task content.

*Repo-wide gate (run, but attribution-gated):*
- [ ] `lake exe cache get` if the Mathlib cache is cold.
- [ ] Full `lake build`.
- [ ] `lake exe checkInitImports`.
- [ ] `lake lint`.
- [ ] `lake exe lint-style`.
- [ ] `lake test`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — expect no import removals (the
      *statements* still depend on `truthAt` and the embedding, so no import becomes redundant);
      investigate if it reports any.

*Attribution protocol (run before treating ANY repo-wide failure as caused by this task):*
- [ ] Identify the failing module. If it lives under any `Tableau/` directory, it is the
      concurrent session's territory: record the failure, do **not** revert any Phase-1 edit, and
      do not block this task on it.
- [ ] Check whether the failing module transitively imports
      `Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity`. If it does not,
      this task's edit cannot be the cause.
- [ ] If still ambiguous, `git stash` this task's edit and re-run the single failing gate. A
      failure that persists without this task's edit is not this task's failure.
- [ ] Record the repo-wide `sorry`-warning count for information. The reference baseline is
      **5 warnings across 4 files** (`Modal/Tableau/FrameSoundness.lean:1252`,
      `Propositional/Tableau/Intuitionistic/Scheme.lean` x2,
      `Propositional/Tableau/Intuitionistic/Completeness.lean`,
      `Propositional/Tableau/Minimal/Completeness.lean`) — **not 4**. A count above 5 is expected
      while the concurrent session runs: it has already recorded a new temporary `sorry` under
      `Scheme.lean` (its commit `178cd446`). All five baseline sites and the new one are under
      `Tableau/`, i.e. entirely outside this task's territory. **This count is never a pass/fail
      gate for this task**; the file-scoped audit above is.
- [ ] Record the total tactic-line reduction and any reverted sites for the task summary.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This plan asserts exactly **one** modified source file
(`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean`) and roughly 18
tactic lines removed — down from v1's four-file / ~30-line assertion, because the sibling
proof-golf task delivered the other three files. Confirm with `git diff --stat` at phase start.
A second modified source file, or a statement-line hunk, indicates scope drift and must be
reconciled before the gate is declared passing. Note that `git status` will show unrelated
modifications from the concurrent tableau session; scope this check to this task's own staged
paths, never to the whole working tree.

**Files to modify**: none (verification only; any edit here is a revert of a Phase-1 site that
failed the gate).

**Verification**:
- The full file-scoped audit above passes in its entirety. This is the binding criterion.
- All seven repo-wide CI steps exit 0, **or** every failure is attributed to the concurrent
  tableau session by the attribution protocol and recorded as such.
- `git diff --stat` lists exactly one source file, under
  `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/`.
- Zero `sorry` occurrences in the four named files and zero `sorryAx` axioms in the touched
  declaration.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity` green
      (binding; unaffected by concurrent tableau work).
- [ ] `grep -n "sorry"` returns nothing on `ModalConservativity.lean` and on all three
      `GenericMCSBridge.lean` files.
- [ ] `bimodal_truthAt_toBimodal_iff_satisfies` confirmed sorry-free and axiom-clean via
      `lean_verify`.
- [ ] Full `lake build` green, **or** every failure attributed to the concurrent tableau session.
- [ ] `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`,
      `lake shake --add-public --keep-implied --keep-prefix` all pass, under the same attribution
      caveat.
- [ ] `git diff` contains proof-body hunks only — no statement, attribute, or import changes.
- [ ] `ModalConservativity.lean` `box`/`diamond` arms unchanged.
- [ ] No file modified under any `Tableau/` directory, under `Cslib/Foundations/`, or under
      `Cslib/Logics/Propositional/`.
- [ ] Exactly one source file in this task's diff.
- [ ] Repo-wide `sorry`-warning count recorded and compared against the **5**-warning /
      4-file baseline, for information only.

## Artifacts & Outputs

- `specs/414_simplify_proofs_normalization_modal_family/plans/02_modal-family-proof-golf.md`
  (this file)
- `specs/414_simplify_proofs_normalization_modal_family/plans/01_modal-family-proof-golf.md`
  (superseded, preserved unchanged)
- `specs/414_simplify_proofs_normalization_modal_family/summaries/02_modal-family-proof-golf-summary.md`
  (produced by `/implement`)
- Modified: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean`
- Not modified (retired to Reasoned Exclusions):
  `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`,
  `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`,
  `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`

## Rollback/Contingency

The remaining change is a single-file proof-body edit with a binary outcome: the site compiles or
it does not. There is no partial-completion failure mode and no site warrants a `[BLOCKED]`
escalation.

- **Per-arm failure**: revert that one arm with `git checkout -p` (or re-type the original from
  the diff) and record it in Phase 1's Reasoned Exclusions table. The original proof is
  sorry-free today and is always the fallback.
- **Per-phase failure**: `git revert` the phase's commit(s). Only Phase 1 produces commits, so a
  phase revert is a whole-task revert.
- **Whole-task rollback**: revert Phase 1's commit(s). The repository returns to a state that is
  known green, with zero semantic change — no declaration, statement, attribute, or import was
  altered at any point.
- **Do not roll back on an unattributed repo-wide failure.** Run Phase 4's attribution protocol
  first. A failure in the concurrent tableau session's territory is not this task's failure, and
  reverting a green single-file edit in response to it destroys correct work for no reason.
- **Do not use destructive git on a dirty tree.** The working tree contains another session's
  uncommitted work. Per `.claude/rules/git-workflow.md`, `git reset --hard`, `git clean -fd`, and
  the `git checkout -- <path>` discard form are forbidden here; use `git checkout -p` / targeted
  `git revert` of this task's own commits instead, and stage only this task's own paths.
- **Retired-phase contingency**: if an implementation-time re-grep finds a residual F1 site in any
  of the three bridge files (i.e. the tree changed after this revision), reopen the affected phase
  by restoring v1's task list for that file rather than improvising — v1 is preserved at
  `plans/01_modal-family-proof-golf.md` for exactly this purpose.
