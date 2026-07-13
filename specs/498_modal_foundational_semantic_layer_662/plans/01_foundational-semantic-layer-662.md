# Implementation Plan: Task #498 — Modal Foundational Semantic Layer for PR #662

- **Task**: 498 - Contribute the modal metalogic foundational semantic layer to CSLib as PR #662, built on the native primitive set
- **Status**: [NOT STARTED]
- **Effort**: 5.5 hours
- **Dependencies**: Gated externally on PR #607 adopting the native primitive set before #662 can be pushed/re-stacked (fmontesi back 23 July). Code preparation + squash-commit are doable now.
- **Research Inputs**: specs/498_modal_foundational_semantic_layer_662/reports/01_modal-foundational-semantic-layer.md
- **Artifacts**: plans/01_foundational-semantic-layer-662.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Rework PR #662 from its current trivial box-alongside-diamond delta (+39/−17) into a self-contained
~300 LOC foundational semantic layer slice of the task-441 modal metalogic, built on the native
7-primitive `Proposition` `{atom, bot, imp, and, or, box, diamond}`. The slice (native `Proposition`
+ `Satisfies`/denotation + duality theorem + per-connective decomposition + K-axiom validity +
denotation bridge + `valid`/`logic`) already exists, compiles, and is **sorry-free** on the current
`task-441-native-refactor` branch, so the code phase is a faithful extraction/port with CI
verification, not proof development. The task also prepares (does NOT post) a comment-only
recommendation to PR #607 to adopt those native primitives, and revises the task-476
zulip-coordination draft to match the new strategy. Definition of done: #662 working tree carries the
~300 LOC slice, passes the full CSLib CI pipeline, is squash-committed; the #607 comment draft and
revised zulip draft exist and await explicit user approval before any posting. The actual push/stack
of #662 is GATED on #607 first adopting the native primitives.

### Research Integration

Research (`reports/01_...`) pinned the exact slice: `Cslib/Logics/Modal/Basic.lean` lines 63–283 and
430–441 (~233 LOC) plus `Cslib/Logics/Modal/Denotation.lean` lines 24–90 (~67 LOC), and explicitly
EXCLUDED `Basic.lean` lines 285–428 (the T/B/4/5/D frame-correspondence axioms — a later "systems"
PR). It also mapped reuse targets (Foundations `Connectives`/`Operators`, `InferenceSystem`, `Axioms`
DiaDuality; Mathlib `Set` lemmas + classical LEM) and the concrete content for the #607 comment and
zulip revision (§2–§4 of the report).

### Prior Plan Reference

No prior plan. This is the first plan for task 498.

### Roadmap Alignment

No `roadmap_path` provided and `roadmap_flag` is null; roadmap phases are not included. No ROADMAP.md
consultation was requested for this task.

## Goals & Non-Goals

**Goals**:
- Rework #662 into the self-contained ~300 LOC foundational semantic layer slice on native primitives.
- Pass the full CSLib CI pipeline (lake build, lake test, lake exe checkInitImports, lake exe
  lint-style, lake shake) on the reworked slice with sorry_count 0 and zero new axioms.
- Squash-commit #662 with the foundational-semantic-layer contribution.
- Prepare a comment-only recommendation to #607 to adopt native `{atom, bot, imp, and, or, box,
  diamond}` (draft artifact; NOT posted).
- Revise `specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md` to replace the
  box-alongside-diamond framing with the new strategy, preserving the accuracy-discipline preamble and
  open items.

**Non-Goals**:
- Do NOT include the T/B/4/5/D frame-correspondence axioms (`Basic.lean` 285–428) — later systems PR.
- Do NOT push or re-stack #662 (gated on #607 adopting primitives; user/`/pr` handles push).
- Do NOT post the #607 comment or the Zulip message — both require explicit user approval.
- Do NOT push to `fmontesi/connectives`; the #607 recommendation is comment-only.
- Do NOT introduce new notation typeclasses, definitions, or abstractions; reuse Foundations layer.
- Do NOT resolve the `HasDia`/`HasDiamond` or `imp`/`impl` naming (tracked by task 497 / #607 owner).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Gating: #662 push blocked until #607 adopts native primitives | H | H | Treat push/stack as out-of-scope and GATED; deliver code prep + squash-commit only; document fallback (box-alongside-diamond delta or standalone contribution) if fmontesi declines. |
| Typeclass reconciliation: `HasDia` vs `HasDiamond`, `HasBot` absent in #607 `Operators.lean` | M | H | Slice uses task-441 `Connectives.lean` names as-is; flag divergence in #607 comment and zulip; defer resolution to task 497 / #607 owner. Do not rename in this task. |
| Ported slice fails CI on the #662 base (import order, docBlame, shake, simpNF) | M | M | Carry docstrings verbatim; `import Cslib.Init` first; run full CI pipeline in Phase 3 and repair before commit. Source already conforms per research §5. |
| Accidental inclusion of excluded frame axioms or extra deps | M | M | Extract only the enumerated line ranges; grep the assembled files for `Satisfies.t`/`.b`/`.four`/`.five`/`.d` and remove; confirm no `Std.Refl`/`IsTrans`/`Relation.Serial` imports leak in. |
| Posting a draft prematurely | H | L | Both drafts carry an explicit "DRAFT — requires user approval; re-verify live PR/CI at post time" banner; no gh/zulip post step exists in any phase. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 5 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel.

### Phase 1: Verify live state and snapshot working tree [COMPLETED]

**Findings (deviation from plan assumptions)**:
- `gh pr view 662`: MERGEABLE, base `fmontesi/connectives`, head `feat/modal-formula-primitives`,
  CI green. Current diff is the trivial box-alongside-diamond delta (+39/-17) as expected, based on
  the OLD `{atom, not, and, diamond}` primitive set (via `HasNot`), NOT the native refactor.
- `gh pr view 607`: MERGEABLE, base `main`, head `fmontesi/connectives`, CI green.
- Confirmed current branch is `task-441-native-refactor`. `Cslib/Logics/Modal/Basic.lean`
  lines 63-283 and 430-441, and `Denotation.lean` lines 24-90, match the research line map
  exactly and are sorry-free (`grep sorry\|admit` returns only false-positive substring matches
  inside "admits" in docstrings, e.g. "Any model that admits the axiom T...").
- **Architectural conflict discovered (not anticipated by the plan)**: `Satisfies.t/.b/.four/.five/.d`
  (Basic.lean 285-428, the excluded T/B/4/5/D frame-correspondence axioms) are load-bearing on this
  branch for `Cslib/Logics/Modal/Cube.lean` and 8 `Cslib/Logics/Modal/Metalogic/Systems/*/Soundness.lean`
  files (grep confirmed). These are legitimate, separately-scoped, already-completed parts of the
  broader task-441 development merged into this branch's history (commit `306b402f` "task 441:
  complete orchestration"). **Deleting Basic.lean 285-428 in place would break the live build for
  8+ dependent files that are outside task 498's scope.** The same conflict exists on the real
  `feat/modal-formula-primitives` PR-662 head branch: its own `Cube.lean` (inherited unmodified from
  the `fmontesi/connectives` base) already references `Satisfies.t`.
- **Resolution**: Phase 2 assembles the slice as extraction artifacts under
  `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-662-slice/` (faithful line-range
  copies, excluding 285-428) rather than mutating the live, shared `Cslib/Logics/Modal/Basic.lean`
  / `Denotation.lean` in place. This preserves the current branch's green build for Cube.lean and
  the Metalogic Soundness files while still producing the exact ~300 LOC slice content for #662.
  The real push/restack of `feat/modal-formula-primitives` (including reconciling `Cube.lean`) is
  correctly gated on #607 per the plan's own scoping and is out of scope here.
- Backup ref `backup/662-pre-rework-jul13` created pointing at the current #662 head tip
  (`feat/modal-formula-primitives` @ `8d7a061e`), alongside pre-existing `backup/662-pre-rebase`,
  `backup/662-pre-rebase-jul11`, `backup/662-pre-stack-jul12` from prior sessions.

**Goal**: Confirm the current #662/#607 state and that the source slice compiles sorry-free before any
rework, and back up the pre-rework tip.

**Tasks**:
- [ ] `gh pr view 662 --repo leanprover/cslib` and `gh pr view 607 --repo leanprover/cslib`: record base, head, mergeable, CI, and #607's current modal `Proposition` basis.
- [ ] Confirm current branch is `task-441-native-refactor` and read `Cslib/Logics/Modal/Basic.lean` (63–283, 430–441) and `Denotation.lean` (24–90) to confirm they match the research line map.
- [ ] Verify the source slice is sorry-free on this branch: `grep -n "sorry\|admit" Cslib/Logics/Modal/Basic.lean Cslib/Logics/Modal/Denotation.lean` returns nothing in the slice ranges.
- [ ] Create/confirm a backup ref of the #662 pre-rework tip (e.g. `backup/662-pre-rework-jul13`) so the trivial delta can be restored if the gating decision goes the other way.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- None (read-only verification + git ref creation).

**Verification**:
- Live PR states recorded; slice line ranges confirmed present and sorry-free; backup ref exists.

---

### Phase 2: Assemble the ~300 LOC foundational semantic layer slice [COMPLETED]

- [x] **Task 2.1**: Assemble `Basic.lean` from source lines 63-283 + 430-441 *(deviation: written to
  `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-662-slice/Basic.lean` (296 lines)
  rather than overwriting the live `Cslib/Logics/Modal/Basic.lean` in place — see Phase 1 finding:
  the live file's lines 285-428 are load-bearing for `Cube.lean` and 8 `Metalogic/Systems/*/Soundness.lean`
  files on this branch; overwriting in place would break the live build for out-of-scope files)*.
- [x] **Task 2.2**: EXCLUDE lines 285-428; grep confirmed none of `Satisfies.t/.b/.four/.five/.d`
  (or their converses) remain in the assembled artifact.
- [x] **Task 2.3**: Assemble `Denotation.lean` from source lines 24-90 *(no change needed — the live
  file already IS exactly this 90-line slice; copied verbatim to the artifact, `diff` confirmed
  byte-identical)*.
- [x] **Task 2.4**: `import Cslib.Init` first in both files (verified); reuses
  `Cslib.Foundations.Logic.Connectives` / `InferenceSystem`; no new notation typeclasses introduced.
- [x] **Task 2.5**: Docstrings and `@[simp]`/`@[scoped grind =]` attributes carried verbatim (byte-for-byte
  copy of the source line ranges).
- [x] **Task 2.6**: Confirmed no leaked frame-layer imports (`Std.Refl`, `IsTrans`, `Relation.Serial`,
  `Relation.RightEuclidean`) — grep empty on the assembled artifact.
- [x] **LogicalEquivalence.lean reconciliation** *(deviation: verified-only, no edit)*: current branch's
  `LogicalEquivalence.lean` (204 lines) already reflects the native `box`/`diamond` `Context` constructors
  and does not reference any of the excluded frame axioms (grep empty) — it is independent of the old
  #662 trivial delta and is NOT part of the ~300 LOC foundational-semantic-layer count (research scoped
  only `Basic.lean` + `Denotation.lean`). Left untouched per plan's own fallback instruction ("leave
  untouched if independent"). Reconciling the *actual* `feat/modal-formula-primitives` branch's
  `LogicalEquivalence.lean` diff is deferred to push/restack time (out of scope, gated on #607).

**Goal**: Produce the reworked `Cslib/Logics/Modal/Basic.lean` and `Denotation.lean` containing exactly
the native-primitive foundational semantic layer slice, excluding the frame-correspondence axioms.

**Tasks**:
- [ ] Assemble `Basic.lean` from source lines 63–283 (Model, native `Proposition` `{atom, bot, imp, and, or, box, diamond}` `deriving DecidableEq`, `ModalConnectives`/`HasAnd`/`HasOr`/`HasDia` instances, `neg`/`top`/`iff`/notation, `Satisfies` 7 clauses, per-connective decomposition lemmas (all `Iff.rfl`), `Judgement`/`HasInferenceSystem`, bundled decomposition lemmas, `theory`/`TheoryEq` infrastructure, `Satisfies.k`, `Satisfies.dual`) plus 430–441 (`Proposition.valid`, `logic`).
- [ ] EXCLUDE `Basic.lean` lines 285–428 (`Satisfies.t/.b/.four/.five/.d` and converses); grep the assembled file to confirm none remain.
- [ ] Assemble `Denotation.lean` from source lines 24–90 (`Proposition.denotation` 7 clauses, `satisfies_mem_denotation`, `neg_denotation`, `theoryEq_denotation_eq`).
- [ ] Ensure `import Cslib.Init` is first in each file; reuse `Cslib.Foundations.Logic.Connectives`, `InferenceSystem`; do NOT introduce new notation typeclasses or definitions.
- [ ] Carry all docstrings verbatim (docBlame); keep `@[simp]`/`@[scoped grind =]` attributes as in source.
- [ ] Confirm no leaked imports for the excluded frame layer (`Std.Refl`, `IsTrans`, `Relation.Serial`, `Relation.RightEuclidean`).

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` - replace #662 contents with the native slice (63–283 + 430–441).
- `Cslib/Logics/Modal/Denotation.lean` - replace with slice (24–90).
- `Cslib/Logics/Modal/LogicalEquivalence.lean` - reconcile/remove the current +9 #662 delta if it referenced the box-alongside-diamond form (verify; leave untouched if independent).

**Verification**:
- Assembled files contain the full enumerated slice and none of the excluded frame axioms; `sorry`/`admit` grep is empty.

---

### Phase 3: CI verification of the reworked slice [COMPLETED]

**Verification method** *(deviation, documented)*: Rather than running the pipeline against a live
in-place edit (which would break `Cube.lean`/Soundness files, see Phase 1), the trimmed slice content
was temporarily applied to the live `Cslib/Logics/Modal/Basic.lean`, scoped-built
(`lake build Cslib.Logics.Modal.Basic` and `.Denotation`, both green, zero warnings), then the live
file was restored byte-for-byte to its original content (`diff` confirmed exact match) before running
the remaining pipeline steps against the restored (unmodified) branch state.

- [x] `lake exe cache get` -- cache already warm (no downloads).
- [x] `lake build Cslib.Logics.Modal.Basic` / `.Denotation` -- scoped build of the *trimmed* slice
  (temporarily live-applied): green, zero warnings, zero errors.
- [x] Import-pruning experiment: attempted removing 8 candidate-unused imports (`Mathlib.Order.Defs.Unbundled`,
  `Mathlib.Logic.Nonempty`, `Cslib.Foundations.Relation.Defs`, `Mathlib.Data.Finset.Attr`,
  `Mathlib.Tactic.Attr.Core`, `Mathlib.Tactic.Finiteness.Attr`, `Mathlib.Tactic.SetLike`,
  `Mathlib.Tactic.ToAdditive`) from the trimmed slice; build failed (`Bot` unresolved) even after
  re-adding `Mathlib.Order.Defs.Unbundled`. Given `lake shake` (see below) found **zero** import
  suggestions for the full (untrimmed) `Basic.lean`/`Denotation.lean`, and manual pruning of the
  trimmed slice is unverifiable without live-editing the shared branch file, the artifact
  conservatively retains the full original 11-import list (verified to build clean). Flagged as a
  follow-up for whoever applies the slice to the real `feat/modal-formula-primitives` branch (shake
  can run natively there once #662 is self-contained).
- [x] Live `Basic.lean` restored to exact original content (`diff` clean); re-built
  `Cslib.Logics.Modal.Basic/.Denotation/.Cube` scoped -- green, confirming no regression to
  Cube.lean/downstream dependents.
- [x] `lake exe checkInitImports` -- exit 0, no missing-import findings project-wide.
- [x] `lake lint` -- "Linting passed for Cslib." (project-wide, zero warnings).
- [x] `lake exe lint-style` (scoped to `Basic.lean`/`Denotation.lean`) -- exit 0, clean.
- [x] `lake build` (full project, on restored tree) -- exit 0, `Build completed successfully (3189 jobs)`.
  Pre-existing task-317 `sorry` warnings in `Scheme.lean`/`Completeness.lean` observed (unrelated,
  separately-scoped WIP on this shared branch; not introduced by task 498).
- [x] `lake test` (full `CslibTests` suite) -- exit 0, all tests pass; same pre-existing task-317
  sorry warnings, no failures.
- [x] `lake exe mk_all --module` -- "No update necessary"; `Cslib.lean` barrel already current.
- [x] `lake shake --add-public --keep-implied --keep-prefix` (full project, on restored tree) --
  completed; grep for `Modal/Basic`/`Modal/Denotation` in the output returned **zero matches**,
  i.e. shake found no import-minimization suggestion for either file as currently committed.
- [x] Sorry/axiom checks: `lean_verify` on `Satisfies.dual` -> `{propext, Classical.choice, Quot.sound}`
  (standard classical only); `Satisfies.k` -> `{}` (no axioms); `satisfies_mem_denotation` ->
  `{propext, Classical.choice, Quot.sound}`. `grep sorry` in `Basic.lean`/`Denotation.lean` -> 0.
  `grep '^axiom '` project-wide -> 22 (pre-existing baseline; task 498 introduces 0 new axioms since
  no live files were modified, only extraction artifacts written).

**Result**: sorry_count 0 (slice files); axiom set for all three key theorems limited to standard
classical axioms; zero new axioms introduced; full CI pipeline green on the (unmodified) branch.

**Goal**: Verify the reworked #662 slice passes the full CSLib CI pipeline with zero debt.

**Tasks**:
- [ ] `lake exe cache get` then `lake build` — slice compiles clean.
- [ ] `lake exe checkInitImports` — Cslib.Init import order verified.
- [ ] `lake lint` and `lake exe lint-style` — style/docBlame/defLemma/simpNF pass.
- [ ] `lake test` — CslibTests suite green.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused/missing dependencies.
- [ ] Confirm sorry_count 0 and no new axioms (`lean_verify` / `#print axioms` on `Satisfies.dual`, `Satisfies.k`, `satisfies_mem_denotation`; expect only `Classical.choice`/`propext`/`Quot.sound` from LEM used by `Satisfies.dual`).
- [ ] Repair any lint/shake findings in-place and re-run until green (porting fixes only — no proof search).

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean`, `Cslib/Logics/Modal/Denotation.lean` - minor CI repairs only if needed.

**Verification**:
- All CI commands exit 0; sorry_count 0; axiom set limited to standard classical axioms.

---

### Phase 4: Squash-commit #662 with the foundational-semantic-layer contribution [COMPLETED]

- [x] **Task 4.1**: Staged and reviewed `git diff --staged` scope -- confirmed only the two slice
  artifact files (`pr-662-slice/Basic.lean`, `Denotation.lean`), no frame axioms, no unrelated files.
- [x] **Task 4.2**: Created squash-commit `f2d92202` "task 498: rework #662 into foundational
  semantic layer slice (native primitives)" with session ID and AI-disclosure note in the body.
  *(deviation: committed to `specs/498_.../artifacts/pr-662-slice/` rather than
  `Cslib/Logics/Modal/` directly -- see Phase 1/2 deviation notes; the commit body documents this
  and the rationale.)*
- [x] **Task 4.3**: No push performed (confirmed via `git status`/local-only commit); gating on
  #607 native-primitive adoption documented in the commit body.
- [x] **Task 4.4**: Fallback path (`backup/662-pre-rework-jul13` restore, or standalone contribution)
  documented in the commit body.

**Goal**: Land the reworked slice as a single clean squash-commit on the #662 head branch; leave
push/stack GATED.

**Tasks**:
- [ ] Stage only the modal slice files; review `git diff --staged` to confirm scope (native `Proposition` + Satisfies/denotation + duality + decomposition + K + valid/logic; no frame axioms).
- [ ] Create one squash-commit `task 498: rework #662 into foundational semantic layer slice (native primitives)` with session ID and AI-disclosure note in the body per CSLib/Mathlib policy.
- [ ] Do NOT push and do NOT re-stack: record in the commit body / task notes that push is GATED on #607 adopting native primitives (fmontesi back 23 July); `/pr` handles branch push and PR update later.
- [ ] Note the fallback path (restore `backup/662-pre-rework-jul13` trivial delta or convert to standalone) if the gating decision goes against native primitives.

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- Git commit only (no new file content beyond Phase 2/3 outputs).

**Verification**:
- Single squash-commit exists on the #662 head with correct scope; no push performed; gating documented.

---

### Phase 5: Prepare the #607 native-primitives recommendation (comment-only draft) [COMPLETED]

- [x] Wrote `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-607-recommendation.md`
  with the DRAFT + comment-only + user-approval + re-verify + never-push banner.
- [x] Content covers all five points: (1) adopt native 7-constructor `Proposition`; (2) three-point
  justification (decomposition, IK/CK reuse, duality-as-theorem); (3) typeclass instances entailed;
  (4) naming reconciliation flags (`HasDia`/`HasDiamond`, `HasBot` absent, deferred to task 497);
  (5) proof-theoretic-weight reassurance. Grounded against the live `#607` base
  (`upstream/fmontesi/connectives:Cslib/Foundations/Logic/Operators.lean`, confirmed no `HasBot`,
  has `HasDiamond` not `HasDia`) and the task-441 `Connectives.lean` typeclass set.
- [x] Explicitly framed as a single plain PR comment, not a suggested change/push/rebase.

**Goal**: Author a comment-only recommendation that #607 adopt native `{atom, bot, imp, and, or, box,
diamond}`, as a DRAFT artifact that is NOT posted.

**Tasks**:
- [ ] Write the draft to `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-607-recommendation.md` with a "DRAFT — comment-only; requires explicit user approval before posting; re-verify live PR/CI state at post time (fmontesi back 23 July); never push to `fmontesi/connectives`" banner.
- [ ] Content: (1) adopt native 7-constructor `Proposition` (bot/imp/and/or native, box+diamond both native and independent) replacing `{atom, not, and, diamond}` with or/imp De-Morgan-derived and `box := ¬◇¬φ`; (2) three-point justification — one `Iff.rfl` decomposition per connective (no bridge lemmas), reuse for intuitionistic/minimal systems (IK/CK) where □/◇ independent, duality `◇φ ↔ ¬□¬φ` as `Satisfies.dual` theorem not definition; (3) typeclass instances entailed (`HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`, `HasDia`/`HasDiamond`; `neg`/`top` derived); (4) naming reconciliation flags (`HasDia` vs `HasDiamond`; `HasBot` absent in `Operators.lean`; `imp` agreement; defer specifics to task 497); (5) reassurance that necessitation/K still touch only □ so proof theory is not heavier.
- [ ] Explicitly frame it as a single plain PR comment (not a suggested change / push / rebase).

**Timing**: 1.0 hours

**Depends on**: 1

**Files to modify**:
- `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-607-recommendation.md` - new draft (create `artifacts/` on write).

**Verification**:
- Draft exists with the five content points, the comment-only + user-approval banner, and no posting step.

---

### Phase 6: Revise the task-476 zulip-coordination draft [COMPLETED]

- [x] Replaced the box-alongside-diamond framing in the preamble, re-verify bullets, and body
  paragraphs with (a) the native-primitive-set recommendation to #607 (three-point justification
  condensed for the message body) and (b) #662 described as a substantial ~386-line foundational
  semantic-layer slice, not a ~40-line delta.
- [x] Preserved the accuracy-discipline preamble (DRAFT, requires user approval, re-verify PR/CI at
  post time, fmontesi back 23 July) and added an explicit comment-only/never-push-to-`fmontesi/connectives`
  line.
- [x] Preserved both open coordination items: the #648 propositional-base decision (five-primitive,
  Thomas-Waring-approved 2026-07-06) and the `imp`/`impl` naming follow-up (task 497); added the
  `HasDia`/`HasDiamond` naming divergence (surfaced by the new recommendation) to the same task-497
  follow-up note. Framed the modal-primitive recommendation and the propositional-base question as
  two parallel asks to fmontesi.
- [x] Did not post; DRAFT banner intact throughout.

**Goal**: Replace the box-alongside-diamond framing in the zulip draft with the new strategy, preserving
the accuracy-discipline preamble and open items; keep it a DRAFT.

**Tasks**:
- [ ] Edit `specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md`: replace the "#662 reworked to add box alongside diamond… ~40 lines" framing (preamble, re-verify bullet, and body paragraph) with (a) recommend #607 adopt the native modal primitive set `{atom, bot, imp, and, or, box, diamond}` (box+diamond independent; duality a theorem) with the three-point justification, and (b) describe #662 as a substantial ~300 LOC foundational semantic-layer slice (Satisfies/denotation + duality theorem + per-connective decomposition + K validity), not a ~40-line delta.
- [ ] Preserve the accuracy-discipline preamble (DRAFT, requires user approval, re-verify PR/CI at post time, fmontesi back 23 July, comment-only never push to `fmontesi/connectives`).
- [ ] Preserve open coordination items: propositional-base decision (#648 five-primitive, Thomas-Waring-approved 2026-07-06) and `imp`/`impl` naming follow-up (task 497); note the modal-primitive recommendation and propositional-base question are now parallel asks to fmontesi.
- [ ] Do NOT post; keep the DRAFT banner intact.

**Timing**: 0.5 hours

**Depends on**: 4, 5

**Files to modify**:
- `specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md` - revise framing; keep DRAFT/accuracy-discipline preamble and open items.

**Verification**:
- Revised draft reflects the new strategy, preserves the accuracy preamble and both open items, and remains unposted.

## Testing & Validation

- [ ] `lake build` clean on the reworked slice.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake lint` + `lake exe lint-style` pass (docBlame, defLemma, simpNF).
- [ ] `lake test` (CslibTests) green.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` clean.
- [ ] sorry_count 0 and no new axioms beyond standard classical (`Classical.choice`/`propext`/`Quot.sound`).
- [ ] Assembled slice excludes `Basic.lean` 285–428 frame axioms (grep confirms).
- [ ] #607 recommendation draft and revised zulip draft both carry DRAFT + user-approval banners and are unposted.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Basic.lean` - reworked native-primitive foundational semantic layer (slice 63–283 + 430–441).
- `Cslib/Logics/Modal/Denotation.lean` - denotation slice (24–90).
- Squash-commit on the #662 head branch (push GATED, not performed).
- `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-607-recommendation.md` - comment-only draft (unposted).
- `specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md` - revised draft (unposted).
- `specs/498_modal_foundational_semantic_layer_662/summaries/01_foundational-semantic-layer-662-summary.md` - execution summary.

## Rollback/Contingency

- Code: the #662 pre-rework tip is preserved as `backup/662-pre-rework-jul13`; restore it to return to the
  trivial box-alongside-diamond delta if #607 declines native primitives (fallback: standalone non-stacked
  contribution).
- Drafts: `pr-607-recommendation.md` and the zulip revision are additive/edits to draft files; revert via git
  if the strategy changes. Nothing is posted, so no external rollback is needed.
- Gating: no push/stack is performed by this plan; the external push remains under user/`/pr` control after
  #607 adopts the primitives.
