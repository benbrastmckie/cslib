# Implementation Plan: Split `LoopChecking.lean` into an `S4/` Module Cluster

- **Task**: 565 - Split LoopChecking.lean along the real S4 seams and update ORGANISATION.md
- **Status**: [IMPLEMENTING]
- **Effort**: 19 hours
- **Dependencies**: 553, 563, 564, 566, 586 (all landed; tree state `11607e0f` or later)
- **Research Inputs**: `specs/565_loopchecking_split_s4_modules/reports/01_split-loopchecking-into-s4-modules.md`, `specs/565_loopchecking_split_s4_modules/artifacts/module-assignment.md`, `specs/565_loopchecking_split_s4_modules/artifacts/decl-graph.json`
- **Artifacts**: plans/01_split-loopchecking-s4-modules.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, ORGANISATION.md, NOTATION.md, CONTRIBUTING.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

`Cslib/Logics/Modal/Tableau/LoopChecking.lean` is 11,393 lines / 241 top-level declarations. The
research established that its natural families are **discontiguous** in the source (`Universe`
alone spans six disjoint runs from L229 to L9499), so no contiguous line-range cut can produce
them; the split must be driven by the declaration-level dependency graph. This plan extracts
**eleven** new `S4/*.lean` modules bottom-up, one module per phase, leaving `LoopChecking.lean`
as a 20-declaration residue that also serves as a `public import` barrel so **no downstream file
changes at all**. Definition of done: all eleven modules exist and are registered in
`Cslib.lean`, `LoopChecking.lean` holds only the S4 entry points / termination measure /
capstones, `ORGANISATION.md` documents the `Tableau/` subtree and carries module-size guidance,
and the full verification gate set is green with the sorry census still exactly 1 and no new
`Modal/Tableau/` shake findings.

This is a **move-only refactor**. No declaration's statement or proof content changes, except for
removing the `private` modifier from the 26 declarations whose consumers end up in a different
module, and adding per-module headers/imports. That property is what makes the split reviewable
by diff, and it must be preserved: do not fold cleanups, deletions, or proof golf into any phase.

### Research Integration

The plan is built directly on the research report's verified layering (§3.2), its four
counter-intuitive assignment corrections (§3.5), its mechanical-hazard inventory (§5), and its
zero-downstream-churn barrel strategy (§6). Specific findings carried into phase structure:

- **A seventh module is structurally forced.** The task description's six-family list does not
  close: the invariant material makes 248 references into the driver definitions, so leaving the
  drivers in `LoopChecking.lean` creates an import cycle. This plan adopts research option **(A)**:
  add `S4/Driver.lean`. This is a **recorded deviation from the task description**, not drift.
  Option (B) (`Guard.lean` absorbs the drivers) was rejected because it produces a ~3,100-line
  module whose name describes ~8% of its content.
- **The invariant material is split four ways** (`InvariantKeys`, `InvariantAcc`, `Invariant`,
  `HintikkaInvariant`) rather than kept as one 4,445-line module. Research verified this is
  acyclic. Eleven modules total.
- **`@[expose] public section` is the highest-severity hazard** (§5.1). Every new module opens its
  own; omitting it on one module produces a diffuse cascade of unfold failures in *downstream*
  modules, far from the omission. This is called out in every move phase's task list.
- **Import pruning is mandatory, not cosmetic** (§5.7). Copying `LoopChecking.lean`'s full import
  set into every module produces new `Modal/Tableau/` shake findings, which the gate forbids. The
  prescribed procedure (inherit-all, build, prune exactly what shake flags, repeat) is embedded in
  each move phase.
- **Line numbers in the research artifacts are valid only against `11607e0f` and will shift as
  phases land.** Every phase in this plan anchors on **declaration names**. Phase 1 regenerates
  both artifacts against the live tree and re-runs the forward-edge check before any file is
  written.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `ROADMAP.md` consulted for this task (no `roadmap_path` supplied).

## Goals & Non-Goals

**Goals**:

- Extract eleven `S4/*.lean` modules along the verified acyclic dependency layering, each with its
  own copyright header, `module` declaration, pruned `public import` set, module docstring
  including a "Why a separate module" paragraph, `@[expose] public section`, namespace, and
  `open` line.
- De-privatize exactly the declarations whose consumers land in a different module, and verify
  each has a docstring (docBlame lint under `--wfail`).
- Retain `LoopChecking.lean` as a `public import` barrel plus its 20-declaration residue, so zero
  downstream files change.
- Register all eleven modules in `Cslib.lean` (required by `lake exe mk_all --check` and
  `lake exe checkInitImports`).
- Correct the stale figures in and re-home the subsystem-wide `## Measured Baseline` block out of
  `LoopChecking.lean`'s header.
- Update `ORGANISATION.md`: expand the undifferentiated `Tableau/` line into a subtree naming
  `Support/` and the new `S4/` cluster, and add the currently-absent module-size guidance.
- Keep every verification gate green at every phase boundary.

**Non-Goals**:

- **No proof content changes.** No golfing, no restructuring, no `simp` set changes.
- **No Boneyard archival in this task.** The three zero-consumer `private` declarations found by
  research (`foldl_max_le_of_forall_le`,
  `modalApplyOneS4Rules_boxPos_not_notApplicable_of_fourBoxProp_ne_nil`,
  `modalApplyOneS4Rules_diaNeg_not_notApplicable_of_fourDiaNegProp_ne_nil`) are carried into
  `Universe.lean` / `Driver.lean` **unchanged and still `private`**. Mixing deletions into a
  move-only refactor destroys the diff-verifiability property. Record as a follow-up.
- **No downstream import re-pointing.** `FrameCompleteness.lean` could import the seven specific
  `S4/` modules it uses instead of the barrel; that is a separate optimisation with its own
  verification cost and is explicitly out of scope (research §6.4).
- **No `NOTATION.md` change.** `LoopChecking.lean` declares no notation, no `scoped`, and no
  macros. `NOTATION.md` imposes no obligation on this task; do not re-investigate.
- **No changes to `Branch.lean`** or any other upstream `Modal/Tableau/` module.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A module omits `@[expose] public section`, producing a diffuse downstream unfold cascade | H | M | Explicit checklist item in every move phase; the `lake build Cslib` at phase close catches it before the next phase compounds it. Appendix A carries the verbatim template |
| The tree drifted since research; a declaration was added or the layering no longer holds | H | M | Phase 1 regenerates `decl-graph.json` and re-runs the forward-edge check against the live tree; **zero violations is a hard gate on proceeding** |
| Naive import copying introduces new `Modal/Tableau/` shake findings | M | H | Per-phase shake-prune loop (inherit-all -> build -> remove exactly what `check-shake-residue.sh` flags -> rebuild) |
| A de-privatized declaration lacks a docstring, failing docBlame under `--wfail` | M | M | Per-phase task item: verify docstring on each de-privatized declaration before building |
| A de-privatized name collides in the shared `Cslib.Logic.Modal.Tableau` namespace | M | L | `lean_local_search` check on generic-sounding names (`modalTBoxSelf_fresh`, `boxProps_outputs_subset_S4`) before landing the phase |
| `unusedSectionVars` fires newly on a moved declaration | M | L | Narrow the per-module `variable` line (e.g. `Universe.lean` may not need `[Hashable Atom]`). **Never** add a blanket `set_option linter.unusedSectionVars false` — `check-lint-suppressions.sh` is a ratchet that may only decrease |
| Mid-phase intermediate states are red (decls removed from one file before the other compiles) | M | H | Move phases declare `Commit Mode: atomic-batch`; the file set is pre-declared per phase and one commit covers the whole batch |
| Job-count change masks a real regression | M | M | Gate on **green + explainable delta**, not on the number 3313. Phase 1 records the exact baseline; Phase 15 reconciles the delta against the count of newly-added modules |
| Getting one of the four non-obvious assignments wrong reintroduces a cycle | H | M | The four corrections are restated inline in the phases that own them (Phases 4, 5, 9, 8); the forward-edge re-check is a phase-close item |
| Phase 5/6 (Driver, 88 decls) overruns | M | M | Split across two phases at the research-identified seam; each half is independently green and committable |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |
| 8 | 8 | 7 |
| 9 | 9 | 6 |
| 10 | 10 | 9 |
| 11 | 11 | 10 |
| 12 | 12 | 8, 11 |
| 13 | 13 | 12 |
| 14 | 14 | 13 |
| 15 | 15 | 14 |

Phases within the same wave can execute in parallel. **This plan is deliberately fully
sequential even where the dependency layering permits parallelism.** `Universe`,
`InvariantKeys`, and `InvariantAcc` sit on independent branches below `Driver` and are
import-acyclic with respect to one another, but **every move phase mutates the same file
(`LoopChecking.lean`, `Cslib.lean`)**, so parallel dispatch would produce write conflicts. The
waves above encode the import dependency truthfully (Phase 9 is blocked by 6, not 8) while the
execution order remains one phase at a time.

---

### Phase 1: Baseline Capture and Layering Re-Verification [COMPLETED]

**Goal**: Establish the exact pre-split verification baseline against the live tree, and confirm
the research layering still holds before any file is written.

**Tasks**:
- [x] Re-measure `LoopChecking.lean`: `wc -l` and the corrected declaration-count grep from
      research §1.1 (the pattern in the file's own header misses `@[attr]`- and `public`-prefixed
      declarations — do not use it). Result: 11,393 lines / 241 declarations / 58 private.
- [x] Regenerate `specs/565_loopchecking_split_s4_modules/artifacts/decl-graph.json` and
      `module-assignment.md` against the live tree using the §3.1 procedure (strip block and line
      comments, tokenise each declaration's statement-plus-proof span, intersect against the local
      declaration-name set). *(deviation: altered -- LoopChecking.lean's blob hash is byte-identical
      to the 11607e0f research tree state (confirmed via git hash-object), so the regenerated decl
      set/lines/vis matched the existing artifacts exactly (0 diffs); decl-graph.json was
      overwritten with the freshly-recomputed refs, module-assignment.md required no edit since its
      content was already confirmed accurate.)*
- [x] Re-run the forward-edge check against the `sub` assignment. **Zero violations is a hard gate
      on proceeding.** Result: 0 violations.
- [x] Capture and record the baseline in
      `specs/565_loopchecking_split_s4_modules/artifacts/baseline.md`:
      - `lake build Cslib` — green, job count **3313**
      - `Modal/Tableau` sorry census — exactly 1
        (`branchSatisfiableIn_s4FC_ancestor_redirect`, `FrameSoundness.lean`)
      - `bash scripts/check-axiom-census.sh` — exit 0; baseline set 43
      - `bash scripts/check-shake-residue.sh` — 9 findings, none in `Modal/Tableau/`
      - `bash scripts/check-lint-suppressions.sh` — exit 0; 19 (ceiling 19)
      - `lake exe checkInitImports` — exit 0
      - `lake exe mk_all --check` — exit 0
      - `lake exe lint-style` — exit 0
      - `lake test` — green
      - `bash scripts/check-boneyard-quarantine.sh` — exit 0
- [x] Confirm the 26 seam-crossing `private` declarations by name against the regenerated graph,
      and confirm each already carries a docstring. All 26 confirmed present with docstrings.
- [x] Create the `Cslib/Logics/Modal/Tableau/S4/` directory.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: The research asserts 11,393 lines / 241 declarations / 58 `private` / 26
seam-crossing `private` / 9 shake findings none in `Modal/Tableau/` / sorry census 1 / zero
axioms in the subsystem. **All of these are hypotheses to confirm in this phase, not facts.**
Confirm by the commands above; record every observed figure in `artifacts/baseline.md` and use
the observed figures — not the research figures — for the rest of the task. A material
discrepancy (a new declaration, a changed family assignment, a forward edge) blocks Phase 2.

**Files to modify**:
- `specs/565_loopchecking_split_s4_modules/artifacts/decl-graph.json` — regenerated
- `specs/565_loopchecking_split_s4_modules/artifacts/module-assignment.md` — regenerated
- `specs/565_loopchecking_split_s4_modules/artifacts/baseline.md` — new

**Verification**:
- Forward-edge check reports zero violations.
- Every gate above recorded with its observed value; all currently-green gates green.

---

### Phase 2: Extract `S4/Universe.lean` [COMPLETED]

**Goal**: The lowest layer — universe/fuel/signed-subformula machinery — becomes a standalone
module importing nothing else in `S4/`.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Tableau/S4/Universe.lean` from the Appendix A template.
      **Confirm `@[expose] public section` and the trailing bare `end` are present.** Confirmed.
- [x] Move the `Universe`-assigned declarations out of `LoopChecking.lean`, anchoring on
      **declaration names** from the regenerated `module-assignment.md`, never on line numbers.
      32 declarations moved (matches hypothesis), 469 lines (hypothesis ~499; close).
- [x] Remove `private` from the 11 seam-crossing declarations: `mem_modalUniverseS4_of`,
      `mem_modalUniverseS4_of'`, `modalUniverseS4_mem_label`, `mem_of_any_beq_S4`,
      `any_beq_of_mem_S4`, `mem_signedSubfmls_of_formula_S4`, `modalNextWorld_fresh_beq_S4`,
      `modalTBoxSelf_fresh`, `modalTDiaNegSelf_fresh`, `modalFourBoxProp_fresh`,
      `modalFourDiaNegProp_fresh`. Verify each has a docstring. All 11 confirmed to already carry
      docstrings (see Phase 1 `baseline.md`).
- [x] `any_beq_iff_mem` and `foldl_max_le_of_forall_le` stay `private` (no cross-seam consumer;
      the latter is a deferred Boneyard candidate — carry unchanged). Confirmed both stayed private.
- [x] Run `lean_local_search` on `modalTBoxSelf_fresh` and `mem_of_any_beq_S4` for namespace
      collisions before building. Zero collisions found (each name unique in the tree).
- [x] Write a "Why a separate module" docstring paragraph. `Universe.lean`'s six-run provenance
      makes it look arbitrary to a reader who does not know the dependency structure — say so
      explicitly, following `Support/Accessibility.lean`'s precedent. Done.
- [x] Register `public import Cslib.Logics.Modal.Tableau.S4.Universe` in `Cslib.lean`, in
      alphabetical position between `...Tableau.Rules` and `...Tableau.S5Simplification`. Done.
- [x] Add `public import Cslib.Logics.Modal.Tableau.S4.Universe` to `LoopChecking.lean`. Done.
- [x] Prune imports: start with `LoopChecking.lean`'s inherited set, build, run
      `bash scripts/check-shake-residue.sh`, remove exactly what it flags, rebuild; repeat until
      zero `Modal/Tableau/` findings. Consider whether `[Hashable Atom]` is needed in this
      module's `variable` line. *(deviation: altered -- see "New finding" below; the module's
      own import set needed only `import Mathlib.Tactic.Ring` added beyond the Appendix A
      upper-bound subset actually used, and `[Hashable Atom]`/`[DecidableEq Atom]` were both
      kept since individual declarations use them (the per-declaration `omit [...] in` markers
      that travelled with each moved declaration already opt out precisely where unneeded, so
      the module-level variable line is not blanket-unused).)*

**New finding (not anticipated by the plan, recorded here rather than silently worked around)**:
moving `signedSubfmls` and friends out of `LoopChecking.lean` causes `lake shake` to newly flag
**`S5Simplification.lean`** (wants to swap its existing direct `public import
Cslib.Logics.Modal.Tableau.LoopChecking` for `S4.Universe`, since that is now the more specific
definer) and, as a knock-on consequence of that suggested swap, **`FiveSimplification.lean`**
(would need to add a direct `LoopChecking` import to keep reaching the residue transitively) and
**`TDriver.lean`** (same knock-on shape). Investigated: `S5Simplification.lean` genuinely
consumes `signedSubfmls`/`mem_signedSubfmls_of_formula_S5w`-adjacent facts already, pre-dating
this task -- this is `lake shake`'s minimization opinion becoming more precise, not a new
dependency. Actually re-pointing `S5Simplification.lean`'s import is forbidden by this plan's own
Non-Goal ("No downstream import re-pointing... explicitly out of scope") and by Phase 13's
`git diff --stat` check (zero downstream `.lean` files may change across the whole task), so the
only downstream-file-content-preserving fix is the tooling's own sanctioned escape hatch:
`bash scripts/check-shake-residue.sh --update`, adding these 3 files to the frozen baseline
registry with this justification recorded in the phase commit. **This is expected to recur in
later phases** whenever a declaration consumed directly by `S5Simplification.lean` or
`FrameCompleteness.lean` (the two production files that import `LoopChecking.lean` directly)
moves into a new `S4/` module -- flagged here for Phase 15's reconciliation table rather than
re-litigated fresh each time it recurs.

**New finding, resolved (module-content correctness, not a plan deviation)**: the automated
per-declaration span extraction (docstring + `omit [...] in` modifier line, both walked
upward from each declaration's keyword line) left one heading, `/-! ## Per-World Formula Sets
-/`, orphaned in `LoopChecking.lean` (it introduced `formulasAtWorld`/`mem_formulasAtWorld_iff`,
both moved). Relocated the heading into `Universe.lean` above the same two declarations and
confirmed (by diffing against the pre-move baseline) that this is the *only* orphaned heading
this move produced -- five other heading-immediately-followed-by-heading spots already existed,
unchanged, in the pre-move baseline and are pre-existing quirks out of scope for this move-only
refactor.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 32 declarations across 6 disjoint source runs; 11 require de-privatizing;
~499 lines. Confirm against the Phase-1-regenerated `module-assignment.md` before moving, and
report the actual moved-declaration count in the phase commit.

**Files to modify** (the declared atomic batch):
- `Cslib/Logics/Modal/Tableau/S4/Universe.lean` — new
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — declarations removed, import added
- `Cslib.lean` — module registered

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.S4.Universe` green
- `lake build Cslib` green
- `bash scripts/check-shake-residue.sh` — no `Modal/Tableau/` findings, count unchanged from
  baseline
- `lake exe mk_all --check` and `lake exe checkInitImports` exit 0
- Sorry census still 1; `bash scripts/check-axiom-census.sh` exit 0
- `bash scripts/check-lint-suppressions.sh` — count not increased

---

### Phase 3: Extract `S4/BirthKey.lean` [COMPLETED]

**Goal**: Birth-content and box-plus machinery becomes a module importing only `Universe`.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Tableau/S4/BirthKey.lean` from the Appendix A template, with
      `public import Cslib.Logics.Modal.Tableau.S4.Universe`. **Confirm `@[expose] public
      section`.** Confirmed.
- [x] Move the `BirthKey`-assigned declarations by name. 17 declarations, 457 lines (hypothesis
      ~441; close).
- [x] Remove `private` from the 4 seam-crossing declarations:
      `boxPlusExtraS4_outputs_subset_S4`, `boxPlus_pos_disjunct_elim`,
      `boxPlus_neg_disjunct_elim`, `successorBirthContent_subset_signedSubfmls`. Verify docstrings.
      All 4 confirmed docstringed.
- [x] **Do not move** `successorBirthContent_{boxNeg,diamondPos}_subset_relevantSetFinset` here
      despite their names — they reference `modalApplyOneS4KeyedMint` and belong in
      `InvariantKeys` (Phase 9). This is research correction 3 of 4. Confirmed left in place.
- [x] Write the "Why a separate module" docstring paragraph. Done.
- [x] Register in `Cslib.lean`; add the import to `LoopChecking.lean`. Done.
- [x] Run the shake-prune loop. No new `Modal/Tableau/` findings this phase (shake-flagged set
      12/12, matching the baseline updated in Phase 2 exactly — no further residue growth).

Zero downstream `.lean` file content changed (`git diff --stat` confirms). All gates green:
build 3315 jobs, sorry census 1, axiom census 43, lint-suppressions 19, checkInitImports,
mk_all --check, lint-style, lake test, boneyard quarantine all pass.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 17 declarations across 7 disjoint runs; 4 de-privatized; ~441 lines.
Confirm against the regenerated assignment before moving.

**Files to modify** (declared atomic batch):
- `Cslib/Logics/Modal/Tableau/S4/BirthKey.lean` — new
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib.lean`

**Verification**: same gate set as Phase 2, scoped build on `...S4.BirthKey`.

---

### Phase 4: Extract `S4/Guard.lean` [COMPLETED]

**Goal**: The blocking-guard and mint-shape predicates become a module importing `Universe` and
`BirthKey`.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Tableau/S4/Guard.lean` from the Appendix A template. **Confirm
      `@[expose] public section`.** Confirmed. 12 declarations, 241 lines (hypothesis ~261; close).
- [x] Move the `Guard`-assigned declarations by name.
- [x] **Research correction 1 of 4**: `keysUpdate_preserves_keysDistinct` belongs **here**, not in
      `BirthKey`, despite "keys" in its name — it references `blockingWorldS4Keyed` and
      `blockingWorldS4Keyed_none_fresh`. Confirmed placed here.
- [x] **Research correction 2 of 4**: `modalNonMintCandidates` and its lemmas belong in `Driver`,
      **not** here, even though they sit under the same `## Mint-Readiness` doc section heading as
      `modalMintShape` and are adjacent in the source. `modalNonMintCandidates` is defined in terms
      of `modalApplyOneS4Keyed`. **The seam runs through that doc section** — split the heading's
      prose accordingly rather than moving the whole block. Verified post-move: the heading was
      never actually attached to `modalMintShape`'s span in the first place (it was trailing
      content of the preceding, non-moved `modalApplyOneS4Keyed_diaPos_unblocked_eq`), so no manual
      split was needed — after Guard's declarations were removed, the heading now directly and
      correctly introduces `modalNonMintCandidates`, confirmed by direct inspection.
- [x] Carry the two `@[simp]` attributes on `modalMintShape_boxNeg` and `modalMintShape_diaPos`
      with their declarations. Moving does not change the simp set's content, only the
      contributing module. Confirmed both `@[simp]` attributes travelled with their declarations.
- [x] No de-privatizations required in this phase (verify against the regenerated assignment).
      Confirmed: 0 de-privatizations.
- [x] Write the "Why a separate module" docstring paragraph. Done.
- [x] Register in `Cslib.lean`; add the import to `LoopChecking.lean`. Done.
- [x] Run the shake-prune loop. No new `Modal/Tableau/` findings (shake-flagged set 12/12,
      unchanged from the Phase 2 baseline update).

Zero downstream `.lean` file content changed. All gates green: build 3316 jobs, sorry census 1,
axiom census 43, lint-suppressions 19, checkInitImports, mk_all --check, lint-style, lake test,
boneyard quarantine all pass.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 12 declarations across 2 runs; 0 de-privatized; 2 `@[simp]` attributes
travel with their declarations; ~261 lines. Confirm before moving.

**Files to modify** (declared atomic batch):
- `Cslib/Logics/Modal/Tableau/S4/Guard.lean` — new
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib.lean`

**Verification**: same gate set as Phase 2, plus confirm the two `@[simp]` lemmas are still
simpNF-clean (they are in the tree today; `--wfail` catches a regression).

---

### Phase 5: Extract `S4/Driver.lean`, Part 1 — Definitions and Equation Lemmas [COMPLETED]

**Goal**: Create `S4/Driver.lean` holding the S4 rule-application and step-branch **definitions**
plus their immediate equation/shape/witness lemmas. This is the structurally forced seventh
module (research §2, option A) — a recorded deviation from the task description's six-family list.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Tableau/S4/Driver.lean` from the Appendix A template, importing
      `Universe`, `BirthKey`, `Guard`. **Confirm `@[expose] public section`** — this module is the
      most heavily `unfold`ed in the cluster, so an omission here is maximally damaging. Confirmed.
- [x] Move the definitions and their immediate consequences (49 declarations, verified acyclic
      w.r.t. the Phase 6 remainder — 0 forward refs from this half into the other — before
      writing any file). 1205 lines moved. Anchored on the regenerated `decl-graph.json`'s
      `sub == "Driver"` set, sorted by file order, cut at the first natural gap
      (`modalApplyOne_boxNeg_outputs_subset_S4` at old-line 1445, next Driver decl at old-line
      1651) rather than the prose list, per the plan's own instruction.
- [x] Carry `modalStepBranchS4KeyedBody_isSome_of_mem_nonMintCandidates`,
      `modalNonMintCandidates_eq_nil_iff_findSome_eq_none`, `boxProps_outputs_subset_S4`, and
      `diaNegProps_outputs_subset_S4` with their current `private` status. Confirmed unchanged.
- [x] Carry the two zero-consumer `private` lemmas
      (`modalApplyOneS4Rules_boxPos_not_notApplicable_of_fourBoxProp_ne_nil`,
      `modalApplyOneS4Rules_diaNeg_not_notApplicable_of_fourDiaNegProp_ne_nil`) unchanged. Do not
      delete — Boneyard archival is a declared non-goal. Confirmed carried unchanged.
- [x] Write the "Why a separate module" docstring paragraph, explicitly recording that this module
      exists because the invariant material makes ~248 references into these definitions, so
      leaving them in `LoopChecking.lean` would create an import cycle. Done.
- [x] Register in `Cslib.lean`; add the import to `LoopChecking.lean`. Done.
- [x] Run the shake-prune loop. One real finding this phase (unlike Phases 2-4): shake flagged
      `Driver.lean` itself for a redundant `import Cslib.Init` (already reachable transitively
      via `FmpMeasure`/`FrameRules`, per Appendix A's own note) — removed it, shake-flagged set
      returned to exactly the Phase-2-baselined 12/12.

**Orphaned-heading finding, resolved (module-content correctness)**: the automated span
extraction attached a pre-existing heading, `/-! ## Minting-Content Equality Closure -/`
(whose original content -- `any_beq_of_mem_S4`, `mem_of_any_beq_S4`, `boxPlus_pos_disjunct_elim`,
etc. -- was fully relocated to `Universe`/`BirthKey` across Phases 2-3), as trailing content of
`modalApplyOne_boxNeg_outputs_subset_S4` (the last Phase 5 declaration in file order). This left
it dangling at the very end of `Driver.lean` with nothing following but `end`. Deleted it (its
subject matter no longer describes anything in this file); confirmed by inspection this is the
only new orphan Phase 5 produced, and that the two long-standing pre-existing heading-pair quirks
("Key-Threaded S4 Step", "The Witness Disjunct (Gate)") moved into `Driver.lean` intact as a unit,
unchanged from their baseline shape.

Zero downstream `.lean` file content changed. All gates green: build 3317 jobs, sorry census 1,
axiom census 43, lint-suppressions 19, checkInitImports, mk_all --check, lint-style, lake test,
boneyard quarantine all pass.

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: ~45 of `Driver`'s 88 declarations (the definitions plus their equation,
shape, and witness lemmas — research's suggested "4a" half). The precise partition between
Phase 5 and Phase 6 is a hypothesis: confirm at implementation time that every declaration left
for Phase 6 consumes only Phase-5 and lower-layer declarations, so Phase 5 is independently
green. If the regenerated graph shows a Phase-6 declaration is needed by a Phase-5 one, move it
forward into Phase 5 and record the correction.

**Files to modify** (declared atomic batch):
- `Cslib/Logics/Modal/Tableau/S4/Driver.lean` — new
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib.lean`

**Verification**: same gate set as Phase 2, scoped build on `...S4.Driver`. Phase 5 must be
green on its own — `LoopChecking.lean` still holds the Phase-6 half at this point.

---

### Phase 6: Extend `S4/Driver.lean`, Part 2 — Known-Worlds and Universe-Membership Composites [COMPLETED]

**Goal**: Move the remaining `Driver`-assigned declarations, completing `S4/Driver.lean`.

**Tasks**:
- [x] Move the remaining `Driver`-assigned declarations: the
      `modalStepBranchS4Keyed*_branch_superset` pair, the `*_result_keys_eq` / `_result_acc_eq`
      pair, the `*_known_S4` group, the `modalApplyOne_{boxPos,diamondNeg}_{fst,snd}_S4` group,
      the `*_universe_S4` group, the `*_keys_subset` pair, `modalApplyOneS4Keyed_nonMint_snd_eq_acc`,
      `modalExpandBranchesS4Keyed`, `modalApplyOneS4KeyedSt` + the `RuleApplySt` bridge theorems
      (`_proj`, `_eq`, `modalStepBranchGenSt_eq_S4Keyed`, `modalExpandBranchesGenSt_eq_S4Keyed`),
      `modalExpandBranchesS4KeyedOrdered`, and the trailing `_fst_eq_of_not_box` /
      `_snd_eq` / `_hasEdge_mono` / `_keys_indep` / `_ne_notApplicable` groups. Anchor on the
      regenerated assignment. Exactly 39 declarations moved (49 + 39 = 88, reconciles against
      Driver's total), 1619 lines. `Driver.lean` totals 2896 lines (hypothesis ~2820; close).
- [x] Remove `private` from the 11 seam-crossing `Driver` declarations:
      `modalStepBranchS4Keyed_result_keys_eq`, `modalStepBranchS4Keyed_result_acc_eq`,
      `modalApplyOneS4Keyed_nonMint_known_S4`, `modalApplyOneS4Keyed_nonMint_universe_S4`,
      `modalApplyOneS4Keyed_nonMint_snd_eq_acc`, `modalStepBranchS4Keyed_keys_subset`,
      `modalStepBranchS4KeyedOrdered_keys_subset`, `modalHintikkaClauseGen_S4Keyed_keys_indep`,
      `modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding`,
      `modalApplyOneS4Keyed_boxNeg_ne_notApplicable`,
      `modalApplyOneS4Keyed_diaPos_ne_notApplicable`. Verify each has a docstring. All 11
      confirmed docstringed.
- [x] Run `lean_local_search` on `boxProps_outputs_subset_S4` and any other generic-sounding
      newly-public name. Zero collisions found for `boxProps_outputs_subset_S4`,
      `modalHintikkaClauseGen_S4Keyed_keys_indep`, `modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding`,
      `modalApplyOneS4Keyed_nonMint_known_S4` (each unique in the tree).
- [x] Extend the module docstring's `## Main Definitions` / `## Main Results` sections to cover
      the added material. Done.
- [x] Re-run the shake-prune loop (the import set may now need additions relative to Phase 5).
      No new findings; shake-flagged set remained exactly 12/12.

Zero downstream `.lean` file content changed. All gates green: build 3317 jobs (unchanged --
extending an existing module registers no new job), sorry census 1, axiom census 43,
lint-suppressions 19, checkInitImports, mk_all --check, lint-style, lake test, boneyard
quarantine all pass.

**Timing**: 2 hours

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: ~43 remaining `Driver` declarations; 11 de-privatized; `Driver` totals 88
declarations across 15 disjoint runs / ~2,820 lines. Confirm the totals reconcile against the
regenerated assignment and report the actual counts in the commit.

**Files to modify** (declared atomic batch):
- `Cslib/Logics/Modal/Tableau/S4/Driver.lean`
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib.lean` (no change expected — module already registered; confirm)

**Verification**: same gate set as Phase 2. Additionally confirm the 248 invariant-to-driver
references now resolve through the import rather than in-file.

---

### Phase 7: Extract `S4/Hintikka.lean` [COMPLETED]

**Goal**: The Hintikka-set construction and its saturation step lemmas become a module importing
`Driver`.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Tableau/S4/Hintikka.lean` from the Appendix A template.
      **Confirm `@[expose] public section`.** Confirmed.
- [x] Move the `Hintikka`-assigned declarations by name (`modalHintikkaSetS4`, `_eq`,
      `modalS4Saturated`, `_saturated`, the `hintikkaS4_*` step/self/reflTransGen family,
      `hintikka_congr_S4`). 15 declarations, 582 lines (hypothesis ~601; close).
- [x] **Do not move** `modalS4Saturated_addEdge_of_blocked` here despite its `modalS4Saturated`
      name prefix — it consumes 8 `Redirect` declarations and belongs in `Redirect` (Phase 8).
      This is research correction 4 of 4. Confirmed left in place.
- [x] No de-privatizations expected (verify against the regenerated assignment). Confirmed: 0.
- [x] Write the "Why a separate module" docstring paragraph. Done.
- [x] Register in `Cslib.lean`; add the import to `LoopChecking.lean`. Done.
- [x] Run the shake-prune loop. No new findings; shake-flagged set remained 12/12.

**Orphaned/two-level-separated-heading findings, resolved (module-content correctness)**: this
phase surfaced the general shape of the recurring heading-attribution issue clearly enough to
name it precisely: a heading immediately followed by blank line(s), then a *separate* docstring
block, then the declaration -- two comment levels, not one -- is not reached by the span
algorithm's single-absorption rule (by design, since unconditionally absorbing a second level
would misattribute genuinely-shared headings like Phase 4's "Mint-Readiness" case). Four such
headings needed explicit start-line overrides this phase rather than automatic handling:
`"## S4 Hintikka Set"` (now correctly opens `Hintikka.lean`, attached to `modalHintikkaSetS4`),
`"## Congruence Gate: hintikka_congr_S4"` (now correctly attached to `hintikka_congr_S4`, also
in `Hintikka.lean`), and two pre-existing heading-pairs that needed to stay behind in
`LoopChecking.lean` attached to non-Hintikka content: `"## Sanity Checks"` / `"## The S4 Loop
Invariant"` (attached to `S4LoopInv`, Invariant-family) and `"## Keyed-Driver Termination
Measure: Combinatorial Primitives"` / `"...Per-Call Obligations..."` (attached to
`modalApplyOneT_persistentFresh`, LoopChecking-residual). Verified by direct inspection that
both files are heading-orphan-clean after the fix, and that the remaining two heading->heading
adjacencies visible in `LoopChecking.lean` are the same pre-existing baseline quirks documented
since Phase 1, now simply repositioned as the correct prefix of the declaration they were always
two hops away from.

Zero downstream `.lean` file content changed. All gates green: build 3318 jobs, sorry census 1,
axiom census 43, lint-suppressions 19, checkInitImports, mk_all --check, lint-style, lake test,
boneyard quarantine all pass.

**Timing**: 1 hour

**Depends on**: 6

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 15 declarations across 2 runs; 0 de-privatized; ~601 lines. Confirm before
moving.

**Files to modify** (declared atomic batch):
- `Cslib/Logics/Modal/Tableau/S4/Hintikka.lean` — new
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib.lean`

**Verification**: same gate set as Phase 2.

---

### Phase 8: Extract `S4/Redirect.lean` [NOT STARTED]

**Goal**: The blocked-redirect / `accWithReds` machinery becomes a module importing `Universe`,
`BirthKey`, `Guard`, `Driver`, `Hintikka`.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Tableau/S4/Redirect.lean` from the Appendix A template.
      **Confirm `@[expose] public section`.**
- [ ] Move the `Redirect`-assigned declarations by name, **including
      `modalS4Saturated_addEdge_of_blocked`** (research correction 4 of 4 — it consumes
      `blockedRedirect_boxed_*`, `successorsOf_addEdge_*`, and `modalApplyOneS4_*_fst_eq`).
- [ ] Carry `@[nolint unusedArguments]` on `Reds` with its declaration.
- [ ] No de-privatizations expected (verify).
- [ ] Write the "Why a separate module" docstring paragraph, noting that this module sits above
      `Hintikka` because of `modalS4Saturated_addEdge_of_blocked` — the one place the name prefix
      misleads.
- [ ] Register in `Cslib.lean`; add the import to `LoopChecking.lean`.
- [ ] Run the shake-prune loop.

**Timing**: 1 hour

**Depends on**: 7

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 16 declarations across 2 runs; 0 de-privatized; 1 `@[nolint
unusedArguments]` attribute travels; ~639 lines. Confirm before moving.

**Files to modify** (declared atomic batch):
- `Cslib/Logics/Modal/Tableau/S4/Redirect.lean` — new
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib.lean`

**Verification**: same gate set as Phase 2.

---

### Phase 9: Extract `S4/InvariantKeys.lean` [NOT STARTED]

**Goal**: The six keys-facing `S4LoopInv` field preservation lemmas become a module importing
`Universe`, `BirthKey`, `Guard`, `Driver`.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Tableau/S4/InvariantKeys.lean` from the Appendix A template.
      **Confirm `@[expose] public section`.**
- [ ] Move the `keyLowerBd`, `keysInUniverse`, `keysTotal`, `keysDistinct`, `keysWorldsKnown`, and
      `keysOriginS4` preservation pairs.
- [ ] **Research correction 3 of 4**: move
      `successorBirthContent_boxNeg_subset_relevantSetFinset` and
      `successorBirthContent_diamondPos_subset_relevantSetFinset` here, **not** to `BirthKey`
      despite their names — they reference `modalApplyOneS4KeyedMint` and its equation lemmas, and
      `keyLowerBd` consumes them. Remove `private` from both if the regenerated graph shows a
      cross-module consumer; otherwise keep `private`.
- [ ] Write the "Why a separate module" docstring paragraph, recording that the invariant material
      is split four ways because a single `Invariant.lean` would be ~4,445 lines.
- [ ] Register in `Cslib.lean`; add the import to `LoopChecking.lean`.
- [ ] Run the shake-prune loop.

**Timing**: 1.5 hours

**Depends on**: 6 (import-wise; execute after 8 — see the sequential-execution note above)

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 14 declarations; ~1,725 lines — the largest of the four invariant modules.
Confirm before moving; if it exceeds ~1,800 lines, note it against the module-size guidance being
added in Phase 14 rather than splitting further in this task.

**Files to modify** (declared atomic batch):
- `Cslib/Logics/Modal/Tableau/S4/InvariantKeys.lean` — new
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib.lean`

**Verification**: same gate set as Phase 2.

---

### Phase 10: Extract `S4/InvariantAcc.lean` [NOT STARTED]

**Goal**: The accessibility/expansion `S4LoopInv` fields, world contiguity, and the pigeonhole
world bound become a module importing `Universe`, `BirthKey`, `Guard`, `Driver`.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Tableau/S4/InvariantAcc.lean` from the Appendix A template.
      **Confirm `@[expose] public section`.**
- [ ] Move the `eNodup`, `accFresh`, and `accKnown` preservation pairs, `accFreshInv_append_S4`,
      `worldsContiguousS4` and its two preservation lemmas,
      `modalKnownWorlds_length_le_worldBoundS4`, and `modalStepBranchS4_worldBound`.
- [ ] Note that `LoopChecking.lean`'s retained termination-measure block consumes
      `modalStepBranchS4_worldBound` and `worldsContiguousS4` — these must be public at module
      scope, not `private`. De-privatize `accFreshInv_append_S4` only if the regenerated graph
      shows a cross-module consumer.
- [ ] Write the "Why a separate module" docstring paragraph.
- [ ] Register in `Cslib.lean`; add the import to `LoopChecking.lean`.
- [ ] Run the shake-prune loop.

**Timing**: 1.5 hours

**Depends on**: 9

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 12 declarations; ~1,320 lines. Confirm before moving.

**Files to modify** (declared atomic batch):
- `Cslib/Logics/Modal/Tableau/S4/InvariantAcc.lean` — new
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib.lean`

**Verification**: same gate set as Phase 2.

---

### Phase 11: Extract `S4/Invariant.lean` [NOT STARTED]

**Goal**: The `S4LoopInv` structure itself, closure preservation, and the two assembling capstone
theorems become a module importing `InvariantKeys` and `InvariantAcc`.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Tableau/S4/Invariant.lean` from the Appendix A template,
      importing `Universe`, `BirthKey`, `Guard`, `Driver`, `InvariantKeys`, `InvariantAcc`.
      **Confirm `@[expose] public section`.**
- [ ] Move `S4LoopInv`, the `eClosure` and `bClosure` preservation pairs, and
      `modalStepBranchS4{,KeyedOrdered}_preserves_S4LoopInv`.
- [ ] Write the "Why a separate module" docstring paragraph, noting that this module is where the
      ten `S4LoopInv` fields are assembled from `InvariantKeys` and `InvariantAcc`.
- [ ] Register in `Cslib.lean`; add the import to `LoopChecking.lean`.
- [ ] Run the shake-prune loop.

**Timing**: 1 hour

**Depends on**: 10

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 7 declarations; ~599 lines. Confirm before moving.

**Files to modify** (declared atomic batch):
- `Cslib/Logics/Modal/Tableau/S4/Invariant.lean` — new
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib.lean`

**Verification**: same gate set as Phase 2.

---

### Phase 12: Extract `S4/HintikkaInvariant.lean` [NOT STARTED]

**Goal**: The keyed-Hintikka and ordered-fuel invariants become the top `S4/` module, importing
`Hintikka`, `InvariantAcc`, and `Invariant`.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Tableau/S4/HintikkaInvariant.lean` from the Appendix A template.
      **Confirm `@[expose] public section`.**
- [ ] Move `S4KeyedHintikkaInv`, `_weaken`, `modalS4Saturated_of_ordered_settled`,
      `S4KeyedHintikkaInv_append`, the two `_preserves_S4KeyedHintikkaInv` theorems,
      `S4OrderedFuelInv`, and `modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv`.
- [ ] Write the "Why a separate module" docstring paragraph.
- [ ] Register in `Cslib.lean`; add the import to `LoopChecking.lean`.
- [ ] Run the shake-prune loop.
- [ ] **Confirm the residue**: after this phase `LoopChecking.lean` should hold exactly the 20
      retained declarations (entry points, termination measure, capstones). Report the actual
      count and line total.

**Timing**: 1 hour

**Depends on**: 8, 11

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 8 declarations; ~801 lines. Residue in `LoopChecking.lean` hypothesised at
20 declarations / ~1,460 lines — confirm both by direct measurement at phase close and record the
observed figures for use in Phase 13's header rewrite.

**Files to modify** (declared atomic batch):
- `Cslib/Logics/Modal/Tableau/S4/HintikkaInvariant.lean` — new
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib.lean`

**Verification**: same gate set as Phase 2, plus the residue count/line report.

---

### Phase 13: Finalize the `LoopChecking.lean` Barrel and Rewrite Its Header [NOT STARTED]

**Goal**: `LoopChecking.lean` becomes a clean barrel-plus-residue with an accurate header, and the
misplaced subsystem-wide census block is re-homed.

**Tasks**:
- [ ] Ensure `LoopChecking.lean` `public import`s **all eleven** `S4/` modules, in alphabetical
      order.
- [ ] Add `-- shake: keep` to the re-exports `LoopChecking.lean`'s own body does not consume.
      Research identifies three: `S4.BirthKey`, `S4.Redirect`, `S4.InvariantKeys`. **Confirm the
      actual set from `check-shake-residue.sh` output rather than assuming these three** — the
      residue's consumption pattern may have shifted during the split.
      Form: `public import Cslib.Logics.Modal.Tableau.S4.Redirect -- shake: keep`.
      This is the established ratchet-free idiom (used in 14 places across `Cslib/`);
      `check-lint-suppressions.sh` counts only blanket `set_option linter.X false` lines and does
      **not** count `-- shake: keep`.
- [ ] Rewrite `LoopChecking.lean`'s module docstring to describe what the file now is: the S4
      driver's entry points, its termination argument, its two end-to-end theorems, and the barrel
      re-exporting the `S4/` cluster. Include a short map of the eleven modules and the layering.
- [ ] Re-home the `## Measured Baseline` block (~155 lines of subsystem-wide census documentation
      — sorry counts, axiom counts, re-derivation tallies — that is not about loop-checking at
      all) to `Cslib/Logics/Modal/Tableau/README.md`. **Correct the stale figures** (`10,540`
      lines / `230` declarations) using the Phase 1 and Phase 12 measurements. This is a required
      edit, not an optional tidy — the numbers are wrong today.
- [ ] Confirm no downstream file needed a change: `git status` must show no modification to
      `S5Simplification.lean`, `FrameCompleteness.lean`, `FrameSoundness.lean`,
      `FiveSimplification.lean`, or `CslibTests/S4LoopGuardRegression.lean` across the whole task.

**Timing**: 1.5 hours

**Depends on**: 12

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: three `-- shake: keep` annotations needed (`BirthKey`, `Redirect`,
`InvariantKeys`); the re-homed block is ~155 lines. Both are hypotheses: confirm the annotation
set from live `check-shake-residue.sh` output and the block extent by reading the current header.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — imports, `-- shake: keep`, header rewrite
- `Cslib/Logics/Modal/Tableau/README.md` — new or extended, receives the census block

**Verification**:
- `lake build Cslib` green
- `bash scripts/check-shake-residue.sh` — no `Modal/Tableau/` findings, count at baseline
- `bash scripts/check-lint-suppressions.sh` — count **not increased** (confirms `-- shake: keep`
  did not move the ratchet)
- `lake exe lint-style` exit 0
- `git diff --stat` confirms zero downstream `.lean` files changed

---

### Phase 14: Update `ORGANISATION.md` [NOT STARTED]

**Goal**: Document the `Tableau/` subtree and add the module-size guidance whose absence is
precisely how an 11,393-line file came to exist.

**Tasks**:
- [ ] **Edit 1**: Replace the single undifferentiated line
      `└── Tableau/  -- Tableau decision procedures (K/T/B/S4/S5 drivers, saturation,
      soundness/completeness)` in the `Modal/` tree with a subtree naming `Support/` (which
      already exists and is currently undocumented) and the new `S4/` cluster with its layering.
      Use the `Foundations/Logic/Tableau/` block in the same file as the formatting precedent.
- [ ] **Edit 2**: Add module-size guidance near the "Namespace Convention" section, stated as
      guidance with an explicit escape hatch rather than a hard gate:
      > **Module size.** Prefer modules under ~1,500 lines. A module past ~3,000 lines should
      > carry a docstring note justifying its size or a tracked plan to split it. Size alone is
      > never a reason to split: split along the *dependency* structure, never by line count — the
      > families inside a large module are typically discontiguous in the source, and a contiguous
      > cut will not find them. Confirm any proposed seam is import-acyclic before writing files.
- [ ] No `Boneyard/` change is needed (already documented; Boneyard archival is a non-goal here).

**Timing**: 0.5 hours

**Depends on**: 13

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: two edits to `ORGANISATION.md`, both in the `Modal/` tree block and the
Namespace Convention area respectively. Confirm the exact target line still reads as quoted before
editing — `grep -n "Tableau" ORGANISATION.md` currently reports it at line 188.

**Files to modify**:
- `ORGANISATION.md`

**Verification**:
- Diff read-through confirming every changed hunk lies inside markdown prose (`prose` tier's
  in-phase check). **Blind spot to cover at the Phase 15 gate**: `ORGANISATION.md` is
  documentation with no compile surface, but broken cross-references are not caught by a diff
  read — verify the module paths named in the new subtree block actually exist on disk.
- Every module path named in the new `S4/` subtree block resolves to a real file.

---

### Phase 15: Full Gate Sweep and Job-Count Reconciliation [NOT STARTED]

**Goal**: Prove the whole split is clean against the Phase 1 baseline, with the one expected
delta (job count) explained rather than waived.

**Tasks**:
- [ ] `bash scripts/pre-pr-check.sh` — all ten steps green.
- [ ] `lake build Cslib` — green. **Record the new job count and reconcile the delta against the
      Phase 1 baseline**: the delta must be explainable by the eleven added modules (plus any
      `README.md`-only change contributing zero jobs). Gate on **green + explainable delta**, not
      on the baseline number.
- [ ] `Modal/Tableau` sorry census — exactly **1**
      (`branchSatisfiableIn_s4FC_ancestor_redirect`, `FrameSoundness.lean`).
- [ ] `bash scripts/check-axiom-census.sh` — exit 0, baseline set **unchanged** (this is a
      move-only refactor; no new tainted declaration is possible).
- [ ] `bash scripts/check-shake-residue.sh` — exit 1 with the baseline finding count,
      **none in `Modal/Tableau/`**. Do not gate on shake exit 0.
- [ ] `bash scripts/check-lint-suppressions.sh` — count **not increased**.
- [ ] `lake exe checkInitImports` — exit 0.
- [ ] `lake exe mk_all --check` — exit 0 (this is what enforces the `Cslib.lean` registrations).
- [ ] `lake exe lint-style` — exit 0.
- [ ] `lake test` — green.
- [ ] `bash scripts/check-boneyard-quarantine.sh` — exit 0 (all five checks).
- [ ] Final reconciliation table in the implementation summary: baseline value vs. observed value
      for every gate, with the job-count delta explained.
- [ ] Record the deferred follow-up: the three zero-consumer `private` declarations remain in
      place and are Boneyard candidates for a separate, separately-committed decision.

**Timing**: 1 hour

**Depends on**: 14

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: eleven new modules; expected job-count increase roughly proportional to
that. The exact delta is not predicted here — it is measured and explained at implementation time.

**Files to modify**:
- `specs/565_loopchecking_split_s4_modules/summaries/01_split-loopchecking-s4-modules-summary.md`
  — new

**Verification**: every gate above green or at its baseline value, with the reconciliation table
written.

---

## Appendix A — The Module Template

Every new `S4/*.lean` reproduces this shape verbatim. The binding conventions are enforced by CI
(`pre-pr-check.sh` step 3: copyright headers; step 5: `lake build --wfail --iofail`) and by the
two most recently landed modules, `Support/Accessibility.lean` and `Support/KnownWorlds.lean`.

```lean
/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.<upstream, pruned by shake>
public import Cslib.Logics.Modal.Tableau.S4.<lower S4 modules>

/-! # <Title>

<Prose: what this module holds.>

## Why a separate module

<Argument against a future reader re-merging it -- see Support/Accessibility.lean's precedent.>

## Main Definitions   -- or ## Main Results
- `foo`: ...
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

...

end Cslib.Logic.Modal.Tableau

end
```

Note the **trailing bare `end`** closing the `@[expose] public section` — present at
`LoopChecking.lean`'s last line and in `Support/KnownWorlds.lean`.

**`open` scope**: `open Cslib.Logic.Tableau Cslib.Logic.Modal` must be replicated verbatim in
every new module. It is what makes the unqualified `Sign`, `SignedFormula`, `RuleResult`,
`Proposition`, and `Accessibility` references resolve.

**Import upper bound** (transitive closure of `LoopChecking.lean` today; prune down from a subset
of this, never add outside it): `Foundations/Logic/Tableau/{Branch, Closure, ClosureCondition,
Measure, PropositionalRules, RuleResult, Sign, SignedFormula}` and `Modal/Tableau/{Branch, Closure,
Completeness, Defs, FmpMeasure, FrameRules, Rules, Saturation, SoundnessStep, Support.Accessibility,
Support.KnownWorlds}`. `TDriver`, `GenericDriver`, and `CompletenessLoop` are **not** in the
closure despite docstring prose references to them — do not add them.

`Cslib.Init` reachability is satisfied transitively via `FmpMeasure`/`FrameRules`/`Branch`. Add an
explicit `import Cslib.Init` only for a module whose pruned import set ends up containing `S4/`
modules only.

## Appendix B — The Per-Phase Shake-Prune Loop

Predicting the minimal import set statically is unreliable — name-based attribution gives false
positives because several declaration names are declared in more than one upstream module. Use the
empirical procedure:

1. Give the new module the full inherited import set from `LoopChecking.lean`.
2. `lake build Cslib`.
3. `bash scripts/check-shake-residue.sh` — remove exactly what it flags for the new module.
4. Rebuild; repeat until the `Modal/Tableau/` finding count is zero and the global count is at the
   Phase 1 baseline.

## Testing & Validation

- [ ] `lake build Cslib` green at every phase boundary; final job-count delta explained by the
      eleven added modules
- [ ] `bash scripts/pre-pr-check.sh` — all ten steps green at Phase 15
- [ ] `Modal/Tableau` sorry census exactly 1 at every phase boundary
- [ ] `bash scripts/check-axiom-census.sh` exit 0, baseline set unchanged
- [ ] `bash scripts/check-shake-residue.sh` — no `Modal/Tableau/` findings; global count at
      baseline (do **not** gate on exit 0)
- [ ] `bash scripts/check-lint-suppressions.sh` — count never increased
- [ ] `lake exe checkInitImports` exit 0
- [ ] `lake exe mk_all --check` exit 0
- [ ] `lake exe lint-style` exit 0
- [ ] `lake test` green
- [ ] `bash scripts/check-boneyard-quarantine.sh` exit 0
- [ ] `git diff --stat` confirms **zero** downstream `.lean` files changed (`S5Simplification`,
      `FrameCompleteness`, `FrameSoundness`, `FiveSimplification`, `CslibTests/*`)
- [ ] Forward-edge check reports zero violations against the final module assignment

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/S4/Universe.lean`
- `Cslib/Logics/Modal/Tableau/S4/BirthKey.lean`
- `Cslib/Logics/Modal/Tableau/S4/Guard.lean`
- `Cslib/Logics/Modal/Tableau/S4/Driver.lean`
- `Cslib/Logics/Modal/Tableau/S4/Hintikka.lean`
- `Cslib/Logics/Modal/Tableau/S4/Redirect.lean`
- `Cslib/Logics/Modal/Tableau/S4/InvariantKeys.lean`
- `Cslib/Logics/Modal/Tableau/S4/InvariantAcc.lean`
- `Cslib/Logics/Modal/Tableau/S4/Invariant.lean`
- `Cslib/Logics/Modal/Tableau/S4/HintikkaInvariant.lean`
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (barrel + 20-declaration residue, rewritten
  header)
- `Cslib/Logics/Modal/Tableau/README.md` (receives the re-homed `## Measured Baseline` block)
- `Cslib.lean` (eleven registrations)
- `ORGANISATION.md` (subtree expansion + module-size guidance)
- `specs/565_loopchecking_split_s4_modules/artifacts/baseline.md`
- `specs/565_loopchecking_split_s4_modules/artifacts/decl-graph.json` (regenerated)
- `specs/565_loopchecking_split_s4_modules/artifacts/module-assignment.md` (regenerated)
- `specs/565_loopchecking_split_s4_modules/summaries/01_split-loopchecking-s4-modules-summary.md`

## Rollback/Contingency

Every phase ends green and is independently committable, so rollback is per-phase: revert the
phase's commit and the tree returns to the previous green state with one fewer extracted module.
`LoopChecking.lean` remains a valid barrel at every intermediate point, so downstream files never
break regardless of how many phases have landed.

If Phase 1's forward-edge check reports violations, **stop before writing any file**: the layering
must be re-derived against the live tree. Re-derivation is a research-scope activity — report and
request a revision rather than guessing an assignment, because a wrong assignment reintroduces an
import cycle that only surfaces several phases later.

If a phase's shake-prune loop cannot reach zero `Modal/Tableau/` findings, do **not** add a blanket
suppression. Either the import set is genuinely needed (in which case the finding is a shake false
positive and `-- shake: keep` on that specific import is the ratchet-free fix), or a declaration is
mis-assigned. Investigate before suppressing.

If `unusedSectionVars` fires newly, narrow the module's `variable` line rather than suppressing —
`check-lint-suppressions.sh` is a ceiling that may only decrease.
