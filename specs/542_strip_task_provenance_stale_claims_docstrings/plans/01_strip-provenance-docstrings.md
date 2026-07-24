# Implementation Plan: Strip Task/Phase Provenance and Stale Claims from Logic-Tree Docstrings

- **Task**: 542 - strip_task_provenance_stale_claims_docstrings
- **Status**: [IMPLEMENTING]
- **Effort**: 9 hours
- **Dependencies**: None (coordinate tasks 543/438/226/425/301 verified non-blocking)
- **Research Inputs**: reports/01_docstring-provenance-sweep.md
- **Artifacts**: plans/01_strip-provenance-docstrings.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, no-task-references-in-deliverables.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This is a pure documentation-hygiene sweep: strip implementation-history narrative (task/phase
numbers, plan references, rollout stories, embedded `specs/NNN` path links, stale sorry/consumer
claims) from shipped docstrings and comments across `Cslib/Logics/{Modal,Propositional,Temporal,Bimodal}`
and `Cslib/Foundations/Logic`, while preserving every mathematical contract and literature
reference. No proof, definition, or `import` changes; zero sorries added or removed. Scope is
~1,299 high-precision provenance lines across ~163 files, with Modal (971 lines / 86 files)
dominating. The edit is judgment-based, not a mechanical `sed` sweep: `no longer` / `used to` /
`previously` phrases frequently describe live mathematics and must be read in context, and no
declaration's only docstring may be deleted (a `docBlame` lint failure). Definition of done: all
provenance removed per the methodology below, and the full CSLib CI suite green (`lake build`,
`lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`, with `docBlame`
especially).

### Research Integration

The plan is built directly on `reports/01_docstring-provenance-sweep.md`. Integrated findings:
- **Provenance inventory** (report §4): per-tree and per-sub-area hit counts drive phase sizing.
  Modal/Tableau (516 hits / 17 files) and the Propositional+Temporal+Bimodal+Foundations remainder
  (~328 hits / ~77 files) are each split into two phases here because each exceeds a single agent
  run; the research's own 5-phase sketch (report §6) grouped them as one apiece.
- **Four specific items** (report §3): item (a) stale "one remaining sorry" comments in the
  Bimodal Chronicle file (file is verified sorry-free), item (c) the Temporal `Completeness.lean`
  commented-out proof carcass (~lines 957-1045) to be replaced by a one-line PTL-FMP pointer,
  item (d) the `Bool.lean` "Matthew Doty's forthcoming work" forward-reference. Item (b)
  (`Algebra/Bridge.lean`) was **already resolved by task 543** and needs only a confirming read.
- **The 24 embedded `specs/NNN` docstring links** (report §4.2) are the most egregious rule
  violations and the top-priority deletions; they are handled within whichever tree phase owns
  each file (file ownership is kept disjoint), never as a separate cross-cutting pass.
- **Editing methodology** (report §5): preserve mathematical contracts and literature/BibKey
  citations, excise only the provenance clause when the two are mixed, substitute durable anchors
  (sibling filename / section heading / the mathematical fact) where provenance explained "why
  this section exists," and never nuke a declaration's sole docstring.
- **Judgment-required phrases** (report §4.3, ~93 lines of `no longer`/`used to`/`previously`/
  `bypassed`/`refactor`/`migration`) are concentrated in the final content phase and flagged for
  per-line contextual reading.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` supplied in the delegation context and no roadmap phases requested; ROADMAP.md
is not consulted or modified by this plan.

## Goals & Non-Goals

**Goals**:
- Remove all task/phase/plan/`specs/NNN`/rollout/`renamed from`/`formerly` provenance narrative
  from shipped docstrings and comments in the five target trees.
- Fix the four specific stale items: (a) Chronicle "one remaining sorry" comments corrected to
  describe the completed, sorry-free construction; (c) Temporal `Completeness.lean` carcass block
  replaced with a one-line mathematical PTL-FMP pointer; (d) `Bool.lean` Doty forward-reference
  reworded to keep only the durable design contract; (b) confirmed already-truthful.
- Delete all 24 embedded `specs/NNN` docstring path links, substituting durable anchors where a
  genuine technique note is lost.
- Keep the library green under the full CSLib CI suite, `docBlame` included.

**Non-Goals**:
- No proof changes, no definition/declaration changes, no `import` changes, no renames.
- No new sorries; no removal of existing (there are none in scope to remove).
- No edits outside the five target trees (task 438's LambdaCalculus / LTL/GNBA files are out of
  scope; `Algebra/Bridge.lean`'s substantive rewrite is already done by task 543).
- No mechanical `sed`/regex bulk deletion — every hit is read in context.
- No task-number or `specs/NNN` citations introduced into any deliverable file (per
  `no-task-references-in-deliverables.md`); the item (c) pointer names the mathematics (PTL Finite
  Model Property), never tasks 425/301.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Over-deletion: a `no longer`/`used to`/`previously` line describing live mathematics is removed | H | M | §4.3 judgment phrases isolated in Phase 7; per-line contextual read mandated; contract-vs-provenance split rule (report §5.1) applied everywhere |
| `docBlame` regression: a declaration's only docstring is deleted to remove provenance | H | M | Strip-don't-nuke rule; every declaration retains its mathematical statement; dedicated Phase 8 runs `lake shake`/`docBlame` across the whole tree before completion |
| Contract corruption: a docstring mixing a contract with a provenance tag loses the contract clause | M | M | Excise only the provenance clause, keep lemma-name cross-references and literature citations (report §5.1-5.2 transforms) |
| New task-number/`specs/NNN` text accidentally introduced (e.g. in item (c) rewrite) | M | L | Durable-anchor substitution only; PTL-FMP mathematical pointer, no task names; advisory `validate-no-task-references.sh` hook surfaces regressions |
| A comment-only edit changes behavior (e.g. touching a code line, or an unclosed `/- -/`) | H | L | Per-phase `lake build` of touched modules; comment-only diffs; final full CI in Phase 8 |
| File-ownership overlap causes conflicting edits across phases | M | L | Disjoint file ownership per phase (explicit exclusion lists); the four specific-item files are owned solely by Phase 1 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4, 5, 6, 7 | -- |
| 2 | 8 | 1, 2, 3, 4, 5, 6, 7 |

Phases within the same wave can execute in parallel: Phases 1-7 own disjoint file sets (no shared
file is edited by two phases), so they carry no inter-phase logical dependency. Under sequential
`/implement`, run Phase 1 first (highest value, judgment-heavy) then 2-7 in any order; Phase 8 is
the single whole-tree CI gate and must run last. Each content phase ends with an incremental
`lake build` of its touched modules and a green commit per the commit-per-green-substep mandate.

---

### Phase 1: Four Specific Items [COMPLETED]

**Goal**: Resolve the four verified stale items in their (disjoint, solely-owned) files. Highest
value, most judgment-heavy, well-localized.

**Tasks**:
- [x] `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` (item a):
  rewrite the line ~51 docstring claim that the `IsSuccArchimedean` discrete case "has one
  remaining sorry (the well-founded termination argument …)" and the line ~426 "(with sorry, like
  the discrete case)" comment to describe the **completed, sorry-free** construction — the file
  has no live `sorry` token. Keep the correct "sorry-free BFMCS" statement near line ~815.
  *(also stripped an incidental "in Phase 4" provenance phrase found in the same block)*
- [x] Same file `## References` (line ~57): keep the `Burgess 1982` literature line; delete the
  `Task 117 plan: specs/117_.../plans/04_case-split-completeness.md` provenance line.
- [x] `Temporal/Tableau/Completeness.lean` (item c): replace the entire
  `/-! ### Remaining FMP-Blocked Obligations … -/` block (~lines 957-1045 — four ```lean-fenced
  commented-out lemma/instance carcasses `temporalTruthLemma_untl`, `temporalTruthLemma_snce`,
  `openBranch_branchSat`, `temporalTableau_complete`, `instDecidableValid`, plus `task 439` /
  `task 426 Phase 3` citations) with a single one-line durable pointer, e.g.: *"The Until/Since
  eventuality-fulfilment cases of the truth lemma — and hence open-branch satisfiability,
  completeness, and the `Decidable (valid ·)` instance — remain blocked on PTL's Finite Model
  Property, which is not yet formalized."* Name the mathematics only; **no task numbers**. Retain
  the live `temporalTruthLemma_propositional_aux` usage near line ~955 (real code, not carcass).
  *(also stripped task/phase provenance from the module docstring's "Main Results"/"Blocked
  Obligations"/"Decomposition Recommendation" sections and the "Time-Ordering Invariant" section,
  since this file is solely owned by Phase 1 and no other phase touches it)*
- [x] `Propositional/Semantics/Bool.lean` (item d, lines 39-41): drop the "(Matthew Doty's
  forthcoming work — not yet in-tree)" parenthetical while keeping the durable design contract:
  *"A future DPLL/Tseitin/CNF procedure should refine these two declarations and reuse this
  module's own `Bool ↔ Prop` bridge (`BoolEvaluate_eq_iff`, `Evaluate_eq_BoolEvaluate`,
  `tautology_iff_boolEvaluate_true`) rather than re-deriving it."* Keep surrounding design notes
  and the `## References` block intact.
- [x] `Propositional/Semantics/Algebra/Bridge.lean` (item b): confirming read only — the task-543
  rewrite is already truthful ("no in-tree consumer … independent algebraic reformulation").
  Grep found zero residual task/phase/specs provenance in the file; no change made.
- [x] `lake build` the four touched modules; confirm comment-only diffs and zero `sorry`.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` - correct stale-sorry comments; drop `specs/117` link
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` - replace carcass block with one-line PTL-FMP pointer
- `Cslib/Logics/Propositional/Semantics/Bool.lean` - remove Doty forward-reference, keep design contract
- `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` - confirm truthful; strip residual provenance only

**Verification**:
- `lake build` of the four modules succeeds; `grep -n "sorry"` shows only prose, no live token; no `specs/` or `task N` string remains in the four files.

---

### Phase 2: Modal/Tableau — Completeness/Loop Cluster [COMPLETED]

**Goal**: Strip provenance from the heaviest Modal/Tableau files (the completeness/loop half of
the 516-hit / 17-file bucket).

**Tasks**:
- [x] `Tableau/FrameCompleteness.lean` (103 hits) — includes an embedded `specs/NNN` link: delete it (top priority).
  *(done: all task/phase/specs provenance stripped across the K/T/B/S5/Five/KB5 sections;
  internal "Phase N" cross-references rewritten to "above"/"below"/lemma-name anchors; the
  embedded `specs/515_.../probes/five-s5-separation.lean` link replaced with a pointer to the
  in-tree `FrameSoundness.lean` lemmas it was citing; `lake build` green, zero live sorry)*
- [x] `Tableau/CompletenessLoop.lean` (73 hits).
  *(done: task/phase provenance stripped throughout; internal "task 515 Phase N" cross-references
  rewritten to "above"/"below" or dropped; bare task-number citations ("503/505/506") reworded to
  name the T/B/S4 systems directly; `lake build` green, zero live sorry; commit 2f93962a)*
- [x] `Tableau/LoopChecking.lean` (72 hits).
  *(done: pervasive "task 511 Phase N" section-header and inline citations stripped; two
  "dispatch"-narrative blocks (bClosure/eClosure closure notes, the `S4LoopInv` preservation
  theorem docstring) rewritten to describe the current completed state instead of dispatch
  history; one literal `[COMPLETED]` phase-status marker and one "the plan" reference also
  removed; `lake build` green, zero live sorry; commit 8d1d66ac)*
- [x] `Tableau/Completeness.lean` (Modal, 32 hits — distinct from the Temporal file in Phase 1).
  *(done: task/phase provenance stripped; `lake build` green, zero live sorry; commit bb979e4c)*
- [x] Any small remaining Tableau files that naturally group with this cluster (implementer's grouping; must stay disjoint from Phase 3's set).
  *(done: `LoopInduction.lean` (2 hits, completeness/loop-themed per the continuation handoff's
  own recommendation) cleaned -- dropped a `(task 404)` citation from an otherwise-legitimate
  design note about superseded helpers. `TDriver.lean`/`BDriver.lean`/`Defs.lean`/`Rules.lean`/
  `SoundnessStep.lean`/`Soundness.lean`/`Saturation.lean` are driver/infrastructure files left for
  Phase 3 per the same recommendation; `FrameRules.lean`/`Closure.lean`/`Branch.lean` have zero
  hits.)*
- [x] Apply the report §5 methodology: excise provenance clauses, keep contracts, lemma cross-references, and literature citations; never delete a sole docstring.
- [x] `lake build` of the touched Modal/Tableau modules.

**Timing**: 1.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` - strip provenance; delete `specs/NNN` link
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` - strip provenance
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - strip provenance
- `Cslib/Logics/Modal/Tableau/Completeness.lean` - strip provenance

**Verification**:
- `lake build` succeeds; no `task N`/`phase N`/`specs/` provenance remains in the touched files; diffs are comment-only.

---

### Phase 3: Modal/Tableau — Soundness/Measure/Simplification Cluster [IN PROGRESS]

**Goal**: Strip provenance from the remaining Modal/Tableau files (the second half of the bucket),
disjoint from Phase 2.

**Tasks**:
- [x] `Tableau/FrameSoundness.lean` (56 hits) — includes an embedded `specs/NNN` link: delete it.
- [x] `Tableau/FmpMeasure.lean` (52 hits).
- [x] `Tableau/S5Simplification.lean` (41 hits) — includes an embedded `specs/NNN` link: delete it.
- [x] `Tableau/FiveSimplification.lean` (39 hits).
- [x] `Tableau/GenericDriver.lean` (36 hits).
- [ ] The remaining lighter Modal/Tableau files not claimed by Phase 2.
- [ ] Apply report §5 methodology throughout.
- [ ] `lake build` of the touched Modal/Tableau modules.

**Timing**: 1.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` - strip provenance; delete `specs/NNN` link
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` - strip provenance
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` - strip provenance; delete `specs/NNN` link
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` - strip provenance
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` - strip provenance
- Remaining `Cslib/Logics/Modal/Tableau/*.lean` not owned by Phase 2

**Verification**:
- `lake build` succeeds; no provenance remains; comment-only diffs; no file overlap with Phase 2.

---

### Phase 4: Modal/Metalogic/Constructive [NOT STARTED]

**Goal**: Strip provenance from `Modal/Metalogic/Constructive` (253 hits / 15 files), including the
`Labelled/` subtree. This sub-area holds the majority of the 24 `specs/NNN` links.

**Tasks**:
- [ ] `Constructive/CS5Canonical.lean` (64), `CS5.lean` (47), `CS4.lean`, `CKExtension.lean`, and `Labelled/PrimeLemma.lean` (45), `Labelled/Soundness.lean` (58), `Labelled/Completeness.lean`, `Labelled/Context.lean`.
- [ ] Delete the embedded `specs/NNN` links in `CS4`, `CS5`, `CS5Canonical`, `CKExtension`, `Labelled/Completeness`, `Labelled/Soundness`, `Labelled/PrimeLemma` (top priority).
- [ ] Note task 544's renames are already in the tree; delete `renamed from`/`formerly` narrative that documents those renames (report §2).
- [ ] Apply report §5 methodology throughout.
- [ ] `lake build` of the touched Constructive modules.

**Timing**: 1.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/{CS4,CS5,CS5Canonical,CKExtension}.lean` - strip provenance; delete `specs/NNN` links
- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/{PrimeLemma,Soundness,Completeness,Context}.lean` - strip provenance; delete `specs/NNN` links
- Remaining `Cslib/Logics/Modal/Metalogic/Constructive/**/*.lean` (15 files total)

**Verification**:
- `lake build` succeeds; no `specs/`/`task N`/`renamed from`/`formerly` provenance remains; comment-only diffs.

---

### Phase 5: Modal/Metalogic Remainder + ProofSystem [NOT STARTED]

**Goal**: Strip provenance from the rest of Modal/Metalogic (Intuitionistic 86, InterSystem 27,
Systems 21, Minimal 6) plus `ProofSystem` (39). ~179 hits.

**Tasks**:
- [ ] `Metalogic/Intuitionistic/TruthLemma.lean` (31) and the rest of `Intuitionistic/` (7 files).
- [ ] `Metalogic/InterSystem/` (7 files), `Metalogic/Systems/` (15 files), `Metalogic/Minimal/` (2 files).
- [ ] `ProofSystem/` (16 files) incl. `ProofSystem/SchemaTags.lean` (lines ~18-30).
- [ ] Apply report §5 methodology; watch for `renamed from` narrative around task-544 renames.
- [ ] `lake build` of the touched modules.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/**/*.lean` (incl. `TruthLemma.lean`)
- `Cslib/Logics/Modal/Metalogic/{InterSystem,Systems,Minimal}/**/*.lean`
- `Cslib/Logics/Modal/ProofSystem/**/*.lean` (incl. `SchemaTags.lean`)

**Verification**:
- `lake build` succeeds; no provenance remains; comment-only diffs; no overlap with Phases 2-4.

---

### Phase 6: Propositional + Temporal (remainder) [NOT STARTED]

**Goal**: Strip provenance from Propositional and Temporal, excluding the three specific-item files
owned by Phase 1 (`Bool.lean`, `Algebra/Bridge.lean`, `Temporal/Tableau/Completeness.lean`).
~156 hits.

**Tasks**:
- [ ] `Propositional/Tableau/Intuitionistic/Scheme.lean` (61 hits) and the rest of Propositional (19 files minus Bool.lean and Algebra/Bridge.lean).
- [ ] Temporal (22 files minus `Tableau/Completeness.lean`).
- [ ] Apply report §5 methodology throughout.
- [ ] `lake build` of the touched Propositional and Temporal modules.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/**/*.lean` EXCEPT `Semantics/Bool.lean` and `Semantics/Algebra/Bridge.lean` (owned by Phase 1)
- `Cslib/Logics/Temporal/**/*.lean` EXCEPT `Tableau/Completeness.lean` (owned by Phase 1)

**Verification**:
- `lake build` succeeds; no provenance remains; comment-only diffs; Phase-1 files untouched here.

---

### Phase 7: Bimodal + Foundations/Logic + §4.3 Judgment Review [NOT STARTED]

**Goal**: Strip provenance from Bimodal (excluding the Chronicle file owned by Phase 1) and
`Foundations/Logic`, and perform the concentrated judgment-required §4.3 review. ~120 hits plus the
~93 `no longer`/`used to`/`previously`/`bypassed`/`refactor`/`migration` lines that must each be
read in context.

**Tasks**:
- [ ] Bimodal (27 files minus `Chronicle/ChronicleToCountermodelBasic.lean`), incl.
  `Metalogic/Separation/Hierarchy/HierarchyInduction.lean` — delete its embedded `specs/NNN` link.
- [ ] `Foundations/Logic/**` (9 files), incl.
  `Metalogic/Chronicle/{ChronicleInterface,SinceSeedConsistency}.lean` — delete their embedded `specs/NNN` links.
- [ ] §4.3 judgment pass: for each `no longer` (43), `used to` (28), `previously` (17),
  `bypassed` (2), `refactor` (4), `migration` (1) hit across all five trees, read in context and
  delete **only** when the sentence is about development history; **keep** when it is about the
  mathematics (e.g. "`R` is no longer symmetric on the sub-frame").
- [ ] `lake build` of the touched Bimodal and Foundations/Logic modules.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Bimodal/**/*.lean` EXCEPT `Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` (owned by Phase 1); incl. `Metalogic/Separation/Hierarchy/HierarchyInduction.lean`
- `Cslib/Foundations/Logic/**/*.lean` incl. `Metalogic/Chronicle/{ChronicleInterface,SinceSeedConsistency}.lean`

**Verification**:
- `lake build` succeeds; no development-history provenance remains; live-mathematics `no longer`/`used to` sentences preserved; comment-only diffs.

---

### Phase 8: Full CI Verification (build, test, checkInitImports, lint-style, shake/docBlame) [NOT STARTED]

**Goal**: Single whole-tree CI gate confirming the sweep introduced no regression and, critically,
no `docBlame` failure (the primary risk of a docstring-stripping task).

**Tasks**:
- [ ] `lake build` (full).
- [ ] `lake test`.
- [ ] `lake exe checkInitImports`.
- [ ] `lake exe lint-style`.
- [ ] `lake shake` (verify no `docBlame` failure — no declaration left docstring-less by the sweep).
- [ ] Repo-wide grep sanity: no remaining `task N` / `Phase N` / `specs/NNN` provenance and no
  live `sorry` introduced in the five trees; confirm the advisory
  `validate-no-task-references.sh` hook surfaces nothing new.
- [ ] If `docBlame` flags any declaration, restore a minimal mathematical docstring for it (strip
  did not preserve enough) and re-run.

**Timing**: 0.75 hours

**Depends on**: 1, 2, 3, 4, 5, 6, 7

**Files to modify**:
- None expected (verification only); minimal docstring restoration if `docBlame` flags a declaration.

**Verification**:
- All five CI commands exit green; `docBlame` clean; grep sanity clean.

## Testing & Validation

- [ ] `lake build` green (per-phase incremental + full in Phase 8).
- [ ] `lake test` green.
- [ ] `lake exe checkInitImports` green.
- [ ] `lake exe lint-style` green.
- [ ] `lake shake` green, `docBlame` in particular (no declaration left without a docstring).
- [ ] All diffs are comment/docstring-only — no proof, definition, or `import` line changed.
- [ ] Zero live `sorry` in scope (none added; the Chronicle file stays sorry-free).
- [ ] No `task N` / `Phase N` / `plan vN` / `specs/NNN` / `renamed from` / `formerly` provenance
  remains in the five trees; literature/BibKey citations retained.
- [ ] No new task-number or `specs/NNN` text introduced into any deliverable (item (c) pointer
  names PTL FMP only).

## Artifacts & Outputs

- plans/01_strip-provenance-docstrings.md (this file)
- summaries/01_strip-provenance-docstrings-summary.md (on implementation completion)
- Comment/docstring-only edits across ~163 files in `Cslib/Logics/{Modal,Propositional,Temporal,Bimodal}` and `Cslib/Foundations/Logic`

## Rollback/Contingency

- All changes are comment/docstring-only and confined to the five target trees, so reversion is a
  clean `git revert`/`git checkout` of the touched `.lean` files with no proof-state consequence.
- If Phase 8 `docBlame` flags a declaration whose docstring was over-stripped, restore a minimal
  mathematical docstring (do not re-add provenance) and re-run — no need to revert the whole phase.
- If a §4.3 judgment call is later found to have removed live-mathematics prose, restore that one
  sentence; the rest of the sweep is unaffected because file ownership is disjoint per phase.
- Per-phase green commits (commit-per-green-substep mandate) keep each phase independently
  revertible.
