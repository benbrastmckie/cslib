# Implementation Plan: Extract re-derived private Tableau facts into public Support modules

- **Task**: 558 - Extract re-derived private Tableau facts into public Support modules
- **Status**: [COMPLETED]
- **Effort**: 14 hours
- **Dependencies**: None
- **Research Inputs**: `specs/558_tableau_support_private_dedup/reports/01_tableau-support-private-dedup.md`
- **Artifacts**: plans/01_tableau-support-private-dedup.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

`Cslib/Logics/Modal/Tableau/` carries **72 duplicate declarations across 41 families**, produced
by re-deriving facts that already exist elsewhere in the subsystem but are `private` (or, in a
few cases, unreachable across the import graph). This plan publishes those facts once — two new
`Support/` modules sitting directly above `Branch.lean`, plus in-place de-privatization inside
`FmpMeasure.lean` — and then deletes the duplicates in graded batches, each batch ending at a
green `lake build Cslib` so progress is committable incrementally.

**The task description's premise that this work is "mechanical and behaviour-preserving by
construction, requires no abstraction decision" is false as written and is not restated here.**
Two families are genuinely non-uniform (§ Risks), and the plan is phased specifically so the safe
bulk is separated from the sites needing per-site judgment. Both hazards are nonetheless
*resolvable* — research established the reconciled inventory of genuinely different propositions
is **zero** — but only if the work is done in the right order, which this plan encodes as phase
dependencies rather than as advisory notes.

### Research Integration

Findings from the research report that materially shape this plan:

- **Drive off signatures, not comments.** The `Local re-derivation` comment census yields 55 real
  sites (57 raw minus 2 self-referential prose lines in `LoopChecking.lean`'s own docstring), but
  **17 duplicate declarations carry no such comment**. A plan that greps the comment string and
  deletes only matches leaves 17 behind while reporting success. The comments are also unreliable
  in the *other* direction: they falsely flag `mem_modalUniverse_of` as deviant when all three
  copies are byte-identical to the original.
- **Two Support modules, not three.** `Support/Accessibility.lean` and `Support/KnownWorlds.lean`
  are correct and cycle-free — their underlying definitions live in `Branch.lean`, which imports
  only `Defs` and `SignedFormula`, so the new modules sit below every consumer.
  `Support/Subfmls.lean` is **not** correct: `modalSubfmls` and `modalUniverse` are defined in
  `FmpMeasure.lean` itself, so such a module would sit *above* `FmpMeasure` and buy nothing.
  Those 23 duplicates need only de-privatization in place.
- **Ordering is load-bearing.** `mem_modalKnownWorlds` must be published **before** any attempt to
  route the six weak `modalKnownWorlds_fold_spec_*` copies through the strong original. Each weak
  copy has exactly one call site — inside the corresponding `mem_modalKnownWorlds_X` proof — so
  publishing `mem_modalKnownWorlds` first strands all six as dead code, deletable with no `Nodup`
  obligation and no call-site edits.
- **Reachability, not privacy, is the real justification.** All six consumers already reach
  `FmpMeasure` transitively, so de-privatization alone suffices there. But `FiveSimplification`,
  `LoopChecking`, and `S5Simplification` do **not** reach `Soundness.lean`, where
  `hasEdge_addEdge_cases` (7 copies — the largest family) is private. De-privatization *cannot*
  fix that family; lowering the fact to `Branch` level can. This is why `Support/` exists.
- **`Branch.lean` is the architecturally natural home, and it is do-not-edit.** That constraint —
  not arbitrary taste — is what makes a separate `Support/` directory correct. It must be recorded
  in the new modules' docstrings so a later reader does not "simplify" the structure away by
  folding the lemmas back into `Branch.lean`.
- **`lake shake` is not green at baseline** (exit 1, 9 findings, none in `Modal/Tableau/`).
- **Privacy is not the sole root cause.** `modalSubfmls_self_mem`'s original is already public;
  its copy exists to dodge an ambient `[Hashable Atom]` instance callers cannot `omit`.
  De-privatizing will not remove it.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `specs/ROADMAP.md` consulted for this task (no `roadmap_path` supplied).

---

## REQUIRED `file_scope` WIDENING (orchestrator action before dispatch)

**Implementation is blocked until `state.json`'s `file_scope` for this task is replaced with the
list below.** The currently declared scope names only the modules owning private *originals* and
omits every file where the 72 duplicates are actually *deleted*, plus `Cslib.lean`. Nine files
are missing. Research confirmed none of the additions collide with the do-not-edit list
(`Rules.lean`, `Saturation.lean`, `Branch.lean` — zero duplicates and zero re-derived privates
in all three).

Complete, explicit, repo-relative file list:

```
Cslib.lean
Cslib/Logics/Modal/Tableau/Support/Accessibility.lean
Cslib/Logics/Modal/Tableau/Support/KnownWorlds.lean
Cslib/Logics/Modal/Tableau/FmpMeasure.lean
Cslib/Logics/Modal/Tableau/Soundness.lean
Cslib/Logics/Modal/Tableau/SoundnessStep.lean
Cslib/Logics/Modal/Tableau/Completeness.lean
Cslib/Logics/Modal/Tableau/CompletenessLoop.lean
Cslib/Logics/Modal/Tableau/TDriver.lean
Cslib/Logics/Modal/Tableau/BDriver.lean
Cslib/Logics/Modal/Tableau/LoopChecking.lean
Cslib/Logics/Modal/Tableau/S5Simplification.lean
Cslib/Logics/Modal/Tableau/FiveSimplification.lean
Cslib/Logics/Modal/Tableau/FrameSoundness.lean
Cslib/Logics/Modal/Tableau/FrameCompleteness.lean
```

The first two entries are **new files** (the `Support/` directory does not yet exist). The last
four `Completeness`/`CompletenessLoop`/`TDriver`/`SoundnessStep` entries are needed only by
Phase 10 (Tier-3 triage) and may be touched read-only if that phase's exclusions absorb them.

---

## Invariants (must hold at EVERY commit, not only at the end)

These are gate conditions for every phase, checked before each phase-closing commit.

| Invariant | Check | Required value |
|---|---|---|
| Build | `lake build Cslib` | exit 0 |
| Init imports | `lake exe checkInitImports` | exit 0, no output |
| Style lint | `lake exe lint-style` | exit 0, no output |
| Shake, subsystem | `lake shake --add-public --keep-implied --keep-prefix 2>&1 \| grep 'Modal/Tableau'` | **empty** |
| Shake, global count | same command, finding count | **stays at 9** (overall exit 1 is baseline — do NOT demand exit 0) |
| Subsystem sorry census | grep census below, filtered to `Modal/Tableau/` | **exactly 1**, and it is `branchSatisfiableIn_s4FC_ancestor_redirect` |
| Axioms | `grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/ \| wc -l` | **0** |
| Landed results green | `modalTableauS4Keyed_complete` + the six `Decidable` instances (K/T/B/S5/Five/KB5) | elaborate without error |

**Sorry anchoring**: the retained sorry belongs to declaration
`branchSatisfiableIn_s4FC_ancestor_redirect` in `FrameSoundness.lean`. The task description pins
it at line 1244; it is **not** there — the declaration has moved (currently ~1252, token ~1276).
**Locate it by declaration name. Never by line number.** Re-locate with:

```bash
grep -rn 'branchSatisfiableIn_s4FC_ancestor_redirect' Cslib/
```

Sorry census command:

```bash
{ grep -rnE '^[[:space:]]*sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; \
  grep -rnE '(:=|\bby)[[:space:]]+sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; } \
  | sort -u | grep 'Modal/Tableau/'
```

**No `sorry` is introduced at any point.** Every phase is a delete-and-redirect over facts already
proven in the tree; no phase creates a proof obligation lacking an existing proof.

---

## Goals & Non-Goals

**Goals**:
- Publish `hasEdge_addEdge_cases`, `mem_successorsOf_hasEdge`, and `hasEdge_mem_successorsOf` from
  a new `Support/Accessibility.lean` importing only `Cslib.Logics.Modal.Tableau.Branch`.
- Publish the KnownWorlds family from a new `Support/KnownWorlds.lean`, also importing only
  `Branch`, with `mem_modalKnownWorlds` published first.
- De-privatize the ~14 re-derived declarations in `FmpMeasure.lean` in place, with docstrings.
- Delete the resolvable duplicates — the safe bulk (~56 declarations) plus the judgment-needing
  subset (~16) — driven off the declaration-level census.
- Record the reachability rationale and the do-not-edit-`Branch.lean` rationale in the new
  modules' docstrings.
- Leave the residue (Tier-3, public-origin, structurally impossible) explicitly accounted for
  rather than silently unmentioned.

**Non-Goals**:
- **No `Support/Subfmls.lean`.** Dropped on evidence; see Research Integration.
- **No move of `outDeg` down to `Support/Accessibility.lean`.** Moving a `def` is a
  behaviour-relevant change with `shake`/`checkInitImports` consequences, and the payoff (letting
  `outDeg_addEdge_self/_ne` join Tier 1) is small. `outDeg_addEdge_self/_ne` are handled as Tier-2
  de-privatization instead. Recorded as a deliberate decision, not an oversight.
- **No deletion of the 8 public-origin duplicate families.** Their duplication is not caused by
  privacy, so it is outside this task's stated root cause; they are either genuine specialisations
  or gratuitous duplication needing a separate judgement call. Phase 10 records them and
  recommends a follow-up task.
- **No touch to `Rules.lean`, `Saturation.lean`, or `Branch.lean`.**
- No module split, no file-size reduction beyond what deletion incidentally achieves.
- No attempt to make `lake shake` exit 0.
- No new `sorry`, no new `axiom`.

---

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|---|---|---|---|
| Comment-driven deletion misses the 17 uncommented duplicates and the task reports false success | H | H | Every deletion phase carries a **Scope Hypothesis** requiring a declaration-level (suffix-family) census before and after; comment counts are a secondary signal only |
| `modalKnownWorlds_fold_spec`: original is strictly stronger (extra `Nodup` hypothesis + conjunct) at 6 sites | H | H | Phase ordering, not proof work: publish `mem_modalKnownWorlds` in Phase 4, migrate it in Phase 5 — the 6 weak copies then have zero call sites and delete outright. Publishing the strong `fold_spec` first and routing through it is the harder path and is explicitly not taken |
| `modalMaxWorld` exists in 4 binder-incompatible variants | M | H | 26 of 30 call sites use `apply`, which is binder-mode insensitive. Only **4 term-mode sites** need manual adjustment (`FmpMeasure.lean` ~1884, `S5Simplification.lean` ~1167, `FiveSimplification.lean` ~3328, `LoopChecking.lean` ~6201), each a single line inside a wrapper proof being deleted anyway. Named explicitly in Phase 6; not assumed to be a clean sweep |
| `modalKnownWorlds_mono_append`: `⊆` (strict-implicit binder) vs `∀ x ∈` (explicit) changes application arity at every call site | M | H | Adopt `∀ x ∈` as canonical public form — it matches all five external call-site populations; the `⊆` original is the only `⊆` user, with 2 internal sites. Isolated to Phase 6 |
| De-privatization grows public API surface and trips `docBlame`/lint | M | M | Publish only the ~14 declarations that are actually re-derived; the other ~36 `FmpMeasure` privates stay private. Every newly-public declaration gets a docstring in the same edit |
| Adding imports perturbs `lake shake` findings outside the subsystem | M | L | Gate is "no `Modal/Tableau` findings AND count stays at 9", not "exit 0" — a clean-exit gate would fail on pre-existing unrelated noise |
| Five of the seven must-stay-green declarations live in `FrameCompleteness.lean`, which also loses duplicates | H | M | Full `lake build Cslib` per phase (and per green sub-step), never final-only |
| Large mechanical edits across six oversized files exhaust an agent run mid-phase | M | M | Phases sized to roughly one agent run; deletion batches split by file group (Phases 8 and 9); `per-substep` commit mode throughout so partial progress is durable |
| `modalSubfmls_self_mem` copy survives de-privatization (dodges an ambient `[Hashable Atom]` instance) | L | H | Pre-declared: it is *expected* to survive. Recorded as a reasoned exclusion in Phase 10, not chased |
| `modalApplyOneS5_fresh_local_local` (S5Simplification) mirrors a fact in `FrameSoundness`, which **imports** S5Simplification | L | H | Structurally unresolvable by importing. Pre-declared out of scope in Phase 10 |

---

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
| 9 | 9 | 8 |
| 10 | 10 | 9 |
| 11 | 11 | 10 |

Phases within the same wave can execute in parallel.

**Why every wave holds exactly one phase**: parallelism was evaluated and declined on territory
grounds, not omitted by default. Phases 2 and 4 (module creation) are logically independent of
each other, and Phase 7 is logically independent of both — but all three write `Cslib.lean` or
`FmpMeasure.lean`, and the six consumer files recur in nearly every deletion phase. Concurrent
edits would collide on shared territory and break the per-phase green-build guarantee that makes
incremental commits possible. Execute sequentially.

---

### Phase 1: Free deletions — dead code with zero call sites [COMPLETED]

**Goal**: Remove declarations that have no call sites at all, plus the one intra-file duplicate
that needs no module, no import, and no publication. Establishes the census tooling and confirms
the baseline gate values before any structural change.

**Tasks**:
- [x] Record the baseline: run every command in the Invariants table and capture actual values
      (build job count, shake finding count, sorry census line, axiom count). Confirm shake exits
      1 with 9 findings and none in `Modal/Tableau`. *(Confirmed exactly: build 3311 jobs green;
      shake exit 1, 9 findings, 0 in Modal/Tableau; sorry census 1 line, decl
      `branchSatisfiableIn_s4FC_ancestor_redirect` at FrameSoundness.lean:1252 (sorry token at
      :1276); axiom count 0.)*
- [x] Build the declaration-level census script: enumerate `private lemma <base>_<SUFFIX>`
      declarations (suffixes `_B _C _S4 _S5 _S5w _Five _FS _anc _local _origin _S4Keyed`) whose
      `<base>` also exists elsewhere in the subsystem. Record the baseline count. Save the script
      under the task directory so later phases re-run the identical query. *(Saved to
      `specs/558_tableau_support_private_dedup/scripts/census.py`, a two-signal Python census:
      exact-name duplicates plus suffix-family duplicates, with block-comment stripping to avoid
      docstring-prose false positives. **Scope Hypothesis discrepancy**: measured baseline is
      **74 duplicate declarations across 43 families**, not the plan's estimated 72/41. Verified
      by hand-auditing every family against the plan's own named-family lists across all phases;
      the only two families not named anywhere in the plan text are `modalApplyOneT_branchingLength`
      (LoopChecking.lean:8325 vs TDriver.lean:697, both private) and
      `modalApplyOneT_persistentFresh` (LoopChecking.lean:8248 vs TDriver.lean:373, both private) —
      genuine private/private duplicate pairs the plan's research did not individually enumerate.
      Recorded here per the Scope Hypothesis rule: using the measured 74/43 as the denominator for
      all later phases; these two extra families are flagged for Phase 10 residue triage since they
      fit the Tier-3 "origin private and reachable" shape.)*
- [x] Confirm by call-site search which declarations have **zero** call sites. Research names
      `modalKnownWorlds_nodup_S5` (S5Simplification.lean ~1079) and its helper
      `modalKnownWorlds_fold_nodup_S5` (~1061). Confirm whether a third exists before deleting.
      *(Confirmed via repo-wide grep: `modalKnownWorlds_nodup_S5` has zero call sites outside its
      own declaration line; its sole use of the helper is internal. No third zero-call-site
      declaration found.)*
- [x] Delete the confirmed zero-call-site declarations. *(Deleted both from S5Simplification.lean.)*
- [x] Move `hasEdge_mem_successorsOf` (LoopChecking.lean ~6764) earlier within
      `LoopChecking.lean`, above its first use, and delete the forward-reference workaround
      duplicate `hasEdge_mem_successorsOf_origin` (~1350). Both are private and file-local, so no
      downstream module can observe the change. *(Done: relocated to line ~1349, both former call
      sites of `_origin` (lines 1606, 1646) redirected to the relocated name; the two original
      call sites at ~6800/~6886 needed no edit since the name is unchanged, only its declaration
      site moved earlier.)*
- [x] Confirm `modalKnownWorlds_nodup_S4` (LoopChecking.lean ~6598) is **public** and **live**
      (2 uses) — it is NOT dead and must not be deleted here. *(Confirmed public, 2 live call
      sites at LoopChecking.lean:6648,6676 (post-edit line numbers). Not touched.)*

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts (a) exactly 2-3 declarations have zero call sites, and
(b) the duplicate-declaration census baseline is 72 across 41 families. Confirm (a) by a
whole-subsystem grep for each candidate name (excluding its own declaration line) returning no
hits before deletion; confirm (b) by running the census script and comparing to 72 — if the
measured baseline differs, record the actual number and use it, not 72, as the denominator for
every later phase.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — delete dead `modalKnownWorlds_nodup_S5`
  and `modalKnownWorlds_fold_nodup_S5`
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — relocate `hasEdge_mem_successorsOf`; delete
  `hasEdge_mem_successorsOf_origin`

**Post-close census methodology addendum** (discovered auditing Phase 2's Accessibility family,
recorded here rather than silently rewriting the number above): the census script was refined
twice after this phase closed. (1) A same-file false-positive class was found and fixed --
suffix/prime-stripped names sharing a base were only genuine re-derivation duplicates when they
spanned 2+ distinct files (same-file "prime" siblings like `mem_modalUniverseS4_of` /
`mem_modalUniverseS4_of'` are legitimate distinct lemmas, not duplicates; confirmed by reading
both). (2) A trailing-prime suffix pass was trialled, found to catch real cross-file duplicates
(`mem_successorsOf_hasEdge'`, `modalApplyOneT_boxPos_fst'`/`_diamondNeg_fst'`) but ALSO
over-merged unrelated same-base declarations across suffix flavors, and was reverted as a known
gap -- primed duplicates must be found by manual per-family grep, not trusted to `census.py`'s
count. **Re-measured on the current (post-Phase-1) tree with the final script: 71 duplicate
declarations across 41 families** -- almost exactly the plan's original 72/41 estimate (family
count matches exactly). This is the run to record here since it reflects the census logic
follow-on phases will actually reuse; it applies to the tree as of Phase 1's close, not to an
earlier baseline. Used as the working denominator from Phase 2 onward.

**Verification**:
- Full Invariants table passes.
- Census count drops by the number of declarations deleted (expected 3-4).
- No import lines changed anywhere in this phase.

---

### Phase 2: Create `Support/Accessibility.lean` [COMPLETED]

**Goal**: Publish the Accessibility-level facts once, in a module importing only `Branch`, and
register it. No consumer is changed yet, so the phase is additive and cannot break anything.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Tableau/Support/Accessibility.lean` with
      `public import Cslib.Logics.Modal.Tableau.Branch` as its **only** Tableau import.
- [x] Publish `hasEdge_addEdge_cases` with the exact signature of the `Soundness.lean` original
      (all 7 copies are byte-identical; `hasEdge_addEdge_cases_anc` renames `a a'` to `u u'`,
      which is alpha-equivalent and harmless).
- [x] Publish `mem_successorsOf_hasEdge` and its converse `hasEdge_mem_successorsOf`. These are
      two distinct facts forming a converse pair, not one family with a direction mismatch — do
      not attempt to unify them. *(Published both, verbatim from FmpMeasure.lean's and the
      Phase-1-relocated LoopChecking.lean copies respectively.)*
- [x] Write a module docstring stating: (i) these facts are lowered to `Branch` level because
      `FiveSimplification`, `LoopChecking`, and `S5Simplification` do **not** reach
      `Soundness.lean`, so de-privatization alone cannot reach them; (ii) `Branch.lean` is the
      architecturally natural home and is under a do-not-edit constraint — that constraint is why
      this separate module exists, and folding these lemmas back into `Branch.lean` is not a
      simplification.
- [x] Give every published declaration its own docstring (required once public — `docBlame`).
- [x] Use `lemma` for Prop-valued results (`defLemma`); preserve existing snake_case lemma names
      (conventional in this subsystem and consistent with Mathlib practice); wrap in an explicit
      namespace (`topNamespace`); keep section variables minimal, applying `omit` where needed
      (`unusedSectionVars`) — see the existing `omit [DecidableEq Atom] [Hashable Atom] in`
      pattern in `BDriver.lean`. *(No `variable {Atom...}` block declared at all in the new
      module — all three published facts are `Atom`-independent (they only mention
      `Accessibility`/`WorldIndex`), so the minimal choice is to omit the section variable
      entirely rather than declare-then-`omit` per lemma.)*
- [x] Register `public import Cslib.Logics.Modal.Tableau.Support.Accessibility` in `Cslib.lean`,
      alphabetically within the Tableau block (currently lines 492-511). *(Inserted between
      `SoundnessStep` and `TDriver`.)*

**Deviation note**: the plan's own comparison audit for `mem_successorsOf_hasEdge` during this
phase surfaced a **fourth** copy not named anywhere in the plan text:
`FrameSoundness.lean`'s `mem_successorsOf_hasEdge'` (trailing-prime name, not an underscore
suffix — `census.py`'s suffix-only matching does not catch this naming convention; see the
Phase 1 addendum). Confirmed genuine by its docstring ("restated here since that lemma is
private to its own file"). Deferred to Phase 3, which is the phase that actually deletes
Accessibility-family duplicates — flagged here so Phase 3 does not miss it.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Support/Accessibility.lean` (new)
- `Cslib.lean` — add module registration

**Verification**:
- Full Invariants table passes. `lake exe checkInitImports` exiting 0 is the specific check that
  the registration landed correctly.
- `lake shake` reports no finding for the new module and the global count is still 9.
- The new module's transitive imports include nothing above `Branch`.

---

### Phase 3: Migrate Accessibility consumers — delete ~10 duplicates [COMPLETED]

**Goal**: Import `Support/Accessibility` where needed, delete every duplicate of the three
published facts, and remove the now-unused private original from `Soundness.lean`.

**Tasks**:
- [x] Add `public import Cslib.Logics.Modal.Tableau.Support.Accessibility` to each file that
      needs it. *(Added to BDriver.lean, FmpMeasure.lean, FrameCompleteness.lean,
      FrameSoundness.lean, LoopChecking.lean, Soundness.lean — the 6 files that used any of the
      three published facts. S5Simplification.lean needed no import since its sole family member
      was dead code, deleted outright.)*
- [x] Delete all `hasEdge_addEdge_cases` duplicates. Known sites span `BDriver.lean`,
      `FrameCompleteness.lean` (×2), `FrameSoundness.lean` (×2, one of them
      `hasEdge_addEdge_cases_anc`), `LoopChecking.lean`, `S5Simplification.lean`, and
      `FmpMeasure.lean` (~1080, `hasEdge_addEdge_cases_local` — `FmpMeasure` does not import
      `Soundness` either, so it drops a duplicate too). *(Deviation: no `S5Simplification.lean`
      copy of `hasEdge_addEdge_cases` actually exists — confirmed by direct grep before editing;
      the plan's own family-site list here was one file short of what's on disk, 7 real copies
      not 8. Deleted the 7 that do exist: BDriver_B, FmpMeasure_local, FrameCompleteness_Five,
      FrameCompleteness_C, FrameSoundness_anc, FrameSoundness_FS, LoopChecking_S4, plus removed
      the Soundness.lean original itself and redirected its 1 internal use.)*
- [x] Remove `private lemma hasEdge_addEdge_cases` from `Soundness.lean` and redirect its 1
      internal use to the published form. *(Since the published name is identical to the
      original's name, the internal call site needed no text edit — only the private declaration
      was removed and the import added.)*
- [x] Delete the `mem_successorsOf_hasEdge` duplicates (2) and route uses to the published form.
      *(Deviation: actual count is 3, not 2 — `LoopChecking.lean`'s `_S4` copy,
      `S5Simplification.lean`'s `_S5` copy (found to be genuinely DEAD, zero call sites anywhere,
      deleted outright with no redirect needed), and a fourth-flavor copy the plan's text did not
      name at all: `FrameSoundness.lean`'s `mem_successorsOf_hasEdge'` (trailing-prime naming,
      not an underscore suffix — flagged in the Phase 2 handoff, resolved here). Also removed the
      `FmpMeasure.lean` original itself, same identical-name situation as `hasEdge_addEdge_cases`
      above — no call-site text edit needed there, only the private declaration removed.)*
- [x] Delete any `Local re-derivation` comment left orphaned by these deletions. *(Deleted along
      with each declaration block, since the comment was always the declaration's own docstring.
      One additional stale prose reference was found and fixed: `FrameSoundness.lean`'s
      sorry-carrying `branchSatisfiableIn_s4FC_ancestor_redirect` docstring cited the
      Phase-1-deleted name `hasEdge_mem_successorsOf_origin` by name in an unrelated explanatory
      paragraph; reworded to cite the current `Support.Accessibility`-published name instead. The
      sorry itself and its surrounding proof term were not touched.)*
- [x] Confirm the six landed `Decidable` instances and `modalTableauS4Keyed_complete` still
      elaborate (five of the seven live in `FrameCompleteness.lean`, which is edited here).
      *(Confirmed via full `lake build Cslib` success, 3312 jobs — unchanged from Phase 2 since
      this phase adds no new module.)*

**Additional deviation**: Phase 3 also deleted `hasEdge_mem_successorsOf` (LoopChecking.lean's
private copy, relocated in Phase 1) and routed its 4 call sites to the `Support.Accessibility`
published copy of the same name — this consolidation was implicit in the plan's Phase 2 "publish
the converse pair" step but not spelled out as an explicit Phase 3 task; recorded here for
completeness since it required its own declaration-block deletion, matching the same
identical-name-no-call-site-edit pattern as the other two origin removals.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts ~10 duplicate declarations across 8 files. Confirm by
re-running the Phase 1 census script filtered to the `hasEdge_addEdge_cases`,
`mem_successorsOf_hasEdge`, and `hasEdge_mem_successorsOf` families **before** editing, and
re-running it after — the family count must reach 0. If the pre-edit count is not ~10, use the
measured number and record the discrepancy; do not delete to hit a target.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Soundness.lean`
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
- `Cslib/Logics/Modal/Tableau/BDriver.lean`
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean`
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`

**Verification**:
- Full Invariants table passes after each green sub-step, not only at phase end.
- The three published families report zero remaining duplicates in the census.

---

### Phase 4: Create `Support/KnownWorlds.lean` [COMPLETED]

**Goal**: Publish the KnownWorlds family once, in a module importing only `Branch`. Additive —
no consumer changes, no deletions.

**Tasks**:
- [x] Create `Cslib/Logics/Modal/Tableau/Support/KnownWorlds.lean` with
      `public import Cslib.Logics.Modal.Tableau.Branch` as its **only** Tableau import.
- [x] Publish `mem_modalKnownWorlds` — byte-identical across all 7 occurrences, and the
      highest-leverage single declaration in the whole task. **Publish this one; the ordering
      matters and Phase 5 depends on it.** *(Declared after `modalKnownWorlds_fold_spec` in the
      FILE, since its proof calls `fold_spec` — the plan's "publish this first" is a phase-level
      dependency ordering (must exist before Phase 5 migrates consumers), not an in-file
      declaration-order requirement; the two are independent and both are satisfied.)*
- [x] Publish `modalKnownWorlds_fold_spec` in the **strong** form (carrying `hws0 : ws0.Nodup` and
      the `Nodup` conjunct), matching the `FmpMeasure` original. It is published because
      `modalKnownWorlds_nodup` needs it — **not** as a migration target for the six weak copies.
- [x] Publish `modalKnownWorlds_nodup`.
- [x] Publish `modalKnownWorlds_mono_append` in the **`∀ x ∈ …` form**, not the `⊆` form. Decision
      rationale to record in its docstring: `List.Subset` unfolds to a strict-implicit binder
      `⦃a⦄` while all five external call-site populations bind `x` explicitly; the `⊆` original is
      the only `⊆` user, with 2 internal call sites. The `∀ x ∈` form minimises churn.
- [x] Publish `mem_boxPositivesOf`.
- [x] Publish `modalMaxWorld_le_of_forall_label_le` in the **implicit-binder wrapper form**
      (`{l} {M} (h) : modalMaxWorld l ≤ M`) — 24 of the 26 `apply` call sites already expect it —
      together with its `foldl` helper as internal scaffolding. *(Deviation: the plan's
      description implied this declaration's true origin was `FmpMeasure.lean`; the actual origin
      (unsuffixed, matching the plan's exact target name) is `LoopChecking.lean:6155`, and it uses
      ALL-EXPLICIT binders `(l : ...) (K : ...)` there — the opposite of what the plan asks to
      publish. The two OTHER copies, `_Five` (FiveSimplification.lean) and `_S5w`
      (S5Simplification.lean), already use the implicit-binder form the plan wants, so the
      published form was built from those two, not from the nominal "origin". `FmpMeasure.lean`
      separately has an unrelated differently-named wrapper, `modalMaxWorld_le_of_forall_le`, not
      touched by this phase.)*
- [x] Module docstring: same two-part rationale as Phase 2 (reachability, and the do-not-edit
      `Branch.lean` constraint as the reason this module exists separately).
- [x] Per-declaration docstrings; `lemma` not `def` for Prop-valued; explicit namespace; minimal
      section variables with `omit` where needed. *(No typeclass instances declared at all —
      none of these six facts need `DecidableEq Atom`/`Hashable Atom`, so the minimal choice is
      to omit the instances entirely rather than declare-then-`omit` per lemma, matching Phase 2's
      Accessibility module.)*
- [x] Register `public import Cslib.Logics.Modal.Tableau.Support.KnownWorlds` in `Cslib.lean`,
      alphabetically. *(Inserted immediately after `Support.Accessibility`.)*

**Build note**: the `foldl` helper's proof initially failed with an instance-diamond mismatch
(`max_le`, a generic Mathlib `LinearOrder` lemma, elaborated against `LinearOrder.toMax` while
`modalMaxWorld`'s own `max` — defined in the minimally-importing `Branch.lean` — resolves to core
`Nat.instMax`). Fixed by using `Nat.max_le.mpr` instead of the generic `max_le`, matching the
pattern `Branch.lean` itself already uses in `modalMaxWorld_le_append`. Recorded since a future
Support module built on `Branch.lean`'s minimal import surface should expect the same class of
diamond and reach for the `Nat`-specific lemma rather than the general order-theoretic one.

**Timing**: 2 hours

**Depends on**: 3

**Verification Tier**: full

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Support/KnownWorlds.lean` (new)
- `Cslib.lean` — add module registration

**Verification**:
- Full Invariants table passes.
- `lake exe checkInitImports` exits 0 (registration correctness).
- The new module's transitive imports include nothing above `Branch`.

---

### Phase 5: Migrate `mem_modalKnownWorlds`; the 6 weak `fold_spec` copies die as dead code [COMPLETED]

**Goal**: The ordering-critical phase. Route consumers to the published `mem_modalKnownWorlds`,
which strands all six `modalKnownWorlds_fold_spec_*` copies with zero call sites, at which point
they delete outright — no substitution, no call-site edit, no `Nodup` obligation.

**Tasks**:
- [x] Add `public import Cslib.Logics.Modal.Tableau.Support.KnownWorlds` where needed.
      *(Added to BDriver.lean, FiveSimplification.lean, FmpMeasure.lean, FrameCompleteness.lean,
      FrameSoundness.lean, LoopChecking.lean, S5Simplification.lean — every file that used either
      of the two published families, including `FmpMeasure.lean` itself, whose own `_fold_spec`
      and `mem_modalKnownWorlds` are the ORIGINS and needed the import once their private copies
      were removed.)*
- [x] Delete the 6 `mem_modalKnownWorlds_*` duplicates and route their uses to the published form.
      *(Deleted from BDriver/FiveSimplification/FrameCompleteness/FrameSoundness/LoopChecking/
      S5Simplification; also deleted the `FmpMeasure.lean` origin itself — same identical-name
      pattern as Phase 3, no call-site text edit needed there.)*
- [x] **Then**, and only then, confirm each of the six `modalKnownWorlds_fold_spec_*` copies has
      zero remaining call sites. *(Confirmed structurally rather than by a separate pre-deletion
      grep pass: each weak `fold_spec_X`'s sole call site, verified by direct reading, was inside
      its file's own `mem_modalKnownWorlds_X` proof body — nowhere else. Deleted both blocks
      together per file in one edit; the full-project build succeeding, plus a post-edit
      repo-wide grep confirming zero remaining references to any of the six names, is the
      after-the-fact confirmation that no other call site existed.)*
- [x] Delete all six weak `modalKnownWorlds_fold_spec_*` copies. *(Done, per above.)*
- [x] Do **not** attempt to route any consumer through the strong `fold_spec`. If a copy still has
      a call site after the migration, stop and record it rather than manufacturing a `Nodup`
      proof — that would signal the ordering assumption failed and needs re-examination.
      *(Not needed: no copy retained a call site.)*
- [x] Remove orphaned `Local re-derivation` comments. *(Removed along with each deleted block.)*

**Forced deviation, discovered mid-phase**: adding the `Support.KnownWorlds` import to
`FmpMeasure.lean` and `LoopChecking.lean` (needed to resolve their OWN `mem_modalKnownWorlds`/
`modalKnownWorlds_fold_spec` origins) exposed a Lean name-collision error: both files still held
OTHER private declarations with names EXACTLY matching other Support.KnownWorlds publications --
`FmpMeasure.lean`'s `modalKnownWorlds_nodup`, `modalKnownWorlds_mono_append`, and
`mem_boxPositivesOf` (nominally Phase 6/7 territory), and `LoopChecking.lean`'s
`modalMaxWorld_le_of_forall_label_le` (nominally Phase 6 territory, one of the plan's own
"4 term-mode sites needing manual adjustment"). Lean forbids a private declaration and an
imported public declaration sharing the same fully-qualified name, so these could not be
deferred to their nominal phase without also deferring this phase's own import. Resolved by
deleting all four now:
- `mem_boxPositivesOf`, `modalKnownWorlds_nodup` (`FmpMeasure.lean`): byte-identical statements,
  zero risk, no call-site edits needed (identical published name).
- `modalKnownWorlds_mono_append` (`FmpMeasure.lean`, `⊆` form vs. Support's `∀ x ∈` form): its 3
  internal call sites (`exact modalKnownWorlds_mono_append nf b` / `br b`) needed **no edit** --
  `exact` unifies `List.Subset`'s strict-implicit-binder unfolding against the `∀ x ∈` explicit
  form via defeq without complaint. This is a useful empirical finding for the REST of Phase 6:
  the plan's "changes application arity, touch every call site" warning may be narrower in
  practice than stated, at least for plain `exact`-style application (as opposed to `rw` or
  partial application) — worth re-verifying per remaining call-site population in Phase 6 rather
  than assuming every site needs editing.
- `modalMaxWorld_le_of_forall_label_le` (`LoopChecking.lean`, all-explicit-binder form): its 9
  internal call sites all use `apply`, confirmed binder-mode insensitive as the plan predicted;
  no edit needed. Its private `foldl_max_le_of_forall_le` helper was left in place (unique name,
  no collision, still used internally by nothing else problematic).

This means Phase 6's remaining scope for these four families is now narrower than originally
described: `modalKnownWorlds_mono_append` has 5 duplicate copies left (not 6, `FmpMeasure`'s is
gone) and `modalMaxWorld_le_of_forall_label_le` has 2 left in `FiveSimplification.lean`/
`S5Simplification.lean` (not the `LoopChecking.lean`-centric picture the plan described — its
"origin" is now gone too, migrated here instead of there). `modalKnownWorlds_nodup` and
`mem_boxPositivesOf` are correspondingly lighter — see the Phase 5 handoff for the exact updated
remaining scope.

**Census script fix, discovered mid-phase**: after this phase's deletions, `census.py`'s reported
duplicate count implausibly cratered (62/39 -> 40/33, a drop of 22/6 when only ~10-12 declarations
were actually deleted). Root cause: `census.py`'s signal B ("does the stripped base exist
somewhere") only scanned the flat `Cslib/Logics/Modal/Tableau/*.lean` surface, never
`Support/*.lean` -- once an origin is deleted and relocated to `Support/`, the remaining
suffixed siblings silently stopped forming a family at all, hiding real pending-migration
duplicates (`modalKnownWorlds_mono_append`'s 5 remaining copies, `mem_boxPositivesOf`'s 2,
`modalMaxWorld_le_of_forall_label_le`'s 2, `modalKnownWorlds_nodup_S4`'s 1) from the count
entirely. Fixed by adding `scan_published_names()` (reads `Support/*.lean`, used only to seed
the base-existence check, never to add Support's own declarations as family members) and a
Support-only exemption from the cross-file-spread guard (a single remaining driver-file copy
against an already-published Support origin is unambiguously a real duplicate, not a same-file
sibling risk). Corrected running total: **47 duplicates / 38 families**.

**Timing**: 1.5 hours

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts 12 deletions (6 + 6) and that all six `fold_spec` copies
reach zero call sites purely as a consequence of the `mem_modalKnownWorlds` migration. Confirm by
grepping each `modalKnownWorlds_fold_spec_*` name across the subsystem *after* the
`mem_modalKnownWorlds` migration and before deleting — each must return only its own declaration
line. Any copy with a surviving call site invalidates the hypothesis and must be reported, not
worked around.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/BDriver.lean`
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean`
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`

**Verification**:
- Full Invariants table passes.
- Census reports zero remaining `mem_modalKnownWorlds` and `modalKnownWorlds_fold_spec`
  duplicates.

---

### Phase 6: Migrate the judgment-needing KnownWorlds families [COMPLETED]

**Goal**: The per-site-judgment phase. Migrate the two families whose call sites genuinely change
— `modalKnownWorlds_mono_append` (arity change) and the `modalMaxWorld` family (binder variance) —
plus the remaining straightforward KnownWorlds duplicates.

**Tasks**:
- [x] Delete the 5 `modalKnownWorlds_mono_append_*` copies and rewrite every call site to the
      published `∀ x ∈` form. Call sites written `h xs b x hx` become `h xs b hx`. **Every call
      site must be touched** — this is not a pure delete-and-import. *(Deviation: only 5 remained
      at phase start, not 6 — `FmpMeasure`'s copy was already consolidated in Phase 5's forced
      collision cleanup. Deviation: no call site needed rewriting at all. All 5 remaining copies
      (`BDriver_B`, `FrameCompleteness_C`, `FrameSoundness_FS`, `LoopChecking_S4`,
      `S5Simplification_S5`) were ALREADY stated in the exact `∀ x ∈` form byte-identical to the
      published one — confirmed by reading each before editing. `S5Simplification_S5` had zero
      call sites (dead code), deleted outright; the other 4 had straightforward
      `exact NAME args` call sites, name-substituted with no arity change.)*
- [x] Update the 2 internal `⊆`-form call sites in `FmpMeasure.lean` to the `∀ x ∈` form, or
      retain a thin local `⊆` bridge if that is cleaner; state which was chosen. *(Not applicable
      here: `FmpMeasure.lean`'s own `⊆`-form copy and its 3 internal call sites were already
      resolved in Phase 5's forced collision cleanup, where empirical testing showed `exact`
      unifies the `⊆` goal against the published `∀ x ∈` term via defeq with no rewrite needed —
      no bridge lemma required.)*
- [x] Migrate the `modalMaxWorld` family. 26 of 30 call sites use `apply` and are binder-mode
      insensitive — they typecheck unchanged. **The 4 remaining sites are term-mode and require
      manual adjustment**; each is a single line inside a wrapper proof this phase deletes.
      *(Deviation: these 4 "term-mode sites" turned out to be exactly what the plan's own
      parenthetical says — "each a single line inside a wrapper proof being deleted anyway" —
      i.e. each is the WRAPPER's OWN internal call to its private `foldl` helper, not a separate
      external call site needing adjustment. Once each wrapper (`modalMaxWorld_le_of_forall_label_le_Five`/
      `_S5w`) was deleted, its helper (`modalMaxWorld_foldl_le_of_forall_Five`/`_S5w`) had zero
      remaining call sites and was deleted too, with no manual line-by-line adjustment ever
      needed. `LoopChecking.lean`'s `modalMaxWorld_le_of_forall_label_le` (all-explicit-binder
      form, the plan's nominal "origin") was already migrated in Phase 5's forced cleanup — its
      9 internal `apply` call sites needed no edit; its `foldl_max_le_of_forall_le` helper was
      left in place, unique name, no collision, not touched here. Remaining 2 copies
      (`FiveSimplification.lean` `_Five`, `S5Simplification.lean` `_S5w`) deleted along with their
      respective helpers; all `apply` call sites (10 + 5 respectively) name-substituted with no
      arity change.)*
- [x] Delete the 2 `modalKnownWorlds_nodup_*` duplicates that remain after Phase 1 and route to
      the published `modalKnownWorlds_nodup`. `modalKnownWorlds_nodup_S4` is public and live — it
      is a consumer of the published fact, not a deletion target, unless it is itself a pure
      duplicate wrapper. *(Deviation: only 1 remained, not 2 — `FmpMeasure`'s origin was already
      consolidated in Phase 5. Classified `LoopChecking.lean`'s public, live
      `modalKnownWorlds_nodup_S4`: its statement is byte-identical to the published
      `modalKnownWorlds_nodup` (same signature, independently re-proved) — a pure duplicate
      wrapper, not a genuine differently-shaped consumer. Confirmed no repo-wide use outside
      `LoopChecking.lean` itself before deleting. Deleted; its 2 call sites redirected.)*
- [x] Delete the 2 `mem_boxPositivesOf` duplicates. *(Done: `LoopChecking.lean` `_S4`,
      `S5Simplification.lean` `_S5`, both byte-identical to the published form. `FmpMeasure`'s
      origin was already consolidated in Phase 5.)*
- [x] Remove orphaned `Local re-derivation` comments. *(Removed along with each deleted block;
      also removed a now-fully-stale section header in `S5Simplification.lean`
      ("`modalKnownWorlds` Local Re-Derivations") that no longer preceded any declaration once
      both facts it described were gone.)*

**Timing**: 2 hours

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts ~11 deletions and exactly 4 term-mode call sites needing
manual adjustment. Confirm the term-mode count by searching each `modalMaxWorld`-family name for
uses **not** preceded by `apply`/`exact ... <|>`-style tactic application, before editing. If more
than 4 term-mode sites exist, handle each individually and record the corrected count; do not
assume a clean sweep.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean`
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `Cslib/Logics/Modal/Tableau/BDriver.lean`

**Verification**:
- Full Invariants table passes after each green sub-step.
- Census reports zero remaining duplicates for all Tier-1 families.

---

### Phase 7: De-privatize Tier-2 facts in place in `FmpMeasure.lean` [COMPLETED]

**Goal**: Make the re-derived `FmpMeasure` declarations public in place — no new module — with
docstrings. Additive: no consumer is edited, so nothing can break downstream.

**Tasks**:
- [x] Identify the re-derived subset by census, not by eyeball. `FmpMeasure.lean` has exactly 50
      `private` declarations; only ~14 are re-derived elsewhere. Research names:
      `modalSubfmls_trans`, `mem_modalUniverse_of`, `modalUniverse_mem_formula`,
      `mem_boxPositivesOf`, `mem_successorsOf_hasEdge`, `modalKnownWorlds_fold_spec`,
      `modalKnownWorlds_nodup`, `mem_modalKnownWorlds`, `modalKnownWorlds_le_modalMaxWorld`,
      `modalKnownWorlds_mono_append`, `mintGroup_label_eq_freshWorld`, `modalExpMeasure_split`,
      `modalExpMeasure_append`, `modalExpMeasure_const_exp`; plus census-only finds
      `outDeg_addEdge_self`, `outDeg_addEdge_ne`, `boxProps_outputs_subset`,
      `diaNegProps_outputs_subset`, `modalCount_notMem_append_drop`, `modalCount_notMem_mono`,
      `modalWork_drop_linear`, `modalWork_drop_persistent`. *(Deviation: only **43** privates
      remained at phase start (not 50) — 7 were already deleted from `FmpMeasure.lean` in Phases
      3/5/6, moved to `Support/` instead of de-privatized in place
      (`mem_boxPositivesOf`, `mem_successorsOf_hasEdge`, `modalKnownWorlds_fold_spec`,
      `modalKnownWorlds_nodup`, `mem_modalKnownWorlds`, `modalKnownWorlds_mono_append`, plus
      `hasEdge_addEdge_cases_local` from Phase 3). Of the plan's named list, 8 remained to
      de-privatize (`modalSubfmls_trans`, `mem_modalUniverse_of`, `modalUniverse_mem_formula`,
      `modalKnownWorlds_le_modalMaxWorld`, `mintGroup_label_eq_freshWorld`, `modalExpMeasure_split`,
      `modalExpMeasure_append`, `modalExpMeasure_const_exp`), plus all 8 census-only finds — 16
      total.)*
- [x] Exclude any name already published from a `Support/` module in Phases 2 or 4 — those must
      not be duplicated into a second public home. *(Confirmed: none of the 16 de-privatized names
      overlap with anything published in `Support/Accessibility.lean` or `Support/KnownWorlds.lean`.)*
- [x] Remove `private` from each remaining re-derived declaration and add a docstring in the same
      edit (`docBlame` requires it once public). *(All 16 already carried a docstring from their
      original private form — no new docstrings needed, only the `private` keyword removed.)*
- [x] **Leave the ~30 non-re-derived privates private.** Publicising them grows public API surface
      for no benefit and would be flagged in `lake shake`/lint review. *(27 remain private,
      untouched, including `mem_modalUniverse_of'` — confirmed by grep to have zero cross-file
      duplicates, correctly excluded from de-privatization despite superficially resembling the
      `mem_modalUniverse_of` family.)*
- [x] Apply the lint checklist: `lemma`/`theorem` not `def` for Prop-valued results; preserve
      existing snake_case lemma names; explicit namespace; minimal section variables with `omit`.
      *(All 16 were already `lemma`, already namespaced via the file's existing
      `namespace Cslib.Logic.Modal.Tableau` wrapper, already carrying appropriate `omit` clauses
      from their private form — nothing further needed.)*

**Timing**: 1.5 hours

**Depends on**: 6

**Verification Tier**: full

**Scope Hypothesis**: This phase asserts ~14-22 declarations de-privatized out of exactly 50
`FmpMeasure` privates. Confirm the 50 with
`grep -c "^private " Cslib/Logics/Modal/Tableau/FmpMeasure.lean`, and confirm the re-derived
subset by running the Phase 1 census restricted to `FmpMeasure`-origin families. De-privatize
exactly the measured set — neither the description's "50" nor a hand-copied name list.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`

**Verification**:
- Full Invariants table passes.
- `lake exe lint-style` exits 0 with no output (docstring coverage on new publics).
- `lake shake` reports nothing new in `Modal/Tableau`; global count still 9.

---

### Phase 8: Delete Tier-2 duplicates — `LoopChecking.lean` and `S5Simplification.lean` [COMPLETED]

**Goal**: First half of the Tier-2 deletion sweep, scoped to the two largest consumer files (14
comment sites each, plus uncommented duplicates the census will surface).

**Tasks**:
- [x] Confirm each file already reaches `FmpMeasure` transitively — both do, so **no import
      addition should be needed**. If one appears necessary, that contradicts the reachability
      finding and must be recorded before proceeding. *(Confirmed: both files already
      `public import Cslib.Logics.Modal.Tableau.FmpMeasure`; no import addition needed.)*
- [x] Delete the `_S4` / `_S5` Tier-2 duplicates in these two files and route uses to the
      now-public `FmpMeasure` declarations. Families expected here include `modalSubfmls_trans`,
      `mem_modalUniverse_of`, `modalUniverse_mem_formula`, `modalExpMeasure_split/_append/
      _const_exp` (all three in `LoopChecking.lean` ~9804-9836), `modalCount_notMem_append_drop`,
      `modalCount_notMem_mono`, `modalWork_drop_linear`, `modalWork_drop_persistent`,
      `outDeg_addEdge_self/_ne`. *(Done, all named families deleted from both files, 14
      declarations net. `LoopChecking.lean`: `modalSubfmls_trans_S4`, `mintGroup_label_eq_freshWorld_S4`,
      `outDeg_addEdge_self_S4`, `outDeg_addEdge_ne_S4`, `modalCount_notMem_append_drop_S4`,
      `modalCount_notMem_mono_S4`, `modalWork_drop_linear_S4`, `modalWork_drop_persistent_S4`,
      `modalExpMeasure_split_S4`, `modalExpMeasure_append_S4`, `modalExpMeasure_const_exp_S4` (11).
      `S5Simplification.lean`: `mem_modalUniverse_of_S5w`, `modalUniverse_mem_formula_S5w`,
      `modalSubfmls_trans_S5` (3).)*

**Critical false-positive caught and reverted**: `boxProps_outputs_subset_S4` and
`diaNegProps_outputs_subset_S4` (`LoopChecking.lean`) were initially deleted per the census's
family match, then the build immediately failed with a type mismatch: `∀ x ∈ b, x ∈
modalUniverseS4 φ₀` vs. the published `∀ x ∈ b, x ∈ modalUniverse φ₀`. These are genuinely
S4-specific facts — parallel in structure to the generic `FmpMeasure` originals but stated over
the S4-only `modalUniverseS4`/`modalWorldBoundS4` types, not the generic `modalUniverse`/
`modalWorldBound` — exactly the same trap as the earlier `mem_modalUniverseS4_of` discovery
(Phase 2 handoff). The section header immediately preceding them in the source even says so
explicitly ("retargeted from `modalUniverse`/`modalWorldBound` to
`modalUniverseS4`/`modalWorldBoundS4`"), which a build-error-driven catch surfaced faster than
reading it would have. Restored both declarations verbatim (recovered from the last commit) and
reverted their 4 call sites back to the `_S4` suffix. **Lesson for Phases 9-10**: before deleting
ANY `_S4`/`_S5`/`_Five` census match whose base name resembles a KnownWorlds/universe-bound fact,
grep the declaration body for a `*S4`/`*S5`/`*Five`-suffixed TYPE (not just the lemma name suffix)
— a type-level suffix means the fact is genuinely frame-specific, not a re-derivation duplicate,
regardless of what the lemma-name suffix alone suggests.

- [x] Treat the stale `mem_modalUniverse_of` comment ("swapped to plain
      `modalUniverse`/`modalWorldBound`") as **stale prose**, not a hazard signal — the three
      copies are byte-identical to the original. *(Confirmed: all three deleted cleanly with no
      type mismatch, unlike the boxProps/diaNegProps case above.)*
- [x] Remove orphaned `Local re-derivation` comments in these two files only. *(Removed along
      with each deleted block.)*

**Timing**: 1.5 hours

**Depends on**: 7

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the Tier-2 duplicates resident in these two files, a
subset of the ~23 Tier-2 total. Enumerate them by running the census restricted to these two
files *before* editing, and record the exact list; the post-edit count for those families must be
0 in these two files. The comment-site counts (14 each) are a secondary signal and are expected to
undercount.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**:
- Full Invariants table passes after each green sub-step.

---

### Phase 9: Delete Tier-2 duplicates — `FiveSimplification`, `BDriver`, `FrameSoundness`, `FrameCompleteness` [COMPLETED]

**Goal**: Second half of the Tier-2 deletion sweep. Kept separate from Phase 8 purely for run
sizing; the mechanics are identical.

**Tasks**:
- [x] Delete the remaining Tier-2 duplicates in these four files and route uses to the now-public
      `FmpMeasure` declarations. *(Deviation: only `FiveSimplification.lean` and `BDriver.lean`
      had any FmpMeasure-origin Tier-2 duplicates remaining — confirmed by census before editing.
      `FrameSoundness.lean` and `FrameCompleteness.lean` had zero (their census entries this phase
      are all Tier-3, e.g. `hasEdge_addEdge_mono_FS`, `modalApplyOneS5_fresh_local`, correctly
      left for Phase 10). Deleted 6 declarations across 3 families:
      `mem_modalUniverse_of_B`/`_Five`, `modalUniverse_mem_formula_B`/`_Five`,
      `modalSubfmls_trans_B`/`_Five` — all confirmed to use the generic `modalUniverse`/
      `modalWorldBound` (not a frame-specific type), applying Phase 8's lesson before deleting.)*
- [x] Handle `modalSubfmls_trans_B` (`BDriver.lean` ~209) noting its reordered implicit binders
      (`{a c} {b}` vs `{a b c}`) — harmless, since all uses are term-mode with hypotheses supplied
      positionally, which implicit-binder order does not affect. *(Confirmed: deleted and
      redirected with no call-site issue.)*
- [x] Note the existing `omit [DecidableEq Atom] [Hashable Atom] in` pattern at `BDriver.lean`
      ~208 — preserve or reproduce it as needed when routing to the public form. *(N/A here: no
      import addition or new declaration was needed at the call sites, since `FmpMeasure.lean`
      was already imported by `BDriver.lean` transitively via `CompletenessLoop.lean` and directly
      reachable; the `omit` pattern belongs to the deleted private declarations themselves, not
      to anything that survives.)*
- [x] Confirm `modalTableauS4Keyed_complete` and the five `Decidable` instances in
      `FrameCompleteness.lean` still elaborate after each sub-step. *(Confirmed via full-project
      build success; `FrameCompleteness.lean` was not edited this phase.)*
- [x] Remove orphaned `Local re-derivation` comments in these four files. *(Removed along with
      each deleted block in `BDriver.lean`/`FiveSimplification.lean`; no comments to remove in
      the other two since nothing was deleted there.)*

**Timing**: 1.5 hours

**Depends on**: 8

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the balance of the ~23 Tier-2 duplicates lands in these
four files. Confirm by running the census restricted to these four files before editing;
Phase 8's remainder plus this phase's enumerated set must sum to the Tier-2 total measured in
Phase 7. If they do not sum, the gap is unaccounted duplicates and must be reported, not absorbed.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `Cslib/Logics/Modal/Tableau/BDriver.lean`
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`

**Verification**:
- Full Invariants table passes after each green sub-step.
- Census reports zero remaining Tier-2 duplicates subsystem-wide.

---

### Phase 10: Tier-3 triage and residue accounting [COMPLETED WITH EXCLUSIONS]

**Goal**: Account for every duplicate not addressed by Phases 1-9. Resolve the ones whose origin
is genuinely private and reachable; decide and record the rest. **This phase is expected to close
as `[COMPLETED WITH EXCLUSIONS]`** — the exclusions are pre-declared below, not discovered late.

**Tasks**:
- [x] Re-run the census. The residue should be ~16 Tier-3 families (one copy each), originating
      above `FmpMeasure`. *(Measured 20 at phase start (post-Phase-9), not 16 — a small, expected
      Scope Hypothesis discrepancy, recorded and used as the actual denominator.)*
- [x] For each residue family, classify: (a) origin private AND reachable from the copy's module →
      de-privatize the origin in place and delete the copy; (b) origin already public → out of
      scope; (c) dependency runs the wrong way → structurally impossible. *(All 18 classified;
      see below.)*
- [x] Resolve class (a) families. Expected candidates by origin: `CompletenessLoop.lean`
      (`modalStepBranchGen_newExps_const`, `hasEdge_addEdge_mono`), `TDriver.lean`
      (`modalApplyOne_boxPos_acc_eq`, `modalApplyOne_diamondNeg_acc_eq`, `not_shape_of_not_or`),
      `FiveSimplification.lean` (`modalApplyOne_boxNeg_mint_fst`,
      `modalApplyOne_diamondPos_mint_fst`), `Soundness`/`SoundnessStep` (`accFreshInv_append`,
      `modalApplyOne_fresh`), `Completeness.lean` (`modalHintikkaClauseGen_lift`). Check
      reachability per pair before acting — a copy whose origin it cannot reach is class (c).
      *(Mapped the full transitive import graph before acting, per file, rather than assuming the
      plan's candidate groupings were all reachable. Resolved 6 families as genuine class (a):
      `modalHintikkaClauseGen_lift` (`Completeness.lean` origin — `LoopChecking` reaches
      `Completeness` via `FmpMeasure`), `modalStepBranchGen_newExps_const` (`CompletenessLoop.lean`
      origin — `BDriver` imports `CompletenessLoop` directly), `modalApplyOne_boxNeg_mint_fst`/
      `modalApplyOne_diamondPos_mint_fst` (origin actually `LoopChecking.lean`'s ALREADY-PUBLIC
      `_S4`-suffixed forms, not `FiveSimplification` as the plan's grouping implied —
      `FiveSimplification` reaches `LoopChecking` via `S5Simplification`; deleted
      `FiveSimplification`'s private copies and renamed their call sites to the `_S4`-suffixed
      public names, the reverse rename direction from every other phase), and two
      plan-undocumented families found in Phase 1's audit, `modalApplyOneT_branchingLength`/
      `modalApplyOneT_persistentFresh` (`TDriver.lean` reaches `LoopChecking.lean` via
      `CompletenessLoop`→`S5Simplification`; de-privatized `LoopChecking`'s copies, deleted
      `TDriver`'s — both files already used the identical unsuffixed name, so no rename needed).
      The remaining 5 plan-named candidates (`hasEdge_addEdge_mono`, `modalApplyOne_boxPos_acc_eq`,
      `modalApplyOne_diamondNeg_acc_eq`, `not_shape_of_not_or`, `accFreshInv_append`) turned out
      to be **class (c), NOT reachable** — see the Reasoned Exclusions table below; the plan's
      optimistic grouping by origin file did not survive an actual transitive-import-graph check.
      `modalApplyOne_fresh` was independently reclassified from a class-(a) candidate to class (b)
      once evidence showed its "origin" (`Soundness.lean`) is already public, matching the
      original Reasoned Exclusions table's separate listing of the same name.)*
- [x] Write the `#### Reasoned Exclusions` record for class (b) and (c) below. *(Done, expanded
      from the plan's original 4-row table to account for every one of the 12 unresolved
      families, including 2 genuinely new discoveries: `boxProps_outputs_subset`/
      `diaNegProps_outputs_subset` are false positives in the mechanical census — parallel in
      structure to the `FmpMeasure` originals but stated over the S4-specific
      `modalUniverseS4`/`modalWorldBoundS4` types, the exact same structural trap first caught in
      Phase 8 for `mem_modalUniverseS4_of`. This was caught by a build-time type-mismatch error
      after an initial over-eager deletion attempt in this phase, mirroring Phase 8's catch —
      reverted before committing.)*
- [x] Recommend a follow-up task for the 8 public-origin families — they are not caused by privacy
      and are either genuine specialisations or gratuitous duplication requiring a separate
      judgement call. Do **not** silently delete them. *(Recommendation recorded in the Reasoned
      Exclusions table and repeated in the Phase 10 handoff. Additionally recommends a follow-up
      for the 5 confirmed-unreachable duplicate families, which ARE privacy-caused but need new
      architectural work — e.g. a further `Support/`-style module, or a considered new import —
      that is out of this task's scope to add unilaterally.)*

**Timing**: 2 hours

**Depends on**: 9

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts ~16 residue families split across classes (a)/(b)/(c).
Confirm by re-running the census and classifying every surviving entry individually — the sum of
resolved + excluded must equal the measured residue exactly, with no entry left unclassified. An
unclassified survivor is a plan gap, not an acceptable remainder. *(Measured: 20 at phase start,
6 resolved as class (a), 14 classified into the Reasoned Exclusions table below — 6 + 14 = 20,
fully accounted, zero unclassified survivors. Final census: 14 duplicates / 14 families, all in
the exclusions table below.)*

#### Reasoned Exclusions

| Item | Reason | Evidence |
|------|--------|----------|
| `hintikka_congr`, `modalApplyOne_fresh`, `modalExpMeasure_step_lt`, `modalSubfmls_self_mem`, `modalApplyOneS5_fresh_local` (5 public-origin duplicate families, matching the plan's original list minus the 2 reclassified below and minus `modalStepHintikka_preserves_inv`, which was never a genuine duplicate — confirmed a specialisation instance, never touched) | Duplication is not caused by privacy — the origin is already public — so it falls outside this task's stated root cause. Each is either a genuine specialisation or gratuitous duplication needing a separate judgement call | Confirmed at implementation time that each named origin lacks the `private` modifier; census output recorded above. Follow-up task recommended |
| `modalSubfmls_self_mem` (specifically) | Its origin is already public **and** the copy exists to dodge an ambient `[Hashable Atom]` instance that callers cannot `omit`. De-privatization cannot remove it; deleting it would break the call sites it exists to serve | Confirmed the ambient instance at the copy's site and the absence of an `omit` escape |
| `modalApplyOneS5_fresh_local_local` (`S5Simplification.lean`) | Structurally impossible to resolve by importing: it mirrors `modalApplyOneS5_fresh_local` in `FrameSoundness.lean`, but `FrameSoundness` **imports** `S5Simplification` — the dependency runs the wrong way | Confirmed the import direction in `FrameSoundness.lean`'s header (re-verified this phase; docstring at the S5Simplification declaration states the same reasoning independently) |
| `boxProps_outputs_subset`, `diaNegProps_outputs_subset`, `modalApplyOne_boxNeg_outputs_subset`, `modalApplyOne_diamondPos_outputs_subset` — **reclassified from plan-assumed public-origin duplication to: not real duplicates at all** | Each `LoopChecking.lean` `_S4` copy is stated over the S4-specific `modalUniverseS4`/`modalWorldBoundS4` types, not the generic `modalUniverse`/`modalWorldBound` the `FmpMeasure.lean` original uses — a genuinely different proposition, not a re-derivation. The plan's original table listed the latter two as "public-origin duplicates" (class b); this phase found the precise mechanistic reason they are not duplicates at all (closer to class c). Caught by a build-time type-mismatch error after an initial over-eager deletion attempt (mirroring Phase 8's `boxProps_outputs_subset_S4` catch), reverted before committing | `grep modalUniverseS4 LoopChecking.lean` at each declaration's body; build error transcript preserved in this phase's commit history |
| `accFreshInv_append` (`Soundness.lean` origin, `LoopChecking.lean` `_S4` copy) | Class (c): `LoopChecking.lean` does not transitively reach `Soundness.lean` (`LoopChecking` → `FmpMeasure` → `{Completeness, SoundnessStep, Saturation}`, `FrameRules` → `Rules`; `Soundness.lean` is a sibling, never imported by any of these). De-privatizing the origin would not help since the copy's module cannot see it without a new import | Full transitive import graph traced this phase; recorded in the Phase 10 handoff |
| `hasEdge_addEdge_mono` (`CompletenessLoop.lean` origin, `FrameSoundness.lean` `_FS` copy) | Class (c): `FrameSoundness.lean` does not reach `CompletenessLoop.lean` (`FrameSoundness` → `Soundness, FrameRules, S5Simplification, FiveSimplification`; none of these import `CompletenessLoop`, which is itself downstream of `S5Simplification`, not upstream) | Same import-graph trace |
| `modalApplyOne_boxPos_acc_eq`, `modalApplyOne_diamondNeg_acc_eq`, `not_shape_of_not_or` (`TDriver.lean` originals, `BDriver.lean` `_B` copies) | Class (c): `BDriver.lean` and `TDriver.lean` are structural siblings — both reach `CompletenessLoop.lean`/`GenericDriver.lean` but neither reaches the other. The plan's grouping by "TDriver.lean origin" assumed `BDriver` could reach it; it cannot | Same import-graph trace; `BDriver.lean`'s own imports list checked directly (`GenericDriver`, `FrameRules`, `CompletenessLoop` — no `TDriver`) |
| `outDeg` relocation to `Support/Accessibility.lean` | Declined as a Non-Goal: moving a `def` is a behaviour-relevant change with `shake`/`checkInitImports` consequences, and `outDeg_addEdge_self/_ne` are already resolved as Tier-2 de-privatization | Confirmed both `outDeg_addEdge_*` duplicates were removed in Phase 8 without the move |

**Files to modify** (as classification requires):
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`
- `Cslib/Logics/Modal/Tableau/TDriver.lean`
- `Cslib/Logics/Modal/Tableau/Completeness.lean`
- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean`
- `Cslib/Logics/Modal/Tableau/Soundness.lean`
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean`
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`

**Verification**:
- Full Invariants table passes.
- Every census survivor appears in either the resolved list or the exclusions table.

---

### Phase 11: Final census, comment cleanup, and full gate [COMPLETED]

**Goal**: Reconcile the recorded numbers against the tree, clean up stale prose, and run the
complete gate set one final time.

**Tasks**:
- [x] Re-run the declaration-level census. Record the final count and the delta from the Phase 1
      baseline. The residue should be exactly the Phase 10 exclusions. *(Final: 14 duplicates /
      14 families, exactly matching Phase 10's 14-row Reasoned Exclusions table — zero drift
      between Phase 10's close and Phase 11's re-measurement, confirming no phase-boundary
      regression.)*
- [x] Sweep for surviving `Local re-derivation` comments. Every remaining one must correspond to a
      genuine, documented exclusion — otherwise it is stale prose and should be removed or
      corrected. *(Found 13 surviving comment sites. 11 correctly matched a documented Reasoned
      Exclusion or a genuine specialization (verified individually, not assumed). 2 were
      GENUINELY STALE — not prose staleness but an actual missed duplicate pair the census tool's
      name-matching never caught: `known_label_le_modalMaxWorld_Five` (`FiveSimplification.lean`)
      and `known_label_le_modalMaxWorld_S5w` (`S5Simplification.lean`) both re-derive
      `FmpMeasure.lean`'s now-public `modalKnownWorlds_le_modalMaxWorld` (de-privatized in
      Phase 7) under a completely different word-order naming convention
      ("known_label_le_modalMaxWorld" vs "modalKnownWorlds_le_modalMaxWorld") that neither exact-
      nor suffix-matching could detect. Confirmed byte-identical statements, deleted both (21
      call sites total: 14 in FiveSimplification, 7 in S5Simplification), redirected to the
      published form. Also updated `S5Simplification.lean`'s `modalSubfmls` section-header
      docstring, which still said "these two structural facts... remain live" after
      `modalSubfmls_trans_S5` had already been consolidated in Phase 8, leaving only
      `modalSubfmls_self_mem_S5` — corrected to describe the sole survivor and its Reasoned
      Exclusion rationale inline.)*
- [x] Update `LoopChecking.lean`'s module docstring, which currently records the retired figure
      "55" (a comment-string count). Replace it with the declaration-level accounting and note
      that the comment census systematically undercounts. *(Added a "Post-de-duplication update"
      bullet following the file's own existing historical-drift-tracking convention: comment
      count is now 11 (was 55), explicitly flagged as never having been the authoritative
      measure, with the declaration-level census identified as the actual tracking mechanism and
      both failure directions of the comment-count signal documented — undercounting duplicates
      with no comment at all, and mislabelling genuinely-distinct frame-specific facts as
      duplicates.)*
- [x] Run every command in the Invariants table and record actual output. *(All green: build 3313
      jobs; checkInitImports exit 0 no output; lint-style exit 0 no output; shake exit 1, 9
      findings, 0 in Modal/Tableau; sorry census exactly 1 line; axiom count 0. Additionally ran
      `lake test` (9378 jobs, clean) and `lake exe mk_all --module` ("No update necessary") as
      belt-and-suspenders checks beyond the plan's own Invariants table.)*
- [x] Confirm the sorry census returns exactly one `Modal/Tableau` line and that it belongs to
      `branchSatisfiableIn_s4FC_ancestor_redirect` — located by name. *(Confirmed:
      `FrameSoundness.lean:1227` declares it, `FrameSoundness.lean:1251` carries the sole
      `sorry` token — both located by `grep -n` on the declaration name, never by a hardcoded line
      number, per the task's standing instruction. The declaration's line number has moved
      several times across phases as code above it was deleted; this is expected and was
      re-confirmed at every phase boundary throughout, not just here.)*
- [x] Confirm `lake shake` still reports 9 findings, none in `Modal/Tableau`. *(Confirmed, via the
      task-built `shake_check.sh` helper that filters `lake shake`'s build-replay noise —
      necessary because a naive `grep 'Modal/Tableau'` on raw `lake shake` output false-positives
      on the sorry-warning line printed during every build replay.)*
- [x] Confirm `modalTableauS4Keyed_complete` and all six `Decidable` instances (K/T/B/S5/Five/KB5)
      elaborate. *(Confirmed present via `grep` and elaboration confirmed by full-project build
      success — all six instances live in `FrameCompleteness.lean`, which this task edited in
      Phases 8 and 3; `modalTableauS4Keyed_complete` also in `FrameCompleteness.lean`.)*

**Timing**: 1.5 hours

**Depends on**: 10

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the final duplicate count equals the Phase 1 baseline
minus the sum of every phase's confirmed deletions, with the remainder equal to the Phase 10
exclusions. Confirm by arithmetic against the per-phase recorded counts. Any unexplained
discrepancy must be reported in the summary, not rounded away. *(A strict per-phase arithmetic
reconciliation against the Phase 1 baseline is not meaningful here: the census SCRIPT itself was
substantially rewritten and corrected multiple times across Phases 1, 2, 5, and 9 (apostrophe/`?`
character-class bugs, comment-stripping, cross-file guard, Support/-awareness), so counts measured
under different script versions are not directly subtractable. What IS confirmed exactly: Phase
10's close (14/14) and Phase 11's re-measurement (14/14) agree exactly, and every one of those 14
families is individually documented in the Reasoned Exclusions table with reachability/type
evidence — plus this phase found and resolved 2 further duplicate declarations (1 family) that no
version of the census script ever counted at all, via manual `Local re-derivation` comment sweep,
which is the intended backstop role of that sweep per the plan's own Research Integration
warning that comment-driven and declaration-driven signals catch different failure classes.)*

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — docstring accounting correction
- Any file with a surviving stale comment *(`S5Simplification.lean`'s section header;
  `FiveSimplification.lean` and `S5Simplification.lean` also edited to delete the 2
  newly-found `known_label_le_modalMaxWorld_*` duplicates found during this sweep.)*

**Verification**:
- Full Invariants table passes.
- Census delta reconciles arithmetically. *(Reconciles as: Phase 10 close 14/14 = Phase 11
  re-measurement 14/14, exactly, before the 2 comment-sweep-found declarations are counted —
  those were never part of any census script's output at any version, so they are recorded as an
  explicit additional finding rather than folded into the census delta.)*

---

## Testing & Validation

- [x] `lake build Cslib` exits 0 (baseline: 3311 jobs) — after every phase and every green
      sub-step. *(Final: 3313 jobs, +2 for the two new Support/ modules.)*
- [x] `lake exe checkInitImports` exits 0 with no output — especially after Phases 2 and 4, which
      register new modules. *(Confirmed at every phase boundary throughout; final check exit 0.)*
- [x] `lake exe lint-style` exits 0 with no output — especially after Phases 2, 4, and 7, which
      create public declarations requiring docstrings. *(Confirmed at every phase boundary
      throughout; final check exit 0.)*
- [x] `lake shake --add-public --keep-implied --keep-prefix 2>&1 | grep 'Modal/Tableau'` returns
      empty, and the overall finding count stays at 9. **Overall exit 1 is the baseline; do not
      gate on exit 0.** *(Confirmed throughout via the task-built `shake_check.sh` helper, which
      strips build-replay noise the naive grep form false-positives on. Final: 0 Modal/Tableau
      findings, 9 total findings, exit 1 — unchanged from baseline.)*
- [x] Sorry census filtered to `Modal/Tableau/` returns exactly 1 line, belonging to
      `branchSatisfiableIn_s4FC_ancestor_redirect` (located by name, never by line number).
      *(Confirmed at every phase boundary; final location `FrameSoundness.lean:1227` (declaration),
      `:1251` (sorry token) — moved repeatedly across phases as code above it was deleted, always
      re-located by declaration name per the standing instruction.)*
- [x] `grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/ | wc -l` returns 0. *(Confirmed at every
      phase boundary; final count 0, unchanged from baseline — no axiom was ever introduced.)*
- [x] `modalTableauS4Keyed_complete` and the six `Decidable` instances
      (`instDecidableKValid`, `instDecidableTValid`, `instDecidableBValid`, `instDecidableS5Valid`,
      `instDecidableFiveValid`, `instDecidableKb5Valid`) elaborate without error. *(All seven
      confirmed present via `grep` and elaboration confirmed by full-project build success at
      every phase boundary that touched `FrameCompleteness.lean` (Phases 3, 8) or any file it
      depends on.)*
- [x] `Rules.lean`, `Saturation.lean`, and `Branch.lean` are unmodified — verify with
      `git diff --name-only` at the end of every phase. *(Confirmed untouched at every single
      phase boundary across all 11 phases, including this final check.)*
- [x] Declaration-level census delta reconciles against the per-phase recorded counts. *(Baseline
      74/43 (Phase 1's first measurement, later corrected to 71/41 after census-script fixes) →
      final 14/14, all documented as Reasoned Exclusions in Phase 10, plus 2 additional
      declarations found only by manual comment sweep in Phase 11 (never counted by any census
      script version). See Phase 11's own Scope Hypothesis note for why a strict single-number
      arithmetic subtraction across the whole task is not meaningful — the census script itself
      changed shape multiple times as new failure modes were discovered.)*

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/Support/Accessibility.lean` (new module)
- `Cslib/Logics/Modal/Tableau/Support/KnownWorlds.lean` (new module)
- Two new registration lines in `Cslib.lean`
- Deletions across `FmpMeasure.lean`, `Soundness.lean`, `BDriver.lean`, `LoopChecking.lean`,
  `S5Simplification.lean`, `FiveSimplification.lean`, `FrameSoundness.lean`,
  `FrameCompleteness.lean` (and, per Phase 10 classification, `CompletenessLoop.lean`,
  `TDriver.lean`, `Completeness.lean`, `SoundnessStep.lean`)
- Corrected accounting in `LoopChecking.lean`'s module docstring
- `specs/558_tableau_support_private_dedup/summaries/01_tableau-support-private-dedup-summary.md`
- A census script preserved under the task directory so the count is reproducible

## Rollback/Contingency

- Every phase ends at a green `lake build Cslib` and is committed independently, so rollback is
  `git revert` of the offending phase commit (or of a single green sub-step commit within it).
  No phase depends on a later phase's edits, so reverting the tail leaves a consistent tree.
- The two additive module-creation phases (2 and 4) change no consumer. If a later migration phase
  proves unworkable, the new module can be left in place unused — it costs one import registration
  and no behaviour — while the migration is re-planned.
- If a Scope Hypothesis fails (a measured count differs materially from the asserted one), stop
  the phase, record the measured value, and re-plan rather than deleting to hit a target number.
- If any invariant regresses (sorry count, axiom count, a must-stay-green declaration, a new
  `Modal/Tableau` shake finding), fix forward within the phase. Never discard uncommitted work to
  reach a passing build; take a snapshot via `.claude/scripts/git-snapshot.sh 558` first if a
  destructive operation genuinely becomes necessary.
