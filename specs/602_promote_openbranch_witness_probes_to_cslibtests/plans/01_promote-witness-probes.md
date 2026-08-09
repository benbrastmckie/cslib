# Implementation Plan: Promote openBranch_countermodel Witness Probes to CslibTests

- **Task**: 602 - Promote the openBranch_countermodel witness probes into CslibTests for CI protection
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: specs/602_promote_openbranch_witness_probes_to_cslibtests/reports/01_promote-witness-probes.md
- **Artifacts**: plans/01_promote-witness-probes.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Three CI-protected `CslibTests/` files are produced from the four scratch witness probes at
`specs/591_decide_openbranch_countermodel_disposition/scratch/`, converting every bare `#eval!`
into the `/-- info: ... -/ #guard_msgs in #eval ...` idiom used by
`CslibTests/BetaSplitRefutation.lean` and `CslibTests/S4LoopGuardRegression.lean`, so a silent
change to `intuitionisticTableau` / `minimalTableau` / the admissible-edge characterisation
becomes a `lake test` build error rather than an unnoticed drift. `WitnessSearch2.lean`'s
exhaustive powerset enumeration is deliberately NOT ported as a live computation (research
measured: no output after 9m10s, not even for the first formula); its CI-relevant content is
folded into the promoted `WitnessProbe.lean` as specific-witness assertions plus a prose record
of the full-search claim. Definition of done: three new files under `CslibTests/`, registered in
the `CslibTests.lean` barrel via `lake exe mk_all --module`, with the full CSLib CI order green
and zero new sorries or axioms.

### Research Integration

Findings from `reports/01_promote-witness-probes.md` that drive this plan:

- `WitnessProbe.lean` (~6.5s) and `WitnessSearch3.lean` (~2.7s) are fast and promotable
  essentially as-is; `MinProbe.lean` (~2.5s compute) is fast but has a genuine parse error.
- `MinProbe.lean`'s parse error (`unexpected token '#eval!'; expected 'lemma'` at its line 59)
  is caused by two `/-- ... -/` declaration docstrings sitting directly above bare `#eval!`
  commands. Converting those calls to the `#guard_msgs` idiom fixes the error as a side effect,
  because there the docstring is consumed by the `#guard_msgs` elaborator rather than attached
  to a declaration.
- `WitnessSearch2.lean` must not be ported as a live enumeration. Its `subsets inclPairs`
  powerset materialisation is the blowup; the `inclPairs` computation itself (an O(n²) filter)
  is cheap and is what Phase 4 tests as a bounded, optional addition.
- Promotion pattern: copyright header, `module` + paired `import` / `public meta import`,
  `/-! # ... -/` module docstring including an explicit "promoted from
  `specs/591_.../scratch/<Name>.lean`" provenance pointer, `set_option autoImplicit false`,
  `#guard_msgs`-wrapped plain `#eval` (not `#eval!`).
- Registration: `lakefile.toml` sets `testDriver = "CslibTests"`, so `lake test` builds the
  `CslibTests` lean_lib; new files reach it only via the `CslibTests.lean` barrel, which CI
  checks with `lake exe mk_all --check`.
- The report captured current output for all three promotable probes. Those captures are
  **reference values subject to re-verification**, not ground truth to transcribe blindly.

**One correction to the research report, applied in this plan**: the report states
`MinProbe.lean` also imports `Minimal.Soundness`. Reading the file, it does not — it uses
`minimalTableau` with only the three shared imports. `WitnessSearch3.lean` is the file carrying
the extra `Cslib.Logics.Propositional.Tableau.Minimal.Soundness` import, which therefore looks
unnecessary (MinProbe resolves `minimalTableau` without it). Phase 2 tests and resolves that
rather than copying it forward unexamined.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` was not supplied as a `roadmap_path` in the delegation context and no roadmap
phases are added to this plan. Consulted read-only for alignment: the roadmap's S4 keyed
loop-check guard entry already cites `CslibTests/AncestorRedirectRefutation.lean` as the
established "regression witness" idiom for a machine-checked refutation. This task extends the
same idiom to the intuitionistic/minimal `openBranch_countermodel` evidence. No roadmap item is
completed or annotated by this task.

## Goals & Non-Goals

**Goals**:
- Three new `CslibTests/` files whose every assertion is `#guard_msgs`-protected, so a
  regression is a build failure rather than a changed printed value.
- `MinProbe.lean`'s parse error fixed as part of promotion (not worked around).
- Provenance preserved: each promoted file's module docstring names the scratch file it came
  from and states what claim it certifies.
- `WitnessSearch2.lean`'s CI-relevant content preserved as fast assertions plus honest prose;
  its slow enumeration documented, not executed.
- Full CSLib CI order green, zero new sorries, zero new axioms.

**Non-Goals**:
- Editing anything outside `CslibTests/` (and the repo-root `CslibTests.lean` barrel, which is
  the registration mechanism this task's scope necessarily implies). In particular, the two
  stale "not CI-protected" citations at `Scheme.lean:7868` and `:7882` are **flagged as a
  follow-up, not edited** — see Phase 5.
- Porting `WitnessSearch2.lean`'s `subsets` / `searchWitness` full enumeration into CI.
- Re-verifying or re-deriving the underlying mathematical claims. This task promotes existing
  machine-checked evidence; it does not re-litigate it.
- Renaming the probes. Base names are kept (`WitnessProbe`, `WitnessSearch3`, `MinProbe`) to
  minimise the diff at the later citation-update follow-up.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A probe's output has drifted since the scratch capture (changes to `intuitionisticTableau` / `minimalTableau`) | H | M | Pre-declare the **semantic** content of each assertion from the report before running; a semantic difference is a finding to report and escalate, never to silently adopt. See the reconciliation protocol below. |
| `#guard_msgs` expected-string differs from the report's captured text purely in formatting (parenthesisation, spacing, line wrapping) | L | H | Formatting is transcription, not a claim: take the exact string from the `#guard_msgs` mismatch diff. This is explicitly distinct from a semantic difference. |
| `WitnessSearch3.lean`'s `Minimal.Soundness` import is unnecessary and `lake shake` flags it | L | M | Phase 2 tests removal directly (build without it); if the build fails, the import is genuinely needed and is kept with a one-line comment saying why. |
| Added `lake test` runtime (~12s total across three files) pushes CI budget | L | L | Measure each file's build time at its phase; if any single file exceeds ~60s, report it before proceeding rather than trimming assertions. |
| Phase 4's optional `inclPairs` assertion turns out expensive | L | M | Phase 4 carries a Scope Hypothesis: measure first; if over budget, drop to prose-only and record the measurement. Dropping it removes nothing required by the task. |
| Scope creep into `Cslib/` while chasing the stale citations | M | M | `file_scope` is `["CslibTests/"]`. Phase 5 records the follow-up in the summary only; no `Cslib/` edit is made under this task. |
| `lake exe checkInitImports` demands `import Cslib.Init` in the new files | L | L | Mirror `BetaSplitRefutation.lean`'s import block exactly (it has no `Cslib.Init` import and passes CI); if `checkInitImports` disagrees, follow what it demands. |

### Reconciliation protocol (applies to every `#guard_msgs` assertion in Phases 1-4)

This is the operational form of the task's "do NOT weaken an assertion to make it pass"
constraint. Before running any newly written assertion:

1. Write down the **semantic claim** the assertion encodes, taken from the research report —
   e.g. for `WitnessProbe`'s `check [(1,0)]`: *"upward-closed AND does not force `phiRef1`,
   i.e. the pair is `(true, false)` — this is the witness"*.
2. Build and read the actual output.
3. If the actual output carries the same semantic content and differs only in rendering,
   transcribe the actual string into the `/-- info: ... -/` block. This is a transcription fix.
4. If the actual output carries **different semantic content** (a `true` became `false`, a
   witness stopped witnessing, a verdict flipped `OPEN`/`CLOSED`, a world/atom table changed
   shape): **stop**. Record it as a finding with the before/after values, mark the phase
   `[BLOCKED]`, and report it. Do not edit the expected value to match, and do not delete or
   soften the assertion.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 1, 2 |
| 4 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Promote WitnessProbe.lean (intuitionistic witness for phiRef1) [COMPLETED]

**Goal**: Create `CslibTests/WitnessProbe.lean` — a compiling, `#guard_msgs`-asserted promotion
of the scratch `WitnessProbe.lean` — and settle the promotion template the next two phases reuse.

**Tasks**:
- [ ] Create `CslibTests/WitnessProbe.lean` with: the Apache copyright header copied from
      `CslibTests/BetaSplitRefutation.lean`, `module`, and the three paired
      `import` / `public meta import` lines the scratch file already has
      (`...Tableau.Intuitionistic.Scheme`, `...Propositional.Defs`,
      `...Foundations.Logic.Tableau.Branch`).
- [ ] Write the `/-! # ... -/` module docstring: what is asserted (that the edge set `[(1,0)]`
      satisfies both conjuncts of `openBranch_countermodel`'s existential for `phiRef1` —
      `upwardClosed = true` and `¬forces phiRef1 at 0` — while the empty, raw-tree and augmented
      frames do not), why it matters (this evidence is what retracted the former
      PERMANENTLY DEFERRED annotations, and the in-source annotations cite it), and the
      provenance pointer: promoted from
      `specs/591_decide_openbranch_countermodel_disposition/scratch/WitnessProbe.lean`.
- [ ] Add `set_option autoImplicit false` and open `Cslib.Logic.PL` / `Cslib.Logic.Tableau`,
      matching the scratch file.
- [ ] Use `namespace CslibTests.WitnessProbe` (NOT the scratch file's bare `namespace
      WitnessProbe`) — `CslibTests/` files namespace under `CslibTests.` per
      `BetaSplitRefutation.lean`, and the `topNamespace`/`dupNamespace` linters check this.
- [ ] Port the definitions verbatim: `pb`, `pr`, `ps`, `phiRef1`, `realBranch`, `branchLabels`,
      `branchAtoms`, `forcesAtom`, `worldUniverse`, `stepFrom`, `succsAux`, `succs`, `evalF`,
      `upwardClosed`, `check`, `atomTable`. Add a docstring to each currently-undocumented `def`
      (the scratch file documents only some; `lake lint`'s `docBlame` will demand the rest).
- [ ] Pre-declare the semantic claim of each of the 7 assertions per the reconciliation protocol,
      then convert each bare `#eval!` to `/-- info: ... -/` + `#guard_msgs in` + plain `#eval`
      (drop the `!`), in the scratch file's order: `atomTable`, `check []`,
      `check [(1,0),(2,1)]`, `check [(1,0)]`, `check [(1,0),(2,1),(1,2),(2,2)]`, and the two
      `succs` sanity checks.
- [ ] Build the module and reconcile expected vs. actual output per the protocol.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts (a) exactly 7 `#guard_msgs` assertions, derived from the
7 `#eval!` calls in the scratch file, and (b) that the reference values in the research report's
"Captured current output" block for `WitnessProbe.lean` still hold. Confirm (a) by counting
`#eval!` occurrences in
`specs/591_decide_openbranch_countermodel_disposition/scratch/WitnessProbe.lean` at
implementation time; confirm (b) by the build-and-reconcile step, treating any semantic
difference as a finding per the reconciliation protocol.

**Files to modify**:
- `CslibTests/WitnessProbe.lean` - new file; the intuitionistic `[(1,0)]` witness, CI-protected.

**Verification**:
- `lake build CslibTests.WitnessProbe` succeeds with no `#guard_msgs` mismatch and no warnings.
- Every assertion's semantic content matches the pre-declared claim (or is escalated as a
  finding).
- File contains no `sorry`, no `axiom`, no bare `#eval!`.
- Note the module's build wall-time for the Phase 5 CI-budget check.

---

### Phase 2: Promote WitnessSearch3.lean (maximal-frame sweep) [COMPLETED]

**Goal**: Create `CslibTests/WitnessSearch3.lean`, CI-protecting the claim that the maximal
admissible inclusion frame is NOT a uniform witness — it fails at exactly the
`phiRef1`/`phiRef3` family and succeeds elsewhere.

**Tasks**:
- [ ] Create `CslibTests/WitnessSearch3.lean` using the template settled in Phase 1
      (header, `module`, paired imports, docstring, `set_option autoImplicit false`,
      `set_option maxRecDepth 100000` — the scratch file sets it, so preserve it —
      `namespace CslibTests.WitnessSearch3`).
- [ ] Resolve the `Cslib.Logics.Propositional.Tableau.Minimal.Soundness` import question: build
      once WITHOUT it (the scratch `MinProbe.lean` resolves `minimalTableau` without it, so it
      is likely dead). If the build succeeds, omit it. If it fails, keep the paired import and
      add a one-line comment naming what it supplies. Record which outcome held.
- [ ] Module docstring: what is asserted (per formula, whether the maximal inclusion frame `⊑`
      itself witnesses the existential, reported with and without a fresh atom-free world), why
      it matters (this is what backs the "maximal inclusion frame is NOT a uniform witness"
      claim, failing at exactly `phiRef1`/`phiRef3`), and the provenance pointer to
      `specs/591_decide_openbranch_countermodel_disposition/scratch/WitnessSearch3.lean`.
- [ ] Port the definitions verbatim (`pa`..`ps`, the branch/succs/eval helpers, `atomsAt`,
      `inclOk`, `inclEdges`, `maximalFrameCheck`, `intBot`, `checkInt`, `checkMin`, and the
      eight formula definitions `phiRef1`, `phiRef2`, `phiRef3`, `exMiddle`, `dblNeg`, `peirce`,
      `deMorgan`, `dummett`), adding docstrings where `docBlame` demands them.
- [ ] Give `checkInt` and `checkMin` explicit result type ascriptions if `lake lint` objects to
      the scratch file's inferred-type `def`s.
- [ ] Pre-declare each assertion's semantic claim, with particular care on the two cited rows —
      `checkInt phiRef1` and `checkInt phiRef3` must report the maximal-frame FAILURE pattern
      (`(true, false)`), and `checkMin phiRef1` likewise — then convert all 12 `#eval!` calls
      (8 `checkInt`, 4 `checkMin`) to the `#guard_msgs` idiom.
- [ ] Build and reconcile per the protocol. The report explicitly flags that this file's
      captured tuple parenthesisation was read off stdout and should be re-derived from the
      actual `#guard_msgs` diff rather than hand-transcribed.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts exactly 12 `#guard_msgs` assertions (8 `checkInt` +
4 `checkMin`) and that the `Minimal.Soundness` import is removable. Confirm the count by
counting `#eval!` occurrences in the scratch file; confirm the import claim by the
build-without-it step, and record the actual outcome either way.

**Files to modify**:
- `CslibTests/WitnessSearch3.lean` - new file; the maximal-inclusion-frame sweep, CI-protected.

**Verification**:
- `lake build CslibTests.WitnessSearch3` succeeds with no `#guard_msgs` mismatch, no warnings.
- The `phiRef1` / `phiRef3` maximal-frame-failure rows assert the failure pattern, not a
  softened one.
- No `sorry`, no `axiom`, no bare `#eval!`.
- Note the module's build wall-time.

---

### Phase 3: Promote MinProbe.lean, fixing the parse error [NOT STARTED]

**Goal**: Create `CslibTests/MinProbe.lean` — the minimal-scheme (`isMinimallyClosed`) witness
evidence — with the scratch file's doc-comment-before-`#eval!` parse error fixed by construction.

**Tasks**:
- [ ] Create `CslibTests/MinProbe.lean` using the Phase 1 template
      (`namespace CslibTests.MinProbe`, `set_option autoImplicit false`,
      `set_option maxRecDepth 100000`, the three paired imports — note the scratch file does
      NOT import `Minimal.Soundness` and does not need it).
- [ ] Module docstring: what is asserted (under `minimalTableau` / `isMinimallyClosed`, both
      `[(1,0)]` and `[(1,0),(2,0)]` discharge the valuation-upward-closure AND the
      `⊥`-upward-closure obligations simultaneously while still falsifying `phiRef1` at world 0,
      whereas `[]`, `[(1,0),(2,1)]` and `[(2,0)]` do not), why it matters (this is the fact the
      `Minimal/Completeness.lean` annotation cites to retract the "independent refutation"
      claim), and the provenance pointer to
      `specs/591_decide_openbranch_countermodel_disposition/scratch/MinProbe.lean`.
- [ ] **Fix the parse error by construction**: the scratch file's two `/-- ... -/` docstrings
      sitting directly above bare `#eval!` commands (the world-table comment and the
      `(edges, val upward-closed, ...)` comment) become, respectively, the `/-- info: ... -/`
      argument of a `#guard_msgs`, with their explanatory prose relocated into the module
      docstring or a `/-! ... -/` section comment. Do NOT leave any `/-- ... -/` block attached
      to a non-declaration.
- [ ] Port the definitions verbatim (`pb`, `pr`, `ps`, `phiRef1`, `branchLabels`, `branchAtoms`,
      `forcesAtom`, `botAtMin`, `atomsAt`, `stepFrom`, `succsAux`, `succs`, `evalF`,
      `upwardClosed`, `botUC`, `minBranch`, `try1`), adding docstrings where `docBlame` demands.
      Note this file's `evalF` and `upwardClosed` take extra parameters (`botAt`, `ws`) relative
      to Phase 1's — they are genuinely different definitions in a different namespace, not a
      duplication to unify.
- [ ] Pre-declare semantic claims, then convert all 6 `#eval!` calls (the world table plus
      `try1 []`, `try1 [(1,0)]`, `try1 [(1,0),(2,1)]`, `try1 [(2,0)]`, `try1 [(1,0),(2,0)]`) to
      the `#guard_msgs` idiom. The two witness rows (`[(1,0)]` and `[(1,0),(2,0)]`) must assert
      the all-three-true pattern; the three non-witness rows must assert their failure pattern.
- [ ] Build and reconcile per the protocol.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts exactly 6 `#guard_msgs` assertions and that exactly two
of the five `try1` candidates (`[(1,0)]` and `[(1,0),(2,0)]`) are witnesses. Confirm the count by
counting `#eval!` occurrences in the scratch file; confirm the two-witness claim from the actual
build output, escalating as a finding if a different set of candidates witnesses.

**Files to modify**:
- `CslibTests/MinProbe.lean` - new file; the minimal-scheme witness evidence, CI-protected, with
  the scratch parse error fixed.

**Verification**:
- `lake build CslibTests.MinProbe` succeeds — this alone is a strictly new result, since the
  scratch original does not parse.
- No `/-- ... -/` block precedes any command; no `#eval!` remains.
- No `sorry`, no `axiom`.
- Note the module's build wall-time.

---

### Phase 4: Fold WitnessSearch2's CI-relevant content into WitnessProbe.lean [NOT STARTED]

**Goal**: Preserve what `WitnessSearch2.lean` certifies without executing its powerset
enumeration: keep the specific-witness assertions fast and CI-protected, and record the
exhaustive-search claim as clearly-attributed prose rather than an unverifiable assertion.

**Tasks**:
- [ ] Add a `/-! ## The exhaustive search, and why it is not re-executed here -/` section to
      `CslibTests/WitnessProbe.lean` recording, in prose: that the admissible edge sets are
      exactly the subsets of the atom-set-inclusion pair set `⊑` (so the original enumeration
      was complete, not a sample); that the original scratch run reported 40 witnesses for
      `phiRef1`; that this figure is **attributed to the original interactive scratch run and is
      NOT re-verified here**; and that a re-run measured no output after 9m10s, which is why it
      is not a CI computation. Point at
      `specs/591_decide_openbranch_countermodel_disposition/scratch/WitnessSearch2.lean` as the
      place to re-run the full search by hand.
- [ ] Record the same-file consolidation decision explicitly in the docstring: there is no
      `CslibTests/WitnessSearch2.lean`, because a file of that name containing no search would
      misrepresent itself; the `Scheme.lean` citation of `WitnessSearch2.lean` should therefore
      retarget to `CslibTests/WitnessProbe.lean` in the Phase 5 follow-up.
- [ ] **Bounded optional addition** — port only the cheap half of `searchWitness`: `subsets`,
      `atomsAt`, `inclOk`, and an `inclPairs`-computing definition WITHOUT the powerset step,
      exposing `(worldCount, admissiblePairCount)` for `phiRef1`. Time it. If it completes in
      under ~10s, add it as a `#guard_msgs` assertion — this CI-protects the size of the search
      space the 40-witness claim ranges over, which is the one part of `WitnessSearch2.lean`
      that is both cheap and load-bearing. If it exceeds the budget, drop it, keep prose only,
      and record the measured time in the docstring and the summary.
- [ ] If the cheap assertion is kept, also assert that the known witness `[(1,0)]` is a subset
      of the computed admissible pair set — this is the cheap, direct form of "the witness lies
      in the enumerated space", and it needs no powerset.
- [ ] For the other seven formulas (`phiRef2`, `phiRef3`, `exMiddle`, `dblNeg`, `peirce`,
      `deMorgan`, `dummett`): do NOT invent witnesses. Phase 2's `CslibTests/WitnessSearch3.lean`
      already witnesses six of them via the maximal frame at negligible cost; cross-reference
      that file from this section and state plainly that the `phiRef1`/`phiRef3` family's
      witnesses are the specific edge sets asserted here and in `MinProbe.lean`, with no
      exhaustive per-formula sweep promoted.
- [ ] Rebuild and reconcile.

**Timing**: 0.75 hours

**Depends on**: 1, 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that computing the admissible pair set without the
powerset step is cheap (under ~10s). Confirm by timing a build of the module with the new
definition before committing to the assertion; if the hypothesis fails, take the documented
prose-only fallback and record the measured time rather than removing the budget check.

**Files to modify**:
- `CslibTests/WitnessProbe.lean` - extend with the search-space section and, conditionally, the
  bounded `inclPairs` assertions.

**Verification**:
- `lake build CslibTests.WitnessProbe` still green, no `#guard_msgs` mismatch.
- The 40-witness figure appears only as attributed, non-re-verified prose — never as a
  `#guard_msgs` assertion.
- No `subsets`-based enumeration is evaluated at build time.

---

### Phase 5: Barrel registration, full CI gate, and follow-up record [NOT STARTED]

**Goal**: Register the three new files so `lake test` picks them up, run the full CSLib CI order
green, and record the out-of-scope follow-up findings.

**Tasks**:
- [ ] Run `lake exe mk_all --module` from the repo root to regenerate `CslibTests.lean`. Do NOT
      hand-edit the barrel. Confirm the three new `public import CslibTests.*` lines landed in
      correct alphabetical position and that the `module -- shake: keep-all ...` first line
      survived.
- [ ] Run the CSLib CI verification order in sequence, fixing forward on any failure:
      `lake build`; `lake exe checkInitImports`; `lake lint`; `lake exe lint-style`;
      `lake test`; `lake exe mk_all --module` (idempotent re-run — must produce no diff);
      `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Confirm `lake test` actually exercises the new assertions (the three modules appear in the
      build output) and record the total added `lake test` wall-time, summed from the per-phase
      measurements plus the observed end-to-end delta.
- [ ] Zero-debt check: `grep` the three new files for `sorry`, `axiom`, `#eval!`, and vacuous
      `:= True` / `:= trivial` patterns — all must be absent. Confirm no new axioms via
      `lean_verify` on a representative promoted definition if any non-`#eval` declaration
      warrants it.
- [ ] Record in the implementation summary, as **flagged follow-ups, not edits**:
      (a) `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:7868` and `:7882` now
      carry stale "not CI-protected" / "not promoted into `CslibTests/`" provenance claims, and
      should be retargeted to `CslibTests/WitnessProbe.lean` and `CslibTests/WitnessSearch3.lean`
      respectively (line numbers are a starting anchor and may have drifted — locate by the
      quoted phrase); (b) `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:143-144`
      cites the minimal-scheme witness fact inline with no filename and can now cite
      `CslibTests/MinProbe.lean`; (c) whether the `Minimal.Soundness` import proved dead
      (Phase 2's finding). All three are `Cslib/` docstring edits outside this task's
      `file_scope` and are deliberately left undone here.
- [ ] Record any semantic-drift findings surfaced by the reconciliation protocol in Phases 1-4.

**Timing**: 1.25 hours

**Depends on**: 1, 2, 3, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts exactly three new barrel entries and an added `lake test`
cost of roughly 12s. Confirm the barrel count from the `mk_all` diff; confirm the cost from the
measured end-to-end `lake test` delta, and report the actual figure rather than the estimate.

**Files to modify**:
- `CslibTests.lean` - regenerated by `lake exe mk_all --module` (three new import lines).

**Verification**:
- Every step of the CSLib CI order exits zero.
- `lake exe mk_all --module` is idempotent (second run produces no diff), which is what
  CI's `lake exe mk_all --check` enforces.
- `git status` shows changes confined to `CslibTests/`, `CslibTests.lean`, and `specs/`.
- Zero new sorries, zero new axioms.

---

## Testing & Validation

- [ ] `lake build CslibTests.WitnessProbe` green, all assertions `#guard_msgs`-protected.
- [ ] `lake build CslibTests.WitnessSearch3` green.
- [ ] `lake build CslibTests.MinProbe` green (a new result — the scratch original does not parse).
- [ ] `lake build` (full project) green.
- [ ] `lake exe checkInitImports` green.
- [ ] `lake lint` green (watch `docBlame` on the ported `def`s, and
      `topNamespace`/`dupNamespace` on the `CslibTests.` namespaces).
- [ ] `lake exe lint-style` green.
- [ ] `lake test` green and visibly exercising the three new modules.
- [ ] `lake exe mk_all --module` idempotent on re-run.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` green.
- [ ] No `sorry`, `axiom`, `#eval!`, or vacuous `:= True` / `:= trivial` in the new files.
- [ ] Negative control: temporarily perturb one expected `/-- info: ... -/` string and confirm
      `lake test` FAILS, then revert. This proves the assertions are actually load-bearing
      rather than silently skipped — the entire point of the promotion.

## Artifacts & Outputs

- `CslibTests/WitnessProbe.lean` - intuitionistic `[(1,0)]` witness for `phiRef1`, plus the
  folded `WitnessSearch2` search-space content.
- `CslibTests/WitnessSearch3.lean` - maximal-inclusion-frame sweep over 8 formulas
  (intuitionistic) + 4 (minimal).
- `CslibTests/MinProbe.lean` - minimal-scheme witness evidence, parse error fixed.
- `CslibTests.lean` - regenerated barrel with three new entries.
- `specs/602_promote_openbranch_witness_probes_to_cslibtests/summaries/01_promote-witness-probes-summary.md`
  - implementation summary including the flagged `Cslib/` citation follow-ups, the
  `Minimal.Soundness` import finding, the Phase 4 timing decision, and any semantic-drift
  findings.

## Rollback/Contingency

- All three promoted files are new; rollback is deleting them and re-running
  `lake exe mk_all --module` to regenerate the barrel without them. No existing file's content
  is modified except the machine-generated barrel, so there is no proof or statement to restore.
- If a probe's output has semantically drifted (reconciliation protocol step 4), do not adjust
  the assertion. Mark the affected phase `[BLOCKED]`, keep the already-green files from earlier
  phases committed, and report the drift — a probe that no longer reproduces is precisely the
  signal this task exists to surface, and finding it before promotion is a successful outcome,
  not a failure.
- If `lake shake` or `lake lint` demands a change that would alter what an assertion computes
  (as opposed to imports, docstrings, or namespacing), stop and report rather than complying —
  the assertions' computational content is the deliverable.
