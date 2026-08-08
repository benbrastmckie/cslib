# Implementation Plan: Promote the three cited-but-absent propositional refutation witnesses into CslibTests/

- **Task**: 592 - Promote the three cited-but-absent propositional refutation witnesses into CslibTests/
- **Status**: [IMPLEMENTING]
- **Effort**: 5.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/592_promote_propositional_refutations_to_cslibtests/reports/01_promote-refutation-witnesses-cslibtests.md`
- **Artifacts**: plans/01_promote-refutation-witnesses-cslibtests.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Two load-bearing refutation witnesses currently live under
`specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/`, where nothing
builds them and nothing protects them from bit-rot; fourteen in-source citations across
`Cslib/Logics/Propositional/Tableau/` point at them with a path prefix that does not resolve from
the repository root. This plan promotes both witnesses into `CslibTests/` as genuine, CI-protected
regression tests (module mode, `#guard_msgs`-asserted, barrel-registered), then repoints all
fourteen citations at paths that resolve from the repository root. Definition of done: both new
`CslibTests.*` targets build with zero warnings and zero `info:` lines, `lake test` passes,
`grep -rn "scratch/" Cslib/Logics/Propositional/Tableau/` returns nothing, the sorry census in
that subtree is still exactly 4, and the set of targets failing the `--wfail --iofail` gate is
byte-identical to the HEAD baseline captured in Phase 1.

### Research Integration

The research report is the primary input and is treated as established fact, not re-derived. The
findings that shape this plan:

- **Finding 1/2 — the correction holds.** All three witnesses exist at HEAD and both load-bearing
  ones compile clean (`lake env lean`, exit 0, zero sorries) against current Mathlib/Cslib. There
  is **no** `[UNVERIFIED] / evidence lost` branch anywhere in this plan, and the implementer must
  not create one. If a witness appears unopenable, that is a path error to re-check, never a
  conclusion to record.
- **Finding 3** supplies the nine exact `#guard_msgs` expected strings.
- **Findings 4/5** supply the verified module-mode header (including the non-obvious
  `Mathlib.Tactic.Ring` / `Mathlib.Tactic.NormNum` doubled meta-imports) and the requirement that
  every retained `#eval` be `#guard_msgs`-wrapped to survive `--iofail`.
- **Finding 6** establishes that the `--wfail --iofail` gate is **already red at HEAD** — this
  drives Phase 1 and the acceptance criterion in Phase 7.
- **Finding 8** establishes that `Scheme.lean:3474` is a fourteenth *repair site*, not the
  template the task description claimed — this drives Phase 6.
- **Findings 9/10/11** supply the citation inventory, the barrel insertion points, and the
  naming/namespace decision.
- **Reuse Check** (report §Reuse Check): no new abstractions. In particular, do **not**
  de-privatise `intExpandBranches.go` to remove `goRaw`'s duplication — that would widen `Cslib/`'s
  public surface to serve a test. `branchesAgree` / `minBranchesAgree` are the intended guard.

Promotion was prototyped end-to-end during research and built green for both files before the
probes were removed. This plan executes a verified-feasible path; it is not exploring one.

**One report figure corrected at plan time.** Finding 5 states "14 bare `#eval`s" and "the five
verbose ones", but its own enumerations are 9 keep (Finding 3) + 7 drop (Finding 5's "Evals to
drop" list). Direct count at HEAD resolves it: `grep -c "#eval"` on the witness returns **16**, at
lines 252-256, 327-332, 392-396. The enumerated lists are correct; the summary numbers 14 and 5
are wrong. Phase 3 uses 16 / 9 / 7 and still re-confirms by grep at implementation time.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` consulted read-only; not modified by this plan.

- **§Remaining A** ("Propositional tableau completeness (**4 sorries**) + atom-persistence lemma")
  is the item this task serves. The four bare Propositional sorries are named there as the
  library's most visible debt; this task makes the evidence underlying their deferral decisions
  in-tree and CI-protected. It does **not** discharge or re-adjudicate them — that is the
  disposition-decision task's job.
- **§Completed** already records the exact precedent being extended: the S4 keyed loop-check guard
  entry cites `CslibTests/AncestorRedirectRefutation.lean` as "the regression witness" for a
  refutation-discharged obligation. This task applies the same pattern to the Propositional
  tableau family.

## Goals & Non-Goals

**Goals**:
- `CslibTests/HvalidShapeRefutation.lean` and `CslibTests/BetaSplitRefutation.lean` exist, are
  module-mode, are barrel-registered, and build with zero warnings and zero `info:` output.
- The nine load-bearing refutation values are asserted by `#guard_msgs`, so a future regression in
  `intuitionisticTableau` / `minimalTableau` breaks the build rather than silently changing a
  printout.
- All fourteen citations in `Cslib/Logics/Propositional/Tableau/` resolve from the repository root.
- Sorry census in `Cslib/Logics/Propositional/Tableau/` unchanged at 4; zero new sorries, zero new
  axioms.

**Non-Goals**:
- Re-adjudicating any `refuted` / `PERMANENTLY DEFERRED` / `DISPOSITION UNDECIDED` / `[UNVERIFIED]`
  verdict. Every annotation's verdict text is left byte-identical; only the path inside it changes.
- Promoting `PersistPrototype.lean`. It is a prototype, not a refutation witness. Its single
  citation is repaired to the archive path (Phase 6). The durability caveat is recorded under Risks.
- Promoting the five uncited probe files (`BetaSplitProbe`, `ForestComparableProbe`,
  `ForestComparableProbe2`, `Gap1FixpointProbe`, `VariantProbe`). Seen, deliberately left.
- Fixing the pre-existing `--wfail --iofail` red at HEAD (the two `Scheme.lean` sorry warnings).
  That failure is not this task's, and silently "fixing" it would hide the very debt the ROADMAP
  tracks.
- Any edit outside `CslibTests/` and `Cslib/Logics/Propositional/Tableau/`, with the single
  exception of the `CslibTests.lean` barrel (required by Finding 10 and unavoidable).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Implementer reads the standing `--wfail --iofail` red as its own regression and starts chasing it | H | H | Phase 1 exists solely to capture the baseline failing-target set to a file before any edit. Every later gate check is a **set difference** against that file, never an exit-code check. Finding 6 is quoted in Phase 1's body. |
| `#guard_msgs` expected strings differ from Finding 3 in whitespace or line-breaking, producing an unfixable-looking mismatch loop | M | M | Phase 3 derives the strings from a live `lake env lean` run on the promoted file and pastes the observed text, using Finding 3's table only to confirm the *values* match. Never hand-transcribe. |
| Rewrapping a citation line breaks out of its comment/docstring region and turns a prose edit into a parse error | H | L | Phases 5 and 6 carry `local` tier, not `prose`, precisely because three lines need rewrapping and site #12 sits inside a docstring. Each edited module is built before the phase closes. |
| The `Mathlib.Tactic.Ring` / `NormNum` meta-import subtlety is forgotten, producing a confusing `unknown tactic` failure in `termination_by`/`decreasing_by` | M | M | Finding 4's verified header is reproduced verbatim in Phase 3's tasks. The expected failure mode is named so it is recognised instantly if it appears. |
| Write-time `no-task-references` hook blocks the Phase 6 archive-path edit | M | L | Research verified the path does not match `TASK_PATTERN` (which requires a literal `task`/`tasks` before digits). If the hook nevertheless fires, **stop and report** — do not add an exemption marker to a `Cslib/` deliverable to route around a guard. |
| Barrel lines inserted at the wrong sort position, or omitted entirely | M | L | Omission is silent and total (an unregistered file is never built, so the promotion buys no CI protection). Phase 7 re-verifies both lines are present and that `lake test` builds them. |
| A count asserted by the research report is wrong (already observed once: the 14/5 eval figures) | M | M | Every count-bearing phase carries a **Scope Hypothesis** with a mechanical confirmation command. Discrepancies are reported, not silently absorbed. |
| Archive path in `Scheme.lean:3474` breaks again on a future vault renumbering | L | L | Accepted, deliberately. Recorded here so it is a known consequence rather than a surprise; promoting `PersistPrototype.lean` would immunise it and is explicitly out of scope. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 5 |
| 6 | 7 | 4, 6 |

Phases within the same wave can execute in parallel. Phases 2 and 3 are serialized despite
touching different witness files because both must edit the shared `CslibTests.lean` barrel.
Phases 4 and 5 are genuinely disjoint: Phase 4 owns `CslibTests/BetaSplitRefutation.lean`, Phase 5
owns the four files under `Cslib/Logics/Propositional/Tableau/`.

---

### Phase 1: Capture the HEAD gate baseline [COMPLETED]

**Actual results** (Scope Hypothesis check): the failing-target set is **5** targets, not the
hypothesized 1 -- `Cslib.Logics.Modal.Tableau.FrameCompleteness`,
`Cslib.Logics.Modal.Tableau.S4.Driver`, `Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness`,
`Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`,
`Cslib.Logics.Propositional.Tableau.Minimal.Completeness`. Per the phase's own instruction ("If
the set is larger than one target ... record the actual values and proceed -- the baseline is
whatever it measures"), the wider set is recorded as-is in `gate-baseline-targets.txt` and used
as the Phase 7 comparison point. The subtree sorry census matched the hypothesis exactly: 4, at
the four named locations. `check-shake-residue.sh` matched its own baseline (12 flagged files).

- **Goal:** Record the exact set of targets failing `lake build --wfail --iofail` at HEAD, before
  any edit, so every later phase can distinguish its own effect on the gate from the standing red.

**Why this phase exists** (Finding 6): the gate is **already red at HEAD** with no changes —
`Scheme.lean:689` and `Scheme.lean:7862` emit `declaration uses 'sorry'` warnings, which `--wfail`
promotes to target failure and `lake` reports as `error: build failed` (exit 1). This is a
pre-existing condition, **not** a regression introduced by this task. Without a recorded baseline,
a later phase cannot tell "still the same two" from "I broke something", and the temptation is
either to chase a phantom or to silently suppress a real sorry. Both are wrong.

- **Tasks:**
  - [ ] Run `lake build --wfail --iofail` over the repository from a clean tree and capture full
        output to `specs/592_promote_propositional_refutations_to_cslibtests/gate-baseline.txt`.
  - [ ] Extract the sorted list of names appearing under `Some required targets logged failures:`
        into `.../gate-baseline-targets.txt`. This sorted list is the comparison artifact — the
        exit code is not, and must never be used as the acceptance signal.
  - [ ] Record the HEAD sorry census for the subtree:
        `grep -rn "sorry" Cslib/Logics/Propositional/Tableau/ | grep -v "^.*--.*sorry"` — confirm
        the four known bare sorries (`Intuitionistic/Completeness.lean:161`,
        `Minimal/Completeness.lean:155`, `Intuitionistic/Scheme.lean:760`,
        `Intuitionistic/Scheme.lean:7937`) and write the count to the baseline file.
  - [ ] Run `bash scripts/check-shake-residue.sh` and append its HEAD result to the baseline file.
  - [ ] Confirm `git status --porcelain` is empty for `CslibTests/` before the baseline run, so the
        baseline is genuinely HEAD and not a dirty tree.

- **Timing:** 0.25 hours (mostly build wall-clock)
- **Depends on:** none
- **Verification Tier:** prose

  *(No deliverable file is edited in this phase. Its only writes are plain-text records under the
  task directory, which have zero compile or elaboration surface. The blind spots `prose` leaves —
  a comment-boundary crossing, a load-bearing doc-comment — cannot arise where no source file is
  touched.)*

- **Scope Hypothesis:** The baseline failing-target set is hypothesized to be exactly
  `{Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme}` and the subtree sorry census exactly
  4. Confirm mechanically by reading the captured `gate-baseline-targets.txt` and the grep count.
  If the set is larger than one target or the census is not 4, **record the actual values and
  proceed** — the baseline is whatever it measures, and a wider baseline is still a valid
  comparison point. Do not attempt to shrink it.

- **Files to modify:**
  - `specs/592_promote_propositional_refutations_to_cslibtests/gate-baseline.txt` - new; full gate output, sorry census, shake result
  - `specs/592_promote_propositional_refutations_to_cslibtests/gate-baseline-targets.txt` - new; sorted failing-target names

- **Verification:**
  - Both baseline files exist and are non-empty.
  - `gate-baseline-targets.txt` is sorted and contains one target name per line.
  - No file under `CslibTests/` or `Cslib/` was modified (`git status --porcelain` clean for both).

---

### Phase 2: Promote HvalidShapeRefutation into CslibTests/ [COMPLETED]

Confirmed the Scope Hypothesis: no extra Mathlib tactic meta-imports were needed (single doubled
import of `Scheme`), and the barrel line sorts between `CslibTests.HilbertSearch` and
`CslibTests.ImportWithMathlib` as hypothesized. `lake build --wfail --iofail
CslibTests.HvalidShapeRefutation` reports `✔ Built` with zero warnings/info specific to the new
target (the logged `Scheme` failure is the pre-existing baseline red, unchanged). `lake test`
succeeds (`✔ [9390/9390] Built CslibTests`). `lake exe lint-style` reports no findings for the
new file.

- **Goal:** `CslibTests/HvalidShapeRefutation.lean` exists as a module-mode, barrel-registered,
  fully-docstringed regression test that builds with zero warnings and zero `info:` lines.

This is the smaller witness (84 lines) and is done first to establish the promotion idiom on low
risk before the 396-line file.

- **Tasks:**
  - [ ] Copy
        `specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/HvalidShapeRefutation.lean`
        to `CslibTests/HvalidShapeRefutation.lean`.
  - [ ] Convert to module mode: `module` as the first line, then the doubled-import idiom
        (`import X` followed by `public meta import X`) for each dependency, matching
        `CslibTests/AncestorRedirectRefutation.lean` and `CslibTests/S4LoopGuardRegression.lean`.
        Per Finding 4 this file needs **no** extra Mathlib tactic imports.
  - [ ] Change the namespace from `Cslib.Logic.PL` to `CslibTests.HvalidShapeRefutation`
        (Finding 11 — test declarations must not land in a library namespace). Retain
        `open Cslib.Logic.PL` so the formula notation still resolves.
  - [ ] Add `set_option autoImplicit false`.
  - [ ] Add a module-level doc comment stating what the file refutes: `IValid (p → (q → p))` holds
        while the old premise's body fails, so the `hvalid` shape the defective
        `tableau_complete` premise demanded is not satisfiable. Give every declaration a
        docstring, including `phiK_valid` and `valuation_not_upward_closed`.
  - [ ] Confirm the file contains no `Cslib.Init` import (Finding 7 — `checkInitImports` filters on
        root `Cslib`, and no existing `CslibTests` file imports it; the new one must not either).
  - [ ] Add `public import CslibTests.HvalidShapeRefutation` to `CslibTests.lean`, in ASCII sort
        order: after `CslibTests.HilbertSearch`, before `CslibTests.ImportWithMathlib`. Edit by
        hand; do **not** run `lake exe mk_all --module`, which targets the `Cslib.lean` barrel.
  - [ ] Confirm every line is ≤ 100 columns.

- **Timing:** 0.75 hours
- **Depends on:** 1
- **Verification Tier:** interface

  *(This phase adds a new module and edits the `CslibTests.lean` barrel, so the changed unit has an
  enumerated direct dependent — the barrel itself — that `local` would not build. The enumerated
  dependent set is exactly `{CslibTests}`, exercised by `lake test`. Chosen over `local` by the
  strictest-applicable tie-break.)*

- **Scope Hypothesis:** This file is hypothesized to need **no** extra Mathlib tactic meta-imports
  (Finding 4 — unlike `BetaSplitRefutation.lean`, it has no `ring` / `norm_num` sites), and its
  barrel line is hypothesized to sort between `CslibTests.HilbertSearch` and
  `CslibTests.ImportWithMathlib`. Confirm the first by building: an `unknown tactic` error names
  exactly which tactic import is missing, and the fix is the doubled `import X` +
  `public meta import X` pair for it. Confirm the second by reading the surrounding lines of
  `CslibTests.lean` rather than trusting the report's excerpt, which may be stale.

- **Files to modify:**
  - `CslibTests/HvalidShapeRefutation.lean` - new; module-mode promotion of the archived witness
  - `CslibTests.lean` - one `public import` line added in ASCII sort position

- **Verification:**
  - `lake build --wfail --iofail CslibTests.HvalidShapeRefutation` reports `✔ Built` with zero
    warnings and zero `info:` lines.
  - `lake test` succeeds (confirms the barrel line parses and the module is reachable).
  - `lake exe lint-style` reports no new findings for the new file.
  - The new target does **not** appear in `gate-baseline-targets.txt` and does not appear in the
    current run's failing-target list.

---

### Phase 3: Promote BetaSplitRefutation into CslibTests/ and make it assert [NOT STARTED]

- **Goal:** `CslibTests/BetaSplitRefutation.lean` exists, builds green under `--wfail --iofail`,
  and asserts the nine load-bearing refutation values via `#guard_msgs` rather than printing them.

- **Tasks:**
  - [ ] Copy
        `specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/BetaSplitRefutation.lean`
        to `CslibTests/BetaSplitRefutation.lean`.
  - [ ] Apply the module-mode header **verbatim** from Finding 4 — all six doubled imports:
        `Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`,
        `Cslib.Logics.Propositional.Defs`, `Cslib.Foundations.Logic.Tableau.Branch`,
        `Mathlib.Tactic.Ring`, `Mathlib.Tactic.NormNum`, each as `import X` +
        `public meta import X`.
        **The two Mathlib tactic imports are the non-obvious part**: `Scheme.lean` imports
        `Mathlib.Tactic.Ring` non-publicly so it does not propagate, and without the explicit
        meta-imports the build fails with `unknown tactic` at the `ring` site in
        `sum_map_pow_const₄` and at the four `Nat.one_le_pow _ _ (by norm_num)` sites inside
        `termination_by`/`decreasing_by`. If that error appears, this task list was not followed —
        it is not a Mathlib problem.
  - [ ] Set namespace `CslibTests.BetaSplitRefutation`; add `set_option autoImplicit false`.
  - [ ] Delete the seven non-load-bearing `#eval`s (output is multi-page or shows no violation):
        `report phiRef2 40`, `report phiRef3 40`, `report phiRef4 40`, `tableAtRealFuel`,
        `branchDump`, `reportMin phiRef3 realFuel`, `reportMin phiRef4 realFuel`.
        **Keep the underlying `def`s** — they stay interactively inspectable and cost nothing.
        Note `phiRef2` deliberately does *not* exhibit the defect (`report phiRef2 40` ends in
        `none`); it must not be promoted to an assertion.
  - [ ] Wrap each of the nine retained `#eval`s as `/-- info: ... -/ #guard_msgs in #eval ...`:
        `report phiRef1 40`, `atomTable phiRef1 40`, `atRealFuel`, `branchesAgree`,
        `fimpWitnesses`, `decisiveFacts`, `reportMin phiRef1 realFuel`, `minBranchesAgree`,
        `minAtomTable`.
  - [ ] Derive the expected strings from a live run (`lake env lean CslibTests/BetaSplitRefutation.lean`
        before wrapping, or from the build's `info:` output), then cross-check the **values**
        against Finding 3's table — in particular `("OPEN", 17, 2, [(1, 0), (2, 1)], [(1, 2), (2, 2)], some (2, 1, 2))`
        for `report phiRef1 40`, `branchesAgree = true`, `decisiveFacts = (true, false)`, and
        `[(2, [2, 3]), (1, [3]), (0, [])]` for `atomTable phiRef1 40`. Paste the observed text; do
        not hand-transcribe from the table. If an observed value disagrees with Finding 3, **stop
        and report** — that would mean the refutation no longer reproduces, which is a finding, not
        an obstacle to route around.
  - [ ] Preserve the module comment explaining that `goRaw` deliberately duplicates the private
        `intExpandBranches.go` (the augmented edge list is a proof-side ghost), and that
        `branchesAgree` / `minBranchesAgree` are the guard keeping the recreation faithful. Do not
        de-privatise `intExpandBranches.go`.
  - [ ] Confirm no `Cslib.Init` import.
  - [ ] Add `public import CslibTests.BetaSplitRefutation` to `CslibTests.lean` in ASCII sort
        order: immediately after `CslibTests.AncestorRedirectRefutation`.

- **Timing:** 1.5 hours
- **Depends on:** 2
- **Verification Tier:** interface

  *(Same rationale as Phase 2: new module plus the shared `CslibTests.lean` barrel, enumerated
  dependent set `{CslibTests}`, exercised by `lake test`.)*

- **Scope Hypothesis:** The witness is hypothesized to contain **16** `#eval` occurrences, of which
  **9** are retained-and-wrapped and **7** are deleted. This corrects the research report, whose
  §Finding 5 prose says "14 bare `#eval`s" and "the five verbose ones" while its own enumerations
  total 16 — the enumerations are right, the summary numbers are wrong. Confirm at implementation
  time with `grep -c "#eval"` on the copied file **before** editing (expect 16, at lines 252-256,
  327-332, 392-396) and `grep -c "#guard_msgs"` **after** (expect 9), with `grep -c "#eval"` also 9
  after. If any count differs, reconcile against the two enumerated lists above — those lists, not
  the totals, are authoritative — and report the discrepancy in the phase's completion note.

- **Files to modify:**
  - `CslibTests/BetaSplitRefutation.lean` - new; module-mode, `#guard_msgs`-asserted promotion
  - `CslibTests.lean` - one `public import` line added in ASCII sort position

- **Verification:**
  - `lake build --wfail --iofail CslibTests.BetaSplitRefutation` reports `✔ Built` with zero
    warnings and zero `info:` lines. A surviving bare `#eval` shows up as an `info:` line and a
    logged target failure — that is the specific failure mode this phase is designed to eliminate.
  - `lake test` succeeds.
  - Neither new target appears in the failing-target set; that set is unchanged from
    `gate-baseline-targets.txt`.

---

### Phase 4: Docstring and style pass on BetaSplitRefutation [NOT STARTED]

- **Goal:** Every declaration in `CslibTests/BetaSplitRefutation.lean` carries a docstring, matching
  the practice of every existing `CslibTests/` file.

Separated from Phase 3 so the risky part (imports, `#guard_msgs` strings) lands green and
committed before the purely additive part begins.

- **Tasks:**
  - [ ] Add a module-level doc comment: what `phiRef1` is, what the refutation shows (worlds 2 and 1
        are augmented-preorder-equivalent while atom `pr` is forced at 2 but not at 1, so the
        decisive triple is `some (2, 1, 2)`), and why the file lives in `CslibTests/`.
  - [ ] Add a docstring to each currently-undocumented declaration: `AugRes`, `expandRaw`,
        `branchLabels`, `branchAtoms`, `forcesAtom`, `pa`, `pb`, `pc`, `realBranch`,
        `recreatedBranch`, `expandRawMin`, `reportMin`, `realBranchMin`, `minBranchesAgree`,
        `minAtomTable`.
  - [ ] Re-check the 100-column limit on every line the docstrings touch.

- **Timing:** 0.75 hours
- **Depends on:** 3
- **Verification Tier:** local

  *(Deliberately **not** `prose`. Lean doc comments are `/-- ... -/` syntax attached to
  declarations — they parse and elaborate, so they are exactly the "doc-comment that is actually
  load-bearing and does compile" case the `prose` tier names as its blind spot. A malformed
  docstring is a parse error, not a cosmetic defect. `local` — single-module build — is sufficient
  because no signature changes and the barrel is untouched.)*

- **Scope Hypothesis:** Fifteen declarations are hypothesized to lack docstrings (the list above;
  note Finding 11 writes `pa`-`pc` as one entry, which expands to three). Confirm at implementation
  time by listing every `def`/`abbrev`/`lemma`/`theorem`/`instance` in the file and checking each
  for a preceding `/--`. Document any declaration found beyond the fifteen and document it too;
  report the corrected count.

- **Files to modify:**
  - `CslibTests/BetaSplitRefutation.lean` - docstrings added; no logic, no imports, no assertions changed

- **Verification:**
  - `lake build --wfail --iofail CslibTests.BetaSplitRefutation` still reports `✔ Built`, zero
    warnings, zero `info:` lines.
  - Every declaration in the file has a preceding docstring.
  - `lake exe lint-style` reports no findings for the file.

---

### Phase 5: Repoint the thirteen scratch/*Refutation.lean citations [NOT STARTED]

- **Goal:** All thirteen citations that name a refutation witness resolve from the repository root
  at their new `CslibTests/` locations.

- **Tasks:**
  - [ ] Apply the substitution `scratch/BetaSplitRefutation.lean` ->
        `CslibTests/BetaSplitRefutation.lean` at the ten Beta sites: `Minimal/Completeness.lean:52`,
        `Minimal/Completeness.lean:149`, `Intuitionistic/Completeness.lean:50`,
        `Intuitionistic/Completeness.lean:144`, `Intuitionistic/Completeness.lean:158`,
        `Intuitionistic/Expansion.lean:297`, `Intuitionistic/Scheme.lean:585`,
        `Intuitionistic/Scheme.lean:747`, `Intuitionistic/Scheme.lean:7845`,
        `Intuitionistic/Scheme.lean:7929`.
  - [ ] Apply `scratch/HvalidShapeRefutation.lean` -> `CslibTests/HvalidShapeRefutation.lean` at
        the three Hvalid sites: `Intuitionistic/Completeness.lean:134`,
        `Intuitionistic/Scheme.lean:7834`, `Intuitionistic/Scheme.lean:7953`.
  - [ ] Rewrap the two lines that exceed 100 columns after the +3-character substitution:
        `Scheme.lean:585` (98 -> 101) and `Scheme.lean:7845` (98 -> 101). Reflow at a word boundary
        onto the following comment line; do not truncate and do not drop words.
  - [ ] Check `Scheme.lean:747` and `Scheme.lean:7953`, which land at exactly 100 after
        substitution. 100 is the limit, so exactly-100 is legal — but confirm with `lint-style`
        rather than by eye, since an off-by-one in the report's byte counts would push them over.
  - [ ] Leave every verdict word untouched. `refuted`, `PERMANENTLY DEFERRED`,
        `DISPOSITION UNDECIDED` (Scheme.lean:7840-7860 and :7926-7938) and the `[UNVERIFIED]`
        marker at :7846 stay byte-identical. Only the path characters change. This task restores
        auditability; it does not re-adjudicate.
  - [ ] Note site #12 (`Scheme.lean:7845`) sits inside a docstring, not a `--` comment — the rewrap
        there must keep the `/-- ... -/` block well-formed.

- **Timing:** 1 hour
- **Depends on:** 3

  *(Depends on 2 and 3 transitively — the verification "every path resolves from the repository
  root" cannot pass until both `CslibTests/` files exist. Listed as 3 because 3 depends on 2.)*

- **Verification Tier:** local

  *(Deliberately **not** `prose`, for two reasons named in the tier's own blind-spot column: three
  lines require rewrapping, which risks crossing a comment or docstring boundary; and site #12 sits
  inside a Lean docstring, which compiles. Each of the four edited modules is built. Not
  `interface` — no symbol name, type, arity, or argument order changes anywhere, so there is no
  dependent set to enumerate.)*

- **Scope Hypothesis:** Thirteen sites are hypothesized here, out of fourteen total `scratch/`
  occurrences in the subtree (the fourteenth, `Scheme.lean:3474`, is Phase 6's). Confirmed at plan
  time: `grep -rn "scratch/" Cslib/Logics/Propositional/Tableau/ | wc -l` returns **14** at HEAD.
  Confirm at implementation time by re-running that grep before the edits (expect 14) and after
  (expect exactly 1, the `Scheme.lean:3474` line). Any other residual count means a site was missed
  or a substitution was applied twice.

- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - 2 citation paths
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` - 4 citation paths
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - 1 citation path
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - 6 citation paths, 2 rewraps

- **Verification:**
  - `grep -rn "scratch/" Cslib/Logics/Propositional/Tableau/` returns exactly one line:
    `Intuitionistic/Scheme.lean:3474`.
  - `lake build` (plain, no `--wfail`) succeeds for all four edited modules. Plain build is correct
    here: `--wfail` on `Scheme` is red at HEAD from the two pre-existing sorry warnings, so its exit
    code carries no signal about this phase.
  - `lake exe lint-style` reports no column-limit findings in the four files.
  - `git diff` shows only path characters and line-wrapping changed — no verdict word altered. Read
    the diff explicitly to confirm this.

---

### Phase 6: Repair the PersistPrototype citation at Scheme.lean:3474 [NOT STARTED]

- **Goal:** The fourteenth citation resolves from the repository root.

**Why this is a separate repair, not a copy of a template** (Finding 8): the task description
states that `Scheme.lean:3474` "is already correct and is the reference form to copy". It is not.
The current text reads
``` `specs/430_.../scratch/PersistPrototype.lean` assumed as a hypothesis, before it was known to be ```
and carries two independent defects: the literal ellipsis `430_...` is not a path, and there is no
`specs/430_*` at the repository root — the directory is
`specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/`. So :3474 fails to resolve
for the same root-relative reason as the other thirteen, plus an ellipsis. The task description's
conclusion that the `scratch/` prefix was task-directory-relative still stands; only the claim that
:3474 is a correct exemplar does not. Treat :3474 as a fourteenth site to repair.

- **Tasks:**
  - [ ] Replace `specs/430_.../scratch/PersistPrototype.lean` with
        `specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/PersistPrototype.lean`.
  - [ ] Reflow the sentence. This is the largest rewrap in the task: 96 -> 151 characters, so the
        line must break across at least two comment lines. Preserve the full sentence including
        "assumed as a hypothesis, before it was known to be ..." and its continuation on the
        following line.
  - [ ] Do not alter the surrounding verdict or annotation text.

- **Timing:** 0.5 hours
- **Depends on:** 5

  *(Serialized after Phase 5 because both phases edit `Scheme.lean`; the dependency is
  file-ownership, not logical.)*

- **Verification Tier:** local

  *(A 55-character expansion forced across a line break carries a real risk of leaving the comment
  region — the exact `prose`-tier blind spot. Build `Scheme` to confirm it still parses.)*

- **Scope Hypothesis:** Exactly **one** site remains after Phase 5, and its line is hypothesized to
  grow from 96 to 151 characters (a +55 expansion needing at least one extra comment line).
  Confirm at implementation time by re-running
  `grep -rn "scratch/" Cslib/Logics/Propositional/Tableau/` (expect exactly one hit) and by
  measuring the actual line length with `awk '{print length}'` before and after, rather than
  trusting the report's byte arithmetic. If more than one site remains, Phase 5 was incomplete —
  return to it rather than absorbing the extra sites here.

- **Verification:**
  - `grep -rn "scratch/" Cslib/Logics/Propositional/Tableau/` returns **nothing**.
  - `grep -rn "430_\.\.\." Cslib/` returns nothing (the ellipsis form is gone).
  - The archive path exists on disk:
    `test -f specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/PersistPrototype.lean`.
  - `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` (plain) succeeds.
  - `lake exe lint-style` reports no column-limit finding at or near :3474.
  - The `no-task-references` write-time hook did not block the edit. If it did, stop and report —
    do not add an exemption marker to a `Cslib/` deliverable.

---

### Phase 7: Final gate against the HEAD baseline [NOT STARTED]

- **Goal:** Confirm the full acceptance criteria, with the `--wfail --iofail` result judged by
  set-difference against the Phase 1 baseline rather than by exit code.

- **Tasks:**
  - [ ] Run `lake test` — must succeed. This is what actually builds the two new files via the
        `CslibTests` barrel root, and is the mechanism that confers CI protection (Finding 7).
  - [ ] Run `lake build --wfail --iofail` over the repository. Extract the failing-target set and
        `diff` it against `gate-baseline-targets.txt`. **Acceptance is: the diff is empty, and
        `CslibTests.BetaSplitRefutation` / `CslibTests.HvalidShapeRefutation` each report `✔ Built`
        with zero warnings and zero `info:` lines.** Acceptance is *not* "the pipeline is green" —
        it cannot be, and making it green is out of scope.
  - [ ] Re-run the subtree sorry census; confirm it is still exactly 4, at the same four locations
        recorded in Phase 1. Confirm zero new axioms.
  - [ ] Run `bash scripts/check-shake-residue.sh`; confirm no new baseline entries. The doubled
        Mathlib tactic imports are genuinely used (by `ring` and `norm_num` in the termination
        proof), so `shake` should not flag them — if it does, that is a finding to report, not a
        reason to drop the imports.
  - [ ] Run `lake exe lint-style` over the whole repository; confirm no new findings.
  - [ ] Confirm both barrel lines are present in `CslibTests.lean` and in ASCII sort position.
  - [ ] Confirm the two promoted files are the only additions under `CslibTests/` and that no probe
        residue was reintroduced (`git status --porcelain CslibTests/`).
  - [ ] Confirm no file outside `CslibTests/`, `CslibTests.lean`,
        `Cslib/Logics/Propositional/Tableau/`, and the task directory was modified.

- **Timing:** 0.75 hours
- **Depends on:** 4, 6
- **Verification Tier:** full

  *(The complete gate set for the repository. Nothing is deferred past this phase — this is the
  ceiling, and it is where the blind spots left open by the `prose`, `local`, and `interface` tiers
  in Phases 1-6 are closed.)*

- **Verification:**
  - `diff` of the current failing-target set against `gate-baseline-targets.txt` is empty.
  - Both new `CslibTests.*` targets green, zero warnings, zero `info:`.
  - `lake test` passes.
  - Subtree sorry census = 4; zero new axioms.
  - `grep -rn "scratch/" Cslib/Logics/Propositional/Tableau/` returns nothing.
  - `check-shake-residue.sh` and `lint-style` clean.

---

## Testing & Validation

- [ ] `lake build --wfail --iofail CslibTests.HvalidShapeRefutation` -> `✔ Built`, zero warnings, zero `info:`
- [ ] `lake build --wfail --iofail CslibTests.BetaSplitRefutation` -> `✔ Built`, zero warnings, zero `info:`
- [ ] `lake test` passes (proves both files are barrel-reachable and CI-protected)
- [ ] Nine `#guard_msgs` assertions match the Finding 3 values, including `branchesAgree = true`,
      `decisiveFacts = (true, false)`, and the decisive triple `some (2, 1, 2)`
- [ ] `grep -rn "scratch/" Cslib/Logics/Propositional/Tableau/` returns nothing
- [ ] Every path cited in the four Tableau files resolves from the repository root (spot-check each
      with `test -f`)
- [ ] Repository-wide `--wfail --iofail` failing-target set is byte-identical to the Phase 1 baseline
- [ ] Sorry census in `Cslib/Logics/Propositional/Tableau/` is exactly 4, unchanged locations
- [ ] Zero new axioms
- [ ] `bash scripts/check-shake-residue.sh` shows no new baseline entries
- [ ] `lake exe lint-style` clean (100-column limit respected, including the three rewrapped lines)
- [ ] No verdict text altered anywhere — confirmed by reading `git diff` on the four Cslib files

## Artifacts & Outputs

- `CslibTests/HvalidShapeRefutation.lean` (new)
- `CslibTests/BetaSplitRefutation.lean` (new)
- `CslibTests.lean` (2 barrel lines added)
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (2 citation paths)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` (4 citation paths)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (1 citation path)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (7 citation paths, 3 rewraps)
- `specs/592_promote_propositional_refutations_to_cslibtests/gate-baseline.txt` (new)
- `specs/592_promote_propositional_refutations_to_cslibtests/gate-baseline-targets.txt` (new)
- `specs/592_promote_propositional_refutations_to_cslibtests/summaries/01_*-summary.md` (on completion)

## Rollback/Contingency

Every phase is independently committable and independently revertible; the two workstreams are in
disjoint trees (`CslibTests/` and `Cslib/Logics/Propositional/Tableau/`), joined only by the
`CslibTests.lean` barrel.

- **A promotion phase (2, 3, 4) fails to go green:** revert that phase's commit. Deleting the new
  `CslibTests/*.lean` file and its barrel line restores HEAD behaviour exactly — no other file
  depends on either. The archived originals under
  `specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/` are never moved or
  modified, so the source of truth survives any failure here.
- **A citation phase (5, 6) breaks a build:** revert that phase's commit. The edits are confined to
  comment and docstring text, so reverting cannot leave a half-state in code.
- **Partial completion is acceptable and useful.** Promotion alone (Phases 1-4) delivers CI
  protection with stale citations; citation repair alone (Phases 5-6) is *not* separately shippable,
  since it would point at files that do not exist. If work must stop mid-task, stop after Phase 4,
  not after Phase 5.
- **The `--wfail --iofail` gate is red at HEAD and will still be red at the end.** That is expected
  and is not a rollback trigger. The rollback trigger is the *failing-target set growing* relative
  to `gate-baseline-targets.txt`.
