# Implementation Plan: Task #581

- **Task**: 581 - sorry_axiom_honesty_gates
- **Status**: [IMPLEMENTING]
- **Effort**: 7.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/581_sorry_axiom_honesty_gates/reports/01_sorry_axiom_honesty_gates.md
- **Artifacts**: plans/01_sorry-axiom-honesty-gates.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, no-task-references-in-deliverables.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add two ratchet gates that make existing proof debt VISIBLE and prevent it from growing: an exact-set
`sorryAx`-taint census over the public `Cslib` API, and a per-file count ceiling on
`set_option warn.sorry false` markers plus code-position `sorry` occurrences. Neither gate discharges
any sorry; both baseline the present tree so they land GREEN on arrival and fail only on regression,
modelled on the in-repo `check-lint-suppressions.sh` (per-file ceiling) and `check-shake-residue.sh`
(exact set) precedents. Definition of done: both scripts exist, exit 0 on the current tree, are wired
into `lean_action_ci.yml` and `pre-pr-check.sh`, are documented in `scripts/README.md`, demonstrably
exit 1 under a deliberately introduced regression and exit 0 (reporting IMPROVED) under a deliberately
introduced improvement, each baseline carries a per-entry debt ledger, and no `.lean` file under
`Cslib/` is modified.

### Research Integration

The research report supplies measured facts this plan treats as settled — **do not re-derive any of
them**:

- **Census cost is decided**: whole-`Cslib`-root-import in a SINGLE process using builtin
  `Lean.collectAxioms` measures ~2.7s over 18,279 public declarations, 43 of which are `sorryAx`-tainted.
  The per-module (one-process-per-file) alternative measured ~16-17 minutes (686 files x ~1.45s) and is
  **rejected**. Do not re-measure. Do not hand-roll a dependency walker — `Lean.collectAxioms` is what
  backs `#print axioms` and is cached via `exportedAxiomsExt`.
- **Public-surface filter**: use `env.setExporting true` + `(exportedEnv.find? n).isSome`. Research
  tested this against the simpler `Name.isInternal` filter and got identical counts (18279/43) on the
  current tree; keep `setExporting` anyway as the technically correct definition of "public", it is free.
- **Suppression numbers**: 18 `set_option warn.sorry false` markers across exactly 5 files (confirmed
  unchanged). True code-position sorry count is **28** across **9** files, split
  Bimodal 23 / Propositional 4 / Modal 1 — independently cross-validated against a figure already on
  record elsewhere in this repo's history. Naive `grep -c sorry` gives 180 and is useless.
- **Per-file sorry split** (use as the baseline acceptance check):
  `ChronicleToCountermodel.lean` 12, `SuccRelation.lean` 7, `UntilSinceCoherence.lean` 2,
  `BXCanonical/Frame.lean` 1, `TemporalConservativity.lean` 1, `Intuitionistic/Scheme.lean` 2,
  `Intuitionistic/Completeness.lean` 1, `Minimal/Completeness.lean` 1, `Modal/Tableau/FrameSoundness.lean` 1.
- **The task description's own Class-1 examples are WRONG**: `intuitionisticTableau_complete` /
  `minimalTableau_complete` contain direct `sorry` tokens and DO warn. The genuine silent-taint
  witnesses are `Cslib.Logic.PL.minimalTableau_decides`
  (`Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean:106`) and
  `Cslib.Logic.PL.intuitionisticTableau_decides`
  (`Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean:97`). Use these as the
  worked example anywhere the mechanism is explained. **Do not propagate the incorrect pair.**
- **`lake build --wfail --iofail` is currently RED on this tree by design** (4 files carry bare
  unsuppressed sorries). This is a pre-existing, accepted, out-of-scope condition — but it dictates the
  CI placement of the new steps (see Phase 4).

Two additional facts verified during planning (cheap, non-duplicative of research):

- **All 18 markers are the declaration-scoped `set_option warn.sorry false in` form; zero are the
  blanket (no trailing `in`) form.** This is decisive for the scanner design: `check-lint-suppressions.sh`'s
  `$`-anchored blanket regex would count **0** here. The new script MUST use the plain substring
  `set_option warn.sorry false` and MUST NOT copy the sibling script's anchored regex.
- **No line in the tree contains both `warn.sorry` and a separate code-position `sorry`.** The
  discrimination rule's "drop the whole line" step (see Phase 3) therefore loses nothing on the current
  tree. Record this as a known, currently-vacuous edge case in the script header.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task.

## Settled Decisions (do not re-litigate)

These were decided by the orchestrator after the research flagged them. The implementer must
implement them as written and must not reopen either.

**D1 — Baseline ledger uses durable anchors, never task numbers.**
`.claude/rules/no-task-references-in-deliverables.md` is a project-instruction-level override and
forbids task-number references anywhere outside `specs/**`. Both baseline files live in `scripts/`, so
they MUST NOT carry task numbers — not in data rows, not in header comments, not in the scripts, the
workflow, or the README. The *intent* of the "live debt ledger" requirement is satisfied in full by the
research's recommended durable anchor: **declaration name + owning file path + the in-source blocking
reason** (`-- blocked on X` / `-- TODO: depends on Y` comments already exist at essentially every sorry
site). This is a strictly better ledger than a task number: self-contained, survives vault renumbering,
and directly greppable (`grep -rn port_continuous_completeness_bimodal Cslib/` immediately answers
"has this blocker landed yet?", which a task number never does).

**D2 — Wire into `lean_action_ci.yml` as scoped, and fix the correctness defect.**
Scope item 3 is an explicit written requirement and stands; it is NOT downgraded to pre-pr-check-only
on precedent grounds. But that workflow's build step is currently red by design, so a step placed after
it would never execute — dead configuration is not a gate. Therefore:
- The Lean-free suppression gate is placed **before** the `leanprover/lean-action@v1` build step, so it
  runs unconditionally and fails fast.
- The build-dependent axiom census is placed **after** the build step and carries `if: always()`.
- An inline comment records the divergence cost this adds against the upstream-synced file, and notes
  that `check-lint-suppressions.sh` / `check-shake-residue.sh` deliberately chose the other tradeoff, so
  a future reader sees the choice was deliberate.
- **Additionally** (not instead) wire both into `scripts/pre-pr-check.sh` and document both in
  `scripts/README.md`, matching how the preceding guard registered itself.

**D3 — Improvements report loudly and exit 0; they do not fail the build.**
Scope item 1 says "require the baseline to be re-tightened." Making an improvement exit 1 would turn a
ratchet into an absolute gate that is red whenever someone fixes something — perverse, and matching
neither in-repo precedent. Both new scripts therefore exit **0** on improvement while printing a
prominent `ACTION REQUIRED` block naming the exact `--update` command. This is the same disposition as
both existing ratchet scripts.

**D4 — No `lakefile.toml` change.** The census Lean driver is invoked via
`lake env lean --run scripts/AxiomCensus.lean`, not registered as a `[[lean_exe]]`. Research confirmed
both work at the same ~2.7s cost; the `lake env lean --run` form keeps `lakefile.toml` out of the diff
entirely, which is worth more than the marginal idiomacy of the `checkInitImports` precedent.

## File Scope (expanded from the declared scope — read this)

The task's declared FILE SCOPE lists 3 files. The actual scope is 8, because two baseline files and one
Lean driver are structurally required by the declared scripts, and `pre-pr-check.sh` / `README.md` are
mandated by D2. The expansion is recorded here so it is not mistaken for scope creep.

| Path | Action | Source of requirement |
|---|---|---|
| `scripts/AxiomCensus.lean` | create | structural (driver for `check-axiom-census.sh`) |
| `scripts/check-axiom-census.sh` | create | declared scope item 1 |
| `scripts/axiom-census-baseline.txt` | create | declared scope items 1 + 4 |
| `scripts/check-sorry-suppressions.sh` | create | declared scope item 2 |
| `scripts/sorry-suppression-baseline.txt` | create | declared scope items 2 + 4 |
| `.github/workflows/lean_action_ci.yml` | modify | declared scope item 3 (D2) |
| `scripts/pre-pr-check.sh` | modify | D2 |
| `scripts/README.md` | modify | D2 |

**Explicitly NOT touched**: `lakefile.toml` (D4); any `.lean` file under `Cslib/`; any existing
`set_option warn.sorry false in` marker; any proof.

## Goals & Non-Goals

**Goals**:
- A `sorryAx`-taint census over the public `Cslib` API that fails when a declaration outside the baseline
  becomes tainted, and reports (without failing) when a baseline entry becomes clean.
- A suppression/sorry count ratchet that distinguishes code-position sorries from prose mentions, with
  the discrimination rule stated explicitly in the script.
- Both gates exit 0 on the current tree, are wired into CI and `pre-pr-check.sh`, and are documented.
- Both baselines double as a live debt ledger via durable anchors (D1).
- Both gates exit 2 — never 0 — when their underlying tool fails to run.

**Non-Goals**:
- Discharging, restating, adding, relocating, or hiding any sorry.
- Removing any existing `set_option warn.sorry false in` marker.
- Altering any proof, or modifying any `.lean` file under `Cslib/`.
- Fixing the pre-existing red `lake build --wfail --iofail` state (4 files with bare sorries).
- Re-litigating D1-D4.

## Carry-Over Conventions (mandatory for both scripts)

1. `set -uo pipefail` **without** `-e`. These tools legitimately exit nonzero when they have findings;
   a naive `set -e` aborts before the comparison ever runs. Accumulate into a counter, single `exit` at
   the end. Both existing ratchet scripts do exactly this and say why in their headers.
2. **Exit-code contract**: `0` clean-or-improved, `1` regression, `2` usage/environment error.
   **Exit 2 when the underlying tool fails to RUN is a hard requirement for BOTH scripts** — a broken
   environment must never masquerade as a clean empty result. This is the direct analogue of
   `check-shake-residue.sh`'s "shake exit 1 but zero parseable lines -> exit 2, never a clean empty set".
3. `--update` (rewrite baseline from current tree) and `--list` (print live state) flags, matching both
   precedents' CLI shape. `--update` MUST refuse to write from a failed/unparseable run (exit 2).
4. Baseline files carry a header comment block: what the file is, that it is machine-generated,
   "do not hand-edit", and the exact regenerating command. Both existing baselines do this and it is
   load-bearing — it is the only thing stopping someone editing the ceiling down without fixing anything.
5. Comparison shape: axiom census = **exact set** (a declaration either is or isn't tainted);
   suppressions = **per-file count ceiling** (the one place the task explicitly says "ceiling").
6. **No task-number references** in any script header, baseline file, workflow comment, or README text (D1).
7. Prove regression AND improvement paths using `.bak` copies and `rm`. **Never** `git checkout -- <path>`
   or `git restore <path>` — forbidden on a dirty tree by `.claude/rules/git-workflow.md`.
8. `shellcheck` is **not installed in this environment** and cannot be run locally; the path-triggered
   `.github/workflows/shellcheck.yml` (`scripts/**/*.sh`, `--severity=warning`) will sweep both new
   scripts automatically. Mitigate by modelling both scripts closely on the two existing ones, which
   already pass.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Axiom census step is red in CI because the build step failed to produce `.olean`s | H | M | Script exits 2 with an explicit "environment broken, run `lake build` first" message — a loud, correct failure, never a silent false pass. Record this expectation in the workflow comment so a red census step is read as "build broken", not "census broken". |
| Live census output does not reproduce 18279/43 | H | L | Phase 2 gates baselining on reproducing exactly 43 tainted declarations; a mismatch halts and is investigated before any baseline is written. |
| `\bsorry\b` occurrence-vs-line counting yields a total other than 28 | M | M | Phase 3 gates baselining on reproducing the exact 9-file/28-total split listed in Research Integration; try occurrence counting (`grep -o \| wc -l`) first, and if the split does not reproduce, adjust and document rather than silently baselining a different number. |
| Implementer copies `check-lint-suppressions.sh`'s `$`-anchored blanket regex | H | M | Called out twice (Research Integration + Phase 3 tasks): all 18 markers are the `... in` form and the anchored regex counts 0. Phase 3 verification requires marker total == 18 across 5 files. |
| `shellcheck` warnings only surface in CI (not installable locally) | M | M | Model both scripts line-for-line on the two existing passing scripts; avoid unquoted expansions, use `while read -r`, assign-then-default around `grep -c`. |
| A stray scratch `.lean` probe file is left under `Cslib/` | H | L | Phase 6 creates the probe and removes it within the same phase, then asserts `git status --porcelain Cslib/` is empty as an explicit checklist item. |
| Adding steps to the upstream-synced workflow creates future sync conflict hunks | M | H | Accepted, explicit cost of D2; recorded inline in the workflow comment alongside the note that the two sibling guards chose the other tradeoff. |
| `scripts/AxiomCensus.lean` trips `lint-style-action` in CI | M | M | Mirror `scripts/CheckInitImports.lean`'s header/module conventions exactly (Phase 1 task); `weak.linter.allScriptsDocumented = false` is already set in `lakefile.toml`. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3 | -- |
| 2 | 2 | 1 |
| 3 | 4, 5 | 2, 3 |
| 4 | 6 | 4, 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Lean axiom-census emitter [COMPLETED]

**Goal**: `scripts/AxiomCensus.lean` prints, in one process, the exact set of `sorryAx`-tainted public
`Cslib` declarations as machine-parseable TSV plus a summary line the shell driver uses as its
exit-2 sanity gate.

**Tasks**:
- [x] Read `scripts/CheckInitImports.lean` and mirror its file header, `module`/import conventions, and
      `main`/IO shape. Do not invent a different style.
- [x] Implement: `import Cslib`; obtain the environment; `env.setExporting true` to get the exported
      environment; iterate `env.constants`; keep constants whose name has prefix `Cslib`, is not
      `Name.isInternal`, whose `ConstantInfo` is `.thmInfo | .defnInfo | .opaqueInfo`, and which satisfy
      `(exportedEnv.find? n).isSome`.
- [x] For each kept declaration call **builtin `Lean.collectAxioms`** (from `Lean.Util.CollectAxioms`).
      Do NOT hand-roll a dependency walker. Tainted := the returned axiom set contains `sorryAx`.
      *(deviation: altered -- measured directly against this repo's actual built `.olean`s, calling
      `Lean.collectAxioms` per declaration in a loop over the 18279 candidates took on the order of
      minutes (individual calls cost 50-300ms EACH, including on repeat calls for the SAME declaration
      within the same process -- confirmed by calling it 5x in a row on one fixed name and observing
      ~64ms every time), because `exportedAxiomsExt`'s cross-declaration cache is not being hit for a
      large fraction of this environment's declarations (verified: some Mathlib declarations are
      likewise uncached/slow, so this is not a Cslib-specific artifact). This directly contradicts the
      research's ~2.7s premise for this exact mechanism on this exact tree. Root cause not further
      diagnosed (outside this task's scope to fix Lean's own extension population). Fix implemented:
      `collectAxiomsCached` in `scripts/AxiomCensus.lean` reimplements the identical dependency-walk
      semantics (same `ConstantInfo` case dispatch, same `sorryAx`-membership taint definition) but
      threads an explicit `IO.Ref (Std.HashMap Name (Array Name))` cache across the WHOLE census run
      instead of per-declaration, so shared dependencies are walked once. This keeps every other part
      of the specified design (single process, whole-root-import, no per-module spawning) and
      reproduces the identical `tainted=43` figure the plan's baseline is built from, in ~8.6s total
      (measured, 3 runs: 8.6s/8.5s/8.7s) -- "a few seconds, not minutes" per this phase's own
      verification bar. Fully documented in the script's own header comment for a future reader.)*
- [x] For each tainted declaration emit one TSV line: `<fully-qualified name>\t<repo-relative file path>\t<reason>`.
  - Owning file path: resolve via the module of the declaration (`env.getModuleFor?` /
    `getModuleIdxFor?` -> module name) and convert the module name to its `Cslib/.../X.lean` path.
  - Reason (durable anchor, D1), in this precedence order:
    1. `direct` — the declaration's own value satisfies `Expr.hasSorry`.
    2. `<name>` — the lexicographically-first constant directly referenced by this declaration
       (`getUsedConstants`) that is itself `sorryAx`-tainted (single-hop attribution).
    3. `transitive` — no single-hop tainted dependency found.
- [x] Emit a final summary line to stdout: `# total=<N> tainted=<M>`. This line is what lets the shell
      driver distinguish "clean census" from "broken environment" — it is not decorative.
- [x] Sort the TSV lines by declaration name so the baseline diff is stable.
- [x] Run `lake env lean --run scripts/AxiomCensus.lean` and confirm it prints `# total=18279 tainted=43`
      (small drift in `total` is acceptable; `tainted=43` is the load-bearing figure) and completes in a
      few seconds, not minutes. Confirmed: `# total=18279 tainted=43`, ~8.6s wall clock.
- [x] Spot-check that `Cslib.Logic.PL.minimalTableau_decides` and
      `Cslib.Logic.PL.intuitionisticTableau_decides` appear in the output — these are the genuine
      silent-taint witnesses and their presence is the proof the census catches what `--wfail` cannot.
      Confirmed present, both with reason = their respective `_complete` dependency (single-hop).

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `scripts/AxiomCensus.lean` - new; single-process census emitter

**Verification**:
- `lake env lean --run scripts/AxiomCensus.lean` exits 0, prints 43 TSV lines plus one `# total=...` line.
- Both `_decides` witnesses present in the output.
- No file under `Cslib/` modified (`git status --porcelain Cslib/` empty).

---

### Phase 2: Axiom-census ratchet script and baseline [NOT STARTED]

**Goal**: `scripts/check-axiom-census.sh` + `scripts/axiom-census-baseline.txt` implement an exact-set
ratchet over the Phase 1 output, green on the current tree.

**Tasks**:
- [ ] Write `scripts/check-axiom-census.sh` modelled structurally on `scripts/check-shake-residue.sh`
      (exact-set precedent): `set -uo pipefail`, `REPO_ROOT` resolved from `BASH_SOURCE`, `cd "$REPO_ROOT" || exit 2`,
      `--update` / `--list` / bare / usage-error dispatch, associative-array set comparison, single exit at end.
- [ ] Header comment block covering: what silent axiom taint is and why `--wfail` cannot see it (use the
      `minimalTableau_decides` / `intuitionisticTableau_decides` worked example — **never** the
      `_complete` pair); why the baseline is an exact set and not a count; that it needs built `.olean`s;
      and the full exit-code contract. No task numbers.
- [ ] Run helper that invokes `lake env lean --run scripts/AxiomCensus.lean` **exactly once**, capturing
      output and exit code into globals (call it directly, never inside `$(...)`, or the assignments are
      lost to a subshell — this is the documented trap in the shake precedent).
- [ ] Exit-2 conditions, all mandatory:
  - the `lake env lean --run` invocation exits nonzero;
  - it exits 0 but no `# total=` summary line is parseable from its output;
  - the summary reports `total=0` (an empty environment must never read as "zero taint").
- [ ] Comparison: build the live set from TSV field 1 only. FAIL (regression) for each live name absent
      from the baseline; IMPROVED for each baseline name absent from the live set.
      **The `<file>` and `<reason>` columns are ledger metadata and are NOT compared** — a changed reason
      for an unchanged declaration must never fail the check. State this in the header.
- [ ] `--update` writes the baseline with the D1 ledger header comment block plus the sorted TSV rows;
      refuses to write from a run that would have exit-2'd.
- [ ] Failure message: name the offending declarations, explain that a declaration outside the baseline
      became `sorryAx`-tainted, and state that a genuinely justified new entry must be added deliberately
      via `--update` in the same commit with the reason in the commit message — never as a silent side effect.
- [ ] Improvement message: `ACTION REQUIRED` block naming `bash scripts/check-axiom-census.sh --update`,
      exit 0 (D3).
- [ ] Generate the baseline via `--update`. **Gate**: confirm it contains exactly 43 data rows before
      accepting it. If not 43, stop and investigate rather than baselining a different number.
- [ ] Run the script bare and confirm `exit 0` with "matches the baseline exactly".

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `scripts/check-axiom-census.sh` - new; exact-set ratchet driver
- `scripts/axiom-census-baseline.txt` - new; 43-row ledger baseline (name / file / reason)

**Verification**:
- `bash scripts/check-axiom-census.sh` exits 0 on the clean tree.
- `bash scripts/check-axiom-census.sh --list` prints the live tainted set.
- Baseline has exactly 43 data rows, each with three tab-separated fields, and a "do not hand-edit"
  header naming the regenerating command.
- No task number appears anywhere in either new file.

---

### Phase 3: Sorry-suppression count ratchet and baseline [NOT STARTED]

**Goal**: `scripts/check-sorry-suppressions.sh` + `scripts/sorry-suppression-baseline.txt` implement a
per-file two-count ceiling (markers, code-position sorries), green on the current tree, with no build
dependency.

**Tasks**:
- [ ] Write the script modelled structurally on `scripts/check-lint-suppressions.sh` (per-file ceiling
      precedent): `set -uo pipefail`, `SCAN_ROOT="Cslib"`, `--update` / `--list` / bare / usage dispatch,
      associative-array ceiling comparison, assign-then-default around `grep -c` (it exits 1 on zero
      matches, so `|| echo 0` would emit two lines).
- [ ] **State the discrimination rule explicitly in the header**, as the tested rule, in this order:
      1. strip block comments `/- ... -/` non-greedily across the whole file (`perl -0777 -pe 's/\/-.*?-\///gs'`),
         which also captures doc comments since `/--` starts with `/-`;
      2. strip line comments (`--` to end of line) per surviving line;
      3. drop any surviving line containing the substring `warn.sorry`;
      4. count `\bsorry\b` word-boundary occurrences on what remains.
      Also state: `sorryAx` is excluded automatically by `\b` (no word boundary between `y` and `A`);
      step 3 is load-bearing, not decorative, because `\bsorry\b` matches inside `warn.sorry` (`.` is a
      non-word character); and step 3's known edge case — a single line carrying both a `warn.sorry`
      option and a separate code-position `sorry` would be undercounted — **does not occur anywhere on
      the current tree** (verified), but is recorded so a future reader knows the limit.
- [ ] Marker count: plain substring `set_option warn.sorry false`. **Do NOT copy
      `check-lint-suppressions.sh`'s `$`-anchored blanket regex** — all 18 markers in this tree are the
      declaration-scoped `... false in` form and the anchored regex would count 0. State in the header
      that this gate deliberately counts BOTH the file-scoped and `in`-scoped forms, because its ratchet
      is on total suppression volume, not on scope discipline (which is the sibling script's job).
- [ ] Emit a baseline row `<markers> <sorries> <path>` for every file with `markers > 0 || sorries > 0`,
      path-sorted for a stable diff.
- [ ] D1 ledger: `--update` also emits, as `#` comment lines beneath the data, the distinct in-source
      blocker annotations found at each file's sorry sites (the trailing `-- blocked on X` /
      `-- TODO: depends on Y` / `-- depends on Z` comment text on lines carrying a code-position sorry),
      formatted `#   <path>: <blocker text>`. Comment lines are skipped by the parser, so the ledger
      never affects comparison. No task numbers.
- [ ] Exit-2 conditions, all mandatory:
  - `perl` is not on `PATH` (`command -v perl`);
  - the `find "$SCAN_ROOT" -name '*.lean'` sweep yields **zero** files (a scan root that resolves to
    nothing must never report "0 sorries, clean");
  - the `perl` comment-stripping pass exits nonzero on any file.
- [ ] Comparison: FAIL when a file's live marker count OR live sorry count exceeds its baseline ceiling
      (including a file with no baseline row introducing either); IMPROVED when either count is below
      baseline. Report both counts distinctly so a maintainer can tell which moved.
- [ ] Improvement message: `ACTION REQUIRED` block naming `bash scripts/check-sorry-suppressions.sh --update`,
      exit 0 (D3).
- [ ] Generate the baseline via `--update`. **Gate**: confirm marker total == 18 across exactly 5 files,
      and sorry total == 28 across exactly 9 files with the per-file split listed in Research Integration
      (12/7/2/1/1 for the Bimodal five, 2/1 for Intuitionistic Scheme/Completeness, 1 for Minimal
      Completeness, 1 for Modal FrameSoundness). If occurrence counting does not reproduce 28, try
      line counting, and document whichever reproduces the verified split. Do not silently baseline a
      different number.
- [ ] Run the script bare and confirm `exit 0`.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `scripts/check-sorry-suppressions.sh` - new; per-file two-count ceiling ratchet
- `scripts/sorry-suppression-baseline.txt` - new; 9-row ceiling baseline plus blocker ledger comments

**Verification**:
- `bash scripts/check-sorry-suppressions.sh` exits 0 on the clean tree.
- `--list` prints per-file `<markers> <sorries> <path>`.
- Totals reproduce 18/5 files and 28/9 files with the exact per-file split.
- Baseline header states "do not hand-edit" and the regenerating command; ledger comment lines present.
- No task number appears anywhere in either new file.

---

### Phase 4: CI wiring in lean_action_ci.yml [NOT STARTED]

**Goal**: Both gates run as their own steps in `.github/workflows/lean_action_ci.yml` and actually
execute, with the divergence cost recorded inline (D2).

**Tasks**:
- [ ] Add the **suppression** step **before** the `uses: leanprover/lean-action@v1` step (after the
      `Set TEST_ARGS manually` step). It is Lean-free and takes seconds, so placing it first makes it
      fail fast and removes any need for `if: always()`. Follow the existing step style:
      `name: "sorry-suppression ratchet"` with `run: |` + `set -e` + `bash scripts/check-sorry-suppressions.sh`.
- [ ] Add the **axiom census** step **after** the `lean-action` build step, carrying `if: always()`, so
      it still executes while the build step remains red on the four known bare-sorry files. Same
      `run: |` + `set -e` + `bash scripts/check-axiom-census.sh` shape.
- [ ] Add an inline comment block above the two new steps recording, without task numbers:
  - that this workflow file is shared with the `leanprover/cslib` upstream remote and actively synced,
    so each new step adds a conflict hunk to every future sync — this is the accepted, deliberate cost
    of wiring these two gates into CI directly;
  - that `check-lint-suppressions.sh` and `check-shake-residue.sh` chose the other tradeoff (a separate
    local-only workflow / `pre-pr-check.sh`-only), so a future reader can see this divergence was a
    deliberate choice and not an accident;
  - why the census step carries `if: always()` (the build step is currently red by design on the four
    files carrying bare unsuppressed sorries; a step placed after it without `if: always()` would never
    execute, and a gate that never executes is not a gate);
  - that the census step exits 2 when `.olean`s are missing, so a red census step means the build is
    broken, not that the census is broken — it never silently reports a clean empty result.
- [ ] Confirm no other step's behaviour changed (the `mk_all --check`, `checkInitImports`, and
      `lint-style-action` steps keep their existing conditions; only the two new steps carry `if: always()`).
- [ ] Validate the YAML parses (`python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/lean_action_ci.yml'))"`
      or equivalent).

**Timing**: 0.75 hours

**Depends on**: 2, 3

**Files to modify**:
- `.github/workflows/lean_action_ci.yml` - two new steps plus the divergence-cost comment block

**Verification**:
- YAML parses.
- `git diff .github/workflows/lean_action_ci.yml` shows only additive hunks (two steps + one comment block).
- No task number in the added text.

---

### Phase 5: pre-pr-check.sh and scripts/README.md wiring [NOT STARTED]

**Goal**: Both gates are locally runnable through the same numbered pre-PR script every other ratchet
uses, and are documented in the same style as the preceding guard (D2).

**Tasks**:
- [ ] Add step 8 to `scripts/pre-pr-check.sh` for the suppression ratchet, following the exact shape of
      the existing steps 6/7: `echo "8. ..."`, `if ! bash "$(dirname "${BASH_SOURCE[0]}")/check-sorry-suppressions.sh"; then ... failed=1; fi`.
- [ ] Add step 9 for the axiom census, with an inline note (like step 7's "needs the completed build from
      steps 4/5 above") that it needs the completed build from steps 4/5.
- [ ] Add a short comment above step 8, in the spirit of the existing step-6 comment, explaining why
      these gates are independent of step 1's PR-scope sorry check: step 1 scans a narrow directory set
      and fails on any sorry there, whereas these two ratchet whole-tree debt and pass on the existing
      debt by construction. They answer different questions.
- [ ] Add two `scripts/README.md` entries under their own headings, mirroring the
      `check-shake-residue.sh` entry's structure (rationale paragraph + `**Usage:**` fenced block with
      the bare / `--list` / `--update` invocations).
  - Axiom-census entry must explain silent taint using the `minimalTableau_decides` /
    `intuitionisticTableau_decides` example, note the build dependency, and note that the baseline
    doubles as a debt ledger keyed on declaration name + owning file + blocking reason.
  - Suppression entry must state the discrimination rule in one or two sentences and note that the
    naive `grep -c sorry` figure is an order of magnitude wrong.
  - No task numbers in either entry.
- [ ] Confirm `bash scripts/pre-pr-check.sh` still has valid syntax (`bash -n scripts/pre-pr-check.sh`).
      Do **not** run the full script here — steps 4/5 rebuild the tree and step 5 is red by design.

**Timing**: 0.75 hours

**Depends on**: 2, 3

**Files to modify**:
- `scripts/pre-pr-check.sh` - two new numbered steps plus an explanatory comment
- `scripts/README.md` - two new documented script entries

**Verification**:
- `bash -n scripts/pre-pr-check.sh` clean.
- Both new steps present and numbered 8/9, using the same `failed=1` accumulation pattern.
- README entries present with `**Usage:**` blocks; no task numbers.

---

### Phase 6: Prove regression and improvement paths, restore clean tree [NOT STARTED]

**Goal**: Demonstrate, with recorded evidence, that each gate exits 1 under a deliberately introduced
regression and exits 0 (reporting IMPROVED) under a deliberately introduced improvement — then leave
the tree exactly as found.

**Method note — read before starting.** The task's definition of done suggests proving the axiom-census
regression with "a scratch tainted declaration". That is **not achievable within this task's non-goals**:
a scratch declaration is only censused if it is reachable from the `Cslib` root import, which requires
editing `Cslib.lean` — a `.lean` file under `Cslib/`, which the non-goals forbid — and would additionally
cost a full rebuild. The equivalent and stronger proof is to mutate the **baseline** instead: removing a
name from the baseline drives the identical code path (live set contains a name absent from baseline ->
FAIL -> exit 1) with zero risk to the library and no rebuild. The suppression gate's scratch-file probe
**is** achievable (its scanner is a pure `find`-based text sweep with no import or build dependency), so
that one is done literally as the definition of done describes.

**Tasks**:
- [ ] Axiom census, **regression**: `cp scripts/axiom-census-baseline.txt scripts/axiom-census-baseline.txt.bak`;
      delete one data row from the baseline; run the script; confirm it prints `FAIL` naming that
      declaration and exits **1**; restore with `mv` from the `.bak`. Record the observed exit code.
- [ ] Axiom census, **improvement**: `.bak` the baseline again; append a data row for a declaration that
      does not exist (e.g. `Cslib.ZZNonexistentCensusProbe`); run the script; confirm it prints
      `IMPROVED` plus the `ACTION REQUIRED` re-baseline instruction and exits **0**; restore via `mv`.
- [ ] Suppressions, **regression (scratch file probe)**: create a new untracked file
      `Cslib/ZZScratchSuppressionProbe.lean` containing one `set_option warn.sorry false in` marker and
      one code-position `sorry`; run the script; confirm it prints `FAIL` for that path (introducing
      counts where the baseline has none) and exits **1**; then `rm` the probe file. Do not build during
      this window and do not leave the file in place.
- [ ] Suppressions, **improvement**: `.bak` the baseline; raise one file's ceilings above its live counts;
      run the script; confirm it reports `IMPROVED` and exits **0**; restore via `mv`.
- [ ] Re-run both scripts bare and confirm both exit **0** on the restored tree.
- [ ] Assert the tree is clean of test residue: `git status --porcelain Cslib/` is **empty**; no `.bak`
      files remain under `scripts/`; `git diff -- scripts/axiom-census-baseline.txt scripts/sorry-suppression-baseline.txt`
      shows the baselines exactly as generated in Phases 2/3.
- [ ] Record all six observed exit codes in the implementation summary as the definition-of-done evidence.

**Timing**: 1.5 hours

**Depends on**: 4, 5

**Files to modify**:
- none permanently (all Phase 6 mutations are `.bak`-restored or `rm`-removed within the phase)

**Verification**:
- Six recorded exit codes: census regression 1, census improvement 0, suppression regression 1,
  suppression improvement 0, both gates bare 0.
- `git status --porcelain Cslib/` empty.
- No `.bak` or scratch `.lean` files remain.

---

## Testing & Validation

- [ ] `lake env lean --run scripts/AxiomCensus.lean` exits 0 and reports `tainted=43`.
- [ ] `bash scripts/check-axiom-census.sh` exits 0 on the clean tree.
- [ ] `bash scripts/check-sorry-suppressions.sh` exits 0 on the clean tree.
- [ ] `bash scripts/check-axiom-census.sh --list` and `--update` behave as specified; `--update` refuses
      to write from a failed run.
- [ ] `bash scripts/check-sorry-suppressions.sh --list` and `--update` behave as specified.
- [ ] Both scripts exit 2 (not 0, not 1) when their underlying tool cannot run — verify at least the
      census case by invoking with a deliberately broken `lake` on `PATH`, or by asserting the code path
      is present and unreachable-by-construction if that cannot be simulated safely.
- [ ] Suppression baseline totals: 18 markers / 5 files; 28 sorries / 9 files with the verified split.
- [ ] Axiom census baseline: exactly 43 rows, three tab-separated fields each.
- [ ] Phase 6's six exit-code observations all match expectation.
- [ ] `bash -n scripts/pre-pr-check.sh` clean; the workflow YAML parses.
- [ ] `git status --porcelain Cslib/` is empty and `git diff -- Cslib/` is empty at the end.
- [ ] `grep -rnE 'task [0-9]+|tasks [0-9]+' scripts/check-axiom-census.sh scripts/check-sorry-suppressions.sh scripts/axiom-census-baseline.txt scripts/sorry-suppression-baseline.txt scripts/AxiomCensus.lean scripts/README.md .github/workflows/lean_action_ci.yml`
      returns nothing (D1 compliance check).
- [ ] Neither the `_complete` pair nor any other incorrect Class-1 example appears in any authored text;
      the `_decides` pair is used wherever the mechanism is explained.

## Artifacts & Outputs

- `scripts/AxiomCensus.lean` (new)
- `scripts/check-axiom-census.sh` (new)
- `scripts/axiom-census-baseline.txt` (new, 43 rows)
- `scripts/check-sorry-suppressions.sh` (new)
- `scripts/sorry-suppression-baseline.txt` (new, 9 rows + ledger comments)
- `.github/workflows/lean_action_ci.yml` (modified: two steps + comment block)
- `scripts/pre-pr-check.sh` (modified: steps 8/9)
- `scripts/README.md` (modified: two entries)
- `specs/581_sorry_axiom_honesty_gates/summaries/01_sorry-axiom-honesty-gates-summary.md`

## Rollback/Contingency

- Every deliverable except three files is a **new** file; rollback is `rm` of the new files. The three
  modified files (`lean_action_ci.yml`, `pre-pr-check.sh`, `README.md`) receive purely additive hunks
  that can be removed by hand.
- No `.lean` file under `Cslib/` is touched, so there is no proof-state to roll back and no rebuild is
  required to recover.
- If Phase 1's census cannot be made to reproduce `tainted=43`, stop before Phase 2 rather than
  baselining an unverified number — an unverified baseline is worse than no gate, because it manufactures
  false confidence. Report the discrepancy and treat it as a blocker.
- If Phase 6 reveals a gate that cannot be made to exit 1 on a real regression, that gate is not done;
  do not wire it into CI and do not claim the definition of done.
- Before any intentional rollback on a dirty tree, run `bash .claude/scripts/git-snapshot.sh 581` first.
  Never use `git checkout -- <path>` or `git restore <path>` to undo Phase 6 test mutations — use the
  `.bak`/`mv` and `rm` mechanics specified in that phase.
