# Repo Lint & Hygiene Cleanup — CI Gate Restoration

- **Task**: 575
- **Status**: PARTIAL
- **Effort**: ~6h spent; ~5-8h remaining (Phase 3's big files and Phase 5 dominate)
- **Dependencies**: none blocking. Coordinate with 557/558 (Modal/Tableau refactor) before large
  edits to `Modal/Tableau/`; coordinate with 317 before edits to `Propositional/Tableau/`.
- **Research Inputs**: four parallel subsystem reviews (Propositional, Modal, Temporal/Bimodal,
  shared infrastructure) conducted 2026-07-27; findings inlined below rather than filed as
  separate reports.
- **Artifacts**: `plans/01_lint-hygiene-ci-gate.md` (this file);
  `remaining-warnings.txt` (historical W1 worklist, now exhausted)
- **Standards**: `.claude/rules/no-task-references-in-deliverables.md`,
  `.claude/rules/git-workflow.md` (commit-per-green-substep), `CONTRIBUTING.md`
- **Type**: cslib
- **Created**: 2026-07-27
- **Last updated**: 2026-07-27

---

## RESUME HERE

Third resume. Status as of this pass: **Phase 1, 2, 6, 8 COMPLETED; Phase 3 and 7 PARTIAL;
Phase 4 and 5 NOT STARTED.** To pick this up cold:

1. Confirm the baseline still holds (2 commands, ~5 min):
   ```bash
   lake build --wfail --iofail   # expect exit 1 with EXACTLY 5 warnings, all "declaration uses sorry"
   lake test                     # expect exit 0, 0 errors
   ```
   If either differs, something landed from another session — reconcile before proceeding.
2. **Phase 8 is now CLOSED** (9/10 rows, 1 excluded by finding — see the phase section for the
   full resolution of the wrapper/lemma rows and why the aggregator-modules row is excluded, not
   deferred). No further action needed on Phase 8.
3. Continue **Phase 3** (task-number references). The census regex now catches both `task N` and
   `task-N` forms with an optional letter suffix (see the phase section) — **use it, not the
   plan's historical figures, which predate the fix**. 26 files are done across four dispatches
   (399 -> 359 sites live count). The worst-offender files (`Intuitionistic/Scheme.lean` 94,
   `LoopChecking.lean` 51, `Nested/Soundness.lean` 28, `ChronicleToCountermodel.lean` 22,
   `Temporal/Tableau/Completeness.lean` 19, plus several more at 8-17) dominate the remaining 359
   and were deliberately left for a dispatch with a larger budget — each requires reading real
   mathematical context per site, not mechanical substitution. **Do not touch
   `Modal/Tableau/FrameSoundness.lean`'s 9 sites without first checking whether task 553 is still
   active** — see the explicit skip note in the phase section.
4. Phase 7 has 2 of 3 items done (`pre-pr-check.sh`, the `LoopChecking.lean` stale census). The
   `ORGANISATION.md` refresh and the `NOTATION.md` `S`->`Sys` rename (24 files in
   `Foundations/Logic/`, 231 named-argument call sites across 18 files — see the Phase 7
   re-scoping finding) were not attempted; the rename is Tier 4/atomic and must not be started
   unless a dispatch can finish it in one shot.
5. Phase 4 (shake) and Phase 5 (suppression audit, 18 of ~570 done) are both still essentially
   untouched and independent of Phase 3/7; any order works among all of these.
6. Two items still need a **user decision before work starts** — see "Open decisions" at the
   bottom (the Chronicle namespace/structure coincidence, item 3, was addressed by an explicit
   user decision: Phase 2 is CLOSED at 7/10 files, and the coincidence itself is routed to a
   separate follow-up task rather than blocking this one further).

**Do not** re-derive the sorry census with a naive grep. Use the method in "Measurement notes".
**Do not** re-derive the task-tracker-reference census with the old, letter-suffix/hyphen-blind
regex — use the fixed one in the Phase 3 section.

---

## Overview

Restore `lake build --wfail --iofail` — the exact CI invocation in
`.github/workflows/lean_action_ci.yml` — to green, and clear the hygiene debt surfaced alongside
it. `--wfail` promotes every warning to a build failure, so at task start CI was red despite
`lake build` and `lake test` both being green.

## Goals & Non-Goals

**Goals**: zero linter warnings; zero task-tracker references in deliverables; import gate
re-enabled; suppression debt audited and reduced; scripts that can actually fail.

**Non-Goals**:
- Discharging any `sorry`. Four files legitimately retain sorries and WILL still be CI-red at task
  end. That is the correct end state; clearing them is mathematical work owned by tasks 317 and
  553/557.
- Any structural consolidation requiring mathematics — see "Routed elsewhere".

## Constraints

- **No sorry may be discharged, added, moved, or suppressed.**
- **No proof term, definition, or theorem statement may be altered.** Only tactic surface syntax
  (`simp [X] at h` -> `simp only [...] at h`).
- **No new `set_option linter.* false`.** Suppressing instead of fixing is the pattern Phase 5
  exists to reverse. If a warning cannot be fixed without changing mathematics, report it.
- Verification protocol (user decision, revised): **risk-tiered batch verification** — see
  "Testing & Validation". Nothing is ever committed unverified; what changed is the *granularity*
  of verification, not its strictness. The superseded rule was "rebuild after each file, commit
  only when green", which ran all four gates (including the 9,253-test `lake test`) against 672
  modules to validate edits that frequently could not affect elaboration at all.

### Explicit non-targets — do NOT "clean" these

Each was investigated and found correct. Re-investigating wastes a cycle.

- `Temporal/Metalogic/PropositionalHelpers.lean` and `Bimodal/Theorems/Perpetuity/Helpers.lean`
  are **not** redundant wrappers. Their aliases carry 187 and 416 call sites (`impTrans` alone:
  47 and 96). They absorb `@`-positional boilerplate once instead of at every call site.
- `TemporalConservativity.lean:245`'s "sorry-free" claim is **true**. It scopes to two
  declarations that both verify axiom-clean; line 243 names the sorry'd one as the gap.
- The three `Chronicle` modules' `Chronicle.` prefix is **not** a doubled namespace — see Phase 2.

---

## Baseline and current state

| Gate | At task start | Now |
|------|--------------|-----|
| `lake build` | green 3259/3259 | green |
| `lake test` | green, 0 errors | green, 0 errors |
| `lake build --wfail --iofail` | **exit 1**, 27 modules, 460 warnings | **exit 1**, 4 modules, **5 warnings — all genuine sorries** |
| `lake exe mk_all --check` | pass | pass |
| `lake exe checkInitImports` | pass | pass |
| `lake shake` | 94 files flagged (CI step disabled) | unchanged |
| Linter sites | 240 | **0** |
| `set_option linter.*` | 511 | 482 |
| `@[nolint]` | 118 | 88 |
| Task-tracker refs in `Cslib/**` | 376 (undercounted; see Phase 3 census-regex fix) | 359 (399 by the corrected regex, minus 40 sites across 19 files fixed this session) |
| Doubled public names | 6 cross-module leaks | **0** |
| Bare sorries (correct method) | 28 | 28 (unchanged by design) |

The 5 remaining warnings, which are the correct end state:
```
Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1253            declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:568    declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:2580   declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:124  declaration uses `sorry`
Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:118     declaration uses `sorry`
```

### Measurement notes — two independent causes of this repo's recurring sorry-count error

Any future census must account for both, or it will be wrong again.

1. `set_option warn.sorry false` contains `sorry` at a word boundary, so a naive `\bsorry\b` scan
   counts 12 option lines as proof holes. This inflated Bimodal 23 -> 35.
2. Nine tracked scratch files at the repo root (8 `Test_*.lean` + `OF`) carried 15 sorries while
   belonging to no build target — invisible to `lake build`, counted by every grep. Removed in
   `2f608bdf`.

The project's own "41 -> 40" figures were wrong in both ways. Correct method: strip `/- -/` and
`--` comments, exclude lines containing `warn.sorry`, scan only build-reachable files.

---

## Implementation Phases

### Phase 1: Linter sites [COMPLETED]

240 distinct source sites across 27 files (460 raw warnings; one recurring flexible-simp pattern
accounted for 241 warnings at only 42 sites). Cleared in 23 individually-verified commits
(`1475b0a4` … `a4cdbe64`).

Fix recipes used, for reference if warnings reappear:
- "simp argument is unused" -> delete the argument from the `simp only [...]` list
- "flexible tactic modifying h" -> `simp [args] at h` becomes `simp only [<explicit>] at h`;
  get the explicit list from `simp?` via `lean_multi_attempt`, never by guessing
- "does not use the following hypothesis in its type" -> rename binder to `_name`; do not delete
- "section variable(s) unused" -> `omit ... in` before the theorem, matching file convention
- "`show` should only indicate intermediate goal states" -> replace `show` with `change`
- unnecessary `simpa` -> prefer `exact <lemma>` over bare `simp`, to keep the citation

Fixing warnings cascades: four extra files (FiveSimplification, TDriver, BDriver,
FrameCompleteness) surfaced new warnings only after earlier fixes landed. Expect this and re-run
the gate after each batch.

### Phase 2: Doubled-namespace public API [COMPLETED]

**Done** (30 declarations, commits `f60f9a74` … `6196b01e`): MetricSoundness (1), Bimodal
Core/DerivationTree (2), Temporal Metalogic/DerivationTree (2), MCS (2), DenseMCS (4), Temporal
ProofSystem/Derivable (9), Bimodal ProofSystem/Derivable (10), plus 2 vestigial suppressions in
the two `ProofSystem/Axioms.lean`. 42 of 78 `dupNamespace` suppressions deleted. All 6
cross-module leaks (`Cslib.Logic.Temporal.Temporal.ThDerivable` and friends) eliminated.

**The three `Chronicle` modules are OUT OF SCOPE by finding, not an incomplete step** — the
original diagnosis that flagged them was WRONG, and re-scoping to exclude them is what closes
this phase correctly. Do not retry as a mechanical rename, and do not attempt the
structure/namespace rename either — both alter definitions and are barred by this task's
hygiene-only constraint. The three `Chronicle` modules' `Chronicle.` prefix is not a repeated
namespace component; it is the *structure* name. `namespace ...Metalogic.Chronicle` contains
`structure Chronicle`, so `def Chronicle.c0` correctly declares the projection-namespace member
that 81 dot-notation call sites (`chi.c0`, `chi.c3`, …) depend on. Stripping it fails with
`Invalid field 'c0': the environment does not contain ...Chronicle.Chronicle.c0`. The 7 files
completed above were the ones that genuinely had doubled namespaces — Phase 2 achieved
everything that was actually in its remit.

The genuine residual defect is the `namespace Chronicle` / `structure Chronicle` name
coincidence. Fixing it means moving the structure to the parent namespace, or renaming the
namespace across the whole `Chronicle/` subtree — a design decision, out of scope for this
hygiene-only task. It is being carried by task 576, which depends on task 568 (the Chronicle
architecture question) so the naming decision is not made twice. The remaining 36
suppressions (33 `@[nolint]`, 3 `set_option`) are **load-bearing** until task 576
makes the call. Files: `Temporal/Metalogic/Chronicle/ChronicleTypes.lean`,
`Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`,
`Foundations/Logic/Metalogic/Chronicle/Types.lean` (9 declarations each).

**Estimation lesson**: the original "~484 reference sites" was wrong by ~80x. The true count was
**6**. Short-form references (`Temporal.SetMaximalConsistent`, 289 occurrences) need no edit —
they resolve to the un-doubled name via the enclosing-namespace walk once the declaration loses
its doubled component. Only fully-qualified spellings break.

### Phase 3: Task-number references in deliverables [IN PROGRESS — 26 files done, 359 sites remain]

**The plan's original "312 sites" figure was stale — a fresh count came back 376, not 312 (cause
not diagnosed; treat the live grep as authoritative, not the plan's number, per this task's own
measurement-discipline lesson).** Violates `.claude/rules/no-task-references-in-deliverables.md`.
An earlier cleanup stripped ~918; these are a regression.

**Census regex fixed this session — two independent gaps closed.** The prior regex
(`\b(task|tasks|phase|report) [0-9]+(\.[0-9]+)?\b`) missed both a letter-suffix form (`Phase 3a`)
and a hyphenated form (`task-530`). The authoritative census is now:
```bash
grep -rnoiE '\b(task|tasks|phase|report)[ -][0-9]+[a-z]?(\.[0-9]+)?\b' Cslib --include='*.lean'
```
This finds 399 sites as of this session's start (up from the pre-session 376/368 figures, which
used the letter-suffix-blind regex) — the increase is measurement correction, not regression: no
new citations were introduced, the old regex simply undercounted. **Still not exhaustive**: a
`(522's ... + 523's ...)` bare-number form (no `task`/`phase` word) was found and fixed by reading
context, not regex; spot-check prose near any remaining hits for similar bare-number forms.

Sampling confirmed the `Phase N` / `report N` hits are task-tracker history ("Phase 6", "plan v3",
"report 08"), not mathematical algorithm phases. Spot-check before bulk-editing any file, since a
legitimate "Phase 3" could exist in an algorithm description.

**Done this session** (399 -> 359 sites; commits `5d52f96a`, `e39211bd`, `0374e921`, `64d6b209`),
19 files, all Tier 1 (comment/docstring-only, no code tokens touched):
- **6 Foundations/Temporal/Bimodal Chronicle-tree files** citing `task-530`'s internal phase
  numbering (Phase 0/1/2/3a/3b/4b): `ChronicleInterface.lean`,
  `CounterexampleElimination/Structures.lean` (Foundations), `Temporal/.../ChronicleTypes.lean`,
  `Bimodal/.../ChronicleTypes.lean`, `Foundations/.../RRelation.lean`, `Foundations/.../Types.lean`.
- **10 Modal metalogic family files** citing bare task numbers (494, 480, 496, 490, 501, 522) for
  a sibling scaffold file already named in the same docstring: `Intuitionistic/{IT,IS4,IS5,IK}`,
  `Minimal/{MT,MS4,MS5,MK}`, `Constructive/CT`, `SchemaSoundness`. Anchor pattern: replace the
  task number with the actual scaffold filename (`Extension.lean`, `MinExtension.lean`,
  `CKExtension.lean`, etc.) — the file that defines the referenced construction.
- **3 more Bimodal Chronicle-tree files** (`RRelation.lean`,
  `CounterexampleElimination/{Structures,BurgessHelpers}.lean`) citing `task-530`/`task 113`/
  `task 107`; the latter two describe a withdrawn lemma — replaced with *why* it was withdrawn
  (false under strict Until semantics) rather than which task found that out.
- **`Bimodal/Metalogic/Bundle/SuccRelation.lean`**: 7 `warn.sorry`-suppressed sorries (not part of
  the 5-warning CI baseline) each carried a `-- sorry: blocked on task 37` trailing comment.
  Traced task 37 in `specs/state.json`: still-blocked `port_continuous_completeness_bimodal`,
  genuinely blocked on BimodalLogic's `FrameClass` lacking a `Continuous` constructor. Replaced
  with that technical reason. **Only the trailing comment was edited on each `sorry` line — the
  `sorry` tactic itself was verified untouched via `git diff` before commit**, satisfying the
  no-sorry-relocated constraint.

Common durable-anchor pattern used repo-wide for `task 36` sites (not touched further this
session — already established by the prior session): task 36 is
`port_discrete_completeness_bimodal`, the not-yet-ported WeakCanonical discrete-completeness
infrastructure — replace `task 36` with "the WeakCanonical discrete-completeness port"
(`ChronicleToCountermodel.lean` alone still has ~10 such mentions untouched).

**Deliberately skipped this session — do not touch without re-checking task 553's live status**:
`Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (9 sites, "Phase 2"/"task 553"). Its citations
sit directly inside the module comment and docstring documenting the file's own `[BLOCKED]`
`sorry` at line 1253 (one of the 5 baseline CI-red warnings), including a direct path reference
to `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/03_ancestor-only-blocking.md`.
Task 553 has its own live task directory with an `.orchestrator-loop-guard` file present in this
repo as of this session (i.e. plausibly concurrently active). Editing this exact prose risks
colliding with that task's own in-progress analysis of the same unresolved sorry. Recommend
re-checking task 553's status in `specs/state.json` before touching this file; if it is no longer
active, the durable-anchor fix is straightforward (the technical argument is already fully
inline in the comment — the specs/ path citation is redundant with it and can simply be dropped).

Worst files remaining (recount before continuing — these are post-session live counts, not
pre-session estimates): `Intuitionistic/Scheme.lean` (94), `Modal/Tableau/LoopChecking.lean` (51),
`Constructive/Nested/Soundness.lean` (28), `ChronicleToCountermodel.lean` (22),
`Temporal/Tableau/Completeness.lean` (19), `Intuitionistic/Expansion.lean` (17),
`Intuitionistic/Completeness.lean` (15), `Constructive/Nested/Rules.lean` (12),
`Constructive/CS5Completeness.lean` (10), `Computability/Languages/OmegaRegularLanguage.lean` (10),
`Modal/Tableau/FrameSoundness.lean` (9, see skip note above),
`Minimal/Completeness.lean` (8), `Constructive/Nested/Context.lean` (8),
`Constructive/Labelled/Soundness.lean` (8). None of these were started this session; they dominate
the remaining 359 sites and require real per-site reading (per this phase's own caution), not
mechanical substitution — budget the next dispatch accordingly.

Replace each with a durable anchor — sibling filename, section heading, or verified fact. **Never
delete the surrounding explanation**; the prose is usually load-bearing, only the identifier rots.

### Phase 4: Import gate (`lake shake`) [NOT STARTED]

Commented out at `.github/workflows/lean_action_ci.yml:29-32`.

**Do not naively re-enable.** ~77% of flagged removals are a redundant `import Cslib.Init`; only
**~24 are genuine** unused module imports, clustered in Tableau code. For every flagged file
another `Cslib.*` import carries `Cslib.Init` transitively, so `checkInitImports` would not break
— but the churn diff would be large and valueless.

Correct sequence: configure shake to always keep `Cslib.Init`, fix the ~24 genuine imports, then
uncomment the CI step.

Reconcile counts first — two runs disagreed: 94 files / 91 removes / 19 adds versus
92 / 106 / 36. Likely flag or version drift; resolve before acting.

### Phase 5: Suppression audit [PARTIAL — 18 of ~570 done]

**Done**: 18 provably-vestigial deletions (`37046110`) — 14 `longLine` in files with no line over
100 chars, 4 `setOption` whose only effect was silencing themselves. Rebuild produced zero new
warnings, confirming they suppressed nothing.

**Structural finding**: 464 of the original 511 were *file-scoped blanket* suppressions; only 47
declaration-scoped. A blanket suppression atop a 2,000-line file silences every *future* violation
too — coverage accumulates rather than decaying. Suppression density also tracks incompleteness:
`Separation/` and `CounterexampleElimination/` dominate the worst-offender list and are the same
areas carrying the sorries.

| Category | Count | Verdict |
|---|---|---|
| Pure style (emptyLine 103, longLine 89, setOption 68, show 18, openClassical 7, maxHeartbeats 3) | 288 | Not justified; no mathematics needed. **Best next target.** |
| Correctness-adjacent (flexible 68, unusedSimpArgs 43, unusedDecidableInType 30, unusedSectionVars 21, dupNamespace 15, unusedVariables 7, unusedTactic 2, privateModule 2) | 188 | Mixed; assess per site |
| `tacticAnalysis.verifyGrindOnly` | 35 | **Justified and correctly scoped — leave alone** |

Of the 118 `@[nolint]`: `dupNamespace` 60 (Phase 2 territory), `unusedArguments` 40 (plausible —
uniform signatures across a lemma family often carry arguments a given case ignores; no evidence
against them found), `docBlame` 15, singletons 3.

Worst offenders: `Separation/DedekindZ/Cases.lean` (12),
`CounterexampleElimination/Elimination.lean` (8), then several at 6-7.

**Method**: remove, rebuild, fix whatever surfaces. Only removal-plus-rebuild proves whether a
suppression is load-bearing.

### Phase 6: Sorry visibility [COMPLETED]

- `ChronicleToCountermodel.lean:46` was the **only file-scoped `warn.sorry` in the repo** (the
  other 11 use `... in` and bind one declaration). It was appended to a block of style
  suppressions and matched their form — correct for linters, wrong for a soundness signal.
  **DONE** (commit `607b92f4`): split into 7 declaration-scoped `set_option warn.sorry false in`
  forms, one per sorry-bearing declaration (`chronicle_gap_contradiction`, `discreteFmcs`,
  `succEmbed`, `rootedSuccDiscreteFmcs`, `rooted_succ_discrete_fmcs_at_s`,
  `cantorBfmcsDiscrete`, `dd_countermodel_chronicle_discrete`) — this covers all 12 sorry tokens
  in the file (two of the seven declarations are structures with multiple sorry'd fields). No
  suppression was removed; the blast radius was narrowed from file-wide to declaration-scoped,
  matching the other 11 `warn.sorry` sites repo-wide. Build unaffected (still exactly the 5
  baseline warnings under `--wfail --iofail`).
- All 12 `warn.sorry` suppressions repo-wide are in Bimodal; Propositional's 4 and Modal's 1 are
  unsuppressed and do surface. Measured asymmetry: `Minimal.Completeness` exits 1 under `--wfail`
  while `Bundle.UntilSinceCoherence` (2 suppressed sorries) exits 0. (Measurement note only, no
  action item.)

### Phase 7: Script and documentation defects [PARTIAL — 2 of 3 items done]

- **`scripts/pre-pr-check.sh:5-26` cannot fail.** **DONE** (commit `7be1fd61`): accumulated a
  `failed` flag across all 5 steps (added a step 5 running `lake build --wfail --iofail`) and
  `exit 1` at the end if any failed; sorry check now strips block/line comments and excludes
  `warn.sorry`-mentioning lines (verified this reproduces Bimodal's true 23-sorry census); debug
  grep now anchors `#check`/`#eval`/`dbg_trace` to line starts, eliminating the 4 docstring false
  positives at `S5Simplification.lean:1963,1966,1970` and `LoopChecking.lean:7178`.
- **`LoopChecking.lean:160-161`** asserted "Repo-wide: 11 TODO:, 8 NOTE:", both wrong and
  self-referentially incoherent (the two asserting lines themselves contain the literal strings
  `NOTE:`/`TODO:`, so they were always among whatever count was correct). **DONE** (commit
  `2fc441a0`): deleted the two-line assertion rather than correcting the numbers, per the plan's
  own guidance that a hardcoded repo-wide census on a comment line will go stale again.
- **`ORGANISATION.md` stale by ~100 files.** NOT STARTED. Every claimed path exists (no
  phantoms); the failure is omission. Modal lists `Metalogic/` as 5 files; reality is 94
  undocumented across `Systems/` (45), `Constructive/` (24), `InterSystem/` (10),
  `Intuitionistic/` (9), `Minimal/` (6). Temporal's `Tableau/` (8 files) absent entirely. The
  `Foundations/Logic/Tableau/` entries ARE current and correct. Consider a CI check diffing
  sketch against filesystem — at this drift rate a hand-maintained census will go stale again.
- **`NOTATION.md` has no logic section**, for a tree that is ~450 of 676 files. NOT STARTED.
  Concrete cost: `Foundations` names its proof-system type parameter `S`, colliding with
  Temporal/Bimodal scoped notation `S` for *Since*, forcing `@`-positional application in 5
  files. Documented five times in `NOTE:` blocks, fixed zero times. Fix: rename `S` -> `Sys` in
  `Foundations/Logic/`, delete the 5 NOTE blocks, add a scoped-notation rule to NOTATION.md.
  (`ORGANISATION.md` and the `S`->`Sys` rename are grouped as one remaining item since neither
  was started this session; treat them as two independent sub-steps when resumed.)

  **Re-scoping finding (this session, investigation only, zero files edited)**: the "5 files"
  framing understates the true footprint. `S` is the bound `Type*` parameter on `InferenceSystem`
  (`Foundations/Logic/InferenceSystem.lean`) and is threaded through **24 files** under
  `Foundations/Logic/**` (`ProofSystem.lean` alone has 177 bare-`S` tokens; `Theorems/
  DerivationCombinators.lean` 96; `Theorems/Modal/S5.lean` 84; `Metalogic/PrimeExclusion.lean` 66;
  `Theorems/Temporal/TemporalDerived.lean` 64; `Metalogic/Consistency.lean` 61;
  `Theorems/Combinators.lean` 60 — the rest smaller). Named-argument call sites `(S := ...)` that
  would need to become `(Sys := ...)` for the rename to typecheck number **231 across 18 files**
  (13 inside `Foundations/Logic/`, plus the 5 real downstream consumers: the two Bimodal
  `Theorems/Propositional/*` files, the two Temporal `Metalogic/*` files named in the NOTE blocks,
  and `Modal/Metalogic/InterSystem/IntToClassical.lean`, which has 62 more occurrences on its own
  despite carrying no NOTE — it uses named args for the same tag with no collision to explain).
  One superficially-matching file, `LinearLogic/CLL/PhaseSemantics/Basic.lean`, is a **false
  positive**: its `(S := ...)` binds an unrelated `S : Set (Fact P)` local variable, not this
  tag — confirmed by reading `sInf_isFact`/`carriersInf` — and must NOT be touched.

  Because `InferenceSystem.lean`/`ProofSystem.lean` sit at the root of the logic dependency graph,
  this is not choppable into independently-green single-file commits the way the rest of this
  task has been: a binder rename only typechecks once every one of the ~18 named-argument-using
  files is updated in the same atomic change, and verifying it means a near-full-project rebuild
  (this module tree feeds nearly everything under `Cslib/Logics/`), not the fast scoped builds
  every other Phase 7/8 item used. That cost profile is disproportionate to a "rename an
  identifier" item inside a hygiene task that otherwise verifies per-file in seconds. Recommend
  either: (a) a dedicated follow-up task sized for one atomic ~18-file commit with a single
  full-project rebuild budgeted in, or (b) if attempted inside this task, doing it as the very
  last action before Definition-of-Done sign-off, in one shot, specifically so a failed attempt
  doesn't cost repeated full rebuilds against an otherwise-finished plan. Not attempted this
  session for exactly that reason — investigation only (`grep`/`Read`), zero `.lean` edits, zero
  `lake build` invocations spent on it.

### Phase 8: Dead-code deletions [COMPLETED — 9/10 rows done, 1 excluded by finding]

User-approved in full.

| Target | Lines | Status | Evidence |
|---|---|---|---|
| 9 root scratch files | — | **DONE** `2f608bdf` | In no build target; 15 phantom sorries |
| `KripkeBridge.lean` | 296 | **DONE** `154fa5ea` | All 6 exports: 0 external refs |
| `Bridge.lean` | 133 | **DONE** `99834bc0` | Self-documents "no in-tree consumer"; 1 hit is a docstring |
| `CanAlgComplete` + `FragmentGeneric` | 333 | **DONE** `f72b3393` | 0 term-level consumers; also patched 4 sibling docstrings' dangling `CanAlgComplete` mentions |
| 9 zero-declaration aggregator modules | 238 | **EXCLUDED — false-positive risk confirmed, see note below** | re-derivation found every remaining candidate is genuine, documented architecture |
| 7 dead MCS-transfer wrappers | ~50 | **DONE** `24435820` | Identified precisely as `*_setConsistent_iff_algebraic`/`*_setMaxConsistent_iff_algebraic`; each had exactly 2 repo-wide occurrences (own docstring bullet + declaration); 8th (`temporal_setMaxConsistent_iff_algebraic`) has 6 external call sites in `Temporal/Metalogic/MCS.lean` — kept |
| `Theory.Derivation.normalize` + `normalizeAux` | ~25 | **DONE** `24ba4d78` | 0 consumers, no correctness theorem; superseded by `Termination.lean`'s structural driver |
| 2 dead `GenericMCSBridge` lemmas | ~15 | **DONE** `24435820` (folded into the wrapper row) | 6 fully-dead `unfoldListImpInTree`/`unfoldListImpInTreeFc` defs (Modal, Propositional, Temporal x2, Bimodal x2) — see note below on the count discrepancy |
| `NativePropositionalEmbedding` | ~5 | **DONE** `4b57fd98` | Uninstantiated stub |
| `hilbertConjImpConservativeOverImp_direct` | ~4 | **DONE** `6de7be96` | Pure alias; `_direct` name is backwards |

**Resolution of the "7 dead MCS-transfer wrappers" and "2 dead GenericMCSBridge lemmas" rows**
(this session): neither row's stale figure named specific declarations, so both were re-derived
from scratch via full reference-count grepping of every `lemma`/`theorem`/`def` in the 4
`GenericMCSBridge.lean` files (Modal, Propositional, Temporal, Bimodal).

- **"7 dead MCS-transfer wrappers (8th has 6 refs)" — exact match found**: the 8
  `*_setConsistent_iff_algebraic`/`*_setMaxConsistent_iff_algebraic` theorems (2 per file,
  "MCS transfer" = transferring `SetConsistent`/`SetMaximalConsistent` status between the
  tree-based and algebraic derivation systems). 7 of the 8 had exactly 2 repo-wide occurrences
  (their own docstring bullet in the file header + their own declaration line) — i.e. truly
  zero consumers, not even within their own file. The 8th, `temporal_setMaxConsistent_iff_algebraic`,
  had exactly 8 occurrences = 2 baseline + **6** external call sites in
  `Cslib/Logics/Temporal/Metalogic/MCS.lean` — an exact match to the plan's "8th has 6 refs,
  keep it" note. Deleted the other 7; kept this one unchanged.
- **"2 dead GenericMCSBridge lemmas" — count could not be reproduced, but a real dead-code
  cluster was found and removed under the same evidentiary standard**: the actual zero-reference
  declarations besides the 7 above are 6 `noncomputable def`s, not 2 `lemma`s:
  `unfoldListImpInTree` (Modal, Propositional, Temporal, Bimodal) and `unfoldListImpInTreeFc`
  (Temporal, Bimodal). Each is a thin post-task-452-generalization delegator to
  `GenericMCS.unfoldListImp` (Foundations) that nothing calls — confirmed independently by
  `GenericMCS.lean`'s own docstring at its `unfoldListImp` definition: "Generic backward helper
  (was `unfoldListImpInTree` × 4)". Per this task's own measurement-discipline lesson (treat a
  live, reproducible count as authoritative over a stale plan figure), these 6 were deleted
  instead of searching further for a nonexistent "2 lemmas" reading. `derivTreeToList(Fc)` and
  `listDerivToTree(Fc)` in all 4 files were verified to have real callers (internal to build the
  `*_deriv_iff_algebraic(_fc)` theorems, or external via `Modal`/`Propositional`
  `DeductionTheorem.lean`) and were left untouched.
- Each file's "Main Results" docstring bullets and "Backward" architecture prose were updated to
  match (describing the direct `GenericMCS.listDerivToTree`/`GenericMCS.unfoldListImp` delegation
  in place of the removed local wrapper), per the never-delete-the-surrounding-explanation
  discipline used in Phase 3. Verified: all 4 files build individually, every affected
  reverse-dependency cone (`Modal`/`Propositional`/`Temporal`/`Bimodal` `DeductionTheorem.lean`,
  `Temporal/Metalogic/DenseMCS.lean`, `Temporal/Metalogic/MCS.lean`) builds clean, and a full
  `lake build Cslib` (3255 jobs) is green.

**Resolution of the "9 zero-declaration aggregator modules" row — EXCLUDED, not attempted,
false-positive risk confirmed a second time**: re-ran the zero-declaration search with a wider
declaration-keyword net than the prior session's pass (which only checked
`theorem|lemma|def|structure|inductive|instance|abbrev|class`) and cross-checked import
reverse-dependencies. Two independent problems ruled out this whole row:

1. **The naive scan itself produces false positives.** In addition to the prior session's
   confirmed false positive (`Automata/DA/Conversions.lean`, a documented `proof_wanted` stub),
   this session's tighter zero-*importer* pass surfaced a 7th zero-declaration/zero-importer
   candidate not in the prior session's set of 6:
   `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` (268 lines). Reading it confirmed it
   is a substantial, actively-used `hilbert_search` proof-search **tactic** implementation (a
   `public meta section` with `private def`, `initialize registerTraceClass`, and `elab`-family
   declarations) — none of which match the `theorem|lemma|def|...` keyword regex, so a purely
   syntactic "zero declarations" scan misclassifies real, load-bearing meta-code as an "empty
   aggregator". This is the second time (of two attempts, two sessions) a naive pass on this
   exact bucket has produced a false positive, which is itself evidence the detection method is
   unsound for this row, not just that individual files need spot-checking.
2. **The remaining 6 candidates are self-documented, deliberate architecture, not orphaned
   scaffolding.** Reading all 6 zero-declaration/zero-importer files
   (`Algebraic/Algebraic.lean`, `Bundle/Bundle.lean`, `Bundle/FMCS.lean`,
   `BXCanonical/BXCanonical.lean`, `BXCanonical/Completeness.lean`, plus the confirmed-dead-code
   exclusion `Automata/DA/Conversions.lean`) shows each carries an explicit comment or docstring
   naming its own purpose: `Algebraic.lean`/`Bundle.lean`/`BXCanonical.lean` are literally headed
   `-- Barrel import for .../ modules`, a deliberate convention (this repo's version of a
   directory barrel file that centralizes Mathlib attribute imports — e.g. `Finset.Attr`,
   `Finiteness.Attr`, `SetLike` — needed by tactics elsewhere in the same subtree) rather than
   accidental cruft; `Bundle/FMCS.lean` documents itself as "Re-export only; FMCS definition is
   in FMCSDef.lean"; `BXCanonical/Completeness.lean` documents planned future growth
   (`completeness_discrete`, `completeness`, pending the WeakCanonical port — the same finding
   the prior session already flagged as borderline). None of these read as "inert leftover
   scaffolding" once opened; they read as intentional (if currently under-wired, 0-importer)
   plumbing, which is the exact category this task's Open Decision 2 (the 620 dead lines in
   `Foundations/Logic/Metalogic/`) already routes to a design call rather than a hygiene
   deletion, not this task's remit.

Given (1) the detection method has now produced a confirmed false positive on two independent
attempts and (2) every surviving candidate self-documents as deliberate architecture, this row
is excluded from Phase 8 by finding — the same disposition Phase 2 used to close at 7/10. The
original "9 files, 238 lines" figure was never reproduced by either session and should be
treated as unreliable; if a future task wants to pursue this, it needs either the original
research artifact (not located) or a human design call on the barrel-file convention itself
(should these 5 genuine barrels be wired into their sibling files' imports, or removed
entirely?), which is out of scope for a hygiene-only task.

Deleting modules requires updating `Cslib.lean` and re-running `lake exe mk_all --module`.
This was not needed this session since only in-file declarations were removed, not files.

---

## Testing & Validation

**Principle**: verification granularity is matched to what an edit can actually break. The
strictness of the final gate is unchanged — every gate below still runs before the task is
declared done, and no commit ever contains unverified work. What changes is that a full-repo
build + 9,253-test suite no longer runs against 672 modules to validate an edit that cannot
affect elaboration.

### Two build commands, deliberately distinguished

| Command | Cost | When |
|---|---|---|
| `lake build Cslib.Path.To.Module` | rebuilds that module's cone only | **during** a phase, per batch |
| `lake build --wfail --iofail` | full repo, 672 modules | **phase boundary only** |

Most files touched by the remaining phases are near-leaves (Phase 3's six worst-offender files
have 0–2 reverse dependents each), so the targeted form is dramatically cheaper and is the
correct in-phase instrument.

### Risk tiers — assign every edit before making it

**When in doubt, use the higher tier.** Mis-assigning downward is the only way this protocol
can lose accuracy, so the tie-break is always upward.

| Tier | Edit class | Can it change elaboration? | Verification |
|---|---|---|---|
| 0 | Non-compiling files: `.md`, `.yml`, `.sh`, `.github/**` | No — Lean never reads them | No Lean build. `bash -n` for shell scripts; nothing for prose |
| 1 | Comment / docstring text only, no code tokens (Phase 3 citations) | No | Batch freely; **one targeted build per batch** |
| 2 | Deletion of dead code (Phase 8) | Only via dangling reference, which the compiler names exactly | `grep` for references first, then batch-delete + one targeted build over affected reverse-deps |
| 3 | Import edits (Phase 4 shake) | Only via missing/unused import, precisely reported | Batch per directory + targeted build; re-run `lake shake` once at phase end |
| 4 | Tactic-surface rewrites, suppression removal (Phase 5) | **Yes — genuinely proof-affecting** | Small batches of *mutually independent* modules; targeted build per batch |

Tier 1's only realistic failure mode is a malformed comment delimiter or an accidental edit
inside a string literal. Both are syntactic, both are caught by any build of that module, and
both are localized by the error message — so per-file granularity buys nothing a per-batch build
does not already give.

### On failure

The compiler names the file and line; fix it directly. Only if a failure is genuinely ambiguous
across a batch, bisect the batch. Expected cost is one build per batch, with a `log(batch)`
penalty on the rare failure — versus one build per file unconditionally.

### Phase-boundary gate (unchanged in strictness)

All four, at every phase boundary and before declaring the task done:

```bash
lake build --wfail --iofail   # must show ONLY the 5 sorry warnings listed above
lake test                     # exit 0, 0 errors
lake exe mk_all --check
lake exe checkInitImports
```

### Commit granularity

Commit per verified-green **batch**, not per file. This still satisfies
`.claude/rules/git-workflow.md`'s commit-per-green-substep mandate: a sub-step is a
progress-file objective reaching `done`, and `files_touched` explicitly accumulates across
multiple files, so a batch is a legitimate sub-step. "Green" still means the batch's own
verification criteria passed. Unverified work remains uncommittable.

## Definition of Done

- `lake build --wfail --iofail` reports no warning other than the 5 genuine sorries. **[MET]**
- `lake test` green, 0 errors. **[MET]**
- Zero `task N` / `Phase N` / `report N` strings in `Cslib/**`.
- `lake shake` clean and its CI step uncommented.
- Suppression audit outcome recorded per site.
- `pre-pr-check.sh` can actually fail. **[MET]**

## Rollback / Contingency

Every commit is verified green before landing, so `git revert <sha>` is safe. Under the
risk-tiered protocol a commit covers a verified batch rather than a single file, so a revert
restores that batch — keep batches to one tier and one phase so a revert stays semantically
clean. No commit in this task alters mathematics, so a revert can never reintroduce a proof
gap — worst case it reintroduces a warning.

If a Phase 5 suppression removal surfaces warnings that cannot be fixed without changing a proof:
restore the suppression, but convert it from file-scoped to declaration-scoped (`... in`) and
record why. Do not leave a blanket suppression in place as the resolution.

---

## Open decisions (blocking, need the user)

1. **`#print axioms` gate — recommend a separate task.** `succ_cofinal`
   (`ChronicleToCountermodel.lean:78`) and `limitDomSubtypeIsSuccArchimedean` (`:87`) consume a
   sorry'd lemma, contain no `sorry` token, emit no warning, and carry docstrings giving no
   warning. Both verify `sorryAx`-contaminated. `bimodal_conservative_over_temporal` (`:289`) is
   contaminated the same way with prose-only disclosure. **No `warn.sorry` policy however strict
   catches this class** — the declarations are clean by every syntactic measure. A `#print axioms`
   gate over the public API is the only mechanism that does. `IsSuccArchimedean` is a
   Mathlib-facing structural property, so a vacuous instance is the worst-shaped version of this.
   This is correctness, not hygiene, and is out of scope for 575.
2. **620 dead lines in `Foundations/Logic/Metalogic/`** — `ProofSystemMorphism` (317),
   `DeductionCharacterization` (159), `SetDeduction` (144). Imported only by the root barrel.
   User deferred deletion: they are plausibly the *right* abstraction that never got adopted —
   `SetDeduction` in particular duplicates functionality Modal/Temporal/Bimodal each solved
   locally. Needs a design call: wire up or delete.
3. **The `Chronicle` namespace/structure name coincidence** (Phase 2) — move the structure to the
   parent namespace, or rename the namespace across the subtree? Out of scope for this
   hygiene-only task; carried by task 576, which depends on task 568. Until decided, 36
   suppressions stay.

---

## Routed elsewhere (needs mathematics — not this task)

Recorded from the four subsystem reviews for the owning tasks:

- **Bimodal Chronicle tree is a wholesale fork of the Temporal one** — 250 of 305 declarations
  shared, `ChronicleConstruction.lean` at 63% line identity. **Task 41 looks under-scoped** if
  framed as extracting a few shared lemmas; this is a merge. Suggested seam: the `ChronicleInterface`
  instance family already in both `ChronicleTypes.lean` files.
- **`GenericMCSBridge.lean` exists 4 times** (845 lines). Falls between task 393 (Lindenbaum) and
  task 41 — neither names it. Needs an ownership call.
- **Three classical-fragment completeness files**: 1,388 lines of one copy-pasted Kalmár skeleton;
  `litCtx_congr` byte-identical across two. (The `litCtx_congr` triplication and the dead
  `Proposition.atoms` are hygiene-only and could fold into 575 if desired.)
- **`IntDecidability`/`MinDecidability`**: 942 lines of 1:1 parallel proof, in a directory where
  `GenericLindenbaum.lean` already establishes the axiom-parameterized-substrate idiom.
- **LTL remains an island**: 2742 lines, 0 sorries, a real proved semantic bridge
  (`EmbeddingSemantics.lean:96,148`), and no consumer. A bridge load-bearing for nothing can rot
  silently.
- **CPL decidability gap**: IPL and MPL have `Fintype`-free tableau `Decidable` instances for
  `Derivable`; CPL has none, purely by omission.
- **Task 317 scope note**: `Tableau/Minimal/Completeness.lean` is a near-line-for-line copy of
  `Tableau/Intuitionistic/Completeness.lean`, one sorry each. Discharging both independently bakes
  the duplication in permanently; make them one bot-forcing-parameterized result **first**.
- **Task 413 sequencing**: it targets proof simplification, but `simp only` cleanup across
  triplicated proof is wasted if the triplication is then removed. Sequence 413 after the
  consolidations above.
- **Test coverage**: the entire metalogic layer has zero executable regression tests.
  `Foundations/Logic/Tableau` (8 files, consumed by three logics) is the highest value-per-line
  gap — a defect in the shared closure condition propagates into every calculus uncaught.
- **Docstring claim inflation**: `HilbertCompleteness.lean:95-97` claims "20+ use-sites"; real
  term-level count is 9, five of which are inside the dead `CanAlgComplete`.
