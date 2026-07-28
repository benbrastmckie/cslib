# Research Report: sorry/axiom honesty gates (task 581)

## Summary

Both gates are feasible as pure-ratchet, zero-debt-compliant scripts. The whole-`Cslib`-root-import
approach for the axiom census is decisively cheap (~2.7s), not the 20-minute worry the scope
raised. The sorry-suppression discrimination rule works and its true code-position count (28)
independently cross-validates against a figure already recorded by task 575. Two things need an
explicit decision before planning: (D) the task-number-in-baseline requirement conflicts with
`.claude/rules/no-task-references-in-deliverables.md`, and (new, found during verification) the
scope's "wire into `lean_action_ci.yml`" instruction conflicts with this repo's own established,
twice-applied precedent of keeping build-dependent/new local ratchet gates *out* of that specific
shared/upstream-synced file, and that workflow's build step is *currently red by design* on this
tree (task 575's own definition-of-done accepts this), which affects how new steps there would
even execute.

## A. Axiom-census enumeration cost — MEASURED

**Method used**: a single Lean script that does `import Cslib` (loading the whole environment
once, reusing cached `.olean`s — no recompilation needed since the tree is already built), then
walks `env.constants`, filters to non-internal `Cslib.*` constants of kind `.thmInfo | .defnInfo |
.opaqueInfo`, and calls the **builtin** `Lean.collectAxioms` (from `Lean.Util.CollectAxioms`,
already `public import`ed by `Lean` itself) per declaration. This is the canonical mechanism —
it is literally what backs `#print axioms` and what Lean's own per-module axiom-export cache
(`exportedAxiomsExt`) uses; there is no need to hand-roll a dependency walker (an artifact from an
unrelated earlier session's scratchpad, `Census.lean`/`Census2.lean`, had already hand-rolled one
via `env.find?` + `getUsedConstants` recursion before this builtin was noticed — the builtin is
strictly better: it is cached across declarations via `exportedAxiomsExt`, sorted, and exactly
matches `#print axioms`'s own semantics).

Driven via `lake env lean --run scripts/<Script>.lean` (interpreted, no `lean_exe` needed, though
registering as a `[[lean_exe]]` — the `CheckInitImports.lean` precedent — is also viable and would
let it run as a compiled binary during `lake build`; either works, see recommendation below).

**Measured timing** (3 runs, warm `.olean` cache, this machine):
```
run 1: 2737 ms
run 2: 2678 ms
run 3: 2697 ms
```
~2.7s wall-clock for a full census of the entire `Cslib` public surface.

**Per-module (separate-process) alternative — measured and rejected**: timed two representative
single-file imports (`Cslib.Foundations.Data.HasFresh`, a shallow leaf, and
`Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleToCountermodel`, a deep one):
both took **~1.4-1.5s each**, because process-startup + transitive-import elaboration cost is paid
fresh by `lake env lean --run` on every invocation regardless of which file is targeted (loading
Mathlib's dependency graph dominates). `Cslib/` has **686** `.lean` files. A "spawn one process per
module" design costs `686 × ~1.45s ≈ 16-17 minutes` at minimum — **~370x slower** than the
whole-root-import approach, for no accuracy benefit (per-module invocation still needs the same
transitive closure loaded per process; it does not shrink the actual elaboration work, it just
repeats the fixed environment-loading cost 686 times).

**Recommendation**: whole-`Cslib`-root-import, single process, using `Lean.collectAxioms`. Report
this as decisive — no further exploration of per-module designs is needed.

**"Public API surface" — enumeration mechanism, and a discovered subtlety**: every file in this
tree already declares `module` (Lean 4's new module system) with `public import`/`private import`
distinctions and `@[expose] public section` blocks (confirmed: `grep -c '^module' $(find Cslib
-name '*.lean')` is nonzero in all 686 files). The technically-correct way to restrict to the
*exported* (public) surface is `env.setExporting true` then `(exportedEnv.find? n).isSome)` —
this is exactly what `Lean.Util.CollectAxioms`'s own `exportedAxiomsExt.exportEntriesFnEx` does
internally. I implemented and tested this filter (`Census3.lean` in scratch): it produced the
**exact same** counts as the simpler `Name.isInternal` filter (18279 total / 43 tainted, both
ways). Reason: this codebase's `private` declarations get Lean's standard name-mangling
(`_private.Module.hash.name`), which `Name.isInternal` already excludes, so on the *current* tree
the extra `setExporting` filter is a no-op. Recommend keeping the `setExporting` filter anyway in
the shipped script — it is the technically correct definition of "public," it's free (no measured
timing difference), and it stays correct if this repo's usage of `private` ever diverges from the
mangled-name convention.

**Live measured totals**: `18279` public `Cslib.*` declarations (`theorem`/`def`/`opaque`, incl.
registered `Decidable` instances, which are `defnInfo`), of which **43** are `sorryAx`-tainted
(full list gathered in section C below, useful directly as the v1 baseline content).

## B. Live re-verification of the task's stated numbers

- **18 `set_option warn.sorry false` markers, across exactly 5 files** — CONFIRMED, unchanged:
  `grep -rn "set_option warn.sorry false" Cslib/ --include='*.lean' | wc -l` → 18; the 5 files are
  `BXCanonical/Frame.lean`, `ConservativeExtension/TemporalConservativity.lean`,
  `Bundle/UntilSinceCoherence.lean`, `BXCanonical/Chronicle/ChronicleToCountermodel.lean`,
  `Bundle/SuccRelation.lean`.

- **Naive `grep -c sorry` over `Cslib/`**: currently **180** (task text said "~168" — small
  upward drift since the task was scoped, consistent with ordinary prose/docstring churn; does not
  change the conclusion that the naive count is useless).

- **True code-position sorry count**: **28**, NOT ~168/180. This independently reproduces a figure
  already on record: task 575 (`specs/TODO.md`, now `[COMPLETED]`) states verbatim "TRUE census is
  28 (Bimodal 23, Propositional 4, Modal 1, Temporal 0, Foundations 0)" and "the project's own
  bare-sorry figures are inflated because `warn.sorry` matches a naive `\bsorry\b` scan... Any
  future sorry count must exclude lines containing `warn.sorry`." My independently-built
  discrimination rule (section C) landed on the identical 28/23/4/1/0/0 split without having read
  that line first — strong cross-validation that both the rule and the number are right.

- **Class 1 "silent taint" — the task's own cited witnesses are WRONG, corrected**: the task
  states `Cslib.Logic.PL.intuitionisticTableau_complete` and `...minimalTableau_complete` are
  examples of "a declaration that consumes a sorry'd lemma but contains **no** `sorry` token."
  This is false for these two specific declarations as of the current tree: I read both bodies
  directly and confirmed each contains a literal `sorry` tactic call in its own proof
  (`Completeness.lean:124` / `Minimal/Completeness.lean:118`), and confirmed via a targeted
  `lake build --wfail --iofail` on each target that Lean **does** emit `warning: ...: declaration
  uses 'sorry'` directly for both — i.e. they are not silent by the "no sorry token" mechanism at
  all (their axiom taint is real and their `#print axioms` output does match what the task quoted,
  but that's simply because they *are* directly sorry'd, which is the ordinary, already-visible
  case, not the class-1 phenomenon).

  I found and verified the **genuine** silent-taint witnesses instead: `Cslib.Logic.PL.
  minimalTableau_decides` (`Minimal/DecisionProcedure.lean:106`) and `Cslib.Logic.PL.
  intuitionisticTableau_decides` (`Intuitionistic/DecisionProcedure.lean:97`). Both contain zero
  `sorry` tokens in their own bodies (confirmed by reading the files); both carry
  `[propext, sorryAx, Classical.choice, Quot.sound]` per `lean_verify`/`#print axioms`, because
  they invoke the sorry'd `_complete` lemmas as opaque constant references. I built each module and
  confirmed the warnings that appear are all attributed to *other* declarations/files (the actual
  sorry sites in `Scheme.lean`/`Completeness.lean`) — **`_decides` itself never gets its own
  "declaration uses sorry" warning anywhere in the build**, which is exactly the silent-taint
  mechanism the task is trying to describe: Lean's warning fires on `Expr.hasSorry` of the
  declaration's own elaborated term (a direct literal occurrence), while `#print axioms`/
  `Lean.collectAxioms` walks the *kernel* dependency graph transitively through referenced
  constants. Use `minimalTableau_decides` / `intuitionisticTableau_decides` as the canonical
  worked example in the plan/implementation instead of the two the scope text names.

- **Current `lake build --wfail --iofail` status — IMPORTANT, not previously stated in scope**:
  this is currently RED on the local tree, independent of anything in this task's scope. I built 4
  targets directly and each failed:
  `Cslib.Logics.Modal.Tableau.FrameSoundness`,
  `Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`,
  `Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness`,
  `Cslib.Logics.Propositional.Tableau.Minimal.Completeness` — each emits a real
  `declaration uses 'sorry'` warning (these are the 4 files with bare, *unsuppressed* sorries: 1 +
  2 + 1 + 1 = 4 of the 28) and `--wfail` promotes it to `error: build failed`. This is not new or
  accidental: `specs/TODO.md` task 575 (`[COMPLETED]`) explicitly scoped this as expected, stating
  its own definition of done as "`lake build --wfail --iofail` reports no failures **other than**
  the 4 genuine-sorry modules" and "The 4 files failing CI on genuine sorries ... will remain
  CI-red after this task and that is expected and correct." The two new gates in this task can each
  independently exit 0 on the current tree (they are ratchet checks, not the `--wfail` build
  itself), but **the `lean_action_ci.yml` job as a whole is not currently green**, and the
  `leanprover/lean-action@v1` build step has no `continue-on-error`, so today any step added after
  it in that same job would never execute in a real run once pushed. See section F for the
  concrete recommendation this drives.

## C. Code-position-vs-prose discrimination rule — defined and tested

**Rule**: strip block comments (`/- ... -/`, which also captures doc comments `/-- ... -/` since
they start with `/-`) non-greedily across the whole file, then strip line comments (`--` to end of
line) per resulting line, then exclude any surviving line containing the substring `warn.sorry`
(so the option name `set_option warn.sorry false` doesn't self-count — `\bsorry\b` matches inside
`warn.sorry` because `.` is a non-word char, so this exclusion is necessary, not decorative), then
count `\bsorry\b` word-boundary occurrences on what remains. `sorryAx` is inherently excluded by
`\b` (no boundary exists between `y` and `A` in `sorryAx`, both being word characters) — no special
case needed for it.

Tested (Perl `-0777` slurp for the block-comment pass, so it correctly spans multi-line
doc comments; verified nested `/- -/` does not occur in the affected files, so non-nested
`.*?` suffices):

```
grep -c sorry (naive, whole repo)              : 180
\bsorry\b word-boundary, no comment stripping  : 180 lines matching; 149 after excluding warn.sorry lines
after full discrimination rule                 : 28  (across 9 files)
```

Per-file breakdown (all 9 files that contain at least one code-position sorry):

| File | sorries | has `warn.sorry false` suppression? |
|---|---|---|
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 12 | yes (partly file-scoped — see below) |
| `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` | 7 | yes |
| `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` | 2 | yes |
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` | 1 | yes |
| `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` | 1 | yes |
| `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` | 2 | **no** |
| `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` | 1 | **no** |
| `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` | 1 | **no** |
| `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` | 1 | **no** |

Bimodal subtotal 23, Propositional 4, Modal 1 — matches task 575's independently-recorded split
exactly (see section B).

Every code-position sorry I inspected already carries a trailing `-- blocked on X` /
`-- TODO: depends on Y` comment naming the concrete blocker (e.g. `-- blocked on upstream
continuous-frame completeness (port_continuous_completeness_bimodal)`,
`-- TODO: depends on discrete_embed_strictMono`, `-- depends on gap_contradicts_prior from
GoodStructuresModelSurgery`). This is directly useful for the ledger design in part D.

## D. Baseline "owning task" vs. no-task-references rule — CONFLICT, recommendation

`.claude/rules/no-task-references-in-deliverables.md` is unambiguous: deliverable files outside
`specs/**` (which includes anything under `scripts/`) MUST NOT cite ephemeral task numbers, because
they are meaningless after a vault renumbering and don't help a future reader. Scope item 4's
literal instruction ("record... the CURRENT owning task for every entry") would violate this rule
if implemented as a bare task number. This is exactly the kind of case the rule's "Reference
Durable Anchors Instead" section anticipates.

**Recommendation**: record, per baseline entry, the fully-qualified declaration name (already the
natural primary key) plus its owning file path (already a required column for lookups), plus a
free-text **reason** column populated from the in-source blocking comment when one exists (section
C showed these already exist at essentially every sorry site: `port_continuous_completeness_bimodal`,
`gap_contradicts_prior from GoodStructuresModelSurgery`, `discrete_embed_strictMono`, "WeakCanonical
discrete-completeness port", etc.). This is a strictly *better* debt ledger than a task number:
- it's self-contained (no cross-reference to `specs/` needed to understand *why*),
- it survives vault renumbering untouched,
- it's already what a maintainer would grep for when deciding whether a blocker has since landed
  (e.g. `grep -rn port_continuous_completeness_bimodal Cslib/` immediately tells you if/where that
  blocking lemma now exists), which a task number never does on its own.

For the axiom-census baseline (item 1, tainted declarations), the reason string can't always be
mechanically derived (taint is transitive, so the "reason" for `minimalTableau_decides` is really
"depends on `minimalTableau_complete`," which is one more level of indirection than a source-file
grep gives). Recommend: reason column = name of the direct sorry'd dependency actually reachable
in the axiom walk when it's a single hop (cheap to compute: same collect-axioms walk, but stop at
the first `sorryAx`-tainted named constant instead of just registering the axiom), falling back to
"(transitive — see file)" when the chain is deeper. This keeps the ledger informative without
requiring a full call-graph explanation feature.

Do **not** use a task number anywhere in `scripts/*-baseline.txt`.

## E. Conventions to carry over from `check-lint-suppressions.sh` / `check-shake-residue.sh`

Both scripts should carry over:
- `set -uo pipefail` (no `-e`) — both existing scripts explicitly avoid `-e` because their core
  comparison logic runs advisory sub-commands that legitimately return nonzero on "found nothing,"
  and the accumulate-then-single-`exit`-at-the-end pattern needs those to keep running.
- Exit-code contract: `0` clean-or-improved, `1` regression, `2` usage/environment error. For the
  axiom census specifically, this means: if `lake env lean --run` fails to produce parseable output
  (crashes, times out, or the census script itself errors), that MUST be `exit 2`, never silently
  reported as "0 tainted." This is exactly `check-shake-residue.sh`'s
  "shake exit 1 but zero flagged-file lines parseable -> exit 2, never a clean empty result" rule,
  and it applies with equal force here: a broken Lean environment must not masquerade as a
  zero-taint census.
- `--update` (rewrite baseline from current tree) and `--list` (print current live set/counts)
  flags, matching both precedents' CLI shape.
- Ratchet-only-decreases semantics: a baseline entry no longer present/tainted is reported as an
  IMPROVEMENT (not a failure) and prompts "re-baseline with `--update`"; a *new* untracked entry is
  a FAIL. This applies directly to both new scripts.
- Header comment block in the baseline file itself: what the file is, that it's machine-generated,
  "do not hand-edit," and the exact command that regenerates it — both existing baseline files do
  this and it's clearly load-bearing (it's the only thing stopping someone from manually editing
  the ceiling down without actually fixing anything).
- Model choice between the two ratchet *shapes*: `check-lint-suppressions.sh` uses a **per-file
  ceiling count**; `check-shake-residue.sh` uses an **exact path/name set**. The axiom-census gate
  (item 1) is naturally a **set** (a given declaration either is or isn't `sorryAx`-tainted — there
  is no meaningful "count per file" the way blanket-suppression occurrences stack) — model it on
  `check-shake-residue.sh`'s exact-set baseline, keyed on fully-qualified declaration name. The
  sorry-suppression gate (item 2) is naturally two **per-file (or aggregate) counts** (number of
  `warn.sorry false` markers, number of bare sorries) — model it on
  `check-lint-suppressions.sh`'s per-file ceiling-count baseline, extended to two count columns
  instead of one.
- `check-shake-residue.sh`'s "needs a completed build" handling (its whole header section on why it
  is invoked from `pre-pr-check.sh` rather than a CI workflow, and why it's absent from
  `lean_action_ci.yml`) is the single most relevant piece of prior art for item 1 (axiom census also
  needs built `.olean`s) — see section F, this precedent directly informs the CI-wiring conflict
  below.

## F. `pre-pr-check.sh` / `scripts/README.md` wiring, and a second scope conflict found

`scripts/pre-pr-check.sh` is a manually maintained, numbered-step script; `check-lint-suppressions.sh`
is step 6, `check-shake-residue.sh` is step 7 (added immediately before this task, with the comment
"needs the completed build from steps 4/5 above"). `scripts/README.md` documents each script under
its own heading with a rationale block and a `Usage:` section.

**Recommendation, direct answer to the research question**: yes, wire both new gates into
`pre-pr-check.sh` (as steps 8 and 9, or combined into one step if the planner prefers) **in
addition to** wherever CI ends up landing, and add matching `scripts/README.md` entries in the same
style as the `check-shake-residue.sh` entry. This is not a genuinely optional call — every existing
ratchet gate in this repo is wired into `pre-pr-check.sh`, and skipping it here would make these two
gates the only ones a contributor can't verify locally before opening a PR.

**Second conflict (new finding, not anticipated by the scope text) — where in CI**: scope item 3
says wire both into `.github/workflows/lean_action_ci.yml`. But:
- `check-lint-suppressions.sh` (no build dependency) was **not** added there; it was added to a
  **new, separate, local-only file**, `.github/workflows/lint-hygiene.yml`, whose own header
  explains why: "every workflow under `.github/workflows/` is shared with the `leanprover/cslib`
  upstream remote, so editing one adds a conflict hunk to every future sync. A new file is a pure
  local addition and conflicts with nothing." (This repo genuinely has an `upstream` remote —
  `git remote -v` confirms `leanprover/cslib` — and a scheduled workflow,
  `merge_main_into_nightly-testing.yml`, that actively merges from it, so this isn't a hypothetical
  concern.)
- `check-shake-residue.sh` (build-dependent, same shape as the axiom census) was deliberately
  **not** added to any CI workflow at all — its header explains it needs built `.olean`s, and a
  new step in the shared `lean_action_ci.yml` "adds a conflict hunk to every future sync," so it
  lives only in `pre-pr-check.sh`.
- Additionally (section B): `lean_action_ci.yml`'s build step is *currently red by design* on this
  tree (task 575's accepted end-state). Steps placed after it in the same job, without
  `if: always()`, will not execute at all in a real run until that pre-existing, out-of-scope
  4-file gap closes.

So scope item 3's literal instruction runs directly counter to a convention this same codebase
established twice, most recently in the task immediately preceding this one. I'm flagging this
for an explicit decision rather than silently picking a side, same as part D. Two reasonable paths,
in order of how well they fit existing precedent:
1. **Follow precedent**: add a new step to `lint-hygiene.yml` for the sorry-suppression counter
   (item 2, no build needed, fits that workflow's "Lean-free, seconds" charter exactly), and do
   **not** add the axiom census (item 1, needs a build) to any CI workflow — rely on
   `pre-pr-check.sh` only, exactly like shake. This keeps `lean_action_ci.yml` untouched.
2. **Follow the literal scope text**: add both as new steps to `lean_action_ci.yml`, using
   `if: always()` on both new steps so they still execute and report independently even while the
   build step remains red on the known 4 files, and accept the sync-conflict-hunk cost the last two
   gates both explicitly avoided.

I recommend option 1 (matches established, twice-validated local convention; avoids reopening the
sync-conflict problem the immediately-preceding task solved) but this is the user's call to make
explicitly in the plan, not mine to decide by omission.

## Recommendations for planning (concrete, ready to phase)

1. **`scripts/check-axiom-census.sh`** + `scripts/axiom-census-baseline.txt`: exact-set baseline
   (declaration name, owning file, reason), driven by a Lean census script
   (`scripts/AxiomCensus.lean`, registered as a `[[lean_exe]]` in `lakefile.toml` mirroring
   `CheckInitImports`, OR invoked via `lake env lean --run` directly — either is fine given the
   ~2.7s cost; `lean_exe` is marginally more idiomatic given the `checkInitImports` precedent and
   avoids re-interpreting the driver script on every invocation). Uses `import Cslib` +
   `env.setExporting true` + `Lean.collectAxioms` per public declaration. Baseline v1 = the 43
   names in section A/C's output. Exit 2 if the run produces no parseable output.
2. **`scripts/check-sorry-suppressions.sh`** + `scripts/sorry-suppression-baseline.txt`: per-file
   two-count ceiling (marker count, sorry count), pure `grep`/`perl` text scan using the section-C
   discrimination rule, no build dependency. Baseline v1 = the 9-file table in section C (5 files
   with markers+sorries, 4 files with sorries-only and 0 markers).
3. Both scripts: `set -uo pipefail`, `--update`/`--list` flags, exit 0/1/2 contract, header comment
   block, ratchet-only-decreases (improvement reported, never failed).
4. Wire both into `pre-pr-check.sh` (new steps 8/9) and document in `scripts/README.md`.
5. CI wiring: get an explicit decision on the `lean_action_ci.yml` vs. `lint-hygiene.yml`-style
   local-file conflict (section F) before implementing item 3's literal text.
6. Baseline "owning" column: declaration/file/reason, never a task number (section D).
7. In the plan or PR description, use `minimalTableau_decides` /
   `intuitionisticTableau_decides` as the Class-1 worked example, not
   `intuitionisticTableau_complete` / `minimalTableau_complete` (section B correction).
8. New scripts will be swept by the existing path-triggered `shellcheck.yml`
   (`scripts/**/*.sh`, `--severity=warning`) automatically — no separate wiring needed there, but
   model the new scripts closely on the two existing ones (which already pass) to minimize risk;
   `shellcheck` itself is not installed in this sandbox so it could not be run locally to confirm.

## Files/paths referenced

- `/home/benjamin/Projects/cslib/scripts/check-lint-suppressions.sh` (model)
- `/home/benjamin/Projects/cslib/scripts/check-shake-residue.sh` (model, build-dependent precedent)
- `/home/benjamin/Projects/cslib/scripts/lint-suppression-baseline.txt` (per-file ceiling format)
- `/home/benjamin/Projects/cslib/scripts/shake-residue-baseline.txt` (exact-set format)
- `/home/benjamin/Projects/cslib/scripts/pre-pr-check.sh` (steps 6/7 precedent; recommend 8/9)
- `/home/benjamin/Projects/cslib/scripts/README.md` (documentation precedent)
- `/home/benjamin/Projects/cslib/scripts/CheckInitImports.lean` +
  `/home/benjamin/Projects/cslib/lakefile.toml` `[[lean_exe]]` block (Lean-exe-in-lakefile precedent)
- `/home/benjamin/Projects/cslib/.github/workflows/lean_action_ci.yml` (shared/upstream-synced;
  current build step is red-by-design on this tree per completed task 575)
- `/home/benjamin/Projects/cslib/.github/workflows/lint-hygiene.yml` (local-only precedent for
  non-build-dependent new gates)
- `/home/benjamin/Projects/cslib/.github/workflows/shellcheck.yml` (auto-covers new scripts)
- `/home/benjamin/Projects/cslib/.claude/rules/no-task-references-in-deliverables.md` (the rule in
  tension with scope item 4)
- `/home/benjamin/Projects/cslib/specs/TODO.md` task 575 entry (independently records the 28/23/4/1/0/0
  sorry split and the "4 files remain CI-red, expected and correct" acceptance)
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean:106` (`minimalTableau_decides`,
  genuine Class-1 witness)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean:97`
  (`intuitionisticTableau_decides`, genuine Class-1 witness)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:124` and
  `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:118` (the two declarations the task
  text cited as Class-1 examples; corrected in section B — they contain direct sorry tokens and are
  not silent)
