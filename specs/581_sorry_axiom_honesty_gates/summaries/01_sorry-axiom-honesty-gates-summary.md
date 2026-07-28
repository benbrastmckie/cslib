# Implementation Summary: Task #581 — sorry_axiom_honesty_gates

- **Plan**: plans/01_sorry-axiom-honesty-gates.md
- **Status**: [COMPLETED] (all 6 phases)
- **Type**: cslib

## Overview

Added two ratchet gates that make existing proof debt visible without discharging any of it:

1. **Axiom census** (`scripts/AxiomCensus.lean` + `scripts/check-axiom-census.sh` +
   `scripts/axiom-census-baseline.txt`): an exact-set ratchet over every public `Cslib.*`
   declaration whose kernel axiom set transitively contains `sorryAx`, even when the
   declaration's own body has no literal `sorry` token (the "silent taint" `--wfail` cannot
   see). Baseline: 43 declarations, exact-set comparison.
2. **Sorry-suppression ratchet** (`scripts/check-sorry-suppressions.sh` +
   `scripts/sorry-suppression-baseline.txt`): a per-file two-count ceiling on
   `set_option warn.sorry false` markers and true code-position `sorry` occurrences, using a
   tested discrimination rule that excludes doc-comment prose and the option name itself.
   Baseline: 18 markers / 5 files, 28 sorries / 9 files — exactly matching the settled figures
   from the research report.

Both gates are wired into `.github/workflows/lean_action_ci.yml` and `scripts/pre-pr-check.sh`
(steps 8/9), documented in `scripts/README.md`, and land GREEN on the current tree by
construction (ratchet, not absolute gate). No `.lean` file under `Cslib/` was modified; no
sorry was discharged, restated, added, relocated, or hidden; no existing
`set_option warn.sorry false in` marker was removed.

## Plan Deviations

**Phase 1 — significant, fully documented deviation from the specified mechanism.** The plan
directed calling the builtin `Lean.collectAxioms` directly per declaration, on the premise that
its results are cached across declarations via the `exportedAxiomsExt` persistent environment
extension (the same mechanism backing `#print axioms`), citing a research measurement of
~2.7s for a full census.

**That premise did not hold when tested against this repo's actual built `.olean`s.** Direct
measurement (5 repeated calls to `Lean.collectAxioms` on the *same* declaration, each taking
~64ms with no speedup) proved the cross-declaration cache is not being hit for a large fraction
of this environment's declarations — confirmed not Cslib-specific (a Mathlib-native declaration,
`Mathlib.Meta.NormNum.evalAdd`, was also uncached/slow at 213ms). A full loop over the 18279
candidates using the literal specified approach was projected at several minutes total — the
same order of cost the per-module design was rejected for, and unacceptable for a gate meant to
run in CI and `pre-pr-check.sh`.

**Fix implemented**: `collectAxiomsCached` in `scripts/AxiomCensus.lean` reimplements the
identical dependency-walk semantics (same `ConstantInfo` case dispatch, same `sorryAx`-membership
taint definition Lean's own `Lean.CollectAxioms.collect` uses) but threads an explicit
`IO.Ref (Std.HashMap Name (Array Name))` cache across the *entire* census run instead of
resetting it per top-level declaration. This keeps every other part of the specified design
(single process, whole-`Cslib`-root-import, no per-module spawning) and reproduces the exact
`tainted=43` figure the plan's baseline is built from, completing in ~8.6s total (three runs:
8.6s / 8.5s / 8.7s) — well within the plan's own "a few seconds, not minutes" verification bar.
This is transparently documented in the script's own module-header doc comment and annotated
inline in the plan file's Phase 1 checklist (not a silent substitution).

**Phase 3 — minor, explicitly-scoped deviation, anticipated by the plan itself.** The D1 debt
ledger only emits a blocker-comment entry for a file's code-position sorry when that exact source
line carries a trailing `--` comment. 5 of the 9 files (the ones with no `warn.sorry` marker,
i.e. the files that are already red under `--wfail` by design) have bare `sorry` with no trailing
comment on that line — their blocker context lives in surrounding docstring prose instead, which
is intentionally not parsed for the ledger (parsing it would reintroduce exactly the naive-grep
overcounting problem the whole task exists to avoid — verified: raw per-line `\bsorry\b`
matching on this tree, even excluding `warn.sorry` lines, gives 150 hits across far more files,
almost entirely prose). One entry (`BXCanonical/Frame.lean`) is truncated at the line boundary
because its blocker comment continues onto a second physical line. Both are cosmetic limits of an
explicitly informational, non-load-bearing mechanism — ledger comment lines are skipped by the
comparison parser — not a defect in the ceiling counts themselves, which were independently
verified against the exact settled 18/5-files and 28/9-files split (first attempt, no fallback to
line counting needed).

**Phase 6 — pre-approved deviation, per the plan's own "Method note".** The axiom-census
regression proof mutates the baseline (removes a row) rather than adding a scratch tainted
declaration, because a scratch declaration would only be censused if reachable from the `Cslib`
root import, which requires editing `Cslib.lean` (forbidden by the non-goals). The plan already
flagged and pre-approved this substitution; the equivalent code path (live name absent from
baseline → FAIL → exit 1) is exercised with zero risk to the library. The suppression gate's
scratch-file probe was done literally as specified.

No other deviations. All Settled Decisions (D1-D4) were implemented as written and not
re-litigated.

## Phase 6 — Definition-of-Done Evidence (six recorded exit codes)

| Proof | Command shape | Observed exit |
|---|---|---|
| Axiom census regression | remove one baseline row, run bare | **1** (`FAIL Cslib.Logic.PL.minimalTableau_decides ...`) |
| Axiom census improvement | append a nonexistent-decl row, run bare | **0** (`IMPROVED ...` + `ACTION REQUIRED`) |
| Suppression regression | scratch-file probe (`Cslib/ZZScratchSuppressionProbe.lean`) | **1** (`FAIL Cslib/ZZScratchSuppressionProbe.lean ...`) |
| Suppression improvement | raise one file's ceiling above live counts | **0** (`ACTION REQUIRED` re-baseline instruction) |
| Suppressions, bare (restored tree) | — | **0** (`OK: sorry/suppression counts match the baseline (or improved).`) |
| Axiom census, bare (restored tree) | — | **0** (`OK: sorryAx-tainted set matches the baseline exactly.`) |

All mutations were `.bak`/`mv`-restored or `rm`-removed within Phase 6 itself (never
`git checkout --`/`git restore`, per the git-workflow constraint on dirty trees). Post-Phase-6
verification: `git status --porcelain Cslib/` empty, no `.bak` files under `scripts/`,
`git diff -- scripts/axiom-census-baseline.txt scripts/sorry-suppression-baseline.txt` empty.

## Final CI Pipeline Verification

Run in full against the restored, clean tree (no `.lean` file under `Cslib/` was ever
permanently modified, so this is a regression check that pre-existing repo health is
unaffected, plus confirmation that the two new gates introduce no new debt):

| Step | Result |
|---|---|
| 0. `lake exe cache get` | cache already warm, no-op |
| 1. `lake build` | succeeds; warnings only from the 4 pre-existing, accepted bare-sorry files |
| 2. `lake exe checkInitImports` | exit 0, no output |
| 3. `lake lint` | pre-existing warnings only, in 4 files unrelated to this task (`FrameSoundness.lean`, `HilbertConservativeGlivenko.lean`, `ChronicleConstruction.lean`, `DenseSoundness.lean`); zero mentions of `scripts/` (not lint-scoped) |
| 4. `lake exe lint-style` | exit 0, no output |
| 5. `lake shake ...` (raw) | exit 1 (expected — pre-existing residue); `bash scripts/check-shake-residue.sh` → exit 0, "matches the baseline exactly" (9 files, unchanged) |
| 6. `lake exe mk_all --check` | "No update necessary" |
| 7. `lake test` | exit 0; only pre-existing warnings (the same 4 bare-sorry files plus one pre-existing `privateInPublic` notice in `CslibTests/FreeMonad.lean`) |
| `bash scripts/check-sorry-suppressions.sh` | exit 0 |
| `bash scripts/check-axiom-census.sh` | exit 0 |

`shellcheck` itself could not be run locally (not installed in this environment, per Carry-Over
Convention 8); both new scripts were modelled closely on the two existing, passing precedents
(`check-lint-suppressions.sh`, `check-shake-residue.sh`) to minimize risk, and will be swept
automatically by the path-triggered `.github/workflows/shellcheck.yml` on push.

### Sorry / vacuous-definition / axiom checks (per this agent's mandatory final-verification stage)

- `grep -rn "\bsorry\b" scripts/AxiomCensus.lean` → only prose in doc comments explaining the
  mechanism (`Expr.hasSorry`, "primary sorry site"), zero actual `sorry` tactic usage.
- Vacuous-definition regex, scoped to files this task touched → zero matches.
- `grep -n "^axiom " scripts/AxiomCensus.lean` → zero matches (no new axioms introduced).
- Repo-wide `Cslib/` sorry/vacuous/axiom counts (168 naive-grep sorries, 1 vacuous-regex hit,
  26 axioms) are **pre-existing and unaffected by this task** — no `.lean` file under `Cslib/`
  was modified (confirmed via `git status --porcelain Cslib/` / `git diff -- Cslib/`, both
  empty at every phase boundary). The single vacuous-regex hit
  (`Cslib/Computability/URM/Basic.lean:92`, `theorem J_IsJump ... := trivial`) is a legitimate,
  pre-existing proof where the naive regex flags `:= trivial` without evaluating whether the
  goal is actually trivial by definition; it predates this task and is out of scope per the
  non-goals and the "no `.lean` file under `Cslib/`" hard constraint.

## Artifacts

- `scripts/AxiomCensus.lean` (new, 172 lines)
- `scripts/check-axiom-census.sh` (new, executable)
- `scripts/axiom-census-baseline.txt` (new, 43 data rows)
- `scripts/check-sorry-suppressions.sh` (new, executable)
- `scripts/sorry-suppression-baseline.txt` (new, 9 data rows + D1 ledger comments)
- `.github/workflows/lean_action_ci.yml` (modified: two new steps + divergence-cost comment block, purely additive)
- `scripts/pre-pr-check.sh` (modified: steps 8/9 + explanatory comment)
- `scripts/README.md` (modified: two new documented entries)

No task-number references appear in any of the above (verified via
`grep -rnE 'task [0-9]+|tasks [0-9]+'` across all seven files — zero hits).
