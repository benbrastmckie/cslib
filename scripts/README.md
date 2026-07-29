# Scripts for working on cslib

This directory contains miscellaneous scripts that are useful for working on or with cslib.
When adding a new script, please make sure to document it here, so other readers have a chance
to learn about it as well!

## Current scripts and their purpose

**Documentation generation**
- `gendocs.sh`
  Generates the documentation for cslib using `lake`.

**Managing nightly-testing and bump branches**
- `create-adaptation-pr.sh` is a variant of the script from Batteries and implements some of the steps
  in the workflow for managing nightly and bump branches.

  Specifically, it will:
  - merge `main` into `bump/v4.x.y`
  - create a new branch from `bump/v4.x.y`, called `bump/nightly-YYYY-MM-DD`
  - merge `nightly-testing` into the new branch
  - open a PR to merge the new branch back into `bump/v4.x.y`
  - announce the PR on zulip
  - finally, merge the new branch back into `nightly-testing`, if conflict resolution was required.

  If there are merge conflicts, it pauses and asks for help from the human driver.

  **Usage:**
  ```bash
  ./scripts/create-adaptation-pr.sh <BUMPVERSION> <NIGHTLYDATE>
  ```
  or with named parameters:
  ```bash
  ./scripts/create-adaptation-pr.sh --bumpversion=<BUMPVERSION> --nightlydate=<NIGHTLYDATE> --nightlysha=<SHA> [--auto=<yes|no>]
  ```

  **Parameters:**
  - `BUMPVERSION`: The upcoming release that we are targeting, e.g., 'v4.10.0'
  - `NIGHTLYDATE`: The date of the nightly toolchain currently used on 'nightly-testing'
  - `NIGHTLYSHA`: The SHA of the nightly toolchain that we want to adapt to
  - `AUTO`: Optional flag to specify automatic mode, default is 'no'

  **Requirements:**
  - `gh` (GitHub CLI) must be installed and authenticated
  - Optional: `zulip-send` CLI for automatic Zulip notifications

**Init Imports**
- `CheckInitImports.lean` (run by `lake exe checkInitImports`) checks that all files transitively import `Cslib.Init`.

**Import minimization (`lake shake`) local guard**
- `check-shake-residue.sh` / `shake-residue-baseline.txt` — a local (non-CI) ratchet on
  `lake shake --add-public --keep-implied --keep-prefix Cslib` import-minimization debt. The
  baseline is an exact set of repo-relative paths known to already be flagged (frozen residue
  that is byte-identical to upstream as of a recorded audit date/SHA, so it is upstream's own
  unresolved debt, not this fork's); the check fails only when the live flagged set contains a
  path outside that baseline, i.e. new import debt this fork introduced. Needs a completed
  `lake build` first (shake inspects the build graph), which is why it is invoked as step 7 of
  `pre-pr-check.sh` rather than joining the Lean-free `lint-hygiene.yml` CI workflow. See the
  header comment in `check-shake-residue.sh` for the full rationale, including why the `--fix`
  flag and the per-file `-- shake: keep` annotation are not usable for the frozen residue.

  **Usage:**
  ```bash
  bash scripts/check-shake-residue.sh            # verify against the baseline
  bash scripts/check-shake-residue.sh --list      # print the live flagged set
  bash scripts/check-shake-residue.sh --update    # re-baseline from the live flagged set
  ```

**Silent `sorryAx` taint (axiom census) ratchet**
- `AxiomCensus.lean` / `check-axiom-census.sh` / `axiom-census-baseline.txt` — a ratchet on
  declarations whose kernel axiom set contains `sorryAx` even though the declaration's own body
  has no literal `sorry` token. `lake build --wfail --iofail` only fails on a DIRECT sorry
  token; a declaration that merely calls an already-sorry'd lemma as a dependency never gets its
  own "declaration uses 'sorry'" warning, so `--wfail` cannot see it. Two genuine, verified
  examples on this tree: `Cslib.Logic.PL.minimalTableau_decides` and
  `Cslib.Logic.PL.intuitionisticTableau_decides` — both build clean under `--wfail`, and both
  still transitively depend on a sorry. `AxiomCensus.lean` (run via
  `lake env lean --run scripts/AxiomCensus.lean`, needing a completed `lake build` first) walks
  the whole public `Cslib` API in one process and reports the exact set of tainted declarations;
  `check-axiom-census.sh` ratchets that set against the frozen baseline, which doubles as a debt
  ledger keyed on declaration name + owning file + in-source blocking reason (never a task
  number). Wired into `.github/workflows/lean_action_ci.yml` (with `if: always()`, since the
  build step it depends on is currently red by design on 4 known bare-sorry files) and as step 9
  of `pre-pr-check.sh`.

  **Usage:**
  ```bash
  bash scripts/check-axiom-census.sh            # verify against the baseline
  bash scripts/check-axiom-census.sh --list      # print the live tainted set
  bash scripts/check-axiom-census.sh --update    # re-baseline from the live tainted set
  ```

**Sorry/suppression volume ratchet**
- `check-sorry-suppressions.sh` / `sorry-suppression-baseline.txt` — a per-file two-count
  ceiling ratchet (marker count, true code-position sorry count) over `Cslib/`. A naive
  `grep -c sorry` massively overcounts on this tree (currently 180): most hits are prose
  mentions in doc comments, and `\bsorry\b` even matches inside the option name
  `set_option warn.sorry false` itself. The script's discrimination rule strips block and line
  comments, excludes lines mentioning `warn.sorry`, then counts word-boundary `sorry`
  occurrences on what remains -- see the header comment for the exact rule. No build dependency
  (pure text sweep), so it is wired into `.github/workflows/lean_action_ci.yml` before the build
  step (fails fast) and as step 8 of `pre-pr-check.sh`. The baseline also doubles as a debt
  ledger, recording each file's in-source blocking comment beneath the data rows.

  **Dual wiring in `pre-pr-check.sh`**: this script is invoked at both step 1 (scoped, via
  `--scope` to four hand-picked trees, for early fast-fail feedback) and step 8 (unscoped,
  whole-tree). Both compare against the same baseline, so step 1 contributes no unique failure
  coverage over step 8 and can never fail where step 8 passes -- see the rationale comment
  above step 8 in `pre-pr-check.sh` for the full relationship, including why step 1 and step 5
  (`lake build --wfail --iofail`) are NOT redundant despite both mentioning sorries.

  **Usage:**
  ```bash
  bash scripts/check-sorry-suppressions.sh                      # verify against the baseline
  bash scripts/check-sorry-suppressions.sh --list                # print current per-file counts
  bash scripts/check-sorry-suppressions.sh --update               # re-baseline from the current tree
  bash scripts/check-sorry-suppressions.sh --scope PATH...        # verify, restricted to PATH...
  bash scripts/check-sorry-suppressions.sh --changed [--base REF] # verify, restricted to changed .lean files (opt-in; default base origin/main)
  ```
