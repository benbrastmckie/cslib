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
