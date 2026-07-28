# Phase 2 Handoff: Add the local shake-residue guard

**Status**: COMPLETED

## What was done
- `scripts/check-shake-residue.sh` (new, executable): exact-set ratchet guard on `lake shake
  --add-public --keep-implied --keep-prefix Cslib`. No args = verify; `--update` = re-baseline;
  `--list` = print live flagged set; unrecognized flag = usage + exit 2.
- Fixed a subshell bug during development: the exit-code capture must happen in a function called
  directly (`run_shake`), not inside a `$(...)` command substitution, or the `shake_exit` global
  assignment is lost to the caller. Verified via `bash -n` and live runs.
- `scripts/shake-residue-baseline.txt` (new): generated via `--update`, contains exactly the 9
  paths from Phase 1's live-verified residue (see phase1-handoff.md for the LcAt.lean deviation).
- `scripts/pre-pr-check.sh`: added step 7 invoking the guard, same accumulate-into-`failed` shape
  as step 6.
- `scripts/README.md`: documented the new script/baseline under a new "Import minimization (`lake
  shake`) local guard" heading.

## Verification proven (not just claimed)
- Clean path: exit 0, "OK: shake-flagged set matches the baseline exactly."
- Regression path: deleted `TimeM.lean` from a `.bak`-backed baseline copy -> FAIL + exit 1,
  restored via `mv` (never `git checkout`/`git restore`).
- Improvement path: appended a fabricated path to a `.bak`-backed baseline copy -> IMPROVED + exit
  0 + re-baseline note, restored via `mv`.
- `--list` prints the 9-path live set, exit 0.
- Bad flag (`--bogus`) -> usage message to stderr, exit 2.

## Next
Phase 3: comment out the `lake shake` CI step in `.github/workflows/lean_action_ci.yml` with the
inline audit-trail rationale block. This phase (guard) is the GATE for Phase 3 -- since the guard
is proven working, Phase 3 may proceed.
