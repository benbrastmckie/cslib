# Phase 1 Handoff — Free deletions (dead code with zero call sites)

**Status**: [COMPLETED]

## What happened

- Captured baseline invariants: `lake build Cslib` green at 3311 jobs; `checkInitImports` exit 0;
  `lint-style` exit 0; `lake shake` exit 1 with 9 findings, none in `Modal/Tableau` (verified via
  a purpose-built `shake_check.sh` that strips build-replay warning noise — a naive
  `grep 'Modal/Tableau'` on raw `lake shake` output false-positives on the sorry-warning line
  every time, since `lake shake` always replays the full build log first); sorry census exactly
  1 line in `Modal/Tableau/`, declaration `branchSatisfiableIn_s4FC_ancestor_redirect` at
  `FrameSoundness.lean:1252` (sorry token at line 1276); axiom count 0.
- Built `specs/558_tableau_support_private_dedup/scripts/census.py`, a two-signal
  declaration-level duplicate census (exact-name duplicates + suffix-family duplicates, with
  block-comment stripping to avoid docstring-prose false positives — e.g. a sentence like
  "...lemma is `private`..." at column 0 was originally mis-parsed as a `lemma is` declaration).
  **Measured baseline: 74 duplicate declarations across 43 families**, not the plan's estimated
  72/41. Hand-verified every family against the plan's own named-family lists; the only two
  unnamed families are `modalApplyOneT_branchingLength` (LoopChecking.lean vs TDriver.lean) and
  `modalApplyOneT_persistentFresh` (same file pair) — flagged for Phase 10 residue triage.
- Deleted `modalKnownWorlds_nodup_S5` and its helper `modalKnownWorlds_fold_nodup_S5`
  (S5Simplification.lean) — zero call sites, confirmed by repo-wide grep before deletion.
- Relocated `hasEdge_mem_successorsOf` earlier in `LoopChecking.lean` (to the point where the
  forward-reference workaround `hasEdge_mem_successorsOf_origin` used to sit) and deleted the
  workaround; redirected its two call sites (lines ~1606, ~1646) to the relocated name.
- Confirmed `modalKnownWorlds_nodup_S4` is public with 2 live call sites — correctly NOT deleted.
- Post-edit census: 72 duplicates / 42 families (both families involved in this phase's deletions
  resolved as expected: the `hasEdge_mem_successorsOf` family disappeared entirely since only one
  copy remains; `modalKnownWorlds_nodup` dropped from 3 to 2 declarations).
- Full invariants table re-verified green after edits. `git diff --name-only` confirms
  `Rules.lean`, `Saturation.lean`, `Branch.lean` untouched.
- Three commits: phase 1.1 (S5Simplification.lean deletions + census script), phase 1.2
  (LoopChecking.lean relocation), phase 1 close (plan-file status update).

## Continuation pointer

Resume at **Phase 2**: create `Cslib/Logics/Modal/Tableau/Support/Accessibility.lean`. Use the
measured **72/42** as the current running census baseline (not the plan's 72/41 — the family
count differs even though the duplicate count coincidentally matches at this checkpoint).

Re-run `python3 specs/558_tableau_support_private_dedup/scripts/census.py --quiet` at the start
of every subsequent phase to track the running total; use `--family NAME` to scope to one family,
`--files F1.lean F2.lean` to scope to specific files (used by Phases 8/9's file-scoped Scope
Hypotheses).

Use `bash specs/558_tableau_support_private_dedup/scripts/shake_check.sh` (not a bare
`lake shake | grep`) for the shake invariant check — it strips the build-replay noise that
otherwise false-positives the `Modal/Tableau` grep on the sorry-warning line every time.
