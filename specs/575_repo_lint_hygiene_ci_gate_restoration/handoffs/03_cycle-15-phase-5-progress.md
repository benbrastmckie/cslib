# Handoff: Cycle 15 (Phase 5 dispatch)

- **Task**: 575
- **Session**: sess_1785175989_6e99ab
- **Scope of this dispatch**: Phase 5 (suppression audit) only, per explicit delegation
  instruction. Phase 7's two carried-forward blockers were NOT re-investigated (see below).

## What was done

Processed 4 more local-only files to zero blanket suppressions each, following the plan's
established Phase 5 method (remove all suppressions, rebuild, categorize what surfaces, fix
mechanical categories, narrow the rest to declaration scope):

1. `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Splitting.lean` (5→0, 765 lines,
   commit `8bb8f6e5`)
2. `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Burgess.lean` (5→0, 870 lines,
   commit `6771ddeb`)
3. `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/Burgess.lean` (5→0,
   987 lines, commit `b54360e8`)
4. `Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean` (5→0, 1088 lines,
   commit `78b7b88a`)

Each file was rebuilt individually (scoped `lake build`), downstream importers rebuilt clean,
`lake exe lint-style` clean, and the suppression ratchet re-baselined
(`bash scripts/check-lint-suppressions.sh --update`) in the same commit as the file, per the
plan's per-file ratchet-gate requirement.

Plan file updated (commit `c311471a`): RESUME HERE section, Phase 5 heading marker, and a new
cycle-15 sub-entry with full per-file category breakdown, two new findings, and a refreshed
worst-offender list / resume point.

## Numbers

- Suppression-audit progress: 193 → 213 sites audited cumulative (33 files fully processed
  cumulative)
- Ratchet (blanket suppressions, repo-wide): 248 → 228
- Local-only in-scope remaining: 214 (live re-count against `upstream/main`)
- Upstream-carved-out (out of scope): 14 (a live re-count found 14, not the "12" some earlier
  cycle entries cite — not re-investigated, the carve-out set itself is unchanged; use the live
  number going forward)

## Verification (full CI pipeline, re-run at cycle end)

- `lake build --wfail --iofail`: exactly 5 baseline sorry warnings (`FrameSoundness.lean:1252`,
  `Intuitionistic/Scheme.lean:570,2583`, `Intuitionistic/Completeness.lean:124`,
  `Minimal/Completeness.lean:118`), zero new anywhere — gate intact
- `lake exe checkInitImports`: clean
- `lake exe lint-style`: clean, no output
- `lake shake --add-public --keep-implied --keep-prefix`: pre-existing findings across ~15
  files, NONE touched this cycle or any prior Phase 5 cycle (e.g.
  `Foundations/Logic/Metalogic/ListDeduction.lean`, `Logics/Modal/Basic.lean`) — flagged in the
  plan as out-of-scope drift, not fixed
- `lake exe mk_all --module`: "No update necessary"
- `lake test`: exit 0, same 5 baseline sorry warnings plus the one pre-existing unrelated
  `backward.privateInPublic` warning in `CslibTests/FreeMonad.lean`
- `sorry_count` (naive grep, documented unreliable): unchanged pattern; `--wfail` count of
  exactly 5 is authoritative
- `vacuous_count`: 1 (the single pre-existing false positive at `Computability/URM/Basic.lean:92`,
  unrelated to this task)
- `axiom_count`: 26, unchanged

## New findings this cycle (recorded in the plan)

1. **Edit-tool false-duplicate-match**: an `Edit` call reported 2 matches for an old_string that
   `grep -F` found only once — the second "match" was the same text at different indentation in
   a different declaration. Lesson: don't assume extra Edit-reported matches are true duplicates;
   verify with `grep -F` and widen context or target individually.
2. Both `Burgess.lean` files (Temporal and Bimodal/BXCanonical) share a near-identical
   `listConj`/`neg_mem_of_inconsistent_union` helper family — same fix pattern applied to both
   independently (not a copy-paste risk since they're genuinely separate files/namespaces).

## Not investigated (carried forward verbatim, per explicit delegation instruction)

Two Phase 7 blockers remain open and awaiting a human decision — NOT re-investigated this
dispatch:

1. **NOTATION.md upstream-PR decision**: the drafted "Logic notation scoping" section cannot
   land locally because the file is confirmed byte-identical to `upstream/main` (out of scope
   under the upstream-exposure carve-out). Needs a human decision: (a) route as a small upstream
   PR (recommended), or (b) explicitly authorize a local exception to the carve-out for this one
   file.
2. **Stale NOTE-block deletion sign-off**: 5 `NOTE:` blocks a prior cycle investigated and found
   NOT stale, deliberately left in place. Still flagged for explicit user sign-off on that
   judgment call.

## Next steps (for a future Phase 5 dispatch)

Count-5 tier down to its final 3 files (smallest first):
`Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/XuGuard.lean` (1146 lines),
`Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` (1435 lines),
`Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` (1532 lines). After those,
re-derive the worst-offender list fresh — the count-4 tier (~15+ files) becomes the new frontier.

Also worth a dedicated follow-up (not Phase 5 itself): the `lake shake` drift flagged above,
across ~15 untouched files — likely landed via an unrelated merge, same class of issue as the
cycle-12/13 `--wfail` regression but for the shake gate instead of the wfail gate.
