# Cycle 22 Handoff — Phase 5 Suppression Audit

**Date**: 2026-07-27
**Session**: sess_1785189125_8d6d8d
**Dispatch**: final cycle of this `/orchestrate` invocation's budget

## Summary

Processed 10 files this cycle, all committed individually after a scoped rebuild of the file
plus every direct downstream importer. This clears the count-3 tier entirely (4 files) and
opportunistically starts the count-2 tier (6 more files, chosen for being small/quick once the
count-3 worklist ran dry).

| File | Lines | Suppressions | Commit |
|---|---|---|---|
| `Bimodal/Metalogic/Soundness/Soundness.lean` | 845→869 | 3→0 | `37ac7f38` |
| `Bimodal/Metalogic/Decidability/Saturation.lean` | 708 | 3→0 | `efb08c0e` |
| `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` | 578 | 3→0 | `74fec4d4` |
| `Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` | 1072 | 3→0 | `1a14739f` |
| `Bimodal/Metalogic/Bundle/FMCSDef.lean` | 43 | 2→0 | `13515a71` |
| `Bimodal/Metalogic/BXCanonical/CanonicalChain.lean` | 92 | 2→0 | `3d50f988` |
| `Bimodal/FrameConditions/Compatibility.lean` | 105 | 2→0 | `a2c7f2f1` |
| `Bimodal/Metalogic/Bundle/Construction.lean` | 123 | 2→0 | `16d312b4` |
| `Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` | 127 | 2→0 | `c0a2c843` |
| `Bimodal/Metalogic/Bundle/BFMCS.lean` | 130 | 2→0 | `c8fa93ef` |

Also re-baselined the lint-suppression ratchet (`851278c7`, `check-lint-suppressions.sh
--update`), which had drifted stale across several prior cycles — now at 86 blanket
suppressions across 63 files repo-wide (12 upstream-carved-out; 72 across 49 files local-only
in-scope). Plan file updated with a full RESUME HERE rewrite including a live re-derived survey
of the entire remaining count-2 (19 files) and count-1 (30 files) tiers (`be235c9f`).

## Progress

- Suppression-audit progress: 268 → 278 sites audited cumulative (68 files fully processed).
- Local-only in-scope count: **72 blanket suppressions across 49 files** (down from 96/59 at
  cycle 21's close — a reduction of 24 sites / 10 files this cycle).
- Count-3, count-4, count-5 tiers are now fully cleared. Only count-6 (1 file, `Interface.lean`,
  3048 lines, deliberately deferred), count-2 (19 files), and count-1 (30 files) remain.

## Key Findings This Cycle

1. The Bimodal `ChronicleTypes.lean` needed and received the identical structure/c0-c5'
   `dupNamespace`-narrowing pattern as the Temporal file closed cycle 21 — confirmed the pattern
   transfers exactly, modulo an extra `fc : FrameClass` parameter on some conditions that shifts
   doc-comment wrap points but not the narrowing strategy.
2. A large file (`SinceSeedConsistency.lean`, 1072 lines) turned out cheaper than several
   mid-sized ones — only 7 genuine `flexible` sites surfaced, and the `setOption`/
   `unusedSimpArgs` blanket suppressions were both entirely unnecessary. Line count does not
   predict remaining-warning count; always re-derive live after removing the blanket lines.
3. Once a tier's tracked worklist runs dry mid-cycle, it's efficient to opportunistically clear
   several very-small next-tier files (several had zero downstream importers, making them
   near-free single-declaration fixes) rather than stopping. This materially increased this
   cycle's file-throughput (10 files vs. the ~5-7/cycle historical average).
4. Files under ~150 lines very often have only 1-2 suppressed categories and 1-4 total warning
   sites once the blanket line is removed. For tier navigation past the count-3 tier, small line
   count is now a stronger effort predictor than the suppression-count tier itself.
5. Reconfirmed the cycle-12/cycle-16 parse hazard: a `set_option ... in` line must go *above*
   the preceding doc comment, not between it and the declaration (caught once this cycle in
   `Saturation.lean`, corrected before commit).

## Verification (end of cycle)

- `lake build --wfail --iofail`: exit 1, exactly the 5 documented baseline sorry warnings
  (`FrameSoundness.lean:1252`, `Intuitionistic/Scheme.lean:570,2583`,
  `Intuitionistic/Completeness.lean:124`, `Minimal/Completeness.lean:118`), zero others.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake exe mk_all --module`: "No update necessary".
- `lake shake --add-public --keep-implied --keep-prefix Cslib`: exactly the 12 documented
  upstream-shared files, zero local-only findings.
- `lake lint`: zero matches on the 7 prevention categories (docBlame, defLemma,
  defsWithUnderscore, simpNF, unusedSectionVars, topNamespace, dupNamespace); 147 errors, all
  `unusedArguments` (out of scope, unchanged from baseline).
- `lake test`: exit 0.
- `bash scripts/check-lint-suppressions.sh`: exit 0, "86 (baseline ceiling 86)".
- Sorry census: 167 naive-grep matches / 37 declarations containing `sorry` (includes the
  `warn.sorry`-guarded pre-existing sorries not counted in the `--wfail` baseline).
- Vacuous-def grep: 1 (the single known pre-existing false positive,
  `Computability/URM/Basic.lean:92`, unrelated to this task).
- Axiom count: 26 (unchanged from baseline).
- Zero sorries added, discharged, or relocated this cycle. Zero axioms added.

## Resume Point

Next target: `Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean` (137 lines),
per smaller-files-first within the count-2 tier. Full live-derived survey of the count-2 and
count-1 tiers is recorded in the plan's RESUME HERE section (specs/575_repo_lint_hygiene_ci_gate_restoration/plans/01_lint-hygiene-ci-gate.md)
— re-verify counts live before trusting, since counts only ever go down.

Estimated remaining effort: roughly 4-6 more cycles, likely higher file-throughput per cycle
than historical average since the count-2/count-1 tail is mostly single- or double-suppression
files once `Interface.lean` (count-6) is set aside.
