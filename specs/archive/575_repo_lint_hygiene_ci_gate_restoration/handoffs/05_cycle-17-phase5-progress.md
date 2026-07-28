# Task 575 — Cycle 17 Handoff (Phase 5 Suppression Audit)

**Date**: 2026-07-27
**Scope of this dispatch**: Phase 5 (suppression audit) only. Final cycle of the prior
`/orchestrate` invocation (5 of 5) — this task is now paused pending a fresh dispatch.

## Summary

Processed 8 files this cycle, all committed individually after a clean scoped rebuild plus
downstream-importer rebuilds:

1. `Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` (5→0, commit `fb747416`)
2. `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` (5→0, commit `fdb6549d`)
   — closes the count-5 tier entirely.
3. `Bimodal/Metalogic/Separation/Eliminations.lean` (6→1, commit `a98d657a`) — the 1 remaining
   line is a permanent, correct non-`in` `style.openClassical` suppression (persistent
   `open Classical`), not residual work.
4. `Bimodal/Metalogic/BXCanonical/TruthLemma.lean` (4→0, commit `20830b5f`)
5. `Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean` (4→0, commit `f0f0bc18`)
6. `Bimodal/Metalogic/ConservativeExtension/Substitution.lean` (4→0, commit `fea58a05`)
7. `Bimodal/Metalogic/Algebraic/ParametricTruthLemma.lean` (4→0, commit `5f549c8f`)
8. `Bimodal/Metalogic/Algebraic/RestrictedParametricTruthLemma.lean` (4→0, commit `97f65e5e`)

Ratchet: 223 → 188 blanket suppressions (35 fewer). Plan updated and committed separately
(commit `84896090`).

## Live re-derivation of the local-only/upstream split

A per-file `git cat-file -e upstream/main:<path>` check (not a cached repo-wide subtraction) on
every file currently carrying a blanket suppression found:

- **188 total** blanket suppressions
- **174 local-only, in-scope**, across **78 files**
- **14 upstream-carved-out**, across **14 files** (unchanged this cycle — correctly out of scope)

This is now the authoritative denominator for Phase 5's remaining work; the plan's previous
"209" figure is superseded.

## What remains

- Count-6 tier: 4 files left (`RecursiveWalks.lean`, `MainElimination.lean`, `Interface.lean`
  — 3048 lines, do not pick first — `ChronicleToCountermodelBasic.lean`).
- Count-5 tier: **empty**.
- Count-4 tier: 6 files left (`Separation/Hierarchy/HierarchyDefs.lean`,
  `Separation/DedekindZ/QLemma.lean`, `ConservativeExtension/ExtFormula.lean`,
  `BXCanonical/Frame.lean`, `BXCanonical/Chronicle/RRelation.lean`,
  `Foundations/Logic/Metalogic/Chronicle/RRelation.lean`).
- Below that: a count-3/count-2/count-1 tail of roughly 68 more files, not yet individually
  surveyed.

**Effort estimate**: this cycle cleared 35 sites in one dispatch — faster than the ~20-27
sites/cycle historical average, because 5 of the 8 files were small (≤330 lines) with mostly
mechanical fixes. At a blended ~20-30 sites/cycle rate, the remaining 174 sites are roughly
**6-9 more cycles**.

## New safety findings this cycle

1. A file whose `style.openClassical` suppression targets a persistent, non-`in` `open Classical`
   correctly bottoms out at 1 remaining blanket line (the non-`in` `set_option` immediately
   before the `open` statement), not 0 — this is the permanent correct end state for that
   category, not incomplete work. Established precedent: `ChronicleToCountermodelBasic.lean`,
   `DedekindZ/QLemma.lean`.
2. `lake lint`'s `unusedArguments` findings (147 repo-wide, confirmed pre-existing via a fresh
   `lake lint` run and cross-checked against files this cycle never opened) are a distinct
   environment linter from this phase's `unusedSectionVars`/`unusedDecidableInType` build-time
   syntax-linter targets. Not one of the agent's own 7 post-lint-check categories
   (docBlame/defLemma/defsWithUnderscore/simpNF/unusedSectionVars/topNamespace/dupNamespace).
   Do not attempt to fix opportunistically — removing a "provably unused" instance argument would
   alter a declaration's elaborated signature, barred by the hygiene-only hard constraint.

## Verification

Full CSLib CI pipeline re-run clean at cycle end:
- `lake build --wfail --iofail`: exactly 5 baseline sorry warnings, zero new
- `lake exe checkInitImports`: clean
- `lake lint`: 147 pre-existing unusedArguments findings (out of scope, see above), zero
  docBlame/defLemma/defsWithUnderscore/simpNF/unusedSectionVars/topNamespace/dupNamespace
- `lake exe lint-style`: clean
- `lake shake --add-public --keep-implied --keep-prefix`: exactly the 12 upstream-shared files
- `lake exe mk_all --module`: "No update necessary"
- `lake test`: exit 0, same 5 baseline sorry warnings plus the one pre-existing unrelated
  `backward.privateInPublic` warning in `CslibTests/FreeMonad.lean`
- True sorry census (comment-stripped method): 28, unchanged
- Vacuous-def grep: unchanged, single pre-existing false positive
  (`Computability/URM/Basic.lean:92`)
- Axiom count: unchanged at 26
- `git diff` across every file touched this cycle: zero `sorry` lines touched

## Carried forward, NOT re-investigated (per delegation instruction)

Phase 7's two blockers, unchanged from prior cycles:

1. **NOTATION.md upstream-PR-vs-local-exception decision**: `NOTATION.md` is confirmed
   byte-identical to `upstream/main`. Needs a human decision — route as a small upstream PR
   (recommended), or explicitly authorize a local exception to the carve-out.
2. **NOTE-block-deletion sign-off**: a prior cycle found the "stale" premise for 5 `NOTE:` block
   deletions false and declined to execute them as literally instructed. Still flagged for
   explicit user sign-off on that judgment call.

Neither blocks continued Phase 5 progress.
