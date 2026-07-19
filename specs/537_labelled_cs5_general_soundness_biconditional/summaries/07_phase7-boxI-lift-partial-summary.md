# Implementation Summary: Phase 7 (boxI_lift) — Partial

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994 Thm
  8.1.4's biconditional
- **Status**: [PARTIAL]
- **Started**: 2026-07-19T17:22:33Z
- **Completed**: 2026-07-19T18:57:00Z
- **Artifacts**: plans/03_direct-route-forest.md (Phase 7 section, partial-progress note)

## Overview

Phase 7 is the plan's sole concentrated-risk phase (audit: ~90% mathematically completable,
~60% chance of fitting a single dispatch — the risk flagged as engineering, not soundness).
This dispatch landed the recommended internal-decomposition helper (`raise_subtree`, the
downward-cascade half of the tree-cascade recursion) fully proven, sorry-free, and axiom-clean,
plus a small supporting lemma (`ht_le_of_reflTransGen`). The assembly step (`boxI_lift` itself,
the ancestor-walk half) was drafted, found unsound in its recursive structure via live
`lean_goal` inspection, and the fix was fully specified but not implemented within budget. This
matches the plan's explicitly sanctioned fallback ("land the green helper... write a partial
handoff... if it wants a second dispatch").

## What Changed

- Added `ht_le_of_reflTransGen` to `Soundness.lean`: rank is non-decreasing along forward
  `G.R`-reachability, a direct consequence of the graded-rank conjunct of `IsDerivationForest`.
- Added `raise_subtree` to `Soundness.lean`: given a node `p` already raised to a fixed target
  `wp`, raises `p` together with the forward-reachable closure through a chosen `Finset` of
  direct raw-neighbours, via repeated `cs5FCIncest_lift` (F1). Well-founded on
  `Set.ncard {q ∈ G.X | ht q ≥ ht p}` (strictly decreasing at each child, since graded rank
  forces `ht c = ht p + 1 > ht p`). ~170 lines.
- Added `public import Mathlib.Data.Set.Card` (needed for `Set.ncard`).
- Updated `plans/03_direct-route-forest.md`: Phase 7 heading `[NOT STARTED]` → `[PARTIAL]`,
  plus a partial-progress note recording exactly what landed and the precise remaining sub-goal
  (the corrected, Finset-exclusion-parametrized ancestor-walk induction statement).
- `boxI_lift` itself was **drafted, found unsound, and discarded before commit** — never
  landed with a `sorry` or any placeholder. The file contains no trace of the discarded draft.

## Decisions

- **Downward-cascade / ancestor-walk split**: the tree-cascade recursion decomposes cleanly into
  (a) raising a node + its own descendants (pure F1, `raise_subtree`, landed) and (b) walking up
  the unique-parent chain toward the root via F2, invoking (a) for sibling branches at each level
  (not yet landed). This split avoids ever needing a general BFS-uniqueness/cycle-freeness lemma
  over the raw `Graph` — disjointness facts are derived locally via a single `huniq` application
  at the last edge of whichever path would witness an overlap.
- **Well-founded measure**: `Set.ncard {q ∈ G.X | ht q ≥ ht p}` (not an explicit "distance from
  x" function) — strictly decreases at each child, avoiding the need to construct or reason
  about a bespoke BFS-distance function.
- **Soundness bug caught before code, not after**: the naive ancestor-walk induction (applying
  the same induction hypothesis unconditionally at each ancestor) was identified as unsound via
  `lean_goal` inspection of the actual proof obligations, before writing the buggy recursive
  call into the file — consistent with the postmortem constraint to machine-check stuck
  sub-goals rather than hand-waving past them.

## Impacts

- `boxI_lift` (Phase 7's target) and therefore the `boxI` producer case (Phase 8) remain
  incomplete. Phase 8 cannot proceed until Phase 7 completes.
- No Preserved Asset was touched; `cs5FCIncest`, `Graph`, and all landed Phases 1-6 lemmas are
  unregressed (confirmed via clean `lake build` of the whole file).
- Zero debt: no `sorry`, no new axiom, no vacuous definition.

## Follow-ups

- Continuation dispatch: implement `boxI_lift` using the corrected Finset-exclusion-parametrized
  induction specified in `plans/03_direct-route-forest.md`'s Phase 7 partial-progress note and
  `handoffs/07_phase7-boxI-lift-partial.md`. Estimated ~120-180 remaining lines, same proof style
  already exercised in `raise_subtree` — no new mathematical content, pure engineering
  completion of an already-identified fix.

## References

- Plan: `specs/537_labelled_cs5_general_soundness_biconditional/plans/03_direct-route-forest.md`
- Handoff: `specs/537_labelled_cs5_general_soundness_biconditional/handoffs/07_phase7-boxI-lift-partial.md`
- Progress: `specs/537_labelled_cs5_general_soundness_biconditional/progress/phase-7-progress.json`
- File: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`
- Audit: `specs/537_labelled_cs5_general_soundness_biconditional/reports/03_tree-shape-invariant-audit.md`
