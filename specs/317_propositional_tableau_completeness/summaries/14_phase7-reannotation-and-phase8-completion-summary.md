# Phase 7 Re-annotation + Phase 8 Summary: Documentation Accuracy and Full CI Gate

- **Task**: 317 - Fill the remaining propositional/intuitionistic tableau completeness sorries
- **Plan**: plans/14_fuel-materialization-repair.md (v14, binding)
- **Phase**: 7 (re-annotation only, blocked phase not re-attempted) + 8 (single dispatch)
- **Session**: sess_1785294636_11f932
- **Status**: [COMPLETED]
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD

## What Was Done

No `Cslib/` proof work was in scope for this dispatch — no new proofs, no sorry closures, no
algorithm changes. Everything below is documentation-accuracy work plus the terminal CI gate.

### Objective A — Phase 7 re-annotation (per reports/17_timp-continuation-options.md)

`reports/17_timp-continuation-options.md` (dedicated blocker research, completed immediately
before this dispatch) found the closure route Phase 7's task list depended on structurally
unavailable in this codebase (the `applyAllTImpRules` self-copy channel was deliberately removed
by the ancestor-blocking calculus repair) and made two corrections to the record:

1. **F1**: reinstating the self-copy channel is termination-safe — already measured, not merely
   plausible, by the ancestor-blocking repair's own variant-selection probe (self-copy retained
   vs. removed both terminate at the identical saturated branch).
2. **F3 (decisive, newly found)**: a bare reinstatement would NOT by itself close Gap 1.
   `truthLemma`'s frame ranges over an AUGMENTED edge list (carrying the ancestor-blocking
   repair's loop-back edges), while any copy channel only reaches the algorithm's RAW edges —
   a gap strictly larger than the copy-channel question. The real remaining obligation is a
   loop-back transfer lemma, the same fact (at the implication shape) that task 430's
   atom-persistence bridge already needs at the atom shape.

Actions taken, all in `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`:

- Re-annotated the `truthLemma` T-imp `sorry` with the standard strategic-sorry comment
  convention (assumption / why-deferred / follow-up), matching how DP-2 is annotated. This sorry
  is now tracked as **DP-5** in the plan's Planned Strategic Sorries table, with follow-up
  task 430 (widened scope per reports/17's recommendation, not itself widened by this dispatch —
  that is a separate task-scope decision left to the user/orchestrator).
- Corrected the STOP-gate note's "Recommendation for continuation" paragraph with F1 and F3.
- Added a superseding "Update" paragraph to the plan's Phase 7 blocker section recording the
  same two corrections against the plan's own prose.
- **Phase 7's heading stays `[BLOCKED]`** — not flipped, not re-attempted, per the mandate.

### Objective B — Phase 8 proper

- **`intUniverse` docstring** (`Scheme.lean`, now ~line 1510-1531 — shifted from the plan's
  original 1585-1599 line numbers by earlier phases' edits): added a "Live development" note
  pointing at `intUniverseExt`/`WBound` as the engine's actual current world-bound account,
  keeping the pre-existing refutation record intact.
- **Engine-restructure documentation**: the `intFuel`→`intFuelExt` / per-branch-fuel story was
  already accurately documented at the `## Per-Branch-Fuel Expansion Engine` module note
  (verified, not edited). Expanded the `## Strict-Decrease Engine` section into a full module
  note: marks `intExpMeasure`/`intWork`/`intExpMeasure_step_lt`(+`_branch`) as
  retained-but-unconsumed by the live engine; records candidate (b) (WF recursion on the
  measure) as elective post-DP-2 future work and candidate (c) (proof/eval-side split) as
  rejected, both with their rejection rationale; records the `s ≲ 22` corpus-row feasibility
  envelope.
- **Divergence-witness note** (`Expansion.lean`): out of this dispatch's territory (task 574's
  file, explicitly excluded). Verified read-only that it already reads "Historical record,
  measured on the RETIRED global-fuel expansion loop" — already accurate, no edit needed.
- **`Completeness.lean` comment sync** (both `Intuitionistic/Completeness.lean` and
  `Minimal/Completeness.lean`): the monotonicity-bridge `sorry`s no longer misstate the blocker
  as awaiting the fuel-sufficiency fixpoint (that fixpoint is landed sorry-free, modulo the
  unrelated DP-2 fresh-mint sorry) — corrected to name the actual blocker: the same
  positive-formula persistence invariant DP-5 needs, here at the atom shape. The bridge sorries
  themselves are untouched (task 430's territory, per the plan's own instruction).
- **Optional conformance regression row**: skipped — genuinely optional per the plan's wording,
  and the existing 44-row corpus (verified green) already exercises the per-branch fuel path.
- **Sorry accounting**: enumerated below; matches the plan's expected terminal set exactly.
- **Full CI gate**: run in full, see Verification.

## Verification

All commands run from repo root, this dispatch.

| Gate | Result |
|---|---|
| `lake build` (full) | GREEN — 3311/3311 jobs |
| `lake exe checkInitImports` | GREEN — exit 0 |
| `lake lint` | **RED at repo level**, but zero findings against any of this task's three territory files (`Intuitionistic/Scheme.lean`, `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`) — every finding is a pre-existing unused-argument warning in unrelated modules (`Bimodal/**`, `LTL/**`, `Modal/Tableau/FrameSoundness.lean`, `Temporal/**`). This dispatch introduces no new lint debt; the repo-wide backlog is outside this task's `file_scope` and not a regression this dispatch caused. Reported explicitly rather than claimed as unearned full-green. |
| `lake exe lint-style` | GREEN — zero output |
| `lake test` | GREEN — full suite built successfully, `CslibTests.TableauConformance` (44-row corpus, incl. divergence-witness row 20) passed within the run; no observed timing regression |
| `lake exe mk_all --module` | SKIPPED — no new file was added this dispatch (plan's own conditional) |
| `lake shake --add-public --keep-implied --keep-prefix` | GREEN for all three territory files (zero import-drift findings); all other findings are in unrelated pre-existing files elsewhere in the repo, out of scope |
| `lean_verify` (scan_source: false) on `openBranch_countermodel`, `tableau_complete` (`Scheme.lean`), `intuitionisticTableau_complete` (`Intuitionistic/Completeness.lean`), `minimalTableau_complete` (`Minimal/Completeness.lean`) | All four: `{propext, Classical.choice, Quot.sound, sorryAx}` — exactly the expected axiom set, `sorryAx` present only via the four declared strategic sorries below, no unexpected axiom |

### Sorry Census (terminal state for this plan)

Direct grep for bare `sorry` (tactic-position, excluding comments/docstrings), this dispatch:

| # | File | Line | Division Point | Owner | Strategic |
|---|------|------|-----------------|-------|-----------|
| 1 | `Intuitionistic/Scheme.lean` | 633 | DP-5: `truthLemma` T-imp Gap 1 (implication-shape persistence) | task 430 | true |
| 2 | `Intuitionistic/Scheme.lean` | 2605 | DP-2: `intFreshMint_preserves_nw` (`hNW` fresh-mint preservation) | task 585 | true |
| 3 | `Intuitionistic/Completeness.lean` | 140 | DP-3: `intuitionisticTableau_complete` monotonicity bridge (atom-shape persistence) | task 430 | true |
| 4 | `Minimal/Completeness.lean` | 128 | DP-4: `minimalTableau_complete` monotonicity bridge (atom-shape persistence) | task 430 | true |

Exactly 4, matching the plan's expected terminal set. None closed, relocated, or weakened by this
dispatch — all four annotations updated for accuracy only.

## Plan Deviations

- The plan's Phase 8 task list named an edit to `Expansion.lean`'s divergence-witness note; this
  was **not made** because `Expansion.lean` is outside this dispatch's H7 territory (task 574's
  file). Verified read-only that the note is already accurate (describes the "RETIRED global-fuel
  expansion loop" correctly) — no stale claim survives there, so no edit was actually needed, but
  this is recorded as a deviation from the plan's literal task-list wording rather than silently
  matched.
- The optional conformance regression row was not added (explicitly optional; existing coverage
  judged sufficient — see above).
- Added a fifth sorry-inventory row (DP-5) not originally in the plan's Planned Strategic Sorries
  table, per the dedicated blocker research's recommendation (reports/17). This is a bookkeeping
  re-annotation of a pre-existing sorry, not a new placement — the plan itself already listed
  Phase 7's T-imp sorry as a target; DP-5 formalizes its terminal disposition.

## Task Completion Assessment

**Task 317 is complete as scoped by plan v14.** All phases have reached a terminal state:
Phases 1-6 and 8 `[COMPLETED]`; Phase 7 `[BLOCKED]` with a named, accepted owner (task 430,
scope widened per reports/17's recommendation — that scope widening itself is a decision for
task 430, not executed by this dispatch). No phase of this plan remains actionable. The four
remaining sorries are all strategic, all owned, all tracked, and the full CI gate is green except
for a pre-existing, out-of-scope repo-wide `lake lint` backlog that this dispatch neither caused
nor is responsible for clearing.

## Follow-ups

- **Task 430** (`prove_atom_persistence_upward_closure_for_intexpan`): recommend widening its
  scope from atom-persistence to positive-formula-persistence along the augmented accessibility
  relation, per reports/17's two-gate recommendation (Gate A: re-run the variant-selection probe
  against the post-repair tree for V1/V4; Gate B, gating: Lean-prototype the loop-back transfer
  lemma before any calculus change). This closes DP-3, DP-4, and DP-5 together if it succeeds.
  Not executed by this dispatch — a scope decision for task 430's own owner.
- **Task 585**: unchanged, still owns DP-2 (`intFreshMint_preserves_nw`).
- The repo-wide `lake lint` backlog (unused-argument warnings across `Bimodal/**`, `LTL/**`,
  `Modal/Tableau/FrameSoundness.lean`, `Temporal/**`) is out of this task's scope; flagged for
  visibility, not for action by this task.

## References

- `plans/14_fuel-materialization-repair.md` (Phase 7 blocker section + DP-5 row + Phase 8 tasks)
- `reports/17_timp-continuation-options.md` (blocker research this dispatch acted on)
- `reports/15_fuel-materialization-repair.md` §7 (Phase 8 doc-addition spec)
- `summaries/14_phase6-r1-restatement-fuel0-discharge-summary.md` (prior phase, sorry census
  baseline of 4 before this dispatch's DP-5 re-annotation)
