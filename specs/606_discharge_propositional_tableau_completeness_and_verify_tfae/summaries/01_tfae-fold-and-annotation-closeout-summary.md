# Implementation Summary: Discharge propositional tableau completeness and verify TFAE fold

- **Task**: 606 - Discharge or restate the four propositional tableau completeness theorems and verify the TFAE fold
- **Status**: [COMPLETED]
- **Started**: 2026-08-10T15:40:46Z
- **Completed**: 2026-08-10T16:12:05Z
- **Effort**: ~2.5 hours (plan estimate: 5 hours)
- **Dependencies**: 603, 604, 605, 609 (all complete)
- **Artifacts**: plans/01_tfae-fold-and-annotation-closeout.md, reports/01_tableau-completeness-ground-truth.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Research established that all four DP sites (`intuitionisticTableau_complete`,
`minimalTableau_complete`, `truthLemma`, `openBranch_countermodel`) were already sorry-free and
axiom-clean, so scope items (a)/(b) required no work. This implementation executed the plan's
remaining two items: (1) landing three new four-node TFAE theorems that fold each tableau
decision procedure into the corresponding closed-formula proof-system equivalence, and (2)
bringing roughly a dozen stale annotation blocks across seven files into agreement with the
sorry-free landed state, eliminating an internal contradiction where one docstring declared
"KNOWN IMPOSSIBLE" a reconciliation a sorry-free proof performs twenty lines above it.

## What Changed

- **`Cslib/Logics/Propositional/ProofSystemEquivalence.lean`**: added `cplProofSystemsWithTableauTfae`,
  `iplProofSystemsWithTableauTfae`, `mplProofSystemsWithTableauTfae` in a new `WithTableau`
  section (local `variable [Hashable Atom]`, `omit` on the CPL theorem since `classicalTableau`
  only needs `DecidableEq Atom`). Reused the research-verified probe proof bodies verbatim,
  including the term-mode `Iff.trans` composition for the IPL/MPL universe-invariance step (`rw`
  cannot solve the universe metavariable). Added four `public import`s and updated the module
  docstring's `Main Results`/`Dependencies` lists and opening prose.
- **`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`**: rewrote the
  `openBranch_rawEdges_upward_closed`/`_both_upward_closed` docstrings to remove the "KNOWN
  IMPOSSIBLE" claim and record retention as the durable raw-frame record; re-tensed five
  "REFUTED at the augmented frame" claims to explicit pre-repair/historical framing, naming the
  repair (`intStepBranchPrio` beta-priority scheduling plus the `IReuseFrozenOrigin`/bare
  `IReuseContain` freeze machinery); closed the monotonicity STOP-gate note, the self-contradicting
  "Gap 1 ... remains the sole blocker" heading, the DP-5 "stays `sorry`" claim, `truthLemma`'s
  "deferred completeness obligation" opening, the DP-2 strategic-sorry paragraph,
  `tableau_complete`'s conditional sorry-free framing, and an incidentally-discovered stale
  "still open" claim on `IAllReuseFrozenOrigin` (item (d), contradicted by task 609's own commit
  history); replaced two drifted internal line-number citations with declaration names.
- **`Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`**: re-tensed
  `intFImpReuseWitnessAnc?`'s "Recorded limitation ... never re-validated" docstring into explicit
  PRE-REPAIR/POST-REPAIR sections, preserving the `phiRef1` counterexample verbatim and naming
  `intStepBranchPrio`/`IReuseFrozenOrigin` as the closing mechanism.
- **`Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`** and
  **`Tableau/Minimal/Completeness.lean`**: rewrote the identical "single deferred completeness
  obligation now lives in `openBranch_countermodel`" phrase in both files; confirmed (did not
  edit) each file's DP-3/DP-4 docstrings, already accurate.
- **`Cslib/Logics/Propositional/Metalogic/IntDecidability.lean`** and **`MinDecidability.lean`**:
  rewrote the "payoff is low while `openBranch_countermodel` ... remains open" claim in both
  files; replaced stale `Scheme.lean:234` citations with the bare declaration name `truthLemma`.
  Confirmed (did not edit) `Tableau/Minimal/DecisionProcedure.lean`'s already-correct past-tense
  note.

All fifteen commits below are docstring/comment-only except Phase 1, which adds three new
theorems and zero edits to any existing declaration body or statement.

## Decisions

- Followed the planner's three binding decisions verbatim: no tableau node on the context-based
  TFAEs (decision a), the three adjacent Metalogic/Expansion files are in scope (decision b), and
  both raw-edges lemmas are retained with corrected docstrings rather than deleted (decision c).
- Deviation (documented in the plan, Phase 3): the `Scheme.lean:908-941`-area self-copy-channel
  paragraph combined a REFUTED clause and a "still open ... surviving existential" clause in one
  sentence; both were re-tensed together in Phase 3 rather than leaving the sentence half-stale,
  and Phase 4 verified (did not re-edit) the result.
- Additional in-scope fix found during the Phase 4 sweep, not pre-declared: `Scheme.lean`'s
  `IAllReuseFrozenOrigin` docstring claimed plan Phase 6 task-list item (d) was "still open",
  directly contradicted by task 609's own commit history and by the `hPendingARFO`/`hDoneARFO`
  hypotheses now present in `intExpandBranches_openBranch_sat`'s statement. Rewritten to "closed".

## Impacts

- The task's HARD CONSTRAINT (tableau nodes must fold into the CPL/IPL/MPL TFAEs) is now
  satisfied by a type-checked artifact rather than an untested assumption.
- `Scheme.lean`'s internal contradiction (a docstring declaring impossible what a sorry-free
  proof performs nearby) is eliminated; the file's account of its own state is now consistent
  with `lean_verify`'s machine-checked axiom profiles.
- No public API was widened: the `[Hashable Atom]` constraint is scoped to the new `WithTableau`
  section only, and the six pre-existing TFAE theorem signatures are untouched.
- The two pre-existing `linter.unusedDecidableInType` warnings on `ivalid_universe_invariant` /
  `mvalid_universe_invariant` were confirmed unchanged, not "fixed" as a side effect.

## Follow-ups

None identified. The task's declared Non-Goals (context-based tableau TFAE nodes, widening
`[Hashable Atom]` onto the existing six signatures, deleting refutation records, "fixing" the two
pre-existing linter warnings) remain out of scope and were not touched.

## Verification (Phase 6 gate)

- `lake build` (full project): exit 0, 3325 jobs.
- `lake test`: exit 0; `CslibTests.BetaSplitRefutation` rebuilt standalone and clean.
- `lake exe lint-style`: exit 0, repo-wide.
- `lake exe checkInitImports`: exit 0.
- `lake lint`: 149 pre-existing findings repo-wide, zero in any of the seven in-scope files.
- `lake shake --add-public --keep-implied --keep-prefix`: none of the seven in-scope files
  appear in the suggested-changes list. `lake exe mk_all --module`: "No update necessary".
- `lean_verify` on all seven target declarations (`intuitionisticTableau_complete`,
  `minimalTableau_complete`, `truthLemma`, `openBranch_countermodel`,
  `cplProofSystemsWithTableauTfae`, `iplProofSystemsWithTableauTfae`,
  `mplProofSystemsWithTableauTfae`): all report exactly
  `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.
- Zero `sorry` tactic occurrences in all seven in-scope files (every `sorry` hit is a prose
  mention inside a docstring/comment, manually reviewed). Zero new vacuous definitions
  repo-wide (the one pre-existing hit, `Cslib/Computability/URM/Basic.lean:92`, is unrelated and
  unchanged). Zero new axioms (26 `^axiom ` declarations repo-wide at both baseline and HEAD).

## References

- `specs/606_discharge_propositional_tableau_completeness_and_verify_tfae/reports/01_tableau-completeness-ground-truth.md`
- `specs/606_discharge_propositional_tableau_completeness_and_verify_tfae/plans/01_tfae-fold-and-annotation-closeout.md`
- Probe file (research-verified, reused verbatim, not part of the repo tree):
  `/tmp/claude-1000/-home-benjamin-Projects-cslib/2b7a4a92-9db5-490b-8511-e9e6eb44721a/scratchpad/tfae_probe.lean`
