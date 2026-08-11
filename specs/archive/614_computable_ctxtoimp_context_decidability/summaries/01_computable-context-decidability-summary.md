# Implementation Summary: Task #614

- **Task**: 614 - Give `ctxToImp` a computable definition so the four context-based `Decidable`
  instances for the propositional sequent calculi stop being `noncomputable`
- **Status**: [COMPLETED]
- **Started**: 2026-08-11T01:20:08Z
- **Effort**: ~3 hours
- **Dependencies**: None
- **Artifacts**: plans/01_computable-context-decidability.md,
  reports/01_computable-context-decidability.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md,
  `.claude/rules/cslib.md`, `.claude/rules/plan-compliance.md`

## Overview

Made `instDecidableLJDerivable`, `instDecidableDerivableInIPL`, `instDecidableLKDerivable`, and
`instDecidableDerivableInCPL` fully computable, with no new typeclass hypothesis and no public
statement change, following the plan's verified Route 3 (`Quotient.recOnSubsingleton` subsingleton
elimination). `ctxToImp` itself stays `noncomputable` — this is a genuine mathematical fact (a
computable `Finset α → β` must be permutation-invariant, and `listToImp` is not), not a defect,
and the plan's own research confirmed the task's title ask is impossible while its stated goal is
fully achievable by a different route. All four plan phases completed; all changes build green,
introduce zero new `sorry`/axioms/vacuous definitions, and pass the full seven-step CSLib CI
order.

## What Changed

- `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean`:
  - Added `ljListDerivableDecidable`, a computable list-level `Decidable` helper preserving the
    `letI`/`ivalid_universe_invariant` universe bridge verbatim.
  - Rewrote `instDecidableLJDerivable`'s body to eliminate `Γ.val` via `Quotient.recOnSubsingleton`
    into the new helper; dropped `noncomputable`.
  - Dropped `noncomputable` from `instDecidableDerivableInIPL` (body unchanged).
  - Corrected five docstring sites (module Strategy/Main Results block, `ctxToImp`,
    `ljProofDeductionFwd`, `ljProofDeductionBwd`, `instDecidableLJDerivable`) to state that the
    three remaining `noncomputable` markers are inherent, not incidental.
- `Cslib/Logics/Propositional/SequentCalculus/LK/Decidability.lean`: the same shape —
  `lkListDerivableDecidable` (no universe bridge needed; `instDecidableTautologyTableau` is
  unpinned), rewritten `instDecidableLKDerivable`, `noncomputable` dropped from
  `instDecidableDerivableInCPL`, four docstring sites corrected.
- `CslibTests/ContextDecidability.lean` (new): `#guard_msgs in #eval` conformance checks —
  non-empty-context LJ/LK derivations (positive and negative), the LJ/LK excluded-middle
  intuitionistic/classical contrast, and the `DerivableIn` forms for IPL/CPL. Registered in
  `CslibTests.lean` alphabetically (between `CLL` and `DFA`).
- `scripts/axiom-census-baseline.txt`: re-baselined (see Plan Deviations — the diff differs from
  the plan's prediction).
- `Cslib.lean`: one line added (`Cslib.Foundations.Logic.Operators`) — pre-existing, unrelated
  barrel drift from task 619, surfaced and fixed by this phase's `mk_all --module` run.

## Decisions

- Followed the plan's Route 3 verbatim: never inlined the list-level helper into the instance
  body (the plan records this as provably non-elaborating — the representative appears as `⟦l⟧`,
  not `↑l`, inside the `Quotient.recOnSubsingleton` lambda), and used
  `List.toFinset_eq h : ⟨↑l, h⟩ = l.toFinset` in the stated orientation, not `.symm`.
- Left `ctxToImp`, `ljProofDeductionFwd`, `ljProofDeductionBwd`, `lkProofDeductionFwd`,
  `lkProofDeductionBwd` `noncomputable`, per the plan — their noncomputability is inherent and no
  decision procedure depends on them any more.

## Plan Deviations

- **Axiom-census prediction did not hold.** The plan predicted `bash scripts/check-axiom-census.sh`
  would fail first (with `ljListDerivableDecidable` newly tainted via
  `intuitionisticTableau_complete`), then `--update` would add exactly one line. Instead, the live
  run reported 17 baseline declarations `IMPROVED` (no longer sorryAx-tainted at all, including
  `instDecidableLJDerivable`/`instDecidableDerivableInIPL`/`instDecidableIValid`/
  `intuitionisticTableau_complete` and their full chain) and exited 0 with **zero regressions**.
  Neither new helper appears in the live tainted set at all. Investigated via `git log`/
  `git status`: the 17 removed declarations all live in
  `Tableau/Intuitionistic/{Completeness,Scheme,DecisionProcedure}.lean` and
  `Tableau/Minimal/{Completeness,DecisionProcedure}.lean` — none touched by this task's Phases
  1-3 — and were already sorry-free per already-committed prior work (task 616 and a
  predecessor) that had never re-baselined the ratchet. Re-tightened the stale, improvement-only
  ratchet (`--update`) since the script itself flags this as safe and recommended, and the actual
  diff (17 lines removed, 0 added) was inspected before committing per the plan's own
  risk-mitigation instruction.
- **One line of pre-existing, unrelated `Cslib.lean` barrel drift** (missing
  `Cslib.Foundations.Logic.Operators`, committed by task 619) was surfaced by this phase's
  `lake exe mk_all --module` run and fixed, since it is required for barrel completeness/CI and
  is outside this task's own edits.
- Both deviations are annotated inline in the plan's Phase 4 checklist.

## Verification

- `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability`,
  `...LK.Decidability`, `CslibTests.ContextDecidability`, `CslibTests` (barrel), and the full
  `lake build` (3325 jobs): all green. Only pre-existing warnings unrelated to this task
  (`unusedDecidableInType` in `Tableau/{Intuitionistic,Minimal}/DecisionProcedure.lean`,
  `simp_all`-flexible in `Modal/Tableau/FrameCompleteness.lean`).
- `grep -n "^noncomputable "` on both Decidability files: exactly 3 hits (LJ) and 2 hits (LK),
  all on the deliberately-retained declarations. Zero of the four target instances carries
  `noncomputable`.
- `lake exe checkInitImports`: exit 0.
- `lake lint`: 0 hits in either target file (its 149 pre-existing errors are all in unrelated
  subtrees, e.g. Bimodal/Automata).
- `lake exe lint-style`: exit 0.
- `lake test`: exit 0 (includes the new `CslibTests/ContextDecidability.lean` `#guard_msgs`
  assertions, all passing).
- `lake exe mk_all --module`: converges to "No update necessary" after the one unrelated fix
  above.
- `bash scripts/check-axiom-census.sh`: exit 0, `OK: sorryAx-tainted set matches the baseline
  exactly` (25 == 25) after `--update`.
- Sorries/vacuous defs/axioms: 0 `sorry`, 0 vacuous definitions, 0 new `axiom` in
  `LJ/Decidability.lean`, `LK/Decidability.lean`, and `CslibTests/ContextDecidability.lean`.
- Semantic confirmation: LJ `{p, p → q} ⊢ q` → `true` (the task's target case), LJ `{q} ⊢ p` →
  `false`, LK counterparts match, LJ `∅ ⊢ p ∨ ¬p` → `false`, LK `∅ ⊢ p ∨ ¬p` → `true`.

## Impacts

- The library can now compute whether a **non-empty** context proves a formula for LJ, LK, IPL,
  and CPL, closing the gap the task's title/goal both targeted.
- No change to any public statement: `Ctx Atom = Finset (Proposition Atom)` unchanged, all four
  instances keep exactly `[DecidableEq Atom] [Hashable Atom]`.

## Follow-ups

- The LM/minimal-logic context decidability item noted in the research report (§11) can inherit
  this exact Route 3 shape (`Quotient.recOnSubsingleton` + a list-level helper) rather than the
  `Finset.toList` taint, given `mvalid_universe_invariant`/`instDecidableMValid` mirror the
  intuitionistic pair.
- The closed-context restriction on the tableau TFAE folds (`ProofSystemEquivalence.lean:176-186`)
  is now revisitable, per the original task description's follow-on note, but remains out of
  scope here.

## References

- `specs/614_computable_ctxtoimp_context_decidability/plans/01_computable-context-decidability.md`
- `specs/614_computable_ctxtoimp_context_decidability/reports/01_computable-context-decidability.md`
