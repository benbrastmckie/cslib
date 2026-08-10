# Implementation Summary: Task #605

- **Task**: 605 - establish_minbranchbotforces_upward_closure_at_bot
- **Status**: Implemented (all 6 phases completed)
- **Plan**: `specs/605_establish_minbranchbotforces_upward_closure_at_bot/plans/01_statement-shape-fix.md`
- **Research**: `specs/605_establish_minbranchbotforces_upward_closure_at_bot/reports/01_minbranchbotforces-upward-closure.md`

## Overview

Landed the research's verified statement-shape fix (option A): `openBranch_countermodel`
(`Scheme.lean`) gained a third existential conjunct -- upward-closure of `S.modelBot b` -- and
`tableau_complete`'s `hvalid` premise gained the matching hypothesis. This closed DP-4
(`minimalTableau_complete` in `Minimal/Completeness.lean`) entirely: the propositional tableau
completeness chain's sorry census went from 3 to 2, with the two survivors being the same single
open obligation (`openBranch_countermodel`'s existential) shared by both DP-3 (intuitionistic)
and, formerly, DP-4 (minimal) -- DP-4 is no longer a separate residual.

The fix required a universe pin (`minimalTableau_complete` now takes `MValid.{_, 0} φ`, since the
countermodel frame is built from `Nat : Type 0` while `MValid.{u, v}` quantifies
`World : Type v`), resolved by a `ULift`-transport universe-invariance bridge
(`mvalid_descend` / `mvalid_universe_invariant`) so `instDecidableDerivableMinPropAxiom` keeps
its original, unpinned public statement.

The plan's six phases sequenced this into landable, always-green steps: land the regression test
first, land the `χ`-generalization and universe bridge independently and additively, then apply
the shape fix as one declared atomic batch across four files, rewrite the in-source annotations
to the resolved disposition, and close with the full CSLib CI gate.

## Phase-by-Phase Results

| Phase | Description | Result |
|-------|-------------|--------|
| 1 | Baseline capture, patch-currency check, refutation test landing | Confirmed baseline sorry census = 3 (`Scheme.lean:8034`, `Intuitionistic/Completeness.lean:170`, `Minimal/Completeness.lean:166`); confirmed the saved `verified-shape-fix.patch` still applied cleanly (`git apply --check` exit 0); confirmed sibling task 609 had not yet landed in `Intuitionistic/Scheme.lean`. Landed `CslibTests/MvalidBotShapeRefutation.lean` (new, 5 theorems, sorry-free) plus its `CslibTests.lean` import. |
| 2 | Chi-generalization and sub-frame monotonicity in `Scheme.lean` | Added `isAccessible_go_subset_mono`, `isAccessible_subset_mono`, `intAccessPreorder_mono_subset` (private/public monotonicity lemmas under superset edge-list inclusion); generalized `openBranch_rawEdges_upward_closed` from `χ := .atom p` to arbitrary `χ`; added `openBranch_rawEdges_both_upward_closed` deriving both the valuation and `⊥`-shape upward-closure facts at one shared `edges` witness. All production docstrings (no `PROBE` markers). Zero external consumers broken (grep-confirmed). |
| 3 | Additive universe-invariance bridge in `DecisionProcedure.lean` | Added `mvalid_descend` (`ULift` transport, `Type v → Type 0`) and `mvalid_universe_invariant` (full iff) as purely additive, sorry-free theorems -- landed before any universe pin existed, so the module stayed green throughout. Added `omit [DecidableEq Atom] [Hashable Atom] in` on `mvalid_descend` to clear an `unusedSectionVars` warning surfaced by the build. |
| 4 | Statement-shape fix, DP-4 closure, and universe pin (atomic batch) | Four files updated together: `Scheme.lean` (third conjunct on `openBranch_countermodel`, matching `hvalid` premise + 4-tuple destructure on `tableau_complete`), `Intuitionistic/Completeness.lean` (mirrored conjunct, trivial `_hbuc` since `intScheme.modelBot = fun _ => False`), `Minimal/Completeness.lean` (mirrored conjunct, universe pin, DP-4 `sorry` replaced by the direct `@h Nat ... _huc _hbuc 0` instantiation), `Minimal/DecisionProcedure.lean` (pinned `minimalTableau_decides`/`instDecidableMValid`, routed `instDecidableDerivableMinPropAxiom` through the bridge). Full `lake build` green at 3325 jobs (matching the research report's verification record); `lake test` green at 9397 jobs. |
| 5 | Rewrite in-source annotations to the resolved disposition | Rewrote `minimalTableau_complete`'s and `minOpenBranch_countermodel`'s docstrings (retired the "two upward-closure premises / DP-4 is open" framing); updated both modules' "Notes on sorry" sections for the 3->2 census; corrected DP-3's docstring and inline comment, which had claimed a one-liner "would type-check" -- the research proved that claim false, so the docstring now records the universe-pin requirement instead; updated `Scheme.lean`'s `openBranch_countermodel`/`tableau_complete` docstrings to describe the third conjunct and the sub-frame transfer via `openBranch_rawEdges_both_upward_closed`. Zero stale-phrase hits, zero task-number citations (grep-confirmed). |
| 6 | Full CSLib CI gate and zero-debt verification | All 7 pipeline steps pass (see table below). Sorry census confirmed 3->2. Zero new axioms (`lean_verify` on `minimalTableau_complete`, `minimalTableau_decides`, `instDecidableMValid`, `instDecidableDerivableMinPropAxiom` all show the pre-existing `{propext, sorryAx, Classical.choice, Quot.sound}` profile, `sorryAx` inherited from `openBranch_countermodel`'s remaining sorry). Zero new vacuous definitions. |

## Verification Gate Table (Phase 6)

| Gate | Result |
|------|--------|
| `lake build` (full project) | green, 3325 jobs |
| `lake exe checkInitImports` | exit 0, clean |
| `lake lint` | zero findings in the five touched files (373 pre-existing findings repo-wide, all outside this task's scope) |
| `lake exe lint-style` | exit 0, clean |
| `lake shake --add-public --keep-implied --keep-prefix` | zero findings in the five touched files |
| `lake exe mk_all --module` | "No update necessary" (`CslibTests.lean`'s import was already hand-added in Phase 1; `Cslib.lean` untouched since no new `Cslib/` file was added) |
| `lake test` | green, 9397 jobs |
| Sorry census (propositional tableau completeness chain) | 2 (`Scheme.lean:8124` `openBranch_countermodel`, `Intuitionistic/Completeness.lean:191` DP-3) -- down from 3 |
| Vacuous definitions | zero introduced (pre-existing repo-wide hit in `Cslib/Computability/URM/Basic.lean` is out of scope and unrelated) |
| New axioms | zero (`axiom` count unchanged at 26 repo-wide, none in this task's diff) |

## Deviations from the Plan

None. All six phases executed as written, in order, with the plan's declared `Commit Mode:
atomic-batch` honored for Phase 4 (all four files verified together before any commit; no
intermediate red state committed).

## Coordination Notes for Sibling Task 609

Recorded here per the plan's Coordination section, for task 606 to reconcile:

1. `openBranch_countermodel`'s existential now carries a **third conjunct**
   (`S.modelBot b`'s upward closure). Any future discharge of this lemma's `sorry` must produce
   all three conjuncts; the witness for the third is already available via
   `openBranch_rawEdges_both_upward_closed` (Phase 2), at the same `edges` as the first.
2. The `Minimal/Completeness.lean` DP-4 one-liner is **already closed** by this task -- no
   remaining call-site work there for 609.
3. DP-3's docstring at `Intuitionistic/Completeness.lean` now records that its previously-quoted
   one-liner does **not** type-check as written, and names the exact universe-pin fix
   (`.{_, 0}` on `h`, `ULift` transport) `Minimal/DecisionProcedure.lean` already builds for
   `MValid`, ready to mirror for `IValid` when DP-3 is eventually closed.
4. Territory: this task touched the `isAccessible` monotonicity region,
   `openBranch_rawEdges_upward_closed`/`_both_upward_closed`, and `openBranch_countermodel`
   /`tableau_complete` at the end of `Scheme.lean`. 609's `intStepBranch`/`intExpandBranches.go`
   rule-selection region and `IReuseContain` threading are disjoint and untouched.

## AI Tools Used

This implementation was executed by Claude Code (Anthropic) following a pre-verified plan and a
pre-verified patch (`verified-shape-fix.patch`, produced during the task's research phase and
re-verified for currency against the current tree before landing). All edits were re-derived
from the verified patch's content (not applied verbatim via `git apply`, to allow docstrings to
be rewritten from probe-era to production wording per CSLib's lint-prevention rules) and
independently re-verified via `lake build`/`lake test`/`lean_verify` at each phase.
