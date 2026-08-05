# Continuation Handoff: Plan 08, Wave 8 Complete (Phases 7.3, 7.4, 8)

- **Plan**: `plans/08_reformulated-s4-redirect-sound-inv.md` (v7)
- **Date**: 2026-08-05
- **Dispatch scope**: wave 8 only (Phases 7.3, 7.4, 8), per delegation instructions

## What landed this dispatch

All three phases closed sorry-free, committed individually, with the sorry census held at
exactly 1 (`FrameSoundness.lean:1251`) and axioms exactly `{propext, Classical.choice,
Quot.sound}` throughout.

1. **Phase 7.3** — `S4RedirectSoundInv_diaPos_blocked`: the diamond-positive mint-blocked mirror
   of the landed `S4RedirectSoundInv_boxNeg_blocked`. The mirror held literally, no
   box/diamond asymmetry found. 118 lines (vs. ~60 estimated — docstring plus the full duplicated
   discharge account for the difference).

2. **Phase 7.4 — the plan's single kill gate — PASSED (outcome i)**. Six lemmas formalize P2 (the
   branch-growth antitone property conjunct (d) needs at a primary-scan/non-mint step, where
   `hmint` is unavailable):
   - `filterMap_any_guard_isEmpty_growth`, `modalTSelf_isEmpty_growth` (generic shrinking facts)
   - `modalApplyOneS4Rules_boxPos_notApplicable_growth` / `_diaNeg_notApplicable_growth`
     (three-layer K/T/4-rule assembly)
   - `modalApplyOne_fst_eq_of_not_box_diamond` (full b-independence for non-box/diamond shapes)
   - `modalApplyOneS4Keyed_notApplicable_growth` (the assembled target, general over every
     signed-formula shape; mint shapes close vacuously since they're always `.linear`)

   The edge-growth half needed **no new lemma** — fully covered by Phase 7.2's
   `modalApplyOneS4Rules_{boxPos,diaNeg}_notApplicable_of_saturated` (already exercised at
   `acc.addEdge`) plus the pre-existing acc-independence lemmas
   (`modalApplyOne_fst_eq_of_not_boxPos_diaNeg`/`modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg`).
   243 lines, matching the ~250-line estimate; only `FrameCompleteness.lean` touched.

3. **Phase 8** — `S4RedirectSoundInv_not_isModalClosed`: the terminal payoff. A classically
   closed branch contradicts `S4RedirectSoundInv`. Reuses `modalClosed_unsat` by supplying its
   discarded edge-realization hypothesis with a vacuous witness at `Accessibility.empty` (the
   same idiom already used at several call sites in this file cluster), avoiding any need to
   reconstruct a genuine edge witness from the weakened conjunct (b). 34 lines.

## Verification performed

- Scoped `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green after every sub-step.
- `#print axioms` via `lake env lean` (not `lean_verify`, per this task's standing note about a
  spurious `sorryAx` on this file cluster) on every new declaration.
- `lake exe lint-style Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` clean throughout.
- `lake exe checkInitImports` clean.
- Sorry census (`grep -rn '^\s*sorry\s*$\|[^a-zA-Z_]sorry\s*$'`) exactly 1 at every checkpoint.
- Downstream consumer `CslibTests/ModalFrameSeparation.lean` (the only file importing
  `FrameCompleteness.lean`) still builds green.
- `git diff --stat` confirmed file-scope compliance at every phase (only `FrameCompleteness.lean`
  touched); `git diff | grep '^-[^-]'` confirmed every phase's diff is purely additive — no
  preserved declaration (per the Testing & Validation checklist) was touched.

## What is NOT done, explicitly

Per the plan's own dependency table, **wave 9 (Phases 7.5, 7.6, 7.7) is now unblocked** (Phase
7.4's gate passed) but was **not attempted this dispatch** — out of this dispatch's assigned
scope (wave 8 only). Wave 10 (Phase 7.8, the dispatcher theorem, `atomic-batch` commit mode)
remains blocked until wave 9 closes in full. Phase 9's capstone-scope decision and Phase 10's
regression/CI close-out are untouched.

**P3 ("mint seed covers the 4-payload") is still not attempted** — it is Phase 7.6's own first
task, per the plan.

## Next continuation step

Dispatch wave 9: Phases 7.5 (propositional/non-mint arm), 7.6 (mint-unblocked arms + P3), and 7.7
(4-rule arms with the ghost-edge disjunction), each of which now has `modalApplyOneS4Keyed_notApplicable_growth`
available to discharge their conjunct-(d) obligation. See each phase's own Scope Hypothesis and
task list in the plan file — they are independently dispatchable within the wave but all three
must close before Phase 7.8 (wave 10) can start.
