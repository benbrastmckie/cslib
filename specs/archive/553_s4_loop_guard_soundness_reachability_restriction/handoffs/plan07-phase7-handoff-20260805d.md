# Handoff: Plan v6 (`plans/07_canonical-witness-truth-lemma.md`), Phase 7 continuation (d)

- **Date**: 2026-08-05
- **Session**: sess_1785947077_74defa (fourth continuation dispatch)
- **Plan**: `plans/07_canonical-witness-truth-lemma.md` (v6, latest; plans 01-05 superseded)
- **Status at handoff**: Phases 1-6 `[COMPLETED]`, Phase 7 `[IN PROGRESS]` (four of the five
  case-split arms now landed sorry-free; see the plan's `#### Phase 7 Progress Record` (fourth
  dispatch, at the top of that subsection) for the authoritative, up-to-date state — this handoff
  summarizes it and adds narrative context).

## Scope of this dispatch

The prior dispatch (handoff `...-20260805c.md`) landed three case-split arms (propositional,
mint-unblocked box-negative, mint-unblocked diamond-positive) and left two 4-rule cases
(box-positive `T(□φ)@w`, diamond-negative `F(◇φ)@w`) as the single largest remaining piece. This
dispatch was scoped to close ONLY those two 4-rule cases, explicitly excluding the mint-blocked
(redirect) case, which the prior dispatch established has no known closing route with
currently-available invariants — that finding was carried forward, not re-attempted.

## What landed this dispatch (sorry-free, `{propext, Classical.choice, Quot.sound}` only)

Both 4-rule cases closed as standalone, case-scoped, sorry-free lemmas, matching the pattern of
the three prior landed lemmas:

- `modalApplyOneS4Keyed_boxPos_sat` (`FrameCompleteness.lean`) — the 4-rule box-positive case.
- `modalApplyOneS4Keyed_diaNeg_sat` (`FrameCompleteness.lean`) — direct dual, diamond-negative.

Supporting infrastructure:

- `modalApplyOneS4Rules_boxPos_soundIn`/`_diaNeg_soundIn` (`FrameCompleteness.lean`, new): the
  actual K+T+4 `RuleResultSat` merge. Reuses the already-landed `modalApplyOneT_boxPos_soundIn`/
  `_diaNeg_soundIn` as a black box for K+T (feeding `hFC.1 : reflFC m.r` extracted from `s4FC`'s
  reflexivity conjunct), then layers the 4-rule propagation on top via one hop of `IsTrans`
  (`hFC.2`) off the recorded successor edge.
- `modalApplyOneT_boxPos_eq`/`_diaNeg_eq` (`FrameCompleteness.lean`, new): `modalApplyOneT`'s own
  `.fst` is always `.notApplicable` or `.persistent` at these shapes — the outer case-split the
  K+T+4 merge needs. Lives in `FrameCompleteness.lean` (not `LoopChecking.lean`) because it needs
  `modalApplyOneT_boxPos_fst` (`TDriver.lean`), which `LoopChecking.lean` does not import.
- Four pre-existing PRIVATE lemmas in `LoopChecking.lean`, de-privatized this dispatch (no proof
  content changed): `modalApplyOneS4Rules_boxPos_fst`/`_diaNeg_fst` (the `.fst` closed form in
  terms of `modalApplyOneT`'s own result) and `modalApplyOneS4Keyed_boxPos_eq_S4Rules`/
  `_diaNeg_eq_S4Rules` (the Keyed→S4Rules bridge, `rfl`) — see "Discovery" below.
- Two more pre-existing private lemmas de-privatized as transitive dependencies:
  `modalApplyOneS4Rules_snd_eq`, `modalApplyOne_boxPos_snd_S4`/`_diamondNeg_snd_S4`.
- Two new small companion lemmas in `LoopChecking.lean`: `modalApplyOneS4Rules_boxPos_snd_eq_acc`/
  `_diaNeg_snd_eq_acc` (chains the two de-privatized `.snd` facts above).

Verification: scoped `lake build Cslib.Logics.Modal.Tableau.LoopChecking` and
`lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` both clean; `lake exe lint-style` clean
on both files; `lake lint` clean on both files (checked via full-repo run, filtered — zero
warnings touching either file; the pre-existing repo-wide warnings are all in unrelated Temporal
metalogic files, out of scope); `lake exe checkInitImports` clean; sorry-free confirmed via
direct `#print axioms` on all four new `FrameCompleteness.lean` declarations
(`modalApplyOneS4Rules_boxPos_soundIn`, `modalApplyOneS4Rules_diaNeg_soundIn`,
`modalApplyOneS4Keyed_boxPos_sat`, `modalApplyOneS4Keyed_diaNeg_sat`) — all report exactly
`{propext, Classical.choice, Quot.sound}`, no `sorryAx`. Bare-tactic sorry census over
`Cslib/Logics/Modal/Tableau/` stayed at exactly 1 (`FrameSoundness.lean:1251`, standing, retained)
after each commit. A whole-project `lake build` was re-run and is clean.

Two separate green commits: `task 553 phase 7.5` (LoopChecking.lean de-privatization + new `.snd`
lemmas) and `task 553 phase 7.6` (FrameCompleteness.lean soundness composition + case lemmas).

## Discovery worth recording for future dispatches

The catalogued route in the prior Progress Record (build a NEW merge lemma from scratch composing
`modalApplyOne_boxPos_sound` + `modalTBoxSelf_sound` + `modalFourBoxProp_sound`, plus two NEW
Keyed→S4→Rules bridge un-privatizations) turned out to be more work than necessary. On inspection,
`LoopChecking.lean` already contained — privately, apparently authored during an earlier phase in
anticipation of this exact need but never wired to `FrameCompleteness.lean` — the precise `.fst`
closed-form lemmas (`modalApplyOneS4Rules_boxPos_fst`/`_diaNeg_fst`) and the Keyed→S4Rules bridge
(`modalApplyOneS4Keyed_boxPos_eq_S4Rules`/`_diaNeg_eq_S4Rules`, a direct `rfl` — simpler than
going through `modalApplyOneS4` as an intermediate step). De-privatizing these four (plus two
small transitively-needed `.snd` facts) and writing only the genuinely-new semantic composition
(`modalApplyOneS4Rules_boxPos_soundIn`/`_diaNeg_soundIn`, reusing `modalApplyOneT_boxPos_soundIn`
as a black box for K+T rather than re-deriving it) was substantially cheaper than the catalogued
from-scratch approach.

**Two real obstacles hit and worked around, worth flagging for whoever next edits this file
cluster**: (1) An initial attempt to build fresh, differently-named driver lemmas directly in
`LoopChecking.lean` collided in NAME with this pre-existing private infrastructure — Lean reports
"a private declaration ... has already been declared" for a same-named public/private pair in the
same file, which is a real (if easily fixed) trap; always grep for the target name across the
WHOLE file before writing new infrastructure, not just the immediate surrounding section. (2)
`LoopChecking.lean` does NOT import `TDriver.lean` (confirmed: `grep -n "^import"
LoopChecking.lean` shows only `Cslib.Init` and `Mathlib.Tactic.Ring`), even though it freely uses
`modalApplyOneT`/`modalTBoxSelf`/`modalFourBoxProp` (which come from `FrameRules.lean`, which
`LoopChecking.lean` DOES import transitively). A lemma needing `modalApplyOneT_boxPos_fst`
(defined in `TDriver.lean`) genuinely cannot live in `LoopChecking.lean` as things stand; it was
placed in `FrameCompleteness.lean` instead, which already imports `TDriver.lean` per the file's
own layering note — this is the RIGHT call given `FrameCompleteness.lean` is documented as "the
only file importing both" the keyed driver definitions and the frame-relativized semantic
apparatus.

## The mint-blocked case — unchanged, still open, not re-attempted

Carried forward verbatim from the third-dispatch handoff (`...-20260805c.md`), read that document
for full technical detail. Summary: `branchSatisfiableIn_s4FC_addEdge_of_blocked` (the Phase 6
capstone) requires `hH : modalHintikkaSetS4 φ₀ b acc` — full branch-level saturation, not
available at an arbitrary settled per-step state (only the currently-firing formula is guaranteed
a witness, not every sibling mint-shaped formula on the branch). The alternative
(extend-ambient-model route) also fails: `blockingWorldS4Keyed`'s redirect target is chosen by a
purely syntactic key-subset comparison with no a priori semantic tie to an arbitrary model
satisfying the branch. This is an open architectural question — either the induction needs a
stronger invariant threaded through every step (carrying enough saturation, or a dedicated
"redirect edges already realized" witness incrementally), or the mint-blocked case is not provable
as a literal per-step preservation lemma and the soundness architecture for the keyed ordered
driver needs to be rethought at the phase-design level. **This dispatch did not touch it, per
explicit out-of-scope instruction from the dispatching orchestrator.** It should be escalated to
planning level / user decision before the next implementation attempt burns tool calls re-deriving
the same dead end.

## Updated case-split table

| Case | Status |
|------|----|
| Propositional/non-modal | **Landed** (`modalApplyOneS4Keyed_notBoxDia_sat`) |
| Mint, unblocked (box-negative) | **Landed** (`modalApplyOneS4Keyed_boxNeg_mint_sat`) |
| Mint, unblocked (diamond-positive) | **Landed** (`modalApplyOneS4Keyed_diaPos_mint_sat`) |
| 4-rule, box-positive (`T(□φ)@w`) | **Landed this dispatch** (`modalApplyOneS4Keyed_boxPos_sat`) |
| 4-rule, diamond-negative (`F(◇φ)@w`) | **Landed this dispatch** (`modalApplyOneS4Keyed_diaNeg_sat`) |
| Mint, blocked (redirect) | **Still open** — the sole remaining case, blocking the dispatcher theorem. Architectural question, not proof-engineering. |

Four of five case-split arms are now landed sorry-free. Mint-blocked is the only remaining case,
but it single-handedly blocks assembling the complete dispatcher theorem — the step lemma cannot
typecheck as a total function over all cases until this one closes (or the architecture changes).

## What remains

- **Mint-blocked (redirect)**: open architectural question, needs planning-level/user input
  before further implementation attempts (see above).
- **Assemble the single dispatcher theorem**: blocked on mint-blocked. Should mirror
  `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`'s case-split shape exactly, per the
  original phase catalogue.
- **Extend the regression corpus** with an `"OPEN"` counterexample row: also blocked on the step
  lemma it would witness.
- **Full 8-step CI gate**: `lake exe cache get` (already warm), scoped builds (done this
  dispatch), `checkInitImports` (done, clean), `lake lint` full repo (done, clean on touched
  files), `lake exe lint-style` (done, clean), `lake test`, `lake shake`, `lake exe mk_all
  --module` (not yet run this dispatch — no new files were added, so `mk_all` should be a no-op,
  but was not independently re-verified; `lake test`/`lake shake` were not run this dispatch,
  deferred to phase close since Phase 7 is not closing this dispatch).
- Still open (per prior handoffs, unresolved): whether Phase 7's task list is bounded to the
  step-level lemma alone, or also needs a fuel-induction wrapper /
  `modalTableauS4KeyedOrdered_sound`-shaped capstone. Not decided this dispatch either — moot
  until mint-blocked resolves.

## Constraints that still apply, unchanged

- File scope: `Cslib/Logics/Modal/Tableau/{FrameCompleteness,FrameSoundness,LoopChecking}.lean`,
  `CslibTests/S4LoopGuardRegression.lean`. Everything else in the subsystem stays read-only.
- The standing sorry at `FrameSoundness.lean:1251` is retained by explicit user decision —
  untouched this dispatch, census confirmed still exactly 1.
- Never commit a `sorry`. Land only what genuinely closes.
- Re-verify every line number and lemma name by grep before trusting any handoff document
  (including this one) — edits shift line numbers and this dispatch discovered pre-existing
  infrastructure the prior handoff's catalogue did not know about.

## Continuation entry point

1. The mint-blocked architectural question is the single blocker on Phase 7's completion. Raise
   it at planning level or to the user rather than re-attempting the catalogued-but-broken route
   (`branchSatisfiableIn_s4FC_addEdge_of_blocked` directly) — see the third-dispatch handoff for
   the full technical dead-end analysis, carried forward unchanged above.
2. Once (if) mint-blocked resolves, assemble the dispatcher theorem from the now-five landed
   case-scoped lemmas, extend the regression corpus, and run the remaining CI steps
   (`lake test`, `lake shake`, `lake exe mk_all --module`) before marking Phase 7
   `[COMPLETED]`.
