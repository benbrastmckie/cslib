# Summary: Phase 8 `[BLOCKED]` — Cross-Label `efq`/`orE` Soundness Gap

- **Task**: 537 — Labelled CS5 general soundness biconditional
- **Plan**: `plans/03_direct-route-forest.md` (v3), Phase 8
- **Status**: `[BLOCKED]` (mathematical finding, not an engineering overrun)
- **File touched**: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`
  (module docstring only)

## What was attempted

Phase 8 asked for the `nik_soundness_onePoint` skeleton to be generalized over an arbitrary
interpretation `ρ` and model, with the motive amended to carry `IsDerivationForest G`, the raw
edge-cond, and the Γ-cond, closing `boxI`/`diaE`/`boxE`/`diaI` via the landed `boxI_lift`/
`box_iff_TClosure`/`dia_iff_TClosure`/`box_gives_here`, and transcribing the remaining 9
propositional constructors from `nik_soundness_onePoint` directly.

`boxI`/`diaE`/`boxE`/`diaI` were confirmed tractable exactly as the plan anticipated. However,
attempting the transcription for `NIK.efq` and `NIK.orE` (the two **cross-label** propositional
constructors, `Deduction.lean:252,277`) surfaced a genuine semantic obstruction: their conclusion
label is independent of their premise's label, with no relation between the two supplied anywhere
in the constructor. The naive motive requires deriving `CKForces (ρ y) A` (for arbitrary `A`) from
`botForces (ρ x)` for the *same, externally-supplied* `ρ` -- and when the conclusion label `y` is
unconstrained by `G.X ∪ ctxLabels Γ`, this is model-theoretically false.

## Machine-verified evidence

A two-point discrete countermodel (`World := Pt (one|two)`, `≤ := Eq`, `r := Eq`) was built and
verified via `lean_run_code`: `cs5FCIncest r` holds, all `CKValidFC` upward-closure and explosion
axioms hold, `botForces := (·=one)`, `CKForces bot` holds at `one`, and `CKForces (atom ())` is
**false** at `two`. This directly refutes the `efq` case of the naive "∀ ρ" motive whenever the
conclusion label is set to a point disconnected from the premise's. `nik_soundness_onePoint`'s
existing `efq` case avoided this only because `World := Unit` forces every interpretation to be
constant -- a degenerate masking, not a resolution, that does not generalize to a non-trivial
`World` (which `boxI`/`diaE` require).

## Why this is out of Phase 8's scope to fix directly

Two candidate fixes were assessed and both require substantial new proof architecture beyond
"transcribe the skeleton":
1. A not-yet-landed connectivity lemma ("`IsDerivationForest` built from `Graph.trivial` via a
   chain of `addEdge`s implies `TClosure TS5 G.R` is total on `G.X`") -- `IsDerivationForest`
   (Phase 6) deliberately omits a connectivity conjunct, so this needs new machinery.
2. An existential reformulation of the whole induction's motive (`∃ ρ'` agreeing with `ρ` on
   `G.X ∪ ctxLabels Γ`) -- consistent with `boxI`/`diaE`/label-local rules on inspection, but
   still needs (1) for `efq`/`orE`'s `y ∈ G.X ∪ ctxLabels Γ` sub-case, and is itself a redesign of
   the induction's shape that the Postmortem Constraints direct against inventing unilaterally.

## Plan Deviations

- Phase 8 was not implemented; recorded `[BLOCKED]` per the escalation protocol rather than forcing
  a `sorry`, an unsound proof, or a large unplanned redesign mid-dispatch.
- The module docstring's stale `INTRACTABLE`/`GATE-C`/"What remains" notes (from earlier,
  since-superseded dispatches on a *different* obstruction, the exact-symmetry "Wall A") were
  intentionally left in place, since the Phase 8 task that would have superseded them
  ("mark the general theorem LANDED; remove the stale notes") did not complete.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness`: green.
- `grep -n '\bsorry\b'`: no new tactic sorry (all hits are prose, pre-existing or in this
  dispatch's own documentation prose).
- `grep -n '^axiom '`: no new axioms.
- No line exceeds the 100-character style limit in the new docstring text.
- All fourteen Preserved Assets and Phases 1-7's landed lemmas are untouched (only a docstring
  section was appended; no theorem/proof code in this file was added or edited).

## Artifacts

- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` (module docstring: new
  "Fifth dispatch" section)
- `specs/537_labelled_cs5_general_soundness_biconditional/plans/03_direct-route-forest.md`
  (Phase 8 heading `[BLOCKED]` with a blocked note)
- `specs/537_labelled_cs5_general_soundness_biconditional/handoffs/08_phase8-blocked-crosslabel-efq.md`
  (full analysis, countermodel, and recommended follow-up scope)
- `specs/537_labelled_cs5_general_soundness_biconditional/.orchestrator-handoff.json`
