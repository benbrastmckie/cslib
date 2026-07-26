# Implementation Summary: Phase 1 -- Red Channel, `accWithReds`, Bifurcated `modalHintikkaSetS4Sub`

- **Task**: 553 - s4_loop_guard_soundness_reachability_restriction
- **Status**: [IN PROGRESS] (task-level; Phase 1 of 12 is [COMPLETED])
- **Started**: 2026-07-26T18:45:00Z
- **Completed**: 2026-07-26T19:40:00Z
- **Effort**: ~1 hour
- **Dependencies**: none (wave 1, first phase of plan v4)
- **Artifacts**: plans/04_subtractive-blocking-red-channel.md (Phase 1 section, plus new
  `#### Phase 1 Statement Validation` subsection)
- **Standards**: status-markers.md, artifact-management.md, tasks.md, this file

## Overview

Phase 1 of plan v4 (route (3): Massacci-style subtractive blocking with a completeness-only
redirect channel) fixes the exact Lean statement shapes the whole route rests on, with no
proofs attempted beyond a single `simp`-level bridge, then re-validates those shapes against
the probe corpus in their *final* form. This is a statement-shape phase by design: report 04
made it a mandatory precondition that clause shapes be settled before any proof work, because
the (b)/(d) trap the route must avoid is a statement-shape trap, not a proof difficulty.

## What Changed

- Added `abbrev Reds (Atom : Type*) [DecidableEq Atom] [Hashable Atom] := List (WorldIndex ×
  WorldIndex × Sign × Proposition Atom)` to `Cslib/Logics/Modal/Tableau/LoopChecking.lean`.
- Added `def accWithReds (acc : Accessibility) (red : Reds Atom) : Accessibility := ⟨acc.edges
  ++ red.map (fun r => (r.1, r.2.1))⟩` and the bridge `theorem hasEdge_accWithReds_iff`.
- Added `def modalHintikkaSetS4Sub` -- the bifurcated S4 Hintikka-set characterization:
  conjunct 2 (saturation) stated over `acc` alone (unchanged from `modalHintikkaSetS4`);
  conjuncts 3/4 (existential witnesses) over `accWithReds acc red`; two new forward-cone
  conjuncts 5/6 (`redBoxForwardCone` G*, `redDiaForwardCone` F*) over
  `Relation.ReflTransGen (accWithReds acc red).hasEdge`.
- Added `structure S4KeyedSubHintikkaInv` -- field statements only (no preservation lemma):
  the five `S4KeyedHintikkaInv` fields with the two witness fields restated over `accWithReds
  acc red`, plus two fields mirroring conjuncts 5/6.
- Extended `specs/553_.../artifacts/s4subtractive3.lean`'s `condGStar`/`condFStar` with a
  field-by-field alignment doc comment cross-referencing the landed conjunct 5/6 statements,
  and re-ran all three sweep corpora (`lake env lean`, exit 0).
- Checked off Phase 1's task list, moved the phase heading to `[COMPLETED]`, and recorded the
  verbatim `#eval` output under a new `#### Phase 1 Statement Validation` subsection in the
  plan.

## Decisions

- **`Reds` takes `Atom` as an explicit parameter**, not the plan's literal bare `abbrev Reds :=
  ...`. `LoopChecking.lean`'s `Atom` is an ambient section `variable` (unlike the probe's
  concrete `P := Proposition Nat`), and a zero-argument abbrev referencing it fails to
  elaborate at every use site (`don't know how to synthesize implicit argument Atom` --
  confirmed by a minimal reproduction before landing). Every use site writes `Reds Atom`
  explicitly. This is a mechanical Lean-elaboration necessity; the type is byte-identical in
  content to the plan's specification.
- **`hasEdge_accWithReds_iff`'s proof** closes with `simp only [accWithReds,
  Accessibility.hasEdge, List.any_append, List.any_map, Function.comp_def]` --
  `Function.comp_def` was needed in addition to the plan's cited `List.any_append` to discharge
  the resulting `∘`-vs-`fun` goal left by `List.any_map`; confirmed via `lean_run_code` before
  landing the real proof.
- **Insertion point**: the new section sits in `LoopChecking.lean` immediately after
  `S4KeyedHintikkaInv_weaken` and before the pre-existing `## Phase 7: Single-Step Invariant
  Preservation` doc heading, since `S4KeyedSubHintikkaInv` is thematically the keyed-invariant
  analogue sitting beside `S4KeyedHintikkaInv`. This shifted every subsequent declaration in
  the file down by ~129 lines -- flagged prominently in the handoff for Phases 2/3.
- **`condGStar`/`condFStar`'s outer iteration order was left unchanged** (per-`red`-entry, via
  the caller's `red.filter`), rather than restructured to textually match the Lean statement's
  `∀ χ, ∀ (src wBlock s φ), ...` binder order. Leading universals commute freely, so this is
  logically immaterial, and restructuring would have changed the failure-counting methodology
  (one failure per formula instead of per redirect), breaking comparability with reports 02/04's
  established 24,314-redirect baseline.

## Impacts

- Phases 2 (GATE A, consumption) and 3 (GATE B, establishment) -- wave 2's two independent
  decision gates -- are now unblocked and can be dispatched in parallel.
- The realigned probe's 0-failure result for conjuncts 5/6 across all three corpora
  (1652+6303+16359 = 24,314 recorded redirects) is a **measurement, not a proof** (per the
  plan's own postmortem constraint) -- it licenses proceeding to Phases 2/3, not a conclusion
  that either gate will close.
- `modalTableauS4Keyed_complete` and every other Preserved Asset remain green; no existing
  declaration was edited in place.

## Follow-ups

- Phases 2 and 3 (wave 2, parallel dispatch) -- see the plan's territory table for file
  ownership.
- Line-number drift: the plan's Phase 2-12 task descriptions cite `LoopChecking.lean` line
  numbers from before this phase's ~129-line insertion. Successor dispatches should re-locate
  cited declarations by name rather than trust the plan's line numbers (recorded in
  `.orchestrator-handoff.json`'s `next_action_hint`).

## Plan Deviations

- **`Reds` parametrization** (explicit `Atom` argument instead of the plan's bare abbrev) --
  see Decisions above. Content-identical; required by Lean elaboration in a polymorphic
  section, unlike the probe's concrete-`Atom` setting.
- No other deviations. All four Phase 1 task-list bullets were completed as specified; the
  bifurcation table (conjunct 2 over `acc`, conjuncts 3/4 over `accWithReds`, conjuncts 5/6
  forward-cone-only) was followed exactly, and the forbidden wrapped-at-target form (d) was not
  used anywhere in the landed statements.

## References

- `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/04_subtractive-blocking-red-channel.md`
  (Overview's bifurcation table; Phase 1 section; `#### Phase 1 Statement Validation`)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (new declarations, inserted before `## Phase 7:
  Single-Step Invariant Preservation`)
- `specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4subtractive3.lean`
  (realigned `condGStar`/`condFStar`)
- `specs/553_s4_loop_guard_soundness_reachability_restriction/.orchestrator-handoff.json`
