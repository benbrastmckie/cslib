# Implementation Summary: Bespoke Keyed S4 Driver

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma (task 511 Phase 7
  follow-on)
- **Plan**: plans/01_keyed-s4-driver-plan.md
- **Status**: PARTIAL (2 of 5 phases complete and committed; 3 phases BLOCKED with a detailed
  continuation handoff)

## What Was Completed

**Phase 1 — Keyed S4 driver definitions** (`Cslib/Logics/Modal/Tableau/LoopChecking.lean`):
- `modalExpandBranchesS4Keyed`: a bespoke `keys`-threaded fuel driver, structurally mirroring
  `modalExpandBranchesGen`/`processNext` (`Saturation.lean`), with a fourth worklist column
  carrying each branch's own `keys` list, stepped by the already-landed
  `modalStepBranchS4Keyed`.
- `modalTableauS4Keyed`: the entry point (`F(φ)@0`, `keys := []`, fuel `modalFuel φ`).
- The live `modalTableauS4` is untouched (kept as the reference artifact).

**Phase 2 — Congruence gate `hintikka_congr_S4`** (same file): proved **unconditionally** (no
saturation hypothesis needed) that the keyed and live S4 rules agree on Hintikka-set-hood, for
any `keys`. This resolved considerably easier than the research survey anticipated:
`modalHintikkaSetGen`'s conjunct 2 returns literal `True` at exactly the two shapes where the
keyed/live rules can differ, and at every other shape the keyed rule falls through to the live
rule by a definitional `rfl` catch-all. The proof is a direct transcription of the S5 precedent
`hintikka_congr` (`S5Simplification.lean:604`).

Both are lake-build-green, zero `sorry`, and `lean_verify`-confirmed axiom-clean
(`propext`/`Classical.choice`/`Quot.sound` only). Committed as
"task 535 phase 1-2: keyed S4 driver definitions + hintikka_congr_S4 crux".

## What Is Blocked

**Phases 3 (termination/Hintikka top-loop), 4 (soundness), and 5 (completeness+decidability)**
are marked `[BLOCKED]` in the plan file. No Lean code was written for these phases — deliberately,
to avoid any `sorry`/placeholder. In-depth source analysis (see the plan's per-phase blocker
notes and the full technical map in `handoffs/01_phase3-5-continuation.md`) established the root
cause: every landed "top-loop" lemma these phases were modeled on
(`modalExpandBranchesHintikka`, `modalExpandBranchesGen_closed_unsatIn`) is hard-wired to a
single **fixed** rule-application function used identically at every fuel step, whereas the
keyed S4 driver's rule genuinely changes at every step (`keys` grows monotonically). None of the
landed generic top-loop machinery can be instantiated directly; a bespoke, keys-threaded
analogue of each (plus a from-scratch S4 minting-shape soundness lemma, since none exists
anywhere in the codebase) is required — estimated 1500-2500 new lines, well beyond this plan's
original 10-16 hour estimate for the full task. The continuation handoff documents a concrete
5-sub-phase decomposition (3a-3e) plus Phases 4-5, identifies exactly which existing lemmas are
reusable at each step, and flags one confirmed (not conjectural) blocker: `modalFuel φ` (K's
fuel, Phase 1's current choice) is **not** provably sufficient for the S4 keyed loop at small
formula complexity (verified via direct arithmetic comparison at `modalComplexity φ₀ = 0`), so a
dedicated `modalFuelS4` is needed.

## Plan Deviations

- Phase 1's checklist item "no proof obligations discharged yet" was exceeded — Phase 2's crux
  was also fully discharged in the same dispatch, ahead of the plan's Wave-1 pairing (both were
  genuinely independent per the plan's own dependency table).
- Phases 3, 4, 5 were not attempted in Lean code (no partial theorem statements or stubs were
  committed) once analysis showed the true scope; this is a deliberate escalation per the
  Escalation Protocol, not a silent skip — each phase's blocker is documented inline in the plan
  file with the specific root cause and what is needed to unblock.
- The plan's Phase 4 heading originally appeared with a duplicate rewrite during editing; this
  was corrected in place (single heading, single blocker block, original Goal/Tasks/Verification
  content preserved below it).

## Verification Performed

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking`: green.
- `lake exe checkInitImports`: clean (no output).
- `lake lint`: `-- Linting passed for Cslib.` (project-wide, no new warnings).
- `lake exe lint-style`: clean (no output).
- `lake shake --add-public --keep-implied --keep-prefix`: no findings against
  `LoopChecking.lean` (pre-existing, unrelated findings against other files left untouched).
- `lake exe mk_all --module`: "No update necessary" (no new files added).
- `lake test`: exit code 0.
- `grep` for `sorry`/vacuous-definition patterns/new `axiom` declarations in
  `LoopChecking.lean`: zero matches (the one `sorry` hit is inside a docstring's prose, not code).
- `lean_verify` on `hintikka_congr_S4`: `propext`/`Classical.choice`/`Quot.sound` only.
- `lean_verify` on `instDecidableS5Valid` (regression check): unchanged, axiom-clean.

## Files Touched

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive only: `modalExpandBranchesS4Keyed`,
  `modalTableauS4Keyed`, `hintikka_congr_S4`).
- `specs/535_abstract_termination_measure_interface_s4b_loop/plans/01_keyed-s4-driver-plan.md`
  (phase status markers, blocker documentation).
- `specs/535_abstract_termination_measure_interface_s4b_loop/handoffs/01_phase3-5-continuation.md`
  (new: full technical map for the follow-on dispatch).

`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` was **not** modified (Phases 4-5, which target
that file, are blocked).
