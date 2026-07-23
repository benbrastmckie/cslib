# Implementation Summary: Dedup Minimal Canonical Model onto Generic Extension

- **Task**: 521 - Dedup Minimal Canonical Model onto Generic Extension
- **Plan**: plans/01_dedup-minimal-canonical-model.md
- **Status**: [COMPLETED]

## Overview

`mk_completeness` (`Cslib/Logics/Modal/Metalogic/Minimal/MinCompleteness.lean`) was rewired to
delegate to the already-proved, `Axioms`-generic `mkvalidFC_completeness`
(`MinExtension.lean:1548`) instantiated at `Axioms := MKModalAxiom` and the trivial frame
condition `FC := (fun {_} _ => True)`, mirroring the existing `mt_completeness` instantiation
pattern (`MT.lean`). This let the bespoke MK-only canonical-model core
(`MinCanonicalModel.lean`, 1089 lines; `MinTruthLemma.lean`, 257 lines) be deleted as dead code,
followed by the now-orphaned `MinPrimeTheory.lean` (125 lines) -- 1471 lines removed in total.

## Phases

- **Phase 1** (commit `c1d6c958`): swapped `MinCompleteness.lean`'s import from `MinTruthLemma`
  to `MinExtension`; replaced the `by_contra`-based proof body with the 12-lambda
  `mkvalidFC_completeness` delegation (`.implyK` ... `.idb`, `trivial` for `h_canonFC`,
  `mvalid_iff_mvalidFC_true.mp h_valid` for the hypothesis conversion). Signature and
  `mk_soundness_completeness` unchanged. Axiom-set baseline captured via `git stash` + `lake env
  lean` + `#print axioms` (the `lean_verify` MCP tool returned an empty axiom list for every
  theorem tried in this session, including unmodified ones, so the direct method was used
  instead): `[propext, Classical.choice, Quot.sound]` for both `mk_completeness` and
  `mk_soundness_completeness`, both before and after the rewire.
- **Phase 2** (commit `072a14f3`): deleted `MinCanonicalModel.lean` and `MinTruthLemma.lean`,
  regenerated `Cslib.lean` via `lake exe mk_all --module` (exactly those two import lines
  removed). Full `lake build Cslib` green.
- **Phase 3** (commit `42a0f14a`): deleted the now-orphaned `MinPrimeTheory.lean` (zero remaining
  importers confirmed by grep; `MinExtension.lean`'s only reference is a doc comment). Regenerated
  the barrel again. Full `lake build Cslib` green.
- **Phase 4**: ran the full CSLib CI pipeline and final axiom-set verification. See Verification
  below for per-step detail, including two out-of-scope findings from concurrent tasks running in
  the same shared working tree.

## Verification

- `lake build` (full): green.
- `lake exe checkInitImports`: passes (exit 0).
- `lake lint`: exactly one finding, an `unusedArguments` warning in
  `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` -- outside this task's scope, not a
  file this task touched.
- `lake exe lint-style`: clean (exit 0).
- `lake test`: fails only on `CslibTests/ModalFrameSeparation.lean` (`decide` reduction stuck on
  `instDecidableS5Valid`/`instDecidableFiveValid`). Confirmed pre-existing and out of scope: added
  by a concurrent task's phase 23.2 work (commit `d5e528b0`), imports only
  `Cslib.Logics.Modal.Tableau.FrameCompleteness`, and has zero connection to the Minimal/
  directory or any file this task touched -- exactly the KB5/Five-simplification blocker flagged
  as out of scope in the delegation brief. All other test targets build green.
- `lake shake --add-public --keep-implied --keep-prefix`: `MinCompleteness.lean`'s only suggestion
  is "remove `import Cslib.Init`", the known systemic false positive that must be kept per
  CONTRIBUTING.md / `checkInitImports`; no actionable trim, no edit applied.
- Axiom-set check (`lake env lean` + `#print axioms`, `lean_verify` MCP tool was unreliable in
  this session): `mk_completeness`, `mk_soundness_completeness`, `mt_completeness`,
  `ms4_completeness`, `ms5_completeness` all report `[propext, Classical.choice, Quot.sound]` --
  identical to the Phase 1 baseline and to each other. Zero new axiom, zero regression.
- Zero `sorry`/`admit`/`axiom` anywhere in `Cslib/Logics/Modal/Metalogic/Minimal/`.
- `git diff --stat` across the three phase commits: 1471 lines deleted from the three removed
  files, matching the plan's target exactly.

## Plan Deviations

- Phase 1's axiom-baseline capture task used `git stash` + `lake env lean` + `#print axioms`
  instead of the `lean_verify` MCP tool, which returned an empty axiom list for every theorem
  queried in this session (including theorems never touched by this task). Same substitution
  applied to Phase 4's final axiom-set check.
- No other deviations. All four phases executed exactly as planned; Phase 3 (the gated,
  reversible `MinPrimeTheory.lean` deletion) was NOT reverted -- zero unexpected dependency
  surfaced.

## Concurrent-Workspace Notes (informational, not a deviation)

This session ran in a shared working tree alongside several other concurrently-orchestrated
tasks (observed: task 502 editing `Segment.lean`'s imports, a KB5/Five-related task editing
`InterSystem/Modularity.lean` and `Tableau/LoopChecking.lean`, and others). Two transient,
non-blocking effects were observed and are recorded for traceability:
- A `git add <exact-two-files>` + `git commit` at the end of Phase 1 incidentally picked up
  another task's already-created, unrelated files (`specs/502_.../plans/...`,
  `specs/502_.../reports/...`) due to a shared git index race between this session's `add` and
  `commit` calls. Content was correct and not modified by this session; Phases 2-3 commits were
  scoped tightly and did not repeat this.
- `lake build`/`lake shake`/`lake test` each hit one transient failure caused by a concurrent
  task's in-flight edit elsewhere in the tree; retrying after that task's edit landed (or
  confirming the failure was in an unrelated, untouched file) resolved or explained each case.

## Public Names Preserved

`mk_completeness : MValid.{u, u} φ → Derivable MKModalAxiom φ` and
`mk_soundness_completeness : MValid.{u, u} φ ↔ Derivable MKModalAxiom φ` retain their exact prior
signatures and file location.

## Files Changed

- Modified: `Cslib/Logics/Modal/Metalogic/Minimal/MinCompleteness.lean`, `Cslib.lean`
- Deleted: `Cslib/Logics/Modal/Metalogic/Minimal/MinCanonicalModel.lean`,
  `Cslib/Logics/Modal/Metalogic/Minimal/MinTruthLemma.lean`,
  `Cslib/Logics/Modal/Metalogic/Minimal/MinPrimeTheory.lean`
