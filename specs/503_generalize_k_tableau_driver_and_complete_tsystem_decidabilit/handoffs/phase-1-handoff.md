# Phase 1 Handoff: Shared Frame-Validity Scaffolding

**Status**: [COMPLETED], green, zero sorry, zero new axiom.

## What Was Built

- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`:
  - `FrameCondition := ∀ {World : Type}, (World → World → Prop) → Prop`
  - `trivialFC : FrameCondition := fun {_} _ => True`
  - `frameValid (FC : FrameCondition) (φ)` — generalizes `kValid`.
  - `branchSatisfiableIn (FC : FrameCondition) b acc` — generalizes `branchSatisfiable`.
  - `frameValid_trivialFC_iff_kValid` — `frameValid trivialFC φ ↔ kValid φ`.
  - `branchSatisfiableIn_trivial_imp` — bridge lemma dropping the trivial FC witness.
  - `modalTableau_sound_frame` — K soundness re-derived through `frameValid`, reusing
    `modalExpandBranches_closed_unsat` verbatim (zero changes to `Soundness.lean`/
    `SoundnessStep.lean`).
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`:
  - `extractModelWith (Cl) b acc` — parameterized model extractor generalizing `extractModel`
    (K) with `r := Cl acc.hasEdge` instead of `r := acc.hasEdge`.
  - `extractModelWith_id` — `extractModelWith id = extractModel`.
  - Module docstring documents the Strategy-B closure-operator table for T/S4/B/S5.

## CI Verification (all green)

- `lake build` (full, 3208 jobs) — pass.
- `lake exe checkInitImports` — pass.
- `lake lint` — no findings in either new file.
- `lake exe lint-style` — pass.
- `lake shake --add-public --keep-implied --keep-prefix` — no findings for either new file
  (repo-wide exit 1 is pre-existing, from unrelated Propositional/Temporal files).
- `lake test` (9199 jobs) — pass.
- `lake exe mk_all --module` — `Cslib.lean` regenerated (also picked up two unrelated files
  from a concurrent session: `Cslib.Logics.Modal.Metalogic.Constructive.{CT,CKExtension}`).
- `grep sorry`/`grep axiom` over `Cslib/Logics/Modal/Tableau/*.lean` — zero.

## Concurrency Hazard (important for continuation)

During this phase, a concurrent orchestrator session (task 396 "salvage 299 soundness
lemmas" and/or task 501 "CK constructive modal extensions", both `status: implementing`)
was actively editing `Cslib/Logics/Modal/Tableau/Defs.lean` and files under
`Cslib/Logics/Modal/Metalogic/Constructive/` in the **same working tree** (no git worktree
isolation between concurrent orchestrator sessions in this environment). This caused two
transient `lake build`/`lake shake` failures that were NOT caused by task 300's own files —
both resolved once the concurrent session's edits settled. No task-300 commit touches
`Defs.lean` or any `Metalogic/Constructive/*` file. Any future dispatch on task 300 should
expect the same hazard and should re-verify CI is green (not assume a red build implies a
task-300 regression) before debugging.

## Scale Assessment for Remaining Phases (read before continuing)

K's own soundness + completeness spans ~5,250 lines across five files
(`Soundness.lean` 353, `SoundnessStep.lean` 744, `Completeness.lean` 935,
`CompletenessLoop.lean` 1353, `FmpMeasure.lean` 2959). Each frame system's *soundness* arm is
genuinely lightweight (a few dozen lines: new persistent/backward tableau rules + a soundness
theorem discharged directly by `Satisfies.t`/`Satisfies.b`/`Satisfies.four`/`Satisfies.five`,
since the frame condition holds by construction of the extracted model's relation via
Strategy-B closure). The *completeness/decidability* obligation for each system
(`Decidable (tValid φ)`, etc.) requires a full new fuel-bounded tableau loop + Hintikka-set
truth lemma + termination/FMP argument mirroring `Completeness.lean`/`CompletenessLoop.lean`/
`FmpMeasure.lean` — i.e., comparable in kind (though the plan's "no new worlds" claims for
T/B/S5 should keep the *termination* argument itself much shorter than K's, since the existing
`modalFuel`/`modalWorldBound` measure can likely be reused with the frame rule counted as a
`persistent` rule) to K's own effort. This confirms the plan's own "under-budgeted" caveat.

**Recommendation for the next dispatch**: attempt Phase 2 (T) scoped down to what is
self-contained per single dispatch — the T rules (`FrameRules.lean`) plus the T soundness arm
(`FrameSoundness.lean`), which is fully achievable and valuable on its own. If the
completeness/decidability portion (`extractModelT`, truth lemma, `tValid`, `Decidable`) does
not fit in the same dispatch, checkpoint at the soundness-arm green milestone and hand off
explicitly rather than risk an incomplete completeness proof.
