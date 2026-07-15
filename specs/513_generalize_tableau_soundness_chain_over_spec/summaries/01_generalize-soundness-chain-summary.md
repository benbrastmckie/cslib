# Implementation Summary: Task #513 — Generalize the Tableau SOUNDNESS Chain over the Rule-Application Interface

- **Task**: 513 - Generalize the tableau soundness chain over the abstract rule-application interface
- **Status**: [COMPLETED]
- **Plan**: plans/01_generalize-soundness-chain.md
- **All 6 phases completed**, sorry-free, standard axiom-trio only.

## What Was Built

Generalized the tableau SOUNDNESS chain (`modalStepBranch_preserves_sat`,
`modalExpandBranches_closed_unsat`) over the abstract rule-application interface
`(apply : RuleApply Atom, FC : FrameCondition)`, then instantiated it at `modalApplyOneT` to
expose `modalTableauT_sound`, completing `tValid_decides` / `instDecidableTValid` (the task 503
Phase 6 target).

### Phase 1 — K arm extraction + prep (`SoundnessStep.lean`, `FrameSoundness.lean`)
- Extracted `modalApplyOne_boxPos_sound` / `modalApplyOne_diaNeg_sound`: standalone
  `RuleResultSat`-valued lemmas isolating the two propagating arms of the K monolith, with zero
  proof-content change (the monolith itself is untouched).
- De-privatized `negImp_alpha_preserved` and added `negImp_alpha_preserved_gen` (FC-lifted
  variant) plus `modalClosed_unsatIn` in `FrameSoundness.lean`.

### Phase 2 — The crux: `modalStepBranchGen_preserves_satIn` (`FrameSoundness.lean`)
- ~420-line FC-threaded port of `modalStepBranch_preserves_sat` over `(apply, FC)`, with three
  raw hypotheses: `hAgree` (S-agree, agreement with `modalApplyOne` off the two propagating
  shapes), `hBoxPos`/`hDiaNeg` (S-boxPos/S-diaNeg, frame-relativized semantic soundness on the
  two propagating shapes). All propositional and minting arms port via `hAgree` reducing to
  `modalApplyOne`, threading the (unchanged) `FC m.r` witness through every
  `branchSatisfiableIn` tuple — the ambient Kripke model `(W, m)` is never rebuilt, only `f` is
  pointwise extended by the two minting arms. Landed on the first build attempt.
- Required adding a private→public import fix: `Mathlib.Data.List.Forall2` was only privately
  imported by `Soundness.lean` and did not propagate transitively under the `module`/`public
  import` system; added directly to `FrameSoundness.lean`.

### Phase 3 — Generic fuel induction: `modalExpandBranchesGen_closed_unsatIn` (`FrameSoundness.lean`)
- ~180-line port of `modalExpandBranches_closed_unsat`, feeding the Phase 2 crux at the step and
  `modalClosed_unsatIn` at the closed leaf; freshness maintenance reuses task 510's already-generic
  `modalStepBranch_preserves_accFreshInv_gen`.

### Phase 4 — K zero-regression (`FrameSoundness.lean`, `Soundness.lean`)
- Added `modalTableau_sound_frame_gen`: re-derives K soundness through `frameValid`/`trivialFC`
  via the generic chain (`modalExpandBranchesGen_closed_unsatIn` at `apply := modalApplyOne`),
  discharging `hAgree` by `rfl`, `hBoxPos`/`hDiaNeg` by Phase 1's extracted lemmas, `hFreshLocal`
  by `modalApplyOne_fresh` (de-privatized in `Soundness.lean`, docstring-only change).
- Confirmed via `git diff` that K's canonical `Type*` public API
  (`modalStepBranch_preserves_sat`, `modalExpandBranches_closed_unsat`, `modalTableau_sound`,
  `kValid`, `modalTableau_decides`, `instDecidableKValid`) remains byte-identical and untouched
  — the only changes anywhere in `Soundness.lean`/`CompletenessLoop.lean` are `private` →
  public visibility flips with added docstrings.

### Phase 5 — T soundness discharges + `modalTableauT_sound` (`FrameCompleteness.lean`, `TDriver.lean`)
- Added `hAgreeT` (verbatim `modalApplyOneT_eq_of_not_boxPos_diaNeg`),
  `modalApplyOneT_boxPos_soundIn` / `modalApplyOneT_diaNeg_soundIn` (splitting `RuleResultSat`
  over `modalApplyOneT`'s `kForms ++ selfNew.filter …` append: the `kForms` half reuses Phase
  1's K lemmas, the `selfNew` half is justified directly by reflexivity), and
  `modalTableauT_sound` (contrapositive over `reflFC` via `modalExpandBranchesGen_closed_unsatIn`
  at `apply := modalApplyOneT`).
- De-privatized four `TDriver.lean` helper lemmas (`modalApplyOneT_boxPos_fst`/`_snd`,
  `modalApplyOneT_diamondNeg_fst`/`_snd`) so `FrameCompleteness.lean` could consume them
  directly, avoiding an import-cycle-inducing dependency on `FmpMeasure.lean`.

### Phase 6 — Decidability wiring + CI sweep (`FrameCompleteness.lean`)
- Added `tValid_decides` and `instDecidableTValid` as one-liners mirroring K's
  `modalTableau_decides` / `instDecidableKValid`, completing the task 503 Phase 6 target.
- Full CSLib CI pipeline run and green: `lake build` (full), `lake exe checkInitImports`,
  `lake lint` (3 pre-existing errors, all in unrelated files `CS5Canonical.lean`/
  `PrimeExclusion.lean`, none introduced by this task), `lake exe lint-style`, `lake shake
  --add-public --keep-implied --keep-prefix` (zero import-diff entries for any file touched by
  this task), `lake test`.

## Deviations from the Plan

- **P2/P3 hypothesis signatures deviate slightly from the report's `hBoxPos`/`hDiaNeg`
  sketch** (report §3.2, §4): the report's signatures omit an explicit membership hypothesis
  (`⟨.pos, .box φ, lbl⟩ ∈ b`), but this is required for soundness (without it, nothing forces
  `Satisfies m (f lbl) (box φ)` to hold). Added `hmem : ⟨.pos, .box φ, lbl⟩ ∈ b` /
  `hmem : ⟨.neg, .diamond φ, lbl⟩ ∈ b` as an explicit hypothesis on `hBoxPos`/`hDiaNeg`,
  matching what the crux actually has in hand at the call site (the found `sf ∈ b`). This is a
  strengthening of the exact hypothesis shape, not a weakening — all downstream discharges (K
  Phase 1, T Phase 5) satisfy it trivially since they already receive `hsfmem`/the membership
  proof from their own call sites.
- **`hAgree`'s hypothesis packaged as a single conjunction** rather than two curried
  hypotheses (report §3.2 shows curried `→ →`): packaged to match
  `modalApplyOneT_eq_of_not_boxPos_diaNeg`'s existing signature exactly, so the T discharge is
  truly zero-new-proof-content (`hAgreeT := modalApplyOneT_eq_of_not_boxPos_diaNeg` verbatim).
- **`modalApplyOneT_boxPos_soundIn`/`_diaNeg_soundIn`'s `selfNew` half is derived directly from
  reflexivity** rather than routed through `branchSatisfiableIn_reflFC_boxPos_mem`/
  `modalTBoxSelf_sound` (plan's suggested discharge path): those lemmas existentially quantify
  their own witnessing model, so they cannot be applied as black boxes to supply a `sfSat m f`
  fact about the caller's own specific `(m, f)`. The reflexivity insight used is identical
  (`hFC.refl (f lbl) : m.r (f lbl) (f lbl)`); this is an equivalent, more direct proof of the
  same semantic fact, not new mathematical content.
- **`modalTableau_sound_frame` (the original K-through-`frameValid` re-derivation) was kept
  unchanged**; a new theorem `modalTableau_sound_frame_gen` was added alongside it to
  demonstrate the generic-chain zero-regression path, since `modalTableau_sound_frame` is not
  on the plan's byte-identical-preservation list but keeping both avoids any risk to existing
  downstream call sites of `modalTableau_sound_frame`.

No phase was `[BLOCKED]`. No `sorry`, no vacuous placeholder, no new axiom anywhere in this
task's changes.

## Files Changed

- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` — Phase 1: extracted arm lemmas,
  de-privatized `negImp_alpha_preserved`.
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — Phases 1-4: `modalClosed_unsatIn`,
  `negImp_alpha_preserved_gen`, `modalStepBranchGen_preserves_satIn` (crux),
  `modalExpandBranchesGen_closed_unsatIn`, `modalTableau_sound_frame_gen`.
- `Cslib/Logics/Modal/Tableau/Soundness.lean` — Phase 4: de-privatized `modalApplyOne_fresh`.
- `Cslib/Logics/Modal/Tableau/TDriver.lean` — Phase 5: de-privatized four helper lemmas.
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — Phases 5-6: `hAgreeT`,
  `modalApplyOneT_boxPos_soundIn`, `modalApplyOneT_diaNeg_soundIn`, `modalTableauT_sound`,
  `tValid_decides`, `instDecidableTValid`.

## Verification

- Zero `sorry` in all five modified files (grep-verified).
- Axiom-trio only (`propext`, `Classical.choice`, `Quot.sound`) on every new public
  declaration, double-checked via `lake env lean` `#print axioms` (not just the MCP
  `lean_verify` tool, which spuriously reported `sorryAx` once and was cross-checked and
  overruled).
- Full CSLib CI green: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe
  lint-style`, `lake shake --add-public --keep-implied --keep-prefix`, `lake test`.
- K's public soundness API confirmed byte-identical via `git diff` against the pre-task commit.

## Downstream Impact

Unblocks:
- Task 503 Phase 6 (`Decidable (tValid φ)`) — **directly completed** by this task
  (`tValid_decides` + `instDecidableTValid`).
- Task 505 (B) and task 504 (S5) — inherit the entire generic soundness chain
  (`modalStepBranchGen_preserves_satIn`, `modalExpandBranchesGen_closed_unsatIn`) for free; each
  must supply only its own `hAgree`/`hBoxPos`/`hDiaNeg` triple plus a `freshLocal` fact.
