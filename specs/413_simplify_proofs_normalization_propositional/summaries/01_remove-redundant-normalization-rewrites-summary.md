# Execution Summary: Remove Redundant listImp/bigconj Normalization Rewrites

- **Task**: 413 - simplify_proofs_normalization_propositional
- **Plan**: `specs/413_simplify_proofs_normalization_propositional/plans/01_remove-redundant-normalization-rewrites.md`
- **Status**: Implemented, all 7 phases `[COMPLETED]`

## What Was Done

All 20 `simp only [listImp_*|bigconj_*]` rewrite invocations in the repository, plus 19
accompanying `unfold ListDeriv` lines, were deleted and replaced with the bare `exact` that
already discharged the goal by defeq (`ListDeriv`/`listImp`/`Deriv` are all transparent
`rfl`-based definitions). Four one-line defeq-reliance doc comments were added to the four
per-logic `derivTreeToList*` bridge lemmas to document the dependency the simplified proofs
now carry explicitly.

### Files Modified

- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — `unfoldListImp`'s `[]` case simplified
  from `by simpa only [listImp_nil] using d` to plain `d`; deleted a `simp only [listImp_cons]
  at d` line. This is the single data-level (non-`Prop`) change in the set; verified under full
  `lake build` only, per the plan's criterion 4.
- `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean` — collapsed a 4-line
  `have`/`unfold`/`simp only`/`exact` block in `list_deriv_reflection` to one `exact` line,
  preserving the `-- φ ∈ Ψ, use ih and then weaken` comment.
- `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` — two `unfold ListDeriv; simp only
  [listImp_nil]; exact ...` chains collapsed to bare `exact` in `mcs_mp_axiom` and
  `mcs_theorem_in_mcs`.
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` — four `simp only [bigconj_*]` lines deleted
  from `bigconj_mem_derivable` and `bigconj_derivable_intro`.
- `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` — `derivTreeToList`'s four arms
  (`ax`, `assumption`, `modusPonens`, `weakening`) stripped of redundant
  `simp only [propAlgDS, treeAlgDS, algebraicDerivationSystem]` / `unfold ListDeriv` prologues;
  defeq-reliance comment added to the lemma's docstring.
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` — same for `derivTreeToList`'s five arms;
  the `necessitation` arm's `have h_thm := by unfold ListDeriv at ih; simp only [listImp_nil]
  at ih; exact ih` restatement collapsed so `ih` is used directly. The `-- ih : ...` and
  `-- Box-necessitation: ...` comments were preserved as standalone comments per the plan;
  a third comment restating the trivial one-line `exact` was judged non-load-bearing and not
  restored (documented in Phase 6).
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — same treatment for
  `derivTreeToListFc`'s seven arms, including collapsing the `temporal_necessitation` and
  `temporal_duality` arms' `h_thm`/`h_dual` restatements.
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — same for
  `derivTreeToListFc`'s eight arms (largest single file win).

### Task Description Reconciliation

`specs/state.json` task 413's description was updated (Phase 7) to reflect the confirmed
repo-wide scope: the task description originally named `Propositional/` as the target, but a
repo-wide grep found zero `listImp`/`bigconj` rewrite sites there — all 20 sites live in
`Foundations/`, `Modal/`, `Temporal/`, and `Bimodal/`, plus one file under
`Propositional/Metalogic/`. `TODO.md` was regenerated via `generate-todo.sh`.

## Plan Deviations

None. All phase task lists were executed exactly as specified in the plan; no step was
skipped, altered, or deferred.

## Verification

- **Phase 1 baseline** (`baseline.md`): 20 residual sites / 8 files confirmed exactly matching
  the report's hypothesis. The report's "15 accompanying unfolds" figure was a
  counting-convention mismatch (raw grep shows 24 total `unfold ListDeriv` occurrences, only 19
  of which the patch removes) — not a scope error; documented, not blocking. The report's
  "exactly 4 pre-existing sorry" hypothesis undercounted by one: the observed baseline is 5
  `sorry` warnings across 4 files (extra one in `Modal/Tableau/FrameSoundness.lean:1252`, an
  unrelated file explicitly documented in-source as "retained by explicit user decision").
  This observed 5-warning baseline, not the report's 4-warning guess, was used for every
  downstream sorry-freeness check.
- Each phase's build (module-scoped for Prop-only phases, full `lake build` for the two
  data-level/adjudication phases) was green with build times at or below the Phase 1 baseline
  envelope for every affected module.
- `lean_verify` on every affected declaration (`mcs_mp_axiom`, `mcs_theorem_in_mcs`,
  `list_deriv_reflection`, `bigconj_mem_derivable`, `bigconj_derivable_intro`,
  `unfoldListImp`, `listDerivToTree`, and all four `derivTreeToList*`) reports no `sorryAx` and
  the standard axiom set (`propext`, `Classical.choice`, `Quot.sound`, or a subset).
- Full-build `sorry` warning set at the end is byte-identical to the Phase 1 observed baseline
  (same 5 warnings, same files/lines) — no new sorry, none of the pre-existing ones touched.
- Final residual-site grep: **0** (no Reasoned Exclusions were needed anywhere).
- Full CSLib 7-step CI pipeline (cache already warm): `lake build` green (3309 jobs);
  `lake exe checkInitImports` clean; `lake lint` clean for all 8 changed files (361 lines of
  pre-existing, unrelated output remain); `lake exe lint-style` clean; `lake test` green
  (9374 jobs); `lake shake --add-public --keep-implied --keep-prefix` proposes nothing for any
  of the 8 changed files.
- Final diffstat: **8 files changed, 35 insertions(+), 74 deletions(-)** (net 39 lines
  removed) — file count matches the report's verified patch exactly; the extra 25 insertions
  versus the report's raw patch are the four Phase 6 defeq-reliance doc comments.

## Artifacts

- `specs/413_simplify_proofs_normalization_propositional/baseline.md`
- `specs/413_simplify_proofs_normalization_propositional/summaries/01_remove-redundant-normalization-rewrites-summary.md` (this file)
- `specs/413_simplify_proofs_normalization_propositional/plans/01_remove-redundant-normalization-rewrites.md` (all 7 phases `[COMPLETED]`)
