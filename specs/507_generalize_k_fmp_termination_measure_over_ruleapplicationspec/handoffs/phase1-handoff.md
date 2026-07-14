# Task 507 Phase 1 Handoff: RuleApplicationSpec Extension

## Status: [COMPLETED], green

## What was done

Extended `RuleApplicationSpec` (`Cslib/Logics/Modal/Tableau/GenericDriver.lean`) with three new
per-single-call step obligations, discharged for `modalApplyOne`:

- `rankStep` — generic form of the per-call rank-preservation fact `modalStepBranch_exists_rank'`
  needs. Discharged by `modalApplyOne_rank_step` (`FmpMeasure.lean`).
- `outDegStep` — generic form of the per-call outDeg/expanded-set counting fact
  `modalStepBranch_preserves_outDegEq` needs. Discharged by `modalApplyOne_outDeg_step`.
- `knownWorldsStep` — generic form of the per-call known-worlds dichotomy
  `modalStepBranch_knownWorlds` needs. Discharged by `modalApplyOne_knownWorlds_step`.

Each discharge lemma in `FmpMeasure.lean` is a **verbatim extraction** of the proof body that was
formerly inlined as a local `have hcases := by <proof>` inside the corresponding helper lemma;
the helper lemma itself was left otherwise untouched except for replacing the inline proof with a
one-line call to the new standalone lemma. Zero proof-content change; pure refactor to make the
per-call fact nameable and hence liftable into the `RuleApplicationSpec` interface.

## Key finding (for Phase 5 continuation)

`modalStepBranch_potential_step`'s own body (the crux lemma), once its three callee lemmas
(`modalStepBranch_exists_rank'`, `modalStepBranch_preserves_outDegEq`,
`modalStepBranch_knownWorlds`) are generalized via the three new fields, needs **no further
field beyond `freshLocal`** — verified by direct reading of its ~160-line body. Every other
`rcases hfstc : (modalApplyOne sf b acc).fst with nf | brs | nf | _` scattered through the
dependency chain is a case-split on `RuleResult`'s four constructors (rule-agnostic, needs no
spec support), not on `modalApplyOne`'s five internal rule shapes — only the three lemmas above
inline the deeper 5-way catalog split, and all three are now behind fields.

`outDeg_le_of_expandedNodup` and `modalStepBranch_eClosure` need **no generalization at all**:
both are already fully rule-agnostic (the former is pure `Accessibility`/list reasoning; the
latter's conclusion only concerns `sf` itself, already known to be in the universe via `sf ∈ b`).
`modalStepBranch_preserves_accTargetsKnown` needs only `spec.freshLocal` (no new field) — its
`rcases modalApplyOne_fresh_local ...` call generalizes directly to `spec.freshLocal` with no
further change.

## Verification

- `lake build` (full project): green (3221 jobs).
- `lake exe checkInitImports`: green.
- `lake lint`: pre-existing unrelated failure in `PrimeExclusion.lean` only; zero new warnings
  in `FmpMeasure.lean`/`GenericDriver.lean`.
- `lake exe lint-style`: green.
- `lake test`: green (`CslibTests` suite).
- `lake exe mk_all --module`: no update necessary.
- `lake shake --add-public --keep-implied --keep-prefix`: 82 warnings on
  `FmpMeasure.lean`+`GenericDriver.lean`, identical to pre-change baseline (no new debt).
- `lean_verify modalApplyOne_spec`: axioms = `{propext, Classical.choice, Quot.sound}`, zero
  sorry.
- `lean_verify` on all three new discharge lemmas: same standard-axiom set, zero sorry.

## Next steps (Phases 2-4)

Phases 2 (outDeg cluster), 3 (rank-existence cluster), 4 (knownWorlds/accTargetsKnown cluster)
should now re-derive `modalStepBranch_preserves_outDegEq`, `modalStepBranch_exists_rank'`,
`modalStepBranch_preserves_accTargetsKnown`, `modalStepBranch_knownWorlds`,
`modalStepBranch_eClosure` as `_gen` lemmas over `(apply, spec)`, invoking
`spec.outDegStep`/`spec.rankStep`/`spec.freshLocal`/`spec.knownWorldsStep` in place of the
`modalApplyOne`-hardcoded calls, then re-deriving the concrete K versions as
`_gen … modalApplyOne modalApplyOne_spec` corollaries with byte-identical statements. The
driver-unfolding boilerplate around each field call (the `simp only [modalStepBranch] at
hstep; obtain ⟨sf, hsfmem, hsf⟩ := ...; split_ifs at hsf with hexp; rcases hfstc : (modalApplyOne
sf b acc).fst with nf | brs | nf | _` dance) is already rule-agnostic and should translate to
`modalStepBranchGen apply`/`apply sf b acc` mechanically.
