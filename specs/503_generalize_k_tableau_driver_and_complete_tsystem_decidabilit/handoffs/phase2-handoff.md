# Phase 2 Handoff -- Task 503

## Status: COMPLETED

## What was done

Created `Cslib/Logics/Modal/Tableau/GenericDriver.lean` (new file, registered in `Cslib.lean`
via `lake exe mk_all --module`):

- `RuleApplicationSpec (apply : RuleApply Atom) : Prop` -- a three-field structural-hypothesis
  bundle:
  - `freshLocal`: world-creation confinement (mirrors `modalApplyOne_fresh_local`).
  - `outputsSubsetUniverse`: catalog membership (mirrors `modalApplyOne_outputs_subset`).
  - `persistentFresh`: persistence/measure hook (mirrors `modalApplyOne_persistent_props`).
- `modalApplyOne_spec : RuleApplicationSpec modalApplyOne` -- the trivial K witness, each field
  discharged directly by the corresponding existing public K lemma.
- A module docstring documenting field provenance, the downstream-reuse contract for tasks
  504 (S5/KB5), 505 (B), 506 (S4, explicitly excluded), and a **"Known Limitation"** section
  (see below).

One supporting visibility change: `FmpMeasure.lean`'s `modalApplyOne_fresh_local` was changed
from `private lemma` to `lemma` (no proof or statement change) so `GenericDriver.lean` could
reuse it directly for `modalApplyOne_spec`'s `freshLocal` field.

## Known Limitation (read before attempting Phase 3)

The three fields in `RuleApplicationSpec` are **necessary but not proven sufficient** to
re-derive `FmpMeasure.lean`'s `modalStepBranch_potential_step` (line ~2146, the actual
termination-measure crux) for an abstract `apply`. I read that lemma's full proof (and its
direct dependency chain: `modalStepBranch_exists_rank'` ~line 1058,
`modalStepBranch_knownWorlds` ~line 1901, `modalStepBranch_preserves_outDegEq` ~line 1365,
`outDeg_le_of_expandedNodup` ~line 1509, plus ~10 further private helpers) before writing the
bundle. Its ~160-line proof (and the ~900-line surrounding apparatus, lines ~1058-2415) does
NOT go through any bundle-shaped hypothesis today -- it `rcases`es directly on
`(modalApplyOne sf b acc).fst`/`.snd` at every step, exploiting the *exact* four concrete rule
shapes (propositional/boxPos/diamondNeg/diamondPos/boxNeg) and their specific interaction with
`outDeg`/`modalKnownWorlds`/rank-map bookkeeping. Generalizing this over `RuleApplicationSpec`
is a from-scratch re-proof of an intricate potential-function argument, not a mechanical
threading exercise -- see Phase 3's [BLOCKED] status below for the recommendation.

## Verification (all green, zero regression)

- `lake build` (full project, 3217 jobs) -- green
- `lake exe checkInitImports` -- clean
- `lake lint` -- 1 pre-existing error (`PrimeExclusion.lean`, unrelated), zero from our files
- `lake exe lint-style` -- clean
- `lake shake --add-public --keep-implied --keep-prefix` -- only the pre-existing
  "remove import Cslib.Init" style suggestion, which matches many other files' pattern in the
  codebase and is intentionally NOT applied (explicit `Cslib.Init` import is mandatory per
  `checkInitImports`)
- `lake exe mk_all --module` -- `Cslib.lean` updated to register `GenericDriver.lean`
- `lake test` -- exit 0, full `CslibTests/` suite green
- `grep -rn "\bsorry\b\|^axiom " GenericDriver.lean` -- zero sorry, zero axiom (the one grep
  hit is a docstring mention, not a tactic)

## Next phase

Phase 3 (generalizing `FmpMeasure.lean`'s termination measure) is being assessed against the
plan's own explicit [BLOCKED] fallback given the scope revealed above; see the Phase 3 section
of the plan file for the documented blocker.
