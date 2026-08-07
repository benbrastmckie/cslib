# Implementation Summary: Box-Plus Birth Keys for the Keyed S4 Loop Guard

- **Task**: 563 - Adopt Lemmon box-plus pairing at the birth-key level
- **Status**: [COMPLETED]
- **Started**: 2026-08-05T00:00:00Z
- **Completed**: 2026-08-05T00:00:00Z
- **Effort**: ~10.5 hours (matches plan estimate)
- **Dependencies**: None
- **Artifacts**: plans/01_boxplus-birth-keys.md, reports/01_boxplus-birth-keys.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Enriched the keyed S4 loop guard's birth keys so that every transmitted box-context pair records
BOTH members — `(pos, ψ)` and `(pos, □ψ)` for each `T(□ψ)@w` on the branch, dually for
`(neg, ψ)`/`(neg, ◇ψ)`. Landed the mint-payload change (`modalApplyOneS4KeyedMint`, additive over
`modalApplyOne`'s own payload), the key enrichment (`successorBirthContent`'s two new filter
disjuncts), and the two payoff lemmas the enrichment exists to enable
(`blockedRedirect_boxed_boxPos_mem`/`_diaNeg_mem`). All six phases of the plan completed;
`Rules.lean` was never touched.

## What Changed

- `def boxPlusPair`, `def boxPlusExtraS4`, `def BoxPlusClosed`, `def modalApplyOneS4KeyedMint` +
  its two full-pair shape lemmas and two existential-witness-form lemmas — all new, additive.
- `def modalApplyOneS4Keyed`'s two unblocked mint arms now call `modalApplyOneS4KeyedMint`
  instead of raw `modalApplyOne`.
- `def successorBirthContent` gained two appended filter disjuncts (box-plus members); the
  original two disjuncts are kept first and syntactically verbatim, per the plan's constraint.
- `def keysOriginS4` gained a third/fourth disjunct (major mid-implementation discovery, not
  pre-declared in the plan — see Decisions below).
- `modalApplyOne_boxNeg_outputs_subset_S4`/`_diamondPos_outputs_subset_S4` and
  `successorBirthContent_boxNeg_subset_relevantSetFinset`/`_diamondPos_subset_relevantSetFinset`
  extended to cover the box-plus payload/key content.
- ~25 declarations across the file (Class-A migrations, `outputsSubsetUniverse_S4`, `bClosure`
  x2, `worldsContiguousS4` x2, `keysOriginS4` x2, `keyLowerBd` x2) repaired to route through the
  new keyed-mint API.
- New payoff lemmas `blockedRedirect_boxed_boxPos_mem`/`blockedRedirect_boxed_diaNeg_mem`, landed
  sorry-free, standard-axioms-only.
- Several new general-purpose bridge lemmas added along the way:
  `modalApplyOneS4KeyedMint_snd_eq`, `modalApplyOneS4KeyedMint_fst_eq_or_linear`,
  `modalApplyOneS4KeyedMint_outDeg_step`, `relevantSetFinset_boxPlus_mono`,
  `boxPlusExtraS4_label_eq_freshWorld`, `boxPlusExtraS4_outputs_subset_S4` (+ its two halves),
  `boxPlus_pos_disjunct_elim`/`boxPlus_neg_disjunct_elim`.

Only `Cslib/Logics/Modal/Tableau/LoopChecking.lean` was modified. `Rules.lean`,
`FmpMeasure.lean`, `FrameCompleteness.lean`, and `CslibTests/S4LoopGuardRegression.lean` all
carry zero diff.

## Decisions

- **Phases 2 and 3 committed together.** After Phase 2's payload-shape change alone, the file
  does not build (6 Class-B declarations genuinely break, as the plan anticipated), and a red
  build must not be committed outside a declared atomic-batch's own pre-commit intermediate
  states. Phase 3's repairs were completed in the same session before the first commit.
- **`keysOriginS4` extended, not left alone.** Its original two-way origin disjunction
  (`(s',φ')=(sign,ψ) ∨ T(box ψ)@u ∈ b`) is FALSE, not merely hard, once the key records box-plus
  members: `(pos, □χ) ∈ k` comes from `T(□χ)@u ∈ b` (one box), never from the doubly-boxed
  `T(□(□χ))@u ∈ b` the original form would demand. Extended with a permissive third/fourth
  disjunct mirroring `successorBirthContent`'s own box-plus filter arms. This is a standalone
  `def` (never an `S4LoopInv` field), and is orthogonal to the in-file "Redirect-Inertness
  Assembly — REMOVED" section's explicit warning against strengthening `keysOriginS4` to rescue a
  different, since-removed, machine-checked-FALSE lemma — that warning is about forcing a false
  conclusion true; this is a weakening needed to keep a now-bigger-scoped invariant actually true.
- **`successorBirthContent_*_subset_relevantSetFinset`'s hypothesis re-keyed.** Both lemmas now
  take `(modalApplyOneS4KeyedMint ...).fst = RuleResult.linear newForms` instead of raw
  `modalApplyOne`'s, since the raw K payload never contains the boxed transmission the new
  disjuncts need. This let `keyLowerBd`'s proof simplify (the Phase 2/3
  `relevantSetFinset_boxPlus_mono` bridge is no longer needed).
- **`BoxPlusClosed` added as report-required infrastructure, not itself consumed.** The actual
  proof obligations were discharged via the `keysOriginS4` extension and the direct subset-lemma
  restatement; `BoxPlusClosed` documents the intended closure property per report §5.2 but has no
  downstream caller in this landing.
- **`blockedRedirect_unwrapped_diaNeg_mem` needed a one-line syntactic adjustment**
  (`Or.inr ⟨rfl, ?_⟩` → `Or.inr (Or.inl ⟨rfl, ?_⟩)`) since its target disjunct's position shifted
  one level deeper once two more disjuncts were appended after it. The underlying condition
  proved is unchanged; `blockedRedirect_unwrapped_boxPos_mem` needed no change at all.

## Impacts

- Phase 5's mandatory completeness gate (`lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`)
  passes cleanly at 900 jobs both before and after the key enrichment, with the sorry census
  unchanged at 1 and zero edits to `FrameCompleteness.lean` — the structural argument (Hintikka
  conjunct 2 is `True` at both mint shapes) held exactly as the research report predicted.
- Full repo verification baseline unchanged: `lake build Cslib` green at 3313 jobs, `lake test`
  green (9378/9378, `S4LoopGuardRegression` unedited), axiom count unchanged at 26, `lake shake`
  unchanged at 9 findings (none in Modal/Tableau), `lake lint` unchanged at 145 pre-existing
  repo-wide findings with zero new findings in `LoopChecking.lean`, `checkInitImports` and
  `lint-style` both exit 0.
- The box-plus payoff lemmas (`blockedRedirect_boxed_boxPos_mem`/`_diaNeg_mem`) are available for
  a future route (1) successor plan, per the in-file "Redirect-Inertness Assembly — REMOVED"
  section's own recommended repair.

## Follow-ups

- None identified. All six plan phases completed with no blockers.

## References

- `specs/563_tableau_boxplus_birth_keys/plans/01_boxplus-birth-keys.md`
- `specs/563_tableau_boxplus_birth_keys/reports/01_boxplus-birth-keys.md`
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
