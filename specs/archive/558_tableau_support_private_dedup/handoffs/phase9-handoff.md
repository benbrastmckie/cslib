# Phase 9 Handoff — Delete Tier-2 duplicates (remaining four files)

**Status**: [COMPLETED]

## What happened

Deleted 6 FmpMeasure-origin Tier-2 duplicates across 3 families: `mem_modalUniverse_of_B`/`_Five`,
`modalUniverse_mem_formula_B`/`_Five`, `modalSubfmls_trans_B`/`_Five` (in `BDriver.lean` and
`FiveSimplification.lean`), routed to the now-public `FmpMeasure.lean` declarations. Applied
Phase 8's lesson: confirmed each used the generic `modalUniverse`/`modalWorldBound`, not a
frame-specific type, before deleting.

**Deviation**: `FrameSoundness.lean` and `FrameCompleteness.lean` had ZERO FmpMeasure-origin
Tier-2 duplicates remaining — confirmed by census before editing, neither file was touched this
phase. Their remaining census entries (`hasEdge_addEdge_mono_FS`, `modalApplyOneS5_fresh_local`,
etc.) are all Tier-3 (Phase 10 territory: origin private in a non-FmpMeasure file, or public-origin
exclusions).

Full invariants table green: build 3313 jobs; checkInitImports 0; lint-style 0; shake 0
Modal/Tableau findings; sorry census exactly 1; axiom count 0; six landed Decidable instances +
`modalTableauS4Keyed_complete` confirmed present (full build success, `FrameCompleteness.lean`
untouched). Post-phase census: **20 duplicates / 20 families**, all remaining entries Tier-3.

## Continuation pointer

Resume at **Phase 10**: Tier-3 triage and residue accounting. Re-run the full census
(`python3 specs/558_tableau_support_private_dedup/scripts/census.py`) — the current 20-family
list is the definitive residue to classify. Cross-reference against the plan's pre-declared
`Reasoned Exclusions` table (8 public-origin families) and the class-(a) candidate list
(`CompletenessLoop.lean`, `TDriver.lean`, `FiveSimplification.lean`, `Soundness`/`SoundnessStep`,
`Completeness.lean` origins), PLUS the two families discovered but not plan-named in Phase 1
(`modalApplyOneT_branchingLength`, `modalApplyOneT_persistentFresh`, both `LoopChecking.lean` vs
`TDriver.lean`). Every one of the current 20 families must land in either a resolved class-(a)
consolidation or the Reasoned Exclusions table — an unclassified survivor is a plan gap per the
plan's own explicit instruction.

Apply Phase 8's type-suffix lesson here too: before de-privatizing any class-(a) origin and
deleting its copy, confirm the copy is stated over the SAME type as the origin, not a
frame-specific variant.
