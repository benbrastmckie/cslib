# Summary: S5 Termination Machinery Plan v5, Phases 0-10

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Status**: [IN PROGRESS] (phases 0-10 of 24 complete; phase 11 onward remain)
- **Started**: 2026-07-15T00:00:00Z
- **Completed**: 2026-07-15 (this dispatch: phase 10)
- **Effort**: ~11 hours (10 phases: kill test, rule, congruence, refutation, arithmetic, generalization, invariant, counting crux, gate, spec split, rank-free Aux invariant)
- **Dependencies**: Task 514 (literature grounding); Task 504 (parent, `modalApplyOneS5`/`extractModelS5*`/`modalTruthLemmaS5` landed)
- **Artifacts**:
  - `Cslib/Logics/Modal/Tableau/S5Simplification.lean` (modified)
  - `Cslib/Logics/Modal/Tableau/BDriver.lean` (modified)
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (modified)
  - `Cslib/Logics/Modal/Tableau/GenericDriver.lean` (modified)
  - `Cslib/Logics/Modal/Tableau/TDriver.lean` (modified)
  - `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (modified)
  - `specs/515_s5_universal_rule_termination_unblock_504/plans/05_s5-termination-machinery.md` (phase status updates)
- **Standards**: `.claude/rules/artifact-formats.md`, `.claude/rules/state-management.md`, `.claude/rules/git-workflow.md`, `.claude/rules/plan-format-enforcement.md`
- **Type**: cslib

## Overview

Plan v5 replaces the birth-key pigeonhole architecture (plan v2, dead per deep research) with a
witness-reuse S5 rule and a linear tag-injection world budget, retargeted at K's own
termination machinery. This dispatch executed Phases 0-6 of the 24-phase plan (the S5 chain,
Phases 0-14, is independent of and precedes the Euclidean 5/KB5 route, Phases 15-23). Every
phase closed sorry-free, CI-green, with an incremental commit.

## What Changed

- **Phase 0**: Scratch-verified (no file edit) that mint tags `(pos,ψ)`/`(neg,ψ)` derived from
  `◇ψ`/`□ψ` subformulas are reachable in `modalSubfmls`/`signedSubfmls` under the
  `neg φ = φ.imp .bot` encoding, via the existing public `modalSubfmls_self_mem`.
- **Phase 1** (`S5Simplification.lean`): Landed `witnessWorldS5`, `modalApplyOneS5w`
  (guard-less witness-reuse rule intercepting exactly the two K-inherited mint shapes),
  `witnessWorldS5_mem`, two `rfl` bridges, and `modalApplyOneS5w_eq_of_not_mint_shape`.
- **Phase 2** (`S5Simplification.lean`): Landed `hintikka_congr`
  (`modalHintikkaSetGen modalApplyOneS5w ↔ modalHintikkaSetGen modalApplyOneS5`), porting the
  entire landed countermodel half of S5 completeness with zero edits to `FrameCompleteness.lean`.
- **Phase 3** (`S5Simplification.lean`, `FrameCompleteness.lean`): Landed the R7 (fuel
  domination) refutation as four `decide`-backed theorems chaining single
  `modalStepBranchGen modalApplyOneS5` steps (the full fuel-wrapped driver does not
  kernel-reduce, same limitation `LoopChecking.lean` already documents). Corrected three
  docstrings: the file-header note, the `modalTableauS5` note (was: "modalFuel is sufficient
  here too" -- false by execution), and `FrameCompleteness.lean`'s 5/KB5 note (was a scheduling
  framing; corrected to the proven frame-class inclusion obstruction, citing
  `probes/five-s5-separation.lean` by theorem name, stated as a route obstruction not an
  impossibility).
- **Phase 4** (`S5Simplification.lean`): Landed `modalOps`, `modalOps_le_complexity`,
  `modalOps_lt_worldBound` (the load-bearing arithmetic bounding mint tags by K's own
  `modalWorldBound`), `mintTags`, `mintTags_card_le_modalOps`.
- **Phase 5** (`BDriver.lean`): Generalized `modalExpandBranchesGen_openBranch_accSourcesKnown`'s
  double induction over an abstract predicate (`modalExpandBranchesGen_openBranch_gen`),
  re-derived the original B theorem from it (zero regression), and landed the new
  `modalExpandBranchesGen_openBranch_accTargetsKnown` -- previously missing across the whole
  repo and required as `modalOpenBranchS5_countermodel`'s `hTgt` argument.
- **Phase 6** (`S5Simplification.lean`): Landed `S5wTagInv`, `usedTags`, `usedTags_mono`, two
  new subformula-closure lemmas (`mem_mintTags_of_diamond_mem`/`_of_box_mem`), and
  `modalApplyOneS5w_outputs_tags`.
- **Phase 7** (`S5Simplification.lean`): Landed the counting crux -- `S5wWorldInv`,
  `modalStepBranchS5w_preserves_worldInv`, `modalMaxWorld_lt_worldBound_of_S5w` -- plus the
  supporting `witnessWorldS5_none_not_mem_usedTags` helper, `modalApplyOneS5w_fresh_local`,
  `modalStepBranchS5w_preserves_accTargetsKnown`, and the central per-call dichotomy
  `modalApplyOneS5w_step`. This is the drop-in replacement for
  `modalMaxWorld_lt_worldBound_of_phiBound`: no rank, no potential, no pigeonhole, no powerset,
  no birth keys.
- **Phase 8** (gate, no production Lean): R1 scratch probe -- **GO** verdict. A scratch
  `lean_run_code` example (`probes/phase8-r1-reuse-soundness.lean`) confirms, sorry-free and
  against the real project imports, that the new soundness case for the reuse edge `w→w'`
  (an existing `w'` already carrying `⟨s,φ,w'⟩`) discharges via the landed
  `accReachableInv_related_s5` (`FrameSoundness.lean:1384`) plus one line of replay from the
  branch's own satisfaction witness -- no model/`f` extension needed. `lean_references` on
  `modalApplyOneS5_snd_eq` (`S5Simplification.lean:358`) found 8 real consumers; none matched the
  plan's cited line numbers (stale, predating Phases 4-7's ~1,500 new lines), but the taxonomy and
  count matched exactly (the reusable `fresh_local` family plus `S5g`-prefixed sites Phase 14
  already retires) -- a documented citation-drift finding, not a blocker. Re-proof size estimate:
  ~150-250 new lines, grounded in measured comparables (`modalStepBranchS5_preserves_satIn`'s
  case sizes, `modalS5BoxAll_soundIn`'s packaging pattern, Phase 7's own preservation-lemma
  sizes) -- well under the 400-line kill threshold. See the plan's Phase 8 completion note for
  the full writeup.
- **Phase 9** (`GenericDriver.lean`, `TDriver.lean`, `BDriver.lean`, `CompletenessLoop.lean`,
  `S5Simplification.lean`): Split `RuleApplicationSpec` into `RuleApplicationSpecCore` (the nine
  fields the Hintikka/saturation machinery consumes: `freshLocal`, `outputsSubsetUniverse`,
  `persistentFresh`, `branchingLength`, `localShapeInvariance`, `boxPosNotExpanding`,
  `diaNegNotExpanding`, and the two witness fields renamed+weakened to `boxNegWitness'`/
  `diaPosWitness'` -- existentially quantified on the witness world rather than fixed at
  `modalNextWorld b`) plus `RuleApplicationSpec extends RuleApplicationSpecCore` (adding
  `rankStep`/`outDegStep`/`knownWorldsStep`, the three fields Phase 2's counterexample proved
  unreachable for any S5 rule). Landed `RuleApplicationSpec.toCore` and
  `modalApplyOneS5w_specCore : RuleApplicationSpecCore modalApplyOneS5w` -- all nine fields
  discharged via the two-layer agreement chain `modalApplyOneS5w → modalApplyOneS5 →
  modalApplyOne`, a new hypothesis-free combined F9/F10 shape fact
  (`modalApplyOneS5_boxPos_diaNeg_shape`), and local re-derivations of `modalUniverse`'s
  membership constructors/extractors (`mem_modalUniverse_of_S5w`,
  `modalUniverse_mem_formula_S5w`; the FmpMeasure.lean originals are `private`, so re-derived
  here matching this file's existing `_S5`/`_S5w` re-derivation convention).
  `modalApplyOneT_spec`/`modalApplyOneB_spec` needed only a 3-line existential-wrapping adapter
  each for the two renamed fields -- verified by building, not assumed.
- **Phase 10** (`CompletenessLoop.lean`): Landed the rank-free loop invariant with the `Aux`
  parametrization, exactly per the plan's fix (not the bare-scalar hazard it warns against).
  `AuxStepPreserved (apply) (Aux)` and `AuxBounds (φ0) (Aux)` state the two obligations any
  `Aux : List (SignedFormula ...) → Accessibility → Prop` must satisfy. `ModalLoopInvHintikka
  (apply) (φ0) (Aux) (b e) (acc)` bundles the five rank-free `ModalPotentialInv` conjuncts
  (`bClosure`, `eClosure`, `eNodup`, `accFresh`, `accKnown`), an opaque `aux : Aux b acc` field,
  and the five Hintikka-witness conjuncts unchanged from `ModalLoopInvGen` -- 11 fields,
  confirming the plan's arity-change warning (`ModalLoopInvGen`'s 7 rank-scoped fields vs. this
  structure's 11). K's instantiation `ModalLoopAuxK` existentially quantifies a rank map
  witnessing `ModalPotentialInv` plus the `phiBound` conservation identity; S5w's instantiation
  `ModalLoopAuxS5w` is `S5wTagInv ∧ S5wWorldInv`, needing no rank map. Both `AuxBounds` instances
  are proved outright, S5w's `AuxStepPreserved` is proved outright (a direct corollary of the
  already-landed `modalStepBranchS5w_preserves_worldInv`), and the full bridge
  `ModalLoopInvGen_iff_hintikka_auxK : (∃ rank, ModalLoopInvGen apply φ0 b e acc rank) ↔
  ModalLoopInvHintikka apply φ0 (ModalLoopAuxK φ0 e) b e acc` confirms K's instantiation is
  logically equivalent to the existing rank-based invariant, not merely elaborating. K's own
  `AuxStepPreserved` is intentionally left to Phase 11 (the step-preservation port). Added one
  new import: `public import Cslib.Logics.Modal.Tableau.S5Simplification`.

## Decisions

- Phase 3's R7 refutation could not embed a `decide`/`rfl` proof of the full fuel-wrapped
  `modalExpandBranchesGen` (its nested well-founded recursion does not kernel-reduce even at
  small fuel). Substituted a chain of four single `modalStepBranchGen` steps (each genuinely
  non-recursive and `decide`-reducible), matching the same evidentiary strength and independently
  cross-checked against the research report's `#eval` table (fuel 10/20/40 -> maxWorld 5/10/20).
- Phase 6's `modalApplyOneS5w_outputs_tags` statement was left as `...` in the plan; landed as
  the conjunction of two directional per-mint-shape lemmas rather than a single combined form.
- Phase 7's `modalStepBranchS5w_preserves_worldInv` takes `accTargetsKnown b acc` as a THIRD
  hypothesis beyond the plan's literal two-hypothesis signature -- a documented, necessary
  deviation (not an optional embellishment): K's own `boxPos`/`diamondNeg` propagation shapes
  emit at `acc.successorsOf w`, which is unbounded by `modalMaxWorld` without it. The
  `accTargetsKnown` preservation instantiation itself was free (a corollary of the already-landed
  generic `modalStepBranch_preserves_accTargetsKnown_gen`).
- `modalMaxWorld_lt_worldBound_of_S5w` needed only `hW : S5wWorldInv`, not `hT : S5wTagInv`,
  narrower than the plan's stated `(hT) (hW)` signature -- the chain
  `modalMaxWorld b ≤ (usedTags φ₀ b).card ≤ (mintTags φ₀).card ≤ modalOps φ₀ < modalWorldBound φ₀`
  never touches `S5wTagInv` directly.
- Phase 9's "Files to modify" list (`GenericDriver.lean`, `S5Simplification.lean`, plus 3-line
  T/B adapters) omitted `CompletenessLoop.lean`, but the field rename there forced six
  destructuring-site updates (`spec.boxNegWitness`/`spec.diaPosWitness` → `spec.boxNegWitness'`/
  `spec.diaPosWitness'`, each gaining an extra existential witness-world binder). This is
  mechanical fallout of the rename, not a design change: `CompletenessLoop.lean`'s seven
  `RuleApplicationSpec`-typed signatures are all left unchanged (still the full spec, not Core),
  since `modalStepGen_preserves_invariant` (and transitively `modalExpandBranchesGen_hintikka`)
  calls `modalStepBranchGen_potential_step`, which needs `rankStep`/`outDegStep`/
  `knownWorldsStep`. Weakening those five (of seven) `CompletenessLoop.lean` signatures whose
  bodies don't touch the three dropped fields to `RuleApplicationSpecCore` is deferred to
  Phase 12 (the parametric Hintikka lift), per the plan's own phase split.
- Phase 9's `outputsSubsetUniverse`/`persistentFresh`/`branchingLength`/`localShapeInvariance`/
  `boxPosNotExpanding`/`diaNegNotExpanding` fields for `modalApplyOneS5w` needed substantially
  more new proof content than the plan's task list detailed (which fully specified only
  `diaPosWitness'`/`boxNegWitness'`) -- roughly 440 new lines total, not a handful of free
  bridges. Each field required a genuine case split on whether `sf` is one of the two S5w
  witness-reuse shapes, one of S5's own two universal-propagation shapes, or neither.
- Phase 10's `AuxStepPreserved` takes `accFreshInv b acc` and `accTargetsKnown b acc` as
  additional ambient hypotheses beyond `Aux b acc` itself (not part of the plan's literal
  two-hypothesis `Aux`/`auxStep`/`auxBound` sketch), matching Phase 7's documented
  `accTargetsKnown`-as-third-hypothesis deviation for `modalStepBranchS5w_preserves_worldInv`.
  Without this, S5w's `AuxStepPreserved` instance could not be discharged from the already-landed
  Phase 7 lemma.
- `ModalLoopAuxS5w` ignores its `Accessibility` argument entirely (S5w's invariant depends only
  on the branch, not `acc`), which `lake lint`'s `unusedArguments` linter flagged as an error
  (not merely a compiler warning); fixed with `@[nolint unusedArguments]`, matching existing
  precedent elsewhere in the library (`CountermodelExtraction.lean`, `SignedFormula.lean`).
- Went beyond the plan's literal verification bar ("both `Aux` instantiations elaborate") by
  proving full theorems (`ModalLoopAuxK_bounds`, `ModalLoopAuxS5w_bounds`,
  `ModalLoopAuxS5w_stepPreserved`, `ModalLoopInvGen_iff_hintikka_auxK`) rather than stopping at
  type-checking, since every one of these was a direct, low-risk corollary of already-landed
  Phase 6-9 machinery.

## Impacts

- Phases 11-14 (the rest of the S5 chain: step preservation, the parametric Hintikka lift +
  K/T/B regression gate, soundness) and Phases 15-23 (the Euclidean 5/KB5 route) remain
  unattempted. Phase 10's completion clears the way to Phase 11; no fallback pivot is needed.
- No existing declaration was renamed, removed, or had its statement weakened by Phase 10;
  `ModalLoopInvGen`, `ModalLoopInv`, and every prior declaration in `CompletenessLoop.lean` are
  byte-identical. Phase 9's `RuleApplicationSpec.boxNegWitness`/`.diaPosWitness` →
  `.boxNegWitness'`/`.diaPosWitness'` rename (the one exception across Phases 0-10) remains as
  documented in that phase's own note.

## Follow-ups

- Next dispatch: Phase 11 (step preservation) -- port `modalStepGen_preserves_invariant`
  (`CompletenessLoop.lean`) to `ModalLoopInvHintikka`, minus its two `potential_step` lines,
  threading `AuxStepPreserved`/`AuxBounds` as explicit hypotheses. K's own `AuxStepPreserved`
  instance (not proved in Phase 10) is needed here, reusing `modalStepBranchGen_potential_step`
  directly rather than re-deriving it.
- Phase 12 should verify (by reading, not assuming) which of `CompletenessLoop.lean`'s seven
  `RuleApplicationSpec`-typed signatures can weaken to `RuleApplicationSpecCore`; Phase 9 confirms
  this for the five whose bodies it touched (`modalLoopGen_bClosure`, `_eBoxOnlyNeg`,
  `_eDiamondOnlyPos`, `_eBoxNegWitness`, `_eDiamondPosWitness`) but did not change their
  signatures, since doing so wasn't required for Phase 9's own goal.
- Future artifacts citing `modalApplyOneS5_snd_eq`'s consumer sites should use the corrected
  line numbers from the Phase 8 completion note, not the stale ones in earlier reports.

## References

- `specs/515_s5_universal_rule_termination_unblock_504/plans/05_s5-termination-machinery.md`
- `specs/515_s5_universal_rule_termination_unblock_504/.orchestrator-handoff.json`
- `specs/515_s5_universal_rule_termination_unblock_504/reports/03_s5-infrastructure-deep-research.md`
- `specs/515_s5_universal_rule_termination_unblock_504/probes/five-s5-separation.lean`
- `specs/515_s5_universal_rule_termination_unblock_504/probes/phase8-r1-reuse-soundness.lean`
