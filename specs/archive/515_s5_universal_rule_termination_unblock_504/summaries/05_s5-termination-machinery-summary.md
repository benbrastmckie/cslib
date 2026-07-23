# Summary: S5 Termination Machinery Plan v5, Phases 0-11

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Status**: [IN PROGRESS] (phases 0-11 of 24 complete; phase 12 onward remain)
- **Started**: 2026-07-15T00:00:00Z
- **Completed**: 2026-07-16 (this dispatch: phase 11)
- **Effort**: ~13 hours (11 phases: kill test, rule, congruence, refutation, arithmetic, generalization, invariant, counting crux, gate, spec split, rank-free Aux invariant, step preservation)
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
- **Phase 11** (`CompletenessLoop.lean`): Landed `modalStepHintikka_preserves_inv`, the
  step-preservation port of `modalStepGen_preserves_invariant` to `ModalLoopInvHintikka`/`Aux`,
  minus the two `potential_step` lines, taking `RuleApplicationSpecCore` plus
  `AuxStepPreserved`/`AuxBounds` in their place. The measure drop consumes
  `modalExpMeasure_step_lt_gen` directly against `RuleApplicationSpecCore`'s three raw fields
  (`branchingLength`/`persistentFresh`/`outputsSubsetUniverse`), bypassing the full-spec-typed
  wrapper. Five of the composed rule-dependent helpers (`modalLoopGen_bClosure`, `_eBoxOnlyNeg`,
  `_eDiamondOnlyPos`, `_eBoxNegWitness`, `_eDiamondPosWitness`) are declared against the full
  `RuleApplicationSpec` even though each proof body only ever touches a Core field; rather than
  weaken those five declarations in place (Phase 12's remit per the plan), landed purely-additive
  `_core`-suffixed twins with identical proof bodies parametrized over `RuleApplicationSpecCore`.
  Landed `modalStepHintikka_preserves_inv_S5w`, a concrete corollary instantiating the generic
  lemma at `Aux := ModalLoopAuxS5w φ0` (using the already-landed Phase 9/10 machinery),
  demonstrating the S5w half of the plan's verification bar sorry-free.

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
- **Phase 11 finding, not a defect**: the plan's verification bar asks the port to close
  sorry-free "at both `Aux` instantiations", but a *closed* `AuxStepPreserved` witness for K's
  `ModalLoopAuxK` genuinely cannot be constructed in its current form. `ModalLoopAuxK (φ0) (e) (b)
  (acc)` freezes `e` to fit `Aux`'s bare `(b → acc → Prop)` type, while `AuxStepPreserved`'s own
  step hypothesis is universally quantified over an independent, per-call `e`. A minting step
  changes `outDeg` against the step's own *current* expanded set, not against `ModalLoopAuxK`'s
  frozen `e`; a concrete counterexample (frozen `e0 := []` with any `boxNeg`/`diamondPos`-shaped
  minting step) makes the post-state `outDegEq` conjunct false. `modalStepHintikka_preserves_inv`
  itself remains fully generic and sorry-free for any `Aux` genuinely satisfying
  `AuxStepPreserved`/`AuxBounds` -- confirmed concretely for S5w via the landed
  `modalStepHintikka_preserves_inv_S5w`. Resolving K's half is architecture work for Phase 12
  (most likely threading the current `e` explicitly rather than freezing it inside `Aux`), not a
  gap in this phase's port; documented in the plan's Phase 11 section and the H9 handoff for
  Phase 12 to consume before attempting the K re-derivation regression gate.

## Impacts

- Phases 12-14 (the parametric Hintikka lift + K/T/B regression gate, soundness) and Phases
  15-23 (the Euclidean 5/KB5 route) remain unattempted. Phase 11's completion clears the way to
  Phase 12, but Phase 12 should read the Phase 11 finding above before attempting the K
  re-derivation: K's `ModalLoopAuxK` needs its `e`-freezing redesigned before it can supply a
  closed `AuxStepPreserved` witness.
- No existing declaration was renamed, removed, or had its statement weakened by Phase 11; every
  prior declaration in `CompletenessLoop.lean` (including `ModalLoopInvGen`, `ModalLoopInv`, and
  all of Phases 0-10's additions) is byte-identical. Phase 11 is purely additive: five `_core`
  helper twins, `modalStepHintikka_preserves_inv`, and `modalStepHintikka_preserves_inv_S5w`.

## Phase 12: The parametric Hintikka lift + the K/T/B REGRESSION GATE [COMPLETED]

Both halves landed in a single dispatch; the phase's authorized two-dispatch split was not needed.

**12a -- `modalExpandBranchesHintikka`** (commit `ecfa123e`, 333 lines).
The prior session crashed mid-phase, leaving 333 uncommitted, never-built lines. The first action
of this dispatch was to establish whether that draft compiled rather than assume either way: it
did, as authored (852/852, zero errors). It was kept, not rewritten. The only substantive change
was stripping three ephemeral task-number citations (`task 515 Phase 12a` in the section header,
two `task 441` inline comments copied verbatim from the port source) and the `Phase 11`/`Phase
12b` plan references from the docstring, replacing them with durable anchors per
`.claude/rules/no-task-references-in-deliverables.md`.

**12b -- the REGRESSION GATE** (commit `4e6b9a98`, net -287 lines). **PASSED.**
`modalExpandBranchesGen_hintikka` is now a 7-line corollary of the parametric lift at
`Aux := ModalLoopAuxK φ0`. Its ~290-line double induction turned out to *be* the
`Aux := ModalLoopAuxK φ0` special case of the lift, so it was deleted rather than kept in
parallel. Three pieces bridge the gap:
- `spec.toCore` -- weakens `RuleApplicationSpec` to the `RuleApplicationSpecCore` the lift takes
- `ModalLoopAuxK_stepPreserved` / `ModalLoopAuxK_bounds` -- the `Aux` obligations (landed 11.5)
- `ModalLoopInvGen_iff_hintikka_auxK` -- converts the K-facing per-index
  `∃ rank, ModalLoopInvGen …` hypothesis into the lift's rank-free `ModalLoopInvHintikka …`

**Why the gate is honest, not merely green.** A regression gate that passes because the statement
was quietly weakened proves nothing, so both invariants were checked mechanically rather than by
eye:
- The K statement is **byte-identical** to the prior revision -- verified by extracting the
  signature (decl line through `:= by`) from `git show HEAD` and from the working tree and
  `diff`ing them; the diff is empty. The two statement-shaped lines that *do* appear in the raw
  diff are from the deleted proof's inner `suffices key` block (they end in `from`), not the
  signature.
- `TDriver.lean` and `BDriver.lean` are **unmodified** (`git status --short` on both: empty) and
  both compile (`lake test` exit 0; TDriver and BDriver both built).

**KILL (R3): not triggered.** The factoring is validated against the K contract. Phase 11.5's
`Aux` re-arity is what made this pass -- the adversarial audit predicted the curried-`e` shape
would fail exactly here, and the crux was `modalStepBranch_preserves_outDegEq_gen` stating its
conclusion at the branch's own new `e` (`p.2`).

**Verification**: `lake build` (852/852), `checkInitImports`, `lint-style`, `lint` (1 error, the
known out-of-scope `PrimeExclusion.lean` baseline), `test` (exit 0), `shake` (clean for
`CompletenessLoop`; all suggestions are pre-existing, other files), `mk_all` (no update). Zero
`sorry`, zero new axioms: `lean_verify` on both `modalExpandBranchesHintikka` and
`modalExpandBranchesGen_hintikka` reports `propext`/`Classical.choice`/`Quot.sound` only, no
`sorryAx`. Repo-wide `sorry`(127)/`axiom`(28) counts are byte-identical to `HEAD` (confirmed by
stash-compare) and none are in `CompletenessLoop.lean`.

## Plan Deviations

None. Phase 12a and 12b were executed as written. The phase's authorization to split across two
dispatches was not exercised (both closed in one), which is under-consumption of budget, not a
deviation from the task sequence.

## Follow-ups

- **Phase 12 is closed and its KILL gate did not fire** (this supersedes the prior dispatch's
  standing warning about it). The Phase 11 finding it warned of -- that K's `ModalLoopAuxK` could
  not supply a closed `AuxStepPreserved` witness in its frozen-`e` form -- was resolved by Phase
  11.5's `e`-threading re-arity, exactly as that finding predicted would be necessary. Phase 14 is
  unblocked on the lift axis.
- Next dispatch: **Phase 13** (S5 soundness re-proof, `modalTableauS5_sound`) is still
  `[IN PROGRESS]` -- it is the parallel fork off Phase 8's probe and was never owned by the
  Phase 9-12 lift chain; it carries its own KILL condition (stop if the re-proof exceeds ~400
  lines). Phase 14 (S5 assembly/archival/CI) depends on both 12 and 13.
- Phase 12 should still verify (by reading, not assuming) which of `CompletenessLoop.lean`'s
  seven `RuleApplicationSpec`-typed signatures can weaken to `RuleApplicationSpecCore`; Phase 9
  confirms this for the five whose bodies it touched (`modalLoopGen_bClosure`, `_eBoxOnlyNeg`,
  `_eDiamondOnlyPos`, `_eBoxNegWitness`, `_eDiamondPosWitness`) but Phase 11 deliberately left
  their signatures unchanged, landing `_core`-suffixed twins instead (Phase 12's remit, per the
  plan's own scoping note, is the actual in-place weakening).
- Future artifacts citing declarations by line number should expect drift: Phases 8, 9, 10, and
  11 have each independently confirmed the plan's line citations are stale (files have grown
  substantially across Phases 4-11); resolve citations by name via `lean_local_search` /
  `lean_declaration_file` / grep, not by trusting the plan's line numbers.

## References

- `specs/515_s5_universal_rule_termination_unblock_504/plans/05_s5-termination-machinery.md`
- `specs/515_s5_universal_rule_termination_unblock_504/.orchestrator-handoff.json`
- `specs/515_s5_universal_rule_termination_unblock_504/reports/03_s5-infrastructure-deep-research.md`
- `specs/515_s5_universal_rule_termination_unblock_504/probes/five-s5-separation.lean`
- `specs/515_s5_universal_rule_termination_unblock_504/probes/phase8-r1-reuse-soundness.lean`
