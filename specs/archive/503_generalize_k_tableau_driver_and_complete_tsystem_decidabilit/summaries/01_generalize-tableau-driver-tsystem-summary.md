# Implementation Summary: Task #503 -- Generalize K Tableau Driver + Complete T-System Decidability

- **Task**: 503
- **Plan**: `specs/503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/plans/01_generalize-tableau-driver-tsystem.md`
- **Status**: PARTIAL (Phases 1-5 COMPLETED and committed, zero-debt; Phase 6 BLOCKED with a
  documented handoff; Phase 7 PARTIAL -- all tasks achievable independent of Phase 6 are done)

This summary supersedes the prior draft written after Phase 4, when Phase 5 was blocked on a
missing Hintikka-set-production prerequisite. Task 510
(`complete_generic_hintikka_saturation_chain`) subsequently delivered that prerequisite
(`modalExpandBranchesT_hintikka`, `TDriver.lean`), unblocking Phase 5. This session consumed it,
completed Phase 5 in full, then hit a new, distinct blocker on Phase 6's soundness-lift
prerequisite. Phase 7 (interface documentation, CI sweep, this summary) was executed for every
task not contingent on Phase 6.

## What Was Delivered (Phases 1-5, zero-debt, full CI green)

### Phase 1 -- Generic driver definitions (`Saturation.lean`)

`RuleApply Atom`, `modalStepBranchGen`, `modalExpandBranchesGen`, `modalTableauGen`: a generic
tableau driver parametrized over an abstract rule-application function matching
`modalApplyOne`'s signature. K's existing `modalStepBranch`/`modalExpandBranches`/`modalTableau`
kept byte-identical; three bridge theorems relate K to the trivial instantiation.

### Phase 2 -- Structural-hypothesis interface bundle (`GenericDriver.lean`, new file)

`RuleApplicationSpec (apply)`, initially three fields (`freshLocal`, `outputsSubsetUniverse`,
`persistentFresh`), `modalApplyOne_spec : RuleApplicationSpec modalApplyOne` (trivial witness).

### Phase 3 -- Generic FMP termination measure (delivered by task 507)

All three K termination lemmas (`modalStepBranch_potential_step`, `modalStepBranch_worldBound`,
`modalExpMeasure_step_lt`) generalized over `(apply, spec : RuleApplicationSpec apply)`.
`RuleApplicationSpec` extended from three to seven fields (`rankStep`, `outDegStep`,
`knownWorldsStep`, `branchingLength` added).

### Phase 4 -- T tableau driver instantiation + `modalApplyOneT_spec` (`TDriver.lean`, new file)

Built `modalStepBranchT`/`modalExpandBranchesT`/`modalTableauT` as the generic driver
(`Saturation.lean`) instantiated at `apply := modalApplyOneT` (`FrameRules.lean`), and proved
`modalApplyOneT_spec : RuleApplicationSpec modalApplyOneT`, discharging all seven fields.
`modalApplyOneT` agrees with `modalApplyOne` outside the two T-relevant shapes (box-positive
`T(□φ)@w`, diamond-negative `F(◇φ)@w`), so every field's "not shaped" case reduces to K's witness;
each field's "shaped" case combines that K witness with a direct argument for the appended
self-conjunct (`modalTBoxSelf`/`modalTDiaNegSelf`).

### Phase 5 -- T truth lemma and `tValid` completeness (delivered this session, `FrameCompleteness.lean`)

Task 510 delivered the missing prerequisite: `modalExpandBranchesT_hintikka` (`TDriver.lean`), a
one-line application of the newly-generic `modalExpandBranchesGen_hintikka` at
`(modalApplyOneT, modalApplyOneT_spec)`, concluding in `modalHintikkaSetGen modalApplyOneT bR aR`.
This session consumed it to close the rest of Phase 5:

- **`hintikkaT_box_pos`/`hintikkaT_diamond_neg`** (the two genuinely-new bridges): stated over
  `Relation.ReflGen acc.hasEdge w w'` (i.e. `w' = w` via `.refl`, or a raw recorded edge via
  `.single`). The `.refl` case is T's actual new content -- either the self-conjunct
  (`modalTBoxSelf`/`modalTDiaNegSelf`) is already on the branch, or `modalApplyOneT`'s merged
  persistent output forces it in. The `.single` case reduces to the same low-level
  `boxPropagation`-membership argument K's own `hintikka_box_pos`/`hintikka_diamond_neg` inline,
  since T's persistent output at these shapes is K's own list merged with a self-conjunct at a
  (possibly) different world, so K's witness list survives into T's merged forcing unchanged.
- **`modalTruthLemmaT`**: strong induction on `modalComplexity`, mirroring `modalTruthLemma`
  (K) and `modalTruthLemmaS4`. Propositional cases route through a local
  `modalApplyOneT_eq_of_not_box_diamond` specialization of `modalApplyOneT_eq_of_not_boxPos_diaNeg`
  and reuse K's `modalApplyOne_*` bridge lemmas verbatim. The box-negative/diamond-positive modal
  cases (the two *unaffected* minting shapes) reuse the **free generic projection bridges**
  `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` that task 510 delivered alongside the crux --
  these needed zero T-specific proof content. Only box-positive/diamond-negative consume the new
  `hintikkaT_*` bridges above.
- **`modalOpenBranchT_countermodel`**, **`modalTableauT_complete`** (the phase's headline
  result, `modalTableauT φ0 = .openBranch b a → ¬ tValid φ0`): assembled by combining
  `modalExpandBranchesT_hintikka` with two `CompletenessLoop.lean` lemmas
  (`modalLoopInvGen_initial`, `modalExpandBranchesGen_openBranch_initial_mem`) that were `private`
  but genuinely `apply`-agnostic (each explicitly flagged "needed by 503" in task 510's own
  docstrings) -- un-privatized as a visibility-only change, not a re-derivation.

Two small `private` local re-derivations (`modalApplyOneT_boxPos_fst'`/`_diamondNeg_fst'`) were
added inside `FrameCompleteness.lean` rather than un-privatizing `TDriver.lean`'s own versions,
since their proofs are three-line verbatim unfoldings and this avoids touching that already-
committed file at all.

## What Was Not Delivered (Phase 6)

### Phase 6 -- `Decidable (tValid φ)` -- BLOCKED (documented in the plan file)

Proving `modalTableauT φ = .closed → tValid φ` (T soundness lifted to the driver level) --the
prerequisite `tValid_decides`/`instDecidableTValid` need -- requires a `branchSatisfiableIn
FC`-generalized analog of `SoundnessStep.lean`'s `modalStepBranch_preserves_sat` (~500 lines) and
`Soundness.lean`'s `modalExpandBranches_closed_unsat` fuel-induction wrapper. No such
generalization exists for soundness anywhere in the codebase (unlike completeness, which task 510
fully generalized). Investigation found the key structural fact that the ambient Kripke model
`(W, m)` never changes throughout `modalStepBranch_preserves_sat`'s proof -- only the
world-assignment function `f` is pointwise redefined at fresh worlds for the two minting rules --
which makes the generalization *structurally* low-risk but still a ~500-line undertaking (plus
new box-positive/diamond-negative handling reusing the already-committed
`modalTBoxSelf_sound`/`modalTDiaNegSelf_sound`), comparable in scope to task 510's own
completeness generalization. See the plan file's Phase 6 section for the full documented blocker
(what was tried, why it's stuck, the four-part follow-up scope, and an explicit warning that
tasks 504/505 will hit this same soundness-generalization gap when they reach their own
decidability results).

### Phase 7 -- Interface documentation, downstream contract, final CI -- PARTIAL

All tasks not contingent on Phase 6 were completed:
- Added a new "Completeness Is Generic; Soundness Is Not Yet" section to `GenericDriver.lean`'s
  module docstring, documenting that task 510's completeness generalization is fully consumed
  (this session, Phase 5) while no soundness-side generalization exists yet, and warning 504/505
  they will need their own soundness-lift phase.
- Ran the full CSLib CI pipeline (see Verification below) -- green.
- Ran a final `lean_verify` sweep on all decls that exist (see below); `tValid_decides`/
  `instDecidableTValid` do not exist since Phase 6 is blocked.
- Wrote this summary.

Marked `[PARTIAL]` rather than `[COMPLETED]` solely because Phase 6 is blocked and two decls the
phase's own checklist named consequently do not exist.

## Plan Deviations

1. **Phase 5**: No separate `modalHintikkaSetT` predicate was defined; the already-generic
   `modalHintikkaSetGen modalApplyOneT` (task 510) has exactly the right shape.
2. **Phase 5**: The genuinely-new reflexive-self-edge reasoning applies to **both**
   box-positive and diamond-negative (not box-positive alone, as the plan's original scoping
   anticipated) -- these are exactly the two shapes `modalApplyOneT` self-propagates on.
   Box-negative/diamond-positive (unaffected minting shapes) reduce to task 510's free generic
   projection bridges instead of needing `modalApplyOneT_eq_of_not_boxPos_diaNeg` directly.
3. **Phase 5**: Two `CompletenessLoop.lean` lemmas were un-privatized
   (`modalLoopInvGen_initial`, `modalExpandBranchesGen_openBranch_initial_mem`) rather than
   re-derived, since both were already proved fully `apply`-agnostic by task 510 and explicitly
   flagged as "needed by 503" in that task's own docstrings.
4. **Phase 6**: Marked `[BLOCKED]` with a documented four-part follow-up plan, per the escalation
   protocol, rather than attempted with `sorry`. Phases 1-5 preserved green.
5. **Phase 7**: Marked `[PARTIAL]`; the final-sweep task's named decl list was adjusted to the
   decls that actually exist (Phase 6's absence means `tValid_decides`/`instDecidableTValid`
   do not exist to verify).

## Verification

Full CSLib CI run at the end of this session (after Phase 5, re-confirmed after Phase 7's
docstring addition):
- `lake build` (full project, 3233 jobs) -- green.
- `lake exe checkInitImports` -- clean.
- `lake lint` -- zero new warnings on touched files (`FrameCompleteness.lean`,
  `CompletenessLoop.lean`, `GenericDriver.lean`); pre-existing unrelated warnings elsewhere in the
  repo untouched.
- `lake exe lint-style` -- clean.
- `lake test` -- exit 0, full `CslibTests/` suite green.
- `lake exe mk_all --module` -- "No update necessary" (no new files added this session).
- `lake shake --add-public --keep-implied --keep-prefix` -- zero new suggestions on touched
  files (pre-existing, unrelated suggestions on other files across the repo untouched).
- `grep -rn "\bsorry\b" Cslib/Logics/Modal/Tableau/FrameCompleteness.lean
  Cslib/Logics/Modal/Tableau/CompletenessLoop.lean Cslib/Logics/Modal/Tableau/GenericDriver.lean` --
  zero sorry. `grep -n "^axiom "` on the same files -- zero axiom.
- `lean_verify` sweep (standard `propext`/`Classical.choice`/`Quot.sound` trio only, on every
  decl checked): `modalTableauGen`, `RuleApplicationSpec`, `modalApplyOne_spec`,
  `modalApplyOneT_spec`, `modalTruthLemmaT`, `hintikkaT_box_pos`, `modalTableauT_complete`.
- Zero-regression gate: K's public theorems (`modalTableau_decides`/`instDecidableKValid`)
  unchanged in statement, still green (no K-touching files modified this session).

## Files Changed (This Session, Phases 5 and 7)

- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` -- new "T Modal Truth Lemma" section
  (~340 lines): local shape-lemma re-derivations, `hintikkaT_box_pos`/`hintikkaT_diamond_neg`,
  `modalTruthLemmaT`, `modalOpenBranchT_countermodel`, `modalTableauT_complete`. Added
  `public import Cslib.Logics.Modal.Tableau.TDriver`.
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` -- two lemmas un-privatized
  (`modalExpandBranchesGen_openBranch_initial_mem`, `modalLoopInvGen_initial`), docstrings
  updated to note the visibility change; no proof content altered.
- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` -- module docstring gained a new
  "Completeness Is Generic; Soundness Is Not Yet" section (Phase 7 downstream-contract update).
- This plan file and summary.

## Recommendation

Spawn a dedicated follow-up task scoped specifically to Phase 6's blocker: a
`branchSatisfiableIn`-generalized per-step soundness lemma
(`modalStepBranchT_preserves_satIn`/generic `modalStepBranchGen_preserves_satIn (FC)`), a
fuel-induction wrapper mirroring `modalExpandBranches_closed_unsat` instantiated at
`modalApplyOneT`/`reflFC`, the top-level `modalTableauT_sound`, and finally `tValid_decides`/
`instDecidableTValid` (fully scoped, tractable one-liners once soundness exists -- see the plan
file's Phase 6 section for the precise scope). Budget at least 3-5 hours, mirroring task 510's
own scope for the structurally-analogous completeness-side generalization. This follow-up task
should also flag itself as relevant groundwork for tasks 504 (S5) and 505 (B), which will need
the same soundness-lift machinery for their own decidability results.
