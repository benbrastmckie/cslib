# Implementation Summary: Task #504 — S5/KB5 Euclidean decidability via generic tableau

- **Task**: 504
- **Plan**: `plans/01_s5-kb5-euclidean-decidability.md`
- **Status**: [PARTIAL] — 2/7 phases fully completed, 1 phase partially delivered, 4 phases
  transitively [BLOCKED] by a genuine, mechanized mathematical obstruction in Phase 2.

## What Was Delivered

- **Phase 1 [COMPLETED]**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean` (new file) defines
  the universal "propagate box to ALL branch worlds" S5 rule (`modalApplyOneS5`,
  `modalS5BoxAll`/`modalS5DiaNegAll`), the agreement lemma
  (`modalApplyOneS5_eq_of_not_boxPos_diaNeg`), and the generic-driver instantiation
  (`modalStepBranchS5`/`modalExpandBranchesS5`/`modalTableauS5` + `_eq` unfold lemmas).
- **Phase 2 [BLOCKED — genuine, mechanized]**: `modalApplyOneS5_spec : RuleApplicationSpec
  modalApplyOneS5` **cannot be constructed**. The `rankStep` field is proven **mathematically
  false** for the universal rule via a fully mechanized, sorry-free counterexample landed
  permanently in `S5Simplification.lean` (`modalApplyOneS5_rankStep_not_dischargeable`, section
  "Phase 2 Obstruction"): a concrete branch/accessibility/rank instantiation where the rule
  emits a formula whose depth exceeds the only rank value any valid `rank'` witness could take.
  Root cause: `rankStep`'s K-style FMP rank-potential argument requires the target world's rank
  to be provably related to the trigger world's rank via a recorded edge (`hedge`) — true for
  T's self-propagation and B's backward-edge propagation, but false for S5's *unrestricted*
  propagation to every known branch world (which can include worlds in unrelated subtrees with
  no edge-relation to the trigger). This is the same underlying class of obstruction already
  documented for S4's transitive 4-rule in `GenericDriver.lean`'s module docstring.
- **Phase 3 [COMPLETED]**: `extractModelS5` (in `FrameCompleteness.lean`) extracts the S5
  countermodel via `Relation.EqvGen` (equivalence closure of recorded edges), independent of the
  blocked rule. `extractModelS5_r`, `instIsEquivEqvGen` (built by hand — no unconditional
  `IsEquiv`-from-`EqvGen` instance exists in Mathlib), `extractModelS5_equiv`,
  `extractModelS5_hasEdge_imp_r`, `extractModelS5_refl` all land sorry/axiom-free.
- **Phase 7 [PARTIAL]**: `extractModelS5_rightEuclidean : Relation.RightEuclidean (extractModelS5
  b acc).r` is delivered (pulled forward from Phase 7 into Phase 3's scope since it depends only
  on `extractModelS5_equiv`), built directly from `IsEquiv`'s `symm`/`trans` projections (the
  plan's originally-cited route via `Relation.symm_rightEuclidean_iff_trans` needs an unavailable
  `[Std.Symm r]` instance for `Relation.EqvGen`). An in-file scope note (in both
  `S5Simplification.lean` and `FrameCompleteness.lean`) documents that genuine pure-K5/pure-5
  completeness (Euclidean without full equivalence) is out of scope — no Mathlib closure operator
  exists for it — and that `fiveValid`/`kb5Valid` *decidability/completeness* via the S5 route is
  itself transitively blocked by Phase 2 (they need `modalTableauS5_sound`/`_complete` as their
  proof engine, which need `modalApplyOneS5_spec`).
- **Phases 4, 5, 6 [BLOCKED — transitively]**: Each phase's tasks consume
  `modalApplyOneS5_spec` (directly, or via generic lemmas parametrized over a `spec` witness),
  which does not exist. No phase task was attempted past confirming the prerequisite type cannot
  be constructed; no `sorry`/`axiom`/vacuous workaround was introduced anywhere.

## Plan Deviations

- Phase 7's `extractModelS5_rightEuclidean` was pulled forward into Phase 3 (both landed in the
  same session/commit scope), since it has no dependency on the blocked rule.
- The plan's suggested `Relation.symm_rightEuclidean_iff_trans` route for `RightEuclidean` was
  replaced with a direct construction from `IsEquiv`'s `symm`/`trans` fields (the cited route
  needs an unavailable `[Std.Symm r]` instance for the generic `Relation.EqvGen` relation).
- `Relation.EqvGen.instIsEquiv` (cited in the plan) does not exist in Mathlib; `instIsEquivEqvGen`
  was built by hand from `EqvGen`'s `.refl`/`.symm`/`.trans` constructors instead.
- `S5Simplification.lean`'s import block was collapsed to a single `public import
  Cslib.Logics.Modal.Tableau.FmpMeasure` (rather than mirroring `BDriver.lean`'s explicit
  `GenericDriver`/`FrameRules`/`Completeness`/`CompletenessLoop` import list) following a
  `lake shake` minimization finding; `FrameCompleteness.lean`'s `public import
  Cslib.Foundations.Relation.Euclidean` was removed for the same reason (the file only needs the
  `RightEuclidean` class from `Defs.lean`, already transitively available, not any theorem from
  `Euclidean.lean` specifically, once the direct-construction route above was adopted).
- Phases 4/5/6's rule-independent standalone pieces (e.g. `s5FC`'s bare definition in Phase 5)
  were deliberately not landed in isolation, since they have no independent use without the
  blocked downstream results.

## Verification

- `lake build` (full project): green, 3236/3236 jobs.
- `lake exe checkInitImports`: clean (both files import `Cslib.Init` transitively via
  `FmpMeasure`/the existing chain).
- `lake lint`: 0 errors in `S5Simplification.lean`/`FrameCompleteness.lean` (1 pre-existing,
  unrelated `unusedArguments` error in `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`
  predates this task).
- `lake exe lint-style`: clean.
- `lake exe mk_all --module`: `Cslib.lean` already registers `S5Simplification.lean`.
- `lake shake --add-public --keep-implied --keep-prefix`: clean for both task-touched files
  (remaining output is pre-existing `Cslib.Init`-removal noise on sibling files
  `Branch.lean`/`Rules.lean`/`GenericDriver.lean`/`TDriver.lean`/`BDriver.lean`, matching an
  established, already-accepted pattern in this file family — not actioned, per
  `checkInitImports`'s stronger mandate).
- `lake test`: green (`CslibTests` suite, exit 0).
- `grep sorry`: 0 in either file (only prose mentions of "sorry-free"/"no sorry").
- `grep '^axiom '`: 0 new axioms in either file.

## Recommended Follow-Up

Per the plan's escalation guidance, recommend spawning a dedicated
`s5-universal-rule-termination` follow-up task to investigate either (a) a restricted S5 rule
design preserving rank-compatibility while still achieving full equivalence closure, or (b) an
S5-specific termination argument bypassing `RuleApplicationSpec`'s rank-potential machinery
entirely (comparable in scope to S4/task 511's loop-checking problem). A separate
`pure-k5-euclidean-closure` follow-up remains recommended for genuine pure-K5/pure-5 (out of
scope here, per the parent plan's non-goals).
