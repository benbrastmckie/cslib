# Summary 14: Phase 20 landed -- `extractModelFive` + Euclidean truth lemma

**Task**: 515 - s5_universal_rule_termination_unblock_504
**Plan**: plans/07_s5-termination-machinery.md (v6)
**Phase**: 20 (`extractModelFive` + the Euclidean truth lemma) -- now `[COMPLETED]`
**Commit**: `deda5136` (`task 515 phase 20: land extractModelFive + Euclidean truth lemma`)

## What landed this dispatch

Resumed from `handoffs/13_phase19b-completed-all-phase19-closed.md` (all of Phase 19, i.e. 19a +
19b, fully `[COMPLETED]`; neither the mint-arm guard, the termination-bound re-derivation, nor
`modalTableauFive_sound` re-touched). This dispatch landed Phase 20 -- the independent
completeness/countermodel track that depends only on Phases 17/18 -- in full, in one green
sub-milestone plus the main capstone commit.

### `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (additive)

Four membership-introduction lemmas, the converse direction to the already-landed
`modalFiveBoxAll_mem`/`modalFiveDiaNegAll_mem`, split by the root/non-root trigger dichotomy
`modalFiveBoxAll`/`modalFiveDiaNegAll`'s own definitions require:

- `modalFiveBoxAll_mem_of_ne_root` / `modalFiveBoxAll_mem_of_root`
- `modalFiveDiaNegAll_mem_of_ne_root` / `modalFiveDiaNegAll_mem_of_root`

These mirror `modalS5BoxAll_mem_of`/`modalS5DiaNegAll_mem_of` (`S5Simplification.lean`), but a
single lemma there becomes two here (root vs. non-root trigger), since `modalFiveBoxAll`'s root
arm additionally requires a genuine recorded edge (`acc.hasEdge 0 v`) rather than bare
known-world membership.

### `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (additive, new section)

- `extractModelFive` -- the model extractor instantiating Strategy B's `extractModelWith` with
  `Relation.EuclGen` (the right-Euclidean least-closure operator) rather than `Relation.EqvGen`,
  the one-word substitution the whole Euclidean route was built for.
- `extractModelFive_r`, `extractModelFive_rightEuclidean`, `extractModelFive_hasEdge_imp_r` --
  mirror the corresponding `extractModelS5_*` lemmas exactly.
- `accTargetsNeRoot` (new predicate), `euclGen_ne_root_of_hasEdge_ne_root`,
  `euclGen_root_imp_hasEdge`, `euclGen_mem_modalKnownWorlds_iff` -- see "Key design finding"
  below.
- `modalApplyOneFive_eq_of_prop_shape` -- a small composed bridge (chains
  `modalApplyOneFive_eq_of_not_mint_shape` with `modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg`)
  needed because Five's propositional-shape agreement with K's `modalApplyOne` is a two-step
  fact, unlike S5's one-step `modalApplyOneS5_eq_of_not_boxPos_diaNeg` (S5 has no separate
  witness-reuse staging).
- `hintikkaFive_box_pos`, `hintikkaFive_diamond_neg` -- the Five analogues of
  `hintikkaS5_box_pos`/`hintikkaS5_diamond_neg`, parametrized by the root/non-root dichotomy.
- `modalTruthLemmaFive` -- the main truth lemma, structurally mirroring `modalTruthLemmaS5`
  (propositional cases, mint-direction box-negative/diamond-positive cases) with the
  universal-propagation direction (box-positive/diamond-negative) newly split on whether the
  trigger world is the root.
- `modalOpenBranchFive_countermodel` -- mirrors `modalOpenBranchS5_countermodel` exactly, taking
  `hSrc`/`hTgt`/`hRoot`/`hH`/`hF` as abstract hypotheses (not itself invoking any top-loop
  propagation lemma -- that discharge is Phase 21's job at the real open-branch call site,
  exactly as `modalTableauS5_complete` already does for `hSrc`/`hTgt`).

## Key design finding: `accTargetsNeRoot` is a genuinely new, necessary hypothesis

The plan's Phase 20 note anticipated "the root case is the only genuinely new one" without
naming a specific extra ingredient. Working the box-positive direction through revealed one is
needed: `modalFiveBoxAll`/`modalFiveDiaNegAll` structurally never place propagated content at
world `0` (a rooted, non-necessarily-reflexive Euclidean frame need not relate the root to
itself). This means the truth lemma's universal-propagation direction is **false in general**
without an extra hypothesis ruling out edges that target the root: a raw edge `acc.hasEdge w 0`
witnesses a model relation `r w 0` (via `Relation.EuclGen.base`) that the Hintikka closure can
never certify a matching branch formula `T(ψ)@0` for (concrete counterexample: `b = [T(□p)@1,
F(p)@0, T(p)@1]`, `acc = {1 → 0}` is Hintikka-closed under `modalApplyOneFive` yet
semantically falsifies `T(□p)@1 → Satisfies M 1 (□p)` against `extractModelFive`, since `p` is
false at world `0` but the box-positive rule never propagates to root to catch this).

The fix: a new abstract hypothesis `accTargetsNeRoot acc : ∀ w w', acc.hasEdge w w' → w' ≠ 0`,
threaded through `modalTruthLemmaFive`/`modalOpenBranchFive_countermodel` alongside the existing
`accSourcesKnown`/`accTargetsKnown`. Two small structural lemmas discharge the two places this
is needed:

- `euclGen_ne_root_of_hasEdge_ne_root`: the right-Euclidean closure's target is always non-root,
  given the raw hypothesis (one-line induction: the `eucl` constructor's conclusion inherits its
  target directly from the second premise, never touching the first).
- `euclGen_root_imp_hasEdge`: `EuclGen r 0 w'` can only arise via the `base` constructor (never
  `eucl`, since that would require a sub-derivation reaching target `0`, ruled out by the
  previous lemma) -- exactly the fact `modalFiveBoxAll`'s root-trigger arm (Route (1)) is built
  to match.

Like `hSrc`/`hTgt`, Phase 20 takes `accTargetsNeRoot` as an abstract hypothesis rather than
re-deriving its top-loop preservation across a real tableau run -- that discharge (true of every
real run: mint targets are fresh hence positive; Phase 19b's
`modalApplyOneFive_agree_or_reuse_ne_root` shows reuse targets are non-root too) is explicitly
deferred to Phase 21's `modalTableauFive_complete`, alongside the existing `hSrc`/`hTgt`
discharge it already needs.

## Verification

- Scoped builds: `Cslib.Logics.Modal.Tableau.FiveSimplification` and
  `Cslib.Logics.Modal.Tableau.FrameCompleteness`, both green, zero new warnings.
- Full `lake build`: 3240/3240 jobs, green.
- `lake exe checkInitImports`: exit 0.
- `lake lint` (full repo): one pre-existing baseline error (`PrimeExclusion.lean`, unrelated);
  zero hits in either touched file.
- `lake exe lint-style`: clean, no output.
- `lake shake --add-public --keep-implied --keep-prefix`: no import-removal/addition suggestion
  for either touched file (only pre-existing baseline suggestions in unrelated Propositional/
  Temporal files).
- `lake exe mk_all --module`: "No update necessary".
- `lake test`: exit 0, full `CslibTests/` suite green.
- `sorry_count` in touched files: 0 (repo-wide count of 131 is entirely pre-existing baseline in
  `Intuitionistic`/`Minimal` Completeness/Scheme files, unrelated to task 515).
- `vacuous_count`/`axiom_count`: the one repo-wide vacuous hit (`Computability/URM/Basic.lean`)
  and 28 `axiom` declarations are all pre-existing baseline, none in either touched file.
- Axioms on every new declaration confirmed via `lake env lean` + `#print axioms` (not
  `lean_verify` alone): `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]` only
  -- no `sorryAx`, no new custom axiom, on all 16 new/modified declarations checked.

## Plan Deviations

- Phase 20's task checklist items are all marked `[x]`, with two inline `(deviation: altered
  -- ...)` annotations documenting the `accTargetsNeRoot` addition and
  `modalOpenBranchFive_countermodel`'s abstract-hypothesis shape (see plan file for full text).
  Both are additive refinements consistent with the phase note's own framing ("the root case is
  the only genuinely new one"), not scope changes.
- The plan file's stray, pre-existing, uncommitted Phase 22 marker (`[NOT STARTED]` ->
  `[IN PROGRESS]`, present in the working tree before this dispatch started, unrelated to any
  work performed here) was deliberately left **unstaged** this time (via `git add -p`,
  hunk-scoped), rather than carried into this commit as happened with the prior dispatch's
  Phase 21 marker. It remains in the working tree for whichever session is responsible for it.

## Files touched this dispatch

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`
  (Phase 20 marker + checklist only, hunk-scoped)
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/summaries/14_phase20-euclidean-truth-lemma-landed.md`
  (this file)
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/handoffs/14_phase20-completed-ready-for-21.md`
  (handoff)
