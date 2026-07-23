# Implementation Summary: S5 Universal-Rule Termination Machinery

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Plan**: `specs/515_s5_universal_rule_termination_unblock_504/plans/01_s5-termination-machinery.md`
- **Status**: [PARTIAL] -- P1/P2 COMPLETED and CI-green; P3/P5 BLOCKED with documented open
  gaps; P4/P6/P7 transitively blocked (not independently attempted)
- **Session**: sess_1784100442_6694d0

## What Landed (sorry-free, CI-green, committed)

### Phase 1 -- Frame surface + S5 world bound + universe (`FrameSoundness.lean`, `S5Simplification.lean`)

- `s5FC`, `s5Valid`, `fiveFC`, `fiveValid`, `kb5FC`, `kb5Valid` (`FrameSoundness.lean`),
  mirroring `s4FC`/`symmFC`. Note: the plan's phrase `fiveValid := frameValid (Cube.Five)` is
  imprecise -- `Cube.Five`/`Cube.KB5` are `Set (Proposition Atom)` logic objects, not
  `FrameCondition` values, so new `fiveFC`/`kb5FC` predicates were authored matching every other
  `*FC`/`*Valid` pair's shape in the file.
- `modalWorldBoundS5`, `modalUniverseS5`, `modalUniverseS5_length_le` (`S5Simplification.lean`),
  a verbatim mirror of `modalWorldBoundS4`/`modalUniverseS4`/`modalUniverseS4_length_le`
  (`LoopChecking.lean:229/235/245`).

### Phase 2 -- Guard + guarded rule (`S5Simplification.lean`)

- `successorBirthContentS5`/`blockingWorldS5` (+3 guard lemmas), reusing
  `successorBirthContent` from `LoopChecking.lean` verbatim (rule-independent).
- `modalApplyOneS5g` (the guarded rule, routing K's two minting shapes `F(□φ)@w`/`T(◇φ)@w`
  through the guard, leaving S5's universal arms `T(□φ)@w`/`F(◇φ)@w` unchanged), plus 6
  agreement lemmas (`modalApplyOneS5g_boxNeg_blocked_eq`/`_boxNeg_unblocked_eq`/
  `_diaPos_blocked_eq`/`_diaPos_unblocked_eq`/`_eq_of_not_boxNeg_diaPos`/
  `_eq_of_not_minting_not_universal`).
- Added `public import Cslib.Logics.Modal.Tableau.LoopChecking` to `S5Simplification.lean`
  (read-only reuse; no edit to `LoopChecking.lean`, zero regression to S4/K/T/B).

### Phase 3 (partial) -- `S5LoopInv` scaffolding (`S5Simplification.lean`)

- `S5LoopInv` structure (the plan's exact four fields: `keysTotal`/`keyLowerBd`/
  `keysDistinct`/`keysInUniverse`).
- `modalStepBranchS5gKeyed` (key-threaded guarded step, mirroring `modalStepBranchS4Keyed`).
- Three local re-derivations of `FmpMeasure.lean`'s `private` `modalKnownWorlds` lemmas
  (`modalKnownWorlds_fold_spec_S5`/`mem_modalKnownWorlds_S5`/`modalKnownWorlds_mono_append_S5`),
  mirroring `BDriver.lean`'s established `_B`-suffixed re-derivation pattern.

All of the above compiles, is sorry-free, introduces zero new axioms, and passed the full CI
pipeline (`lake build` 3236/3236, `lake exe checkInitImports`, `lake exe lint-style`, `lake
lint` -- only the pre-existing unrelated `PrimeExclusion.lean` `unusedArguments` error, `lake
shake --add-public --keep-implied --keep-prefix` -- no import-diff for the touched files, `lake
test` 9227/9227 -- exit 0).

## What Is Blocked, and Why (exact, not hand-waved)

### Phase 3 -- `S5LoopInv` preservation lemmas [BLOCKED]

Two distinct, concrete obstructions, both grounded in reading the actual dependency chain:

1. **Infrastructure gap.** The only public lemma letting a non-`RuleApplicationSpec` step
   reason "which labels can newly appear on the branch",
   `modalApplyOne_knownWorlds_step` (`FmpMeasure.lean:2042`), requires `accTargetsKnown b acc`
   as a standing hypothesis. `keysInUniverse` additionally needs a subformula-closure fact
   (`φ ∈ modalSubfmls φ₀`) to place a newly-inserted birth-key pair inside `signedSubfmls φ₀`.
   Neither is present in the plan's literal four-field `S5LoopInv` -- exactly why `S4LoopInv`
   (`LoopChecking.lean:1127`) carries six *additional* generic fields
   (`bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`/`outDegEq`) the plan's Phase 3 task
   list did not ask for. S4 needed them too; it just never got far enough to expose the need
   (blueprint F2: `LoopChecking.lean` ends at the `S4LoopInv` *structure*).
2. **Design-level gap (`keysDistinct`), the deeper issue.** `blockingWorldS5_none_fresh`
   (Phase 2) compares the prospective birth content against every known world's *current*
   `relevantSetFinset`. But `S5LoopInv.keyLowerBd` only records that a *stored* key is a
   **lower bound** (not equal) to its world's current relevant set -- by design, to survive
   monotonic branch growth. A newly-minted key could therefore coincide with an older world's
   frozen, historical key even though it differs from that world's now-larger current relevant
   set. Nothing in the four-field invariant (or the guard, which only ever compares against
   *current* relevant sets) rules this out. This is an open **design** question -- the guard
   would need to compare the prospective birth content against every *stored key* (not every
   world's current relevant set) for `blockingWorldS5_none_fresh` to directly discharge
   `keysDistinct`'s new-vs-old case. S4 never encountered this either, for the identical reason.

**To unblock**: (a) decide whether to extend `S5LoopInv` to the full ten-field shape (mirroring
`S4LoopInv`, absorbing its own preservation obligations) or thread the missing hypotheses
per-lemma; (b) resolve the `keysDistinct` design gap, most plausibly by redesigning
`blockingWorldS5` to compare against the threaded `keys` list directly rather than
`relevantSetFinset`'s live value -- a change to Phase 2's already-committed guard, needing
re-verification against its already-landed agreement lemmas.

### Phase 5 -- Soundness `modalTableauS5_sound` [BLOCKED]

Clarified the plan text: soundness targets the already-landed **unguarded**
`modalApplyOneS5`/`modalTableauS5` (task 504), matching the Dependency Analysis table (Phase 5
depends on Phase 1 only) and F5's blueprint framing, not `modalApplyOneS5g`.
`(modalApplyOneS5 sf b acc).snd = (modalApplyOne sf b acc).snd` holds unconditionally (every
match arm returns K's `kAcc`), so the `freshLocal`-style dichotomy is genuinely easy via
`modalApplyOne_fresh_local`.

**BLOCKER**: the existing generic soundness bridge `modalExpandBranchesGen_closed_unsatIn`
(`FrameSoundness.lean:728`) threads only `accFreshInv` and hands per-shape `hBoxPos`/`hDiaNeg`
hypotheses only *direct-edge* relatedness (`hacc : acc.hasEdge w w' → m.r (f w) (f w')`) at each
single step -- no reachability-closure fact is available. S5's universal arms
(`modalS5BoxAll`/`modalS5DiaNegAll`) propagate to **every** known world, not just direct-edge
successors of the trigger, so `RuleResultSat` needs `m.r (f lbl) (f w')` for a `w'` that may be
many mint-tree edges away -- direct-edge `hacc` is insufficient (confirmed by inspecting T's own
`modalApplyOne_boxPos_sound`/`modalApplyOne_diaNeg_sound`, `SoundnessStep.lean:446/490`, which
only ever use `hacc` at the trigger's own direct edges, matching T's self-propagation and B's
predecessor-propagation but not S5's whole-known-world propagation). This is sharper than the
plan's "genuinely new content" framing suggested: it requires a **new top-level fuel-induction
bridge** threading a "every known world is `acc`-reachable from world 0" invariant alongside
`accFreshInv`, not merely two new per-shape lemmas plugged into the existing bridge.

**What was established (not committed -- no Lean file changes for this phase, to keep no
partial/uncertain code in the tree)**: confirmed the `.snd` agreement fact; traced
`modalExpandBranchesGen_closed_unsatIn` and its 300+-line single-step callee
`modalStepBranchGen_preserves_satIn` (the "K monolith") and confirmed neither threads
reachability; sketched (on paper, not in Lean) a *scoped* single-step reachability-preservation
argument specific to `modalApplyOneS5` (reusing the already-landed `modalS5BoxAll_mem`/
`modalS5DiaNegAll_mem` for the non-mint case and `modalApplyOne_fresh_local`'s dichotomy for the
mint case) that looks tractable on its own, but assembling the full replacement top-level
induction (combining it with `modalStepBranchGen_preserves_satIn` as a black box) was not
completed within budget.

**To unblock**: author `modalExpandBranchesGen_closed_unsatIn_reachable` (or an S5-specialized
variant) threading `∀ w ∈ modalKnownWorlds b, Relation.ReflTransGen (acc.hasEdge) 0 w` alongside
`accFreshInv`; then re-derive `hBoxPos`/`hDiaNeg` for S5's universal arms via the equivalence
projections (`Std.Refl`/`Relation.RightEuclidean` from `s5FC`) applied to the reachability
witness.

### Phase 4, 6, 7 [BLOCKED, transitively]

Not independently attempted. P4's pigeonhole consumes `S5LoopInv.keysDistinct`/
`keysInUniverse` (both open in P3). P6 depends on P3 and P4. P7 depends on P6. Strategy 2 (the
pre-authorized semantic bounded-model FMP fallback for P6's decidability capstone) was not
attempted -- it was not reached given the upstream blocks and remaining budget, and remains a
sound next-step recommendation for a follow-up task, independent of P3's open design question.

## Plan Deviations

- **Phase 5 target clarified**: proved (attempted) against the unguarded `modalApplyOneS5`/
  `modalTableauS5`, not `modalApplyOneS5g`, resolving an internal inconsistency between the
  plan's task-list prose and its own Dependency Analysis table (see above).
- **No file edits for the two blocked phases' unrealized content**: per the zero-debt contract,
  no `sorry`, no partial/uncertain lemma bodies, and no speculative `S5LoopInv` field additions
  were committed. Phase 3's structure/keyed-step/re-derivations *are* committed because they are
  complete, sorry-free, and independently useful regardless of how the design gaps above are
  eventually resolved.
- **`S5LoopInv` kept to the plan's literal four fields**, even though the investigation shows a
  faithful implementation likely needs more (see Phase 3's infrastructure gap) -- extending it
  was judged a design decision for a follow-up task/plan revision, not something to improvise
  mid-implementation.

## Zero-Debt Confirmation

- `grep -rn '\bsorry\b' Cslib/Logics/Modal/Tableau/S5Simplification.lean
  Cslib/Logics/Modal/Tableau/FrameSoundness.lean` -- one match, a pre-existing prose mention
  ("sorry-free counterexample") inside task 504's already-landed `RankStepObstruction` doc
  comment; zero actual `sorry` tactics.
- `grep -n '^axiom ' <touched files>` -- zero.
- No vacuous definitions (`def X := True`, etc.) introduced.
- No `RuleApplicationSpec modalApplyOneS5` witness reintroduced; no rank axiom re-added (D2/D5
  honored).

## Final CI State

- `lake build` (full project): 3236/3236, green.
- `lake exe checkInitImports`: exit 0.
- `lake exe lint-style`: exit 0.
- `lake lint`: 1 error, pre-existing and unrelated (`PrimeExclusion.lean` `unusedArguments`,
  predates this task).
- `lake shake --add-public --keep-implied --keep-prefix`: no import-diff for the touched files
  (pre-existing noise elsewhere in the codebase, not actioned per the plan's testing note).
- `lake test`: exit 0 (9227/9227 jobs).

## Resume Point

Resume at **Phase 3**, with two concrete design/infrastructure decisions to make first (see
"To unblock" above for both P3 and P5). Recommend a short follow-up research/planning pass
(rather than jumping straight back into implementation) to decide: (a) whether `S5LoopInv`
should absorb `S4LoopInv`'s six generic fields wholesale, (b) whether `blockingWorldS5` should
be redesigned to compare against `keys` directly instead of `relevantSetFinset`, and (c) whether
to build the new reachability-threading soundness bridge as fully generic (reusable by S4 too)
or S5-scoped. All landed work (P1, P2, and Phase 3's scaffolding) is committed and CI-green, so
a resumed session can build directly on it without re-deriving any of it.

## Relevant Files

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/S5Simplification.lean`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/plans/01_s5-termination-machinery.md`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/reports/01_s5-termination-implementation-blueprint.md`
