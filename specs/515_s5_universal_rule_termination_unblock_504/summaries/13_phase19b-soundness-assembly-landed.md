# Summary 13: Phase 19b `modalTableauFive_sound` bespoke assembly landed

**Task**: 515 (`s5_universal_rule_termination_unblock_504`)
**Plan**: `plans/07_s5-termination-machinery.md` (v6)
**Phase**: 19b (`modalTableauFive_sound` bespoke assembly) -- now `[COMPLETED]`
**Commits landed this dispatch**:
- `b13f8c96` (`task 515 phase 19b.1: land root-exclusion strengthening for modalApplyOneFive reuse`)
- `0499449f` (`task 515 phase 19b: land modalTableauFive_sound bespoke soundness assembly`)

## Scope of this dispatch

Resumed from continuation handoff `handoffs/12_phase19a-completed-ready-for-19b.md` (Phase 19a
fully `[COMPLETED]`: the mint-arm guard `56a84d07` and the source-split termination-bound
re-derivation `2c7abe73`, neither re-touched this dispatch). This dispatch closed Phase 19b: the
second and final soundness gap for the Euclidean-frame (5/KB5) tableau, landing
`modalTableauFive_sound`.

## What landed

### Sub-milestone 1 (`b13f8c96`, `FiveSimplification.lean`, additive)

Three small strengthening lemmas, needed because `accReachableInv_related_five` (unlike S5's
`accReachableInv_related_s5`) requires **both** endpoints of a reuse edge to be non-root
(`fiveFC` is only `RightEuclidean`, not an equivalence, so relating the root to an arbitrary
known world is unsound in general -- the two-island adversarial-model kill from `reports/08_*`).
The already-landed `modalApplyOneFive_agree_or_reuse` did not expose this fact:

- `modalApplyOneFive_diaPos_eq_or_reuse_ne_root` / `modalApplyOneFive_boxNeg_eq_or_reuse_ne_root`:
  per-shape strengthenings of the landed `_eq_or_reuse` lemmas, additionally packaging `w ≠ 0`
  (immediate from the guard's own `if sf.label == 0 then .. else ..` case split -- reuse only
  fires in the `else` branch).
- `modalApplyOneFive_agree_or_reuse_ne_root`: the combined dichotomy, exposing
  `sf.label ≠ 0 ∧ sf'.label ≠ 0` at a reuse call (the latter via `witnessWorldFive_mem`'s own
  root-exclusion, already established).

### Sub-milestone 2 (`0499449f`, `FrameSoundness.lean`, additive)

The bespoke Five/KB5 fuel-induction assembly, mirroring the S5 bespoke chain (`S5SoundInv` →
`modalStepBranchS5Gen_preserves_satIn` → `modalExpandBranchesS5Gen_closed_unsatIn` →
`modalTableauS5Gen_sound`/`_S5w_sound`/`_S5_sound`, ~860 lines at the S5 frame class) but stated
**directly and non-generically** over the single shipped `modalApplyOneFive` rule -- no
`RuleApply`/`S5SoundSpec`-style abstraction layer was needed or added, since Five (unlike S5) has
only one rule stage.

- **`modalStepBranchFive_preserves_satIn`**: per-step `fiveFC`-satisfiability preservation.
  - **Witness-reuse case** (handled first): discharged via `modalApplyOneFive_agree_or_reuse_ne_root`
    (sub-milestone 1) + `accReachableInv_related_five` at the two root-excluded endpoints. No
    world is minted; `f` is not extended.
  - **Propagation shapes** (box-positive/diamond-negative): discharged via the already-landed
    `modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn`, operating directly on
    `modalApplyOneFiveProp`.
  - **Every other shape** (ordinary prop rules, and the two K-minting shapes when
    `modalApplyOneFive` agrees with `modalApplyOneFiveProp`, i.e. no reuse fired): ported the K
    arm verbatim via `modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg`, byte-identical to the S5
    chain's own "not shape" branch under the literal `s5FC ↦ fiveFC` substitution -- that branch
    never inspects frame-condition-specific facts (reflexivity, symmetry, Euclideanness), only
    threading the frame-condition witness `hFC` opaquely through the output model.
- **`modalExpandBranchesFive_closed_unsatIn`**: the fuel induction, threading the already-landed
  `FiveSoundInv` (`accFreshInv ∧ accReachableInv ∧ accTargetsKnown`) via `List.Forall₂`, reusing
  `modalStepBranch_preserves_accFreshInv_gen`/`modalStepBranch_preserves_accTargetsKnown_gen`
  (generic, instantiated at `modalApplyOneFive`/`modalApplyOneFive_fresh_local`) and the
  already-landed `modalStepBranchFive_preserves_accReachableInv`.
- **`modalTableauFive_sound`**: the capstone theorem
  `(h : modalTableauFive φ = .closed) : fiveValid φ`, contrapositive over `fiveFC` from the
  initial branch `[⟨.neg, φ, 0⟩]`, with the initial `FiveSoundInv` witness built from
  `accFreshInv_empty`, the already-landed `accReachableInv_initial`, and the trivial vacuous
  `accTargetsKnown` for the edgeless empty accessibility relation.

## Key design finding: no world-bound hypothesis needed

Phase 19a's `FiveWorldInv`/`modalMaxWorld_lt_worldBound_of_FiveWorldInv` termination-bound
machinery is **not consumed by this soundness assembly at all**. Inspection of the S5 chain's own
`S5SoundInv` confirmed it likewise carries **no world-bound term** -- `modalApplyOneFive_specCore`'s
`outputsSubsetUniverse`/`hW : modalMaxWorld b < modalWorldBound φ0` field is Hintikka/completeness-
side machinery (feeding Phase 21's decidability lift), not soundness-side. This substantially
reduced Phase 19b's actual scope relative to the plan's conservative "may need `FiveWorldInv` as an
inductive invariant across the induction" framing: the *static* Phase 19a machinery already
supplies everything Phase 21 will need; Phase 19b required no further step-preservation proof for
`FiveWorldInv`.

## Verification performed

- `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` (scoped) -- green, sorry-free.
- `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` (scoped) -- green, sorry-free.
- `lake build` (full project) -- green, 3240/3240 jobs.
- `lake exe checkInitImports` -- exit 0.
- `lake exe lint-style` -- exit 0, no output.
- `lake lint` (full-repo scan) -- zero new warnings attributable to either touched file (only the
  pre-existing `FiveSimplification.lean:522-523` baseline and the standing repo-wide
  `PrimeExclusion.lean` error, both unchanged).
- `lake shake --add-public --keep-implied --keep-prefix` -- no import-removal/addition suggestion
  for either touched file.
- `lake exe mk_all --module` -- "No update necessary".
- `lake test` -- exit 0, full `CslibTests/` suite green.
- `grep -n "sorry"` on both touched files -- zero hits.
- Axiom check via `lake env lean` + `#print axioms` on all three new top-level declarations
  (`modalStepBranchFive_preserves_satIn`, `modalExpandBranchesFive_closed_unsatIn`,
  `modalTableauFive_sound`) and the three sub-milestone-1 lemmas -- all report only `[propext,
  Classical.choice, Quot.sound]` (a subset for the two pure-`Prop`-level lemmas) -- no `sorryAx`,
  no new custom axiom.

## Plan Deviations

None. Both Phase 19b tasks were completed as specified:
1. `modalStepBranchFive_preserves_satIn` -- landed, per the plan's exact dispatch description
   (propagation via `modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn` +
   `accReachableInv_related_five`; witness-reuse via the 19a guard).
2. The fuel induction assembled into `modalTableauFive_sound` -- landed, mirroring the S5 bespoke
   chain's shape (`FiveSoundInv` in place of `S5SoundInv`).

The KILL CONDITION was not triggered: the assembly built sorry-free on the first attempt, at
~640 new lines total (75 in `FiveSimplification.lean` + 565 in `FrameSoundness.lean`, plus doc
comments) against the plan's ~800-1100-line estimate -- well within budget, mainly because no
`RuleApply`/spec-class abstraction layer was needed (Five has only one rule) and no world-bound
step-invariant was needed (see the design finding above).

Hard constraints honored: worked in `FrameSoundness.lean` (primary target per the plan's own
"Files to modify" line) plus a small additive strengthening in `FiveSimplification.lean`; did not
touch `S5Simplification.lean`'s shared `S5w*` declarations; zero `sorry`; did not weaken
`modalApplyOneFive_specCore`/`fiveFC`/`kb5FC`/the soundness target's statement; resolved every
declaration by name; two sub-milestone commits (`phase 19b.1`, `phase 19b`), each independently
`lake build`-verified and sorry-free before committing; `git add` scoped narrowly to the touched
files only.

## Files changed

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (additive:
  three root-exclusion strengthening lemmas)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (additive: the
  bespoke Five/KB5 soundness assembly, ~565 lines)
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`
  (Phase 19b marked `[COMPLETED]`, all three checklist items marked `[x]` with landing notes)

## Next steps

Phase 19b is `[COMPLETED]`. **All of Phase 19 (19a + 19b) is now closed** -- both Phase-19
soundness gaps (Route-1 propagation, landed earlier; and the mint-arm witness-reuse gap, closed
by 19a's guard + 19b's soundness assembly) are resolved, and `modalTableauFive_sound` is fully
assembled and green. Phases 20-23 remain queued (Phase 20, the completeness/countermodel half, was
already `[IN PROGRESS]` in parallel per the plan's wave sequencing and is untouched by this
dispatch). Per instruction, Phases 20-23 were NOT started this dispatch.
