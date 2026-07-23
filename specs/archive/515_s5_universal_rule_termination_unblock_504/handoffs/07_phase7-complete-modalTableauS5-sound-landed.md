# Handoff: Cycle 8 -- Phase 7 COMPLETE (`modalTableauS5_sound` landed sorry-free)

**Date**: 2026-07-15
**Session**: sess_1784149767_9c2b55 (cycle 8, hard-mode dispatch, resumed at Phase 7)
**Status**: Phases 1-7 are ALL `[COMPLETED]`. Phase 7's final fuel-induction assembly
(`modalTableauS5_sound`), left `[PARTIAL]` at the end of cycle 7 (handoff 06), is now landed
sorry-free and CI-green. Phases 8, 9 remain `[NOT STARTED]` -- not attempted this cycle (see
"Why Phase 8 was not attempted" below).

**Commit this cycle** (scoped to `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` only, plus this
task's own plan/summary/handoff artifacts):
- `task 515 phase 7: complete -- modalTableauS5_sound assembly landed sorry-free` (see `git log`
  for the exact hash; committed immediately after this handoff is written).

## What landed this cycle

Per handoff 06's recipe, chose **Strategy 2 (bespoke copy)** over Strategy 1 (extraction) to keep
zero blast-radius on the frozen K/T/B/S4 soundness chain. Three new declarations, all in
`FrameSoundness.lean`, immediately after the cycle-7 semantic core:

1. **`S5SoundInv`** (new `def`): `accFreshInv b acc ∧ accReachableInv b acc ∧ accTargetsKnown b
   acc`, bundled into one `Prop` so a single `List.Forall₂` threads all three invariants through
   the outer fuel induction (mirroring how the K/T generic chain threads `accFreshInv` alone via
   `List.Forall₂ (fun b acc => accFreshInv b acc)`).

2. **`modalStepBranchS5_preserves_satIn`** (new `theorem`): bespoke S5 specialization of
   `modalStepBranchGen_preserves_satIn` (`FrameSoundness.lean:193`, the generic K/T/B/S4 crux),
   fixed to `apply := modalApplyOneS5`, `FC := s5FC`, with an added `hreach : accReachableInv b
   acc` parameter. Structure:
   - Box-pos/dia-neg branch: swaps in the landed `modalS5BoxAll_soundIn hFC hacc hb hreach
     hsfmem` / `modalS5DiaNegAll_soundIn hFC hacc hb hreach hsfmem` in place of the generic
     theorem's `hBoxPos`/`hDiaNeg` parameters (which CANNOT receive `hreach`, since their type is
     universally quantified over all `(b, acc)` pairs -- confirmed structurally in handoff 06,
     not merely assumed).
   - Every other shape ("not box/dia" branch): byte-for-byte copy of the generic crux's own "not
     shape" branch (originally `FrameSoundness.lean:318-718`, ~400 lines). Confirmed via `grep`
     BEFORE writing that the ONLY two places in that branch referencing the generic `apply`/`FC`
     parameters are: (a) the `heq := hAgree ... ` derivation (replaced with
     `modalApplyOneS5_eq_of_not_boxPos_diaNeg ...`), and (b) one `negImp_alpha_preserved_gen FC
     hFC hacc hb hneg` call inside the `imp`/`bot` sub-case (its `FC` replaced by `s5FC`). Every
     other line in that branch is untouched verbatim (it only ever references the LOCAL
     hypothesis names `hFC`/`hacc`/`hb`/`hInv`, never the outer type parameters).

3. **`modalExpandBranchesS5_closed_unsatIn`** (new `theorem`): bespoke S5 specialization of
   `modalExpandBranchesGen_closed_unsatIn` (`FrameSoundness.lean:729`), fixed similarly, threading
   `S5SoundInv` (not bare `accFreshInv`) via `List.Forall₂`. At each step of the succ-case
   induction, the combined invariant for each new child branch is built from THREE
   preservation calls:
   - `modalStepBranch_preserves_accFreshInv_gen modalApplyOneS5 modalApplyOneS5_fresh_local ...`
     (ALREADY GENERIC in `apply`, from `Soundness.lean:122` -- zero new proof content, reused
     directly).
   - `modalStepBranch_preserves_accTargetsKnown_gen modalApplyOneS5 modalApplyOneS5_fresh_local
     ...` (ALREADY GENERIC in `apply`, from `FmpMeasure.lean:1907` -- zero new proof content).
   - `modalStepBranchS5_preserves_accReachableInv ...` (the cycle-7-landed lemma, already S5
     bespoke).
   The rest of the induction (zero/succ fuel cases, `List.Forall₂` bookkeeping, `done`/`pending`
   list-splitting arithmetic) is a byte-for-byte copy of the generic version with `FC → s5FC`,
   `apply → modalApplyOneS5` substitutions and the invariant-threading swapped from bare
   `accFreshInv` to `S5SoundInv` (destructured non-destructively via `hInv_bh.1`/`.2.1`/`.2.2`
   into `hFresh_bh`/`hReach_bh`/`hKnown_bh` immediately after the `cons hInv_bh hInv_rest` match,
   so the original bundled `hInv_bh` remains available for the `List.Forall₂.cons` re-bundling
   in the "closed" branch).

4. **`modalTableauS5_sound`** (new `theorem`, the capstone): mirrors `modalTableauT_sound`
   (`FrameCompleteness.lean:1182`) exactly. `by_contra` on a falsifying model at world `w`; builds
   the initial `branchSatisfiableIn s5FC [⟨.neg, φ, 0⟩] Accessibility.empty` witness (same shape
   as T's); builds the initial `S5SoundInv` witness as `⟨accFreshInv_empty _,
   accReachableInv_initial φ, <inline vacuous accTargetsKnown proof for the edgeless
   Accessibility.empty>⟩`; feeds both into `modalExpandBranchesS5_closed_unsatIn (modalFuel φ)` at
   `[[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty]`; the `h : modalTableauS5 φ = .closed` hypothesis
   is threaded to the generic-driver form via a `have h' : modalExpandBranchesGen modalApplyOneS5
   ... = .closed := h` term (typechecks via defeq unfolding of `modalTableauS5 →
   modalTableauGen modalApplyOneS5 → modalExpandBranchesGen modalApplyOneS5 ...`, exactly as T's
   own proof does at `FrameCompleteness.lean:1205-1208`).

## CI verification (this cycle)

- `lake build` (full project): 3239/3239 jobs green.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake lint`: 0 new errors (only the 1 pre-existing unrelated `PrimeExclusion.lean`
  `unusedArguments` error, confirmed untouched).
- `lake test`: `CslibTests` suite exit 0.
- `lake shake --add-public --keep-implied --keep-prefix`: the only suggestion touching
  `FrameSoundness.lean` is `remove import Mathlib.Data.List.Forall2` -- confirmed **pre-existing**
  and unrelated to this cycle's additions: `Soundness.lean` (already `public import`ed by
  `FrameSoundness.lean`) also directly `import`s `Mathlib.Data.List.Forall2`, and `List.Forall₂`
  was already used extensively by the pre-existing (untouched) K/T generic fuel induction before
  this cycle's edits -- the redundant-transitive-import fact predates this dispatch. (A
  before/after `git stash` A/B comparison was attempted but proved unreliable: `lake shake`
  reads stale `.olean` caches without rebuilding, so stashing the file produces a spurious
  "target is out-of-date" error for that file rather than an accurate baseline. Manual inspection
  of the import graph was used instead, and is conclusive.)
- `grep -c sorry Cslib/Logics/Modal/Tableau/FrameSoundness.lean`: 0.
- `grep -c '^axiom ' Cslib/Logics/Modal/Tableau/FrameSoundness.lean`: 0.
- `lean_verify` on `modalTableauS5_sound`, `modalStepBranchS5_preserves_satIn`,
  `modalExpandBranchesS5_closed_unsatIn`: `{"axioms":["propext","Classical.choice","Quot.sound"],
  "warnings":[]}` for all three -- standard Mathlib axioms only, no new axioms.

**Zero-regression confirmation**: no pre-existing declaration in `FrameSoundness.lean` was
edited -- this cycle's diff is a pure append (verified: the only `Edit` call this cycle targeted
the string immediately preceding `end Cslib.Logic.Modal.Tableau` / `end`, inserting new content
before it). The full `lake build`/`lake test` re-run above confirms the entire K/T/B/S4 chain
remains green.

## `sorry_inventory`

Empty. Zero sorries introduced or remaining in any file touched this cycle.

## Why Phase 8 was not attempted this cycle

Phase 7's assembly consumed the bulk of this dispatch's tool-call and context budget (reading the
~1700-line file's generic machinery in full to confirm the bespoke-copy transformation was exact,
then writing and verifying ~700 lines of new proof). Phase 8 (spec-free Hintikka lift + fuel
bridge + `Decidable (s5Valid φ)`) is explicitly flagged in the plan as the **HIGH-risk hard
frontier** ("No template; the hard frontier (F4)") deserving its own dedicated, fresh-context
dispatch rather than a rushed attempt on a nearly-exhausted budget. This is a deliberate
stopping point, not a blocker: Phase 7 is fully closed and green, and Phase 8 does NOT depend on
it (plan's own "Depends on: 6 and 3" line, both already landed).

## Next dispatch recipe (Phase 8 entry point)

1. Read the plan's Phase 8 section (`plans/02_s5-termination-machinery.md`) and this summary's
   "Cycle 8: Phase 7 Completion" section in full first.
2. Read `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean:876` (`modalExpandBranchesGen_hintikka`)
   to understand the existing rank-bound generic Hintikka lift this must be generalized from
   (swap the induction measure from `ModalLoopInvGen` (rank) to `S5LoopInv` (world bound, landed
   Phase 3/6)).
3. Attempt `modalExpandBranchesS5_hintikka` first (Option (i), the loop-checking capstone). If it
   resists within budget: mark Phase 8 `[BLOCKED]` with the exact `lean_goal` open state at the
   failing induction step, then pivot to **Strategy 2 (pre-authorized, F8)**: semantic
   bounded-model FMP via the landed `extractModelS5` (equivalence-relation model enumeration
   `≤ 2^(2·|Sf|)` + filtration truth lemma), which bypasses the generic driver's termination
   entirely (Massacci Fact 9.1: S5 has polynomial single-cluster models). This gives
   `instDecidableS5Valid` sorry-free without the Hintikka lift.
4. Also attend to the fuel bridge (F6): prove `modalExpMeasureS5 (modalUniverseS5 φ) ... ≤
   modalFuel φ` (Option (i)) or, if domination is false, define `modalTableauS5g` with a derived
   `modalFuelS5` (Option (ii)).
5. Phase 9 (5/KB5 validity + completeness) is gated on Phase 8; do not attempt until Phase 8 lands
   (or lands a partial fragment sufficient for `fiveValid`'s direct `Satisfies.five` route, per
   the plan's Phase 9 blocked-branch note).

## Reusable building blocks now available (do not re-derive)

All cycle-7 building blocks (`modalApplyOneS5_fresh_local`, `accReachableInv` (+`_initial`),
`modalStepBranchS5_preserves_accReachableInv`, `reachable_imp_related_s5`,
`accReachableInv_related_s5`, `modalS5BoxAll_soundIn`, `modalS5DiaNegAll_soundIn`) PLUS, new this
cycle:
- `S5SoundInv`, `modalStepBranchS5_preserves_satIn`, `modalExpandBranchesS5_closed_unsatIn`,
  `modalTableauS5_sound` (all in `FrameSoundness.lean`, appended after the cycle-7 section).
- Confirmed-generic (reusable at any `apply`, no re-derivation needed):
  `modalStepBranch_preserves_accFreshInv_gen` (`Soundness.lean:122`),
  `modalStepBranch_preserves_accTargetsKnown_gen` (`FmpMeasure.lean:1907`),
  `forall₂_replicate_right` (`LoopInduction.lean:43`).
