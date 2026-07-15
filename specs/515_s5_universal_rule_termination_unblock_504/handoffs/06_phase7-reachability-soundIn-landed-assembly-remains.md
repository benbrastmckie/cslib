# Handoff: Cycle 7 -- Phase 7 partial (reachability + rule-level soundness landed; assembly remains)

**Date**: 2026-07-15
**Session**: sess_1784146228_152bbf (cycle 7, hard-mode dispatch, resume at Phase 7)
**Status**: Phases 1-6 remain `[COMPLETED]` (untouched, frozen, green -- verified via full `lake
build`/`lake test` this cycle too). Phase 7 is `[PARTIAL]`: four of five sub-tasks landed
sorry-free and CI-green; the final fuel-induction assembly (`modalTableauS5_sound`) was not
attempted. Phases 8, 9 remain `[NOT STARTED]`.

**Commits this cycle** (all scoped to `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` only):
1. `e2430463` -- `modalApplyOneS5_fresh_local` + `accReachableInv` scaffolding
2. `a1018c6b` -- `modalStepBranchS5_preserves_accReachableInv`
3. `4dd7d0e7` -- `modalS5BoxAll_soundIn` / `modalS5DiaNegAll_soundIn`

## What landed this cycle (all sorry-free, CI-green)

1. **`modalApplyOneS5_fresh_local`**: the S5 driver satisfies the same `freshLocal` dichotomy as
   K's `modalApplyOne_fresh_local` (`FmpMeasure.lean:802`). Lifted via the already-landed
   `modalApplyOneS5_snd_eq` (case: acc unchanged) and `modalApplyOneS5_eq_of_linear` (case: K's
   result is `.linear`, so S5 agrees with K exactly).

2. **`accReachableInv`** (new invariant): `∀ w ∈ modalKnownWorlds b, Relation.ReflTransGen (fun
   a c => acc.hasEdge a c) 0 w` -- every known world of a branch is reachable from world `0` via
   the recorded accessibility edges. This is the extra invariant beyond `accFreshInv` that S5
   soundness needs: the universal rules propagate to *every* known world, not just
   directly-`acc`-connected ones, so their soundness needs every known world related to a common
   origin in the model.
   - `accReachableInv_initial`: holds for the initial singleton branch `[⟨.neg, φ, 0⟩]` against
     `Accessibility.empty` (trivial, `w = 0` by reflexivity).
   - `modalStepBranchS5_preserves_accReachableInv`: single-step preservation across a
     `modalStepBranchGen modalApplyOneS5` step, given `accTargetsKnown b acc` also holds. Reuses
     the ALREADY-LANDED (Phase 4/5, `S5Simplification.lean:860`) `modalApplyOneS5_knownWorlds_step`
     -- **do not re-derive this**, it already exists publicly. The "acc unchanged" branch
     transfers reachability for known worlds unchanged (every emitted formula's label, whether
     from K's own bounded propagation or the S5 universal arms, is already known on `b`); the
     "mint" branch extends the popped formula's own (already-known, hence already-reachable)
     witness by the one fresh edge via `Relation.ReflTransGen.tail`.
   - Local re-derivations needed (the `FmpMeasure.lean`/`Soundness.lean` originals are `private`,
     unavailable across files -- same pattern `S5Simplification.lean`/`BDriver.lean` already use,
     suffixed `_FS` here for FrameSoundness): `modalKnownWorlds_fold_spec_FS`,
     `mem_modalKnownWorlds_FS`, `modalKnownWorlds_mono_append_FS`,
     `modalKnownWorlds_append_subset_of_labels_known` (new converse direction, not present
     elsewhere), `hasEdge_addEdge_cases_FS`, `hasEdge_addEdge_mono_FS` (new), `hasEdge_addEdge_self_FS`
     (new).

3. **`reachable_imp_related_s5`**: `accReachableInv`'s witness (reachability from `0`) plus
   `hacc` (edge-to-model-relatedness) plus `s5FC` (`Std.Refl` + `Relation.RightEuclidean`) gives
   `m.r (f 0) (f w)` for any known `w`. Proved by `induction hreach` (on `Relation.ReflTransGen`
   directly -- Lean's default recursor handles the endpoint-generalization correctly): base case
   is `hFC.1.refl`; the tail step needs `m.r (f 0)(f prev)` [ih] composed with `m.r (f
   prev)(f w)` [from `hacc`] into `m.r (f 0)(f w)` -- done via **two** raw
   `Relation.RightEuclidean.rightEuclidean` field-projection applications (NOT via `Std.Symm`/
   `IsTrans` typeclass instance search, which would need `haveI` juggling): first symmetrize
   `ih` (`heuc.rightEuclidean ih (hFC.1.refl (f 0))`), then compose with the step
   (`heuc.rightEuclidean <that> step`). This sidesteps all typeclass-instance plumbing --
   `Relation.RightEuclidean` is a plain one-field structure/class, so `.rightEuclidean` works as
   direct dot-notation on any term, instance search not required.
4. **`accReachableInv_related_s5`**: corollary -- any two known worlds `w, w'` (both reachable
   from `0`) are related `m.r (f w) (f w')` directly, via ONE more `rightEuclidean` application
   on the two `reachable_imp_related_s5` witnesses (both from the SAME origin `0`, so no
   symmetrization needed this time).

5. **`modalS5BoxAll_soundIn` / `modalS5DiaNegAll_soundIn`**: the rule-level frame-relativized
   semantic soundness of `modalApplyOneS5`'s box-positive/diamond-negative output under `s5FC`,
   given `accReachableInv`. Structure (mirrors `modalApplyOneS5_boxPos_diaNeg_eq`'s own proof
   skeleton, `S5Simplification.lean:486-570`, but threading `RuleResultSat`/`sfSat` instead of
   just "labels known"):
   - `modalApplyOne_boxPos_eq`/`modalApplyOne_diamondNeg_eq` (`Rules.lean:244/273`) give K's own
     `kResult` dichotomy (`.notApplicable` or `.persistent kForms`) -- rules out `.linear`/
     `.branching` for K itself at these two shapes.
   - `modalApplyOne_boxPos_sound`/`modalApplyOne_diaNeg_sound` (`SoundnessStep.lean:446/490`)
     give `RuleResultSat` for `kForms` directly (K's OWN bounded propagation, sound via direct
     `hacc` edges -- reused as a black box, unchanged).
   - The S5-added universal-propagation half (`modalS5BoxAll`/`modalS5DiaNegAll`'s output): for
     `x` in that list, `modalS5BoxAll_mem`/`modalS5DiaNegAll_mem` give `x`'s formula shape and
     `x.label ∈ modalKnownWorlds b`; combined with `lbl`'s own known-ness (from `hmem`) and
     `accReachableInv_related_s5`, get `m.r (f lbl) (f x.label)`, then `sfSat_pos`/`sfSat_neg`
     close it via the box/diamond `Satisfies` unfold.
   - Final assembly: `unfold modalApplyOneS5`, case on K's `kResult` dichotomy (as
     `modalApplyOneS5_boxPos_diaNeg_eq` itself does), combine `RuleResultSat`-for-`kForms` with
     the S5-half's `sfSat` fact over the `kForms ++ allNew.filter (...)` append (or bare
     `allNew` in the notApplicable-upgraded case).

## What remains: `modalTableauS5_sound` (the fuel-induction assembly)

**Not attempted this cycle** -- no `lean_goal` failure to report (the theorem statement itself
was never written), so this is a **structural** blocker, established by direct inspection, not
a failed proof attempt:

- Cannot reuse the existing `modalExpandBranchesGen_closed_unsatIn`/
  `modalStepBranchGen_preserves_satIn` (`FrameSoundness.lean:193`/`728`) generically at
  `apply := modalApplyOneS5`: their `hBoxPos`/`hDiaNeg` hypotheses are universally quantified
  over **all** `(b, acc)` pairs (only `hFC`, `hacc`, `hb`, `hmem` available inside the proof
  obligation) -- there is no parameter slot to receive `accReachableInv b acc`, which is
  genuinely required (it is a fact about the *specific computational history* of `(b,acc)`, not
  derivable from `hacc` alone for an arbitrary pair). Confirmed by reading the full hBoxPos/
  hDiaNeg signatures (`FrameSoundness.lean:199-216`) -- there is no way to thread an extra
  invariant through without changing the lemma's type.
- The needed replacement is a **bespoke fuel induction** combining `branchSatisfiableIn s5FC`,
  `accReachableInv`, and `accTargetsKnown` together, case-splitting on the popped `sf`'s shape:
  - **Box-pos/dia-neg shape**: reduces cleanly to the now-landed `modalS5BoxAll_soundIn`/
    `modalS5DiaNegAll_soundIn` (semantic half) plus `modalApplyOneS5_boxPos_diaNeg_eq`
    (structural half, rules out `.linear`/`.branching`). **This part is ready to assemble.**
  - **Every other shape** (atomic no-ops, all six propositional α/β rules, the two K-minting
    shapes `F(□φ)`/`T(◇φ)`): `modalApplyOneS5` agrees with `modalApplyOne` exactly
    (`modalApplyOneS5_eq_of_not_boxPos_diaNeg`), so the semantics needed here are IDENTICAL to
    the "not shape" branch already proved inline inside `modalStepBranchGen_preserves_satIn`
    (`FrameSoundness.lean:230-717`, ~490 lines -- the K/T-shared monolith, of which only
    `negImp_alpha_preserved_gen` was ever factored into a standalone reusable lemma; the rest
    is a single giant `match`/`rcases` chain not currently callable as a black box).
- **Two viable strategies for the next dispatch** (neither attempted; pick one and go):
  1. **Extract-and-reuse** (cleaner, touches existing code): refactor
     `modalStepBranchGen_preserves_satIn`'s "not shape" branch (lines ~230-717) into its own
     lemma, parametrized generically over `apply`/`FC`, taking `happly_eq : apply sf b acc =
     modalApplyOne sf b acc` (rather than deriving it from `hAgree` applied to the ambient `sf`)
     plus the usual `sf, e, b, acc, hsfmem, hsf, hFC, hacc, hb` -- then BOTH the original K/T
     crux and the new S5 assembly call it. Risk: must not regress the existing (frozen, green)
     `modalStepBranchGen_preserves_satIn`/`modalTableauT_sound`/etc. -- run `lake build` and
     `lake test` immediately after the refactor, before adding any new S5-specific code, to
     isolate any regression.
  2. **Bespoke copy**: write a standalone S5-only version of the ~490-line "not shape" branch,
     specialized to `apply := modalApplyOneS5` throughout (same case structure, same tactics,
     `hFC`/`hacc`/`hb` threaded unchanged as the existing code already does -- reachability is
     irrelevant to this branch since only the box-pos/dia-neg shapes need it). Lower risk to
     existing code, but ~490 lines of near-duplicate proof.
- Either way, the outer fuel induction itself (zero/succ cases, `List.Forall₂` bookkeeping) can
  mirror `modalExpandBranchesGen_closed_unsatIn`'s existing skeleton (`FrameSoundness.lean:728-897`)
  near-verbatim, with `accReachableInv`/`accTargetsKnown` added as extra threaded
  `List.Forall₂`-tracked invariants alongside `accFreshInv` (drop `accFreshInv` entirely if
  unneeded -- it does not appear to be used by anything in the box/dia soundIn lemmas or by
  `accTargetsKnown`'s own generic preservation lemma, `modalStepBranch_preserves_accTargetsKnown_gen`,
  `FmpMeasure.lean:1907`, which is ALREADY generic and directly reusable at `apply :=
  modalApplyOneS5` given `modalApplyOneS5_fresh_local` -- landed this cycle -- as its
  `hFreshLocal` witness).

## Next dispatch recipe

1. Read this handoff in full, then `FrameSoundness.lean`'s new Phase 7 section (search
   `## Task 515 Phase 7`, ~line 1296 onward) to see the five landed lemmas in place.
2. Pick strategy 1 or 2 above for the "not shape" case. If picking strategy 1 (extraction),
   `lake build`+`lake test` immediately after the refactor, BEFORE writing any new S5 code, to
   confirm zero regression on the existing K/T/B/S4 soundness chain.
3. Write the outer bespoke fuel induction (`modalExpandBranchesS5_closed_unsatIn` or similar
   name), mirroring `modalExpandBranchesGen_closed_unsatIn`'s zero/succ skeleton
   (`FrameSoundness.lean:728-897`), threading `accReachableInv`+`accTargetsKnown` via
   `modalStepBranchS5_preserves_accReachableInv` (landed) and
   `modalStepBranch_preserves_accTargetsKnown_gen` (already generic, reuse directly).
4. Assemble `modalTableauS5_sound` mirroring `modalTableauT_sound`
   (`FrameCompleteness.lean:1182`), instantiating the new S5 fuel induction against
   `modalTableauS5`/`modalApplyOneS5` (landed by task 504).
5. After Phase 7 closes, Phase 8 (spec-free Hintikka lift, HIGH risk, Strategy-2 FMP fallback
   pre-authorized) is the only remaining hard frontier; it does NOT depend on Phase 7 per the
   plan's own dependency line ("Depends on: 6 and 3"), so it can also be attempted in parallel
   or first if Phase 7's assembly proves stubborn again.

## Reusable building blocks now available (do not re-derive)

- `modalApplyOneS5_fresh_local`, `accReachableInv`, `accReachableInv_initial`,
  `modalStepBranchS5_preserves_accReachableInv`, `reachable_imp_related_s5`,
  `accReachableInv_related_s5`, `modalS5BoxAll_soundIn`, `modalS5DiaNegAll_soundIn` (all in
  `FrameSoundness.lean`, ~line 1296 onward).
- `modalApplyOneS5_knownWorlds_step` (already landed Phase 4/5, `S5Simplification.lean:860`).
- `modalStepBranch_preserves_accTargetsKnown_gen` (generic, `FmpMeasure.lean:1907`), directly
  usable at `apply := modalApplyOneS5` via `modalApplyOneS5_fresh_local`.
