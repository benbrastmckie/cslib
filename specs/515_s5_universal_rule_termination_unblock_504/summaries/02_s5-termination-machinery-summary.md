# Implementation Summary: S5 Universal-Rule Termination Machinery (v2 plan, round 2, cycle 2)

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Plan**: `plans/02_s5-termination-machinery.md`
- **Status**: PARTIAL -- Phase 3 COMPLETED; Phase 4 (generic-field preservation) BLOCKED at 4 of
  6 fields (`eNodup`/`accFresh`/`accKnown`/`outDegEq` landed; `bClosure`/`eClosure` blocked on a
  missing contiguity invariant, see below); Phase 6 (pigeonhole world bound) COMPLETED; Phases
  5, 7, 8, 9 NOT STARTED.
- **Commits this dispatch (cycle 2)**: `db5b837a` (Phase 4: accFresh/accKnown/outDegEq),
  `8e4a17ba` (Phase 6: pigeonhole world bound)
- **Handoffs**:
  - `handoffs/01_phase4-generic-field-preservation.md` (prior dispatch: proof template, gotchas)
  - `handoffs/02_phase4-bclosure-contiguity-gap.md` (this dispatch: exact `bClosure`/`eClosure`
    blocker and recommended 12th-invariant-field fix)

## Cycle 2 Context

This dispatch resumed from a quota-halted prior session. Step 0 recovered ~364 lines of
UNVERIFIED mid-edit WIP from git stash (`task515-cycle2-WIP`) via `git stash pop` (clean, no
conflicts), covering draft `accFresh`/`accKnown`/`outDegEq` preservation lemmas. The stash
restored cleanly but did not build; one outstanding `rw` failure in `outDegEq`'s proof was
diagnosed and fixed (see "Central finding" below). All three stashed lemmas then built,
verified, and were committed. Phase 6's pigeonhole bound was then authored fresh (not present in
the stash) and landed in full. Phase 4's `bClosure`/`eClosure` were then investigated and found
to require additional infrastructure not achievable safely within this dispatch's remaining
budget (documented as a precise, actionable blocker rather than rushed with `sorry` or a
vacuous placeholder).

## Per-Phase Status Ledger

| Phase | Status | Notes |
|-------|--------|-------|
| 1. Frame surface + S5 world bound + universe | COMPLETED (prior dispatch) | commit `66021669` |
| 2. Live-set guard + guarded rule (preserved scaffold) | COMPLETED (prior dispatch) | commit `aa9015d6` |
| 3. Keys-aware guard redesign + extended `S5LoopInv` | COMPLETED (prior dispatch) | commit `4f41f3a4` |
| 4. Generic-field preservation lemmas | **BLOCKED (4/6)** | `eNodup` (prior dispatch, `12f32499`); `accFresh`/`accKnown`/`outDegEq` (this dispatch, `db5b837a`); `bClosure`/`eClosure` BLOCKED -- see handoff 02 |
| 5. Birth-key preservation lemmas | NOT STARTED | gated on Phase 4; `keysDistinct` assessed easy (`blockingWorldS5Keyed_none_fresh` already landed), `keysTotal`/`keysInUniverse` share the same contiguity-gap blocker as `bClosure` |
| 6. Pigeonhole world bound | **COMPLETED** | `modalKnownWorlds_length_le_worldBoundS5`, this dispatch, commit `8e4a17ba` |
| 7. Soundness bridge `modalTableauS5_sound` | NOT STARTED | independent of termination chain; not attempted this dispatch (budget spent on Phase 4/6 investigation) |
| 8. Spec-free Hintikka lift + fuel + completeness + decidability | NOT STARTED | highest-risk frontier per plan |
| 9. 5/KB5 validity + completeness | NOT STARTED | gated on Phase 8 |

## What Was Delivered This Dispatch (Cycle 2)

### Phase 4: `accFresh`/`accKnown`/`outDegEq` (commit `db5b837a`)

Both `modalStepBranchS5g_preserves_accFresh` and `_preserves_accKnown` built cleanly from the
recovered stash with no changes needed. `modalStepBranchS5g_preserves_outDegEq`'s stashed proof
had one outstanding build error, fixed as follows:

**Central finding (reusable pattern)**: the stashed proof's final step,
`rw [modalApplyOne_outDeg_step ..., ← modalApplyOneS5_eshape_eq ...]`, failed with "did not find
occurrence of the pattern" even though the pattern was visibly present in the goal's pretty-print.
Root cause: Lean compiles each `match ... with` expression to its own auto-generated matcher
auxiliary constant, PER OCCURRENCE in the source -- so two syntactically-identical `match`
expressions written in two different lemmas' statements (`modalApplyOne_outDeg_step` and
`modalApplyOneS5_eshape_eq`) are backed by two DIFFERENT matcher constants, which `rw`'s
`kabstract` cannot unify (it requires the same head symbol), even though `exact`/term-mode
elaboration succeeds via `isDefEq` (which unfolds matcher auxiliaries during whnf and finds them
defeq). **Fix**: bridge the two lemmas via a term-mode composition instead of `rw`:
```lean
have hfull := (modalApplyOne_outDeg_step ...).trans
  (congrArg (fun l => (List.filter ... l).length) (modalApplyOneS5_eshape_eq ...).symm)
```
then `rw [hfull]` (a plain, single-instance substitution, safe) and case-split cleanly. Also
required one `omit [Hashable Atom] in` annotation to clear a new `unusedSectionVars` warning
introduced by the lemma (caught by `lake shake`, not `lake lint`, but fixed per the lint
prevention rules regardless).

### Phase 6: Pigeonhole world bound (commit `8e4a17ba`)

`modalKnownWorlds_length_le_worldBoundS5 φ₀ b keys hTotal hDistinct hInUniv` -- a **static**
lemma (per the resume task's explicit directive) requiring only `S5LoopInv`'s three birth-key
structural fields on a fixed `(b, keys)` pair, no step-preservation reasoning. Proof: inject each
known world into `(signedSubfmls φ₀).powerset` via a classical choice of its birth key
(`keysTotal`); `keysDistinct` gives injectivity; `keysInUniverse` gives codomain membership; then
`Finset.card_le_card_of_injOn` + `List.toFinset_card_of_nodup` + the pre-existing
`signedSubfmls_powerset_card_le` (`LoopChecking.lean`, reused as-is since `modalWorldBoundS5 φ₀`
is definitionally `modalWorldBoundS4 φ₀`, both `2 ^ (2 * (modalSubfmls φ₀).length)`). Added two
supporting local re-derivations (`modalKnownWorlds_nodup_S5`, `modalKnownWorlds_fold_nodup_S5`)
mirroring the file's existing pattern of re-deriving `FmpMeasure.lean`'s private lemmas locally.

### Phase 4: `bClosure`/`eClosure` -- BLOCKED (investigated, not landed)

Consuming Phase 6's pigeonhole bound to close `bClosure`/`eClosure`'s mint-case obligation (as
the prior handoff recommended) revealed a **genuine gap**: Phase 6 bounds the *count* of known
worlds, but placing a freshly-minted formula (at label `modalNextWorld b`) into `modalUniverseS5
φ₀` needs a bound on the *numeric value* `modalNextWorld b`. Bridging count to value requires an
ADDITIONAL invariant -- known-world labels form a contiguous range `{0, ..., modalMaxWorld b}`
(true for this driver, since worlds are only ever minted at exactly `modalMaxWorld b + 1`, and
blocked steps leave `b` unchanged) -- which is **not currently present anywhere in the codebase**
(confirmed by targeted grep across `FmpMeasure.lean`/`LoopChecking.lean`/`S5Simplification.lean`/
`GenericDriver.lean`; only a one-directional per-element bound,
`modalKnownWorlds_le_modalMaxWorld`, exists). This is a real, provable fact but requires its own
new `S5LoopInv` field and preservation lemma -- scoped in full detail, with a concrete
recommended field statement and per-case proof sketch, in
`handoffs/02_phase4-bclosure-contiguity-gap.md`. **No `sorry` or vacuous placeholder was used**;
`bClosure`/`eClosure` remain unproven `[ ]` tasks in the plan, and Phase 4's header is marked
`[BLOCKED]` accordingly.

## Plan Deviations

1. **`S5LoopInv.keysKnown` (Phase 3, prior dispatch)**: unchanged from before, see round 2 plan
   history.
2. **Phase 4 status this dispatch**: 4 of 6 fields landed and CI-green (`eNodup`, `accFresh`,
   `accKnown`, `outDegEq`); `bClosure`/`eClosure` remain blocked on a newly-identified,
   precisely-scoped missing invariant (contiguous world numbering), documented in handoff 02
   rather than rushed.
3. **Phase 6 landed in full this dispatch**, ahead of Phase 5 (which the plan lists as its
   dependency) -- justified because the resume task explicitly directed establishing the
   pigeonhole bound as a static fact (no step-preservation reasoning needed), independent of
   Phase 5's birth-key preservation proofs.
4. **Phase 7 not attempted** this dispatch (budget consumed by the Phase 4/6 investigation);
   remains independent and available for a future dispatch per the plan's own framing.

## Verification (at final commit `8e4a17ba`)

- `lake build` (full project): 3236/3236 jobs green.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake lint`: 0 new warnings on touched files (1 pre-existing unrelated `unusedArguments` error
  in `PrimeExclusion.lean`, predates this task).
- `lake test`: `CslibTests` suite green.
- `lake shake --add-public --keep-implied --keep-prefix`: 0 new import-minimization suggestions
  for `S5Simplification.lean` (some informational `unusedSectionVars`/style messages appear in
  `lake shake`'s own broader analysis, consistent with many pre-existing declarations throughout
  the codebase already carrying the same messages -- confirmed these are NOT part of `lake
  lint`'s 17-linter error-producing output, which is clean).
- `grep -n sorry Cslib/Logics/Modal/Tableau/S5Simplification.lean`: 0 matches outside a prose
  reference inside an existing doc comment.
- `grep -n '^axiom ' Cslib/Logics/Modal/Tableau/S5Simplification.lean`: 0 matches.

## Continuation Guidance

See `handoffs/02_phase4-bclosure-contiguity-gap.md` for full technical detail. In brief, the next
dispatch should:

1. Add a 12th `S5LoopInv` field capturing world-label contiguity (e.g.
   `worldsContiguous : modalMaxWorld b < (modalKnownWorlds b).length` or the exact equality form),
   and prove it preserved across a `modalStepBranchS5gKeyed` step (blocked case trivial since `b`
   is unchanged; non-blocked non-minting case needs a "append at known labels doesn't grow the
   known-world count" lemma; non-blocked minting case needs "append at `modalNextWorld b` grows
   both `modalMaxWorld` and the known-world count by exactly 1", partly available via
   `modalNextWorld_not_mem_modalKnownWorlds`, currently private in `FmpMeasure.lean` and needing
   a local `_S5` re-derivation).
2. Use the new field + Phase 6's `modalKnownWorlds_length_le_worldBoundS5` (via `omega`) to close
   `bClosure`/`eClosure`'s mint-case obligations, completing Phase 4.
3. Proceed to Phase 5 (birth-key preservation); `keysDistinct` should be the easy field
   (`blockingWorldS5Keyed_none_fresh`, already landed); `keysTotal`/`keysInUniverse` likely reuse
   the same new 12th-field machinery.
4. Phase 7 (soundness bridge) can be attempted independently/in parallel at any point.

No `sorry`, no vacuous definitions, and no re-added rank axiom were introduced at any point this
dispatch.
