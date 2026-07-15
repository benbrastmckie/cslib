# Implementation Summary: S5 Universal-Rule Termination Machinery (v2 plan, round 2)

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Plan**: `plans/02_s5-termination-machinery.md`
- **Status**: PARTIAL -- Phase 3 (the crux guard redesign) COMPLETED and CI-green; Phase 4
  (generic-field preservation) IN PROGRESS, 1 of 6 fields landed; Phases 5-9 NOT STARTED.
- **Commits**: `4f41f3a4` (Phase 3), `12f32499` (Phase 4 partial)
- **Handoff**: `handoffs/01_phase4-generic-field-preservation.md` (detailed technical handoff
  with proof template, gotchas, and exact remaining obligations)

## Per-Phase Status Ledger

| Phase | Status | Notes |
|-------|--------|-------|
| 1. Frame surface + S5 world bound + universe | COMPLETED (prior dispatch) | commit `66021669` |
| 2. Live-set guard + guarded rule (preserved scaffold) | COMPLETED (prior dispatch) | commit `aa9015d6` |
| 3. Keys-aware guard redesign + extended `S5LoopInv` | **COMPLETED** | commit `4f41f3a4`, this dispatch |
| 4. Generic-field preservation lemmas | **IN PROGRESS (1/6)** | commit `12f32499`, this dispatch |
| 5. Birth-key preservation lemmas | NOT STARTED | gated on Phase 4 |
| 6. Pigeonhole world bound | NOT STARTED | gated on Phase 5; entangled with Phase 4's `bClosure`/`eClosure` (see handoff) |
| 7. Soundness bridge `modalTableauS5_sound` | NOT STARTED | independent of termination chain; not attempted this dispatch |
| 8. Spec-free Hintikka lift + fuel + completeness + decidability | NOT STARTED | highest-risk frontier per plan |
| 9. 5/KB5 validity + completeness | NOT STARTED | gated on Phase 8 |

## What Was Delivered

### Phase 3 (COMPLETED)

`Cslib/Logics/Modal/Tableau/S5Simplification.lean`:

- `blockingWorldS5Keyed φ₀ keys b s φ w` -- the keys-aware minting guard, comparing the
  prospective birth content against the threaded **stored keys** list rather than live relevant
  sets. This is the crux fix superseding the v1 `blockingWorldS5` design.
- `blockingWorldS5Keyed_eq_birthContent`, `blockingWorldS5Keyed_none_fresh` -- the guard's
  contract lemmas; `_none_fresh` directly discharges `keysDistinct`'s new-vs-old case.
- `S5LoopInv` extended from 4 to 11 fields: `bClosure`, `eNodup`, `eClosure`, `accFresh`,
  `accKnown`, `outDegEq` (the six generic fields mirroring `S4LoopInv`, `LoopChecking.lean:1127`)
  plus the four birth-key fields (`keysTotal`, `keyLowerBd`, `keysDistinct`, `keysInUniverse`,
  carried from v1 unchanged) plus one deviation field `keysKnown` (converse of `keysTotal`,
  needed because the keyed guard no longer gets "returned world is known" for free from
  filtering over `modalKnownWorlds b` directly -- see Plan Deviations below).
- `modalStepBranchS5gKeyed` redesigned: computes the block/mint decision itself via the keyed
  guard on the two minting shapes, bypassing `modalApplyOneS5g`'s live-set dispatch there
  entirely. `modalApplyOneS5g` and its Phase 2 agreement lemmas are preserved untouched.

### Phase 4 (IN PROGRESS)

- `hasEdge_addEdge_cases_S5` (private, reusable) -- local re-derivation of edge decomposition
  under `Accessibility.addEdge`.
- `modalStepBranchS5gKeyed_expanded_shape` (private, reusable) -- characterizes the expanded-set
  evolution across all 14 leaf cases of the stepper's dispatch as either `e ++ [sf]` or `e`
  unchanged.
- `modalStepBranchS5g_preserves_eNodup` -- landed sorry-free, the first of six generic-field
  preservation lemmas.

**Central finding**: the existing generic `_gen` preservation wrappers in `FmpMeasure.lean`
(`modalStepBranch_preserves_accTargetsKnown_gen`, `modalStepBranch_knownWorlds_gen`, etc.) all
presuppose a `hFreshLocal`-style dichotomy (acc unchanged, or exactly one edge to a genuinely
fresh world) that the keyed guard's *blocked* case violates (it adds a loop-back edge to an
*existing* known world). So none of the remaining five Phase 4 fields (or the four Phase 5
fields) can be discharged via those wrappers -- each requires direct case analysis on
`modalStepBranchS5gKeyed`'s own three-way dispatch, following the proof template documented in
the handoff. This confirms the plan's own "No template" framing for Phase 4/5 was correct.

## Plan Deviations

1. **`S5LoopInv.keysKnown` (Phase 3)**: an 11th field beyond the plan's stated ten-field mirror
   of `S4LoopInv`. Necessary because the keyed guard filters over `keys` (not
   `modalKnownWorlds b` directly), so it no longer gets "the returned blocked world is known" for
   free the way the v1 live-set guard did. Documented in the field's own docstring and in the
   plan file's Phase 3 task checklist.
2. **`modalStepBranchS5gKeyed`'s non-minting delegation (Phase 3)**: delegates non-minting shapes
   to `modalApplyOneS5` directly rather than routing through `modalApplyOneS5g` (a distinction
   without difference, since `modalApplyOneS5g` reduces to `modalApplyOneS5` there anyway).
   Documented in the plan file.
3. **Phase 4 scope this dispatch**: only 1 of 6 fields landed (`eNodup`); `accFresh`/`accKnown`/
   `outDegEq` assessed tractable but not attempted; `bClosure`/`eClosure` identified as entangled
   with the Phase 6 pigeonhole cardinality argument (see handoff for the exact technical reason
   and recommended resolution order). This is an honest scope reduction, not a design change --
   documented per-task in the plan file's Phase 4 checklist.

## Verification (at final commit `12f32499`)

- `lake build` (full project): 3236/3236 jobs green.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake lint`: 0 new warnings on touched files (1 pre-existing unrelated `unusedArguments` error
  in `PrimeExclusion.lean`, predates this task, per the plan's own testing note).
- `lake test`: `CslibTests` suite green.
- `lake shake --add-public --keep-implied --keep-prefix`: clean on touched files.
- `grep -n sorry Cslib/Logics/Modal/Tableau/S5Simplification.lean`: 0 matches outside a prose
  reference inside an existing doc comment (the Phase 2 obstruction section's description of its
  own counterexample as "sorry-free").
- `grep -n '^axiom ' Cslib/Logics/Modal/Tableau/S5Simplification.lean`: 0 matches.

## Continuation Guidance

See `handoffs/01_phase4-generic-field-preservation.md` for the full technical detail. In brief,
the next dispatch should:

1. Complete Phase 4's remaining five fields (`accFresh`, `accKnown`, `outDegEq` first --
   assessed tractable; `bClosure`/`eClosure` last, after resolving the pigeonhole entanglement
   by proving the cardinality bound as a private static helper, independent of step-preservation
   reasoning, consumed by both `bClosure` and Phase 6's public lemma).
2. Reuse the proof template and gotchas documented in the handoff -- they generalize directly
   (same 3-way-then-14-leaf case split, same `injection`/`rename_i` pattern for the
   contradiction-vs-valid dichotomy).
3. Proceed to Phase 5 (birth-key preservation) once Phase 4 is fully green; `keysDistinct` should
   be the easy field there (directly discharged by `blockingWorldS5Keyed_none_fresh`, already
   landed).
4. Phase 7 (soundness bridge) can be attempted independently/in parallel, since it forks off
   Phase 1 and does not depend on Phases 3-6.

No `sorry`, no vacuous definitions, and no re-added rank axiom were introduced at any point.
