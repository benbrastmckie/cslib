# Summary 12: Phase 19a termination-bound re-derivation landed

**Task**: 515 (`s5_universal_rule_termination_unblock_504`)
**Plan**: `plans/07_s5-termination-machinery.md` (v6)
**Phase**: 19a (`Guarded mint arm + termination bound re-derivation`) -- now `[COMPLETED]`
**Commit landed this dispatch**: `2c7abe73` (`task 515 phase 19a.2: land source-split
termination-bound re-derivation`), plan-marker commit `c3d6c608`

## Scope of this dispatch

Resumed from continuation handoff `handoffs/11_phase19a-mint-arm-guard-landed-termination-open.md`.
The mint-arm guard (Phase 19a's first task) was already landed and green (`56a84d07`) -- not
re-touched. This dispatch executed the second (previously unattempted) Phase 19a task: re-deriving
the tag-injection termination bound under the refined "≤1 mint per tag per source-class {root,
non-root}" invariant that the guard requires (per `reports/08_mint-arm-reuse-route-decision.md`).

## What landed

All additive, in `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`:

- **Import**: `public import Cslib.Logics.Modal.Tableau.S5Simplification` (to reuse the
  rule-independent `mintTags`/`S5wTagInv`/tag-membership corollaries verbatim) and
  `import Mathlib.Tactic.Ring` (needed by a `calc`/`ring` step; not previously required in this
  file).
- **`usedTagsFiveNonRoot`/`usedTagsFiveRoot`**: source-split analogues of `usedTags`, each a
  `Finset` filter of the reused `mintTags φ₀` -- non-root witness presence and root-trigger
  presence respectively -- plus their monotonicity lemmas (`usedTagsFiveNonRoot_mono`/
  `usedTagsFiveRoot_mono`).
- **`witnessWorldFive_none_not_mem_usedTagsFiveNonRoot`**: the non-root reuse-miss case, a direct
  analogue of `witnessWorldS5_none_not_mem_usedTags` adapted to `witnessWorldFive`'s root-excluding
  search domain.
- **`diamondPos_root_mem_usedTagsFiveRoot`/`boxNeg_root_mem_usedTagsFiveRoot`**: the
  root-trigger-always-fresh case -- no "unused" precondition needed, since the root-triggered mint
  arm fires unconditionally; the fact is witnessed directly by the trigger's own presence on the
  branch.
- **`FiveWorldInv`**: the source-split world-bound invariant, `modalMaxWorld b ≤
  (usedTagsFiveNonRoot φ₀ b).card + (usedTagsFiveRoot φ₀ b).card`.
- **`two_mul_modalOps_lt_worldBound`**: arithmetic companion to `modalOps_lt_worldBound` showing
  `2 * modalOps φ < modalWorldBound φ` still holds (the larger, still-linear constant Route (a)
  needs).
- **`modalMaxWorld_lt_worldBound_of_FiveWorldInv`**: the final chain, `modalMaxWorld b <
  modalWorldBound φ₀`, matching `outputsSubsetUniverse`'s `hW` hypothesis shape exactly.
- **Module docstring correction**: the pre-guard claim that the whole `S5w*` chain "applies
  unchanged" was stale (true only for `mintTags`/`S5wTagInv`, not for the witness-reuse-specific
  `usedTags`/`S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w`); corrected to describe the
  source-split structures this dispatch adds. Two other stale `witnessWorldS5`-as-shipped-rule
  references (pre-dating the `56a84d07` guard) also corrected to `witnessWorldFive`.

## Scope note (intentional, not a deviation)

This lands the *static* source-split structures and the final arithmetic bound only -- mirroring
`S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w`'s own shape, which likewise take the world-bound
invariant as a hypothesis rather than proving it holds at every reachable branch. The *inductive*
step-preservation proof establishing `FiveWorldInv` holds across the whole fuel-driven expansion
(the source-split analogue of `S5wTagInv_S5wWorldInv_step`) is Phase 19b-scale work, for whatever
call site eventually maintains it across the fuel induction. This matches both the plan's own
checklist wording (which lists the six named declarations to re-derive, not a step-induction) and
the continuation handoff's task breakdown (tasks 1-3, all addressed). `modalApplyOneFive_specCore`
was re-verified unconditionally (untouched by this dispatch); its `outputsSubsetUniverse` field
still takes the world-bound fact as a raw hypothesis parameter, discharged nowhere in this file yet
(per handoff 11's own note, unaffected by this dispatch).

## Verification performed

- `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` (scoped) -- green, sorry-free.
- `lake build` (full project) -- green, 3240/3240 jobs.
- `lake exe checkInitImports` -- exit 0.
- `lake exe lint-style` -- exit 0, no output.
- `lake lint` (full-repo scan) -- zero new warnings attributable to `FiveSimplification.lean`
  (only the two pre-existing baseline info/warning lines at 522/523, unchanged by this dispatch,
  plus the standing repo-wide `PrimeExclusion.lean` baseline error).
- `lake shake --add-public --keep-implied --keep-prefix` -- no import-removal suggestion for
  `FiveSimplification.lean`; exit 1 is the pre-existing repo-wide baseline (unrelated files).
- `lake exe mk_all --module` -- "No update necessary" (no new files).
- `lake test` -- exit 0, full `CslibTests/` suite green.
- `grep -n "sorry\|admit"` on the file -- zero hits.
- Axiom check via `lake env lean` + `#print axioms` on every new declaration
  (`usedTagsFiveNonRoot_mono`, `usedTagsFiveRoot_mono`,
  `witnessWorldFive_none_not_mem_usedTagsFiveNonRoot`, `diamondPos_root_mem_usedTagsFiveRoot`,
  `boxNeg_root_mem_usedTagsFiveRoot`, `two_mul_modalOps_lt_worldBound`,
  `modalMaxWorld_lt_worldBound_of_FiveWorldInv`) -- all report only `[propext, Classical.choice,
  Quot.sound]` (or a subset) -- no `sorryAx`, no new custom axiom.

## Plan Deviations

None. All three sub-tasks from the continuation handoff/task instructions were completed as
specified:
1. Source-split `usedTags`/`S5wTagInv`/`S5wWorldInv`-shaped family of new, additive lemmas --
   landed (`usedTagsFiveNonRoot`/`usedTagsFiveRoot`/`FiveWorldInv`, with `S5wTagInv` itself reused
   verbatim as intended).
2. Source-split analogue of `witnessWorldS5_none_not_mem_usedTags` against `witnessWorldFive`,
   with the extra root-trigger-always-fresh case -- landed as two lemmas
   (`witnessWorldFive_none_not_mem_usedTagsFiveNonRoot` for the non-root case,
   `diamondPos_root_mem_usedTagsFiveRoot`/`boxNeg_root_mem_usedTagsFiveRoot` for the root case).
3. Chain to a `modalMaxWorld_lt_worldBound_of_S5w`-analogue giving `modalMaxWorld b ≤ 2 *
   modalOps φ0` (tightened to `< modalWorldBound φ0`, matching the original's stronger target
   type) -- landed (`modalMaxWorld_lt_worldBound_of_FiveWorldInv`).

Hard constraints honored: worked only in `FiveSimplification.lean` (additive lemmas only); did
not touch any `S5Simplification.lean` declaration's content (only added a `public import` of the
file); zero `sorry`; did not weaken `modalApplyOneFive_specCore`'s statement or `fiveFC`/`kb5FC`'s
definitions; resolved every declaration by name (via `lean_local_search`/`lean_declaration_file`
where checking existing names, and direct source reads for the target file); made a single
sub-milestone commit (`task 515 phase 19a.2`), scoped `git add` to the single touched file; stayed
well within the ~800-line soft ceiling (211 net insertions).

## Files changed

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (additive
  termination-bound section + import + docstring corrections)
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`
  (Phase 19a marked `[COMPLETED]`, second checklist item marked `[x]` with landing notes)

## Next steps

Phase 19a is `[COMPLETED]`. Phase 19b (`modalTableauFive_sound` bespoke assembly) may now begin in
a future dispatch, per the plan's own sequencing (`Depends on: 18`, with 19a now fully closed).
Phase 19b will need to establish (or otherwise discharge) `FiveWorldInv`/`outputsSubsetUniverse`'s
`hW` hypothesis at whatever call site the fuel-induction soundness assembly requires it -- the
inductive step-preservation proof noted as deferred above. Phases 20-23 remain queued behind 19b.
