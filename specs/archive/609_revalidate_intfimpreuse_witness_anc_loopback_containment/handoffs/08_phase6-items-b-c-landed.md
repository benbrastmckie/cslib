# Handoff: Phase 6, task-list items (b) and (c) landed

**Task**: 609 - Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows.
**Plan**: `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/plans/01_beta-priority-repair.md`
**Phase**: 6 ("Snapshot-free `IReuseContain`, re-threaded through the `key` induction") --
remains `[IN PROGRESS]`.
**This dispatch**: landed real, compiling, sorry-free Lean closing task-list items (b) and (c) in
full. Full CI pipeline green.

## What landed

### Item (b): growing-edges composition

`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`:

- `isAccessible_reconcile_of_worldHist` (private, `:3904`, under a new `### Edge-list
  reconciliation across growth` section at `:3879`): given `IWorldHist`/`IWorldHistCounter`
  witnesses at a SMALLER `edges_small` (`nw_small`) and a LARGER `edges_big` (`nw_big`), with
  `nw_small ≤ nw_big`, `edges_small ⊆ edges_big` (list membership), and a target `w' < nw_small`,
  any `isAccessible edges_big w w' = true` reconciles down to `isAccessible edges_small w w' =
  true`. Proved via `parAncestor`, NOT item (a)'s go-level lemma
  (`isAccessible_go_append_eq_of_fresh`): any `parAncestor`-chain ending at a target `c < nw_small`
  stays entirely inside `[0, c]` (`parAncestor_le`'s descent bound), hence inside the domain where
  the two `IWorldHist` witnesses' `par` functions are FORCED to agree
  (`edges_shape_of_worldHist`'s uniqueness argument, using the `hsub` containment) -- the witness
  round-trips through the smaller `par` and `hWH_small`'s own (H1-acc) clause, at `edges_small`'s
  OWN canonical fuel. This sidesteps the previous dispatch's identified "wrapper-level fuel
  mismatch" gap entirely -- no fuel arithmetic needed.
- `applyAllTImpRules_agrees_grow` (private, `:7464`) and `applyPersistenceFixpoint_agrees_grow`
  (private, `:7589`), under a new `### Growing-edges composition` section (`:7443`): the literal
  growing-edges generalizations of `applyAllTImpRules_agrees`/`applyPersistenceFixpoint_agrees`
  the task list asked for. Identical proof shape to the originals, except the checkpoint facts
  (`hfrz`, `hpp`, `hic`, `hcons`) stay pinned to `edges_small`/a fixed `b`, while the round actually
  computed (`applyAllTImpRules bv edges_big`) runs against the bigger `edges_big`; every `hacc`
  witness the proof extracts is reconciled down to `edges_small` via
  `isAccessible_reconcile_of_worldHist` before being fed to `hpp`; the label-order fact
  (`IWorldHist_isAccessible_lt`) needs no reconciliation and is read off directly at `edges_big`.

**Not yet wired into the induction** -- these are free-standing lemmas, not yet invoked at any of
the six `IReuseContain_mono` use sites. That wiring is item (e)'s job.

### Item (c): `IReuseFrozen`/`IAllReuseFrozen`

`Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`:

- `IFrozenBelow_downward` (right after `IFrozenBelow`'s definition): `w0' ≤ w0 → IFrozenBelow w0 e
  b → IFrozenBelow w0' e b`, the "trivial to add" downward-closure-in-threshold lemma the Phase 6
  investigation note's point 1 named.

`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (right after
`IAllReuseContain_map_const`, `:7741` onward):

- `IReuseFrozen (lbH : IEdges) (e : List (ISF Atom)) (b : IBranch Atom) : Prop := ∀ x l, (x, l) ∈
  lbH → IFrozenBelow (l + 1) e b` -- exactly the Investigation note's point 2 sketch.
- `IReuseFrozen_snoc`: extends `IReuseFrozen` by a newly recorded loop-back edge, given the freeze
  checkpoint directly (mirrors `IReuseContain_snoc`'s shape).
- `IAllReuseFrozen`: the 3-list zip over `(bs, expSets, lbSets)` mirroring `IAllWorldHist`'s
  4-list-zip template (NOT `IAllReuseContain`'s narrower 2-list zip, which lacks the per-branch
  expanded set `e` that `IFrozenBelow` needs).
- `IAllReuseFrozen_append`/`IAllReuseFrozen_map_const`: structural companions mirroring
  `IAllWorldHist_append`/`IAllWorldHist_map_const` exactly.

**Deliberately NOT attempted**: any "`IReuseFrozen` survives branch growth" lemma. Unlike
`IReuseContain_mono` (a one-liner), `IFrozenBelow` is NOT naively monotone under branch growth --
its `∀ sf ∈ b` quantifier makes a BIGGER `b` a STRICTLY STRONGER requirement, not weaker. Genuine
preservation needs the real freeze machinery (`IFrozenBelow_intStepBranchPrio_ge` +
`IFrozenBelow_applyPersistenceFixpoint`/`applyPersistenceFixpoint_agrees_grow`), which is item
(e)'s job. **Do not attempt a cheap `IReuseFrozen_mono` shortcut** -- it is not a one-liner.

All eight new declarations verified individually via `lean_verify`: axioms are exactly
`propext`/`Classical.choice`/`Quot.sound` (the file's existing baseline), zero sorries.

## Verification (full CI pipeline)

- `lake exe cache get`: already warm, no-op.
- `lake build` (full, all 3325 jobs): green. Only pre-existing warnings (unrelated
  `FrameCompleteness.lean` flexible-tactic linter notes, unrelated
  `Minimal/DecisionProcedure.lean` unused-decidable-instance note, the pre-existing baseline
  `sorry` at `Scheme.lean:8963` (shifted from `:8624`), and `Completeness.lean:181`'s pre-existing
  `sorry`).
- `lake exe checkInitImports`: clean.
- `lake lint`: 149 findings, ZERO attributable to `Scheme.lean` or `Expansion.lean` -- confirmed
  via grep for both file names and for all eight new declaration names in the lint output.
- `lake exe lint-style`: clean (no output).
- `lake shake --add-public --keep-implied --keep-prefix`: no import-minimization suggestion for
  either touched file; all suggestions are pre-existing, unrelated files.
- `lake exe mk_all --module`: "No update necessary".
- `lake test`: green (9397 jobs, all `CslibTests/` targets pass).
- Sorry count: 196 -> 196 (unchanged). Axiom count: 26 -> 26 (unchanged). Vacuous-definition grep:
  1 (unchanged, the same pre-existing `Computability/URM/Basic.lean` false positive).

## Stray uncommitted edit found and corrected (recurrence of the same issue as the previous
dispatch)

At dispatch start, the plan file and `specs/state.json` again carried an uncommitted,
unexplained edit marking `### Phase 7: Export augmented-frame positive persistence` as `[IN
PROGRESS]` with no corresponding task-body changes, on top of the previous dispatch's own commit
(`5d92b737`) which had already reverted this same marker once. Reverted back to `[NOT STARTED]`
again. The recurrence (twice now, both times on top of a clean prior commit) suggests some
process outside this task's own dispatches is touching these two files between sessions; flagging
for visibility, not something this dispatch can root-cause or fix.

## Concrete next steps, in dependency order (items (d)-(f) remain)

1. **(d)** Thread `IAllReuseFrozen` through the `key` suffices statement of
   `intExpandBranches_openBranch_sat` (the outer lemma's own `hARC : IAllReuseContain branches
   lbSets` parameter at `:7847`, and the `key` statement itself at `:7863` -- re-grep before
   editing) alongside `IAllReuseContain`.
2. **(e)** Replace the six confirmed `IReuseContain_mono` use sites (current line numbers, as of
   this dispatch -- re-grep before editing): `:7962` (case2), `:8059` (case4), `:8177` (case5),
   `:8307` (case6, alongside the `IReuseContain_snoc` call at `:8388`), `:8565` (case7), `:8735`
   (case8). At each site, wire up `applyAllTImpRules_agrees_grow`/
   `applyPersistenceFixpoint_agrees_grow` (item (b)) composed with `IReuseFrozen`/
   `IAllReuseFrozen` (item (c)) to justify containment survival, instead of the snapshot-based
   `IReuseContain_mono`. This will need, at each site, the actual origin/later `IWorldHist`
   witnesses, the `nw_small ≤ nw_big` fact, and the `edges_small ⊆ edges_big` containment fact --
   raw edges only ever grow by append across the induction (true structurally), but this is not
   yet packaged as its own reusable lemma. Consider landing a small `IAllRawEdges`-append-style
   helper (or just deriving the containment inline at each site from the existing accumulator
   structure) before attempting the six rewrites.
3. **(f)** Only then restate `IReuseContain` (`:7651`) itself to drop the snapshot.

## Territory

Unaffected beyond the additive insertions at `Scheme.lean:3879-3960` (reconciliation lemma),
`Scheme.lean:7443-7625` (growing-edges composition), `Scheme.lean:7741-7815` (`IReuseFrozen`/
`IAllReuseFrozen`), and `Expansion.lean` (right after `IFrozenBelow`'s definition,
`IFrozenBelow_downward`) -- all private lemmas/defs, purely additive, no existing declaration
modified beyond the mechanical line-shift. Task 605 continues to own the `isAccessible`-
monotonicity / `openBranch_countermodel` / `tableau_complete` region at the end of `Scheme.lean`;
this task's work stays confined to the `intStepBranchPrio` / `intExpandBranches.go` / `IReuseContain`
region plus the shared `isAccessible`/`IWorldHist` sections near the top of the file, as in every
prior dispatch.
