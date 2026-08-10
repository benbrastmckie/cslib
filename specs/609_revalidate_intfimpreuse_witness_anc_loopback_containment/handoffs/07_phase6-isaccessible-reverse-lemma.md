# Handoff: Phase 6, task-list item (a) landed (`isAccessible` reverse-direction lemma)

**Task**: 609 - Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows.
**Plan**: `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/plans/01_beta-priority-repair.md`
**Phase**: 6 ("Snapshot-free `IReuseContain`, re-threaded through the `key` induction") -- remains
`[IN PROGRESS]`.
**This dispatch**: landed real, compiling, sorry-free Lean (the immediately-preceding dispatch was
investigation-only with zero code landed; this one closes that gap for item (a) of the
dependency-ordered task list). Full CI pipeline green.

## What landed

`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`, immediately after
`isAccessible_append_mono`/`intAccessPreorder_mono_append` (now `:386-461`, under a new
`### Reverse-direction append monotonicity (fresh-target case)` section):

- `isAccessible_go_fresh_dead_end` (private, `:404`): from a fresh node `nw` (never a parent-slot
  member of `edges`) with `l ≠ nw`, the extended list `edges ++ [(nw, l)]` has zero outgoing
  candidates from `nw`, at any fuel.
- `isAccessible_go_append_eq_of_fresh` (private, `:433`): the go-level reverse-direction lemma per
  the prior dispatch's sketch -- `isAccessible.go (edges ++ [(nw, l)]) target current fuel = true
  → target ≠ nw → isAccessible.go edges target current fuel = true`, fuel-preserving (same fuel on
  both sides). This is the counterpart to `isAccessible_go_append_mono` (`:316`).

Both are sorry-free and axiom-clean (`lean_verify`: only `propext`/`Quot.sound`). Full pipeline
run this dispatch: `lake exe cache get` (warm, no-op), `lake build` (green, 3325 jobs), `lake exe
checkInitImports` (clean), `lake test` (green), `lake lint` (149 pre-existing library-wide
findings, ZERO in `Scheme.lean` -- confirmed via grep, nothing attributable to this dispatch's
edits), `lake exe lint-style` (clean on `Scheme.lean`), `lake shake --add-public --keep-implied
--keep-prefix` (clean on `Scheme.lean`, only the pre-existing baseline `sorry` warning at
`:8624`), `lake exe mk_all --module` (no update necessary). Sorry count 196 -> 196 (unchanged),
axiom count 26 -> 26 (unchanged), vacuous-definition grep unchanged (1 pre-existing false positive
in `Computability/URM/Basic.lean`, unrelated).

## What did NOT land, and why (a genuinely new, third gap -- not previously identified)

A wrapper-level (non-`.go`) form, `isAccessible (edges ++ [(nw, l)]) w w' = true → w' ≠ nw →
isAccessible edges w w' = true`, was deliberately NOT attempted. It hits a fuel mismatch the
go-level lemma does not: `isAccessible (edges ++ [(nw, l)]) w w'` unfolds to `go
(edges++[(nw,l)]) w' w (edges.length + 1) = true` (fuel = the EXTENDED list's own length). Feeding
this into the go-level lemma above (fuel-preserving) gives `go edges w' w (edges.length + 1) =
true` -- ONE MORE than `isAccessible edges w w'`'s own fuel bound (`edges.length`). The FORWARD
direction (`isAccessible_append_mono`) never hits this because it goes from a SMALLER fuel bound
up to a LARGER one, closing via the already-landed, upward-only `isAccessible_go_fuel_mono`. The
REVERSE direction needs to go DOWN by one unit of fuel on the UNEXTENDED list, which is not valid
in general for a fuel-bounded DFS (more fuel can only preserve or extend reachability, never the
converse) without an extra "fuel `edges.length` already suffices; more fuel changes nothing"
saturation fact.

That saturation fact is very plausibly true here specifically, because `edges` is provably a
genuine forest under this file's OWN invariants (every child has exactly one parent, fixed once at
mint time) -- see the already-landed `IWorldHistCounter` (`nw = edges.length + 1`, `:3527` as of
this dispatch) and `edges_shape_of_worldHist` / `parAncestor_of_isAccessible`
(`:3563-3599`), which already derive the `parAncestor`-vs-`isAccessible` coincidence. But proving
the saturation fact needs that `par`/`nw` context threaded in, which a bare `isAccessible` lemma
about arbitrary `IEdges` does not have. **Do not attempt a generic fuel-saturation lemma about
arbitrary `IEdges` lists** -- reach for `IWorldHistCounter`/`edges_shape_of_worldHist`/
`parAncestor_of_isAccessible` first. Task-list item (b) ("generalize
`applyAllTImpRules_agrees`/`applyPersistenceFixpoint_agrees`... to compose across a GROWING `edges
⊇ edges₀`") already has exactly this context (`nw`, `par`, `IWorldHistCounter`) available at its
call site, so close the wrapper-level equality there, not as a preliminary standalone lemma.

Full analysis recorded in the plan's own Phase 6 "Progress note (this dispatch, item (a)
landed)" section (immediately after the dependency-ordered task list) -- that is the authoritative
record; this handoff is a pointer/summary.

## Concrete next steps, in dependency order (from the plan's task list, items (b)-(f) remain)

1. **(b)** Generalize `applyAllTImpRules_agrees`/`applyPersistenceFixpoint_agrees` (or add a
   corollary) to compose across a GROWING `edges ⊇ edges₀`. This is where the wrapper-level
   `isAccessible` equality for `w' < w0` should actually get closed, using `IWorldHistCounter` +
   `edges_shape_of_worldHist`/`parAncestor_of_isAccessible` to reconcile fuel bounds, plus item
   (a)'s go-level lemma landed this dispatch.
2. **(c)** Land `IReuseFrozen`/`IAllReuseFrozen` (3-list zip over `(bs, expSets, lbSets)`,
   mirroring `IAllWorldHist`'s 4-list-zip template) with append/map_const companion lemmas.
3. **(d)** Thread `IAllReuseFrozen` through the `key` suffices statement of
   `intExpandBranches_openBranch_sat` (`Scheme.lean:7524` as of this dispatch -- re-grep before
   editing) alongside `IAllReuseContain`.
4. **(e)** Replace the six confirmed `IReuseContain_mono` use sites (current line numbers, as of
   this dispatch -- re-grep before editing, they will have shifted again on any further insertion):
   `:7623` (case2), `:7720` (case4), `:7838` (case5), `:7968` (case6, alongside the
   `IReuseContain_snoc` call at `:8049`), `:8226` (case7), `:8396` (case8). Extend
   `IReuseContain_snoc`'s call site to also establish the newly-recorded edge's `IReuseFrozen`
   witness.
5. **(f)** Only then restate `IReuseContain` (`:7395`) itself to drop the snapshot.

## Territory

Unaffected this dispatch beyond the additive insertion at `Scheme.lean:386-461` (private lemmas,
purely additive, no existing declaration modified or renumbered beyond the mechanical line-shift).
Task 605 continues to own the `isAccessible`-monotonicity / `openBranch_countermodel` /
`tableau_complete` region at the end of `Scheme.lean`; this task's work stays confined to the
`intStepBranchPrio` / `intExpandBranches.go` / `IReuseContain` region plus the shared
`isAccessible` append-monotonicity section near the top of the file (lines ~250-475), as in every
prior dispatch.

## Stray uncommitted edit found and corrected

At dispatch start, the plan file and `specs/state.json` carried an uncommitted, unexplained edit
marking `### Phase 7: Export augmented-frame positive persistence` as `[IN PROGRESS]` with no
corresponding task-body changes (Phase 7 depends on Phase 6, which is not done). This was reverted
back to `[NOT STARTED]` as part of this dispatch's plan-file edit, since it was factually
incorrect and unrelated to any actual Phase 7 work.
