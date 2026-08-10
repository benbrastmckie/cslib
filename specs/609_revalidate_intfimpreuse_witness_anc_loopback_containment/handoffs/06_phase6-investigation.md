# Handoff: Phase 6 investigation (no code changes)

**Task**: 609 - Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows.
**Plan**: `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/plans/01_beta-priority-repair.md`
**Phase**: 6 ("Snapshot-free `IReuseContain`, re-threaded through the `key` induction") -- remains `[IN PROGRESS]`.
**This dispatch**: investigation only. Zero `.lean` files were edited. The tree is exactly at the
Phase 5 closing commit `ab3f283e`.

## Why no code landed this dispatch

The full mechanism for Phase 6 was worked out (see the plan's own "Investigation note" under
Phase 6, which is the authoritative, detailed record -- this handoff is a pointer/summary, not a
duplicate). In short:

1. Dropping `IReuseContain`'s snapshot existential requires a new companion invariant
   (`IReuseFrozen`, per-edge `IFrozenBelow (l+1) e b`) threaded through
   `intExpandBranches_openBranch_sat`'s induction, replacing `IReuseContain_mono` at its six
   confirmed use sites.
2. Composing that invariant across MANY go-calls (not just one persistence-fixpoint round) needs
   the ORIGIN branch (at loop-back-record time) held fixed, per Phase 5's already-landed
   `applyAllTImpRules_agrees`/`IFrozenBelow_applyPersistenceFixpoint`.
3. That composition, worked through in full, surfaces a SECOND, previously-unforeseen gap: the
   origin's raw-edge list is smaller than a later go-call's raw-edge list (raw edges only grow, by
   one pair per minted world), and Phase 5's lemmas need `isAccessible` facts stated at a FIXED
   edge list. The already-landed `isAccessible_append_mono` (`Scheme.lean:367`) only gives one
   direction (append never loses reachability); the REVERSE direction (append never gains
   reachability whose target is not the fresh node itself) is not yet proved anywhere in the file,
   and is needed to reconcile the origin's edge list with later, larger ones.

Both gaps have a validated proof sketch in the plan's Investigation note. I chose not to force the
first new lemma (`isAccessible` reverse-direction) through in the time remaining this dispatch:
a first attempt at it started producing a genuinely unresolved sub-case rather than a clean proof,
and forcing it through under time pressure risked landing something sloppy or, worse, a `sorry` --
both prohibited. Better to hand off a precise, validated plan than a half-built lemma.

## Concrete next steps (also recorded in the plan, Investigation note point 5)

In dependency order:
1. `isAccessible_append_eq_of_fresh` (name TBD) -- the reverse-direction lemma. **Do this fully
   from scratch with a clean head**, not by resuming a half-finished attempt; the case split on
   "candidate came from the new edge vs. an old edge" needs care, and the `current = nw` dead-end
   sub-case is the one that wants a genuinely fresh derivation rather than patching.
2. Generalize `applyAllTImpRules_agrees`/`applyPersistenceFixpoint_agrees` (or add a corollary) to
   compose across growing `edges ⊇ edges₀`, using (1).
3. Land `IReuseFrozen` / `IAllReuseFrozen` (3-list zip over `(bs, expSets, lbSets)`, mirroring
   `IAllWorldHist`'s 4-list-zip template at `Scheme.lean:3873`) with append/map_const companions.
4. Thread `IAllReuseFrozen` through the `key` suffices statement of
   `intExpandBranches_openBranch_sat` (`Scheme.lean:7434` as of this dispatch).
5. Replace the six `IReuseContain_mono` use sites (current line numbers in the plan's Investigation
   note -- re-grep before editing, they will have shifted) with the composed freeze argument, and
   extend the `IReuseContain_snoc` call site (case6) to also establish the new edge's `IReuseFrozen`
   witness.
6. Only then restate `IReuseContain` itself to drop the snapshot (small, final step).

## Territory

Unaffected this dispatch (no edits). Task 605 continues to own the `isAccessible`-monotonicity /
`openBranch_countermodel` / `tableau_complete` region at the end of `Scheme.lean`; this task's
future work stays confined to the `intStepBranchPrio` / `intExpandBranches.go` / `IReuseContain`
region, as in every prior dispatch.
