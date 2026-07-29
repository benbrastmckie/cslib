# Phase 5 Handoff: Investigation Findings and Partial Progress

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Phase**: 5 of 8
- **Status**: PARTIAL (not BLOCKED — Gate B's PASS verdict stands; the remaining gap is
  buildable but genuinely large, consistent with the plan's own sizing warning)
- **Prior state**: Phases 1-4 complete and committed (`e52f2624`, `611e8f9d`, `8f504c77`).
  Phases 6-8 remain `[NOT STARTED]`, unchanged — they depend on Phase 5's export, which this
  dispatch did not complete.

## What this dispatch did

No `Cslib/` writes were made for Phase 5 — everything below is investigation. The tree remains
exactly as Phase 4 left it (full `lake build` green, sorry count 5, all in the same locations as
recorded in the Phase 4 commit).

## Finding 1 (new, useful, de-risks the remaining scope): the RAW-edge terminal fact is cheap

The plan's Phase 5 draft (written before Phase 4 existed) assumed a brand-new parallel-list
invariant needed threading through all of `intExpandBranches.go`'s cases, mirroring the full
`IAllWorldHist`/`IAllAccessConsistent` build-out. **This is not necessary for the raw-edge half
of the problem.** Concretely:

- `IAllFuel φ0 bs es fuels` (`Scheme.lean`, already landed) gives, per branch,
  `intWork (intUniverseExt φ0) b e < f`, i.e.
  `(intUniverseExt φ0).countP (fun sf => !(b.any (· == sf))) + (intUniverseExt φ0).countP (fun sf
  => !(e.any (· == sf))) < f`. Since both summands are non-negative, this directly gives
  `(intUniverseExt φ0).countP (fun sf => !(b.any (· == sf))) ≤ f` (with room to spare) —
  **exactly** the `hfuel` premise `applyPersistenceFixpoint_genuine_of_count_le_fuel` (Phase 4)
  needs, using the SAME fuel `f` that `applyPersistenceFixpoint` is actually called with in
  `intExpandBranches.go`'s definition (`let bPers := applyPersistenceFixpoint b edges f`).
- `IAllUniv φ0 bs` (already landed) supplies the `hb` premise the same lemma needs.
- Both `IAllUniv` and `IAllFuel` are ALREADY threaded as hypotheses through the entire `key`
  induction inside `intExpandBranches_openBranch_sat` (see its signature, `hUniv`/`hFuel`
  parameters, and the per-case specializations `hUnivP_head`/`hFuel_bh_eH` etc. visible at every
  case, e.g. lines 6809-6827 in the reuse-case arm).
- **Consequence**: at the one substantive terminal return site (`intStepBranch bPers e nw =
  none`, i.e. the branch is genuinely saturated and returned as the open countermodel), the facts
  already in scope (`hUnivP_head`/`hFuelP`-derived, specialized to the head branch and its fuel)
  are already sufficient to invoke `applyPersistenceFixpoint_genuine_of_count_le_fuel` and then
  `applyAllTImpRules_copy_complete_of_fixpoint` (Phase 4, both landed sorry-free) to get: **for
  `T(χ)@w ∈ b` and `w'` raw-accessible from `w` with some existing entry on `b`, `T(χ)@w' ∈ b`.**
  No new parallel-list invariant is needed for this half of the goal.
- The other return sites (`f = 0` and `intStepBranch`'s `.notApplicable` result) are already
  discharged by contradiction in the existing proof (`intWork < 0` is absurd;
  `intStepBranch_result_ne_notApplicable` rules out the other), per the `IAllFuel` docstring's own
  note ("Supplies the fuel-0 discharge", `Scheme.lean:4528`) — so they need no new work either.

**This finding should NOT be re-derived from scratch by a continuation** — it substantially
narrows what Phase 5 actually needs to build.

## Finding 2 (confirms Gate B's own conclusion independently): the AUGMENTED-edge case is the
genuine remaining gap, and it is NOT merely a transfer-of-already-known-facts problem

The plan's goal (Overview) is persistence along `intAccessPreorder augEdges` — the AUGMENTED edge
list `truthLemma` actually installs (`Scheme.lean` conclusion witness, threaded as `pendingAug`/
`doneAug`/`hACC : IAllAccessConsistent` alongside the induction, separate from the raw `edgeSets`
list). The augmented list is the raw edges plus loop-back edges added exactly once per ancestor
reuse: in the reuse arm of `intExpandBranches.go`'s functional-induction proof (`Scheme.lean`,
the case handling `intFImpReuseWitnessAnc? bPers edges newForms newE = some x`), the augmented
list for that branch is extended via `doneAug ++ [augH ++ [(x, l)]] ++ ...` where `l = newE.2`
(the would-be new world's source) — i.e. exactly one new pair `(x, l)` per reuse event.

At that insertion site, two facts are already established and consumed immediately (not
exported): `houtPhi : bPers.any (fun y => y.sign==.pos && y.formula==φ && y.label==x) = true`
(the antecedent `φ` of the CURRENT firing implication is forced at `x`) and `hcont` (from
`intFImpReuseWitnessAnc?_spec`, `Expansion.lean:321-339`): **every formula in `newForms`'s
positive projection is already contained in `posFormulasAt bPers x`** — i.e. every element of
`Sfor(l)` (the would-be new world's forced set) is already forced at `x`, AT REUSE TIME.

**Confirmed by fresh derivation (matches Gate B's own verdict, not merely re-asserting it):**
this containment fact does NOT, by itself, give the general invariant Phase 5 needs, for two
independent reasons:

1. **Scope**: `hcont` only covers the SPECIFIC formulas in `Sfor(l)` known at the moment of the
   reuse decision. The exported invariant must hold for the FINAL branch and for ANY positive
   formula, including ones that arrive at `x` (or that a copy channel would otherwise deliver to
   `l`) AFTER the reuse decision was made. `hcont`'s containment does trivially survive to the
   final branch for those specific formulas (ordinary branch-append monotonicity, already a
   ubiquitous pattern in this file — e.g. `IWorldHist_mono`, `hmemP` — this part is NOT hard), but
   that is not the same as a general persistence guarantee at `l` for formulas arriving later.
2. **The copy channel itself only ever propagates along RAW edges**: `applyAllTImpRules`'s
   `genCopies` (`Expansion.lean`, Phase 3) computes `accessibleWorlds` via
   `isAccessible edges sf.label ·` using the per-branch RAW `edges` parameter, never the
   augmented list. So even granting persistence at `x` for a formula that arrives after the
   reuse event, nothing in the current algorithm ever copies it across the loop-back edge to
   `l`. This is precisely **F3** from the plan's Research Integration section ("the copy channel
   filters on raw edges and is strictly weaker... the fix must be at the invariant level"), now
   confirmed by direct inspection of `genCopies`'s own definition rather than by citation alone.

This matches Gate B's own prototype conclusion exactly: the "ancestor sub-case" (closing
persistence at `x` from an arbitrary later-arriving source) is a genuine open gap, not a
notational inconvenience, and it needs `T(χ)`'s own **origin** world traced back far enough to
be raw-accessible to `x` directly — i.e. a provenance argument in the shape of `IWorldHist`'s
existing `par`/`obl`/`fire`/`sfor` witness functions (`Scheme.lean:3213-3243`), generalized from
"the specific mint-time reuse-residue set" to "every positive formula's point of origin",
repurposed rather than invented fresh (per Gate B's own recommendation, which this investigation
does not overturn — it independently re-derives the same conclusion from the live code, which is
the strongest form of confirmation available).

## Why this dispatch stops here rather than attempting the origin-tracing build-out

Building the origin-tracing extension is a genuine, sizeable engineering task — comparable in
scope to `IWorldHist` itself, which took multiple dedicated phases (`intWorldHist_chain_le`'s
pigeonhole bound, `pathOf`/`pathOf_injOn` path-encoding injectivity, `intWorldHist_nw_le`'s
post-blocking world bound, and the DP-2 retirement) to land soundly. Attempting to compress that
scope into the remainder of a single dispatch risks either an unsound argument or a forced
shortcut (a vacuous placeholder or a weakened statement), both of which are explicitly prohibited.
Per the Escalation Protocol, the correct action is to stop, document precisely, and hand off —
not to force a result.

## Concrete continuation plan for the next dispatch

1. **Do not re-litigate Finding 1.** The raw-edge terminal fact composes directly from
   `IAllUniv`/`IAllFuel` (already threaded) plus `applyAllTImpRules_copy_complete_of_fixpoint`
   (Phase 4, landed). This can be added to `intExpandBranches_openBranch_sat`'s conclusion as a
   RAW-edge conjunct cheaply, if useful as a stepping stone — but by itself it does not unblock
   Phase 6/7, which need the AUGMENTED-edge version specifically (per the plan's Overview).
2. **The one genuinely open problem**: prove a one-step transfer lemma across a SINGLE recorded
   loop-back edge `(x, l)` — for `T(χ)@l' ∈ b` reachable in some sense through `(x,l)`, establish
   `T(χ)@x ∈ b`-style persistence generally, not just for `Sfor(l)`'s reuse-time snapshot. The
   natural route (per Gate B and confirmed here): extend `IWorldHist`'s witness functions (or a
   sibling invariant threaded alongside them, mirroring `IAllAccessConsistent`'s
   companion-not-merged pattern relative to `IAllConsistent`) to record, for every positive
   formula's presence on the branch, a traceable origin world, then show that origin is always
   raw-accessible to any `x` a loop-back edge points from.
3. **Re-confirm the Phase 2 Scope Hypothesis explicitly**: does the single-hop transfer lemma
   compose under `Relation.ReflTransGen` when MULTIPLE loop-back edges are in play (a branch can
   accumulate more than one reuse event)? Gate B's verdict did not explicitly re-confirm this;
   it is still open and should be checked before assuming a single-hop proof generalizes.
4. Only after 2-3 are resolved does exporting `IPosPersist edges b` in
   `intExpandBranches_openBranch_sat`'s conclusion (extending the existential from `∃ edges,
   IBranchSaturation Atom b ∧ IFimpAccess edges b` to also carry the persistence conjunct) become
   a mechanical step — the intermediate (non-terminal) cases of the `key` induction delegate to
   `ih` polymorphically and do not need individual attention; only the terminal return sites do.

## Verification state (unchanged from Phase 4's commit)

- `lake build` (full project): green.
- Bare sorry count: 5 (DP-3 `Completeness.lean:140`, DP-4 `Minimal/Completeness.lean:128`, DP-5
  `Scheme.lean:727`, plus two unrelated sorries outside this task's scope). DP-2 remains retired
  (task 585), untouched.
- No `Cslib/` or `CslibTests/` writes this dispatch; `git status --short Cslib/ CslibTests/` is
  empty.
