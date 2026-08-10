# Handoff: Phase 7 COMPLETE -- augmented-frame positive persistence exported

**Task**: 609 - Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows.
**Plan**: `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/plans/01_beta-priority-repair.md`
**Phase**: 7 ("Export augmented-frame positive persistence") -- now `[COMPLETED]`.

## What this dispatch did

Landed all four Phase 7 tasks in a single green checkpoint (one commit), following the plan's
decompose-and-chain design:

1. **`isAccessible_go_decompose` / `isAccessible_decompose`** (new, generic, `Atom`-independent,
   placed near the other `isAccessible_go_*` lemmas after `isAccessible_one_hop_ext`): decompose
   a single `isAccessible edges w w' = true` fact into `w = w'` or a genuine
   `Relation.ReflTransGen (fun a c => (c, a) ∈ edges) w w'` chain, by structural induction on
   `isAccessible.go`'s own fuel-bounded recursion. This is distinct from (and much cheaper than)
   proving `isAccessible` itself transitive -- the thing `Scheme.lean`'s existing docstring
   (`:250-257`) explains the codebase deliberately avoids -- since `go`'s recursion already IS a
   chain of single edges, one per unfold; no new graph-reachability argument was needed.

2. **`IAugMembers` / `IAllAugMembers`** (new provenance invariant, placed after
   `IAllReuseContain_map_const`): `IAugMembers augH edgesH lbH := ∀ e ∈ augH, e ∈ edgesH ∨
   e ∈ lbH` -- every edge in the augmented list is either a raw parent-child edge (from world
   creation) or a recorded loop-back edge (from the reuse site), since `augH` only ever grows by
   ONE of exactly these two append operations, always in lockstep with `edgesH`'s or `lbH`'s own
   growth. `IAllAugMembers` is the 3-list-zip companion (pure edge-list bookkeeping, no branch
   content, mirroring `IAllWorldHistCounter`'s shape). Two step lemmas
   (`IAugMembers_edges_snoc`/`IAugMembers_lb_snoc`) and the usual `_append`/`_map_const`
   companions were also landed.

3. **Threaded `IAllAugMembers` through all ten `key`-induction cases** in
   `intExpandBranches_openBranch_sat` (case1-case10), mirroring exactly how Phase 6 threaded
   `IAllReuseFrozenOrigin`: two new hypotheses (`hPendingAAM`/`hDoneAAM`) inserted right after the
   ARFO pair in `key`'s `∀`-statement and every case's `intro` line; destructured via
   `cases hpAug`/`cases hpLB` alongside the existing ACC/ARC/ARFO destructuring; propagated
   through every recursive `refine ih (...)` call via `IAllAugMembers_append`/`_map_const`,
   exactly mirroring the existing ARFO-block's positional slot. The sole real "step" proofs are
   at the two edge-growing sites: case6 (reuse, `IAugMembers_lb_snoc`) and case7 (mint,
   `IAugMembers_edges_snoc`); every other case just carries the fact through unchanged.

4. **`IAugMembers_persist`** (the phase's actual payoff, placed right after `IAllAugMembers`'s
   companions): combines `IAugMembers`, `IPosPersistRaw`, `IReuseContain`, and `IWorldsPlanted`
   into the target shape `∀ χ x y, isAccessible augH x y = true → T(χ)@x ∈ b → T(χ)@y ∈ b`, by
   `isAccessible_decompose`-ing the hypothesis into a chain, then tail-peeling exactly as
   `openBranch_rawEdges_upward_closed` does -- at each hop, casing on whether the edge is raw
   (apply `IPosPersistRaw` via `isAccessible_one_step` + `IWorldsPlanted` for the entry-existence
   side condition) or loop-back (apply `IReuseContain` directly, no side condition needed).

5. **`intExpandBranches_openBranch_sat`'s conclusion extended** with a 7th conjunct carrying
   exactly this derived fact (added directly, not as a separate corollary -- see the plan's
   recorded deviation rationale), computed at the sole `.openBranch` leaf (case4) via
   `IAugMembers_persist hAAM_bh_head hpp hARC_bPers hwp`. The signature also gained a new
   `hAAM : IAllAugMembers augSets edgeSets lbSets` parameter; the lemma's one call site
   (`openBranch_rawEdges_upward_closed`) was updated with a trivial proof
   (`by simp [IAllAugMembers, IAugMembers]`, since it calls in with all-empty edge lists) and an
   extra `_hpersAug` binder in its `obtain` (unused there, since that lemma only needs the raw
   conjuncts).

6. **Shape-check `example`** added right after `intExpandBranches_openBranch_sat` (before the
   Parametric Open Branch Countermodel section): destructures the new conjunct and feeds it to
   `truthLemma`'s `hpers` parameter via a bare `exact`, no coercion -- mechanically confirming the
   plan's exact-shape requirement rather than only checking it by inspection (`truthLemma`'s own
   conclusion needed wrapping in `∃ edges, letI : Preorder Nat := intAccessPreorder edges; ...`
   to typecheck at the statement level, since `edges` is not known until the `obtain` inside the
   proof).

## Verification (full pipeline, one commit)

- `lake build` (scoped then full, 3325 jobs): green.
- `lake exe checkInitImports`: clean.
- `lake lint`: zero findings attributable to `Scheme.lean`.
- `lake exe lint-style`: clean.
- `lake shake --add-public --keep-implied --keep-prefix`: no suggestion for `Scheme.lean`.
- `lake exe mk_all --module`: "No update necessary".
- `lake test`: green, 9397 jobs (exit 0, zero `✖` marks).
- Sorry count: 196 -> 196 (unchanged). Axiom count: 26 -> 26 (unchanged). Vacuous-definition grep:
  1 -> 1 (unchanged, pre-existing `Computability/URM/Basic.lean` false positive).
- `intExpandBranches_openBranch_sat` and `openBranch_rawEdges_upward_closed` re-verified via
  `lean_verify`: axioms `{propext, Classical.choice, Quot.sound}`, no `sorryAx`, both times.

## Territory

Confined to: (a) the `isAccessible_go_*` family near the top of `Scheme.lean` (new decomposition
lemmas only, no edits to existing lemmas there), (b) the `IReuseContain`/`IAllReuseContain`
region (new `IAugMembers` block inserted after it, no edits to existing declarations), and
(c) the `intExpandBranches_openBranch_sat`/`key` induction region. Did NOT touch task 605's
`isAccessible`-monotonicity/`openBranch_countermodel`/`tableau_complete` region at the end of
`Scheme.lean` -- its pre-existing `sorry` (line 9596 as of this dispatch's final commit) is
untouched, and its own docstring's frame-adequacy table is unchanged (updating that table's
claims to reflect this phase's new capability is Phase 8's job, not this one's).

## Next steps: Phase 8

Phase 8 ("Discharge `openBranch_countermodel`") is `[NOT STARTED]`, depends on Phase 7 (now
satisfied). Its goal: replace `openBranch_countermodel`'s whole-existential `sorry` with a direct
`truthLemma` instantiation at the augmented frame, supplying `hfimp` from `IFimpAccess` (already
held) and `hpers` from this phase's new conjunct. This phase interacts directly with task 605's
territory (the `hbuc`/`modelBot` upward-closure conjunct) -- read `openBranch_countermodel`'s
current signature first to detect whether 605's conjunct has landed before assuming either shape.
See the plan's Phase 8 section for the full task list and the Scope Hypothesis about 605's patch
shape. This is a fresh phase requiring its own dispatch -- not attempted here.
