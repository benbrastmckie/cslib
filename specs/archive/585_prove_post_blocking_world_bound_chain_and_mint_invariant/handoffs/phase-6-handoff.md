# Phase 6 Handoff: IWorldHist definition, counter-redundancy, plumbing, entry case

- **Task**: 585 - prove_post_blocking_world_bound_chain_and_mint_invariant
- **Phase**: 6 of 11 -- [COMPLETED]
- **Plan**: `specs/585_prove_post_blocking_world_bound_chain_and_mint_invariant/plans/01_dp2-worldhist-mint-invariant.md`

## What was done

Added to `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (additive only, +187/-0,
inserted between `intFImp_mint_residue` (Phase 5) and `intFreshMint_preserves_nw` (DP-2's
still-present sorry)):

1. `parAncestor (par : Nat → Nat) (x y : Nat) : Prop` -- reflexive-transitive closure of `par`
   via `Relation.ReflTransGen (fun a b => a = par b)`.
2. `IWorldHist φ0 b _e nw edges : Prop` -- the structural creation-history invariant, report
   section 3.2's (H1)-(H5) PLUS a new (H1-acc) clause:
   `∀ c', parAncestor par c' c → isAccessible edges c' c = true`.
   This is the phase's one substantive design deviation -- see "Deviation" below.
3. `IWorldHist_entry` -- standalone, generalized entry lemma (vacuous at `nw = 1`).
4. `IWorldHistCounter nw edges := nw = edges.length + 1` plus `IWorldHistCounter_entry : rfl`.
5. `IAllWorldHistCounter` (2-list companion over `nws`/`edgeSets`) with `_append`/`_map_const`.
6. `IAllWorldHist` (4-list companion over `bs`/`es`/`nws`/`edgeSets` -- new shape, one list wider
   than any existing companion in the file) with `_append`/`_map_const`.

All six new top-level declarations (`IWorldHist_entry`, `IWorldHistCounter_entry`,
`IAllWorldHistCounter_append`, `IAllWorldHistCounter_map_const`, `IAllWorldHist_append`,
`IAllWorldHist_map_const`) verified sorry-free via a temporary `#print axioms` pass (only
`propext`/`Quot.sound`; removed before this handoff). `lake build` green: scoped (858 jobs) and
full-project (3311 jobs). Sorry census unchanged: Tableau subtree 4, repo-wide 6.

## Deviation: (H1-acc) added to IWorldHist

The report's draft (H1) is bare edge membership `(c, par c) ∈ edges`. That alone cannot supply
Phase 7's mint-arm need for `hacc : isAccessible edges c' p = true` (an input to
`intFImp_mint_residue`, Phase 5) for an ARBITRARY `parAncestor`-ancestor `c'` of the new parent
`p` -- deriving that from a FIXED `edges` snapshot by chaining (H1)'s one-hop memberships hits
exactly the fuel deficit Phase 1 already found and worked around (`isAccessible_one_hop_ext` is
proved only in the append-specialized shape). (H1-acc) fixes this by carrying genuine
`isAccessible` ancestor-accessibility as invariant DATA, so Phase 7 never needs to re-derive it:
old pairs survive `edges`'s growth via `isAccessible_append_mono`; the newly-minted world's
accessibility from every ancestor of its parent follows by composing the parent's
already-established accessibility with `isAccessible_one_hop_ext`.

## Deviation: induction wiring deferred to Phases 7-8

The plan's Phase 6 task list says to "thread both companions through the `key` induction's
hypothesis list," but the SAME phase's Exit Criteria explicitly says: "Because arms are not yet
proved, this phase must NOT assert the invariant as an established conclusion of the induction
... defer the induction wiring to Phases 7-8." Wiring requires supplying the new hypotheses at
every recursive `ih` call across all ten `intExpandBranches.go.induct` cases, which requires the
per-arm preservation proofs that ARE Phases 7-8's content. Per the Exit Criteria's own
resolution, this phase delivered all pieces as complete, sorry-free, standalone declarations and
deferred the wiring. `intExpandBranches_openBranch_sat`'s signature and `key` statement are
UNCHANGED by this phase.

## `hNC` disposition (addressed, not resolved by consumption)

Phase 3's `hNC` hypothesis remains linter-flagged as unreferenced. Concluded (not punted): its
sole consumer is `intFImp_mint_residue`'s `hNC` parameter, reachable only inside the mint arm --
which this phase's Exit Criteria forbids touching. Concrete consumption site: Phase 7.

## Next steps (Phase 7: mint-arm preservation)

1. Add `hWH : IAllWorldHist φ0 branches expandedSets nextWorlds edgeSets` and
   `hWHC : IAllWorldHistCounter nextWorlds edgeSets` to `intExpandBranches_openBranch_sat`'s
   top-level signature, and the corresponding `pending`/`done` pairs to the `suffices key`
   statement's hypothesis chain (positioned last, mirroring Phase 4's `hLBS` threading pattern
   at `Scheme.lean:5259` / `5292-5293`).
2. Discharge entry at the `key branches ...` call (`Scheme.lean` ~5296-5300) using
   `IWorldHist_entry`/`IWorldHistCounter_entry` for `pending`, and the trivial `[]`-case for
   `done` (mirroring `(by simp [IAllLabelBoundStrict])`'s pattern for the other companions).
3. Thread `hWH`/`hWHC` through all ten `intExpandBranches.go.induct` cases as Phase 4 did for
   `hLBS` (extract head/tail, derive the `bPers`-state fact, supply two new trailing arguments to
   every recursive `ih` call).
4. In the mint arm specifically (case with `newEdge = some (nw, l)`, `intFImpReuseWitnessAnc? =
   none`): construct the extended witness functions (override `par`/`obl`/`sfor`/`fire` at
   `c = nw`), discharge (H1) from Phase 4's `ILabelBoundStrict`, (H1-acc) via
   `isAccessible_append_mono` (old pairs) + `isAccessible_one_hop_ext` (new pairs, composed with
   the parent's already-established accessibility), (H2) from `intSubfmls` containment facts
   already available at the call site, (H3) from the planted facts plus
   `applyPersistenceFixpoint_mem_preserved`, (H4) from `intStepBranch_some_exists_fuel`'s
   duplicate-free fact, and (H5) via `intFImp_mint_residue` (Phase 5) supplying `hacc` from
   (H1-acc), `hmem`/`hsub` from (H3), `hNC` from Phase 3's hypothesis.
5. Discharge counter-redundancy on the mint arm (`nw' = nw + 1` and `edges' = edges ++ [newE]`,
   both by exactly one).

## Files touched this phase

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (only)
- `specs/585_prove_post_blocking_world_bound_chain_and_mint_invariant/plans/01_dp2-worldhist-mint-invariant.md`
- `specs/585_prove_post_blocking_world_bound_chain_and_mint_invariant/summaries/01_dp2-worldhist-mint-invariant-summary.md`
