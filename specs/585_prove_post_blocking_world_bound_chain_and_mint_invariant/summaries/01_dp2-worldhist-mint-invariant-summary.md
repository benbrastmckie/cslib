# Implementation Summary: DP-2 World-History Invariant and Mint Residue (Partial)

- **Task**: 585 - prove_post_blocking_world_bound_chain_and_mint_invariant
- **Status**: [PARTIAL] -- 5 of 11 phases complete; DP-2's sorry is NOT yet retired
- **Plan**: `specs/585_prove_post_blocking_world_bound_chain_and_mint_invariant/plans/01_dp2-worldhist-mint-invariant.md`

## Update (this dispatch: Phase 4)

**Phase 4 is now COMPLETED** (previously deferred/NOT STARTED). Added `ILabelBoundStrict b nw :=
∀ sf ∈ b, sf.label < nw` and its full plumbing (`_extendMany`, step-level companions
`intStepBranch_linear_preserves_labelStrict` / `intStepBranch_branch_preserves_labelStrict`
mirroring the existing `ILabelBound`-preservation case splits, `_applyAllTImpRules` /
`_applyPersistenceFixpoint`), plus the 2-list-zip list companion `IAllLabelBoundStrict bs nws`
(narrower than the plan's named 3-list template since `ILabelBoundStrict` has no expanded-set
component) with `_append`/`_map` plumbing. Threaded a new `hLBS` hypothesis onto
`intExpandBranches_openBranch_sat`'s signature and two new hypotheses onto the induction's
`suffices key` chain (positioned last, so every existing argument position is untouched), then
threaded through all ten `intExpandBranches.go.induct` cases, discharging entry at
`openBranch_countermodel` (`0 < 1` for the singleton start state). `lake build` green (full
project, 3311 jobs). Sorry census unchanged (Tableau subtree 4, repo-wide 6 -- correct, this
phase is additive-only). `git diff --stat`: single file (`Scheme.lean`, +309/-12); every
"deletion" is a re-issued argument-list line gaining two trailing names, verified by inspecting
every `-` line in the diff -- no proof content was removed. `IAllConsistent`/`ILabelBound` remain
byte-identical to their pre-phase bodies. Full detail and the added-line-count discussion (309
vs. the plan's ~120-180 estimate, and why the excess is benign) is recorded in the plan file's
Phase 4 section.

**Phases remaining: 6, 7, 8, 9, 10, 11** (unchanged in scope from the original plan; Phase 6's
`IWorldHist` design must incorporate the ancestor-accessibility incremental-threading finding
recorded below and in the plan's Phase 1 section).

## What Was Completed

**Phase 1 (COMPLETED, with a documented deviation)**: `isAccessible` one-hop extension. The
literally-stated lemma shape (fixed `edges`, no append) has a one-unit fuel deficit that cannot
be closed in general; the lemma was specialized to the exact append shape used at every mint
site (`edges ++ [(c, p)]`), which is fuel-exact. Added `isAccessible_go_direct`,
`isAccessible_go_one_hop_ext`, `isAccessible_one_hop_ext` to `Scheme.lean` (additive,
sorry-free).

**Phase 2 (COMPLETED)**: `intFImpReuseWitnessAnc?_none_spec` in `Expansion.lean` (additive,
sorry-free). `intFImpReuseWitnessAnc?` itself is untouched.

**Phase 3 (COMPLETED)**: Added the `hNC` (no-contradiction) hypothesis to
`intExpandBranches_openBranch_sat`'s signature, discharged at its sole call site
(`openBranch_countermodel`) via `S.no_contradiction`. Not yet consumed inside the induction
(that happens in Phase 7).

**Phase 5 (COMPLETED -- GO)**: The go/no-go gate. Proved `intFImp_mint_residue`, the standalone
snapshot-free mint-time residue lemma with all five reuse-check conjunct inputs supplied as
explicit hypotheses (report section 4.2). **This is the single highest-risk step in the entire
route and it succeeds.** The conclusion's free variables contain neither a branch nor an edge
list. Reordered ahead of Phase 4 per the plan's own dependency-wave table (Phases 4 and 5 are
mutually independent, both blocked only by 1-3) since Phase 5 is the highest-value checkpoint to
de-risk before committing to Phase 4's large, self-contained invariant-threading work.

**Phase 4 (COMPLETED, in a later dispatch)**: Strict label bound (`ILabelBoundStrict`), its
2-list companion `IAllLabelBoundStrict`, and `_append`/`_map_const` plumbing, threaded through
all ten cases of `intExpandBranches_openBranch_sat`'s `key` induction. See the "Update (this
dispatch: Phase 4)" section above for the outcome.

**Phases 6-11 (NOT STARTED)**: `IWorldHist` definition and 4-list companion (Phase 6), mint-arm
and non-mint-arm preservation (Phases 7-8), the pigeonhole depth bound (Phase 9), the
path-injection size bound (Phase 10), and the final sorry retirement + call-site rewiring
(Phase 11).

## Verification (as of this dispatch)

- `lake build` (full project): green (3311 jobs).
- Tableau-subtree bare-sorry census: **4** (unchanged; target after Phase 11 is 3).
- Repo-wide bare-sorry census: **6** (unchanged; target after Phase 11 is 5).
- No `sorry`, `admit`, vacuous placeholder, or relocated obligation was introduced at any point.
- `intFImpReuseWitnessAnc?` (`Expansion.lean`) byte-identical to its pre-task state.
- `intCreatedChain_le` untouched (Phase 9 not yet started).
- `IAllConsistent`/`ILabelBound` byte-identical to their pre-Phase-4 bodies (new declarations only).
- Only `Scheme.lean` and `Expansion.lean` were modified across the whole task so far, matching
  the plan's file-scope hypothesis.
- DP-3 (`Intuitionistic/Completeness.lean:129`), DP-4 (`Minimal/Completeness.lean:118`), DP-5
  (`Scheme.lean:669`) untouched.

## Key Finding Worth Recording for the Next Dispatch

While investigating Phase 1's one-hop extension, a genuine subtlety was discovered and is
recorded in the plan's Phase 1 section: **ancestor-accessibility (`isAccessible edges c' p` for
an arbitrary-distance `par`-ancestor `c'` of `p`) cannot be derived post-hoc from a fixed `edges`
snapshot** -- `isAccessible edges x y` always uses fuel exactly `edges.length` for every pair, so
composing multiple hops from already-fixed-fuel facts creates a one-unit-per-hop deficit that
cannot be recovered (fuel can only be grown, never shrunk, via the existing
`isAccessible_go_fuel_mono`). The fix is architectural: ancestor-accessibility must be threaded
as an INCREMENTAL invariant, updated by exactly one hop (via `isAccessible_append_mono` +
`isAccessible_one_hop_ext`) in lockstep with `edges`'s real growth at each mint -- never
recomputed from scratch by induction over a fixed ancestor chain. **This means Phase 6's
`IWorldHist` definition likely needs an additional clause (or an accompanying companion
invariant) tracking per-created-world ancestor-accessibility, beyond the report's literal
(H1)-(H5) clauses**, so that Phase 7's mint arm can discharge (H5)'s `hacc` input by threading
forward rather than re-deriving. This is flagged now so the next dispatch does not re-discover
it from scratch.

## Continuation Pointer

Resume with Phase 6, incorporating the ancestor-accessibility threading note above into
`IWorldHist`'s design before committing to its exact clause list. Phases 7-8 consume Phase 5's
`intFImp_mint_residue` lemma directly at the mint arm (supplying `hacc` from the
incrementally-threaded accessibility invariant, `hmem`/`hsub` from (H3), `hNC` from Phase 3's
already-threaded hypothesis, `hψ`/`hnone`/`hle` from local mint-site facts), and now also have
Phase 4's `ILabelBoundStrict`/`IAllLabelBoundStrict` available to supply `par c < c` (H1) directly
from the threaded strict bound at the mint site, without re-deriving it.

## Plan Deviations

- Phase 1: statement specialized from the fixed-`edges` form to the append form
  (`edges ++ [(c, p)]`), per the fuel-deficit finding above; documented inline in the plan's
  Phase 1 section.
- Phase 5 executed before Phase 4 (both are Wave-2, mutually independent per the plan's own
  dependency table); Phase 4 was not skipped, only reordered, and was completed in this dispatch.
- Phase 4: the plan's "companion... 3-list zip over `bs`, `es`, `nws`" template (`IAllConsistent`'s
  own shape) was narrowed to a 2-list zip over `bs`, `nws` only, since `ILabelBoundStrict` has no
  expanded-set component and a spurious third list would carry no information. Added-line count
  (309) exceeds the ~120-180 estimate; see the plan's Phase 4 section for why this is benign
  (argument threading across ten induction cases, not invariant merging).

## AI Tools Used

This implementation was carried out by Claude Code (Anthropic) under the CSLib
cslib-implementation-agent contract: writing and verifying the new Lean lemmas via `lake build`
and iterative goal-state checking, and drafting this summary and the plan-file phase annotations.
All Lean code was verified to compile via `lake build` during this session.
