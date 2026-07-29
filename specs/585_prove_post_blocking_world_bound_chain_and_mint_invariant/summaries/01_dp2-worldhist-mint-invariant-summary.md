# Implementation Summary: DP-2 World-History Invariant and Mint Residue (Partial)

- **Task**: 585 - prove_post_blocking_world_bound_chain_and_mint_invariant
- **Status**: [PARTIAL] -- 8 of 11 phases complete; DP-2's sorry is NOT yet retired
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Plan**: `specs/585_prove_post_blocking_world_bound_chain_and_mint_invariant/plans/01_dp2-worldhist-mint-invariant.md`

## Update (this dispatch: Phases 7-8, resumed from a broken build)

This dispatch resumed from `handoffs/RESUME-broken-build.md`, written by an operator after a
prior dispatch died mid-edit on API errors, leaving `Scheme.lean` red (25 build errors, +349/-10
uncommitted). The goal was explicitly a green build, not necessarily Phase 7 completion, with
route A (finish the deferred `IAllWorldHist`/`IAllWorldHistCounter` wiring) preferred over route
B (revert the signature change) only if achievable without ending on a red build.

**Route A was chosen and completed successfully.** Three findings, in order of discovery:

1. **The handoff's leading hypothesis for cluster 2 was wrong, but its instinct (one structural
   cause, not eight) was right.** The actual cause: `subst hcn` in the new `IWorldHist_mint`
   lemma (at the `by_cases hcn : c = nwH` / `subst hcn` step) eliminates the `nwH` local
   variable, replacing every occurrence with `c` throughout the context and goal -- so the
   proof's subsequent literal uses of `nwH` (lines ~3393-3419) referenced an identifier that no
   longer existed post-substitution. Fixed by renaming `nwH` to `c` in the post-subst branch,
   plus two small `Or`/append-membership mismatches this exposed (`simp` and
   `List.mem_append.mp` fixes) and one unrelated `rw`-vs-`simp` beta-reduction issue in the
   pre-existing helper `parAncestor_of_extend`. `IWorldHist_mint` (Phase 6's already-complete
   standalone lemma, now touched only for this bug) is sorry-free and clean.
2. **Cluster 1 (the real Phase 7/8 gap) was completed in full**, not deferred. Across
   `intExpandBranches.go.induct`'s ten cases: `case5` (alpha arm) and `case6` (reuse-witness
   arm) needed an `IWorldHist_mono` transfer plus the four missing `ih` call arguments; `case7`
   (the actual MINT arm -- "No reusable ancestor: fresh world creation") needed a full
   `IWorldHist_mint` application, extracting `φ`/`ψ`/`l` from the fired formula via the
   pre-built `intApplyRuleFull_some_edge_inv` helper (already present, with a docstring noting
   it exists exactly for this purpose); `case8` (beta/branching arm) needed the same
   `IWorldHist_mono` transfer via `IAllWorldHist_map_const`. `case6`/`case7`/`case8`'s `intro`
   lines were missing `hWHP hWHD hWHCP hWHCD` bindings entirely, which silently misbound `hgo`
   to the wrong hypothesis type (a second latent bug, distinct from the `nwH` one, caught by
   Lean's type errors rather than by inspection). `case9`/`case10` (terminal contradiction
   cases) needed placeholder bindings only. The `openBranch_countermodel` entry point needed
   `hWH`/`hWHC` witnesses (`IWorldHist_entry`/`IWorldHistCounter_entry`, both from Phase 6) --
   this required pinning `branches`/`expandedSets`/`nextWorlds`/`edgeSets`/`fuels` explicitly
   rather than via `_`, since anonymous-constructor notation cannot elaborate against an
   unresolved metavariable.
3. Two lint warnings (missing `omit [DecidableEq Atom] [Hashable Atom] in` on `IWorldHist_mono`;
   an unused `Function.comp_def` simp argument) were fixed proactively, per the lint-prevention
   contract, even though they are not in PR CI.

**Verification**: full CSLib CI pipeline green -- `lake build` (both scoped, 858 jobs, and
project-wide, 3311 jobs), `lake exe checkInitImports`, `lake lint` (zero warnings in
`Scheme.lean`), `lake exe lint-style`, `lake shake` (no changes needed to this file),
`lake exe mk_all --module` (no update needed), `lake test`. Sorry census unchanged at 4
(`Scheme.lean:725` DP-5, `Scheme.lean:3493` DP-2 -- this task's target, still open as expected
since Phases 9-11 remain -- `Completeness.lean:140` DP-3, `Minimal/Completeness.lean:128` DP-4;
the latter three are owned by other tasks and were not touched). No new axioms, no vacuous
definitions.

Plan phases 7 and 8 are marked `[COMPLETED]` with inline deviation annotations (the actual
case/lemma names used, versus the plan's pre-shift line-number references, which had drifted
after Phase 6's edits).

**Phases remaining: 9, 10, 11** (pigeonhole depth bound from (*), path-injection size bound /
`intWorldHist_nw_le`, retire the DP-2 sorry and rewire the call site).

## Update (this dispatch: Phase 6)

**Phase 6 is now COMPLETED** (previously NOT STARTED). Added the structural creation-history
invariant `IWorldHist φ0 b _e nw edges` (private, additive, sorry-free) and its full supporting
infrastructure: `parAncestor` (reflexive-transitive closure of `par`, via
`Relation.ReflTransGen`), the counter-redundancy predicate `IWorldHistCounter nw edges :=
nw = edges.length + 1` with its entry lemma (`rfl`), the 2-list companion
`IAllWorldHistCounter` with `_append`/`_map_const` plumbing, the 4-list companion `IAllWorldHist`
over `(bs, es, nws, edgeSets)` -- a genuinely new shape, one list wider than any existing
companion in the file -- with its own `_append`/`_map_const` plumbing, and the standalone entry
lemma `IWorldHist_entry` (vacuously true at `nw = 1`, generalized over the branch/expanded-set/
edges arguments). All six new declarations verified sorry-free via a temporary `#print axioms`
pass (only `propext`/`Quot.sound`; the temporary lines were removed before this commit). `lake
build` green, both scoped (858 jobs) and full-project (3311 jobs). `git diff --stat`: single file
(`Scheme.lean`, +187/-0), purely additive. Sorry census unchanged (Tableau subtree 4, repo-wide
6 -- correct, this phase is additive-only).

**Design deviation, resolving the Phase 1 finding flagged in the previous dispatch's summary**:
`IWorldHist` gained an additional clause (H1-acc) beyond the report's literal (H1)-(H5):
`∀ c', parAncestor par c' c → isAccessible edges c' c = true`, carrying genuine
ancestor-accessibility as invariant DATA rather than as a value the mint-arm proof would need to
re-derive post-hoc from a fixed `edges` snapshot (which Phase 1 showed has a provable one-unit
fuel deficit). This clause is additive to the report's draft; nothing in (H1)-(H5) was removed
or weakened. It is designed so Phase 7's mint arm can discharge it mechanically: old
ancestor-accessibility pairs survive `edges`'s growth via `isAccessible_append_mono`, and the
newly-minted world's accessibility from every ancestor of its parent follows by composing the
parent's already-established accessibility with `isAccessible_one_hop_ext`.

**`hNC` disposition**: Phase 3's `hNC` hypothesis remains linter-flagged as unreferenced, exactly
as Phase 3 itself predicted. This phase concluded (rather than punting) that `hNC` is genuinely
needed, not dead: its sole consumer is `intFImp_mint_residue`'s `hNC` parameter (Phase 5), reachable
only from inside the mint arm of `intExpandBranches.go`'s recursion -- code this phase's own Exit
Criteria explicitly forbid touching. See the plan's Phase 6 section for the full reasoning.

**Task-list vs. Exit-Criteria tension**: the plan's Phase 6 task list asks to "thread both
companions through the `key` induction's hypothesis list," but this phase's own Exit Criteria
(the authoritative acceptance gate) explicitly prohibits asserting the invariant as an established
conclusion of the induction before the arms are proved, and explicitly sanctions deferring
"the induction wiring to Phases 7-8" when intermediate scaffolding is unavoidable. Wiring new
hypotheses into `key`'s statement requires supplying them at every recursive `ih` call across all
ten `intExpandBranches.go.induct` cases, which requires the per-arm preservation proofs that ARE
Phases 7-8's entire content. This phase therefore built all pieces as complete, sorry-free,
standalone declarations and deferred the wiring, per the Exit Criteria's own resolution; the
checklist item is marked with an inline deviation annotation in the plan file rather than silently
left unticked.

**Phases remaining: 7, 8, 9, 10, 11** (unchanged in scope from the original plan).

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

**Phase 6 (COMPLETED, this dispatch)**: `IWorldHist` structural invariant, `parAncestor`, the
counter-redundancy companion, the 4-list companion `IAllWorldHist`, all plumbing, and the
standalone entry lemma. See the "Update (this dispatch: Phase 6)" section above for the outcome
and the (H1-acc) design deviation.

**Phases 7-11 (NOT STARTED)**: mint-arm and non-mint-arm preservation of `IWorldHist` and the
counter-redundancy invariant, wiring both into `intExpandBranches_openBranch_sat`'s signature and
`key` induction (Phases 7-8), the pigeonhole depth bound (Phase 9), the path-injection size bound
(Phase 10), and the final sorry retirement + call-site rewiring (Phase 11).

## Verification (as of this dispatch)

- `lake build` (full project): green (3311 jobs).
- Tableau-subtree bare-sorry census: **4** (unchanged; target after Phase 11 is 3).
- Repo-wide bare-sorry census: **6** (unchanged; target after Phase 11 is 5).
- No `sorry`, `admit`, vacuous placeholder, or relocated obligation was introduced at any point.
- `intFImpReuseWitnessAnc?` (`Expansion.lean`) byte-identical to its pre-task state.
- `intCreatedChain_le` untouched (Phase 9 not yet started).
- `IAllConsistent`/`ILabelBound` byte-identical to their pre-Phase-4 bodies (new declarations only).
- `IWorldHist`, `parAncestor`, `IWorldHistCounter`, `IAllWorldHistCounter`, `IAllWorldHist`, and
  their plumbing all verified sorry-free by a temporary (removed) `#print axioms` pass.
- Only `Scheme.lean` and `Expansion.lean` were modified across the whole task so far, matching
  the plan's file-scope hypothesis.
- DP-3 (`Intuitionistic/Completeness.lean:129`), DP-4 (`Minimal/Completeness.lean:118`), DP-5
  (`Scheme.lean:669`) untouched.

## Key Finding, Now Resolved in Phase 6

The previous dispatch's summary flagged a genuine subtlety discovered while investigating Phase
1's one-hop extension: **ancestor-accessibility (`isAccessible edges c' p` for an
arbitrary-distance `par`-ancestor `c'` of `p`) cannot be derived post-hoc from a fixed `edges`
snapshot** (a provable one-unit-per-hop fuel deficit). Phase 6 resolves this by adding clause
(H1-acc) directly to `IWorldHist`, carrying genuine ancestor-accessibility as invariant DATA,
incrementally maintainable via `isAccessible_append_mono` + `isAccessible_one_hop_ext`. See the
"Update (this dispatch: Phase 6)" section above for the full design and the plan's Phase 6
section for the complete deviation record.

## Continuation Pointer

Resume with Phase 7 (mint-arm preservation of `IWorldHist` and the counter-redundancy invariant).
This requires wiring `IAllWorldHist`/`IAllWorldHistCounter` into `intExpandBranches_openBranch_sat`'s
signature and `key` induction statement (deferred by Phase 6, per its own Exit Criteria), then
discharging the mint arm's five `IWorldHist` clauses plus counter-redundancy. Phase 7 consumes
Phase 5's `intFImp_mint_residue` lemma directly at the mint arm (supplying `hacc` from the
newly-added (H1-acc) clause -- now genuinely available as an inductive hypothesis rather than
needing re-derivation, `hmem`/`hsub` from (H3), `hNC` from Phase 3's already-threaded hypothesis,
`hψ`/`hnone`/`hle` from local mint-site facts), and has Phase 4's `ILabelBoundStrict`/
`IAllLabelBoundStrict` available to supply `par c < c` (H1) directly from the threaded strict
bound at the mint site, without re-deriving it. (H4) sibling uniqueness should come from
`intStepBranch_some_exists_fuel`'s duplicate-free fact per the plan's Phase 7 task list.

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
- Phase 6: `IWorldHist` gained an additional clause (H1-acc, ancestor-accessibility as invariant
  data) beyond the report's literal (H1)-(H5), per the Phase 1 finding; see the plan's Phase 6
  section for the full design rationale. The final task-list item ("thread both companions
  through the `key` induction's hypothesis list") was deferred to Phases 7-8, per this phase's
  own Exit Criteria, which explicitly forbids wiring the induction before the arms are proved;
  all pieces were instead delivered as complete, sorry-free, standalone declarations.

## AI Tools Used

This implementation was carried out by Claude Code (Anthropic) under the CSLib
cslib-implementation-agent contract: writing and verifying the new Lean lemmas via `lake build`
and iterative goal-state checking, and drafting this summary and the plan-file phase annotations.
All Lean code was verified to compile via `lake build` during this session.
