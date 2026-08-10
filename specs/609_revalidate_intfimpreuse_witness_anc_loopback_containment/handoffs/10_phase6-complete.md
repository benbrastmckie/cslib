# Handoff: Phase 6 COMPLETE -- IReuseContain restated bare-form, all six sites wired

**Task**: 609 - Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows.
**Plan**: `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/plans/01_beta-priority-repair.md`
**Phase**: 6 ("Snapshot-free `IReuseContain`, re-threaded through the `key` induction") -- now
`[COMPLETED]`.

## What this dispatch did

Directed to attempt the six-site wiring FIRST rather than survey for a fifth round of
scaffolding (four prior dispatches had each found a new prerequisite and stopped without
attempting the wiring itself). This dispatch did attempt it, in three concrete steps, and
closed the phase in full across two commits:

### Commit 1 (`237cfcc4`): closed the fourth gap

`intStepBranchPrio_newEdge_frozen` (new, `Expansion.lean`, right after
`intStepBranchPrioFirstPass_none_frozen`): the "record-time checkpoint"
`IReuseFrozenOrigin_snoc`'s own docstring named (`IFrozenBelow nextWorld expanded b`, available
whenever `intStepBranchPrio` actually plants a new edge) had never been landed as an actual
lemma -- only claimed in a docstring. Closed via a three-lemma chain:
`intApplyRuleFull_not_worldCreating_newEdge_none` (a non-world-creating rule never plants an
edge) -> `intStepBranchPrioFirstPass_linearResult_newEdge_none` (the first pass, which only ever
selects non-world-creating formulas, inherits the same fact) -> `intStepBranchPrio_newEdge_firstPass_none`
(so if the OVERALL step plants an edge, the first pass must have returned `none`, i.e. `intStepBranchPrio`
reached its `intStepBranch` fallback) -> `intStepBranchPrio_newEdge_frozen` (compose with
`intStepBranchPrioFirstPass_none_frozen`).

### Commit 2 (`21a2e460`): item (d), threaded `IAllReuseFrozenOrigin` through `key`

Added `hARFO : IAllReuseFrozenOrigin` as a parameter to `intExpandBranches_openBranch_sat` and to
`key`'s own hypothesis chain (mirroring `hARC`'s existing threading exactly). All 10 induction
cases updated; cases 2, 5, 6, 7, 8 derive and forward the advanced witness via
`IReuseFrozenOrigin_persist`/`_extendMany`/`_snoc`. Two new small lemmas discovered while
attempting the wiring (not pre-planned): `IReuseFrozenOrigin_labelBound` and
`IReuseFrozenOrigin_widen` (monotonicity of `IReuseFrozenOrigin` in its own `e`/`edges`/`nw`
parameters -- needed because the induction's parallel `pendingExp`/`pendingEdges`/`pendingNW`
lists grow at every alpha/beta/mint step). Committed as its own green checkpoint before
attempting item (e), deliberately, per the commit-per-green-substep mandate.

### Commit 3 (`97796a79`): items (e) and (f), closing the phase

Attempting item (e) surfaced a FIFTH gap: `IReuseFrozenOrigin` as landed did not store the
origin's own containment fact, so it could propagate a freeze bound but not actually derive
`IReuseContain`. Fix: one more existential conjunct on `IReuseFrozenOrigin` -- the origin's own
`∀χ, T(χ)@l∈b_o → T(χ)@x∈b_o`, planted once at `IReuseFrozenOrigin_snoc`'s record time (now
taking a `hcontGen`-shaped parameter) and carried unchanged by `_persist`/`_extendMany`/`_widen`
(none of which touch `b_o`). This unlocked one new corollary, `IReuseFrozenOrigin_reuseContain`,
which derives bare `IReuseContain` uniformly from any `IReuseFrozenOrigin` witness -- collapsing
the plan's anticipated six bespoke "already-present vs. newly-arrived" case-split proofs into one
substitution per site. This is a genuine, favorable simplification over the plan's original
decomposition, found only by attempting the wiring.

`IReuseContain` restated to the plan's target bare form; `IReuseContain_mono` removed
(unprovable in general under bare semantics); `IReuseContain_snoc` removed (subsumed by the new
corollary). All six former use sites (cases 2, 4, 5, 6, 7, 8) now read
`IReuseFrozenOrigin_reuseContain hARFO_*`.

## Verification (both commits, full pipeline each time)

- `lake build` (scoped then full, 3325 jobs): green.
- `lake exe checkInitImports`: clean.
- `lake lint`: zero findings attributable to `Scheme.lean`/`Expansion.lean`.
- `lake exe lint-style`: clean.
- `lake shake --add-public --keep-implied --keep-prefix`: no suggestion for either file.
- `lake exe mk_all --module`: "No update necessary".
- `lake test`: green, 9397 jobs, run in the foreground each time (not backgrounded).
- Sorry count: 196 -> 196 (unchanged). Axiom count: 26 -> 26 (unchanged). Vacuous-definition
  grep: 1 -> 1 (unchanged, pre-existing `Computability/URM/Basic.lean` false positive).
- `intExpandBranches_openBranch_sat` re-verified via `lean_verify` after both commits: axioms
  `{propext, Classical.choice, Quot.sound}`, no `sorryAx`. (One intermediate check produced a
  stale `sorryAx` reading from a mid-edit LSP cache state; a fresh `lake build` + re-check
  resolved to clean -- recorded here so a future dispatch does not chase a phantom regression.)

## Territory

Confined to the `intStepBranchPrio`/`intExpandBranches.go`/`IReuseContain`/`IReuseFrozenOrigin`
region and the shared `isAccessible`/`IWorldHist` sections near the top of `Scheme.lean`, plus
`Expansion.lean`'s freeze-precondition section. Did not touch task 605's
`isAccessible`-monotonicity/`openBranch_countermodel`/`tableau_complete` region at the end of
`Scheme.lean` (its own pre-existing `sorry` at line 9332, current numbering, is untouched).

## Next steps: Phase 7

Phase 7 ("Export augmented-frame positive persistence") is `[NOT STARTED]`, depends on Phase 6
(now satisfied). Its goal: decompose augmented-frame persistence into raw-edge persistence
(`IPosPersistRaw`, already sorry-free) plus the loop-back edges (the now-bare `IReuseContain`
this phase landed), chain along `ReflTransGen`, and extend
`intExpandBranches_openBranch_sat`'s conclusion (or a corollary) with the derived persistence
fact matching `truthLemma`'s `hpers` parameter shape. See the plan's Phase 7 section for the
full task list. This is a fresh phase requiring its own dispatch -- not attempted here.
