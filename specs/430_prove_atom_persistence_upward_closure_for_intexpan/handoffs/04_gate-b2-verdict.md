# Gate B2 Verdict: Beta-Split Refutation Probe

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Phase**: 5 of 14 (plan 06)
- **Status**: COMPLETED
- **Scratch artifact**: `scratch/BetaSplitProbe.lean`, independently compiled via
  `lake env lean` against the real library (`Scheme.lean` imported directly; the REAL,
  already-V4 `applyAllTImpRules`/`applyPersistenceFixpoint`/`intFImpReuseWitnessAnc?` from
  `Expansion.lean` are used verbatim -- no local reimplementation of the persistence/reuse
  logic, only the outer `intExpandBranches.go` worklist loop is recreated locally, since it is
  `private` to `Scheme.lean`, with an added parallel `augEdges` accumulator matching exactly
  how the real `key`-induction proof's ghost witness `augSets`/`augH` evolves). **Zero writes
  to `Cslib/` or `CslibTests/` from this phase** -- confirmed via
  `git status --short Cslib/ CslibTests/` showing only Phase 6's three files (a separate,
  independently-authorized parallel phase; see the Gating contract).

## Method

Per report 05 §4's exact recipe:
1. Construct `φ0` candidates forcing a disjunction under nested implications, so a blocked
   world `w` and its reused ancestor `x` both carry `T(r ∨ s)`.
2. Run the recreated `intExpandBranches`-equivalent loop at generous fuel, tracking BOTH the
   raw edge list and the AUGMENTED edge list (`augEdges`) -- the loop-back-edge-carrying list
   `truthLemma`'s frame is actually installed over, per the plan's Overview and report 05 §1/§4.
3. Decide atom-level upward-closure computationally over `isAccessible augEdges w w'`
   (`upwardClosedCheck`, `Bool`-valued, `#eval`-able -- this reduces to the SAME reachability
   `intAccessPreorder augEdges`'s `≤` computes, since `isAccessible` is already the full
   transitive-closure DFS over its edge list; see `intAccessPreorder_le_of_isAccessible`).
4. Widen across a small family until either a violation is found (REFUTED) or the mechanism is
   confirmed exercised without violation across the family (PASS).

Eight candidates were tested (see `BetaSplitProbe.lean`'s own verdict block for the full
results table): the canonical divergence witness (sanity baseline, confirms reuse fires but has
no disjunction at all -- zero branching events by construction); five hand-built candidates
specifically engineering nested F-implications with `pr ∨ ps` as the antecedent; and two
variants of the canonical witness with `pr ∨ ps` substituted for one or both of its own
recurring antecedent slots.

## Result

**Three candidates genuinely exercise the mechanism** (`phiRS`, `phiRS2`, `phiBeta2`): a real
loop-back edge was recorded (`reuseActuallyFired = true`, i.e. a 2-cycle in the augmented
frame -- confirmed by construction, not merely asserted, since `pr ∨ ps` is literally the
antecedent of the recurring/nested F-implication driving the reuse mechanism in each). In all
three, `upwardClosedCheck` returned `true`: **no atom-level disagreement was found across the
augmented frame**.

The other five candidates (`phiBeta1`, `phiBeta3`, `phiBeta4`, `phiBeta5`, and the disjunction
never firing case) either never triggered reuse at all (too shallow -- confirmed both
empirically, `reuseActuallyFired = false`, and analytically for `phiBeta4`: no OTHER, unrelated
obligation exists for the ancestor-reuse candidate search to reuse against in that
construction, so `intFImpReuseWitnessAnc?` structurally cannot return `some x` there) or also
returned no violation when they did fire.

Per the plan's Phase 5 acceptance criterion -- "confirm a reuse event actually fired and that
both worlds carry the disjunction in the returned branch" before reading any PASS as
meaningful -- **`phiRS`, `phiRS2`, and `phiBeta2` satisfy both conditions**, so this is not an
unexercised-mechanism INCONCLUSIVE result.

## Why the risk is hard to realize (analytical, cross-checked against the empirical results)

`intFImpReuseWitnessAnc?`'s containment conjunct (`hcont`, exported by
`intFImpReuseWitnessAnc?_spec`, `Expansion.lean:321`) is re-evaluated FRESH, over the CURRENT
branch state, at the exact moment each reuse decision is made -- it is not a stale check.
Since `genCopies` (V4, `Expansion.lean:158-182`) copies the ORIGINAL disjunction formula
verbatim to every raw-accessible descendant (not merely whatever atom choice an ancestor's OWN
branching already resolved to), the containment check sees the SAME live disjunction (or its
already-resolved specialization, if resolution has already happened) at both sides whenever it
is evaluated, and refuses reuse (`intFImpReuseWitnessAnc?` returns `none`) if the two sides
disagree at that moment. Constructing an actual counterexample requires the disjunction to
arrive at an already-reuse-linked pair via a genuinely INDEPENDENT path strictly AFTER the
reuse decision is recorded -- several hand constructions aimed exactly at this shape
(`phiBeta4`, `phiBeta5`) did not produce it within this session's fuel/complexity budget, and
the constructions that DID exercise live reuse-with-disjunction did not exhibit it either.

## Verdict: PASS (with residual risk explicitly carried forward)

**Not refuted.** No counterexample was found across the tested family, and the mechanism was
genuinely exercised (not merely attempted) in three of the eight candidates. This is **not** an
exhaustive proof of absence -- an accident of formula construction, or a much deeper
fuel/complexity regime, could in principle still exhibit the beta-split refutation shape. This
residual risk is carried forward explicitly, not swept aside:

- **Phase 9** ("post-reuse closure lemma") is the load-bearing point where this risk would
  surface as an actual proof obstruction if it is real; it retains the license (per the plan)
  to record COLLAPSED and escalate to Phase 10 rather than forcing an unsound shortcut.
- **Phase 11** ("multi-hop composition") is the second load-bearing point, for the case where a
  single recorded loop-back edge is fine in isolation but composition under
  `Relation.ReflTransGen` across several accumulated reuse events breaks down.
- If either phase discovers a genuine obstruction traceable to this exact mechanism, that
  discovery supersedes this PASS and the plan's Rollback/Contingency for a later-phase failure
  applies (stop, record, do not force a result) -- it does NOT retroactively require reopening
  Phase 5, since Phase 5's job (per its own Goal) was to decide whether to gate the build-out at
  all, not to guarantee its ultimate success.

**Proceed to Phase 7** with this residual risk recorded. Per the Gating contract, Phases 7-13
were NOT started before this verdict was recorded.

## Verification state

- `lake env lean scratch/BetaSplitProbe.lean` -- compiles clean (definitions, termination
  proof, and all `#eval` calls). No `Cslib/` writes from this phase.
- `git status --short Cslib/ CslibTests/` -- shows only Phase 6's three files (a separate,
  independently-authorized parallel phase), zero Phase-5-attributable changes.
