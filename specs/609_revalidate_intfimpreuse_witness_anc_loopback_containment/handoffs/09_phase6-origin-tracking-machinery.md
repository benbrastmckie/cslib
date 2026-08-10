# Handoff: Phase 6, origin-tracking freeze machinery landed (a third gap found and closed)

**Task**: 609 - Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows.
**Plan**: `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/plans/01_beta-priority-repair.md`
**Phase**: 6 ("Snapshot-free `IReuseContain`, re-threaded through the `key` induction") --
remains `[IN PROGRESS]`.
**This dispatch**: was asked to close task-list items (d)-(f) (thread `IAllReuseFrozen` into
`key`, rewire the six `IReuseContain_mono` use sites, restate `IReuseContain`). Instead found
that item (c)'s landed `IReuseFrozen`/`IAllReuseFrozen` cannot actually support the
round-to-round preservation items (d)-(f) need, diagnosed why, and closed the gap at the design
level with new, real, compiling, sorry-free machinery. Items (d)-(f) as originally scoped remain
open, but the next dispatch should find the six-site wiring far more mechanical than before.

## The gap found

`IReuseFrozen lbH e b := ∀ x l, (x,l) ∈ lbH → IFrozenBelow (l+1) e b` states `IFrozenBelow`
about the CURRENT `(e, b)` directly. This is provable at the EXACT round a loop-back edge
`(x, l)` is recorded (via `intStepBranchPrioFirstPass_none_frozen`), but is NOT re-derivable at
any LATER round: doing so needs `IFrozenBelow_applyPersistenceFixpoint`'s own
`hpp : IPosPersistRaw edges b` hypothesis about that round's PRE-persistence branch (`bh`, not
`bPers`) -- checked directly against that lemma's signature (Phase 5 section,
`Scheme.lean` ~7300s as of this dispatch) -- and `IPosPersistRaw` about a pre-persistence `bh`
does not hold in general (only `applyPersistenceFixpoint_copy_complete`-style derivation about
the POST-persistence output does). This is the exact same asymmetry the Phase 6 investigation
note's point 3 already diagnosed for `IReuseContain`'s own transport -- it turns out to apply
identically to `IReuseFrozen`'s own round-to-round propagation, which is why the previous
dispatch's "do not attempt a cheap `IReuseFrozen_mono` shortcut -- it is not a one-liner" warning
was pointing at something deeper than a missing lemma.

## The fix landed: origin-tracking

`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`, right after
`IAllReuseFrozen_map_const` (`:7813` onward as of this dispatch), under a new
`### Origin-tracked reuse-time freeze witness` section:

- **`IReuseFrozenOrigin (φ0) (lbH) (e) (edges) (nw) (b) : Prop`**: replaces the CURRENT-state
  `IFrozenBelow` claim with a full EXISTENTIAL checkpoint snapshot per recorded edge: the origin
  `(b_o, e_o, edges_o, nw_o)` at record time (carrying its own
  `IFrozenBelow`/`IPosPersistRaw`/`IExpandedConsistent`/open-consistency/`IWorldHist`/
  `IWorldHistCounter` facts), plus three monotonicity witnesses relating it to the CURRENT
  `(e, edges, nw)` (`e_o ⊆ e`, `edges_o ⊆ edges`, `nw_o ≤ nw` -- the origin's own bookkeeping
  only ever grows into the current state), plus the actual freeze CONTENT as its own conjunct,
  `∀ sf ∈ b, sf.label < l+1 → sf ∈ b_o` (current content below the threshold already agrees with
  the origin). Deliberately heavier than `IReuseFrozen` -- the same kind of "existential witness
  that survives forever" idea `IReuseContain`'s OLD `bSnap` snapshot already used, decorated with
  enough checkpoint context to be RE-EXTENDABLE forward using machinery already on hand.
- **`IReuseFrozenOrigin_frozenBelow`**: derives `IFrozenBelow (l+1) e b` about the CURRENT
  `(e, b)` FROM the existential (`hagree` transports `sf ∈ b` down to `sf ∈ b_o`, the origin's
  own `hfrz` classifies it, `e_o ⊆ e` lifts the `sf ∈ e_o` disjunct). This is the key that
  unlocks `IFrozenBelow_intStepBranchPrio_ge` at ANY later round without re-deriving
  `IPosPersistRaw` about that round's pre-persistence branch -- the actual fix for the gap.
- **`IReuseFrozenOrigin_snoc`**: records a freshly-minted edge, using the CURRENT state as its
  own origin reflexively (mirrors `IReuseFrozen_snoc`, threading the full checkpoint context).
- **`IReuseFrozenOrigin_persist`**: advances across ONE round's `applyPersistenceFixpoint` (same
  `e`/`edges`/`nw` throughout a round, only the branch grows `bh → bPers`) -- a direct corollary
  of `applyPersistenceFixpoint_agrees_grow` (item (b), landed last dispatch) at each edge's own
  origin.
- **`IReuseFrozenOrigin_extendMany`**: advances across `Branch.extendMany bPers newForms`, GIVEN
  every element of `newForms` lands at a label `≥ l+1` (the label bound
  `IFrozenBelow_intStepBranchPrio_ge` supplies at each use site, composed with
  `IReuseFrozenOrigin_frozenBelow` above -- not yet wired at the sites themselves).
- **`IAllReuseFrozenOrigin`/`_append`/`_map_const`**: the 5-list zip companion over
  `(bs, expSets, edgeSets, nws, lbSets)`, mirroring `IAllReuseFrozen`'s 3-list zip but extended
  with the per-branch-position `edges`/`nw` context this origin-tracked version needs, plus
  append/map_const companions mirroring the established template exactly.

All eight new declarations verified individually via `lean_verify`: axioms are a subset of the
file's existing baseline (`propext`/`Classical.choice`/`Quot.sound`), zero sorries.

**Not attempted this dispatch**: threading `IAllReuseFrozenOrigin` through
`intExpandBranches_openBranch_sat`'s `key` statement (item (d)); the six `IReuseContain_mono`
use sites are untouched (item (e)); `IReuseContain` itself is unchanged, still the
snapshot-existential form (item (f)).

## Concrete next steps, in dependency order (items (d)-(f) remain)

1. **(d)** Thread `IAllReuseFrozenOrigin` through `key`'s statement and the outer lemma's own
   parameters (mirrors exactly how `hARC`/`IAllReuseContain` is already threaded -- add a
   parallel `hARF : IAllReuseFrozenOrigin φ0 branches expandedSets edgeSets nextWorlds lbSets`
   argument and matching `pendingARF`/`doneARF`-style plumbing through `key`'s own
   quantifiers). Re-grep exact line numbers before editing.
2. **(e)** At each of the six sites (re-grep; roughly bh→bPers persistence transport in
   case2/case4/case6, bPers→extendMany in case5/case7/case8, per the established Scope
   Hypothesis mapping), replace `IReuseContain_mono` with:
   - `IFrozenBelow_intStepBranchPrio_ge` (Phase 5, using `IReuseFrozenOrigin_frozenBelow`'s
     output as its `hfrz` input) to get the label bound for that site's newly-produced content;
   - `IReuseFrozenOrigin_persist` (persistence-fixpoint transport sites) or
     `IReuseFrozenOrigin_extendMany` (content-only growth sites, feeding it the label bound
     just derived) to advance `IReuseFrozenOrigin` itself;
   - the ACTUAL `IReuseContain` (bare, post-restatement) transport, built from
     `IReuseFrozenOrigin_frozenBelow`'s derived `IFrozenBelow` fact plus a case split on whether
     the target formula was already present pre-transport (trivial monotonicity, via
     `applyPersistenceFixpoint_mem_preserved`/`Branch.extendMany`'s own append structure) or
     newly arrived (impossible below the freeze threshold, by the derived `IFrozenBelow` fact).
   Also extend `IReuseContain_snoc`'s call site (case6) to establish the new edge's
   `IReuseFrozenOrigin` witness via `IReuseFrozenOrigin_snoc`.
3. **(f)** Only then restate `IReuseContain` (`Scheme.lean:6814`-ish, re-grep) to drop the
   snapshot, per the plan's own Tasks list.

## Verification (full CI pipeline, all green)

- `lake build` (scoped then full, 3325 jobs): green, only pre-existing warnings/sorries.
- `lake exe checkInitImports`: clean.
- `lake lint`: 373 findings, ZERO attributable to `Scheme.lean` (grep-confirmed against the file
  name and every new declaration name).
- `lake exe lint-style`: clean (no output).
- `lake shake --add-public --keep-implied --keep-prefix`: no import-minimization suggestion for
  `Scheme.lean`; all suggestions pre-existing, unrelated files.
- `lake exe mk_all --module`: "No update necessary".
- `lake test`: green (9397 CslibTests jobs, exit 0, zero errors).
- Sorry count: 196 -> 196 (unchanged). Axiom count: 26 -> 26 (unchanged). Vacuous-definition
  grep: 1 (unchanged, the same pre-existing `Computability/URM/Basic.lean` false positive).

## Territory

Purely additive insertion at `Scheme.lean:7813-8038` (as of this dispatch) -- no existing
declaration modified beyond the mechanical line-shift. Task 605 continues to own the
`isAccessible`-monotonicity / `openBranch_countermodel` / `tableau_complete` region at the end
of `Scheme.lean`; this task's work stays confined to the `intStepBranchPrio` /
`intExpandBranches.go` / `IReuseContain` region plus the shared `isAccessible`/`IWorldHist`
sections near the top of the file, as in every prior dispatch.
