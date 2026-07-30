# Handoff: `ForestComparable` Export Landed, Phase 10 Continuation Notes

- **Task**: prove_atom_persistence_upward_closure_for_intexpan
- **Plan**: `plans/06_gate-b2-then-origin-tracing-export.md`, Phase 10
- **Status**: PARTIAL (not BLOCKED) — Phase 10's own first construction step (the
  `ForestComparable` export, named by handoff 08) is now landed, sorry-free, in
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`. Full `lake build` green
  (3311 jobs), identical 4 in-scope sorries as Phase 8/9 (no regression, no new sorries).
  Phase 10's REMAINING tasks (origin-tracing witness extension, (H3) generalization,
  origin-raw-accessibility proof, Phase 9 residual-lemma retry) are still open.

## What was landed this dispatch

Read `handoffs/08_phase9-collapsed-phase10-handoff.md` first for the entry context. That
handoff identified `ForestComparable`/`par`-linearity as needing a "further
`intExpandBranches_openBranch_sat` conclusion-signature change... the same kind of change
Phases 7/8 each made, each its own dispatch" — i.e. potentially a full dispatch's worth of
threading a NEW invariant through the 10-case induction. This dispatch found and verified a
materially cheaper route: **`ForestComparable` is a pure corollary of the already-landed
`IWorldHist`/`IWorldHistCounter` invariants, requiring zero new invariant threading.**

### The three-step derivation (all sorry-free, verified first in scratch, then ported)

1. **`edges_shape_of_worldHist`** (counting/pigeonhole): `IWorldHist`'s (H1) clause gives
   `nw - 1` pairwise-distinct required pairs `(c, par c)` (`1 ≤ c < nw`) as MEMBERS of `edges`;
   `IWorldHistCounter` gives `edges.length = nw - 1` exactly. Since a list of length `n`
   containing `n` pairwise-distinct required elements cannot contain anything else
   (`Finset.eq_of_subset_of_card_le` applied to `edges.toFinset` vs. the required `Finset.Ico`
   image), **every** member of `edges` has the shape `(c, par c)` for some `c` — not just the
   `nw - 1` required ones being present, but nothing extra being present either. This is the
   fact (H1-acc) alone does NOT supply (H1-acc only gives the forward `parAncestor →
   isAccessible` direction).
2. **`parAncestor_of_isAccessible`**: given step 1's shape fact, `isAccessible`'s fuel-indexed
   DFS (`isAccessible.go`) is shown to coincide with `parAncestor` — this is precisely the
   CONVERSE direction handoffs 07/08 flagged as unestablished (`isAccessible edges x l = true`,
   the shape the reuse witness `intFImpReuseWitnessAnc?_spec` actually supplies, converted into
   `parAncestor par x l`). Proved by induction on `go`'s fuel: each DFS step from `current` to
   `child` uses an edge `(child, current) ∈ edges`, which by step 1 has the shape
   `(child, par child)`, giving `current = par child` — exactly the base step relation
   `parAncestor` is built from — so the whole DFS trace assembles into a `parAncestor` chain via
   `Relation.ReflTransGen.head`.
3. **`parAncestor_comparable`**: pure `par`-linearity — any two `parAncestor`-ancestors of a
   common world are themselves comparable. Proved via the standard `parAncestor`-as-iterate
   bridge (`parAncestor_iff_iterate : parAncestor par x y ↔ ∃ n, x = par^[n] y`, itself a clean
   induction on `ReflTransGen`/`Nat` respectively): both ancestors are `par`-iterates of the
   common point, and `Nat` iterate-counts are always comparable (`le_total`), so one ancestor is
   a further iterate of the other.

`IWorldHist_forestComparable` combines all three with (H1-acc) (case-split on whether the
`c` argument is the root `0`, using `parAncestor_zero`, or `1 ≤ c < nw`, using (H1-acc) directly)
to produce `ForestComparable nw edges := ∀ w x l, w < nw → x < nw → isAccessible edges w l =
true → isAccessible edges x l = true → isAccessible edges w x = true ∨ isAccessible edges x w =
true` — exactly the shape `specs/430_.../scratch/PersistPrototype.lean` assumed as an unproven
hypothesis.

### Threading into `intExpandBranches_openBranch_sat`

Confirmed by direct case inspection that `case4` of the 10-case `.go.induct` split is the SOLE
case producing the `.openBranch b` result (the other 9 cases all recurse via `ih`; only `case4`'s
`injection hgo` leads to a real construction, `case3`'s leads to an `omega` contradiction via
`hFuel`). This meant only `case4` needed modification:
- Un-discarded `hWHP`/`hWHCP` (previously `_hWHP`/`_hWHCP`, i.e. already-threaded-but-unused data).
- Extracted `hWH_head : IWorldHist φ0 bh eH nwH edgesH` / `hWHC_head : IWorldHistCounter nwH
  edgesH` from the head of the list (exactly as every other case already does for its OWN use of
  `hWHP`/`hWHCP`, e.g. `case5`'s `hWH_ext` transfer).
- Applied `IWorldHist_forestComparable hWH_head hWHC_head : ForestComparable nwH edgesH`.
- Added `nwH` and this fact to the final existential tuple.

The lemma's conclusion changed from a 3-existential/4-conjunct shape to a 4-existential
(`edges rawEdges lbEdges nwF`)/5-conjunct shape (added `ForestComparable nwF rawEdges` — `rawEdges`
because that is the existential `edgesH` is bound to at the exit tuple's 2nd position, confirmed
by matching `⟨augH, edgesH, lbH, ...⟩` against `(edges, rawEdges, lbEdges, ...)`). The sole
consumer, `openBranch_countermodel`, had its destructuring updated to add `_nwF`/`_hfc` (both
still unused — Phase 10's remaining tasks are what will consume them, via the Phase 9 residual
lemma retry, task 7 of handoff 08's list).

### Where the new code lives

All new declarations are `private` (matching `IPosPersistRaw`/`IReuseContain`'s visibility),
inserted in `Scheme.lean` immediately after `IWorldHistCounter_entry` (before the
`IAllWorldHistCounter` list-companion section): `edges_shape_of_worldHist`,
`parAncestor_of_isAccessible`, `parAncestor_iff_iterate`, `parAncestor_comparable`,
`ForestComparable` (the new `private def`), `IWorldHist_forestComparable`. New imports added:
`Mathlib.Data.Finset.Card`, `Mathlib.Data.Finset.Image`, `Mathlib.Order.Interval.Finset.Nat`,
`Mathlib.Logic.Function.Iterate` (all genuinely used, confirmed via a scoped `lake shake` run
with no complaints).

Scratch de-risking artifacts (kept for reference, not imported by anything real):
`specs/430_.../scratch/ForestComparableProbe.lean` (the counting lemma in isolation, generic
types) and `specs/430_.../scratch/ForestComparableProbe2.lean` (the full 3-step chain, with
locally-copied `parAncestor`/real `isAccessible`, before porting into `Scheme.lean` proper).

## What Phase 10 still needs (do not re-derive the above)

Per handoff 08's remaining task list (now that the `ForestComparable` prerequisite is done):

1. Extend `IWorldHist`'s witness functions — or thread a sibling invariant, mirroring
   `IAllAccessConsistent`'s companion-not-merged pattern — to record a traceable origin world
   for every positive formula's presence on the branch (not just mint obligations, which is all
   `IWorldHist`'s `sfor`/`obl` currently track). THIS is the piece still comparable in scope to
   building `IWorldHist` itself — the `ForestComparable` export was a genuinely separable,
   cheaper prerequisite, not a down-payment on this part.
2. Generalize (H3)'s planted-positive-content shape (`Scheme.lean`, near the `IWorldHist` def:
   `∀ χ ∈ sfor c, χ ∈ posFormulasAt b c`) from "the mint-time `Sfor` set" to "every positive
   formula's point of origin".
3. Prove the recorded origin is raw-accessible to any `x` a loop-back edge points from, using
   (H1-acc) and the NOW-AVAILABLE `ForestComparable`/`IWorldHist_forestComparable`.
4. Reuse `IWorldHist_mono` for the transfer in every non-minting arm and `IWorldHist_entry` for
   the vacuous entry discharge. Do not re-derive either.
5. Reuse `IAllWorldHist_append`/`_map_const` and the `IAllWorldHistCounter` family for the
   list-level plumbing.
6. Once origin-tracing lands, **re-attempt Phase 9's residual lemma**: the `y ≤ x` closing
   argument from handoff 07 is reusable verbatim; the `x ≤ y ≤ w` case now has
   `ForestComparable`/`IWorldHist_forestComparable` available (this dispatch's deliverable) but
   still needs the origin-tracing extension (items 1-3 above) to identify `χ`'s true origin and
   place it `≤ x`.
7. Do **not** reach for `intWorldHist_chain_le`, `pathOf`, `pathOf_injOn`, or
   `intWorldHist_nw_le` — world-**bound** machinery, unchanged exclusion from every earlier
   phase.

## Do not re-derive

- Everything in "What was landed this dispatch" above (the full `ForestComparable` chain) —
  landed, sorry-free, reusable as-is via `IWorldHist_forestComparable`.
- Handoff 07's full sub-case analysis (the `y ≤ x` closing argument, the `x ≤ y ≤ w` gap
  characterization) — still applies unchanged.
- Phase 7's `IPosPersistRaw` and Phase 8's `IReuseContain`/`IAllReuseContain` — landed,
  sorry-free, reusable as-is.
- The exclusion list (quotient/blocking-frame route, Route C, `≤`-on-ℕ, budgeting
  `pathOf`/`intWorldHist_nw_le` as reuse wins) — still prohibited, unchanged.

## Verification

Full `lake build` (3311 jobs) green. `lake test` (9376 jobs) green. `lake exe checkInitImports`
clean (exit 0). `lake exe lint-style` clean (exit 0). `lake exe mk_all --module`: no update
necessary. Scoped `lake shake` on the modified module: no complaints (all 4 new imports
genuinely used). `lake lint`: zero warnings attributable to `Scheme.lean` (grepped the full
output for the filename — no hits); the 361 lines of lint output are pre-existing, unrelated to
this module. Identical 4 in-scope sorries as Phase 8/9 (`Scheme.lean:675` DP-5,
`Scheme.lean:7818`'s conjunct surfacing at `Intuitionistic/Completeness.lean:137` DP-3 and
`Minimal/Completeness.lean:133` DP-4; `Modal/Tableau/FrameSoundness.lean:1252` unrelated,
pre-existing). `lean_verify` on `openBranch_countermodel`, `tableau_complete`,
`intuitionisticTableau_complete`, `minimalTableau_complete`: all report only
`["propext", "sorryAx", "Classical.choice", "Quot.sound"]`, unchanged from Phase 8/9 (transitive
`sorryAx` from the still-open sorries, not a new axiom).

## Files touched this dispatch

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (new private lemmas; new
  imports; `intExpandBranches_openBranch_sat`'s conclusion gained a 4th existential (`nwF`) and
  5th conjunct (`ForestComparable nwF rawEdges`); `case4` of its induction un-discards
  `hWHP`/`hWHCP` and constructs the new conjunct; `openBranch_countermodel`'s destructuring
  updated to match)
- `specs/430_.../scratch/ForestComparableProbe.lean` (new — counting lemma probe)
- `specs/430_.../scratch/ForestComparableProbe2.lean` (new — full 3-step chain probe)
- `specs/430_.../plans/06_gate-b2-then-origin-tracing-export.md` (Phase 10 annotated with the
  prerequisite-completed note; checklist item 1 annotated, not checked — the origin-tracing
  extension itself remains open)
- `specs/430_.../handoffs/09_forestcomparable-export-phase10-continuation.md` (this file)
