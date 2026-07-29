# Gate B Verdict: Single Loop-Back Hop Persistence Prototype

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Phase**: 2 of 8
- **Status**: COMPLETED
- **Scratch artifact**: `scratch/PersistPrototype.lean`, independently compiled via
  `lake env lean` against the real library (`Rules.lean`/`Expansion.lean` imported directly;
  real `IEdges`, `isAccessible`, `ISF`, `Proposition`, `IBranch` types — not a reimplementation).
  **Zero writes to `Cslib/` or `CslibTests/`** — confirmed via `git status --short Cslib/
  CslibTests/` (empty).

## Method

Restricted to a single recorded loop-back pair `(x, l)` per the plan's scope. Rather than
re-deriving the whole forward induction abstractly, the prototype states the exact
`Sfor`-containment survival question as a theorem (`gateB_single_hop_successor`) over the
REAL types, with three documented hypotheses standing in for facts the later phases are
responsible for establishing:

- `ForestComparable edges` — any two raw-ancestors of a common world are comparable. Not
  proved in the prototype; already available in substance from `Scheme.lean`'s **private**
  `IWorldHist` invariant (task 585, DP-2): `par : Nat → Nat` is a genuine total
  unique-parent function, so `parAncestor` chains are automatically linear, and `IWorldHist`'s
  (H1-acc) clause already links `parAncestor` to `isAccessible`. Phase 5 needs to **export** a
  public corollary of this shape, not invent new forest machinery.
- `SelfCopyReach b edges` — `T(φ→χ)@w`'s own content reaches every raw-descendant of `w`.
  Stands in for Phase 3's reinstated self-copy channel (V1/V4) at Phase 4's fixpoint.
- `OriginTraceable b edges` — placeholder for provenance tracing (see Verdict below).

## Result

`lake env lean scratch/PersistPrototype.lean` — **compiles clean**, with exactly one expected
`sorry` warning (line 64 of the file, the one case documented below as open). No errors.

### Descendant sub-case (`w` raw-descendant of `x`) — CLOSES CLEANLY, no `sorry`

When the `T(φ→χ)@w` source that fires against `T(φ)@l` is itself a raw-descendant of `x`
(`isAccessible edges w x`, established via `ForestComparable`'s disjunction), `SelfCopyReach`
delivers a copy of `T(φ→χ)` to `x` directly, and `hcont` (the blocking-time containment)
supplies `T(φ)@x`. Zero additional hypotheses needed beyond the three listed above.

### Ancestor sub-case (`x` raw-ancestor of `w`) — genuine remaining gap, marked `sorry`

This is the risk the plan's risk table names: a naive "the same rule fires at `x` too"
argument **fails** here, because `SelfCopyReach`/persistence is forward-only (content at a
descendant `w` does not flow backward to its ancestor `x`). Closing this case needs
`T(φ→χ)`'s **own origin** `w0` to be shown raw-accessible to `x` (`isAccessible edges w0 x`),
at which point `SelfCopyReach` fired from `w0` (not `w`) delivers the copy to `x` directly.

**This is not a fresh, unbuilt requirement.** `Scheme.lean`'s private `IWorldHist` invariant
(task 585, DP-2) already threads exactly this shape of provenance data — `par`/`obl`/`fire`/
`sfor` witness functions, one per created world, carried through the SAME forward induction
Phase 5 must extend — for a different purpose (the mint-time reuse residue argument). The
`OriginTraceable` placeholder in the prototype is a stand-in for repurposing that landed
machinery to positive-formula content generally, not a new open research problem.

## Verdict: PASS (conditional)

**Not refuted.** No counterexample was found. Contrast this directly with Option 2 (the
quotient route), which carries a CONCRETE, proven counterexample (`intBlockRep`'s
non-monotonicity under branch growth) — a genuinely different epistemic status. Gate B finds
a real, substantial, but **buildable** remaining obligation, not a wall.

Per the plan's binary contract ("PASS: containment survives; proceed to Phase 3" / "FAIL: it
does not; terminal deferral"): **PASS.** Proceed to Phase 3 (revert `a70187dd`'s three hunks),
contingent on Gate A's variant-selection verdict.

**Scope note for Phase 5**: the invariant to thread is NOT simply pairwise
`Sfor(l) ⊆ Sfor(x)` re-derived at each induction step — the ancestor sub-case shows that
formula-level provenance (which world a positive formula's content ORIGINATES at) is the
load-bearing fact, not branch-growth monotonicity alone. Phase 5 should investigate extending
`IWorldHist`'s existing `par`/`obl`/`fire`/`sfor` witness functions (or a sibling invariant
threaded alongside them, mirroring `IAllAccessConsistent`'s companion-not-merged pattern)
rather than inventing new provenance tracking. This is a genuine, sizeable engineering task —
comparable in scope to the existing `IWorldHist`/`IAllAccessConsistent` threading — not a
one-line corollary; report 17's low-confidence 600-1200 line estimate is not contradicted by
this finding.
