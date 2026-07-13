# Task 317 Phase 1 Continuation Handoff

**As of commit `6e24520d`** (task 317 phase 1 (partial): edge-accessibility monotonicity
infrastructure). Scoped build green:
`lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` -> `Build completed
successfully (662 jobs)`. Four inventory sorries unchanged (now at `Scheme.lean:510`,
`Scheme.lean:1289`, `Completeness.lean:113`, `Minimal/Completeness.lean:110`).

## What landed

Purely additive infrastructure in `Scheme.lean`, right after `intAccessPreorder_le_of_isAccessible`
and after `IExpandedConsistent_mono`:

- `isAccessible_one_step`, `isAccessible_go_append_mono`, `isAccessible_go_fuel_mono`,
  `isAccessible_append_mono`: a direct edge `(w', w) ∈ edges` witnesses one-hop accessibility,
  and any accessibility fact survives as `edges` grows by appending one new edge (the expansion
  loop only ever appends).
- `intAccessPreorder_mono_append`: lifts the above through `Relation.ReflTransGen.mono` to the
  `intAccessPreorder` `Preorder` instance's `≤`.
- `sfAccessSat` / `IExpandedAccessConsistent` / `IAllAccessConsistent` (+ mono lemmas): a
  companion invariant, structurally mirroring `sfSatisfied` / `IExpandedConsistent` /
  `IAllConsistent` but restricted to the single `.neg, .imp` case, stating the F(φ→ψ) witness is
  genuinely `isAccessible`, not merely `≤`. Deliberately kept SEPARATE from the existing
  invariants (not merged in-place) so no already-green call site changes shape.

None of this is wired into the actual saturation/countermodel machinery yet — it is pure
scaffolding, verified in isolation.

## Why full Phase 1 could not land this cycle (design already worked out)

`truthLemma`'s F-imp case currently uses `hsat.sat_fimp` which only supplies a numeric
`w ≤ w'` witness (Nat's ambient, global `≤`, via `IBranchSaturation.sat_fimp`'s CURRENT stated
type at `Scheme.lean` ~line 94-99 pre-edit). That is exactly the "phantom sibling worlds" gap
reports 08/09 identify: it is not strong enough to instantiate `truthLemma` over
`intAccessPreorder edges`. To close this, `sat_fimp`'s type itself must change to require
`isAccessible edges w w' = true` instead of `w ≤ w'` — which means `IBranchSaturation` must
gain access to an `edges` value.

**Recommended design (worked out, not yet applied): make `edges` a FIELD of
`IBranchSaturation`, not a structure PARAMETER.**

```lean
structure IBranchSaturation (Atom : Type*) [DecidableEq Atom] [Hashable Atom]
    (b : IBranch Atom) where
  edges : IEdges
  sat_tand : ...   -- unchanged
  sat_fand : ...   -- unchanged
  sat_tor  : ...   -- unchanged
  sat_for_ : ...   -- unchanged
  sat_fimp : ∀ (φ ψ : Proposition Atom) (w : Nat),
      b.any (fun sf => sf.sign == .neg && sf.formula == .imp φ ψ && sf.label == w) = true →
      ∃ (w' : Nat), isAccessible edges w w' = true ∧
        b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w') = true ∧
        b.any (fun sf => sf.sign == .neg && sf.formula == ψ && sf.label == w') = true
```

This is deliberately a **field**, not a parameter, so that `IBranchSaturation Atom b`'s ARITY
never changes. Every existing `(hsat : IBranchSaturation Atom b)` hypothesis in
`Completeness.lean`/`Minimal/Completeness.lean` stays syntactically unchanged; you only need
`hsat.edges` (a projection) wherever the edges value is needed. This avoids threading a new
explicit parameter through every call site's ARGUMENT LIST — but their STATED TYPES (return
types mentioning `IForces`) still need a `letI`/explicit-instance annotation (see below), since
the concrete `Preorder Nat` instance used must change from the ambient global one to
`intAccessPreorder hsat.edges`.

`intExpandBranches_openBranch_sat`'s return type simplifies from `∃ edges : IEdges,
IBranchSaturation Atom b` to plain `IBranchSaturation Atom b` (edges now travels inside the
structure), which also simplifies `openBranch_countermodel`'s call site (`obtain ⟨edges, hsat⟩
:= ...` becomes `have hsat := ...`, then reference `hsat.edges`).

### Installing the frame in `truthLemma` (and downstream) via `letI`

`intAccessPreorder`'s own docstring already anticipates this: "installed locally (via
`letI`/an explicit instance argument at use sites) rather than as a global instance". Concretely:

```lean
lemma truthLemma (S : IntMinScheme Atom) (b : IBranch Atom)
    (hopen : S.closurePred b = false)
    (hsat : IBranchSaturation Atom b)
    (φ : Proposition Atom) (w : Nat) :
    letI : Preorder Nat := intAccessPreorder hsat.edges
    (b.any (...) → IForces (intExtractValuation b) (S.modelBot b) w φ) ∧
    (b.any (...) → ¬ IForces (intExtractValuation b) (S.modelBot b) w φ) := by
  letI : Preorder Nat := intAccessPreorder hsat.edges
  induction φ generalizing w with
  ...
```

`letI` inside a type (before `:=`) is valid Lean 4 syntax and lets the REST of the statement
(and, matched in the `by`-block, the proof) resolve `IForces`'s `[Preorder World]` instance to
`intAccessPreorder hsat.edges` instead of the ambient global `Nat.instPreorder`, without an `@`
at every occurrence.

**Important consequence**: because `hsat`'s TYPE stays `IBranchSaturation Atom b` (unchanged
arity), but the STATEMENT of `truthLemma` (and everything that calls it) now pins a specific,
non-defeq `Preorder Nat` instance via `letI`, every caller whose OWN stated return type mentions
`IForces` at `World = Nat` needs the SAME `letI` treatment to keep types matching. This means
Phase 1 (truthLemma) is **not independently buildable-green in isolation** — it immediately
forces at least:

1. `openBranch_countermodel` (`Scheme.lean` ~1475): its conclusion `¬ IForces (intExtractValuation
   b) (S.modelBot b) 0 φ` needs to become (per the plan's own Postmortem-5 revision)
   `∃ edges, ¬ @IForces Nat Atom (intAccessPreorder edges) ...` (Phase 2's target) — because
   `edges` is discovered INSIDE this lemma's own proof (via `intExpandBranches_openBranch_sat`),
   not available at its signature unless existentially exposed.
2. `intTruthLemma`, `intuitionisticOpenBranch_countermodel` (`Completeness.lean` ~69,87) and
   their minimal mirrors (`minTruthLemma`?, `minOpenBranch_countermodel`,
   `Minimal/Completeness.lean` ~76+) — Phase 3's targets.
3. `tableau_complete`/`intuitionisticTableau_complete`/`minimalTableau_complete`'s `hvalid`
   instantiation — Phase 4's deferred-monotonicity bridge.

**Conclusion for the next dispatch**: Phases 1–4 (Wave A) are causally serial and should be
implemented and landed as ONE consistent change (matching the plan's own dependency table
"Wave A (Phases 1-4) is strictly serial"). Attempting Phase 1 alone without also touching
Phase 2/3/4's targets in the SAME commit leaves the tree non-building. Budget accordingly —
this is realistically several hundred lines across `Scheme.lean` + both `Completeness.lean`
files landed together, not four small independent commits.

## Per-site accessibility witnesses already available (de-risks Wave A materially)

The two places where `sat_fimp`'s witness is produced ALREADY have the stronger accessibility
fact sitting right there, currently discarded:

1. **Fresh-world creation** (`intStepBranch_linear_preserves`'s `.neg, .imp` case,
   `Scheme.lean` ~826-848 pre-edit): `intFImpRule` returns edge `(w', w) = (nw, l)`; the witness
   `nw` is accessible via `isAccessible_one_step`/`isAccessible_of_mem_edge` applied to
   `(nw, l) ∈ edges ++ [(nw, l)]` (trivial membership).
2. **Option-A dedup reuse** (`intFImpReuseWitness?` in `Expansion.lean:263-291`, consumed at
   `Scheme.lean` ~1180-1224 pre-edit): `intFImpReuseWitness?_spec` (`Expansion.lean:300-327`)
   ALREADY returns `isAccessible edges newEdge.2 x = true` as its FIRST conjunct (named `hacc`
   at the Scheme.lean call site, currently unused for this purpose — only `hle`/`w.ble x` is
   consumed). This is exactly the fact needed; no new proof obligation here, just plumbing.

So the REMAINING Wave A work is threading, not fresh mathematics: wire the already-committed
`isAccessible_*`/`sfAccessSat`/`IExpandedAccessConsistent` infrastructure (this commit) and the
two already-available per-site witnesses above into `IBranchSaturation`'s new `edges` field +
`sat_fimp`'s new type, then propagate the `letI`-based frame change through `truthLemma` →
`openBranch_countermodel` → `intTruthLemma`/`intuitionisticOpenBranch_countermodel` (+ minimal
mirrors) → the `tableau_complete` bridge (Phase 4, monotonicity still deferred to Phase 9/10
per the plan — do NOT attempt to discharge it early).

## Concrete next steps (in order)

1. Change `IBranchSaturation` to add the `edges : IEdges` field (first field) and restate
   `sat_fimp` over `isAccessible edges w w'` (drop the `w ≤ w'` conjunct entirely — no downstream
   consumer needs it once `truthLemma` is rewritten).
2. Update `IExpandedConsistent_sat` (private, `Scheme.lean` ~642): add an explicit `edges`
   parameter, use it (and the newly-landed `sfAccessSat`/`IExpandedAccessConsistent` companion
   invariant, threaded through the SAME induction as `IExpandedConsistent`/`IAllConsistent`) to
   discharge the new `sat_fimp` field via `refine { edges := edges, sat_tand := ?_, ... }`.
3. Update `intStepBranch_linear_preserves`/`intStepBranch_branch_preserves` to also carry/return
   `IExpandedAccessConsistent`/`IAllAccessConsistent` facts alongside the existing
   `IExpandedConsistent`/`IAllConsistent` ones (mirroring exactly the same case structure; the
   `.neg, .imp` case supplies the new edge via `isAccessible_one_step`, all other cases carry
   forward unchanged via `sfAccessSat_mono`/`IExpandedAccessConsistent_mono`).
4. Update the outer `intExpandBranches_openBranch_sat` induction to thread `IAllAccessConsistent`
   alongside `IAllConsistent` (same `edgeSets`-indexed structure, already tracked for length
   purposes — just add the extra invariant conjunct), and change its return type from
   `∃ edges : IEdges, IBranchSaturation Atom b` to plain `IBranchSaturation Atom b`.
5. Rewrite `truthLemma`'s F-imp case using `hsat.sat_fimp` (now an `isAccessible` witness) lifted
   via `intAccessPreorder_le_of_isAccessible`; add the `letI : Preorder Nat := intAccessPreorder
   hsat.edges` to both the statement and the proof; leave the T-imp case as `sorry` (unchanged,
   deferred to Phase 9).
6. Update `openBranch_countermodel` to the Postmortem-5-revised existential conclusion
   (`∃ edges, ¬ @IForces Nat Atom (intAccessPreorder edges) ...`), dropping the
   `obtain ⟨edges, hsat⟩ := ...` in favor of `have hsat := ...` + `hsat.edges`.
7. Mirror into `Completeness.lean` (`intTruthLemma`, `intuitionisticOpenBranch_countermodel`)
   and `Minimal/Completeness.lean` (their analogues) with the same `letI`/existential pattern.
8. Leave `tableau_complete`/`intuitionisticTableau_complete`/`minimalTableau_complete`'s
   `hvalid`-bridge sorries exactly as-is (Phase 4's deferred-monotonicity bridge, discharged only
   in Phase 9/10) — do NOT attempt to close them early; only their SURROUNDING types may need
   the same `letI`/existential threading to keep compiling.
9. Scoped build (`Scheme.lean`, then `Completeness`, then `Minimal.Completeness`) at each step;
   commit Wave A as a whole once green (four sorries preserved, unchanged count, now possibly at
   new line numbers).

## Territory / coordination reminders (unchanged from the plan)

- Task 430 is sequenced strictly after 317 and gated on Wave A landing; do not let it touch
  `Completeness.lean`/`Minimal/Completeness.lean` until Wave A + Phase 9 monotonicity land.
- `Soundness.lean` (task 316) is read-only unless Phase 5's fuel-raise strictly forces it — none
  of the above touches `Soundness.lean`.
- Single-writer-per-file (R7): re-run `git log -1 -- <file>` at the start of the next dispatch
  to confirm no other concurrent session has touched `Scheme.lean`/`Completeness.lean`/
  `Minimal/Completeness.lean` since commit `6e24520d`.

## Addendum: a discarded WIP attempt at step 3 (do this atomically next time)

A concurrent dispatch in this same cycle attempted step 3 above (threading
`IExpandedAccessConsistent` through `intStepBranch_linear_preserves`/`intStepBranch_branch_preserves`)
but was found uncommitted and non-building at cycle end, and was discarded (`git checkout --`)
to keep the tree at the green `6e24520d` checkpoint. The approach itself was correct (added an
`hACC : IExpandedAccessConsistent edges b e` hypothesis and a third conjunct to each lemma's
conclusion, using `isAccessible_one_step`/`sfAccessSat_mono`/`sfAccessSat_edges_mono` exactly as
sketched above) but it broke the build because:

- The outer `intExpandBranches_openBranch_sat` induction's call sites (`Scheme.lean` ~1408 and
  ~1487) call `intStepBranch_linear_preserves hIC_bPers hLB_bPers hstep` /
  `intStepBranch_branch_preserves hIC_bPers hLB_bPers hstep` positionally — adding a THIRD
  explicit hypothesis argument to these lemmas shifts `hstep` out of position and these two call
  sites were not updated in the same edit.
- A stray `Hashable Atom` instance-resolution failure appeared at line 1037 (likely an `omit`
  clause needing adjustment near the new `.neg, .imp` case, since several nearby lemmas are
  stated with `omit [Hashable Atom] in` and the new code block may need the same treatment, or
  the reverse — omitted where it shouldn't be).

**Recommendation**: when redoing step 3, update `intStepBranch_linear_preserves`/
`intStepBranch_branch_preserves` AND their two call sites in the outer induction (plus
`IAllAccessConsistent` threading through the `IAllConsistent_append`/`IAllConsistent_map`
equivalents already landed) in the SAME edit before attempting a build, rather than building
after only the lemma signatures change.
