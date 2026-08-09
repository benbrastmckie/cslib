# Research Report: Uniform frame for `openBranch_countermodel` conjunct 1

**Task**: 603 — construct_uniform_frame_for_openbranch_countermodel
**Session**: sess_1786308724_41a1c9_603
**File in scope**: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
**Status**: route identified, machine-grounded (empirical evidence from task 591's probes plus a
sorry-free library lemma already covering the persistence step); concrete Lean skeleton below.
Conjunct 1 is NOT yet discharged in-source — that is implementation work — but the construction,
the exact supporting lemma, and the one small plumbing gap that must be closed are all pinned
down precisely.

---

## 1. Recommended construction: reuse `rawEdges`, unchanged

**Do not invent a new definition.** `intExpandBranches_openBranch_sat`
(`Scheme.lean:6815-6844`, private) already produces everything needed. Its conclusion is

```
∃ (edges rawEdges lbEdges : IEdges) (nwF : Nat), IBranchSaturation Atom b ∧
  IFimpAccess edges b ∧ IPosPersistRaw rawEdges b ∧ IReuseContain lbEdges b ∧
  ForestComparable nwF rawEdges
```

`openBranch_countermodel`'s current proof (`Scheme.lean:7914-7919`) already destructures this
5-tuple but **discards** `rawEdges`, `lbEdges`, and `nwF` (bound as `_rawEdges`, `_lbEdges`,
`_nwF`), keeping only the augmented `edges` (the `augSets` witness, tree edges plus the
loop-back edges recorded at reuse/blocking sites) to feed both conjuncts.

`rawEdges` is exactly "raw edges pruned at reuse/blocking sites" from the delegation brief and
from task 591's own report (`specs/591_.../reports/01_openbranch-countermodel-disposition.md`
§6, "Proof route" step 2): it is the tree-only parent→child edge list built by
`intFImpRule`'s world-creation step (`Rules.lean:159-164`), threaded through the SAME induction
as `edges`/`augSets` but never receiving the loop-back edges `IReuseContain`/`augSets` add at
reuse sites. The distinction is visible directly in the induction's exit case
(`Scheme.lean:7059-7060`): `⟨augH, edgesH, lbH, nwH, ..., hpp, hARC_bPers, hfc⟩` — `edgesH` (=
`rawEdges` in the outer statement) and `augH` (= `edges`/`augSets`) are two DIFFERENT lists
threaded in parallel through the whole 10-case induction, and only `edgesH` pairs with
`IPosPersistRaw`.

**The construction for conjunct 1 is: `edges := rawEdges`.**

## 2. Why this works: `IPosPersistRaw` is already sorry-free and is exactly atom persistence

```
private def IPosPersistRaw (edges : IEdges) (b : IBranch Atom) : Prop :=
  ∀ (χ : Proposition Atom) (w w' : Nat), isAccessible edges w w' = true →
    (⟨.pos, χ, w⟩ : ISF Atom) ∈ b → b.any (fun sf => sf.label == w') = true →
    (⟨.pos, χ, w'⟩ : ISF Atom) ∈ b
```
(`Scheme.lean:6701-6704`). It is discharged, sorry-free, inside the same induction via
`applyPersistenceFixpoint_copy_complete` (`Scheme.lean:7052-7055`, itself landed sorry-free per
its own docstring at `Scheme.lean:6689-6700` — "Phase 4, landed sorry-free"). Specializing
`χ := .atom p` turns `IPosPersistRaw rawEdges b` into exactly the one-step form of conjunct 1:

```
isAccessible rawEdges w w' = true → T(atom p)@w ∈ b → (∃ entry at w') → T(atom p)@w' ∈ b
```

which is `intExtractValuation b w p → intExtractValuation b w' p` given one `isAccessible`
step (`intExtractValuation` unfolds to exactly this membership via `List.any`/`==`,
`Soundness.lean:1129-1130`).

This is independent corroboration of the empirical evidence task 591 already recorded
(`reports/01_openbranch-countermodel-disposition.md` §4.1/§4.5, `WitnessProbe.lean:87`): for the
concrete `phiRef1` branch, the **full** raw tree `[(1,0),(2,1)]` is upward-closed (`true`) —
pruning to `[(1,0)]` was needed only to falsify `phiRef1` at world 0 (conjunct 2), not for
conjunct 1. `IPosPersistRaw` explains *why* this generalizes to every branch, not just the one
example: it is a proved structural fact about the algorithm's raw edges, not a coincidence of one
witness.

## 3. What conjunct 1's frame relation actually is, and the one gap to close

`openBranch_countermodel`'s conjunct 1 quantifies over `intAccessPreorder edges`'s `≤`, which is
`Relation.ReflTransGen (fun x y => isAccessible edges x y = true)` (`Scheme.lean:268-274`), not a
single `isAccessible` call. `IPosPersistRaw` only gives ONE `isAccessible`-step transfer, so the
target lemma needs an induction over the `ReflTransGen` chain, applying `IPosPersistRaw` at each
step. Each step needs `IPosPersistRaw`'s third hypothesis: `b.any (fun sf => sf.label == w') =
true` — "the target world already has *some* entry on `b`."

**This side condition is not yet exported, but it is cheap to establish**, in exact analogy to
how `ForestComparable` itself was derived (`Scheme.lean:3329-3348`, "a pure COROLLARY of the
already-landed `IWorldHist`/`IWorldHistCounter` invariants: no new invariant needs threading
through `intExpandBranches_openBranch_sat`'s 10-case induction"):

1. **Structural half (needs no invariant): if `isAccessible edges w y = true` and `w ≠ y`, then
   `y` is a "child" endpoint of some edge in `edges`.** This falls straight out of unfolding
   `isAccessible`/`isAccessible.go` (`Rules.lean:92-107`): the DFS only ever returns `true` at a
   non-reflexive target by finding `child == w'` in `edges.filterMap (fun (child,parent) => if
   parent==current then some child else none)`, i.e. `∃ parent, (y, parent) ∈ edges`. This is the
   same style of argument already used by `isAccessible_one_step`/`parAncestor_of_isAccessible`
   (`Scheme.lean:298-311`, `3390-3434`) and needs no new hypothesis — it is a standalone
   corollary of `isAccessible`'s definition, provable independent of `IWorldHist`.

2. **Provenance half (needs `IWorldHist`'s already-threaded (H3) clause): every edge-list child
   `c` (`1 ≤ c < nwF`) has a planted branch entry.** `IWorldHist`'s (H3) clause already states
   `(⟨.neg, obl c, c⟩ : ISF Atom) ∈ b` for every `1 ≤ c < nw` (`Scheme.lean:3272`), which
   immediately gives `b.any (fun sf => sf.label == c) = true`. `edges_shape_of_worldHist`
   (`Scheme.lean:3355-3382`) already proves every pair in `rawEdges` (there called `edges`) has
   the shape `(c, par c)` for such a `c` — its proof internally extracts `1 ≤ c < nw` from
   `Finset.Ico 1 nw` (see the discarded `_hc1 _hc2` at `Scheme.lean:3381`) but does not currently
   return that bound in its stated conclusion. A trivial strengthening (return the bound, or add
   a new corollary lemma alongside it rather than editing the existing one) supplies exactly what
   step 2 needs.

3. **Assemble at the existing derivation site.** `hWH_head : IWorldHist φ0 bh eH nwH edgesH` and
   `hWHC_head : IWorldHistCounter nwH edgesH` are ALREADY in scope at `Scheme.lean:7017-7019`,
   the exact point `hfc := IWorldHist_forestComparable hWH_head hWHC_head` is computed
   (`Scheme.lean:7058`). A new corollary, e.g.
   ```
   private lemma IWorldHist_worlds_planted {φ0 b e nw edges}
       (hWH : IWorldHist φ0 b e nw edges) (hWHC : IWorldHistCounter nw edges)
       {c p : Nat} (hmem : (c, p) ∈ edges) :
       b.any (fun sf => sf.label == c) = true
   ```
   proved the same way as `IWorldHist_forestComparable` (destructure `hWH`, apply the
   strengthened `edges_shape_of_worldHist` to get `1 ≤ c < nw` and `c = c'`, then `(hall c
   hc1 hc2).2.2.2.2.1` for the (H3) membership fact), can be computed right there and packaged
   as a SIXTH conjunct in `intExpandBranches_openBranch_sat`'s existential — no new
   invariant-threading through the 10-case induction, exactly the `ForestComparable` precedent.

This is the only piece of new Lean machinery this task's route needs, and it is small (one
corollary lemma, one widened existential, mirroring an already-landed pattern in the same file).

## 4. Target lemma (conjunct 1 only — do not fold into `openBranch_countermodel`)

Per the delegation's scope, conjunct 2 stays out of scope, and `openBranch_countermodel`'s
existing `edges` variable (`augSets`) is what conjunct 2's `refine ⟨edges, ?_,
(truthLemma ...).2 hFmem⟩` (`Scheme.lean:7948`) already needs — that binding cannot be swapped to
`rawEdges` without also re-solving conjunct 2 for `rawEdges` (successor-task work: does
`IFimpAccess rawEdges b` hold, or does `truthLemma` need re-deriving over the raw frame?). So
this task's deliverable should be a **standalone** lemma, not an edit to
`openBranch_countermodel`'s existing `sorry`:

```lean
/-- Conjunct 1 of `openBranch_countermodel`, discharged uniformly for the RAW (tree-only,
reuse/loop-back-pruned) edge witness `intExpandBranches_openBranch_sat` already produces.
Needs no fact about the tableau algorithm beyond `IPosPersistRaw` (already sorry-free) plus the
branch-entry-existence corollary of `IWorldHist`'s (H3) clause (§3). Conjunct 2 (¬IForces) is
NOT addressed here -- see the successor task. -/
lemma openBranch_rawEdges_upward_closed (S : IntMinScheme Atom) (φ : Proposition Atom)
    (b : IBranch Atom)
    (h : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
        [intFuelExt φ] S.closurePred = .openBranch b) :
    ∃ edges : IEdges,
      ∀ {w w' : Nat} (p : Atom), @LE.le Nat (intAccessPreorder edges).toLE w w' →
        intExtractValuation b w p → intExtractValuation b w' p := by
  obtain ⟨_edges, rawEdges, _lbEdges, _nwF, _hsat, _hfimp, hpp, _hrc, _hfc, hplanted⟩ :=
    intExpandBranches_openBranch_sat φ [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [intFuelExt φ]
      [[]] [[]] _ _ (by ...) rfl rfl (by ...) (by ...)
      (fun b hb x hx => by ...) (fun nw hnw => by ...) (by ...) (by ...)
      ⟨IWorldHist_entry _ _ _ _, trivial⟩ ⟨IWorldHistCounter_entry, trivial⟩ (fun b' hb' ψ w hmem hcontra => by ...) h
  -- (obtain-block mirrors openBranch_countermodel's own destructuring exactly,
  --  Scheme.lean:7914-7946, plus the new 6th conjunct `hplanted` from §3)
  refine ⟨rawEdges, ?_⟩
  intro w w' p hle hval
  induction hle using Relation.ReflTransGen.head_induction_on with
  | refl => exact hval
  | head hstep _hrest ih =>
    -- hstep : isAccessible rawEdges w y = true  (single hop into the chain)
    apply ih
    by_cases hwy : w == y
    · simpa [intExtractValuation, hwy] using hval
    · have hy_child : ∃ p, (y, p) ∈ rawEdges := isAccessible_reach_mem_edges hstep (by simpa using hwy)
      obtain ⟨p', hp'⟩ := hy_child
      have hentry : b.any (fun sf => sf.label == y) = true := hplanted hp'
      simpa [intExtractValuation] using hpp (.atom p) w y hstep (by simpa [intExtractValuation] using hval) hentry
```

(Names/argument order above are indicative, not final — `Relation.ReflTransGen.head_induction_on`
peels from the LEFT end of the chain, so the exact motive/direction should be checked with
`lean_goal` during implementation; `Relation.ReflTransGen.trans_induction_on` is a fallback if the
head-induction shape does not unify cleanly with a universally-quantified `p`.)

`isAccessible_reach_mem_edges` is the new, easy structural lemma from §3 item 1 (unfold
`isAccessible`/`isAccessible.go`; no `IWorldHist` needed for this half).

## 5. Explicitly ruled out (per delegation) — do not re-attempt

- **The maximal inclusion frame `⊑`** (every pair with `A(w) ⊆ A(w')`). Task 591's exhaustive
  probe (`WitnessSearch3.lean`, `reports/01_....md` §4.4) shows it fails to be a uniform witness
  at `phiRef1`/`phiRef3` — this is about serving BOTH conjuncts uniformly (the frame that must
  simultaneously support the successor task's conjunct-2 truth lemma), and the delegation is
  explicit that this route is ruled out; do not re-derive or re-propose it even restricted to
  conjunct 1 alone.
- **A brand-new `inclEdges b : IEdges` definition built from scratch off `intExtractValuation`.**
  Report 591 §6 floated this as one option ("Define `inclEdges b : IEdges`... short, and
  independent of all algorithm invariants"), but the delegation's "known starting point" already
  points at the algorithm's own `rawEdges`, which is (a) already computed, (b) already proved
  upward-closed via `IPosPersistRaw`, and (c) the more promising candidate for the successor
  task's conjunct-2 reconciliation (since it is the actual accessibility relation the algorithm's
  ψ-consequence propagation reasons over, unlike an atom-inclusion-only frame with no connection
  to `IFimpAccess`). Recommend `rawEdges`, not a fresh `inclEdges`.

## 6. Alternative route (noted, not recommended for this task)

The delegation also names fixing `intFImpReuseWitnessAnc?`'s defect (`Expansion.lean`) — the
containment check recorded at a loop-back edge is never re-validated as the branch grows — as an
alternative path to a workable AUGMENTED frame. This is calculus-level work in `Expansion.lean`,
outside this task's `file_scope` (`Scheme.lean` only), and the `rawEdges` route above appears
tractable without it. Not pursued here; flagged only so a future dispatch does not need to
re-derive that this option exists and why it was set aside.

## 7. Relationship to conjunct 2 / the successor task

This task's lemma (`openBranch_rawEdges_upward_closed` or similarly named) is deliberately
**decoupled** from `openBranch_countermodel`. The successor task's job is to reconcile the two
conjuncts under a single `edges` — either (a) show `rawEdges` also supports a conjunct-2 truth
lemma (would need `IFimpAccess rawEdges b`, not currently exported — `IFimpAccess` is only
established for the augmented `edges`/`augSets`, `Scheme.lean:6843`), or (b) restate
`openBranch_countermodel` to existentially quantify `edges` separately for each conjunct (not
sound — the statement needs ONE `edges` witnessing both) and find a genuinely uniform
construction. Task 591's report (§5) already names this as "equivalent to the completeness
theorem itself" — expect it to be the hard remaining piece, not a quick follow-up.

## 8. Reuse-first check (CSLib reuse-first philosophy)

No new typeclass, notation, or CSLib/Mathlib abstraction is needed. Everything cited already
exists in this file or its siblings:
- `intAccessPreorder`, `intAccessPreorder_le_of_isAccessible`, `isAccessible`,
  `isAccessible_append_mono` (`Scheme.lean:268-384`, `Rules.lean:85-107`)
- `IPosPersistRaw` (`Scheme.lean:6701-6704`) and its sorry-free discharge
  (`applyPersistenceFixpoint_copy_complete`, `Scheme.lean:5464`, used at `7052-7055`)
- `IWorldHist`, `IWorldHistCounter`, `edges_shape_of_worldHist`,
  `IWorldHist_forestComparable` (`Scheme.lean:3146-3510`) — the exact precedent pattern to copy
  for the one new corollary this route needs
- `intExtractValuation` (`Soundness.lean:1129`)
- `Mathlib.Relation.ReflTransGen` (`.head_induction_on`, `.trans_induction_on`, `.mono`) is
  already the closure mechanism throughout this file — no Mathlib addition needed.

## 9. Zero-debt compliance

The route above requires **zero new sorries and zero new axioms**: `IPosPersistRaw` is already
proved; the one new corollary (`IWorldHist_worlds_planted` or equivalent) follows the exact,
already-successful `IWorldHist_forestComparable` derivation pattern (same hypotheses, same
call site, same "pure corollary, no new induction-threading" shape); the structural
`isAccessible`-unfolding lemma needs no invariant at all. The four pre-existing sorries in this
file are untouched by this task's scope (conjunct 1 of `openBranch_countermodel` itself stays
`sorry` until the successor task reconciles it with conjunct 2 — this task deliberately produces
a new, additional, sorry-free lemma alongside it, not a modification of the existing `sorry`
site).

## References

* Task 591 report: `specs/591_decide_openbranch_countermodel_disposition/reports/01_openbranch-countermodel-disposition.md`
  (§3 the `𝒫(⊑)` characterization, §4.1/§4.5 raw-tree-is-upward-closed evidence, §6 the
  "raw edges pruned at reuse/blocking sites" recommendation this task follows)
* `specs/591_.../scratch/WitnessProbe.lean` (the `[(1,0),(2,1)]` raw-tree upward-closure probe)
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4 —
  cited by `openBranch_countermodel`'s own docstring for the general shape of this construction.
