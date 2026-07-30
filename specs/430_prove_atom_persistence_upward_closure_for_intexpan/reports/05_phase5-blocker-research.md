# Phase 5 Blocker Research: Origin-Tracing Necessity, Scope, and a New Refutation Risk

- **Task**: 430 — prove_atom_persistence_upward_closure_for_intexpan
- **Dispatch type**: research only (blocker escalation). Zero writes to `Cslib/` or `CslibTests/`.
- **Verdict**: `tractable_large`, **but** with a newly-identified, unretired **refutation risk**
  that must be probed before any large build-out, plus a **machine-verified statement-shape
  defect** that blocks DP-3/DP-4 independently of all persistence work.

## Executive summary

Three findings, in descending order of consequence:

1. **DP-3 and DP-4 are unprovable AS STATED** — machine-verified, not conjectured. This is
   independent of the persistence invariant and was not previously recorded. The route through
   `tableau_complete` discards the provenance of `b`, and the resulting goal is false at a
   concrete witness. A signature change is mandatory. See §1.
2. **A new refutation risk for the augmented statement itself**: independent beta-split
   (disjunction) choices at a reused ancestor `x` versus at the blocked world `w` appear to break
   atom-level persistence across the recorded loop-back edge. Gate B did not consider this
   mechanism — it analysed only the *copy* argument's descendant/ancestor sub-cases. If this
   shape is realizable, the terminal answer is permanent deferral. See §4.
3. **A genuine de-risking discovery**: the algorithm's reuse check already enforces exactly the
   backward containment the loop-back edge needs — `{φ} ∪ posFormulasAt bPers w ⊆
   posFormulasAt bPers x` — at reuse time. So the gap is purely *temporal* (post-reuse arrivals),
   narrower than "build `IWorldHist` again". See §3.

## 1. The statement-shape defect (machine-verified)

`tableau_complete` (`Scheme.lean:7446`) demands:

```lean
(hvalid : ∀ (edges : IEdges) (b : IBranch Atom),
  @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ)
```

quantified over **arbitrary** `edges` and **arbitrary** `b`, with no hypothesis tying either to a
tableau run. Its proof (`:7451-7457`) only ever uses `hvalid edges b` at the `b` returned by
`openBranch_countermodel`, so the premise is strictly stronger than the proof needs.

`IValid φ` (`Kripke.lean:145`) supplies forcing only for **upward-closed** valuations. At the
DP-3 site (`Completeness.lean:131-140`), `apply tableau_complete intScheme; intro edges _b` leaves
a goal about an arbitrary `(edges, _b)` pair, and `intExtractValuation _b` is not upward closed
along `intAccessPreorder edges` in general.

**Verified refutation** — `scratch/HvalidShapeRefutation.lean`, compiled with
`lake env lean`, **zero errors and zero sorries**:

| Declaration | Content |
|---|---|
| `phiK` | `p → (q → p)` (the `implyK` axiom shape) |
| `edgesCE` | `[(1, 0)]` — `(child, parent)`, so `0 ≤ 1` |
| `bCE` | `[T(atom p)@0, T(atom q)@1]` |
| `phiK_valid` | `IValid phiK` — **proved** |
| `valuation_not_upward_closed` | `intExtractValuation bCE` is not upward closed along the frame — **proved** |
| `hvalid_body_false` | `¬ @IForces _ _ (intAccessPreorder edgesCE) (intExtractValuation bCE) intBotForces 0 phiK` — **proved** |

Since `hvalid`'s body is false at a witness while `IValid phiK` holds, `hvalid` is not a
consequence of `IValid φ`. **The `sorry` at `Completeness.lean:140` cannot be filled**, and by the
identical construction neither can `Minimal/Completeness.lean:128`.

**This does not refute `intuitionisticTableau_complete` itself** — the theorem is very likely true.
It refutes the *proof route*: `apply tableau_complete intScheme` throws away the fact that `b`
came from `intExpandBranches`, and no amount of persistence work restores it.

**Required fix** (mechanical, and independent of §3/§4): move the obligation to where the
provenance lives. Either

- (preferred) strengthen `openBranch_countermodel`'s conclusion to
  `∃ edges, (upward-closure of intExtractValuation b along intAccessPreorder edges) ∧ ¬IForces …`,
  and weaken `tableau_complete`'s `hvalid` to accept that upward-closure as a hypothesis; or
- restrict `hvalid` to `(b : IBranch Atom) → intExpandBranches … = .openBranch b → …`.

With either, DP-3/DP-4 collapse to `exact h Nat (intExtractValuation b) huc 0`-shaped one-liners.
`tableau_complete` stays sorry-free; `Soundness.lean` is untouched.

## 2. `IWorldHist` reuse audit (item 1)

`IWorldHist` (`Scheme.lean:3213-3243`) is an existential over four witness functions
`par`/`obl`/`sfor`/`fire` with clauses (H0), (H1), (H1-acc), (H2), (H3), (H3-exp), (H4), (H5).

**Reusable as-is** — no modification needed:

- `par : Nat → Nat` with (H0) `par 0 = 0` and (H1) `(c, par c) ∈ edges ∧ par c < c`. A genuine
  total unique-parent function, so ancestor chains are automatically **linear**. This is exactly
  the `ForestComparable` hypothesis Gate B's prototype assumed; it needs *exporting*, not building.
- (H1-acc) `∀ c', parAncestor par c' c → isAccessible edges c' c = true` — the bridge from
  `par`-ancestry to raw accessibility. Directly load-bearing for the ancestor sub-case.
- (H3) `∀ χ ∈ sfor c, χ ∈ posFormulasAt b c` — a **monotone planted positive-content fact**, the
  closest existing analogue to what positive-formula tracing needs.
- `IWorldHist_mono` (`:3263`) — branch/expanded-set monotonicity; the transfer lemma every
  non-minting arm uses. Any new companion clause of the same membership shape inherits this pattern.
- `IWorldHist_entry` (`:3251`) — vacuous entry discharge.
- `IAllWorldHist` (`:3330`) plus `IAllWorldHist_append`/`_map_const`, and the
  `IAllWorldHistCounter` family — the list-level plumbing a companion invariant would mirror.
- `intWorldHist_chain_le` (`:3618`), `pathOf` (`:3798`), `pathOf_some`/`pathOf_none`,
  `pathOf_injOn` (`:3843`), `intWorldHist_nw_le` (`:3944`) — pigeonhole/world-bound machinery.
  Relevant to *bounding*, largely **not** to persistence; do not budget these as reuse wins.
- `IAllUniv` (`:2834`), `IAllFuel` (`:4537`) with their `_append`/`_map` lemmas — already threaded
  through the whole `key` induction (Finding 1 of the prior dispatch).
- Phase 4's landed `applyAllTImpRules_copy_complete_of_fixpoint`,
  `applyPersistenceFixpoint_copy_complete`, and
  `applyPersistenceFixpoint_genuine_of_count_le_fuel`.
- `intFImpReuseWitnessAnc?_spec` (`Expansion.lean:321`) — the five-conjunct reuse fact, including
  the containment in §3.
- `intAccessPreorder_le_of_isAccessible` (`:276`), `isAccessible_one_step`,
  `sfAccessSat_edges_mono`.

**Must be built new**:

- A companion clause/invariant recording positive-content containment **across each recorded
  loop-back edge**, surviving to the final branch. `sfor c` records only the *mint-time* Sfor set
  of a created world; the reuse arm creates **no** world (`Scheme.lean:4705-4714` keeps `edges` and
  `nw` unchanged), so no existing clause covers the reuse pair `(x, w)` at all.
- The post-reuse closure lemma (§3) — the actual large piece.
- Multi-hop composition under `Relation.ReflTransGen` (still unconfirmed; see §5).
- The `hvalid`/`openBranch_countermodel` signature change (§1).

## 3. What the algorithm already guarantees (item 2, the de-risking finding)

**Edge direction, confirmed from source.** `isAccessible` (`Rules.lean:92-107`) filters
`fun (child, parent) => if parent == current`, so an edge is `(child, parent)` and accessibility
runs parent → child. The reuse arm appends `(x, l)` with `l = newEdge.2 = w`
(`Scheme.lean:6918`, `:6945`), i.e. **`w ≤ x`**. The reuse check also requires
`isAccessible edges x w` (`Expansion.lean:305`), i.e. **`x ≤ w`** in the raw relation.

So `x` and `w` become **preorder-equivalent** in the augmented frame. Upward closure of
`intExtractValuation` therefore demands that `w` and `x` **agree on atoms** in the final branch —
a much stronger demand than one-directional persistence, and the reason the "ancestor sub-case"
is not a notational inconvenience.

**The reuse check already enforces exactly this containment at reuse time.**
`intFImpReuseWitnessAnc?` (`Expansion.lean:296-307`):

```lean
-- Sfor(w') = {φ} ∪ posFormulasAt bPers w, read off newForms's sign = .pos sublist.
let sfor := newForms.filterMap fun sf => if sf.sign == .pos then some sf.formula else none
…
if isAccessible edges x w && x.ble w && sfor.all (forcedAtX.contains ·) && … then some x
```

Because `propagatePersistence` puts every positive formula of `w` into `newForms`, `sfor` **is**
`{φ} ∪ posFormulasAt bPers w`. The conjunct `sfor.all (forcedAtX.contains ·)` therefore states

> `posFormulasAt bPers w ⊆ posFormulasAt bPers x`

— precisely the backward containment the loop-back edge needs, already checked by the algorithm and
already exported as `hcont` by `intFImpReuseWitnessAnc?_spec`. Moreover `bPers` is
`applyPersistenceFixpoint b edges f`, so at reuse time `w` has *already* received every copy from
every raw ancestor (Phase 4's copy-completeness), and all of it is at `x`.

**Weaker sufficient statement.** Full per-formula origin tracing may be avoidable. The residual
obligation is only:

> No positive formula arrives at `w` after the reuse event without also being at `x`.

Post-reuse arrivals at `w` have exactly two sources, and both have a candidate cheap discharge:

- **Decomposition at `w`** of a premise already present at reuse time. That premise is at `x` by
  the containment above, and the final branch is **saturated** — `IBranchSaturation` is already in
  `intExpandBranches_openBranch_sat`'s conclusion — so the same decomposition is available at `x`.
- **A copy from a raw ancestor `y` of `w`.** `par`-linearity makes `y` and `x` comparable. If
  `y ≤ x`, the V4 copy channel delivers to `x` as well (it copies to all raw descendants). If
  `x ≤ y ≤ w`, it does not, and one recurses on `y`.

This reduces the problem from "trace every formula's origin" to "show post-reuse content at `w` is
covered at `x`", leaning on already-exported saturation plus already-landed copy-completeness.
**Flagged UNVERIFIED**: I did not prove this, and the `x ≤ y ≤ w` recursion is where it could
still collapse into full origin tracing. It is nonetheless a materially cheaper first attempt than
re-building `IWorldHist`, and should be attempted before the general machinery.

## 4. Refutation risk (item 4) — NEW, and the top priority

Gate B's PASS verdict analysed the *copy* argument's descendant and ancestor sub-cases. It did not
consider **independent beta-split choices**, which appear to break the statement outright.

**Candidate counterexample shape.** Let `T(r ∨ s)@w` be present at reuse time, with `r`, `s`
atoms. By the containment of §3, `T(r ∨ s)@x` is present too. These are two *distinct* signed
formulas (different labels), each expanded by its own beta rule, each splitting independently. A
single open branch may therefore select

- `T(r)@w` from the split at `w`, and
- `T(s)@x` from the split at `x`.

The copy channel sends `T(s)` from `x` down to `w` (raw `x ≤ w`), so `w` carries both `r` and `s`;
`x` carries only `s`. The augmented edge gives `w ≤ x`, so upward closure demands `T(r)@x` — which
is absent. **Atom-level persistence fails, and nothing forces the branch to close.**

Critically, the reuse check is **not re-run** after the augmented edge is recorded (the reuse arm
returns and the loop continues), so there is no mechanism to invalidate the loop-back edge when the
two worlds later diverge. This is the same *temporal* gap as §3, but in a form that may make the
statement **false** rather than merely hard.

**Status: UNVERIFIED.** I did not construct a concrete `φ0` realizing it, and it may be
unrealizable — the branch ordering in `intStepBranch` might always expand `T(r ∨ s)@x` before the
reuse fires at `w`, or such branches might always close for an independent reason.

**Recommended re-gate (Gate B2), before any build-out.** Cheap, and directly decisive:

1. Pick `φ0` forcing a disjunction under nested implications, so that a blocked world and its
   reused ancestor both carry the same disjunction.
2. Run `intExpandBranches` at `fuel ≥ 120`, take the open branch and the **augmented** edge list
   (the `augSets` witness, not raw `edgeSets`).
3. Decide atom-level persistence computationally: for all `w ≤ w'` in
   `intAccessPreorder augEdges` and all atoms `p`, check
   `intExtractValuation b w p → intExtractValuation b w' p`. All three are decidable, so `decide`
   or a `Bool`-valued harness suffices — the same empirical style Gate A used.
4. **A single failing instance is a refutation** ⇒ verdict (c), permanent deferral of DP-3/DP-4/DP-5,
   with the quotient/blocking-frame route remaining prohibited.

## 5. Decomposition (item 3)

Ordered; each sub-phase sized for one agent run. Sub-phase 0 is gating.

0. **Gate B2 — beta-split refutation probe** (§4). GATING. If it fails, stop: permanent deferral.
1. **Statement-shape fix** (§1). Independent of 0 and of all persistence work; can proceed in
   parallel. Strengthen `openBranch_countermodel`'s conclusion with the upward-closure conjunct and
   weaken `tableau_complete`'s `hvalid` to accept it. Leaves the persistence premise as the only
   remaining hole, now stated where `b`'s provenance is in scope.
2. **Export raw-edge persistence** (prior dispatch's Finding 1). Add the raw-edge conjunct to
   `intExpandBranches_openBranch_sat`'s conclusion from the already-threaded `IAllUniv`/`IAllFuel`
   plus Phase 4's two lemmas. Cheap; a stepping stone, not sufficient alone.
3. **Export reuse-time containment.** Thread `posFormulasAt bPers w ⊆ posFormulasAt bPers x` as a
   monotone planted fact per recorded loop-back edge, surviving to the final branch — a companion
   invariant beside `IAllAccessConsistent`, mirroring its companion-not-merged pattern, reusing
   `IWorldHist_mono`'s shape and the `IAllWorldHist_append`/`_map_const` plumbing.
4. **Post-reuse closure lemma** (§3, the large piece). Attempt the saturation + copy-completeness
   route first; fall back to full origin tracing only if the `x ≤ y ≤ w` recursion forces it.
5. **Multi-hop composition.** Confirm the single-hop lemma composes under `Relation.ReflTransGen`
   when a branch accumulates several reuse events. Still unconfirmed — the prior dispatch's item 3,
   which Gate B never re-checked.
6. **Discharge DP-5** (`Scheme.lean:727`) from the exported invariant.
7. **Discharge DP-3/DP-4** at atom shape — mechanical once 1 and 6 land.
8. **Final CI**: `lake build`, `checkInitImports`, `lint`, `lint-style`, `shake`, `test`,
   `TableauConformance`; `lean_verify` for axiom cleanliness; confirm DP-2 untouched.

## Line-number corrections

The task description's line numbers predate Phases 3-4. Current, verified by content:

| Sorry | Description says | Actual |
|---|---|---|
| DP-5 | `Scheme.lean:633` | **`Scheme.lean:727`** |
| DP-3 | `Completeness.lean:140` | `Completeness.lean:140` (unchanged) |
| DP-4 | `Minimal/Completeness.lean:128` | `Minimal/Completeness.lean:128` (unchanged) |
| DP-2 | `Scheme.lean:2605` | referenced at `Scheme.lean:2820` (retired, untouched) |

Bare-sorry count in task scope: exactly 3 (DP-3, DP-4, DP-5).

## Artifacts

- `scratch/HvalidShapeRefutation.lean` — the §1 refutation, `lake env lean` clean, zero sorries.
