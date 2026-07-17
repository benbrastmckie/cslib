# Report 08 — Mint-arm witness-reuse gap: route decision (a / b / Fallback 4)

**Task**: 515 (`s5_universal_rule_termination_unblock_504`)
**Question**: How to resolve the Phase 19 mint-arm witness-reuse soundness gap (handoff 10) —
Route (a) rule-level guard + termination re-derivation, Route (b) Euclidean-closure model repair,
or Fallback 4 (accept the S5-only green partial).

## Verdict

**Route (a)** — a root-aware guard on the mint arms, with the tag-injection termination bound
re-derived under a root-class / cluster-class split. It is the **only sound-and-bounded** path.
**Route (b) is dead** (killed below by box anti-monotonicity + closure-vacuity). Fallback 4 is a
legitimate terminus *only if* Route (a)'s termination re-derivation is later judged not worth its
cost — it is not warranted on soundness grounds.

**Confidence**: high that Route (b) is dead; high that Route (a) is mathematically sound and
world-bounded remains **linear**; medium on the *Lean* cost of re-deriving the termination bound
(it is bounded, but is genuinely its own phase, not a local patch).

**Critical scoping fact for the orchestrator**: Route (a) does **not** fit one more implementation
dispatch. The termination re-derivation is Phase-6/7-scale, and Phases 20–23 sit on top. This
orchestration run ends in a **partial** regardless of which route is chosen; the decision here is
about the *project's* forward path, and what to bake into the plan for the next `/research +
/plan` cycle.

## Why Route (b) is dead (decisive, two independent kills)

Route (b) = "leave the rule unchanged; in the soundness proof, close `m.r` under
right-Euclideanness so the reuse edge holds."

**Kill 1 — closure is vacuous in the soundness direction.** In `modalTableauFive_sound` the model
`m` is *given to satisfy* `fiveFC`, i.e. `m.r` is **already** `RightEuclidean`
(`FrameSoundness.lean:1284`, `fiveFC := RightEuclidean r`). By `EuclGen.least` (`m.r` is a
right-Euclidean relation containing itself ⇒ `EuclGen m.r ⊆ m.r`) together with `EuclGen.mono`
(`m.r ⊆ EuclGen m.r`), **`EuclGen m.r = m.r`**. Closing an already-closed relation adds no edges,
so it cannot supply the missing `m.r (f w) (f w')`. The `EuclGen` API — built for the
*completeness* direction (Phase 20, where the canonical relation is *not* yet Euclidean) — does
nothing on the soundness side.

**Kill 2 — "add the reuse pair, then close" breaks box formulas (anti-monotonicity).** The only
non-vacuous reading is `r' := EuclGen (m.r ∪ {(f w, f w')})`, adding the edge by fiat then
re-closing. Box formulas are anti-monotone in the relation, and the branch carries box formulas at
the very world being edited. Concrete killer (realizable, not asserted):

- Branch: `T(◇p)@w`, `T(□q)@w` (same trigger world `w`), and `T(p)@w'` with `w'` a *separate*
  world satisfying `p` but **not** `q`.
- Model `m`: `w → a`, with `a ⊨ p ∧ q`. Then `Satisfies m w (◇p)` ✓ (via `a`) and
  `Satisfies m w (□q)` ✓ (every current successor `a ⊨ q`). `w'` is not an `m`-successor of `w`.
- `witnessWorldS5 b .pos p` may return `w'` (it checks only the *syntactic* presence of `⟨.pos, p, w'⟩`
  on the branch — see `S5Simplification.lean:521`, `.find?` over `modalKnownWorlds`), so the rule
  adds edge `w → w'`.
- In `r'` the world `w` now has successor `w'` with `w' ⊭ q`, so `Satisfies m' w (□q)` is **false**.
  A branch formula that held has been falsified. Route (b) does not "preserve satisfaction"; it
  destroys it.

This is exactly the anti-monotonicity the directive asked to stress, and it fires on an ordinary
branch (a world carrying both a diamond and a box — the generic case). No "closure preserves
satisfaction" lemma can exist, because the statement is **false**. Route (b) is dead.

## Why Route (a) is sound and stays linearly world-bounded

The gap is entirely the **root's asymmetry**, in the mint arms this time (the same root asymmetry
Route 1 fixed for the propagation arms). `s5FC` is an equivalence relation
(`FrameSoundness.lean:1275`, `Refl ∧ RightEuclidean`), so in S5 *any* two known worlds are related
(`accReachableInv_related_s5`) and witness reuse never adds a semantically-absent edge. `fiveFC`
drops reflexivity, so relatedness holds **only** between two non-root cluster members
(`accReachableInv_related_five`, both endpoints non-root, `:1451`). Two unsound sub-cases:

- **Root as witness** (`w' = 0`): world `0` has in-degree zero in a rooted tableau (nothing emits
  an edge *into* the root), and `reachable_imp_cod_related_five` never has `f 0` as its target
  endpoint. **Fix**: exclude `0` from witness candidacy. This never forces a second mint of an
  already-minted tag, because a formula sitting at the *root* was never *minted* (root formulas
  arrive by decomposition, not by `witnessWorldS5`), so it never consumed a `(sign, subformula)`
  tag — minting fresh for it is that tag's *first* mint.
- **Root as trigger** (`w = 0`, reusing non-root `w'` with no recorded `0 → w'` edge): needs
  `m.r (f 0) (f w')`, which `RightEuclidean` does not force. **Fix**: root-triggered mint arms
  mint fresh (equivalently: reuse only under an `acc.hasEdge 0 w'` guard, symmetric to Route 1).

**Termination survives, still linear.** The landed bound
(`modalMaxWorld_lt_worldBound_of_S5w`, Phases 6/7) rests on "≤ one mint per `(sign, subformula)`
tag." Under the guard, the invariant refines to "≤ one mint per tag **per source-class**
{root, non-root}." The root contributes at most one mint per tag, bounded by the root's own
diamond / negated-box subformulas (≤ `|modalSubfmls φ₀|`); the non-root cluster contributes at
most one mint per tag as before. New world bound ≈ `2 · |modalSubfmls φ₀|` — a larger **constant**,
still **linear**, decidability unaffected.

**Honest cost.** Mathematically bounded; in Lean it is *not* a local patch. `witnessWorldS5`'s
guard changes the mint-arm output, so `modalApplyOneFive_specCore`'s world-bound fields and the
`mintTags`/`usedTags`/`S5wTagInv`/`S5wWorldInv` chain that feeds
`modalMaxWorld_lt_worldBound_of_S5w` must be re-stated for the source-split invariant and
re-proved. That is Phase-6/7-scale work — its own phase(s), and it must be re-derived *before* the
`modalStepBranchFive_preserves_satIn` soundness assembly (which then discharges cleanly, since the
guard guarantees every reuse edge is either a genuine `m.r` edge (non-root/non-root, via
`accReachableInv_related_five`) or a freshly-minted successor).

## Blast radius

- `FiveSimplification.lean`: guard the two mint arms (root-trigger ⇒ mint; exclude `0` as witness);
  re-verify `modalApplyOneFive_specCore` (world-bound fields **loosen** on the reuse side but the
  mint side gains the root-class allowance — net linear).
- Termination chain (the `S5w*` invariants + `modalMaxWorld_lt_worldBound_of_S5w`): re-derive under
  the source-split tag invariant. **This is the real cost and the real risk.**
- `FrameSoundness.lean`: then `modalStepBranchFive_preserves_satIn` + `modalTableauFive_sound`
  assemble on top, reusing every green Milestone-1–3 piece from handoff 10 unchanged.
- `GenericDriver.lean`: **not touched** (mint arms emit via the existing `freshLocal` one-edge
  contract; the guard only *narrows* when reuse fires).

## Recommendation to the orchestrator (this run) and the project (next cycle)

1. **This run**: land the current green partial. Per plan **R9**, Phases 0–14 (S5), Phase 18 (the
   `modalApplyOneFive` rule + termination), and the Phase-19 soundness building blocks
   (`accReachableInv_related_five`, `FiveSoundInv`, the three handoff-10 milestones) are all
   green/committed — a real partial delivery, **not** a failure. Mark the 5/KB5 chain
   (Phase-19 capstone – 23) `[BLOCKED]` with **Route (a) selected** and this report cited, so the
   diagnosis is not re-discovered a third time.
2. **Next project cycle** (fresh `/research` is *not* needed — this report is the research;
   go straight to `/revise`/`/plan`): re-scope Phase 19 into
   **19a** (guarded mint arms + termination-bound re-derivation under the source-split invariant —
   its own phase, with a KILL budget) and **19b** (the `modalTableauFive_sound` assembly). Only if
   19a's termination re-derivation blows its KILL budget does **Fallback 4** (permanent S5-only
   delivery) become the terminus.
3. **Do not** attempt Route (b) — the "closure preserves satisfaction" lemma it needs is provably
   false (Kill 2).

Route (a) is the honest answer to "no matter the cost": the deliverable is genuinely reachable and
soundly bounded; the cost is a dedicated termination-bound re-derivation phase, which the plan
should schedule explicitly rather than have an implementer improvise.
