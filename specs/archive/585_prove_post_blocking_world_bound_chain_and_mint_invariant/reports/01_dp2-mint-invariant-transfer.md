# DP-2: Runtime-Check-to-Final-Branch Transfer and the Fresh-Mint World-Bound Invariant

**Task**: 585 — prove_post_blocking_world_bound_chain_and_mint_invariant
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
**Scope**: DP-2 only (`intFreshMint_preserves_nw`, `Scheme.lean:2602-2605`)
**Repo state**: commit `37e75e68` (description cites `640b68d4`; all declarations re-located by
name and content, line numbers below verified against `37e75e68`)
**Session**: sess_1785342409_76dad9

---

## 0. Executive summary

Five findings, in order of consequence for the plan:

1. **The description's proposed premise shape does not work.** Restating
   `intFreshMint_preserves_nw` with the numeric strict premise `nw < WBound φ0` and "threading
   that premise through the fresh-mint arm" is **not inductive**: after the mint the counter is
   `nw + 1`, and `nw < WBound φ0` gives only `nw + 1 ≤ WBound φ0`, not `nw + 1 < WBound φ0`,
   which is what the *next* mint on the same branch needs. No purely numeric strengthening of
   `IAllNW` is preserved by the mint arm. The threaded invariant **must be structural**; the
   numeric bound must be a *derived corollary*, re-derived at each consumption site.

2. **The correct threaded object is a creation-history invariant over `(b, e, nw, edges)`.** The
   counter is redundant with structure: `edges` grows by exactly one pair per mint and by nothing
   else, so `nw = edges.length + 1` is an exactly-preserved invariant (Section 3.1). Bounding
   `nw` therefore reduces to bounding the size of the created-world tree recorded in `edges`.

3. **The runtime-check-to-final-branch transfer, as `intCreatedChain_le`'s `hunb` is currently
   stated, is not derivable — and does not need to be.** Conjunct 3 of the reuse check moves the
   wrong way under branch growth (Section 4.1: a *refutation* of the naive transfer). But the
   obligation can be discharged at *mint time* into a **snapshot-free residual fact** (★ in
   Section 4.2) that is permanently true and needs no ghost history of branch states. This is the
   central new result of this research and it is what unblocks DP-2 in principle.

4. **DP-2 is not a leaf lemma; it is the finite-model-property core of the whole intuitionistic
   completeness development.** `hNW` exists only to keep `hUniv`, which exists only to keep
   `hFuel`, which exists only to refute the fuel-exhaustion arm (`case3`,
   `Scheme.lean:4969-4997`). Discharging DP-2 = proving the tableau saturates. Two independent
   "cheap route" candidates were checked and both are **provably circular** (Section 6).

5. **Honest scope**: ~900-1400 lines of new Lean across six sub-developments, two of which
   (`isAccessible` one-hop extension; the tree-size cardinality injection) are self-contained but
   nontrivial. Section 8 gives the phase decomposition and an explicit go/no-go criterion for
   `[BLOCKED]` per the task's binding constraints.

---

## 1. Verified ground state

All facts below were read from the files, not inferred from the task description.

| Fact | Location | Verified content |
|---|---|---|
| DP-2 sorry | `Scheme.lean:2602-2605` | `intFreshMint_preserves_nw {φ0} {nw} (hnwB : nw ≤ WBound φ0) : nw + 1 ≤ WBound φ0 := by sorry` |
| Sole call site | `Scheme.lean:5362-5363` | `have hNW_ext : nw' ≤ WBound φ0 := by rw [hnw'_eq]; exact intFreshMint_preserves_nw hNWP_head` — inside `case7`, the fresh-mint arm |
| `hNWP_head` origin | `Scheme.lean:5299` | `hNWP nwH List.mem_cons_self`, i.e. the bare `IAllNW` head — confirms the docstring's claim that this is the only locally available fact |
| `IAllNW` | `Scheme.lean:2416-2417` | `∀ nw ∈ nws, nw ≤ WBound φ0` |
| `WBound` | `Scheme.lean:1692-1693` | `((intSubfmls φ).toFinset.card + 1) ^ (intChainBound φ + 1)` |
| `intChainBound` | `Scheme.lean:1683-1684` | `2 ^ (intSubfmls φ).toFinset.card * (intSubfmls φ).toFinset.card` |
| `intCreatedChain_le` | `Scheme.lean:1757-1814` | Proved, sorry-free. `hunb` quantifies the five reuse conjuncts **against the final branch `b`** |
| Bare sorries in subtree | grep, whole subtree | exactly 4: `Scheme.lean:633`, `Scheme.lean:2605`, `Intuitionistic/Completeness.lean:140`, `Minimal/Completeness.lean:128` — matches the description |

Engine facts read from `intExpandBranches.go` (`Scheme.lean:3206-3338`):

- `edges` is appended to in **exactly one arm**: the fresh-mint arm, `doneEdges ++ [edges ++ [newE]] ++ restEdges` (line 3272). The alpha arm (3249), reuse arm (3263) and beta arm (3282) all pass `edges` through unchanged.
- `nw` increments in **exactly the same arm** (`nw'` at line 3271); `intApplyRuleFull_linearResult_nextWorld` (`Scheme.lean:2494-2522`) proves `nw' = nw + 1` on the world-creating arm and `nw' = nw` elsewhere.
- `newE = (w', w) = (nw, l)` where `l = sf.label` of the fired `F(φ → ψ)` — from `intFImpRule` (`Rules.lean:159-164`), which returns edge `(w', w)` with `w' = nextWorld`. `IEdges` pairs are `(child, parent)` (`Rules.lean:80-85`).
- The branch is **monotone along any lineage**: `Branch.extendMany b sfs = sfs ++ b` (`Foundations/Logic/Tableau/Branch.lean:62`) and `applyPersistenceFixpoint` only appends (`applyPersistenceFixpoint_mem_preserved`, used at `Scheme.lean:5341`).
- **Non-closure is available at the mint site**: `case7` opens with `rw [if_neg hcl] at hgo` (line 5295) where `hcl : ¬(closurePred bPers = true)`.
- The fired formula and its freshness are available: `intStepBranch_some_exists_fuel hstep` (`Scheme.lean:3163-3182`) yields `sf ∈ bPers ∧ e.any (· == sf) = false ∧ intApplyRuleFull sf nw bPers = … ∧ newExp = e ++ [sf]`. This is the hook for the branching-factor bound.
- Entry state (`openBranch_countermodel`, `Scheme.lean:5578`): `branches = [[⟨.neg, φ, 0⟩]]`, `nextWorlds = [1]`, `edgeSets = [[]]`.

---

## 2. Why the lemma as written is false, and what `hNW` is actually for

`hnwB : nw ≤ WBound φ0` is consistent with `nw = WBound φ0`; the conclusion is then
`WBound φ0 + 1 ≤ WBound φ0`. The docstring at `Scheme.lean:2587-2589` states this correctly.

What is *not* stated anywhere, and matters for planning: **`hNW` has no independent purpose.**
Tracing consumers:

- `hnwB` is consumed only by `intApplyRuleFull_outputs_subset_ext` (`Scheme.lean:2345-2346`, via
  `mem_intUniverseExt_of hnw`), to place the newly minted label inside `intUniverseExt φ0`
  (whose label range is `List.range (WBound φ + 1)`, `Scheme.lean:2108`).
- That is used by `intStepBranch_linear_preserves_univ` / `_branch_preserves_univ`
  (`Scheme.lean:2451`, `2472`) to keep `IAllUniv`.
- `IAllUniv` is used only to feed `intWork_drop`'s `sf ∈ intUniverseExt φ0` premise
  (`Scheme.lean:5364-5371`), i.e. to keep `IAllFuel`.
- `IAllFuel` is used only in `case3` (`Scheme.lean:4995-4997`) to refute the per-branch
  fuel-exhaustion arm by `intWork … < 0`.

So the chain is `hNW → hUniv → hFuel → "the engine never exhausts fuel"`. **DP-2 is the
finite-model property.** The plan must be written knowing this, not as if a numeric arithmetic
lemma were missing.

---

## 3. The correct restatement

### 3.1 The counter is redundant with `edges`

```lean
-- exactly preserved by all four arms; entry gives 1 = 0 + 1
IAllNWEdges : nw = edges.length + 1
```

Only the mint arm changes either side, and it changes both by one. This converts the "runtime
counter" into a structural quantity and is the first, cheap step of the transfer the task asks
about. It is a parallel-list invariant over `(pendingNW, pendingEdges)` in the same "companion,
not merged" shape as `IAllConsistent`/`IAllAccessConsistent`, and both lists are already threaded
through the induction with length hypotheses (`hLenP`, `Scheme.lean:4889`).

### 3.2 The invariant that must be threaded (replacing / accompanying `IAllNW`)

Per-branch, over the state `(b, e, nw, edges)`:

```lean
private def IWorldHist (φ0 : Proposition Atom) (b : IBranch Atom) (e : List (ISF Atom))
    (nw : Nat) (edges : IEdges) : Prop :=
  ∃ (par : Nat → Nat) (obl : Nat → Proposition Atom)
    (sfor : Nat → List (Proposition Atom)) (fire : Nat → Proposition Atom),
    ∀ c, 1 ≤ c → c < nw →
      -- (H1) tree structure
      (c, par c) ∈ edges ∧ par c < c ∧
      -- (H2) universe containment of the recorded data
      obl c ∈ intSubfmls φ0 ∧ fire c ∈ intSubfmls φ0 ∧
      (∀ χ ∈ sfor c, χ ∈ intSubfmls φ0) ∧
      -- (H3) planted, monotone facts (survive every later append to b)
      (⟨.neg, obl c, c⟩ : ISF Atom) ∈ b ∧
      (∀ χ ∈ sfor c, χ ∈ posFormulasAt b c) ∧
      -- (H4) sibling uniqueness: (parent, fired implication) determines the child
      (∀ c', 1 ≤ c' → c' < nw → par c = par c' → fire c = fire c' → c = c') ∧
      -- (H5) the snapshot-free residue of the mint-time reuse check  (★, Section 4.2)
      (∀ c', 1 ≤ c' → c' < c → parAncestor par c' (par c) → obl c' = obl c →
        ¬ (∀ χ ∈ sfor c, χ ∈ sfor c'))
```

where `parAncestor par x y` is reflexive-transitive iteration of `par` (well-founded by
`par c < c`). Every clause is either about fixed arithmetic/subformula data (H1, H2, H4, H5) or
monotone in `b` (H3) — **no branch snapshot appears anywhere**. That is the property that makes
the invariant threadable at all.

### 3.3 The restated lemma

`intFreshMint_preserves_nw` should stop being a numeric transfer lemma. The honest replacement is

```lean
/-- The post-blocking world bound, derived from the creation-history invariant. -/
private lemma intWorldHist_nw_le {φ0 : Proposition Atom} {b e nw edges}
    (hHist : IWorldHist φ0 b e nw edges) : nw ≤ WBound φ0
```

applied at the call site to the **post-mint** state (branch `Branch.extendMany bPers newForms`,
edges `edges ++ [newE]`, counter `nw + 1`), yielding `nw + 1 ≤ WBound φ0` directly — which is
exactly `hNW_ext` at `Scheme.lean:5362`. If the planner prefers to keep the declaration name for
continuity, the acceptable strengthened form is

```lean
private lemma intFreshMint_preserves_nw {φ0 : Proposition Atom} {b e nw edges}
    (hHist : IWorldHist φ0 (Branch.extendMany bPers newForms) (e ++ [sf]) (nw + 1)
               (edges ++ [newE])) :
    nw + 1 ≤ WBound φ0
```

i.e. the premise is the post-mint history invariant, discharged at the call site by the mint-arm
preservation lemma. **This satisfies the acceptance gate's "premise must be discharged at the
call site"** only because `IWorldHist` is itself established inductively — which is the bulk of
the work (Section 5).

---

## 4. The transfer: refutation of the naive route, and the route that works

### 4.1 Refutation — `intCreatedChain_le`'s `hunb` cannot be supplied by monotonicity

`hunb` (`Scheme.lean:1765-1769`) demands, at every creation site `j`, that **no** `x` satisfies
the five conjuncts *evaluated against the final branch `b`*. The runtime fact is that
`intFImpReuseWitnessAnc? bPers edges newForms newE = none`, i.e. no `x` satisfies the five
conjuncts *against the mint-time branch `bPers`*. To supply `hunb` one needs
`final conjuncts → runtime conjuncts`. Conjunct-by-conjunct:

| # | Final form (`intCreatedChain_le`) | Runtime form (`intFImpReuseWitnessAnc?`, `Expansion.lean:279-283`) | Transfer |
|---|---|---|---|
| 1 | `isAccessible edges_final x (ws j)` | `isAccessible edges_j x w` | needs edge-stability lemma (Section 5.1) — obtainable |
| 2 | `x ≤ ws j` | `x.ble w` | identical |
| 3 | `∀ χ ∈ posFormulasAt b_final (ws (j+1)), χ ∈ posFormulasAt b_final x` | `sfor ⊆ posFormulasAt bPers x` | **fails** |
| 4 | `ψ ∉ posFormulasAt b_final (…)` | `¬ (posFormulasAt bPers x).contains ψ` | anti-monotone; needs openness at time `j` |
| 5 | `⟨.neg, ψ, x⟩ ∈ b_final` | `bPers.any (…)` | monotone the wrong way, but obtainable from planting |

Conjunct 3 is the killer. The final form gives `sfor ⊆ posFormulasAt b_final x`; the runtime form
requires `sfor ⊆ posFormulasAt bPers x` with `bPers ⊆ b_final`. Positive content at `x` only
grows, so the final containment is strictly weaker at the right-hand side and the implication runs
backwards. **There is no monotonicity argument that recovers it**, and no additional invariant
about `b_final` fixes it, because the gap is a genuine loss of information about *when* a formula
arrived at `x`.

This is a real, hard negative result and it explains precisely why `intCreatedChain_le`'s
docstring (`Scheme.lean:1749-1751`) delegates the transfer without performing it. **The plan must
not attempt this route.**

### 4.2 The route that works — discharge at mint time into a snapshot-free residue

Invert the direction: instead of transporting the runtime `none` forward to the final branch,
**consume it immediately, at the mint, while `bPers` is still the current state**, and keep only
what survives.

At the mint of world `c = nw` from parent `p = l` with obligation `ψ` and propagated positive set
`sfor = φ :: posFormulasAt bPers l` (`intFImpRule`, `Rules.lean:162-164`; the `sfor` projection is
exactly `newForms.filterMap (pos)`, cf. `Scheme.lean:5214-5216`), the runtime check returned
`none`. For an arbitrary already-created world `c'` with `1 ≤ c' < c` that is a `par`-ancestor of
`p` and has `obl c' = ψ`, instantiate the `none` at `x := c'`:

- `c'` **is** among the candidate labels `(bPers.map (·.label)).eraseDups`, because
  `⟨.neg, obl c', c'⟩ ∈ bPers` by (H3). *(This needs a new `_none` spec lemma — Section 5.2.)*
- conjunct 1 holds: `c'` is a `par`-ancestor of `p`, and each `par` step is a member of `edges`
  by (H1), so `isAccessible edges c' p = true` by `isAccessible_one_step` (`Scheme.lean:293`) plus
  a one-hop extension lemma (Section 5.1).
- conjunct 2 holds: `c' < c` and `par`-ancestors have smaller labels (`par c < c`, (H1)).
- conjunct 4 holds: `⟨.neg, obl c', c'⟩ ∈ bPers` by (H3) and `bPers` is **not closed** (`hcl`),
  so `obl c' ∉ posFormulasAt bPers c'` — via `IntMinScheme.no_contradiction`
  (`Scheme.lean:163-166`), see Section 5.3.
- conjunct 5 holds: same (H3) fact, with `obl c' = ψ`.

Therefore conjunct 3 must fail: `¬ (sfor ⊆ posFormulasAt bPers c')`. But (H3) gives
`sfor c' ⊆ posFormulasAt bPers c'`. Hence

> **(★)  `¬ (sfor c ⊆ sfor c')`.**

`(★)` mentions only the two recorded creation-time sets — **no branch, no edge list, no snapshot**.
It is therefore permanently true and is exactly clause (H5) of `IWorldHist`. This is the
"runtime-check-to-final-branch transfer" the task description calls genuinely unproven research
work; the resolution is that the transfer to the *final* branch is unnecessary and impossible,
while the transfer to a *snapshot-free residue* is available and cheap at the mint site.

### 4.3 Depth bound from (★)

Along any `par`-ancestor chain of created worlds, the pairs `((sfor c).toFinset, obl c)` are
pairwise distinct: if two chain members `c' < c` had equal pairs, (★) would be contradicted by
`sfor c ⊆ sfor c'`. The pairs live in
`(intSubfmls φ0).toFinset.powerset ×ˢ (intSubfmls φ0).toFinset`, of cardinality
`2 ^ card * card = intChainBound φ0` (`Scheme.lean:1683-1684`). So

> chain length ≤ `intChainBound φ0`.

This is the same pigeonhole `intCreatedChain_le` already performs (`Scheme.lean:1774-1814`); the
proof transfers essentially verbatim with `posFormulasAt b (ws (i+1))` replaced by `sfor` and
`hunb` replaced by (★). **`intCreatedChain_le` itself stays untouched and sorry-free**; the new
lemma is a sibling, not an edit. (Note: the existing lemma then becomes unconsumed by this route.
That is acceptable and should be recorded in its docstring, not deleted — it is a correct lemma
and the negative result in 4.1 is worth preserving next to it.)

### 4.4 Branching bound

Children of `p` are in bijection with distinct `(p, fire c)` pairs by (H4), and
`fire c ∈ intSubfmls φ0` by (H2). Hence out-degree ≤ `(intSubfmls φ0).toFinset.card`.
(H4) is established at the mint from `intStepBranch_some_exists_fuel`'s
`e.any (· == sf) = false` together with `newExp = e ++ [sf]`: the expanded set is duplicate-free
along a lineage and never shrinks, so the triple `⟨.neg, χ, p⟩` fires at most once.

### 4.5 The size bound — and why `WBound`'s exact shape is the target

`WBound φ = (B + 1) ^ (D + 1)` with `B = (intSubfmls φ).toFinset.card` and
`D = intChainBound φ`. This is **exactly** `Fintype.card (Fin (D+1) → Option S)` where `S` has
`B` elements — verified: `Fintype.card_pi_const : Fintype.card (Fin n → α) = Fintype.card α ^ n`
(Mathlib, `Mathlib.Data.Fintype.BigOperators`). So the intended final step is an **injection**

```
{0, …, nw-1}  ↪  (Fin (intChainBound φ0 + 1) → Option {χ // χ ∈ (intSubfmls φ0).toFinset})
c ↦ its root-to-`c` path of fired implications, padded with `none`
```

injective by (H4) (each step of the path is determined by parent + fired formula) and
well-defined by 4.3 (path length ≤ `D`). Then `nw ≤ WBound φ0` by
`Finset.card_le_card_of_injOn`. The definition of `WBound` was clearly authored with this
encoding in mind; matching it exactly avoids any arithmetic slack argument.

---

## 5. Concrete new obligations (all verified as currently absent)

### 5.1 `isAccessible` one-hop extension
Needed: `(c, p) ∈ edges → isAccessible edges x p = true → isAccessible edges x c = true`.
Present today: `isAccessible_one_step` (`Scheme.lean:293-305`),
`isAccessible_go_append_mono` (`310`), `isAccessible_go_fuel_mono` (`339`). **Transitivity /
one-hop extension is absent** — `Scheme.lean:250` explicitly declines to prove it ("sound
regardless of whether `isAccessible edges` is already transitive"). `isAccessible` is a
fuel-bounded DFS with `fuel = edges.length` (`Rules.lean:92-107`); since `par c < c` makes every
path strictly increasing, path length is bounded by `edges.length`, so the fuel suffices. Expect
~100-180 lines.

Note: with the (★) route, the **edge-stability** direction (new edges never create new ancestry
into old nodes) is *not* required — ancestry is used positively only, via the `par` function,
which is stable by construction.

### 5.2 `intFImpReuseWitnessAnc?_none_spec`
Present: only the `some` direction (`Expansion.lean:295-322`). Needed: if the function returns
`none` and `x ∈ (bPers.map (·.label)).eraseDups` and the obligation lookup succeeds, then the
five conjuncts fail at `x`. Mechanical from `List.findSome?_eq_none` plus the same `if`-unfold the
existing spec uses. **This does not edit `intFImpReuseWitnessAnc?`** and so does not violate the
binding constraint. ~40-70 lines. Recommend placing it in `Expansion.lean` next to its sibling.

### 5.3 A `closurePred` hypothesis on `intExpandBranches_openBranch_sat`
Conjunct 4 of 4.2 needs: `closurePred b = false → ⟨.neg, ψ, w⟩ ∈ b → ψ ∉ posFormulasAt b w`.
`intExpandBranches_openBranch_sat` (`Scheme.lean:4856-4874`) takes `closurePred` as a bare
parameter with no properties. **The needed property already exists as a scheme field**:
`IntMinScheme.no_contradiction` (`Scheme.lean:163-166`), proved for both schemes. Add it as a
hypothesis to `intExpandBranches_openBranch_sat` and discharge it at the single call site
(`openBranch_countermodel`, `Scheme.lean:5597-5609`) with `S.no_contradiction`. This is a
hypothesis that **is** discharged at its call site, so it is not a weakening.

### 5.4 Strict label bound
`ILabelBound b nw := ∀ sf ∈ b, sf.label ≤ nw` (`Scheme.lean:953-954`) is too weak for
`par c < c`. A parallel strict form (`< nw`) is needed. Entry: `[⟨.neg, φ, 0⟩]` with `nw = 1`;
mint: new labels `= nw < nw + 1`; alpha/beta: labels unchanged. Cheap (~60 lines), but must be
threaded as a genuine parallel invariant, not derived.

### 5.5 `IWorldHist` preservation across all four arms + entry
The bulk. Entry is vacuous (`nw = 1`, no `c` with `1 ≤ c < 1`). Alpha, beta and reuse arms
preserve everything by monotonicity of `b` and constancy of `nw`/`edges`. The mint arm is where
(★) is manufactured (Section 4.2) and where the existential witnesses are extended by one point.
Expect ~350-550 lines including the append/map plumbing lemmas mirroring
`IAllNW_append`/`IAllNW_map_const` (`Scheme.lean:2421`, `2433`).

### 5.6 The counting lemmas
4.3 (pigeonhole, ~120 lines, adapted from `intCreatedChain_le`'s body) and 4.5 (path injection
into `Fin (D+1) → Option S`, ~200-350 lines: `parIter`, depth, path construction, injectivity,
`Finset.card_le_card_of_injOn`, `Fintype.card_pi_const`).

---

## 6. Cheap routes checked and refuted

Both are recorded so the plan does not re-derive them.

**(a) Bound the counter by the fuel.** `nw + f` is non-increasing along a lineage (each mint
spends one fuel), so `nw ≤ 1 + intFuelExt φ0` is trivially provable. It is useless:
`intFuelExt φ = 4 * (2 * φ.complexity + 1) * (WBound φ + 1) + 1` (`Scheme.lean:1720-1721`) is
strictly **larger** than `WBound φ`. Resizing `intUniverseExt`'s label range to `intFuelExt`
instead is circular: `intFuelExt` must dominate `2 * (intUniverseExt φ).length` (that is what
`intWork_init_lt_intFuelExt` needs, `Scheme.lean:3370`) and
`(intUniverseExt φ).length ≤ 2 * (2 * φ.complexity + 1) * (L + 1)` where `L` is the label bound
(`intUniverseExt_length_le`, `Scheme.lean:2117`). Setting `L := intFuelExt` yields
`F ≥ 4(2c+1)(F+1)`, which has no solution in `ℕ`. **Provably circular.**

**(b) Count worlds without the tree.** Two created worlds with the same `(sfor, obl)` pair
conflict only when one is an ancestor of the other — the check is ancestor-directed by design
(`Expansion.lean:231-246`). Siblings never block each other, so a flat pigeonhole over pairs gives
no bound. `depth × branching` is unavoidable, and `WBound`'s definition already encodes exactly
that product.

---

## 7. Interaction with the concurrent task

`specs/430_prove_atom_persistence_upward_closure_for_intexpan/` owns DP-3/DP-4/DP-5 and also edits
`Scheme.lean`. Territory analysis:

- **This task's edits**: `Scheme.lean:2354-2605` (the `hUniv`/`hNW` invariant block), the
  `case6`/`case7` arms of `intExpandBranches_openBranch_sat` (~`5120-5400`), that lemma's
  signature (`4856-4874`), its call site (`5597-5609`), plus a new lemma in `Expansion.lean`
  and possibly a new section near `intCreatedChain_le` (`1757`).
- **The other task's edits**: `truthLemma`'s T-imp case (`Scheme.lean:633`) and the two
  `Completeness.lean` files.
- **Overlap**: none at the line level, but both touch `Scheme.lean` and the other task's widened
  scope ("positive-formula persistence along the augmented relation") is *conceptually adjacent*
  to (H3). Serialize; do not run concurrently. If a persistence/upward-closure lemma lands from
  that task, check whether it subsumes (H3) before re-proving it.

---

## 8. Recommended phase decomposition and the go/no-go gate

| Phase | Content | Est. lines | Independent? |
|---|---|---|---|
| 1 | `isAccessible` one-hop extension (5.1) | 100-180 | yes — self-contained, verifiable alone |
| 2 | `intFImpReuseWitnessAnc?_none_spec` (5.2) + strict label bound (5.4) | 100-150 | yes |
| 3 | `closurePred` no-contradiction hypothesis threading (5.3) | 60-100 | yes — pure signature + call-site work |
| 4 | `IWorldHist` def + `nw = edges.length + 1` + append/map plumbing + entry case | 150-250 | depends on 2, 4 |
| 5 | Mint-arm preservation, including the (★) manufacture — **the crux** | 250-400 | depends on 1, 2, 3, 4 |
| 6 | Alpha/beta/reuse-arm preservation | 100-150 | depends on 4 |
| 7 | Pigeonhole depth bound from (★) (4.3) | 100-150 | depends on 4 |
| 8 | Path-injection size bound + `intWorldHist_nw_le` (4.5) | 200-350 | depends on 4, 7 |
| 9 | Retire the sorry; rewire `Scheme.lean:5362-5363`; `lake build` | 30-60 | depends on all |

Phases 1-3 are **strictly additive and independently verifiable**, and I recommend they be
executed first regardless of the go/no-go outcome: each removes a named absent lemma and none of
them can be invalidated by a later change of route.

**Go/no-go gate.** The single point where the whole route can still fail is Phase 5, specifically
the instantiation of `intFImpReuseWitnessAnc? … = none` at `x := c'`. The derivation in 4.2 is
airtight on paper and every one of its five inputs was located in the source, but it has not been
Lean-checked. Recommended gate: **if Phase 5 cannot produce (★) as a sorry-free `have` within its
dispatch, mark the phase `[BLOCKED]`** with the exact goal state reached — per the task's binding
constraints, do not substitute a placeholder, do not relocate the obligation into a new
sorry-bearing helper, and do not add an undischarged hypothesis to
`intExpandBranches_openBranch_sat`.

**Constraint compliance check for the recommended route**: no `eraseDups`/`2 ^ U.length` bound
form is used; `intFImpReuseWitnessAnc?` is not edited (only a new spec lemma added alongside);
the bound comes entirely from blocking combinatorics via (★) and never from `intUniverse`'s linear
range; no vacuous definitions; every strengthened premise is discharged at its call site.

---

## 9. What is genuinely still unproven

To be explicit, since the task description asks for precision on this point:

- (★)'s derivation (4.2) is **new and unverified in Lean**. Its five inputs are each located in
  the source and individually plausible, but the composition has not been machine-checked.
- The path-injection argument (4.5) is standard combinatorics but has no Mathlib lemma that does
  it end-to-end; only `Fintype.card_pi_const` and `Finset.card_le_card_of_injOn` are available as
  building blocks (the former verified via Loogle).
- The refutation in 4.1 is a claim about non-derivability, argued semantically. It is strong
  enough to justify abandoning that route, but it is not a formal independence result.
