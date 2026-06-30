# Teammate C (Critic) Findings: Atom Persistence / Upward-Closure for `intExpandBranches`

**Task**: 430 · **Parent**: 317 · **Role**: Critic (stress-test seed report `01_atom-persistence-upward-closure.md`)
**Session**: sess_1782818058_465873
**Method**: targeted reads + grep; no full `lake build`. All claims grounded in file:line.

---

## TL;DR for the synthesizer

The seed's **diagnosis** (naive Nat-`≤` lemma is false; the model should use the edge/accessibility
order) is **correct and well-grounded** — even the code author agrees with it in a doc comment
(`Rules.lean:171-173`). But the seed's **prescription (Approach A)** rests on an unstated and
**likely false assumption**: that one-step edge persistence is already enforced by the machinery and
"just" needs lifting. It is **not**. `propagatePersistence` is a *creation-time snapshot*, and the
only post-creation propagation (`intTImpRule`) fires *only on implication consequents*. So
**even edge-order upward-closure is not obviously enforced** and may require a hard
expansion-ordering invariant (same territory as 317's open B2 leaf sorries) or a propagation
strengthening (the rejected Approach C). The seed also **understates Approach A's blast radius**
(edges are not in the returned branch) and **misses a cheaper order candidate** (specialization /
containment preorder) that sidesteps edges entirely.

---

## 1. Claim-by-claim verdicts

### Claim 1 (seed §4): "Countermodel uses `≤` on ℕ; doc comments say so." → **VALIDATED (code agrees with doc)**

- `truthLemma` (`Scheme.lean:303-310`), `openBranch_countermodel` (`:730-734`), and
  `tableau_complete` (`:775-778`) all state `IForces (intExtractValuation b) (S.modelBot b) w φ`
  with `w : Nat` and **no explicit `Preorder` argument**. `IForces` requires `[Preorder World]`
  (`Kripke.lean:81`), so Lean resolves the **default `Preorder Nat` = `≤`**. The doc comments
  (`Scheme.lean:763-765`, and `Completeness.lean:35-41/85`) say "World = ℕ … `≤` on Nat" — **doc
  and code agree**. No discrepancy.

- **Important nuance the seed glosses (refines its §2 "freedom" claim):** the two bridge `sorry`s
  (`Completeness.lean:112` int, `:109` min) sit *after* `apply tableau_complete …; intro _b`. At
  that point the **goal's Preorder is already fixed** by `tableau_complete`/`intScheme` to the
  default Nat `≤`. `IValid` (`Kripke.lean:145-148`) does quantify over *all* preorders, but to
  *discharge this goal* you must instantiate `IValid` at **exactly the goal's preorder**. So the
  "freedom to choose the order" is **not exercisable at the bridge in isolation** — exercising it
  *requires changing the order in the whole `truthLemma`/`openBranch_countermodel`/`tableau_complete`
  chain first*. The seed's §2/§4 present the order choice as a localized countermodel decision; it is
  in fact a **global signature change**. (Seed §5 cost/risk hints at this but the framing in §2/§4
  is misleading.)

### Claim 2 (seed §3.1 / §5-B): "`propagatePersistence` only copies parent→direct-child; could the fixpoint achieve closure indirectly?" → **PARTIALLY REFUTED — and this is the headline finding**

What the code actually does:

- `propagatePersistence` (`Rules.lean:139-141`) copies **all** pos formulas at `fromWorld` to
  `toWorld`. It is invoked in **exactly one place**: `intFImpRule` (`Rules.lean:158`), i.e. **only at
  world creation, parent `w` → fresh child `w' = nextWorld`** (verified by grep: the only
  non-proof usage). It is a **snapshot taken at creation time**.
- The only **post-creation** propagation is `applyPersistenceFixpoint` (`Expansion.lean:133-139`),
  which iterates `applyAllTImpRules` (`:118-127`) → `intTImpRule` (`Rules.lean:174-186`). This
  propagates **only the consequent `ψ` of an implication `T(φ→ψ)`** to accessible worlds where
  `T(φ)` already holds. It **does not copy bare atoms**.

Consequence (**both the seed and naive Approach A miss this**): a **bare atom** `T(p)@w` that is
added to an *existing* world `w` *after* a child `w'` of `w` was already created — e.g. via a
conjunction split `T(p∧q)@w` (saturation `sat_tand`, `Scheme.lean:75`) or disjunction split
expanded after `w'` exists — is propagated to `w'` by **neither** mechanism (`propagatePersistence`
is creation-only; `intTImpRule` only fires on implications). The partial rescue is that
`propagatePersistence` copies the *compound* `T(p∧q)@w` to `w'` **if it was present at `w` at
creation time**, and `w'`'s own saturation then re-derives `T(p)@w'`. But for compounds/atoms that
arrive at `w` *strictly after* `w'` is created, there is **no re-propagation**.

**Therefore: edge-order upward-closure of `intExtractValuation b` is NOT mechanically guaranteed.**
Its truth reduces to a delicate *expansion-ordering / fixpoint-completeness* invariant (does every
atom-producing expansion at `w` happen before any child of `w` is created, or does the fixpoint
re-saturate children?). That is **the same class of hard analysis as 317's B2 leaf sorries**
(`intExpandBranches_openBranch_sat`, `Scheme.lean:485`), and it might even be **false** as the
machinery stands — in which case the only fixes are (a) strengthen propagation (= the rejected
Approach C, breaks soundness reasoning at `Soundness.lean:212,1016`) or (b) prove a non-obvious
ordering invariant. The seed's Approach A pieces 2-3 ("one-step persistence already added by
`propagatePersistence`, just lift along accessibility") **assume away exactly this gap**.

Sub-point on the seed's "could it fail to close even along edges": **yes**, additionally via fuel:
`applyPersistenceFixpoint` is called with finite fuel (`Expansion.lean:200`,
`fuel'+1`); if it stops before a true fixpoint (`:138` length-equality test), the returned branch is
not even T-imp-saturated. (`isAccessible`'s own fuel = `edges.length`, `Rules.lean:102`, is fine for
the acyclic tree.)

### Claim 3 (seed): "Is `intExtractValuation` the right valuation? Is there a deeper forcing/order mismatch?" → **REFUTED (no deeper mismatch) but with one real proof-level coupling**

- No deeper mismatch: `truthLemma` proves `¬ IForces (intExtractValuation b) (S.modelBot b) 0 φ`
  and the bridge needs `IForces (intExtractValuation b) (S.modelBot b) 0 φ` — **same valuation, same
  `botForces`, same ambient preorder** on both sides. The contradiction in `tableau_complete:783` is
  clean. `intExtractValuation` *is* the right valuation; there is no "truthLemma proves a different
  forcing" problem. The valuation is `b.any (T(atom p)@w)` (`Soundness.lean:1640` per seed) and
  `IForces_atom` (`Kripke.lean:90-93`) reads it directly.
- The **only** order-sensitivity (the genuine "Q3 blast radius") is in the **imp F-direction proof**,
  `truthLemma … imp` (`Scheme.lean:331-335`): line 335 feeds `hw' : w ≤ w'` obtained from
  `hsat.sat_fimp` (`:334`) into `hcontra` (whose `≤` comes from `IForces_imp`,
  `Kripke.lean:100-104`). These unify **only because both are Nat's default `≤`**. `sat_fimp` itself
  is stated in Nat `≤` (`Scheme.lean:97`, justified by "strictly increasing labels", note at
  `:70-71`). So switching the ambient preorder **breaks line 335** unless `sat_fimp` is *also*
  restated in the new order. Compatibility is achievable (the fresh child *is* edge-accessible from
  its parent — `intFImpRule` adds edge `(w',w)`, `Rules.lean:159`, and `isAccessible e w w' = true`
  one-step), but it is a **coordinated change to `IBranchSaturation` + its (still-open) construction
  proof**, not a free rewire.

### Claim 4 (seed §5 cost/risk): "Does Approach A break green `truthLemma` and/or/imp-F cases?" → **MOSTLY REFUTED for `and`/`or`; CONFIRMED-but-narrow for `imp-F`**

- `atom`/`bot`/`and`/`or` cases (`Scheme.lean:312-320, 336-365`) are **world-local** (`IForces_and`,
  `IForces_or` evaluate at the same `w`, `Kripke.lean:106-116`) — **ordering-agnostic**, will not
  break. Seed correct.
- `imp-F` (`:331-335`) is the **only currently-green proof that breaks** under an order change, and it
  breaks *mechanically* (type mismatch at line 335), not *semantically* — it becomes provable again
  once `sat_fimp` is edge-restated (see Claim 3). Nothing becomes **false**.
- The `imp-T` direction (`:329-330`) is **already a sorry owned by 317** — not green, so not a
  "break" but a coupling (see Unasked Q4).
- Generic lemmas `iforces_persistence` (`Kripke.lean:125`, uses `le_trans`) and
  `mvalid_implies_ivalid` (`:165`) are preorder-generic — **safe**.

  Net: the blast radius **on green proofs** is *smaller* than the seed implies (one proof line). The
  blast radius **on the overall refactor** is *much larger* (see Claim 5 / Unasked Qs).

### Claim 5 (seed): "Is Approach A circular/unsound? Does the edge preorder satisfy IValid's upward-closure demand?" → **Not unsound, not circular — but viability hinges on an unproven (possibly false) persistence fact**

- **Not unsound / not circular**: `IValid`/`MValid` (`Kripke.lean:145-158`) hold for *every*
  preorder. Choosing `isAccessible`-based `≤` (reflexive: `Rules.lean:88`; transitive: to be proven)
  and supplying a *true* upward-closure proof is a legitimate instantiation. No circularity.
- **But** the upward-closure proof you must supply is exactly the fact undermined in Claim 2. So
  Approach A is sound *if and only if* edge-order upward-closure is actually true of the final
  saturated branch — which the machinery does **not** obviously enforce. The risk is **unprovability
  / falsity**, not unsoundness.
- Secondary unprovability risk the seed flags correctly: transitivity of the **fueled DFS**
  `isAccessible` (`Rules.lean:87-102`) is a non-trivial standalone lemma. Mathlib's
  `Relation.ReflTransGen` (seed open-Q6) would give transitivity free **but** requires bridging the
  `Bool` DFS to a `Prop` closure and re-proving `sat_fimp`/`intTImpRule` agree with it.

---

## 2. Gaps & Risks the seed under-weights

1. **[HIGH] Persistence is a creation-time snapshot, not an edge invariant** (Claim 2). The seed's
   core mechanical premise ("propagatePersistence is exactly the operation that enforces upward
   closure along edges", §4) is **only true for the snapshot at creation**, not for atoms/compounds
   added to a parent later. This is the single biggest threat to Approach A and is unaddressed.

2. **[HIGH] Edges are not in the returned branch.** `IntTableauResult.openBranch : IBranch Atom → …`
   (`Expansion.lean:79`) carries **only `b`**, no `IEdges`. The edge order needs the edges, and they
   are **not recoverable from `b`** (a `List (ISF Atom)` loses parent-child structure). So Approach A
   requires changing the **inductive result type** and the entire `intExpandBranches` recursion
   (`Expansion.lean:170+`) plus the three 317 leaf lemmas that destructure it
   (`intExpandBranches_openBranch_sat/_closed/_initial_mem`, `Scheme.lean:485/392/589`). This
   **directly contradicts** the seed's §7 hope to "land self-contained pieces first … without
   editing 317's open proofs." The edges-plumbing is the *gating* decision, not a footnote
   (seed demotes it to open-Q5).

3. **[MED] Per-branch preorder plumbing.** The edge order depends on `b`'s edges, so it cannot be a
   single global `Preorder Nat`. `truthLemma`/`openBranch_countermodel`/`tableau_complete` would each
   need the edges as a parameter and a consistent `letI : Preorder Nat := …` so the `IForces` terms
   match. Real refactor of all three signatures.

4. **[MED] 430 is not cleanly separable from 317.** The upward-closure fact (whether as a new
   `IBranchSaturation` field `sat_atom_persist` per 317 handoff B3, or a standalone lemma) is proven
   from the same expansion analysis as the B2 leaf sorries. Treating 430 as an independent unblock of
   317 is partly illusory; they share the hard core.

5. **[LOW] `minBranchBotForces` confirmed isomorphic to the atom problem.** `minBranchBotForces b w =
   b.any (T(⊥)@w)` (`Soundness.lean:168-170`) has the *same shape* as `intExtractValuation` (both
   "is this positive formula at `w` on `b`"). §6's "one generic positive-formula-persistence lemma
   covers both" is **validated** — good. (Its doc at `:165-167` repeats the same Nat-`≤`/accessibility
   conflation found everywhere.)

---

## 3. Unasked Questions (critic value-add)

- **U1 — Specialization / containment preorder (the missed cheaper order).** Define
  `w ≤ w' := ∀ p, intExtractValuation b w p → intExtractValuation b w' p` (reflexive, transitive by
  construction). Then **val-upward-closure is true by definition** — no edges, no fueled-DFS
  transitivity, no return-type change (sidesteps Gaps #2, #3, and the Claim-2 snapshot problem for
  *atoms*). Cost shifts entirely to proving `sat_fimp`'s witness `w'` satisfies the **containment**
  order (the fresh child must contain `w`'s atoms — which is what `propagatePersistence` gives *at
  creation*, modulo the same later-atom caveat). This may **dominate Approach A** and is **completely
  absent** from the seed. Needs a proof spike before committing to edges. (Caveat: it makes `imp-T`
  harder — see U4.)

- **U2 — Does the order choice change the difficulty of 317's *open* `imp-T` sorry (`Scheme.lean:330`)?**
  Yes, and the seed never asks. The `imp` cases quantify `∀ w' ≥ w`. A **narrower** order (edge) =
  *fewer* accessible `w'` = **easier** `imp-T`; a **broader** order (Nat `≤`, or containment) =
  **harder** `imp-T`. This is an argument *for* the edge order beyond upward-closure — but it also
  means the order decision is entangled with 317's hardest remaining obligation and must be made
  jointly, not in isolation.

- **U3 — Is the upward-closure property even TRUE of the produced branches?** Before any proof
  strategy, run a *concrete falsification spike*: construct (on paper or via `#eval`) a small `φ`
  whose expansion creates a child `w'` of `w` and then adds `T(p)@w` via a `∧`-split at `w`, and
  check whether `T(p)@w'` ends up on the final branch. If not, **both Approach A and B are dead** and
  the task is really "strengthen propagation or reformulate," i.e. it should be **[BLOCKED]** for a
  design decision, not implemented. (This is the decisive cheap experiment the seed should have led
  with, analogous to its own open-Q1 but aimed at *persistence*, not *siblings*.)

- **U4 — Should upward-closure be a field of `IBranchSaturation` or a separate lemma?** If a field, it
  is constructed inside `intExpandBranches_openBranch_sat` (the B2 sorry site) and automatically
  shares fuel/induction with the other saturation conditions — likely the *right* home, and it makes
  the truthLemma/bridge wiring uniform. The seed mentions this (§6) but does not weigh it against the
  "self-contained standalone lemma" plan in §7, which the edges problem (Gap #2) largely invalidates
  anyway.

- **U5 — Reflexivity/`w ≤ w'` direction sanity at world 0.** The bridge needs forcing **at world 0**
  (`tableau_complete:776`). Under the edge order, is every other world `≥ 0`? Worlds are created as
  children of `0` or descendants, so `isAccessible edges 0 w'` should hold for all reachable `w'` —
  but `intExtractValuation` upward-closure is only ever *used* from lower to higher; confirm no proof
  needs the *reverse*. Minor, but unstated.

---

## 4. Recommendation: is the seed's Approach-A lean justified?

**Partially. The lean is defensible but premature, and the report should not be treated as
green-lighting an Approach-A implementation.**

- The seed is **right** that Nat-`≤` is the wrong order (confirmed by `intTImpRule`'s own doc,
  `Rules.lean:171-173`: it *deliberately* replaced the `≥ w` proxy precisely because it wrongly
  treated siblings as accessible). **Approach B (chain/no-siblings) is effectively dead already** —
  no need to spend much confirming it; the code author already moved off sibling-`≤`.
- The seed is **wrong (or unverified)** that one-step edge persistence is already enforced and merely
  needs lifting (Claim 2 / Gap #1). This is the load-bearing assumption of Approach A and it is **not
  established by the code**; it may be false.
- The seed **under-scopes** Approach A: edges-not-in-result (Gap #2) makes it a deep refactor coupled
  to 317, not a set of independent additions.
- The seed **misses** the specialization-preorder alternative (U1), which may be strictly cheaper.

**Recommended next actions, in order:**
1. **Falsification spike (U3)** — decide whether *any* upward-closure (edge or containment) is true
   of the produced branches. Cheap, decisive. If false → **[BLOCKED]**, escalate a design decision
   (strengthen `propagatePersistence` to re-fire, or carry persistence in the fixpoint for atoms).
2. If true, **prototype U1 (containment preorder)** before edges — it avoids Gaps #2/#3 entirely.
3. Only if U1 fails, pursue edge-based Approach A, and budget for: result-type change to carry
   `IEdges`, `sat_fimp` edge-restatement, fueled-DFS transitivity (or `ReflTransGen` bridge),
   per-branch preorder plumbing, and re-proof of `truthLemma` imp-F line 335 — **all coordinated with
   317**, not landed independently.
4. Expose the persistence fact **once** (preferably an `IBranchSaturation` field, U4) for both
   `intExtractValuation` and `minBranchBotForces` (validated isomorphic, Gap #5).

**No new axioms** in any path (consistent with the seed's §9 and the zero-debt gate).

---

## 5. Confidence

- **HIGH** on the code-grounded facts: default Preorder is Nat `≤` (Claim 1); `propagatePersistence`
  is creation-only and the fixpoint propagates only implication consequents (Claim 2 / Gap #1); edges
  absent from `IntTableauResult.openBranch` (Gap #2); `imp-F` line 335 is the sole order-sensitive
  green proof (Claims 3-4); `minBranchBotForces` isomorphic to `intExtractValuation` (Gap #5);
  `intTImpRule` doc confirms the sibling/Nat-`≤` defect (Approach B dead).
- **MEDIUM** on whether edge-order upward-closure is ultimately *true* (Claim 2 / U3) — this needs the
  falsification spike; I did not run `#eval` (context frugality), I reasoned from the definitions.
- **MEDIUM** on the specialization-preorder alternative (U1) being viable — promising but unproven;
  needs a spike.
- **HIGH** that the seed's Approach-A blast-radius estimate is too optimistic and that 430 is not
  cleanly separable from 317.
