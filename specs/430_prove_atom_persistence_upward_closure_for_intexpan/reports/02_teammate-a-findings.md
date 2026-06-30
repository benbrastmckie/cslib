# Teammate A Findings — Atom-Persistence / Upward-Closure (Task 430)

**Role**: Teammate A (PRIMARY / decisive technical determination)
**Session**: sess_1782818058_465873
**Method**: direct code reads (Rules.lean, Expansion.lean, Soundness.lean); two hand-traced
expansion runs. No `lake build` (context frugality). Every claim grounded at file:line.

---

## Key Findings

1. **Q1 is DECISIVE: sibling worlds DO occur on open branches returned by `intExpandBranches`.**
   The expansion loop picks "the first unexpanded applicable formula" with no per-world
   stratification (`intStepBranch`, `Expansion.lean:150-157`), and `intFImpRule` always creates a
   *fresh* child of the firing formula's own label (`Rules.lean:153-158`). Two `F(→)` formulas at
   the same parent label therefore create two children of that parent = **siblings** (a genuine
   tree, not a chain).

2. **Consequence: the naive `≤`-on-ℕ upward-closure lemma is provably FALSE.** Concrete
   counterexample below (φ = `(a→b) ∨ (c→d)`): `T(a)@1` on the branch, `T(a)@2` absent, yet
   `1 ≤ 2` on ℕ. So Approach B (chain) is **refuted**; **Approach A (edge-based order) is required.**

3. **Q2 is DECISIVE: do NOT prove the fueled `Bool` `isAccessible` transitive. Use Mathlib
   `Relation.ReflTransGen` over the parent-child step relation** to obtain reflexivity +
   transitivity (hence a `Preorder`) for free. Keep `isAccessible` only for its operational role
   inside `intTImpRule`.

4. **PRIMARY technical determination (the decisive caveat the seed did not surface):** even the
   **edge-based** upward-closure of the *raw* `intExtractValuation` is **not** a one-line theorem,
   because atom persistence is **not a manifest saturation invariant** — `propagatePersistence`
   runs **only at child-creation time** (`Rules.lean:138-140`, invoked only at `Rules.lean:157`)
   and is **never re-run** in the saturation fixpoint (`applyPersistenceFixpoint` only iterates
   `intTImpRule`, `Expansion.lean:118-139`). The robust, *trivially provable* form of the
   obligation uses the **edge-ancestor closure** of the valuation (upward-closed by
   `ReflTransGen.trans` in 3 lines). This discharges the named obligation and relocates the
   residual difficulty into the `truthLemma` F-atom direction (task 317's territory).

5. **Prerequisite blocker for ANY edge-based approach:** `intExpandBranches` returns
   `.openBranch b` and **discards the edge list** (`Expansion.lean:182, 208`). The edges must be
   threaded out (return `(b, edges)` or carry edges in the open-branch result) before a Preorder
   can be defined at the bridge site.

---

## Recommended Approach: **A (edge-based Preorder), decisively — with the ancestor-closure valuation**

Reject B (refuted, Finding 2). Reject C (breaks soundness; seed §5). Adopt A, refined:

- **Preorder**: `IAccessible edges := Relation.ReflTransGen (fun p c => (c, p) ∈ edges)`
  (edge `(child, parent)` ⇒ child reachable from parent in one step ⇒ `parent ≤ child`).
  Reflexivity and transitivity are free (`ReflTransGen.refl`, `ReflTransGen.trans`).
- **Valuation**: replace the raw `intExtractValuation` (Finding 4) with its edge-ancestor closure
  in the *countermodel construction* so upward-closure is true *by construction*.
- **Instantiate** `IValid`/`MValid` (which quantify over **all** `Preorder`s, seed §2) at this
  Preorder rather than `≤` on ℕ.

This is the only approach for which the upward-closure obligation named by task 430 is provable
without first re-architecting the tableau rules. The remaining hard obligation (F-atom soundness
of the closure valuation) is a `truthLemma` matter and is flagged in "Residual obligation" below.

---

## Evidence / Examples

### Code facts (file:line)

- `intStepBranch` = "first unexpanded formula with an applicable rule", scans branch in order,
  no per-world ordering: `Expansion.lean:150-157`.
- `intFImpRule φ ψ w nextWorld b` → child `w' = nextWorld`, adds `[T(φ)@w', F(ψ)@w']`, appends
  `propagatePersistence b w w'`, returns edge `(w', w)`: `Rules.lean:153-158`.
- `F(φ∨ψ)` is an **alpha** rule: adds `F(φ)@l, F(ψ)@l` **at the same world** `l`:
  `Rules.lean:258-259`.
- `propagatePersistence` copies parent's positive formulas to child **once, at creation only**;
  it is invoked nowhere except `intFImpRule`: `Rules.lean:138-140`, `Rules.lean:157`.
- `applyPersistenceFixpoint` iterates **only** `applyAllTImpRules` (i.e. `intTImpRule`, T(→)
  consequents); it does **not** re-propagate atoms: `Expansion.lean:118-139`.
- Open branch returned discards edges: `Expansion.lean:181-183` (fuel-out) and
  `Expansion.lean:206-208` (saturated-open) both yield `.openBranch b` with no edge component.
- Valuation looks only at **atoms**: `Soundness.lean:1640-1641`
  (`b.any (sign == .pos && formula == .atom p && label == w)`).

### Counterexample to `≤`-on-ℕ upward-closure (Q1, order-robust, refutes Approach B)

Test validity of φ = `(a→b) ∨ (c→d)` (a,b,c,d distinct atoms). Initial branch `[F(φ)@0]`,
`nextWorld = 1`, `edges = []`.

1. `F((a→b)∨(c→d))@0` → alpha (`Rules.lean:258`): branch gains `F(a→b)@0, F(c→d)@0` (this order).
2. First unexpanded applicable = `F(a→b)@0` → `intFImpRule a b 0 1`: child **world 1**, edge
   `(1,0)`, adds `T(a)@1, F(b)@1`; persistence copies `posFormulasAt b 0` = ∅ (world 0 has only
   F-formulas). `nextWorld = 2`.
3. Next unexpanded applicable = `F(c→d)@0` → `intFImpRule c d 0 2`: child **world 2**, edge
   `(2,0)`, adds `T(c)@2, F(d)@2`; persistence ∅. `nextWorld = 3`.

Final branch: `[F(φ)@0, F(a→b)@0, F(c→d)@0, T(a)@1, F(b)@1, T(c)@2, F(d)@2]`.
Edges `[(1,0),(2,0)]` ⇒ **worlds 1 and 2 are siblings** (common parent 0, mutually inaccessible).
No complementary pair, no `T(⊥)` ⇒ branch is **open** and **saturated** (no `T(→)`, so the
persistence fixpoint is a no-op) ⇒ returned as `.openBranch`.

Now `intExtractValuation b 1 a = true` (`T(a)@1` present) but `intExtractValuation b 2 a = false`
(`T(a)@2` absent), while `1 ≤ 2` on ℕ. **Upward-closure w.r.t. `≤`-on-ℕ fails.** ∎

This counterexample does **not** threaten the edge order: 1 and 2 are not edge-related, so
`IAccessible edges 1 2 = False` and there is no obligation to relate them.

### Risk scenario for raw EDGE-based upward-closure (Finding 4)

Because `propagatePersistence` fires only at child creation and is never re-run, an atom that
arrives at a **parent** *after* a child was created is not back-propagated by any rule. The
benign paths are covered — pre-existing positive formulas are copied at creation
(`Rules.lean:157`), and `T(φ→ψ)` consequents reach descendants because `intTImpRule` iterates
**all** accessible worlds (`Rules.lean:176-185`). But there is **no rule** that re-propagates a
positive atom/disjunct introduced at a parent post-creation down to an existing child. Whether
branch traversal order *accidentally* avoids every such case is **unproven**; there is no
saturation invariant asserting "`T(p)@parent` ⇒ `T(p)@child`" for atoms. Hence a direct proof of
raw edge-upward-closure is **not** available, motivating the ancestor-closure valuation.

---

## Exact lemma statement(s) to prove

### Q2 primitive + Preorder (free)

```lean
/-- Edge-based Kripke accessibility as a Prop relation: `(child, parent) ∈ edges`
    means `parent ≤ child`. -/
def IAccessible (edges : IEdges) : Nat → Nat → Prop :=
  Relation.ReflTransGen (fun p c => (c, p) ∈ edges)

-- Reflexivity/transitivity are FREE:
--   refl  := Relation.ReflTransGen.refl
--   trans := Relation.ReflTransGen.trans
-- Supply locally at the bridge:  letI : Preorder Nat := ⟨IAccessible edges, …, …⟩
-- (a local Preorder for IValid's `[Preorder World]`, avoiding clash with ℕ's `≤`).
```

### The upward-closure obligation, in its provable form (ancestor-closure valuation)

```lean
/-- Countermodel valuation: `p` holds at `w` iff some edge-ancestor carries `T(p)`. -/
def intExtractValuationUC (b : IBranch Atom) (edges : IEdges) (w : Nat) (p : Atom) : Prop :=
  ∃ w0, IAccessible edges w0 w ∧ intExtractValuation b w0 p

/-- Upward closure — TRIVIAL via transitivity of ReflTransGen. -/
theorem intExtractValuationUC_upward_closed
    (b : IBranch Atom) (edges : IEdges) {w w' : Nat} (p : Atom)
    (hle : IAccessible edges w w') :
    intExtractValuationUC b edges w p → intExtractValuationUC b edges w' p := by
  rintro ⟨w0, hw0, hval⟩
  exact ⟨w0, hw0.trans hle, hval⟩
```

(Lit. note: `Relation.ReflTransGen`, `.refl`, `.trans`, `.head`, `.tail`, and
`head_induction_on` are standard `Mathlib/Logic/Relation`; Cslib depends on Mathlib.
`lean_local_search "Relation.ReflTransGen"` returned no *local* decl, as expected for a Mathlib
symbol — it is not project-defined; confirm with `lean_hover_info` at use site during impl.)

### If instead the raw valuation must be kept (the structural route)

You must first establish a **saturation invariant** (currently absent from the rules):

```lean
theorem intExtractValuation_edge_upward
    {b : IBranch Atom} {edges : IEdges} {w w' p}
    (hsat : <b is an open saturated branch with edge set `edges`>)
    (hedge : (w', w) ∈ edges)
    (hval : intExtractValuation b w p) :
    intExtractValuation b w' p
```

This is **not** provable from the current rules (Finding 4 / Risk scenario). Making it true
requires adding atom (all-positive-formula) persistence to `applyPersistenceFixpoint` along
edges and re-checking Soundness (`Soundness.lean:212, 1016`). Recommend the ancestor-closure
valuation over this route for the named task; this structural change is the true root fix for
317's `truthLemma`.

---

## Residual obligation (hand-off to 317)

With the closure valuation, the **F-atom direction** of `truthLemma` becomes:
`F(p)@w` on an open saturated branch ⇒ `¬ intExtractValuationUC b edges w p`, i.e. **no
edge-ancestor of `w` carries `T(p)`**. That needs exactly the edge-atom-consistency invariant
(ancestor `T(p)` + descendant `F(p)` ⇒ closure ⇒ contradiction with openness), which in turn
needs ancestor→descendant atom persistence — the same structural gap. So the upward-closure
*per se* is cheap; the genuine remaining work is the persistence invariant inside 317's
`truthLemma`, not the ordering choice.

## Minimal-logic variant (brief)

`minimalTableau_complete` shares `intExtractValuation` (`Soundness.lean:1638`) ⇒ same closure-
valuation treatment. Its extra `bf_upward_closed` for `minBranchBotForces` should fall to the
identical `ReflTransGen.trans` argument **if** `minBranchBotForces` is defined via accessibility;
verify its definition before committing (out of scope for my Q1/Q2 but flagged).

---

## Confidence

| Claim | Confidence | Basis |
|---|---|---|
| Q1: siblings occur; `≤`-on-ℕ upward-closure false | **High** | Order-robust hand-trace of `(a→b)∨(c→d)`, grounded at file:line |
| Q2: use `ReflTransGen`, not fueled `isAccessible` | **High** | Standard Mathlib; fuel-DFS transitivity is genuinely hard, ReflTransGen gives Preorder free |
| Finding 4: raw valuation not provably edge-upward-closed | **High** | `propagatePersistence` is creation-time only (`Rules.lean:157`), never in fixpoint (`Expansion.lean:118-139`); no saturation invariant |
| Closure-valuation upward-closure is trivially provable | **High** | 3-line `ReflTransGen.trans` proof above |
| Edges must be threaded out of the open-branch result | **High** | `.openBranch b` drops edges (`Expansion.lean:182, 208`) |
| Residual `truthLemma` obligation needs persistence invariant | **Medium-High** | Reasoned from rule set; not exhaustively model-checked |

**No new axioms.** All recommendations are constructive (definitions + a transitivity proof) or
structural (rule addition with Soundness re-check), none introduce `axiom`/`sorry`.
