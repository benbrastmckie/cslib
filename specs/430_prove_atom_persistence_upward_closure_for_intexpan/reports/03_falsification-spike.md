# Falsification Spike Report — Task #430 (Atom Persistence / Upward-Closure)

**Task**: 430 (`prove_atom_persistence_upward_closure_for_intexpan`) · **Parent**: 317 · **Type**: cslib
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
**Session**: sess_1782818058_465873 · **Date**: 2026-06-30
**Builds on**: `reports/02_team-research.md`, `02_teammate-a-findings.md`, `02_teammate-c-findings.md`
**Method**: EMPIRICAL. One scratch module (`Cslib/Scratch430.lean`, since removed/restored to HEAD)
built against the live tableau, reusing the actual rule pipeline
(`applyPersistenceFixpoint`, `intStepBranch`, `intApplyRuleFull`, `isAccessible`,
`intExtractValuation`). All claims grounded in observed `#eval` output. No new axioms; no `sorry`
introduced (the `valUCProp_upward` prototype compiled clean).

---

## Executive summary (what the experiments actually showed)

- **EXPERIMENT 1 — raw edge-upward-closure: FAILS.** Concretely refuted with an *engineered* open
  saturated branch where a genuine parent→child edge has `T(p)@parent` but not `T(p)@child`. The
  `(a→b)∨(c→d)` example only refutes `≤`-on-ℕ (siblings); it does **not** refute edge-UC. The real
  refutation needed a deeper formula (`phi4` below).
- **EXPERIMENT 2 — Route C (containment preorder): REFUTED.** On the same engineered branches the
  parent is **not** ⊑ its sat_fimp-created child, so the `truthLemma` `imp-F` witness (`Scheme.lean:334-335`)
  is not derivable under `⊑`. Route C's "child contains parent's atoms by construction" premise is
  **false** whenever atoms arrive at the parent *after* the child is created.
- **Route A (edge-ancestor closure valuation): UC holds by construction (verified), BUT not a free
  win.** The closure valuation is upward-closed on every branch (verified empirically + a clean 3-line
  Lean proof). Its `Preorder` (via `Relation.ReflTransGen`) and `IValid` instantiation at `World = ℕ`
  **typecheck**. However its `truthLemma` **atom-F** case requires an *edge-atom-consistency* invariant
  that I **falsified** on an engineered saturated branch (`phi6`): a branch with `F(d)@2` while an edge
  ancestor carries `T(d)@1`. So Route A does **not** discharge completeness for an *arbitrary* saturated
  open branch either.
- **DECISION: Route A over Route C** (Route C is strictly worse — refuted at imp-F *and* coarsens
  imp-T). **But neither route is a standalone fix.** The binding constraint for *both* is an
  **edge-atom-persistence invariant on the *returned* branch**, which is exactly task 317's open B2
  expansion analysis. Empirically the *returned* branch (first open leaf) was genuine in every test,
  but that is an unproven ordering property.

---

## Setup

`Cslib/Scratch430.lean` reused the real rules but added a faithful per-branch saturator
`satBranch` (identical `applyPersistenceFixpoint` / `intStepBranch` / `closurePred` / edge
bookkeeping as `intExpandBranches`, `Expansion.lean:170-236`) that DFS-collects **every** open
saturated leaf together with its `IEdges` — because the production `IntTableauResult.openBranch`
discards edges (`Expansion.lean:79`, confirmed). Atoms encoded as `Nat`: `a=0,b=1,c=2,d=3,e=4,g=5,h=6`.
Edge convention matches the code: an edge `(child,parent)` means `parent ≤ child`, and
`isAccessible edges w w'` (`Rules.lean:87`) = "`w'` is a descendant of `w`" = `w ≤ w'`.

---

## EXPERIMENT 1 — raw valuation edge-upward-closure

### 1a. Team A's `(a→b)∨(c→d)` only refutes `≤`-on-ℕ, NOT edge-UC

`phi1 = (a→b)∨(c→d)`, one open branch:
```
edges = [(1,0),(2,0)]      -- worlds 1,2 are SIBLINGS (both children of 0)
world 0: {}   world 1: {a}   world 2: {c}
edgeUC_violations = []                       -- edge-UC HOLDS
natUC_violations  = [(0,1,2)]   -- atom a at world1 true, world2 false, but 1≤2 on ℕ
```
Confirms S1 exactly (T(a)@1, T(a)@2 absent, `1≤2` on ℕ). But worlds 1 and 2 are **not**
edge-related (`isAccessible [(1,0),(2,0)] 1 2 = false`), so this is **not** a counterexample to
edge-UC. `phi2`, `phi3`, `phi5` likewise show empty `edgeUC_violations`. Reasoning from the rules,
the *born-T-before-F* ordering (`intFImpRule` emits `[T(φ)@w', F(ψ)@w']`, `Rules.lean:157`) plus the
fixpoint re-running `intTImpRule` tends to settle antecedents before children are created, so naive
shapes do **not** break edge-UC.

### 1b. Engineered refutation — `phi4` breaks edge-UC on a real parent→child edge

`phi4 = (a ∧ (a→(c∨d))) → (g→h)`. Mechanism: at world 1 the antecedent yields `T(a)@1` and
`T(a→(c∨d))@1`; the fixpoint adds the *compound* `T(c∨d)@1`; `F(g→h)@1` then creates child world 2
**copying the still-unsplit `c∨d`**; worlds 1 and 2 subsequently split `c∨d` **independently**.
Observed (4 open branches):
```
edges = [(1,0),(2,1)]               -- 0→1→2 CHAIN; world 1 ≤ world 2
branch2: world1={d,a}  world2={c,a,g}   edgeUC_violations = [(3,(1,2))]   -- T(d)@1, ¬T(d)@2, 1≤2
branch3: world1={c,a}  world2={d,a,g}   edgeUC_violations = [(2,(1,2))]   -- T(c)@1, ¬T(c)@2, 1≤2
```
**This is a decisive refutation of raw edge-upward-closure**: `(2,1)` is a genuine world-creating
edge (world 2 is the sat_fimp child of world 1), so `world1 ≤ world2` in the edge order, yet a raw
positive atom at world 1 is absent at world 2.

> **Root cause (confirms Team A Finding 4 / Team C Claim 2, now witnessed):** `propagatePersistence`
> (`Rules.lean:139-141`, `:158`) is a creation-time snapshot of the *compound* `c∨d`; the post-creation
> fixpoint (`Expansion.lean:133-139`) only propagates *implication consequents*, never re-settles a
> disjunction. Parent and child split the copied disjunction independently → divergent atoms across an edge.

**EXPERIMENT 1 RESULT: raw edge-UC FAILS.** Witness `phi4`, branch 2: edge `(2,1)`, `T(d)@1`
present, `T(d)@2` absent.

---

## EXPERIMENT 2 — Route C containment preorder, and Route A closure valuation

### 2a. Route C (`w ⊑ w' := ∀p, rawval w p → rawval w' p`) is REFUTED at imp-F

`⊑` is trivially a `Preorder` (refl/trans immediate) and makes the raw valuation UC *by definition*.
The decisive test is whether the `truthLemma` `imp-F` witness survives: `sat_fimp` (`Scheme.lean:95-99`,
consumed at `:334-335`) hands back the **freshly created child** `w'`, and `imp-F` needs `w ⊑ w'`.
Checking which world-creating edges fail containment (`parent ⋢ child`):
```
phi4 containment-bad edges per branch: [[], [(1,2)], [(1,2)], []]
phi1 containment-bad edges:            [[]]      -- siblings fine (world0 empty ⊑ all)
```
On `phi4` branches 2 and 3, the sat_fimp edge `(parent=1 → child=2)` has `world1 ⋢ world2`
(world 1 carries `d`/`c` that world 2 lacks). So under `⊑` the child witness is **not** ⊒ the parent,
`imp-F` cannot be instantiated, and `F(g→h)@1` becomes *vacuously forced* (no ⊒-world carries `g`).
The `truthLemma` is therefore **false** under `⊑` for these saturated open branches.

> The task's stated Route-C hypothesis ("propagatePersistence copies ALL T-atoms parent→child, so
> `w ⊑ w'` holds for the freshly created child") is **empirically false**: it holds only at *creation
> time*; atoms that appear at the parent *after* the child via independent disjunction splitting break
> containment. **Route C is refuted.**

### 2b. Route A closure valuation `valUC w p := ∃ w0, IAccessible w0 w ∧ rawval w0 p`

- **Upward-closed by construction — VERIFIED.** On `phi4` (the branch where raw UC fails):
  ```
  phi4 closure-valuation edge-UC violations: [[], [], [], []]   -- all empty
  ```
  And the Lean proof compiles clean (no sorry):
  ```lean
  def IAccessibleP (edges) : Nat → Nat → Prop := Relation.ReflTransGen (fun p c => (c,p) ∈ edges)
  theorem valUCProp_upward (h : IAccessibleP edges w w') :
      valUCProp b edges w p → valUCProp b edges w' p := by
    rintro ⟨w0, hw0, hv⟩; exact ⟨w0, hw0.trans h, hv⟩
  ```
- **`Preorder` + `IValid` instantiation TYPECHECKS.** `edgePreorder edges : Preorder Nat` built from
  `ReflTransGen` compiled (needed explicit `lt` + `lt_iff_le_not_ge := Iff.rfl` to avoid the default
  `lt` field's `rfl` failure — a real but trivial gotcha). The term
  `letI : Preorder Nat := edgePreorder edges; IForces (fun w p => valUCProp b edges w p) (fun _ => False) w φ`
  elaborated at `World = ℕ`. **Caveat (do not over-read):** this is a *standalone* term. Team C's
  point stands — at the bridge (`Completeness.lean:108-112`) the goal's `Preorder` is already fixed to
  the default `≤` by `tableau_complete`/`intScheme`, so the order switch is a **global signature
  change** to `truthLemma`/`openBranch_countermodel`/`tableau_complete`, not a `letI` at the bridge.

- **CRITICAL obstacle for Route A — the truthLemma atom-F case is FALSIFIED on a saturated branch.**
  The current `truthLemma` atom-F case (`Scheme.lean:312-317`) uses the **raw** valuation and
  `no_contradiction`. Switching to `valUC` changes it to: `F(p)@w ⟹ ¬∃ ancestor w0 with T(p)@w0`.
  Engineered `phi6 = (a ∧ (a→(c∨d))) → (e→d)` (child world 2 created by `F(e→d)@1` carries `F(d)@2`):
  ```
  phi6 closure F-atom conflicts per branch: [[], [(3,2)]]
  branch2 summary: edges=[(1,0),(2,1)]  world1={d,a}  world2={c,a,e}   (F(d)@2 on branch)
  ```
  Branch 2 is a **saturated open branch satisfying `IBranchSaturation`** (all `sat_*` fields hold —
  there is **no** atom-persistence field) on which `valUC 2 d = true` (ancestor world 1 has `T(d)`)
  while `F(d)@2` is present. So under the closure valuation the `truthLemma` atom-F case
  (`F(d)@2 ⟹ ¬IForces 2 d`) is **false**. **Route A does not discharge an *arbitrary* saturated open
  branch.**

### 2c. The returned branch is genuine — but only by an unproven ordering accident

The production `intuitionisticTableau` returns the **first** open leaf. Observed:
```
phi6 REAL returned branch: world0={} world1={c,a} world2={c,a,e}   -- GENUINE (no ancestor-d/F-d clash)
phi4 REAL returned branch: world0={} world1={c,a} world2={c,a,g}   -- GENUINE (edgeUC clean)
```
Because each disjunction splits `[first, second]` (c before d) and parent+child split in the same
order, the *first* combined branch is the internally-consistent `(first,first)` leaf; the spurious
`(d,c)`/`(c,d)` leaves come later. So in practice the returned branch **is** edge-atom-persistent and
for it `valUC = rawval` (closure adds nothing). **But this is a fragile, unproven ordering property**,
not a theorem, and it is exactly 317's open `intExpandBranches_openBranch_sat` (B2) territory.

---

## DECISION

**Route A (edge order) over Route C (containment).** Route C is strictly dominated: it is refuted at
`imp-F` (§2a) *and*, being a coarser order, makes 317's already-`sorry` `imp-T` case
(`Scheme.lean:329-330`) harder (Team C U2). Route A keeps the order narrow (helps imp-T), and its
closure valuation makes upward-closure true unconditionally (§2b).

**However — and this is the load-bearing finding — Route A's closure valuation is NOT a self-contained
completion of task 430.** Both the raw-edge route and the closure route reduce to the SAME missing
fact: an **edge-atom-persistence invariant** ("if `T(p)@w0` and `w0 ≤ w` along edges, then `T(p)@w`")
that the rule system does **not** guarantee for arbitrary saturated open branches (falsified: `phi6`
branch 2). Two non-`sorry` ways to obtain it, both coupled to 317:

1. **Saturation-field route (preferred, no algorithm change).** Add an `IBranchSaturation` field
   `sat_atom_persist` (Team C U4) and prove the **returned** branch satisfies it inside
   `intExpandBranches_openBranch_sat` (317 B2). With that field, **raw `intExtractValuation` is already
   edge-UC** and the closure valuation is *unnecessary* — `v_upward_closed` (`Kripke.lean:65`) follows
   directly, and the existing raw-valuation `truthLemma` (atom-F, imp-F) is preserved unchanged except
   for the order restatement of `sat_fimp`. The closure valuation only becomes necessary if that field
   proves unprovable for the returned branch.
2. **Strengthen-propagation route (algorithm change — last resort).** Make persistence re-fire for
   bare atoms/disjuncts in `applyPersistenceFixpoint`, so *every* saturated open branch is
   edge-atom-persistent. This is the previously-rejected "Approach C / strengthen propagation"; it
   re-opens `Soundness.lean` (`:212`, `:1016`) and is heavier.

**Net recommendation to the planner:** adopt the **edge order (Route A's `ReflTransGen` preorder)** and
pursue **route 1 (the `sat_atom_persist` saturation field on the returned branch)**, keeping the raw
valuation. Treat the closure valuation as a documented fallback. **Do not plan 430 as an independent
unblock of 317** — the binding obligation lives in 317's B2 expansion proof. If the `sat_atom_persist`
field cannot be proven for the returned branch (i.e. the returned branch can itself be spurious),
escalate to **[BLOCKED]** for a design decision (route 2 vs. an expansion-ordering invariant).

---

## Newly discovered obstacles for the planner

1. **The upward-closure obligation is not a branch-local lemma.** For an *arbitrary* saturated open
   branch, NO order+valuation choice makes the `truthLemma` provable (raw fails UC; closure fails
   atom-F; containment fails imp-F). The obligation is intrinsically about the **returned** branch and
   couples to 317 B2. (Confirms and sharpens Team C Gap #4 / U3.)
2. **`sat_fimp` order restatement is mandatory and order-specific.** `Scheme.lean:97` (`w ≤ w'` on ℕ)
   must become `IAccessibleP edges w w'`; the witness child *is* one-step edge-accessible
   (`intFImpRule` adds edge `(w',w)`, `Rules.lean:159`), so this is re-derivable, not false — but it is
   a coordinated change to `IBranchSaturation` and its (still-open) construction proof.
3. **`Preorder Nat` `lt` gotcha.** Building a custom `Preorder Nat` from `ReflTransGen` needs explicit
   `lt` + `lt_iff_le_not_ge := Iff.rfl`; the auto-derived `lt` field fails `rfl`. Minor but will bite.
4. **Edges are still dropped by the result type** (`Expansion.lean:79`, `:182/:208`). Any edge-based
   order needs edges threaded out (S3) — re-confirmed; my spike had to re-run a private saturator to
   see them.
5. **Pre-existing committed scratch file.** `Cslib/Scratch430.lean` already exists **in HEAD** (a prior
   spike run committed it; 199 lines, same imports as this spike). I restored it to its HEAD state so my
   session leaves zero net change, but it should be **removed from the source tree** in cleanup — a
   stray module under `Cslib/` will affect `lake exe mk_all`/barrel and lint. Flagging for the
   orchestrator/planner; I did not delete a tracked file under a "write the report only" scope.

---

## Confidence

| Claim | Confidence | Basis |
|---|---|---|
| Raw edge-UC FAILS | **HIGH** | `#eval` witness `phi4` b2/b3, real rule pipeline |
| Route C refuted (imp-F / containment) | **HIGH** | `#eval` `containmentBadEdges phi4 = [[],[(1,2)],[(1,2)],[]]` |
| Route A closure valuation is UC + typechecks | **HIGH** | empty `closureUCViolations`; compiled Lean proof + `IValid` term |
| Route A atom-F case falsified on a saturated branch | **HIGH** | `#eval` `phi6` conflict `(3,2)` on a saturated open `IBranchSaturation` branch |
| Returned branch is genuine ⇒ raw=closure on it | **MEDIUM** | observed for all tested φ; ordering property unproven |
| `sat_atom_persist`-field route is the right plan | **MEDIUM-HIGH** | reduces both routes to one invariant; coupling to 317 B2 is structural |

**No new axioms. No `sorry` introduced.** Scratch module removed/restored to HEAD; working tree
matches HEAD.
