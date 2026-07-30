# Teammate B Findings — Wiring Mechanics, Edge Threading, Prior Art

**Task**: 430 (`prove_atom_persistence_upward_closure_for_intexpan`)
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
**Teammate**: B (ALTERNATIVES / wiring mechanics & prior art)
**Session**: sess_1782818058_465873
**Scope**: Q5 (edge threading / return-type blast radius), Preorder wiring mechanism,
prior art in the soundness proof and Mathlib. Assumes Approach A (edge-based Preorder) and
works out HOW to wire it. Does NOT re-determine siblings/transitivity (Teammate A).

---

## Key Findings (headline first)

1. **Edges ARE already threaded through the whole expansion loop, but the RETURN type drops
   them.** `intExpandBranches` takes `(edgeSets : List IEdges)` and the inner `go` carries
   `doneEdges`/`pendingEdges` in lockstep with branches (`Expansion.lean:170-235`). However the
   result type `IntTableauResult.openBranch : IBranch Atom → IntTableauResult Atom`
   (`Expansion.lean:79`) carries **only the branch** — the branch's final edge set is discarded
   at every `.openBranch …` return site (`Expansion.lean:182, 208, 232`).

2. **Edges are NOT recoverable from `b` alone.** `IBranch = List (ISF Atom)` (`Rules.lean:71`)
   is a flat list of sign/formula/`Nat`-label triples. The parent→child tree is stored *only*
   in the separate `IEdges = List (Nat × Nat)` (`Rules.lean:80`). From `b` you can recover the
   set of world labels (`b.map (·.label)`), but **not** which world is the parent of which —
   and because sibling worlds occur (Teammate A's question; persistence is along tree edges, not
   numeric `≤`), label order does not reconstruct the edges. **Conclusion: Approach A needs a
   plumbing change to thread the final `IEdges` out alongside `b`.**

3. **The three completeness theorems bake in `World = ℕ` with the *ambient default* `Preorder ℕ`
   (`≤`).** `truthLemma` (`Scheme.lean:303-310`), `openBranch_countermodel` (`:730-751`), and
   `tableau_complete` (`:775-783`) all write `IForces (intExtractValuation b) (S.modelBot b) w φ`
   with `w : Nat`. The `[Preorder World]` of `IForces` (`Kripke.lean:81`) is resolved at *each
   lemma's declaration* against `Nat.instPreorder`. A downstream `letI`/`haveI` at the bridge
   **cannot retroactively change** the order those already-elaborated statements use. So switching
   to the edge order is a **statement-level generalization of these three lemmas**, not a local
   instance trick.

4. **PRIOR ART — the soundness proof already solved the entire edge↔order problem.** The dual
   `tableau_sound` direction does *not* use `≤` on `ℕ`; it maps `Nat` labels into an abstract
   `[Preorder World]` via `worldOf : Nat → World` and requires only a one-directional bridge
   `MonotoneEdges worldOf edges := ∀ w w', isAccessible edges w w' → worldOf w ≤ worldOf w'`
   (`Soundness.lean:346-348`). All the fiddly `isAccessible` lemmas Approach A needs already
   exist and are sorry-free (see Reusable Lemmas below). **Completeness should mirror this
   pattern**, not invent a new wrapper.

5. **One generic persistence lemma covers both bridges.** `minBranchBotForces b w` = "T(⊥) at
   label `w` on `b`" (`Minimal/Soundness.lean:168`) — structurally identical to
   `intExtractValuation b w p` = "T(atom p)@w on `b`" (`Soundness.lean:1640`). Both are "a
   positive formula sits at label `w`", and `propagatePersistence` copies **all** positive
   formulas (`posFormulasAt` filters on `sign == .pos` only; `Rules.lean:125-140`). So a single
   lemma "`T(α)@w ∈ b ∧ isAccessible edges w w' → T(α)@w' ∈ b`" instantiated at `α := .atom p`
   and `α := .bot` discharges both `v_upward_closed` and `bf_upward_closed`. This satisfies the
   "expose persistence once, no int/min duplication" requirement (seed §6).

6. **`iforces_persistence` is directly reusable.** `Kripke.lean:125-140` proves full forcing
   persistence for *any* `[Preorder World]` given `v_uc` + `bf_uc`. Once the edge-Preorder and
   the edge-upward-closure of the valuation are in hand, forcing-persistence is free.

---

## Q5 — Exact signature/return-type change and blast radius

### Required change

`IntTableauResult.openBranch` must additionally carry the branch's final edge set:

```lean
-- Expansion.lean:75-79  (BEFORE)
inductive IntTableauResult (Atom : Type*) : Type _ where
  | closed : IntTableauResult Atom
  | openBranch : IBranch Atom → IntTableauResult Atom

-- (AFTER)
inductive IntTableauResult (Atom : Type*) : Type _ where
  | closed : IntTableauResult Atom
  | openBranch : IBranch Atom → IEdges → IntTableauResult Atom
```

Then the three return sites pass the in-scope edges:
- `Expansion.lean:182` `| some b => .openBranch b` — the fuel=0 path discards `edgeSets`; it must
  return the edge set paired with the chosen branch. NOTE: `findSome?` here only yields `b`, so
  this site must be rewritten to also select the parallel `edges` (e.g. zip
  `branches`/`edgeSets`, or fold returning `(b, edges)`).
- `Expansion.lean:208` `| none => .openBranch bPers` — return `.openBranch bPers edges`
  (the `edges` bound at `:197` is exactly this branch's edge set; `bPers` is built from it at
  `:199`). Trivial.
- `Expansion.lean:232` `.notApplicable => .openBranch bPers` — same: `.openBranch bPers edges`.

### Blast radius (every site that constructs or matches `IntTableauResult.openBranch`)

**Constructors (Expansion.lean)** — 3 sites: `:182, :208, :232` (above). `intuitionisticTableau`
(`:270`) and `minimalTableau` (`:283`) just forward the result type, so they need no body change
beyond recompilation.

**Pattern matches that bind the branch** (these gain an `edges` binder; mostly mechanical):
- `Scheme.lean` structural lemmas — `intExpandBranches_openBranch_closed` (`:392-475`),
  `intExpandBranches_openBranch_sat` (`:485-582`), `intExpandBranches_openBranch_initial_mem`
  (`:589-...`). Each states `… = .openBranch b` and an inner `go … = .openBranch b`; the RHS
  becomes `.openBranch b edges` (a fresh `edges` existential/variable per lemma). These three are
  **the heaviest hit** because they do deep induction with `injection`/`simp only
  [intExpandBranches.go]` on the constructor; adding a field changes the `injection` arities.
- `Scheme.lean` `openBranch_countermodel` (`:730`, hypothesis `h : … = .openBranch b`) and
  `tableau_complete` (`:775`, the `cases … with | openBranch b =>` at `:783`).
- `Completeness.lean:87` (`intuitionisticTableau_complete`'s helper hypothesis
  `h : intuitionisticTableau φ = .openBranch b`) and the analogous `Minimal/Completeness.lean:94`.
- **Decision procedures** (currently ignore the branch, so trivially safe — just add `_`):
  `Intuitionistic/DecisionProcedure.lean:108` (`| .openBranch _ =>`),
  `Minimal/DecisionProcedure.lean:117` (`| .openBranch _ =>`). These become `.openBranch _ _`.
- **Classical tableau is a SEPARATE type** (`ClassicalTableauResult`, `Classical/Expansion.lean:57`)
  — NOT affected. `Classical/DecisionProcedure.lean:83` matches the classical type. No change.

**Net blast radius**: 1 type def + 3 constructor sites + ~8 match/statement sites, all in the
`Intuitionistic`/`Minimal` tableau subtree. No change outside
`Cslib/Logics/Propositional/Tableau/{Intuitionistic,Minimal}/`. The genuinely non-mechanical
edits are (a) the fuel=0 site `:182` (needs to pick the parallel edge set, not just the branch),
and (b) the three deep-induction structural lemmas whose `injection`/`simp` steps must absorb the
new field. **This plumbing change overlaps task 317's open structural lemmas** (`…_openBranch_sat`
leaf sorries) — coordinate, do it in one combined edit.

### Cheaper alternative to the type change (recommended to evaluate first)

`openBranch_countermodel`/`tableau_complete` are only ever invoked with the **fixed initial call**
`intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] (2^…) S.closurePred`. Instead of widening the
result type, add a **side lemma that recovers the final edges** as an existential:

```lean
lemma intExpandBranches_openBranch_edges (fuel) (branches expandedSets nextWorlds edgeSets) …
    (h : intExpandBranches … = .openBranch b) :
    ∃ edges, MonotoneEdges_witness … b edges ∧ <edge-persistence facts about b w.r.t. edges>
```

i.e. prove the *consequence you actually need* (the per-branch edge set exists and the valuation
is upward-closed w.r.t. `isAccessible` of that set) by induction on the loop, **without changing
the data type**. This keeps `IntTableauResult` untouched (zero blast radius on decision procedures
and the classical/minimal matchers) and confines all new work to one new Scheme.lean lemma proved
by the *same* induction skeleton already used by `intExpandBranches_openBranch_sat`. Given the
soundness loop-induction already threads `edges` through exactly this recursion
(`Soundness.lean` loop lemmas + `intExpandBranches_closed_unsat` with `intro b edges nw hmem` at
`Scheme.lean:269`), this existential-recovery route is likely **less invasive** than widening the
constructor. **Recommend the planner choose between (i) widen constructor vs (ii) existential
recovery lemma after one spike; default to (ii).**

---

## Recommended wiring mechanism

**Mirror the soundness `worldOf : Nat → World` + `MonotoneEdges` abstraction. Do NOT use `letI`
on `ℕ`, and prefer it over a bespoke wrapper type.**

Rationale and mechanics:

- **Why not `letI : Preorder ℕ := ⟨isAccessible edges⟩` at the bridge.** Two defects: (1) it
  creates a second `Preorder ℕ` instance → diamond; `≤`, `le_refl`, `omega`, and every
  `Nat.le_*` simp lemma become ambiguous/inapplicable inside the same scope (and `truthLemma`'s
  structural neighbours do genuine `Nat` counter/fuel arithmetic). (2) More fundamentally, the
  order used *inside* `truthLemma`/`openBranch_countermodel` is fixed when those lemmas are
  elaborated; a `letI` at the call site cannot change it. So `letI` is rejected.

- **Why not strictly necessary to introduce a `def IWorld (edges) := ℕ` wrapper.** A type synonym
  with `instance : Preorder (IWorld edges) := ⟨isAccessible edges, …⟩` is the textbook
  "same carrier, different order" idiom (cf. `OrderDual`, `Lex`) and would avoid clobbering
  `Nat`. It works, but it forces isAccessible to *be* a full `Preorder` (refl + trans as a `Bool`
  relation) and re-states the three lemmas over the wrapper. The soundness pattern is strictly
  more economical because it needs only the **one-directional** `MonotoneEdges`.

- **Recommended: generalize the three completeness lemmas to an abstract `World`,** exactly like
  `tableau_sound` (`Scheme.lean:245-288`) and `intBranchSatisfied` (`Soundness.lean:56`):
  ```lean
  lemma truthLemma {World} [Preorder World] (worldOf : Nat → World)
      (edges : IEdges) (hmono : MonotoneEdges worldOf edges)
      (S) (b) (hopen) (hsat) (φ) (w : Nat) :
      (… → IForces (val∘worldOf …) (S.modelBot b) (worldOf w) φ) ∧ (… ¬ …)
  ```
  where the valuation is `fun (x : World) p => ∃ w, worldOf w = x ∧ intExtractValuation b w p`
  (or, when `worldOf = id` and `World = ℕ` carrying the edge order, just `intExtractValuation b`).
  The F-imp case (`Scheme.lean:331-335`) currently consumes `hsat.sat_fimp` giving `w ≤ w'`; under
  the generalization it consumes `isAccessible edges w w'` and converts via `hmono` to
  `worldOf w ≤ worldOf w'`. **This is precisely the `IBranchSaturation.sat_fimp` restatement
  (`Scheme.lean:97`, currently `∃ w', w ≤ w' ∧ …`) that must change to `∃ w', isAccessible
  edges w w' ∧ …`** — Teammate A's siblings/transitivity territory and task 317's `sat_fimp`.

- **At the bridge** (`Completeness.lean:105-112` and `Minimal/Completeness.lean`):
  instantiate `IValid φ` / `MValid φ` with `World := ℕ`, the edge-order Preorder (or abstract
  `World` + `worldOf = id`), `val := intExtractValuation b`, and supply `v_uc` from the single
  edge-persistence lemma (Key Finding 5). For minimal, also supply `bf_uc` from the *same* lemma
  at `α := .bot`. Then `tableau_complete` discharges the rest. The `edges` needed here come from
  Q5's recovery (existential lemma (ii) or widened constructor (i)).

**Bottom line**: the cleanest mechanism is *not* a new instance and *not* a new type — it is to
**reuse the soundness `MonotoneEdges`/`worldOf` machinery verbatim on the completeness side**,
threading `edges` out of the loop via a recovery lemma.

---

## Reusable lemmas / definitions (file:line)

| Lemma / def | Location | Reuse for task 430 |
|---|---|---|
| `MonotoneEdges worldOf edges := ∀ w w', isAccessible edges w w' → worldOf w ≤ worldOf w'` | `Soundness.lean:346-348` | **The exact edge↔order bridge.** Reuse as-is on the completeness side. |
| `isAccessible_one_step : (child,parent) ∈ edges → isAccessible edges parent child = true` | `Soundness.lean:447-465` | One-step accessibility for the tree edge `(w',w)` added by `intFImpRule`. Solves seed Q#2 base case. |
| `isAccessible_go_mono_fuel` (fuel monotonicity of the DFS) | `Soundness.lean:505-529` | **Resolves the seed's fuel-bound worry** (Open Q#2): more fuel never loses reachability. |
| `monotoneEdges_go` (multi-step monotone lift via `isAccessible_one_step` + `le_trans` at `:567`) | `Soundness.lean:535-569` | The multi-step "accessibility ⇒ order" induction — **already proven**. Completeness needs the same shape. |
| `isAccessible_go_reach_nw_implies_reach_parent` | `Soundness.lean:577-…` | DFS reachability decomposition through a fresh world; reusable for the persistence-along-path argument. |
| `intBranchSatisfied {World}[Preorder World] val bf worldOf b` | `Soundness.lean:56-63` | The abstract-`World` satisfaction shape to mirror for the truth lemma's generalization. |
| `intExpandBranches_closed_unsat` (threads `edges` through the loop; `intro b edges nw hmem`) | used at `Scheme.lean:262-279` | Proof that the loop preserves the per-branch edge invariant — **template for the Q5 edge-recovery lemma (route ii)**. |
| `tableau_sound` (`worldOf := fun _ => w₀`; discharges `isAccessible edges w w' → worldOf w ≤ worldOf w'` at `:282-287`) | `Scheme.lean:245-288` | End-to-end demonstration that the abstract-`World`/`MonotoneEdges` wiring compiles and closes. |
| `iforces_persistence` (forcing persists for any `[Preorder World]` given `v_uc`+`bf_uc`) | `Kripke.lean:125-140` | Directly reusable once edge-upward-closure of the valuation is proved. |
| `applyPersistenceFixpoint_mem_preserved` (membership preserved across fixpoint) | `Scheme.lean:373-385` | Carries `T(α)@w' ∈ b` forward through the persistence fixpoint (append-only). |
| `propagatePersistence` copies **all** positive formulas (atoms AND ⊥) | `Rules.lean:125-140` | One persistence lemma ⇒ both `intExtractValuation` and `minBranchBotForces` upward-closure. |
| `minBranchBotForces b w` = "T(⊥)@w on b" | `Minimal/Soundness.lean:168` | Same shape as `intExtractValuation`; covered by the shared lemma. |

### Mathlib RTC / Preorder (seed Open Q#6)

- `Relation.ReflTransGen r` is **reflexive and transitive by construction**
  (`Relation.ReflTransGen.refl`, `.trans`, `.single`, `.head`/`.tail` induction). Using
  `le := Relation.ReflTransGen (parentChild edges)` as the world order makes refl+trans **free**,
  sidestepping any need to prove the `Bool` DFS is transitive.
- The bridge `isAccessible edges w w' = true ↔ ReflTransGen (parentChild) w w'` is the only cost:
  `→`/`forward` follows from `isAccessible_one_step` + the existing DFS lemmas;
  `←`/`backward` needs fuel-sufficiency, for which `isAccessible_go_mono_fuel` already exists.
- **Recommendation**: do NOT make `isAccessible` itself a `Preorder` (would require proving Bool
  transitivity directly). Instead either (a) reuse the soundness `MonotoneEdges`/abstract-`World`
  route (cheapest — no transitivity proof needed at all), or (b) if a concrete `ℕ`-carried order
  is preferred, define it via `Relation.ReflTransGen` and bridge to `isAccessible` only where the
  loop produces `Bool` facts. Route (a) is preferred.

---

## Confidence Level

**High** on the structural/wiring findings, all grounded in direct reads:
- Edges threaded internally but dropped at the result type — **verified** (`Expansion.lean:79,
  170-235`).
- Edges not recoverable from `b` — **verified** (`IBranch`/`IEdges` defs, sibling worlds).
- `letI`-on-`ℕ` is the wrong mechanism; statements bake in ambient order — **verified**
  (`truthLemma`/`openBranch_countermodel`/`tableau_complete` signatures).
- Soundness already provides `MonotoneEdges` + the full `isAccessible` lemma suite, and a single
  persistence lemma covers int+min — **verified** (`Soundness.lean:346-577`, `Rules.lean:125`,
  `Minimal/Soundness.lean:168`).

**Medium** on the recommendation that the **existential edge-recovery lemma (route ii)** beats
widening the `openBranch` constructor (route i): both are viable; route ii avoids touching the
decision procedures and the result type but requires one new induction lemma over the loop. A
short spike (replicating the `intExpandBranches_closed_unsat` induction) would confirm. No new
axioms are introduced by either route.

**Dependency on Teammate A**: the `sat_fimp` restatement (`w ≤ w'` → `isAccessible edges w w'`,
`Scheme.lean:97`) and the question of whether `isAccessible` needs full transitivity vs. only the
one-directional `MonotoneEdges` lift hinge on the siblings/accessibility determination Teammate A
owns. My recommendation (abstract `World` + `MonotoneEdges`, no Bool transitivity proof) is robust
to either outcome.
