# Teammate D Findings — Shared-Lemma Placement & Strategic Generalization (Task 430)

**Author**: Teammate D (HORIZONS) · **Session**: sess_1782818058_465873
**Scope**: Q4 (minBranchBotForces upward-closure + IntMinScheme field decision) + cross-task generalization.
**Method**: targeted reads only (no full `lake build`), all claims grounded in file:line.

---

## Key Findings

### KF1 — `minBranchBotForces` is the SAME predicate shape as `intExtractValuation`

`minBranchBotForces` (`Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean:168-170`):

```lean
def minBranchBotForces (b : IBranch Atom) (w : Nat) : Prop :=
  b.any (fun sf => sf.sign == .pos && sf.formula == (HasBot.bot : Proposition Atom) && sf.label == w)
```

`intExtractValuation` (`Intuitionistic/Soundness.lean:1640`):

```lean
def intExtractValuation (b : IBranch Atom) (w : Nat) (p : Atom) : Prop :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)
```

These are **the identical "positive (T) signed-formula at label `w`" membership query**, differing
only in the formula slot (`.atom p` vs `⊥`). The `minBranchBotForces` docstring
(`Minimal/Soundness.lean:165-167`) already asserts the consequence we need:

> "This is upward-closed by the persistence fixpoint: if T(⊥) is at world w and w ≤ w', then
> T(⊥) is also at w' (since T(⊥) is a T-formula and persistence propagates all T-formulas from
> accessible worlds)."

**Consequence (answers Q4 primary):** `minBranchBotForces b` IS upward-closed under exactly the
same order chosen for atoms. Both reduce to one fact: *T-formula membership propagates along the
persistence relation*. Whatever order discharges atom persistence (the edge-accessibility
Preorder of seed §4–5, NOT `≤` on ℕ) discharges bot persistence verbatim. So **one shared lemma
proves both bridges.**

### KF2 — The shared persistence fact must be stated over an arbitrary formula

The single generic lemma (its content is "T-persistence", instantiated twice):

```lean
/-- Positive (T) signed-formula membership at a world. -/
def posAtWorld (b : IBranch Atom) (φ : Proposition Atom) (w : Nat) : Prop :=
  b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w)
-- intExtractValuation b w p = posAtWorld b (.atom p) w        (definitional)
-- minBranchBotForces b w   = posAtWorld b ⊥ w                  (definitional)

/-- Shared persistence/upward-closure core (parametric in φ). -/
theorem posAtWorld_upward_closed
    (b : IBranch Atom) (edges : IEdges)
    (hpers : IBranchPersistence b edges)          -- new saturation fact, see KF4
    (φ : Proposition Atom) {w w' : Nat}
    (hacc : isAccessible edges w w' = true)        -- the CHOSEN order (seed Approach A)
    (h : posAtWorld b φ w = true) : posAtWorld b φ w' = true
```

Corollaries (consumed by the two bridges, no int/min duplication):

```lean
theorem intExtractValuation_upward_closed … := posAtWorld_upward_closed b edges hpers (.atom p) …
theorem minBranchBotForces_upward_closed  … := posAtWorld_upward_closed b edges hpers ⊥        …
```

### KF3 — Recommendation: do NOT add `val_upward_closed`/`bf_upward_closed` fields to `IntMinScheme`

Read of `IntMinScheme` (`Intuitionistic/Scheme.lean:116-144`, fields `closurePred`, `modelBot`,
`bot_truth`, `no_contradiction`) plus its module doc (`Scheme.lean:24-34`) shows the maintainers
**already considered and deliberately rejected** an upward-closure field:

> "`modelBot_uc` (upward-closure of `modelBot b`) is omitted from this interface because it
> requires a saturation hypothesis for the minimal scheme; it is proved inline inside the
> parametric truth lemma." (`Scheme.lean:32-34`)

Concrete reasons a field is the wrong home:

1. **`IntMinScheme` bundles only the two *divergence* points** (closurePred, modelBot —
   `Scheme.lean:14-18`). `val_upward_closed` for `intExtractValuation` is **identical across both
   schemes** (non-divergent), so it does not belong in a divergence-bundling structure at all.
2. **Order-coupling.** Every other `IntMinScheme` field is stated *without* a Preorder. An
   upward-closure field must name the order — and the order is exactly the contested quantity
   (`≤`-on-ℕ vs `isAccessible`, seed §4). Putting it in the structure freezes the order choice
   into the interface that 317's `truthLemma`/`tableau_complete` build on.
3. **`edges` are not in scope of the structure.** UC under the correct (edge) order needs the
   branch's `IEdges`; `IntMinScheme` carries none, and `IBranchSaturation` (`Scheme.lean:72`) is
   indexed by `b` only — see KF4.

**Preferred design:** two standalone corollaries of `posAtWorld_upward_closed` (KF2), kept as free
lemmas next to the definitions. The bridge feeds them directly into `IValid`/`MValid`.

**If the team insists on structural uniformity** (mirroring how task 317 added `no_contradiction`
as a per-scheme obligation field): add exactly **ONE** field, not two —

```lean
  /-- Upward-closure of the countermodel bot predicate along the branch's accessibility order. -/
  modelBot_uc : ∀ (b : IBranch Atom) (edges : IEdges), IBranchPersistence b edges →
      ∀ {w w' : Nat}, isAccessible edges w w' = true → modelBot b w → modelBot b w'
```

— discharged trivially for `intScheme` (`modelBot = fun _ _ => False`, vacuous) and via
`minBranchBotForces_upward_closed` for `minScheme`. Keep `val`-UC as a free shared lemma regardless
(it is not divergent). Net recommendation: **standalone lemmas, no new field**; the one-field
fallback is acceptable only if uniform plumbing is judged worth re-coupling the structure to the
order.

### KF4 — The missing ingredient is an *edge-indexed* persistence saturation, parallel to `_openBranch_sat`

`IBranchSaturation` (`Scheme.lean:72-99`) does NOT contain a persistence/edge field, and is indexed
by `b` alone (no `edges`). Its `sat_fimp` (`Scheme.lean:94-99`) states the F→ witness with **numeric
`w ≤ w'`** — itself an instance of the seed's design tension and not the fact we need.

The fact 430 actually needs (T-formula propagation along edges) should be produced as a **new,
self-contained extraction** parallel to `intExpandBranches_openBranch_sat` (`Scheme.lean:748-749`):

```lean
def IBranchPersistence (b : IBranch Atom) (edges : IEdges) : Prop :=
  ∀ (φ : Proposition Atom) {w w' : Nat},
    isAccessible edges w w' = true → posAtWorld b φ w = true → posAtWorld b φ w' = true

theorem intExpandBranches_openBranch_persistence … : IBranchPersistence b edges
```

This is the heart of 430. It is provable from the persistence machinery the seed already mapped
(`propagatePersistence` `Rules.lean:138`; `applyPersistenceFixpoint_mem_preserved` `Scheme.lean:373`;
one-step along a tree edge + induction on `isAccessible`), and it **does not touch the `truthLemma`
block** (317 territory).

### KF5 — ⚠ Structural blocker: the open-branch result discards `edges` (sharpens seed Q5)

`IntTableauResult.openBranch` carries only the branch:
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean:79`

```lean
| openBranch : IBranch Atom → IntTableauResult Atom
```

…yet `intExpandBranches` threads `edgeSets : List IEdges` internally
(`Expansion.lean:174`, `:194-204`). So at the bridge site (`openBranch_countermodel`,
`tableau_complete`) **the branch's final `edges` are not recoverable** — which is precisely what
the edge-based Preorder (seed Approach A) needs. Resolution options, in rising cost:
(a) extend the constructor to `openBranch : IBranch Atom → IEdges → …` (touches soundness +
317's `openBranch_countermodel`); (b) reconstruct edges deterministically from `b`'s labels;
(c) re-run the edge bookkeeping at the bridge. This is a real prerequisite, not a detail — flag it
to the planner.

---

## Strategic Generalization

### Placement that minimizes coupling (and avoids 317's in-flight `truthLemma`)

The **order-locking is the entanglement**, not the persistence lemma. Evidence: `IForces`
(`Kripke.lean:81-88`) is `[Preorder World]`-implicit; `tableau_complete`'s `hvalid`
(`Scheme.lean:776`) is `IForces (intExtractValuation b) (S.modelBot b) 0 φ` which forces
`World = ℕ` with the **ambient default `≤`** instance. The bridge sorries
(`Intuitionistic/Completeness.lean:112`, `Minimal/Completeness.lean:109`) must therefore produce
`IForces` *at that same `≤`-on-ℕ order* — but UC under `≤`-on-ℕ is false (seed §4). So the two
bridge sorries **cannot be closed** until the Preorder used by `truthLemma` /
`openBranch_countermodel` / `tableau_complete` is switched to edge-accessibility — and those live in
317's territory.

Recommended split (composes cleanly, three of four pieces are conflict-free):

1. **Land now, zero 317 conflict** (own a NEW file, e.g.
   `Intuitionistic/Persistence.lean`, or append near the defs in `…/Soundness.lean:1640` /
   `Minimal/Soundness.lean:168`):
   - `isAccessible` is a lawful `Preorder` (refl `Rules.lean:88`; transitivity is the non-trivial
     fueled-DFS lemma, seed Q2 — fuel bound `Rules.lean:101`).
   - `IBranchPersistence` + `intExpandBranches_openBranch_persistence` (KF4).
   - `posAtWorld_upward_closed` + the two corollaries (KF2).
2. **Coordinate with 317** (touches the contested order — do LAST, single combined edit):
   - resolve KF5 (recover `edges` at the bridge), switch the Preorder, re-check the `imp` cases of
     `truthLemma` under `≤ := isAccessible`, then discharge both bridge sorries via the corollaries.

This keeps 430 from editing the `truthLemma` imp-T block and the `intStepBranch` leaf sorries that
317 still owns (seed §7), while still delivering the reusable core.

### The same defect family recurs — factor a shared "branch accessibility Preorder" utility

The `≤`-on-ℕ-labels vs tree/edge-accessibility mismatch is **not local to PL-int/min**:

- **Temporal (task 301)** — `ordConstraints_strict` is documented *false as stated* and BLOCKED in
  `Cslib/Logics/Temporal/Tableau/Completeness.lean:34-70`, `:255-259`, `:330-337`. The in-file fix
  note even proposes "use a topological sort to build [the order]" — the same remedy as switching
  from numeric `≤` to a derived accessibility order.
- **Modal tableaux (299/385)** build world trees in the same numeric-label style (PL-tableau
  analogues under `Cslib/Logics/Modal/Metalogic/…/Completeness.lean`); they will hit the identical
  order-vs-tree question when their countermodels are wired.

**Opportunity (concrete):** factor an `edges : List (Nat × Nat) → Preorder Nat` utility = the
reflexive-transitive closure of parent-child edges, with the transitivity lemma proved once.
`Relation.ReflTransGen` is **not yet used anywhere in `Cslib/Logics/`** (grep: 0 hits) and is the
natural Mathlib backing — bridging the `Bool` DFS `isAccessible` (`Rules.lean:87-101`) to a `Prop`
`ReflTransGen` of the edge step would make transitivity free (seed Q6) and give a single reusable
`Preorder` construction serving 430, 301, and 299/385. Recommend the 430 transitivity lemma be
written against this general edge-RTC shape (not bespoke to `isAccessible`'s fuel), so it lifts to
the other tableaux without rework. Keep scope discipline: build the utility *as a byproduct* of 430,
do not expand 430 to retrofit 301/modal.

---

## Confidence Level

**High** on:
- KF1 (predicate-shape identity ⇒ one shared lemma covers both bridges) — direct read of both defs.
- KF3 (no field; structure deliberately omits UC; val-UC is non-divergent) — direct read of struct
  + its module doc.
- The order-locking entanglement with 317 (`IForces` Preorder-implicit forced to `≤`-on-ℕ at the
  bridge) — direct read of `Kripke.lean:81-88`, `Scheme.lean:776`, both `Completeness.lean` sorries.
- KF5 (edges discarded by `openBranch`) — direct read of `Expansion.lean:79` vs `:174`.

**Medium** on:
- Exact signature of `IBranchPersistence` / its extraction proof difficulty (KF4) — proof not
  attempted; depends on the one-step edge-persistence lemma and `isAccessible` transitivity, both
  unproven (seed Q2). No `lake build` run per frugality.
- Reusability across 301/modal as a single utility — pattern match is strong (301 confirmed in
  file), but modal tableau countermodel wiring not deeply inspected this pass.

**No new axioms** proposed anywhere. The recommendation is structural (shared parametric lemma +
corollaries), not a sorry/axiom bridge.
