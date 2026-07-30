# Seed Research Report: Atom Persistence / Upward-Closure for `intExpandBranches` Open Branches

**Task**: 430 (`prove_atom_persistence_upward_closure_for_intexpan`)
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
**Parent**: 317 (`propositional_tableau_completeness`)
**Topic**: PL-Tableau
**Type**: cslib · **Status**: seed (researched — needs deeper investigation)
**Author note**: This is an orchestrator-authored seed grounded in a direct read of the
relevant code. It identifies the precise obligation, maps the code, and — most importantly —
surfaces a **design tension that must be resolved before the lemma can be stated provably**.
Treat the "Open Questions" section as the actual research agenda.

---

## 1. Objective

Discharge the two validity-bridge `sorry`s left by task 317:

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:112`
  (`intuitionisticTableau_complete`)
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:109`
  (`minimalTableau_complete`)

Both reduce to one structural fact: the extracted branch valuation is **upward-closed**
(atom persistence). The lemma to prove, in its naive form:

```
intExtractValuation b w p  ∧  w ≤ w'  →  intExtractValuation b w' p
```

where (verified, `Soundness.lean:1640`):

```lean
def intExtractValuation (b : IBranch Atom) (w : Nat) (p : Atom) : Prop :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)
```

So concretely: `T(atom p)@w ∈ b ∧ w ≤ w' → T(atom p)@w' ∈ b`, for any branch `b` returned
as `intExpandBranches ... = .openBranch b`.

---

## 2. Why the bridges need exactly this

The bridge proof (verified, `Completeness.lean:105-112`) is:

```lean
theorem intuitionisticTableau_complete (φ) (h : IValid φ) : intuitionisticTableau φ = .closed := by
  apply tableau_complete intScheme
  intro _b
  sorry  -- need: IForces (intExtractValuation _b) intBotForces 0 φ
```

`tableau_complete intScheme` (`Scheme.lean:775`) demands
`hvalid : ∀ b, IForces (intExtractValuation b) (intScheme.modelBot b) 0 φ`.

`IValid` is (verified, `Kripke.lean:142-147`):

```lean
def IValid (φ) : Prop :=
  ∀ (World : Type v) [Preorder World] (val : World → Atom → Prop),
    (∀ {w w'} (p), w ≤ w' → val w p → val w' p) →   -- ← upward-closure obligation
    … → IForces val … φ
```

So to feed `IValid φ` we instantiate `World`, pick a `Preorder`, set `val := intExtractValuation b`,
and **must supply the upward-closure proof**. That proof is task 430. For the minimal bridge,
`MValid` (`Kripke.lean:153-157`) additionally requires `bf_upward_closed` for
`minBranchBotForces b` — see §6.

Crucially, **`IValid`/`MValid` quantify over *all* `Preorder`s** — we are free to choose the
ordering on worlds. This freedom is the key to resolving the design tension below.

---

## 3. The persistence machinery (code map)

| Definition | File:line | Role |
|---|---|---|
| `IBranch := List (ISF Atom)` | `Rules.lean:71` | a branch is a list of signed, world-labeled formulas |
| `IEdges := List (Nat × Nat)` | `Rules.lean:80` | parent-child edges `(child, parent)` |
| `isAccessible edges w w'` | `Rules.lean:87` | **reflexive-transitive closure** of parent-child; the *real* Kripke accessibility |
| `posFormulasAt b w` | `Rules.lean:125` | all `T`-formulas at world `w` |
| `propagatePersistence b w w'` | `Rules.lean:138` | copies **every** `T(α)@w` to `w'` (label-rewrite) |
| `intFImpRule φ ψ w nw b` | `Rules.lean:153` | F(φ→ψ) world-creation: new child `w'=nw`, adds `T(φ)@w'`, `F(ψ)@w'`, **and `propagatePersistence b w w'`**, edge `(w',w)` |
| `intTImpRule φ ψ w edges b` | `Rules.lean:173` | T(φ→ψ): for each `w'` with `isAccessible edges w w'`, if `T(φ)@w'` then add `T(ψ)@w'` |
| `applyAllTImpRules` / `applyPersistenceFixpoint` | `Expansion.lean:118/133` | append-only; iterate persistence to fixpoint |
| `applyPersistenceFixpoint_mem_preserved` | `Scheme.lean:373` | **already proved**: membership preserved across the fixpoint (append-only) |

Key mechanical facts (verified by reading the defs):

1. `propagatePersistence` copies `T(α)@w` to `w'` **only when explicitly invoked**, and it is
   invoked **only inside `intFImpRule`**, i.e. **only from a parent `w` to its freshly-created
   direct child `w' = nextWorld`** (`Rules.lean:157`).
2. Fresh worlds are allocated by an incrementing `nextWorld` counter, so a child's label is
   always numerically **greater** than its parent's. Hence *tree-edge `(w',w)` ⟹ `w < w'`*.
3. The expansion is **append-only** for membership (`applyPersistenceFixpoint_mem_preserved`),
   so once `T(atom p)@w'` lands on a branch it stays.

---

## 4. ⚠ Central design tension (the headline finding)

**The naive lemma in §1 is very likely FALSE as stated, because the countermodel currently
fixes `World = ℕ` ordered by `≤` on `ℕ`, while persistence is propagated along the
parent-child *tree*, not along `≤`.**

Evidence:
- The countermodel is instantiated at `World = ℕ` with the default `≤` Preorder — see the doc
  comments at `openBranch_countermodel` / `tableau_complete` (`Scheme.lean` ~lines 759-766:
  "applied at World `= ℕ`, `val = intExtractValuation b`, with the upward-closure of …").
- `propagatePersistence` only copies a parent's `T`-atoms to its **direct child**. Consider two
  F-implications at world `0` producing two children, worlds `1` and `2` (siblings, both edges
  point to parent `0`). Then `1 ≤ 2` numerically, but world `2` is **not** accessible from world
  `1`, and `propagatePersistence` never copies `T(atom p)@1` to world `2`. So
  `intExtractValuation b 1 p` can hold while `intExtractValuation b 2 p` fails — **violating
  upward-closure w.r.t. `≤` on `ℕ`**.

This is the **same class of defect** already documented for task 301
(`specs/301_temporal_tableau`): `ordConstraints_strict` was found *false as stated* because the
world/time labels do not respect the claimed numeric ordering invariant. See
`specs/301_temporal_tableau/.orchestrator-handoff.json` ("DESIGN FLAW (not proof complexity)…").
The spawn analysis for this task anticipated the same: *"If `≤` on Nat conflicts with the
sibling-world tree structure, fall back to restructuring the countermodel to use `isAccessible`
edges-based Preorder."*

**The resolution leverages the freedom from §2:** `IValid`/`MValid` hold for *every* `Preorder`,
so the countermodel should not use `≤` on `ℕ` — it should use the **edge-based accessibility
relation** as its Preorder. Under that ordering, upward-closure becomes *true and provable*
because `propagatePersistence` is exactly the operation that enforces it along edges.

---

## 5. Candidate approaches (ranked)

### Approach A — Edge-based Preorder (recommended)
Make the countermodel's world ordering `w ≤ w' := isAccessible edges w w'` (for the branch's
edge set), and prove `intExtractValuation b` is upward-closed **w.r.t. that order**.

Required pieces:
1. **`isAccessible` is a lawful `Preorder`** on `ℕ` (for a fixed `edges`):
   - reflexive: immediate from `Rules.lean:88` (`w == w' → true`);
   - transitive: prove `isAccessible edges a b → isAccessible edges b c → isAccessible edges a c`
     (closure of the DFS — a non-trivial but self-contained lemma; mind the fuel bound at
     `Rules.lean:101`, `fuel = edges.length`).
2. **One-step atom persistence**: along a single tree edge `(w', w)` created by `intFImpRule`,
   `T(atom p)@w ∈ b → T(atom p)@w' ∈ b` (this is exactly what `propagatePersistence` adds; combine
   with `applyPersistenceFixpoint_mem_preserved` to carry it forward).
3. **Multi-step**: lift (2) along `isAccessible` by induction on the accessibility path, using (1).
4. **Rewire the bridges/countermodel** to instantiate `IValid`/`MValid` at this Preorder instead
   of `≤` on `ℕ`.

**Cost/risk**: This changes the Preorder used by `truthLemma` and `openBranch_countermodel`.
Task 317 already proved the `truthLemma` `and`/`or` cases and the `imp` F-direction **using
`w ≤ w'`**. Those proofs must be re-checked under `≤ := isAccessible`. The `imp` cases are the
sensitive ones (they quantify over `w' ≥ w`); `and`/`or` are world-local and should be
ordering-agnostic. **Coordinate with task 317** — this approach may require editing
`Scheme.lean` definitions that 317 is still working on (the `intStepBranch` leaf sorries and the
`imp` T-direction). See §7.

### Approach B — Prove the tree is actually a chain (cheap if true, likely false)
If the expansion only ever produces a **linear** chain of worlds (no siblings), then `≤` on `ℕ`
*would* coincide with accessibility and the naive lemma holds. **First research action: decide
whether siblings can occur.** Inspect whether multiple `F(→)` formulas at the same world (or at
incomparable worlds) can both fire within one open branch. Reading `intStepBranch` /
`intExpandBranches` (`Scheme.lean` expansion loop) settles this. *Prior:* siblings almost
certainly occur, so this approach probably fails — but confirming it cheaply rules out the
expensive Approach A path and documents why.

### Approach C — Strengthen `propagatePersistence` to copy along `≤` (do not pursue)
Copying parent atoms to *all* numerically-greater worlds would force upward-closure on `≤` by
construction, but it changes the tableau's operational semantics and would **invalidate the
already-green soundness proof** (`Soundness.lean` reasons about `propagatePersistence` at
`:212`, `:1016`). Rejected unless A and B both fail.

---

## 6. Minimal-logic variant (second bridge)

`Minimal/Completeness.lean:109` (`minimalTableau_complete`) needs the **same** atom-persistence
fact (the valuation is shared — `intExtractValuation` is "the shared valuation used by both the
intuitionistic and minimal countermodel constructions", `Soundness.lean:1638`), **plus**
`bf_upward_closed` for `minBranchBotForces b` (the minimal `botForces`). Investigate
`minBranchBotForces`:
- If it is defined as "`F(⊥)`/closure-driven forcing of ⊥ at accessible worlds", it should be
  upward-closed by the *same* edge-propagation argument as atoms — try to **prove both from one
  generic lemma** over the saturation/edge structure (mirrors how task 369 parameterized int+min
  over `(closurePred, modelBot)`; the `IntMinScheme` structure at `Scheme.lean:120` is the natural
  home for a shared `val_upward_closed` / `bf_upward_closed` field).
- Deliverable should expose the persistence fact **once** (e.g. as a new `IntMinScheme` field or a
  standalone lemma quantified over the scheme), not duplicated across int and min.

---

## 7. Coordination with task 317 (important)

Task 317 is `[BLOCKED]` on 430 and still owns these `Scheme.lean` sorries:
- `truthLemma` **imp T-direction** (`Scheme.lean` ~:330);
- the three `intExpandBranches_openBranch_sat` **leaf** sorries (`intStepBranch` internals,
  ~:511/:566/:580).

If Approach A is chosen, the change of Preorder touches `truthLemma`/`openBranch_countermodel`,
which **overlaps 317's territory**. Recommended sequencing:
1. Do the **research/decision** (siblings? which approach?) first and record it here.
2. If Approach A: land the *self-contained* pieces first — the `Preorder`/transitivity instance
   for `isAccessible` and the edge-persistence lemma — as standalone additions that do **not**
   require editing 317's open proofs.
3. Defer the *rewiring* of the bridges + any `truthLemma` re-statement until 317's `truthLemma`
   is otherwise stable, or coordinate a single combined edit. Avoid two agents editing the
   `truthLemma` block concurrently (this caused context/merge thrash during 317).

---

## 8. Open questions (the actual research agenda)

1. **Do sibling worlds occur?** Trace `intStepBranch`/`intExpandBranches` to confirm whether ≥2
   children of a single parent (or worlds on incomparable branches) can coexist on one open
   branch. This decides A vs B. *(Highest priority — cheap, decisive.)*
2. **Is `isAccessible` transitive?** Prove or refute
   `isAccessible e a b → isAccessible e b c → isAccessible e a c`. Watch the fuel bound
   (`edges.length`) — a path through the closure may need more steps than a single DFS budget;
   may need a fuel-monotonicity / "enough fuel" lemma.
3. **Does the chosen Preorder break the already-proved `truthLemma` cases?** Specifically the
   `imp` F-direction proved in 317 under `w ≤ w'`. Re-derive under `≤ := isAccessible`.
4. **Is `minBranchBotForces b` upward-closed under the same order?** (§6) — read its definition.
5. **Edge bookkeeping at the bridge site.** `openBranch_countermodel`/`tableau_complete` must
   thread the branch's `edges` to define the Preorder. Where do the final `edges` live for a
   returned `openBranch b`? Is the edge list recoverable from `b`, or must
   `intExpandBranches` also return it? (May require returning/recovering `IEdges` alongside `b`.)
6. **Reflexive-transitive-closure already in Mathlib?** Consider `Relation.ReflTransGen` for the
   accessibility relation/Preorder instead of the bespoke fueled `isAccessible`, which could make
   transitivity free. Evaluate cost of bridging the `Bool` DFS to a `Prop` closure.

---

## 9. Verification criteria (definition of done)

- Both bridges (`Intuitionistic/Completeness.lean:112`, `Minimal/Completeness.lean:109`) are
  `sorry`-free.
- A single reusable persistence/upward-closure lemma (preferably a scheme field) is exposed and
  consumed by both bridges (no int/min duplication).
- No new `axiom`s (`lean_verify` on the bridge theorems and the new lemma).
- `lake build` green for `Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness`,
  `…Minimal.Completeness`, and `…Intuitionistic.Scheme`.
- Soundness remains green (Approach C is rejected precisely to protect this).
- Full CI before PR: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`, `lake test`.

---

## 10. Pointers

- Bridges: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:105-112`,
  `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (~:100-109).
- Valuation: `…/Intuitionistic/Soundness.lean:1640` (`intExtractValuation`), `:1647`
  (`intBotForces`).
- Semantics: `Cslib/Logics/Propositional/Semantics/Kripke.lean` — `KripkeModel:58`,
  `IForces:81`, `iforces_persistence:125`, `IValid:145`, `MValid:153`.
- Persistence rules: `…/Intuitionistic/Rules.lean:87` (`isAccessible`), `:138`
  (`propagatePersistence`), `:153` (`intFImpRule`), `:173` (`intTImpRule`).
- Already-proved helper: `…/Intuitionistic/Scheme.lean:373`
  (`applyPersistenceFixpoint_mem_preserved`); scheme structure `IntMinScheme` at `Scheme.lean:120`;
  saturation structure `IBranchSaturation` at `Scheme.lean:72`.
- Analogous prior design flaw: `specs/301_temporal_tableau/.orchestrator-handoff.json`
  (`ordConstraints_strict` false-as-stated).
- Parent handoff: `specs/317_propositional_tableau_completeness/.orchestrator-handoff.json`
  (blocker B3 = atom persistence).
