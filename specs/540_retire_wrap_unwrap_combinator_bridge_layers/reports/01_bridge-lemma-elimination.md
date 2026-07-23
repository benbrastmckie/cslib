# Research Report: Bridge-Lemma Elimination (wrap/unwrap + embedding-rfl layers)

**Task:** 540 — Retire wrap/unwrap combinator bridge layers and per-target embedding-rfl restatements
**Type:** cslib (refactor / consolidation)
**Date:** 2026-07-23
**Zero-debt note:** This is a pure consolidation refactor. No `sorry`, no new axioms, and no vacuous
definitions are required or recommended anywhere in the proposed work. Every deletion is replaced by
an existing or once-proved generic surface.

---

## 1. Executive Summary

The task identifies four bridge/restatement layers to retire. Research confirms the diagnosis is
**substantially correct** but surfaces **three scope corrections** the planner must incorporate:

1. **wrap/unwrap is already redundant with existing Foundations API** — not merely re-provable, but
   literally re-declaring `InferenceSystem.DerivableIn.fromDerivation` / `.toDerivation`, which
   already have bidirectional `Coe` instances (`InferenceSystem.lean:71-85`). Reuse-first verdict:
   **do NOT introduce a new bridge typeclass**; the combinator content is *already proved once* in
   `Foundations/Logic/Theorems/{Combinators,Propositional/Core,Propositional/Connectives}.lean`.
   What is missing is a *raw-derivation-typed* thin generic layer (returns `S⇓φ` rather than
   `DerivableIn S φ`), which can be proved once over the `InferenceSystem` instance.

2. **The embedding-rfl drop set is smaller than "34".** The PL→{Modal,Temporal,Bimodal} embeddings
   (`toModal`/`toTemporal`/`PL.Proposition.toBimodal`) *are* `φ.embed` and their `_atom/_bot/_imp`
   restatements duplicate the generic `embed_*` lemmas. But the **Modal→Bimodal** (`Modal.Proposition.toBimodal`,
   `ModalEmbedding.lean`) and **Temporal→Bimodal** (`Temporal.Formula.toBimodal`, `TemporalEmbedding.lean`)
   embeddings are **separate structural recursions, NOT instances of `PL.embed`** — their restatements
   **cannot** be folded into `embed_*` and must be retained (or given their own generic skeleton, which
   is out of scope). The task's inclusion of the ModalEmbedding/TemporalEmbedding rfl blocks in the drop
   set is incorrect for those two files.

3. **Item 3 (route Modal reproofs through the generic layer) collides with the SCOPE GUARD.** Modal's
   `imp_trans0` and siblings work over a *variable* `Axioms : Proposition → Prop` predicate with axiom
   witnesses passed explicitly, and `imp_trans0` itself calls `deductionTheorem`. Routing them through
   the generic combinator layer requires the `MinimalHilbert (Modal.HilbertOf Axioms)` instance that
   lives in the scope-guarded `Modal/Metalogic/GenericMCSBridge.lean`. *Using* that existing instance is
   fine; *modifying* the bridge is not. This item is partially entangled and should be de-risked or
   deferred (see §6).

---

## 2. Reuse-First Findings (mandatory check)

| Needed capability | Already exists in CSLib? | Location |
|---|---|---|
| `DerivationTree → Nonempty` (`wrap`) | **YES** — `InferenceSystem.DerivableIn.fromDerivation` + `Coe (S⇓a) (DerivableIn S a)` | `Foundations/Logic/InferenceSystem.lean:71-75` |
| `Nonempty → DerivationTree` (`unwrap`) | **YES** — `InferenceSystem.DerivableIn.toDerivation` (= `Classical.choice`) + noncomputable `Coe (DerivableIn S a) (S⇓a)` | `Foundations/Logic/InferenceSystem.lean:78-85` |
| Generic combinators (imp_trans, identity, pairing, dni, combine_imp_conj/_3, flip, b_combinator) | **YES** — proved once over `[InferenceSystem S F]` | `Foundations/Logic/Theorems/Combinators.lean:53-340` |
| Generic propositional theorems (double_negation, efq_axiom, lce_imp, rce_imp, raa, efq_neg, peirce_axiom, rcp, neg_identity) | **YES** | `Foundations/Logic/Theorems/Propositional/Core.lean` |
| Generic connectives (classical_merge, iff_intro, contraposition, contrapose_imp/iff, iff_neg_intro, demorgan_*) | **YES** | `Foundations/Logic/Theorems/Propositional/Connectives.lean` |
| Generic PL embedding equational lemmas (`embed_atom/bot/imp/and/or`) | **YES** — `@[simp]` | `Logics/Propositional/Embedding.lean:90-119` |
| Raw-`S⇓φ`-typed thin combinator layer (returns derivation, not `DerivableIn`) | **NO** — this is the one new (thin, once-proved) surface to add | (to create) |

**Key structural fact.** For `Bimodal.HilbertTM` and `Temporal.HilbertBX`, the `InferenceSystem`
instance sets `derivation φ := DerivationTree FrameClass.Base [] φ` (`Bimodal/ProofSystem/Instances.lean:47-50`;
analogous for Temporal). Therefore `HilbertTM⇓φ` **is definitionally** `DerivationTree FrameClass.Base [] φ`,
and `DerivableIn HilbertTM φ = Nonempty (DerivationTree FrameClass.Base [] φ)`. The `wrap`/`unwrap`
pair is exactly the `Nonempty` (un)wrapping the InferenceSystem API already provides.

`wrap d = ⟨d⟩` ≡ `DerivableIn.fromDerivation d`.
`unwrap h = h.some` ≡ `DerivableIn.toDerivation h` (`Nonempty.some` is `Classical.choice`).

---

## 3. Layer Inventory (what exists today)

### 3a. wrap/unwrap primitive pairs (3 sites — all deletable)
- `Temporal/Metalogic/PropositionalHelpers.lean:51,56` (`wrap`, `unwrap`)
- `Bimodal/Theorems/Perpetuity/Helpers.lean:56,60` (`wrap`, `unwrap`)
- `Bimodal/Theorems/Propositional/Connectives.lean:45,50` (`wrap'`, `unwrap'` — themselves aliases of the Perpetuity pair)

### 3b. Per-target combinator restatement defs (the "28 defs / ~58 unwrap uses")
- **Temporal `PropositionalHelpers.lean`**: 8 delegating defs (`doubleNegation`, `efqAxiom`, `impTrans`,
  `pairing`, `lceImp`, `rceImp`, `dni`, `identity`, `demorganDisjNegBackward`).
- **Bimodal `Perpetuity/Helpers.lean`**: 8 delegating combinator defs (`impTrans`, `identity`,
  `combineImpConj3`, `combineImpConj`, `dni`, `contraposition`, `doubleNegation`, `lceImp`, `rceImp`)
  **plus 4 genuinely tree-structural helpers** (`boxToFuture`, `boxToPast`, `boxToPresent`,
  `tempFutureDerived`) that must stay.
- **Bimodal `Theorems/Propositional/Core.lean`**: 8 delegating defs (`lem`, `efqAxiom`, `peirceAxiom`,
  `doubleNegation`, `raa`, `efqNeg`, `lceImp`, `rceImp`) **plus 5 context/tree-structural defs**
  (`ecq`, `ldi`, `rdi`, `rcp`, `lce`, `rce`) that must stay (they use `DerivationTree.assumption`,
  `weakening`, `bCombinator` directly).
- **Bimodal `Theorems/Propositional/Connectives.lean`**: ~9 delegating defs (`classicalMerge`,
  `iffIntro`, `contraposeImp`, `contraposition`, `contraposeIff`, `iffNegIntro`, `demorgan*`) plus
  `iffElimLeft/Right` (context-based, stay) and `demorganConjNeg/DisjNeg` (built from `iffIntro`, stay
  or re-route).

> Frame-class caveat: several Bimodal delegating defs (`efqAxiom`, `peirceAxiom`, `doubleNegation`,
> `lceImp`, `rceImp`) are `{fc : FrameClass}`-polymorphic and wrap the Base result in
> `DerivationTree.lift (FrameClass.base_le fc)`. The generic raw layer produces `.Base` only; the
> `.lift` is a genuinely Bimodal concern and would remain as a thin per-target shim (one line) or be
> pushed to call sites. Do not assume these collapse to zero lines.

### 3c. Modal local combinator reproofs (item 3)
- `Modal/Metalogic/Intuitionistic/CanonicalModel.lean`: `box_mono:206`, `dia_mono:215`,
  `imp_trans0:223`, `boxOr_of_boxDisj:240` — all `private`, all take explicit axiom-witness hypotheses
  (`h_implyK`, `h_implyS`, `h_efq`, `h_orI1/2`, `h_orE`, `h_K`, …) over a variable `Axioms` predicate.
- `Modal/Metalogic/Constructive/CS5.lean`: `box_mono_or_left:471`, `box_mono_or_right:479`.

Only `imp_trans0` is a *pure propositional* combinator (the others are box/diamond-monotonicity, which
are genuinely modal and out of the propositional-combinator family). `imp_trans0` calls
`deductionTheorem` and passes K/S witnesses manually.

### 3d. Embedding-rfl restatements (item 4)
| File | Function | Built on `PL.embed`? | `_atom/_bot/_imp` foldable into `embed_*`? |
|---|---|---|---|
| `Modal/FromPropositional.lean:50-61` | `PL.Proposition.toModal := φ.embed` | **YES** | **Yes** (with caveats §5) |
| `Temporal/FromPropositional.lean:49-60` | `PL.Proposition.toTemporal := φ.embed` | **YES** | **Yes** (with caveats §5) |
| `Bimodal/Embedding/PropositionalEmbedding.lean:59-73` | `PL.Proposition.toBimodal := φ.embed` | **YES** | **Yes** (with caveats §5) |
| `Bimodal/Embedding/ModalEmbedding.lean:45-59` | `Modal.Proposition.toBimodal` (separate recursion, 7 ctors incl. `box`/`diamond`/native `and`/`or`) | **NO** | **No — keep** |
| `Bimodal/Embedding/TemporalEmbedding.lean:50-66` | `Temporal.Formula.toBimodal` (separate recursion incl. `untl`) | **NO** | **No — keep** |

So the genuinely drop-eligible restatements are the **3 `_atom` + 3 `_bot` + 3 `_imp` = 9** across the
three PL→X embeddings (not 34). The `_and/_or/_neg/_box/_untl` stay per the task, and the two X→Bimodal
files stay entirely.

---

## 4. Recommended Approach (for the planner)

**Reuse-first, once-proved-generic. No new bridge typeclass.**

**Phase A — Generic raw-derivation combinator layer (once).** Create a small module (suggested:
`Foundations/Logic/Theorems/DerivationCombinators.lean` or extend `Combinators.lean`) providing, for
`[InferenceSystem S F] [ … MinimalHilbert/ClassicalHilbert as needed]`, combinators typed at `S⇓·`:
```
noncomputable def impTransD {A B C} (d1 : S⇓(A→B)) (d2 : S⇓(B→C)) : S⇓(A→C) :=
  (Theorems.Combinators.imp_trans (d1 : DerivableIn S _) (d2 : DerivableIn S _)).toDerivation
```
and likewise for `identity`, `dni`, `pairing`, `combineImpConj[_3]`, `doubleNegation`, `efqAxiom`,
`lceImp`, `rceImp`, `contraposition`, `classicalMerge`, `demorgan*`. These are the *only* new
declarations. They are thin, use the existing `Coe`s, and are proved once.

**Phase B — Retire the 3 wrap/unwrap pairs** (§3a) and repoint their delegating defs. Two sub-options:
- (B1, lowest churn) Keep the per-target *names* but re-implement each as a one-liner over the Phase-A
  generic (`def impTrans h1 h2 := Combinators.impTransD h1 h2`), deleting `wrap`/`unwrap`. This preserves
  every downstream call site unchanged.
- (B2, maximal deletion) Delete the per-target names too and update downstream call sites to the generic
  names via `open`/scoped alias. Larger surface (see §7 consumer counts) — higher risk.

  **Recommendation: B1** for Temporal/Bimodal delegating defs (preserves ~21 Temporal + ~18 Bimodal
  downstream files untouched), reserving B2 only if the planner wants the full name unification and
  budgets the consumer-update phase.

**Phase C — Embedding-rfl consolidation (PL→X only).** Drop the 9 `_atom/_bot/_imp` restatements for
`toModal`/`toTemporal`/`toBimodal`, having simp reach them via the generic `embed_*`. This requires a
`toX`-unfolding hook (§5). Keep `_and/_or/_neg` and the entire Modal→Bimodal / Temporal→Bimodal files.

**Phase D — Modal (item 3): de-risk or defer.** See §6.

Each phase ends with a scoped `lake build` of the touched module tree.

---

## 5. Critical Caveats for the Embedding Consolidation (Phase C)

1. **`toModal`/`toTemporal`/`toBimodal` are plain `def`s, not reducible.** The generic `embed_atom`
   is `embed`-headed; simp will **not** rewrite a `toModal (atom p)` goal via `embed_atom` unless
   `toModal` unfolds to `embed`. Options: (a) add `@[simp] theorem toModal_eq_embed : φ.toModal = φ.embed := rfl`
   (single lemma replacing three), or (b) make `toModal` an `abbrev`. Option (a) is the minimal,
   lowest-risk change and is itself a net reduction (1 lemma replaces 3).

2. **Normal-form drift (constructor-form vs typeclass-form).** `toModal_imp`'s RHS is
   `Modal.Proposition.imp φ₁.toModal φ₂.toModal` (constructor form); `embed_imp`'s RHS is
   `HasImp.imp a.embed b.embed` (typeclass form). These are defeq but **syntactically different**, so
   downstream simp normal forms shift from constructor-form to typeclass-form. This is the real risk of
   Phase C and must be validated by a full `lake build`, not assumed benign.

3. **Name-reference check is clean.** Grep found **no** by-name references to `toModal_atom/bot/imp`
   or `toTemporal_atom/bot/imp` outside their defining files — they are `@[simp]`-only. `toBimodal_*`
   *is* referenced by the two X→Bimodal files, but those keep their own restatements. So Phase C risk is
   confined to simp-normal-form drift, which `lake build` will catch deterministically.

---

## 6. SCOPE-GUARD Analysis (Modal item 3)

The SCOPE GUARD states tasks 393 (Lindenbaum/MCS) and 41 (completeness infra) own the MCS/deduction-theorem
seams, and to coordinate before touching `GenericMCSBridge` files.

- `Modal.HilbertOf Axioms` + its `MinimalHilbert` instance live in `Modal/Metalogic/GenericMCSBridge.lean`
  (confirmed by the `GenericMCS.lean` docstring, §"Logics using this seam"). This is scope-guarded.
- Modal's `imp_trans0` (`CanonicalModel.lean:223`) works over a *variable* `Axioms` predicate with K/S
  witnesses supplied as hypotheses and calls `deductionTheorem`. To replace it with
  `Combinators.imp_trans` at `HilbertOf Axioms`, one must obtain `MinimalHilbert (HilbertOf Axioms)` at
  the call site.

**Verdict:** *Using* the already-published `MinimalHilbert (HilbertOf Axioms)` instance (import + instance
resolution) does **not** modify the bridge and is within scope. *Any* edit to `GenericMCSBridge.lean`
itself (e.g., to add/adjust the instance or expose a helper) is **out of scope** and requires coordination.
`box_mono`/`dia_mono`/`boxOr_of_boxDisj`/`box_mono_or_*` are genuinely modal (box/diamond monotonicity),
**not** members of the propositional-combinator family, and should be left as-is.

**Recommendation:** Treat item 3 as a *narrow, optional* phase limited to replacing `imp_trans0`'s body
with a call to the generic `impTransD`/`imp_trans` at `HilbertOf Axioms` **iff** the existing instance is
usable without editing the bridge. If instance resolution requires bridge changes, mark this phase
**[BLOCKED — coordinate with tasks 393/41]** rather than touching the guarded file. Do not force it.

---

## 7. Refactor Surface / Consumer Sizing

- **Temporal combinators (`PropositionalHelpers`)**: ~21 files under `Temporal/Metalogic/**` open the
  namespace (Chronicle construction, TruthLemma, DenseCompleteness, PointInsertion/*, etc.). Favors
  Phase-B option **B1** (keep names) to avoid touching all of them.
- **Bimodal Propositional combinators**: ~18 consumer files under `Bimodal/Metalogic/**`
  (Algebraic/*, BXCanonical/*, Bundle/*). Same recommendation.
- **Perpetuity wrap/unwrap**: also consumed by `Bimodal/Metalogic/Core/MCSProperties.lean` — verify this
  consumer does not import `wrap`/`unwrap` by name before deleting them (it likely uses the combinator
  defs, not the primitives).
- **wrap/unwrap primitives themselves**: only used inside the 3 helper files (as the implementation of
  the delegating defs) — safe to delete once the delegating defs are repointed to Phase A.

---

## 8. Tactic / Verification Notes

- No proof search is needed: every replacement is a definitional/`rfl`/`Coe` rewrite or a call to an
  existing generic theorem. `simp`/`aesop` are not load-bearing here.
- The one place `simp` matters is Phase C (embedding), where the risk is normal-form drift; verify with
  scoped `lake build Cslib.Logics.Modal`, `…Temporal`, `…Bimodal` after the embedding edits.
- Recommended phase-end verification: `lake build Cslib.Logics.Temporal`,
  `lake build Cslib.Logics.Bimodal`, `lake build Cslib.Logics.Modal`, then full `lake build`.

## 9. Suggested Phase Decomposition (hand-off to planner)

1. **Phase A** — Add generic raw-`S⇓`-typed combinator layer (once). New file/section only; no deletions.
2. **Phase B-Temporal** — Repoint `PropositionalHelpers` delegating defs to Phase A; delete `wrap`/`unwrap`.
3. **Phase B-Bimodal-Perpetuity** — Repoint `Perpetuity/Helpers` combinator defs; delete `wrap`/`unwrap`;
   keep the 4 tree-structural temporal helpers.
4. **Phase B-Bimodal-Propositional** — Repoint Core+Connectives delegating defs; delete `wrap'`/`unwrap'`;
   keep context/tree-structural defs and the `{fc}`-lift shims.
5. **Phase C** — Embedding consolidation: add `toX_eq_embed` simp unfolders, delete the 9 PL→X
   `_atom/_bot/_imp` restatements; keep `_and/_or/_neg` and the X→Bimodal files.
6. **Phase D (optional/guarded)** — Modal `imp_trans0` re-route, subject to §6 scope check.
7. **Verification** — full `lake build` (+ `lake exe checkInitImports`, `lake lint` on touched files;
   watch `docBlame` on any new generic defs — each needs a docstring).

---

## References (durable anchors)
- `Cslib/Foundations/Logic/InferenceSystem.lean` — `DerivableIn`, `fromDerivation`/`toDerivation`, `Coe`s
- `Cslib/Foundations/Logic/Theorems/Combinators.lean` — once-proved generic combinators
- `Cslib/Foundations/Logic/Theorems/Propositional/{Core,Connectives}.lean` — generic propositional theorems
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — the "prove-once-generic + per-logic iff bridge"
  pattern the task cites as the model; documents the `HilbertOf`/`MinimalHilbert` seam and scope
- `Cslib/Logics/Propositional/Embedding.lean:80-119` — `embed` skeleton + generic `embed_*` simp lemmas
