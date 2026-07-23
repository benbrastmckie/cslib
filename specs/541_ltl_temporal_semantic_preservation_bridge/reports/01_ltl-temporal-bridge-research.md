# Research Report: LTL-to-Temporal Semantic Preservation Bridge

## Summary

The LTL-to-Temporal embedding (`Formula.toTemporal` in `Cslib/Logics/LTL/Embedding.lean`)
is a disconnected island: the file defines the syntactic map but contains **zero theorems**,
and while it is present in the `Cslib.lean` barrel, **no semantic file imports it** and its
docstring asserts semantic preservation (including a reflexive-until vs strict-until
reconciliation) that is never proven.

**Key finding: the docstring claim is CORRECT and the satisfaction-preservation theorem is
fully provable with zero sorry.** The reflexive-until vs strict-until reconciliation is exactly
resolved by the `reflexiveUntl a b = b ∨ (a ∧ (a U b))` definition, and the `next → untl ⊥`
mapping is resolved by the discreteness of ℕ. No correction to the translation is required; the
work is to *prove* what the docstring asserts and wire a consumer (satisfiability transfer).

All required library API already exists (ωSequence reindexing lemmas, Temporal semantic
or/and lemmas). No new axioms, no sorry, no vacuous definitions are needed.

## Reuse-First Check (CSLib philosophy)

Every ingredient the bridge needs already exists in the library:

| Need | Existing declaration | Location |
|------|---------------------|----------|
| `(w.drop n).head = w n` | `ωSequence.head_drop` | `Foundations/Data/OmegaSequence/Init.lean:106` |
| `drop n (drop m s) = drop (m+n) s` | `ωSequence.drop_drop` (`@[simp]`) | `Init.lean:72` |
| `tail (drop i s) = drop (i+1) s` | `ωSequence.tail_drop'` (`@[simp]`) | `Init.lean:79` |
| `(drop m s) n = s (m+n)` | `ωSequence.get_drop` (`@[simp]`) | `Init.lean:64` |
| `s.drop 0 = s` | `ωSequence.drop_zero` (`@[simp]`, rfl) | `Init.lean:101` |
| `Satisfies M t (φ ∨ ψ) ↔ …` | `Temporal.sat_or_iff` | `Temporal/Metalogic/Soundness.lean:54` |
| `Satisfies M t (φ ∧ ψ) ↔ …` | `Temporal.sat_and_iff` | `Temporal/Metalogic/Soundness.lean:43` |
| Target satisfiability predicate | `Temporal.Satisfiable` | `Temporal/Semantics/Validity.lean:112` |

No new abstractions are recommended. The only new declarations are the bridge model, the main
bridge theorem, and the transfer corollary.

## Current State of the Island

- `Cslib/Logics/LTL/Embedding.lean` defines only `Formula.toTemporal` (5-case syntactic map),
  zero theorems. Its imports are the two `Syntax/Formula` files only — it does **not** import
  either satisfaction relation, so it cannot state (let alone prove) a semantic claim.
- Barrel status: `Cslib.lean:333` lists `Cslib.Logics.LTL.Embedding`, so it compiles, but the
  disconnection is at the *theorem/semantic* level, exactly as the task states.
- Grep confirms **no importer** of `Cslib.Logics.LTL.Embedding` and no reference to LTL's
  `toTemporal` outside its own file. (The many `toTemporal` hits elsewhere are a distinct
  `PL.Proposition.toTemporal`, unrelated.)
- Complete, sorry-free downstream LTL results stranded on the ω-word side:
  `Cslib/Logics/LTL/Semantics/GNBA/Correctness.lean` (`gnba_language_eq`, Baier–Katoen 5.39),
  `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` (`Formula.isRegular`),
  `Cslib/Logics/LTL/ModelChecking.lean:98` (`ltlModelChecking`).

## The Two Semantics (ground truth)

LTL (`Cslib/Logics/LTL/Semantics/Satisfies.lean:57`), over `ωSequence State`,
valuation `v : Atom → State → Prop`, evaluated at a word `w`:

```
atom p     : v p w.head
bot        : False
imp φ ψ    : Satisfies v w φ → Satisfies v w ψ
next φ      : Satisfies v w.tail φ
untl φ ψ    : ∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ   -- φ=guard, ψ=event
```

The `untl` witness `j` ranges over **all** ℕ including `j = 0`, so LTL until is **reflexive
(non-strict)**: at `j = 0` the event holds now with no guard obligation.

Temporal (`Cslib/Logics/Temporal/Semantics/Satisfies.lean:66`), over a `LinearOrder D`,
`TemporalModel D Atom` (a valuation `D → Atom → Prop`), evaluated at point `t`:

```
untl ψ φ    : ∃ s, t < s ∧ Satisfies M s φ ∧ ∀ r, t < r → r < s → Satisfies M r ψ   -- ψ=guard, φ=event (STRICT: s > t)
```

Temporal until is **strict** (`t < s`, guard on the open interval `(t, s)`).
`reflexiveUntl φ ψ := ψ ∨ (φ ∧ (φ U ψ))` (`Temporal/Syntax/Formula.lean:296`) recovers the
non-strict version.

Both logics use the **Pnueli convention** `untl guard event`, so no argument swap is needed —
the embedding's `.untl φ₁ φ₂ => (toTemporal φ₁).reflexiveUntl (toTemporal φ₂)` maps
guard→guard, event→event correctly.

## The Bridge Model

The canonical time domain is `D = ℕ` with its standard `LinearOrder`. Given LTL data
`(v, w)`, define the temporal model whose atom-truth at time `n` is the LTL truth at the
`n`-th state of the word:

```lean
def toTemporalModel (v : Atom → State → Prop) (w : ωSequence State) : Temporal.TemporalModel ℕ Atom :=
  ⟨fun n p => v p (w n)⟩
```

Note `w n = (w.drop n).head` by `head_drop`, so atoms line up definitionally after that rewrite.

## Main Theorem (provable, zero sorry)

```lean
theorem satisfies_toTemporal (v : Atom → State → Prop) (w : ωSequence State) (n : ℕ)
    (φ : LTL.Formula Atom) :
    LTL.Satisfies v (w.drop n) φ ↔ Temporal.Satisfies (toTemporalModel v w) n φ.toTemporal
```

Proof strategy: `induction φ generalizing n`. Verified case-by-case:

- **atom p**: LHS `v p (w.drop n).head`; rewrite with `head_drop` to `v p (w n)` =
  `(toTemporalModel v w).valuation n p` = RHS. Closes by `simp [head_drop]` / `Iff.rfl` after
  the rewrite.
- **bot**: both `False`, `Iff.rfl`.
- **imp φ ψ**: both sides are `(·→·)` of the sub-results; discharge by the two IHs at the same
  `n`.
- **next φ** (`toTemporal = .untl .bot (toTemporal φ)`): LHS `= Satisfies v (w.drop n).tail φ
  = Satisfies v (w.drop (n+1)) φ` (via `tail_drop'`), and IH at `n+1` gives
  `Satisfies M (n+1) (toTemporal φ)`. RHS is the Temporal strict-until with guard `⊥`:
  `∃ s, n < s ∧ Satisfies M s (toTemporal φ) ∧ ∀ r, n < r → r < s → False`. The guard `⊥`
  forbids any point strictly between `n` and `s`; combined with `n < s`, **ℕ discreteness
  forces `s = n+1`**. Hence RHS ↔ `Satisfies M (n+1) (toTemporal φ)`, matching LHS.
  Discreteness sub-argument (no library lemma needed, `omega`-backed):
  ```
  -- (→) from ⟨s, hns, hsat, hguard⟩: by_contra s ≠ n+1 ⇒ n+1 < s ⇒ hguard (n+1) (by omega) (by omega) : False
  -- (←) witness s := n+1: n < n+1; the guard range n < r < n+1 is empty by omega.
  ```
- **untl φ₁ φ₂** (`toTemporal = reflexiveUntl (toTemporal φ₁) (toTemporal φ₂)
  = b ∨ (a ∧ (a U b))`, with `a = toTemporal φ₁` guard, `b = toTemporal φ₂` event):
  Reindex LHS with `drop_drop` (`(w.drop n).drop j = w.drop (n+j)`) and the two IHs:
  ```
  LHS ↔ ∃ j, Satisfies M (n+j) b ∧ ∀ k < j, Satisfies M (n+k) a
  ```
  Unfold RHS with `sat_or_iff` then `sat_and_iff` and `untl_iff`:
  ```
  RHS ↔ Satisfies M n b ∨ (Satisfies M n a ∧ ∃ s, n < s ∧ Satisfies M s b ∧ ∀ r, n<r → r<s → Satisfies M r a)
  ```
  Equivalence (the reflexive/strict reconciliation):
  - `j = 0` ⇒ `b` at `n` ⇒ left disjunct.
  - `j ≥ 1` ⇒ `a` at `n` (`k=0`) and event `b` at `s := n+j` with guard `a` on `(n, s)` (each
    such `r = n+k`, `0 < k < j`) ⇒ right disjunct.
  - Conversely the left disjunct gives witness `j = 0`; the right disjunct gives witness
    `j = s - n` with `∀ i ∈ [n, s), a` assembled from `a@n` and the strict guard.
  The `r ↔ n+k` index translation is discharged by `omega` (`k := r - n`).

## Consumer / Transfer Result (gives the module a consumer)

```lean
theorem satisfiable_toTemporal {Atom State : Type*} (φ : LTL.Formula Atom)
    (h : LTL.Satisfiable (State := State) φ) : Temporal.Satisfiable φ.toTemporal
```

Proof: `obtain ⟨v, w, hsat⟩ := h`; provide `D := ℕ`, `LinearOrder ℕ`, `Nontrivial ℕ`,
`M := toTemporalModel v w`, `t := 0`; the goal `Satisfies M 0 φ.toTemporal` follows from the
main theorem at `n = 0` (`drop_zero : w.drop 0 = w`) applied to `hsat`.

- `LTL.Satisfiable` (`LTL/Semantics/Satisfies.lean:70`) is `∃ v w, Satisfies v w φ`, with
  `State` an implicit module variable — hence the explicit `(State := State)` binder above.
- `Temporal.Satisfiable` (`Temporal/Semantics/Validity.lean:112`) quantifies `D : Type` with
  `Nontrivial D`. `ℕ : Type 0` satisfies both (`Nontrivial ℕ`, `LinearOrder ℕ` are instances),
  so the universe/quantifier shape fits with no friction.

This wires a genuine downstream LTL fact (satisfiability, which the GNBA/model-checking
apparatus can establish) across the bridge into Temporal satisfiability, making `toTemporal`
a used definition.

Optional bonus (not required by task): the reverse direction on validity,
`Temporal.Valid φ.toTemporal → LTL.Valid φ` (Temporal `Valid` quantifies over *all* nontrivial
linear orders ⊇ ℕ-models), also follows from the main theorem; note it is one-directional
(Temporal validity is strictly stronger since it ranges over dense orders too), so
satisfiability is the cleaner headline consumer.

## Recommended File Placement & Imports

Create a new flat sibling file (mirrors how `Temporal/ConservativeExtension.lean` and
`Temporal/FromPropositional.lean` sit as flat semantic-bridge files):

- Path: `Cslib/Logics/LTL/EmbeddingSemantics.lean`
  (alternative acceptable name: `Cslib/Logics/LTL/Semantics/TemporalBridge.lean`)
- Must begin with `import Cslib.Init` requirement satisfied transitively; use `module` + the
  `public import` style of neighboring files.
- Imports:
  - `Cslib.Logics.LTL.Embedding` (the `toTemporal` map — this file becomes its consumer)
  - `Cslib.Logics.LTL.Semantics.Satisfies`
  - `Cslib.Logics.Temporal.Semantics.Satisfies`
  - `Cslib.Logics.Temporal.Semantics.Validity` (for `Temporal.Satisfiable`)
- **Import-weight decision for `sat_or_iff` / `sat_and_iff`**: these live in
  `Temporal/Metalogic/Soundness.lean`, which transitively drags in the whole ProofSystem.
  To keep a *semantics-only* bridge, prefer proving two tiny local classical helpers
  (`Satisfies M t (φ ∨ ψ) ↔ …`, `… (φ ∧ ψ) ↔ …`, ~6 lines each, copy the exact proofs from
  `Soundness.lean:43,54`). Reuse-by-import is the alternative if pulling Metalogic into the
  bridge is deemed acceptable. Recommendation: **local helpers** (lighter, no proof-system
  dependency, still zero-debt). Both are compliant.
- After adding the file, run `lake exe mk_all --module` to update the `Cslib.lean` barrel, and
  `lake exe checkInitImports`.

## Namespace / Lint Notes (CSLib standards)

- Namespace: `Cslib.Logic.LTL` (note: singular `Logic`, matching both `Embedding.lean:37` and
  `Temporal` files — the directory is `Logics/` but the namespace root is `Cslib.Logic`).
- All new declarations need docstrings (docBlame). Prop-valued results must be
  `theorem`/`lemma`, not `def` (defLemma). Names must be lowerCamelCase, no underscores in the
  identifier tail beyond the established `satisfies_toTemporal`-style — follow neighboring
  naming (`temporal_satisfies_toTemporal_iff_evaluate` shows underscores are tolerated in this
  corner of the tree, but prefer the local convention; confirm with `lake lint`).
- `toTemporalModel` is a `def` returning data (a `TemporalModel`) — correct to use `def`.
- Keep section variables minimal; the model/theorems only need `{Atom State : Type*}`. Use
  `omit` if any unused-section-variable lint fires.

## Tactic Survey (advisory)

- atom/bot/imp cases: `simp [Satisfies, LTL.Satisfies, toTemporal, head_drop]` + IH `rw`.
- next case: manual `constructor`; `omega` for the discreteness forcing `s = n+1`.
- untl case: `rw [sat_or_iff, sat_and_iff, untl_iff]` (or local helpers); `simp only [drop_drop]`
  for reindexing; `omega` for the `r = n + k` index bijection; `Nat.add`/`Nat.sub` arithmetic
  all within `omega` reach.
- `drop_drop`, `tail_drop'`, `get_drop`, `head_drop`, `drop_zero` are `@[simp]`, so a plain
  `simp` frequently discharges the sequence-reindexing boilerplate.

## Zero-Debt Assessment

No sorry, no new axiom, no vacuous definition is required. Every case of the main theorem has a
concrete, verified discharge path grounded in existing library API. The docstring's semantic
claim is sound as written — the task's "if unprovable, correct the translation" contingency is
**not triggered**; the correct outcome is to prove the existing claim, not amend it.

## Suggested Phase Decomposition (for planning)

1. Add `toTemporalModel` def + (if chosen) the two local `or`/`and` semantic helpers.
2. Prove `satisfies_toTemporal` (main bridge), one case at a time (atom/bot/imp/next/untl).
3. Prove `satisfiable_toTemporal` transfer corollary (consumes main theorem at `n=0`).
4. Barrel update (`mk_all --module`), `checkInitImports`, `lake build`, `lake lint`,
   `lake exe lint-style`.

## References

- Pnueli 1977, *The Temporal Logic of Programs* (until convention).
- Burgess 1984, *Basic Tense Logic* (strict tense operators) — cited in `Embedding.lean`.
- Baier & Katoen, *Principles of Model Checking*, Thm 5.39 (`gnba_language_eq`, downstream).
