# LJ `impL` Maehara Interpolant — Single-Conclusion Intuitionistic Sequent Calculus

**Task**: 374 — Sequent calculus interpolation
**Scope**: Derive the mathematically correct Maehara interpolant for the implication-left
(`⊃L` / `LJProof.impL`) rule. Text-only proof-theory derivation; no Lean editing, no builds.
**Date**: 2026-06-28

## Setting (grounded in cslib source)

`Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean` (all-additive Negri–von Plato
presentation, single-conclusion). Relevant constructors (verified):

- `impL A B (h : (A → B) ∈ Γ) (d₁ : Γ ⊢ A) (d₂ : insert B Γ ⊢ C) : Γ ⊢ C`
- `impR A B (d : insert A Γ ⊢ B) : Γ ⊢ A → B`
- `andR A B (d₁ : Γ ⊢ A) (d₂ : Γ ⊢ B) : Γ ⊢ A ∧ B`
- `andL A B (h : (A ∧ B) ∈ Γ) (d : insert A (insert B Γ) ⊢ C) : Γ ⊢ C`
- `mono (hL : Γ ⊆ Γ') : Γ ⊢ C → Γ' ⊢ C`  (left weakening / antecedent monotonicity)

Interpolation statement (`ljMaeharaCore`, verified in `Interpolation.lean:65-71`): for
`Γ ⊢ C` and any cover `Γ = Γ₁ ∪ Γ₂`, there is `I` with
1. `I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars`,
2. `Nonempty (Γ₁ ⊢ I)`,
3. `Nonempty (insert I Γ₂ ⊢ C)`.

For the `impL` node, the conclusion is `Γ ⊢ C` with `A→B ∈ Γ`, premises `d₁ : Γ ⊢ A` and
`d₂ : insert B Γ ⊢ C`. The hypothesis `A→B ∈ Γ = Γ₁ ∪ Γ₂` splits via `Finset.mem_union`
into exactly the two cases below.

**Induction hypotheses available** (each quantified over *all* partitions):
- `ih₁` on `d₁` (conclusion `A`, context `Γ`): for `Γ = Δ₁ ∪ Δ₂`, gives `J` with
  `Δ₁ ⊢ J`, `insert J Δ₂ ⊢ A`, `J.vars ⊆ Δ₁.vars ∩ (Δ₂ ∪ {A}).vars`.
- `ih₂` on `d₂` (conclusion `C`, context `insert B Γ`): for `insert B Γ = Δ₁ ∪ Δ₂`, gives
  `K` with `Δ₁ ⊢ K`, `insert K Δ₂ ⊢ C`, `K.vars ⊆ Δ₁.vars ∩ (Δ₂ ∪ {C}).vars`.

Key vars facts used throughout: from `A→B ∈ Γ_k`, `vars(A) ∪ vars(B) ⊆ vars(Γ_k)` (because
`vars(A→B) = vars(A) ∪ vars(B)` and `A→B ∈ Γ_k`). This is what absorbs the "extra" `A`/`B`
variables that the sub-interpolant bounds introduce.

---

## Case 1: `A→B ∈ Γ₂` (principal implication on the succedent / `Γ₂` side)

**Interpolant**: `I = J ∧ K`.

**IH calls** (note the partitions are *cover equalities* the implementer must discharge):
- `ih₁` with `Δ₁ = Γ₁`, `Δ₂ = Γ₂`   (cover: `Γ = Γ₁ ∪ Γ₂`, i.e. `hant`).
  Yields `J`: `Γ₁ ⊢ J`,  `insert J Γ₂ ⊢ A`,  `J.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {A}).vars`.
- `ih₂` with `Δ₁ = Γ₁`, `Δ₂ = insert B Γ₂`   (cover: `insert B Γ = Γ₁ ∪ insert B Γ₂`).
  Yields `K`: `Γ₁ ⊢ K`,  `insert K (insert B Γ₂) ⊢ C`,
  `K.vars ⊆ Γ₁.vars ∩ (insert B Γ₂ ∪ {C}).vars`.

### (a) `Γ₁ ⊢ I`  i.e. `Γ₁ ⊢ J ∧ K`
`andR J K` applied to `Γ₁ ⊢ J` (from `ih₁`) and `Γ₁ ⊢ K` (from `ih₂`). One rule: **andR**.

### (b) `insert I Γ₂ ⊢ C`  i.e. `insert (J ∧ K) Γ₂ ⊢ C`
Let `Σ = insert J (insert K (insert (J ∧ K) Γ₂))`. Note `A→B ∈ Γ₂ ⊆ Σ`.

1. **andL** with principal `J ∧ K ∈ insert (J∧K) Γ₂`: reduces the goal
   `insert (J∧K) Γ₂ ⊢ C` to `Σ ⊢ C`.
2. **impL** with principal `A→B ∈ Σ`. Two premises:
   - `Σ ⊢ A`: from `insert J Γ₂ ⊢ A` (`ih₁`) by **mono** (`insert J Γ₂ ⊆ Σ`).
   - `insert B Σ ⊢ C`: from `insert K (insert B Γ₂) ⊢ C` (`ih₂`) by **mono**
     (`insert K (insert B Γ₂) ⊆ insert B Σ`, since `K ∈ Σ`, `Γ₂ ⊆ Σ`, and `B` is inserted).
   impL yields `Σ ⊢ C`, discharging step 1.

   *Where `A→B ∈ Γ₂` is used*: as the principal-formula membership of this **impL**. The
   succedent side `Γ₂` carries the implication, so the *right* sequent does the elimination.

### (c) vars bound: `I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars`
`I.vars = J.vars ∪ K.vars`.
- `J.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {A}).vars`. Since `vars(A) ⊆ Γ₂.vars` (from `A→B ∈ Γ₂`),
  `(Γ₂ ∪ {A}).vars = Γ₂.vars ⊆ (Γ₂ ∪ {C}).vars`. So `J.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars`.
- `K.vars ⊆ Γ₁.vars ∩ (insert B Γ₂ ∪ {C}).vars`. Since `vars(B) ⊆ Γ₂.vars`,
  `(insert B Γ₂ ∪ {C}).vars = (Γ₂ ∪ {C}).vars`. So `K.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars`.

Union of the two ⊆ `Γ₁.vars ∩ (Γ₂ ∪ {C}).vars`. ✓

---

## Case 2: `A→B ∈ Γ₁` (principal implication on the interpolant-proving / `Γ₁` side)

This is the obstructed case. The naive `I₁ ∨ I₂` (correct for two-sided LK) **fails**:
in `insert I Γ₂ ⊢ C` the formula `A→B` is on the `Γ₁` side, so the right sequent cannot
apply `impL`. The fix is to **carry the implication into the interpolant**.

**Interpolant**: `I = J → K`  (an *implication* interpolant — this is essential, see below).

**IH calls** (note `ih₁` uses the *swapped* partition compared with Case 1):
- `ih₁` with `Δ₁ = Γ₂`, `Δ₂ = Γ₁`   (cover: `Γ = Γ₂ ∪ Γ₁`; the same set, commuted).
  Yields `J`: `Γ₂ ⊢ J`,  `insert J Γ₁ ⊢ A`,  `J.vars ⊆ Γ₂.vars ∩ (Γ₁ ∪ {A}).vars`.
- `ih₂` with `Δ₁ = insert B Γ₁`, `Δ₂ = Γ₂`   (cover: `insert B Γ = insert B Γ₁ ∪ Γ₂`).
  Yields `K`: `insert B Γ₁ ⊢ K`,  `insert K Γ₂ ⊢ C`,
  `K.vars ⊆ (insert B Γ₁).vars ∩ (Γ₂ ∪ {C}).vars`.

### (a) `Γ₁ ⊢ I`  i.e. `Γ₁ ⊢ J → K`
1. **impR** (principal `J → K`): reduces goal to `insert J Γ₁ ⊢ K`.
2. **impL** with principal `A→B ∈ insert J Γ₁` (membership from `A→B ∈ Γ₁`). Two premises:
   - `insert J Γ₁ ⊢ A`: directly from `ih₁`.
   - `insert B (insert J Γ₁) ⊢ K`: from `insert B Γ₁ ⊢ K` (`ih₂`) by **mono**
     (`insert B Γ₁ ⊆ insert B (insert J Γ₁)`).
   impL yields `insert J Γ₁ ⊢ K`, discharging step 1.

   *Where `A→B ∈ Γ₁` is used*: principal of this **impL**. `Γ₁` holds the implication and
   performs the elimination *while proving the interpolant* — producing `K` from `A` (the `J`
   side) plus the consequent `B`.

### (b) `insert I Γ₂ ⊢ C`  i.e. `insert (J → K) Γ₂ ⊢ C`
`A→B` is **not** available here. Instead `J → K` itself is the principal formula.
1. **impL** with principal `J → K ∈ insert (J→K) Γ₂`. Two premises:
   - `insert (J→K) Γ₂ ⊢ J`: from `Γ₂ ⊢ J` (`ih₁`) by **mono** (`Γ₂ ⊆ insert (J→K) Γ₂`).
   - `insert K (insert (J→K) Γ₂) ⊢ C`: from `insert K Γ₂ ⊢ C` (`ih₂`) by **mono**.
   impL yields `insert (J→K) Γ₂ ⊢ C`. ✓

   The interpolant's implication shape is exactly what lets `Γ₂` — which can prove `J` but
   cannot eliminate `A→B` — discharge `J` and consume `K` to reach `C`.

### (c) vars bound: `I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars`
`I.vars = J.vars ∪ K.vars`.
- `J.vars ⊆ Γ₂.vars ∩ (Γ₁ ∪ {A}).vars`. Since `vars(A) ⊆ Γ₁.vars` (from `A→B ∈ Γ₁`),
  `(Γ₁ ∪ {A}).vars = Γ₁.vars`. So `J.vars ⊆ Γ₂.vars ∩ Γ₁.vars = Γ₁.vars ∩ Γ₂.vars
  ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars`.
- `K.vars ⊆ (insert B Γ₁).vars ∩ (Γ₂ ∪ {C}).vars`. Since `vars(B) ⊆ Γ₁.vars`,
  `(insert B Γ₁).vars = Γ₁.vars`. So `K.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {C}).vars`.

Union ⊆ `Γ₁.vars ∩ (Γ₂ ∪ {C}).vars`. ✓

**Why `I` must be an implication (not `∨`/`∧`)**: obligation (b) must hold with `A→B`
absent from its context. The only formula in `insert I Γ₂` that can trigger the elimination
linking "Γ₂ proves something (`J`)" to "that yields `C` (via `K`)" is `I` itself; an
elimination on `I` requires `I` to be an implication `J → K`. Disjunction/conjunction
interpolants give no rule that consumes the `Γ₂`-provable `J` to deliver `K`. Symmetrically,
obligation (a) needs `Γ₁`'s `A→B` to manufacture `K` from the antecedent `J` — packaged by
`impR` as `J → K`. The two obligations are the two halves of a single implication.

---

## Summary table

| Case | `I` | `ih₁` partition `(Δ₁,Δ₂)` → gives `J` | `ih₂` partition `(Δ₁,Δ₂)` → gives `K` | `Γ₁ ⊢ I` via | `insert I Γ₂ ⊢ C` via |
|------|-----|----------------------------------------|----------------------------------------|--------------|------------------------|
| `A→B ∈ Γ₂` | `J ∧ K` | `(Γ₁, Γ₂)` | `(Γ₁, insert B Γ₂)` | `andR` | `andL` then `impL` (principal `A→B ∈ Γ₂`), premises by `mono` |
| `A→B ∈ Γ₁` | `J → K` | `(Γ₂, Γ₁)` | `(insert B Γ₁, Γ₂)` | `impR` then `impL` (principal `A→B ∈ Γ₁`), 2nd premise by `mono` | `impL` (principal `J→K`), both premises by `mono` |

## Cover-equality side goals the implementer must discharge

- Case 1 `ih₂`: `insert B Γ = Γ₁ ∪ insert B Γ₂` (from `Γ = Γ₁ ∪ Γ₂`, push `insert B` right).
- Case 2 `ih₁`: `Γ = Γ₂ ∪ Γ₁` (commute the given cover; `Finset.union_comm`).
- Case 2 `ih₂`: `insert B Γ = insert B Γ₁ ∪ Γ₂` (push `insert B` left).

All follow from `hant : Γ = Γ₁ ∪ Γ₂` with `Finset.insert_union` / `Finset.union_comm`.

## Rules used (cslib constructor names)

`andR`, `andL`, `impR`, `impL`, `mono`. No `cut` (construction is cut-free, preserving
`LJCutFree`). No `ax`/`orL`/`orR*`/`botL`/`weakL` needed for this node beyond what `mono`
provides. `mono` is the only weakening device required; each use is a concrete `Finset ⊆`
fact (subset of inserts/unions).

## References

- S. Negri, J. von Plato, *Structural Proof Theory*, CUP 2001, Ch. 3 (the all-additive
  G3i presentation this cslib calculus follows; interpolation via Maehara partitions).
- A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*, 2nd ed., CUP 2000, Ch. 4 and the
  Craig–Maehara interpolation development: the `⊃L` interpolant is the conjunction of premise
  interpolants when the principal implication lies in the succedent-bearing group, and the
  *implication* `J → K` of premise interpolants when it lies in the opposite group.
- G. Takeuti, *Proof Theory*, 2nd ed., §6–7 (Maehara's lemma; the L⊃ case dichotomy on which
  partition contains the principal formula).

The Case 2 "implication interpolant" is the standard resolution of the obstruction the team
lead identified: it is precisely the construction that handles `→`-left when the implication
sits on the interpolant-proving side in single-conclusion (intuitionistic) Maehara.
