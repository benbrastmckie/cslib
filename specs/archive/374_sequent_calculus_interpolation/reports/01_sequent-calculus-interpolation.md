# Research Report: Craig Interpolation for LK / LJ via Maehara's Method (Task 374)

**Task type:** cslib (Lean 4, propositional sequent calculus)
**Status:** researched
**Worktree:** `.claude/worktrees/orchestrate-376-371-363-374-369-317-375`
**Dependency:** task 371 (LJ subformula property) — COMPLETE, foundations in place.

---

## 1. Goal Restatement

Add Craig interpolation for the propositional sequent calculi LK (classical) and LJ
(intuitionistic) via **Maehara's method**:

- **LK (split/Maehara form):** for a cut-free proof of `Γ ⊢ₛ Δ` and any cover
  `Γ = Γ₁ ∪ Γ₂`, `Δ = Δ₁ ∪ Δ₂`, construct an interpolant `I` with
  - `Γ₁ ⊢ₛ {I} ∪ Δ₁` derivable,
  - `{I} ∪ Γ₂ ⊢ₛ Δ₂` derivable,
  - `vars I ⊆ vars(Γ₁ ∪ Δ₁) ∩ vars(Γ₂ ∪ Δ₂)` (shared-vocabulary constraint).
- **Craig corollary (implication form):** if `⊢ A → B` then there is `I` with
  `⊢ A → I`, `⊢ I → B`, `vars I ⊆ vars A ∩ vars B`. Obtained by taking the partition
  `Γ₁ = {A}`, `Δ₂ = {B}`, `Γ₂ = Δ₁ = ∅` of the sequent `A ⊢ₛ B`.
- **LJ analogue (single-conclusion):** for `Γ₁ ∪ Γ₂ ⊢ C`, construct `I` with `Γ₁ ⊢ I`
  and `{I} ∪ Γ₂ ⊢ C`, `vars I ⊆ vars Γ₁ ∩ vars(Γ₂ ∪ {C})`.

Constraints: **no new axioms; no `sorry`**; CI green (`lake build`, `lake test`,
`lake exe checkInitImports`, `lake exe lint-style`, `lake shake`).

---

## 2. Existing Datatypes the Induction Recurses On (cite file:line)

### 2.1 Sequents

- **LK sequent** — `Cslib/Logics/Propositional/SequentCalculus/Defs.lean:50-54`:
  ```lean
  structure LKSequent (Atom) [DecidableEq Atom] where
    ant : Finset (Proposition Atom)   -- Γ
    suc : Finset (Proposition Atom)   -- Δ
  ```
  Notation `Γ ⊢ₛ Δ` (`Defs.lean:57`). Two-sided, multi-conclusion, **Finset-based**.

- **LJ sequent** reuses the ND `Sequent` — `NaturalDeduction/Basic.lean:101,108,111`:
  ```lean
  abbrev Ctx (Atom) := Finset (Proposition Atom)
  abbrev Sequent {Atom} := Ctx Atom × Proposition Atom    -- (Γ, C)
  scoped notation Γ " ⊢ " A => (⟨Γ, A⟩ : Sequent)
  ```
  Single-conclusion: succedent is one `Proposition Atom`, not a Finset.

### 2.2 Proof terms (what `induction d` recurses on)

- **`LKProof : LKSequent Atom → Type u`** — `LK/Basic.lean:70-123`. 11 constructors:
  `ax, botL, andL, andR, orL, orR, impL, impR, weakL, weakR, cut`.
  All-additive: every rule carries explicit context Finsets; principal-formula
  membership is a hypothesis (`A ∈ Γ` / `∈ Δ`), and premises use `insert`
  (e.g. `andL`: premise `insert A (insert B Γ) ⊢ₛ Δ`).
- **`LJProof : @Sequent Atom → Type u`** — `LJ/Basic.lean:86-135`. 11 constructors:
  `ax, botL, andL, andR, orL, orR1, orR2, impL, impR, weakL, cut`.
  Note: **no `weakR`** (single conclusion), and right-disjunction is split into
  `orR1`/`orR2`.
- **Cut-free predicates:** `CutFree : LKProof seq → Prop` (`LK/Basic.lean:180-191`),
  `LJCutFree : LJProof seq → Prop` (`LJ/Basic.lean:193-204`); both define `cut ↦ False`.
  Cut-free subtypes: `CutFreeLKProof` (`LK/Basic.lean:194`), `CutFreeLJProof`
  (`LJ/Basic.lean:207`).

### 2.3 Structural-rule landscape — a major simplification

Because contexts are **Finsets**, the textbook Maehara cases for **contraction** and
**exchange do not exist as constructors** (Finset idempotence + unorderedness absorb
them). `¬A`, `⊤` are `abbrev`s for `imp` (`Defs.lean:95-98`), so there are **no
separate ¬/⊤ rules**; `⊥`-left is the single `botL` leaf. Hence the interpolation
induction has exactly **one case per cut-free constructor** — 10 for LK (ax, botL,
andL, andR, orL, orR, impL, impR, weakL, weakR), 10 for LJ (ax, botL, andL, andR,
orL, orR1, orR2, impL, impR, weakL). The `cut` case is **vacuous** (closed by
`absurd hcf id`, exactly as in the subformula-property proof).

### 2.4 Foundations from task 371 to build on

- `LKProof.cutElim` — `LK/CutElimination.lean:839` — `(d : LKProof seq) : Nonempty (CutFreeLKProof seq)`.
- `LJProof.cutElim` — `LJ/CutElimination.lean:23` — every LJ sequent has a cut-free proof.
- `LKProof.mono` (`LK/Basic.lean:143`), `LJProof.mono` (`LJ/Basic.lean:158`):
  weakening/monotonicity on contexts — **essential** for assembling interpolant
  sequents (e.g. lifting `Γ₁ ⊢ₛ {I} ∪ Δ₁` to a larger context).
- `LKProof.formulas`/`LJProof.formulas` and the subformula property proofs
  (`LK/SubformulaProperty.lean`, `LJ/SubformulaProperty.lean`). **The
  `cutFreeSubformulaProp` proof (`LK/SubformulaProperty.lean:90-243`) is the exact
  structural template** for the Maehara induction: it takes `(d : LKProof seq)` and
  `(hcf : CutFree d)` as *separate* arguments and runs `induction d with`, which
  side-steps the "Finset-quotient index" problem that blocks `induction` on a
  `CutFreeLKProof` subtype directly. Maehara should follow this pattern precisely.

---

## 3. Key Design Question: Representing the Partition + Shared Vocabulary

This is the crux flagged by the task. Two interlocking sub-problems.

### 3.1 Partitioned sequents

The proof index `Γ ⊢ₛ Δ` is fixed, but the interpolant depends on a *partition* of
it. Since `LKProof` is indexed by the whole sequent and we cannot add the partition
to the index without changing the datatype, **thread the partition through the
induction as extra ∀-quantified data plus cover equations** — the standard
"generalize the goal" technique. Recommended core statement (LK):

```lean
private lemma maeharaCore {seq : LKSequent Atom} (d : LKProof seq) (hcf : CutFree d) :
    ∀ Γ₁ Γ₂ Δ₁ Δ₂ : Finset (Proposition Atom),
      seq.ant = Γ₁ ∪ Γ₂ → seq.suc = Δ₁ ∪ Δ₂ →
      ∃ I : Proposition Atom,
        I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars ∧
        Nonempty (LKProof (Γ₁ ⊢ₛ insert I Δ₁)) ∧
        Nonempty (LKProof (insert I Γ₂ ⊢ₛ Δ₂))
```

**Design decisions (recommended):**

1. **Use a *cover* (`Γ = Γ₁ ∪ Γ₂`), not a `Disjoint` partition.** Maehara is sound
   for any cover. Allowing overlap means each rule case only needs
   `Finset.mem_union : x ∈ Γ₁ ∪ Γ₂ ↔ x ∈ Γ₁ ∨ x ∈ Γ₂` to decide which side the
   principal formula sits on — no disjointness side-conditions to discharge, and no
   `Finset.sdiff` bookkeeping. This is the single most important simplification.
2. **Take `d` and `hcf` separately and `induction d with`** (the
   `cutFreeSubformulaProp` pattern). Do **not** try to `induction` on a
   `CutFreeLKProof` subtype.
3. **Use `Nonempty (LKProof …)` (Prop), not `LKProof …` (Type), for the two
   conclusion-derivations.** The vocabulary statement is `∃`/Prop already; keeping the
   whole invariant in `Prop` avoids universe/definitional-equality friction when
   reassembling `insert`-laden sequents, and lets the `cut` case close by `absurd`.

**Per-case mechanics of the partition refinement.** In each rule case, the principal
formula `P` is in `Γ` (or `Δ`); from the cover equation, `mem_union` gives
`P ∈ Γ₁ ∨ P ∈ Γ₂`. Case-split, then apply the IH to the *premise* sequent with a
**refined cover** that moves the principal/auxiliary formulas to the chosen side, e.g.
for `andL` (premise antecedent `insert A (insert B Γ)`) with `A∧B ∈ Γ₁`, instantiate
the IH cover as `insert A (insert B Γ₁)` / `Γ₂`. The reconstruction obligation
`insert A (insert B Γ₁) ∪ Γ₂ = insert A (insert B (Γ₁∪Γ₂))` is discharged by
`Finset.insert_union` (confirmed present, see §4). The interpolant produced by the IH
is then either returned as-is or combined (∧/∨/→ with the principal subformulas)
depending on which side the principal formula landed — this is the Maehara case table
(§5).

### 3.2 Shared vocabulary (`vars`)

The existing `Proposition.atoms` (`Metalogic/ClassicalImpCompleteness.lean:103`) is
**not reusable**: it returns `List Atom` and only covers `atom`/`imp` (it sends
`and`/`or` to `[]`). Interpolation needs a total, Finset-valued occurrence function.

**Recommendation — define a fresh `Proposition.vars`:**
```lean
def Proposition.vars : Proposition Atom → Finset Atom
  | .atom x => {x}
  | .bot    => ∅
  | .imp a b => a.vars ∪ b.vars
  | .and a b => a.vars ∪ b.vars
  | .or a b  => a.vars ∪ b.vars
```
plus the Finset-of-formulas lift `S.vars := S.biUnion Proposition.vars` (via
`Finset.biUnion`, confirmed present). Required supporting lemmas (all mechanical):
`vars` distributes over the connectives; `(S ∪ T).vars = S.vars ∪ T.vars`;
`(insert A S).vars = A.vars ∪ S.vars`; and the subset-inter manipulation
(`Finset.subset_inter_iff`, `Finset.mem_inter`). The vocabulary bound **must be carried
inside the same induction** as the provability part (the interpolant is built
compositionally; its `vars` is bounded by combinations of sub-interpolant `vars` plus
principal-subformula `vars`), so it cannot be factored into a separate after-the-fact
lemma. This roughly **doubles** the per-case proof burden versus a provability-only
version.

> Place `Proposition.vars` in `Subformula.lean` or a new
> `SequentCalculus/Vocabulary.lean` so both LK and LJ developments share it.

---

## 4. Mathlib / CSLib Reuse (verified)

| Need | Lemma / def | Status |
|------|-------------|--------|
| Lift `vars` over a Finset of formulas | `Finset.biUnion` (`Mathlib.Data.Finset.Union`) | **confirmed** via loogle |
| Refine partition under `insert` | `Finset.insert_union : insert a s ∪ t = insert a (s ∪ t)` (`Mathlib.Data.Finset.Lattice.Lemmas`) | **confirmed** via loogle |
| Decide principal-formula side | `Finset.mem_union` | standard |
| Vocabulary-intersection bound | `Finset.subset_inter_iff`, `Finset.mem_inter`, `Finset.inter_subset_left/right` | standard |
| Symmetric `insert`/union shuffles | `Finset.union_insert`, `Finset.insert_comm`, `Finset.insert_subset_insert` | standard (already used in `LK/Basic.lean`) |
| Assemble conclusion derivations | `LKProof.mono` / `LJProof.mono` (in-repo) | **in repo** |
| Get cut-free proof for corollaries | `LKProof.cutElim` / `LJProof.cutElim` (in repo) | **in repo** |
| Subformula bookkeeping for `vars ⊆ subformula vars` | `Proposition.IsSubformula`, `.trans`, `.and_left`… (`Subformula.lean`) | **in repo** |

**Reuse-first verdict:** No Craig interpolation exists anywhere in CSLib
(`lean_local_search "interpolation"` → empty) and Mathlib has none for this calculus,
so the theorems are genuinely new. All *infrastructure* (Finset ops, `mono`,
`cutElim`, subformula API) is already present; the only new low-level definition needed
is `Proposition.vars` (+ its mechanical lemmas).

---

## 5. Phase-by-Phase Induction Skeleton (Maehara case table)

Below, "return `I`" means the interpolant for the conclusion; sub-interpolants from
premises are `I₁`, `I₂`. Difficulty: **(M)** mechanical, **(H)** hard.

### LK cases (induction on `LKProof`, `cut` vacuous)

| Constructor | Interpolant construction (sketch) | Diff |
|-------------|-----------------------------------|------|
| `ax A` (`A ∈ Γ`, `A ∈ Δ`) | Depends on side of the two `A` occurrences. Four sub-cases by `(A∈Γ₁?,A∈Δ₁? …)`. Interpolant is one of `⊥`, `⊤`(=`⊥→⊥`), `A`, or `¬A` to bridge the two halves. Classic Maehara leaf table. | H (leaf is fiddly) |
| `botL` (`⊥ ∈ Γ`) | If `⊥∈Γ₁`: `I=⊥`; left half `Γ₁⊢⊥,Δ₁` by `botL`, right `⊥,Γ₂⊢Δ₂` by `botL`. If `⊥∈Γ₂`: `I=⊤`. | M |
| `weakL A` | Principal `A` added to `Γ`. Side-split: weaken the appropriate half-derivation via `mono`; `vars` bound only shrinks. | M |
| `weakR A` | Dual of `weakL` on succedent. | M |
| `andL A B` | IH with `A,B` placed on side of `A∧B`; reuse `I`; reassemble premise via `insert_union`; `andL` re-applied on chosen half. `vars` unchanged (A,B subformulas of A∧B). | M |
| `orR A B` | IH on premise `…⊢ insert A (insert B Δ)`; reuse `I`; `orR` re-applied on chosen half. | M |
| `impR A B` | IH on premise `insert A Γ ⊢ insert B Δ`; A on left side, B on right side of the same half; reuse `I`. | M/H |
| `andR A B` | **Two premises.** Get `I₁` (for `…⊢A,Δ`) and `I₂` (for `…⊢B,Δ`). If `A∧B∈Δ₁`: `I = I₁ ∨ I₂`; if `∈Δ₂`: `I = I₁ ∧ I₂`. Must reassemble both half-derivations and prove `vars(I₁∘I₂)=vars I₁ ∪ vars I₂ ⊆ …`. | **H** |
| `orL A B` | **Two premises** (`insert A Γ`, `insert B Γ`). Dual of `andR`: `A∨B∈Γ₁ → I=I₁∨I₂`; `∈Γ₂ → I=I₁∧I₂`. | **H** |
| `impL A B` | **Two premises** (`Γ⊢A,Δ` and `insert B Γ⊢Δ`), and `A` moves to succedent while `B` to antecedent. Most intricate combination (`I₁∧I₂` / `I₁∨I₂` depending on side of `A→B`). | **H** |
| `cut` | Vacuous: `exact absurd hcf id`. | trivial |

**Hard cases = the four with two premises / side-crossing: `ax` (leaf table),
`andR`, `orL`, `impL`** (and `impR` to a lesser degree). The seven one-premise/leaf
cases are mechanical extensions of the partition-refinement pattern.

### LJ cases (induction on `LJProof`; single conclusion `C` is **not** split)

Antecedent only is partitioned (`Γ = Γ₁ ∪ Γ₂`); the lone conclusion `C` always belongs
to the "right" component conceptually. Interpolant sequents are single-conclusion:
`Γ₁ ⊢ I` and `insert I Γ₂ ⊢ C`. Cases mirror LK but:
- `orR1`/`orR2`, `andR`, `impR` act on the (unsplit) succedent → one-premise cases,
  interpolant passed through; **mechanical**.
- `andL`, `orL`, `impL`, `ax`, `botL`, `weakL` mirror LK but with the single-conclusion
  shapes; `impL`/`orL` remain the **hard** two-premise cases.
- Intuitionistic constraint: because the right interpolant sequent `insert I Γ₂ ⊢ C`
  must remain single-conclusion, the leaf/`ax` interpolant table is *simpler* than LK
  (no `¬A` succedent-crossing tricks), but `impR`'s interpolant must stay intuitionistically
  valid — watch the `ax` and `impL` cases.

---

## 6. LJ: Reuse vs. Separate Development

**Recommendation: separate development.** The LK Maehara core proves split provability
for **two-sided** sequents (`Γ₁ ⊢ₛ {I}∪Δ₁`), whereas LJ requires **single-conclusion**
sequents (`Γ₁ ⊢ I`, `insert I Γ₂ ⊢ C`). These have different `LKProof`/`LJProof` index
shapes, so the LK construction cannot be instantiated for LJ. What *is* shared:
- `Proposition.vars` and all its lemmas (define once, in shared file).
- The proof *architecture* (separate-`d`-and-`hcf` helper, cover-equation threading,
  `mem_union` side-split, `insert_union` reassembly).
- Subformula API.

So LJ is a parallel ~0.7× re-implementation of the LK induction, not a corollary.
(There is a classical embedding LJ→LK, but using it to *transport* interpolation back to
LJ would require re-deriving intuitionistic provability of the interpolant sequents from
classical ones — strictly harder than re-running the induction. Avoid.)

---

## 7. Corollaries

- **Craig (implication), LK:** From `maeharaCore` on a cut-free proof of `(∅ ⊢ₛ {A→B})`
  reduced via `impR`-inversion to `({A} ⊢ₛ {B})`, partition `Γ₁={A}, Δ₂={B}, Γ₂=Δ₁=∅`.
  Yields `I` with `A ⊢ₛ I`, `I ⊢ₛ B`, `vars I ⊆ vars A ∩ vars B`; package as
  `⊢ A→I`, `⊢ I→B` via `impR`. Mechanical once the core is done.
- **LJ Craig:** analogous from the LJ core.
- **Algebraic / Lindenbaum–Heyting interpolation corollary:** the task marks this
  "consider… out-of-scope-unless-cheap." It is **NOT cheap** — it needs a
  Lindenbaum/Heyting-algebra substrate that does not yet exist in this directory.
  **Recommend explicitly out of scope** for task 374; spin off as a follow-up task if
  desired.

---

## 8. Risks

1. **`vars`-bound bookkeeping (highest risk).** Carrying the
   `vars I ⊆ vars(Γ₁∪Δ₁) ∩ vars(Γ₂∪Δ₂)` invariant through every case roughly doubles
   proof size and is the main source of `simp`/`Finset` grind. Mitigation: prove a small
   battery of `vars` rewrite lemmas up front (`vars_and`, `vars_or`, `vars_imp`,
   `vars_union`, `vars_insert`, `vars_biUnion_subset`) so each case is `simp`-closable.
2. **Leaf `ax` table.** The identity-axiom interpolant has 2–4 sub-cases (which side each
   of the two `A` occurrences lands). Getting `⊥/⊤/A/¬A` right and re-deriving both half
   sequents is the classic Maehara subtlety. Allocate dedicated effort.
3. **Two-premise interpolant combination (`andR`,`orL`,`impL`).** Reassembling *both*
   half-derivations with `mono`/`insert_union` and proving the combined `vars` bound is
   the bulk of the hard work.
4. **Induction index hygiene.** Must use the separate `(d, hcf)` + `induction d with`
   pattern; attempting `induction` on the `CutFree` subtype or with the cover equations
   un-generalized will fail. The `cutFreeSubformulaProp` precedent de-risks this.
5. **`Nonempty` vs `Type` derivations.** Keeping conclusions in `Prop` (`Nonempty`) is
   recommended; if a later need wants the actual proof term, switching is invasive.
6. **lint/CI:** new `def Proposition.vars` and any `@[simp]` `vars` lemmas need docstrings
   (docBlame) and simpNF-valid LHSs; Prop-valued results must be `lemma`/`theorem`.

---

## 9. Realistic Phase Count & Effort Estimate

Estimated **~400–650 lines**, **6 phases** (largest item in the backlog as flagged):

1. **Phase 1 — `Proposition.vars` + lemma battery** (shared file). ~60–90 lines. (M)
2. **Phase 2 — LK `maeharaCore` statement + easy cases** (ax-leaf placeholder, botL,
   weakL, weakR, andL, orR). Establish the partition-threading scaffold. ~120–160 lines.
3. **Phase 3 — LK hard cases** (`ax` full leaf table, `andR`, `orL`, `impL`, `impR`).
   ~120–180 lines. (H)
4. **Phase 4 — LK Craig corollary** (`A→B` form) + top-level
   `CutFreeLKProof.interpolation` / `LKProof.interpolation` (via `cutElim`). ~50–70 lines.
5. **Phase 5 — LJ `maeharaCore` (single-conclusion) all cases.** ~120–170 lines. (H for
   impL/orL).
6. **Phase 6 — LJ Craig corollary + CI hardening** (lint, shake, init imports, test).
   ~40–60 lines.

Suggested new files (mirroring the existing `LK/…`, `LJ/…` layout):
`SequentCalculus/Vocabulary.lean` (or extend `Subformula.lean`),
`SequentCalculus/LK/Interpolation.lean`, `SequentCalculus/LJ/Interpolation.lean`.
Algebraic-interpolation corollary: **excluded** (§7).

**No `sorry`, no new axioms** is achievable — the construction is fully classical
structural induction over an already-cut-eliminated proof, with all required Finset and
cut-elimination infrastructure present in-repo. The risk is *length/bookkeeping*, not
*provability*; if a phase stalls it should be marked `[BLOCKED]` with the exact stuck
goal, never `sorry`-deferred.
