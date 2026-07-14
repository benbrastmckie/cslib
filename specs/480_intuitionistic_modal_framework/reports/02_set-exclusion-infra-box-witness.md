# Research Report 02: Set-Exclusion Infrastructure + Corrected Box Witness (Task 480, Phase 2b)

- **Task**: 480 — Intuitionistic modal metalogic framework
- **Focus**: ONE blocker — the missing SET-exclusion ("Lindenbaum pair") infrastructure that Phase 2b's
  seeded-`w'` box-witness construction requires.
- **Mode**: `--hard --lit` (H2 anti-analysis, H3 BibKey grounding, H4 adversarial verification)
- **Reference grounding tier**: Tier 1 (literature-backed)
- **Verdict**: **FEASIBLE, zero-debt, purely additive.** Concrete Lean statement + proof strategy below.

## Executive Summary

The Phase 2b blocker is correctly diagnosed in the plan's "UPDATE (second dispatch)" note: the seeded-`w'`
construction needs to extend a set to a prime theory that excludes an **entire set** `Σ`, and Cslib has only
**single-formula** exclusion (`Metalogic.prime_exclusion`). This report delivers the exact generalizing lemma
(`prime_set_exclusion`), grounded against the **actual** `PrimeExclusion.lean` code, and confirms the whole change
is additive (no edit to `prime_exclusion` or any existing declaration). The generic Zorn/chain machinery already
in the file carries over almost verbatim; the only genuinely new content is (a) an object-level big-disjunction
`bigOr` with two monotonicity lemmas, and (b) the disjunction-property step of `set_maximal_is_prime`. Estimated
~180–250 lines in Foundations, plus a ~40-line modal wrapper.

---

## Source-to-Implementation Mapping (H3, Tier 1)

| Source Claim | BibKey | Lean Target | Translation Notes |
|--------------|--------|-------------|-------------------|
| Prime filters as intuitionistic-modal worlds; "certain prime filters + accessibility between prime filters" | `Wijesekera1990` (chunks 0040–0044) | `CanonicalPrimeWorld`, `canonicalR` | OCR is severely truncated (2 lines/chunk); confirms methodology, not usable for line-by-line transliteration. **BibKey NOT yet in `references.bib` — must be added.** |
| Canonical birelational model `B=(W,≤,R,V)` for IK; `cmreach` = box-clause ∧ diamond-clause | `Simpson1994` (Ch. 3, chunk_0223) | `canonicalR` (Phase 2a, confirmed correct) | BibKey present (`references.bib:86`). OCR-garbled for the F2 / witness derivations. |
| Lindenbaum-pair extension: `Γ ⊬ Σ` (no finite disjunction of `Σ` derivable from `Γ`) ⟹ ∃ prime `T ⊇ Γ`, `T ∩ Σ = ∅` | ianshil/CK (`theories/Completeness_th/general_th_completeness.v`, `Lindenbaum_pair`/`pair_extCKH_prv`) | **`prime_set_exclusion`** (NEW, this report) | External Coq mechanization; no `references.bib` entry (code artifact, cite inline as a URL comment). Definitionally matches our `canonicalR`. |
| Generic prime exclusion via Zorn (single formula) | `ChagrovZakharyaschev1997`, Lemma 5.5 | `Metalogic.prime_exclusion` (existing) | BibKey present (`references.bib:75`). The set version is the natural generalization of its Zorn domain. |

**BibKey verification status**: `Simpson1994` ✅, `ChagrovZakharyaschev1997` ✅ verified in `references.bib`.
`Wijesekera1990` ❌ **absent** — a `@article{Wijesekera1990,...}` entry (Constructive Modal Logics I, *Annals of
Pure and Applied Logic* 50(3):271–301, 1990) should be added before any file cites `[Wijesekera1990]`. It is
already referenced textually in `CanonicalModel.lean`'s docstring, so this is a pre-existing citation gap, not one
introduced here.

---

## Deliverable 1 — Exact Lean statement of the set-exclusion lemma

Placed in `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` (see Deliverable 4 for placement rationale),
inside a new `section` adding `variable [HasBot F]` (HasBot is already in scope: `Connectives.lean:80`, imported
transitively via `Consistency.lean:11`). All additions are new declarations — nothing existing is touched.

```lean
/-- Object-level iterated disjunction of a finite list; `bigOr [] = ⊥`. -/
def bigOr : List F → F
  | []      => HasBot.bot
  | x :: xs => HasOr.or x (bigOr xs)

/-- `T` derives no finite disjunction of `Σ`. For deductively-closed `T` this is equivalent to
`∀ l ⊆ Σ (finite), T ⊬ bigOr l`. The `l = []` case is `⊥ ∉ T` (consistency), so this predicate
subsumes consistency-relative-to-`Σ`. -/
def DerivExcludes (D : DerivationSystem F) (Σ : Set F) (T : Set F) : Prop :=
  ∀ l : List F, (∀ x ∈ l, x ∈ Σ) → bigOr l ∉ T

/-- Zorn domain for set exclusion: admissible `Σ`-excluding supersets of `S`. -/
def SetExcludingSupersets (D : DerivationSystem F) (Cons : Set F → Prop)
    (S : Set F) (Σ : Set F) : Set (Set F) :=
  {T | S ⊆ T ∧ Admissible D Cons T ∧ DerivExcludes D Σ T}

/-- **Generic Set (Lindenbaum-Pair) Exclusion Lemma**: given an admissible `S` that derives no
finite disjunction of `Σ`, there is a prime admissible `T ⊇ S` still deriving no finite disjunction
of `Σ` (in particular `T ∩ Σ = ∅`). Generalizes `prime_exclusion` from a single excluded formula
to an excluded set. -/
theorem prime_set_exclusion
    (D : DerivationSystem F) (Cons : Set F → Prop)
    {S : Set F} (hS : Admissible D Cons S)
    {Σ : Set F} (h_excl : DerivExcludes D Σ S)          -- the consistency-relative-to-Σ hypothesis
    -- object-logic ∨/⊥ schemas as empty-context derivations (all exist as `Axioms.OrI1/OrI2/OrE/EFQ`):
    (hOrI1 : ∀ A B : F, D.Deriv [] (HasImp.imp A (HasOr.or A B)))
    (hOrI2 : ∀ A B : F, D.Deriv [] (HasImp.imp B (HasOr.or A B)))
    (hOrE  : ∀ A B χ : F, D.Deriv [] (HasImp.imp (HasImp.imp A χ)
                (HasImp.imp (HasImp.imp B χ) (HasImp.imp (HasOr.or A B) χ))))
    (hEFQ  : ∀ A : F, D.Deriv [] (HasImp.imp HasBot.bot A))
    -- SAME closure operator + laws + cut witness that `prime_exclusion` already takes:
    (cl : Set F → Set F)
    (cl_subset : ∀ X, X ⊆ cl X)
    (cl_mem_imp : ∀ {X ψ}, ψ ∈ cl X → ∃ L, (∀ x ∈ L, x ∈ X) ∧ D.Deriv L ψ)
    (cl_admissible_of_cons : ∀ {X}, Cons X → Admissible D Cons (cl X))
    (hCut : ∀ {U : Set F} {L : List F} {a b : F},
        (∀ x ∈ L, x ∈ insert a U) → D.Deriv L b →
        ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (HasImp.imp a b))
    (hConsChain : ∀ C, IsChain (· ⊆ ·) C → C.Nonempty →
        C ⊆ SetExcludingSupersets D Cons S Σ → Cons (⋃₀ C)) :
    ∃ T, S ⊆ T ∧ PrimeAdmissible D Cons T ∧ DerivExcludes D Σ T
```

**Precise consistency-relative-to-`Σ` hypothesis**: `h_excl : DerivExcludes D Σ S`, i.e.
`∀ l : List F, (∀ x ∈ l, x ∈ Σ) → bigOr l ∉ S`. Since `S` is deductively closed (from `hS`), this is exactly
"no finite disjunction of `Σ` is derivable from `S`" — the ianshil/CK `pair` condition.

**Single-formula `prime_exclusion` as a corollary** (`Σ := {phi}`): every sublist of `{phi}` is `[]` (→ `⊥`) or
`[phi, …, phi]` (→ `phi ⊔ (phi ⊔ … ⊔ ⊥)`). `DerivExcludes D {phi} S` then unpacks to `⊥ ∉ S` (consistency, which
`prime_exclusion` gets from `hS`/`Cons`) and, via the disjunction property of the **output** `T`, to `phi ∉ T`
(strip the trailing `⊔⊥` using `PrimeAdmissible`). So `prime_exclusion`'s conclusion is recoverable, at the cost
of the extra `hOrI1/hOrI2/hEFQ` schema inputs (which every real instantiation already has). **Recommendation: do
NOT refactor `prime_exclusion` to route through this** — keep it independent to hold blast radius at zero (see
Deliverable 4). Note `bigOr [phi] = phi ⊔ ⊥`, not `phi`; if a perfectly clean corollary is wanted later, define
`bigOr [x] = x` with a 3-way match, at the cost of slightly more append-lemma case-work.

---

## Deliverable 2 — Proof strategy, reuse, and feasibility

### Helpers that carry over essentially verbatim

| Existing helper (`PrimeExclusion.lean`) | Reuse in set version |
|-----------------------------------------|----------------------|
| `prime_excluding_base_mem` (L71) | Direct analogue `set_excluding_base_mem`: `S ∈ SetExcludingSupersets` from `hS` + `h_excl`. Trivial. |
| `deductivelyClosed_chain_union` (L82) | **Used unchanged** (about `DeductivelyClosed`, `Σ`-agnostic). |
| `prime_excluding_chain_union` (L94) | Analogue `set_excluding_chain_union`: the `phi ∉ ⋃₀C` clause becomes `DerivExcludes D Σ (⋃₀C)`. Same one-line `rintro ⟨T,hTC,h⟩` argument — `bigOr l ∈ ⋃₀C` lands in a single chain member, contradicting that member's `DerivExcludes`. (Even simpler than the existing version; no `finite_list_in_chain_member` needed because `bigOr l` is a single formula.) |
| `zorn_subset_nonempty` call (L243) | Unchanged shape. |

### The one genuinely new argument: `set_maximal_is_prime`

Mirror of `prime_maximal_is_prime` (L125). Setup identical: `A ⊔ B ∈ T`, assume `A ∉ T`, `B ∉ T`, derive `False`.
The single change is that the fixed excluded `phi` becomes a **per-branch finite disjunction** of `Σ`:

1. For `X ∈ {A, B}`: `cl (insert X T)` is not in the Zorn domain (else maximality forces it `= T`, but it
   contains `X ∉ T`). Case on `Cons (insert X T)`:
   - **Consistent**: `cl_admissible_of_cons` makes it admissible, so the domain-failure is `DerivExcludes`
     failing: `∃ lₓ` with `(∀ y ∈ lₓ, y ∈ Σ)` and `bigOr lₓ ∈ cl (insert X T)`. Via `cl_mem_imp` + `hCut`,
     extract `Lₓ ⊆ T` with `Lₓ ⊢ X → bigOr lₓ`.
   - **Inconsistent**: `insert X T ⊢ ⊥`; via `hCut` get `Lₓ ⊆ T` with `Lₓ ⊢ X → ⊥`. Take `lₓ := []`
     (`bigOr [] = ⊥`); same shape `Lₓ ⊢ X → bigOr lₓ`. (This replaces the old `phi_mem_cl_of_not_cons` EFQ
     bridge — now discharged by `hEFQ` at the combination step.)
   Both branches yield `lₐ, l_b ⊆ Σ` (possibly empty) and `Lₐ, L_b ⊆ T` with `Lₐ ⊢ A → bigOr lₐ`,
   `L_b ⊢ B → bigOr l_b`.
2. **Combine** to target `χ := bigOr (lₐ ++ l_b)` (a disjunction of `Σ`, hence forbidden in `T`):
   - `⊢ bigOr lₐ → bigOr (lₐ ++ l_b)`  — **NEW** `bigOr_append_left` (see below).
   - `⊢ bigOr l_b → bigOr (lₐ ++ l_b)`  — **NEW** `bigOr_append_right`.
   - compose (imp-transitivity via `hOrI`/MP) to get `A → χ` and `B → χ`, then `hOrE` + `A ⊔ B ∈ T` gives
     `T ⊢ χ`; deductive closure of `T` gives `bigOr (lₐ ++ l_b) ∈ T`, contradicting `DerivExcludes D Σ T`
     applied to `lₐ ++ l_b`.

   The orE-plumbing (weaken `hOrE`, three MPs, `h_dc`) is **copied verbatim** from `prime_maximal_is_prime`
   L182–211 with `phi` replaced by `χ`.

### New derivation lemmas (the only real new work)

All provable from the supplied `hOrI1/hOrI2/hOrE/hEFQ` empty-context schemas — **no new axiom**:

- `bigOr_append_right : ∀ l₁ l₂, D.Deriv [] (HasImp.imp (bigOr l₂) (bigOr (l₁ ++ l₂)))`
  — induction on `l₁`: base = identity `⊢ φ → φ`; step = `hOrI2` composed with IH.
- `or_right_mono : (D.Deriv [] (b → b')) → D.Deriv [] ((HasOr.or x b) → (HasOr.or x b'))`
  — from `hOrI1 x b'`, `hOrI2 x b'`, `hOrE`.
- `bigOr_append_left : ∀ l₁ l₂, D.Deriv [] (HasImp.imp (bigOr l₁) (bigOr (l₁ ++ l₂)))`
  — induction on `l₁`: base `⊢ ⊥ → bigOr l₂` = `hEFQ`; step = `or_right_mono` applied to IH.
- plus small `imp`-transitivity/`MP`-composition glue (the file already has this pattern).

These mirror `PrimeTheory.lean`'s existing bespoke `DerivationTree` constructions (e.g. `modal_deriv_imp_of_union`,
`modalNegPhiImpPsi`), so the style is well-precedented.

### Feasibility & line estimate

**Zero-debt: FEASIBLE.** No step needs a lemma Cslib lacks — `OrI1/OrI2/OrE/EFQ` all exist in
`Cslib.Logic.Axioms` (`Axioms.lean:122–133, 85`), and the Zorn/chain scaffolding is reused. There is **no** open
mathematical question (the plan's `◇⊤` red herring is resolved by the seeded-`w'` move; the ianshil/CK
mechanization is a working proof of exactly this lemma).

| Component | File | Est. lines |
|-----------|------|-----------|
| `bigOr`, `DerivExcludes`, `SetExcludingSupersets`, `bigOr_append_*`, `or_right_mono` | `PrimeExclusion.lean` | ~70–100 |
| `set_excluding_base_mem`, `set_excluding_chain_union`, `set_maximal_is_prime`, `prime_set_exclusion` | `PrimeExclusion.lean` | ~110–150 |
| **Foundations subtotal** | | **~180–250** |
| `modal_set_exclusion` wrapper (mirror of `modal_prime_exclusion`) | `PrimeTheory.lean` | ~40 |

This exceeds one bounded phase; recommend it be its own phase/task (the plan already anticipated this).

---

## Deliverable 3 — Reformulated `canonical_box_witness` + where K◇ discharges the obligation

### Corrected statement (pair `⟨w', u⟩`, `w ≤ w'`)

```lean
/-- Box witness (corrected): from `□φ ∉ w`, produce a SEEDED extension `w' ≥ w` and a prime `u`
excluding `φ` with `canonicalR w' u`. The outer `w ≤ w'` is load-bearing (consumed by `BForces_box`
in Phase 3b), NOT the `⟨w, v⟩` sketch of report §6.5. -/
theorem canonical_box_witness
    {Axioms : Proposition Atom → Prop}
    (h_implyK : …) (h_implyS : …) (h_efq : …) (h_orE : …)
    (h_orI1 : …) (h_orI2 : …)                    -- new: OrI schemas for prime_set_exclusion
    (h_K : ∀ φ ψ, Axioms (Axioms.AxiomK φ ψ))    -- box distribution (already used in step 1)
    (h_Kdia : ∀ A B : Proposition Atom,          -- new: K◇ = □(A→B) → (◇A → ◇B)
        Axioms ((□(A.imp B)).imp ((◇A).imp (◇B))))
    (w : CanonicalPrimeWorld Axioms) {φ : Proposition Atom} (h_notbox : (□φ) ∉ w.val) :
    ∃ w' u : CanonicalPrimeWorld Axioms, w ≤ w' ∧ canonicalR w' u ∧ φ ∉ u.val
```

`h_Kdia` is a **new explicit parametric hypothesis** in the framework's established style (an
`Axioms (…)` schema, exactly like `h_implyK`/`h_orE`). There is no `Axioms.AxiomKDia` abbrev yet
(`Axioms.lean` has only classical, `◇`-encoded modal axioms); adding one is optional and out of scope.

### Construction (transliterate ianshil/CK `general_th_completeness.v`, Box case, lines ~140–200)

- **Step 1 (already `[x]`)**: `u := ` prime extension (`modal_prime_exclusion`) of `{ψ | □ψ ∈ w.val}` excluding
  `φ`. Gives `{ψ | □ψ ∈ w.val} ⊆ u.val`, `φ ∉ u.val`. Requires `{ψ | □ψ ∈ w.val}` admissible: deductive closure
  uses the deductively-closed variant of `derive_box_from_box_context` (`MCS.lean:357`, box-distributes-over-
  derivation); `φ ∉ closure` from `□φ ∉ w.val`.
- **Step 2 (the fix, needs `prime_set_exclusion`)**: `w' := ` prime extension of
  `Γ := w.val ∪ {◇A | A ∈ u.val}` **excluding** `Σ := {□B | B ∉ u.val}`, via `modal_set_exclusion`.
- **The three witness obligations then hold by construction:**
  - `w ≤ w'`: `w.val ⊆ Γ ⊆ w'.val`. ✅
  - diamond clause `∀ψ, ψ ∈ u.val → ◇ψ ∈ w'.val`: `◇ψ ∈ {◇A | A ∈ u.val} ⊆ Γ ⊆ w'.val`. ✅ (seeding)
  - box clause `∀ψ, □ψ ∈ w'.val → ψ ∈ u.val`: contrapositive `ψ ∉ u.val → □ψ ∈ Σ → □ψ ∉ w'.val`
    (from `DerivExcludes` applied to `l := [□ψ]`, since `w'` is `Σ`-excluding). ✅
  - `φ ∉ u.val`: Step 1. ✅

### Where K◇ discharges the seeding consistency obligation

The `prime_set_exclusion` precondition for Step 2 is
`h_excl : DerivExcludes (modalDerivationSystem Axioms) Σ Γ`, i.e.

> no finite disjunction `□B₁ ⊔ … ⊔ □Bₙ` (each `Bᵢ ∉ u.val`) is derivable from
> `Γ = w.val ∪ {◇A | A ∈ u.val}`.

This is a **separate, second new sub-lemma** (call it `box_witness_pair_underivable`) — it is NOT part of the
generic infra lemma; it is the modal-specific consistency argument the implementer must prove in the re-dispatched
Phase 2b. Sketch (this is the `Kd`/`K_rule` step in ianshil/CK): suppose `Γ ⊢ □B₁ ⊔ … ⊔ □Bₙ`. A finite subset
uses `g₁,…,g_k ∈ w.val` and `◇A₁,…,◇A_m` with each `Aⱼ ∈ u.val`. The only object-logic bridge between the boxed
conclusion and the diamond hypotheses is **K◇** (`□(A→B) → (◇A → ◇B)`): it lets a proof of
`□(Aⱼ → (B₁ ∨ … ∨ Bₙ))` be turned into `◇Aⱼ → ◇(B₁ ∨ … ∨ Bₙ)`. Combined with `{ψ | □ψ ∈ w} ⊆ u`, the disjunction
property of the prime theory `u`, and `Bᵢ ∉ u.val`, this forces some `Bᵢ ∈ u.val` — contradiction. **Estimate
~60–120 lines**; it is the delicate modal step and should carry its own STOP contingency. It depends only on the
axioms `AxiomK` and K◇ plus `u`'s primeness — no `◇⊤`/seriality precondition anywhere (the seeded `w'` removes it).

`canonical_diamond_witness` (Phase 2c) is the **mirror image**: seed the *box*-side and exclude a diamond-set;
the same `prime_set_exclusion` covers it. (Confirms the plan's note.)

---

## Deliverable 4 — Placement & blast radius

**Recommendation: put the generic lemma (`bigOr`, `DerivExcludes`, `SetExcludingSupersets`,
`set_excluding_base_mem`, `set_excluding_chain_union`, `set_maximal_is_prime`, `prime_set_exclusion`, and the
`bigOr_append_*`/`or_right_mono` derivation helpers) in Foundations `PrimeExclusion.lean`; add a thin
`modal_set_exclusion` wrapper in `PrimeTheory.lean`.**

Rationale:
- It is **generic and reusable** — the minimal (`MinLindenbaum`), intuitionistic (`IntLindenbaum`), and modal
  layers all instantiate the same abstract `DerivationSystem`; set exclusion is exactly as foundational as
  single-formula exclusion. Burying it in the modal layer would deny reuse to the propositional intuitionistic
  completeness development.
- It lives **beside** the machinery it reuses (`deductivelyClosed_chain_union`, `PrimeExcludingSupersets`,
  `prime_maximal_is_prime`), keeping the two Zorn arguments in one place.

**The change is purely ADDITIVE — confirmed:**
- No existing declaration is modified. `prime_exclusion` and all its helpers are left byte-for-byte identical;
  the corollary relationship is documented, not enforced by refactor (deliberately, to keep blast radius zero).
- Only new `def`/`theorem`s are added, inside a new `section` that adds `variable [HasBot F]`. `HasBot` is already
  in scope (`Connectives.lean:80`, imported via `Consistency.lean:11`), so **no new import** is required and no
  existing signature (which uses only `[HasImp F] [HasOr F]`) changes.
- `PrimeExclusion.lean` is imported widely across `Metalogic/`, but additive-only changes to a `public section`
  cannot break downstream elaboration (no instance/notation/signature churn). The CI gates
  (`checkInitImports`, `lint-style`, `shake`) are unaffected beyond docstring-lint on the new decls.

The modal wrapper `modal_set_exclusion` in `PrimeTheory.lean` mirrors `modal_prime_exclusion` (L315–358) exactly:
supply `Cons := ModalSetConsistent Axioms`, `cl := modalDeductiveClosure Axioms`, the `hOrI1/hOrI2` from
`Axioms.OrI1/OrI2`, `hEFQ` from `h_efq`, and the same `hConsChain` chain-consistency closure. ~40 lines, additive
to `PrimeTheory.lean` (Phase 1 is otherwise preserved; adding one new theorem does not "re-open" it — but confirm
this is acceptable under the plan's "do not modify `PrimeTheory.lean`" rule; if strict, place `modal_set_exclusion`
in `CanonicalModel.lean` instead, which is equally valid since it only needs the public `prime_set_exclusion`).

---

## Deliverable 5 — BibKey-grounded citations

- `[Simpson1994]` ✅ (`references.bib:86`) — Ch. 3 canonical birelational model; `cmreach`/`canonicalR`
  box+diamond clauses. OCR-garbled for F2/witness derivations; use ianshil/CK as the reconstruction reference.
- `[ChagrovZakharyaschev1997]` ✅ (`references.bib:75`), Lemma 5.5 — the single-formula Zorn prime-exclusion that
  `prime_set_exclusion` generalizes.
- `[Wijesekera1990]` ❌ **not in `references.bib`** — add
  `@article{Wijesekera1990, author={Wijesekera, Duminda}, title={Constructive Modal Logics I},
  journal={Annals of Pure and Applied Logic}, volume={50}, number={3}, pages={271--301}, year={1990}}`.
  Local corpus `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/` chunks 0040–0044 confirm the
  "prime filters + accessibility between prime filters" methodology but are too OCR-truncated for transliteration.
- **ianshil/CK** (`github.com/ianshil/CK`, `theories/Completeness_th/general_th_completeness.v`) — a working Coq
  mechanization of exactly this construction; `Lindenbaum_pair`/`pair_extCKH_prv` is the `prime_set_exclusion`
  reference proof and its `cmreach`/`Kd` are the `canonicalR`/box-witness references. Cite inline as a URL comment
  (code artifact, not a bibliography entry).
- **Cleaner secondary IK source than the OCR scan**: `biermandepaiva_2000_onanintuitionisticmodallogic` is present
  in the global corpus but treats IS4 categorically and does **not** give the prime-theory canonical model; it is
  NOT a better substitute for the witness derivation. The ianshil/CK mechanization remains the most reliable
  ground truth for the exact multi-step argument. No cleaner canonical-model paper was found locally.

---

## Adversarial Self-Verification (H4)

Challenged each load-bearing claim:

1. **"The generic Zorn machinery carries over."** Verified against actual code: `deductivelyClosed_chain_union`
   (L82) is `Σ`-agnostic (reused unchanged); `prime_excluding_chain_union` (L94) and `prime_maximal_is_prime`
   (L125) have the `phi`-specific clause isolated to one sub-goal each, mechanically replaceable by `DerivExcludes`
   / `bigOr (lₐ++l_b)`. **Confirmed** — no hidden dependence on single-formula-ness elsewhere.
2. **"Only genuinely new work is `bigOr` + monotonicity + the disjunction-property step."** Challenged: does the
   inconsistent-`Cons` branch still close without the old `phi_mem_cl_of_not_cons` bridge? Yes — `lₓ := []`,
   `bigOr [] = ⊥`, and `hEFQ` lifts `X → ⊥` at the combine step. **Confirmed, and it simplifies the signature**
   (bridge removed). Uncertainty (LOW): the exact `List.append`/`bigOr` `simp` normal forms may need one or two
   `List.mem_append` lemmas — routine, not a design risk.
3. **"Single-formula `prime_exclusion` is a corollary."** Challenged and PARTIALLY REVISED: `bigOr [phi] = phi ⊔ ⊥`,
   not `phi`, so the corollary needs the output `T`'s disjunction property to strip `⊔⊥`, and needs the extra
   `OrI/EFQ` schema inputs. So it is a corollary **modulo added hypotheses**, not a literal drop-in. Revised the
   recommendation accordingly: keep `prime_exclusion` independent; do not refactor. **This is the safe,
   zero-blast-radius choice** and satisfies the task's "(or could be) a corollary" wording.
4. **"K◇ discharges the seeding obligation."** Challenged the scope: the K◇ argument is NOT inside the generic
   infra lemma — it is a *separate* modal sub-lemma (`box_witness_pair_underivable`) proving the
   `DerivExcludes Γ Σ` precondition. Flagged explicitly (Deliverable 3) with its own ~60–120-line estimate and
   STOP contingency, so the implementer does not conflate "add the infra lemma" (routine) with "prove the modal
   consistency argument" (delicate). This is the one residual risk; grounded on ianshil/CK `Kd`/`K_rule`.
5. **"Purely additive."** Challenged the `[HasBot F]` addition: verified `HasBot` is already imported
   (`Connectives.lean:80` via `Consistency.lean:11`), so no new import and no change to existing `[HasImp][HasOr]`
   signatures. **Confirmed additive.** Residual (LOW): placing `modal_set_exclusion` in `PrimeTheory.lean`
   technically edits a "preserved" file — flagged the `CanonicalModel.lean` alternative to respect the plan's
   no-touch rule if enforced strictly.

**No forbidden outputs**: this report ends in concrete Lean signatures and a phase-ready construction, not an
analysis-only verdict. **Zero-debt compliance**: no recommendation introduces `sorry`/`admit`/`axiom`; K◇ is a
parametric hypothesis (framework style), not a new global `axiom`. **Reuse Check**: exhausted — `lean_local_search`
equivalent (grep) over `Foundations/` and `Logics/Modal/` confirmed no existing set/pair-exclusion lemma; the OrI
schemas already exist and are reused rather than redefined.

## Recommended next steps

1. Add `prime_set_exclusion` (+ helpers) to `PrimeExclusion.lean` as its own phase/task — additive, ~180–250 lines,
   zero-debt (feasible).
2. Add `modal_set_exclusion` wrapper (~40 lines; in `CanonicalModel.lean` to respect the `PrimeTheory.lean`
   no-touch rule, or `PrimeTheory.lean` if permitted).
3. Re-dispatch Phase 2b with the corrected `⟨w', u⟩` witness; prove `box_witness_pair_underivable` (the K◇
   consistency sub-lemma) with a STOP contingency.
4. Add the `Wijesekera1990` entry to `references.bib` before any file emits a `[Wijesekera1990]` citation.
