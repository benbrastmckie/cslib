# Research Report: Task 344 — Algebraic Strong (Context/Theory) Completeness for the Hilbert System

**Task**: Add algebraic STRONG completeness for the Hilbert system, extending 341's weak
completeness and factored through `v ⊨ T`. Goal:

```
SetDerivable Axioms Γ φ ↔ (algebraic Γ-consequence)
```

where algebraic Γ-consequence means: every GHA model `(v, bot_val)` with
`v ⊨[bot_val] AxiomTheory Axioms` **and** `v⟦ψ⟧ = ⊤` for all `ψ ∈ Γ` satisfies `v⟦φ⟧ = ⊤`.
Stay on Hilbert; reuse `SetDerivable`, `HilbertLindenbaumAlgebra`/`canonicalV`/`canonicalBotVal`,
and `[MinimalAxioms Axioms]`. Recover 341's weak theorem as the `Γ = ∅` case. CI green.

**Status**: researched

---

## 1. Executive Summary

The forward (soundness) direction is a **clean one-line reuse** of the existing
`alg_theory_soundness` (Soundness.lean:200) — verified to compile (Section 5.1).

The backward (completeness) direction is the substantive work. The key research finding:

> **The pointwise-⊤ premise cannot be discharged by instantiating the *standard*
> `canonicalV` Lindenbaum model**, because `canonicalV ⊨ Γ` forces every `ψ ∈ Γ` to be a
> *theorem* (`[ψ] = ⊤ ↔ Derivable Axioms ψ`, via `hilbertLindenbaumMk_eq_top_iff`). That only
> holds for `Γ ⊆ {theorems}`, i.e. essentially the `Γ = ∅` case.

Two sound routes exist. I recommend **Route A (Γ-relativized Lindenbaum quotient)** because it
stays purely on the Hilbert substrate (the task's explicit constraint) and reuses the existing
quotient scaffolding by parameter substitution. **Route B (Kripke bridge) is UNSOUND for the
strong case** and must be avoided — documented in Section 4.3 as an anti-pattern.

The only genuinely new metatheoretic lemma needed is a **deduction theorem at the
`SetDerivable` level** (`setDeriv_deduction`), which mirrors the already-proven
`min_deriv_imp_of_union` (MinLindenbaum.lean:116) line-for-line and is generic over
`[MinimalAxioms Axioms]`. Verified: `setDeriv_cut` reduces cleanly to it plus the existing
`SetDerivable_mp` (Section 5.2).

**Recommendation**: Implement Route A in three phases:
1. **P1 — SetDerivable metatheory**: `setDeriv_deduction` (+ `setDeriv_cut`), generic, mirroring
   `min_deriv_imp_of_union`.
2. **P2 — Γ-relativized quotient + top-char**: a context-relative top characterization
   `relMk_eq_top_iff : [ψ]_Γ = ⊤ ↔ SetDerivable Axioms Γ ψ`, built by reusing the
   `HilbertLindenbaumAlgebra` construction with `SetDerivable Axioms Γ` as the provability
   relation (or by a contrapositive that constructs the witness model from `Γ`).
3. **P3 — The iff theorem** `hilbert_alg_strong_complete_theory`, with forward = `alg_theory_soundness`
   reuse and backward = relativized instantiation. Recover 341 as `Γ = ∅` (via
   `SetDerivable_empty_iff`).

---

## 2. Mapping the 341 Weak-Completeness Scaffolding

All file paths are absolute under `/home/benjamin/Projects/cslib/`.

### 2.1 The weak theorem to extend (341)

`Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean:64`

```lean
theorem hilbert_alg_complete_theory {Atom : Type u}
    (Axioms : PL.Proposition Atom → Prop) [MinimalAxioms Axioms]
    {φ : PL.Proposition Atom} :
    Derivable Axioms φ ↔
    ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      v ⊨[bot_val] AxiomTheory Axioms → AlgEvaluate v bot_val φ = ⊤
```

Backward proof body (lines 73–79): instantiate at `HilbertLindenbaumAlgebra Axioms` with
`canonicalV`/`canonicalBotVal`, discharge the `AlgTValid` premise via `canonicalV_algTValid`,
then `canonicalV_spec` + `hilbertLindenbaumMk_eq_top_iff`. **This is the exact shape task 344
generalizes** — adding the `Γ` premise on both sides.

### 2.2 The Lindenbaum quotient scaffolding

`Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean`

| Symbol | Line | Meaning |
|---|---|---|
| `HilbertEquiv Axioms A B` | 56 | `Deriv Axioms [A] B ∧ Deriv Axioms [B] A` |
| `hilbertPropositionSetoid` | 133 | setoid from `HilbertEquiv` (needs `MinimalAxioms` for trans) |
| `HilbertLindenbaumAlgebra Axioms` | 146 | `Quotient hilbertPropositionSetoid` |
| `hilbertLindenbaumMk A` | 152 | quotient map `A ↦ [A]` |
| `hilbertLindenbaumLe` | 162 | `[A] ≤ [B] ↔ Deriv Axioms [A] B` |
| `hilbertLindenbaumGHA` (instance) | 483 | the `GeneralizedHeytingAlgebra` instance |
| `hilbertLindenbaumMk_eq_top_iff` | 557 | **`[A] = ⊤ ↔ Derivable Axioms A`** (top-char) |
| `canonicalV` | 591 | `x ↦ [atom x]` |
| `canonicalBotVal` | 596 | `[⊥]` |
| `canonicalV_spec` | 607 | truth lemma: `AlgEvaluate canonicalV canonicalBotVal A = [A]` |
| `canonicalV_axiom_top` | 624 | each axiom `φ` has `[φ] = ⊤` |
| `canonicalV_algTValid` | 636 | `canonicalV ⊨[canonicalBotVal] AxiomTheory Axioms` |

The GHA axioms are built from derivability lemmas, notably the himp adjunction
`hilbertLindenbaumLe_himp_iff` (line 439: `[A] ≤ [B → C] ↔ [A ∧ B] ≤ [C]`), proved via
`hilbertImpIDeriv` (deduction theorem) + cut. **These are the lemmas the Γ-relativized quotient
must re-establish at the `SetDerivable Γ` level.**

### 2.3 Theory-parametric soundness (already handles arbitrary context)

`Cslib/Logics/Propositional/Semantics/Algebra/Soundness.lean:200`

```lean
theorem alg_theory_soundness
    {Axioms} [MinimalAxioms Axioms] {Γ : List _} {φ}
    (d : DerivationTree Axioms Γ φ)
    {H} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H)
    (hT : v ⊨[bot_val] AxiomTheory Axioms)
    (h_ctx : ∀ ψ, ψ ∈ Γ → AlgEvaluate v bot_val ψ = ⊤) :
    AlgEvaluate v bot_val φ = ⊤
```

This **already** quantifies over an arbitrary list context `Γ` with a per-formula `h_ctx`
hypothesis. The forward direction of strong completeness is a direct wrapper (Section 5.1).

### 2.4 Set-derivability and the entailment layer (343)

`Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean`

| Symbol | Line | Meaning |
|---|---|---|
| `SetDerivable Axioms Γ φ` | 57 | `∃ L, (∀ x ∈ L, x ∈ Γ) ∧ Deriv Axioms L φ` |
| `SetDerivable_of_mem` | 65 | `φ ∈ Γ → SetDerivable Axioms Γ φ` |
| `SetDerivable_weakening` | 74 | monotone in `Γ` |
| `SetDerivable_of_Derivable` | 82 | theorems are set-derivable from any `Γ` |
| `SetDerivable_empty_iff` | 90 | **`SetDerivable Axioms ∅ φ ↔ Derivable Axioms φ`** (recovers 341) |
| `SetDerivable_mp` | 106 | modus ponens closed under `SetDerivable` |

`Cslib/Logics/Propositional/Defs.lean` (343):
- `Satisfies eval A := eval A = ⊤` (222), notation `eval ⊨ A`
- `SatisfiesTheory eval T := ∀ A ∈ T, eval A = ⊤` (233), notation `eval ⊨ T`
- `AlgTValid T v bot_val := SatisfiesTheory (AlgEvaluate v bot_val) T` (Algebra.lean:150),
  notation `v ⊨[bot_val] T`

`AxiomTheory Axioms := { φ | Axioms φ }` lives in
`Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean:85` with simp lemma
`mem_axiomTheory` (line 89).

---

## 3. Precise Statement Form

The premise `v⟦ψ⟧ = ⊤ for ψ ∈ Γ` is exactly `SatisfiesTheory (AlgEvaluate v bot_val) Γ`,
which the `⊨` notation from 343 renders as `(AlgEvaluate v bot_val) ⊨ Γ`. **Recommended primary
statement** (pointwise-⊤ form, matching the task's first clause and 343's `SatisfiesTheory`):

```lean
/-- **Theory-Parametric Hilbert-Level Algebraic STRONG Completeness.** -/
theorem hilbert_alg_strong_complete_theory {Atom : Type u}
    (Axioms : PL.Proposition Atom → Prop) [MinimalAxioms Axioms]
    {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    SetDerivable Axioms Γ φ ↔
    ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      v ⊨[bot_val] AxiomTheory Axioms →
      SatisfiesTheory (AlgEvaluate v bot_val) Γ →
      AlgEvaluate v bot_val φ = ⊤
```

### 3.1 Two strength encodings — pick pointwise-⊤; defer ≤ to task 345

The task says the pointwise-⊤ form is *"equivalently the SValid/≤ form `v⟦Γ⟧ ≤ v⟦φ⟧`"*. Research
finding: **these two are NOT unconditionally interchangeable** and the ≤ form is the harder one.

- `v⟦Γ⟧` requires an *infimum* `⨅ ψ ∈ Γ, AlgEvaluate v bot_val ψ`. For **infinite** `Γ`, this
  infimum need not exist in a (non-complete) GHA. A `GeneralizedHeytingAlgebra` is **not** a
  complete lattice; arbitrary infima are unavailable.
- The pointwise-⊤ form has no such issue and is the faithful finitary notion matching
  `SetDerivable` (which is itself finitary/compact by construction).
- `SValid` does **not exist** in the codebase (`lean_local_search "SValid"` → empty). Introducing
  it (the `⨅`/`≤` reconciliation) is precisely the scope of **task 345** ("Reconcile the two
  strength encodings", TODO.md:140–142), which depends on 344.

**Recommendation**: 344 proves the pointwise-⊤ iff above. Leave the `≤`/`SValid` reconciliation
(and any finite-`Γ` `Finset.inf` bridge) to 345. Optionally, 344 MAY add a finite-`Γ` corollary
`v⟦L.inf⟧ ≤ v⟦φ⟧` form if cheap, but it is not required.

### 3.2 Recovering 341 (the `Γ = ∅` case)

```lean
example {Atom : Type u} (Axioms) [MinimalAxioms Axioms] {φ} :
    Derivable Axioms φ ↔
    ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      v ⊨[bot_val] AxiomTheory Axioms → AlgEvaluate v bot_val φ = ⊤ := by
  rw [← SetDerivable_empty_iff]
  -- hilbert_alg_strong_complete_theory at Γ = ∅; the (SatisfiesTheory _ ∅) premise is vacuous
  ...
```

The `SatisfiesTheory (AlgEvaluate v bot_val) ∅` premise is vacuously true
(`fun A hA => absurd hA (Set.not_mem_empty A)`), so the strong statement at `Γ = ∅` collapses to
exactly `hilbert_alg_complete_theory` modulo `SetDerivable_empty_iff`. **This recovery should be a
named lemma/`example` in the PR to certify the task's "recover 341" requirement** (and a regression
guard that 341's statement was not weakened).

---

## 4. Proof Strategy

### 4.1 Forward (→), soundness — CONFIRMED, trivial reuse

```lean
intro hd H _ v bot_val hT hΓ
obtain ⟨L, hL_sub, ⟨d⟩⟩ := hd
exact alg_theory_soundness d v bot_val hT (fun ψ hψ => hΓ ψ (hL_sub ψ hψ))
```

Verified to compile (Section 5.1). `hΓ : SatisfiesTheory (AlgEvaluate v bot_val) Γ` unfolds to
`∀ ψ ∈ Γ, AlgEvaluate v bot_val ψ = ⊤`, and `hL_sub : ∀ x ∈ L, x ∈ Γ` lifts it to the list
context `h_ctx` that `alg_theory_soundness` expects.

### 4.2 Backward (←), completeness — Route A: Γ-relativized Lindenbaum quotient (RECOMMENDED)

The obstruction (Section 1): the *standard* `canonicalV` model satisfies `Γ` only when `Γ`
consists of theorems. The fix is to build a model in which **every `ψ ∈ Γ` is `⊤`** — namely the
Lindenbaum algebra **relative to the context `Γ`**, where "provability" is `SetDerivable Axioms Γ`
instead of `Derivable Axioms`.

Concretely, define the relativized equivalence and reuse the *entire* GHA construction with the
provability relation swapped:

```
RelEquiv Axioms Γ A B := SetDerivable Axioms Γ (A.imp B) ∧ SetDerivable Axioms Γ (B.imp A)
```

(equivalently, factor `Deriv Axioms [A] B` through `SetDerivable Axioms (insert A Γ) B`). The GHA
axioms transfer because the underlying derivability facts have `SetDerivable`-level analogues:

| GHA axiom (HilbertLindenbaum.lean) | `Deriv`-level lemma used | `SetDerivable`-level analogue needed |
|---|---|---|
| `le_himp_iff` (439) | `hilbertImpIDeriv` + cut | `setDeriv_deduction` (NEW) + `SetDerivable_mp` |
| `le_trans` (348) | `hilbertCutSingletonDeriv` | `setDeriv_cut` (NEW; = deduction + mp) |
| `le_refl` (339) | `assumption_deriv` | `SetDerivable_of_mem` |
| `sup`/`inf`/congruence | `hilbertOr*/And*Deriv` | weaken to `SetDerivable` via `SetDerivable_weakening` + `SetDerivable_mp` |
| top-char (557) | `hilbertImpIDeriv` + cut | `relMk_eq_top_iff` (NEW): `[ψ]_Γ = ⊤ ↔ SetDerivable Axioms Γ ψ` |

Then the backward proof mirrors 341 line-for-line:

```lean
intro h
-- canonicalV_Γ ⊨ AxiomTheory Axioms   (theorems are SetDerivable from any Γ)
-- canonicalV_Γ ⊨ Γ                     (ψ ∈ Γ ⇒ SetDerivable Γ ψ ⇒ [ψ]_Γ = ⊤)
have hLind : AlgEvaluate (canonicalV_Γ) (canonicalBotVal_Γ) φ = ⊤ :=
  h (RelLindenbaumAlgebra Axioms Γ) canonicalV_Γ canonicalBotVal_Γ
    canonicalV_Γ_algTValid canonicalV_Γ_satisfiesΓ
rw [canonicalV_Γ_spec] at hLind
exact relMk_eq_top_iff.mp hLind
```

- `canonicalV_Γ ⊨ Γ` holds because for `ψ ∈ Γ`, `SetDerivable Axioms Γ ψ` follows from
  `SetDerivable_of_mem`, and `relMk_eq_top_iff` then gives `[ψ]_Γ = ⊤`. **This is exactly the step
  that fails for the standard `canonicalV` and succeeds for the relativized one.**
- `canonicalV_Γ ⊨ AxiomTheory Axioms` holds because axioms are derivable from `[]`, hence
  `SetDerivable Axioms Γ`-provable via `SetDerivable_of_Derivable`.

**Implementation economy.** There are two sub-options for building the relativized quotient:

- **A1 (parameterize the existing construction)**: generalize `HilbertEquiv`/the quotient/the GHA
  instance over a "provability relation" so both `Derivable` and `SetDerivable Γ` instantiate it.
  Cleanest long-term, but touches HilbertLindenbaum.lean — must keep 341 proofs `rfl`-stable
  (achievable by making the current defs thin specializations of the generic ones).
- **A2 (fresh relativized copy)**: add a new section/file `HilbertLindenbaumRel.lean` duplicating
  the ~10 GHA-axiom lemmas with `SetDerivable Axioms Γ` in place of `Deriv Axioms`. Zero risk to
  341; modest duplication. **Recommended for a first landing** given the task's "341 untouched"
  invariant; A1 can be a later refactor (or folded into 345).

**The only new *metatheorem*** (everything else is mechanical transfer) is the `SetDerivable`
deduction theorem:

```lean
theorem setDeriv_deduction (Axioms) [MinimalAxioms Axioms] {Γ A B}
    (h : SetDerivable Axioms (insert A Γ) B) : SetDerivable Axioms Γ (A.imp B)
```

Proof: mirror `min_deriv_imp_of_union` (MinLindenbaum.lean:116) verbatim — `obtain ⟨L, hL, ⟨d⟩⟩`,
weaken to `A :: L`, apply `deductionTheorem inst.h_K inst.h_S`, then `deductionWithMem` +
`removeAll` to clear `A` from the list (case split on `A ∈ L`). `deductionTheorem`,
`deductionWithMem`, `removeAll`, `removeAll_subset_of_subset` are all generic over `Axioms` with
`h_implyK`/`h_implyS` witnesses (DeductionTheorem.lean:130, :71), supplied by
`inst.h_K`/`inst.h_S` from `MinimalAxioms`.

### 4.3 Backward (←), Route B: Kripke bridge — REJECTED (UNSOUND)

I tested instantiating the algebraic-Γ-consequence at the upset algebra (`KripkeBridge.lean`,
`kripkeAlgBridge`:211, `mValidOfGHAValid`:280) to reduce to the existing Kripke
`min_strong_completeness` (MinStrongCompleteness.lean:244). **It does not work** and is unsound for
the strong case:

- `kripkeAlgBridge` gives `IForces v bf w ψ ↔ toDual w ∈ AlgEvaluate (upsetVal ..) (upsetBotVal ..) ψ`.
- The algebraic premise `SatisfiesTheory (AlgEvaluate ..) Γ` means `AlgEvaluate .. ψ = ⊤`, i.e.
  `toDual w ∈ eval ψ` for **all** worlds `w` (`⊤ = Set.univ`).
- But the Kripke consequence (`MSemanticEntails`) only provides forcing of `Γ` at a **single**
  world `w₀`. There is no way to upgrade "`ψ` forced at `w₀`" to "`ψ` forced at every world", so the
  `SatisfiesTheory (AlgEvaluate ..) Γ` premise of the algebraic hypothesis **cannot be discharged**.

This mismatch (pointwise-`⊤` over all worlds vs. forcing at one world) is fundamental: the
algebraic `= ⊤` condition is strictly stronger than per-world Kripke forcing. Beyond soundness, the
bridge route also contradicts the task's "stay on Hilbert, not Kripke-based" directive. **Do not
pursue Route B.** (This is a concrete instance of why the *relativized* model in Route A — where
`Γ` is baked into provability so its members are genuinely `⊤` everywhere — is necessary.)

---

## 5. Verification Evidence (lean-lsp / lake)

### 5.1 Forward direction compiles (scratch, since removed)

```lean
theorem strong_fwd_test (Axioms) [MinimalAxioms Axioms] {Γ : Set _} {φ}
    (hd : SetDerivable Axioms Γ φ)
    (H) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H)
    (hT : v ⊨[bot_val] AxiomTheory Axioms)
    (hΓ : SatisfiesTheory (AlgEvaluate v bot_val) Γ) :
    AlgEvaluate v bot_val φ = ⊤ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := hd
  obtain ⟨d⟩ := hL_deriv
  exact alg_theory_soundness d v bot_val hT (fun ψ hψ => hΓ ψ (hL_sub ψ hψ))
```
**Result**: `lake build` → `Build completed successfully (726 jobs)`.

### 5.2 `setDeriv_cut` reduces to `setDeriv_deduction` + `SetDerivable_mp` (scratch, since removed)

```lean
theorem setDeriv_cut (Axioms) [MinimalAxioms Axioms] {Γ : Set _} {A B}
    (hAB : SetDerivable Axioms (insert A Γ) B) (hA : SetDerivable Axioms Γ A) :
    SetDerivable Axioms Γ B :=
  SetDerivable_mp (setDeriv_deduction Axioms hAB) hA
```
**Result**: `lake build` → `Build completed successfully` with `setDeriv_deduction` `sorry`'d.
Confirms the composition typechecks and `SetDerivable_mp` has the right shape.

### 5.3 Reuse-check results (CSLib/Mathlib API)

- `SetDerivable_mp` — EXISTS, SemanticConsequence.lean:106. Use directly.
- `SetDerivable_of_mem`, `SetDerivable_of_Derivable`, `SetDerivable_weakening`,
  `SetDerivable_empty_iff` — EXIST, SemanticConsequence.lean. Use directly.
- `alg_theory_soundness` — EXISTS, Soundness.lean:200. Forward direction.
- `deductionTheorem`, `deductionWithMem`, `removeAll`, `removeAll_subset_of_subset` — EXIST,
  generic over `Axioms`, DeductionTheorem.lean. Building blocks for `setDeriv_deduction`.
- `min_deriv_imp_of_union` — EXISTS, MinLindenbaum.lean:116. **Template** for `setDeriv_deduction`
  (currently specialized to `MinPropAxiom`; generalize the `MinPropAxiom.mem_*` witnesses to
  `inst.h_K`/`inst.h_S`).
- `himp_eq_top_iff` (Mathlib) — EXISTS: `a ⇨ b = ⊤ ↔ a ≤ b` (the algebraic deduction theorem).
- `le_himp_iff` (Mathlib) — EXISTS: `a ≤ b ⇨ c ↔ a ⊓ b ≤ c`.
- `SetDerivable_deduction` / `setDeriv_deduction` — DO NOT EXIST. **New (P1).**
- `SValid` — DOES NOT EXIST. Out of scope for 344 (task 345).
- Γ-relativized quotient / `relMk_eq_top_iff` — DO NOT EXIST. **New (P2).**

---

## 6. Recommended Phase Plan (for the planner)

**P1 — `SetDerivable` deduction metatheory** (target: `SemanticConsequence.lean` or a new
`Metalogic/SetDeduction.lean`):
- `setDeriv_deduction : SetDerivable Axioms (insert A Γ) B → SetDerivable Axioms Γ (A.imp B)`
  (mirror `min_deriv_imp_of_union`, generic over `[MinimalAxioms Axioms]`).
- `setDeriv_cut` (one line via `setDeriv_deduction` + `SetDerivable_mp`). Verified shape (5.2).
- Verify: `lake build` of the touched module.

**P2 — Γ-relativized Lindenbaum quotient + top characterization** (Route A2: new file
`Semantics/Algebra/HilbertLindenbaumRel.lean`):
- `RelEquiv Axioms Γ`, setoid, `RelLindenbaumAlgebra Axioms Γ`, `relMk`, `relLe`.
- GHA instance (transfer the ~10 axiom lemmas using P1 + existing `SetDerivable_*`).
- `relMk_eq_top_iff : relMk Axioms Γ ψ = ⊤ ↔ SetDerivable Axioms Γ ψ`.
- `relCanonicalV`/`relCanonicalBotVal`, `relCanonicalV_spec` (truth lemma; structural induction
  mirroring `canonicalV_spec`), `relCanonicalV_algTValid`, `relCanonicalV_satisfiesΓ`.
- Verify: `lake build` of the new module.

**P3 — The strong-completeness iff + 341 recovery** (target: `HilbertCompleteness.lean` or a new
`HilbertStrongCompleteness.lean`):
- `hilbert_alg_strong_complete_theory` (Section 3 statement); forward via `alg_theory_soundness`
  (5.1), backward via P2 instantiation.
- `hilbert_alg_strong_complete_theory_empty` (or `example`): `Γ = ∅` recovers
  `hilbert_alg_complete_theory` via `SetDerivable_empty_iff`. Regression guard.
- Optional per-tier corollaries (`MPL`/`IPL`/`CPL`) mirroring HilbertCompleteness.lean:93/122/155
  if cheap.
- Full CI: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`,
  `lake test`, and `lake exe mk_all --module` if a new file is added.

---

## 7. Constraints, Risks, and Invariants

- **Zero-debt**: no `sorry`, no new axioms. The only `sorry` in this research was a scratch
  placeholder for `setDeriv_deduction`, which is concretely implementable from
  `min_deriv_imp_of_union`. If `setDeriv_deduction` or the relativized truth lemma proves
  intractable in implementation, mark the phase `[BLOCKED]` — do **not** defer with `sorry`.
- **341 untouched invariant**: prefer Route A2 (fresh relativized file) so HilbertLindenbaum.lean,
  Soundness.lean, HilbertCompleteness.lean, and Soundness.lean are not edited. If A1 (generalize in
  place) is chosen later, the existing defs must remain `rfl`-stable specializations.
- **343 invariant**: use `SatisfiesTheory`/`v ⊨[bot_val] T` exactly as defined; do not touch the
  Prop-valued `SemanticEntails` family (the deferred `propext` unification is task-345+ scope).
- **Universe discipline**: pin `{Atom : Type u}` and `(H : Type u)` to the same `u`, matching
  `hilbert_alg_complete_theory` (HilbertCompleteness.lean:64 universe note). `Type _` causes
  universe-metavariable mismatches against the Lindenbaum construction.
- **Lint**: new declarations need docstrings (docBlame); Prop-valued ⇒ `theorem`/`lemma` not `def`
  (defLemma); lowerCamelCase names (defsWithUnderscore — note existing code uses `SetDerivable_*`
  with underscores, so match the *local* file convention); `@[simp]` only with verified LHS
  (simpNF); minimize section variables (`omit`/`unusedSectionVars`).
- **Notation**: this module is algebraic (`⇨`, `⊓`, `⊔`, `≤`, `⊤`), not operational-semantics
  arrows, so the Option A/B/C reduction-notation choice does not apply here.

---

## 8. References

- A. Rasiowa, *An Algebraic Approach to Non-Classical Logics* — Lindenbaum-algebra completeness.
- A. Chagrov, M. Zakharyaschev, *Modal Logic*, Thm 1.4.3 (deduction theorem),
  Thm 1.16 / 2.43 (set-derivability / strong completeness).
