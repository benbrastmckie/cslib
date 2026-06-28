# Research Report: Deduction Theorem — Weakest-Logic Converse (Task 351)

**Date:** 2026-06-26
**Agent:** cslib-research-agent
**Scope:** Prove the *converse* of the deduction theorem characterization — that an axiom
class bundling Modus Ponens + the Deduction Theorem property derives the K and S axioms, hence
instances `MinimalHilbert` (IPL⟨→,⊤⟩), the weakest logic admitting deduction. Plus decouple the
generic `DerivationSystem`/`HasDeductionTheorem` layer from `[HasBot F]`.

All line/name references below were verified against current source. **The mathematical heart
(§3) was verified by `lake build`: both `dt_implies_implyK` and `dt_implies_implyS` compile
cleanly against the live CSLib `DerivationSystem`/`HasDeductionTheorem` definitions.**

---

## 0. Executive Summary

1. **The converse is real and currently absent.** Every existing
   `deductionTheorem`/`hasDeductionTheorem`/`algebraic_has_deduction_theorem` consumes K and S
   (via `MinimalHilbert`, or via explicit `h_implyK`/`h_implyS` witnesses) to *prove* deduction.
   No declaration derives K or S *from* deduction. Confirmed by repo-wide grep — no `weakest`/
   `characteriz` result exists for the deduction theorem.

2. **The mathematical heart is short, ⊥-free, and verified.** From only `D.assumption`
   (reflection), `D.mp`, and `hdt : HasDeductionTheorem D`, the K axiom needs **2** `hdt`
   applications and the S axiom needs **3** `hdt` applications plus 3 `D.mp`. Both compile
   today against `Cslib/Foundations/Logic/Metalogic/Consistency.lean`. Full proof terms in §3.

3. **`DerivationSystem` and `HasDeductionTheorem` carry a spurious `[HasBot F]`.** Verified:
   neither uses `⊥`. `DerivationSystem F` *fails to elaborate* with only `[HasImp F]` in scope
   (probe in §5), proving the dependency is forced solely by the structure signature + the
   file-level `variable {F} [HasBot F] [HasImp F]` block (Consistency.lean:44). The consistency
   machinery (`Consistent`, `SetConsistent`, `set_lindenbaum`, the three closure properties)
   genuinely needs `⊥` and stays put.

4. **Precedent for a ⊥-free class already exists.** `HasHilbertTree` (DeductionHelpers.lean:61)
   is declared `class HasHilbertTree (F : Type*) [HasImp F]` — **no `HasBot`** — and bundles
   exactly `Tree/implyK/implyS/assumption/mp/weakening`. `ImpAxiom` (FragmentAxioms.lean:84) is
   the ⊥-free *axiom-schema* precedent. The new converse class is "`HasHilbertTree` minus the
   `implyK`/`implyS` fields plus a `deduction` field" — and the converse then proves
   `HasDeductionTree → HasHilbertTree`.

5. **"Instances `MinimalHilbert`" needs one thin bridge.** `MinimalHilbert` is keyed on a
   *type* `S` with `[InferenceSystem S F]`, and its three components (`ModusPonens`,
   `HasAxiomImplyK`, `HasAxiomImplyS`) are all phrased via `InferenceSystem.DerivableIn S`
   (= `Nonempty (S⇓·)`, **empty-context** theoremhood; InferenceSystem.lean:65). The converse
   naturally lives at the *context-based* `DerivationSystem` level. To literally produce a
   `MinimalHilbert` instance you wrap a DT-system's empty-context derivations as an
   `InferenceSystem` (≈10 lines). Two presentation options in §6.

6. **Recommended home:** a new file
   `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean`, with the
   `Consistency.lean` `variable`-block split done as a small in-place refactor. See §6–§7.

---

## 1. The K/S/MP core at `ProofSystem.lean:342` (verified against source)

`MinimalHilbert` (Cslib/Foundations/Logic/ProofSystem.lean:342):

```lean
class MinimalHilbert (S : Type*) [HasBot F] [HasImp F]
    [InferenceSystem S F]
    extends ModusPonens S (F := F),
            HasAxiomImplyK S (F := F),
            HasAxiomImplyS S (F := F)
```

Components (all in `ProofSystem.lean`, `variable (S : Type*) [HasBot F] [HasImp F]
[InferenceSystem S F]`):

| Component | Line | Statement |
|-----------|------|-----------|
| `ModusPonens.mp` | 74 | `DerivableIn S (φ → ψ) → DerivableIn S φ → DerivableIn S ψ` |
| `HasAxiomImplyK.implyK` | 116 | `DerivableIn S (Axioms.ImplyK φ ψ)` |
| `HasAxiomImplyS.implyS` | 120 | `DerivableIn S (Axioms.ImplyS φ ψ χ)` |

Axiom schemas (`Cslib/Foundations/Logic/Axioms.lean`, `namespace Cslib.Logic.Axioms`,
`variable [HasBot F] [HasImp F]`):

```lean
protected abbrev ImplyK (φ ψ : F) : F := φ → (ψ → φ)                              -- :76
protected abbrev ImplyS (φ ψ χ : F) : F :=                                        -- :80
  (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
```
(Both are `protected abbrev`; refer to them as `Axioms.ImplyK`/`Axioms.ImplyS`.) Note: these
abbreviations are declared under `[HasBot F]` (the whole `Propositional` section is), but their
*bodies* use only `HasImp.imp` — `⊥` is incidental, not load-bearing. EFQ/Peirce sit in the
same section and *do* use `⊥`.

`MinimalHilbert` is keyed on a **type** `S`, not a predicate (cf. task 350 §5 blocker for
Modal/Propositional). For the converse this is fine: we control the system we instance.

---

## 2. The forward direction and how it consumes K/S

There are two forward layers; both consume K and S, neither derives them.

### 2.1 Generic algebraic layer (the one the converse pairs with)

`ListDeriv Γ φ := InferenceSystem.DerivableIn S (listImp Γ φ)` (ListDeduction.lean:47), under
`variable {F} [HasBot F] [HasImp F]`, `{S} [InferenceSystem S F]`, `[MinimalHilbert S]`
(ListDeduction.lean:38–40).

`list_deduction_theorem` (ListDeduction.lean:55):
```lean
theorem list_deduction_theorem (φ ψ : F) (Γ : List F) :
    ListDeriv (S := S) (φ :: Γ) ψ ↔ ListDeriv (S := S) Γ (HasImp.imp φ ψ) := by
  unfold ListDeriv; constructor
  · intro h; exact ModusPonens.mp (list_flip_implication1 φ ψ Γ) h
  · intro h; exact ModusPonens.mp (list_flip_implication2 φ ψ Γ) h
```
The `list_flip_implication1/2` flip lemmas (in `ListImplication.lean`) are built from
`listImp_axiom_k`/`listImp_axiom_s`, which bottom out at `HasAxiomImplyK.implyK` /
`HasAxiomImplyS.implyS` — i.e. **K and S are inputs**. `list_deriv_reflection`
(ListDeduction.lean:68) and `list_deriv_mp` (ListDeduction.lean:89) likewise consume K/S.

`algebraic_has_deduction_theorem` (GenericMCS.lean:65) packages this:
```lean
theorem algebraic_has_deduction_theorem :
    HasDeductionTheorem (algebraicDerivationSystem (S := S) (F := F)) := by
  intro Γ φ ψ h; exact (list_deduction_theorem φ ψ Γ).mp h
```
where `algebraicDerivationSystem : DerivationSystem F` (GenericMCS.lean:54) wires `ListDeriv`'s
monotonic/reflection/mp into a `DerivationSystem`. This is the **MinimalHilbert ⇒ DT** arrow.

### 2.2 Per-logic tree layer (explicit `h_implyK`/`h_implyS` witnesses)

The four hand `deductionTheorem` defs (PL/Modal/Temporal/Bimodal — see task 350 report §2)
and the `HasHilbertTree` helpers (DeductionHelpers.lean) take K/S **as given fields/arguments**
(`HasHilbertTree.implyK`/`.implyS`, lines 65–69) and use them in `deductionImpSelf` (S,K,K),
`deductionAssumptionOther` (K), `deductionMpUnderImp` (S). Again K/S are inputs.

**Conclusion:** in every direction currently present, K and S flow *in*. Task 351 reverses one
arrow: K, S flow *out* of DT + MP.

---

## 3. The mathematical heart — deriving K and S from DT + MP (VERIFIED)

Stated at the `DerivationSystem` level: given `D : DerivationSystem F` and
`hdt : HasDeductionTheorem D`, derive K and S as empty-context derivations. Uses only
`D.assumption`, `D.mp`, `hdt`. **No weakening, no `⊥`.** The following compiles
(`lake build` clean) against `Consistency.lean` + `Axioms.lean`:

```lean
variable {F : Type*} [HasBot F] [HasImp F]   -- HasBot only because DerivationSystem demands it today

theorem dt_implies_implyK (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
    (A B : F) : D.Deriv [] (Axioms.ImplyK A B) := by
  have h1 : D.Deriv [B, A] A := D.assumption (by simp)          -- A ∈ [B, A]
  have h2 : D.Deriv [A] (HasImp.imp B A) := hdt h1              -- strip B
  exact hdt h2                                                  -- strip A : ⊢ A → (B → A)

theorem dt_implies_implyS (D : DerivationSystem F) (hdt : HasDeductionTheorem D)
    (A B C : F) : D.Deriv [] (Axioms.ImplyS A B C) := by
  set p := HasImp.imp A (HasImp.imp B C)                        -- A → (B → C)
  set q := HasImp.imp A B                                       -- A → B
  have hA  : D.Deriv [A, q, p] A := D.assumption (by simp)
  have hqd : D.Deriv [A, q, p] q := D.assumption (by simp)
  have hpd : D.Deriv [A, q, p] p := D.assumption (by simp)
  have hB  : D.Deriv [A, q, p] B := D.mp hqd hA                 -- B   from (A→B), A
  have hBC : D.Deriv [A, q, p] (HasImp.imp B C) := D.mp hpd hA  -- B→C from (A→(B→C)), A
  have hC  : D.Deriv [A, q, p] C := D.mp hBC hB                 -- C
  have s3  : D.Deriv [q, p] (HasImp.imp A C) := hdt hC          -- strip A
  have s2  : D.Deriv [p] (HasImp.imp q (HasImp.imp A C)) := hdt s3   -- strip q
  exact hdt s2                                                  -- strip p : the S axiom
```

Why it works: `HasDeductionTheorem D` (Consistency.lean:182) strips the **head** of the
context (`D.Deriv (φ :: Γ) ψ → D.Deriv Γ (φ → ψ)`). So building the context in the order the
antecedents will appear, then peeling off with `hdt`, reconstructs nested implications. K is the
"weakening" pattern (conclude `A` ignoring `B`); S is the "distribution" pattern (use both
hypotheses on the shared `A`). This is the standard Hilbert-Bernays argument — exactly the
content Doty refers to as making IPL⟨→,⊤⟩ the weakest logic with the deduction theorem.

These derivations transfer verbatim to a ⊥-free system: replace `D.Deriv` by the new class's
context-derivability; nothing references `⊥`.

---

## 4. The new axiom class bundling MP + DT property + reflection

The class is "a context-derivability with reflection, MP, weakening, and deduction" — i.e.
**`HasHilbertTree` with the `implyK`/`implyS` fields removed and a `deduction` field added.**
Two faithful encodings:

### 4.1 Prop-valued (recommended; reuses existing `DerivationSystem`)

After the §5 decoupling, `DerivationSystem` is `[HasImp F]`-only and already supplies
`assumption`, `mp`, `weakening`. A DT system is then simply the pair
`(D : DerivationSystem F) (hdt : HasDeductionTheorem D)` — *no new class needed* for the
mathematical content. If a bundled typeclass is desired for instance resolution:

```lean
/-- A purely-implicational system with modus ponens, reflection (assumption),
weakening, and the deduction theorem. The weakest setting deriving K and S. -/
class HasDeductionSystem (F : Type*) [HasImp F] where
  Deriv : List F → F → Prop
  assumption : ∀ {Γ φ}, φ ∈ Γ → Deriv Γ φ
  mp : ∀ {Γ φ ψ}, Deriv Γ (HasImp.imp φ ψ) → Deriv Γ φ → Deriv Γ ψ
  weakening : ∀ {Γ Δ φ}, Deriv Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Deriv Δ φ
  deduction : ∀ {Γ φ ψ}, Deriv (φ :: Γ) ψ → Deriv Γ (HasImp.imp φ ψ)
```
(`weakening` is not needed for K/S but belongs to the abstraction and is used by the
`closed_under_derivation` machinery; keep it for parity with `DerivationSystem`.)

### 4.2 Type-valued (mirrors `HasHilbertTree`, gives a clean subsumption)

```lean
class HasDeductionTree (F : Type*) [HasImp F] where
  Tree : List F → F → Type*
  assumption : {Γ : List F} → {φ : F} → φ ∈ Γ → Tree Γ φ
  mp : {Γ : List F} → {φ ψ : F} → Tree Γ (HasImp.imp φ ψ) → Tree Γ φ → Tree Γ ψ
  weakening : {Γ Δ : List F} → {φ : F} → Tree Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Tree Δ φ
  deduction : {Γ : List F} → {φ ψ : F} → Tree (φ :: Γ) ψ → Tree Γ (HasImp.imp φ ψ)
```
Then the converse is exactly `instance : HasHilbertTree F` (DeductionHelpers.lean:61), whose
`implyK`/`implyS` fields are produced by the §3 derivations (type-valued versions). This is the
most reuse-faithful statement of "DT+MP instances the implicational Hilbert core": it lands
directly on the existing ⊥-free tree class.

**Recommendation:** primary deliverable in the **Prop-valued** form (4.1), because it plugs
straight into `algebraic_has_deduction_theorem` and the existing `Consistency` closure lemmas,
and because the K/S derivations are already verified there (§3). Optionally also provide the
`HasDeductionTree → HasHilbertTree` instance (4.2) as the tree-level corollary.

---

## 5. The `[HasBot F]` decoupling (verified)

### 5.1 What is genuinely implicational vs. needs `⊥`, in `Consistency.lean`

File-level block: `variable {F : Type*} [HasBot F] [HasImp F]` (Consistency.lean:44).

| Declaration | Line | Uses `⊥`? | Verdict |
|-------------|------|-----------|---------|
| `DerivationSystem` (structure) | 55 | **No** (`Deriv`/`weakening`/`assumption`/`mp`; only `mp` uses `imp`) | ⊥-free — but signature forces `[HasBot F]` |
| `Consistent` | 68 | Yes (`HasBot.bot`) | needs `⊥` |
| `SetConsistent`, `SetMaximalConsistent`, `ConsistentSupersets` | 72,77,82 | Yes (via `Consistent`) | needs `⊥` |
| `set_consistent_not_both` | 86 | Yes | needs `⊥` |
| `finite_list_in_chain_member`, `consistent_chain_union` | 110,137 | Yes (consistency) | needs `⊥` |
| `set_lindenbaum` | 152 | Yes | needs `⊥` |
| **`HasDeductionTheorem`** | **182** | **No** (only `HasImp.imp`) | **⊥-free — the decoupling target** |
| `derives_from_insert_to_cons` | 188 | No directly, but tied to MCS | stays with consistency |
| `closed_under_derivation`, `implication_property`, `negation_complete` | 213,246,264 | Yes (`⊥`/negation) | needs `⊥` |

So **exactly `DerivationSystem` (the structure) and `HasDeductionTheorem`** are the
purely-implicational items currently trapped under `[HasBot F]`.

### 5.2 Proof that the dependency is spurious (verified by build)

Probe (built in-repo): with `variable {F : Type*} [HasImp F]` only,
`#check (DerivationSystem F)` and `#check fun (D : DerivationSystem F) => HasDeductionTheorem D`
**fail** with "failed to synthesize instance" — confirming the only thing demanding `HasBot` is
`DerivationSystem`'s signature `structure DerivationSystem (F) [HasBot F] [HasImp F]`. Drop that
`[HasBot F]` and the implicational core is free.

### 5.3 Precedent for the ⊥-free class

- **`HasHilbertTree`** (DeductionHelpers.lean:61): `class HasHilbertTree (F : Type*) [HasImp F]`
  — already ⊥-free, same `assumption/mp/weakening` shape; the model to mirror.
- **`ImpAxiom`** (FragmentAxioms.lean:84): the ⊥-free *axiom schema* for IPL⟨→,⊤⟩ (just
  `implyK`/`implyS` constructors), with subsumption `ImpAxiom.toConjImpAxiom` (:95). This is the
  concrete IPL⟨→,⊤⟩ object the characterization is *about*.

### 5.4 Refactor shape and blast radius

In `Consistency.lean`, split the `variable` block so `DerivationSystem` and
`HasDeductionTheorem` are emitted under `[HasImp F]` only, and re-introduce `[HasBot F]` (a
fresh `variable` line) immediately before `Consistent` (line 68 onward). Drop `[HasBot F]` from
the `DerivationSystem` structure signature.

Blast radius: `DerivationSystem` is referenced in **33** files, `HasDeductionTheorem` in **30**
occurrences. The change is *widening* (removing a constraint), so all existing call sites — which
already have `[HasBot F]` in scope — continue to elaborate. No downstream signature needs `⊥`
*added*. Risk is low but the full `lake build` must confirm (the structure-signature edit is the
only one that could ripple). This is a "generalize in place" refactor, not a rewrite.

Alternative (lower-risk, less reuse): leave `Consistency.lean` untouched and put the new ⊥-free
class + converse entirely in the new file (§6), phrased against `HasDeductionSystem`/
`HasDeductionTree` rather than `DerivationSystem`. Trade-off: a second parallel abstraction
instead of generalizing the canonical one. **Recommend the in-place generalization** (reuse-first),
with the alternative as fallback if the build surfaces unexpected coupling.

---

## 6. Where the characterization theorem should live

**New file:** `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean`.

Imports: `Consistency` (DerivationSystem, HasDeductionTheorem, closure props), `GenericMCS`
(algebraicDerivationSystem, algebraic_has_deduction_theorem), `ListDeduction` + `ProofSystem`
(MinimalHilbert), `Axioms` (ImplyK/ImplyS).

Contents:
1. `dt_implies_implyK`, `dt_implies_implyS` (§3) — the converse heart.
2. (Optional, type-valued) `instance HasDeductionTree → HasHilbertTree` (§4.2).
3. The **MinimalHilbert-instancing bridge.** `MinimalHilbert` needs an `[InferenceSystem S F]`
   whose `DerivableIn` is empty-context theoremhood. Wrap a DT system:

   ```lean
   /-- Empty-context theoremhood of a deduction system as an inference system. -/
   def dtInferenceSystem (D : DerivationSystem F) : InferenceSystem ? F := ...
   --   derivation φ := PLift (D.Deriv [] φ)        -- DerivableIn ↔ D.Deriv []
   ```
   Then, given `hdt`:
   - `ModusPonens` ← `D.mp` at `[]`;
   - `HasAxiomImplyK.implyK` ← `dt_implies_implyK`;
   - `HasAxiomImplyS.implyS` ← `dt_implies_implyS`;
   - hence `instance : MinimalHilbert _`.

   This wrapper is the small piece of new infra needed to read the converse as literally
   "instances `MinimalHilbert`". (It is the dual of `algebraicDerivationSystem`, which goes
   `MinimalHilbert → DerivationSystem`.)
4. The **equivalence/characterization** statement, e.g.:

   ```lean
   /-- IPL⟨→,⊤⟩ characterization: a system admits the deduction theorem iff it proves K and S
   (with MP + reflection). Forward = algebraic_has_deduction_theorem; converse = dt_implies_*. -/
   theorem deduction_theorem_iff_minimal_hilbert ... 
   ```
   Forward arrow reuses `algebraic_has_deduction_theorem` (GenericMCS.lean:65); converse is the
   new `dt_implies_implyK`/`dt_implies_implyS`. Phrase the "weakest logic" claim as: any
   `HasDeductionSystem`/`DerivationSystem`-with-`hdt` yields a `MinimalHilbert` instance (via
   the §6.3 bridge), and `MinimalHilbert` yields `HasDeductionTheorem` (via the algebraic
   system) — closing the loop.

Rationale for a new file (vs. appending to `Consistency.lean` or `GenericMCS.lean`): keeps the
converse + bridge + InferenceSystem wrapper isolated, avoids enlarging the high-traffic
`Consistency.lean`, and matches CSLib's one-concept-per-file `Metalogic/` layout
(ListDeduction / SetDeduction / GenericMCS / MCSProperties / DeductionHelpers).

---

## 7. Zero-debt / no-sorry assessment

- **§3 K/S derivations are verified sorry-free** (built in-repo). They use no choice, no `⊥`,
  no axioms — pure `assumption`/`mp`/`hdt`.
- The MinimalHilbert bridge (§6.3) uses only `PLift`/`Nonempty` plumbing and the verified K/S
  theorems; no `sorry`, no new `axiom`. (`DerivableIn` is already `Nonempty`-based;
  `algebraic_has_deduction_theorem` is the existing dual, also sorry-free.)
- The `[HasBot F]` decoupling is a constraint-*removal* refactor; it cannot introduce `sorry`
  and cannot strengthen any obligation. Only risk is a build ripple from the structure-signature
  edit, mitigated by a full `lake build`.
- **No `sorry` deferral, no new axiom, no vacuous definitions are needed or permitted.** If the
  MinimalHilbert bridge proves awkward in Lean's instance resolution, the fallback is to ship the
  converse as explicit theorems (`dt_implies_implyK/S`) + the `HasDeductionTree → HasHilbertTree`
  instance and state the characterization without the typeclass instance — still a complete,
  sorry-free converse. Decompose rather than defer.

---

## 8. CI / verification checklist (from the task)

After implementation, run (cslib order):
- `lake build` (full — required because the `DerivationSystem` signature edit is library-wide)
- `lake exe checkInitImports` (new file must `import Cslib.Init`)
- `lake exe lint-style`
- `lake test`
- `lake exe mk_all --module` (new file → update `Cslib.lean` barrel)
- `lake shake --add-public --keep-implied --keep-prefix`

Lint-prevention notes for the new declarations: docstrings on every decl (docBlame);
`dt_implies_implyK`/`...S` and the characterization are `Prop`-valued → use `theorem`
(defLemma); lowerCamelCase, no underscores in *def* names (the `dt_implies_*` names use
underscores — acceptable for `theorem`s, but prefer `dtImpliesImplyK`-style only if a `def`;
for theorems snake_case matches existing `list_deduction_theorem` convention, so keep
snake_case to match the file's neighbors); wrap instances in their namespace (topNamespace).

---

## 9. Verified reference table

| Symbol | File:line | Note |
|--------|-----------|------|
| `MinimalHilbert` | `Foundations/Logic/ProofSystem.lean:342` | K+S+MP, keyed on type `S` |
| `ModusPonens.mp` | `ProofSystem.lean:74` | over `DerivableIn` |
| `HasAxiomImplyK.implyK` | `ProofSystem.lean:116` | `DerivableIn (Axioms.ImplyK φ ψ)` |
| `HasAxiomImplyS.implyS` | `ProofSystem.lean:120` | `DerivableIn (Axioms.ImplyS φ ψ χ)` |
| `Axioms.ImplyK` | `Foundations/Logic/Axioms.lean:76` | `φ → (ψ → φ)`, protected abbrev |
| `Axioms.ImplyS` | `Axioms.lean:80` | `(φ→(ψ→χ))→((φ→ψ)→(φ→χ))` |
| `ListDeriv` | `Metalogic/ListDeduction.lean:47` | `DerivableIn (listImp Γ φ)` |
| `list_deduction_theorem` | `ListDeduction.lean:55` | forward; consumes K/S via flip lemmas |
| `list_deriv_reflection` | `ListDeduction.lean:68` | reflection (assumption) |
| `list_deriv_mp` | `ListDeduction.lean:89` | contextual MP |
| `DerivationSystem` | `Metalogic/Consistency.lean:55` | ⊥-free content; sig forces `[HasBot F]` |
| `HasDeductionTheorem` | `Consistency.lean:182` | **⊥-free; decoupling target** |
| `SetMaximalConsistent.closed_under_derivation` | `Consistency.lean:213` | needs `⊥` |
| `...implication_property` / `...negation_complete` | `Consistency.lean:246/264` | need `⊥` |
| `set_lindenbaum` | `Consistency.lean:152` | needs `⊥` |
| `algebraicDerivationSystem` | `Metalogic/GenericMCS.lean:54` | MinimalHilbert → DerivationSystem |
| `algebraic_has_deduction_theorem` | `GenericMCS.lean:65` | **forward arrow** (MinimalHilbert ⇒ DT) |
| `HasHilbertTree` | `Metalogic/DeductionHelpers.lean:61` | ⊥-free `[HasImp F]` class — precedent/target |
| `deductionImpSelf`/`deductionMpUnderImp` | `DeductionHelpers.lean:92/111` | consume K/S (forward) |
| `ImpAxiom` | `Logics/Propositional/ProofSystem/FragmentAxioms.lean:84` | ⊥-free IPL⟨→,⊤⟩ schema |
| `ImpAxiom.toConjImpAxiom` | `FragmentAxioms.lean:95` | subsumption |
| `InferenceSystem.DerivableIn` | `Foundations/Logic/InferenceSystem.lean:65` | `Nonempty (S⇓a)`, empty-context |

---

## 10. Recommended implementation order (for the planner)

1. **Decouple** (Consistency.lean): split the `variable` block; drop `[HasBot F]` from the
   `DerivationSystem` structure. Full `lake build` to confirm no ripple. *(constraint removal)*
2. **Converse heart** (new `DeductionCharacterization.lean`): `dt_implies_implyK`,
   `dt_implies_implyS` — already verified (§3). *(the mathematical core)*
3. **New ⊥-free class** (§4): `HasDeductionSystem` (Prop) and/or `HasDeductionTree` (Type), with
   the `HasDeductionTree → HasHilbertTree` instance as a reuse corollary.
4. **MinimalHilbert bridge** (§6.3): `dtInferenceSystem` wrapper + `MinimalHilbert` instance.
5. **Characterization theorem** (§6.4): combine the new converse with
   `algebraic_has_deduction_theorem` into the IPL⟨→,⊤⟩-weakest-logic equivalence.
6. **CI** (§8), update `Cslib.lean` via `mk_all`.

Relation to siblings: builds on task 350's generic layer (forward direction intact); task 345
(MinimalAxioms/IsMinimal) may interact with how the characterization is phrased — coordinate
naming if 345 lands first.
