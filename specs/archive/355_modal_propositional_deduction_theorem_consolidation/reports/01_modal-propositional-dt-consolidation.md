# Research Report: Modal & Propositional Deduction Theorem Consolidation (Task 355)

**Date:** 2026-06-27
**Agent:** cslib-research-agent
**Session:** sess_1782560395_aeb7ef_355
**Scope:** Complete the consolidation begun in task 350. Route the **Modal** and
**Propositional** `deductionTheorem` defs through the generic algebraic deduction-theorem
layer, building the missing `predicate → InferenceSystem` infrastructure (`HilbertOf` wrapper)
that task 350 deferred. Zero technical debt; signature-preserving; ~25 raw call sites must
keep compiling.

---

## 0. Executive Summary

1. **This is the deferred "Phase M/P" of task 350.** Task 350 fully consolidated Temporal and
   Bimodal (fixed systems `HilbertBX`/`HilbertTM` with pre-existing `InferenceSystem` +
   `MinimalHilbert` instances). Modal/Propositional were deferred because their
   `deductionTheorem` is polymorphic over a predicate `Axioms : Proposition Atom → Prop`, and
   `algebraicDerivationSystem` is keyed on a **type** `S` with `[InferenceSystem S F]
   [MinimalHilbert S]`. The bridge therefore requires a new wrapper turning a predicate into a
   tag type. The wrapper design is already named and sketched in the Modal doc-only bridge
   (`Modal/Metalogic/GenericMCSBridge.lean:46-55`).

2. **The single new abstraction needed:** a tag type `HilbertOf Axioms` whose
   `InferenceSystem.derivation φ := DerivationTree Axioms [] φ`, plus a predicate-level class
   `HasMinimalAxioms Axioms` (carrying the `implyK`/`implyS` witnesses) from which the
   `MinimalHilbert (HilbertOf Axioms)` instance is synthesised. Everything else is a
   line-for-line transcription of the Temporal/Bimodal bridge (`deriv_tree_to_list`,
   `unfold_listImp_in_tree`, `list_deriv_to_tree`, `*_deriv_iff_algebraic`).

3. **The re-routed `deductionTheorem` body is 3 lines** (the exact Temporal template,
   `Temporal/Metalogic/DeductionTheorem.lean:69-71`), wrapped with one `haveI` to install the
   `HasMinimalAxioms` instance from the existing `h_implyK`/`h_implyS` hypotheses. Signatures
   are preserved verbatim, so all ~25 raw `DerivationTree` consumers keep compiling.

4. **`deductionWithMem` is deleted** in both logics (Modal `:50`, PL `:71`), along with the
   WF-recursion bodies and the `letI : HasHilbertTree …` blocks. No `deductionWithMem` call
   sites exist outside the two defining files (verified — see §6).

5. **Zero new sorry, zero new axioms.** The only classical content is `Nonempty.some` /
   `DerivableIn.toDerivation` (`Classical.choice`), already present in the temporal/bimodal
   consolidation and acceptable on these already-`noncomputable` defs.

6. **PL is strictly simpler than Modal:** the PL `DerivationTree` has only 4 constructors (no
   `necessitation`), so the PL forward bridge drops the `necessitation` case entirely. Modal
   has 5 constructors (adds `necessitation`), handled exactly as Temporal handles
   `temporal_necessitation` (reconstruct at empty context).

---

## 1. Verified template assets (from task 350)

All four are confirmed present and are the literal templates for this task.

| Asset | File:line | Role |
|-------|-----------|------|
| `temporalAlgDS` / `bimodalAlgDS` | `Temporal/.../GenericMCSBridge.lean:68`, `Bimodal/.../Core/GenericMCSBridge.lean:79` | `@algebraicDerivationSystem F _ _ S _ _` shorthand |
| `deriv_tree_to_list` (forward) | `Temporal:82`, `Bimodal:94` | structural induction on tree |
| `unfold_listImp_in_tree` (backward helper) | `Temporal:137`, `Bimodal:161` | peel `listImp` via assumptions |
| `list_deriv_to_tree` (backward) | `Temporal:163`, `Bimodal:187` | weaken `[]→Γ`, then unfold |
| `*_deriv_iff_algebraic` | `Temporal:184`, `Bimodal:206` | the pointwise equivalence |
| `*_setConsistent_iff_algebraic` / `*_setMaxConsistent_iff_algebraic` | `Temporal:198/210`, `Bimodal:220/232` | MCS equivalences |
| re-routed `deductionTheorem` (3-line body) | `Temporal/Metalogic/DeductionTheorem.lean:66-71` | **the body template** |
| re-routed `*_has_deduction_theorem` | `Temporal:76-81` | wrapper template |

The Bimodal bridge (`Bimodal/.../Core/GenericMCSBridge.lean`) is the closest template because
it was authored fresh in task 350 (the Temporal one predated it). Its "Design Note"
(lines 49-54) documents the no-cycle discipline: **the bridge file must NOT import
`DeductionTheorem.lean`**; it derives the equivalence purely from the `InferenceSystem` +
`MinimalHilbert` instances.

---

## 2. Verified generic layer (Foundations)

| Symbol | File:line | Signature (verified) |
|--------|-----------|----------------------|
| `InferenceSystem` | `Foundations/Logic/InferenceSystem.lean:42` | `class InferenceSystem (S α : Type*) where derivation (a : α) : Sort v` |
| `InferenceSystem.DerivableIn` | `…/InferenceSystem.lean:65` | `DerivableIn S a := Nonempty (S⇓a)` |
| `DerivableIn.toDerivation` | `…/InferenceSystem.lean:78` | `noncomputable, Classical.choice` |
| `ModusPonens` | `Foundations/Logic/ProofSystem.lean:74` | `mp : DerivableIn S (imp φ ψ) → DerivableIn S φ → DerivableIn S ψ` |
| `HasAxiomImplyK` | `…/ProofSystem.lean:116` | `implyK : DerivableIn S (Axioms.ImplyK φ ψ)` |
| `HasAxiomImplyS` | `…/ProofSystem.lean:120` | `implyS : DerivableIn S (Axioms.ImplyS φ ψ χ)` |
| `MinimalHilbert` | `…/ProofSystem.lean:342` | `extends ModusPonens S, HasAxiomImplyK S, HasAxiomImplyS S` |
| `Axioms.ImplyK` | `Foundations/Logic/Axioms.lean:76` | `imp φ (imp ψ φ)` |
| `Axioms.ImplyS` | `…/Axioms.lean:80` | `imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ))` |
| `algebraicDerivationSystem` | `Foundations/Logic/Metalogic/GenericMCS.lean:54` | needs `[InferenceSystem S F] [MinimalHilbert S]` |
| `algebraic_has_deduction_theorem` | `…/GenericMCS.lean:65` | `HasDeductionTheorem (algebraicDerivationSystem (S := S))` |
| `HasDeductionTheorem` | `…/Consistency.lean:187` | `∀ {Γ φ ψ}, D.Deriv (φ::Γ) ψ → D.Deriv Γ (imp φ ψ)` (Γ/φ/ψ **implicit**) |

Key fact: `algebraicDerivationSystem`'s *signature* requires `[MinimalHilbert S]` (file-level
`variable`, `GenericMCS.lean:37-39`), even though its body only uses `ListDeriv` lemmas.
Therefore the wrapper must supply a `MinimalHilbert (HilbertOf Axioms)` instance to even
*form* `algebraicDerivationSystem (S := HilbertOf Axioms)`.

`HasDeductionTheorem` has **implicit** `Γ φ ψ`, which is why the temporal body applies
`algebraic_has_deduction_theorem (… .mp ⟨d⟩)` with no positional arguments.

---

## 3. Verified target files (current hand-proof state)

### 3.1 Modal — `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean`
- `deductionWithMem` (def) — line **50** — DELETE.
- `deductionTheorem` (def) — line **109** — RE-IMPLEMENT (signature preserved).
- `hasDeductionTheorem` (theorem) — line **177** — RE-PROVE via bridge.
- Parameterized over `{Axioms : Proposition Atom → Prop}` + `h_implyK`/`h_implyS`.
- `modalDerivationSystem Axioms` def at `Modal/Metalogic/DerivationTree.lean:198`;
  `Modal.Deriv Axioms Γ φ := Nonempty (DerivationTree Axioms Γ φ)` (`DerivationTree.lean:159`).
- Modal `DerivationTree` constructors (`DerivationTree.lean:98`): `ax`, `assumption`,
  `modus_ponens`, **`necessitation`** (empty-context only), `weakening` — **5 constructors**.

### 3.2 Propositional — `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`
- A file-local `HasHilbertTree` instance fixed at `PropositionalAxiom` — line **56** —
  DELETE (only used by the WF bodies).
- `deductionWithMem` (def) — line **71** — DELETE.
- `deductionTheorem` (def) — line **130** — RE-IMPLEMENT (signature preserved).
- `hasDeductionTheorem` (theorem) — line **198** — RE-PROVE via bridge.
- `propDerivationSystem Axioms` def at `Propositional/ProofSystem/Derivation.lean:157`;
  `PL.Deriv Axioms Γ φ := Nonempty (DerivationTree Axioms Γ φ)`.
- PL `DerivationTree` constructors (`Derivation.lean:68`): `ax`, `assumption`,
  `modus_ponens`, `weakening` — **4 constructors, no necessitation**.

### 3.3 Concrete-instance template — `Modal/ProofSystem/Instances/K.lean:62-113`
This is the literal pattern the wrapper instances copy (just replacing the fixed `HilbertK`
tag and the `KAxiom` constructors with the parameterized `HilbertOf Axioms` / witness fields):
```lean
instance : InferenceSystem Modal.HilbertK (Modal.Proposition Atom) where
  derivation φ := Modal.DerivationTree (@Modal.KAxiom Atom) [] φ
instance : ModusPonens Modal.HilbertK (F := Modal.Proposition Atom) where
  mp := fun h1 h2 => by obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
                        exact ⟨Modal.DerivationTree.modus_ponens [] _ _ d1 d2⟩
instance : HasAxiomImplyK Modal.HilbertK (F := Modal.Proposition Atom) where
  implyK := ⟨Modal.DerivationTree.ax [] _ (Modal.KAxiom.implyK _ _)⟩
```
`Modal.Proposition Atom` already carries `HasBot`/`HasImp`/`HasBox` instances (confirmed: the
existing doc bridge `#check @algebraicDerivationSystem (Modal.Proposition Atom) _ _
(S := Modal.HilbertK) _` type-checks per `GenericMCSBridge.lean:67`).

---

## 4. The new infrastructure (concrete Lean sketches)

### 4.1 Predicate-level minimal-axioms class (generic, in `GenericMCS.lean`)

The task lists `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` among the files to modify.
The natural Foundations-level addition is a generic class capturing "this predicate contains
the K and S axiom schemata", stated over an arbitrary `F` with `[HasImp F]`:

```lean
namespace Cslib.Logic.Metalogic.GenericMCS

variable {F : Type*} [HasImp F]

/-- A formula predicate `Axioms` that contains the minimal Hilbert axiom schemata
`ImplyK` (`φ → ψ → φ`) and `ImplyS` (`(φ → ψ → χ) → (φ → ψ) → φ → χ`). This is the
predicate-level analogue of `MinimalHilbert`; it is what a tree-based `DerivationTree Axioms`
proof system needs in order to synthesise a `MinimalHilbert` instance on its `HilbertOf`
wrapper. -/
class HasMinimalAxioms (Axioms : F → Prop) : Prop where
  /-- `Axioms` contains every `ImplyK` instance. -/
  has_implyK : ∀ φ ψ, Axioms (Axioms.ImplyK φ ψ)
  /-- `Axioms` contains every `ImplyS` instance. -/
  has_implyS : ∀ φ ψ χ, Axioms (Axioms.ImplyS φ ψ χ)
```

Note `Axioms.ImplyK φ ψ` is defeq to `φ.imp (ψ.imp φ)` (`Axioms.lean:76`), exactly the shape
of the existing `h_implyK` hypothesis, so `⟨h_implyK, h_implyS⟩ : HasMinimalAxioms Axioms`
type-checks directly. (Lint: this is `Prop`-valued → must be `class … : Prop`; fields use
lowerCamelCase with no underscores — prefer `hasImplyK`/`hasImplyS` field names to satisfy
`defsWithUnderscore`; docstrings required by `docBlame`.)

Because `HilbertOf` (next section) is keyed on a logic-specific `DerivationTree`, the wrapper
*type* and its `InferenceSystem`/`MinimalHilbert` instances live in each logic's bridge file,
but they share this single generic `HasMinimalAxioms` class. This is the only Foundations
change; it is genuine new shared infrastructure, not a duplication.

### 4.2 The `HilbertOf` wrapper (per-logic, in each bridge file)

`HilbertOf` must reference the concrete `DerivationTree` former, and Modal's and PL's
`DerivationTree` are **distinct inductive types over distinct `Proposition` types**. So there
are two copies (Modal in `Modal/Metalogic/GenericMCSBridge.lean`, PL in the new
`Propositional/Metalogic/GenericMCSBridge.lean`). Modal version:

```lean
namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-- Tag type packaging an axiom predicate `Axioms` as an `InferenceSystem`, so that the
generic `algebraicDerivationSystem` can be instantiated at it. Uninhabited; used only as an
instance-resolution key (cf. `Modal.HilbertK : Type := Empty`). -/
inductive HilbertOf (Axioms : Proposition Atom → Prop) : Type

instance : InferenceSystem (HilbertOf Axioms) (Proposition Atom) where
  derivation φ := DerivationTree Axioms [] φ

instance : ModusPonens (HilbertOf Axioms) (F := Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨DerivationTree.modus_ponens [] _ _ d1 d2⟩

instance [Metalogic.GenericMCS.HasMinimalAxioms Axioms] :
    HasAxiomImplyK (HilbertOf Axioms) (F := Proposition Atom) where
  implyK := ⟨DerivationTree.ax [] _ (Metalogic.GenericMCS.HasMinimalAxioms.hasImplyK _ _)⟩

instance [Metalogic.GenericMCS.HasMinimalAxioms Axioms] :
    HasAxiomImplyS (HilbertOf Axioms) (F := Proposition Atom) where
  implyS := ⟨DerivationTree.ax [] _ (Metalogic.GenericMCS.HasMinimalAxioms.hasImplyS _ _ _)⟩

instance [Metalogic.GenericMCS.HasMinimalAxioms Axioms] :
    MinimalHilbert (HilbertOf Axioms) (F := Proposition Atom) where
```

Design points (all load-bearing):
- **`inductive HilbertOf … : Type` with no constructors** gives a distinct type *former*
  `HilbertOf` so instance search keys on `HilbertOf ?Axioms` and unifies `?Axioms`. A
  `def HilbertOf Axioms := Empty` would unfold to `Empty` during TC search and lose the
  parameter — **do not** use a plain `def` unless marked `irreducible`. (The fixed tags like
  `HilbertK` use `opaque … : Type := Empty`, but `opaque` cannot be parameterized, so an empty
  `inductive`/`structure` is the parameterized analogue.)
- `derivation φ := DerivationTree Axioms [] φ` makes `(HilbertOf Axioms)⇓φ` defeq to the tree,
  so `DerivableIn.toDerivation` yields a `DerivationTree Axioms [] φ` for the necessitation
  case — identical to how the temporal bridge bottoms out.
- The `MinimalHilbert` instance is **conditional on `[HasMinimalAxioms Axioms]`**; this is what
  the re-routed `deductionTheorem` supplies via `haveI` from its `h_implyK`/`h_implyS` args.

The PL version is identical with `Proposition`→`PL.Proposition` and namespace
`Cslib.Logic.PL`. PL needs `[HasBot (PL.Proposition Atom)]` and `[HasImp …]` for
`MinimalHilbert`/`algebraicDerivationSystem` — verify these instances exist (they must, since
`propDerivationSystem` and the existing PL semantics operate over `imp`/`bot`).

### 4.3 The bridge (per-logic) — transcription of Temporal/Bimodal

Modal bridge body (mirrors `Bimodal/.../Core/GenericMCSBridge.lean` exactly, minus the two
temporal constructors, plus Modal's single `necessitation` case):

```lean
/-- Algebraic system at the `HilbertOf Axioms` wrapper. -/
@[reducible] def modalAlgDS (Axioms : Proposition Atom → Prop)
    [Metalogic.GenericMCS.HasMinimalAxioms Axioms] :
    Metalogic.DerivationSystem (Proposition Atom) :=
  @algebraicDerivationSystem (Proposition Atom) _ _ (HilbertOf Axioms) _ _

noncomputable def deriv_tree_to_list
    {Axioms : Proposition Atom → Prop} [Metalogic.GenericMCS.HasMinimalAxioms Axioms]
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms Γ φ) : (modalAlgDS Axioms).Deriv Γ φ := by
  induction d with
  | ax Γ ψ h_ax =>
    have h_thm : InferenceSystem.DerivableIn (HilbertOf Axioms) ψ :=
      ⟨DerivationTree.ax [] ψ h_ax⟩
    simp only [modalAlgDS, algebraicDerivationSystem]; unfold ListDeriv
    exact ModusPonens.mp (listImp_axiom_k ψ Γ) h_thm
  | assumption Γ ψ h_mem =>
    simp only [modalAlgDS, algebraicDerivationSystem]; exact list_deriv_reflection h_mem
  | @modus_ponens Γ χ ψ _d₁ _d₂ ih₁ ih₂ =>
    simp only [modalAlgDS, algebraicDerivationSystem] at *; exact list_deriv_mp ih₁ ih₂
  | @necessitation ψ _d ih =>
    -- ih : DerivableIn (HilbertOf Axioms) ψ at empty context
    simp only [modalAlgDS, algebraicDerivationSystem] at *
    have h_thm : InferenceSystem.DerivableIn (HilbertOf Axioms) ψ := by
      unfold ListDeriv at ih; simp only [listImp_nil] at ih; exact ih
    unfold ListDeriv; simp only [listImp_nil]
    exact ⟨DerivationTree.necessitation ψ h_thm.toDerivation⟩
  | @weakening Γ' Γ ψ _d h_sub ih =>
    simp only [modalAlgDS, algebraicDerivationSystem] at *
    exact list_deriv_monotonic h_sub ih
```

`unfold_listImp_in_tree`, `list_deriv_to_tree`, `modal_deriv_iff_algebraic`,
`modal_setConsistent_iff_algebraic`, `modal_setMaxConsistent_iff_algebraic` are copied
verbatim from the Bimodal file with the obvious renames. The `axiom`-case constructor is named
`ax` in Modal/PL (Bimodal/Temporal use `«axiom»`); adjust the `induction … with` arm name.

The `necessitation` constructor's premise/conclusion are at empty context
(`DerivationTree Axioms [] φ → DerivationTree Axioms [] (box φ)`), so the case reconstructs
`⟨DerivationTree.necessitation ψ h_thm.toDerivation⟩` exactly as Temporal handles
`temporal_necessitation` (`Temporal/.../GenericMCSBridge.lean:101-112`).

**PL bridge** drops the `necessitation` arm entirely (4-constructor `induction`), giving a
strictly smaller file than the temporal template.

Helper lemmas reused (verified present, used by the temporal/bimodal bridges):
`listImp_axiom_k`, `list_deriv_reflection`, `list_deriv_mp`, `list_deriv_monotonic`,
`listImp_nil`, `listImp_cons` (namespaces `Cslib.Logic.Metalogic.ListImplication` /
`…ListDeduction`), opened as in the bimodal bridge header.

### 4.4 Re-routed `deductionTheorem` (signature preserved)

Modal (`Modal/Metalogic/DeductionTheorem.lean`, replacing lines 50-187):

```lean
noncomputable def deductionTheorem
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (Γ : List (Proposition Atom)) (A B : Proposition Atom)
    (d : DerivationTree Axioms (A :: Γ) B) :
    DerivationTree Axioms Γ (A → B) :=
  haveI : Metalogic.GenericMCS.HasMinimalAxioms Axioms := ⟨h_implyK, h_implyS⟩
  (modal_deriv_iff_algebraic.mpr
    (algebraic_has_deduction_theorem
      (modal_deriv_iff_algebraic.mp ⟨d⟩))).some

theorem hasDeductionTheorem
    {Axioms : Proposition Atom → Prop}
    (h_implyK : …) (h_implyS : …) :
    Metalogic.HasDeductionTheorem (modalDerivationSystem Axioms) := by
  haveI : Metalogic.GenericMCS.HasMinimalAxioms Axioms := ⟨h_implyK, h_implyS⟩
  intro Γ φ ψ h
  exact modal_deriv_iff_algebraic.mpr
    (algebraic_has_deduction_theorem (modal_deriv_iff_algebraic.mp h))
```

- `⟨d⟩ : modalDerivationSystem Axioms |>.Deriv (A::Γ) B` (defeq `Nonempty (DerivationTree …)`).
- `.some` extracts the tree from the `Nonempty` result (`Nonempty.some`, `Classical.choice`);
  identical to the temporal body's final `.some` (`Temporal/…/DeductionTheorem.lean:71`).
- `algebraic_has_deduction_theorem` infers `S := HilbertOf Axioms` from `modalAlgDS` (a
  `@[reducible]` alias). **Verification point:** if elaboration fails to unify, annotate
  `algebraic_has_deduction_theorem (S := HilbertOf Axioms)`.
- The new body uses **neither** `removeAll` **nor** `Classical.propDecidable`, so the
  file-local `attribute [local instance] Classical.propDecidable` and the `ListHelpers` /
  `DeductionHelpers` imports can be dropped (confirm with `lake shake`).

PL is identical with `PL.Proposition` and `propDerivationSystem`.

---

## 5. Import / cycle discipline (verified safe)

Per the Bimodal "Design Note", the bridge file must not import its `DeductionTheorem.lean`.

**Modal:**
- `Modal/Metalogic/GenericMCSBridge.lean` (currently doc-only, imports
  `Foundations…GenericMCS` + `Modal.Metalogic.DerivationTree`): add real content; also import
  `Foundations…MCSProperties` (for the SetConsistent equivalences, as temporal does). It does
  **not** import `DeductionTheorem.lean`. Remove the `module  -- shake: keep-all` marker and
  the gap-analysis comment body (replace with a real module docstring).
- `Modal/Metalogic/DeductionTheorem.lean`: add `public import …Modal.Metalogic.GenericMCSBridge`
  and `public import …Foundations.Logic.Metalogic.GenericMCS`; drop `ListHelpers` +
  `DeductionHelpers` imports.
- No cycle: `DeductionTheorem → GenericMCSBridge → {DerivationTree, GenericMCS, MCSProperties}`,
  none of which import `DeductionTheorem`.

**Propositional:**
- New file `Propositional/Metalogic/GenericMCSBridge.lean` importing
  `Propositional.ProofSystem.Derivation` (tree + `propDerivationSystem`),
  `Foundations…GenericMCS`, `Foundations…MCSProperties`.
- `Propositional/Metalogic/DeductionTheorem.lean`: add the bridge + `GenericMCS` imports; drop
  `ListHelpers` + `DeductionHelpers` (and `ProofSystem.Axioms` if the deleted
  `PropositionalAxiom`-fixed `HasHilbertTree` instance was its only consumer — verify).
- Register the new file in `Cslib.lean` via `lake exe mk_all --module` (task 350 hit a
  `Cslib.lean` drift issue here — expect to re-run `mk_all`).

---

## 6. Raw call-site audit (signatures MUST be preserved)

`deductionWithMem` has **no external callers** — safe to delete. Verified:
```
grep -rn deductionWithMem Cslib/Logics/Modal  Cslib/Logics/Propositional
```
returns only the two defining `DeductionTheorem.lean` files (and the internal recursive
calls). `deductionTheorem`/`hasDeductionTheorem` external consumers (must keep compiling):

- **Modal** (`grep` confirmed, excluding the defining file):
  `Metalogic/Completeness.lean`, `Metalogic/MCS.lean`,
  `Metalogic/Systems/K/Completeness.lean`, `Metalogic/Systems/D/Completeness.lean`
  (the doc bridge `GenericMCSBridge.lean` only *mentions* the names in prose).
- **Propositional** (`grep` confirmed):
  `Metalogic/StrongCompleteness.lean`, `Metalogic/MinLindenbaum.lean`,
  `Metalogic/IntLindenbaum.lean`, `NaturalDeduction/FromHilbert.lean`,
  `NaturalDeduction/Equivalence.lean`, `Semantics/SemanticConsequence.lean`.

These call `deductionTheorem h_implyK h_implyS Γ A B d` (or `.deductionWithMem`-free
variants). Because the re-implementation keeps the exact parameter list
(`{Axioms} (h_implyK) (h_implyS) (Γ) (A B) (d)`), every call site is source-compatible. The
`hasDeductionTheorem` consumers (feeding `Consistency.lean` closure lemmas) likewise keep
their `(h_implyK) (h_implyS)` argument shape.

**Witness preservation:** Modal/PL carry no extra logic-specific DT witnesses beyond
`h_implyK`/`h_implyS` (unlike Temporal's `temporal_necessitation`/`temporal_duality`, which are
*tree constructors*, not DT parameters, and are handled inside the forward bridge case). The
modal `necessitation` constructor is preserved by the forward bridge case in §4.3.

---

## 7. Reuse-first findings

- **No existing `HilbertOf` or predicate-level minimal-axioms class.** `grep -rn HilbertOf
  Cslib/` matches only the Modal doc bridge prose. The wrapper is genuinely new (and was
  explicitly scoped as a follow-up by task 350).
- **Everything else is reuse:** `algebraicDerivationSystem`,
  `algebraic_has_deduction_theorem`, the entire bridge skeleton (`deriv_tree_to_list`,
  `unfold_listImp_in_tree`, `list_deriv_to_tree`, `*_deriv_iff_algebraic`, MCS equivalences),
  and the `K.lean` instance pattern are all copied from verified task-350 assets.
- **No Mathlib lemmas required** beyond `List.mem_cons` / `List.nil_subset` already used by the
  temporal/bimodal bridges. This is an internal-CSLib consolidation; LeanSearch/Loogle yielded
  nothing more apt than the existing `list_deduction_theorem` chain.

---

## 8. Suggested phasing for the planner (mirrors task 350's Phases B/3)

1. **Phase 1 — Foundations:** add `HasMinimalAxioms` (generic) to `GenericMCS.lean`. Build
   `Cslib.Foundations.Logic.Metalogic.GenericMCS`.
2. **Phase 2 — Modal bridge:** replace the doc-only `Modal/Metalogic/GenericMCSBridge.lean`
   with `HilbertOf` + instances + full bridge (mirror Bimodal, add `necessitation` case). Build
   `Cslib.Logics.Modal.Metalogic.GenericMCSBridge`.
3. **Phase 3 — Modal DT reroute:** re-implement `deductionTheorem`/`hasDeductionTheorem`,
   delete `deductionWithMem`. Build `Cslib.Logics.Modal.Metalogic` + the 4 Modal consumers.
4. **Phase 4 — PL bridge:** new `Propositional/Metalogic/GenericMCSBridge.lean` (4-constructor,
   no necessitation). `mk_all --module`. Build it.
5. **Phase 5 — PL DT reroute:** re-implement `deductionTheorem`/`hasDeductionTheorem`, delete
   `deductionWithMem` + the fixed `HasHilbertTree` instance. Build
   `Cslib.Logics.Propositional.Metalogic` + the 6 PL consumers.
6. **Phase 6 — CI:** `lake build`, `lake test`, `lake exe checkInitImports`,
   `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`; confirm
   sorry-free downstream (MCS, Completeness, TruthLemma/StrongCompleteness/NaturalDeduction).

Phases 2-3 (Modal) and 4-5 (PL) are independent after Phase 1 → can run as parallel waves with
file-ownership territories (Modal vs Propositional dirs are disjoint).

---

## 9. Risks & verification points (for implementer)

| # | Risk | Mitigation |
|---|------|-----------|
| R1 | `inductive HilbertOf … : Type` instance-key behaviour; `def`+unfold would break TC search | Use empty `inductive`/`structure`; if search still unfolds, add `irreducible`. Verify with `#check (inferInstance : MinimalHilbert (HilbertOf MyPred))` under a `haveI : HasMinimalAxioms`. |
| R2 | `algebraic_has_deduction_theorem` fails to infer `S := HilbertOf Axioms` through the `@[reducible] modalAlgDS` alias | Annotate `(S := HilbertOf Axioms)` explicitly (temporal didn't need it; predicate parameter may require it). |
| R3 | `.some` doesn't see through `modalDerivationSystem.Deriv` to `Nonempty` | Defeq held for temporal; if not, use `(… .mpr …)` then `Classical.choice` / `Nonempty.some` after an explicit `unfold modalDerivationSystem Modal.Deriv`. |
| R4 | PL missing `HasBot`/`HasImp (PL.Proposition Atom)` instance for `MinimalHilbert` | `lean_hover_info` on `propDerivationSystem`; both must already exist for `imp`/`bot` to typecheck. |
| R5 | `Cslib.lean` barrel drift when adding the new PL bridge file | Run `lake exe mk_all --module` (task 350 precedent). |
| R6 | Lint: new class/defs need docstrings (`docBlame`), Prop-class fields lowerCamelCase (`defsWithUnderscore`), instances namespace-wrapped (`topNamespace`) | Apply CSLib lint-prevention rules; bridge defs are `noncomputable def` (Type-valued, correct vs `defLemma`). |

---

## 10. Zero-debt assessment

- **No new `sorry`.** Every step is a total construction or a `Classical.choice` extraction
  already inherent to the `noncomputable` defs.
- **No new axioms.** `HasMinimalAxioms` is an ordinary `Prop` class; `HilbertOf` is an
  uninhabited tag with explicit instances; the bridge is constructive modulo the same
  `Classical.choice` task 350 already shipped for Temporal/Bimodal.
- **No vacuous defs.** `HilbertOf` is a tag type (legitimate, mirrors `HilbertK : Type :=
  Empty`); it is never claimed inhabited. Its content is entirely in the instances.
- If any phase cannot be completed sorry-free (e.g. an unforeseen instance-resolution wall at
  R1/R2 with no annotation fix), the correct action is **mark that phase [BLOCKED]** for user
  review — **not** a `sorry` or axiom. No blocker is anticipated given the verified template
  parity.

---

## 11. Verified symbol/line reference table

| Symbol | File:line | Status |
|--------|-----------|--------|
| Modal `deductionTheorem` / `deductionWithMem` / `hasDeductionTheorem` | `Modal/Metalogic/DeductionTheorem.lean:109 / 50 / 177` | verified |
| PL `deductionTheorem` / `deductionWithMem` / `hasDeductionTheorem` | `Propositional/Metalogic/DeductionTheorem.lean:130 / 71 / 198` | verified |
| PL fixed `HasHilbertTree` instance (to delete) | `Propositional/Metalogic/DeductionTheorem.lean:56` | verified |
| `modalDerivationSystem` / `Modal.Deriv` | `Modal/Metalogic/DerivationTree.lean:198 / 159` | verified |
| `propDerivationSystem` / `PL.Deriv` | `Propositional/ProofSystem/Derivation.lean:157` | verified |
| Modal `DerivationTree` (5 ctors incl. `necessitation`) | `Modal/Metalogic/DerivationTree.lean:98` | verified |
| PL `DerivationTree` (4 ctors, no necessitation) | `Propositional/ProofSystem/Derivation.lean:68` | verified |
| Modal doc-only bridge (HilbertOf sketch) | `Modal/Metalogic/GenericMCSBridge.lean:46-55` | verified |
| Modal `InferenceSystem`/instance template | `Modal/ProofSystem/Instances/K.lean:62-113` | verified |
| `HilbertK : Type := Empty` (tag precedent) | `Foundations/Logic/ProofSystem.lean:506` | verified |
| `algebraicDerivationSystem` / `algebraic_has_deduction_theorem` | `Foundations/Logic/Metalogic/GenericMCS.lean:54 / 65` | verified |
| `HasDeductionTheorem` (implicit Γφψ) | `Foundations/Logic/Metalogic/Consistency.lean:187` | verified |
| `InferenceSystem` / `DerivableIn` / `toDerivation` | `Foundations/Logic/InferenceSystem.lean:42 / 65 / 78` | verified |
| `MinimalHilbert` / `HasAxiomImplyK` / `HasAxiomImplyS` / `ModusPonens` | `Foundations/Logic/ProofSystem.lean:342 / 116 / 120 / 74` | verified |
| `Axioms.ImplyK` / `Axioms.ImplyS` | `Foundations/Logic/Axioms.lean:76 / 80` | verified |
| Temporal re-routed `deductionTheorem` (body template) | `Temporal/Metalogic/DeductionTheorem.lean:66-81` | verified |
| Bimodal fresh bridge (closest template) | `Bimodal/Metalogic/Core/GenericMCSBridge.lean` | verified |
| Temporal bridge (necessitation-case template) | `Temporal/Metalogic/GenericMCSBridge.lean:101-128` | verified |
