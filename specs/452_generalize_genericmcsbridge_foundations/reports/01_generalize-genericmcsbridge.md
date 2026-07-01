# Research Report: Task 452 — Generalize GenericMCSBridge (hoist the shared MCS-bridge trio into Foundations)

- **Task**: 452
- **Type**: cslib (Lean 4 / CSLib)
- **Date**: 2026-07-01
- **Scope**: Collapse Temporal/Bimodal intra-file base↔Fc duplication (step 1) and hoist the
  logic-independent MCS-bridge machinery into `Cslib/Foundations/Logic/Metalogic/` (step 2).
- **Grounding**: All claims below are read from the actual source files and their proof bodies.
  Definitional-equality claims are evidenced by how the existing proofs `unfold`/`simp only`;
  they carry a Phase‑0 `lake build` gate before any deletions.

---

## 1. Diff-level breakdown: shared skeleton vs. per-logic divergence

### 1.1 The four files and their five-block structure

| File | Lines | Index param | Extra tree rules (beyond ax/assumption/mp/weakening) | Intra-file base+Fc dup? |
|------|-------|-------------|------------------------------------------------------|-------------------------|
| `Logics/Propositional/Metalogic/GenericMCSBridge.lean` | 256 | `Axioms : Proposition → Prop` | none | no |
| `Logics/Modal/Metalogic/GenericMCSBridge.lean` | 267 | `Axioms : Proposition → Prop` | `necessitation` | no |
| `Logics/Temporal/Metalogic/GenericMCSBridge.lean` | 370 | `fc : FrameClass` | `temporal_necessitation`, `temporal_duality` | **yes** (L66–221 base vs L239–370 Fc) |
| `Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` | 405 | `fc : FrameClass` | `necessitation`, `temporal_necessitation`, `temporal_duality` | **yes** (L66–243 base vs L244–405 Fc) |

Every file is the same five blocks in the same order:

1. **Tag + instance boilerplate** — `HilbertOf`/`HilbertBX(Fc)`/`HilbertTM(Fc)` tag `inductive`;
   `InferenceSystem` (`derivation φ := DerivationTree … [] φ`); `ModusPonens`; `HasAxiomImplyK`;
   `HasAxiomImplyS`; `MinimalHilbert`; an `@[reducible]` `…AlgDS` alias for
   `algebraicDerivationSystem`.
2. **Forward** `derivTreeToList` — `induction d` on the concrete tree. **Logic-specific.**
3. **Backward helper** `unfoldListImpInTree` — list induction using only
   `assumption`+`modus_ponens`. **Logic-independent** (verbatim modulo the `DerivationTree …`
   prefix; ~19 L each).
4. **Backward** `listDerivToTree` — `h.toDerivation` → `weakening` from `[]` → `unfoldListImpInTree`.
   **Logic-independent** (~15 L each).
5. **Iff trio** — `{logic}_deriv_iff_algebraic` (forward+backward), then
   `{logic}_setConsistent_iff_algebraic` and `{logic}_setMaxConsistent_iff_algebraic`.
   The two consistency lemmas are **logic-independent** (they only pipe the deriv-iff through
   `SetConsistent`/`SetMaximalConsistent`; ~12 L each).

### 1.2 Identical / near-identical / genuinely-specific

- **Byte-identical logic (modulo namespace/prefix rename)**:
  - `unfoldListImpInTree` — all four bodies match line-for-line except the `DerivationTree`
    qualifier (`PL.DerivationTree`, `DerivationTree`, `Bimodal.DerivationTree`) and `Context` vs
    `List (Proposition Atom)`. `Context Atom` is `abbrev … := List (Formula Atom)` in both
    Temporal (`Syntax/Context.lean:45`) and Bimodal (`Syntax/Context.lean:43`), so every context
    is uniformly `List F`.
  - `listDerivToTree` — identical modulo the same prefixes.
  - `…_setConsistent_iff_algebraic` and `…_setMaxConsistent_iff_algebraic` — identical modulo the
    name of the deriv-iff they call.
- **Near-identical (structural, renamed constructors)**: the tag/instance boilerplate (block 1).
  The only real differences are: (a) the axiom-witness feeding `HasAxiomImplyK/S`
  (`h.hasImplyK`/`h.hasImplyS` for PL/Modal vs `.imp_s`/`.imp_k` + `FrameClass.base_le fc` for
  Temporal/Bimodal — note Temporal/Bimodal **swap** the K/S axiom names, documented in-file);
  (b) `ModusPonens.mp` uses the tree `modus_ponens` at `[]` in all four.
- **Genuinely logic-specific** (must stay per-logic): the **forward** `derivTreeToList` induction.
  Lean's `induction d with | ctor …` names concrete constructors, so it cannot be written over an
  abstract `D`. The `ax`/`«axiom»` arm differs (PL/Modal `ax Γ ψ h_ax`, 3 args; Temporal/Bimodal
  `«axiom» Γ ψ h_ax h_fc`, 4 args with the `h.minFrameClass ≤ fc` side-condition), and the extra
  arms (`necessitation`, `temporal_necessitation`, `temporal_duality`) are present only where the
  calculus has those rules. These arms are exactly the "logic-specific content" and are ~20 L (PL),
  ~30 L (Modal), ~47 L (Temporal), ~59 L (Bimodal).

**Conclusion**: of the 1298 lines, the forward inductions (~160 L total) are irreducibly
per-logic; essentially everything else is mechanical duplication.

---

## 2. The typeclass abstraction (Goal 2) and reuse check

### 2.1 Reuse-first findings (what Foundations already provides)

- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` (167 L) already defines
  `algebraicDerivationSystem`, `algebraic_has_deduction_theorem`, and the
  `HasMinimalAxioms (Axioms : F → Prop)` predicate class. It imports only `ListDeduction` and
  `Consistency` — **no** `Cslib/Logics/*` dependency.
- `Cslib/Foundations/Logic/InferenceSystem.lean` — `class InferenceSystem (S α)` with
  `derivation : α → Sort v` (so `Type u`-valued trees are fine), `DerivableIn S a := Nonempty (S⇓a)`,
  and `DerivableIn.toDerivation` (Classical.choice). This is the exact interface the backward
  direction consumes.
- `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` — `SetConsistent`, `SetMaximalConsistent`,
  `closed_under_derivation`, etc. Foundations-level.
- `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` — `listImp_axiom_k`, `listImp_nil`,
  `listImp_cons`; `ListDeduction` — `list_deriv_reflection`, `list_deriv_mp`,
  `list_deriv_monotonic`, `ListDeriv`. All Foundations-level, already used by the bridges.
- **`Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean`** — proves the *converse*
  (`HasDeductionTheorem D → MinimalHilbert (DtSystem D hdt)`) over the **algebraic** `DerivationSystem`
  (`Deriv : List F → F → Prop`). It is the closest existing pattern (generic tag `structure DtSystem`
  + `InferenceSystem` + `MinimalHilbert`), but it is **not** a drop-in for this task: it operates on
  a `Prop`-valued `DerivationSystem`, whereas the bridge needs a **`Type`-valued contextual tree
  family** `D : List F → F → Type*` with real `assumption`/`mp`/`weakening` constructors. So a new
  (small) typeclass is required; nothing existing already captures it.

**Verdict**: Existing `InferenceSystem`/`MinimalHilbert`/`HasAxiomImplyK/S`/`algebraicDerivationSystem`
supply the *inference-system* side. The missing piece is a data-carrying class abstracting the
**tree family** and its four structural constructors + K/S. This must be new.

### 2.2 Proposed new typeclass `HilbertTree`

```lean
namespace Cslib.Logic.Metalogic.GenericMCS   -- extend the existing namespace

variable {F : Type*} [HasImp F]

/-- A `Type`-valued contextual derivation-tree family closed under assumption, modus ponens,
weakening, and containing the K and S axiom schemata at the empty context. This is exactly the
interface the backward MCS-bridge direction needs; the forward direction stays per-logic. -/
class HilbertTree (D : List F → F → Type*) where
  assumption : ∀ {Γ : List F} {a : F}, a ∈ Γ → D Γ a
  mp         : ∀ {Γ : List F} {φ ψ : F}, D Γ (HasImp.imp φ ψ) → D Γ φ → D Γ ψ
  weakening  : ∀ {Γ Δ : List F} {φ : F}, Γ ⊆ Δ → D Γ φ → D Δ φ
  axiomK     : ∀ (φ ψ : F), D [] (HasImp.imp φ (HasImp.imp ψ φ))
  axiomS     : ∀ (φ ψ χ : F), D [] (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
                 (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ)))
```

Every field is transcribed directly from working code:
- `assumption` ← `DerivationTree.assumption Γ a ha_mem`;
- `mp` ← `DerivationTree.modus_ponens Γ φ ψ d d_a`;
- `weakening` ← `DerivationTree.weakening [] Γ _ d₀ (List.nil_subset Γ)` (arg order is our choice);
- `axiomK`/`axiomS` ← `DerivationTree.ax [] _ (h.hasImplyK …)` (PL/Modal) and
  `.axiom [] _ (.imp_s …) (FrameClass.base_le fc)` (Temporal/Bimodal).

### 2.3 Generic tag + instances + helpers (all Foundations, zero logic imports)

```lean
/-- Tag type for the inference system of closed `D`-derivations. -/
structure ClosedHilbert (D : List F → F → Type*) : Type where

instance (D) : InferenceSystem (ClosedHilbert D) F where derivation φ := D [] φ

instance (D) [HilbertTree (F := F) D] : ModusPonens (ClosedHilbert D) (F := F) where
  mp h₁ h₂ := by obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂; exact ⟨HilbertTree.mp d₁ d₂⟩
instance (D) [HilbertTree (F := F) D] : HasAxiomImplyK (ClosedHilbert D) (F := F) where
  implyK := ⟨HilbertTree.axiomK _ _⟩
instance (D) [HilbertTree (F := F) D] : HasAxiomImplyS (ClosedHilbert D) (F := F) where
  implyS := ⟨HilbertTree.axiomS _ _ _⟩
instance (D) [HilbertTree (F := F) D] : MinimalHilbert (ClosedHilbert D) (F := F) where

@[reducible] def treeAlgDS (D) [HilbertTree (F := F) D] : DerivationSystem F :=
  algebraicDerivationSystem (S := ClosedHilbert D)

/-- Generic backward helper (was `unfoldListImpInTree` × 4). -/
noncomputable def unfoldListImp [HilbertTree (F := F) D] {Γ : List F} {φ : F} :
    (Ψ : List F) → D Γ (listImp Ψ φ) → (∀ a ∈ Ψ, a ∈ Γ) → D Γ φ
  | [], d, _ => by simpa only [listImp_nil] using d
  | a :: Ψ', d, h_sub => by
      simp only [listImp_cons] at d
      have ha : a ∈ Γ := h_sub a (List.mem_cons.mpr (Or.inl rfl))
      exact unfoldListImp Ψ' (HilbertTree.mp d (HilbertTree.assumption ha))
        (fun x hx => h_sub x (List.mem_cons.mpr (Or.inr hx)))

/-- Generic backward direction (was `listDerivToTree` × 4). -/
noncomputable def listDerivToTree [HilbertTree (F := F) D] {Γ : List F} {φ : F}
    (h : (treeAlgDS D).Deriv Γ φ) : D Γ φ := by
  simp only [treeAlgDS, algebraicDerivationSystem] at h
  unfold ListDeriv at h
  have d₀ : D [] (listImp Γ φ) := h.toDerivation
  exact unfoldListImp Γ (HilbertTree.weakening (List.nil_subset Γ) d₀) (fun _ ha => ha)

/-- Generic assembler for the derivability iff, taking the per-logic forward direction. -/
theorem deriv_iff_algebraic_of_forward [HilbertTree (F := F) D]
    {treeSys : DerivationSystem F}
    (h_tree : ∀ {Γ φ}, treeSys.Deriv Γ φ ↔ Nonempty (D Γ φ))
    (forward : ∀ {Γ φ}, D Γ φ → (treeAlgDS D).Deriv Γ φ)
    {Γ : List F} {φ : F} : treeSys.Deriv Γ φ ↔ (treeAlgDS D).Deriv Γ φ := by
  rw [h_tree]; exact ⟨fun ⟨d⟩ => forward d, fun h => ⟨listDerivToTree h⟩⟩

/-- Fully generic consistency transfer (was `…_setConsistent_iff_algebraic` × 4). -/
theorem setConsistent_iff_congr {D₁ D₂ : DerivationSystem F}
    (h : ∀ Γ φ, D₁.Deriv Γ φ ↔ D₂.Deriv Γ φ) {Ω : Set F} :
    SetConsistent D₁ Ω ↔ SetConsistent D₂ Ω := by
  unfold SetConsistent Consistent
  exact ⟨fun hc L hL hd => hc L hL ((h _ _).mpr hd),
         fun hc L hL hd => hc L hL ((h _ _).mp hd)⟩

/-- Fully generic MCS transfer (was `…_setMaxConsistent_iff_algebraic` × 4). -/
theorem setMaxConsistent_iff_congr {D₁ D₂ : DerivationSystem F}
    (h : ∀ Γ φ, D₁.Deriv Γ φ ↔ D₂.Deriv Γ φ) {Ω : Set F} :
    SetMaximalConsistent D₁ Ω ↔ SetMaximalConsistent D₂ Ω := by
  unfold SetMaximalConsistent
  exact ⟨fun ⟨hc, hm⟩ => ⟨(setConsistent_iff_congr h).mp hc,
            fun φ hφ hi => hm φ hφ ((setConsistent_iff_congr h).mpr hi)⟩,
         fun ⟨hc, hm⟩ => ⟨(setConsistent_iff_congr h).mpr hc,
            fun φ hφ hi => hm φ hφ ((setConsistent_iff_congr h).mp hi)⟩⟩
```

`setConsistent_iff_congr` / `setMaxConsistent_iff_congr` are **pure `DerivationSystem` corollaries**
— no tree, no `HilbertTree`. They belong in `GenericMCS.lean` (or `MCSProperties.lean`) and are the
cleanest, zero-risk win (they eliminate ~24 L × 4 = ~96 L).

### 2.4 What stays per-logic after extraction

Each bridge shrinks to: (a) `instance : HilbertTree (DerivationTree …) := { … }` (~10 L, concrete
constructors); (b) the forward `derivTreeToList` induction (unchanged, ~20–59 L); (c) three thin
`def`/`theorem` re-exports assembling the public names from the generic combinators.

---

## 3. Validate step (1): base bridge as `fc := .Base` specialization (Goal 3)

### 3.1 The Fc API is real and total

- `FrameClass` (`Temporal/ProofSystem/Axioms.lean:40`) = `Base | Dense | Discrete`, with `LE` (Base
  ≤ everything), `PartialOrder`, `DecidableRel`, and `FrameClass.base_le (fc) : Base ≤ fc`
  (`:63`, proof `cases fc <;> trivial`).
- `DerivationTree (fc : FrameClass) : Context → Formula → Type u`
  (`Temporal/ProofSystem/Derivation.lean:50`, Bimodal `:53`). The `axiom` constructor carries
  `h_fc : h.minFrameClass ≤ fc`.
- Temporal already has `HilbertBXFc fc` + `MinimalHilbert (HilbertBXFc fc)` + `derivTreeToListFc`
  + `unfoldListImpInTreeFc` + `listDerivToTreeFc` + `temporal_deriv_iff_algebraic_fc` (L239–370).
  Bimodal mirrors this with `HilbertTMFc fc` (L244–405).

### 3.2 The base↔Fc defeq

`HilbertBX`'s `InferenceSystem` is `derivation φ := DerivationTree FrameClass.Base [] φ`
(`Temporal/ProofSystem/Instances.lean:43`). `HilbertBXFc fc`'s is `derivation φ := DerivationTree fc
[] φ`. **At `fc := .Base` these are literally the same expression.** Therefore

```
temporalAlgDS.Deriv Γ φ
  = ListDeriv (S := HilbertBX) Γ φ = Nonempty (HilbertBX ⇓ listImp Γ φ)
  = Nonempty (DerivationTree .Base [] (listImp Γ φ))
temporalAlgDSFc .Base .Deriv Γ φ
  = ListDeriv (S := HilbertBXFc .Base) Γ φ
  = Nonempty (DerivationTree .Base [] (listImp Γ φ))
```

are **definitionally equal**. This is corroborated by the existing base proofs, which `simp only
[temporalAlgDS, algebraicDerivationSystem]; unfold ListDeriv` and then treat the goal as
`Nonempty (DerivationTree .Base [] …)` — identical to what the `_fc` proofs do. Likewise
`temporalDerivationSystem.Deriv Γ φ` `unfold`s to `Nonempty (DerivationTree .Base Γ φ)` (the base
`temporal_deriv_iff_algebraic` proof does exactly `unfold temporalDerivationSystem Temporal.Deriv`),
which is precisely the LHS of `temporal_deriv_iff_algebraic_fc (fc := .Base)`.

### 3.3 Concrete step-(1) realization (lowest risk)

Keep the base *public names and statements verbatim*; replace only the three base proof **bodies**
with one-line delegations to the `_fc` versions:

```lean
lemma derivTreeToList (d : DerivationTree FrameClass.Base Γ φ) :
    (temporalAlgDS (Atom := Atom)).Deriv Γ φ := derivTreeToListFc d
noncomputable def unfoldListImpInTree (Ψ) (d) (h_sub) := unfoldListImpInTreeFc (fc := .Base) Ψ d h_sub
noncomputable def listDerivToTree (h : temporalAlgDS.Deriv Γ φ) :=
    listDerivToTreeFc (fc := .Base) h
```

Each delegation typechecks by the §3.2 defeq. **Implementation constraint discovered**: the `_fc`
block is currently *below* the base block in both files (Temporal base L66–221, Fc L239–370; Bimodal
base L66–243, Fc L244–405). Lean requires the `_fc` definitions to be in scope first, so **the Fc
block must be moved above the base block** (or the base defs deleted and re-expressed after Fc).
This reordering is the only structural change; it touches no other file.

Net reduction from step (1) alone: Temporal ~60 L, Bimodal ~70 L (the base forward/helper/backward
proof bodies become 3 one-liners each). Public names `temporalAlgDS`,
`temporal_deriv_iff_algebraic`, `bimodalAlgDS`, `bimodal_deriv_iff_algebraic`, and the `_fc`
theorems are all preserved.

**Interaction with step (2)**: after step (1), the *only* backward machinery left is the `_fc`
`unfoldListImpInTreeFc`/`listDerivToTreeFc`, which are themselves instances of the generic
`unfoldListImp`/`listDerivToTree` from §2.3 (with `D := DerivationTree fc`). So step (2) then
replaces even those with `HilbertTree`-based delegations. Do **step (1) first** (no cross-logic
abstraction, easy to verify), then step (2).

---

## 4. Home, name, and import implications (Goal 4)

### 4.1 Name collision on the proposed path

The task proposes `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — **that file already exists**
(167 L, holds `algebraicDerivationSystem` + `HasMinimalAxioms`). Do **not** create a second file at
that path. Two acceptable homes:

- **(Preferred) Extend the existing `GenericMCS.lean`** — add the `HilbertTree` class, `ClosedHilbert`
  tag + instances, `treeAlgDS`, `unfoldListImp`, `listDerivToTree`, and the two `*_iff_congr`
  corollaries into the existing `namespace Cslib.Logic.Metalogic.GenericMCS`. Reuse-first; the
  material is a natural continuation of that module and shares its imports.
- **(Alt) New sibling file** `Cslib/Foundations/Logic/Metalogic/TreeBridge.lean`
  (namespace `Cslib.Logic.Metalogic.GenericMCS`), `public import`ing `GenericMCS` and
  `MCSProperties`. Choose this only if keeping `GenericMCS.lean` small is preferred; it adds one
  barrel entry (`lake exe mk_all --module`).

### 4.2 No import cycle

The new material is parametric over abstract `F` and `D : List F → F → Type*` and references only
Foundations symbols (`InferenceSystem`, `MinimalHilbert`, `HasAxiomImplyK/S`, `algebraicDerivationSystem`,
`ListDeriv`, `listImp_*`, `list_deriv_*`, `SetConsistent`, `SetMaximalConsistent`). It imports **no**
`Cslib/Logics/*`. The per-logic bridges already `public import
Cslib.Foundations.Logic.Metalogic.GenericMCS`, so they pick up the new symbols with no new import.
**No cycle is created.**

### 4.3 Importers and public API to preserve

Each bridge is imported only within its own logic (no cross-logic bridge import today):

| Bridge | Imported by |
|--------|-------------|
| PL | `Propositional/Metalogic/DeductionTheorem.lean` |
| Modal | `Modal/Metalogic/DeductionTheorem.lean` |
| Temporal | `Temporal/Metalogic/{DeductionTheorem, MCS, DenseMCS}.lean` |
| Bimodal | `Bimodal/Metalogic/Core/DeductionTheorem.lean` |

External references that the refactor **must keep resolvable** (grep-verified; excludes the four
bridge files themselves and doc-only mentions in `Foundations/.../GenericMCS.lean`):

- `listDerivToTree` — used by **PL** and **Modal** `DeductionTheorem.lean` (⚠ not internal-only).
- `temporalAlgDS`, `temporal_deriv_iff_algebraic` — Temporal `DeductionTheorem.lean`.
- `temporal_deriv_iff_algebraic_fc`, `HilbertBXFc` — Temporal `DenseMCS.lean`.
- `bimodal_deriv_iff_algebraic`, `bimodal_deriv_iff_algebraic_fc`, `HilbertTMFc` — Bimodal
  `Core/DeductionTheorem.lean`.
- `modal_deriv_iff_algebraic` (Modal DT), `pl_deriv_iff_algebraic` (PL DT).
- `unfoldListImpInTree`, `derivTreeToList*`, `…AlgDSFc`, `modalAlgDS`, `propAlgDS`,
  `bimodalAlgDS` — **no external references** (safe to restructure freely).

Design rule: keep every externally-referenced name as a thin `def`/`theorem`/`abbrev` at its current
location and signature; only the *bodies* move to the generic combinators.

### 4.4 Tag types cannot be globally replaced

`Temporal.HilbertBX` carries **22 `HasAxiom*` instances** registered in
`Temporal/ProofSystem/Instances.lean` (and Bimodal `HilbertTM` similarly). The generic
`ClosedHilbert D` tag only supplies the minimal K/S/MP/MinimalHilbert bundle. Therefore
`HilbertBX`/`HilbertBXFc`/`HilbertTM`/`HilbertTMFc` must be **kept** (they are load-bearing
downstream and externally referenced). Consequence: for **Temporal/Bimodal**, hoist the *helpers and
corollaries* (§2.3) but keep the tag + `MinimalHilbert` boilerplate local. For **PL/Modal**, the
tags `HilbertOf` are not referenced externally, so those two could optionally adopt the generic
`ClosedHilbert (DerivationTree Axioms)` tag fully — a further ~35 L × 2 saving — but that is
optional and higher-touch; recommend deferring it to keep the first pass low-risk.

---

## 5. Collision check with in-flight/pending tasks (Goal 5)

| Task | Status | Files it touches | Conflict with 452? |
|------|--------|------------------|--------------------|
| **441** Modal proposition native refactor | [PLANNED], ~1.5–2k L | Redefines `Modal.Proposition` (native `atom/bot/imp/and/or/box/diamond`); cascades `Modal/Basic.lean`, `Modal/LogicalEquivalence.lean`, `Modal/Tableau/*`, `Bimodal/Embedding/ModalEmbedding.lean`. Plan does **not** list `Modal/Metalogic/DerivationTree.lean` or the Modal bridge. | **Low–moderate.** 441 changes the *formula* constructors, not the *derivation-tree* constructors (`ax/assumption/mp/necessitation/weakening`) the Modal bridge inducts on; `HasImp`/`HasBot` and K/S shapes are unchanged. The Modal bridge should survive 441 with at most a rebase. Coordinate ordering; the Modal portion of 452 is tiny (a `HilbertTree` instance + delegations). |
| **442** Modal tableau FMP fuel | [COMPLETED] | tableau/FMP | **None.** |
| **449** Define BX+ (`FrameClass.Metric` + 4 axioms + soundness) | [NOT STARTED] | `Temporal/ProofSystem/Axioms.lean` (extends `FrameClass` inductive + `LE`/`PartialOrder`/`DecidableRel`/`minFrameClass`), Temporal `Soundness.lean`, `DerivationTree FrameClass.Metric` plumbing. | **Forward-compatible.** The Temporal bridge is already `fc`-polymorphic; the generic `HilbertTree (DerivationTree fc)` instance and `base_le fc` cover a new `.Metric` case automatically. 449 does not touch the bridge file. If 449 lands first, 452 rebases mechanically; if 452 lands first, 449's `base_le`/`minFrameClass` additions Just Work. |
| **450** TM conservative over BX+ | [NOT STARTED] | Bimodal metalogic (conservativity), depends on 449. | **Low.** May edit files near the Bimodal bridge, but 452 preserves the Bimodal public API. Preserve names → no break. |
| **451** BX+ completeness | [NOT STARTED] | BX+ metatheory. | **None expected** (downstream of 449/450). |
| **415** Lifting audit | [COMPLETED] | audit only; spawned 416/393. | **Complementary, not overlapping.** 415's report explicitly names `GenericMCS`/`GenericMCSBridge` as the shared substrate and confirms the per-logic divergence ("Modal has `necessitation`; PL has none — confirmed in `GenericMCSBridge.lean`"), but its spawned tasks (416 GenericLindenbaum, 393 Min/Int closure micro-dup) do **not** cover the MCS-bridge trio. 452 is the missing follow-up. |
| **393** residual Min/Int closure dedup | (from 415) | Lindenbaum closure-scaffolding (~40 L). | **Disjoint** duplication (Lindenbaum, not the bridge trio). No overlap. |
| **439** processNext / tableau | [RESEARCHED] | Temporal tableau ordering. | **None** (tableau, not metalogic bridge). |

**Sequencing recommendation**: 452 preserves all public names, so it can land independently.
Preferred order to minimize rebases: land **441** (large, Modal-wide) before or clearly separated
from 452's Modal touch; land **452** before **449–451** (452 is a pure refactor; 449–451 then build
on the cleaner base). If 449 must go first, 452's Temporal/Bimodal work is unaffected in substance.

---

## 6. Concrete signatures for the extracted module (Goal 6)

See the fully-worked code in §2.2–§2.3. Summary of the new Foundations surface:

- `class HilbertTree (D : List F → F → Type*)` — 5 fields (`assumption`, `mp`, `weakening`,
  `axiomK`, `axiomS`).
- `structure ClosedHilbert (D)` + `InferenceSystem`/`ModusPonens`/`HasAxiomImplyK`/`HasAxiomImplyS`/
  `MinimalHilbert` instances + `@[reducible] def treeAlgDS`.
- `noncomputable def unfoldListImp` — generic backward helper.
- `noncomputable def listDerivToTree` — generic backward direction.
- `theorem deriv_iff_algebraic_of_forward` — assembles the deriv-iff from a per-logic forward map.
- `theorem setConsistent_iff_congr`, `theorem setMaxConsistent_iff_congr` — pure `DerivationSystem`
  transfer lemmas.

Per-logic instance example (Temporal):

```lean
instance (fc : FrameClass) : HilbertTree (F := Formula Atom) (DerivationTree fc) where
  assumption {Γ a} h := DerivationTree.assumption Γ a h
  mp {Γ φ ψ} d₁ d₂  := DerivationTree.modus_ponens Γ φ ψ d₁ d₂
  weakening {Γ Δ φ} h d := DerivationTree.weakening Γ Δ φ d h
  axiomK φ ψ := .axiom [] _ (.imp_s _ _) (FrameClass.base_le fc)
  axiomS φ ψ χ := .axiom [] _ (.imp_k _ _ _) (FrameClass.base_le fc)
```

(PL/Modal supply `axiomK/axiomS` from `HasMinimalAxioms.hasImplyK/hasImplyS` with `DerivationTree.ax`.)

---

## 7. Elimination estimate

| Item | Per-file | ×N | Generic cost | Net saved |
|------|----------|----|--------------|-----------|
| Step 1: Temporal/Bimodal base forward+helper+backward bodies → 3 delegations | ~60 / ~70 | 2 | 0 | ~130 |
| `unfoldListImpInTree(Fc)` bodies → generic `unfoldListImp` | ~19 | 4 (+2 Fc) | ~10 | ~55 |
| `listDerivToTree(Fc)` bodies → generic `listDerivToTree` | ~15 | 4 (+2 Fc) | ~10 | ~45 |
| `…_setConsistent_iff` + `…_setMaxConsistent_iff` → 2 generic congr lemmas | ~24 | 4 | ~14 | ~82 |
| (optional) PL/Modal tag boilerplate → `ClosedHilbert` | ~35 | 2 | in generic | ~55 (deferred) |
| **Total (first pass, excl. optional)** | | | ~+50 new Foundations L | **~300–330 eliminated** |

Consistent with the task's 300–450 estimate. The optional PL/Modal tag adoption reaches the upper end.

---

## 8. Risks, unknowns, and Phase‑0 gate

1. **Defeq gate (blocking).** §3.2 (base↔Fc) and §2.3 (`treeAlgDS`/`ClosedHilbert` unfolding) are
   argued by reading, not compiled. Implementation **Phase 0** must: (a) add the generic module and
   `lake build` it in isolation; (b) prove the Temporal base delegation `derivTreeToList d :=
   derivTreeToListFc d` compiles after reordering, before deleting any base body. Do not delete a
   proof body until its delegation builds.
2. **Definition ordering (Temporal & Bimodal).** The `_fc` block must move above the base block
   (§3.3). Pure reordering; verify with `lake build Cslib.Logics.Temporal.Metalogic.GenericMCSBridge`.
3. **Universe/`Type*`.** `DerivationTree` is `Type u`; `InferenceSystem.derivation : α → Sort v`
   accommodates it (existing instances already do `derivation φ := DerivationTree … [] φ`). The
   generic `ClosedHilbert D`/`treeAlgDS` must carry the same universe polymorphism — check the
   `S := ClosedHilbert D` elaboration against `algebraicDerivationSystem`'s `[InferenceSystem S F]`.
4. **`weakening` argument order & implicit binders.** The `HilbertTree` fields use implicit
   `{Γ Δ φ}` whereas concrete constructors take them explicitly; the per-logic instance adapts
   (shown in §6). Confirm elaboration.
5. **Tag types stay (§4.4).** Do not replace `HilbertBX(Fc)`/`HilbertTM(Fc)`; only hoist helpers.
6. **Zero-debt**: the refactor introduces no new proof obligations that could need `sorry`/axioms —
   it moves existing sorry-free proofs. DoD (build/test/lint green, zero new sorries/axioms) is
   achievable; verify with `lake build`, `lake test`, `lake lint`, `lake exe lint-style`,
   `lake exe checkInitImports`, and (new file) `lake exe mk_all --module`, plus `lean_verify` on the
   generic defs.

## 9. Suggested phase decomposition for planning

- **Phase 0** — Add generic `HilbertTree`/`ClosedHilbert`/`treeAlgDS`/`unfoldImp`/`listDerivToTree`
  + `*_iff_congr` to `Foundations/.../GenericMCS.lean`; `lake build` in isolation. No per-logic edits.
- **Phase 1** — Collapse Temporal base↔Fc (reorder Fc above base; delegate 3 bodies). Build+verify.
- **Phase 2** — Collapse Bimodal base↔Fc likewise. Build+verify.
- **Phase 3** — Retarget Temporal & Bimodal `_fc` helpers to the generic `unfoldImp`/`listDerivToTree`
  via a `HilbertTree (DerivationTree fc)` instance; replace the two consistency lemmas with
  `*_iff_congr`. Build+verify.
- **Phase 4** — Retarget PL & Modal (add `HilbertTree (DerivationTree Axioms)`; delegate helpers +
  consistency lemmas; keep `listDerivToTree` name for external callers). Build+verify.
- **Phase 5** — Full `lake build`/`test`/`lint`/`lint-style`/`checkInitImports`/`shake`; `lean_verify`
  the generic defs for zero axioms/sorries.
- **(Optional Phase 6)** — PL/Modal adopt `ClosedHilbert` tag to retire remaining boilerplate.
