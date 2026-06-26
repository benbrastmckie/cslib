# Research Report: Generic Deduction Theorem & Lindenbaum Consolidation (Task 350)

**Date:** 2026-06-26
**Agent:** cslib-research-agent
**Scope:** Route the four logics' deduction-theorem and Lindenbaum machinery through the
Foundations generic layer, deleting duplicated hand proofs. Reuse-first analysis.

---

## 0. Executive Summary (key findings, some correcting the task premise)

1. **Lindenbaum is already consolidated.** Every *plain* Lindenbaum lemma
   (`prop_lindenbaum`, `modal_lindenbaum`, `temporal_lindenbaum`, `bimodal_lindenbaum`,
   plus `temporal_lindenbaum_fc`) is already a one-line delegation to the generic
   `Metalogic.set_lindenbaum`. There are **no remaining hand Zorn proofs of plain
   Lindenbaum**. The Zorn uses that remain in `Logics/` are for *different,
   extra-structured* constructions (R-maximal DCS extensions, restricted/closure MCS,
   intuitionistic/minimal prime-exclusion) which are explicitly out of scope ("where the
   logic carries no extra structure"). **No Lindenbaum work is required.**

2. **The deduction theorem has two layers per logic, only one of which is cheaply
   reroutable.**
   - *Layer A — Prop-level wrapper* (`HasDeductionTheorem` instance, ~6 lines each): feeds
     `Consistency.lean` closure properties. Reroutable through a bridge + generic
     `algebraic_has_deduction_theorem`.
   - *Layer B — Type-valued `deductionTheorem` def + `deductionWithMem` helper*
     (~150-230 lines each, WF recursion on tree height): the actual bulk. It is consumed
     **directly as a raw `DerivationTree` producer** at ~40 call sites across Modal,
     Propositional, Bimodal, and Temporal. These consumers need an actual tree, not the
     `Prop`-level predicate.

3. **The generic `algebraic_has_deduction_theorem` only proves the `Prop`-level
   `HasDeductionTheorem` for `algebraicDerivationSystem` (ListDeriv).** Transferring it to a
   logic's *tree-based* `DerivationSystem` requires a pointwise equivalence bridge
   `treeDS.Deriv Γ φ ↔ algDS.Deriv Γ φ`.

4. **Bridge status (corrects the task description):**
   - **Temporal** — real bridge exists (`temporal_deriv_iff_algebraic`), and it is
     **independent of the hand proof** (uses no `deductionTheorem`/`deductionWithMem`).
     Ready to reroute.
   - **Modal** — `GenericMCSBridge.lean` is **documentation-only** (contains *no* Lean
     theorem). The task's claim that Modal has a usable "seam" is inaccurate. Its gap
     analysis is also **outdated/over-pessimistic**: since `InferenceSystem Modal.HilbertK`
     is defined as `DerivationTree KAxiom [] φ`, the temporal-style equivalence *is*
     buildable (the `□(φ→φ)` "counterexample" is in fact derivable in `algDS` at `[]`).
   - **Propositional, Bimodal** — no bridge; must be created (Bimodal mirrors Temporal;
     Propositional mirrors Modal).

5. **Architectural blocker for Modal & Propositional:** their `deductionTheorem` is
   polymorphic over an **`Axioms : Proposition → Prop` predicate**, whereas
   `algebraicDerivationSystem` is keyed on a **type `S` with `[InferenceSystem S]
   [MinimalHilbert S]`**. The generic layer cannot be applied to an arbitrary predicate
   without new "predicate → InferenceSystem" infrastructure. Temporal and Bimodal use a
   **fixed** system (`HilbertBX` / `FrameClass.Base`) and map cleanly.

6. **Recommended reuse-first scope:** fully consolidate **Temporal** (bridge exists) and
   **Bimodal** (build bridge) via signature-preserving re-implementation of the
   Type-valued `deductionTheorem` (deleting `deductionWithMem` + the WF body). Treat
   **Modal/Propositional** as a separate, larger effort gated on new infrastructure;
   without that, only the trivial Layer-A wrapper can be rerouted there, which is low value
   and may not justify the change. See §7 for the concrete plan and §8 for the
   no-sorry/zero-debt assessment.

---

## 1. The generic Foundations layer (verified)

All paths are `Cslib/Foundations/Logic/Metalogic/`.

### 1.1 `list_deduction_theorem` — `ListDeduction.lean:55`
```lean
theorem list_deduction_theorem (φ ψ : F) (Γ : List F) :
    ListDeriv (S := S) (φ :: Γ) ψ ↔ ListDeriv (S := S) Γ (HasImp.imp φ ψ)
```
- Requires `[HasBot F] [HasImp F] [InferenceSystem S F] [MinimalHilbert S (F := F)]`
  (file-level `variable`s, lines 38-40).
- Structural proof via `list_flip_implication1/2` (the "flip lemmas") — **no induction on
  proof trees**. `ListDeriv Γ φ := InferenceSystem.DerivableIn S (listImp Γ φ)` (line 47).

### 1.2 `algebraic_has_deduction_theorem` — `GenericMCS.lean:65`
```lean
theorem algebraic_has_deduction_theorem :
    HasDeductionTheorem (algebraicDerivationSystem (S := S) (F := F))
```
- `algebraicDerivationSystem : DerivationSystem F` (`GenericMCS.lean:54`) bundles `ListDeriv`
  with weakening/assumption/mp.
- Proof body is `(list_deduction_theorem φ ψ Γ).mp h` — trivial once you are in `ListDeriv`.
- Convenience wrappers `algebraic_mcs_{closed_under_derivation,implication_property,negation_complete}`
  (lines 74-93).

### 1.3 `set_lindenbaum` — `Consistency.lean:152`
```lean
theorem set_lindenbaum (D : DerivationSystem F) {S : Set F}
    (hS : SetConsistent D S) :
    ∃ M : Set F, S ⊆ M ∧ SetMaximalConsistent D M
```
- Generic over **any** `DerivationSystem F` (no `MinimalHilbert` needed). Uses
  `zorn_subset_nonempty` + `consistent_chain_union` (lines 137-143).
- `HasDeductionTheorem D` is a standalone `Prop` (`Consistency.lean:182`); the closure
  properties `SetMaximalConsistent.{closed_under_derivation,implication_property,negation_complete}`
  (lines 213, 246, 264) take it as a hypothesis `hdt`.

### 1.4 `MinimalHilbert` typeclass — `Cslib/Foundations/Logic/ProofSystem.lean:342`
```lean
class MinimalHilbert (S : Type*) [HasBot F] [HasImp F] [InferenceSystem S F]
    extends ModusPonens S (F := F), HasAxiomImplyK S (F := F), HasAxiomImplyS S (F := F)
```
= MP + K + S. `IntuitionisticHilbert` adds EFQ; `ClassicalHilbert` adds Peirce;
`ModalHilbert` adds `Necessitation` + `HasAxiomK` (line 361). It is keyed on a **type `S`**,
not a predicate — central to the §5 blocker.

---

## 2. The four hand proofs of the deduction theorem (verified line refs)

| Logic | File | `deductionWithMem` | `deductionTheorem` | Prop-level wrapper | Parameterization |
|-------|------|--------------------|--------------------|--------------------|------------------|
| Propositional | `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` | `:71` (def) | `:130` (def) | `hasDeductionTheorem :198` | over `Axioms : PL.Proposition → Prop` + implyK/implyS witnesses |
| Modal | `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` | `:50` | `:109` | `hasDeductionTheorem :177` | over `Axioms : Proposition → Prop` + witnesses |
| Temporal | `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` | `:72` | `:119` | `temporal_has_deduction_theorem :167` | **fixed** `FrameClass.Base` |
| Bimodal | `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` | `:83` | `:161` | `bimodalHasDeductionTheorem :225` | over **value** `fc : FrameClass` |

Plus a frame-class variant: `temporal_has_deduction_theorem_fc`
(`Cslib/Logics/Temporal/Metalogic/DenseMCS.lean:265`), wrapping a `deductionTheoremFc` def
(same WF-recursion shape, defined earlier in `DenseMCS.lean`).

**Common structure (all four are near-identical):** WF recursion `termination_by d.height`,
matching on the `DerivationTree` constructors — `axiom`, `assumption` (split same/other via
`deductionImpSelf` / `deductionAssumptionOther`), `modus_ponens` (`deductionMpUnderImp`),
`weakening` (three subcases using `deductionWithMem` + `removeAll`), and the
necessitation/duality constructors which are *vacuously impossible* under a non-empty context
(`simp at hA`). All four share the helpers from
`Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean`
(`deductionAxiom`, `deductionImpSelf`, `deductionAssumptionOther`, `deductionMpUnderImp`) and
the `HasHilbertTree` instance pattern. This is exactly the 4x duplication the task targets.

**Critical: the Type-valued `deductionTheorem`/`deductionWithMem` are consumed as raw-tree
producers (NOT just for the wrapper).** Direct call sites (excluding the defining files):
- **Bimodal (~16):** `BXCanonical/TruthLemma.lean:102`, `BXCanonical/Completeness/Dense.lean:80`,
  `Core/MaximalConsistent.lean:153`, `Bundle/WitnessSeed.lean:{177,294,412,487}`,
  `Metalogic/Completeness.lean:{92,200,201}`, `BXCanonical/Frame.lean:{210,260,321,...}`.
- **Temporal (~2 raw + chronicle):** `Chronicle/Frame.lean:{153,200}`.
- **Modal (~15):** `Metalogic/Completeness.lean:{128,129,176,177,229,230,314,343,395,542(WithMem),563}`,
  `Metalogic/MCS.lean:{254,325}`, `Systems/K/Completeness.lean:{85,209,238}`,
  `Systems/D/Completeness.lean:{94,286,315}`.
- **Propositional (~10):** `Metalogic/StrongCompleteness.lean:{288,341,447(WithMem),474}`,
  `Metalogic/MinLindenbaum.lean:{128,131(WithMem)}`, `Metalogic/IntLindenbaum.lean:{145,148(WithMem)}`,
  `NaturalDeduction/FromHilbert.lean:{80,146}`, `NaturalDeduction/Equivalence.lean:285`.

**Consequence:** the bulk def cannot simply be *deleted*. It must be **re-implemented with the
same type signature** (so consumers keep compiling), with the body delegating to the bridge +
generic theorem and `deductionWithMem` removed. Only the WF-recursion bodies and
`deductionWithMem` are eliminated.

---

## 3. Lindenbaum is already generic (no work required)

All verified to delegate directly to `Metalogic.set_lindenbaum`:

| Lemma | Location | Body |
|-------|----------|------|
| `prop_lindenbaum` | `Propositional/Metalogic/MCS.lean:60` | `Metalogic.set_lindenbaum (propDerivationSystem Axioms) hS` |
| `modal_lindenbaum` | `Modal/Metalogic/MCS.lean:59` | `Metalogic.set_lindenbaum (modalDerivationSystem Axioms) hS` |
| `temporal_lindenbaum` | `Temporal/Metalogic/MCS.lean:67` | `Metalogic.set_lindenbaum temporalDerivationSystem hS` |
| `temporal_lindenbaum_fc` | `Temporal/Metalogic/DenseMCS.lean:276` | `Metalogic.set_lindenbaum (temporalDerivationSystemFc fc) hS` |
| `bimodal_lindenbaum` | `Bimodal/Metalogic/Core/MaximalConsistent.lean:92` | `Metalogic.set_lindenbaum bimodalDerivationSystem hΩ` |

This consolidation was completed by task 338 (Propositional/Temporal) and already covers
Modal/Bimodal too. **Remaining `zorn_subset(_nonempty)` uses in `Logics/` are out of scope:**
`Bimodal/.../RestrictedMCS.lean`, `Bimodal|Temporal/.../Chronicle/RRelation.lean` (R-maximal
DCS), `Propositional/Metalogic/{MinLindenbaum,IntLindenbaum}.lean` (φ-excluding prime
extensions). These carry extra structure (deductive closure, R-relations, primeness) beyond
plain set-MCS and are correctly *not* delegated.

---

## 4. The existing seams (bridges)

### 4.1 Temporal bridge — REAL, reusable, independent of hand proof
`Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` proves:
- `deriv_tree_to_list` (`:86`, forward, structural induction; handles
  `temporal_necessitation`/`temporal_duality` at empty context by reconstructing via the
  underlying `HilbertBX` derivation),
- `unfold_listImp_in_tree` (`:141`, backward helper),
- `list_deriv_to_tree` (`:167`, backward),
- **`temporal_deriv_iff_algebraic` (`:188`)** — the pointwise equivalence,
- `temporal_setConsistent_iff_algebraic` (`:202`), `temporal_setMaxConsistent_iff_algebraic`
  (`:214`).

Verified: this file uses **none** of `deductionTheorem`/`deductionWithMem`/`temporal_has_deduction_theorem`.
Its `public import ...Temporal.Metalogic.DeductionTheorem` (line 9) is therefore **not
load-bearing for the equivalence** and is a candidate to drop once the wiring is reordered.
This is what makes a clean reroute possible without an import cycle.

Mechanism that makes it work: `temporalDerivationSystem.Deriv Γ φ = Nonempty (DerivationTree
FrameClass.Base Γ φ)`, and `algDS.Deriv [] φ = ListDeriv [] φ =
InferenceSystem.DerivableIn HilbertBX φ = Nonempty (DerivationTree FrameClass.Base [] φ)`
(`InferenceSystem HilbertBX` is defined this way at
`Temporal/ProofSystem/Instances.lean:43`). So `ListDeriv` at empty context is *full*
`HilbertBX` provability, including necessitation — the bridge handles necessitation purely
by bottoming out at the inference system.

### 4.2 Modal bridge — DOCUMENTATION ONLY (no theorem)
`Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` contains a gap analysis and **zero Lean
declarations** (the file body is a comment block, lines 12-122). Its conclusion ("the two
systems cannot replace each other" because of a necessitation gap) is **outdated**: the modal
`InferenceSystem` is `derivation φ := DerivationTree (@KAxiom Atom) [] φ`
(`Modal/ProofSystem/Instances/K.lean:62-64`), structurally identical to Temporal. The
temporal bridge construction transfers directly; the doc's `□(φ→φ)` example is in fact
derivable in `algDS` at `[]`. **This file needs a real bridge built, not merely reused**, and
its gap-analysis comment should be corrected.

### 4.3 Propositional, Bimodal — no bridge file exists
Must be created. Bimodal can mirror Temporal (fixed system at `FrameClass.Base`);
Propositional mirrors Modal.

---

## 5. The Modal/Propositional architectural blocker (most important risk)

`algebraicDerivationSystem` requires `[InferenceSystem S F] [MinimalHilbert S (F := F)]` for a
**type** `S`. But:

- `propDerivationSystem (Axioms : PL.Proposition → Prop)` and
  `modalDerivationSystem (Axioms : Proposition → Prop)` are parameterized over a **Prop-valued
  predicate**, and the hand `deductionTheorem` is universally quantified over all such
  `Axioms` (given `h_implyK`/`h_implyS` witnesses). There is no `InferenceSystem`/`MinimalHilbert`
  instance for an arbitrary predicate.
- Concrete registered systems do have the instances (`HilbertK`, `HilbertCl`,
  `HilbertInt`, `HilbertMin`, `HilbertConjImp`, `HilbertImp`, etc.), but the polymorphic
  `deductionTheorem`/`hasDeductionTheorem` are applied at many predicates
  (`MinPropAxiom`, `IntPropAxiom`, `ConjImpAxiom`, `ImpAxiom`, `ConjImpBotAxiom`,
  `PropositionalAxiom`, `KAxiom`, ...; see
  `Propositional/ProofSystem/FragmentAxioms.lean:{235,240,392}` and the
  Min/Int Lindenbaum/StrongCompleteness/NaturalDeduction call sites).

To route these through the generic layer you would need new infrastructure: a
"predicate → InferenceSystem + MinimalHilbert" packaging (e.g. a wrapper type
`HilbertOf Axioms` whose `derivation` is `DerivationTree Axioms []`, with `MinimalHilbert`
synthesised from the implyK/implyS witnesses). That is a non-trivial design addition, not a
reuse. **By contrast, Temporal (`HilbertBX`) and Bimodal at `FrameClass.Base` (`HilbertTM`,
`InferenceSystem` at `Bimodal/ProofSystem/Instances.lean:47`) are single fixed systems with
the instances already in place**, so the generic layer applies directly.

Bimodal subtlety: the bimodal `deductionTheorem` is polymorphic over a **value**
`fc : FrameClass`, but the `InferenceSystem`/`MinimalHilbert` instances exist only at
`FrameClass.Base`. The bridge can be built at `fc = Base`; other `fc` would need their own
inference-system instances. Most consumers use `FrameClass.Base`, but this must be audited
before deleting the polymorphic body.

---

## 6. Logic-specific witnesses to preserve

These must remain after consolidation (they live outside the deduction theorem and are
unaffected, but the bridge's forward direction must continue to reconstruct them):
- **Temporal:** `temporal_necessitation` (G-necessitation) and `temporal_duality`
  (`swapTemporal`) constructors — handled in `deriv_tree_to_list` cases
  (`GenericMCSBridge.lean:105,117`). Also `g_witness`/`h_witness` and `allFuture`/`allPast`
  closure used downstream in Chronicle/DenseMCS — these are MCS-property level, not DT level,
  and are untouched.
- **Bimodal:** `necessitation`, `temporal_necessitation`, `temporal_duality` (7-constructor
  tree). Bundle/Chronicle witness machinery (`WitnessSeed`, `PointInsertion`) consumes raw
  `deductionTheorem` trees — signature must be preserved.
- The bridge forward direction must reconstruct each non-propositional constructor at empty
  context exactly as the temporal bridge does (necessitation/duality only fire at `[]`).

---

## 7. Reuse-first plan (concrete, ordered, zero-debt)

### Phase T — Temporal (lowest risk; bridge already exists)
1. In `Temporal/Metalogic/GenericMCSBridge.lean`, drop the non-load-bearing
   `import ...DeductionTheorem` (verify no transitive need) to break any future cycle.
2. Re-implement `temporalDerivationSystem`'s deduction theorem via the bridge. Two options:
   - **Minimal:** re-prove only `temporal_has_deduction_theorem`
     (`DeductionTheorem.lean:167`) as
     `intro Γ φ ψ h; rw [temporal_deriv_iff_algebraic] at h ⊢;
      exact algebraic_has_deduction_theorem h` (needs the bridge available; may require
     moving this wrapper into/after the bridge file).
   - **Full (recommended):** keep the *signature* of the Type-valued `deductionTheorem`
     but replace its body with a bridge round-trip
     (`⟨d⟩ → temporal_deriv_iff_algebraic → algebraic_has_deduction_theorem → mpr → .some`),
     and **delete `deductionWithMem`** and the WF body. This preserves the ~2 raw call sites
     in `Chronicle/Frame.lean` and removes ~230 lines.
3. Repeat for `temporalDerivationSystemFc`/`deductionTheoremFc` in `DenseMCS.lean` only if a
   bridge at arbitrary `fc` is available; otherwise leave as-is (extra structure).
4. Verify: `lake build Cslib.Logics.Temporal.Metalogic` + downstream (Completeness,
   Chronicle, DenseCompleteness).

### Phase B — Bimodal (build bridge, then mirror Phase T)
1. Create `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` mirroring the temporal
   bridge at `S := Bimodal.HilbertTM` / `FrameClass.Base`: `bimodal_deriv_iff_algebraic`,
   plus consistency/maxconsistency equivalences. Reconstruct `necessitation`,
   `temporal_necessitation`, `temporal_duality` in the forward case.
2. Audit that all raw `deductionTheorem` consumers use `fc = Base` (TruthLemma, WitnessSeed,
   Frame, Completeness, MaximalConsistent). If any use other `fc`, scope the deletion to
   `Base` and keep the general body for those.
3. Re-implement `deductionTheorem` (Core/DeductionTheorem.lean:161) via the bridge
   (signature preserved), **delete `deductionWithMem` (:83)**, and re-prove
   `bimodalHasDeductionTheorem` (:225) through the bridge.
4. Verify build of Bimodal Metalogic + BXCanonical + Bundle.

### Phase M/P — Modal & Propositional (gated; do NOT force)
Because of §5, full consolidation requires new "predicate → InferenceSystem + MinimalHilbert"
infrastructure. Options, in preference order:
1. **Recommended:** scope this task to Temporal + Bimodal; spawn a follow-up task for the
   Modal/Propositional infrastructure (`HilbertOf Axioms` wrapper + bridge), since it is a
   genuine new abstraction, not a reuse. Update the Modal `GenericMCSBridge.lean` gap-analysis
   comment to reflect that the equivalence is buildable and to point at the follow-up.
2. If the planner insists on Modal/Prop now: build the wrapper type + instances, then a
   per-predicate bridge `propDerivationSystem Axioms .Deriv ↔ algebraicDerivationSystem
   (S := HilbertOf Axioms) .Deriv`. Re-implement both `deductionTheorem` defs (signatures
   preserved) and delete the two `deductionWithMem`. This is the largest and riskiest piece;
   ~25 raw call sites must keep compiling.

### Net deletion estimate
- Eliminated WF bodies + `deductionWithMem`: ~150-230 lines/logic.
- Temporal: pure win (bridge sunk cost). Bimodal: ~+140 bridge lines, ~-230 DT lines, plus
  free MCS equivalences. Modal/Prop: requires new infra (net may be neutral until reused
  elsewhere).

---

## 8. Zero-debt / no-sorry assessment

- The bridge round-trip uses `Nonempty.some` (Classical choice); all four `deductionTheorem`
  defs are already `noncomputable`, so this introduces **no new axiom and no `sorry`** — it
  is the same classical content already present.
- No vacuous definitions are involved; signatures are preserved so the proof obligations of
  downstream consumers are unchanged.
- **No `sorry` deferral is needed or recommended.** If the Modal/Prop infrastructure proves
  too large for one task, the correct action is **plan decomposition / spawning a follow-up
  task** (Phase M/P option 1), NOT a partial proof. Mark Modal/Prop `[BLOCKED]` for user
  review only if the planner cannot accommodate the new abstraction.

---

## 9. CI / verification checklist (from the task)

Run after each phase (scoped) and at the end (full):
- `lake build` (full at end; scoped `lake build Cslib.Logics.<Logic>.Metalogic` per phase)
- `lake test`
- `lake exe checkInitImports`
- `lake exe lint-style`
- `lake shake --add-public --keep-implied --keep-prefix`

Downstream sorry-free consumers to re-verify explicitly: Modal/Temporal/Bimodal
`Completeness`, Bimodal `BXCanonical/TruthLemma` + `Chronicle`, Temporal `Chronicle` +
`DenseCompleteness`, Propositional `StrongCompleteness` + NaturalDeduction `Equivalence`.

---

## 10. Verified line/name reference table

| Symbol | File:line | Status |
|--------|-----------|--------|
| `list_deduction_theorem` | `Foundations/.../ListDeduction.lean:55` | verified |
| `algebraic_has_deduction_theorem` | `Foundations/.../GenericMCS.lean:65` | verified |
| `algebraicDerivationSystem` | `Foundations/.../GenericMCS.lean:54` | verified |
| `set_lindenbaum` | `Foundations/.../Consistency.lean:152` | verified |
| `HasDeductionTheorem` | `Foundations/.../Consistency.lean:182` | verified |
| `MinimalHilbert` | `Foundations/Logic/ProofSystem.lean:342` | verified |
| PL `hasDeductionTheorem` | `Propositional/Metalogic/DeductionTheorem.lean:198` | verified |
| PL `deductionTheorem`/`deductionWithMem` | `…/DeductionTheorem.lean:130/71` | verified |
| Modal `hasDeductionTheorem` | `Modal/Metalogic/DeductionTheorem.lean:177` | verified |
| Modal `deductionTheorem`/`deductionWithMem` | `…/DeductionTheorem.lean:109/50` | verified |
| `temporal_has_deduction_theorem` | `Temporal/Metalogic/DeductionTheorem.lean:167` | verified |
| Temporal `deductionTheorem`/`deductionWithMem` | `…/DeductionTheorem.lean:119/72` | verified |
| `temporal_has_deduction_theorem_fc` | `Temporal/Metalogic/DenseMCS.lean:265` | verified |
| `bimodalHasDeductionTheorem` | `Bimodal/Metalogic/Core/DeductionTheorem.lean:225` | verified |
| Bimodal `deductionTheorem`/`deductionWithMem` | `…/Core/DeductionTheorem.lean:161/83` | verified |
| `temporal_deriv_iff_algebraic` | `Temporal/Metalogic/GenericMCSBridge.lean:188` | verified |
| Modal bridge (doc-only) | `Modal/Metalogic/GenericMCSBridge.lean` (no decls) | verified |
| `prop_lindenbaum` | `Propositional/Metalogic/MCS.lean:60` (delegates) | verified |
| `modal_lindenbaum` | `Modal/Metalogic/MCS.lean:59` (delegates) | verified |
| `temporal_lindenbaum` | `Temporal/Metalogic/MCS.lean:67` (delegates) | verified |
| `bimodal_lindenbaum` | `Bimodal/Metalogic/Core/MaximalConsistent.lean:92` (delegates) | verified |
| Modal `InferenceSystem HilbertK` = `DerivationTree KAxiom []` | `Modal/ProofSystem/Instances/K.lean:62` | verified |
| Temporal `InferenceSystem HilbertBX` = `DerivationTree Base []` | `Temporal/ProofSystem/Instances.lean:43` | verified |
| Bimodal `InferenceSystem HilbertTM` = `DerivationTree Base []` | `Bimodal/ProofSystem/Instances.lean:47` | verified |
