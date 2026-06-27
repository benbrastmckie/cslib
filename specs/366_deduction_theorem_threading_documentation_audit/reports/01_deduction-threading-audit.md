# Research Report: Deduction-Theorem Threading & Documentation Audit (Task 366)

- **Task**: 366 — deduction_theorem_threading_documentation_audit (capstone audit)
- **Session**: sess_1782560395_aeb7ef_366
- **Date**: 2026-06-27
- **Scope**: Deduction-theorem modules + direct consumers across Propositional, Modal,
  Temporal, Bimodal. Per task note, the broken Tableau / Bimodal-Separation subtrees
  owned by task 364 are out of scope.

## Executive Summary

The consolidation through the generic algebraic seam
(`algebraic_has_deduction_theorem` in `GenericMCS.lean`, on top of
`list_deduction_theorem` in `ListDeduction.lean`) is **complete for the
single-frame-class deduction theorems** (Propositional, Modal, and Temporal's
`FrameClass.Base` theorem). All these route through their `*_deriv_iff_algebraic`
bridge with no remaining hand WF-recursion.

However, the audit finds **two material residues** that contradict the task's
premise that "NO logic retains a hand WF-recursion deduction-theorem body," plus a
**factual correction** to the prior task-355 research note about `deductionWithMem`:

1. **Bimodal `deductionTheorem` / `deductionWithMem`** (`Core/DeductionTheorem.lean`)
   still use full structural-match + `termination_by h.height` / `decreasing_by`.
   Only the *instance* `bimodalHasDeductionTheorem` is bridge-routed; the public
   `def deductionTheorem` (≈80 call sites) is **not**.
2. **Temporal `deductionTheoremFc` / `deductionWithMemFc`** (`DenseMCS.lean`) still use
   `termination_by d.height` / `decreasing_by`. The wrapper
   `temporal_has_deduction_theorem_fc` consumes the hand-recursion body, **not** the
   bridge.
3. **`deductionWithMem` is NOT callerless.** The task carried forward a task-355 note
   that PL's `deductionWithMem` "has zero external callers." This is **false**: PL's
   `deductionWithMem` has **4 external callers** and Modal's has **1**. The audit
   decision is therefore **KEEP + document**, not delete.

Root cause of (1) and (2): the algebraic bridge is built at a **single, fixed proof
system** (`Bimodal.HilbertTM` ≅ `FrameClass.Base`; Temporal `temporalDerivationSystem`
at `FrameClass.Base`). The two residual definitions are **polymorphic over an arbitrary
`fc : FrameClass`**, for which no `MinimalHilbert` instance / bridge exists. They cannot
be trivially rerouted without first generalising the bridge to arbitrary `fc`.

All audited deduction modules and their direct consumers **build green and are
sorry-free** (verified by scoped `lake build`; see Verification section).

---

## 1. Residue Inventory (hand-recursion / deductionWithMem)

### 1.1 Bridge-routed (CLEAN — no residue)

| Logic | File | `deductionTheorem` body | Instance | Bridge |
|-------|------|-------------------------|----------|--------|
| Propositional | `Logics/Propositional/Metalogic/DeductionTheorem.lean` | `list_deriv_to_tree ∘ algebraic_has_deduction_theorem ∘ pl_deriv_iff_algebraic.mp` (L66–77) | `hasDeductionTheorem` (L104) bridge-routed | `pl_deriv_iff_algebraic` |
| Modal | `Logics/Modal/Metalogic/DeductionTheorem.lean` | `list_deriv_to_tree ∘ … ∘ modal_deriv_iff_algebraic.mp` (L63–74) | `hasDeductionTheorem` (L101) bridge-routed | `modal_deriv_iff_algebraic` |
| Temporal (Base) | `Logics/Temporal/Metalogic/DeductionTheorem.lean` | `temporal_deriv_iff_algebraic.mpr ∘ … ∘ .mp` (L66–71) | `temporal_has_deduction_theorem` (L76) bridge-routed | `temporal_deriv_iff_algebraic` |

No `termination_by` / `decreasing_by` in any of these three files. Confirmed by
targeted grep over the four `DeductionTheorem.lean` files: only the Bimodal one matches.

### 1.2 Hand WF-recursion RESIDUE (still present)

**(R1) Bimodal — `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean`**

- `deductionWithMem` (L80–130): full 7-arm `match h with` + `termination_by h.height`
  + `decreasing_by` (L126–130).
- `deductionTheorem` (L151–200): full structural match + `termination_by h.height`
  + `decreasing_by` (L194–200).
- `bimodalHasDeductionTheorem` (L214–219): **IS** bridge-routed via
  `bimodal_deriv_iff_algebraic` + `algebraic_has_deduction_theorem`. This is the only
  part of this file that touches the generic seam.
- Module docstring (L26–41) still describes "induction on the derivation structure"
  and "7-constructor DerivationTree" — i.e. documents the *old* hand-recursion design,
  not the consolidated seam. **Docstring is stale.**

**(R2) Temporal (fc-parameterized) — `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean`**

- `deductionWithMemFc` (L178–217): `match d with` + `termination_by d.height`
  + `decreasing_by` (L213–217).
- `deductionTheoremFc` (L220–264): `match d with` + `termination_by d.height`
  + `decreasing_by` (L259–264).
- `temporal_has_deduction_theorem_fc` (L269–274): wraps `deductionTheoremFc` directly
  — **NOT** bridge-routed.

Note: the Temporal *Base* file (`Temporal/Metalogic/DeductionTheorem.lean`) was already
consolidated in a prior task; its own docstring (L38) correctly claims it "eliminates the
hand-written well-founded recursion and `deductionWithMem` helper." The hand recursion
simply migrated to the **fc-parameterized** `DenseMCS.lean` layer, which the task premise
overlooked.

### 1.3 Root cause — why R1/R2 are not (yet) reroutable

- The algebraic path requires `[MinimalHilbert S]`. The bridges are constructed at a
  **single fixed `S`**:
  - Bimodal: `bimodalAlgDS = algebraicDerivationSystem (S := Bimodal.HilbertTM)`, and
    `bimodal_deriv_iff_algebraic` / `list_deriv_to_tree` are hardcoded to
    `DerivationTree FrameClass.Base` (`Core/GenericMCSBridge.lean` L79–215).
  - Temporal: `temporal_deriv_iff_algebraic` is at `FrameClass.Base`
    (`temporalDerivationSystem`).
- `Bimodal.deductionTheorem {fc}` and `Temporal.deductionTheoremFc {fc}` are **generic
  over `fc : FrameClass`**. There is no `MinimalHilbert` instance / bridge for an
  arbitrary `fc`, so the generic seam is unavailable for these signatures.
- Consequence: rerouting R1/R2 is **not a thin re-route**. It requires either
  (a) generalising the bridge to arbitrary `fc` (build a per-`fc`
  `InferenceSystem`+`MinimalHilbert` for `HilbertOf`-style tag at `fc`), then routing
  `deductionTheoremFc`/`deductionTheorem {fc}` through it; or (b) a documented design
  decision that the fc-polymorphic layer retains structural recursion while the
  `FrameClass.Base` instance (the one the generic MCS framework actually consumes)
  routes through the seam. **This is a planning decision flagged below.**

### 1.4 `deductionWithMem` helper status (FACTUAL CORRECTION)

| Logic | `deductionWithMem` impl | External callers | Decision |
|-------|-------------------------|------------------|----------|
| Propositional | rerouted on top of `deductionTheorem` (L85–96), `noncomputable def` | **4**: `IntLindenbaum.lean:148`, `MinLindenbaum.lean:131`, `StrongCompleteness.lean:447`, `Semantics/SemanticConsequence.lean:159` | **KEEP + document** |
| Modal | rerouted on top of `deductionTheorem` (L82–93) | **1**: `Modal/Metalogic/Completeness.lean:542` | **KEEP + document** |
| Bimodal | hand WF-recursion (L80–130) | internal only (called by `deductionTheorem` L98,99,110,177) | bound to R1; keep iff R1 kept |
| Temporal (`deductionWithMemFc`) | hand WF-recursion (DenseMCS L178–217) | internal only (called by `deductionTheoremFc` L192,193,201,244) | bound to R2; keep iff R2 kept |

**Correction to task premise**: the carried-forward note "the `deductionWithMem` helper …
has zero external callers" is incorrect for the PL (and Modal) helpers — they are
load-bearing in StrongCompleteness, both Lindenbaum constructions, and
SemanticConsequence. Deleting either PL or Modal `deductionWithMem` would break those
consumers. The correct outcome is to **retain them and add a short docstring note** that
they are a thin `removeAll`-aware wrapper over the seam-routed `deductionTheorem`, kept
because removing-all-occurrences is the shape required by Lindenbaum/consistency
elimination.

---

## 2. Downstream Consumer Threading (all sorry-free, all green)

`grep` for `sorry`/`admit` across all deduction modules + four bridges: **none found.**
Every consumer reaches the deduction theorem either through the seam-routed
`*_has_deduction_theorem` instance or through the (still structurally-defined but
sorry-free) `deductionTheorem` def. No signature drift was observed: all call sites use
the published `deductionTheorem (… ) Γ A B d` / `deductionWithMem (…)` shapes.

### Instance-routed consumers (MCS closure properties)

- **Propositional**: `MCS.lean`, `MinLindenbaum.lean`, `IntLindenbaum.lean`,
  `StrongCompleteness.lean` thread `hasDeductionTheorem` into
  `SetMaximalConsistent.closed_under_derivation / implication_property /
  negation_complete`.
- **Modal**: `MCS.lean`, `Completeness.lean`, `Systems/K/Completeness.lean`,
  `Systems/D/Completeness.lean`.
- **Temporal**: `MCS.lean` (Base), `DenseMCS.lean` (fc via
  `temporal_has_deduction_theorem_fc`), `Completeness.lean`, `DenseCompleteness.lean`.
- **Bimodal**: `Core/MaximalConsistent.lean`, `Core/MCSProperties.lean`,
  `Core/RestrictedMCS.lean`, `Algebraic/UltrafilterMCS.lean`, `Completeness.lean`, plus
  the Bundle / BXCanonical TruthLemma / Frame consumers — all via the polymorphic
  `deductionTheorem` def (which is itself green/sorry-free, just not seam-routed).

### Raw `deductionTheorem` call sites

~25+ raw `DerivationTree`-level call sites exist (TruthLemma, ProofSystemEquivalence /
`NaturalDeduction/Equivalence.lean` + `FromHilbert.lean`, RestrictedMCS, WitnessSeed,
PointInsertion, RRelation, etc.). All compiled green in the scoped builds; none exhibit
signature drift. The `NaturalDeduction` equivalence (`Equivalence.lean:285`,
`FromHilbert.lean:80,146`) — the "ProofSystemEquivalence" consumer named in the task —
consumes `deductionTheorem inst.h_K inst.h_S …` and builds green.

---

## 3. Verification (scoped `lake build`, task-364 subtree excluded)

All commands returned `Build completed successfully` / `EXIT: 0`:

1. Deduction core + seam:
   `Foundations.Logic.Metalogic.GenericMCS`,
   `Propositional/Modal/Temporal.Metalogic.DeductionTheorem`,
   `Bimodal.Metalogic.Core.DeductionTheorem`, `Temporal.Metalogic.DenseMCS` — 655 jobs, OK.
2. Consumers: `Propositional StrongCompleteness / MinLindenbaum / IntLindenbaum / MCS /
   Semantics.SemanticConsequence`, `Modal Completeness / MCS`, `Temporal MCS /
   Completeness`, `Bimodal Completeness` — 998 jobs, OK.
3. Equivalence + extras: `Propositional.NaturalDeduction.Equivalence / FromHilbert`,
   `Bimodal.Core.MaximalConsistent`, `Temporal.DenseCompleteness` — 962 jobs, OK.

Confirms: zero behavioural regressions in the in-scope tree; the only RED in the library
is the pre-existing task-364 Tableau/Bimodal-Separation breakage, which is untouched here.

---

## 4. Documentation Deliverables (exact)

The task requires "a single authoritative architecture docstring … explaining the
predicate→type `HilbertOf` bridge and how the four structural logics inherit one
deduction theorem." Current state:

- **`HilbertOf` is per-logic, not central.** It is defined as an empty `inductive
  HilbertOf (Axioms …)` in each predicate-axiom bridge
  (`Propositional/Metalogic/GenericMCSBridge.lean` L86; Modal bridge analogously).
  Bimodal/Temporal instead bridge a concrete `HilbertTM` / `temporalDerivationSystem`
  (no `HilbertOf`). There is currently **no single doc** tying these together.
- The PL bridge (`GenericMCSBridge.lean`) and PL `DeductionTheorem.lean` already carry
  **good module docstrings** (the new files from 355). These need only minor
  cross-reference additions, not rewrites.

### D1 — Authoritative architecture docstring (NEW)
Add to `Foundations/Logic/Metalogic/GenericMCS.lean` (preferred home; it already owns
`algebraic_has_deduction_theorem` and `HasMinimalAxioms`). Content:
- The `listImp` → `ListDeriv` → `algebraic_has_deduction_theorem` chain (one generic
  proof, no per-logic tree induction).
- The predicate→type pattern: `HasMinimalAxioms Axioms` (predicate level) →
  `HilbertOf Axioms` empty tag type → `MinimalHilbert (HilbertOf Axioms)` instance →
  algebraic path, with the per-logic `*_deriv_iff_algebraic` bridge closing the loop
  back to `DerivationTree`.
- An explicit **frame-class caveat**: the seam services single-frame-class systems
  (`FrameClass.Base` / `HilbertTM`); the fc-polymorphic Bimodal/Temporal deduction
  theorems (R1/R2) retain structural recursion and why (see §1.3).

### D2 — Curated module docstrings (REVISE)
- `Propositional/Metalogic/DeductionTheorem.lean`: docstring already describes the
  re-route (L29–35); add a one-line note on `deductionWithMem`'s 4 real callers and a
  cross-ref to D1. **Do not** keep any "zero callers / candidate for deletion" framing.
- `Propositional/Metalogic/GenericMCSBridge.lean`: already strong (L12–64); add cross-ref
  to D1.
- `Bimodal/Metalogic/Core/DeductionTheorem.lean`: docstring (L26–41) is **stale** — it
  documents hand-recursion as the design. Either (a) if R1 is rerouted, rewrite to the
  seam; or (b) if R1 is retained by design, rewrite to state explicitly *why* the
  fc-polymorphic body cannot use the seam, cross-referencing D1 and the Base-only
  `bimodalHasDeductionTheorem` instance.
- `Temporal/Metalogic/DenseMCS.lean`: add a docstring note on `deductionTheoremFc` /
  `deductionWithMemFc` mirroring the Bimodal decision (R2 parallels R1).

### D3 — Cross-reference resolution
Ensure each `DeductionTheorem.lean` / bridge `## References` block points to D1 and to
the sibling logics' files. Current reference blocks are mostly present but do not point
at a single authoritative doc (because none exists yet).

---

## 5. Concrete Punch-List for Implementation Phase

**Decision gate (must resolve first):** For R1 (Bimodal) and R2 (Temporal-fc), choose:
- **Option A (full consolidation)**: generalise the algebraic bridge to arbitrary
  `fc : FrameClass` (per-`fc` `InferenceSystem` + `MinimalHilbert` for the tag type),
  then reroute `deductionTheorem {fc}` / `deductionTheoremFc` through it and delete the
  hand recursion + internal `deductionWithMem(Fc)`. Higher effort; achieves the task's
  literal "no hand WF-recursion" goal. Must stay sorry-free and zero-behavioural-change.
- **Option B (documented design boundary)**: retain R1/R2 structural recursion, document
  that the seam covers the `FrameClass.Base` instances consumed by the generic MCS
  framework while the fc-polymorphic public defs keep structural recursion by necessity.
  Lower effort; requires honest docstrings (D2) and updating the task-366 premise.

Recommended: confirm Option A feasibility early (does a per-`fc` `MinimalHilbert` instance
type-check?); fall back to Option B if the per-`fc` instance is not constructible without
new axioms. **Do not** introduce `sorry` or axioms to force Option A.

Ordered tasks:
1. **[decision]** Resolve Option A vs B for R1/R2 (spike: attempt a per-`fc`
   `MinimalHilbert`/bridge for one frame class; if green, do A, else B).
2. **[code, if A]** Generalise `Core/GenericMCSBridge.lean` (and Temporal bridge) to
   arbitrary `fc`; reroute `Bimodal.deductionTheorem` + `deductionWithMem` and
   `Temporal.deductionTheoremFc` + `deductionWithMemFc`; remove `termination_by` blocks.
   Scoped build of all consumers must stay green/sorry-free.
3. **[doc D1]** Add authoritative architecture docstring to `GenericMCS.lean` (predicate→
   type `HilbertOf` bridge; one-deduction-theorem inheritance; frame-class caveat).
4. **[doc D2]** Revise the four `DeductionTheorem.lean` / `DenseMCS` docstrings:
   - PL: correct the `deductionWithMem` caller framing (4 callers, KEEP).
   - Bimodal: replace stale hand-recursion narrative per the chosen option.
   - Temporal DenseMCS: add fc deduction-theorem note.
5. **[doc D3]** Resolve `## References` cross-refs to D1 across all bridge/DT files.
6. **[keep + annotate]** Retain PL & Modal `deductionWithMem` (load-bearing); add the
   one-line "thin removeAll wrapper over seam-routed deductionTheorem" docstring note.
7. **[verify]** Re-run scoped builds (the three batches in §3) + `lake exe
   checkInitImports` on touched files. Do **not** attempt full-library `lake build`
   (RED from task-364); document that exclusion in the summary.

---

## 6. Notes / Risks

- **Zero-debt**: every in-scope module is already sorry-free; the implementation must not
  regress this. If Option A cannot be completed sorry-free, prefer Option B over any
  `sorry`/axiom.
- **No signature drift** observed; any re-route must preserve the public signatures of
  `deductionTheorem` and `deductionWithMem(Fc)` so the ~25+ raw call sites stay valid.
- **Out of scope**: Tableau / Bimodal-Separation subtrees (task 364). Do not build or edit.
