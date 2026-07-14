# Implementation Plan: Generalize GenericMCSBridge — hoist the shared MCS-bridge trio into Foundations

- **Task**: 452 - Generalize GenericMCSBridge: hoist shared MCS-bridge trio into Foundations and collapse base/Fc duplication
- **Status**: [COMPLETED]
- **Effort**: 8 hours (7 hours excluding the optional Phase 6)
- **Dependencies**: None (task-level). Coordinate ordering with 441 (Modal native refactor) and 449-451 (BX+); see Risks.
- **Research Inputs**: reports/01_generalize-genericmcsbridge.md
- **Artifacts**: plans/01_hoist-mcs-bridge-foundations.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

The four `GenericMCSBridge.lean` files (Propositional 256 L, Modal 267 L, Temporal 370 L,
Bimodal/Core 405 L; 1298 L across the bridges) share a near-verbatim skeleton whose backward
direction (`unfoldListImpInTree`, `listDerivToTree`) and consistency/MCS transfer lemmas
(`_setConsistent_iff_algebraic`, `_setMaxConsistent_iff_algebraic`) contain no logic-specific
content, while Temporal and Bimodal additionally duplicate their own base↔Fc sections inside a
single file. This plan executes the research-validated two-part refactor: **Part A** collapses the
Temporal/Bimodal intra-file base↔Fc duplication (the base helpers are definitionally equal to the
existing `_fc` versions, so they become one-line delegations after reordering the `_fc` block above
the base block), and **Part B** extracts the shared machinery into the *existing*
`Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` (167 L) behind a new data-carrying typeclass
`HilbertTree (D : List F → F → Type*)`, reducing each per-logic bridge to a thin instantiation.
Definition of done: shared abstraction in Foundations, all four bridges reduced to thin
instantiations, full CI green, and **zero new sorries or axioms** (the refactor only moves existing
sorry-free proofs). Every deletion is gated on a prior compile of its replacement.

The plan is sized so each phase fits one implementation-agent run. It refines the task's requested
Phase 0-4 narrative into finer, independently-committable phases:

- Requested **Phase 0** (baseline gate) -> Phase 0.
- Requested **Phase 1 / Part A** (base↔Fc collapse) -> Phases 1 (Temporal) + 2 (Bimodal).
- Requested **Phase 2 / Part B core** (typeclass + hoist + retarget) -> Phases 3 (add generic
  module) + 4 (retarget Temporal/Bimodal) + 5 (retarget PL/Modal).
- Requested **Phase 3** (optional tag boilerplate) -> Phase 6.
- Requested **Phase 4** (final CI + accounting) -> Phase 7.

### Research Integration

Built directly on reports/01_generalize-genericmcsbridge.md, which is API-grounded. Key findings
carried into this plan verbatim:
- Part A base↔Fc defeq (§3.2): `temporalAlgDS.Deriv` and `temporalAlgDSFc .Base .Deriv` both reduce
  to `Nonempty (DerivationTree .Base [] (listImp Γ φ))`; base helpers become delegations. Constraint:
  the `_fc` block currently sits *below* the base block and must be reordered above it (Lean scoping).
- Part B needs a NEW typeclass `HilbertTree` (§2.2) — no existing Foundations abstraction
  (InferenceSystem, MinimalHilbert, HasAxiomImplyK/S, algebraicDerivationSystem, ListDeriv,
  DtSystem, DeductionCharacterization) captures a `Type`-valued contextual tree family.
- PATH COLLISION (§4.1): `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` already exists (167 L).
  This plan EXTENDS it (no overwrite, no new barrel entry, no `mk_all` needed). No import cycle
  (§4.2): new material is parametric over abstract `F`/`D` and imports no `Cslib/Logics/*`.
- The forward `derivTreeToList` induction is IRREDUCIBLY per-logic (§1.2, §2.4) — left in place.
- Public names to preserve (§4.3-§4.4): tags `HilbertBX(Fc)`/`HilbertTM(Fc)` (22 downstream
  `HasAxiom` instances); the three iff-theorems per logic; `listDerivToTree` (external: PL+Modal DT).
- Zero-debt is achievable (§8.6): refactor moves existing sorry-free proofs, gated on a Phase-0
  green baseline and per-phase compile-before-delete discipline.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` supplied and no ROADMAP.md consulted for this task. The task originates from
review 2026-07-01-2 (HIGH) as a Foundations deduplication follow-up to the 415 lifting audit.

## Goals & Non-Goals

**Goals**:
- Collapse Temporal and Bimodal intra-file base↔Fc duplication (Part A), replacing base
  forward/helper/backward bodies with one-line delegations to the `_fc` versions.
- Introduce `HilbertTree (D : List F → F → Type*)` plus `ClosedHilbert` tag, generic
  `unfoldListImp`/`listDerivToTree`, `deriv_iff_algebraic_of_forward`, and the two
  `*_iff_congr` transfer lemmas into the existing `Foundations/.../GenericMCS.lean` (Part B).
- Reduce all four per-logic bridges to thin `HilbertTree` instantiations + per-logic forward
  induction + thin public-name re-exports.
- Preserve every externally-referenced public name and statement (tags, three iff-theorems,
  `listDerivToTree`, `*AlgDS`, `*_fc` theorems).
- Full CI green (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake`) and zero new sorries/axioms, verified with `lean_verify` on the moved defs.
- Eliminate ~300-330 lines (up to ~385 with optional Phase 6).

**Non-Goals**:
- Hoisting the forward `derivTreeToList` induction (irreducibly per-logic; stays put).
- Replacing the `HilbertBX(Fc)`/`HilbertTM(Fc)` tag types with the generic `ClosedHilbert` tag
  (they carry 22 downstream `HasAxiom` instances; must stay).
- Any semantic change to derivability, consistency, or MCS behavior — this is a pure refactor.
- Creating a new sibling file (`TreeBridge.lean`); extend the existing `GenericMCS.lean` instead.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Base↔Fc defeq (§3.2) argued from source, not yet compiled | H | M | Phase 1/2 add the `_fc`-above-base reorder and prove each base delegation compiles BEFORE deleting any base body. Do not delete a proof body until its delegation builds. |
| `treeAlgDS`/`ClosedHilbert` universe mismatch (`DerivationTree : Type u` vs `InferenceSystem.derivation : Sort v`) (§8.3) | H | M | Phase 3 builds the generic module in isolation first; check `S := ClosedHilbert D` elaboration against `algebraicDerivationSystem`'s `[InferenceSystem S F]` before any retarget. |
| `HilbertTree` implicit `{Γ Δ φ}` binders vs explicit concrete constructor args (§8.4) | M | M | Per-logic instance adapts binder explicitness (worked example in §6); confirm elaboration in Phase 4/5 on first instance before propagating. |
| Definition-ordering regression in Temporal/Bimodal after reorder (§8.2) | M | M | Pure reordering; verify with targeted `lake build` of the single module before broadening. |
| Breaking an externally-referenced public name | H | L | Design rule (§4.3): keep every externally-referenced name as a thin `def`/`theorem`/`abbrev` at its current signature; only bodies move. Grep for callers before/after each retarget. |
| Collision with 441 (Modal native refactor, PLANNED, ~1.5-2k L) | M | L | 441 changes `Modal.Proposition` constructors, not `DerivationTree` constructors the Modal bridge inducts on; Modal bridge survives with at most a rebase. 452's Modal touch is tiny (one instance + delegations). Coordinate ordering; land 441 before/clearly separated from Phase 5. |
| Collision with 449-451 (BX+, NOT STARTED) | L | L | Forward-compatible: Temporal bridge already `fc`-polymorphic; generic `HilbertTree (DerivationTree fc)` + `base_le fc` cover a new `FrameClass.Metric` automatically. Preserve public names -> trivial rebase either order. |
| Introducing a new proof obligation needing `sorry` | H | L | Refactor MOVES existing sorry-free proofs; no new obligations. Phase 7 `lean_verify` on every moved/generic def confirms zero axioms/sorries. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | 1, 2, 3 | 0 |
| 3 | 4, 5 | 1, 2, 3 (Phase 4); 3 (Phase 5) |
| 4 | 6 | 5 |
| 5 | 7 | 4, 5, 6 |

Phases within the same wave can execute in parallel. Phase 6 is optional; if skipped, Phase 7
depends only on 4 and 5. Phases 1, 2, 3 touch disjoint files (Temporal bridge / Bimodal bridge /
Foundations module) and are safely parallel. Phases 4 and 5 touch disjoint files
(Temporal+Bimodal / PL+Modal) and are safely parallel.

---

### Phase 0: Baseline green gate and line-count snapshot [COMPLETED]

**Goal**: Establish a known-green baseline and record current line counts of the four bridge files
and `GenericMCS.lean` for the final elimination accounting. No source edits.

**Tasks**:
- [x] Run the full CI baseline to confirm a green starting point: `lake build`, `lake test`,
      `lake exe checkInitImports`, `lake exe lint-style`.
- [x] Record exact line counts: `wc -l` on
      `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean`,
      `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`,
      `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`,
      `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`,
      `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`. (Reference baseline: 256 / 267 / 370 /
      405 / 167.) Confirmed exact match: 256 / 267 / 370 / 405 / 167.
- [x] Write the baseline numbers into the summary/handoff so Phase 7 can compute net elimination.
- [x] Grep-confirm the external-reference set (§4.3) so Phases 4-5 know which names to preserve:
      `listDerivToTree`, `temporalAlgDS`, `temporal_deriv_iff_algebraic(_fc)`, `HilbertBXFc`,
      `bimodal_deriv_iff_algebraic(_fc)`, `HilbertTMFc`, `modal_deriv_iff_algebraic`,
      `pl_deriv_iff_algebraic`. Confirmed: all resolve exactly as documented in the research report.

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**: none (read/verify only).

**CI gate**: `lake build` (must be green before proceeding). No deletions yet.

**Verification**:
- Baseline CI is green; line counts recorded; external-reference grep list captured.

---

### Phase 1: Part A.1 — Temporal base↔Fc collapse [COMPLETED]

**Goal**: Reorder the Temporal `_fc` block above the base block and rewrite the three base bodies
(`derivTreeToList`, `unfoldListImpInTree`, `listDerivToTree`) as one-line delegations to their
`_fc` counterparts at `fc := .Base`, preserving all public names and statements.

**Tasks**:
- [x] Move the `_fc` block (currently ~L239-370) above the base block (currently ~L66-221) so the
      `_fc` definitions are in scope first (Lean scoping requirement, §3.3).
- [x] Rewrite base `derivTreeToList d := derivTreeToListFc d`, `unfoldListImpInTree Ψ d h_sub :=
      unfoldListImpInTreeFc (fc := .Base) Ψ d h_sub`, `listDerivToTree h := listDerivToTreeFc
      (fc := .Base) h` (bodies from §3.3; each typechecks by the §3.2 defeq).
- [x] Compile the delegations BEFORE deleting the old base bodies; only then remove the old bodies.
- [x] Keep `temporalAlgDS`, `temporal_deriv_iff_algebraic`, and all `_fc` names/statements intact.

**Result**: 370L -> 306L (64L reduction). `lean_verify` on `derivTreeToList`, `listDerivToTree`,
`temporal_deriv_iff_algebraic` all report `["propext","Classical.choice"]` only (zero-debt).

**Timing**: 1 hour

**Depends on**: 0

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — reorder `_fc` above base; base
  helpers become delegations (~60 L net reduction).

**CI gate**: `lake build Cslib.Logics.Temporal.Metalogic.GenericMCSBridge` then the full quartet
`lake build && lake test && lake exe checkInitImports && lake exe lint-style`. Commit
`task 452 phase 1: collapse Temporal base/Fc duplication`.

**Verification**:
- Targeted module builds; full CI green; `temporalAlgDS`/`temporal_deriv_iff_algebraic` and the
  `_fc` theorems still resolve (grep + build of Temporal `DeductionTheorem.lean`, `MCS.lean`,
  `DenseMCS.lean`).

---

### Phase 2: Part A.2 — Bimodal base↔Fc collapse [COMPLETED]

**Goal**: Same collapse as Phase 1 applied to the Bimodal/Core bridge (`HilbertTMFc`), preserving
`bimodal_deriv_iff_algebraic`, `bimodal_deriv_iff_algebraic_fc`, and `HilbertTMFc`.

**Tasks**:
- [x] Move the Bimodal `_fc` block (currently ~L244-405) above the base block (~L66-243).
- [x] Rewrite the three base bodies as delegations to the `_fc` versions at `fc := .Base`.
- [x] Compile delegations before deleting old base bodies.
- [x] Preserve `bimodalAlgDS`, `bimodal_deriv_iff_algebraic(_fc)`, `HilbertTMFc`.

**Result**: 405L -> 330L (75L reduction). `lean_verify` on `derivTreeToList`,
`bimodal_deriv_iff_algebraic` report `["propext","Classical.choice"]` only (zero-debt).

**Timing**: 1 hour

**Depends on**: 0

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — reorder + delegate (~70 L net
  reduction).

**CI gate**: `lake build Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge` then
`lake build && lake test && lake exe checkInitImports && lake exe lint-style`. Commit
`task 452 phase 2: collapse Bimodal base/Fc duplication`.

**Verification**:
- Targeted module builds; full CI green; Bimodal `Core/DeductionTheorem.lean` still resolves the
  preserved names.

---

### Phase 3: Part B core.1 — Add the generic `HilbertTree` module to Foundations [COMPLETED]

**Goal**: Extend the EXISTING `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` with the generic
tree-bridge machinery and build it in isolation. No per-logic edits in this phase.

**Tasks**:
- [x] Add into `namespace Cslib.Logic.Metalogic.GenericMCS` (signatures from §2.2-§2.3, §6):
  - `class HilbertTree (D : List F → F → Type*)` — 5 fields
    (`assumption`, `mp`, `weakening`, `axiomK`, `axiomS`).
  - `structure ClosedHilbert (D)` + `InferenceSystem` / `ModusPonens` / `HasAxiomImplyK` /
    `HasAxiomImplyS` / `MinimalHilbert` instances + `@[reducible] def treeAlgDS`.
  - `noncomputable def unfoldListImp` (generic backward helper).
  - `noncomputable def listDerivToTree` (generic backward direction).
  - `theorem deriv_iff_algebraic_of_forward` (assembles the deriv-iff from a per-logic forward map).
  - `theorem setConsistent_iff_congr`, `theorem setMaxConsistent_iff_congr` (pure
    `DerivationSystem` transfer lemmas — no tree, zero-risk).
- [x] Confirm the universe check: `S := ClosedHilbert D` elaborates against
      `algebraicDerivationSystem`'s `[InferenceSystem S F]` (Risk row 2); adjust universe
      annotations if needed. Compiled clean on first attempt, no universe annotations needed
      (`InferenceSystem.derivation : α → Sort v` already accommodates `D [] φ : Type*`).
- [x] Do NOT create a sibling file and do NOT touch the barrel (extending an existing module means
      no `lake exe mk_all --module` needed).
- [x] `lean_verify` each new def/theorem for zero axioms/sorries as soon as it compiles.

**Result**: 167L -> 290L (+123L; within the ~50L-plus-docstrings cost side of the elimination
accounting). `lean_verify` on `unfoldListImp`, `listDerivToTree`, `deriv_iff_algebraic_of_forward`,
`setConsistent_iff_congr`, `setMaxConsistent_iff_congr` all report only the standard trusted set
(propext/Classical.choice) or empty — zero-debt confirmed. Full CI green (one transient
filesystem I/O error on an unrelated file during the first `lake build`, resolved on retry).

**Timing**: 1.5 hours

**Depends on**: 0

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — add ~50 L of generic material (extend, do
  not overwrite the existing 167 L).

**CI gate**: `lake build Cslib.Foundations.Logic.Metalogic.GenericMCS` in isolation, then
`lake build && lake exe checkInitImports && lake exe lint-style`. Commit
`task 452 phase 3: add generic HilbertTree bridge to Foundations`.

**Verification**:
- Foundations module builds standalone; downstream bridges still build (they gain symbols, lose
  none); `lean_verify` reports zero axioms/sorries on the new defs.

---

### Phase 4: Part B core.2 — Retarget Temporal & Bimodal to the generic machinery [COMPLETED]

**Goal**: Replace the Temporal and Bimodal `_fc` backward helpers with delegations to the generic
`unfoldListImp`/`listDerivToTree` via a `HilbertTree (DerivationTree fc)` instance, and replace the
two consistency/MCS lemmas with `setConsistent_iff_congr`/`setMaxConsistent_iff_congr`. Keep the
`HilbertBX(Fc)`/`HilbertTM(Fc)` tags and `MinimalHilbert` boilerplate local (§4.4). Preserve all
public theorem names.

**Tasks**:
- [x] Temporal: add `instance (fc : FrameClass) : HilbertTree (F := Formula Atom) (DerivationTree
      fc)` (worked example, §6); retarget `unfoldListImpInTreeFc`/`listDerivToTreeFc` bodies (or the
      already-delegating base helpers) to the generic combinators; replace
      `temporal_setConsistent_iff_algebraic`/`temporal_setMaxConsistent_iff_algebraic` bodies with
      the generic `*_iff_congr`. Keep public names/statements.
- [x] Bimodal: same retarget with `HilbertTMFc`.
- [x] Compile each retarget before deleting the replaced bodies.
- [x] Confirm implicit `{Γ Δ φ}` binder adaptation on the first instance (Risk row 3) before
      propagating to the second.

**Result**: Temporal 306L -> 299L, Bimodal 330L -> 325L. `#print axioms` (via `lean_run_code`,
bypassing stale-LSP `lean_verify` results caused by a concurrently-broken unrelated file) confirms
`listDerivToTreeFc`/`unfoldListImpInTreeFc`/`*_setMaxConsistent_iff_algebraic` for both logics
depend only on `propext`/`Classical.choice` — zero-debt confirmed.

**Deviation discovered**: Bimodal's `HilbertTree (F := ...) (...)` named-argument instance syntax
(which worked verbatim for Temporal) produces a raw parser error in the Bimodal file because
Bimodal's temporal `F` (future) notation shadows the bare identifier `F`, forcing Lean to
auto-bind the class's implicit type parameter as the escaped `«F»`. Fixed by using the fully
positional form `@HilbertTree (Bimodal.Formula Atom) _ (Bimodal.DerivationTree fc) where ...`
instead of `HilbertTree (F := ...) (...) where ...`. Documented inline in the instance's docstring.

**Environment note**: two `lake build` runs on the full project failed transiently in unrelated
files (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`,
`Cslib/Logics/Temporal/Tableau/Saturation.lean`) due to concurrently-running tasks 439/317
actively editing those files mid-session (confirmed via `git diff --stat` showing uncommitted
changes to those files, unrelated to this task's diff). CI gate for this phase was verified via
scoped `lake build` of all directly-touched and downstream-importing modules (all green), plus
`lake exe lint-style` (clean) and `#print axioms` zero-debt checks. Full-project `lake build`/
`lake test`/`checkInitImports` deferred to Phase 7 pending the concurrent tasks' completion.

**Timing**: 1.5 hours

**Depends on**: 1, 2, 3

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — HilbertTree instance + delegations.
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — HilbertTree instance + delegations.

**CI gate**: targeted `lake build` of both modules, then
`lake build && lake test && lake exe checkInitImports && lake exe lint-style`. Commit per logic
where feasible: `task 452 phase 4: retarget Temporal bridge to generic HilbertTree` and
`task 452 phase 4: retarget Bimodal bridge to generic HilbertTree`.

**Verification**:
- Both modules build; full CI green; preserved names (`temporalAlgDS`,
  `temporal_deriv_iff_algebraic(_fc)`, `HilbertBXFc`, `bimodal_deriv_iff_algebraic(_fc)`,
  `HilbertTMFc`) still resolve from their importers.

---

### Phase 5: Part B core.3 — Retarget PL & Modal to the generic machinery [COMPLETED]

**Goal**: Add `HilbertTree (DerivationTree Axioms)` instances for PL and Modal; delegate the
backward helpers and the two consistency/MCS lemmas to the generic combinators; KEEP the public
`listDerivToTree` name at its current signature (external callers: PL and Modal
`DeductionTheorem.lean`). Keep the `HilbertOf` tags local for now (Phase 6 optionally retires them).

**Tasks**:
- [x] PL: add `HilbertTree (DerivationTree Axioms)` instance with `axiomK`/`axiomS` from
      `HasMinimalAxioms.hasImplyK/hasImplyS` via `DerivationTree.ax` (§6); retarget
      `unfoldListImpInTree`/`listDerivToTree` bodies to the generic combinators; replace the two
      consistency lemmas with `*_iff_congr`; preserve `pl_deriv_iff_algebraic`, `propAlgDS`, and the
      public `listDerivToTree`.
- [x] Modal: same retarget; preserve `modal_deriv_iff_algebraic`, `modalAlgDS`, and the public
      `listDerivToTree`. Leave the `necessitation` arm of the forward induction untouched (per-logic).
- [x] Compile each retarget before deleting replaced bodies; grep to confirm `listDerivToTree`
      callers in `DeductionTheorem.lean` still resolve.

**Result**: PL 256L -> 236L, Modal 267L -> 246L. `lake build` of both bridge files AND their
downstream importers (`Propositional/Metalogic/DeductionTheorem.lean`,
`Modal/Metalogic/DeductionTheorem.lean`) green, confirming the public `listDerivToTree` name
still resolves for both external callers. `#print axioms` on `listDerivToTree`,
`unfoldListImpInTree`, `*_setMaxConsistent_iff_algebraic` for both logics: only
`propext`/`Classical.choice` -- zero-debt confirmed. `unfoldListImpInTree` gained a new
`[HasMinimalAxioms Axioms]` constraint (needed to supply the `HilbertTree` instance); safe per
the research report's external-reference table (`unfoldListImpInTree` has no external callers).
`lake exe lint-style` clean. Full-repo `lake build` still blocked by the same concurrently-running
task 439 Saturation.lean issue noted in Phase 4 (unrelated file, unrelated to this diff).

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` — HilbertTree instance + delegations.
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` — HilbertTree instance + delegations.

**CI gate**: targeted `lake build` of both modules, then
`lake build && lake test && lake exe checkInitImports && lake exe lint-style`. Commit
`task 452 phase 5: retarget PL and Modal bridges to generic HilbertTree`.

**Verification**:
- Both modules build; PL/Modal `DeductionTheorem.lean` still resolve `listDerivToTree` and the
  `*_deriv_iff_algebraic` names; full CI green.

---

### Phase 6: (Optional) PL/Modal adopt the `ClosedHilbert` tag [COMPLETED]

**Goal**: If budget allows, retire the remaining PL/Modal tag + `MinimalHilbert` boilerplate by
adopting the generic `ClosedHilbert (DerivationTree Axioms)` tag (their `HilbertOf` tags have no
external references, §4.4), for a further ~55 L saving. Higher-touch; skip if time-constrained.

**Tasks**:
- [x] PL: replace the local `HilbertOf` tag + instance bundle with the generic `ClosedHilbert`
      tag/instances; keep `pl_deriv_iff_algebraic` and `propAlgDS` as thin re-exports.
- [x] Modal: same, keeping `modal_deriv_iff_algebraic` and `modalAlgDS`.
- [x] Confirm no external caller referenced the retired `HilbertOf` tag (grep).

**Result**: PL 235L -> 201L (34L further reduction), Modal 246L -> 213L (33L further
reduction); 67L total from Phase 6. `propAlgDS`/`modalAlgDS` became one-line aliases to
`treeAlgDS (...DerivationTree Axioms)`. Discovered the same Lean-scoping requirement as
Phase 1/2: the `HilbertTree` instance must be declared BEFORE `propAlgDS`/`modalAlgDS`
(which now call `treeAlgDS`, requiring the instance in scope) -- reordered accordingly.
`#print axioms` on `pl_deriv_iff_algebraic`, `derivTreeToList`, `listDerivToTree` (both
logics): only `propext`/`Classical.choice` -- zero-debt confirmed. Grep confirms zero
remaining code references to the retired `HilbertOf` tag in either logic (only doc-comment
mentions, which were updated to reference `ClosedHilbert`). Full CI green: `lake build`,
`lake exe checkInitImports`, `lake exe lint-style`, `lake test`, `lake shake` (zero
suggestions on all 5 touched files).

**Timing**: 1 hour

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean`.
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`.

**CI gate**: targeted `lake build` of both modules, then
`lake build && lake test && lake exe checkInitImports && lake exe lint-style`. Commit
`task 452 phase 6: PL/Modal adopt generic ClosedHilbert tag`.

**Verification**:
- Both modules build; full CI green; no dangling references to the retired `HilbertOf` tags.

---

### Phase 7: Final CI gate, zero-debt verification, and elimination accounting [COMPLETED]

**Goal**: Run the complete CI pipeline, verify zero new sorries/axioms on all moved/generic defs,
and compute net line elimination against the Phase-0 baseline.

**Tasks**:
- [x] Full pipeline: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
      `lake shake --add-public --keep-implied --keep-prefix`.
- [x] `lean_verify` (fully-qualified) on the generic defs and the preserved per-logic theorems, e.g.
      `Cslib.Logic.Metalogic.GenericMCS.listDerivToTree`,
      `Cslib.Logic.Metalogic.GenericMCS.unfoldListImp`,
      `Cslib.Logic.Metalogic.GenericMCS.setConsistent_iff_congr`,
      `Cslib.Logic.Metalogic.GenericMCS.setMaxConsistent_iff_congr`,
      `Cslib.Logic.Metalogic.GenericMCS.deriv_iff_algebraic_of_forward`, plus each
      `*_deriv_iff_algebraic(_fc)` — assert zero `sorry`/`axiom` beyond the standard trusted set.
      (Used `#print axioms` via `lean_run_code` for the definitive check, since `lean_verify` was
      intermittently affected by stale LSP state from the concurrent tasks noted in Phase 4/5.)
- [x] `wc -l` the four bridges + `GenericMCS.lean`; compute net reduction vs the Phase-0 baseline
      (target ~300-330 L eliminated, up to ~385 L if Phase 6 ran). Record in the summary.
- [x] Confirm the full external-reference set from Phase 0 still resolves.

**Final CI results** (all green):
- `lake build`: 3188/3188 jobs, full project.
- `lake exe checkInitImports`: exit 0.
- `lake exe lint-style`: exit 0, no output.
- `lake test`: exit 0, `CslibTests` full suite (9179 jobs).
- `lake shake --add-public --keep-implied --keep-prefix`: zero suggestions on all 5 touched
  files (one suggestion surfaced mid-Phase-5 for the PL bridge's import of `MCSProperties` vs
  `GenericMCS`; fixed by switching the import and dropping the now-dead
  `open ...MCSProperties`).

**Zero-debt**: `#print axioms` on `GenericMCS.listDerivToTree`, `unfoldListImp`,
`deriv_iff_algebraic_of_forward` (propext/Classical.choice), `setConsistent_iff_congr`/
`setMaxConsistent_iff_congr` (no axioms at all — pure `DerivationSystem` corollaries), and all
four preserved `*_deriv_iff_algebraic(_fc)` theorems (propext/Classical.choice only) — no
`sorryAx`, no new axioms anywhere. Grep of all 5 touched files for `sorry`/`^axiom ` finds only
prose mentions in docstrings (zero real occurrences).

**External-reference re-verification**: all 8 names from the Phase-0 grep list
(`listDerivToTree`, `temporalAlgDS`, `temporal_deriv_iff_algebraic(_fc)`, `HilbertBXFc`,
`bimodal_deriv_iff_algebraic(_fc)`, `HilbertTMFc`, `modal_deriv_iff_algebraic`,
`pl_deriv_iff_algebraic`) still resolve identically from their importers.

**Elimination accounting** (baseline -> final, `wc -l`):
| File | Baseline | Final | Δ |
|------|----------|-------|---|
| Propositional/Metalogic/GenericMCSBridge.lean | 256 | 201 | -55 |
| Modal/Metalogic/GenericMCSBridge.lean | 267 | 213 | -54 |
| Temporal/Metalogic/GenericMCSBridge.lean | 370 | 299 | -71 |
| Bimodal/Metalogic/Core/GenericMCSBridge.lean | 405 | 325 | -80 |
| Foundations/Logic/Metalogic/GenericMCS.lean | 167 | 290 | +123 |
| **Total** | **1465** | **1328** | **-137** |

**Target vs actual**: the plan targeted ~300-330 L eliminated (up to ~385 L with Phase 6). The
actual measured net elimination is **137 L** (bridges alone shrank by 260 L; the Foundations
module grew by 123 L to host the shared machinery, for a 137 L net). This falls short of the
research report's estimate. Root cause, documented honestly rather than adjusted to fit the
target: the report's "generic cost" line items (+10, +10, +14, "~+50 new Foundations L" total)
significantly underestimated (a) the mandatory per-declaration docstrings required by CSLib's
lint-prevention rules for every new `class`/`structure`/`instance`/`def`/`theorem` in the
~10 new Foundations declarations, and (b) the per-logic `HilbertTree` instance boilerplate
(~7-10 L with docstring × 4 logics = ~35 L) that is net-new code (Temporal/Bimodal keep their
existing tag + `HasAxiomImplyK`/`HasAxiomImplyS` instances per the Non-Goals, so the K/S-axiom
derivation logic is now duplicated between the kept tag instances and the new `HilbertTree`
instance for those two logics -- an intentional, plan-sanctioned tradeoff since replacing the
tags is explicitly out of scope, Non-Goals). The qualitative goals of the plan -- single shared
abstraction, all four bridges as thin instantiations, zero new sorries/axioms, full CI green,
every public name preserved -- are fully met; the quantitative line-count target was optimistic.

**Timing**: 0.75 hours

**Depends on**: 4, 5, 6 (Phase 6 only if executed; otherwise 4, 5)

**Files to modify**: none (verification + summary only).

**CI gate**: entire pipeline green;
`lean_verify` clean; net elimination within the target band.

**Verification**:
- All five CI commands pass; `lean_verify` reports zero new axioms/sorries; measured net
  elimination reported against the Phase-0 baseline.

## Testing & Validation

- [ ] Phase 0 baseline CI green and line counts recorded.
- [ ] After each of Phases 1-6: targeted `lake build` of the changed module(s), then
      `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style` all green.
- [ ] Phase 7: full pipeline including `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] `lean_verify` on all generic and preserved theorems shows zero new sorries/axioms.
- [ ] Every externally-referenced name (`listDerivToTree`, `temporalAlgDS`,
      `temporal_deriv_iff_algebraic(_fc)`, `HilbertBXFc`, `bimodal_deriv_iff_algebraic(_fc)`,
      `HilbertTMFc`, `modal_deriv_iff_algebraic`, `pl_deriv_iff_algebraic`) still resolves from its
      importer.
- [ ] Net line elimination measured within the ~300-330 L target (up to ~385 L with Phase 6).

## Artifacts & Outputs

- `specs/452_generalize_genericmcsbridge_foundations/plans/01_hoist-mcs-bridge-foundations.md` (this plan).
- Modified `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` (extended with generic HilbertTree machinery).
- Modified `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean`.
- Modified `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`.
- Modified `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`.
- Modified `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`.
- `specs/452_generalize_genericmcsbridge_foundations/summaries/NN_hoist-mcs-bridge-foundations-summary.md` (on completion).

## Rollback/Contingency

- Each phase is a self-contained, independently-committable green milestone; revert the offending
  phase's commit(s) to return to the last green state without losing prior phases.
- Compile-before-delete discipline (never delete a proof body until its replacement builds) means an
  aborted phase leaves a still-green working tree.
- If the Part B universe/binder checks (Phase 3/4 risks) fail to elaborate, fall back to the sibling
  `TreeBridge.lean` home (§4.1 alternative) — one added barrel entry via
  `lake exe mk_all --module`; the retarget phases are otherwise unchanged.
- If 441 (Modal refactor) lands mid-flight, rebase Phase 5's tiny Modal touch (one instance +
  delegations) onto the new `Modal.Proposition`; the `DerivationTree` constructors it depends on are
  unchanged.
- Part A (Phases 1-2) and Part B (Phases 3-5) are independent; either can be shipped alone if the
  other is blocked.
