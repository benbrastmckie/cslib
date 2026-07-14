# Implementation Summary: Generalize GenericMCSBridge — hoist the shared MCS-bridge trio into Foundations

- **Task**: 452
- **Plan**: specs/452_generalize_genericmcsbridge_foundations/plans/01_hoist-mcs-bridge-foundations.md
- **Status**: Implemented — all 8 phases (0-7, including the optional Phase 6) complete, committed, and CI-green.

## What Was Built

**Part A (Phases 1-2)**: Collapsed the intra-file base↔Fc duplication in the Temporal and
Bimodal `GenericMCSBridge.lean` files. The `_fc`-parameterized block was reordered above the
base block (Lean scoping requirement), and the three base helpers (`derivTreeToList`,
`unfoldListImpInTree`, `listDerivToTree`) were rewritten as one-line delegations to their `_fc`
counterparts at `fc := .Base`, exploiting the definitional equality between
`temporalAlgDS.Deriv`/`bimodalAlgDS.Deriv` and `(...AlgDSFc .Base).Deriv`.

**Part B (Phases 3-6)**: Extended the *existing* `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`
(not a new file) with a generic `HilbertTree (D : List F → F → Type*)` typeclass (5 fields:
`assumption`/`mp`/`weakening`/`axiomK`/`axiomS`), a `ClosedHilbert D` tag with the standard
`InferenceSystem`/`ModusPonens`/`HasAxiomImplyK`/`HasAxiomImplyS`/`MinimalHilbert` instance
bundle, `treeAlgDS`, generic `unfoldListImp`/`listDerivToTree` backward combinators, a
`deriv_iff_algebraic_of_forward` assembler, and two pure `DerivationSystem` transfer lemmas
(`setConsistent_iff_congr`/`setMaxConsistent_iff_congr`). All four per-logic bridges
(Propositional, Modal, Temporal, Bimodal) were then retargeted: each adds a
`HilbertTree (DerivationTree ...)` instance and delegates its backward helper, backward
direction, and both consistency/MCS lemmas to the generic combinators. Phase 6 (optional, run
to completion) additionally retired the local `HilbertOf Axioms` tag in PL and Modal in favor of
the generic `ClosedHilbert` tag, since that tag had no external references.

The forward `derivTreeToList` structural induction remains per-logic in all four bridges, as
required by the plan's Non-Goals (Lean's `induction d with | ctor ...` cannot be written
generically over an abstract `D`).

## Files Modified

- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — extended (167L → 290L): new
  `HilbertTree`, `ClosedHilbert`, `treeAlgDS`, `unfoldListImp`, `listDerivToTree`,
  `deriv_iff_algebraic_of_forward`, `setConsistent_iff_congr`, `setMaxConsistent_iff_congr`.
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` (370L → 299L)
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` (405L → 325L)
- `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` (256L → 201L)
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` (267L → 213L)
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` — doc-comment update only
  (`HilbertOf` → `ClosedHilbert` reference).
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` — doc-comment update only.

## Public API Preserved

Every externally-referenced name resolves identically to baseline (grep-verified before and
after): `listDerivToTree` (PL, Modal — used by their `DeductionTheorem.lean`), `temporalAlgDS`,
`temporal_deriv_iff_algebraic`, `temporal_deriv_iff_algebraic_fc`, `HilbertBXFc`,
`bimodal_deriv_iff_algebraic`, `bimodal_deriv_iff_algebraic_fc`, `HilbertTMFc`,
`modal_deriv_iff_algebraic`, `pl_deriv_iff_algebraic`, `propAlgDS`, `modalAlgDS`. The
`HilbertBX(Fc)`/`HilbertTM(Fc)` tags and their `MinimalHilbert` boilerplate were kept local to
Temporal/Bimodal per the plan's Non-Goals (22 downstream `HasAxiom*` instances depend on them).

## Verification

- **Build**: `lake build` — 3188/3188 jobs, full project green.
- **CI pipeline**: `lake exe checkInitImports` (exit 0), `lake exe lint-style` (exit 0, no
  output), `lake test` (exit 0, full `CslibTests` suite), `lake shake --add-public
  --keep-implied --keep-prefix` (zero suggestions on all 5 touched files after one import fix
  in the PL bridge, see Deviations).
- **Zero-debt**: `#print axioms` (via `lean_run_code`, bypassing an intermittently stale
  `lean_verify`/LSP state caused by a concurrent task) on all new Foundations definitions and
  all four preserved `*_deriv_iff_algebraic(_fc)` theorems: only `propext`/`Classical.choice`
  (the two pure `DerivationSystem` congruence lemmas depend on no axioms at all). No `sorryAx`,
  no new `axiom` declarations. Grep of all touched files for `\bsorry\b` / `^axiom ` finds only
  prose mentions in docstrings.
- **Elimination accounting** (`wc -l`, baseline → final):

  | File | Baseline | Final | Δ |
  |------|----------|-------|---|
  | Propositional/Metalogic/GenericMCSBridge.lean | 256 | 201 | -55 |
  | Modal/Metalogic/GenericMCSBridge.lean | 267 | 213 | -54 |
  | Temporal/Metalogic/GenericMCSBridge.lean | 370 | 299 | -71 |
  | Bimodal/Metalogic/Core/GenericMCSBridge.lean | 405 | 325 | -80 |
  | Foundations/Logic/Metalogic/GenericMCS.lean | 167 | 290 | +123 |
  | **Total** | **1465** | **1328** | **-137** |

  The plan targeted ~300-330 L eliminated (up to ~385 L with Phase 6); the actual net
  elimination is 137 L. See "Plan Deviations" for the honest root-cause explanation — this is
  reported as measured, not adjusted to match the target.

## Plan Deviations

1. **Bimodal `HilbertTree` instance syntax** (Phase 4): the named-argument form
   `HilbertTree (F := ...) (...)` that worked verbatim in the Temporal bridge produces a raw
   Lean parser error in the Bimodal bridge, because Bimodal's temporal `F` (future) notation
   shadows the bare identifier `F`, forcing the class's auto-bound implicit type parameter to
   elaborate as the escaped `«F»` in that scope. Fixed by using the fully positional
   `@HilbertTree (Bimodal.Formula Atom) _ (Bimodal.DerivationTree fc) where ...` form instead.
   Documented inline in the instance's docstring; confirmed via an isolated `lean_run_code`
   repro before applying to the file.

2. **Declaration ordering for `treeAlgDS`-based aliases** (Phases 3-6): in every bridge file,
   the per-logic `HilbertTree (DerivationTree ...)` instance must be declared *before* any
   definition that calls `treeAlgDS`/`GenericMCS.listDerivToTree`/`GenericMCS.unfoldListImp`
   (Lean scoping — the instance must already be resolvable). This bit twice: once when writing
   `propAlgDS`/`modalAlgDS` as `treeAlgDS (...)` aliases in Phase 6, requiring a reorder in both
   PL and Modal identical to the fix already applied in Phase 3/4 for `temporalAlgDSFc`-style
   defs.

3. **PL bridge import fix** (surfaced during Phase 7's `lake shake` run, applied and re-verified
   before Phase 6): the PL bridge's growing reliance on `GenericMCS` symbols (added in Phase 5)
   made its existing `public import ...MCSProperties` (which only transitively re-exported
   `GenericMCS`) suboptimal; `lake shake` flagged it. Fixed by importing `GenericMCS` directly
   and dropping the now-unnecessary `open ...MCSProperties` (nothing in the file used anything
   `MCSProperties`-specific; `SetConsistent`/`SetMaximalConsistent` come from `Consistency.lean`,
   transitively available via `GenericMCS`). Re-verified with a scoped build and a full
   `lake shake` sweep (zero suggestions on all 5 touched files) after the fix.

4. **`unfoldListImpInTree` gained a new `[HasMinimalAxioms Axioms]` constraint** (PL and Modal,
   Phase 5): the original signature had no such constraint (it used only raw tree operations);
   delegating to the generic `unfoldListImp` requires the `HilbertTree` instance, which itself
   requires `[HasMinimalAxioms Axioms]`. Safe per the research report's external-reference
   table: `unfoldListImpInTree` has no external callers in either logic.

5. **Elimination target not met** (Phase 7): see the accounting table above and its
   explanation. The qualitative refactor goals (shared abstraction, thin per-logic
   instantiations, zero new sorries/axioms, all public names preserved, full CI green) are all
   met; the research report's line-count estimate for the "generic cost" side (~+50 new
   Foundations lines) undercounted mandatory docstring overhead and the net-new
   `HilbertTree`-instance boilerplate (~35 L across 4 logics) that coexists with — rather than
   replaces — the kept `HilbertBX(Fc)`/`HilbertTM(Fc)` tag machinery in Temporal/Bimodal (kept
   per Non-Goals). No workaround or number-adjustment was applied; the actual measured 137 L
   net elimination is reported as-is.

6. **Environment note, not a deviation**: two full-repo `lake build` runs failed transiently
   during Phases 4-5 in files unrelated to this task (`Cslib/Logics/Propositional/Tableau/
   Intuitionistic/Scheme.lean`, `Cslib/Logics/Temporal/Tableau/Saturation.lean`,
   `Cslib/Logics/Temporal/Tableau/Completeness.lean`) because tasks 317/439 were concurrently
   editing those files in the same working tree (confirmed via `git diff --stat` showing
   uncommitted changes to those files, disjoint from this task's diff). Verification for the
   affected phases used scoped `lake build` of touched + downstream-importing modules instead;
   the full pipeline was successfully re-run and confirmed green once those tasks' edits
   stabilized, before Phase 7 concluded.

## Coordination Notes for Downstream Tasks

- Task 441 (Modal native refactor, PLANNED): this task's Modal touch is limited to
  `Modal/Metalogic/GenericMCSBridge.lean` and a one-line doc update in
  `Modal/Metalogic/DeductionTheorem.lean`; the `DerivationTree` constructors 441 does not
  change are what the Modal forward induction inducts on, so 441 should rebase cleanly.
- Tasks 449-451 (BX+): the Temporal bridge is already `fc`-polymorphic and the new
  `HilbertTree (DerivationTree fc)` instance is defined for arbitrary `fc`, so a new
  `FrameClass.Metric` case is covered automatically without further bridge changes.
- Task 453 (heartbeat audit): confirmed no file overlap.
