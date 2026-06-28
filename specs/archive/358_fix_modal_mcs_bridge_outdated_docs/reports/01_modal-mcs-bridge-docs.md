# Research Report: Fix Modal GenericMCSBridge Outdated Docs (Task 358)

**Session**: sess_1782522754_5f0817_358
**Date**: 2026-06-27
**Task type**: cslib (documentation-only)
**Source**: /vet of task 350

## 1. Problem Statement

`Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` is a documentation-only file (no Lean
declarations). It is internally **self-contradictory**:

- Lines 14-35 contain a `CORRECTION NOTICE` (task 350, 2026-06-25) stating that the file's
  original gap-analysis conclusion is **OUTDATED** and **incorrect** — the temporal-style
  bridge IS buildable.
- Lines 37-160 still contain the **obsolete** "Gap Analysis" (Component 1 / 2 / 3),
  "Conclusion" table, "Follow-up Tasks", and a closing `NOTE` block — all of which assert
  the OLD (now-retracted) claim that the bridge cannot/should not be built and that the two
  systems are "architecturally distinct".

A reader hitting the body after the notice receives directly contradictory guidance.

## 2. Verification of the Corrected Understanding

I read the target file in full and the two referenced template files. Findings confirm the
CORRECTION NOTICE is the accurate account.

### 2.1 The Temporal/Bimodal bridges are fully proven (not documentation)

Both sibling files contain **complete, proven `theorem`s**, not gap analyses:

- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — defines `temporalAlgDS`, and proves
  `deriv_tree_to_list`, `unfold_listImp_in_tree`, `list_deriv_to_tree`,
  `temporal_deriv_iff_algebraic`, `temporal_setConsistent_iff_algebraic`,
  `temporal_setMaxConsistent_iff_algebraic`.
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — the parallel proven file for
  `Bimodal.HilbertTM` (the "newly added bimodal bridge" the notice refers to).

The construction in both: forward direction is structural induction on `DerivationTree`,
where the non-propositional rules (necessitation / temporal_necessitation / temporal_duality)
fire only at empty context and bottom out at `InferenceSystem.DerivableIn`; backward direction
extracts `[] ⊢ listImp Γ φ`, weakens to `Γ`, then peels `listImp` via `unfold_listImp_in_tree`.

### 2.2 Why those bridges work but Modal's is "documentation only"

The difference is **predicate-parameterisation vs. type-parameterisation**, exactly as the
CORRECTION NOTICE states:

- `algebraicDerivationSystem` is parameterised by a **type** `S` carrying `[InferenceSystem S F]`
  + `[MinimalHilbert S]` (+ `[Necessitation S]`) instances. Temporal and Bimodal each have a
  single concrete such type (`Temporal.HilbertBX`, `Bimodal.HilbertTM`), so
  `algebraicDerivationSystem (S := HilbertBX)` is directly instantiable and a single bridge
  theorem covers the whole logic.
- `modalDerivationSystem` (defined at `Cslib/Logics/Modal/Metalogic/DerivationTree.lean:198`)
  is parameterised by a **value-level predicate** `Axioms : Proposition Atom → Prop`:

  ```lean
  def modalDerivationSystem (Axioms : Proposition Atom → Prop) :
      Metalogic.DerivationSystem (Proposition Atom) where
    Deriv := Deriv Axioms
    ...
  ```

  There is no single type `S` to instantiate `algebraicDerivationSystem` at for an arbitrary
  `Axioms`. That is the genuine, still-valid barrier — and it is an **infrastructure gap, not
  a semantic one**.

### 2.3 The bridge IS buildable (two senses)

- **Per concrete system**: each concrete modal Hilbert type already carries the full instance
  stack. `Cslib/Logics/Modal/ProofSystem/Instances/K.lean:62-113` registers
  `InferenceSystem Modal.HilbertK` (with `derivation φ := DerivationTree (@KAxiom Atom) [] φ` —
  the same structural pattern as Temporal/Bimodal), plus `ModusPonens`, `Necessitation`, the
  `HasAxiom*` axioms, and `ModalHilbert`. So a temporal-style bridge
  `modalDerivationSystem (@KAxiom Atom) ↔ algebraicDerivationSystem (S := HilbertK)` could be
  written today, verbatim from the Temporal template (likewise K4, K5, D, …).
- **Generically over `Axioms`**: requires the `HilbertOf Axioms` wrapper type — a `Type` whose
  `InferenceSystem` maps derivability to `Nonempty (DerivationTree Axioms [] φ)` and whose
  `Necessitation` instance lifts the tree-level constructor. This is the follow-up work; it is
  what makes ONE generic bridge possible rather than one-per-system.

### 2.4 The `□(φ→φ)` "counterexample" was wrong

Confirmed by the notice's own reasoning (lines 82-89): at empty context,
`algDS.Deriv [] φ = InferenceSystem.DerivableIn HilbertK φ = Nonempty (DerivationTree KAxiom [] φ)`,
which **includes** necessitation: `DerivationTree.necessitation (φ→φ) imp_self_deriv` witnesses
`□(φ→φ)`. The old Component 2 claim that `□(φ→φ)` is NOT algebraically derivable is false.

### 2.5 What remains accurate in the old body

Only two substantive points survive, and both are already covered by the CORRECTION NOTICE and
the "Using GenericMCS with Modal Logics Today" paragraph:
- Modal logics can already use the algebraic MCS path for **propositional** MCS reasoning today
  (`Modal.HilbertK → MinimalHilbert → algebraicDerivationSystem`), no new code required.
- The follow-up (wrapper type + bridge + WF-recursion-free `deductionTheorem`) touches ~25 raw
  call sites across `Modal/Completeness`, `MCS`, `Systems/{K,D}`,
  `Propositional/StrongCompleteness`, `Min/IntLindenbaum`, `NaturalDeduction`.

Everything else in lines 46-160 (the "not equivalent / cannot replace each other" framing, the
Component-1/2/3 structure, the "extend ListDeriv with a necessitation rule / retire
modalDerivationSystem" follow-ups, and the closing NOTE block) is obsolete and contradicts the
notice.

## 3. Recommendation: Remove, Don't Archive

**Recommendation: REMOVE the obsolete analysis (current lines 37-160) and replace the whole
docstring with the corrected version below.** Do not keep an in-file "archived" copy.

Rationale:
- The obsolete text's only value is historical, and git history already preserves it
  (the file is committed). An in-file archive would re-introduce the contradiction risk and
  add maintenance noise.
- CSLib's docstrings are reference material for contributors; keeping a retracted analysis
  inline invites future readers to act on it.
- The corrected docstring below preserves every still-accurate fact (current usability,
  the real barrier, the follow-up scope), so no information is lost.

The file remains documentation-only after this change (still no Lean declarations) — this is a
pure docstring rewrite, zero proof obligations, zero sorry risk, fully compatible with the
zero-debt policy.

## 4. Proposed Rewritten Module Docstring

Replace the entire block from line 12 (`/-! # GenericMCS Bridge Analysis...`) through line 160
(end of the closing `NOTE` block) with the following. Keep lines 1-10 (copyright, `module`,
the two `public import`s) unchanged.

```lean
/-! # GenericMCS Bridge for Normal Modal Logics (status note)

This module documents the relationship between the two derivation systems available for
normal modal logics and records why the generic tree↔algebraic bridge is not yet proved
here. It contains no Lean declarations.

1. **`algebraicDerivationSystem (S := Modal.HilbertK)`**: built from `ListDeriv` via the
   generic MCS framework. Available for any `MinimalHilbert` proof system.
2. **`modalDerivationSystem (@KAxiom Atom)`**: built from explicit `DerivationTree`
   induction, parameterised by an axiom predicate `Axioms : Proposition Atom → Prop`.

## The bridge IS buildable

A temporal-style bidirectional bridge
`modalDerivationSystem.Deriv Γ φ ↔ algebraicDerivationSystem.Deriv Γ φ` is constructible by
exactly the same proof used for the Temporal and Bimodal logics:

* `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`
* `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`

Both prove `*_deriv_iff_algebraic`, `*_setConsistent_iff_algebraic`, and
`*_setMaxConsistent_iff_algebraic` by structural induction on `DerivationTree` (forward) and
`listImp`-peeling (backward). For any *concrete* modal system the same proof transfers
directly: `Modal.HilbertK` already carries `InferenceSystem`, `ModusPonens`, `Necessitation`,
the `HasAxiom*` instances, and `ModalHilbert` (see
`Cslib/Logics/Modal/ProofSystem/Instances/K.lean`), with
`derivation φ := DerivationTree (@KAxiom Atom) [] φ` — the same structural pattern as
`HilbertT`/`HilbertTM`.

(The old `□(φ → φ)` "counterexample" claiming this formula was not algebraically derivable
from `[]` was mistaken: at empty context `algDS.Deriv [] φ` unfolds to
`Nonempty (DerivationTree KAxiom [] φ)`, which includes necessitation, so
`DerivationTree.necessitation (φ→φ) ⋯` witnesses `□(φ → φ)`.)

## Why it is not proved here yet (infrastructure gap)

`modalDerivationSystem` is parameterised by a value-level predicate
`Axioms : Proposition Atom → Prop`, whereas `algebraicDerivationSystem` is parameterised by a
*type* `S` carrying `[InferenceSystem S F]` and `[MinimalHilbert S]` instances. For an
arbitrary `Axioms` there is no single type `S` to instantiate `algebraicDerivationSystem` at,
so the one-bridge-covers-all-systems form requires a wrapper type
`HilbertOf Axioms : Type` whose `InferenceSystem` maps derivability to
`Nonempty (DerivationTree Axioms [] φ)` and whose `Necessitation` instance lifts the
tree-level necessitation constructor. This is an infrastructure gap, not a semantic one.

## What modal logics can already use today

The propositional MCS path works with no new code: the instance chain
`Modal.HilbertK → MinimalHilbert → algebraicDerivationSystem` makes all
`SetMaximalConsistent` properties from the generic MCS framework available for propositional
reasoning. For modal-specific MCS properties (box closure, box-box, …) the tree-based
`modalDerivationSystem` path is used because necessitation is required.

```lean
-- Already works (no new code needed):
#check @algebraicDerivationSystem (Modal.Proposition Atom) _ _ (S := Modal.HilbertK) _
#check @algebraic_mcs_negation_complete (Modal.Proposition Atom) _ _ (S := Modal.HilbertK) _
```

## Follow-up task

Build the `HilbertOf Axioms` wrapper type with `InferenceSystem` + `MinimalHilbert` +
`Necessitation` instances synthesised from the axiom constructors, prove the modal and
propositional bridges (mirroring the Temporal/Bimodal files), and re-implement both
`deductionTheorem` defs without WF-recursion. Roughly 25 raw call sites across
`Modal/Completeness`, `MCS`, `Systems/{K,D}`, `Propositional/StrongCompleteness`,
`Min/IntLindenbaum`, and `NaturalDeduction` must keep compiling. See the task 350 summary for
full scope.
-/
```

Notes on the proposed docstring:
- Keeps the markdown nested code fence (` ```lean ` inside the doc comment) — this is the same
  pattern the current file already uses (lines 141-148), so it is known to compile.
- Drops the obsolete `## Gap Analysis`, `### Component 1/2/3`, `## Conclusion` table, the
  "extend ListDeriv / retire modalDerivationSystem" follow-ups, and the trailing standalone
  `/-! NOTE ... -/` block.
- Folds the surviving CORRECTION-NOTICE content into a clean, non-self-contradictory narrative
  (no more "OUTDATED" meta-commentary referring to text that no longer exists).

## 5. Implementation Notes for Downstream

- **Scope**: single-file docstring edit. No `.lean` declarations added or removed; the file
  stays documentation-only.
- **Build/CI**: `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` should be run to
  confirm the doc comment parses (nested fences, unicode `□`, `↔` already appear in the
  current file and in siblings, so no new hazards). No `lake lint` docBlame impact — there are
  no declarations to document.
- **Preserve lines 1-10 verbatim** (copyright header, `module  -- shake: keep-all`, the two
  `public import`s). The `-- shake: keep-all` comment must stay so `lake shake` does not strip
  the imports from this declaration-free file.
- **Cross-references**: the Temporal and Bimodal bridge files both already reference this file
  as "gap analysis (documentation only)" (Temporal line 51, Bimodal line 61). After this
  rewrite the file is better described as a "status note"; updating those two back-references
  is optional/nice-to-have and out of strict scope for task 358, but worth flagging to the
  planner.
- **Zero-debt**: no sorries, no axioms, no vacuous defs involved. Pure documentation.

## 6. Reuse Check (CSLib reuse-first)

No new abstractions are proposed by this task. The corrected docstring points to the existing,
already-proven Temporal/Bimodal bridges as the reuse template, and to the existing concrete
`Modal.Hilbert*` instance stacks. The only *new* construct named (the `HilbertOf Axioms`
wrapper) is explicitly deferred to a separate follow-up task, not introduced here.
