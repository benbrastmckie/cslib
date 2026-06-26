# Implementation Plan: Task #353

- **Task**: 353 - Add the MPL ⟨∧,→,⊥,⊤⟩ fragment axiom system `ConjImpBotMinAxiom`
- **Status**: [COMPLETED]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/353_mpl_conjimpbot_fragment_axiom/reports/01_conjimpbotmin-axiom.md
- **Artifacts**: plans/01_conjimpbotmin-axiom.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, CONTRIBUTING.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Add `ConjImpBotMinAxiom`, the fourth element of the MPL fragment tower, to
`Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean`. It is exactly `ConjImpBotAxiom`
minus the ex-falso (`⊥ → φ`) constructor — the point where the minimal-logic (MPL) tower diverges
from the intuitionistic tower. The research found this is a faithful mechanical transcription with
verified byte-for-byte templates and zero sorry risk: a single append of a ready-to-drop-in Lean
block, followed by the CI pipeline. No new file, no `mk_all`, no new imports, and `ConjImpBotAxiom`
is left untouched.

### Research Integration

The research report (`reports/01_conjimpbotmin-axiom.md`) supplies a complete, verified drop-in code
block (report lines 108-251) plus a CI checklist (report lines 270-283). Key findings driving this
plan:

- `MinPropAxiom` (Axioms.lean:126) already contains the five target constructors (`implyK`,
  `implyS`, `andI`, `andE1`, `andE2`) with identical names/shapes and **no** `efq` — so the second
  subsumption targets `MinPropAxiom`, not `IntPropAxiom`.
- `ConjImpBotAxiom` (FragmentAxioms.lean:259-394) is the structural template; the new type drops
  only its final `efq` constructor and the corresponding `efq_isOrFree` lemma.
- All helpers (`hasDeductionTheorem`, `propDerivationSystem`, `imp_isOrFree`, `and_isOrFree`,
  `Proposition.subst`, `Metalogic.HasDeductionTheorem`) are already imported (file lines 9-12) and
  reused directly — **no new imports**.
- The file is already in the barrel (`Cslib.lean:432`); since no new file is created, `mk_all` is
  not required.
- Every proof body is a verified copy of a body that already compiles, with the sole change being
  removal of the `efq` case. Zero sorry/axiom risk.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found (roadmap_flag not set).

## Goals & Non-Goals

**Goals**:
- Add inductive `ConjImpBotMinAxiom` with exactly 5 constructors (`implyK`, `implyS`, `andI`,
  `andE1`, `andE2`).
- Add subsumption theorems `ConjImpAxiom.toConjImpBotMinAxiom` and
  `ConjImpBotMinAxiom.toMinPropAxiom` (target `MinPropAxiom`, **not** `IntPropAxiom`).
- Add the `ConjImpBotMinAxiom` namespace block with `mem_implyK` / `mem_implyS` deduction-theorem
  witnesses.
- Add `subst_preserves_conjImpBotMinAxiom` substitution-closure theorem.
- Add the five `conjImpBotMinAxiom_*_isOrFree` fragment-predicate compatibility lemmas (no
  `efq_isOrFree`).
- Add the `conjImpBotMinAxiom_hasDeductionTheorem` instance.
- Pass the full CI pipeline.

**Non-Goals**:
- Do **not** modify or touch `ConjImpBotAxiom` (lines 259-394) or any existing declaration.
- Do **not** add an ex-falso (`efq`) constructor or an `efq_isOrFree` lemma.
- Do **not** create a new file, run `mk_all`, or add imports.
- Do **not** target `IntPropAxiom` for the second subsumption.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Append placed at wrong location (after `end Cslib.Logic.PL`) | M | L | Insert strictly after line 394, before `end Cslib.Logic.PL` at line 396; verify with a context read before editing |
| Accidental edit to `ConjImpBotAxiom` block | M | L | Pure append only; do not edit lines 259-394; confirm via `git diff` after edit |
| Dot-notation resolution (`.implyK` etc.) ambiguous | L | L | Copy proof bodies verbatim from report; expected type drives resolution as in existing `toMinPropAxiom` |
| `subst` signature universe-variable mismatch | L | L | Copy `subst_preserves_conjImpBotMinAxiom` signature exactly (local `{Atom : Type u}` rebind) per report note 2 |
| Lint failure (docBlame/defLemma/topNamespace) | L | L | Every declaration has a docstring; Prop items use `theorem`/`lemma`; run `lake exe lint-style` in verification |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Append `ConjImpBotMinAxiom` block [COMPLETED]

**Goal**: Insert the complete, verified drop-in Lean code for `ConjImpBotMinAxiom` into
`FragmentAxioms.lean` immediately after the `ConjImpBotAxiom` Deduction-Theorem block.

**Tasks**:
- [ ] Read `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` lines ~388-396 to confirm
      the insertion point (after line 394, before `end Cslib.Logic.PL` at line 396).
- [ ] Insert the drop-in block from research report lines 108-251 verbatim, in this order:
      (a) `/-! ## ConjImpBotMin Axiom System -/` + `inductive ConjImpBotMinAxiom` (5 constructors:
      `implyK`, `implyS`, `andI`, `andE1`, `andE2`);
      (b) `/-! ## ConjImpBotMin Axiom Subsumption -/` + `ConjImpAxiom.toConjImpBotMinAxiom` and
      `ConjImpBotMinAxiom.toMinPropAxiom`;
      (c) `/-! ## ConjImpBotMin Implication Axiom Witnesses -/` + `namespace ConjImpBotMinAxiom`
      with `mem_implyK` / `mem_implyS`, then `end ConjImpBotMinAxiom`;
      (d) `/-! ## ConjImpBotMin Substitution Closure -/` + `subst_preserves_conjImpBotMinAxiom`
      (copy the `{Atom : Type u}` signature exactly);
      (e) `/-! ## ConjImpBotMin Fragment Predicate Compatibility -/` + the five
      `conjImpBotMinAxiom_*_isOrFree` lemmas (no `efq_isOrFree`);
      (f) `/-! ## ConjImpBotMin Deduction Theorem Instance -/` + `conjImpBotMinAxiom_hasDeductionTheorem`.
- [ ] Confirm `ConjImpBotAxiom` (lines 259-394) and all prior declarations are untouched.
- [ ] (Optional, recommended) Add a `ConjImpBotMinAxiom` bullet to the module docstring
      (lines 14-31) to keep the header accurate — only if it does not perturb the build.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` - append the `ConjImpBotMinAxiom`
  block (inductive + 2 subsumptions + 2 witnesses + substitution closure + 5 isOrFree lemmas +
  deduction-theorem instance) after line 394, before `end Cslib.Logic.PL`. No edits elsewhere.

**Verification**:
- The new declarations are all present and in order; `ConjImpBotMinAxiom` has exactly 5
  constructors and no `efq`.
- `ConjImpBotMinAxiom.toMinPropAxiom` targets `MinPropAxiom` (not `IntPropAxiom`).
- `git diff` shows only additions after line 394 (plus optional docstring bullet); no changes to
  lines 259-394.

---

### Phase 2: CI verification pipeline [COMPLETED]

**Goal**: Verify the addition compiles cleanly and passes the full CSLib CI pipeline, run in order.

**Tasks**:
- [ ] `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` (scoped build of the
      edited module — fast feedback).
- [ ] `lake exe checkInitImports` (file already imports `Cslib.Init`; no new file).
- [ ] `lake exe lint-style`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] `lake test` (CslibTests suite).
- [ ] `lake build` (full final build).
- [ ] On any failure, inspect diagnostics, correct against the report template, and re-run the
      pipeline from the scoped build.

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- None (verification only). Any fix loops back into Phase 1's file.

**Verification**:
- All six CI commands exit 0.
- No `sorry`, no new `axiom`, no new warnings introduced by the added declarations.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` succeeds (scoped).
- [ ] `lake exe checkInitImports` succeeds.
- [ ] `lake exe lint-style` succeeds.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` succeeds.
- [ ] `lake test` succeeds.
- [ ] `lake build` (full) succeeds.
- [ ] `git diff` confirms `ConjImpBotAxiom` and all prior declarations are unchanged.

## Artifacts & Outputs

- Updated `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` containing the new
  `ConjImpBotMinAxiom` axiom system (inductive + 2 subsumptions + 2 witnesses + substitution
  closure + 5 `isOrFree` lemmas + deduction-theorem instance).
- Green CI run across the full pipeline.

## Rollback/Contingency

The change is a pure append to a single file. To revert:
```bash
cd /home/benjamin/Projects/cslib
git checkout -- Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean
```
Because no new file, import, or barrel entry is introduced, reverting the single file fully restores
the prior state. If a CI step fails, fix in place against the verified report template and re-run
the pipeline from the scoped build; no partial-state cleanup is needed.
