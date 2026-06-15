# Implementation Plan: BoolEvaluate for Propositional Logic

- **Task**: 202 - review_hilbert_classes_vs_pr648
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/04_bool-evaluate-design.md
- **Artifacts**: plans/05_bool-evaluate-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Add a computable Boolean evaluation function `BoolEvaluate` for propositional logic alongside the existing `Prop`-valued `Evaluate`. The implementation lives in a new file `Cslib/Logics/Propositional/Semantics/Bool.lean` and includes the definition, simp lemmas, the bridge lemma `BoolEvaluate_eq_iff`, negation bridge, factoring through Bool, and a decidability instance. All proofs are already verified via `lean_run_code` in the research phase.

### Research Integration

The research report (04_bool-evaluate-design.md) provides a complete, verified draft implementation. Key findings:
- No existing `BoolEvaluate` or Bool-based evaluation in CSLib (confirmed via `lean_local_search` and grep).
- The `imp` case uses `!a || b` (standard Boolean material conditional).
- The bridge lemma proof is 8 lines, using structural induction with case-splitting on `Bool` for the `imp` case.
- No new Mathlib imports needed beyond what `Semantics.Basic` already provides.
- Placing in a separate file avoids forcing 5 downstream consumers to carry unused Bool machinery.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This addition is part of the Propositional Semantics module. While not explicitly listed in the roadmap, it strengthens the `Logics/Propositional/Semantics/` directory with decidable evaluation -- a prerequisite for future decision procedures and any automated truth-table checking.

## Goals & Non-Goals

**Goals**:
- Create `Cslib/Logics/Propositional/Semantics/Bool.lean` with `BoolEvaluate` and companion lemmas
- Ensure the bridge lemma `BoolEvaluate_eq_iff` connects Boolean and `Prop`-valued evaluation
- Pass full CSLib CI pipeline (build, checkInitImports, lint-style)

**Non-Goals**:
- Modifying existing `Evaluate` or any other file in `Semantics/`
- Adding `#eval` / `#decide` examples or tactics consuming `BoolEvaluate`
- Extending `BoolEvaluate` to modal or temporal logics (future work)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Proof from research does not compile in context | M | L | All proofs were verified via `lean_run_code`; re-verify after file creation |
| `lake exe mk_all --module` misses the new file | L | L | Run `lake exe checkInitImports` as a separate verification step |
| `@[expose] public section` or `module` keyword not compatible with current CSLib conventions | M | L | Check existing files for convention; fall back to explicit `namespace` + manual section if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Create BoolEvaluate File [NOT STARTED]

**Goal**: Write the new file with all definitions, simp lemmas, bridge lemma, and decidability instance.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Semantics/Bool.lean` with the complete implementation from the research report (Section 8)
- [ ] Verify the file follows CSLib conventions (copyright header, module docstring, namespace, `@[expose] public section` or equivalent)
- [ ] Run `lake exe mk_all --module` to register the file in `Cslib.lean`

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Bool.lean` - new file (create)

**Verification**:
- File exists with `BoolValuation`, `BoolEvaluate`, five `@[simp]` lemmas, `BoolEvaluate_eq_iff`, `BoolEvaluate_eq_false_iff`, `Evaluate_eq_BoolEvaluate`, `instDecidableBoolEvaluate`
- `lake exe mk_all --module` completes without error

---

### Phase 2: CI Verification [NOT STARTED]

**Goal**: Confirm the new file compiles and passes the full CSLib CI pipeline.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Bool` to verify the single file compiles
- [ ] Run `lake build` to confirm no regressions
- [ ] Run `lake exe checkInitImports` to verify import registration
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Fix any issues found (style nits, import adjustments)

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Bool.lean` - fixes if needed

**Verification**:
- All four CI commands exit with code 0
- No `sorry` in the file

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Bool` succeeds
- [ ] `lake build` succeeds (no regressions in downstream files)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `grep -c sorry Cslib/Logics/Propositional/Semantics/Bool.lean` returns 0

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Bool.lean` - new file with BoolEvaluate and companions
- `plans/05_bool-evaluate-plan.md` - this plan

## Rollback/Contingency

Delete the new file and revert the `Cslib.lean` import entry:
```bash
rm Cslib/Logics/Propositional/Semantics/Bool.lean
lake exe mk_all --module
```
No existing files are modified, so rollback is trivial.
