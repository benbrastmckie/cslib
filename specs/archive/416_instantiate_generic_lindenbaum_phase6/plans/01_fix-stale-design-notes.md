# Implementation Plan: Task #416

- **Task**: 416 - Instantiate GenericLindenbaum (Phase 6)
- **Status**: [COMPLETED]
- **Effort**: 0.4 hours
- **Dependencies**: None (code consolidation already landed in commit 9242d243)
- **Research Inputs**: specs/416_instantiate_generic_lindenbaum_phase6/reports/01_generic-lindenbaum-phase6.md
- **Artifacts**: plans/01_fix-stale-design-notes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, cslib.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The named deliverable of task 416 — re-instantiating `MinTheory`/`IntDCCS` Lindenbaum
machinery on the generic `GenericLindenbaum` substrate — is **already landed** in commit
`9242d243` ("task 407 phase 6"), an ancestor of HEAD. The substrate is active and consumed
by both `MinLindenbaum.lean` and `IntLindenbaum.lean` via six thin lemmas; scoped build is
green with 0 sorry / 0 axioms. The only residual, in-scope, zero-risk deliverable is a
documentation drift: the "Design Notes" paragraph at `GenericLindenbaum.lean:45-52` still
claims the file is "additive" and that re-instantiation is "deferred to Phase 6". This plan
is a single doc-only phase that rewrites that paragraph to reflect reality, then verifies the
full CSLib CI quartet stays green.

### Research Integration

Key findings from `reports/01_generic-lindenbaum-phase6.md`:
- The substrate is NOT dormant. Both Lindenbaum files import it and delegate to it. The six
  thin instances are `min_/int_deriv_from_closure_to_S`, `min_/int_deriv_imp_of_union`, and
  `min_/int_imp_witness`, located at MinLindenbaum.lean:91,107,144 and
  IntLindenbaum.lean:108,124,178, each calling `generic_deriv_from_closure_to_S` /
  `generic_deriv_imp_of_union` / `generic_imp_witness`.
- The explosion parameter `h_cons_ext` is wired exactly as designed: `fun _ _ => trivial`
  for minimal logic, EFQ + `intDeductiveClosure_consistent` for intuitionistic logic.
- Build green (727 jobs), 0 sorry, 0 axioms across all three files. Zero-debt already met.
- The 415 audit's "additive / unused" finding was driven solely by this stale docstring —
  a documentation-vs-code drift, not a real consolidation gap.
- The residual closure-def micro-duplication (`minDeductiveClosure` / `intDeductiveClosure`
  and their two trivial closure lemmas each) is **OUT OF SCOPE** — those are public defs
  consumed by `MinStrongCompleteness`, `IntStrongCompleteness`, and `IntDecidability`, which
  are task 393 territory. Do NOT touch them under 416.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided to this planning invocation; no ROADMAP phases added.

## Goals & Non-Goals

**Goals**:
- Rewrite the "Design Notes" docstring paragraph at `GenericLindenbaum.lean:45-52` so it
  states the substrate is active and load-bearing, instantiated by both `MinLindenbaum.lean`
  and `IntLindenbaum.lean` (task 407 phase 6, commit 9242d243).
- Preserve the still-accurate explosion-parameterization explanation and the deduction-theorem
  access note already present in the module docstring.
- Verify the full CSLib CI quartet remains green after the edit.

**Non-Goals**:
- Re-implementing or re-instantiating any Lindenbaum machinery (already done in 9242d243).
- Collapsing the residual `minDeductiveClosure` / `intDeductiveClosure` defs or their closure
  lemmas (task 393 territory — do NOT double-edit).
- Renaming `MinTheory` / `IntDCCS` predicates (downstream references them by name across 5 files).
- Any proof, definition, or behavioral change. This is a pure prose edit.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Edit accidentally alters code outside the docstring comment block | H | L | Edit is confined to lines within the `## Design Notes` prose inside the existing `/-! ... -/` doc comment; verify with `lake build` + git diff review |
| Docstring rewrite introduces a docBlame or doc-format lint warning | L | L | Pure prose replacement inside an existing doc comment (no new decl, no removed docstring); run `lake exe lint-style` to confirm |
| Touching task-393 territory by reflex | M | L | Plan explicitly forbids editing closure defs/lemmas; only the Design Notes paragraph is in scope |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Single phase; no parallelism.

### Phase 1: Rewrite Stale Design Notes Docstring [COMPLETED]

**Goal**: Replace the now-false "additive / deferred to Phase 6" Design Notes paragraph with
prose that accurately describes the active, instantiated substrate, then confirm CI is green.

**Tasks**:
- [ ] Read `Cslib/Logics/Propositional/Metalogic/GenericLindenbaum.lean` lines 43-57 to
      confirm the exact current text of the `## Design Notes` paragraph (lines 45-52).
- [ ] Edit the `## Design Notes` paragraph so it states:
      - The substrate is **active / load-bearing**, not additive.
      - Re-instantiation was completed in task 407 phase 6 (commit 9242d243).
      - Both `MinLindenbaum.lean` and `IntLindenbaum.lean` import this module and delegate to
        the `generic_*` lemmas (the six thin instances:
        `min_/int_deriv_from_closure_to_S`, `min_/int_deriv_imp_of_union`,
        `min_/int_imp_witness`).
      - Keep the existing accurate note that the deduction theorem is accessed via explicit
        `h_implyK` / `h_implyS` witnesses.
- [ ] Do NOT modify any `def`, `lemma`, `theorem`, or other code; the edit is confined to the
      prose inside the module doc comment.
- [ ] Run the CSLib CI quartet and confirm green (see Verification).

**Timing**: 0.4 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/GenericLindenbaum.lean` - rewrite the `## Design Notes`
  prose paragraph (lines ~45-52) only; no code changes.

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.GenericLindenbaum` (and the two consumers
  `...MinLindenbaum`, `...IntLindenbaum`) -> success.
- `lake build` -> success (final full-project check).
- `lake test` -> CslibTests pass.
- `lake exe checkInitImports` -> pass.
- `lake exe lint-style` -> pass (no new text-lint warnings).
- `lake shake --add-public --keep-implied --keep-prefix` -> no new findings introduced by the edit.
- `grep -nE 'sorry|admit|native_decide|^axiom' GenericLindenbaum.lean MinLindenbaum.lean IntLindenbaum.lean`
  -> NONE (0 new sorry, 0 new axioms).
- `git diff` confirms the only changed lines are inside the Design Notes prose comment.

---

## Testing & Validation

- [ ] Scoped build of `GenericLindenbaum`, `MinLindenbaum`, `IntLindenbaum` succeeds.
- [ ] Full `lake build` succeeds.
- [ ] `lake test`, `lake exe checkInitImports`, `lake exe lint-style` all pass.
- [ ] `lake shake` introduces no new import findings attributable to this edit.
- [ ] 0 new sorry, 0 new axioms (verified by grep across the three files).
- [ ] `git diff` shows changes confined to the Design Notes docstring prose.

## Artifacts & Outputs

- Modified `Cslib/Logics/Propositional/Metalogic/GenericLindenbaum.lean` (docstring prose only).
- Execution summary at `specs/416_instantiate_generic_lindenbaum_phase6/summaries/01_*-summary.md`.

## Rollback/Contingency

If any CI step fails (it should not, since no code changes), revert the single-file edit with
`git checkout -- Cslib/Logics/Propositional/Metalogic/GenericLindenbaum.lean` and re-confirm
the pre-edit green state. Because the change is doc-only and confined to one comment block,
rollback is trivial and risk-free.

If the orchestrator policy requires a *code-consolidation* deliverable rather than a doc fix,
the honest disposition (per research §7) is to mark task 416 [COMPLETED] citing 9242d243 and
fold the §5 closure-def residue into task 393 — do NOT re-do already-landed work.
