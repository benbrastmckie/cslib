# Implementation Summary: Task #615

- **Task**: 615 - Add algebraic semantic validity as a further equivalent node in the
  propositional proof-system TFAE families
- **Status**: [PARTIAL]
- **Started**: 2026-08-11T00:36:09Z
- **Effort**: ~1.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_algebraic-node-tfae-folds.md, reports/01_algebraic-node-tfae.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md,
  `.claude/rules/cslib.md`, `.claude/rules/plan-compliance.md`

## Overview

Added three new four-way `List.TFAE` theorems to
`Cslib/Logics/Propositional/ProofSystemEquivalence.lean`, folding algebraic semantic validity
(`BAValid`, `HAValid`, `GHAValid`) onto the existing closed three-way equivalences for CPL, IPL,
and MPL: `cplProofSystemsWithAlgebraTfae`, `iplProofSystemsWithAlgebraTfae`,
`mplProofSystemsWithAlgebraTfae`. Each fold is pure composition — no new lemmas — since
`CPL/IPL/MPL.hilbert_alg_completeness` are already stated as node 1 of the closed TFAE ↔
tier-matched algebraic validity. The module docstring (opening paragraph, `## Main Results`,
`## Dependencies`, and a new section-level docstring) records the closed-only decision and its
reason. All three plan phases were executed and all changes are confined to the one file named
in the territory contract. Six of the seven CSLib CI steps pass cleanly; the seventh
(`lake test`) is blocked by a full-repo test failure in `CslibTests/GrindLint.lean` caused by
concurrently-landed sibling-task commits touching `Cslib/Logics/Bimodal` and
`Cslib/Logics/Temporal`, which this task's territory contract does not authorize fixing.

## What Changed

- `Cslib/Logics/Propositional/ProofSystemEquivalence.lean`:
  - Added `public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness`.
  - Added `universe u` near the file-level `variable {Atom : Type*} [DecidableEq Atom]`.
  - Added `section WithAlgebra` (after `end WithTableau`, before `end Cslib.Logic.PL`) with a
    section-level `/-! ## Algebraic Semantics Folds (closed formulas only) ... -/` docstring and
    three theorems, each binding its own `{Atom : Type u} [DecidableEq Atom]` (shadowing the
    file-level `Type*` variable, since `BAValid`/`HAValid`/`GHAValid` need an explicit,
    nameable universe pin `.{u, u}`):
    - `cplProofSystemsWithAlgebraTfae` — nodes 1-3 from `cplProofSystemsTfaeClosed`, node 4
      `BAValid.{u, u} φ` via `CPL.hilbert_alg_completeness`.
    - `iplProofSystemsWithAlgebraTfae` — nodes 1-3 from `iplProofSystemsTfaeClosed`, node 4
      `HAValid.{u, u} φ` via `IPL.hilbert_alg_completeness`.
    - `mplProofSystemsWithAlgebraTfae` — nodes 1-3 from `mplProofSystemsTfaeClosed`, node 4
      `GHAValid.{u, u} φ` via `MPL.hilbert_alg_completeness`.
  - Extended the module's opening paragraph, `## Main Results`, and `## Dependencies` to cover
    the three new theorems and the algebraic-fold dependencies.

No other file was modified (territory: `Cslib/Foundations/Logic/ProofSystem.lean` was in scope
per the delegation contract but the plan explicitly excludes it as a Non-Goal / optional
follow-up — see report §8 — so it was correctly left untouched).

## Decisions

- Followed the plan/report verbatim: closed-families-only algebraic node (no context-based node,
  no five-way fold) — both were researched and deliberately rejected (report §4.2, §5.4).
- The new section introduces no `variable` line; the constraint is a universe pin, not a
  typeclass, so each theorem's own `{Atom : Type u} [DecidableEq Atom]` binder shadows the
  file-level `Atom`/`[DecidableEq Atom]` cleanly with no `unusedSectionVars` fallout, confirmed
  by `lake lint`.

## Plan Deviations

- Phase 2's task item "Add the section-level docstring immediately before `section WithAlgebra`"
  was already satisfied inside the Phase 1 edit, since report §5.2 bundles the section docstring
  together with the section body it introduces. Re-verified present and correct in Phase 2 rather
  than re-authored; annotated inline in the plan.

## Verification

- Build: `lake build Cslib.Logics.Propositional.ProofSystemEquivalence` (scoped, after each
  phase) and `lake build` (full project, 3325/3325 jobs) both green. Only pre-existing warnings
  in unrelated files (`Tableau/Intuitionistic/DecisionProcedure.lean`,
  `Tableau/Minimal/DecisionProcedure.lean`, `Modal/Tableau/FrameCompleteness.lean`), none
  introduced by this task.
- `lake exe checkInitImports`: exit 0.
- `lake lint`: zero warnings anywhere in `ProofSystemEquivalence.lean` (checked `docBlame`,
  `defLemma`, `defsWithUnderscore`, `unusedSectionVars` explicitly).
- `lake exe lint-style`: exit 0.
- `lake shake --add-public --keep-implied --keep-prefix`: no suggestion touching
  `ProofSystemEquivalence.lean` or the new `HilbertCompleteness` import.
- Sorries: `grep -rn 'sorry' Cslib/Logics/Propositional/ProofSystemEquivalence.lean` — zero
  matches.
- Axioms: `#print axioms` on all three new theorems (via `lake env lean` on a scratch file) —
  each depends on exactly `[propext, Classical.choice, Quot.sound]`, no new axioms.
- Existing statements: diffed against the pre-Phase-1 commit; every removed/changed line falls
  inside the module docstring's opening paragraph, `## Main Results`, or `## Dependencies` —
  none of the nine existing TFAE theorem signatures or proofs were touched.
- **`lake test`: FAILS**, but not due to this task's changes — see Blocker below.

## Blocker (out-of-territory, `lake test` only)

`lake test` fails on `CslibTests.GrindLint`: a `#guard_msgs` mismatch reports new `grind`
instantiations from `Cslib.Logic.Bimodal.Axiom.linear_since.sizeOf_spec`,
`Cslib.Logic.Bimodal.Axiom.linear_until.sizeOf_spec`,
`Cslib.Logic.Temporal.Axiom.linear_since.sizeOf_spec`, and
`Cslib.Logic.Temporal.Axiom.linear_until.sizeOf_spec`. `git log` traces these to
concurrently-landed sibling-task commits ("pre-land Bimodal bridge lemmas", "pre-land Temporal
bridge lemma") that introduced new `grind`-eligible declarations without a corresponding
`#grind_lint skip` entry in `CslibTests/GrindLint.lean`. This task's delegation contract
restricts edits to `Cslib/Foundations/Logic/ProofSystem.lean` and
`Cslib/Logics/Propositional/ProofSystemEquivalence.lean` only, so fixing `GrindLint.lean` or the
`Bimodal`/`Temporal` axiom declarations is out of scope for this implementer. Re-ran `lake test`
a second time after further sibling commits landed and the failure persisted identically,
confirming it is not transient. **Needs**: a `#grind_lint skip` entry (or underlying fix) for the
four flagged declarations, to be applied by whichever task owns `Cslib/Logics/Bimodal` /
`Cslib/Logics/Temporal`.

## Impacts

- The proof-system × logic TFAE matrix documented in
  `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` now has two independent fourth nodes
  on each closed family (tableau decision procedure, algebraic validity), fully symmetric across
  CPL/IPL/MPL.
- No change to any existing public API; purely additive.

## Follow-ups

- Optional (out of scope, per report §8): a one-line cross-reference from
  `Cslib/Foundations/Logic/ProofSystem.lean:55` to the three new `...WithAlgebraTfae` theorems,
  once the folds exist, would further improve discoverability.
- The `CslibTests.GrindLint` failure documented above needs to be resolved by the
  Bimodal/Temporal-owning task before the full CSLib CI sequence can go green again.

## References

- `specs/615_algebraic_node_proof_system_tfae/plans/01_algebraic-node-tfae-folds.md`
- `specs/615_algebraic_node_proof_system_tfae/reports/01_algebraic-node-tfae.md`
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean`
