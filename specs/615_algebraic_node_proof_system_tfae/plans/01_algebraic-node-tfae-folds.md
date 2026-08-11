# Implementation Plan: Algebraic Node in the Propositional Proof-System TFAE Families

- **Task**: 615 - Add algebraic semantic validity as a further equivalent node in the
  propositional proof-system TFAE families
- **Status**: [PARTIAL]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/615_algebraic_node_proof_system_tfae/reports/01_algebraic-node-tfae.md`
- **Artifacts**: plans/01_algebraic-node-tfae-folds.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md,
  `.claude/rules/cslib.md`, `.claude/rules/plan-compliance.md`
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add three new four-way TFAE theorems to `Cslib/Logics/Propositional/ProofSystemEquivalence.lean`
that fold algebraic semantic validity (`BAValid`, `HAValid`, `GHAValid`) onto the existing
**closed** three-way equivalences for CPL, IPL, and MPL. The research phase established that this
is pure composition with zero new lemmas: `CPL/IPL/MPL.hilbert_alg_completeness` are already
stated as "node 1 of the closed TFAE ↔ tier-matched algebraic validity", so each fold is a single
`tfae_have 1 ↔ 4 := <completeness theorem>`. The work is one new `public import`, one new section
containing three theorems, and module-docstring updates recording the closed-only decision.
Definition of done: `lake build` green, the CSLib CI sequence green, zero new sorries, axioms
unchanged at `[propext, Classical.choice, Quot.sound]`, and the nine existing TFAE theorem
statements byte-identical.

### Research Integration

The research report (`reports/01_algebraic-node-tfae.md`) compiled every line of the recommended
implementation against the live build via `lake env lean` on a scratch file. Findings carried
directly into this plan:

- **Section 5.2** of the report contains the complete literal code to write (import line, section,
  three theorems, module-docstring prose). This plan does not re-derive it — Phase 1 and Phase 2
  transcribe it.
- **Closed-only decision** (report §4): the tier-matched validity predicates are empty-context
  notions, and `RelLindenbaumAlgebra` carries only a `GeneralizedHeytingAlgebra` instance, so a
  tier-matched context-based node is not available. The non-tier-matched alternative compiles
  (report §6 Test D) but is rejected. This decision must be recorded in the module docstring.
- **No `Iff.trans` gotcha here** (report §4.1): unlike the IPL/MPL tableau folds at
  `ProofSystemEquivalence.lean:229-243`, there is no universe-invariance bridge in the chain, so
  the completeness term is supplied directly and the `rw`-vs-`Iff.trans` issue never arises.
- **Universe pin, not a typeclass** (report §5.2): `GHAValid`/`HAValid`/`BAValid` must be written
  `.{u, u}`, and an auto-bound `Type*` universe cannot be named, so each new theorem carries its
  own `{Atom : Type u} [DecidableEq Atom]` binder shadowing the file-level `variable`. This
  shadowing was verified to compile cleanly. The new section therefore introduces no `variable`
  line (contrast `section WithTableau`, which scopes `[Hashable Atom]`).
- **Five-way fold rejected** (report §5.4): a single Hilbert/ND/sequent/tableau/algebra theorem
  would force `[Hashable Atom]` onto the algebraic equivalence, violating the task's scope
  discipline. Two separate four-way folds off a shared three-way core is the shape to build.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context; no ROADMAP.md consulted.

## Goals & Non-Goals

**Goals**:
- Add `cplProofSystemsWithAlgebraTfae`, `iplProofSystemsWithAlgebraTfae`, and
  `mplProofSystemsWithAlgebraTfae` as four-way closed TFAE theorems with algebraic validity as
  node 4.
- Add the single `public import` of `Semantics.Algebra.HilbertCompleteness`.
- Record the closed-only decision, and its reason, in the module docstring so the shape reads as
  a decision rather than an omission.
- Mirror the existing typeclass hygiene: the new section introduces no typeclass burden on the
  six pure proof-theoretic equivalences.
- Pass the full CSLib CI sequence with zero new sorries and no new axioms.

**Non-Goals**:
- No context-based algebraic node (decided against; see report §4.2).
- No five-way tableau+algebra fold (decided against; see report §5.4).
- No new lemma, predicate, typeclass, notation, or `HeytingAlgebra`/`BooleanAlgebra` instance on
  `RelLindenbaumAlgebra`.
- No change to the statements of the nine existing TFAE theorems.
- No edit to `Cslib/Foundations/Logic/ProofSystem.lean` (report §8 records this as an optional
  out-of-scope follow-up).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `lake shake` strips or reshuffles the new `public import` | M | L | Report §7 predicts the import survives because it is genuinely used; run shake without `--fix` first, inspect the diff, and only apply if it does not remove the new import |
| `unusedSectionVars` fires because the new theorems shadow the file-level `Atom`/`[DecidableEq Atom]` | L | L | Report §7 predicts no `omit` is needed; confirm with `lake lint` in Phase 3 and add `omit` only if the linter actually complains |
| `docBlame` fires on the three new theorems | L | M | Write docstrings as part of Phase 1, in the tableau folds' numbered-node style — not deferred to a cleanup pass |
| Universe-binder shadowing rejected in the real file (research verified it only in a scratch file with a reproduced `variable` line) | H | L | Phase 1 ends with a scoped `lake build` of the module; if shadowing is rejected, the fallback is to move the three theorems into their own `universe u` section header without a file-level shadow, not to abandon the pin |
| Mathlib cache miss causing a 30-45 min rebuild | M | M | Run `lake exe cache get` before the first build (CSLib CI step 0) |
| Task-number citation leaking into the Lean file | L | L | `.claude/rules/no-task-references-in-deliverables.md` applies to `Cslib/**`; docstring prose must cite durable anchors (theorem names, file paths), never a task number |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Add the import and the three algebraic folds [COMPLETED]

- **Goal:** `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` contains a new
  `section WithAlgebra` with three documented four-way TFAE theorems, and the module compiles.
- **Tasks:**
  - [ ] Run `lake exe cache get` if the Mathlib cache is not already present.
  - [ ] Add `public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness` to
        the import block (after the existing `public import` lines, before
        `import Mathlib.Tactic.TFAE`).
  - [ ] Add `universe u` near the existing `variable {Atom : Type*} [DecidableEq Atom]` line
        (or inside the new section).
  - [ ] Open a new `section WithAlgebra` after `end WithTableau` and before
        `end Cslib.Logic.PL`. Introduce **no** `variable` line in this section — the constraint
        is a universe pin, not a typeclass.
  - [ ] Transcribe `cplProofSystemsWithAlgebraTfae` verbatim from report §5.2 (binder
        `{Atom : Type u} [DecidableEq Atom]`; node 4 `BAValid.{u, u} φ`; body
        `have h := cplProofSystemsTfaeClosed (Atom := Atom) φ` / `tfae_have 1 ↔ 2 := h.out 0 1` /
        `tfae_have 2 ↔ 3 := h.out 1 2` / `tfae_have 1 ↔ 4 := CPL.hilbert_alg_completeness` /
        `tfae_finish`).
  - [ ] Transcribe `iplProofSystemsWithAlgebraTfae` (node 4 `HAValid.{u, u} φ`, fold term
        `IPL.hilbert_alg_completeness`) and `mplProofSystemsWithAlgebraTfae` (node 4
        `GHAValid.{u, u} φ`, fold term `MPL.hilbert_alg_completeness`) the same way.
  - [ ] Give each of the three theorems a docstring in the tableau folds' style: a numbered node
        list plus a sentence naming which `...Closed` theorem supplies nodes 1-3 and which
        completeness theorem supplies `1 ↔ 4`. Cite theorem names, never task numbers.
  - [ ] Close the section with `end WithAlgebra`.
  - [ ] Verify: `lake build Cslib.Logics.Propositional.ProofSystemEquivalence`.
- **Timing:** 45 minutes (build time dominates)
- **Depends on:** none
- **Verification Tier:** local
- **Commit Mode:** per-substep
- **Scope Hypothesis:** This phase asserts exactly one file modified, one import line added, and
  three new theorems. Confirm at implementation time with
  `git status --short` (expect only `Cslib/Logics/Propositional/ProofSystemEquivalence.lean`) and
  `grep -c 'ProofSystemsWithAlgebraTfae' Cslib/Logics/Propositional/ProofSystemEquivalence.lean`
  (expect 3 declaration sites). If the count or file list differs, stop and reconcile before
  committing.
- **Files to modify:**
  - `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` - new import, `universe u`, new
    `section WithAlgebra` with three documented theorems
- **Verification:**
  - `lake build Cslib.Logics.Propositional.ProofSystemEquivalence` succeeds with no errors and no
    new warnings.
  - The three new declarations elaborate (no `sorry`, no `error`).
  - `git diff` shows no change to any of the nine existing TFAE theorem statements.

---

### Phase 2: Record the closed-only decision in the module docstring [COMPLETED]

- **Goal:** The module docstring documents the new theorems and states, with reasons, why the
  algebraic node lives on the closed families alone.
- **Tasks:**
  - [x] Extend the opening paragraph (currently at `ProofSystemEquivalence.lean:21-27`) to
        mention algebraic semantics alongside the tableau decision procedure, and note that the
        closed families now carry two independent fourth nodes (tableau, algebra).
  - [x] Add the three `...WithAlgebraTfae` entries to `## Main Results`.
  - [x] Add `MPL.hilbert_alg_completeness`, `IPL.hilbert_alg_completeness`, and
        `CPL.hilbert_alg_completeness` to `## Dependencies`, labelled as the algebraic folds.
  - [x] Add the section-level `/-! ## Algebraic Semantics Folds (closed formulas only) ... -/`
        docstring immediately before `section WithAlgebra`, transcribing the prose drafted in
        report §5.2: (a) the tier-matched predicates are empty-context notions, so the folds
        extend the `...Closed` families; (b) a context-based node was considered and deliberately
        not added, because `hilbert_alg_strong_complete_theory` is theory-generic over
        generalized Heyting algebras and a tier-matched form would need
        `HeytingAlgebra`/`BooleanAlgebra` instances on `RelLindenbaumAlgebra`, which carries only
        a `GeneralizedHeytingAlgebra` instance; (c) the constraint here is a universe pin rather
        than an extra typeclass, contrasting with `section WithTableau`.
        *(deviation: this section docstring was already transcribed verbatim from report §5.2 as
        part of the Phase 1 `section WithAlgebra` edit, since report §5.2 bundles the section
        docstring together with the section body; re-verified present and correct here rather
        than re-authored)*
  - [x] Confirm no task number appears anywhere in the added prose.
  - [x] Verify: `lake build Cslib.Logics.Propositional.ProofSystemEquivalence`.
- **Timing:** 20 minutes
- **Depends on:** 1
- **Verification Tier:** prose
- **Commit Mode:** per-substep
- **Files to modify:**
  - `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` - module docstring (opening
    paragraph, Main Results, Dependencies) and the new section docstring
- **Verification:**
  - Diff read-through confirms every changed hunk lies inside a `/-!` or `/--` comment region.
  - The docstring answers "context-based, closed, or both?" explicitly and gives the reason.
  - `grep -nE '[Tt]ask [0-9]+' Cslib/Logics/Propositional/ProofSystemEquivalence.lean` returns
    nothing.
  - `lake build Cslib.Logics.Propositional.ProofSystemEquivalence` still succeeds (module
    docstrings are load-bearing enough to break the build if malformed).

---

### Phase 3: Full CSLib CI gate and zero-debt verification [PARTIAL]

- **Goal:** The whole repository is green under the CSLib CI sequence, with no new sorries, no
  new axioms, and no change to the existing TFAE statements.
- **Tasks:**
  - [x] `lake build` (full project) — succeeds, 3325/3325 jobs, only pre-existing warnings in
        unrelated files (`Tableau/Intuitionistic/DecisionProcedure.lean`,
        `Tableau/Minimal/DecisionProcedure.lean`, `Modal/Tableau/FrameCompleteness.lean`).
  - [x] `lake exe checkInitImports` — exit 0.
  - [x] `lake lint` — zero warnings on `ProofSystemEquivalence.lean`; no `docBlame`, `defLemma`,
        `defsWithUnderscore`, or `unusedSectionVars` fired. No `omit` needed, as predicted.
  - [x] `lake exe lint-style` — exit 0.
  - [ ] `lake test` *(deviation: blocked — see below)*.
  - [x] `lake shake --add-public --keep-implied --keep-prefix` — no suggestion touching
        `ProofSystemEquivalence.lean` or the new `HilbertCompleteness` import.
  - [x] Confirm zero sorries: `grep -rn 'sorry' .../ProofSystemEquivalence.lean` returns nothing.
  - [x] Confirm axioms via `#print axioms` on all three new theorems: exactly
        `[propext, Classical.choice, Quot.sound]` for each.
  - [x] Confirm the nine existing TFAE theorem statements are untouched: diffed against the
        pre-Phase-1 commit and confirmed every removed/changed line falls inside the module
        docstring opening paragraph, `## Main Results`, or `## Dependencies` — no theorem
        signature or proof line touched.
  - [x] `lake exe mk_all --module` — confirmed not required; `Cslib.lean:566` already lists
        `ProofSystemEquivalence`.

**BLOCKER (Phase 3, `lake test` step only)**: `lake test` fails on `CslibTests.GrindLint`, with
a `#guard_msgs` mismatch reporting new `grind` instantiations from
`Cslib.Logic.Bimodal.Axiom.linear_since.sizeOf_spec`, `Cslib.Logic.Bimodal.Axiom.linear_until.sizeOf_spec`,
`Cslib.Logic.Temporal.Axiom.linear_since.sizeOf_spec`, and
`Cslib.Logic.Temporal.Axiom.linear_until.sizeOf_spec`. These four declarations live in
`Cslib/Logics/Bimodal/**` and `Cslib/Logics/Temporal/**`, which this task's territory contract
does not authorize editing (this implementer is scoped to
`Cslib/Foundations/Logic/ProofSystem.lean` and
`Cslib/Logics/Propositional/ProofSystemEquivalence.lean` only). Root-caused by `git log`: the
axioms were introduced by concurrently-landed sibling-task commits ("pre-land Bimodal bridge
lemmas", "pre-land Temporal bridge lemma") that added new `grind`-eligible declarations without
a corresponding `#grind_lint skip` entry in `CslibTests/GrindLint.lean` — unrelated to this
task's Propositional file. Re-ran `lake test` a second time after further sibling commits landed
(`f086905d`) and the failure persisted identically, confirming it is not transient.
**What is needed to unblock**: a `#grind_lint skip` entry added for the four flagged
declarations (or their fix) in `CslibTests/GrindLint.lean`, which belongs to the sibling
Bimodal/Temporal task's territory, not this one.
**Prohibited workarounds**: not applicable — no `sorry`/vacuous placeholder was considered; this
is a full-repo test-suite gate failure outside this task's edit scope, not a gap in this task's
own proof content.
- **Timing:** 30 minutes (dominated by full build and test)
- **Depends on:** 2
- **Verification Tier:** full
- **Commit Mode:** per-substep
- **Scope Hypothesis:** This phase asserts the existing nine TFAE theorems are unchanged and that
  no file other than `ProofSystemEquivalence.lean` is modified. Confirm with
  `git status --short` and a hunk-by-hunk read of `git diff`. A modification outside the four
  permitted regions listed above falsifies the hypothesis and must be reverted or justified.
- **Files to modify:**
  - None expected; only lint-driven touch-ups to
    `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` if a linter fires
- **Verification:**
  - Six of seven CI steps exit zero; `lake test` fails on `CslibTests.GrindLint`, root-caused to
    concurrently-landed sibling-task commits outside this task's territory (see BLOCKER above).
  - Zero sorries, axioms exactly `[propext, Classical.choice, Quot.sound]`.
  - `git diff` confined to the new import, `universe u`, `section WithAlgebra`, and docstrings.

---

## Testing & Validation

- [x] `lake build` green (full project).
- [x] `lake exe checkInitImports` green.
- [x] `lake lint` green — no new `docBlame`, `defLemma`, `defsWithUnderscore`, or
      `unusedSectionVars` warnings.
- [x] `lake exe lint-style` green.
- [ ] `lake test` green *(blocked by `CslibTests.GrindLint` failure outside this task's territory
      — see Phase 3 BLOCKER)*.
- [x] `lake shake --add-public --keep-implied --keep-prefix` reports no removal of the new import.
- [x] Zero new sorries.
- [x] `#print axioms` on the three new theorems yields `[propext, Classical.choice, Quot.sound]`.
- [x] The nine existing TFAE theorem statements are byte-identical to their pre-change form.
- [x] The module docstring states the closed-vs-context decision and its reason.
- [x] No task number appears in the Lean file.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` — one new `public import`,
  `universe u`, `section WithAlgebra` with `cplProofSystemsWithAlgebraTfae`,
  `iplProofSystemsWithAlgebraTfae`, `mplProofSystemsWithAlgebraTfae`, plus module and section
  docstring updates.
- `specs/615_algebraic_node_proof_system_tfae/plans/01_algebraic-node-tfae-folds.md` (this file).
- `specs/615_algebraic_node_proof_system_tfae/summaries/01_algebraic-node-tfae-folds-summary.md`
  (produced by `/implement`).

## Rollback/Contingency

All changes are confined to one file and are purely additive. To revert:
`git checkout HEAD -- Cslib/Logics/Propositional/ProofSystemEquivalence.lean` (only from a clean
or snapshotted tree — see `.claude/rules/git-workflow.md`'s "No Destructive Git on Uncommitted
Work"; run `bash .claude/scripts/git-snapshot.sh 615` first if the tree is dirty).

Contingencies:
- If the `{Atom : Type u}` shadowing is rejected in the real file, move the three theorems under
  an explicit `universe u` section header rather than dropping the `.{u, u}` pin — the pin is part
  of the statement, since there is no universe-invariance lemma for algebraic validity.
- If `lake shake` insists on removing the new import, keep the import and record the shake
  suggestion as a false positive in the implementation summary rather than deleting a genuinely
  used import.
- If a phase cannot be completed as written, mark it `[BLOCKED]` and escalate per
  `.claude/rules/plan-compliance.md` — do not substitute an alternative proof strategy.
