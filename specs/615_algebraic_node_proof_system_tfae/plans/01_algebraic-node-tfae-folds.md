# Implementation Plan: Algebraic Node in the Propositional Proof-System TFAE Families

- **Task**: 615 - Add algebraic semantic validity as a further equivalent node in the
  propositional proof-system TFAE families
- **Status**: [NOT STARTED]
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

### Phase 1: Add the import and the three algebraic folds [NOT STARTED]

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

### Phase 2: Record the closed-only decision in the module docstring [NOT STARTED]

- **Goal:** The module docstring documents the new theorems and states, with reasons, why the
  algebraic node lives on the closed families alone.
- **Tasks:**
  - [ ] Extend the opening paragraph (currently at `ProofSystemEquivalence.lean:21-27`) to
        mention algebraic semantics alongside the tableau decision procedure, and note that the
        closed families now carry two independent fourth nodes (tableau, algebra).
  - [ ] Add the three `...WithAlgebraTfae` entries to `## Main Results`.
  - [ ] Add `MPL.hilbert_alg_completeness`, `IPL.hilbert_alg_completeness`, and
        `CPL.hilbert_alg_completeness` to `## Dependencies`, labelled as the algebraic folds.
  - [ ] Add the section-level `/-! ## Algebraic Semantics Folds (closed formulas only) ... -/`
        docstring immediately before `section WithAlgebra`, transcribing the prose drafted in
        report §5.2: (a) the tier-matched predicates are empty-context notions, so the folds
        extend the `...Closed` families; (b) a context-based node was considered and deliberately
        not added, because `hilbert_alg_strong_complete_theory` is theory-generic over
        generalized Heyting algebras and a tier-matched form would need
        `HeytingAlgebra`/`BooleanAlgebra` instances on `RelLindenbaumAlgebra`, which carries only
        a `GeneralizedHeytingAlgebra` instance; (c) the constraint here is a universe pin rather
        than an extra typeclass, contrasting with `section WithTableau`.
  - [ ] Confirm no task number appears anywhere in the added prose.
  - [ ] Verify: `lake build Cslib.Logics.Propositional.ProofSystemEquivalence`.
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

### Phase 3: Full CSLib CI gate and zero-debt verification [NOT STARTED]

- **Goal:** The whole repository is green under the CSLib CI sequence, with no new sorries, no
  new axioms, and no change to the existing TFAE statements.
- **Tasks:**
  - [ ] `lake build` (full project).
  - [ ] `lake exe checkInitImports`.
  - [ ] `lake lint` — in particular check `docBlame`, `defLemma`, `defsWithUnderscore`, and
        `unusedSectionVars` on the three new theorems. Add `omit` only if `unusedSectionVars`
        actually fires.
  - [ ] `lake exe lint-style`.
  - [ ] `lake test`.
  - [ ] `lake shake --add-public --keep-implied --keep-prefix` — inspect output; do **not** apply
        a suggestion that removes the new `HilbertCompleteness` import.
  - [ ] Confirm zero sorries: `grep -rn 'sorry' Cslib/Logics/Propositional/ProofSystemEquivalence.lean`
        returns nothing.
  - [ ] Confirm axioms via `lean_verify` (or `#print axioms`) on all three new theorems: expect
        exactly `[propext, Classical.choice, Quot.sound]`.
  - [ ] Confirm the nine existing TFAE theorem statements are untouched by reading
        `git diff Cslib/Logics/Propositional/ProofSystemEquivalence.lean` and checking that every
        hunk falls inside the new import line, the `universe u` line, the new section, or a
        docstring.
  - [ ] `lake exe mk_all --module` is **not** required — no new file is added.
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
  - All seven CI steps exit zero.
  - Zero sorries, axioms exactly `[propext, Classical.choice, Quot.sound]`.
  - `git diff` confined to the new import, `universe u`, `section WithAlgebra`, and docstrings.

---

## Testing & Validation

- [ ] `lake build` green (full project).
- [ ] `lake exe checkInitImports` green.
- [ ] `lake lint` green — no new `docBlame`, `defLemma`, `defsWithUnderscore`, or
      `unusedSectionVars` warnings.
- [ ] `lake exe lint-style` green.
- [ ] `lake test` green.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no removal of the new import.
- [ ] Zero new sorries.
- [ ] `#print axioms` on the three new theorems yields `[propext, Classical.choice, Quot.sound]`.
- [ ] The nine existing TFAE theorem statements are byte-identical to their pre-change form.
- [ ] The module docstring states the closed-vs-context decision and its reason.
- [ ] No task number appears in the Lean file.

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
