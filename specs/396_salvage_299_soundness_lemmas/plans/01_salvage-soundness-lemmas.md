# Implementation Plan: Salvage task-299 Soundness Proof-Engineering Lemmas

- **Task**: 396 - Evaluate and salvage architecture-independent proof-engineering lemmas from the stopped task-299 modal-K soundness re-attempt (`wip/task-299-soundness-refactor` @ `27d93e2d`) into current main modal-tableau soundness code
- **Status**: [NOT STARTED]
- **Effort**: 4.5 hours
- **Dependencies**: None (all salvage dependencies already resolve on main)
- **Research Inputs**:
  - reports/01_salvage-299-soundness-lemmas.md
  - reports/02_encoding-staleness-correction.md (CRITICAL — supersedes report 01's Phase A for or/and)
- **Artifacts**: plans/01_salvage-soundness-lemmas.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Transplant the architecture-independent (accessibility-blind) proof-engineering payload from the
stopped 299 soundness re-attempt into current main. The payload is two independent tranches: (1)
four recognizer inverse-characterization lemmas (`modal{Neg,Imp,Or,And}Of?_eq_some`) for
`Cslib/Logics/Modal/Tableau/Defs.lean`, and (2) a satisfaction bridge block (`sfSat`,
`sfSat_pos`, `sfSat_neg`, `RuleResultSat`, `applyPropRule_sat`, `tryAllPropRules_sat`) for
`Cslib/Logics/Modal/Tableau/SoundnessStep.lean`. Definition of done: all salvaged items land on
main with zero `sorry`/axioms and the full CSLib CI pipeline green. The global-`Accessibility`
core (`modalStepBranch_preserves_sat`), `Proposition.beqToEq`, and `branchSatisfiable` /
`modalClosed_unsat` are explicitly out of scope (superseded, redundant, or already current).

### Research Integration

- **Report 01** catalogs the acc-free payload and classifies each candidate portable vs
  architecture-coupled. Its Phase-A recommendation to cherry-pick `modalOrOf?_eq_some` /
  `modalAndOf?_eq_some` verbatim is **corrected** by report 02.
- **Report 02 (CRITICAL)**: commit `27d93e2d` predates task 441, which replaced the Łukasiewicz
  and/or encoding with native `Proposition.and` / `Proposition.or` constructors. The branch's
  `modalOrOf?_eq_some` (concludes `φ = .imp (.imp a .bot) b`) and `modalAndOf?_eq_some`
  (concludes `φ = .imp (.imp a (.imp b .bot)) .bot`) are **FALSE on main** and must be RESTATED
  against native `.or a b` / `.and a b` — not cherry-picked. `modalNegOf?_eq_some`
  (`φ = .imp ψ .bot`) and `modalImpOf?_eq_some` (`φ = .imp a b`) port cleanly. `applyPropRule_sat`
  is a template, not a copy: its and/or proof-arms must consume the restated characterizations.
- **Grounding confirmed this planning session**: `Defs.lean` on main already has native `.or`/`.and`
  recognizers (lines 157, 173) plus forward lemmas `modalOrOf?_or` (164), `modalAndOf?_and` (180),
  `modalNegOf?_neg` (145), `modalImpOf?_imp` (207), but no inverse `_eq_some` lemmas. The prop-rule
  engine (`applyPropRule`/`tryAllPropRules`/`RuleResult` from `Foundations/Logic/Tableau/`) is
  already imported and used across the modal soundness stack (`FmpMeasure.lean`), so the Phase-B
  bridge dependencies all resolve on main. `SoundnessStep.lean` already has `branchSatisfiable`
  (line 63) and `modalClosed_unsat` (line 92) — confirmed present, out of scope.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in the dispatch and `roadmap_flag` is not set; no ROADMAP.md phases.

## Goals & Non-Goals

**Goals**:
- Add the four `modal{Neg,Imp,Or,And}Of?_eq_some` inverse-characterization lemmas to `Defs.lean`,
  with or/and RESTATED against native constructors.
- Add the encoding-independent satisfaction predicates (`sfSat`, `sfSat_pos`, `sfSat_neg`,
  `RuleResultSat`) to `SoundnessStep.lean`.
- Add `applyPropRule_sat` and `tryAllPropRules_sat` with and/or proof-arms reworked for native
  constructors.
- Keep every phase at a green `lake build`; finish with the full CI pipeline green and zero
  `sorry`/axioms.

**Non-Goals**:
- Merging `modalStepBranch_preserves_sat` or any global-`Accessibility` machinery
  (`maxWorld`/`nextWorld`/`modalFreshWorld`, Branch/Rules additions) — superseded, out of scope.
- Copying `Proposition.beqToEq` — main already has the strictly-better
  `LawfulBEq.eq_of_beq` one-liner (`SoundnessStep.lean:83`).
- Re-adding or downgrading `branchSatisfiable` / `modalClosed_unsat` — already current; do not
  downgrade the shared `branchSatisfiable.{v,u}` to `Type 0` (main's completeness loop
  instantiates its universes explicitly).
- Any wholesale merge of the 299 branch (its full tip is UNBUILT).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Cherry-picking stale or/and characterizations (false on main) | H | M | Report 02 mandate: RESTATE or/and against native `.or`/`.and`; verify each `_eq_some` by `#check`/build, not by copying branch text |
| `applyPropRule_sat` and/or arms assume Łukasiewicz `rw` rewrites | H | M | Rework and/or arms to consume Phase-2 restated lemmas + native constructors; transfer neg/imp arms directly |
| Bridge block has no consumer on main / universe mismatch with `branchSatisfiable.{v,u}` | M | M | Keep bridge monomorphic `{W : Type}` per report guidance (standalone lemmas, no downgrade of shared predicate); if a genuine universe wall appears, restate the obligation rather than adding `sorry` |
| `modalImpOf?_eq_some` needs the branch's nested `split` that may not collapse on main | L | M | Re-derive fresh with `unfold; split; simp_all`; fall back to manual nested `split` only if needed |
| `lake shake` flags a newly-unused import from added defs | L | L | Bridge uses only already-imported symbols; run shake in Phase 5 and adjust imports if flagged |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel. Phases 2 (Defs.lean) and 3
(SoundnessStep.lean) touch disjoint files and are parallel-safe.

### Phase 1: Baseline and Reference Extraction [COMPLETED]

**Goal**: Establish a green baseline for the target files and capture the exact `27d93e2d`
source of the salvage payload as a read-only reference (no production edits).

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Modal.Tableau.Defs Cslib.Logics.Modal.Tableau.SoundnessStep`
      and confirm green baseline.
- [ ] `git show 27d93e2d:Cslib/Logics/Modal/Tableau/Soundness.lean` and extract the acc-free block
      (approx lines 158-215: `sfSat`, `sfSat_pos/neg`, `RuleResultSat`, `applyPropRule_sat`,
      `tryAllPropRules_sat`) and the four `*_eq_some` proofs into a scratch reference note.
- [ ] Confirm main's native encoding: `Defs.lean` `modalOrOf?` matches `.or a b` (line 157),
      `modalAndOf?` matches `.and a b` (line 173); note that branch's or/and characterizations are
      stale and must be restated.
- [ ] Record the exact `#check` signatures the restated lemmas must have (target conclusions:
      `φ = .or a b`, `φ = .and a b`, `φ = .imp ψ .bot`, `φ = .imp a b`).

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- None (read-only baseline; scratch reference only, not committed to `Cslib/`).

**Verification**:
- Baseline `lake build` of both target modules passes.
- Reference note captures payload signatures and the encoding-staleness delta.

---

### Phase 2: Recognizer Inverse-Characterization Lemmas [COMPLETED]

**Goal**: Add the four `modal{Neg,Imp,Or,And}Of?_eq_some` inverse lemmas to `Defs.lean` — the
highest-value, lowest-risk, friction-relieving deliverable — with or/and restated against native
constructors.

**Tasks**:
- [ ] Add `modalNegOf?_eq_some {φ ψ} (h : modalNegOf? φ = some ψ) : φ = .imp ψ .bot` next to the
      existing `modalNegOf?_neg` forward lemma; prove by `unfold modalNegOf? at h; split at h <;> simp_all`.
- [ ] Add `modalImpOf?_eq_some {φ a b} (h : modalImpOf? φ = some (a, b)) : φ = .imp a b`; re-derive
      fresh (branch's nested `split` may collapse on main).
- [ ] Add `modalOrOf?_eq_some {φ a b} (h : modalOrOf? φ = some (a, b)) : φ = .or a b` — RESTATED
      against native `.or`, NOT cherry-picked; prove `unfold modalOrOf? at h; split at h <;> simp_all`.
- [ ] Add `modalAndOf?_eq_some {φ a b} (h : modalAndOf? φ = some (a, b)) : φ = .and a b` — RESTATED
      against native `.and`; same idiom.
- [ ] Add concise docstrings matching the existing forward-lemma style in `Defs.lean`.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/Defs.lean` — add four `_eq_some` lemmas beside the forward lemmas
  (near lines 145-208).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.Defs` green.
- Each lemma's stated conclusion uses the native/target shape (`#check` confirms
  `.or a b` / `.and a b` / `.imp ψ .bot` / `.imp a b`); no Łukasiewicz shapes.
- No `sorry`/axiom introduced (`lean_verify` or `#print axioms` on each lemma).

---

### Phase 3: Satisfaction Predicates (Encoding-Independent) [COMPLETED]

**Goal**: Add the encoding-independent satisfaction-predicate scaffolding
(`sfSat`, `sfSat_pos`, `sfSat_neg`, `RuleResultSat`) to `SoundnessStep.lean` using the
monomorphic `{W : Type}` convention.

**Tasks**:
- [ ] Add `sfSat {W : Type} (m : Model W Atom) (f : WorldIndex → W) (sf) : Prop` — positive formula
      holds at `f sf.label`, negative fails there (port verbatim; report 01 items 1-3 unchanged).
- [ ] Add `sfSat_pos`, `sfSat_neg` trivial constructor lemmas.
- [ ] Add `RuleResultSat {W : Type} (m) (f) (R : RuleResult ...) : Prop` matching on
      `linear`/`branching`/`persistent`/`notApplicable` (RuleResult is already in scope via the
      imported Foundations engine).
- [ ] Keep `{W : Type}` monomorphic; do NOT downgrade the shared `branchSatisfiable.{v,u}`.
- [ ] Add docstrings consistent with `SoundnessStep.lean` style.

**Timing**: 0.75 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` — add the four satisfaction-predicate
  declarations (defs + two constructor lemmas).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.SoundnessStep` green.
- `RuleResultSat` type-checks against the imported `RuleResult`; `sfSat` type-checks against
  `Model`/`Satisfies`.
- No `sorry`/axiom introduced.

---

### Phase 4: Propositional-Rule Satisfaction Bridge [NOT STARTED]

**Goal**: Add `applyPropRule_sat` and `tryAllPropRules_sat` — the reusable bridge theorem that
applying a propositional rule to a satisfied signed formula preserves satisfiability — with and/or
proof-arms reworked for native constructors.

**Tasks**:
- [ ] Add `applyPropRule_sat {W : Type} (m) (f) (sf) (rule) (hsf : sfSat m f sf) : RuleResultSat m f (applyPropRule modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf rule)`.
- [ ] Rework the and/or case-arms: consume Phase-2 `modalOrOf?_eq_some` / `modalAndOf?_eq_some`
      (native `.or`/`.and`) instead of the branch's Łukasiewicz `rw`; transfer neg/imp arms
      directly.
- [ ] Add `tryAllPropRules_sat` as the thin wrapper over `applyPropRule_sat` (branch `:388`),
      re-derived once `applyPropRule_sat` builds.
- [ ] Build from Phase-2 lemmas + `sfSat_pos`/`sfSat_neg` + `Model`/`Satisfies` only; introduce no
      `Accessibility`/`acc`/`m.r` reference.
- [ ] If a universe or missing-consumer wall appears, restate the obligation against the native
      predicates rather than adding any `sorry`.

**Timing**: 1.5 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` — add `applyPropRule_sat`, `tryAllPropRules_sat`.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.SoundnessStep` green.
- `#print axioms applyPropRule_sat` / `tryAllPropRules_sat` show no `sorry`/axiom.
- Signatures are acc-free (grep the new block for `Accessibility`/`acc`/`m.r` — none).

---

### Phase 5: Full CI Verification and Summary [NOT STARTED]

**Goal**: Run the complete CSLib CI pipeline over the changed modules, confirm zero technical
debt, and write the execution summary.

**Tasks**:
- [ ] `lake build` (full) green.
- [ ] `lake test` (CslibTests) green.
- [ ] `lake exe checkInitImports` green.
- [ ] `lake exe lint-style` green.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — resolve any import findings on the
      touched files.
- [ ] Grep the two changed files for `sorry`/`admit`/`axiom` — confirm none.
- [ ] Write `summaries/01_salvage-soundness-lemmas-summary.md` cataloging salvaged vs excluded
      items and CI results.

**Timing**: 0.75 hours

**Depends on**: 4

**Files to modify**:
- `specs/396_salvage_299_soundness_lemmas/summaries/01_salvage-soundness-lemmas-summary.md` (new).

**Verification**:
- All five CI commands exit clean.
- Summary records the six-item payload landed and the excluded set (`modalStepBranch_preserves_sat`,
  `Proposition.beqToEq`, `branchSatisfiable`/`modalClosed_unsat`).

---

## Testing & Validation

- [ ] `lake build` full green (all Modal tableau modules recompile).
- [ ] `lake test` green.
- [ ] `lake exe checkInitImports` green.
- [ ] `lake exe lint-style` green.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` clean on touched files.
- [ ] Four `*_eq_some` lemmas conclude native/target shapes (no Łukasiewicz).
- [ ] `#print axioms` on all salvaged declarations shows no `sorryAx`.
- [ ] New bridge block contains no `Accessibility`/`acc`/`m.r` token.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/Defs.lean` — four `modal*Of?_eq_some` inverse lemmas.
- `Cslib/Logics/Modal/Tableau/SoundnessStep.lean` — `sfSat`, `sfSat_pos`, `sfSat_neg`,
  `RuleResultSat`, `applyPropRule_sat`, `tryAllPropRules_sat`.
- `specs/396_salvage_299_soundness_lemmas/plans/01_salvage-soundness-lemmas.md` (this file).
- `specs/396_salvage_299_soundness_lemmas/summaries/01_salvage-soundness-lemmas-summary.md`.

## Rollback/Contingency

- All changes are additive (new lemmas/defs beside existing code) — `git checkout -- <file>` on
  the two touched files reverts cleanly with no dependents to break.
- If Phase 4 hits a genuine architecture wall (no consumer / universe conflict), land Phases 2-3
  (independently valuable, especially the recognizer lemmas) and mark Phase 4 [BLOCKED] with the
  obligation documented for a follow-up — never bridge with `sorry`/axiom.
- Per-phase green milestones mean each completed phase is independently committable and revertible.
