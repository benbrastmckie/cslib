# Implementation Plan: Task #401 — Polymorphic Evaluator (Bool / Prop / DPLL) Consolidation

- **Task**: 401 - Polymorphic evaluator Bool/Prop/DPLL reconciliation
- **Status**: [IMPLEMENTING]
- **Effort**: 2.5 hours (Phases 1–2 core; Phase 3 optional/conditional)
- **Dependencies**: None
- **Research Inputs**: specs/401_polymorphic_evaluator_bool_prop_dpll/reports/01_polymorphic-evaluator-bool-prop-dpll.md
- **Artifacts**: plans/01_evaluator-bool-prop-dpll-docs.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This is a **documentation-consolidation task, not new theory**. The research confirms the full
evaluator infrastructure already exists and builds: `AlgEvaluate` (the GHA-polymorphic evaluator),
`Evaluate` (Prop-valued), `BoolEvaluate` (Bool-valued, computable) + its `Decidable` instances,
and the two bridge theorems `propEvaluateEq` / `boolEvaluateEq` proving `Evaluate` and
`BoolEvaluate` are `AlgEvaluate` instantiated at `Prop` and `Bool`. The soundness chain to
`prop_strong_soundness` is already provable through the existing lemma chain (no new bridge lemma
required). The work is to (1) fix stale theorem-name references in the `Bridge.lean` module
docstring, (2) consolidate the three-evaluator narrative into ONE canonical "evaluation story" in
`Bridge.lean`, (3) add cross-reference docstrings in `Bool.lean` and `Algebra.lean` naming the
canonical DPLL/SAT decision path and leaving a forward-looking anchor for Matthew Doty's DPLL/Tseitin
work, and (4) OPTIONALLY add one or two additive algebraic-validity convenience lemmas, gated on a
clean completeness round-trip and never sorried.

Definition of done: docstring drift fixed, canonical story present, cross-references added, full CI
green (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`),
zero new sorries/axioms.

### Research Integration

Integrated from `reports/01_polymorphic-evaluator-bool-prop-dpll.md`:
- Confirmed declarations and exact line numbers in `Semantics/Bool.lean`, `Semantics/Algebra.lean`,
  `Semantics/Algebra/Bridge.lean`.
- Gap 1 (DEFECT): `Bridge.lean` module docstring (lines 22, 25, 31, 36) references the stale names
  `prop_evaluate_eq` / `bool_evaluate_eq`; actual declarations are `propEvaluateEq` / `boolEvaluateEq`
  (verified directly against the source: theorems on lines 58 and 78).
- Gap 2: no single "ONE story" doc block tying the three evaluators together.
- Gap 4: DPLL/SAT entry point (`BoolEvaluate`, `instDecidableTautology`) not surfaced as canonical;
  Doty's DPLL/Tseitin/CNF work is NOT yet in-tree (forward-looking anchor only).
- Gap 3 (optional): no `baValid_imp_tautology` / `tautology_iff_baValid` lemma; the easy direction is
  self-contained, the hard direction needs `CPL.hilbert_alg_complete` (verify signature first).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap context provided to this planning run; not modifying ROADMAP.md.

## Goals & Non-Goals

**Goals**:
- Eliminate the stale theorem-name references in the `Bridge.lean` module docstring.
- Establish `Bridge.lean` as the single canonical home of the "ONE evaluation story" (evaluator
  table + soundness-chain diagram), keeping `Valuation = Atom → Prop` documented as canonical.
- Cross-reference the story from `Bool.lean` and `Algebra.lean`, naming `BoolEvaluate` +
  `instDecidableTautology` as the canonical DPLL/SAT decision path and leaving a docstring anchor
  for forthcoming DPLL/Tseitin work.
- Keep the entire change zero-debt: no new sorries, no new axioms, CI green.

**Non-Goals**:
- No new evaluator definitions, no refactor of `AlgEvaluate` / `Evaluate` / `BoolEvaluate`.
- No new soundness bridge lemma (the existing chain already discharges it).
- No DPLL/CNF/Tseitin code (not in scope; only a forward-looking docstring anchor).
- Renaming `Valuation` away from `Atom → Prop` (must stay canonical for the canonical model).
- Forcing the `tautology_iff_baValid` round-trip if it is not a clean one-liner (Phase 3 is optional).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Docstring edits accidentally change a proof or break `module` / `@[expose] public section` blocks | M | L | Edit only comment/docstring text; never touch the `theorem` bodies; run scoped `lake build` after each file |
| Optional lemma (`tautology_iff_baValid`) hard direction does not have a clean round-trip | M | M | Phase 3 is explicitly optional/conditional: verify `CPL.hilbert_alg_complete` signature FIRST; if not clean, ship only `baValid_imp_tautology` (easy direction) or skip entirely — never `sorry` |
| New lemma trips lint (docBlame / defsWithUnderscore / defLemma) | L | M | Give any new lemma a docstring, a lowerCamelCase name, and `lemma`/`theorem`; run `lake lint` |
| `lake shake` flags an import change | L | L | No imports are added in core phases; if Phase 3 needs a completeness import, run `lake shake --fix` and re-verify |
| Cross-reference points at a non-existent name | L | L | Reference only verified names (`propEvaluateEq`, `boolEvaluateEq`, `instDecidableTautology`, `BoolEvaluate`) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |

Phases within the same wave can execute in parallel. Phase 3 is optional/conditional and may be
skipped without affecting completion of the core task.

### Phase 1: Fix docstring drift and write the canonical "ONE evaluation story" [COMPLETED]

**Goal**: Correct the stale theorem-name references and expand the `Bridge.lean` module docstring
into the single authoritative narrative tying `Evaluate`, `BoolEvaluate`, and `AlgEvaluate` together.

**Tasks**:
- [ ] In `Semantics/Algebra/Bridge.lean` module docstring, replace `prop_evaluate_eq` → `propEvaluateEq`
      (occurrences at lines 22 and 31) and `bool_evaluate_eq` → `boolEvaluateEq` (occurrences at lines
      25 and 36). Four replacements total; confirm zero remaining `prop_evaluate_eq` / `bool_evaluate_eq`
      via grep after editing.
- [ ] Expand the module docstring into the canonical "ONE evaluation story" containing:
      - An evaluator table with columns: Evaluator | Type | Valuation | Role | `AlgEvaluate` specialization.
        Rows: `Evaluate` (Prop; `Valuation = Atom→Prop`; uniformity with Kripke + where
        soundness/completeness are stated; `AlgEvaluate · False` @ `Prop`, via `propEvaluateEq`);
        `BoolEvaluate` (Bool; `BoolValuation = Atom→Bool`; computable decision DPLL/SAT;
        `AlgEvaluate · false` @ `Bool`, via `boolEvaluateEq`); `AlgEvaluate` (GHA `H`; `Atom→H` + `bot_val`;
        common generalization / tiered soundness-completeness; —).
      - The soundness-chain diagram from the research report (`BoolEvaluate v φ = true`
        ⟺ `BoolEvaluate_eq_iff` ⟺ `Evaluate` ⟺ `propEvaluateEq` / `boolEvaluateEq` `AlgEvaluate`,
        and `SemanticEntails` / `prop_strong_soundness` stated in `Evaluate`).
      - An explicit note: "`Valuation` stays `Atom → Prop` — the canonical model construction needs it."
- [ ] Preserve the existing `module`, `import`, `public import`, and `@[expose] public section` lines and
      the `## References` section unchanged.
- [ ] Do NOT modify the `propEvaluateEq` / `boolEvaluateEq` theorem bodies.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` — fix 4 stale name references in the
  module docstring; expand the module docstring with the evaluator table, soundness-chain diagram,
  and the `Valuation = Atom→Prop` canonical note.

**Verification**:
- `grep -n "prop_evaluate_eq\|bool_evaluate_eq" Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean`
  returns nothing.
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Bridge` succeeds.
- Module docstring contains the evaluator table and soundness-chain diagram.

---

### Phase 2: Add cross-reference docstrings in Bool.lean and Algebra.lean [IN PROGRESS]

**Goal**: Point the two host files at the canonical story and explicitly name the DPLL/SAT decision
path, leaving a forward-looking anchor for Matthew Doty's DPLL/Tseitin work.

**Tasks**:
- [ ] In `Semantics/Bool.lean` ("Design Notes" / module docstring), add a cross-reference pointing at
      `boolEvaluateEq` / `propEvaluateEq` (in `Semantics/Algebra/Bridge.lean`) for the unified
      evaluation story, and explicitly name `BoolEvaluate` + `instDecidableTautology` as the canonical
      computable DPLL/SAT decision path.
- [ ] Add a short docstring pointer noting that a future DPLL/Tseitin/CNF procedure (Matthew Doty's
      forthcoming work — not yet in-tree) should refine `BoolEvaluate` / `instDecidableTautology` and
      reuse the existing Bool↔Prop bridge rather than re-deriving it. Keep `BoolEvaluate` and
      `instDecidableTautology` as the clearly-named anchors.
- [ ] In `Semantics/Algebra.lean` ("Main Definitions" / module docstring), note that `AlgEvaluate`
      specializes to `Evaluate` (via `propEvaluateEq`) and `BoolEvaluate` (via `boolEvaluateEq`), with
      a pointer to `Semantics/Algebra/Bridge.lean` for the consolidated story.
- [ ] Reference only verified declaration names; touch docstrings/comments only, no code.

**Timing**: 0.75 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Bool.lean` — docstring cross-reference + DPLL/SAT anchor note.
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` — docstring cross-reference to the bridges and
  the canonical story.

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Bool` and
  `lake build Cslib.Logics.Propositional.Semantics.Algebra` succeed.
- Each file's docstring references `propEvaluateEq` / `boolEvaluateEq` and `Bridge.lean`; `Bool.lean`
  names `BoolEvaluate` + `instDecidableTautology` as the DPLL/SAT path.

---

### Phase 3: (OPTIONAL / CONDITIONAL) Add algebraic-validity convenience lemma(s) [NOT STARTED]

**Goal**: Surface classical validity in algebraic vocabulary by adding `baValid_imp_tautology`, and —
only if a clean completeness round-trip exists — the full `tautology_iff_baValid`. This phase is
optional; skipping it does not block task completion.

**Tasks**:
- [ ] VERIFY FIRST: inspect the exact name and signature of `CPL.hilbert_alg_complete` (in
      `Semantics/Algebra/HilbertCompleteness.lean`, ~line 166) and the classical completeness theorem
      via `lean_local_search` / `lean_hover_info`. Confirm whether `Tautology φ → BAValid φ` composes
      cleanly from existing results (`prop_soundness_tautology`, classical completeness,
      `hilbert_alg_complete`).
- [ ] Add `baValid_imp_tautology : BAValid φ → Tautology φ` in `Semantics/Algebra/Bridge.lean`:
      instantiate `BAValid` at `H := Bool`, then rewrite with `boolEvaluateEq` and
      `tautology_iff_boolEvaluate_true`. (Easy, self-contained direction.)
- [ ] IF AND ONLY IF the round-trip is a clean one-liner: add the reverse direction and package as
      `tautology_iff_baValid : Tautology φ ↔ BAValid φ`. If it is NOT clean, ship only
      `baValid_imp_tautology` and record the iff as a documented roadmap note in the docstring —
      do NOT introduce a `sorry` or a vacuous placeholder.
- [ ] Give any new lemma a docstring, a lowerCamelCase name, and `lemma`/`theorem` keyword (lint
      compliance: docBlame, defsWithUnderscore, defLemma).

**Timing**: 1 hour (skippable)

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` — add `baValid_imp_tautology` (and
  conditionally `tautology_iff_baValid`).

**Verification**:
- `lean_verify` on any new lemma shows no `sorry` and no new axioms.
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Bridge` succeeds.
- If only the easy direction shipped, the docstring records the iff as a roadmap note.

---

## Testing & Validation

- [ ] `grep` confirms no remaining `prop_evaluate_eq` / `bool_evaluate_eq` in `Bridge.lean`.
- [ ] `lake build` (full project) is green.
- [ ] `lake exe checkInitImports` passes (every touched file still imports `Cslib.Init`).
- [ ] `lake exe lint-style` passes.
- [ ] `lake lint` passes (any new Phase 3 lemma is docstringed, lowerCamelCase, `lemma`/`theorem`).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (no spurious imports; if Phase 3
      adds a completeness import, minimize with `--fix`).
- [ ] `lake test` passes.
- [ ] No new sorries and no new axioms (`lean_verify` on any new declaration).

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` (docstring fix + canonical story; optional lemma)
- `Cslib/Logics/Propositional/Semantics/Bool.lean` (docstring cross-references)
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` (docstring cross-references)
- `specs/401_polymorphic_evaluator_bool_prop_dpll/summaries/01_evaluator-bool-prop-dpll-docs-summary.md` (on completion)

## Rollback/Contingency

- All core changes are docstring/comment edits confined to three files; revert via
  `git checkout -- <file>` for any file that regresses CI.
- Phase 3 is isolated and optional: if the optional lemma cannot be proved cleanly, drop it (or keep
  only `baValid_imp_tautology`) and leave the iff as a documented roadmap note — never `sorry`.
- If `lake shake` or `lake lint` flags an issue introduced by Phase 3, prefer dropping the optional
  lemma over weakening verification; the core documentation task (Phases 1–2) stands on its own.
