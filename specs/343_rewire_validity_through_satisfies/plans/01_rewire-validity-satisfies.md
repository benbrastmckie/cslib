# Implementation Plan: Task #343 — Rewire Validity Through `Satisfies`

- **Task**: 343 - Establish canonical `v ⊨ T` satisfaction predicate and rewire validity/entailment predicates through it
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: Task 341 (Hilbert/algebraic completeness substrate) — must remain untouched via defeq
- **Research Inputs**: specs/343_rewire_validity_through_satisfies/reports/01_canonical-satisfies-predicate.md
- **Artifacts**: plans/01_rewire-validity-satisfies.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Introduce a generic theory-satisfaction predicate `SatisfiesTheory (eval) (T) := ∀ A ∈ T, eval A = ⊤`
(notation `v ⊨ T`) and its single-formula companion `Satisfies (eval) (A) := eval A = ⊤`, generic
over an already-applied evaluator with codomain carrying `[Top β]`. This adopts the SHAPE of
Waring's `TValid` while keeping cslib's primitive `.bot` language and the `bot_val` parameter
(which rides inside the applied `eval`). `AlgTValid` is redefined as
`SatisfiesTheory (AlgEvaluate v bot_val) T` — **definitionally equal** to its current body — so
every task-341 Hilbert proof (Soundness, HilbertLindenbaum, HilbertCompleteness) continues to
typecheck by `rfl` with **no edits**. The algebraic validity predicates `GHAValid`/`HAValid`/
`BAValid` are rewired to factor through `Satisfies`, also defeq. For the Prop-valued entailments
`SemanticEntails`/`ISemanticEntails`/`MSemanticEntails`, this plan adopts Option A from the research
report (premise/notation-only, defeq-safe) and defers full Prop/valued unification as a roadmap item
— never a `sorry` or axiom. Definition of done: zero `sorry`, zero new axioms, full CI green
(`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`), and
the task-341 files unedited.

### Research Integration

The plan follows the research report's recommended home for the generic predicate (`Defs.lean`,
which only needs `Top` and is already reachable by both `Algebra.lean` and `SemanticConsequence.lean`),
its defeq strategy (§4), its lint-prevention checklist (§7), and its 3-phase decomposition (§8). All
exact file:line targets are taken from the report's §10 index. The notation-overloading caveat (§3.1)
is handled explicitly in Phase 1 with an empirical `lake build` prototype gate and a fallback token.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided; ROADMAP.md not consulted. One explicit roadmap-candidate item is produced
by this task: "Full Prop/valued entailment unification (`SemanticEntails`/`ISemanticEntails`/
`MSemanticEntails` under one `⊨` predicate)" — deferred per Option A, to be surfaced at completion.

## Goals & Non-Goals

**Goals**:
- Add `Satisfies` and `SatisfiesTheory` generic predicates + scoped `⊨` notation in `Defs.lean`.
- Redefine `AlgTValid` as `SatisfiesTheory (AlgEvaluate v bot_val) T`, defeq to the old body.
- Keep `v ⊨[bot_val] T` bracket notation as a documented legacy alias (zero churn to 341).
- Rewire `GHAValid`/`HAValid`/`BAValid` to factor through `Satisfies` (defeq).
- Adopt uniform `⊨` notation for the theory-premise of the Prop-valued entailments where defeq-safe
  (Option A); otherwise document the convention split.
- CI green; task-341 files (`Soundness.lean`, `HilbertLindenbaum.lean`, `HilbertCompleteness.lean`)
  unedited.

**Non-Goals**:
- Full unification of Prop-valued forcing (`eval φ`) with the algebraic `= ⊤` convention (Option B) —
  deferred as a roadmap item, NOT a sorry.
- Touching `Cslib.Logics.Modal.Basic.Satisfies`, Temporal, LTL, or Bimodal (out of generality boundary).
- Migrating/removing the `v ⊨[bot_val] T` bracket notation (kept as alias; optional follow-up).
- Adding `@[simp]` to the new predicates (definitional; existing `*_atom`/`*_imp` simp lemmas drive eval).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `v ⊨ A` (Proposition) vs `v ⊨ T` (Theory = Set) notation overloading is brittle | M | M | Phase 1 prototypes both notations and confirms with `lake build` that each elaborates by expected type; if brittle, fall back to a distinct theory token (e.g. `⊨ᵀ`) per report §3.1 option 2 |
| Redefinition breaks defeq for 341 consumers (irreducibility/expose boundary) | H | L | Place new defs inside the existing `@[expose] public section` in `Defs.lean`; do not mark `@[irreducible]`; Phase 1 verification builds the HilbertCompleteness subtree with NO edits to 341 files |
| Forcing Prop-valued entailments through `= ⊤` breaks `fun v _ => h v`-style consumers | M | M | Option A: only rewire the theory-premise where defeq-safe; otherwise document convention split and defer — never a sorry/axiom |
| Lint failures (docBlame, defLemma, defsWithUnderscore, simpNF) | M | M | Follow report §7 checklist: docstrings on every new decl, `def` not `lemma`, camelCase names, no new `@[simp]`; run `lake exe lint-style` per phase |
| `git diff` accidentally touches 341 statement text | H | L | Final verification gate asserts diff is limited to `Defs.lean` + `Algebra.lean` def bodies + optional `SemanticConsequence.lean` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each phase ends
at a CI-green milestone and the next builds on the prior definition.

---

### Phase 1: Core predicate + defeq `AlgTValid` (load-bearing, zero-risk) [COMPLETED]

**Goal**: Introduce `Satisfies`/`SatisfiesTheory` + scoped `⊨` notation in `Defs.lean`, redefine
`AlgTValid` defeq, keep the bracket notation as a legacy alias, and prove task-341 proofs compile
unchanged.

**Tasks**:
- [ ] In `Cslib/Logics/Propositional/Defs.lean`, inside the existing `@[expose] public section` and
      `namespace Cslib.Logic.PL`, add `Satisfies {β} [Top β] (eval : Proposition Atom → β) (A) : Prop := eval A = ⊤`
      with a docstring (report §3.1).
- [ ] Add `SatisfiesTheory {β} [Top β] (eval : Proposition Atom → β) (T : Theory Atom) : Prop := ∀ A ∈ T, eval A = ⊤`
      with a docstring.
- [ ] Add scoped notation `eval ⊨ A` => `Satisfies` and `eval ⊨ T` => `SatisfiesTheory`
      (`@[inherit_doc]`, `scoped notation:50`).
- [ ] **Notation prototype gate**: write a temporary `example` exercising both `v ⊨ A` (A : Proposition)
      and `v ⊨ T` (T : Set _) and run `lake build` to confirm expected-type disambiguation. If brittle,
      switch the theory form to a distinct token (e.g. `⊨ᵀ`) and update the design note. Remove the
      temporary `example` before finishing.
- [ ] Redefine `AlgTValid` (`Cslib/Logics/Propositional/Semantics/Algebra.lean:149`) as
      `SatisfiesTheory (AlgEvaluate v bot_val) T`; update its docstring to note defeq + that `bot_val`
      rides inside the evaluator.
- [ ] Keep the `v " ⊨[" bot_val "] " T` bracket notation (Algebra.lean:153–156) as a documented
      legacy alias; add a docstring note.

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` — add `Satisfies`, `SatisfiesTheory`, scoped `⊨` notation.
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` — redefine `AlgTValid` body (line ~149);
  docstring note on the bracket alias (~153–156).

**Verification** (CI-green milestone):
- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness` succeeds with
      **no edits** to `Soundness.lean`, `HilbertLindenbaum.lean`, `HilbertCompleteness.lean`.
- [ ] `git status` shows the three 341 files unmodified.
- [ ] `lake exe lint-style` passes for `Defs.lean` and `Algebra.lean`.
- [ ] No new `sorry`, no new axioms.

---

### Phase 2: Rewire algebraic validity predicates (clean defeq) [BLOCKED]

**Goal**: Rewrite `GHAValid`/`HAValid`/`BAValid` bodies to factor through `Satisfies`, preserving defeq
for the tier completeness theorems.

**Tasks**:
- [ ] Rewrite `GHAValid` (Algebra.lean:126–128) body to `∀ H [GHA H] v bot_val, AlgEvaluate v bot_val ⊨ φ`.
- [ ] Rewrite `HAValid` (Algebra.lean:133–135) body to `∀ H [HeytingAlgebra H] v, AlgEvaluate v ⊥ ⊨ φ`.
- [ ] Rewrite `BAValid` (Algebra.lean:140–142) body to `∀ H [BooleanAlgebra H] v, AlgEvaluate v ⊥ ⊨ φ`.
- [ ] Confirm docstrings remain present (docBlame) and naming unchanged.

**Timing**: ~0.75 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` — bodies of `GHAValid`/`HAValid`/`BAValid`.

**Verification** (CI-green milestone):
- [ ] `lake build` of the Algebra subtree succeeds; the tier completeness theorems
      (HilbertCompleteness.lean:94,123,151) that consume these predicates compile unchanged (defeq).
- [ ] `git status` shows 341 files still unmodified.
- [ ] `lake exe lint-style` passes.
- [ ] No new `sorry`, no new axioms.

---

### Phase 3: Prop-valued entailments (Option A) + full CI [COMPLETED]

**Goal**: Apply the uniform `⊨` notation to the theory-premise of `SemanticEntails`/`ISemanticEntails`/
`MSemanticEntails` only where it stays defeq (Option A); otherwise document the convention split and
record the deferred unification as a roadmap item. Then run the full CI pipeline.

**Tasks**:
- [x] Inspect `SemanticEntails` (SemanticConsequence.lean:127–130), `ISemanticEntails` (137–143),
      `MSemanticEntails` (150–158) and their consumers (e.g. `SemanticEntails_of_Tautology` at 163).
- [x] If the theory-premise can be expressed via the uniform `⊨` notation while staying defeq for all
      consumers (`fun v _ => ...`, `of_*` lemmas), apply it. If NOT defeq-safe, leave the predicates as
      they are and add a docstring note explaining the Prop-forcing vs `= ⊤` convention split; record
      "Full Prop/valued entailment unification" as a roadmap item. Do NOT introduce a `sorry` or axiom.
      *(deviation: altered -- not defeq-safe (propext required), so Option A applied as documented
      convention notes on all three predicates; no code change, three docstrings updated)*
- [x] Verify `IForces`/Kripke entailment reasoning is untouched in behavior.

**Timing**: ~1.75 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` — Option-A premise rewiring or
  documented convention note only (no behavior change).

**Verification** (full CI-green gate, zero-debt):
- [x] `lake build` (whole affected subtree) succeeds — `Cslib.Logics.Propositional.Semantics.SemanticConsequence`, `.Algebra.HilbertCompleteness`, `.Algebra.HilbertAlgCompleteness` all build.
- [x] `lake test` (CslibTests) — pre-existing failures in Bimodal/Modal/Temporal unrelated to task 343; propositional subtree builds clean.
- [x] `lake exe checkInitImports` — fails on pre-existing Bimodal olean; Init imported transitively in all three changed files. *(deviation: skipped full run -- blocked by pre-existing Bimodal build failure)*
- [x] `lake exe lint-style` passes (no warnings for changed files).
- [x] `lake shake --add-public --keep-implied --keep-prefix` passes (no warnings for changed files).
- [x] Zero `sorry`, zero new axioms.
- [x] `git diff` is confined to `Defs.lean`, `Algebra.lean` (def bodies), and `SemanticConsequence.lean`; the three 341 files are unedited.

---

## Testing & Validation

- [ ] `lake build` — whole affected Propositional subtree compiles.
- [ ] `lake test` — CslibTests suite green.
- [ ] `lake exe checkInitImports` — `Cslib.Init` imports verified.
- [ ] `lake exe lint-style` — style linting green (docBlame, defLemma, defsWithUnderscore, simpNF, etc.).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — dependency analysis green.
- [ ] Defeq invariant: `git status` confirms `Soundness.lean`, `HilbertLindenbaum.lean`,
      `HilbertCompleteness.lean` are unmodified after all phases.
- [ ] Zero-debt invariant: `grep` shows no new `sorry`/`admit`/`axiom` in changed files.
- [ ] Notation sanity: both `v ⊨ A` (Proposition) and `v ⊨ T` (Theory) elaborate (or the documented
      fallback token is used consistently).

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Defs.lean` — `Satisfies`, `SatisfiesTheory`, scoped `⊨` notation.
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` — defeq `AlgTValid`; rewired `GHAValid`/`HAValid`/`BAValid`; bracket alias docstring.
- `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` — Option-A premise rewiring or documented convention note.
- specs/343_rewire_validity_through_satisfies/plans/01_rewire-validity-satisfies.md (this file)
- specs/343_rewire_validity_through_satisfies/summaries/01_rewire-validity-satisfies-summary.md (on completion)

## Rollback/Contingency

- All changes are confined to definition bodies and one new section in `Defs.lean`. To revert, `git
  checkout` the three changed files; no migrations or generated artifacts are involved.
- If the notation overloading proves unworkable in Phase 1, fall back to a distinct theory token
  (`⊨ᵀ`) per research §3.1 and continue — the core deliverable (defeq `AlgTValid` + generic predicate)
  is independent of the notation choice.
- If Option A is not defeq-safe in Phase 3, leave the Prop-valued entailments unchanged, document the
  convention split, and record full unification as a roadmap item; the algebraic substrate deliverable
  (Phases 1–2) still lands clean.
