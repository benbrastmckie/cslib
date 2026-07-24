# Implementation Plan: Naming / Notation Uniformity Sweep

- **Task**: 544 - unify_validity_derivability_naming_notation
- **Status**: [COMPLETED]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_naming-notation-uniformity-sweep.md
- **Artifacts**: plans/01_naming-notation-uniformity.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This is a mechanical naming/notation uniformity sweep across the four logic families under
`Cslib/Logics/{Propositional,Modal,Temporal,Bimodal}`. It executes six independent rename/notation
items identified in the research report. Every item is a pure rename (plus one notation addition
and one deprecated alias); no definitions are added, no proofs are weakened, and zero `sorry` /
axioms are introduced. Definition of done: all six items landed, the full CI pipeline green
(`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`),
and no false-positive corruption of the guarded homographs.

### Research Integration

The plan implements the research report's six-item recommendation set verbatim, with the two open
design decisions resolved per the autonomous-run directives:

- **Item 2 (notation scoping)**: BOTH the new Temporal turnstile notation AND the existing Bimodal
  turnstile notation are made `scoped` (avoids the latent global-`⊨` conflict a future
  cross-importing file would hit).
- **Item 5 (S5 axiom)**: Option A — rename `ModalAxiom` → `S5Axiom` **in place** in
  `DerivationTree.lean` with a `@[deprecated]` alias; NO relocation to `Instances/S5.lean`
  (relocation would invert a dependency edge and force ~13 files to gain imports).

The report's three false-positive guards are honored as hard constraints (see Risks): the English
word "Valid" in `Temporal/ProofSystem/Axioms.lean:216,221`, the 174-occurrence `*negation_complete`
property family plus `propositions_complete`, and docstring/task-number mentions of `ModalAxiom`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this run (no roadmap_path / roadmap_flag provided).

## Goals & Non-Goals

**Goals**:
- Align Temporal validity vocabulary to Bimodal (lowercase `valid*`) — item 1.
- Add a `scoped` `⊨` turnstile notation to Temporal and convert Bimodal's turnstile pair to
  `scoped` — item 2.
- Rename `NIKTheorem` → `NIKDerivable` — item 4.
- Rename S5 `ModalAxiom` → `S5Axiom` in place with a deprecated alias — item 5, Option A.
- Standardize conservativity theorems on `<extending>_conservative_over_<base>` — item 6.
- Rename the genuine Algebra-layer completeness theorems `_complete` → `_completeness` — item 3.
- Keep the tree zero-debt: no `sorry`, no axioms, no weakened proofs; full CI green.

**Non-Goals**:
- Renaming the Tableau-layer `_complete` theorems (research listed them as an optional extension;
  the autonomous directive scopes item 3 to the Algebra layer only).
- Renaming the `*negation_complete` MCS property family or `propositions_complete` (item 3 exclusion).
- Renaming Propositional `Tautology` (a genuinely distinct word; out of scope for item 1).
- Relocating `S5Axiom` into `Instances/S5.lean` (item 5 Option B is explicitly not chosen).
- Touching the task-497 seam (`imp` vs `impl` constructor naming).
- Adding NOTATION.md documentation for the new turnstile (optional per report, not required).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Blind `sed` corrupts English "Valid" in `Temporal/ProofSystem/Axioms.lean:216,221` | H | M | Rename via word-boundary + identifier-position matching only; diff-review those two lines; they are prose, not the predicate |
| Blind `s/_complete/_completeness/` corrupts the 174 `*negation_complete` + `propositions_complete` names | H | M | Rename per-declaration, driven by the explicit six-theorem (C) list; never a global suffix substitution |
| Item 2 unscoped notation re-introduces a latent global `⊨` conflict | M | L | Make BOTH Temporal and Bimodal turnstile notations `scoped`; scan Bimodal use-sites for needed `open scoped` |
| Item 5 deprecated alias placed to create an import cycle | M | L | Keep both `S5Axiom` and the `ModalAxiom` alias in `DerivationTree.lean` (no relocation); no new imports introduced |
| A conservativity theorem's actual base is not CPL, so `_over_cpl` misnames it | M | L | Spot-check each theorem's stated base before assigning `_cpl`; report confirms B/S5/T sampled over CPL |
| Docstring/task-number mentions left stale while editing item 5 | L | M | Reword `ModalAxiom` docstring mentions and task-number references to durable anchors per no-task-references-in-deliverables.md |
| A rename misses a reference and breaks the build | M | M | Per-phase scoped `lake build` of the touched module before proceeding; final full-pipeline phase |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3, 4, 5, 6 | -- |
| 2 | 2 | 1 |
| 3 | 7 | 1, 2, 3, 4, 5, 6 |

Phases within the same wave can execute in parallel (they touch disjoint file trees). Phase 2
must follow Phase 1 because it references the renamed `valid` / `semanticConsequence`.

### Phase 1: Temporal validity vocabulary alignment (item 1) [COMPLETED]

**Goal**: Rename the seven capitalized Temporal validity predicates to their lowercase Bimodal-
matching forms, updating all references and docstrings, without corrupting the English word "Valid".

**Tasks**:
- [x] In `Cslib/Logics/Temporal/Semantics/Validity.lean`, rename definitions: `Valid`→`valid`,
      `ValidSerial`→`validSerial`, `ValidDense`→`validDense`, `ValidDiscrete`→`validDiscrete`,
      `SemanticConsequence`→`semanticConsequence`, `Satisfiable`→`satisfiable`,
      `FormulaSatisfiable`→`formulaSatisfiable`.
- [x] Update the module-header `## Validity Hierarchy` ASCII block and reduction-lemma docstrings
      that name the old identifiers.
- [x] Update all consumer references in `Temporal/Metalogic/DenseSoundness.lean`,
      `Temporal/Metalogic/Chronicle/ChronicleTypes.lean`, `Temporal/Tableau/Completeness.lean`,
      `Temporal/ProofSystem/Axioms.lean`, and the one qualified `Temporal.<Name>` external reference
      *(also updated `Temporal/Metalogic/DenseCompleteness.lean`, an additional consumer found
      during the sweep that the plan's file list omitted; `ChronicleTypes.lean`'s "Valid Chronicle"
      header names the unrelated `ValidChronicle` structure, not the renamed predicate, so left as
      prose)*.
- [x] CRITICAL: leave the English word "Valid" in `Temporal/ProofSystem/Axioms.lean:216,221`
      ("Valid on densely ordered frames") untouched; diff-review those lines.
- [x] Do NOT rename Propositional `Tautology`.

**Timing**: 60 min

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Semantics/Validity.lean` - predicate definitions + header block
- `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean` - references
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` - references
- `Cslib/Logics/Temporal/Tableau/Completeness.lean` - references
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` - references (preserve prose "Valid")

**Verification**:
- Scoped `lake build Cslib.Logics.Temporal` succeeds.
- `grep -nw 'Valid\|ValidSerial\|ValidDense\|ValidDiscrete\|SemanticConsequence\|Satisfiable\|FormulaSatisfiable'`
  in the Temporal tree returns only the two guarded prose occurrences.

### Phase 2: Temporal turnstile notation, scoped (item 2) [COMPLETED]

**Goal**: Add the `⊨` turnstile notation pair to Temporal as `scoped`, and convert Bimodal's
existing turnstile pair to `scoped`, fixing any use-sites that then need `open scoped`.

**Tasks**:
- [x] In `Temporal/Semantics/Validity.lean` (after the renamed `valid` / `semanticConsequence`),
      add inside `namespace Cslib.Logic.Temporal`:
      `scoped notation:50 "⊨ " φ:50 => valid φ` and
      `scoped notation:50 Γ:50 " ⊨ " φ:50 => semanticConsequence Γ φ`.
- [x] In `Bimodal/Semantics/Validity.lean:60,81`, convert the existing two turnstile notations to
      `scoped` inside `namespace Cslib.Logic.Bimodal`.
- [x] Scan Bimodal use-sites of `⊨` and add `open scoped Cslib.Logic.Bimodal` where the notation
      is now needed but no longer globally in scope *(all 4 code use-sites --
      Metalogic/Decidability.lean, Metalogic/Soundness/Soundness.lean,
      Metalogic/Decidability/Correctness.lean, FrameConditions/Validity.lean -- already had a
      bare `open Cslib.Logic.Bimodal`, which also activates scoped notation in Lean 4, so no
      `open scoped` additions were needed; all four build clean)*.

**Timing**: 45 min

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Semantics/Validity.lean` - add scoped notation pair
- `Cslib/Logics/Bimodal/Semantics/Validity.lean` - convert existing pair to scoped
- Bimodal consumer files using `⊨` - add `open scoped` as needed

**Verification**:
- Scoped `lake build Cslib.Logics.Temporal` and `lake build Cslib.Logics.Bimodal` both succeed
  (confirms no unresolved `⊨` after scoping).

### Phase 3: NIKTheorem → NIKDerivable (item 4) [COMPLETED]

**Goal**: Rename the lone `…Theorem` predicate to the `Derivable`-family name across its 15 sites.

**Tasks**:
- [x] In `Modal/Metalogic/Constructive/Labelled/Deduction.lean:316`, rename
      `def NIKTheorem` → `def NIKDerivable`.
- [x] Update all 15 references, including the docstring mentions in
      `Constructive/Labelled/Completeness.lean` and `Constructive/Labelled/Soundness.lean` (e.g.
      the `nik_TS5_consistent : ¬ NIKTheorem TS5 ⊥` certificate).

**Timing**: 30 min

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Deduction.lean` - def rename
- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Completeness.lean` - references + docstrings
- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` - references + docstrings

**Verification**:
- Scoped `lake build` of the `Constructive/Labelled` subtree succeeds.
- `grep -nw NIKTheorem Cslib/Logics/Modal` returns nothing.

### Phase 4: S5 ModalAxiom → S5Axiom in place + deprecated alias (item 5, Option A) [COMPLETED]

**Goal**: Give S5 its proper `S5Axiom` name (matching all 14 siblings) with zero import
reorganization, keeping the 57 existing sites compiling via a deprecated alias.

**Tasks**:
- [x] In `Modal/Metalogic/DerivationTree.lean:69`, rename
      `abbrev ModalAxiom := SchemaUnion s5Tags` → `abbrev S5Axiom := SchemaUnion s5Tags`.
- [x] In the same file, add `@[deprecated (since := "…")] alias ModalAxiom := S5Axiom`
      (or `abbrev ModalAxiom := S5Axiom`) so all 57 sites keep compiling; do NOT relocate.
- [x] Migrate the primary code references to `S5Axiom` where low-churn (Soundness, MCS,
      Completeness, Systems/S5/*, InterSystem/*, Bimodal ModalConservativity, ProofSystem/Instances)
      as opportunistic cleanup; the alias covers any left behind *(migration was in fact complete
      across all 15 files with standalone `ModalAxiom` references -- zero uses of the deprecated
      alias remain outside its own declaration; compound identifiers like `IKModalAxiom`/
      `CKModalAxiom`/the two `*Axiom_implies_ModalAxiom` lemma names were left untouched as
      out-of-scope distinct declarations, per word-boundary matching)*.
- [x] Reword the `ModalAxiom` docstring mentions and any task-number references (e.g. "task 523")
      in `DerivationTree.lean` / `SchemaUnion.lean` to durable anchors per
      no-task-references-in-deliverables.md.

**Timing**: 60 min

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` - rename + alias + docstring reword
- Downstream `ModalAxiom` consumers (Soundness, MCS, Completeness, Systems/S5/*, InterSystem/*,
  Bimodal ModalConservativity, ProofSystem/Instances, Instances/S5) - migrate to `S5Axiom`

**Verification**:
- Scoped `lake build Cslib.Logics.Modal` and `lake build Cslib.Logics.Bimodal` succeed.
- No import cycle (alias stays in `DerivationTree.lean`; no new imports added).

### Phase 5: Conservativity naming standardization (item 6) [COMPLETED]

**Goal**: Standardize the 18 `<sys>_conservative_extension` theorems on the more-informative
`<extending>_conservative_over_<base>` scheme, fixing the two off-pattern names.

**Tasks**:
- [x] Rename the 18 `<sys>_conservative_extension` theorems to `<sys>_conservative_over_cpl`,
      verifying each theorem's stated base is CPL (via `Tautology`/`toModal`) before assigning
      `_cpl` *(17 distinct theorem declarations found via repo-wide word-boundary grep across
      the 15 Modal Systems/*/ConservativeExtension.lean files + Bimodal + Temporal; all renamed;
      the plan's "18" count appears to be a minor overcount in the research report -- no 18th
      site exists)*.
- [x] Fix the bare outlier: `Systems/K/ConservativeExtension.lean:24`
      `modal_conservative_extension` → `k_conservative_over_cpl`.
- [x] Fix `Bimodal/…/PropositionalConservativity.lean:97` `bimodal_conservative_extension` →
      `bimodal_conservative_over_cpl`.
- [x] Fix `Temporal/ConservativeExtension.lean:61` `temporal_conservative_extension` →
      `temporal_conservative_over_cpl`.
- [x] Update each theorem's (mostly single) references; leave the `…/ConservativeExtension.lean`
      file names unchanged.
- [x] Do NOT rename the already-compliant Scheme 2 names landed by the fragment work
      (`bimodal_conservative_over_s5`, `cpl_conservative_over_imp`, etc.) *(the generic
      `conservative_over_cpl` combinator in ConservativityLift.lean, called by
      `bimodal_conservative_over_cpl`'s proof, is a distinct pre-existing declaration and was
      left untouched)*.

**Timing**: 50 min

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/**/ConservativeExtension.lean` (the ~15 `<sys>_conservative_extension` sites)
- `Cslib/Logics/Modal/Systems/K/ConservativeExtension.lean` - `modal_` → `k_conservative_over_cpl`
- `Cslib/Logics/Bimodal/**/PropositionalConservativity.lean` - `bimodal_conservative_over_cpl`
- `Cslib/Logics/Temporal/ConservativeExtension.lean` - `temporal_conservative_over_cpl`

**Verification**:
- Scoped `lake build` of the touched Modal/Bimodal/Temporal modules succeeds.
- `grep -rn '_conservative_extension' Cslib/Logics` returns nothing (all migrated).

### Phase 6: Algebra-layer completeness suffix `_complete` → `_completeness` (item 3) [COMPLETED]

**Goal**: Rename only the six genuine Algebra-layer completeness theorems, per-declaration,
without touching the excluded property homographs.

**Tasks**:
- [x] Rename per-declaration in `Propositional/Semantics/Algebra/`:
      `hilbert_alg_complete`→`hilbert_alg_completeness` (48 refs),
      `conjImp_brouwerian_complete`→`conjImp_brouwerian_completeness` (17),
      `imp_hilbert_complete`→`imp_hilbert_completeness` (10),
      `conjImpBot_pointedBrouwerian_complete`→`conjImpBot_pointedBrouwerian_completeness` (8),
      `conjImpBotMin_brouwerianBot_complete`→`conjImpBotMin_brouwerianBot_completeness` (7),
      `brouwerianBot_complete`→`brouwerianBot_completeness` (6) *(the rename touched 18 files
      total, beyond the plan's 5-file estimate, since references extend across the wider
      Algebra/ fragment-conservativity network; 3 docstring lines grew past the 100-char
      longLine limit from the longer suffix and were rewrapped)*.
- [x] CRITICAL EXCLUSIONS — do NOT touch: the `*negation_complete` family
      (`prop_/modal_/temporal_/restricted_mcs_/closure_mcs_/mcs_closure_/algebraic_mcs_negation_complete`,
      174 occurrences) or `propositions_complete` (`HML/Basic.lean:186`) or any local
      `big_complete`/`small_complete` `have`-names *(all verified untouched: negation_complete
      count still 174, propositions_complete still present in HML/Basic.lean, big_complete/
      small_complete have-names in HilbertConservativeGlivenko.lean untouched)*.
- [x] Do NOT rename the Tableau-layer `_complete` theorems (out of scope for this run).

**Timing**: 45 min

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean` - 2 theorems
- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean` - 1 theorem
- `Cslib/Logics/Propositional/Semantics/Algebra/PointedBrouwerianCompleteness.lean` - 1 theorem
- `Cslib/Logics/Propositional/Semantics/Algebra/MplPointedConservative.lean` - 1 theorem
- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompletenessGeneric.lean` - 1 theorem

**Verification**:
- Scoped `lake build Cslib.Logics.Propositional` succeeds.
- `grep -c 'negation_complete' ` count unchanged from baseline (property family untouched).
- `grep -nw 'propositions_complete'` still present (untouched).

### Phase 7: Full CI verification [COMPLETED]

**Goal**: Confirm the whole sweep is zero-debt and green across the full CI pipeline.

**Tasks**:
- [x] `lake build` (full) succeeds -- 3253 jobs, all green.
- [x] `lake test` succeeds -- 9245 jobs, all green.
- [x] `lake exe checkInitImports` succeeds -- silent/clean exit.
- [x] `lake exe lint-style` succeeds (no new `defsWithUnderscore`/`dupNamespace` from renames) --
      exit 0, no output.
- [x] `lake shake` succeeds (no import regressions; Option A introduces none) *(shake's pre-
      existing baseline findings -- ~60 files, all `import Cslib.Init` redundancy or unrelated
      Mathlib import-shape suggestions -- were cross-checked against every file this task
      touched; none reference an added/removed import, since no `import`/`public import` line
      was edited anywhere in this task -- only identifiers were renamed and two notation
      declarations were added using already-imported symbols, so the dependency graph is
      provably unchanged)*.
- [x] Confirm zero `sorry` and zero new axioms across touched files -- verified via
      `git diff --name-only` against the pre-task commit; every `sorry`/`axiom` grep hit in
      touched files is prose (docstring mentions of "sorry-free", "axiom predicate", or
      already-commented-out `-- sorry` lines), zero live `sorry` tactics or `axiom` declarations.

**Timing**: 30 min

**Depends on**: 1, 2, 3, 4, 5, 6

**Files to modify**:
- None (verification only)

**Verification**:
- All five CI commands exit 0; `grep -rn 'sorry' ` over touched files finds none.

## Testing & Validation

- [x] `lake build` green (full tree)
- [x] `lake test` green
- [x] `lake exe checkInitImports` green
- [x] `lake exe lint-style` green
- [x] `lake shake` green (pre-existing baseline findings only; no regressions from this task)
- [x] Guarded homographs intact: English "Valid" prose (Axioms.lean:216,221),
      `*negation_complete` family (174), `propositions_complete`
- [x] No `sorry`, no new axioms, no weakened proofs
- [x] Task-497 seam (`imp` vs `impl`) untouched (no files under the constructor seam were
      touched by this task's diff)

## Artifacts & Outputs

- plans/01_naming-notation-uniformity.md (this file)
- summaries/01_naming-notation-uniformity-summary.md (produced at implementation)

## Rollback/Contingency

Each phase is an independent rename confined to a disjoint file subtree and is committed only when
its scoped `lake build` passes. If a phase breaks the build and cannot be fixed forward quickly,
revert that phase's commit (renames are self-contained; no proof logic changes to untangle). The
deprecated `ModalAxiom` alias (Phase 4) means even a partial item-5 migration leaves the tree
compiling. No destructive git on uncommitted work; snapshot before any intentional rollback.
