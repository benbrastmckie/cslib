# Implementation Plan: Code Hygiene Refactor of Logics/ Chronicle Mega-Files

- **Task**: 321 - Refactor oversized/poorly-structured files in Cslib/Logics/ and Cslib/Foundations/ for code hygiene
- **Status**: [NOT STARTED]
- **Effort**: 12 hours (7 phases)
- **Dependencies**: None
- **Research Inputs**: specs/321_code_hygiene_logics_foundations/reports/01_code-hygiene-survey.md
- **Artifacts**: plans/01_code-hygiene-refactor.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; ORGANISATION.md
- **Type**: cslib

## Overview

The size debt surfaced by the research survey is concentrated almost entirely in the Bimodal
and Temporal **Chronicle** developments inside `Cslib/Logics/`. Four mega-files (2731-3566
lines) — `PointInsertion.lean` and `CounterexampleElimination.lean`, each duplicated under
`Bimodal/Metalogic/BXCanonical/Chronicle/` and `Temporal/Metalogic/Chronicle/` — dominate the
debt while carrying only 1-3 external importers each, and they declare **zero** `private`
helpers despite holding 13-79 declarations apiece. This plan executes the survey's recommended
order: privatize-first (mechanical, no import changes), validate the barrel-split pattern on a
clean well-understood file (`LTL/Semantics/GNBA.lean`), then split the four mega-files **one per
phase** with scoped `lake build` + `lake shake` between each. Every phase leaves the build green
and preserves the public API. Definition of done: the four Chronicle mega-files are each reduced
to a barrel module re-exporting smaller submodules, internal helpers are `private`, no public
import path or namespace member changes, and the full CI gate passes.

### Research Integration

Report `01_code-hygiene-survey.md` drives this plan directly:
- **Finding A** (four near-leaf mega-files, 1-3 importers) → Phases 4-7 split them one at a time.
- **Finding B** (zero abstraction barriers in Chronicle files) → Phases 1-2 privatize helpers.
- **Finding C** (probable Bimodal/Temporal Chronicle divergence) → **deferred** (see Follow-Ups).
- **Finding E** (Foundations is healthy, no file needs splitting) → Foundations is a Non-Goal.
- Survey's **recommended execution order** (P1 privatize → P3.8 validate barrel on GNBA → P2
  mega-splits one-per-phase) → Phase sequence below.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided to this planning run; no ROADMAP.md alignment performed.

## Goals & Non-Goals

**Goals**:
- Add abstraction barriers: mark demonstrably-internal helpers `private` in the four Chronicle
  mega-files, with no change to import paths or to the public namespace surface.
- Establish and document a repeatable **barrel-split pattern** (original module path becomes a
  barrel that `import`s new submodules) by first applying it to a clean file (`GNBA.lean`).
- Split each of the four Chronicle mega-files into 3-5 submodules along the author-intended
  `/-! ##` section boundaries, re-exported via the original module path.
- Keep `lake build` green after every phase and pass the full CSLib CI gate.
- Preserve the public API exactly: every name importable as
  `Cslib.Logic...Chronicle.<decl>` before the split remains importable after.

**Non-Goals**:
- No splitting of any `Cslib/Foundations/` file (survey Finding E: Foundations is the model,
  largest file 600 lines, well-structured — no action needed).
- No investigation or unification of the Bimodal-vs-Temporal Chronicle duplication (Finding C);
  deferred to a dedicated follow-up task.
- No splitting of the second-tier 1000-1700 line files (`RRelation`, `ChronicleConstruction`,
  `Separation/*`, etc.) in this plan; flagged as a follow-up after the mega-files land.
- No new definitions, typeclasses, abstractions, `sorry`, or axioms. This is split/hide only.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A `private` helper is referenced across what become separate submodules (Lean `private` is module-scoped, invisible to importers of the barrel) | H | M | During each split, co-locate a private helper in the same submodule as its sole user; if used by multiple submodules, either de-privatize it (so the barrel re-exports it) or move it to a shared `<File>/Private.lean` base submodule imported by the others. `lake build` flags "unknown identifier" immediately. |
| Internal declaration dependency order broken by a split (decls freely reference each other within one file) | H | M | Split strictly along the existing `/-! ##` boundaries which already respect authoring order; place earlier sections in earlier-imported submodules; build after each extracted submodule, not just at the end. |
| Downstream importer breaks because a public name moved | M | L | Barrel keeps the **original module path and namespace**; submodules declare into the same `Cslib.Logic...Chronicle` namespace; `lake shake` confirms no dangling/now-unused imports. Importers (1-3 per file) never change. |
| Privatizing a decl that an external file actually uses | M | L | Phase 1-2 use `grep -rl "import ...<mod>"` + identifier fan-in across `Cslib/` per decl before prepending `private`; build the file's importers. |
| `lake build` of these heavy proof modules is slow, masking iteration | L | H | Build the single affected module + its direct importers per step, not the whole library, until the phase's final verification. |
| New submodule files miss required module docstrings (docBlame) | M | M | Each new file gets a `/-! # ... -/` module docstring; run `lake exe lint-style` in the phase verification. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4, 6 | 1, 3 / 2, 3 |
| 3 | 5, 7 | 4 / 6 |

Phases within the same wave can execute in parallel (they touch disjoint directories).

---

### Phase 1: Privatize internal helpers in the Bimodal Chronicle mega-files [COMPLETED]

**Goal**: Shrink the public surface of the two Bimodal Chronicle mega-files before they are
split, with zero import changes.

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` (3566 lines, 79 decls, 0 private)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` (3545 lines, 13 decls, 0 private)

**Tasks**:
- [ ] For each `theorem`/`lemma`/`def` in the two files, check identifier fan-in across `Cslib/`
      (`grep -rn "\b<name>\b" Cslib/` excluding the defining file). The only external importers
      are: `CounterexampleElimination.lean` and `ChronicleConstruction.lean` import
      `PointInsertion`; `ChronicleConstruction.lean` imports `CounterexampleElimination`.
- [ ] Prepend `private` to every declaration referenced **only** within its own file. Leave the
      headline/interface lemmas (those referenced by the importers above) public.
- [ ] Do not move or rename anything; do not touch `import` lines.
- [ ] Record (in the commit message) the public names that remain, to seed the split phases.

**Timing**: 1.5 hours

**Depends on**: none

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.PointInsertion`
- `lake build Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.CounterexampleElimination`
- `lake build Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleConstruction` (importer)
- `lake exe lint-style` on the two files; no new `sorry`/axioms.

---

### Phase 2: Privatize internal helpers in the Temporal Chronicle mega-files [NOT STARTED]

**Goal**: Same as Phase 1 for the Temporal Chronicle pair; disjoint directory, runs in parallel.

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` (2731 lines, 79 decls, 0 private)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` (3262 lines, 10 decls, 0 private)

**Tasks**:
- [ ] Fan-in check each declaration across `Cslib/`. External importers: `Metalogic.lean` and
      `ChronicleConstruction.lean` import both; `CounterexampleElimination.lean` imports
      `PointInsertion`.
- [ ] Prepend `private` to declarations referenced only within their own file; keep
      importer-referenced lemmas public.
- [ ] No import-line, move, or rename changes.

**Timing**: 1.5 hours

**Depends on**: none

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion`
- `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.CounterexampleElimination`
- `lake build Cslib.Logics.Temporal.Metalogic` (importer barrel)
- `lake exe lint-style`; no new `sorry`/axioms.

---

### Phase 3: Validate and document the barrel-split pattern on GNBA.lean [NOT STARTED]

**Goal**: Establish the canonical barrel-split recipe on a clean, well-privatized, single-importer
file so the higher-risk Chronicle splits follow a proven template.

**Why GNBA**: `Cslib/Logics/LTL/Semantics/GNBA.lean` (1401 lines, already 16 `private`,
14+ `/-! ##` sections, exactly **one** external importer: `OmegaRegular.lean`). Low blast radius.

**Files to modify / create**:
- Create `Cslib/Logics/LTL/Semantics/GNBA/Closure.lean` — subformulas, Fischer-Ladner closure,
  closure-membership lemmas (sections at lines 65-329).
- Create `Cslib/Logics/LTL/Semantics/GNBA/Atoms.lean` — atom predicate, finiteness, canonical
  atoms from semantic valuations (sections 187-472).
- Create `Cslib/Logics/LTL/Semantics/GNBA/Construction.lean` — GNBA state/transition/initial,
  Until acceptance sets, GNBA-to-NBA conversion (sections 473-626).
- Create `Cslib/Logics/LTL/Semantics/GNBA/Correctness.lean` — canonical run transitions, counter
  step, GNBA language equality (sections 627-1399).
- Rewrite `Cslib/Logics/LTL/Semantics/GNBA.lean` as a **barrel**: keep the module docstring and
  `import` the four new submodules; no declarations remain in it.

**Tasks**:
- [ ] Move each section block into its submodule under the **same** `namespace Cslib.Logic.LTL`.
- [ ] Preserve declaration order across submodules (Closure → Atoms → Construction → Correctness)
      and have each submodule import the earlier ones it references.
- [ ] Resolve any cross-submodule `private` reference per the Risks table (co-locate, or move to
      a shared base, or de-privatize that single name).
- [ ] Add a `/-! # ... -/` module docstring to each new file.
- [ ] Confirm `OmegaRegular.lean` still compiles unchanged (its `import ...GNBA` now hits the barrel).
- [ ] Write a 6-8 line "Barrel-Split Recipe" note into the phase commit message / summary to reuse
      in Phases 4-7.

**Timing**: 1 hour

**Depends on**: none

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.GNBA`
- `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` (sole importer)
- `lake shake --add-public --keep-implied --keep-prefix` on the LTL/Semantics modules — confirms
  no dangling or now-unused imports.
- `lake exe checkInitImports`; `lake exe lint-style`.

---

### Phase 4: Split Bimodal/.../Chronicle/PointInsertion.lean [NOT STARTED]

**Goal**: Reduce the single largest file (3566 lines) to a barrel over 3-4 submodules, public API
unchanged.

**Files to modify / create** (under `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/`):
- `Seeds.lean` — helper F/G lemmas, Lemma 2.4/2.5/2.6, seriality, seed consistency, R3Maximal
  (sections at lines 101-572).
- `Burgess.lean` — Burgess Lemma 2.6, Xu Lemma 2.3, gContent/hContent ⊆ B, duality, Lemma 2.6
  interval insertion, Lemma 2.7 + helpers, list-conjunction helpers (sections 573-1508).
- `XuGuard.lean` — Xu Lemma 3.2.1 full guard strengthening (large block, lines 1509-2599).
- `Since.lean` — Lemma 2.7' Since direction, Lemma 2.4 enriched seed (with/without guard, Since)
  (sections 2600-3565).
- Rewrite `Chronicle/PointInsertion.lean` as a barrel importing the four submodules.

**Tasks**:
- [ ] Extract sections one submodule at a time, building after each extraction.
- [ ] Keep the `namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle`; chain submodule
      imports in declaration order (Seeds → Burgess → XuGuard → Since).
- [ ] Handle cross-submodule `private` references per the Risks table; keep importer-facing lemmas
      public in whichever submodule defines them (barrel re-exports them).
- [ ] Module docstring on each new file.

**Timing**: 2 hours

**Depends on**: 1, 3

**Verification**:
- `lake build` the new barrel + submodules.
- `lake build` importers: `Chronicle.CounterexampleElimination`, `Chronicle.ChronicleConstruction`.
- `lake shake --add-public --keep-implied --keep-prefix`; `lake exe checkInitImports`; `lake exe lint-style`.

---

### Phase 5: Split Bimodal/.../Chronicle/CounterexampleElimination.lean [NOT STARTED]

**Goal**: Reduce 3545 lines to a barrel over submodules; runs after Phase 4 (same directory, and
this file imports `PointInsertion`).

**Files to modify / create** (under `.../Chronicle/CounterexampleElimination/`):
- `Structures.lean` — C5/C5' counterexample structures, fresh-rationals helper (lines 66-183).
- `BurgessHelpers.lean` — BurgessR3Maximal fc helper lemmas (lines 184-355).
- `Elimination.lean` — Lemma 2.10 C5 elimination, G-propagation elimination (lines 356-547).
- `Interface.lean` — Potential counterexample interface (lines 548-3544; the bulk; if this single
  block exceeds one comfortable build, sub-split it at internal `section`/major decl boundaries).
- Rewrite `Chronicle/CounterexampleElimination.lean` as a barrel.

**Tasks**:
- [ ] Extract per section, building after each; preserve order Structures → BurgessHelpers →
      Elimination → Interface.
- [ ] The barrel's `import Cslib.Logics.Bimodal...Chronicle.PointInsertion` continues to resolve
      (Phase 4 kept that barrel path), so no importer edits.
- [ ] Resolve cross-submodule `private` references; module docstrings on new files.

**Timing**: 2 hours

**Depends on**: 4

**Verification**:
- `lake build` barrel + submodules; `lake build Chronicle.ChronicleConstruction` (importer).
- `lake shake --add-public --keep-implied --keep-prefix`; `lake exe checkInitImports`; `lake exe lint-style`.

---

### Phase 6: Split Temporal/.../Chronicle/CounterexampleElimination.lean [NOT STARTED]

**Goal**: Reduce 3262 lines to a barrel; the "Recursive Walks" block (lines 521-1613, ~1090 lines)
becomes its own submodule. Disjoint directory from Phases 4-5, so parallel with Wave 2.

**Files to modify / create** (under `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination/`):
- `Structures.lean` — C5/C5' structures, fresh-rationals, BurgessR3Maximal helpers (lines 62-291).
- `Elimination.lean` — Lemma 2.10 C5 elimination, potential-counterexample interface,
  walk-result structures (lines 292-520).
- `RecursiveWalks.lean` — the recursive walks block (lines 521-1613).
- `MainElimination.lean` — main elimination function and remainder (lines 1614-3261).
- Rewrite `Chronicle/CounterexampleElimination.lean` as a barrel.

**Tasks**:
- [ ] Extract per section, building after each; order Structures → Elimination → RecursiveWalks →
      MainElimination.
- [ ] Keep `namespace Cslib.Logic.Temporal.Metalogic.Chronicle`; the barrel keeps importing
      `Chronicle.PointInsertion` (not yet split — fine).
- [ ] Resolve cross-submodule `private` references; module docstrings on new files.

**Timing**: 2 hours

**Depends on**: 2, 3

**Verification**:
- `lake build` barrel + submodules; `lake build Chronicle.ChronicleConstruction` and
  `Cslib.Logics.Temporal.Metalogic` (importers).
- `lake shake --add-public --keep-implied --keep-prefix`; `lake exe checkInitImports`; `lake exe lint-style`.

---

### Phase 7: Split Temporal/.../Chronicle/PointInsertion.lean [NOT STARTED]

**Goal**: Reduce 2731 lines to a barrel; mirror of Phase 4. Runs after Phase 6 (same directory;
this file is imported by the Temporal CounterexampleElimination barrel from Phase 6, whose path is
preserved).

**Files to modify / create** (under `.../Temporal/Metalogic/Chronicle/PointInsertion/`):
- `Seeds.lean` — F/G helper, Lemma 2.4/2.5/2.6, MCS-level axiom helpers, seriality, DCS neg
  insert, R3Maximal/BurgessR3Maximal properties (lines 52-519).
- `Burgess.lean` — gContent ⊆ B, Xu Lemma 2.3, derivation monotonicity, BX13', F/P monotonicity,
  Xu Lemma 3.2.1, duality, Lemma 2.6 interval insertion, propositional/list/guard helpers
  (lines 520-1345).
- `Splitting.lean` — iterated BX13 structures, Lemma 2.7, Lemma 2.8 (lines 1346-2069).
- `Since.lean` — Lemma 2.4 enriched, Phase-4 Since-direction mirrors (lines 2070-2730).
- Rewrite `Chronicle/PointInsertion.lean` as a barrel.

**Tasks**:
- [ ] Extract per section, building after each; order Seeds → Burgess → Splitting → Since.
- [ ] Barrel keeps the original module path so the Phase-6 CounterexampleElimination submodules
      and `Temporal/Metalogic.lean` importer resolve unchanged.
- [ ] Resolve cross-submodule `private` references; module docstrings on new files.

**Timing**: 2 hours

**Depends on**: 6

**Verification**:
- `lake build` barrel + submodules; `lake build` importers (`Chronicle.CounterexampleElimination`,
  `Chronicle.ChronicleConstruction`, `Cslib.Logics.Temporal.Metalogic`).
- `lake shake --add-public --keep-implied --keep-prefix`; `lake exe checkInitImports`; `lake exe lint-style`.

## Testing & Validation

Run after every phase (scoped) and once fully at the end (whole-library):
- [ ] `lake build` of the affected module + its direct importers is green.
- [ ] `lake test` (CslibTests suite) passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes (including module-docstring/docBlame on every new file).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no dangling or now-unused
      imports introduced by the split.
- [ ] No new `sorry` and no new axioms anywhere (`grep -rn "sorry" <changed files>`).
- [ ] API preservation check: every name importable from each original Chronicle module path
      before the split remains importable after (spot-check the 1-3 importers per file compile
      with **no** edits to their `import` lines).

## Artifacts & Outputs

- `specs/321_code_hygiene_logics_foundations/plans/01_code-hygiene-refactor.md` (this plan)
- New submodule files under `LTL/Semantics/GNBA/` (Phase 3)
- New submodule directories `PointInsertion/` and `CounterexampleElimination/` under both
  `Bimodal/Metalogic/BXCanonical/Chronicle/` and `Temporal/Metalogic/Chronicle/` (Phases 4-7)
- Five rewritten barrel modules at the original paths (`GNBA.lean` + four Chronicle mega-files)
- `specs/321_code_hygiene_logics_foundations/summaries/01_code-hygiene-refactor-summary.md` (on completion)

## Rollback/Contingency

- Each phase is an isolated, build-green commit; revert a single phase commit to undo it without
  affecting earlier phases.
- Privatization phases (1-2) change no import paths, so reverting them is a pure text revert.
- For a split phase, if the barrel approach surfaces an intractable cross-submodule `private`
  dependency, fall back to de-privatizing the offending name (restoring the public surface) rather
  than abandoning the split; in the worst case, revert that phase's commit and leave the file
  un-split — earlier phases remain valid.

## Deferred / Follow-Ups (NOT in this plan)

- **Bimodal vs Temporal Chronicle duplication investigation** (survey Finding C): the parallel
  `PointInsertion` / `CounterexampleElimination` / `ChronicleConstruction` modules appear to have
  diverged rather than sharing an abstraction. Determining whether a shared `Foundations`/base
  module is feasible is a deep, high-risk design question — spawn a dedicated research task; do
  not attempt opportunistically here.
- **Second-tier splits** (survey P3 actions 6-7): `RRelation.lean` (1694),
  `ChronicleConstruction.lean` (1532 / 1435), `ChronicleToCountermodelBasic.lean` (1209),
  `Separation/DedekindZ/Cases.lean` (1671), `Separation/Hierarchy/HierarchyInduction.lean` (1450),
  `HierarchyDefs.lean` (1001). Apply the same privatize-then-barrel-split pattern in a follow-up
  once the four mega-files land.
- **Foundations**: no action (Finding E — already the structural model).
