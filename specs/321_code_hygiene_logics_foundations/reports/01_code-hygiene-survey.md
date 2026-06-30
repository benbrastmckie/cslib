# Code Hygiene Survey: Logics/ and Foundations/

**Task**: 321 — Review file size and structure throughout `Cslib/Logics/` and
`Cslib/Foundations/`; identify over-long / poorly-structured files; produce a prioritized
refactoring plan respecting reuse-first philosophy and `ORGANISATION.md`.

**Date**: 2026-06-30 · **Agent**: cslib-research-agent

## 1. Survey Method

```
find Cslib/Logics Cslib/Foundations -name '*.lean' | xargs wc -l | sort -rn
```
Supplemented by per-file structural probes: counts of `theorem/lemma`, `def/structure/
inductive/class/instance`, `section ... end` blocks, `private` declarations, and `/-! ##`
section-header positions (used as natural split-point markers); plus import fan-in counts
(`grep -rl "import Cslib.Logics.<mod>"`).

## 2. Size Distribution (the headline numbers)

| Metric | Value |
|--------|-------|
| Total `.lean` files in scope | 484 |
| Files > 400 lines | 85 |
| Files > 700 lines | 39 |
| Files > 1000 lines | 20 |
| Files using `section`/`end` at all | 58 / 484 (~12%) |
| Total lines (Logics + Foundations) | ~138,800 (Logics ~123k, Foundations ~15.8k) |

**Foundations is healthy**: largest file is 600 lines (`Semantics/LTS/Bisimulation.lean`);
only ~8 files exceed 400 and all stay under the 600-line mark. Foundations files also tend to
use `section`/`end` and `/-! ##` headers. **The size problem is almost entirely in
`Logics/`**, concentrated in the Bimodal and Temporal metalogic developments.

### Top 20 candidates (all in Logics/)

| Lines | File | priv/decl | split markers |
|------:|------|-----------|---------------|
| 3566 | `Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` | 0/79 | rich `/-! ##` (20+) |
| 3545 | `Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` | 0/13 | 7 sections |
| 3262 | `Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` | 0/10 | 8 sections |
| 2731 | `Temporal/Metalogic/Chronicle/PointInsertion.lean` | 0/79 | rich `/-! ##` |
| 1694 | `Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean` | 0/61 | — |
| 1671 | `Bimodal/Metalogic/Separation/DedekindZ/Cases.lean` | 0/39 | — |
| 1654 | `Propositional/Tableau/Intuitionistic/Soundness.lean` | 21/9 | 7 sections |
| 1638 | `Modal/Tableau/SoundnessStep.lean` | 1/5 | 4 sections |
| 1532 | `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` | 0/53 | — |
| 1450 | `Bimodal/Metalogic/Separation/Hierarchy/HierarchyInduction.lean` | 0/61 | — |
| 1435 | `Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` | 0/51 | — |
| 1401 | `LTL/Semantics/GNBA.lean` | 16/26 | 14 sections |
| 1340 | `Propositional/Tableau/Classical/Completeness.lean` | 23/6 | — |
| 1209 | `Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` | 0/30 | — |
| 1208 | `Bimodal/Metalogic/Decidability/Tableau.lean` | 0/27 | — |
| 1134 | `Propositional/ProofSystem/FragmentAxioms.lean` | 0/86 | 15 sections |
| 1104 | `Bimodal/Metalogic/Soundness/DenseValidity.lean` | 0/36 | — |
| 1103 | `Propositional/NaturalDeduction/Normalization/Termination.lean` | 43/3 | — |
| 1095 | `Bimodal/Metalogic/Decidability/CountermodelExtraction.lean` | 0/44 | — |
| 1001 | `Bimodal/Metalogic/Separation/Hierarchy/HierarchyDefs.lean` | 0/75 | — |

## 3. Structural Findings

### Finding A — Four mega-files (2700–3566 lines) dominate the debt
`PointInsertion.lean` and `CounterexampleElimination.lean`, each appearing in **both**
`Bimodal/.../BXCanonical/Chronicle/` and `Temporal/.../Chronicle/`, are the four largest files
in the entire library. Combined: ~13,100 lines (~9.5% of the surveyed total). They are the
Burgess–Xu chronicle construction for completeness.

**Encouraging risk signal**: these files are near-leaves in the import DAG.

| File | external importers |
|------|-------------------:|
| `Bimodal/.../Chronicle/PointInsertion.lean` | 2 |
| `Bimodal/.../Chronicle/CounterexampleElimination.lean` | 1 |
| `Temporal/.../Chronicle/CounterexampleElimination.lean` | 2 |

Low fan-in means a split into a barrel module + submodules touches very few downstream
imports. The real cost is *internal*: declarations within a single file freely reference each
other, so a split must respect declaration dependency order. The dense `/-! ##` headers
(`PointInsertion` has 20+) provide natural, author-intended boundaries to split along.

### Finding B — Near-total absence of abstraction barriers in metalogic files
A stark bimodal pattern in `private` usage:

- **Good hygiene** (Tableau / Normalization families): `Termination.lean` 43 private / 3
  public, `Classical/Completeness.lean` 23/6, `Intuitionistic/Soundness.lean` 21/9,
  `GNBA.lean` 16/26. These expose only their headline theorems.
- **Zero abstraction barrier** (Bimodal/Temporal Chronicle + Separation families): every one
  of the 12 largest Bimodal/Temporal files declares **0 `private`** despite carrying 30–86
  declarations each (`PointInsertion` 79, `FragmentAxioms` 86, `HierarchyDefs` 75,
  `RRelation` 61). Many of these are demonstrably internal helpers ("Helper:", "seed
  consistency", "fc Helper Lemmas" headers) yet are fully public.

This is the single largest *expose-only-what-should-be-exposed* gap in the survey. It directly
matches the task's "unnecessary public exports / missing abstraction barriers" objective and is
independent of file-splitting.

### Finding C — Probable code duplication between Bimodal and Temporal chronicles
The `Chronicle/PointInsertion`, `Chronicle/CounterexampleElimination`, and
`Chronicle/ChronicleConstruction` modules exist in *parallel* under both `Bimodal/Metalogic/
BXCanonical/` and `Temporal/Metalogic/`, with matching `/-! ##` section headers (C5/C5'
structures, "Finding Fresh Rationals", "BurgessR3Maximal helper lemmas", Lemma 2.10). Sizes
differ (3545 vs 3262; 1532 vs 1435), indicating the two copies have **diverged** rather than
sharing a common abstraction. Per cslib's reuse-first philosophy, the shared Burgess–Xu
chronicle machinery is a candidate for a common abstraction in `Foundations/` (or a shared
`Logics/.../Chronicle` base), but this is a deep, high-risk refactor requiring its own
research task — **flagged, not recommended for immediate action**.

### Finding D — `section`/`end` underused as a hygiene tool
Only ~12% of files use `section`/`end`. Several large zero-private files (`RRelation`,
`HierarchyDefs`, `ChronicleConstruction`) would benefit from `section`-scoped `variable`
declarations and `private` blocks to both shrink boilerplate and bound visibility. This is
low-value on its own but pairs naturally with Finding B work.

### Finding E — Foundations is the model; no Foundations file needs splitting
`Foundations/Semantics/LTS/Bisimulation.lean` (600, 43 thm / 18 def, 3 sections, good headers)
and `Foundations/Logic/ProofSystem.lean` (559, 64 typeclass decls, 5 sections) are large but
well-organized along clear responsibilities. No Foundations file is recommended for splitting;
they set the structural standard the Logics/ refactors should aim for.

## 4. Reuse Check (per CSLib reuse-first protocol)

- The over-long files are **proof developments**, not new abstractions — the refactor is
  *splitting/hiding*, not *defining*. No new typeclasses or definitions are recommended, so the
  reuse-first gate is satisfied by construction for Priorities P1–P3 below.
- Finding C is the one place new abstraction *could* be justified; it is deferred to a separate
  research task precisely because reuse-first demands verifying the two copies are genuinely
  unifiable before introducing a shared module.
- Zero-debt compliance: all recommended actions are mechanical/structural and introduce no
  `sorry` and no axioms.

## 5. Prioritized Refactoring Actions

Risk legend: **[SAFE]** = mechanical, low import blast-radius, build-verifiable in isolation ·
**[MED]** = needs care with internal declaration ordering · **[HIGH]** = broad ripple or design
decision, own task.

### P1 — Add abstraction barriers (highest value / lowest risk)
1. **[SAFE]** Mark internal helper lemmas `private` in the zero-private large files, starting
   with `PointInsertion.lean` (79 decls), `RRelation.lean` (61), `HierarchyDefs.lean` (75),
   `ChronicleConstruction.lean` (53), `FragmentAxioms.lean` (86). Method: for each declaration,
   check `grep -rl` fan-in across `Cslib/`; if referenced only within its own file, prepend
   `private`. Verify with `lake build`. No file moves, no import changes. Do this **before** any
   splitting — it shrinks the public surface that splits must preserve.

### P2 — Split the four mega-files along existing `/-! ##` boundaries
2. **[MED]** `Bimodal/.../Chronicle/PointInsertion.lean` (3566) — split into 3–4 submodules at
   the major `/-! ##` headers (e.g. MCS-level axiom lemmas · seed-consistency/DCS extension ·
   R3Maximal/Burgess Lemma 2.6 · Xu Lemma 2.3 / gContent⊆B), re-exported via a
   `PointInsertion.lean` barrel `import`. Only 2 external importers, both satisfied by the
   barrel. Respect declaration order between the new submodules.
3. **[MED]** `Bimodal/.../Chronicle/CounterexampleElimination.lean` (3545) — split at its 7
   sections (C5/C5' structures · fresh-rationals helper · BurgessR3Maximal helpers · Lemma 2.10
   · G-propagation · interface). 1 external importer.
4. **[MED]** `Temporal/.../Chronicle/CounterexampleElimination.lean` (3262) — split at its 8
   sections (notably the 1093-line "Recursive Walks" block 521–1614 is its own module).
5. **[MED]** `Temporal/.../Chronicle/PointInsertion.lean` (2731) — mirror of action 2.

Sequencing note: do P1 (privatization) on each file immediately before splitting it, so each
submodule's public API is already minimized.

### P3 — Split the 1000–1700 line second tier (after P2 lands)
6. **[MED]** `Bimodal/.../Chronicle/RRelation.lean` (1694), `ChronicleConstruction.lean`
   (1532), `Temporal/.../ChronicleConstruction.lean` (1435), `ChronicleToCountermodelBasic.lean`
   (1209) — same barrel-split pattern.
7. **[MED]** `Separation/DedekindZ/Cases.lean` (1671), `Separation/Hierarchy/HierarchyInduction
   .lean` (1450), `HierarchyDefs.lean` (1001) — split by case/lemma family.
8. **[SAFE]** `Propositional/Tableau/Intuitionistic/Soundness.lean` (1654) and
   `LTL/Semantics/GNBA.lean` (1401) — already well-privatized and section-delimited; splitting
   at their `/-! ##` headers is low-risk and these are good *first* splits to validate the
   barrel pattern before tackling the higher-risk Chronicle files.

### P4 — Deferred / own-task items
9. **[HIGH]** Investigate Bimodal vs Temporal Chronicle duplication (Finding C); spawn a
   dedicated research task to determine whether a shared `Foundations`/base abstraction is
   feasible. Do **not** attempt opportunistically.
10. **[SAFE]** Optionally introduce `section`/`variable`/`private` blocks (Finding D) in the
    large zero-section files as part of P1/P3 passes; cosmetic, bundle with adjacent work.

### Recommended execution order
P1 (privatize, per-file) → P3 action 8 (low-risk splits to validate barrel pattern) → P2
(mega-file splits, one file per phase, `lake build` between each) → P3 actions 6–7 → P4
deferred to a separate task.

## 6. Verification Guidance for Implementer
- After every privatization or split: `lake build` the affected module + its importers.
- Run the CSLib CI gate (`lake exe checkInitImports`, `lake exe lint-style`, `lake shake
  --add-public --keep-implied --keep-prefix`) — `shake` will confirm no import is left
  dangling after a split, and flags now-unused imports the split exposes.
- New files need module docstrings (docBlame) and must follow `ORGANISATION.md` directory
  placement (keep submodules under the same `Chronicle/`, `Separation/`, etc. directory; barrel
  keeps the original module name/path so the namespace `Cslib.Logic.Bimodal...` is unchanged).
- Zero-debt: no `sorry`, no new axioms introduced by any action above.
