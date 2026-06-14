# Research Report: Task #189 — Eliminate Legacy Weak Completeness Files

- **Task**: 189 - Eliminate legacy weak completeness files by merging canonical model infrastructure into strong completeness files
- **Started**: 2026-06-14T00:00:00Z
- **Completed**: 2026-06-14T00:30:00Z
- **Effort**: Team research (3 teammates, standard mode)
- **Dependencies**: None
- **Sources/Inputs**:
  - `specs/189_rename_completeness_to_canonical_model/reports/01_teammate-a-findings.md` — Merge feasibility and import graph
  - `specs/189_rename_completeness_to_canonical_model/reports/01_teammate-b-findings.md` — File structure, standards, docstrings
  - `specs/189_rename_completeness_to_canonical_model/reports/01_teammate-c-findings.md` — Downstream impact and CI strategy
  - `Cslib/Logics/Propositional/Metalogic/Completeness.lean` (347 lines)
  - `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` (235 lines)
  - `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` (181 lines)
  - `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` (193 lines)
  - `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` (194 lines)
  - `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` (174 lines)
  - `Cslib.lean` barrel file (lines 341, 343, 348)
- **Artifacts**: `specs/189_rename_completeness_to_canonical_model/reports/01_team-research.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report.md

## Project Context

- **Upstream Dependencies**: `MCS.lean`, `IntLindenbaum.lean`, `MinLindenbaum.lean`, `Semantics.Basic`, `Semantics.Kripke`, `SemanticConsequence`, `Soundness.lean`, `IntSoundness.lean`, `MinSoundness.lean`
- **Downstream Dependents**: `StrongCompleteness.lean`, `IntStrongCompleteness.lean`, `MinStrongCompleteness.lean`, `Cslib.lean` barrel, `PropositionalConservativity.lean`, `Temporal/ConservativeExtension.lean`, `Modal/K/ConservativeExtension.lean`
- **Alternative Paths**: None — a 1:1 collapse with a single direct consumer per file is the cleanest possible merge topology
- **Potential Extensions**: Future per-connective helper extraction from `StrongCompleteness.lean` if classical truth lemma grows beyond ~600 lines

## Executive Summary

- The merge is structurally clean and fully feasible: each of the 3 legacy files (`Completeness.lean`, `IntCompleteness.lean`, `MinCompleteness.lean`) has exactly one direct consumer (its corresponding `Strong*` file), zero external declaration references outside those consumers, and zero name conflicts with declarations in the target files.
- Only 4 files require edits: the 3 strong completeness files (import swap + content insertion) and the `Cslib.lean` barrel file (3 import line deletions). All other files — conservative extensions, soundness files, MCS, Lindenbaum — are completely unaffected.
- Merged file sizes are acceptable at approximately 545 lines (classical), 340 lines (intuitionistic), and 335 lines (minimal), consistent with Modal K's self-contained `K/Completeness.lean` (301 lines) and within CSLib norms.
- The proposed section order (canonical model definitions, truth lemma, strong soundness, strong completeness, corollaries) is consistent across all three logics and matches the Modal K convention of self-contained per-system completeness files.
- Full-coverage docstrings for all three merged files were prepared by Teammate B, ready for direct adoption during implementation.
- A 4-phase CI verification plan (scoped builds first, then full build, then CI pipeline) ensures fast feedback and correct ordering of merge, delete, and barrel-update steps.

## Findings

### Primary Angle: Merge Feasibility and Import Graph (Teammate A)

**Consumer analysis — the critical enabler:**

| Legacy File | Direct Lean Consumers | External Declaration Uses |
|-------------|----------------------|--------------------------|
| `Completeness.lean` | `StrongCompleteness.lean` (line 10), `Cslib.lean` (line 341) | 0 — only `prop_truth_lemma` and `canonicalValuation` used inside `StrongCompleteness.lean` |
| `IntCompleteness.lean` | `IntStrongCompleteness.lean` (line 11), `Cslib.lean` (line 343) | 0 — all Int* declarations used only inside `IntStrongCompleteness.lean` |
| `MinCompleteness.lean` | `MinStrongCompleteness.lean` (line 11), `Cslib.lean` (line 348) | 0 — all Min* declarations used only inside `MinStrongCompleteness.lean` |

The `Cslib.lean` entries are barrel-file `public import` lines, not declaration-level references. Removing them does not break any consumer because the Strong* files (which stay in the barrel) already expose all declarations transitively.

**Import substitutions required after merge:**

After absorbing source content, each strong completeness file must replace its `import Completeness` line with direct imports of the legacy file's own imports:

| Target File | Import to Remove | Imports to Add |
|-------------|-----------------|----------------|
| `StrongCompleteness.lean` | `Metalogic.Completeness` | `Metalogic.MCS` (Semantics.Basic already covered transitively by SemanticConsequence) |
| `IntStrongCompleteness.lean` | `Metalogic.IntCompleteness` | `Metalogic.IntLindenbaum` (Semantics.Kripke likely covered transitively; verify) |
| `MinStrongCompleteness.lean` | `Metalogic.MinCompleteness` | `Metalogic.MinLindenbaum` (Semantics.Kripke likely covered transitively; verify) |

**Circular import risk: None.** All upstream files (MCS, Lindenbaum, Soundness) are strictly below the completeness layer and do not import any completeness file.

**Declarations to move (19 total across 3 merges):**

- `Completeness.lean -> StrongCompleteness.lean`: `canonicalValuation` (def), `prop_truth_lemma_atom/bot/and/or/imp` (5 theorems), `prop_truth_lemma` (theorem) — 7 declarations, zero name conflicts
- `IntCompleteness.lean -> IntStrongCompleteness.lean`: `IntCanonicalWorld` (def), `Preorder (IntCanonicalWorld Atom)` (instance), `intCanonicalVal` (def), `intCanonicalVal_upward_closed` (theorem), `int_truth_lemma` (theorem) — 5 declarations, zero name conflicts
- `MinCompleteness.lean -> MinStrongCompleteness.lean`: `MinCanonicalWorld` (def), `Preorder (MinCanonicalWorld Atom)` (instance), `minCanonicalVal` (def), `minCanonicalVal_upward_closed` (theorem), `minBotForces` (def), `minBotForces_upward_closed` (theorem), `min_truth_lemma` (theorem) — 7 declarations, zero name conflicts

### Alternative Angle: File Structure, Standards, and Docstrings (Teammate B)

**Canonical section order (uniform across all 3 merged files):**

1. Module header (copyright, imports, module docstring)
2. Namespace + universe declarations
3. Canonical Model / Valuation definitions
4. Truth Lemma helpers (per-connective, classical only)
5. Truth Lemma (main)
6. Strong Soundness
7. Consistency / DNE helpers
8. Strong Completeness
9. Biconditional wrapper
10. Compactness Corollary
11. Weak Completeness Corollary
12. Weak Completeness biconditional
13. End namespace

**Convention alignment:** This structure matches Modal K's `K/Completeness.lean` (301 lines), which already combines canonical model + truth lemma + completeness theorem in a single self-contained file. Propositional logics have no shared parameterized infrastructure (unlike Modal's shared base), making the current 2-file split an unnecessary indirection for each system.

**Naming conventions: all declarations pass review.** Classical uses `prop_` prefix; intuitionistic uses `int_` / `Int` (camelCase for types); minimal uses `min_` / `Min`. One optional rename exists: `canonicalValuation` (no prefix) could become `propCanonicalValuation` for consistency, but this is low-priority and should not block the merge.

**`@[expose] public section` handling:** Both legacy and strong completeness files use this pattern. The merged file keeps only the strong completeness file's single `@[expose] public section`; the legacy file's instance is dropped. Similarly for `module`, `variable`, and `universe` declarations — one copy retained.

**Edge cases identified:**
- `attribute [local instance] Classical.propDecidable` in `StrongCompleteness.lean` (line 55) but not in `Completeness.lean` — no conflict, applies to subsequent proofs only.
- `open Cslib.Logic.Helpers` in `StrongCompleteness.lean` (line 49) but not in `Completeness.lean` — no conflict, legacy content does not use Helpers.

**Prepared docstrings (ready for adoption):**

*StrongCompleteness.lean* — summary: "Proves soundness and completeness for classical propositional logic via the canonical valuation (MCS) construction. Main results: `prop_truth_lemma`, `prop_strong_completeness`, `prop_compactness`, `prop_completeness`. Reference: Chagrov-Zakharyaschev Theorem 1.16."

*IntStrongCompleteness.lean* — summary: "Proves soundness and completeness for intuitionistic propositional logic via prime DCCS canonical Kripke model. Main results: `int_truth_lemma`, `int_strong_completeness`, `int_compactness`, `int_completeness`. Key design: primeness enables disjunction backward direction; `int_prime_exclusion` for the implication case. Reference: Chagrov-Zakharyaschev Theorem 2.43."

*MinStrongCompleteness.lean* — summary: "Proves soundness and completeness for minimal propositional logic via prime MinTheory canonical Kripke model. Main results: `min_truth_lemma`, `min_strong_completeness`, `min_compactness`, `min_completeness`. Key difference from Int: `minBotForces` is a genuine predicate, not trivially `False`; `MValid` quantifies over arbitrary upward-closed `bot_forces`. Reference: Chagrov-Zakharyaschev Theorem 2.43."

Full docstring text is in `specs/189_rename_completeness_to_canonical_model/reports/01_teammate-b-findings.md`, Section 3.

### Downstream Impact and CI Strategy (Teammate C — Critic)

**Conservative extension files — zero impact confirmed:**

All three conservative extension files already import `StrongCompleteness.lean` directly and use only `prop_completeness`, which is defined in `StrongCompleteness.lean`, not in `Completeness.lean`. They require no changes.

| Conservative Extension File | Import Used | Declaration Used | Change Needed |
|----------------------------|-------------|-----------------|---------------|
| `Modal/K/ConservativeExtension.lean` | `StrongCompleteness` (line 11) | `prop_completeness` (line 50) | None |
| `Temporal/ConservativeExtension.lean` | `StrongCompleteness` (line 12) | `prop_completeness` (line 90) | None |
| `Bimodal/ConservativeExtension/PropositionalConservativity.lean` | `StrongCompleteness` (line 12) | `prop_completeness` (line 119) | None |

**Soundness files — zero impact.** No soundness file imports any completeness file. Import direction is strictly downward: `MCS/Lindenbaum -> Completeness -> StrongCompleteness`.

**CI verification plan (4 phases, correct ordering):**

Phase 1 — Merge content into strong completeness files (3 edits)
Phase 2 — Update `Cslib.lean` by running `lake exe mk_all --module` after file deletion (not before)
Phase 3 — Delete the 3 legacy files
Phase 4 — Verify in sequence:
```
lake build Cslib.Logics.Propositional.Metalogic.StrongCompleteness
lake build Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness
lake build Cslib.Logics.Propositional.Metalogic.MinStrongCompleteness
lake build Cslib.Logics.Modal.Metalogic.Systems.K.ConservativeExtension
lake build Cslib.Logics.Temporal.ConservativeExtension
lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.PropositionalConservativity
lake build
lake exe checkInitImports
lake exe lint-style
lake test
lake exe mk_all --module
```

**Key ordering constraint:** Merge before delete. If legacy files are deleted first, the strong completeness files immediately break (they still import the legacy files at that point). Barrel update (`mk_all --module`) must come after deletion, not before.

**Medium-risk item — import transitivity:** Some newly explicit imports may be redundant due to transitive closure (e.g., `Semantics.Basic` via `SemanticConsequence`). Run `lake shake` after the build passes to identify and clean up redundant imports. This is a cleanliness issue, not a correctness risk.

**Edge case — `mk_all` timing:** If `lake exe mk_all --module` is run before deleting the legacy files, it will re-add them to the barrel. The correct sequence is: merge -> delete files -> run `mk_all` -> build.

## Decisions

- **Proceed with merge as designed.** Three teammates independently confirmed feasibility. No blockers, no name conflicts, no circular dependencies, no external declaration leakage.
- **Adopt the uniform 13-section layout** from Teammate B for all three merged files.
- **Use the prepared docstrings** from Teammate B Section 3 directly in the merged files.
- **Follow the 4-phase CI plan** from Teammate C: merge first, delete second, barrel third, build+CI last.
- **Defer the optional `canonicalValuation` -> `propCanonicalValuation` rename.** It does not block the merge and carries zero external consumer risk either way.
- **Run `lake shake` after CI passes** to clean up any redundant transitive imports that become explicit during the merge.

## Recommendations

1. **Phase 1 (edit 3 files):** In `StrongCompleteness.lean`, replace `import Metalogic.Completeness` with `import Metalogic.MCS`. In `IntStrongCompleteness.lean`, replace `import Metalogic.IntCompleteness` with `import Metalogic.IntLindenbaum`. In `MinStrongCompleteness.lean`, replace `import Metalogic.MinCompleteness` with `import Metalogic.MinLindenbaum`. Insert legacy file content immediately before the first theorem that references it (after the import block, before "Strong Soundness").

2. **Verify transitive imports experimentally.** Teammate A and C both note that `Semantics.Basic` is likely transitively available via `SemanticConsequence` and `Semantics.Kripke` likely via `SemanticConsequence`. Do a quick scoped build after Phase 1 to confirm before proceeding.

3. **Phase 3 (delete 3 files):** Remove `Completeness.lean`, `IntCompleteness.lean`, `MinCompleteness.lean` from disk. Do this only after the scoped builds in Phase 4 pass.

4. **Phase 2 (update barrel):** Run `lake exe mk_all --module` after deletion. Alternatively, manually remove lines 341, 343, and 348 from `Cslib.lean`. Either approach is correct; `mk_all` is safer as it regenerates the entire barrel.

5. **Install docstrings** from Teammate B at the top of each merged file, replacing the existing module docstrings.

6. **Run `lake shake --add-public --keep-implied --keep-prefix`** after a full `lake build` passes to detect and eliminate any import redundancy introduced during the merge.

## Risks and Mitigations

| Risk | Level | Mitigation |
|------|-------|------------|
| Name conflicts in merged files | None | Verified across all 19 declarations: zero overlap |
| Circular imports after merge | None | Dependency direction is strictly one-way; verified against MCS, Lindenbaum, Soundness |
| External consumer breakage | None | All 3 conservative extension consumers use `prop_completeness` from StrongCompleteness.lean only |
| Missing transitive imports | Low | Add explicit imports during merge; verify with scoped build; use `lake shake` to clean up |
| Merged file exceeds size norms | Low | Largest merged file is ~545 lines (classical); comparable to Modal Completeness.lean at 475 lines; within CSLib norms |
| Incorrect `mk_all` timing | Low | Run `mk_all` after file deletion, not before; failure mode is obvious (barrel re-adds deleted modules) |
| Olean cache stale after deletion | Low | `lake build` handles this; `lake clean && lake build` resolves edge cases |

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Merge feasibility, import graph, declaration inventory | Completed | High |
| B | File structure, section order, naming conventions, docstrings | Completed | High |
| C | Downstream impact analysis, conservative extensions, CI ordering | Completed | High |

## Appendix

### Files to Edit (3)

- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean`
- `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean`
- `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean`

### Files to Delete (3)

- `Cslib/Logics/Propositional/Metalogic/Completeness.lean`
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean`
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean`

### Files to Update (1)

- `Cslib.lean` — remove lines 341 (`Completeness`), 343 (`IntCompleteness`), 348 (`MinCompleteness`); or regenerate via `lake exe mk_all --module`

### Files Confirmed Unaffected

- `Cslib/Logics/Modal/Metalogic/Systems/K/ConservativeExtension.lean`
- `Cslib/Logics/Temporal/ConservativeExtension.lean`
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean`
- All soundness files (`Soundness.lean`, `IntSoundness.lean`, `MinSoundness.lean`)
- All MCS and Lindenbaum files
- All Modal, Temporal, and Bimodal completeness files

### References

- Chagrov, A. and Zakharyaschev, M. (1997). *Modal Logic*. Oxford University Press.
  - Theorem 1.16: Classical propositional completeness (canonicalValuation / MCS construction)
  - Theorem 2.43: Intuitionistic and minimal completeness (prime DCCS / prime MinTheory construction)
- Teammate finding files:
  - `specs/189_rename_completeness_to_canonical_model/reports/01_teammate-a-findings.md`
  - `specs/189_rename_completeness_to_canonical_model/reports/01_teammate-b-findings.md`
  - `specs/189_rename_completeness_to_canonical_model/reports/01_teammate-c-findings.md`
