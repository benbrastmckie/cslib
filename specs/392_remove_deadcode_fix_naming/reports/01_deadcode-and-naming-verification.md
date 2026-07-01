# Task 392 Research: Dead-Code Deletion + Naming Fixes (grep-verified)

**Session**: sess_1782924983_6bcecb_392
**Date**: 2026-07-01
**Scope**: Delete grep-verified dead decls; fix `Extention`->`Extension` typo; rename 5 underscore decls. LK/LJ `cutAdm_*`/`ljCutAdm_*` renames are OUT (task 386 owns them).
**Method**: Live repo-wide `grep` for every target. Description line numbers are STALE (files edited by tasks 389/460); this report gives CURRENT line numbers and reconciles each item.

---

## 1. Sequencing / Ownership (resolved)

| Task | Status | Impact on 392 |
|------|--------|---------------|
| **386** `fix_lake_lint_errors_propositional` | **completed** (archived) | Sequencing constraint SATISFIED. 386 already renamed the 13 `defsWithUnderscore` incl. LK/LJ `cutAdm_*`/`ljCutAdm_*`. Those are OUT of 392. All 392 renames are now safe to do. |
| **395** reconciliation | completed | Confirmed 386 owns cutAdm; 392 drops them. |
| **317** `propositional_tableau_completeness` | planned (on hold) | OWNS `Classical/Completeness.lean` + `Classical/Soundness.lean`. See §5 risk note. |
| **389 / 460** | completed | Recently edited the target files -> stale line numbers in the task description. |

Verified 386 already did LK/LJ renames: `grep cutAdm_` / `ljCutAdm_` — do NOT touch these in 392.

---

## 2. Dead Declarations — VERIFIED 0 call sites (DELETE)

All rows below were confirmed with repo-wide `grep` excluding the declaration line itself.

| # | Declaration | File | Current line | Ext. refs | Desc. line | Match |
|---|-------------|------|-------------:|----------:|-----------|-------|
| 1 | `classicalApplyOne_pos_atom` | Tableau/Classical/Soundness.lean | 73 | 0 | 73 | exact |
| 2 | `classicalApplyOne_pos_bot` | " | 77 | 0 | — | |
| 3 | `classicalApplyOne_pos_and` | " | 81 | 0 | — | |
| 4 | `classicalApplyOne_pos_or` | " | 86 | 0 | — | |
| 5 | `classicalApplyOne_pos_imp` | " | 91 | 0 | — | |
| 6 | `classicalApplyOne_pos_neg` | " | 102 | 0 | — | |
| 7 | `classicalApplyOne_neg_atom` | " | 107 | 0 | — | |
| 8 | `classicalApplyOne_neg_bot` | " | 111 | 0 | — | |
| 9 | `classicalApplyOne_neg_and` | " | 115 | 0 | — | |
| 10 | `classicalApplyOne_neg_or` | " | 120 | 0 | — | |
| 11 | `classicalApplyOne_neg_imp` | " | 125 | 0 | — | |
| 12 | `classicalApplyOne_neg_neg` | " | 136 | 0 | 136 | exact |
| 13 | `classicalBranchSatisfiable_not_closed` | Tableau/Classical/Soundness.lean | 486 | 0 | 486 | exact |
| 14 | `mem_extendMany_of_mem` | Tableau/Classical/Completeness.lean | 450 | 0 | 435 | stale (+15) |
| 15 | `hintikka_inv_mono` | Tableau/Classical/Completeness.lean | 462 | 0 | 447 | stale (+15) |
| 16 | `propImpOrNegOf?` | Tableau/Defs.lean | 81 | 0 code | 81 | exact |
| 17 | `closurePred_false_of_sat` | Tableau/Intuitionistic/Soundness.lean | 431 | 0 | 431 | exact |
| 18 | `isAccessible_go_mono_fuel` | Tableau/Intuitionistic/Soundness.lean | 505 | 0 | 505 | exact |
| 19 | `hilbertAxiomToND` | NaturalDeduction/Equivalence.lean | 305 | 0 | 305 | exact |
| 20 | `mem_insert_left` | SequentCalculus/LK/Completeness.lean | 69 | 0 | 69 | exact |
| 21 | `mem_insert_right` | SequentCalculus/LK/Completeness.lean | 73 | 0 | 73 | exact |

### Notes on specific dead decls

- **#1–12 (classicalApplyOne_* simp lemmas, lines 73–141)**: NONE are marked `@[simp]` (verified — the block header comment calls them "Helper simp lemmas" but no `@[simp]` attribute is attached). So deletion cannot change simp-set behavior elsewhere. The parent function `classicalApplyOne` is heavily used and stays. Do NOT confuse these with `classicalApplyOne_output_complexity` (Completeness.lean:631, 2 refs) and `classicalApplyOne_branching_length` (Completeness.lean:826, 1 ref) which are LIVE.
- **#16 `propImpOrNegOf?`**: 0 code call sites. The only textual hit outside the declaration is a **stale comment** at `Tableau/Intuitionistic/Rules.lean:203` ("We use `propImpOrNegOf?`..."). `intApplyRule`/`intApplyRuleFull` (Rules.lean:204/245) reference NONE of the `propXxxOf?` helpers. **Deletion must also fix/remove the stale comment at Rules.lean:203** or it becomes a dangling reference.
- **#20/#21 `mem_insert_left`/`mem_insert_right`**: Local wrappers over `Finset.mem_insert_self` / `Finset.mem_insert_of_mem`. Every proof in the file calls the `Finset.*` lemmas directly, so the wrappers are unused. Confirm the surrounding `simp`/comment block doesn't reference them by name (it does not).

---

## 3. "Intuitionistic/Rules.lean:114/203" — NO dead decls (reconciled)

The description lists `Intuitionistic/Rules.lean:114/203` as dead decls, but a full content scan shows **NO dead top-level declarations in Rules.lean** (every decl has >0 refs: `isAccessible` 90, `posFormulasAt` 18, `intApplyRule` 81, etc.). Current line 115 = `IntTableauState` (live structure), line 204 = `intApplyRule` (81 refs).

**Conclusion**: The Rules.lean dead decls the description referred to were already removed by 389/460, OR the numbers are stale. The ONLY actionable item in Rules.lean is the **stale comment at :203** referencing `propImpOrNegOf?` (handled together with dead-decl #16). **Do NOT delete any declaration in Rules.lean.** Recommend the implementer re-run a scan and, finding nothing dead, skip.

---

## 4. Renames (all in-scope; 386 complete so all safe now)

### 4a. `modus_ponens` constructor -> `modusPonens` — LARGE (97 sites / 26 files)

- Target: the **Propositional** `DerivationTree` constructor, `Cslib/Logics/Propositional/ProofSystem/Derivation.lean:77`.
- **CRITICAL disambiguation**: Bimodal / Temporal / Modal / ExtDerivation each define a SEPARATE inductive with an identically-named `modus_ponens` constructor. Explore-agent verification: **NO cross-imports** — those files must NOT be touched. Naive repo-wide sed of `modus_ponens` would corrupt them.
- **97 functional edit sites across 26 files**, all under `Cslib/Logics/Propositional/`. Full file-by-file enumeration in Appendix A.
- Patterns: `| modus_ponens`, `| .modus_ponens`, `| @modus_ponens` (GenericMCSBridge.lean:133), `.modus_ponens`, `DerivationTree.modus_ponens`, `PL.DerivationTree.modus_ponens`, unqualified `modus_ponens Γ φ ψ`.
- **Out of scope but note**: helper lemmas `height_modus_ponens_left` / `height_modus_ponens_right` (Derivation.lean:100/105) contain underscores too and will remain snake_case after this rename — a naming inconsistency the task does NOT cover. Flag to user; a follow-up may rename them.
- **Recommendation**: This rename dwarfs every other item in 392 (blast radius 26 files vs. the rest being ≤4 sites each). It MUST be its own phase with a dedicated `lake build` gate, edited per-file (not global sed). Consider whether it warrants being split into its own task.

### 4b. `lift_int_to_cl` -> `liftIntToCl`

- File (only): `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean`. Decl `:263` + uses `:270, :272, :278`. 4 sites, self-contained.
- Sibling `liftMinToCl` (MinLindenbaum) is already camelCase — this makes them consistent.

### 4c. `goodSelection_seq` -> `goodSelectionSeq`

- File (only): `Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean`. Decl `:82` + uses `:84, :89, :90, :95, :98, :100, :114, :115, :116, :118`.
- **WORD-BOUNDARY HAZARD**: a separate declaration `goodSelection_seq_prop` (`:88`, used `:118`) shares the prefix. Naive string-replace `goodSelection_seq`->`goodSelectionSeq` would corrupt it into `goodSelectionSeq_prop`. Use word-boundary matching (`\bgoodSelection_seq\b`, which does NOT match inside `goodSelection_seq_prop` because `_` is a word char) or edit each site individually. `goodSelection_seq_prop` is a separate underscore name NOT in 392 scope.

### 4d. `HasFresh.to_infinite` -> `HasFresh.toInfinite`

- File (only): `Cslib/Foundations/Data/HasFresh.lean`. Instance decl `:38` + docstring reference `:44`. No explicit external references (used via typeclass resolution, so renaming the instance name is safe). 2 sites.

### 4e. `emptyHrelation_apply` -> `emptyHRelation_apply`

- File (only): `Cslib/Foundations/Relation/Domain.lean:30`. 0 external refs.
- This is a **capitalization fix** (`Hrelation`->`HRelation`) to match the underlying def `emptyHRelation` and its sibling `emptyHRelation_emptyRelation` (:27). The trailing `_apply` is a legitimate Mathlib naming convention (application lemma) and should be KEPT. Confirm the exact expected name with `lake lint` at implementation time.

---

## 5. `Extention` -> `Extension` typo — WIDER than described (3-theorem rename, 5 call/comment sites)

The description says "(Equivalence.lean:256-257, Defs.lean:190/195)" but the typo'd names are REFERENCED elsewhere and must all be updated or the build breaks:

| Decl (typo) | -> Fixed | Decl site | Call sites | Comment sites |
|-------------|----------|-----------|-----------|---------------|
| `instIsIntuitionisticExtention` | `instIsIntuitionisticExtension` | Defs.lean:190 | Basic.lean:302, AxiomAdmissibility.lean:230 | Basic.lean:215, Equivalence.lean:256 |
| `instIsClassicalExtention` | `instIsClassicalExtension` | Defs.lean:195 | AxiomAdmissibility.lean:232 | Equivalence.lean:256 |
| `instIsMinimalExtention` | `instIsMinimalExtension` | Equivalence.lean:257 | (none) | — |

**All 3 are `theorem`s** (used as explicit instance builders). Missing the Basic.lean/AxiomAdmissibility.lean call sites would break compilation.

---

## 6. Task 317 entanglement (Classical/Completeness + Soundness)

Verification:
- `Classical/Completeness.lean` currently has **0 `sorry`** and **no working-tree diff** (`git diff --stat` empty despite the session-start status snapshot). No live 317 WIP region exists in the file.
- Dead decls #14/#15 (`mem_extendMany_of_mem`:450, `hintikka_inv_mono`:462) have **0 refs** and are not adjacent to any sorry.

**Recommendation**: Safe to delete #14/#15 now. Because these files are 317-owned, the implementer should re-grep at implementation time. Conservative fallback if 317 resumes concurrently: defer ONLY #14/#15 (and the Soundness.lean items #1–13/#17/#18), landing the non-Tableau renames/deletions independently. No sorry is touched by any 392 edit.

---

## 7. Recommended phasing (for the planner)

1. **Phase A — dead-code deletion (low risk)**: decls #1–21 minus the Rules.lean non-issue. Includes fixing the stale Rules.lean:203 comment when deleting `propImpOrNegOf?`. `lake build` the four affected modules.
2. **Phase B — small renames**: 4b (IntLindenbaum), 4c (InfiniteGraphRamsey, word-boundary care), 4d (HasFresh), 4e (Domain). Each self-contained; `lake build` each module.
3. **Phase C — `Extention` typo rename**: 3 theorems + call sites in Basic.lean/AxiomAdmissibility.lean. `lake build` Propositional.NaturalDeduction + Propositional.Defs consumers.
4. **Phase D — `modus_ponens` constructor rename (large, isolated)**: 97 sites / 26 files, per-file edits, dedicated full `lake build`. Consider splitting to its own task.

**CI**: after all phases, run `lake build`, `lake exe checkInitImports`, `lake lint` (confirm the targeted `defsWithUnderscore` entries clear), `lake exe lint-style`, `lake test`. Zero-debt: no `sorry`/axiom introduced by any edit.

---

## Appendix A — `modus_ponens` (Propositional) edit sites by file (97 total)

ProofSystem/Derivation.lean (8: L77 decl, L95, L102, L107, L137; docstring L66; helper-lemma names L100/L105 NOT renamed) · ProofSystem/Instances.lean (1: L58) · ProofSystem/IntMinInstances.lean (2: L54, L121) · ProofSystem/FragmentInstances.lean (3: L55, L102, L134) · Metalogic/Soundness.lean (1: L72) · Metalogic/IntSoundness.lean (1: L109) · Metalogic/MinSoundness.lean (1: L106) · Metalogic/StrongCompleteness.lean (18: L122,123,141,155,183,197,229,230,231,273,282,301,325,336,411,419,422,427) · Metalogic/IntStrongCompleteness.lean (7: L132,133,147,157,172,182,248) · Metalogic/MinStrongCompleteness.lean (6: L143,144,158,168,183,193) · Metalogic/IntLindenbaum.lean (6: L76,80,83,243,269,270) · Metalogic/MinLindenbaum.lean (2: L210,211) · Metalogic/GenericLindenbaum.lean (4: L195,202,205,208) · Metalogic/GenericMCSBridge.lean (2 code: L91, L133 `@modus_ponens`; comments L44/L115) · Semantics/Algebra/Soundness.lean (4: L179,212,244,276) · Semantics/Algebra/LiftViaMorphism.lean (5: L83,95,107,175; comment L75) · Semantics/Algebra/BrouwerianCompleteness.lean (1: L118) · Semantics/Algebra/BrouwerianCompletenessGeneric.lean (1: L149) · Semantics/Algebra/HilbertAlgCompleteness.lean (1: L97) · Semantics/Algebra/PointedBrouwerianCompleteness.lean (1: L114) · Semantics/Algebra/MplPointedConservative.lean (1: L104) · Semantics/Algebra/ConjImpConservative.lean (2: L67,68) · Semantics/SemanticConsequence.lean (4: L181,189,193,200) · NaturalDeduction/Equivalence.lean (4 code: L296,377,394; comment L285) · NaturalDeduction/FromHilbert.lean (5: L91,104,154,300,301) · NaturalDeduction/HilbertDerivedRules.lean (15: L108,109,156,157,173,188,205,220,248,251,252,282,291,293,295)

(Comment-only lines listed for completeness; renaming them keeps docs accurate but is not build-critical.)
