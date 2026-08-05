# Statement-Equivalence Audit of the Surviving Re-Derivations

**Status**: read-only audit, no edits made. Produced after the Support-module extraction landed,
against the duplicate inventory that extraction measured by signature matching.

**Scope**: 45 re-derivation rows across four families (KNOWNWORLDS, SUBFMLS/UNIVERSE,
ACCESSIBILITY, MEASURE), each compared statement-for-statement against its claimed origin.

**Method**: per-row Read/Grep comparison of the rederivation's full signature against the origin
declaration's, classified as IDENTICAL / WEAKER / DIFFERENT / NOT_FOUND. Alpha-renaming and
notational spellings of the same proposition count as IDENTICAL; a dropped hypothesis or
conjunct counts as WEAKER; a different proposition counts as DIFFERENT.

## Totals

| Verdict | Count |
|---------|-------|
| IDENTICAL | 38 |
| WEAKER | 6 |
| DIFFERENT | 1 |
| NOT_FOUND | 0 |
| **Total rows** | **45** |

## Bottom line for a mechanical dedup pass

1. **One row is genuinely unsafe to delete mechanically**:
   `LoopChecking.lean` `hasEdge_mem_successorsOf_origin`. It is the *converse* of a different
   lemma (`hasEdge_mem_successorsOf`, still private in the same file), **not** a copy of
   `mem_successorsOf_hasEdge` from `FmpMeasure.lean`. Its own docstring confirms this. It
   belongs to a separate origin/converse chain and must not be conflated with the audited pair.

2. **Six WEAKER rows are all one family** — `modalKnownWorlds_fold_spec` and its Nodup-splinter.
   Every non-`FmpMeasure` copy dropped the `.Nodup` conjunct **and** the `hws0 : ws0.Nodup`
   hypothesis, keeping only the `∀ x, x ∈ fold... ↔ ...` half. Safe to delete and replace with an
   import **only if** no call site consumes the `.1` (Nodup) component of the original's
   conjunction — check before deleting whole-cloth.

3. **The remaining 38 rows are byte-for-byte or alpha-equivalent** and are safe to delete and
   replace with imports mechanically.

## Group KNOWNWORLDS

| origin | rederivation(s) | verdict | detail |
|--------|-----------------|---------|--------|
| `FmpMeasure.lean` `modalKnownWorlds_fold_spec` | `BDriver.lean` `_fold_spec_B`; `FiveSimplification.lean` `_fold_spec_Five`; `FrameSoundness.lean` `_fold_spec_FS`; `LoopChecking.lean` `_fold_spec_S4`; `S5Simplification.lean` `_fold_spec_S5` | **WEAKER** (×5) | Origin: `(l) (ws0) (hws0 : ws0.Nodup) : (fold...).Nodup ∧ ∀ x, x ∈ fold... ↔ ...`. Each rederivation drops `hws0` and the `.Nodup` conjunct, keeping only the iff half. One comment admits the drop explicitly. |
| same | `S5Simplification.lean` `_fold_nodup_S5` | **WEAKER** (companion) | A *separate* lemma proving only the missing Nodup half: `(l) (ws0) (hws0 : ws0.Nodup) : (fold...).Nodup`. Together with `_fold_spec_S5` it reconstructs the origin's full conjunction, but as two lemmas rather than one. Only `S5Simplification.lean` does this split-recovery; the other four files never recover the Nodup half locally — they obtain it from the separately-audited `modalKnownWorlds_nodup_S4`/`_S5`. No information is lost project-wide, only re-derived under a different name and location. |
| `FmpMeasure.lean` `mem_modalKnownWorlds` | `_B`, `_Five`, `_C`, `_FS`, `_S4`, `_S5` | IDENTICAL (×6) | `(l) (x) : x ∈ modalKnownWorlds l ↔ ∃ sf ∈ l, sf.label = x`, verbatim in all six. |
| `FmpMeasure.lean` `modalKnownWorlds_mono_append` | `_B`, `_C`, `_FS`, `_S4`, `_S5` | IDENTICAL (×5) | Origin states the conclusion as `modalKnownWorlds b ⊆ modalKnownWorlds (xs ++ b)`; all five spell it `∀ x ∈ modalKnownWorlds b, x ∈ modalKnownWorlds (xs ++ b)`. `⊆` on `List` unfolds to exactly this — notation only. |
| `FmpMeasure.lean` `modalKnownWorlds_nodup` | `_S4`, `_S5` | IDENTICAL (×2) | `(l) : (modalKnownWorlds l).Nodup` verbatim. The S4 copy is a public `lemma` rather than `private`; the statement is unchanged. |
| `FmpMeasure.lean` `modalKnownWorlds_le_modalMaxWorld` | `FiveSimplification.lean` `known_label_le_modalMaxWorld_Five` | IDENTICAL | Names diverge substantially ("known_label" vs "modalKnownWorlds") but the statement is character-for-character identical: `{b} {w} (h : w ∈ modalKnownWorlds b) : w ≤ modalMaxWorld b`. A naming choice, not a statement deviation. |
| `FmpMeasure.lean` `mintGroup_label_eq_freshWorld` | `LoopChecking.lean` `_S4` | IDENTICAL | Full multi-line signature (list of minted formulas via `boxPositivesOf`/`filterMap` over `b`) matches verbatim. |
| `FmpMeasure.lean` `modalMaxWorld_foldl_le`, `modalMaxWorld_le_of_forall_le` | `FiveSimplification.lean` `modalMaxWorld_foldl_le_of_forall_Five`, `modalMaxWorld_le_of_forall_label_le_Five` | IDENTICAL (chain) | **Citation-graph note**: both Five lemmas state in their doc comments that they mirror `S5Simplification.lean`'s `modalMaxWorld_foldl_le_of_forall_S5w` / `modalMaxWorld_le_of_forall_label_le_S5w`, **not** `FmpMeasure.lean` directly. Full chain checked: the `FmpMeasure` origin uses **explicit** binders `(l) (c M : Nat) (hc : c ≤ M) ...`; the S5w version uses **implicit** binders `{l} {M init : WorldIndex} (hinit : init ≤ M) ...`. `WorldIndex` is `abbrev WorldIndex := Nat`, so the type is reducibly identical and the binder mode is the only difference — cosmetic, though it changes call-site argument passing. The Five pair is then verbatim identical to the S5w pair. The chain `FmpMeasure → S5w → Five` is content-preserving throughout, but the direct citation runs through `S5Simplification.lean`. |

## Group SUBFMLS/UNIVERSE

All IDENTICAL, 8 rows.

- `FmpMeasure.lean` `modalSubfmls_trans` vs `S5Simplification.lean` `_S5`, `FiveSimplification.lean` `_Five` — verbatim (`{a b c} (hab : a ∈ modalSubfmls b) (hbc : b ∈ modalSubfmls c) : a ∈ modalSubfmls c`).
- `FmpMeasure.lean` `modalUniverse_mem_formula` vs `_Five`, `_S5w` — verbatim.
- `FmpMeasure.lean` `mem_modalUniverse_of` vs `_Five`, `_S5w` — verbatim. **On the "swapped to" comment**: it does *not* describe a deviation from the origin. It refers to swapping the S5 family's own now-archived `modalUniverseS5`/`modalWorldBoundS5` for the plain `modalUniverse`/`modalWorldBound` used everywhere else (those S5-specific universe lemmas are archived, superseded by the linear budget argument). Both copies end up on the plain forms, matching the origin exactly.
- `FmpMeasure.lean` `mem_boxPositivesOf` vs `S5Simplification.lean` `_S5` — verbatim.
- `FmpMeasure.lean` `modalSubfmls_self_mem` (a public `@[simp] lemma`, not in fact `private`) vs `S5Simplification.lean` `_S5` — verbatim: `(φ : Proposition Atom) : φ ∈ modalSubfmls φ`.

## Group ACCESSIBILITY

| origin | rederivation(s) | verdict | detail |
|--------|-----------------|---------|--------|
| `Soundness.lean` `hasEdge_addEdge_cases` | `BDriver.lean` `_B`; `FrameCompleteness.lean` `hasEdge_addEdge_cases_Five`; `FrameCompleteness.lean` `_C`; `FrameSoundness.lean` `_anc`; `FrameSoundness.lean` `_FS`; `LoopChecking.lean` `_S4`; `FmpMeasure.lean` `_local` | IDENTICAL (×7) | All match `{acc} {w w' a a'} (h : (acc.addEdge w w').hasEdge a a' = true) : (a = w ∧ a' = w') ∨ acc.hasEdge a a' = true`. `_anc` alpha-renames `a a'` → `u u'`. Naming oddity worth noting: `hasEdge_addEdge_cases_Five` lives in `FrameCompleteness.lean`, not `FiveSimplification.lean`. `FmpMeasure.lean`'s `_local` is itself a re-derivation per its own docstring, and is also identical. |
| `FmpMeasure.lean` `mem_successorsOf_hasEdge` | `LoopChecking.lean` `_S4`; `S5Simplification.lean` `_S5` | IDENTICAL (×2) | Both match `{acc} {w w'} (h : w' ∈ acc.successorsOf w) : acc.hasEdge w w' = true` verbatim. |
| — | `LoopChecking.lean` `hasEdge_mem_successorsOf_origin` | **DIFFERENT** | The **converse**: `{acc} {w w'} (hr : acc.hasEdge w w' = true) : w' ∈ acc.successorsOf w`. Its docstring states it mirrors a *different, later, still-private* lemma in the same file (`hasEdge_mem_successorsOf`), not `mem_successorsOf_hasEdge`. Separate origin/converse chain — **do not conflate with the audited pair**. |
| `Soundness.lean` `accFreshInv_append` | `LoopChecking.lean` `_S4` | IDENTICAL | `{b} {acc} (hInv : accFreshInv b acc) (xs) : accFreshInv (xs ++ b) acc` verbatim. |
| `FmpMeasure.lean` `outDeg_addEdge_self` | `LoopChecking.lean` `outDeg_addEdge_self_S4` | IDENTICAL | `(acc) (w wf) : outDeg (acc.addEdge w wf) w = outDeg acc w + 1` verbatim. |
| `FmpMeasure.lean` `outDeg_addEdge_ne` | `LoopChecking.lean` `outDeg_addEdge_ne_S4` | IDENTICAL | `(acc) (w wf w') (h : w' ≠ w) : outDeg (acc.addEdge w wf) w' = outDeg acc w'` verbatim. |

## Group MEASURE

All IDENTICAL, 3 rows — `FmpMeasure.lean` `modalExpMeasure_split` / `_append` / `_const_exp` vs
`LoopChecking.lean`'s `_S4`-suffixed copies. All three signatures verbatim identical, and the
`LoopChecking` docstrings cite `FmpMeasure.lean` as the source, confirming direction of
derivation.

Two structural notes:

- This group belongs to a different subsystem (the Strict-Decrease Engine's measure-additivity
  lemmas) than the known-worlds/subformula bookkeeping the other groups cover, but follows the
  same private-and-out-of-territory re-derivation pattern.
- `modalExpMeasure_const_exp_S4`'s own docstring flags that it was **not** in the original
  enumeration of helpers needing re-derivation (only `_split` and `_append` were listed). It was
  added because the generic engine also depends on it. Not a statement deviation — recorded as a
  provenance gap in the inventory.

## Relationship to this task's roadmap items

This audit directly serves the first roadmap item recorded on completion of the Support-module
extraction ("adjudicate the public-origin duplicate families left unresolved"). It supplies the
per-row verdicts that item presupposes, and narrows the mechanically-unsafe set to exactly one
row plus one family requiring a call-site check.

It does **not** address the second roadmap item (the confirmed-unreachable, privacy-caused
families that de-privatization alone cannot resolve). Those are an import-reachability problem,
not a statement-equivalence problem, and no verdict here bears on them.
