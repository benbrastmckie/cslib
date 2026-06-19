# Research Report: Modal/Metalogic Citation Standardization

## Task Overview

Standardize all citations in `Cslib/Logics/Modal/Metalogic/` to use the Lean4Doc bib link format, following the pattern already established in `StrongCompleteness.lean` files.

## Available Bib Keys in `references.bib`

Two bib keys are relevant:

- **`Blackburn2001`**: Blackburn, Patrick and Rijke, Maarten de and Venema, Yde. *Modal Logic*. Cambridge University Press, 2001.
- **`ChagrovZakharyaschev1997`**: Chagrov, Alexander and Zakharyaschev, Michael. *Modal Logic*. Oxford Logic Guides 35, Oxford University Press, 1997.

## Target Format (Template from StrongCompleteness.lean)

The correct Lean4Doc bib link format is:

```
* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thm 4.28
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16
```

Files already using this format correctly: all 15 `StrongCompleteness.lean` files plus `K/ConservativeExtension.lean` (16 files total, though the ConservativeExtension uses the shorter `[Blackburn2001]` inline form).

## Citation Format Variants Found (Non-Standard)

Six distinct non-standard citation formats exist across the codebase:

| Format ID | Pattern | Example | Count |
|-----------|---------|---------|-------|
| F1 | Dash separator, no year | `Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, ...)` | ~12 |
| F2 | Comma separator, with year, quotes | `Blackburn, de Rijke, Venema, "Modal Logic" (2002), ...` | ~14 |
| F3 | Dash separator, no detail | `Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Canonical Models)` | 1 |
| F4 | Inline "Blackburn" shorthand | `(Blackburn et al. Table 4.1)` or `(Blackburn Theorem 4.28, clause 1)` | ~15 |
| F5 | Undefined "BRV" abbreviation | `(BRV Theorem 4.28 clause 2)` or `(BRV Lemma 4.21 for K)` | ~30 |
| F6 | BimodalLogic cross-repo path | `BimodalLogic/Theories/Bimodal/...` | 3 |

## Issue Categories

### Category 1: Module Docstring References Section Citations

These appear as `* Blackburn, ...` lines in `## References` sections of module docstrings.

**Target conversion**: All must become `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], <specific-ref>`.

**Files needing conversion** (30 Soundness + Completeness files):

#### Soundness.lean files (15 files)

| System | Current Citation | Target Citation |
|--------|-----------------|-----------------|
| Core Soundness.lean | `* Cslib/Logics/Modal/Basic.lean -- ...` (internal only) | Remove (internal ref, not literature) |
| K/Soundness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9` |
| K4/Soundness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |
| K5/Soundness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |
| K45/Soundness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |
| KB5/Soundness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9` |
| T/Soundness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |
| TB/Soundness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |
| S4/Soundness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |
| S5/Soundness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9` |
| D/Soundness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |
| D4/Soundness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |
| D5/Soundness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |
| D45/Soundness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |
| DB/Soundness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |
| B/Soundness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Def. 4.9, Table 4.1` |

#### Completeness.lean files (15 files)

| System | Current Citation | Target Citation |
|--------|-----------------|-----------------|
| Core Completeness.lean | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Canonical Models)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4` |
| K/Completeness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.20-4.23)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thms 4.20--4.23` |
| K4/Completeness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.27)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thms 4.22, 4.27` |
| K5/Completeness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4` |
| K45/Completeness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.27, Definition 4.30)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thms 4.22, 4.27, Def. 4.30` |
| KB5/Completeness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.23, 4.28)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thms 4.22, 4.23, 4.28` |
| T/Completeness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.28)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thms 4.22, 4.28` |
| TB/Completeness | `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.28)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thms 4.22, 4.28` |
| S4/Completeness | (no Blackburn ref in References section -- implicit) | Add `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4` |
| S5/Completeness | (no Blackburn ref in References section -- implicit) | Add `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4` |
| D/Completeness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4` |
| D4/Completeness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4` |
| D5/Completeness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4` |
| D45/Completeness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4` |
| DB/Completeness | `* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Ch. 4` |

Note: B/Completeness has no References section (it is a stub re-export file).

### Category 2: Undefined "BRV" Abbreviation in Module Docstrings

The abbreviation "BRV" (for Blackburn, de Rijke, Venema) appears in docstrings without being defined. Per the task description:
- In module docstrings: replace with spelled-out `[Blackburn2001]` references
- In inline code comments: may keep "BRV" if the module docstring defines the abbreviation

**Files with BRV in module docstrings** (must spell out or use bib key):

| File | Lines | BRV Occurrences | Context |
|------|-------|-----------------|---------|
| Completeness.lean (core) | 101 | 1 | `/--` docstring: "BRV Theorem 4.28 clause 2" |
| K/Completeness.lean | 19,26,27 | 3 | module docstring: "BRV Lemma 4.20", "BRV Lemma 4.21" |
| K45/Completeness.lean | 27 | 1 | module docstring: "BRV Lemma 4.21 for K" |
| T/Completeness.lean | 26 | 1 | module docstring: "BRV Thm 4.28 cl.1" |
| TB/Completeness.lean | 28,29 | 2 | module docstring: "BRV Thm 4.28 cl.1", "BRV Thm 4.28 cl.2" |

**Files with BRV in section headers (`/-!`) and declaration docstrings (`/--`)**:

These are technically docstrings, not inline code comments. The task says "inline code comments may keep BRV if the abbreviation is defined in the file's docstring." Since no file currently defines BRV in its module docstring, all occurrences should be replaced.

| File | Lines | Context |
|------|-------|---------|
| K/Soundness.lean | 38 | `/-! ## K Axiom Soundness (BRV Definition 4.9 for K) -/` |
| K4/Soundness.lean | 43 | `/-! ## K4 Axiom Soundness (BRV Definition 4.9 for K4) -/` |
| S4/Soundness.lean | 44 | `/-! ## S4 Axiom Soundness (BRV Definition 4.9 for S4) -/` |
| T/Soundness.lean | 39 | `/-! ## T Axiom Soundness (BRV Definition 4.9 for T) -/` |
| TB/Soundness.lean | 45 | `/-! ## TB Axiom Soundness (BRV Definition 4.9 for TB) -/` |
| K45/Soundness.lean | 45 | `/-! ## K45 Axiom Soundness (BRV Definition 4.9 for K45) -/` |
| KB5/Soundness.lean | 45 | `/-! ## KB5 Axiom Soundness (BRV Definition 4.9 for KB5) -/` |
| K/Completeness.lean | 46,111,128,130,164,166 | Multiple section headers and docstrings |
| T/Completeness.lean | 47,49,61,63 | Section headers and docstrings |
| TB/Completeness.lean | 51,53,64,77,79 | Section headers and docstrings |

**Recommended replacement**: In module docstrings, replace "BRV" with `[Blackburn2001]`. In section headers and declaration docstrings, replace "BRV" with the spelled-out "Blackburn et al." since bib link format is not supported outside of `## References` sections. Alternatively, after adding a definition "BRV := Blackburn, de Rijke, Venema [Blackburn2001]" in the module docstring, inline uses of "BRV" could be kept.

**Recommended approach**: Replace all BRV in section headers (`/-!`) with "[Blackburn2001]" and in declaration docstrings (`/--`) with "[Blackburn2001]" since these are rendered by Lean4Doc. In inline code comments (`-- comment`), BRV can remain if the module docstring defines it.

The one inline code comment with BRV:
- `K/Completeness.lean:111`: `  · -- Case: neg phi NOT in L -- K-SPECIFIC FIX (BRV Lemma 4.20)` -- this is a true inline code comment.

### Category 3: Internal File References in References Sections

The `## References` section of the core `Soundness.lean` contains `* Cslib/Logics/Modal/Basic.lean -- semantic definitions and axiom validity proofs` which is an internal codebase path, not a literature citation.

**Files with internal Cslib path references in `## References`**:

| File | Internal Reference | Action |
|------|-------------------|--------|
| Soundness.lean (core) | `* Cslib/Logics/Modal/Basic.lean -- semantic definitions and axiom validity proofs` | Remove (no literature source) |
| StrongCompleteness.lean (core) | `* Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean -- propositional template` | Remove (internal ref) |
| DeductionTheorem.lean | `* Cslib/Foundations/Logic/Metalogic/Consistency.lean` | Remove (internal ref) |
| DerivationTree.lean | `* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS API` | Remove (internal ref) |
| MCS.lean | `* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS framework` | Remove (internal ref) |
| B/Soundness.lean | `* Cslib/Logics/Modal/Basic.lean -- ...` | Remove |
| B/StrongCompleteness.lean | `* Cslib/Logics/Modal/Metalogic/Systems/B/Completeness.lean -- ...` | Remove |
| (and ~30 more system files) | Various `* Cslib/...` paths | Remove |

**Policy decision needed**: The task says "replace with bib citations where a literature source exists, otherwise remove if no literature source applies." Since these internal paths are not literature, they should all be removed from `## References` sections. They can optionally be moved to a `## See Also` section or simply deleted.

### Category 4: BimodalLogic Cross-Repo References

Three files reference the BimodalLogic project (a separate repository):

| File | Reference | Action |
|------|-----------|--------|
| DerivationTree.lean | `* BimodalLogic/Theories/Bimodal/ProofSystem/Derivation.lean -- reference pattern` | Remove (stale cross-repo path) |
| DeductionTheorem.lean | `* BimodalLogic/Theories/Bimodal/Metalogic/Core/DeductionTheorem.lean` | Remove (stale cross-repo path) |
| MCS.lean | `* BimodalLogic/Theories/Bimodal/Metalogic/Core/MCSProperties.lean -- reference pattern` | Remove (stale cross-repo path) |

These are all "reference pattern" annotations from when code was ported from the BimodalLogic project. None correspond to literature sources. They should be removed.

### Category 5: Inline "Blackburn" References in Body Text

Several Soundness and Completeness files reference "Blackburn" by short name in body text (not in `## References` sections):

| Pattern | Files | Example | Action |
|---------|-------|---------|--------|
| `(Blackburn et al. Table 4.1)` | K4, S4, TB, K45 Soundness | Body text describing frame class | Replace with `([Blackburn2001] Table 4.1)` |
| `(Blackburn Definition 4.9, Table 4.1)` | K4, S4, TB, K45 Soundness | Body text | Replace with `([Blackburn2001] Def. 4.9, Table 4.1)` |
| `(Blackburn Theorem 4.28, clause 1)` | S4, TB Soundness | Inline axiom explanation | Replace with `([Blackburn2001] Thm 4.28, cl. 1)` |
| `(Blackburn Theorem 4.27)` | K4, S4, K45 Soundness | Inline axiom explanation | Replace with `([Blackburn2001] Thm 4.27)` |
| `Blackburn, de Rijke, Venema "Modal Logic" (2002)` | K, K4, K45, KB5, T, TB Completeness | Intro paragraph | Replace with `[Blackburn2001]` |
| `Blackburn Theorem 4.28 clause 3` | D/Completeness | Section header + docstring | Replace with `[Blackburn2001] Thm 4.28, cl. 3` |
| `Blackburn Lemma 4.21` | D/Completeness | Docstring | Replace with `[Blackburn2001] Lemma 4.21` |

## File Change Summary

### Total files needing changes: 51

| Category | File Count | Change Type |
|----------|-----------|-------------|
| Soundness.lean (systems) | 15 | Convert References section + inline refs |
| Completeness.lean (systems) | 14 | Convert References section + inline refs |
| StrongCompleteness.lean (systems) | 0 | Already correct format |
| Core Soundness.lean | 1 | Remove internal ref from References |
| Core Completeness.lean | 1 | Convert inline BRV + References section |
| Core StrongCompleteness.lean | 1 | Remove internal ref from References |
| DeductionTheorem.lean | 1 | Remove BimodalLogic + internal refs |
| DerivationTree.lean | 1 | Remove BimodalLogic + internal refs |
| MCS.lean | 1 | Remove BimodalLogic + internal refs |
| K/ConservativeExtension.lean | 0 | Already correct format |
| B/Completeness.lean | 0 | Stub file, no References section |

**Net total**: ~35 files need edits (15 Soundness + 14 Completeness + 1 core Soundness + 1 core Completeness + 1 core StrongCompleteness + 3 infrastructure files).

Note: StrongCompleteness system files already use correct format but many have internal `* Cslib/...` references that should also be removed (~15 files with internal refs to remove).

### Revised total with StrongCompleteness internal refs: ~50 files

## Implementation Recommendations

### Phase 1: Mechanical References Section Conversion (~30 files)

Convert all `## References` bullet points from plain-text Blackburn/Chagrov citations to Lean4Doc bib link format. This is a mechanical search-and-replace with 6 format variants.

### Phase 2: Remove Internal and Cross-Repo References (~35 files)

Remove all `* Cslib/...` and `* BimodalLogic/...` lines from `## References` sections. If a file's `## References` section becomes empty after removal, remove the section header too.

### Phase 3: Replace BRV and Inline Blackburn References (~15 files)

Replace "BRV" in docstrings and section headers with `[Blackburn2001]`. Replace inline "Blackburn" shorthand with `[Blackburn2001]`. The one inline code comment at `K/Completeness.lean:111` can keep "BRV" if the module docstring is updated to define the abbreviation; otherwise replace it too.

### Phase 4: Verification

Run `lake build` to ensure no docstring syntax errors were introduced.

## Blockers

None. All required bib keys exist in `references.bib`. The target format is well-established in the StrongCompleteness files.
