# Implementation Plan: Task #186

- **Task**: 186 - hilbert_nd_equivalence_refactor
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: Task 185 (propositional foundations quality audit)
- **Research Inputs**: specs/186_hilbert_nd_equivalence_refactor/reports/01_team-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Refactor the Hilbert/natural deduction extensional equivalence in
`Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` to eliminate the unused `h_EFQ`
parameter, lift the equivalence from closed to context-based form, add the minimal logic
corollary, and bring documentation and literature citations up to standard. Research confirmed
unanimously (4 teammates, HIGH confidence) that `h_EFQ` is provably unused across all 10 match
arms of `ndToHilbert`, so removal is a pure deletion. The context-based equivalence composes
existing `hilbert_to_nd_deriv` and `nd_to_hilbert_deriv` with `Finset.toList_toFinset` as the
bridge.

### Research Integration

Key findings integrated from team research report (01_team-research.md):

1. `h_EFQ` is never consumed in `ndToHilbert` -- all 10 match arms verified (Section 1).
2. Context-based equivalence is a one-liner using `Finset.toList_toFinset` (Section 2).
3. MinPropAxiom has exactly the 8 witnesses needed after EFQ removal (Section 3).
4. `AxiomTheory MinPropAxiom` vs `MPL` distinction must be documented (Section 4).
5. No downstream consumers of `hilbert_iff_nd` outside NaturalDeduction/ (Section 7).
6. Missing BibTeX entries: vanDalen2013, Herbrand1930, Fitting1969 (Section 6).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly addressed by this task.

## Goals & Non-Goals

**Goals**:
- Remove unused `h_EFQ` parameter from `ndToHilbert` and all downstream signatures
- Add context-based equivalence `hilbert_iff_nd_ctx` as the primary generic theorem
- Add minimal logic corollary `hilbert_iff_nd_ctx_min` (previously blocked by EFQ requirement)
- Refactor closed-context theorems (`hilbert_iff_nd`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`) as corollaries of context-based versions at `Gamma = empty`
- Add literature citations (Prawitz 1965, Troelstra & van Dalen 1988) to module docstring
- Add vanDalen2013, Herbrand1930, Fitting1969 to references.bib
- Document the `AxiomTheory Axioms` vs `MPL`/`IPL`/`CPL` distinction

**Non-Goals**:
- Proving the deeper result `Derivable MinPropAxiom phi <-> DerivableIn MPL (empty turnstile phi)` (out of scope, separate theorem)
- Structure bundling of axiom witnesses (deferred ergonomic improvement)
- Making `ndToHilbert` computable (requires deep refactor of deductionTheorem)
- Touching DeductionTheorem.lean citations (separate task)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `Finset.toList_toFinset` not available in current Mathlib | H | L | Research confirmed it is standard Mathlib; verify with `lean_loogle` during Phase 2; fallback: prove it locally |
| Removing `h_EFQ` breaks a missed consumer | H | L | Grep confirmed zero downstream consumers; `lake build` after Phase 1 catches any |
| `List.toFinset_nil` or `Finset.toList_toFinset` name mismatch | M | L | Check exact name with `lean_local_search` or `lean_hover_info` before writing proofs |
| `hilbert_iff_nd` forward direction needs different bridge at `Gamma = empty` | M | L | Current proof already uses `List.toFinset_nil`; context version uses `Finset.toList_toFinset` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Remove `h_EFQ` Parameter [NOT STARTED]

**Goal**: Delete the unused `h_EFQ` parameter from `ndToHilbert`, `nd_to_hilbert_deriv`, and `hilbert_iff_nd`, along with all recursive call sites. Verify the build passes with no proof changes.

**Tasks**:
- [ ] Remove `h_EFQ` parameter declaration from `ndToHilbert` signature (line 162)
- [ ] Remove `h_EFQ` from all 10 recursive calls within `ndToHilbert` match arms (lines 178-215) -- each call currently passes `h_EFQ` as the 3rd positional argument
- [ ] Remove `h_EFQ` from `nd_to_hilbert_deriv` signature (line 224) and its call to `ndToHilbert` (line 236)
- [ ] Remove `h_EFQ` from `hilbert_iff_nd` signature (line 250) and its call to `nd_to_hilbert_deriv` (line 267)
- [ ] Remove `h_EFQ` from `hilbert_iff_nd_int` instantiation (line 281: `(fun phi => .efq phi)`)
- [ ] Remove `h_EFQ` from `hilbert_iff_nd_cl` instantiation (line 298: `(fun phi => .efq phi)`)
- [ ] Update the module-level docstring to remove "EFQ" from the parameter description (line 20: "K, S, and EFQ" -> "K and S")
- [ ] Update the `ndToHilbert` docstring to remove "EFQ" mention (line 145: "Requires explicit K, S, and EFQ")
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` to verify

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` -- remove `h_EFQ` parameter from 4 definitions/theorems and all recursive call sites; update 2 docstrings

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` passes with zero errors
- `grep -n "h_EFQ" Equivalence.lean` returns no matches
- All 3 existing corollaries (`hilbert_iff_nd`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`) still type-check

---

### Phase 2: Add Context-Based Equivalence and Corollaries [NOT STARTED]

**Goal**: Add the context-based generic equivalence theorem `hilbert_iff_nd_ctx` using `Finset.toList_toFinset` as the bridge, then add all 4 corollary instantiations (min/int/cl context-based, plus refactored closed-context versions).

**Tasks**:
- [ ] Add `hilbert_iff_nd_ctx` theorem: generic context-based equivalence with 8 axiom parameters (K, S, andI, andE1, andE2, orI1, orI2, orE), statement `Deriv Axioms Gamma.toList phi <-> DerivableIn (AxiomTheory Axioms) (Gamma turnstile phi)` for `Gamma : Ctx Atom`
  - Forward: apply `hilbert_to_nd_deriv`, rewrite with `Finset.toList_toFinset`
  - Backward: apply `nd_to_hilbert_deriv` directly
- [ ] Add `hilbert_iff_nd_ctx_min` corollary: instantiate `hilbert_iff_nd_ctx` with `MinPropAxiom` witnesses (implyK, implyS, andI, andE1, andE2, orI1, orI2, orE)
- [ ] Add `hilbert_iff_nd_ctx_int` corollary: instantiate with `IntPropAxiom` witnesses
- [ ] Add `hilbert_iff_nd_ctx_cl` corollary: instantiate with `PropositionalAxiom` witnesses
- [ ] Refactor `hilbert_iff_nd` to derive from `hilbert_iff_nd_ctx` at `Gamma = empty` (using `Finset.empty_toList` and `Derivable`/`Deriv [] phi` equivalence), or keep current proof if cleaner
- [ ] Refactor `hilbert_iff_nd_int` and `hilbert_iff_nd_cl` to instantiate via corresponding `_ctx` versions at `Gamma = empty`
- [ ] Add `hilbert_iff_nd_min` closed-context corollary (at `Gamma = empty`) from `hilbert_iff_nd_ctx_min`
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` to verify

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` -- add ~40 lines: 1 generic context theorem, 4 context corollaries, 1 new closed corollary (`_min`), refactor 3 existing closed corollaries

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` passes
- All 8 theorems type-check: `hilbert_iff_nd_ctx`, `hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl`, `hilbert_iff_nd`, `hilbert_iff_nd_min`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`
- `lean_verify` on key theorems shows no sorry or axiom leakage

---

### Phase 3: Documentation and Literature References [NOT STARTED]

**Goal**: Update module docstring with literature citations, document the AxiomTheory design distinction, update Defs.lean bridge mention, and add missing BibTeX entries.

**Tasks**:
- [ ] Rewrite `Equivalence.lean` module docstring:
  - Add external literature references: Prawitz 1965 Ch. I Section 1.2 (primary), Troelstra & van Dalen 1988 Section 10.4 (intuitionistic case)
  - Update "Main Definitions" to list context-based theorems as primary, closed-context as corollaries
  - Add "Design" subsection documenting `AxiomTheory Axioms` vs `MPL`/`IPL`/`CPL` distinction: the equivalence bridges two parameterized systems sharing the same axiom predicate, not a statement about pure logic strength
  - Note context-based version follows from deduction theorem (standard consequence, not novel)
  - Remove outdated "EFQ" references from design description
- [ ] Update `Defs.lean` module docstring to mention context-based equivalence is available in `NaturalDeduction/Equivalence.lean` (one-line addition to existing bridge description, if any reference exists)
- [ ] Add `vanDalen2013` entry to `references.bib`:
  ```
  @book{vanDalen2013,
    author = {van Dalen, Dirk},
    title = {Logic and Structure},
    edition = {5th},
    publisher = {Springer},
    year = {2013},
    doi = {10.1007/978-1-4471-4558-5}
  }
  ```
- [ ] Add `Herbrand1930` entry to `references.bib`:
  ```
  @phdthesis{Herbrand1930,
    author = {Herbrand, Jacques},
    title = {Recherches sur la th\'{e}orie de la d\'{e}monstration},
    school = {Universit\'{e} de Paris},
    year = {1930}
  }
  ```
- [ ] Add `Fitting1969` entry to `references.bib`:
  ```
  @book{Fitting1969,
    author = {Fitting, Melvin},
    title = {Intuitionistic Logic, Model Theory and Forcing},
    publisher = {North-Holland},
    year = {1969}
  }
  ```
- [ ] Check if `list_cons_mem_finset_insert_toList` bridge lemma is still used after Phase 2 refactoring; remove if orphaned
- [ ] Run full CI: `lake build` then `lake exe checkInitImports` then `lake exe lint-style`

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` -- rewrite module docstring (~30 lines), possibly remove unused bridge lemma
- `Cslib/Logics/Propositional/Defs.lean` -- one-line docstring update
- `references.bib` -- add 3 BibTeX entries (~25 lines)

**Verification**:
- `lake build` passes (full project)
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- Module docstring contains citations to Prawitz1965 and TroelstraVanDalen1988
- `references.bib` contains vanDalen2013, Herbrand1930, Fitting1969
- No unused lemmas remain in Equivalence.lean

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` passes after each phase
- [ ] `lake build` (full project) passes after Phase 3
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `grep -n "h_EFQ" Equivalence.lean` returns zero matches
- [ ] All 8 equivalence theorems type-check without sorry
- [ ] `lean_verify` confirms no axiom leakage on `hilbert_iff_nd_ctx_min`
- [ ] `references.bib` validates (no duplicate keys, proper BibTeX syntax)

## Artifacts & Outputs

- `specs/186_hilbert_nd_equivalence_refactor/plans/01_implementation-plan.md` (this plan)
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (refactored)
- `Cslib/Logics/Propositional/Defs.lean` (minor docstring update)
- `references.bib` (3 new entries)
- `specs/186_hilbert_nd_equivalence_refactor/summaries/01_implementation-summary.md` (on completion)

## Rollback/Contingency

All changes are in 3 files. If implementation fails:
- `git checkout -- Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` restores the original
- `git checkout -- Cslib/Logics/Propositional/Defs.lean` restores original
- `git checkout -- references.bib` restores original
- No new files are created (aside from plan/summary artifacts)
- Phase 1 is independently valuable: if Phase 2 fails, the EFQ removal still stands as an improvement
