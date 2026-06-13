# Implementation Summary: Task #186

- **Task**: 186 - hilbert_nd_equivalence_refactor
- **Status**: IMPLEMENTED
- **Session**: sess_1781387781_12f49d
- **Completed**: 2026-06-13

## What Was Done

### Phase 1: Removed `h_EFQ` Parameter [COMPLETED]

- Removed `h_EFQ : ∀ φ, Axioms (⊥ → φ)` from `ndToHilbert` signature
- Removed from all 10 recursive call sites within `ndToHilbert`
- Removed from `nd_to_hilbert_deriv`, `hilbert_iff_nd`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`
- Updated module docstring and `ndToHilbert` docstring to remove EFQ mention

### Phase 2: Added Context-Based Equivalence [COMPLETED]

- Added `hilbert_iff_nd_ctx` (generic, 8 params): `Deriv Axioms Γ.toList φ ↔ DerivableIn (AxiomTheory Axioms) (Γ ⊢ φ)` using `Finset.toList_toFinset` as bridge
- Added `hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl` instantiations
- Added `hilbert_iff_nd_min` closed-context corollary (previously impossible due to EFQ requirement)
- Total 8 equivalence theorems now available

### Phase 3: Documentation and References [COMPLETED]

- Rewrote Equivalence.lean module docstring with Prawitz1965 and TroelstraVanDalen1988 citations
- Documented `AxiomTheory Axioms` vs `MPL`/`IPL`/`CPL` distinction in Design section
- Added EFQ removal rationale to module docstring
- Updated Defs.lean bridge description to mention all 8 equivalence forms
- Added `Fitting1969`, `Herbrand1930`, `vanDalen2013` to references.bib
- Removed unused `list_cons_mem_finset_insert_toList` lemma

## Plan Deviations

- `hilbert_iff_nd_min` was implemented directly via `hilbert_iff_nd` (same 8 params) rather than as corollary of `hilbert_iff_nd_ctx_min` at `Γ = ∅`. This avoided the `Finset.toList_empty` name mismatch issue in this Lean version while producing an equivalent clean proof.
- Existing `hilbert_iff_nd`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl` were kept with their direct proofs (not refactored as corollaries of context versions), per the plan's "or keep current proof if cleaner" option.

## CI Verification Results

- `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence`: PASSED
- `lake exe checkInitImports`: PASSED
- `lake lint`: 837 pre-existing errors in other modules (none from our changes)
- `lake exe lint-style`: PASSED (no errors in our files)
- `lake shake --add-public --keep-implied --keep-prefix`: PASSED (no suggestions for our files)
- `lake exe mk_all --module`: "No update necessary"
- `lake test`: PASSED

## Axiom Verification

- `hilbert_iff_nd_ctx`: `{propext, Classical.choice, Quot.sound}` (standard)
- `hilbert_iff_nd_ctx_min`: `{propext, Classical.choice, Quot.sound}` (standard)
- `hilbert_iff_nd_min`: `{propext, Classical.choice, Quot.sound}` (standard)
- `hilbert_iff_nd_ctx_cl`: `{propext, Classical.choice, Quot.sound}` (standard)
- Zero sorries in modified files; no new axioms introduced

## AI Tools Used

- Claude Code (cslib-implementation-agent): Implemented all three phases of the refactor,
  verified proofs using lean-lsp MCP tools, and ran the full CSLib CI pipeline.
