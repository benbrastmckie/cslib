# Research Report: Stale Module Docstrings in Modal/Metalogic

**Task**: 238 — Fix stale module docstrings in Modal/Metalogic after task 237 theorem migration  
**Session**: sess_1750300800_multi_238

## Summary

After task 237 migrated weak completeness theorems from individual Completeness.lean files
into StrongCompleteness.lean (as corollaries of strong completeness), several module
docstrings became stale. This report documents the current state of all 9 affected files
and specifies the exact changes needed.

## Affected Files

### File Group 1: Core Completeness.lean

**File**: `Cslib/Logics/Modal/Metalogic/Completeness.lean`

**Current docstring** (lines 12-37):
```
/-! # Completeness Theorem for Normal Modal Logics

This module proves completeness via the canonical Kripke model
construction, parameterized over an axiom predicate `Axioms`. The
parameterized infrastructure supports all normal modal logics; an
S5-specific wrapper instantiates at `ModalAxiom`.

## Main Results

- `CanonicalWorld Axioms`: The type of worlds in the canonical model (MCS).
- `CanonicalModel Axioms`: The canonical Kripke model.
- `canonical_refl`, `canonical_trans`, `canonical_eucl`: Frame properties.
- `truth_lemma`: `Satisfies (CanonicalModel Axioms) S phi <-> phi in S.val`.
- `completeness`: If `phi` is valid over all S5 frames, then `phi` is S5-derivable.

## Design
...
-/
```

**Issues**:
1. The Main Results section lists `completeness` as a theorem in this file, but task 237
   moved system-specific completeness theorems to individual StrongCompleteness.lean files.
   There is no `completeness` theorem in this file.
2. The description says "an S5-specific wrapper instantiates at `ModalAxiom`" — this S5
   wrapper no longer exists in this file.
3. The title "Completeness Theorem for Normal Modal Logics" overstates what the file provides;
   it provides completeness *infrastructure* (canonical model, frame properties, truth lemma,
   consistency lemma), not completeness theorems themselves.
4. Main Results also references `canonical_eucl` but the file actually has two variants:
   `canonical_eucl` (from B+T+4) and `canonical_eucl_from_5` (from axiom 5 alone).

**What the file actually contains**:
- `CanonicalWorld Axioms` — type of canonical worlds
- `CanonicalModel Axioms` — canonical Kripke model definition
- `canonical_refl` — reflexivity from axiom T
- `canonical_trans` — transitivity from axiom 4
- `canonical_symm` — symmetry from axiom B
- `canonical_eucl` — Euclideanness from B+T+4
- `canonical_eucl_from_5` — Euclideanness from axiom 5 alone
- `truth_lemma` — truth lemma for logics with axiom T
- `neg_consistent_of_not_derivable` — consistency of negation (used by all completeness proofs)

### File Group 2: 8 Empty-Body Completeness.lean Files

These files have empty Lean bodies (only namespace/universe declarations) and exist purely
for import chain stability. Their docstrings are stale because they still describe proof
work that was either never in these files or was moved to StrongCompleteness.lean.

#### 2a. K4/Completeness.lean
**Current title**: "Completeness Theorem for K4 Modal Logic"  
**Current description**: "This module proves completeness for K4 modal logic..."  
**Problem**: Says "proves completeness" but has no proofs. Also contains a contradictory
hybrid: both describes the proof approach in detail AND says "provides import infrastructure."

#### 2b. K5/Completeness.lean
**Current title**: "Completeness Theorem for Modal Logic K5"  
**Current description**: "This module proves completeness for modal logic K5..."  
**Problem**: Says "proves completeness" AND "provides import infrastructure" — contradictory
hybrid docstring. Task description specifically calls out K5 as having this contradiction.

#### 2c. K45/Completeness.lean
**Current title**: "Completeness Theorem for K45 Modal Logic"  
**Current description**: "This module proves completeness for K45 modal logic..."  
**Problem**: Says "proves completeness" but file has no proofs.

#### 2d. KB5/Completeness.lean
**Current title**: "Completeness Theorem for KB5 Modal Logic"  
**Current description**: "This module proves completeness for KB5 modal logic..."  
**Problem**: Says "proves completeness" but file has no proofs.

#### 2e. D4/Completeness.lean
**Current title**: "Completeness Theorem for Modal Logic D4 (KD4)"  
**Current description**: "This module proves completeness for modal logic D4..."  
**Problem**: Says "proves completeness" but file has no proofs.

#### 2f. D5/Completeness.lean
**Current title**: "Completeness Theorem for Modal Logic D5 (KD5)"  
**Current description**: "This module proves completeness for modal logic D5..."  
**Problem**: Says "proves completeness" but file has no proofs.

#### 2g. D45/Completeness.lean
**Current title**: "Completeness Theorem for Modal Logic D45 (KD45)"  
**Current description**: "This module proves completeness for modal logic D45..."  
**Problem**: Says "proves completeness" but file has no proofs.

#### 2h. DB/Completeness.lean
**Current title**: "Completeness Theorem for Modal Logic DB (KDB)"  
**Current description**: "This module proves completeness for modal logic DB..."  
**Problem**: Says "proves completeness" but file has no proofs.

## Target Pattern: B/S4/S5

The B, S4, and S5 Completeness.lean files already have the correct infrastructure docstring
pattern. All three share the same structure:

**B/Completeness.lean** (lines 13-22):
```
/-! # B Completeness Infrastructure

This module provides import infrastructure for modal logic B.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `b_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.B.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

**S4/Completeness.lean** (lines 13-21):
```
/-! # S4 Completeness Infrastructure

This module provides import infrastructure for modal logic S4.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `s4_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.S4.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

**S5/Completeness.lean** (lines 13-21): identical structure to S4, with `s5` substituted.

### Template for Empty-Body Files

```
/-! # {SYSTEM} Completeness Infrastructure

This module provides import infrastructure for modal logic {SYSTEM}.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `{system}_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.{SYSTEM}.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

## Files NOT Needing Changes

The following files are already correct and should NOT be modified:

| File | Reason |
|------|--------|
| B/Completeness.lean | Already has infrastructure docstring (target pattern) |
| S4/Completeness.lean | Already has infrastructure docstring (target pattern) |
| S5/Completeness.lean | Already has infrastructure docstring (target pattern) |
| K/Completeness.lean | Contains actual proofs (k_truth_lemma, etc.); docstring is accurate |
| D/Completeness.lean | Contains actual proofs (truth_lemma_d, etc.); docstring is accurate |
| T/Completeness.lean | Contains actual proofs (t_truth_lemma, etc.); docstring is accurate |
| TB/Completeness.lean | Contains actual proofs (tb_truth_lemma, etc.); docstring is accurate |

## Exact Changes Required

### Change 1: Core Completeness.lean

Replace the module docstring (lines 12-37) with an updated version that:

1. Changes title from "Completeness Theorem for Normal Modal Logics" to
   "Canonical Model Infrastructure for Normal Modal Logics"
2. Removes the `completeness` theorem from Main Results
3. Adds `canonical_symm`, `canonical_eucl_from_5`, and `neg_consistent_of_not_derivable`
   to Main Results
4. Updates description to clarify this file provides shared infrastructure used by all
   15 system-specific completeness proofs
5. Removes "an S5-specific wrapper instantiates at `ModalAxiom`" phrasing

Proposed replacement:
```
/-! # Canonical Model Infrastructure for Normal Modal Logics

This module provides the shared canonical model infrastructure for proving
completeness of normal modal logics. The parameterized definitions and
lemmas here are instantiated by each system-specific `StrongCompleteness.lean`
module.

## Main Results

- `CanonicalWorld Axioms`: The type of worlds in the canonical model (MCS).
- `CanonicalModel Axioms`: The canonical Kripke model.
- `canonical_refl`: Reflexivity of canonical frame (from axiom T).
- `canonical_trans`: Transitivity of canonical frame (from axiom 4).
- `canonical_symm`: Symmetry of canonical frame (from axiom B).
- `canonical_eucl`: Euclideanness of canonical frame (from axioms B, T, 4).
- `canonical_eucl_from_5`: Euclideanness of canonical frame (from axiom 5 alone).
- `truth_lemma`: Truth lemma for logics containing axiom T.
- `neg_consistent_of_not_derivable`: Consistency of negation for completeness proofs.

## Design

The parameterized canonical model and truth lemma take explicit axiom hypotheses
for the propositional axioms (implyK, implyS, efq, peirce) and modal axioms
(K, T, 4, B, 5) as needed. System-specific completeness theorems instantiate
these in their respective `StrongCompleteness.lean` modules.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Canonical Models)
-/
```

### Change 2: K4/Completeness.lean (lines 13-41)

Replace stale docstring with infrastructure pattern:
```
/-! # K4 Completeness Infrastructure

This module provides import infrastructure for modal logic K4.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `k4_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.K4.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

### Change 3: K5/Completeness.lean (lines 13-36)

Replace contradictory hybrid docstring with infrastructure pattern:
```
/-! # K5 Completeness Infrastructure

This module provides import infrastructure for modal logic K5.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `k5_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.K5.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

### Change 4: K45/Completeness.lean (lines 13-42)

Replace stale docstring with infrastructure pattern:
```
/-! # K45 Completeness Infrastructure

This module provides import infrastructure for modal logic K45.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `k45_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.K45.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

### Change 5: KB5/Completeness.lean (lines 13-46)

Replace stale docstring with infrastructure pattern:
```
/-! # KB5 Completeness Infrastructure

This module provides import infrastructure for modal logic KB5.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `kb5_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.KB5.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

### Change 6: D4/Completeness.lean (lines 13-37)

Replace stale docstring with infrastructure pattern:
```
/-! # D4 Completeness Infrastructure

This module provides import infrastructure for modal logic D4.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `d4_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.D4.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

### Change 7: D5/Completeness.lean (lines 13-37)

Replace stale docstring with infrastructure pattern:
```
/-! # D5 Completeness Infrastructure

This module provides import infrastructure for modal logic D5.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `d5_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.D5.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

### Change 8: D45/Completeness.lean (lines 13-40)

Replace stale docstring with infrastructure pattern:
```
/-! # D45 Completeness Infrastructure

This module provides import infrastructure for modal logic D45.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `d45_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.D45.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

### Change 9: DB/Completeness.lean (lines 13-37)

Replace stale docstring with infrastructure pattern:
```
/-! # DB Completeness Infrastructure

This module provides import infrastructure for modal logic DB.
The canonical model construction and supporting lemmas are
imported transitively from the shared infrastructure modules.

The weak completeness theorem `db_completeness` is located in
`Cslib.Logics.Modal.Metalogic.Systems.DB.StrongCompleteness`,
where it is derived as a corollary of strong completeness.
-/
```

## Complexity Assessment

This is a straightforward text-only task. All 9 changes are docstring replacements with no
Lean code modifications. No build verification is needed because `/-! ... -/` comments are
not compiled. The implementation should be a single-phase, single-agent operation.

## Risk Assessment

- **Zero risk** to build: changes are comment-only
- **Zero risk** to CI: no code changes, no import changes
- **No blockers** identified
