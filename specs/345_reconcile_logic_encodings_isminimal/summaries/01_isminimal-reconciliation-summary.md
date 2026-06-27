# Implementation Summary: Task 345 — Reconcile Logic Encodings (IsMinimal)

- **Status**: COMPLETED
- **Session**: sess_1782560707_b3ce16_345
- **File modified**: `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`

## What Was Implemented

Seven new declarations were added to `Equivalence.lean` inside `namespace Cslib.Logic.PL`,
forming the "strength by inclusion" view that reconciles the two encodings of minimal
propositional strength on the Hilbert substrate.

### New Declarations (in order)

1. **`abbrev minimal : Theory Atom`** — The Hilbert axiom set for the 8 connective schemas
   (K, S, andI, andE1, andE2, orI1, orI2, orE), defined as `AxiomTheory (@MinPropAxiom Atom)`.
   Docstring loudly states `minimal ≠ MPL`.

2. **`abbrev IsMinimal (T : Theory Atom) : Prop`** — The inclusion predicate: a theory carries
   the minimal Hilbert schemas iff it contains `minimal`. Defined as
   `MinimalAxioms (fun φ => φ ∈ T)`, reusing the existing 8-field typeclass (DRY).

3. **`theorem minimalAxioms_iff_forall_minPropAxiom (★)`** — The core bridge lemma:
   `MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ`. Proved by `constructor` + `cases` on
   `MinPropAxiom`, mirroring `MinPropAxiom.toIntPropAxiom`.

4. **`theorem isMinimalIff`** — `IsMinimal T ↔ minimal ⊆ T`. Derived from (★) and
   `mem_axiomTheory`.

5. **`theorem minimalAxioms_iff_subset`** — `MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms`.
   The high-value bridge between typeclass encoding and inclusion encoding, also from (★).

6. **`theorem instIsMinimalExtention`** — Monotone propagation: `[IsMinimal T] → T ⊆ T' → IsMinimal T'`.
   Term-mode proof via (★).

7. **`instance instIsMinimalMinimal`** — `IsMinimal minimal` (base instance). Proved via
   `isMinimalIff` + reflexivity.

## Plan Deviations

- **`@[scoped grind =]` on `isMinimalIff` dropped**: The attribute requires `MinimalAxioms`
  to be tagged `@[scoped grind]` in the same namespace. Since `MinimalAxioms` is not so tagged
  in `Cslib.Logic.PL` (it's not in `Theory` namespace like `IsIntuitionistic`/`IsClassical`),
  the attribute caused a parse error. Removed to avoid the error; the theorem is fully proved
  without it. *(deviation: altered -- removed @[scoped grind =] attribute)*

- **`@[scoped grind →]` on `instIsMinimalExtention` dropped**: Same reasoning. *(deviation: altered)*

- **`omit ... in` ordering**: In CSLib's module system, `omit [DecidableEq Atom] in` must
  precede the docstring, not follow it. All `omit ... in` modifiers were placed before the
  `/-- docstring -/`. *(deviation: altered -- correct ordering discovered during implementation)*

- **`Set.subset_refl` → `fun _ hx => hx`**: `Set.subset_refl` is not in scope under this name.
  Used the definitional proof `fun _ hx => hx` instead. *(deviation: altered)*

## Verification Results

- **Build**: `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` — PASSED
- **checkInitImports**: `Cslib.Init` imported transitively (Equivalence → Basic → Defs → Init)
- **lint-style**: No issues for `Equivalence.lean`
- **lake shake**: No issues for `Equivalence.lean`
- **lake test**: All Propositional module tests passed (pre-existing failures in Bimodal/Modal Tableau are unrelated)
- **sorry count**: 0
- **vacuous count**: 0
- **new axioms**: 0
- **lean_verify**: `minimalAxioms_iff_forall_minPropAxiom`, `isMinimalIff`, `minimalAxioms_iff_subset`, `instIsMinimalExtention` — all `axioms: []`
