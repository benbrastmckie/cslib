# Implementation Summary: Phase 2 -- box_iff_TClosure, dia_iff_TClosure

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994 Thm
  8.1.4's biconditional
- **Plan**: plans/02_direct-route.md (v2), Phase 2
- **Status**: [COMPLETED]
- **File modified**: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`

## What was landed

Two new theorems, both sorry-free and axiom-clean (`lean_verify` reports `axioms: []` for each),
extending the Phase 1 base biconditionals (`box_iff_base`, `dia_iff_base`) over the entire
`TClosure {T,B,Four}` class by induction on the `TClosure` derivation:

- `box_iff_TClosure` -- box-forcing equivalence across a `TClosure TS5 R x y`-related label pair,
  interpreted into the model via `ρ : Label Atom → World`.
- `dia_iff_TClosure` -- the dual diamond-forcing equivalence.

Each proof is a five-case induction on `TClosure`, exactly matching the plan's specified case
breakdown:

| Case | Discharge |
|------|-----------|
| `base` | `box_iff_base`/`dia_iff_base` applied to the raw edge-cond hypothesis at the base edge |
| `refl` | `Iff.rfl` |
| `symm` | `Iff.symm` of the inductive hypothesis |
| `trans` | `Iff.trans` of the two inductive hypotheses |
| `eucl` | `absurd` via `GeomAxiom.noConfusion`, since `GeomAxiom.Five ∈ TS5` unfolds to a false three-way constructor-clash disjunction (`Five ∉ TS5`) |

## Plan Deviations

The plan's Phase 2 task text states the goal in shorthand: `box_iff_TClosure : TClosure TS5 R a b
→ (CKForces … a (□A) ↔ CKForces … b (□A))`. Read literally this would need `a`, `b` to be
directly `World`-typed arguments of `TClosure`. This is not well-typed: `TClosure` (declared in
`Deduction.lean:195`) is hardwired to `Label Atom` as its carrier type (`TClosure (𝒯 : Set
GeomAxiom) (R : Label Atom → Label Atom → Prop) : Label Atom → Label Atom → Prop`), not a generic
`World`, and this file may not touch `Deduction.lean` (single-file scope, Preserved Assets).

The only well-typed concretization consistent with the plan's own case-by-case discharge recipe
(`base → box_iff_base`; `refl → Iff.rfl`; `symm → Iff.symm`; `trans → Iff.trans`; `eucl` vacuous)
and with the report's explicit worked example ("`boxE` then closes: from `CKForces (ρx) (□A)` and
`TClosure x y`, transport to `CKForces (ρy) (□A)` via the box-iff") is:

```lean
theorem box_iff_TClosure {Atom : Type u} {World : Type v} [Preorder World]
    {r : World → World → Prop} (hfc : cs5FCIncest r)
    {R : Label Atom → Label Atom → Prop} {ρ : Label Atom → World}
    (hedge : ∀ a b, R a b → r (ρ a) (ρ b)) {x y : Label Atom} (hxy : TClosure TS5 R x y)
    {P : World → Prop} :
    (∀ w' ≥ ρ x, ∀ u, r w' u → P u) ↔ (∀ w' ≥ ρ y, ∀ u, r w' u → P u)
```

i.e. `x y : Label Atom` (matching `TClosure`'s real domain), `ρ : Label Atom → World` interpreting
labels into the model, and an explicit **raw** edge-cond hypothesis `hedge : ∀ a b, R a b →
r (ρ a) (ρ b)` (MMS Def 5.1) that the `base` case consumes to hand `box_iff_base` the `r (ρ x)
(ρ y)` fact it needs. This is a signature concretization forced by `TClosure`'s actual type, not a
strategy substitution: the induction structure, case names, and discharge tactics are exactly as
the plan specifies. `R` and `ρ` are left as explicit parameters (rather than hardcoding `G.R` and
a graph-specific interpretation) so Phase 5 can instantiate them directly against whatever
graph/interpretation it is generalizing over, per the plan's own Phase 5 task list ("Discharge
`boxE`/`diaI` ... via `box_iff_TClosure`/`dia_iff_TClosure` (Phase 2) + the here-helpers").

No other deviation. The Postmortem Constraints' forbidden decomposition (TClosure-clique or exact
`r`-symmetry) was not touched; `hedge` is precisely the sanctioned raw edge-cond invariant.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness`: green.
- `lake exe checkInitImports`: exit 0.
- `lean_verify` on `box_iff_TClosure`: `axioms: []`.
- `lean_verify` on `dia_iff_TClosure`: `axioms: []`.
- `grep '\bsorry\b' Soundness.lean`: zero tactic-level hits (only pre-existing prose mentions in
  module docstrings, unrelated to this phase).
- `grep '^axiom ' Soundness.lean`: zero.
- All six Preserved Assets untouched (no edits outside the new section inserted between
  `dia_iff_base` and the one-point soundness section).

## Next phase

Phase 3 (F2 target-raise + reflexive here-extraction helpers) is independent of Phases 1-2 and can
proceed next per the plan's Dependency Analysis (sequenced after Phases 1-2 only by single-file
territory on `Soundness.lean`, not by a logical dependency).
