# Implementation Summary: Task #398 — efq as Primitive ND Rule (IPL-as-base, MPL retained)

- **Task**: 398 - Make IPL the base propositional logic: add efq as a primitive ND rule, preserving MPL metatheory
- **Status**: [COMPLETED]
- **Phases**: 7/7 completed
- **Zero-debt**: enforced throughout — no `sorry`, `admit`, axiom, or vacuous definition introduced

## What Was Done

### Core Change (Phase 1)
Added `efq {Γ A} [IsIntuitionistic T] : Derivation Γ ⊥ → Derivation Γ A` as a primitive gated
constructor to `Theory.Derivation` in `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`.
The `[IsIntuitionistic T]` instance binder makes efq available exactly at IPL/CPL strength and
unconstructible at MPL (minimal) strength. All three total recursions (`weak`, `subs`,
`substAtom`) and `DerivedRules.botE` (redefined to `Derivation.efq d`) were updated.

### ND–Hilbert Bridge (Phase 2)
Added the `efq` arm to `ndToHilbert`, realising efq-as-rule ↔ efq-as-axiom. The MPL
correspondence (`hilbert_iff_nd_min`, `hilbert_iff_nd_ctx_min`) was preserved unchanged: efq is
unconstructible at `AxiomTheory MinPropAxiom`, so ND-minimal is identical to before.

### Curry-Howard Mirror (Phase 3)
Added `Term.efq [IsIntuitionistic T] : Term Γ ⊥ → Term Γ A` to `CurryHoward/Defs.lean` and
repaired both iso directions and the reduction congruence arm in `Isomorphism.lean` and
`Reduction.lean`.

### Normalization (Phases 4–6)
Extended all four normalization modules with efq arms:
- **Basic/Reduction** (Phase 4): `height`, `isNormal`, `isStronglyNormal` with atomic-restriction
  side condition; efq-permutation conversions in `Reduction.lean`.
- **Termination** (Phase 5): ~52 match sites in `Termination.lean`; the SN measure covers
  efq-permutation reductions.
- **SubformulaProperty** (Phase 6): efq arms in `subformula_property_of_isStronglyNormal` and
  `subformula_property` with zero debt — no `sorry` and no statement weakening.

### Prose Update + Full Verification (Phase 7)
- Updated `Basic.lean` Implementation-notes: records efq as a primitive gated constructor,
  IPL as the base logic, and MPL retained as a fragment layer beneath IPL.
- Added `efq` arm to `ndToLJ` (LJ/Completeness.lean): cut on `⊥` then `botL`.
- Added `efq` arm to `ndToLK` (LK/Completeness.lean): cut on `⊥` then `botL` (with `mono`).
- Full `lake build` (3148 jobs): green.
- CI pipeline: `lake test` (all pass), `lake exe checkInitImports` (clean),
  `lake exe lint-style` (clean), `lake shake` (no regressions in modified files).

## Preserved MPL Assets (Rebuild-Only, No Edits)

All of the following rebuilt green with no source modifications:
- `Metalogic/MinSoundness`, `MinLindenbaum`, `MinStrongCompleteness`
- `Semantics/Algebra/HilbertAlgCompleteness` (provides `MPL/IPL/CPL.hilbert_alg_complete`)
- `Semantics/Algebra/HilbertConservativeGlivenko`, `ConservativeChain`, `MplConservativeChain`
- `Semantics/Algebra/Conservative`, `ImpConservative`, `OrImpConservative`,
  `ConjImpConservative`, `ConjImpBotConservative`
- `Semantics/Algebra/Glivenko`
- All `botE` call sites in `AxiomAdmissibility.lean`, `FromHilbert.lean`

## Downstream Confirmation

- `SequentCalculus/LJ/Completeness` and `LK/Completeness`: green (efq arms added).
- `Modal/Metalogic`, `Modal/FromPropositional`: green (no edits).
- Full library build covers all Temporal, Bimodal, HML modules.

## Key Design Decisions

1. **Gated constructor**: `efq` carries `[IsIntuitionistic T]`; MPL admits no such instance.
2. **Subformula property**: atomic-restriction encoded in the normal-form predicate; no statement
   weakening; no `sorry`.
3. **No Zulip post**: per policy, prose changes are in-source docstrings only.

## Commits

```
d67dfbc9  (pre-task baseline)
90b68d1f  task 398 phase 1: add gated efq constructor and total-recursion arms
4bbd91e1  task 398 phase 2: efq arm in ndToHilbert; hilbert_iff_nd* and MPL correspondence preserved
323f4cbf  task 398 phase 4: normalization efq arms (Basic/Reduction) with decided subformula strategy
34e54fa1  task 398 phase 5: efq arms in Normalization.Termination (SN measure)
95ef5208  task 398 phase 3: repair Curry-Howard reduction efq arms (completes phase 3)
cc56f146  task 398 phase 6: efq arms in Normalization.SubformulaProperty (zero-debt)
13a5b7bd  task 398 phase 7: IPL-as-base docstrings; LJ/LK efq arms; full build + CI green; MPL retained
```

## Plan Deviations

None. All 7 phases completed as planned. Phase 7 extended the original scope with LJ/LK
Completeness efq arms (not listed as files to modify in the plan, but required by the new
constructor for exhaustive match coverage — consistent with the plan's goal of "confirm
insulated and green").
