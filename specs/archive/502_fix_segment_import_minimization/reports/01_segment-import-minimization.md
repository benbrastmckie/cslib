# Research Report: Segment.lean Import Minimization

**Task**: 502 — replace transitive `public import ...PrimeTheory` in
`Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean` with direct public imports of the two
modules whose declarations Segment actually consumes.

**Type**: cslib (Lean 4) | Single-file, single-import-line change.

## Summary

The `lake shake` suggestion from the vet of task 493 is confirmed correct. Segment.lean pulls
in `Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory` publicly but consumes **zero**
PrimeTheory-local declarations. Every symbol it uses is declared in — or publicly re-exported
by — exactly two upstream modules:

- `Cslib.Logics.Modal.Metalogic.DerivationTree`
- `Cslib.Foundations.Logic.Metalogic.PrimeExclusion`

Both must be `public import` (Segment's declarations reference these types in public,
`@[expose] public section` signatures). The plain `import Cslib.Init` line is retained per the
CONTRIBUTING.md `Cslib.Init` mandate (enforced by `lake exe checkInitImports`); shake's
suggestion to drop it is the known systemic out-of-scope false positive and is ignored.

## (1) Current Import Block (verified)

`Segment.lean` lines 7-10:

```lean
module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory
```

- Line 9 `import Cslib.Init` — plain (non-public) — **KEEP**.
- Line 10 `public import ...Intuitionistic.PrimeTheory` — **REPLACE** with two direct imports.

## (2) Symbols Segment.lean Consumes -> Declaring Module

| Symbol used in Segment.lean | Declared in | Reached via |
|---|---|---|
| `Metalogic.PrimeAdmissible` (`QuasiPrime` abbrev, l.65) | `Foundations/Logic/Metalogic/PrimeExclusion.lean:63` | PrimeExclusion (direct) |
| `Metalogic.DeductivelyClosed` (l.70, 89) | `Foundations/Logic/Metalogic/PrimeExclusion.lean:44` | PrimeExclusion (direct) |
| `modalDerivationSystem` (l.65 etc.) | `Logics/Modal/Metalogic/DerivationTree.lean:234` | DerivationTree (direct) |
| `DerivationTree` + ctors `.ax`, `.modus_ponens`, `.weakening`, `.assumption` (l.95-97) | `Logics/Modal/Metalogic/DerivationTree.lean:134` | DerivationTree (direct) |
| `Proposition` / `.bot` / `.box` / `.or` / `.imp` / `.atom` | `Logics/Modal/Basic.lean:72` | DerivationTree -> `public import Cslib.Logics.Modal.Basic` |
| `◇` notation (`Proposition.diamond`) | `Logics/Modal/Basic.lean:235` (`scoped prefix:40 "◇"`) | DerivationTree -> Modal.Basic (scoped notation; namespace `Cslib.Logic.Modal` open in Segment) |
| `DerivationSystem` (in `PrimeAdmissible`/`DeductivelyClosed` sigs) | `Foundations/Logic/Metalogic/Consistency.lean` | Both PrimeExclusion and DerivationTree `public import` Consistency |

An automated scan of every top-level declaration name in PrimeTheory.lean
(`ModalSetConsistent`, `ModalPrimeTheory`, `modalDeductiveClosure`, `modal_prime_exclusion`,
`modal_imp_witness`, etc.) against Segment.lean found **no matches** — Segment consumes none of
PrimeTheory's own lemmas. Likewise, no `DeductionTheorem` or `ListHelpers` declaration (the two
other things PrimeTheory adds beyond the target pair) is referenced by Segment.

## (3) Transitive Coverage: two direct imports fully cover the old public re-exports

`PrimeTheory.lean` public imports: PrimeExclusion, Consistency, DerivationTree,
DeductionTheorem, Modal.Basic, ListHelpers.

The replacement pair's public-import closure:

- `DerivationTree.lean` -> `public import` Modal.Basic, Consistency, `Foundations/Logic/Axioms`
- `PrimeExclusion.lean` -> `public import` Consistency

Union covers everything Segment needs: **Modal.Basic** (Proposition + `◇`/`□` notation),
**Consistency** (DerivationSystem), **PrimeExclusion** (PrimeAdmissible, DeductivelyClosed),
**DerivationTree** (the inductive, its constructors, `modalDerivationSystem`). The dropped
transitive modules (DeductionTheorem, ListHelpers) and PrimeTheory's own body contribute
nothing Segment uses. Coverage is complete.

## (4) Target Module Paths Exist (verified)

- `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` — exists.
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` — exists.

Both are already in PrimeTheory's own public-import list (lines 10 and 12), so the module paths
are known-good.

## (5) Recommended Edit (grounds the implementation plan)

Replace line 10 of Segment.lean with two public imports, Foundations-before-Logics ordering
(matching PrimeTheory's own convention):

```lean
module

import Cslib.Init
public import Cslib.Foundations.Logic.Metalogic.PrimeExclusion
public import Cslib.Logics.Modal.Metalogic.DerivationTree
```

Both must be `public` (not plain) because Segment's declarations sit under
`@[expose] public section` and reference these types in their public signatures — dropping
`public` would re-break shake / downstream visibility.

**Do NOT** remove `import Cslib.Init` (line 9). Shake flags it, but the `Cslib.Init` import is
mandated by CONTRIBUTING.md and enforced by `lake exe checkInitImports`; this is the known
systemic out-of-scope shake false positive.

## Verification Command (for implementation phase)

```bash
lake build          # must succeed with no errors
lake shake --add-public --keep-implied --keep-prefix   # must no longer flag Segment.lean line 10
```

(Scoped alternative for faster iteration: `lake build Cslib.Logics.Modal.Metalogic.Constructive.Segment`.)
Expect shake to still report the `import Cslib.Init` line project-wide; that is out of scope and
intentionally left as-is.

## Reuse / Zero-Debt Notes

- No new definitions, abstractions, axioms, or `sorry` involved — pure import reduction.
- No notation changes; the file's existing scoped `◇`/`□` usage is unaffected.
- Single-import-line mechanical change; trivial to plan as one phase.

## Constraints for Implementation

- `.lean` plan-compliance rule applies: execute the single specified edit; do not re-derive
  scope or touch other imports.
- Keep `import Cslib.Init` exactly as-is.
- Verify with `lake build` + the shake command above before marking complete.
