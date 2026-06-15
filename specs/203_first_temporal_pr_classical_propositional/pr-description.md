# PR: feat(Logics/Temporal): temporal formula type with propositional structure

## Summary

This PR introduces `Cslib.Logics.Temporal.Syntax.Formula`, a new module defining the
temporal logic formula type with five primitive constructors and propositional/temporal
structure.

**Key contributions**:

- `Formula α` inductive type with five primitives: `atom`, `bot`, `imp`, `untl`, `snce`
- Derived propositional connectives (`neg`, `top`, `or`, `and`, `iff`) as `abbrev`
- Derived temporal operators (`someFuture`, `allFuture`, `somePast`, `allPast`) as `abbrev`
- `TemporalConnectives (Formula α)` instance connecting to the `Connectives.lean` typeclass hierarchy
- `Bot (Formula α)` and `Top (Formula α)` instances
- Scoped notation for all operators: `¬`, `∧`, `∨`, `→`, `↔`, `U`, `S`, `𝐅`, `𝐆`, `𝐏`, `𝐇`
- `Encodable`/`Countable`/`Infinite`/`Denumerable` instances via Cantor pairing encoding
- `ReflBEq (Formula α)` and `LawfulBEq (Formula α)` instances with explicit proofs

**Scope**: This PR is the first in a planned series of temporal logic PRs. It covers
the core formula type and propositional/structural properties, stopping cleanly at the
`BEqLaws` section boundary (~300 LOC). Temporal-specific content (complexity measure,
`swapTemporal` duality, atom collection, additional derived operators) will follow in
subsequent PRs.

## Dependency

This PR **depends on PR #648** (`feat(Foundations): propositional connectives typeclass hierarchy`),
which introduces `Cslib.Foundations.Logic.Connectives` with:
- `HasBot`, `HasImp`, `HasUntil`, `HasSince` operator typeclasses
- `PropositionalConnectives`, `TemporalConnectives` bundled classes
- Derived `HasNeg`, `HasTop`, `HasOr`, `HasAnd`, `HasIff` via typeclass extension

This PR's branch should be rebased on or merged after PR #648.

## Technical Details

### Formula Type

```lean
inductive Formula (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Formula Atom)
  | untl (φ₁ φ₂ : Formula Atom)
  | snce (φ₁ φ₂ : Formula Atom)
deriving DecidableEq, BEq
```

The five-primitive design is standard for minimal temporal logic (following Kamp 1968 and
Gabbay et al. 1980). The `BEq` derivation provides boolean equality, with the `ReflBEq`
and `LawfulBEq` instances proved manually in the `BEqLaws` section.

### Burgess Convention for Temporal Operators

The derived operators use the Burgess convention: in `untl event guard` and `snce event guard`,
the first argument is the **event** (holds at the witness point) and the second is the **guard**
(holds at all intermediate points).

- `someFuture φ` (F φ): `φ U ⊤` — φ holds at some future point
- `allFuture φ` (G φ): `¬F ¬φ` — φ holds at all future points
- `somePast φ` (P φ): `φ S ⊤` — φ held at some past point
- `allPast φ` (H φ): `¬P ¬φ` — φ held at all past points

This matches the abstract typeclass expansion in the planned `Axioms.lean`.

### Countability Construction

Formula countability is established via a Cantor pairing encoding:

```lean
noncomputable def Formula.encodeNat [Encodable Atom] : Formula Atom → ℕ
  | .atom a => Nat.pair 0 (Encodable.encode a)
  | .bot    => Nat.pair 1 0
  | .imp φ ψ => Nat.pair 2 (Nat.pair φ.encodeNat ψ.encodeNat)
  | .untl φ ψ => Nat.pair 3 (Nat.pair φ.encodeNat ψ.encodeNat)
  | .snce φ ψ => Nat.pair 4 (Nat.pair φ.encodeNat ψ.encodeNat)
```

Injectivity is proved by structural induction, then used to derive:
- `Countable (Formula Atom)` when `Countable Atom`
- `Infinite (Formula Atom)` when `Infinite Atom` (via injection from `Atom`)
- `Denumerable (Formula Atom)` when `Countable Atom` and `Infinite Atom`

## References

- Kamp, H. (1968). *Tense Logic and the Theory of Linear Order*. PhD thesis, UCLA.
- Gabbay, D., Pnueli, A., Shelah, S., and Stavi, J. (1980). On the temporal analysis of
  fairness. In *Proceedings of the 7th ACM SIGPLAN-SIGACT Symposium on Principles of
  Programming Languages*, pp. 163–173. ACM.

## Contribution Roadmap

This is **PR 1 of ~9** planned temporal logic PRs:

| PR | Content | Depends on |
|----|---------|------------|
| **PR 1 (this)** | Formula type, propositional structure, BEq/countability | #648 |
| PR 2 | Complexity measure, temporal depth, derived operators | PR 1 |
| PR 3 | `swapTemporal` duality, atom collection | PR 2 |
| PR 4 | Kripke model type, temporal satisfaction relation | PR 1 |
| PR 5 | Soundness: axiom schema verification | PR 4 |
| PR 6 | Bimodal embedding (temporal into bimodal) | PR 1 |
| PR 7 | Canonical model construction | PR 5 |
| PR 8 | Completeness theorem | PR 7 |
| PR 9 | Decidability (filtration method) | PR 8 |

## Test Plan

- [x] `lake build Cslib.Logics.Temporal.Syntax.Formula` passes with no errors
- [x] `lake exe checkInitImports` passes (Cslib.Init import verified)
- [x] `lake exe lint-style` passes with no style warnings
- [x] `lake exe mk_all --module` confirms `Cslib.lean` is up to date
- [x] No `sorry` or vacuous definitions present
- [x] File is ~307 LOC (within target range of ~300 LOC)

## AI Tools Used

- Claude Code (cslib-implementation-agent): Truncated `Formula.lean` to the ~300 LOC PR
  scope (through `end BEqLaws`), removed the `Mathlib.Data.Finset.Basic` import (not needed
  for the truncated content), updated the module docstring to reflect the PR scope, and ran
  the CSLib CI verification pipeline (`lake build`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake exe mk_all --module`). Composed this PR description
  based on analysis of the file content.
