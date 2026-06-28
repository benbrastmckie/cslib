# Implementation Summary: Curry-Howard Isomorphism for ND Proofs

- **Task**: 293 - Curry-Howard Isomorphism between ND Proofs and Typed Lambda Terms
- **Status**: [COMPLETED]
- **Duration**: 1 session
- **Artifacts**: plans/01_curry-howard-plan.md, summaries/01_curry-howard-summary.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md

## What Was Implemented

The Curry-Howard isomorphism between `Theory.Derivation` (propositional natural deduction proofs)
and a purpose-built intrinsically-typed simply-typed lambda calculus `Theory.Term`. The
implementation consists of two new files:

### `Cslib/Logics/Propositional/CurryHoward/Defs.lean`

Defines `Theory.Term {T : Theory Atom} : Ctx Atom -> Proposition Atom -> Type u`, an
intrinsically-typed term inductive with exactly 10 constructors mirroring the 10 constructors
of `Theory.Derivation`:

| `Derivation` constructor | `Term` constructor | Curry-Howard correspondence |
|--------------------------|--------------------|-----------------------------|
| `ax`    | `const` | theory axiom ↔ closed term constant |
| `ass`   | `var`   | context assumption ↔ variable |
| `andI`  | `pair`  | conjunction intro ↔ pair introduction |
| `andE1` | `fst`   | left conjunction elim ↔ first projection |
| `andE2` | `snd`   | right conjunction elim ↔ second projection |
| `orI1`  | `inl`   | left disjunction intro ↔ left injection |
| `orI2`  | `inr`   | right disjunction intro ↔ right injection |
| `orE`   | `case_` | disjunction elim ↔ case analysis |
| `impI`  | `lam`   | implication intro ↔ lambda abstraction |
| `impE`  | `app`   | implication elim (modus ponens) ↔ function application |

### `Cslib/Logics/Propositional/CurryHoward/Isomorphism.lean`

Defines the forward and backward maps and proves the roundtrip properties:

- `Theory.curryHowardForward : T.Derivation G A → Theory.Term G A` - structural recursion,
  maps each Derivation constructor to its Term counterpart.
- `Theory.curryHowardBackward : Theory.Term G A → T.Derivation G A` - structural recursion,
  maps each Term constructor back to its Derivation counterpart.
- `Theory.curryHoward_forward_backward` - `forward (backward t) = t` by structural induction;
  each of the 10 cases is proved by `simp` with IHs.
- `Theory.curryHoward_backward_forward` - `backward (forward d) = d` by structural induction;
  each of the 10 cases is proved by `simp` with IHs.
- `Theory.curryHowardEquiv : T.Derivation G A ≃ Theory.Term G A` - bundles the maps and
  roundtrip proofs as a formal equivalence.

## Verification Results

- **sorry count**: 0 (verified by grep and `lean_verify`)
- **vacuous definitions**: 0
- **new axioms**: 0 (only `propext` and `Quot.sound` from standard Lean foundations)
- `lake build Cslib.Logics.Propositional.CurryHoward.Defs` - PASS
- `lake build Cslib.Logics.Propositional.CurryHoward.Isomorphism` - PASS
- `lake exe lint-style` - PASS (no output = no issues)
- `lake exe mk_all --module` - PASS (Cslib.lean updated with both new modules)
- `lake exe checkInitImports` - FAILS due to pre-existing `Tableau/Intuitionistic/Soundness`
  build failure (task 316 in-progress work); both CurryHoward files import `Cslib.Init` directly
- `lake lint` - FAILS due to same pre-existing `Tableau/Intuitionistic/Soundness` issue
- `lake test` - FAILS due to pre-existing issues in Tableau (task 316) and SequentCalculus files

Pre-existing failures in other tasks (316, SequentCalculus) are NOT caused by this task's changes.
Task-scoped verification passes completely.

## Design Decisions

1. **Intrinsically-typed representation**: The `Term` type indexes over both context `G` and type
   `A`, making well-typedness a compile-time invariant. This matches the design of `Derivation`
   and makes the isomorphism maps trivially structural.

2. **Constructor naming**: Following standard Curry-Howard naming (`lam`, `app`, `pair`, `fst`,
   `snd`, `inl`, `inr`, `case_`, `const`, `var`). The `case_` name (with trailing underscore)
   avoids collision with Lean's built-in `cases` tactic keyword.

3. **`public import` for Derivation**: The file uses `public import` for
   `NaturalDeduction.Basic` so that downstream files importing `CurryHoward.Defs` can see
   `Ctx`, `Theory`, `Proposition` etc. without additional imports.

4. **Proof strategy**: Roundtrip proofs use `simp [curryHowardForward, curryHowardBackward, ih]`
   at each induction case. Since both maps are constructor-for-constructor renamings, each case
   reduces definitionally once the induction hypotheses are applied.

5. **Independence from task 290**: The isomorphism is entirely independent of normalization
   (`reduceStep`, `isNormal`). No imports from task 290 are used.

## Plan Deviations

- **Import style**: Used `public import` instead of `import` for `NaturalDeduction.Basic`
  in `Defs.lean`. This was necessary because the `Theory`, `Ctx`, and `Proposition` types
  are only accessible through public re-exports. The plan did not specify import visibility
  but the change is required for the file to compile.

- **Proof tactic**: The plan expected roundtrip proofs with "each case reduces to `rfl`".
  In practice, cases for multi-argument constructors required `simp [...]` with induction
  hypotheses rather than bare `rfl`. The `rfl` cases (for `const`/`ax` and `var`/`ass`) do
  work with `rfl`; the multi-argument cases require `simp`. This is a minor tactic detail,
  not a conceptual deviation.

## References

* [M. H. B. Sørensen, P. Urzyczyn, *Lectures on the Curry-Howard Isomorphism*][SorensenUrzyczyn2006],
  Section 2.2
