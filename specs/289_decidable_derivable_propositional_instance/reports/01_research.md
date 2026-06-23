# Research Report: Decidable (Derivable PropositionalAxiom phi) Instance

**Task**: 289 -- Compose instDecidableTautology with prop_completeness_iff_tautology
**Session**: sess_1782234996_fa3ea6_289
**Status**: Researched

## Summary

This is a confirmed one-liner composition gap. Both components exist, are in the same
namespace, and are available through the same import chain. The composition compiles
without errors. No blockers found.

## Component Analysis

### Component 1: instDecidableTautology

- **File**: `Cslib/Logics/Propositional/Semantics/Bool.lean` (line 175)
- **Namespace**: `Cslib.Logic.PL`
- **Signature**:
  ```
  instDecidableTautology.{u_1} {Atom : Type u_1}
    [Fintype Atom] [DecidableEq Atom]
    (phi : Proposition Atom) : Decidable (Tautology phi)
  ```
- **Mechanism**: Reduces tautology to enumeration of all Boolean valuations via
  `tautology_iff_boolEvaluate_true`, then uses `Fintype` decidability.

### Component 2: prop_completeness_iff_tautology

- **File**: `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` (line 558)
- **Namespace**: `Cslib.Logic.PL`
- **Signature**:
  ```
  @[simp] theorem prop_completeness_iff_tautology.{u} {Atom : Type u}
    {phi : Proposition Atom} :
    Tautology phi <-> Derivable PropositionalAxiom phi
  ```
- **Attributes**: `@[simp]`
- **Proof**: `(prop_completeness, prop_soundness_tautology)`

### Composition

The standard library combinator `decidable_of_iff` bridges the two:

```
decidable_of_iff : {b : Prop} -> (a : Prop) -> (a <-> b) -> [Decidable a] -> Decidable b
```

Applied as:
```lean
decidable_of_iff (Tautology phi) prop_completeness_iff_tautology
```

This produces `Decidable (Derivable PropositionalAxiom phi)` from the existing
`Decidable (Tautology phi)` instance via the iff bridge.

## Verified Implementation

The following code compiles cleanly (tested via `lean_run_code`):

```lean
/-- Derivability from `PropositionalAxiom` is decidable when `Atom` is a `Fintype` with
`DecidableEq`. The decision procedure reduces derivability to tautology-checking via
`prop_completeness_iff_tautology`, then uses `instDecidableTautology` to enumerate all
Boolean valuations. -/
instance instDecidableDerivablePropositionalAxiom [Fintype Atom] [DecidableEq Atom]
    (phi : PL.Proposition Atom) : Decidable (Derivable PropositionalAxiom phi) :=
  decidable_of_iff (Tautology phi) prop_completeness_iff_tautology
```

## File Placement Recommendation

**Recommended**: Inline in `StrongCompleteness.lean`, immediately before `end Cslib.Logic.PL`
(after line 560).

**Rationale**:
1. `StrongCompleteness.lean` already imports `Bool.lean` (which provides
   `instDecidableTautology`), so no additional imports are needed.
2. `prop_completeness_iff_tautology` is defined in the same file -- the instance is a
   direct corollary.
3. Both components are in the same namespace (`Cslib.Logic.PL`).
4. The instance is a single line -- creating a separate `Decidability.lean` file would
   add overhead (copyright header, module directive, imports, docstrings) disproportionate
   to the content.
5. The Bimodal precedent (`Cslib/Logics/Bimodal/Metalogic/Decidability/`) uses a separate
   directory because the decision procedure is a multi-file tableau construction. The
   propositional case is fundamentally different: it is a one-line consequence of
   completeness, not a standalone decision procedure.

**Against a separate file**: If a separate file is created, it would need:
- `import Cslib.Logics.Propositional.Metalogic.StrongCompleteness`
- An entry in `Cslib.lean` via `lake exe mk_all --module`
- This would be the first single-instance file in CSLib, setting an unusual precedent

## Lint Compliance

- **docBlame**: Docstring included in the implementation above.
- **defLemma**: `instance` (= `def`) is correct because `Decidable` returns `Type`, not `Prop`.
- **defsWithUnderscore**: Name uses lowerCamelCase (no underscores in the Lean sense -- the
  generated internal name follows CSLib instance naming conventions).
- **topNamespace**: Instance is inside `namespace Cslib.Logic.PL`.
- **unusedSectionVars**: No section variables introduced.

## Universe Considerations

- `instDecidableTautology` is universe-polymorphic: `{Atom : Type u_1}`
- `prop_completeness_iff_tautology` uses `{Atom : Type u}`
- The composition with `variable {Atom : Type*}` unifies cleanly -- confirmed by compilation.

## Dependencies

- **Task 266**: Archived/completed. All required infrastructure is in place.
- **No additional dependencies identified**.

## Blockers

None. This is a straightforward one-liner composition.

## Tactic Survey

Not applicable -- the implementation is a term-mode definition, not a tactic proof.
`decidable_of_iff` handles everything in one application.
