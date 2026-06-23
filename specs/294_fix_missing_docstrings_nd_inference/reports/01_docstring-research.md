# Research Report: Missing Docstrings in InferenceSystem and NaturalDeduction/Basic

## Summary

Six declarations need docstrings to satisfy the `docBlame` linter. All fixes are mechanical: add `/-- ... -/` doc comments before each declaration. No code changes, no proof changes.

## Target Declarations

### File 1: `Cslib/Foundations/Logic/InferenceSystem.lean`

**1. Line 74 -- Anonymous `Coe` instance (derivation to derivability)**

```lean
instance [InferenceSystem S α] {a : α} : Coe (S⇓a) (DerivableIn S a) := ⟨DerivableIn.fromDerivation⟩
```

Suggested docstring: Coercion from a derivation `S⇓a` to `DerivableIn S a` (derivability). Wraps `DerivableIn.fromDerivation`.

**2. Line 81 -- Anonymous `Coe` instance (derivability to derivation)**

```lean
noncomputable instance [InferenceSystem S α] {a : α} : Coe (DerivableIn S a) (S⇓a) :=
  ⟨DerivableIn.toDerivation⟩
```

Suggested docstring: Noncomputable coercion from `DerivableIn S a` to `S⇓a`, extracting a derivation via `Classical.choice`. Wraps `DerivableIn.toDerivation`.

### File 2: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`

**3. Line 158 -- `emptySequent_eq`**

```lean
theorem Theory.Derivation.emptySequent_eq {A : Proposition Atom} : T⇓A = T⇓(∅ ⊢ A) := rfl
```

Suggested docstring: A derivation `T⇓A` is definitionally equal to a derivation of the empty sequent `T⇓(∅ ⊢ A)`.

**4. Line 160 -- `iff_derivableIn_empty`**

```lean
theorem DerivableIn.iff_derivableIn_empty {A : Proposition Atom} :
    DerivableIn T A ↔ DerivableIn T (∅ ⊢ A) := by rfl
```

Suggested docstring: Derivability `DerivableIn T A` is equivalent to derivability of the empty sequent `DerivableIn T (∅ ⊢ A)`.

**5. Line 335 -- `derivableIn_top`**

```lean
theorem derivableIn_top : DerivableIn T (⊤ : Proposition Atom) := ⟨derivationTop⟩
```

Suggested docstring: The verum `⊤` is derivable in any theory.

**6. Line 361 -- `equiv.refl`**

```lean
def equiv.refl (A : Proposition Atom) : T.equiv A A :=
  let D : T⇓({A} ⊢ A) := ass <| Finset.mem_singleton_self A;
  ⟨D, D⟩
```

This declaration already has a docstring on line 360: `/-- An equivalence of a proposition with itself. -/`. The `/vet` report may have been generated before this docstring was added, or the linter flagged a different issue. **Verify at implementation time** whether the linter still flags this line.

## Docstring Style Conventions

Observations from surrounding code:

- Docstrings use `/-- ... -/` format (Lean 4 doc comment syntax)
- Single-line docstrings for simple declarations
- Multi-line for complex definitions, using indented continuation
- Backticks for inline code references (e.g., `` `DerivableIn S a` ``)
- Reference to related definitions when the declaration wraps or delegates

## Implementation Notes

- All 6 edits are independent and can be applied in any order.
- After edits, verify with `lake build Cslib.Foundations.Logic.InferenceSystem` and `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic`.
- Run `lake lint` to confirm the `docBlame` warnings are resolved for these declarations.
- Declaration 6 (`equiv.refl`) already appears to have a docstring; double-check with linter.
