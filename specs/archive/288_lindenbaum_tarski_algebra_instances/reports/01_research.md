# Research Report: Lindenbaum-Tarski Algebra Instances (Task 288)

## Summary

The Lindenbaum-Tarski algebra instances for MPL, IPL, and CPL already exist in the codebase
in two parallel constructions (ND-based and Hilbert-based), but they are generic/anonymous
instances parameterized over arbitrary `T : Theory Atom` or `Axioms : Proposition Atom -> Prop`,
not exported as named, standalone facts for the specific named theories MPL, IPL, and CPL. This
task creates a thin facade module that specializes and names these instances for direct use.

## Existing Codebase Analysis

### Two Parallel Lindenbaum-Tarski Constructions

CSLib has two Lindenbaum algebra constructions:

**1. ND-Based (`Lindenbaum.lean`)**
- Type: `LindenbaumAlgebra T` = `Quotient (T.propositionSetoid)` where `T : Theory Atom`
- Generic instances:
  - `GeneralizedHeytingAlgebra (LindenbaumAlgebra T)` -- for any theory T (line 273)
  - `HeytingAlgebra (LindenbaumAlgebra T)` -- when `[IsIntuitionistic T]` (line 339)
  - `BooleanAlgebra (LindenbaumAlgebra T)` -- when `[IsIntuitionistic T] [IsClassical T]` (line 402, noncomputable)

**2. Hilbert-Based (`HilbertLindenbaum.lean`)**
- Type: `HilbertLindenbaumAlgebra Axioms` = `Quotient (@hilbertPropositionSetoid _ Axioms _)`
  where `Axioms : Proposition Atom -> Prop` with `[MinimalAxioms Axioms]`
- Generic instances:
  - `hilbertLindenbaumGHA` : `GeneralizedHeytingAlgebra (HilbertLindenbaumAlgebra Axioms)` -- for any `[MinimalAxioms Axioms]` (line 483)
  - `hilbertLindenbaumIntHA` : `HeytingAlgebra (HilbertLindenbaumAlgebra (@IntPropAxiom Atom))` (line 658)
  - `hilbertLindenbaumClHA` : `HeytingAlgebra (HilbertLindenbaumAlgebra (@PropositionalAxiom Atom))` (line 663)
  - `hilbertLindenbaumClBA` : `BooleanAlgebra (HilbertLindenbaumAlgebra (@PropositionalAxiom Atom))` (line 719)

### What Is Missing

The Hilbert-based construction already has named, specific instances (`hilbertLindenbaumIntHA`,
`hilbertLindenbaumClBA`, etc.) but these are keyed on axiom predicates (`IntPropAxiom`,
`PropositionalAxiom`), not on the user-facing theory names (MPL, IPL, CPL).

The ND-based construction has fully generic instances parameterized by `T : Theory Atom` with
typeclass constraints (`IsIntuitionistic`, `IsClassical`). The specific theories MPL, IPL, CPL
are:
- `MPL = (empty : Theory Atom)` -- minimal propositional logic
- `IPL = Set.range (Proposition.imp bot . )` -- intuitionistic (explosion)
- `CPL = Set.range (fun A => neg (neg A) -> A)` -- classical (DNE)

The generic ND instances fire automatically via typeclass resolution when the theory constraints
are met. However, users cannot write `inferInstance : GeneralizedHeytingAlgebra (LindenbaumAlgebra MPL)`
because `MPL = empty` has no `IsIntuitionistic` instance, and the GHA instance requires no such
constraint. So the GHA instance *does* fire for MPL, but the HA and BA instances require:
- For IPL: `IsIntuitionistic IPL` (which exists as `instIsIntuitionisticIPL`)
- For CPL: both `IsIntuitionistic` and `IsClassical` -- but CPL is defined as just the DNE axiom
  set, not as a theory containing both EFQ and DNE.

**Key observation**: `CPL` as defined in `Defs.lean` is `Set.range (fun A => neg (neg A) -> A)`.
This is NOT a superset of `IPL`. To get the BooleanAlgebra instance on `LindenbaumAlgebra CPL`,
we would need both `[IsIntuitionistic CPL]` and `[IsClassical CPL]`. The `IsClassical CPL`
instance exists (`instIsClassicalCPL`), but `IsIntuitionistic CPL` does NOT exist because CPL
does not contain the EFQ axioms.

This means the task has a design choice: either (a) define a combined theory `CPL_full = IPL union CPL`
and use that, or (b) create the BooleanAlgebra instance using a named abbrev for the combined
theory.

Looking at the HilbertConservativeGlivenko.lean bridge theorems, we see:
```
derivableInCplIffDerivableProp: DerivableIn (IPL union CPL : Theory Atom) phi <-> Derivable PropositionalAxiom phi
```
This confirms that the "full CPL" in the ND world is `IPL union CPL`, not just `CPL` alone.

### Theory Definitions and Instances

| Theory | Definition | IsIntuitionistic? | IsClassical? |
|--------|-----------|-------------------|--------------|
| MPL | `empty` | No | No |
| IPL | `Set.range (bot.imp . )` | Yes (`instIsIntuitionisticIPL`) | No |
| CPL | `Set.range (fun A => neg (neg A) -> A)` | No | Yes (`instIsClassicalCPL`) |
| IPL union CPL | `IPL union CPL` | Yes (via `instIsIntuitionisticExtention`) | Yes (via `instIsClassicalExtention`) |

### Mathlib Typeclasses

- `GeneralizedHeytingAlgebra` (from `Mathlib.Order.Heyting.Basic`): bounded distributive lattice
  with `himp`. Semantics for MPL. Already available as anonymous instance for any `T`.
- `HeytingAlgebra` (from `Mathlib.Order.Heyting.Basic`): GHA + `bot` + `bot_le`. Semantics
  for IPL. Available for any `[IsIntuitionistic T]`.
- `BooleanAlgebra` (from `Mathlib.Order.BooleanAlgebra.Basic`): HA + excluded middle.
  Semantics for CPL. Available via `BooleanAlgebra.ofRegular` for
  `[IsIntuitionistic T] [IsClassical T]`.

## Recommended Approach

### Named Type Abbreviations

Create named type aliases that make the relationship between logics and algebras explicit:

```lean
/-- The Lindenbaum-Tarski algebra of MPL (minimal propositional logic). -/
abbrev MPL.LindenbaumAlgebra (Atom : Type u) [DecidableEq Atom] :=
  Cslib.Logic.PL.LindenbaumAlgebra (Theory.MPL : Theory Atom)

/-- The Lindenbaum-Tarski algebra of IPL (intuitionistic propositional logic). -/
abbrev IPL.LindenbaumAlgebra (Atom : Type u) [DecidableEq Atom] :=
  Cslib.Logic.PL.LindenbaumAlgebra (Theory.IPL : Theory Atom)

/-- The Lindenbaum-Tarski algebra of CPL (classical propositional logic).
Note: uses `IPL union CPL` as the full classical theory with explosion. -/
abbrev CPL.LindenbaumAlgebra (Atom : Type u) [DecidableEq Atom] :=
  Cslib.Logic.PL.LindenbaumAlgebra (Theory.IPL ∪ Theory.CPL : Theory Atom)
```

### Named Instance Declarations

Export explicitly named instance declarations. For the ND-based construction, the GHA instance
is already generic (works for any T), so we just need named wrappers:

```lean
-- MPL: GeneralizedHeytingAlgebra
instance MPL.instGHA : GeneralizedHeytingAlgebra (MPL.LindenbaumAlgebra Atom) := inferInstance

-- IPL: HeytingAlgebra (via IsIntuitionistic IPL)
instance IPL.instHA : HeytingAlgebra (IPL.LindenbaumAlgebra Atom) := inferInstance

-- CPL: BooleanAlgebra (via IsIntuitionistic and IsClassical on IPL union CPL)
noncomputable instance CPL.instBA : BooleanAlgebra (CPL.LindenbaumAlgebra Atom) := inferInstance
```

The `inferInstance` approach works because:
- `LindenbaumAlgebra T` already carries `GeneralizedHeytingAlgebra` for all T
- `IsIntuitionistic IPL` already exists
- For `IPL union CPL`: `IsIntuitionistic` follows from `instIsIntuitionisticExtention` with
  `Set.subset_union_left`, and `IsClassical` from `instIsClassicalExtention` with `Set.subset_union_right`

**However**, we need to verify that the `IsIntuitionistic (IPL union CPL)` and `IsClassical (IPL union CPL)`
instances can be synthesized automatically. If not, we may need to provide explicit instances.

### Characterization Theorems

Export theorems that state the algebraic characterization as standalone facts:

```lean
/-- The Lindenbaum-Tarski algebra of MPL is a GeneralizedHeytingAlgebra. -/
theorem MPL.lindenbaumIsGHA :
    GeneralizedHeytingAlgebra (LindenbaumAlgebra (Theory.MPL : Theory Atom)) := inferInstance

/-- The Lindenbaum-Tarski algebra of IPL is a HeytingAlgebra. -/
theorem IPL.lindenbaumIsHA :
    HeytingAlgebra (LindenbaumAlgebra (Theory.IPL : Theory Atom)) := inferInstance

/-- The Lindenbaum-Tarski algebra of CPL is a BooleanAlgebra. -/
theorem CPL.lindenbaumIsBA :
    BooleanAlgebra (LindenbaumAlgebra (Theory.IPL ∪ Theory.CPL : Theory Atom)) := inferInstance
```

### Module Structure

A single new module at `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean`:

```
Section 1: Named type abbreviations (MPL.LindenbaumAlgebra, IPL.LindenbaumAlgebra, CPL.LindenbaumAlgebra)
Section 2: Explicit IsIntuitionistic/IsClassical instances for the union theory (if needed)
Section 3: Named instances (GHA, HA, BA)
Section 4: Characterization theorems
Section 5: Nontriviality results
Section 6: (Optional) Free Boolean algebra universal property for CPL
```

### Dependencies

This module imports:
- `Cslib.Logics.Propositional.Semantics.Algebra.Lindenbaum` (for LindenbaumAlgebra + instances)
- Possibly `Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum` (if also exporting
  Hilbert-specific instances)

### Imports and CI

After creating the file:
1. Run `lake exe mk_all --module` to update `Cslib.lean` barrel import
2. Run `lake build Cslib.Logics.Propositional.Semantics.Algebra.LindenbaumInstances`
3. Run standard CI pipeline

## Free Boolean Algebra Universal Property (Optional)

### What This Would Mean

The free Boolean algebra on generators `Atom` is the unique (up to isomorphism) Boolean algebra
`F(Atom)` such that for every Boolean algebra `B` and every function `f : Atom -> B`, there
exists a unique Boolean algebra homomorphism `hat f : F(Atom) -> B` extending `f`.

For CPL, the claim would be: `CPL.LindenbaumAlgebra Atom` is the free Boolean algebra on `Atom`.

### Feasibility Assessment

**Not feasible as a zero-sorry implementation in this task**, for these reasons:

1. **No `FreeBooleanAlgebra` in Mathlib**: Mathlib has no `FreeBooleanAlgebra` type or
   universal property characterization. We would need to define it from scratch.

2. **Homomorphism infrastructure**: We would need `BoundedLatticeHom` or `BoolAlgHom`
   (Boolean algebra homomorphisms), which exist in Mathlib but require careful use.

3. **Proof complexity**: The universal property requires proving:
   - Existence of the extension: given `f : Atom -> B`, construct `hat f : CPL.LindenbaumAlgebra Atom -> B`
     as the map induced by `AlgEvaluate (f . ) bot`. This is the easier direction.
   - Uniqueness of the extension: any Boolean algebra homomorphism agreeing with `f` on generators
     must equal `hat f`. This requires showing the quotient map is jointly surjective (every
     equivalence class is generated by formulas over atoms), which is true by construction but
     needs careful argument.
   - Functoriality properties.

4. **Scope**: This would be a significant standalone project, not a side feature of an instance
   export task.

**Recommendation**: Mark as a future task. The existence direction (the canonical map) can
be sketched as a theorem using `AlgEvaluate`, but the full universal property proof is
substantial. Suggest creating a separate task for this.

## Blockers

**No blockers** for the core task (exporting named instances). The dependency on task 266 is
satisfied -- the relevant code (Lindenbaum.lean, HilbertLindenbaum.lean, Completeness.lean) all
exist and have been building since task 266 was completed.

**Potential issue**: The `CPL` theory definition is just the DNE axioms, not the full
EFQ+DNE combination. The module must either:
- Define a combined theory alias (recommended: `Theory.CPL_full := IPL union CPL`), or
- Use `IPL union CPL` directly in the abbrevs

The HilbertConservativeGlivenko.lean bridge already uses `IPL union CPL` as the ND-level classical
theory, establishing precedent for this approach.

## Tactic Survey

The implementation is primarily definitional (abbrevs, instances via `inferInstance`). The main
risk is whether typeclass synthesis can find the required instances for the union theory. A quick
check with `lean_run_code` or `lean_multi_attempt` would confirm this during planning.

Key tactics needed:
- `inferInstance` -- for most instances
- Possibly `exact instIsIntuitionisticExtention Set.subset_union_left` -- for the IPL union CPL case
- `exact instIsClassicalExtention Set.subset_union_right` -- for the CPL union case

## File Dependencies Graph

```
LindenbaumInstances.lean (NEW)
  |
  +-- Lindenbaum.lean
  |     +-- NaturalDeduction/DerivedRules.lean
  |     +-- Mathlib.Order.Heyting.Regular
  |
  +-- HilbertLindenbaum.lean (optional, for Hilbert-specific instances)
        +-- Algebra.lean
        +-- NaturalDeduction/HilbertDerivedRules.lean
        +-- NaturalDeduction/Equivalence.lean
```

## Recommendations

1. **Core deliverable**: Create `LindenbaumInstances.lean` with named type abbreviations and
   named instance declarations for MPL (GHA), IPL (HA), and CPL (BA).

2. **Theory handling**: Use `Theory.IPL union Theory.CPL` for the ND-level classical theory,
   consistent with existing bridge theorems. Do NOT define a new `Theory.CPL_full` -- just
   use the union directly in the abbreviation.

3. **Scope**: Include both ND-based and Hilbert-based named instances. The Hilbert-based ones
   already have partial names (`hilbertLindenbaumIntHA`, `hilbertLindenbaumClBA`) but could
   benefit from better-named re-exports.

4. **Free Boolean algebra**: Defer to a separate task. Document as a future direction in the
   module docstring.

5. **Implementation complexity**: Low. This is a thin facade module (~100-150 lines) with no
   new proofs beyond possibly `instIsIntuitionistic (IPL union CPL)` and
   `instIsClassical (IPL union CPL)`, which may already resolve via typeclass synthesis.
