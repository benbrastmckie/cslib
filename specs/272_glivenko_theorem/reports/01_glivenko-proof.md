# Research Report: Glivenko's Theorem (Task 272)

## Task

Prove Glivenko's theorem: if CPL proves A then IPL proves not-not-A. Place in
`Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean` alongside `Conservative.lean`.

## Proof Strategy: Regular Elements of Heyting Algebras

### Core Mathematical Idea

In any HeytingAlgebra H, the **regular elements** (those a with a^cc = a) form a
BooleanAlgebra. Mathlib provides this as `Heyting.Regular.instBooleanAlgebra`. The proof
lifts a valuation v : Atom -> H to v' : Atom -> Regular H via the double-complement map,
then uses BA-validity to conclude HA-validity of the double negation.

### Proof Chain

1. **CPL proves A** (hypothesis)
2. **A is BA-valid**: by algebraic completeness (`alg_complete_classical`)
3. **For any HA H and v : Atom -> H**: define v'(x) = toRegular(v(x)) = (v(x)^cc, ...)
4. **AlgEvaluate v' bot A = top in Regular H**: by BA-validity (Regular H is a BA)
5. **Embedding lemma**: (AlgEvaluate v' bot A).val = (AlgEvaluate v bot A)^cc
6. **Therefore**: (AlgEvaluate v bot A)^cc = top
7. **AlgEvaluate v bot (not-not-A) = (AlgEvaluate v bot A)^cc**: by definition of neg and himp_bot
8. **Therefore**: AlgEvaluate v bot (not-not-A) = top
9. **IPL proves not-not-A**: by IPL algebraic completeness (`IPL.alg_complete`)

### Why Regular Elements Work

The key properties of the double-complement map on HeytingAlgebras are:

| Connective | Regular α operation | Relation to α | Mathlib lemma |
|------------|-------------------|---------------|---------------|
| himp (=>) | (a => b).val = a.val => b.val | Identical | `Heyting.Regular.coe_himp` |
| inf (and) | (a inf b).val = a.val inf b.val | Identical | `Heyting.Regular.coe_inf` |
| sup (or) | (a sup b).val = (a.val sup b.val)^cc | Regularized | `Heyting.Regular.coe_sup` |
| bot | bot.val = bot | Identical | `Heyting.Regular.coe_bot` |
| top | top.val = top | Identical | `Heyting.Regular.coe_top` |

The embedding lemma then follows by structural induction on formulas, using:

- **imp case**: `compl_compl_himp_distrib : (a => b)^cc = a^cc => b^cc`
- **and case**: `compl_compl_inf_distrib : (a inf b)^cc = a^cc inf b^cc`
- **or case**: `(a^cc sup b^cc)^c = a^c inf b^c = (a sup b)^c` (via `Heyting.isRegular_compl`)
  so `(a^cc sup b^cc)^cc = (a sup b)^cc`
- **bot case**: `bot^cc = bot` (via `compl_bot` and `compl_top`)

### Negation-Evaluation Identity

A critical fact: `AlgEvaluate v bot (not-not-A) = (AlgEvaluate v bot A)^cc` in any
HeytingAlgebra. This follows because:
- `neg A = A -> bot` (definition of `Proposition.neg`)
- `AlgEvaluate v bot (A -> bot) = (AlgEvaluate v bot A) => bot = (AlgEvaluate v bot A)^c`
  (by `HeytingAlgebra.himp_bot`)
- `AlgEvaluate v bot ((A -> bot) -> bot) = ((AlgEvaluate v bot A)^c) => bot = (AlgEvaluate v bot A)^cc`
  (by `HeytingAlgebra.himp_bot` again)

## Theory Design: CPL as IPL union CPL

### The Theory Issue

In CSLib, `Theory.CPL` is defined as `Set.range (fun A => not-not-A -> A)` -- only the DNE
axioms, **without** ex falso quodlibet. This means `CPL` has `IsClassical` but NOT
`IsIntuitionistic`.

For Glivenko's theorem, "CPL proves A" means derivability in a theory with **both** EFQ and
DNE. The correct formulation uses `IPL union CPL`:

```lean
-- IPL = Set.range (Proposition.imp bot .)  -- EFQ axioms
-- CPL = Set.range (fun A => not-not-A -> A)  -- DNE axioms

instance : IsIntuitionistic (IPL union CPL : Theory Atom) where
  efq A := Set.mem_union_left _ (Set.mem_range.mpr (A, rfl))

instance : IsClassical (IPL union CPL : Theory Atom) where
  dne A := Set.mem_union_right _ (Set.mem_range.mpr (A, rfl))
```

This enables using `alg_complete_classical` which requires both `[IsIntuitionistic T]` and
`[IsClassical T]`.

### Why Not Define a Combined CPL Theory?

The existing `Theory.CPL` definition is intentional: it keeps the theory definitions
minimal and compositional. The Glivenko theorem naturally takes the union, matching the
mathematical convention that "classical logic" means "intuitionistic + DNE."

## Verified Proof Code

The following code has been verified to compile against the current CSLib codebase.

### File: `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean`

```lean
module

public import Cslib.Logics.Propositional.Semantics.Algebra.Completeness
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Mathlib.Order.Heyting.Regular

open Cslib.Logic.PL Proposition Theory Cslib.Logic.InferenceSystem
     Cslib.Logic.InferenceSystem.DerivableIn

universe u

-- Abbreviation for evaluation in the Regular subalgebra
private abbrev evalR {Atom : Type u} {alpha : Type u} [HeytingAlgebra alpha]
    (v : Atom -> alpha) (A : Proposition Atom) : Heyting.Regular alpha :=
  AlgEvaluate (fun x => Heyting.Regular.toRegular (v x)) bot A

-- Embedding lemma: evaluation in Regular alpha gives double complement of evaluation in alpha
private theorem eval_regular_val
    {Atom : Type u} {alpha : Type u} [HeytingAlgebra alpha]
    (v : Atom -> alpha) (A : Proposition Atom) :
    (evalR v A).val = (AlgEvaluate v (bot : alpha) A)^cc := by
  induction A with
  | atom x => rfl
  | bot => simp [evalR, AlgEvaluate, compl_bot, compl_top]
  | imp a b iha ihb =>
    change (evalR v a => evalR v b).val = _
    rw [Heyting.Regular.coe_himp, iha, ihb, AlgEvaluate_imp, compl_compl_himp_distrib]
  | and a b iha ihb =>
    change (evalR v a inf evalR v b).val = _
    rw [Heyting.Regular.coe_inf, iha, ihb, AlgEvaluate_and, compl_compl_inf_distrib]
  | or a b iha ihb =>
    change (evalR v a sup evalR v b).val = _
    rw [Heyting.Regular.coe_sup, iha, ihb, AlgEvaluate_or]
    congr 1
    rw [compl_sup, compl_sup, Heyting.isRegular_compl, Heyting.isRegular_compl]

-- Algebraic Glivenko: BA-valid implies HA-valid under double negation
theorem glivenko_algebraic {Atom : Type u} {A : Proposition Atom}
    (h : forall (H : Type u) [BooleanAlgebra H] (v : Atom -> H),
      AlgEvaluate v (bot : H) A = top) :
    forall (H : Type u) [HeytingAlgebra H] (v : Atom -> H),
      AlgEvaluate v (bot : H) (neg (neg A)) = top := by
  intro H _ v
  simp only [Proposition.neg, AlgEvaluate_imp, AlgEvaluate_bot]
  rw [HeytingAlgebra.himp_bot, HeytingAlgebra.himp_bot]
  have hBA := h (Heyting.Regular H) (fun x => Heyting.Regular.toRegular (v x))
  have := congr_arg Heyting.Regular.val hBA
  rw [eval_regular_val, Heyting.Regular.coe_top] at this
  exact this

variable {Atom : Type u} [DecidableEq Atom]

instance : IsIntuitionistic (IPL union CPL : Theory Atom) where
  efq A := Set.mem_union_left _ (Set.mem_range.mpr (A, rfl))

instance : IsClassical (IPL union CPL : Theory Atom) where
  dne A := Set.mem_union_right _ (Set.mem_range.mpr (A, rfl))

-- Proof-theoretic Glivenko: CPL-derivable implies IPL-derivable under double negation
theorem glivenko {A : Proposition Atom}
    (h : DerivableIn (IPL union CPL : Theory Atom) A) :
    DerivableIn (IPL : Theory Atom) (neg (neg A)) := by
  rw [alg_complete_classical] at h
  rw [IPL.alg_complete]
  intro H _ v
  apply glivenko_algebraic
  intro H' _ v'
  apply h v'
  intro B hB
  rcases (Set.mem_union B IPL CPL).mp hB with hIPL | hCPL
  . obtain (C, rfl) := Set.mem_range.mp hIPL
    simp [AlgEvaluate]
  . obtain (C, rfl) := Set.mem_range.mp hCPL
    simp only [Proposition.neg, AlgEvaluate_imp, AlgEvaluate_bot]
    rw [himp_eq_top_iff, HeytingAlgebra.himp_bot, HeytingAlgebra.himp_bot, compl_compl]
```

**Note**: The above uses ASCII for readability. The actual Lean file should use Unicode
operators. See the implementation plan for the exact file content.

## Mathlib API Dependencies

### Required Imports

| Import | Provides |
|--------|----------|
| `Mathlib.Order.Heyting.Regular` | `Heyting.Regular`, `BooleanAlgebra` instance, `coe_*` simp lemmas |

### Key Lemmas Used

| Lemma | Type | Source |
|-------|------|--------|
| `Heyting.Regular.instBooleanAlgebra` | `BooleanAlgebra (Regular alpha)` | `Mathlib.Order.Heyting.Regular` |
| `Heyting.Regular.toRegular` | `alpha ->o Regular alpha` | `Mathlib.Order.Heyting.Regular` |
| `Heyting.Regular.coe_himp` | `(a => b).val = a.val => b.val` | `Mathlib.Order.Heyting.Regular` |
| `Heyting.Regular.coe_inf` | `(a inf b).val = a.val inf b.val` | `Mathlib.Order.Heyting.Regular` |
| `Heyting.Regular.coe_sup` | `(a sup b).val = (a.val sup b.val)^cc` | `Mathlib.Order.Heyting.Regular` |
| `Heyting.Regular.coe_bot` | `bot.val = bot` | `Mathlib.Order.Heyting.Regular` |
| `Heyting.Regular.coe_top` | `top.val = top` | `Mathlib.Order.Heyting.Regular` |
| `compl_compl_himp_distrib` | `(a => b)^cc = a^cc => b^cc` | `Mathlib.Order.Heyting.Basic` |
| `compl_compl_inf_distrib` | `(a inf b)^cc = a^cc inf b^cc` | `Mathlib.Order.Heyting.Basic` |
| `Heyting.isRegular_compl` | `a^ccc = a^c` | `Mathlib.Order.Heyting.Regular` |
| `HeytingAlgebra.himp_bot` | `a => bot = a^c` | `Mathlib.Order.Heyting.Basic` |
| `compl_compl` | `a^cc = a` (in BA) | `Mathlib.Order.BooleanAlgebra.Basic` |
| `compl_bot` | `bot^c = top` | `Mathlib.Order.Heyting.Basic` |
| `compl_top` | `top^c = bot` | `Mathlib.Order.Heyting.Basic` |

### CSLib Definitions Used

| Definition | Type | Source |
|------------|------|--------|
| `AlgEvaluate` | `(Atom -> H) -> H -> Proposition Atom -> H` | `Semantics/Algebra.lean` |
| `IPL.alg_complete` | `DerivableIn IPL A <-> forall HA, forall v, eval v bot A = top` | `Completeness.lean` |
| `alg_complete_classical` | `DerivableIn T A <-> forall BA, forall v, ... -> eval v bot A = top` | `Completeness.lean` |
| `Theory.IPL` | `Set.range (Proposition.imp bot .)` | `Defs.lean` |
| `Theory.CPL` | `Set.range (fun A => neg (neg A) -> A)` | `Defs.lean` |
| `IsIntuitionistic` | efq axiom class | `Defs.lean` |
| `IsClassical` | dne axiom class | `Defs.lean` |

## Reuse Check Results

| Check | Result |
|-------|--------|
| CSLib Foundations | No existing Glivenko or double-negation translation |
| CSLib Logics | `Conservative.lean` provides the structural pattern (same directory, same imports) |
| Mathlib `Heyting.Regular` | Provides the BooleanAlgebra instance -- the core algebraic tool |
| Existing completeness | `IPL.alg_complete` and `alg_complete_classical` provide both directions |

No new abstractions or typeclasses needed. The proof reuses existing infrastructure entirely.

## File Organization

### New File

`Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean`

### Declarations (5 total)

1. `evalR` (private abbrev) -- Regular-lifted evaluation
2. `eval_regular_val` (private theorem) -- Embedding lemma
3. `glivenko_algebraic` (theorem) -- Algebraic core: BA-valid -> HA-valid under double negation
4. `instIsIntuitionisticIPLunionCPL` (instance) -- IPL union CPL is intuitionistic
5. `instIsClassicalIPLunionCPL` (instance) -- IPL union CPL is classical
6. `glivenko` (theorem) -- Proof-theoretic Glivenko

### Estimated Line Count

- Module header and docstring: ~35 lines
- `evalR` + `eval_regular_val`: ~25 lines
- `glivenko_algebraic`: ~15 lines
- Instances + `glivenko`: ~25 lines
- Total: ~100 lines

### Required CI Updates

- `Cslib.lean` barrel import: add `import Cslib.Logics.Propositional.Semantics.Algebra.Glivenko`
- Run `lake exe mk_all --module` to regenerate

## Tactic Survey Results

The proof is entirely structural -- no automation beyond `simp`, `rw`, and `congr`:

| Tactic | Used For |
|--------|----------|
| `simp` | AlgEvaluate unfolding, bot/top simplification |
| `rw` | Applying Mathlib distribution lemmas (`compl_compl_himp_distrib`, etc.) |
| `congr` | Reducing `a^cc = b^cc` to `a^c = b^c` in the or case |
| `change` | Converting `.val` field projection goals to match `coe_*` simp lemmas |
| `exact` | Closing goals with computed terms |
| `rcases` / `obtain` | Decomposing Set.mem_union and Set.mem_range |

No `sorry`, `decide`, `omega`, `ring`, or `aesop` required.

## Risk Assessment

**Low risk**. The proof has been fully verified in `lean_run_code`. The main risks are:

1. **Universe constraints**: The proof uses `universe u` throughout, matching the pattern in
   `Completeness.lean` and `Conservative.lean`. The `Regular H` type lives in the same
   universe as `H`, so no universe lifting is needed.

2. **Instance diamonds**: The `inf` operation on `Regular alpha` has a potential diamond between
   the GHA inf from `BooleanAlgebra` and the subtype inf. This is resolved by Mathlib's
   instance hierarchy and verified by compilation.

3. **Import transitivity**: `Mathlib.Order.Heyting.Regular` is already imported by
   `Semantics/Algebra/Lindenbaum.lean`, so it's already in the dependency graph. No new
   transitive dependencies.
