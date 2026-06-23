# Research Report: Hilbert-Primary Conservative Extension and Glivenko

**Task**: 284 — Restate ipl_conservative_over_mpl and glivenko as Hilbert-primary
**Session**: sess_1782187168_2b1b69_284

## Executive Summary

The existing `ipl_conservative_over_mpl` and `glivenko` theorems in CSLib are stated using the
ND-level `DerivableIn` system. This task restates them as Hilbert-primary using `Derivable`
with the Hilbert axiom predicates (`MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom`),
routing through the Hilbert algebraic completeness from task 283. ND versions are recovered
as corollaries via an algebraic bridge.

## 1. Current Architecture

### 1.1 Conservative Extension (Conservative.lean)

**File**: `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`

Current signature:
```lean
theorem ipl_conservative_over_mpl {A : Proposition Atom}
    (hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    DerivableIn (MPL (Atom := Atom)) A
```

Uses `DerivableIn` (ND system), routed through ND-level `MPL.alg_complete` and
`IPL.alg_complete` (from `Completeness.lean`). The algebraic core is:
1. Rewrite goal via `MPL.alg_complete` to `forall G [GHA G] v bot_val, AlgEvaluate ... = top`
2. From `IPL.alg_complete.mp h`, instantiate at `WithBot G` with lifted valuation
3. `coe_AlgEvaluate` + `WithBot.coe_eq_coe.mp` close the goal

Supporting infrastructure in the same file:
- `Proposition.IsBotFree`: Bot-free predicate
- `AlgEvaluate_botFree_independent`: Bot-free evaluation is independent of `bot_val`
- `GHAValid_implies_HAValid`, `HAValid_implies_BAValid`: Validity subsumption
- `instHeytingAlgebraWithBot`: `WithBot G` is a HeytingAlgebra when `G` is a GHA
- `coe_AlgEvaluate`: Embedding lemma for `WithBot`

### 1.2 Glivenko's Theorem (Glivenko.lean)

**File**: `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean`

Current signature:
```lean
theorem glivenko {A : Proposition Atom}
    (h : DerivableIn (IPL ∪ CPL : Theory Atom) A) :
    DerivableIn (IPL : Theory Atom) (¬¬A)
```

Uses `DerivableIn` (ND system), routed through `alg_complete_classical` and `IPL.alg_complete`.
The algebraic core is:
1. `alg_complete_classical.mp h` gives BA-validity (modulo discharging theory membership)
2. `glivenko_algebraic` lifts BA-validity of `A` to HA-validity of `¬¬A`
3. `IPL.alg_complete.mpr` converts back to ND derivability

Supporting infrastructure:
- `evalR`: Regular-lifted evaluation
- `eval_regular_val`: Embedding lemma for Regular subalgebra
- `glivenko_algebraic`: The pure algebraic core (`BAValid A → HAValid (¬¬A)`)
- Theory instances: `IsIntuitionistic (IPL ∪ CPL)`, `IsClassical (IPL ∪ CPL)`

### 1.3 Hilbert Completeness (HilbertCompleteness.lean)

**File**: `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean`

Available from task 283:
```lean
theorem MPL.hilbert_alg_complete {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@MinPropAxiom Atom) φ ↔ GHAValid.{u, u} φ

theorem IPL.hilbert_alg_complete {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@IntPropAxiom Atom) φ ↔ HAValid.{u, u} φ

theorem CPL.hilbert_alg_complete {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@PropositionalAxiom Atom) φ ↔ BAValid.{u, u} φ
```

### 1.4 Hilbert-ND Bridge (Equivalence.lean)

**File**: `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`

Available bridges:
```lean
theorem hilbert_iff_nd_min {φ : PL.Proposition Atom} :
    Derivable MinPropAxiom φ ↔ DerivableIn (AxiomTheory MinPropAxiom) (∅ ⊢ φ)

theorem hilbert_iff_nd_int {φ : PL.Proposition Atom} :
    Derivable IntPropAxiom φ ↔ DerivableIn (AxiomTheory IntPropAxiom) (∅ ⊢ φ)

theorem hilbert_iff_nd_cl {φ : PL.Proposition Atom} :
    Derivable PropositionalAxiom φ ↔ DerivableIn (AxiomTheory PropositionalAxiom) (∅ ⊢ φ)
```

**Critical gap**: These bridge to `AxiomTheory Axioms` (a set containing ALL axiom schemata),
NOT to `MPL`/`IPL`/`CPL` (which contain only the axioms beyond the primitive ND rules).
The Equivalence.lean docstring explicitly notes: "AxiomTheory Axioms is not the same as
MPL, IPL, or CPL."

## 2. Proposed Hilbert-Primary Theorems

### 2.1 Hilbert Conservative Extension

```lean
theorem hilbert_ipl_conservative_over_mpl {Atom : Type u} {φ : PL.Proposition Atom}
    (hBF : φ.IsBotFree = true) (h : Derivable (@IntPropAxiom Atom) φ) :
    Derivable (@MinPropAxiom Atom) φ
```

**Proof route**:
1. `IPL.hilbert_alg_complete.mp h` gives `HAValid.{u,u} φ`
2. For any `G : Type u` with `[GeneralizedHeytingAlgebra G]`, `v : Atom → G`, `bot_val : G`:
   - Instantiate HAValid at `(WithBot G)` with `fun x => (v x : WithBot G)`
   - Apply `coe_AlgEvaluate v bot_val φ hBF` to rewrite
   - Apply `WithBot.coe_eq_coe.mp` to extract equality in `G`
3. This gives `GHAValid.{u,u} φ`
4. `MPL.hilbert_alg_complete.mpr` gives `Derivable MinPropAxiom φ`

**Note**: Steps 2-3 are exactly the algebraic core already proved in Conservative.lean for
the ND version. The only change is the entry/exit through Hilbert completeness instead of
ND completeness.

### 2.2 Hilbert Glivenko

```lean
theorem hilbert_glivenko {Atom : Type u} {φ : PL.Proposition Atom}
    (h : Derivable (@PropositionalAxiom Atom) φ) :
    Derivable (@IntPropAxiom Atom) (¬¬φ)
```

**Proof route**:
1. `CPL.hilbert_alg_complete.mp h` gives `BAValid.{u,u} φ`
2. `glivenko_algebraic` gives `HAValid.{u,u} (¬¬φ)` (the algebraic core is already proved)
3. `IPL.hilbert_alg_complete.mpr` gives `Derivable IntPropAxiom (¬¬φ)`

**Note**: This is very clean — 3 lines. The entire algebraic argument (`glivenko_algebraic`)
is already available. `BAValid.{u,u}` matches `glivenko_algebraic`'s hypothesis (both
quantify over `H : Type u`), and `HAValid.{u,u}` matches `IPL.hilbert_alg_complete.mpr`.

## 3. ND Corollary Bridge

### 3.1 The Gap

To derive ND versions as corollaries of the Hilbert versions, we need:
```lean
DerivableIn (IPL) φ ↔ Derivable IntPropAxiom φ
DerivableIn (MPL) φ ↔ Derivable MinPropAxiom φ
DerivableIn (IPL ∪ CPL) φ ↔ Derivable PropositionalAxiom φ
```

These do NOT currently exist. The `hilbert_iff_nd_*` bridge goes to `AxiomTheory Axioms`,
which is a different theory than `MPL`/`IPL`/`CPL`.

### 3.2 Algebraic Bridge Strategy

Each bridge can be proved by routing through algebraic completeness:

**For IPL**:
```lean
theorem derivableIn_ipl_iff_derivable_int {Atom : Type u} [DecidableEq Atom]
    {φ : PL.Proposition Atom} :
    DerivableIn (IPL (Atom := Atom)) φ ↔ Derivable (@IntPropAxiom Atom) φ
```

Proof:
- Forward: `DerivableIn IPL φ → HAValid.{u,u} φ` (by ND `IPL.alg_complete.mp`)
  then `→ Derivable IntPropAxiom φ` (by `IPL.hilbert_alg_complete.mpr`)
- Backward: `Derivable IntPropAxiom φ → HAValid.{u,u} φ` (by `IPL.hilbert_alg_complete.mp`)
  then `→ DerivableIn IPL φ` (by ND `IPL.alg_complete.mpr`)

**Issue**: Universe alignment. ND `IPL.alg_complete` (from `Completeness.lean`) uses
implicit universe `u` from the section variable, while Hilbert `IPL.hilbert_alg_complete`
explicitly annotates `.{u,u}`. Both quantify over `H : Type u` where `u` is the atom
universe, so they should align.

**For MPL**: Same pattern using `GHAValid` and `MPL.alg_complete` / `MPL.hilbert_alg_complete`.

**For CPL (IPL ∪ CPL)**: The ND side uses `alg_complete_classical` which operates on
`[IsIntuitionistic T] [IsClassical T]` theories, quantifying over `H : Type u` with
`BooleanAlgebra` and requiring `T`-validity. This is more complex because:
- The Hilbert side uses `Derivable PropositionalAxiom` (no theory parameter)
- The ND side uses `DerivableIn (IPL ∪ CPL)` (theory with axioms)
- The ND completeness `alg_complete_classical` has a theory-validity hypothesis

The bridge proof would need to show:
- Forward: From `DerivableIn (IPL ∪ CPL) φ`, use `alg_complete_classical` to get BA-validity
  (discharging theory-validity for IPL ∪ CPL axioms in any BA), then `CPL.hilbert_alg_complete.mpr`.
- Backward: From `Derivable PropositionalAxiom φ`, use `CPL.hilbert_alg_complete.mp` to get
  BA-validity, then show `DerivableIn (IPL ∪ CPL) φ` via ND `alg_complete_classical.mpr`.

### 3.3 ND Corollaries

Once the bridges exist, the ND versions are one-line corollaries:

```lean
-- Existing theorem restated as corollary:
theorem ipl_conservative_over_mpl' {A : Proposition Atom}
    (hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    DerivableIn (MPL (Atom := Atom)) A :=
  derivableIn_mpl_iff_derivable_min.mpr
    (hilbert_ipl_conservative_over_mpl hBF (derivableIn_ipl_iff_derivable_int.mp h))

theorem glivenko' {A : Proposition Atom}
    (h : DerivableIn (IPL ∪ CPL : Theory Atom) A) :
    DerivableIn (IPL : Theory Atom) (¬¬A) :=
  derivableIn_ipl_iff_derivable_int.mpr
    (hilbert_glivenko (derivableIn_cpl_iff_derivable_prop.mp h))
```

## 4. Universe Analysis

All three Hilbert completeness theorems use `.{u, u}` where `u` is the atom universe.
The ND completeness theorems use implicit universes from section variables.

Key universe constraints:
- `GHAValid.{u_1, u_2}` has two universe parameters (atom, algebra)
- `HAValid.{u_1, u_2}` similarly
- `BAValid.{u_1, u_2}` similarly
- Hilbert completeness pins both to `u` (the atom universe)
- ND completeness pins both to `u` via section variables
- `glivenko_algebraic` quantifies over `H : Type u`
- `WithBot G : Type u` when `G : Type u` (stays in same universe)

No universe issues are anticipated.

## 5. File Organization

### 5.1 New File

Create `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean`
containing:
1. Hilbert-primary conservative extension (`hilbert_ipl_conservative_over_mpl`)
2. Hilbert-primary Glivenko (`hilbert_glivenko`)
3. Algebraic bridges (`derivableIn_mpl_iff_derivable_min`, `derivableIn_ipl_iff_derivable_int`,
   `derivableIn_cpl_iff_derivable_prop`)
4. ND corollary restated as one-liners

### 5.2 Dependencies

The new file needs to import:
- `Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness` (Hilbert completeness)
- `Cslib.Logics.Propositional.Semantics.Algebra.Conservative` (WithBot infrastructure, IsBotFree)
- `Cslib.Logics.Propositional.Semantics.Algebra.Glivenko` (glivenko_algebraic, evalR infrastructure)
- `Cslib.Logics.Propositional.Semantics.Algebra.Completeness` (ND-level completeness for bridges)

### 5.3 Existing Files

No modifications needed to existing files. The Hilbert-primary versions are NEW theorems
that coexist alongside the existing ND-level versions.

## 6. Proof Complexity Assessment

### 6.1 Hilbert Conservative Extension

**Estimated complexity**: Low. The proof follows the same algebraic route as the existing
ND version but uses `IPL.hilbert_alg_complete.mp` / `MPL.hilbert_alg_complete.mpr` instead of
the ND versions. The algebraic core (`coe_AlgEvaluate`, `WithBot.coe_eq_coe.mp`) is reused
directly.

Estimated proof: ~5-8 lines.

### 6.2 Hilbert Glivenko

**Estimated complexity**: Very low. Three-step composition:
1. `CPL.hilbert_alg_complete.mp` (Hilbert → BA-validity)
2. `glivenko_algebraic` (BA-validity → HA-validity of ¬¬)
3. `IPL.hilbert_alg_complete.mpr` (HA-validity → Hilbert)

Estimated proof: ~3-5 lines.

### 6.3 Algebraic Bridges

**Estimated complexity**: Medium. Each bridge requires composing two completeness directions.
The main potential issue is universe alignment between ND and Hilbert completeness.

For `derivableIn_ipl_iff_derivable_int`: both directions are ~2 lines each through HAValid.

For `derivableIn_cpl_iff_derivable_prop`: slightly more complex because `alg_complete_classical`
requires discharging theory-validity hypotheses.

Estimated total: ~15-25 lines for all three bridges.

### 6.4 Total Estimate

~30-50 lines of new Lean code (proofs only, excluding docstrings/module documentation).
Zero sorry risk — all algebraic infrastructure is already proved.

## 7. Risk Assessment

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| Universe mismatch between ND/Hilbert completeness | Low | Both pin to atom universe `u` |
| `glivenko_algebraic` universe incompatibility | Very Low | Already uses `Type u` matching `.{u,u}` |
| `alg_complete_classical` theory-validity discharge | Low | Same pattern as existing `glivenko` proof |
| Missing `Derivable_mono` for propositional logic | N/A | Not needed; conservative extension goes opposite direction |

## 8. Reuse Check Summary

- `Proposition.IsBotFree`: EXISTS in Conservative.lean -- REUSE
- `coe_AlgEvaluate`: EXISTS in Conservative.lean -- REUSE
- `instHeytingAlgebraWithBot`: EXISTS in Conservative.lean -- REUSE
- `glivenko_algebraic`: EXISTS in Glivenko.lean -- REUSE
- `eval_regular_val`: EXISTS in Glivenko.lean -- REUSE (indirectly via `glivenko_algebraic`)
- `GHAValid_implies_HAValid`: EXISTS in Conservative.lean -- available if needed
- `HAValid_implies_BAValid`: EXISTS in Conservative.lean -- available if needed
- `MPL.hilbert_alg_complete`, `IPL.hilbert_alg_complete`, `CPL.hilbert_alg_complete`: EXISTS in HilbertCompleteness.lean -- REUSE
- `hilbert_iff_nd_*`: EXISTS in Equivalence.lean -- NOT NEEDED (bridge goes through algebra)
- `derivableIn_*_iff_derivable_*`: DOES NOT EXIST -- NEW (algebraic bridges)

No new definitions are recommended. All new content is theorems/lemmas composing existing infrastructure.
