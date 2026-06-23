# Research Report: Hilbert Derived Structural Rules

## Task 281 -- Complete the Set of Hilbert Derived Structural Rules

**Session**: sess_1782187168_2b1b69_281
**Date**: 2026-06-22

---

## 1. Current State of HilbertDerivedRules.lean

The file `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` already contains a **comprehensive set** of derived rules at both the `DerivationTree` level and the `Deriv` (Prop-level) wrapper. Specifically:

### Existing Rules (DerivationTree level)

| Rule | Name | Layer | Axioms Required |
|------|------|-------|-----------------|
| Negation Introduction | `hilbertNegI` | Minimal (K,S) | h_K, h_S |
| Negation Elimination | `hilbertNegE` | Minimal | (none) |
| Biconditional Introduction | `hilbertIffI` | Minimal | h_andI |
| Top Introduction | `hilbertTopI` | Intuitionistic | h_EFQ |
| Bottom Elimination | `hilbertBotE` | Intuitionistic | h_EFQ |
| Conjunction Introduction | `hilbertAndI` | Minimal | h_andI |
| Left Conjunction Elim | `hilbertAndE1` | Minimal | h_andE1 |
| Right Conjunction Elim | `hilbertAndE2` | Minimal | h_andE2 |
| Left Disjunction Intro | `hilbertOrI1` | Minimal | h_orI1 |
| Right Disjunction Intro | `hilbertOrI2` | Minimal | h_orI2 |
| Disjunction Elimination | `hilbertOrE` | Minimal (K,S) | h_K, h_S, h_orE |
| Double Negation Elim | `hilbertDne` | Classical | h_K, h_S, h_EFQ, h_Peirce |
| Left Biconditional Elim | `hilbertIffE1` | Minimal | h_andE1 |
| Right Biconditional Elim | `hilbertIffE2` | Minimal | h_andE2 |

### Existing Deriv-level Wrappers

All 14 rules above have `Deriv`-level wrappers with the `Deriv` suffix:
`hilbertNegIDeriv`, `hilbertNegEDeriv`, `hilbertTopIDeriv`, `hilbertAndIDeriv`,
`hilbertAndE1Deriv`, `hilbertAndE2Deriv`, `hilbertOrI1Deriv`, `hilbertOrI2Deriv`,
`hilbertOrEDeriv`, `hilbertDneDeriv`, `hilbertIffIDeriv`, `hilbertIffE1Deriv`,
`hilbertIffE2Deriv`.

### Existing Rules in FromHilbert.lean

The file `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` provides additional ND-flavored wrappers around the Hilbert infrastructure:

| Rule | Name | Axioms Required |
|------|------|-----------------|
| Implication Introduction | `impI` | h_K, h_S |
| Implication Elimination | `impE` | (none) |
| Bottom Elimination | `botE` | h_EFQ |
| Assumption | `assume` | (none) |
| Axiom Rule | `axiomRule` | (none) |
| Cut | `hilbertCut` | h_K, h_S |
| Weakening | `hilbertWeakening` | (none) |
| Substitution | `hilbertSubstitution` | h_subst |

All have Deriv-level wrappers: `impIDeriv`, `impEDeriv`, `botEDeriv`, `hilbertCutDeriv`, `hilbertWeakeningDeriv`, `hilbertSubstitutionDeriv`.

---

## 2. Hilbert System Architecture

### DerivationTree (Cslib/Logics/Propositional/ProofSystem/Derivation.lean)

The core type is:

```lean
inductive DerivationTree (Axioms : PL.Proposition Atom -> Prop) :
    List (PL.Proposition Atom) -> PL.Proposition Atom -> Type _ where
  | ax (G : List _) (phi : _) (h : Axioms phi)
  | assumption (G : List _) (phi : _) (h : phi in G)
  | modus_ponens (G : List _) (phi psi : _) (d1 : ... (phi -> psi)) (d2 : ... phi)
  | weakening (G D : List _) (phi : _) (d : ... G phi) (h : forall x in G, x in D)
```

### Axiom Tiers (Cslib/Logics/Propositional/ProofSystem/Axioms.lean)

Three inductive predicates define axiom schemata:

- **MinPropAxiom** (8 constructors): implyK, implyS, andI, andE1, andE2, orI1, orI2, orE
- **IntPropAxiom** (9 constructors): MinPropAxiom + efq
- **PropositionalAxiom** (10 constructors): IntPropAxiom + peirce

Subsumption: `MinPropAxiom.toIntPropAxiom` and `IntPropAxiom.toPropAxiom`.

### Key Metatheorems

- **Deduction Theorem** (`deductionTheorem`): If `A :: G |- B` then `G |- A -> B`. Requires K and S axioms. This is what `impI` wraps.
- **Deduction with Membership** (`deductionWithMem`): Removes all occurrences of a hypothesis.

### Prop-level Infrastructure

- `Deriv Axioms G phi := Nonempty (DerivationTree Axioms G phi)`
- `Derivable Axioms phi := Deriv Axioms [] phi`
- `propDerivationSystem Axioms : Metalogic.DerivationSystem`

---

## 3. ND Rules for Reference

The ND system (`Theory.Derivation` in `NaturalDeduction/Basic.lean`) has 10 primitive constructors:

1. `ax` -- theory axiom
2. `ass` -- context assumption
3. `andI` -- conjunction introduction
4. `andE1` -- left conjunction elimination
5. `andE2` -- right conjunction elimination
6. `orI1` -- left disjunction introduction
7. `orI2` -- right disjunction introduction
8. `orE` -- disjunction elimination
9. `impI` -- implication introduction
10. `impE` -- implication elimination

Plus derived rules in `DerivedRules.lean`:
- `botE` (requires `[IsIntuitionistic T]`)
- `negI`, `negE` (wrappers around impI/impE since neg A = A -> bot)
- `topI`
- `dne` (requires `[IsClassical T]`)
- `iffI`, `iffE1`, `iffE2`

---

## 4. Lindenbaum Algebra Usage

### Algebra-level Lindenbaum (Semantics/Algebra/Lindenbaum.lean)

This file constructs `LindenbaumAlgebra T` as a quotient and proves:
- `GeneralizedHeytingAlgebra` instance for any theory T
- `HeytingAlgebra` instance for `[IsIntuitionistic T]`
- `BooleanAlgebra` instance for `[IsIntuitionistic T] [IsClassical T]`

**ND Rules Used Directly** (in the Lindenbaum algebra proofs):
- `Derivation.ass` (assumption)
- `Derivation.andI` (conjunction introduction)
- `Derivation.andE1` (left conjunction elimination)
- `Derivation.andE2` (right conjunction elimination)
- `Derivation.orI1` (left disjunction introduction)
- `Derivation.orI2` (right disjunction introduction)
- `Derivation.orE` (disjunction elimination)
- `Derivation.impI` (implication introduction)
- `Derivation.impE` (implication elimination)
- `Derivation.botE` (bottom elimination, for HA instance)
- `Derivation.dne` (double negation elimination, for BA instance)
- `Theory.derivationTop` (top introduction, for GHA)

This is the **entire** set of ND structural rules used by the Lindenbaum construction.

### Metalogic-level Lindenbaum files

**MinLindenbaum.lean** uses Hilbert `DerivationTree` (not ND) directly. Rules used:
- `DerivationTree.ax` with `MinPropAxiom.orE`
- `DerivationTree.modus_ponens`
- `DerivationTree.weakening`
- `DerivationTree.assumption`
- `propDerivationSystem MinPropAxiom` (mp, weakening, assumption)
- `deductionTheorem` (via `hasDeductionTheorem`)
- `deductionWithMem` (for cut lemma)

**IntLindenbaum.lean** similarly uses:
- `DerivationTree.ax` with `IntPropAxiom.orE`, `IntPropAxiom.efq`
- `DerivationTree.modus_ponens`
- `DerivationTree.weakening`
- `DerivationTree.assumption`
- `propDerivationSystem IntPropAxiom`
- `deductionTheorem` / `deductionWithMem`

### StrongCompleteness files

These use `MinLindenbaum` and `IntLindenbaum` results, not direct derivation tree manipulation.

---

## 5. Gap Analysis

### Task Description vs. Reality

The task description asks: "extend [HilbertDerivedRules.lean] to include all ND structural rules as Hilbert-derived theorems for each tier (MPL/IPL/CPL): andI, andE1, andE2, orI1, orI2, orE, impI, impE, botE (IPL+CPL), dne (CPL)."

**Finding: ALL of these rules already exist.**

| Required Rule | Status | Location |
|---------------|--------|----------|
| andI | EXISTS | `hilbertAndI` in HilbertDerivedRules.lean:148 |
| andE1 | EXISTS | `hilbertAndE1` in HilbertDerivedRules.lean:166 |
| andE2 | EXISTS | `hilbertAndE2` in HilbertDerivedRules.lean:181 |
| orI1 | EXISTS | `hilbertOrI1` in HilbertDerivedRules.lean:198 |
| orI2 | EXISTS | `hilbertOrI2` in HilbertDerivedRules.lean:213 |
| orE | EXISTS | `hilbertOrE` in HilbertDerivedRules.lean:229 |
| impI | EXISTS | `impI` in FromHilbert.lean:71 (deduction theorem wrapper) |
| impE | EXISTS | `impE` in FromHilbert.lean:84 (modus ponens wrapper) |
| botE (IPL+CPL) | EXISTS | `hilbertBotE` in HilbertDerivedRules.lean:133 and `botE` in FromHilbert.lean:97 |
| dne (CPL) | EXISTS | `hilbertDne` in HilbertDerivedRules.lean:265 |

### What IS Missing: Tier-Specific Instantiations

The existing rules are all **generic** -- parameterized over an arbitrary `Axioms` predicate with explicit axiom witnesses (e.g., `h_K`, `h_S`, `h_andI`). What may be needed for the Lindenbaum rebuild (tasks 282-285) is:

1. **Tier-specific instantiations**: Named lemmas that specialize the generic rules to `MinPropAxiom`, `IntPropAxiom`, and `PropositionalAxiom` without requiring the caller to provide explicit axiom witnesses each time.

2. **Missing impI/impE wrappers in HilbertDerivedRules.lean**: The `impI`/`impE` rules live in `FromHilbert.lean`, not in `HilbertDerivedRules.lean`. The task may intend to co-locate all rules in one file with consistent naming (`hilbertImpI`, `hilbertImpE`).

3. **Missing `hilbertBotEDeriv`**: While `hilbertBotE` exists at the DerivationTree level and `botEDeriv` exists in FromHilbert.lean, there is no `hilbertBotEDeriv` wrapper in HilbertDerivedRules.lean (the `botEDeriv` in FromHilbert.lean serves this role, but naming is inconsistent).

### Recommended Additions

#### A. Naming Consistency (add to HilbertDerivedRules.lean)

Add `hilbert`-prefixed wrappers for rules currently only in FromHilbert.lean:
- `hilbertImpI` (wrapping `impI`)
- `hilbertImpE` (wrapping `impE`)
- `hilbertImpIDeriv` (wrapping `impIDeriv`)
- `hilbertImpEDeriv` (wrapping `impEDeriv`)
- `hilbertBotEDeriv` (wrapping `botEDeriv`)

#### B. Tier-Specific Convenience Lemmas

For each of MPL/IPL/CPL, provide versions that use the concrete axiom predicate and auto-supply witnesses. These would enable callers to write `minHilbertAndI d1 d2` instead of `hilbertAndI MinPropAxiom.andI d1 d2`. Namespaces would be:

**MPL tier** (MinPropAxiom -- 8 axioms, no EFQ, no Peirce):
- `MinPropAxiom.hilbertAndI`, `MinPropAxiom.hilbertAndE1`, `MinPropAxiom.hilbertAndE2`
- `MinPropAxiom.hilbertOrI1`, `MinPropAxiom.hilbertOrI2`, `MinPropAxiom.hilbertOrE`
- `MinPropAxiom.hilbertImpI`, `MinPropAxiom.hilbertImpE`
- `MinPropAxiom.hilbertNegI`, `MinPropAxiom.hilbertNegE`
- `MinPropAxiom.hilbertIffI`, `MinPropAxiom.hilbertIffE1`, `MinPropAxiom.hilbertIffE2`

**IPL tier** (IntPropAxiom -- adds EFQ):
- All MPL rules plus:
- `IntPropAxiom.hilbertBotE`, `IntPropAxiom.hilbertTopI`

**CPL tier** (PropositionalAxiom -- adds Peirce):
- All IPL rules plus:
- `PropositionalAxiom.hilbertDne`

#### C. What the Lindenbaum Rebuild Actually Needs

Looking at the Lindenbaum algebra file (`Semantics/Algebra/Lindenbaum.lean`), it uses the **ND system** (`Theory.Derivation`) directly, not the Hilbert system. The task chain (281-285) aims to rebuild this over Hilbert.

For a Hilbert-primary Lindenbaum algebra, the proofs would need to use `DerivationTree` and `Deriv` instead of `Theory.Derivation` and `DerivableIn`. The specific rules needed are:

| Lindenbaum Proof | ND Rule Used | Hilbert Equivalent Needed |
|------------------|-------------|--------------------------|
| `lindenbaumLe_refl` | `Derivation.ass` | `DerivationTree.assumption` (primitive) |
| `lindenbaumLe_trans` | `DerivableIn.cut` | `hilbertCut` or derivation via DT |
| `lindenbaumLe_sup_left` | `Derivation.orI1` + `Derivation.ass` | `hilbertOrI1` + `assumption` |
| `lindenbaumLe_sup_right` | `Derivation.orI2` + `Derivation.ass` | `hilbertOrI2` + `assumption` |
| `lindenbaumSup_le` | `Derivation.orE` + weakening | `hilbertOrE` + `weakening` |
| `lindenbaumInf_le_left` | `Derivation.andE1` + `Derivation.ass` | `hilbertAndE1` + `assumption` |
| `lindenbaumInf_le_right` | `Derivation.andE2` + `Derivation.ass` | `hilbertAndE2` + `assumption` |
| `lindenbaumLe_inf` | `Derivation.andI` | `hilbertAndI` |
| `lindenbaumLe_himp_iff` | `Derivation.impI`, `Derivation.impE`, `Derivation.andE1`, `Derivation.andE2`, `Derivation.andI` | `impI`, `impE`, `hilbertAndE1`, `hilbertAndE2`, `hilbertAndI` |
| `lindenbaumLe_top` | `Derivation.impI` + `Derivation.ass` | `impI` + `assumption` |
| `lindenbaumBot_le` | `Derivation.botE` + `Derivation.ass` | `hilbertBotE` + `assumption` |
| `lindenbaumEM` | `Derivation.dne`, `Derivation.impI`, `Derivation.impE`, `Derivation.orI1`, `Derivation.orI2` | `hilbertDne`, `impI`, `impE`, `hilbertOrI1`, `hilbertOrI2` |

**All needed rules already exist in the Hilbert framework.** The rebuild (tasks 282-285) would rewrite the Lindenbaum algebra proofs to use `DerivationTree`/`Deriv` + the existing Hilbert derived rules instead of `Theory.Derivation`/`DerivableIn`.

---

## 6. Proof Strategy for Potential Additions

### Tier-Specific Instantiations (if added)

These would be trivial wrappers. For example:

```lean
namespace MinPropAxiom
noncomputable def hilbertImpI {G : List (PL.Proposition Atom)}
    {A B : PL.Proposition Atom}
    (d : DerivationTree MinPropAxiom (A :: G) B) :
    DerivationTree MinPropAxiom G (A -> B) :=
  impI mem_implyK mem_implyS d
end MinPropAxiom
```

Each tier instantiation just supplies the concrete axiom witnesses from the corresponding namespace (e.g., `MinPropAxiom.mem_implyK`, `IntPropAxiom.mem_implyK`).

### Naming Convention Wrappers

For `hilbertImpI`/`hilbertImpE` in HilbertDerivedRules.lean:

```lean
noncomputable def hilbertImpI
    {Axioms : PL.Proposition Atom -> Prop}
    (h_K : forall (phi psi : PL.Proposition Atom), Axioms (phi.imp (psi.imp phi)))
    (h_S : forall (phi psi chi : PL.Proposition Atom),
      Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))))
    {G : List (PL.Proposition Atom)} {A B : PL.Proposition Atom}
    (d : DerivationTree Axioms (A :: G) B) :
    DerivationTree Axioms G (A -> B) :=
  impI h_K h_S d

def hilbertImpE
    {Axioms : PL.Proposition Atom -> Prop}
    {G : List (PL.Proposition Atom)} {A B : PL.Proposition Atom}
    (d1 : DerivationTree Axioms G (A -> B))
    (d2 : DerivationTree Axioms G A) :
    DerivationTree Axioms G B :=
  impE d1 d2
```

---

## 7. Architectural Observations

### Two-File Design

The current split between `FromHilbert.lean` and `HilbertDerivedRules.lean` is functional but creates a naming asymmetry:
- `FromHilbert.lean`: `impI`, `impE`, `botE`, `assume`, `axiomRule`, `hilbertCut`, `hilbertWeakening`
- `HilbertDerivedRules.lean`: `hilbertNegI`, `hilbertNegE`, `hilbertAndI`, ... (all `hilbert`-prefixed)

The task description's intent seems to be consolidating all rules with consistent naming in `HilbertDerivedRules.lean`.

### Context Representation Difference

The ND system uses `Finset` contexts; the Hilbert system uses `List` contexts. The `Equivalence.lean` bridge handles this via `Finset.toList` / `List.toFinset`. A Hilbert-primary Lindenbaum would work directly with `List` contexts, eliminating this translation overhead.

### The Lindenbaum Algebra File Uses ND Directly

The current `Semantics/Algebra/Lindenbaum.lean` works entirely with the ND system. Rewriting it over Hilbert (tasks 282-285) means replacing every `Theory.Derivation.*` call with the corresponding `hilbert*` call from `HilbertDerivedRules.lean` and `FromHilbert.lean`, and changing contexts from `Finset` to `List` (or using the bridge).

### DerivableIn vs. Deriv

The ND system uses `DerivableIn T (G |- phi)` while Hilbert uses `Deriv Axioms G phi`. Both are `Nonempty` wrappers. The Hilbert-primary Lindenbaum would define:
- `lindenbaumLe` using `Deriv Axioms [A] B` instead of `DerivableIn T ({A} |- B)`
- All lattice operations using `Deriv`-level Hilbert rules

---

## 8. Recommendations

### Option A: Minimal -- Declare Task Already Done

All rules listed in the task description (andI, andE1, andE2, orI1, orI2, orE, impI, impE, botE, dne) already exist in the Hilbert framework across `HilbertDerivedRules.lean` and `FromHilbert.lean`. The task could be marked as already satisfied.

### Option B: Consolidation -- Add Naming Wrappers (Recommended)

Add `hilbertImpI`, `hilbertImpE`, and `hilbertBotEDeriv` to `HilbertDerivedRules.lean` for naming consistency. This is minimal work (3 thin wrappers + 3 Deriv wrappers = 6 definitions, all trivial).

### Option C: Full Tier Specialization

Add tier-specific convenience lemmas in `MinPropAxiom`, `IntPropAxiom`, and `PropositionalAxiom` namespaces. This provides the most ergonomic API for the downstream Lindenbaum rebuild but adds ~30 one-liner definitions.

### Recommendation

**Option B** is the right scope for this task. It resolves the naming inconsistency with minimal effort and gives the Lindenbaum rebuild (tasks 282-285) a complete, consistently-named API in one file. Option C can be deferred to when the Lindenbaum rebuild reveals whether tier-specific sugar is actually needed.

---

## 9. Implementation Notes

- All new definitions are trivial wrappers (1-2 lines each).
- `hilbertImpI` is `noncomputable` (delegates to deduction theorem).
- `hilbertImpE` is computable (just `DerivationTree.modus_ponens`).
- No new axioms or sorry patterns needed.
- Zero risk of proof failure -- these are definitional wrappings of existing functions.
- Build verification: `lake build Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules`
