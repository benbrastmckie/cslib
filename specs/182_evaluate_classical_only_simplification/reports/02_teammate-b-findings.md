# Teammate B Findings: Foundations Typeclass Theorems and Axiom Derivability

## Task 182 -- Evaluate classical only simplification

### Investigation Angle

Foundations typeclass theorems and axiom derivability: catalog all and/or reasoning
available from the Foundations layer, verify Lukasiewicz encoding compliance, map the
wrap/unwrap bridge pattern, and identify any gaps where upper layers use and/or
reasoning not derivable from Foundations alone.

---

## 1. Complete Catalog of Foundations Propositional Theorems

### 1.1 Combinators (Cslib/Foundations/Logic/Theorems/Combinators.lean)

All require `[MinimalHilbert S]` (i.e., `HasAxiomImplyK`, `HasAxiomImplyS`, `ModusPonens`).

| Theorem | Signature | And/Or Related? |
|---------|-----------|-----------------|
| `imp_trans` | `(S |- A -> B) -> (S |- B -> C) -> (S |- A -> C)` | No |
| `identity` | `S |- A -> A` | No |
| `b_combinator` | `S |- (B -> C) -> (A -> B) -> (A -> C)` | No |
| `flip` | `S |- (A -> B -> C) -> (B -> A -> C)` | No |
| `app1` | `S |- A -> (A -> B) -> B` | No |
| `app2` | `S |- A -> B -> (A -> B -> C) -> C` | No |
| **`pairing`** | `S |- A -> B -> neg(A -> neg B)` | **YES -- conjunction intro (Lukasiewicz)** |
| `dni` | `S |- A -> neg neg A` | No |
| **`combine_imp_conj`** | `(S |- P -> A) -> (S |- P -> B) -> (S |- P -> neg(A -> neg B))` | **YES -- conj intro under implication** |
| **`combine_imp_conj_3`** | `(S |- P -> A) -> (S |- P -> B) -> (S |- P -> C) -> S |- P -> neg(A -> neg(neg(B -> neg C)))` | **YES -- triple conj intro** |

**Critical observation**: `pairing` is defined as `app2 A B bot` -- it produces
`imp A (imp B (imp (imp A (imp B bot)) bot))`, which is the Lukasiewicz encoding
`A -> B -> neg(A -> neg B)`. It does NOT use `HasAnd.and`.

### 1.2 Propositional Core (Cslib/Foundations/Logic/Theorems/Propositional/Core.lean)

| Theorem | Typeclass | Signature | And/Or Related? |
|---------|-----------|-----------|-----------------|
| `lem` | `MinimalHilbert` | `S |- neg A -> neg A` (trivial LEM) | No |
| `efq_axiom` | `IntuitionisticHilbert` | `S |- bot -> A` | No |
| `raa` | `IntuitionisticHilbert` | `S |- A -> (neg A -> B)` | No |
| `efq_neg` | `IntuitionisticHilbert` | `S |- neg A -> (A -> B)` | No |
| `peirce_axiom` | `ClassicalHilbert` | `S |- ((A -> B) -> A) -> A` | No |
| `double_negation` | `ClassicalHilbert` | `S |- neg neg A -> A` | No |
| `rcp` | `ClassicalHilbert` | `(S |- neg A -> neg B) -> (S |- B -> A)` | No |
| **`lce_imp`** | `ClassicalHilbert` | `S |- neg(A -> neg B) -> A` | **YES -- left conj elim (Lukasiewicz)** |
| **`rce_imp`** | `ClassicalHilbert` | `S |- neg(A -> neg B) -> B` | **YES -- right conj elim (Lukasiewicz)** |

**Critical observation**: `lce_imp` and `rce_imp` are DT-free (deduction-theorem-free) and
produce formulas using raw `HasImp.imp`/`HasBot.bot`. They work on the Lukasiewicz
encoding `neg(A -> neg B)`, not on `HasAnd.and`.

### 1.3 Propositional Connectives (Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean)

| Theorem | Typeclass | Signature | And/Or Related? |
|---------|-----------|-----------|-----------------|
| `contrapose_imp` | `MinimalHilbert` | `S |- (A -> B) -> (neg B -> neg A)` | No |
| `contraposition` | `MinimalHilbert` | `(S |- A -> B) -> (S |- neg B -> neg A)` | No |
| **`iff_intro`** | `MinimalHilbert` | `(S |- A -> B) -> (S |- B -> A) -> (S |- neg((A -> B) -> neg(B -> A)))` | **YES -- iff as Lukasiewicz conj** |
| **`iff_neg_intro`** | `MinimalHilbert` | Similar for neg formulas | **YES** |
| **`classical_merge`** | `ClassicalHilbert` | `S |- (A -> B) -> ((neg A -> B) -> B)` | **YES -- case split (disjunction-like)** |
| **`contrapose_iff`** | `ClassicalHilbert` | Uses `lce_imp`/`rce_imp` to extract biconditional components | **YES** |
| **`demorgan_conj_neg_forward`** | `ClassicalHilbert` | `S |- neg neg(A -> neg B) -> (neg neg A -> neg B)` | **YES -- De Morgan 1 forward** |
| **`demorgan_conj_neg_backward`** | `ClassicalHilbert` | `S |- (neg neg A -> neg B) -> neg neg(A -> neg B)` | **YES -- De Morgan 1 backward** |
| **`demorgan_conj_neg`** | `ClassicalHilbert` | Biconditional of above | **YES** |
| **`demorgan_disj_neg_forward`** | `ClassicalHilbert` | `S |- neg(neg A -> B) -> neg(neg A -> neg neg B)` | **YES -- De Morgan 2 forward** |
| **`demorgan_disj_neg_backward`** | `ClassicalHilbert` | `S |- neg(neg A -> neg neg B) -> neg(neg A -> B)` | **YES -- De Morgan 2 backward** |
| **`demorgan_disj_neg`** | `ClassicalHilbert` | Biconditional of above | **YES** |

**Critical observation**: ALL theorems in the Foundations layer use purely Lukasiewicz
encoding. The Foundations layer has no dependency on `HasAnd`/`HasOr` at all -- these
theorems only require `HasImp` and `HasBot`.

---

## 2. Typeclass Instances Currently Registered in Upper Layers

### 2.1 Modal K (Cslib/Logics/Modal/ProofSystem/Instances/K.lean)

Current axiom set (11 axioms):
- `HasAxiomImplyK` -- weakening
- `HasAxiomImplyS` -- distribution
- `HasAxiomEFQ` -- ex falso
- `HasAxiomPeirce` -- Peirce's law
- `HasAxiomAndI` -- conjunction intro (primitive)
- `HasAxiomAndE1` -- left conj elim (primitive)
- `HasAxiomAndE2` -- right conj elim (primitive)
- `HasAxiomOrI1` -- left disj intro (primitive)
- `HasAxiomOrI2` -- right disj intro (primitive)
- `HasAxiomOrE` -- disj elim (primitive)
- `HasAxiomK` -- modal distribution

All 15 modal systems (K, T, B, D, S4, S5, K4, K5, K45, KB5, TB, D4, D5, D45, DB)
register the same 6 and/or axiom instances.

After revert: only ImplyK, ImplyS, EFQ, Peirce, and the system-specific modal axioms.
The HasAxiomAnd*/HasAxiomOr* instances would be removed (since `HasAnd`/`HasOr` typeclasses
would no longer be available for Modal.Proposition).

### 2.2 Temporal BX (Cslib/Logics/Temporal/ProofSystem/Instances.lean)

Current: 4 propositional + 6 and/or + 22 temporal + TemporalNecessitation + ClassicalHilbert.

After revert: 4 propositional + 22 temporal + TemporalNecessitation + ClassicalHilbert.
The 6 and/or instances are removed.

### 2.3 Bimodal TM (Cslib/Logics/Bimodal/ProofSystem/Instances.lean)

Current: 4 propositional + 6 and/or + 4 modal (K/T/4/B) + 22 temporal +
TemporalNecessitation + Necessitation + ModalS5Hilbert + ClassicalHilbert +
HasAxiomMF + BimodalTMHilbert.

After revert: same minus the 6 and/or instances.

---

## 3. Lukasiewicz Encoding Verification

### 3.1 Foundations Theorems: Pure Lukasiewicz Encoding -- CONFIRMED

Every and/or theorem in the Foundations layer produces terms using only `HasImp.imp` and
`HasBot.bot`. The encoding is:

```
neg phi      := imp phi bot
and phi psi  := imp (imp phi (imp psi bot)) bot    -- i.e., neg(phi -> neg psi)
or phi psi   := imp (imp phi bot) psi              -- i.e., neg phi -> psi
iff phi psi  := and (imp phi psi) (imp psi phi)    -- encoded as nested neg/imp/bot
```

Proof that Foundations theorems are encoding-clean:

- `pairing` (line 276-282 of Combinators.lean): Defined as `app2 A B bot`, producing
  `imp A (imp B (imp (imp A (imp B bot)) bot))`. This is exactly
  `A -> B -> neg(A -> neg B)` = `A -> B -> (A and B)_Luk`.

- `lce_imp` (line 240-256 of Core.lean): Type signature is
  `imp (imp (imp phi (imp psi bot)) bot) phi`. This is `neg(phi -> neg psi) -> phi`
  = `(phi and psi)_Luk -> phi`.

- `rce_imp` (line 266-307 of Core.lean): Type signature is
  `imp (imp (imp phi (imp psi bot)) bot) psi`. This is `(phi and psi)_Luk -> psi`.

- `combine_imp_conj` (line 296-312): Produces
  `imp P (imp (imp A1 (imp B1 bot)) bot)` = `P -> (A1 and B1)_Luk`.

None of these reference `HasAnd.and` or `HasOr.or`. They are pure imp/bot terms.

### 3.2 Upper Layer Helpers: Currently Use Primitive Constructors -- WILL CHANGE

The upper layer helpers (PropositionalHelpers.lean, Perpetuity/Helpers.lean) currently
bridge to the **primitive** `Formula.and`/`Formula.or` via `HasAxiomAndI`/`HasAxiomAndE1`/etc.

For example, in Temporal `PropositionalHelpers.lean`:
```lean
def pairing (phi psi : Formula Atom) :
    DerivationTree FrameClass.Base [] (phi.imp (psi.imp (Formula.and phi psi))) :=
  unwrap (HasAxiomAndI.andI (phi := phi) (psi := psi) ...)
```

This produces `Formula.and phi psi` -- a **primitive constructor** call.

In Bimodal `Theorems/Combinators.lean` (line 137-138, comment):
> "Uses HasAxiomAndI directly since Formula.and is a primitive constructor,
> not the implication encoding neg(A -> neg B) used by the Foundations combinator."

**After revert**: When `.and`/`.or` become abbreviations (Lukasiewicz encoding), `HasAnd.and`
would unfold to `imp (imp phi (imp psi bot)) bot`, and `HasOr.or` would unfold to
`imp (imp phi bot) psi`. At that point, the Foundations theorems (`Combinators.pairing`,
`Core.lce_imp`, `Core.rce_imp`) would produce **exactly the same terms** as the abbreviated
`Formula.and`/`Formula.or` -- they would be definitionally equal.

---

## 4. Wrap/Unwrap Bridge Pattern Analysis

### 4.1 Pattern Description

Each upper layer bridges between its concrete `DerivationTree` type and the abstract
`InferenceSystem.DerivableIn` interface:

```lean
def wrap (d : DerivationTree fc [] phi) : InferenceSystem.DerivableIn S phi := ⟨d⟩
def unwrap (h : InferenceSystem.DerivableIn S phi) : DerivationTree fc [] phi := h.some
```

This allows calling Foundations theorems (which use `InferenceSystem.DerivableIn`) and
converting results back to the layer's `DerivationTree` type.

### 4.2 Current Bridge Files

**Temporal** (`Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean`):
- `wrap`/`unwrap` for `Temporal.HilbertBX` <-> `DerivationTree FrameClass.Base [] phi`
- Helpers: `doubleNegation`, `efqAxiom`, `impTrans`, `pairing`, `lceImp`, `rceImp`,
  `dni`, `identity`, `demorganDisjNegBackward`
- `pairing`, `lceImp`, `rceImp` delegate to `HasAxiomAndI.andI`, `HasAxiomAndE1.andE1`,
  `HasAxiomAndE2.andE2`
- `demorganDisjNegBackward` uses `HasAxiomOrE.orE`, `HasAxiomAndE1.andE1`, `HasAxiomAndE2.andE2`

**Bimodal Perpetuity** (`Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean`):
- `wrap`/`unwrap` for `Bimodal.HilbertTM` <-> `DerivationTree FrameClass.Base [] phi`
- Helpers: `impTrans`, `identity`, `combineImpConj`, `combineImpConj_3`, `dni`,
  `contraposition`, `doubleNegation`, `lceImp`, `rceImp`, `boxToFuture`, `boxToPast`,
  `boxToPresent`, `tempFutureDerived`
- `combineImpConj` uses `HasAxiomAndI.andI` and `HasAxiomImplyS.implyS`
- `lceImp`/`rceImp` use `HasAxiomAndE1.andE1`/`HasAxiomAndE2.andE2`

**Bimodal Propositional Core** (`Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean`):
- Uses `unwrap` from Perpetuity.Helpers
- `efqAxiom`, `peirceAxiom`, `doubleNegation` delegate to Foundations Core via wrap/unwrap
- `lceImp`, `rceImp` delegate to `HasAxiomAndE1.andE1`/`HasAxiomAndE2.andE2`
- `ldi`, `rdi` use `Axiom.orI1`/`Axiom.orI2` (primitive axiom constructors)
- `lem` proved directly from Peirce + OrI1/OrI2 (primitive)

**Bimodal Propositional Connectives** (`Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean`):
- `classicalMerge`, `contraposeImp`, `contraposition` delegate to Foundations via wrap/unwrap
- `iffIntro`, `contraposeIff`, `iffNegIntro` use `HasAxiomAndI` (primitive and)
- `demorganConjNegForward`/`Backward` proved directly from primitive axioms
- `demorganDisjNegForward`/`Backward` proved directly from primitive axioms

### 4.3 After Revert: Simplified Helpers

After revert, the bridge files simplify dramatically:

**What gets removed from each helpers file:**
- `pairing` (use Foundations `Combinators.pairing` directly)
- `lceImp` (use Foundations `Core.lce_imp` directly)
- `rceImp` (use Foundations `Core.rce_imp` directly)
- `demorganDisjNegBackward` (use Foundations `Connectives.demorgan_disj_neg_backward`)
- `combineImpConj` (use Foundations `Combinators.combine_imp_conj` directly)
- All De Morgan proofs can delegate to Foundations

**What remains in helpers:**
- `wrap`/`unwrap` (always needed)
- `impTrans` (convenience wrapper)
- `identity` (convenience wrapper)
- `doubleNegation` (convenience wrapper)
- `dni` (convenience wrapper)
- `contraposition` (convenience wrapper)
- Temporal/modal-specific helpers (boxToFuture, boxToPast, etc.)

---

## 5. Gap Analysis: Upper Layer Usage Not Covered by Foundations

### 5.1 Full Coverage (No Gaps) -- Propositional Reasoning

After revert, every propositional and/or reasoning pattern used in the upper layers
is covered by Foundations theorems:

| Upper Layer Need | Foundations Theorem | Notes |
|-----------------|-------------------|-------|
| Conjunction intro: `A, B |- A and B` | `Combinators.pairing` | Produces Lukasiewicz conj |
| Left conj elim: `A and B |- A` | `Core.lce_imp` | DT-free, classical |
| Right conj elim: `A and B |- B` | `Core.rce_imp` | DT-free, classical |
| Combine under imp: `(P -> A), (P -> B) |- P -> A and B` | `Combinators.combine_imp_conj` | |
| Triple combine: three imps to nested conj | `Combinators.combine_imp_conj_3` | |
| Iff intro: `(A -> B), (B -> A) |- A iff B` | `Connectives.iff_intro` | Conj of imps |
| Contrapose iff | `Connectives.contrapose_iff` | Uses lce_imp/rce_imp |
| De Morgan neg(A and B) <-> neg A or neg B | `Connectives.demorgan_conj_neg` | Both directions |
| De Morgan neg(A or B) <-> neg A and neg B | `Connectives.demorgan_disj_neg` | Both directions |
| Classical merge: `(A -> B), (neg A -> B) |- B` | `Connectives.classical_merge` | Case analysis |
| Contraposition | `Connectives.contraposition` | |
| Double negation elimination | `Core.double_negation` | |
| Reverse contraposition | `Core.rcp` | |

### 5.2 MCS-Level Helpers That Use Primitive And/Or

The following MCS-level helpers currently depend on primitive and/or constructors.
After revert, they will use Lukasiewicz-encoded formulas instead:

**Bimodal:**
- `SetMaximalConsistent.mcs_or_resolve` (MCSProperties.lean:496) -- Uses `Formula.or`
  in type signature, and `Axiom.orE` internally. After revert: `Formula.or phi psi`
  unfolds to `imp (imp phi bot) psi`, and `orE` axiom is removed. This function
  must be re-proved using `classical_merge` or `implication_property`.
  
  Re-proof strategy: Since `or phi psi = imp (neg phi) psi` under Lukasiewicz, having
  `(neg phi -> psi) in Omega` and `neg phi in Omega` gives `psi in Omega` by
  `implication_property`. If `phi in Omega`, we already have it. So
  `negation_complete` + `implication_property` handles this case without any axiom.

**Temporal:**
- `temporal_or_resolve_left` (MCS.lean:493) -- Same pattern, same re-proof strategy.
- `conj_mcs` (PointInsertion.lean:205) -- Uses `dcs_conj_closed` which uses `pairing`.
  After revert: `pairing` produces `neg(A -> neg B)` which IS the Lukasiewicz `and`,
  so this works unchanged (types align definitionally).
- `or_elim_mcs` (PointInsertion.lean:213) -- Uses `temporal_or_resolve_left`.

### 5.3 Truth Lemma Cases

**Temporal TruthLemma** (Chronicle/TruthLemma.lean:223-253):
- `| and phi psi ...` case -- Uses `conj_mcs` (forward) and `lceImp`/`rceImp` (backward).
  After revert: This **case disappears entirely** from the structural induction, since
  `and` is no longer a constructor. The Lukasiewicz encoding `neg(phi -> neg psi)` reduces
  through the `imp` case automatically.
- `| or phi psi ...` case -- Same: disappears from induction, reduces through `imp`.

**Bimodal TruthLemma** (BXCanonical/TruthLemma.lean):
- Currently does NOT have explicit and/or cases (the truth lemma handles atom, bot, imp,
  box, G, H, untl, snce). This is because the and/or cases must be handled elsewhere
  in the full completeness proof.

### 5.4 Soundness Cases

**Temporal Soundness** (Metalogic/Soundness.lean:69-100):
- `| and_intro phi psi =>` -- Soundness of and-introduction axiom
- `| and_elim_left phi psi =>` -- Soundness of and-elimination left
- `| and_elim_right phi psi =>` -- Soundness of and-elimination right
- `| or_intro_left phi psi =>` -- Soundness of or-introduction left
- `| or_intro_right phi psi =>` -- Soundness of or-introduction right
- `| or_elim phi psi chi =>` -- Soundness of or-elimination (not shown above but exists)
- Lines 362-366: and/or constructor cases in the formula induction

After revert: These 6 axiom soundness cases are removed (axioms removed). The 2 formula
induction cases (and/or) are also removed.

**Bimodal Soundness** (Metalogic/Soundness/):
- Same pattern across all soundness files (Soundness.lean, DenseValidity.lean).
- 6 axiom cases + formula induction cases per file.

### 5.5 Semantics Satisfaction Cases

**Modal Satisfies** (Basic.lean:107-108):
```lean
| .and phi1 phi2 => Satisfies m w phi1 /\ Satisfies m w phi2
| .or phi1 phi2 => Satisfies m w phi1 \/ Satisfies m w phi2
```

After revert: These cases are removed. Under Lukasiewicz encoding:
- `Satisfies m w (and phi psi)` = `Satisfies m w (neg(phi -> neg psi))`
  = `not (Satisfies m w phi -> not (Satisfies m w psi))`
  = (classically) `Satisfies m w phi /\ Satisfies m w psi` -- same semantics.
- `Satisfies m w (or phi psi)` = `Satisfies m w (neg phi -> psi)`
  = `(not (Satisfies m w phi)) -> Satisfies m w psi` -- classically equivalent.

**Temporal Satisfies** (Semantics/Satisfies.lean:63-64):
```lean
| .and phi psi => Satisfies M t phi /\ Satisfies M t psi
| .or phi psi => Satisfies M t phi \/ Satisfies M t psi
```

Same removal pattern.

### 5.6 Identified Gaps

**GAP 1: Disjunction reasoning in MCS without OrE axiom**

`mcs_or_resolve` (both layers) currently uses the `OrE` axiom directly. After revert,
`OrE` is no longer a primitive axiom. However, the function can be re-proved:

Under Lukasiewicz `or phi psi = imp (neg phi) psi`:
- Having `(neg phi -> psi) in Omega` and `neg phi in Omega` gives `psi in Omega`
  via `implication_property`.
- Having `phi in Omega` gives `phi in Omega` directly.
- `negation_complete` gives `phi in Omega` or `neg phi in Omega`.

This is actually simpler than the current proof. **No gap -- re-proof is straightforward.**

**GAP 2: Bimodal LindenbaumQuotient `provEquiv_or_congr`**

(`Algebraic/LindenbaumQuotient.lean:181-200`)
Currently uses `Axiom.orI1`, `Axiom.orI2`, `Axiom.orE` directly. After revert, these
axiom constructors are removed.

Re-proof strategy: Under Lukasiewicz `or A B = imp (neg A) B`:
- `orI1 : A -> or A B` = `A -> (neg A -> B)` -- this is `raa` (reductio ad absurdum)
- `orI2 : B -> or A B` = `B -> (neg A -> B)` -- this is `ImplyK` (weakening)
- `orE` can be derived from classical_merge + contraposition

**No gap -- all three are derivable from ClassicalHilbert.**

**GAP 3: Bimodal `lem` (Law of Excluded Middle with primitive or)**

(`Theorems/Propositional/Core.lean:44-97`)
Currently proved using `Axiom.orI1`, `Axiom.orI2`, and `Peirce` with primitive `or`.
After revert: `or A (neg A)` = `imp (neg A) (neg A)` = identity on `neg A`.

This reduces to `Combinators.identity (neg A)` -- trivially derivable. **No gap.**

**GAP 4: Pattern matches on `.and`/`.or` constructors**

All pattern matches that currently have `.and`/`.or` arms will lose these arms after
revert. This includes:

| Layer | File Type | Current and/or arms | After revert |
|-------|-----------|---------------------|-------------|
| Modal | Satisfies, Denotation, LogicalEquivalence | ~8 each | Removed |
| Modal | Axiom inductive (KAxiom, etc.) | andI/andE1/andE2/orI1/orI2/orE | Removed |
| Modal | Soundness | 6 axiom + 2 formula | Removed |
| Modal | DerivationTree | andI/andE1/andE2/orI1/orI2/orE | Removed |
| Temporal | Satisfies, Subformulas | 2 each | Removed |
| Temporal | Axiom inductive | 6 and/or axioms | Removed |
| Temporal | Soundness, DenseSoundness | 6 + 2 each | Removed |
| Temporal | TruthLemma | 2 | Removed |
| Bimodal | All above + Separation, Decidability, Algebraic | 50+ | Removed |

**These are pure removals, not gaps. No replacement code needed.**

---

## 6. Typeclass Requirements After Revert

### 6.1 What ClassicalHilbert Provides

After revert, the upper layers only need `ClassicalHilbert S`:
- `ModusPonens` (inference rule)
- `HasAxiomImplyK` (weakening)
- `HasAxiomImplyS` (distribution)
- `HasAxiomEFQ` (ex falso)
- `HasAxiomPeirce` (Peirce's law / classical logic)

From these five, ALL propositional reasoning (including and/or) is derivable:

| Derived Capability | Required Axioms | Proof |
|-------------------|----------------|-------|
| Identity (A -> A) | ImplyK, ImplyS | SKK construction |
| Composition (B combinator) | ImplyK, ImplyS | imp_trans of K and S |
| Flip (C combinator) | ImplyK, ImplyS | Multiple K/S steps |
| DNI (A -> neg neg A) | ImplyK, ImplyS | = app1 at bot |
| DNE (neg neg A -> A) | EFQ, Peirce, ImplyK, ImplyS | Peirce(A,bot) + EFQ + B |
| Conj intro (A -> B -> A and B) | ImplyK, ImplyS | pairing = app2 at bot |
| Left conj elim (A and B -> A) | EFQ, Peirce, ImplyK, ImplyS | Peirce(A,neg B) + efq_neg |
| Right conj elim (A and B -> B) | EFQ, Peirce, ImplyK, ImplyS | Peirce(B,bot) + K + B |
| Disj intro left (A -> A or B) | ImplyK, ImplyS | = raa = app1 at bot |
| Disj intro right (B -> A or B) | ImplyK, ImplyS | = ImplyK |
| Disj elim | EFQ, Peirce, ImplyK, ImplyS | classical_merge |
| De Morgan (both) | EFQ, Peirce, ImplyK, ImplyS | Composition of above |
| Contraposition | ImplyK, ImplyS | B combinator at bot |

### 6.2 What Gets Removed from the Typeclass Hierarchy

The following typeclasses in `ProofSystem.lean` are no longer needed by the upper layers:
- `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`
- `HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE`

These remain in the Foundations for the Propositional layer (which keeps primitive and/or).

The bundled classes `TemporalBXHilbert` and `BimodalTMHilbert` currently extend
`HasAxiomAndI`/etc. After revert, their dependency on `HasAnd F`/`HasOr F` is removed,
and the and/or axiom extends are dropped.

---

## 7. Summary of Findings

### 7.1 Completeness of Foundations Coverage

**All and/or reasoning used by the upper layers is derivable from Foundations theorems**
using only `ClassicalHilbert` (ImplyK, ImplyS, EFQ, Peirce, MP). There are zero gaps
where a theorem would require primitive and/or axioms that cannot be obtained from the
Lukasiewicz encoding.

### 7.2 Encoding Alignment

The Foundations theorems produce Lukasiewicz-encoded terms (`imp`/`bot` only). After revert,
the upper layer `Formula.and`/`Formula.or` become abbreviations that unfold to exactly
these Lukasiewicz terms. This means:
- Foundations theorems apply directly (no translation needed)
- Type signatures align by definitional equality
- The wrap/unwrap bridge works unchanged

### 7.3 Bridge Simplification

The helpers files (PropositionalHelpers, Perpetuity/Helpers) can be significantly simplified:
- Remove and/or-specific helpers that duplicate Foundations theorems
- Keep only the wrap/unwrap bridge and convenience wrappers
- Estimated reduction: ~40% of helper code

### 7.4 Proof Obligations After Revert

No new theorems needed. The revert is purely subtractive:
- Remove 6 axiom constructors per system
- Remove 6 HasAxiom instances per system
- Remove pattern match arms for and/or
- Remove soundness cases for and/or axioms
- Remove truth lemma cases for and/or (automatically handled by imp/bot reduction)
- Re-proof `mcs_or_resolve` / `temporal_or_resolve_left` using `implication_property`
  (these become simpler, not harder)

### 7.5 Risk Assessment

**Low risk**: The Foundations theorems are already proven and tested. The Lukasiewicz
encoding is mathematically well-established. The only "new" proofs are the MCS helper
re-proofs, which are simpler than the originals because `or phi psi = neg phi -> psi`
is directly handled by `implication_property`.
