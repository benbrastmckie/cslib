# Deep Research: Algebraic Completeness for Propositional Logic with Primitive Bot

**Task**: 227 -- Algebraic completeness design (second research pass)
**Session**: sess_1750130000_research227
**Date**: 2026-06-17

---

## A. JohanssonAlgebra Typeclass Design

### A.1 Exact Definition

```lean
/-- A Johansson algebra (j-algebra) is a generalized Heyting algebra equipped with
a designated element playing the role of falsum. Unlike in a Heyting algebra, this
element has no axiomatic constraints (it need not be a bottom element).

Johansson algebras are the algebraic semantics of minimal propositional logic (MPL).
Adding the axiom `designated_bot <= a` for all `a` upgrades to a HeytingAlgebra (IPL).

Reference: Johansson 1937, Rasiowa 1974, Citkin 2021. -/
class JohanssonAlgebra (H : Type*) extends GeneralizedHeytingAlgebra H where
  /-- The designated element corresponding to propositional falsum. -/
  designated_bot : H
```

This is a 5-line typeclass (plus docstring) that extends `GeneralizedHeytingAlgebra` by adding a single field `designated_bot : H`.

### A.2 Position in Mathlib's Hierarchy

Mathlib's order-theoretic hierarchy relevant to us:

```
GeneralizedHeytingAlgebra H
  -- has: top, inf, sup, himp (a => b)
  -- lacks: bot

HeytingAlgebra H extends GeneralizedHeytingAlgebra H
  -- adds: bot, with bot_le : forall a, bot <= a
  -- adds: himp_bot : a => bot = compl a

BooleanAlgebra H extends HeytingAlgebra H (via GeneralizedBooleanAlgebra)
  -- adds: compl with inf_compl_le_bot, top_le_sup_compl
```

`JohanssonAlgebra` sits between GHA and HA:

```
GHA <--- JohanssonAlgebra (adds designated_bot, no axioms on it)
  |
  v
HeytingAlgebra (adds bot with bot_le)
  |
  v
BooleanAlgebra (adds complementation laws)
```

### A.3 Instance: HeytingAlgebra -> JohanssonAlgebra

```lean
/-- Every Heyting algebra is a Johansson algebra where the designated element is
the algebra's bottom. -/
instance [HeytingAlgebra H] : JohanssonAlgebra H where
  designated_bot := bot
```

This is the canonical instance. Note: `BooleanAlgebra` inherits this transitively.

### A.4 Impact on AlgEvaluate

Currently:
```lean
def AlgEvaluate [GeneralizedHeytingAlgebra H] (v : Atom -> H) (bot_val : H) :
    PL.Proposition Atom -> H
```

Refactored:
```lean
def AlgEvaluate [JohanssonAlgebra H] (v : Atom -> H) :
    PL.Proposition Atom -> H
  | .atom x => v x
  | .bot => JohanssonAlgebra.designated_bot
  | .imp a b => AlgEvaluate v a => AlgEvaluate v b
  | .and a b => AlgEvaluate v a ⊓ AlgEvaluate v b
  | .or a b => AlgEvaluate v a ⊔ AlgEvaluate v b
```

The `bot_val` parameter is absorbed into the typeclass. This eliminates a loose parameter from every call site.

**Backward compatibility**: The old `AlgEvaluate v bot_val phi` can be recovered as `AlgEvaluate (H := JohanssonAlgebra.mk bot_val) v phi` if we define a convenience constructor. However, the cleaner approach is to directly refactor.

### A.5 Impact on Validity Definitions

Currently:
```lean
def GHAValid (phi) := forall (H) [GHA H] (v) (bot_val), AlgEvaluate v bot_val phi = top
def HAValid (phi) := forall (H) [HA H] (v), AlgEvaluate v bot phi = top
def BAValid (phi) := forall (H) [BA H] (v), AlgEvaluate v bot phi = top
```

Refactored:
```lean
def JValid (phi) := forall (H) [JohanssonAlgebra H] (v), AlgEvaluate v phi = top
def HAValid (phi) := forall (H) [HeytingAlgebra H] (v), AlgEvaluate v phi = top
def BAValid (phi) := forall (H) [BooleanAlgebra H] (v), AlgEvaluate v phi = top
```

`GHAValid` becomes `JValid` (Johansson-valid). `HAValid` and `BAValid` are unchanged in meaning -- the `HeytingAlgebra` instance provides `designated_bot = bot`, so `AlgEvaluate v .bot = bot` automatically.

### A.6 Simp Lemmas Needed

```lean
@[simp] theorem AlgEvaluate_bot [JohanssonAlgebra H] (v : Atom -> H) :
    AlgEvaluate v .bot = JohanssonAlgebra.designated_bot := rfl

-- For HA/BA specialization:
@[simp] theorem AlgEvaluate_bot_ha [HeytingAlgebra H] (v : Atom -> H) :
    AlgEvaluate v (.bot : PL.Proposition Atom) = (bot : H) := rfl
```

### A.7 Decision: Typeclass vs Loose Parameter

**Recommendation: Keep Option A (loose bot_val) for the initial completeness PR; introduce JohanssonAlgebra in a second "polish" PR.**

Rationale:
1. xcthulhu's completeness code works with the loose `bot_val` parameter directly.
2. The BimodalLogic code also uses a loose parameter pattern.
3. Introducing a new typeclass simultaneously with 1000+ lines of completeness proofs risks reviewability issues.
4. A clean refactoring PR after completeness is established is more maintainable.

However, the report below describes exact signatures in BOTH the loose-parameter style (for the initial PR) and the typeclass style (for the polish PR), so the planner can choose.

---

## B. Lindenbaum Algebra Construction for Primitive-Bot Proposition

### B.1 Key Infrastructure Already in CSLib

The following are already present in CSLib's `NaturalDeduction/Basic.lean`:

| Component | Location | Type |
|-----------|----------|------|
| `Theory.Equiv` | `Basic.lean:150` | `Nonempty (T.equiv A B)` |
| `Theory.propositionSetoid` | `Basic.lean:392` | `Setoid (Proposition Atom)` |
| `equiv_equivalence` | `Basic.lean:388` | `Equivalence T.Equiv` |
| `derivable_iff_equiv_top` | `Basic.lean:312` | `DerivableIn T A <-> A ≡[T] ⊤` |
| `derivableIn_top` | `Basic.lean:310` | `DerivableIn T ⊤` |
| `DerivableIn.cut` | `Basic.lean` | Cut rule |
| `Derivation.weak` | `Basic.lean:180` | Weakening |

These are all the building blocks needed for the Lindenbaum algebra construction.

### B.2 Quotient Type

xcthulhu defines the Lindenbaum quotient as:

```lean
-- Type alias (Heyting.lean uses Quotient directly)
abbrev LindenbaumAlg (T : Theory Atom) := Quotient T.propositionSetoid
```

In CSLib this is directly available as `Quotient T.propositionSetoid`.

### B.3 Partial Order

xcthulhu's `propPO` (Heyting.lean:~line 142):

```lean
instance propPO : PartialOrder (Quotient T.propositionSetoid) where
  le := Quotient.lift₂ (fun A B => DerivableIn T ({A} ⊢ B)) (by ...)
  le_refl := ...   -- from equiv.refl
  le_trans := ...  -- from DerivableIn.cut
  le_antisymm := ... -- from equiv_iff
```

The well-definedness proof needs `equiv_iff_equiv_derivableIn` and `equiv_iff_equiv_derivableIn_hypothesis`, both present in CSLib at `Basic.lean:350,362`.

### B.4 Lattice Structure

xcthulhu's `propLattice` defines:
- `sup` via `Quotient.lift₂ (fun A B => ⟦A ∨ B⟧)` -- well-defined by `Theory.Equiv.or_or`
- `inf` via `Quotient.lift₂ (fun A B => ⟦A ∧ B⟧)` -- well-defined by `Theory.Equiv.and_and`

**Congruence lemmas needed**: `Theory.Equiv.or_or` and `Theory.Equiv.and_and` -- showing ProvEquiv respects conjunction and disjunction. These are present in the BimodalLogic codebase (`provEquiv_and_congr`, `provEquiv_or_congr`) and can be derived from the existing `equiv_iff_equiv_derivableIn` infrastructure.

The lattice laws (le_sup_left, sup_le, inf_le_left, le_inf) all follow from ND derivation rules (disjI₁, disjE, conjE₁, conjI) -- all present in CSLib.

### B.5 GeneralizedHeytingAlgebra Instance

xcthulhu's `propGeneralizedHeyting` (Heyting.lean:~line 252):

```lean
instance propGeneralizedHeyting [Inhabited Atom] :
    GeneralizedHeytingAlgebra (Quotient T.propositionSetoid) where
  top := ⟦⊤⟧
  le_top := ...  -- from derivableIn_top
  himp := Quotient.lift₂ (fun A B => ⟦A → B⟧) (by ...)
  le_himp_iff := ... -- from implI / implE
```

The `le_himp_iff` proof is the key algebraic content: it establishes the adjunction `A ⊓ B ≤ C <-> A ≤ B ⇨ C` in the Lindenbaum algebra, which translates to the equivalence between `{A ∧ B} ⊢ C` and `{A} ⊢ B → C`. This is exactly the deduction theorem for ND.

**Requires `[Inhabited Atom]`**: This is because `top = ⟦⊤⟧ = ⟦⊥ → ⊥⟧` uses the `bot` constructor, which is always available (it's primitive in our `Proposition` type), but the general theory machinery sometimes needs a witness atom. In xcthulhu's code, `[Inhabited Atom]` is required for `derivationTop` and related. In CSLib, `derivationTop` is unconditional (it's `impI ∅ (ass ...)` which works without inhabitants).

**Important finding**: CSLib's `derivableIn_top` DOES NOT require `[Inhabited Atom]` -- it works unconditionally because `⊤ = ⊥ → ⊥` and the proof is `impI ∅ (ass ...)`. This is better than xcthulhu's version.

### B.6 HeytingAlgebra Instance (for IPL and richer theories)

xcthulhu's `propHeyting` / `propHeytingOfLE`:

```lean
@[reducible]
def propHeytingOfLE [Bot Atom] (h : IPL ≤ T) :
    HeytingAlgebra (Quotient T.propositionSetoid) where
  bot_le := Quotient.ind fun A => by
    simp only [T.bot, T.mk_le_mk]
    -- Uses efqOfIPLHyp to derive {⊥} ⊢ A
    refine ⟨efqOfIPLHyp ? (Finset.mem_singleton_self ⊥) A⟩
    exact (nonempty_embedding_iff_le.mpr h).some
  himp_bot := Quotient.ind fun A => rfl
```

**Critical point about `[Bot Atom]`**: xcthulhu's code requires `[Bot Atom]` because their `Proposition` does NOT have a primitive `bot`. Instead, `⊥` in propositions is `atom ⊥` where `⊥ : Atom` is given by `[Bot Atom]`.

**In CSLib, we do NOT need `[Bot Atom]`** because `Proposition.bot` is primitive. This simplifies the construction significantly:

```lean
-- CSLib version (no [Bot Atom] needed)
def propHeytingOfIPL [IsIntuitionistic T] :
    HeytingAlgebra (Quotient T.propositionSetoid) where
  bot := ⟦.bot⟧
  bot_le := Quotient.ind fun A => by
    simp only [mk_le_mk]
    -- Uses efq from IsIntuitionistic: ⊢ ⊥ → A is in T
    exact ⟨...⟩  -- derive {⊥} ⊢ A using ax (IsIntuitionistic.efq A)
  himp_bot := Quotient.ind fun A => rfl
```

### B.7 BooleanAlgebra Instance (for CPL and richer theories)

xcthulhu's `propBoolean` / `propBooleanOfLE`:

```lean
def propBooleanOfLE [Bot Atom] (h : CPL ≤ T) :
    BooleanAlgebra (Quotient T.propositionSetoid) := by
  let iH : HeytingAlgebra ... := propHeytingOfLE (ipl_le_cpl.trans h)
  refine BooleanAlgebra.ofRegular (Quotient.ind fun A => ?)
  -- Show: every element is Heyting-regular (¬¬A = A)
  -- Uses dneOfCPL
```

BimodalLogic's `BooleanStructure.lean` proves this in ~450 lines with a more direct construction building `BooleanAlgebra` from scratch (sup = or, inf = and, compl = neg, sdiff, himp).

**CSLib version**: Following xcthulhu's approach is much more concise. `BooleanAlgebra.ofRegular` reduces the problem to showing every quotient element is Heyting-regular (i.e., `¬¬⟦A⟧ = ⟦A⟧`), which follows from double-negation elimination (Peirce's law or DNE axiom).

### B.8 The JohanssonAlgebra Instance

For the Lindenbaum algebra of ANY theory T (not just IPL/CPL), the JohanssonAlgebra instance is:

```lean
-- With loose bot_val approach (current)
-- No special instance needed; just use:
-- bot_val := ⟦.bot⟧ in AlgEvaluate

-- With JohanssonAlgebra typeclass:
instance propJohansson :
    JohanssonAlgebra (Quotient T.propositionSetoid) where
  designated_bot := ⟦.bot⟧
```

### B.9 Key Verification: ⟦.bot⟧ Behavior

**For MPL**: `⟦.bot⟧` is NOT the bottom of the GHA. There is no proof that `{⊥} ⊢ A` for arbitrary A (no efq). So `⟦.bot⟧ ≤ ⟦A⟧` does NOT hold in general. The GHA has no bottom element -- only `⊤ = ⟦⊤⟧`.

**For IPL**: `⟦.bot⟧` IS the bottom of the HA. The `propHeytingOfIPL` instance proves `bot_le` using efq, establishing `⟦.bot⟧ ≤ ⟦A⟧` for all A.

**For CPL**: `⟦.bot⟧` IS the bottom of the BA (inherited from HA).

This is exactly the three-tier behavior we need.

---

## C. Dedekind-MacNeille Completion

### C.1 Why It's Needed

The MPL completeness theorem needs to state: "valid in all Heyting algebras (with unrestricted bot_val)". But the Lindenbaum algebra for MPL is only a GHA, not an HA. We need to promote GHA -> HA to close the completeness argument.

The Dedekind-MacNeille completion provides this: for any GHA, its D-M completion is a HeytingAlgebra (in fact a complete Heyting algebra), and the embedding preserves GHA operations (inf, sup, himp, top).

### C.2 Mathlib Status

**Mathlib does NOT have**:
- `DedekindMacNeilleCompletion` (confirmed via loogle search: zero results)
- A general "closeds of a closure operator form a CompleteLattice" instance
- `GeneralizedHeytingHom` (confirmed: not in Mathlib)

**Mathlib DOES have**:
- `ClosureOperator` (in `Mathlib.Order.Closure`)
- `ClosureOperator.IsClosed` and related API
- `GaloisConnection` and `GaloisConnection.closureOperator`
- `HeytingHom` (in `Mathlib.Order.Heyting.Hom`) -- NEW since xcthulhu wrote his code
- `completeLatticeOfSup` -- construct CompleteLattice from a sSup operation

### C.3 xcthulhu's DedekindMacneille.lean (418 lines)

Structure:
1. **CompleteLattice on Closeds** (~110 lines): Proves closeds of any closure operator on `Set α` form a complete lattice. This is custom and not in Mathlib.
2. **D-M Galois Connection** (~10 lines): `DedekindMacNeilleConnection α` -- the standard upper/lower bounds adjunction.
3. **D-M Closure Operator** (~5 lines): `DedekindMacNeilleClosureOperator α` from the Galois connection.
4. **D-M Completion type** (~3 lines): `abbrev DedekindMacNeilleCompletion α := (DedekindMacNeilleClosureOperator α).Closeds`.
5. **LinearOrder for linearly ordered α** (~60 lines): If α is linear, completion is linear.
6. **Order embedding coe'** (~20 lines): `α ↪o DedekindMacNeilleCompletion α`.
7. **HeytingAlgebra on completion of GHA** (~100 lines): The key result. Defines `himp` on closed sets and proves `le_himp_iff`.
8. **Coe lemmas** (~80 lines): `coe_inf`, `coe_sup`, `coe_himp`, `coe_top` -- showing the embedding preserves operations.
9. **Universal property** (~30 lines): Extension theorem.

### C.4 Dependencies

xcthulhu's `DedekindMacneille.lean` depends on:
- `Mathlib.Order.Heyting.Basic` -- for GHA, HA
- `Mathlib.Order.Closure` -- for ClosureOperator
- `Mathlib.SetTheory.Cardinal.Aleph` -- (probably only for universe issues)

It does NOT depend on any of the `ForMathlib/Order/` files (Ideal, PFilter, etc.). Those are used by the PrimeSeparator which is used elsewhere but not by the completeness proof.

### C.5 What Needs Porting

| File | Lines | Needed For | Mathlib Overlap |
|------|-------|------------|-----------------|
| `DedekindMacneille.lean` | 418 | MPL completeness | None -- must port entirely |
| `ForMathlib/Order/Heyting/Hom.lean` | 310 | Extension.toGeneralizedHeytingHom | Partial -- `HeytingHom` is now in Mathlib, but `GeneralizedHeytingHom` is not |

The `ForMathlib/Order/Heyting/Hom.lean` defines:
- `HImpHom` (Heyting implication homomorphism)
- `HImpHomClass`
- `GeneralizedHeytingHom` (lattice hom + himp hom)
- `GeneralizedHeytingHomClass`
- `HeytingHom` (GHA hom + map_bot)
- `HeytingHomClass`

Since Mathlib now has `HeytingHom` and `HeytingHomClass`, the `HeytingHom` portion is already upstream. But `GeneralizedHeytingHom` is NOT in Mathlib and IS needed by the completeness proof (for the `Extension.toGeneralizedHeytingHom` used in the Hom section at the end of Heyting.lean).

**However**: The Hom section of Heyting.lean is about theory extensions, not about the core completeness proof. The core completeness theorems (`Theory.complete`, `MPL.complete`, `IPL.complete`, `CPL.complete`) do NOT use `GeneralizedHeytingHom`. So for the initial completeness PR, we can skip the Hom section entirely.

### C.6 Does D-M Completion Preserve JohanssonAlgebra Structure?

Yes. The D-M completion of a GHA gives a HeytingAlgebra. If we have a JohanssonAlgebra (GHA + designated_bot), the D-M completion is an HA with `designated_bot_DM := coe' designated_bot`. The key property is:

- `coe'` preserves inf, sup, himp (proved in xcthulhu's `coe_inf`, `coe_sup`, `coe_himp`)
- `coe'` preserves top (proved in `coe_top`)
- The promoted `designated_bot_DM = coe' designated_bot` is just a regular element of the HA

So yes, the JohanssonAlgebra structure is preserved in the sense that the canonical valuation lifts correctly through the D-M embedding.

---

## D. Soundness (Already Exists, Needs Refactoring)

### D.1 Current State

`Algebra/Soundness.lean` (264 lines) proves:
- `min_alg_axiom_sound`: Each MinPropAxiom is GHAValid
- `int_alg_axiom_sound`: Each IntPropAxiom is HAValid
- `prop_alg_axiom_sound`: Each PropositionalAxiom is BAValid
- `min_alg_soundness` / `int_alg_soundness` / `prop_alg_soundness`: Derivation-level soundness
- `min_alg_soundness_derivable` / `int_alg_soundness_derivable` / `prop_alg_soundness_derivable`: Closed-context soundness

### D.2 Changes with JohanssonAlgebra Typeclass

If we introduce `JohanssonAlgebra`, the soundness proofs simplify slightly:

**Before** (loose bot_val):
```lean
theorem min_alg_axiom_sound {phi} (h : MinPropAxiom phi) : GHAValid phi := by
  intro H _ v bot_val
  cases h with ...
```

**After** (typeclass):
```lean
theorem min_alg_axiom_sound {phi} (h : MinPropAxiom phi) : JValid phi := by
  intro H _ v
  cases h with ...
```

The individual case proofs are identical -- they never use `bot_val` because MinPropAxiom has no efq case. The only difference is that `bot_val` is now `JohanssonAlgebra.designated_bot` and doesn't need to be explicitly named.

**If we keep loose bot_val**: No changes needed to soundness at all.

### D.3 Refactored Signatures (Typeclass Style)

```lean
-- JValid = valid in all Johansson algebras = MPL
theorem min_alg_axiom_sound {phi} (h : MinPropAxiom phi) : JValid phi

-- HAValid = valid in all Heyting algebras = IPL
theorem int_alg_axiom_sound {phi} (h : IntPropAxiom phi) : HAValid phi

-- BAValid = valid in all Boolean algebras = CPL
theorem prop_alg_axiom_sound {phi} (h : PropositionalAxiom phi) : BAValid phi
```

---

## E. Completeness Theorems -- Exact Specifications

### E.1 With Loose bot_val (Recommended for Initial PR)

#### General Theory Completeness

```lean
/-- Algebraic completeness for an arbitrary theory T.
A proposition is derivable from T iff it evaluates to top under every HA
valuation that validates T (with unrestricted bot_val).

This uses the Dedekind-MacNeille completion to promote the Lindenbaum GHA to an HA. -/
theorem Theory.algebraic_complete {T : Theory Atom} [Inhabited Atom]
    {A : PL.Proposition Atom} :
    DerivableIn T A <->
    forall {H : Type*} [HeytingAlgebra H] {v : Atom -> H} (bot_val : H),
      (forall B in T, AlgEvaluate v bot_val B = top) -> AlgEvaluate v bot_val A = top
```

#### MPL Completeness

```lean
/-- MPL algebraic completeness: derivable in minimal logic iff valid in all
Heyting algebras with unrestricted bot_val. -/
theorem MPL.algebraic_complete [Inhabited Atom] {A : PL.Proposition Atom} :
    DerivableIn MPL A <->
    forall {H : Type*} [HeytingAlgebra H] {v : Atom -> H} (bot_val : H),
      AlgEvaluate v bot_val A = top
```

Note: This quantifies over HA with unrestricted `bot_val`, NOT over GHA. The D-M completion is what makes this possible.

#### IPL Completeness

```lean
/-- IPL algebraic completeness: derivable in intuitionistic logic iff valid in all
Heyting algebras with bot_val = bot. -/
theorem IPL.algebraic_complete {A : PL.Proposition Atom} :
    DerivableIn IPL A <->
    forall {H : Type*} [HeytingAlgebra H] {v : Atom -> H},
      AlgEvaluate v (bot : H) A = top
```

#### CPL Completeness

```lean
/-- CPL algebraic completeness: derivable in classical logic iff valid in all
Boolean algebras with bot_val = bot. -/
theorem CPL.algebraic_complete {A : PL.Proposition Atom} :
    DerivableIn CPL A <->
    forall {H : Type*} [BooleanAlgebra H] {v : Atom -> H},
      AlgEvaluate v (bot : H) A = top
```

### E.2 With JohanssonAlgebra Typeclass (Future Polish PR)

```lean
theorem MPL.algebraic_complete {A} :
    DerivableIn MPL A <->
    forall {H} [JohanssonAlgebra H] {v : Atom -> H}, AlgEvaluate v A = top

-- Note: this quantifies over JohanssonAlgebra, not just HeytingAlgebra!
-- The D-M completion promotes GHA -> HA -> JohanssonAlgebra (with designated_bot := bot)
-- This is a stronger statement: valid in ALL j-algebras iff derivable in MPL.
```

### E.3 Proof Architecture

```
1. Define canonical valuation:
   canonicalV : Atom -> Quotient T.propositionSetoid
   canonicalV x := ⟦.atom x⟧
   bot_val := ⟦.bot⟧

2. Truth Lemma (on Lindenbaum GHA):
   canonicalV_spec : AlgEvaluate canonicalV ⟦.bot⟧ phi = ⟦phi⟧
   -- by induction on phi
   -- .atom case: unfold
   -- .bot case: unfold  (THIS IS THE NEW CASE)
   -- .imp case: mk_himp_mk
   -- .and case: mk_inf_mk
   -- .or case: mk_sup_mk

3. Lindenbaum completeness:
   lindenbaum_complete : canonicalV ⊨ A <-> DerivableIn T A
   -- Unfold PValid: ⟦A⟧ = top
   -- By derivable_iff_equiv_top

4. Theory validity:
   tValid_canonicalV : canonicalV ⊨ T
   -- Each axiom B in T: DerivableIn T B (by ax), hence ⟦B⟧ = top

5. For MPL (general T completeness):
   -- Need to promote from GHA to HA for the right-to-left direction
   canonicalVDM : Atom -> DedekindMacNeilleCompletion (Quotient T.propositionSetoid)
   canonicalVDM x := coe' (canonicalV x)
   -- bot_val_DM := coe' ⟦.bot⟧

   canonicalVDM_spec : AlgEvaluate canonicalVDM (coe' ⟦.bot⟧) phi = coe' ⟦phi⟧
   -- Uses coe_inf, coe_sup, coe_himp
   -- NEW: .bot case uses coe' directly

   tValid_canonicalVDM : canonicalVDM ⊨ T
   -- Lifts from tValid_canonicalV

6. Theory.complete :
   -- Forward: soundness (DerivableIn.sound')
   -- Backward: instantiate with canonicalVDM, use injectivity of coe'
```

### E.4 Connecting to Hilbert System

The completeness theorems above use `DerivableIn T A` which is the ND-level derivability. The equivalence to the Hilbert system's `Derivable Axioms phi` is established in `NaturalDeduction/Equivalence.lean`:

```lean
hilbert_iff_nd_min : Derivable MinPropAxiom phi <-> DerivableIn MPL phi
hilbert_iff_nd_int : Derivable IntPropAxiom phi <-> DerivableIn IPL phi
hilbert_iff_nd_cl  : Derivable PropositionalAxiom phi <-> DerivableIn CPL phi
```

So the Hilbert-level completeness theorems are immediate corollaries:

```lean
theorem Hilbert.MPL.algebraic_complete {A} :
    Derivable MinPropAxiom A <->
    forall {H} [HA H] {v} (bot_val), AlgEvaluate v bot_val A = top :=
  hilbert_iff_nd_min.trans MPL.algebraic_complete

-- Similarly for IPL and CPL
```

---

## F. Conservative Extension Results

### F.1 IPL Conservative Over MPL for Bot-Free Formulas

**Statement**: If a formula `A` does not contain `.bot`, and `A` is valid in all HAs with `bot_val = bot`, then `A` is valid in all HAs with unrestricted `bot_val`.

```lean
/-- A proposition is bot-free if it contains no occurrence of .bot. -/
def Proposition.isBotFree : PL.Proposition Atom -> Bool
  | .atom _ => true
  | .bot => false
  | .imp a b => a.isBotFree && b.isBotFree
  | .and a b => a.isBotFree && b.isBotFree
  | .or a b => a.isBotFree && b.isBotFree

/-- For bot-free formulas, AlgEvaluate is independent of bot_val. -/
theorem AlgEvaluate_botFree_independent {phi : PL.Proposition Atom}
    (hbf : phi.isBotFree = true)
    [GeneralizedHeytingAlgebra H] (v : Atom -> H) (b1 b2 : H) :
    AlgEvaluate v b1 phi = AlgEvaluate v b2 phi := by
  induction phi with
  | atom _ => rfl
  | bot => simp at hbf
  | imp a b iha ihb => simp [AlgEvaluate, iha ..., ihb ...]
  | and a b iha ihb => simp [AlgEvaluate, iha ..., ihb ...]
  | or a b iha ihb => simp [AlgEvaluate, iha ..., ihb ...]

/-- IPL is a conservative extension of MPL for bot-free formulas:
if DerivableIn IPL A and A is bot-free, then DerivableIn MPL A. -/
theorem ipl_conservative_over_mpl {A : PL.Proposition Atom}
    (hbf : A.isBotFree = true) :
    DerivableIn IPL A -> DerivableIn MPL A := by
  -- From IPL completeness: DerivableIn IPL A <-> HAValid A (with bot = bot)
  -- From MPL completeness: DerivableIn MPL A <-> GHAValid A (with all bot_val)
  -- For bot-free A: HAValid A (with bot = bot) implies GHAValid A (with all bot_val)
  --   because AlgEvaluate is independent of bot_val for bot-free formulas
  ...
```

This follows directly from the algebraic completeness results and `AlgEvaluate_botFree_independent`.

### F.2 Glivenko's Theorem (CPL Conservative Over IPL for Double-Negation-Stable Formulas)

```lean
/-- Glivenko's theorem: if A is classically derivable, then ¬¬A is
intuitionistically derivable. -/
theorem glivenko {A : PL.Proposition Atom} :
    DerivableIn CPL A -> DerivableIn IPL (¬¬A)
```

This is a deeper result that may not follow purely from algebraic completeness. The algebraic proof would require showing that for any HA H and valuation v, `¬¬(AlgEvaluate v bot A) = top` whenever `A` is BA-valid. This uses the embedding of HA into its Boolean envelope.

**Recommendation**: Defer Glivenko to a separate task. The bot-free conservative extension is the natural algebraic corollary.

### F.3 Exact Signatures

```lean
-- Conservative extension (direct algebraic corollary)
theorem ipl_conservative_over_mpl {A : PL.Proposition Atom}
    (hbf : A.isBotFree = true) :
    DerivableIn IPL A -> DerivableIn MPL A

-- Converse is always true by theory monotonicity
theorem mpl_derivable_implies_ipl {A : PL.Proposition Atom} :
    DerivableIn MPL A -> DerivableIn IPL A
-- follows from MPL <= IPL (empty theory subset)

-- Similarly for the Hilbert system
theorem Hilbert.ipl_conservative_over_mpl {A : PL.Proposition Atom}
    (hbf : A.isBotFree = true) :
    Derivable IntPropAxiom A -> Derivable MinPropAxiom A
```

---

## G. Compatibility with Existing Code

### G.1 Impact on Modal/Temporal/Bimodal

**None** if we keep backward compatibility with `AlgEvaluate v bot_val phi`.

If we introduce `JohanssonAlgebra`, we would need to:
1. Add `import Cslib.Logics.Propositional.Semantics.Algebra.JohanssonAlgebra` to modal files that use `AlgEvaluate`
2. Update call sites from `AlgEvaluate v bot_val` to `AlgEvaluate v`

Currently, the only files using `AlgEvaluate` are:
- `Semantics/Algebra.lean` (definition)
- `Semantics/Algebra/Soundness.lean` (soundness proofs)
- `Semantics/Algebra/Bridge.lean` (bridge to Bool/Prop evaluators)

No modal/temporal/bimodal files use `AlgEvaluate` yet. So the impact is zero.

### G.2 Impact on Kripke Completeness

None. The Kripke completeness proofs use `Evaluate` (Prop-valued), not `AlgEvaluate`. The algebraic completeness proofs are independent.

The bridge lemma `propEvaluateEq` connects the two: `Evaluate v phi <-> AlgEvaluate (fun a => v a) False phi`. Once algebraic completeness is proved, this bridge can be used to derive Kripke completeness as a corollary of algebraic completeness (though the existing direct Kripke proofs are already sorry-free).

### G.3 Impact on Bridge.lean

`Bridge.lean` currently uses:
```lean
AlgEvaluate (fun a => v a) False phi  -- Prop, bot_val = False
AlgEvaluate (fun a => v a) false phi  -- Bool, bot_val = false
```

With `JohanssonAlgebra`, these become:
```lean
-- Prop already has HeytingAlgebra, so JohanssonAlgebra instance gives designated_bot = False
AlgEvaluate (fun a => v a) phi  -- bot_val = designated_bot = False

-- Bool already has BooleanAlgebra, so designated_bot = false
AlgEvaluate (fun a => v a) phi  -- bot_val = designated_bot = false
```

The bridge lemmas would need minor signature updates but the proofs would be simpler.

---

## H. File Structure and Dependency Graph

### H.1 New Files to Create

| File | Est. Lines | Purpose | Dependencies |
|------|-----------|---------|--------------|
| `Semantics/Algebra/DedekindMacNeille.lean` | ~420 | D-M completion (ported from xcthulhu) | Mathlib.Order.Heyting.Basic, Mathlib.Order.Closure |
| `Semantics/Algebra/Lindenbaum.lean` | ~300 | Lindenbaum quotient + GHA/HA/BA instances | NaturalDeduction/Basic, Algebra.lean |
| `Semantics/Algebra/Completeness.lean` | ~200 | Canonical valuation + truth lemma + completeness | Lindenbaum.lean, DedekindMacNeille.lean, Soundness.lean |
| `Semantics/Algebra/Conservative.lean` | ~80 | Conservative extension results | Completeness.lean |

**Optional (polish PR)**:
| `Semantics/Algebra/JohanssonAlgebra.lean` | ~30 | JohanssonAlgebra typeclass + HA instance | Mathlib.Order.Heyting.Basic |

### H.2 Existing Files to Modify

| File | Changes | Est. Lines Changed |
|------|---------|-------------------|
| `Semantics/Algebra.lean` | Add `JohanssonAlgebra` import (if typeclass PR), docstring updates | ~5 |
| `Semantics/Algebra/Soundness.lean` | Only if typeclass PR: update signatures | ~20 |
| `Semantics/Algebra/Bridge.lean` | Only if typeclass PR: update signatures | ~10 |

### H.3 Dependency Graph

```
                     Mathlib.Order.Heyting.Basic
                              |
                     Mathlib.Order.Closure
                              |
               DedekindMacNeille.lean (NEW, ~420 lines)
                              |
                              |         NaturalDeduction/Basic.lean (EXISTS)
                              |                    |
                              |         Algebra.lean (EXISTS)
                              |                    |
                              |         Soundness.lean (EXISTS)
                              |                   /
                              |                  /
                     Lindenbaum.lean (NEW, ~300 lines)
                              |
                     Completeness.lean (NEW, ~200 lines)
                              |
                     Conservative.lean (NEW, ~80 lines)
```

### H.4 Estimated Total

| Component | Lines | Status |
|-----------|-------|--------|
| DedekindMacNeille port | ~420 | Port from xcthulhu (mechanical) |
| Lindenbaum algebra | ~300 | Adapt from xcthulhu (small changes for primitive bot) |
| Completeness theorems | ~200 | Adapt from xcthulhu (~15 lines of changes for .bot case) |
| Conservative extension | ~80 | New (straightforward corollary) |
| **Total new code** | **~1000** | |
| Soundness refactoring | ~20 | Only if typeclass PR |
| Bridge refactoring | ~10 | Only if typeclass PR |

### H.5 Phasing Recommendation

**Phase 1** (PR-ready, ~420 lines): Port `DedekindMacNeille.lean`
- Pure order theory, no logic content
- Can be reviewed independently
- Could be submitted as a ForMathlib PR

**Phase 2** (PR-ready, ~500 lines): Lindenbaum + Completeness
- `Lindenbaum.lean`: quotient, PO, Lattice, GHA, HA, BA instances
- `Completeness.lean`: canonical valuation, truth lemma, completeness theorems
- Depends on Phase 1

**Phase 3** (PR-ready, ~80 lines): Conservative Extension
- `Conservative.lean`: bot-free independence lemma + conservative extension
- Depends on Phase 2

**Phase 4** (Optional polish, ~60 lines): JohanssonAlgebra Typeclass
- Introduce typeclass, refactor AlgEvaluate and Soundness
- Independent timing, but logically depends on Phase 2 being complete

---

## I. Key Differences Between xcthulhu and CSLib Approaches

| Aspect | xcthulhu | CSLib (ours) |
|--------|----------|--------------|
| Bot representation | `[Bot Atom]`, `atom bot` | Primitive `.bot` constructor |
| Atom constraint | `[DecidableEq Atom]` | `[DecidableEq Atom]` (same) |
| Inhabitedness | `[Inhabited Atom]` often needed | Less often needed (bot is free) |
| Proof system | Natural Deduction only | ND + Hilbert + bridge |
| Sequent type | `Ctx Atom x Proposition Atom` | Same (via NaturalDeduction/Basic) |
| DerivableIn | Via `InferenceSystem` class | Same |
| AlgEvaluate | `Valuation.interp` (no bot case) | `AlgEvaluate v bot_val` (has bot case) |
| Bot in Lindenbaum | `propBot : bot := ⟦atom bot⟧` (needs `[Bot Atom]`) | `⟦.bot⟧` (always available) |
| Theories | `MPL, IPL, CPL` as sets | Same names, same definitions |
| Completeness stmt | Via `Valuation.PValid`/`TValid` | Via `AlgEvaluate ... = top` directly |

### Key Adaptations for CSLib

1. **Add `.bot` case to `canonicalV_spec`**: One new line `| .bot => simp [AlgEvaluate, canonicalV]`
2. **Add `.bot` case to `canonicalVDM_spec`**: One new line using `coe'`
3. **Remove `[Bot Atom]` requirements**: Our `.bot` is primitive, so `propBot` / `propHeyting` etc. don't need `[Bot Atom]`
4. **Connect to Hilbert system**: Corollaries via `hilbert_iff_nd_min/int/cl`
5. **Use `bot_val` parameter instead of `Valuation.interp`**: Mechanical signature change

---

## J. Risk Assessment

### Low Risk
- DedekindMacNeille port: mechanical, well-tested code
- Lindenbaum GHA instance: close translation of xcthulhu
- Conservative extension: simple corollary

### Medium Risk
- HeytingAlgebra instance (`propHeyting`): needs `efqOfIPLHyp` adaptation
- BooleanAlgebra instance (`propBoolean`): needs `dneOfCPL` adaptation
- `Inhabited Atom` requirements: may need to thread through more carefully

### Low Risk of Sorry
The entire proof architecture is constructive and well-understood. xcthulhu's code compiles without sorry for all core completeness. The only risk is if CSLib's ND API has subtle differences requiring workarounds. Mitigation: the ND/Hilbert equivalence bridge is already proven.

---

## K. References

- Johansson, I. (1937). "Der Minimalkalkul, ein reduzierter intuitionistischer Formalismus." Compositio Mathematica, 4, 119-136.
- Rasiowa, H. (1974). An Algebraic Approach to Non-Classical Logics. North-Holland.
- Rasiowa, H. & Sikorski, R. (1963). The Mathematics of Metamathematics. PWN.
- Citkin, A. (2021). "On Finitely-Generated Johansson Algebras." BLAST 2021.
- xcthulhu (Thomas Waring). CSLib branch `488309e3` -- Heyting.lean (completeness), DedekindMacneille.lean (order completion).
- BimodalLogic repo: `Metalogic/Algebraic/BooleanStructure.lean` (sorry-free BA on Lindenbaum).
