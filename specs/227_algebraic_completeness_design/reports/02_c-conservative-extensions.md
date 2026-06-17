# Research Report: Conservative Extensions and Kripke-Algebraic Bridge

**Task**: 227 -- Algebraic completeness design (Teammate C)
**Session**: sess_1750130000_research227
**Date**: 2026-06-17
**Focus**: Conservative extension theorems, Glivenko's theorem, Kripke-algebraic bridge

## 1. Conservative Extension: IPL over MPL

### 1.1 Statement and Meaning

"IPL is a conservative extension of MPL for bot-free formulas" means:

> If a formula phi that does not contain the `bot` constructor is derivable in IPL
> (i.e., using `IntPropAxiom` which includes `efq`), then phi is already derivable in MPL
> (using only `MinPropAxiom`, without `efq`).

Equivalently in algebraic terms: if phi is bot-free and `HAValid phi` (valid in all Heyting
algebras with `bot_val = bot`), then `GHAValid phi` (valid in all GHAs with arbitrary `bot_val`).

The argument is straightforward: if phi never mentions `bot`, then `AlgEvaluate v bot_val phi`
does not depend on `bot_val` at all -- the `bot` case of the recursion is never reached.
Therefore the value of `bot_val` is irrelevant, and validity over all HAs with `bot_val = bot`
implies validity over all GHAs with arbitrary `bot_val`.

### 1.2 CSLib Does NOT Have a Bot-Free Predicate

Searched `Cslib/Logics/Propositional/` for `IsBotFree`, `botFree`, `bot_free`, `BotFree`,
`NoBot`, `noBot` -- no results. The only `bot_free` in CSLib is in
`Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/HintikkaPoint.lean` (a field in
`BXPoint`, not a reusable predicate).

A `IsBotFree` predicate is needed for the conservative extension theorem. It would be a simple
inductive proposition on `PL.Proposition`:

```lean
/-- A proposition is bot-free if it does not contain the `bot` constructor. -/
def Proposition.IsBotFree : PL.Proposition Atom -> Prop
  | .atom _ => True
  | .bot => False
  | .imp a b => a.IsBotFree /\ b.IsBotFree
  | .and a b => a.IsBotFree /\ b.IsBotFree
  | .or a b => a.IsBotFree /\ b.IsBotFree
```

Or equivalently as a `Bool`-valued function with a bridge lemma.

### 1.3 Key Lemma: Bot-Free Evaluation Independence

The core algebraic lemma underlying the conservative extension is:

```lean
/-- If phi is bot-free, then AlgEvaluate does not depend on bot_val. -/
theorem AlgEvaluate_botFree_independent
    {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom -> H) (b1 b2 : H) (phi : PL.Proposition Atom)
    (hbf : phi.IsBotFree) :
    AlgEvaluate v b1 phi = AlgEvaluate v b2 phi
```

Proof: by structural induction on phi. The `bot` case is ruled out by `hbf`. All other cases
recurse and use the inductive hypothesis, since `imp`, `and`, `or` only combine sub-evaluations
and `atom` doesn't use `bot_val`.

### 1.4 Conservative Extension Theorem Signatures

**Semantic version (algebraic)**:
```lean
/-- IPL is a conservative extension of MPL for bot-free formulas:
    if phi is bot-free and HAValid phi, then GHAValid phi. -/
theorem HAValid_implies_GHAValid_of_botFree
    {phi : PL.Proposition Atom}
    (hbf : phi.IsBotFree) (h : HAValid phi) : GHAValid phi
```

Proof sketch: Given any GHA `H`, assignment `v`, and `bot_val`, we need
`AlgEvaluate v bot_val phi = top`. Since `phi` is bot-free,
`AlgEvaluate v bot_val phi = AlgEvaluate v bot phi` (by independence lemma).
But `H` as a GHA has `bot` (it has a lattice bottom from `OrderBot`... actually
`GeneralizedHeytingAlgebra` does NOT have `Bot` in general).

**Important subtlety**: `GeneralizedHeytingAlgebra` does not guarantee a bottom element.
So we cannot simply substitute `bot_val = bot`. Instead, the proof works differently:

Since `phi` is bot-free, `AlgEvaluate v bot_val phi = AlgEvaluate v bot_val' phi` for ANY
two values of `bot_val`. In particular, pick `bot_val' = bot_val` in a Heyting algebra
`H' = H` where we adjoin a bottom. But this is awkward because `H` might not be a HA.

**Better approach**: State the theorem purely syntactically via the proof systems:

```lean
/-- If phi is bot-free and Derivable IntPropAxiom phi, then Derivable MinPropAxiom phi. -/
theorem Derivable_MinPropAxiom_of_IntPropAxiom_botFree
    {phi : PL.Proposition Atom}
    (hbf : phi.IsBotFree) (h : Derivable IntPropAxiom phi) :
    Derivable MinPropAxiom phi
```

This is the classical proof-theoretic conservative extension and requires different
machinery (e.g., proof transformation that eliminates uses of `efq`).

**Algebraic approach via HA validity**: The cleaner algebraic version is:

```lean
/-- For bot-free formulas, validity in all HAs (bot_val = bot) implies validity
    in all HAs with arbitrary bot_val. -/
theorem HAValid_botFree_implies_arbitrary_bot
    {phi : PL.Proposition Atom}
    (hbf : phi.IsBotFree) (h : HAValid phi) :
    forall (H : Type*) [HeytingAlgebra H] (v : Atom -> H) (bot_val : H),
      AlgEvaluate v bot_val phi = top
```

This is provable using `AlgEvaluate_botFree_independent`: given any HA `H`, any `v`, and
any `bot_val`, we have `AlgEvaluate v bot_val phi = AlgEvaluate v (bot : H) phi = top`
(by independence and `h`). This works because `HeytingAlgebra` does have `Bot`.

### 1.5 What About Formulas That Mention bot?

For formulas that DO mention `bot`, the conservative extension fails. Counter-example:
`bot -> A` (i.e., `efq`) is `IntPropAxiom` but not `MinPropAxiom`. No weaker result
exists in general -- the presence of `bot` in the formula is what makes `efq` relevant.

However, there is a **conditional** result: if a formula phi mentioning bot is derivable in
IPL using only the bot-free fragment of the premises, then there may be a way to eliminate
the efq uses. This is more subtle and likely not worth pursuing for this task.

## 2. Glivenko's Theorem

### 2.1 Statement

**Glivenko's theorem** (1929): For any propositional formula phi,

> CPL derives phi if and only if IPL derives not-not-phi.

In CSLib notation:
```lean
theorem glivenko :
    Derivable PropositionalAxiom phi <->
    Derivable IntPropAxiom (neg (neg phi))
```

where `neg phi = phi.imp .bot` and `neg (neg phi) = (phi.imp .bot).imp .bot`.

### 2.2 Algebraic Proof Strategy

The algebraic proof of Glivenko's theorem proceeds via the **regular elements** of a
Heyting algebra:

1. **Mathlib has `Heyting.Regular`**: The subtype `{ a : alpha // a^^compl^^compl = a }`
   where `compl a = a -> bot` in the Heyting algebra. Key Mathlib declarations:
   - `Heyting.Regular.lattice : Lattice (Heyting.Regular alpha)` -- lattice structure
   - `Heyting.Regular.instBooleanAlgebra : BooleanAlgebra (Heyting.Regular alpha)` -- BA structure
   - `BooleanAlgebra.ofRegular` -- construct BA from regularity condition

2. **The double-negation map** `a |-> a^^compl^^compl` is a surjective lattice homomorphism
   from `H` onto `Heyting.Regular H`, and `Heyting.Regular H` is a BooleanAlgebra.

3. **Glivenko via algebras**: phi is CPL-valid iff `AlgEvaluate v bot phi = top` in all BAs.
   By completeness, this is equivalent to `AlgEvaluate v bot phi = top` in all
   `Heyting.Regular H`. The double-negation embedding then gives: for all HAs `H`,
   `AlgEvaluate v bot (neg (neg phi)) = top`.

### 2.3 Direct Proof Strategy (Without Full Algebraic Completeness)

Since we do not yet have algebraic completeness, an alternative is a **syntactic proof**:

**Forward direction** (CPL derives phi => IPL derives not-not-phi): This follows from the
fact that `not-not-phi -> phi` (DNE) is classical but `phi -> not-not-phi` is intuitionistic.
So if CPL derives phi, we need to show IPL derives not-not-phi. This is done by showing that
the double-negation translation preserves derivability.

**Backward direction** (IPL derives not-not-phi => CPL derives phi): CPL extends IPL, so
if IPL derives not-not-phi, then CPL derives not-not-phi. CPL also derives `not-not-phi -> phi`
(DNE/Peirce). By modus ponens, CPL derives phi.

### 2.4 Interaction with Primitive bot

Glivenko's theorem works naturally with primitive bot because:
- `neg phi = phi -> bot` uses the primitive `bot` constructor
- `not-not-phi = (phi -> bot) -> bot` is a well-formed `PL.Proposition`
- The algebraic semantics maps `bot` to `bot_val`, and for IPL/CPL both use `bot_val = bot`
- The Heyting complement `a^^compl = a himp bot` matches `neg` exactly

No special handling of primitive bot is needed for Glivenko -- it's one of the places
where primitive bot simplifies rather than complicates things.

### 2.5 Lean 4 Formalization Status

No existing Lean 4 formalization of Glivenko's theorem was found in:
- Mathlib (searched via `lean_local_search` for "Glivenko", "DoubleNegation" -- no results)
- CSLib (no results)
- BimodalLogic (no results)

The Trufas 2024 thesis (arXiv:2410.23765) formalizes IPL in Lean 4 but does not include
Glivenko. This would be a novel contribution.

### 2.6 Recommended Theorem Signatures

```lean
/-- Glivenko's theorem (forward): classical derivability implies intuitionistic
    derivability of the double negation. -/
theorem glivenko_forward {phi : PL.Proposition Atom}
    (h : Derivable PropositionalAxiom phi) :
    Derivable IntPropAxiom (neg (neg phi))

/-- Glivenko's theorem (backward): intuitionistic derivability of the double
    negation implies classical derivability. -/
theorem glivenko_backward {phi : PL.Proposition Atom}
    (h : Derivable IntPropAxiom (neg (neg phi))) :
    Derivable PropositionalAxiom phi

/-- Glivenko's theorem (iff): phi is classically derivable iff not-not-phi is
    intuitionistically derivable. -/
theorem glivenko_iff {phi : PL.Proposition Atom} :
    Derivable PropositionalAxiom phi <->
    Derivable IntPropAxiom (neg (neg phi))
```

**Algebraic Glivenko** (requires completeness):
```lean
/-- Algebraic Glivenko: BAValid phi iff HAValid (neg (neg phi)). -/
theorem glivenko_algebraic {phi : PL.Proposition Atom} :
    BAValid phi <-> HAValid (neg (neg phi))
```

## 3. Bridge Between Kripke and Algebraic Semantics

### 3.1 The UpperSet Construction

The standard bridge between Kripke and algebraic semantics for propositional logic uses
the **upset lattice** of the frame:

Given a Kripke frame `(W, <=)` (a preorder):
- `UpperSet W` is the type of upward-closed subsets of W
- Mathlib provides `UpperSet.completelyDistribLattice : CompletelyDistribLattice (UpperSet W)`
- Since `CompletelyDistribLattice extends BiheytingAlgebra extends HeytingAlgebra`, we get
  `HeytingAlgebra (UpperSet W)` automatically

The Heyting operations on `UpperSet W` are:
- Meet (inf): intersection
- Join (sup): union
- Implication (himp): `S himp T = { w | forall w' >= w, w' in S -> w' in T }`
- Bot: `Set.univ` (the "empty" upper set... actually `UpperSet` has reversed order:
  `Top` = empty set, `Bot` = univ for the lattice structure)

**Important**: `UpperSet` uses **reverse inclusion** as its ordering. So `bot` in the
`UpperSet` lattice is `Set.univ` (the largest upper set), and `top` is the empty set.
This means care is needed when mapping to Kripke semantics.

### 3.2 The botForces <-> bot_val Correspondence

In CSLib's Kripke semantics:
- `IForces v botForces w phi` evaluates phi at world w
- `botForces : World -> Prop` determines where bot is forced

In algebraic semantics on `UpperSet World`:
- The valuation `v_alg : Atom -> UpperSet World` is defined by
  `v_alg(a) = { w | v w a }` (the upper set of worlds where atom a is true)
- The bot value `bot_val : UpperSet World` corresponds to
  `{ w | botForces w }` (the upper set of worlds where bot is forced)

The key bridge lemma would state:

```lean
/-- The Kripke forcing relation corresponds to algebraic evaluation in the
    upset lattice of worlds. -/
theorem IForces_eq_AlgEvaluate_UpperSet
    [Preorder World]
    {v : World -> Atom -> Prop} {botForces : World -> Prop}
    (v_uc : forall {w w'} (p : Atom), w <= w' -> v w p -> v w' p)
    (bf_uc : forall {w w'}, w <= w' -> botForces w -> botForces w')
    (w : World) (phi : PL.Proposition Atom) :
    IForces v botForces w phi <->
    w in (AlgEvaluate
      (fun a => UpperSet.mk { w | v w a } (fun _ _ h => v_uc _ h))
      (UpperSet.mk { w | botForces w } (fun _ _ h => bf_uc h))
      phi : UpperSet World)
```

This is provable by structural induction on phi:
- **atom**: Both sides reduce to `v w a`. Immediate.
- **bot**: Both sides reduce to `botForces w`. Immediate.
- **imp**: `IForces v bf w (phi -> psi)` is `forall w' >= w, IForces v bf w' phi -> IForces v bf w' psi`.
  On the algebraic side, `S himp T = { w | forall w' >= w, w' in S -> w' in T }` for `UpperSet`.
  These match by the inductive hypothesis.
- **and**: `IForces v bf w (phi /\ psi)` = conjunction; algebraic side is `inf` = intersection. Match.
- **or**: `IForces v bf w (phi \/ psi)` = disjunction; algebraic side is `sup` = union. Match.

### 3.3 Connecting Validity Notions

Once the bridge lemma is established:

```lean
/-- Kripke validity implies algebraic validity in the UpperSet algebra. -/
theorem MValid_implies_UpperSet_valid {phi : PL.Proposition Atom}
    (h : MValid phi) (W : Type*) [Preorder W]
    (v : Atom -> UpperSet W) (bot_val : UpperSet W) :
    AlgEvaluate v bot_val phi = top

/-- Algebraic validity in all HAs implies Kripke validity. -/
-- This is the harder direction: need to show UpperSet algebras are "enough"
-- (i.e., every HA embeds into some UpperSet algebra)
```

The converse direction (algebraic validity implies Kripke validity) requires showing that
UpperSet algebras are universal for Heyting algebras. This follows from the representation
theorem: every Heyting algebra embeds into the UpperSet algebra of its prime filter spectrum.
This is a deep result and would be a substantial formalization effort.

### 3.4 What CSLib Already Has

CSLib has `Bridge.lean` connecting `AlgEvaluate` to `Evaluate` (Prop) and `BoolEvaluate`
(Bool), but NOT connecting `AlgEvaluate` to `IForces` (Kripke). The Kripke-algebraic bridge
would be new.

### 3.5 Feasibility Assessment

- **IForces_eq_AlgEvaluate_UpperSet**: Moderate difficulty (~50-80 lines). The main challenge
  is handling the `UpperSet` API correctly (reversed ordering, membership coercions).
- **MValid_implies_UpperSet_valid**: Easy consequence of the bridge lemma.
- **Full equivalence (Kripke validity <-> algebraic validity)**: Hard. Requires representation
  theorem. Recommend deferring to a future task.

## 4. Subsumption Between Axiom Tiers

### 4.1 Existing Results

CSLib has explicit subsumption theorems in `ProofSystem/Axioms.lean`:

```
MinPropAxiom.toIntPropAxiom : MinPropAxiom phi -> IntPropAxiom phi
IntPropAxiom.toPropAxiom : IntPropAxiom phi -> PropositionalAxiom phi
```

The axiom hierarchy is:
- `MinPropAxiom` (8 constructors): implyK, implyS, andI, andE1, andE2, orI1, orI2, orE
- `IntPropAxiom` (9 constructors): all of MinPropAxiom + efq
- `PropositionalAxiom` (10 constructors): all of IntPropAxiom + peirce

### 4.2 Mapping to Algebra Hierarchy

| Axiom tier | Algebra tier | Key axiom difference | Algebra property |
|------------|-------------|---------------------|------------------|
| `MinPropAxiom` | GHA (JohanssonAlgebra) | -- | `a himp b` exists |
| `IntPropAxiom` | HeytingAlgebra | + efq: `bot -> phi` | + `bot_le : bot <= a` |
| `PropositionalAxiom` | BooleanAlgebra | + peirce: `((p->q)->p)->p` | + `a \/ a^^compl = top` |

The soundness results in `Algebra/Soundness.lean` demonstrate this mapping:
- `min_alg_axiom_sound`: MinPropAxiom -> GHAValid
- `int_alg_axiom_sound`: IntPropAxiom -> HAValid (delegates to min_alg_axiom_sound + `bot_le` for efq)
- `prop_alg_axiom_sound`: PropositionalAxiom -> BAValid (delegates to int_alg_axiom_sound + BA for peirce)

### 4.3 Missing: Algebraic Validity Subsumption

The soundness file does NOT state the subsumption between validity notions:

```lean
-- These would be useful:
theorem GHAValid_implies_HAValid (h : GHAValid phi) : HAValid phi
theorem HAValid_implies_BAValid (h : HAValid phi) : BAValid phi
```

The first is immediate: GHAValid quantifies over ALL GHAs with ALL bot_val, so in particular
over all HAs with bot_val = bot. The second follows because every BA is an HA.

## 5. BimodalLogic Conservative Extension Infrastructure

### 5.1 Structure

The BimodalLogic project has a complete conservative extension proof in
`Theories/Bimodal/Metalogic/ConservativeExtension/` (4 files, ~1000 lines total):

| File | Lines | Content |
|------|-------|---------|
| `ExtFormula.lean` | ~353 | Extended formula type `ExtFormula` with `ExtAtom = Atom + Unit`, embedding `embedFormula`, freshness `fresh_not_in_embedFormula_atoms` |
| `ExtDerivation.lean` | ~287 | Extended axioms, derivation trees, `embedAxiom`, `embedDerivation` |
| `Substitution.lean` | ~262 | Substitution `sigma[q -> bot]`, axiom closure, preservation lemmas |
| `Lifting.lean` | ~697 | `liftDerivationWith`, `lift_derivation_qfree` -- the main theorem |

### 5.2 Architecture Pattern

The conservative extension uses the **Goldblatt/BdRV naming argument**:

1. **Extend the language**: `Atom -> ExtAtom = Atom + Unit` (add one fresh atom `q`)
2. **Embed derivations**: `embedDerivation : DerivationTree fc Gamma phi -> ExtDerivationTree fc (Gamma.map embedFormula) (embedFormula phi)`
3. **Substitution closure**: All axiom schemas are closed under substitution `sigma[q -> bot]`
4. **Lift back**: Project extended derivations back to base language via `unembedFormula`

The main theorem is:
```
lift_derivation_qfree : ExtDerivationTree fc (L.map embedFormula) (embedFormula phi) ->
    Nonempty (DerivationTree fc L phi)
```

### 5.3 Relevance to Propositional Conservative Extension

The BimodalLogic infrastructure handles a **modal** conservative extension (adding an
irreflexivity axiom involving a fresh atom). For the propositional IPL-over-MPL case, the
conservative extension is conceptually simpler because it's about formula structure (bot-free)
rather than fresh atoms. However, the BimodalLogic approach could be adapted if we wanted
a proof-transformation-based conservative extension for propositional logic.

**Key difference**: The propositional conservative extension (IPL over MPL for bot-free
formulas) is most naturally proved algebraically (via `AlgEvaluate_botFree_independent`),
not via the Goldblatt naming argument. The naming argument is overkill for this case.

## 6. Recommended Theorems for Implementation

### Priority 1: Conservative Extension (Bot-Free Independence)

```lean
-- New predicate
def Proposition.IsBotFree : PL.Proposition Atom -> Prop

-- Core lemma
theorem AlgEvaluate_botFree_independent
    [GeneralizedHeytingAlgebra H] (v : Atom -> H) (b1 b2 : H)
    (phi : PL.Proposition Atom) (hbf : phi.IsBotFree) :
    AlgEvaluate v b1 phi = AlgEvaluate v b2 phi

-- Conservative extension (HA version)
theorem HAValid_botFree_implies_arbitrary_bot
    (phi : PL.Proposition Atom) (hbf : phi.IsBotFree) (h : HAValid phi) :
    forall (H : Type*) [HeytingAlgebra H] (v : Atom -> H) (bot_val : H),
      AlgEvaluate v bot_val phi = top
```

### Priority 2: Validity Subsumption

```lean
theorem GHAValid_implies_HAValid (h : GHAValid phi) : HAValid phi
theorem HAValid_implies_BAValid (h : HAValid phi) : BAValid phi
```

### Priority 3: Kripke-Algebraic Bridge

```lean
theorem IForces_eq_AlgEvaluate_UpperSet
    [Preorder World] ... :
    IForces v botForces w phi <->
    w in (AlgEvaluate v_alg bot_val_alg phi : UpperSet World)
```

### Priority 4: Glivenko's Theorem (Longer Term)

Best approached after algebraic completeness is available, as the algebraic proof
via `Heyting.Regular` is the most elegant. The syntactic proof is possible but more
involved and less reusable.

## 7. Key Mathlib API for Implementation

| Declaration | Type | Location | Use |
|-------------|------|----------|-----|
| `UpperSet.completelyDistribLattice` | `CompletelyDistribLattice (UpperSet alpha)` | `Order.UpperLower.CompleteLattice` | UpperSet is an HA |
| `Heyting.Regular.instBooleanAlgebra` | `BooleanAlgebra (Heyting.Regular alpha)` | `Order.Heyting.Regular` | Regular elements form BA |
| `Heyting.Regular.lattice` | `Lattice (Heyting.Regular alpha)` | `Order.Heyting.Regular` | Regular elements form lattice |
| `BooleanAlgebra.ofRegular` | `(forall a, IsRegular (a \/ a^^compl)) -> BooleanAlgebra alpha` | `Order.Heyting.Regular` | Construct BA |
| `Order.Frame` | `extends CompleteLattice, HeytingAlgebra` | `Order.CompleteBooleanAlgebra` | Frame = complete HA |
| `himp_eq_top_iff` | `a himp b = top <-> a <= b` | `Order.Heyting.Basic` | Validity = ordering |
| `le_himp_iff` | `a <= b himp c <-> a inf b <= c` | `Order.Heyting.Basic` | Adjunction |
| `bot_le` | `bot <= a` | (HeytingAlgebra) | efq in HA |

## 8. Summary

- **Conservative extension** (IPL over MPL for bot-free formulas) is achievable via a simple
  algebraic independence lemma. CSLib needs a new `IsBotFree` predicate (~10 lines).
- **Glivenko's theorem** is best approached algebraically via `Heyting.Regular` after
  completeness is proved. Mathlib has the necessary BA-on-regular-elements infrastructure.
  No existing Lean 4 formalization of Glivenko was found -- this would be novel.
- **Kripke-algebraic bridge**: `UpperSet World` is a `HeytingAlgebra` via Mathlib's
  `CompletelyDistribLattice` instance. The bridge lemma `IForces <-> AlgEvaluate` is
  straightforward by structural induction. Full Kripke-algebraic equivalence requires a
  representation theorem (deferred).
- **Axiom subsumption** is established at the axiom level but not at the validity level.
  Adding `GHAValid_implies_HAValid` and `HAValid_implies_BAValid` is trivial.
- **BimodalLogic's conservative extension** uses a different approach (fresh atom + substitution)
  that is relevant for modal logics but overkill for the propositional bot-free case.
