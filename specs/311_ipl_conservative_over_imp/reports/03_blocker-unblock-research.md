# Research Report: Unblocking IPL Conservative over IPL(->,%top) (Task 311)

## Problem Statement

Prove: `Derivable IntPropAxiom phi -> IsImpTopOnly phi -> Derivable ImpAxiom phi`

The existing codebase has algebraic completeness for both systems:
- `IPL.hilbert_alg_complete`: `Derivable IntPropAxiom phi <-> HAValid phi` (HeytingAlgebra validity)
- `imp_hilbert_iff`: `IsImpTopOnly phi -> (Derivable ImpAxiom phi <-> HilbertValid phi)` (HilbertAlgebra validity)

So the theorem reduces to: `HAValid phi -> HilbertValid phi` for IsImpTopOnly formulas.

## Two-Step Decomposition (Key Finding)

The existing conservativity infrastructure enables a two-step factorization:

**Step 1** (ALREADY PROVEN): `Derivable IntPropAxiom phi -> Derivable ConjImpAxiom phi` for
IsImpTopOnly formulas.
- `hilbertIplConservativeOverConjImp` proves this for IsOrBotFree formulas
- `IsImpTopOnly_implies_IsOrBotFree` gives the precondition

**Step 2** (THE REMAINING GAP): `Derivable ConjImpAxiom phi -> Derivable ImpAxiom phi` for
IsImpTopOnly formulas.

This reduces the problem from "IPL conservative over IPL(->,top)" to the simpler
"IPL(conj,imp,top) conservative over IPL(->,top)" for imp-top-only formulas.

Algebraically, Step 2 requires: `BrouwerianValid phi -> HilbertValid phi` for IsImpTopOnly phi.
I.e., if phi evaluates to top in every BrouwerianSemilattice (using only himp), then it evaluates
to top in every HilbertAlgebra (using only himp).

## Approach Analysis

### Approach 1: HilbertFilter Embedding (BLOCKED)

**Status**: Blocked -- backward direction of himp preservation fails.

The `HilbertFilter H` construction achieves:
- `CompleteLattice (HilbertFilter H)` -- proven
- `GeneralizedHeytingAlgebra (HilbertFilter H)` -- proven
- `HeytingAlgebra (HilbertFilter H)` -- achievable by adding `Compl F := F => bot` and
  proving `himp_bot` (trivial since `HeytingAlgebra.mk` requires GHA + OrderBot + Compl + himp_bot)

The `principal : H -> HilbertFilter H` map satisfies:
- Injective -- proven (`principal_injective`)
- Order-reversing -- proven (`principal_le_iff`)
- Forward himp: `principal(a => b) <= himpFilter(principal a)(principal b)` -- proven (`principal_le_himp`)
- **Backward himp: `himpFilter(principal a)(principal b) <= principal(a => b)` -- PROVABLY FALSE**

The backward direction fails because `x in himpFilter(principal a)(principal b)` means
"for all y >= x, a <= y implies b <= y", but deriving `a => b <= x` from this requires
meet (inf), which HilbertAlgebras lack.

Even instantiating `HAValid phi` at `HilbertFilter H` with valuation `principal . v` gives
`AlgEvaluate (principal . v) bot phi = top = topFilter`, but `principal_le_algEvaluate`
gives `principal(HilbertEvaluate v phi) <= topFilter` which is trivially true and useless.
The embedding is order-reversing, so HAValid giving top (maximal) in the filter lattice
cannot be used to conclude principal(eval) = bot (minimal), which would give eval = top in H.

### Approach 2: GHA -> HeytingAlgebra Promotion (NOT SUFFICIENT BY ITSELF)

**Status**: The promotion works but doesn't solve the embedding problem.

`HeytingAlgebra.mk` in Mathlib requires `GeneralizedHeytingAlgebra + OrderBot + Compl + himp_bot`.
Since `HilbertFilter H` is a GHA and a CompleteLattice (hence has OrderBot), defining
`Compl F := F => bot` makes it a HeytingAlgebra trivially. The himp operation is inherited
unchanged from the GHA.

This does NOT help with the backward direction of himp preservation for `principal`.

### Approach 3: Proof-Theoretic (BLOCKED by sorry)

**Status**: Blocked -- `cutAdmissibility` in LJ has a sorry.

A cut-free sequent calculus for IPL(->,top) would give the subformula property: any
proof of an imp-top-only sequent uses only imp-top-only formulas. This would show that
no conjunction or disjunction axioms are needed, proving conservativity directly.

The LJ sequent calculus exists in `Cslib/Logics/Propositional/SequentCalculus/LJ/`, but
`cutAdmissibility` (in `CutElimination.lean`) has a sorry.

### Approach 4: Free BrouwerianSemilattice Construction (VIABLE -- RECOMMENDED)

**Status**: Viable but requires new infrastructure.

**Mathematical Construction**: Given a HilbertAlgebra H, construct the free
BrouwerianSemilattice BS(H) as follows:

- **Elements**: Finite multisets (or lists modulo permutation) of elements of H, representing
  formal meets `a1 inf a2 inf ... inf an`.
- **Ordering**: `S <= T` iff for each element `t` of T, there is a Hilbert derivation
  `s1, ..., sm |- t` (using only the K and S axioms and modus ponens from elements of S).
- **Meet**: `S inf T = S union T` (concatenation of multisets).
- **Top**: Empty multiset (represents the empty meet = top).
- **Himp**: `S => T` defined via the adjunction `U inf S <= T iff U <= S => T`.

**Why himp is preserved**: The embedding `eta : H -> BS(H)` sends `a |-> {a}` (singleton).
Then `eta(a => b) = {a => b}` and `eta(a) => eta(b) = {a} => {b}`. The adjunction gives:
`U inf {a} <= {b} iff U <= {a} => {b}`. Unpacking: `U union {a} |- b iff U |- a -> b`.
This is exactly the **Hilbert deduction theorem**, which is already proven in the codebase
(`hilbertImpIDeriv` and `hilbertImpEDeriv`). So `{a => b} = {a} => {b}` follows from the
deduction theorem.

**Why eta reflects top**: `eta(a) = {a} = top = {}` is impossible since {a} is nonempty.
More relevantly: `{a} <= {} = top` means "nothing needs to be derived", which is always true.
And `{} <= {a}` means "a is derivable from nothing", i.e., a = top in H. So
`eta(a) = top in BS(H)` iff `a = top in H`.

**Composition with LowerSet**: Once BS(H) is constructed, `LowerSet(BS(H))` is a
HeytingAlgebra (via `LowerSet.completelyDistribLattice`), and the composed embedding
`LowerSet.Iic . eta : H -> LowerSet(BS(H))` preserves himp (since both `eta` and
`LowerSet.Iic` preserve himp -- the latter via `iicHimp` which works on BSLs).

**Estimated difficulty**: Medium-high. Requires:
1. Define the multiset-based BSL (new file, ~200-300 lines)
2. Prove BrouwerianSemilattice instance (needs adjunction proof via deduction theorem)
3. Prove eta preserves himp and reflects top (~50 lines)
4. Compose with LowerSet.Iic to get HA embedding (~30 lines)
5. Prove the conservativity theorem using this embedding (~30 lines)

### Approach 5: Lindenbaum Quotient Map (CIRCULAR)

**Status**: Circular -- the quotient map reflecting top IS the conservativity theorem.

The natural map `q : ImpLindenbaumAlgebra -> IntLindenbaumAlgebra` defined by
`q([phi]_Imp) = [phi]_Int` preserves himp and top. But `q` reflects top (i.e.,
`q(x) = top implies x = top`) if and only if
`Derivable IntPropAxiom phi -> Derivable ImpAxiom phi`, which is the theorem we want to prove.

### Approach 6: Prop-valued Yoneda Embedding (BLOCKED)

**Status**: Blocked -- backward direction of himp preservation fails for Prop.

The embedding `eta(a)(x) = (a <= x)` into `(H -> Prop)` does not preserve himp.
Counterexample: in the free HilbertAlgebra on {a,b}, `eta(a => b)(b) = (a => b <= b)` is
false (since a => b is strictly above b by K), but `(eta(a) => eta(b))(b) = (a <= b -> b <= b)`
is vacuously true.

### Approach 7: Induction on Derivation Tree (UNCERTAIN)

**Status**: Uncertain viability, potentially simpler.

Given `Derivable ConjImpAxiom phi` with `phi.IsImpTopOnly`, transform the derivation tree to
eliminate uses of conjunction axioms (andI, andE1, andE2). This is a normalization procedure.

The difficulty is that Hilbert-style derivations don't have the subformula property.
Intermediate formulas in the derivation may involve conjunction even though the conclusion
is imp-only. Eliminating these detours requires either:
- A full normalization theorem for Hilbert derivations (substantial)
- A translation to sequent calculus, cut-elimination, and back (blocked by sorry)
- A direct combinatorial argument specific to the conjunction axioms

This approach is uncertain but could be simpler than Approach 4 if a clean combinatorial
argument exists.

## Recommendation

**Primary**: Approach 4 (Free BrouwerianSemilattice Construction)

This is the mathematically cleanest approach with clear formalizability. The key insight is
that the Hilbert deduction theorem (already proven) provides the BSL adjunction for the
free meet extension. The composition with `LowerSet.Iic` (whose himp preservation for BSLs
is already proven in `iicHimp`) gives a himp-preserving embedding into a HeytingAlgebra.

**Implementation steps**:

Phase 1: Create `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean`
- Define `FreeMeetExtension H` = `Multiset H` (or `List H` modulo equivalence)
- Define ordering via Hilbert deducibility
- Prove it's a BrouwerianSemilattice using `hilbertImpIDeriv`/`hilbertImpEDeriv`

Phase 2: Create `Cslib/Foundations/Order/HilbertAlgebra/HimpPreservingEmbedding.lean`
- Define `freeMeetEmbed : H -> FreeMeetExtension H` (singleton map)
- Prove himp preservation (uses deduction theorem)
- Prove top reflection (singleton nonempty argument)

Phase 3: Create `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean`
- Define `hilbertToHeyting : H -> LowerSet (FreeMeetExtension H)` = `LowerSet.Iic . freeMeetEmbed`
- Prove himp preservation (compose `iicHimp` and `freeMeetEmbed_himp`)
- Prove top reflection (compose both reflections)
- Prove the conservativity theorem following the ConjImpConservative pattern

**Fallback**: Approach 7 (Direct derivation tree transformation). If the free BSL
construction proves too complex, investigate whether conjunction axioms can be eliminated
from Hilbert derivations via a direct combinatorial argument.

## Existing Infrastructure Used

| Component | File | Purpose |
|-----------|------|---------|
| `hilbertIplConservativeOverConjImp` | `ConjImpConservative.lean` | Step 1: IPL -> ConjImp |
| `IsImpTopOnly_implies_IsOrBotFree` | `FragmentPredicates.lean` | Precondition for Step 1 |
| `imp_hilbert_complete` | `HilbertAlgCompleteness.lean` | HilbertValid -> Derivable ImpAxiom |
| `hilbertImpIDeriv` / `hilbertImpEDeriv` | `HilbertDeduction.lean` | Deduction theorem for BSL adjunction |
| `iicHimp` | `FreeJoinCompletion.lean` | LowerSet.Iic preserves himp on BSLs |
| `brouwerianEmbeddingLemma` | `FreeJoinCompletion.lean` | BSL validity <-> HA validity |
| `coe_AlgEvaluate_impTopOnly` | `FragmentPredicates.lean` | himp-morphism commutes with eval |
| `principal_le_himp` | `DiegoEmbedding.lean` | Forward half (not used directly) |
| `IPL.hilbert_alg_complete` | `HilbertCompleteness.lean` | IPL <-> HAValid |

## Source-to-Implementation Mapping

| Source Claim | BibKey | Lean Target | Translation Notes |
|--------------|--------|-------------|-------------------|
| Diego embedding theorem | Diego1966 (NOT in references.bib) | `DiegoEmbedding.lean` | Partial: only forward himp inequality proven |
| Rasiowa Ch V, Thm V.3.3 | Rasiowa1974 | `instGeneralizedHeytingAlgebra` | Filter lattice GHA instance |
| Rasiowa Ch V, Thm V.4.2 | Rasiowa1974 | NOT YET FORMALIZED | Full himp-preserving embedding into HA |
| Hilbert deduction theorem | (standard) | `hilbertImpIDeriv`/`hilbertImpEDeriv` | Key to free BSL construction |
| Free BSL construction | Kohler1981 (NOT in references.bib) | NOT YET FORMALIZED | Phase 1-2 of recommendation |

## Adversarial Self-Verification

1. **Challenged: "HilbertFilter H is a HeytingAlgebra"** -- Confirmed. HeytingAlgebra.mk requires
   GHA + OrderBot + Compl + himp_bot. HilbertFilter H is a GHA (proven) and CompleteLattice
   (proven, hence OrderBot). Defining Compl as `F => bot` makes himp_bot trivial.

2. **Challenged: "principal backward direction is provably false"** -- Verified via explicit
   counterexample analysis: in any non-trivial HilbertAlgebra H with incomparable a, b,
   `x in himpFilter(principal a)(principal b)` means "x >= a implies x >= b" while
   `x in principal(a => b)` means `a => b <= x`. The former is strictly weaker when H lacks
   meet.

3. **Challenged: "Deduction theorem gives BSL adjunction"** -- Confirmed. The deduction theorem
   `Gamma, A |- B <-> Gamma |- A -> B` is exactly the adjunction
   `U inf {a} <= {b} <-> U <= {a} => {b}` when elements are identified with singleton multisets
   and meet is multiset union.

4. **Challenged: "Free BSL approach composes with LowerSet"** -- Confirmed. `iicHimp` proves
   `LowerSet.Iic` preserves himp for any BrouwerianSemilattice. The free BSL is a BSL by
   construction. The composition `LowerSet.Iic . eta` preserves himp as a composition of
   two himp-preserving maps.

5. **BibKey verification**: `Rasiowa1974` is in references.bib. `Diego1966`, `Nemitz1965`,
   `Kohler1981` are referenced in source file docstrings but NOT in references.bib -- they
   should be added.
