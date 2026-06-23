# Research Report: Hilbert Algebra Soundness and Completeness for IPL⟨->,T⟩

Task: 309
Session: sess_1782252559_952370_309
Agent: cslib-research-hard-agent
Reference Grounding Tier: 1 (literature-backed)

## Source-to-Implementation Mapping

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|--------|---------------|-----------------|----------------|--------|
| [Rasiowa1974] | Def V.1.1 | `HilbertAlgebra` | `class HilbertAlgebra (H : Type*) extends HImp H, Top H` | transcribed (task 304) |
| [Rasiowa1974] | Ch V | `HilbertEvaluate` | `(v : Atom -> H) -> PL.Proposition Atom -> H` | transcribed (task 304) |
| [Rasiowa1974] | Ch V | `HilbertValid` | `forall (H : Type*) [HilbertAlgebra H] (v : Atom -> H), HilbertEvaluate v phi = T` | transcribed (task 304) |
| [Rasiowa1974] | Thm V.2.1 | `imp_hilbert_axiom_sound` | `ImpAxiom phi -> HilbertValid phi` | pending |
| [Rasiowa1974] | Thm V.2 | `imp_hilbert_soundness_derivable` | `Derivable ImpAxiom phi -> HilbertValid phi` | pending |
| [Rasiowa1974] | Def V.4 | `ImpEquiv` | `Deriv ImpAxiom [A] B /\ Deriv ImpAxiom [B] A` | pending |
| [Rasiowa1974] | Def V.4 | `ImpLindenbaumAlgebra` | `Quotient impPropositionSetoid` | pending |
| [Rasiowa1974] | Def V.4 | `impLindenbaumMk` | `PL.Proposition Atom -> ImpLindenbaumAlgebra Atom` | pending |
| [Rasiowa1974] | Thm V.5 | `impLindenbaumHA` | `HilbertAlgebra (ImpLindenbaumAlgebra Atom)` | pending |
| [Rasiowa1974] | Lem V.4 | `impLindenbaumMk_eq_top_iff` | `impLindenbaumMk A = T <-> Derivable ImpAxiom A` | pending |
| [Rasiowa1974] | Lem V.5 | `impCanonicalV_spec` (truth lemma) | `HilbertEvaluate impCanonicalV A = impLindenbaumMk A` | pending |
| [Rasiowa1974] | Thm V.6 | `imp_hilbert_complete` | `IsImpTopOnly phi -> HilbertValid phi -> Derivable ImpAxiom phi` | pending |
| [Rasiowa1974] | Thm V.6 | `imp_hilbert_iff` | `IsImpTopOnly phi -> (Derivable ImpAxiom phi <-> HilbertValid phi)` | pending |

BibKey verification: `Rasiowa1974` verified in `references.bib` at line 757. Diego (1966) is NOT in `references.bib` -- needs to be added for full citation coverage, but is not essential for the formalization since Rasiowa (1974) subsumes the required results.

## Findings

### 1. Existing Infrastructure Assessment

**Task 304 (COMPLETED) provides**:
- `HilbertAlgebra` typeclass at `Cslib/Foundations/Order/HilbertAlgebra.lean` (207 lines) with fields `himp_K`, `himp_S`, `himp_antisymm`, `himp_self` and derived lemmas `himp_top`, `himp_mp`, `himp_trans`, `top_himp`, `himp_eq_top_iff`, `instPartialOrder`, `instOrderTop`.
- `HilbertEvaluate` and `HilbertValid` at `Cslib/Logics/Propositional/Semantics/Algebra/Hilbert.lean` (107 lines).
- `BrouwerianSemilattice.toHilbertAlgebra` forgetful instance (priority 100).

**Proof system for ImpAxiom**:
- `ImpAxiom` inductive at `FragmentAxioms.lean` lines 84-90 with constructors `implyK` and `implyS`.
- `ImpAxiom.mem_implyK` and `ImpAxiom.mem_implyS` witnesses at lines 131-141.
- `impAxiom_hasDeductionTheorem` at line 241.
- `ImpAxiom.toConjImpAxiom` subsumption at lines 95-99.
- Fragment predicates: `IsImpTopOnly` at `FragmentPredicates.lean` lines 63-67 with `imp_isImpTopOnly`, `subst_preserves_isImpTopOnly`.

**Existing completeness infrastructure**:
- `HilbertLindenbaum.lean` (727 lines): Lindenbaum algebra for `MinimalAxioms`-based systems. **Cannot be used for ImpAxiom** because `MinimalAxioms` requires AND and OR axiom schema fields that `ImpAxiom` does not provide.
- `BrouwerianCompleteness.lean` (529 lines): Lindenbaum algebra for `ConjImpAxiom` over `BrouwerianSemilattice`. **This is the exact template** for task 309 -- same pattern but replacing `ConjImpAxiom` with `ImpAxiom` and `BrouwerianSemilattice` with `HilbertAlgebra`.
- `HilbertCompleteness.lean` (121 lines): Completeness for MPL/IPL/CPL via the `HilbertLindenbaumAlgebra` from `HilbertLindenbaum.lean`. Operates at the `MinimalAxioms` level, not the `ImpAxiom` level.

### 2. What Needs to Be Built

The target file `HilbertAlgCompleteness.lean` does NOT exist. The task requires building a complete, standalone Lindenbaum construction for `ImpAxiom` -> `HilbertAlgebra`, following the pattern of `BrouwerianCompleteness.lean`.

**Key structural difference from the Brouwerian case**: The Brouwerian Lindenbaum algebra is a `BrouwerianSemilattice` which requires `SemilatticeInf` (and hence `inf` and `le_inf`). Those require the AND axioms (`andI`, `andE1`, `andE2`) from `ConjImpAxiom`. The Hilbert algebra Lindenbaum construction does NOT need these -- it only needs `himp` (which comes from the `imp` connective) and the K/S axioms. The construction is strictly simpler.

### 3. Proof Strategy

#### Part A: Soundness

**Theorem**: `imp_hilbert_axiom_sound : ImpAxiom phi -> HilbertValid phi`

Proof by case analysis on the two `ImpAxiom` constructors:
- `implyK phi psi`: Need `v phi ⇨ (v psi ⇨ v phi) = T`. Use `HilbertAlgebra.himp_K`.
- `implyS phi psi chi`: Need the S combinator identity. Use `HilbertAlgebra.himp_S`.

Both cases are direct applications of the `HilbertAlgebra` axiom fields. This is the simplest soundness proof in the hierarchy.

**Derivation-level soundness**: Induction on `DerivationTree ImpAxiom`, following the exact pattern from `min_alg_soundness` in `Soundness.lean` but using `HilbertEvaluate` instead of `AlgEvaluate` and `HilbertAlgebra.himp_eq_top_iff` instead of `himp_eq_top_iff`.

#### Part B: Lindenbaum Construction

1. **ImpEquiv relation**: `ImpEquiv A B := Deriv ImpAxiom [A] B /\ Deriv ImpAxiom [B] A`
   - Reflexivity: `assumption_deriv`
   - Symmetry: swap components
   - Transitivity: `hilbertCutSingletonDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS`

2. **Setoid and Quotient**: `impPropositionSetoid`, `ImpLindenbaumAlgebra Atom`, `impLindenbaumMk`

3. **Order**: `impLindenbaumLe x y := Quotient.liftOn2 x y (fun A B => Deriv ImpAxiom [A] B) ...`
   - Well-definedness uses the same congruence argument as `brouwerianLindenbaumLe`.

4. **Himp operation**: `impLindenbaumHimp x y := Quotient.lift2 (fun A B => impLindenbaumMk (A.imp B)) ...`
   - Congruence via `impEquivImpCongr` (same pattern as `conjImpEquivImpCongr`, using only K/S, no AND).

5. **Top element**: `T := impLindenbaumMk (bot.imp bot)` (same as other constructions).

#### Part C: HilbertAlgebra Instance

Proving `HilbertAlgebra (ImpLindenbaumAlgebra Atom)` requires four fields:

1. **himp_K**: `[A] ⇨ ([B] ⇨ [A]) = T`, i.e., `[A -> (B -> A)] = T`, i.e., `Derivable ImpAxiom (A -> (B -> A))`. This is immediate from `ImpAxiom.implyK`.

2. **himp_S**: `([A] ⇨ ([B] ⇨ [C])) ⇨ (([A] ⇨ [B]) ⇨ ([A] ⇨ [C])) = T`. This unfolds to `Derivable ImpAxiom ((A -> (B -> C)) -> ((A -> B) -> (A -> C)))`. Immediate from `ImpAxiom.implyS`.

3. **himp_antisymm**: If `[A] ⇨ [B] = T` and `[B] ⇨ [A] = T`, then `[A] = [B]`. This unfolds to: if `Derivable ImpAxiom (A -> B)` and `Derivable ImpAxiom (B -> A)`, then `[A] = [B]` in the quotient. Use `Quotient.sound` with the witnessing derivations `Deriv ImpAxiom [A] B` and `Deriv ImpAxiom [B] A` (obtained from `Derivable` via weakening, then modus ponens).

4. **himp_self**: `[A] ⇨ [A] = T`, i.e., `Derivable ImpAxiom (A -> A)`. Proved via `hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS` applied to `assumption_deriv`.

**Key insight**: Unlike `BrouwerianSemilattice`, `HilbertAlgebra` does NOT require `le_himp_iff` (the adjunction / deduction theorem). The K/S/antisymm/self fields are all provable WITHOUT the inf operation. This makes the construction significantly simpler than the Brouwerian case.

#### Part D: Truth Lemma and Completeness

**Truth Lemma** (restricted to `IsImpTopOnly`):
```
HilbertEvaluate impCanonicalV A = impLindenbaumMk A
```
for `A.IsImpTopOnly = true`.

Proof by structural induction on `A`:
- `atom x`: definitional.
- `bot`: `IsImpTopOnly` is `false` for `bot`, so this case is vacuous.
- `imp a b`: `HilbertEvaluate v (a -> b) = HilbertEvaluate v a ⇨ HilbertEvaluate v b = [a] ⇨ [b] = [a -> b]`.
- `and`, `or`: `IsImpTopOnly` is `false`, vacuous.

The restriction to `IsImpTopOnly` is essential because `HilbertEvaluate` maps `bot`, `and`, `or` to `T` (the default), but `[bot]`, `[and a b]`, `[or a b]` are NOT necessarily `T` in the Lindenbaum algebra (no EFQ, no AND/OR axioms).

**Completeness**:
```
imp_hilbert_complete : IsImpTopOnly phi -> HilbertValid phi -> Derivable ImpAxiom phi
```
Proof: Instantiate `HilbertValid` at `ImpLindenbaumAlgebra Atom` with `impCanonicalV`. Apply truth lemma. Extract via `impLindenbaumMk_eq_top_iff`.

**Top characterization**: `impLindenbaumMk_eq_top_iff : impLindenbaumMk A = T <-> Derivable ImpAxiom A`. Same pattern as `brouwerianLindenbaumMk_eq_top_iff`.

### 4. Conservative Extension Result (Bonus)

Once soundness and completeness are established, the conservative extension theorem follows:

```
hilbertIplConservativeOverImp : IsImpTopOnly phi -> Derivable IntPropAxiom phi -> Derivable ImpAxiom phi
```

Proof strategy (following `hilbertIplConservativeOverConjImp`):
1. `IPL.hilbert_alg_complete.mp h` gives `HAValid phi`.
2. For any `HilbertAlgebra H` and `v`, instantiate at some free completion. But since `HilbertAlgebra` is weaker than `HeytingAlgebra`, we need the forgetful instance `BrouwerianSemilattice.toHilbertAlgebra` and the fact that `GeneralizedHeytingAlgebra` extends `BrouwerianSemilattice`. Since every `HeytingAlgebra` is a `HilbertAlgebra` (via the forgetful path), `HAValid phi` directly implies `HilbertValid phi` for imp-top-only formulas (using `coe_AlgEvaluate_impTopOnly`).
3. Apply `imp_hilbert_complete`.

This conservative extension proof needs careful handling of the evaluator mismatch: `HAValid` uses `AlgEvaluate` while `HilbertValid` uses `HilbertEvaluate`. For `IsImpTopOnly` formulas, both evaluators agree (they only use `⇨`), so a bridge lemma is needed.

### 5. File Organization

Target: `Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean`

Required imports:
- `Cslib.Logics.Propositional.Semantics.Algebra.Hilbert` (HilbertEvaluate, HilbertValid)
- `Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` (ImpAxiom, deduction theorem)
- `Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules` (hilbertImpIDeriv etc.)
- `Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates` (IsImpTopOnly)

Estimated size: ~350-450 lines (comparable to `BrouwerianCompleteness.lean` at 529 lines, minus the AND-related infrastructure which is not needed).

### 6. Key Lemma Dependencies

All required derivation infrastructure already exists:
- `hilbertCutSingletonDeriv`: cut rule for singleton contexts (requires K, S witnesses)
- `hilbertCutListDeriv`: cut rule for general contexts
- `hilbertImpIDeriv`: deduction theorem / implication introduction
- `hilbertImpEDeriv`: modus ponens
- `hilbertWeakenSingleton`: weakening from singleton to extended context
- `assumption_deriv`: assumption rule
- `weakening_deriv`: general weakening
- `ImpAxiom.mem_implyK`, `ImpAxiom.mem_implyS`: axiom witnesses

No new derivation-level lemmas are needed.

## Adversarial Self-Verification

### Challenge 1: Is the `HilbertAlgebra` instance really provable without `le_himp_iff`?

**Verified**: Yes. `HilbertAlgebra` requires only `himp_K`, `himp_S`, `himp_antisymm`, and `himp_self` -- all equational/implicational identities. None require the adjunction `a <= b ⇨ c <-> a inf b <= c`. The Brouwerian construction needed `le_himp_iff` because `BrouwerianSemilattice` requires it, but `HilbertAlgebra` does not.

### Challenge 2: Does `impEquivImpCongr` work without AND axioms?

**Verified**: Yes. The proof of `conjImpEquivImpCongr` in `BrouwerianCompleteness.lean` (lines 242-263) uses ONLY `hilbertImpIDeriv`, `hilbertImpEDeriv`, `hilbertWeakenSingleton`, `hilbertCutListDeriv`, and `assumption_deriv` -- all of which require only K and S axiom witnesses. No AND axioms are used. The proof transfers directly by replacing `ConjImpAxiom.mem_implyK/S` with `ImpAxiom.mem_implyK/S`.

### Challenge 3: Is the truth lemma restriction to `IsImpTopOnly` sufficient for completeness?

**Verified**: Yes. `HilbertValid` quantifies over all `HilbertAlgebra H` and all `v : Atom -> H`. Since `HilbertEvaluate` maps `bot`, `and`, `or` to `T`, any formula containing these connectives is trivially Hilbert-valid. The completeness theorem only needs to handle `IsImpTopOnly` formulas, and the truth lemma works exactly for these.

### Challenge 4: Is the conservative extension bridge possible?

**Verified with caveat**: The bridge from `HAValid phi` to `HilbertValid phi` for `IsImpTopOnly` formulas requires showing that `AlgEvaluate v bot phi = HilbertEvaluate v phi` when `phi.IsImpTopOnly = true`. For such formulas, both evaluators compute the same recursive function (only the `atom` and `imp` branches fire). A simple structural induction suffices. However, the `AlgEvaluate` uses `bot` while `HilbertEvaluate` uses `T` for the `bot` case -- but for `IsImpTopOnly` formulas, the `bot` case is unreachable. This bridge is straightforward.

### Challenge 5: Reuse completeness -- is anything in Foundations already doing this?

**Verified**: No existing file in `Cslib/Foundations/` or `Cslib/Logics/Propositional/Semantics/Algebra/` provides `HilbertAlgebra`-level completeness for `ImpAxiom`. The `HilbertCompleteness.lean` file handles `MinPropAxiom/IntPropAxiom/PropositionalAxiom` via `MinimalAxioms`-based Lindenbaum algebras, NOT `ImpAxiom`-based ones.

### BibKey Verification Status

- `Rasiowa1974`: VERIFIED in `references.bib` line 757
- `Diego1966`: NOT FOUND in `references.bib` -- recommend adding if the PR references it

### Confidence Assessment

All recommendations are high-confidence. The construction follows a well-established pattern (`BrouwerianCompleteness.lean`) with strictly fewer proof obligations (no AND operations). The main risk is the conservative extension bridge, which is optional and can be deferred if the bridge lemma is more complex than expected.

## Recommendations

### Phase 1: Soundness (~80 lines)
- `imp_hilbert_axiom_sound`: case analysis on K, S
- `imp_hilbert_soundness`: induction on `DerivationTree`
- `imp_hilbert_soundness_derivable`: wrapper

### Phase 2: Lindenbaum Construction (~200 lines)
- `ImpEquiv`, setoid, quotient, quotient map
- `impLindenbaumLe`, congruence lemmas
- `impLindenbaumHimp`
- `HilbertAlgebra` instance (the centerpiece)
- `impLindenbaumMk_eq_top_iff`

### Phase 3: Truth Lemma and Completeness (~80 lines)
- `impCanonicalV`
- `impCanonicalV_spec` (truth lemma, restricted to `IsImpTopOnly`)
- `imp_hilbert_complete`
- `imp_hilbert_iff`

### Phase 4 (Optional): Conservative Extension (~50 lines)
- Bridge lemma: `AlgEvaluate`/`HilbertEvaluate` agreement for `IsImpTopOnly`
- `hilbertIplConservativeOverImp`

Total estimated: 350-410 lines (without Phase 4), ~450 lines (with Phase 4).

Zero-debt compliance: All proofs follow established patterns with complete infrastructure. No sorry deferral needed.
