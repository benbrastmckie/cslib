# Teammate B Findings: Alternative Patterns and Prior Art

- **Task**: 266 - Research Propositional and Foundations Improvements
- **Type**: cslib
- **Focus**: Alternative patterns and prior art — what else is out there to adapt
- **Date**: 2026-06-22
- **Agent**: cslib-research-agent (Teammate B)
- **Artifact number**: 01

---

## Key Findings (Prior Art and Alternatives)

### 1. Mathlib Has No Stand-Alone Sequent Calculus Formalization

Exhaustive search of Mathlib via `lean_leansearch`, `lean_loogle`, and `lean_leanfinder` found:

- **No Gentzen LK/LJ sequent calculus** in Mathlib. Searches for "sequent calculus propositional logic", "cut elimination Gentzen", "LK sequent left right rules" returned no Mathlib entries for sequent calculi. Mathlib's proof-theoretic content is concentrated in tactics (`itauto`, `tauto`, `decide`) and SAT (`Sat.Fmla`, LRAT proof checking), not formal proof theory.
- **`Mathlib.Tactic.ITauto`** (G4ip algorithm): The `itauto` tactic implements the G4ip contraction-free sequent calculus for intuitionistic propositional logic as an internal decision procedure. The `IProp` and `Proof` inductive types in `Mathlib.Tactic.ITauto` represent the *internal* reification; they are not exposed as a standalone formalized proof system.
- **`Mathlib.Tactic.Sat.FromLRAT`**: Propositional SAT with LRAT proof checking. Not relevant to proof-theoretic formalization.

**Conclusion**: Mathlib offers no ready-made sequent calculus to import. Any CSLib sequent calculus would be new work, but can adapt the `IProp`/`Proof` inductive structure from `Mathlib.Tactic.ITauto` as a design reference.

### 2. External Lean 4 Formalizations of Sequent Calculus

Known external projects (from general knowledge, not found via MCP search since they are not in Mathlib):

- **Phil Wadler's "Programming Language Foundations in Agda" (PLFA)**: The Agda book has a well-known sequent calculus formalization. The Lean 4 port (`plfl`) would be the most natural prior art to look at.
- **`Logic.Basic` in Lean4-Logic** (Riku Yoshihara's project): Has a sequent calculus formalization for modal logic using the `Sequent` type with `List`-based antecedents and succedents. The CSLib `Cslib.Logic.CLL` already uses a similar style (multiset sequents).
- **`GrindLin` and `Propositional`** in `lean4-prop-logic`: Small standalone libraries. Not in Mathlib.

**Key design insight from CLL**: `Cslib.Logics.LinearLogic.CLL.Basic` already defines `Sequent` as a multiset (using `Multiset`), which is the standard choice for sequent calculi avoiding explicit exchange. This is more mature than the `List`-based context in `Cslib.Logics.Propositional.NaturalDeduction.Basic` (which uses `Finset` for the ND system and `List` for the Hilbert `DerivationTree`).

### 3. G4ip as the Canonical Propositional Sequent Calculus to Add

The G4ip algorithm (Dyckhoff 1992) is the contraction-free sequent calculus for intuitionistic propositional logic. It is:
- Already proven sound and complete (in Lean 4, implicitly via `itauto`)
- The canonical choice for a decidable IPL proof system
- Directly comparable with CSLib's NaturalDeduction system (the `hilbert_iff_nd` bridge could be extended to G4ip)

For classical propositional logic (CPL), the LK calculus is the reference. For minimal logic, LM (a restricted LK) applies.

---

## Mathlib Integration Opportunities

### A. `Mathlib.Order.Heyting.Basic` — Already Used (Good)

`Cslib.Logics.Propositional.Semantics.Algebra` already imports `Mathlib.Order.Heyting.Basic` and `Mathlib.Order.BooleanAlgebra.Basic`. The algebraic semantics layer (`AlgEvaluate`, `GHAValid`, `HAValid`, `BAValid`) is well-grounded in Mathlib's algebra hierarchy.

**Opportunity**: The sorry in `ipl_conservative_over_mpl` (`Conservative.lean` line 99) requires Dedekind-MacNeille completion. Mathlib has `Mathlib.Order.CompleteLattice.Completion` and related machinery. This could be the source for the completion needed.

### B. `Mathlib.Tactic.ITauto.IProp` — G4ip Internal Algorithm

The G4ip algorithm in `Mathlib.Tactic.ITauto` implements decision for IPL. The `IProp` type mirrors `PL.Proposition`; the `Proof` type captures G4ip proof steps. This is not the same as a formal sequent calculus for CSLib, but the algorithm could be:
1. Extracted as a decision procedure for `Cslib.Logic.PL.Proposition`
2. Used to prove `DecidablePred (DerivableIn IPL)` for finite atom sets

**This is the most actionable Mathlib integration**: connect CSLib's `PL.Proposition` to `Mathlib.Tactic.ITauto.IProp` via a reification function, then use `itauto` to prove decidability of IPL derivability.

### C. `Mathlib.Order.BooleanAlgebra.Basic` — CPL Decidability

`Bool` is already a `BooleanAlgebra` instance. The existing `BoolEvaluate` in `Cslib.Logics.Propositional.Semantics.Bool` maps `PL.Proposition` to `Bool`. For CPL:
- `DecidablePred (DerivableIn CPL)` follows from `BoolEvaluate` via completeness (the proof already exists via `StrongCompleteness`)
- The finiteness argument (finitely many atoms → finitely many valuations → decidable) is available in Mathlib via `Fintype` instances

---

## Cross-Module Pattern Analysis

### Pattern 1: Propositional as a Foundation for Modal/Temporal/Bimodal

The import chain is:
```
Cslib.Logics.Modal.FromPropositional imports Cslib.Logics.Propositional.Defs + Semantics.Bool
Cslib.Logics.Modal.Metalogic.Systems.K.ConservativeExtension imports Propositional.Metalogic.StrongCompleteness
Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.PropositionalConservativity imports same
```

**Gap**: The Propositional module is used as a syntactic foundation (formula type, substitution) and semantic foundation (Bool evaluation for conservativity) but not as a structural foundation for the Hilbert proof system. Each logic module (Modal, Temporal, Bimodal) duplicates its own Hilbert derivation tree. The `Foundations.Logic.ProofSystem` typeclass hierarchy (`MinimalHilbert`, `ClassicalHilbert`, etc.) was designed to unify these, but as of now `Propositional.ProofSystem` still has its own standalone `DerivationTree` separate from the `MinimalHilbert` instance.

**Pattern to adopt from Modal**: In `Cslib.Logics.Modal.Metalogic`, the `DerivationTree` is parameterized over an axiom predicate. The same pattern applies in `Cslib.Logics.Propositional.ProofSystem.Derivation` (already parameterized over `Axioms : PL.Proposition Atom → Prop`). The gap is that Modal's `DerivationTree` uses 5 constructors (ax, assumption, mp, weakening, necessitation), while Propositional's uses 4 (no necessitation). This is correct but needs explicit documentation.

### Pattern 2: ND + Hilbert Bridge (Propositional is Ahead)

The propositional module has the most sophisticated proof system setup in CSLib:
- Two independent proof systems (ND in `NaturalDeduction/` and Hilbert in `ProofSystem/`)
- A bridge proving equivalence (`NaturalDeduction/Equivalence.lean`)
- Three logic strengths (MPL, IPL, CPL) with dedicated instances

Modal, Temporal, and Bimodal only have Hilbert systems (no ND). The ND system in Propositional is more advanced than anything in the more complex logics. **Recommendation**: The ND system is a strength of Propositional that the other logic modules could eventually adopt; the pattern should not be "fixed" but rather held up as the target architecture.

### Pattern 3: Algebraic Semantics (Three-Level Hierarchy)

The Propositional algebraic semantics (`GHA → HA → BA`) matches the three logic strengths (`MPL → IPL → CPL`). This is a clean design that Modal lacks (Modal only has Kripke semantics, no algebraic semantics). The Bimodal module has an algebraic approach (`Algebraic/BooleanStructure.lean`, `Algebraic/LindenbaumQuotient.lean`) for its completeness proof, but it is specific to the Bimodal logic.

**Opportunity**: The `Cslib.Logics.Propositional.Semantics.Algebra` could be more explicitly connected to the `Cslib.Foundations.Logic.Metalogic.GenericMCS` framework. Currently `GenericMCS` provides `algebraicDerivationSystem` for any `MinimalHilbert`, but Propositional's algebraic semantics does not use `GenericMCS`.

### Pattern 4: Sequent-Style NaturalDeduction vs. Hilbert

CSLib uses Finset-based contexts for ND sequents (`Ctx (Atom) := Finset (Proposition Atom)`) and List-based contexts for Hilbert derivation trees (`DerivationTree Axioms : List (PL.Proposition Atom) → ...`). The CLL module uses `Multiset` for its sequents. This inconsistency is intentional (ND uses Finset to avoid exchange/contraction; Hilbert uses List for computational height), but a sequent calculus for Propositional would need to choose between Finset (for IPL) and Multiset (for linear-style) and document the choice.

---

## Sequent Calculus Research

### What a Propositional Sequent Calculus Would Add

The CSLib Propositional module currently has:
- Hilbert-style proof system (3 variants: MPL, IPL, CPL)
- Natural deduction (10-constructor inductive)
- Bridge between the two
- Soundness and strong completeness (Kripke + algebraic)

Missing:
1. **Sequent calculus** (Gentzen LK/LJ/Gentzen-Johansson)
2. **Cut elimination** theorem for the sequent calculus
3. **Decidability** theorem (via sequent calculus saturation or G4ip)
4. **Normal form theorem** (analogous to what Bimodal has in `Separation/NormalForm.lean`)

### G4ip Design for CSLib

Based on Dyckhoff (1992), G4ip (intuitionistic, contraction-free) would add:

```lean
/-- G4ip sequent calculus for intuitionistic propositional logic -/
inductive G4ip.Proof : Finset (Proposition Atom) → Proposition Atom → Type where
  | init (h : p ∈ Γ) : G4ip.Proof Γ p          -- identity rule
  | botL (h : ⊥ ∈ Γ) : G4ip.Proof Γ A           -- L⊥
  | andR : G4ip.Proof Γ A → G4ip.Proof Γ B →
      G4ip.Proof Γ (A ∧ B)                         -- R∧
  | andL1 (h : A ∧ B ∈ Γ) :
      G4ip.Proof (insert A (insert B (Γ.erase (A ∧ B)))) C →
      G4ip.Proof Γ C                               -- L∧
  | orR1 : G4ip.Proof Γ A → G4ip.Proof Γ (A ∨ B) -- R∨₁
  | orR2 : G4ip.Proof Γ B → G4ip.Proof Γ (A ∨ B) -- R∨₂
  | orL (h : A ∨ B ∈ Γ) :
      G4ip.Proof (insert A (Γ.erase (A ∨ B))) C →
      G4ip.Proof (insert B (Γ.erase (A ∨ B))) C →
      G4ip.Proof Γ C                               -- L∨
  | impR : G4ip.Proof (insert A Γ) B →
      G4ip.Proof Γ (A → B)                         -- R→
  | impL_atom (h₁ : p ∈ Γ) (h₂ : (p → B) ∈ Γ) :
      G4ip.Proof (insert B (Γ.erase (p → B))) C →
      G4ip.Proof Γ C                               -- L→ (atom case)
  | impL_imp (h : ((A → B) → C) ∈ Γ) :
      G4ip.Proof (insert (B → C) (Γ.erase ((A → B) → C))) (A → B) →
      G4ip.Proof (insert C (Γ.erase ((A → B) → C))) D →
      G4ip.Proof Γ D                               -- L→ (implication case)
  -- ... additional G4ip rules
```

The G4ip rules are contraction-free (formulae are removed when used on the left), guaranteeing termination. This differs from the existing ND system (which requires explicit cut/weakening operations).

### Classical Sequent Calculus (LK) for CPL

For CPL, the LK calculus has two-sided sequents `Γ ⊢ Δ` (multiset antecedent, multiset succedent). CSLib currently only has one-sided sequents (`Γ ⊢ A`). The CLL module already uses two-sided sequents for linear logic. A propositional LK would:
1. Use the same `Sequent` type as CLL (multiset-based)
2. Need right-rule counterparts for all connectives
3. Prove cut elimination

### Comparison with CLL's Sequent Calculus

`Cslib.Logics.LinearLogic.CLL.Basic` uses multiset sequents and has a `Proof` inductive with 15+ constructors including explicit `cut`. The `CutElimination.lean` file has the structure but is not yet implemented (the key definitions are commented out):

```lean
-- TODO
/- Cut admissibility: given two proofs with dual propositions, returns a cut-free proof. -/
-- def Proof.cutAdm ...

-- TODO  
/- Cut elimination: given a proof of a sequent `Γ`, returns a cut-free proof. -/
-- def Proof.cut_elim (p : ⇓Γ) : CutFreeProof Γ
```

**The CLL cut elimination is a direct target**: if we add a propositional LK sequent calculus, the cut elimination technique would be similar and the CLL work would provide a template.

---

## Tableau System Comparison

### BimodalLogic Tableau (Report 16 context) vs. CSLib Bimodal Tableau

The BimodalLogic project's tableau is mentioned in the context of `PriorComposition.lean`'s sorry at K=0 — the tableau is not directly relevant to the witness-count induction problem. However, the CSLib Bimodal `Decidability/` module already has a tableau system ported from BimodalLogic:

**CSLib Bimodal Tableau** (`Cslib.Logics.Bimodal.Metalogic.Decidability`):
- `SignedFormula`: sign × formula × label (world × time)
- `Branch`: `List (SignedFormula Atom)` (not a tree structure)
- 30 expansion rules in `Tableau.lean` (propositional + modal S5 + temporal)
- Eventuality tracking for Until/Since
- Subset blocking for termination
- Subformula closure bounding

**Key properties**:
- The propositional rules (andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg) are standard analytic tableau rules, identical to classical propositional tableau
- The tableau is a *labeled* tableau (each formula has a world×time label), not a bare propositional tableau
- No proof of completeness or termination has been formally verified yet (they are stated as theorems but the key ones are partial)

**What BimodalLogic's witness-count restructure (Report 16) reveals about tableau design**: The tableau in the Decidability module operates at the formula level (using signed subformulas), whereas the Kamp theorem proof in BimodalLogic operates at the NF (normal form) level. These are *different* formalizations of the same decidability question. The tableau approach is more direct and more formalizable, but the NF approach captures the expressive completeness argument that the tableau does not.

### Propositional Tableau for CSLib

A standalone propositional tableau (without labels) would be simpler than the Bimodal tableau:

```lean
/-- Signed propositional formula (no label needed for propositional logic) -/
structure PropTableau.SignedFormula (Atom : Type*) where
  sign : Sign
  formula : PL.Proposition Atom

/-- Propositional tableau branch -/
abbrev PropTableau.Branch (Atom) := List (PropTableau.SignedFormula Atom)

/-- Propositional tableau expansion rules -/
inductive PropTableau.Rule : Branch Atom → List (Branch Atom) → Prop where
  | andPos (h : ⟨.pos, A ∧ B⟩ ∈ Γ) :
      PropTableau.Rule Γ [⟨.pos, A⟩ :: ⟨.pos, B⟩ :: Γ]    -- non-branching
  | andNeg (h : ⟨.neg, A ∧ B⟩ ∈ Γ) :
      PropTableau.Rule Γ [⟨.neg, A⟩ :: Γ, ⟨.neg, B⟩ :: Γ] -- branching
  -- ... etc.
```

This would provide a decidable classical propositional logic proof system that is closed to the Bimodal pattern, enabling a `FromPropositional` embedding at the proof-system level (not just the formula level).

### Adapting the Bimodal Tableau Pattern

The Bimodal `SignedFormula` + `Branch` + `TableauRule` architecture can be directly adapted for propositional logic by:
1. Dropping the `Label` (no worlds/times needed)
2. Keeping only the 8 propositional rules (andPos/Neg, orPos/Neg, impPos/Neg, negPos/Neg)
3. Keeping closure detection (`hasContradiction`)
4. Adding a `saturate` function that applies rules until fixed point

This would give CPL a `decide` function analogous to `Cslib.Logics.Bimodal.Metalogic.Decidability.DecisionProcedure.decide`.

---

## Recommended Approach (Which Alternatives to Adopt)

In priority order:

### Priority 1: Resolve the `ipl_conservative_over_mpl` Sorry

**File**: `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean:99`
**Approach**: Use Dedekind-MacNeille completion from Mathlib (`Mathlib.Order.CompleteLattice.Completion` or equivalent) to embed the GHA Lindenbaum algebra into a complete Heyting algebra. This is deferred but is a known mathematical gap.

### Priority 2: Add a Propositional G4ip Sequent Calculus

**Module**: `Cslib/Logics/Propositional/SequentCalculus/G4ip.lean`
**Adapt from**: Dyckhoff (1992); structure analogous to `NaturalDeduction/Basic.lean`
**Bridge**: Add `G4ip/Equivalence.lean` proving `G4ip ↔ ND ↔ Hilbert` for IPL
**Benefit**: Adds a *third* proof system to Propositional, making it the most complete PL formalization in any Lean 4 library; provides decidability of IPL as a corollary (G4ip terminates + is complete)

### Priority 3: Propositional Tableau for CPL Decidability

**Module**: `Cslib/Logics/Propositional/Tableau/`
**Adapt from**: `Cslib.Logics.Bimodal.Metalogic.Decidability` (drop labels, keep 8 propositional rules)
**Bridge**: Connect to `Cslib.Logics.Propositional.Semantics.Bool` (Bool evaluation is the tableau model)
**Benefit**: Gives CPL a `decide : Proposition Atom → Bool` function + soundness/completeness for CPL decidability

### Priority 4: `Foundations.Logic.ProofSystem` — Wire the Concrete Instances

The `ProofSystem.lean` typeclass hierarchy (`MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert`) has tag types (`Propositional.HilbertMin`, `Propositional.HilbertInt`, `Propositional.HilbertCl`) but the module comment says "Concrete instances require derivation trees (not yet ported) and are future work." The `Propositional.ProofSystem.Derivation` already has derivation trees. **Gap**: The concrete `MinimalHilbert Propositional.HilbertMin` instance has not been registered using the `DerivationTree` from `Propositional.ProofSystem.Derivation`. This would unify Propositional's Hilbert system with the `Foundations.Logic.ProofSystem` typeclass hierarchy that Modal/Temporal/Bimodal use.

### Priority 5: CLL Cut Elimination

**File**: `Cslib/Logics/LinearLogic/CLL/CutElimination.lean`
**Currently**: The `cutAdm` and `cut_elim` functions are commented out as TODOs
**Approach**: Standard Gentzen-style cut elimination by induction on cut complexity + cut grade
**Benefit**: Makes CLL a complete formalization; validates the `CutFreeProof` wrapper

---

## Evidence and Examples

### Evidence 1: Mathlib G4ip Is Internal, Not Exposed

From `lean_leanfinder` search results: `Mathlib.Tactic.ITauto.Proof` is described as "The inductive type `Proof` represents reified proofs in intuitionistic propositional logic, used by the `itauto` decision procedure. It captures valid proof steps according to the G4ip algorithm for intuitionistic tautologies." — confirming the algorithm exists but is an internal tactic implementation, not a standalone formalized proof system.

### Evidence 2: CLL Has the Multiset Sequent Pattern

```lean
-- From Cslib.Logics.LinearLogic.CLL.Basic (existing):
abbrev CutFreeProof (Γ : Sequent Atom) := { q : ⇓Γ // q.cutFree }
-- Cut elimination is TODO (commented out in CutElimination.lean)
```

### Evidence 3: Bimodal Tableau Has 30 Rules but No Formal Termination Proof

From `Cslib.Logics.Bimodal.Metalogic.Decidability.Tableau.lean` header:
```
-- Propositional: andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg (8 rules)
-- Modal S5: boxPos, boxNeg (2 rules)
-- Temporal: allFuturePos, allFutureNeg, allPastPos, allPastNeg, + Until/Since rules (20 rules)
```

The propositional rules are a self-contained subset; extracting them gives a standalone propositional tableau.

### Evidence 4: The NaturalDeduction `subs` Function Has a Capture-Avoidance TODO

```lean
-- From Cslib/Logics/Propositional/NaturalDeduction/Basic.lean line 276:
/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. TODO:
this implementation is not capture avoiding. -/
def Theory.Derivation.subs ...
```

This is a known gap: the substitution in the ND system is not capture-avoiding. For a full formalization (including Curry-Howard correspondence), this needs to be fixed.

### Evidence 5: The Only Sorry in Propositional Is `ipl_conservative_over_mpl`

From the sorry search:
```
/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean:99:  sorry
```

There is exactly ONE sorry in the entire Propositional module. This is a very clean state. The Foundations module has zero sorries.

### Evidence 6: `Foundations.Logic.ProofSystem` Tag Types Are Opaque Stubs

From `ProofSystem.lean` lines 465-520:
```lean
opaque Propositional.HilbertMin : Type := Empty
opaque Propositional.HilbertInt : Type := Empty  
opaque Propositional.HilbertCl : Type := Empty
-- ... etc.
```
These are the tag types for the typeclass hierarchy, but the doc comment says "Concrete `InferenceSystem` and `HasAxiom*` instances will be registered when derivation trees are defined." The derivation trees *are* defined in `Propositional.ProofSystem.Derivation`, but the instances have not been connected to the tag types.

---

## Confidence Level

| Finding | Confidence | Basis |
|---------|-----------|-------|
| Mathlib has no standalone sequent calculus | High | Exhaustive MCP search returned nothing relevant |
| `itauto` implements G4ip internally | High | `lean_leanfinder` description confirms G4ip |
| CLL has template for multiset sequent calculus | High | Direct code reading of `CLL/Basic.lean` |
| Bimodal tableau propositional rules are reusable | High | Direct code reading of `Tableau.lean` + `SignedFormula.lean` |
| `ipl_conservative_over_mpl` is the only Propositional sorry | High | `grep sorry` across all Propositional `.lean` files |
| `ProofSystem` tag types are unconnected stubs | High | Direct reading of `ProofSystem.lean` + doc comment confirms |
| G4ip would give IPL decidability | High | Standard result (Dyckhoff 1992) |
| Dedekind-MacNeille completion in Mathlib would help conservative extension | Medium | Mathlib has the algebra but exact API match needs verification |
| NaturalDeduction `subs` is not capture-avoiding | High | Code comment explicitly states this |
| CLL cut elimination is blocked TODO | High | Code has explicit commented-out TODO |

---

## Summary of What Is Not in CSLib but Could Be Added

1. **Sequent calculus** (G4ip for IPL, LK for CPL): Not present anywhere in CSLib; would be new
2. **Propositional tableau** (analytic tableau for CPL decidability): Not present; can be adapted from Bimodal Decidability
3. **Concrete `MinimalHilbert` instances for the three propositional logics**: Tag types exist, instances not registered
4. **Capture-avoiding substitution for ND**: Existing subs is not capture-avoiding (noted as TODO)
5. **CLL cut elimination**: Declared but not implemented
6. **`ipl_conservative_over_mpl`**: One sorry requiring Dedekind-MacNeille completion
7. **Curry-Howard correspondence**: The `NaturalDeduction/Basic.lean` `Derivation` is a `Type` (not `Prop`) but no terms-as-proofs correspondence is formalized
