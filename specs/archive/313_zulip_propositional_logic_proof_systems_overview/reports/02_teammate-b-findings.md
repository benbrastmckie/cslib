# Teammate B Findings: Cross-System Equivalence Bridges and Conservative Extension Chain

**Task 313** — Research for Zulip comment on CSLib propositional logic proof systems
**Focus**: Cross-system equivalence bridges, conservative extension chain, and gap analysis

---

## 1. The Three Logics: Axiom Differentiation

CSLib defines three propositional logics as Hilbert systems with a shared axiom core, distinguished by additional axioms:

| Logic | Axiom Type | Extra Axiom(s) vs. Previous | Algebraic Semantics |
|-------|-----------|--------------------------|---------------------|
| MPL (Minimal) | `MinPropAxiom` | K, S, andI/E, orI/E (no bottom axiom) | GHA (GeneralizedHeytingAlgebra) |
| IPL (Intuitionistic) | `IntPropAxiom` | + efq: `⊥ → φ` | HA (HeytingAlgebra) |
| CPL (Classical) | `PropositionalAxiom` | + peirce: `((φ→ψ)→φ)→φ` | BA (BooleanAlgebra) |

The axiom subsumption chain is formally proved:
- `MinPropAxiom.toIntPropAxiom`: every minimal axiom is intuitionistic
- `IntPropAxiom.toPropositionalAxiom`: every intuitionistic axiom is classical (implied)

The key differentiators:
- MPL → IPL: adding EFQ (`⊥ → φ`) — explosion/ex falso quodlibet
- IPL → CPL: adding Peirce's law (`((φ→ψ)→φ)→φ`) — equivalent to double-negation elimination

---

## 2. Complete Equivalence Map

### 2.1 Hilbert ↔ Natural Deduction

**File**: `NaturalDeduction/Equivalence.lean`

This is the most thoroughly established cross-system bridge. The equivalences are:

```
Hilbert (Deriv Axioms Γ.toList φ)
    ⟺ [hilbert_iff_nd_ctx]
Natural Deduction (DerivableIn (AxiomTheory Axioms) (Γ ⊢ φ))
```

**Established for all three logics** via a single generic parameterized theorem:

| Theorem | Logic | Form |
|---------|-------|------|
| `hilbert_iff_nd_ctx_min` | MPL | Context-based (`Γ`) |
| `hilbert_iff_nd_ctx_int` | IPL | Context-based (`Γ`) |
| `hilbert_iff_nd_ctx_cl` | CPL | Context-based (`Γ`) |
| `hilbert_iff_nd_min` | MPL | Empty context (`∅`) |
| `hilbert_iff_nd_int` | IPL | Empty context (`∅`) |
| `hilbert_iff_nd_cl` | CPL | Empty context (`∅`) |

**Mechanism**: The `MinimalAxioms` typeclass bundles 8 axiom witnesses (K, S, andI/E, orI/E) needed for the ND-to-Hilbert translation direction (via the deduction theorem). All three axiom predicates provide this instance.

**Translation functions**:
- `hilbertToND`: Computable, structural. Hilbert `ax`→ND `ax`; `assumption`→ND `ass`; MP→ND `impE`; `weakening`→ND `weakCtx`.
- `ndToHilbert`: Noncomputable (uses `deductionTheorem` which requires `Classical.propDecidable`). The `impI` case applies the deduction theorem; `orE` reconstructs via Hilbert OrE + deduction theorem on branches.

### 2.2 Hilbert ↔ Sequent Calculus (LK — Classical)

**Files**: `SequentCalculus/LK/Completeness.lean`, `SequentCalculus/LK/Soundness.lean`

```
Hilbert CPL (Deriv PropositionalAxiom Γ.toList φ)
    ⟺ [hilbert_iff_lk]
LK Sequent Calculus (Nonempty (LKProof (Γ ⊢ₛ {φ})))
```

Established via three-way composition:
1. `hilbert_iff_nd_ctx_cl`: Hilbert ↔ ND (see §2.1)
2. `nd_iff_lk`: ND ↔ LK

The `nd_iff_lk` bridge:
- **Forward**: `ndToLK` — structural translation, ND derivation → LK proof of `Γ ⊢ₛ {A}`
- **Backward**: LK soundness (`LKProof.sound`) → semantic validity → `prop_strong_completeness` → Hilbert → ND

Additional corollaries:
- `lk_completeness`: Every tautology has an LK proof
- `lk_iff_tautology`: `Tautology φ ↔ Nonempty (LKProof (∅ ⊢ₛ {φ}))` (full soundness + completeness)

**Cut elimination** (`LK/CutElimination.lean`): `LKProof.cutElim` — every LK-derivable sequent has a cut-free proof. Proved via structural induction on the cut formula.

### 2.3 Hilbert ↔ Sequent Calculus (LJ — Intuitionistic)

**Files**: `SequentCalculus/LJ/Completeness.lean`, `SequentCalculus/LJ/Soundness.lean`

```
Hilbert IPL (Deriv IntPropAxiom Γ.toList φ)
    ⟺ [hilbert_iff_lj]
LJ Sequent Calculus (Nonempty (LJProof (Γ ⊢ φ)))
```

Same three-way composition pattern:
1. `hilbert_iff_nd_ctx_int`: Hilbert ↔ ND
2. `nd_iff_lj`: ND ↔ LJ

The `nd_iff_lj` bridge:
- **Forward**: `ndToLJ` — structural translation
- **Backward**: LJ Kripke soundness (`LJProof.sound`) → `ISemanticEntails` → `int_strong_completeness` → Hilbert → ND

Corollary:
- `lj_iff_ivalid`: `IValid φ ↔ Nonempty (LJProof (∅ ⊢ φ))` (full Kripke soundness + completeness for LJ)

**Cut elimination** (`LJ/CutElimination.lean`): `LJProof.cutElim` — proved by well-founded induction on `(sizeOf A, d₁.height + d₂.height)` under lexicographic ordering.

**Note on LJ vs LK**: LJ uses a single-conclusion sequent (`Γ ⊢ A`) while LK uses a multi-conclusion sequent (`Γ ⊢ₛ Δ`). This structural difference correctly distinguishes intuitionistic from classical logic.

### 2.4 Tableau Systems

**Files**: `Tableau/Classical/`, `Tableau/Intuitionistic/`, `Tableau/Minimal/`

The tableau systems exist but have a different status from the sequent calculi:

**Classical Tableau** (`classicalTableau`):
- Soundness/completeness proofs marked `sorry` (flagged in module docstrings)
- `Decidable (Tautology φ)` instance: structurally sorry-free via tableau; existing `instDecidableTautology` in `Bool.lean` provides the primary sorry-free instance
- `Decidable (Derivable PropositionalAxiom φ)` via `prop_completeness_iff_tautology`
- Bridge to Hilbert/ND: indirect, via `prop_completeness_iff_tautology` in the decision procedure

**Intuitionistic Tableau** (`intuitionisticTableau`):
- Kripke soundness/completeness proofs marked `sorry`
- `Decidable (IValid φ)` provided (structure sorry-free)

**Minimal Tableau** (`minimalTableau`):
- Reuses intuitionistic expansion with `MinimalClosure`
- Key semantic difference: T(⊥) does NOT close a branch (⊥ can be forced)
- Soundness/completeness marked `sorry`
- `Decidable (MValid φ)` provided; `Decidable (Derivable MinPropAxiom φ)` via this
- `min_soundness_completeness` promised in module header

**Current tableau bridge status**: The tableau systems currently have no formally proved direct bridge to Hilbert or sequent calculus — the connections are asserted but the proofs are deferred (sorry). The decision procedures are connected indirectly through the existing boolean/Kripke completeness infrastructure.

---

## 3. Algebraic Semantics Bridges

### 3.1 The Three Algebraic Completeness Results

Three Hilbert algebraic completeness theorems form the backbone of the conservative extension and Glivenko results:

| System | Algebraic Structure | Completeness | File |
|--------|--------------------|--------------|----|
| MPL | GHA (GeneralizedHeytingAlgebra) | `MPL.hilbert_alg_complete` | `HilbertCompleteness.lean` |
| IPL | HA (HeytingAlgebra) | `IPL.hilbert_alg_complete` | `HilbertCompleteness.lean` |
| CPL | BA (BooleanAlgebra) | `CPL.hilbert_alg_complete` | `HilbertCompleteness.lean` |

**Algebraic bridges** (in `HilbertConservativeGlivenko.lean`):
- `derivableInMplIffDerivableMin`: `DerivableIn ∅ φ ↔ Derivable MinPropAxiom φ`
- `derivableInIplIffDerivableInt`: `DerivableIn IPL φ ↔ Derivable IntPropAxiom φ`
- `derivableInCplIffDerivableProp`: `DerivableIn (IPL ∪ CPL) φ ↔ Derivable PropositionalAxiom φ`

### 3.2 Kripke–Algebraic Bridge

**File**: `Semantics/Algebra/KripkeBridge.lean`

The central theorem `kripkeAlgBridge` establishes:
```
IForces v bf w φ ↔ toDual w ∈ AlgEvaluate (upsetVal v hv) (upsetBotVal bf hbf) φ
```

Upsets of a Kripke preorder (represented as lower sets of `OrderDual World`) form a HeytingAlgebra. This connects Kripke semantics to algebraic semantics bidirectionally.

Corollaries:
- `iValidOfHAValid`: HA-validity → intuitionistic Kripke validity
- `mValidOfGHAValid`: GHA-validity → minimal Kripke validity

### 3.3 Evaluator Bridge

**File**: `Semantics/Algebra/Bridge.lean`

- `propEvaluateEq`: Classical Prop-valued `Evaluate v φ ↔ AlgEvaluate (v·) False φ` (Prop as HeytingAlgebra)
- `boolEvaluateEq`: Bool-valued `BoolEvaluate v φ = AlgEvaluate (v·) false φ` (Bool as BooleanAlgebra)

### 3.4 Hilbert Algebra

**File**: `Foundations/Order/HilbertAlgebra.lean`

`HilbertAlgebra` is the algebraic semantics for the purely implicational fragment IPL⟨→,⊤⟩:
```
class HilbertAlgebra H extends HImp H, Top H where
  himp_K : a ⇨ (b ⇨ a) = ⊤     -- K combinator
  himp_S : ...                   -- S combinator
  himp_antisymm : ...            -- induced partial order antisymmetry
  himp_self : a ⇨ a = ⊤         -- reflexivity
```
Every BrouwerianSemilattice (and hence every GHA) is a HilbertAlgebra.

**File**: `Semantics/Algebra/HilbertAlgCompleteness.lean`

`imp_hilbert_iff`: For `IsImpTopOnly` formulas: `Derivable ImpAxiom φ ↔ HilbertValid φ`

---

## 4. Conservative Extension Chain

### 4.1 Full Chain

The conservative extension chain, from smallest to largest fragment:

```
ImpAxiom ⊆ ConjImpAxiom ⊆ ConjImpBotAxiom ⊆ MinPropAxiom ⊆ IntPropAxiom ⊆ PropositionalAxiom

IPL⟨→,⊤⟩ ⊆ IPL⟨∧,→,⊤⟩ ⊆ IPL⟨∧,→,⊥,⊤⟩ ⊆ MPL ⊆ IPL ⊆ CPL
```

Conservative extension results proved:

| Theorem | Conservative Extension | Restriction | Method |
|---------|----------------------|-------------|--------|
| `hilbertIplConservativeOverMpl` | IPL conservative over MPL | `IsBotFree` | `WithBot` GHA embedding |
| `ipl_conservative_over_mpl` (ND corollary) | IPL conservative over MPL | `IsBotFree` | via algebraic bridges |
| `hilbertIplConservativeOverConjImp` | IPL conservative over IPL⟨∧,→,⊤⟩ | `IsOrBotFree` | `LowerSet` HA (Brouwerian) |
| `ipl_conservative_over_conjImp` (ND corollary) | IPL conservative over IPL⟨∧,→,⊤⟩ | `IsOrBotFree` | via algebraic bridges |
| `hilbertIplConservativeOverConjImpBot` | IPL conservative over IPL⟨∧,→,⊥,⊤⟩ | `IsOrFree` | `NonemptyLowerSet` HA |
| `ipl_conservative_over_conjImpBot` (ND corollary) | IPL conservative over IPL⟨∧,→,⊥,⊤⟩ | `IsOrFree` | via algebraic bridges |

**Key technical insight**: Each conservativity result requires a different algebraic model:
- `WithBot G`: extends a GHA with a fresh bottom → handles bot-free formulas
- `LowerSet B` (Brouwerian semilattice): handles or-bot-free formulas
- `NonemptyLowerSet B` (pointed Brouwerian): handles or-free formulas (preserves `⊥` unlike `LowerSet`)

**Subsumption direction** (the "free" direction) is proved structurally via `liftDerivationTree` for all cases.

### 4.2 Glivenko's Theorem

**Files**: `Semantics/Algebra/Glivenko.lean`, `Semantics/Algebra/HilbertConservativeGlivenko.lean`

```
hilbertGlivenko: Derivable PropositionalAxiom φ → Derivable IntPropAxiom (¬¬φ)
glivenko (ND): DerivableIn (IPL ∪ CPL) φ → DerivableIn IPL (¬¬φ)
```

**Method**: `glivenko_algebraic` — if `φ` is BA-valid, then `¬¬φ` is HA-valid. Uses the regular elements of a Heyting algebra: `Heyting.Regular H` is a BooleanAlgebra, and lifting the valuation via double-complement gives the result.

The ND version `glivenko` serves as the main result connecting CPL derivability to IPL derivability.

---

## 5. Fragment System Architecture

### 5.1 Fragment Axiom Predicates (FragmentAxioms.lean)

Four fragment predicates form a subsumption chain:

```
ImpAxiom ⊆ ConjImpAxiom ⊆ ConjImpBotAxiom ⊆ MinPropAxiom (⊆ IntPropAxiom ⊆ PropositionalAxiom)
```

Each fragment has:
- Substitution closure (`subst_preserves_*`)
- Deduction theorem instance (`hasDeductionTheorem`)
- Fragment predicate compatibility lemmas (e.g., applying constructors to `IsOrBotFree` formulas preserves `IsOrBotFree`)

### 5.2 Fragment Predicates (FragmentPredicates.lean)

Formula classification predicates used in conservative extension theorems:
- `IsBotFree`: formula mentions no `⊥`
- `IsOrBotFree`: formula mentions neither `∨` nor `⊥`
- `IsOrFree`: formula mentions no `∨`
- `IsImpTopOnly`: formula uses only `→` and `⊤` (for Hilbert algebra completeness)

---

## 6. Equivalence Diagram

```
                        ALGEBRAIC SEMANTICS
    GHAValid (MPL) ←─── HAValid (IPL) ←─── BAValid (CPL)
         ↕                    ↕                  ↕
    Derivable             Derivable          Derivable
   MinPropAxiom  ←─────  IntPropAxiom ←──── PropositionalAxiom
         ↕                    ↕                  ↕
    Hilbert ↔ ND_MPL     Hilbert ↔ ND_IPL   Hilbert ↔ ND_CPL
    [hilbert_iff_nd_min] [hilbert_iff_nd_int] [hilbert_iff_nd_cl]
                              ↕                  ↕
                         ND_IPL ↔ LJ_IPL    ND_CPL ↔ LK_CPL
                        [nd_iff_lj]          [nd_iff_lk]
                              ↕                  ↕
                         LJProof ↔ IValid   LKProof ↔ Tautology
                        [lj_iff_ivalid]      [lk_iff_tautology]
                              ↕                  ↕
                         KRIPKE IPL          BOOL/PROP CPL

                    CONSERVATIVE EXTENSIONS (vertical direction):
    MPL ← (bot-free) ── IPL ← (Glivenko: ¬¬) ── CPL
    ConjImp ← (or-bot-free) ── IPL
    ConjImpBot ← (or-free) ── IPL
```

### Cross-System Equivalence Inventory

| Source | Target | Bridge Theorem | Status |
|--------|--------|----------------|--------|
| Hilbert MPL | ND MPL | `hilbert_iff_nd_min` / `hilbert_iff_nd_ctx_min` | PROVED |
| Hilbert IPL | ND IPL | `hilbert_iff_nd_int` / `hilbert_iff_nd_ctx_int` | PROVED |
| Hilbert CPL | ND CPL | `hilbert_iff_nd_cl` / `hilbert_iff_nd_ctx_cl` | PROVED |
| ND IPL | LJ IPL | `nd_iff_lj` | PROVED |
| ND CPL | LK CPL | `nd_iff_lk` | PROVED |
| Hilbert IPL | LJ IPL | `hilbert_iff_lj` (composition) | PROVED |
| Hilbert CPL | LK CPL | `hilbert_iff_lk` (composition) | PROVED |
| LK CPL | Tautology | `lk_iff_tautology` | PROVED |
| LJ IPL | IValid | `lj_iff_ivalid` | PROVED |
| Hilbert MPL | ND MPL | via `derivableInMplIffDerivableMin` | PROVED |
| Classical Tableau | Tautology | `classicalTableau_sound/complete` | SORRY (decision proc OK) |
| Intuitionistic Tableau | IValid | `intuitionisticTableau_sound/complete` | SORRY (decision proc OK) |
| Minimal Tableau | MValid | `minimalTableau_sound/complete` | SORRY (decision proc OK) |
| LK | LJ (CPL/IPL interplay) | (none direct) | MISSING |
| Tableau | Sequent Calculus | (none) | MISSING |
| Hilbert MPL | LJ/LK | (none direct) | MISSING |

---

## 7. Gap Analysis

### 7.1 Tableau Soundness/Completeness Proofs

**Status**: All three tableau systems (classical, intuitionistic, minimal) have soundness and completeness proofs marked `sorry`. The module docstrings explicitly acknowledge this:

- `Classical/Soundness.lean`: "key lemmas are stated and their proofs are marked sorry"
- `Classical/Completeness.lean`: "Full proof is marked sorry"
- `Intuitionistic/Soundness.lean`: "The formal loop induction is marked sorry"
- `Minimal/DecisionProcedure.lean`: "Soundness and completeness proofs are marked sorry"

**Impact**: The `Decidable` instances are structurally correct but rest on sorry-tagged lemmas. The primary sorry-free decision procedure for CPL uses boolean enumeration (`instDecidableTautology` in `Bool.lean`).

**Path to resolution**: Each requires formalizing the branch expansion loop induction — the main difficulty is the fuel-based loop termination argument.

### 7.2 Missing Bridge: Hilbert MPL ↔ LJ/LK

There is no direct Hilbert MPL ↔ LJ or LK equivalence bridge. The Hilbert–LJ bridge exists only for IPL (`hilbert_iff_lj`); the Hilbert–LK bridge only for CPL (`hilbert_iff_lk`). A minimal sequent calculus (analogous to LJ without the botL rule) would be needed to complete this picture.

### 7.3 Missing Bridge: Tableau ↔ Sequent Calculus

No formal bridge exists between the tableau systems and the sequent calculi. Such bridges would be natural cross-system results showing these are different decision procedures for the same logics.

### 7.4 LK–LJ Relationship

There is no formal theorem in CSLib stating that LK is an extension of LJ (or comparing their provability). The structural difference (multi-conclusion vs. single-conclusion) is exploited in the completeness proofs but not stated as a cross-system theorem.

### 7.5 No Formal Hilbert CPL ↔ Hilbert IPL Bridge via Peirce

While the axiom subsumption `IntPropAxiom → PropositionalAxiom` is proved and the Glivenko embedding `glivenko` is proved, there is no theorem of the form "CPL ⊢ φ iff IPL ⊢ ¬¬φ is a tautology" (the Glivenko translation in full generality). The current `glivenko` theorem goes one direction: CPL provability implies IPL provability of `¬¬φ`.

---

## 8. The Vision: All Four Systems Equivalent for All Three Logics

The current state and the natural vision can be summarized as follows:

**Fully established** (all three logics):
- Hilbert ↔ ND (all three logics, with and without context)

**Partially established** (two of three logics):
- Hilbert ↔ LJ (IPL only)
- Hilbert ↔ LK (CPL only)
- Sequent calculus ↔ semantic validity (IPL via Kripke, CPL via Boolean semantics)
- Cut elimination (both LJ and LK)

**Structurally present but sorry-dependent** (all three logics):
- Tableau soundness/completeness (classical, intuitionistic, minimal)
- Tableau decision procedures (structurally sorry-free but depend on sorry-tagged lemmas)

**Missing**:
- Hilbert MPL ↔ LJ (a "minimal sequent calculus" LM would need to be designed)
- Any tableau ↔ sequent calculus bridge
- LK ↔ LJ formal comparison

The dominant advantage structure for each system:
- **Hilbert**: cleanest for metatheoretic work (deduction theorem, soundness/completeness via algebra, conservative extensions)
- **ND**: most natural for proof construction; Curry-Howard correspondence
- **Sequent Calculus**: best for structural proof theory (cut elimination, proof search)
- **Tableau**: algorithmic decision procedures with direct countermodel extraction

The conservative extension results establish a rich fragment hierarchy unique to the algebraic approach: the IPL/MPL relationship for bot-free and or-free fragments is formalized in a way that goes significantly beyond what the proof-system equivalences alone would provide.
