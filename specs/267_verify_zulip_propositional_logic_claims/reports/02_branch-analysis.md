# Branch Analysis: Thomas Waring's Intuitionistic ND vs CSLib Main

**Task**: 267 -- verify_zulip_propositional_logic_claims
**Date**: 2026-06-22
**Session**: sess_1782155940_pIuU3o
**Branch**: `thomaskwaring/cslib_SKI` branch `intuitionistic`
**File analyzed**: `Cslib/Logics/Propositional/NaturalDeduction/Intuitionistic.lean`
**Reference**: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (branch version)

---

## 1. File Overview: Thomas's Intuitionistic.lean

### Imports
- `Cslib.Logics.Propositional.NaturalDeduction.Basic` (his own Basic.lean)
- `Mathlib.Order.WithBot`

### Namespace
- `Cslib.Logic.PL`

### Key Definitions (complete inventory)

| # | Declaration | Kind | Type/Signature |
|---|-------------|------|----------------|
| 1 | `IProposition` | `inductive` | `(Atom : Type u) : Type u` with constructors: `atom`, `or`, `and`, `impl`, `bot` |
| 2 | `IProposition.neg` | `abbrev` | `IProposition Atom -> IProposition Atom` (defined as `impl . bot`) |
| 3 | `IProposition.top` | `abbrev` | `IProposition Atom` (defined as `impl bot bot`) |
| 4 | `ICtx` | `abbrev` | `Finset (IProposition Atom)` |
| 5 | `ITheory` | `abbrev` | `Set (IProposition Atom)` |
| 6 | `ITheory.IDerivation` | `inductive` | `ICtx Atom -> IProposition Atom -> Type u` with constructors: `ax`, `ass`, `conjI`, `conjE1`, `conjE2`, `disjI1`, `disjI2`, `disjE`, `implI`, `implE`, **`efq`** |
| 7 | `Proposition.toIProposition` | `def` | `Proposition (WithBot Atom) -> IProposition Atom` |
| 8 | `IProposition.toProposition` | `def` | `IProposition Atom -> Proposition (WithBot Atom)` |
| 9 | `propEquiv` | `def` | `Proposition (WithBot Atom) ~= IProposition Atom` (an `Equiv`) |
| 10 | `Ctx.toICtx` | `def` | `Ctx (WithBot Atom) -> ICtx Atom` |
| 11 | `ICtx.toCtx` | `def` | `ICtx Atom -> Ctx (WithBot Atom)` |
| 12 | `Theory.toITheory` | `def` | `Theory Atom -> ITheory Atom` |
| 13 | `ITheory.toTheory` | `def` | `ITheory Atom -> Theory (WithBot Atom)` |
| 14 | `Theory.iCompletion` | `def` | `Theory Atom -> Theory (WithBot Atom)` |
| 15 | `Theory.toTheory_toITheory` | `lemma` | `T.toITheory.toTheory = T.iCompletion` |
| 16 | `ITheory.IDerivation.toDerivation` | `def` | `T.IDerivation Gamma A -> T.toTheory.Derivation Gamma.toCtx A.toProposition` |
| 17 | `Theory.Derivation.toIDerivation` | `noncomputable def` | `T.iCompletion.Derivation Gamma A -> T.toITheory.IDerivation Gamma.toICtx A.toIProposition` |

### Simp lemmas
- `Ctx.toICtx_insert`
- `ICtx.toCtx_insert`

---

## 2. Claim-by-Claim Verification: Does CSLib Main Have Equivalents?

| # | Thomas's Declaration | CSLib Main Equivalent? | Confidence | Notes |
|---|---------------------|----------------------|------------|-------|
| 1 | `IProposition` (separate inductive) | **NO** | HIGH | CSLib main has a single `Proposition` type with primitive `bot` constructor. No separate `IProposition` type exists. |
| 2 | `IProposition.neg` | **YES** (equivalent) | HIGH | CSLib main: `Proposition.neg` defined as `Proposition.imp . .bot`. Same definition. |
| 3 | `IProposition.top` | **YES** (equivalent) | HIGH | CSLib main: `Proposition.top` defined as `.imp .bot .bot`. Same definition. |
| 4 | `ICtx` (Finset of IProposition) | **NO** (as separate type) | HIGH | CSLib uses `Ctx Atom := Finset (Proposition Atom)`. No `ICtx`. |
| 5 | `ITheory` (Set of IProposition) | **NO** (as separate type) | HIGH | CSLib uses `Theory Atom := Set (Proposition Atom)`. No `ITheory`. |
| 6 | `ITheory.IDerivation` with `efq` constructor | **NO** (different design) | HIGH | CSLib main's `Theory.Derivation` has 10 primitive constructors (no `efq`). `efq`/`botE` is a derived rule requiring `[IsIntuitionistic T]`. See Design Comparison below. |
| 7 | `Proposition.toIProposition` | **NO** | HIGH | Not needed in CSLib main -- there is only one proposition type. |
| 8 | `IProposition.toProposition` | **NO** | HIGH | Not needed -- no dual type to convert from. |
| 9 | `propEquiv` | **NO** | HIGH | Not needed -- CSLib main does not have two proposition types to establish equivalence between. |
| 10 | `Ctx.toICtx` | **NO** | HIGH | Not needed -- single context type. |
| 11 | `ICtx.toCtx` | **NO** | HIGH | Not needed -- single context type. |
| 12 | `Theory.toITheory` | **NO** | HIGH | Not needed -- single theory type hierarchy. |
| 13 | `ITheory.toTheory` | **NO** | HIGH | Not needed -- single theory type hierarchy. |
| 14 | `Theory.iCompletion` | **PARTIAL** | HIGH | CSLib main has `Theory.intuitionisticCompletion` with the same definition: `(WithBot.some <$> T) ∪ IPL`. Thomas calls it `iCompletion`, CSLib calls it `intuitionisticCompletion`. Same semantics. |
| 15 | `toTheory_toITheory` | **NO** | HIGH | Cannot exist in CSLib main because `toITheory` does not exist. |
| 16 | `IDerivation.toDerivation` | **NO** | HIGH | Not needed -- CSLib has no `IDerivation` to convert from. The concept is subsumed by `Derivation.weak` + theory monotonicity. |
| 17 | `Derivation.toIDerivation` | **NO** | HIGH | Not needed -- CSLib main does not split derivation types. The concept is subsumed by the `[IsIntuitionistic T]` typeclass approach. |

### Summary Counts
- **YES** (direct equivalent): 2 (`neg`, `top`)
- **PARTIAL** (similar but renamed/restructured): 1 (`iCompletion` / `intuitionisticCompletion`)
- **NO** (not present, by design): 14

---

## 3. Design Comparison: Key Structural Differences

### 3.1 Proposition Type Architecture

| Aspect | Thomas's Branch | CSLib Main |
|--------|----------------|------------|
| Proposition types | Two: `Proposition` (minimal, no `bot`) and `IProposition` (with `bot`) | One: `Proposition` (with primitive `bot`) |
| How bot enters | `IProposition.bot` is a constructor; minimal `Proposition` has no bot | `Proposition.bot` is a primitive constructor shared by MPL/IPL/CPL |
| Atom type trick | Uses `WithBot Atom` to adjoin bot to minimal propositions | Not needed -- `bot` is always available |

**Implications**: Thomas's design requires an explicit `propEquiv : Proposition (WithBot Atom) ~= IProposition Atom` equivalence to bridge the two types. CSLib main avoids this entirely by having a single type with `bot` always present. The trade-off is that CSLib's `Proposition` type for minimal logic (MPL) includes a `bot` constructor that is semantically inert in MPL (no elimination rule), while Thomas's design is cleaner for MPL (no bot at all).

### 3.2 Derivation System Design

| Aspect | Thomas's Branch | CSLib Main |
|--------|----------------|------------|
| efq placement | Constructor of `IDerivation` (11 constructors total) | **Derived rule** via theory axiom + `impE` (10 constructors) |
| Logic strength | Controlled by choosing `Derivation` (minimal) vs `IDerivation` (intuitionistic) | Controlled by theory parameter: `MPL`, `IPL`, `CPL` via typeclasses |
| Typeclass support | None (separate inductive types) | `IsIntuitionistic T`, `IsClassical T` typeclasses |
| Extensibility | Add new inductive for each logic (classical would need yet another type) | Add new axiom schema to theory; same `Derivation` type |

**Key CSLib main design**: `botE` is defined as:
```lean
def Theory.Derivation.botE [IsIntuitionistic T] (d : T.Derivation Gamma bot) : T.Derivation Gamma A :=
  Derivation.impE (Derivation.ax (IsIntuitionistic.efq A)) d
```
This derives efq from the theory axiom `bot -> A` using modus ponens. The `[IsIntuitionistic T]` typeclass guarantees `(bot -> A) in T`.

### 3.3 Computability

| Aspect | Thomas's Branch | CSLib Main |
|--------|----------------|------------|
| `toDerivation` (I -> minimal) | Computable (`def`) | N/A (no dual type) |
| `toIDerivation` (minimal -> I) | **`noncomputable def`** | N/A |
| Why noncomputable? | The `ax` case uses `Classical.choose` to witness the IPL axiom form | CSLib avoids this entirely |

Thomas's `toIDerivation` is noncomputable because when translating a minimal derivation's `ax hA` case, it needs to determine whether the axiom `A` belongs to `IPL` or to the original theory. If `A in IPL (WithBot Atom)`, it must construct the corresponding intuitionistic derivation, which requires `Classical.choose_spec hA'` to extract the proposition for which `bot -> A` holds. The `by_cases hA' : A in IPL (WithBot Atom)` introduces classical reasoning.

### 3.4 Naming Conventions

| Thomas's Branch | CSLib Main |
|----------------|------------|
| `conjI`, `conjE1`, `conjE2` | `andI`, `andE1`, `andE2` |
| `disjI1`, `disjI2`, `disjE` | `orI1`, `orI2`, `orE` |
| `implI`, `implE` | `impI`, `impE` |
| `iCompletion` | `intuitionisticCompletion` |
| Context param: implicit `{Gamma}` on most rules | Context param: explicit `(G : Ctx Atom)` on most rules |

### 3.5 Theory-Based vs Type-Based Logic Hierarchy

Thomas's branch uses a **type-based** approach:
- `Derivation` (minimal logic) vs `IDerivation` (intuitionistic) are separate inductive types
- Adding classical logic would require a third inductive type with yet more constructors
- Translation between logics requires explicit conversion functions (`toDerivation`, `toIDerivation`)

CSLib main uses a **theory-based** approach:
- Single `Derivation` type parametrized by theory `T`
- Logic strength controlled by what axioms `T` contains
- `IsIntuitionistic T` (has `bot -> A`) and `IsClassical T` (has `neg neg A -> A`) are typeclasses
- Extending to new logics = defining new axiom schemas and typeclass instances
- No conversion functions needed; monotonicity (`weakTheory`) handles theory extension

---

## 4. Thomas's Basic.lean vs CSLib Main's Basic.lean

Thomas's `Basic.lean` on the branch and CSLib main's `Basic.lean` are structurally very similar (Thomas is the original author of both). Key differences:

| Feature | Thomas's Branch Basic.lean | CSLib Main Basic.lean |
|---------|---------------------------|----------------------|
| Constructor naming | `conjI`/`conjE1`/`disjI1`/`implI`/`implE` | `andI`/`andE1`/`orI1`/`impI`/`impE` |
| Context parameter | Mostly implicit `{Gamma}` | Mostly explicit `(G : Ctx Atom)` |
| Copyright | Thomas Waring only | Thomas Waring + Benjamin Brast-McKie |
| Module doc design notes | References Zulip discussion link | Expanded design trade-off documentation |
| `[Inhabited Atom]` requirement | Present on `derivationTop`, `derivable_iff_equiv_top` | Removed (not needed) |
| Congruence lemmas | Not present | `Equiv.imp_congr`, `Equiv.and_congr`, `Equiv.or_congr` added |

The core `Derivation` inductive and derived operations (weak, cut, subs, substAtom, equiv) are the same in both. CSLib main has been extended with congruence lemmas and DerivedRules.lean.

---

## 5. What CSLib Main Has That Thomas's Branch Does Not

CSLib main has significant additional infrastructure beyond what Thomas's branch provides:

1. **DerivedRules.lean**: Full suite of derived rules (`botE`, `negI`, `negE`, `topI`, `dne`, `iffI`, `iffE1`, `iffE2`) with both `Derivation`-level and `DerivableIn`-level versions.

2. **Equivalence.lean**: Bridge between ND and Hilbert proof systems (`hilbert_iff_nd`, `hilbert_iff_nd_min`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`) for all three logic strengths.

3. **ProofSystem/**: Complete Hilbert-style proof system (`DerivationTree`, `MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom`) with instance registration.

4. **Metalogic/**: Soundness and strong completeness proofs for all three logics (minimal, intuitionistic, classical), deduction theorem, Lindenbaum's lemma, MCS theory.

5. **Semantics/**: Algebraic semantics (Heyting algebra-based), Kripke semantics, boolean semantics, and bridges between them.

6. **Congruence lemmas**: `Equiv.imp_congr`, `Equiv.and_congr`, `Equiv.or_congr` in Basic.lean.

7. **Typeclass hierarchy**: `IsIntuitionistic`, `IsClassical` typeclasses with monotonicity lemmas, connected to the Foundations `InferenceSystem` infrastructure.

---

## 6. What Thomas's Branch Has That CSLib Main Does Not

Thomas's branch provides exactly one thing that CSLib main does not:

1. **Explicit `IProposition`/`IDerivation` types with `propEquiv` bridge**: The file establishes a formal type-level equivalence between minimal logic (with `WithBot Atom`) and genuine intuitionistic logic (with primitive `bot` and `efq` rule). This is a mathematical result showing that the two formulations are inter-derivable.

This is not present in CSLib main because CSLib's hybrid design (primitive `bot` + derived `efq`) makes it unnecessary -- the two formulations are collapsed into one type parametrized by the theory.

---

## 7. Confidence Assessment

| Finding | Confidence |
|---------|-----------|
| CSLib main has NO `IProposition` or `IDerivation` types | HIGH -- confirmed by exhaustive grep |
| CSLib main has NO `propEquiv` | HIGH -- confirmed by grep |
| CSLib main has NO `toIDerivation` / `toDerivation` | HIGH -- confirmed by grep |
| CSLib main's efq is a derived rule, not a constructor | HIGH -- confirmed by reading `DerivedRules.lean` line 86-89 |
| Thomas's `toIDerivation` is noncomputable due to `Classical.choose` | HIGH -- confirmed by reading branch source code |
| `intuitionisticCompletion` in CSLib matches `iCompletion` in Thomas's branch | HIGH -- both are `(WithBot.some <$> T) ∪ IPL` |
| Thomas's branch Basic.lean is the ancestor of CSLib main's Basic.lean | HIGH -- copyright headers confirm shared authorship, core structure identical |
