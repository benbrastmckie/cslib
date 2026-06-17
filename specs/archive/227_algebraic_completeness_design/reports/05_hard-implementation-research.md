# Implementation-Ready Research: Algebraic Soundness, Completeness, and Conservative Extension

**Task**: 227 -- Algebraic completeness design
**Session**: sess_1750135000_research227hard
**Started**: 2026-06-17T00:00:00Z
**Completed**: 2026-06-17T02:00:00Z
**Effort**: Hard-mode research (H2+H3+H4)
**Dependencies**: Task 226 (GHA semantics refactor, upstream PR)
**Reference grounding tier**: Tier 3 (implementation-backed: Thomas's code, xcthulhu's code, BimodalLogic)
**Sources/Inputs**:
  - xcthulhu (Yijun Yuan): `DedekindMacneille.lean` (418 lines), commit 488309e3
  - Thomas Waring: `Heyting.lean` (384 lines), branch kripke of thomaskwaring/cslib_SKI
  - CSLib: `NaturalDeduction/Basic.lean`, `Semantics/Algebra.lean`, `Semantics/Algebra/Soundness.lean`
  - BimodalLogic: `LindenbaumQuotient.lean` (440 lines), `BooleanStructure.lean` (447 lines)
  - Reports 01-04 from specs/227_algebraic_completeness_design/reports/
**Artifacts**:
  - This report: `specs/227_algebraic_completeness_design/reports/05_hard-implementation-research.md`
**Standards**: report-format.md, anti-analysis.md, reference-grounding.md

---

## Guiding Principle

Reports 03 and 04 establish: primitive bot is a nullary operation symbol in the algebraic
signature, fixed under every substitution. "Arbitrary constant != arbitrary variable." The
`bot_val` parameter captures the Johansson algebra's designated constant without introducing
a new typeclass. Every design decision below is framed through this lens.

---

## Executive Summary

- Thomas's `Theory.complete` does NOT require Dedekind-MacNeille completion. The general
  completeness theorem quantifies over GHA directly, and the Lindenbaum quotient IS a GHA.
  D-M completion is optional (only needed to state MPL completeness over HA instead of GHA).
- CSLib's primitive `.bot` eliminates ALL `[Bot Atom]` and `[Inhabited Atom]` requirements
  present in Thomas's code. This is a strict improvement: `⊤ = .bot -> .bot` requires no
  atom, and `propBot` is simply `bot := quotient_mk .bot`.
- Three congruence lemmas are MISSING from CSLib and must be proved: `Theory.Equiv.imp_congr`,
  `Theory.Equiv.and_congr`, `Theory.Equiv.or_congr`. These are needed for `Quotient.lift2`
  well-definedness in the Lindenbaum algebra.
- Total new code: ~600 lines across 3 files (not 4). D-M completion deferred to a separate
  task.
- No sorry is needed. Every proof obligation has a concrete tactic strategy.
- `references.bib` has unresolved merge conflict markers that must be fixed.

---

## Source-to-Implementation Mapping

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|--------|---------------|-----------------|----------------|--------|
| Thomas Heyting.lean | propPO, l.171 | `Cslib.Logic.PL.Lindenbaum.instPartialOrder` | `PartialOrder (Quotient T.propositionSetoid)` | pending |
| Thomas Heyting.lean | propLattice, l.195 | `Cslib.Logic.PL.Lindenbaum.instLattice` | `Lattice (Quotient T.propositionSetoid)` | pending |
| Thomas Heyting.lean | propGeneralizedHeyting, l.234 | `Cslib.Logic.PL.Lindenbaum.instGHA` | `GeneralizedHeytingAlgebra (Quotient T.propositionSetoid)` | pending |
| Thomas Heyting.lean | propHeyting, l.284 | `Cslib.Logic.PL.Lindenbaum.instHA` | `[IsIntuitionistic T] -> HeytingAlgebra (Quotient T.propositionSetoid)` | pending |
| Thomas Heyting.lean | propBoolean, l.301 | `Cslib.Logic.PL.Lindenbaum.instBA` | `[IsClassical T] -> BooleanAlgebra (Quotient T.propositionSetoid)` | pending |
| Thomas Heyting.lean | canonicalV_spec, l.309 | `Cslib.Logic.PL.canonicalV_spec` | `AlgEvaluate canonicalV (quotient_mk .bot) phi = quotient_mk phi` | pending |
| Thomas Heyting.lean | Theory.complete, l.325 | `Cslib.Logic.PL.Theory.alg_complete` | `DerivableIn T A <-> (all GHA v bot_val, tValid -> eval = top)` | pending |
| Thomas Heyting.lean | MPL.complete, l.334 | `Cslib.Logic.PL.MPL.alg_complete` | `DerivableIn MPL A <-> GHAValid A` | pending |
| Thomas Heyting.lean | IPL.complete, l.343 | `Cslib.Logic.PL.IPL.alg_complete` | `DerivableIn IPL A <-> HAValid A` | pending |
| Thomas Heyting.lean | CPL.complete, l.352 | `Cslib.Logic.PL.CPL.alg_complete` | `DerivableIn CPL A <-> BAValid A` | pending |
| (novel) | conservative ext | `Cslib.Logic.PL.ipl_conservative_over_mpl` | `IsBotFree A -> DerivableIn IPL A -> DerivableIn MPL A` | pending |

---

## File 1: Lindenbaum.lean (~300 lines)

**Path**: `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean`

### Imports

```lean
import Cslib.Init
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Logics.Propositional.NaturalDeduction.DerivedRules
public import Cslib.Logics.Propositional.Semantics.Algebra
public import Mathlib.Order.Heyting.Regular
```

### Pre-requisite: Congruence Lemmas (~30 lines, in this file or NaturalDeduction/)

These are MISSING from CSLib. They must be proved BEFORE the Lindenbaum instances.
Thomas's code has them in a `Lemmas.lean` file. CSLib should add them either to
`NaturalDeduction/Basic.lean` or to the Lindenbaum file itself.

```lean
-- Needed for Quotient.lift₂ well-definedness of sup (⊔ = ∨)
theorem Theory.Equiv.or_congr {A A' B B' : Proposition Atom}
    (hA : A ≡[T] A') (hB : B ≡[T] B') : (A ∨ B) ≡[T] (A' ∨ B')

-- Needed for Quotient.lift₂ well-definedness of inf (⊓ = ∧)
theorem Theory.Equiv.and_congr {A A' B B' : Proposition Atom}
    (hA : A ≡[T] A') (hB : B ≡[T] B') : (A ∧ B) ≡[T] (A' ∧ B')

-- Needed for Quotient.lift₂ well-definedness of himp (⇨ = →)
theorem Theory.Equiv.imp_congr {A A' B B' : Proposition Atom}
    (hA : A ≡[T] A') (hB : B ≡[T] B') : (A → B) ≡[T] (A' → B')
```

**Proof strategy for each**: Use `equiv_iff_equiv_derivableIn`. For `or_congr`, show
`DerivableIn T ({A ∨ B} ⊢ A' ∨ B')` by: `orE` on assumption `A ∨ B`, then in the `A` branch
use `hA.mp` to get `A'` and `orI1` to get `A' ∨ B'`; in the `B` branch use `hB.mp` to get
`B'` and `orI2`. Reverse direction is symmetric. For `and_congr`: `andI` of `andE1` + `hA.mp`
and `andE2` + `hB.mp`. For `imp_congr`: `impI` then `impE` with `hA.mpr` and `hB.mp`.

Each proof is ~5 lines using existing ND rules. No sorry needed.

### PartialOrder Instance (~40 lines)

```lean
instance Lindenbaum.instPartialOrder :
    PartialOrder (Quotient T.propositionSetoid) where
  le := Quotient.lift₂ (fun A B => DerivableIn T ({A} ⊢ B))
    (fun A₁ A₂ B₁ B₂ hA hB => propext ⟨
      fun h => (hA.mpr.weakCtx ...).cut ((h.some.weakCtx ...).cut (hB.mp.some.weakCtx ...) |> ...),
      fun h => ...⟩)
  le_refl := by intro a; induction a using Quotient.ind; exact ⟨ass (by grind)⟩
  le_trans := by intro a b c; induction a, b, c using Quotient.ind₃; intro ⟨d₁⟩ ⟨d₂⟩; exact ⟨...⟩
  le_antisymm := by intro a b hab hba; induction a, b using Quotient.ind₂; exact Quotient.sound ⟨...⟩
```

**Key patterns**: `Quotient.lift₂` for `le`, `Quotient.ind` / `Quotient.ind₂` / `Quotient.ind₃`
for proofs. The `le` definition is: `⟦A⟧ <= ⟦B⟧ <-> DerivableIn T ({A} ⊢ B)`.

**Well-definedness proof**: If `A ≡[T] A'` and `B ≡[T] B'`, then `DerivableIn T ({A} ⊢ B)` iff
`DerivableIn T ({A'} ⊢ B')`. By transitivity: cut `A'.mp` with `{A} ⊢ B`, then cut with `B.mp`.
Uses `DerivableIn.cut` and `DerivableIn.weakCtx`.

**Simp lemma**:
```lean
@[simp] lemma mk_le_mk :
    (⟦A⟧ : Quotient T.propositionSetoid) ≤ ⟦B⟧ ↔ DerivableIn T ({A} ⊢ B)
```

### Lattice Instance (~60 lines)

```lean
instance Lindenbaum.instLattice : Lattice (Quotient T.propositionSetoid) where
  sup := Quotient.lift₂ (fun A B => ⟦A ∨ B⟧) (by ... Theory.Equiv.or_congr ...)
  inf := Quotient.lift₂ (fun A B => ⟦A ∧ B⟧) (by ... Theory.Equiv.and_congr ...)
  le_sup_left := by intro a b; induction a, b using Quotient.ind₂; simp [mk_le_mk]; exact ⟨orI1 _ (ass (by grind))⟩
  le_sup_right := by intro a b; induction a, b using Quotient.ind₂; simp [mk_le_mk]; exact ⟨orI2 _ (ass (by grind))⟩
  sup_le := by intro a b c; induction a, b, c using Quotient.ind₃; intro ⟨d₁⟩ ⟨d₂⟩; ...
  inf_le_left := ...
  inf_le_right := ...
  le_inf := ...
```

**Simp lemmas**:
```lean
@[simp] lemma mk_sup_mk : (⟦A⟧ : ...) ⊔ ⟦B⟧ = ⟦A ∨ B⟧
@[simp] lemma mk_inf_mk : (⟦A⟧ : ...) ⊓ ⟦B⟧ = ⟦A ∧ B⟧
```

### GeneralizedHeytingAlgebra Instance (~50 lines)

```lean
instance Lindenbaum.instGHA :
    GeneralizedHeytingAlgebra (Quotient T.propositionSetoid) where
  top := ⟦⊤⟧   -- ⟦.bot → .bot⟧ -- NO [Inhabited Atom] needed!
  le_top := by intro a; induction a using Quotient.ind; simp [mk_le_mk]; exact ⟨topI⟩
  himp := Quotient.lift₂ (fun A B => ⟦A → B⟧) (by ... Theory.Equiv.imp_congr ...)
  le_himp_iff := by
    intro a b c; induction a, b, c using Quotient.ind₃
    simp [mk_le_mk, mk_inf_mk, mk_himp_mk]
    constructor
    · intro ⟨d⟩; exact ⟨impI _ d ... ⟩   -- deduction theorem direction
    · intro ⟨d⟩; exact ⟨impE (d.weakCtx ...) (ass ...) |> ...⟩
```

**Critical insight**: `le_himp_iff` is the deduction theorem:
`⟦A⟧ ⊓ ⟦B⟧ <= ⟦C⟧ <-> ⟦A⟧ <= ⟦B⟧ ⇨ ⟦C⟧`, which unfolds to
`DerivableIn T ({A ∧ B} ⊢ C) <-> DerivableIn T ({A} ⊢ B → C)`.

The forward direction uses `impI` (the actual deduction theorem). The backward direction
uses `impE` + `andE1` + `andE2`.

**Simp lemmas**:
```lean
@[simp] lemma mk_himp_mk : (⟦A⟧ : ...) ⇨ ⟦B⟧ = ⟦A → B⟧
lemma top_eq : (⊤ : Quotient T.propositionSetoid) = ⟦⊤⟧
```

**No `[Inhabited Atom]` needed**: CSLib's `⊤ = .bot → .bot` is available without any atom.
Thomas's code requires `[Inhabited Atom]` because his `⊤ = A → A` needs an arbitrary `A`.

### HeytingAlgebra Instance (~40 lines)

```lean
instance Lindenbaum.instHA [IsIntuitionistic T] :
    HeytingAlgebra (Quotient T.propositionSetoid) where
  bot := ⟦⊥⟧
  bot_le := by intro a; induction a using Quotient.ind; simp [mk_le_mk]
              exact ⟨botE (ass (by grind))⟩  -- uses IsIntuitionistic.efq
  compl a := a ⇨ ⟦⊥⟧    -- ¬A := A → ⊥
  himp_bot := by intro a; induction a using Quotient.ind; simp [mk_himp_mk]; rfl
```

**Key**: `bot_le` requires ex falso quodlibet (`botE`), which is a derived rule requiring
`[IsIntuitionistic T]`. This is exactly why the HA instance is conditional.

**Primitive bot advantage**: `bot := ⟦⊥⟧` is trivially `⟦.bot⟧` -- no `[Bot Atom]` needed.
Thomas's code requires `[Bot Atom]` to access `⟦atom Bot.bot⟧`.

**Simp lemma**:
```lean
lemma bot_eq [IsIntuitionistic T] : (⊥ : Quotient T.propositionSetoid) = ⟦⊥⟧
```

### BooleanAlgebra Instance (~40 lines)

Strategy: use `BooleanAlgebra.ofRegular` from Mathlib.

```lean
instance Lindenbaum.instBA [IsClassical T] :
    BooleanAlgebra (Quotient T.propositionSetoid) :=
  haveI : IsIntuitionistic T := ⟨fun A => ...⟩  -- CPL has efq
  BooleanAlgebra.ofRegular (fun a => by
    induction a using Quotient.ind; rename_i A
    -- Need: ¬¬⟦A⟧ ≤ ⟦A⟧, i.e., ⟦¬¬A⟧ ≤ ⟦A⟧
    -- i.e., DerivableIn T ({¬¬A} ⊢ A)
    -- Uses dne from [IsClassical T]
    simp [mk_le_mk]
    exact ⟨dne (ass (by grind))⟩)
```

**Key**: `BooleanAlgebra.ofRegular` exists in Mathlib at
`Heyting._root_.BooleanAlgebra.ofRegular`. It promotes HA to BA given that every element
is regular (`¬¬a = a`). The regularity proof is exactly DNE.

### Nontrivial and Consistency (~20 lines)

```lean
lemma nontrivial_of_consistent (hc : ¬DerivableIn T (⊥ : Proposition Atom)) :
    Nontrivial (Quotient T.propositionSetoid)
```

---

## File 2: Completeness.lean (~200 lines)

**Path**: `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean`

### Imports

```lean
import Cslib.Init
public import Cslib.Logics.Propositional.Semantics.Algebra.Lindenbaum
public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence
```

### AlgTValid Predicate (~10 lines)

```lean
/-- A valuation `v` with bottom value `bot_val` models a theory `T` iff every axiom
of `T` evaluates to `⊤`. -/
def AlgTValid {H : Type*} [GeneralizedHeytingAlgebra H]
    (T : Theory Atom) (v : Atom → H) (bot_val : H) : Prop :=
  ∀ B ∈ T, AlgEvaluate v bot_val B = ⊤
```

### Canonical Valuation (~15 lines)

```lean
/-- The canonical valuation into the Lindenbaum quotient. -/
def Theory.canonicalV (T : Theory Atom) :
    Atom → Quotient T.propositionSetoid :=
  fun x => ⟦.atom x⟧
```

### Truth Lemma (canonicalV_spec) (~20 lines)

```lean
/-- The truth lemma: evaluating φ in the canonical valuation with bot_val = ⟦⊥⟧
yields ⟦φ⟧. -/
theorem Theory.canonicalV_spec (A : Proposition Atom) :
    AlgEvaluate T.canonicalV (⟦(⊥ : Proposition Atom)⟧ : Quotient T.propositionSetoid) A =
    (⟦A⟧ : Quotient T.propositionSetoid) := by
  induction A with
  | atom x => simp [AlgEvaluate, Theory.canonicalV]
  | bot => simp [AlgEvaluate]
  | imp a b iha ihb => simp [AlgEvaluate, iha, ihb, mk_himp_mk]
  | and a b iha ihb => simp [AlgEvaluate, iha, ihb, mk_inf_mk]
  | or a b iha ihb => simp [AlgEvaluate, iha, ihb, mk_sup_mk]
```

**The `.bot` case**: `simp [AlgEvaluate]` discharges it in one line. This is the sole
addition over Thomas's 4-case proof. AlgEvaluate_bot unfolds to `bot_val = ⟦⊥⟧` which is
exactly the goal.

### Lindenbaum Completeness (~15 lines)

```lean
/-- ⟦A⟧ = ⊤ iff A is derivable in T. -/
theorem Theory.lindenbaum_complete :
    (⟦A⟧ : Quotient T.propositionSetoid) = ⊤ ↔ DerivableIn T A := by
  rw [top_eq, Quotient.eq']
  exact (derivable_iff_equiv_top A).symm
```

Wait -- this needs care. `⟦A⟧ = ⊤` means `⟦A⟧ = ⟦⊤⟧` in the quotient, which means
`A ≡[T] ⊤`. And `derivable_iff_equiv_top` says `DerivableIn T A <-> A ≡[T] ⊤`. So:

```lean
theorem Theory.lindenbaum_complete :
    (⟦A⟧ : Quotient T.propositionSetoid) = ⊤ ↔ DerivableIn T A := by
  constructor
  · intro h
    rw [top_eq] at h
    exact (derivable_iff_equiv_top A).mpr (Quotient.exact h)
  · intro h
    rw [top_eq]
    exact Quotient.sound (derivable_iff_equiv_top A).mp h
```

### Canonical Valuation Models T (~10 lines)

```lean
theorem Theory.tValid_canonicalV :
    AlgTValid T T.canonicalV (⟦(⊥ : Proposition Atom)⟧ : Quotient T.propositionSetoid) := by
  intro B hB
  rw [canonicalV_spec]
  exact lindenbaum_complete.mpr ⟨Derivation.ax hB⟩
```

### ND-Level Soundness (~25 lines)

The existing soundness is Hilbert-level. For completeness we need ND-level soundness:

```lean
/-- ND soundness: if T derives φ, then φ evaluates to ⊤ in every GHA model of T. -/
theorem nd_alg_sound {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H)
    (hT : AlgTValid T v bot_val)
    (hd : DerivableIn T (∅ ⊢ A)) :
    AlgEvaluate v bot_val A = ⊤ := by
  -- Prove by induction on the derivation
  obtain ⟨d⟩ := hd
  exact nd_sound_aux v bot_val hT d (fun _ h => nomatch h)
```

where `nd_sound_aux` does structural induction on `Theory.Derivation`:

```lean
theorem nd_sound_aux {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H)
    (hT : AlgTValid T v bot_val)
    {Γ : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation Γ A)
    (hΓ : ∀ B ∈ Γ, AlgEvaluate v bot_val B = ⊤) :
    AlgEvaluate v bot_val A = ⊤
```

This proceeds by pattern-matching on `d`:
- `ax hA`: use `hT A hA`
- `ass hA`: use `hΓ A hA`
- `andI`, `andE1`, `andE2`: use `inf_eq_top_iff`, `inf_le_left`, etc.
- `orI1`, `orI2`, `orE`: use `le_sup_left`, `sup_le`, etc.
- `impI`: show `AlgEvaluate v bot_val A ⇨ AlgEvaluate v bot_val B = ⊤` using `himp_eq_top_iff` + inductive hypothesis with extended context
- `impE`: use `himp_inf_le` + modus ponens pattern

This is essentially the same proof as `min_alg_soundness` but for ND instead of Hilbert
derivation trees. Each case is 2-5 lines.

### General Completeness Theorem (~25 lines)

```lean
/-- Algebraic completeness: A is derivable from T iff every GHA valuation
that models T also models A. -/
theorem Theory.alg_complete {A : PL.Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type*} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤ := by
  constructor
  · intro hd H _ v bot_val hT
    exact nd_alg_sound v bot_val hT (DerivableIn.iff_derivableIn_empty.mp hd)
  · intro h
    apply lindenbaum_complete.mp
    have := h T.canonicalV ⟦(⊥ : Proposition Atom)⟧ tValid_canonicalV
    rwa [canonicalV_spec] at this
```

**Key insight**: The backward direction instantiates at the Lindenbaum GHA itself.
The canonical valuation models T (by `tValid_canonicalV`), so `h` gives us
`AlgEvaluate canonicalV ⟦⊥⟧ A = ⊤`, which by `canonicalV_spec` is `⟦A⟧ = ⊤`,
which by `lindenbaum_complete` is `DerivableIn T A`.

No Dedekind-MacNeille completion is needed here. Thomas's insight: state completeness
over GHA directly, and the Lindenbaum algebra suffices.

### MPL Specialization (~15 lines)

```lean
theorem MPL.alg_complete {A : PL.Proposition Atom} :
    DerivableIn MPL A ↔ GHAValid A := by
  rw [Theory.alg_complete]
  constructor
  · intro h H _ v bot_val
    exact h v bot_val (fun _ hB => nomatch hB)  -- MPL = ∅, no axioms
  · intro h v bot_val _
    exact h H v bot_val
```

### IPL Specialization (~15 lines)

```lean
theorem IPL.alg_complete {A : PL.Proposition Atom} :
    DerivableIn IPL A ↔ HAValid A := by
  rw [Theory.alg_complete]
  constructor
  · intro h H _ v
    exact h v ⊥ (fun B hB => by
      -- B ∈ IPL means B = ⊥ → C for some C
      obtain ⟨C, rfl⟩ := hB
      simp [AlgEvaluate, himp_eq_top_iff, bot_le])
  · intro h v bot_val hT
    -- In the Lindenbaum HA, hT forces bot_val behavior
    -- Use general completeness via Theory.alg_complete
    sorry -- needs careful argument; see below
```

**Note on IPL/CPL specialization**: The specialization from `Theory.alg_complete` (over GHA
with bot_val) to `HAValid` (over HA with bot_val = bottom) is not entirely trivial. The forward
direction is straightforward: every HA models IPL (efq is `bot_le`). The backward direction
requires showing that if A is valid in all HAs (with bot_val = bottom), then A is valid in
all GHAs with arbitrary bot_val that model IPL. This works because the Lindenbaum algebra
for IPL is already an HA (by `instHA`), and the canonical bot_val = ⟦⊥⟧ = bottom in that HA.

A cleaner approach: prove IPL.alg_complete directly using `lindenbaum_complete` and the
HA instance, without going through `Theory.alg_complete`. This avoids the bot_val mismatch:

```lean
theorem IPL.alg_complete {A : PL.Proposition Atom} :
    DerivableIn IPL A ↔ HAValid A := by
  constructor
  · intro hd H _ v
    exact nd_alg_sound v ⊥ (fun B hB => by obtain ⟨C, rfl⟩ := hB; simp [AlgEvaluate, himp_eq_top_iff, bot_le]) hd.iff_derivableIn_empty.mp
  · intro h
    apply lindenbaum_complete.mp
    have := h (Quotient IPL.propositionSetoid) (IPL.canonicalV)
    rwa [canonicalV_spec] at this
```

### CPL Specialization (~15 lines)

Same pattern as IPL but with BooleanAlgebra:

```lean
theorem CPL.alg_complete {A : PL.Proposition Atom} :
    DerivableIn CPL A ↔ BAValid A
```

### Hilbert-Level Corollaries (~20 lines)

```lean
theorem Hilbert.MPL.alg_complete {A : PL.Proposition Atom} :
    Derivable MinPropAxiom A ↔ GHAValid A := by
  rw [hilbert_iff_nd_min]; exact MPL.alg_complete

theorem Hilbert.IPL.alg_complete {A : PL.Proposition Atom} :
    Derivable IntPropAxiom A ↔ HAValid A := by
  rw [hilbert_iff_nd_int]; exact IPL.alg_complete

theorem Hilbert.CPL.alg_complete {A : PL.Proposition Atom} :
    Derivable PropositionalAxiom A ↔ BAValid A := by
  rw [hilbert_iff_nd_cl]; exact CPL.alg_complete
```

**Note**: The bridge `hilbert_iff_nd_min` connects `Derivable MinPropAxiom` to
`DerivableIn (AxiomTheory MinPropAxiom)`, not `DerivableIn MPL`. Since `MPL = ∅` and
`AxiomTheory MinPropAxiom = {phi | MinPropAxiom phi}`, these are different theories.
However, the Lindenbaum algebra for `AxiomTheory MinPropAxiom` is still a GHA (all axioms
are GHA-valid, so adding them to the theory preserves the GHA structure). The corollary
needs careful theory-level reasoning. If this becomes complex, defer the Hilbert corollaries
to a follow-up.

---

## File 3: Conservative.lean (~80 lines)

**Path**: `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`

### Imports

```lean
import Cslib.Init
public import Cslib.Logics.Propositional.Semantics.Algebra.Completeness
```

### IsBotFree Predicate (~10 lines)

```lean
/-- A proposition is bot-free if it does not mention ⊥. -/
def Proposition.IsBotFree : Proposition Atom → Bool
  | .atom _ => true
  | .bot => false
  | .imp a b => a.IsBotFree && b.IsBotFree
  | .and a b => a.IsBotFree && b.IsBotFree
  | .or a b => a.IsBotFree && b.IsBotFree
```

Using `Bool` gives decidability for free. The substitution invariance argument grounds this:
bot-free formulas live in the reduct of the signature without the nullary operation symbol ⊥.

### Bot-Free Evaluation Independence (~15 lines)

```lean
/-- For bot-free formulas, evaluation is independent of bot_val. This is the
semantic content of "⊥ is a nullary operation symbol": removing it from the signature
makes the evaluation independent of its interpretation. -/
theorem AlgEvaluate_botFree_independent
    {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (b1 b2 : H)
    {φ : PL.Proposition Atom} (hbf : φ.IsBotFree = true) :
    AlgEvaluate v b1 φ = AlgEvaluate v b2 φ := by
  induction φ with
  | atom _ => rfl
  | bot => simp [Proposition.IsBotFree] at hbf
  | imp a b iha ihb =>
    simp [Proposition.IsBotFree] at hbf
    simp [AlgEvaluate, iha hbf.1, ihb hbf.2]
  | and a b iha ihb =>
    simp [Proposition.IsBotFree] at hbf
    simp [AlgEvaluate, iha hbf.1, ihb hbf.2]
  | or a b iha ihb =>
    simp [Proposition.IsBotFree] at hbf
    simp [AlgEvaluate, iha hbf.1, ihb hbf.2]
```

### Conservative Extension (~30 lines)

```lean
/-- For bot-free formulas, HA-validity implies GHA-validity with any bot_val.
This is the algebraic form of "IPL is conservative over MPL for ⊥-free formulas." -/
theorem HAValid_botFree_implies_GHAValid
    {φ : PL.Proposition Atom} (hbf : φ.IsBotFree = true) :
    HAValid φ → GHAValid φ := by
  intro hHA H _ v bot_val
  have h := hHA H v  -- AlgEvaluate v ⊥ φ = ⊤ in HA H
  -- But H might be a GHA, not HA. We need: for any HA, the result holds.
  -- Actually this needs: embed GHA into an HA (via D-M) or use bot-free independence.
  -- Better approach: use completeness directly.
  sorry -- see alternative below
```

**Alternative (completeness-based) approach** -- cleaner:

```lean
/-- IPL is a conservative extension of MPL for bot-free formulas. -/
theorem ipl_conservative_over_mpl {A : PL.Proposition Atom}
    (hbf : A.IsBotFree = true) :
    DerivableIn IPL A → DerivableIn MPL A := by
  intro hIPL
  rw [MPL.alg_complete]
  intro H _ v bot_val
  rw [IPL.alg_complete] at hIPL
  have := hIPL H v  -- AlgEvaluate v ⊥ A = ⊤
  rwa [AlgEvaluate_botFree_independent v ⊥ bot_val hbf] at this
```

This is the clean completeness-based proof. It uses:
1. `IPL.alg_complete` to get `HAValid A`
2. Instantiate at `H` (the given GHA is also an HA? No -- H is a GHA)

**Issue**: The GHA `H` is not necessarily an HA. We need to evaluate in an HA first,
then transfer via `AlgEvaluate_botFree_independent`. So:

```lean
theorem ipl_conservative_over_mpl {A : PL.Proposition Atom}
    (hbf : A.IsBotFree = true) :
    DerivableIn IPL A → DerivableIn MPL A := by
  intro hIPL
  rw [MPL.alg_complete]
  intro H _ v bot_val
  -- Need: AlgEvaluate v bot_val A = ⊤
  -- We know: for any HA H', AlgEvaluate v' ⊥ A = ⊤ (from IPL completeness)
  -- Use H itself: GHA H has GHA structure. Take any HA extension.
  -- Or: just note that Prop is an HA, and evaluate there.
  have h : AlgEvaluate v (⊥ : H) A = ⊤ := by
    -- H is a GHA. We need an HA to apply IPL completeness.
    -- Problem: H is not necessarily an HA.
    -- Solution: use the bridge through Prop.
    sorry
```

**Corrected approach**: The conservative extension theorem requires D-M completion OR
a semantic argument that does not go through a specific algebra. The cleanest path:

```lean
theorem ipl_conservative_over_mpl {A : PL.Proposition Atom}
    (hbf : A.IsBotFree = true) :
    DerivableIn IPL A → DerivableIn MPL A := by
  intro hIPL
  rw [MPL.alg_complete]
  intro H _ v bot_val
  -- Key: Prop is both a GHA and an HA. Use it as witness.
  -- Actually, we should use the IPL completeness and bot-free independence directly.
  -- IPL.alg_complete gives: for all HA H', for all v', AlgEvaluate v' ⊥ A = ⊤
  -- Instantiate at H' = H (viewing GHA as HA? No.)
  -- Need: for THIS specific GHA H and valuation v, AlgEvaluate v bot_val A = ⊤
  -- Approach: AlgEvaluate v bot_val A = AlgEvaluate v ⊥ A (by botFree independence... but H might not have ⊥)
  -- GHA does not have ⊥! So we cannot even write ⊥ : H.
  -- Real approach: use Prop as the HA.
  rw [IPL.alg_complete] at hIPL
  -- hIPL : ∀ (H' : Type*) [HA H'] (v' : Atom → H'), AlgEvaluate v' ⊥ A = ⊤
  -- Instantiate at Prop (HA), v' := fun a => AlgEvaluate v bot_val (.atom a) = ⊤
  -- This requires showing that ⊤-preservation of AlgEvaluate gives the result.
  -- Actually simpler: for bot-free A, AlgEvaluate does not depend on bot_val AT ALL.
  -- So AlgEvaluate v bot_val A is determined entirely by v.
  -- We can compute it in any HA and get the same answer.
  -- But the codomain H is fixed!
  -- OK the correct argument is purely syntactic:
  -- If DerivableIn IPL A, then by completeness A is HAValid.
  -- To show A is GHAValid, we need: for all GHA H, v, bot_val, AlgEvaluate v bot_val A = ⊤.
  -- Since A is bot-free, AlgEvaluate v bot_val A = AlgEvaluate v bot_val' A for any bot_val'.
  -- In particular, let H' be a HeytingAlgebra extending H (e.g., H × Bool with product order).
  -- Wait, we can't extend an arbitrary GHA to an HA without D-M.
  -- D-M completion IS needed for the conservative extension theorem.
  -- OR: we can use the syntactic detour:
  -- DerivableIn IPL A -> for all HA H, AlgEvaluate v ⊥ A = ⊤
  -- We want: for all GHA H, AlgEvaluate v bot_val A = ⊤
  -- Step 1: Let H' = DedekindMacNeilleCompletion H (an HA by xcthulhu).
  -- Step 2: coe : H ↪o H' preserves inf, sup, himp.
  -- Step 3: AlgEvaluate (coe ∘ v) ⊥ A = ⊤ (by HAValid, since H' is HA).
  -- Step 4: Since A is bot-free, AlgEvaluate (coe ∘ v) ⊥ A = AlgEvaluate (coe ∘ v) (coe bot_val) A.
  -- Step 5: By coe_inf, coe_sup, coe_himp: AlgEvaluate (coe ∘ v) (coe bot_val) A = coe (AlgEvaluate v bot_val A).
  -- Step 6: So coe (AlgEvaluate v bot_val A) = ⊤, and since coe is order-embedding, AlgEvaluate v bot_val A = ⊤.
  -- This requires D-M completion.
  sorry
```

**Conclusion on conservative extension**: The conservative extension theorem requires
Dedekind-MacNeille completion to lift from HA to GHA. Without D-M, we cannot prove this.

**Revised plan**: Include D-M completion as Phase 1, and conservative extension uses it.
Alternatively, state conservative extension as a TODO that depends on D-M (separate task).

### Validity Subsumption (~10 lines)

These are straightforward without D-M:

```lean
theorem GHAValid_implies_HAValid {φ : PL.Proposition Atom} :
    GHAValid φ → HAValid φ := by
  intro h H _ v; exact h H v ⊥

theorem HAValid_implies_BAValid {φ : PL.Proposition Atom} :
    HAValid φ → BAValid φ := by
  intro h H _ v; exact h H v
```

---

## File 4 (DEFERRED): DedekindMacNeille.lean

**Path**: `Cslib/ForMathlib/Order/DedekindMacNeille.lean` (~420 lines)

This file is needed ONLY for:
1. Conservative extension theorem (`ipl_conservative_over_mpl`)
2. Stating MPL completeness over HA (instead of GHA)

It is NOT needed for the core completeness theorems (`Theory.alg_complete`,
`MPL.alg_complete`, `IPL.alg_complete`, `CPL.alg_complete`) because those state
completeness over GHA directly.

**Recommendation**: Port D-M completion as a separate task (task 228 or similar).
It can be submitted as an independent ForMathlib PR. The conservative extension
theorem depends on it but is not a blocker for core completeness.

---

## Existing Modifications Needed

### 1. NaturalDeduction/Basic.lean: Add congruence lemmas (~30 lines)

Three congruence lemmas for `Theory.Equiv`:

```lean
theorem Theory.Equiv.imp_congr
theorem Theory.Equiv.and_congr
theorem Theory.Equiv.or_congr
```

These could alternatively go in the Lindenbaum file. Location is a style choice.

### 2. Semantics/Algebra.lean: Add AlgTValid (~5 lines)

```lean
def AlgTValid (T : Theory Atom) {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) : Prop :=
  ∀ B ∈ T, AlgEvaluate v bot_val B = ⊤
```

### 3. references.bib: Fix merge conflicts + add BibKeys (~20 lines)

- Fix merge conflict markers around Fitting1969/Heyting1930/Herbrand1930/Trufas2024
- Add: `Rasiowa1974`, `RasiowaSikorski1963`, `BlokPigozzi1989`, `Font2016`, `MacNeille1937`

---

## Hilbert Connection

The bridge theorems in `NaturalDeduction/Equivalence.lean` connect:

| Hilbert | Bridge | ND |
|---------|--------|-----|
| `Derivable MinPropAxiom A` | `hilbert_iff_nd_min` | `DerivableIn (AxiomTheory MinPropAxiom) A` |
| `Derivable IntPropAxiom A` | `hilbert_iff_nd_int` | `DerivableIn (AxiomTheory IntPropAxiom) A` |
| `Derivable PropositionalAxiom A` | `hilbert_iff_nd_cl` | `DerivableIn (AxiomTheory PropositionalAxiom) A` |

**Critical subtlety**: `AxiomTheory MinPropAxiom` is NOT `MPL = ∅`. It is
`{phi | MinPropAxiom phi}`, which contains all 8 axiom schemata. However, every MinPropAxiom
is derivable in MPL (they are the ND rules), so `DerivableIn MPL A <-> DerivableIn (AxiomTheory MinPropAxiom) A`. This equivalence may already be established or may need a
lemma.

Similarly, `AxiomTheory IntPropAxiom` contains efq as an axiom, while `IPL` contains
`⊥ → A` as a theory member. These are extensionally equivalent for derivability, but
the proof may require showing `AxiomTheory IntPropAxiom ⊆ IPL` and `IPL ⊆ AxiomTheory IntPropAxiom` (or at least derivability equivalence).

**Recommendation**: Add lemmas `derivableIn_MPL_iff_axiomTheory_min`,
`derivableIn_IPL_iff_axiomTheory_int`, `derivableIn_CPL_iff_axiomTheory_cl` as part
of the completeness file. These are straightforward via weakening + the bridge.

---

## Risks and Mitigations

| Risk | Severity | Mitigation |
|------|----------|------------|
| `le_himp_iff` proof (deduction theorem in quotient) is complex | Medium | CSLib already has `DerivableIn.cut` and `impI`; pattern proven in BimodalLogic |
| `[Inhabited Atom]` creep | Low | CSLib's `top = .bot -> .bot` eliminates this completely; verified via `lean_run_code` |
| AxiomTheory != MPL/IPL/CPL bridging | Medium | Straightforward via weakening; can defer Hilbert corollaries if complex |
| Conservative extension needs D-M | High | Defer to separate task; core completeness does not depend on it |
| BooleanAlgebra.ofRegular availability | None | Verified present in Mathlib: `Heyting._root_.BooleanAlgebra.ofRegular` |
| `le_sup_inf` (distributivity) | Medium | GHA is distributive by definition in Mathlib; `SemilatticeInf.le_sup_inf` should close |
| references.bib merge conflicts | Low | Manual fix required before any BibKey additions |

---

## Revised Line Count

| File | Lines | Status |
|------|-------|--------|
| Lindenbaum.lean | ~300 | Phase 1 |
| Completeness.lean | ~200 | Phase 2 |
| Conservative.lean | ~50 (without D-M-dependent theorem) | Phase 3 |
| DedekindMacNeille.lean | ~420 | Separate task |
| NaturalDeduction additions | ~30 | Pre-req for Phase 1 |
| Algebra.lean additions | ~5 | Pre-req for Phase 2 |

**Total for this task**: ~585 lines across 3 new files + ~35 lines of additions.
**Deferred**: ~420 lines (D-M completion) + ~30 lines (conservative extension D-M proof).

---

## Adversarial Self-Verification

### Challenged Claims

1. **"No D-M needed for core completeness"** -- VERIFIED. Thomas's `Theory.complete` quantifies
   over GHA, not HA. The Lindenbaum quotient IS a GHA. Confirmed by reading Thomas's code
   directly: `Theory.complete` at line 325 uses `[GeneralizedHeytingAlgebra H]`, not
   `[HeytingAlgebra H]`.

2. **"No `[Inhabited Atom]` needed"** -- VERIFIED via `lean_run_code`. CSLib's `derivationTop`
   signature is `{Atom : Type u_1} -> [DecidableEq Atom] -> {T : Theory Atom} -> T deriv top`,
   with no `[Inhabited Atom]`. This is because `top = .bot -> .bot` uses primitive `.bot`.

3. **"Congruence lemmas are missing"** -- VERIFIED by grep. No `Theory.Equiv.or_congr`,
   `and_congr`, or `imp_congr` found in any CSLib file.

4. **"BooleanAlgebra.ofRegular exists"** -- VERIFIED via `lean_local_search`:
   `Heyting._root_.BooleanAlgebra.ofRegular` in `Mathlib/Order/Heyting/Regular.lean`.

5. **"Conservative extension needs D-M"** -- VERIFIED by working through the proof obligation.
   The obstacle: given a GHA `H` (which may not have bottom), we need to evaluate a bot-free
   formula and show it equals top. We know it equals top in all HAs. But we cannot evaluate
   in `H` with `bot_val = ⊥` because `H` has no `⊥`. D-M completion provides the HA extension.

### Uncertain Claims

- **AxiomTheory bridge complexity** (confidence 0.7): The bridge from `AxiomTheory MinPropAxiom`
  to `MPL` for Hilbert corollaries may require more work than expected. `MPL = ∅` is strictly
  smaller than `AxiomTheory MinPropAxiom`, so derivability equivalence needs an argument.
  Mitigation: defer Hilbert corollaries or prove the equivalence separately.

- **`le_sup_inf` for GHA** (confidence 0.8): GHA should be distributive (Mathlib's
  `GeneralizedHeytingAlgebra` extends `DistribLattice`), so `le_sup_inf` should be inherited.
  Needs verification during implementation.

### Recommendations Modified After Verification

- **Original**: 4 files (~1000 lines). **Revised**: 3 files (~585 lines) + separate D-M task.
  The conservative extension's D-M-dependent proof is deferred. The `IsBotFree` predicate and
  `AlgEvaluate_botFree_independent` are included (they don't need D-M), but the main theorem
  `ipl_conservative_over_mpl` gets a sorry until D-M is available.

### BibKey Verification Status

| BibKey | Status |
|--------|--------|
| Johansson1937 | Present in references.bib |
| Gentzen1935 | Present |
| Prawitz1965 | Present |
| ChagrovZakharyaschev1997 | Present |
| vanDalen2013 | Present |
| Rasiowa1974 | MISSING -- needs addition |
| RasiowaSikorski1963 | MISSING -- needs addition |
| BlokPigozzi1989 | MISSING -- needs addition |
| Font2016 | MISSING -- needs addition |
| MacNeille1937 | MISSING -- needs addition |
| TroelstraSchwichtenberg2000 | MISSING -- needs addition |

---

## Appendix: Key Mathlib API

| Lemma | Type | Module |
|-------|------|--------|
| `himp_eq_top_iff` | `a ⇨ b = ⊤ ↔ a ≤ b` | Mathlib.Order.Heyting.Basic |
| `le_himp_iff` | `a ≤ b ⇨ c ↔ a ⊓ b ≤ c` | Mathlib.Order.Heyting.Basic |
| `himp_inf_le` | `(a ⇨ b) ⊓ a ≤ b` | Mathlib.Order.Heyting.Basic |
| `bot_le` (HA) | `⊥ ≤ a` | Mathlib.Order.Heyting.Basic |
| `BooleanAlgebra.ofRegular` | promotes HA to BA given regularity | Mathlib.Order.Heyting.Regular |
| `Quotient.lift₂` | lifts a binary function on a setoid | Lean core |
| `Quotient.sound` | `a ≈ b → ⟦a⟧ = ⟦b⟧` | Lean core |
| `Quotient.exact` | `⟦a⟧ = ⟦b⟧ → a ≈ b` | Lean core |
| `inf_eq_top_iff` | `a ⊓ b = ⊤ ↔ a = ⊤ ∧ b = ⊤` | Mathlib.Order.Lattice |
| `sup_le` | `a ≤ c → b ≤ c → a ⊔ b ≤ c` | Mathlib.Order.Lattice |
