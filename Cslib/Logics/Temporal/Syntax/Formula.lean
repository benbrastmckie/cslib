/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic

/-! # Temporal Logic Formula

This module defines the formula type for temporal logic with primitives
`{atom, bot, imp, untl, snce, allFuture, allPast}`. The `untl` (until) and `snce` (since)
operators are the basic existential temporal modalities; `allFuture` (G) and `allPast` (H)
are primitive universal temporal modalities, promoted from derived abbreviations to
constructors.

## Main definitions

- `Formula` : Inductive type for temporal logic formulas with constructors
  `atom`, `bot`, `imp`, `untl`, `snce`, `allFuture`, `allPast`
- `Formula.someFuture` (𝐅): `⊤ U φ` — φ holds at some future point (derived)
- `Formula.allFuture` (𝐆): primitive constructor — φ holds at all future points
- `Formula.somePast` (𝐏): `⊤ S φ` — φ held at some past point (derived)
- `Formula.allPast` (𝐇): primitive constructor — φ held at all past points

## Notation

Propositional connectives (scoped to `Cslib.Logic.Temporal`):
- `¬` (prefix, 40) : negation (`Formula.neg`)
- `∧` (infix, 36) : conjunction (`Formula.and`)
- `∨` (infix, 35) : disjunction (`Formula.or`)
- `→` (infix, 30) : implication (`Formula.imp`)
- `↔` (infix, 30) : biconditional (`Formula.iff`)

Temporal operators (scoped to `Cslib.Logic.Temporal`):
- `U` (infix, 40) : until (`Formula.untl`)
- `S` (infix, 40) : since (`Formula.snce`)
- `𝐅` (prefix, 40) : some future / eventually (`Formula.someFuture`)
- `𝐆` (prefix, 40) : all future / globally (`Formula.allFuture`)
- `𝐏` (prefix, 40) : some past (`Formula.somePast`)
- `𝐇` (prefix, 40) : all past / historically (`Formula.allPast`)
- `△` (prefix, 80) : always — at all times past, present, and future (`Formula.always`)
- `▽` (prefix, 80) : sometimes — at some time past, present, or future (`Formula.sometimes`)

## Derived Temporal Operators

The derived operators use the Pnueli convention: in `untl guard event` and `snce guard event`,
the first argument is the **guard** (holds at all intermediate points) and the second is the
**event** (holds at the witness point). This matches `Cslib.Logics.LTL` and the axiom
expansion in `Axioms.lean`.

- `someFuture φ` (𝐅 φ): `⊤ U φ` — φ holds at some future point (Pnueli: `untl ⊤ φ`)
- `allFuture φ` (𝐆 φ): primitive constructor — φ holds at all future points
- `somePast φ` (𝐏 φ): `⊤ S φ` — φ held at some past point (Pnueli: `snce ⊤ φ`)
- `allPast φ` (𝐇 φ): primitive constructor — φ held at all past points

The classical equivalences `𝐆φ ↔ ¬𝐅¬φ` and `𝐇φ ↔ ¬𝐏¬φ` hold as *theorems*, not as
definitional equalities. Promoting G/H to constructors enables intuitionistic temporal logics
where `Gφ` is strictly stronger than `¬𝐅¬φ`.

## Convention Note

This module uses the **Pnueli convention** for `untl` and `snce`: `untl guard event`,
where the **guard** (holds at all intermediate points) comes first and the **event**
(holds at the witness point) comes second. This matches [Pnueli1977] and agrees with
`Cslib.Logics.LTL`:

- `someFuture φ = untl ⊤ φ` (⊤ is the trivial guard, φ is the event).
- `somePast φ = snce ⊤ φ` (⊤ is the trivial guard, φ is the event).

Both `Cslib.Logics.Temporal` and `Cslib.Logics.LTL` use the Pnueli convention,
so no argument-order swap is needed in the embedding. The module
`Cslib.Logics.LTL.Embedding` maps LTL `untl` directly to Temporal `reflexiveUntl`
without swapping arguments.

## References

* [H. Kamp, *Tense Logic and the Theory of Linear Order*][Kamp1968]
* [D. Gabbay, A. Pnueli, S. Shelah, J. Stavi, *On the temporal analysis of fairness*][GPSS1980]
-/

@[expose] public section

namespace Cslib.Logic.Temporal

/-- Temporal logic formula type.

Primitives: atoms, falsum, implication, until, since, allFuture (G), allPast (H).

`allFuture` and `allPast` are primitive universal temporal operators.
The derived existential operators `someFuture` (F) and `somePast` (P) remain abbreviations:
`𝐅φ = ⊤ U φ` and `𝐏φ = ⊤ S φ`. The classical equivalences `𝐆φ ↔ ¬𝐅¬φ` and `𝐇φ ↔ ¬𝐏¬φ`
hold as theorems (see `allFutureIffNegSomeFutureNeg`). -/
inductive Formula (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
  /-- Implication. -/
  | imp (φ₁ φ₂ : Formula Atom)
  /-- Until temporal operator: φ₁ U φ₂. -/
  | untl (φ₁ φ₂ : Formula Atom)
  /-- Since temporal operator: φ₁ S φ₂. -/
  | snce (φ₁ φ₂ : Formula Atom)
  /-- All future (globally): G φ — φ holds at all strictly future times. Primitive constructor.
  Classical equivalence `𝐆φ ↔ ¬𝐅¬φ` is a theorem, not a definition. -/
  | allFuture (φ : Formula Atom)
  /-- All past (historically): H φ — φ held at all strictly past times. Primitive constructor.
  Classical equivalence `𝐇φ ↔ ¬𝐏¬φ` is a theorem, not a definition. -/
  | allPast (φ : Formula Atom)
deriving DecidableEq

/-- Register `Temporal.Formula` as an instance of `TemporalConnectives`.

Registered before the derived-connective `abbrev`s so that the
`PropositionalConnectives.neg` / `.top` defaults are in scope
when `Formula.neg` and `Formula.top` are elaborated. -/
instance : TemporalConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  untl := .untl
  snce := .snce

/-- Negation: ¬φ := φ → ⊥.

Delegates to the canonical `PropositionalConnectives.neg` default. -/
abbrev Formula.neg (φ : Formula Atom) : Formula Atom := PropositionalConnectives.neg φ

/-- Verum / top: ⊤ := ⊥ → ⊥.

Delegates to the canonical `PropositionalConnectives.top` default. -/
abbrev Formula.top : Formula Atom := PropositionalConnectives.top

/-- Disjunction: φ₁ ∨ φ₂ := ¬φ₁ → φ₂ -/
abbrev Formula.or (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  .imp (.imp φ₁ .bot) φ₂

/-- Conjunction: φ₁ ∧ φ₂ := ¬(φ₁ → ¬φ₂) -/
abbrev Formula.and (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  .imp (.imp φ₁ (.imp φ₂ .bot)) .bot

/-- Biconditional: φ₁ ↔ φ₂ := (φ₁ → φ₂) ∧ (φ₂ → φ₁) -/
abbrev Formula.iff (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  (φ₁.imp φ₂).and (φ₂.imp φ₁)

/-- Some future (eventually): 𝐅 φ := ⊤ U φ.
    Pnueli convention: `untl guard event` — ⊤ is the trivial guard,
    φ is the event (holds at witness). Agrees with LTL `someFuture φ = ⊤ U φ`. -/
abbrev Formula.someFuture (φ : Formula Atom) : Formula Atom :=
  .untl .top φ

-- Note: `Formula.allFuture` and `Formula.allPast` are inductive constructors.
-- The notation `𝐆`/`𝐇` binds directly to the constructors.

/-- Some past: 𝐏 φ := ⊤ S φ.
    Pnueli convention: `snce guard event` — ⊤ is the trivial guard,
    φ is the event (holds at witness). Agrees with LTL `somePast φ = ⊤ S φ`. -/
abbrev Formula.somePast (φ : Formula Atom) : Formula Atom :=
  .snce .top φ

@[inherit_doc] scoped prefix:40 "¬" => Formula.neg
@[inherit_doc] scoped infix:36 " ∧ " => Formula.and
@[inherit_doc] scoped infix:35 " ∨ " => Formula.or
@[inherit_doc] scoped infixr:25 " → " => Formula.imp
@[inherit_doc] scoped infixr:20 " ↔ " => Formula.iff
@[inherit_doc] scoped infix:40 " U " => Formula.untl
@[inherit_doc] scoped infix:40 " S " => Formula.snce
@[inherit_doc] scoped prefix:40 "𝐅" => Formula.someFuture
@[inherit_doc] scoped prefix:40 "𝐆" => Formula.allFuture
@[inherit_doc] scoped prefix:40 "𝐏" => Formula.somePast
@[inherit_doc] scoped prefix:40 "𝐇" => Formula.allPast

instance : Bot (Formula Atom) := ⟨.bot⟩
instance : Top (Formula Atom) := ⟨.top⟩

end Cslib.Logic.Temporal

@[expose] public section

/-! ## Structural Properties and Derived Operators

Extensions to `Temporal.Formula` providing:
- Complexity measure
- Temporal depth and implication count
- Additional derived temporal operators
- Swap temporal duality transformation
- Atom collection function
- Positive hypothesis predicate
-/

namespace Cslib.Logic.Temporal

/-! ### Complexity Measure -/

namespace Formula

variable {Atom : Type*}

/--
Structural complexity of a formula (number of connectives + 1).

Pattern-aware cases for derived temporal operators (Pnueli convention: `untl guard event`):
- `F(φ) = ⊤ U φ` → treated as overhead 1, not 4
- `P(φ) = ⊤ S φ` → treated as overhead 1, not 4
- `G(φ)` and `H(φ)` are now primitive constructors → overhead 1 directly
- `next(φ) = ⊥ U φ` → treated as overhead 1
- `prev(φ) = ⊥ S φ` → treated as overhead 1
- `R(φ, ψ) = ¬(¬ψ U ¬φ)` → treated as overhead 1
- `T(φ, ψ) = ¬(¬ψ S ¬φ)` → treated as overhead 1
-/
def complexity : Formula Atom → Nat
  | .atom _ => 1
  | .bot => 1
  -- G(φ) and H(φ) are primitive constructors
  | .allFuture φ => 1 + complexity φ
  | .allPast φ => 1 + complexity φ
  -- R(φ, ψ) = release = imp (untl (imp φ bot) (imp ψ bot)) bot  [¬(¬φ_guard U ¬ψ_event) in Pnueli]
  | .imp (.untl (.imp φ .bot) (.imp ψ .bot)) .bot =>
    1 + complexity φ + complexity ψ
  -- T(φ, ψ) = trigger = imp (snce (imp φ bot) (imp ψ bot)) bot  [¬(¬φ_guard S ¬ψ_event) in Pnueli]
  | .imp (.snce (.imp φ .bot) (.imp ψ .bot)) .bot =>
    1 + complexity φ + complexity ψ
  -- generic imp
  | .imp φ ψ => 1 + complexity φ + complexity ψ
  -- F(φ) = untl (imp bot bot) φ  [⊤ U φ in Pnueli: guard=⊤, event=φ]
  | .untl (.imp .bot .bot) φ => 1 + complexity φ
  -- next(φ) = untl bot φ  [⊥ U φ in Pnueli: guard=⊥ impossible, forces immediate step]
  | .untl .bot φ => 1 + complexity φ
  -- generic untl
  | .untl ψ φ => 1 + complexity φ + complexity ψ
  -- P(φ) = snce (imp bot bot) φ  [⊤ S φ in Pnueli: guard=⊤, event=φ]
  | .snce (.imp .bot .bot) φ => 1 + complexity φ
  -- prev(φ) = snce bot φ  [⊥ S φ in Pnueli: guard=⊥ impossible, forces immediate step]
  | .snce .bot φ => 1 + complexity φ
  -- generic snce
  | .snce ψ φ => 1 + complexity φ + complexity ψ

/-! ### Temporal Depth -/

/--
Temporal depth: nesting level of temporal operators.

Computes the maximum nesting depth of temporal operators (U, S, G, H) in a formula.
-/
def temporalDepth : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ => max φ.temporalDepth ψ.temporalDepth
  | .untl ψ φ => 1 + max φ.temporalDepth ψ.temporalDepth
  | .snce ψ φ => 1 + max φ.temporalDepth ψ.temporalDepth
  | .allFuture φ => 1 + φ.temporalDepth
  | .allPast φ => 1 + φ.temporalDepth

/--
Count implication operators in a formula.

Useful for heuristic scoring in proof search.
-/
def countImplications : Formula Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp φ ψ => 1 + φ.countImplications + ψ.countImplications
  | .untl ψ φ => φ.countImplications + ψ.countImplications
  | .snce ψ φ => φ.countImplications + ψ.countImplications
  | .allFuture φ => φ.countImplications
  | .allPast φ => φ.countImplications

/-! ### Additional Derived Temporal Operators -/

/-- Next-step operator: X(φ) = ⊥ U φ.
    X(φ) at t means φ holds at t+1. Pnueli convention: ⊥ is the guard (impossible at any
    intermediate point), φ is the event, forcing the witness to be immediately next. -/
def next (φ : Formula Atom) : Formula Atom := .untl .bot φ

/-- Previous-step operator: Y(φ) = ⊥ S φ.
    Y(φ) at t means φ holds at t-1. Pnueli convention: ⊥ is the guard (impossible at any
    intermediate point), φ is the event, forcing the witness to be immediately previous. -/
def prev (φ : Formula Atom) : Formula Atom := .snce .bot φ

/-- Derived reflexive future operator: G'φ := φ ∧ Gφ. -/
def weakFuture (φ : Formula Atom) : Formula Atom :=
  φ ∧ 𝐆φ

/-- Derived reflexive past operator: H'φ := φ ∧ Hφ. -/
def weakPast (φ : Formula Atom) : Formula Atom :=
  φ ∧ 𝐇φ

/-- Reflexive until: event holds at some point ≥ t with guard at all intermediate points.
    Pnueli convention: first arg is guard (holds at all intermediate points),
    second arg is event (holds at the witness point, which may be t itself).
    `reflexiveUntl φ ψ` at t ↔ ∃ s ≥ t, ψ(s) ∧ ∀ r ∈ [t,s), φ(r). -/
abbrev reflexiveUntl (φ ψ : Formula Atom) : Formula Atom :=
  ψ ∨ (φ ∧ (φ U ψ))

/-- Reflexive since: event held at some point ≤ t with guard at all intermediate points.
    Pnueli convention: first arg is guard (holds at all intermediate points),
    second arg is event (holds at the witness point, which may be t itself).
    `reflexiveSnce φ ψ` at t ↔ ∃ s ≤ t, ψ(s) ∧ ∀ r ∈ (s,t], φ(r). -/
abbrev reflexiveSnce (φ ψ : Formula Atom) : Formula Atom :=
  ψ ∨ (φ ∧ (φ S ψ))

/-- Temporal 'always' operator (△φ): Hφ ∧ φ ∧ Gφ.
    φ holds at all times (past, present, and future). -/
def always (φ : Formula Atom) : Formula Atom :=
  𝐇φ ∧ (φ ∧ 𝐆φ)

/-- Temporal 'sometimes' operator (▽φ): ¬△¬φ.
    φ holds at some time (past, present, or future). -/
def sometimes (φ : Formula Atom) : Formula Atom :=
  ¬(always (¬φ))

/-- Release operator R(φ, ψ) := ¬(¬φ U ¬ψ). Dual of Until.
    Pnueli convention: `untl (neg φ) (neg ψ)` where ¬φ is the guard and ¬ψ is the event,
    i.e., `¬φ U ¬ψ` — guard=¬φ, event=¬ψ. -/
def release (φ ψ : Formula Atom) : Formula Atom :=
  ¬((¬ψ) U (¬φ))

/-- Trigger operator T(φ, ψ) := ¬(¬φ S ¬ψ). Dual of Since (past analog of Release).
    Pnueli convention: `snce (neg φ) (neg ψ)` where ¬φ is the guard and ¬ψ is the event,
    i.e., `¬φ S ¬ψ` — guard=¬φ, event=¬ψ. -/
def trigger (φ ψ : Formula Atom) : Formula Atom :=
  ¬((¬ψ) S (¬φ))

/-- Weak Until operator W(φ, ψ) := (φ U ψ) ∨ G(φ). Until without the liveness requirement. -/
def weakUntil (φ ψ : Formula Atom) : Formula Atom :=
  (φ U ψ) ∨ 𝐆φ

/-- Weak Since operator WS(φ, ψ) := (φ S ψ) ∨ H(φ). Since without the liveness requirement. -/
def weakSince (φ ψ : Formula Atom) : Formula Atom :=
  (φ S ψ) ∨ 𝐇φ

/-- Strong Release operator M(φ, ψ) := ψ U (ψ ∧ φ). Dual of weak until.
    Pnueli convention: `untl ψ (ψ ∧ φ)` where ψ is the guard and ψ∧φ is the event. -/
def strongRelease (φ ψ : Formula Atom) : Formula Atom :=
  (ψ ∧ φ) U ψ

/-- Strong Trigger operator ST(φ, ψ) := ψ S (ψ ∧ φ). Past dual of strong release.
    Pnueli convention: `snce ψ (ψ ∧ φ)` where ψ is the guard and ψ∧φ is the event. -/
def strongTrigger (φ ψ : Formula Atom) : Formula Atom :=
  (ψ ∧ φ) S ψ

/-- Notation for temporal 'always' operator using upward triangle. -/
scoped prefix:80 "△" => Formula.always

/-- Notation for temporal 'sometimes' operator using downward triangle. -/
scoped prefix:80 "▽" => Formula.sometimes

/-! ### Swap Temporal Duality -/

/--
Swap temporal operators (past ↔ future) in a formula.

This transformation is used in the temporal duality inference rule (TD):
if `⊢ φ` then `⊢ swapTemporal φ`.

**Why this definition is not shared with `Bimodal.Formula.swapTemporal`**:
`Temporal.Formula` and `Bimodal.Formula` are distinct inductive types (Lean 4 cannot extend
inductives), so `swapTemporal` must pattern-match on each type's own constructors separately.
`Bimodal.Formula` adds a `box` case (`swap (box φ) = box (swap φ)`) that does not appear here.
The derived-operator exchange theorems below (`swapTemporal_neg`, `swapTemporal_someFuture`, etc.)
are intentionally mirrored in `Bimodal.Syntax.Formula`; this structural duplication is inherent
to the distinct inductive types and is not an abstraction opportunity.
-/
def swapTemporal : Formula Atom → Formula Atom
  | .atom s => .atom s
  | .bot => .bot
  | .imp φ ψ => .imp (swapTemporal φ) (swapTemporal ψ)
  | .untl ψ φ => .snce (swapTemporal ψ) (swapTemporal φ)
  | .snce ψ φ => .untl (swapTemporal ψ) (swapTemporal φ)
  | .allFuture φ => .allPast (swapTemporal φ)
  | .allPast φ => .allFuture (swapTemporal φ)

/-- swapTemporal is an involution (applying it twice gives identity). -/
theorem swapTemporal_involution (φ : Formula Atom) :
    φ.swapTemporal.swapTemporal = φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp _ _ ihp ihq => simp only [swapTemporal, ihp, ihq]
  | untl _ _ ih2 ih1 => simp only [swapTemporal, ih1, ih2]
  | snce _ _ ih2 ih1 => simp only [swapTemporal, ih1, ih2]
  | allFuture _ ih => simp only [swapTemporal, ih]
  | allPast _ ih => simp only [swapTemporal, ih]

/-- swapTemporal distributes over negation: swap(¬φ) = ¬(swap φ). -/
theorem swapTemporal_neg (φ : Formula Atom) :
    (Formula.neg φ).swapTemporal = Formula.neg φ.swapTemporal := by
  simp only [Formula.neg, PropositionalConnectives.neg, swapTemporal]

/-- swapTemporal exchanges someFuture and somePast: swap(Fφ) = P(swap φ). -/
@[simp]
theorem swapTemporal_someFuture (φ : Formula Atom) :
    (Formula.someFuture φ).swapTemporal = Formula.somePast φ.swapTemporal := by
  simp only [Formula.somePast, Formula.top, PropositionalConnectives.top, swapTemporal]

/-- swapTemporal exchanges somePast and someFuture: swap(Pφ) = F(swap φ). -/
@[simp]
theorem swapTemporal_somePast (φ : Formula Atom) :
    (Formula.somePast φ).swapTemporal = Formula.someFuture φ.swapTemporal := by
  simp only [Formula.someFuture, Formula.top, PropositionalConnectives.top, swapTemporal]

/-- swapTemporal exchanges allFuture and allPast: swap(Gφ) = H(swap φ). -/
@[simp]
theorem swapTemporal_allFuture (φ : Formula Atom) :
    (Formula.allFuture φ).swapTemporal = Formula.allPast φ.swapTemporal :=
  rfl

/-- swapTemporal exchanges allPast and allFuture: swap(Hφ) = G(swap φ). -/
@[simp]
theorem swapTemporal_allPast (φ : Formula Atom) :
    (Formula.allPast φ).swapTemporal = Formula.allFuture φ.swapTemporal :=
  rfl

/-- swapTemporal distributes over next/prev: swap(X(φ)) = Y(swap(φ)). -/
theorem swapTemporal_next (φ : Formula Atom) :
    (next φ).swapTemporal = prev φ.swapTemporal := by
  simp [next, prev, swapTemporal]

/-- swapTemporal distributes over prev/next: swap(Y(φ)) = X(swap(φ)). -/
theorem swapTemporal_prev (φ : Formula Atom) :
    (prev φ).swapTemporal = next φ.swapTemporal := by
  simp [prev, next, swapTemporal]

/-- swapTemporal distributes over strongRelease: swap(M(φ,ψ)) = ST(swap φ, swap ψ). -/
theorem swapTemporal_strongRelease (φ ψ : Formula Atom) :
    (strongRelease φ ψ).swapTemporal =
      strongTrigger φ.swapTemporal ψ.swapTemporal := by
  simp [strongRelease, strongTrigger, Formula.and, swapTemporal]

/-- swapTemporal distributes over strongTrigger: swap(ST(φ,ψ)) = M(swap φ, swap ψ). -/
theorem swapTemporal_strongTrigger (φ ψ : Formula Atom) :
    (strongTrigger φ ψ).swapTemporal =
      strongRelease φ.swapTemporal ψ.swapTemporal := by
  simp [strongRelease, strongTrigger, Formula.and, swapTemporal]

/-! ### Positive Hypothesis Predicate -/

/--
Whether a formula requires the single-family/single-time hypotheses.
All non-imp formulas need these for propagation.
-/
def needsPositiveHypotheses : Formula Atom → Bool
  | .imp _ _ => false
  | _ => true

@[simp] lemma needsPositiveHypotheses_atom (s : Atom) :
    (Formula.atom s).needsPositiveHypotheses = true := rfl

@[simp] lemma needsPositiveHypotheses_bot :
    (Formula.bot : Formula Atom).needsPositiveHypotheses = true := rfl

@[simp] lemma needsPositiveHypotheses_untl (p q : Formula Atom) :
    (Formula.untl q p).needsPositiveHypotheses = true := rfl

@[simp] lemma needsPositiveHypotheses_snce (p q : Formula Atom) :
    (Formula.snce q p).needsPositiveHypotheses = true := rfl

@[simp] lemma needsPositiveHypotheses_imp (p q : Formula Atom) :
    (Formula.imp p q).needsPositiveHypotheses = false := rfl

@[simp] lemma needsPositiveHypotheses_allFuture (p : Formula Atom) :
    (Formula.allFuture p).needsPositiveHypotheses = true := rfl

@[simp] lemma needsPositiveHypotheses_allPast (p : Formula Atom) :
    (Formula.allPast p).needsPositiveHypotheses = true := rfl

/-! ### Propositional Atoms -/

section Atoms

variable [DecidableEq Atom]

/-- The set of propositional atoms appearing in a formula. -/
def atoms : Formula Atom → Finset Atom
  | .atom s => {s}
  | .bot => ∅
  | .imp φ ψ => atoms φ ∪ atoms ψ
  | .untl ψ φ => atoms φ ∪ atoms ψ
  | .snce ψ φ => atoms φ ∪ atoms ψ
  | .allFuture φ => atoms φ
  | .allPast φ => atoms φ

/-- swapTemporal preserves atoms: swapping past/future does not change which atoms appear. -/
theorem atoms_swapTemporal (φ : Formula Atom) :
    atoms (swapTemporal φ) = atoms φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | imp _ _ ih1 ih2 => simp only [swapTemporal, atoms]; rw [ih1, ih2]
  | untl _ _ ih2 ih1 => simp only [swapTemporal, atoms]; rw [ih1, ih2]
  | snce _ _ ih2 ih1 => simp only [swapTemporal, atoms]; rw [ih1, ih2]
  | allFuture _ ih => simp only [swapTemporal, atoms]; exact ih
  | allPast _ ih => simp only [swapTemporal, atoms]; exact ih

end Atoms

end Formula

end Cslib.Logic.Temporal

end
