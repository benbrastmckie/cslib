/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Deduction

/-! # Contexts and 𝒯-primeness (Task 517 Phase 4)

This module lands A. K. Simpson's notion of a **context** `(G, Γ)` and of a **𝒯-prime**
context [Simpson1994], `:5941-5960`, together with the order `(G,Γ) ⊆ (H,Δ)` on contexts and the
fixed target frame theory `𝒯_S5 := {χ_T, χ_5}` (`IS5 = IKT5`, `:3827`). This is the substrate
that Phase 5's Prime Lemma 5.3.1 maximalises (Zorn over *whole* contexts) and that Phase 6's
Canonical Model Lemma 5.3.2 reads off truth from.

**Task 517 scope note**: this file covers Phase 4 only. Phase 3 (`Adequacy.lean`, the gated
adequacy bridge) is dispatched separately, in parallel, with disjoint file ownership -- this
file does not depend on it and does not touch it. Phases 5-9 (the Prime Lemma, the canonical
model, the birelation construction, the frame-class match, and final assembly) are **not**
attempted here.

## The key structural insight, preserved here

Simpson's Zorn (Phase 5) is over **whole contexts**, so a context is **one object** carrying
**all labels at once**: a single Lindenbaum-style maximalisation extends `Γ` (and, where needed,
`G`) against **one global constraint** simultaneously for every label, rather than threading a
separate maximalisation per label with the other components held fixed. This is exactly the
"simultaneous maximal pair" that CSLib's own `CS5.lean:700-710` named as the missing object, and
is why Route B escapes task 512's wall (whose prior Lindenbaum engine fixed one component while
extending the other -- that engine is explicitly **not** reused here; grep confirms this module
references neither it nor its supporting theory type). Concretely, this module's `Context` and
`TPrime` place **no bound** on `Γ` (typed as a `Set`, not a `List`,
precisely so Phase 5's Zorn chains can take arbitrary -- including infinite -- unions) and place
**no bound** on `G`; the order `Context.le` below is a plain, unbounded inclusion order. Any
future phase that fixes a head or bounds a context in the box-backward direction re-enters
task 512's wall (`cs5_symmetric_tail_box_gap`, see the plan's standing constraint) -- nothing in
this file does so.

## Design decision: `Context.Γ : Set (LabelledFormula Atom)`, not `List`

`Deduction.lean`'s `NIK` relation (`Γ ⊢_G x:A`) necessarily uses `List (LabelledFormula Atom)`
for its assumption context: derivations are finite objects, and every application of a rule uses
only finitely many open assumptions (Simpson `:5090`, verbatim: "a derivation ... from open
assumptions `y₁Rz₁,…,yₘRzₘ, x₁:A₁,…,xₙ:Aₙ`" -- always a finite list). A **context** `(G,Γ)`
(Chapter 5's Henkin-style construction), by contrast, is a member of a Zorn poset whose chains
must close under union (Phase 5): the maximal element obtained from Zorn's lemma is, in general,
an infinite union of finite extensions, and so **cannot** be represented by a `List`. Simpson
himself treats `Γ` as a set throughout Chapter 5 (e.g. "Consider the set `C` of all contexts
`(G',Γ') ⊇ (G,Γ)`", `:5990`). This module therefore types `Context.Γ : Set (LabelledFormula
Atom)` and bridges the two notions with `Deriv` (below): `Deriv 𝒯 G Γ φ` holds iff `φ` is
derivable, via the finitary `NIK`, from *some* finite sublist drawn from the (possibly infinite)
set `Γ`. All of `TPrime`'s clauses that mention `⊢_G` (deductive closure, consistency) are
stated using `Deriv`, not `NIK` directly. This is the one definitional choice in this phase not
dictated verbatim by the plan's task list, flagged per the escalation protocol; it is the choice
that keeps Phase 5's Zorn-over-contexts expressible at all.

## Contents

- `Label.InW`: the free-algebra membership predicate `x ∈ W(V')` (label built from prefix
  variables in `V'` via zero or more `dwitness` applications).
- `GeomWitnessClosure`: Context clause 3, the geometric-witness closure condition for the
  (elided, per Phase 1) k-ary geometric-sequent witness operators -- vacuously `True` under the
  present `Label` type, documented rather than silently omitted.
- `Context`: Simpson's context `(G,Γ)` (`:5941`), with all three numbered clauses plus the
  "`G` contains every prefix in `Γ`" side condition.
- `Context.le` / the `(G,Γ) ⊆ (H,Δ)` order (`:5941`, immediately after the definition), together
  with a `Preorder` instance.
- `Deriv`: the set-lifted consequence relation bridging `Context.Γ : Set` and `NIK`'s finitary
  `List`, plus `Deriv.mono` (monotonicity under `Context.le`) and `Deriv.ofNIK`.
- `TPrime`: Simpson's 𝒯-prime context (`:5953`) -- clause 0 (classical model of `𝒯`) plus the
  four numbered clauses (deductive closure, consistency, disjunction property, diamond
  property). **The Consistency clause is what banishes `Ω`** (the exploding, everywhere-true
  world) -- see the module-level note below.
- `TS5`: the fixed target frame theory `𝒯_S5 := {χ_T, χ_5}` (`IS5 = IKT5`, `:3827`).
- `equivalence_of_refl_eucl` / `equivalence_of_classicalModel_TS5`: reflexive + Euclidean ⟹
  equivalence relation, consumed by Phase 8's frame-class match.

## Why the Consistency clause matters (guardrail analysis, `cs5Incest_forces_symm`)

`cs5Incest_forces_symm` (`CS5Canonical.lean:643`) is a guardrail theorem that, in CSLib's
*canonical*-model construction, is fatal in composition with `Ω = Set.univ` being universally
reachable (`Ω`'s underlying theory is `⊤`, hence consistent with everything, hence reachable from
every world). Here, **`TPrime`'s Consistency clause (`∀ x ∈ G.X, ¬ Deriv 𝒯 G Γ (x ∶ ⊥)`) rules
out any such exploding node by construction**: no label in a 𝒯-prime context's graph can derive
`⊥`, so there is no `Ω`-like node for the guardrail to become fatal against. The guardrail
theorem *itself* still applies to the birelation model `B_K` built downstream (Phase 7) and
yields plain box-symmetry there -- a true, harmless theorem, not a contradiction -- precisely
*because* `B_K` has no `Ω` (Phase 7's concern; not re-derived here, but the load-bearing
Consistency clause it depends on is landed in this file as a **defining clause of `TPrime`**, not
something derived from the other clauses).

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 5, §5.3 ("Completeness"): `Context` and `TPrime` at `:5941-5960`; the context order
  immediately following; `𝒯_S5 = {χ_T, χ_5}` at `:3827`.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Labelled

universe u

variable {Atom : Type u}

/-! ## The free algebra `W(V')` -/

/-- `x ∈ W(V')`: `x` is built from prefix variables in `V'` via zero or more `dwitness`
applications (Simpson's free algebra `W(V')`, `:5883-5905`). Structural recursion on `x`. -/
def Label.InW (V' : Set PrefixVar) : Label Atom → Prop
  | .var n => n ∈ V'
  | .dwitness x _ => Label.InW V' x

/-! ## Context clause 3: the geometric-witness closure condition -/

set_option linter.unusedVariables false in
/-- Context clause 3 (Simpson `:5941`, item 3): the geometric-witness closure condition for the
`k`-ary Skolem witnesses of existential geometric sequents (i.e. `χ_D`, seriality: "each of the
witness variables ... is in `G` only if the others are and ... the relations ... all hold in
`G`"). Phase 1 (`Syntax.lean`, "Definitional choice") elided the `k`-ary witness operators from
`Label` -- only the unary diamond-witness `dwitness` is implemented -- because `TS5 := {χ_T,
χ_5}` (fixed below) are both **universal Horn** axioms with no existential conclusion, hence need
no Skolem witness at all. Consequently, under the present `Label` type (which has no `k`-ary
witness constructor), this clause is **vacuously satisfied** by every graph: there is no witness
variable of that shape for the condition to constrain on. Documented explicitly (as a separate
`def`, per the plan) rather than silently omitted, so that a future extension adding `k`-ary
witness constructors (e.g. for `χ_D`) has an exact, isolated place to strengthen this definition
without touching any other clause of `Context`. Both `𝒯` and `G` are kept as explicit
parameters even though the body does not mention them, so the definition reads, at every call
site, as "the closure condition for graph `G` relative to theory `𝒯`"; both the core
`unusedVariables` linter and Mathlib's `unusedArguments` environment linter are disabled locally
for exactly this reason (`@[nolint unusedArguments]`). -/
@[nolint unusedArguments]
def GeomWitnessClosure (𝒯 : Set GeomAxiom) (G : Graph Atom) : Prop := True

set_option linter.unusedVariables false in
/-- `GeomWitnessClosure` holds for every graph (see its docstring: vacuous under the present
`Label` type). In particular it is trivially preserved under graph union, which is exactly what
Phase 5's Zorn chain-closure argument needs from this clause. -/
@[simp] theorem geomWitnessClosure_holds (𝒯 : Set GeomAxiom) (G : Graph Atom) :
    GeomWitnessClosure 𝒯 G := trivial

/-! ## Contexts -/

/-- A **context** `(G,Γ)` (Simpson `:5941`): `G` contains every prefix occurring in `Γ`, and the
three numbered clauses hold. **`Γ` is a `Set`, not a `List`** -- see the module docstring,
"Design decision" -- because Phase 5's Zorn poset must be able to take unions of chains, which
may be infinite. -/
structure Context (𝒯 : Set GeomAxiom) (Atom : Type u) : Type u where
  /-- The underlying graph. -/
  G : Graph Atom
  /-- The (possibly infinite) set of prefixed formulae. -/
  Γ : Set (LabelledFormula Atom)
  /-- `G` contains every prefix occurring in `Γ`. -/
  ctxSubset : ∀ φ ∈ Γ, φ.lbl ∈ G.X
  /-- Clause 1: the underlying set of `G` lies in `W(V')` for some coinfinite `V'`. -/
  coinfinite : ∃ V' : Set PrefixVar, Coinfinite V' ∧ ∀ x ∈ G.X, Label.InW V' x
  /-- Clause 2: the diamond-witness label `v_{x:◇A}` is in `G` only if the distinguished edge
  `xRv_{x:◇A}` is in `G` and `v_{x:◇A}:A ∈ Γ`. -/
  dwitnessMem : ∀ (x : Label Atom) (A : Proposition Atom), Label.dwitness x A ∈ G.X →
    G.R x (Label.dwitness x A) ∧ (Label.dwitness x A ∶ A) ∈ Γ
  /-- Clause 3: the geometric-witness closure condition. -/
  geomWitnessClosure : GeomWitnessClosure 𝒯 G

/-- The context order: `(G,Γ) ⊆ (H,Δ)` iff `G ≤ H` (the sub-graph order, `Syntax.lean`) and
`Γ ⊆ Δ` (Simpson, immediately after the definition of `Context`, `:5941`). This is the order
underlying both Phase 5's Zorn poset and Phase 6's canonical model `≤`. **It is deliberately a
plain, unbounded inclusion order** -- no fixed head, no bound on `G` or `Γ` -- per the plan's
standing constraint that the box clause's `≤`-quantification (Phase 6) must range over
arbitrarily larger contexts; bounding this order here would re-impose exactly the hypothesis
that makes `cs5_symmetric_tail_box_gap` fatal and re-enter task 512's wall. -/
def Context.le {𝒯 : Set GeomAxiom} (C D : Context 𝒯 Atom) : Prop := C.G ≤ D.G ∧ C.Γ ⊆ D.Γ

instance {𝒯 : Set GeomAxiom} : LE (Context 𝒯 Atom) := ⟨Context.le⟩

@[refl] theorem Context.le_refl {𝒯 : Set GeomAxiom} (C : Context 𝒯 Atom) : C ≤ C :=
  ⟨Graph.le_refl C.G, Set.Subset.refl _⟩

theorem Context.le_trans {𝒯 : Set GeomAxiom} {C D E : Context 𝒯 Atom} (h1 : C ≤ D) (h2 : D ≤ E) :
    C ≤ E :=
  ⟨Graph.le_trans h1.1 h2.1, h1.2.trans h2.2⟩

instance {𝒯 : Set GeomAxiom} : Preorder (Context 𝒯 Atom) where
  le := Context.le
  le_refl := Context.le_refl
  le_trans := fun _ _ _ => Context.le_trans

/-! ## The set-lifted consequence relation -/

/-- `Deriv 𝒯 G Γ φ`: `φ` is derivable, via the finitary `NIK`, from some finite sublist drawn
from the (possibly infinite) set `Γ`. Bridges `Context.Γ : Set` with `NIK`'s `List`-typed
assumption context (see the module docstring, "Design decision"). This is the relation used by
`TPrime`'s clauses wherever Simpson writes `⊢_G` or `⊬_G` against a context's `Γ`. -/
def Deriv (𝒯 : Set GeomAxiom) (G : Graph Atom) (Γ : Set (LabelledFormula Atom))
    (φ : LabelledFormula Atom) : Prop :=
  ∃ Γ₀ : List (LabelledFormula Atom), (∀ ψ ∈ Γ₀, ψ ∈ Γ) ∧ NIK 𝒯 G Γ₀ φ

/-- Any `NIK`-derivation from a finite list `Γ₀` contained in `Γ` witnesses `Deriv 𝒯 G Γ`. -/
theorem Deriv.ofNIK {𝒯 : Set GeomAxiom} {G : Graph Atom} {Γ₀ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (h : NIK 𝒯 G Γ₀ φ) (Γ : Set (LabelledFormula Atom))
    (hΓ₀ : ∀ ψ ∈ Γ₀, ψ ∈ Γ) : Deriv 𝒯 G Γ φ := ⟨Γ₀, hΓ₀, h⟩

/-- **Monotonicity of `Deriv`** under the context order: derivability from a smaller context
transfers to any larger one. This is exactly the fact Phase 5's Zorn chain-closure argument and
Phase 6's `□`-backward case (both applying the Prime Lemma to a strictly larger context) will
consume. Proved directly from `NIK.weaken` -- the witnessing finite sublist `Γ₀` is reused
unchanged; only the ambient graph is weakened. -/
theorem Deriv.mono {𝒯 : Set GeomAxiom} {G G' : Graph Atom} {Γ Δ : Set (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (h : Deriv 𝒯 G Γ φ) (hG : G ≤ G') (hΓΔ : Γ ⊆ Δ) :
    Deriv 𝒯 G' Δ φ := by
  obtain ⟨Γ₀, hΓ₀, hNIK⟩ := h
  exact ⟨Γ₀, fun ψ hψ => hΓΔ (hΓ₀ ψ hψ), hNIK.weaken hG (fun ψ hψ => hψ)⟩

/-! ## 𝒯-prime contexts -/

/-- A **𝒯-prime context** (Simpson `:5953`): a context `(G,Γ)` such that `G` is a classical model
of `𝒯` (clause 0) and the four numbered clauses hold. **The Consistency clause banishes `Ω`**
(the exploding, everywhere-inconsistent world) -- see the module docstring, "Why the Consistency
clause matters". -/
structure TPrime (𝒯 : Set GeomAxiom) (Atom : Type u) : Type u extends Context 𝒯 Atom where
  /-- Clause 0: `G` is a classical model of `𝒯`. -/
  clModel : ClassicalModel 𝒯 G.R
  /-- Clause 1: deductive closure -- `Γ ⊢_G x:A ⟹ x:A ∈ Γ`. -/
  deductiveClosure : ∀ (x : Label Atom) (A : Proposition Atom), Deriv 𝒯 G Γ (x ∶ A) → (x ∶ A) ∈ Γ
  /-- Clause 2: consistency -- `∀ x` in `G`, `Γ ⊬_G x:⊥`. **This is what banishes `Ω`**; it is a
  *defining* clause of `TPrime`, not something derived from the other clauses. -/
  consistency : ∀ x ∈ G.X, ¬ Deriv 𝒯 G Γ (x ∶ Proposition.bot)
  /-- Clause 3: the disjunction property -- `x:A∨B ∈ Γ ⟹ x:A ∈ Γ ∨ x:B ∈ Γ`. -/
  disjunction : ∀ (x : Label Atom) (A B : Proposition Atom),
      (x ∶ Proposition.or A B) ∈ Γ → (x ∶ A) ∈ Γ ∨ (x ∶ B) ∈ Γ
  /-- Clause 4: the diamond property -- `x:◇A ∈ Γ ⟹ ∃y. xRy in G ∧ y:A ∈ Γ`. -/
  diamond : ∀ (x : Label Atom) (A : Proposition Atom),
      (x ∶ Proposition.diamond A) ∈ Γ → ∃ y, G.R x y ∧ (y ∶ A) ∈ Γ

/-! ## The target frame theory `𝒯_S5` -/

/-- **`𝒯_S5 := {χ_T, χ_5}`**: Simpson's presentation of `IS5 = IKT5` (`:3827`, verbatim: "we
write `IT`, `IS4` and `IS5` for `IKT`, `IKT4` and `IKT5` respectively") as a basic geometric
theory over `R`: reflexivity plus Euclideanness. This is the frame theory fixed for the entire
Route B construction (Phases 5-9); per the plan's Non-Goals, **Simpson's geometric-theory
presentation is used throughout, not Marin's `klmn` condition** -- `cs5FCIncest` is only
*derived* from `𝒯_S5`-classical-modelhood at the very end (Phase 8). -/
def TS5 : Set GeomAxiom := {GeomAxiom.T, GeomAxiom.Five}

theorem GeomAxiom.T_mem_TS5 : GeomAxiom.T ∈ TS5 := Or.inl rfl

theorem GeomAxiom.Five_mem_TS5 : GeomAxiom.Five ∈ TS5 := Or.inr rfl

/-- **Reflexive + Euclidean ⟹ equivalence relation.** A relation satisfying `χ_T` and `χ_5` is
automatically symmetric (via reflexivity, instantiating Euclideanness at the reflexive point)
and transitive (via that derived symmetry, instantiating Euclideanness again); together with
reflexivity this gives a full equivalence relation. **Symmetry is free and structural here** --
exactly as `cs5Tail_symm` is free on the CSLib canonical-model side (report 01, Deliverable 5):
it was never the gap in either framework. Consumed by Phase 8's frame-class match (`cs5FCIncest`
conjuncts 1, 2, 5) via `equivalence_of_classicalModel_TS5` below. -/
theorem equivalence_of_refl_eucl {R : Label Atom → Label Atom → Prop}
    (hrefl : GeomAxiom.T.Holds R) (heucl : GeomAxiom.Five.Holds R) : Equivalence R where
  refl := hrefl
  symm := fun {x y} hxy => heucl x y x hxy (hrefl x)
  trans := fun {x y z} hxy hyz => heucl y x z (heucl x y x hxy (hrefl x)) hyz

/-- Specialization of `equivalence_of_refl_eucl` to a relation classically modelling the whole
of `TS5`: `H ⊨_cl 𝒯_S5 ⟹ H` is an equivalence relation. This is exactly `TPrime`'s clause 0
instantiated at `𝒯_S5`, the fact Phase 8 needs to discharge `cs5FCIncest`'s reflexivity,
transitivity, and (via `Equivalence.symm`) `cs5Incest` conjuncts. -/
theorem equivalence_of_classicalModel_TS5 {R : Label Atom → Label Atom → Prop}
    (h : ClassicalModel TS5 R) : Equivalence R :=
  equivalence_of_refl_eucl (h GeomAxiom.T GeomAxiom.T_mem_TS5)
    (h GeomAxiom.Five GeomAxiom.Five_mem_TS5)

end Cslib.Logic.Modal.Labelled
