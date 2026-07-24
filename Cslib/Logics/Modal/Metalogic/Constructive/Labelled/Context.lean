/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Deduction

/-! # Contexts and 𝒯-primeness

This module lands A. K. Simpson's notion of a **context** `(G, Γ)` and of a **𝒯-prime**
context [Simpson1994], `:5941-5960`, together with the order `(G,Γ) ⊆ (H,Δ)` on contexts and the
fixed target frame theory `𝒯_S5 := {χ_T, χ_B, χ_4}` (`IKTB4`; see `TS5` for why this
presentation rather than Simpson's `IKT5`). This is the substrate that the Prime Lemma 5.3.1
maximalises (Zorn over *whole* contexts) and that the Canonical Model Lemma 5.3.2 reads truth
off from.

**Scope note**: this file lands the context substrate only. `Adequacy.lean` (the gated adequacy
bridge) is developed separately, with disjoint file ownership -- this file does not depend on it
and does not touch it. The Prime Lemma, the canonical model, the birelation construction, the
frame-class match, and final assembly are **not** attempted here.

## The key structural insight, preserved here

Simpson's Zorn (the Prime Lemma, developed separately) is over **whole contexts**, so a context
is **one object** carrying **all labels at once**: a single Lindenbaum-style maximalisation
extends `Γ` (and, where needed, `G`) against **one global constraint** simultaneously for every
label, rather than threading a separate maximalisation per label with the other components held
fixed. This is exactly the "simultaneous maximal pair" that CSLib's own `CS5.lean:700-710` named
as the missing object, and is why this route escapes the wall recorded by
`cs5_symmetric_tail_box_gap`: the earlier Lindenbaum engine that hit that wall fixed one
component while extending the other, and is explicitly **not** reused here (grep confirms this
module references neither it nor its supporting theory type). Concretely, this module's `Context`
and `TPrime` place **no bound** on `Γ` (typed as a `Set`, not a `List`, precisely so the Zorn
chains can take arbitrary -- including infinite -- unions) and place **no bound** on `G`; the
order `Context.le` below is a plain, unbounded inclusion order. Any future development that fixes
a head or bounds a context in the box-backward direction re-enters that wall
(`cs5_symmetric_tail_box_gap`) -- nothing in this file does so.

## Design decision: `Context.Γ : Set (LabelledFormula Atom)`, not `List`

`Deduction.lean`'s `NIK` relation (`Γ ⊢_G x:A`) necessarily uses `List (LabelledFormula Atom)`
for its assumption context: derivations are finite objects, and every application of a rule uses
only finitely many open assumptions (Simpson `:5090`, verbatim: "a derivation ... from open
assumptions `y₁Rz₁,…,yₘRzₘ, x₁:A₁,…,xₙ:Aₙ`" -- always a finite list). A **context** `(G,Γ)`
(Chapter 5's Henkin-style construction), by contrast, is a member of a Zorn poset whose chains
must close under union: the maximal element obtained from Zorn's lemma is, in general,
an infinite union of finite extensions, and so **cannot** be represented by a `List`. Simpson
himself treats `Γ` as a set throughout Chapter 5 (e.g. "Consider the set `C` of all contexts
`(G',Γ') ⊇ (G,Γ)`", `:5990`). This module therefore types `Context.Γ : Set (LabelledFormula
Atom)` and bridges the two notions with `Deriv` (below): `Deriv 𝒯 G Γ φ` holds iff `φ` is
derivable, via the finitary `NIK`, from *some* finite sublist drawn from the (possibly infinite)
set `Γ`. All of `TPrime`'s clauses that mention `⊢_G` (deductive closure, consistency) are
stated using `Deriv`, not `NIK` directly. This is a definitional choice not dictated verbatim by
Simpson's text, flagged here rather than made silently; it is the choice that keeps
Zorn-over-contexts expressible at all.

## Contents

- `Label.InW`: the free-algebra membership predicate `x ∈ W(V')` (label built from prefix
  variables in `V'` via zero or more `dwitness` applications).
- `Context`: Simpson's context `(G,Γ)` (`:5941`), with the applicable numbered clauses plus the
  "`G` contains every prefix in `Γ`" side condition. Simpson's clause 3 (geometric-witness
  closure) is **absent by construction** -- it constrains the Skolem witnesses of *existential*
  geometric axioms, and `GeomAxiom` (`Deduction.lean`) admits only universal Horn axioms, which
  have none. See the `Context` docstring.
- `Context.le` / the `(G,Γ) ⊆ (H,Δ)` order (`:5941`, immediately after the definition), together
  with a `Preorder` instance.
- `Deriv`: the set-lifted consequence relation bridging `Context.Γ : Set` and `NIK`'s finitary
  `List`, plus `Deriv.mono` (monotonicity under `Context.le`) and `Deriv.ofNIK`.
- `TPrime`: Simpson's 𝒯-prime context (`:5953`) -- clause 0 (**domain-relative** classical model
  of `𝒯`, `ClassicalModelOn`) plus the four numbered clauses (deductive closure -- **relativized
  to `x ∈ G.X`** --, consistency, disjunction property, diamond property). Clauses 0 and 1 are
  repaired from a type-wide transcription defect (see "Why the repaired `TPrime` does not
  re-trip the three prime-theory guardrails" below). **The Consistency clause is what banishes
  `Ω`** (the exploding, everywhere-true world) -- see the module-level note below.
- `TS5`: the fixed target frame theory `𝒯_S5 := {χ_T, χ_B, χ_4}` (`IKTB4`), chosen so that its
  axiom set matches CSLib's `CS5ModalAxiom` schema-for-schema -- see its docstring for why the
  `IKT5` presentation is deliberately not used.
- `classicalModelOn_TS5_iff`: `ClassicalModelOn TS5 D R` unfolds to domain-relative
  reflexivity/symmetry/transitivity on `D`, at no extra cost over the type-wide form.
- `equivalence_of_refl_eucl`: reflexive + Euclidean ⟹ equivalence relation (retained as the
  record that the `IKT5` presentation agrees).
- `equivalence_of_classicalModel_TS5`: `⊨_cl 𝒯_S5 ⟹ Equivalence` (type-wide; retained, not what
  `TPrime.clModel` supplies post-repair).
- `EquivalenceOn` / `equivalence_of_classicalModelOn_TS5`: the **domain-relative** equivalence
  `TPrime.clModel` at `TS5` actually supplies (see "The domain-relative equivalence design
  choice" below) -- consumed by the frame-class match downstream.

## Why the Consistency clause matters (guardrail analysis, `cs5Incest_forces_symm`)

`cs5Incest_forces_symm` (`CS5Canonical.lean:643`) is a guardrail theorem that, in CSLib's
*canonical*-model construction, is fatal in composition with `Ω = Set.univ` being universally
reachable (`Ω`'s underlying theory is `⊤`, hence consistent with everything, hence reachable from
every world). Here, **`TPrime`'s Consistency clause (`∀ x ∈ G.X, ¬ Deriv 𝒯 G Γ (x ∶ ⊥)`) rules
out any such exploding node by construction**: no label in a 𝒯-prime context's graph can derive
`⊥`, so there is no `Ω`-like node for the guardrail to become fatal against. The guardrail
theorem *itself* still applies to the birelation model `B_K` built downstream and
yields plain box-symmetry there -- a true, harmless theorem, not a contradiction -- precisely
*because* `B_K` has no `Ω` (that construction's concern; not re-derived here, but the load-bearing
Consistency clause it depends on is landed in this file as a **defining clause of `TPrime`**, not
something derived from the other clauses).

## Why the repaired `TPrime` does not re-trip the three prime-theory guardrails

This module repairs `TPrime`'s clauses 0-1 (domain-relative `ClassicalModelOn`, relativized
`deductiveClosure`) and `NIK`'s `(⊥E)`/`(∨E)` (`Deduction.lean`, cross-label). None of these
repairs turn a labelled bounded context into a **prime theory** -- the object CSLib's mainline
canonical-model guardrails are about -- so each guardrail is checked explicitly and does not
re-fire:

1. **`cs5_symmetric_tail_box_gap` (`CS5.lean:712` -- THE prime-theory Lindenbaum wall).** That
   wall is a construction that fixes one component (a head theory) while extending the other,
   and cannot satisfy the symmetric back-clause and refute the box subject jointly. `TPrime`
   above is a **single Zorn object**: `Context.Γ : Set (LabelledFormula Atom)` and `Context.G`
   grow *together* under `Context.le`'s plain, unbounded inclusion order (no fixed head, no
   bound -- see "The key structural insight" above). The repair does not introduce a head or a
   bound: `NIK`'s cross-label `efq`/`orE` only widen two elimination rules to an independent
   conclusion label, and the relativized clauses only add a domain hypothesis `x ∈ G.X`. The
   "simultaneous maximal pair" the wall's own docstring names as the missing object is exactly
   what this Zorn poset produces. **Guardrail does not apply.**
2. **`cs5Incest_forces_symm` (`CS5Canonical.lean:643`, axiom-free).** Fatal only in composition
   with an exploding `Ω`-world (theory `⊤`, reachable from everywhere). `TPrime`'s Consistency
   clause (`∀ x ∈ G.X, ¬ Deriv 𝒯 G Γ (x ∶ ⊥)`, unchanged by this repair) banishes `Ω` by
   construction, and the repair *sharpens* this: cross-label `(⊥E)` means a single `z:⊥` would
   collapse every `x:A` at once (`NIKX.consistency_step`), which is precisely why Simpson calls
   consistency "immediate" (p. 93). No `Ω`-node exists for the guardrail to become fatal against;
   it remains
   a true, harmless theorem about the downstream `B_K` model. **Guardrail does not apply.**
3. **`cs5TwoSidedR_iff_cs5Tail` (`CS5Canonical.lean:511`).** Equates Simpson's two-sided `R` with
   the old `cs5Tail` wall **over CS5 quasi-prime theories**. `TPrime` contexts are not quasi-prime
   theories: worlds are graph nodes (`Context.G : Graph Atom`) carrying an explicit relation
   `G.R`, and this repair keeps the canonical relation as the **raw** graph relation (clause 0 is
   about `G.R` itself, domain-relativized -- not a two-sided `R` reconstructed from theory
   membership). The `iff` has no quasi-prime-theory hypothesis to fire on here.
   **Guardrail does not apply.**

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 5, §5.3 ("Completeness"): `Context` and `TPrime` at `:5941-5960`; the context order
  immediately following; Simpson's own `IS5 = IKT5` presentation at `:3827` (this module fixes
  the Hilbert-equivalent `IKTB4` presentation instead -- see `TS5`).
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

/-! ## Contexts -/

/-- A **context** `(G,Γ)` (Simpson `:5941`): `G` contains every prefix occurring in `Γ`, and the
numbered clauses hold. **`Γ` is a `Set`, not a `List`** -- see the module docstring,
"Design decision" -- because the Zorn poset over contexts must be able to take unions of chains,
which may be infinite.

**On Simpson's clause 3 (the geometric-witness closure condition).** Simpson's third numbered
clause constrains the `k`-ary Skolem witness variables of geometric sequents with an
**existential** conclusion ("each of the witness variables ... is in `G` only if the others are
and ... the relations ... all hold in `G`"). It has **no counterpart here, by construction**:
`GeomAxiom` (`Deduction.lean`) represents only universal Horn axioms, which have no witness
variables for such a clause to constrain. The clause is therefore *absent*, rather than stated
and discharged trivially -- there is no proposition here for a reader to mistake for an enforced
constraint. Adding an existential axiom later cannot silently bypass this: `GeomAxiom.Holds`
matches exhaustively on `GeomAxiom`, so a new constructor forces a decision at that match (and at
`TClosure`) in the same change, which is where the witness machinery would have to be designed.

**Why `𝒯` is still an index.** No field above mentions `𝒯`; a context is, with clause 3 absent,
genuinely theory-independent. The parameter is retained because `TPrime` (below) extends
`Context 𝒯 Atom` and *is* 𝒯-relative (clause 0 and every `Deriv 𝒯` clause), and because
`Context.le` and the Zorn poset are threaded at a fixed `𝒯`. It is an index, not a claim of
dependence. -/
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

/-- The context order: `(G,Γ) ⊆ (H,Δ)` iff `G ≤ H` (the sub-graph order, `Syntax.lean`) and
`Γ ⊆ Δ` (Simpson, immediately after the definition of `Context`, `:5941`). This is the order
underlying both the Zorn poset and the canonical model's `≤`. **It is deliberately a
plain, unbounded inclusion order** -- no fixed head, no bound on `G` or `Γ` -- because the box
clause's `≤`-quantification must range over arbitrarily larger contexts; bounding this order
here would re-impose exactly the hypothesis that makes `cs5_symmetric_tail_box_gap` fatal and
re-enter the wall it records. -/
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
transfers to any larger one. This is exactly the fact the Zorn chain-closure argument and the
`□`-backward case (both applying the Prime Lemma to a strictly larger context) will
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
  /-- Clause 0: `G` is a classical model of `𝒯`, **domain-relative** (Simpson's actual
  `H ⊨_CL 𝒯`, `:5953`, quantifiers ranging over `G`'s underlying set `G.X`, not the whole
  `Label Atom` type). **Repair**: a type-wide `ClassicalModel 𝒯 G.R` clause would be a
  transcription defect that provably empties `TPrime` at `𝒯 = TS5` (`clModel .T` chained with
  `Graph.edge_mem` forces `G.X = univ`, contradicting `coinfinite`). `ClassicalModelOn` is the
  fix; it costs nothing at `TS5` (`classicalModelOn_TS5_iff` below) and matches Simpson's
  canonical-model construction, which fixes satisfaction *in the structure `H`* (p. 94) rather
  than type-wide. -/
  clModel : ClassicalModelOn 𝒯 G.X G.R
  /-- Clause 1: deductive closure -- `Γ ⊢_G x:A ⟹ x:A ∈ Γ`, **relativized to `x ∈ G.X`**.
  **Repair**: a type-wide quantifier here would be a `𝒯`-agnostic emptiness driver --
  `NIK.impI` + `NIK.assumption` derive `x:A⊃A` at *every* label with no premises, so a type-wide
  clause would force `(x ∶ A⊃A) ∈ Γ` for every label, hence (via `ctxSubset`) `G.X = univ`,
  contradicting `coinfinite`, for **every** `𝒯` including `𝒯 = ∅`. Simpson's clause 1
  (p. 92, "if `Γ ⊢^𝒯_G x:A` then `x:A ∈ Γ`") is itself a judgement about labels *of `G`*, and
  Lemma 5.3.1's own deductive-closure step needs exactly the relativized form: extending
  `(H, Δ ∪ {y:B})` to a context requires `y ∈ H.X` (`Context.ctxSubset`), which only the
  relativized clause supplies. -/
  deductiveClosure : ∀ x ∈ G.X, ∀ (A : Proposition Atom), Deriv 𝒯 G Γ (x ∶ A) → (x ∶ A) ∈ Γ
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

/-- **`𝒯_S5 := {χ_T, χ_B, χ_4}`**: the target frame theory, presented as reflexivity plus symmetry
plus transitivity, i.e. `IKTB4`. This is the frame theory fixed for the entire labelled
construction; **Simpson's geometric-theory presentation is used throughout, not Marin's `klmn`
condition** -- `cs5FCIncest` is only *derived* from `𝒯_S5`-classical-modelhood at the very end.

**Why `{χ_T, χ_B, χ_4}` and not Simpson's `{χ_T, χ_5}`.** Simpson writes `IS5 = IKT5` (`:3827`,
verbatim: "we write `IT`, `IS4` and `IS5` for `IKT`, `IKT4` and `IKT5` respectively"), so
`Ax({χ_T, χ_5}) = IKT5`. But this development's target is CSLib's `CS5ModalAxiom`, which is
`IKTB4`. Classically the two presentations axiomatise the same logic, and the frame conditions are
interderivable (see `equivalence_of_refl_eucl` below, which is retained precisely to record that
`{χ_T, χ_5}` also yields an equivalence relation). **Constructively, however, `IKT5 ⟺ IKTB4` is
not available off the shelf**, and routing through `{χ_T, χ_5}` would put an *unproved
constructive bridge* on the critical path -- a corner this development does not cut. Fixing
`𝒯_S5 := {χ_T, χ_B, χ_4}` instead lines the axiom set up with `CS5ModalAxiom` **by construction**:
under Simpson's `Ax(-)` (Fig 3-7/6-3), `Ax({χ_T, χ_B, χ_4})` is `IKTB4`, matching `CS5ModalAxiom`
schema-for-schema, where `Ax({χ_T, χ_5})` would be `IKT5` and need the bridge. (`Ax(-)` itself is
not formalised in this file; what *is* landed here is the frame-condition half, below.)
Correspondingly, each of `χ_B`/`χ_4` is *literally* symmetry/transitivity under
`GeomAxiom.Holds`, so the
equivalence-relation fact downstream needs no derivation at all (see
`equivalence_of_classicalModel_TS5`). The one frame condition this drops
(`GeomAxiom.Five`-modelhood) is not consumed anywhere downstream. -/
def TS5 : Set GeomAxiom := {GeomAxiom.T, GeomAxiom.B, GeomAxiom.Four}

theorem GeomAxiom.T_mem_TS5 : GeomAxiom.T ∈ TS5 := Or.inl rfl

theorem GeomAxiom.B_mem_TS5 : GeomAxiom.B ∈ TS5 := Or.inr (Or.inl rfl)

theorem GeomAxiom.Four_mem_TS5 : GeomAxiom.Four ∈ TS5 := Or.inr (Or.inr rfl)

/-- **The domain-relative repair is free at `TS5`**: `ClassicalModelOn TS5 D R` unfolds to
exactly the domain-relative reflexivity/symmetry/transitivity clauses, with no cost beyond
`ClassicalModel`'s type-wide unfolding. Consumed by `equivalence_of_classicalModelOn_TS5`
below. -/
theorem classicalModelOn_TS5_iff {D : Set (Label Atom)} {R : Label Atom → Label Atom → Prop} :
    ClassicalModelOn TS5 D R ↔
      ((∀ x ∈ D, R x x) ∧ (∀ x ∈ D, ∀ y ∈ D, R x y → R y x) ∧
        (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, R x y → R y z → R x z)) := by
  constructor
  · intro h
    exact ⟨h GeomAxiom.T GeomAxiom.T_mem_TS5, h GeomAxiom.B GeomAxiom.B_mem_TS5,
      h GeomAxiom.Four GeomAxiom.Four_mem_TS5⟩
  · rintro ⟨hT, hB, hF⟩ χ hχ
    rcases hχ with rfl | rfl | rfl
    · exact hT
    · exact hB
    · exact hF

/-- **Reflexive + Euclidean ⟹ equivalence relation.** A relation satisfying `χ_T` and `χ_5` is
automatically symmetric (via reflexivity, instantiating Euclideanness at the reflexive point)
and transitive (via that derived symmetry, instantiating Euclideanness again); together with
reflexivity this gives a full equivalence relation. **Symmetry is free and structural here** --
exactly as `cs5Tail_symm` is free on the CSLib canonical-model side: it was never the gap in
either framework. Consumed by the frame-class match (`cs5FCIncest`
conjuncts 1, 2, 5) via `equivalence_of_classicalModel_TS5` below. -/
theorem equivalence_of_refl_eucl {R : Label Atom → Label Atom → Prop}
    (hrefl : GeomAxiom.T.Holds R) (heucl : GeomAxiom.Five.Holds R) : Equivalence R where
  refl := hrefl
  symm := fun {x y} hxy => heucl x y x hxy (hrefl x)
  trans := fun {x y z} hxy hyz => heucl y x z (heucl x y x hxy (hrefl x)) hyz

/-- A relation classically modelling the whole of `TS5` is an equivalence relation:
`H ⊨_cl 𝒯_S5 ⟹ H` is reflexive, symmetric and transitive. This is exactly `TPrime`'s clause 0
instantiated at `𝒯_S5`, the fact the frame-class match needs to discharge `cs5FCIncest`'s
reflexivity, transitivity, and `cs5Incest` conjuncts.

Under the `{χ_T, χ_B, χ_4}` presentation this is **immediate**: `χ_T`, `χ_B` and `χ_4` unfold, via
`GeomAxiom.Holds`, to literally reflexivity, symmetry and transitivity, so each field is a direct
projection of clause 0 with no derivation step. This is the payoff of fixing `TS5` as `IKTB4`
rather than `IKT5` -- see the `TS5` docstring. -/
theorem equivalence_of_classicalModel_TS5 {R : Label Atom → Label Atom → Prop}
    (h : ClassicalModel TS5 R) : Equivalence R where
  refl := h GeomAxiom.T GeomAxiom.T_mem_TS5
  symm := fun {x y} hxy => h GeomAxiom.B GeomAxiom.B_mem_TS5 x y hxy
  trans := fun {x y z} hxy hyz => h GeomAxiom.Four GeomAxiom.Four_mem_TS5 x y z hxy hyz

/-! ## The domain-relative equivalence design choice

**Design choice, resolved here**: under the `ClassicalModelOn` repair, `TPrime.clModel` only
supplies reflexivity/symmetry/transitivity **on `G.X`**, not type-wide, so the equivalence the
frame-class match (`FrameClass.lean`) needs is necessarily **domain-relative**, not the type-wide
`Equivalence` `equivalence_of_classicalModel_TS5` above produces. This module commits to
carrying a domain-relative equivalence throughout (`EquivalenceOn`), rather than switching the
world domain to the subtype `↥H.X` -- the domain-relative-predicate route requires no change to
`Context`/`TPrime`'s existing `Label Atom`-indexed fields, whereas a subtype-domain route would
ripple through every clause. `equivalence_of_classicalModel_TS5` above is retained unchanged (a
true, harmless fact about the type-wide clause, e.g. for callers not needing domain-relativity);
it is `equivalence_of_classicalModelOn_TS5` below that `FrameClass.lean` consumes. -/

/-- **Domain-relative equivalence**: `R` is reflexive, symmetric and transitive **on `D`** only
(no claim is made about pairs outside `D`). The domain-relative analogue of `Equivalence` that
`TPrime.clModel : ClassicalModelOn 𝒯 G.X G.R` supports. -/
structure EquivalenceOn (D : Set (Label Atom)) (R : Label Atom → Label Atom → Prop) : Prop where
  /-- Reflexivity on `D`. -/
  refl : ∀ x ∈ D, R x x
  /-- Symmetry on `D`. -/
  symm : ∀ x ∈ D, ∀ y ∈ D, R x y → R y x
  /-- Transitivity on `D`. -/
  trans : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, R x y → R y z → R x z

/-- A relation domain-relatively modelling `TS5` is a domain-relative equivalence relation:
`H ⊨_CL^{H.X} 𝒯_S5 ⟹ H` is reflexive, symmetric and transitive **on `H.X`**. This is exactly
`TPrime`'s repaired clause 0 instantiated at `𝒯_S5`, and is what the frame-class match
(`FrameClass.lean`) consumes to discharge `cs5FCIncest`'s reflexivity, transitivity, and
`cs5Incest` conjuncts over
the domain-relative canonical model. Immediate from `classicalModelOn_TS5_iff`, for the same
reason `equivalence_of_classicalModel_TS5` is immediate from `ClassicalModel`: `χ_T`/`χ_B`/`χ_4`
unfold, via `GeomAxiom.HoldsOn`, to literally domain-relative reflexivity/symmetry/transitivity. -/
theorem equivalence_of_classicalModelOn_TS5 {D : Set (Label Atom)}
    {R : Label Atom → Label Atom → Prop} (h : ClassicalModelOn TS5 D R) : EquivalenceOn D R :=
  let ⟨hT, hB, hF⟩ := classicalModelOn_TS5_iff.mp h
  { refl := hT, symm := hB, trans := hF }

end Cslib.Logic.Modal.Labelled
