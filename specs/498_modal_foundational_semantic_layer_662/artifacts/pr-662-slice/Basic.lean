/-
Copyright (c) 2026 Fabrizio Montesi, Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marianna Girlando, Benjamin Brast-McKie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Logic.Nonempty
public import Cslib.Foundations.Relation.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToAdditive

/-! # Modal Logic

Modal logic is a logic for reasoning about relational structures, studying statements about
necessity (`□φ`) and possibility `◇φ`.

## Primitives

The formula type uses `{atom, bot, imp, and, or, box, diamond}` as native constructors,
mirroring `PL.Proposition`'s native `and`/`or`. Negation and verum remain derived connectives
via the Lukasiewicz convention: `¬φ := φ → ⊥`, `⊤ := ⊥ → ⊥`.

**Why is diamond primitive here (unlike the historical CSLib presentation)?** Classically,
diamond can be derived from box as `◇φ := ¬□¬φ`, and box alone suffices for necessitation and
the K axiom. However, task 441 makes `diamond` a native constructor (alongside `and`/`or`) so
that: (1) the tableau and truth-lemma machinery get one decomposition rule per connective
(structural induction, no Lukasiewicz-bridge lemmas), and (2) future non-classical modal
logics (intuitionistic, minimal — see [Blackburn2001] Chapter 1, [ChagrovZakharyaschev1997]
Section 3.1) can reuse this same datatype, since `□` and `◇` become independent operators in
those settings. `HasDia` (`Foundations/Logic/Connectives.lean`) is instantiated below alongside
`HasAnd`/`HasOr`. Classically, the duality `◇φ ↔ ¬□¬φ` is recovered as a genuine *theorem*
(`Satisfies.dual`, proved semantically) rather than holding definitionally; at the Hilbert
proof-system level, the duality is recovered via the `AxiomDiaDualityFwd`/`AxiomDiaDualityBack`
characterization schemata (see `Foundations/Logic/Axioms.lean`), instantiated for all systems
in `ProofSystem/Instances/*.lean`.

Note: The propositional formula type `PL.Proposition` has `and`/`or` as native constructors
with `HasAnd`/`HasOr` instances; `Modal.Proposition` now mirrors this directly, additionally
providing `HasDia`. The embedding `PL.Proposition.toModal` (in `FromPropositional`) still
produces the raw nested-`imp`/`bot` shape for `and`/`or` on its RHS (a conservativity artifact
of the shared `PL.Proposition.embed` skeleton), documented at its declaration site.

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
* The definitions of theory equivalence and the denotational semantics of worlds are inspired by
  the development of `Cslib.Logic.HML`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

/-- A model consists of a relation between worlds `r` and a valuation `v`. -/
structure Model (World : Type*) (Atom : Type*) where
  /-- World accessibility relation. -/
  r : World → World → Prop
  /-- Valuation of atoms at a world. -/
  v : World → Atom → Prop

/-- Propositions. Primitives are atoms, falsum, implication, conjunction, disjunction,
necessity (box), and possibility (diamond). -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
  /-- Implication. -/
  | imp (φ₁ φ₂ : Proposition Atom)
  /-- Conjunction. -/
  | and (φ₁ φ₂ : Proposition Atom)
  /-- Disjunction. -/
  | or (φ₁ φ₂ : Proposition Atom)
  /-- Necessity / box. -/
  | box (φ : Proposition Atom)
  /-- Possibility / diamond. -/
  | diamond (φ : Proposition Atom)
  deriving DecidableEq

/-- Register `Modal.Proposition` as an instance of `ModalConnectives`.

Registered before the derived-connective `abbrev`s so that the
`PropositionalConnectives.neg` / `.top` defaults are in scope
when `Proposition.neg` and `Proposition.top` are elaborated. -/
instance : ModalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp
  box := .box

/-- Register `HasAnd` instance for `Proposition`. -/
instance : HasAnd (Proposition Atom) where
  and := .and

/-- Register `HasOr` instance for `Proposition`. -/
instance : HasOr (Proposition Atom) where
  or := .or

/-- Register `HasDia` instance for `Proposition`. -/
instance : HasDia (Proposition Atom) where
  dia := .diamond

/-- Negation as derived connective: ¬φ := φ → ⊥.

Delegates to the canonical `PropositionalConnectives.neg` default (task 340). -/
abbrev Proposition.neg (φ : Proposition Atom) : Proposition Atom :=
  PropositionalConnectives.neg φ

/-- Verum / top: ⊤ := ⊥ → ⊥.

Delegates to the canonical `PropositionalConnectives.top` default (task 340). -/
abbrev Proposition.top : Proposition Atom := PropositionalConnectives.top

/-- Reduction lemma: `neg φ` unfolds to `.imp φ .bot`. -/
@[simp] lemma Proposition.neg_def (φ : Proposition Atom) : Proposition.neg φ = .imp φ .bot := rfl

/-- Reduction lemma: `top` unfolds to `.imp .bot .bot`. -/
@[simp] lemma Proposition.top_def : (Proposition.top : Proposition Atom) = .imp .bot .bot := rfl

/-- Bi-implication. -/
abbrev Proposition.iff (φ₁ φ₂ : Proposition Atom) : Proposition Atom :=
  .and (.imp φ₁ φ₂) (.imp φ₂ φ₁)

/-- Bottom element of `Proposition Atom`, registered as the canonical `⊥`. -/
instance : Bot (Proposition Atom) := ⟨.bot⟩

@[inherit_doc] scoped prefix:40 "¬" => Proposition.neg
@[inherit_doc] scoped infix:36 " ∧ " => Proposition.and
@[inherit_doc] scoped infix:35 " ∨ " => Proposition.or
@[inherit_doc] scoped infix:30 " → " => Proposition.imp
@[inherit_doc] scoped prefix:40 "□" => Proposition.box
@[inherit_doc] scoped prefix:40 "◇" => Proposition.diamond
@[inherit_doc] scoped infix:30 " ↔ " => Proposition.iff

/-- Satisfaction relation. `Satisfies m w φ` means that, in the model `m`, the world `w` satisfies
the proposition `φ`. -/
@[scoped grind]
def Satisfies (m : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p => m.v w p
  | .bot => False
  | .imp φ₁ φ₂ => Satisfies m w φ₁ → Satisfies m w φ₂
  | .and φ₁ φ₂ => Satisfies m w φ₁ ∧ Satisfies m w φ₂
  | .or φ₁ φ₂ => Satisfies m w φ₁ ∨ Satisfies m w φ₂
  | .box φ => ∀ w', m.r w w' → Satisfies m w' φ
  | .diamond φ => ∃ w', m.r w w' ∧ Satisfies m w' φ

/-- Satisfaction of negation. -/
theorem Satisfies.neg_iff : Satisfies m w (¬φ) ↔ ¬Satisfies m w φ :=
  ⟨fun h hs => h hs, fun h hs => absurd hs h⟩

/-- Satisfaction of diamond. -/
theorem Satisfies.diamond_iff : Satisfies m w (◇φ) ↔ ∃ w', m.r w w' ∧ Satisfies m w' φ :=
  Iff.rfl

/-- Satisfaction of conjunction. -/
theorem Satisfies.and_iff : Satisfies m w (φ₁ ∧ φ₂) ↔ Satisfies m w φ₁ ∧ Satisfies m w φ₂ :=
  Iff.rfl

/-- Satisfaction of disjunction. -/
theorem Satisfies.or_iff : Satisfies m w (φ₁ ∨ φ₂) ↔ Satisfies m w φ₁ ∨ Satisfies m w φ₂ :=
  Iff.rfl

/-- Judgement, representing the conclusions one reaches in modal logic. -/
structure Judgement World Atom where
  /-- Constructs a judgement. -/
  mk ::
  /-- Model. -/
  m : Model World Atom
  /-- The world satisfying the proposition `φ`. -/
  w : World
  /-- The proposition satisfied by the world `w`. -/
  φ : Proposition Atom

@[inherit_doc] scoped notation "Modal[" m "," w " ⊨ " φ "]" => Judgement.mk m w φ

/-- Satisfaction for judgements. This just refers to the unbundled `Satisfies`. -/
@[simp, scoped grind =]
def Satisfies.Bundled (j : Judgement World Atom) : Prop := Satisfies j.m j.w j.φ

/-- Register `Judgement` as a `HasInferenceSystem`, using `Satisfies.Bundled` as the
satisfaction predicate. -/
instance : HasInferenceSystem (Judgement World Atom) := ⟨Satisfies.Bundled⟩

open scoped InferenceSystem Proposition

/-- Unfolding lemma: the derivation notation `⇓Modal[m,w ⊨ φ]` equals `Satisfies m w φ`. -/
@[scoped grind =]
theorem derivation_def {m : Model World Atom} {w : World} {φ : Proposition Atom} :
  ⇓Modal[m,w ⊨ φ] = Satisfies m w φ := rfl

/-- A world satisfies a proposition iff it does not satisfy the negation of the proposition. -/
@[scoped grind =]
theorem neg_satisfies : ⇓Modal[m,w ⊨ ¬φ] ↔ ¬⇓Modal[m,w ⊨ φ] := Satisfies.neg_iff

/-- Characterisation of the `∨` connective. -/
@[scoped grind =]
theorem Satisfies.or_iff_or {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∨ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∨ ⇓Modal[m,w ⊨ φ₂] := Satisfies.or_iff

/-- Characterisation of the `→` connective. -/
@[scoped grind =]
theorem Satisfies.impl_iff_impl {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ → φ₂] ↔ (⇓Modal[m,w ⊨ φ₁] → ⇓Modal[m,w ⊨ φ₂]) :=
  Iff.rfl

/-- Characterisation of the `□` modality. -/
@[scoped grind =]
theorem Satisfies.box_iff_forall {m : Model World Atom} :
    ⇓Modal[m,w ⊨ □φ] ↔ ∀ w', m.r w w' → ⇓Modal[m,w' ⊨ φ] :=
  Iff.rfl

/-- Characterisation of the `◇` modality. -/
@[scoped grind =]
theorem Satisfies.diamond_iff_exists {m : Model World Atom} :
    ⇓Modal[m,w ⊨ ◇φ] ↔ ∃ w', m.r w w' ∧ ⇓Modal[m,w' ⊨ φ] := Satisfies.diamond_iff

/-- Characterisation of `∧` in terms of satisfaction. -/
@[scoped grind =]
theorem Satisfies.and_iff_and {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∧ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∧ ⇓Modal[m,w ⊨ φ₂] := Satisfies.and_iff

/-- The theory of a world in a model is the set of all propositions that it satisfies. -/
abbrev theory (m : Model World Atom) (w : World) : Set (Proposition Atom) :=
  {φ | ⇓Modal[m,w ⊨ φ]}

/-- Two worlds are theory-equivalent under a model if they have the same theory. -/
abbrev TheoryEq (m : Model World Atom) (w₁ w₂ : World) :=
  theory m w₁ = theory m w₂

/-- Two worlds are theory-equivalent iff they satisfy the same propositions. -/
theorem TheoryEq.ext_iff : TheoryEq m w₁ w₂ ↔ (∀ φ, φ ∈ theory m w₁ ↔ φ ∈ theory m w₂) :=
  Set.ext_iff

/-- Any proposition satisfied by a world is in the theory of that world. -/
@[scoped grind →]
theorem satisfies_theory (h : Satisfies m w φ) : φ ∈ theory m w := h

/-- If two worlds are not theory equivalent, there exists a distinguishing proposition. -/
lemma not_theoryEq_satisfies (h : ¬TheoryEq m w₁ w₂) :
    ∃ φ, (⇓Modal[m,w₁ ⊨ φ] ∧ ¬⇓Modal[m,w₂ ⊨ φ]) := by
  rw [TheoryEq.ext_iff] at h
  push Not at h
  obtain ⟨φ, h⟩ := h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨φ, h1, h2⟩
  · exact ⟨¬φ, neg_satisfies.mpr h1, fun h3 => neg_satisfies.mp h3 h2⟩

/-- If two worlds are theory equivalent and the former satisfies a proposition, the latter does as
well. -/
theorem theoryEq_satisfies {m : Model World Atom} (h : TheoryEq m w₁ w₂)
    (hs : Satisfies m w₁ φ) : ⇓Modal[m,w₂ ⊨ φ] := by
  apply TheoryEq.ext_iff.1 at h
  exact (h φ).mp hs

/-- The K axiom, valid for all models. -/
theorem Satisfies.k : ⇓Modal[m,w ⊨ □(φ₁ → φ₂) → (□φ₁ → □φ₂)] := by
  change Satisfies m w (.imp (.box (.imp φ₁ φ₂)) (.imp (.box φ₁) (.box φ₂)))
  simp only [Satisfies]
  intro h1 h2 w' hr
  exact h1 w' hr (h2 w' hr)

/-- The dual axiom, valid for all models.

Since `diamond` is a native constructor (task 441), this is no longer a definitional
unfolding: it is proved as a genuine semantic theorem using excluded middle. -/
theorem Satisfies.dual : ⇓Modal[m,w ⊨ ◇φ ↔ ¬□¬φ] := by
  change Satisfies m w (.iff (.diamond φ) (.neg (.box (.neg φ))))
  simp only [Proposition.neg_def, Satisfies]
  constructor
  · rintro ⟨w', hr, hs⟩ hbox
    exact hbox w' hr hs
  · intro h
    by_contra hc
    push Not at hc
    exact h fun w' hr hs => hc w' hr hs

/-- A proposition is valid in a class of models `S` (modelled as a set) if it is satisfied under
all models in `S` for all worlds. -/
@[simp, scoped grind =]
def Proposition.valid (S : Set (Model World Atom)) (φ : Proposition Atom) : Prop :=
  ∀ (m : Model World Atom), ∀ (_ : m ∈ S), ∀ (w : World), ⇓Modal[m,w ⊨ φ]

/-- The modal logic of a class of models `S` is the set of all propositions valid in `S`. -/
@[simp, scoped grind =]
def logic (S : Set (Model World Atom)) : Set (Proposition Atom) :=
  {φ | φ.valid S}

end Cslib.Logic.Modal
