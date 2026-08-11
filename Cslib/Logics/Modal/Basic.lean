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
public import Mathlib.Order.Notation
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
the K axiom. However, `diamond` is a native constructor (alongside `and`/`or`) so that:
(1) the tableau and truth-lemma machinery get one decomposition rule per connective (structural
induction, no Lukasiewicz-bridge lemmas), and (2) future non-classical modal logics
(intuitionistic, minimal — see [Simpson1994]) can reuse this same datatype, since `□` and `◇`
become independent operators in those settings. `HasDiamond` (`Foundations/Logic/Connectives.lean`)
is instantiated below alongside `HasAnd`/`HasOr`. Classically, the duality `◇φ ↔ ¬□¬φ` is
recovered as a genuine *theorem* (`Satisfies.dual`, proved semantically) rather than holding
definitionally; at the Hilbert proof-system level, the duality is recovered via the
`AxiomDiamondDualityFwd`/`AxiomDiamondDualityBack` characterization schemata (see
`Foundations/Logic/Axioms.lean`), instantiated for all systems in `ProofSystem/Instances/*.lean`.

Note: The propositional formula type `PL.Proposition` has `and`/`or` as native constructors
with `HasAnd`/`HasOr` instances; `Modal.Proposition` now mirrors this directly, additionally
providing `HasDiamond`. The embedding `PL.Proposition.toModal` (in `FromPropositional`) still
produces the raw nested-`imp`/`bot` shape for `and`/`or` on its RHS (a conservativity artifact
of the shared `PL.Proposition.embed` skeleton), documented at its declaration site.

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994]
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

/-- Register `HasDiamond` instance for `Proposition`. -/
instance : HasDiamond (Proposition Atom) where
  diamond := .diamond

/-- Bridge lemma: the concrete constructor `Proposition.and` agrees with the `HasAnd` projection
supplied by the `HasAnd` instance above. Compensates for the local `∧` notation bound to
`Proposition.and`, which shadows the scoped `HasAnd.and` notation from `Cslib.Logic`. -/
@[scoped grind =] lemma Proposition.and_def (φ ψ : Proposition Atom) :
    φ.and ψ = HasAnd.and φ ψ := rfl

/-- Bridge lemma: the concrete constructor `Proposition.or` agrees with the `HasOr` projection
supplied by the `HasOr` instance above. Compensates for the local `∨` notation bound to
`Proposition.or`, which shadows the scoped `HasOr.or` notation from `Cslib.Logic`. -/
@[scoped grind =] lemma Proposition.or_def (φ ψ : Proposition Atom) :
    φ.or ψ = HasOr.or φ ψ := rfl

/-- Bridge lemma: the concrete constructor `Proposition.imp` agrees with the `HasImp` projection
supplied by the `ModalConnectives` instance above. Compensates for the local `→` notation
bound to `Proposition.imp`, which shadows the scoped `HasImp.imp` notation from
`Cslib.Logic`. -/
@[scoped grind =] lemma Proposition.imp_def (φ ψ : Proposition Atom) :
    φ.imp ψ = HasImp.imp φ ψ := rfl

/-- Bridge lemma: the concrete constructor `Proposition.box` agrees with the `HasBox` projection
supplied by the `ModalConnectives` instance above. Compensates for the local `□` notation
bound to `Proposition.box`, which shadows the scoped `HasBox.box` notation from
`Cslib.Logic`. -/
@[scoped grind =] lemma Proposition.box_def (φ : Proposition Atom) :
    φ.box = HasBox.box φ := rfl

/-- Bridge lemma: the concrete constructor `Proposition.diamond` agrees with the `HasDiamond`
projection supplied by the `HasDiamond` instance above. Compensates for the local `◇` notation
bound to `Proposition.diamond`, which shadows the scoped `HasDiamond.diamond` notation from
`Cslib.Logic`. -/
@[scoped grind =] lemma Proposition.diamond_def (φ : Proposition Atom) :
    φ.diamond = HasDiamond.diamond φ := rfl

/-- Negation as derived connective: ¬φ := φ → ⊥.

Delegates to the canonical `PropositionalConnectives.neg` default. -/
abbrev Proposition.neg (φ : Proposition Atom) : Proposition Atom :=
  PropositionalConnectives.neg φ

/-- Verum / top: ⊤ := ⊥ → ⊥.

Delegates to the canonical `PropositionalConnectives.top` default. -/
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

/-- Relabel the atoms of a proposition along `f : Atom → Atom'`, leaving the connective
structure untouched. This is the formula-level functorial action used to transport
propositions (and, via `Metalogic.Deriv.map`, derivations) across a change of atom type --
e.g. tagging a proposition as belonging to the "left" or "right" copy of a doubled atom space
`Atom ⊕ Atom`. -/
def Proposition.map (f : Atom → Atom') : Proposition Atom → Proposition Atom'
  | .atom p => .atom (f p)
  | .bot => .bot
  | .imp φ₁ φ₂ => .imp (φ₁.map f) (φ₂.map f)
  | .and φ₁ φ₂ => .and (φ₁.map f) (φ₂.map f)
  | .or φ₁ φ₂ => .or (φ₁.map f) (φ₂.map f)
  | .box φ => .box (φ.map f)
  | .diamond φ => .diamond (φ.map f)

@[simp] theorem Proposition.map_atom (f : Atom → Atom') (p : Atom) :
    (Proposition.atom p).map f = .atom (f p) := rfl

@[simp] theorem Proposition.map_bot (f : Atom → Atom') :
    (Proposition.bot : Proposition Atom).map f = .bot := rfl

@[simp] theorem Proposition.map_imp (f : Atom → Atom') (φ₁ φ₂ : Proposition Atom) :
    (φ₁.imp φ₂).map f = (φ₁.map f).imp (φ₂.map f) := rfl

@[simp] theorem Proposition.map_and (f : Atom → Atom') (φ₁ φ₂ : Proposition Atom) :
    (φ₁.and φ₂).map f = (φ₁.map f).and (φ₂.map f) := rfl

@[simp] theorem Proposition.map_or (f : Atom → Atom') (φ₁ φ₂ : Proposition Atom) :
    (φ₁.or φ₂).map f = (φ₁.map f).or (φ₂.map f) := rfl

@[simp] theorem Proposition.map_box (f : Atom → Atom') (φ : Proposition Atom) :
    (Proposition.box φ).map f = .box (φ.map f) := rfl

@[simp] theorem Proposition.map_diamond (f : Atom → Atom') (φ : Proposition Atom) :
    (Proposition.diamond φ).map f = .diamond (φ.map f) := rfl

/-- Auxiliary injectivity statement for `Proposition.map`, proved by structural induction with
an explicit second proposition (rather than via `Function.Injective`'s implicit binders, which
do not generalize cleanly under `induction`). -/
theorem Proposition.map_injective_aux {f : Atom → Atom'} (hf : Function.Injective f)
    (φ ψ : Proposition Atom) (h : φ.map f = ψ.map f) : φ = ψ := by
  induction φ generalizing ψ with
  | atom p =>
    cases ψ <;> simp only [Proposition.map, Proposition.atom.injEq, reduceCtorEq] at h
    exact congrArg Proposition.atom (hf h)
  | bot =>
    cases ψ <;> simp [Proposition.map] at h
    rfl
  | imp φ₁ φ₂ ih₁ ih₂ =>
    cases ψ <;> simp only [Proposition.map, Proposition.imp.injEq, reduceCtorEq] at h
    exact congrArg₂ Proposition.imp (ih₁ _ h.1) (ih₂ _ h.2)
  | and φ₁ φ₂ ih₁ ih₂ =>
    cases ψ <;> simp only [Proposition.map, Proposition.and.injEq, reduceCtorEq] at h
    exact congrArg₂ Proposition.and (ih₁ _ h.1) (ih₂ _ h.2)
  | or φ₁ φ₂ ih₁ ih₂ =>
    cases ψ <;> simp only [Proposition.map, Proposition.or.injEq, reduceCtorEq] at h
    exact congrArg₂ Proposition.or (ih₁ _ h.1) (ih₂ _ h.2)
  | box φ ih =>
    cases ψ <;> simp only [Proposition.map, Proposition.box.injEq, reduceCtorEq] at h
    exact congrArg Proposition.box (ih _ h)
  | diamond φ ih =>
    cases ψ <;> simp only [Proposition.map, Proposition.diamond.injEq, reduceCtorEq] at h
    exact congrArg Proposition.diamond (ih _ h)

/-- `Proposition.map` is injective whenever the underlying atom relabeling is injective. -/
theorem Proposition.map_injective {f : Atom → Atom'} (hf : Function.Injective f) :
    Function.Injective (Proposition.map f) :=
  fun _ _ h => Proposition.map_injective_aux hf _ _ h

/-- `Proposition.map` along the identity atom relabeling is the identity. A generic relabeling
fact, useful whenever a formula is transported through an atom-type isomorphism or projection. -/
@[simp] theorem Proposition.map_id (φ : Proposition Atom) :
    φ.map (id : Atom → Atom) = φ := by
  induction φ with
  | atom p => rfl
  | bot => rfl
  | imp _ _ ih₁ ih₂ => simp [Proposition.map, ih₁, ih₂]
  | and _ _ ih₁ ih₂ => simp [Proposition.map, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [Proposition.map, ih₁, ih₂]
  | box _ ih => simp [Proposition.map, ih]
  | diamond _ ih => simp [Proposition.map, ih]

/-- `Proposition.map` is functorial: relabeling along `f` then `g` equals relabeling along the
composite `g ∘ f`. A generic relabeling-composition fact, useful whenever a formula is
transported through a chain of atom-type maps. -/
theorem Proposition.map_map (f : Atom → Atom') (g : Atom' → Atom'') (φ : Proposition Atom) :
    (φ.map f).map g = φ.map (g ∘ f) := by
  induction φ with
  | atom p => rfl
  | bot => rfl
  | imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | and _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | box _ ih => simp [ih]
  | diamond _ ih => simp [ih]

@[inherit_doc] scoped prefix:40 "¬" => Proposition.neg
@[inherit_doc] scoped infixr:20 " ↔ " => Proposition.iff

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

Since `diamond` is a native constructor, this is no longer a definitional
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

/-- The T axiom, valid for all reflexive models. -/
theorem Satisfies.t {m : Model World Atom} [instRefl : Std.Refl m.r] {w : World}
    (φ : Proposition Atom) : ⇓Modal[m,w ⊨ φ → ◇φ] := by
  change Satisfies m w φ → Satisfies m w (◇φ)
  intro hφ
  rw [diamond_iff]
  exact ⟨w, instRefl.refl w, hφ⟩

/-- Any model that admits the axiom T is reflexive. -/
theorem Satisfies.t_refl {r : World → World → Prop} [Nonempty Atom]
    (h : ∀ {v} {w} {φ : Proposition Atom}, ⇓Modal[⟨r, v⟩,w ⊨ φ → ◇φ]) : Std.Refl r where
  refl w := by
    have a := Classical.arbitrary Atom
    let v : World → Atom → Prop := fun w' _ => w' = w
    have h' := h (v := v) (w := w) (φ := .atom a)
    simp only [derivation_def] at h'
    have hsat : Satisfies ⟨r, v⟩ w (.atom a) := rfl
    have h₂ := h' hsat
    rw [diamond_iff] at h₂
    obtain ⟨w', hr, hv⟩ := h₂
    change w' = w at hv
    rwa [hv] at hr

/-- In any reflexive model, `□φ → φ` is equivalent to `φ → ◇φ`. -/
theorem Satisfies.t_box_diamond [Std.Refl m.r] :
    ⇓Modal[m,w ⊨ □φ → φ] ↔ ⇓Modal[m,w ⊨ φ → ◇φ] := by
  have hrefl := Std.Refl.refl (r := m.r) w
  change ((∀ w', m.r w w' → Satisfies m w' φ) → Satisfies m w φ) ↔
       (Satisfies m w φ → Satisfies m w (◇φ))
  constructor
  · intro h hφ
    rw [diamond_iff]
    exact ⟨w, hrefl, hφ⟩
  · intro h hbox
    have hφ := hbox w hrefl
    exact hφ

/-- The B axiom, valid for all symmetric models. -/
theorem Satisfies.b {m : Model World Atom} [instSymm : Std.Symm m.r] {w : World}
    (φ : Proposition Atom) :
    ⇓Modal[m,w ⊨ φ → □◇φ] := by
  change Satisfies m w φ → ∀ w', m.r w w' → Satisfies m w' (◇φ)
  intro hφ w' hr
  rw [diamond_iff]
  exact ⟨w, instSymm.symm w w' hr, hφ⟩

/-- Any model that admits the axiom B is symmetric. -/
theorem Satisfies.b_symm {World Atom} {r : World → World → Prop} [Nonempty Atom]
    (h : ∀ {v} {w} {φ : Proposition Atom}, ⇓Modal[⟨r, v⟩,w ⊨ φ → □◇φ]) : Std.Symm r where
  symm {w₁ w₂} hr := by
    have a := Classical.arbitrary Atom
    let v₁ := fun (w' : World) (_ : Atom) => w' = w₁
    have h₁ : Satisfies ⟨r, v₁⟩ w₁ (.atom a) →
               ∀ w', r w₁ w' → Satisfies ⟨r, v₁⟩ w' (◇(.atom a)) :=
      h (v := v₁) (w := w₁) (φ := .atom a)
    have hsat : Satisfies ⟨r, v₁⟩ w₁ (.atom a) := rfl
    have h₂ := h₁ hsat w₂ hr
    rw [diamond_iff] at h₂
    obtain ⟨w'', hr', hv⟩ := h₂
    simp only [Satisfies] at hv
    rwa [← hv]

/-- The 4 axiom, valid for all transitive models. -/
theorem Satisfies.four {m : Model World Atom} [IsTrans World m.r] {w : World}
    (φ : Proposition Atom) : ⇓Modal[m,w ⊨ ◇◇φ → ◇φ] := by
  change Satisfies m w (◇◇φ) → Satisfies m w (◇φ)
  rw [diamond_iff, diamond_iff]
  intro ⟨w', hr₁, h'⟩
  rw [diamond_iff] at h'
  obtain ⟨w'', hr₂, hs⟩ := h'
  exact ⟨w'', IsTrans.trans _ _ _ hr₁ hr₂, hs⟩

/-- Any model that admits 4 is transitive. -/
theorem Satisfies.four_trans {r : World → World → Prop} [Nonempty Atom]
    (h : ∀ {v} {w} {φ : Proposition Atom}, ⇓Modal[⟨r, v⟩,w ⊨ ◇◇φ → ◇φ]) : IsTrans World r where
  trans w₁ w₂ w₃ h₁ h₂ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (_ : Atom) => w' = w₃
    have h' : Satisfies ⟨r, v⟩ w₁ (◇◇(.atom a)) →
              Satisfies ⟨r, v⟩ w₁ (◇(.atom a)) :=
      h (v := v) (w := w₁) (φ := .atom a)
    have hdd : Satisfies ⟨r, v⟩ w₁ (◇◇(.atom a)) := by
      rw [diamond_iff]
      exact ⟨w₂, h₁, by rw [diamond_iff]; exact ⟨w₃, h₂, rfl⟩⟩
    have h₃ := h' hdd
    rw [diamond_iff] at h₃
    obtain ⟨w', hr, hv⟩ := h₃
    simp only [Satisfies] at hv
    rwa [← hv]

/-- The 5 axiom, valid for all Euclidean models. -/
theorem Satisfies.five {m : Model World Atom} [Relation.RightEuclidean m.r]
    {w : World}
    (φ : Proposition Atom) : ⇓Modal[m,w ⊨ ◇φ → □◇φ] := by
  have heuc := @Relation.RightEuclidean.rightEuclidean (r := m.r)
  change Satisfies m w (◇φ) → ∀ w', m.r w w' → Satisfies m w' (◇φ)
  intro hdiam w' hr
  rw [diamond_iff] at hdiam ⊢
  obtain ⟨w'', hr', hs⟩ := hdiam
  exact ⟨w'', heuc hr hr', hs⟩

/-- Any model that admits 5 is Euclidean. -/
theorem Satisfies.five_rightEuclidean {r : World → World → Prop} [Nonempty Atom]
    (h : ∀ {v} {w : World} {φ : Proposition Atom}, ⇓Modal[⟨r, v⟩,w ⊨ ◇φ → □◇φ]) :
    Relation.RightEuclidean r where
  rightEuclidean {w₁ w₂ w₃} h₁ h₂ := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (_ : Atom) => w' = w₃
    have h' : Satisfies ⟨r, v⟩ w₁ (◇(.atom a)) →
              ∀ w', r w₁ w' → Satisfies ⟨r, v⟩ w' (◇(.atom a)) :=
      h (v := v) (w := w₁) (φ := .atom a)
    have hdiam : Satisfies ⟨r, v⟩ w₁ (◇(.atom a)) := by
      rw [diamond_iff]; exact ⟨w₃, h₂, rfl⟩
    have h₂' := h' hdiam w₂ h₁
    rw [diamond_iff] at h₂'
    obtain ⟨w', hr, hv⟩ := h₂'
    simp only [Satisfies] at hv
    rwa [← hv]

/-- The D axiom, valid for all serial models. -/
theorem Satisfies.d {m : Model World Atom} [hSer : Relation.Serial m.r] {w}
    (φ : Proposition Atom) :
    ⇓Modal[m,w ⊨ □φ → ◇φ] := by
  change (∀ w', m.r w w' → Satisfies m w' φ) → Satisfies m w (◇φ)
  intro hbox
  rw [diamond_iff]
  obtain ⟨w', hr⟩ := hSer.serial w
  exact ⟨w', hr, hbox w' hr⟩

/-- Any model that admits D is serial. -/
theorem Satisfies.d_serial {r : World → World → Prop} [Nonempty Atom]
    (h : ∀ {v} {w} {φ : Proposition Atom}, ⇓Modal[⟨r, v⟩,w ⊨ □φ → ◇φ]) : Relation.Serial r where
  serial w₁ := by
    have a := Classical.arbitrary Atom
    let v := fun (_ : World) (_ : Atom) => True
    have h' : (∀ w', r w₁ w' → Satisfies ⟨r, v⟩ w' (.atom a)) →
              Satisfies ⟨r, v⟩ w₁ (◇(.atom a)) :=
      h (v := v) (w := w₁) (φ := .atom a)
    have hbox : ∀ w', r w₁ w' → Satisfies ⟨r, v⟩ w' (.atom a) :=
      fun _ _ => trivial
    have h₃ := h' hbox
    rw [diamond_iff] at h₃
    obtain ⟨w', hr, _⟩ := h₃
    exact ⟨w', hr⟩

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
