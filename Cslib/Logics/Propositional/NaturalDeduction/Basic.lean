/-
Copyright (c) 2025 Thomas Waring, 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Benjamin Brast-McKie
-/
module

public import Cslib.Logics.Propositional.Defs
public import Cslib.Foundations.Logic.InferenceSystem
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.Image

/-! # Natural deduction for propositional logic

We define, for minimal logic, deduction trees (a `Type`) and derivability (a `Prop`) relative to a
`Theory` (set of propositions).

## Main definitions

- `Sequent` : a pair of a context and conclusion.
- `Derivation` : natural deduction derivation, done in "sequent style", ie with explicit
hypotheses at each step. Contexts are `Finset`'s of propositions, which avoids explicit contraction
and exchange, and the axiom rule derives `Γ ⊢ A` for any context `Γ` with `A ∈ Γ`, allowing
weakening to be a derived rule. The derivation may appeal to hypotheses from the `Theory T`. This
defines an instance of `InferenceSystem T Sequent`.
- `Theory.equiv` : `Type`-valued equivalence of propositions.
- `Theory.Equiv` : `Prop`-valued equivalence of propositions.

## Main results

- `Derivation.weak` : weakening as a derived rule.
- `Derivation.cut`, `Derivation.subs` : replace a hypothesis in a derivation — the two versions
differ in the construction of the relevant derivation.
- `Theory.equiv_equivalence` : equivalence of propositions is an equivalence relation.

## Notation

The sequent `⟨Γ, A⟩` is notated `Γ ⊢ A`, so that a derivation using axioms from a theory `T` is
noted `T⇓(Γ ⊢ A)`. We define also an `InferenceSystem T (Proposition Atom)`, so that `T⇓A`
abbreviates a derivation of `A` in the empty context: `T⇓(∅ ⊢ A)`.

## Implementation notes

The primitive inference rules are: axiom (from theory), assumption (from context),
conjunction introduction and elimination (×2), disjunction introduction (×2) and elimination,
implication introduction and elimination, and ex falso quodlibet (bottom elimination) — 11
constructors in total. The `efq` rule is *gated*: it carries an `[IsIntuitionistic T]` instance
binder, so it is available at IPL/CPL strength but unconstructible at MPL strength.

**MPL is the base logic.** Logic strength is controlled by the theory parameter:
- `MPL` (minimal propositional logic [Johansson1937]): the theory admits no `IsIntuitionistic`
  instance, so `efq` is gated off, leaving the 10 ungated primitive rules. MPL is the base
  derivation relation — it has no ⊥-rule. This is formalized by `MinimalDerivation` and
  `IsBotRuleFree` (see below).
- `IPL` (intuitionistic propositional logic): `[IsIntuitionistic T]` holds, so the explosion
  property module `efq` (`⊥ → A`) is available. IPL = MPL + explosion.
- `CPL` (classical propositional logic): adds the classicality property `¬¬A → A` (double
  negation elimination). CPL = IPL + classicality.

The **property modules** are typeclasses: `IsIntuitionistic T` (explosion/efq) and
`IsClassical T` (double negation elimination). Each property is *additive*: it can be
layered on the MPL base independently. `MinimalAxioms` identifies the 8 connective axiom
schemas of the Hilbert substrate shared by all three systems.

**Design A: `⊥` as a primitive nullary connective (this implementation).** The signature
is the fixed set `{⊥, →, ∧, ∨}` where `⊥` is a nullary constructor of `Proposition` with
*underdetermined meaning* — no intro rule and no elim rule at base (MPL) strength. The
meaning of `⊥` is determined by the property modules: at IPL/CPL strength `efq` adds the
elim rule (explosion); at MPL strength `⊥` is an ordinary proposition with no special rule.

The canonical justification for Design A is **substitution-invariance**: any renaming of
atoms that sends `p₀ ↦ ⊥` must commute with derivability. If `⊥` were treated as a
meta-symbol excluded from the language, the language would fail to be closed under
propositional substitution — `A[p₀/⊥]` would escape the language. Concretely: the
`substAtom` operation (`Derivation.substAtom`) works uniformly over all propositions
including `⊥ = .bot` (the `| .bot => .bot` case in every embedding). This is also the
free-algebra argument: the type `Proposition Atom` is the free monad on `{⊥, →, ∧, ∨}`,
so `⊥` is an element of this algebra, not an external constant. See the
[CSLib Zulip thread on Propositional Logic](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic)
for the full argument (#604219492).

**Design B (not implemented, documented here for reference).** Two variants were
considered but rejected: (B1) a fragment language without `⊥` for MPL, extending the
language to add `⊥` for IPL; and (B2) encoding `⊥` as a distinguished atom `⊥ : Atom`.
Both violate substitution-invariance: B1 requires a language extension rather than a
property extension; B2 treats `⊥` as syntactically distinguishable from other atoms while
remaining in the same type, which breaks the free-algebra structure. Design A (⊥ as
constructor, explosion as property) is the only choice compatible with the shared
`Proposition` type and the single-substitution-monad architecture.

`⊥` is the one connective with **no introduction rule** in any proof system; the asymmetry
(0 intro rules, 1 elim rule) is a property of `⊥` itself, not a defect of this design. This
matches Gentzen-style constructor-rule correspondence in on-paper natural deduction
presentations ([Prawitz1965], §10.4 of [TroelstraVanDalen1988], §2.2 of
[SorensenUrzyczyn2006]), which include bottom elimination as a primitive rule. Gating
`efq` on `[IsIntuitionistic T]` keeps API uniformity and zero duplication across the
multi-logic hierarchy (Modal, Temporal, Bimodal): a single `Proposition` type with primitive
`⊥` lets MPL, IPL, and CPL share one substitution monad and one set of bridge lemmas,
with the `FromPropositional` embeddings using the direct map `| .bot => .bot`.

This design choice and its trade-offs are discussed further in the
[CSLib Zulip thread on Propositional Logic](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic).

## References

* [I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*][Johansson1937]
* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
* [A. S. Troelstra, D. van Dalen,
  *Constructivism in Mathematics: An Introduction*][TroelstraVanDalen1988], Section 10.4
* [G. Gentzen,
  *Untersuchungen über das logische Schließen*][Gentzen1935]
* [M. H. B. Sørensen, P. Urzyczyn,
  *Lectures on the Curry-Howard Isomorphism*][SorensenUrzyczyn2006], Section 2.2
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

variable {Atom : Type u} [DecidableEq Atom]

/-- Contexts are finsets of propositions. -/
abbrev Ctx (Atom) := Finset (Proposition Atom)

/-- Map a context along a substitution. -/
def Ctx.subst {Atom Atom' : Type u} [DecidableEq Atom'] (f : Atom → Proposition Atom') :
    Ctx Atom → Ctx Atom' := Finset.image (· >>= f)

/-- Sequents {A₁, ..., Aₙ} ⊢ B. -/
abbrev Sequent {Atom} := Ctx Atom × Proposition Atom

@[inherit_doc Sequent]
scoped notation Γ:60 " ⊢ " A => (⟨Γ, A⟩ : Sequent)

/-- A `T`-derivation of {A₁, ..., Aₙ} ⊢ B demonstrates B using (undischarged) assumptions among Aᵢ,
possibly appealing to axioms from `T`. Primitives: axiom, assumption, conjunction intro/elim,
disjunction intro/elim, and implication intro/elim. **MPL is the base**: these 10 ungated rules
are the base derivation relation, with no ⊥-rule. Ex falso quodlibet (bottom elimination) is the
explosion property module `efq`, gated by `[IsIntuitionistic T]`: it is available at IPL/CPL
strength but unconstructible at MPL strength, making IPL = MPL + explosion. -/
inductive Theory.Derivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  /-- Axiom -/
  | ax {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ T) : Derivation Γ A
  /-- Assumption -/
  | ass {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ Γ) : Derivation Γ A
  /-- Conjunction introduction -/
  | andI {A B : Proposition Atom} (G : Ctx Atom) :
      Derivation G A → Derivation G B → Derivation G (A ∧ B)
  /-- Left conjunction elimination -/
  | andE1 {A B : Proposition Atom} (G : Ctx Atom) :
      Derivation G (A ∧ B) → Derivation G A
  /-- Right conjunction elimination -/
  | andE2 {A B : Proposition Atom} (G : Ctx Atom) :
      Derivation G (A ∧ B) → Derivation G B
  /-- Left disjunction introduction -/
  | orI1 {A B : Proposition Atom} (G : Ctx Atom) :
      Derivation G A → Derivation G (A ∨ B)
  /-- Right disjunction introduction -/
  | orI2 {A B : Proposition Atom} (G : Ctx Atom) :
      Derivation G B → Derivation G (A ∨ B)
  /-- Disjunction elimination -/
  | orE {A B C : Proposition Atom} (G : Ctx Atom) :
      Derivation G (A ∨ B) → Derivation (insert A G) C → Derivation (insert B G) C →
      Derivation G C
  /-- Implication introduction -/
  | impI {A B : Proposition Atom} (Γ : Ctx Atom) :
      Derivation (insert A Γ) B → Derivation Γ (A → B)
  /-- Implication elimination (modus ponens) -/
  | impE {Γ : Ctx Atom} {A B : Proposition Atom} :
      Derivation Γ (A → B) → Derivation Γ A → Derivation Γ B
  /-- The explosion property module: ex falso quodlibet (bottom elimination).
  Requires `[IsIntuitionistic T]`. Available at IPL/CPL strength; absent at MPL strength.
  This gated constructor marks the transition from MPL (base, no ⊥-rule) to IPL (MPL +
  explosion). `MPL = ∅` admits no `IsIntuitionistic` instance, so `efq` is structurally
  unconstructible at minimal strength (not merely inadmissible). Every `MinimalDerivation`
  satisfies `IsBotRuleFree` precisely because no `efq` term is constructible there. -/
  | efq {Γ : Ctx Atom} {A : Proposition Atom} [IsIntuitionistic T] :
      Derivation Γ ⊥ → Derivation Γ A

/-- Inference system for derivations under the theory `T`. -/
instance (T : Theory Atom) : InferenceSystem T (Sequent (Atom := Atom)) where
  derivation S := T.Derivation S.1 S.2

/-- Inference system for propositions (using the empty context). -/
instance (T : Theory Atom) : InferenceSystem T (Proposition Atom) where
  derivation A := T.Derivation ∅ A

variable {T : Theory Atom}

/-- A derivation `T⇓A` is definitionally equal to a derivation of the empty sequent `T⇓(∅ ⊢ A)`. -/
theorem Theory.Derivation.emptySequent_eq {A : Proposition Atom} : T⇓A = T⇓(∅ ⊢ A) := rfl

/-- Derivability `DerivableIn T A` is equivalent to derivability of the empty sequent
`DerivableIn T (∅ ⊢ A)`. -/
theorem DerivableIn.iff_derivableIn_empty {A : Proposition Atom} :
    DerivableIn T A ↔ DerivableIn T (∅ ⊢ A) := by rfl

/-! ### Gate-free fragment view (S1): MinimalDerivation and IsBotRuleFree

The following abbreviation and predicate name the `⊥`-rule-free view of the shared
`Theory.Derivation` inductive. They do not introduce a new inductive type — the design
deliberately shares one derivation type across MPL/IPL/CPL, gating `efq` on
`[IsIntuitionistic T]`. These objects exist so that later phases can refer to the
gate-free fragment by name rather than reasoning about the absence of `efq` ad hoc.

The connection to the gate mechanism: `efq` requires `[IsIntuitionistic T]`; `MPL = ∅`
admits no `IsIntuitionistic` instance (`IsIntuitionistic MPL` would require `IPL ⊆ ∅`,
which is false). Hence every `MinimalDerivation` is automatically `IsBotRuleFree`.
This is the operational content of `min_consistent : ¬ Derivable MinPropAxiom ⊥`
(MinLindenbaum.lean) and `instIsIntuitionisticExtension` (Defs.lean): the `efq`
constructor is structurally unconstructible at MPL strength, not merely inadmissible. -/

/-- A derivation is `⊥`-rule-free if it does not appeal to the `efq` constructor.
Since `efq` carries `[IsIntuitionistic T]`, every derivation at `MPL` strength
(`MPL = ∅` admits no `IsIntuitionistic` instance) satisfies this predicate.
This predicate names the gate-free fragment within the shared derivation inductive
without introducing a separate `⊥`-rule-free inductive type. -/
def Theory.Derivation.IsBotRuleFree {T : Theory Atom} :
    ∀ {Γ : Ctx Atom} {A : Proposition Atom}, T.Derivation Γ A → Prop
  | _, _, ax _ => True
  | _, _, ass _ => True
  | _, _, andI _ D₁ D₂ => D₁.IsBotRuleFree ∧ D₂.IsBotRuleFree
  | _, _, andE1 _ D => D.IsBotRuleFree
  | _, _, andE2 _ D => D.IsBotRuleFree
  | _, _, orI1 _ D => D.IsBotRuleFree
  | _, _, orI2 _ D => D.IsBotRuleFree
  | _, _, orE _ D DA DB => D.IsBotRuleFree ∧ DA.IsBotRuleFree ∧ DB.IsBotRuleFree
  | _, _, impI _ D => D.IsBotRuleFree
  | _, _, impE D D' => D.IsBotRuleFree ∧ D'.IsBotRuleFree
  | _, _, efq _ => False

/-- The type of minimal-strength derivations of `Γ ⊢ A`: `Theory.Derivation` for the
empty theory `MPL = ∅`. Since `MPL` admits no `IsIntuitionistic` instance, the `efq`
constructor is unconstructible at this strength — every term of `MinimalDerivation Γ A`
is automatically `IsBotRuleFree`. This corresponds to the `efq`-free sub-language that
is the natural deduction fragment of minimal propositional logic (MPL). -/
abbrev Theory.MinimalDerivation (Γ : Ctx Atom) (A : Proposition Atom) :=
  MPL.Derivation Γ A

/-- An equivalence between A and B is a derivation of B from A and vice-versa. -/
def Theory.equiv (A B : Proposition Atom) :=
  T⇓({A} ⊢ B) × T⇓({B} ⊢ A)

/-- Forward direction of an equivalence. -/
def Theory.equiv.mp {A B : Proposition Atom} (e : T.equiv A B) : T⇓({A} ⊢ B) := e.1

/-- Reverse direction of an equivalence. -/
def Theory.equiv.mpr {A B : Proposition Atom} (e : T.equiv A B) : T⇓({B} ⊢ A) := e.2

/-- `A` and `B` are T-equivalent if `T.equiv A B` is nonempty. -/
def Theory.Equiv (A B : Proposition Atom) := Nonempty (T.equiv A B)

@[inherit_doc]
scoped notation A " ≡[" T' "] " B:29 => Theory.Equiv (T := T') A B

lemma Theory.Equiv.mp {A B : Proposition Atom} (h : A ≡[T] B) : DerivableIn T ({A} ⊢ B) :=
  ⟨h.some.mp⟩

lemma Theory.Equiv.mpr {A B : Proposition Atom} (h : A ≡[T] B) : DerivableIn T ({B} ⊢ A) :=
  ⟨h.some.mpr⟩

theorem Theory.equiv_iff {A B : Proposition Atom} :
  A ≡[T] B ↔ DerivableIn T ({A} ⊢ B) ∧ DerivableIn T ({B} ⊢ A) := by
  constructor
  · intro h
    exact ⟨h.mp, h.mpr⟩
  · intro ⟨⟨D⟩, ⟨E⟩⟩
    exact ⟨D, E⟩

/-- Minimally equivalent propositions. -/
abbrev Equiv : Proposition Atom → Proposition Atom → Prop := MPL.Equiv

@[inherit_doc]
scoped infix:29 " ≡ " => Equiv

open Derivation DerivableIn

/-! ### Operations on derivations -/

/-- Weakening is a derived rule. -/
def Theory.Derivation.weak {T T' : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) : T.Derivation Γ A → T'.Derivation Δ A
  | ax hA => ax <| hTheory hA
  | ass hA => ass <| hCtx hA
  | @andI _ _ _ A B G D₁ D₂ => andI Δ (D₁.weak hTheory hCtx) (D₂.weak hTheory hCtx)
  | @andE1 _ _ _ A B G D => andE1 Δ (D.weak hTheory hCtx)
  | @andE2 _ _ _ A B G D => andE2 Δ (D.weak hTheory hCtx)
  | @orI1 _ _ _ A B G D => orI1 Δ (D.weak hTheory hCtx)
  | @orI2 _ _ _ A B G D => orI2 Δ (D.weak hTheory hCtx)
  | @orE _ _ _ _ _ _ _ D DA DB =>
    orE Δ (D.weak hTheory hCtx)
      (DA.weak hTheory (Finset.insert_subset_insert _ hCtx))
      (DB.weak hTheory (Finset.insert_subset_insert _ hCtx))
  | @impI _ _ _ A B Γ D => impI (Δ) <| D.weak hTheory <| Finset.insert_subset_insert _ hCtx
  | impE D D' => impE (D.weak hTheory hCtx) (D'.weak hTheory hCtx)
  | efq D =>
      haveI : IsIntuitionistic T' := instIsIntuitionisticExtension hTheory
      efq (D.weak hTheory hCtx)

/-- Weakening the theory only. -/
def Theory.Derivation.weakTheory {T T' : Theory Atom} {Γ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') : T⇓(Γ ⊢ A) → T'⇓(Γ ⊢ A):=
  Derivation.weak hTheory Finset.Subset.rfl

/-- Weakening the context only. -/
def Theory.Derivation.weakCtx {T : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hCtx : Γ ⊆ Δ) : T⇓(Γ ⊢ A) → T⇓(Δ ⊢ A) :=
  Derivation.weak Set.Subset.rfl hCtx

/-- Proof irrelevant weakening. -/
theorem DerivableIn.weak {T T' : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) : DerivableIn T (Γ ⊢ A) → DerivableIn T' (Δ ⊢ A)
  | ⟨D⟩ => ⟨D.weak hTheory hCtx⟩

/-- Proof irrelevant weakening of the theory. -/
theorem DerivableIn.weakTheory {T T' : Theory Atom} {Γ : Ctx Atom} {A : Proposition Atom}
    (hTheory : T ⊆ T') : DerivableIn T (Γ ⊢ A) → DerivableIn T' (Γ ⊢ A)
  | ⟨D⟩ => ⟨D.weakTheory hTheory⟩

/-- Proof irrelevant weakening of the context. -/
theorem DerivableIn.weakCtx {T : Theory Atom} {Γ Δ : Ctx Atom} {A : Proposition Atom}
    (hCtx : Γ ⊆ Δ) : DerivableIn T (Γ ⊢ A) → DerivableIn T (Δ ⊢ A)
  | ⟨D⟩ => ⟨D.weakCtx hCtx⟩

/--
Implement the cut rule, removing a hypothesis `A` from `E` using a derivation `D`. This is *not*
substitution, which would replace appeals to `A` in `E` by the whole derivation `D`.
-/
def Theory.Derivation.cut {Γ Δ : Ctx Atom} {A B : Proposition Atom}
    (D : T⇓(Γ ⊢ A)) (E : T⇓(insert A Δ ⊢ B)) : T⇓((Γ ∪ Δ) ⊢ B) := by
  refine impE (A := A) ?_ (D.weakCtx Finset.subset_union_left)
  have : insert A Δ ⊆ insert A (Γ ∪ Δ) := by grind
  exact impI (Γ ∪ Δ) <| E.weakCtx this

/-- Proof irrelevant cut rule. -/
theorem DerivableIn.cut {Γ Δ : Ctx Atom} {A B : Proposition Atom} :
    DerivableIn T (Γ ⊢ A) → DerivableIn T ((insert A Δ) ⊢ B) → DerivableIn T ((Γ ∪ Δ) ⊢ B)
  | ⟨D⟩, ⟨E⟩ => ⟨D.cut E⟩

/-- Remove unnecessary hypotheses. This can't be computable because it requires picking an order
on the finset `Δ`. -/
theorem DerivableIn.cut_away {Γ Γ' : Ctx Atom} {B : Proposition Atom}
    (hΔ : ∀ A ∈ Γ', DerivableIn T (Γ ⊢ A)) (hDer : DerivableIn T ((Γ ∪ Γ') ⊢ B)) :
    DerivableIn T (Γ ⊢ B) := by
  induction Γ' using Finset.induction with
  | empty => exact DerivableIn.weakCtx (by grind) hDer
  | insert A Δ hA ih =>
    apply ih
    · intro A' hA'
      exact hΔ A' <| Finset.mem_insert_of_mem hA'
    · apply Finset.union_left_idem Γ Δ ▸ DerivableIn.cut (Δ := Γ ∪ Δ)
      · exact hΔ A <| Finset.mem_insert_self A Δ
      · rwa [← Finset.union_insert A Γ Δ]

/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`.
Note: propositional logic has no binding operators, so capture avoidance does not apply here.
This substitution is straightforward replacement without any variable renaming concerns. -/
def Theory.Derivation.subs {Γ Γ' Δ : Ctx Atom} {B : Proposition Atom}
    (Ds : ∀ A ∈ Γ', T⇓(Δ ⊢ A)) :
      T.Derivation Γ B → T.Derivation (Γ \ Γ' ∪ Δ) B
  | ax hB => ax hB
  | @ass _ _ _ _ B hB => by
    by_cases B ∈ Γ'
    case pos h =>
      exact (Ds B h).weakCtx <| by grind
    case neg h =>
      exact ass <| by grind
  | @andI _ _ _ A' B' _ E₁ E₂ => andI _ (E₁.subs Ds) (E₂.subs Ds)
  | @andE1 _ _ _ A' B' _ E => andE1 _ (E.subs Ds)
  | @andE2 _ _ _ A' B' _ E => andE2 _ (E.subs Ds)
  | @orI1 _ _ _ A' B' _ E => orI1 _ (E.subs Ds)
  | @orI2 _ _ _ A' B' _ E => orI2 _ (E.subs Ds)
  | @orE _ _ _ A' B' C' _ E EA EB => by
    apply orE _ (E.subs Ds)
    · rw [show insert A' (Γ \ Γ' ∪ Δ) = (insert A' Γ \ Γ') ∪ insert A' Δ by grind]
      exact EA.subs Ds |>.weakCtx (by grind)
    · rw [show insert B' (Γ \ Γ' ∪ Δ) = (insert B' Γ \ Γ') ∪ insert B' Δ by grind]
      exact EB.subs Ds |>.weakCtx (by grind)
  | @impI _ _ _ A' _ _ E .. => by
    apply impI
    rw [show insert A' (Γ \ Γ' ∪ Δ) = (insert A' Γ \ Γ') ∪ insert A' Δ by grind]
    exact E.subs Ds |>.weakCtx (by grind)
  | impE E E' => impE (E.subs Ds) (E'.subs Ds)
  | efq E => efq (E.subs Ds)

/-- Transport a derivation along a substitution of atoms. -/
def Theory.Derivation.substAtom {Atom Atom' : Type u} [DecidableEq Atom] [DecidableEq Atom']
    {T : Theory Atom} (f : Atom → Proposition Atom') {Γ : Ctx Atom} {B : Proposition Atom} :
    T.Derivation Γ B → (T.subst f).Derivation (Γ.subst f) (B >>= f)
  | ax h => ax <| Set.mem_image_of_mem (· >>= f) h
  | ass h => ass <| Finset.mem_image_of_mem (· >>= f) h
  | andI _ D₁ D₂ => andI _ (D₁.substAtom f) (D₂.substAtom f)
  | andE1 _ D => andE1 _ (D.substAtom f)
  | andE2 _ D => andE2 _ (D.substAtom f)
  | orI1 _ D => orI1 _ (D.substAtom f)
  | orI2 _ D => orI2 _ (D.substAtom f)
  | orE _ D DA DB =>
    orE _ (D.substAtom f)
      ((Finset.image_insert (· >>= f) _ _) ▸ (DA.substAtom f))
      ((Finset.image_insert (· >>= f) _ _) ▸ (DB.substAtom f))
  | impI _ D => impI _ <| (Finset.image_insert (· >>= f) _ _) ▸ (D.substAtom f)
  | impE D E => impE (D.substAtom f) (E.substAtom f)
  | efq D => impE (ax (Set.mem_image_of_mem (· >>= f) (IsIntuitionistic.efq _))) (D.substAtom f)

theorem DerivableIn.substAtom {Atom Atom' : Type u} [DecidableEq Atom] [DecidableEq Atom']
    {T : Theory Atom}
    (f : Atom → Proposition Atom') {Γ : Ctx Atom} {B : Proposition Atom} :
    DerivableIn T (Γ ⊢ B) → DerivableIn (T.subst f) ((Γ.subst f) ⊢ (B >>= f))
  | ⟨D⟩ => ⟨D.substAtom f⟩

/-! ### Properties of equivalence -/

/-- A derivation of the canonical tautology. -/
def Theory.derivationTop : T⇓(⊤ : Proposition Atom) :=
  impI ∅ <| ass <| by grind

/-- The verum `⊤` is derivable in any theory. -/
theorem derivableIn_top : DerivableIn T (⊤ : Proposition Atom) := ⟨derivationTop⟩

theorem derivable_iff_equiv_top (A : Proposition Atom) :
    DerivableIn T A ↔ A ≡[T] ⊤ := by
  constructor <;> intro h
  · refine ⟨derivationTop.weakCtx <| by grind, ?_⟩
    let D := Classical.choice h
    exact D.weakCtx <| by grind
  · have := DerivableIn.cut (derivableIn_top (T := T)) (B := A) (Δ := ∅)
    rw [←show (∅ : Ctx Atom) = ∅ ∪ ∅ by rfl] at this
    exact this h.mpr

namespace Theory

/-- Change the conclusion along an equivalence. -/
def mapEquivConclusion (Γ : Ctx Atom) {A B : Proposition Atom} (e : T.equiv A B)
    (D : T⇓(Γ ⊢ A)) : T⇓(Γ ⊢ B) :=
  Γ.union_empty ▸ Derivation.cut (Δ := ∅) D e.1

/-- Replace a hypothesis along an equivalence. -/
def mapEquivHypothesis (Γ : Ctx Atom) {A B : Proposition Atom} (e : T.equiv A B)
    (C : Proposition Atom) (D : T⇓(insert A Γ ⊢ C)) : T⇓(insert B Γ ⊢ C) := by
  have : insert B Γ = {B} ∪ Γ := rfl
  exact this ▸ Derivation.cut e.2 D

/-- An equivalence of a proposition with itself. -/
def equiv.refl (A : Proposition Atom) : T.equiv A A :=
  let D : T⇓({A} ⊢ A) := ass <| Finset.mem_singleton_self A;
  ⟨D, D⟩

/-- Reverse an equivalence. -/
def equiv.symm {A B : Proposition Atom} (e : T.equiv A B) : T.equiv B A :=
  ⟨e.mpr, e.mp⟩

/-- Compose two equivalences. -/
def equiv.trans {A B C : Proposition Atom} (eAB : T.equiv A B)
    (eBC : T.equiv B C) : T.equiv A C :=
  ⟨mapEquivConclusion _ eBC eAB.mp, mapEquivConclusion _ eAB.symm eBC.mpr⟩

/-- `A` and `B` are equivalent (in `T`) iff they are provable from the same contexts. -/
theorem equiv_iff_equiv_derivableIn {A B : Proposition Atom} :
    A ≡[T] B ↔ ∀ Γ : Ctx Atom, DerivableIn T (Γ ⊢ A) ↔ DerivableIn T (Γ ⊢ B) := by
  constructor
  · intro ⟨e⟩ Γ
    exact ⟨fun D => mapEquivConclusion Γ e D.some, fun D => mapEquivConclusion Γ e.symm D.some⟩
  · intro h
    rw [equiv_iff]
    constructor
    · exact (h {A}).mp ⟨ass <| by grind⟩
    · exact (h {B}).mpr ⟨ass <| by grind⟩

/-- `A` and `B` are equivalent (in `T`) iff they have the same strength as hypotheses. -/
theorem equiv_iff_equiv_derivableIn_hypothesis {A B : Proposition Atom} :
    A ≡[T] B ↔
      ∀ (Γ : Ctx Atom) (C : Proposition Atom),
      DerivableIn T ((insert A Γ) ⊢ C) ↔ DerivableIn T ((insert B Γ) ⊢ C) := by
  constructor
  · intro ⟨e⟩ Γ C
    exact ⟨fun D => mapEquivHypothesis Γ e C D.some, fun E => mapEquivHypothesis Γ e.symm C E.some⟩
  · intro h
    rw [equiv_iff]
    constructor
    · exact (h ∅ B).mpr ⟨ass <| by grind⟩
    · exact (h ∅ A).mp ⟨ass <| by grind⟩

@[refl]
theorem Equiv.refl {T : Theory Atom} (A : Proposition Atom) : A ≡[T] A := by
  exact ⟨equiv.refl A⟩

theorem Equiv.symm {T : Theory Atom} {A B : Proposition Atom} :
    (A ≡[T] B) → B ≡[T] A
  | ⟨e⟩ => ⟨e.symm⟩

theorem Equiv.trans {T : Theory Atom} {A B C : Proposition Atom} :
    (A ≡[T] B) → (B ≡[T] C) → A ≡[T] C
  | ⟨e⟩, ⟨e'⟩ => ⟨e.trans e'⟩

/-- Equivalence is indeed an equivalence relation. -/
theorem equiv_equivalence (T : Theory Atom) : Equivalence (T.Equiv (Atom := Atom)) :=
  ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- The setoid of propositions under equivalence. -/
protected def propositionSetoid (T : Theory Atom) : Setoid (Proposition Atom) :=
  ⟨T.Equiv, T.equiv_equivalence⟩

/-! ### Congruence lemmas for equivalence -/

/-- Congruence of equivalence under implication: if `A ≡[T] A'` and `B ≡[T] B'`
then `(A → B) ≡[T] (A' → B')`.

Proved using `impI`, `impE`, and the existing `mapEquivConclusion`/`mapEquivHypothesis`
helpers. -/
theorem Equiv.imp_congr {T : Theory Atom} {A A' B B' : Proposition Atom}
    (hA : A ≡[T] A') (hB : B ≡[T] B') : (A → B) ≡[T] (A' → B') := by
  obtain ⟨eA⟩ := hA; obtain ⟨eB⟩ := hB
  -- In the forward direction, `impI {A → B}` produces context `insert A' {A → B}`.
  -- There: A' ∈ insert A' {A → B} by mem_insert_self
  --        A → B ∈ insert A' {A → B} by mem_insert_of_mem, mem_singleton_self
  let fwd : T⇓({A → B} ⊢ A' → B') :=
    Derivation.impI {A → B}
      (mapEquivConclusion _ eB
        (Derivation.impE
          (Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          (mapEquivConclusion _ eA.symm
            (Derivation.ass (Finset.mem_insert_self _ _)))))
  let bwd : T⇓({A' → B'} ⊢ A → B) :=
    Derivation.impI {A' → B'}
      (mapEquivConclusion _ eB.symm
        (Derivation.impE
          (Derivation.ass (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          (mapEquivConclusion _ eA
            (Derivation.ass (Finset.mem_insert_self _ _)))))
  exact ⟨⟨fwd, bwd⟩⟩

/-- Congruence of equivalence under conjunction: if `A ≡[T] A'` and `B ≡[T] B'`
then `(A ∧ B) ≡[T] (A' ∧ B')`. -/
theorem Equiv.and_congr {T : Theory Atom} {A A' B B' : Proposition Atom}
    (hA : A ≡[T] A') (hB : B ≡[T] B') : (A ∧ B) ≡[T] (A' ∧ B') := by
  obtain ⟨eA⟩ := hA; obtain ⟨eB⟩ := hB
  let fwd : T⇓({A ∧ B} ⊢ A' ∧ B') :=
    Derivation.andI {A ∧ B}
      (mapEquivConclusion _ eA
        (Derivation.andE1 {A ∧ B} (Derivation.ass (Finset.mem_singleton_self _))))
      (mapEquivConclusion _ eB
        (Derivation.andE2 {A ∧ B} (Derivation.ass (Finset.mem_singleton_self _))))
  let bwd : T⇓({A' ∧ B'} ⊢ A ∧ B) :=
    Derivation.andI {A' ∧ B'}
      (mapEquivConclusion _ eA.symm
        (Derivation.andE1 {A' ∧ B'} (Derivation.ass (Finset.mem_singleton_self _))))
      (mapEquivConclusion _ eB.symm
        (Derivation.andE2 {A' ∧ B'} (Derivation.ass (Finset.mem_singleton_self _))))
  exact ⟨⟨fwd, bwd⟩⟩

/-- Congruence of equivalence under disjunction: if `A ≡[T] A'` and `B ≡[T] B'`
then `(A ∨ B) ≡[T] (A' ∨ B')`. -/
theorem Equiv.or_congr {T : Theory Atom} {A A' B B' : Proposition Atom}
    (hA : A ≡[T] A') (hB : B ≡[T] B') : (A ∨ B) ≡[T] (A' ∨ B') := by
  obtain ⟨eA⟩ := hA; obtain ⟨eB⟩ := hB
  -- orE context: `insert A {A ∨ B}` and `insert B {A ∨ B}`
  let fwd : T⇓({A ∨ B} ⊢ A' ∨ B') :=
    Derivation.orE {A ∨ B} (Derivation.ass (Finset.mem_singleton_self _))
      (Derivation.orI1 _
        (mapEquivConclusion _ eA (Derivation.ass (Finset.mem_insert_self _ _))))
      (Derivation.orI2 _
        (mapEquivConclusion _ eB (Derivation.ass (Finset.mem_insert_self _ _))))
  let bwd : T⇓({A' ∨ B'} ⊢ A ∨ B) :=
    Derivation.orE {A' ∨ B'} (Derivation.ass (Finset.mem_singleton_self _))
      (Derivation.orI1 _
        (mapEquivConclusion _ eA.symm (Derivation.ass (Finset.mem_insert_self _ _))))
      (Derivation.orI2 _
        (mapEquivConclusion _ eB.symm (Derivation.ass (Finset.mem_insert_self _ _))))
  exact ⟨⟨fwd, bwd⟩⟩

end Cslib.Logic.PL.Theory
