/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Syntax

/-! # The Labelled Deduction System `N_IK(𝒯)`

This module lands A. K. Simpson's labelled natural-deduction system `N_IK` [Simpson1994],
Figure 4-1 (`:4630-4670`), extended with the geometric rules `{(R_χ) | χ ∈ 𝒯}` (`:4940`) that
give `N_IK(𝒯)`, plus the consequence relation `Γ ⊢_G x:A` (`:5090`) and the weakening /
graph-morphism lemmas (Prop. 4.4.1, `:5135`).

**Scope note**: this file lands the deduction system only. It is the adequacy gate's
prerequisite -- `Adequacy.lean` (the adequacy bridge, developed separately) quantifies over the
`NIK` relation defined here and needs nothing more from this file than what is landed below.
Contexts (`Context.lean`), the Prime Lemma, the canonical model, the birelation construction, the
frame-class match, and final assembly are **not** attempted here.

## Design

### Encoding decision: named labels with cofinite side conditions, not locally-nameless

The plan's contingency note suggested a locally-nameless encoding (precedent: CSLib's
`Languages/LambdaCalculus/LocallyNameless`). **This module departs from that suggestion, and the
departure is flagged here as required by the escalation protocol.** Locally-nameless indices are
designed for binders scoped *within a single inductive term*; here, by contrast, a label is a
*name* shared across two independently-threaded pieces of judgement state -- the formula context
`Γ` (a `List (LabelledFormula Atom)`) and the graph `G` (a `Graph Atom`, `Syntax.lean`) -- and a
fresh label introduced by `(□I)`/`(◇E)` must simultaneously avoid capture in *both*. There is no
single inductive term whose binding structure de Bruijn indices could describe. Instead this module
uses the **cofinite-quantification** technique that CSLib's own locally-nameless developments use
for their `abs`-style binders (e.g. `Typing.abs` in
`Cslib/Languages/LambdaCalculus/LocallyNameless/Stlc/Basic.lean`): the eigenvariable rules
`(□I)`/`(◇E)` quantify over *all* labels outside a finite exclusion set `L`, rather than
asserting existence of a single fresh witness. This is the standard technique (Aydemir et al.,
*Engineering Formal Metatheory*, POPL 2008) for making weakening lemmas immediate, without a
separate renaming/permutation lemma: the induction hypothesis at a cofinite premise already
covers every sufficiently fresh choice, so weakening a derivation to a bigger context or a bigger
graph is a direct pointwise application of the same premise, re-packaged under a larger exclusion
set. See `NIK.weaken` below.

### The geometric extension `(R_χ)`: 𝒯-closure of the graph relation, flagged

Report 01 cites the geometric rules `{(R_χ) | χ ∈ 𝒯}` only by source location (`:4940`) without
transcribing Figure 4-3's exact rule shape (the report explicitly does not reproduce it, since its
own scope was the completeness spine, not Chapter 4's syntax in full). **This is a genuine gap in
the available source material, flagged rather than guessed silently.** This module resolves it
via the standard treatment of geometric theories in labelled deduction (as in labelled sequent
calculi for modal logics, e.g. Negri's `G3`-systems): `(□E)` and `(◇I)` -- the two rules with a
relational premise, confirmed by inspection to be the only two (see `NIK.smoke_boxE` below and
the structural check accompanying it) -- consume not just a literal edge of
`G.R` but any edge in the **𝒯-closure** `TClosure 𝒯 G.R` of `G.R` under the axioms of `𝒯`
(reflexivity `χ_T`, symmetry `χ_B`, transitivity `χ_4`, Euclideanness `χ_5`).

Seriality (`χ_D`) is **not a constructor of `GeomAxiom` at all**, rather than being a constructor
that `TClosure` skips. It has an existential conclusion (`∀x, ∃y, xRy`) and so would need a
fresh-witness-introducing rule structurally like `(□I)`/`(◇E)`, plus a Skolem witness operator on
`Label`, not a pure relational closure. Representing it in the type while leaving `TClosure` and
`Label` unable to honour it would make `Context {χ_D}` a wrong definition -- the type would
advertise a constraint that no closure operator enforces. Excluding it from the type instead makes
that unrepresentable *by construction*. This costs nothing here: the target frame theory `𝒯_S5`
(fixed in `Context.lean`) does not include `χ_D`. Adding seriality later remains additive, but
must extend `GeomAxiom`, `TClosure`, and `Label`'s witness operators together.

### Why all four axioms are kept here, and none of them fixed

Simpson presents `IS5` as `IKT5` (`:3827`), i.e. as `Ax({χ_T, χ_5})`. CSLib's `CS5ModalAxiom`
(`CS5.lean:182`) is instead `IKTB4`, naming `bBox`/`bDia` (symmetry) and `4`. These are
Hilbert-equivalent presentations of the same logic (via Pacheco's `CS5 ≡ IS5`,
`CS5.lean:93-99`), but they are *structurally different* axiom/frame-condition sets, and the
equivalence is **not** constructively available off the shelf.

This module therefore fixes **nothing**: `GeomAxiom` below carries each of Simpson's universal
Horn basic geometric axioms (`T`, `B`, `Four`, `Five`) and `TClosure` implements the rule for
every one of them, so either presentation is expressible downstream. `Context.lean` is where the
target theory is actually fixed, as `𝒯_S5 := {χ_T, χ_B, χ_4}` -- matching `CS5ModalAxiom`
schema-for-schema and so avoiding an unproved constructive `IKT5 ⟺ IKTB4` bridge on the critical
path. See that file's `TS5` docstring for the full rationale.

## Contents

- `GeomAxiom`: the universal Horn basic geometric axioms `χ_T, χ_B, χ_4, χ_5` (Simpson §3.2;
  `χ_D` is excluded -- see the type's docstring).
- `GeomAxiom.Holds` / `ClassicalModel`: the classical-model semantics of a geometric axiom /
  theory on a relation (`G ⊨_cl 𝒯`).
- `TClosure`: the 𝒯-closure of a relation, realizing `(R_χ)` for every axiom of `GeomAxiom`.
- `NIK`: the labelled natural-deduction relation `Γ ⊢_G x:A`, i.e. `N_IK(𝒯)` (Figure 4-1 plus the
  geometric extension).
- `NIK.weaken`: the combined weakening / graph-morphism lemma (Prop. 4.4.1).
- `NIK.smoke_boxE`: the required smoke-test derivation `x:□A, xRy ⊢ y:A` via `(□E)`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 4 (`N_IK`, Figure 4-1, `:4630-4670`) and §5.1 (the consequence relation, `:5090-5135`).
-/

@[expose] public section

namespace Cslib.Logic.Modal.Labelled

universe u

variable {Atom : Type u}

/-! ## Geometric axioms and their closure -/

/-- The **universal Horn** basic geometric axioms of Simpson's frame theories,
`𝒯 ⊆ {χ_T, χ_B, χ_4, χ_5}` (§3.2). `T` = reflexivity, `B` = symmetry, `Four` = transitivity,
`Five` = Euclideanness.

**Why `χ_D` (seriality) is absent.** Simpson's §3.2 also lists `χ_D := ∀x, ∃y, xRy`. It is the
sole axiom of the five with an **existential conclusion**, and it is deliberately **not** a
constructor of this type. Every axiom represented here is quantifier-free in its conclusion, which
is exactly the property that lets `TClosure` (below) realize `(R_χ)` for **every** `χ` in this
type by a pure relational closure, with no fresh-witness-introducing rule and no Skolem witness
operator on `Label`. Admitting `χ_D` as a constructor without also extending `TClosure` and
`Label` would make `Context {χ_D}` (`Context.lean`) a *wrong definition*: the closure operators
would silently ignore the axiom while the type advertised that they honoured it. Adding seriality
later is purely additive but must extend `TClosure` and `Label`'s witness operators **in the same
change** as the constructor. -/
inductive GeomAxiom : Type where
  /-- Reflexivity: `∀x, xRx`. -/
  | T
  /-- Symmetry: `∀x y, xRy → yRx`. -/
  | B
  /-- Transitivity: `∀x y z, xRy → yRz → xRz`. -/
  | Four
  /-- Euclideanness: `∀x y z, xRy → xRz → yRz`. -/
  | Five

/-- The classical-model clause for a single geometric axiom on a relation `R`. -/
def GeomAxiom.Holds (χ : GeomAxiom) (R : Label Atom → Label Atom → Prop) : Prop :=
  match χ with
  | .T => ∀ x, R x x
  | .B => ∀ x y, R x y → R y x
  | .Four => ∀ x y z, R x y → R y z → R x z
  | .Five => ∀ x y z, R x y → R x z → R y z

/-- `R ⊨_cl 𝒯`: `R` is a classical model of every axiom in `𝒯` (Simpson `:5759`, `:5953`
clause 0). -/
def ClassicalModel (𝒯 : Set GeomAxiom) (R : Label Atom → Label Atom → Prop) : Prop :=
  ∀ χ ∈ 𝒯, χ.Holds R

/-- The **𝒯-closure** of a relation `R`: the smallest relation extending `R` that satisfies the
geometric axioms in `𝒯`. This realizes the geometric rules `(R_χ)` (`:4940`); see the module
docstring ("The geometric extension") for why this is flagged as a definitional choice. Because
every constructor of `GeomAxiom` is universal Horn (seriality is not representable -- see
`GeomAxiom`), this closure covers **every** axiom of the type, with no silently-ignored case. -/
inductive TClosure (𝒯 : Set GeomAxiom) (R : Label Atom → Label Atom → Prop) :
    Label Atom → Label Atom → Prop where
  /-- Every edge of `R` is in its 𝒯-closure. -/
  | base {x y} (h : R x y) : TClosure 𝒯 R x y
  /-- `(R_χ_T)`: reflexivity is licensed at every label once `χ_T ∈ 𝒯`. -/
  | refl (h : GeomAxiom.T ∈ 𝒯) (x : Label Atom) : TClosure 𝒯 R x x
  /-- `(R_χ_B)`: symmetry. -/
  | symm {x y} (h : GeomAxiom.B ∈ 𝒯) (hxy : TClosure 𝒯 R x y) : TClosure 𝒯 R y x
  /-- `(R_χ_4)`: transitivity. -/
  | trans {x y z} (h : GeomAxiom.Four ∈ 𝒯) (hxy : TClosure 𝒯 R x y)
      (hyz : TClosure 𝒯 R y z) : TClosure 𝒯 R x z
  /-- `(R_χ_5)`: Euclideanness. -/
  | eucl {x y z} (h : GeomAxiom.Five ∈ 𝒯) (hxy : TClosure 𝒯 R x y)
      (hxz : TClosure 𝒯 R x z) : TClosure 𝒯 R y z

/-- `TClosure` is monotone in the underlying relation: extending `R` to `R'` extends the
𝒯-closure accordingly. Used by `NIK.weaken`'s `(□E)`/`(◇I)` cases. -/
theorem TClosure.mono {𝒯 : Set GeomAxiom} {R R' : Label Atom → Label Atom → Prop}
    (hmono : ∀ x y, R x y → R' x y) {x y : Label Atom} (h : TClosure 𝒯 R x y) :
    TClosure 𝒯 R' x y := by
  induction h with
  | base h => exact .base (hmono _ _ h)
  | refl h x => exact .refl h x
  | symm h _ ih => exact .symm h ih
  | trans h _ _ ihxy ihyz => exact .trans h ihxy ihyz
  | eucl h _ _ ihxy ihxz => exact .eucl h ihxy ihxz

/-- The set of labels occurring (as the labelling prefix) in a context `Γ`. Used as the
"open assumptions" set against which `(□I)`/`(◇E)`'s eigenvariable freshness is checked --
sound because Simpson's own judgement `Γ ⊢_G x:A` already *defines* `Γ` to be exactly the open
assumptions of the derivation (`:5090`), so checking freshness against all of `Γ` is not an
approximation but a direct transcription. -/
def LabelledFormula.ctxLabels (Γ : List (LabelledFormula Atom)) : Set (Label Atom) :=
  {x | ∃ φ ∈ Γ, φ.lbl = x}

/-! ## The labelled deduction system `N_IK(𝒯)` -/

/-- The labelled natural-deduction consequence relation `Γ ⊢_G x:A`, i.e. `N_IK(𝒯)`
(Figure 4-1, `:4630-4670`, plus the geometric extension `{(R_χ) | χ ∈ 𝒯}`, `:4940`).

`(□I)` and `(◇E)` use **cofinite quantification** over a finite exclusion set `L` for their
eigenvariable `y` (see the module docstring, "Encoding decision"), which is what makes the
weakening lemma (`NIK.weaken`) a direct structural induction. `(□E)` and `(◇I)` are, by
inspection, the only two rules with a relational premise, and that premise ranges over the
**𝒯-closure** of `G.R` (see "The geometric extension"). -/
inductive NIK (𝒯 : Set GeomAxiom) : Graph Atom → List (LabelledFormula Atom) →
    LabelledFormula Atom → Prop where
  /-- Any formula already in the context is derivable. -/
  | assumption (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (φ : LabelledFormula Atom)
      (h : φ ∈ Γ) : NIK 𝒯 G Γ φ
  /-- Ex falso quodlibet, label-local. -/
  | efq (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A : Proposition Atom) (h : NIK 𝒯 G Γ (x ∶ .bot)) : NIK 𝒯 G Γ (x ∶ A)
  /-- `(∧I)`, label-local. -/
  | andI (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (hA : NIK 𝒯 G Γ (x ∶ A)) (hB : NIK 𝒯 G Γ (x ∶ B)) :
      NIK 𝒯 G Γ (x ∶ .and A B)
  /-- `(∧E)`, left projection. -/
  | andE1 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIK 𝒯 G Γ (x ∶ .and A B)) : NIK 𝒯 G Γ (x ∶ A)
  /-- `(∧E)`, right projection. -/
  | andE2 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIK 𝒯 G Γ (x ∶ .and A B)) : NIK 𝒯 G Γ (x ∶ B)
  /-- `(∨I)`, left injection. -/
  | orI1 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIK 𝒯 G Γ (x ∶ A)) : NIK 𝒯 G Γ (x ∶ .or A B)
  /-- `(∨I)`, right injection. -/
  | orI2 (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIK 𝒯 G Γ (x ∶ B)) : NIK 𝒯 G Γ (x ∶ .or A B)
  /-- `(∨E)`, label-local case split, discharging both branch assumptions. -/
  | orE (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B C : Proposition Atom) (hor : NIK 𝒯 G Γ (x ∶ .or A B))
      (hA : NIK 𝒯 G ((x ∶ A) :: Γ) (x ∶ C)) (hB : NIK 𝒯 G ((x ∶ B) :: Γ) (x ∶ C)) :
      NIK 𝒯 G Γ (x ∶ C)
  /-- `(⊃I)`, discharging the antecedent assumption. -/
  | impI (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (h : NIK 𝒯 G ((x ∶ A) :: Γ) (x ∶ B)) : NIK 𝒯 G Γ (x ∶ .imp A B)
  /-- `(⊃E)` / modus ponens, label-local. -/
  | impE (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
      (A B : Proposition Atom) (himp : NIK 𝒯 G Γ (x ∶ .imp A B)) (hA : NIK 𝒯 G Γ (x ∶ A)) :
      NIK 𝒯 G Γ (x ∶ B)
  /-- `(□E)`: from `x:□A` and a (possibly 𝒯-derived) edge `xRy`, conclude `y:A`. -/
  | boxE (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x y : Label Atom)
      (A : Proposition Atom) (hR : TClosure 𝒯 G.R x y) (h : NIK 𝒯 G Γ (x ∶ .box A)) :
      NIK 𝒯 G Γ (y ∶ A)
  /-- `(□I)`: if, for cofinitely many `y` (all `y` outside the finite exclusion set `L`), adding
  the edge `xRy` to `G` lets us derive `y:A` (with `Γ` unchanged), conclude `x:□A`. This encodes
  Simpson's side condition "`y` different from `x` and not occurring in any open assumptions
  other than the distinguished occurrences of `xRy`" (`:4661`) via cofinite quantification;
  see the module docstring. -/
  | boxI (L : Set (Label Atom)) (hL : L.Finite) (G : Graph Atom)
      (Γ : List (LabelledFormula Atom)) (x : Label Atom) (A : Proposition Atom)
      (h : ∀ y ∉ L, NIK 𝒯 (G.addEdge x y) Γ (y ∶ A)) : NIK 𝒯 G Γ (x ∶ .box A)
  /-- `(◇I)`: from a (possibly 𝒯-derived) edge `xRy` and `y:A`, conclude `x:◇A`. -/
  | diaI (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x y : Label Atom)
      (A : Proposition Atom) (hR : TClosure 𝒯 G.R x y) (h : NIK 𝒯 G Γ (y ∶ A)) :
      NIK 𝒯 G Γ (x ∶ .diamond A)
  /-- `(◇E)`: from `x:◇A`, and, for cofinitely many `y` (all `y` outside `L`), a derivation of
  `z:B` from `Γ` extended by `y:A` and `G` extended by the edge `xRy`, conclude `z:B`. Encodes
  Simpson's side condition "`y` different from both `x` and `z` and not occurring in any open
  assumptions upon which `z:B` depends other than the distinguished occurrences of `y:A` and
  `xRy`" (`:4664`) via cofinite quantification. -/
  | diaE (L : Set (Label Atom)) (hL : L.Finite) (G : Graph Atom)
      (Γ : List (LabelledFormula Atom)) (x z : Label Atom) (A B : Proposition Atom)
      (hdia : NIK 𝒯 G Γ (x ∶ .diamond A))
      (h : ∀ y ∉ L, NIK 𝒯 (G.addEdge x y) ((y ∶ A) :: Γ) (z ∶ B)) : NIK 𝒯 G Γ (z ∶ B)

/-- `A` is a **theorem** of `N_IK(𝒯)` iff `⊢_𝒯 A` over the trivial graph, at the trivial graph's
distinguished node (Simpson `:5114`). -/
def NIKTheorem (𝒯 : Set GeomAxiom) (A : Proposition Atom) : Prop :=
  NIK 𝒯 (Graph.trivial Atom) [] ((Graph.trivial Atom).nonempty.choose ∶ A)

/-! ## Weakening / graph-morphism lemmas (Prop. 4.4.1) -/

/-- **Weakening / graph-morphism.** If `Γ ⊢_G x:A` and both the context and the graph are
extended (`Γ ⊆ Δ`, `G ≤ G'`), then `Δ ⊢_{G'} x:A`. Combines Simpson's Prop. 4.4.1's two
weakening directions (in the context, and in the graph) into a single induction; the eigenvariable
cases (`(□I)`/`(◇E)`) go through directly by re-applying the same cofinite premise, without any
separate renaming lemma, because of the cofinite-quantification encoding (see the module
docstring). -/
theorem NIK.weaken {𝒯 : Set GeomAxiom} {G G' : Graph Atom} {Γ Δ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (h : NIK 𝒯 G Γ φ) (hG : G ≤ G') (hΓ : ∀ ψ ∈ Γ, ψ ∈ Δ) :
    NIK 𝒯 G' Δ φ := by
  induction h generalizing G' Δ with
  | assumption G Γ φ hmem => exact .assumption G' Δ φ (hΓ _ hmem)
  | efq G Γ x A _ ih => exact .efq G' Δ x A (ih hG hΓ)
  | andI G Γ x A B _ _ ihA ihB => exact .andI G' Δ x A B (ihA hG hΓ) (ihB hG hΓ)
  | andE1 G Γ x A B _ ih => exact .andE1 G' Δ x A B (ih hG hΓ)
  | andE2 G Γ x A B _ ih => exact .andE2 G' Δ x A B (ih hG hΓ)
  | orI1 G Γ x A B _ ih => exact .orI1 G' Δ x A B (ih hG hΓ)
  | orI2 G Γ x A B _ ih => exact .orI2 G' Δ x A B (ih hG hΓ)
  | orE G Γ x A B C _ _ _ ihor ihA ihB =>
      refine .orE G' Δ x A B C (ihor hG hΓ) (ihA hG ?_) (ihB hG ?_)
      · intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hΓ _ hψ)
      · intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hΓ _ hψ)
  | impI G Γ x A B _ ih =>
      refine .impI G' Δ x A B (ih hG ?_)
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hΓ _ hψ)
  | impE G Γ x A B _ _ ihimp ihA => exact .impE G' Δ x A B (ihimp hG hΓ) (ihA hG hΓ)
  | boxE G Γ x y A hR _ ih => exact .boxE G' Δ x y A (TClosure.mono hG.2 hR) (ih hG hΓ)
  | boxI L hL G Γ x A _ ih =>
      refine .boxI L hL G' Δ x A ?_
      intro y hy
      exact ih y hy (Graph.addEdge_mono hG x y) hΓ
  | diaI G Γ x y A hR _ ih => exact .diaI G' Δ x y A (TClosure.mono hG.2 hR) (ih hG hΓ)
  | diaE L hL G Γ x z A B _ _ ihdia ih =>
      refine .diaE L hL G' Δ x z A B (ihdia hG hΓ) ?_
      intro y hy
      refine ih y hy (Graph.addEdge_mono hG x y) ?_
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hΓ _ hψ)

/-! ## Smoke test -/

/-- **Smoke test**: `x:□A, xRy ⊢_G y:A` via `(□E)` alone, for any `𝒯`.
Confirms `(□E)` needs only a graph edge (here, already literal, not even requiring 𝒯-closure)
and the boxed formula. -/
theorem NIK.smoke_boxE {𝒯 : Set GeomAxiom} {G : Graph Atom} {Γ : List (LabelledFormula Atom)}
    {x y : Label Atom} {A : Proposition Atom} (hxy : G.R x y) (hmem : (x ∶ .box A) ∈ Γ) :
    NIK 𝒯 G Γ (y ∶ A) :=
  NIK.boxE G Γ x y A (.base hxy) (NIK.assumption G Γ (x ∶ .box A) hmem)

end Cslib.Logic.Modal.Labelled
