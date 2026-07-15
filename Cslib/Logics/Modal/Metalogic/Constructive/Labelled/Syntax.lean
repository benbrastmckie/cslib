/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Basic
public import Mathlib.Data.Set.Finite.Basic

/-! # Labelled Syntax (Simpson's Labelled Natural Deduction)

This module lands the syntactic layer of A. K. Simpson's labelled natural-deduction
presentation of intuitionistic modal logic [Simpson1994], Chapter 4-5: prefix variables,
the witness algebra, graphs of prefixes, and labelled formulae. This is the minimal
prerequisite for the `N_IK(𝒯)` deduction system (`Deduction.lean`) and, downstream,
for the adequacy gate (`Adequacy.lean`) which quantifies over the resulting
consequence relation.

**Scope note**: this file and `Deduction.lean` land the syntax and the deduction system only.
Adequacy, contexts (`Context.lean`), the Prime Lemma, the canonical model, the birelation
construction, the frame-class match, and the final assembly of `cs5_completeness` are developed
separately and are **not** attempted here.

## Contents

- `PrefixVar`: the raw prefix variables `V`, taken to be `ℕ` (countably infinite).
- `Coinfinite`: a subset `V' ⊆ V` is coinfinite iff its complement is infinite. The fresh-label
  supply lemma (`exists_fresh_notMem_of_coinfinite`) extracts a label outside any subset
  contained in a coinfinite `V'` -- this is load-bearing for the `□`-backward case of the
  Canonical Model Lemma 5.3.2 (not attempted here; the supply lemma is landed in this file
  because it is a purely syntactic fact about the label supply).
- `Label Atom`: the witness algebra `W(V)`, the free algebra over `PrefixVar` with one unary
  witness operator `dwitness x A` (Simpson's `v_{x:◇A}`) per modal formula. See the
  "Definitional choice" note below for why the `k`-ary geometric-sequent witness operators are
  elided.
- `Graph Atom`: a non-empty set of nodes `X` with an edge relation `R` confined to `X`, plus the
  operations `union`, `addNodes`, `addEdge`, and the **trivial graph** (a single node, no edges).
  `Graph.le` is the "sub-graph" order used by the weakening lemmas (`Deduction.lean`) and the
  canonical model's `≤` (not attempted here).
- `LabelledFormula Atom`: Simpson's `x : A` judgement, as a structure with fields `lbl` and
  `prop`.

## Definitional choice: only the diamond-witness operator

Simpson's witness algebra `W(V')` (`:5883-5905`) has, in general, one unary operator
`v_{x:◇A}` per modal formula **and** a `k`-ary operator per geometric sequent (used to supply
Skolem witnesses for geometric axioms with an existential conclusion, e.g. `χ_D`, seriality).
This module implements only the diamond-witness operator `dwitness`.

This is not a gap but a consequence of a deliberate choice made in `Deduction.lean`: `GeomAxiom`
represents **only universal Horn** geometric axioms (`χ_T`, `χ_B`, `χ_4`, `χ_5`), each of which
has no existential in its conclusion and therefore needs no Skolem/geometric-sequent witness
operator at all. Seriality `χ_D` -- the sole axiom that would need one -- is correspondingly not
representable in `GeomAxiom`, so there is no axiom in the system whose witnesses this algebra
fails to supply. See `GeomAxiom`'s docstring for why that exclusion is enforced at the type rather
than papered over downstream. Adding `χ_D` later means extending `GeomAxiom`, `TClosure`, and this
`Label` type's witness operators **together**, in one change.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 4 (labelled syntax, `N_IK`) and Chapter 5 (contexts, `:5047-5135`).
-/

@[expose] public section

namespace Cslib.Logic.Modal.Labelled

universe u

variable {Atom : Type u}

/-! ## Prefix variables -/

/-- Prefix variables `V`: countably infinite (Simpson `:5881`). Concretely taken to be `ℕ`. -/
abbrev PrefixVar : Type := ℕ

/-- A subset `V' ⊆ V` is **coinfinite** iff its complement is infinite. Simpson works with
coinfinite `V'` throughout so that a supply of fresh witnesses (elements of `V \ V'`) is always
available (`:5920`). -/
def Coinfinite (V' : Set PrefixVar) : Prop := V'ᶜ.Infinite

/-- **Fresh-label supply lemma.** If `V'` is coinfinite and `H ⊆ V'`, there is a label `z ∉ H`.
This is exactly Simpson's "take any `z ∈ V \ V'`" step (`:6152`), specialized so the witness
avoids any subset `H` contained in `V'` (in particular the labels already appearing in a context
whose underlying set lies in `W(V')`). Load-bearing for the `□`-backward case of the Canonical
Model Lemma 5.3.2 (not attempted here). -/
theorem exists_fresh_notMem_of_coinfinite {V' : Set PrefixVar} (hV' : Coinfinite V')
    (H : Set PrefixVar) (hH : H ⊆ V') : ∃ z, z ∉ H := by
  obtain ⟨z, hz⟩ := hV'.nonempty
  exact ⟨z, fun hzH => hz (hH hzH)⟩

/-! ## The witness algebra `W(V)` -/

/-- The witness algebra `W(V)`: the free algebra over prefix variables (`PrefixVar`), with one
unary operator `dwitness x A` (Simpson's `v_{x:◇A}`) per modal formula. See the module docstring
("Definitional choice") for why the geometric-sequent witness operators are elided. -/
inductive Label (Atom : Type u) : Type u where
  /-- A raw prefix variable. -/
  | var (n : PrefixVar) : Label Atom
  /-- The diamond witness `v_{x:◇A}` for the diamond formula `x:◇A` (Simpson `:5883`). -/
  | dwitness (x : Label Atom) (A : Proposition Atom) : Label Atom

/-! ## Graphs of prefixes -/

/-- A graph `(X, R)` of prefixes: a non-empty set of nodes `X` together with an edge relation
`R` whose edges are confined to `X` (Simpson `:5047-5065`). -/
structure Graph (Atom : Type u) : Type u where
  /-- The (non-empty) set of nodes. -/
  X : Set (Label Atom)
  /-- The edge relation. -/
  R : Label Atom → Label Atom → Prop
  /-- `X` is non-empty. -/
  nonempty : X.Nonempty
  /-- Edges are confined to `X`. -/
  edge_mem : ∀ x y, R x y → x ∈ X ∧ y ∈ X

namespace Graph

/-- The trivial graph `𝒯 = ({x}, ∅)`: a single node, no edges (Simpson `:5077`). -/
def trivial (Atom : Type u) : Graph Atom where
  X := {Label.var 0}
  R := fun _ _ => False
  nonempty := ⟨Label.var 0, rfl⟩
  edge_mem := fun _ _ h => h.elim

/-- The union `G ∪ G'` of two graphs: union of nodes, union of edges. -/
def union (G G' : Graph Atom) : Graph Atom where
  X := G.X ∪ G'.X
  R := fun x y => G.R x y ∨ G'.R x y
  nonempty := G.nonempty.mono Set.subset_union_left
  edge_mem := by
    rintro x y (h | h)
    · exact ⟨Or.inl (G.edge_mem x y h).1, Or.inl (G.edge_mem x y h).2⟩
    · exact ⟨Or.inr (G'.edge_mem x y h).1, Or.inr (G'.edge_mem x y h).2⟩

/-- The graph `G ∪ X'` obtained from `G` by adjoining a set of new (isolated) nodes `X'`. -/
def addNodes (G : Graph Atom) (X' : Set (Label Atom)) : Graph Atom where
  X := G.X ∪ X'
  R := G.R
  nonempty := G.nonempty.mono Set.subset_union_left
  edge_mem := fun x y h => ⟨Or.inl (G.edge_mem x y h).1, Or.inl (G.edge_mem x y h).2⟩

/-- The graph `G ∪ {xRy}` obtained from `G` by adjoining a single edge `x R y` (and its
endpoints, if new). -/
def addEdge (G : Graph Atom) (x y : Label Atom) : Graph Atom where
  X := G.X ∪ {x, y}
  R := fun a b => G.R a b ∨ (a = x ∧ b = y)
  nonempty := G.nonempty.mono Set.subset_union_left
  edge_mem := by
    rintro a b (hab | ⟨rfl, rfl⟩)
    · exact ⟨Or.inl (G.edge_mem a b hab).1, Or.inl (G.edge_mem a b hab).2⟩
    · exact ⟨Or.inr (by simp), Or.inr (by simp)⟩

/-- The sub-graph order: `G ≤ G'` iff `G'` extends `G`'s nodes and edges. This is the order used
by the weakening/graph-morphism lemmas (`Deduction.lean`) and, downstream, the canonical
model's `≤` (not attempted here). -/
def le (G G' : Graph Atom) : Prop := G.X ⊆ G'.X ∧ ∀ x y, G.R x y → G'.R x y

instance : LE (Graph Atom) := ⟨le⟩

@[refl] theorem le_refl (G : Graph Atom) : G ≤ G := ⟨Set.Subset.refl _, fun _ _ h => h⟩

theorem le_trans {G G' G'' : Graph Atom} (h1 : G ≤ G') (h2 : G' ≤ G'') : G ≤ G'' :=
  ⟨h1.1.trans h2.1, fun x y h => h2.2 x y (h1.2 x y h)⟩

instance : Preorder (Graph Atom) where
  le := le
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans

/-- Adding the same edge to both sides of a `≤`-related pair of graphs preserves `≤`. Used by
the weakening lemma for the `(□I)`/`(◇E)` cases, where the eigenvariable's graph is extended by
one edge on both the small and the large side. -/
theorem addEdge_mono {G G' : Graph Atom} (h : G ≤ G') (x y : Label Atom) :
    G.addEdge x y ≤ G'.addEdge x y := by
  constructor
  · intro a ha
    rcases ha with ha | ha
    · exact Or.inl (h.1 ha)
    · exact Or.inr ha
  · intro a b hab
    rcases hab with hab | hab
    · exact Or.inl (h.2 a b hab)
    · exact Or.inr hab

end Graph

/-! ## Labelled formulae -/

/-- A labelled formula `x : A`, for `x : Label Atom` a prefix and `A : Proposition Atom` a modal
formula (Simpson's `x:A` judgement). -/
structure LabelledFormula (Atom : Type u) : Type u where
  /-- The label (prefix). -/
  lbl : Label Atom
  /-- The formula. -/
  prop : Proposition Atom

/-- Notation `x ∶ A` for the labelled formula with label `x` and formula `A`
(Simpson's `x:A` judgement). -/
scoped notation:65 x " ∶ " A => LabelledFormula.mk x A

end Cslib.Logic.Modal.Labelled
