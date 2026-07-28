import Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5

namespace Cslib.Logic.Modal.RaProbe

open Cslib.Logic Cslib.Logic.Modal

universe u v

variable {Atom : Type u}

/-! # Round-3 Probe: (R-a) — total-model refutation capacity of `is5FC`

**VERDICT: kill-criterion FIRED — (R-a) is REFUTED.** Total-`r` `is5FC` models validate
`□a ∨ ¬□a` at every world (`total_validates_boxEm`), yet `□a ∨ ¬□a` is not `IS5`-derivable
(`boxEm_not_derivable`), so no total-`r` model can refute this `IS5` non-theorem anywhere, and
the product-model route's requirement — a total-`r` countermodel for every `(H, A)` with
`A ∉ cl_IS5(H)` — fails at the instance `H := ∅`, `A := □a ∨ ¬□a` (`ra_route_refuted`).

The mechanism: under CSLib's `BForces` box clause
`w ⊩ □φ ↔ ∀ w' ≥ w, ∀ u, r w' u → u ⊩ φ` (`Birelational.lean:118`), a total `r` makes the
quantification world-independent — box degenerates to a global modality. A meta-level classical
case split on `∀ u, val u a` then forces `□a ∨ ¬□a` everywhere. Underivability comes from the
two-world chain `w₀ ≤ w₁` with `r := Eq` (an `is5FC` model), `a` true at `w₁` only, which
refutes both disjuncts at `w₀`, converted by `is5_soundness_derivable`. -/

/-- The separating formula `□a ∨ ¬□a` (with `¬φ := φ → ⊥`). -/
abbrev boxEm (a : Atom) : Proposition Atom :=
  (Proposition.box (Proposition.atom a)).or
    ((Proposition.box (Proposition.atom a)).imp Proposition.bot)

/-! ## P1: total-model validity of `□a ∨ ¬□a` -/

/-- **P1 (total-validity).** In any birelational model whose modal relation `r` is total,
`□a ∨ ¬□a` is forced at every world. Neither the frame conditions `f1`/`f2` nor
`≤`-monotonicity of `val` is needed: totality alone degenerates the box clause to the
world-independent `∀ u, val u a`, and the meta-level classical case split on that proposition
decides the disjunction. -/
theorem total_validates_boxEm {World : Type v} [Preorder World]
    (r : World → World → Prop) (total : ∀ x y, r x y)
    (val : World → Atom → Prop) (a : Atom) (w : World) :
    BForces r val (fun _ => False) w (boxEm a) := by
  by_cases h : ∀ u : World, val u a
  · -- Left disjunct: `□a` holds since every `r`-successor of every `≤`-successor forces `a`.
    exact Or.inl fun w' _ u _ => h u
  · -- Right disjunct: some `u₀` fails `a`, and totality makes `u₀` an `r`-successor of every
    -- world, so no `≤`-successor of `w` forces `□a` — `¬□a` holds vacuously.
    obtain ⟨u₀, hu₀⟩ := not_forall.mp h
    exact Or.inr fun w' _ hbox => hu₀ (hbox w' (le_refl w') u₀ (total w' u₀))

/-! ## P2: `□a ∨ ¬□a` is not `IS5`-derivable

Countermodel: the two-world chain `w₀ ≤ w₁` with `r := Eq` (identity is an equivalence, so
`is5FC` holds; `f1`/`f2` hold with witnesses `w'`/`u'`), `a` true at `w₁` only (monotone).
At `w₀`: `□a` fails (instantiate the box at `w₀` itself, whose unique `Eq`-successor `w₀`
fails `a`), and `¬□a` fails (the `≤`-successor `w₁` forces `□a`, since every `≤`-successor of
`w₁` is `w₁` and its unique `Eq`-successor `w₁` forces `a`). -/

/-- The two-world chain for the P2 countermodel. -/
inductive PW where
  /-- Bottom world: `a` false here. -/
  | w0
  /-- Top world: `a` true here. -/
  | w1

/-- Chain order: `x ≤ y` iff `x = y` or `y` is the top world. -/
instance : Preorder PW where
  le x y := x = y ∨ y = PW.w1
  le_refl x := Or.inl rfl
  le_trans x y z hxy hyz := by
    cases hxy with
    | inl h => exact h ▸ hyz
    | inr h => cases hyz with
      | inl h2 => exact Or.inr (h2 ▸ h)
      | inr h2 => exact Or.inr h2

/-- Every `≤`-successor of the top world is the top world. -/
theorem pw_top {x : PW} (h : PW.w1 ≤ x) : x = PW.w1 := by
  cases h with
  | inl h => exact h.symm
  | inr h => exact h

/-- The valuation "true exactly at `w₁`" is `≤`-monotone. -/
theorem pw_mono {x y : PW} (h : x ≤ y) (hx : x = PW.w1) : y = PW.w1 := by
  cases h with
  | inl h => exact h ▸ hx
  | inr h => exact h

/-- **P2 (underivability).** `□a ∨ ¬□a` is not derivable from `IS5ModalAxiom`, by
`is5_soundness_derivable` and the two-world chain countermodel. -/
theorem boxEm_not_derivable (a : Atom) : ¬ Derivable IS5ModalAxiom (boxEm a) := by
  intro h
  have hvalid := is5_soundness_derivable (Atom := Atom) h
  have hforce := hvalid PW (fun x y => x = y)
    ⟨fun _ => rfl, fun h1 h2 => h1.trans h2, fun h1 => h1.symm⟩
    (fun {_ w' _} hle hr => ⟨w', rfl, hr ▸ hle⟩)
    (fun {_ _ u'} hr hle => ⟨u', hr.symm ▸ hle, rfl⟩)
    (fun x (_ : Atom) => x = PW.w1)
    (fun _ hle hx => pw_mono hle hx)
    PW.w0
  cases hforce with
  | inl hbox =>
    -- `w₀ ⊩ □a` instantiated at `w' := w₀`, `u := w₀` gives `val w₀ a`, i.e. `w₀ = w₁`.
    exact PW.noConfusion (hbox PW.w0 (le_refl _) PW.w0 rfl)
  | inr himp =>
    -- `w₀ ⊩ ¬□a` applied to the `≤`-successor `w₁`, which forces `□a`.
    exact himp PW.w1 (Or.inr rfl)
      (fun w'' hle u hru => hru ▸ pw_top hle)

/-! ## P3: refutation of the route-required form of (R-a) -/

/-- The model data the product-model route requires for a pair `(H, A)`: a total-`r`
birelational model (with monotone valuation, hence an `is5FC` model — totality trivially gives
reflexivity, transitivity, symmetry, and both frame conditions) containing worlds `u ⊩ H` and
`v ⊮ A` with `r u v`. Bundled as a structure to keep the existential telescope readable. -/
structure TotalCountermodel (Atom : Type u) (H : Set (Proposition Atom))
    (A : Proposition Atom) where
  /-- The world carrier. -/
  World : Type v
  /-- The intuitionistic preorder. -/
  [instPreorder : Preorder World]
  /-- The modal accessibility relation. -/
  r : World → World → Prop
  /-- The route's totality requirement on `r`. -/
  total : ∀ x y, r x y
  /-- The valuation. -/
  val : World → Atom → Prop
  /-- `≤`-monotonicity of the valuation. -/
  val_mono : ∀ {x y : World} (p : Atom), x ≤ y → val x p → val y p
  /-- The world forcing the seed. -/
  u : World
  /-- The world refuting the target. -/
  v : World
  /-- `u` forces every member of `H`. -/
  seed_forced : ∀ φ ∈ H, BForces r val (fun _ => False) u φ
  /-- `v` refutes `A`. -/
  target_refuted : ¬ BForces r val (fun _ => False) v A
  /-- The route's cross-relation requirement. -/
  rel : r u v

/-- **(R-a), route-required form**: for every `(H, A)` with `A ∉ cl_IS5(H)`, a total-`r`
countermodel exists. This is the statement the product-model route needs as its model supply. -/
def RaRouteRequirement (Atom : Type u) : Prop :=
  ∀ (H : Set (Proposition Atom)) (A : Proposition Atom),
    A ∉ modalDeductiveClosure IS5ModalAxiom H →
    Nonempty (TotalCountermodel.{u, v} Atom H A)

/-- Bridge: non-derivability places `□a ∨ ¬□a` outside `cl_IS5(∅)` (the closure's witness list
over `∅` is forced empty, and `Deriv [] = Derivable`). -/
theorem boxEm_not_in_empty_closure (a : Atom) :
    boxEm a ∉ modalDeductiveClosure IS5ModalAxiom (∅ : Set (Proposition Atom)) := by
  rintro ⟨L, hL, hd⟩
  have hLnil : L = [] := by
    cases L with
    | nil => rfl
    | cons x xs => exact absurd (hL x (List.mem_cons_self ..)) (fun hx => hx)
  subst hLnil
  exact boxEm_not_derivable a hd

/-- **P3 (route refutation).** The route-required form of (R-a) is false for every atom type
with a distinguished element: at the instance `H := ∅`, `A := □a ∨ ¬□a`, the side condition
holds (P2 + bridge), yet by P1 no total-`r` model refutes `A` at any world. -/
theorem ra_route_refuted (a : Atom) : ¬ RaRouteRequirement.{u, v} Atom := by
  intro hroute
  obtain ⟨M⟩ := hroute ∅ (boxEm a) (boxEm_not_in_empty_closure a)
  letI := M.instPreorder
  exact M.target_refuted (total_validates_boxEm M.r M.total M.val a M.v)

/-! ## Axiom audit

Expected: standard axioms only (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`,
no custom axioms. The classical usage is meta-level only (the case split in P1, the
countermodel bookkeeping in P2), consistent with the repository's other refutation probes. -/

#print axioms total_validates_boxEm
#print axioms boxEm_not_derivable
#print axioms ra_route_refuted

end Cslib.Logic.Modal.RaProbe
