import Cslib.Init
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Rules
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat

/-!
Scratch probe (task territory only, Phase 10 first construction step de-risking): the
`ForestComparable` export chain. `parAncestor`/`isAccessible` copied/re-derived locally since
the originals are `private` in `Scheme.lean`.
-/

open Cslib.Logic.PL

/-- Local copy of `Scheme.lean`'s private `parAncestor`. -/
def parAncestor (par : Nat → Nat) (x y : Nat) : Prop :=
  Relation.ReflTransGen (fun a b => a = par b) x y

/-- STEP 1 (verified separately in `ForestComparableProbe.lean` for the counting/pigeonhole
argument establishing `hshape` from `IWorldHist`'s (H1) membership clause plus
`IWorldHistCounter`'s length fact): given every member of `edges` has the shape `(c, par c)`,
`isAccessible` reachability implies `parAncestor`. This is the direction (H1-acc) does NOT
supply on its own (handoff 07/08's identified gap) -- it closes it, using only `hshape`. -/
theorem isAccessible_to_parAncestor {par : Nat → Nat} {edges : List (Nat × Nat)}
    (hshape : ∀ p ∈ edges, ∃ c, p = (c, par c))
    (w w' : Nat) (h : isAccessible edges w w' = true) :
    parAncestor par w w' := by
  simp only [isAccessible] at h
  by_cases heq : w == w'
  · have : w = w' := by simpa using heq
    subst this
    exact Relation.ReflTransGen.refl
  · simp only [heq, Bool.false_eq_true, ite_false] at h
    suffices key : ∀ (current fuel : Nat), isAccessible.go edges w' current fuel = true →
        current = w' ∨ parAncestor par current w' by
      rcases key w edges.length h with heq2 | hpar
      · subst heq2; exact Relation.ReflTransGen.refl
      · exact hpar
    intro current fuel
    induction fuel generalizing current with
    | zero => simp [isAccessible.go]
    | succ k ih =>
      simp only [isAccessible.go]
      intro hstep
      rw [List.any_eq_true] at hstep
      obtain ⟨child, hchild, hcond⟩ := hstep
      simp only [List.mem_filterMap] at hchild
      obtain ⟨⟨c, p⟩, hedges, hfilt⟩ := hchild
      by_cases hpc : p == current
      · have hpeq : p = current := by simpa using hpc
        subst hpeq
        simp only [hpc, ite_true, Option.some.injEq] at hfilt
        subst hfilt
        obtain ⟨c', hc'⟩ := hshape (c, p) hedges
        rw [Prod.mk.injEq] at hc'
        obtain ⟨hcc, hpar_eq⟩ := hc'
        subst hcc
        by_cases hce : c == w'
        · have hcw' : c = w' := by simpa using hce
          right
          rw [hcw'] at hpar_eq
          exact Relation.ReflTransGen.single hpar_eq
        · simp only [hce, Bool.false_eq_true, ite_false] at hcond
          rcases ih c hcond with heq3 | hpar3
          · right; rw [heq3] at hpar_eq; exact Relation.ReflTransGen.single hpar_eq
          · right; exact Relation.ReflTransGen.head hpar_eq hpar3
      · simp only [Bool.not_eq_true] at hpc
        simp [hpc] at hfilt

/-- Auxiliary: `parAncestor` unwinds to explicit `par`-iteration. Both directions are a clean
induction on the `ReflTransGen`/`Nat` structure respectively; this is the standard bridge that
makes `parAncestor`-linearity a one-line consequence of `Nat`-comparability below. -/
theorem parAncestor_iff_iterate {par : Nat → Nat} {x y : Nat} :
    parAncestor par x y ↔ ∃ n, x = par^[n] y := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | @head a b hab _hchain ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + 1, by rw [Function.iterate_succ_apply', ← hm, hab]⟩
  · rintro ⟨n, hn⟩
    subst hn
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Relation.ReflTransGen.head rfl ih

/-- STEP 2: pure `parAncestor`-linearity -- any two `parAncestor`-ancestors of a common world
`c` are themselves comparable. Depends only on `par` being a genuine (single-valued) function,
not on `edges`/`isAccessible` at all. -/
theorem parAncestor_comparable {par : Nat → Nat} {x y c : Nat}
    (hx : parAncestor par x c) (hy : parAncestor par y c) :
    parAncestor par x y ∨ parAncestor par y x := by
  obtain ⟨n, hn⟩ := parAncestor_iff_iterate.mp hx
  obtain ⟨m, hm⟩ := parAncestor_iff_iterate.mp hy
  rcases le_total n m with hle | hle
  · right
    apply parAncestor_iff_iterate.mpr
    refine ⟨m - n, ?_⟩
    rw [hm, hn, ← Function.iterate_add_apply]
    congr 1
    omega
  · left
    apply parAncestor_iff_iterate.mpr
    refine ⟨n - m, ?_⟩
    rw [hn, hm, ← Function.iterate_add_apply]
    congr 1
    omega

/-- STEP 3 (the full `ForestComparable` export, combining Steps 1-2): under the `edges`-shape
hypothesis (Step 1's precondition) plus (H1-acc)-style forward accessibility (the ALREADY-landed
`IWorldHist` clause: `parAncestor par c' c → isAccessible edges c' c`), any two worlds
`isAccessible`-reachable to a common world `l` are themselves `isAccessible`-comparable. This is
exactly the `ForestComparable` shape from `scratch/PersistPrototype.lean`, fully derived (no
`sorry`) from the already-landed `IWorldHist`/`IWorldHistCounter` machinery. -/
theorem forestComparable_of_shape {par : Nat → Nat} {edges : List (Nat × Nat)}
    (hshape : ∀ p ∈ edges, ∃ c, p = (c, par c))
    (hacc : ∀ c' c, parAncestor par c' c → isAccessible edges c' c = true)
    (w x l : Nat) (hwl : isAccessible edges w l = true) (hxl : isAccessible edges x l = true) :
    isAccessible edges w x = true ∨ isAccessible edges x w = true := by
  have hwl' : parAncestor par w l := isAccessible_to_parAncestor hshape w l hwl
  have hxl' : parAncestor par x l := isAccessible_to_parAncestor hshape x l hxl
  rcases parAncestor_comparable hwl' hxl' with hwx | hxw
  · left; exact hacc w x hwx
  · right; exact hacc x w hxw
