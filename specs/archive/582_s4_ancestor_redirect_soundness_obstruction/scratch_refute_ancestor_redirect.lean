import Cslib.Logics.Modal.Tableau.FrameSoundness

/-!
Scratch refutation probe.

Claim: the STATEMENT of `branchSatisfiableIn_s4FC_ancestor_redirect` is FALSE, not merely
unprovable from the given hypotheses.

Countermodel data (labels are `Nat`):
  x = 0, src = 1, a = 2
  acc  = { 0 -> 1, 2 -> 1 }        (so `acc.hasEdge a src = acc.hasEdge 2 1 = true`)
  b    = [ T(box p)@0 , F(p)@2 ]
  hboxback / hdianeg hold VACUOUSLY (no box-positive or diamond-negative formula at label 1).

`b` IS satisfiable at `acc` (witness below), but `b` is NOT satisfiable at
`acc.addEdge src a = acc.addEdge 1 2`, because the edge conjunct forces
  m.r (f 0) (f 1)  and  m.r (f 1) (f 2),
transitivity forces m.r (f 0) (f 2), T(box p)@0 then forces p at f 2, contradicting F(p)@2.
-/

set_option autoImplicit false

open Cslib.Logic.Modal Cslib.Logic.Modal.Tableau Cslib.Logic.Tableau

namespace RefuteAncestorRedirect

abbrev A := Nat
abbrev p : Proposition A := .atom 0

/-- `acc` : edges 0 -> 1 and 2 -> 1. -/
def acc : Accessibility := ⟨[(0, 1), (2, 1)]⟩

/-- The branch: `T(□p)@0`, `F(p)@2`. -/
def b : List (SignedFormula (Proposition A) WorldIndex) :=
  [⟨.pos, .box p, 0⟩, ⟨.neg, p, 2⟩]

/-- Witness frame on `Nat`: `j` is accessible from `i` iff `j = i` or `j = 1`.
Reflexive and transitive; has `0 -> 1` and `2 -> 1` but NOT `1 -> 2`. -/
def R : Nat → Nat → Prop := fun i j => j = i ∨ j = 1

/-- Witness model: `p` true exactly at worlds `0` and `1`. -/
def M : Model Nat A := { r := R, v := fun w _ => w = 0 ∨ w = 1 }

theorem hFC : s4FC M.r := by
  refine ⟨⟨fun _ => Or.inl rfl⟩, ⟨?_⟩⟩
  rintro i j k hij (rfl | rfl)
  · exact hij
  · exact Or.inr rfl

/-- **`hanc` holds**: `acc.hasEdge a src` with `a = 2`, `src = 1`. -/
theorem hanc : acc.hasEdge 2 1 = true := by decide

/-- **`hboxback` holds vacuously**: no `T(□ψ)@1` on the branch. -/
theorem hboxback : ∀ ψ : Proposition A,
    (⟨.pos, .box ψ, 1⟩ : SignedFormula (Proposition A) WorldIndex) ∈ b →
    (⟨.pos, ψ, 2⟩ : SignedFormula (Proposition A) WorldIndex) ∈ b := by
  intro ψ hmem
  simp [b, SignedFormula.mk.injEq] at hmem

/-- **`hdianeg` holds vacuously**: no `F(◇ψ)@1` on the branch. -/
theorem hdianeg : ∀ ψ : Proposition A,
    (⟨.neg, .diamond ψ, 1⟩ : SignedFormula (Proposition A) WorldIndex) ∈ b →
    (⟨.neg, ψ, 2⟩ : SignedFormula (Proposition A) WorldIndex) ∈ b := by
  intro ψ hmem
  simp [b, SignedFormula.mk.injEq] at hmem

/-- **The hypothesis `h` holds**: `b` is S4-satisfiable at `acc`. -/
theorem sat_before : branchSatisfiableIn s4FC b acc := by
  refine ⟨Nat, M, id, hFC, ?_, ?_⟩
  · -- Every recorded edge has target `1`, and `R i 1` holds for every `i`.
    intro w w' hedge
    refine Or.inr ?_
    simp only [id_eq]
    simp only [acc, Accessibility.hasEdge, List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at hedge
    rcases hedge with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h.symm
  · intro sf hsf
    simp only [b, List.mem_cons, List.not_mem_nil, or_false] at hsf
    rcases hsf with rfl | rfl
    · refine ⟨fun _ => ?_, fun hs => by simp at hs⟩
      -- `Satisfies M 0 (□p)`: successors of `0` are exactly `{0, 1}`, where `p` holds.
      intro w' hw'
      exact hw'
    · refine ⟨fun hs => by simp at hs, fun _ hs => ?_⟩
      simp [Satisfies, M] at hs

/-- **The conclusion FAILS**: `b` is NOT S4-satisfiable at `acc.addEdge src a`. -/
theorem not_sat_after : ¬ branchSatisfiableIn s4FC b (acc.addEdge 1 2) := by
  rintro ⟨W, m, f, ⟨_, htrans⟩, hedges, hb⟩
  have e01 : m.r (f 0) (f 1) := hedges 0 1 (by decide)
  have e12 : m.r (f 1) (f 2) := hedges 1 2 (by decide)
  have e02 : m.r (f 0) (f 2) := htrans.trans _ _ _ e01 e12
  have hbox := (hb ⟨.pos, .box p, 0⟩ (by simp [b])).1 rfl
  have hneg := (hb ⟨.neg, p, 2⟩ (by simp [b])).2 rfl
  simp only [Satisfies] at hbox
  exact hneg (hbox (f 2) e02)

/-- **Therefore the lemma's statement is refutable.** -/
theorem statement_is_false :
    ¬ (∀ (b : List (SignedFormula (Proposition A) WorldIndex)) (acc : Accessibility),
        branchSatisfiableIn s4FC b acc → ∀ (src a : WorldIndex),
        acc.hasEdge a src = true →
        (∀ ψ, (⟨.pos, .box ψ, src⟩ : SignedFormula (Proposition A) WorldIndex) ∈ b →
          (⟨.pos, ψ, a⟩ : SignedFormula (Proposition A) WorldIndex) ∈ b) →
        (∀ ψ, (⟨.neg, .diamond ψ, src⟩ : SignedFormula (Proposition A) WorldIndex) ∈ b →
          (⟨.neg, ψ, a⟩ : SignedFormula (Proposition A) WorldIndex) ∈ b) →
        branchSatisfiableIn s4FC b (acc.addEdge src a)) := by
  intro H
  exact not_sat_after (H b acc sat_before 1 2 hanc hboxback hdianeg)

end RefuteAncestorRedirect

#print axioms RefuteAncestorRedirect.statement_is_false
#print axioms RefuteAncestorRedirect.sat_before
#print axioms RefuteAncestorRedirect.not_sat_after
