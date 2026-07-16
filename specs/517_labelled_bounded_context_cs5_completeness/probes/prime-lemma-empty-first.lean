import Cslib.Init
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context

/-! # Task 517 Phase 21 — scratch: is `TPrime 𝒯 Atom` empty for EVERY `𝒯`? -/

namespace Cslib.Logic.Modal.Labelled

universe u
variable {Atom : Type u} {𝒯 : Set GeomAxiom}

/-- `x : A ⊃ A` is derivable at **every** label, over **every** graph, from **every** context:
`impI` + `assumption`, no side conditions, no premises. -/
theorem NIK.imp_self (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
    (A : Proposition Atom) : NIK 𝒯 G Γ (x ∶ .imp A A) :=
  .impI G Γ x A A (.assumption _ _ _ (by simp))

theorem Deriv.imp_self {G : Graph Atom} {Γ : Set (LabelledFormula Atom)} (x : Label Atom)
    (A : Proposition Atom) : Deriv 𝒯 G Γ (x ∶ .imp A A) :=
  ⟨[], by simp, NIK.imp_self G [] x A⟩

/-- **`TPrime 𝒯 Atom` is uninhabited for EVERY `𝒯` — including `𝒯 = ∅`.** -/
theorem tPrime_false (P : TPrime 𝒯 Atom) : False := by
  obtain ⟨V', hV', hX⟩ := P.coinfinite
  obtain ⟨n, hn⟩ := hV'.nonempty
  have hmem := P.deductiveClosure (Label.var n) (.imp .bot .bot) (Deriv.imp_self _ _)
  exact hn (hX _ (P.ctxSubset _ hmem))

end Cslib.Logic.Modal.Labelled

#print axioms Cslib.Logic.Modal.Labelled.tPrime_false
