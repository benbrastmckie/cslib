import Cslib.Logics.Modal.Metalogic.Constructive.CS5Completeness

namespace Cslib.Logic.Modal
open Cslib.Logic

universe u
variable {Atom : Type u}

/-- The sum-elimination retraction collapsing the two tagged copies. -/
def cs5PairRetract : Sum Atom Atom → Atom := Sum.elim id id

@[simp] theorem cs5PairRetract_tauL (φ : Proposition Atom) :
    Proposition.map cs5PairRetract (cs5PairTauL φ) = φ := by
  rw [cs5PairTauL, Proposition.map_map]
  have h : (cs5PairRetract ∘ Sum.inl : Atom → Atom) = id := rfl
  rw [h, Proposition.map_id]

@[simp] theorem cs5PairRetract_tauR (φ : Proposition Atom) :
    Proposition.map cs5PairRetract (cs5PairTauR φ) = φ := by
  rw [cs5PairTauR, Proposition.map_map]
  have h : (cs5PairRetract ∘ Sum.inr : Atom → Atom) = id := rfl
  rw [h, Proposition.map_id]

/-- **Contradicts the recorded Non-Goal.** The retraction IS schema-compatible: every
`CS5PairAxiom` instance maps to a genuine `CS5ModalAxiom` instance. Both cross axioms land on
`CS5ModalAxiom.tBox` (`□B → B`), which *is* a CS5 schema instance since `CS5` contains `T`. -/
theorem cs5PairRetract_schema_compatible (ψ : Proposition (Atom ⊕ Atom)) (h : CS5PairAxiom ψ) :
    CS5ModalAxiom (Proposition.map cs5PairRetract ψ) := by
  cases h with
  | left ψ h => rwa [cs5PairRetract_tauL]
  | right ψ h => rwa [cs5PairRetract_tauR]
  | cross1 B => simpa [cs5PairRetract_tauL, cs5PairRetract_tauR] using CS5ModalAxiom.tBox B
  | cross2 B => simpa [cs5PairRetract_tauL, cs5PairRetract_tauR] using CS5ModalAxiom.tBox B
  | implyK φ ψ => exact CS5ModalAxiom.implyK (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | implyS φ ψ χ => exact CS5ModalAxiom.implyS (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ) (Proposition.map cs5PairRetract χ)
  | efq φ => exact CS5ModalAxiom.efq (Proposition.map cs5PairRetract φ)
  | andI φ ψ => exact CS5ModalAxiom.andI (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | andE1 φ ψ => exact CS5ModalAxiom.andE1 (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | andE2 φ ψ => exact CS5ModalAxiom.andE2 (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | orI1 φ ψ => exact CS5ModalAxiom.orI1 (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | orI2 φ ψ => exact CS5ModalAxiom.orI2 (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ)
  | orE φ ψ χ => exact CS5ModalAxiom.orE (Proposition.map cs5PairRetract φ) (Proposition.map cs5PairRetract ψ) (Proposition.map cs5PairRetract χ)

/-- The retraction sends the two-sided seed into `H ∪ cl(boxInv H)`. -/
theorem cs5PairRetract_seed {H : Set (Proposition Atom)} {x : Proposition (Atom ⊕ Atom)}
    (hx : x ∈ cs5PairSeed H) :
    Proposition.map cs5PairRetract x ∈ H ∪ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H) := by
  rcases cs5PairSeed_mem_iff.mp hx with ⟨φ, hφ, rfl⟩ | ⟨ψ, hψ, rfl⟩
  · exact Or.inl (by rwa [cs5PairRetract_tauL])
  · exact Or.inr (by rwa [cs5PairRetract_tauR])

/-- **The collapse bound (best obtainable from any atom relabeling).** If `τ_R A` is in the
combined closure of the seed then `A` is in the plain `CS5` closure of `H ∪ cl(boxInv H)`.
Since `□A ∉ H` does **not** give `A ∉ H`, this bound is too weak to discharge `hR` -- the route
fails for this reason, not for schema-incompatibility. -/
theorem cs5PairRetract_bound {H : Set (Proposition Atom)} {A : Proposition Atom}
    (h : cs5PairTauR A ∈ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)) :
    A ∈ modalDeductiveClosure (@CS5ModalAxiom Atom)
      (H ∪ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H)) := by
  obtain ⟨L, hL, hd⟩ := h
  refine ⟨L.map (Proposition.map cs5PairRetract), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact cs5PairRetract_seed (hL y hy)
  · have := Deriv.map cs5PairRetract cs5PairRetract_schema_compatible hd
    rwa [cs5PairRetract_tauR] at this

end Cslib.Logic.Modal
