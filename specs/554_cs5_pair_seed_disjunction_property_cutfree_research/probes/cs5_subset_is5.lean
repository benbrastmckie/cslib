import Cslib.Logics.Modal.Metalogic.Constructive.CS5Completeness
import Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5

namespace Cslib.Logic.Modal
open Cslib.Logic

universe u
variable {Atom : Type u}

/-! # Round-2 Probe: `CS5 ⊆ IS5` is a one-line schema inclusion

The IS5-detour route (report §5) needs only the *easy* direction of the CS5/IS5 relationship:
every `CS5ModalAxiom` constructor is literally an `IS5ModalAxiom` constructor.  `IS5ModalAxiom`
additionally has `kdisj` (k3), `kfs` (k4), `kbot` (k5); `CS5ModalAxiom` has no constructor absent
from `IS5ModalAxiom`.  So no collapse theorem is needed for this direction. -/

/-- **Schema inclusion.** Every `CS5` axiom instance is an `IS5` axiom instance. -/
theorem cs5Axiom_to_is5Axiom {φ : Proposition Atom} (h : CS5ModalAxiom φ) : IS5ModalAxiom φ := by
  cases h with
  | implyK φ ψ => exact .implyK φ ψ
  | implyS φ ψ χ => exact .implyS φ ψ χ
  | efq φ => exact .efq φ
  | andI φ ψ => exact .andI φ ψ
  | andE1 φ ψ => exact .andE1 φ ψ
  | andE2 φ ψ => exact .andE2 φ ψ
  | orI1 φ ψ => exact .orI1 φ ψ
  | orI2 φ ψ => exact .orI2 φ ψ
  | orE φ ψ χ => exact .orE φ ψ χ
  | k φ ψ => exact .k φ ψ
  | kdia φ ψ => exact .kdia φ ψ
  | tBox φ => exact .tBox φ
  | tDia φ => exact .tDia φ
  | fourBox φ => exact .fourBox φ
  | fourDia φ => exact .fourDia φ
  | bBox φ => exact .bBox φ
  | bDia φ => exact .bDia φ

/-- **Derivability transport.** `CS5`-derivability implies `IS5`-derivability, context and all. -/
theorem cs5_deriv_to_is5 {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : Deriv (@CS5ModalAxiom Atom) Γ φ) : Deriv (@IS5ModalAxiom Atom) Γ φ := by
  obtain ⟨t⟩ := d
  have h := t.map id (fun ψ hψ => by simpa using cs5Axiom_to_is5Axiom hψ)
  rw [List.map_congr_left (fun ψ _ => Proposition.map_id ψ), List.map_id_fun',
    Proposition.map_id] at h
  exact ⟨h⟩

/-- Corollary at the level of deductive closures: `cl_{CS5} S ⊆ cl_{IS5} S`. -/
theorem cs5_closure_subset_is5_closure (S : Set (Proposition Atom)) :
    modalDeductiveClosure (@CS5ModalAxiom Atom) S ⊆ modalDeductiveClosure (@IS5ModalAxiom Atom) S :=
  fun _ ⟨L, hL, hd⟩ => ⟨L, hL, cs5_deriv_to_is5 hd⟩

end Cslib.Logic.Modal
