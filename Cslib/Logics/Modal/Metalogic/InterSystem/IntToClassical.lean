/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.ProofSystem.Instances.K
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IK
public import Cslib.Logics.Modal.Metalogic.InterSystem.Lifting
public import Cslib.Foundations.Logic.Theorems.Modal.Basic
public import Cslib.Foundations.Logic.Theorems.Combinators

/-! # The Intuitionistic → Classical Bridge (`IK → K`)

This module begins the one genuinely hard direction of task 484's lattice: intuitionistic
`IK` uses a **primitive** diamond with Fischer-Servi axiom schemata (`kdia`, `cd`, `idb`,
`dbot`), while classical `K` uses the **dual** diamond (`◇φ := ¬□¬φ`, witnessed by the
`diaDualityFwd`/`diaDualityBack` axiom schemata). This is not a syntactic rename — each
`IKModalAxiom` instance must be shown *derivable* (not literally an axiom instance) in
`KAxiom`, using the new generalized lift `Derivable_of_axiom_derivable`
(`InterSystem/Lifting.lean`).

## This Module (Phase 6 — Tractable Schemata)

Per-axiom classical `K`-derivations for the tractable `IKModalAxiom` schemata:

- The eight shared propositional constructors (`implyK`, `implyS`, `andI`, `andE1`, `andE2`,
  `orI1`, `orI2`, `orE`) and `efq`, `k` (`modalK`): **direct** — each is a literal `KAxiom`
  instance under the same name.
- `kdia` (`□(φ → ψ) → (◇φ → ◇ψ)`): derived via the generic raw-encoding K-diamond
  distribution theorem `k_dist_diamond` (`Theorems/Modal/Basic.lean`) composed with the
  `diaDualityFwd`/`diaDualityBack` axiom instances, using only the `flip`/`b_combinator`/
  `imp_trans` propositional combinators (`Theorems/Combinators.lean`).
- `dbot` (`◇⊥ → ⊥`): derived from `⊢ □¬⊥` (necessitation of the tautology `⊢ ¬⊥`, i.e.
  `identity ⊥ : ⊢ ⊥ → ⊥`), `app1` (`φ → ((φ → ψ) → ψ)`), and `diaDualityFwd`.

`cd` (`◇(φ ∨ ψ) → (◇φ ∨ ◇ψ)`) and `idb` (`(◇φ → □ψ) → □(φ → ψ)`) are deferred to Phase 7
(`the fiddliest two Fischer-Servi schemata`); the final assembly
`∀ φ, IKModalAxiom φ → Derivable KAxiom φ` and the concluding
`ikDerivable_implies_kDerivable` are also deferred to Phase 7, once all 14 schemata are
covered.
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-! ## Direct Schemata (Literal `KAxiom` Instances) -/

/-- `IK`'s `implyK` is a literal `KAxiom` instance. -/
theorem k_derivable_of_ik_implyK {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (φ.imp (ψ.imp φ)) :=
  ⟨.ax [] _ (KAxiom.implyK φ ψ)⟩

/-- `IK`'s `implyS` is a literal `KAxiom` instance. -/
theorem k_derivable_of_ik_implyS {φ ψ χ : Proposition Atom} :
    Derivable (@KAxiom Atom) ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  ⟨.ax [] _ (KAxiom.implyS φ ψ χ)⟩

/-- `IK`'s `efq` is a literal `KAxiom` instance. -/
theorem k_derivable_of_ik_efq {φ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Proposition.bot.imp φ) :=
  ⟨.ax [] _ (KAxiom.efq φ)⟩

/-- `IK`'s `andI` is a literal `KAxiom` instance. -/
theorem k_derivable_of_ik_andI {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.AndI φ ψ) :=
  ⟨.ax [] _ (KAxiom.andI φ ψ)⟩

/-- `IK`'s `andE1` is a literal `KAxiom` instance. -/
theorem k_derivable_of_ik_andE1 {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.AndE1 φ ψ) :=
  ⟨.ax [] _ (KAxiom.andE1 φ ψ)⟩

/-- `IK`'s `andE2` is a literal `KAxiom` instance. -/
theorem k_derivable_of_ik_andE2 {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.AndE2 φ ψ) :=
  ⟨.ax [] _ (KAxiom.andE2 φ ψ)⟩

/-- `IK`'s `orI1` is a literal `KAxiom` instance. -/
theorem k_derivable_of_ik_orI1 {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.OrI1 φ ψ) :=
  ⟨.ax [] _ (KAxiom.orI1 φ ψ)⟩

/-- `IK`'s `orI2` is a literal `KAxiom` instance. -/
theorem k_derivable_of_ik_orI2 {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.OrI2 φ ψ) :=
  ⟨.ax [] _ (KAxiom.orI2 φ ψ)⟩

/-- `IK`'s `orE` is a literal `KAxiom` instance. -/
theorem k_derivable_of_ik_orE {φ ψ χ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.OrE φ ψ χ) :=
  ⟨.ax [] _ (KAxiom.orE φ ψ χ)⟩

/-- `IK`'s `k` (`k1`/Kb, `□(φ → ψ) → (□φ → □ψ)`) is a literal `KAxiom.modalK` instance. -/
theorem k_derivable_of_ik_k {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom)
      ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))) :=
  ⟨.ax [] _ (KAxiom.modalK φ ψ)⟩

/-! ## Derived Schemata -/

/-- `IK`'s `kdia` (`k2`/Kd: `□(φ → ψ) → (◇φ → ◇ψ)`) is **derivable**, not a literal axiom,
in classical `K`: `K` axiomatizes diamond distribution via the raw `¬□¬`-encoded
`k_dist_diamond` plus the `diaDualityFwd`/`diaDualityBack` bridge axioms, not via a
primitive-diamond schema.

Proof (all steps generic combinators from `Theorems/Modal/Basic.lean` /
`Theorems/Combinators.lean`, instantiated at `S := Modal.HilbertK`):
with `A := □(φ → ψ)`, `B := ¬□¬φ`, `C := ¬□¬ψ`, `D := ◇φ`, `E := ◇ψ`:
1. `k1 : A → (B → C)` (`k_dist_diamond`).
2. `fwd : D → B` (`diaDualityFwd`), `back : C → E` (`diaDualityBack`).
3. `ModusPonens.mp flip k1 : B → (A → C)`; `imp_trans fwd this : D → (A → C)`;
   `ModusPonens.mp flip this : A → (D → C)`.
4. `ModusPonens.mp b_combinator back : (D → C) → (D → E)`.
5. `imp_trans` step 3 and step 4: `A → (D → E)`, i.e. the goal.

(`flip` and `b_combinator` are unconditional tautologies of shape `⊢ X → Y`; each use above
applies `ModusPonens.mp` to instantiate them against a concrete hypothesis.) -/
theorem k_derivable_of_ik_kdia {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom)
      ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))) := by
  have k1 := @Cslib.Logic.Theorems.Modal.Basic.k_dist_diamond
    (Proposition Atom) _ _ _ Modal.HilbertK _ _ φ ψ
  have fwd := HasAxiomDiaDualityFwd.diaDualityFwd (S := Modal.HilbertK) (φ := φ)
  have back := HasAxiomDiaDualityBack.diaDualityBack (S := Modal.HilbertK) (φ := ψ)
  have step1 := ModusPonens.mp (Cslib.Logic.Theorems.Combinators.flip (S := Modal.HilbertK)) k1
  have step2 := Cslib.Logic.Theorems.Combinators.imp_trans fwd step1
  have step3 := ModusPonens.mp (Cslib.Logic.Theorems.Combinators.flip (S := Modal.HilbertK)) step2
  have step4 := ModusPonens.mp
    (Cslib.Logic.Theorems.Combinators.b_combinator (S := Modal.HilbertK) (φ := ◇φ)) back
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans step3 step4
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- `IK`'s `dbot` (`k5`/Nd: `◇⊥ → ⊥`) is **derivable** in classical `K` from the tautology
`⊢ ⊥ → ⊥` (`identity`), necessitated to `⊢ □(⊥ → ⊥)` (i.e. `⊢ □¬⊥`), then `app1` and
`diaDualityFwd` compose it into `◇⊥ → ⊥`. -/
theorem k_derivable_of_ik_dbot :
    Derivable (@KAxiom Atom) ((◇(Proposition.bot : Proposition Atom)).imp Proposition.bot) := by
  have hid := Cslib.Logic.Theorems.Combinators.identity (S := Modal.HilbertK)
    (F := Proposition Atom) Proposition.bot
  obtain ⟨dId⟩ := hid
  have hboxNegBot := (⟨.necessitation _ dId⟩ :
    Derivable (@KAxiom Atom) (Proposition.box (Proposition.bot.imp Proposition.bot)))
  obtain ⟨dBoxNegBot⟩ := hboxNegBot
  have happ1 := @Cslib.Logic.Theorems.Combinators.app1
    (Proposition Atom) _ _ Modal.HilbertK _ _
    (Proposition.box (Proposition.bot.imp Proposition.bot)) Proposition.bot
  have hnegneg := ModusPonens.mp happ1 ⟨dBoxNegBot⟩
  have fwd := HasAxiomDiaDualityFwd.diaDualityFwd (S := Modal.HilbertK)
    (φ := (Proposition.bot : Proposition Atom))
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans fwd hnegneg
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

end Cslib.Logic.Modal

end
