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

/-! ## Helper Combinators (Phase 7) -/

/-- Necessitated K-distribution over a two-step implication: from a closed
`⊢ A → (B → C)`, derive `⊢ □A → (□B → □C)`. Necessitates the hypothesis and applies
`KAxiom.modalK` twice, composed via `imp_trans`. -/
theorem k_boxDistrib2 {A B C : Proposition Atom}
    (h : Derivable (@KAxiom Atom) (A.imp (B.imp C))) :
    Derivable (@KAxiom Atom)
      ((Proposition.box A).imp ((Proposition.box B).imp (Proposition.box C))) := by
  obtain ⟨d⟩ := h
  have hIS : InferenceSystem.DerivableIn Modal.HilbertK (A.imp (B.imp C)) := ⟨d⟩
  have hbox := Necessitation.nec hIS
  have kAB := HasAxiomK.K (S := Modal.HilbertK) (φ := A) (ψ := B.imp C)
  have step1 := ModusPonens.mp kAB hbox
  have kBC := HasAxiomK.K (S := Modal.HilbertK) (φ := B) (ψ := C)
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans step1 kBC
  obtain ⟨dg⟩ := goal
  exact ⟨dg⟩

/-- Dual negation: `⊢ ¬◇φ → □¬φ`. Derived from `diaDualityBack` (contraposed) composed
with `double_negation`. -/
theorem k_dualNeg {φ : Proposition Atom} :
    Derivable (@KAxiom Atom)
      (((◇φ).imp Proposition.bot).imp (Proposition.box (φ.imp Proposition.bot))) := by
  have back := HasAxiomDiaDualityBack.diaDualityBack (S := Modal.HilbertK) (φ := φ)
  have contra := Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    (S := Modal.HilbertK) back
  have dne := @Cslib.Logic.Theorems.Propositional.Core.double_negation
    (Proposition Atom) _ _ Modal.HilbertK _ _ (Proposition.box (φ.imp Proposition.bot))
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans contra dne
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- Necessitated K-distribution (single step): from a closed `⊢ A → B`, derive
`⊢ □A → □B`. Necessitates the hypothesis and applies `KAxiom.modalK`. -/
theorem k_boxMono {A B : Proposition Atom} (h : Derivable (@KAxiom Atom) (A.imp B)) :
    Derivable (@KAxiom Atom) ((Proposition.box A).imp (Proposition.box B)) := by
  obtain ⟨d⟩ := h
  have hIS : InferenceSystem.DerivableIn Modal.HilbertK (A.imp B) := ⟨d⟩
  have hbox := Necessitation.nec hIS
  have kAB := HasAxiomK.K (S := Modal.HilbertK) (φ := A) (ψ := B)
  have goal := ModusPonens.mp kAB hbox
  obtain ⟨dg⟩ := goal
  exact ⟨dg⟩

/-- Diamond monotonicity: from a closed `⊢ A → B`, derive `⊢ ◇A → ◇B`. Necessitates the
hypothesis and applies `k_derivable_of_ik_kdia`. -/
theorem k_diamondMono {A B : Proposition Atom} (h : Derivable (@KAxiom Atom) (A.imp B)) :
    Derivable (@KAxiom Atom) ((◇A).imp (◇B)) := by
  obtain ⟨d⟩ := h
  have hIS : InferenceSystem.DerivableIn Modal.HilbertK (A.imp B) := ⟨d⟩
  have hbox := Necessitation.nec hIS
  have kdiaInst := k_derivable_of_ik_kdia (φ := A) (ψ := B)
  obtain ⟨dkdia⟩ := kdiaInst
  have kdiaIS : InferenceSystem.DerivableIn Modal.HilbertK
      ((Proposition.box (A.imp B)).imp ((◇A).imp (◇B))) := ⟨dkdia⟩
  have goal := ModusPonens.mp kdiaIS hbox
  obtain ⟨dg⟩ := goal
  exact ⟨dg⟩

/-- Converse Peirce-style decomposition of a negated implication into a native conjunction:
`⊢ ¬(A → B) → (A ∧ ¬B)`. Needs classical DNE (`efq_neg` contraposed, composed with
`double_negation`, for the `A`-component; `implyK` contraposed for the `¬B`-component;
combined via the `implyS` S-combinator into the native `andI`). -/
theorem k_notImpToAnd {A B : Proposition Atom} :
    Derivable (@KAxiom Atom)
      (((A.imp B).imp Proposition.bot).imp (A.and (B.imp Proposition.bot))) := by
  have efqNeg := @Cslib.Logic.Theorems.Propositional.Core.efq_neg
    (Proposition Atom) _ _ Modal.HilbertK _ _ (φ := A) (ψ := B)
  have p1contra := Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    (S := Modal.HilbertK) efqNeg
  have dneA := @Cslib.Logic.Theorems.Propositional.Core.double_negation
    (Proposition Atom) _ _ Modal.HilbertK _ _ A
  have p1 := Cslib.Logic.Theorems.Combinators.imp_trans p1contra dneA
  have implyKInst := HasAxiomImplyK.implyK (S := Modal.HilbertK) (φ := B) (ψ := A)
  have p2 := Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    (S := Modal.HilbertK) implyKInst
  have andIInst := HasAxiomAndI.andI (S := Modal.HilbertK) (φ := A) (ψ := B.imp Proposition.bot)
  have step := Cslib.Logic.Theorems.Combinators.imp_trans p1 andIInst
  have implySInst := HasAxiomImplyS.implyS (S := Modal.HilbertK)
    (φ := (A.imp B).imp Proposition.bot) (ψ := B.imp Proposition.bot)
    (χ := A.and (B.imp Proposition.bot))
  have goal := ModusPonens.mp (ModusPonens.mp implySInst step) p2
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- Native-conjunction-to-negated-implication: `⊢ (A ∧ ¬B) → ¬(A → B)`. Purely minimal
(no DNE needed): extract `A` and `¬B` from the conjunction via `andE1`/`andE2`, then combine
with a fixed instance of `b_combinator` (twice) and the `implyS` S-combinator to discharge
the shared antecedent `A ∧ ¬B`. -/
theorem k_andToNotImp {A B : Proposition Atom} :
    Derivable (@KAxiom Atom)
      ((A.and (B.imp Proposition.bot)).imp ((A.imp B).imp Proposition.bot)) := by
  have f1 := HasAxiomAndE1.andE1 (S := Modal.HilbertK) (φ := A) (ψ := B.imp Proposition.bot)
  have f2 := HasAxiomAndE2.andE2 (S := Modal.HilbertK) (φ := A) (ψ := B.imp Proposition.bot)
  have bCA : InferenceSystem.DerivableIn Modal.HilbertK
      ((A.imp B).imp (((A.and (B.imp Proposition.bot)).imp A).imp
        ((A.and (B.imp Proposition.bot)).imp B))) := by
    have raw := Cslib.Logic.Theorems.Combinators.b_combinator (S := Modal.HilbertK)
      (φ := A.and (B.imp Proposition.bot)) (ψ := A) (χ := B)
    exact raw
  have flippedBCA := ModusPonens.mp (Cslib.Logic.Theorems.Combinators.flip (S := Modal.HilbertK))
    bCA
  have substepA := ModusPonens.mp flippedBCA f1
  have hPrime := ModusPonens.mp (Cslib.Logic.Theorems.Combinators.flip (S := Modal.HilbertK))
    substepA
  have bDirect := Cslib.Logic.Theorems.Combinators.b_combinator (S := Modal.HilbertK)
    (φ := A.imp B) (ψ := B) (χ := (Proposition.bot : Proposition Atom))
  have hDoublePrime := Cslib.Logic.Theorems.Combinators.imp_trans f2 bDirect
  have implySInst := HasAxiomImplyS.implyS (S := Modal.HilbertK)
    (φ := A.and (B.imp Proposition.bot)) (ψ := (A.imp B).imp B)
    (χ := (A.imp B).imp Proposition.bot)
  have goal := ModusPonens.mp (ModusPonens.mp implySInst hDoublePrime) hPrime
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- `¬□X → ◇¬X` for any formula `X` (needed with `X := φ → ψ` for `idb`). Derived from
`box_mono` of `double_negation` (contraposed) composed with `diaDualityBack` at `¬X`. -/
theorem k_notBoxToDiaNeg {X : Proposition Atom} :
    Derivable (@KAxiom Atom)
      (((Proposition.box X).imp Proposition.bot).imp
        (◇(X.imp Proposition.bot))) := by
  have dneX := @Cslib.Logic.Theorems.Propositional.Core.double_negation
    (Proposition Atom) _ _ Modal.HilbertK _ _ X
  obtain ⟨ddneX⟩ := dneX
  have dneXK : Derivable (@KAxiom Atom)
      (((X.imp Proposition.bot).imp Proposition.bot).imp X) := ⟨ddneX⟩
  have boxDne := k_boxMono dneXK
  obtain ⟨dbd⟩ := boxDne
  have boxDneIS : InferenceSystem.DerivableIn Modal.HilbertK
      ((Proposition.box ((X.imp Proposition.bot).imp Proposition.bot)).imp
        (Proposition.box X)) := ⟨dbd⟩
  have contraBoxDne := Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    (S := Modal.HilbertK) boxDneIS
  have dualBack := HasAxiomDiaDualityBack.diaDualityBack (S := Modal.HilbertK)
    (φ := X.imp Proposition.bot)
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans contraBoxDne dualBack
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- `◇¬X → ¬□X` for any formula `X`. Derived from `diaDualityFwd` at `¬X` composed with the
contraposition of `box_mono` of `dni`. -/
theorem k_diaNegToNotBox {X : Proposition Atom} :
    Derivable (@KAxiom Atom)
      ((◇(X.imp Proposition.bot)).imp ((Proposition.box X).imp Proposition.bot)) := by
  have dniX := Cslib.Logic.Theorems.Combinators.dni (S := Modal.HilbertK) (F := Proposition Atom) X
  obtain ⟨ddniX⟩ := dniX
  have dniXK : Derivable (@KAxiom Atom)
      (X.imp ((X.imp Proposition.bot).imp Proposition.bot)) := ⟨ddniX⟩
  have boxDni := k_boxMono dniXK
  obtain ⟨dbd⟩ := boxDni
  have boxDniIS : InferenceSystem.DerivableIn Modal.HilbertK
      ((Proposition.box X).imp
        (Proposition.box ((X.imp Proposition.bot).imp Proposition.bot))) := ⟨dbd⟩
  have contraBoxDni := Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    (S := Modal.HilbertK) boxDniIS
  have dualFwdNegX := HasAxiomDiaDualityFwd.diaDualityFwd (S := Modal.HilbertK)
    (φ := X.imp Proposition.bot)
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans dualFwdNegX contraBoxDni
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-! ## `cd` (Fischer-Servi `k3`/Cd) -/

/-- `IK`'s `cd` (`k3`/Cd, Fischer-Servi: `◇(φ ∨ ψ) → (◇φ ∨ ◇ψ)`) is **derivable** in
classical `K`, proved via its contrapositive plus reverse contraposition (`rcp`, needs
classical DNE/Peirce — available since `KAxiom` includes `peirce`):

With `A₀ := ◇(φ ∨ ψ)`, `B₀ := ◇φ ∨ ◇ψ`, `P := ¬B₀`:
1. `k1 : ¬φ → (¬ψ → ¬(φ ∨ ψ))` is literally `orE φ ψ ⊥`.
2. `T2 := boxDistrib2 k1 : □¬φ → (□¬ψ → □¬(φ ∨ ψ))`.
3. `notDiaPhi := contraposition (orI1 : ◇φ → B₀) : P → ¬◇φ`;
   `notDiaPsi := contraposition (orI2 : ◇ψ → B₀) : P → ¬◇ψ`.
4. `toBoxNotPhi := imp_trans notDiaPhi dualNeg(φ) : P → □¬φ`;
   `toBoxNotPsi := imp_trans notDiaPsi dualNeg(ψ) : P → □¬ψ`.
5. `step7a := imp_trans toBoxNotPhi T2 : P → (□¬ψ → □¬(φ ∨ ψ))`.
6. `step8 := MP (MP implyS step7a) toBoxNotPsi : P → □¬(φ ∨ ψ)` (`implyS`-combinator
   discharges the shared antecedent `P`).
7. `dualFwdOr := diaDualityFwd (φ ∨ ψ) : A₀ → ¬□¬(φ ∨ ψ)`; via `flip` and `imp_trans` with
   step 6: `contrapositive := P → ¬A₀`.
8. `rcp contrapositive : A₀ → B₀`, i.e. the goal. -/
theorem k_derivable_of_ik_cd {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ))) := by
  have k1 := HasAxiomOrE.orE (S := Modal.HilbertK) (φ := φ) (ψ := ψ)
    (χ := (Proposition.bot : Proposition Atom))
  have t2ish := k_boxDistrib2 k1
  obtain ⟨dT2⟩ := t2ish
  have T2 : InferenceSystem.DerivableIn Modal.HilbertK
      ((Proposition.box (φ.imp Proposition.bot)).imp
        ((Proposition.box (ψ.imp Proposition.bot)).imp
          (Proposition.box ((φ.or ψ).imp Proposition.bot)))) := ⟨dT2⟩
  have orI1Inst := HasAxiomOrI1.orI1 (S := Modal.HilbertK) (φ := ◇φ) (ψ := ◇ψ)
  have orI2Inst := HasAxiomOrI2.orI2 (S := Modal.HilbertK) (φ := ◇φ) (ψ := ◇ψ)
  have notDiaPhi := Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    (S := Modal.HilbertK) orI1Inst
  have notDiaPsi := Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    (S := Modal.HilbertK) orI2Inst
  have dualNegPhi := k_dualNeg (φ := φ)
  obtain ⟨dDNφ⟩ := dualNegPhi
  have dualNegPhiIS : InferenceSystem.DerivableIn Modal.HilbertK
      (((◇φ).imp Proposition.bot).imp (Proposition.box (φ.imp Proposition.bot))) := ⟨dDNφ⟩
  have dualNegPsi := k_dualNeg (φ := ψ)
  obtain ⟨dDNψ⟩ := dualNegPsi
  have dualNegPsiIS : InferenceSystem.DerivableIn Modal.HilbertK
      (((◇ψ).imp Proposition.bot).imp (Proposition.box (ψ.imp Proposition.bot))) := ⟨dDNψ⟩
  have toBoxNotPhi := Cslib.Logic.Theorems.Combinators.imp_trans notDiaPhi dualNegPhiIS
  have toBoxNotPsi := Cslib.Logic.Theorems.Combinators.imp_trans notDiaPsi dualNegPsiIS
  have step7a := Cslib.Logic.Theorems.Combinators.imp_trans toBoxNotPhi T2
  have step8 := ModusPonens.mp
    (ModusPonens.mp
      (HasAxiomImplyS.implyS (S := Modal.HilbertK)
        (φ := (((◇φ).or (◇ψ)).imp Proposition.bot))
        (ψ := Proposition.box (ψ.imp Proposition.bot))
        (χ := Proposition.box ((φ.or ψ).imp Proposition.bot)))
      step7a) toBoxNotPsi
  have dualFwdOr := HasAxiomDiaDualityFwd.diaDualityFwd (S := Modal.HilbertK) (φ := φ.or ψ)
  have flipped := ModusPonens.mp (Cslib.Logic.Theorems.Combinators.flip (S := Modal.HilbertK))
    dualFwdOr
  have contrapositive := Cslib.Logic.Theorems.Combinators.imp_trans step8 flipped
  have goal := @Cslib.Logic.Theorems.Propositional.Core.rcp
    (Proposition Atom) _ _ Modal.HilbertK _ _
    (φ := (◇φ).or (◇ψ)) (ψ := ◇(φ.or ψ)) contrapositive
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-! ## `idb` (Fischer-Servi `k4`/Idb) -/

/-- `IK`'s `idb` (`k4`/Idb, Fischer-Servi: `(◇φ → □ψ) → □(φ → ψ)`) is **derivable** in
classical `K` — the fiddliest schema, proved via its contrapositive plus `rcp`:

With `A₀ := ◇φ → □ψ`, `B₀ := □(φ → ψ)`:
1. `toDiaNeg := notBoxToDiaNeg (X := φ → ψ) : ¬B₀ → ◇¬(φ → ψ)`.
2. `toAnd := notImpToAnd (A := φ, B := ψ) : ¬(φ → ψ) → (φ ∧ ¬ψ)`.
3. `toDiaAnd := diamondMono toAnd : ◇¬(φ → ψ) → ◇(φ ∧ ¬ψ)` (call the consequent `Q`).
4. `toDiaPhi := diamondMono (andE1 : (φ ∧ ¬ψ) → φ) : Q → ◇φ`;
   `toDiaNegPsi := diamondMono (andE2 : (φ ∧ ¬ψ) → ¬ψ) : Q → ◇¬ψ`.
5. `toNotBoxPsi := diaNegToNotBox (X := ψ) : ◇¬ψ → ¬□ψ`;
   `toNotBoxPsiFinal := imp_trans toDiaNegPsi toNotBoxPsi : Q → ¬□ψ`.
6. Pair `toDiaPhi` and `toNotBoxPsiFinal` via `andI` + `implyS` (shared antecedent `Q`):
   `pairFinal : Q → (◇φ ∧ ¬□ψ)`.
7. `toNotA0 := imp_trans pairFinal (andToNotImp (A := ◇φ, B := □ψ)) : Q → ¬A₀`.
8. Chain steps 1, 3, 7: `contrapositive := ¬B₀ → ¬A₀`.
9. `rcp contrapositive : A₀ → B₀`, i.e. the goal. -/
theorem k_derivable_of_ik_idb {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ))) := by
  have toDiaNeg := k_notBoxToDiaNeg (X := φ.imp ψ)
  obtain ⟨dTDN⟩ := toDiaNeg
  have toDiaNegIS : InferenceSystem.DerivableIn Modal.HilbertK
      (((Proposition.box (φ.imp ψ)).imp Proposition.bot).imp (◇((φ.imp ψ).imp Proposition.bot))) :=
    ⟨dTDN⟩
  have toAnd := k_notImpToAnd (A := φ) (B := ψ)
  have toDiaAnd := k_diamondMono toAnd
  obtain ⟨dTDA⟩ := toDiaAnd
  have toDiaAndIS : InferenceSystem.DerivableIn Modal.HilbertK
      ((◇((φ.imp ψ).imp Proposition.bot)).imp (◇(φ.and (ψ.imp Proposition.bot)))) := ⟨dTDA⟩
  have andE1Inst := HasAxiomAndE1.andE1 (S := Modal.HilbertK) (φ := φ) (ψ := ψ.imp Proposition.bot)
  obtain ⟨dAndE1⟩ := andE1Inst
  have andE1K : Derivable (@KAxiom Atom) ((φ.and (ψ.imp Proposition.bot)).imp φ) := ⟨dAndE1⟩
  have andE2Inst := HasAxiomAndE2.andE2 (S := Modal.HilbertK) (φ := φ) (ψ := ψ.imp Proposition.bot)
  obtain ⟨dAndE2⟩ := andE2Inst
  have andE2K : Derivable (@KAxiom Atom)
      ((φ.and (ψ.imp Proposition.bot)).imp (ψ.imp Proposition.bot)) := ⟨dAndE2⟩
  have toDiaPhi := k_diamondMono andE1K
  obtain ⟨dTDP⟩ := toDiaPhi
  have toDiaPhiIS : InferenceSystem.DerivableIn Modal.HilbertK
      ((◇(φ.and (ψ.imp Proposition.bot))).imp (◇φ)) := ⟨dTDP⟩
  have toDiaNegPsi := k_diamondMono andE2K
  obtain ⟨dTDNP⟩ := toDiaNegPsi
  have toDiaNegPsiIS : InferenceSystem.DerivableIn Modal.HilbertK
      ((◇(φ.and (ψ.imp Proposition.bot))).imp (◇(ψ.imp Proposition.bot))) := ⟨dTDNP⟩
  have toNotBoxPsi := k_diaNegToNotBox (X := ψ)
  obtain ⟨dNBP⟩ := toNotBoxPsi
  have toNotBoxPsiIS : InferenceSystem.DerivableIn Modal.HilbertK
      ((◇(ψ.imp Proposition.bot)).imp ((Proposition.box ψ).imp Proposition.bot)) := ⟨dNBP⟩
  have toNotBoxPsiFinal := Cslib.Logic.Theorems.Combinators.imp_trans toDiaNegPsiIS toNotBoxPsiIS
  have andIInst2 := HasAxiomAndI.andI (S := Modal.HilbertK) (φ := ◇φ)
    (ψ := (Proposition.box ψ).imp Proposition.bot)
  have stepPair := Cslib.Logic.Theorems.Combinators.imp_trans toDiaPhiIS andIInst2
  have implySInst2 := HasAxiomImplyS.implyS (S := Modal.HilbertK)
    (φ := ◇(φ.and (ψ.imp Proposition.bot)))
    (ψ := (Proposition.box ψ).imp Proposition.bot)
    (χ := (◇φ).and ((Proposition.box ψ).imp Proposition.bot))
  have pairFinal := ModusPonens.mp (ModusPonens.mp implySInst2 stepPair) toNotBoxPsiFinal
  have andToNotImp2 := k_andToNotImp (A := ◇φ) (B := Proposition.box ψ)
  obtain ⟨dATNI⟩ := andToNotImp2
  have andToNotImp2IS : InferenceSystem.DerivableIn Modal.HilbertK
      (((◇φ).and ((Proposition.box ψ).imp Proposition.bot)).imp
        (((◇φ).imp (Proposition.box ψ)).imp Proposition.bot)) := ⟨dATNI⟩
  have toNotA0 := Cslib.Logic.Theorems.Combinators.imp_trans pairFinal andToNotImp2IS
  have chain1 := Cslib.Logic.Theorems.Combinators.imp_trans toDiaNegIS toDiaAndIS
  have contrapositive := Cslib.Logic.Theorems.Combinators.imp_trans chain1 toNotA0
  have goal := @Cslib.Logic.Theorems.Propositional.Core.rcp
    (Proposition Atom) _ _ Modal.HilbertK _ _
    (φ := Proposition.box (φ.imp ψ)) (ψ := (◇φ).imp (Proposition.box ψ)) contrapositive
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

end Cslib.Logic.Modal

end
