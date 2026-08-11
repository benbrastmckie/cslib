/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.ProofSystem.Instances.K
public import Cslib.Logics.Modal.ProofSystem.Instances.T
public import Cslib.Logics.Modal.ProofSystem.Instances.S4
public import Cslib.Logics.Modal.ProofSystem.Instances.S5
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IK
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IT
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IS4
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5
public import Cslib.Logics.Modal.Metalogic.InterSystem.Lifting
public import Cslib.Logics.Modal.Metalogic.InterSystem.AxiomSubsumption
public import Cslib.Foundations.Logic.Theorems.Modal.Basic
public import Cslib.Foundations.Logic.Theorems.Combinators

/-! # The Intuitionistic → Classical Bridge (`IK → K`)

This module proves the one genuinely hard direction of the same-language-base modal lattice:
intuitionistic `IK` uses a **primitive** diamond with Fischer-Servi axiom schemata (`kdia`,
`cd`, `idb`, `dbot`), while classical `K` uses the **dual** diamond (`◇φ := ¬□¬φ`, witnessed by
the `diamondDualityFwd`/`diamondDualityBack` axiom schemata). This is not a syntactic rename — each
`IKModalAxiom` instance must be shown *derivable* (not literally an axiom instance) in
`KAxiom`, using the generalized lift `Derivable_of_axiom_derivable`
(`InterSystem/Lifting.lean`).

## Per-Axiom Classical `K`-Derivations

- The eight shared propositional constructors (`implyK`, `implyS`, `andI`, `andE1`, `andE2`,
  `orI1`, `orI2`, `orE`) and `efq`, `k` (`modalK`): **direct** — each is a literal `KAxiom`
  instance under the same name.
- `kdia` (`□(φ → ψ) → (◇φ → ◇ψ)`): derived via the generic raw-encoding K-diamond
  distribution theorem `k_dist_diamond` (`Theorems/Modal/Basic.lean`) composed with the
  `diamondDualityFwd`/`diamondDualityBack` axiom instances, using only the `flip`/`b_combinator`/
  `imp_trans` propositional combinators (`Theorems/Combinators.lean`).
- `dbot` (`◇⊥ → ⊥`): derived from `⊢ □¬⊥` (necessitation of the tautology `⊢ ¬⊥`, i.e.
  `identity ⊥ : ⊢ ⊥ → ⊥`), `app1` (`φ → ((φ → ψ) → ψ)`), and `diamondDualityFwd`.
- `cd` (`◇(φ ∨ ψ) → (◇φ ∨ ◇ψ)`) and `idb` (`(◇φ → □ψ) → □(φ → ψ)`), the two fiddliest
  Fischer-Servi schemata, are each derived via their contrapositive plus `rcp` (see
  `k_derivable_of_ik_cd`/`k_derivable_of_ik_idb` for the step-by-step derivations).

The final assembly `∀ φ, IKModalAxiom φ → Derivable KAxiom φ`
(`ikAxiom_derivable_in_K`) and the concluding `ikDerivable_implies_kDerivable` combine all 14
schemata into the bridge theorem. The module also carries the analogous `IT → T`, `IS4 → S4`,
and `IS5 → S5` bridges (`itDerivable_implies_tDerivable`, `is4Derivable_implies_s4Derivable`,
`is5Derivable_implies_s5Derivable`), each reusing the `IK → K` derivations for the shared axioms
and adding only the system-specific schema (`tDia`, `fourDia`, `bDia`).
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-! ## Direct Schemata (Literal `KAxiom` Instances) -/

/-- `IK`'s `implyK` is a `KAxiom` instance, produced as a bare `SchemaUnion kTags` witness
rather than a named constructor directly -- `KAxiom` is `abbrev KAxiom := SchemaUnion kTags`,
so this witness typechecks directly by defeq. -/
theorem k_derivable_of_ik_implyK {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (φ.imp (ψ.imp φ)) :=
  ⟨.ax [] _ ⟨.implyK, by decide, φ, ψ, rfl⟩⟩

/-- `IK`'s `implyS` is a `KAxiom` instance
produced as a bare `SchemaUnion` witness (see `implyK` above). -/
theorem k_derivable_of_ik_implyS {φ ψ χ : Proposition Atom} :
    Derivable (@KAxiom Atom) ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  ⟨.ax [] _ ⟨.implyS, by decide, φ, ψ, χ, rfl⟩⟩

/-- `IK`'s `efq` is a `KAxiom` instance
produced as a bare `SchemaUnion` witness (see `implyK` above). -/
theorem k_derivable_of_ik_efq {φ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Proposition.bot.imp φ) :=
  ⟨.ax [] _ ⟨.efq, by decide, φ, rfl⟩⟩

/-- `IK`'s `andI` is a `KAxiom` instance
produced as a bare `SchemaUnion` witness (see `implyK` above). -/
theorem k_derivable_of_ik_andI {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.AndI φ ψ) :=
  ⟨.ax [] _ ⟨.andI, by decide, φ, ψ, rfl⟩⟩

/-- `IK`'s `andE1` is a `KAxiom` instance
produced as a bare `SchemaUnion` witness (see `implyK` above). -/
theorem k_derivable_of_ik_andE1 {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.AndE1 φ ψ) :=
  ⟨.ax [] _ ⟨.andE1, by decide, φ, ψ, rfl⟩⟩

/-- `IK`'s `andE2` is a `KAxiom` instance
produced as a bare `SchemaUnion` witness (see `implyK` above). -/
theorem k_derivable_of_ik_andE2 {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.AndE2 φ ψ) :=
  ⟨.ax [] _ ⟨.andE2, by decide, φ, ψ, rfl⟩⟩

/-- `IK`'s `orI1` is a `KAxiom` instance
produced as a bare `SchemaUnion` witness (see `implyK` above). -/
theorem k_derivable_of_ik_orI1 {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.OrI1 φ ψ) :=
  ⟨.ax [] _ ⟨.orI1, by decide, φ, ψ, rfl⟩⟩

/-- `IK`'s `orI2` is a `KAxiom` instance
produced as a bare `SchemaUnion` witness (see `implyK` above). -/
theorem k_derivable_of_ik_orI2 {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.OrI2 φ ψ) :=
  ⟨.ax [] _ ⟨.orI2, by decide, φ, ψ, rfl⟩⟩

/-- `IK`'s `orE` is a `KAxiom` instance
produced as a bare `SchemaUnion` witness (see `implyK` above). -/
theorem k_derivable_of_ik_orE {φ ψ χ : Proposition Atom} :
    Derivable (@KAxiom Atom) (Cslib.Logic.Axioms.OrE φ ψ χ) :=
  ⟨.ax [] _ ⟨.orE, by decide, φ, ψ, χ, rfl⟩⟩

/-- `IK`'s `k` (`k1`/Kb, `□(φ → ψ) → (□φ → □ψ)`) is a `KAxiom` instance produced as a bare
`SchemaUnion` witness (see `implyK` above). -/
theorem k_derivable_of_ik_k {φ ψ : Proposition Atom} :
    Derivable (@KAxiom Atom)
      ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ))) :=
  ⟨.ax [] _ ⟨.modalK, by decide, φ, ψ, rfl⟩⟩

/-! ## Derived Schemata -/

/-- `IK`'s `kdia` (`k2`/Kd: `□(φ → ψ) → (◇φ → ◇ψ)`) is **derivable**, not a literal axiom,
in classical `K`: `K` axiomatizes diamond distribution via the raw `¬□¬`-encoded
`k_dist_diamond` plus the `diamondDualityFwd`/`diamondDualityBack` bridge axioms, not via a
primitive-diamond schema.

Proof (all steps generic combinators from `Theorems/Modal/Basic.lean` /
`Theorems/Combinators.lean`, instantiated at `S := Modal.HilbertK`):
with `A := □(φ → ψ)`, `B := ¬□¬φ`, `C := ¬□¬ψ`, `D := ◇φ`, `E := ◇ψ`:
1. `k1 : A → (B → C)` (`k_dist_diamond`).
2. `fwd : D → B` (`diamondDualityFwd`), `back : C → E` (`diamondDualityBack`).
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
  have fwd := HasAxiomDiamondDualityFwd.diamondDualityFwd (S := Modal.HilbertK) (φ := φ)
  have back := HasAxiomDiamondDualityBack.diamondDualityBack (S := Modal.HilbertK) (φ := ψ)
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
`diamondDualityFwd` compose it into `◇⊥ → ⊥`. -/
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
  have fwd := HasAxiomDiamondDualityFwd.diamondDualityFwd (S := Modal.HilbertK)
    (φ := (Proposition.bot : Proposition Atom))
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans fwd hnegneg
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-! ## Helper Combinators -/

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

/-- Dual negation: `⊢ ¬◇φ → □¬φ`. Derived from `diamondDualityBack` (contraposed) composed
with `double_negation`. -/
theorem k_dualNeg {φ : Proposition Atom} :
    Derivable (@KAxiom Atom)
      (((◇φ).imp Proposition.bot).imp (Proposition.box (φ.imp Proposition.bot))) := by
  have back := HasAxiomDiamondDualityBack.diamondDualityBack (S := Modal.HilbertK) (φ := φ)
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
`box_mono` of `double_negation` (contraposed) composed with `diamondDualityBack` at `¬X`. -/
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
  have dualBack := HasAxiomDiamondDualityBack.diamondDualityBack (S := Modal.HilbertK)
    (φ := X.imp Proposition.bot)
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans contraBoxDne dualBack
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- `◇¬X → ¬□X` for any formula `X`. Derived from `diamondDualityFwd` at `¬X` composed with the
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
  have dualFwdNegX := HasAxiomDiamondDualityFwd.diamondDualityFwd (S := Modal.HilbertK)
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
7. `dualFwdOr := diamondDualityFwd (φ ∨ ψ) : A₀ → ¬□¬(φ ∨ ψ)`; via `flip` and `imp_trans` with
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
  have dualFwdOr := HasAxiomDiamondDualityFwd.diamondDualityFwd (S := Modal.HilbertK) (φ := φ.or ψ)
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

/-! ## Assembly: The `IK → K` Bridge -/

/-- Every `IKModalAxiom` instance is `Derivable` in classical `K`. Assembles the 14
per-axiom derivations above (the 12 from the Direct/Derived Schemata sections above plus
`cd`/`idb`) into the total axiom→derivation map required by
`Derivable_of_axiom_derivable`. -/
theorem ikAxiom_derivable_in_K {φ : Proposition Atom} (h : IKModalAxiom φ) :
    Derivable (@KAxiom Atom) φ :=
  match h with
  | .implyK _ _ => k_derivable_of_ik_implyK
  | .implyS _ _ _ => k_derivable_of_ik_implyS
  | .efq _ => k_derivable_of_ik_efq
  | .andI _ _ => k_derivable_of_ik_andI
  | .andE1 _ _ => k_derivable_of_ik_andE1
  | .andE2 _ _ => k_derivable_of_ik_andE2
  | .orI1 _ _ => k_derivable_of_ik_orI1
  | .orI2 _ _ => k_derivable_of_ik_orI2
  | .orE _ _ _ => k_derivable_of_ik_orE
  | .k _ _ => k_derivable_of_ik_k
  | .kdia _ _ => k_derivable_of_ik_kdia
  | .cd _ _ => k_derivable_of_ik_cd
  | .idb _ _ => k_derivable_of_ik_idb
  | .dbot => k_derivable_of_ik_dbot

/-- **The `IK → K` bridge**: every `IK`-derivable formula is `K`-derivable. Concludes the
generalized axiom→derivation lift `Derivable_of_axiom_derivable`
(`InterSystem/Lifting.lean`) applied to `ikAxiom_derivable_in_K`. This is the "honest"
Intuitionistic-to-Classical bridge: adding `peirce` (DNE) to `IK`'s Fischer-Servi
primitive-diamond axioms collapses them to classical `K`'s dual-diamond axiomatization
(`diamondDualityFwd`/`diamondDualityBack`); the two axiomatizations characterize the same classical
diamond, but only propositionally, not syntactically. -/
theorem ikDerivable_implies_kDerivable {φ : Proposition Atom} (h : Derivable IKModalAxiom φ) :
    Derivable (@KAxiom Atom) φ :=
  Derivable_of_axiom_derivable (fun _ hax => ikAxiom_derivable_in_K hax) h

/-! ## Rung Bridge: `IT → T` -/

/-- `IT`'s `tDia` (`φ → ◇φ`) is **derivable** in classical `T`: `modalT` at `¬φ` gives
`□¬φ → ¬φ`; `flip` gives `φ → ¬□¬φ`; compose with `diamondDualityBack` to reach `φ → ◇φ`. -/
theorem t_derivable_of_it_tDia {φ : Proposition Atom} :
    Derivable (@TAxiom Atom) (φ.imp (◇φ)) := by
  have modalTNeg := HasAxiomT.T (S := Modal.HilbertT) (φ := φ.imp Proposition.bot)
  have flipped := ModusPonens.mp
    (Cslib.Logic.Theorems.Combinators.flip (S := Modal.HilbertT)) modalTNeg
  have back := HasAxiomDiamondDualityBack.diamondDualityBack (S := Modal.HilbertT) (φ := φ)
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans flipped back
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- Every `ITModalAxiom` instance is `Derivable` in classical `T`: the 14 `IK`-inherited
constructors lift via `Derivable_mono (fun _ => KAxiom_implies_TAxiom)` composed with
`ikAxiom_derivable_in_K`; `tBox` is a bare `SchemaUnion tTags` witness (`TAxiom` is now
`abbrev TAxiom := SchemaUnion tTags`); `tDia` is `t_derivable_of_it_tDia`. -/
theorem itAxiom_derivable_in_T {φ : Proposition Atom} (h : ITModalAxiom φ) :
    Derivable (@TAxiom Atom) φ :=
  match h with
  | .implyK _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_implyK
  | .implyS _ _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_implyS
  | .efq _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_efq
  | .andI _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_andI
  | .andE1 _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_andE1
  | .andE2 _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_andE2
  | .orI1 _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_orI1
  | .orI2 _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_orI2
  | .orE _ _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_orE
  | .k _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_k
  | .kdia _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_kdia
  | .cd _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_cd
  | .idb _ _ => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_idb
  | .dbot => Derivable_mono (fun _ => KAxiom_implies_TAxiom) k_derivable_of_ik_dbot
  | .tBox φ => ⟨.ax [] _ ⟨.modalT, by decide, φ, rfl⟩⟩
  | .tDia _ => t_derivable_of_it_tDia

/-- **The `IT → T` bridge**: every `IT`-derivable formula is `T`-derivable. -/
theorem itDerivable_implies_tDerivable {φ : Proposition Atom} (h : Derivable ITModalAxiom φ) :
    Derivable (@TAxiom Atom) φ :=
  Derivable_of_axiom_derivable (fun _ hax => itAxiom_derivable_in_T hax) h

/-! ## Rung Bridge: `IS4 → S4` -/

/-- `¬◇X → □¬X` in classical `S4` (same construction as `k_dualNeg`, instantiated at
`S := Modal.HilbertS4`). -/
theorem s4_dualNeg {X : Proposition Atom} :
    Derivable (@S4Axiom Atom)
      (((◇X).imp Proposition.bot).imp (Proposition.box (X.imp Proposition.bot))) := by
  have back := HasAxiomDiamondDualityBack.diamondDualityBack (S := Modal.HilbertS4) (φ := X)
  have contra := Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    (S := Modal.HilbertS4) back
  have dne := @Cslib.Logic.Theorems.Propositional.Core.double_negation
    (Proposition Atom) _ _ Modal.HilbertS4 _ _ (Proposition.box (X.imp Proposition.bot))
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans contra dne
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- `□¬X → ¬◇X` in classical `S4` (converse of `s4_dualNeg`): from `dni` composed with
the contraposition of `diamondDualityFwd`. -/
theorem s4_boxNegToNotDia {X : Proposition Atom} :
    Derivable (@S4Axiom Atom)
      ((Proposition.box (X.imp Proposition.bot)).imp ((◇X).imp Proposition.bot)) := by
  have fwd := HasAxiomDiamondDualityFwd.diamondDualityFwd (S := Modal.HilbertS4) (φ := X)
  have contra := Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    (S := Modal.HilbertS4) fwd
  have dni := Cslib.Logic.Theorems.Combinators.dni (S := Modal.HilbertS4) (F := Proposition Atom)
    (Proposition.box (X.imp Proposition.bot))
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans dni contra
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- `IS4`'s `fourDia` (`◇◇φ → ◇φ`) is **derivable** in classical `S4`, proved via its
contrapositive plus `rcp`:

1. `dualNegPhi := s4_dualNeg φ : ¬◇φ → □¬φ`.
2. `four := HasAxiom4.four (φ := ¬φ) : □¬φ → □□¬φ`.
3. `boxMono4 : □□¬φ → □¬◇φ`, necessitating `s4_boxNegToNotDia φ : □¬φ → ¬◇φ` and applying
   `HasAxiomK.K`.
4. `notDiaDia := s4_boxNegToNotDia (X := ◇φ) : □¬◇φ → ¬◇◇φ`.
5. Chain 1–4: `contrapositive := ¬◇φ → ¬◇◇φ`; `rcp contrapositive : ◇◇φ → ◇φ`. -/
theorem s4_derivable_of_is4_fourDia {φ : Proposition Atom} :
    Derivable (@S4Axiom Atom) ((◇(◇φ)).imp (◇φ)) := by
  have dualNegPhi := s4_dualNeg (X := φ)
  obtain ⟨dDN⟩ := dualNegPhi
  have dualNegPhiIS : InferenceSystem.DerivableIn Modal.HilbertS4
      (((◇φ).imp Proposition.bot).imp (Proposition.box (φ.imp Proposition.bot))) := ⟨dDN⟩
  have four := HasAxiom4.four (S := Modal.HilbertS4) (φ := φ.imp Proposition.bot)
  have boxNegToNotDiaPhi := s4_boxNegToNotDia (X := φ)
  obtain ⟨dBNTD⟩ := boxNegToNotDiaPhi
  have boxNegToNotDiaPhiIS : InferenceSystem.DerivableIn Modal.HilbertS4
      ((Proposition.box (φ.imp Proposition.bot)).imp ((◇φ).imp Proposition.bot)) := ⟨dBNTD⟩
  have necBNTD := Necessitation.nec boxNegToNotDiaPhiIS
  have kBNTD := HasAxiomK.K (S := Modal.HilbertS4)
    (φ := Proposition.box (φ.imp Proposition.bot)) (ψ := (◇φ).imp Proposition.bot)
  have boxMono4 := ModusPonens.mp kBNTD necBNTD
  have chain1 := Cslib.Logic.Theorems.Combinators.imp_trans four boxMono4
  have notDiaDia := s4_boxNegToNotDia (X := ◇φ)
  obtain ⟨dND⟩ := notDiaDia
  have notDiaDiaIS : InferenceSystem.DerivableIn Modal.HilbertS4
      ((Proposition.box ((◇φ).imp Proposition.bot)).imp ((◇(◇φ)).imp Proposition.bot)) := ⟨dND⟩
  have chain2 := Cslib.Logic.Theorems.Combinators.imp_trans chain1 notDiaDiaIS
  have contrapositive := Cslib.Logic.Theorems.Combinators.imp_trans dualNegPhiIS chain2
  have goal := @Cslib.Logic.Theorems.Propositional.Core.rcp
    (Proposition Atom) _ _ Modal.HilbertS4 _ _
    (φ := ◇φ) (ψ := ◇(◇φ)) contrapositive
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- Every `IS4ModalAxiom` instance is `Derivable` in classical `S4`: the 16 `IT`-inherited
constructors lift via `Derivable_mono (fun _ => TAxiom_implies_S4Axiom)` composed with
`itAxiom_derivable_in_T`; `fourBox` is a bare `SchemaUnion s4Tags` witness (`S4Axiom` is
now `abbrev S4Axiom := SchemaUnion s4Tags`); `fourDia` is `s4_derivable_of_is4_fourDia`. -/
theorem is4Axiom_derivable_in_S4 {φ : Proposition Atom} (h : IS4ModalAxiom φ) :
    Derivable (@S4Axiom Atom) φ :=
  match h with
  | .implyK _ _ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.implyK _ _))
  | .implyS _ _ _ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.implyS _ _ _))
  | .efq _ => Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.efq _))
  | .andI _ _ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.andI _ _))
  | .andE1 _ _ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.andE1 _ _))
  | .andE2 _ _ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.andE2 _ _))
  | .orI1 _ _ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.orI1 _ _))
  | .orI2 _ _ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.orI2 _ _))
  | .orE _ _ _ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.orE _ _ _))
  | .k _ _ => Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.k _ _))
  | .kdia _ _ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.kdia _ _))
  | .cd _ _ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.cd _ _))
  | .idb _ _ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.idb _ _))
  | .dbot => Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T .dbot)
  | .tBox φ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.tBox φ))
  | .tDia φ =>
      Derivable_mono (fun _ => TAxiom_implies_S4Axiom) (itAxiom_derivable_in_T (.tDia φ))
  | .fourBox φ => ⟨.ax [] _ ⟨.modalFour, by decide, φ, rfl⟩⟩
  | .fourDia _ => s4_derivable_of_is4_fourDia

/-- **The `IS4 → S4` bridge**: every `IS4`-derivable formula is `S4`-derivable. -/
theorem is4Derivable_implies_s4Derivable {φ : Proposition Atom} (h : Derivable IS4ModalAxiom φ) :
    Derivable (@S4Axiom Atom) φ :=
  Derivable_of_axiom_derivable (fun _ hax => is4Axiom_derivable_in_S4 hax) h

/-! ## Rung Bridge: `IS5 → S5` -/

/-- `□¬X → ¬◇X` in classical `S5` (same construction as `k_diaNegToNotBox`'s converse /
`s4_boxNegToNotDia`, instantiated at `S := Modal.HilbertS5`, `Axioms := S5Axiom`). -/
theorem s5_boxNegToNotDia {X : Proposition Atom} :
    Derivable (@S5Axiom Atom)
      ((Proposition.box (X.imp Proposition.bot)).imp ((◇X).imp Proposition.bot)) := by
  have fwd := HasAxiomDiamondDualityFwd.diamondDualityFwd (S := Modal.HilbertS5) (φ := X)
  have contra := Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    (S := Modal.HilbertS5) fwd
  have dni := Cslib.Logic.Theorems.Combinators.dni (S := Modal.HilbertS5) (F := Proposition Atom)
    (Proposition.box (X.imp Proposition.bot))
  have goal := Cslib.Logic.Theorems.Combinators.imp_trans dni contra
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- `IS5`'s `bDia` (`◇□φ → φ`) is **derivable** in classical `S5`, proved via its
contrapositive plus `rcp`:

1. `boxMonoDni : □φ → □¬¬φ` (necessitated `dni`, K-distributed); `innerFix := contraposition
   boxMonoDni : ¬□¬¬φ → ¬□φ`.
2. `boxMonoInnerFix : □¬□¬¬φ → □¬□φ` (necessitated `innerFix`, K-distributed).
3. `bNegPhi := HasAxiomB.B (φ := ¬φ) : ¬φ → □¬□¬¬φ` (symmetry axiom `B` at `¬φ`).
4. `chain := imp_trans bNegPhi boxMonoInnerFix : ¬φ → □¬□φ`.
5. `notDiaBoxPhi := s5_boxNegToNotDia (X := □φ) : □¬□φ → ¬◇□φ`.
6. `contrapositive := imp_trans chain notDiaBoxPhi : ¬φ → ¬◇□φ`; `rcp contrapositive :
   ◇□φ → φ`, i.e. the goal. -/
theorem s5_derivable_of_is5_bDia {φ : Proposition Atom} :
    Derivable (@S5Axiom Atom) ((◇(Proposition.box φ)).imp φ) := by
  have dniPhi := Cslib.Logic.Theorems.Combinators.dni (S := Modal.HilbertS5)
    (F := Proposition Atom) φ
  have necDni := Necessitation.nec dniPhi
  have kDni := HasAxiomK.K (S := Modal.HilbertS5) (φ := φ)
    (ψ := (φ.imp Proposition.bot).imp Proposition.bot)
  have boxMonoDni := ModusPonens.mp kDni necDni
  have innerFix := Cslib.Logic.Theorems.Propositional.Connectives.contraposition
    (S := Modal.HilbertS5) boxMonoDni
  have necInnerFix := Necessitation.nec innerFix
  have kInnerFix := HasAxiomK.K (S := Modal.HilbertS5)
    (φ := (Proposition.box ((φ.imp Proposition.bot).imp Proposition.bot)).imp Proposition.bot)
    (ψ := (Proposition.box φ).imp Proposition.bot)
  have boxMonoInnerFix := ModusPonens.mp kInnerFix necInnerFix
  have bNegPhi := HasAxiomB.B (S := Modal.HilbertS5) (φ := φ.imp Proposition.bot)
  have chain := Cslib.Logic.Theorems.Combinators.imp_trans bNegPhi boxMonoInnerFix
  have notDiaBoxPhi := s5_boxNegToNotDia (X := Proposition.box φ)
  obtain ⟨dNDBP⟩ := notDiaBoxPhi
  have notDiaBoxPhiIS : InferenceSystem.DerivableIn Modal.HilbertS5
      ((Proposition.box ((Proposition.box φ).imp Proposition.bot)).imp
        ((◇(Proposition.box φ)).imp Proposition.bot)) := ⟨dNDBP⟩
  have contrapositive := Cslib.Logic.Theorems.Combinators.imp_trans chain notDiaBoxPhiIS
  have goal := @Cslib.Logic.Theorems.Propositional.Core.rcp
    (Proposition Atom) _ _ Modal.HilbertS5 _ _
    (φ := φ) (ψ := ◇(Proposition.box φ)) contrapositive
  obtain ⟨d⟩ := goal
  exact ⟨d⟩

/-- Every `IS5ModalAxiom` instance is `Derivable` in classical `S5` (`S5Axiom`): the 18
`IS4`-inherited constructors lift via `Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom)`
composed with `is4Axiom_derivable_in_S4`; `bBox` is `box_mono (diamondDualityBack φ)` composed
with the literal `modalB` axiom; `bDia` is `s5_derivable_of_is5_bDia`. -/
theorem is5Axiom_derivable_in_S5 {φ : Proposition Atom} (h : IS5ModalAxiom φ) :
    Derivable (@S5Axiom Atom) φ :=
  match h with
  | .implyK _ _ =>
      Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom) (is4Axiom_derivable_in_S4 (.implyK _ _))
  | .implyS _ _ _ => Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom)
      (is4Axiom_derivable_in_S4 (.implyS _ _ _))
  | .efq _ =>
      Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom) (is4Axiom_derivable_in_S4 (.efq _))
  | .andI _ _ =>
      Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom) (is4Axiom_derivable_in_S4 (.andI _ _))
  | .andE1 _ _ => Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom)
      (is4Axiom_derivable_in_S4 (.andE1 _ _))
  | .andE2 _ _ => Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom)
      (is4Axiom_derivable_in_S4 (.andE2 _ _))
  | .orI1 _ _ =>
      Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom) (is4Axiom_derivable_in_S4 (.orI1 _ _))
  | .orI2 _ _ =>
      Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom) (is4Axiom_derivable_in_S4 (.orI2 _ _))
  | .orE _ _ _ => Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom)
      (is4Axiom_derivable_in_S4 (.orE _ _ _))
  | .k _ _ =>
      Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom) (is4Axiom_derivable_in_S4 (.k _ _))
  | .kdia _ _ =>
      Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom) (is4Axiom_derivable_in_S4 (.kdia _ _))
  | .cd _ _ =>
      Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom) (is4Axiom_derivable_in_S4 (.cd _ _))
  | .idb _ _ =>
      Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom) (is4Axiom_derivable_in_S4 (.idb _ _))
  | .dbot =>
      Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom) (is4Axiom_derivable_in_S4 .dbot)
  | .tBox φ => Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom)
      (is4Axiom_derivable_in_S4 (.tBox φ))
  | .tDia φ => Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom)
      (is4Axiom_derivable_in_S4 (.tDia φ))
  | .fourBox φ => Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom)
      (is4Axiom_derivable_in_S4 (.fourBox φ))
  | .fourDia φ => Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom)
      (is4Axiom_derivable_in_S4 (.fourDia φ))
  | .bBox φ => by
      have back := HasAxiomDiamondDualityBack.diamondDualityBack (S := Modal.HilbertS5) (φ := φ)
      have necBack := Necessitation.nec back
      have kBack := HasAxiomK.K (S := Modal.HilbertS5)
        (φ := (Proposition.box (φ.imp Proposition.bot)).imp Proposition.bot) (ψ := ◇φ)
      have boxMonoBack := ModusPonens.mp kBack necBack
      have bInst := HasAxiomB.B (S := Modal.HilbertS5) (φ := φ)
      have goal := Cslib.Logic.Theorems.Combinators.imp_trans bInst boxMonoBack
      obtain ⟨d⟩ := goal
      exact ⟨d⟩
  | .bDia _ => s5_derivable_of_is5_bDia

/-- **The `IS5 → S5` bridge**: every `IS5`-derivable formula is `S5` (`S5Axiom`)
-derivable. This concludes the full suite of rung bridges (`IK → K`, `IT → T`, `IS4 → S4`,
`IS5 → S5`) established in this module. -/
theorem is5Derivable_implies_s5Derivable {φ : Proposition Atom} (h : Derivable IS5ModalAxiom φ) :
    Derivable (@S5Axiom Atom) φ :=
  Derivable_of_axiom_derivable (fun _ hax => is5Axiom_derivable_in_S5 hax) h

end Cslib.Logic.Modal

end
