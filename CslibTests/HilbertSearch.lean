/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public meta import Cslib.Foundations.Logic.Automation.HilbertSearch
public meta import Cslib.Logics.Modal.ProofSystem.Instances
public meta import Cslib.Logics.Propositional.ProofSystem.Instances
public meta import Cslib.Logics.Temporal.ProofSystem.Instances

open Cslib.Logic

/-! # Hilbert Search Tactic Tests

This file tests the `hilbert_search` tactic across multiple proof systems.

## Test Organization

- **Tier 1 (depth 1-3)**: Core propositional/modal axioms and rules, must succeed at default fuel
- **Tier 2 (depth 4-6)**: Deeper derivations, may need higher fuel
- **Negative tests**: Verify fuel exhaustion fails gracefully
- **Tier 3 (must not hang)**: Verify tactic terminates even on unprovable goals
-/

namespace CslibTests.HilbertSearch

/-! ## Tier 1 Tests — Positive (default fuel, propositional)
These must all succeed at the default fuel level (30). -/

/-- Test 1: ImplyK axiom — `⊢ φ → (ψ → φ)` — closes at depth 1 via direct axiom application. -/
example [HasBot F] [HasImp F] [InferenceSystem S F] [MinimalHilbert S (F := F)]
    (a b : F) :
    InferenceSystem.DerivableIn S (HasImp.imp a (HasImp.imp b a)) := by
  hilbert_search

/-- Test 2: Identity rule — `⊢ φ → φ` — closes at depth 1 via `identity` theorem. -/
example [HasBot F] [HasImp F] [InferenceSystem S F] [MinimalHilbert S (F := F)]
    (phi : F) :
    InferenceSystem.DerivableIn S (HasImp.imp phi phi) := by
  hilbert_search

/-- Test 3: Modus ponens from assumptions — closes `⊢ b` from `h1 : ⊢ a → b` and `h2 : ⊢ a`
    via assumption lookup + MP. -/
example [HasBot F] [HasImp F] [InferenceSystem S F] [MinimalHilbert S (F := F)]
    (a b : F)
    (h1 : InferenceSystem.DerivableIn S (HasImp.imp a b))
    (h2 : InferenceSystem.DerivableIn S a) :
    InferenceSystem.DerivableIn S b := by
  hilbert_search

/-- Test 4: Box monotonicity from hypothesis — closes `⊢ □a → □b` from `h : ⊢ a → b`
    via `box_mono` rule at depth 2. -/
example [HasBot F] [HasImp F] [HasBox F] [InferenceSystem S F] [ModalHilbert S (F := F)]
    (a b : F)
    (h : InferenceSystem.DerivableIn S (HasImp.imp a b)) :
    InferenceSystem.DerivableIn S (HasImp.imp (HasBox.box a) (HasBox.box b)) := by
  hilbert_search

/-- Test 5: Necessitation of identity — closes `⊢ □(φ → φ)` via `nec(identity)` at depth 2. -/
example [HasBot F] [HasImp F] [HasBox F] [InferenceSystem S F] [ModalHilbert S (F := F)]
    (a : F) :
    InferenceSystem.DerivableIn S (HasBox.box (HasImp.imp a a)) := by
  hilbert_search

/-- Test 6: EFQ axiom — closes `⊢ ⊥ → φ` at depth 1 via `efq` axiom. -/
example [HasBot F] [HasImp F] [InferenceSystem S F] [IntuitionisticHilbert S (F := F)]
    (phi : F) :
    InferenceSystem.DerivableIn S (HasImp.imp (HasBot.bot : F) phi) := by
  hilbert_search

/-- Test 7: Peirce's law — closes `⊢ ((φ → ψ) → φ) → φ` at depth 1 via `peirce` axiom. -/
example [HasBot F] [HasImp F] [InferenceSystem S F] [ClassicalHilbert S (F := F)]
    (phi psi : F) :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp (HasImp.imp phi psi) phi) phi) := by
  hilbert_search

/-- Test 8: B combinator — closes `⊢ (ψ → χ) → (φ → ψ) → (φ → χ)` via direct
    `b_combinator` theorem application at depth 1. -/
example [HasBot F] [HasImp F] [InferenceSystem S F] [MinimalHilbert S (F := F)]
    (phi psi chi : F) :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp psi chi)
        (HasImp.imp (HasImp.imp phi psi)
          (HasImp.imp phi chi))) := by
  hilbert_search

/-- Test 9: ImplyS axiom — closes the S-combinator formula `⊢ (φ → ψ → χ) → (φ → ψ) → φ → χ`
    at depth 1 via `implyS` axiom. -/
example [HasBot F] [HasImp F] [InferenceSystem S F] [MinimalHilbert S (F := F)]
    (phi psi chi : F) :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasImp.imp phi (HasImp.imp psi chi))
        (HasImp.imp (HasImp.imp phi psi)
          (HasImp.imp phi chi))) := by
  hilbert_search

/-- Test 10: Axiom K (modal distribution) — closes `⊢ □(φ → ψ) → □φ → □ψ` at depth 1. -/
example [HasBot F] [HasImp F] [HasBox F] [InferenceSystem S F] [ModalHilbert S (F := F)]
    (phi psi : F) :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasBox.box (HasImp.imp phi psi))
        (HasImp.imp (HasBox.box phi) (HasBox.box psi))) := by
  hilbert_search

/-- Test 11: Axiom T (reflexivity) — closes `⊢ □φ → φ` at depth 1. -/
example [HasBot F] [HasImp F] [HasBox F] [InferenceSystem S F] [ModalTHilbert S (F := F)]
    (phi : F) :
    InferenceSystem.DerivableIn S (HasImp.imp (HasBox.box phi) phi) := by
  hilbert_search

/-- Test 12: Axiom 4 (transitivity) — closes `⊢ □φ → □□φ` at depth 1. -/
example [HasBot F] [HasImp F] [HasBox F] [InferenceSystem S F] [ModalS4Hilbert S (F := F)]
    (phi : F) :
    InferenceSystem.DerivableIn S
      (HasImp.imp (HasBox.box phi) (HasBox.box (HasBox.box phi))) := by
  hilbert_search

/-! ## Tier 1 Tests — Positive (propositional system with tag type) -/

/-- Test 13: Identity on classical propositional logic. -/
example (a : Cslib.Logic.PL.Proposition Nat) :
    InferenceSystem.DerivableIn Propositional.HilbertCl
      (HasImp.imp a a) := by
  hilbert_search

/-- Test 14: MP on classical propositional logic from hypotheses. -/
example (a b : Cslib.Logic.PL.Proposition Nat)
    (h1 : InferenceSystem.DerivableIn Propositional.HilbertCl (HasImp.imp a b))
    (h2 : InferenceSystem.DerivableIn Propositional.HilbertCl a) :
    InferenceSystem.DerivableIn Propositional.HilbertCl b := by
  hilbert_search

/-! ## Tier 2 Tests — Deeper Derivations -/

/-- Test 15: Chaining two MP steps from hypotheses. -/
example [HasBot F] [HasImp F] [InferenceSystem S F] [MinimalHilbert S (F := F)]
    (a b c : F)
    (h1 : InferenceSystem.DerivableIn S (HasImp.imp a b))
    (h2 : InferenceSystem.DerivableIn S (HasImp.imp b c))
    (h3 : InferenceSystem.DerivableIn S a) :
    InferenceSystem.DerivableIn S c := by
  hilbert_search

/-- Test 16: Transitivity of implication (`imp_trans`) using theorem application. -/
example [HasBot F] [HasImp F] [InferenceSystem S F] [MinimalHilbert S (F := F)]
    (a b c : F)
    (h1 : InferenceSystem.DerivableIn S (HasImp.imp a b))
    (h2 : InferenceSystem.DerivableIn S (HasImp.imp b c)) :
    InferenceSystem.DerivableIn S (HasImp.imp a c) := by
  hilbert_search

/-- Test 17: Nested box via nec + nec. From `h : ⊢ φ`, derive `⊢ □□φ` using
    necessitation twice. -/
example [HasBot F] [HasImp F] [HasBox F] [InferenceSystem S F] [ModalHilbert S (F := F)]
    (phi : F) (h : InferenceSystem.DerivableIn S phi) :
    InferenceSystem.DerivableIn S (HasBox.box (HasBox.box phi)) := by
  hilbert_search

/-! ## Negative Tests — Verify graceful failure at low fuel -/

/-- Negative test 1: `hilbert_search 0` always fails (zero fuel).
The error message includes "hilbert_search failed". -/
example [HasBot F] [HasImp F] [InferenceSystem S F] [MinimalHilbert S (F := F)]
    (phi : F) :
    InferenceSystem.DerivableIn S (HasImp.imp phi phi) := by
  fail_if_success (hilbert_search 0)
  exact (Theorems.Combinators.identity phi)

/-- Negative test 2: `hilbert_search 1` on a depth-3 goal (□□(φ→φ)) fails gracefully
    and terminates (does not hang). -/
example [HasBot F] [HasImp F] [HasBox F] [InferenceSystem S F] [ModalHilbert S (F := F)]
    (phi : F) :
    InferenceSystem.DerivableIn S (HasBox.box (HasBox.box (HasImp.imp phi phi))) := by
  fail_if_success (hilbert_search 1)
  exact Necessitation.nec (Necessitation.nec (Theorems.Combinators.identity phi))

/-! ## Temporal Tests — Temporal BX System

These tests verify that the tactic works on `Temporal.HilbertBX` proof goals
using the temporal axiom instances. -/

/-- Temporal Test 1: Serial future axiom — `⊢ ⊤ → F(⊤)` — depth 1 via direct axiom. -/
example :
    InferenceSystem.DerivableIn Temporal.HilbertBX
      (HasImp.imp
        (HasImp.imp (HasBot.bot : Cslib.Logic.Temporal.Formula Nat) HasBot.bot)
        (HasUntil.untl
          (HasImp.imp (HasBot.bot : Cslib.Logic.Temporal.Formula Nat) HasBot.bot)
          (HasImp.imp (HasBot.bot : Cslib.Logic.Temporal.Formula Nat) HasBot.bot))) := by
  hilbert_search

/-- Temporal Test 2: Identity holds in temporal system. -/
example (phi : Cslib.Logic.Temporal.Formula Nat) :
    InferenceSystem.DerivableIn Temporal.HilbertBX
      (HasImp.imp phi phi) := by
  hilbert_search

/-- Temporal Test 3: MP from hypotheses in temporal system. -/
example (phi psi : Cslib.Logic.Temporal.Formula Nat)
    (h1 : InferenceSystem.DerivableIn Temporal.HilbertBX (HasImp.imp phi psi))
    (h2 : InferenceSystem.DerivableIn Temporal.HilbertBX phi) :
    InferenceSystem.DerivableIn Temporal.HilbertBX psi := by
  hilbert_search

/-- Temporal Test 4: Temporal necessitation (G-nec) produces a derivability in the
    temporal system. From `⊢ φ`, the tactic should derive `⊢ G(φ)` using
    temporal necessitation. -/
example (phi : Cslib.Logic.Temporal.Formula Nat)
    (h : InferenceSystem.DerivableIn Temporal.HilbertBX phi) :
    InferenceSystem.DerivableIn Temporal.HilbertBX
      (HasImp.imp
        (HasUntil.untl
          (HasImp.imp (HasBot.bot : Cslib.Logic.Temporal.Formula Nat) HasBot.bot)
          (HasImp.imp phi HasBot.bot))
        HasBot.bot) := by
  hilbert_search

end CslibTests.HilbertSearch
