/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Logics.Propositional.Tableau.Minimal.Completeness
public meta import Cslib.Logics.Propositional.Tableau.Minimal.Completeness

/-! # `hvalid`-Shape Refutation at the `⊥` Formula Shape

Executable regression witness that `tableau_complete`'s (`Scheme.lean`) `hvalid` premise, with
only the valuation upward-closure premise supplied, is not derivable from `MValid φ` alone. This
is the `minScheme`/`⊥`-formula analogue of `CslibTests/HvalidShapeRefutation.lean`'s defect, one
conjunct later: `MValid` demands upward closure of BOTH the valuation and `bot_forces`, but the
old `hvalid` premise shape only supplied the former.

This file exhibits a concrete `(edges, b, φ)` with `MValid φ` true and the `hvalid` body FALSE,
even though the supplied valuation upward-closure premise holds:

`φ = ⊥ → ((⊥ → ⊥) → ⊥)` — minimally valid, needing only `bot_forces` upward closure
(`phiBotK_valid`).
`edges = [(1, 0)]` — (child, parent), so `0 ≤ 1`.
`b     = [T(⊥)@0]` — no atoms at all, so `intExtractValuation b` is empty and its upward closure
holds vacuously (`val_upward_closed`), while `minBranchBotForces b` is NOT upward closed
(`bot_not_upward_closed`): it holds at world `0` but not at world `1`, breaking `IForces` at
world `0` (`hvalid_body_false`).

This shows the DP-4 goal was not merely hard but unprovable AS STATED for that premise shape —
the fix is a statement-shape change (adding the matching `bot_forces` upward-closure premise to
`hvalid`), landed alongside this file as a permanent regression guard against reintroducing the
old, refuted shape. -/

set_option autoImplicit false

open Cslib.Logic.PL Relation

namespace CslibTests.MvalidBotShapeRefutation

/-- `HasBot.bot` is the `Proposition.bot` constructor. -/
lemma bot_eq : (Cslib.Logic.HasBot.bot : Proposition Nat) = Proposition.bot := rfl

/-- `⊥ → ((⊥ → ⊥) → ⊥)`. -/
def phiBotK : Proposition Nat :=
  Proposition.bot.imp ((Proposition.bot.imp Proposition.bot).imp Proposition.bot)

/-- Edge list with a single edge, child `1` and parent `0`, so `0 ≤ 1`. -/
def edgesCE : IEdges := [(1, 0)]

/-- Branch with only `T(⊥)@0` — no atoms at all. -/
def bCE : IBranch Nat := [⟨.pos, Proposition.bot, 0⟩]

/-- `0 ≤ 1` in the countermodel frame built from `edgesCE`. -/
lemma le_zero_one : @LE.le Nat (intAccessPreorder edgesCE).toLE 0 1 := by
  apply intAccessPreorder_le_of_isAccessible
  decide

/-- The extracted valuation is empty, hence vacuously upward closed. -/
theorem val_upward_closed :
    ∀ {w w' : Nat} (p : Nat),
      @LE.le Nat (intAccessPreorder edgesCE).toLE w w' →
      intExtractValuation bCE w p → intExtractValuation bCE w' p := by
  intro w w' p _hle hval
  simp [intExtractValuation, bCE] at hval

/-- `minBranchBotForces bCE` is NOT upward closed along this frame. -/
theorem bot_not_upward_closed :
    ¬ (∀ {w w' : Nat}, @LE.le Nat (intAccessPreorder edgesCE).toLE w w' →
        minBranchBotForces bCE w → minBranchBotForces bCE w') := by
  intro h
  have h0 : minBranchBotForces bCE 0 := by simp [minBranchBotForces, bCE, bot_eq]
  have h1 : minBranchBotForces bCE 1 := h le_zero_one h0
  simp [minBranchBotForces, bCE, bot_eq] at h1

/-- `phiBotK` is minimally valid. -/
theorem phiBotK_valid : MValid.{0, 0} phiBotK := by
  intro World _inst val bot_forces _vuc buc w w1 hw1 hbot1 w2 hw2 _htop
  exact buc hw2 hbot1

/-- The `hvalid` body as `tableau_complete` used to state it — with ONLY the valuation
upward-closure premise available — is FALSE at this witness, even though `phiBotK` is `MValid`
and the valuation IS upward closed. -/
theorem hvalid_body_false :
    ¬ @IForces Nat Nat (intAccessPreorder edgesCE)
        (intExtractValuation bCE) (minBranchBotForces bCE) 0 phiBotK := by
  intro hf
  have h0 : minBranchBotForces bCE 0 := by simp [minBranchBotForces, bCE, bot_eq]
  have hstep := hf 0 Relation.ReflTransGen.refl h0
  have htop : @IForces Nat Nat (intAccessPreorder edgesCE)
      (intExtractValuation bCE) (minBranchBotForces bCE) 1
      (Proposition.bot.imp Proposition.bot) := fun _ _ hb => hb
  have hbot1 : minBranchBotForces bCE 1 := hstep 1 le_zero_one htop
  simp [minBranchBotForces, bCE, bot_eq] at hbot1

end CslibTests.MvalidBotShapeRefutation
