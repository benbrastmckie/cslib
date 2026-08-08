/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme

/-! # `hvalid`-Shape Refutation

Executable regression witness that `tableau_complete`'s (`Scheme.lean`) `hvalid` premise is not
derivable from `IValid φ` alone. `tableau_complete` demands

```
hvalid : ∀ (edges : IEdges) (b : IBranch Atom),
  @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ
```

quantified over ARBITRARY `edges` and ARBITRARY `b`, with no hypothesis tying either to an actual
tableau run. `IValid φ` only supplies forcing for UPWARD-CLOSED valuations. This file exhibits a
concrete `(edges, b, φ)` with `IValid φ` true and the `hvalid` body FALSE: `IValid (p → (q → p))`
holds (`phiK_valid`, the `implyK` axiom shape) while the old premise's body fails against a
deliberately non-upward-closed valuation (`hvalid_body_false`), showing the DP-3/DP-4 goals are
not merely hard but unprovable AS STATED for that premise shape.

Witness: `φ = p → (q → p)`,
  `edges = [(1, 0)]`  -- (child, parent), so `0 ≤ 1`
  `b     = [T(atom p)@0, T(atom q)@1]`
so `intExtractValuation b` assigns `p` at world `0` but NOT at world `1`, while `0 ≤ 1` -- a
non-upward-closed valuation, which is exactly what `IValid` is not required to cover. -/

set_option autoImplicit false

open Cslib.Logic.PL Relation

namespace CslibTests.HvalidShapeRefutation

/-- Atoms: `0` is `p`, `1` is `q`. -/
abbrev A := Nat

/-- `p → (q → p)`, the `implyK` axiom shape. -/
def phiK : Proposition A :=
  (Proposition.atom 0).imp ((Proposition.atom 1).imp (Proposition.atom 0))

/-- Edge list with a single edge, child `1` and parent `0`, so `0 ≤ 1`. -/
def edgesCE : IEdges := [(1, 0)]

/-- Branch forcing `p` at world `0` and `q` at world `1` — deliberately NOT upward closed. -/
def bCE : IBranch A := [⟨.pos, .atom 0, 0⟩, ⟨.pos, .atom 1, 1⟩]

/-- `0 ≤ 1` in the countermodel frame built from `edgesCE`. -/
lemma le_zero_one : @LE.le Nat (intAccessPreorder edgesCE).toLE 0 1 := by
  apply intAccessPreorder_le_of_isAccessible
  decide

/-- The extracted valuation forces `p` at world `0`. -/
lemma val_p_at_zero : intExtractValuation bCE 0 0 := by
  simp [intExtractValuation, bCE]

/-- The extracted valuation forces `q` at world `1`. -/
lemma val_q_at_one : intExtractValuation bCE 1 1 := by
  simp [intExtractValuation, bCE]

/-- The extracted valuation does NOT force `p` at world `1`. -/
lemma not_val_p_at_one : ¬ intExtractValuation bCE 1 0 := by
  simp [intExtractValuation, bCE]

/-- **The valuation is not upward closed along the frame** — the premise `IValid` requires. -/
theorem valuation_not_upward_closed :
    ¬ (∀ {w w' : Nat} (p : A),
        @LE.le Nat (intAccessPreorder edgesCE).toLE w w' →
        intExtractValuation bCE w p → intExtractValuation bCE w' p) := by
  intro huc
  exact not_val_p_at_one (huc 0 le_zero_one val_p_at_zero)

/-- **`phiK` is intuitionistically valid.** Standard: weakening/`implyK`. -/
theorem phiK_valid : IValid phiK := by
  intro World _inst val huc w
  simp only [phiK, IForces_imp, IForces_atom]
  intro u _hwu hp v huv _hq
  exact huc 0 huv hp

/-- **The `hvalid` body FAILS at this `(edges, b)`**, even though `phiK` is valid.

This is the decisive fact: `tableau_complete`'s `hvalid` premise, as currently stated
(universally quantified over `edges` and `b`), is NOT a consequence of `IValid φ`. -/
theorem hvalid_body_false :
    ¬ @IForces A Nat (intAccessPreorder edgesCE) (intExtractValuation bCE) intBotForces 0 phiK := by
  simp only [phiK, IForces_imp, IForces_atom]
  intro hf
  -- Instantiate the outer implication at `u = 0` (reflexivity) with `p` forced at `0`,
  -- then the inner one at `v = 1` with `q` forced at `1`.
  have hinner := hf 0 Relation.ReflTransGen.refl val_p_at_zero
  exact not_val_p_at_one (hinner 1 le_zero_one val_q_at_one)

end CslibTests.HvalidShapeRefutation
