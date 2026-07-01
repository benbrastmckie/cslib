/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Init
public import Cslib.Logics.Temporal.Metalogic.PropositionalHelpers
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

/-! # Temporal Theorems

Barrel import for temporal theorem modules:
- `TemporalDerived`: 20+ derived theorems (G/H distribution, contraposition, etc.)
- `FrameConditions`: Frame condition typeclasses (Linear, Serial, Dense, Discrete)

## Classical Equivalences (task 180, Phase 9)

`allFuture` (`𝐆`) and `allPast` (`𝐇`) were promoted from derived abbreviations to primitive
`Formula` constructors (task 180) so that intuitionistic temporal logics — where `𝐆φ` is
strictly stronger than `¬𝐅¬φ` — are expressible ([Boudou2017]). The classical duality
`𝐆φ ↔ ¬𝐅¬φ` / `𝐇φ ↔ ¬𝐏¬φ` therefore can no longer be definitional; it is packaged below as a
theorem, assembled from the two-directional bridge axioms
(`Axiom.allFuture_to_classic`/`Axiom.classic_to_allFuture`, and the past duals) that were
proved *sound* in `Metalogic.Soundness`/`Metalogic.DenseSoundness`.

**Honesty caveat (D3):** this equivalence is a theorem *about* `HilbertBX`, built by packaging
two axioms — it is not *derived* from the propositional/mono axioms of the system. Attempting
such a derivation is known to be impossible once `𝐆`/`𝐇` are primitive (F2): the bridge from
`𝐆φ` to `¬𝐅¬φ` is genuinely classical (uses Peirce's law in `classic_to_allFuture`), and no
combination of the mono/enrichment/connect axioms recovers it without assuming the bridge
itself. Soundness of the bridge axioms (proved in `Soundness.lean`/`DenseSoundness.lean`) is
therefore an *assertion*, not a *proof*, of conservativity over the classical fragment: we
trust the semantic soundness argument, we do not exhibit a syntactic derivation from a smaller
axiom set.
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic

open Cslib.Logic.Temporal

variable {Atom : Type*}

noncomputable section

/-- Classical duality for `allFuture` (`𝐆`): `𝐆φ ↔ ¬𝐅¬φ`.

Packaged from the two bridge axioms `Axiom.allFuture_to_classic` (`𝐆φ → ¬𝐅¬φ`, holds
constructively) and `Axiom.classic_to_allFuture` (`¬𝐅¬φ → 𝐆φ`, requires Peirce's law).

**D3 honesty caveat:** this `Iff` is a thin wrapper around the two axioms, not a derivation
from the propositional/mono axiom fragment — see the module docstring. -/
def allFuture_iff_neg_someFuture_neg (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.allFuture ↔ ¬𝐅¬φ) :=
  let d_fwd : DerivationTree FrameClass.Base [] (φ.allFuture.imp (¬𝐅¬φ)) :=
    DerivationTree.axiom [] _ (Axiom.allFuture_to_classic φ) trivial
  let d_bwd : DerivationTree FrameClass.Base [] ((¬𝐅¬φ).imp φ.allFuture) :=
    DerivationTree.axiom [] _ (Axiom.classic_to_allFuture φ) trivial
  let d_pair := pairing (φ.allFuture.imp (¬𝐅¬φ)) ((¬𝐅¬φ).imp φ.allFuture)
  DerivationTree.modus_ponens [] _ _
    (DerivationTree.modus_ponens [] _ _ d_pair d_fwd) d_bwd

/-- Classical duality for `allPast` (`𝐇`): `𝐇φ ↔ ¬𝐏¬φ`. Past dual of
`allFuture_iff_neg_someFuture_neg`; see its docstring for the D3 honesty caveat. -/
def allPast_iff_neg_somePast_neg (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.allPast ↔ ¬𝐏¬φ) :=
  let d_fwd : DerivationTree FrameClass.Base [] (φ.allPast.imp (¬𝐏¬φ)) :=
    DerivationTree.axiom [] _ (Axiom.allPast_to_classic φ) trivial
  let d_bwd : DerivationTree FrameClass.Base [] ((¬𝐏¬φ).imp φ.allPast) :=
    DerivationTree.axiom [] _ (Axiom.classic_to_allPast φ) trivial
  let d_pair := pairing (φ.allPast.imp (¬𝐏¬φ)) ((¬𝐏¬φ).imp φ.allPast)
  DerivationTree.modus_ponens [] _ _
    (DerivationTree.modus_ponens [] _ _ d_pair d_fwd) d_bwd

end -- noncomputable section

end Cslib.Logic.Temporal.Metalogic

