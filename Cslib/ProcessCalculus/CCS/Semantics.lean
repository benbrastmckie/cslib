/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Semantics.LTS.Basic
import Cslib.ProcessCalculus.CCS.Basic
import Cslib.Data.FinFun

/-! # Semantics of CCS

## Main definitions
- `CCS.tr`: transition relation for CCS.
- `CCS.lts`: the `LTS` of CCS.

## Implementation notes
We use a `FinFun` for the set of equation that define constants.
This is not really necessary, and could easily be generalised.
-/

variable {Name : Type u} {Constant : Type v} {defs : Constant ⇀ CCS.Process Name Constant}

namespace CCS

open Process

/-- The transition relation for CCS. -/
inductive tr : Process Name Constant → Act Name → Process Name Constant → Prop where
| pre : tr (pre μ p) μ p
| parL : tr p μ p' → tr (par p q) μ (par p' q)
| parR : tr q μ q' → tr (par p q) μ (par p q')
| com : tr p μ p' → tr q μ.co q' → tr (par p q) Act.τ (par p' q')
| choiceL : tr p μ p' → tr (choice p q) μ p'
| choiceR : tr q μ q' → tr (choice p q) μ q'
| res : μ ≠ Act.name a → μ ≠ Act.coname a → tr p μ p' → tr (res a p) μ (res a p')
| const : defs.defined k → defs.apply k = p → tr p μ p' → tr (const k) μ p'

/-- The `LTS` of CCS. -/
def lts : LTS (Process Name Constant) (Act Name) := {
  tr := @CCS.tr Name Constant defs
}

end CCS
