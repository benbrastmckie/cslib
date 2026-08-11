/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Logics.Temporal.Tableau.Saturation
import Cslib.Logics.Temporal.Syntax.Formula
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
import Cslib.Logics.Propositional.Defs
public meta import Cslib.Logics.Temporal.Tableau.Saturation
public meta import Cslib.Logics.Temporal.Syntax.Formula
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
public meta import Cslib.Logics.Propositional.Defs

/-! # Tableau Calculus Conformance Harness

Executable regression corpus for the temporal (`temporalTableau`) and intuitionistic
propositional (`intuitionisticTableau`) tableau decision procedures. Each row below asserts
the actual decision-procedure verdict against the *semantically* correct verdict via
`#guard_msgs in #eval`, so this file is a live conformance check, not a build-time-only
guarantee: a tableau calculus can be sorry-free and `lake build`-green while still deciding
the wrong verdict on a textbook-valid formula, because rule-set incompleteness is invisible to
the type checker.

## Mechanism (why `#eval`, not `decide`/`rfl`/proof terms)

- `decide`, `native_decide`, and `rfl` **stall on `WellFounded.fix`**: both
  `temporalExpandBranches` and `intExpandBranches` compile through nested `let rec`s that do
  not reduce in the kernel (see `CslibTests/ModalFrameSeparation.lean`'s header for the
  identical failure mode on the modal tableau driver). Proof-term assertions (the
  `ModalFrameSeparation.lean` idiom) are unavailable for the temporal driver because the
  completeness theorem it would need (`temporalTableau_complete`) does not exist yet — it
  remains a blocked obligation (`Temporal/Tableau/Completeness.lean:122`). For the
  intuitionistic driver the completeness theorem now exists and is sorry-free
  (`intuitionisticTableau_complete`, `intuitionisticTableau_decides`), but the kernel-reduction
  stall above is independent of theorem availability and applies to both rows regardless, so
  `#eval` remains the mechanism here too.
- `#eval` **does** reduce (it uses the compiler, not the kernel), but only works from
  `CslibTests/`, not from inside `Cslib/Logics/.../Tableau/` itself.
- The header above needs **both** `import X` and `public meta import X` for the same module:
  without the plain form, referencing a constructor (e.g. `Formula.atom`) fails with
  `may not access declaration ... imported as 'meta'`; without the `meta` form, referencing
  `temporalTableau`/`intuitionisticTableau` themselves fails with `... is not accessible here`.
- `TemporalTableauResult` and `IntTableauResult` derive neither `Repr` nor `BEq`, so a plain
  `#guard` (or `#eval` compared for equality) is not usable. Each result is rendered through a
  `String`-valued verdict adapter (`temporalVerdict`/`intVerdict` below, defined here and not
  in `Cslib/`, since they exist only to make assertions legible) and asserted via
  `#guard_msgs in #eval`, the idiom already used elsewhere in `CslibTests/`
  (`LTS.lean`, `Reduction.lean`, `HasFresh.lean`).

## Validity target (D1)

`temporalTableau` decides `validDiscrete`, **not** `Temporal.valid`: `Temporal.valid`
quantifies only over an arbitrary `[LinearOrder D] [Nontrivial D]`, which need not be serial —
`𝐆p → 𝐅p` is false on a two-point linear order and so is not `Temporal.valid`. The rows below
that depend on seriality (`𝐆p → 𝐅p`, `𝐇p → 𝐏p`, and everything built from `𝐆`/`𝐇` reaching a
witness) are sound only against `branchSat`'s frame class (`NoMaxOrder`/`NoMinOrder`,
`Soundness.lean:95-106`), i.e. against `validDiscrete`. This file exists precisely so that
distinction stays visible rather than being asserted only in a docstring elsewhere.

## Corpus provenance

Every row's expected verdict is justified below by the formula's own mathematical validity —
never by what the decision procedure happens to print. The corpus groups some rows into
`k`-indexed families (`𝐆p → 𝐅^k p` for `k = 1..5`; `𝐅^k p → 𝐅^k p` for `k = 0..6`); expanding
those families into individually-asserted formulas yields **44** individually-executed rows: 24
temporal and 20 propositional.

The propositional corpus's 20th row is the divergence witness `φ0` documented in
`Expansion.lean`'s "Divergence witness: no world bound exists for this calculus" note. Under the
unrepaired calculus, `intExpandBranches` never returned a verdict for `φ0` at all (unbounded
world growth); under the ancestor-directed blocking check that repairs the calculus, `φ0` now
terminates. This row asserts `φ0`'s correct semantic verdict as a termination regression guard —
a future edit that reintroduces unbounded growth on this witness fails this row instead of
hanging silently.

All 44 rows are green: the rule-completeness repairs are complete, and this file is a regression
guard — a future edit that reopens any row here is a real defect, not an expected transitional
state.
-/

namespace CslibTests.TableauConformance

open Cslib.Logic.Temporal.Tableau (TemporalTableauResult temporalTableau)
open Cslib.Logic.PL (IntTableauResult intuitionisticTableau)

/-- `String`-valued verdict adapter for `TemporalTableauResult`: neither `Repr` nor `BEq` is
derived for the result type, so a direct `#guard` is unusable; rendering to `String` makes
`#guard_msgs in #eval` the assertion route. Test-only: intentionally not exposed from
`Cslib/`. -/
def temporalVerdict : TemporalTableauResult Nat → String
  | .closed => "CLOSED"
  | .openBranch _ _ => "OPEN"

/-- `String`-valued verdict adapter for `IntTableauResult`; see `temporalVerdict`. -/
def intVerdict : IntTableauResult Nat → String
  | .closed => "CLOSED"
  | .openBranch _ => "OPEN"

/-! ## Temporal Corpus (`temporalTableau`, `Formula Nat`)

24 rows, all green. -/

section TemporalCorpus

open Cslib.Logic.Temporal

/-- The single temporal atom used throughout this corpus. -/
def tp : Formula Nat := .atom 0

/-- `n`-fold iterated `𝐅` (someFuture), test-local sugar so the `𝐆p → 𝐅^k p` and
`𝐅^k p → 𝐅^k p` families below don't need hand-nested notation. Test-only. -/
def someFutureN : Nat → Formula Nat → Formula Nat
  | 0, φ => φ
  | n + 1, φ => 𝐅 (someFutureN n φ)

-- p → p : CLOSED (valid; reflexivity of →)
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (tp → tp))

-- p : OPEN (an atom alone is not valid)
/-- info: "OPEN" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau tp)

-- Gp → p : OPEN (𝐆 is over *strictly* future times, so this is correctly not valid)
/-- info: "OPEN" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 tp → tp))

-- Fp → Fp : CLOSED
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐅 tp → 𝐅 tp))

-- Future seriality: CLOSED. validDiscrete-only per D1 (not Temporal.valid): sound because
-- branchSat mandates NoMaxOrder/NoMinOrder.
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 tp → 𝐅 tp))

-- Past seriality: CLOSED, symmetric to future seriality (NoMinOrder).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐇 tp → 𝐏 tp))

-- Future transitivity: CLOSED (𝐆φ holds at t entails 𝐆φ holds at every future time of t too).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 tp → 𝐆 (𝐆 tp)))

-- Past transitivity: CLOSED, dual of future transitivity.
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐇 tp → 𝐇 (𝐇 tp)))

-- Conversion (𝐆/𝐏 duality): CLOSED (p now entails Pp at every future time).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (tp → 𝐆 (𝐏 tp)))

-- Conversion (𝐇/𝐅 duality): CLOSED (p now entails Fp at every past time).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (tp → 𝐇 (𝐅 tp)))

-- K for 𝐆: CLOSED (standard K-axiom instance for the future-necessity modality).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 (¬ tp) → (𝐆 tp → 𝐆 (⊥ : Formula Nat))))

-- 𝐆/𝐅 duality: CLOSED (¬𝐆p is equivalent to 𝐅¬p).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (¬ (𝐆 tp) → 𝐅 (¬ tp)))

-- Family: Gp → F^k p for k = 1..5, all CLOSED (seriality composed k times; k = 1 duplicates the
-- seriality row above by construction, 𝐅^1 = 𝐅, and is kept for the family's own record).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 tp → someFutureN 1 tp))

/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 tp → someFutureN 2 tp))

/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 tp → someFutureN 3 tp))

/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 tp → someFutureN 4 tp))

/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 tp → someFutureN 5 tp))

-- Green family: F^k p → F^k p for k = 0..6, always valid by reflexivity, unaffected by any
-- rule-completeness repair. Regression guard that iterated F does not spuriously open.
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (someFutureN 0 tp → someFutureN 0 tp))

/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (someFutureN 1 tp → someFutureN 1 tp))

/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (someFutureN 2 tp → someFutureN 2 tp))

/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (someFutureN 3 tp → someFutureN 3 tp))

/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (someFutureN 4 tp → someFutureN 4 tp))

/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (someFutureN 5 tp → someFutureN 5 tp))

/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (someFutureN 6 tp → someFutureN 6 tp))

end TemporalCorpus

/-! ## Propositional Corpus (`intuitionisticTableau`, `Proposition Nat`)

20 rows, all green: 14 closed (IPC-valid) + 6 open (IPC-invalid). -/

section PropositionalCorpus

open Cslib.Logic.PL

/-- Propositional atoms used throughout this corpus. -/
def ia : Proposition Nat := .atom 0
def ib : Proposition Nat := .atom 1
def ic : Proposition Nat := .atom 2

-- a → a : CLOSED
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (ia → ia))

-- a → (b → a) : CLOSED
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (ia → (ib → ia)))

-- b → (a → b) : CLOSED
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (ib → (ia → ib)))

-- ((a→b) ∧ a) → b : CLOSED
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (((ia → ib) ∧ ia) → ib))

-- ¬(a ∧ ¬a) : CLOSED
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (¬ (ia ∧ ¬ ia)))

-- (a→(b→c)) → ((a→b)→(a→c)) : CLOSED (K)
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau ((ia → (ib → ic)) → ((ia → ib) → (ia → ic))))

-- (¬a ∨ b) → (a → b) : CLOSED
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau ((¬ ia ∨ ib) → (ia → ib)))

-- (a→b) → (¬b → ¬a) : CLOSED
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau ((ia → ib) → (¬ ib → ¬ ia)))

-- (a→c) → ((b→c) → ((a∨b)→c)) : CLOSED
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau ((ia → ic) → ((ib → ic) → ((ia ∨ ib) → ic))))

-- (a ∧ (b∨c)) → ((a∧b) ∨ (a∧c)) : CLOSED
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau ((ia ∧ (ib ∨ ic)) → ((ia ∧ ib) ∨ (ia ∧ ic))))

-- (a→b) → ((b→c)→(a→c)) : CLOSED
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau ((ia → ib) → ((ib → ic) → (ia → ic))))

-- IPC-valid: from b, weakening gives a→b, hence a→c, with a gives c.
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (((ia → ib) → (ia → ic)) → (ia → (ib → ic))))

-- IPC-valid: textbook ¬¬¬a → ¬a.
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (¬ (¬ (¬ ia)) → ¬ ia))

-- IPC-valid: from b, weakening gives a→b, hence c.
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (((ia → ib) → ic) → (ib → ic)))

-- ((a→b)→a) → a : OPEN (Peirce's law, not IPC-valid)
/-- info: "OPEN" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (((ia → ib) → ia) → ia))

-- (a→b) ∨ (b→a) : OPEN (Dummett's linearity axiom, not IPC-valid)
/-- info: "OPEN" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau ((ia → ib) ∨ (ib → ia)))

-- ¬(a∧b) → (¬a ∨ ¬b) : OPEN (De Morgan direction not IPC-valid)
/-- info: "OPEN" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (¬ (ia ∧ ib) → (¬ ia ∨ ¬ ib)))

-- ¬a ∨ ¬¬a : OPEN (weak excluded middle, not IPC-valid)
/-- info: "OPEN" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (¬ ia ∨ ¬ (¬ ia)))

-- (¬a→(b∨c)) → ((¬a→b) ∨ (¬a→c)) : OPEN (Kreisel-Putnam, not IPC-valid)
/-- info: "OPEN" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau ((¬ ia → (ib ∨ ic)) → ((¬ ia → ib) ∨ (¬ ia → ic))))

/-- Additional atoms for the divergence-witness row below, test-only. -/
def id_ : Proposition Nat := .atom 3
def ie : Proposition Nat := .atom 4
def if_ : Proposition Nat := .atom 5
def iu1 : Proposition Nat := .atom 6
def iv1 : Proposition Nat := .atom 7
def iu2 : Proposition Nat := .atom 8
def iv2 : Proposition Nat := .atom 9

-- φ0 = (((a→b)→c) ∧ ((d→e)→f)) → ((u1→v1) ∨ (u2→v2)) : OPEN, not IPC-valid — classically
-- falsified by a=⊤,b=⊥,d=⊤,e=⊥,u1=⊤,v1=⊥,u2=⊤,v2=⊥ (both antecedent conjuncts are vacuously
-- true via a false hypothesis; both consequent disjuncts are false). This is the divergence
-- witness documented in `Expansion.lean`'s "Divergence witness: no world bound exists for this
-- calculus" note: under the unrepaired calculus `intExpandBranches` never returned a verdict for
-- it; under ancestor-directed blocking it now terminates. Termination regression guard.
/-- info: "OPEN" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau
  ((((ia → ib) → ic) ∧ ((id_ → ie) → if_)) → ((iu1 → iv1) ∨ (iu2 → iv2))))

end PropositionalCorpus

end CslibTests.TableauConformance
