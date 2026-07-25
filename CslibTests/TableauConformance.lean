/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Logics.Temporal.Tableau.Saturation
import Cslib.Logics.Temporal.Syntax.Formula
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
import Cslib.Logics.Propositional.Defs
public meta import Cslib.Logics.Temporal.Tableau.Saturation
public meta import Cslib.Logics.Temporal.Syntax.Formula
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
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
  `ModalFrameSeparation.lean` idiom) are unavailable here because the completeness theorems
  the driver would need do not exist yet for either calculus.
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

Every row's expected verdict and every row currently marked as a defect is transcribed from
Finding 0 of the task's research report. Finding 0's summary table groups some rows into
`k`-indexed families (`𝐆p → 𝐅^k p` for `k = 1..5`; `𝐅^k p → 𝐅^k p` for `k = 0..6`); expanding
those families into individually-asserted formulas — required so Phase 7's `k = 4` cut is its
own detector, not folded into a family average — yields **43** individually-executed rows here
at Phase 1 landing time (27 green, 16 red), rather than the plan's rounded "44 rows / 32 green /
12 red" summary figures, which count some multi-formula families as a single row. The set of
*which* formulas were originally red is unaffected by this counting difference; only the row
arithmetic differs. Rows are repaired by the implementation phases named inline below as they
land: Phase 2 flipped the 3 propositional rows (30 green / 13 red as of Phase 2); Phase 6/7
flipped 12 of the remaining 13 temporal rows (42 green / 1 red as of this reconciliation). The
one still-red row (`𝐇p → 𝐇𝐇p`, past transitivity) is a newly discovered defect, independent of
the Deliverable 3/4 cap-removal work Phase 7 was scoped to, and is documented inline at its row
below rather than silently left under a stale "flips in Phase 7" annotation. Row-by-row
annotations record which phase flipped (or will flip) each row; Phase 8 removes those
annotations once the whole corpus is green, converting this file into a pure regression guard.
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

24 rows: originally 11 green, 13 red (defects named in the task's six deliverables plus the
Finding 2b/2c seventh defect). As of this reconciliation: 23 green, 1 red (`𝐇p → 𝐇𝐇p`, a newly
discovered past-transitivity defect in `allPastPosAt`, out of scope for this dispatch — see its
row below). -/

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

-- Future seriality, Deliverable 2(i): CLOSED (flipped in Phase 6).
-- validDiscrete-only per D1 (not Temporal.valid): sound because branchSat mandates
-- NoMaxOrder/NoMinOrder.
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 tp → 𝐅 tp))

-- Past seriality, Deliverable 2(i): CLOSED (flipped in Phase 6).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐇 tp → 𝐏 tp))

-- Future transitivity, Deliverable 2(iii): CLOSED (flipped in Phase 6, via someFuturePos plus
-- transitive TimeOrdering.ancestorTimes propagation in allFuturePosAt).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 tp → 𝐆 (𝐆 tp)))

-- DEFECT (past transitivity): mathematically valid (dual of Gp → GGp) but still OPEN, a newly
-- discovered defect distinct from the Branch.lean/SignedFormula.lean ancestorTimes bug fixed
-- alongside this reconciliation. Root cause: Rules.lean's allPastPosAt reuses the future-only
-- TimeOrdering.ancestorTimes to decide T(Hφ) propagation, checking whether `t` is in `t_anc`'s
-- forward light-cone instead of whether `t_anc` is in `t`'s forward light-cone (the direction
-- needed to propagate a past-obligation backward). Out of this dispatch's authorized scope
-- (Branch.lean/SignedFormula.lean only); raised as a new blocker, not fixed here.
/-- info: "OPEN" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐇 tp → 𝐇 (𝐇 tp)))

-- Conversion, Deliverable 2(iii): CLOSED (flipped in Phase 6).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (tp → 𝐆 (𝐏 tp)))

-- Conversion, Deliverable 2(iii): CLOSED (flipped in Phase 6).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (tp → 𝐇 (𝐅 tp)))

-- K for G, Finding 2b: CLOSED (flipped by the Phase 7 dedup wiring, commit 53eeabf2).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (𝐆 (¬ tp) → (𝐆 tp → 𝐆 (⊥ : Formula Nat))))

-- G/F duality, Finding 2b: CLOSED (flipped by the Phase 7 dedup wiring, commit 53eeabf2).
/-- info: "CLOSED" -/
#guard_msgs in
#eval temporalVerdict (temporalTableau (¬ (𝐆 tp) → 𝐅 (¬ tp)))

-- Family (Deliverables 3+4, dedup-based termination): Gp → F^k p for k = 1..5, all CLOSED.
-- Realized via the isTemporallyBlocked dedup gate (Rules.lean:365,391, commit 53eeabf2) plus
-- the Branch.lean ancestorTimes fix (undirected-traversal bug, commit 8b3e8df7) that unblocked
-- k >= 2; k = 1 duplicates the seriality row above by construction (𝐅^1 = 𝐅) and is kept for
-- the family's own record.
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

19 rows, all green as of Phase 2: 14 closed (11 originally green + 3 flipped by the Fitting
`T(→)` split, Deliverable 6) + 5 IPC-invalid open rows. -/

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

-- FIXED in Phase 2 (Deliverable 6: T(→) branching rule added to intApplyRuleFull).
-- IPC-valid: from b, weakening gives a→b, hence a→c, with a gives c.
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (((ia → ib) → (ia → ic)) → (ia → (ib → ic))))

-- FIXED in Phase 2 (Deliverable 6). IPC-valid: textbook ¬¬¬a → ¬a.
/-- info: "CLOSED" -/
#guard_msgs in
#eval intVerdict (intuitionisticTableau (¬ (¬ (¬ ia)) → ¬ ia))

-- FIXED in Phase 2 (Deliverable 6).
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

end PropositionalCorpus

end CslibTests.TableauConformance
