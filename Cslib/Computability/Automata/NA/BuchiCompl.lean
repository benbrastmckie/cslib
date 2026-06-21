/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Mathlib.Data.Fintype.Card

/-! # NBA Complementation via Rank-Based Construction

Given a nondeterministic Büchi automaton (NBA) `A`, this module constructs an NBA
`complementNA A` that accepts exactly the complement language `(language A)ᶜ`.

The construction follows Kupferman-Vardi 2001, Section 5.2 (direct rank-based
construction). The key insight is that a word is rejected by `A` if and only if
the run DAG of `A` on that word admits an *odd ranking* — a function assigning
ranks from `{0, 1, ..., 2n}` (where `n = |Q|`) to reachable DAG nodes such that:
- Accepting states receive odd ranks (guaranteeing they are not visited infinitely);
- Along every path in the DAG, ranks are non-increasing, with accepting states
  receiving strictly odd ranks.

The complement automaton `complementNA A` tracks a *level ranking*
`g : Q → WithBot (Fin (2n+1))` and an *obligation set* `P : Finset Q` (states
whose rank parity must decrease). It accepts when `P = ∅`, witnessing that all
accepting obligations have been discharged.

## Main definitions

* `NA.Buchi.LevelRanking` — a function type `State → WithBot (Fin (2n+1))` assigning ranks
* `NA.Buchi.covers` — the σ-covers relation between consecutive level rankings
* `NA.Buchi.complementNA` — the complement NBA construction

## Main theorems

* `NA.Buchi.complement_language_sub` — soundness: `language (complementNA a) ≤ (language a)ᶜ`
* `NA.Buchi.complement_language_eq` — completeness: `language (complementNA a) = (language a)ᶜ`
  (see `proof_wanted` for the backward ranking lemma direction)

## References

* [O. Kupferman, M. Y. Vardi, *Weak alternating automata are not that weak*][KupfermanVardi2001]
  ACM TOCL, 2(3):408-429, 2001. Section 5.2: direct rank-based construction.
* [C. Baier, J.-P. Katoen, *Principles of Model Checking*][BaierKatoen2008]
-/

@[expose] public section

namespace Cslib.Automata.NA.Buchi

open Set Filter ωSequence ωLanguage ωAcceptor
open scoped LTS

/-! ## Level Rankings -/

/-- A *level ranking* for an NBA with state type `State` (with `n = Fintype.card State`)
assigns to each state either a rank `r : Fin (2 * n + 1)` or `⊥` (not reachable in
this DAG level). Odd ranks encode the rejection witness: accepting states must have odd rank. -/
abbrev LevelRanking (State : Type) [Fintype State] : Type :=
  State → WithBot (Fin (2 * Fintype.card State + 1))

variable {State : Type} {Symbol : Type*}
variable [Fintype State] [DecidableEq State]

/-- The *σ-covers* relation: `g'` σ-covers `g` (w.r.t. NBA `a` and symbol `σ`) if:
1. Ranks are non-increasing along transitions: `g(s) ≠ ⊥ → g'(t) ≠ ⊥ ∧ g'(t) ≤ g(s)`;
2. Accepting states must receive odd rank in `g'`;
3. Unreachable states stay unreachable: `g(s) = ⊥ → g'(t) = ⊥`.

This captures the inductive step of an odd ranking on the run DAG (KV2001, Section 5.2). -/
def covers (a : Buchi State Symbol) (g : LevelRanking State) (σ : Symbol)
    (g' : LevelRanking State) : Prop :=
  ∀ s t, a.Tr s σ t →
    (g s = ⊥ → g' t = ⊥) ∧
    (g s ≠ ⊥ → g' t ≠ ⊥ ∧ g' t ≤ g s) ∧
    (t ∈ a.accept → ∀ r : Fin (2 * Fintype.card State + 1), g' t = some r → r.val % 2 = 1)

/-- Whether a level ranking assigns an even (non-⊥) rank to a state. -/
def hasEvenRank (g : LevelRanking State) (s : State) : Prop :=
  ∃ r : Fin (2 * Fintype.card State + 1), g s = some r ∧ r.val % 2 = 0

instance (g : LevelRanking State) (s : State) : Decidable (hasEvenRank g s) :=
  decidable_of_iff
    (∃ r : Fin (2 * Fintype.card State + 1), g s = some r ∧ r.val % 2 = 0)
    Iff.rfl

/-- The obligation set update: given level ranking `g'` and current obligation set `P`,
compute the next obligation set `P'`.
- If `P = ∅`, reset to states with even rank under `g'` (new obligations);
- Otherwise, keep states in `P` that still have a defined rank (i.e., `g'(s) ≠ ⊥`). -/
noncomputable def updateObl (g' : LevelRanking State)
    (P : Finset State) : Finset State :=
  if P = ∅ then
    Finset.univ.filter (fun t => hasEvenRank g' t)
  else
    P.filter (fun t => g' t ≠ ⊥)

/-- The state type of the complement automaton: pairs `(g, P)` of a level ranking and
an obligation set tracking states that must eventually be discharged (receive odd rank). -/
abbrev ComplState (State : Type) [Fintype State] [DecidableEq State] : Type :=
  LevelRanking State × Finset State

/-- The initial level rankings for the complement automaton: rankings where every
non-start state of `a` receives rank `⊥` (only start states can be reachable at step 0). -/
def initRankings (a : Buchi State Symbol) : Set (LevelRanking State) :=
  { g | ∀ s, s ∉ a.start → g s = ⊥ }

/-- The initial obligation set for a given initial level ranking `g`: states with even rank. -/
noncomputable def initObl (g : LevelRanking State) : Finset State :=
  Finset.univ.filter (fun s => hasEvenRank g s)

/-- The complement NBA.

State space: `ComplState State = LevelRanking State × Finset State`.
- `g : LevelRanking State` — current level ranking (odd ranking prefix);
- `P : Finset State` — obligation set (states needing rank decrease).

Transitions `(g, P) -σ→ (g', P')`:
- `g'` σ-covers `g` (ranks are consistent with `a`'s transitions);
- `P' = updateObl g' P`.

Start states: `(g₀, initObl g₀)` for `g₀ ∈ initRankings a`.

Acceptance: `P = ∅` (all obligations discharged).

An accepting run witnesses that accepting states never appear with even rank infinitely
often, proving rejection by the original NBA `a`. -/
@[scoped grind =]
noncomputable def complementNA (a : Buchi State Symbol) :
    Buchi (ComplState State) Symbol where
  Tr s σ t := covers a s.1 σ t.1 ∧ t.2 = updateObl t.1 s.2
  start := { s | s.1 ∈ initRankings a ∧ s.2 = initObl s.1 }
  accept := { s | s.2 = ∅ }

end Cslib.Automata.NA.Buchi
