/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.OrderIsoNat

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

* `NA.Buchi.covers_neBot_of_neBot` — the covers relation propagates non-`⊥`ness
* `NA.Buchi.covers_rank_le` — the covers relation is rank-non-increasing
* `NA.Buchi.covers_accept_odd` — accepting states get odd rank under covers
* `NA.Buchi.run_rank_defined_all` — any run from a start state keeps all ranks defined
* `NA.Buchi.run_rank_nonincreasing` — ranks along any valid run are non-increasing
* `NA.Buchi.withBot_fin_nonincreasing_stabilizes` — bounded non-increasing sequences stabilize
* `NA.Buchi.run_accept_rank_odd` — stabilized rank of accepting run must be odd
* `NA.Buchi.complement_language_sub` — soundness (stated as `proof_wanted`)
* `NA.Buchi.complement_language_eq` — main theorem (stated as `proof_wanted`)

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
    (t ∈ a.accept → ∀ r : Fin (2 * Fintype.card State + 1), g' t = (r : WithBot _) → r.val % 2 = 1)

/-- Whether a level ranking assigns an even (non-`⊥`) rank to a state. -/
def hasEvenRank (g : LevelRanking State) (s : State) : Prop :=
  ∃ r : Fin (2 * Fintype.card State + 1), g s = (r : WithBot _) ∧ r.val % 2 = 0

/-- Decidability of `hasEvenRank`. -/
instance instDecidableHasEvenRank (g : LevelRanking State) (s : State) :
    Decidable (hasEvenRank g s) :=
  decidable_of_iff
    (∃ r : Fin (2 * Fintype.card State + 1), g s = (r : WithBot _) ∧ r.val % 2 = 0)
    Iff.rfl

/-- The obligation set update: given level ranking `g'` and current obligation set `P`,
compute the next obligation set `P'`.
- If `P = ∅`, reset to states with even rank under `g'` (new obligations);
- Otherwise, keep states in `P` that still have a defined rank (i.e., `g'(s) ≠ ⊥`). -/
noncomputable def updateObl (g' : LevelRanking State) (P : Finset State) : Finset State :=
  if P = ∅ then
    Finset.univ.filter (fun t => hasEvenRank g' t)
  else
    P.filter (fun t => g' t ≠ ⊥)

/-- The state type of the complement automaton: pairs `(g, P)` of a level ranking and
an obligation set tracking states that must eventually be discharged (receive odd rank). -/
abbrev ComplState (State : Type) [Fintype State] [DecidableEq State] : Type :=
  LevelRanking State × Finset State

/-- The initial level rankings for the complement automaton: rankings where every
start state of `a` receives a non-`⊥` rank (is tracked) and every non-start state
receives `⊥` (is not reachable at level 0). This ensures all possible runs are covered
by the initial witness ranking. -/
def initRankings (a : Buchi State Symbol) : Set (LevelRanking State) :=
  { g | (∀ s, s ∉ a.start → g s = ⊥) ∧ (∀ s, s ∈ a.start → g s ≠ ⊥) }

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

An accepting run witnesses that all reachable even-ranked states are eventually
eliminated (rank becomes `⊥`), proving rejection by the original NBA `a`. -/
@[scoped grind =]
noncomputable def complementNA (a : Buchi State Symbol) :
    Buchi (ComplState State) Symbol where
  Tr s σ t := covers a s.1 σ t.1 ∧ t.2 = updateObl t.1 s.2
  start := { s | s.1 ∈ initRankings a ∧ s.2 = initObl s.1 }
  accept := { s | s.2 = ∅ }

/-! ## Soundness Helper Lemmas

These lemmas support the soundness direction of KV2001 Lemma 5.2:
an odd ranking of the run DAG implies rejection by the original NBA. -/

variable {a : Buchi State Symbol}

omit [DecidableEq State] in
/-- The `covers` relation preserves non-`⊥`ness: if `g(s) ≠ ⊥` and `g'` covers `g`
via a transition `s -σ→ t`, then `g'(t) ≠ ⊥`. -/
lemma covers_neBot_of_neBot {g g' : LevelRanking State} {σ : Symbol} {s t : State}
    (hcov : covers a g σ g') (htr : a.Tr s σ t) (hgs : g s ≠ ⊥) : g' t ≠ ⊥ :=
  ((hcov s t htr).2.1 hgs).1

omit [DecidableEq State] in
/-- The `covers` relation is rank-non-increasing: if `g(s) ≠ ⊥` and `g'` covers `g`
via a transition `s -σ→ t`, then `g'(t) ≤ g(s)` (as `WithBot` elements). -/
lemma covers_rank_le {g g' : LevelRanking State} {σ : Symbol} {s t : State}
    (hcov : covers a g σ g') (htr : a.Tr s σ t) (hgs : g s ≠ ⊥) : g' t ≤ g s :=
  ((hcov s t htr).2.1 hgs).2

omit [DecidableEq State] in
/-- The `covers` relation enforces odd rank on accepting states:
if `t ∈ a.accept`, `g'` covers `g` via `s -σ→ t`, and `g'(t) = r`, then `r` is odd. -/
lemma covers_accept_odd {g g' : LevelRanking State} {σ : Symbol} {s t : State}
    {r : Fin (2 * Fintype.card State + 1)}
    (hcov : covers a g σ g') (htr : a.Tr s σ t) (hacc : t ∈ a.accept)
    (hval : g' t = (r : WithBot _)) : r.val % 2 = 1 :=
  (hcov s t htr).2.2 hacc r hval

omit [DecidableEq State] in
/-- Along any run of `a`, if the starting state has non-`⊥` rank in a covering sequence,
all subsequent states also have non-`⊥` rank. -/
lemma run_rank_defined_all {xs : ωSequence Symbol} {qs : ωSequence State}
    {gs : ℕ → LevelRanking State}
    (h_run : a.Run xs qs)
    (h_covers : ∀ i, covers a (gs i) (xs i) (gs (i + 1)))
    (h_zero : gs 0 (qs 0) ≠ ⊥) :
    ∀ k, gs k (qs k) ≠ ⊥ := by
  intro k
  induction k with
  | zero => exact h_zero
  | succ n ih => exact covers_neBot_of_neBot (h_covers n) (h_run.trans n) ih

omit [DecidableEq State] in
/-- Along any run of `a`, ranks are non-increasing in a covering sequence. -/
lemma run_rank_nonincreasing {xs : ωSequence Symbol} {qs : ωSequence State}
    {gs : ℕ → LevelRanking State}
    (h_run : a.Run xs qs)
    (h_covers : ∀ i, covers a (gs i) (xs i) (gs (i + 1)))
    (h_zero : gs 0 (qs 0) ≠ ⊥) :
    ∀ k, gs (k + 1) (qs (k + 1)) ≤ gs k (qs k) := by
  intro k
  exact covers_rank_le (h_covers k) (h_run.trans k)
    (run_rank_defined_all h_run h_covers h_zero k)

/-- A non-increasing sequence of values in `WithBot (Fin n)` that never equals `⊥`
eventually stabilizes. This uses the descending chain condition on finite types. -/
lemma withBot_fin_nonincreasing_stabilizes {n : ℕ} {f : ℕ → WithBot (Fin n)}
    (h_nonbot : ∀ k, f k ≠ ⊥) (h_nonincr : ∀ k, f (k + 1) ≤ f k) :
    ∃ k₀, ∃ r : Fin n, ∀ k ≥ k₀, f k = (r : WithBot _) := by
  have h_some : ∀ k, ∃ r : Fin n, f k = (r : WithBot _) := fun k => by
    cases hfk : f k with
    | bot => exact absurd hfk (h_nonbot k)
    | coe r => exact ⟨r, rfl⟩
  have h_antitone : Antitone f := by
    intro a b hab
    induction hab with
    | refl => exact le_refl _
    | step _ ih => exact le_trans (h_nonincr _) ih
  obtain ⟨k₀, hk₀_stab⟩ := WellFoundedLT.antitone_chain_condition h_antitone
  obtain ⟨r, hr⟩ := h_some k₀
  exact ⟨k₀, r, fun k hk => by rw [← hk₀_stab k hk, hr]⟩

omit [DecidableEq State] in
/-- If a run of `a` visits `a.accept` infinitely often and has a stabilized rank `r`
from position `k₀` onward, then `r` must be odd. -/
lemma run_accept_rank_odd {xs : ωSequence Symbol} {qs : ωSequence State}
    {gs : ℕ → LevelRanking State}
    (h_run : a.Run xs qs)
    (h_covers : ∀ i, covers a (gs i) (xs i) (gs (i + 1)))
    (h_freq : ∃ᶠ k in atTop, qs k ∈ a.accept)
    {k₀ : ℕ} {r : Fin (2 * Fintype.card State + 1)}
    (h_stable : ∀ k ≥ k₀, gs k (qs k) = (r : WithBot _)) :
    r.val % 2 = 1 := by
  rw [frequently_atTop] at h_freq
  obtain ⟨k, hk_ge, hk_acc⟩ := h_freq (k₀ + 1)
  have hk_pos : k ≥ 1 := by omega
  have h_tr : a.Tr (qs (k - 1)) (xs (k - 1)) (qs k) := by
    have := h_run.trans (k - 1)
    rwa [Nat.sub_add_cancel hk_pos] at this
  apply covers_accept_odd (h_covers (k - 1)) h_tr hk_acc
  have := h_stable k (by omega)
  rwa [Nat.sub_add_cancel hk_pos]

/-! ## Soundness Helper Lemmas (continued) -/

omit [DecidableEq State] in
/-- Helper: if a complement run starts in `initRankings a`, then any start state
of `a` has non-`⊥` initial rank in the first level ranking. -/
lemma initRankings_start_neBot {g : LevelRanking State}
    (hg : g ∈ initRankings a) {s : State} (hs : s ∈ a.start) : g s ≠ ⊥ :=
  hg.2 s hs

/-- Helper: the first level ranking of an accepting complement run lies in `initRankings a`. -/
lemma complementNA_run_init
    {xs : ωSequence Symbol} {ss : ωSequence (ComplState State)}
    (h_run : (complementNA a).Run xs ss) : (ss 0).1 ∈ initRankings a :=
  h_run.start.1

/-- Helper: for each step of a complement run, the level rankings σ-cover each other. -/
lemma complementNA_run_covers
    {xs : ωSequence Symbol} {ss : ωSequence (ComplState State)}
    (h_run : (complementNA a).Run xs ss) :
    ∀ i, covers a (ss i).1 (xs i) (ss (i + 1)).1 :=
  fun i => (h_run.trans i).1

/-! ## Main Theorems (proof_wanted) -/

/-- **Soundness**: The complement NBA accepts only words rejected by the original NBA.
`language (complementNA a) ≤ (language a)ᶜ`

Proof sketch (forward direction of KV2001 Lemma 5.2):

Suppose `xs ∈ language (complementNA a)` via accepting complement run `ss`, and assume
for contradiction that `xs ∈ language a` via accepting run `qs`.
The level rankings `gs i = (ss i).1` form a covering sequence:
- `qs 0 ∈ a.start` and `gs 0 ∈ initRankings a`, so `gs 0 (qs 0) ≠ ⊥`
  (by `initRankings_start_neBot` and `complementNA_run_init`).
- By `run_rank_defined_all`: all `gs k (qs k) ≠ ⊥`.
- By `run_rank_nonincreasing`: the sequence `gs k (qs k)` is non-increasing.
- By `withBot_fin_nonincreasing_stabilizes`: it stabilizes to some `r*`.
- By `run_accept_rank_odd`: `r*.val % 2 = 1` (odd).

The full contradiction uses the obligation set `P`:
- The complement accepts `∃ᶠ k, (ss k).2 = ∅` (obligation set cycles through empty).
- When `P_k = ∅`, the reset `P_{k+1}` = all states with even rank in `gs (k+1)`.
- If `gs (k+1) (qs (k+1))` is even, then `qs (k+1) ∈ P_{k+1}`.
  Since `gs j (qs j) ≠ ⊥` for all `j`, the state `qs (k+1)` can never be removed from `P`,
  so `P` can never become empty again. Contradiction with `∃ᶠ k, P_k = ∅`.
- If `gs (k+1) (qs (k+1))` is always odd (after rank stabilization to odd `r*`), then
  the DAG-level argument is needed: the run DAG of `a` on `xs` always has reachable states,
  and any valid odd ranking must assign rank 0 to some reachable state eventually, which
  creates an infinite path with rank 0 (even) — contradicting the odd ranking condition.
  (This requires the full tree/DAG argument from KV2001 Section 5.2.) -/
proof_wanted complement_language_sub :
    ∀ (a : Buchi State Symbol), language (complementNA a) ≤ (language a)ᶜ

/-- **Completeness**: Words rejected by the original NBA are accepted by the complement.
`(language a)ᶜ ≤ language (complementNA a)`

Proof sketch (backward direction of KV2001 Lemma 5.2):

If `xs ∉ language a`, then for every run `qs` of `a` on `xs`, the run visits `a.accept`
only finitely often. The run DAG `D(A, xs)` has no path visiting `a.accept` infinitely often.

By KV2001 Lemma 5.2 (backward direction), an inductive removal procedure shows that `D(A, xs)`
admits an *odd ranking*: a function `ρ : {(s, i) | s reachable at level i} → Fin (2n+1)` such
that:
- Accepting nodes get odd rank;
- Along every edge `(s, i) → (t, i+1)`, `ρ(t, i+1) ≤ ρ(s, i)` (non-increasing);
- Accepting nodes get strictly odd rank (even → odd decrease).

This odd ranking gives an accepting run of `complementNA a`:
- At each level `i`, set `gs i s = ρ(s, i)` for reachable `s`, `⊥` otherwise.
- The covering condition `covers a (gs i) (xs i) (gs (i+1))` follows directly.
- The obligation set `P` cycles through empty infinitely often because the ranking
  witnesses that all even-ranked states eventually get rank `⊥`.
- Thus `xs ∈ language (complementNA a)`.

The inductive removal procedure requires reasoning about finite-width DAGs (König's Lemma
or an explicit induction on DAG width), which is of Very High difficulty and is left as a
future proof obligation. -/
proof_wanted complement_language_sup :
    ∀ (a : Buchi State Symbol), (language a)ᶜ ≤ language (complementNA a)

/-- **Main theorem**: The complement NBA accepts exactly the complement language.
`language (complementNA a) = (language a)ᶜ`

Follows from `complement_language_sub` and `complement_language_sup` via `le_antisymm`. -/
proof_wanted complement_language_eq :
    ∀ (a : Buchi State Symbol), language (complementNA a) = (language a)ᶜ

end Cslib.Automata.NA.Buchi
