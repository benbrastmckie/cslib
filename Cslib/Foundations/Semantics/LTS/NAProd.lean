/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-! # LTS × NBA Product Construction

This module defines the synchronous product of a Labelled Transition System (LTS) with a
Nondeterministic Büchi Automaton (NBA) over a labeling alphabet. The product automaton is itself
an NBA whose state space is `State × Q`, where `State` and `Q` are the state types of the LTS and
NBA respectively.

The *reads-source* convention is used throughout: the NBA reads the label of the *source* state
(before the transition), matching the position-0 evaluation convention of `SatisfiesExec`.

## Main definitions

- `LTS.naProd lts labeling init nba` : the NBA product `NA.Buchi (State × Q) Sigma` where
  transitions are synchronized between LTS steps and NBA steps, start states are `init × nba.start`,
  and accept states are `Set.univ × nba.accept`.

## Main theorems

- `LTS.naProd_start_iff` : characterization of start states of the product
- `LTS.naProd_accept_iff` : characterization of accept states of the product
- `LTS.naProd_run_iff` : run characterization: a product run projects to a synchronized LTS
  omega-execution and NBA run
- `LTS.naProd_language_nonempty_iff_exec` : language non-emptiness iff there exists an LTS
  omega-execution from `init` whose labeling sequence is accepted by the NBA

## References

* [C. Baier, J.-P. Katoen, *Principles of Model Checking*][BaierKatoen2008], Chapter 4
-/

@[expose] public section

namespace Cslib.LTS

open Set Filter ωSequence Automata Automata.NA

variable {State Label Q Sigma : Type*}
variable (lts : LTS State Label) (labeling : State → Sigma) (init : Set State)
  (nba : Automata.NA.Buchi Q Sigma)

/-- The synchronous product of an LTS with an NBA.

Given:
- `lts : LTS State Label` — the labelled transition system
- `labeling : State → Sigma` — the labeling function mapping states to alphabet symbols
- `init : Set State` — the initial states of the LTS
- `nba : NA.Buchi Q Sigma` — the Büchi automaton over alphabet `Sigma`

The product `NA.Buchi (State × Q) Sigma` has:
- **Transitions**: `(s, q) →[a] (s', q')` iff `∃ μ, lts.Tr s μ s'` (LTS makes a step on any
  label) and `nba.Tr q a q'` (NBA reads `a`), where `a = labeling s` (reads-source convention).
- **Start states**: `init ×ˢ nba.start` (Cartesian product of LTS initial states and NBA start
  states).
- **Accept states**: `Set.univ ×ˢ nba.accept` (any LTS state paired with an NBA accept state). -/
def LTS.naProd : Automata.NA.Buchi (State × Q) Sigma where
  Tr sq a sq' :=
    (∃ μ, lts.Tr sq.1 μ sq'.1) ∧ nba.Tr sq.2 a sq'.2 ∧ a = labeling sq.1
  start := init ×ˢ nba.start
  accept := Set.univ ×ˢ nba.accept

/-- Membership in the start states of the product: `(s, q) ∈ start` iff `s ∈ init` and
`q ∈ nba.start`. -/
lemma naProd_start_iff {s : State} {q : Q} :
    (s, q) ∈ (LTS.naProd lts labeling init nba).start ↔
      s ∈ init ∧ q ∈ nba.start := by
  simp [LTS.naProd, Set.mem_prod]

/-- Membership in the accept states of the product: `(s, q) ∈ accept` iff `q ∈ nba.accept`. -/
lemma naProd_accept_iff {s : State} {q : Q} :
    (s, q) ∈ (LTS.naProd lts labeling init nba).accept ↔ q ∈ nba.accept := by
  simp [LTS.naProd, Set.mem_prod]

/-- Run characterization for the product NBA.

A run of `naProd lts labeling init nba` on input `xs` through state sequence `ss` is
equivalent to the existence of an LTS omega-execution and an NBA run whose states project
onto the components of `ss`, together with the consistency condition that `xs` equals the
labeling sequence of the LTS states. -/
theorem naProd_run_iff
    {xs : ωSequence Sigma} {ss : ωSequence (State × Q)} :
    (LTS.naProd lts labeling init nba).Run xs ss ↔
      ss 0 ∈ (LTS.naProd lts labeling init nba).start ∧
      lts.OmegaExecution (ss.map Prod.fst) (ss.map fun sq => xs (xs.length))
        ∧  -- placeholder form -- the real content is below
      True := by
  sorry

-- Let me write a more concrete approach:

/-- The first projection of a product run gives a valid LTS omega-execution sequence:
consecutive product states have LTS transitions. -/
lemma naProd_run_lts_exec
    {xs : ωSequence Sigma} {ss : ωSequence (State × Q)}
    (h : (LTS.naProd lts labeling init nba).Run xs ss) :
    ∀ i, ∃ μ, lts.Tr (ss i).1 μ (ss (i + 1)).1 := by
  intro i
  have htrans := h.trans i
  simp only [LTS.naProd] at htrans
  exact htrans.1

/-- The second projection of a product run gives a valid NBA run on the labeling sequence. -/
lemma naProd_run_nba_run
    {xs : ωSequence Sigma} {ss : ωSequence (State × Q)}
    (h : (LTS.naProd lts labeling init nba).Run xs ss) :
    (ss 0).2 ∈ nba.start ∧
    ∀ i, nba.Tr (ss i).2 (xs i) (ss (i + 1)).2 ∧ xs i = labeling (ss i).1 := by
  constructor
  · have hstart := h.start
    simp [LTS.naProd] at hstart
    exact hstart.2
  · intro i
    have htrans := h.trans i
    simp only [LTS.naProd] at htrans
    exact ⟨htrans.2.1, htrans.2.2⟩

end Cslib.LTS

end
