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
  transitions are synchronized between LTS steps and NBA steps, start states are
  `init × nba.start`, and accept states are `Set.univ × nba.accept`.

## Main theorems

- `LTS.naProd_start_iff` : characterization of start states of the product
- `LTS.naProd_accept_iff` : characterization of accept states of the product
- `LTS.naProd_tr_iff` : characterization of transitions of the product
- `LTS.naProd_language_nonempty_of_exec` : non-empty LTS execution implies non-empty product
  language
- `LTS.exec_of_naProd_language_nonempty` : non-empty product language implies non-empty LTS
  execution
- `LTS.naProd_language_nonempty_iff_exec` : language non-emptiness iff there exists an LTS
  execution from `init` whose labeling sequence is accepted by the NBA

## References

* [C. Baier, J.-P. Katoen, *Principles of Model Checking*][BaierKatoen2008], Chapter 4
-/

@[expose] public section

namespace Cslib.LTS

open Set Filter ωSequence Automata Automata.NA

variable {State Label Q Sigma : Type*}

/-- The synchronous product of an LTS with an NBA.

Given:
- `lts : LTS State Label` — the labelled transition system
- `labeling : State → Sigma` — the labeling function mapping states to alphabet symbols
- `init : Set State` — the initial states of the LTS
- `nba : NA.Buchi Q Sigma` — the Büchi automaton over alphabet `Sigma`

The product `NA.Buchi (State × Q) Sigma` has:
- **Transitions**: `(s, q) →[labeling s] (s', q')` iff `∃ μ, lts.Tr s μ s'` (LTS makes a step)
  and `nba.Tr q (labeling s) q'` (NBA reads the label of the source state). The input symbol `a`
  must equal `labeling s` (reads-source convention).
- **Start states**: `init ×ˢ nba.start` (Cartesian product of LTS initial states and NBA start
  states).
- **Accept states**: `Set.univ ×ˢ nba.accept` (any LTS state paired with an NBA accept state). -/
def naProd (lts : LTS State Label) (labeling : State → Sigma) (init : Set State)
    (nba : Automata.NA.Buchi Q Sigma) : Automata.NA.Buchi (State × Q) Sigma where
  Tr sq a sq' :=
    (∃ μ, lts.Tr sq.1 μ sq'.1) ∧ nba.Tr sq.2 a sq'.2 ∧ a = labeling sq.1
  start := init ×ˢ nba.start
  accept := Set.univ ×ˢ nba.accept

variable (lts : LTS State Label) (labeling : State → Sigma) (init : Set State)
  (nba : Automata.NA.Buchi Q Sigma)

/-- Membership in the start states of the product: `(s, q) ∈ start` iff `s ∈ init` and
`q ∈ nba.start`. -/
@[simp]
lemma naProd_start_iff {s : State} {q : Q} :
    (s, q) ∈ (naProd lts labeling init nba).start ↔ s ∈ init ∧ q ∈ nba.start := by
  simp [naProd, Set.mem_prod]

/-- Membership in the accept states of the product: `(s, q) ∈ accept` iff `q ∈ nba.accept`. -/
@[simp]
lemma naProd_accept_iff {s : State} {q : Q} :
    (s, q) ∈ (naProd lts labeling init nba).accept ↔ q ∈ nba.accept := by
  simp [naProd, Set.mem_prod]

/-- The transition relation of `naProd` unfolds: `naProd.Tr (s, q) a (s', q')` iff
there exists a label `μ` with `lts.Tr s μ s'`, `nba.Tr q a q'`, and `a = labeling s`. -/
@[simp]
lemma naProd_tr_iff {s s' : State} {q q' : Q} {a : Sigma} :
    (naProd lts labeling init nba).Tr (s, q) a (s', q') ↔
      (∃ μ, lts.Tr s μ s') ∧ nba.Tr q a q' ∧ a = labeling s := by
  simp [naProd]

/-- If there exists an LTS omega-execution from a state in `init` whose labeling sequence is
accepted by the NBA, then the product NBA language is non-empty.

Given LTS execution `ss_lts` with transition labels `mus`, NBA run `ss_nba` that starts in
`nba.start` and accepts infinitely often, the product run on `ss = fun i => (ss_lts i, ss_nba i)`
with input `xs = fun i => labeling (ss_lts i)` is an accepting product run. -/
theorem naProd_language_nonempty_of_exec
    {s₀ : State} (hs₀ : s₀ ∈ init)
    {ss_lts : ωSequence State} {mus : ωSequence Label}
    {ss_nba : ωSequence Q}
    (h_lts : lts.OmegaExecution ss_lts mus)
    (h_ss0 : ss_lts 0 = s₀)
    (h_nba_start : ss_nba 0 ∈ nba.start)
    (h_nba_run : ∀ i, nba.Tr (ss_nba i) (labeling (ss_lts i)) (ss_nba (i + 1)))
    (h_nba_acc : ∃ᶠ k in atTop, ss_nba k ∈ nba.accept) :
    (ωAcceptor.language (naProd lts labeling init nba)).toSet.Nonempty := by
  -- Construct the product run on input xs = fun i => labeling (ss_lts i)
  let xs : ωSequence Sigma := ωSequence.mk (fun i => labeling (ss_lts i))
  let ss : ωSequence (State × Q) := ωSequence.mk (fun i => (ss_lts i, ss_nba i))
  -- The product run
  have h_run : (naProd lts labeling init nba).Run xs ss := by
    constructor
    · -- Start: (ss_lts 0, ss_nba 0) ∈ init × nba.start
      change ss_lts 0 ∈ init ∧ ss_nba 0 ∈ nba.start
      exact ⟨h_ss0 ▸ hs₀, h_nba_start⟩
    · -- Transitions at each step i
      intro i
      simp only [naProd]
      exact ⟨⟨mus i, h_lts i⟩, h_nba_run i, rfl⟩
  -- Acceptance: ss_nba k ∈ nba.accept infinitely often implies (ss k) ∈ accept infinitely often
  have h_acc : ∃ᶠ k in atTop, ss k ∈ (naProd lts labeling init nba).accept := by
    rw [Filter.frequently_atTop] at h_nba_acc ⊢
    intro n
    obtain ⟨k, hk, hkacc⟩ := h_nba_acc n
    exact ⟨k, hk, by simp [ss, get_fun, hkacc]⟩
  exact ⟨xs, ⟨ss, h_run, h_acc⟩⟩

/-- If the product NBA language is non-empty, then there exists an LTS omega-execution from a
state in `init` whose labeling sequence is accepted by the NBA.

Given a product accepting run, project onto LTS and NBA components and extract the witnessing data:
- The LTS state sequence `ss_lts = fun i => (ss i).1`
- The NBA state sequence `ss_nba = fun i => (ss i).2`
- A label sequence `mus` witnessing LTS transitions (extracted classically from existentials in
  the product transition relation).
- The NBA run conditions and infinite acceptance. -/
theorem exec_of_naProd_language_nonempty
    (h : (ωAcceptor.language (naProd lts labeling init nba)).toSet.Nonempty) :
    ∃ s₀ ∈ init, ∃ (ss_lts : ωSequence State) (mus : ωSequence Label) (ss_nba : ωSequence Q),
      lts.OmegaExecution ss_lts mus ∧
      ss_lts 0 = s₀ ∧
      ss_nba 0 ∈ nba.start ∧
      (∀ i, nba.Tr (ss_nba i) (labeling (ss_lts i)) (ss_nba (i + 1))) ∧
      ∃ᶠ k in atTop, ss_nba k ∈ nba.accept := by
  -- Unpack the non-empty language: get accepting run
  obtain ⟨xs, ss, h_run, h_acc⟩ := h
  -- Project onto LTS and NBA components
  let ss_lts : ωSequence State := ss.map Prod.fst
  let ss_nba : ωSequence Q := ss.map Prod.snd
  -- Extract the LTS label sequence classically from product transitions
  let mus : ωSequence Label := ωSequence.mk (fun i => (h_run.trans i).1.choose)
  refine ⟨ss_lts 0, ?_, ss_lts, mus, ss_nba, ?_, rfl, ?_, ?_, ?_⟩
  · -- s₀ = (ss 0).1 ∈ init
    have hstart := h_run.start
    simp only [naProd, Set.mem_prod] at hstart
    exact hstart.1
  · -- lts.OmegaExecution ss_lts mus
    intro i
    simp only [ss_lts, mus, get_map, get_fun]
    exact (h_run.trans i).1.choose_spec
  · -- ss_nba 0 ∈ nba.start
    have hstart := h_run.start
    simp only [naProd, Set.mem_prod] at hstart
    exact hstart.2
  · -- ∀ i, nba.Tr (ss_nba i) (labeling (ss_lts i)) (ss_nba (i+1))
    intro i
    have htrans := h_run.trans i
    simp only [naProd] at htrans
    -- htrans.2.1 : nba.Tr (ss i).2 (xs i) (ss (i+1)).2
    -- htrans.2.2 : xs i = labeling (ss i).1
    rw [htrans.2.2] at htrans
    exact htrans.2.1
  · -- ∃ᶠ k in atTop, ss_nba k ∈ nba.accept
    rw [Filter.frequently_atTop] at h_acc ⊢
    intro n
    obtain ⟨k, hk, hkacc⟩ := h_acc n
    obtain ⟨-, h2⟩ := hkacc
    exact ⟨k, hk, h2⟩

/-- Language non-emptiness of the product NBA is equivalent to the existence of an LTS
omega-execution from a state in `init` whose labeling sequence is accepted by the NBA.

This is the key theorem connecting product construction to model checking: the product
NBA accepts iff there is a synchronized LTS-NBA run. -/
theorem naProd_language_nonempty_iff_exec :
    (ωAcceptor.language (naProd lts labeling init nba)).toSet.Nonempty ↔
      ∃ s₀ ∈ init, ∃ (ss_lts : ωSequence State) (mus : ωSequence Label) (ss_nba : ωSequence Q),
        lts.OmegaExecution ss_lts mus ∧
        ss_lts 0 = s₀ ∧
        ss_nba 0 ∈ nba.start ∧
        (∀ i, nba.Tr (ss_nba i) (labeling (ss_lts i)) (ss_nba (i + 1))) ∧
        ∃ᶠ k in atTop, ss_nba k ∈ nba.accept :=
  ⟨exec_of_naProd_language_nonempty lts labeling init nba, by
   rintro ⟨s₀, hs₀, ss_lts, mus, ss_nba, h_lts, h_ss0, h_start, h_tr, h_acc⟩
   exact naProd_language_nonempty_of_exec lts labeling init nba hs₀ h_lts h_ss0 h_start h_tr h_acc⟩

end Cslib.LTS

end
