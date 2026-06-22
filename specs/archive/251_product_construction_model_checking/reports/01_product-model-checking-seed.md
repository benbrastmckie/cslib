# Product Construction and Model Checking Reduction — Seed Report

## Problem Statement

The automata-theoretic approach to LTL model checking (Vardi–Wolper 1986) reduces the
model checking problem to NBA emptiness:

> A Kripke structure M satisfies an LTL formula φ iff the product of M with the NBA
> for ¬φ has an empty accepted language.

This requires three components:
1. **LTL-to-NBA**: translate ¬φ to an NBA A_¬φ (task 242, Vardi-Wolper tableau)
2. **Product construction**: build the synchronous product M ⊗ A_¬φ
3. **Emptiness check**: decide L(M ⊗ A_¬φ) = ∅ (task 248)

This task formalizes component (2) and proves the overall reduction theorem.

## Product Construction

### Definition

Given a Kripke structure M = (S, S₀, R, L) over atomic propositions AP, and an NBA
A = (Q, 2^AP, δ, q₀, F), the product M ⊗ A is an NBA:

- States: S × Q
- Initial states: S₀ × {q₀}
- Transitions: ((s,q), (s',q')) ∈ δ_⊗ iff R(s,s') ∧ q' ∈ δ(q, L(s'))
- Accepting states: S × F

### Correctness Theorem

L(M ⊗ A_¬φ) ≠ ∅ iff there exists a path π in M such that π ⊨ ¬φ, iff M ⊭ φ.

The proof has two directions:
- **Soundness**: an accepting run of M ⊗ A_¬φ projects to a path in M satisfying ¬φ
- **Completeness**: a path in M satisfying ¬φ lifts to an accepting run of M ⊗ A_¬φ
  (using the correctness of the LTL-to-NBA translation)

## Existing CSLib Infrastructure

CSLib already has rich LTS infrastructure that this task should build on:

- `Cslib/Foundations/Semantics/LTS/Basic.lean` — `LTS State Label` with `Tr` relation,
  multistep `MTr`, reachability, classes (image-finite, finitely branching, deterministic)
- `Cslib/Foundations/Semantics/LTS/OmegaExecution.lean` — `OmegaExecution` for infinite
  runs of an LTS (ω-sequence of states + labels)
- `Cslib/Foundations/Semantics/FLTS/Basic.lean` — `FLTS` (functional/deterministic LTS),
  used as base for DA
- `Cslib/Foundations/Semantics/FLTS/Prod.lean` — FLTS product construction
- `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` — `SatisfiesExec` bridges
  LTL satisfaction to LTS omega-executions via a labeling function `State → (Atom → Prop)`.
  This is exactly the model checking connection.

No new transition system type is needed. The product construction should use `LTS` with
a labeling function, matching the existing `SatisfiesExec` pattern.

## CSLib Integration Points

- `Cslib/Foundations/Semantics/LTS/` — LTS type, OmegaExecution (system side)
- `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` — SatisfiesExec bridge
- `Cslib/Computability/Automata/NA/Basic.lean` — NBA types (automaton side)
- `Cslib/Computability/Automata/NA/Prod.lean` — existing NBA × NBA product (for
  intersection); the LTS × NBA product is structurally different
- Task 242 (Vardi-Wolper) — provides LTL-to-NBA for ¬φ
- Task 248 (emptiness) — emptiness of the product NBA

## Literature

- Vardi, M.Y., Wolper, P. "An automata-theoretic approach to automatic program
  verification." In *Proceedings of the 1st LICS*, IEEE, 1986, pp. 332–344.
- Clarke, E.M., Grumberg, O., Peled, D.A. *Model Checking*. MIT Press, 1999.
  Chapter 9 (automata-theoretic model checking).
- Baier, C., Katoen, J.-P. *Principles of Model Checking*. MIT Press, 2008.
  Chapters 4 (linear-time properties), 5 (LTL model checking).
- Vardi, M.Y. "An automata-theoretic approach to linear temporal logic." In
  Moller, F., Birtwistle, G. (eds.), *Logics for Concurrency*, LNCS 1043, Springer,
  1996, pp. 238–266.
- Gerth, R., Peled, D., Vardi, M.Y., Wolper, P. "Simple on-the-fly automatic
  verification of linear temporal logic." In *Proceedings of PSTV*, Chapman & Hall,
  1995, pp. 3–18.
