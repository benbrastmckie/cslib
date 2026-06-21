# NBA Emptiness Checking — Seed Report

## Problem Statement

Given a nondeterministic Büchi automaton (NBA) A = (Q, Σ, δ, q₀, F), decide whether
L(A) = ∅ — i.e., whether A accepts any ω-word. Equivalently: does there exist a
reachable accepting cycle (a cycle through the accepting states F reachable from q₀)?

This is the key decision problem connecting automata constructions to verification:
LTL model checking reduces to NBA emptiness of a product automaton (task 251).

## Algorithms

### Nested DFS (Courcoubetis–Vardi–Wolper–Yannakakis 1992)

Two-phase depth-first search: the outer DFS explores from q₀; when it backtracks from
an accepting state q ∈ F, an inner DFS checks whether q is reachable from itself
(i.e., lies on a cycle). If the inner DFS reaches q, an accepting cycle exists.

- **Complexity**: O(|Q| × |δ|) time, O(|Q|) space
- **On-the-fly**: can interleave with automaton construction (important for model checking)
- **Limitation**: inherently sequential; parallelization is non-trivial

### SCC-Based (Tarjan / Emerson–Lei)

Compute the strongly connected components of the automaton's transition graph. The NBA
is non-empty iff there exists an SCC that (1) is reachable from q₀, (2) contains at
least one accepting state, and (3) is non-trivial (has at least one edge).

- **Complexity**: O(|Q| + |δ|) via Tarjan's algorithm
- **Advantage**: cleaner correctness proof, standard graph-theoretic infrastructure
- **Disadvantage**: requires full graph exploration before deciding (not on-the-fly)

### Formalization Considerations

The SCC-based approach likely has a cleaner Lean 4 formalization:
- Tarjan's SCC algorithm has well-understood invariants
- The correctness criterion ("reachable non-trivial SCC with accepting state") is a
  clean graph-theoretic predicate
- Mathlib has `Mathlib.Combinatorics.SimpleGraph` infrastructure, though adapting to
  directed labeled transition graphs requires work

The nested DFS approach is more relevant for executable model checking but harder to
verify (subtle correctness argument involving DFS stack invariants).

## CSLib Integration Points

- `Cslib/Computability/Automata/NA/Basic.lean` — NBA type definitions, Büchi acceptance
  via `∃ᶠ k in atTop, ss k ∈ a.accept` (Filter.Frequently/atTop formulation)
- `Cslib/Foundations/Data/OmegaSequence/InfOcc.lean` — `infOcc` predicate for "infinitely
  often", with StrictMono characterization and finite-type pigeonhole
- `Cslib/Computability/Automata/NA/Equivalence.lean` — language equivalence
- Product construction (task 251) will compose emptiness with LTS × NBA product
- GNBA emptiness follows from NBA emptiness + GNBA-to-NBA translation (task 236)

## Literature

- Büchi, J.R. "On a decision method in restricted second order arithmetic." In
  *Proceedings of the International Congress on Logic, Methodology and Philosophy of
  Science*, Stanford University Press, 1962.
- Courcoubetis, C., Vardi, M.Y., Wolper, P., Yannakakis, M. "Memory-efficient
  algorithms for the verification of temporal properties." *Formal Methods in System
  Design*, 1(2/3):275–288, 1992.
- Schwoon, S., Esparza, J. "A note on on-the-fly verification algorithms." In
  *Proceedings of TACAS*, LNCS 985, Springer, 2005.
- Tarjan, R. "Depth-first search and linear graph algorithms." *SIAM Journal on
  Computing*, 1(2):146–160, 1972.
- Emerson, E.A., Lei, C.-L. "Efficient model checking in fragments of the
  propositional mu-calculus." In *Proceedings of LICS*, IEEE, 1986.
- Baier, C., Katoen, J.-P. *Principles of Model Checking*. MIT Press, 2008.
  Chapters 4.4 (persistence checking) and 7.3 (NBA emptiness).
