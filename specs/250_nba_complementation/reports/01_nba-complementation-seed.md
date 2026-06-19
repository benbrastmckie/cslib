# NBA Complementation — Seed Report

## Problem Statement

Given an NBA A with n states, construct an NBA A' such that L(A') = Σ^ω \ L(A).
Unlike finite automata, Büchi automata complementation is non-trivial: the subset
construction does not preserve the Büchi acceptance condition.

CSLib already has ω-regular language complementation via the Büchi congruence
(language-theoretic, in `Cslib/Computability/Languages/OmegaRegularLanguage.lean`).
This task provides the automata-level construction needed for algorithmic applications.

## Approaches

### 1. Determinization-Based (via McNaughton/Safra)

Determinize the NBA to a deterministic Muller/Rabin/parity automaton (task 241), then
complement by flipping the acceptance condition on the deterministic automaton (trivial
for deterministic automata). Finally convert back to NBA if needed.

- **Complexity**: 2^O(n log n) states (Safra), doubly-exponential (McNaughton)
- **Advantage**: modular — reuses determinization infrastructure
- **Disadvantage**: large blowup; depends on task 241

### 2. Rank-Based (Kupferman–Vardi 2001)

Track rankings of states: assign ranks from {0, ..., 2n} to each state in the subset,
where odd-ranked states are "doomed" (will not visit accepting states infinitely often).
An accepting run of the complement automaton witnesses that all runs of the original
are eventually doomed.

- **Complexity**: O((0.96n)^2n) — tightest known upper bound (Schewe 2009)
- **Advantage**: direct construction, avoids full determinization
- **Disadvantage**: complex invariants in the correctness proof

### 3. Slice-Based (Kähler–Wilke 2008)

Alternative to rank-based using "slices" of the run DAG. Potentially cleaner
correctness argument but less well-known.

### Formalization Considerations

- The rank-based approach has a cleaner self-contained correctness proof
- The determinization-based approach is modular but creates a dependency chain
- For CSLib, both approaches are valuable: rank-based for a standalone complement,
  determinization-based as a corollary of McNaughton (task 241)
- The tight bound proof (Schewe 2009) may be overkill for a first formalization;
  the original Kupferman-Vardi construction suffices

## CSLib Integration Points

- `Cslib/Computability/Automata/NA/Basic.lean` — NBA type
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` — existing language-level
  complement (Büchi congruence approach)
- Task 241 (McNaughton) — provides determinization route
- Task 248 (emptiness) — complement + emptiness = universality checking
- Task 251 (product) — complement + product = language inclusion

## Literature

- Büchi, J.R. "On a decision method in restricted second order arithmetic." In
  *Proceedings of the International Congress on Logic, Methodology and Philosophy of
  Science*, Stanford University Press, 1962.
- Safra, S. "On the complexity of ω-automata." In *Proceedings of the 29th FOCS*,
  IEEE, 1988, pp. 319–327.
- Kupferman, O., Vardi, M.Y. "Weak alternating automata are not that weak." *ACM
  Transactions on Computational Logic*, 2(3):408–429, 2001.
- Schewe, S. "Büchi complementation made tight." In *Proceedings of STACS*, LNCS
  5404, Springer, 2009, pp. 661–672.
- Piterman, N. "From nondeterministic Büchi and Streett automata to deterministic
  parity automata." *Logical Methods in Computer Science*, 3(3):5, 2007.
- Kähler, D., Wilke, T. "Complementation, disambiguation, and determinization of
  Büchi automata unified." In *Proceedings of ICALP*, LNCS 5126, Springer, 2008,
  pp. 724–735.
- Yan, Q. "Lower bounds for complementation of ω-automata via the full automata
  technique." *Logical Methods in Computer Science*, 4(1):5, 2008.
