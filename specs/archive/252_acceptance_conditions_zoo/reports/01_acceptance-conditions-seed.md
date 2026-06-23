# Acceptance Conditions Zoo — Seed Report

## Problem Statement

CSLib currently has two acceptance conditions for deterministic ω-automata:
- **Büchi**: DBA in `Cslib/Computability/Automata/DA/Basic.lean` (visit accepting
  states infinitely often)
- **Muller**: DMA in `Cslib/Computability/Automata/DA/Basic.lean` (the set of
  infinitely-visited states belongs to a designated family of accepting sets)

Two important acceptance conditions are missing: **Rabin** and **parity**. These are
widely used in automata theory and have clean conversion theorems between them. Parity
acceptance in particular is central to the connection with parity games and the
μ-calculus.

## Acceptance Conditions

### Rabin Acceptance

A Rabin acceptance condition consists of k pairs (E₁,F₁), ..., (Eₖ,Fₖ) where
Eᵢ, Fᵢ ⊆ Q. A run ρ is accepting iff there exists i such that:
- Inf(ρ) ∩ Eᵢ = ∅ (finitely many visits to Eᵢ)
- Inf(ρ) ∩ Fᵢ ≠ ∅ (infinitely many visits to Fᵢ)

where Inf(ρ) is the set of states visited infinitely often.

Rabin acceptance captures exactly the ω-regular languages on deterministic automata
(Rabin 1969). Büchi is the special case k=1 with E₁=∅.

### Streett Acceptance (Dual of Rabin)

A Streett condition uses the same pair structure but with the dual criterion: for ALL
i, if Inf(ρ) ∩ Fᵢ ≠ ∅ then Inf(ρ) ∩ Eᵢ ≠ ∅. Streett acceptance is useful for
fairness constraints.

### Parity Acceptance

Each state q has a priority c(q) ∈ ℕ. A run ρ is accepting iff the minimum (or
maximum, depending on convention) priority occurring infinitely often is even.

- **Min-even**: min{c(q) | q ∈ Inf(ρ)} is even (Emerson–Jutla convention)
- **Max-even**: max{c(q) | q ∈ Inf(ρ)} is even (alternative convention)

Parity acceptance is the bridge to parity games (Emerson–Jutla–Sistla 1993,
Zielonka 1998) and the μ-calculus (Emerson–Jutla 1991).

## Classical Conversions

| From | To | Complexity | Reference |
|------|----|-----------|-----------|
| Muller → Rabin | Polynomial (in Muller table size) | Standard |
| Rabin → Muller | Polynomial | Standard |
| Rabin → Parity | O(n · k!) states | Piterman 2007 |
| Parity → Rabin | Direct (k/2 pairs) | Trivial |
| Büchi → Rabin | Direct (1 pair) | Trivial |
| Streett → Rabin | Complement pairs | Trivial |
| NBA → DRA | 2^O(n log n) | Safra 1988 |
| NBA → DPA | O(n!)/(e/2)^n | Piterman 2007 |

The key non-trivial conversion is Rabin-to-parity (Piterman 2007), which produces a
deterministic parity automaton with O(n · k!) states from a deterministic Rabin
automaton with n states and k pairs.

## Formalization Plan (Sketch)

1. Define `DetRabinAutomaton` with Rabin pairs acceptance
2. Define `DetParityAutomaton` with priority coloring acceptance
3. Prove Muller↔Rabin conversion
4. Prove Rabin→Parity conversion (Piterman 2007)
5. Prove Parity→Rabin conversion (direct)
6. Optionally: Streett acceptance and Rabin↔Streett duality

## CSLib Integration Points

- `Cslib/Computability/Automata/DA/Basic.lean` — existing DBA/DMA types with Büchi
  acceptance (`∃ᶠ k in atTop`) and Muller acceptance (`infOcc ∈ accept`)
- `Cslib/Foundations/Data/OmegaSequence/InfOcc.lean` — `infOcc` predicate providing
  the "infinitely often" foundation that Rabin and parity acceptance will build on.
  Includes StrictMono characterization and finite-type pigeonhole.
- `Cslib/Computability/Automata/NA/Basic.lean` — nondeterministic Büchi/Muller for
  comparison; Rabin/parity could also have nondeterministic variants
- Task 241 (McNaughton) — produces DMA; Muller→Rabin→Parity gives DPA
- Task 250 (complementation) — complement of DRA is DStreett (trivial)
- Future: parity games, μ-calculus model checking

## Literature

- Muller, D.E. "Infinite sequences and finite machines." In *Proceedings of the 4th
  Annual Symposium on Switching Circuit Theory and Logical Design*, IEEE, 1963,
  pp. 3–16.
- Rabin, M.O. "Decidability of second-order theories and automata on infinite trees."
  *Transactions of the AMS*, 141:1–35, 1969.
- Emerson, E.A., Jutla, C.S. "Tree automata, mu-calculus and determinacy." In
  *Proceedings of the 32nd FOCS*, IEEE, 1991, pp. 368–377.
- Thomas, W. "Languages, automata, and logic." In Rozenberg, G., Salomaa, A. (eds.),
  *Handbook of Formal Languages*, vol. 3, Springer, 1997, pp. 389–455.
- Piterman, N. "From nondeterministic Büchi and Streett automata to deterministic
  parity automata." *Logical Methods in Computer Science*, 3(3):5, 2007.
- Zielonka, W. "Infinite games on finitely coloured graphs with applications to
  automata on infinite trees." *Theoretical Computer Science*, 200(1–2):135–183, 1998.
- Löding, C. "Optimal bounds for transformations of ω-automata." In *Proceedings of
  FSTTCS*, LNCS 1738, Springer, 1999, pp. 97–109.
- Safra, S. "On the complexity of ω-automata." In *Proceedings of the 29th FOCS*,
  IEEE, 1988, pp. 319–327.
