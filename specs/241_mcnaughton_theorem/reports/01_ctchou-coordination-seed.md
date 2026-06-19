# ctchou/AutomataTheory Coordination — Seed Report

## Overview

The [ctchou/AutomataTheory](https://github.com/ctchou/AutomataTheory) repository is
an independent Lean 4 formalization of automata theory on finite and infinite words.
It includes results that overlap significantly with CSLib tasks 241–245.

## Known Contents (from online research)

### Claimed Results
- McNaughton's theorem (equivalence of ω-regular languages and deterministic Muller
  automata) — directly overlaps with CSLib task 241
- Closure of regular languages under boolean operations, concatenation, Kleene star
- Closure of ω-regular languages under union, intersection, complementation,
  concatenation, ω-iteration
- ω-regular complementation (modulo a Ramsey theorem)
- Uniform framework for finite and infinite words

### Architecture Questions (to investigate)
1. **Type definitions**: Does it define its own automata types or build on Mathlib's
   `DFA`/`NFA`? CSLib uses its own `NA.BuchiAutomaton` and `DA.DetMullerAutomaton`.
2. **Mathlib dependency**: Which Mathlib version? Does it use `Mathlib.Computability.*`?
3. **Word representation**: CSLib uses `ℕ → α` for ω-words. Does ctchou match?
4. **Acceptance conditions**: How are Büchi/Muller acceptance formalized? CSLib uses
   `Set.Infinite` for Büchi and explicit Muller acceptance sets.
5. **Proof techniques**: Does the McNaughton proof use the standard congruence-based
   approach, the Ramsey-theoretic approach, or something else?

## Coordination Assessment Criteria

### Compatibility Dimensions
| Dimension | Assessment Needed |
|-----------|-------------------|
| Type compatibility | Can types be unified or do they require translation layers? |
| Naming conventions | Does it follow Mathlib/CSLib naming standards? |
| Import structure | Does it fit CSLib's module hierarchy? |
| Proof style | Tactic-heavy vs term-mode? Consistent with CSLib? |
| Licensing | MIT/Apache compatible with CSLib's license? |

### Possible Outcomes
1. **Port**: Adapt proofs to CSLib's type definitions and conventions
2. **Coordinate**: Propose shared upstream types, build complementary results
3. **Independent**: Develop CSLib's own proofs (if architecturally incompatible)
4. **Reference**: Use as proof sketch / strategy guide even if code isn't portable

## Impact on CSLib Tasks

| Task | Impact |
|------|--------|
| 241 (McNaughton) | Could port rather than build from scratch — largest potential savings |
| 250 (NBA complementation) | ω-regular complementation exists; automata-level construction may differ |
| 243 (DBA) | May have relevant DBA constructions |
| 252 (Acceptance zoo) | Muller acceptance likely formalized; Rabin/parity may not be |

## Research Plan

1. Clone and build ctchou/AutomataTheory against current Mathlib
2. Map type definitions against CSLib's automata types
3. Evaluate McNaughton proof structure and adaptability
4. Check license file
5. Optionally: reach out to author about coordination

## Literature

- McNaughton, R. "Testing and generating infinite sequences by a finite automaton."
  *Information and Control*, 9(5):521–530, 1966.
- Thomas, W. "Automata on infinite objects." In van Leeuwen, J. (ed.), *Handbook of
  Theoretical Computer Science*, vol. B, Elsevier, 1990, pp. 133–191.
- Perrin, D., Pin, J.-É. *Infinite Words: Automata, Semigroups, Logic and Games*.
  Pure and Applied Mathematics vol. 141, Academic Press, 2004.
