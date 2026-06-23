# Task 252: Acceptance Conditions Zoo — Implementation Summary

## Overview

Formalized Rabin, Streett, and parity acceptance conditions for deterministic automata in CSLib,
alongside the existing Muller (DMA) and Büchi (DBA) acceptance. Proved the classical conversions
between them and deferred the two hard directions (LAR and exponential-pairs) as `proof_wanted`.

## Files Created

### Cslib/Computability/Automata/DA/Rabin.lean (235 lines)

- `DA.Rabin` — Rabin acceptance: set of `(E, F)` pairs; run accepted iff for some pair,
  `infOcc ∩ E = ∅` and `infOcc ∩ F ≠ ∅`
- `DA.Streett` — Streett acceptance (dual of Rabin): all pairs must satisfy the condition
- `Buchi.toRabin` / `Buchi.toRabin_language_eq` — DBA → DRA (1 Rabin pair)
- `Rabin.toMuller` / `Rabin.toMuller_language_eq` — DRA → DMA (same state space)
- `Rabin.toStreett` / `Rabin.toStreett_language_eq` — Rabin-Streett duality
- `Streett.toRabin` / `Streett.toRabin_language_eq` — Streett-Rabin duality

### Cslib/Computability/Automata/DA/Parity.lean (193 lines)

- `DA.Parity` — Parity acceptance: coloring function `c : State → ℕ`;
  run accepted iff minimum infinitely-occurring color is even
- `Parity.toRabin` / `Parity.toRabin_language_eq` — DPA → DRA conversion

### Cslib/Computability/Automata/DA/Conversions.lean (111 lines)

- `proof_wanted Rabin.toParity_exists` — DRA → DPA via LAR construction (Kupferman-Vardi 1998)
- `proof_wanted Muller.toRabin_exists` — DMA → DRA with exponential pair blowup

## Conversion Chain (Proved)

```
DBA → DRA ↔ DSA
       ↓
      DMA
DPA → DRA
```

## CI Verification

- `lake build`: Pass (3043 jobs)
- `lake exe checkInitImports`: Pass
- `lake exe lint-style`: Pass
- `lake test`: Pass
- `lake exe mk_all --module`: No update needed
- `lake shake`: Pass (one cosmetic `privateModule` warning on Conversions.lean)

## Metrics

- Lines added: ~539 across 3 new files
- `sorry` count: 0
- `proof_wanted` count: 4 (2 deferred conversions, each with existence statement)
- New axioms: 0
