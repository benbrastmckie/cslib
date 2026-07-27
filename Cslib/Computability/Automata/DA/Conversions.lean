/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Computability.Automata.DA.Parity

/-! # Acceptance condition conversions (proof_wanted stubs)

This file collects `proof_wanted` declarations for the two hard directions of the
acceptance condition equivalence chain:

```
DBA → DRA → DMA → DPA → DRA → DMA
         ↑                    ↑
       (trivial)           (proved)
```

The **same-state-space** conversions that require complex constructions:

* `DA.Rabin.toParity_exists` — DRA → DPA using the *latest appearance record* (LAR)
  construction (Kupferman–Vardi 1998, Zielonka 1998). The DPA may have a larger state space
  (LAR blows up exponentially). This is **not** Piterman's 2006 determinization theorem,
  which converts NBA → DPA.

* `DA.Muller.toRabin_exists` — DMA → DRA, again with an exponential blowup in the number
  of pairs (bounded by `2^|Q|`). The conversion is straightforward (enumerate all accepting
  sets as Rabin pairs), but requires state-space type-lifting for a clean formalization.

## Summary of proved conversions (see `Rabin.lean`, `Parity.lean`, `BuchiChar.lean`)

| Source | Target | Proved | Notes |
|--------|--------|--------|-------|
| DBA    | DRA    | Yes    | `Buchi.toRabin_language_eq` — 1 Rabin pair |
| DBA    | DMA    | Yes    | `Buchi.toMuller_language_eq` — same state space |
| DRA    | DMA    | Yes    | `Rabin.toMuller_language_eq` — same state space |
| DPA    | DRA    | Yes    | `Parity.toRabin_language_eq` — infinitely many pairs |
| DRA    | DSA    | Yes    | `Rabin.toStreett_language_eq` — duality |
| DSA    | DRA    | Yes    | `Streett.toRabin_language_eq` — duality |
| DRA    | DPA    | Deferred | LAR construction; see below |
| DMA    | DRA    | Deferred | Exponential pairs; see below |

## References

* [O. Kupferman, M. Y. Vardi, *Freedom, Weakness, and Determinism: from Linear-Time
  to Branching-Time*, LICS 1998][KupfermanVardi1998]
* [W. Zielonka, *Infinite Games on Finitely Coloured Graphs with Applications to
  Automata on Infinite Trees*, TCS 1998][Zielonka1998]
* [W. Thomas, *Infinite Words*, Chapter 3][Thomas2003]
-/

-- This module consists exclusively of `proof_wanted` statements, which are elaborated and
-- discarded rather than added to the environment. It therefore declares nothing public (the
-- `@[expose] public section` below has nothing to expose) and the `privateModule` linter cannot
-- be satisfied without adding a declaration, which would change the file's mathematical content.
set_option linter.privateModule false

@[expose] public section

namespace Cslib.Automata.DA

open Set Filter Cslib.ωSequence ωLanguage ωAcceptor Acceptor
open scoped Cslib.FLTS

/-! ## Deferred: DRA → DPA (LAR construction) -/

/-- **DRA → DPA conversion** (deferred; LAR construction required).

Every deterministic Rabin automaton can be converted to a deterministic parity automaton
recognizing the same language. The construction uses the *latest appearance record* (LAR),
a data structure that tracks the order in which the Rabin pairs were last satisfied.

**Construction sketch** (Kupferman–Vardi 1998, Zielonka 1998):
Given DRA `a` over state space `State` with `k` Rabin pairs, the DPA has state space
`State × Fin k ! × Fin k` (current state × permutation of pairs × "top" index).
The priority function assigns even/odd colors based on whether the current "top" index
points to a satisfied Rabin pair.

**Note**: This is NOT Piterman's 2006 theorem, which converts *nondeterministic* Büchi
automata to deterministic parity automata. The present statement converts a deterministic
Rabin automaton to a deterministic parity automaton with a larger (but still finite) state
space.

**State space blowup**: The DPA state space is `|State| × k! × k` where `k` is the number
of Rabin pairs. For infinite Rabin pair sets, an additional finiteness hypothesis is needed. -/
proof_wanted Rabin.toParity_exists
    {State Symbol : Type*} [Fintype State] [DecidableEq State]
    (a : Rabin State Symbol) (h_fin : (a.pairs).Finite) :
    ∃ (S : Type) (_ : Finite S) (da : DA.Parity S Symbol), language da = language a

/-! ## Deferred: DMA → DRA (exponential pairs) -/

/-- **DMA → DRA conversion** (deferred; exponential pair blowup).

Every deterministic Muller automaton over a finite state space can be converted to a
deterministic Rabin automaton recognizing the same language.

**Construction sketch**: Given DMA `a` over state space `State` with acceptance family
`a.accept ⊆ 2^State`, the DRA can be taken with state space `State` and Rabin pairs
`{(State \ F, F) | F ∈ a.accept}`. However:
- The avoidance set `State \ F` may not enforce the exact `infOcc = F` condition;
  Muller acceptance requires *equality*, not just nonemptiness.
- A correct construction requires `|a.accept|` many pairs, one per accepting set.

**Finiteness requirement**: `a.accept` must be finite (guaranteed when `[Fintype State]`
since `a.accept ⊆ 𝒫 State` and `|𝒫 State| = 2^|State|`).

**See also**: `Rabin.toMuller_language_eq` for the reverse (easy) direction. -/
proof_wanted Muller.toRabin_exists
    {State Symbol : Type*} [Fintype State] [DecidableEq State]
    (a : Muller State Symbol) :
    ∃ (S : Type) (_ : Finite S) (da : DA.Rabin S Symbol), language da = language a

end Cslib.Automata.DA
