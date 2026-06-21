# NBA Complementation — Literature Sources

## Primary Sources (Rank-Based Approach)

### Kupferman & Vardi 2001 — Weak Alternating Automata Are Not That Weak
The foundational paper for the rank-based complementation construction. Defines the ranking
function approach: states ranked {0, ..., 2n}, odd-ranked states are "doomed" (will not visit
accepting states infinitely often). Section on Büchi complementation via rankings is the
primary reference for this task.

- `~/Projects/Literature/sources/kupferman_vardi_2001/Kupferman_Vardi_2001_Weak_Alternating_Automata.md` (985 lines)

### Schewe 2009 — Büchi Complementation Made Tight
Improves Kupferman-Vardi with tight upper bound O((0.96n)^{2n}). Introduces reduced rankings
and optimized subset-ranking pairs. The tighter construction may be overkill for first
formalization but provides the definitive complexity result.

- `~/Projects/Literature/sources/schewe_2009/Schewe_2009_Buchi_Complementation.md` (655 lines)

## Secondary Sources

### Piterman 2007 — From Nondeterministic Büchi and Streett to Deterministic Parity
Relevant if pursuing the determinization-based complementation route (task 241 dependency).
Covers the Safra-Piterman construction for determinizing Büchi automata.

- `~/Projects/Literature/sources/piterman_2007/Piterman_2007_Buchi_Streett_Parity.md` (1056 lines)

### Yan 2008 — Lower Bounds for Complementation of ω-Automata
Establishes lower bounds via the full automata technique. Useful for understanding why
complementation is inherently expensive and for verifying that the construction achieves
optimal complexity.

- `~/Projects/Literature/sources/yan_2008/Yan_2008_Lower_Bounds_Complementation.md` (1333 lines)

### Thomas 1997 — Languages, Automata, and Logic
Comprehensive survey of ω-automata theory. Chapter covers Büchi automata, complementation,
determinization, and the connection to monadic second-order logic. Good background reference.

- `~/Projects/Literature/sources/thomas_1997_languages/Thomas_1997_Languages_Automata_Logic.md` (3001 lines)

## Textbook Reference

### Baier & Katoen 2008 — Principles of Model Checking
Chapter 4 (§4.3) covers ω-automata fundamentals: NBA definition, ω-regular languages,
GNBA-to-NBA conversion, intersection via product, and complementation overview.

- `~/Projects/Literature/sources/baier_katoen_2008/Baier_Katoen_2008_part03.md` (4000 lines) — Ch. 4: ω-automata, NBA, product, complementation, persistence checking

## Not Available (Gaps)

| Reference | Notes |
|-----------|-------|
| Büchi 1962 | Foundational; not needed for construction details |
| Safra 1988 | Determinization construction; only needed if pursuing task 241 route |
| Kähler & Wilke 2008 | Slice-based alternative; low priority |
