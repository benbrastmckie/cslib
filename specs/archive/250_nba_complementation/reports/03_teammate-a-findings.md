# NBA Complementation — Teammate A Findings (Primary Approach)

## Summary

This report provides a systematic analysis of implementation approaches for NBA
complementation in CSLib, with direct reference to the Kupferman-Vardi 2001 and
Schewe 2009 papers and a thorough audit of CSLib's existing NBA infrastructure.

---

## Key Findings

### Finding 1: Kupferman-Vardi Section 5.2 is the right target

KV2001 presents two equivalent formulations of the rank-based complementation:

- **Section 5.1**: Three-step pipeline through alternating automata (NBA → dual co-Büchi
  universal automaton → weak alternating automaton → NBA complement). The WAA step is
  the theoretical insight, but Section 5.2 unifies everything into a single direct construction.
- **Section 5.2**: Direct construction without alternating automata, working purely on
  the "run DAG" of the original NBA. KV2001 itself says (footnote 1, p. 17):
  *"We have found it easier to teach the direct construction."*

**Recommendation**: implement Section 5.2 of KV2001, not the alternating-automata pipeline.
This avoids the need to formalize weak alternating automata entirely.

### Finding 2: The direct construction has a clean 3-component state space

The complement automaton `A'` from KV2001 Section 5.2 has:

- **State space**: `R × 2^Q` where `R` is the set of level rankings
  `g : Q → {⊥, 0, 1, …, 2n}`, with the constraint that if `g(q)` is odd then `q ∉ F`
- **Initial state**: `(g_in, ∅)` where `g_in(q_in) = 2n` and `g_in(q) = ⊥` for `q ≠ q_in`
- **Transition function** `δ'((g, P), σ)`:
  - If `P ≠ ∅`: non-deterministically choose `g'` that `σ`-covers `g`,
    and set `P' = {q' : g'(q') ∈ 2ω, ∃q ∈ P, q' ∈ δ(q, σ)}`
    (tracking successors of P that still have even rank, minus those with odd rank)
  - If `P = ∅`: choose `g'` that `σ`-covers `g`,
    and set `P' = {q' : g'(q') ∈ 2ω}` (all even-ranked successors)
- **Accepting states**: `{(g, ∅)}` — when P becomes empty, all tracking obligations resolved
- **Key invariant**: `g'` must `σ`-cover `g`, meaning for all `q` with `g(q) ≠ ⊥` and
  `q' ∈ δ(q, σ)`, we have `0 ≤ g'(q') ≤ g(q)` (ranks decrease monotonically along edges)

The Schewe 2009 construction (Section 3) introduces a refined state space
`Q1 ∪ Q2` with `Q1 = 2^Q` (initial tracking phase) and `Q2 = {(S, O, f, i)}` where `f`
is a "tight level ranking" restricted to a specific even rank `i` under cyclic testing.
This refinement reduces the state count by an exponential factor but requires more
complex proof obligations.

### Finding 3: The correctness proof rests on Lemma 5.2 (KV2001)

The central correctness theorem (KV2001, Lemma 5.2, p. 17):

> **A rejects w iff there exists an odd ranking for the run DAG of A on w.**

An "odd ranking" for the run DAG `G` is a function `f : Q × ℕ → [2n]` such that:
1. If `f(q, l)` is odd, then `q ∉ F` (accepting states get only even ranks)
2. Ranks decrease monotonically along DAG edges
3. All infinite paths eventually stabilize at an odd rank

The proof has two parts:
- **Forward** (`odd ranking ⟹ rejection`): every path is eventually trapped in an odd
  rank, so all runs visit `F` only finitely often
- **Backward** (`rejection ⟹ odd ranking exists`): construct the ranking by an inductive
  removal procedure (define `G₀ = G`, then alternately remove "endangered" vertices
  (assign rank `2i`) and "safe" vertices (assign rank `2i+1`)); since |Q| is finite,
  this terminates in at most `n+1` rounds (Lemma 3.2 / Corollary 3.3 of KV2001)

This termination argument is the hardest proof obligation. It requires:
- A monotone inductive sequence of sub-DAGs
- A "width decrease" argument (Lemma 3.2 style)
- König's Lemma (infinite paths through infinite DAGs)

### Finding 4: No existing CSLib/Mathlib run DAG formalization

Searches for `RunDAG`, `LevelRanking`, `runDAG`, and `level_ranking` in CSLib/Mathlib
returned no results. The entire run DAG infrastructure must be built from scratch:

- `NA.Buchi.RunDAG` — the directed graph `G = (V, E)` with `V ⊆ Q × ℕ`
- `NA.Buchi.LevelRanking` — a function `Q → Fin (2n+1) ⊕ {⊥}` satisfying odd-rank
  and monotonicity constraints
- `NA.Buchi.OddRanking` — a level ranking that witnesses rejection
- `NA.Buchi.endangered` / `safe` — the inductive vertex removal predicates

The closest existing infrastructure:
- `Cslib.ωSequence.infOcc` and `frequently_in_finite_type` (used in Emptiness.lean)
  are directly relevant for the backward direction (stabilization at odd rank)
- `NA.addHist` provides the pattern for adding auxiliary "history" components to NBA
  states (used for the `P` component tracking even-ranked obligations)
- `LTS.OmegaExecution` and `extract_mTr` provide the run extraction toolkit
- `Cslib.LTS.CanReach` for reachability reasoning

### Finding 5: CSLib's existing language-level complement is via Büchi congruence, NOT the rank construction

`OmegaRegularLanguage.lean` line 251 (`IsRegular.compl`) proves closure under
complementation via the Büchi congruence and saturation argument — a completely different
approach that does not produce an explicit complement automaton. There is therefore **no
existing automaton-level complement** to reuse or extend. Task 250 fills this gap.

### Finding 6: The Schewe 2009 refinements are modular additions

The Schewe construction can be viewed as adding three independent optimizations over KV2001:
1. Replace all level rankings `R` with tight level rankings `T ⊂ R`
2. Split the state into a tracking phase `Q1` and a ranking phase `Q2`
3. Cycle through even ranks `{0, 2, ..., r-1}` instead of checking all at once

A staged implementation is natural: first implement KV2001 (Section 5.2 direct
construction), then optionally improve to Schewe's tight-ranking variant. The correctness
proof for KV2001 is self-contained. Schewe Section 3 correctness reuses KV2001's
Propositions 2.1 and 2.3 as Propositions (so they must be stated as standalone lemmas).

---

## Recommended Approach

### Approach: KV2001 Section 5.2 — Direct Rank-Based Construction

**Rationale**: The direct construction (Section 5.2) is the right target for a first
formalization because:
- It avoids alternating automata entirely (simpler type structure)
- KV2001 itself recommends it for teaching/implementation
- The state type `R × 2^Q` is straightforward to define in Lean 4
- The correctness proof is entirely self-contained within NBA theory
- The Schewe improvements can be layered on top as follow-up tasks

### Proposed File Structure

```
Cslib/Computability/Automata/NA/
├── RunDAG.lean             -- Run DAG definition and ranking theory
├── BuchiComplement.lean    -- The complement automaton construction + correctness
```

### Stage 1: `RunDAG.lean` — Core theory

Key definitions and theorems:

```lean
-- The run DAG: all reachable (state, level) pairs
def RunDAG (a : Buchi State Symbol) (xs : ωSequence Symbol) : Set (State × ℕ)

-- A level ranking: maps states to {0,1,...,2n} ∪ {⊥}
-- (⊥ means unreachable at that level)
structure LevelRanking (n : ℕ) (Q : Type*) where
  f : Q → Option (Fin (2 * n + 1))
  -- accepting states cannot have odd rank:
  -- if f q = some ⟨k, _⟩ and k is odd, then q ∉ F

-- A ranking for a run DAG: assigns ranks to all reachable (q, l) pairs
-- (decreasing along edges, odd only for non-accepting)
structure OddRanking (a : Buchi State Symbol) (xs : ωSequence Symbol) where
  rank : State → ℕ → Option (Fin (2 * Fintype.card State + 1))
  -- properties...

-- CENTRAL LEMMA (KV2001 Lemma 5.2)
theorem rejects_iff_odd_ranking [Finite State]
    (a : Buchi State Symbol) (xs : ωSequence Symbol) :
    xs ∉ ωAcceptor.language a ↔ ∃ r : OddRanking a xs, r.isOdd
```

### Stage 2: `BuchiComplement.lean` — Complement automaton

```lean
-- State type for the complement automaton
-- Level ranking (as a partial function) paired with an obligation set
def ComplementState (State : Type*) (n : ℕ) : Type* :=
  (State → Option (Fin (2 * n + 1))) × Finset State

-- The complement NBA
noncomputable def complement [Fintype State]
    (a : Buchi State Symbol) :
    Buchi (ComplementState State (Fintype.card State)) Symbol

-- Main correctness theorem
theorem complement_language [Fintype State] [Inhabited Symbol]
    (a : Buchi State Symbol) :
    ωAcceptor.language (complement a) = (ωAcceptor.language a)ᶜ
```

### Key proof obligations and estimated difficulty

| Proof obligation | Difficulty | Key tool |
|-----------------|------------|----------|
| Run DAG is well-defined (V finite per level) | Low | `Finite State` + `Finset.image` |
| Ranking decrease along edges (monotonicity) | Low | definition |
| Odd ranking ⟹ rejection (forward, Lemma 5.2a) | Low-Medium | `frequently_iff_strictMono` |
| Rejection ⟹ odd ranking exists (backward) | High | inductive sequence + König |
| König's Lemma (infinite DAG has infinite path) | Medium | `Finset.exists_ne_map_eq_of_card_lt` |
| Width decrease (Lemma 3.2 analogue) | Medium-High | induction on sub-DAGs |
| Complement transition function well-typed | Low | `Finset` operations |
| Complement accepts iff odd ranking (soundness) | Medium | Lemma 5.2 instantiation |
| Complement rejects iff no odd ranking (completeness) | Medium | Lemma 5.2 instantiation |
| `complement_language` (combining above) | Low once lemmas proved | |

### Estimated proof size

- `RunDAG.lean`: ~300-450 lines
- `BuchiComplement.lean`: ~250-350 lines

### Lean 4 type choices

The `LevelRanking` type should use `State → Option (Fin (2 * n + 1))` where `⊥ = none`
represents "state not tracked at this level." The `σ-covers` relation becomes:

```lean
def sigmaCovers (n : ℕ) (g g' : State → Option (Fin (2 * n + 1)))
    (a : Buchi State Symbol) (σ : Symbol) : Prop :=
  ∀ q q', g q ≠ none → a.Tr q σ q' → ∃ k, g' q' = some k ∧ k ≤ (g q).get (by exact...)
```

The obligation set `P : Finset State` tracks "states that have had even rank since the
last cut-point." The acceptance condition `{(g, ∅) | ...}` maps to `P = ∅`.

---

## Evidence from Literature

### KV2001 Section 5.2 Direct Construction (most faithful source)

The automaton is defined formally on pages 17-18 with:
- State: `R × 2^Q` (level rankings paired with obligation subsets)
- Initial state: `⟨g_in, ∅⟩` where `g_in(q_in) = 2n`, `g_in(q) = ⊥` for `q ≠ q_in`
- Transitions: non-deterministic choice of `g'` that `σ`-covers `g`, then update `P`
- Accepting: `R × {∅}`

KV2001 also notes (p. 18) that the state `(g, P)` in Section 5.2 corresponds exactly
to `(S, O)` in Section 5.1 with `S = {⟨q, g(q)⟩ : g(q) ≠ ⊥}` and
`O = {⟨q, g(q)⟩ : q ∈ P, g(q) ≠ ⊥}`. This bijection is worth proving as a lemma
if we want to formally connect the two constructions.

### Schewe 2009 Two-Phase Construction

The Schewe construction splits into:
- `Q1 = 2^Q` (first phase: pure subset tracking)
- `Q2 = {(S, O, f, i)}` (second phase: tight rankings, cycling even-rank test)

This is strictly more complex to formalize. The main new ingredient is "tightness":
a level ranking `f` of rank `r` is tight if it is onto `{1, 3, ..., r}` (all odd ranks
up to `r` are used). The Schewe state count is `O(tight(n+1))` vs KV2001's `O((6n)^n)`.

**Recommendation**: implement KV2001 first; leave Schewe as a follow-up (task 250b or
a sub-task of task 250).

---

## CSLib Infrastructure Reuse

### Directly Reusable

| Component | Location | How Used |
|-----------|----------|----------|
| `NA.Buchi` structure | `NA/Basic.lean` | The automaton type to complement |
| `NA.Run` | `NA/Basic.lean` | Runs of the original and complement automata |
| `NA.addHist` | `NA/Hist.lean` | Pattern for extending state with `P` component |
| `ωSequence.infOcc` | `Foundations/Data/OmegaSequence/InfOcc.lean` | Infinite occurrence |
| `frequently_in_finite_type` | same | Pigeonhole for finite state types |
| `frequently_iff_strictMono` | same | Extracting monotone witness for inf-freq |
| `LTS.OmegaExecution.extract_mTr` | `Foundations/Semantics/LTS/OmegaExecution.lean` | Path extraction |
| `LTS.CanReach` | `Foundations/Semantics/LTS/Basic.lean` | State reachability |

### Patterns to Follow

The BuchiInter construction (`NA/BuchiInter.lean`) is the closest pattern: it adds a
history component `Bool` to track which automaton to satisfy next. The complement
construction follows the same pattern but with a more complex history type.

The Emptiness proof (`NA/Emptiness.lean`) uses exactly the tools needed for the
backward direction: `frequently_in_finite_type` + `extract_mTr` to extract cycles.
The complement backward direction uses analogous techniques.

### Not Available (Must Build)

- Run DAG as a formal graph object
- `Finset.Reachable` from a starting set (or equivalent)
- König's Lemma for finite-width infinite DAGs
- Level ranking predicates (`isOdd`, `sigmaCovers`, `endangered`, `safe`)

König's Lemma may be derivable from `Finset.exists_ne_map_eq_of_card_lt` (pigeonhole)
applied to the "level" function; the argument is: if at every level there are finitely
many vertices, and the DAG is infinite, then some vertex must have infinitely many
successors, and by pigeonhole, some successor type must repeat, giving an infinite path.
A search for existing Mathlib infinite path / König lemmas:

```
lean_leansearch: "infinite directed graph has infinite path"
```

(not found in CSLib/Mathlib — must be proved locally)

---

## Notation and Naming Conventions

Following CSLib conventions:
- Use `Buchi` (not `NBA`) as the Lean name (consistent with existing `NA.Buchi`)
- Use `compl` or `complement` (consistent with `IsRegular.compl`)
- Use `ωAcceptor.language` for the language extractor (consistent with Emptiness.lean)
- Level rankings: `LevelRanking` (camelCase), not `level_ranking` (lint: `defsWithUnderscore`)
- Acceptance condition: `accept` field (consistent with `NA.Buchi.accept`)
- State namespace: `Cslib.Automata.NA.Buchi.complement` (consistent with existing namespace)

---

## Confidence Level: HIGH

The recommendation to use KV2001 Section 5.2 (direct construction) is grounded in:
- Full reading of both KV2001 and Schewe 2009 papers
- Verified absence of existing run DAG / level ranking infrastructure in CSLib/Mathlib
- Cross-check with CSLib's existing Emptiness.lean proof techniques
- Pattern alignment with existing NA construction files (Hist, BuchiInter)
- KV2001 itself recommends the direct construction for implementation

The main risk is the backward direction proof (rejection ⟹ odd ranking exists): this
requires the "width decrease" lemma (Lemma 3.2 of KV2001) which is a non-trivial
combinatorial argument. An alternative proof strategy using well-foundedness of the
lexicographic order on (sub-DAG, level) pairs may ease formalization.

---

## Literature Proof Structure (KV2001 Section 5.2)

Step-by-step for the correctness proof of the complement NBA:

1. **Define run DAG** `G = (V, E)` for `A` on word `w`
   - `V`: states reachable at each level
   - `E`: edges induced by the transition function

2. **Define rankings** for a run DAG `G`:
   - Rank function `f : V → [2n]` with odd-ranks only for non-accepting states
   - Ranks decrease monotonically along edges (second condition)
   - "Odd ranking": all paths eventually stabilize at an odd rank

3. **Lemma 5.2 (KV2001)**: `A` rejects `w` iff `G` has an odd ranking
   - Forward: odd ranking ⟹ all runs visit `F` only finitely often (direct)
   - Backward: rejection ⟹ construct odd ranking from inductive DAG sequence:
     - `G₀ = G`
     - `G_{2i+1} = G_{2i}` minus "endangered" vertices (rank `2i`)
     - `G_{2i+2} = G_{2i+1}` minus "safe" vertices (rank `2i+1`)
     - Terminates: `G_{2n+1} = ∅` (by width-decrease induction)
     - Odd ranking: the resulting function is odd

4. **Complement NBA `A'` guesses odd rankings**:
   - State: `(g, P)` where `g` is the current level ranking, `P` tracks
     even-ranked obligations
   - Non-deterministically advance `g` to `g'` that `σ`-covers `g`
   - Track which states need to reach an odd rank via `P`
   - Accept when `P = ∅` (all obligations resolved)

5. **Soundness** (`A'` accepts `w` ⟹ `A` rejects `w`):
   - An accepting run of `A'` produces a sequence of level rankings
   - This sequence witnesses an odd ranking for `G`
   - Apply Lemma 5.2 backward

6. **Completeness** (`A` rejects `w` ⟹ `A'` accepts `w`):
   - By Lemma 5.2, there exists an odd ranking `f` for `G`
   - Construct an accepting run of `A'` that follows `f`
   - The construction ensures `P` becomes `∅` infinitely often

Lean-specific translation notes:
- Step 2 ranks should use `Fin (2 * n + 1)` or `ℕ` bounded by `2n`
- Step 3's "width decrease" uses well-founded induction on `ncard` of sub-DAG levels
- The "σ-covers" relation in Step 4 is a Prop over pairs of functions
- Step 6 requires constructing the run non-computably (`Classical.choice`)

---

## Tactic Survey (Preliminary)

For the key proof obligations, the most useful tactics are likely:

| Goal type | Tactic strategy |
|-----------|----------------|
| Finite sub-DAG induction | `induction` on `Finset.card` |
| König's Lemma (infinite path) | Pigeonhole via `Finset.exists_ne_map_eq_of_card_lt` |
| Infinite occurrence stabilization | `frequently_iff_strictMono` + custom extraction |
| Odd ranking existence | `Classical.choice` + constructed witness |
| Transition well-typed | `simp`, `omega`, `Fin` arithmetic |
| Language membership | `simp [ωAcceptor.language]`, unfold `Accepts` |

`aesop` and `grind` should handle the structural parts (run membership, transition
unfolding). The combinatorial arguments (width decrease, König) will need explicit
induction.
