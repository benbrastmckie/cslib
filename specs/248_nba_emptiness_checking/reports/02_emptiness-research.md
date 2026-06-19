# NBA Emptiness Checking -- Research Report

## Summary

This report investigates approaches for formalizing NBA emptiness checking in Lean 4 within CSLib's existing automata infrastructure. The key finding is that a **semantic/declarative approach** best fits the existing codebase, rather than implementing algorithmic procedures (nested DFS or Tarjan's SCC). The central theorem is a characterization of language non-emptiness as the existence of a reachable accepting cycle, formulated in terms of the existing `NA.Run`, `MTr`, and `Filter.Frequently/atTop` infrastructure.

## Existing Infrastructure Analysis

### NBA and Buchi Acceptance (NA/Basic.lean)

The NBA is defined as `NA.Buchi State Symbol` extending `NA State Symbol` with an `accept : Set State` field. Acceptance is defined via the `ωAcceptor` instance:

```lean
instance : ωAcceptor (Buchi State Symbol) Symbol where
  Accepts (a : Buchi State Symbol) (xs : ωSequence Symbol) :=
    ∃ ss, a.Run xs ss ∧ ∃ᶠ k in atTop, ss k ∈ a.accept
```

where `a.Run xs ss` requires `ss 0 ∈ a.start` and `a.OmegaExecution ss xs` (transition relation holds at every step).

### LTS Reachability (LTS/Basic.lean)

The LTS already provides:
- `MTr`: multistep transitions via inductively-defined step sequences with label lists
- `CanReach s1 s2 := ∃ μs, lts.MTr s1 μs s2`: reachability predicate
- `Execution`: intermediate state sequences for multistep transitions

### OmegaSequence Infrastructure (InfOcc.lean)

Key lemma already available:
- `frequently_iff_strictMono`: `(∃ᶠ n in atTop, p n) ↔ ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ m, p (f m)` -- this is crucial for converting between the "infinitely often" filter formulation and constructive subsequence witnesses
- `frequently_in_finite_type`: In a finite type, `∃ᶠ k, xs k ∈ s` iff `∃ x ∈ s, ∃ᶠ k, xs k = x` -- pigeonhole for infinite occurrences

### Language and ω-Language Infrastructure

- `ωLanguage` is `Set (ωSequence α)` wrapped in a structure
- `ωAcceptor.language a = { xs | Accepts a xs }` 
- `IsRegular p := ∃ (State : Type) (_ : Finite State) (na : NA.Buchi State Symbol), language na = p`

### GNBA / LTL Integration

The GNBA tableau construction (GNBA.lean) already proves `gnba_language_eq`: the NBA language equals the formula's omega-language. The emptiness module would enable deciding whether a given NBA has any accepting runs, completing the pipeline from LTL formulas through GNBA to emptiness decisions.

## Recommended Approach: Semantic/Declarative

### Rationale

1. **No algorithmic infrastructure needed**: CSLib does not have (and does not need) executable graph traversal algorithms. The emptiness characterization is a mathematical theorem about when a Buchi language is non-empty.

2. **Perfect fit with existing API**: The `MTr` (multistep transition), `Run` (infinite run), `CanReach` (reachability), and `Filter.Frequently/atTop` predicates are exactly the building blocks needed.

3. **Reuse-first**: The infrastructure for pigeonhole in finite types (`frequently_in_finite_type` in InfOcc.lean) and the `frequently_iff_strictMono` equivalence are already available and directly applicable.

4. **Zero-debt completability**: The semantic approach uses well-understood proof techniques (constructing runs from cycle repetitions, extracting cycles from runs via pigeonhole) that can be completed without sorry.

### Why NOT Nested DFS or SCC Algorithms

- **Nested DFS**: Requires formalizing DFS stack invariants, marking schemes, and the subtle correctness argument. CSLib has no DFS infrastructure. This is an algorithmic verification task, not a mathematical one.
- **SCC-based**: Requires formalizing Tarjan's algorithm or equivalent, which is a significant undertaking. Mathlib's `SimpleGraph` uses undirected graphs and is not directly applicable to directed labeled transition systems.
- **Both are overkill**: For the purpose of connecting LTL-to-NBA translation to model checking, the semantic characterization theorem is what is needed. The algorithms are implementation optimizations for executable model checkers.

## Key Theorems to Formalize

### Definition: Reachable Accepting Cycle

```lean
/-- An NBA has a reachable accepting cycle if there exists:
    (1) a start state s₀ ∈ na.start
    (2) an accepting state q ∈ na.accept
    (3) s₀ can reach q via some label sequence
    (4) q can reach itself via some non-empty label sequence -/
def Buchi.HasReachableAcceptingCycle (a : Buchi State Symbol) : Prop :=
  ∃ s₀ ∈ a.start, ∃ q ∈ a.accept,
    a.toLTS.CanReach s₀ q ∧ ∃ μs, μs ≠ [] ∧ a.toLTS.MTr q μs q
```

Note: The `toLTS` coercion extracts the transition system from the `NA` structure. The non-emptiness of `μs` ensures the cycle is non-trivial (not just reflexivity).

### Theorem 1: Non-empty language implies reachable accepting cycle (finite state)

```lean
theorem Buchi.nonempty_language_of_hasReachableAcceptingCycle
    (a : Buchi State Symbol) [Finite State]
    (h : (ωAcceptor.language a).toSet.Nonempty) :
    a.HasReachableAcceptingCycle
```

**Proof strategy**:
1. Unfold: `h` gives `∃ xs ss, a.Run xs ss ∧ ∃ᶠ k in atTop, ss k ∈ a.accept`
2. By `frequently_in_finite_type` (since `State` is finite), obtain a specific accepting state `q ∈ a.accept` visited infinitely often: `∃ᶠ k in atTop, ss k = q`
3. By `frequently_iff_strictMono`, get a strictly monotonic function `f : ℕ → ℕ` with `ss (f m) = q` for all `m`
4. In particular, `ss (f 0) = q` and `ss (f 1) = q` with `f 0 < f 1`
5. The run from step 0 to step `f 0` gives reachability from `ss 0 ∈ a.start` to `q` (via `OmegaExecution.extract_mTr`)
6. The run from step `f 0` to step `f 1` gives `q` reaching itself (via `OmegaExecution.extract_mTr`)
7. Since `f 0 < f 1`, the label list is non-empty

### Theorem 2: Reachable accepting cycle implies non-empty language

```lean
theorem Buchi.hasReachableAcceptingCycle_of_nonempty_language
    (a : Buchi State Symbol) [Inhabited Symbol]
    (h : a.HasReachableAcceptingCycle) :
    (ωAcceptor.language a).toSet.Nonempty
```

**Proof strategy**:
1. Unfold: `h` gives `s₀, q, μs_reach, μs_cycle` with `a.MTr s₀ μs_reach q` and `a.MTr q μs_cycle q` and `μs_cycle ≠ []`
2. Construct an ω-sequence of symbols by repeating `μs_reach ++ μs_cycle ++ μs_cycle ++ ...` (i.e., `μs_reach ++ω (const μs_cycle).flatten`)
3. Construct the corresponding state run by concatenating the execution witnesses
4. The state `q` appears at positions `|μs_reach|, |μs_reach| + |μs_cycle|, |μs_reach| + 2|μs_cycle|, ...` which is infinitely often
5. Use `OmegaExecution.flatten_mTr` (or `append`) to build the infinite run from the finite pieces

**Key Mathlib/CSLib lemmas needed**:
- `OmegaExecution.append` for prepending the reachability path
- `OmegaExecution.flatten_mTr` for repeating the cycle
- `frequently_iff_strictMono` for showing `q` appears infinitely often

### Theorem 3: Emptiness characterization (combined)

```lean
theorem Buchi.language_nonempty_iff_hasReachableAcceptingCycle
    [Finite State] [Inhabited Symbol] (a : Buchi State Symbol) :
    (ωAcceptor.language a).toSet.Nonempty ↔ a.HasReachableAcceptingCycle
```

### Theorem 4: Language emptiness

```lean
theorem Buchi.language_eq_bot_iff
    [Finite State] [Inhabited Symbol] (a : Buchi State Symbol) :
    ωAcceptor.language a = ⊥ ↔ ¬a.HasReachableAcceptingCycle
```

## Proof Dependency Analysis

### Forward direction (nonempty -> cycle):

1. `ωAcceptor.language` / `Accepts` (NA/Basic.lean) -- unfold definition
2. `NA.Run` (NA/Basic.lean) -- start state + omega execution
3. `frequently_in_finite_type` (InfOcc.lean) -- pigeonhole: get a specific repeated accepting state
4. `frequently_iff_strictMono` (InfOcc.lean) -- convert to subsequence witnessing repetition
5. `OmegaExecution.extract_mTr` (LTS/OmegaExecution.lean) -- extract finite MTr from infinite run

### Backward direction (cycle -> nonempty):

1. `MTr.comp` (LTS/Basic.lean) -- compose reach path with cycle
2. `OmegaExecution.flatten_mTr` (LTS/OmegaExecution.lean) -- build infinite run from repeated cycles
3. `OmegaExecution.append` (LTS/OmegaExecution.lean) -- prepend reach path
4. `frequently_iff_strictMono` (InfOcc.lean) -- show q visited infinitely often

### Additional utilities that may be needed:

- `ωSequence.const` -- constant sequence for repeating cycle labels
- `ωSequence.flatten` -- flattening sequence of lists
- `List.length_pos_iff` -- converting between `μs ≠ []` and `μs.length > 0`

## File Structure

**Target file**: `Cslib/Computability/Automata/NA/Emptiness.lean`

```lean
/-
Copyright (c) 2026 ... All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/

module

public import Cslib.Computability.Automata.NA.Basic

/-! # NBA Emptiness Checking

Characterization of when a nondeterministic Büchi automaton (NBA) accepts at least
one ω-word. The key result is that the language is non-empty if and only if there
exists a reachable accepting cycle: a state reachable from a start state that is
accepting and lies on a non-trivial cycle.

## Main definitions

* `NA.Buchi.HasReachableAcceptingCycle` - the NBA has a reachable non-trivial cycle
  through an accepting state

## Main theorems

* `NA.Buchi.language_nonempty_iff_hasReachableAcceptingCycle` - language non-emptiness
  is equivalent to the existence of a reachable accepting cycle (requires `[Finite State]`
  and `[Inhabited Symbol]`)
* `NA.Buchi.language_eq_bot_iff` - language equals bottom iff no reachable accepting cycle

## References

* [C. Baier, J.-P. Katoen, *Principles of Model Checking*][BaierKatoen2008],
  Chapters 4.4, 7.3
-/
```

### Import Analysis

The file needs only `Cslib.Computability.Automata.NA.Basic` as a direct import. This transitively provides:
- `Cslib.Foundations.Data.OmegaSequence.InfOcc` (for `frequently_in_finite_type`, `frequently_iff_strictMono`)
- `Cslib.Foundations.Semantics.LTS.OmegaExecution` (for `OmegaExecution.extract_mTr`, `flatten_mTr`, `append`)
- `Cslib.Foundations.Semantics.LTS.Basic` (for `MTr`, `CanReach`)
- `Cslib.Computability.Automata.Acceptors.OmegaAcceptor` (for `ωAcceptor`, `language`)

No additional Mathlib imports should be needed beyond what is already transitively imported via Basic.lean.

## Complexity Estimate

- **Definition of `HasReachableAcceptingCycle`**: ~5 lines
- **Forward direction** (nonempty -> cycle): ~30-50 lines (pigeonhole + extraction)
- **Backward direction** (cycle -> nonempty): ~40-60 lines (run construction)
- **Combined iff**: ~5 lines
- **Emptiness characterization**: ~5 lines
- **Module boilerplate**: ~20 lines

**Total estimate**: 100-150 lines of Lean code

## Potential Challenges

1. **Run construction for backward direction**: Building the infinite run from repeated cycles requires careful use of `flatten_mTr`. The `[Inhabited Symbol]` hypothesis is needed because `flatten` requires it. The constant sequence `ωSequence.const μs_cycle` provides the label sequence, and `flatten_mTr` with `MTr.refl`/cycle repetition builds the state sequence.

2. **Extract_mTr alignment**: Extracting `MTr` from the infinite run at the right indices requires showing that `ωSequence.extract` on the label sequence gives the right list. The `extract_eq_take`/`take`/`drop` lemmas should handle this.

3. **Non-triviality of the cycle**: The condition `μs ≠ []` (equivalently `μs.length > 0`) is essential for showing the cycle visits `q` at strictly increasing positions. Without it, `MTr.refl` would give a trivial "cycle" at the same position, and the `StrictMono` condition for `frequently_iff_strictMono` would fail.

4. **Finiteness requirement**: The forward direction requires `[Finite State]` for the pigeonhole principle. This is the standard assumption for emptiness checking -- infinite-state automata can have non-empty languages without reachable accepting cycles in the finite sense.

## Namespace and Lint Considerations

- All declarations should be in `Cslib.Automata.NA.Buchi` namespace (consistent with existing code)
- Use `@[expose] public section` wrapper (consistent with other NA files)
- All public declarations need docstrings (docBlame linter)
- Prop-valued declarations should use `lemma`/`theorem` not `def` (defLemma linter)
- The predicate `HasReachableAcceptingCycle` is `Prop`-valued but a predicate definition, so `def` is appropriate (it defines a predicate, not proves one)
- Follow naming convention: `lowerCamelCase` for all declarations

## Literature Proof Structure

### Baier-Katoen Lemma 4.41 (Criterion for Nonemptiness of an NBA)

**Source**: Baier & Katoen, *Principles of Model Checking*, Chapter 4, Lemma 4.41.

**Statement**: For NBA A = (Q, Sigma, delta, Q_0, F), the following are equivalent:
- (a) L_omega(A) is non-empty
- (b) There exist q_0 in Q_0, q in F, w in Sigma*, v in Sigma+ such that q in delta*(q_0, w) intersect delta*(q, v)

That is: there exists a start state q_0, an accepting state q reachable from q_0 via word w, and q can reach itself via a non-empty word v.

**Proof structure**:

1. **(a) implies (b)**: Given an accepting run q_0, q_1, q_2, ..., pick q in F appearing infinitely often. Take two indices i < j with q_i = q_j = q. Set w = A_0 ... A_{i-1} (reach prefix) and v = A_i ... A_{j-1} (non-empty cycle). Then q in delta*(q_0, w) and q in delta*(q, v).

2. **(b) implies (a)**: Construct sigma = w v^omega. The run q_0 ... q ... q ... visits q infinitely often. Since q in F, the run is accepting, so sigma in L_omega(A).

### Courcoubetis-Vardi-Wolper-Yannakakis 1992

**Source**: Courcoubetis et al., "Memory-efficient algorithms for verification of temporal properties", 1992.

**Emptiness characterization (cited from Vardi & Wolper)**: "A Buchi automaton is nonempty iff it has some state f in F that is reachable from the initial state and reachable from itself (in one or more steps)."

The "one or more steps" qualifier is critical -- the cycle must be non-trivial. This matches the v in Sigma+ requirement in Baier-Katoen.

### Lean Translation Notes

The proof structure maps directly to CSLib's infrastructure:

| Literature Concept | CSLib Encoding |
|-------------------|----------------|
| q_0 in Q_0 | `ss 0 ∈ a.start` (from `NA.Run`) |
| q in F | `q ∈ a.accept` |
| q in delta*(q_0, w) | `a.toLTS.MTr (ss 0) (μs.extract 0 i) q` via `extract_mTr` |
| q in delta*(q, v) | `a.toLTS.MTr q (μs.extract i j) q` via `extract_mTr` |
| v non-empty (Sigma+) | `μs.extract i j ≠ []` follows from `i < j` |
| Accepting run from v^omega | `OmegaExecution.flatten_mTr` with `ωSequence.const` |
| q visited infinitely often | `frequently_iff_strictMono` with arithmetic positions |
| q in F picked from run | `frequently_in_finite_type` (pigeonhole) |

The step-by-step mapping confirms that no new infrastructure is needed -- every component of the proof has a direct CSLib counterpart.

## Connection to Model Checking Pipeline

This module is the key building block for:
1. **LTL model checking** (task 251): Given an LTS model M and LTL formula phi, construct the product NBA of M and the NBA for neg(phi). Emptiness of the product NBA means M satisfies phi.
2. **GNBA emptiness**: Since GNBAs are converted to NBAs (cycling counter construction in GNBA.lean), NBA emptiness immediately gives GNBA emptiness.
3. **Decidability**: For finite-state systems with finite alphabets, `HasReachableAcceptingCycle` is decidable (all quantifiers range over finite types), enabling computational emptiness checking.
