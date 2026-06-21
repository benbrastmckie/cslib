# NBA Complementation -- Teammate C Critical Analysis

## Key Findings

- **CSLib already has omega-regular complement closure at the language level**: `IsRegular.compl` in `OmegaRegularLanguage.lean` proves that the complement of an omega-regular language is omega-regular, using the Buchi congruence approach. This means the *existence* of a complementing NBA is already established. Task 250 is about providing an *explicit automaton construction*.

- **The rank-based construction (Kupferman-Vardi Section 5.2) requires entirely new infrastructure that does not exist in CSLib**: No DAG types, no ranking functions, no notion of "run DAG" (the DAG formed by all possible runs on a given word), no "level ranking" type. Every component must be built from scratch.

- **The correctness proof is the hard part, not the construction**: Defining the complement automaton (state space = `(Q -> Fin (2n+1) + bot) x Finset Q`, transitions defined by "covers" relation) is straightforward Lean. Proving `L(complement A) = Sigma^omega \ L(A)` requires the full ranking lemma machinery from Kupferman-Vardi Sections 3 and 5.2, including the "odd ranking exists iff no accepting run" direction.

- **The ranking lemma proof relies on Konig's lemma**: Lemma 3.2 in Kupferman-Vardi explicitly uses Konig's lemma ("by Konig's Lemma, G_{2i} contains an infinite path"). Mathlib has `Mathlib.Order.KonigLemma` but it is phrased in terms of partial orders (`exists_seq_covby_of_forall_covby_finite`), not graph-theoretic DAGs. The adaptation to the run DAG setting is non-trivial.

- **Task 241 (McNaughton's theorem / determinization) is NOT STARTED**: The determinization-based complementation route is completely blocked. The rank-based approach is the only viable path for task 250.

## Infrastructure Gap Analysis

### What CSLib Has (Reusable)

| Component | Location | Relevance |
|-----------|----------|-----------|
| `NA.Buchi` structure | `NA/Basic.lean` | Starting point for complement |
| `NA.Run`, `OmegaExecution` | `NA/Basic.lean`, `LTS/OmegaExecution.lean` | Run definition, finite path extraction |
| `ωAcceptor.language` | `Acceptors/OmegaAcceptor.lean` | Language definition |
| `frequently_in_finite_type` | `InfOcc.lean` | Pigeonhole for infinite state sequences |
| `frequently_iff_strictMono` | `InfOcc.lean` | Subsequence extraction |
| `OmegaExecution.flatten_mTr` | `LTS/OmegaExecution.lean` | Building infinite runs from repeated finite parts |
| `OmegaExecution.append` | `LTS/OmegaExecution.lean` | Prepending finite path to infinite run |
| `NA.Buchi.Emptiness` | `NA/Emptiness.lean` | Emptiness characterization (task 248) |
| `Nat.Even`, `Nat.Odd` | Mathlib | Parity reasoning |
| `Mathlib.Order.KonigLemma` | Mathlib | Konig's lemma (abstract form) |

### What CSLib Lacks (Must Build)

| Component | Difficulty | Description |
|-----------|------------|-------------|
| Run DAG definition | Medium | DAG of `(State x Nat)` pairs representing all possible runs on a fixed word |
| Level ranking type | Low | Function `Q -> Fin (2n+1) + {bot}` with parity constraint on accepting states |
| "Covers" relation | Low | `g' sigma-covers g` predicate on level rankings |
| Ranking function definition | High | The inductive `G_0 supset G_1 supset ...` construction, with "endangered" and "safe" vertex concepts |
| Odd ranking lemma | Very High | "A rejects w iff there is an odd ranking for the run DAG" -- the core mathematical content |
| Complement NBA definition | Low-Medium | State space `R x 2^Q`, transitions, acceptance condition |
| Correctness proof (easy direction) | Medium | "If complement accepts w, then A rejects w" |
| Correctness proof (hard direction) | Very High | "If A rejects w, then complement accepts w" -- requires the full ranking machinery |

### Fintype/Decidability Requirements

The NBA type parameters `State` and `Symbol` are unconstrained in the base definition. The complement construction requires:

- `[Finite State]` -- to bound ranks by `2|Q|` and to ensure the run DAG has finitely many states per level
- `[Fintype State]` or `[Finset State]` -- the complement automaton's state space involves `Q -> Fin (2n+1)` functions and subsets of Q; computing `|Q| = n` requires `Nat.card` or `Fintype.card`
- `[DecidableEq State]` -- likely needed for Finset membership in the `O` (obligation) tracking component
- `[DecidableEq Symbol]` -- possibly needed but less certain
- `[Inhabited Symbol]` -- for constructing accepting runs (as in the emptiness backward direction)

The existing emptiness checking uses `[Finite State]` (forward direction) and `[Inhabited Symbol]` (backward direction). The complement construction will need at minimum `[Finite State]` and likely `[Fintype State]` for concrete cardinality.

## Formalization Difficulty Assessment

| Component | Difficulty | Rationale |
|-----------|------------|-----------|
| Complement NBA definition (states, transitions, acceptance) | **Low-Medium** | Straightforward type definition; main issue is getting the `Option (Fin (2*n))` or `WithBot (Fin (2*n+1))` encoding right |
| Run DAG formalization | **Medium** | Need to define `Q_l` (active states at level l) inductively, and the edge relation -- conceptually clear but Lean encoding choices matter |
| Level ranking type and "covers" relation | **Low** | Simple predicates on functions |
| Ranking function construction (G_0 supset G_1 supset ...) | **High** | Inductive definition of the endangered/safe filtration requires careful reasoning about infinite subgraphs |
| Konig's lemma application | **High** | Mathlib's Konig lemma is in `Order.KonigLemma`, phrased abstractly; bridging to the DAG setting requires encoding the DAG as a partial order or using the `exists_seq_forall_proj_of_forall_finite` version for inverse systems |
| Odd ranking implies rejection (easy direction) | **Medium** | If every path is trapped in an odd rank, then every path visits accept only finitely often -- direct |
| Rejection implies odd ranking (hard direction) | **Very High** | This is the core difficulty: constructing the ranking function from the assumption that no run accepts. Requires proving G_{2n+1} is empty (Corollary 3.3) and that the resulting function satisfies all ranking properties |
| Correctness: L(complement) = complement of L(A) | **Very High** | Two directions, each requiring careful reasoning about nondeterministic guessing of level rankings and the obligation tracking mechanism |
| Overall integration and compilation | **Medium** | Ensuring all pieces fit together, handling universe issues, import management |

## Risk Assessment

### Risk 1: Ranking Lemma Proof Complexity (Likelihood: HIGH, Impact: CRITICAL)

The central mathematical content is Lemma 5.2 ("A rejects w iff there is an odd ranking for the run DAG"). The backward direction requires:
1. Defining the filtration G_0 supset G_1 supset ... inductively
2. Proving G_{2n} is finite (using Konig's lemma and induction on the width)
3. Proving G_{2n+1} is empty (corollary of above)
4. Constructing the ranking function
5. Proving it satisfies the odd ranking property

Each step involves non-trivial reasoning about infinite graphs, reachability, finiteness, and parity. This alone could consume the entire implementation budget.

**Mitigation**: Split into a separate subtask. Consider proving only the "easy direction" (odd ranking implies rejection) in task 250 and deferring the hard direction.

### Risk 2: Konig's Lemma Bridge (Likelihood: HIGH, Impact: HIGH)

Mathlib's `Mathlib.Order.KonigLemma` provides:
- `exists_seq_covby_of_forall_covby_finite`: for partial orders with finitely-branching cover relation, infinite upward sets have infinite paths
- `exists_seq_forall_proj_of_forall_finite`: for inverse systems with finite fibers, nonempty levels yield a consistent sequence

The run DAG is not naturally a partial order in Mathlib's sense. The "finitely branching" condition is satisfied (each state at level l has at most |delta(q, sigma_l)| successors at level l+1, and delta is finite-valued when State is Finite), but encoding this requires building a bridge. The `exists_seq_forall_proj_of_forall_finite` version (for inverse systems) may be more directly applicable, viewing the DAG levels as the inverse system.

**Mitigation**: Prove a custom Konig-like lemma for the run DAG directly, bypassing Mathlib's abstract version. This adds code but simplifies the proof structure.

### Risk 3: State Space Blow-Up in Lean Types (Likelihood: MEDIUM, Impact: MEDIUM)

The complement automaton has state space `(Q -> Fin (2n+1) + {bot}) x Finset Q`. In Lean, this would be something like `(State -> WithBot (Fin (2 * Nat.card State + 1))) x Finset State`. This requires:
- `Nat.card State` to compute `n`
- `Fintype State` instance for `Finset State`
- The state type of the complement depends on the cardinality of the original state type, which creates a dependent-type situation

This is manageable but requires careful Lean engineering. The `Fin (2 * n + 1)` type depends on a natural number that comes from the cardinality, which means the complement automaton's state type is universe-polymorphic in a non-trivial way.

**Mitigation**: Use `Nat.card` consistently and require `[Fintype State]` rather than just `[Finite State]`. Alternatively, use `Nat`-valued ranking functions with a separate boundedness proof.

### Risk 4: No Prior Lean 4 Formalization to Reference (Likelihood: HIGH, Impact: MEDIUM)

There is no known Lean 4 formalization of NBA complementation via the rank-based approach. The ctchou/AutomataTheory project (referenced in task 241) may have relevant infrastructure but focuses on McNaughton/determinization, and task 241 has not even started. There is no Lean 4 proof to adapt or port.

**Mitigation**: Rely on the paper's proof structure directly. The Kupferman-Vardi Section 5.2 presentation is relatively self-contained.

### Risk 5: Sorry Risk in Correctness Proof (Likelihood: MEDIUM-HIGH, Impact: HIGH)

Given the proof complexity (rating: Very High for multiple components), there is significant risk that the full correctness proof cannot be completed without sorry. The zero-debt policy strictly prohibits sorry deferral. If the hard direction of the ranking lemma proves intractable, the task would need to be marked BLOCKED.

**Mitigation**: Decompose into phases. Phase 1 defines the complement automaton and proves basic properties. Phase 2 proves the easy direction. Phase 3 tackles the hard direction. If Phase 3 blocks, Phases 1-2 still provide value.

## Scope Recommendation

**The task as stated is too large for a single implementation cycle.** The full rank-based complement with correctness proof is comparable in complexity to task 248 (emptiness checking) multiplied by 3-5x. Task 248 was a "simple" 2-phase task (~170 lines); the complement with full correctness would be 500-1000+ lines of non-trivial proof.

### Recommended Decomposition

**Phase 1 (Achievable, High Value)**: Define the complement NBA construction
- Define level ranking type
- Define the "covers" relation
- Define the complement automaton `NA.Buchi.complement`
- Prove basic structural lemmas (state space finiteness when original is finite)
- Target: ~100-150 lines

**Phase 2 (Achievable, Medium Value)**: Easy direction of correctness
- "If the complement accepts w, then w is not in L(A)"
- This direction does not require the ranking lemma -- it follows from the structure of the complement automaton directly
- Target: ~100-200 lines

**Phase 3 (Hard, High Value but Risky)**: Hard direction of correctness
- "If w is not in L(A), then the complement accepts w"
- Requires the full ranking function machinery
- Requires the odd ranking lemma
- Requires Konig's lemma application
- Target: ~300-500+ lines
- Risk: May block and require marking as [BLOCKED]

**Alternative Minimum Viable Approach**: Instead of the full rank-based correctness proof, prove `language (complement A) = (language A)^c` by connecting to the existing `IsRegular.compl` theorem. This would show that the *construction* produces the right answer without re-proving complement closure from scratch. However, this circular approach (using the language-level result to validate the automaton-level construction) may be unsatisfying.

### Another Alternative: Definitional-Only Phase

Define the complement automaton and prove `[Finite State] -> Finite (complement A).State` without proving the language equality. This is valuable as infrastructure for future work and can be done in one cycle. The correctness proof can be a follow-up task.

## Confidence Level

**Overall confidence in completing the full task (definition + correctness proof) in one implementation cycle: LOW (25-30%)**

The ranking lemma machinery is the bottleneck. If the scope is restricted to Phase 1 (definition) + Phase 2 (easy direction), confidence rises to **MEDIUM-HIGH (70-80%)**. If restricted to Phase 1 only (definition + finiteness), confidence is **HIGH (90%+)**.

**Recommendation**: Scope the implementation plan to Phase 1 + Phase 2, with Phase 3 as a separate follow-up task. This aligns with the zero-debt policy (no sorrys needed in Phases 1-2) and provides concrete, useful artifacts.

## Tactic Survey Notes

For the straightforward parts (complement definition, covers relation, basic properties):
- `simp`, `omega`, `decide` should handle most finiteness and cardinality reasoning
- `grind` is used extensively in existing CSLib automata code and should continue to work
- `aesop` may help with set membership reasoning in the obligation tracking component

For the ranking lemma (if attempted):
- Induction on `n` (number of states) for the filtration argument
- `Nat.strongRecOn` or well-founded recursion on the filtration index
- `Set.Finite` reasoning for the "endangered" predicate
- Parity reasoning via `Nat.even_or_odd`, `Nat.not_odd_iff_even`
- Mathlib's `Mathlib.Order.KonigLemma` for the infinite path extraction

No tactic survey was run via `lean_multi_attempt` as there is no proof file to test against yet.
