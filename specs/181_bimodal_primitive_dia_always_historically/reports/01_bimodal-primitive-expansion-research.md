# Research Report: Primitive Diamond/Always/Historically for Bimodal Logic

## Task 181 — bimodal_primitive_dia_always_historically

### Motivation

The Bimodal layer is the union of Modal and Temporal, so its primitive set must include all primitives from both layers. After tasks 179 (Modal +diamond) and 180 (Temporal +allFuture/allPast), the Bimodal formula type grows from 8 to 11 constructors:

```
Current:   {atom, bot, imp, and, or, box, untl, snce}           — 8 primitives
Proposed:  {atom, bot, imp, and, or, box, dia, untl, snce,      — 11 primitives
            allFuture, allPast}
```

### Primitive Justification Summary

Each primitive pair reflects a classical equivalence that breaks in weaker logics:

| Pair | Classical equivalence | Breaks in |
|------|----------------------|-----------|
| `bot` + `imp` | `neg A = A → ⊥` | Minimal (neg weaker without explosion) |
| `and` + `or` | `A ∧ B = ¬(A → ¬B)` | Intuitionistic (non-interdefinable: Wajsberg 1938) |
| `box` + `dia` | `◇A = ¬□¬A` | Intuitionistic (double negation elimination fails) |
| `untl` + `snce` | Independent (Kamp basis) | N/A — always primitive |
| `allFuture` + `allPast` | `GA = ¬F(¬A)` | Intuitionistic (absence of counterexample ≠ universal truth) |

The 11-primitive design is the minimal set that supports all three propositional bases (minimal, intuitionistic, classical) across the full bimodal language. Removing any constructor would either lose expressiveness or bake in a classical assumption.

### Extension Architecture

The Bimodal layer sits at the top of the extension hierarchy:

```
Propositional:  {atom, bot, imp, and, or}                        — 5
     ↓ +box,dia
Modal:          {atom, bot, imp, and, or, box, dia}               — 7
     ↓ +untl,snce,allFuture,allPast
Temporal:       {atom, bot, imp, and, or, untl, snce,             — 9
                 allFuture, allPast}
                          ↘              ↙
Bimodal:        {atom, bot, imp, and, or, box, dia, untl, snce,  — 11
                 allFuture, allPast}
```

Each layer is a conservative extension of the one below — embedding homomorphisms map propositional formulas into modal/temporal/bimodal formulas. The embeddings are:
- `PropositionalEmbedding`: maps 5 propositional primitives into Bimodal (no change needed)
- `ModalEmbedding`: maps box → box, dia → dia (new: must map .dia)
- `TemporalEmbedding`: maps untl → untl, snce → snce, allFuture → allFuture, allPast → allPast (new: must map .allFuture, .allPast)

### Scope Assessment

This task follows the exact playbook established by task 177 (bimodal and/or propagation). The estimated scope is similar:

| Category | Estimated files | Change type |
|----------|----------------|------------|
| Syntax/Formula.lean | 1 | 3 new constructors + all match cases |
| Syntax/Context, Subformulas, SubformulaClosure | 4-6 | .dia/.allFuture/.allPast cases |
| Semantics (Truth, Validity, TaskFrame, etc.) | 4-5 | Structural truthAt clauses |
| ProofSystem (Axioms, Derivation, Instances, Substitution) | 4 | Axiom constructors |
| Embedding (Modal, Temporal) | 2 | Homomorphic mapping |
| Metalogic/Core (DerivationTree, DeductionTheorem, MCS) | 4 | Constructor cases |
| Metalogic/Soundness | 4 | Axiom soundness cases |
| Metalogic/Completeness + BXCanonical | 8-10 | Truth lemma, chronicle |
| Metalogic/ConservativeExtension | 4 | ExtFormula + lifting |
| Metalogic/Separation | 10-15 | Defs, hierarchy, closure |
| Metalogic/Decidability | 3-5 | Tableau, signed formulas |
| Metalogic/Algebraic | 5-8 | Lindenbaum, truth lemma |
| Theorems (Combinators, Perpetuity, etc.) | 3-5 | Diamond/G/H derived theorems |
| **Total** | **~50-65** | ~2000-2500 lines |

### Lessons from Task 177

Task 177 (bimodal and/or propagation) required ~15 agent dispatches across multiple rounds to fix all 127 files. Key lessons for task 181:

1. **Root-cause cascade pattern**: A small number of root-cause files (where constructors are defined or first pattern-matched) cause cascading failures in downstream files. Fix root causes first.

2. **Three error categories**:
   - "Missing cases" — mechanical, add constructor alternatives to pattern matches
   - "Function expected" / type mismatch — old proofs that relied on abbreviation expansion (e.g., treating `G(A)` as `¬F(¬A)` which is an `imp` expression)
   - Or-resolution style — proofs that used `implication_property` on derived connectives now need dedicated MCS helpers

3. **Separation layer is hardest**: The Separation subsystem (~17 files, ~10K lines) has the deepest pattern matching and most complex proofs. Budget extra time here.

4. **DenseValidity pattern**: Soundness proofs for dense models treat conjunction/disjunction/always/eventually as functions (from the abbreviation era). These need systematic rewriting to use structural destructuring.

### Interaction Between New Primitives

The three new constructors interact in bimodal-specific ways:

- **◇ and G**: `◇G(A)` ("it's possible that A always holds") is expressible and meaningful. In classical bimodal logic, `◇G(A) = ¬□¬¬F(¬A)` — a deeply nested expression that becomes clean with primitive ◇ and G.

- **◇ and H**: Similarly, `◇H(A)` ("it's possible that A has always held") becomes a simple primitive expression.

- **Box-temporal interaction axioms**: The existing axioms like `□A → GA` (modal-future) and `□A → HA` (modal-past) don't reference ◇/G/H in ways that change, but the proofs of their validity may need updating if they relied on abbreviation expansion.

### Classical Equivalences as Theorems

After this task, all three pairs of classical equivalences should be provable as theorems for classical bimodal logic (the system with Peirce's law):

1. `◇A ↔ ¬□¬A` — from task 179's modal diamond duality
2. `G(A) ↔ ¬F(¬A)` — from task 180's temporal always duality
3. `H(A) ↔ ¬P(¬A)` — from task 180's temporal historically duality

These validate that the 11-primitive design is a conservative extension of the current 8-primitive classical bimodal logic.

### Future Work Enabled

With the complete 11-primitive set, the following become expressible:

| Logic | Description | Enabled by |
|-------|------------|-----------|
| Intuitionistic bimodal | Full intuitionistic base with □, ◇, U, S, G, H | All primitives |
| Minimal bimodal | Johansson-style with bot-flexible models | botForces parameterization + all primitives |
| Constructive temporal | Davies-style staged computation | Primitive G + intuitionistic base |
| Intuitionistic S4 + temporal | Topological temporal logic | Primitive ◇ + G + intuitionistic base |

### References

- Fischer Servi, G. (1984). Axiomatisations for some intuitionistic modal logics.
- Simpson, A. (1994). *The Proof Theory and Semantics of Intuitionistic Modal Logic*. PhD thesis, Edinburgh.
- Boudou, J. et al. (2017). A decidable intuitionistic temporal logic. *CSL*.
- Wajsberg, M. (1938). Untersuchungen über den Aussagenkalkül von Heyting.
- Johansson, I. (1937). Der Minimalkalkül. *Compositio Mathematica*, 4, 119-136.
- Kamp, H. (1968). *Tense Logic and the Theory of Linear Order*. PhD thesis, UCLA.
