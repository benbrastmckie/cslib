# NBA Complementation — Teammate D: Strategic Horizons

## Summary

NBA complementation sits at the heart of the automata-theoretic verification pipeline.
This report assesses how task 250 fits into CSLib's long-term roadmap, which approach
serves the project best, and what API conventions will most benefit downstream users.

---

## Key Findings

### Finding 1: The Task Landscape Shows a Partially Realized Verification Pipeline

After examining `specs/state.json` and all related task directories:

| Task | Topic | Status |
|------|-------|--------|
| 241 | McNaughton's Theorem (NBA → DMA) | not_started |
| 242 | Vardi-Wolper Tableau (LTL → NBA) | not_started |
| 248 | NBA Emptiness Checking | completed |
| 250 | NBA Complementation | researching (this task) |
| 251 | Product Construction + Model Checking | researching |
| 252 | Acceptance Conditions Zoo | not_started |

Task 248 (emptiness) is complete and provides `HasReachableAcceptingCycle` and
`language_nonempty_iff`. Task 251 (product) is being researched in parallel. Tasks 241
and 242 are not yet started. This means:

1. **Complementation cannot wait for 241**: The McNaughton/Safra determinization-based
   route has no near-term foundation. A standalone rank-based construction is necessary.
2. **Task 251 is the primary downstream consumer**: The most immediate use of complement
   is in the model checking reduction `L(M ⊗ A_¬φ) = ∅`, which requires complement of
   the property automaton. This is the Vardi-Wolper pipeline's central step.
3. **Task 248 is the secondary consumer**: Complement + emptiness = universality
   checking. This is the algorithmic completeness direction: `L(A) = Σ^ω ↔ L(Ā) = ∅`.

### Finding 2: The Language-Level Complement Already Exists — But Provides No Construction

`OmegaRegularLanguage.lean` contains `IsRegular.compl`, which proves the *existence* of
a complement NBA via the Büchi congruence (an indirect, non-constructive argument). It
states: for any ω-regular language `p`, `pᶜ` is also ω-regular.

What is missing — and what task 250 provides — is an *explicit, computable construction*
`complementNBA : NA.Buchi State Symbol → NA.Buchi _ Symbol` together with a correctness
theorem `language_compl_eq`. These are what task 251 (model checking) needs: not just
that some complement exists, but a concrete automaton you can product with.

This distinction is critical for API design: task 250 should produce both the
**construction** (a function mapping NBA to NBA) and the **correctness lemma** (language
equation), fitting the pattern of `BuchiInter.lean` (`interNA` + `inter_language_eq`).

### Finding 3: Rank-Based Construction Is the Correct Strategic Choice

The determinization-based route (via task 241, McNaughton/Safra) has two problems:
- **Dependency**: Task 241 is not started and has no plan.
- **Complexity**: The doubly-exponential blow-up of McNaughton makes the correctness
  proof significantly harder and the resulting automaton less useful in practice.

The rank-based construction (Kupferman-Vardi 2001, refined by Schewe 2009) is
**self-contained** and has a direct correctness proof that does not depend on
determinization. It matches CSLib's construction-first philosophy: define a concrete
automaton, prove the language equation.

Later, if task 241 is completed, a second theorem can establish the McNaughton route as
a **corollary** (flip acceptance on the deterministic Muller automaton). This is a
natural follow-on, not a dependency.

### Finding 4: Proof Complexity Favors the Original Kupferman-Vardi Construction

The Schewe 2009 tight bound improves state complexity but makes the correctness proof
significantly harder (reduced rankings, tighter invariants). For a first CSLib
formalization, the original Kupferman-Vardi 2001 construction is the right target:

- Soundness: if the complement automaton accepts `xs`, then every run of the original
  NBA on `xs` is eventually doomed (has a suffix with no accepting state).
- Completeness: if `xs ∉ L(A)`, construct a ranking witnessing that all runs are doomed.

The Schewe tight-bound formalization is a natural task 250 sequel (task 250+), but
attempting it in the same task will dramatically increase complexity and risk of sorry.

### Finding 5: The BuchiInter Pattern Sets the Right Template

The existing `BuchiInter.lean` (138 lines) provides the architectural template:
1. Define the construction as a `noncomputable def` (state type may be infinite/complex)
2. Prove a `language_eq` theorem using `mem_ext` + set membership arguments
3. Use `Filter.frequently` / `atTop` for infinite recurrence conditions
4. Open `ωLanguage`, `ωAcceptor`, `Filter` locally

The complement construction will be more complex (rank tracking requires paired state
type `Finset State × (State → Option ℕ)` or similar), but the top-level structure
should mirror `BuchiInter`: a `def complementNA` and a `theorem complement_language_eq`.

### Finding 6: The Proposed File Location and Module Name

Following CSLib conventions:
- **File**: `Cslib/Computability/Automata/NA/BuchiCompl.lean`
  (mirrors `BuchiInter.lean`, `BuchiEquiv.lean`)
- **Namespace**: `Cslib.Automata.NA.Buchi`
- **Primary definition**: `complementNA (a : Buchi State Symbol) : Buchi _ Symbol`
- **Primary theorem**: `complement_language_eq : language (complementNA a) = (language a)ᶜ`

The `compl` suffix in theorem names follows the existing CSLib convention
(`IsRegular.compl`, `ωLanguage.compl_def`, `ωLanguage.mem_compl`).

### Finding 7: Phased Approach Is Feasible and Preferred Over Sorry Deferral

The rank-based construction has two clearly separable proof obligations:

**Phase 1 — Construction only**: Define `complementNA` with the run-DAG ranking
state type, initial states, transitions. Prove nothing. This is a definition phase.

**Phase 2 — Soundness**: If an accepting run of `complementNA a` exists, then `xs ∉ L(a)`.
This direction is usually proved by showing a valid ranking exists.

**Phase 3 — Completeness**: If `xs ∉ L(a)`, construct an accepting run of `complementNA a`.
This direction requires the "run DAG" argument: for any word not in `L(a)`, all runs
of `a` on it are "trapped" and rank assignments can be made consistently.

These phases can be submitted as a multi-phase implementation. Critically, **no sorry
deferral is acceptable** — each phase must be complete before the next is started. If
Phase 3 proves blocked, the task should transition to `[BLOCKED]` rather than using sorry.

### Finding 8: Adjacent Tasks Can Be Advanced Simultaneously

Two derivative theorems can be proved as immediate corollaries of `complement_language_eq`:

1. **Universality corollary** (bridges tasks 248 and 250):
   ```
   theorem language_univ_iff [Finite State] [Inhabited Symbol] (a : Buchi State Symbol) :
       language a = ⊤ ↔ ¬(complementNA a).HasReachableAcceptingCycle
   ```
   This is `language_eq_bot_iff` (from Emptiness.lean) applied to `complementNA a`.

2. **Language inclusion corollary** (bridges tasks 250 and 251):
   ```
   theorem language_le_iff (a b : Buchi _ Symbol) :
       language a ≤ language b ↔
       ¬(interNA (complementNA b) a).HasReachableAcceptingCycle
   ```
   These should be placed in a `BuchiComplApplications.lean` file or added to the bottom
   of `BuchiCompl.lean` after the main theorem.

Both corollaries require only `complement_language_eq` + existing infrastructure (no new
proof work). Implementing them simultaneously with the main construction maximizes value.

---

## Strategic Recommendations

### Recommendation 1: Implement Rank-Based Construction Standalone (Do Not Wait for Task 241)

Task 241 (McNaughton/Safra) is not started and adds no value to the complementation
construction. The rank-based approach is self-contained and directly serves tasks 248
and 251. Proceed without the determinization route.

After task 241 is eventually completed, a one-theorem corollary file
(`BuchiComplViaMcNaughton.lean`) can be added to derive complement from determinization,
documenting the alternative approach.

**Confidence**: High.

### Recommendation 2: Target the Kupferman-Vardi 2001 Construction, Not Schewe 2009

The Schewe tight-bound is a follow-on task (call it "task 250+"). The Kupferman-Vardi
construction is sufficient for all downstream uses (tasks 248, 251), and its correctness
proof is tractable within a single implementation task. Schewe's improvements are about
state-count tightness — irrelevant to the applications this task serves.

**Confidence**: High.

### Recommendation 3: API Should Expose Both the Automaton and the Language Equation

Do not expose only `complement_language_eq` as a black-box language closure result
(that is already in `OmegaRegularLanguage.lean`). The construction function
`complementNA` must be in the public API because:

1. Task 251 needs a concrete automaton to product with.
2. The universality corollary needs `complementNA a` to apply `HasReachableAcceptingCycle`.
3. Future tasks (intersection non-emptiness, synthesis problems) will need explicit
   complement automata.

**API surface** (what goes in the module's docstring header):
```
* `NA.Buchi.complementNA` -- the rank-based complement construction
* `NA.Buchi.complement_language_eq` -- language correctness theorem
* `NA.Buchi.language_univ_iff` -- universality corollary (optional, same file)
```

**Confidence**: High.

### Recommendation 4: Phased Implementation — Three Phases with No Sorry

Recommended phase structure for the implementation plan:

| Phase | Content | Deliverable |
|-------|---------|-------------|
| Phase 1 | State type, `complementNA` definition, helper lemmas for runs | Compiling `def complementNA` |
| Phase 2 | Soundness: accepting run implies word not in original language | `complement_language_eq` forward direction |
| Phase 3 | Completeness: word not in original implies accepting run exists | `complement_language_eq` full biconditional |

Each phase must be sorry-free before the next begins. If Phase 3 requires decomposing
into smaller lemmas (ranking consistency, run-DAG finiteness, etc.), those become
sub-phases tracked in the plan file, not sorry placeholders.

**Confidence**: High.

### Recommendation 5: Consider a Two-PR Strategy

Given the proof complexity, a two-PR strategy may be practical:

**PR A** (task 250, first PR): `complementNA` definition + soundness only (Phase 1 + Phase 2).
This is already a substantial contribution — a concrete complement automaton with a partial
correctness guarantee (no false positives).

**PR B** (task 250, second PR or separate task): Completeness direction + universality corollary.

This two-PR split reduces review burden and allows early feedback on the construction
definition before the harder completeness proof is reviewed. Both PRs must be sorry-free;
the split is not a sorry deferral — it is a scope deferral.

However, this recommendation is **conditional**: if the Kupferman-Vardi completeness proof
turns out to be tractable in Lean (within 500 lines), complete it in a single task. Only
split if Phase 3 proves unexpectedly difficult.

**Confidence**: Medium (depends on proof complexity discovered during implementation).

### Recommendation 6: Name and Namespace Conventions

Follow the existing `BuchiInter.lean` pattern:

```lean
-- In Cslib.Automata.NA.Buchi namespace:
noncomputable def complementNA (a : Buchi State Symbol) : Buchi _ Symbol := ...

theorem complement_language_eq (a : Buchi State Symbol) :
    language (complementNA a) = (language a)ᶜ := ...
```

The state type for the rank-based construction will be something like
`Finset State × (State → Option (Fin (2 * Fintype.card State + 1)))` for a finite-state
NBA. Use a `noncomputable def` wrapper to hide this complexity from callers.

**Confidence**: High.

---

## Confidence Level

| Area | Level | Rationale |
|------|-------|-----------|
| Rank-based over determinization | High | Clear architectural argument; task 241 not started |
| Kupferman-Vardi over Schewe | High | Sufficient for downstream; Schewe adds only tightness |
| API surface (complementNA + language_eq) | High | Follows BuchiInter pattern exactly |
| Phased implementation feasibility | High | Standard for complex constructions |
| Two-PR strategy | Medium | Depends on Phase 3 complexity discovered during implementation |
| Corollaries in same file | Medium | Value is clear; scope may push to follow-on |

Overall confidence: **High** for the strategic direction; **Medium** for timeline
estimates. The main risk is proof complexity in Phase 3 (completeness direction), which
requires constructing an explicit ranking for every word not in the language — a
non-trivial inductive argument that has historically been the hardest part to formalize
in other proof assistants.

---

## Appendix: Key CSLib Architecture Facts for Implementers

1. **NBA type**: `NA.Buchi State Symbol` in `Cslib/Computability/Automata/NA/Basic.lean`
   with `accept : Set State` and `ωAcceptor` instance using `∃ᶠ k in atTop, ss k ∈ a.accept`.

2. **Existing complement (language level only)**:
   `IsRegular.compl` in `OmegaRegularLanguage.lean` — proves existence but provides no
   construction.

3. **Template for new construction file**: Follow `BuchiInter.lean`:
   - Header: `public import Cslib.Computability.Automata.NA.Basic` (+ others as needed)
   - Namespace: `Cslib.Automata.NA.Buchi`
   - Opens: `Set Filter ωSequence ωLanguage ωAcceptor` (plus `Classical` for noncomputable)

4. **Task 248 emptiness result** (available as import):
   - `HasReachableAcceptingCycle`: the semantic criterion
   - `language_eq_bot_iff`: `language a = ⊥ ↔ ¬HasReachableAcceptingCycle a`

5. **No sorry policy**: CSLib's zero-debt completion gate prohibits sorry. All three
   phases must be complete before PR submission. If Phase 3 proves intractable, use
   `proof_wanted` (not sorry) and transition task to `[BLOCKED]`.
