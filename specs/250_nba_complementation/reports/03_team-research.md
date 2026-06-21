# Research Report: Task #250

**Task**: NBA Complementation
**Date**: 2026-06-20
**Mode**: Team Research (4 teammates)

## Summary

All four teammates converge on a single conclusion: the **Kupferman-Vardi 2001 Section 5.2 direct rank-based construction** is the only viable standalone approach for NBA complementation in CSLib. The determinization route is blocked (task 241 not started), the existing language-level complement (`IsRegular.compl`) is non-constructive and cannot yield an explicit automaton, and no compositional shortcut exists through current infrastructure.

The construction requires entirely new infrastructure (run DAGs, level rankings, the "covers" relation) — nothing in CSLib or Mathlib provides these. The key risk is the **ranking lemma's backward direction** (rejection implies odd ranking exists), which requires König's Lemma applied to run DAGs and is rated "Very High" difficulty. The recommended strategy is a phased implementation: construction + soundness first, with the hard completeness direction as a separable follow-up if it proves intractable.

## Key Findings

### Primary Approach (from Teammate A)

**KV2001 Section 5.2 — Direct Rank-Based Construction** is the recommended target. KV2001 itself describes this as "easier to teach" than the alternating-automata pipeline (Section 5.1). The construction has three components:

- **State space**: `(Q → Option (Fin (2n+1))) × Finset Q` — a level ranking paired with an obligation set P
- **Transitions**: non-deterministically choose `g'` that σ-covers `g`, then update P (tracking even-ranked successors)
- **Acceptance**: `P = ∅` (all tracking obligations resolved)

**Central correctness hinge** (KV2001 Lemma 5.2): *"A rejects w iff the run DAG of A on w has an odd ranking."* The forward direction (odd ranking ⟹ rejection) is direct. The backward direction (rejection ⟹ odd ranking exists) requires an inductive removal procedure over sub-DAGs with a width-decrease argument — this is the hardest proof obligation.

Two new files are proposed:
- `NA/RunDAG.lean` — run DAG definition, level ranking theory, odd ranking lemma (~300-450 lines)
- `NA/BuchiComplement.lean` — complement automaton construction + correctness (~250-350 lines)

**Confidence**: HIGH — grounded in full reading of both KV2001 and Schewe 2009, with exhaustive search of existing infrastructure.

### Alternative Approaches (from Teammate B)

Seven alternative paths were systematically evaluated. **All are blocked or inapplicable**:

1. **Language-level complement** (`IsRegular.compl`): purely existential — the witness NBA is buried in a `grind` call over Büchi congruence. Extracting it requires rebuilding the rank construction anyway.
2. **NBA↔language isomorphism**: does not exist. `IsRegular.iff_da_muller` (McNaughton's theorem) is `proof_wanted` — blocked by task 241.
3. **Determinization route** (Piterman/Safra): blocked by task 241 (not started).
4. **Intersection + determinization shortcut**: circular dependency.
5. **No NBA complement in CSLib or Mathlib**: `DFA.instCompl` exists for finite words only.
6. **Thomas 1997 confirms**: NBA cannot be complemented by flipping accept sets; no elementary trick exists.
7. **Piterman 2007 notes**: complementation is simpler than determinization, arguing for standalone rank-based.

**Key bonus recommendation**: the main value-add from task 250 is a `complement_language_eq` theorem that makes `IsRegular.compl` derivable as a constructive corollary with an explicit automaton witness.

**Confidence**: HIGH.

### Gaps and Shortcomings (from Critic)

The Critic identifies the following risks:

1. **Ranking Lemma Proof Complexity** (CRITICAL): The backward direction of Lemma 5.2 requires König's Lemma applied to run DAGs. Mathlib's `Order.KonigLemma` is phrased in terms of partial orders, not graph-theoretic DAGs — a non-trivial bridge is needed. This alone could consume the entire implementation budget.

2. **König's Lemma Bridge** (HIGH): The `exists_seq_forall_proj_of_forall_finite` version may be more applicable via inverse systems, but encoding the DAG structure requires careful work.

3. **State Space Type Engineering** (MEDIUM): The complement state type `(State → WithBot (Fin (2 * n + 1))) × Finset State` depends on `Fintype.card State`, creating dependent-type complexity. Requires `[Fintype State]` rather than just `[Finite State]`.

4. **No Prior Lean 4 Formalization** (MEDIUM): No known Lean 4 or Coq formalization of the rank-based construction exists to reference.

5. **Sorry Risk** (HIGH): If the hard direction proves intractable, the task would need `proof_wanted` and `[BLOCKED]` status.

**Scope recommendation**: The full task is too large for one cycle. Phases 1+2 (construction + easy direction) have 70-80% confidence; Phase 3 (hard direction) has only 25-30% confidence.

**Confidence in assessment**: HIGH.

### Strategic Horizons (from Horizons)

1. **Pipeline status**: Task 248 (emptiness) is complete; tasks 241 and 242 are not started. Complementation must proceed standalone.
2. **API design**: Mirror `BuchiInter.lean` — expose both `complementNA` (construction) and `complement_language_eq` (correctness). The construction must be public because task 251 needs a concrete automaton to product with.
3. **Phased implementation**: Three phases (construction, soundness, completeness), each sorry-free. No sorry deferral — use `proof_wanted` and `[BLOCKED]` if Phase 3 is intractable.
4. **Immediate corollaries**: Universality (`language_univ_iff` via complement + emptiness) and language inclusion (`language_le_iff` via complement + intersection) should be added in the same file.
5. **File location**: `Cslib/Computability/Automata/NA/BuchiCompl.lean`, following naming of `BuchiInter.lean` and `BuchiEquiv.lean`.

**Confidence**: HIGH.

## Synthesis

### Conflicts Resolved

**Scope conflict (Teammate A vs Teammate C)**: Teammate A assesses the full task as achievable (~650-750 lines total across two files) with HIGH confidence, while Teammate C rates full-task completion at only 25-30% confidence due to the ranking lemma's backward direction.

**Resolution**: Both assessments are valid at different scopes. Teammate A's estimates are correct for the *construction* and *forward direction* of correctness. Teammate C's skepticism is correct about the *backward direction* (rejection ⟹ odd ranking). The recommended approach is:
- **Phases 1+2** (construction + soundness): HIGH confidence, ~300-500 lines. This is Teammate A's core recommendation and is achievable in one cycle.
- **Phase 3** (completeness / backward direction): MEDIUM-LOW confidence, ~300-500+ lines. This should be planned as a phase but accepted as potentially requiring a follow-up task.

**File structure conflict (Teammate A vs Teammate D)**: Teammate A proposes two files (`RunDAG.lean` + `BuchiComplement.lean`). Teammate D proposes one file (`BuchiCompl.lean`).

**Resolution**: Adopt a hybrid — use `BuchiCompl.lean` as the primary file (matching `BuchiInter.lean` naming). If the run DAG infrastructure grows large enough to warrant separation, extract `RunDAG.lean` during implementation. Start with one file, split only if needed.

### Gaps Identified

1. **König's Lemma bridge**: No ready-made bridge from Mathlib's abstract König's Lemma to graph-theoretic run DAGs. May need a custom proof (~50-100 lines).
2. **`Fintype` vs `Finite` constraint**: The complement construction requires `[Fintype State]` for concrete cardinality, not just `[Finite State]`. This is a stronger assumption than the emptiness proof (task 248) required.
3. **Schewe refinements deferred**: The tight-bound construction (Schewe 2009) is out of scope for task 250. Should be a follow-up task.
4. **No test cases**: No concrete small-automaton test cases exist in CSLib for complementation. Adding a 2-3 state test NBA would aid debugging.

### Recommendations

**1. Approach**: Kupferman-Vardi 2001 Section 5.2 direct rank-based construction. Do NOT attempt the alternating-automata pipeline (Section 5.1) or Schewe's tight-ranking variant.

**2. File structure**:
```
Cslib/Computability/Automata/NA/BuchiCompl.lean
```
Primary definitions: `complementNA`, `complement_language_eq`. If run DAG theory exceeds ~200 lines, extract to `RunDAG.lean`.

**3. API surface** (mirroring `BuchiInter.lean`):
- `NA.Buchi.complementNA : Buchi State Symbol → Buchi _ Symbol`
- `NA.Buchi.complement_language_eq : language (complementNA a) = (language a)ᶜ`
- Corollaries: `language_univ_iff`, `language_le_iff` (in same file or follow-on)

**4. Implementation phases**:

| Phase | Content | Confidence | Lines (est.) |
|-------|---------|------------|-------------|
| Phase 1 | State type, `complementNA` definition, helper lemmas | 90%+ | 100-150 |
| Phase 2 | Soundness: complement accepts ⟹ original rejects | 70-80% | 150-250 |
| Phase 3 | Completeness: original rejects ⟹ complement accepts | 25-40% | 300-500+ |

**5. Risk mitigation**:
- Accept Phases 1+2 as the minimum viable deliverable
- Phase 3 should be attempted but may result in `proof_wanted` + `[BLOCKED]` if the ranking lemma backward direction proves intractable
- Consider a custom König's Lemma for run DAGs rather than bridging to Mathlib's abstract version
- Use `Nat`-valued ranking functions with separate boundedness proofs as an alternative to `Fin`-valued functions if dependent-type issues arise

**6. Type constraints**:
- `[Fintype State]` (not just `[Finite State]`) for the complement construction
- `[DecidableEq State]` for `Finset` membership in obligation tracking
- `[Inhabited Symbol]` for completeness direction (constructing accepting runs)

**7. Reusable infrastructure**:

| Component | Location | Role |
|-----------|----------|------|
| `NA.Buchi` | `NA/Basic.lean` | Input type |
| `NA.addHist` | `NA/Hist.lean` | History-state pattern for P component |
| `frequently_in_finite_type` | `InfOcc.lean` | Pigeonhole for stabilization |
| `frequently_iff_strictMono` | `InfOcc.lean` | Monotone subsequence extraction |
| `OmegaExecution.extract_mTr` | `LTS/OmegaExecution.lean` | Run extraction |
| `HasReachableAcceptingCycle` | `NA/Emptiness.lean` | Emptiness (for corollaries) |

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (rank-based construction) | completed | HIGH |
| B | Alternatives (compositional routes) | completed | HIGH |
| C | Critic (risks, feasibility, scope) | completed | HIGH |
| D | Horizons (strategic fit, API design) | completed | HIGH |

## References

- Kupferman, O., Vardi, M.Y. "Weak alternating automata are not that weak." *ACM TOCL*, 2(3):408-429, 2001. — Section 5.2: direct rank-based construction (primary source)
- Schewe, S. "Büchi complementation made tight." *STACS 2009*, LNCS 5404, pp. 661-672. — Tight bound refinement (deferred to follow-up task)
- Thomas, W. "Languages, automata, and logic." *Handbook of Formal Languages*, vol. 3, 1997, pp. 389-455. — Survey confirming two independent complementation routes
- Piterman, N. "From nondeterministic Büchi and Streett automata to deterministic parity automata." *LMCS*, 3(3):5, 2007. — Confirms complementation is simpler than determinization
- Yan, Q. "Lower bounds for complementation of ω-automata via the full automata technique." *LMCS*, 4(1):5, 2008. — Lower bounds establishing construction optimality
- Baier, C., Katoen, J.-P. *Principles of Model Checking*. MIT Press, 2008. Ch. 4. — Textbook treatment of ω-automata and complementation
