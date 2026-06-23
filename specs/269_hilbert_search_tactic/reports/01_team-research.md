# Research Report: Task #269

**Task**: hilbert_search_tactic
**Date**: 2026-06-22
**Mode**: Team Research (4 teammates, standard mode)
**Completed**: 2026-06-22

---

## Summary

The research establishes that building a generic bounded proof-search tactic for CSLib's
`InferenceSystem` is both strategically important and technically achievable, but requires
resolving a fundamental architectural choice before implementation begins: tactic-mode
(TacticM/MetaM elaboration plugin) versus term-mode (computable search function). The
correct design is a **two-layer architecture** — a term-mode search function at the
`DerivableIn S φ` level (returning `Option (DerivableIn S φ)`) as the core, wrapped by a
thin `TacticM` elaborator as the user-facing tactic. The key technical constraint is that
a generic tactic cannot pattern-match on the formula structure without additional `HasImpView`
/ `HasBoxView` typeclasses not currently in CSLib — the first implementation should target
axiom dispatch and modus ponens via local hypothesis scanning, deferring full DFS with
formula decomposition until those typeclasses exist. The implementation is novel: no
equivalent generic Hilbert proof-search tactic exists in the Lean 4 ecosystem.

---

## Key Findings

### Primary Approach (from Teammate A)

Teammate A provides the most detailed architectural analysis, grounded in both the
BimodalLogic `modal_search` reference (~700 lines in Helpers.lean + Commands.lean) and CSLib's
concrete `InferenceSystem` API.

**Critical finding**: The BimodalLogic tactic works by pattern-matching on the *shape* of a
concrete `DerivationTree` expression. CSLib's `InferenceSystem.derivation S φ` is opaque —
it dispatches to whatever concrete type the instance provides. This makes direct porting
impossible. The correct target for `hilbert_search` is `InferenceSystem.DerivableIn S φ`
(the `Nonempty (S⇓φ)` wrapper), which is the common interface all instances share.

**Goal extraction pattern** (meta-level):
```lean
def extractDerivableGoal (goalType : Expr) : MetaM (Option (Expr × Expr)) := do
  let goalType ← whnf goalType
  match goalType with
  | .app (.app (.app (.app (.const ``InferenceSystem.DerivableIn _) S) _α) _inst) formula =>
    return some (S, formula)
  | _ => return none
```

**Axiom dispatch**: Rather than iterating hardcoded constructor names (as in BimodalLogic),
use `observing? do goal.apply (mkConst axiomMethod)` over a list of `HasAxiom*` typeclass
methods (`HasAxiomImplyK.implyK`, `HasAxiomK.K`, etc.). The `observing?` pattern from
BimodalLogic is directly portable — it avoids corrupting mvar state on failure.

**Assumption handling**: CSLib's `DerivableIn` goals carry no context. "Assumption lookup"
must scan Lean's local context for hypotheses of type `DerivableIn S ψ` and chain them via
`ModusPonens.mp`.

**Scope constraint**: `hilbert_search` operates on `DerivableIn S φ` goals only (empty-context
Hilbert proofs). Context-relative goals `Γ ⊢ φ` are out of scope — users must use
`listDeduction` or explicit `DerivationTree` constructors for those.

**Proposed file location**: `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` under
the `Cslib.Logic` namespace.

---

### Alternative Approaches (from Teammate B)

Teammate B surveys prior art and confirms there is zero prior Hilbert proof-search
infrastructure in CSLib. Key alternative findings:

**Mathlib prior art**: `Mathlib.Tactic.ITauto` (744 lines) uses a two-phase
reify-then-replay architecture — find the proof structure in a reified domain, then apply
it to the Lean goal via MetaM. The reification approach avoids manipulating MVarIds during
search. Mathlib's `TFAE.dfs` implements a DFS over implication graphs nearly identical in
structure to Hilbert backward search.

**Aesop assessment**: Aesop is available (transitive dependency via Mathlib) and supports
custom rule registration. However, Aesop cannot do formula-directed backward reasoning
(e.g., knowing to decompose `DerivableIn S (imp φ ψ)` into proving φ → ψ and ψ independently).
It is suitable for simple axiom closure cases but insufficient for a full DFS.

**The buildCompositionalProof precedent**: `Cslib/Logics/Bimodal/Metalogic/Decidability/
ProofExtraction.lean` (lines 155-204) already implements the fuel-based recursive pattern
the generic search should follow:
```lean
def buildCompositionalProof (phi : Formula Atom) (fuel : Nat) :
    Option (DerivationTree .Base [] phi) :=
  if fuel = 0 then none
  else match tryAxiomProof phi with
       | some proof => some proof
       | none => match phi with
                 | .box inner => ...
                 | .imp a b => ...
```

**Recommended architecture (Tier 1 + Tier 2)**:
- Tier 1 (~400 lines): Term-mode search functions parameterized by `[MinimalHilbert S]`,
  `[ModalHilbert S]`, etc., returning `Option (DerivableIn S φ)`. No metaprogramming.
  Immediately testable via `#eval`/`#check`.
- Tier 2 (~50-80 lines): Thin `TacticM` elaborator wrapping Tier 1. Lives in a
  `meta section`.

**Against pure MetaM from scratch**: CSLib contribution standards strongly prefer
term-mode definitions. Only `Relation/Attr.lean` uses `Lean.Elab.*`. A heavy MetaM tactic
would be inconsistent with CSLib's code style and likely require Zulip sign-off.

---

### Gaps and Shortcomings (from Critic)

Teammate C identifies the most substantive architectural risks and unresolved design
questions. These findings carry high confidence and directly shape the recommendations.

**Central gap — formula decomposition**: For a genuine DFS (not just axiom dispatch), the
search must decompose formulas: given a goal `DerivableIn S (imp φ ψ)`, it must extract
`φ` and `ψ`. The `InferenceSystem S α` typeclass provides only `derivation (a : α) : Sort v`
— no decomposition interface. At the MetaM level this is achievable via `whnf` + expression
matching, but at the term-mode level it requires additional typeclasses not currently in CSLib:
```lean
class HasImpView (F : Type*) [HasImp F] where
  viewImp : F → Option (F × F)
```
Without `HasImpView`/`HasBoxView`, the tactic can dispatch axioms but cannot perform
structural backward decomposition (the "D" in DFS).

**Tactic vs term-mode is unresolved in the task description**: The task says "build a tactic"
and cites a ~700-line tactic implementation, but CSLib's architecture and contribution
standards favor term-mode. This ambiguity must be resolved before implementation to avoid
teammates implementing incompatible things.

**Scope underestimated**: A genuinely generic implementation covering propositional, modal,
temporal, and bimodal logics requires 600-1200 lines minimum (new typeclasses + search loop
+ per-logic instances + tests). The "700 lines" estimate from the task description assumes
a bimodal-specific port, not a generic implementation.

**`boundedSearchWithProofStub` is bimodal-specific**: The stub in `AxiomMatcher.lean:456`
is typed to `Option (DerivationTree FrameClass.Base [] φ)` — filling it in does not produce
a generic component. Teammates should not confuse "filling the stub" with "building the
generic tactic."

**Error transparency**: A proof-search tactic that returns only "search failed" on failure
will be rejected in PR review on usability grounds. The tactic must report at minimum: depth
reached, last formula attempted, suggestion to increase depth.

**Assumption lookup ambiguity**: The task description lists "assumption lookup" as a search
strategy, but this has two incompatible meanings: (a) scanning Lean's local context for
`DerivableIn S ψ` hypotheses (for the TacticM path), or (b) passing an explicit `List F`
to the term-mode search. These require different APIs.

**Soundness specification**: The implementation must not use `Lean.Meta.mkSorry` or
manipulate metavariables incorrectly. The term-mode path is automatically sound by typing;
the TacticM path requires explicit soundness specification.

**`DecidableEq` on abstract `F`**: The abstract `F` in `InferenceSystem S F` has no
`DecidableEq` constraint. Adding `[DecidableEq F]` to the search signature is the correct
resolution (all concrete CSLib formula types have it), but it must appear explicitly in the
type signature.

---

### Strategic Horizons (from Teammate D)

Teammate D contextualizes the task within CSLib's broader mission and adjacent opportunities.

**Foundational infrastructure, not nice-to-have**: CSLib has 20+ registered proof systems
with zero automation to use them. Every theorem in `Foundations/Logic/Theorems/` requires
manual `ModusPonens.mp` chains. A working `hilbert_search` eliminates this asymmetry —
adding a new proof system would unlock immediate automation.

**Three enabled opportunities**:
1. Zero-boilerplate proof systems: new logics can prove theorems immediately after registering
   instances
2. Decision procedure integration: layered automation architecture (fast path via registered
   decision procedure → bounded DFS → user-guided)
3. Generic MCS infrastructure: `Foundations/Logic/Metalogic/` has generic `SetConsistent` /
   `Lindenbaum` theorems requiring manual `DerivableIn S (imp φ ψ)` discharges; `hilbert_search`
   would close these automatically

**Phased implementation is correct**: Propositional first (`MinimalHilbert`), then classical
(`ClassicalHilbert`), then modal (`ModalHilbert`), then temporal/bimodal. This matches the
typeclass hierarchy and allows incremental verification.

**Ecosystem novelty**: No generic Hilbert proof-search tactic exists for modal/temporal logics
in the Lean 4 ecosystem. CSLib would be first. The cslib Zulip community will likely be
receptive — generic automation fits the "shared infrastructure" mission.

**Proof-by-reflection is the ideal long-term path**: Define `BoundedDerivable S φ n : Bool`,
prove soundness, use `decide`. Requires `[Fintype F]` or computable formula enumeration —
not available generically today but the right long-term direction.

**Task synergies**: Task 266 (normalization tags) unlocks concrete modal instances needed by
`hilbert_search`. Task 278 (simp/grind tags) is independent. Task 279 (sequent calculus LK)
is orthogonal — `hilbert_search` does not apply to sequent goals.

---

## Synthesis

### Conflicts Resolved

**Conflict 1: Tactic-mode (A) vs term-mode search (B, D)**

Teammate A advocates for a full `TacticM`/`MetaM` elaboration tactic following BimodalLogic's
architecture. Teammates B and D advocate for a term-mode search function (Tier 1) with a
thin tactic wrapper (Tier 2). The Critic flags the unresolved ambiguity as high-risk.

**Resolution: Two-layer architecture wins.** The evidence for term-mode Tier 1 is stronger:
- CSLib contribution standards strongly prefer term-mode; only one file in CSLib currently
  uses `Lean.Elab.*` (Attr.lean), and that is for a notation attribute
- Teammate B's `buildCompositionalProof` precedent validates the term-mode approach as already
  present in CSLib (ProofExtraction.lean, lines 155-204) — the generic tactic follows the
  same pattern
- The term-mode Tier 1 is independently useful (callable directly from proofs) and testable
  before the tactic wrapper exists
- The thin Tier 2 TacticM wrapper (~50-80 lines) preserves the user-facing tactic interface
  without committing to a heavy MetaM implementation

The BimodalLogic `modal_search` architecture is the correct model for understanding what the
tactic must do, but not the right model for how to implement it in CSLib.

**Conflict 2: Aesop sufficiency (B: "insufficient") vs Aesop viability (C: "already available")**

Teammate B concludes Aesop is insufficient for formula-directed backward reasoning. The Critic
notes Aesop is already available and suggests it might handle `DerivableIn` goals with
appropriate rule registrations. Teammate D assesses Aesop as a valid long-term direction but
not the right first step.

**Resolution: Aesop is insufficient for the core DFS; viable only as a post-hoc complement.**
The evidence is clear: Aesop performs best-first search over Lean proof goals but cannot
"see inside" the formula `φ` to decompose `imp φ ψ` into subgoals without a formula
decomposition oracle. The modus ponens backward decomposition — the most important search
step — requires knowing the antecedent, which Aesop cannot determine without formula-directed
dispatch. Aesop can be used after a `hilbert_search` phase to close residual propositional
goals, but cannot replace the custom search. The Critic's concern about Aesop being "already
available" is a research question worth Zulip discussion, not a blocker.

**Conflict 3: Scope estimate — 700 lines (A, D) vs 600-1200 lines (C)**

Teammate A implicitly accepts the task's "~700 lines" estimate. The Critic argues a genuinely
generic implementation requires 600-1200 lines. Teammate D's phased plan is consistent with
the Critic's estimate when all four logic levels are included.

**Resolution: Critic's estimate is correct for the full generic version; the phased approach
resolves the tension.** Phase 1 (propositional, `MinimalHilbert`) is ~200-300 lines and
deliverable as a standalone PR. Full genericity across all four logic levels is a multi-phase
effort. The implementation plan should scope Phase 1 to propositional + minimal modal and
treat temporal/bimodal as later phases. This matches CSLib's incremental contribution model.

**Conflict 4: Generic formula decomposition at meta-level (A: feasible) vs term-mode (C: requires new typeclasses)**

Teammate A asserts that formula decomposition is possible at the MetaM level via `whnf` +
expression matching. The Critic asserts that term-mode formula decomposition requires new
`HasImpView`/`HasBoxView` typeclasses. These are not in conflict — they operate at different
layers.

**Resolution: Both are correct in their respective layers.** The TacticM elaborator (Tier 2)
CAN do formula decomposition via MetaM expression inspection using `whnf`. The term-mode
search function (Tier 1) CANNOT do formula decomposition without `HasImpView`. This means
the two layers have different capabilities: Tier 1 handles axiom dispatch and local hypothesis
MP chaining; full structural DFS (box introduction, imp decomposition) belongs to Tier 2. This
division of responsibility should be made explicit in the implementation plan.

---

### Coverage Gaps

**Gap 1: `HasImpView`/`HasBoxView` typeclass design**

No teammate analyzed whether these typeclasses should be added to CSLib's typeclass hierarchy
or handled differently. This is the gating question for full term-mode DFS. The implementation
plan should include a Zulip discussion item on this design decision.

**Gap 2: Tactic error message design**

The Critic flags this as a hard requirement for PR acceptance, but no teammate proposed a
concrete error message format. The plan needs a spec: at minimum, depth-reached reporting,
last-formula attempted, and "try increasing depth" suggestion.

**Gap 3: Temporal and bimodal rules**

Teammate B explicitly flags that the temporal formula case (`Until`/`Since`) needs a dedicated
subgoal strategy — the `imp` decomposition pattern does not cover `untl`/`snce` constructors.
Teammate A notes temporal necessitation (`TemporalNecessitation.tempNec`/`tempNecPast`) but
does not analyze what formula patterns trigger it. The plan should defer temporal/bimodal to
a later phase rather than attempt it in Phase 1.

**Gap 4: Integration tests and performance specification**

The Critic notes CSLib has no infrastructure for tactic timing/resource-bounded performance
tests. No teammate proposed what the test suite should look like beyond "positive and negative
cases." The plan needs a minimal test specification: which formulas must succeed, which must
fail within bound, and what timing is acceptable.

**Gap 5: Interaction with `@[simp]` and `@[aesop]` in existing proofs**

The Critic flags this risk but no teammate analyzed whether `hilbert_search` could be
accidentally triggered by simp or cause recursive loops. The implementation plan should specify
that `hilbert_search` must NOT be registered as `@[simp]` or `@[aesop]` and must not call
`aesop` internally.

**Gap 6: Universe polymorphism**

Teammate B mentions possible "unification failures on universe polymorphism" when calling
`ModusPonens.mp` and `Necessitation.nec` from term-mode, but does not analyze this concretely.
The implementation phase should prototype the universe polymorphism behavior early.

---

### Recommendations

1. **Resolve tactic-vs-term-mode in the plan**: Adopt the two-layer architecture explicitly.
   Tier 1 is a term-mode `def hilbertSearch [DecidableEq F] [MinimalHilbert S (F := F)] ...`
   returning `Option (DerivableIn S φ)`. Tier 2 is a thin `meta section` `TacticM` wrapper.
   Document this split in the plan as a design decision, not an implementation detail.

2. **Phase 1 scope: propositional + minimal modal only**. Target `MinimalHilbert` (implyK,
   implyS, modus ponens) and `ClassicalHilbert` (add EFQ, Peirce). Modal necessitation and
   temporal rules should be Phase 2+. This produces a PR-ready deliverable in ~200-300 lines.

3. **Do NOT fill `boundedSearchWithProofStub` in AxiomMatcher.lean** as the primary
   deliverable. That stub is bimodal-specific and typed to `DerivationTree FrameClass.Base`.
   The generic `hilbert_search` belongs in `Cslib/Foundations/Logic/ProofSearch.lean` or
   `Cslib/Foundations/Logic/Automation/HilbertSearch.lean`.

4. **Add `[DecidableEq F]` to all search function signatures** from the start. This is the
   correct constraint (all concrete CSLib formula types satisfy it) and avoids late-stage API
   breakage.

5. **Implement formula decomposition exclusively in Tier 2 (TacticM layer)**. The TacticM
   elaborator can use `whnf` + MetaM expression matching to inspect formula structure without
   requiring new `HasImpView` typeclasses. Reserve `HasImpView` design as a post-Phase-1
   Zulip discussion item.

6. **Design error messages before implementing search**. Specify: on depth exhaustion, report
   the goal formula and depth attempted; on structural mismatch, report "goal is not a
   `DerivableIn` statement." This is a PR acceptance requirement.

7. **Raise three questions on Zulip before Phase 2**:
   - Should `HasImpView`/`HasBoxView` be added to the typeclass hierarchy?
   - Preferred file location: `Foundations/Logic/Automation/` vs `Logics/Tactics/`?
   - Has anyone profiled Aesop with `@[aesop apply (rule_sets := [hilbert])]` on `DerivableIn`
     goals?

8. **Test plan must include both success and depth-limit cases**. Minimum test suite: `identity`
   (`⊢ φ → φ`), `imp_trans` (`⊢ (φ → ψ) → (ψ → χ) → (φ → χ)`), `K` axiom instantiation,
   and a formula that exceeds depth 5 to verify failure behavior.

9. **Use the `observing?` pattern from BimodalLogic** for the TacticM layer's axiom dispatch.
   This is the proven pattern for non-destructive goal application attempts and is directly
   portable.

10. **Do not register `hilbert_search` as `@[simp]` or `@[aesop]`**. The tactic must be
    explicitly invoked only. Document this constraint in the file's module docstring.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary Architecture (BimodalLogic port, CSLib target API) | completed | Medium-High |
| B | Alternative Patterns (prior art, two-tier design, aesop assessment) | completed | High |
| C | Critic (design gaps, scope risks, unresolved ambiguities) | completed | High |
| D | Horizons (strategic importance, phased plan, ecosystem context) | completed | High |

---

## References

### CSLib Source Files

| File | Relevance |
|------|-----------|
| `Cslib/Foundations/Logic/InferenceSystem.lean` | InferenceSystem typeclass — primary target |
| `Cslib/Foundations/Logic/ProofSystem.lean` | HasAxiom*, ModusPonens, Necessitation typeclasses |
| `Cslib/Foundations/Logic/Theorems/Combinators.lean` | imp_trans, identity, b_combinator — rule building blocks |
| `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean` | Generic deduction lemmas for list contexts |
| `Cslib/Logics/Bimodal/Metalogic/Decidability/AxiomMatcher.lean` | boundedSearchWithProofStub (line 456); matchAxiom pattern |
| `Cslib/Logics/Bimodal/Metalogic/Decidability/ProofExtraction.lean` | buildCompositionalProof (lines 155-204) — term-mode precedent |
| `Cslib/Logics/Propositional/ProofSystem/Instances.lean` | InferenceSystem + ModusPonens instance registration pattern |
| `Cslib/Logics/Modal/ProofSystem/Instances/S5.lean` | Modal instance registration |
| `Cslib/Foundations/Relation/Attr.lean` | Only existing meta section usage in CSLib |
| `Cslib/Foundations/Lint/Basic.lean` | Meta section pattern reference |

### BimodalLogic Reference Implementation

| File | Lines | Relevance |
|------|-------|-----------|
| `BimodalLogic/Theories/Bimodal/Automation/Tactics/Helpers.lean` | ~700 | Core modal_search logic — architecture reference |
| `BimodalLogic/Theories/Bimodal/Automation/Tactics/Commands.lean` | ~400 | Syntax, config, elab_rules — Tier 2 reference |

### Mathlib Prior Art

| Component | Relevance |
|-----------|-----------|
| `Mathlib.Tactic.ITauto` (744 lines) | Two-phase reify+replay architecture |
| `Mathlib.Tactic.TFAE.dfs` | DFS over implication graphs — closest structural analog |
| `Aesop` | Available via Mathlib; viable for simple axiom closure, insufficient for formula-directed DFS |
