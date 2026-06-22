# Teammate C Findings — Critical Analysis
# Product Construction and Model Checking (Task 251)

## Overview

This report identifies gaps, risks, and hidden assumptions in the seed report
(`01_product-model-checking-seed.md`) and literature sources
(`02_literature-sources.md`) for task 251. The analysis is based on direct
inspection of the relevant Lean files in CSLib.

---

## Key Findings

### Finding 1: Task 242 Dependency Is Misleading (Severity: HIGH)

The seed report states: "Task 242 (Vardi-Wolper) — provides LTL-to-NBA for ¬φ."

Task 242 (`vardi_wolper_tableau_construction`) is currently `not_started` in
`state.json`. However, the LTL-to-NBA translation **already exists** in
`Cslib/Logics/LTL/Semantics/GNBA.lean` and `OmegaRegular.lean`, implemented
as part of task 236 (GNBA construction):

- `Formula.gnbaNBA φ : NA.Buchi (GNBANBAState φ) (Set Atom)` — the NBA for φ
- `Formula.gnba_language_eq φ` — correctness (Baier-Katoen Theorem 5.39)
- `Formula.isRegular φ` — every LTL formula defines an ω-regular language
- Both files are sorry-free

**Consequence**: Task 251 can use `gnbaNBA (neg φ)` (where `neg φ = imp φ bot`)
as the NBA for ¬φ today, without waiting for task 242. The seed report's framing
suggests task 251 is blocked on task 242, but this is factually incorrect.
Task 242 appears to be a planned alternative (more direct) LTL-to-NBA construction
that would replace or complement the GNBA approach.

**Risk**: Implementation will be misled into searching for a task-242 API that does
not exist, when the needed API (`gnbaNBA`) already exists. If task 251 is designed
to import from task 242, that import will fail.

---

### Finding 2: Type Mismatch — `Set Atom` vs `Atom → Prop` (Severity: HIGH)

The two existing bridges operate on different types:

- `SatisfiesExec` in `OmegaExecutionSatisfies.lean`:
  uses `labeling : State → (Atom → Prop)` as the labeling function

- `gnbaNBA` in `GNBA.lean`:
  has alphabet type `Set Atom` (via `NA.Buchi (GNBANBAState φ) (Set Atom)`)
  and uses valuation `fun p s => p ∈ s : Atom → Set Atom → Prop`

These two interfaces are logically equivalent but **not definitionally equal** in
Lean 4. To state the product construction correctness theorem in terms of
`SatisfiesExec`, the implementation must bridge:

```
labeling_prop : State → Atom → Prop
⟷ (classical)
labeling_set  : State → Set Atom     where labeling_set s = {p | labeling_prop s p}
```

For `[Fintype Atom]`, `Atom → Prop ≅ Set Atom` (both are equivalent via
`Set.mem_def`), but they are **propositionally** — not definitionally — equal.
Every statement linking the product NBA to `SatisfiesExec` will require a
rewriting step using `Set.mem_def` or a custom bridge lemma.

**Concrete impact**: The model checking theorem
```
M ⊨ φ ↔ L(M ⊗ gnbaNBA(¬φ)) = ∅
```
cannot be stated using raw `SatisfiesExec` with `Atom → Prop` labeling if the
product is defined with alphabet `Set Atom`. The implementation must either:
- Unify on one representation (recommend `Set Atom` with `[Fintype Atom]`), or
- Provide explicit conversion lemmas before stating the main theorem.

The seed report does not identify or address this mismatch.

---

### Finding 3: LTS Has No Initial States — Missing Kripke Structure Type (Severity: HIGH)

The product construction definition in the seed report states:
> "Initial states: S₀ × {q₀}"

`CSLib.LTS` has no concept of initial states (`LTS State Label` is just a
transition relation). The NBA (`NA`) has `start : Set State`, but there is no
corresponding field in `LTS`.

The standard model checking statement "M satisfies φ" is defined over Kripke
structures M = (S, S₀, R, L) where S₀ ⊆ S are the initial states. Without a
notion of initial states, the statement "M ⊨ φ" cannot be formalized directly
with the existing `LTS` type.

**Options**, in increasing scope:

1. **Minimal**: Parameterize by initial state(s). Define
   `ModelSatisfies (lts : LTS State Label) (initialStates : Set State)
    (labeling : State → Set Atom) (φ : Formula Atom) : Prop`
   as a local abbreviation in the new file. This avoids new top-level types.

2. **Structural**: Define a `KripkeStructure` or `LabeledLTS` type in
   `Foundations/` combining LTS + initial states + labeling. But the seed report
   explicitly says "No new transition system type is needed," contradicting this.

3. **Scope reduction**: State the product construction lemma without initial states,
   and state the model checking reduction theorem for a fixed single initial state
   `s₀ : State`. This is the safest approach for zero-debt compliance.

The seed report's claim "No new transition system type is needed" is too quick.
Either a new type is needed, or the implementation must carefully parameterize by
initial states.

---

### Finding 4: The LTS Label Type is Orthogonal to NBA Alphabet (Severity: MEDIUM)

The CSLib LTS uses `Tr : State → Label → State → Prop` where `Label` is the
transition label type. In model checking, the NBA alphabet is `Set Atom` (the set
of propositions holding at each state), which is **completely different** from the
LTS transition label.

In the product construction, the transition condition is:
```
((s, q), (s', q')) ∈ δ_⊗ iff (∃ μ, lts.Tr s μ s') ∧ na.Tr q (labeling s') q'
```
(the specific LTS label μ is existentially quantified away — it is irrelevant).

The product NBA reads `Set Atom` symbols (from the NBA side), not `Label` values
(from the LTS side). The resulting product is:
```
NA.Buchi (State × GNBANBAState φ) (Set Atom)
```
Note the absence of `Label` in the product type — the LTS label is consumed during
construction.

**Risk**: The definition of `LTSProduct` must existentially quantify over the LTS
label:
```
Tr (s, q) a (s', q') :=
  (∃ μ : Label, lts.Tr s μ s') ∧ na.Tr q a q'
```
This means the product definition is **not** a straightforward type product —
it requires discarding the `Label` dimension. The seed report's formulation
mentions "R(s,s')" (unlabeled transition) without clarifying how this maps to
the labeled `Tr`.

---

### Finding 5: Scope — Full Reduction Theorem Is Ambitious (Severity: MEDIUM)

The task description asks for TWO things:
1. The product construction (definition)
2. The full model checking reduction theorem (proof)

The full reduction theorem has two directions:
- **Soundness**: accepting run of M ⊗ A_¬φ → path in M satisfying ¬φ
  (projection argument — moderate difficulty)
- **Completeness**: path in M satisfying ¬φ → accepting run of M ⊗ A_¬φ
  (lift argument — requires correctness of gnbaNBA, i.e., `gnba_language_eq`)

The completeness direction requires:
- The path in M satisfies ¬φ, so the sequence of labeling values is in
  `L(gnbaNBA(¬φ))` (by `gnba_language_eq`)
- Extracting an accepting run of `gnbaNBA(¬φ)` from this
- Zipping it with the LTS run to construct a product run

This is non-trivial because the "sequence of labeling values" is an
`ωSequence (Set Atom)` while the LTS run is an `ωSequence State` — these must be
carefully coordinated, and the `[Fintype Atom]` hypothesis required by
`gnba_language_eq` must be tracked through.

**Assessment**: Doing both the definition and the full bidirectional theorem in one
task is realistic but will be tight. A plan decomposition into (a) product
definition + soundness, then (b) completeness, is advisable to guard against
sorry risk.

---

### Finding 6: Task 248 Provides Exactly What Is Needed (Severity: LOW — POSITIVE)

Task 248 (`nba_emptiness_checking`) is **completed** and provides:
- `NA.Buchi.HasReachableAcceptingCycle` (definition)
- `NA.Buchi.language_nonempty_iff` — L(A) ≠ ∅ ↔ HasReachableAcceptingCycle A
  (requires `[Finite State]` and `[Inhabited Symbol]`)
- `NA.Buchi.language_eq_bot_iff` — L(A) = ⊥ ↔ ¬HasReachableAcceptingCycle A

For the product NBA of type `NA.Buchi (State × GNBANBAState φ) (Set Atom)`:
- `[Finite State]` may need to be an additional hypothesis (the LTS state space
  is not finite in general)
- `[Inhabited (Set Atom)]` holds since `Set Atom` contains ∅

The `[Finite State]` requirement is a real constraint: the language nonemptiness
characterization via task 248 only applies to finite-state systems. If the system
M has infinite state space, `language_nonempty_iff` does not apply. The task
description and seed report do not mention this constraint.

---

## Gaps Identified

| # | Gap | Location in Seed | Impact |
|---|-----|-----------------|--------|
| G1 | Task 242 does not exist; gnbaNBA already exists | "Task 242 provides LTL-to-NBA" | HIGH — misleading dependency |
| G2 | Set Atom vs Atom → Prop type mismatch | "SatisfiesExec ... State → (Atom → Prop)" | HIGH — requires bridge lemmas |
| G3 | LTS has no initial states | "Initial states: S₀ × {q₀}" | HIGH — cannot state M ⊨ φ without this |
| G4 | LTS Label is orthogonal to NBA alphabet | Implicit in product definition | MEDIUM — must existentially quantify |
| G5 | [Finite State] required for emptiness theorem | Not mentioned | MEDIUM — limits generality |
| G6 | Scope includes full bidirectional proof | Single task description | MEDIUM — proof complexity |

---

## Risk Assessment

**Overall Risk Level: MEDIUM-HIGH**

The product construction definition itself (the new NBA from LTS × NBA) is
straightforward to implement and should be easy to get right in Lean 4. The type
is clear: `NA.Buchi (State × GNBANBAState φ) (Set Atom)`.

The model checking **reduction theorem** carries higher risk:
- The type mismatch (Gap G2) will produce unexpected proof obligations unless
  addressed upfront in the design. Failure to identify this early could lead to
  mid-proof dead ends.
- The initial states gap (Gap G3) will force either a new type or a careful
  parameterization. Without resolution, the theorem cannot be stated.
- The LTS Label gap (Gap G4) is architecturally clear but easy to miss in
  implementation.

**Zero-Debt Risk**: The completeness direction (LTS run → product run) is the most
proof-intensive part. If the plan does not budget enough complexity here, it may
invite sorry deferral. The `gnba_language_eq` chain is long (1484-line GNBA.lean),
and extracting the run from a language membership proof requires careful
`OmegaExecution.append` and `flatten_mTr` usage.

**Recommended Scope Adjustment**: A plan that clearly defines:
1. A `LTSProduct` type (product NBA construction) with accompanying lemmas
   (projection, lift, initial states)
2. A `ModelChecking` module with the main theorem, explicitly handling:
   - Labeling type unification (Set Atom vs Atom → Prop)
   - Initial states parameterization
   - [Finite State] as an explicit hypothesis
   ...would be lower risk than one that assumes these details will resolve naturally.

---

## Confidence Level

- **Task 242 dependency analysis**: HIGH CONFIDENCE. Directly verified by reading
  `state.json` (task 242 = `not_started`) and `GNBA.lean` (gnbaNBA exists, sorry-free).
- **Type mismatch identification**: HIGH CONFIDENCE. Directly verified by reading
  `OmegaExecutionSatisfies.lean` (uses `Atom → Prop`) and `GNBA.lean` (uses `Set Atom`).
- **Initial states gap**: HIGH CONFIDENCE. Directly verified by reading
  `LTS/Basic.lean` (no `start` field) and the product construction definition.
- **LTS Label orthogonality**: HIGH CONFIDENCE. Structural analysis of `LTS.Tr` type.
- **Scope assessment**: MEDIUM CONFIDENCE. Based on reading the GNBA correctness proof
  structure in `GNBA.lean`; the actual proof difficulty may vary.
- **Task 248 sufficiency**: HIGH CONFIDENCE. Read the completed `Emptiness.lean`;
  the `[Finite State]` requirement is clearly stated in the theorems.
