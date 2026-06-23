# Teammate C Findings: Critical Analysis
# Task 269 — Build Generic Bounded Proof-Search Tactic for InferenceSystem

**Role**: Critic  
**Date**: 2026-06-22  
**Focus**: Feasibility risks, scope concerns, integration risks, missing considerations

---

## Key Findings

### 1. The "Tactic" vs "Term-Mode Search" Distinction Is Unresolved

The task says "build a tactic (e.g., `hilbert_search`)". This is ambiguous about whether
the implementation should be:

- **(A) A Lean 4 `TacticM` elaboration plugin** — registered with `elab_rules tactic | ...`,
  calling into `MetaM` to generate proof terms at elaboration time. This requires importing
  `Lean.Elab.Tactic`, writing in the meta language, and lives outside the normal term-mode proof.
- **(B) A term-mode decision procedure** — a regular `def hilbert_search : ... -> Option (S⇓φ)`
  that is called with `exact hilbert_search ...` or `decide`. This is a pure Lean 4 definition
  with no metaprogramming.
- **(C) An `aesop` extension** — registering `@[aesop apply]`-attributed lemmas so that `aesop`
  can drive the search automatically.

The task description says "inspired by BimodalLogic `modal_search` (~700 lines)" — but CSLib
already has a different architecture than BimodalLogic. The BimodalLogic `modal_search` was
written as a term-level decision procedure, while the task calls it a "tactic". Which one is
intended has major architectural consequences and must be clarified before implementation begins.

**Risk**: Without resolving this distinction, two teammates may implement incompatible things.

---

### 2. The InferenceSystem API Does Not Support Term-Mode Pattern Matching on Formulas

The `InferenceSystem` typeclass has the signature:

```lean
class InferenceSystem (S : Type*) (α : Type*) where
  derivation (a : α) : Sort v
```

The type `α` is abstract at the typeclass level. To perform "modus ponens decomposition"
(find `φ` and `ψ` such that the goal is `S⇓ψ` and we can recurse on `S⇓(φ→ψ)` and `S⇓φ`),
the search procedure needs to:

1. **Match** the formula `a : α` against the pattern `HasImp.imp φ ψ` — this requires
   `HasImp α` and the ability to **invert** the `imp` constructor.
2. **Enumerate subformulas** — this is not in the `InferenceSystem` interface; it is
   formula-type-specific.
3. **Check equality** of formulas during hypothesis lookup — requires `DecidableEq α`.

Concretely, the `AxiomMatcher` in Bimodal uses direct pattern matching on the `Formula Atom`
inductive type (not through a typeclass), and `DerivationTree` is parameterized over the
concrete formula type, not an abstract `α`. The abstract `InferenceSystem S α` interface
exposes only `derivation (a : α) : Sort v` — no decomposition, no enumeration, no equality.

**Consequence**: A genuinely generic proof search over `InferenceSystem S α` would need
additional typeclasses:

```lean
-- Formula decomposition (not currently in CSLib)
class HasImpView (F : Type*) [HasImp F] where
  viewImp : F → Option (F × F)

-- Assumption tracking (not currently in CSLib)
class HasAssumptions (S : Type*) (F : Type*) [InferenceSystem S F] where
  assumptions : List F
```

Without these, the "generic" tactic must be either:
- Hardcoded to specific formula types (not generic), or
- Limited to axiom dispatch (not a real DFS proof search)

This is a **fundamental design gap** in the task description that prior research may miss.

---

### 3. The Existing Infrastructure Already Provides Alternatives

The task asks for a "generic bounded DFS proof-search tactic" — but CSLib already has
several mechanisms that partially fulfill this role:

- **`aesop`**: Already imported via `Mathlib.Tactic.Common` in `Cslib.Init`. The `aesop`
  tactic performs best-first proof search and can be extended with `@[aesop apply]` attributes.
  For `DerivableIn` goals, `aesop` with appropriate rule registrations might already work.

- **`Combinators.lean`**: The `imp_trans`, `identity`, `b_combinator`, `flip` theorems in
  `Cslib.Foundations.Logic.Theorems.Combinators` already provide foundational propositional
  reasoning in generic `[MinimalHilbert S]` contexts.

- **`Cslib.Foundations.Logic.Metalogic.ListDeduction`**: Already provides generic deduction
  lemmas for list contexts.

**Risk**: The task may be reinventing infrastructure that `aesop` + appropriate rule
registrations would already provide. A Zulip discussion question should explicitly ask:
"Has anyone tried using `aesop` with `@[aesop apply (rule_sets := [hilbert])]` on
`DerivableIn` goals?"

---

### 4. The `boundedSearchWithProofStub` Is Already Present as a Stub

In `AxiomMatcher.lean` (line 456), there is already:

```lean
def boundedSearchWithProofStub (_ : Context Atom) (φ : Formula Atom) (_ : Nat) :
    Option (DerivationTree FrameClass.Base ([] : Context Atom) φ) × Nat × Nat :=
  (none, 0, 0)
```

This stub exists specifically because the bimodal tableau procedure does not need forward
proof search (it uses backward tableau). The `DecisionProcedure.lean` calls this stub and
falls through to tableau. If the implementation team fills in this stub, it is
**Bimodal-specific**, not generic over `InferenceSystem S α`.

**Risk**: Teammates A and B may focus on "filling in the stub" rather than building a
genuinely generic component.

---

### 5. Soundness Cannot Be Guaranteed by Search Depth Alone

A bounded DFS over Hilbert axioms is sound if and only if every construction step produces
a valid derivation. For a term-mode approach, soundness is automatic: if `buildProof` returns
`some d`, then `d : S⇓φ` is a proof term, so soundness is immediate by typing.

However, for a **tactic** approach (Option A above), the tactic closes the goal by
constructing and applying a proof term. Here:
- If the term-mode search returns a wrong proof term (impossible in well-typed Lean), the
  kernel would reject it.
- If the `TacticM` code uses `sorry` internally or synthesizes incorrect metavariables,
  it could introduce unsoundness.

The **real soundness risk** is if the tactic is implemented using `Lean.Meta.mkSorry`
or `Expr.mvar` tricks to "claim" goals are closed without proof. The task description does
not address this at all.

**Recommendation**: Specify that the implementation must not use `Lean.Meta.mkSorry`,
must not manipulate metavariables directly, and must construct actual proof terms.

---

### 6. Scope Is Dramatically Underestimated for a "Generic" Version

The BimodalLogic `modal_search` at ~700 lines is specific to one formula type with one
concrete `DerivationTree`. A genuinely generic version over `InferenceSystem S α` must:

1. Abstract over formula decomposition (requires new typeclasses — see point 2 above)
2. Abstract over axiom enumeration (each logic has different axioms; currently each logic
   has a specific inductive type like `KAxiom`, `TAxiom`, `ModalAxiom`)
3. Handle all three logic levels: propositional uses `PL.DerivationTree`, modal uses
   `Modal.DerivationTree`, temporal/bimodal use separate trees with different parameters
4. Handle `Context` (assumption lookup) generically — each logic has its own `Context`
   type or uses `List F`

A minimal viable implementation that is genuinely generic (not per-logic) would require
approximately:
- 100-200 lines: new typeclasses for formula decomposition
- 200-400 lines: generic search loop
- 200-400 lines: per-logic instances (propositional, modal, temporal, bimodal)
- 100-200 lines: tests and examples

Total: 600-1200 lines minimum. The 700-line estimate assumes the implementation is
**not actually generic** but rather another Bimodal-specific implementation.

---

### 7. Formula Type Decidability Is Only Partially Available

The bounded search needs `DecidableEq` on the formula type to check membership in
hypothesis lists. Current status:

- `PL.Proposition Atom`: `deriving DecidableEq` — **available**
- `Modal.Proposition Atom`: `deriving DecidableEq` — **available**
- `Temporal.Formula Atom`: `deriving DecidableEq` — **available**
- `Bimodal.Formula Atom`: `deriving DecidableEq` — **available**

However, the abstract `F` in `InferenceSystem S F` has no `DecidableEq` constraint.
Adding `[DecidableEq F]` to the search signature would break the generality promise
(not all formula types need this) and requires adding it to every caller site.

---

### 8. Error Messages and Failure Transparency Are Not Designed

If `hilbert_search` fails to find a proof within the depth bound:
- What does the user see? "search failed" is not informative.
- Does the tactic suggest increasing the depth?
- Does it report the deepest point reached?
- Does it explain why it backtracked?

The task description is completely silent on this. For a library tactic, error quality is
not optional — `aesop` provides traceable search trees precisely because opaque failure
is useless.

**Risk**: A proof-search tactic with no diagnostics will be rejected in PR review on
usability grounds alone.

---

### 9. Testing Is Structurally Harder for Proof-Search Tactics Than for Theorems

Testing `hilbert_search` requires:
- Formulas where it **succeeds** (positive tests — verifies the search finds proofs)
- Formulas where it **fails within bound** (negative tests — verifies depth bound is respected)
- **Performance tests** — does it run in acceptable time for expected formulas?
- **Regression tests** — does adding new axiom instances slow it down?

The CslibTests framework is currently used for structural tests (LTS, bisimulation, etc.),
not for tactic performance. The test infrastructure for timing/resource-bounded search does
not exist in CSLib.

---

### 10. Interaction with Existing Automation Is Uncharted

CSLib already uses:
- `simp` and `simp only` throughout
- `aesop` (via Mathlib) 
- `omega`, `decide`, `ring`
- `grind` (CSLib's `@[grind =]` attribute on `rwConclusion`)

A new `hilbert_search` tactic must not conflict with these. In particular:
- If `hilbert_search` is marked `@[simp]` or `@[aesop]`, it could cause unexpected
  recursive application during unrelated proofs.
- If it uses `aesop` internally, recursive loops are possible.

The task description does not mention interaction with existing automation at all.

---

### 11. The "Assumption Lookup" Strategy Is Undefined for InferenceSystem

The task description lists "assumption lookup" as a search strategy. But:
- `InferenceSystem S α` has no notion of a context/hypothesis list.
- The existing `DerivationTree` constructors have an `assumption` rule, but it's
  specific to each logic's `Context` type (e.g., `Context Atom = List (Formula Atom)`).
- In the generic `HasAxiom*` typeclass hierarchy, there is no `assumption` rule at all
  — it only exists in the concrete `DerivationTree` inductives.

For a tactic-mode implementation, "assumption lookup" means searching the Lean proof
context for `DerivableIn S φ` hypotheses — this is doable via `Lean.Meta.getLocalDecls`.
For term-mode, it requires passing an explicit list of hypotheses.

The task description conflates these two very different notions of "assumption".

---

### 12. Questions for Zulip Discussion

The following design decisions should be raised with the CSLib community before implementation:

1. **Tactic vs term-mode**: Should `hilbert_search` be a `TacticM` elaborator, a
   `decide`-based decision procedure, or an `aesop` extension?

2. **Genericity boundary**: Should the tactic be generic over all `[MinimalHilbert S]`
   systems, or is it acceptable to have per-logic instances that share a common skeleton?

3. **Formula decomposition**: Should CSLib add `HasImpView`, `HasBoxView`, etc. typeclasses
   for formula decomposition? Or should each concrete formula type provide a pattern-matching
   helper that the search can use via a typeclass?

4. **`aesop` alternative**: Has anyone profiled whether `aesop` with appropriate
   `@[aesop apply]` registrations already handles `DerivableIn` goals for common formulas?
   If yes, `hilbert_search` becomes a tactic policy decision, not a search implementation.

5. **Scope definition**: What is the minimum viable scope — axiom dispatch only, or full
   DFS with necessitation/MP decomposition?

---

## Recommended Approach

Given the risks above, the recommended approach is:

**Phase 1 (Minimal)**: Build a term-mode axiom dispatcher that handles the common cases
(identity, weakening, necessitation, K-axiom, T-axiom) for `[ClassicalHilbert S]` and
`[ModalHilbert S]`. Expose as `exact hilbert_axiom_dispatch`. ~100-150 lines. No
metaprogramming, guaranteed sound.

**Phase 2 (Conditional on Phase 1 success)**: Wrap Phase 1 in a `TacticM` elaborator
that also checks Lean hypotheses for `DerivableIn` facts and applies MP automatically.
~200 additional lines.

**Do NOT attempt Phase 3** (genuine generic DFS with formula decomposition) until new
typeclasses for formula decomposition are designed and reviewed on Zulip.

---

## Evidence and Examples

**Evidence for point 2 (formula decomposition gap)**:

The `AxiomMatcher.matchAxiom` function matches `Formula Atom` directly:
```lean
def matchAxiom (φ : Formula Atom) : Option (AxiomWitness Atom) :=
  match φ with
  | .imp lhs rhs => ...
```
This is not abstractable over `HasImp F` without an `invImp : F → Option (F × F)` helper.

**Evidence for point 3 (aesop already available)**:
`Cslib.Init` imports `Mathlib.Tactic.Common` which imports `Aesop`.
`Cslib.Foundations.Logic.Theorems.Combinators` provides `imp_trans`, `identity`, `b_combinator`
as generic `[MinimalHilbert S]` theorems — the raw material for an aesop rule set is already there.

**Evidence for point 4 (stub already exists)**:
`AxiomMatcher.lean` lines 455-459: `boundedSearchWithProofStub` returns `(none, 0, 0)` — the
exact feature slot the task wants to fill is already identified as a stub by a prior implementer.

**Evidence for point 6 (scope underestimate)**:
The `ProofSystem.lean` file is 523 lines defining only the typeclass hierarchy.
The `AxiomMatcher.lean` is 498 lines for **one logic** (bimodal with 42 axioms).
A generic version covering 4 logics × ~5-42 axioms each would balloon significantly.

---

## Confidence Level

| Finding | Confidence |
|---------|-----------|
| Tactic vs term-mode ambiguity | High — the task description is genuinely ambiguous |
| Formula decomposition gap | High — verified by reading InferenceSystem.lean and AxiomMatcher.lean |
| aesop already available | High — verified in Init.lean |
| Scope underestimate | Medium-High — depends on how strictly "generic" is interpreted |
| Soundness risk | Medium — depends on implementation choice |
| Error message gap | High — task description is silent on this |
| Assumption lookup ambiguity | High — two incompatible meanings in scope |
| Decidability gap | Medium — concrete types have it; abstract F does not |
| Testing infrastructure gap | Medium — existing tests don't cover tactic timing |
