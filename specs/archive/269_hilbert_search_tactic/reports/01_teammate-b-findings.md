# Teammate B Findings: Alternative Approaches and Prior Art

**Task 269**: Build generic bounded proof-search tactic for InferenceSystem
**Role**: Alternative patterns and existing solutions
**Date**: 2026-06-22

---

## Key Findings

### 1. No Pre-Existing Hilbert Proof Search in CSLib or Mathlib

No file in CSLib or Mathlib implements a Hilbert-style bounded proof-search tactic. The
relevant search term `hilbert_search`, `modal_search`, `bounded_proof_search` yields zero
results in the codebase. The BimodalLogic `modal_search` mentioned in the task description
lives in the BimodalLogic project (external) and has not been ported to CSLib. Its stub
(`boundedSearchWithProofStub`) is explicitly stubbed out at:

- `Cslib/Logics/Bimodal/Metalogic/Decidability/AxiomMatcher.lean:456`

This stub always returns `(none, 0, 0)` and is explicitly deferred. The task is therefore
implementing net-new infrastructure, not wrapping anything existing.

### 2. Closest Prior Art: Mathlib's `itauto` and `tauto` Tactics

The most structurally similar prior art is `Mathlib.Tactic.ITauto` (744 lines). It implements:

- A **reified propositional formula type** `IProp` (separate from the goal's Expr)
- A **reified proof type** `Proof` (a tree of proof constructors)
- A **core search loop** `prove : Context → IProp → StateM Nat (Bool × Proof)` that:
  - Applies deterministic level-1 rules (no splitting) exhaustively
  - Tries level-2 splitting rules
  - Falls back to level-3 non-deterministic rules in `search`
- A **reconstruction phase** `applyProof : MVarId → NameMap Expr → Proof → MetaM Unit`
  that replays the reified proof against the actual Lean goal

The key insight from `itauto` for our task: it works in two phases -- (1) find the proof
structure in a reified domain, then (2) apply it to the Lean goal via MetaM. This avoids
the difficulty of manipulating MVarIds directly during search.

Architecture verdict: `itauto` is tightly coupled to propositional logic and cannot be
reused directly. But the two-phase (reify + replay) pattern is directly applicable.

### 3. The TFAE Tactic Has a DFS That Is Very Close to What We Need

`Mathlib.Tactic.TFAE.dfs` implements a genuine DFS over a graph of `Prop → Prop`
implications in the context. Simplified:

```lean
partial def dfs (i j : ℕ) (P P' : Q(Prop)) (hP : Q($P)) :
    StateT (Std.HashSet ℕ) MetaM Q($P') := do
  if i == j then return hP
  modify (·.insert i)
  for (a, b, h) in hyps do
    if i == a then
      if !(← get).contains b then
        try return ← dfs b j Q P' q($h $hP) catch _ => pure ()
  failure
```

This is essentially the structure of a Hilbert backward proof search: try each applicable
rule/hypothesis, recurse. For our tactic, `hyps` would be the Hilbert rules (axioms +
modus ponens) rather than local context hypotheses.

### 4. Aesop as an Alternative to Building from Scratch

Aesop (`aesop`) is available in CSLib (it is a transitive dependency via Mathlib). It supports:
- **BestFirst, DepthFirst, BreadthFirst** strategy selection via `Options.strategy`
- **Configurable depth/width** limits: `maxRuleApplicationDepth` (default 30),
  `maxRuleApplications` (default 200)
- **Custom rule registration** via `@[aesop]` attribute or `(add ...)` clause at call site
- **Rule builders**: `apply`, `tactic`, `forward`, `cases`, `norm_simp`, etc.
- **Named rule sets** for clean encapsulation

The critical question is: can we register Hilbert axioms and inference rules as Aesop rules?
YES -- via the `tactic` builder and the `(add safe apply ...)` syntax. For example:

```lean
-- Register modus ponens as an Aesop safe rule at priority 90
@[aesop safe (rule_sets [HilbertK]) apply]
theorem mp_rule [ModalHilbert S] {φ ψ : F} :
    InferenceSystem.DerivableIn S (HasImp.imp φ ψ) →
    InferenceSystem.DerivableIn S φ →
    InferenceSystem.DerivableIn S ψ :=
  ModusPonens.mp
```

Then `aesop (rule_sets [HilbertK]) (config := { strategy := .depthFirst, maxRuleApplicationDepth := 10 })` 
would perform bounded DFS using those rules.

The appeal of this approach: zero new MetaM/TacticM code. The limitation: Aesop works on
the Lean proof state (MetaM level), not on the CSLib `DerivableIn S φ` propositions
generically. It can prove `DerivableIn S φ` goals by applying Lean lemmas, but it cannot
"see inside" `φ` to do formula-directed search.

**Aesop assessment**: Suitable for simple propositional and modal cases. Insufficient for:
- Modus ponens decomposition (which requires knowing the antecedent formula)
- Backward search that generates subgoals from the target formula

### 5. Existing Automation in CSLib: Very Minimal

Survey of `@[aesop]` and related usage in CSLib proper (not Mathlib):
- `aesop` is used as a closing tactic in 5 files (CLL, LambdaCalculus, NA, URM, Named)
- No `@[aesop]` rule registrations exist in any CSLib file
- No `macro`/`elab` tactic definitions exist in CSLib (only `Relation/Attr.lean` uses
  `registerBuiltinAttribute` but this is for the `reduction_sys` notation attribute, not
  proof automation)
- The only tactic meta-programming in CSLib is `Lean.Elab.Command`-level (notation
  generation), not `TacticM`-level

CSLib currently relies entirely on Lean's built-in tactics (`simp`, `aesop`, `grind`,
`omega`, `decide`) plus explicit term-mode proofs for derivation trees.

### 6. The InferenceSystem Typeclass Architecture: Key Constraint

`InferenceSystem S α` provides one field: `derivation (a : α) : Sort v`. The actual
derivation type is abstract. The `DerivableIn S φ = Nonempty (S⇓φ)` wrapper is Prop-valued.

This has a critical implication for tactic metaprogramming: **a generic tactic cannot
pattern-match on the formula `φ` at the Lean elaboration level without knowing the
concrete formula type**. The tactic would need to:

1. Inspect the goal type `DerivableIn S φ` or `S⇓φ`
2. Reduce `φ` to a concrete term (e.g., `HasImp.imp a b`)
3. Dispatch on connective structure using `whnf` or `matchAppOf`

This is possible in MetaM but requires knowing the connective typeclass instances for the
concrete formula type at the call site -- which is available via typeclass inference.

### 7. Search Strategy Analysis: DFS vs IDDFS vs BFS

For Hilbert proof search over modal/temporal formulas:

| Strategy | Pros | Cons |
|----------|------|------|
| DFS (depth-first) | Simple; easy fuel control; works for propositional | May miss proofs; gets stuck in deep wrong branches |
| BFS (breadth-first) | Complete at each depth | Exponential memory; impractical for modal |
| IDDFS (iterative deepening) | Complete; linear memory | Slightly slower; harder to implement in Lean |
| Best-first (Aesop's default) | Heuristic-guided; flexible | Requires priority function; complex |

For CSLib's use case (proving concrete derivability goals), **DFS with configurable depth**
is the correct choice because:
- Formula size is small and bounded (proof terms are explicitly constructed)
- The BimodalLogic reference implementation uses DFS (per task description)
- IDDFS adds complexity without benefit for bounded-depth use cases

### 8. Alternative Architecture: Term-Mode Search Function + `decide` Tactic Bridge

Rather than a full `TacticM` tactic, an alternative architecture is:
1. A computable `search : S → φ → Nat → Option (S⇓φ)` function at the object level
2. A `decide`-style tactic that calls the search and reflects the result

This avoids MetaM entirely for the search logic. The search runs as a Lean computation,
and if it returns `some proof`, the tactic constructs `Nonempty.intro proof`. If it returns
`none`, the tactic fails.

**Critical obstacle**: The `InferenceSystem.derivation` type is `Sort v` (not necessarily
`Type`), so search results cannot be `Decidable` in general. However, for concrete
derivation tree types (which ARE `Type`-valued), this works.

The `buildCompositionalProof` function in `AxiomMatcher.lean` already implements this
pattern: it returns `Option (DerivationTree ...)` computed purely, then the tactic wraps
in `Nonempty`. This is the cleanest architecture for the generic case.

### 9. The Typeclass-Dispatch Feasibility Question

Can a single tactic work generically over all `[MinimalHilbert S]`, `[ModalHilbert S]`,
`[BimodalTMHilbert S]`?

Analysis: YES, at the `DerivableIn`/`Nonempty` level. The tactic can:
1. Check what axiom typeclasses are available (`synthInstance? (HasAxiomK S)`, etc.)
2. Use those to select applicable rules
3. Call `imp_trans`, `identity`, etc. from `Theorems/Combinators.lean` generically

The `Cslib.Logic.Theorems.Combinators` module already provides `imp_trans`, `identity`,
`b_combinator`, `flip`, `app1`, `app2` -- all generic over `[MinimalHilbert S]`.
`Cslib.Logic.Theorems.Modal.Basic` provides `box_mono`, `k_dist_diamond`, etc. over
`[ModalHilbert S]`.

These theorem-level combinators can be the "rules" the tactic applies, avoiding the need
to directly touch `DerivationTree` constructors.

### 10. The Lean 4 Meta-Programming Pattern for a Custom Tactic

For implementing `hilbert_search` as a Lean 4 tactic, the standard pattern (from `tauto`
and `itauto`) is:

```lean
-- 1. Declare syntax
syntax (name := hilbertSearchTactic) "hilbert_search" (num)? : tactic

-- 2. Register elaborator
@[tactic hilbertSearchTactic]
def evalHilbertSearch : Tactic := fun stx => do
  let depth := ...
  let goal ← getMainGoal
  -- inspect goal, dispatch search, close goal
```

This requires `public meta import Lean.Elab.Tactic` in a `meta section`. CSLib currently
has no `meta section` code outside of `Foundations/Relation/Attr.lean` (which uses it for
a notation attribute). The tactic would need to live in a separate `meta` module.

---

## Recommended Approach

**Two-tier hybrid architecture** (Medium-High confidence):

**Tier 1: Term-mode search library** (the bulk of the work, ~400 lines)
- A family of computable search functions operating on CSLib's `DerivableIn` Prop wrapper
- Functions parameterized by `[ClassicalHilbert S]`, `[ModalHilbert S]`, etc.
- Uses `Cslib.Logic.Theorems.Combinators` as the rule set
- DFS with fuel parameter for termination
- Returns `Option (DerivableIn S φ)` (not `Option (DerivationTree ...)` -- avoids needing
  the concrete type)
- Can be called directly in term-mode proofs without any tactic machinery

**Tier 2: Thin tactic wrapper** (small, ~50-80 lines)
- A `meta section` with `hilbert_search (depth := 10)` syntax
- Calls the Tier 1 search, wraps result in `exact` if found
- Falls back to `aesop` with a named rule set for simple cases

This approach has several advantages over alternatives:
1. The term-mode library (Tier 1) is immediately useful without the meta machinery
2. It can be tested via `#eval` and `#check` before the tactic exists
3. The `buildCompositionalProof` pattern in `AxiomMatcher.lean` validates this architecture
4. No new axioms, no sorry patterns -- just terminating computation

**Against pure Aesop approach**: Aesop cannot do formula-directed backward reasoning
(e.g., knowing to split `DerivableIn S (imp φ ψ)` into finding derivations of `φ → ψ`
vs `ψ` independently). Formula-directed search requires inspecting the formula structure.

**Against full MetaM tactic from scratch**: The CSLib contribution standards strongly prefer
definitions in `Prop`/term mode with `noncomputable` sparingly. A full MetaM approach
would need a `meta section` with heavy Lean.Elab imports, which is inconsistent with
CSLib's current code style (no files except `Attr.lean` use `Lean.Elab.*`).

---

## Evidence and Examples

### Pattern 1: The buildCompositionalProof pattern (already in CSLib)

The proof extraction in `Cslib/Logics/Bimodal/Metalogic/Decidability/ProofExtraction.lean`
(lines 155-204) implements the exact pattern Tier 1 should use:

```lean
def buildCompositionalProof (phi : Formula Atom) (fuel : Nat) :
    Option (DerivationTree .Base ([] : Context Atom) phi) :=
  if fuel = 0 then none
  else
    match tryAxiomProof phi with
    | some proof => some proof
    | none =>
    match phi with
    | .box inner =>
        match buildCompositionalProof inner (fuel - 1) with
        | some proofInner => some (DerivationTree.necessitation inner proofInner)
        | none => none
    | .imp a b =>
        if h : a = b then some (h ▸ identity a)
        else
          match buildCompositionalProof b (fuel - 1) with
          | some proofB => ... -- weakening
          | none => none
    | _ => none
```

The generic `hilbert_search` function should follow this exact fuel-based recursive
structure, but parameterized over `[MinimalHilbert S]` instead of hardcoded to `DerivationTree`.

### Pattern 2: The itauto prove/search decomposition

The `itauto` tactic separates its search into three priority levels and two functions:

```
prove (level 1 + 2) + search (level 3 fallback)
```

For Hilbert search, the analogous decomposition is:

```
fastPath (axiom matching) + compositional (structural decomp) + depthSearch (MP backward)
```

This matches the three-phase structure already visible in `buildCompositionalProof` and
`enhancedSearch`.

### Pattern 3: CSLib's DerivableIn vs DerivationTree choice

The `DerivableIn S φ = Nonempty (S⇓φ)` type is the right target for a generic tactic.
`ModusPonens.mp`, `HasAxiomK.K`, etc. all operate on `DerivableIn`, not on the concrete
derivation tree type. Working at this level means:

```lean
-- Works generically for ANY S with [ModalHilbert S]:
def search_box [ModalHilbert S (F := F)] {φ : F} (h : DerivableIn S φ) (fuel : Nat) :
    Option (DerivableIn S (HasBox.box φ)) :=
  some (Necessitation.nec h)
```

No knowledge of `DerivationTree` constructors needed.

---

## Confidence Level

**High confidence on**:
- CSLib currently has zero Hilbert proof search tactics (confirmed by exhaustive grep)
- The `buildCompositionalProof` pattern in `AxiomMatcher.lean` is the right model
- The two-tier (term-mode search + thin tactic wrapper) architecture is sound and consistent with CSLib style
- Aesop alone is insufficient for formula-directed backward proof search
- Working at the `DerivableIn S φ` level (not `DerivationTree`) enables true genericity

**Medium confidence on**:
- The thin tactic wrapper (Tier 2) is feasible without violating CSLib's contribution standards
  on `meta section` usage -- but this needs verification against CONTRIBUTING.md
- Iterative deepening is not worth the complexity over simple DFS for CSLib's target use cases
- The `Cslib.Logic.Theorems.Combinators` and `Theorems.Modal.Basic` combinators are
  sufficient rule building blocks (may need additional lemmas for temporal cases)

**Low confidence on**:
- Whether Aesop with custom rule sets can handle the modus ponens decomposition case
  with formula-directed dispatch (this would need prototyping to confirm)
- Exact complexity of the thin tactic wrapper given CSLib's `meta` usage constraints

---

## Gaps for Teammate A to Address

1. The concrete InferenceSystem typeclass instances (e.g., `ClassicalHilbert`, `ModalHilbert`)
   need to be examined to confirm the `ModusPonens.mp` / `Necessitation.nec` APIs are
   callable from term-mode search without unification failures on universe polymorphism
2. The temporal formula case (Until/Since) needs a dedicated subgoal strategy -- the `imp`
   decomposition pattern does not cover `untl`/`snce` constructors
3. The assumption lookup case (when there are hypotheses in a context `Γ`) needs a concrete
   plan -- the task mentions "assumption lookup" but CSLib's generic `InferenceSystem` does
   not have an `assumption` rule at the typeclass level (only `DerivationTree` has it)
