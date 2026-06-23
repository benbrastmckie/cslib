# Teammate C Findings: Best Practices, Standards, and Pitfalls

**Task 269**: Build generic bounded proof-search tactic for InferenceSystem
**Role**: CSLib contribution standards, performance/termination concerns, testing strategies,
error messages and diagnostics (Round 2)
**Date**: 2026-06-23

---

## 1. CSLib Contribution Standards for Automation Code

### 1.1 File Location

Based on ORGANISATION.md and the existing `Foundations/Logic/` tree, the correct location
for the tactic implementation is:

```
Cslib/Foundations/Logic/Automation/HilbertSearch.lean
```

This matches the ORGANISATION.md structure: `Foundations/` provides general-purpose
infrastructure shared across all logics. A new `Automation/` subdirectory follows the
existing pattern of `Theorems/`, `Metalogic/`, and `Metalogic/` as sub-namespaces. The
namespace would be `Cslib.Logic.Automation` (abbreviated `Cslib.Logic.Automation.HilbertSearch`).

**Import in barrel files**: After adding the file, run:
```bash
lake exe mk_all --module
```
to update `Cslib.lean`. Also run `lake shake --add-public --keep-implied --keep-prefix` to
verify no over-imports.

### 1.2 Every File Must Import Cslib.Init

The first non-copyright line must be:
```lean
import Cslib.Init
```
This is enforced by `lake exe checkInitImports`. The Init module sets up default linting
rules and the common tactic set (`Mathlib.Tactic.Common`).

**Implementation pattern** (from `Cslib/Foundations/Relation/Attr.lean`):
```lean
/-
Copyright (c) 2026 <Author>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <Author>
-/

module

public import Cslib.Init
-- additional imports follow
```

### 1.3 The `module` Declaration

Every CSLib file begins with `module` (a Lean 4 module declaration keyword). This is not
optional.

### 1.4 `public meta section` vs `@[expose] public section`

CSLib has two patterns for marking code that is only available in meta/tactic contexts:

**`public meta section`** (for tactic/elaborator code, imported by `public meta import`):
- Used in `Cslib/Foundations/Relation/Attr.lean` (the `reduction_sys` attribute)
- Used in `Cslib/Foundations/Semantics/LTS/Notation.lean` (the `lts` attribute)
- The enclosing imports use `public meta import Cslib.Init` pattern

**`@[expose] public section`** (for normal math definitions exported via expose):
- Used in `Cslib/Foundations/Logic/InferenceSystem.lean`, `ProofSystem.lean`, etc.
- Makes declarations available when the file is imported with `public import`

**For the search tactic**, the tactic elaboration code (anything using `TacticM`, `MetaM`,
`elab_rules`, `syntax`, `macro_rules`) must go inside a `public meta section` block. The
pure search function (term-mode, returning `Option (DerivableIn S φ)`) can go in a normal
`@[expose] public section` if it has no meta dependencies.

**Practical split**:
```lean
-- Pure term-mode search function (normal section)
@[expose] public section
  /-- Bounded Hilbert proof search (pure term-mode). -/
  def hilbertSearchTerm (fuel : Nat) ... : Option (DerivableIn S φ) := ...
end

-- Tactic elaboration (meta section)
public meta section
  open Lean Meta Elab.Tactic in
  /-- `hilbert_search` tactic ... -/
  syntax ... : tactic
  elab_rules : tactic | ...
end
```

### 1.5 Naming Conventions

CSLib follows Mathlib naming conventions with domain-appropriate names (from CONTRIBUTING.md):
- Tactic names: `snake_case` for the user-facing syntax (`hilbert_search`, `hilbert_search n`)
- Lean declaration names: `lowerCamelCase` (`hilbertSearchCore`, `hilbertSearchFuel`)
- The linter `defsWithUnderscore` flags any declaration name containing underscores

**Important**: The tactic syntax keyword (`syntax "hilbert_search" ...`) uses underscores
as part of the user-visible tactic name — this is NOT a Lean declaration name and is not
subject to the `defsWithUnderscore` lint. Only `def`, `theorem`, `lemma`, `class`,
`structure` names are checked.

### 1.6 Docstring Requirements (`docBlame`)

Every `def`, `theorem`, `lemma`, `class`, `instance`, `structure`, `inductive` needs a
docstring. The `docBlame` linter fires for any missing documentation.

For meta declarations, `@[nolint docBlame]` suppresses the check:
```lean
@[nolint docBlame]
def internalHelper ...
```

This pattern appears in `Cslib/Foundations/Relation/Attr.lean` for the notation macros
that are auto-generated.

For the main public-facing tactic and search function, proper docstrings are required.
**Template** (from CSLib sources):
```lean
/-- Bounded backward-chaining proof search for Hilbert-style proof systems.

`hilbert_search` attempts to find a proof of the current goal of the form
`InferenceSystem.DerivableIn S φ` by backward chaining through available axioms
and inference rules. The optional `n` argument limits the search depth (default: 20).

Usage:
- `hilbert_search` — search with default depth limit
- `hilbert_search 30` — search with explicit depth limit of 30
- `hilbert_search?` — search and report the found derivation

Fails with a diagnostic message if no proof is found within the depth limit. -/
syntax (name := hilbertSearch) "hilbert_search" (num)? : tactic
```

### 1.7 `@[simp]` Attribute Conventions

CSLib uses `@[simp]` sparingly. The `simpNF` linter checks that the LHS of every `@[simp]`
lemma is already in normal form (no redundant simp applications would fire on the LHS itself).

**For the search tactic**: Do NOT add `@[simp]` to the search function. Simp lemmas in the
search tactic (e.g., about `DerivableIn.fromDerivation`) should only be added if they are
genuinely useful for downstream goals beyond the tactic itself.

### 1.8 `@[scoped grind =]` Attribute Conventions

The `@[scoped grind =]` attribute marks equations that `grind` uses for equational reasoning
(visible in `Cslib/Foundations/Logic/InferenceSystem.lean` on `rwConclusion`, in
`Cslib/Logics/Propositional/Defs.lean` on `isIntuitionisticIff`, etc.).

**For the search tactic**: The main candidate would be a `@[scoped grind =]` annotation on
any auxiliary equation used to normalize derivability goals. However, adding `@[scoped grind]`
attributes to new declarations requires passing the `GrindLint.lean` test (`#grind_lint check`).
New attributes should start without `@[scoped grind]` and add them only after the lint test
passes. If they cause runaway instantiations, add a `#grind_lint skip` entry to
`CslibTests/GrindLint.lean`.

### 1.9 `@[aesop]` Attribute Conventions

CSLib uses `@[aesop]` only in a few places (`Cslib/Logics/Propositional/Defs.lean`,
`Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean`). The convention is conservative:
add `@[aesop]` only to constructors or rules that are clearly safe and non-diverging for
aesop's heuristic search. Do NOT add `@[aesop]` to the `hilbert_search` internal rules
without careful testing.

### 1.10 `topNamespace` Instance Wrapping

The `topNamespace` linter (`Cslib/Foundations/Lint/Basic.lean`) checks that every new
declaration has at least one namespace prefix. For `instance` declarations specifically,
ensure they are wrapped in a `namespace Cslib.Logic.Automation` block:

```lean
namespace Cslib.Logic.Automation
-- instance declarations here
end Cslib.Logic.Automation
```

---

## 2. Performance and Termination

### 2.1 Termination Strategy: Fuel (Not Depth)

**Recommendation**: Use **fuel-based** termination rather than depth-based termination.

- Fuel decrement per rule application (not per formula nesting depth)
- Lean 4 requires structurally decreasing arguments for `def` — use `Nat` fuel
- Pattern: `def search (fuel : Nat) ... : Option Result := match fuel with | 0 => none | n+1 => ...`

This is simpler to reason about than depth-limited DFS and easier to expose in the tactic
interface (users pass `n` to `hilbert_search n`).

**Termination guarantee**: Once fuel = 0, the function returns `none` unconditionally.
Lean's kernel can see this is terminating because it uses structural recursion on `Nat`.

```lean
/-- Core fuel-limited Hilbert backward search. -/
def hilbertSearchCore [MinimalHilbert S (F := F)]
    (fuel : Nat) (target : F) : Option (DerivableIn S target) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    -- Try axioms first (no recursive calls)
    -- Then try modus ponens (recursive calls decrement fuel)
    sorry
```

### 2.2 Typical Search Depths for Hilbert Proofs

Examining `Cslib/Foundations/Logic/Theorems/Combinators.lean`:

| Theorem | MP applications | Estimated depth |
|---------|----------------|-----------------|
| `identity` | 3 (SKK) | depth ≤ 3 |
| `imp_trans` | 3 | depth ≤ 3 |
| `b_combinator` | 1 | depth ≤ 2 |
| `flip` | ~10 | depth ≤ 10 |
| `app1` | 2 | depth ≤ 3 |
| `app2` | ~20 | depth ≤ 20 |
| `double_negation` | 5 | depth ≤ 5 |

The longest proofs in `Combinators.lean` are `app2` (~20 MP steps) and `flip` (~10 MP steps).
For modal and temporal axiom applications, depths will be similar (modal axiom K requires
~5 steps from axiom schemas).

**Recommended default fuel**: 30
**Maximum practical fuel**: 100 (anything beyond this will timeout in practice)

For the Lean 4 tactic default:
```lean
syntax (name := hilbertSearch) "hilbert_search" (num)? : tactic
-- fuel = 30 when no num is given; user can specify higher
```

### 2.3 Exponential Blowup in Backward Chaining

The primary pitfall is **exponential search in modus ponens backward chaining**:
To prove `ψ`, try each `φ → ψ` in scope, and for each try to prove `φ` recursively.
With `n` candidate premises and depth `d`, worst case is `O(n^d)` nodes.

**Mitigations**:

1. **Axiom-first ordering**: Check direct axiom matches before recursing on MP. This prunes
   trivially satisfied goals immediately without expanding the search tree.

2. **Goal syntactic matching**: Before trying modus ponens, check if the goal is syntactically
   an axiom schema instance using `Expr.eqv` or unification. The `observing?` pattern from
   BimodalLogic (as noted by Teammate A) ensures failed `goal.apply` attempts do not corrupt
   mvar state.

3. **Fuel decrement per MP step** (not per level): Each MP application decrements fuel by 1
   regardless of nesting depth. This prevents one long chain from consuming all fuel without
   attempting branching alternatives.

4. **Early termination on closed goal**: After each tactic application, check `goal.isAssigned`
   to detect if the goal is already closed without further work.

### 2.4 Performance Pitfalls with Typeclass Resolution

**Pitfall 1: Repeated typeclass resolution in loops**.
When iterating over axiom methods, calling `synthInstance? (mkApp ...)` inside a tight loop
can be expensive. Synthesize all typeclass instances ONCE before the search loop:
```lean
-- Resolve instances once, outside the search function
let modusPonensInst ← synthInstance? (mkApp (mkConst ``ModusPonens) #[S])
let implyKInst ← synthInstance? (mkApp2 (mkConst ``HasAxiomImplyK) S)
```

**Pitfall 2: `whnf` in tight inner loops**.
Calling `whnf goalType` at every search node is expensive. Cache the whnf'd goal type
at the top of each search call, not inside nested sub-searches.

**Pitfall 3: `isDefEq` for formula matching**.
Prefer syntactic unification (`Expr.eqv`, `MVarId.apply`) over `isDefEq` for formula
matching during axiom dispatch. The `observing?` pattern from BimodalLogic wraps failed
`apply` attempts without corrupting mvar state.

**Pitfall 4: Large term construction in `MetaM`**.
Building large proof terms via MetaM `mkAppM` is slower than using `Lean.MVarId.apply`.
Prefer the tactic-level `apply` which handles implicit argument synthesis automatically.

### 2.5 ITauto's Termination Approach (Reference Implementation)

`Mathlib.Tactic.ITauto` (744 lines) does NOT use fuel. Instead it uses the **G4ip algorithm**,
which terminates by tracking formula complexity (the "weight" of the sequent decreases with
each rule application). This works because intuitionistic logic has finite formula sets and the
rules are subformula-preserving.

For Hilbert-style proofs over `DerivableIn S φ` with opaque formulas, the G4ip approach is
not directly applicable because:
1. CSLib's formulas are opaque to the tactic (no built-in decomposition view)
2. Hilbert proof search may require generating new formulas (via weakening/ImplyK)

**Conclusion**: Fuel-based termination is the right choice for CSLib's Hilbert tactic. G4ip
is the right choice if/when CSLib adds a sequent calculus layer.

---

## 3. Testing Strategies for Proof-Search Tactics

### 3.1 How CSLib Tests Existing Automation

CSLib's testing pattern (from `CslibTests/`):

1. **Compile-time `example` blocks**: The dominant pattern (see `CslibTests/Propositional.lean`).
   Each test is a named `theorem` with a docstring, not anonymous `#check`. This means the
   test participates in `docBlame` linting for the test file.

2. **`#guard_msgs` for error output testing**: Used in `CslibTests/GrindLint.lean` (the
   `#guard_msgs in #grind_lint check` pattern). This captures expected output and fails
   if output changes.

3. **`decide` for decidable propositions**: `CslibTests/Propositional.lean` uses `by decide`
   extensively for small finite decidable examples.

4. **`lake test`**: Runs all `CslibTests/*.lean` files. Tests must be in the `CslibTests`
   namespace (by convention).

**Test file header** (from `CslibTests/Propositional.lean`):
```lean
module

public meta import Cslib.Foundations.Logic.Automation.HilbertSearch
-- Additional imports
```

Note: Test files use `public meta import` (not `public import`) because tactic code is
meta-level. The header of `CslibTests/Propositional.lean` uses `public meta import`.

**Test file structure**:
```lean
namespace CslibTests.HilbertSearch
-- Tests here
end CslibTests.HilbertSearch
```

### 3.2 What Test Patterns Work for Tactics

**Pattern 1: Positive compile-time tests** — verify the tactic closes the goal:
```lean
/-- hilbert_search closes identity: ⊢ φ → φ. -/
example [MinimalHilbert S (F := F)] (φ : F) :
    InferenceSystem.DerivableIn S (HasImp.imp φ φ) := by
  hilbert_search

/-- hilbert_search closes transitivity: from ⊢ φ→ψ and ⊢ ψ→χ, derive ⊢ φ→χ. -/
example [MinimalHilbert S (F := F)] {φ ψ χ : F}
    (h1 : InferenceSystem.DerivableIn S (HasImp.imp φ ψ))
    (h2 : InferenceSystem.DerivableIn S (HasImp.imp ψ χ)) :
    InferenceSystem.DerivableIn S (HasImp.imp φ χ) := by
  hilbert_search
```

**Pattern 2: Depth-sensitive positive tests** — verify search succeeds at known depths:
```lean
/-- hilbert_search 3 closes identity (depth bound confirmed). -/
example [MinimalHilbert S (F := F)] (φ : F) :
    InferenceSystem.DerivableIn S (HasImp.imp φ φ) := by
  hilbert_search 3
```

**Pattern 3: Negative tests using `success_if_fail_with_msg`** — verify graceful failure:
```lean
/-- hilbert_search fails with depth 0. -/
example [MinimalHilbert S (F := F)] (φ ψ : F) :
    InferenceSystem.DerivableIn S (HasImp.imp φ φ) := by
  success_if_fail_with_msg "hilbert_search failed: no proof found within depth limit 0"
    hilbert_search 0
  exact HasAxiomImplyK.implyK  -- close manually
```

**Pattern 4: Tests across multiple logics** — verify the tactic is truly generic:
```lean
open Cslib.Logic in
/-- hilbert_search works for modal logic K. -/
example [ModalHilbert S (F := F)] (φ ψ : F) :
    InferenceSystem.DerivableIn S (Axioms.ImplyK φ ψ) := by
  hilbert_search

open Cslib.Logic in
/-- hilbert_search works for propositional classical logic. -/
example [ClassicalHilbert S (F := F)] (φ ψ : F) :
    InferenceSystem.DerivableIn S (Axioms.ImplyK φ ψ) := by
  hilbert_search
```

### 3.3 Testing Failure at Expected Depths

To systematically test depth bounds, write tests that succeed at depth `d` but fail at `d-1`:
```lean
/-- flip combinator requires at least 10 steps. -/
example [MinimalHilbert S (F := F)] {φ ψ χ : F} :
    InferenceSystem.DerivableIn S (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
      (HasImp.imp ψ (HasImp.imp φ χ))) := by
  -- Should succeed at default depth 30
  hilbert_search

/-- flip combinator fails at depth 5 (requires ~10 steps). -/
example [MinimalHilbert S (F := F)] {φ ψ χ : F} :
    InferenceSystem.DerivableIn S (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
      (HasImp.imp ψ (HasImp.imp φ χ))) := by
  success_if_fail_with_msg "hilbert_search failed"
    hilbert_search 5
  exact Cslib.Logic.Theorems.Combinators.flip  -- close manually
```

### 3.4 `#guard_msgs` for Output Verification

For verifying that diagnostic messages have the right format:
```lean
/--
error: hilbert_search failed: no proof found within depth limit 0.
Goal: InferenceSystem.DerivableIn S (HasImp.imp φ φ)
-/
#guard_msgs in
example [MinimalHilbert S (F := F)] (φ : F) :
    InferenceSystem.DerivableIn S (HasImp.imp φ φ) := by
  hilbert_search 0
```

This approach is used in `CslibTests/GrindLint.lean` and is the standard Lean 4 pattern
for testing tactic error output.

---

## 4. Error Messages and Diagnostics

### 4.1 How Lean 4 Tactics Report Failure

The canonical pattern (from `Mathlib/Tactic/Contrapose.lean`):
```lean
throwTacticEx `tacticName goal m!"human-readable message with {interpolated} {values}"
```

This throws a `TacticException` associated with the goal mvar, which Lean displays with
the goal context automatically appended.

For the `hilbert_search` tactic:
```lean
throwTacticEx `hilbertSearch goal
  m!"hilbert_search failed: no proof found within depth limit {fuel}.\n\
     Goal: {← ppExpr goalType}\n\
     Hint: try a larger depth limit (e.g., `hilbert_search {fuel * 2}`)"
```

**Alternative**: `Macro.throwError` is for macro-level parse failures (wrong syntax),
not tactic runtime failures. Use `throwTacticEx` for runtime search failures.

### 4.2 Best Practices for Search Failure Messages

Based on the Lean 4 / Mathlib tactic ecosystem standards:

**Include in failure message**:
1. The tactic name (to identify which tactic failed)
2. The depth limit that was used (actionable: user knows to increase it)
3. The goal type (shows what was being attempted)
4. A remediation hint (how to try again)

**Do NOT include** in failure message:
- Internal search tree state (too verbose for normal use)
- Stack traces from Lean's MetaM (confusing to users)
- Large expression pretty-prints for complex formulas

**Example well-formatted failure**:
```
hilbert_search failed: no proof found within depth limit 30.
Goal: InferenceSystem.DerivableIn S (HasImp.imp φ (HasImp.imp φ φ))
Hint: try `hilbert_search 60` for a deeper search, or check that the goal
      is a theorem of the currently assumed Hilbert system.
```

### 4.3 Debuggable Traces via `registerTraceClass`

For debugging the search algorithm, register a trace class and use `withTraceNode`:

```lean
initialize registerTraceClass `Cslib.Logic.hilbertSearch
initialize registerTraceClass `Cslib.Logic.hilbertSearch.verbose
```

Usage in the search function:
```lean
withTraceNode `Cslib.Logic.hilbertSearch
  (fun _ => return m!"hilbert_search at depth {fuel}: trying {← ppExpr goal}") do
  trace[Cslib.Logic.hilbertSearch.verbose] "Trying axiom: {axiomName}"
  ...
```

Users can enable debugging with:
```lean
set_option trace.Cslib.Logic.hilbertSearch true
```

This pattern is used in `Mathlib.Tactic.FunProp` (registered in
`Mathlib/Tactic/FunProp/Types.lean` with `registerTraceClass ``Meta.Tactic.fun_prop`) and
in the `aesop` package (`Aesop/Saturate.lean`).

### 4.4 Verbose Mode with `?` Suffix

A `hilbert_search?` variant should report the found proof as a `Try this:` suggestion.
This follows the Mathlib convention (used by `exact?`, `apply?`, `simp?`).

Lean 4 provides `Lean.MVarId.TryThis.addSuggestion` for this. The suggestion would be
the explicit derivation chain (e.g., `exact ModusPonens.mp HasAxiomImplyK.implyK ...`).

---

## 5. Critical Pitfalls and Anti-Patterns

### 5.1 Using `lean_diagnostic_messages` or `lean_file_outline`

These tools are blocked (known bugs in lean-lsp-mcp). Do not use them during implementation.

### 5.2 Returning a `sorry`-Based Proof

Any implementation that produces `sorry` (even indirectly, as a vacuous definition like
`def X := True`) violates CSLib's zero-debt policy. The tactic must either:
- Return a genuine proof via `Nonempty.intro` wrapping a concrete derivation, OR
- Fail explicitly via `throwTacticEx`

### 5.3 Non-Terminating Meta Code

In `public meta section` blocks, Lean does not enforce structural termination. Unbounded
loops (e.g., `while true do`) will cause the elaborator to hang. All search functions
must be explicitly fuel-limited.

**Safe pattern**:
```lean
/-- Bounded search: terminates because fuel is structural. -/
def hilbertSearchFuel [ClassicalHilbert S (F := F)]
    (fuel : Nat) : Option ... :=
  match fuel with | 0 => none | n + 1 => ...  -- structural recursion on Nat
```

**Unsafe pattern** (will not typecheck without `partial`):
```lean
-- AVOID: requires `partial` or explicit termination proof
def hilbertSearchLoop (depth : Nat) : Option ... :=
  if depth = 0 then none else ...  -- if-then-else is not structural
```

### 5.4 Adding `@[simp]` to the Search Function or Its Helpers

Adding `@[simp]` to search-related functions or intermediate combinators risks triggering
`simpNF` lint failures and slow simp performance. Only add `@[simp]` to genuine algebraic
simplification lemmas, not to proof-search helpers.

### 5.5 Missing `omit` for Unused Section Variables

If the implementation file uses `variable` declarations (common in CSLib), and some
definitions do not use all variables, add `omit` to silence the `unusedSectionVars` linter:
```lean
variable {S : Type*} [InferenceSystem S F] [MinimalHilbert S]

-- This def doesn't use MinimalHilbert; omit it
omit [MinimalHilbert S] in
def goalIsDerivable (goal : F) : Bool := ...
```

### 5.6 Forgetting `lake exe mk_all` After Adding Files

Every new `.lean` file must be registered in `Cslib.lean` (the barrel import). Run:
```bash
lake exe mk_all --module
```
after adding `HilbertSearch.lean`. Without this, `lake test` will miss the new file.

### 5.7 The `GrindLint` Test for `@[scoped grind]` Annotations

If any search helper carries `@[scoped grind =]` (as `rwConclusion` does in InferenceSystem),
it may trigger the `GrindLint.lean` test. Check:
```bash
lake test -- runs GrindLint.lean among others
```
If a new annotation causes `#grind_lint check` to fail, add a skip entry:
```lean
#grind_lint skip Cslib.Logic.Automation.newHelper
```

---

## 6. Placement Summary

### Recommended Structure

```
Cslib/Foundations/Logic/
└── Automation/
    └── HilbertSearch.lean     -- main tactic file
```

**Namespace**: `Cslib.Logic.Automation`

**File header**:
```lean
/-
Copyright (c) 2026 <Authors>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <Authors>
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.ProofSystem
-- Additional imports as needed
```

**Main declaration structure**:
```
-- @[expose] public section: Pure term-mode bounded search
-- public meta section:
--   1. registerTraceClass for debugging
--   2. Goal extraction helper (extractDerivableGoal)
--   3. Axiom-dispatch function (tryAxioms)
--   4. Core search loop (hilbertSearchMeta, fuel-limited)
--   5. Tactic elaboration (syntax + elab_rules)
```

### Test File

```
CslibTests/HilbertSearch.lean
```

Uses `public meta import Cslib.Foundations.Logic.Automation.HilbertSearch`.

### CI Steps After Implementation

In order:
1. `lake build` — build and check syntax linters
2. `lake exe checkInitImports` — verify Cslib.Init import present
3. `lake lint` — check docBlame, defLemma, defsWithUnderscore, simpNF, unusedSectionVars,
   topNamespace, dupNamespace
4. `lake exe lint-style` — check text linters
5. `lake test` — run CslibTests (includes new HilbertSearch.lean tests)
6. `lake exe mk_all --module` — update Cslib.lean
7. `lake shake --add-public --keep-implied --keep-prefix` — minimize imports

---

## 7. Summary of Key Findings

- **File location**: `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` under namespace
  `Cslib.Logic.Automation`
- **Section pattern**: Term-mode search in `@[expose] public section`; tactic elaboration
  in `public meta section`; trace class registration via `registerTraceClass`
- **Fuel termination**: Structural recursion on `Nat` fuel, default 30, maximum ~100
- **Depth expectations**: Most Hilbert theorems in CSLib require 3–20 steps; `app2`-level
  proofs use ~20 steps; default fuel of 30 covers observed proofs
- **Blowup mitigation**: Axiom-first ordering, `observing?` pattern for safe `apply` attempts,
  fuel-per-MP-step (not per-depth-level)
- **Testing**: `example` blocks with `success_if_fail_with_msg` for negative cases;
  `#guard_msgs` for error message format; cross-logic tests for genericity
- **Error messages**: Use `throwTacticEx` with depth limit, goal type, and remediation hint;
  register trace class for `set_option trace.Cslib.Logic.hilbertSearch true`
- **Lint compliance**: docBlame (all declarations need docstrings), defsWithUnderscore
  (no underscores in Lean declaration names), topNamespace (instances in namespace),
  defLemma (Prop-valued declarations use `lemma`/`theorem` not `def`), unusedSectionVars
  (`omit` for unused variables)
- **Grind lint**: New `@[scoped grind]` annotations require passing `CslibTests/GrindLint.lean`;
  add `#grind_lint skip` entries for any that cause runaway instantiation
