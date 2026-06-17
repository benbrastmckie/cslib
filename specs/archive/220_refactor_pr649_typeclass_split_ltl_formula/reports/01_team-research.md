# Research Report: Task #220

**Task**: Refactor PR #649: typeclass split and LTL formula
**Date**: 2026-06-15
**Mode**: Team Research (4 teammates)

## Summary

PR #649 adds temporal logic connective typeclasses and formula types to CSLib. Reviewer feedback from Matthew (abstract MCS/Deduction Theorem into classes) and ctchou (future-only operators, LTS connection, remove irrelevant instances) requires a follow-up commit. Research confirms the proposed `FutureTemporalConnectives` / `LTLConnectives` hierarchy is sound, and that Matthew's abstraction request is already satisfied by existing `GenericMCS.lean` infrastructure. The minimal viable commit adds 3 new typeclasses to `Connectives.lean`, creates `LTL.Formula` with primitive `next`, removes irrelevant instances from `Temporal.Formula`, and optionally adds basic omega-word satisfaction semantics.

## Key Findings

### 1. Matthew's Abstraction Is Already Implemented

All 4 teammates confirmed: CSLib's `GenericMCS.lean` already provides `algebraicDerivationSystem` and `algebraic_has_deduction_theorem` for ANY logic with `MinimalHilbert` (K + S + MP). The Isabelle locale approach Matthew referenced is explicitly cited in `GenericMCS.lean:27`. No new MCS or deduction theorem machinery is needed. The correct response to Matthew is to demonstrate that LTL inherits this infrastructure when a proof system is eventually added.

**Evidence**: `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` lines 42-61.

### 2. Typeclass Hierarchy Design: Restructure on PR Branch, Additive on Main

**Conflict resolved**: Teammates A and B recommended restructuring `TemporalConnectives` to extend `FutureTemporalConnectives`. Teammate D recommended keeping it additive. Teammate C's critical finding resolves this: **the PR branch's `Connectives.lean` does NOT include `HasBox`, `ModalConnectives`, or `BimodalConnectives`** — it's a stripped-down version with only `PropositionalConnectives` and `TemporalConnectives`. Therefore:

- On the PR branch, changing `TemporalConnectives extends FutureTemporalConnectives, HasSince` is safe (no diamond risk).
- The main branch's `BimodalConnectives` diamond concern is irrelevant to the PR scope.
- When the PR eventually merges to main, `BimodalConnectives` already avoids extending `TemporalConnectives` directly (explicit anti-diamond comment at `Connectives.lean:127-130`).

**Recommended hierarchy** (on the PR branch):
```
PropositionalConnectives (HasBot + HasImp)      [UNCHANGED]
            |
FutureTemporalConnectives (+ HasUntil)          [NEW]
       /                \
LTLConnectives      TemporalConnectives
 (+ HasNext)           (+ HasSince)             [MODIFIED parent]
```

### 3. `HasNext` Must Be a Primitive Atomic Typeclass

All teammates agree: `HasNext` should be an independent typeclass (like `HasBox`, `HasUntil`), NOT derived from `HasUntil`. Key reasons:

- **Semantic correctness**: `next φ := φ U ⊥` is ALWAYS FALSE in dense time models (because there's always a point between t and s where guard ⊥ fails). `next` is only meaningful as a primitive in discrete (omega-word) semantics.
- **Lean 4 coherence**: `LTL.Formula.next` as a constructor is definitionally distinct from `untl φ bot`, so they can't be auto-unified by the typeclass system.
- **Existing pattern**: `HasBox` and `HasDia` are independent typeclasses in modal logic, not derived from each other.

A compatibility theorem `ltl_next_eq_untl_bot` in the `toTemporal` embedding handles the bridge.

### 4. `LTL.Formula` Should Be a New Inductive

All teammates favor Option A (new inductive `{atom, bot, imp, next, untl}`) over subtype or type synonym approaches:

- Consistent with CSLib pattern: each logic gets its own inductive type.
- `next` as a primitive constructor enables clean structural induction for future completeness proofs.
- `toTemporal : LTL.Formula → Temporal.Formula` embedding is a clean homomorphism mapping `next φ` to `untl (toTemporal φ) bot`.
- No code duplication concern for this PR (Encodable/BEq deferred).

### 5. Keep `snce` in `Temporal.Formula`

Removing `snce` from `Temporal.Formula` would break the entire temporal metalogic (`MCS.lean`, `DeductionTheorem.lean`, `GeneralizedNecessitation.lean`, `CompletenessHelpers.lean`, etc.). All teammates agree: keep `Temporal.Formula` as-is with both `untl` and `snce`. The new `LTL.Formula` simply doesn't include `snce`.

### 6. What to Remove from the PR

ctchou explicitly called out Encodable/Countable/Infinite/Denumerable instances as "completely irrelevant." Recommended removals from `Temporal/Syntax/Formula.lean`:

- Remove `public import Mathlib.Logic.Encodable.Basic`
- Remove `public import Mathlib.Logic.Denumerable`
- Remove the entire `Countability` section (lines 167-257)
- Remove manual `BEq`/`LawfulBEq` proofs (lines 259-333), keeping `deriving DecidableEq, BEq`
- Remove `public import Mathlib.Data.Finset.Basic` (only used for `atoms` Finset, which depends on DecidableEq not Encodable — verify)

### 7. LTL Satisfaction Semantics: Minimal Scope

**Conflict resolved**: Teammates B and D favor including basic omega-word semantics. Teammate C warns of scope creep. Compromise: include a minimal satisfaction relation definition over `ℕ → (Atom → Prop)` (no proofs about it, just the inductive definition). This shows responsiveness to ctchou's "omega-execution" request without creating proof obligations.

```lean
def Satisfies (v : ℕ → Atom → Prop) (i : ℕ) : Formula Atom → Prop
  | .atom p   => v i p
  | .bot      => False
  | .imp φ ψ  => Satisfies v i φ → Satisfies v i ψ
  | .next φ   => Satisfies v (i + 1) φ
  | .untl φ ψ => ∃ j, j > i ∧ Satisfies v j φ ∧ ∀ k, i < k → k < j → Satisfies v k ψ
```

The LTS bridge (connecting `OmegaExecution` to LTL satisfaction) should be deferred.

## Synthesis

### Conflicts Resolved

| Conflict | Resolution |
|----------|------------|
| Restructure vs. additive TemporalConnectives | Restructure on PR branch (safe — no BimodalConnectives in PR scope) |
| Include vs. defer LTL semantics | Include minimal definition only (no proofs), defer LTS bridge |
| Remove vs. keep snce in Temporal.Formula | Keep snce (metalogic depends on it); LTL.Formula excludes it |

### Gaps Identified

1. **Burgess convention documentation**: LTL.Formula should clearly document that `untl event guard` follows Burgess convention (first arg = event, second = guard). Standard LTL papers reverse this.
2. **LTS integration**: ctchou's request to "talk about omega-executions of LTS" is not fully addressed by omega-word semantics alone. The bridge from `LTS.OmegaExecution` to `LTLModel` should be noted as future work.
3. **Reviewer intent validation**: Whether ctchou wants `HasSince` removed from the PR entirely vs. retained in `TemporalConnectives` is ambiguous. The safe interpretation: keep `TemporalConnectives` with `HasSince`, create LTL without it.
4. **PR branch vs. main divergence**: The PR branch has a simplified `Connectives.lean`. Any changes must target the PR branch state, not main.

### Recommendations

#### Minimum Viable Commit (files changed/created):

1. **`Cslib/Foundations/Logic/Connectives.lean`** (MODIFY):
   - Add `HasNext` typeclass
   - Add `FutureTemporalConnectives extends PropositionalConnectives, HasUntil`
   - Add `LTLConnectives extends FutureTemporalConnectives, HasNext`
   - Change `TemporalConnectives` to `extends FutureTemporalConnectives, HasSince`

2. **`Cslib/Logics/Temporal/Syntax/Formula.lean`** (MODIFY):
   - Remove Encodable/Countable/Infinite/Denumerable instances and imports
   - Remove manual BEq proofs (keep `deriving DecidableEq, BEq`)
   - Update `TemporalConnectives` instance (unchanged fields, but class parent changed)

3. **`Cslib/Logics/LTL/Syntax/Formula.lean`** (NEW):
   - Inductive `{atom, bot, imp, next, untl}` with `next` as primitive constructor
   - `LTLConnectives` instance
   - Derived connectives: `neg`, `top`, `or`, `and`, `someFuture`, `allFuture`
   - `toTemporal : LTL.Formula → Temporal.Formula` embedding
   - Scoped notation

4. **`Cslib/Logics/LTL/Semantics/Satisfies.lean`** (NEW, optional):
   - Basic satisfaction relation over `ℕ → (Atom → Prop)`
   - No proof obligations (just the definition + `Valid`, `Satisfiable` predicates)

5. **`Cslib.lean`** (MODIFY): Update barrel imports via `lake exe mk_all --module`

6. **`references.bib`** (MODIFY if needed): Add Vardi & Wolper 1986 if not already present

#### What NOT to Include:
- MCS / Lindenbaum for LTL (GenericMCS handles it when proof system is added)
- LTL proof system / axiom typeclasses / derivation trees
- LTS bridge (connecting OmegaExecution to LTL semantics)
- Past-time operators in LTL
- Countability/BEq instances for LTL.Formula

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary implementation approach | completed | high |
| B | Alternative patterns and prior art | completed | high |
| C | Critic: gaps and blind spots | completed | high |
| D | Strategic horizons | completed | high |

## References

- Kamp, H. (1968). *Tense Logic and the Theory of Linear Order*
- Vardi, M. Y. & Wolper, P. (1986). *An Automata-Theoretic Approach to Automatic Program Verification*
- Burgess, J. P. (1982). *Axioms for Tense Logic*
- CSLib `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — algebraic MCS framework
- CSLib `Cslib/Foundations/Logic/ProofSystem.lean` — MinimalHilbert typeclass
- CSLib `Cslib/Foundations/Semantics/LTS/OmegaExecution.lean` — omega-execution infrastructure
- Isabelle `Propositional_Logic_Class.thy` — locale-based propositional axiom abstraction (cited in GenericMCS.lean)
