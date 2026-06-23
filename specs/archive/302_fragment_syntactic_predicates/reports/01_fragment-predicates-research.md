# Research Report: Fragment Syntactic Predicates and Independence Lemmas

**Task**: 302 — Fragment Syntactic Predicates and Independence Lemmas
**Date**: 2026-06-23
**Status**: Complete

## 1. Existing Pattern Analysis

### 1.1 IsBotFree Reference Implementation

File: `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`

`IsBotFree` is a `Bool`-valued recursive predicate on `Proposition Atom`:
- `.atom _` => `true`
- `.bot` => `false`
- `.imp a b` => `a.IsBotFree && b.IsBotFree`
- `.and a b` => `a.IsBotFree && b.IsBotFree`
- `.or a b` => `a.IsBotFree && b.IsBotFree`

The independence theorem `AlgEvaluate_botFree_independent` proves that for bot-free formulas,
`AlgEvaluate v b1 A = AlgEvaluate v b2 A` (evaluation is independent of `bot_val`). Proof
strategy: induction on `A`, `simp [Proposition.IsBotFree] at hA` to decompose the conjunction
in binary cases, then `simp` with the simp lemmas `AlgEvaluate_imp`, `AlgEvaluate_and`,
`AlgEvaluate_or` and the inductive hypotheses.

### 1.2 AlgEvaluate Operation Mapping

From `Cslib/Logics/Propositional/Semantics/Algebra.lean`, the evaluator maps connectives to
algebraic operations on a `GeneralizedHeytingAlgebra H`:

| Constructor | Algebraic Operation | Parameters Used |
|-------------|---------------------|-----------------|
| `.atom x` | `v x` | `v` only |
| `.bot` | `bot_val` | `bot_val` only |
| `.imp a b` | `eval a ⇨ eval b` | `⇨` (Heyting implication) |
| `.and a b` | `eval a ⊓ eval b` | `⊓` (meet/inf) |
| `.or a b` | `eval a ⊔ eval b` | `⊔` (join/sup) |

The `GeneralizedHeytingAlgebra` typeclass provides all four: `⊓`, `⊔`, `⇨`, `⊤`. The `bot_val`
is an explicit parameter (not from the typeclass).

### 1.3 Proposition Type

From `Cslib/Logics/Propositional/Defs.lean`:
- 5 constructors: `atom`, `bot`, `imp`, `and`, `or`
- `subst` is defined recursively, distributing over all constructors
- Derived: `neg A := A.imp .bot`, `top := .imp .bot .bot`, `iff A B := (A.imp B).and (B.imp A)`

## 2. New Predicate Definitions

### 2.1 IsOrFree

Formulas containing no disjunction (`.or`). Uses only `atom`, `bot`, `imp`, `and`.

```lean
def Proposition.IsOrFree : Proposition Atom → Bool
  | .atom _ => true
  | .bot => true
  | .imp a b => a.IsOrFree && b.IsOrFree
  | .and a b => a.IsOrFree && b.IsOrFree
  | .or _ _ => false
```

**Independence**: For or-free formulas, `AlgEvaluate` never invokes `⊔` (join). Given two
algebras that agree on `⊓`, `⇨`, `⊤`, and `bot_val`, the evaluation is identical.

The precise statement: if `A.IsOrFree = true`, then `AlgEvaluate` depends only on `v`, `bot_val`,
`⇨`, and `⊓` -- it is independent of `⊔`. However, this cannot be stated as simply as the
bot-free case (where we vary a single parameter `bot_val`), because `⊔` is baked into the
`GeneralizedHeytingAlgebra` typeclass. The useful form for downstream tasks is:

**For task 306/307**: Given a `BrouwerianSemilattice B` (once defined in task 303 -- a
`SemilatticeInf` + `OrderTop` + `HImp`) and a `HeytingAlgebra H` with an embedding
`ι : B → H` preserving `⊓`, `⇨`, `⊤`, we need: for or-free formulas,
`AlgEvaluate (ι ∘ v) bot_val_H A = ι (BrouwerianEvaluate v A)`.

But **for this task**, the right form parallels `AlgEvaluate_botFree_independent`: we need to
show evaluation doesn't touch `⊔`. Since `⊔` is a typeclass field (not a free parameter like
`bot_val`), the cleanest approach is a **generalized evaluator** or a direct statement:

> For any two `GeneralizedHeytingAlgebra` instances on the same type `H` that agree on `⊓`, `⇨`,
> and `⊤`, and for any or-free formula `A`, `AlgEvaluate` under instance 1 equals `AlgEvaluate`
> under instance 2.

This is complex. The simpler and more useful approach (matching how Conservative.lean actually
uses the independence) is to define a **fragment evaluator** and prove it agrees with
`AlgEvaluate` on the appropriate fragment. But the task description says "independence lemmas
for each" analogous to the bot-free case.

**Recommended approach**: Define the predicates, prove the evaluator-agrees-on-fragment lemma
using a direct structural approach. For `IsOrFree`, prove:

```lean
theorem AlgEvaluate_orFree_eq
    {H : Type*} [inst1 inst2 : GeneralizedHeytingAlgebra H]
    (h_inf : @Inf.inf H inst1.toInf = @Inf.inf H inst2.toInf)
    (h_himp : @HImp.himp H inst1.toHImp = @HImp.himp H inst2.toHImp)
    (h_top : @Top.top H inst1.toTop = @Top.top H inst2.toTop)
    (v : Atom → H) (bot_val : H) (A : Proposition Atom)
    (hA : A.IsOrFree = true) :
    @AlgEvaluate _ H inst1 v bot_val A = @AlgEvaluate _ H inst2 v bot_val A
```

However, this may be overly complex and hard to use downstream. Let me reconsider.

**Actually, the simplest useful pattern** mirrors `AlgEvaluate_botFree_independent` directly.
For or-free formulas, we want to show evaluation doesn't use `⊔`. The practical statement is:

```lean
theorem AlgEvaluate_orFree_independent
    {Atom : Type*} {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) (j₁ j₂ : H → H → H) (A : Proposition Atom)
    (hA : A.IsOrFree = true) :
    AlgEvaluateWith v bot_val j₁ A = AlgEvaluateWith v bot_val j₂ A
```

But this requires a parameterized evaluator `AlgEvaluateWith` that takes `join` as a parameter.
That's a non-trivial change to the architecture.

**Best approach for this task**: After studying the Conservative.lean usage pattern more
carefully, the independence lemmas are **not** used in isolation -- they're used as part of
an embedding lemma (like `coe_AlgEvaluate`). The embedding lemma is what the conservative
extension actually needs. So the independence lemmas serve as stepping stones.

For the fragment predicates task, I recommend:

1. **Define the three predicates** (straightforward, following `IsBotFree` pattern)
2. **Prove conjunction closure** (if `A.IsOrFree` and `B.IsOrFree` then `(A.imp B).IsOrFree` etc.)
3. **Prove substitution closure** (if `A.IsOrFree` and all `f x` are or-free, then `(A.subst f).IsOrFree`)
4. **Prove the subsumption hierarchy** (`IsImpTopOnly → IsOrBotFree → IsOrFree`, `IsBotFree ∧ IsOrFree → IsOrBotFree`)
5. **Prove structural independence lemmas** using the pattern: for or-free formulas, evaluation in any GHA equals evaluation in a GHA where `⊔` has been replaced, formalized by working with two GHA instances

After further reflection, the cleanest independence statement that avoids needing a parameterized
evaluator is this: define the independence as "evaluation factors through a restricted evaluator."
Specifically, define restricted evaluators for each fragment and prove they agree with
`AlgEvaluate` on the fragment. This is what the embedding lemmas (tasks 307, 311) will need.

**However**, looking again at the task description: "or-free evaluation is independent of the
join operation, imp-top-only evaluation is independent of join, meet, and bot_val." The task
description explicitly asks for independence from specific operations.

The most practical formulation uses `@`-notation to access different GHA instances:

```lean
/-- For or-free formulas, AlgEvaluate is independent of the join (⊔) operation. -/
theorem AlgEvaluate_orFree_independent_of_sup
    {H : Type*} [inst₁ inst₂ : GeneralizedHeytingAlgebra H]
    (h_inf : @Inf.inf H inst₁.toInf = @Inf.inf H inst₂.toInf)
    (h_himp : @HImp.himp H inst₁.toHImp = @HImp.himp H inst₂.toHImp)
    (h_top : @Top.top H inst₁.toTop = @Top.top H inst₂.toTop)
    (v : Atom → H) (bot_val : H) (A : Proposition Atom)
    (hA : A.IsOrFree = true) :
    @AlgEvaluate _ H inst₁ v bot_val A = @AlgEvaluate _ H inst₂ v bot_val A
```

This is clean, provable by structural induction, and directly states the independence.

### 2.2 IsOrBotFree

Formulas containing neither disjunction nor falsum. Uses only `atom`, `imp`, `and`.

```lean
def Proposition.IsOrBotFree : Proposition Atom → Bool
  | .atom _ => true
  | .bot => false
  | .imp a b => a.IsOrBotFree && b.IsOrBotFree
  | .and a b => a.IsOrBotFree && b.IsOrBotFree
  | .or _ _ => false
```

**Independence**: doesn't use `⊔` or `bot_val`. Statement:

```lean
theorem AlgEvaluate_orBotFree_independent
    {H : Type*} [inst₁ inst₂ : GeneralizedHeytingAlgebra H]
    (h_inf : @Inf.inf H inst₁.toInf = @Inf.inf H inst₂.toInf)
    (h_himp : @HImp.himp H inst₁.toHImp = @HImp.himp H inst₂.toHImp)
    (h_top : @Top.top H inst₁.toTop = @Top.top H inst₂.toTop)
    (v : Atom → H) (b₁ b₂ : H) (A : Proposition Atom)
    (hA : A.IsOrBotFree = true) :
    @AlgEvaluate _ H inst₁ v b₁ A = @AlgEvaluate _ H inst₂ v b₂ A
```

Note: this combines the `IsBotFree`-style `bot_val` independence with the `IsOrFree`-style
`⊔` independence. It subsumes both `AlgEvaluate_botFree_independent` (when restricted to
or-free formulas) and `AlgEvaluate_orFree_independent` (when `bot_val` is also varied).

### 2.3 IsImpTopOnly

Formulas using only implication and atoms. No conjunction, disjunction, or falsum. Since
`⊤ := ⊥ → ⊥`, formulas containing `⊤` as a derived connective actually contain `⊥`. So
"imp-top-only" means: only `.atom` and `.imp` constructors (plus `⊤` which unfolds to `.imp .bot .bot`).

Wait -- there is a subtlety. `Proposition.top` is `abbrev`'d as `.imp .bot .bot`. If we define
`IsImpTopOnly` to reject `.bot`, then `⊤` (which unfolds to `⊥ → ⊥`) would be rejected. But
the task says "only implication and atoms (no conjunction, disjunction, or falsum)."

Looking at the task description again: "IsImpTopOnly -- only implication and atoms (no
conjunction, disjunction, or falsum)." This means `.bot` is excluded. The name is slightly
misleading -- it's really "IsImpAtomOnly" since `⊤` would need `.bot` in its definition. But
following the task description:

```lean
def Proposition.IsImpTopOnly : Proposition Atom → Bool
  | .atom _ => true
  | .bot => false
  | .imp a b => a.IsImpTopOnly && b.IsImpTopOnly
  | .and _ _ => false
  | .or _ _ => false
```

Actually, reconsidering: the task says "IsImpTopOnly" and the downstream task 309 is about
`IPL⟨→,⊤⟩` which is the implicational fragment. The `ImpAxiom` from task 305 has only K and S
axioms, which are purely implicational (no `.bot`, `.and`, `.or`). So the predicate should allow
only `.atom` and `.imp`. Since `⊤ = ⊥ → ⊥` uses `.bot`, the name "ImpTopOnly" is a bit of a
misnomer for the syntactic predicate -- it's really "ImpOnly" at the syntax level.

**Resolution**: The intended meaning is that the *logic fragment* allows `→` and `⊤`, but at the
`Proposition` syntax level, `⊤` is derived from `.bot` and `.imp`. For Hilbert algebra
completeness (task 309), the formulas that matter are the ones generated by the `ImpAxiom`
constructors (K and S), which only use `.imp` and `.atom`. So the predicate should reject
`.bot`, `.and`, and `.or`.

However, for the independence lemma to be useful with `⊤`, we need to handle `⊤ = ⊥ → ⊥`
appearing in derivations. The solution: the independence lemma will show evaluation depends
only on `⇨` (not on `⊓`, `⊔`, or `bot_val`). If `⊤` appears as `⊥ → ⊥`, it evaluates to
`bot_val ⇨ bot_val`, which depends on `bot_val` and `⇨`. But since `bot_val ⇨ bot_val = ⊤`
in any GHA (by `le_himp_iff` with `le_refl`), this is actually `⊤` regardless.

**Final definition**: Following the task description literally, `IsImpTopOnly` rejects `.bot`:

```lean
def Proposition.IsImpTopOnly : Proposition Atom → Bool
  | .atom _ => true
  | .bot => false
  | .imp a b => a.IsImpTopOnly && b.IsImpTopOnly
  | .and _ _ => false
  | .or _ _ => false
```

**Independence**:

```lean
theorem AlgEvaluate_impTopOnly_independent
    {H : Type*} [inst₁ inst₂ : GeneralizedHeytingAlgebra H]
    (h_himp : @HImp.himp H inst₁.toHImp = @HImp.himp H inst₂.toHImp)
    (h_top : @Top.top H inst₁.toTop = @Top.top H inst₂.toTop)
    (v : Atom → H) (b₁ b₂ : H) (A : Proposition Atom)
    (hA : A.IsImpTopOnly = true) :
    @AlgEvaluate _ H inst₁ v b₁ A = @AlgEvaluate _ H inst₂ v b₂ A
```

Note: this is independent of `⊓`, `⊔`, AND `bot_val`. The `.bot` case is vacuously true
(rejected by the predicate), and `.and`/`.or` cases are likewise vacuous.

## 3. Subsumption Hierarchy

The predicates form a natural containment chain:

```
IsImpTopOnly ⊆ IsOrBotFree ⊆ IsOrFree
                IsOrBotFree ⊆ IsBotFree
```

Formally:
- `IsImpTopOnly_implies_IsOrBotFree`: `A.IsImpTopOnly = true → A.IsOrBotFree = true`
- `IsOrBotFree_implies_IsOrFree`: `A.IsOrBotFree = true → A.IsOrFree = true`
- `IsOrBotFree_implies_IsBotFree`: `A.IsOrBotFree = true → A.IsBotFree = true`
- `IsOrBotFree_iff`: `A.IsOrBotFree = true ↔ A.IsOrFree = true ∧ A.IsBotFree = true`

These are all straightforward by structural induction.

## 4. Closure Properties

### 4.1 Conjunction Closure (Connective Preservation)

Each predicate is closed under the connectives allowed in its fragment:

For `IsOrFree`:
- `imp_isOrFree`: `A.IsOrFree → B.IsOrFree → (A.imp B).IsOrFree`
- `and_isOrFree`: `A.IsOrFree → B.IsOrFree → (A.and B).IsOrFree`

For `IsOrBotFree`:
- `imp_isOrBotFree`: `A.IsOrBotFree → B.IsOrBotFree → (A.imp B).IsOrBotFree`
- `and_isOrBotFree`: `A.IsOrBotFree → B.IsOrBotFree → (A.and B).IsOrBotFree`

For `IsImpTopOnly`:
- `imp_isImpTopOnly`: `A.IsImpTopOnly → B.IsImpTopOnly → (A.imp B).IsImpTopOnly`

These follow immediately from the definition (just `Bool.and_eq_true_iff` + conjunction).

### 4.2 Substitution Closure

For downstream task 305 (fragment proof systems), we need: if `A` is in a fragment and all
substitution images `f x` are in the fragment, then `A.subst f` is in the fragment.

```lean
theorem subst_preserves_isOrFree (A : Proposition Atom)
    (hA : A.IsOrFree = true) (f : Atom → Proposition Atom')
    (hf : ∀ x, (f x).IsOrFree = true) :
    (A.subst f).IsOrFree = true

theorem subst_preserves_isOrBotFree (A : Proposition Atom)
    (hA : A.IsOrBotFree = true) (f : Atom → Proposition Atom')
    (hf : ∀ x, (f x).IsOrBotFree = true) :
    (A.subst f).IsOrBotFree = true

theorem subst_preserves_isImpTopOnly (A : Proposition Atom)
    (hA : A.IsImpTopOnly = true) (f : Atom → Proposition Atom')
    (hf : ∀ x, (f x).IsImpTopOnly = true) :
    (A.subst f).IsImpTopOnly = true
```

Proof pattern: induction on `A`, using the hypothesis `hf` at atoms and the conjunction
decomposition at binary connectives. The `.bot`, `.or`, `.and` (for ImpTopOnly) cases are
vacuously true since the predicate returns `false`.

## 5. Independence Lemma Proof Strategy

### 5.1 Approach: Two-Instance Formulation

The cleanest approach uses two GHA instances on the same carrier type, requiring only the
operations used by the fragment to agree. This avoids needing a parameterized evaluator.

**Proof technique**: Structural induction on `A`. For each case:
- **atom**: `AlgEvaluate v bot_val (.atom x) = v x` under both instances. Equal by `rfl`.
- **bot**: Either vacuous (predicate rejects it) or uses `bot_val` directly.
- **imp**: `AlgEvaluate v b (.imp a b) = eval a ⇨ eval b`. By IH, `eval a` and `eval b` agree.
  By `h_himp`, `⇨` agrees. So the results agree.
- **and**: Similar, using `h_inf`.
- **or**: Either vacuous (predicate rejects it) or uses `h_sup`.

The key technical detail: we need `funext`-style equalities for the typeclass operations
(`h_inf : @Inf.inf H inst1.toInf = @Inf.inf H inst2.toInf`). Then `congr` or `simp` with
these equalities handles the connective cases.

Actually, there is a cleaner alternative: use `congrArg` after proving the recursive evaluations
agree. Since `@AlgEvaluate` unfolds to pattern matching, we need:

```lean
show @AlgEvaluate _ H inst₁ v b₁ (.imp a c) = @AlgEvaluate _ H inst₂ v b₂ (.imp a c)
-- unfolds to:
show @HImp.himp H inst₁.toHImp (eval₁ a) (eval₁ c) = @HImp.himp H inst₂.toHImp (eval₂ a) (eval₂ c)
-- by IH: eval₁ a = eval₂ a, eval₁ c = eval₂ c
-- by h_himp: @HImp.himp inst₁ = @HImp.himp inst₂
-- combine with congr
```

This should work. The `simp` lemmas `AlgEvaluate_imp` etc. unfold using the *ambient* instance,
so we need to be careful with instance management. Using `@AlgEvaluate` explicitly and `simp only`
with the correct instance should handle this.

### 5.2 Alternative: Restricted Evaluators

An alternative approach (which may be simpler in practice) is to define fragment-specific
evaluators that only require the fragment's algebraic operations, then prove they agree with
`AlgEvaluate` on the fragment. For example:

```lean
def AlgEvaluateOrFree {H : Type*} [SemilatticeInf H] [OrderTop H] [HImp H]
    (v : Atom → H) (bot_val : H) : Proposition Atom → H
  | .atom x => v x
  | .bot => bot_val
  | .imp a b => AlgEvaluateOrFree v bot_val a ⇨ AlgEvaluateOrFree v bot_val b
  | .and a b => AlgEvaluateOrFree v bot_val a ⊓ AlgEvaluateOrFree v bot_val b
  | .or a b => ⊤  -- dummy, never reached for or-free formulas
```

This is problematic because: (a) it introduces new definitions that need maintenance, (b) the
dummy case (`⊤` for unreachable `.or`) is inelegant, and (c) it doesn't compose well with
existing infrastructure that uses `AlgEvaluate`.

**Recommendation**: Use the two-instance formulation. It's cleaner and directly usable by
downstream embedding lemmas.

## 6. File Organization

Target file: `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean`

### 6.1 Import Structure

```lean
import Cslib.Logics.Propositional.Semantics.Algebra.Conservative
```

This transitively imports:
- `Cslib.Logics.Propositional.Semantics.Algebra` (for `AlgEvaluate` and simp lemmas)
- `Cslib.Logics.Propositional.Defs` (for `Proposition`, `subst`)
- `Mathlib.Order.WithBot`
- `Mathlib.Order.Heyting.Basic`

We import `Conservative.lean` to have `IsBotFree` available for the `IsOrBotFree_iff` lemma.

### 6.2 Proposed Section Structure

1. **Predicate Definitions** (3 defs)
2. **Subsumption Hierarchy** (~4 lemmas)
3. **Connective Closure** (~5 lemmas)
4. **Substitution Closure** (3 theorems)
5. **Independence Lemmas** (3 theorems)

### 6.3 Barrel Import Update

After creating the file, run `lake exe mk_all --module` to update `Cslib.lean` to include
`Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates`.

## 7. Downstream Task Requirements

### Task 305: Fragment Hilbert Proof Systems
- Needs: `IsOrBotFree`, `IsImpTopOnly`, substitution closure for both
- The `ConjImpAxiom` constructors (K, S, andI, andE1, andE2) all produce or-bot-free formulas
- The `ImpAxiom` constructors (K, S only) all produce imp-top-only formulas
- Substitution closure is needed to prove `subst_preserves_conjImpAxiom` and
  `subst_preserves_impAxiom`

### Task 306: Brouwerian Soundness/Completeness
- Needs: `IsOrBotFree` to characterize the formulas in the conjunctive-implicational fragment
- The Lindenbaum construction quotients by `ConjImpAxiom`-derivability

### Task 307: Free Join Completion
- Needs: `IsOrBotFree` for the embedding lemma (or-bot-free formulas evaluate the same way
  in the original Brouwerian semilattice and its free join completion)
- This is the analog of `coe_AlgEvaluate` for the ∧→⊤ conservative extension

### Task 309: Hilbert Algebra Soundness/Completeness
- Needs: `IsImpTopOnly` to characterize implication-only formulas
- Lindenbaum construction quotients by `ImpAxiom`-derivability

## 8. Tactic Survey

For the independence lemmas, the proof structure is:
- `induction A with` to case-split
- `simp [Proposition.IsOrFree]` (or similar) to decompose the Boolean conjunction
- `simp only [AlgEvaluate_imp, ...]` with IH and instance-equality hypotheses

Key tactics:
- `induction`: Primary proof structure
- `simp`: Decompose `Bool.and_eq_true` hypotheses and unfold evaluator
- `congr`: Combine IH results with operation-equality hypotheses
- `rfl`: Handle atom cases
- `simp ... at hA`: Contradict false fragment membership in excluded cases

The proofs should be straightforward, ~10-15 lines each, closely following
`AlgEvaluate_botFree_independent`.

## 9. Risk Assessment

**Low risk**: All definitions and proofs follow established patterns. No new architectural
decisions needed.

**Potential issue**: The two-instance independence formulation requires `@`-notation to override
typeclass resolution. This can make proofs verbose. If the instance equality hypotheses are
awkward to state, an alternative is to prove independence for specific downstream constructions
(e.g., the `WithBot` embedding or the downset embedding) directly, without the general
two-instance form.

**Recommendation**: Start with the two-instance form. If it proves too awkward in practice,
the implementation agent can pivot to construction-specific embedding lemmas, which may be
more natural for the downstream tasks anyway.

**Alternative simpler formulation**: Rather than the fully general two-instance form, consider
the "parameter independence" style that parallels `AlgEvaluate_botFree_independent` more
closely. For `IsOrBotFree`, combine bot-independence and or-independence. This may be more
composable downstream.

## 10. Estimated Complexity

- **Definitions**: 3 simple recursive defs (~5 lines each)
- **Subsumption**: 4 simple lemmas (~5 lines each)
- **Connective closure**: 5 trivial lemmas (~3 lines each)
- **Substitution closure**: 3 inductive proofs (~10 lines each)
- **Independence lemmas**: 3 inductive proofs (~15 lines each)

**Total**: ~150-200 lines of Lean 4 code. Single-phase implementation.
