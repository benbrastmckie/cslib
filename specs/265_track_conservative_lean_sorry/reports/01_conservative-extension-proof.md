# Research Report: Conservative Extension of IPL over MPL for Bot-Free Formulas

**Task**: 265 -- track_conservative_lean_sorry
**Session**: sess_1782155556_ff49bc
**Date**: 2026-06-22

## 1. Literature Survey

### 1.1 Johansson 1937 (Primary Source)

The conservative extension result originates with Johansson's foundational paper
*Der Minimalkalkul, ein reduzierter intuitionistischer Formalismus* (1937). In Section 2,
Johansson states:

> Im Minimalkalkul sind diejenigen Satze, die nur Implication, Konjunktion, Disjunktion
> und Aussagenvariable enthalten, genau dieselben wie in der angegebenen Arbeit von Heyting.

Translation: "In the minimal calculus, those sentences that contain only implication,
conjunction, disjunction, and propositional variables are exactly the same as in Heyting's
[intuitionistic] system."

Johansson's argument is essentially syntactic: Heyting's Sections 2 and 3 (which develop
the connectives without using the ex-falso axiom 4.1) transfer unchanged to the minimal
calculus. The only differences arise in Section 4 (which concerns bot and negation).

### 1.2 Rasiowa 1974 (Algebraic Approach)

Rasiowa's *An Algebraic Approach to Non-Classical Logics* develops the algebraic semantics
systematically. The three-tier hierarchy of algebras:
- Generalized Heyting Algebra (GHA) = Johansson algebra = semantics for MPL
- Heyting Algebra (HA) = GHA + bottom = semantics for IPL
- Boolean Algebra (BA) = HA + excluded middle = semantics for CPL

The conservative extension follows from algebraic completeness at each tier plus the
observation that bot-free evaluation is independent of the bottom element. This is the
approach the CSLib codebase already follows.

### 1.3 Troelstra & van Dalen 1988

*Constructivism in Mathematics* discusses the relationship between minimal and
intuitionistic logic. The conservativity result is standard but typically handled via
proof-theoretic methods (normalization, subformula property).

### 1.4 No Existing Formalizations Found

No Lean 4 formalization of this specific result was found in Mathlib or in the
FormalizedFormalLogic project. The result is standard but has not been formalized before
in Lean 4 to our knowledge.

## 2. The Proof Gap: Analysis

### 2.1 What We Have

The CSLib codebase has an excellent algebraic infrastructure:

| Result | Location | Status |
|--------|----------|--------|
| `AlgEvaluate` (generic evaluator over GHA) | `Algebra.lean` | Done |
| `AlgEvaluate_botFree_independent` | `Conservative.lean:48` | Done |
| `MPL.alg_complete` (GHA completeness) | `Completeness.lean:237` | Done |
| `IPL.alg_complete` (HA completeness) | `Completeness.lean:252` | Done |
| `GHAValid_implies_HAValid` | `Conservative.lean:69` | Done |
| `LindenbaumAlgebra` as GHA/HA/BA | `Lindenbaum.lean` | Done |

### 2.2 The Gap

The proof requires going from HA-validity to GHA-validity for bot-free formulas:

```
IPL.alg_complete.mp h  :  forall HA H, forall v, AlgEvaluate v bot A = top
  ---> need: forall GHA G, forall v bot_val, AlgEvaluate v bot_val A = top
MPL.alg_complete.mpr   :  ... -> DerivableIn MPL A
```

Given an arbitrary GHA G, we need to construct an HA in which bot-free evaluation
matches. The problem: G has no designated bottom element, so we cannot directly
instantiate IPL.alg_complete.

### 2.3 Why the Blocker Message Was Partially Correct

The task description mentioned "Dedekind-MacNeille completion" as a possible approach.
This is one valid algebraic completion method, but it is severe overkill for this problem.
A much simpler construction suffices: `WithBot G`.

## 3. Proof Strategy: WithBot Embedding

### 3.1 Core Idea

Given any `GeneralizedHeytingAlgebra G`, construct `HeytingAlgebra (WithBot G)` by
adjoining a fresh bottom element. The embedding `(coe) : G -> WithBot G` preserves
all lattice operations and Heyting implication. For bot-free formulas, evaluation
in `WithBot G` via the lifted valuation equals the lift of evaluation in `G`.

### 3.2 Detailed Proof Outline

**Step 1**: Construct `HeytingAlgebra (WithBot G)` for any GHA `G`.

Define the Heyting implication on `WithBot G`:
```
bot  => y     = top                (bot implies anything)
coe a => bot  = bot                (non-bot implies bot = bot)
coe a => coe b = coe (a => b)     (lift from G)
```

The adjunction `a <= (b => c) iff a inf b <= c` holds by case analysis:
- Both bot: trivial
- `a = coe a', b = bot`: both sides reduce to `a' <= top` and `bot <= c`
- `a = coe a', b = coe b', c = bot`: both sides are false (coe not <= bot)
- `a = coe a', b = coe b', c = coe c'`: reduces to `le_himp_iff` in `G`

**Verified**: This instance compiles in Lean 4 using `HeytingAlgebra.ofHImp`. The
prerequisites `DistribLattice (WithBot G)`, `BoundedOrder (WithBot G)` are all provided
by Mathlib (`WithBot.distribLattice`, `WithBot.instOrderBot`, `WithBot.instOrderTop`).

**Step 2**: Prove the embedding lemma.

```lean
theorem coe_AlgEvaluate (v : Atom -> G) (bot_val : G) (A : Proposition Atom)
    (hBF : A.IsBotFree = true) :
    AlgEvaluate (fun x => (v x : WithBot G)) (bot : WithBot G) A =
      ((AlgEvaluate v bot_val A : G) : WithBot G)
```

By induction on `A` (which is bot-free):
- `atom x`: both sides are `coe (v x)` -- by `rfl`
- `bot`: impossible since `A` is bot-free
- `imp a b`: LHS = `(coe (eval a)) => (coe (eval b))` in WithBot G
  = `coe (eval a => eval b)` by definition of `withBotHimp`
  = `coe (AlgEvaluate v bot_val (imp a b))` -- by RHS definition
- `and a b`: uses `WithBot.coe_inf`
- `or a b`: uses `WithBot.coe_sup`

**Verified**: This lemma compiles in a standalone test.

**Step 3**: The main theorem.

```lean
theorem ipl_conservative_over_mpl {A : Proposition Atom}
    (hBF : A.IsBotFree = true) (h : DerivableIn IPL A) :
    DerivableIn MPL A := by
  rw [MPL.alg_complete]
  intro G _ v bot_val
  -- Lift to WithBot G (which is an HA)
  have hIPL := IPL.alg_complete.mp h (H := WithBot G) (fun x => (v x : WithBot G))
  -- hIPL : AlgEvaluate (coe . v) bot A = top  (in WithBot G)
  -- By embedding lemma: this equals coe (AlgEvaluate v bot_val A)
  rw [coe_AlgEvaluate v bot_val A hBF] at hIPL
  -- hIPL : coe (AlgEvaluate v bot_val A) = top
  -- Since top in WithBot G = coe (top in G), and coe is injective:
  exact WithBot.coe_eq_coe.mp hIPL
```

### 3.3 Universe Level Analysis

Both `MPL.alg_complete` and `IPL.alg_complete` quantify over `H : Type u` where
`Atom : Type u`. Since `WithBot G : Type u` when `G : Type u` (WithBot = Option,
which preserves universe level), universe levels match perfectly.

## 4. Mathlib API Availability

### 4.1 Available (No New Code Needed)

| API | Module | Usage |
|-----|--------|-------|
| `WithBot.distribLattice` | `Mathlib.Order.WithBot` | DistribLattice on WithBot G |
| `WithBot.instOrderBot` | `Mathlib.Order.WithBot` | Bottom element for WithBot G |
| `WithBot.instOrderTop` | `Mathlib.Order.WithBot` | Top element for WithBot G |
| `WithBot.coe_inf` | `Mathlib.Order.WithBot` | Coe preserves inf |
| `WithBot.coe_sup` | `Mathlib.Order.WithBot` | Coe preserves sup |
| `WithBot.coe_eq_coe` | `Mathlib.Order.WithBot` | Coe injectivity |
| `HeytingAlgebra.ofHImp` | `Mathlib.Order.Heyting.Basic` | Build HA from himp + adjunction |
| `WithBot.not_coe_le_bot` | `Mathlib.Order.WithBot` | coe a is not <= bot |
| `le_himp_iff` | `Mathlib.Order.Heyting.Basic` | GHA adjunction |

### 4.2 Missing (Must Be Built)

| Item | Complexity | Lines (est.) |
|------|-----------|--------------|
| `withBotHimp` definition | Simple | 4 |
| `HeytingAlgebra (WithBot G)` instance | Medium | 20-25 |
| `coe_AlgEvaluate` embedding lemma | Simple | 15 |
| Main theorem proof | Simple | 10 |

**Total new code**: approximately 50-60 lines.

### 4.3 Why HeytingAlgebra (WithBot G) Is Not in Mathlib

Mathlib does not provide a `HeytingAlgebra (WithBot alpha)` instance for
`[GeneralizedHeytingAlgebra alpha]`. This is likely because the construction is
somewhat niche: the standard use case for `WithBot` is adjoining a bottom to a
lattice/semilattice, not specifically for Heyting algebra extension. The Heyting
implication on `WithBot G` requires a custom definition (not just lifting from `G`)
because the `bot => _` case introduces new behavior (`bot => y = top`).

This instance could potentially be contributed to Mathlib separately, but for CSLib
it suffices to define it locally in `Conservative.lean`.

## 5. Alternative Approaches Considered

### 5.1 Syntactic Proof Transformation (Approach B)

**Idea**: Given an IPL derivation of a bot-free formula, transform it syntactically to
remove all uses of `botE` / ex-falso.

**Assessment**: This would require induction on `Theory.Derivation`, which has 10
constructors. The key insight is that `botE` (derived from `impE` + `ax (efq A)`) can
only produce a formula `A` from `bot`. If `A` is bot-free and the derivation is in
normal form, `botE` should be eliminable. However:

- The ND system does not have a normalization/cut-elimination theorem formalized.
- Induction on the derivation tree with weakening and cut makes the syntactic argument
  more complex than the algebraic one.
- The algebraic infrastructure is already in place.

**Verdict**: Feasible but significantly more work (100+ lines) and less elegant.

### 5.2 Kripke Semantics Route (Approach C)

**Idea**: Route through the KripkeBridge to use Kripke frame validity.

**Assessment**: `KripkeBridge.lean` shows that upset algebras of Kripke frames form
HeytingAlgebras. However, the completeness theorems are stated in terms of algebraic
validity, not Kripke validity. Going Kripke would require Kripke completeness for both
MPL and IPL, which is not yet formalized. The algebraic route is more direct.

**Verdict**: Not feasible without significant additional infrastructure.

### 5.3 Dedekind-MacNeille Completion (Approach D)

**Idea**: Embed any GHA into an HA via Dedekind-MacNeille completion.

**Assessment**: This is the original blocker message. Dedekind-MacNeille completion
preserves meets and joins but does NOT generally preserve Heyting implication (it
preserves it only for completely distributive lattices). Moreover, Mathlib does not
have a Dedekind-MacNeille construction. This approach is both incorrect in general
and unavailable in Mathlib.

**Verdict**: Incorrect and infeasible. The `WithBot` approach is strictly better.

## 6. Recommended Approach

**Use the WithBot embedding (Approach A)**. This is:
- Algebraically clean and follows the existing codebase conventions
- Requires approximately 50-60 lines of new code
- All Mathlib prerequisites are available
- Has been verified to compile in standalone tests
- Zero sorry risk (all steps are straightforward)

### 6.1 Implementation Plan

**Phase 1**: Define `withBotHimp` and prove the `HeytingAlgebra (WithBot G)` instance.
Place in `Conservative.lean` between the `AlgEvaluate_botFree_independent` theorem
and the `ipl_conservative_over_mpl` statement.

**Phase 2**: Prove the `coe_AlgEvaluate` embedding lemma. This is a direct structural
induction mirroring `AlgEvaluate_botFree_independent`.

**Phase 3**: Fill the `sorry` in `ipl_conservative_over_mpl` using `MPL.alg_complete`,
`IPL.alg_complete`, the embedding lemma, and `WithBot.coe_eq_coe`.

**Import requirements**: `Mathlib.Order.WithBot` may need to be added to
`Conservative.lean`'s imports (it is already transitively available via
`Mathlib.Order.Heyting.Regular` imported by `Lindenbaum.lean`, but an explicit import
may be cleaner).

### 6.2 Proof Sketch (Lean 4)

```lean
/-- Heyting implication on `WithBot G` for a GHA `G`. -/
noncomputable def withBotHimp {G : Type*} [GeneralizedHeytingAlgebra G] :
    WithBot G -> WithBot G -> WithBot G
  | bot, _ => top
  | (a : G), bot => bot
  | (a : G), (b : G) => ((a => b : G) : WithBot G)

/-- Every GHA can be extended to an HA by adjoining a bottom element. -/
noncomputable instance {G : Type*} [GeneralizedHeytingAlgebra G] :
    HeytingAlgebra (WithBot G) :=
  HeytingAlgebra.ofHImp withBotHimp (by
    intro a b c
    cases a with
    | bot => constructor <;> intro _ <;> exact bot_le
    | coe a' =>
      cases b with
      | bot => constructor; intro _; exact bot_le; intro _; exact le_top
      | coe b' =>
        cases c with
        | bot =>
          constructor
          · intro h; exact absurd h (WithBot.not_coe_le_bot _)
          · intro h; simp only [<- WithBot.coe_inf] at h
            exact absurd h (WithBot.not_coe_le_bot _)
        | coe c' =>
          simp only [withBotHimp, WithBot.coe_le_coe, <- WithBot.coe_inf]
          exact le_himp_iff)

/-- For bot-free formulas, evaluation in WithBot G via coe equals coe of evaluation in G. -/
theorem coe_AlgEvaluate ... := by induction A ...

/-- IPL is conservative over MPL for bot-free formulas. -/
theorem ipl_conservative_over_mpl ... := by
  rw [MPL.alg_complete]
  intro G _ v bot_val
  have := IPL.alg_complete.mp h (H := WithBot G) (fun x => (v x : WithBot G))
  rw [coe_AlgEvaluate v bot_val A hBF] at this
  exact WithBot.coe_eq_coe.mp this
```

## 7. Estimated Complexity

| Item | Difficulty | Lines | Risk |
|------|-----------|-------|------|
| `withBotHimp` definition | Trivial | 4 | None |
| `HeytingAlgebra (WithBot G)` | Low-Medium | 20-25 | Low (verified) |
| `coe_AlgEvaluate` lemma | Low | 12-15 | None (verified) |
| Main theorem | Low | 8-10 | None |
| Docstrings + cleanup | Low | 10-15 | None |
| **Total** | **Low** | **55-70** | **Very Low** |

The approach has been fully verified in standalone Lean 4 snippets. The only remaining
work is adapting to the actual CSLib definitions (which use `@[expose] public section`,
specific naming conventions, etc.) and ensuring the linter is satisfied.

## 8. Tactic Survey Results

The proof primarily uses:
- `cases` / `constructor` for the case analysis in the HA instance
- `simp only` with `WithBot.coe_le_coe`, `WithBot.coe_inf`, `WithBot.coe_sup`
- `le_himp_iff` for the GHA adjunction
- `rw` for the embedding lemma application
- `induction` for the structural induction on bot-free formulas
- `exact` / `absurd` for contradictions in the bot cases

No `omega`, `aesop`, `decide`, or `norm_num` are needed. The proof is entirely
order-theoretic and structural.
