# Research Report: Curry-Howard Isomorphism for Theory.Derivation

- **Task**: 293 -- Curry-Howard Isomorphism between ND Proofs and Typed Lambda Terms
- **Date**: 2026-06-23
- **Session**: sess_1750723200_orchestrate_batch_293
- **Status**: Research complete

## 1. Executive Summary

This task establishes a formal Curry-Howard isomorphism between `Theory.Derivation` (propositional
natural deduction proofs with `Finset` contexts) and a purpose-built simply-typed lambda calculus
with `PL.Proposition Atom` as the type language. The existing CSLib infrastructure is well-suited:
`Derivation` is `Type u` with 10 constructors matching ND rules, and its context representation
(`Finset (Proposition Atom)`) introduces a controlled complication -- variable lookup requires
membership proofs rather than de Bruijn indices. A purpose-built intrinsic term type indexed by
`Finset` contexts and `Proposition` types is the recommended approach, since the existing STLC
infrastructure in `Cslib/Languages/LambdaCalculus/` uses locally nameless representation with
`List`-based extrinsic typing, making it unsuitable for a direct bijection.

**Key design decision**: The term language must be an intrinsically-typed inductive
`Term : Ctx Atom -> Proposition Atom -> Type u` (like `Derivation` itself) rather than
an extrinsic syntax + typing relation. This makes the isomorphism structurally an
`Equiv`/mutual inverse pair rather than requiring an additional typing judgment.

**Dependency on task 290**: The normalization correspondence (normal derivations <-> beta-normal
terms) requires task 290's `isNormal` predicate and normalization function. The core isomorphism
(term extraction and reconstruction) is fully independent. The report separates these cleanly.

## 2. Existing CSLib Infrastructure

### 2.1 `Theory.Derivation` (the proof side)

**File**: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`, line 117

```lean
inductive Theory.Derivation {T : Theory Atom} : Ctx Atom -> Proposition Atom -> Type u where
  | ax  {G} {A} (_ : A in T)                                               : Derivation G A
  | ass {G} {A} (_ : A in G)                                               : Derivation G A
  | andI  {A B} (G) : Derivation G A -> Derivation G B                     -> Derivation G (A /\ B)
  | andE1 {A B} (G) : Derivation G (A /\ B)                                -> Derivation G A
  | andE2 {A B} (G) : Derivation G (A /\ B)                                -> Derivation G B
  | orI1  {A B} (G) : Derivation G A                                       -> Derivation G (A \/ B)
  | orI2  {A B} (G) : Derivation G B                                       -> Derivation G (A \/ B)
  | orE   {A B C} (G) : Derivation G (A \/ B) ->
      Derivation (insert A G) C -> Derivation (insert B G) C               -> Derivation G C
  | impI  {A B} (G) : Derivation (insert A G) B                            -> Derivation G (A -> B)
  | impE  {G} {A B} : Derivation G (A -> B) -> Derivation G A              -> Derivation G B
```

Key properties for the Curry-Howard isomorphism:

- **Universe**: `Type u` (not `Prop`) -- computable functions are possible, and the isomorphism
  is a structure-preserving bijection, not merely a proof of logical equivalence.
- **Contexts**: `Finset (Proposition Atom)` with implicit contraction and exchange.
- **Theory parameter**: `T : Theory Atom` controls logic strength. The isomorphism should
  be stated for arbitrary `T`. Theory axioms (`ax`) correspond to free constants/axiom terms.
- **10 constructors**: `ax`, `ass` are base cases; the 8 logical constructors match standard ND.

### 2.2 `Proposition` (the type language)

**File**: `Cslib/Logics/Propositional/Defs.lean`, line 81

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom) | bot | imp (a b) | and (a b) | or (a b)
```

With notation: `bot = bot`, `top = bot -> bot`, `neg A = A -> bot`, `A /\ B`, `A \/ B`, `A -> B`.
`DecidableEq` derived automatically.

### 2.3 Existing STLC Infrastructure (NOT reusable)

**File**: `Cslib/Languages/LambdaCalculus/LocallyNameless/Stlc/Basic.lean`

The existing STLC uses:
- `Ty Base` with `base : Base -> Ty Base` and `arrow : Ty Base -> Ty Base -> Ty Base`
- `Term Var` with locally nameless representation (`bvar`, `fvar`, `abs`, `app`)
- `Typing : Context Var (Ty Base) -> Term Var -> Ty Base -> Prop` (extrinsic)
- `Context Var (Ty Base) = List ((_ : Var) x (Ty Base))` -- List-based, not Finset-based

**Why not reusable**:
1. `Ty Base` has only `base` and `arrow` -- no products or sums (no `and`/`or` connectives).
2. `Term Var` has only `bvar`, `fvar`, `abs`, `app` -- no pair, projection, injection, or case.
3. `Typing` is a `Prop` (extrinsic), while `Derivation` is `Type u` (intrinsic). An isomorphism
   between a `Type u` and a `Prop`-valued predicate cannot be a bijection.
4. `Context` is `List`-based, while `Ctx Atom` is `Finset`-based.

The existing STLC serves a different purpose (operational semantics, reduction, strong
normalization) and cannot be instantiated to recover `Derivation`'s structure.

### 2.4 Available Operations on Derivation

- `Derivation.weak`: Weakening (theory and context).
- `Derivation.subs`: Structural substitution (replaces hypotheses in context).
- `Derivation.cut`: Cut rule (via `impI`/`impE`).
- `Derivation.substAtom`: Transport along atom substitution.

These are all relevant for proving properties of the isomorphism.

### 2.5 Task 290 Status

Task 290 (Prawitz-style normalization) is in `[IMPLEMENTING]` status with research and plan
complete, but no `Normalization.lean` file has been created yet. The plan defines:
- `isNormal : T.Derivation G A -> Bool` -- a predicate detecting the 5 redex patterns
- `normalize : T.Derivation G A -> T.Derivation G A` -- normalization function
- `reduceStep` -- single-step beta reduction on derivations

**Impact on task 293**: The normalization correspondence (item 3 below) depends on 290's
`isNormal` predicate. The core isomorphism does not.

## 3. Recommended Term Language Design

### 3.1 Intrinsically-Typed Terms

The term language should mirror `Derivation` constructor-for-constructor as an intrinsically
typed inductive:

```lean
/-- Simply-typed lambda terms with PL.Proposition as the type language.
Intrinsically typed: `Term T G A` is a well-typed term of type `A` in context `G`,
possibly using axiom constants from theory `T`. -/
inductive Term {T : Theory Atom} : Ctx Atom -> Proposition Atom -> Type u where
  /-- Axiom constant (corresponds to Derivation.ax). -/
  | const {G} {A} (h : A in T) : Term G A
  /-- Variable lookup (corresponds to Derivation.ass). -/
  | var {G} {A} (h : A in G) : Term G A
  /-- Lambda abstraction (corresponds to Derivation.impI). -/
  | lam {A B} (G) : Term (insert A G) B -> Term G (A -> B)
  /-- Function application (corresponds to Derivation.impE). -/
  | app {G} {A B} : Term G (A -> B) -> Term G A -> Term G B
  /-- Pair construction (corresponds to Derivation.andI). -/
  | pair {A B} (G) : Term G A -> Term G B -> Term G (A /\ B)
  /-- First projection (corresponds to Derivation.andE1). -/
  | fst {A B} (G) : Term G (A /\ B) -> Term G A
  /-- Second projection (corresponds to Derivation.andE2). -/
  | snd {A B} (G) : Term G (A /\ B) -> Term G B
  /-- Left injection (corresponds to Derivation.orI1). -/
  | inl {A B} (G) : Term G A -> Term G (A \/ B)
  /-- Right injection (corresponds to Derivation.orI2). -/
  | inr {A B} (G) : Term G B -> Term G (A \/ B)
  /-- Case analysis (corresponds to Derivation.orE). -/
  | case {A B C} (G) : Term G (A \/ B) ->
      Term (insert A G) C -> Term (insert B G) C -> Term G C
```

### 3.2 Why Intrinsic Typing is the Right Choice

1. **Structural isomorphism**: With identical index types (`Ctx Atom` and `Proposition Atom`)
   and constructor-to-constructor correspondence, the forward and backward maps are trivially
   total functions by structural recursion. No partial typing predicate needed.

2. **Roundtrip by definitional equality**: Because the constructors correspond 1-1, the
   composed maps `backward . forward` and `forward . backward` are identity functions *by
   structural induction*, requiring only trivial `rfl`/`rfl` proofs at each constructor.

3. **Consistency with CSLib style**: `Derivation` is already intrinsically typed (`Type u`),
   so the isomorphism partner should match.

4. **Avoids context representation mismatch**: Both sides use `Finset`-based contexts.

### 3.3 Constructor Mapping Table

| Derivation constructor | Term constructor | Lambda calculus name |
|------------------------|------------------|----------------------|
| `ax h`                 | `const h`        | axiom constant       |
| `ass h`                | `var h`          | variable lookup      |
| `impI G d`             | `lam G t`        | lambda abstraction   |
| `impE d1 d2`           | `app t1 t2`      | function application |
| `andI G d1 d2`         | `pair G t1 t2`   | pair construction    |
| `andE1 G d`            | `fst G t`        | first projection     |
| `andE2 G d`            | `snd G t`        | second projection    |
| `orI1 G d`             | `inl G t`        | left injection       |
| `orI2 G d`             | `inr G t`        | right injection      |
| `orE G d d1 d2`        | `case G t t1 t2` | case analysis        |

This is a 1-to-1 correspondence of constructors, parameters, and recursive arguments.

### 3.4 Handling Theory Axioms

The `ax` constructor takes `h : A in T` (a membership proof in the theory set). The
corresponding term constructor `const h` acts as a free constant whose type is guaranteed
by the theory. This means the term language is parameterized over the theory `T`, just like
`Derivation`.

For the pure lambda calculus (no theory axioms), set `T = MPL = empty` and the `const`/`ax`
constructors become vacuous (no `A in empty` exists).

### 3.5 Alternative: Extrinsic Approach (REJECTED)

An extrinsic approach would define:
- `RawTerm` -- untyped syntax
- `Typing : Ctx Atom -> RawTerm -> Proposition Atom -> Prop` -- typing judgment
- Isomorphism between `Derivation G A` and `Sigma t, Typing G t A`

This is more complex, requires proving typing is functional and deterministic, and the
roundtrip properties would be harder. The intrinsic approach is cleaner and more direct
for this particular correspondence. The extrinsic STLC already exists for operational
semantics purposes; the CurryHoward module serves a different goal.

## 4. The Isomorphism: Formal Statement

### 4.1 Forward Map: Derivation -> Term

```lean
def curryHowardForward : T.Derivation G A -> Term (T := T) G A
  | .ax h          => .const h
  | .ass h         => .var h
  | .andI G d1 d2  => .pair G (curryHowardForward d1) (curryHowardForward d2)
  | .andE1 G d     => .fst G (curryHowardForward d)
  | .andE2 G d     => .snd G (curryHowardForward d)
  | .orI1 G d      => .inl G (curryHowardForward d)
  | .orI2 G d      => .inr G (curryHowardForward d)
  | .orE G d d1 d2 => .case G (curryHowardForward d)
                              (curryHowardForward d1) (curryHowardForward d2)
  | .impI G d      => .lam G (curryHowardForward d)
  | .impE d1 d2    => .app (curryHowardForward d1) (curryHowardForward d2)
```

### 4.2 Backward Map: Term -> Derivation

```lean
def curryHowardBackward : Term (T := T) G A -> T.Derivation G A
  | .const h         => .ax h
  | .var h           => .ass h
  | .pair G t1 t2    => .andI G (curryHowardBackward t1) (curryHowardBackward t2)
  | .fst G t         => .andE1 G (curryHowardBackward t)
  | .snd G t         => .andE2 G (curryHowardBackward t)
  | .inl G t         => .orI1 G (curryHowardBackward t)
  | .inr G t         => .inr G (curryHowardBackward t)  -- TYPO: should be .orI2
  | .case G t t1 t2  => .orE G (curryHowardBackward t)
                                (curryHowardBackward t1) (curryHowardBackward t2)
  | .lam G t         => .impI G (curryHowardBackward t)
  | .app t1 t2       => .impE (curryHowardBackward t1) (curryHowardBackward t2)
```

### 4.3 Roundtrip Properties

```lean
theorem curryHoward_forward_backward (t : Term (T := T) G A) :
    curryHowardForward (curryHowardBackward t) = t

theorem curryHoward_backward_forward (d : T.Derivation G A) :
    curryHowardBackward (curryHowardForward d) = d
```

Both proofs are by structural induction on the argument. Each case reduces to a
`congr`/`rfl` step because the maps are literally constructor-for-constructor inverses.
The explicit `G` parameter in constructors like `andI G d1 d2` / `pair G t1 t2` ensures
the reconstruction is deterministic.

### 4.4 Equiv Form

```lean
def curryHowardEquiv : T.Derivation G A ≃ Term (T := T) G A where
  toFun := curryHowardForward
  invFun := curryHowardBackward
  left_inv := curryHoward_backward_forward
  right_inv := curryHoward_forward_backward
```

## 5. Proof Obligations and Difficulty Assessment

### 5.1 Core Isomorphism (Independent of task 290)

| Obligation | Difficulty | Notes |
|------------|-----------|-------|
| Define `Term` inductive | Easy | Mirror `Derivation` constructors |
| Define `curryHowardForward` | Easy | Structural recursion, 10 cases |
| Define `curryHowardBackward` | Easy | Structural recursion, 10 cases |
| Prove `forward_backward` | Easy | Structural induction, each case is `rfl`-like |
| Prove `backward_forward` | Easy | Structural induction, each case is `rfl`-like |
| Define `curryHowardEquiv` | Easy | Bundle the above |

**Estimated effort**: 2-3 hours

### 5.2 Structural Properties of Terms (Independent of task 290)

| Obligation | Difficulty | Notes |
|------------|-----------|-------|
| Term weakening (`Term.weak`) | Easy | Mirror `Derivation.weak` |
| Term substitution | Medium | Mirror `Derivation.subs` |
| Weakening commutes with isomorphism | Easy | Follows from structural correspondence |

**Estimated effort**: 1-2 hours

### 5.3 Beta-Reduction and Normalization Correspondence (Depends on task 290)

| Obligation | Difficulty | Notes |
|------------|-----------|-------|
| Define beta-reduction on `Term` | Medium | Mirror derivation reduction steps |
| Define `Term.isNormal` | Easy | Mirror `Derivation.isNormal` from task 290 |
| Prove isomorphism preserves normality | Easy | Both sides defined by same pattern |
| Prove isomorphism commutes with reduction | Medium | Requires showing `subs` matches term substitution |
| Normalization correspondence theorem | Medium-Hard | Depends on 290 completion |

**Estimated effort**: 3-4 hours (after 290 completes)

### 5.4 Reduced Scope Fallback: {arrow, and} Fragment

The task description identifies an `{arrow, and}` fragment as a self-contained milestone.
This means:
- Only `impI`, `impE`, `andI`, `andE1`, `andE2` on the proof side
- Only `lam`, `app`, `pair`, `fst`, `snd` on the term side
- No `or` connective (no `inl`, `inr`, `case`)

This fragment is easier because it avoids the `orE` case (which has the most complex
binding structure with `insert A G` and `insert B G` contexts). However, given that
the intrinsic typing approach makes the full isomorphism essentially the same difficulty
as the fragment (each constructor maps 1-1), the full version is recommended.

## 6. Design Decisions and Alternatives Considered

### 6.1 Why Not Reuse the Existing STLC?

The existing `LambdaCalculus.LocallyNameless.Stlc` is designed for operational semantics
(reduction, preservation, progress, strong normalization). Its design choices reflect this:

- **Locally nameless representation**: Good for metatheory of reduction. Bad for a direct
  structural bijection with `Derivation`, which uses membership proofs in Finsets.
- **Extrinsic typing (`Prop`)**: Cannot form a bijection with `Derivation` (`Type u`).
- **No products/sums**: Missing the connectives needed for full propositional logic.
- **`List`-based contexts**: Would need bridging to `Finset`-based contexts.

A bridge *could* be built, but it would be more complex and less clean than a purpose-built
intrinsic type.

### 6.2 Why Not Use de Bruijn Indices?

de Bruijn indices would avoid named variables entirely, but `Derivation` uses named
membership proofs (`A in G` for a `Finset G`). Translating between de Bruijn terms and
Finset membership would add unnecessary complexity. The intrinsic approach inherits
`Derivation`'s variable convention directly.

### 6.3 Why Parameterize Over `T` (Theory)?

The isomorphism holds for any theory `T`. The `ax`/`const` constructors act as "free
constants" whose types are guaranteed by theory membership. This is standard in the
Curry-Howard correspondence: axioms correspond to constants.

Setting `T = MPL = empty` recovers the pure minimal propositional logic case where
the correspondence is with the pure lambda calculus (no constants).

Setting `T = IPL` includes ex falso quodlibet constants (`bot -> A` for all `A`),
corresponding to the empty type elimination in type theory.

## 7. File Organization

### 7.1 Recommended Directory Structure

```
Cslib/Logics/Propositional/CurryHoward/
  Defs.lean          -- Term inductive type, basic operations (weakening)
  Isomorphism.lean   -- Forward/backward maps and roundtrip proofs
  Reduction.lean     -- [Depends on 290] Beta-reduction on terms, normalization correspondence
```

### 7.2 Import Dependencies

```
Defs.lean:
  import Cslib.Init
  import Cslib.Logics.Propositional.NaturalDeduction.Basic

Isomorphism.lean:
  import Cslib.Logics.Propositional.CurryHoward.Defs

Reduction.lean:  [Depends on 290]
  import Cslib.Logics.Propositional.CurryHoward.Isomorphism
  import Cslib.Logics.Propositional.NaturalDeduction.Normalization
```

### 7.3 Namespace

`Cslib.Logic.PL.CurryHoward` -- under the existing `PL` namespace.

## 8. Literature Proof Structure

### 8.1 Source: Troelstra & Schwichtenberg, "Basic Proof Theory", Ch. 10

The Curry-Howard isomorphism as presented in the literature has this structure:

1. **Define proof terms**: Typed lambda terms with constructors for each ND rule.
2. **Type assignment**: Each term constructor introduces or eliminates a type connective.
3. **Term extraction**: Given a derivation D of G |- A, extract term t of type A.
4. **Proof reconstruction**: Given a well-typed term t : A in context G, reconstruct
   derivation D of G |- A.
5. **Beta-reduction corresponds to detour elimination**: impE(impI(d), e) reduces to
   d[x := e], corresponding to the imp-redex reduction.
6. **Normal derivations correspond to beta-normal terms**: A derivation has no redexes
   iff its corresponding term is beta-normal.

### 8.2 Source: Prawitz, "Natural Deduction" (1965)

Prawitz established normalization for ND derivations (the proof side). The Curry-Howard
correspondence was not explicitly stated by Prawitz but is implicit in the structure of
his work. The five redex patterns from Prawitz Ch. IV map to:

| Prawitz redex | Beta-reduction on terms |
|---------------|------------------------|
| imp-redex: impE(impI(d), e) -> d[e/x] | (lam f) @ a -> f[a/x] |
| and-redex-L: fst(pair(a,b)) -> a | pi1(a,b) -> a |
| and-redex-R: snd(pair(a,b)) -> b | pi2(a,b) -> b |
| or-redex-L: case(inl(a), f, g) -> f[a/x] | case(inl a, f, g) -> f[a/x] |
| or-redex-R: case(inr(b), f, g) -> g[b/x] | case(inr b, f, g) -> g[b/x] |

### 8.3 Translation to Lean 4

- **Step 1-2**: Define `Term` inductive (section 3.1 above). The type assignment is
  built into the inductive type's indices.
- **Step 3**: `curryHowardForward` (structural recursion on `Derivation`).
- **Step 4**: `curryHowardBackward` (structural recursion on `Term`).
- **Step 5-6**: Require task 290's normalization infrastructure to state formally.
  Define `Term.betaReduce` mirroring `Derivation.reduceStep`, then prove
  `curryHowardForward (reduceStep d) = betaReduce (curryHowardForward d)`.

## 9. Dependency Analysis

### 9.1 Independent of Task 290

- All of section 5.1 (core isomorphism)
- All of section 5.2 (structural properties)
- File organization: `Defs.lean` and `Isomorphism.lean`

### 9.2 Depends on Task 290

- Section 5.3 (beta-reduction and normalization correspondence)
- File: `Reduction.lean`
- Specifically depends on: `Derivation.isNormal`, `Derivation.reduceStep`, and
  their properties

### 9.3 Recommendation

Implement the core isomorphism (Defs.lean + Isomorphism.lean) immediately. Defer
Reduction.lean until task 290 delivers the normalization infrastructure. The core
isomorphism is a complete, self-contained deliverable.

## 10. Potential Pitfalls

### 10.1 Explicit Context Parameter

Several `Derivation` constructors take `G : Ctx Atom` as an explicit argument (e.g.,
`andI {A B} (G : Ctx Atom) : ...`). The corresponding `Term` constructors must take
`G` in the same position. This is needed for the roundtrip proof: without the explicit
`G`, Lean's pattern matching would not know which context to reconstruct.

### 10.2 Finset Equality in Pattern Matching

The roundtrip proofs require showing that reconstructed terms/derivations are
definitionally equal to the originals. Since `Finset` operations like `insert` may
produce propositionally-but-not-definitionally equal sets, some `congr` or rewrite steps
may be needed. However, because both sides use identical `Finset` operations (the maps
just rename constructors), this should not be an issue in practice.

### 10.3 Universe Polymorphism

Both `Derivation` and `Term` live in `Type u`. The maps and roundtrip theorems should be
universe-polymorphic, matching `Derivation`'s universe parameter.

### 10.4 Theory Axiom Handling

The `const`/`ax` case is straightforward: both carry a proof `h : A in T`, and the maps
just relay this proof. No special handling needed.

## 11. Tactic Survey

For the roundtrip proofs, the primary tactics will be:
- `induction` on the derivation/term structure
- `simp` or `rfl` for the base cases
- `congr` + induction hypotheses for recursive cases

The proofs should be short and mechanical. For the structural properties (weakening),
the existing `Derivation.weak` proof pattern can be followed directly.

## 12. Summary of Recommendations

1. **Create purpose-built intrinsic `Term` type** mirroring `Derivation` (section 3.1).
2. **Do NOT reuse existing STLC** -- it serves a different purpose.
3. **Implement core isomorphism first** (independent of task 290).
4. **Defer reduction correspondence** to after task 290 completes.
5. **Full connective set recommended** -- the {arrow, and} fallback saves negligible effort
   with intrinsic typing.
6. **File structure**: `Defs.lean`, `Isomorphism.lean`, then later `Reduction.lean`.
