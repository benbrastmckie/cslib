# Teammate C (Critic) Findings: Zulip Thread Verification
## Task 267 — Verify Claims in CSLib Propositional Logic Thread

**Thread**: https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/605813681
**Messages fetched**: 25 (2026-06-12 to 2026-06-22)
**Participants**: Benjamin Brast-McKie, Thomas Waring, Matthew Doty, Ching-Tsun Chou (referenced)

---

## Key Findings

### 1. Claims About Thomas's "Branch" Are Unverifiable Against Current Main

Thomas Waring (messages 18, 20, 23) makes multiple claims referencing code in an external
branch, not in CSLib main. Specifically:
- His `Theory.complete` theorem signature (msg 18)
- His `AlgEvaluate` definition with `Valuation Atom H` type alias (msg 18)
- His `IProposition` / `IDerivation` split design (msg 23)
- His `propEquiv`, `toDerivation`, `toIDerivation` compilation claims (msg 23)

**Risk**: A reader treating these as claims about what is currently in CSLib would be
misled. Thomas is describing his own experimental branch. The actual CSLib code uses
`Theory.alg_complete` (not `Theory.complete`), `AlgEvaluate` with explicit
`(v : Atom → H) (bot_val : H)` parameters (not a bundled `Valuation Atom H` type alias),
and there is no `IProposition` / `IDerivation` in the current codebase.

**Confidence**: High — confirmed by searching the entire Cslib/ tree.

### 2. Thomas's Theorem Signature Differs From Actual Code

Thomas (msg 18) states the completeness theorem as:
```
theorem Theory.complete [Inhabited Atom] {A : Proposition Atom} :
  DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] {v : Valuation Atom H}, (v ⊨ T) → v ⊨ A
```

The actual theorem in `Semantics/Algebra/Completeness.lean` is:
```lean
theorem Theory.alg_complete {A : Proposition Atom} :
    DerivableIn T A ↔
      ∀ {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
        AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤
```

Differences: (a) name is `alg_complete` not `complete`; (b) requires `[DecidableEq Atom]`
(from section variable) not `[Inhabited Atom]`; (c) `v : Atom → H` is explicit not bundled;
(d) `bot_val : H` is an explicit parameter; (e) uses `AlgTValid` predicate, not `v ⊨ T`
notation; (f) conclusion is `AlgEvaluate v bot_val A = ⊤`, not `v ⊨ A`.

**Risk**: Thomas is describing his own branch design. The `v ⊨ T` notation is mentioned in
message 25 as having been "adopted" via `AlgTValid`, but the surface syntax differs. A
reader looking for `Theory.complete` with `[Inhabited Atom]` will not find it.

**Confidence**: High — directly confirmed by reading the file.

### 3. Benjamin's Claim of "Convergence" on ⊥-as-Primitive Is Overstated

Benjamin (msg 25) says "I think the thread has substantially converged on this." But:
- Thomas (msg 23, 2026-06-21) explicitly argues for a different design where IPL has ⊥ as
  primitive and MPL is encoded into it
- Matthew (msg 21, 2026-06-17) says "I am still a proponent of an explicit falsum in the
  base syntax"
- The thread ends with Benjamin's position (msg 25, 2026-06-22) — which is the most recent
  message — but Thomas has not responded to it

The thread captures a live design disagreement, not a resolved consensus. The claim of
"convergence" is Benjamin's assessment of the thread, stated from his own perspective.

**Risk**: Anyone relying on this thread as a record of settled design decisions will be
misled. The thread records ongoing debate, not resolution.

**Confidence**: High — based on the chronological record of the messages.

### 4. The "non-capture-avoiding subs" Is Documented But Its Practical Impact Is Unassessed

The `subs` function in `NaturalDeduction/Basic.lean` line 275 carries a TODO comment
stating "this implementation is not capture avoiding." No message in the thread addresses
this known defect. Benjamin (msg 22) argues at length for substitution invariance
(`substAtom`) but the `subs` function's soundness issue is not mentioned.

**Risk**: The thread discussion of substitution is focused entirely on `substAtom`
(atom-substitution), while the derivation-substitution function `subs` has a known
correctness defect that is not discussed. These are different functions with different
properties. A reader might conflate the two substitution results.

**Confidence**: High — both the TODO comment and the `substAtom` discussion are in the code.

### 5. Message 11 (Matthew) Proposes `canonicalValuation` Using `decide` — This Was Not Adopted

Matthew (msg 11) proposes changing `canonicalValuation` to:
```
noncomputable def canonicalValuation (S : Set (PL.Proposition Atom)) : Valuation Atom :=
  fun p => decide (Proposition.atom p ∈ S)
```

The actual code (`StrongCompleteness.lean` line 72–74) keeps the Prop-valued version:
```lean
def canonicalValuation (S : Set (PL.Proposition Atom)) : Valuation Atom :=
  fun p => Proposition.atom p ∈ S
```

**Risk**: Matthew's proposal was not accepted. A reader might think it was, based on the
thread. Benjamin's explanation (msg 12) explains why: the `decide` approach would change
the type of `canonicalValuation` from `Atom → Prop` to `Atom → Bool` (via `decide`
returning `Bool`), complicating the truth lemma.

**Confidence**: High — confirmed by reading the current file.

### 6. Bridge Lemma Naming Is Inconsistent Between Messages and Code

- Benjamin (msg 10) names the bridge lemma `BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ`
  — this matches `BoolEvaluate_eq_iff` in `Semantics/Bool.lean`
- Benjamin (msg 25) names bridge lemmas `propEvaluateEq` and `boolEvaluateEq` in
  `Semantics/Algebra/Bridge.lean` — these connect to `AlgEvaluate`, a different evaluator

These are two different sets of bridge lemmas, connecting different pairs of evaluators.
The thread switches between discussing them without distinguishing them clearly.

**Risk**: A reader may think `BoolEvaluate_eq_iff` and `boolEvaluateEq` are the same lemma
(they are not). The former bridges `BoolEvaluate` to `Evaluate` (Prop-valued). The latter
bridges `BoolEvaluate` to `AlgEvaluate` (GHA-valued).

**Confidence**: High — verified by reading both files.

### 7. Matthew's Claim About `botForces` Being Unusual Is Not Substantiated

Matthew (msg 19) says "I've never seen anything like @Benjamin Brast-McKie's `botForces`
for Kripke semantics for intuitionistic logic before."

This is accurate as a statement of surprise, but it may be misleading as a claim. The
`botForces` parameter serves a standard role in minimal logic Kripke semantics: in minimal
logic models, ⊥ does not necessarily force a contradiction. This is well-established in the
literature (e.g., Chagrov & Zakharyaschev, *Modal Logic*, Ch. 2). The claim could lead a
reader to think the design is idiosyncratic when it correctly handles the minimal logic
case.

**Risk**: Matthew's skepticism ("I've never seen") is not evidence that the design is wrong.
It is evidence that it is unfamiliar to Matthew. The corresponding algebraic treatment
(`bot_val` as a free parameter in `AlgEvaluate`) is well-motivated.

**Confidence**: Medium — the literature on minimal logic Kripke semantics is sparse and the
standard presentations vary.

### 8. The "10 Primitive Constructors" Count Is Accurate

Benjamin (msg 6, paraphrased) and the `NaturalDeduction/Basic.lean` module doc both claim
10 primitive constructors for `Theory.Derivation`. The actual constructors are:
`ax`, `ass`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `impI`, `impE` — that is
exactly 10.

**Confidence**: High — directly verified.

### 9. Benjamin's Claim About `FromPropositional` Embeddings Is Partially Accurate But Understates Complexity

Benjamin (msg 22, 25) says the `FromPropositional` embeddings benefit from `⊥`-as-constructor
because the map `| .bot => .bot` requires no side conditions. This is true for the
syntactic embedding of formulas.

What is not checked in the thread: whether the FromPropositional maps also require a proof
that the embedding preserves derivability (semantic/proof-theoretic soundness of the
embedding), which is a separate concern from the syntactic map. The thread discussion
focuses only on the syntactic substitution aspect.

**Confidence**: Medium — the claim is accurate for the stated point but may be incomplete.

### 10. The Message 7 Claim About `bot` Is About Historical State, Not Current

Benjamin (msg 7, 2026-06-15): "One issue regarding the syntax is that bot is not currently
taken to be a primitive constructor in Proposition/"

This was a claim about a past version of the code. In the current `Defs.lean`, `bot` IS a
primitive constructor:
```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | bot
  ...
```

**Risk**: This claim is historically accurate (it was the state at the time of writing)
but could confuse a reader encountering it as a description of the current codebase.

**Confidence**: High — the PR mentioned by Benjamin (to add `bot` as a primitive) has been
merged.

### 11. IPL.alg_complete Uses [HeytingAlgebra] With bot_val = ⊥ Implicitly

Benjamin (msg 22, 25) discusses how for IPL, `bot_val = ⊥` is the correct choice.
The actual `IPL.alg_complete` theorem signature in the code:
```lean
theorem IPL.alg_complete {Atom : Type u} [DecidableEq Atom] {A : Proposition Atom} :
    DerivableIn (IPL (Atom := Atom)) A ↔
      ∀ {H : Type u} [HeytingAlgebra H] (v : Atom → H),
        AlgEvaluate v (⊥ : H) A = ⊤
```
This matches the discussion, but the thread never explicitly states the `HeytingAlgebra`
specialization. A reader might not understand why IPL gets `HeytingAlgebra` while MPL gets
`GeneralizedHeytingAlgebra`.

**Confidence**: High — verified in Completeness.lean.

---

## Recommended Additional Verification

1. **Verify Thomas's branch** (referenced as a "potential compromise" in msg 23): The branch
   URL is mentioned but not fully specified. Verify whether `IProposition`, `IDerivation`,
   `propEquiv`, `toDerivation`, `toIDerivation` actually compile and the `Classical.choose`
   claim is accurate. This cannot be done from the current main branch.

2. **Verify the Dedekind-MacNeille completion claim** (msgs 19, 20, 25): Matthew (msg 19)
   links to a modification of Thomas's branch using DM completion. The claim that
   `ipl_conservative_over_mpl` follows from DM completion should be verified against
   the Mathlib API (`Mathlib.Order.CompleteLattice.Completion` or similar). The current
   code uses `sorry` with a comment attributing the gap to DM completion.

3. **Verify the bridge lemma `BoolEvaluate_eq_iff` connects correctly to strong soundness**:
   Benjamin (msg 10) says it enables connecting DPLL to `prop_strong_soundness`. Confirm
   the chain `BoolEvaluate → Evaluate (via BoolEvaluate_eq_iff) → SemanticEntails (via
   prop_strong_soundness)` is actually proven end-to-end, not just stated.

4. **Verify the claim that `noncomputable toIDerivation` uses `Classical.choose`** (msg 25):
   This is a claim about Thomas's branch. If the branch is accessible, check whether
   `Classical.choose` would introduce non-computability in a way that affects usability.

5. **Ching-Tsun Chou** is referenced in messages 12 and 17 as having made suggestions, but
   his actual messages are not visible in the fetched 25 messages (he may have messaged in
   a different Zulip thread or outside this thread). His suggestion about `Bool.lean` alone
   sufficing (msg 12) and agreement about a separate `bot` constructor (msg 17) should be
   tracked down.

---

## Evidence Summary

| Claim | Message | Status | Evidence |
|-------|---------|--------|----------|
| `bot` is primitive constructor in `Proposition` | 7, 22, 25 | ACCURATE (currently) | `Defs.lean` line 85: `\| bot` |
| 10 primitive ND constructors | 6 (paraphrase), module doc | ACCURATE | Count: ax, ass, andI, andE1, andE2, orI1, orI2, orE, impI, impE |
| `deductionTheorem` exists | 6 | ACCURATE | `Metalogic/DeductionTheorem.lean` confirmed |
| `min_strong_completeness` exists | 6 | ACCURATE | `Metalogic/MinStrongCompleteness.lean` line 244 |
| `int_strong_completeness` exists | 6 | ACCURATE | `Metalogic/IntStrongCompleteness.lean` line 246 |
| `prop_strong_completeness` exists | 6 | ACCURATE | `Metalogic/StrongCompleteness.lean` line 490 |
| `hilbert_iff_nd` family (8 theorems) | module doc | ACCURATE | `NaturalDeduction/Equivalence.lean` lines 305–360 |
| `BoolEvaluate_eq_iff` exists in `Bool.lean` | 10 | ACCURATE | `Semantics/Bool.lean` line 114 |
| `canonicalValuation` uses `Prop` (not `decide`) | 10, 11, 12 | ACCURATE (current) | `StrongCompleteness.lean` line 72–74 |
| `Theory.complete` (Thomas's name) = `Theory.alg_complete` | 18, 25 | MISLEADING | Name is `alg_complete`; signature differs |
| `AlgTValid` notation for `v ⊨ T` | 18, 25 | ACCURATE | `Semantics/Algebra.lean` line 141 |
| `propEvaluateEq` and `boolEvaluateEq` in `Bridge.lean` | 25 | ACCURATE | `Semantics/Algebra/Bridge.lean` lines 58, 78 |
| One sorry (`ipl_conservative_over_mpl`) | thread context | ACCURATE | `Conservative.lean` line 99 |
| `subs` is non-capture-avoiding | thread context | ACCURATE (known defect) | `Basic.lean` line 275 TODO |
| `IProposition`/`IDerivation` in Thomas's branch | 23, 25 | UNVERIFIABLE from main | Not in current codebase |
| Thread "has converged" on ⊥-as-primitive | 25 | OVERSTATED | Thomas has not responded to msg 25 |

---

## Confidence Level

**Overall**: High for verifiable code claims; Medium for design philosophy claims; Low for
claims about Thomas's unmerged branch.

The principal risk in this thread is that readers will conflate:
1. What is in current CSLib main vs. what is in experimental branches
2. Thomas's (branch) naming conventions vs. actual theorem names in CSLib
3. The `substAtom` (atom-substitution, sound) result vs. `subs` (hypothesis-substitution,
   non-capture-avoiding, defective TODO)
4. The different bridge lemma pairs (`BoolEvaluate_eq_iff` vs. `boolEvaluateEq`)
5. Benjamin's summary of consensus vs. actual remaining disagreement
