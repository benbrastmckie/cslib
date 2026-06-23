# Research Report: Brouwerian Soundness and Completeness (Task 306)

## 1. Executive Summary

This task requires proving soundness and completeness of IPL{and,imp,top} w.r.t. Brouwerian
semilattices. The existing infrastructure provides a near-exact template: the
`HilbertLindenbaum.lean` construction for `MinPropAxiom` / `MinimalAxioms` can be adapted to
`ConjImpAxiom` with the key simplification that no join (sup) operation is needed. The target
file is `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean`.

## 2. Existing Infrastructure Analysis

### 2.1 Template: HilbertLindenbaum.lean

The existing `HilbertLindenbaum.lean` constructs the Lindenbaum-Tarski algebra for axiom
predicates satisfying `MinimalAxioms` (which requires K, S, andI, andE1, andE2, orI1, orI2,
orE). The construction:

1. Defines `HilbertEquiv Axioms A B := Deriv Axioms [A] B /\ Deriv Axioms [B] A`
2. Proves it is an equivalence relation (refl, symm, trans)
3. Builds a `Setoid` and quotient type `HilbertLindenbaumAlgebra`
4. Defines quotient operations: `hilbertLindenbaumLe`, `hilbertLindenbaumInf`,
   `hilbertLindenbaumSup`, `hilbertLindenbaumHimp`
5. Proves all GHA axioms and constructs a `GeneralizedHeytingAlgebra` instance
6. Defines `canonicalV` and proves the truth lemma `canonicalV_spec`
7. Proves `hilbertLindenbaumMk_eq_top_iff`

### 2.2 Key Difference: No Join Required

The Brouwerian Lindenbaum algebra only needs:
- **LE (order)**: `[A] <= [B] iff Deriv ConjImpAxiom [A] B`
- **Inf (meet)**: `[A] inf [B] = [A and B]`
- **HImp**: `[A] himp [B] = [A imp B]`
- **Top**: `[top]` (which is `[bot.imp bot]`)

It does NOT need:
- **Sup (join)**: No `hilbertLindenbaumSup` analogue
- **OrI1, OrI2, OrE axioms**: `ConjImpAxiom` does not include these

This simplifies the construction significantly. The `BrouwerianSemilattice` typeclass requires
only `SemilatticeInf`, `OrderTop`, `HImp`, and the adjunction `le_himp_iff`.

### 2.3 Template: HilbertCompleteness.lean

The completeness proof pattern is:
1. **Soundness direction**: Proved via case analysis on axiom constructors
2. **Completeness direction**: Instantiate validity at the Lindenbaum algebra with canonical
   valuation, apply truth lemma, extract derivability

### 2.4 Template: Soundness.lean

Soundness is proved by:
1. Showing each axiom schema evaluates to top in the target algebra class
2. Showing modus ponens preserves top-evaluation
3. Induction on the derivation tree

### 2.5 BrouwerianSemilattice (Task 303)

Located at `Cslib/Foundations/Order/BrouwerianSemilattice.lean`. Key lemmas available:
- `BrouwerianSemilattice.le_himp_iff`: The adjunction `a <= b himp c <-> a inf b <= c`
- `BrouwerianSemilattice.himp_eq_top_iff`: `a himp b = top <-> a <= b`
- `BrouwerianSemilattice.himp_inf_le`: Modus ponens `(a himp b) inf a <= b`
- `BrouwerianSemilattice.himp_self`: `a himp a = top`
- `BrouwerianSemilattice.le_himp`: `a <= b himp a` (weakening)
- `BrouwerianSemilattice.himp_himp`: Currying `a himp (b himp c) = (a inf b) himp c`

### 2.6 BrouwerianEvaluate (Task 303)

Located at `Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean`:
- `BrouwerianEvaluate v (.atom x) = v x`
- `BrouwerianEvaluate v (.bot) = top` (default, no bottom in Brouwerian semilattice)
- `BrouwerianEvaluate v (.imp a b) = BrouwerianEvaluate v a himp BrouwerianEvaluate v b`
- `BrouwerianEvaluate v (.and a b) = BrouwerianEvaluate v a inf BrouwerianEvaluate v b`
- `BrouwerianEvaluate v (.or _ _) = top` (default)
- `BrouwerianValid phi` = for all H, v: `BrouwerianEvaluate v phi = top`

### 2.7 ConjImpAxiom (Task 305)

Located at `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean`:
- 5 constructors: `implyK`, `implyS`, `andI`, `andE1`, `andE2`
- Subsumption: `ConjImpAxiom.toMinPropAxiom`
- Witnesses: `ConjImpAxiom.mem_implyK`, `ConjImpAxiom.mem_implyS`
- Deduction theorem: `conjImpAxiom_hasDeductionTheorem`

### 2.8 FragmentInstances (Task 305)

Located at `Cslib/Logics/Propositional/ProofSystem/FragmentInstances.lean`:
- `InferenceSystem Propositional.HilbertConjImp` registered
- `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomAndI`, `HasAxiomAndE1`,
  `HasAxiomAndE2`, `MinimalHilbert` instances registered
- Requires `[DecidableEq Atom]`

### 2.9 Derived Rules Available

All Hilbert derived rules in `HilbertDerivedRules.lean` are parameterized over explicit axiom
witnesses (not `MinimalAxioms`), so they work with `ConjImpAxiom` directly. Key ones:
- `hilbertImpIDeriv h_K h_S`: From `Deriv (A :: Gamma) B`, derive `Deriv Gamma (A imp B)`
- `hilbertImpEDeriv`: Modus ponens
- `hilbertAndIDeriv h_andI`: Conjunction introduction
- `hilbertAndE1Deriv h_andE1`: Left conjunction elimination
- `hilbertAndE2Deriv h_andE2`: Right conjunction elimination
- `hilbertCutSingletonDeriv h_K h_S`: Cut on singleton contexts
- `hilbertCutListDeriv h_K h_S`: Cut on general contexts
- `hilbertWeakenSingleton`: Weaken from singleton to cons list

These are all usable with `ConjImpAxiom.mem_implyK` and `ConjImpAxiom.mem_implyS`.

## 3. Proof Architecture

### 3.1 Soundness

**Statement**: If `Derivable ConjImpAxiom phi` then `BrouwerianValid phi`.

**Proof Strategy** (following `Soundness.lean` pattern):

Step 1: Prove each `ConjImpAxiom` constructor evaluates to top in any `BrouwerianSemilattice`.

For each constructor, we need `BrouwerianEvaluate v phi = top`:

- **implyK** (`phi imp (psi imp phi)`):
  `BrouwerianEvaluate = (v_phi himp (v_psi himp v_phi))`.
  By `himp_eq_top_iff + le_himp_iff`: need `v_phi inf v_psi <= v_phi`, which is `inf_le_left`.

- **implyS** (`(phi imp (psi imp chi)) imp ((phi imp psi) imp (phi imp chi))`):
  Same algebraic argument as in `Soundness.lean`, but using `BrouwerianSemilattice` lemmas
  instead of `GeneralizedHeytingAlgebra` ones. The proof is identical structurally because
  `BrouwerianSemilattice` provides the same `le_himp_iff` and `himp_inf_le`.

- **andI** (`phi imp (psi imp (phi and psi))`):
  Need `v_phi inf v_psi <= v_phi inf v_psi`. Trivially `le_refl`.

- **andE1** (`(phi and psi) imp phi`):
  Need `v_phi inf v_psi <= v_phi`. This is `inf_le_left`.

- **andE2** (`(phi and psi) imp psi`):
  Need `v_phi inf v_psi <= v_psi`. This is `inf_le_right`.

Step 2: Prove soundness at the derivation tree level by induction (match on derivation tree
constructors: ax, assumption, modus_ponens, weakening).

Step 3: Derive `conjImp_brouwerian_soundness_derivable`: `Derivable ConjImpAxiom phi ->
BrouwerianValid phi`.

**Key observation**: The soundness proof is structurally identical to `min_alg_axiom_sound`
but:
- Uses `BrouwerianSemilattice` instead of `GeneralizedHeytingAlgebra`
- Uses `BrouwerianEvaluate` instead of `AlgEvaluate`
- Has only 5 cases instead of 8 (no orI1, orI2, orE)
- Uses `BrouwerianSemilattice.himp_eq_top_iff` and `BrouwerianSemilattice.le_himp_iff`
  instead of Mathlib's `himp_eq_top_iff` and `le_himp_iff`

### 3.2 Lindenbaum Construction

**Key structures to define**:

1. **ConjImpEquiv**: `ConjImpEquiv A B := Deriv ConjImpAxiom [A] B /\ Deriv ConjImpAxiom [B] A`

2. **conjImpPropositionSetoid**: The setoid on `Proposition Atom`. Reflexivity via assumption,
   symmetry by swapping, transitivity via `hilbertCutSingletonDeriv` with
   `ConjImpAxiom.mem_implyK` and `ConjImpAxiom.mem_implyS`.

3. **BrouwerianLindenbaumAlgebra**: `Quotient conjImpPropositionSetoid`

4. **Quotient map**: `brouwerianLindenbaumMk A : BrouwerianLindenbaumAlgebra`

5. **Order**: `[A] <= [B] iff Deriv ConjImpAxiom [A] B`

6. **Meet**: `[A] inf [B] = [A and B]` (requires and-congruence)

7. **HImp**: `[A] himp [B] = [A imp B]` (requires imp-congruence)

8. **Top**: `[Proposition.top]` = `[bot.imp bot]`

**Congruence lemmas needed** (paralleling HilbertLindenbaum.lean):
- `conjImpEquivAndCongr`: If `A ~ A'` and `B ~ B'` then `A and B ~ A' and B'`
- `conjImpEquivImpCongr`: If `A ~ A'` and `B ~ B'` then `A imp B ~ A' imp B'`

These proofs follow exactly the same structure as `hilbertEquivAndCongr` and
`hilbertEquivImpCongr`, but using `ConjImpAxiom` witnesses instead of `MinimalAxioms`.

**Key simplification**: No `conjImpEquivOrCongr` needed (no join in the algebra).

### 3.3 BrouwerianSemilattice Instance

Need to prove:
- **le_refl**: Via `assumption_deriv`
- **le_trans**: Via `hilbertCutSingletonDeriv`
- **le_antisymm**: Via `Quotient.sound`
- **inf_le_left**: `[A and B] <= [A]` via `hilbertAndE1Deriv`
- **inf_le_right**: `[A and B] <= [B]` via `hilbertAndE2Deriv`
- **le_inf**: From `[A] <= [B]` and `[A] <= [C]`, derive `[A] <= [B and C]` via `hilbertAndIDeriv`
- **le_top**: `[A] <= [top]` via `hilbertImpIDeriv` (derive `[] |- A imp (bot imp bot)`)
- **le_himp_iff**: `[A] <= [B imp C] <-> [A and B] <= [C]`

The `le_himp_iff` proof is the hardest. It follows exactly the same structure as
`hilbertLindenbaumLe_himp_iff` in the existing code:
- Forward: From `[A] |- B imp C`, get `[A and B] |- C` using andE1, andE2, impE
- Backward: From `[A and B] |- C`, get `[A] |- B imp C` using impI, andI

### 3.4 Truth Lemma

**Canonical valuation**: `brouwerianCanonicalV p = brouwerianLindenbaumMk (.atom p)`

**Truth lemma**: `BrouwerianEvaluate brouwerianCanonicalV A = brouwerianLindenbaumMk A`

Proof by structural induction on `A`:
- `atom x`: By definition `brouwerianCanonicalV x = brouwerianLindenbaumMk (.atom x)`. Done.
- `bot`: `BrouwerianEvaluate v .bot = top`. And `top = brouwerianLindenbaumMk (.top)`. Need
  `top = [bot.imp bot]`. Since top in the `BrouwerianSemilattice` instance is `[Proposition.top]`
  and `Proposition.top = .imp .bot .bot`, this should be definitional or a simple rewrite.
  **Wait**: `BrouwerianEvaluate v .bot = top` (the algebra top), and the top in our
  `BrouwerianSemilattice` instance is `brouwerianLindenbaumMk Proposition.top`. But
  `brouwerianLindenbaumMk .bot` is NOT the top element. We need to show
  `brouwerianLindenbaumMk .bot = top`.
  
  Actually, in the Brouwerian case, `BrouwerianEvaluate v .bot = top`. And in our Lindenbaum
  algebra, `top = brouwerianLindenbaumMk Proposition.top = brouwerianLindenbaumMk (.imp .bot .bot)`.
  So we need `[bot] = top` in the quotient. That means `Deriv ConjImpAxiom [bot] (.imp .bot .bot)`
  AND `Deriv ConjImpAxiom [.imp .bot .bot] .bot`. The first is fine (via impI on assumption).
  But the second requires deriving `.bot` from `[.imp .bot .bot]`, which requires applying
  `(.imp .bot .bot)` to `.bot`. But we can only get `.bot` if we already have `.bot`!
  
  **CRITICAL ISSUE**: `[bot]` is NOT equivalent to `[top]` under `ConjImpAxiom`. Since
  `ConjImpAxiom` has no EFQ axiom, we cannot derive `.bot` from `[.imp .bot .bot]`, and
  we cannot derive arbitrary propositions from `.bot`. So `[bot] != top` in the quotient.
  
  **Resolution**: The truth lemma maps `BrouwerianEvaluate v A` to `brouwerianLindenbaumMk A`
  only for formulas in the `{and, imp}` fragment (no bot, no or). For the `bot` and `or` cases:
  - `BrouwerianEvaluate v .bot = top` (algebra top)
  - `BrouwerianEvaluate v (.or a b) = top` (algebra top)
  
  But `brouwerianLindenbaumMk .bot` is NOT top. So the truth lemma cannot state
  `BrouwerianEvaluate v A = brouwerianLindenbaumMk A` for all A.
  
  **However**: For the completeness proof, we only need the truth lemma for formulas that are
  actually derivable in the `ConjImpAxiom` system. And in practice, the truth lemma approach
  used in `HilbertCompleteness.lean` works differently: it evaluates with a canonical
  valuation and then extracts derivability from `[phi] = top`.
  
  **The correct approach** is:
  1. The truth lemma should state: for the canonical valuation `v(p) = [atom p]`,
     `BrouwerianEvaluate v A = brouwerianLindenbaumMk A` holds for ALL formulas A.
  2. For `.bot`: we need `top = brouwerianLindenbaumMk .bot`. This requires `[bot] = top`.
  3. For `.or`: we need `top = brouwerianLindenbaumMk (.or a b)`. This requires `[a or b] = top`.
  
  Neither of these hold in general! The quotient `[bot]` is NOT top because ConjImpAxiom
  cannot derive everything from bot.
  
  **CORRECT SOLUTION**: The truth lemma is NOT stated as `BrouwerianEvaluate v A = [A]` for
  all A. Instead, the completeness proof works as follows:
  
  The completeness direction says: if `BrouwerianValid phi` then `Derivable ConjImpAxiom phi`.
  
  To prove this, instantiate `BrouwerianValid phi` at the Brouwerian Lindenbaum algebra with
  the canonical valuation `v(p) = [atom p]`. This gives
  `BrouwerianEvaluate brouwerianCanonicalV phi = top`.
  
  Now we need a "truth lemma" that converts this to `brouwerianLindenbaumMk phi = top` (which
  then gives `Derivable ConjImpAxiom phi` via the analogue of
  `hilbertLindenbaumMk_eq_top_iff`).
  
  The truth lemma for the Brouwerian case is:
  `BrouwerianEvaluate brouwerianCanonicalV A = brouwerianLindenbaumMk A`
  
  This works for:
  - `atom x`: trivially
  - `imp a b`: `[a] himp [b] = [a imp b]` by the himp definition on the quotient
  - `and a b`: `[a] inf [b] = [a and b]` by the inf definition on the quotient
  - `bot`: Need `top = [bot]`. **THIS IS THE PROBLEM.**
  - `or a b`: Need `top = [a or b]`. **ALSO A PROBLEM.**
  
  **FINAL RESOLUTION**: The truth lemma CAN be stated for all A, BUT the `.bot` and `.or`
  cases require that `[bot] = top` and `[or a b] = top` in the Lindenbaum algebra. Let us
  check whether `[bot] = top`:
  - Top is `[Proposition.top]` = `[bot.imp bot]` in the HilbertLindenbaum construction.
  - `[bot] = top` iff `ConjImpEquiv bot (bot.imp bot)`, i.e., `Deriv ConjImpAxiom [bot] (bot.imp bot)` AND `Deriv ConjImpAxiom [bot.imp bot] bot`.
  - First direction: From `[bot]`, derive `bot.imp bot`: use impI; from `[bot, bot]`, derive `bot` by assumption. So `[bot] |- bot.imp bot`. YES.
  - Second direction: From `[bot.imp bot]`, derive `bot`: apply `bot.imp bot` to `bot`. But we need `bot` to apply it! We don't have `bot`. So we CANNOT derive `bot` from `[bot.imp bot]`. NO.
  
  So `[bot] != top`. This means the naive truth lemma fails for `.bot`.
  
  **THE REAL SOLUTION**: Don't define top as `[bot.imp bot]`. Instead, define top as `[bot]`!
  
  Wait, that doesn't work either because then `[bot]` would be top, but `[A] <= [bot]` would
  mean `Deriv ConjImpAxiom [A] bot`, which we can't prove for all A without EFQ.
  
  **ACTUALLY**, we need `le_top`: for all x, `x <= top`. If top is `[bot]`, we need
  `Deriv ConjImpAxiom [A] bot` for all A, which is false.
  
  If top is `[bot.imp bot]`, we need `Deriv ConjImpAxiom [A] (bot.imp bot)` for all A. This
  is: derive `bot imp bot` from `[A]`. Using impI: from `[bot, A]`, derive `bot` by assumption.
  So `[A] |- bot.imp bot`. YES, this works. So top = `[bot.imp bot]` and le_top is satisfied.
  
  So the issue is specifically with the truth lemma's `.bot` case. The solution:
  
  **The truth lemma does NOT need to hold for `.bot` and `.or` because these connectives
  evaluate to `top` in `BrouwerianEvaluate`, and in the completeness proof, if the INPUT
  formula `phi` is `BrouwerianValid`, then `BrouwerianEvaluate v phi = top`. But if `phi`
  contains `.bot` or `.or`, those subformulas map to `top` in the evaluator, which is fine
  because the truth lemma only needs to give us `BrouwerianEvaluate v phi = [phi]` when
  restricted to the fragment.**
  
  **Actually, we need a different approach. The simplest solution**:
  
  The truth lemma states: `BrouwerianEvaluate brouwerianCanonicalV A = brouwerianLindenbaumMk A`
  
  For `.bot`: LHS = `top`. RHS = `brouwerianLindenbaumMk .bot`. We need `[bot] = top`.
  But `[bot] != top` as shown above.
  
  **The correct approach is to NOT use this equality for bot/or cases. Instead**:
  
  Since `BrouwerianEvaluate v .bot = top` and `BrouwerianEvaluate v (.or a b) = top`, the
  truth lemma should be:
  
  `BrouwerianEvaluate brouwerianCanonicalV A = top -> brouwerianLindenbaumMk A = top`
  
  This is what we actually need for completeness! But this is weaker and easier to prove.
  We can prove it by induction on A:
  - For `atom x`: If `[atom x] = top`, then done.
  - For `imp a b`: If `[a] himp [b] = top`, then `[a imp b] = top`.
  - For `and a b`: If `[a] inf [b] = top`, then `[a and b] = top`.
  - For `bot`: `top = top`. Done trivially.
  - For `or`: `top = top`. Done trivially.
  
  **Wait, this is the wrong direction.** We need:
  `BrouwerianEvaluate v phi = top -> Derivable ConjImpAxiom phi`
  
  The simplest approach: prove the truth lemma as an IMPLICATION rather than an equality.
  `BrouwerianEvaluate brouwerianCanonicalV A = top -> brouwerianLindenbaumMk A = top`
  
  By induction:
  - `atom x`: hypothesis gives `[atom x] = top`, i.e., `Derivable ConjImpAxiom (atom x)`,
    so `brouwerianLindenbaumMk (atom x) = top` by mk_eq_top_iff.
  - `imp a b`: `BrouwerianEvaluate v (a imp b) = [a] himp [b]` (where we use the
    structural induction hypotheses to replace subterms... no, this doesn't work as stated
    because the IH applies when the subterm evaluates to top, not in general.)
  
  **REVISED APPROACH**: The truth lemma should be a true equality, not just an implication.
  The way to handle it is the same as `canonicalV_spec` in the GHA case:
  
  Looking at `canonicalV_spec` more carefully: it has a `canonicalBotVal` parameter, which
  is `hilbertLindenbaumMk .bot`. In the GHA Lindenbaum algebra, `.bot` is mapped to
  `hilbertLindenbaumMk .bot` as the bot_val parameter of `AlgEvaluate`. The truth lemma
  says `AlgEvaluate (canonicalV) (canonicalBotVal) A = hilbertLindenbaumMk A` for ALL A,
  including `.bot` (where both sides reduce to `hilbertLindenbaumMk .bot`).
  
  For `BrouwerianEvaluate`, the `.bot` case gives `top`, not `hilbertLindenbaumMk .bot`.
  So the truth lemma `BrouwerianEvaluate v A = brouwerianLindenbaumMk A` FAILS for `.bot`.
  
  **THE DEFINITIVE SOLUTION**: We need a modified approach that works around the bot/or issue.
  
  **Option 1: Restrict to the fragment.**
  State the truth lemma only for `IsOrBotFree` formulas:
  `A.IsOrBotFree = true -> BrouwerianEvaluate brouwerianCanonicalV A = brouwerianLindenbaumMk A`
  
  Then for completeness: if `phi` is a formula in the or-bot-free fragment (which all
  ConjImpAxiom instances are), the truth lemma applies.
  
  **BUT**: The completeness theorem says `BrouwerianValid phi -> Derivable ConjImpAxiom phi`
  for ALL phi, not just or-bot-free ones. For formulas containing bot/or, `BrouwerianEvaluate`
  maps those to `top`, making it trivially valid. We need a different argument for those cases.
  
  Actually, for formulas containing bot or or, `BrouwerianValid phi` doesn't necessarily hold
  unless the formula evaluates to top regardless. E.g., `bot imp bot` evaluates to
  `top himp top = top`, so it's Brouwerian-valid. And `atom x` evaluates to `v x`, which is
  not necessarily top. The point is: the validity condition is on the WHOLE formula.
  
  **Option 2: Redefine top in the Brouwerian Lindenbaum algebra.**
  Instead of `top = [bot.imp bot]`, use a different representative. But there's no natural
  choice that makes `[bot] = top`.
  
  **Option 3: The cleanest solution.**
  
  Observe that in `BrouwerianEvaluate`, bot and or both map to `top`. So the truth lemma
  only needs to handle the `{atom, imp, and}` connectives inductively, with bot and or
  being trivially `top = top`. The issue is that `brouwerianLindenbaumMk .bot` is NOT `top`.
  
  So the truth lemma should say:
  ```
  BrouwerianEvaluate brouwerianCanonicalV A = brouwerianLindenbaumMk_modified A
  ```
  where `brouwerianLindenbaumMk_modified` maps `.bot` to `top` and `.or a b` to `top`.
  
  But that's ugly. The real insight is:
  
  **We don't need `BrouwerianEvaluate v A = [A]` for ALL A. We only need it for the specific
  phi that appears in the completeness statement. And if `BrouwerianValid phi` holds, we need
  `BrouwerianEvaluate v phi = top -> Derivable ConjImpAxiom phi`.**
  
  **Option 4 (RECOMMENDED): Prove the truth lemma for or-bot-free formulas, then prove
  completeness for all formulas by a case analysis.**
  
  For the completeness direction:
  - If `phi` is or-bot-free: use the Lindenbaum construction + restricted truth lemma.
  - If `phi` contains bot or or: these subformulas evaluate to `top` in every
    `BrouwerianSemilattice`, making the validity condition potentially trivially satisfiable
    or unsatisfiable depending on the overall formula structure.
  
  **Actually, the simplest is Option 5:**
  
  **Option 5 (SIMPLEST AND RECOMMENDED):**
  
  Define the truth lemma inductively, handling each case:
  
  ```lean
  theorem brouwerianCanonicalV_spec (A : PL.Proposition Atom) :
      BrouwerianEvaluate (brouwerianCanonicalV) A =
      match A with
      | .bot => top
      | .or _ _ => top  
      | _ => brouwerianLindenbaumMk A
  ```
  
  No wait, this doesn't typecheck cleanly.
  
  **Option 6 (ACTUALLY THE SIMPLEST):**
  
  Just prove `BrouwerianEvaluate v phi = top -> Derivable ConjImpAxiom phi` directly
  without a truth lemma intermediary. We instantiate at the Lindenbaum algebra, so
  `BrouwerianEvaluate brouwerianCanonicalV phi = top`. Then we need to extract
  `Derivable ConjImpAxiom phi`. We prove this by induction on phi:
  
  - `atom x`: `v x = top` means `[atom x] = top` means `Derivable ConjImpAxiom (atom x)`.
  - `bot`: `top = top` means nothing. But we need `Derivable ConjImpAxiom bot`. This is FALSE
    in general! So if `BrouwerianValid bot`, then... let's check: `BrouwerianEvaluate v bot = top`
    for all H, v. That's `top = top`. True. So `bot` IS Brouwerian-valid. But `bot` is NOT
    derivable in `ConjImpAxiom`. **THIS MEANS THE COMPLETENESS DIRECTION IS FALSE AS STATED!**
  
  **WAIT.** Let me re-examine: `bot` IS Brouwerian-valid because `BrouwerianEvaluate v bot = top`
  by definition. But `bot` is NOT derivable from `ConjImpAxiom` (there's no EFQ, and no way to
  derive falsum from nothing). So `BrouwerianValid phi -> Derivable ConjImpAxiom phi` is FALSE
  for `phi = bot`.
  
  **This means the completeness theorem as stated in the task description is WRONG for formulas
  outside the or-bot-free fragment.**
  
  **CORRECTION**: The completeness theorem must be restricted to the or-bot-free fragment:
  
  ```
  For phi or-bot-free:
    Derivable ConjImpAxiom phi <-> BrouwerianValid phi
  ```
  
  Or equivalently: the Brouwerian evaluator is only faithful on the `{and, imp, atom}` fragment.
  This is exactly what the design notes in `Brouwerian.lean` state: "On formulas in the
  {inf, himp, top} fragment (i.e., formulas where bot and or do not appear)..."
  
  **So the correct approach is:**
  
  1. State soundness for ALL formulas: `Derivable ConjImpAxiom phi -> BrouwerianValid phi`.
     This is correct because `ConjImpAxiom` only has or-bot-free axioms, and or/bot evaluate
     to top (vacuously true). Actually wait: even soundness needs care. If `phi` has or/bot
     subformulas, then `BrouwerianEvaluate` maps those to `top`, which may or may not match
     what the axiom system derives.
     
     Actually, soundness is simpler: if `Derivable ConjImpAxiom phi`, then `phi` is provable
     using only K, S, andI, andE1, andE2, and modus ponens. Since all these axioms evaluate
     to top in every BrouwerianSemilattice (we can verify each), and modus ponens preserves
     top-evaluation (using himp_eq_top_iff), soundness holds for ALL phi.
     
  2. State completeness for or-bot-free formulas:
     `phi.IsOrBotFree = true -> BrouwerianValid phi -> Derivable ConjImpAxiom phi`
     
  3. The truth lemma is: for or-bot-free A:
     `BrouwerianEvaluate brouwerianCanonicalV A = brouwerianLindenbaumMk A`

  4. `brouwerianLindenbaumMk_eq_top_iff`:
     `brouwerianLindenbaumMk A = top <-> Derivable ConjImpAxiom A`

  **Actually let me reconsider once more.** Maybe the task description's intention is that the
  completeness theorem is only for formulas in the `{and, imp, top}` fragment, i.e., formulas
  built using `atom`, `and`, `imp` only (or with `.top` = `.imp .bot .bot`). The task says
  "IPL{and, imp, top}" which is exactly the or-bot-free fragment.
  
  **Let me re-read the task**: "if Derivable ConjImpAxiom phi then BrouwerianEvaluate v phi = top
  in every BrouwerianSemilattice" (soundness) and completeness via Lindenbaum.
  
  The right statement for the biconditional is:
  
  ```
  For phi in the or-bot-free fragment:
    Derivable ConjImpAxiom phi <-> BrouwerianValid phi
  ```
  
  For soundness without the fragment restriction:
  ```
  Derivable ConjImpAxiom phi -> BrouwerianValid phi
  ```
  (This is correct for all phi.)

### 3.5 The Or-Bot-Free Truth Lemma (Revised)

For the canonical valuation `v(p) = [atom p]` and an or-bot-free formula A:

```
BrouwerianEvaluate brouwerianCanonicalV A = brouwerianLindenbaumMk A
```

Proof by induction on A (only `atom`, `imp`, `and` cases since A is or-bot-free):
- `atom x`: `v x = [atom x]`. Done by definition.
- `imp a b`: `BrouwerianEvaluate v (a imp b) = BrouwerianEvaluate v a himp BrouwerianEvaluate v b`.
  By IH on a and b (both or-bot-free): `= [a] himp [b] = [a imp b]`.
  Uses `brouwerianLindenbaumMk_himp` simp lemma.
- `and a b`: Similar, uses `brouwerianLindenbaumMk_inf`.
- `bot`: Cannot occur (contradicts `IsOrBotFree`).
- `or`: Cannot occur (contradicts `IsOrBotFree`).

### 3.6 The mk_eq_top_iff Lemma

```
brouwerianLindenbaumMk A = top <-> Derivable ConjImpAxiom A
```

Where `top = brouwerianLindenbaumMk (bot.imp bot)`.

Forward: `[A] = [bot.imp bot]` means `ConjImpEquiv A (bot.imp bot)`, so
`Deriv ConjImpAxiom [bot.imp bot] A`. Combined with `Derivable ConjImpAxiom (bot.imp bot)`
(provable via impI + assumption), we get `Derivable ConjImpAxiom A` by cut.

Backward: `Derivable ConjImpAxiom A` means `Deriv ConjImpAxiom [] A`.
Need `[A] = [bot.imp bot]`, i.e., `Deriv [A] (bot.imp bot)` and `Deriv [bot.imp bot] A`.
First: `[A] |- bot.imp bot` via impI + assumption. Done.
Second: `[bot.imp bot] |- A` via weakening from `[] |- A`.

### 3.7 Complete Proof Architecture

The file `BrouwerianCompleteness.lean` should contain:

**Section 1: Brouwerian Soundness**
- `conjImp_brouwerian_axiom_sound`: Each ConjImpAxiom is BrouwerianValid
- `conjImp_brouwerian_soundness`: Derivation-level soundness
- `conjImp_brouwerian_soundness_derivable`: Derivable -> BrouwerianValid

**Section 2: Brouwerian Lindenbaum Construction**
- `ConjImpEquiv`: The equivalence relation
- `conjImpEquiv_refl`, `conjImpEquiv_symm`, `conjImpEquiv_trans`
- `conjImpPropositionSetoid`: The setoid
- `BrouwerianLindenbaumAlgebra`: The quotient type
- `brouwerianLindenbaumMk`: The quotient map
- Congruence: `conjImpEquivAndCongr`, `conjImpEquivImpCongr`
- Operations: `brouwerianLindenbaumLe`, `brouwerianLindenbaumInf`, `brouwerianLindenbaumHimp`
- Simp lemmas: `brouwerianLindenbaumLe_mk`, `brouwerianLindenbaumInf_mk`, `brouwerianLindenbaumHimp_mk`

**Section 3: BrouwerianSemilattice Instance**
- Proofs of all BrouwerianSemilattice axioms
- `brouwerianLindenbaumBSL`: The BrouwerianSemilattice instance

**Section 4: Truth Lemma and Completeness**
- `brouwerianLindenbaumMk_eq_top_iff`: `[A] = top <-> Derivable ConjImpAxiom A`
- `brouwerianCanonicalV`: The canonical valuation
- `brouwerianCanonicalV_spec`: Truth lemma (for IsOrBotFree formulas)
- `conjImp_brouwerian_complete`: The completeness theorem (for IsOrBotFree formulas)
  `A.IsOrBotFree = true -> BrouwerianValid A -> Derivable ConjImpAxiom A`
- The biconditional: `A.IsOrBotFree = true -> (Derivable ConjImpAxiom A <-> BrouwerianValid A)`

## 4. Technical Considerations

### 4.1 Universe Polymorphism

Following `HilbertCompleteness.lean`, the completeness theorem needs universe annotations.
The Lindenbaum algebra lives at universe `u` (same as `Atom : Type u`), and `BrouwerianValid`
quantifies over all types at some universe. The statement should be:

```lean
theorem conjImp_brouwerian_complete {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrBotFree = true)
    (h : BrouwerianValid.{u, u} φ) :
    Derivable ConjImpAxiom φ
```

### 4.2 Noncomputability

The construction is `noncomputable` (like HilbertLindenbaum) because it uses `Quotient.lift`
and the deduction theorem (which is noncomputable due to WF recursion on derivation trees).

### 4.3 Imports

The file needs:
```lean
public import Cslib.Logics.Propositional.Semantics.Algebra.Brouwerian
public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates
public import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules
```

The `HilbertLindenbaum` file should NOT be imported directly (to avoid pulling in
`MinimalAxioms` and the GHA instance which would create diamond issues). However, some
helpers defined there (`hilbertCutSingletonDeriv`, `hilbertWeakenSingleton`,
`hilbertCutListDeriv`) will be needed. These are currently defined in `HilbertLindenbaum.lean`.

**Two options:**
1. Import `HilbertLindenbaum.lean` and reuse the helpers (they are parameterized over arbitrary
   `Axioms` with explicit K/S witnesses, so they work with `ConjImpAxiom`).
2. Duplicate the helpers in the new file.

**Option 1 is preferred** (reuse-first). The helpers `hilbertCutSingletonDeriv`,
`hilbertWeakenSingleton`, and `hilbertCutListDeriv` are not specific to `MinimalAxioms`.

### 4.4 DecidableEq Consideration

The `FragmentInstances.lean` requires `[DecidableEq Atom]`. The Lindenbaum construction
in `HilbertLindenbaum.lean` does NOT require `DecidableEq`. We should check whether our
construction needs it. Looking at the helpers:
- `hilbertCutSingletonDeriv`: No DecidableEq needed
- `impIDeriv`: No DecidableEq needed (uses WF recursion on height)
- `Quotient` operations: No DecidableEq needed

So the Brouwerian Lindenbaum construction should NOT require `DecidableEq Atom`.

### 4.5 The IsOrBotFree Induction Tactic

For the truth lemma restricted to `IsOrBotFree`, the proof by induction needs to handle
the `bot` and `or` cases by contradiction (since `IsOrBotFree bot = false`). This is
straightforward: `simp [Proposition.IsOrBotFree]` discharges these impossible cases.

## 5. Potential Blockers

### 5.1 No Blockers Identified

All prerequisites are in place:
- `BrouwerianSemilattice` typeclass with all needed lemmas (task 303 complete)
- `BrouwerianEvaluate` and `BrouwerianValid` (task 303 complete)
- `ConjImpAxiom` with witnesses and deduction theorem (task 305 complete)
- All Hilbert derived rules available with explicit axiom witnesses
- The `HilbertLindenbaum.lean` provides a near-exact template
- The `IsOrBotFree` predicate for the truth lemma restriction (task 302 complete)

### 5.2 Risk: Universe Issues in BrouwerianValid

`BrouwerianValid` quantifies over `(H : Type*) [BrouwerianSemilattice H]`. The Lindenbaum
algebra lives at `Type u` where `Atom : Type u`. The completeness proof instantiates at
`H = BrouwerianLindenbaumAlgebra`, which should be at the same universe. This parallels
the GHA case and should work with `BrouwerianValid.{u, u}`.

## 6. Estimated Complexity

- **Soundness**: ~60 lines (5 axiom cases, derivation-level induction, derivable wrapper)
- **Lindenbaum construction**: ~250 lines (equivalence relation, setoid, quotient, operations,
  congruence, all BrouwerianSemilattice axioms). Simpler than HilbertLindenbaum (~500 lines)
  because no join operation.
- **Truth lemma + completeness**: ~80 lines
- **Total**: ~400 lines

## 7. Recommendations

1. **Follow the HilbertLindenbaum.lean template closely** for naming and structure
2. **Import HilbertLindenbaum.lean** to reuse `hilbertCutSingletonDeriv` and friends
3. **Restrict the truth lemma to IsOrBotFree** formulas
4. **State the completeness theorem with the IsOrBotFree hypothesis**
5. **Use explicit ConjImpAxiom witnesses** (`.mem_implyK`, `.mem_implyS`, `.andI`, `.andE1`,
   `.andE2`) throughout rather than a typeclass
6. **Mark the entire section `noncomputable`** following the HilbertLindenbaum pattern
7. **Use `@[expose] public section`** for module-level visibility following CSLib convention
