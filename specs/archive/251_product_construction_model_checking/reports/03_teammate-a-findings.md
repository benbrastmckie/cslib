# Teammate A Findings: Product Construction and Model Checking — Primary Approach

## Summary

This report covers the primary implementation approach for the LTS × NBA product construction
and the LTL model checking reduction theorem. All infrastructure has been examined in detail.
No prior implementation exists for the LTS × NBA product; everything must be built fresh.

---

## Key Findings

### 1. What the LTS × NBA Product Means in Lean 4 Terms

The mathematical definition (Baier-Katoen Def. 4.62, p. 200) is:

Given a transition system `TS = (S, Act, →, I, AP, L)` (no terminal states) and an NBA
`A = (Q, 2^AP, δ, Q₀, F)` (nonblocking), the product `TS ⊗ A` has:

- **States**: `S × Q`
- **Transitions**: `(s,q) →α (t,p)` iff `s →α t` in TS and `q →[L(t)] p` in A
  (the NBA reads the LABEL of the TARGET state after the transition)
- **Initial states**: `{(s₀, q) | s₀ ∈ I, ∃ q₀ ∈ Q₀, q₀ →[L(s₀)] q}`
  (read initial state label to step into NBA before the first system transition)
- **Accept states**: `S × F` (pairs whose second component is in F)

**CRITICAL subtlety**: In the product, the NBA reads `L(t)` (the label of the *destination* state
after the transition), not `L(s)` (the source). This is the standard Baier-Katoen convention.
The initial states also involve a preliminary NBA step reading `L(s₀)`.

### 2. CSLib Type Alignment

The CSLib `LTS State Label` type has `Tr : State → Label → State → Prop`. The NBA in CSLib is
`NA.Buchi State Symbol` which extends `NA State Symbol` (which extends `LTS State Symbol` with a
`start : Set State` field) and adds `accept : Set State`.

The NBA's `Tr : State → Symbol → State → Prop` has the same shape as LTS. The product must be an
`NA.Buchi (S × Q) Act` (or just an `LTS (S × Q) Act`) where:

```lean
-- The product NBA Tr
Tr (s, q) α (t, p) := lts.Tr s α t ∧ nba.Tr q (labeling t) p
```

where `labeling : LTSState → (Atom → Prop)` is the labeling function connecting LTS states
to NBA alphabet elements.

**The alphabet mismatch**: The NBA alphabet is `Set Atom` (or `Atom → Prop` in CSLib's treatment).
The LTS labels are action labels `Act` (separate from atoms). The product transition system
uses Act as its action label type. The NBA steps are driven by the labeling of LTS states, not
by LTS action labels.

### 3. The Labeling Function — The Core Connection

`SatisfiesExec` in `OmegaExecutionSatisfies.lean` already establishes the pattern:

```lean
def SatisfiesExec (labeling : State → (Atom → Prop))
    (ss : ωSequence State) (φ : Formula Atom) : Prop :=
  Satisfies (fun p s => labeling s p) ss φ
```

The labeling function `labeling : State → (Atom → Prop)` maps LTS states to truth assignments
over atoms. This is exactly what connects the LTS to the NBA alphabet.

For the product construction:
- The NBA alphabet is `Atom → Prop` (or equivalently `Set Atom` where `Fintype Atom`)
- The labeling function provides the NBA input symbol for each LTS state

### 4. What Already Exists vs. What Must Be Built

**Reuse (directly available)**:
- `LTS State Label` — the LTS type (`Basic.lean`)
- `LTS.OmegaExecution ss μs` — infinite runs (`OmegaExecution.lean`)
- `NA.Buchi State Symbol` — the NBA type (`NA/Basic.lean`)
- `NA.Buchi.HasReachableAcceptingCycle` and `language_nonempty_iff` — emptiness (`Emptiness.lean`)
- `SatisfiesExec labeling ss φ` — the LTS → LTL bridge (`OmegaExecutionSatisfies.lean`)
- `OmegaExecution.flatten_mTr`, `OmegaExecution.append` — for building accepting runs

**Must Build (completely new)**:
- `LTS.productWithNBA` (or `Cslib.Automata.NA.Buchi.productWithLTS`) — the product construction
  as an `NA.Buchi (LTSState × NBAState) Act`
- `productWithNBA_run_iff` — characterizing runs of the product in terms of components
- `modelChecking_reduction` — the main theorem connecting M ⊨ φ to emptiness of the product
- Supporting lemmas: projection of product runs, lifting of LTS runs to product runs

**The NBA × NBA product in `NA/Prod.lean` is NOT reusable** — it synchronizes two NBAs on
the *same* symbol stream. The LTS × NBA product has asymmetric input: the LTS drives the
actions, and the NBA reads the derived labeling. This is a fundamentally different construction.

**The FLTS product in `FLTS/Prod.lean` is NOT reusable** — it takes two FLTSs with the same
label type and returns a product FLTS. The LTS × NBA product returns an NBA, not an FLTS.

### 5. The Precise Model Checking Statement

Following Baier-Katoen Theorem 4.63 and Vardi 1996 Section 4.2, the reduction theorem should state:

```lean
theorem modelChecking_reduction
    {LTSState NBAState Atom Act : Type*}
    (lts : LTS LTSState Act)
    (init : Set LTSState)
    (labeling : LTSState → (Atom → Prop))
    (nba : NA.Buchi NBAState (Atom → Prop))
    (φ : Formula Atom) :
    -- M satisfies φ iff the product with NBA for ¬φ has empty language
    (∀ ss : ωSequence LTSState,
      ss 0 ∈ init →
      lts.OmegaExecution ss (some stream) →
      SatisfiesExec labeling ss φ) ↔
    (productWithNBA lts init labeling nba).language = ⊥
```

However, the *exact* statement depends on two choices:

**Choice A (Cleaner)**: State the theorem directly in terms of omega-executions:

```lean
-- M ⊭ φ iff ∃ an accepting run of the product
¬(∀ ss μs, ss 0 ∈ init → lts.OmegaExecution ss μs →
    SatisfiesExec labeling ss φ) ↔
  (productWithNBA lts init labeling nba).HasReachableAcceptingCycle
```

This avoids needing task 242 (LTL-to-NBA) and works for any NBA A where `language(A) = L(¬φ)`.

**Choice B (Full theorem)**: Require `language(nba) = (Formula.neg φ).omegaLanguage`. This
introduces a dependency on task 242. For now, Choice A is preferred — the theorem remains
parameterized over any NBA A with the right language property, passed as a hypothesis.

### 6. Proof Strategy for the Reduction

The proof follows Baier-Katoen Theorem 4.63 proof (two directions):

**Forward (soundness / contrapositive)**:
If there is an accepting run of `product`, project it to get:
- An omega-execution `ss` in the LTS starting from `init`
- An accepting run `qs` of NBA starting from `start`
- Such that `qs 0 ∈ nba.start` and `∀ i, nba.Tr (qs i) (labeling (ss (i+1))) (qs (i+1))`
- The run `qs` is accepting: `∃ᶠ k, qs k ∈ nba.accept`
- Hence `labeling ∘ ss ∈ language(nba)`, meaning `SatisfiesExec labeling ss (¬φ)` holds

**Backward (completeness)**:
Given an omega-execution `ss` with `SatisfiesExec labeling ss (¬φ)`:
- The sequence `(labeling ∘ ss).tail` (shifting because NBA reads L of target) is in `language(nba)`
- Get an accepting NBA run `qs` for this sequence
- Pair `(ss, qs)` to form a valid product run
- The accepting states of the product are `S × nba.accept`, hit infinitely often

### 7. Product Transition Relation — Key Design Decision

There are two choices for the product transition relation:

**Option 1 (reads L(target), standard for Baier-Katoen)**:
```lean
Tr (s, q) α (t, p) := lts.Tr s α t ∧ nba.Tr q (labeling t) p
```
Initial states: `{(s₀, q) | s₀ ∈ init ∧ q₀ ∈ nba.start ∧ nba.Tr q₀ (labeling s₀) q}`

**Option 2 (reads L(source), alternative)**:
```lean
Tr (s, q) α (t, p) := lts.Tr s α t ∧ nba.Tr q (labeling s) p
```
Initial states: `{(s₀, q₀) | s₀ ∈ init ∧ q₀ ∈ nba.start}`

Option 1 is more standard in the literature but requires the preliminary NBA step at initial
states. Option 2 is simpler to define but shifts semantics by one step.

**Recommendation**: Use Option 1 (standard Baier-Katoen Def. 4.62) because it aligns with
the standard treatment. The `SatisfiesExec` definition reads atoms at `ss.head` (position 0),
and the NBA accepting language includes that initial step.

For `OmegaExecutionSatisfies`, `SatisfiesExec labeling ss φ` evaluates `φ` at `ss 0` using
`labeling (ss 0)`. The NBA run for the trace should start by reading `labeling (ss 0)`, which
aligns with the initial step in Option 1.

### 8. File Structure Recommendation

Two new files should be created:

**File 1**: `Cslib/Logics/LTL/Semantics/LTSProduct.lean`
- Imports: `OmegaExecutionSatisfies`, `Cslib.Computability.Automata.NA.Basic`
- Defines: `LTS.productWithNBA` (returns `NA.Buchi (LTSState × NBAState) Act`)
- Key lemmas: `productWithNBA_run_iff`, `productWithNBA_initial_iff`, `productWithNBA_accept_iff`
- Run projection lemmas: `productWithNBA_proj_lts`, `productWithNBA_proj_nba`
- Run lifting lemma: `productWithNBA_lift`

**File 2**: `Cslib/Logics/LTL/Semantics/ModelChecking.lean`
- Imports: `LTSProduct`, `Cslib.Computability.Automata.NA.Emptiness`
- Defines: The notion of an LTS satisfying an LTL formula:
  `def LTS.SatisfiesLTL (lts : LTS S Act) (init : Set S) (labeling : S → Atom → Prop) (φ : Formula Atom) : Prop`
- Main theorem: `modelChecking_iff` — M ⊨ φ ↔ L(M ⊗ A_¬φ) = ∅

**Alternative**: `ModelChecking.lean` can be in `Cslib/Logics/LTL/` directly.

### 9. Key Proof Obligations

1. `productWithNBA_run_iff`: A run of the product is equivalent to a synchronized pair of runs
2. `productWithNBA_proj_lts`: The LTS component of a product run is a valid LTS omega-execution
3. `productWithNBA_proj_nba`: The NBA component of a product run is a valid NBA run (for the labeling-derived symbol stream)
4. `productWithNBA_lift`: A valid LTS execution + NBA run → product run
5. `modelChecking_iff`: The main biconditional (two directions, using the above lemmas + `language_nonempty_iff` from Emptiness.lean)

### 10. Dependency on Task 242

Task 251 (this task) is **independent of task 242** if stated generically:
"For any NBA A with `language A = neg_φ_language`, M ⊨ φ ↔ L(M ⊗ A) = ∅"

The full end-to-end theorem "M ⊨ φ ↔ L(M ⊗ A_¬φ) = ∅" where `A_¬φ` is the Vardi-Wolper
NBA for ¬φ requires `Formula.isRegular` from task 242/the GNBA construction. But since
`Formula.isRegular` already exists in `OmegaRegular.lean`, a specialized version can be
written directly using `Formula.gnbaNBA (Formula.imp φ Formula.bot)`.

---

## Recommended Approach

### Phase 1: Define the Product Construction (`LTSProduct.lean`)

```lean
/-- The synchronous product of an LTS with an NBA over a labeling function.
The product is itself an NBA whose states are pairs (lts_state, nba_state).
The product transition reads the NBA symbol from the labeling of the *target* LTS state,
following Baier-Katoen Definition 4.62. -/
def LTS.productWithNBA
    (lts : LTS LTSState Act)
    (init : Set LTSState)
    (labeling : LTSState → (Atom → Prop))
    (nba : NA.Buchi NBAState (Atom → Prop)) :
    NA.Buchi (LTSState × NBAState) Act where
  -- Transition: LTS moves, NBA reads label of target state
  Tr sq α tq' := lts.Tr sq.1 α tq'.1 ∧ nba.Tr sq.2 (labeling tq'.1) tq'.2
  -- Initial states: LTS starts in init, NBA makes first step reading label of initial LTS state
  start := { sq | sq.1 ∈ init ∧ ∃ q₀ ∈ nba.start, nba.Tr q₀ (labeling sq.1) sq.2 }
  -- Accepting: second component in nba.accept
  accept := Set.univ ×ˢ nba.accept
```

**Alternative initial states formulation** (simpler, reads L(source) at step 0):
```lean
  start := init ×ˢ nba.start
```
With transition `Tr (s, q) α (t, p) := lts.Tr s α t ∧ nba.Tr q (labeling s) p`.

This "reads source" convention is mathematically equivalent after a one-step shift and may
be easier to prove. **Recommend starting with the "reads source" convention** and checking
against `SatisfiesExec` which reads `ss.head` (the source).

### Phase 2: Prove the Run Characterization

```lean
theorem productWithNBA_run_iff
    {lts : LTS LTSState Act} {init : Set LTSState}
    {labeling : LTSState → (Atom → Prop)}
    {nba : NA.Buchi NBAState (Atom → Prop)}
    {xs : ωSequence Act} {sqs : ωSequence (LTSState × NBAState)} :
    (lts.productWithNBA init labeling nba).Run xs sqs ↔
      sqs.map Prod.fst 0 ∈ init ∧
      lts.OmegaExecution (sqs.map Prod.fst) xs ∧
      (sqs.map Prod.snd) 0 ∈ nba.start ∧
      ∀ i, nba.Tr (sqs.map Prod.snd i) (labeling (sqs.map Prod.fst i)) (sqs.map Prod.snd (i+1))
```

### Phase 3: Prove the Model Checking Theorem

Using the run characterization and `NA.Buchi.language_nonempty_iff`:

```lean
theorem modelChecking_iff
    {LTSState NBAState Atom Act : Type*} [Finite NBAState] [Inhabited Act]
    (lts : LTS LTSState Act)
    (init : Set LTSState)
    (labeling : LTSState → (Atom → Prop))
    (nba : NA.Buchi NBAState (Atom → Prop))
    (φ : Formula Atom)
    (h_language : language nba = (Formula.imp φ Formula.bot).omegaLanguage) :
    (∀ ss : ωSequence LTSState, ∀ μs : ωSequence Act,
      ss 0 ∈ init → lts.OmegaExecution ss μs →
      SatisfiesExec labeling ss φ) ↔
    language (lts.productWithNBA init labeling nba) = ⊥
```

---

## Evidence from Literature

**Baier-Katoen Definition 4.62** (p. 200): Defines `TS ⊗ A` exactly as above. The proof of
Theorem 4.63 (pp. 200-202) establishes that checking `Traces(TS) ∩ Lω(A) = ∅` reduces to
checking whether accept states in the product are visited infinitely often — exactly
`language_nonempty_iff` from Emptiness.lean in CSLib.

**Vardi 1996 Section 4.2** (p. 884-888 in the markdown): States the verification problem and
reduction: construct the intersection automaton `L(AP) ∩ L(A_¬φ)` and check emptiness.
In CSLib terms, this is the product construction.

**Key quote from Vardi 1996**: "A finite-state program P = (W, w₀, R, V) can be viewed as a
Büchi automaton AP = (Σ, W, {w₀}, δ, W), where Σ = 2^Prop and s' ∈ δ(s, a) iff (s,s') ∈ R
and a = V(s)." — This tells us the LTS-to-NBA view: the LTS itself is an NBA over the alphabet
of truth assignments (with all states accepting). The product is then NBA intersection.

---

## Confidence Level

**High confidence** on:
- Infrastructure reuse: LTS, NA.Buchi, OmegaExecution, SatisfiesExec, Emptiness are all exactly
  what's needed
- Product definition: the transition rule and accept states are clear
- The "reads source" vs "reads target" distinction requires careful alignment with SatisfiesExec

**Medium confidence** on:
- Exact initial state formulation (reads source vs reads target — needs testing with simp/aesop)
- Whether `SatisfiesExec labeling ss φ` aligns perfectly with the product's accepting runs
  without an off-by-one shift in state indexing

**Low concern** (expected to be routine):
- Projection and lifting lemmas for product runs
- These follow the same pattern as `iProd_run_iff` in `NA/Prod.lean`

**Potential blocker** (LOW RISK):
- If the NBA alphabet is `Atom → Prop` (a non-`Fintype` type), `language_nonempty_iff` from
  Emptiness.lean requires `[Inhabited Symbol]` but NOT `Finite Symbol`. So this should be fine.
- The `[Finite NBAState]` hypothesis is needed for the forward direction of `language_nonempty_iff`.

---

## Literature Proof Structure

Following Baier-Katoen Theorem 4.63:

1. **Lemma 1 (product run characterization)**: (s,q) sequence is a product run iff s is an
   LTS execution and q is an NBA run for the `labeling ∘ s` symbol sequence

2. **Lemma 2 (projection)**: From any accepting product run `(ss, qs)`:
   - `ss` is an LTS execution starting in `init`
   - `qs` is an NBA run for `labeling ∘ ss`
   - `qs` is accepting (visits `nba.accept` infinitely often)
   - Hence `labeling ∘ ss ∈ language(nba)`, i.e., `SatisfiesExec labeling ss (¬φ)`

3. **Lemma 3 (lifting)**: From any LTS execution `ss` with `SatisfiesExec labeling ss (¬φ)`:
   - There exists an accepting NBA run `qs` for `labeling ∘ ss`
   - Pair `(ss, qs)` is a valid accepting product run
   - Hence `language(product) ≠ ⊥`

4. **Theorem (main)**: Chain Lemmas 2+3 with `language_nonempty_iff` to get the biconditional

**Lean-specific translation considerations**:
- Step 2 uses `OmegaExecution.extract_mTr` to show `qs 0 ∈ nba.start` and transitions hold
- Step 3 uses `NA.Run` to unpack the accepting NBA run, then `ωSequence.map Prod.snd` to project
- The "infinitely often" condition uses `∃ᶠ k in atTop, ...` (Filter.frequently) — matches
  the Buchi acceptance in CSLib (`NA.Buchi.Accepts`)
