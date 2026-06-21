# Teammate A Findings: DBA Constructions in CSLib

## Key Findings

- CSLib's DA infrastructure is at `Cslib/Computability/Automata/DA/` (not `Cslib/Computability/DA/` as referenced in some prior documents). Core types: `DA`, `DA.Buchi`, `DA.Muller`, `DA.FinAcc`, `DA.prod`, with `DA.run` producing `ωSequence State`.
- A critical missing lemma is `DA.prod_run_eq`: the product DA's run projects to component runs. The finite-word version `DA.prod_mtr_eq` exists but there is no omega-level analog. This is needed for both union and intersection proofs.
- The NBA intersection in `NA/BuchiInter.lean` uses a `Bool`-indexed product with history state (counter) via `addHist`, operating on nondeterministic automata. The DBA intersection must be rebuilt from scratch for deterministic automata since the DA type uses `FLTS` (functional transitions), not `LTS` (relational transitions).
- CSLib has NO strongly connected component (SCC) or "loop" infrastructure. Mathlib has `Quiver.StronglyConnectedComponent` but CSLib's `FLTS`/`DA` do not implement the `Quiver` typeclass. Landweber's Theorem therefore requires new definitions for "loop" and "superloop" over DA transition graphs.
- The complement non-closure proof is essentially free: `IsRegular.not_da_buchi` already proves the witness (`eventuallyZero` is omega-regular but not DBA-recognizable), and we just need to exhibit a DBA for the complement direction ("infinitely many 1s" is trivially DBA-recognizable).

## 1. CSLib DBA Infrastructure Analysis

### 1.1 Core Types and Definitions

**File**: `Cslib/Computability/Automata/DA/Basic.lean`

```lean
-- Deterministic automaton: FLTS + start state
structure DA (State Symbol : Type*) extends FLTS State Symbol where
  start : State

-- Infinite run (produces ωSequence State)
def DA.run (da : DA State Symbol) (xs : ωSequence Symbol) : ωSequence State := da.run' xs

-- Key simp lemmas
@[simp] theorem run_zero : da.run xs 0 = da.start
@[simp] theorem run_succ : da.run xs (n + 1) = da.tr (da.run xs n) (xs n)
@[simp] theorem mtr_extract_eq_run : da.mtr da.start (xs.extract 0 n) = da.run xs n

-- Deterministic Buchi automaton
structure DA.Buchi (State Symbol : Type*) extends DA State Symbol where
  accept : Set State

-- Acceptance: visiting accept infinitely often
instance : ωAcceptor (Buchi State Symbol) Symbol where
  Accepts a xs := ∃ᶠ k in atTop, a.run xs k ∈ a.accept

-- Deterministic Muller automaton  
structure DA.Muller (State Symbol : Type*) extends DA State Symbol where
  accept : Set (Set State)

-- Acceptance: infOcc of run is in accept family
instance : ωAcceptor (Muller State Symbol) Symbol where
  Accepts a xs := (a.run xs).infOcc ∈ a.accept

-- Finite acceptance (DFA-like)
structure DA.FinAcc (State Symbol : Type*) extends DA State Symbol where
  accept : Set State
```

**Key observation**: `DA.Buchi` and `DA.Muller` both extend `DA`, NOT each other. They share the same `toDA` field. This means we can construct from a common `DA` base:

```lean
-- To create a Buchi from a DA:
DA.Buchi.mk da acc    -- where da : DA State Symbol, acc : Set State

-- To create a Muller from a DA:
DA.Muller.mk da acc   -- where da : DA State Symbol, acc : Set (Set State)
```

### 1.2 Product Construction

**File**: `Cslib/Computability/Automata/DA/Prod.lean`

```lean
def DA.prod (da1 : DA State1 Symbol) (da2 : DA State2 Symbol) : DA (State1 × State2) Symbol where
  toFLTS := da1.toFLTS.prod da2.toFLTS
  start := (da1.start, da2.start)

@[simp] theorem DA.prod_mtr_eq (da1 da2) (s : State1 × State2) (xs : List Symbol) :
    (da1.prod da2).mtr s xs = (da1.mtr s.fst xs, da2.mtr s.snd xs)
```

**Critical gap**: No `prod_run_eq` for infinite runs. We need:

```lean
-- NEEDED (not yet in CSLib)
@[simp] theorem DA.prod_run_eq (da1 : DA State1 Symbol) (da2 : DA State2 Symbol)
    (xs : ωSequence Symbol) (n : ℕ) :
    (da1.prod da2).run xs n = (da1.run xs n, da2.run xs n)
```

Proof strategy: straightforward induction on `n`, using `run_zero` and `run_succ` and the definition of `FLTS.prod.tr`.

### 1.3 NBA Intersection Pattern (Counter Trick)

**File**: `Cslib/Computability/Automata/NA/BuchiInter.lean`

The NBA intersection uses a sophisticated architecture:

1. `NA.iProd` -- product of `Bool`-indexed automata producing `(Π i, State i)` states
2. `NA.addHist` -- adds a history state (the `Bool` counter) to track which accepting condition was last seen
3. `histTrans` -- the counter toggle logic: if `false` accepting condition met, flip to `true`; if `true` met, flip to `false`; otherwise hold
4. `interAccept` -- accepting states are the union `interAcc false acc ∪ interAcc true acc`

**Key structural difference for DBA**: The NBA version uses `LTS` (relational transitions) and `NA.Run` (existential witness for run). The DBA version uses `FLTS` (functional transitions) and `DA.run` (deterministic function). This means:
- We CANNOT directly instantiate the NBA intersection for DBAs
- We must build a new deterministic product-with-counter construction
- BUT the mathematical idea is identical: product state space with a `Fin 3` counter cycling through {wait for F1} -> {wait for F2} -> {signal and reset}

### 1.4 Relevant infOcc Infrastructure

**File**: `Cslib/Foundations/Data/OmegaSequence/InfOcc.lean`

```lean
def infOcc (xs : ωSequence α) : Set α := { x | ∃ᶠ k in atTop, xs k = x }

-- Key helper for finite types:
theorem frequently_in_finite_type [Finite α] {s : Set α} {xs : ωSequence α} :
    (∃ᶠ k in atTop, xs k ∈ s) ↔ ∃ x ∈ s, ∃ᶠ k in atTop, xs k = x
```

The `infOcc` definition is used in `DA.Muller` acceptance. For Landweber's Theorem, we need `infOcc` to characterize "loops" -- the set of infinitely recurring states in a DA run.

### 1.5 Existing Complement/Non-Closure Results

**File**: `Cslib/Computability/Languages/OmegaRegularLanguage.lean`

```lean
-- The witness language
def eventuallyZero : ωLanguage (Fin 2) := { xs | ∀ᶠ k in atTop, xs k = 0 }

-- eventuallyZero is NBA-recognizable
theorem eventuallyZero_accepted_by_na_buchi : language eventuallyZeroNa = eventuallyZero

-- eventuallyZero is NOT the omega-limit of any language
theorem eventuallyZero_not_omegaLim : ¬ ∃ l : Language (Fin 2), l↗ω = eventuallyZero

-- DBA language = omega-limit (so eventuallyZero cannot be DBA-recognized)
theorem buchi_eq_finAcc_omegaLim :
    language (Buchi.mk da acc) = (language (FinAcc.mk da acc))↗ω

-- Main non-existence result
theorem IsRegular.not_da_buchi :
    ∃ (Symbol : Type) (p : ωLanguage Symbol), p.IsRegular ∧
      ¬ ∃ (State : Type) (da : DA.Buchi State Symbol), language da = p
```

## 2. Proposed Constructions: Exact Lean 4 Signatures

### 2.1 DBA Product Run Lemma (Prerequisite)

**File**: `Cslib/Computability/Automata/DA/Prod.lean` (extend existing file)

**Imports needed**: No new imports (already has DA.Basic and FLTS.Prod)

```lean
/-- The run of the product DA projects to the component DA runs. -/
@[simp, scoped grind =]
theorem prod_run_eq (da1 : DA State1 Symbol) (da2 : DA State2 Symbol)
    (xs : ωSequence Symbol) (n : ℕ) :
    (da1.prod da2).run xs n = (da1.run xs n, da2.run xs n) := by
  induction n with
  | zero => simp [prod]
  | succ n ih => simp [prod, ih]
```

**Proof strategy**: Direct induction on `n`. Base case: both sides are `(da1.start, da2.start)`. Inductive step: unfold `run_succ` and `FLTS.prod.tr`, apply IH.

**Confidence**: High -- this is a straightforward equational lemma.

### 2.2 DBA Union

**File**: `Cslib/Computability/Automata/DA/BuchiClosure.lean` (new file)

**Imports needed**:
- `Cslib.Computability.Automata.DA.Prod`
- `Cslib.Computability.Automata.DA.Basic`

```lean
/-- The union of two deterministic Buchi automata. The product automaton accepts
if either component visits its accepting states infinitely often. -/
@[scoped grind =]
def DA.Buchi.union (a₁ : DA.Buchi State1 Symbol) (a₂ : DA.Buchi State2 Symbol) :
    DA.Buchi (State1 × State2) Symbol where
  toDA := a₁.toDA.prod a₂.toDA
  accept := (a₁.accept ×ˢ Set.univ) ∪ (Set.univ ×ˢ a₂.accept)

/-- The language of the union DBA is the union of the component languages. -/
@[simp, scoped grind =]
theorem DA.Buchi.union_language_eq {a₁ : DA.Buchi State1 Symbol} {a₂ : DA.Buchi State2 Symbol} :
    ωAcceptor.language (a₁.union a₂) = ωAcceptor.language a₁ ⊔ ωAcceptor.language a₂
```

**Proof strategy**:

The proof of `union_language_eq` requires showing:
```
∃ᶠ k in atTop, (da₁.run xs k, da₂.run xs k) ∈ (F₁ × univ) ∪ (univ × F₂)
↔ (∃ᶠ k in atTop, da₁.run xs k ∈ F₁) ∨ (∃ᶠ k in atTop, da₂.run xs k ∈ F₂)
```

- Forward direction: Use `Filter.frequently_or_distrib` -- if a disjunction happens frequently, at least one disjunct happens frequently. Membership in `(F₁ × univ) ∪ (univ × F₂)` is exactly `fst ∈ F₁ ∨ snd ∈ F₂`.
- Backward direction: If `∃ᶠ k, run₁ k ∈ F₁`, then `∃ᶠ k, (run₁ k, run₂ k) ∈ F₁ × univ ⊆ accept`. Similarly for the other disjunct.
- Both directions use `prod_run_eq` to decompose the product run.

**Confidence**: High -- clean application of `frequently_or_distrib` and set membership.

### 2.3 DBA Intersection

**File**: `Cslib/Computability/Automata/DA/BuchiClosure.lean` (same file as union)

**Imports needed**: Additionally need `Cslib.Foundations.Data.OmegaSequence.Temporal` (for the `LeadsTo`/temporal reasoning used in BuchiInter proof pattern)

```lean
/-- The counter transition for DBA intersection. Cycles through states:
- 0: waiting for a₁.accept
- 1: waiting for a₂.accept  
- 2: both seen, signal acceptance and reset -/
@[scoped grind =]
def DA.Buchi.interCounterTr (a₁ : DA.Buchi State1 Symbol) (a₂ : DA.Buchi State2 Symbol)
    (s₁ : State1) (s₂ : State2) (c : Fin 3) : Fin 3 :=
  match c with
  | 0 => if s₁ ∈ a₁.accept then 1 else 0
  | 1 => if s₂ ∈ a₂.accept then 2 else 1
  | 2 => if s₁ ∈ a₁.accept then 1 else 0

/-- The intersection of two deterministic Buchi automata using the counter trick. -/
@[scoped grind =]
noncomputable def DA.Buchi.inter (a₁ : DA.Buchi State1 Symbol) (a₂ : DA.Buchi State2 Symbol) :
    DA.Buchi (State1 × State2 × Fin 3) Symbol where
  tr := fun (s₁, s₂, c) x =>
    let s₁' := a₁.tr s₁ x
    let s₂' := a₂.tr s₂ x
    (s₁', s₂', interCounterTr a₁ a₂ s₁' s₂' c)
  start := (a₁.start, a₂.start, 0)
  accept := Set.univ ×ˢ Set.univ ×ˢ {(2 : Fin 3)}

/-- The language of the intersection DBA is the intersection of the component languages. -/
theorem DA.Buchi.inter_language_eq {a₁ : DA.Buchi State1 Symbol} {a₂ : DA.Buchi State2 Symbol} :
    ωAcceptor.language (a₁.inter a₂) = ωAcceptor.language a₁ ⊓ ωAcceptor.language a₂
```

**Proof strategy**:

This is significantly harder than the union case. The proof must show:

- Forward: If the counter hits 2 infinitely often, then between consecutive hits of 2, both F₁ and F₂ were visited. Since the counter cycles 0 -> 1 -> 2 -> 0, hitting 2 infinitely often means both accepting conditions are met infinitely often.
- Backward: If both accepting conditions hold infinitely often, the counter must cycle through all three states infinitely often (since from state 0 it will eventually see F₁ and advance to 1, from 1 it will eventually see F₂ and advance to 2).

The proof pattern follows the temporal reasoning in `NA/BuchiInter.lean` but adapted for deterministic runs. Key Mathlib/CSLib lemmas:
- `Filter.frequently_atTop` for extracting witnesses
- The temporal `LeadsTo` infrastructure from `OmegaSequence/Temporal.lean`
- `until_frequently_not_leadsTo` and `until_frequently_leadsTo_and`

**Note on `noncomputable`**: The counter transition uses `if s₁ ∈ a₁.accept` which requires `Decidable` membership. We can either add `[DecidablePred a₁.accept]` or use `noncomputable` + `open scoped Classical`.

**Alternative approach**: Instead of `Fin 3`, we could use `Bool` as in the NBA version (toggling between "waiting for F₁" and "waiting for F₂"). The `Bool` approach is simpler but slightly less standard. The `Fin 3` approach with the explicit "signal" state matches Thomas 2003 Ch.1 more closely.

**Confidence**: Medium -- the construction is clear but the proof of language equality requires careful temporal reasoning. The NA/BuchiInter proof is 130+ lines and the DBA version should be comparable or slightly simpler (deterministic runs avoid existential witnesses).

### 2.4 DBA Complement Non-Closure

**File**: `Cslib/Computability/Automata/DA/BuchiClosure.lean` (same file)

```lean
/-- The complement of "infinitely many 1s" over {0,1} is "eventually zero", which is
the standard witness that DBAs are not closed under complement. -/
def DA.Buchi.infOftenOne : DA.Buchi (Fin 2) (Fin 2) where
  tr s _ := s          -- identity transition (any transition works for this 1-state witness)
  start := 0
  accept := {(1 : Fin 2)}  -- this needs thought -- see below

/-- DBAs are not closed under complement: there exists a DBA-recognizable language
whose complement is not DBA-recognizable. -/
theorem DA.Buchi.not_closed_complement :
    ∃ (Symbol : Type) (L : ωLanguage Symbol),
      (∃ (S : Type) (a : DA.Buchi S Symbol), ωAcceptor.language a = L) ∧
      ¬ ∃ (S : Type) (a : DA.Buchi S Symbol), ωAcceptor.language a = Lᶜ
```

**Proof strategy**:

The witness language is `L = (eventuallyZero)ᶜ = {xs | ∃ᶠ k in atTop, xs k = 1}` (infinitely many 1s over `Fin 2`).

Step 1: Show `L` is DBA-recognizable by constructing a simple 2-state DBA:
```
State 0: non-accepting
State 1: accepting  
Transition: δ(s, 0) = 0, δ(s, 1) = 1
Accept: {1}
```
This DBA visits state 1 infinitely often iff the input has infinitely many 1s.

Step 2: Show `Lᶜ = eventuallyZero` is NOT DBA-recognizable. This follows directly from `IsRegular.not_da_buchi`, which proves `¬ ∃ (State : Type) (da : DA.Buchi State (Fin 2)), language da = eventuallyZero`.

Key reuse: We need to connect `Lᶜ = eventuallyZero`. The complement of "infinitely many 1s" is "eventually all 0s" which is exactly `eventuallyZero`. This requires:
```lean
(∃ᶠ k in atTop, xs k = 1)ᶜ = (∀ᶠ k in atTop, xs k = 0)
```
which follows from `Filter.not_frequently` and `Fin.eq_zero_or_one`.

**Confidence**: High -- almost entirely reuses existing CSLib infrastructure. The witness DBA is trivial, and the non-recognizability of the complement is already proved.

### 2.5 Landweber Characterization (Theorem 3.32)

**File**: `Cslib/Computability/Automata/DA/Landweber.lean` (new file)

**Imports needed**:
- `Cslib.Computability.Automata.DA.Basic`
- `Cslib.Foundations.Data.OmegaSequence.InfOcc`

#### New Definitions Required

```lean
/-- A set of states S is a *loop* in a DA if S is nonempty and every state in S
can reach every other state in S via the transition function. -/
def DA.IsLoop (da : DA State Symbol) (S : Set State) : Prop :=
  S.Nonempty ∧ ∀ s ∈ S, ∀ s' ∈ S, ∃ w : List Symbol, da.mtr s w = s' ∧
    ∀ i < w.length, da.mtr s (w.take (i + 1)) ∈ S  -- stays within S

/-- Simplified version: a loop is a nonempty set where every pair is mutually reachable.
(Without the "staying within S" constraint -- just reachability.) -/
def DA.IsLoop' (da : DA State Symbol) (S : Set State) : Prop :=
  S.Nonempty ∧ ∀ s ∈ S, ∀ s' ∈ S, ∃ w : List Symbol, w ≠ [] ∧ da.mtr s w = s'

/-- An acceptance family F is closed under superloops if for every loop S ∈ F
and every loop S' ⊇ S, also S' ∈ F. -/
def DA.Muller.ClosedUnderSuperloops (a : DA.Muller State Symbol) : Prop :=
  ∀ S ∈ a.accept, ∀ S', a.toDA.IsLoop S → a.toDA.IsLoop S' → S ⊆ S' → S' ∈ a.accept
```

**Note on Loop Definition**: Thomas defines "loop" as `S ≠ ∅ ∧ ∀s, s' ∈ S, ∃w ∈ Σ⁺, δ(s,w) = s'`. This is essentially a strongly connected subgraph in the DA's transition graph. The "staying within S" constraint is NOT part of Thomas's definition -- a loop only requires reachability, not that the intermediate states remain in S. So `IsLoop'` is the correct formalization.

However, Thomas also states that loops are exactly the sets that can occur as `Inf(ρ)` of some run. This connection to `infOcc` is crucial and should be proved as a lemma:

```lean
/-- A loop is exactly a set that occurs as the set of infinitely recurring states
of some run. -/
theorem DA.isLoop_iff_infOcc [Finite State] (da : DA State Symbol) (S : Set State) :
    da.IsLoop' S ↔ ∃ xs : ωSequence Symbol, (da.run xs).infOcc = S
```

#### Main Theorem Signature

```lean
/-- **Landweber's Theorem (part b)**: A Muller automaton's language is DBA-recognizable
iff its acceptance family is closed under superloops. -/
theorem DA.Muller.dba_recognizable_iff_closedUnderSuperloops
    [Finite State] (a : DA.Muller State Symbol) :
    (∃ acc : Set State, ωAcceptor.language (DA.Buchi.mk a.toDA acc) = ωAcceptor.language a) ↔
    a.ClosedUnderSuperloops
```

**Alternative formulation** (language-level):

```lean
/-- Language-level Landweber: an omega-regular language given by a DMA is DBA-recognizable
iff the acceptance family is closed under superloops. -/
theorem DA.Muller.language_eq_dba_iff_closedUnderSuperloops
    [Finite State] (a : DA.Muller State Symbol) :
    (∃ (S : Type) (_ : Finite S) (b : DA.Buchi S Symbol),
      ωAcceptor.language b = ωAcceptor.language a) ↔
    a.ClosedUnderSuperloops
```

**Note**: The first formulation requires the DBA to share the same underlying DA (same state space and transitions), which is stronger than the language-level equivalence. Thomas's proof of the forward direction (F = F₂ implies DBA-recognizable) constructs a DBA with state space `Q × 2^Q`, so it does NOT share the same state space. The second formulation is more faithful.

#### Proof Strategy (from Thomas 2003 Theorem 3.32)

**Forward direction** (F closed under superloops implies DBA-recognizable):

1. Construct a DBA `A'` with state set `Q × 2^Q` and start state `(q₀, ∅)`.
2. The second component `R` accumulates visited states: `R' := R ∪ {q'}` where `q' = δ(q, a)`.
3. When `R` becomes a loop that is a superset of some F-loop (i.e., `R ∈ F₂`), reset `R := ∅`. The accepting states are `{(q, ∅)}`.
4. `A'` accepts iff the reset happens infinitely often.
5. Key equivalence: resets happen infinitely often iff eventually the run cycles through states that form a superloop of some F-loop, which by closure under superloops means the infOcc is in F.

**Backward direction** (DBA-recognizable implies F closed under superloops):

1. Given DBA `B = (Q, Σ, q₀, δ, F_B)` recognizing `L(A)`, and a loop `S ∈ F`, and a superloop `S' ⊇ S`.
2. Pick `q ∈ S`, reached by `A` via some word `w`. Continue with `γ` such that `A` loops through `S` and hence accepts.
3. Since `B` accepts `wγ`, `B` visits `F_B` infinitely often. Pick the first visit after some prefix `wu₁`.
4. Continue via `v₁` through `S` back to `q`, then via `x₁` through the additional states of `S'` back to `q`.
5. Repeat: `wu₁v₁x₁u₂v₂x₂...` is accepted by `B` (since each `u_i` witnesses a visit to `F_B`) and makes `A` cycle through all of `S'`, so `S' ∈ F`.

**Estimated complexity**: 300-400 lines. The forward direction requires the accumulator DBA construction and a somewhat intricate argument about when resets occur. The backward direction is a pumping/composition argument.

**Dependencies**: Requires `DA.IsLoop'`, `ClosedUnderSuperloops`, and several helper lemmas about loops and infOcc.

**Confidence**: Medium-Low -- this is the most complex construction. The forward direction involves a non-trivial DBA construction with `2^Q` blowup, and the equivalence proof requires careful reasoning about eventual behavior. The backward direction is a clever pumping argument that is conceptually clear but technically involved to formalize.

## 3. Literature Proof Structure (Thomas 2003 Thm 3.32)

### Part (b): F = F₂ iff DBA-recognizable

**Definition of F₂**: `F₂ = F ∪ {F ∪ E | F ∪ E is a loop with at least one state more than F ∈ F}` = "F plus all proper superloops of F-loops". Equivalently, F is closed under superloops iff `F = F₂`.

**Forward (F = F₂ implies DBA-recognizable)**:

Step 1: State that `A` accepts `α` iff `A` eventually assumes a superloop of an F-loop on `α` (by definition of `F₂`).

Step 2: Construct DBA `A'` with state set `Q × 2^Q`, start `(q₀, ∅)`.
- Accumulate visited states in `R`
- When `R` becomes/contains a loop that is in `F₂`, reset `R := ∅`
- Accept states: `{(q, ∅)}`

Step 3: Show `A'` accepts `α` iff infinitely often the accumulator resets.

Step 4: Show this is equivalent to: for some `S' ⊇ S` with `S ∈ F`, precisely the states of `S'` are visited infinitely often.

Step 5: Since `F` is closed under superloops, this means `S' ∈ F`, so `A` accepts.

**Lean translation considerations**:
- Step 2 needs `[Finite State]` to make `Set State` finite (for the powerset component) and `[DecidableEq State]` for set membership
- The "check if R contains an F₂-loop" is a decidable predicate on finite sets
- The accumulator reset logic requires careful formalization of the finite-word intermediate steps

**Backward (DBA-recognizable implies F = F₂)**:

Step 1: Given DBA `B` with final states `F_B` recognizing `L(A)`.

Step 2: Take `S ∈ F` and `S' ⊇ S` a loop.

Step 3: Find `q ∈ S` reached by `w`, and `γ` making `A` loop through `S` (so `A` accepts `wγ`).

Step 4: Since `B` accepts `wγ`, it visits `F_B` infinitely often. After prefix `wu₁`, `B` is in some final state.

Step 5: Continue via `v₁` through `S` back to `q`, then via `x₁` through the `S' \ S` states back to `q`.

Step 6: Repeat to get `wu₁v₁x₁u₂v₂x₂...` which `B` accepts (visiting `F_B` after each `u_i`) and which makes `A` visit all of `S'` infinitely often.

Step 7: Therefore `Inf(run_A) = S'`, so `S' ∈ F`.

**Lean translation considerations**:
- Steps 3-5 require reasoning about finite paths in the DA transition graph
- Step 6 requires constructing an omega-word from infinitely many finite segments -- this connects to `ωSequence.flatten`
- Step 7 requires connecting `infOcc` of the constructed run to `S'`

## 4. Reuse Check Results

### Found in CSLib (reusable)

| Component | Location | Usage |
|-----------|----------|-------|
| `DA.prod` | `DA/Prod.lean` | Base for union/intersection product construction |
| `DA.prod_mtr_eq` | `DA/Prod.lean` | Finite-word product decomposition (extend to omega) |
| `infOcc` | `InfOcc.lean` | Infinite occurrence tracking for Muller/Landweber |
| `frequently_in_finite_type` | `InfOcc.lean` | Pigeonhole for finite state spaces |
| `eventuallyZero_not_omegaLim` | `ExampleEventuallyZero.lean` | Complement non-closure witness |
| `IsRegular.not_da_buchi` | `OmegaRegularLanguage.lean` | Complement non-closure main result |
| `buchi_eq_finAcc_omegaLim` | `DA/Buchi.lean` | DBA = omega-limit characterization |
| `Filter.frequently_or_distrib` | Mathlib | Union proof: frequently of disjunction |
| `LeadsTo`, `Step`, `until_frequently_*` | `Temporal.lean` | Temporal reasoning for intersection proof |

### Found in Mathlib (potentially reusable)

| Component | Location | Usage |
|-----------|----------|-------|
| `Quiver.StronglyConnectedComponent` | `Mathlib.Combinatorics.Quiver.ConnectedComponent` | SCC definition -- but requires Quiver instance for DA |
| `Quiver.stronglyConnectedSetoid` | Same | SCC equivalence relation |
| `Nat.exists_subseq_of_forall_mem_union` | `Mathlib.Order.OrderIsoNat` | Alternative to `frequently_or_distrib` for pigeonhole |

### Must be newly defined

| Component | Reason |
|-----------|--------|
| `DA.prod_run_eq` | Omega-level product run decomposition (simple extension of existing `prod_mtr_eq`) |
| `DA.IsLoop` / `DA.IsLoop'` | "Loop" (SCC) in DA transition graph -- CSLib has no SCC machinery |
| `DA.Muller.ClosedUnderSuperloops` | Superloop closure property for acceptance family |
| DBA intersection construction | Cannot reuse NBA version due to LTS vs FLTS mismatch |
| DBA union construction | New, but simple given `DA.prod` |
| Complement non-closure witness DBA | Simple 2-state DBA for "infinitely many 1s" |

### Not reusable (considered but rejected)

| Component | Reason |
|-----------|--------|
| `NA.Buchi.interNA` / `addHist` | Built on `LTS` (relational), not `FLTS` (functional). Cannot be instantiated for deterministic automata. |
| `Quiver.StronglyConnectedComponent` | Requires `Quiver` instance. DA's `FLTS` does not implement `Quiver` (it uses `State → Symbol → State`, not `State → State → Prop`). Creating a `Quiver` instance would require fixing a symbol, losing generality. Better to define `IsLoop` directly. |

## 5. Recommended Approach

### Priority Order

1. **`DA.prod_run_eq`** (prerequisite, ~10 lines) -- needed by both union and intersection
2. **DBA Union** (~80-120 lines) -- simplest construction, builds confidence
3. **DBA Complement Non-Closure** (~60-80 lines) -- high reuse, mostly connecting existing results
4. **DBA Intersection** (~150-200 lines) -- counter trick, harder but well-understood
5. **Landweber's Theorem** (~300-400 lines) -- most complex, requires new SCC infrastructure

### Dependencies

```
prod_run_eq ──→ DBA Union
           ──→ DBA Intersection
                      
(independent) ──→ DBA Complement Non-Closure

IsLoop + ClosedUnderSuperloops ──→ Landweber's Theorem
```

Items 1-4 are independent of Landweber. The first three can go in a single `BuchiClosure.lean` file. Landweber needs its own file with the new SCC definitions.

### Feasibility Assessment

- Items 1-3 are clearly feasible now with zero new infrastructure beyond `prod_run_eq`.
- Item 4 (intersection) is feasible but requires careful temporal reasoning -- the NBA intersection proof pattern provides a template.
- Item 5 (Landweber) is feasible with the literature proof as guide, but is the most labor-intensive. It may be appropriate to split into sub-phases: (a) define `IsLoop` and prove connection to `infOcc`, (b) prove forward direction, (c) prove backward direction.

## 6. Confidence Assessment

- **`prod_run_eq`**: HIGH -- trivial induction, ~10 lines
- **DBA Union**: HIGH -- clean product + pigeonhole argument, ~80-120 lines, `frequently_or_distrib` handles the hard part
- **DBA Complement Non-Closure**: HIGH -- almost entirely reuses existing results, ~60-80 lines
- **DBA Intersection**: MEDIUM -- counter trick is well-understood but the correctness proof requires temporal reasoning infrastructure; ~150-200 lines, follows NBA pattern
- **Landweber Theorem**: MEDIUM-LOW -- most substantial new contribution; requires new definitions (`IsLoop`, `ClosedUnderSuperloops`), powerset DBA construction, and careful pumping arguments; ~300-400 lines total; complete proof available in Thomas 2003
