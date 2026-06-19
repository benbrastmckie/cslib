# Research Report: Proving `gnba_language_eq` — GNBA/NBA Correctness

**Task**: 236 — Follow-up PRs from PR #649 (Büchi / omega-regular)
**Focus**: Complete proof strategy for `Formula.gnba_language_eq` (sorry at GNBA.lean:795)
**Session**: sess_1750345929_a1b2c3

---

## 0. Critical Bug: `gnbaNBA` Counter Advances Unconditionally

The cycling counter in `gnbaNBA` (GNBA.lean:656-663) always advances unconditionally:

```lean
Tr := fun ⟨B, i⟩ a ⟨B', j⟩ =>
  Formula.gnbaTr φ B a B' ∧
  (i.val + 1 = j.val ∨
   (j = ⟨0, Nat.succ_pos _⟩ ∧ i.val = Formula.gnbaK φ))
```

**Problem**: The counter transition `i+1 = j ∨ (j = 0 ∧ i = gnbaK)` always advances the
counter by 1 (wrapping at gnbaK). In ANY infinite run, the counter cycles
`0, 1, ..., gnbaK, 0, 1, ...` and visits counter=0 infinitely often. Every run is
Büchi-accepting regardless of GNBA acceptance sets. The NBA accepts
`L(GNBA transition system)`, not `L(GNBA)`. The theorem `gnba_language_eq` cannot be
proved with this definition.

### Standard Degeneralization (Baier-Katoen Lemma 4.56)

The correct cycling counter uses **conditional** advancement:

```
(B, i) →_a (B', j)  iff  B →_a B' in GNBA  and
  if B ∈ F_{accept_set(i)}   -- current state satisfies current acceptance set
    then j = (i + 1) mod k   -- advance counter
    else j = i               -- stay: waiting for acceptance set i
```

where `k = gnbaK φ` (number of Until subformulas = number of acceptance sets).

### Corrected Definition (Lean sketch)

```lean
noncomputable def Formula.gnbaNBA (φ : Formula Atom) :
    NA.Buchi (Formula.GNBANBAState φ) (Set Atom) where
  Tr := fun ⟨B, i⟩ a ⟨B', j⟩ =>
    Formula.gnbaTr φ B a B' ∧
    if h : Formula.gnbaK φ = 0 then
      j.val = 0
    else
      let idx : Fin (Formula.gnbaK φ) := ⟨i.val % Formula.gnbaK φ, Nat.mod_lt _ (by omega)⟩
      let χ := (Formula.untlFinset φ)[idx]
      if B ∈ Formula.gnbaAcceptSet φ χ then
        j.val = (i.val + 1) % (Formula.gnbaK φ)
      else
        j = i
  start := { s | s.1 ∈ Formula.gnbaStart φ ∧ s.2 = ⟨0, Nat.succ_pos _⟩ }
  accept := { s | s.2 = ⟨0, Nat.succ_pos _⟩ }
```

**State space consideration**: With `Fin (gnbaK φ).succ`, counter values range from
`0` to `gnbaK φ`. When `gnbaK φ = k > 0`, the counter values `0..k-1` correspond to
the k acceptance sets (mod k ensures this). When `gnbaK φ = 0`, there are no Until
subformulas, the GNBA has no acceptance constraints, and the counter stays at 0.

**This must be fixed before `gnba_language_eq` can be proved.**

---

## 1. Literature Sources

| Source | Content | Relevance |
|--------|---------|-----------|
| Baier-Katoen Ch.5, Def 5.37 | GNBA construction from LTL | Core definition reference |
| Baier-Katoen Ch.5, Thm 5.39 | GNBA language = LTL language | Correctness proof structure |
| Baier-Katoen Ch.4, Lem 4.56 | GNBA-to-NBA degeneralization | Counter cycling proof |
| Vardi-Wolper 1986 | Original automata-theoretic LTL→NBA | Historical reference |
| Schimpf-Merz-Smaus (TPHOLs 2009) | Isabelle/HOL formalization | Formalization precedent |
| AFP LTL_to_GBA (2014) | Isabelle Archive of Formal Proofs | Machine-checked reference |

---

## 2. Overall Proof Decomposition

The proof of `gnba_language_eq` decomposes into:

```
gnba_language_eq : language (gnbaNBA φ) = gnbaOmegaLanguage φ

  = gnba_completeness : gnbaOmegaLanguage φ ⊆ language (gnbaNBA φ)
  + gnba_soundness    : language (gnbaNBA φ) ⊆ gnbaOmegaLanguage φ
```

The completeness direction constructs an accepting NBA run from a satisfying valuation.
The soundness direction extracts satisfaction from an accepting NBA run.

Both directions go through the GNBA level:
- **Completeness**: satisfaction → GNBA accepting run → NBA accepting run
- **Soundness**: NBA accepting run → GNBA accepting run → satisfaction

---

## 3. Completeness: Satisfaction → NBA Accepting Run

### Goal

Given `v : ℕ → Set Atom` with `Satisfies (fun n p => p ∈ v n) 0 φ`, construct
`ss : ℕ → GNBANBAState φ` such that `gnbaNBA φ .Run v ss ∧ ∃ᶠ k in atTop, ss k ∈ accept`.

### Step C1: Canonical GNBA Run

Define `gnbaRun : ℕ → GNBAState φ`:
```
gnbaRun i := ⟨canonicalAtom (fun n p => p ∈ v n) i φ, canonicalAtom_isAtom ...⟩
```

**Already proved**:
- `canonicalAtom_isAtom` (GNBA.lean:449): canonical atom is a valid atom ✓
- `canonicalAtom_gnbaTr` (GNBA.lean:728): GNBA transitions hold along canonical run ✓

### Step C2: Start State

Need: `φ ∈ (gnbaRun 0).val`, i.e., `φ ∈ closure φ ∧ Satisfies v 0 φ`.
- First conjunct: `self_mem_closure φ` ✓
- Second conjunct: hypothesis `hsat` ✓

```lean
lemma canonicalAtom_mem_start (hsat : Satisfies v 0 φ) :
    ⟨canonicalAtom v 0 φ, canonicalAtom_isAtom v 0 φ⟩ ∈ gnbaStart φ :=
  canonicalAtom_mem_iff.mpr ⟨self_mem_closure φ, hsat⟩
```

### Step C3: GNBA Acceptance for Canonical Run

**Key new lemma**: For each Until subformula `χ = untl ψ₁ ψ₂` in `closure φ`:

```
∃ᶠ k in atTop, gnbaRun k ∈ gnbaAcceptSet φ χ
```

i.e., infinitely often, either `χ ∉ (gnbaRun k).val` or `ψ₂ ∈ (gnbaRun k).val`.

**Proof by contradiction**: Assume `¬(∃ᶠ k in atTop, P k)`, so `∀ᶠ k in atTop, ¬P k`.
This means: from some N onwards, `χ ∈ (gnbaRun k).val ∧ ψ₂ ∉ (gnbaRun k).val` for all k ≥ N.

By canonical atom definition:
- `χ ∈ (gnbaRun k).val` means `Satisfies v k (untl ψ₁ ψ₂)` for all k ≥ N
- In particular, `Satisfies v N (untl ψ₁ ψ₂)` gives `∃ j ≥ N, Satisfies v j ψ₂`
- So `ψ₂ ∈ (gnbaRun j).val` for this j ≥ N, contradicting `ψ₂ ∉ (gnbaRun j).val` ∎

**Lean approach**: Use `Filter.Frequently.filter_mono` or prove via
`frequently_atTop` ↔ `∀ N, ∃ k ≥ N, P k`. The contradiction uses `Satisfies`
unfolding and the canonical atom membership characterization.

### Step C4: Counter Sequence Construction (Degeneralization Backward)

Define the counter sequence `ctr : ℕ → Fin (gnbaK φ).succ` recursively:
```
ctr 0 := ⟨0, Nat.succ_pos _⟩
ctr (n+1) :=
  if gnbaK φ = 0 then ⟨0, ...⟩
  else
    let idx := ⟨(ctr n).val % gnbaK φ, ...⟩
    let χ := (untlFinset φ)[idx]
    if gnbaRun n ∈ gnbaAcceptSet φ χ then
      ⟨((ctr n).val + 1) % gnbaK φ, ...⟩
    else
      ctr n
```

**NBA run**: `nbaRun i := (gnbaRun i, ctr i)`

**Transitions**: By construction, `gnbaTr` holds (from `canonicalAtom_gnbaTr`) and
the counter follows the corrected conditional advance rule.

### Step C5: Counter Returns to 0 Infinitely Often

**Need**: `∃ᶠ k in atTop, (ctr k).val = 0` (equivalently, `nbaRun k ∈ accept`).

**When `gnbaK φ = 0`**: `ctr k = 0` for all k, so trivially frequently. ✓

**When `gnbaK φ = K > 0`**: By induction on counter value.

**Key lemma (counter progress)**: If counter = j at time n, then there exists m > n
with counter = (j+1) mod K at time m.

*Proof*: The counter stays at j until the GNBA run visits acceptance set F_j.
By Step C3, the GNBA run visits F_j infinitely often. So there exists some m ≥ n
with `gnbaRun m ∈ gnbaAcceptSet φ (untlFinset φ)[j]` and counter still at j.
At that step, the counter advances to (j+1) mod K. ∎

**Counter cycling**: From counter = 0 at time t₀:
- Eventually counter = 1 (after F_0 visited)
- Eventually counter = 2 (after F_1 visited)
- ...
- Eventually counter = 0 again (after F_{K-1} visited)

This whole cycle takes finitely many steps. Since it can be repeated from any point,
counter = 0 occurs infinitely often.

**Lean approach**: Define `next_accept_visit : Fin K → ℕ → ℕ` using `Nat.find` or
classical choice, then chain them. Or prove directly by
`∀ N, ∃ k ≥ N, (ctr k).val = 0` using iterated application of the counter progress
lemma.

---

## 4. Soundness: NBA Accepting Run → Satisfaction

### Goal

Given `⟨ss, hrun, hacc⟩` where `ss : ℕ → GNBANBAState φ`,
`hrun : gnbaNBA φ .Run v ss`, `hacc : ∃ᶠ k in atTop, ss k ∈ accept`, show
`Satisfies (fun n p => p ∈ v n) 0 φ`.

### Step S0: Extract GNBA Run from NBA Run

Define `B : ℕ → GNBAState φ` by `B i := (ss i).1` and `ctr i := (ss i).2`.

From `hrun.trans` (OmegaExecution), at each step i:
- `gnbaTr φ (B i) (v i) (B i+1)` (the GNBA transition holds)
- Counter follows the conditional advance rule

### Step S1: NBA Acceptance → GNBA Acceptance (Degeneralization Forward)

**Need**: For each Until subformula `χ ∈ untlSubformulas φ`:
```
∃ᶠ k in atTop, (B k) ∈ gnbaAcceptSet φ χ
```

**Proof**: From `hacc`, counter = 0 occurs infinitely often. Between any two
consecutive returns to counter = 0, the counter passes through values 0, 1, ..., K-1.
Each time the counter advances from j to j+1, the GNBA state at that step is in F_j
(by the conditional advance rule). So between two counter-0 visits, every F_j is
visited at least once.

Since counter-0 occurs infinitely often, every F_j is visited infinitely often. ∎

**Lean approach**: Given `hacc : ∃ᶠ k in atTop, (ctr k).val = 0`:
- Between consecutive counter-0 times `t₁ < t₂`, for each j ∈ {0,...,K-1}, there
  exists some k with t₁ ≤ k < t₂ and counter advances from j to j+1 at step k,
  which means `B k ∈ F_j`.
- Since there are infinitely many such intervals, each F_j is visited infinitely often.

### Step S2: Key Structural Lemma (Soundness Core)

For all `ψ ∈ closure φ` and all `i`:
```
ψ ∈ (B i).val → Satisfies (fun n p => p ∈ v n) i ψ
```

**Proof by structural induction on ψ** (the IH is available for all i):

#### Case `atom p`

`atom p ∈ (B i).val`. By letter consistency (from `gnbaTr` at step i):
`atom p ∈ (B i).val ↔ p ∈ v i`.
So `p ∈ v i`, which is `Satisfies v i (atom p)`. ✓

#### Case `bot`

`bot ∈ (B i).val`. By `(B i).property.botConsistent`, `bot ∉ (B i).val`.
Contradiction — the implication holds vacuously. ✓

#### Case `imp ψ₁ ψ₂`

`imp ψ₁ ψ₂ ∈ (B i).val`. Need `Satisfies v i ψ₁ → Satisfies v i ψ₂`.

By `(B i).property.impClosure`:
`imp ψ₁ ψ₂ ∈ (B i).val ↔ (ψ₁ ∉ (B i).val ∨ ψ₂ ∈ (B i).val)`

So either `ψ₁ ∉ (B i).val` or `ψ₂ ∈ (B i).val`.

- If `ψ₂ ∈ (B i).val`: by IH on ψ₂, `Satisfies v i ψ₂`, so implication holds. ✓
- If `ψ₁ ∉ (B i).val`: **need reverse direction** — `ψ₁ ∉ (B i).val → ¬Satisfies v i ψ₁`.

**Reverse direction via propositional consistency**: If `ψ₁ ∈ subformulas φ`, then
by `propConsistent`: `ψ₁ ∉ (B i).val → imp ψ₁ bot ∈ (B i).val`.
By IH on `imp ψ₁ bot`: `Satisfies v i (imp ψ₁ bot)`, i.e., `¬Satisfies v i ψ₁`.

**But**: propConsistent only applies to subformulas, not all closure members. We need
to handle the case where `ψ₁` is a closure member but not a subformula (i.e.,
`ψ₁ = imp χ bot` for some subformula χ, or `ψ₁ = next (untl χ₁ χ₂)`).

**For `ψ₁ = imp χ bot`**: `imp χ bot ∉ (B i).val`. By propConsistent on χ
(which IS a subformula): `χ ∈ (B i).val`. So `Satisfies v i χ` (by IH on χ).
Then `Satisfies v i (imp χ bot)` requires `Satisfies v i χ → False`, which is
`¬Satisfies v i χ`. But we just showed `Satisfies v i χ`. Contradiction with
`¬Satisfies v i (imp χ bot)` — wait, we need `¬Satisfies v i ψ₁ = ¬Satisfies v i (imp χ bot)`.
`Satisfies v i (imp χ bot) = (Satisfies v i χ → False)`. Since `Satisfies v i χ` holds
(IH on χ), `Satisfies v i (imp χ bot)` is false. So `¬Satisfies v i (imp χ bot)` holds.
This means the implication `Satisfies v i ψ₁ → Satisfies v i ψ₂` holds vacuously. ✓

**For `ψ₁ = next (untl χ₁ χ₂)`**: Similar — use next-step consistency and IH.

**Practical implementation**: The cleanest approach is to prove S2 as stated (forward
only), and handle the imp case by:
1. From `impClosure`, get `ψ₁ ∉ B_i ∨ ψ₂ ∈ B_i`
2. Case `ψ₂ ∈ B_i`: IH gives `Satisfies v i ψ₂`, done
3. Case `ψ₁ ∉ B_i`: Assume `Satisfies v i ψ₁` for contradiction.
   Use `mem_closure_cases` to determine what form ψ₁ takes:
   - If ψ₁ ∈ subformulas: by propConsistent, `imp ψ₁ bot ∈ B_i`.
     By IH on `imp ψ₁ bot`: `¬Satisfies v i ψ₁`. Contradiction.
   - If ψ₁ = imp χ bot: `Satisfies v i (imp χ bot)` means `¬Satisfies v i χ`.
     By propConsistent on χ: `χ ∉ B_i → imp χ bot ∈ B_i`. But `ψ₁ = imp χ bot ∉ B_i`,
     so `χ ∈ B_i`. By IH on χ: `Satisfies v i χ`. Contradiction with `¬Satisfies v i χ`.
   - If ψ₁ = next (untl χ₁ χ₂): `Satisfies v i (next (untl χ₁ χ₂))` means
     `Satisfies v (i+1) (untl χ₁ χ₂)`. By next-step consistency (transition at step i):
     `next (untl χ₁ χ₂) ∈ B_i ↔ untl χ₁ χ₂ ∈ B_{i+1}`. Since `next (untl χ₁ χ₂) ∉ B_i`,
     `untl χ₁ χ₂ ∉ B_{i+1}`. By propConsistent on `untl χ₁ χ₂` (which IS a subformula):
     `imp (untl χ₁ χ₂) bot ∈ B_{i+1}`. By IH: `¬Satisfies v (i+1) (untl χ₁ χ₂)`.
     Contradiction.

#### Case `next ψ`

`next ψ ∈ (B i).val`. By next-step consistency (transition condition 2):
`next ψ ∈ (B i).val ↔ ψ ∈ (B (i+1)).val`.
So `ψ ∈ (B (i+1)).val`. By IH at position i+1: `Satisfies v (i+1) ψ`.
So `Satisfies v i (next ψ)`. ✓

#### Case `untl ψ₁ ψ₂` (THE HARD CASE)

`untl ψ₁ ψ₂ ∈ (B i).val`. Need: `∃ j ≥ i, Satisfies v j ψ₂ ∧ ∀ k, i ≤ k → k < j → Satisfies v k ψ₁`.

**Step 1**: From GNBA acceptance (Step S1), acceptance set F_{ψ₁Uψ₂} is visited
infinitely often: `∃ᶠ k in atTop, (B k) ∈ gnbaAcceptSet φ (untl ψ₁ ψ₂)`.

In particular: `∃ j ≥ i, untl ψ₁ ψ₂ ∉ (B j).val ∨ ψ₂ ∈ (B j).val`.

**Step 2**: Take the **minimum** such j ≥ i (by well-ordering / `Nat.find`).

**Step 3**: Show sub-case `untl ψ₁ ψ₂ ∉ (B j).val` is impossible.

- If j = i: contradicts hypothesis `untl ψ₁ ψ₂ ∈ (B i).val`.
- If j > i: for all k with i ≤ k < j, by minimality, `untl ψ₁ ψ₂ ∈ (B k).val`
  and `ψ₂ ∉ (B k).val`. At k = j-1:
  - `untl ψ₁ ψ₂ ∈ (B (j-1)).val` and `ψ₂ ∉ (B (j-1)).val`
  - By Until expansion (transition at step j-1):
    `untl ψ₁ ψ₂ ∈ (B (j-1)).val ↔ (ψ₂ ∈ (B (j-1)).val ∨ (ψ₁ ∈ (B (j-1)).val ∧ untl ψ₁ ψ₂ ∈ (B j).val))`
  - Since `ψ₂ ∉ (B (j-1)).val`: `ψ₁ ∈ (B (j-1)).val ∧ untl ψ₁ ψ₂ ∈ (B j).val`
  - So `untl ψ₁ ψ₂ ∈ (B j).val`, contradicting `untl ψ₁ ψ₂ ∉ (B j).val`. ∎

**Step 4**: So `ψ₂ ∈ (B j).val`. By IH on ψ₂ at position j: `Satisfies v j ψ₂`. ✓

**Step 5**: For all k with i ≤ k < j:
- By minimality of j: `untl ψ₁ ψ₂ ∈ (B k).val` and `ψ₂ ∉ (B k).val`
- By `untlLeft` atom property: `ψ₁ ∈ (B k).val`
- By IH on ψ₁ at position k: `Satisfies v k ψ₁` ✓

**Step 6**: Combine: `⟨j, hij, Satisfies v j ψ₂, ∀ k, i ≤ k → k < j → Satisfies v k ψ₁⟩`. ✓

### Step S3: Conclude

From `hrun.start`: `(ss 0).1 ∈ gnbaStart φ`, i.e., `φ ∈ (B 0).val`.
From `φ ∈ closure φ` (`self_mem_closure`) and S2 at i=0: `Satisfies v 0 φ`. ✓

---

## 5. CSLib-Specific Implementation Details

### 5.1 Run and Acceptance Types

```lean
-- NBA acceptance:
∃ ss, a.Run xs ss ∧ ∃ᶠ k in atTop, ss k ∈ a.accept

-- Run structure:
structure Run (na : NA State Symbol) (xs : ωSequence Symbol) (ss : ωSequence State) where
  start : ss 0 ∈ na.start
  trans : na.OmegaExecution ss xs

-- OmegaExecution:
def OmegaExecution (lts : LTS State Label) (ss : ωSequence State) (μs : ωSequence Label) : Prop :=
  ∀ i, lts.Tr (ss i) (μs i) (ss (i + 1))
```

### 5.2 `∃ᶠ` (Frequently) API

Key Mathlib lemmas:
- `Filter.frequently_atTop` : `(∃ᶠ x in atTop, p x) ↔ ∀ n, ∃ x ≥ n, p x`
- `frequently_iff_strictMono` (InfOcc.lean:34): `(∃ᶠ n in atTop, p n) ↔ ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ m, p (f m)`

For completeness C3: prove `∀ N, ∃ k ≥ N, P k`, then convert via `frequently_atTop`.
For soundness Until case: use `frequently_atTop.mp` to extract `∃ j ≥ i, P j`.

### 5.3 ωLanguage Equality

```lean
-- Use ext to reduce to membership equivalence:
theorem gnba_language_eq ... := by
  ext v
  simp only [ωAcceptor.mem_language]
  -- Goal: Accepts (gnbaNBA φ) v ↔ v ∈ gnbaOmegaLanguage φ
  constructor
  · exact gnba_soundness φ v
  · exact gnba_completeness φ v
```

### 5.4 Existing Proof Patterns (from OmegaRegular.lean)

The proofs of `atomNBA_language_eq` and `nextNBA_language_eq` follow this pattern:
1. `ωLanguage.mem_ext` to reduce to `∀ xs, xs ∈ LHS ↔ xs ∈ RHS`
2. `simp` to unfold `mem_language`, `Satisfies`
3. Forward: extract satisfaction from accepting run
4. Backward: construct run from satisfaction, prove start/trans/accept

The `∃ᶠ k in atTop` acceptance is typically proved via `rw [frequently_atTop]` then
`intro k; refine ⟨..., by omega, ...⟩`.

### 5.5 Satisfies Convention

CSLib uses `untl guard event` (Burgess convention):
```lean
| .untl ψ φ => ∃ j ≥ i, Satisfies v j φ ∧ ∀ k, i ≤ k → k < j → Satisfies v k ψ
```

The acceptance set `gnbaAcceptSet φ χ` for `χ = untl ψ₁ ψ₂`:
```
F_{ψ₁ U ψ₂} = { B | untl ψ₁ ψ₂ ∉ B.val ∨ ψ₂ ∈ B.val }
```

where ψ₂ is the event (second argument). This matches the existing definition.

---

## 6. Proof Dependencies (Recommended Order)

```
1. Fix gnbaNBA definition (conditional counter advance)
   ↓
2. Completeness C2: canonicalAtom_mem_start (trivial)
   ↓
3. Completeness C3: canonicalAtom_gnba_acceptance (new, ~40-60 lines)
   ↓
4. Completeness C4: counter_cycling (new, ~60-100 lines)
   ↓
5. gnba_completeness (combine C2 + C3 + C4, ~30-50 lines)
   ↓
6. Soundness S1: degeneralization_forward (NBA acc → GNBA acc, ~40-60 lines)
   ↓
7. Soundness S2: gnba_soundness_key (structural induction, ~100-150 lines)
   ↓
8. gnba_soundness (combine S1 + S2 + S3, ~20-30 lines)
   ↓
9. gnba_language_eq (ext + completeness + soundness, ~10-20 lines)
```

### Estimated Total: 340-530 lines of new proof code

---

## 7. Summary of Required Changes

1. **Fix `Formula.gnbaNBA`** (GNBA.lean:656-663): Replace unconditional counter advance
   with conditional advance based on acceptance set membership.

2. **Add helper lemmas**:
   - `canonicalAtom_mem_start`: canonical atom at 0 is a start state
   - `canonicalAtom_gnba_acceptance`: canonical run visits each acceptance set infinitely often
   - `counter_cycling`: counter returns to 0 infinitely often when all acceptance sets visited ∞-often
   - `degeneralization_forward`: NBA Büchi acceptance implies all GNBA acceptance sets visited ∞-often
   - `gnba_soundness_key`: ψ ∈ B_i → Satisfies v i ψ (by structural induction on ψ)

3. **Prove `gnba_completeness` and `gnba_soundness`** as separate lemmas.

4. **Replace the `sorry`** in `gnba_language_eq` with `ext v; exact ⟨gnba_soundness, gnba_completeness⟩`.

5. **Verify**: `lean_verify` on `gnba_language_eq` shows no `sorryAx`, and by transitive
   dependency, `Formula.isRegular` in OmegaRegular.lean also becomes sorry-free.

---

## 8. Risk Assessment

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Fixing gnbaNBA breaks `isRegular'`/`isRegular_untl` downstream | M | L | The only downstream use is `gnba_language_eq` which already has sorry; the fix makes it provable |
| Counter cycling proof is technically involved | M | M | Split into small lemmas; counter progress lemma + iteration |
| Soundness imp case needs careful handling of closure vs subformula distinction | H | M | Use `mem_closure_cases` to split into three sub-cases; each handled by existing atom properties |
| Soundness Until case needs `Nat.find` for minimum witness | M | L | Well-established Mathlib pattern |
| Total proof size (~400+ lines) may exceed single-phase implementation scope | H | M | Decompose into 3 sub-phases: (a) fix + completeness, (b) soundness, (c) integration |
