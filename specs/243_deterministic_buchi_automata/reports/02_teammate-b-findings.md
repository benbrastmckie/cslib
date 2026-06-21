# Task 243: DBA Constructions — Teammate B Findings (Alternative Approaches & Reuse)

**Focus**: Alternative implementation strategies, reuse opportunities, simplification paths.

---

## Key Findings

### 1. DBA Non-Complement: Already a One-Line Corollary

**Finding (Confidence: High)**

`IsRegular.not_da_buchi` in `OmegaRegularLanguage.lean` (line 61–69) already proves
the non-closure result: there exists an ω-regular language not DBA-recognizable.
The DBA non-closure under complement is a **trivial corollary** — no new construction needed:

```lean
-- The witness: L = eventuallyZero is ω-regular but not DBA-recognizable (lines 61–69)
-- Its complement is "infinitely many 1s" which IS DBA-recognizable
-- Together: DBAs are not closed under complement
theorem DA.Buchi.not_closed_complement :
    ∃ (Symbol : Type) (L : ωLanguage Symbol),
      (∃ S (da : DA.Buchi S Symbol), language da = L) ∧
      ¬ ∃ S (da : DA.Buchi S Symbol), language da = Lᶜ := by
  -- Witness: Lᶜ = eventuallyZero (not DBA-recognizable by IsRegular.not_da_buchi)
  -- L = eventuallyZero's complement (1s infinitely often) IS DBA-recognizable
  ...
```

This requires flipping the roles (the complement of the non-DBA language IS DBA-recognizable),
but the proof obligation is just a one-liner using `IsRegular.not_da_buchi` as the
non-recognizability witness.

**Recommended approach**: Do not write a separate proof. State
`DA.Buchi.not_closed_complement` as a corollary of `IsRegular.not_da_buchi` in a new
`DA/BuchiClosure.lean`. The proof body is ~5 lines.

---

### 2. DBA Union: NOT Derivable from `IsRegular.sup` + `of_da_buchi` Without New Construction

**Finding (Confidence: High)**

`IsRegular.sup` (OmegaRegularLanguage.lean line 108) proves: if `p1` and `p2` are ω-regular,
then `p1 ⊔ p2` is ω-regular — but via the NBA sum construction (`NA.iSum`), not a DBA.

`IsRegular.of_da_buchi` (line 55) shows DBA language → ω-regular. But composing these
gives only: "the union of two DBA languages is ω-regular," NOT "the union of two DBA
languages is DBA-recognizable."

To prove DBA closure under union, a **direct product construction** is needed:

```
State: S₁ × S₂
accept: (F₁ × Q₂) ∪ (Q₁ × F₂)
```

The proof requires showing that visiting `F₁ × Q₂ ∪ Q₁ × F₂` infinitely often implies
visiting `F₁ × Q₂` infinitely often OR `Q₁ × F₂` infinitely often (by pigeonhole on the
two halves of a finite-union acceptance condition). This uses `frequently_in_finite_type`
(already in CSLib's `InfOcc.lean`) applied to a 2-element type.

**The key lemma**: if `∃ᶠ k in atTop, ss k ∈ S ∪ T` and `S` and `T` are disjoint finite
sets (or at least S, T finite), then `∃ᶠ k in atTop, ss k ∈ S` or `∃ᶠ k in atTop, ss k ∈ T`.
In Filter terms: `frequently_or_distrib` in Mathlib (`Filter.Frequently.or_distrib`) gives
`(∃ᶠ k, p k ∨ q k) ↔ (∃ᶠ k, p k) ∨ (∃ᶠ k, q k)` only for eventually-stable situations.
For the general case, the argument needs: in a finite set `{false, true}`, if something is
in the image infinitely often, some preimage class is infinite — exactly `frequently_in_finite_type`.

**`DA.prod` is directly usable**: The product DA `da1.prod da2` has run
`(da1.prod da2).run xs = (da1.run xs, da2.run xs)` by `prod_mtr_eq`. This run-decomposition
lemma does NOT currently exist for `DA.run` (only `prod_mtr_eq` for finite prefixes).

**Missing lemma needed**:
```lean
lemma DA.prod_run_eq (da1 : DA State1 Symbol) (da2 : DA State2 Symbol) (xs : ωSequence Symbol) :
    (da1.prod da2).run xs = (da1.run xs).zip (da2.run xs) := by
  ext n; simp [DA.prod, DA.run, prod_mtr_eq] -- or induction
```
This is a simple proof by induction on `n`, but needs to be added to `DA/Prod.lean`.

---

### 3. NBA Intersection (`BuchiInter.lean`) Is NOT Directly Adaptable to DBA Intersection

**Finding (Confidence: High)**

`NA/BuchiInter.lean` uses a nondeterministic history-state trick with `addHist` and
`histTrans` (lines 35–55). The "history bit" records which accepting set was last seen,
and toggling is nondeterministic (the automaton guesses when the next visit occurs).

For **deterministic** intersection, the key insight is: given `da1.run xs` and `da2.run xs`
are both determined (unique runs), the counter can be advanced deterministically. The
3-state counter version works as:

```
Counter state: Fin 3
  - 0: waiting for F₁ to be visited
  - 1: F₁ seen, waiting for F₂
  - 2: F₂ seen (reset to 0 on next step)
  Accept: counter = 2 (or = 0 after reset; either convention works)
```

The DBA intersection state is `S₁ × S₂ × Fin 3`, entirely deterministic. The NBA
`BuchiInter.lean` is a TEMPLATE showing the proof strategy (handling the toggle logic)
but NOT a drop-in adapter — the NBA proof relies on nondeterministic choice in
`hist_run_exists` (line 129), which has no deterministic analogue. The DBA proof instead
uses the uniqueness of `da.run` directly.

**Recommended approach**: Use the logical structure of `BuchiInter.lean` as a proof
template (toggling logic, `inter_freq_acc_freq_acc` analogue), but implement fresh
deterministic code. State: `S₁ × S₂ × Bool` (false = waiting for acc1, true = waiting for acc2).

---

### 4. `infOcc` Has Minimal Lemmas — Gaps for Landweber Proof

**Finding (Confidence: High)**

`Cslib.ωSequence.infOcc` (InfOcc.lean line 30) is defined as:
```lean
def infOcc (xs : ωSequence α) : Set α :=
  { x | ∃ᶠ k in atTop, xs k = x }
```

It is used in:
- `DA.Muller` acceptance (DA/Basic.lean line 117): `(a.run xs).infOcc ∈ a.accept`
- `NA.Muller` acceptance (NA/Basic.lean line 97): `∃ ss, a.Run xs ss ∧ ss.infOcc ∈ a.accept`

**Existing lemmas** (`InfOcc.lean`):
- `frequently_iff_strictMono`: `(∃ᶠ k, p k) ↔ ∃ f, StrictMono f ∧ ∀ m, p (f m)`
- `frequently_in_finite_type`: `(∃ᶠ k, xs k ∈ s) ↔ ∃ x ∈ s, ∃ᶠ k, xs k = x`
- `frequently_in_strictMono`: auxiliary for pigeonhole on strict monotone enumeration
- `strictMono_of_infinite`: extract strict-mono function from infinite set

**Missing lemmas for Landweber** — these do NOT currently exist and must be added:

```lean
-- infOcc membership characterization
lemma mem_infOcc (xs : ωSequence α) (x : α) :
    x ∈ xs.infOcc ↔ ∃ᶠ k in atTop, xs k = x := Iff.rfl

-- infOcc as a subset
lemma infOcc_subset_range (xs : ωSequence α) :
    xs.infOcc ⊆ Set.range xs := ...

-- infOcc of product run: product = pair of infOccs
lemma infOcc_prod_run_fst (xs : ωSequence Symbol) (da1 : DA State1 Symbol) (da2 : DA State2 Symbol) :
    ((da1.prod da2).run xs).infOcc.image Prod.fst = (da1.run xs).infOcc := ...

-- Finiteness of infOcc in finite type
lemma infOcc_finite [Finite α] (xs : ωSequence α) :
    (xs.infOcc).Finite := ...

-- Nonemptiness: some state always occurs infinitely often in finite-state run
lemma infOcc_nonempty_of_finite [Finite α] (xs : ωSequence α) :
    (xs.infOcc).Nonempty := by
  -- Follows from Finite.exists_infinite_fiber applied to xs viewed as function ℕ → α
  ...
```

For the **Landweber proof** (Thomas 2003 Thm 3.32b), the key facts needed are:
1. `infOcc` is nonempty in finite-state runs (from pigeonhole).
2. The DA accumulates states until it revisits the same set (`infOcc` stabilizes).
3. If the accumulated set is a superloop of an F-loop, acceptance follows.

The `Inf(ρ)` notation from Thomas 2003 is exactly `infOcc (da.run xs)` in CSLib.

---

### 5. Landweber Characterization: Use `buchi_eq_finAcc_omegaLim` Directly

**Finding (Confidence: Medium)**

Thomas 2003 Thm 3.32b proves: `L` is DBA-recognizable iff the Muller acceptance family
`F` is closed under superloops.

CSLib already has `buchi_eq_finAcc_omegaLim` (DA/Buchi.lean line 26):
```lean
theorem buchi_eq_finAcc_omegaLim :
    language (Buchi.mk da acc) = (language (FinAcc.mk da acc))↗ω
```

This shows every DBA language is an ω-limit of a DFA language. For the Landweber theorem:
- The **forward direction** (DBA → superloop-closed F): given a DBA recognizing `L`,
  construct the Muller automaton whose run visits `infOcc` and show F is superloop-closed.
  **`buchi_eq_finAcc_omegaLim` is directly useful** here because it gives the ω-limit
  characterization, connecting infinite-visit structure to loop structure.
- The **backward direction** (superloop-closed F → DBA): the construction in Thomas 2003 is:
  `State = Q × 2^Q`, tracking accumulated states, resetting when an F-loop (or superloop)
  is hit.

**Recommended formulation** (closer to Thomas 2003 than a Muller reformulation):

```lean
-- Define: a loop is a nonempty set S ⊆ Q where every state reaches every other
def DA.IsLoop (da : DA State Symbol) (S : Set State) : Prop :=
  S.Nonempty ∧ ∀ s t ∈ S, ∃ xs : List Symbol, xs ≠ [] ∧ da.mtr s xs = t

-- Define: an accepting family (for Muller) is closed under superloops
def DA.Muller.ClosedUnderSuperloops (a : DA.Muller State Symbol) : Prop :=
  ∀ F ∈ a.accept, ∀ S, a.IsLoop S → F ⊆ S → S ∈ a.accept

-- Landweber's Theorem
theorem DA.Muller.dba_recognizable_iff_closedUnderSuperloops
    [Finite State] (a : DA.Muller State Symbol) :
    (∃ acc : Set State, language (DA.Buchi.mk a.toDA acc) = language a) ↔
    a.ClosedUnderSuperloops
```

The Muller formulation is MORE NATURAL for the backward direction (constructing the DBA)
because it gives access to the accepting family F directly. Using `buchi_eq_finAcc_omegaLim`
in the forward direction avoids duplicating the ω-limit characterization.

A pure "omegaLim" formulation like "L is DBA-recognizable iff L = (L₀)↗ω for some regular
L₀" is equivalent but requires an additional lemma connecting ω-limits to loop structure —
more work with less textbook alignment.

---

### 6. Mathlib Has No Omega-Automata Infrastructure

**Finding (Confidence: High)**

The Mathlib search for "omega automaton Buchi" returned only finite-word automata:
`DFA`, `NFA`, and `Language.IsRegular` (finite-word version). **No Büchi, Muller, Rabin,
or ω-automata exist in Mathlib.** CSLib's entire omega-automata stack is original.

Mathlib's `DFA.inter` and `DFA.union` (Mathlib.Computability.DFA) are direct analogues for
finite words — the interface patterns (`DFA.inter_accept`, `DFA.accepts_inter`) are good
stylistic models for the DBA union/intersection theorems to follow.

**Reuse opportunity from Mathlib**:
- `Finite.exists_infinite_fiber` (Mathlib.Data.Fintype.Pigeonhole): already imported in
  `InfOcc.lean` via `Mathlib.Data.Fintype.Pigeonhole`. This is the key pigeonhole lemma.
- `Filter.Frequently.or_distrib`-style reasoning and `frequently_or_distrib` — confirm
  existence in Mathlib for the union proof.
- `Nat.frequently_atTop_iff_infinite` (Mathlib.Order.Filter.Cofinite): already used in
  `InfOcc.lean` for the `frequently_iff_strictMono` proof.
- `Filter.cofinite.limsup_set_eq` (Mathlib.Order.LiminfLimsup): `infOcc` is definitionally
  equal to `Filter.limsup (fun k => {xs k}) Filter.cofinite` via
  `Filter.mem_limsup_iff_frequently_mem`. This connection is **not currently formalized**
  and could provide a bridge to Mathlib's limsup lemma library.

---

### 7. `frequently_in_finite_type` Is the Key Reuse Lemma for DBA Union

**Finding (Confidence: High)**

`frequently_in_finite_type` (InfOcc.lean line 46):
```lean
theorem frequently_in_finite_type [Finite α] {s : Set α} {xs : ωSequence α} :
    (∃ᶠ k in atTop, xs k ∈ s) ↔ ∃ x ∈ s, ∃ᶠ k in atTop, xs k = x
```

For the DBA union proof, the argument is:
- `da1.run xs` and `da2.run xs` are projections of `(da1.prod da2).run xs`.
- `(da1.prod da2).run xs k ∈ F₁ × Q₂ ∪ Q₁ × F₂` infinitely often.
- `Fin 2 → Set (S₁ × S₂)` where `(F₁ × Q₂)` corresponds to index 0 and `(Q₁ × F₂)` to index 1.
- Apply `frequently_in_finite_type` to `Fin 2` → get at least one index holds infinitely often.

However, the exact formulation needed is `frequently_or_distrib`:
```
(∃ᶠ k in atTop, P k ∨ Q k) → (∃ᶠ k in atTop, P k) ∨ (∃ᶠ k in atTop, Q k)
```

Let me check if this exists in Mathlib:

**Result**: `Filter.Frequently` does have `frequently_or_distrib_left` and
`frequently_or_distrib_right` but NOT a general `frequently_or_distrib` for `∨` in
the right direction (the `→` direction). The `∨`-introduction direction holds trivially;
the `∨`-elimination-from-frequently is the hard direction and requires finite-type
pigeonhole. The correct Mathlib lemma is via:
```lean
simp only [frequently_or_distrib] -- if it exists
-- or
rw [Nat.frequently_atTop_iff_infinite] -- convert to infinite set
-- then use Set.Infinite.union → one of the two is infinite
```

`Set.Infinite.of_not_finite` + `Set.Finite.union` gives: if `S ∪ T` is infinite and
both `S` and `T` are finite, contradiction. The contrapositive: if `S ∪ T` is infinite,
then `S` or `T` is infinite. This is `Set.infinite_union` (or `Set.Infinite.subset`).

---

## Recommended Approach

### For DBA Union (Phase 1a)

**Use `DA.prod` directly, add one helper lemma to `DA/Prod.lean`:**

```lean
-- In DA/Prod.lean (new lemma)
theorem DA.prod_run_fst_eq (da1 : DA State1 Symbol) (da2 : DA State2 Symbol)
    (xs : ωSequence Symbol) :
    (da1.prod da2).run xs = (da1.run xs).zip (da2.run xs) -- or state via pair projections
```

**DBA union construction** (new file `DA/BuchiClosure.lean`):
```lean
def DA.Buchi.union (a1 : DA.Buchi State1 Symbol) (a2 : DA.Buchi State2 Symbol) :
    DA.Buchi (State1 × State2) Symbol where
  toDA := a1.toDA.prod a2.toDA
  accept := (a1.accept ×ˢ Set.univ) ∪ (Set.univ ×ˢ a2.accept)
```

**Proof key step**: `frequently_or_distrib` in the form:
```lean
-- The run visits the union acceptance set infinitely often
-- iff it visits the F1-component infinitely often OR the F2-component
simp [Set.union_def, or_iff_not_imp_left, Set.Infinite.of_not_finite]
```

### For DBA Intersection (Phase 1b)

**New file `DA/BuchiClosure.lean`**, state = `S₁ × S₂ × Bool`:
- `false` = "waiting for acc1"
- `true` = "acc1 seen, waiting for acc2"
- Accept when current phase transitions from `true` to `false` (accepting cycle completed)

The counter toggles deterministically. Use `NA.BuchiInter.lean`'s proof strategy for
`inter_freq_acc_freq_acc` adapted to the deterministic setting (no `hist_run_exists` needed).

### For Landweber's Theorem (Phase 2)

**New file `DA/BuchiChar.lean`**, following Thomas 2003 Thm 3.32b:
- State: `Q × Finset Q` (current state, accumulated state set since last F-loop)
- Accept: when accumulated set becomes an F-loop (or its superloop) and resets
- Use `infOcc` for the correctness argument
- Forward direction: use `buchi_eq_finAcc_omegaLim` as a bridge + new `infOcc` lemmas

**Missing infrastructure** (add to `InfOcc.lean` or new `InfOcc/Basic.lean`):
- `infOcc_finite`: `infOcc` of finite-type ω-sequence is finite
- `infOcc_nonempty_of_finite`: pigeonhole says something always recurs
- `mem_infOcc`: unfold characterization of `infOcc` membership

---

## Evidence / Examples

### Direct Reuse Evidence

| CSLib Item | File | Used For |
|-----------|------|---------|
| `DA.prod` | `DA/Prod.lean` | DBA union/intersection product construction |
| `DA.run`, `run_succ`, `run_zero` | `DA/Basic.lean` | All DBA constructions |
| `buchi_eq_finAcc_omegaLim` | `DA/Buchi.lean` | Landweber forward direction |
| `frequently_in_finite_type` | `InfOcc.lean` | DBA union pigeonhole proof |
| `frequently_iff_strictMono` | `InfOcc.lean` | Extracting infinite visits |
| `IsRegular.not_da_buchi` | `OmegaRegularLanguage.lean` | DBA complement non-closure proof |
| `DA.Buchi.toNABuchi_language_eq` | `DA/ToNA.lean` | Landweber backward direction (NBA route) |
| `Finite.exists_infinite_fiber` | Mathlib (imported) | DBA union via pigeonhole |

### Missing Infrastructure (Must Add)

| Item | Location | Needed For |
|------|---------|-----------|
| `DA.prod_run_eq` (run projection lemma) | `DA/Prod.lean` | All DBA product proofs |
| `infOcc_finite` | `InfOcc.lean` | Landweber + DBA inter |
| `infOcc_nonempty_of_finite` | `InfOcc.lean` | Landweber construction |
| `DA.IsLoop` (loop definition) | `DA/BuchiChar.lean` | Landweber statement |
| `DA.Muller.ClosedUnderSuperloops` | `DA/BuchiChar.lean` | Landweber statement |

---

## Confidence Levels

| Finding | Confidence | Basis |
|---------|-----------|-------|
| Non-closure under complement is a trivial corollary | High | Direct inspection of `not_da_buchi` |
| DBA union NOT derivable without new construction | High | Checked `IsRegular.sup` uses NBA, not DBA |
| NBA intersection pattern NOT drop-in for DBA | High | `hist_run_exists` requires nondeterminism |
| `infOcc` has minimal lemmas; gaps for Landweber | High | Only 1 def found in local search |
| Landweber best as Muller formulation | Medium | Thomas 2003 proof structure reviewed |
| No Mathlib omega-automata | High | LeanSearch returns only `DFA`, `NFA` |
| `frequently_in_finite_type` is the union proof key | High | Pattern already used in `Pair.lean` line 113 |
| `DA.prod_run_eq` needs to be added | High | `prod_mtr_eq` only covers finite words |

---

## Summary of Gaps vs. Teammate A Scope

Teammate A likely covers the primary construction designs. This report adds:

1. **Shortcut**: DBA complement non-closure is a 5-line corollary of `IsRegular.not_da_buchi`.
2. **Obstacle**: DBA union proof requires a `DA.prod_run_eq` lemma not currently in `DA/Prod.lean`.
3. **Negative**: NBA intersection code cannot be adapted directly (nondeterminism is structural).
4. **Gap inventory**: `infOcc` needs 2–3 new lemmas for Landweber to work.
5. **Landweber recommendation**: Use Muller formulation with `ClosedUnderSuperloops`, leverage
   `buchi_eq_finAcc_omegaLim` for the forward direction proof.
6. **Mathlib**: No omega-automata exist; Mathlib's `DFA.inter`/`DFA.union` are style models only.
