# Teammate A (Primary Angle): Decidable Instance Analysis and Verified Fix Strategy

**Task**: 236 -- Follow-up PRs from PR #649 (Buchi / omega-regular)
**Focus**: Deep analysis of the 3 sorry markers in GNBA.lean, root cause identification, and verified proof strategies

---

## Key Findings

### 1. The "Decidable Instance Mismatch" Diagnosis Is Incorrect

**Confidence: HIGH (verified via lean_run_code)**

The previous reports (04, plan 05) attribute the root cause to a Decidable instance mismatch between `open Classical in` (on `gnbaNBA`) and `classical` tactic (in the proof). This diagnosis is **wrong**:

```lean
-- Both produce the SAME instance: Classical.propDecidable
-- Test: rfl succeeds between Classical.dec and Classical.propDecidable
example (p : Prop) : @Classical.dec p = @Classical.propDecidable p := by rfl
```

I verified this directly: `Classical.dec` and `Classical.propDecidable` are **definitionally equal** in Lean 4. The `open Classical in` scoping and the `classical` tactic both provide the same `Decidable` instance. The if-then-else expressions using either instance are definitionally equal.

### 2. The Real Issue: Not Understanding That the Proof IS Within Reach

**Confidence: HIGH (verified via lean_run_code)**

The three sorries are not blocked by any fundamental technical issue. They are provable using straightforward tactic sequences. The key insight is:

1. `ctr(n+1)` is definitionally equal to `step n (ctr n)` thanks to `Nat.rec_add_one`
2. The `ctr` definition (even with the `match + Nat.rec` pattern) works correctly
3. `simp only [Formula.gnbaNBA, ss, ctr, Nat.rec_add_one]` followed by `split` handles the if-then-else chain

I verified this with a comprehensive reproduction matching the actual code structure (Fin types, List.get, let bindings, classical scoping, match + Nat.rec pattern). All three sorry patterns compile and complete.

### 3. The gnbaNBA Definition (accept = {counter = K}) Is Correct

**Confidence: HIGH**

The current definition uses `accept := { s | s.2.val = Formula.gnbaK phi }` (counter = K), which is a valid variant of the standard Baier-Katoen Lemma 4.56. The standard uses modular arithmetic with accept = 0; the current uses linear counting 0..K with accept = K. Both are mathematically equivalent:

- Standard (Baier-Katoen): Counter cycles 0 -> 1 -> ... -> K-1 -> 0. Accept at 0.
- Current (CSLib): Counter goes 0 -> 1 -> ... -> K -> 0 -> 1 -> .... Accept at K.

The current variant has one extra counter value (K+1 total via `Fin (K+1)`) but this is harmless and actually simplifies the reset logic (the `else` branch of `i.val < K` handles the reset naturally).

### 4. No Refactoring of `ctr` Is Needed

**Confidence: HIGH (verified via lean_run_code)**

Teammate C's report suggested redefining `ctr` to remove the outer `match`. This is unnecessary. The current definition:

```lean
let ctr : N -> Fin K.succ := fun n =>
  match n with
  | 0 => init
  | n + 1 => by exact Nat.rec init step (n + 1)
```

already gives `ctr n = Nat.rec init step n` for all n, because:
- `ctr 0 = init = Nat.rec init step 0` (definitional)
- `ctr (n+1) = Nat.rec init step (n+1)` (by definition)

So `Nat.rec_add_one` gives `ctr (n+1) = step n (ctr n)` definitionally. I verified that the current definition works without changes.

### 5. The Monolithic Proof Structure Is Fine

**Confidence: HIGH**

The soundness direction is fully proved (no sorry, lines 811-1127). The completeness direction has 3 sorries, all in counter cycling. Splitting into separate lemmas would not help the proof and would require spelling out types for local `have` bindings. Keep the monolithic structure.

---

## Recommended Approach

### Fix Strategy: Inline Proofs at Each Sorry Location

**No helper lemma extraction needed. Each sorry can be filled in directly.**

#### Sorry 1 (line 1205) -- `hss_trans` counter condition

Replace `sorry` with:

```lean
simp only [Formula.gnbaNBA, ss, ctr, Nat.rec_add_one]
split
. simp
. split
  . split
    . simp
    . rfl
  . simp
```

This works because:
- `simp only [Formula.gnbaNBA, ss, ctr, Nat.rec_add_one]` unfolds the definition and counter, reducing `ctr (n+1)` to `step n (ctr n)`
- `split` handles `dite (K = 0)`
- Nested `split` handles `dite (i.val < K)` and `ite (B n in acc)`
- In each branch, the computed value trivially satisfies the proposition

#### Sorry 2 (line 1324) -- `hctr_stay_step`

Replace `sorry` with:

```lean
simp only [ctr, Nat.rec_add_one]
split
. omega  -- K = 0 contradicts m < K
. split
  . rename_i hK hlt
    split
    . rename_i hmem
      exfalso
      have : (({val := (ctr (t + d')).val, isLt := hlt} : Fin K)) = 
             ({val := m, isLt := hm} : Fin K) := by ext; exact hctr_d'
      rw [this] at hmem
      exact hno_acc_d' hmem
    . rfl
  . omega
```

Note: The exact variable names (`hK`, `hlt`, `hmem`, `hctr_d'`, `hno_acc_d'`, `hm`) must match the proof context at that point. The core idea: unfold `ctr`, split on the if-chain, and in the acceptance branch use `exfalso` because the hypothesis says `B (t+d') not-in gnbaAcceptSet` while the if-branch says it is -- bridging via `Fin.ext` from `(ctr (t+d')).val = m`.

#### Sorry 3 (line 1359) -- `hctr_advance`

Replace `sorry` with:

```lean
simp only [ctr, Nat.rec_add_one]
split
. omega  -- K = 0 contradicts m < K
. split
  . rename_i hK hlt
    split
    . simp [hctr_t_d_min]  -- advance: val = prev.val + 1 = m + 1
    . rename_i hnotmem
      exfalso
      have : (({val := (ctr (t + d_min)).val, isLt := hlt} : Fin K)) =
             ({val := m, isLt := hm} : Fin K) := by ext; exact hctr_t_d_min
      rw [this] at hnotmem
      exact hnotmem hd_min_mem
  . omega
```

### Alternative Approach: Extract Counter Step Lemma

If the implementation agent prefers a cleaner separation, define a single helper:

```lean
have hctr_step : forall n,
    if hK : K = 0 then (ctr (n+1)).val = 0
    else if hlt : (ctr n).val < K then
      let chi := (Formula.untlFinset phi).toList.get
          {val := (ctr n).val, isLt := by rwa [Finset.length_toList, <- Formula.gnbaK]}
      if B n in Formula.gnbaAcceptSet phi chi then (ctr (n+1)).val = (ctr n).val + 1
      else ctr (n+1) = ctr n
    else (ctr (n+1)).val = 0 := by
  intro n
  simp only [ctr, Nat.rec_add_one]
  split <;> [simp; split <;> [split <;> [simp; rfl]; simp]]
```

Then use `hctr_step n` at sorry 1, and extract specific cases from `hctr_step (t + d')` for sorries 2 and 3 by case analysis with `dif_neg hK` and the appropriate `ite` branch.

---

## Evidence

### Verified Reproductions

All proof strategies were verified via `lean_run_code` with comprehensive reproductions that match the actual code structure:

| Feature | Reproduced | Result |
|---------|-----------|--------|
| `open Classical in` vs `classical` tactic | Yes | Same instance, rfl succeeds |
| Match + Nat.rec pattern | Yes | Works without refactoring |
| Fin types with let bindings | Yes | simp + split handles correctly |
| List.get with proof terms | Yes | Proof-irrelevant, works |
| gnbaNBA.Tr counter condition | Yes | Full proof compiles |
| Counter stay case (sorry 2) | Yes | Full proof compiles |
| Counter advance case (sorry 3) | Yes | Full proof compiles |
| Structure field access (MyBuchi.Tr) | Yes | simp unfolds correctly |

### Key Lean Lemma Used

`Nat.rec_add_one` from `Mathlib.Data.Nat.Init`:
```
Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n)
```

This is already available through GNBA.lean's Mathlib imports. No new imports needed.

---

## Implementation Notes

### Variable Name Mapping

The proofs reference variables from the surrounding proof context. Here is the mapping between the reproduction and the actual file:

| Reproduction | Actual file | Location |
|-------------|-------------|----------|
| `K` | `Formula.gnbaK phi` (aliased as `K` at line 1174) | Line 1174 |
| `Bseq` / `B` | `B : N -> Formula.GNBAState phi` | Line 1133 |
| `accSets` | `Formula.gnbaAcceptSet phi` | Line 603 |
| `ctr` | `ctr : N -> Fin K.succ` | Line 1176 |
| `ss` | `ss : N -> Formula.GNBANBAState phi` | Line 1195 |

### Potential Complications in the Actual File

1. **LSP timeouts**: The file is ~1400 lines and causes LSP tool timeouts. Use `lake build` for verification, not `lean_goal`.

2. **Variable scoping at sorry sites**: The exact `rename_i` names may differ depending on Lean's internal naming. The implementation agent should use `lean_goal` (if it works) or match by structure. Using `next` or named `rename_i` is safer.

3. **Index proof terms**: The gnbaNBA definition uses `by rwa [Finset.length_toList, <- Formula.gnbaK]` for the list index proof, while the ctr uses `Finset.length_toList ... |> idx.isLt`. These are proof-irrelevant for `List.get`, so they unify fine after `simp`.

4. **The `split` tactic behavior**: After `simp only [Formula.gnbaNBA, ss, ctr, Nat.rec_add_one]`, the goal should be an if-then-else chain. The `split` tactic handles `dite` (dependent if) and `ite` (non-dependent if) uniformly. Three nested `split` calls handle the three-level if-chain.

### Estimated Effort

- Filling 3 sorries: 30-60 minutes
- Verification (`lake build`): 10-15 minutes
- Total: ~1 hour

This is a mechanical task once the proof strategy is known. No mathematical insight is needed beyond what is documented here.

---

## Assessment of Previous Reports

| Report | Key Claim | Verdict |
|--------|-----------|---------|
| Report 04 | "Decidable instance mismatch is the root cause" | INCORRECT -- instances are definitionally equal |
| Report 04 | "gnbaNBA counter was unconditional" | WAS TRUE, now fixed -- current definition is correct |
| Plan 05 | "Phase 2 (soundness) needs 8 hours" | INCORRECT -- soundness is already complete |
| Plan 05 | "Total effort 18 hours" | OVERESTIMATED ~18x -- actual work is ~1 hour |
| Teammate C | "Decidable mismatch is wrong, real issue is Nat.rec unfoldability" | PARTIALLY CORRECT -- the Nat.rec does need unfolding, but it works fine with `Nat.rec_add_one` |
| Teammate C | "Redefine ctr to remove outer match" | UNNECESSARY -- current definition works |
| Teammate D | "Keep monolithic proof structure" | CORRECT |
| Teammate D | "Don't refactor to general GNBA type" | CORRECT for this PR |
