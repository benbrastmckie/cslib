# Research Report: Task #236 — GNBA Correctness Final Analysis

**Task**: 236 — Follow-up PRs from PR #649 (Buchi / omega-regular)
**Date**: 2026-06-19
**Mode**: Team Research (4 teammates)
**Session**: sess_1781899793_33c593

---

## Summary

Four research agents investigated the 3 remaining sorry markers in `GNBA.lean` from complementary angles: primary proof strategy (A), literature survey and alternatives (B), critical audit (C), and strategic horizons (D). All four converged on a corrected diagnosis and a clear fix path.

**The previous diagnosis was wrong.** Reports 04 and plan 05 attributed the blockers to a "Decidable instance mismatch" between `open Classical in` (on `gnbaNBA`) and `classical` tactic (in the proof). All teammates independently verified that both use the identical `Classical.propDecidable` instance — `rfl` succeeds between them.

**The actual remaining work is 30-80 lines, not 400-500 lines.** The soundness direction (lines 811-1127) is already fully proved with no sorry. Plan 05's Phase 2 (soundness, 8 hours) requires zero work. The 18-hour effort estimate was overestimated 6-10x.

**All 3 sorry markers share a single root cause** and can be resolved with the same technique: unfolding the `ctr` definition via `Nat.rec_add_one` and case-splitting the if-then-else chain.

---

## Key Findings

### 1. Corrected Root Cause Diagnosis

**Previous diagnosis (WRONG)**: Decidable instance mismatch between `Classical.dec` and `Classical.propDecidable`.

**Correct diagnosis**: The 3 sorry markers are straightforward proof obligations about the counter transition that can be discharged by:
1. Unfolding `ctr` using `simp only [ctr, Nat.rec_add_one]` (which reduces `Nat.rec base step (n+1)` to `step n (Nat.rec base step n)`)
2. Unfolding `gnbaNBA` definition
3. Case-splitting the nested `dite`/`ite` chain with `split`

**Evidence**: Teammate A verified all three fix strategies via `lean_run_code` with comprehensive reproductions matching the actual code structure (Fin types, List.get with let bindings, Classical scoping, match + Nat.rec pattern).

**Confidence**: HIGH (verified by 3 of 4 teammates independently)

### 2. Mathematical Correctness Confirmed

All teammates verified:
- The `accept = {counter = K}` variant is correct and equivalent to Baier-Katoen Lemma 4.56
- No off-by-one errors in counter cycling
- The K = 0 edge case (no Until subformulas) is correctly handled
- Acceptance sets (`gnbaAcceptSet`) match the standard definition
- The counter reset transition from K to 0 is correct

**Confidence**: HIGH (unanimous across all 4 teammates)

### 3. Proof Architecture Is Sound

- Soundness direction: COMPLETE (316 lines, no sorry)
- Completeness direction: 3 sorry markers, all in counter transition proof
- The monolithic proof structure is appropriate — splitting would add verbosity without benefit
- The biconditional `hkey` lemma (`ψ ∈ B_i ↔ Satisfies v i ψ`) is fully proved
- All supporting lemmas exist and are sorry-free: `canonicalAtom_gnbaTr`, `canonicalAtom_isAtom`, `mem_closure_cases`, `IsAtom.untlLeft`

### 4. CSLib's Work Is Novel

No Lean 4 formalization of GNBA-to-NBA degeneralization exists anywhere. The closest precedents are:
- Isabelle/HOL: Schimpf, Merz, Smaus (TPHOLs 2009); CAVA Automata Library (AFP 2014)
- HOL4: Jantsch and Norrish (ITP 2018)
- Lean 4: Chou "AutomataTheory" (2025) covers omega-regular languages but NOT degeneralization

### 5. Downstream Impact Is Immediate

Closing the 3 sorry markers makes `Formula.isRegular` fully sorry-free — the headline result of the entire LTL module. All five cases (atom, bot, imp, next, untl) are already proved contingent on `gnba_language_eq`. This enables LTL model checking decidability, satisfiability decidability, and formula equivalence checking.

---

## Recommended Approach

### Primary Strategy: Inline Fix (Teammate A — verified)

No refactoring of `ctr` or `gnbaNBA` is needed. Each sorry can be filled directly:

#### Sorry 1 (line 1205) — `hss_trans` counter condition

```lean
simp only [Formula.gnbaNBA, ss, ctr, Nat.rec_add_one]
split
· simp
· split
  · split
    · simp
    · rfl
  · simp
```

**Explanation**: `simp only [...]` unfolds the gnbaNBA definition, ss, ctr, and applies `Nat.rec_add_one` to reduce `ctr (n+1)` to `step n (ctr n)`. The three nested `split` calls handle the `dite (K = 0)`, `dite (i.val < K)`, and `ite (B n ∈ acc)` chain.

#### Sorry 2 (line 1324) — `hctr_stay_step`

```lean
simp only [ctr, Nat.rec_add_one]
split
· omega
· split
  · rename_i hK hlt
    split
    · rename_i hmem
      exfalso
      have : (⟨(ctr (t + d')).val, hlt⟩ : Fin K) =
             (⟨m, hm⟩ : Fin K) := by ext; exact hctr_d'
      rw [this] at hmem
      exact hno_acc_d' hmem
    · rfl
  · omega
```

**Explanation**: Unfold ctr, case-split. In the acceptance branch, use `exfalso` because `hno_acc_d'` says `B (t+d') ∉ acc(χ_m)` while the branch assumes membership, bridging via `Fin.ext` from `hctr_d' : (ctr (t+d')).val = m`.

#### Sorry 3 (line 1359) — `hctr_advance`

```lean
simp only [ctr, Nat.rec_add_one]
split
· omega
· split
  · rename_i hK hlt
    split
    · simp [hctr_t_d_min]
    · rename_i hnotmem
      exfalso
      have : (⟨(ctr (t + d_min)).val, hlt⟩ : Fin K) =
             (⟨m, hm⟩ : Fin K) := by ext; exact hctr_t_d_min
      rw [this] at hnotmem
      exact hnotmem hd_min_mem
  · omega
```

**Explanation**: Same pattern as sorry 2 but reversed — the non-membership branch is contradicted by `hd_min_mem`.

### Fallback Strategy: Extract Counter Step (Teammate B/C)

If the inline fix encounters issues in the actual file (e.g., `simp` timeout on the 1400-line file), extract the counter as standalone definitions:

```lean
noncomputable def Formula.counterStep (φ : Formula Atom)
    (B : ℕ → GNBAState φ) (n : ℕ) (prev : Fin (gnbaK φ).succ) : Fin (gnbaK φ).succ :=
  if hK : gnbaK φ = 0 then ⟨0, by omega⟩
  else if hlt : prev.val < gnbaK φ then
    let χ := (untlFinset φ).toList.get ⟨prev.val, by rwa [Finset.length_toList, ← gnbaK]⟩
    if B n ∈ gnbaAcceptSet φ χ then ⟨prev.val + 1, by omega⟩
    else prev
  else ⟨0, Nat.succ_pos _⟩

noncomputable def Formula.counterSeq (φ : Formula Atom)
    (B : ℕ → GNBAState φ) : ℕ → Fin (gnbaK φ).succ
  | 0 => ⟨0, Nat.succ_pos _⟩
  | n + 1 => counterStep φ B n (counterSeq φ B n)
```

Then prove `counterSeq_succ` (should be `rfl`) and replace `ctr` with `counterSeq`. All three sorry locations become trivial applications of `counterSeq_succ`.

**Use this fallback only if the primary inline fix fails.**

---

## Synthesis

### Conflicts Resolved

| Conflict | Teammate A | Teammate B/C | Resolution |
|----------|-----------|-------------|------------|
| Need to refactor `ctr`? | No — works as-is with `Nat.rec_add_one` | Yes — extract as standalone def | **A wins** (verified on reproductions; B/C did not verify their alternative) |
| Root cause: Decidable? | No — both instances identical | No — unfoldability issue | **Unanimous**: not a Decidable issue |
| Need `ctr_succ` lemma? | No — `simp` handles it | Yes — explicit recursion equation | **A wins** for simplicity; B/C approach is valid fallback |

### Gaps Identified

1. **None of the inline fixes were tested on the actual 1400-line file.** Teammate A verified on reproductions matching the code structure, but the actual file may have different elaboration behavior due to its size. `simp` may timeout.

2. **Variable names in `rename_i`** may differ from what's expected. The implementation agent should use `lean_goal` (if responsive) or pattern-match by structure rather than relying on exact names.

3. **`lake build` is the reliable verification method**, not `lean_goal` or `lean_hover_info`, which timeout on this file.

### Recommendations

1. **Try the primary inline fix first** (sorry 1 → sorry 2 → sorry 3). Each is 5-10 lines.
2. **If `simp` times out**, fall back to the extraction strategy.
3. **Verify with `lake build Cslib.Logics.LTL.Semantics.GNBA`** after each sorry.
4. **Run `lean_verify` on `Formula.gnba_language_eq`** to confirm no `sorryAx`.
5. **Submit as a single PR** — no value in intermediate PRs.
6. **Do NOT refactor to general GNBA type** in this PR (follow-up task).

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|------------------|
| A | Primary proof strategy | completed | HIGH | Verified all 3 fixes via lean_run_code; corrected "Decidable mismatch" diagnosis |
| B | Literature & alternatives | completed | HIGH | Comprehensive literature survey; confirmed CSLib's work is novel; recommended extraction fallback |
| C | Critical audit | completed | HIGH | Verified soundness is complete; confirmed mathematical correctness; validated all assumptions |
| D | Strategic horizons | completed | HIGH | Scoped remaining work to 30-80 lines; confirmed downstream `isRegular` payoff |

---

## Literature References

### Essential References (for the construction)

| Source | Content | Relevance |
|--------|---------|-----------|
| Baier & Katoen, "Principles of Model Checking" (2008) | Ch. 4 Lem. 4.56 (degeneralization), Ch. 5 Def. 5.37/Thm. 5.39 (GNBA from LTL) | Primary reference for the construction |
| Vardi & Wolper (1986) | Original automata-theoretic LTL→NBA | Theoretical foundation |

### Formalization Precedents (for proof techniques)

| Source | Language | Content | Notes |
|--------|----------|---------|-------|
| Schimpf, Merz, Smaus (TPHOLs 2009) | Isabelle/HOL | LTL→GBA verified | PDF: inria.hal.science/inria-00408950 |
| AFP "LTL_to_GBA" (2014) | Isabelle/HOL | GBA construction | isa-afp.org/entries/LTL_to_GBA.html |
| CAVA Automata Library (AFP 2014) | Isabelle/HOL | General automata framework | isa-afp.org/entries/CAVA_Automata.html |
| Esparza, Lammich, et al. (CAV 2013) | Isabelle/HOL | Full LTL model checker | Degeneralization embedded in pipeline |
| Jantsch & Norrish (ITP 2018) | HOL4/CakeML | LTL→BA via VWAA | Includes standalone GBA→BA step |
| Brunner, Seidl, Sickert (ITP 2019) | Isabelle/HOL | LTL→DRA (bypasses GBA) | Alternative approach, not applicable |
| Chou "AutomataTheory" (Lean 4, 2025) | Lean 4 | Omega-regular, McNaughton's | No degeneralization |

### Literature Availability

None of the above are currently in `specs/literature/`. The most useful to obtain would be:
1. **Baier & Katoen Ch. 4-5** — the canonical reference for this exact construction
2. **Schimpf, Merz, Smaus (2009)** — closest formalization precedent, PDF freely available
3. **Jantsch & Norrish (2018)** — the only formalization with standalone GBA→BA, PDF at cakeml.org/itp18.pdf

However, the remaining proof work is purely technical (unfolding definitions and case-splitting), not mathematical. The literature references are more relevant for documentation and PR description than for completing the proof.

---

## Assessment of Previous Reports

| Report/Plan | Key Claim | Verdict |
|-------------|-----------|---------|
| Report 04 | "Decidable instance mismatch is root cause" | **INCORRECT** — instances are definitionally equal |
| Report 04 | "gnbaNBA counter was unconditional" | Was true, now fixed — current definition is correct |
| Plan 05 Phase 2 | "Soundness needs 8 hours" | **INCORRECT** — soundness is already complete |
| Plan 05 | "Total effort 18 hours" | **Overestimated ~10-18x** — actual work is 1-3 hours |
| Plan 05 | "~400-500 lines of new proof code" | **Overestimated ~5-15x** — actual work is 30-80 lines |

---

## Next Steps

1. `/plan 236` — Update plan to reflect corrected diagnosis and reduced scope
2. `/implement 236` — Fill the 3 sorry markers using the primary inline strategy
3. `lean_verify Formula.gnba_language_eq` — Confirm sorry-free
4. `lean_verify Formula.isRegular` — Confirm transitively sorry-free
5. `/pr 236` — Submit as single PR to cslib
