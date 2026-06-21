# Teammate D (Horizons): Strategic Analysis of GNBA Correctness Proof

**Task**: 236 -- Follow-up PRs from PR #649 (Buchi / omega-regular)
**Focus**: Long-term alignment, reusability, downstream impact, and quality standards

---

## Key Findings

### 1. Proof Architecture for Reusability

**Confidence**: HIGH

The current implementation **tightly couples** the GNBA-to-NBA degeneralization to LTL formulas. All definitions (`GNBAState`, `gnbaTr`, `gnbaStart`, `gnbaAcceptSet`, `gnbaNBA`, `gnba_language_eq`) live in the `Cslib.Logic.LTL` namespace and are parameterized by `Formula Atom`. This is a defensible choice *for the current task scope*, but it leaves significant reuse potential on the table.

**Current structure (LTL-specific)**:
```
Formula.GNBAState φ     -- atoms of φ
Formula.gnbaTr φ         -- GNBA transition for φ
Formula.gnbaNBA φ        -- NBA via cycling counter for φ
Formula.gnba_language_eq -- correctness for φ
```

**Ideal general structure (not recommended for this PR)**:
```
Cslib.Automata.NA.GNBA          -- general GNBA type
Cslib.Automata.NA.GNBA.toBuchi  -- degeneralization construction
Cslib.Automata.NA.GNBA.toBuchi_language_eq  -- general correctness
```

**Recommendation**: Complete the current LTL-specific proof as-is. A general GNBA type and degeneralization theorem should be a **follow-up task** (see Section 3). The reason is practical: the current proof is ~1400 lines deep, the 3 remaining sorries are in counter cycling lemmas, and refactoring to a general GNBA type would require rethinking the entire module structure -- a scope expansion that risks destabilizing the existing work.

However, the current proof's *internal structure* already partially enables future extraction:
- `canonicalAtom_gnbaTr` proves GNBA transitions hold for *any* canonical run
- The cycling counter construction (`ctr`) is functionally independent of the specific GNBA
- The soundness direction's `hkey` biconditional lemma is the only deeply LTL-specific part

**Evidence**: CSLib's `Cslib.Automata.NA.BuchiInter` already has a general product construction with history state for NBA intersection. A general GNBA type would fit naturally alongside this as `Cslib.Automata.NA.GBuchi` (or `NA.GNBA`), following the existing pattern: `NA.Buchi` for NBA, `NA.Muller` for Muller, `DA.Buchi` for deterministic Buchi.

### 2. The Counter Construction as Reusable Infrastructure

**Confidence**: MEDIUM

The cycling counter is a standard construction in automata theory (Baier-Katoen Lemma 4.56). Its core idea -- "visit a sequence of acceptance sets in order, cycling forever" -- appears in multiple contexts:

1. **GNBA-to-NBA degeneralization** (current use)
2. **NBA intersection** (already in CSLib as `BuchiInter` -- uses a 2-set version with Bool toggle)
3. **Rabin-to-Buchi conversion** (would need multi-set cycling)
4. **Streett-to-Buchi conversion** (similar pattern)

The current `gnbaCounterStep` is defined inline via `Nat.rec` within the `ctr` let-binding in the completeness proof. It is **not** a standalone definition. The `gnbaNBA` definition embeds the counter logic directly in the `Tr` field.

**Key observation**: The existing `BuchiInter` in CSLib uses a *different* mechanism (Bool history state toggle) for a 2-acceptance-set case. A general k-acceptance-set version would unify `BuchiInter` (k=2) with GNBA degeneralization (k=gnbaK). However, this unification is non-trivial because:
- `BuchiInter` uses `Prod` with history state
- GNBA degeneralization uses `Fin k.succ` counter
- The acceptance semantics differ (toggle vs. ordered cycling)

**Mathlib connection**: There is no existing Mathlib infrastructure for "visit each set in a sequence infinitely often." The closest Mathlib concept is `Filter.Frequently` (used extensively in the current proof). The cycling property could potentially be expressed as: for each `i < k`, `{n | B n in F_i}` is cofinite -- which is `∃ᶠ n in atTop, B n ∈ F_i`. But the *ordered* cycling (visit F_0, then F_1, ..., then F_{k-1}, then repeat) is specific to degeneralization and not a generic Mathlib pattern.

**Recommendation**: Keep `gnbaCounterStep` as an LTL-internal construction for now. If a general GNBA type is created later, the counter construction should be extracted to a standalone `GNBA.degeneralize` function in `Cslib.Automata.NA`.

### 3. Downstream Impact

**Confidence**: HIGH

Once `gnba_language_eq` is sorry-free, the following becomes immediately available:

**Already proven (contingent on sorry removal)**:
- `Formula.isRegular' φ` (OmegaRegular.lean:364): Any LTL formula over `[Finite Atom]` defines an omega-regular language. Uses `gnba_language_eq` directly.
- `Formula.isRegular_untl` (OmegaRegular.lean:374): The Until case of `Formula.isRegular`. Delegates to `isRegular'`.
- `Formula.isRegular φ` (OmegaRegular.lean:393): The main theorem. Structural induction where the `untl` case calls `isRegular_untl`.

**All five `Formula.isRegular` cases are already complete** (`atom`, `bot`, `imp`, `next`, `untl`) -- the only gap is the 3 sorries in `gnba_language_eq`. Closing those sorries makes the entire LTL omega-regularity theorem sorry-free.

**What this enables downstream**:

| Capability | Status | Dependency |
|------------|--------|------------|
| LTL model checking decidability | Enabled | `Formula.isRegular` |
| LTL satisfiability decidability | Enabled | `Formula.isRegular` + emptiness check |
| LTL formula equivalence checking | Enabled | complement + intersection + emptiness |
| Closure of LTL languages under Boolean ops | Already proved | `IsRegular.sup`, `.inf`, `.compl` in `OmegaRegularLanguage.lean` |
| LTL formulas define omega-regular languages | Enabled | This is `Formula.isRegular` itself |

**McNaughton's theorem** (`IsRegular.iff_da_muller`): This is a `proof_wanted` at OmegaRegularLanguage.lean:262. It states that omega-regular languages are exactly those accepted by deterministic Muller automata. This is *independent* of the GNBA work -- it does not require `gnba_language_eq`. The GNBA work establishes LTL subset-of omega-regular; McNaughton's theorem characterizes omega-regular differently.

**Deterministic Buchi automata**: CSLib already proves that there exists an omega-regular language NOT accepted by any deterministic Buchi automaton (`IsRegular.not_da_buchi` at OmegaRegularLanguage.lean:61). This is complete and unrelated to GNBA.

**Follow-up PRs from the original task-236 description**:
The task title mentions "follow-up PRs from PR #649." PR #649 likely contributed the Buchi automata infrastructure (`NA.Buchi`, `BuchiEquiv`, `BuchiInter`, `OmegaRegularLanguage`). The follow-up work was the LTL omega-regularity proof (GNBA construction). Once this is complete, the natural next steps are:
1. General GNBA type and degeneralization theorem (reusability)
2. CTL/CTL* omega-regular language characterization (if CSLib adds CTL)
3. McNaughton's theorem (already `proof_wanted`)
4. LTL model checking pipeline (decidability results)

### 4. Quality Standards for CSLib PRs

**Confidence**: HIGH

Based on inspection of the existing codebase (particularly `NA/Basic.lean`, `OmegaRegularLanguage.lean`, `BuchiEquiv.lean`), CSLib PRs follow these quality standards:

**Naming conventions**:
- Definitions: `camelCase` (`gnbaTr`, `gnbaStart`, `gnbaAcceptSet`)
- Theorems/lemmas: `snake_case` with dots for namespace (`gnba_language_eq`, `canonicalAtom_isAtom`)
- The existing code in GNBA.lean follows this convention correctly.

**Proof style**:
- CSLib uses **tactic proofs** throughout (consistent with Mathlib style)
- Term-mode proofs are acceptable for simple definitions and short lemmas
- The existing GNBA.lean uses tactic proofs exclusively for all non-trivial lemmas -- this is correct
- `grind` tactic is used in some CSLib files (BuchiEquiv, OmegaRegularLanguage) but not in GNBA.lean. This is fine -- `grind` is not required.

**Documentation requirements**:
- CSLib enforces `docBlame` linting: ALL public declarations need docstrings
- The current GNBA.lean has thorough docstrings on all definitions and key lemmas
- Private helpers (`private lemma`) do not need docstrings
- Module-level docstring with `/-! ... -/` is present and comprehensive

**sorry hygiene**:
- The zero-debt policy is strict: NO sorry in merged PRs
- `proof_wanted` is the accepted way to mark unproved theorems (used for McNaughton's in OmegaRegularLanguage.lean:262)
- The 3 remaining sorries in GNBA.lean must ALL be eliminated before PR submission

**What the PR should include**:
1. Sorry-free `gnba_language_eq` (the main correctness theorem)
2. All existing docstrings preserved/updated
3. Clean `lake build` + `lake lint` + `lake exe checkInitImports`
4. AI disclosure in PR description (per CSLib/Mathlib policy)

### 5. Scope Assessment

**Confidence**: HIGH

**Current state**: GNBA.lean is 1402 lines. The soundness direction is fully proven. The completeness direction has 3 sorries, all in counter cycling (lines 1205, 1324, 1359). The root cause is a Decidable instance mismatch between `open Classical in` on `gnbaNBA` and `classical` tactic in the proof.

**Estimated remaining work**: 30-80 lines of proof code, focused on aligning the Decidable instances or working around the mismatch. This is NOT a 400-500 line task (that was the original estimate for the full correctness proof, most of which is now complete).

**PR strategy recommendation**:

| Option | Scope | Risk | Recommendation |
|--------|-------|------|----------------|
| A: Single PR (fix all 3 sorries) | Low | Low | **Recommended** |
| B: Separate "fix gnbaNBA" + "complete proof" | Medium | Medium | Unnecessary complexity |
| C: Land intermediate (completeness-only or soundness-only) | Low | Low | Not useful -- soundness is already done, and completeness alone doesn't give `isRegular` |

**Rationale for Option A**: The 3 sorries share a single root cause (Decidable instance mismatch). Fixing one fixes all three. The gnbaNBA definition is already corrected (conditional counter advance). There is no value in landing the fix separately because the intermediate state (corrected gnbaNBA with sorries) is not useful to anyone.

**Should Phase 1 and Phase 2 be separate PRs?** No. Phase 2 (soundness) is already complete. Phase 1 (completeness) has 3 sorries that are all in the counter cycling sub-proof. Splitting this would create an artificial boundary.

### 6. Creative/Unconventional Approaches

**Confidence**: MEDIUM

**6a. Decidable instance alignment (the blocking issue)**:

The root cause of the 3 sorries is that `gnbaNBA` uses `open Classical in` (providing `Classical.dec`) for the `if B in gnbaAcceptSet` condition, while the proof uses `classical` tactic (providing `Classical.propDecidable`). These are propositionally equal but not definitionally equal.

**Strategy 4 from the handoff is most promising**: Prove `hss_trans` by case analysis on the conditions rather than by definitional unfolding. This avoids the Decidable instance mismatch entirely. The proof would:
1. Extract the GNBA transition from `hgnbaTr`
2. For the counter condition: case-split on `gnbaK phi = 0`, `ctr(n).val < gnbaK`, and `B n in gnbaAcceptSet`
3. In each case, show the counter value matches what `gnbaNBA.Tr` requires
4. Use `congr` or `convert` with propositional equality proofs to bridge the Decidable gap

An alternative approach: use `@dite` explicitly with `Classical.dec` in the proof to match the instance used in `gnbaNBA`. Or use `simp only [dif_pos, dif_neg]` to normalize both sides.

**6b. Simulation relation approach**:

The existing LTS `IsSimulation` infrastructure (in `Cslib.Foundations.Semantics.LTS.Simulation`) defines simulation relations between LTS states. Could the GNBA-to-NBA correctness be expressed as a simulation? 

This is **not recommended** for the current proof. The reason: `gnba_language_eq` proves *language equality* (not just inclusion), which requires both simulation and cosimulation (bisimulation). The current direct proof structure (completeness + soundness) is standard and more appropriate. A simulation-based approach would add complexity without simplifying the proof.

**6c. Decidable automation**:

Could `decide` help with counter stepping? No -- `gnbaK phi` is not a compile-time constant, so `Decidable` instances for counter values are not computable. The counter stepping is inherently about properties of natural number sequences, where `omega` and manual case analysis are the right tools.

**6d. Definitional unfolding strategy**:

Could the proof exploit Lean 4's definitional reduction more aggressively? The `ctr` definition uses `Nat.rec`, and `gnbaNBA.Tr` uses `if-then-else`. If both used the same `Decidable` instance, the counter transition would hold by `rfl` or `simp`. The cleanest fix might be to define `ctr` using `open Classical in` to match `gnbaNBA`:

```lean
open Classical in
let ctr : N -> Fin K.succ := ...
```

This would make the Decidable instances align definitionally, and the counter transition proof would simplify to `exact And.intro (hgnbaTr n) rfl` or similar.

**6e. Finset.sum / combinatorial tools**:

The counter cycling argument does not involve sums or combinatorial identities. It is about ordered visitation of acceptance sets. `Finset.sum` is not applicable. The proof correctly uses `Nat.find` for the minimal witness -- this is the standard approach.

---

## Recommended Approach

1. **Fix the 3 sorries by aligning Decidable instances**: Either define `ctr` inside `open Classical in` (strategy 6d above), or prove the counter transition by case analysis (strategy 4 from the handoff). The former is cleaner; the latter is more robust.

2. **Submit as a single PR** fixing all 3 sorries. No value in intermediate PRs.

3. **Do NOT refactor to a general GNBA type in this PR**. File a follow-up task for general GNBA degeneralization after this PR lands.

4. **Ensure all docstrings are present**, `lake lint` passes, and the PR description includes AI disclosure.

5. **The downstream payoff is immediate**: closing 3 sorries makes `Formula.isRegular` fully proved, which is the headline result of the LTL module.

---

## Evidence and Observations

### Codebase State

| Metric | Value |
|--------|-------|
| GNBA.lean total lines | 1402 |
| Sorries remaining | 3 (lines 1205, 1324, 1359) |
| All in completeness counter cycling | Yes |
| Soundness direction | Fully proven |
| Root cause | Decidable instance mismatch |
| Estimated fix effort | 30-80 lines |

### Downstream Dependencies

| File | Depends on `gnba_language_eq` | Status |
|------|------------------------------|--------|
| `OmegaRegular.lean:364` (`isRegular'`) | Direct | Ready when sorry-free |
| `OmegaRegular.lean:374` (`isRegular_untl`) | Via `isRegular'` | Ready when sorry-free |
| `OmegaRegular.lean:393` (`isRegular`) | Via `isRegular_untl` | Ready when sorry-free |

### Existing CSLib Automata Infrastructure

| Component | Location | Relevance |
|-----------|----------|-----------|
| `NA.Buchi` | `NA/Basic.lean` | State type used by `gnbaNBA` |
| `NA.Buchi.BuchiCongruence` | `Congruences/BuchiCongruence.lean` | Used by complement proof |
| `NA.Buchi.interNA` | `NA/BuchiInter.lean` | 2-set cycling (Bool toggle) |
| `NA.Buchi.reindex` | `NA/BuchiEquiv.lean` | State relabeling |
| `DA.Buchi` | `DA/Buchi.lean` | Deterministic Buchi |
| `NA.Muller` | `NA/Basic.lean` | Muller acceptance (infOcc) |
| `IsRegular.compl` | `OmegaRegularLanguage.lean` | Complement closure |
| `IsRegular.sup/inf` | `OmegaRegularLanguage.lean` | Boolean closure |
| `proof_wanted iff_da_muller` | `OmegaRegularLanguage.lean:262` | McNaughton's theorem |

### Reuse Potential for General GNBA

| Future Consumer | Would Benefit from General GNBA | Priority |
|-----------------|--------------------------------|----------|
| CTL* omega-regularity | Yes (CTL* uses GNBA too) | Medium (CTL* not in CSLib) |
| Rabin automata conversion | Partially | Low |
| General multiple-acceptance NBA | Yes | Medium |
| LTL model checking formalization | No (uses `isRegular` directly) | N/A |
