# Research Report: Until (untl) Case for LTL Omega-Regularity

**Task**: 236 -- Follow-up PRs from PR #649 (Buchi / omega-regular)
**Focus**: Proving `Formula.isRegular_untl` -- the `untl` case of `Formula.isRegular`
**Session**: sess_1781845064_ffa85c

---

## 1. Problem Statement

The file `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` proves `Formula.isRegular` by
structural induction on LTL formulas. All cases are complete except `untl`:

```lean
proof_wanted Formula.isRegular_untl {Atom : Type} [Finite Atom] {φ ψ : Formula Atom}
    (hφ : φ.omegaLanguage.IsRegular) (hψ : ψ.omegaLanguage.IsRegular) :
    (Formula.untl φ ψ).omegaLanguage.IsRegular
```

### Semantics (Standard Convention)

In CSLib's LTL, `untl φ ψ` = `φ U ψ` (standard "phi until psi"):
- `φ` is the **guard** (first argument): holds at all intermediate positions
- `ψ` is the **event** (second argument): holds at the witness position

This matches the standard LTL semantics where `p U q` means "p holds until q becomes true."
Verified by: `someFuture φ = .untl .top φ` (guard = top, event = phi, so phi eventually
holds -- consistent with standard F operator).

The satisfaction at position `i` (from the `Satisfies` definition, where Lean pattern-match
binders shadow the `proof_wanted` variable names):
```lean
| .untl ψ φ => ∃ j ≥ i, Satisfies v j φ ∧ ∀ k, i ≤ k → k < j → Satisfies v k ψ
```

Here the Lean binder `ψ` binds the first constructor argument (guard) and `φ` binds the
second (event). In the `proof_wanted`, `φ` is the guard (first arg) and `ψ` is the event
(second arg). The guard is vacuously satisfied when `j = i` (event happens immediately).

**Note**: Some docstrings in the codebase reference "Burgess convention" but the code
implements standard LTL semantics. Use the code semantics above, not the docstrings.

At position 0 (the `omegaLanguage` definition):
```
v ∈ L(untl φ ψ) ↔ ∃ j ≥ 0, (v.drop j ∈ L(ψ)) ∧ (∀ k < j, v.drop k ∈ L(φ))
```

where `v.drop k ∈ L(φ)` follows from `satisfies_shift` (already proved in the file).

---

## 2. Why This Case Is Hard

Unlike `atom`, `bot`, `imp`, and `next`, the `untl` case cannot be reduced to a simple
composition of existing omega-regular closure operations. The fundamental difficulty:

### 2.1 The Guard Is an Omega-Property

"φ holds at position k" (`v.drop k ∈ L(φ)`) is an **omega-language membership** check on
the suffix starting at k. This is NOT a single-letter predicate. If φ contains temporal
operators (nested until/next), checking φ at position k requires examining the entire
infinite suffix `v(k), v(k+1), v(k+2), ...`.

### 2.2 No Finite-Word Decomposition

One might hope: `L(untl φ ψ) = L_guard * L(ψ)` for a regular finite-word language L_guard.
This fails because the guard check at position k depends on the infinite continuation,
not just the finite prefix `v[0..k)`.

### 2.3 Countable Union Problem

The natural decomposition is:

```
L(untl φ ψ) = ⋃_{j≥0} (⋂_{k<j} next^k(L(φ))) ∩ next^j(L(ψ))
```

Each term is omega-regular (finite intersection + next preserve omega-regularity). But this
is a **countable union** of omega-regular languages, and omega-regular languages are NOT
closed under countable union in general.

### 2.4 Fixed-Point Recursion

The expansion law `L(untl φ ψ) = L(ψ) ∪ (L(φ) ∩ next(L(untl φ ψ)))` characterizes
`L(untl φ ψ)` as the least fixed point of `F(Z) = L(ψ) ∪ (L(φ) ∩ next(Z))`.
While F maps omega-regular languages to omega-regular languages, the least fixed point
of such an operator is not guaranteed to be omega-regular (the omega-regular languages
don't form a complete sublattice).

---

## 3. Existing CSLib Infrastructure

### 3.1 Omega-Regular Closure Operations (All Proved)

| Operation | Declaration | Status |
|-----------|-------------|--------|
| Empty (⊥) | `IsRegular.bot` | Done |
| Full (⊤) | `IsRegular.top` | Done |
| Union (⊔) | `IsRegular.sup` | Done |
| Intersection (⊓) | `IsRegular.inf` | Done |
| Complement (ᶜ) | `IsRegular.compl` | Done |
| Finite union (⨆) | `IsRegular.iSup` | Done |
| Finite intersection (⨅) | `IsRegular.iInf` | Done |
| Concat (L * P) | `IsRegular.hmul` | Done |
| Omega-power (L^ω) | `IsRegular.omegaPow` | Done |
| Omega-limit (L↗ω) | `IsRegular.regular_omegaLim` | Done |
| Saturating cover | `IsRegular.fin_cover_saturates` | Done |

### 3.2 NBA Construction Primitives

| Construction | File | Purpose |
|-------------|------|---------|
| `NA.concat` | `NA/Concat.lean` | Concatenate FinAcc with NA |
| `FinAcc.loop` | `NA/Loop.lean` | Omega-power (loop construction) |
| `interNA` | `NA/BuchiInter.lean` | Intersection with toggle history |
| `NA.iSum` | `NA/Sum.lean` | Union of indexed family |
| `NA.iProd` | `NA/Prod.lean` | Product of indexed family |
| `NA.addHist` | `NA/Hist.lean` | Add history/tracking state |
| `NA.Buchi.reindex` | `NA/BuchiEquiv.lean` | Reindex state space |

### 3.3 Key Existing Theorems

- `satisfies_shift`: `Satisfies v (i+k) φ ↔ Satisfies (fun n => v (n+k)) i φ`
- `omegaLanguage_next`: `L(Xφ) = { xs | xs.tail ∈ L(φ) }`
- `nextNBA_language_eq`: language of `nextNBA na` = `{ xs | xs.tail ∈ language na }`
- `concat_language_eq`: language of `concat na1 na2` = `language na1 * language na2`
- `inter_language_eq`: language of `interNA na acc` = `⨅ i, language (na i, acc i)`
- `eq_fin_iSup_hmul_omegaPow`: every omega-regular language = `⨆ i, L_i * M_i^ω`

### 3.4 Finite-Word Regular Language Operations

| Operation | Declaration | Status |
|-----------|-------------|--------|
| Complement | `Cslib.Language.IsRegular.compl` | Done |
| Intersection | `Cslib.Language.IsRegular.inf` | Done |
| Union | `Cslib.Language.IsRegular.add` | Done |
| Concat | `Cslib.Language.IsRegular.mul` | Done |
| Kleene star | `Cslib.Language.IsRegular.kstar` | Done |
| Empty | `Cslib.Language.IsRegular.zero` | Done |
| Epsilon | `Cslib.Language.IsRegular.one` | Done |

---

## 4. Proof Approaches Analyzed

### 4.1 Approach A: Direct NBA Construction (RECOMMENDED)

**Idea**: Build a custom NBA `untlNBA` whose language equals `(untl φ ψ).omegaLanguage`,
following the pattern of `atomNBA` and `nextNBA` in the existing file.

**Construction sketch**: Given NBAs `na_φ` (states `S_φ`) for L(φ) and `na_ψ` (states `S_ψ`)
for L(ψ):

The NBA for `untl φ ψ` has state space `(S_φ ⊕ S_ψ)` with a "mode" flag:

- **Guard mode**: Running a copy of `na_φ`. At each step, nondeterministically either:
  - Continue the current `na_φ` run (stay in guard mode)
  - Switch to event mode: transition to an `na_ψ` start state
- **Event mode**: Running `na_ψ`. Accept via `na_ψ`'s acceptance condition.

The acceptance condition enforces that:
1. Eventually we switch to event mode (the event ψ must happen)
2. Once in event mode, `na_ψ` accepts (ψ holds at the switch position)

**Key challenge**: The guard check requires verifying that `na_φ` ACCEPTS the suffix from
each position k < j. A single run of `na_φ` from position 0 does not establish acceptance
of each individual suffix. This is the core technical difficulty.

**Resolution via nondeterminism**: The NBA nondeterministically "checks" the guard at each
position by tracking the set of `na_φ`-states reachable from `start_φ` at the current
position. This uses a power-set construction (subset of S_φ), yielding state space
`Set S_φ × (S_ψ ⊕ Unit)`, which is finite when S_φ and S_ψ are finite.

Concretely:
- State: `(Finset S_φ) × Option S_ψ`
  - `Finset S_φ` = current "frontier" of possible na_φ-states (started fresh at this position + advanced from previous positions)
  - `Option S_ψ` = `none` (guard mode) or `some s_ψ` (event mode, tracking na_ψ state)
- Transition on letter `a`:
  - Guard mode `(F, none)`: advance F via na_φ transitions, add start_φ (fresh guard check for next position). Nondeterministically switch to event mode by choosing `some s_ψ` with `s_ψ ∈ start_ψ`.
  - Event mode `(F, some s_ψ)`: advance s_ψ via na_ψ transitions. The F component is irrelevant (or can be dropped).
- Start: `({start_φ}, none)` -- though needs adjustment for the `j = 0` case (event immediately)
- Accept: `(_, some s_ψ)` where `s_ψ ∈ accept_ψ`

**Issue with this construction**: The `Finset S_φ` component tracks reachable states but does
not verify ACCEPTANCE of na_φ on the suffixes. An omega-word where na_φ has a run (reaches
states) but never accepts would still pass the guard check.

**Fix**: Add an acceptance obligation. The guard mode must verify that for each position k < j,
the run of na_φ started at position k visits accept_φ infinitely often (or at least once before
position j). For a finite prefix (positions k to j-1), this simplifies to: the run visits
accept_φ at least once. This can be tracked with an additional boolean per active run.

But tracking acceptance of multiple simultaneous runs requires exponential state space and
is complex. This leads to:

**Practical assessment**: The direct NBA construction with full guard verification is
feasible but involves:
- State space: `Finset (S_φ × Bool) × Option S_ψ` (exponential in |S_φ|)
- Complex transition function
- Lengthy correctness proof (hundreds of lines)

**Effort estimate**: 15-25 hours of implementation work.

### 4.2 Approach B: Compositional via concat + complement (ALTERNATIVE)

**Idea**: Express `L(untl φ ψ)` using the existing concat, complement, and intersection
operations.

**Key decomposition**:

```
L(untl φ ψ) = ⋃_j { v | v.take j ∈ L_guard_j ∧ v.drop j ∈ L(ψ) }
```

where `L_guard_j = { w : [Set Atom]^j | ∀ k < j, the suffix from position k satisfies φ }`.

This `L_guard_j` is NOT a standard finite-word language because the check "suffix from k
satisfies φ" depends on the infinite continuation.

However, if we use the `eq_fin_iSup_hmul_omegaPow` decomposition of L(φ) and L(ψ) into
finite unions of `L_i * M_i^ω`, we can express the guard condition in terms of finite-word
language operations on the L_i and M_i components.

**Practical assessment**: This approach reduces the problem to showing that the "until"
combination of `⨆_i L_i * M_i^ω` terms is itself a finite union of `L' * M'^ω` terms.
This is doable but requires substantial algebraic manipulation of finite-word languages
and omega-powers.

**Effort estimate**: 20-30 hours.

### 4.3 Approach C: Büchi Congruence Saturation (MOST CSLib-NATIVE)

**Idea**: Use the existing `IsRegular.fin_cover_saturates` framework. Construct a finite
cover of omega-regular languages that saturates `L(untl φ ψ)`, then conclude
omega-regularity.

**Key insight**: From the NBAs for φ and ψ, form the product automaton A_prod running both
in parallel. The Büchi congruence of A_prod partitions omega-words into finitely many
equivalence classes. If `L(untl φ ψ)` is a union of these equivalence classes, we're done.

**Challenge**: Proving saturation requires showing that if two omega-words are in the same
Büchi congruence class of A_prod, then either both or neither satisfy `untl φ ψ`. This
is NOT obvious because the congruence classes depend on the pair (L(φ), L(ψ)) behavior,
not on the Until combination.

**Practical assessment**: Would require proving new lemmas about how Büchi congruences
interact with the Until operator. The saturation framework is powerful but was designed
for complement, not for arbitrary combinations.

**Effort estimate**: 15-20 hours.

### 4.4 Approach D: Fixed-Point with Finite Stabilization (CLEANEST IF FEASIBLE)

**Idea**: Show that the fixed-point iteration `Z_{n+1} = L(ψ) ∪ (L(φ) ∩ next(Z_n))`
stabilizes after finitely many steps when the alphabet is finite.

**Mathematical basis**: Over a finite alphabet, the lattice of omega-regular languages is
Noetherian modulo the Büchi congruence. The operator F preserves omega-regularity (proved
using `IsRegular.sup`, `IsRegular.inf`, and `isRegular_next`). If the ascending chain
Z_0 ⊂ Z_1 ⊂ Z_2 ⊂ ... stabilizes, the fixed point is omega-regular.

**Stabilization argument**: Each Z_n is omega-regular, recognized by some NBA of bounded
size (each application of F increases the state count by a bounded amount). Over a finite
alphabet, there are only finitely many omega-regular languages recognizable by NBAs with
at most N states. So the chain must stabilize.

**Issue**: The state count bound grows with n (each `next` + `inf` + `sup` operation at least
doubles the state space). So the chain Z_n has NBAs with state counts growing like
O(|S_φ|^n * |S_ψ|), which does NOT stabilize.

**Resolution**: Use the Büchi congruence to quotient the state space. After quotienting, there
are only finitely many behaviors. But formalizing this requires the full Büchi congruence
theory applied to the Until operator.

**Practical assessment**: Mathematically elegant but requires formalizing the stabilization
argument, which is as hard as the direct construction.

**Effort estimate**: 20-25 hours.

---

## 5. Recommended Strategy

### Primary Recommendation: Approach A (Direct NBA Construction)

The direct NBA construction is recommended because:

1. **Follows existing pattern**: `atomNBA` and `nextNBA` in the same file set the precedent
2. **Self-contained**: No new infrastructure files needed; everything goes in `OmegaRegular.lean`
3. **Well-understood**: The standard LTL-to-Büchi construction is textbook material
4. **Reuses existing primitives**: Can use `addHist` for obligation tracking, `iProd` for
   product states, or build from scratch like `nextNBA`

### Simplified Construction (Recommended Variant)

Instead of the full power-set construction (Approach 4.1), use the following observation:

**The guard condition can be absorbed into the event check via the expansion law.**

Define the NBA `untlNBA na_φ na_ψ` with states `S_φ × S_ψ × {guard, event}`:

1. **Start in both modes simultaneously**: Initial states include both:
   - `(s_φ, s_ψ, guard)` for `s_φ ∈ start_φ, s_ψ ∈ start_ψ` (check φ while waiting)
   - `(s_φ, s_ψ, event)` for `s_φ ∈ start_φ, s_ψ ∈ start_ψ` (j = 0 case: event immediately)

2. **Guard mode transitions**: `(s_φ, s_ψ, guard) →[a] (s_φ', s_ψ', mode')` where:
   - `na_φ.Tr s_φ a s_φ'` (advance φ-run)
   - `s_ψ' ∈ start_ψ` (reset ψ-tracking to start for potential event at next position)
   - `mode' = guard` (continue guard) OR
   - `mode' = event` (nondeterministically switch to event at next position)
   - Also: `na_φ.Tr s_φ a s_φ'` and `na_ψ.Tr s_ψ a s_ψ'` with `mode' = event`
     (switch mid-step)

3. **Event mode transitions**: `(s_φ, s_ψ, event) →[a] (s_φ', s_ψ', event)` where:
   - `na_ψ.Tr s_ψ a s_ψ'` (advance ψ-run)
   - `s_φ'` arbitrary (φ-component unused in event mode)

4. **Acceptance**: `(s_φ, s_ψ, event)` where `s_ψ ∈ accept_ψ`

**Correctness intuition**: The NBA nondeterministically guesses the event position j. Before j,
it runs na_φ to "verify" φ, but the key subtlety is that the na_φ run from position 0
doesn't directly verify φ at each individual position.

**THIS CONSTRUCTION HAS A SOUNDNESS GAP**: The na_φ run from position 0 verifies that na_φ
has some run, but not that it ACCEPTS (visits accept_φ infinitely often). For the guard
check, we need φ to HOLD at each position, which requires na_φ to accept the suffix.

### Addressing the Gap: Two Sub-Approaches

**Sub-approach A1**: Accept the gap and add an acceptance check for na_φ. This requires:
- An additional acceptance condition: in guard mode, accept_φ must be visited infinitely often
- Use the `interNA` toggle mechanism to check both "na_φ accepts in guard mode" and
  "na_ψ accepts in event mode"
- This creates a GNBA (two acceptance sets); convert to NBA using the existing
  `interNA`/`interAccept` pattern

**Sub-approach A2**: Use the `concat` construction. Define:
- `untlNBA na_φ na_ψ` via `concat na_guard na_ψ` where `na_guard` is a FinAcc (finite acceptor)
  that accepts exactly the prefixes `[a_0, ..., a_{j-1}]` such that φ holds at positions
  0, ..., j-1.
- The `na_guard` accepts a prefix `w` iff for every suffix that could follow w, na_φ would
  accept when started at each position k < |w|.
- This is the power-set / subset-construction approach on finite prefixes.

**Sub-approach A2 is cleaner** because it reduces the Until problem to:
1. Constructing `na_guard` (a FinAcc for the guard prefixes)
2. Using the existing `concat_language_eq` to combine with na_ψ

### Phase Structure Recommendation

Given the complexity, split the `untl` case into sub-phases:

**Phase 3a**: Prove `omegaLanguage_untl` -- the semantic equation:
```lean
(Formula.untl φ ψ).omegaLanguage = ⟨{ v | ∃ j, v.drop j ∈ ψ.omegaLanguage ∧
    ∀ k < j, v.drop k ∈ φ.omegaLanguage }⟩
```
This uses `satisfies_shift` and should be straightforward (10-20 lines).

**Phase 3b**: Construct `untlNBA` and prove `untlNBA_language_eq`.

**Phase 3c**: Prove `Formula.isRegular_untl` using the NBA from Phase 3b.

---

## 6. Alternative: Defer to proof_wanted

If the full NBA construction proves too complex within the task scope, the existing
`proof_wanted` pattern is acceptable. The remaining four cases (atom, bot, imp, next) are
already proved and independently valuable. The main theorem `Formula.isRegular` currently
uses `sorry` for the `untl` case, and the `proof_wanted` clearly documents the gap.

This option should be considered if the implementation estimate exceeds the available time.

---

## 7. Tactic Survey Results

For the `omegaLanguage_untl` semantic equation (Phase 3a), the following tactics are relevant:
- `satisfies_shift` for converting between positional and suffix-based formulations
- `simp only [mem_omegaLanguage, Satisfies]` for unfolding definitions
- `ext` / `ωLanguage.mem_ext` for language equality
- `omega` for arithmetic inequalities on indices

For the NBA construction (Phase 3b), the `atomNBA` and `nextNBA` proofs provide templates:
- `constructor` / `refine ⟨_, _, _⟩` for existential witnesses
- `cases` / `rcases` / `match` for state case analysis
- `frequently_atTop` for Büchi acceptance conditions
- `grind` for automata-level reasoning (used extensively in `Concat.lean`)

---

## 8. External References

### Standard LTL-to-Büchi Construction

The standard references for the Until case in LTL-to-Büchi translation:

1. **Vardi-Wolper (1986)**: "An automata-theoretic approach to automatic program verification"
   -- Original LTL-to-NBA construction via tableau/graph-based method.

2. **Gerth et al. (1995)**: "Simple on-the-fly automatic verification of linear temporal logic"
   -- The GPVW algorithm; standard implementation basis. Uses graph-based node expansion.

3. **Baier & Katoen**: "Principles of Model Checking", Chapter 5
   -- Textbook treatment of LTL-to-GNBA-to-NBA conversion.

### Verified Constructions

4. **Schimpf, Merz, Smaus (2009)**: "Construction of Büchi Automata for LTL Model Checking
   Verified in Isabelle/HOL" -- Full Isabelle verification of the Gerth et al. algorithm.

5. **LeanLTL (2025)**: "A unifying framework for linear temporal logics in Lean" (arXiv:2507.01780)
   -- Recent Lean 4 formalization; scope and coverage of the Until case not confirmed.

---

## 9. Summary

| Approach | Effort | Risk | CSLib Fit |
|----------|--------|------|-----------|
| A: Direct NBA | 15-25h | Medium | High (follows atomNBA/nextNBA pattern) |
| B: Compositional | 20-30h | High | Medium (needs algebraic manipulation) |
| C: Saturation | 15-20h | Medium | High (uses existing framework) |
| D: Fixed-point | 20-25h | High | Medium (needs stabilization proof) |
| Defer (proof_wanted) | 0h | None | High (already done) |

**Primary recommendation**: Approach A (direct NBA construction), using the `concat`
primitive (Sub-approach A2) where possible. The semantic equation (Phase 3a) should be
proved first as a foundation, then the NBA constructed and its language equality proved.

**Fallback**: Keep the existing `proof_wanted` and `sorry` if the construction exceeds
the available scope. The four completed cases are independently valuable.
