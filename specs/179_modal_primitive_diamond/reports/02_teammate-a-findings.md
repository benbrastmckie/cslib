# Teammate A Findings: Primary Approach for Primitive Diamond

## Task 179 — Primitive Diamond for Modal.Proposition

## Key Findings

### 1. Is `dia` Needed? — Current State Assessment

**The current `Proposition` type has exactly `{atom, bot, imp, box}` as primitives.**

However, the task description says `{atom, bot, imp, and, or, box, dia}` is the target. This is
important: the current type does NOT have `and` or `or` as primitive constructors either. They are
encoded via Lukasiewicz abbreviations:
- `¬φ := φ → ⊥`
- `φ ∧ ψ := ¬(φ → ¬ψ)` (i.e., `(φ → (ψ → ⊥)) → ⊥`)
- `φ ∨ ψ := ¬φ → ψ`
- `◇φ := ¬□¬φ` (i.e., `(□(φ → ⊥)) → ⊥`)

The task description's claimed target `{atom, bot, imp, and, or, box, dia}` appears aspirational.
Adding `and` and `or` as primitive constructors would require a much larger restructuring than adding
only `dia`. This report focuses on adding `dia` alone, which is the smaller and more justified change.

**Existing problems caused by derived diamond:**

1. **Axiom D encoding is fragile**: In `ProofSystem/Instances/D.lean`, the `modalD` constructor
   type is spelled out as `(□φ).imp ((□(φ.imp .bot)).imp .bot)` because Lean needs the full
   syntactic expansion. The comment says `where ◇φ = (□(φ → ⊥)) → ⊥`. This is correct for
   classical K, but the encoding is non-idiomatic.

2. **Axiom B encoding**: In `DerivationTree.lean` and in axiom predicates (B, KB5, TB, DB, S5),
   the B axiom `φ → □◇φ` is spelled out as `φ.imp (Proposition.box (Proposition.diamond φ))`,
   which expands to `φ.imp (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot))`. This
   expansion appears in every system that has B, and it requires the reader to mentally unfold the
   notation.

3. **Axiom 5 encoding**: `◇φ → □◇φ` unfolds to a deeply nested expression (both occurrences
   of `◇φ` expand), making it cognitively harder to match against the semantic proof.

4. **Completeness proofs**: In `Completeness.lean` and `D/Completeness.lean`, the diamond-expanded
   forms require explicit reasoning steps that comment on the expansion (`-- diamond(neg phi) = ...`).
   These comments appear 5+ times across files, indicating the expansion creates cognitive overhead.

5. **No current breakage**: There are no proof failures or `sorry`s due to derived diamond.
   All current classical modal logics (K through S5) are complete and sound with the derived form.
   The problems are all *anticipatory*: they will become real when adding intuitionistic modal logics.

**Would adding `dia` now introduce unnecessary complexity?**

No, for two reasons:
- The overhead of adding `dia` is bounded: it requires adding one match arm per inductive over
  `Proposition`. The codebase currently has approximately 15 such inductives spread across 8 files.
- The benefit is immediate: all axiom encoding becomes simpler and more readable. Axiom D, B, 5
  can all be written using `◇` directly without internal expansion.

### 2. Upstream Comparison

**Confirmed from prior research**: Upstream CSLib uses `{atom, not, and, diamond}` as primitives,
deriving box classically. This is the opposite extreme from the fork. Having both as primitive is
the correct design for supporting non-classical logics.

However, a critical observation: the upstream convention cannot be directly imported here because
the fork's axiom system is box-centric (all the classical modal axioms use `□` as the primary
modality). Making `dia` primitive does not require any change to the axiom style — axioms remain
box-primary, but the `◇` abbreviation is now backed by a primitive constructor rather than an
encoding.

### 3. File Impact Analysis

**Files requiring modification when adding `dia` constructor:**

| File | Change | Complexity |
|------|--------|-----------|
| `Basic.lean` | Add `.dia` constructor to `Proposition`; add `Satisfies` case `\| .dia φ => ∃ w', ...`; drop `diamond` abbreviation (or keep as backward alias) | Low |
| `Denotation.lean` | Add `.dia` case to `Proposition.denotation` | Low |
| `LogicalEquivalence.lean` | Add `.dia` constructor to `Proposition.Context`; add `.dia` case in `fill`; add `.dia` case in `congruence` induction | Low |
| `Cube.lean` | Add `.dia` case to any induction (if any); update any axiom statements using `◇` | Low |
| `Metalogic/DerivationTree.lean` | The axiom types use `Proposition.diamond` which will now be a constructor call — this is a **non-change** if `diamond` remains an abbrev pointing to `.dia`. But if `dia` is added as a constructor, `ModalAxiom.modalB` needs no change (it uses `Proposition.diamond`). | None if abbrev maintained |
| `ProofSystem/Instances/*.lean` (15 files) | Axiom constructors using `◇` notation change syntactic form only if `diamond` abbreviation is dropped. If `diamond` remains pointing to `.dia`, NO change needed. | None if abbrev maintained |
| `Metalogic/Soundness.lean` | `soundness` theorem induction over `DerivationTree` — no match on `Proposition`. | None |
| `Metalogic/Completeness.lean` | `truth_lemma` and variants do induction on `Proposition` with cases `atom`, `bot`, `imp`, `box`. Need `.dia` case added. | Medium (3 truth lemma families) |
| `Metalogic/Systems/*/Soundness.lean` (15 files) | Axiom soundness proofs match on axiom constructors, not on `Proposition`. No change needed. | None |
| `Metalogic/Systems/*/Completeness.lean` (15 files) | Completeness proofs call `truth_lemma`/`k_truth_lemma`/`truth_lemma_d`. If those have `.dia` cases, no change in individual system completeness files. | None |
| `FromPropositional.lean` | The `toModal` embedding uses `Proposition` constructors. Only if it references `diamond` directly. | Check needed |

**Actual impact is much smaller than report 01 estimated (55 files)**. Key insight:

The critical observation is that `truth_lemma` does **pattern matching on `Proposition`**. Currently
it has 4 cases: `atom`, `bot`, `imp`, `box`. Adding `dia` as a primitive requires a 5th case in
the truth lemma and its two variants (`k_truth_lemma` and `truth_lemma_d`). This is the main work.

**Revised impact: 6-10 files need substantive changes**, the rest need either no change or trivial
abbreviation updates.

### 4. The Key Implementation Decision: Diamond as Abbrev vs. Constructor

**Option A (Recommended): Add `.dia` constructor, keep `diamond` as `abbrev` pointing to `.dia`**

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Proposition Atom)
  | box (φ : Proposition Atom)
  | dia (φ : Proposition Atom)  -- NEW: primitive diamond
  deriving DecidableEq, BEq

-- Keep backward-compatible abbreviation:
abbrev Proposition.diamond (φ : Proposition Atom) : Proposition Atom := .dia φ
```

This approach:
- Zero breaking changes: all existing code uses `Proposition.diamond` which now maps to `.dia`
- The `◇` notation continues to work unchanged
- Satisfies clause becomes: `| .dia φ => ∃ w', m.r w w' ∧ Satisfies m w' φ`
- The existing `diamond_iff` theorem becomes definitionally true (not just classically true)
- Truth lemmas need a `.dia` case, but it is trivial: same as what `diamond_iff` currently proves

**Option B: Make `diamond` the primary name for the constructor**

```lean
  | diamond (φ : Proposition Atom)
```

This breaks all existing pattern matches that use `Proposition.diamond` if they use dot-notation
in matches. Less clean, more breakage. Not recommended.

**Option C: Change nothing about the abbreviation structure**

Simply add `.dia` constructor but route `Proposition.diamond` to it. Same as Option A.

### 5. The Truth Lemma Extension

The `.dia` case in the truth lemma is the most substantive new proof obligation:

```lean
| .dia φ => by
  constructor
  · intro h_sat
    -- h_sat : ∃ w', m.r S.val w' ∧ Satisfies (CanonicalModel) ⟨w', ?⟩ φ
    -- Use IH to get φ ∈ w'.val
    -- Need: dia φ ∈ S.val
    -- This requires an "existence lemma": if dia φ ∉ S, find MCS T with neg(dia φ) ∈ T
    -- But neg(dia φ) = box(neg φ), so if dia φ ∉ S, box(neg φ) ∈ S by negation completeness
    -- Then any accessible world T has neg φ ∈ T, contradicting φ ∈ T
    sorry
  · intro h_dia T hST
    -- h_dia : dia φ ∈ S.val
    -- hST : (CanonicalModel).r S T (i.e., ∀ ψ, box ψ ∈ S → ψ ∈ T)
    -- Need: Satisfies (CanonicalModel) T φ
    -- From dia φ ∈ S.val, we know ∃ T, box_accessible and φ ∈ T
    -- But hST gives: T is accessible from S. We need φ ∈ T.
    -- PROBLEM: dia φ ∈ S does NOT directly give φ ∈ any box-accessible world
    -- The classical canonical model has R S T iff ∀ψ, □ψ ∈ S → ψ ∈ T
    -- If dia φ ∈ S (= neg(box(neg φ)) ∈ S), then box(neg φ) ∉ S
    -- So neg φ ∉ T for all box-accessible T... but we need φ ∈ T
    sorry
```

**Critical insight**: The classical truth lemma for `◇φ` does NOT require a new case when `◇` is
derived, because it reduces to the `box` case through `diamond = neg(box(neg))`. When `dia` becomes
primitive, the truth lemma for `.dia` requires the **"diamond witness lemma"**: if `dia φ ∈ S`
(with `S` being an MCS), then there exists a box-accessible world `T` containing `φ`.

In the **classical K context**, this diamond witness follows from the derivable equivalence
`◇φ ↔ ¬□¬φ`: if `dia φ ∈ S` and we can show `dia φ = ¬□¬φ` holds in the MCS, then
`□¬φ ∉ S`, and the K-specific box witness applied to `¬φ` gives a box-accessible `T` with
`¬φ ∉ T`, i.e., `φ ∈ T` by negation completeness.

This chain is sound but requires:
1. The theorem that `dia φ ↔ ¬□¬φ` holds classically (i.e., Peirce's law axiom)
2. The `mcs_neg_of_not_mem` lemma already in MCS.lean
3. The existing box witness lemmas

**The truth lemma for `.dia` is not trivial but is provable without sorry using existing MCS
infrastructure.** It requires adding:
- A lemma `mcs_dia_exists`: if `dia φ ∈ S` and S is classically MCS, then the K-style
  box-accessible witness `T` (satisfying `∀ψ, □ψ ∈ S → ψ ∈ T`) contains `φ`

This lemma connects primitive `.dia` back to the box-centric canonical accessibility relation.

### 6. Timing: Before or After First Upstream PR?

**Recommendation: After the first PR.**

Reasoning:
- Task 175 (Propositional PR readiness, which this depends on) and the first PR submission are
  the immediate priority
- The `dia` change is purely additive and backward-compatible (with Option A)
- It does not break any existing soundness/completeness theorems
- Adding it now would make the PR for the existing classical logics larger and harder to review
- The first PR demonstrates the fork's value; `dia` adds complexity without a use-site yet

**However**, if the plan is to include intuitionistic modal logics in the same PR, then `dia`
must come first. Given that the current scope is classical logics only, deferring `dia` is correct.

### 7. Risks and Tradeoffs

**Risk of adding `dia` now:**
- The truth lemma for `.dia` in the classical context requires a non-trivial new proof
  (the diamond witness lemma). This is the main implementation risk.
- The implementation across ~8 files must be done consistently to avoid sorry.
- The `DecidableEq` instance derived automatically will include `.dia` correctly, but if any
  file has explicit `DecidableEq` recursion, it needs a new case.

**Risk of NOT adding `dia` now:**
- All future work on modal logics carries the cognitive overhead of the nested expansion
- When intuitionistic modal logics are eventually added, the change will be required and will
  touch many more files (because the intuitionistic base has its own connective infrastructure)
- The upstream CSLib divergence grows, making eventual merging harder

**Cost of NOT adding `dia` for the CURRENT PR:**
- Zero. The current classical systems (K through S5) are all sound, complete, and fully proved.
- The derived diamond is classically correct for all 13 classical systems currently formalized.

## Recommended Approach

**Do not add `dia` in the current PR.** Instead:

1. Submit the existing classical modal logic formalization (K through S5) as the first PR
2. Open a follow-up task (task 180 or similar) specifically for adding primitive `dia`
3. In that follow-up task, use Option A (`.dia` constructor + `diamond` abbreviation pointing
   to it) to minimize breaking changes
4. The key proof obligation is: add `.dia` case to `truth_lemma`, `k_truth_lemma`,
   `truth_lemma_d` in Completeness.lean and K/Completeness.lean, D/Completeness.lean
5. Add `mcs_dia_exists` lemma to MCS.lean connecting `dia φ ∈ S` to box-witness accessibility

**If `dia` is required before the PR** (e.g., if the first PR scope includes systems that
reference diamond as primitive), then:

1. Start with `Basic.lean`: add `.dia` constructor, add `Satisfies` case
2. Add `dia` case to `Denotation.lean` and `LogicalEquivalence.lean`
3. Add `mcs_dia_exists` to `MCS.lean`
4. Add `.dia` case to all three truth lemma families in `Completeness.lean`,
   `K/Completeness.lean`, `D/Completeness.lean`
5. Verify: `lake build Cslib.Logics.Modal` and run all tests

Estimated implementation effort: 2-3 hours of focused Lean work.

## Evidence / Examples

**Current axiom D encoding (non-idiomatic):**
```lean
-- In ProofSystem/Instances/D.lean
| modalD (φ : Proposition Atom) :
    DAxiom (Proposition.imp (Proposition.box φ)
      (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot)) Proposition.bot))
```
Comment says `□φ → ◇φ where ◇φ = (□(φ → ⊥)) → ⊥`.

**With primitive `.dia`, this would become:**
```lean
| modalD (φ : Proposition Atom) :
    DAxiom (Proposition.imp (Proposition.box φ) (Proposition.dia φ))
```
The axiom D statement `□φ → ◇φ` becomes transparent.

**Current truth lemma: no `.dia` case needed (it unfolds through `.imp` and `.box`):**
```lean
| .imp φ ψ => ...  -- handles ◇φ = (□(φ→⊥))→⊥ via the imp and box cases
```

**With primitive `.dia`, the truth lemma needs:**
```lean
| .dia φ => by
  constructor
  · intro ⟨T, hST, hφ_T⟩  -- IH on φ
    -- diamond witness: from T accessible, φ ∈ T, conclude dia φ ∈ S
    -- via: box(neg φ) ∉ S → dia φ ∈ S (classical reasoning in MCS)
    ...
  · intro h_dia T hST
    -- from dia φ ∈ S, find witness T containing φ (mcs_dia_exists)
    ...
```

## Confidence Level

- **Is `dia` needed eventually?** High confidence: Yes. Intuitionistic modal logics cannot
  be formalized without primitive diamond.
- **Are there current proofs breaking?** High confidence: No. All 13 classical systems are
  complete and sound with derived diamond.
- **Best approach?** High confidence: Option A (`.dia` constructor + backward-compatible
  `diamond` abbreviation).
- **Timing: before or after first PR?** Medium-high confidence: After. The current scope
  does not require primitive diamond, and adding it increases the first PR's scope unnecessarily.
- **Truth lemma proof difficulty?** Medium confidence: The `.dia` case is non-trivial but
  provable using existing MCS infrastructure. Main new lemma needed: `mcs_dia_exists`.
- **Total file impact?** High confidence: 6-10 files, not 55. The key insight is that
  `ProofSystem/Instances/*.lean` and `Metalogic/Systems/*/Soundness.lean` and Completeness
  files do NOT need changes because they don't induct on `Proposition`.
