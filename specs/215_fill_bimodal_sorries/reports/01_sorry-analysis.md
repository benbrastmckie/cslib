# Sorry Analysis: Task 215 — Fill Bimodal Sorry Declarations

## Summary

22 sorry declarations across 6 files, all annotated with blocking task references. After analysis of each goal state against the available BX axiom system, **all 22 sorries are genuinely blocked** on upstream dependencies. None can be filled with the current axiom set.

The sorries divide into two categories:
- **9 sorries blocked on task 37** (strict Until/Since semantics gap): Axioms BX8/BX8'/BX9/BX9' and temporal-T for G/H were removed as unsound under strict (irreflexive) Until/Since semantics. All 9 sorries require at least one removed axiom.
- **13 sorries blocked on task 36** (discrete completeness pipeline): Depend on upstream BimodalLogic infrastructure (GoodStructuresModelSurgery, discrete_embed_strictMono) that has not been ported or developed.

## Complete Sorry Table

| # | File | Line | Goal | Blocker | Strategy | Difficulty |
|---|------|------|------|---------|----------|------------|
| 1 | Bundle/SuccRelation.lean | 256 | `((ψ ∨ φ ∧ ψ U φ) U ⊥) ∈ M` | Task 37 | Requires BX9 (Until elimination) — removed | BLOCKED |
| 2 | Bundle/SuccRelation.lean | 261 | `((ψ ∨ φ ∧ ψ S φ) S ⊥) ∈ M` | Task 37 | Requires BX9' (Since elimination) — removed | BLOCKED |
| 3 | Bundle/SuccRelation.lean | 267 | `(ψ U φ) ∈ v` | Task 37 | Requires until_unfold + g_content_subset | BLOCKED |
| 4 | Bundle/SuccRelation.lean | 273 | `(ψ U φ) ∈ M` from `(ψ ∨ φ ∧ ψ U φ) ∈ M` | Task 37 | Requires BX8 (reflexive Until intro) — removed | BLOCKED |
| 5 | Bundle/SuccRelation.lean | 279 | `(ψ S φ) ∈ M` from `(ψ ∨ φ ∧ ψ S φ) ∈ M` | Task 37 | Requires BX8' — removed | BLOCKED |
| 6 | Bundle/SuccRelation.lean | 283 | `gContent u ⊆ u` | Task 37 | Requires G(φ) → φ (temporal-T) — invalid under strict G | BLOCKED |
| 7 | Bundle/SuccRelation.lean | 287 | `hContent u ⊆ u` | Task 37 | Requires H(φ) → φ — invalid under strict H | BLOCKED |
| 8 | Bundle/UntilSinceCoherence.lean | 39 | `(ψ U φ) ∈ M` from `ψ ∈ M` | Task 37 | Requires BX8 (reflexive Until intro) — removed | BLOCKED |
| 9 | Bundle/UntilSinceCoherence.lean | 43 | `(ψ S φ) ∈ M` from `ψ ∈ M` | Task 37 | Requires BX8' (reflexive Since intro) — removed | BLOCKED |
| 10 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 73 | `False` from gap hypothesis | Task 36 | Requires gap_contradicts_prior from GoodStructuresModelSurgery | BLOCKED |
| 11 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 143 | `forward_G` field of `discreteFmcs` | Task 36 | Requires discrete_embed_strictMono | BLOCKED |
| 12 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 144 | `backward_H` field of `discreteFmcs` | Task 36 | Requires discrete_embed_strictMono | BLOCKED |
| 13 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 150 | `LimitDomSubtype → ℤ` function | Task 36 | Requires Z-isomorphism construction | BLOCKED |
| 14 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 155 | `FMCS Atom ℤ fc` construction | Task 36 | Requires succEmbed + Z-iso | BLOCKED |
| 15 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 160 | `(rootedSuccDiscreteFmcs ...).mcs s = N` | Task 36 | Depends on sorry #14 | BLOCKED |
| 16 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 170 | `nonempty` field of `cantorBfmcsDiscrete` | Task 36 | Depends on sorry #14 | BLOCKED |
| 17 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 171 | `modal_forward` of `cantorBfmcsDiscrete` | Task 36 | Depends on sorry #14 | BLOCKED |
| 18 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 172 | `modal_backward` of `cantorBfmcsDiscrete` | Task 36 | Depends on sorry #14 | BLOCKED |
| 19 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 173 | `evalFamily` of `cantorBfmcsDiscrete` | Task 36 | Depends on sorry #14 | BLOCKED |
| 20 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 174 | `eval_family_mem` of `cantorBfmcsDiscrete` | Task 36 | Depends on sorry #14 | BLOCKED |
| 21 | BXCanonical/Chronicle/ChronicleToCountermodel.lean | 185 | `∃ countermodel` (discrete case) | Task 36 | Entire discrete pipeline | BLOCKED |
| 22 | BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean | 825 | `∃ countermodel` (dense case, universe) | Task 36 | Universe mismatch with ParametricCanonicalTaskFrame | BLOCKED* |

Additional sorries referenced in task description but not in the original count:

| # | File | Line | Goal | Blocker | Strategy | Difficulty |
|---|------|------|------|---------|----------|------------|
| A | BXCanonical/Completeness/Dense.lean | 122 | `False` from `countermodel_dense` | Task 36 | Depends on sorry #22 | BLOCKED |
| B | BXCanonical/Frame.lean | 160 | `bxLe w w` (= `gContent w ⊆ w`) | Task 37 | Same as sorry #6 (temporal-T) | BLOCKED |

## Detailed Analysis by Category

### Category A: Task 37 — Strict Until/Since Semantics Gap (9 sorries)

**Root Cause**: The BX axiom system underwent a transition from reflexive to strict (open guard) Until/Since semantics. Under strict semantics:
- `F(φ) = φ U ⊤` means "φ at some **strictly future** time"
- `G(φ) = ¬F(¬φ)` means "¬φ never at any strictly future time" — says nothing about the present
- `P(φ) = φ S ⊤` means "φ at some **strictly past** time"
- `H(φ) = ¬P(¬φ)` says nothing about the present

Three axiom families were removed as unsound under strict semantics:
1. **BX8/BX8'** (reflexive intro): `ψ → (ψ U φ)` / `ψ → (ψ S φ)` — ψ holding now does not entail a strictly future witness
2. **BX9/BX9'** (Until/Since elimination): `(ψ U φ) → (ψ ∨ φ)` / `(ψ S φ) → (ψ ∨ φ)` — Invalid under open guard semantics
3. **Temporal-T** for G/H: `G(φ) → φ` / `H(φ) → φ` — G is non-reflexive (strict future only)

All 9 task-37 sorries require at least one of these removed axioms. The dependency graph:

```
BX8 (removed) ← backward_until_reflexive (#8), or_until_in_mcs (#4)
BX8' (removed) ← backward_since_reflexive (#9), or_since_in_mcs (#5)
BX9 (removed) ← until_unfold_in_mcs (#1)
BX9' (removed) ← since_unfold_in_mcs (#2)
temporal-T (invalid) ← g_content_subset_mcs (#6), h_content_subset_mcs (#7)
until_unfold + g_content_subset ← until_persists_through_succ (#3)
```

**Resolution Path**: Task 37 is blocked on upstream BimodalLogic development of continuous completeness. The semantic gap requires either:
- Restoring reflexivity (e.g., moving to weak Until where `t ≤ s` replaces `t < s`)
- Or reworking the completeness proof to avoid these lemmas entirely

### Category B: Task 36 — Discrete Completeness Pipeline (13 sorries)

**Root Cause**: The discrete case requires infrastructure from `WeakCanonical.IntegerModel.GoodStructuresModelSurgery` which has not been ported from the upstream BimodalLogic project. The upstream project itself has 36 sorries in this area.

**Dependency Graph**:
```
gap_contradicts_prior (upstream) ← chronicle_gap_contradiction (#10)
    ← succ_cofinal ← limitDomSubtypeIsSuccArchimedean
    ← orderIsoIntOfLinearSuccPredArch (Mathlib, available)
    ← succEmbed (#13)
    ← discreteFmcs (#11, #12)
    ← rootedSuccDiscreteFmcs (#14)
    ← rooted_succ_discrete_fmcs_at_s (#15)
    ← cantorBfmcsDiscrete (#16-#20)
    ← dd_countermodel_chronicle_discrete (#21)
```

**Sorry #22 (countermodel_dense) is special**: The comment says "universe mismatch with ParametricCanonicalTaskFrame." This is potentially fixable independently of task 36 by adjusting universe levels — `ParametricCanonicalTaskFrame` requires `Atom : Type` but the file uses `Atom : Type*` (universe polymorphic). However, fixing this universe issue alone doesn't resolve the downstream `completeness_dense` sorry (#A), which also needs the discrete case or a proof that the discrete case never arises under Dense frame class.

**Sorry #A (completeness_dense)**: The Dense.lean sorry at line 122 is in the `h_box_dense` case of the completeness theorem. Despite being in the "dense" branch, it requires `countermodel_dense` which has the universe mismatch. The other branch (non-dense) is already handled by the `dense_indicator` axiom. So this sorry is actually **close to provable** if the universe issue in `countermodel_dense` is resolved.

### Category C: Frame.lean Reflexivity (1 sorry, overlapping with Category A)

**Sorry #B (bx_le_refl)**: `bxLe w w` where `bxLe w v = gContent w.formulas ⊆ v.formulas`. This is exactly `gContent w.formulas ⊆ w.formulas`, identical to sorry #6 (`g_content_subset_mcs`). Both require `G(φ) → φ` which is invalid under strict semantics.

## Implementation Phases

Since all sorries are genuinely blocked, there are no implementation phases. Instead, the task should be marked as **BLOCKED** with the following resolution path:

### Recommended Actions

1. **Mark task 215 as BLOCKED** with dependencies on tasks 36 and 37
2. **For the universe mismatch (sorry #22)**: Create a separate task to fix the `Type*` vs `Type` issue in `ParametricCanonicalTaskFrame`. This is likely a focused fix that adjusts universe annotations and could unblock `countermodel_dense` and `completeness_dense`.
3. **For the strict semantics gap (task 37 sorries)**: These require upstream development of a completeness proof that works under strict Until/Since. This is the most fundamental blocker.
4. **For the discrete pipeline (task 36 sorries)**: These require porting ~6 files from upstream BimodalLogic after the upstream sorry elimination completes.

### Possible Exception: Completeness Dense Case

If the universe mismatch in `countermodel_dense` (#22) is fixed, then `completeness_dense` (#A in Dense.lean:122) becomes provable:

```lean
-- Dense case: □(F'T) ∈ M — invoke countermodel_dense (now universe-fixed)
obtain ⟨D, _, _, _, _, TF, TM, Omega, hSC, τ, hτ, t, hfalse⟩ :=
    Chronicle.countermodel_dense FrameClass.Dense A hM_mcs φ h_neg_in h_box_dense
-- But φ is validDense, so truthAt holds everywhere — contradiction
exact hfalse (h_valid_dense D ‹_› ‹_› ‹_› ‹_› TF TM Omega hSC τ hτ t)
```

This would require verifying that the `validDense` quantifier matches the existential from `countermodel_dense`, which needs universe alignment.

## Risk Assessment

| Risk | Impact | Likelihood |
|------|--------|------------|
| Task 37 remains blocked indefinitely | High — 9 sorries, core Until/Since properties | Medium — fundamental semantic issue |
| Task 36 remains blocked indefinitely | High — 13 sorries, entire discrete pipeline | Medium — upstream has 36 sorries |
| Universe fix introduces new issues | Low — isolated change | Low — well-understood problem |
| Strict semantics invalidates completeness approach | Critical — would require major rewrite | Low — Burgess/Reynolds theory well-established |
