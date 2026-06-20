# Research Report: Task #254

**Task**: Revise LTL conventions on main to conform to standard semantic definitions
**Date**: 2026-06-19
**Mode**: Team Research (4 teammates)

## Summary

The feature branch `feat/temporal-formula-propositional` (commit 3e147123) made LTL-focused changes for a PR. Porting those changes to main requires careful scoping because main has a richer typeclass hierarchy (Modal, Temporal, Bimodal) that the feature branch removed for PR simplicity. The task description is partially misleading: the `untl` argument order in CODE is identical on both branches — only docstrings and notation symbols change. The `Satisfies.lean` rewrite to `ωSequence State` is the highest-impact change, cascading into 3 downstream files totaling ~1900 lines.

## Key Findings

### 1. The `untl` argument order does NOT change in code (all 4 teammates confirm)

Both branches have identical constructor usage:
- `someFuture φ = .untl .top φ` (first arg = guard/⊤, second arg = event/φ)
- Axioms.lean confirms: BX2G = guard monotonicity (first arg varies), BX3 = event monotonicity (second arg varies)

Main's docstrings incorrectly label this as "Burgess: event U guard" (implying first=event). The feature branch corrects to "guard U event" (first=guard). This is a **docstring fix**, not a semantic change. The task description's "change untl argument order" is misleading.

### 2. Connectives.lean must be ADDITIVE, not subtractive (teammates B, C, D)

The feature branch removed `HasBox`, `HasSince`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives` because the PR branch only contained LTL files. On main, these are actively used by:

| Class | Used by |
|-------|---------|
| `HasBox` | 14 `ModalHilbert` proof system classes, `Necessitation` rule, `Theorems/Modal/*` |
| `HasSince` | `TemporalBXHilbert`, `BimodalTMHilbert`, `Axioms.lean` temporal section, `TemporalDerived.lean` |
| `ModalConnectives` | `Modal/Basic.lean` instance registration |
| `TemporalConnectives` | `Temporal/Syntax/Formula.lean` instance registration |
| `BimodalConnectives` | `Bimodal/Syntax/Formula.lean` instance registration |

**Correct approach**: ADD `FutureTemporalConnectives` and `LTLConnectives` alongside existing classes. Do NOT remove existing classes. The task description says "remove HasSince/TemporalConnectives/BimodalConnectives" but this would break the build.

### 3. Satisfies.lean rewrite cascades into 3 files (teammates A, B, C)

Changing from `Satisfies (v : ℕ → (Atom → Prop)) (i : ℕ)` to `Satisfies (v : Atom → State → Prop) (w : ωSequence State)` breaks:

| File | Lines | Satisfies refs | Complexity |
|------|-------|---------------|------------|
| `OmegaExecutionSatisfies.lean` | 108 | Bridge definition | Low — may simplify |
| `OmegaRegular.lean` | 404 | 22 refs, `satisfies_shift` lemma | Medium |
| `GNBA.lean` | 1423 | 41 refs, `canonicalAtom` construction | High |

Options: (a) update all 3 files to new API, or (b) remove them from `Cslib.lean` as the feature branch did and defer to follow-up tasks.

### 4. Notation changes are safe but have minor risks

| Change | Risk |
|--------|------|
| `U → 𝓤` | `𝓤` is Mathlib's `uniformity` symbol (scoped to `[Uniformity]`). No immediate clash but latent risk. |
| `◇, □` for LTL | Already defined in `Modal/Basic.lean` and `Bimodal/Syntax/Formula.lean`. All scoped — no clash unless both namespaces opened together. |
| `◯` for next | No conflict found. |
| `⇝` for leadsto | New, no conflict. |

### 5. Scope clarification: LTL-only, not whole hierarchy

The task should ONLY touch:
- `Cslib/Logics/LTL/` files (Formula, Satisfies, Embedding, downstream semantics)
- `Cslib/Foundations/Logic/Connectives.lean` (additive changes only)

The task should NOT touch:
- `Cslib/Logics/Temporal/` (has own Burgess-based proof system)
- `Cslib/Logics/Modal/` (14 ModalHilbert classes depend on HasBox)
- `Cslib/Logics/Bimodal/` (BimodalConnectives instance is load-bearing)
- `Cslib/Foundations/Logic/ProofSystem.lean`, `Axioms.lean`, `Theorems/`

## Synthesis

### Conflicts Resolved

1. **Teammate A vs C on "argument order change"**: Both agree code is identical; only docstrings change. A's initial framing suggested a semantic change but the detailed analysis confirms docstring-only. **Resolution**: docstring fix, not semantic change.

2. **Task description vs feature branch on Connectives.lean scope**: Task says "remove HasSince/TemporalConnectives/BimodalConnectives". All teammates agree this would break main. **Resolution**: additive changes only — add FutureTemporalConnectives and LTLConnectives, keep existing classes.

3. **Teammate B's "no semantic inversion" vs A's "argument-order mismatch"**: Both are correct when read carefully. The constructor positions haven't changed; only the English labels (guard vs event) in docstrings are swapped. **Resolution**: update docstrings to standard convention labels, no code changes to constructor order.

### Gaps Identified

1. **Satisfies cascade strategy not decided**: Should downstream files (GNBA, OmegaRegular, OmegaExecutionSatisfies) be updated or removed from Cslib.lean? This is a major scoping decision.

2. **references.bib**: `BaierKatoen2008` is cited in GNBA.lean and Emptiness.lean but missing from `references.bib`. Burgess entries should NOT be removed (used by Temporal/Bimodal modules).

3. **Embedding.lean**: Needs docstring updates to reference new ωSequence model. Code stays unchanged.

### Recommendations

**Phased approach**:

**Phase 1 — Notation + docstrings** (low risk, no cascade):
- Formula.lean: notation symbols, docstring convention labels, add leadsto
- Embedding.lean: docstring updates only
- Connectives.lean: add FutureTemporalConnectives/LTLConnectives, update docstrings (keep all existing classes)

**Phase 2 — Satisfies rewrite** (high risk, cascades):
- Satisfies.lean: ωSequence State + valuation rewrite
- OmegaExecutionSatisfies.lean: update bridge definition
- OmegaRegular.lean: rewrite with ωSequence operations
- GNBA.lean: rewrite canonicalAtom and all proofs

**Alternative**: Phase 2 could instead remove OmegaExecutionSatisfies, OmegaRegular, and GNBA from Cslib.lean (matching the feature branch) and defer their ωSequence port to separate tasks.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary: file-by-file diff | completed | high |
| B | Alternatives: downstream impacts | completed | high |
| C | Critic: verification and gaps | completed | high |
| D | Horizons: strategic scoping | completed | high |

## References

- Feature branch commit: 3e147123 (feat/temporal-formula-propositional)
- [Pnueli1977] — standard LTL semantics
- [VardiWolper1986] — automata-theoretic approach
- [BaierKatoen2008] — model checking (missing from references.bib, cited in GNBA)
