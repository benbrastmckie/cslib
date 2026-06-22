# Research Report: Task #251

**Task**: Product Construction and Model Checking Reduction
**Date**: 2026-06-20
**Mode**: Team Research (4 teammates)

## Summary

The LTS × NBA product construction and model checking reduction theorem are well-understood mathematically and have excellent infrastructure support in CSLib. All four teammates converge on a standalone product definition (existing products cannot be reused) with the model checking theorem parameterized over any NBA — making it independent of task 242. Three critical design issues were identified by the Critic: (1) the task 242 dependency cited in the seed report is misleading — `gnbaNBA` already exists in GNBA.lean; (2) a `Set Atom` vs `Atom → Prop` type mismatch requires bridge lemmas; (3) CSLib's `LTS` type has no initial states, requiring explicit parameterization. The strategic recommendation is a two-file architecture: a generic product in `Cslib/Foundations/Semantics/LTS/Prod.lean` and the LTL corollary in `Cslib/Logics/LTL/ModelChecking.lean`.

---

## Key Findings

### Primary Approach (from Teammate A)

**Product Definition**: The product `NA.Buchi (LTSState × NBAState) Act` is defined with:
- Transition: `Tr (s, q) α (t, p) := lts.Tr s α t ∧ nba.Tr q (labeling t) p` (NBA reads label of *target* state, per Baier-Katoen Def. 4.62)
- Alternative "reads source" convention: `Tr (s, q) α (t, p) := lts.Tr s α t ∧ nba.Tr q (labeling s) p` with initial states `init ×ˢ nba.start` (simpler, recommended to start with)
- Accept states: `Set.univ ×ˢ nba.accept`

**Proof Strategy**: Three lemmas chaining to the main biconditional:
1. `productWithNBA_run_iff` — run characterization (product run ↔ synchronized LTS execution + NBA run)
2. `productWithNBA_proj` — projection (accepting product run → LTS path satisfying ¬φ)
3. `productWithNBA_lift` — lifting (LTS path satisfying ¬φ → accepting product run)

**Model Checking Theorem**: Parameterized over any NBA with `(h : language nba = (Formula.neg φ).omegaLanguage)`, avoiding task 242 dependency. The unconditional corollary follows from `Formula.isRegular (Formula.neg φ)`.

**Infrastructure**: `LTS.OmegaExecution`, `NA.Buchi`, `SatisfiesExec`, `language_nonempty_iff` (task 248) are all directly usable. No history bit needed (unlike `BuchiInter`).

### Alternative Approaches (from Teammate B)

**Existing products cannot be reused** (confirmed definitively):
- `FLTS.prod` requires both sides to consume the same label `μ`; the LTS × NBA product passes `L(s')` to the NBA, not the LTS transition label. Structural mismatch is definitive.
- `NA.iProd` requires both components to read the same external symbol. The LTS × NBA product has the NBA's input generated *internally* by applying `L` to the successor state — a forward dependency that cannot be expressed in `iProd`.

**`SatisfiesExec` is necessary but not sufficient**: It bridges LTL satisfaction to LTS paths (the system side), but both proof directions still require an explicit product — soundness for projection, completeness for co-induction.

**On-the-fly formalization is out of scope**: Gerth 1995 and Courcoubetis 1992 confirm that on-the-fly is an algorithmic efficiency technique; the correctness argument always reduces to emptiness of the fully-defined product. Separate future task.

**No categorical abstraction warranted**: CSLib has no category-theoretic framework for LTSs; the set-theoretic approach from the literature is the right style.

### Gaps and Shortcomings (from Critic)

**Six gaps identified, three HIGH severity:**

1. **Task 242 dependency is misleading (HIGH)**: The seed report says "task 242 provides LTL-to-NBA" but task 242 is `not_started`. The LTL-to-NBA translation already exists: `Formula.gnbaNBA φ` in `GNBA.lean` is sorry-free and provides `gnba_language_eq`. Task 251 can use `gnbaNBA (neg φ)` today.

2. **`Set Atom` vs `Atom → Prop` type mismatch (HIGH)**: `SatisfiesExec` uses `labeling : State → (Atom → Prop)` while `gnbaNBA` has alphabet type `Set Atom`. These are propositionally but not definitionally equal. Every statement linking the product to `SatisfiesExec` requires rewriting via `Set.mem_def` or a custom bridge lemma.

3. **LTS has no initial states (HIGH)**: `CSLib.LTS` has no `start` field. The product construction assumes initial states `S₀`. Must either parameterize by `init : Set State` or introduce a new type. The minimal approach (parameterize) is recommended.

4. **LTS Label is orthogonal to NBA alphabet (MEDIUM)**: The product transition must existentially quantify over the LTS label: `(∃ μ, lts.Tr s μ s') ∧ nba.Tr q (labeling s') q'`. The seed report glosses over this.

5. **`[Finite State]` required for emptiness theorem (MEDIUM)**: Task 248's `language_nonempty_iff` requires `[Finite State]`, limiting the model checking theorem to finite-state systems (standard for algorithmic model checking but should be explicit).

6. **Scope is ambitious (MEDIUM)**: Full bidirectional proof in one task is tight. The completeness direction threads through the 1484-line `gnba_language_eq` correctness chain. Phase decomposition is advisable.

### Strategic Horizons (from Horizons)

**Pipeline status**: Task 248 (emptiness) is complete; the GNBA construction exists; task 251 is the capstone connecting CSLib's logic and computability tracks.

**Two-file architecture**: The product construction should live in `Cslib/Foundations/Semantics/LTS/Prod.lean` (no LTL dependency) for maximum reusability. The LTL corollary belongs in `Cslib/Logics/LTL/ModelChecking.lean`. This respects CSLib's layer structure and enables future CTL*, HML, and game-based model checking reuse.

**Two-level theorem**: State the model checking result at two levels:
- Level A (generic): ω-regular model checking — product language nonempty ↔ traces intersect NBA language
- Level B (LTL corollary): instantiate with `gnbaNBA (neg φ)`, using `Formula.isRegular`

**No task-242 blocking**: The conditional theorem `ltl_modelChecking_of_nba` with hypothesis `(h : language nba = ...)` is fully provable now. The unconditional version follows immediately from `Formula.isRegular (Formula.neg φ)`.

**KripkeModel wrapper**: Consider a lightweight `KripkeModel` structure bundling LTS + init + labeling, but only if no existing CSLib type covers this. Not strictly necessary — parameters can be passed individually.

---

## Synthesis

### Conflicts Resolved

**1. File location: LTL/Semantics/ vs LTS/Prod.lean**

Teammate A recommends `Cslib/Logics/LTL/Semantics/LTSProduct.lean`. Teammate D recommends splitting into `Cslib/Foundations/Semantics/LTS/Prod.lean` (generic product) and `Cslib/Logics/LTL/ModelChecking.lean` (LTL corollary).

**Resolution: Teammate D's split is correct.** The product construction has no LTL dependency — it takes an arbitrary LTS, labeling function, and NBA. Placing it in `Foundations/` avoids a layering violation (Computability importing Logics) and enables reuse for other logics. However, the existing file `Cslib/Foundations/Semantics/FLTS/Prod.lean` already uses the name `Prod.lean` for FLTS products, so the new file should be `Cslib/Foundations/Semantics/LTS/NAProd.lean` or similar to avoid confusion.

**2. Product transition: reads source vs reads target**

Teammate A recommends starting with "reads source" convention (simpler initial states). Baier-Katoen uses "reads target" (standard). Teammate D follows BK directly.

**Resolution: Use "reads source" convention** (`Tr (s, q) α (t, p) := lts.Tr s α t ∧ nba.Tr q (labeling s) p` with `start := init ×ˢ nba.start`). This aligns with `SatisfiesExec` which evaluates at `ss.head` (position 0), produces simpler initial states, and is mathematically equivalent after a one-step shift. The BK "reads target" convention can be stated as a derived equivalence.

**3. Product symbol type: Act vs Set Atom**

Teammate A defines the product as `NA.Buchi (S × Q) Act`. Teammate C notes the LTS label is orthogonal and must be existentially quantified. Teammate B confirms the product NBA reads `Set Atom`, not `Act`.

**Resolution**: The product should be defined as `NA.Buchi (S × Q) (Set Atom)` (the NBA's alphabet type), with the LTS label existentially quantified in the transition: `Tr (s, q) a (s', q') := (∃ μ, lts.Tr s μ s') ∧ nba.Tr q a q'`. This matches the standard treatment where the product is an ω-automaton over the proposition alphabet.

**Alternative**: Keep `Act` as the product label type if we want the product to track which LTS action was taken (useful for counterexample extraction). This is a design choice that should be resolved during planning.

### Gaps Identified

1. **Bridge lemmas for `Set Atom` ↔ `Atom → Prop`** are needed before the model checking theorem can be stated cleanly. These should be utility lemmas in a shared location.

2. **Initial state handling** must be resolved: parameterize by `init : Set State` (minimal, recommended) or introduce a `KripkeModel` wrapper (cleaner but more scope). The plan should make this choice explicit.

3. **`[Finite S]` hypothesis** must be explicit in the model checking theorem statement. This is standard for algorithmic model checking but should be documented.

4. **Completeness direction complexity**: Threading through `gnba_language_eq` to extract an accepting NBA run from a language membership proof is the most complex proof obligation. The plan should budget for this.

### Recommendations

1. **Two-file architecture**:
   - `Cslib/Foundations/Semantics/LTS/NAProd.lean`: Generic LTS × NBA product (no LTL imports)
   - `Cslib/Logics/LTL/ModelChecking.lean`: LTL model checking reduction (imports product + SatisfiesExec + Emptiness + GNBA)

2. **Parameterize, don't wrap**: Pass `init : Set State` and `labeling : State → Set Atom` as parameters rather than introducing a new `KripkeModel` type. This is minimal-scope and follows CSLib conventions.

3. **Use `Set Atom` throughout**: Unify on `Set Atom` as the labeling type to align with `gnbaNBA`. Provide a thin bridge lemma `satisfiesExec_iff_set` converting between `Atom → Prop` and `Set Atom` representations.

4. **Phase decomposition**:
   - Phase 1: Product definition + run characterization lemmas (~150 lines)
   - Phase 2: Soundness direction (projection) (~100 lines)
   - Phase 3: Completeness direction (lifting via gnba_language_eq) (~200 lines)
   - Phase 4: LTL model checking corollary in ModelChecking.lean (~50 lines)

5. **Do not block on task 242**: Use `gnbaNBA (Formula.neg φ)` directly, or parameterize over any NBA with the right language. Both approaches are fully implementable today.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary approach | completed | High (infrastructure, definition) / Medium (initial state convention) |
| B | Alternatives | completed | High (product uniqueness) / Medium-High (file location) |
| C | Critic | completed | High (all 6 gaps verified by direct code inspection) |
| D | Horizons | completed | High (architecture, pipeline) / Medium (KripkeModel wrapper) |

---

## References

- Baier, C., Katoen, J.-P. *Principles of Model Checking*. MIT Press, 2008. Definition 4.62 (product), Theorem 4.63 (reduction).
  - `~/Projects/Literature/sources/baier_katoen_2008/Baier_Katoen_2008_part03.md`
- Vardi, M.Y. "An automata-theoretic approach to linear temporal logic." LNCS 1043, Springer, 1996. Section 4.2.
  - `~/Projects/Literature/sources/vardi_1996/Vardi_1996_Automata_Theoretic_LTL.md`
- Gerth, R. et al. "Simple on-the-fly automatic verification of LTL." PSTV, 1995.
  - `~/Projects/Literature/sources/gerth_1995/Gerth_1995_OnTheFly_LTL_Verification.md`
- Courcoubetis, C. et al. "Memory-efficient algorithms for the verification of temporal properties." 1992.
  - `~/Projects/Literature/sources/courcoubetis_1992/Courcoubetis_1992_Memory_Efficient_Verification.md`
