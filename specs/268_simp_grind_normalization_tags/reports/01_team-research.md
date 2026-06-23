# Research Report: Task #268

**Task**: simp_grind_normalization_tags
**Date**: 2026-06-22
**Mode**: Team Research (4 teammates, 3 completed, 1 timed out)

## Summary

CSLib uses a well-established three-tier co-tagging convention for simp/grind attributes. This task targets ~15 lemmas across 4 files that currently have `@[simp]` only (missing `scoped grind =`) or have no tags at all. The changes are low-risk with zero impact on existing simp proofs, but the GrindLint test (`CslibTests/GrindLint.lean`) may require new `#grind_lint skip` entries for some newly tagged lemmas.

## Key Findings

### Three-Tier Tagging Convention

CSLib follows a consistent pattern evidenced across `HML/Basic.lean`, `Modal/Basic.lean`, `Modal/Denotation.lean`, `Modal/Cube.lean`, and `OmegaSequence/Init.lean`:

| Lemma Character | Attribute | Example |
|----------------|-----------|---------|
| Definitional equality (`X = Y`, structural unfolding) | `@[simp, scoped grind =]` | `listImp_nil`, `Proposition.denotation` |
| Iff characterization (`X ↔ Y`) | `@[scoped grind =]` (no simp) | `Satisfies.or_iff_or`, `derivation_def` |
| Inductive def for grind case-split | `@[scoped grind]` (no `=`) | `Satisfies`, `Parallel.fvar` |

The `simp` tag is withheld from iff characterizations because simp would loop on the bidirectional rewrite. The `=` variant of grind uses iffs as directed rewrites.

### Target Files and Lemmas

#### File 1: `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` (HIGH PRIORITY)
**Action**: Upgrade `@[simp]` to `@[simp, scoped grind =]`
- `listImp_nil` (line ~51): `listImp [] φ = φ`
- `listImp_cons` (line ~54): `listImp (ψ :: Ψ) φ = HasImp.imp ψ (listImp Ψ φ)`

These are rfl-proved structural equalities — the canonical co-tag pattern.

#### File 2: `Cslib/Foundations/Logic/Theorems/BigConj.lean` (HIGH PRIORITY)
**Action**: Upgrade `@[simp]` to `@[simp, scoped grind =]`
- `bigconj_nil` (line ~72): `bigconj [] = HasBot.bot`
- `bigconj_singleton` (line ~76)
- `bigconj_cons_cons` (line ~79)
- `negBigconj_def` (line ~87)

#### File 3: `Cslib/Logics/Temporal/FromPropositional.lean` (MEDIUM PRIORITY)
**Action**: Upgrade `@[simp]` to `@[simp, scoped grind =]`
- `PL.Proposition.toTemporal_atom` (line ~69)
- `PL.Proposition.toTemporal_bot` (line ~74)
- `PL.Proposition.toTemporal_imp` (line ~79)
- `PL.Proposition.toTemporal_and` (line ~84)
- `PL.Proposition.toTemporal_or` (line ~90)

#### File 4: `Cslib/Logics/Modal/Basic.lean` (MEDIUM PRIORITY, OPTIONAL)
**Action**: Add `@[scoped grind =]` only (NOT `@[simp]`) to unwrapped characterization lemmas:
- `Satisfies.neg_iff`
- `Satisfies.diamond_iff`
- `Satisfies.and_iff`
- `Satisfies.or_iff`

**Note**: The `⇓Modal[...]`-wrapped versions at lines 199-232 already have `@[scoped grind =]`. Adding tags to the unwrapped versions is safe but may be redundant. Implementer should decide based on whether grind encounters the unwrapped forms.

### Explicit Exclusions

**Do NOT tag** (derivability constructors and proof-search targets):
- All `Derivable.ax`, `Derivable.mp`, `Derivable.nec`, `Derivable.weaken` across PL, Modal, Temporal, Bimodal
- `Derivable.lift` (frame-class monotonicity — not definitional)
- `Derivable.ofTree` (coercion — could cause simp to fire on `Nonempty.intro` patterns)
- Height lemmas (`height_modus_ponens_left`, etc.)
- `propDerivationSystem`, `modalDerivationSystem` (struct constructors)
- `swapTemporal_*` lemmas (used only in targeted `simp only [...]` calls)
- Substitution lemmas in `Bimodal/ProofSystem/Substitution.lean` (targeted simp, not grind)

### Risk Assessment

**Simp loop risk**: None. All derived connectives are `abbrev` (already kernel-transparent). No inverse lemma pairs exist for any target lemma. Adding `scoped grind =` to existing `@[simp]` lemmas does not change simp behavior — the two tactic engines are independent.

**Existing proof breakage**: Zero. Adding `scoped grind =` is purely additive. The `scoped` qualifier limits activation to files that open the relevant namespace.

**GrindLint test risk**: HIGH. `CslibTests/GrindLint.lean` already has `#grind_lint skip` entries for `Cslib.Logic.Modal.neg_denotation`, `Cslib.Logic.Modal.Satisfies.and_iff_and`, and `Cslib.Logic.Modal.Satisfies.or_iff_or`. New `scoped grind =` annotations may trigger grind lint failures requiring new skip entries. The implementer must run `lake test` after each batch and add skip entries as needed.

**simpNF lint risk**: Low. All target lemmas are `theorem` declarations with clean structural LHS. The `defLemma` linter won't trigger. One precedent exists for `@[simp, nolint simpNF, scoped grind =]` in `BuchiClosure.lean` line 96, but the target lemmas should not need it.

## Synthesis

### Conflicts Resolved

1. **Modal `Satisfies.*_iff` redundancy**: Teammate A recommends adding `@[scoped grind =]` to unwrapped versions; Teammate B notes the wrapped `⇓Modal[...]` versions are already tagged, making this potentially redundant. **Resolution**: Mark as optional/medium priority. The wrapped versions are the canonical grind targets; unwrapped versions are harmless but may be unnecessary.

2. **Bimodal Substitution.lean scope**: Teammate A flagged these at low priority; Teammate B explicitly recommends leaving as `@[simp]` only since they're used in targeted `simp only` calls. **Resolution**: Exclude from this task — not in the normalization/definitional layer.

### Gaps Identified

1. **`ListDeduction.lean` and `SetDeduction.lean`**: Critic recommends checking these Foundation metalogic files for any structural `@[simp]`-appropriate lemmas. They may contain `listImp`-adjacent definitions.

2. **15 Modal system instance files**: All 15 per-system files (K, T, D, S4, S5, TB, KB5, D4, D5, D45, DB, B, K4, K5, K45) in `Modal/ProofSystem/` are in scope. The implementation must not limit to K alone. However, these files may only contain instance registrations (no lemmas to tag).

3. **Teammate D (Horizons) timed out**: Strategic alignment and cross-system consistency analysis was not completed. The key unanswered question is whether other logic systems (e.g., Intuitionistic, Epistemic) should get similar treatment in future tasks.

### Recommendations

1. **Process in dependency order**: ListImplication → BigConj → FromPropositional → Modal/Basic
2. **Run `lake build` between each file** to catch simpNF violations early
3. **Run `lake test` after all changes** to check GrindLint — be prepared to add skip entries
4. **Run full CI pipeline** (`lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`) before considering complete

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (file inventory, lemma catalog) | completed | high |
| B | Alternatives (Mathlib conventions, risks, strategies) | completed | high |
| C | Critic (scope gaps, boundary cases, CI risks) | completed | high |
| D | Horizons (strategic alignment) | timed out | n/a |

## References

- `Cslib/Logics/HML/Basic.lean` — canonical co-tagging example
- `Cslib/Logics/Modal/Basic.lean` lines 189-232 — iff characterization pattern
- `Cslib/Logics/Modal/Cube.lean` — 15 modal logic definitions with `@[scoped grind =]`
- `Cslib/Foundations/Data/OmegaSequence/Init.lean` — 15+ structural equalities with `@[simp, scoped grind =]`
- `CslibTests/GrindLint.lean` — grind lint skip entries (CI risk reference)
- `Cslib/Computability/Automata/DA/BuchiClosure.lean` line 96 — `nolint simpNF` precedent
