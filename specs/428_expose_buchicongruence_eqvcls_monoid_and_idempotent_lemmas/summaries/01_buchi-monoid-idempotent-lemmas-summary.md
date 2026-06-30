# Implementation Summary: Task #428

- **Task**: 428 - expose_buchicongruence_eqvcls_monoid_and_idempotent_lemmas
- **Status**: [IMPLEMENTING] -> [PR READY]
- **Phases Completed**: 2/2
- **File Modified**: `Cslib/Computability/Languages/Congruences/BuchiCongruence.lean`

## What Was Implemented

Added 86 lines to `BuchiCongruence.lean` after `buchiFamily_saturation`, providing the full
monoid structure on `Quotient na.BuchiCongruence.eq` and the algebraic lemmas needed by
downstream tasks 429 and 241.

### Phase 1: Monoid Structure [COMPLETED]

**`buchiCongruence_left_cov`** (helper lemma):
- Proves left covariance: if `na.BuchiCongruence.eq u u'` then `na.BuchiCongruence.eq (w ++ u) (w ++ u')`.
- Proof uses explicit splitting via `LTS.pairLang_split` and `LTS.pairViaLang_split`, combining with
  `LTS.pairLang_append`, `LTS.pairViaLang_append_pairLang`, and `LTS.pairLang_append_pairViaLang`.

**`buchiCongruence_instMonoid`** (instance):
- Defines `Monoid (Quotient na.BuchiCongruence.eq)` with:
  - `mul a b := Quotient.liftOn₂ a b (fun u v => ⟦u ++ v⟧) ...` (well-defined by right + left covariance)
  - `one := ⟦[]⟧`
  - `mul_assoc`: via `Quotient.inductionOn` + `List.append_assoc`
  - `one_mul`: `rfl` (since `[] ++ u = u` definitionally)
  - `mul_one`: via `List.append_nil`

**`buchiCongruence_mk_append`** (simp lemma, deliverable 1):
- States `(⟦u ++ v⟧ : Quotient na.BuchiCongruence.eq) = ⟦u⟧ * ⟦v⟧`
- Proved via `Quotient.liftOn₂_mk`
- Tagged `@[simp]` for downstream use

### Phase 2: Idempotent-Power and Absorption Lemmas [COMPLETED]

**`buchiCongruence_pow_succ`** (helper):
- `b * b = b → ∀ n, b ^ (n + 1) = b`
- Proved by induction: base `simp`, step `simp only [pow_succ, ih, hb]`

**`buchiCongruence_idempotentPow`** (deliverable 2):
- `b * b = b → k ≠ 0 → b ^ k = b`
- Delegates to `buchiCongruence_pow_succ` after pattern-matching `k = succ n`

**`buchiCongruence_absorption`** (deliverable 3):
- `b * b = b → a * b = a → ∀ k, a * b ^ k = a`
- `k = 0`: `simp` (uses `b ^ 0 = 1` and `a * 1 = a`)
- `k = n + 1`: `rw [buchiCongruence_pow_succ hb, hab]`

## Plan Deviations

- **`IsIdempotentElem.pow_eq` not available**: The idempotent-power collapse was planned to use
  `IsIdempotentElem.pow_eq` from `Mathlib.Algebra.Group.Idempotent`, but that module is not
  transitively imported. Instead, proved `buchiCongruence_pow_succ` manually by induction and
  derived `buchiCongruence_idempotentPow` from it. Result: same API, no new import needed.
- **`grind` for left covariance failed**: The plan suggested using grind with the same hints as
  `right_cov.elim`, but grind could not canonicalize `na.BuchiCongruence.eq` against the
  synthesized `List.isSetoid Symbol` instance. Replaced with an explicit proof using the
  `pairLang_split`/`pairLang_append`/`pairViaLang_split`/`pairViaLang_append_pairLang`/
  `pairLang_append_pairViaLang` lemmas directly.
- **`private` conflicted with `@[expose] public section`**: Removed `private` from left covariance;
  the lemma is now public. This is consistent with all other declarations in the section.

## CI Verification Results

- `lake build Cslib.Computability.Languages.Congruences.BuchiCongruence`: PASS (clean, no warnings)
- `lake exe checkInitImports`: PASS (no issues for BuchiCongruence)
- `lake lint` (BuchiCongruence-specific): PASS (no docBlame/defLemma/simpNF/defsWithUnderscore warnings)
- `lake exe lint-style`: PASS (no style issues)
- `lake shake --add-public --keep-implied --keep-prefix`: PASS (no BuchiCongruence issues)
- `lake exe mk_all --module`: PASS (no new files; BuchiCongruence already listed)
- Sorry count in modified file: 0
- New axioms introduced: 0
- Full `lake test`: Pre-existing failure in `Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness` (unrelated to task 428)

## Artifacts

- **Modified**: `/home/benjamin/Projects/cslib/Cslib/Computability/Languages/Congruences/BuchiCongruence.lean` (86 lines added)
- **Plan**: `specs/428_expose_buchicongruence_eqvcls_monoid_and_idempotent_lemmas/plans/01_buchi-monoid-idempotent-lemmas.md`
- **Summary**: `specs/428_expose_buchicongruence_eqvcls_monoid_and_idempotent_lemmas/summaries/01_buchi-monoid-idempotent-lemmas-summary.md` (this file)
