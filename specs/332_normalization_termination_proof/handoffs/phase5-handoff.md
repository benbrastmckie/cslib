# Task 332 — Phase 5+6 Handoff (FINAL integration: port + re-point + CI)

Status: **COMPLETE for Normalization/** — zero sorries, green build, axiom-clean.

## What was done

1. **Ported** `Normalization/TerminationScratch.lean` → `Normalization/Termination.lean`
   (the constructive, height-free strong-normalization development: L3/L4/L5 mutual block,
   L6 `snForm`, supporting lemmas, and `exists_stronglyNormal_form`).
2. **Deleted the fuel theorem** `Theory.Derivation.normalize_isStronglyNormal` (the sole `sorry`).
   Renamed the `SCRATCH` section header and updated the module docstring `## Main Results`
   to advertise `exists_stronglyNormal_form` instead of the retired fuel theorem.
3. **Made `exists_stronglyNormal_form` public** (dropped `private`); smart-eliminator helpers
   remain private.
4. **Re-pointed** `Normalization/SubformulaProperty.lean`'s `subformula_property` to consume
   `exists_stronglyNormal_form` (constructive, height-free) instead of the fuel theorem;
   updated its docstring.
5. **Deleted** `Normalization/TerminationScratch.lean` (`git rm`).
6. **Lint cleanup** in the ported code: removed 8 `unnecessarySeqFocus` (`<;>`→sequencing,
   linter-verified single-goal), wrapped 2 over-long `decreasing_by` lines, moved the
   `maxHeartbeats` rationale comment to immediately follow the `set_option … in`, added
   `omit [DecidableEq Atom] in` to the six `cx_*` complexity lemmas, and converted three
   `show` (let-unfolding, defeq) to `change`.

## Verification (Normalization/)

- `lake build …Normalization.SubformulaProperty` (transitively builds Termination): **GREEN**,
  no "declaration uses sorry".
- `grep` real `sorry`/`admit` in `Normalization/*.lean`: **0** (only "sorry-free" prose remains).
- `#print axioms subformula_property` and `exists_stronglyNormal_form`:
  `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`, no new axioms**.
- `lake exe lint-style`: **EXIT 0** (pass).
- Barrel (`Cslib.lean`): `Normalization.Termination` present, `TerminationScratch` absent — correct.

## Residual (non-blocking, not enforced by runnable gates)

- 2 info-level `linter.flexible` nags in Termination.lean (`simp [isStronglyNormal]; exact ha`
  at the two neutral `impE` base cases). Left as-is: converting to `simp only` needs the exact
  lemma set and risks the proof for an info-level linter not checked by `lake exe lint-style`.

## Whole-project CI gates blocked by UNRELATED pre-existing breakage

`lake exe checkInitImports`, `lake lint`, `lake test`, and `lake shake` all require a fully
built project. The full `lake build` fails on modules **outside task 332's territory** and
unrelated to this diff (which touches only `Normalization/`):

- `Cslib/Logics/Bimodal/Metalogic/Separation/{Duality,Eliminations}.lean`,
  `…/DedekindZ/QLemma.lean`, `Cslib/Logics/Bimodal/Theorems/Perpetuity/Bridge.lean`,
  `Cslib/Logics/Modal/Tableau/Soundness.lean` (`simp made no progress`, `unsolved goals`,
  `Type mismatch`).

None of these import `Normalization`. The team lead pre-acknowledged "unrelated modules may be
independently red; ensure Normalization/ is clean." Normalization is clean and green. The Init
import chain for the changed files is byte-for-byte the previously-passing header
(Termination→Reduction→Basic→…→Cslib.Init), so checkInitImports is satisfied for this module in
principle; its project-wide failure is solely the missing unrelated `Bridge.olean`.

`lake exe mk_all --module` wanted to add two unrelated files to the barrel
(`Metalogic.IntFMPSpike`, `Semantics.Algebra.BrouwerianCompletenessGeneric`) left out by other
in-flight tasks; that change was reverted as out-of-scope (it does not concern Normalization).

## Commits
- `115b7ffe` task 332 phase 5: port constructive normal form, re-point subformula_property, retire fuel sorry
- `93d2635f` task 332 phase 6: clear lint warnings in ported normalization
