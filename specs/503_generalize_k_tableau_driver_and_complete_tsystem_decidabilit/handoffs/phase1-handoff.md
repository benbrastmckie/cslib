# Phase 1 Handoff -- Task 503

## Status: COMPLETED

## What was done

Added a generic tableau driver to `Cslib/Logics/Modal/Tableau/Saturation.lean`:
- `RuleApply Atom` (`@[nolint unusedArguments]` abbrev): the shape of a rule-application
  function matching `modalApplyOne`'s signature.
- `modalStepBranchGen apply b expanded acc`: generic one-step branch expansion.
- `modalExpandBranchesGen apply branches expandedSets accs fuel`: generic fuel-based
  expansion loop (with its own internal `processNext` `let rec`, matching the K original's
  shape).
- `modalTableauGen apply φ`: generic entry point.

K's `modalStepBranch`/`modalExpandBranches`/`modalTableau` were **kept as byte-identical
original recursive definitions** (zero touch) rather than becoming wrappers around the `Gen`
versions. This was a deliberate deviation from the plan's suggested `abbrev`/wrapper mechanism:
wrapping broke 14+ downstream `simp only [modalStepBranch]` call sites and every
`modalExpandBranches.processNext`-referencing proof in `Soundness.lean`/`CompletenessLoop.lean`,
because wrapping changes the auto-generated equation-lemma/internal-helper shape that those
proofs depend on syntactically.

Instead, three bridge theorems were proved (not `@[simp]`, to avoid silently changing existing
bare `simp` call behavior elsewhere):
- `modalStepBranch_eq : modalStepBranch b e a = modalStepBranchGen modalApplyOne b e a` (`rfl`)
- `modalExpandBranches_eq : modalExpandBranches branches expandedSets accs fuel =
  modalExpandBranchesGen modalApplyOne branches expandedSets accs fuel` (induction on `fuel`
  with inner induction on the worklist)
- `modalTableau_eq : modalTableau φ = modalTableauGen modalApplyOne φ` (via
  `modalExpandBranches_eq`)

## Verification (all green, zero regression)

- `lake build Cslib.Logics.Modal.Tableau.Saturation` -- green
- `lake build` (full project, 3216 jobs) -- green, warnings identical to pre-change baseline
- `lake exe checkInitImports` -- clean
- `lake lint` -- 1 pre-existing error (`PrimeExclusion.lean`, unrelated), zero from our files
  (fixed one `unusedArguments` hit on `RuleApply` via `@[nolint unusedArguments]`)
- `lake exe lint-style` -- clean
- `lake shake --add-public --keep-implied --keep-prefix` -- no suggestions for any
  `Modal/Tableau/*.lean` file
- `lake exe mk_all --module` -- no update necessary (no new files yet)
- `lake test` -- exit 0, full `CslibTests/` suite green
- `grep -rn "\bsorry\b\|^axiom " Saturation.lean` -- empty (zero sorry, zero axiom)

## Next phase

Phase 2: create `Cslib/Logics/Modal/Tableau/GenericDriver.lean` with the `RuleApplicationSpec`
structural-hypothesis interface bundle and `modalApplyOne_spec` trivial witness. Field-list
derivation requires reading `FmpMeasure.lean`'s `modalStepBranch_potential_step` (~line 2146)
and `modalStepBranch_worldBound` (~line 2376) proofs to see exactly what concrete
`modalApplyOne` facts they consume.

## Key learning for tasks 504/505/506 and future re-runs

When generalizing a hard-coded recursive driver into a parametrized one, do NOT turn the
original into a wrapper/abbrev around the generic version if any downstream proof references
the original's auto-generated internal helpers (e.g. `foo.processNext`) or relies on
`simp only [foo]`/`unfold foo` producing a specific normal form. Instead: keep the original
verbatim, add the generic version as an independent parallel definition, and bridge them with
an explicit (possibly non-trivial, induction-based) equality theorem. Grep for
`<defname>\.` and `simp.*\[<defname>\]`/`unfold <defname>` across the codebase BEFORE choosing
the wrapper approach, to detect this risk early.
