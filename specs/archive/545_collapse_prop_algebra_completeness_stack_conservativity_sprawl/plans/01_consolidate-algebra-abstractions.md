# Implementation Plan: Consolidate Propositional Algebra Completeness Stack & Conservativity Sprawl

- **Task**: 545 - Collapse propositional-algebra completeness stack and fragment-conservativity sprawl
- **Status**: [COMPLETED]
- **Effort**: 8 hours
- **Dependencies**: None (task 393 boundary confirmed disjoint — see Overview)
- **Research Inputs**: specs/545_collapse_prop_algebra_completeness_stack_conservativity_sprawl/reports/01_algebra-consolidation-research.md
- **Artifacts**: plans/01_consolidate-algebra-abstractions.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is a **mechanical, zero-new-mathematics refactor** of `Cslib/Logics/Propositional/Semantics/Algebra/`.
Every term relocated or parameterized is an existing sorry-free proof; no proof is re-derived and
no `sorry`/`admit`/vacuous def is introduced. Two consolidations are performed, in the
research-recommended order (Part B first, the cleaner win; Part A second, narrower):

- **Part B — fragment-conservativity sprawl**: four fragment files realize the *same* four-theorem
  skeleton, differing only in the fragment predicate `P`, target axioms `Ax`, and the hard-direction
  algebraic route. Factor a generic `structure FragmentConservativity P` mirroring the existing
  `CanAlgComplete` structure-by-reuse idiom, deriving the subsumption/iff/ND corollaries once and
  supplying four `def` instances that each reuse the retained hard-direction proof verbatim.
- **Part A — completeness stack**: adopt `CanAlgComplete` as the single *documented* terminal
  interface for fragment completeness; collapse the genuinely redundant zero-consumer `*_iff_chain`
  family in `ConservativeChain.lean`; and reclassify the load-bearing piecewise theorems as
  documented internal inputs (docstring only — they stay public).

**Definition of done**: zero sorry throughout; `lake build`, `lake test`,
`lake exe checkInitImports`, `lake exe lint-style`, and `lake shake` all pass; the barrel
(`Cslib.lean`) is refreshed via `lake exe mk_all --module`.

### Research Integration

The research report (`reports/01_algebra-consolidation-research.md`) is integrated as follows:

- **Scope boundary vs task 393 confirmed disjoint** (report §1): task 393 owns the CROSS-FAMILY
  (`Temporal/`/`Bimodal/`/`Modal/`) MCS/GenericMCSBridge/Lindenbaum consolidation; this task touches
  only `Logics/Propositional/Semantics/Algebra/`. No file overlap. `HilbertLindenbaum.lean` and any
  `GenericMCS*`/cross-family file are OUT OF SCOPE and must not be touched.
- **Part A premise correction** (report §2.2): the task's naive framing ("demote HilbertCompleteness/
  BrouwerianCompleteness piecewise theorems to private corollaries") would break the build.
  `MPL.hilbert_alg_complete` (20 use-sites incl. `Cslib/Foundations/Logic/ProofSystem.lean`) and
  `conjImp_brouwerian_complete` (14 use-sites) are load-bearing INPUTS to `CanAlgComplete`, NOT
  redundant duplicates. They MUST stay public. Only the zero-consumer `*_iff_chain` family is safely
  collapsible.
- **Part B design** (report §3.2): use a `structure` (not `class`) because `Ax` is output data that
  varies per fragment and is not inferable by instance search — identical rationale to `CanAlgComplete`.
- **Hard-direction retention** (report §3.1): the OrImp hard direction is **sequent-calculus**
  (`hilbert_iff_lj` -> `LJProof.cutElim` -> `cutFreeLJ_toOrImp`), not algebraic; every fragment's
  hard direction (#1) must be kept verbatim. Only the generic #2/#3/#4 skeleton is consolidated.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in the delegation context; no ROADMAP.md consulted.

## Goals & Non-Goals

**Goals**:
- Introduce a generic `FragmentConservativity` core parameterized by the fragment predicate,
  deriving the subsumption/iff/ND corollaries once (replacing the 4×3 = 12 boilerplate theorems).
- Supply four `def` instances (`Imp`, `ConjImp`, `ConjImpBot`, `OrImp`) reusing the retained
  hard-direction proofs verbatim.
- Adopt `CanAlgComplete` as the documented terminal completeness interface; collapse the
  zero-consumer `*_iff_chain` family; reclassify load-bearing piecewise theorems in docstrings.
- Preserve every public theorem name/signature that has nonzero use-sites (re-express as one-line
  corollaries rather than deleting).
- Keep the tree zero-sorry and green across the full CI gate.

**Non-Goals**:
- No modification of `HilbertLindenbaum.lean`, `HilbertLindenbaumRel.lean`, any `GenericMCS*` file,
  or any `Temporal/`/`Bimodal/`/`Modal/` cross-family file (task 393 territory).
- No re-derivation of any proof; no new mathematics; no new Mathlib instantiation.
- No privatization or deletion of any name with nonzero use-sites (esp. `MPL.hilbert_alg_complete`,
  `conjImp_brouwerian_complete`).
- No aggressive Part-A deletion beyond the zero-consumer `*_iff_chain` set (see Risks).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Privatizing a load-bearing name (e.g. `MPL.hilbert_alg_complete`) breaks Foundations + IPL/CPL siblings | H | M | Preserve all nonzero-use-site names/signatures; Part A touches docstrings only for those. Verify with a repo-wide grep before any deletion. |
| Removing/renaming a public conservativity theorem breaks `Metalogic/ClassicalImpCompleteness.lean` (only external importer of the sprawl) | H | M | Re-export or keep one-line corollaries for every nonzero-use-site name; scoped-build `ClassicalImpCompleteness` after retiring per-fragment files. |
| Universe-metavariable mismatch in the generic `structure` | M | M | Carry `universe u` and pin `Atom`/algebra to the same level, exactly as `CanAlgComplete` and `brouwerianBot_complete` already do. |
| Wide import union in a single consolidated file | M | M | Use the two-file split (thin generic core + instances sibling) to localize fragment-specific machinery; fall back to single file only if import surface proves manageable. |
| Barrel (`Cslib.lean`) drifts after add/remove of files | M | H | Run `lake exe mk_all --module` after every add/remove; purge retired file names; verify `lake exe checkInitImports`. |
| Module-system header drift (`module`/`public import`/`@[expose] public section`) | M | M | Copy the exact header pattern from `CanAlgComplete.lean`; begin new files with `import Cslib.Init`. |
| Lint failures on new declarations (docBlame, dupNamespace, topNamespace) | M | H | Docstring every new declaration and structure field; wrap instances in explicit namespace; avoid `Cslib.Logic.PL`-prefix repetition; `def` for the data instances, `theorem`/`lemma` for Prop results. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This refactor is fully sequential: each phase
must leave the tree green before the next begins, and Parts A and B both touch `ConservativeChain.lean`,
so they cannot overlap.

---

### Phase 1: Generic FragmentConservativity core [COMPLETED]

**Goal**: Create the thin generic core file holding the `structure FragmentConservativity`, the three
generic derived theorems, and the relocated generic combinators — with the tree still green.

**Tasks**:
- [x] Create `Cslib/Logics/Propositional/Semantics/Algebra/FragmentConservativity.lean` with the
      module-system header copied from `CanAlgComplete.lean` (`import Cslib.Init`, `public import`s,
      `@[expose] public section`).
- [x] Define `structure FragmentConservativity {Atom} (P : Proposition Atom → Bool)` with fields
      `Ax`, `hard`, `sub` (per report §3.2), carrying `universe u` and pinning `Atom`/algebra levels.
      Docstring the structure and every field (docBlame).
- [x] Relocate the generic combinators `liftDerivationTree` and `derivable_mono` from
      `ConjImpConservative.lean` into this core (leave a transitional re-export if any sibling still
      references them by the old path).
- [x] Derive the three generic theorems from the structure:
      `fragmentConservativity_derivableOfDerivableInt` (from `sub` via `derivable_mono`),
      `fragmentConservativity_iff` (bundle of `hard` + the above),
      `fragmentConservativity_nd` (ND corollary via `derivableInIplIffDerivableInt`).
- [x] Run `lake exe mk_all --module` to add the new file to the barrel.

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentConservativity.lean` - new generic core
- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean` - move out `liftDerivationTree`/`derivable_mono` (transitional re-export if needed)
- `Cslib.lean` - barrel refresh (via `mk_all --module`)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.FragmentConservativity` succeeds.
- No `sorry`/`admit` in the new file (grep).

---

### Phase 2: Four fragment instances [COMPLETED]

**Goal**: Provide the four `def` instances of `FragmentConservativity`, each reusing its retained
hard-direction proof verbatim.

**Tasks**:
- [x] Decide file placement (committed design: two-file split — put instances in a sibling
      `FragmentConservativityInstances.lean` importing the core plus the union of fragment machinery;
      fall back to appending into the core only if the import surface proves manageable).
- [x] `fragmentConservativityConjImp` (`IsOrBotFree`/`ConjImpAxiom`): reuse the
      `IPL.hilbert_alg_complete` -> `LowerSet B` Heyting -> `brouwerianEmbeddingLemma` ->
      `conjImp_brouwerian_complete` hard direction verbatim; trivial `sub`.
- [x] `fragmentConservativityImp` (`IsImpTopOnly`/`ImpAxiom`): reuse the ConjImp +
      `FreeMeetExtension` free BSL + `freeMeetEvaluateEq` + `imp_hilbert_complete` route verbatim.
- [x] `fragmentConservativityConjImpBot` (`IsOrFree`/`ConjImpBotAxiom`): reuse the
      `NonemptyLowerSet` Heyting + `nonemptyLowerSet_evaluate_commutes` +
      `conjImpBot_pointedBrouwerian_complete` route verbatim.
- [x] `fragmentConservativityOrImp` (`IsAndBotFree`/`OrImpAxiom`): reuse the sequent-calculus
      `hilbert_iff_lj` -> `LJProof.cutElim` -> `cutFreeLJ_toOrImp` route verbatim (the non-algebraic
      one out — keep as-is).
- [x] Wrap instances in an explicit namespace; `def` (data) not `theorem`; docstring each.
- [x] Refresh barrel if a new file was added.
- [x] *(deviation: altered -- the re-homed 4×3 boilerplate theorems are NOT defined in this file
      in Phase 2 as originally scoped; they are deferred to Phase 3, defined atomically together
      with removing their bespoke bodies from the four per-fragment files, to avoid a
      duplicate-declaration name clash. The four instances alone are complete and green here.)*

**Timing**: ~2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentConservativityInstances.lean` - new (or append to core)
- `Cslib.lean` - barrel refresh if a file was added

**Verification**:
- `lake build` of the instances module succeeds.
- Each instance's `hard` field is definitionally the pre-existing hard-direction term (no proof re-derivation).
- No `sorry`/`admit` (grep).

---

### Phase 3: Re-express boilerplate, retire per-fragment surface [COMPLETED]

**Goal**: Re-express the 4×3 per-fragment boilerplate theorems (#2-#4) as thin corollaries of the
generic ones, preserving every nonzero-use-site name/signature; reduce the now-redundant per-fragment
files to re-export shims (or retire them), keeping all external importers resolving.

**Tasks**:
- [x] For each fragment, replace the bespoke `derivableXOfDerivableInt` / `hilbertIplConservativeOverX_iff`
      / `ipl_conservative_over_X` proof bodies with one-line terms delegating to
      `fragmentConservativity_derivableOfDerivableInt` / `_iff` / `_nd` applied to the matching instance.
      Preserve the exact public names and signatures (snake_case theorem names are grandfathered).
      *(deviation: altered -- re-homed into `FragmentConservativityInstances.lean` rather than
      rewritten in place in the four per-fragment files, since the instance the one-liners need is
      defined downstream of those files; see Phase 2's deviation note. `ConservativeChain.lean`'s
      import list was updated (3 individual fragment imports collapsed to one
      `FragmentConservativityInstances` import) so every consumer keeps resolving the relocated names
      transitively -- verified green by `lake build`.)*
- [x] Preserve `derivableMinOfDerivableConjImp` / `derivableMinOfDerivableImp` (2 use-sites each,
      CanAlgComplete inputs) and `GHAValid_implies_BrouwerianValid_direct` (8 use-sites) either in place
      or as re-exports. *(untouched -- these live in `CanAlgComplete.lean`/`MplConservativeChain.lean`,
      outside Phase 3's scope; verified still building.)*
- [x] Reduce the emptied per-fragment files (`ImpConservative.lean`, `ConjImpConservative.lean`,
      `ConjImpBotConservative.lean`, `OrImpConservative.lean`) to re-export shims pointing at the new
      module, OR retire them and re-home their nonzero-use-site names into the new module.
      *(each file now retains only its hard-direction theorem + supporting machinery; the 12
      boilerplate theorems are re-homed, not re-exported, into `FragmentConservativityInstances.lean`.)*
- [x] Confirm `Cslib/Logics/Modal/Metalogic/ClassicalImpCompleteness.lean` (only external importer of
      `ImpConservative`/`ConjImpConservative`) still resolves its transitive imports.
      *(it only used `liftDerivationTree`, re-exported transitively since Phase 1 -- verified green.)*
- [x] Run `lake exe mk_all --module`; purge any retired file names from the barrel.
      *(no files added/removed in Phase 3, so no barrel change was needed.)*

**Timing**: ~2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean` - shim/retire
- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean` - shim/retire
- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpBotConservative.lean` - shim/retire
- `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean` - shim/retire
- `Cslib.lean` - barrel refresh

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.ClassicalImpCompleteness` succeeds.
- Repo-wide grep confirms no nonzero-use-site name lost its definition/re-export.
- No `sorry`/`admit` (grep).

---

### Phase 4: Part A — terminal interface + collapse *_iff_chain [COMPLETED]

**Goal**: Adopt `CanAlgComplete` as the documented terminal fragment-completeness interface, collapse
the zero-consumer `*_iff_chain` restatements, and reclassify load-bearing piecewise theorems in
docstrings (keeping them public).

**Tasks**:
- [x] Verify (repo-wide grep) that `impAxiom_iff_chain`, `conjImpAxiom_iff_chain`,
      `orImpAxiom_iff_chain`, `minAxiom_iff_chain` still have zero external use-sites.
- [x] In `ConservativeChain.lean`, delete the four `*_iff_chain` theorems, OR re-express each as a
      one-line corollary of `canAlgComplete_iff` / the retained fragment instances (remove the parallel
      bespoke proofs either way). *(deleted outright -- each was a `.symm` of an already-public
      biconditional with zero consumers; a docstring note left in their place pointing to
      `CanAlgComplete.lean`.)*
- [x] Add/adjust the `CanAlgComplete.lean` docstring to declare it the terminal generic
      fragment-completeness interface.
- [x] Reclassify `MPL.hilbert_alg_complete`, `conjImp_brouwerian_complete`, and the other load-bearing
      inputs in their docstrings as "internal inputs to `CanAlgComplete`" — **docstring text only; do
      NOT change visibility, names, or signatures**.
- [x] If any fragment-completeness *restatement* is found to be a literal `canAlgComplete_iff`
      instance, replace only its proof body with a one-line term (keep the name if it has consumers).
      *(none found: `mplAxiom_iff_conjImpAxiom`/`mplAxiom_iff_impAxiom` are MPL-to-fragment
      biconditionals, not `canAlgComplete_iff`/`fragmentConservativity_iff` instances -- left
      untouched.)*

**Timing**: ~1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` - collapse `*_iff_chain`
- `Cslib/Logics/Propositional/Semantics/Algebra/CanAlgComplete.lean` - terminal-interface docstring
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` - docstring reclassification only
- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean` - docstring reclassification only

**Verification**:
- `lake build` of `ConservativeChain` and `CanAlgComplete` succeeds.
- `lake build Cslib.Foundations.Logic.ProofSystem` succeeds (load-bearing consumer intact).
- No `sorry`/`admit` (grep).

---

### Phase 5: Full verification gate [COMPLETED]

**Goal**: Confirm the whole tree is green, zero-sorry, barrel-consistent, and lint-clean.

**Tasks**:
- [x] `lake exe mk_all --module` (final barrel refresh; confirm no diff churn beyond intended add/remove).
      *(no diff -- barrel already consistent.)*
- [x] `lake build` (full). *(3253/3253 jobs green; only pre-existing unrelated warnings/sorries in
      Tableau/ files, not touched by this task.)*
- [x] `lake test`. *(exit 0.)*
- [x] `lake exe checkInitImports`. *(exit 0.)*
- [x] `lake exe lint-style`. *(exit 0, no output.)*
- [x] `lake shake` (no new redundant imports introduced by the consolidation).
      *(found and fixed real dead imports left by Phase 3's boilerplate removal: dropped the
      now-unused `HilbertConservativeGlivenko`/`FragmentConservativity`/cross-fragment imports
      from the four per-fragment files, and repointed `ClassicalImpCompleteness.lean`,
      `LiftViaMorphism.lean`, `MplConservativeChain.lean` to import `FragmentConservativity.lean`
      directly instead of transitively. Net shake-output line count decreased
      [2964 -> 2958]; remaining output in touched files is only the project-wide
      `import Cslib.Init` false-positive (mandated by the Init Import Requirement,
      not actionable) plus one pre-existing unrelated dead import in `ConservativeChain.lean`
      predating this task.)*
- [x] Final repo-wide grep for `sorry`/`admit`/vacuous def in all touched files — must be empty.
      *(empty; repo-wide sorry/vacuous-def counts elsewhere are pre-existing and outside this
      task's touched-file set.)*

**Timing**: ~1 hour

**Depends on**: 4

**Files to modify**:
- `Cslib.lean` - final barrel state (if any drift)

**Verification**:
- All six CI steps pass (`build`, `test`, `checkInitImports`, `lint-style`, `shake`, `mk_all` clean).
- Zero-sorry grep is empty across the directory.

## Testing & Validation

- [x] `lake build` — full tree compiles.
- [x] `lake test` — test suite green.
- [x] `lake exe checkInitImports` — every module's `import Cslib.Init` discipline holds.
- [x] `lake exe lint-style` — style-clean (docBlame, dupNamespace, topNamespace, defsWithUnderscore).
- [x] `lake shake` — no redundant imports introduced.
- [x] `lake exe mk_all --module` — barrel matches filesystem (no uncommitted drift).
- [x] Zero-sorry: grep for `sorry`/`admit`/vacuous def across `Algebra/` returns nothing.
- [x] Every nonzero-use-site public name preserved (repo-wide grep for each name still resolves).

## Artifacts & Outputs

- `plans/01_consolidate-algebra-abstractions.md` (this file)
- `summaries/01_consolidate-algebra-abstractions-summary.md` (produced at implementation completion)
- New: `Cslib/Logics/Propositional/Semantics/Algebra/FragmentConservativity.lean` (generic core)
- New (committed design): `Cslib/Logics/Propositional/Semantics/Algebra/FragmentConservativityInstances.lean`
- Modified: `ConservativeChain.lean`, `CanAlgComplete.lean`, `HilbertCompleteness.lean`,
  `BrouwerianCompleteness.lean`, the four per-fragment `*Conservative.lean` shims, `Cslib.lean` barrel

## Rollback/Contingency

- This is a pure re-organization; every phase leaves the tree green and is committed independently, so
  rollback is `git revert` of the offending phase commit (working tree stays clean between phases).
- If Part A pressure escalates beyond the zero-consumer `*_iff_chain` set (e.g. a request to privatize
  `MPL.hilbert_alg_complete` or `conjImp_brouwerian_complete`), do NOT proceed — mark the task
  `[BLOCKED]` for user review rather than break `Foundations/Logic/ProofSystem.lean` and the IPL/CPL
  siblings (report §2.2, §6).
- If the two-file split's import union proves problematic, collapse the instances into the core file
  (single-file, task-literal alternative) — both satisfy "one generic core parameterized by the
  fragment predicate".
