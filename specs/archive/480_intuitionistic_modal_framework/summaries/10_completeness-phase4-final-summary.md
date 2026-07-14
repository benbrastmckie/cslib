# Phase 4 (FINAL) Summary: Completeness.lean — Parametric Packaging

**Task**: 480 (intuitionistic modal framework) | **Plan**: v4 | **Phase**: 4 (final) | **Status**: COMPLETED

This dispatch completes task 480. All 12 phases (1, 2a, 2-infra, 2b-sublemma, 2b, 2c, 2d, 3a, 3b,
3c, and now 4) are `[COMPLETED]`; the framework is sorry-free and axiom-free.

## What Was Proved

New file `Cslib/Logics/Modal/Metalogic/Intuitionistic/Completeness.lean` (~340 lines, 4
declarations), importing `TruthLemma.lean` (Phase 3).

### `canonicalBModel`

Assembles `CanonicalPrimeWorld`, the canonical `Preorder` (set inclusion, Phase 2a), `canonicalR`
(Phase 2a), `canonicalVal` (Phase 2a), and `canonical_f1`/`canonical_f2` (Phase 2d) into a concrete
`BModel (CanonicalPrimeWorld Axioms) Atom` term, verified field-for-field against
`Birelational.lean`'s `BModel` structure (`r`, `f1`, `f2`, `v`, `botForces`,
`v_upward_closed`, `bf_upward_closed`). `botForces` is threaded as a parameter (with its
upward-closure proof) so both completeness statements below reuse this single assembly.

### `canonical_prime_world_nonempty_of_consistent` (the consistency hook)

```
¬ Derivable Axioms (⊥ : Proposition Atom) → Nonempty (CanonicalPrimeWorld Axioms)
```

A purely parametric hook (plan v4 Non-Goals: "No soundness/consistency discharge of any concrete
axiom set — the framework exposes the hook only"): if `Axioms` is consistent, the canonical model
is inhabited. Concrete consistency of IK/CK is left to tasks 492/493. Proved via
`modal_prime_exclusion` excluding `⊥` from the deductive closure of `∅`; any finite sublist of that
closure reduces (`modal_deriv_from_closure_to_S`) to a derivation from `∅` itself (i.e. `[]`), so
consistency of the closure follows directly from the hypothesis.

### `ivalid_completeness` / `mvalid_completeness`

```
ivalid_completeness : IValid.{u,u} φ → Derivable Axioms φ
mvalid_completeness  : MValid.{u,u} φ → Derivable Axioms φ
```

Both carry the full five-hypothesis union `{ h_K, h_Kdia, h_Idb, h_Cd, h_dbot }` plus the
intuitionistic base (`h_implyK`, `h_implyS`, `h_efq`, `h_orI1`, `h_orI2`, `h_orE`, `h_andI`,
`h_andE1`, `h_andE2`), matching report 03's definitive per-lemma axiom map. Proved by
contrapositive with a consistent/inconsistent case split on the deductive closure of `∅`
(mirroring `Cslib.Logic.PL.int_strong_completeness`'s `Γ = ∅` instantiation, so no separate global
consistency hypothesis is needed on the completeness statements themselves):

- **Consistent case**: `modal_prime_exclusion` builds a canonical prime world `w₀` excluding `φ`.
  `ivalid_completeness` instantiates `IValid` at the canonical model with `botForces := fun _ =>
  False` (bridged to `⊥ ∉ w.val` via `canonical_bot_not_mem`); `mvalid_completeness` instantiates
  `MValid`'s arbitrary `botForces` parameter to `fun w => ⊥ ∈ w.val` (upward-closed for free via
  set inclusion, no extra hypothesis needed). Either way, `canonical_truth_lemma` forces
  `φ ∈ w₀.val`, contradicting the exclusion.
- **Inconsistent case**: the closure of `∅` deriving `⊥` reduces (`modal_deriv_from_closure_to_S`)
  to `Derivable Axioms ⊥` directly; `h_efq` then derives `φ`, contradicting the contrapositive
  hypothesis.

## Reference Grounding

- [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (birelational canonical model, `IValid`/`MValid` distinction).
- [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43
  (completeness-by-canonical-model template), Lemma 5.5 (prime exclusion).
- `Cslib.Logic.PL.int_strong_completeness` / `int_completeness`
  (`IntStrongCompleteness.lean:257-341`) — the `Γ = ∅` case-split proof pattern transliterated here
  (consistent case via prime exclusion, inconsistent case via EFQ set-derivability).
- Report 03 §4 row 8 (assembled five-axiom union), §7/§10 (parametric `ivalid`/`mvalid` +
  consistency hook design).

## Plan Deviations

- **`ci-pipeline.md`'s documented `Cslib.Init` shake exception applies as-is**: `lake shake`
  flags `remove import Cslib.Init` on the new file; this is the standard, expected false-positive
  (every CSLib file must import `Cslib.Init` per `checkInitImports`, even when shake sees no direct
  symbol use) and was left untouched, matching existing project convention.
- **Shake also surfaced import-minimization suggestions on the frozen Phase 1/2a/3 files**
  (`PrimeTheory.lean`, `CanonicalModel.lean`, `TruthLemma.lean`) — e.g. `TruthLemma.lean` could add
  a direct `Birelational.lean` import instead of relying on the transitive one. Per the dispatch
  instructions ("Prior phases COMPLETE and committed (import/build only; do NOT modify)"), these
  were left untouched; noted here for a future dedicated import-cleanup task if desired.
- **`lake lint` (full-tree) surfaces one pre-existing, out-of-scope finding**: an `unusedArguments`
  warning on `Cslib.Logic.Metalogic.DerivExcludes` (argument 5, `_D`) in the frozen
  `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`. Confirmed via `git diff --stat` that
  this file has zero changes from this dispatch (last touched at commit `4e3ef59c`, Phase 2-infra);
  the finding is unrelated to Phase 4 and out of scope per the plan's frozen-file constraint
  ("Do NOT modify any declaration in `PrimeExclusion.lean`").
- No other deviations from the plan's Phase 4 task list; all four checklist items completed as
  specified.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.Completeness` — succeeded (597 jobs), no
  warnings.
- `lake build` (full project) — succeeded (3194 jobs); only pre-existing, unrelated
  warnings/sorries (`Cslib/Logics/Propositional/Tableau/Intuitionistic/{Scheme,Completeness}.lean`,
  `Tableau/Minimal/Completeness.lean`, `SequentCalculus/LK/*`), outside this task's scope,
  confirmed pre-existing via `git log`.
- `lake exe checkInitImports` — passed (no output).
- `lake exe lint-style` (scoped and full-tree) — passed (no output).
- `lake lint` (full-tree) — 1 pre-existing, out-of-scope finding in frozen `PrimeExclusion.lean`
  (see Plan Deviations); nothing in the new `Completeness.lean` or any file touched this dispatch.
- `lake test` (CslibTests) — passed.
- `lake exe mk_all --module` — registered all four `Intuitionistic/` modules (`PrimeTheory`,
  `CanonicalModel`, `TruthLemma`, `Completeness`) in `Cslib.lean` (they were not previously
  registered); diff is 4 additive lines only.
- `lake shake --add-public --keep-implied --keep-prefix` (scoped to the four `Intuitionistic/`
  modules) — only the standard `Cslib.Init` false-positive on the new file plus out-of-scope
  suggestions on frozen prior-phase files (see Plan Deviations).
- `lean_verify` on all 4 new declarations (`canonicalBModel`, `canonical_prime_world_nonempty_of_
  consistent`, `ivalid_completeness`, `mvalid_completeness`) — axioms = `{propext,
  Classical.choice, Quot.sound}` only; no `sorry`, no new `axiom`.
- ZERO-DEBT: `grep -rnE "sorry|admit"` over `Intuitionistic/` and `PrimeExclusion.lean` returns
  nothing (docstring mentions of the words "sorry"/"axiom" only, no actual tactics/declarations).
- Untouched-classical: `git diff --stat` shows changes only to `Cslib.lean` (+4 lines, barrel
  registration) plus the new `Completeness.lean` file; `MCS.lean`, classical `Completeness.lean`,
  propositional `Int*` files, `PrimeTheory.lean`, and `CanonicalModel.lean` are byte-for-byte
  unchanged.
- Pre-existing sorries in `Tableau/Intuitionistic/{Scheme,Completeness}.lean` and
  `Tableau/Minimal/Completeness.lean` confirmed pre-existing (last touched at commits
  `969782b5`/`19c68791`, unrelated to task 480) and out of scope.

## Task 480 Completion

With Phase 4 complete, task 480's full deliverable set is in place:

- `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean` (Phase 1)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` (Phases 2a/2b-sublemma/2b/2c/2d)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` (Phases 3a/3b/3c)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/Completeness.lean` (Phase 4, this dispatch)
- `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` (Phase 2-infra, frozen, extended)
- `Cslib.lean` (barrel, all four `Intuitionistic/` modules now registered)

The framework exposes `ivalid_completeness`/`mvalid_completeness` with the definitive five-axiom
parametric hypothesis set `{ h_K, h_Kdia, h_Idb, h_Cd, h_dbot }`, ready for tasks 492 (IK) and its
`Cd+Idb`-containing extensions to instantiate directly. Task 493 (bare CK) is flagged (not
implemented here, per the Downstream-Impact Note) as requiring a separate segment/fallible-world
canonical construction, since it cannot reuse the prime-pair box/diamond witnesses.

Ready for PR preparation.
