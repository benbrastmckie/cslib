# Implementation Summary: Task #408 — Property-Gated `botL` Sequent Calculus

- **Task**: 408 — Sequent calculus: property-gated `botL` (single MPL/IPL inductive; metatheory proved once)
- **Plan**: plans/01_gated-botl-seqproof.md
- **Status**: Implemented — all 7 phases COMPLETED; full library `lake build` green; zero debt in task scope
- **Session**: sess_1782760056_06c853_408

## What Was Done

Unified the MPL and IPL single-conclusion sequent calculi into one inductive
`SeqProof (T : Theory Atom) : @Sequent Atom → Type u` with the explosion rule `botL` gated by
`[IsIntuitionistic T]` — the exact analogue of the shipped gated `efq` in `Theory.Derivation`.
`LJProof` is now `abbrev LJProof seq := SeqProof IPL seq`, recovering every existing LJ result
with its original public signature. `SeqProofMinimal := SeqProof MPL` names the `botL`-free
minimal calculus.

The structural metatheory is defined **once generically over `T`**:
- `SeqProof.height`, `SeqProof.mono` (gated-`botL` arm rebinds its stored instance via `letI`),
  `SeqProof.CutFree`, `SeqProof.IsBotRuleFree`, `SeqProof.formulas`.
- LJ-facing names are preserved as re-exports: `LJProof.height`, `LJProof.mono`, `LJCutFree`,
  `CutFreeLJProof`. Cut elimination (`ljCutAdmissibility`, `LJProof.cutElim`), subformula property,
  soundness (`LJProof.sound`), completeness (`hilbert_iff_lj`), interpolation
  (`LJProof.interpolation`), and decidability all keep their original signatures and now run over
  the unified inductive at `T = IPL`.

## Key Technical Findings

- **Gate is inert at IPL.** A `botL` *match arm* on `SeqProof T` at generic `T` must use the
  `@`-qualified pattern `@SeqProof.botL _ _ _ _ _ inst hbot` (7 positional args: Atom, DecidableEq,
  T, Γ, C, instance, membership) because an anonymous `.botL _ _ _` triggers instance *synthesis*
  of `IsIntuitionistic T`. At `T = IPL` the instance `instIsIntuitionisticIPL` is synthesizable, so
  the existing anonymous `.botL` match arms in the IPL-specific files (Soundness, CutElimination
  helpers, etc.) continued to compile unchanged. Generic definitions (`height`, `mono`, `CutFree`,
  `IsBotRuleFree`, `formulas`) use the `@`-pattern; the `mono` reconstruction uses `letI := inst`.
- **`LJProof.<constructor>` no longer resolves** as a qualified name (the abbrev has no namespace),
  so explicit constructor references in Completeness/Interpolation/SubformulaProperty/Decidability/
  OrImpConservative were retargeted `LJProof.<ctor>` → `SeqProof.<ctor>` (ax, botL, andL, andR, orL,
  orR1, orR2, impL, impR, weakL, cut). The named methods/theorems (`LJProof.mono`, `.height`,
  `.cutElim`, `.sound`, `.formulas`, `.interpolation`, `.subformula`) are untouched.
- **`SeqProof.formulas` made generic.** Its recursive `d.formulas` calls resolve on sub-terms typed
  `SeqProof T`, so it was renamed from `LJProof.formulas` into the `SeqProof` namespace.
- **`open Theory`** added to `LJ/Basic.lean` so `IsIntuitionistic`/`IPL`/`MPL` resolve.

## Files Modified

- `Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean` — unified inductive `SeqProof T`,
  gated `botL`, `LJProof`/`SeqProofMinimal` abbrevs, generic structural defs + IPL re-exports.
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` — `LJCutFree.mono` simp sets
  retargeted to the generic `SeqProof.mono`/`SeqProof.CutFree` equations; botL arms unchanged.
- `Cslib/Logics/Propositional/SequentCalculus/LJ/SubformulaProperty.lean` — `SeqProof.formulas`
  generic; constructor refs retargeted.
- `Cslib/Logics/Propositional/SequentCalculus/LJ/{Soundness,Completeness,Decidability}.lean` —
  constructor refs retargeted (Soundness needed no change).
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean` — constructor refs retargeted;
  `ljMaeharaCore` heartbeat budget 400k → 800k (re-export indirection adds whnf overhead).
- `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean` — constructor refs retargeted.

## Verification

| Check | Result |
|-------|--------|
| Full `lake build` (3153 jobs) | GREEN |
| `lake exe checkInitImports` | PASS (exit 0) |
| `lake exe lint-style` | PASS (exit 0) |
| `lake shake --add-public --keep-implied --keep-prefix` | exit 0 (only pre-existing `Cslib.Init` / Tableau / Temporal advisories) |
| `lake exe mk_all --module` | No update necessary (no new files) |
| LK regression (`LKProof.cutElim`, `hilbert_iff_lk`, LK build) | Intact, untouched |
| `sorry`/`admit`/new `axiom` in task-408 files | ZERO (all grep hits are docstring prose) |
| New environment-lint issues from task 408 | ZERO |

## Plan Deviations

- **Placement of `SeqProof`**: defined inside `LJ/Basic.lean` (the plan's permitted alternative to a
  new `SequentCalculus/Basic.lean`/`Defs.lean`). This avoids a new file (no barrel/`mk_all`/`shake`/
  `checkInitImports` churn) and keeps the import graph unchanged. `SequentCalculus/Defs.lean` (LK
  sequents) was left untouched.
- **botL match arms in IPL-specific files**: the plan budgeted switching ~36 arms to the `@`-pattern.
  In practice only the *generic-over-`T`* definitions required the `@`-pattern; IPL-specific arms
  synthesize `IsIntuitionistic IPL` and compiled unchanged. Net edits were therefore the constructor
  re-targeting (`LJProof.<ctor>` → `SeqProof.<ctor>`) plus the generic-def `@`-patterns.
- **Interpolation heartbeats**: `ljMaeharaCore` budget raised 400k → 800k (the re-export wrappers add
  whnf/unfolding cost across the large induction). Localized perf cost only.

## Pre-Existing Issues (NOT introduced by task 408, out of scope)

- **`lake test` fails on `CslibTests.GrindLint`** for `Cslib.Logic.PL.IntFinWorld.mk.sizeOf_spec`
  (>100 grind instantiations) in `Metalogic/IntDecidability.lean`. This is deductively independent of
  the refactor: `#grind_lint` instantiation counts depend only on `@[grind]`-tagged lemmas, and
  neither the old `LJProof` nor the new `SeqProof` adds any; `IntDecidability.lean` does not import
  the sequent-calculus files; the failure's instantiation trace contains no `SeqProof.*` lemma; and
  the file was last changed by tasks 385/400. Recommend a separate task to address the grind-lint
  threshold in the `IntFMPSpike`/`IntDecidability` spike code.
- **`lake lint` `defsWithUnderscore`** on `ljCutAdm_principal_andR/orR/impR`, `ljCutAdm_left`,
  `ljCutAdm_right` — these helper names predate task 408 (present verbatim at HEAD~3); the task-408
  diff did not touch their signatures. `lake lint` is a weekly-cron check, not PR CI.
- **5 pre-existing `sorry`s** in `Tableau/{Intuitionistic,Minimal}/*` and Tableau style-linter
  warnings — unrelated files, present before task 408.
