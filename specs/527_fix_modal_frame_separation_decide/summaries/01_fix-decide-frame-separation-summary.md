# Implementation Summary: Task #527

- **Task**: 527 - Fix `lake test` failure in `CslibTests/ModalFrameSeparation.lean` (stuck `decide`
  on S5/Five separation checks)
- **Status**: [COMPLETED]
- **Plan**: `specs/527_fix_modal_frame_separation_decide/plans/01_fix-decide-frame-separation.md`

## What Was Done

Replaced the two stuck `decide` examples in `CslibTests/ModalFrameSeparation.lean` with the
already-proven separation theorems from `FrameSoundness.lean`, mirroring the existing `kb5Valid`
example (Option (b) from the plan, adopted verbatim):

- S5 example (was `decide (s5Valid ...) = true := by decide`, stuck because
  `instDecidableS5Valid` routes through `modalExpandBranchesGen`'s nested `let rec`, which
  compiles to `WellFounded.fix` and does not reduce in the kernel) →
  `example : s5Valid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) := boxImp_s5Valid ()`
- Five example (same stuck-`decide` root cause via `instDecidableFiveValid`) →
  `example : ¬ fiveValid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) := boxImp_not_fiveValid`
- Switched `Atom` from `Bool`/`.atom false` to `Unit`/`.atom ()` on both examples, matching the
  theorem statements and the existing `kb5Valid` example's convention.
- Updated all three docstrings (module docstring, S5 example, Five example) to state the checks
  are proved via the ported separation theorems in `FrameSoundness.lean`, removing all claims
  that the checks route through `decide`/the `Decidable` instances. `grep -iE
  'decide|instDecidable'` afterward confirms the only remaining occurrences are explanatory
  (stating that `decide` is *not* used), not stale routing claims.

`modalExpandBranchesGen` was not touched (Option (a) explicitly ruled out); `native_decide` was
not used.

## Plan Deviations

None. All five checklist items in Phase 1 were executed exactly as specified; both theorem
signatures (`boxImp_s5Valid (p : Unit) : s5Valid (.imp (.box (.atom p)) (.atom p))` and
`boxImp_not_fiveValid : ¬ fiveValid (Atom := Unit) (.imp (.box (.atom ())) (.atom ()))`,
confirmed by reading `FrameSoundness.lean:1343` and `:1349` directly) matched the plan's stated
signatures exactly, so no adjustment was needed.

## Verification

- `lake build CslibTests.ModalFrameSeparation` — succeeded, no reduction/"got stuck" errors.
- `lake test` — exit code 0, full suite green (9230/9230, `Built CslibTests`).
- `lake exe checkInitImports` — no output (all files, including the modified one, import
  `Cslib.Init` transitively).
- `lake lint` — full output is 3 lines total, none referencing `ModalFrameSeparation.lean`; no
  docBlame/defLemma/defsWithUnderscore/simpNF/unusedSectionVars/topNamespace/dupNamespace
  warnings introduced.
- `lake exe lint-style` — no output (no text-lint issues).
- `lake shake --add-public --keep-implied --keep-prefix` — no entry for
  `ModalFrameSeparation.lean` or `FrameSoundness.lean`; all reported entries are pre-existing
  debt in unrelated files (Propositional/Temporal tableau modules), out of scope per the plan's
  non-goals.
- `lake exe mk_all --module` — "No update necessary".
- `grep -n "\bsorry\b" CslibTests/ModalFrameSeparation.lean` — 0 matches.
- Repo-wide `sorry_count` (133) and `axiom_count` (28) are pre-existing baselines, all outside
  `CslibTests/` and unrelated to this change; this task introduced zero new sorries and zero new
  axioms (the replacement terms are direct applications of already-proven, already-compiling
  theorems).
- One pre-existing vacuous-pattern match (`Cslib/Computability/URM/Basic.lean:92`,
  `theorem J_IsJump ... := trivial`) is unrelated to this task and was not touched.

## Files Modified

- `CslibTests/ModalFrameSeparation.lean` (two examples rewritten, three docstrings updated,
  `Atom` switched from `Bool` to `Unit` on the S5/Five examples)
- `specs/527_fix_modal_frame_separation_decide/plans/01_fix-decide-frame-separation.md` (phase
  status, checklist items, plan-level status marked complete)
