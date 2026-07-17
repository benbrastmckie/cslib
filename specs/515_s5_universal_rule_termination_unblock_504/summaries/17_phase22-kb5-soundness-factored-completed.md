# Summary 17: Phase 22 COMPLETED -- KB5 rule + soundness landed by factoring, not cloning

**Task**: 515 - s5_universal_rule_termination_unblock_504
**Plan**: plans/07_s5-termination-machinery.md (v6)
**Phase**: 22 (`modalApplyOneKb5` + `modalTableauKb5_sound`) -- now `[COMPLETED]`

## What landed this dispatch

Resumed from `summaries/16_phase21-hintikka-wall-landed-completed.md`, which shipped
`fiveValid` decidability (Phase 21) and left Phase 22 (KB5 rule + soundness) and Phase 23 (KB5
completeness) queued. This dispatch's scope was Phase 22 only.

**Key finding, before writing any code**: `modalApplyOneFive`'s tableau rule
(`FiveSimplification.lean`) is **purely syntactic** -- a function of the branch and the
accessibility relation alone. Neither its definition nor any field of
`RuleApplicationSpecCore modalApplyOneFive` inspects a frame condition anywhere. Its soundness
proof (`modalTableauFive_sound`) shows that a branch the rule closes is unsatisfiable on
**every** Euclidean frame (`fiveFC`). Since `kb5FC := Std.Symm r ∧ Relation.RightEuclidean r` is
*strictly stronger* than `fiveFC := Relation.RightEuclidean r` (every KB5 frame is, in
particular, a Five frame), a branch unsatisfiable on every Euclidean frame is unsatisfiable on
every KB5 frame too. **The unmodified `modalApplyOneFive` rule is therefore already a sound KB5
tableau rule.** No cloned rule, root-aware mint-arm guard, or Phase 18/19a/19b-style
termination-bound re-derivation was needed for soundness -- a dramatically cheaper path than the
plan's own task list anticipated (which expected a Phase 15(c)/17 root/cluster-dichotomy rule and
a ported termination argument).

Two commits, both green:

1. **`6edb30cc`** (`FiveSimplification.lean`, `FrameSoundness.lean`): landed
   `modalApplyOneKb5 := modalApplyOneFive` (a literal alias, not a clone),
   `modalApplyOneKb5_specCore := modalApplyOneFive_specCore` (transfers by `rfl`),
   `modalStepBranchKb5`/`modalExpandBranchesKb5`/`modalTableauKb5` (driver instantiation,
   mirroring the Five driver section verbatim with the alias substituted), plus the bridge lemma
   `modalTableauKb5_eq_modalTableauFive` (`modalTableauKb5 φ = modalTableauFive φ := rfl`). In
   `FrameSoundness.lean`: `kb5FC_imp_fiveFC` (frame-condition projection, one line) and
   `fiveValid_imp_kb5Valid` (frame-class monotonicity, mirroring the
   `specs/515_.../probes/five-s5-separation.lean` bridging pattern one level down the hierarchy),
   and the capstone `modalTableauKb5_sound (φ) (h : modalTableauKb5 φ = .closed) : kb5Valid φ :=
   fiveValid_imp_kb5Valid φ (modalTableauFive_sound φ h)` -- a two-line proof, not a bespoke
   fuel-induction re-derivation.
2. **`75ca9d06`** (plan file): Phase 22 marked `[COMPLETED]`, checklist ticked with deviation
   notes recording the "factor, not clone" decision, phase note added explaining the argument and
   its scope (soundness only; completeness is a separate question, deferred to Phase 23).

## A placement bug caught by the build, not by review

The first attempt inserted the new KB5 section immediately after `modalTableauFive_eq` (early in
`FiveSimplification.lean`), before `modalApplyOneFive_specCore` is actually defined later in the
file (in the "Strategy" discharge section). This produced an `Unknown identifier
modalApplyOneFive_specCore` build error. Fixed by moving the entire KB5-instantiation section to
directly after `modalApplyOneFive_specCore`'s definition. This is exactly the kind of ordering
bug the LSP-based `lean_verify`/`lean_goal` checks used before the first `lake build` attempt
could not have caught (they reported clean results against a stale/cached elaboration state) --
recorded here as the reason the final verification pass **also** ran a real `lake build`, not
just LSP tools.

## An external, non-blocking build interruption

At dispatch start, `Cslib/Logics/Modal/Tableau/LoopChecking.lean` was mid-edit by a concurrent
session (task 511, uncommitted WIP with a real tactic-failure bug at the time) and blocked a full
`lake build`. Per the hard constraint, this file was never touched. LSP-based verification
(`lean_goal`, `lean_verify`/`#print axioms`) was used to sanity-check the new declarations while
that concurrent breakage was outstanding. The concurrent session resolved and committed its own
work partway through this dispatch (visible as `e6997750`/`8a9b3e68`/`b61d3cc5` and later `task
511: record Phase 5 re-block...` in `git log`), after which a full `lake build` ran clean and
confirmed everything reported by the LSP.

## Verification

- **Sorry-free**: `grep -rn '\bsorry\b'` on both touched files returns zero hits.
- **Axioms**: `#print axioms` via `lake env lean` on all twelve new public declarations
  (`modalApplyOneKb5`, `modalApplyOneKb5_specCore`, `modalStepBranchKb5`,
  `modalExpandBranchesKb5`, `modalTableauKb5`, `modalStepBranchKb5_eq`,
  `modalExpandBranchesKb5_eq`, `modalTableauKb5_eq`, `modalTableauKb5_eq_modalTableauFive`,
  `kb5FC_imp_fiveFC`, `fiveValid_imp_kb5Valid`, `modalTableauKb5_sound`) confirms
  `[propext, Classical.choice, Quot.sound]` at most -- `kb5FC_imp_fiveFC` and
  `fiveValid_imp_kb5Valid` need **no axioms at all**. No `sorryAx`, no new custom axiom (repo-wide
  `axiom` count unchanged at 28, all pre-existing).
- **Full CI green**: `lake build` (3240/3240), `lake exe checkInitImports` (exit 0), `lake lint`
  (only the pre-existing `PrimeExclusion.lean` baseline remains, unrelated to this dispatch),
  `lake exe lint-style` (clean), `lake shake --add-public --keep-implied --keep-prefix` (no
  import changes suggested for either touched file), `lake test` (exit 0; pre-existing
  Intuitionistic/Minimal `sorry` warnings are an unrelated baseline). `mk_all` not required (no
  new file added).

## Plan Deviations

- **`modalApplyOneKb5` shape**: landed as a literal alias `modalApplyOneKb5 := modalApplyOneFive`,
  not the Phase 15(c)/17 root/cluster-dichotomy rule the task text anticipated. The syntactic
  rule needs no KB5-specific shape at all -- see the phase note in the plan file for the full
  argument.
- **Termination-argument port from Phase 18**: skipped as moot. The termination bound is a
  property of `modalApplyOneFive` alone, independent of any frame condition; since
  `modalApplyOneKb5 = modalApplyOneFive` definitionally, Phase 19a's bound already applies to
  KB5 verbatim with zero new proof. No mint-arm guard, source-split tag invariant, or
  termination re-derivation was needed.
- **`modalTableauKb5_sound` proof**: landed as a two-line frame-class-monotonicity corollary of
  `modalTableauFive_sound`, not a bespoke Phase 19b-style fuel-induction re-derivation.
- **No sibling `Kb5Simplification.lean`**: the "factor, don't clone" decision meant both landed
  declarations fit naturally into the plan's already-named files (`FiveSimplification.lean`,
  `FrameSoundness.lean`); no new file was created, so `mk_all`/import-barrel updates were not
  needed.

## Files touched

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- `/home/benjamin/Projects/cslib/specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`

## What this unblocks

Phase 23 (KB5 completeness, `Decidable (kb5Valid φ)`, final docstring reconciliation) is next.
Unlike soundness, completeness is **not** free from this phase's factoring: `kb5Valid` is
strictly weaker than `fiveValid` (`kb5FC` is a proper subclass of `fiveFC`-frames), so some
`kb5Valid` formulas may leave `modalTableauFive`/`modalTableauKb5` open. Phase 23 is expected to
need a genuine `extractModelKb5` (symmetric-model extraction from an open branch at the PER
normal form), per the plan's own task list -- this is out of Phase 22's scope and was not
attempted this dispatch.
