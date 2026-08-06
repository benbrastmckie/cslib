# Implementation Summary: Adjudicate and delete the audited duplicate re-derivation families

- **Task**: 586 - Adjudicate and delete the audited duplicate re-derivation families
- **Status**: Implemented
- **Plan**: `plans/01_delete-surviving-duplicate.md`
- **Research**: `reports/01_adjudicate-duplicate-families.md`

## What was done

The task brief presumed 45 surviving duplicate re-derivation rows awaiting deletion. The
research established that 43 of those rows had already been deleted by a prior task's own
Phases 8-11, roughly five and a half hours *before* the statement-equivalence audit that
enumerates them was committed — the audit was an input-staleness artifact, not a description of
the live tree. Exactly two audited declarations survived: `accFreshInv_append_S4` (out of scope
by the task's own reachability boundary) and `modalSubfmls_self_mem_S5` (in scope).

The plan's four phases were executed in full:

1. **Drift guard** (Phase 1): re-ran the declaration-level census against the live tree before
   any writes. All six confirmations matched the research's figures exactly — zero divergence,
   so no `[BLOCKED]` stop was triggered.
2. **Deletion** (Phase 2): deleted the `private lemma modalSubfmls_self_mem_S5` from
   `S5Simplification.lean` (its `omit [DecidableEq Atom] [Hashable Atom] in` prefix and
   docstring), and rewrote its 8 same-file call sites
   (`List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 X)`) to the public origin
   `modalSubfmls_self_mem` in `FmpMeasure.lean`. `lake build
   Cslib.Logics.Modal.Tableau.S5Simplification` passed at exit 0, 868 jobs — matching the
   research's pre-verified figure exactly.
3. **Prose reconciliation** (Phase 3): corrected the three stale records the deletions
   falsified:
   - `S5Simplification.lean`'s module-docstring section `## \`modalSubfmls\` Structural
     Re-Derivations` (lines 86-95 pre-edit) named `modalSubfmls_self_mem_S5` as "the sole
     surviving local re-derivation" and justified retaining it on the `[Hashable Atom]` ground.
     With that declaration deleted (and `modalSubfmls_trans_S5` already consolidated earlier),
     no re-derivation content remained under the header, so the whole section was removed per
     the plan's explicit fallback instruction. The one non-redundant fact it carried — that
     `modalUniverseS5`/`modalWorldBoundS5` were archived in favor of the linear budget argument
     — is independently recorded elsewhere in the same file (near the `modalWorldBoundS5`
     definition).
   - `FiveSimplification.lean` carried an orphaned section header, `` `modalKnownWorlds`/
     `modalUniverse` Local Re-Derivations`` (line 730), whose body described Five-suffixed
     re-derivations that no longer exist and which was immediately followed by the next `/-!
     ##` header with no declarations in between. Removed.
   - `LoopChecking.lean`'s "Post-de-duplication update" bullet recorded the repo-wide
     `Local re-derivation` comment-string count as **11**; re-measurement after Phase 2 (`grep
     -rho 'Local re-derivation' Cslib/ | wc -l`) returns **12**. Corrected all three occurrences
     of the stale figure within that bullet (the headline count, the "55 minus N" comparison,
     and the "remaining N comment sites" cross-reference). The historical **55** and **77**
     baselines in the separate "Inventory figures that drifted" block were left untouched, per
     the plan's explicit instruction not to destroy that record.
4. **Full gate** (Phase 4): all eight measured gates re-run and recorded against baseline (see
   table below).

## Task 558 Phase 10 Reasoned Exclusions: superseded entry

Task 558's Phase 10 Reasoned Exclusions table retained `modalSubfmls_self_mem_S5` on this
ground: "Its origin is already public **and** the copy exists to dodge an ambient
`[Hashable Atom]` instance that callers cannot `omit`. De-privatization cannot remove it;
deleting it would break the call sites it exists to serve."

This entry is **superseded**. `git blame` dates the copy (`S5Simplification.lean`'s `private
lemma modalSubfmls_self_mem_S5` plus its `[Hashable Atom]`-rationale docstring) to 2026-07-15,
and the origin's `omit [DecidableEq Atom] [Hashable Atom] in` prefix (`FmpMeasure.lean`) to
2026-07-27 — twelve days later. The rationale was true when written and became false when the
origin acquired the same `omit` prefix as the copy, making the two signatures byte-identical and
instance-free (and the two proofs already byte-identical:
`cases φ <;> simp [modalSubfmls]`). Task 558 Phase 10 recorded the exclusion without
re-checking the origin's signature after the 2026-07-27 change. This task's deletion is the
correction to that stale record. Task 558's historical plan files were not rewritten — this
summary is the durable correction record, per the plan's Prior Plan Reference.

## `accFreshInv_append_S4`: decided, evidenced exclusion (not unfinished work)

`accFreshInv_append_S4` (private, `LoopChecking.lean`) remains untouched. This is a decided
exclusion, not a gap: its origin `accFreshInv_append` is `private` to `Soundness.lean`, and
`LoopChecking.lean`'s import block (`FmpMeasure`, `FrameRules`, `Support.Accessibility`,
`Support.KnownWorlds` + Mathlib) does not include `Soundness.lean` — the two files are siblings,
never in an upstream relation. De-privatizing the origin would not help; a new import would be
required, which is out of this task's scope (class (c), import reachability, in the prior
task's exclusion taxonomy). Phase 1's drift guard reconfirmed both facts directly against the
live tree before Phase 2 wrote anything.

## Plan Deviations

None. All four phases were executed exactly as planned, with the two deferred-count corrections
in Phase 3 (the "55 minus N" and "remaining N comment sites" occurrences) folded into the same
edit as the explicitly-named headline count, since all three restate the identical quantity
within one bullet — a scope-preserving completion of the named task item, not a substitution.

## Testing & Validation — observed vs. baseline

| Gate | Baseline (research) | Observed | Status |
|---|---|---|---|
| `lake build Cslib` | exit 0, 3313 jobs | exit 0, 3313 jobs | PASS |
| `Modal/Tableau` sorry census | exactly 1 | 1 (`branchSatisfiableIn_s4FC_ancestor_redirect`, `FrameSoundness.lean`) | PASS |
| `Modal/Tableau` axiom census | 0 | 0 | PASS |
| `lake shake --add-public --keep-implied --keep-prefix` | 9 findings, exit 1, none in `Modal/Tableau` | 9 findings, exit 1, none in `Modal/Tableau` | PASS (delta 0) |
| `lake lint` | 145 findings, exit 1 | 145 findings, exit 1 | PASS (delta 0) |
| `lake exe checkInitImports` | exit 0 | exit 0 | PASS |
| `lake exe lint-style` | exit 0 | exit 0 | PASS |
| `lake test` | exit 0, 3676 jobs | exit 0 (job count not stable across consecutive invocations at this cache state -- 9378 then 3538 -- a pre-existing reporting quirk unrelated to this task) | PASS |
| Zero references to `modalSubfmls_self_mem_S5` under `Cslib/` | required | 0 matches | PASS |
| `accFreshInv_append_S4` untouched, present in `LoopChecking.lean` | required | present, unmodified | PASS |
| Exactly one declaration deleted across the whole task | required | 1 (`modalSubfmls_self_mem_S5`) | PASS |

No divergence from baseline on any gate. No `sorry` introduced. No new axioms. No new
definitions, lemmas, notation, or typeclasses.

## Files Modified

- `Cslib/Logics/Modal/Tableau/S5Simplification.lean` — deleted `private lemma
  modalSubfmls_self_mem_S5` (with its `omit` prefix and docstring), rewrote 8 call sites to
  `modalSubfmls_self_mem`, removed the now-empty `## \`modalSubfmls\` Structural Re-Derivations`
  module-docstring section.
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` — removed the orphaned `` `modalKnownWorlds`/
  `modalUniverse` Local Re-Derivations`` section header and body.
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — corrected the "Post-de-duplication update"
  comment-site count from 11 to 12 (three occurrences within the same bullet).
