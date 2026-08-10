# Handoff: Phase 9 COMPLETE -- plan's final phase closed, task 609 fully implemented

**Task**: 609 - Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows.
**Plan**: `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/plans/01_beta-priority-repair.md`
**Phase**: 9 ("The downstream `Completeness.lean` sorries and the 606 handoff") -- now `[COMPLETED]`.

**All 9 phases of the plan are now `[COMPLETED]`. The plan-level `- **Status**` field is set to
`[COMPLETED]`. This is the final dispatch for task 609.**

## What this dispatch did

At dispatch start, `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:191`
carried the ONLY declaration-level `sorry` left in the entire repo:
`intuitionisticTableau_complete` (DP-3), whose body was `sorry` with an in-source docstring
recording (a) the DP-3 obligation used to be genuinely open because `openBranch_countermodel`'s
upward-closure conjunct was open, and (b) even setting that aside, the bare one-liner the
research report quoted does not type-check because `IValid` quantifies `World : Type v` while the
countermodel frame is `Nat : Type 0`.

Both preconditions for closing DP-3 were satisfied by this point: Phase 8 (prior dispatch)
discharged `openBranch_countermodel` entirely, and `Minimal/Completeness.lean`'s
`minimalTableau_complete` (DP-4) already demonstrated the universe-pin pattern needed (pin the
theorem's own hypothesis to universe `0`, build a `ULift`-based descent lemma for callers who
have the unpinned form).

1. **Pinned `intuitionisticTableau_complete`'s hypothesis to `IValid.{_, 0} φ`** (mirroring
   `minimalTableau_complete`'s existing `MValid.{_, 0}` pin). Discharged the body with
   `exact @h Nat (intAccessPreorder edges) (intExtractValuation _b) _huc 0` -- `IValid` has no
   separate `bot_forces` argument (fixed to `fun _ => False`, matching `intScheme.modelBot`
   defeq), so `_hbuc` from `tableau_complete`'s three-hypothesis `intro` is simply unused, unlike
   `MValid`'s proof which threads `_hbuc` through explicitly.

2. **This pin change is a breaking change to `intuitionisticTableau_complete`'s public type**,
   confirmed by a scoped build of `Intuitionistic/DecisionProcedure.lean` immediately after step 1
   (deliberately, not by chance): it failed with a universe-mismatch application error at
   `intuitionisticTableau_decides` and a `Decidable (IValid φ)` synthesis failure at
   `instDecidableIValid`. Fixed by building the `IValid` analogue of
   `Minimal/DecisionProcedure.lean`'s `mvalid_descend` / `mvalid_universe_invariant` bridge:
   `ivalid_descend : IValid.{_, v} φ → IValid.{_, 0} φ` (via `ULift` transport, simplified
   relative to `mvalid_descend` since `IValid` carries no `bot_forces` argument to transport) and
   `ivalid_universe_invariant : IValid.{_, v} φ ↔ IValid.{_, 0} φ`. Re-pinned
   `intuitionisticTableau_decides` and `instDecidableIValid` to `IValid.{_, 0} φ` (mirroring
   `minimalTableau_decides`/`instDecidableMValid`'s existing pin) and routed
   `instDecidableDerivableIntPropAxiom` through the new bridge to keep its own public statement
   unpinned, mirroring `instDecidableDerivableMinPropAxiom` exactly.

3. **A second, further-downstream break surfaced at `SequentCalculus/LJ/Decidability.lean`**
   (not anticipated by the plan's "Files to modify" list, discovered by a repo-wide `lake build`
   after step 2): `instDecidableLJDerivable` relied on `instDecidableIValid`'s now-pinned
   `Decidable (IValid.{_, 0} φ)` instance resolving directly against `decidable_of_iff`'s implicit
   `[Decidable a]` search for the UNPINNED `IValid (ctxToImp Γ A)`, which unified the search to
   `Type 0` and then broke `lj_iff_ivalid.mp`/`.mpr` (which need `IValid.{u, u}`, `u` = `Atom`'s
   own universe). Fixed the same way as `instDecidableDerivableIntPropAxiom`: a local `letI`
   recovering an unpinned `Decidable (IValid _)` instance via `ivalid_universe_invariant` before
   `decidable_of_iff` runs.

4. **Rewrote the in-source prohibition and "Notes on sorry"** in
   `Intuitionistic/Completeness.lean` (module docstring, `intuitionisticTableau_complete`'s own
   docstring, and `intuitionisticOpenBranch_countermodel`'s docstring) to record that DP-3 is now
   discharged and name the discharging lemma (`openBranch_countermodel`, Phase 8), replacing the
   old "genuinely open, not refuted" language. Checked `Minimal/Completeness.lean` for a
   counterpart prohibition before touching it -- found none (605 had already fully retired it
   there) -- but its "Notes on sorry" and `minOpenBranch_countermodel` docstring still claimed
   `openBranch_countermodel` "still carries the deferred sorry", which was now false; updated
   those too.

5. **Also updated (deviation, scope expansion beyond the plan's named files)**: the parallel
   "Notes on sorry" / axiom-profile prose in `Intuitionistic/DecisionProcedure.lean`,
   `Minimal/DecisionProcedure.lean`, `Metalogic/IntDecidability.lean`, and
   `Metalogic/MinDecidability.lean` -- all four made some form of the same now-false claim
   ("carries the deferred completeness `sorryAx`", or cited specific now-stale sorry line
   numbers). Left untouched: a historical "STOP-gate finding" block deep in `Scheme.lean` (around
   line 740) that cites the old `Completeness.lean:113`/`Minimal/Completeness.lean:110` line
   numbers -- that block is explicitly self-labeled as a superseded historical record (predates
   the DP-5 `hpers` discharge) and `Scheme.lean` is outside Phase 9's declared file scope; editing
   arbitrary historical commentary throughout a 9800+ line file is not this phase's mandate.

## Verification (full pipeline, run twice -- once before, once after the two extra doc-only
Metalogic-file edits, to confirm no regression)

- `lake build` (full, 3325 jobs): green, no errors, both times.
- `lake exe checkInitImports`: clean.
- `lake lint`: zero findings attributable to any of the seven touched files (confirmed by grepping
  the full lint output for each file path; the pre-existing repo-wide noise, e.g. Bimodal/LTL/Modal
  unused-argument findings, is unrelated and unchanged).
- `lake exe lint-style`: clean.
- `lake shake --add-public --keep-implied --keep-prefix`: no import-minimization suggestion for
  any of the seven touched files (only the same two pre-existing `unusedDecidableInType` linter
  warnings that already existed on the Minimal side before this dispatch, now mirrored on the
  Intuitionistic side by the new `ivalid_universe_invariant`, exactly matching
  `mvalid_universe_invariant`'s pre-existing warning shape).
- `lake exe mk_all --module`: "No update necessary".
- `lake test`: green, 9397 jobs, exit 0, zero `✖` marks.
- **Declaration-level sorry count (whole repo, `lake build`'s `declaration uses 'sorry'`
  warnings): 1 -> 0.** The repo has zero declaration-level sorries.
- Axiom count: 26 -> 26 (unchanged). Vacuous-definition grep: 1 -> 1 (unchanged, pre-existing
  `Computability/URM/Basic.lean` false positive, same as every prior phase's report).
- `lean_verify` (after a genuinely fresh `lake build`, not just LSP cache) on
  `intuitionisticTableau_complete`, `minimalTableau_complete`, `instDecidableDerivableIntPropAxiom`,
  `instDecidableLJDerivable`, and `ivalid_descend`: all report only
  `{propext, Classical.choice, Quot.sound}` (or a strict subset), no `sorryAx`.
- A repo-wide `grep -rn '\bsorry\b'` still finds bare `sorry`s in `Cslib/Logics/Bimodal/**`
  (`TemporalConservativity.lean`, `ChronicleToCountermodel.lean`) -- these are pre-existing,
  entirely unrelated to propositional tableau completeness, and every one is wrapped in
  `set_option warn.sorry false in`, which is why they do not surface as `lake build`
  "declaration uses 'sorry'" warnings (the authoritative metric this task and its predecessor
  dispatches have used throughout).

## Files modified

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` -- DP-3 discharged,
  docstrings rewritten.
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean` -- `ivalid_descend` /
  `ivalid_universe_invariant` added; `intuitionisticTableau_decides`, `instDecidableIValid`
  re-pinned; `instDecidableDerivableIntPropAxiom` routed through the new bridge; docstrings
  updated.
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` -- `instDecidableLJDerivable`
  routed through `ivalid_universe_invariant`.
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` -- docstring-only (no theorem
  body change; DP-4 was already closed by 605).
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` -- docstring-only.
- `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` -- docstring-only.
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` -- docstring-only.
- `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/plans/01_beta-priority-repair.md`
  -- Phase 9 marked `[COMPLETED]`, task list checked off with a deviation annotation; plan-level
  `- **Status**` set to `[COMPLETED]`.

## Excluded constructions

Did not re-attempt any of the task's excluded constructions (rawEdges as the conjunct-2 witness,
pruning at blocked/strictly-blocked worlds, the greatest `IFimpAccess`-supported fixpoint, the
maximal atom-inclusion frame, V2/V3) -- none were relevant to this phase's scope (a universe-pin
bridge over an already-discharged conjunct), and none were touched.

## Task 606 reconciliation (the "606 handoff" this phase's title names)

Task 606 ("Discharge or restate the four propositional tableau completeness theorems and verify
the TFAE fold", `not_started`) names four sites: DP-3 (`intuitionisticTableau_complete`), DP-4
(`minimalTableau_complete`), DP-5 (`truthLemma`), DP-6 (`openBranch_countermodel`). **All four are
now sorry-free**: DP-3 by this phase; DP-4 by task 605; DP-5 by an earlier phase of this plan
(`hpers` positive-persistence hypothesis); DP-6 by Phase 8. Task 606's stated premise (four open
completeness sorries to discharge or restate) no longer holds against the current tree. Its
"HARD CONSTRAINT" (the TFAE fold in `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` must
still type-check) is independently confirmed satisfied: `ProofSystemEquivalence.lean` is part of
the full repo-wide `lake build` that went green in this dispatch's verification. Recommendation:
task 606 should be re-scoped or closed as superseded before any further dispatch on it -- its
description's line numbers and "four open sorries" framing are now stale, and dispatching against
it as written risks wasted analysis against a premise that no longer holds.

## Plan status

All 9 phases `[COMPLETED]`. Plan-level `- **Status**` field set to `[COMPLETED]`. This is the
final dispatch for task 609; no further phases remain.
