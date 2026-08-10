# Implementation Plan: Statement-Shape Fix for `minBranchBotForces` Upward Closure

- **Task**: 605 - establish_minbranchbotforces_upward_closure_at_bot
- **Status**: [IMPLEMENTING]
- **Effort**: 7 hours
- **Dependencies**: None (blocks nothing; interacts with 609 — see Coordination below)
- **Research Inputs**: `specs/605_establish_minbranchbotforces_upward_closure_at_bot/reports/01_minbranchbotforces-upward-closure.md`
- **Artifacts**: plans/01_statement-shape-fix.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Research established three machine-checked results: the `⊥`-instance of the upward-closure
obligation is free from the already-`χ`-general `IPosPersistRaw`; `tableau_complete`'s `hvalid`
premise shape is **refuted** for `minScheme`, making DP-4's `sorry` unclosable as stated; and a
statement-shape fix (adding a `modelBot` upward-closure conjunct to `openBranch_countermodel` and
the matching premise to `tableau_complete`) closes DP-4 end to end with the full project green.
The complete verified diff exists as `verified-shape-fix.patch` (130 insertions, 4 Lean files);
the working tree was deliberately reverted after verification because sibling work was in flight.

This plan sequences that patch into landable phases: land the refutation test, land the
`χ`-generalization independently, land the universe-invariance bridge additively (so no phase ever
leaves `DecisionProcedure.lean` red), then apply the shape fix as one declared atomic batch,
rewrite the in-source annotations to the resolved wording, and close with the full CSLib CI gate.

**Definition of done**: full `lake build` green, `lake test` green, the propositional tableau
completeness chain's sorry census down from 3 to 2, zero new sorries, zero new axioms.

### Research Integration

Every phase below traces to a verified result in the research report:

| Report section | Phase |
|---|---|
| §2 negative result, `MvalidBotShapeRefutation.lean.verified` | 1 |
| §3 positive result + frame generality (two monotonicity lemmas) | 2 |
| §4 "Discovered blocker: a universe pin is required" (`ULift` bridge) | 3 |
| §4 the end-to-end fix table (4 files) + §6 recommendation (A) | 4 |
| §6 annotation rewrite for DP-4 and the DP-3 universe-pin note | 5 |
| §5 verification record | 6 |

The research's own suggested phasing is 5 steps; this plan splits its step 4 into an additive
pre-pin bridge (Phase 3) and the pin itself (Phase 4). That split exists for a concrete reason:
pinning `minimalTableau_complete` to `MValid.{_, 0}` immediately breaks `minimalTableau_decides`
and `instDecidableMValid`, so pin-and-consumers cannot be separated, but the bridge lemmas
`mvalid_descend` / `mvalid_universe_invariant` **can** be proved before the pin exists and land
green on their own.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` supplied in the delegation context; no ROADMAP.md consulted.

### Coordination with Sibling Task 609

Sibling task 609 (researched in parallel, plan in flight) reorders `intStepBranch`'s rule
selection to beta-priority in the same `Intuitionistic/Scheme.lean`, and downstream task 606
depends on both. Four concrete interaction points, all of which the implementer must preserve:

1. **609's phase 4 discharges `openBranch_countermodel`.** After this plan lands, that lemma's
   existential carries a **third conjunct** (`S.modelBot b` upward closure). 609's discharge must
   produce all three conjuncts, not two. The witness is already supplied by this plan's Phase 2
   lemma `openBranch_rawEdges_both_upward_closed`, which hands back both upward-closure facts at
   one shared `edges`.
2. **609's phase 4 also plans "the two `Completeness.lean` one-liners".** After this plan lands
   under option A, the `Minimal/Completeness.lean` one-liner is **already closed** — 609's
   remaining call-site work on that file is nil, and only the intuitionistic (DP-3) one-liner
   remains.
3. **609's report quotes `exact h Nat (intExtractValuation _b) _huc 0` as the DP-3 one-liner.**
   Research proved that claim false: `MValid`/`IValid` quantify `World : Type v` while the
   countermodel frame is `Nat : Type 0`, so the DP-3 site needs the same `.{_, 0}` universe pin
   and the same `ULift` transport this plan builds in Phase 3. Phase 5 records that finding at
   the DP-3 site so 609 does not rediscover it.
4. **Territory overlap in `Scheme.lean`.** 609 edits the `intStepBranch` / `intExpandBranches.go`
   region (around the rule-selection code) and the `IReuseContain` threading; this plan edits the
   `isAccessible` monotonicity region, `openBranch_rawEdges_upward_closed`, and
   `openBranch_countermodel` / `tableau_complete` at the end of the file. The regions are
   disjoint, but both are in one 8,166-line file — whichever task lands second rebases rather
   than re-applies.

Phase 1 exists in part to detect, before any edit, whether 609 has already landed and invalidated
the saved patch.

## Goals & Non-Goals

**Goals**:
- Land the verified statement-shape fix: `modelBot` upward-closure conjunct on
  `openBranch_countermodel`, matching premise on `tableau_complete`, all four call sites repaired.
- Close DP-4's `sorry` in `Minimal/Completeness.lean` (research recommendation option A).
- Land `CslibTests/MvalidBotShapeRefutation.lean` as a permanent regression guard on the refuted
  premise shape.
- Generalize `openBranch_rawEdges_upward_closed` to arbitrary `χ` and add the two sub-frame
  monotonicity lemmas, so the result is not `rawEdges`-specific.
- Resolve the universe pin with a proved `ULift` transport, keeping
  `instDecidableDerivableMinPropAxiom` working at its original universe.
- Rewrite the DP-4 and DP-3 annotations to the resolved disposition, and record the universe-pin
  finding at the DP-3 site.

**Non-Goals**:
- Discharging `openBranch_countermodel`'s own existential `sorry`. That remains open and is 609's
  phase-4 target; this plan makes its statement stronger, not closed.
- Discharging DP-3 (`intuitionisticTableau_complete`'s deliberate `sorry`). It stays as-is; only
  its annotation gains the universe-pin note.
- Any change to `intStepBranch` rule-selection order, `IReuseContain`, or the beta-priority
  question — entirely 609's territory.
- Updating `CslibTests/BetaSplitRefutation.lean`'s `#guard_msgs` values. Those change only under
  609's calculus repair, not under this statement-shape change.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| 609 lands first and the saved patch no longer applies | M | M | Phase 1 runs `git apply --check` before any edit; on failure the implementer rebases hunk-by-hunk against the report's §4 change table rather than force-applying. The four hunks are small and the target regions are disjoint from 609's. |
| Verified patch carries `PROBE:` docstring markers from the research probe | M | H | Confirmed present on five declarations. Phases 2-4 explicitly require rewriting every `PROBE` docstring to production wording before commit; Phase 6's `lake lint` (docBlame) is the backstop. |
| Universe pin ripples further than the three named declarations | H | L | Phase 3 lands the bridge additively and green first; Phase 4's atomic batch then updates the three consumers together, so a wider ripple surfaces inside one phase's build rather than across a wave boundary. |
| Phase 4 leaves the tree red between file edits | H | H (by construction) | Declared `Commit Mode: atomic-batch`. The four files are one objective; intermediate per-file states are expected red and are not committed. |
| Option A (closing DP-4) is judged to break parity with DP-3's deliberate-sorry discipline | L | L | Option B is a two-line retreat: keep `sorry` in place of the `exact @h ...` term. Everything else in the plan is unaffected. Recorded under Rollback/Contingency. |
| Task-number citations leak into Lean docstrings during Phase 5 | M | M | `.claude/rules/no-task-references-in-deliverables.md` forbids task numbers outside `specs/**`. Phase 5's tasks require describing the beta-priority reorder by content, never by task number; the write-time hook is the backstop. |
| New test file not picked up by `lake test` | L | M | `CslibTests.lean` is a 26-import barrel; Phase 1 adds the `public import` line alongside the three existing `*Refutation` imports. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel. Phases 2 and 3 touch disjoint files
(`Intuitionistic/Scheme.lean` versus `Minimal/DecisionProcedure.lean`) and may be dispatched
concurrently with explicit file ownership.

---

### Phase 1: Baseline capture, patch-currency check, and refutation test landing [COMPLETED]

- **Goal:** Establish the pre-change baseline, confirm the saved patch still applies against the
  current tree, and land the refutation file as a permanent regression guard. Nothing in this
  phase depends on the shape fix.

- **Tasks:**
  - [x] Record the pre-change sorry census for the propositional tableau completeness chain
    (expected: 3 — `Scheme.lean` `openBranch_countermodel`, `Intuitionistic/Completeness.lean`
    DP-3, `Minimal/Completeness.lean` DP-4). Capture exact file:line for each.
    *(confirmed 3: `Scheme.lean:8034` `openBranch_countermodel`,
    `Intuitionistic/Completeness.lean:170` DP-3 `intuitionisticTableau_complete`,
    `Minimal/Completeness.lean:166` DP-4 `minimalTableau_complete`)*
  - [x] Run `git apply --check specs/605_establish_minbranchbotforces_upward_closure_at_bot/verified-shape-fix.patch`
    and record the result. If it fails, record which hunks conflict and note that later phases
    rebase against the report's §4 change table instead of applying the patch verbatim.
    *(patch applies cleanly against current HEAD — `git apply --check` exited 0)*
  - [x] Check whether sibling work has landed in `Intuitionistic/Scheme.lean` since the patch was
    verified (`git log --oneline -- Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`).
    *(no task 609 commits present; latest touching commit is task 604 phase 2, pre-dating this
    plan — 609 has not landed)*
  - [x] Copy `MvalidBotShapeRefutation.lean.verified` to
    `CslibTests/MvalidBotShapeRefutation.lean`, prepending the CSLib copyright header block used
    by `CslibTests/HvalidShapeRefutation.lean` and a `/-! # ... -/` module docstring that states
    what the file refutes: that `tableau_complete`'s `hvalid` body, with only the valuation
    upward-closure premise available, is false at an atom-free witness even though the formula is
    `MValid`. Do not cite task numbers in the file.
  - [x] Add `public import CslibTests.MvalidBotShapeRefutation` to `CslibTests.lean`, in
    alphabetical position among the existing imports.
  - [x] Build and test: `lake build CslibTests.MvalidBotShapeRefutation` then `lake test`.
    *(both green; only pre-existing sorry warnings emitted)*

- **Timing:** 1 hour

- **Depends on:** none

- **Verification Tier:** local

- **Scope Hypothesis:** The plan asserts (a) the saved patch applied cleanly as of 2026-08-09,
  (b) the chain's pre-change sorry count is 3, and (c) `CslibTests.lean` needs exactly one new
  import line. Confirm all three by the commands in the tasks above before proceeding; if (a)
  fails, treat every later phase's "apply the patch hunk" instruction as "reconstruct the hunk
  from the report's §4 change table".

- **Files to modify**:
  - `CslibTests/MvalidBotShapeRefutation.lean` - new file; the verified refutation plus CSLib
    header and module docstring
  - `CslibTests.lean` - one new `public import` line

- **Verification**:
  - `lake build CslibTests.MvalidBotShapeRefutation` green, zero sorries in the new file
  - `lake test` green
  - Baseline sorry census recorded with exact file:line for each of the three sites

---

### Phase 2: Chi-generalization and sub-frame monotonicity in `Scheme.lean` [COMPLETED]

- **Goal:** Generalize `openBranch_rawEdges_upward_closed` from `χ := .atom p` to arbitrary
  `χ : Proposition Atom`, add the two `isAccessible` sub-frame monotonicity lemmas, and expose
  both upward-closure facts at one shared `edges` witness. Isolated, sorry-free, and independently
  valuable even if nothing else in this plan lands.

- **Tasks:**
  - [x] Add `isAccessible_go_subset_mono` (private) next to the existing
    `isAccessible_go_append_mono`, modelled verbatim on that lemma's proof shape.
  - [x] Add `isAccessible_subset_mono` (private) next to `isAccessible_append_mono`.
  - [x] Add `intAccessPreorder_mono_subset`, lifting through `Relation.ReflTransGen.mono`.
  - [x] Generalize `openBranch_rawEdges_upward_closed`'s conclusion to the bare
    positive-formula-membership predicate quantified over `χ`, per the report's §3 statement. The
    proof body needs three substitutions: `.atom p` → `χ`, drop the `intExtractValuation` unfolds,
    bind `χ` in the `intro`.
  - [x] Add `openBranch_rawEdges_both_upward_closed`, deriving the valuation fact at `χ := .atom p`
    and the `⊥` fact at `χ := HasBot.bot` from one call to the generalized lemma.
  - [x] Rewrite every `PROBE:` / `**PROBE**:` docstring marker on these five declarations to
    production wording. State what each lemma says and why it exists (anti-monotonicity of upward
    closure in the edge set, so the result transfers to any sub-frame of `rawEdges`) — no probe
    language, no task numbers. *(all production wording; zero `PROBE` occurrences confirmed by
    grep)*
  - [x] Confirm no other call site of `openBranch_rawEdges_upward_closed` exists that the
    generalized statement breaks. *(grepped `Cslib/` and `CslibTests/` — zero external
    consumers, only the definition itself and doc-comment mentions)*

- **Timing:** 1.5 hours

- **Depends on:** 1

- **Verification Tier:** interface

- **Commit Mode:** per-substep

- **Scope Hypothesis:** The plan asserts five declarations change or are added in exactly one file
  (~90 lines of insertion), and that `openBranch_rawEdges_upward_closed` has no consumer outside
  this file that the generalized statement breaks. Confirm the second by grepping for the lemma
  name across `Cslib/` and `CslibTests/` before editing; if a consumer exists, repair it in this
  phase and record the count in the phase's completion note.

- **Files to modify**:
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - three new monotonicity
    lemmas, one generalized statement, one new combined lemma

- **Verification**:
  - `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` green, and the only
    remaining `sorry` in the module is the pre-existing `openBranch_countermodel` one
  - Enumerated direct dependents also build:
    `Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness`,
    `Cslib.Logics.Propositional.Tableau.Minimal.Completeness`
  - No occurrence of `PROBE` remains in the touched region

---

### Phase 3: Additive universe-invariance bridge in `DecisionProcedure.lean` [COMPLETED]

- **Goal:** Land `mvalid_descend` and `mvalid_universe_invariant` as purely additive, green
  lemmas, before any universe pin exists. This is what lets Phase 4 pin
  `minimalTableau_complete` without leaving `DecisionProcedure.lean` red.

- **Tasks:**
  - [x] Add `mvalid_descend : MValid.{_, v} φ → MValid.{_, 0} φ`, proved by lifting a `Type 0`
    model through `ULift` (`Preorder.lift ULift.down`) and transporting forcing back along
    `ULift.down` by induction on `φ`.
  - [x] Add `mvalid_universe_invariant : MValid.{_, v} φ ↔ MValid.{_, 0} φ`. The reverse direction
    composes `minimalTableau_complete` (instantiated at universe `0`, which type-checks against
    the current unpinned signature) with the universe-polymorphic `minimalTableau_sound`.
  - [x] Rewrite both `PROBE:` docstrings to production wording explaining that `MValid` is
    universe-invariant and why the `Type 0` direction needs an explicit `ULift` transport.
    *(zero `PROBE` occurrences confirmed by grep; also added `omit [DecidableEq Atom]
    [Hashable Atom] in` before `mvalid_descend` to clear an `unusedSectionVars` warning
    surfaced by the build)*
  - [x] Do **not** touch `minimalTableau_decides`, `instDecidableMValid`, or
    `instDecidableDerivableMinPropAxiom` in this phase — those change in Phase 4 together with the
    pin. *(confirmed unchanged in this commit)*

- **Timing:** 1 hour

- **Depends on:** 1

- **Verification Tier:** local

- **Commit Mode:** per-substep

- **Scope Hypothesis:** The plan asserts both bridge lemmas are provable against the *current,
  unpinned* `minimalTableau_complete` signature, so this phase is additive and green on its own.
  Confirm by building the module after adding them; if the reverse direction does not type-check
  pre-pin, merge this phase into Phase 4's atomic batch rather than weakening either statement.

- **Files to modify**:
  - `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - two new theorems

- **Verification**:
  - `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` green
  - Both new theorems sorry-free
  - No occurrence of `PROBE` remains in the touched region

---

### Phase 4: Statement-shape fix, DP-4 closure, and universe pin [NOT STARTED]

- **Goal:** Add the `modelBot` upward-closure conjunct through `openBranch_countermodel` and
  `tableau_complete`, mirror it at both `Completeness.lean` call sites, replace DP-4's `sorry`
  with the direct instantiation (research recommendation option A), and pin
  `minimalTableau_complete` to `MValid.{_, 0}` with its three consumers updated to route through
  the Phase 3 bridge.

- **Tasks:**
  - [ ] `Scheme.lean`: add the third conjunct
    `∀ {w w'}, w ≤ w' → S.modelBot b w → S.modelBot b w'` to `openBranch_countermodel`'s
    existential. It goes behind the existing `sorry`; no new sorry is introduced.
  - [ ] `Scheme.lean`: add the matching premise to `tableau_complete`'s `hvalid`, and destructure
    the now-4-tuple in its `openBranch` branch (`⟨edges, huc, hbuc, hcm⟩`).
  - [ ] `Intuitionistic/Completeness.lean`: mirror the conjunct on
    `intuitionisticOpenBranch_countermodel`, and add `_hbuc` to the `intro` at
    `intuitionisticTableau_complete`. For `intScheme`, `modelBot = fun _ => False`, so the
    conjunct is trivial — zero proof cost on the intuitionistic side. DP-3's `sorry` stays.
  - [ ] `Minimal/Completeness.lean`: mirror the conjunct on `minOpenBranch_countermodel`; pin
    `minimalTableau_complete` to `(h : MValid.{_, 0} φ)`; replace the DP-4 `sorry` with
    `exact @h Nat (intAccessPreorder edges) (intExtractValuation _b) (minBranchBotForces _b) _huc _hbuc 0`.
  - [ ] `Minimal/DecisionProcedure.lean`: pin `minimalTableau_decides` and `instDecidableMValid`
    to `MValid.{_, 0}`, and give `instDecidableDerivableMinPropAxiom` a
    `letI : Decidable (MValid φ) := decidable_of_iff (MValid.{_, 0} φ) (mvalid_universe_invariant φ).symm`
    so its original statement is preserved.
  - [ ] Verify the whole batch together — intermediate per-file states are expected red and must
    not be committed.

- **Timing:** 1.5 hours

- **Depends on:** 2, 3

- **Verification Tier:** full

- **Commit Mode:** atomic-batch

- **Scope Hypothesis:** The plan asserts exactly four files and six edit sites
  (`openBranch_countermodel`, `tableau_complete`, `intuitionisticOpenBranch_countermodel` +
  `intuitionisticTableau_complete`'s `intro`, `minOpenBranch_countermodel`,
  `minimalTableau_complete`, and three `DecisionProcedure.lean` declarations). Confirm by grepping
  for every consumer of `openBranch_countermodel` and `tableau_complete` across `Cslib/` and
  `CslibTests/` before editing; any consumer beyond this list joins the same atomic batch. The
  anti-abuse guard applies: the batch is declared here, in advance, and must not be widened
  retroactively to avoid committing already-green work.

- **Files to modify**:
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - third conjunct on
    `openBranch_countermodel`; matching `hvalid` premise and 4-tuple destructure on
    `tableau_complete`
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` - mirrored conjunct;
    `_hbuc` in the `intro`
  - `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - mirrored conjunct; universe
    pin; DP-4 `sorry` replaced by the direct instantiation
  - `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - universe pin on two
    declarations; bridge routing in `instDecidableDerivableMinPropAxiom`

- **Verification**:
  - Full `lake build` green
  - `Minimal/Completeness.lean` is sorry-free
  - Chain sorry census is 2 (`Scheme.lean`'s `openBranch_countermodel`,
    `Intuitionistic/Completeness.lean`'s DP-3) — down from 3
  - Zero new axioms: `lean_verify` on `minimalTableau_complete`, `minimalTableau_decides`, and
    `instDecidableDerivableMinPropAxiom` shows no axiom beyond the pre-existing `sorryAx` taint
    inherited from `openBranch_countermodel`

---

### Phase 5: Rewrite in-source annotations to the resolved disposition [NOT STARTED]

- **Goal:** Bring every docstring and inline annotation that describes the old two-obligation
  framing into line with what is now true, and record the universe-pin finding where the DP-3 site
  will need it.

- **Tasks:**
  - [ ] `Minimal/Completeness.lean`: rewrite `minimalTableau_complete`'s docstring. Remove the
    "two upward-closure premises / DP-4 is open" framing and the stale `sorry` narrative. State
    plainly that the site now rests on `openBranch_countermodel` alone, that the `⊥`-shape
    obligation is discharged via the `χ`-general raw-edge persistence lemma, and that the earlier
    premise shape was refuted by `CslibTests/MvalidBotShapeRefutation.lean`.
  - [ ] `Minimal/Completeness.lean`: update `minOpenBranch_countermodel`'s docstring for the third
    conjunct, replacing the "only ONE of `MValid`'s two upward-closure premises" sentence.
  - [ ] `Minimal/Completeness.lean` / `Minimal/DecisionProcedure.lean`: update the "Notes on
    sorry" sections for the new census.
  - [ ] `Intuitionistic/Completeness.lean`: add the universe-pin note to DP-3's docstring — the
    quoted one-liner `exact h Nat (intExtractValuation _b) _huc 0` does **not** type-check as
    written, because `IValid` quantifies `World : Type v` while the countermodel frame is
    `Nat : Type 0`; closing DP-3 will need the same `.{_, 0}` pin and the `ULift` transport now
    available in `Minimal/DecisionProcedure.lean`. Keep the deliberate `sorry` and its existing
    rationale intact.
  - [ ] `Scheme.lean`: update `openBranch_countermodel`'s and `tableau_complete`'s docstrings to
    describe the third conjunct and to note that a sub-frame of `rawEdges` discharges both
    upward-closure conjuncts via `openBranch_rawEdges_both_upward_closed`.
  - [ ] `CslibTests/MvalidBotShapeRefutation.lean`: if the module docstring written in Phase 1
    described the defect as live, adjust it to record that the shape is now fixed and this file
    stands as the regression guard.
  - [ ] Cite durable anchors only — lemma names, file paths, section headings. No task numbers in
    any file outside `specs/**`; describe the sibling beta-priority rule-selection reorder by
    content if it is mentioned at all.

- **Timing:** 1 hour

- **Depends on:** 4

- **Verification Tier:** local

- **Commit Mode:** per-substep

- **Scope Hypothesis:** The plan asserts five annotation sites across four Lean files. Confirm by
  grepping for the stale phrases (`two upward-closure`, `DP-4`, `named residual`, `SEPARATE fact`)
  across `Cslib/Logics/Propositional/Tableau/` before editing; every hit is either rewritten or
  explicitly justified as still-accurate in the phase completion note.

- **Files to modify**:
  - `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - docstrings and notes
  - `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - notes
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` - DP-3 universe-pin note
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - two docstrings
  - `CslibTests/MvalidBotShapeRefutation.lean` - module docstring wording

- **Verification**:
  - Each touched module builds (`lake build` on the four `Cslib.…` module names plus
    `CslibTests.MvalidBotShapeRefutation`) — Lean docstrings elaborate, so a comment-only edit is
    still a compile surface
  - No `grep -rn "task [0-9]"` hit in any touched file
  - No stale phrase from the Scope Hypothesis list survives unjustified

---

### Phase 6: Full CSLib CI gate and zero-debt verification [NOT STARTED]

- **Goal:** Run the complete CSLib verification pipeline and confirm the zero-debt claims the
  research report makes.

- **Tasks:**
  - [ ] `lake exe cache get` (if the Mathlib cache is cold)
  - [ ] `lake build` — full project, expected green
  - [ ] `lake exe checkInitImports`
  - [ ] `lake lint` — resolve any `docBlame` hit on the new declarations
  - [ ] `lake exe lint-style`
  - [ ] `lake test`
  - [ ] `lake shake --add-public --keep-implied --keep-prefix`
  - [ ] Confirm the final sorry census in the propositional tableau completeness chain is exactly
    2, and that both remaining sites are the pre-existing `openBranch_countermodel` existential
    and DP-3
  - [ ] Confirm zero new axioms across the changed declarations
  - [ ] Write the implementation summary, recording the option-A decision and the four 609
    interaction points so task 606 can reconcile

- **Timing:** 1 hour

- **Depends on:** 5

- **Verification Tier:** full

- **Commit Mode:** per-substep

- **Files to modify**:
  - Lint-driven touch-ups only, if any
  - `specs/605_establish_minbranchbotforces_upward_closure_at_bot/summaries/01_statement-shape-fix-summary.md`

- **Verification**:
  - Every step of the 7-step CSLib CI order passes
  - Sorry census 3 → 2 confirmed; zero new sorries; zero new axioms

---

## Testing & Validation

- [ ] `lake build` (full project) green
- [ ] `lake test` green, including the new `CslibTests/MvalidBotShapeRefutation.lean`
- [ ] `lake lint` clean on all new and changed declarations (docBlame in particular — five
      declarations arrive with probe-era docstrings)
- [ ] `lake exe lint-style` clean
- [ ] `lake exe checkInitImports` clean
- [ ] Sorry census in `Cslib/Logics/Propositional/Tableau/` reduced from 3 to 2; the two survivors
      are `Scheme.lean`'s `openBranch_countermodel` and `Intuitionistic/Completeness.lean`'s DP-3
- [ ] Zero new axioms (`lean_verify` on `minimalTableau_complete`, `minimalTableau_decides`,
      `instDecidableMValid`, `instDecidableDerivableMinPropAxiom`)
- [ ] `instDecidableDerivableMinPropAxiom`'s public statement is unchanged despite the universe pin
- [ ] No `PROBE` marker survives anywhere in `Cslib/`
- [ ] No task-number citation in any file outside `specs/**`

## Artifacts & Outputs

- `CslibTests/MvalidBotShapeRefutation.lean` (new)
- `CslibTests.lean` (one import line)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`
- `specs/605_establish_minbranchbotforces_upward_closure_at_bot/summaries/01_statement-shape-fix-summary.md`

## Rollback/Contingency

- **Per-phase**: every phase except 4 is `per-substep` and ends green, so a single `git revert` of
  that phase's commit restores a buildable tree. Phase 4 is one atomic-batch commit covering four
  files, so it reverts as a unit.
- **Option B fallback**: if closing DP-4 is judged to break parity with DP-3's deliberate-sorry
  discipline, restore the `sorry` in place of Phase 4's
  `exact @h Nat (intAccessPreorder edges) …` term. The universe pin is then no longer required, so
  Phase 4's `Minimal/DecisionProcedure.lean` edits and Phase 3's bridge become unnecessary but
  harmless (they are additive and independently green). Everything else — the third conjunct, the
  `χ`-generalization, the refutation test, the annotation rewrite — stands unchanged. The
  annotation in Phase 5 would then say the `⊥` obligation is discharged and the shape defect
  refuted, with one obligation remaining rather than zero at this site.
- **If 609 lands first and conflicts**: rebase the four Phase 4 hunks against the report's §4
  change table rather than force-applying the saved patch. The conjunct addition and the call-site
  repairs are each a few lines; the `χ`-generalization in Phase 2 is the only hunk with
  substantial proof-body movement, and its target region (`isAccessible` monotonicity,
  `openBranch_rawEdges_upward_closed`) is disjoint from 609's `intStepBranch` region.
