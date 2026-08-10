# Implementation Plan: Task #606

- **Task**: 606 - Discharge or restate the four propositional tableau completeness theorems and verify the TFAE fold
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: 603, 604, 605, 609 (all complete)
- **Research Inputs**: specs/606_discharge_propositional_tableau_completeness_and_verify_tfae/reports/01_tableau-completeness-ground-truth.md
- **Artifacts**: plans/01_tfae-fold-and-annotation-closeout.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Research established, by `lean_verify` on fully-qualified names plus a green `lake build`
(exit 0, 3325 jobs), that all four DP sites (`intuitionisticTableau_complete`,
`minimalTableau_complete`, `truthLemma`, `openBranch_countermodel`) are already sorry-free and
axiom-clean at `{propext, Classical.choice, Quot.sound}`. Scope items (a) discharge each sorry
and (b) repair call sites therefore require no work, and no theorem needs restatement — so the
task's "laundering a sorry via a weakened statement" prohibition is not engaged at any point in
this plan.

Two things genuinely remain. First, the task's HARD CONSTRAINT — that the landed statements be
strong enough to fold tableau nodes into the CPL/IPL/MPL TFAEs — was **untested, not satisfied**:
`ProofSystemEquivalence.lean` contains no tableau node at all. Research machine-verified the fold
with a 6-probe file compiled by `lake env lean` (exit 0, zero errors, zero warnings), preserved at
`/tmp/claude-1000/-home-benjamin-Projects-cslib/2b7a4a92-9db5-490b-8511-e9e6eb44721a/scratchpad/tfae_probe.lean`.
Second, roughly twelve annotation blocks now contradict the landed proofs — most severely
`Scheme.lean:9682`, whose docstring declares "KNOWN IMPOSSIBLE" a reconciliation that a
sorry-free proof performs twenty lines above it.

**Definition of done**: the three four-node TFAE theorems land and type-check; every annotation
block enumerated in report sections 3.1-3.5 describes the landed state; `lake build`, `lake test`,
and `lake exe lint-style` are all green; zero new sorries and zero new axioms.

### Research Integration

- Report section 1 supplies the four verified axiom profiles and the DP-3 prohibition resolution
  (the `exact @h Nat ...` shape is used, but `_huc` is genuinely proved at `Scheme.lean:9645-9665`
  via `hpersAug`, so nothing is laundered — no action at DP-3).
- Report section 2.3 supplies verbatim, compiler-verified proof text for all three folds.
- Report section 2.4 supplies two empirically-discovered gotchas, both incorporated as explicit
  Phase 1 tasks: `rw` cannot apply the universe-invariance lemmas (universe metavariable
  unsolvable — use term-mode `Iff.trans`), and `[Hashable Atom]` is missing from the file's
  `variable` line at `:47`.
- Report sections 3.1-3.5 supply the annotation inventory that Phases 2-5 execute against.
- Report section 4 confirms no new abstraction is needed anywhere: the folds are pure
  compositions of six existing named bridge theorems plus two existing universe-invariance lemmas.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found; no roadmap flag set.

## Decisions on the Three Open Questions

The researcher deliberately left three questions to the planner. All three are decided here and
are binding on the implementer.

| # | Question | Decision | Rationale |
|---|----------|----------|-----------|
| (a) | Tableau node on the context-based TFAEs (`cplProofSystemsTfae` / `iplProofSystemsTfae` / `mplProofSystemsTfae`)? | **NO** — fold into the three `...Closed` variants only | The tableau procedures take a closed formula and no context argument, so a context-based node is new proof work via a deduction-theorem route, not a fold; the task's hard constraint is satisfied by the `...Closed` folds. |
| (b) | Are `Metalogic/IntDecidability.lean`, `Metalogic/MinDecidability.lean`, `Tableau/Intuitionistic/Expansion.lean` in scope? | **YES** — explicit `file_scope` widening, recorded below | They carry the identical stale claim; leaving them makes the repo's account of its own state inconsistent again the moment this task closes, which is the exact failure mode the task exists to end. |
| (c) | Retain the now-unused `openBranch_rawEdges_upward_closed` / `openBranch_rawEdges_both_upward_closed`? | **YES** — retain both, with corrected docstrings | They are the durable record of the raw-frame route and cost nothing; deleting them would destroy the explanation of why the augmented-frame route exists, contradicting the task's preserve-the-counter-instance-record precedent. |

**file_scope widening (explicit)**: the task's declared four-file `file_scope` is widened by
decision (b) to seven files. Added: `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean`,
`Cslib/Logics/Propositional/Metalogic/MinDecidability.lean`,
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`. All three additions are
docstring/comment-only edits; no declaration in any of them is touched.

## Goals & Non-Goals

**Goals**:
- Land three four-node TFAE theorems (CPL, IPL, MPL) folding the tableau decision procedures into
  the closed-formula proof-system equivalences, reusing the machine-verified probe text verbatim.
- Bring every stale annotation block in report sections 3.1-3.5 into agreement with the landed,
  sorry-free proofs — eliminating the `Scheme.lean:9682` internal contradiction first.
- Preserve, by re-tensing rather than deleting, every counter-instance and refutation record that
  explains why the current hypotheses (`hpersAug`, the R1 preconditions, the loop-back
  re-validation) exist at all.
- Finish with `lake build`, `lake test`, and `lake exe lint-style` all green, zero new sorries,
  zero new axioms.

**Non-Goals**:
- Restating any of the four DP theorems. Research confirms none requires it.
- Touching the DP-3 proof. The in-source prohibition is resolved, not violated.
- Adding a tableau node to the three context-based TFAEs (decision (a)).
- Widening the `[Hashable Atom]` constraint onto the six existing TFAE signatures (the new-section
  route is used instead; see Phase 1).
- Deleting any refutation or counter-instance record.
- "Fixing" the two pre-existing `linter.unusedDecidableInType` warnings on
  `ivalid_universe_invariant` / `mvalid_universe_invariant` — out of scope, and changing those
  signatures would touch the `Decidable` instances.
- Converting the retained raw-edges lemmas into live call sites, or deleting them.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Implementer re-derives the fold proofs instead of reusing the verified probe text, and burns cycles on the `rw` universe-metavariable failure | M | M | Phase 1 tasks name the probe file path and quote the term-mode `Iff.trans` form; `plan-compliance.md` forbids substituting an alternative approach |
| Missing `[Hashable Atom]` causes an elaboration failure that tempts widening the six existing signatures | M | M | Phase 1 mandates a new section with a local `variable [Hashable Atom]`; widening the existing six is listed as a Non-Goal |
| New public imports pull `Scheme.lean` (9833 lines) into `ProofSystemEquivalence.lean`, materially raising that module's build cost | L | H | Accepted and expected; Phase 1 verification is scoped to the module plus its one dependent (`Cslib.lean`), with the full build deferred to Phase 6 |
| Docstring edit accidentally crosses a `/--`/`-/` boundary and breaks parsing of a 9833-line file | H | L | Phases 2-5 carry Verification Tier `local` (build the single edited module), not `prose`, precisely because Lean docstrings have a parse surface |
| Over-zealous cleanup deletes a counter-instance record instead of re-tensing it | H | M | Phase 3 states PRESERVE-DO-NOT-DELETE as its goal and requires each edit to retain the `phiRef1` / pre-repair content while marking it historical |
| Rewritten annotations re-introduce line-number citations that drift again | M | H | Phase 5 mandates declaration names over line numbers wherever a rewrite has the choice |
| `lake test` `#guard_msgs` assertions in `CslibTests/` are perturbed | H | L | No Lean term or tactic in any tested declaration is edited by Phases 2-5; Phase 6 runs `lake test` explicitly to confirm |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 2 |
| 3 | 4 | 3 |
| 4 | 5 | 4 |
| 5 | 6 | 1, 5 |

Phases within the same wave can execute in parallel.

**Territory note**: Phase 1 owns `ProofSystemEquivalence.lean` exclusively; Phase 2 owns
`Scheme.lean`. They share no file and are safe to run concurrently. Phases 2, 3, 4, and 5 all
touch `Scheme.lean` and are therefore chained sequentially rather than parallelized, despite being
documentation-only.

---

### Phase 1: Land the TFAE fold in ProofSystemEquivalence.lean [COMPLETED]

**Goal**: Add the three four-node TFAE theorems (CPL, IPL, MPL) that fold each tableau decision
procedure into the corresponding closed-formula proof-system equivalence, satisfying the task's
HARD CONSTRAINT with a type-checked artifact rather than an assumption.

**Tasks**:
- [x] Read the verified probe file at
      `/tmp/claude-1000/-home-benjamin-Projects-cslib/2b7a4a92-9db5-490b-8511-e9e6eb44721a/scratchpad/tfae_probe.lean`
      and reuse its proof bodies verbatim. Do not re-derive them.
- [x] Add four `public import` lines to `Cslib/Logics/Propositional/ProofSystemEquivalence.lean`:
      `Cslib.Logics.Propositional.Tableau.Intuitionistic.DecisionProcedure`,
      `Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure`,
      `Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure`,
      `Cslib.Logics.Propositional.Metalogic.StrongCompleteness`.
- [x] Open `Cslib.Logic.Tableau` alongside the existing `open InferenceSystem`.
- [x] Open a NEW section carrying a local `variable [Hashable Atom]`. Do NOT add `[Hashable Atom]`
      to the file's `variable` line at `:47`, and do NOT widen the six existing TFAE signatures.
- [x] Add `cplProofSystemsWithTableauTfae`: nodes `Derivable PropositionalAxiom φ`, ND at `∅`,
      `Nonempty (LKProof ((∅ : Ctx Atom) ⊢ₛ ({φ} : Finset _)))`, `classicalTableau φ = .closed`.
      Bridge node 1 ↔ 4 with `rw [← prop_completeness_iff_tautology, ← classicalTableau_decides]`.
- [x] Add `iplProofSystemsWithTableauTfae`: nodes `Derivable IntPropAxiom φ`, ND at `∅`,
      `Nonempty (LJProof ((∅ : Ctx Atom) ⊢ φ))`, `intuitionisticTableau φ = .closed`. Bridge
      node 1 ↔ 4 with the term-mode composition
      `int_soundness_completeness.symm.trans ((ivalid_universe_invariant φ).trans (intuitionisticTableau_decides φ).symm)`.
      Do NOT attempt `rw [ivalid_universe_invariant]` — it fails with an unsolvable universe
      metavariable (`Did not find an occurrence of the pattern IValid ?φ`).
- [x] Add `mplProofSystemsWithTableauTfae`: the exact MPL analogue via
      `min_soundness_completeness` / `mvalid_universe_invariant` / `minimalTableau_decides`.
- [x] Give each new theorem a docstring in the file's existing house style (a `**Bold Title**`
      line, the numbered node list, then the composition rationale) — required for `docBlame`.
- [x] Use `theorem` (not `lemma`) and lowerCamelCase names without underscores, matching the six
      siblings.
- [x] Update the module docstring's `## Main Results` list (`:22-31`) to name the three new
      theorems, and its `## Dependencies` list (`:33-38`) to name the three bridge families
      (`prop_completeness_iff_tautology`/`classicalTableau_decides`,
      `int_soundness_completeness`/`ivalid_universe_invariant`/`intuitionisticTableau_decides`,
      `min_soundness_completeness`/`mvalid_universe_invariant`/`minimalTableau_decides`).
      Also update the opening prose, which currently claims the module collects *three-way*
      equivalences only.
- [x] Run `lake build Cslib.Logics.Propositional.ProofSystemEquivalence`, then
      `lake build Cslib` to confirm the barrel still elaborates.
- [x] Run `lean_verify` on the three new fully-qualified theorem names; confirm the axiom set is
      exactly `{propext, Classical.choice, Quot.sound}` and no `sorryAx` appears.

**Timing**: 1.25 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: This phase asserts exactly three new theorems and exactly four new
`public import` lines, with zero edits to any existing declaration body. Confirm at implementation
time by diffing `ProofSystemEquivalence.lean` and checking that the only changed regions are the
import block, the `open` line, the module docstring, and one appended section.

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` - four public imports, one `open`
  addition, module docstring update, one new section with three TFAE theorems

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystemEquivalence` exits 0 with zero errors.
- `lake build Cslib` exits 0.
- `lean_verify` on each of the three new names reports no `sorryAx` and the clean three-axiom set.
- `grep -c 'sorry' Cslib/Logics/Propositional/ProofSystemEquivalence.lean` returns 0.

---

### Phase 2: Remove the KNOWN IMPOSSIBLE claim in Scheme.lean [COMPLETED]

**Goal**: Eliminate the file's central internal contradiction by rewriting
`openBranch_rawEdges_upward_closed`'s docstring, and record the retention rationale for both
now-unused raw-edges lemmas per decision (c).

**Tasks**:
- [x] Read `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` around `:9640-9700` to
      re-locate the docstring (line numbers in the report may have drifted; anchor on the
      declaration name `openBranch_rawEdges_upward_closed`, not the line number).
- [x] Rewrite the docstring, deleting every one of these now-false present-tense clauses:
      (i) that `openBranch_countermodel` carries a `sorry`; (ii) that it "commits to no `edges`
      witness at all"; (iii) that reconciling the two conjuncts over one uniform `edges` is
      "KNOWN IMPOSSIBLE"; (iv) that closing the gap is calculus-level work "outside this file's
      scope".
- [x] Replace with the landed account: `openBranch_countermodel` is sorry-free and commits to the
      augmented-frame witness; the reconciliation the old text called impossible is performed in
      this same file via `hpersAug`; the calculus-level `intFImpReuseWitnessAnc?` loop-back
      re-validation that made it possible has landed. Cross-reference the frame-adequacy table by
      its content ("augmented, post-repair | holds | holds"), not by line number.
- [x] State plainly that this lemma is **retained but not on the live route** — it is the durable
      record of the raw-frame approach, superseded by the augmented-frame route through
      `hpersAug`. Do not delete it and do not mark it deprecated.
- [x] Apply the same retention wording to `openBranch_rawEdges_both_upward_closed`'s docstring.
- [x] Confirm by inspection of the resulting diff that every changed hunk lies inside a `/-- -/`
      docstring and no declaration body, binder, or statement was touched.
- [x] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts the contradiction is confined to two docstrings (those of
`openBranch_rawEdges_upward_closed` and `openBranch_rawEdges_both_upward_closed`). Confirm at
implementation time with `grep -n 'KNOWN IMPOSSIBLE' Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
returning zero matches after the edit, and by checking no other declaration's docstring makes the
same impossibility claim.

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - docstrings of
  `openBranch_rawEdges_upward_closed` and `openBranch_rawEdges_both_upward_closed`

**Verification**:
- `grep -n 'KNOWN IMPOSSIBLE' Cslib/.../Scheme.lean` returns no matches.
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` exits 0.
- Diff review confirms all changed lines are inside docstrings.

---

### Phase 3: Re-tense the augmented-frame refutation claims as historical [COMPLETED]

**Goal**: Convert every present-tense "REFUTED at the augmented frame" assertion into an
explicitly pre-repair, historical record — **preserving the content**, because the `phiRef1`
counterexample is precisely why `hpersAug` and the loop-back re-validation exist.

**Tasks**:
- [x] Re-locate each site by content search rather than by line number; the report catalogues six:
      `Scheme.lean:796-800` (obstruction "real only at the AUGMENTED frame"),
      `Scheme.lean:849-851` ("does not discharge the `sorry` immediately below ... refuted at
      `phiRef1`"), `Scheme.lean:1000-1008` (in-proof comment, "`hpers` is REFUTED at the AUGMENTED
      frame"), `Scheme.lean:7226-7233` (`IPosPersistRaw` docstring, "now known-refuted rather than
      pending"), and `Expansion.lean:525-545` ("Recorded limitation: a FRAME-CONSTRUCTION defect
      ... never re-validated afterwards"). The sixth, `Scheme.lean:9682-9688`, is already handled
      by Phase 2 — verify it, do not re-edit it.
- [x] For each site, re-tense to a pre-repair frame: name what was refuted, at which witness
      (`phiRef1`), against which pre-repair calculus, and state that the repair
      (`intStepBranchPrio` beta-priority, plus the `intFImpReuseWitnessAnc?` loop-back
      re-validation) closed it. Keep the counterexample itself intact.
- [x] Where a site cites `CslibTests/BetaSplitRefutation.lean` as a current refutation, re-tense to
      match that file's own module header: it refutes the PRE-repair calculus, and every
      `#guard_msgs` assertion in it now passes against the REPAIRED calculus.
- [x] MUST NOT delete any counter-instance record, witness formula, or refutation narrative. The
      precedent is `intExpandBranches_openBranch_sat`'s surviving counter-instance record, which
      remains the durable explanation of why the R1 hypotheses exist.
- [x] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` and
      `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion`.

**Deviation note**: while re-tensing the `Scheme.lean:908-941`-area paragraph (self-copy-channel
analysis note), its REFUTED clause was inextricable from its adjoining "still open ... surviving
existential" clause (one sentence covers both) — that is one of the ten sites Phase 4's task list
also names (`Scheme.lean:908-941`, "Recommendation for continuation" / "surviving existential").
Both clauses were re-tensed together here rather than leaving the sentence half-stale; Phase 4
verifies this site rather than re-editing it.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Scope Hypothesis**: The report asserts six sites carrying this claim, one of which
(`Scheme.lean:9682-9688`) is closed by Phase 2, leaving five to edit here. Confirm at
implementation time by grepping the two files for `REFUTED`, `refuted`, and `never re-validated`
and reconciling the hit list against the five; any additional hit is an undercount and must be
handled in this phase, and any absent site recorded as such.

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - four sites (docstrings and one
  in-proof comment)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - the recorded-limitation
  block (scoped in by decision (b))

**Verification**:
- Grep for `REFUTED` / `refuted` in both files: every surviving hit reads as historical/pre-repair.
- The `phiRef1` witness and the recorded-limitation narrative are still present (record survives).
- Both scoped `lake build` invocations exit 0.

---

### Phase 4: Clear the "still open / still sorry" claims [COMPLETED]

**Goal**: Bring the ten stale open-obligation claims catalogued in report section 3.3 into
agreement with the sorry-free landed state.

**Tasks**:
- [x] `Scheme.lean` "Blocker (documented, not a `sorry`...)" block plus its "Recommendation for
      continuation": both cited sorries no longer exist and both line refs are stale; rewrite to
      record that monotonicity is now supplied by `hpersAug`.
- [x] `Scheme.lean` "Gap 1 (fuel entanglement) is UNCHANGED and remains the sole blocker." — the
      heading still reads as current even though a later line already says the claim is STALE.
      Fold the correction into the heading rather than leaving a self-contradicting pair.
- [x] `Scheme.lean` "The case nonetheless **stays `sorry`**" — DP-5 is discharged; rewrite.
- [x] `Scheme.lean` "Recommendation for continuation" + "still open ... `openBranch_countermodel`'s
      own surviving existential" — that existential is discharged; rewrite. *(deviation: this
      exact sentence was already re-tensed in Phase 3, since its REFUTED clause and its
      still-open clause were one inseparable sentence; verified here as already correct, not
      re-edited — see Phase 3's deviation note.)*
- [x] `Scheme.lean` `truthLemma` docstring opening "the single deferred completeness obligation" —
      it defers nothing; rewrite.
- [x] `Scheme.lean` "DP-2 strategic sorry ... this lemma's proof is deferred ... Follow-up: DP-2,
      see the plan's Planned Strategic Sorries table" — no DP-2 sorry exists and the file is
      sorry-free; rewrite.
- [x] `Scheme.lean` "Re-validating it is what lets the augmented frame carry positive persistence
      ... and closing this lemma's `sorry`" — present-tense residue; make it past-tense ("closed").
- [x] `Scheme.lean` "This theorem is sorry-free **given** `openBranch_countermodel S`; the deferred
      obligation ... now lives entirely inside `openBranch_countermodel`" — drop the conditional
      framing; the obligation is discharged, so the theorem is sorry-free outright.
- [x] `Tableau/Intuitionistic/Completeness.lean` "The single deferred completeness obligation now
      lives in `openBranch_countermodel`" — same phrase, same staleness; rewrite.
- [x] `Tableau/Minimal/Completeness.lean` — identical phrase; rewrite identically.
- [x] While in `Completeness.lean`, confirm (do not edit) that the DP-3 docstring's existing
      explanation of why the in-source prohibition no longer applies is accurate and retained.
      Confirmed at `Completeness.lean:52-60` ("DP-3, historical record") and `:170-176` ("DP-3,
      now sorry-free") — both accurate, not edited.
- [x] Scoped `lake build` of each of the three modules.
- [x] *(deviation: additional in-scope fix found during the Phase 4 sweep, not pre-declared)*
      `Scheme.lean`'s `IAllReuseFrozenOrigin` docstring claimed "plan Phase 6 task-list item (d),
      still open" — directly contradicted by task 609 phase 6.5's commit message ("thread
      IAllReuseFrozenOrigin through the key induction (item d)") and by the `hPendingARFO`/
      `hDoneARFO` hypotheses now present in `intExpandBranches_openBranch_sat`'s own statement.
      Rewritten to "closed".

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: local

**Scope Hypothesis**: The report enumerates ten sites across three files (eight in `Scheme.lean`,
one each in the two `Completeness.lean` files). Confirm at implementation time by grepping all
three files for `still open`, `stays `sorry``, `deferred`, `remains the sole blocker`, and
`surviving existential`, and reconciling the hit list against the ten; treat any extra hit as
in-scope for this phase rather than deferring it.

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - eight annotation blocks
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` - one block
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - one block

**Verification**:
- No surviving present-tense claim in any of the three files asserts an open sorry or a deferred
  obligation in this dependency chain.
- `grep -n '\bsorry\b'` across the three files returns only prose mentions that are now correctly
  historical, and zero `sorry` tactic occurrences.
- Scoped `lake build` of all three modules exits 0.

---

### Phase 5: Adjacent-file sweep and stale-line-reference sweep [NOT STARTED]

**Goal**: Close the two adjacent-file sites admitted by decision (b), and replace drifted
line-number citations with durable declaration-name anchors.

**Tasks**:
- [ ] `Metalogic/IntDecidability.lean`: rewrite "the payoff is low while `openBranch_countermodel`
      ... which `truthLemma` alone does not discharge — remains open." It does not remain open.
- [ ] `Metalogic/MinDecidability.lean`: the identical claim; rewrite identically.
- [ ] Confirm (do not edit) that `Tableau/Minimal/DecisionProcedure.lean`'s "closing what used to
      be this dependency chain's one remaining declaration-level sorry" is already correctly
      past-tense. Record that it was checked.
- [ ] Fix the confirmed drifted line references, preferring declaration names to line numbers in
      every rewrite: the frame-adequacy table's `IFimpAccess` "holds (`:6924`)" citation (`:6924`
      is now inside `intuitionisticTableau_sound`); the "`sorry` at `Completeness.lean:113` /
      `Minimal/Completeness.lean:110`" citation (both now point at ordinary proved code); the
      "`IPosPersistRaw`/`IWorldsPlanted`, `:6782`/`:3568`" citation (`IPosPersistRaw` is at
      `:7239`); and the `IntDecidability.lean` / `MinDecidability.lean` citations of
      "`Scheme.lean:234`" for `truthLemma` (it is at `:964`).
- [ ] Where a rewrite can name a declaration instead of a line, name the declaration. The four DP
      sites have already drifted twice in a 9833-line file under active development.
- [ ] Scoped `lake build` of the two `Metalogic` modules and of `Scheme.lean`.

**Timing**: 0.75 hours

**Depends on**: 4

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts two adjacent files needing edits (a third,
`Minimal/DecisionProcedure.lean`, needing none) and five confirmed drifted line references.
Confirm at implementation time by re-checking each cited line number against the current file
before rewriting it, and by scanning `Scheme.lean` docstrings for any further `:NNNN` citation
that no longer resolves to the declaration it names.

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` - stale open claim + `truthLemma`
  line citation (scoped in by decision (b))
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` - identical (scoped in by decision (b))
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - drifted internal line
  references

**Verification**:
- Neither `Metalogic` file asserts an open obligation in this chain.
- Every remaining `:NNNN` citation touched in this phase resolves to the declaration it names, or
  has been replaced by a declaration name.
- Scoped `lake build` of all three modules exits 0.

---

### Phase 6: Full verification gate [NOT STARTED]

**Goal**: Run the complete CI gate set and confirm zero new sorries, zero new axioms, and no
regression in the `#guard_msgs` assertions that pin the algorithm's behaviour.

**Tasks**:
- [ ] `lake build` (full project). Must exit 0 with zero errors.
- [ ] `lake test` — the `CslibTests/` probe files (notably `BetaSplitRefutation.lean`) carry
      `#guard_msgs` assertions pinning post-repair behaviour; all must still pass.
- [ ] `lake exe lint-style` — text linters over every edited file.
- [ ] `lake exe checkInitImports` — confirm the four new imports in `ProofSystemEquivalence.lean`
      did not disturb the `Cslib.Init` requirement.
- [ ] `lake lint` — environment linters; confirm the three new theorems raise no `docBlame` and no
      naming violations. Confirm the two pre-existing `linter.unusedDecidableInType` warnings on
      `ivalid_universe_invariant` / `mvalid_universe_invariant` are unchanged and were not
      "fixed" as a side effect.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — check import minimization on
      `ProofSystemEquivalence.lean`. `lake exe mk_all --module` is NOT needed (no new file).
- [ ] `lean_verify` on all four DP sites plus the three new TFAE theorems; confirm every one
      reports exactly `{propext, Classical.choice, Quot.sound}` with no `sorryAx`.
- [ ] `grep -rn '\bsorry\b'` across all seven in-scope files; confirm zero `sorry` tactic
      occurrences and that every prose mention reads as historical.
- [ ] Record the final gate results in the implementation summary.

**Timing**: 0.75 hours

**Depends on**: 1, 5

**Verification Tier**: full

**Scope Hypothesis**: This phase asserts seven in-scope files (four from the task's declared
`file_scope` plus the three added by decision (b)) and seven declarations to `lean_verify` (the
four DP sites plus the three new TFAE theorems). Confirm at implementation time by reconciling the
file list against the union of `files_touched` actually recorded across Phases 1-5; any file
edited but absent from the seven must be added to the gate's grep and verify sweep.

**Files to modify**:
- None (verification only)

**Verification**:
- All six gate commands exit 0.
- Seven `lean_verify` calls return the clean three-axiom set with no `sorryAx`.
- Zero `sorry` tactic occurrences repo-wide in the in-scope files.

---

## Testing & Validation

- [ ] `lake build` exits 0, zero errors.
- [ ] `lake test` passes; all `CslibTests/` `#guard_msgs` assertions unchanged and green.
- [ ] `lake exe lint-style` clean over every edited file.
- [ ] `lake exe checkInitImports` clean.
- [ ] `lake lint` raises no new warnings; the three new theorems have docstrings and conforming
      lowerCamelCase names.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unnecessary import in
      `ProofSystemEquivalence.lean`.
- [ ] `lean_verify` on `intuitionisticTableau_complete`, `minimalTableau_complete`, `truthLemma`,
      `openBranch_countermodel`, and the three new TFAE theorems: all
      `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.
- [ ] Zero new sorries, zero new axioms (the binding constraint).
- [ ] No counter-instance or refutation record deleted — spot-check that the `phiRef1` narrative
      and the `Expansion.lean` recorded-limitation block still exist, re-tensed.
- [ ] No theorem statement altered anywhere (the laundering prohibition stays un-engaged).

## Artifacts & Outputs

- `plans/01_tfae-fold-and-annotation-closeout.md` (this file)
- `summaries/01_tfae-fold-and-annotation-closeout-summary.md` (produced at implementation)
- Three new theorems in `Cslib/Logics/Propositional/ProofSystemEquivalence.lean`:
  `cplProofSystemsWithTableauTfae`, `iplProofSystemsWithTableauTfae`,
  `mplProofSystemsWithTableauTfae`
- Corrected annotations across `Scheme.lean`, `Tableau/Intuitionistic/Completeness.lean`,
  `Tableau/Minimal/Completeness.lean`, `Tableau/Intuitionistic/Expansion.lean`,
  `Metalogic/IntDecidability.lean`, `Metalogic/MinDecidability.lean`

## Rollback/Contingency

Every phase is independently revertible by file, and Phases 2-5 are documentation-only, so they
cannot break a proof.

- **Phase 1 fails to elaborate**: the probe file is the ground truth and compiled at exit 0; the
  most likely causes are a missing `open Cslib.Logic.Tableau`, the missing `[Hashable Atom]`
  variable, or an attempt to use `rw` on the universe-invariance lemmas. Re-read the probe and
  match it verbatim. If it still fails, revert `ProofSystemEquivalence.lean` to HEAD (`git
  checkout HEAD -- <path>` on an otherwise clean tree) and mark Phase 1 `[BLOCKED]` with the exact
  elaboration error — do not weaken any TFAE statement to make it pass.
- **A docstring edit breaks parsing**: the phase-scoped `lake build` catches it immediately; revert
  that single file and redo the edit with tighter `/-- -/` boundaries.
- **`lake test` regresses**: this would mean a Phase 2-5 edit crossed out of a comment region.
  Bisect by file using the per-phase commits, revert the offending file, and redo.
- **Do not** use `git reset --hard` or any destructive git operation on a dirty tree without first
  running `bash .claude/scripts/git-snapshot.sh 606`.
