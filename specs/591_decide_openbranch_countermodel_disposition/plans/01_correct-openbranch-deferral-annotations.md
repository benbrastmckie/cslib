# Implementation Plan: Correct the `openBranch_countermodel` deferral annotations

- **Task**: 591 - Decide the openBranch_countermodel upward-closure disposition (root of DP-3/DP-4/DP-5)
- **Status**: [IMPLEMENTING]
- **Effort**: 3.5 hours
- **Dependencies**: None remaining (see Research Integration — the stated prerequisite is already satisfied)
- **Research Inputs**: `specs/591_decide_openbranch_countermodel_disposition/reports/01_openbranch-countermodel-disposition.md`
- **Artifacts**: plans/01_correct-openbranch-deferral-annotations.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The research phase reached a machine-checked verdict: the `∃ edges` conjunct of
`openBranch_countermodel` is **not** refuted, and the `[UNVERIFIED]` inference that all four
in-source "PERMANENTLY DEFERRED / unprovable as stated / refuted" annotations rest on is
machine-refuted. This plan is therefore a pure **annotation-correction** task across three Lean
files: replace the false "refuted / permanently deferred / terminal" framing with the corrected
framing "open, augmented-frame route known-bad, admissible space characterised", without
touching a single line of code.

The four `sorry`s stay. Zero new sorries, zero new axioms, zero signature changes, zero tactic
changes. Definition of done: all deferral-language hunks in the three in-scope files carry the
corrected framing, no in-source claim overstates what was established, and the full CI gate
(`scripts/pre-pr-check.sh`) passes with the sorry and axiom ratchets unchanged.

### Research Integration

Load-bearing findings from the report, in the order they matter for the new annotation text:

1. **§2, the decisive structural argument (needs no computation).** `IValid φ` quantifies over
   *every* preorder and *every* upward-closed valuation, so any refutation of
   `openBranch_countermodel` must exhibit an **IPC-valid** `φ` on which the algorithm returns
   `.openBranch`. `phiRef1 = ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr` is not even
   *classically* valid, so it was never a candidate refutation of this lemma. This argument is
   self-contained and is the content the corrected annotations should lead with.
2. **§3, the admissible-edge-space characterisation.** The admissible `edges` are exactly the
   subsets of the atom-set-inclusion preorder `⊑`, and every such subset is automatically
   upward-closed. Consequence: **conjunct 1 needs no fact about the tableau algorithm at all** —
   the whole persistence / `genCopies` / augmented-edge invariant apparatus DP-3/DP-4 are
   annotated as blocked on is simply not required for it.
3. **§4.1–§4.2, the witness.** On the branch the real `intuitionisticTableau` returns for
   `phiRef1`, `edges = [(1, 0)]` satisfies **both** conjuncts. Exhaustive enumeration over the
   complete admissible space finds 40 witnesses for `phiRef1` under `intScheme`, and witnesses
   for `phiRef2`/`phiRef3`/`exMiddle`/`dblNeg`/`peirce`/`deMorgan`/`dummett`.
4. **§4.3, DP-4's independence claim is refuted.** Under `minScheme`, `[(1, 0)]` discharges
   **both** upward-closure obligations (valuation and `⊥`) and still falsifies `phiRef1` at
   world 0.
5. **§4.4, the honesty bound.** The maximal inclusion frame `⊑` is **not** a uniform witness —
   it fails at exactly the `phiRef1`/`phiRef3` family. The general `∀ φ` statement remains
   **unproved**, and per §2 proving it is equivalent to proving the tableau procedure complete.
6. **§4.5 / §6, what survives.** The `BetaSplitRefutation.lean` counterexample remains a real
   refutation of *augmented-frame positive-formula persistence*. What does not follow is DP-5's
   conclusion, because `truthLemma`'s frame is a parameter and the refuted invariant is only
   needed when that parameter is the augmented frame.

Two premises in the original task description are factually wrong and must not be carried into
the new annotations: `CslibTests/BetaSplitRefutation.lean` is **present** and CI-protected (the
stated prerequisite is satisfied — no dependency blocks this work), and DP-4 is **not** refuted
independently of DP-3.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `specs/ROADMAP.md` consulted for this task (`roadmap_path` not supplied in the delegation
context, `roadmap_flag` not set).

## Goals & Non-Goals

**Goals**:
- Replace every "PERMANENTLY DEFERRED / unprovable as stated / refuted / terminal deferral /
  no follow-up is scheduled" claim in the three in-scope files with the corrected framing.
- Lift the `openBranch_countermodel` docstring's "**No change to this statement is authorized**"
  freeze, which was conditioned on exactly the machine-checked confirmation that now exists.
- Record, in-source, the §2 structural argument and the §3 admissible-space characterisation, so
  a future reader can see *why* the deferrals were wrong without re-deriving anything.
- Keep the honesty bound visible: the general `∀ φ` statement is open, and the obvious canonical
  frame is not a uniform witness.
- Leave the repository's sorry and axiom ratchets bit-for-bit unchanged.

**Non-Goals**:
- Discharging any of the four `sorry`s. This is not a sorry-discharge task.
- Proving `openBranch_countermodel` in general, or constructing `inclEdges` / a uniform frame.
- Any change to `CslibTests/`, `Expansion.lean`, `Rules.lean`, `Kripke.lean`, `Soundness.lean`,
  or any file outside the three-file `file_scope`.
- Promoting the research scratch probes into `CslibTests/` (see Artifacts & Outputs — recorded
  as a named follow-up, deliberately not done here).
- Editing the task tracker's restatement task. This plan *reports* that its premise is now
  false; re-scoping it is a separate tracker action.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A rewritten block comment breaks a `/-` … `-/` delimiter, silently turning prose into code | H | M | `check-sorry-suppressions.sh` strips block comments *before* counting `\bsorry\b`; a broken delimiter therefore changes the per-file sorry count and trips the ratchet. Run it after every phase, not just at the end. |
| New annotation overclaims — reads as if the lemma is now proved | H | M | Phase 1 fixes canonical wording that names the `∀ φ` statement as open and the maximal frame as a non-witness; every editing phase re-checks against that text. Verification includes an explicit "no overclaim" read-through. |
| Rewrapped prose exceeds the repo's hard 100-column limit | M | H | Measured baseline: all three files are at exactly 0 lines over 100. Every phase ends with an `awk length>100` check on its own files. |
| An edit accidentally deletes a `sorry` token or touches a tactic line | H | L | Per-phase `git diff` review restricted to comment/docstring regions; sorry-count ratchet catches deletion; `lake build` catches a broken proof. |
| Scope is larger than the delegation's "four sites" — the module-level `## Notes on sorry` sections repeat the same false claims | M | Confirmed | Already enumerated below (10 hunks, not 4). Leaving the module notes uncorrected would make each file self-contradictory. All extra hunks lie inside the declared `file_scope`. |
| Full `lake build` on a 7,993-line file is slow, tempting a skipped final gate | M | M | Phase 6 is a standalone phase with its own budget; per-phase tiers are deliberately `local` so the cost is paid once at the end, not six times. |
| The corrected annotations cite non-CI-protected scratch probes | M | M | Content rule C7 below: annotations lead with the §2 structural argument (self-contained, needs no artifact) and label computed evidence as computed. No scratch path and no task number is cited in source. |

## Scope: the actual hunk inventory

The delegation names four sites. A grep of the three in-scope files for the deferral vocabulary
finds **ten** hunks. The four named sites are a subset; the remainder repeat the same false
claims at module level and in one stale cross-reference. All ten lie inside `file_scope`.

| # | File | Approx. lines | What it currently claims | Phase |
|---|------|--------------|--------------------------|-------|
| H1 | `Intuitionistic/Scheme.lean` | 7844–7858 | `openBranch_countermodel` docstring: "DISPOSITION UNDECIDED … gated on an open decision point"; "No change to this statement is authorized" | 2 |
| H2 | `Intuitionistic/Scheme.lean` | 7928–7939 | proof-site comment: same "DISPOSITION UNDECIDED", `[UNVERIFIED]` inference | 2 |
| H3 | `Intuitionistic/Scheme.lean` | 744–760 | DP-5: "PERMANENTLY DEFERRED, unprovable as stated … REFUTED by a machine-verified counterexample"; "a refutation of the STATEMENT" | 3 |
| H4 | `Intuitionistic/Scheme.lean` | 583–585 | stale cross-reference: "nor DP-3/DP-4/DP-5: those depend on the AUGMENTED-frame positive-formula persistence invariant, which is … separately REFUTED" | 3 |
| H5 | `Intuitionistic/Completeness.lean` | 46–57 | module `## Notes on sorry`: "DP-3 is PERMANENTLY DEFERRED — unprovable as stated"; "not scheduled for any follow-up" | 4 |
| H6 | `Intuitionistic/Completeness.lean` | 139–149 | `intuitionisticTableau_complete` docstring: same, plus "terminal deferral" | 4 |
| H7 | `Intuitionistic/Completeness.lean` | 154–160 | in-proof DP-3 comment: same, plus the `exact h …` prohibition | 4 |
| H8 | `Minimal/Completeness.lean` | 50–60 | module `## Notes on sorry`: "DP-4 is PERMANENTLY DEFERRED … refuted **independently** of DP-3" | 5 |
| H9 | `Minimal/Completeness.lean` | 136–143 | `minimalTableau_complete` docstring: same, plus "terminal deferral, not an unfinished step" | 5 |
| H10 | `Minimal/Completeness.lean` | 148–154 | in-proof DP-4 comment: same | 5 |

Line numbers are indicative anchors only; locate hunks by their quoted phrases, since earlier
phases shift later line numbers within the same file.

## Content rules (binding on every editing phase)

These are the constraints the corrected annotations must satisfy. An editing phase is not green
until its diff satisfies all of them.

- **C1 — the `sorry`s stay.** No `sorry` token is deleted, moved, or discharged. No `exact`,
  `apply`, or any other tactic is added.
- **C2 — comments and docstrings only.** Every changed line must lie inside a `/-- … -/`,
  `/-! … -/`, `/- … -/`, or `--` region. No signature, statement, `theorem`/`lemma` line, import,
  or tactic block is touched.
- **C3 — do not discharge DP-3 by laundering.** The existing prohibition on
  `exact h Nat (intExtractValuation _b) _huc 0` is **kept**, and kept for the corrected reason:
  it type-checks but only launders a still-undischarged conjunct through the file. The reason
  changes from "the premise is refuted" to "the premise is open"; the prohibition itself does not.
- **C4 — no overclaim.** The general `∀ φ` statement remains **unproved**. The maximal inclusion
  frame `⊑` is **not** a uniform witness (it fails at `phiRef1`/`phiRef3`). Per §2, proving the
  lemma in general is equivalent to proving the tableau procedure complete — it is not a small
  residual. Every corrected annotation must say so.
- **C5 — preserve what genuinely survives.** The `BetaSplitRefutation.lean` counterexample is
  still a real refutation of *augmented-frame positive-formula persistence*, and the
  `intFImpReuseWitnessAnc?` frame-construction defect is still real. Only the *conclusion drawn
  from them* is corrected. Do not delete or weaken the counterexample's description.
- **C6 — no task-number citations.** Per `.claude/rules/no-task-references-in-deliverables.md`,
  the new annotations must not contain "task N", "tasks N-M", or a reference to the restatement
  task by number. Cite durable anchors: declaration names, file names, `phiRef1`, the witness
  edge set.
- **C7 — evidence honesty.** Lead with the §2 structural argument, which is self-contained and
  needs no external artifact. The `[(1, 0)]` witness and the enumeration counts are supporting
  evidence and must be labelled as computed against the real `intuitionisticTableau` /
  `minimalTableau` rather than presented as CI-protected facts (the probes are not in
  `CslibTests/`). Do not repeat the original sin of resting an annotation on an unlabelled,
  unverifiable inference.
- **C8 — 100-column hard limit.** Measured baseline is 0 lines over 100 in all three files.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4, 5 | 2 |
| 4 | 6 | 3, 4, 5 |

Phases within the same wave can execute in parallel. Wave 3's three phases touch disjoint
regions (Phase 3 edits two `Scheme.lean` hunks far above Phase 2's; Phases 4 and 5 edit separate
files), so they are territory-safe in parallel. If run serially, any order within the wave works.

---

### Phase 1: Baseline capture and canonical corrected wording [COMPLETED]

**Goal**: Freeze the pre-edit mechanical baseline, and author one canonical corrected-annotation
text block so the ten hunks do not drift into ten different framings.

**Tasks**:
- [ ] Record the pre-edit baseline into the task scratch directory: per-file output of
      `bash scripts/check-sorry-suppressions.sh` for the three in-scope files, the current
      `\bsorry\b` code-position counts, and `awk 'length($0)>100'` counts (expected: 0, 0, 0).
- [ ] Confirm the hunk inventory above by grepping the three files for
      `PERMANENTLY DEFERRED|unprovable as stated|REFUTED|refuted|DISPOSITION UNDECIDED|terminal deferral|UNVERIFIED|no follow-up`.
      Record the actual hunk count found; if it differs from 10, record the delta and treat the
      found set as authoritative.
- [ ] Author a canonical corrected-framing paragraph covering: the §2 structural argument; the
      `[(1, 0)]` witness for `phiRef1`; the §3 `𝒫(⊑)` admissible-space characterisation and its
      consequence that conjunct 1 needs no algorithm invariant; the §4.4 honesty bound; and what
      genuinely survives (C5). Save it to the task scratch directory as the shared source text.
- [ ] Author a one-sentence "disposition line" that replaces the header of each hunk, e.g. the
      shape "**open — augmented-frame route known-bad, admissible edge space characterised**",
      so all ten hunks open consistently.

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This plan asserts **10** deferral-language hunks across the three in-scope
files, and a clean baseline of 0 over-100-column lines and unchanged sorry/axiom ratchets.
Confirm at implementation time by running the grep above and the two census scripts; if the hunk
count differs, update the inventory table in this plan before proceeding to Phase 2 rather than
silently editing a different set.

**Files to modify**:
- `specs/591_decide_openbranch_countermodel_disposition/scratch/` — new baseline record and
  canonical wording file (task artifacts, not repository deliverables)

**Verification**:
- Baseline file exists, is non-empty, and records three per-file sorry counts plus three
  over-100 counts.
- Canonical wording text explicitly contains a sentence asserting the `∀ φ` statement is
  unproved (C4) and a sentence preserving the augmented-frame counterexample (C5).

---

### Phase 2: Correct `openBranch_countermodel` in `Scheme.lean` (H1, H2) [COMPLETED]

**Goal**: Replace the "DISPOSITION UNDECIDED / no change authorized" framing at the root site —
the docstring and the proof-site comment of `openBranch_countermodel` — with the corrected
framing. This is the root hunk the other eight cross-reference.

**Tasks**:
- [ ] Rewrite H1 (the `**DISPOSITION UNDECIDED …**` paragraph in the `openBranch_countermodel`
      docstring): state the disposition as **decided — not refuted**; record the §2 structural
      argument; record the `[(1, 0)]` witness; record the §3 `𝒫(⊑)` characterisation and that
      conjunct 1 needs no algorithm invariant; state that the augmented frame is a bad *witness
      choice*, not evidence against the statement.
- [ ] Remove the "**No change to this statement is authorized until one of those exists**" freeze
      and the "do not revert, weaken, delete, or restate" clause — the machine-checked
      confirmation those were conditioned on now exists.
- [ ] Add the C4 honesty bound: the general `∀ φ` statement is open, the maximal inclusion frame
      is not a uniform witness, and proving it in general is equivalent to procedure completeness.
- [ ] Rewrite H2 (the proof-site comment above the `sorry`) to match, keeping it shorter than the
      docstring and pointing at the docstring for the full disposition. Keep the sentence
      explaining that `edges` here is the `augSets` witness.
- [ ] Confirm the `sorry` on the line after H2 is untouched.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Asserts exactly 2 hunks in `Scheme.lean` for this phase (docstring +
proof-site comment of `openBranch_countermodel`). Confirm by grepping `Scheme.lean` for
`DISPOSITION UNDECIDED` — expect exactly the 2 regions before the edit and 0 after.

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — H1 docstring paragraph and
  H2 proof-site comment block, comments only

**Verification**:
- `git diff` shows changes confined to comment/docstring regions (C2); no `sorry`, tactic, or
  signature line altered (C1).
- `grep -c 'DISPOSITION UNDECIDED' Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
  returns 0.
- `bash scripts/check-sorry-suppressions.sh` — `Scheme.lean`'s sorry count is unchanged from the
  Phase 1 baseline (a changed count means a broken comment delimiter).
- `awk 'length($0)>100' Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` is empty.
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` succeeds with no new
  errors or warnings beyond the pre-existing `sorry` warnings.
- Read-through: the new text contains no claim that the lemma is proved (C4).

---

### Phase 3: Correct DP-5 and the stale cross-reference in `Scheme.lean` (H3, H4) [COMPLETED]

**Goal**: Correct DP-5's conclusion — the augmented-frame refutation is real, but "a refutation
of the STATEMENT" does not follow — and fix the stale claim at H4 that DP-3/DP-4/DP-5 all depend
on the refuted invariant.

**Tasks**:
- [ ] Rewrite H3's `DP-5 -- PERMANENTLY DEFERRED, unprovable as stated` block: keep the
      counterexample description verbatim in substance (C5 — it *is* a refutation of
      augmented-edge positive-formula persistence), but correct the conclusion. `truthLemma`'s
      frame is a parameter; the refuted invariant is needed only when that parameter is the
      augmented frame. Re-annotate as: the augmented-frame instantiation is refuted; the lemma
      over a sub-`⊑` frame is **open**.
- [ ] Replace "This is a refutation of the STATEMENT, not a proof-route failure" with the
      corrected reading, and drop "not 'deferred to future work'" / terminal-deferral language.
- [ ] Rewrite H4's clause "nor DP-3/DP-4/DP-5: those depend on the AUGMENTED-frame
      positive-formula persistence invariant, which is separately REFUTED": per §3, DP-3/DP-4's
      conjunct needs **no** algorithm invariant at all, so the dependency claim is wrong for
      them. Narrow the claim to DP-5's augmented-frame instantiation and mark the rest corrected.
- [ ] Preserve H4's surrounding historical-record framing ("Retained here, uncorrected in place,
      as a historical record") for the *fuel-sufficiency* material, which this task does not
      touch — correct only the DP-3/DP-4/DP-5 dependency sentence.

**Timing**: 0.5 hours

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Asserts exactly 2 hunks (the DP-5 in-proof block and the one stale
cross-reference sentence). Confirm by grepping `Scheme.lean` for `PERMANENTLY DEFERRED` — expect
1 region before, 0 after — and for `DP-3/DP-4/DP-5` — expect 1 region, edited in place.

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — H3 in-proof comment block and
  H4 cross-reference sentence, comments only

**Verification**:
- `grep -c 'PERMANENTLY DEFERRED' Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
  returns 0.
- The `intro _` / `sorry` pair at the end of H3's block is byte-identical to before (C1).
- `git diff` confined to comment regions; `awk 'length($0)>100'` empty.
- `bash scripts/check-sorry-suppressions.sh` — `Scheme.lean` count matches the Phase 1 baseline.
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` succeeds.
- Read-through: H3 still describes the counterexample and the `intFImpReuseWitnessAnc?` defect
  (C5), and no longer calls it a refutation of the statement.

---

### Phase 4: Correct DP-3 in `Intuitionistic/Completeness.lean` (H5, H6, H7) [IN PROGRESS]

**Goal**: Re-annotate DP-3 as an **open** obligation blocked on a uniform frame construction,
across all three hunks in the file, while keeping the `exact h …` prohibition.

**Tasks**:
- [ ] Rewrite H5 (module-level `## Notes on sorry`): replace "DP-3 is PERMANENTLY DEFERRED —
      unprovable as stated" and "not scheduled for any follow-up" with the corrected framing;
      state that the premise DP-3 consumes is **open**, not refuted, and point at
      `Scheme.lean`'s `openBranch_countermodel` docstring for the full disposition.
- [ ] Rewrite H6 (`intuitionisticTableau_complete` docstring): same correction. Keep the
      statement-shape-fix paragraph above it unchanged — it describes a separate, still-valid
      repair. Keep the sentence explaining that `IValid φ` instantiates directly under the new
      shape.
- [ ] Rewrite H7 (in-proof comment above the `sorry`): keep the `exact h Nat
      (intExtractValuation _b) _huc 0` prohibition (C3) with the corrected reason — it launders
      an **undischarged** conjunct, not a refuted one. Drop "Not a route failure; no follow-up is
      scheduled."
- [ ] Add, in H5 or H6, the honesty bound (C4): the remaining obligation is a uniform
      construction of `edges` from `b` plus a truth lemma over that frame, which per the
      structural argument is equivalent to procedure completeness — genuine open work, not a
      small residual.
- [ ] Confirm the `sorry` on the final line of the proof is untouched.

**Timing**: 0.5 hours

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Asserts exactly 3 hunks in this 165-line file. Confirm by grepping for
`PERMANENTLY DEFERRED` (expect 3 regions before, 0 after) and `DISPOSITION UNDECIDED` (expect 2
mentions before, 0 after).

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` — H5 module docstring
  section, H6 theorem docstring, H7 in-proof comment, comments only

**Verification**:
- `grep -cE 'PERMANENTLY DEFERRED|unprovable as stated|terminal deferral|no follow-up'` returns 0
  for this file.
- `grep -c 'exact h Nat (intExtractValuation _b) _huc 0'` still returns ≥ 1 — the prohibition is
  preserved (C3).
- `git diff` confined to comment regions; `awk 'length($0)>100'` empty.
- `bash scripts/check-sorry-suppressions.sh` — this file's sorry count matches the Phase 1
  baseline.
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness` succeeds.

---

### Phase 5: Correct DP-4 in `Minimal/Completeness.lean` (H8, H9, H10) [NOT STARTED]

**Goal**: Re-annotate DP-4 as open, explicitly retract the "refuted **independently** of DP-3"
claim, and keep the genuinely-separate `minBranchBotForces b` upward-closure obligation as a
named residual.

**Tasks**:
- [ ] Rewrite H8 (module-level `## Notes on sorry`): retract "DP-4 is PERMANENTLY DEFERRED —
      unprovable as stated … refuted **independently** of DP-3". Record §4.3: under `minScheme`,
      `edges = [(1, 0)]` discharges **both** upward-closure obligations (valuation and `⊥`) and
      still falsifies `phiRef1` at world 0, so the independent-refutation claim is refuted.
- [ ] Rewrite H9 (`minimalTableau_complete` docstring): same correction. **Keep** the accurate
      part — `MValid φ` needs two upward-closure premises and the supplied `_huc` discharges only
      the first — and promote obligation (2), `minBranchBotForces b`'s own upward closure, to a
      **named residual**: it holds at the `[(1, 0)]` witness but is not proved in general.
- [ ] Rewrite H10 (in-proof comment above the `sorry`): drop "PERMANENTLY DEFERRED, unprovable as
      stated, refuted INDEPENDENTLY of DP-3" and "no follow-up is scheduled"; keep the accurate
      description of what the `exact h Nat … hbotuc 0` discharge would require, restated as
      "would type-check once both upward-closure obligations are discharged; both are open".
- [ ] Preserve the `reportMin phiRef1 realFuel` / `minBranchesAgree = true` evidence description
      (C5) — it accurately reports what the counterexample computes; only the conclusion changes.
- [ ] Confirm the `sorry` on the final line of the proof is untouched.

**Timing**: 0.5 hours

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Asserts exactly 3 hunks in this 159-line file. Confirm by grepping for
`PERMANENTLY DEFERRED` (expect 3 regions before, 0 after) and `independently|INDEPENDENTLY`
(expect 3 mentions before, 0 asserting independent refutation after).

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` — H8 module docstring section,
  H9 theorem docstring, H10 in-proof comment, comments only

**Verification**:
- `grep -cE 'PERMANENTLY DEFERRED|unprovable as stated|terminal deferral|no follow-up'` returns 0
  for this file.
- No surviving sentence asserts DP-4 is refuted independently of DP-3.
- The `minBranchBotForces b` upward-closure obligation is still named in the docstring.
- `git diff` confined to comment regions; `awk 'length($0)>100'` empty.
- `bash scripts/check-sorry-suppressions.sh` — this file's sorry count matches the Phase 1
  baseline.
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.Completeness` succeeds.

---

### Phase 6: Full gate, cross-file consistency, and residual reporting [NOT STARTED]

**Goal**: Run the complete repository gate, confirm the ten hunks now tell one consistent story
across the three files, and record the residuals and tracker corrections the research phase
surfaced.

**Tasks**:
- [ ] Run `bash scripts/pre-pr-check.sh` and confirm all ten steps pass — in particular step 5
      (`lake build --wfail --iofail` full-repo warning gate), step 8 (sorry-suppression ratchet)
      and step 9 (axiom-census ratchet).
- [ ] Confirm the sorry ratchet is **unchanged, not merely non-regressed**: the three in-scope
      files' counts equal the Phase 1 baseline exactly, in both the marker and sorry columns.
- [ ] Confirm `bash scripts/check-axiom-census.sh` reports no new axiom taint.
- [ ] Cross-file consistency read-through: `Scheme.lean`'s corrected `openBranch_countermodel`
      docstring is the single authority; H5–H10 point at it and none of them contradicts it or
      re-asserts a refutation.
- [ ] Repo-wide residual grep: confirm no surviving occurrence of `PERMANENTLY DEFERRED` or
      `DISPOSITION UNDECIDED` in the three in-scope files, and check whether the phrase leaked
      into any other file (report only — out-of-scope files are not edited).
- [ ] Verify `.claude/scripts/check-task-references.sh`-style compliance for the edited files:
      no "task N" citations introduced (C6).
- [ ] Write the execution summary at
      `specs/591_decide_openbranch_countermodel_disposition/summaries/01_correct-openbranch-deferral-annotations-summary.md`,
      recording: hunks corrected, sorry/axiom deltas (expected 0/0), and the residuals below.
- [ ] Record the two tracker corrections in the summary (report only, no tracker edits here):
      (1) the task description's prerequisite premise is false — `CslibTests/BetaSplitRefutation.lean`
      is present and CI-protected; (2) the restatement task
      (`restate_propositional_tableau_completeness_theorems`) rests on the now-disproved premise
      that the conjunct is refuted, and should be re-scoped or blocked rather than executed as
      written.
- [ ] Record the follow-up recommendation: promote the research scratch probes (`WitnessProbe`,
      `WitnessSearch2`, `WitnessSearch3`, `MinProbe`) into `CslibTests/`, mirroring
      `BetaSplitRefutation.lean`'s promotion, so the new annotations' computed evidence becomes
      CI-protected. Deliberately not done here — it is outside `file_scope`.

**Timing**: 0.75 hours

**Depends on**: 3, 4, 5

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: Asserts that the full gate passes with **zero** delta in both the sorry
ratchet and the axiom census. Confirm by diffing the Phase 1 baseline record against the
post-edit run of the same two scripts; any non-zero delta is a hard failure of this task's
central constraint, not a tolerable variance.

**Files to modify**:
- `specs/591_decide_openbranch_countermodel_disposition/summaries/01_correct-openbranch-deferral-annotations-summary.md`
  — new execution summary

**Verification**:
- `bash scripts/pre-pr-check.sh` exits 0.
- Sorry and axiom censuses are byte-identical to the Phase 1 baseline for the three files.
- All four `sorry`s are still present: `Scheme.lean` ×2, `Intuitionistic/Completeness.lean` ×1,
  `Minimal/Completeness.lean` ×1.
- Summary file exists and records the tracker corrections and the follow-up recommendation.

---

## Testing & Validation

- [ ] `bash scripts/pre-pr-check.sh` passes all ten steps.
- [ ] `bash scripts/check-sorry-suppressions.sh` — zero delta against the Phase 1 baseline for
      all three in-scope files (both marker and sorry columns).
- [ ] `bash scripts/check-axiom-census.sh` — zero new axiom taint.
- [ ] `lake build --wfail --iofail` — no new warnings beyond the four pre-existing `sorry`
      warnings.
- [ ] All four `sorry`s present and in their original positions.
- [ ] `awk 'length($0)>100'` empty for all three files.
- [ ] `git diff` for the three Lean files touches only comment and docstring regions.
- [ ] No surviving `PERMANENTLY DEFERRED`, `unprovable as stated`, `DISPOSITION UNDECIDED`,
      `terminal deferral`, or `no follow-up is scheduled` in the three in-scope files.
- [ ] The `exact h Nat (intExtractValuation _b) _huc 0` prohibition survives in
      `Intuitionistic/Completeness.lean`.
- [ ] Manual read-through confirms no annotation claims the lemma is proved, and each records
      that the maximal inclusion frame is not a uniform witness.

## Artifacts & Outputs

- Corrected annotations in `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
  (H1–H4), `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` (H5–H7), and
  `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (H8–H10).
- Baseline record and canonical wording text in the task `scratch/` directory (Phase 1).
- `specs/591_decide_openbranch_countermodel_disposition/summaries/01_correct-openbranch-deferral-annotations-summary.md`.
- **Named residuals reported, not resolved**: (a) the general `∀ φ` `openBranch_countermodel`
  statement remains open and is equivalent to procedure completeness; (b)
  `minBranchBotForces b`'s upward closure is a separate, unproved obligation; (c) the
  `intFImpReuseWitnessAnc?` frame-construction defect is real and unfixed; (d) the research
  probes are not CI-protected and should be promoted to `CslibTests/` by a follow-up task;
  (e) the restatement task's premise is now false and it should be re-scoped or blocked.

## Rollback/Contingency

Every change is a comment or docstring edit, so rollback is total and risk-free:
`git checkout -- <file>` restores any single file to its pre-edit state with no proof or build
consequence (note the repo's destructive-git guard — snapshot first via
`bash .claude/scripts/git-snapshot.sh 591` if the tree is dirty). Phases commit independently
per the commit-per-green-substep mandate, so a bad phase can be reverted without losing earlier
ones.

Contingency if Phase 1's hunk-count confirmation finds a materially different inventory (for
example, deferral language in a fourth file): correct the inventory table in this plan, keep the
edits inside `file_scope`, and record any out-of-scope occurrences in the Phase 6 summary as a
follow-up rather than expanding scope mid-task.

Contingency if the sorry or axiom ratchet moves at any phase: stop immediately and treat it as a
broken comment delimiter (the ratchet strips block comments before counting, so a count change on
a comment-only edit is diagnostic of exactly that). Revert the phase and re-apply in smaller
hunks.
