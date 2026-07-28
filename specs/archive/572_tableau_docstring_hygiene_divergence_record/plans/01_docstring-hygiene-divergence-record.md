# Implementation Plan: Task #572

- **Task**: 572 - tableau_docstring_hygiene_divergence_record
- **Status**: [COMPLETED]
- **Effort**: 5 hours
- **Dependencies**: None (this task must land BEFORE any other work in the Intuitionistic tableau repair programme)
- **Research Inputs**: `specs/317_propositional_tableau_completeness/reports/14_blocker-analysis.md`
- **Artifacts**: plans/01_docstring-hygiene-divergence-record.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Three docstrings in `Cslib/Logics/Propositional/Tableau/Intuitionistic/` assert claims that are
contradicted by the current code, and two BibKeys cited in prose are absent from
`references.bib`. This plan corrects the stale claims, records two Lean-verified refutations
(the expansion-loop divergence witness and the fuel-0 saturation counter-instance) as permanent
in-source notes, and lands the two missing bibliography entries. Every phase is a
comment/docstring/BibTeX edit only: no Lean definition, theorem statement, tactic, or `sorry`
may change.

### Research Integration

The delegation context supplies `reports/14_blocker-analysis.md` as the grounding artifact for
the divergence witness (branch/world counts at increasing fuel) and the fuel-0 counter-instance.
The implementer should read that report before Phase 1 and Phase 2 to transcribe the numeric
data faithfully. Line numbers quoted in the task description were re-verified against the
working tree during planning; the verified anchors are recorded per phase below and are current
as of this plan's authoring.

### Verified Anchors (re-checked against the working tree)

| Item | Location (verified) | Current text (excerpt) |
|------|--------------------|------------------------|
| 1 | `Scheme.lean:3020-3041` | `/-! ### GAP 2 investigation ... determinacy remains BLOCKED` |
| 2a | `Scheme.lean:527` | `` `sat_timp` is NOT added as an `IBranchSaturation` field `` |
| 2b | `Scheme.lean:595-597` | `` `sat_timp` is therefore deliberately NOT added as an `IBranchSaturation` field `` (**second, undocumented instance of the same false claim**) |
| 2-truth | `Scheme.lean:105-108` | `sat_timp` **is** a live `IBranchSaturation` field |
| 3 | `Expansion.lean:124-125` | `termination is unaffected since the number of distinct (implication, world) copies is bounded by intUniverse φ0` |
| 4a | `Scheme.lean:1813` | `(hnw : nextWorld ≤ φ0.complexity + 1) :` |
| 4b | `Scheme.lean:1570-1577` | `intUniverse` docstring + `List.range (φ.complexity + 2)` |
| 5 | `Scheme.lean:2557-2558, 2578` | fuel-0 base case `sorry` in `intExpandBranches_openBranch_sat` |
| 6a | `Expansion.lean:210` | `` [`GargGenoveseNegri2012`; BibKey added to `references.bib` in Phase 6] `` — `grep -c` on `references.bib` returns **0** |
| 6b | `Expansion.lean:264` | `(Dyckhoff 1992 / Negri–von Plato 2001 §5.5)` — `Dyckhoff` count **0**; `NegriVonPlato2001` **already present** at `references.bib:913` |

**Two findings beyond the task description**, both grounded in the files and in scope
(documentation-only):

1. **Item 2 has a second instance.** The false "not added as a field" claim appears at
   `Scheme.lean:595-597` as well as at `:527`. Correcting only `:527` would leave the identical
   refuted claim live at the exact site (`truthLemma`'s T-imp case) most likely to be read by a
   future dispatch. Phase 4 corrects both.
2. **`Scheme.lean:492-500` already says Gap 2 is RESOLVED.** The file therefore currently
   contradicts itself: the STOP-gate header says resolved, the trailing block at `:3020` says
   blocked. The remaining obstruction at the T-imp `sorry` is *Gap 1* (each accessible world
   carrying its own `T(φ→ψ)` copy), not Gap 2 determinacy. Phase 4's rewrite must make the file
   internally consistent, not merely delete the trailing block.

### Baseline Invariants (must be identical after every phase)

```
bare `sorry` tactic occurrences (grep -cE '^[[:space:]]*sorry[[:space:]]*$'):
  Scheme.lean        2   (lines 599, 2578)
  Completeness.lean  1
  Expansion.lean     0
  Rules.lean         0
  Soundness.lean     0
  DecisionProcedure.lean 0
max line length in Scheme.lean / Expansion.lean: <= 100 (currently 0 lines exceed)
```

### Prior Plan Reference

No prior plan for this task. The twelve plan versions under
`specs/317_propositional_tableau_completeness/plans/` are the *cause* of this task, not a
template: their recurring failure mode was treating `intExpandBranches_world_bound` / `hnw` /
`hUniv` as hard-but-provable. This plan's function is to make that misreading impossible for
future readers of the source.

### Roadmap Alignment

No `roadmap_path` supplied in the delegation context; no ROADMAP.md consulted.

## Goals & Non-Goals

**Goals**:
- Remove or rewrite every docstring claim in the Intuitionistic tableau directory that is
  contradicted by the current code (items 1, 2, 3).
- Record the divergence witness and the fuel-0 counter-instance as permanent, discoverable
  in-source notes with durable heading anchors, so no future dispatch re-attempts a refuted
  goal (items 4, 5).
- Land the two missing BibKeys and repair the two citation sites (item 6).
- Leave `lake build` green and the sorry inventory bit-identical.

**Non-Goals**:
- Closing, moving, restating, or adding any `sorry`. The fuel-0 goal's restatement is
  explicitly deferred.
- Any change to a Lean definition, theorem statement, hypothesis, or tactic — including
  removing the now-known-false `hnw` hypothesis from `intApplyRuleFull_outputs_subset`.
- A repository-wide sweep of task-number citations from `.lean` files. Roughly 40 such
  citations exist across `Scheme.lean`, `Completeness.lean`, and `Expansion.lean`. This plan
  removes them only from prose it is already rewriting; the remainder stays for a separate task.
- Claiming Gap 1 (persistence fuel-sufficiency) is refuted. The divergence witness refutes the
  *world bound*; the plan cross-references it from the Gap 1 discussion but does not assert
  more than the witness supports.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| An edit accidentally lands inside code rather than a comment | H | L | Phase 6 audits `git diff -U0` and asserts every changed line is inside `--`, `/--`, `/-!`, or `references.bib` |
| Rewritten docstring exceeds the 100-char style limit | M | M | Per-phase check: `awk 'length>100' <file>`; baseline is zero violations |
| Deleting the `:3020` block detaches a doc from a declaration | M | L | The block is a standalone `/-! ... -/` module note between `tableau_complete` and `end Cslib.Logic.PL`; verify with `lake build` |
| New prose cites task numbers, violating the deliverables rule | M | M | Every phase states the durable anchor to use instead; Phase 6 greps the diff for `task [0-9]`, `phase [0-9]`, `report [0-9]`, `plan [0-9]` |
| Embedding a live `#eval` to "prove" the divergence witness trips the debug-artifact check | M | M | The witness is recorded as prose + a table. **No `#eval`, `#check`, or `dbg_trace` may enter any `Cslib/` file.** Re-verification, if done, happens in a scratch file outside the repo |
| BibTeX field values (authors, pages, DOI) are wrong | M | M | Phase 5 verifies against the Literature index / Zotero first; falls back to the fields given in this plan and flags any that could not be confirmed |
| Duplicate/conflicting `GargGenoveseNegri2012` entry if task 456 lands first | M | M | Phase 5 re-greps immediately before writing; if present, verify equivalence instead of adding |
| Rewriting the Gap 1/Gap 2 narrative introduces a *new* false claim | H | M | Phase 4 is constrained to state only what the code shows: field exists at `:105-108`, reflexive at the copy's own label, `Rules.lean` `.pos, .imp` arm fires reflexively |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 5 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 6 | 2, 3, 4, 5 |

Phases within the same wave can execute in parallel. Territory is file-disjoint within each
wave: Phase 2/3/4 own `Scheme.lean`, Phases 1 and 5 own `Expansion.lean` + `references.bib`.
Phase 5 depends on Phase 1 only for `Expansion.lean` serialization, not for content.

**Global constraint applying to every phase**: documentation and `references.bib` only. If a
phase would require touching a Lean term, stop and record the obstruction rather than editing.

---

### Phase 1: Expansion.lean — divergence-witness note and termination-claim correction [COMPLETED]

**Goal**: Create the canonical, durably-anchored record of the divergence witness in
`Expansion.lean`, and replace the circular termination claim at `:124-125` with an accurate one
that points at it. This phase creates the anchor that Phases 2, 3, and 4 cross-reference, so it
runs first and alone.

**Tasks**:
- [x] Read `specs/317_propositional_tableau_completeness/reports/14_blocker-analysis.md` and
      transcribe the divergence data exactly. *(also cross-checked against report 13, the cited
      full derivation, which carries the complete fuel/max-label table; used report 13's fuller
      figures where 14 only summarized.)*
- [x] Add a new module-level note in `Expansion.lean` immediately before the `## Decision
      Procedures` section header (i.e. before `intFuel`), so it sits adjacent to the existing
      fuel/measure documentation. Used the stable, greppable heading
      `/-! ### Divergence witness: no world bound exists for this calculus -/`.
- [x] The note contains, in prose (no `#eval`): the witness formula (complexity 9); the measured
      max-label growth table at fuel 10/20/30/40/60/80/120/160/200/260 (linear, no saturation);
      the structural-duplication fact (period-2 grandparent duplication from world 3); the three
      labelled (a)/(b)/(c) consequences; a closing directive against attempting
      `intExpandBranches_world_bound`/`hnw`/`hUniv` as stated; and a method statement (evaluation
      of `intExpandBranches` on the witness at increasing fuel, re-verified in Lean).
- [x] Replaced the circular clause at `Expansion.lean:124-125` with an accurate statement:
      termination is NOT established, the loop diverges on some inputs, the `intUniverse φ0`
      bound is itself refuted; cross-references the *Divergence witness* note. Rest of
      `applyAllTImpRules`'s docstring left intact.
- [x] No task/plan/report/phase numbers in new prose; cites declaration names and section
      headings only.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` — new module note before
  `## Decision Procedures`; rewritten clause in `applyAllTImpRules`'s docstring

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` succeeds
- `awk 'length>100 {print FNR}' Cslib/.../Expansion.lean` prints nothing
- `grep -cE '^[[:space:]]*sorry[[:space:]]*$' Cslib/.../Expansion.lean` returns `0`
- `grep -n '#eval\|#check\|dbg_trace' Cslib/.../Expansion.lean` returns nothing
- `git diff -- Cslib/.../Expansion.lean` shows only comment-line changes
- `grep -n 'Divergence witness' Cslib/.../Expansion.lean` returns the new anchor

---

### Phase 2: Scheme.lean — annotate the refuted world-bound sites [COMPLETED]

**Goal**: Mark `intUniverse` and `intApplyRuleFull_outputs_subset`'s `hnw` as refuted-by-
counterexample, pointing at Phase 1's anchor, without touching either declaration.

**Tasks**:
- [x] Amended `intUniverse`'s docstring to state that the linear world bound `φ.complexity + 1`
      it assumes is REFUTED as an invariant of branches actually produced by
      `intExpandBranches`; the definition is retained as a measure-domain convenience only and
      must not be read as a containment guarantee. Points at the *Divergence witness* note in
      `Expansion.lean`.
- [x] Replaced the ephemeral citation
      `report 07 §Q4 F5, `intExpandBranches_world_bound` (continuation, see handoff)` with a
      durable anchor (the `Expansion.lean` note plus the already-cited `modalUniverse` /
      `FmpMeasure.lean:149-152` mirror).
- [x] Amended `intApplyRuleFull_outputs_subset`'s docstring to state that the `hnw` hypothesis
      is FALSE for branches the expansion loop actually produces — refuted by direct
      counterexample, not merely unproven — so the lemma is conditionally true but its
      hypothesis is not dischargeable at the intended call sites. States explicitly that the
      hypothesis is deliberately left in place. Points at the *Divergence witness* note.
- [x] Dropped `(task 317 phase 6.2, ... report 07 line 143)` and `(task 317 phase 10)` from the
      rewritten prose, replacing with declaration-name anchors.
- [x] Did not alter the `hnw` binder, the lemma statement, or any tactic (verified: `hnw`
      hypothesis and lemma signature grep-identical after the edit).

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — docstrings at `:1570-1574`
  and `:1798-1809` only

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` succeeds
- `awk 'length>100' Cslib/.../Scheme.lean` prints nothing
- `grep -cE '^[[:space:]]*sorry[[:space:]]*$' Cslib/.../Scheme.lean` returns `2`
- `git diff -- Cslib/.../Scheme.lean` touches only lines inside `/-- ... -/` blocks
- `grep -n 'hnw : nextWorld ≤ φ0.complexity + 1' Cslib/.../Scheme.lean` still matches (statement
  unchanged)

---

### Phase 3: Scheme.lean — record the fuel-0 refutation at the `sorry` [COMPLETED]

**Goal**: Record, at and around the `sorry` in `intExpandBranches_openBranch_sat`'s fuel-0 case,
that the goal is FALSE at its current statement, with the Lean-verified counter-instance — so no
future dispatch attempts to close it as stated.

**Tasks**:
- [x] Replaced the fuel-0 comment block with an accurate refutation record stating that the
      goal is FALSE AT ITS CURRENT STATEMENT.
- [x] Included the counter-instance verbatim: `branches = [[⟨.neg, p ∧ q, 0⟩]]`,
      `expandedSets = [[]]`, `nextWorlds = [1]`, `edgeSets = [[]]`.
- [x] Included why every hypothesis holds: `ILabelBound` holds trivially; `IExpandedConsistent`
      / `IAllAccessConsistent` are vacuous at `e = []`; the length hypotheses are `(1, 1)`. The
      loop returns exactly this branch, and `IBranchSaturation.sat_fand`'s premise evaluates
      `true` while both disjuncts evaluate `false`.
- [x] Stated the consequence explicitly: no proof can close this `sorry` at its current
      statement; the lemma must be RESTATED (e.g. with a saturation-establishing precondition on
      the initial worklist), out of scope here — this note only records the refutation.
- [x] Amended the lemma's docstring to say the base case is refuted, not merely gapped, and
      point at the in-proof note.
- [x] The `sorry` token stays exactly where it is, on the same line, unchanged (verified: still
      the second of two bare `sorry` occurrences, still inside the `| zero =>` branch).

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — docstring at `:2556-2558`
  and the in-proof comment at `:2575-2577`

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` succeeds
- `grep -cE '^[[:space:]]*sorry[[:space:]]*$' Cslib/.../Scheme.lean` returns `2`
- The second `sorry` is still inside `intExpandBranches_openBranch_sat`'s `| zero =>` branch
- `awk 'length>100' Cslib/.../Scheme.lean` prints nothing

---

### Phase 4: Scheme.lean — `sat_timp` hygiene (items 1 and 2) [COMPLETED]

**Goal**: Make the file's account of `sat_timp` internally consistent and true to the code:
delete/rewrite the stale trailing GAP 2 block, and correct BOTH instances of the false "not
added as a field" claim.

**Tasks**:
- [x] Verified first: `sat_timp` is a live `IBranchSaturation` field at `Scheme.lean:105-108`,
      and the STOP-gate note already declares Gap 2 RESOLVED. Confirmed before editing.
- [x] **Deleted** the trailing GAP 2 investigation block (standalone module note immediately
      before `end Cslib.Logic.PL`, refuted in full by the current code — Gap 2/determinacy is
      already resolved earlier in the file).
- [x] Corrected the first "not added as a field" instance (the STOP-gate's "Consequence"
      paragraph). Now states: `sat_timp` IS an `IBranchSaturation` field (`:105-108`), realized
      by `intApplyRuleFull`'s `.pos, .imp` branching arm (`Rules.lean:245-268`, `:274-275`),
      reflexive at the label of the copy it is given. No converse of the induction hypothesis is
      needed: in `truthLemma`'s T-imp case the `F(φ')@w'` arm contradicts `IForces w' φ'` via
      `ih_φ'.2`, and the `T(ψ')@w'` arm yields the goal via `ih_ψ'.1`. Stale phase-numbered
      framing dropped.
- [x] Corrected the SECOND instance inside `truthLemma`'s T-imp case comment. Now states the
      field exists and supplies the disjunction at the label its copy carries; the case remains
      `sorry` solely because the disjunction is available at `w'` only once `w'` carries its own
      `T(φ'→ψ')` copy — the copy-propagation invariant (Gap 1), which is not established.
- [x] Added a cross-reference in the Gap 1 discussion to the *Divergence witness* note in
      `Expansion.lean`, noting that the world bound any fuel-sufficiency argument would
      ultimately be sized against is refuted, WITHOUT asserting Gap 1 itself is refuted.
- [x] Dropped task/phase/plan/report citations from all prose rewritten in this phase; used
      declaration names and file/section anchors instead.
- [x] Did not touch the `sorry` at the end of the T-imp case, the `intro _` before it, or any
      tactic (verified: `intro _` / `sorry` pair unchanged, still the first of the two bare
      `sorry` occurrences).

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — `:492-539` region,
  `:586-598` comment block, deletion of `:3020-3041`

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` succeeds
- `grep -cE '^[[:space:]]*sorry[[:space:]]*$' Cslib/.../Scheme.lean` returns `2`
- `grep -n 'determinacy remains' Cslib/.../Scheme.lean` returns nothing
- `grep -in 'NOT added as an .IBranchSaturation. field' Cslib/.../Scheme.lean` returns nothing
- `grep -n 'sat_timp :' Cslib/.../Scheme.lean` still matches at `:105-108` (field intact)
- `awk 'length>100' Cslib/.../Scheme.lean` prints nothing

---

### Phase 5: references.bib — add the two dangling BibKeys [COMPLETED]

**Goal**: Land `GargGenoveseNegri2012` and `Dyckhoff1992`, and repair the two citation sites in
`Expansion.lean` that reference them.

**Tasks**:
- [x] Re-ran `grep -c GargGenoveseNegri2012 references.bib` and `grep -c Dyckhoff
      references.bib` immediately before editing: both returned `0`, so no conflicting entry
      existed to reconcile with.
- [x] Added `@inproceedings{GargGenoveseNegri2012, ...}` (author `Garg, Deepak and Genovese,
      Valerio and Negri, Sara`; title `Countermodels from Sequent Calculi in Multi-Modal
      Logics`; booktitle `Proceedings of the 27th Annual IEEE/ACM Symposium on Logic in
      Computer Science (LICS 2012)`; publisher `IEEE`; year `2012`) next to the Fitting
      entries, matching the surrounding two-space-indent, aligned-`=` style.
      *(deviation: pages/DOI NOT confirmable this session — no network access and no local
      match in `~/Projects/Literature/index.json` or `zotero-library.json` — landed with the
      confirmed fields only, per the plan's own fallback instruction; flagged in the task
      summary rather than invented.)*
- [x] Added `@article{Dyckhoff1992, ...}`: author `Dyckhoff, Roy`; title `Contraction-free
      sequent calculi for intuitionistic logic`; journal `Journal of Symbolic Logic`; volume
      `57`; number `3`; pages `795--807`; year `1992`.
      *(deviation: DOI not confirmable this session for the same reason; landed without it.)*
- [x] Fixed the `Expansion.lean` bracketed claim asserting a completed future action
      (`BibKey added to references.bib in Phase 6`) — replaced with a plain citation
      `[`GargGenoveseNegri2012`]`.
- [x] Fixed the bare prose citation `(Dyckhoff 1992 / Negri–von Plato 2001 §5.5)` — attached
      `[`Dyckhoff1992`]` (new) and `[`NegriVonPlato2001`]` (already present).
- [x] **Coordination note recorded** in the task summary artifact (not in `references.bib`,
      per the no-task-references rule): `GargGenoveseNegri2012` has landed; any other in-flight
      task adding the same BibKey should verify-not-duplicate.
- [x] Zero-risk cleanup performed: removed `Directly relevant to task 504.` from the `Gore1999`
      entry's `note` field (one-sentence removal, does not obscure the diff).

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `references.bib` — two new entries
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` — citation sites at `:210`
  and `:264`

**Verification**:
- `grep -c GargGenoveseNegri2012 references.bib` returns `1`
- `grep -c 'Dyckhoff1992' references.bib` returns at least `1`
- No duplicate BibTeX keys: `grep -o '^@[a-z]*{[A-Za-z0-9]*' references.bib | sort | uniq -d`
  returns nothing
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` succeeds
- `git diff -- Cslib/.../Expansion.lean` shows only comment-line changes

---

### Phase 6: Full verification and invariant audit [COMPLETED]

**Goal**: Prove the hard constraint held: no Lean semantics changed, sorry inventory identical,
style clean, no task-number citations introduced into deliverables.

**Tasks**:
- [x] Built every module in the directory (`Rules`, `Expansion`, `Scheme`, `Soundness`,
      `Completeness`, `DecisionProcedure`) individually — all green. Then `lake build` for the
      whole library (3259 jobs) — green.
- [x] Sorry inventory unchanged against the baseline table: Scheme 2 (line 605, `truthLemma`'s
      T-imp case; line 2620, `intExpandBranches_openBranch_sat`'s fuel-0 case), Completeness 1,
      all others 0.
- [x] No debug artifacts in any `Cslib/` file under the directory (grep returned nothing).
- [x] Style: no line over 100 chars in either edited `.lean` file; no trailing whitespace
      introduced; copyright headers intact (`head -1` of each file starts with `/-`).
- [x] **Semantics audit**: `git diff -U0` reviewed line-by-line for both edited `.lean` files —
      every added/removed line sits inside a `--` line comment, a `/-- ... -/` docstring, or a
      `/-! ... -/` module note. No code line was touched.
- [x] **Rule audit**: `git diff -- Cslib/ references.bib | grep -inE '^\+.*(task [0-9]|phase
      [0-9]|plan [0-9]{2}|report [0-9]{2})'` returned nothing.
- [x] Ran `lake exe lint-style` locally (available in this `lakefile.toml`) — exit 0, no output.
      Also ran `lake exe checkInitImports` (exit 0), `lake lint` (no new warnings on the two
      touched files), `lake test` (exit 0, full suite green), and `lake exe mk_all --module`
      ("No update necessary"). `lake shake` reported one pre-existing import-minimization
      suggestion on `Expansion.lean` unrelated to this task (no import statement was added or
      touched by this plan; verified this task's diff contains zero `import` lines).
- [x] Confirmed the *Divergence witness* anchor is discoverable: `grep -rn 'Divergence witness'
      Cslib/` returns the note itself plus its self-reference and the three cross-references
      added in Phases 2, 3, and 4 (five total occurrences).

**Timing**: 0.5 hours

**Depends on**: 2, 3, 4, 5

**Files to modify**: none (verification only)

**Verification**:
- All commands above pass with the stated outputs
- `lake build` exits 0

---

## Testing & Validation

- [ ] `lake build` succeeds for the whole library
- [ ] Bare-`sorry` counts per file identical to the baseline table
- [ ] `git diff -U0 -- Cslib/` contains no non-comment line changes
- [ ] No `#eval` / `#check` / `dbg_trace` in `Cslib/`
- [ ] No line in the two edited `.lean` files exceeds 100 characters
- [ ] `grep -c GargGenoveseNegri2012 references.bib` == 1; `Dyckhoff1992` present; no duplicate
      BibTeX keys
- [ ] `grep -n 'determinacy remains' Cslib/` returns nothing
- [ ] `grep -in 'NOT added as an .IBranchSaturation. field' Cslib/` returns nothing
- [ ] No task/phase/plan/report number citations in any added prose

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` — *Divergence witness*
  module note; corrected termination claim; two repaired citation sites
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — corrected `intUniverse` and
  `intApplyRuleFull_outputs_subset` docstrings; fuel-0 refutation record; corrected `sat_timp`
  account (both instances); deleted stale GAP 2 block
- `references.bib` — `GargGenoveseNegri2012`, `Dyckhoff1992`
- `specs/572_tableau_docstring_hygiene_divergence_record/summaries/01_*-summary.md` — including
  the task 456 coordination note for `GargGenoveseNegri2012`

## Rollback/Contingency

Every change is confined to comments and one BibTeX file, so rollback is
`git checkout -- Cslib/Logics/Propositional/Tableau/Intuitionistic/ references.bib`. If a phase
fails verification, revert that phase's files and leave earlier phases in place; phases are
sequenced so each leaves the build green independently. If a BibTeX field cannot be confirmed,
land the entry with the confirmed fields only and record the unconfirmed ones in the summary
rather than inventing values. If Phase 4's deletion of the `:3020-3041` block turns out to
break the build (it should not — it is a standalone module note), restore it and instead rewrite
it in place to state that Gap 2 is resolved.
