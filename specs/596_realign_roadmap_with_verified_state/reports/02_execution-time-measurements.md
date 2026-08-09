# Execution-Time Measurement Record: Task 596

**Execution date**: 2026-08-09
**HEAD at measurement time**: `5a4b5ce61464138576761a198b787d2047522703`

This record is the single source of truth for every numeral written into `specs/ROADMAP.md` by
Phases 2-5 of the implementation plan. Phase 6 cross-checks every figure in ROADMAP.md against
this file. Every entry below states the exact command run and its raw output.

## 1. Sorry census — IMPORTANT METHODOLOGY FINDING

The plan designates `bash .claude/scripts/lean-sorry-census.sh` as "the counter of record" and
predicts it will show Bimodal 41 / Propositional 4 / Modal 0 = 45, correcting the old ROADMAP
figure of Bimodal 23 / Propositional 4 / Modal 0 = 27.

**Commands run and raw output**:

```
$ bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/Bimodal
sorry_count: 41

$ bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/Propositional
sorry_count: 4

$ bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/Modal
sorry_count: 0

$ bash .claude/scripts/lean-sorry-census.sh Cslib/
sorry_count: 45

$ bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/Temporal   # -> 0
$ bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/LTL        # -> 0
$ bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/HML        # -> 0
$ bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/LinearLogic # -> 0
$ bash .claude/scripts/lean-sorry-census.sh Cslib/Foundations       # -> 0
```

This reproduces the plan's predicted 41/4/0 = 45 exactly. **However, direct inspection of the
script's matching logic and per-file output revealed that this figure is inflated by a real bug
in the script itself**, discovered during this measurement pass (not previously known/documented
anywhere in the plan, research report, or task description):

The script strips comments/strings correctly, then matches `\bsorry\b` on the stripped text. But
it does **not** exclude `set_option warn.sorry false in` — the annotation directive that suppresses
the "declaration uses sorry" compiler warning. Because `.` is a non-word character, `\bsorry\b`
also matches the "sorry" substring inside "warn.sorry", so **every suppression-annotation line is
counted as an extra phantom sorry, in addition to the real sorry it annotates**.

Verified by hand for every Bimodal file carrying sorries (command:
`bash .claude/scripts/lean-sorry-census.sh <file>`, then manually separating inventory lines that
are literally `set_option warn.sorry false in` from lines containing a real `sorry` tactic/term):

| File | script `sorry_count` | `set_option warn.sorry false in` lines | real `sorry` occurrences |
|---|---|---|---|
| `BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 19 | 7 | 12 |
| `BXCanonical/Frame.lean` | 2 | 1 | 1 |
| `Bundle/SuccRelation.lean` | 14 | 7 | 7 |
| `Bundle/UntilSinceCoherence.lean` | 4 | 2 | 2 |
| `ConservativeExtension/TemporalConservativity.lean` | 2 | 1 | 1 |
| **Total** | **41** | **18** | **23** |

`23 + 18 = 41` exactly, confirming the mechanism: the script's Bimodal total is the true raw-sorry
count (23) plus the number of suppression annotations (18), not the true raw-sorry count alone.

**Corroborating evidence this 23 figure (not 41) is the correct raw-sorry count**: the currently
open task 215 ("Fill the discrete-gated Bimodal sorries (BXCanonical Chronicle and Frame)", in
`specs/state.json`) independently states its own hand-audited scope as "BXCanonical/Chronicle/
ChronicleToCountermodel.lean: 12 sorries (lines 75, 145, 146, 152, 157, 162, 172, 173, 174, 175,
176, 187)" and "BXCanonical/Frame.lean: 1 sorry (line 161)" — **12 + 1 = 13**, matching this
measurement's manually-verified real-sorry counts for those two files exactly (12 and 1), and
matching neither the script's inflated 19+2=21 nor the old ROADMAP figure of 14.

Propositional has zero `set_option warn.sorry false in` annotations (confirmed: all 4 Propositional
sorries are bare), so Propositional's script count (4) is unaffected by this bug and is the correct
raw count. Modal is 0 either way.

**Corrected raw sorry counts** (script total minus double-counted annotation lines):
- Bimodal: **23** (BXCanonical 13 [12 Chronicle + 1 Frame], Bundle 9 [7 SuccRelation + 2
  UntilSinceCoherence], TemporalConservativity 1)
- Propositional: **4** (unaffected by the bug)
- Modal: **0**
- **Repo-wide total: 27**

This is numerically identical to the OLD ROADMAP figure (27: Bimodal 23 / Propositional 4 /
Modal 0), which the task description asserted was already correct and out of scope. Per this
measurement, that assertion holds: **the old figure was right; the "corrected" 41/45 figure is an
artifact of a bug in the designated counter script**, not of the suppression-methodology mechanism
the task description hypothesized (annotations undercounting multi-sorry declarations).

**Escalation**: this materially contradicts the task's own non-negotiable constraint ("The
sorry-census correction must state WHY the previous figure was wrong ... not merely swap the
number"). Flagged to the dispatching session (`team-lead`) before writing anything into
ROADMAP.md; this record captures the full evidence trail regardless of the resolution. **A
follow-up task to fix the `lean-sorry-census.sh` regex (exclude `set_option warn.sorry false in`
lines from the match, e.g. via a line-level pre-filter or a more specific regex than `\bsorry\b`)
should be created independently of how the ROADMAP census wording is resolved.**

### Bare vs. suppressed split (for the "gates lake build --wfail --iofail" claim)

```
$ grep -B1 sorry Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean | grep -c 'set_option warn.sorry'
0
$ grep -B1 sorry Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean | grep -c 'set_option warn.sorry'
0
$ grep -B1 sorry Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean | grep -c 'set_option warn.sorry'
0
```
Confirmed: all 4 Propositional sorries are bare (no suppression annotation) — this is what the
existing ROADMAP prose claims drives the red `lake build --wfail --iofail`. All 18 Bimodal
suppression sites are `warn.sorry`-annotated (per the table above), so Bimodal sorries do not
contribute to the build-red state; this matches the existing ROADMAP prose.

## 2. Decidability instances

```
$ grep -rn "^instance instDecidable.*Valid" --include=*.lean Cslib/
Cslib/Logics/Modal/Tableau/CompletenessLoop.lean:2308:instance instDecidableKValid
Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean:116:instance instDecidableMValid
Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:1390:instance instDecidableTValid
Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:2479:instance instDecidableBValid
Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:2753:instance instDecidableTBValid
Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:3246:instance instDecidableS5Valid
Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:4024:instance instDecidableFiveValid
Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:4900:instance instDecidableKb5Valid
Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:9101:instance instDecidableS4Valid
Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean:107:instance instDecidableIValid
```

10 hits total; 2 are Propositional (MValid, IValid — decision procedures for the propositional
tableau systems, not modal cube corners) and **8 are Modal cube corners**: K (`CompletenessLoop.
lean:2308`), T, B, TB, S5, Five (K5/Euclidean), Kb5, S4 (all six of the latter in
`FrameCompleteness.lean`). Matches the research report's prediction of 8 exactly. K is confirmed
in `CompletenessLoop.lean`, not `FrameCompleteness.lean` — the ROADMAP:114 attribution of all
instances to `FrameCompleteness.lean` is confirmed false.

Matrix coverage: **8 of 15** classical-cube systems have a `Decidable` instance (K, T, B, TB, S5,
K5/Five, KB5, S4). The 7 without: D, D4, D5, D45, DB, K4, K45.

## 3. Modal system grid and subsumption theorems

```
$ ls Cslib/Logics/Modal/ProofSystem/Instances/ | wc -l
15
$ ls Cslib/Logics/Modal/ProofSystem/Instances/
B.lean D.lean D4.lean D5.lean D45.lean DB.lean K.lean K4.lean K45.lean K5.lean
KB5.lean S4.lean S5.lean T.lean TB.lean

$ grep -c "^theorem \|^lemma " Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean
24
```
Both confirmed accurate as currently stated in ROADMAP.md — no correction needed for these two
figures.

## 4. LoopChecking.lean and S4/ directory

```
$ wc -l Cslib/Logics/Modal/Tableau/LoopChecking.lean
2216
$ grep -c "^theorem \|^lemma \|^def \|^instance \|^structure \|^inductive " Cslib/Logics/Modal/Tableau/LoopChecking.lean
15
$ ls Cslib/Logics/Modal/Tableau/S4/
BirthKey.lean Driver.lean Guard.lean Hintikka.lean HintikkaInvariant.lean
InvariantAcc.lean InvariantKeys.lean Invariant.lean Redirect.lean Universe.lean
$ wc -l Cslib/Logics/Modal/Tableau/S4/*.lean Cslib/Logics/Modal/Tableau/LoopChecking.lean | tail -1
12510 total
$ wc -l Cslib/Logics/Modal/Tableau/S4/Driver.lean
2913
$ grep -c "^theorem \|^lemma \|^def \|^instance \|^structure \|^inductive " Cslib/Logics/Modal/Tableau/S4/Driver.lean
73
```
`LoopChecking.lean` is **2,216 lines / 15 declarations** — neither ROADMAP's 10,723/230 nor the
task description's 1,626/20. The 10 `S4/*.lean` modules plus `LoopChecking.lean` combined total
**12,510 lines**. `S4/Driver.lean` alone is 2,913 lines / 73 declarations. Task 600 ("Retire the
unordered S4 stepper stack at LoopChecking.lean") is open (`not_started`) and targets this file, so
the figure is flagged as fast-moving in the ROADMAP edit.

## 5. Structural confirmations

```
$ ls -la Boneyard/ && find Boneyard/ -type f
Boneyard/README.md
Boneyard/ModalTableauS4Keyed/README.md
Boneyard/ModalTableauS4Keyed/KeysRootEmpty.lean
Boneyard/ModalTableauS4Keyed/RedirectOriginTransfer.lean
```
Confirmed exists, 2 files under `ModalTableauS4Keyed/` plus its own README.

```
$ wc -l Cslib/Foundations/Logic/Tableau/Blocking.lean
202
$ grep -n "^theorem \|^lemma \|^def \|^structure \|^inductive " Cslib/Foundations/Logic/Tableau/Blocking.lean
72:def typeAt
77:def posTypeAt
86:def containmentBlocked
91:lemma mem_typeAt_iff
106:lemma containmentBlocked_iff
130:theorem card_image_le_pow_of_forall_subset
142:theorem toFinset_eraseDups
150:theorem distinctTypes_le_pow
163:theorem exists_typeAt_eq_of_card_lt
185:theorem strictChain_le_card
```
Confirmed exists, 202 lines, 10 declarations (2 `def`s beyond `typeAt`/`posTypeAt` plus 8
theorems/lemmas — includes the 4 declarations named in the task description
(`Branch.typeAt`, `containmentBlocked`, `distinctTypes_le_pow`, `strictChain_le_card`) plus 6 more.
No longer "(new)".

```
$ ls Cslib/Logics/Temporal/Tableau/
Branch.lean Closure.lean Completeness.lean Defs.lean Rules.lean Saturation.lean Soundness.lean TimeOrdering.lean
$ wc -l Cslib/Logics/Temporal/Tableau/*.lean | tail -1
4269 total
```
8 files, 4,269 lines combined. Sorry-free (per Modal/Temporal census above).

```
$ sed -n '1,40p' Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean
```
Docstring (re-read in full at execution time) confirms: "The general `nik_TS5_soundness` is **not
yet landed**: the tree-shape invariant and graph-lifting machinery are outstanding ... assessed
intractable at standard effort pending resolution of a genuine open mathematical question." Only
the anti-vacuity corollary `nik_TS5_consistent` (proved via the direct one-point route, not as a
corollary of the general theorem) has landed. The ROADMAP "Completed" CS5 row overstates this.

## 6. Open task enumeration and roadmap cross-reference

```
$ python3 -c "import json; d=json.load(open('specs/state.json')); print(len(d['active_projects']))"
46
```

Full list (`project_number status task_type | title`), current tree:

```
36 not_started lean4 | Port discrete completeness (completeness_discrete) from upstream BimodalLogic
37 blocked lean4 | Port continuous extension completeness once developed upstream
39 not_started lean4 | Discrete temporal completeness
40 blocked lean4 | Continuous temporal completeness
41 not_started lean4 | Abstract shared completeness infrastructure between temporal and bimodal
181 not_started cslib | Propagate primitive diamond, allFuture, and allPast constructors to Bimodal
215 blocked cslib | Fill the discrete-gated Bimodal sorries (BXCanonical Chronicle and Frame)
300 blocked cslib | Umbrella task for modal frame extensions T/S4/S5 (and derived cube corners)
301 blocked cslib | Implement tableau decision procedure for temporal logic
375 not_started cslib | Fold the TABLEAU decision systems into the propositional proof-system TFAE
400 not_started cslib | Unbundle connective typeclasses; reconcile with fmontesi PR #607
409 blocked cslib | Literal bot-rule-free base ND inductive
425 not_started cslib | [Decomposed from temporal tableau umbrella, blocker C]
450 not_started cslib | Prove TM conservative over BX+ and close TemporalConservativity sorry
497 not_started cslib | Reconcile 'imp' vs 'impl' naming in Propositional
506 completed cslib | Deliver plan Phases 5 and 6 of task 300 (S4 loop-checking)
511 completed cslib | Follow-on to task 506 (S4 loop-checking): close S4 termination bound + decidability
534 not_started cslib | Pure K5/5 Euclidean tableau completeness without the equivalence route
537 blocked cslib | Prove the general labelled SOUNDNESS direction nik_TS5_soundness
548 completed cslib | Eight-corner decidability research/decidability, scope narrowed
551 blocked cslib | Deliver NATIVE Hilbert canonical-model completeness for constructive CS5
554 blocked cslib | CS5 rescoped research
568 blocked cslib | Research the highest-quality Chronicle-structure refactor
569 not_started cslib | Establish whether continuous time needs axioms beyond density
571 blocked cslib | Fill the strict-Until/Since-gated Bimodal sorries (SuccRelation, UntilSinceCoherence)
576 not_started cslib | Resolve the Chronicle namespace/structure name coincidence
583 abandoned cslib | Restate intExpandBranches_openBranch_sat
588 not_started cslib | Resolve five import-reachability duplicate families
589 not_started cslib | Fix repo-wide unusedArguments lint findings
590 not_started cslib | Re-establish six out-of-tree probe verdicts
591 completed cslib | Decide the openBranch_countermodel upward-closure disposition
592 completed cslib | Promote three cited-but-absent propositional refutation witnesses into CslibTests
593 expanded cslib | Find a uniform frame construction for openBranch_countermodel
594 not_started meta | Metatask: reconcile all open task records against verified repository state
595 not_started meta | Add a dependency-integrity validation gate
596 implementing meta | Correct ROADMAP.md's stale cleanup agenda (this task)
597 completed cslib | Decide the tableau driver abstraction across three termination regimes
598 completed cslib | Prototype and measure a serial-successor rule spec for the modal tableau driver
599 not_started cslib | Prototype the Euclidean rule combinator
600 not_started cslib | Retire the unordered S4 stepper stack at LoopChecking.lean
601 completed cslib | Port CompletenessLoop.lean top-loop Hintikka chain to RuleApplicationSpecAt
602 completed cslib | Promote openBranch_countermodel witness probes into CslibTests
603 completed cslib | Construct a uniform frame for openBranch_countermodel
604 planning cslib | Prove the countermodel forcing conjunct over the constructed frame
605 not_started cslib | Establish upward-closure of minBranchBotForces at the bot formula shape
606 not_started cslib | Discharge or restate the four propositional tableau completeness theorems
```

**Task numbers literally cited in ROADMAP.md prose** (verified by grepping each candidate number
with context and excluding false-positive numeric matches that are counts/sizes, not task
references — e.g. "10,723 lines" contains "723" but is not a citation of task 723; "14
declarations", "23 sorries", "230 declarations", "89% overlap" are similarly counts, not task
numbers):

```
36, 37, 215, 300, 375, 450, 506, 511, 530, 534, 553, 557, 558, 562, 563, 564, 565, 566, 567, 574,
582, 583, 413, 414, 317, 430, 456
```
27 distinct task numbers cited. Of these, `530` (Chronicle consolidation, completed) and `553`,
`582` (S4 keyed loop-check guard, discharged-by-refutation) do not appear in the current
`active_projects` list (already archived as terminal). `574` also does not appear as an
independent active entry (see item 8 below — chain fully terminal).

**Set difference — open tasks (from the current 46-entry `active_projects` list) with zero
ROADMAP.md presence** (i.e. active-project number not in the cited-task-number set above):

```
39, 40, 41, 181, 301, 400, 409, 425, 497, 537, 548, 551, 554, 568, 569, 571, 576, 588, 589, 590,
591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606
```
**36 of 46** open tasks (per this same `active_projects`-length methodology used by the research
report) have zero roadmap presence — matches the research report's prediction exactly.
**Roadmap-present count: 10 of 46** (36, 37, 215, 300, 450, 506, 511, 534, 583, plus 574's chain
head — see item 8).

## 7. Task status verification for every cited task number

| Task | Status (state.json / archive) | Terminal? |
|---|---|---|
| 36 | not_started | No |
| 37 | blocked | No |
| 215 | blocked | No |
| 300 | blocked | No |
| 317 | archived (see below) | Yes |
| 375 | not_started | No |
| 413 | completed (archive) | Yes |
| 414 | completed (archive) | Yes |
| 430 | archived (see below) | Yes |
| 450 | not_started | No |
| 456 | archived (see below) | Yes |
| 506 | completed (active list) | Yes |
| 511 | completed (active list) | Yes |
| 530 | completed (archive) | Yes |
| 534 | not_started | No |
| 553 | archived (see below) | Yes |
| 557 | expanded (archive) | Yes |
| 558, 562-567 | completed (archive) | Yes (all 7) |
| 574 | archived (see below) | Yes |
| 582 | archived (see below) | Yes |
| 583 | abandoned (active list) | Yes |

```
$ python3 -c "import json; d=json.load(open('specs/archive/state.json')); \
  projs=d.get('completed_projects',[])+d.get('archived_projects',[]); \
  nums=[317,430,456,553,574,582]; \
  print({p['project_number']: p['status'] for p in projs if p['project_number'] in nums})"
```
(Run at execution time; 317, 430, 456, 553, 574, 582 all resolve to terminal statuses in the
archive, consistent with the research report's finding that the Propositional tableau chain
(574→456→317,430,583) is 5/5 terminal and the S4-keyed guard chain (553→582) is fully discharged.)

## 8. Sanity checks

```
$ grep -n "Modal Tableau Decidability" specs/ROADMAP.md
(no output — confirmed still absent)

$ grep -i "BXCanonical\|algebraic.pipeline" specs/state.json specs/archive/state.json
(only hits are task 215's description text quoting the BXCanonical file paths as its own scope —
no task targets the BXCanonical-vs-algebraic-pipeline DECISION by name; confirmed still untracked)
```

## Summary table of figures for Phases 2-5 to consume

| Figure | Old ROADMAP value | Measured value | Action |
|---|---|---|---|
| Sorry census | 27 (Bi 23/Pr 4/Mo 0) | **PENDING team-lead decision** — see section 1. Candidate corrected value: 27 (Bi 23/Pr 4/Mo 0), i.e. unchanged, with a methodology note about the census-script bug; alternative: 45 (Bi 41/Pr 4/Mo 0) per literal script output | Hold — do not write Phase 2 census prose until resolved |
| Decidability instances | 6 | 8 (K,T,B,TB,S5,Five,Kb5,S4) | Correct to 8; correct K's file attribution to `CompletenessLoop.lean` |
| 15-system grid | 15 | 15 | No change |
| 24 subsumption theorems | 24 | 24 | No change |
| S4 row tracking (511→506→300) | in Remaining | 511 completed | Move to Completed |
| Pure-K5/5 row (534) | in Remaining | 534 not_started | Keep, unchanged |
| Propositional tableau chain (574→456→317,430,583) | "4/5 archived" | 5/5 terminal (574,456,317,430 completed; 583 abandoned); sorries now owned by 593's children 601-606 | Repoint to 593/601-606 |
| S4 keyed guard (553→582) | discharged by refutation | still confirmed discharged | Keep, re-confirm artifacts exist |
| Bimodal discrete completeness sorry count | 23 sorries / 36,37,215 | PENDING (see above); ownership split BXCanonical 13 (task 215) / Bundle 9 (task 571, unnamed on roadmap) / TemporalConservativity 1 (task 450, already separately rowed) | Hold pending census resolution; correct ownership split regardless |
| Bimodal→temporal conservativity | 1 sorry / 450 | 1 real sorry (task 450 not_started) | Keep, confirm |
| Modal tableau refactor programme (557→558,562-567) | in Remaining | all 8 terminal | Move to Completed |
| LoopChecking.lean size | 10,723 lines / 230 decls | 2,216 lines / 15 decls (task 600 open against it — flag as fast-moving) | Correct, date-stamp |
| Boneyard/ | pending | exists, 2 files + README | Move to Completed |
| Blocking.lean | "(new)" | exists, 202 lines / 10 decls | Drop "(new)" tag, state size |
| Proof-style simplification (413,414) | lower-priority outstanding | both completed | Move to Completed |
| BXCanonical sorry count (open decision) | 14 | PENDING (candidate: 13, per corrected raw count) | Hold; create decision task regardless with whichever count is confirmed |
| Decidability-instances row attribution | all to FrameCompleteness.lean | K is in CompletenessLoop.lean:2308; other 7 in FrameCompleteness.lean | Correct attribution, cite both files |
| CS5 "capstone" claim | fully delivered | general soundness direction NOT landed per Soundness.lean docstring; only anti-vacuity corollary landed | Qualify row |
| Temporal "tableau" claim | delivered | directory exists (8 files, 4269 lines, sorry-free) but owning tasks 301/425 non-terminal | Qualify row |
| Section C "folded into 530" | folded into consolidation | 530 closed as descoped partial (phases 3b/3c/4a/4b explicitly descoped); task 41 still holds obligation, task 568 exists because 530 didn't deliver it | Correct row |
| Open task coverage | 20/30 (review-time) | 36/46 absent (10/46 present) | State with as-of date |

**No ROADMAP.md edit has occurred in this phase.** `git status --short` at end of Phase 1 shows no
`.lean` file modified **by this task**. It does show three Propositional tableau files
(`Intuitionistic/Completeness.lean`, `Intuitionistic/Scheme.lean`, `Minimal/Completeness.lean`)
as modified — these are exactly the three files carrying the 4 Propositional sorries measured
above, and are within the declared scope of the concurrently-running tasks 604/605/606
("Discharge or restate the four propositional tableau completeness theorems"), running in
parallel in this same session. This task made zero edits to any `.lean` file (confirmed: no
`Write`/`Edit` tool call in this task's execution touched any `.lean` path). Because another
task is actively landing proof work against exactly the sorries this record measured, the
Propositional sorry count (4, all bare) is flagged as **live and subject to change before Phase 6
re-verification** — Phase 6 should re-run the Propositional census fresh rather than trust this
Phase 1 snapshot if a meaningful delay has elapsed.
