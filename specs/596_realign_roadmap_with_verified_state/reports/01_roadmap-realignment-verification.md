# Research Report: Task 596

**Task**: 596 - Correct ROADMAP.md's stale cleanup agenda and fold in the unrepresented open tasks
**Started**: 2026-08-09
**Completed**: 2026-08-09
**Effort**: large (documentation-only; verification-heavy)
**Dependencies**: None
**Sources/Inputs**:
- Live tree at `/home/benjamin/Projects/cslib` (HEAD `d1de5b85`)
- `bash .claude/scripts/lean-sorry-census.sh` (comment/string-aware sorry counter — authoritative)
- `git worktree` checkout of commit `26644732` (the exact commit ROADMAP.md's "Verified sorry
  counts (2026-08-07)" line cites) for apples-to-apples comparison
- `specs/state.json`, `specs/archive/state.json`
- `specs/ROADMAP.md`, `specs/ROADMAP-alignment-audit.md`, `specs/reviews/review-2026-08-07.md`
- Direct file reads: `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`,
  `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`, `Cslib/Foundations/Logic/Tableau/Blocking.lean`,
  `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`,
  `specs/archive/530_.../summaries/02_*.md`, `specs/548_.../` (state.json entry)
**Artifacts**: this report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- The task description's own baseline figures ("re-verified 2026-08-07 and accurate") are
  **wrong in one specific case and right in others** — I re-verified every one directly against
  the tree/commit, not from the description. See the table in "Findings" below.
- **Biggest single finding, not in the task description at all**: the "27 sorries (Bimodal 23 /
  Propositional 4 / Modal 0)" census on ROADMAP.md:146-149 was **already wrong at the exact
  commit it cites** (`26644732`, 2026-08-07). A proper comment/string-aware census
  (`.claude/scripts/lean-sorry-census.sh`, verified against `26644732` via `git worktree`) gives
  **Bimodal = 41**, not 23, at that same commit — total 45, not 27. The undercount is a
  methodology artifact: 7 `set_option warn.sorry false` suppression annotations were apparently
  counted 1-for-1 as "sorries," but several of the annotated declarations contain 4-6 raw
  `sorry` occurrences each. Current tree: still 41/4/0 = 45 (Bimodal/Propositional/Modal
  unchanged from `26644732`; no further drift since the review, just a review-time miscount that
  needs correcting, not a moving target).
- The Section B "stale row" claims (1) all check out as described and are *further* along than
  the task description states in one case: `LoopChecking.lean` is now 2,216 lines / 15
  declarations (not the review's 1,626/20, and nowhere near ROADMAP's 10,723/230) — it has grown
  since 2026-08-07 as the `S4/Driver.lean` module (now 2,913 lines) absorbed more logic. Boneyard/,
  `Blocking.lean`, and all 8 refactor-programme subtasks (558, 562-567 + parent 557 expanded) are
  confirmed terminal, as is the 413/414 proof-style pair.
- **Forward progress since the review that the task description does not know about**: task 511
  (S4 decidability capstone) and task 548 (TB corner) both **completed after** commit
  `26644732`, landing `instDecidableS4Valid` and `instDecidableTBValid`. The modal decidability
  matrix is now **8/15** (K, T, B, TB, S5, K5/Five, KB5, S4), not the 6 ROADMAP:114 claims — this
  is genuine progress, not a miscount (6 *was* correct at `26644732`). K still lives at
  `CompletenessLoop.lean:2308`, confirming the task description's `:114` FrameCompleteness
  mis-attribution.
- Propositional tableau completeness's ROADMAP:155 tracking chain (`574 → 456 → 317, 430, 583`)
  is now **5/5 terminal**, not 4/5: 574/456/317/430 completed, 583 **abandoned** (task
  description said 583 was still open/active — it is not). The chain is fully dead with no
  successor named on the roadmap, even though the 4 sorries it was tracking are still live
  (confirmed by census) and are now actually owned by task 593's expansion tree (601-606: three
  completed, one researching, two not-started).
- Task count has grown to **46 open tasks** (not 30), of which **36 have no roadmap presence**
  (not 20) — the set kept growing between the review and this research pass, including this very
  reconciliation effort's own siblings (594, 595) and five newly-created tasks (599-606).
- `ROADMAP-alignment-audit.md:79`'s "Modal Tableau Decidability section" recommendation is
  confirmed still unapplied (`grep` for the phrase in ROADMAP.md returns nothing).
- The `:173-176` "open decision (no task yet)" on BXCanonical/dense is confirmed still
  undecided — no task in `specs/state.json` or the archive targets "BXCanonical" or "abandon...
  algebraic pipeline" by name.

## Context & Scope

Task 596 asks for a documentation-only realignment of `specs/ROADMAP.md` against verified
repository state, per five numbered items in the task description. The description itself warns
its cited figures are dated 2026-08-07 and may have drifted; my job was to re-verify everything
against the current tree (or, where the claim is inherently "as of the review commit," against
that exact commit) rather than trust either ROADMAP.md's numbers or the task description's
numbers. Findings below are organized by the description's five numbered items, plus a
"baseline recheck" section for the figures the description said not to disturb.

## Findings

### Baseline recheck (description said "already correct — do not disturb")

| Claim | Description says | Verified now | Verdict |
|---|---|---|---|
| Sorry census | 27 (Bimodal 23 / Propositional 4 / Modal 0) | **45** (Bimodal 41 / Propositional 4 / Modal 0), confirmed identical at commit `26644732` via worktree | **WRONG even at the cited commit** — not tree drift, a review-time undercount. Must be corrected on ROADMAP.md:146-149 and 157. |
| 15-system grid | accurate | `ls Cslib/Logics/Modal/ProofSystem/Instances/` = 15 files (K,T,B,D,D4,D5,D45,DB,K4,K45,K5,KB5,S4,S5,TB) | Confirmed accurate. |
| 24 subsumption theorems | accurate | `grep -c "^theorem \|^lemma "` on `InterSystem/AxiomSubsumption.lean` = 24 | Confirmed accurate. |
| 6 `instDecidable*Valid` instances | accurate | **8 now** (K, T, B, TB, S5, Five/K5, Kb5, S4) — but 6 *was* correct at commit `26644732`; S4 landed via task 511 (completed 2026-08-08) and TB via task 548 (completed 2026-08-09), both after the review | Was accurate at the review commit; **stale now** due to genuine forward progress. Update to 8. |

**Why the sorry-count miscount matters for the fix**: the undercount traces to counting
`set_option warn.sorry false in` suppression-annotation *sites* rather than raw `sorry`
occurrences. E.g. `BXCanonical/Chronicle/ChronicleToCountermodel.lean` has 7 suppression
annotations but 19 actual `sorry` terms (one annotated declaration alone,
`chronicle_temporal_frame` fields at lines 200-204, carries 5). Any future ROADMAP sorry census
should re-run `.claude/scripts/lean-sorry-census.sh` (the repo's own comment/string-aware
counter) rather than a suppression-annotation count or a naive `grep -c sorry`.

Current per-file Bimodal breakdown (via the census script, current tree):

| File | Sorries | Description's (stale) figure |
|---|---|---|
| `BXCanonical/Chronicle/ChronicleToCountermodel.lean` | 19 | 12 |
| `Bundle/SuccRelation.lean` | 14 | 7 |
| `Bundle/UntilSinceCoherence.lean` | 4 | 2 |
| `ConservativeExtension/TemporalConservativity.lean` | 2 | 1 |
| `BXCanonical/Frame.lean` | 2 | 1 |
| **Total** | **41** | 23 |

BXCanonical total (Chronicle + Frame) is **21**, not the description's 13 or ROADMAP's 14.

### (1) Section B stale rows

All five confirmed stale as described, plus corrections:

- **Modal tableau refactor programme** (557 → 558, 562-567): 557 status = `expanded`; all of
  558, 562, 563, 564, 565, 566, 567 = `completed` in `specs/archive/state.json`. Confirmed
  terminal, move to Completed.
- **`LoopChecking.lean` size**: currently **2,216 lines / 15 declarations**. Neither ROADMAP's
  10,723/230 nor the task description's 1,626/20 is current — the file grew since 2026-08-07 (the
  parallel `S4/Driver.lean` module the split produced is now 2,913 lines / 73 decls, up from
  whatever it was at the review). The 10 `Modal/Tableau/S4/*.lean` modules total 12,510 lines
  combined with `LoopChecking.lean`. Use the freshly-measured 2,216/15 figure, not either stale
  number, and note in the ROADMAP entry that this figure moves quickly (task 600, "retire the
  unordered S4 stepper stack at LoopChecking," is open and not_started — expect further change).
- **`Boneyard/`**: confirmed exists (`Boneyard/README.md`, `Boneyard/ModalTableauS4Keyed/` with
  2 files). Terminal.
- **`Foundations/Logic/Tableau/Blocking.lean`**: confirmed exists, 202 lines, with exactly the 4
  named declarations (`Branch.typeAt`, `Branch.containmentBlocked`, `distinctTypes_le_pow`,
  `strictChain_le_card`) plus 3 more not named in the task description
  (`mem_typeAt_iff`, `containmentBlocked_iff`, `exists_typeAt_eq_of_card_lt`,
  `card_image_le_pow_of_forall_subset`, `toFinset_eraseDups`). No longer "(new)"; drop the tag.
- **Proof-style simplification** (413, 414): both `completed` in the archive. Terminal.

### (2) Further falsified claims

| ROADMAP claim | Verified current state |
|---|---|
| `:175` BXCanonical "14 sorries" | **21** (19 ChronicleToCountermodel + 2 Frame), not 14, not the task description's 13 |
| `:157` 23 sorries split 13/9/1 across three tasks | Actual Bimodal total is 41: BXCanonical 21, Bundle (SuccRelation+UntilSinceCoherence) 18, TemporalConservativity 2. The three-way split concept is directionally right but every number is off; also, the tracking column at `:157` lists only `36, 37, 215` — 36/37 are the upstream BimodalLogic-port gates (`36` not_started, `37` blocked), 215 is `blocked` ("Fill the discrete-gated Bimodal sorries"). None of these three currently-open tasks names Bundle/SuccRelation.lean or UntilSinceCoherence.lean specifically in ROADMAP prose — confirmed unnamed as the task description states. |
| `:153` gates S4 decidability on 511 → 506 → 300 | **511 is now `completed`** (2026-08-08, after the review). `instDecidableS4Valid` landed (`FrameCompleteness.lean:9101`). This row should move out of "Remaining" entirely — S4 is delivered. |
| `:155` tracking chain 574→456→317,430,583 "4/5 archived" | Now **5/5 terminal**: 574, 456, 317, 430 = `completed`; 583 = `abandoned` (not merely "the one open row" as the task description implies — it closed since). The chain is fully dead. The 4 live Propositional sorries it was tracking (confirmed still 4 by census: `Intuitionistic/Scheme.lean` ×2, `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`) are now actually owned by task 593's expansion (601 completed, 602 completed, 603 completed, 604 researching, 605/606 not_started) — ROADMAP:155 should repoint to 593/601-606, not the dead 574/456/317/430/583 chain. |
| `:183` "folded into" Chronicle consolidation (530) | Confirmed false as stated. 530 is `completed` but closed as a **descoped partial**: its own summary states Phases 3b/3c/4a/4b were formally descoped by an explicit 2026-07-26 user scoping decision, because each tree's `Chronicle` structure is locally indexed and a bridging `.toGeneric` projection breaks `rcases`/`simp`. Only `ChronicleTypes`/`RRelation`'s shared core/Phase-3a helpers ended up generic. Task 41 ("abstract shared completeness infrastructure between temporal and bimodal") is still `not_started`; task 568 ("research the highest-quality Chronicle-structure refactor") is `blocked`. Neither is named at `:183`. |
| `:114` attributes all 6 (now 8) decidability instances to `FrameCompleteness.lean` | Confirmed: `instDecidableKValid` lives at `CompletenessLoop.lean:2308`, not `FrameCompleteness.lean`. The other 7 (T, B, TB, S5, Five, Kb5, S4) are correctly in `FrameCompleteness.lean`. |

### (3) Open tasks with no roadmap presence

Total open tasks: **46** (`specs/state.json`, not 30). Task numbers literally appearing anywhere
in ROADMAP.md's prose: `7, 8, 10, 14, 15, 23, 24, 26, 27, 36, 37, 42, 89, 215, 230, 300, 317, 375,
413, 414, 430, 450, 456, 506, 511, 530, 534, 553, 557, 558, 562-567, 574, 582, 583, 723`.
Cross-referencing against the current open list, **36 of 46 open tasks have zero roadmap
presence** (this grew from the review's 20/30 because 16 new tasks were created since, several of
them siblings of this reconciliation effort itself):

- **548** (decidability corners): now `completed`, but scope-narrowed — matrix is 8/15, not the
  "essentially delivered" framing `:114` implies. The still-blocked corners (D, K4, K45, D4, D5,
  D45 — 6 named in 548's own scope-narrowing note, gated on a seriality/`RuleApplicationSpec`
  spec-shape blocker for D-type frames) remain unaddressed and unowned by any single open task;
  successor gates are owned by 598 (completed), 599 (not_started), 600 (not_started).
- **CS5 stream** (537, 551, 554 — all `blocked`): absent from roadmap. The "Completed" CS5 row at
  `:130` ("Constructive CS5 ≡ IS5 completeness ... the constructive capstone") is contradicted by
  `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`'s own module docstring
  (confirmed by direct read, current tree): *"The general `nik_TS5_soundness` is **not yet
  landed**... assessed intractable at standard effort pending resolution of a genuine open
  mathematical question."* Only the anti-vacuity corollary landed, not the general soundness
  direction task 537 owns.
- **Temporal tableau** (301 `blocked`, 425 `not_started`): absent from roadmap. `:122` lists
  "tableau" as a delivered Temporal component; `Cslib/Logics/Temporal/Tableau/` does exist (8
  files, 4,269 lines: Branch, Closure, Completeness, Defs, Rules, Saturation, Soundness,
  TimeOrdering) and the Temporal tree is sorry-free per census, but the git history shows task
  301's own commits marking Completeness as `[PARTIAL]` ("phase 8: Completeness — extractModel,
  structural branch lemmas [PARTIAL]") and both 301/425 remain open, non-terminal statuses. The
  "tableau" claim at `:122` is overstated as unqualified-delivered.
- **571** (`blocked`, strict-Until/Since-gated Bimodal sorries — SuccRelation/UntilSinceCoherence,
  the 18-sorry Bundle group above), **568/569** (Chronicle refactor research / continuous-time
  axioms), **576** (`not_started`, Chronicle namespace/structure coincidence), **39/40/41**
  (temporal/bimodal completeness port infrastructure), **181** (`not_started`, primitive
  diamond/allFuture/allPast propagation), **400/497/409** (propositional upstream: connective
  typeclass unbundling, imp/impl naming, bot-rule-free ND), **588/589/590** (import-reachability
  dedup, unusedArguments lint, out-of-tree probe re-establishment): all confirmed absent from
  ROADMAP.md and still open/blocked/not_started in current state.json.
- Additionally absent and newly created since the review (not named in the task description,
  surfaced by this re-verification): **591-593** (completed/completed/expanded — the
  openBranch_countermodel disposition stream, now superseded by its own children 601-606),
  **594/595** (this reconciliation effort's meta siblings), **597/598** (completed — tableau
  driver abstraction decisions), **599/600/601/602/603** (599/600 not_started, 601/602/603
  completed), **604** (`researching`), **605/606** (`not_started`).

### (4) ROADMAP-alignment-audit.md:79 recommendation

Confirmed still unapplied: `grep -n "Modal Tableau Decidability" specs/ROADMAP.md` returns
nothing. The audit file's Tier 4 entry (`ROADMAP-alignment-audit.md:79`) recommended either
adding this section or explicitly scoping down further spawns; neither happened. This task
should implement it, and per the task description also give CS5, temporal-tableau, and
propositional-upstream their own sections — all three streams are currently fully invisible on
the roadmap per finding (3) above.

### (5) BXCanonical/dense open decision

Confirmed still unresolved: no task in `specs/state.json` or `specs/archive/state.json` targets
"BXCanonical" or the algebraic-pipeline-vs-dense-completion decision by name (checked via title/
description grep across both state files). The `:173-176` "open decision (no task yet)" framing
is still accurate today, just with the corrected sorry count (21, not 14) once updated per
finding (2).

## Decisions

None — this is a research report; the realignment itself is implementation work for `/plan` and
`/implement`. No numeric claim above should be copied verbatim into a future plan without a fresh
re-run of the same verification commands, since (per the sorry-census and decidability-matrix
findings) the tree continues to move and even the review commit's own baseline had at least one
outright error.

## Risks & Mitigations

- **Risk**: the sorry-census correction (23→41 for Bimodal, 27→45 total) is the single highest-
  leverage but also highest-blast-radius change — it appears in the ROADMAP prose in at least
  three places (`:146-149`, `:157`, `:175`) and likely elsewhere (`README.md` was also cited by
  commit `26644732`'s own message, "reconcile falsified sorry-count prose in README and
  ROADMAP" — worth a quick grep of README.md for the same 27/23 figures during implementation,
  though README.md is out of this task's `file_scope` (`specs/ROADMAP.md` only) and should only
  be flagged, not edited).
  **Mitigation**: implementer should re-run `bash .claude/scripts/lean-sorry-census.sh
  Cslib/Logics/Bimodal` (and Propositional, Modal) fresh at execution time rather than trust
  even this report's numbers verbatim, per the task's own constraint.
- **Risk**: `LoopChecking.lean`'s line/declaration count is a fast-moving target (task 600 is
  open against it). **Mitigation**: implementer should re-measure at execution time; consider
  phrasing the ROADMAP entry to avoid embedding a specific line count that will stale again
  quickly, or explicitly date-stamp it.
- **Risk**: the open-task list will have moved again between this report and `/plan`/`/implement`
  dispatch (it moved from 30→46 between the review and this report). **Mitigation**: implementer
  should re-run the state.json task enumeration and roadmap cross-reference at execution time,
  not copy the 36/46 figure from this report.

## Context Extension Recommendations

None — this is a project-specific (cslib) documentation task, not an agent-system gap.

## Appendix

Key commands used (all re-runnable at execution time for a fresh check):

```bash
bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/Bimodal      # -> sorry_count: 41
bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/Propositional # -> sorry_count: 4
bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/Modal         # -> sorry_count: 0
grep -c "^theorem \|^lemma " Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean # -> 24
ls Cslib/Logics/Modal/ProofSystem/Instances/ | wc -l                 # -> 15
grep -rn "^instance instDecidable.*Valid" --include=*.lean Cslib/    # -> 8 hits
wc -l Cslib/Logics/Modal/Tableau/LoopChecking.lean                   # -> 2216
python3 -c "import json; d=json.load(open('specs/state.json')); print(len(d['active_projects']))"  # -> 46
```

Worktree comparison against the exact commit ROADMAP.md's sorry census cites:
```bash
git worktree add /tmp/cslib-old-596 26644732
bash .claude/scripts/lean-sorry-census.sh /tmp/cslib-old-596/Cslib/Logics/Bimodal  # -> sorry_count: 41 (same as current)
git worktree remove /tmp/cslib-old-596 --force
```
