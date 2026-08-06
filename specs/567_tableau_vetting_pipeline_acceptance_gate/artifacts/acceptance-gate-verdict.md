# Acceptance-Gate Verdict — Tableau Vetting-Pipeline Acceptance Gate

**Verdict: `PASS WITH FIX TASKS`**

**Tree SHA**: `a0a24c0f` (post Phases 1-5 of this gate; the corrections this document itself
records are already applied and included in this SHA)
**Toolchain**: Lean `v4.33.0-rc1`, Lake `5.0.0-src`
**Verification date**: 2026-08-06
**Evidence base**: `specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/measurement-ledger.md`
(live re-measurement, Phase 1 partition, Phase 5 post-fix re-run)

---

## 1. Verdict Grammar

The gate emits exactly one of four verdicts. The distinction that matters is "does this block
the programme", not "is everything perfect":

| Verdict | Meaning | Emitted when |
|---|---|---|
| **PASS** | Programme accepted; no follow-up needed | Every blocking criterion green, and no finding at Medium or above |
| **PASS WITH FIX TASKS** | Programme accepted; follow-up recorded and linked | Every blocking criterion green, but one or more Medium/High findings exist that are (a) not proof defects, (b) not behaviour regressions, and (c) independently fixable |
| **CONDITIONAL** | Programme not yet accepted; a bounded, named repair must land first | A criterion is red but the repair is scoped, understood, and estimated |
| **FAIL** | Programme rejected back to implementation | A behavioural criterion is red — sorry census risen, a capstone or instance broken, a new axiom, or an unexplained regression-corpus divergence |

**This gate emits `PASS WITH FIX TASKS`.**

---

## 2. Blocking Criteria (all eleven green)

Any red criterion below would force `CONDITIONAL` or `FAIL`. All eleven are green, verified live
in Phase 5 against tree state `a0a24c0f` (see the measurement ledger's Phase 5 evidence table for
full command output):

| # | Criterion | Verification command | Result |
|---|---|---|---|
| B1 | `modalTableauS4Keyed_complete` green, standard axioms only | `#print axioms` | GREEN — `[propext, Classical.choice, Quot.sound]` only |
| B2 | All six `Decidable` instances green, standard axioms only | `#print axioms` on `instDecidable{K,T,B,S5,Five,Kb5}Valid` | GREEN — all six, standard axioms only |
| B3 | Tableau sorry census ≤ 1 | README's two-grep command filtered to `Modal/Tableau/` | GREEN — exactly 1 (`FrameSoundness.lean:1251`) |
| B4 | Subsystem axiom declarations = 0 | `grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/` | GREEN — 0 |
| B5 | Repo-wide `sorryAx` taint set unchanged | `scripts/check-axiom-census.sh` | GREEN — 43/43 exact-set match |
| B6 | `lake build Cslib` green | exit code | GREEN — exit 0, 3323 jobs |
| B7 | `lake test` green — all eight `S4LoopGuardRegression` rows | exit code | GREEN — exit 0, including KNOWN-UNSOUND row 1 still `"CLOSED"` |
| B8 | `lake exe checkInitImports` green | exit code | GREEN — exit 0 |
| B9 | `lake exe lint-style` green | exit code | GREEN — exit 0 |
| B10 | `mk_all` produces no change | diff `Cslib.lean` before/after | GREEN — byte-identical (md5 match), `git status` clean |
| B11 | Sorry/suppression/shake/lint-suppression/boneyard ratchets green | the four `scripts/check-*.sh` plus shake residue | GREEN — 28/28, 18/18, 12/12, 19/19, 5/5 |

**All eleven blocking criteria are green.**

---

## 3. Non-Blocking Criteria (four; red never blocks, always routes to a fix task)

| # | Criterion | Live | Rationale for non-blocking |
|---|---|---|---|
| N1 | `lake lint` green | RED — 145 errors | Not in PR CI (weekly cron only); all 145 pre-existing (`unusedArguments`, oldest attributed commit predates this programme); **zero** in `S4/` or `LoopChecking.lean` |
| N2 | `lake build --wfail --iofail` green | RED — 6 modules | Reproduces the documented Reasoned Exclusion **exactly** (same module set, same warning counts as recorded at the `LoopChecking.lean` split); no new warning site |
| N3 | Documentation figures reproduce | Was RED (9 findings + 2 self-flagged-stale + 2 undiscovered word-count drifts); **now GREEN** — corrected in Phases 2-3 of this gate | Documentation accuracy, not correctness; independently fixable and was in fact fixed by this same task |
| N4 | Out-of-tree probe reproduction | Partially RED — `s4witness.lean` did not reproduce its recorded trace (D8); `s4driver.lean` reproduced exactly | Cause identified and chronologically attributed to pre-programme work (box-plus birth-key enrichment, 2026-08-05, predates the programme's 2026-08-06 commits); re-recorded with attribution in Phase 4 of this gate |

---

## 4. Decision Rule

A finding is **fix-task-needed** (non-blocking) when **all three** hold:

1. **No proof is weaker.** No `sorry` added, no axiom added, no capstone or instance broken.
2. **The defect is either pre-existing or documentational.** `git log`/`git merge-base` shows the
   defect's origin commit is outside this programme's commit range, **or** the defect lives only
   in prose/comments/measurement rows.
3. **The fix is independently schedulable** — it does not need the programme reopened, and does
   not gate any downstream consumer.

A finding is **blocking** when any of:
- A blocking criterion (§2) is red.
- A regression-corpus divergence has **no identified cause** — an unexplained behavioural change
  is a FAIL even when every build is green, because behaviour preservation is then unproven.
- A documentation defect would mislead a reader into an incorrect *correctness* claim.

**Applied to this gate's one gate-critical finding (D8, the `s4witness.lean` divergence)**: Phase
1 of this task re-ran the probe live and captured the trace verbatim; Phase 4 verified the
box-plus attribution (three commits, all dated 2026-08-05, `git merge-base --is-ancestor`
confirming the enrichment predates the programme's own 2026-08-06 commits) **fully explains**
every one of the three concrete divergences — no unexplained residual. Under this decision rule,
an unexplained divergence would have forced `FAIL`; this one, explained and dated, does not.
D8 avoided `FAIL` for exactly this reason, not by default.

---

## 5. Remediation Ledger

**Findings this task fixed** (all documentation/artifact-only; zero `.lean` proof terms touched):

| Finding | Fix | Verified by |
|---|---|---|
| D1 — S4 module count off-by-one ("eleven" vs ten) | Corrected at 6 sites: `LoopChecking.lean` docstring, `ORGANISATION.md`, 4 `README.md` prose sites | `grep` confirms zero remaining module-count "eleven" hits (7 unrelated `RuleApplicationSpec`-field hits correctly left untouched) |
| D2 — `LoopChecking.lean` size (1,723 vs 1,626) | Corrected at 2 `README.md` sites | `wc -l` matches |
| D3 — pre-split declaration count (241/221 vs 243/223) | Corrected at 2 `README.md` sites, arithmetic now closes exactly (20+223=243) | live declaration-count grep matches |
| D4 — repo-wide code-position sorry count (29 vs 28) | Corrected at 2 `README.md` sites | two-grep census matches |
| D5 — regression-corpus size (197 vs 214) | Corrected in `README.md` measurement comment | `wc -l` matches |
| D6 — `hintikkaS4_*` bridge set (8 vs 10) and `ModalTableauResult` span (8/9 vs 9/10) | Corrected; repo-wide `ModalTableauResult` command **rescoped** from a bare `.` scan (which drifted every time a `specs/` task artifact mentioned the identifier) to `Cslib CslibTests` | live grep matches; rescoped command confirmed not to traverse `specs/` |
| §6.1 self-flagged stale figures — `FrameSoundness.lean`/`FrameCompleteness.lean` sizes (5,317/4,307 vs 5,396/8,264) | Refreshed, caveat sentence updated to new provenance | `wc -l` matches |
| Undiscovered at plan time — axiom-census raw word-occurrence counts (3/1,701 vs 11/1,704) | Corrected during Phase 3's closing full-region re-run | live `grep -row` matches |
| D8 — `s4witness.lean` stale recorded verdict | Re-recorded additively in `specs/553_.../reports/02_...md` §2.2a, with SUPERSEDED pointer on the original, live trace appended, and box-plus attribution (3 SHAs, dated, `merge-base` evidence) | 75 insertions / 0 deletions; original trace, hypothesis table, and refutation argument all intact; `CslibTests/` untouched |

**Findings this task deliberately did NOT fix** (recorded as Reasoned Exclusions or roadmap
items, §6-7 below): D7 (stale `s4subtractive3.lean` line citations), D9 (`s4probe.lean`
description mismatch), the 145 `unusedArguments` lint findings, the six unrun expensive probe
harnesses, the `lake build --wfail --iofail` six-module set.

---

## 6. Reasoned Exclusions

| Item | Reason | Evidence |
|---|---|---|
| 145 pre-existing `lake lint` `unusedArguments` findings (10 in `Modal/Tableau/`, zero in `S4/`/`LoopChecking.lean`) | `lake lint` is not in PR CI (weekly cron only); all findings pre-date this programme (oldest attributed commit for `modalTBoxSelf_sound` is far earlier, unrelated task) | Phase 5 lint log: 145/145 baseline match; zero `S4/`/`LoopChecking.lean` hits |
| Six unrun expensive out-of-tree probe harnesses (`s4probe.lean`, `s4boxed.lean`, `s4ancestor.lean`, `s4subtractive.lean`, `s4subtractive2.lean`, `s4subtractive3.lean`) | Re-running is a multi-hour job (largest sweep: 110,741 terminal leaves, 8-condition check each); disproportionate for a routine acceptance gate; needs its own dedicated budget | research report §5.5 |
| `lake build --wfail --iofail` six-module failure set | Reproduces the `LoopChecking.lean`-split task's documented exclusion exactly; fixing requires resolving the one recorded `[BLOCKED]` `sorry` or touching five untouched files, both outside this gate's territory | Phase 5 evidence table: exact module/warning-count match, no new site |
| `s4ancestor.lean` having no logged actual result to reproduce at all | The file carries only inline `(expect …)` annotations; the acceptance criterion "reproduces its recorded verdict" cannot be applied — there is no recorded verdict | research report §5.5 |

---

## 7. Standing Do-Nots (so a future reader does not undo this gate's findings)

- **The `S4LoopGuardRegression.lean` KNOWN-UNSOUND row 1 must stay `"CLOSED"`.** It is a
  deliberate regression lock (the file's own docstring is explicit) recording the shipped
  unordered driver's current, unsound verdict. Changing it to `"OPEN"` destroys the regression
  test.
- **No direct `import Cslib.Init` in any `S4/` module.** All ten satisfy `checkInitImports`
  transitively via `FmpMeasure.lean`'s direct import. Direct imports would create shake residue
  without fixing anything real.
- **Do not touch any of the 145 pre-existing `lake lint` `unusedArguments` findings** as part of
  a future acceptance gate for this programme; they are repo-wide debt (§6 above), scoped for
  the separate fix-task bundle below, not this programme's territory.

---

## 8. Roadmap Items (proposed; not created as tasks — orchestrator/user decides)

Written verbatim into `.return-meta.json`'s `completion_data.roadmap_items`:

1. **Retarget stale out-of-tree probe artifact records.** Annotate the S4 loop-guard report 01's
   `s4probe.lean` harness description as describing a superseded revision of the file (eight
   identifiers it names — `dfsR`, `classify`, `statsL`, `badL`, `hasCountermodel`, `notS4Valid`,
   `def sat`, `def isS4` — have zero matches in the current on-disk file), and replace
   `s4subtractive3.lean`'s pre-split `LoopChecking.lean:NNNN` line citations with declaration
   names (the declarations still exist, under the same names, in `S4/Hintikka.lean`,
   `S4/HintikkaInvariant.lean`, `S4/Driver.lean` — only the file:line citations are wrong).
2. **Repo-wide `unusedArguments` lint hygiene.** 145 sites across 27 modules (10 in
   `Modal/Tableau/`); uniform pattern is an unused `[Hashable Atom]` (or analogous) section-level
   instance binder; idiomatic fix is `omit [Hashable Atom] in` before the affected block.
3. **Re-establish the six expensive out-of-tree probe verdicts** (`s4probe.lean`, `s4boxed.lean`,
   `s4ancestor.lean`, `s4subtractive.lean`, `s4subtractive2.lean`, `s4subtractive3.lean`) under a
   dedicated multi-hour budget.

No task was created for any of these; `git diff specs/state.json` for `active_projects` is empty.
