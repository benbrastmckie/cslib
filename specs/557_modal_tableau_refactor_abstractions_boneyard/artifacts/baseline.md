# Measured Baseline — Modal Tableau Subsystem

- **Captured**: 2026-07-26
- **Captured at commit**: `7eb51f69f04ae061f4d99eee4d92d641af4a80b8`
- **Toolchain**: Lake 5.0.0-src+68218e8 (Lean 4.31.0)
- **Phase**: 2 (Stale-Build Clearance, Baseline Capture, Literature Index Repair)
- **Status of this capture**: measurements complete; **build gate BLOCKED** (see §1)

Every row below carries the exact command that reproduces it. Run each from the repository root.
Where a measured value differs from the figure carried in the plan, the row says so explicitly and
records **the measured value with its command** — no figure has been silently adjusted to match a
prior claim, per the Postmortem Constraint "Do NOT 'fix' a drifted number by adjusting it."

---

## 1. Build and CI gate status — BLOCKED

| Gate | Result | Command |
|---|---|---|
| Mathlib cache | OK — "No files to download", 8542 files already decompressed | `lake exe cache get` |
| `lake build` | **FAILS** (exit 1) | `lake build` |
| `lake exe checkInitImports` | **FAILS** (exit 1) | `lake exe checkInitImports` |

### 1.1 The build failure is a genuine compile error, not a stale artifact

The prerequisite recorded in the plan was that `checkInitImports` fails on a *stale build* (a
missing `Nested/Soundness.olean`) and that a rebuild would clear it. **That diagnosis is
superseded by this capture.** The olean is missing because the module does not compile:

```
error: Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean:1329:2: Missing cases:
_, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)
error: Lean exited with code 1
Some required targets logged failures:
- Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness
error: build failed
```

`checkInitImports` then fails downstream, as a consequence rather than as an independent defect:

```
uncaught exception: object file '.../Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.olean'
of module Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness does not exist
```

Reproduce:

```bash
lake build 2>&1 | tail -20
lake exe checkInitImports; echo "exit=$?"
```

### 1.2 Provenance: the error is outside Tableau and belongs to another task

```bash
git log --oneline -3 -- Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean
git status --short Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean   # clean — committed, not a local edit
```

The failing file was last touched by commit `88b198bf` ("task 554 phase 13.1: discharge boxL,
fourL, bStruct, boxR, diaL, tR, tL, diaR, fourR; assemble nested_sound with impL strategic
sorry"). It is committed work belonging to an in-flight, unrelated task on the constructive
nested-sequent subsystem. It is **not** in the modal Tableau subsystem and **not** in this task's
territory.

Per the phase specification — "If the build surfaces genuine errors outside Tableau, record them
and mark `[BLOCKED]`; do not repair unrelated subsystems under this task" — the error is recorded
here and the phase is marked `[BLOCKED]`. No repair was attempted, no `sorry` was added, and no
prior commit was reverted.

**Consequence for the programme**: verification gate V6 ("`checkInitImports` clean") is **not**
established. Every later acceptance gate in this plan that reads "checkInitImports clean"
currently verifies against nothing. This blocker must clear — by the owner of the constructive
nested-sequent work, not by this task — before those gates carry meaning.

---

## 2. File size and declaration density

| Fact | Measured | Command |
|---|---|---|
| `LoopChecking.lean` | 10,540 lines | `wc -l Cslib/Logics/Modal/Tableau/LoopChecking.lean` |
| `FrameSoundness.lean` | 5,317 lines | `wc -l Cslib/Logics/Modal/Tableau/FrameSoundness.lean` |
| `FrameCompleteness.lean` | 4,307 lines | `wc -l Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` |
| Three-file total | 20,164 lines | `wc -l Cslib/Logics/Modal/Tableau/{LoopChecking,FrameSoundness,FrameCompleteness}.lean` |
| `LoopChecking.lean` declarations | 230 | `grep -cE '^(private )?(protected )?(noncomputable )?(theorem\|lemma\|def\|abbrev\|instance\|structure\|inductive) ' Cslib/Logics/Modal/Tableau/LoopChecking.lean` |

All five match the plan's figures exactly.

---

## 3. Sorry census

### 3.1 Tableau subsystem — 1 sorry (matches plan)

```bash
{ grep -rnE '^[[:space:]]*sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/ ; \
  grep -rnE '(:=|\bby)[[:space:]]+sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/ ; } \
  | sort -u | grep 'Modal/Tableau/'
```

Sole result:

```
Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1244:    sorry
```

This is `branchSatisfiableIn_s4FC_ancestor_redirect` — the retained, user-decided, **IMMOVABLE**
sorry. Tableau sorry census is **1**, as the plan states.

### 3.2 Repo-wide — 29 measured, where the plan carries 10

```bash
{ grep -rnE '^[[:space:]]*sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/ ; \
  grep -rnE '(:=|\bby)[[:space:]]+sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/ ; } \
  | sort -u | wc -l
```

Measured: **29**. Distribution:

| Count | File |
|---|---|
| 12 | `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` |
| 7 | `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` |
| 2 | `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` |
| 2 | `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean` |
| 1 | `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` |
| 1 | `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` |
| 1 | `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` |
| 1 | `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` |
| 1 | `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` |
| 1 | `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean` |

**This is recorded as measured, not reconciled to the plan's 10.** The discrepancy is a
measurement-definition artifact, and the definition matters, so all three are given:

| Definition | Count | Command |
|---|---|---|
| Code-position `sorry` (the row above; excludes all prose/docstring mentions) | **29** | see above |
| The CI-pipeline grep, which also catches docstring prose such as "sorry-free" | 158 | `grep -rn "\bsorry\b" Cslib/ \| grep -v "^[[:space:]]*--" \| wc -l` |
| `declaration uses 'sorry'` warnings emitted by this build | 5 | `lake build 2>&1 \| grep -c "declaration uses \`sorry\`"` |

The 5-warning figure is an **undercount and must not be used as a census**: the build was
incremental, so fully-cached modules (including the whole Tableau subsystem) never re-elaborated
and never re-emitted their warnings. `FrameSoundness.lean:1244` is a real sorry that produced no
warning in this run. Only a clean-slate build would make the warning count authoritative, and a
clean-slate build is currently impossible (§1). **The 29-row code-position census is the figure
later phases should verify against.**

---

## 4. Axiom census — a scope distinction, not a corrected number

| Scope | Declarations | Raw word matches | Command |
|---|---|---|---|
| Tableau subsystem | **0** | 3 | `grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/ \| wc -l` / `grep -row 'axiom' Cslib/Logics/Modal/Tableau/ \| wc -l` |
| Repo-wide `Cslib/` | **26** | 1,701 | `grep -rnE '^axiom ' Cslib/ \| wc -l` / `grep -row 'axiom' Cslib/ \| wc -l` |

Both scopes match the plan. **These two numbers do not contradict each other and neither
supersedes the other**: the Tableau subsystem declares zero axioms; the repository declares 26,
none of them in Tableau. The 3 and 1,701 raw counts are word occurrences in prose and identifiers,
not declarations, and are recorded only to show why a naive word-count grep diverges. The
previously-noted "26 vs 47" discrepancy was a scope confusion of exactly this kind, not a drift.

---

## 5. Tag census

| Scope | FIX | NOTE | TODO | QUESTION | Command |
|---|---|---|---|---|---|
| `LoopChecking.lean` | 0 | 0 | 0 | 0 | `grep -c 'TODO:' Cslib/Logics/Modal/Tableau/LoopChecking.lean` (and `FIX:`/`NOTE:`/`QUESTION:`) |
| `FrameSoundness.lean` | 0 | 0 | 0 | 0 | as above |
| `FrameCompleteness.lean` | 0 | 0 | 0 | 0 | as above |
| Repo-wide `Cslib/` | — | **8** | **11** | — | `grep -rn 'TODO:' --include='*.lean' Cslib/ \| wc -l` / `grep -rn 'NOTE:' --include='*.lean' Cslib/ \| wc -l` |

0/0/0/0 in the three files and 11 TODO / 8 NOTE repo-wide — matches the plan.

---

## 6. Re-derivation debt — 55 sites, including `LoopChecking.lean`'s 14

```bash
grep -rho 'Local re-derivation' Cslib/ | wc -l
```

Measured: **55** exact-phrase occurrences. Per-file distribution (occurrence-counting, so
multiple hits on one line are counted separately):

```bash
for f in $(grep -rl 'Local re-derivation' --include='*.lean' Cslib/); do
  printf "%s\t%s\n" "$(grep -o 'Local re-derivation' $f | wc -l)" "$f"; done | sort -rn
```

| Sites | File |
|---|---|
| 14 | `Cslib/Logics/Modal/Tableau/S5Simplification.lean` |
| 14 | `Cslib/Logics/Modal/Tableau/LoopChecking.lean` |
| 10 | `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` |
| 6 | `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` |
| 6 | `Cslib/Logics/Modal/Tableau/BDriver.lean` |
| 5 | `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` |
| **55** | **total** |

The count is **55**, not the 77 carried in research report 01. `LoopChecking.lean`'s **14 sites**
are present in this distribution; report 01's per-file table omitted them entirely. The corrected
headline is smaller but the extraction work is **larger**, because the omitted file is the largest
one in the subsystem.

---

## 7. `ModalTableauResult` module span — 8 Tableau, 9 repo-wide

```bash
grep -rl 'ModalTableauResult' --include='*.lean' Cslib/Logics/Modal/Tableau/ | wc -l   # 8
grep -rl 'ModalTableauResult' --include='*.lean' . --exclude-dir=.lake | sort           # 9 modules
```

The 8 Tableau modules:

```
Cslib/Logics/Modal/Tableau/BDriver.lean
Cslib/Logics/Modal/Tableau/CompletenessLoop.lean
Cslib/Logics/Modal/Tableau/FiveSimplification.lean
Cslib/Logics/Modal/Tableau/FrameCompleteness.lean
Cslib/Logics/Modal/Tableau/LoopChecking.lean
Cslib/Logics/Modal/Tableau/S5Simplification.lean
Cslib/Logics/Modal/Tableau/Saturation.lean
Cslib/Logics/Modal/Tableau/TDriver.lean
```

The 9th repo-wide module is `CslibTests/S4LoopGuardRegression.lean`. (A tenth textual hit,
`specs/553_.../artifacts/s4driver.lean`, is a task artifact rather than a repository module and is
excluded from the span.)

**The span is 8 Tableau modules / 9 repo-wide.** Report 01's "measured 11" is drift; the task
description's original 8 was correct, and this baseline restores it.

---

## 8. `hintikkaS4_*` bridges — 8 declarations

```bash
grep -nE '^(private )?(theorem|lemma) hintikkaS4_' Cslib/Logics/Modal/Tableau/LoopChecking.lean
```

**8** declared bridges, at exactly the preserved-asset line numbers:

| Line | Bridge |
|---|---|
| 6626 | `hintikkaS4_box_pos_step` |
| 6712 | `hintikkaS4_dia_neg_step` |
| 6804 | `hintikkaS4_box_pos_self` |
| 6887 | `hintikkaS4_dia_neg_self` |
| 6972 | `hintikkaS4_box_neg` |
| 6984 | `hintikkaS4_diamond_pos` |
| 7008 | `hintikkaS4_box_pos_reflTransGen` |
| 7024 | `hintikkaS4_dia_neg_reflTransGen` |

Scope distinction: a *distinct-identifier* count over the same file returns 11, because three
further `hintikkaS4_*` identifiers appear in call positions or prose without being declarations
there (`grep -roE '\bhintikkaS4_[A-Za-z0-9_]*' ... | sort -u | wc -l` → 11). **The bridge count is
8**; 11 is an identifier-mention count and is recorded only to keep the two from being confused.

---

## 9. `S4LoopInv` structural anchors — all exact

```bash
grep -n 'structure S4LoopInv' Cslib/Logics/Modal/Tableau/LoopChecking.lean
sed -n '7070,7090p' Cslib/Logics/Modal/Tableau/LoopChecking.lean
grep -rn 'outDegEq :=' --include='*.lean' Cslib/
```

| Anchor | Line | Verified |
|---|---|---|
| `structure S4LoopInv` header | `LoopChecking.lean:7070` | exact |
| `outDegEq` field | `LoopChecking.lean:7084` | exact (15th line of the structure body) |
| Provision site 1 | `LoopChecking.lean:7569` (`outDegEq := modalStepBranchS4_preserves_outDegEq …`) | exact |
| Provision site 2 | `LoopChecking.lean:7633` (`outDegEq := modalStepBranchS4KeyedOrdered_preserves_outDegEq …`) | exact |
| Provision site 3 | `FrameCompleteness.lean:4217-4218` (positional anonymous constructor: `· intro w` / `simp [outDeg, Accessibility.successorsOf, Accessibility.empty]`) | exact |

The header is at **7070**, confirming the plan's correction of report 01's `:7072`.

---

## 10. Regression corpus and `Boneyard/`

| Fact | Measured | Command |
|---|---|---|
| `CslibTests/S4LoopGuardRegression.lean` | 197 lines | `wc -l CslibTests/S4LoopGuardRegression.lean` |
| `Boneyard/` directory | **absent** | `find . -type d -name 'Boneyard' -not -path './.lake/*'` (no output) |

Both match the plan.

---

## 11. Amplification figures — NOT re-measured

The two amplification figures carried from research report 01 —

- **4 declarations / 1,036 lines**
- **43 declarations / 1,983 lines reachable from `modalTableauS4Keyed_complete`**

— were **not re-measured in this capture**, and **no substitute number has been fabricated for
either**. They are reproduced above solely as unverified inheritances from report 01.

Re-measuring them requires reachability analysis over the elaborated environment (transitive
dependency closure from a named theorem), which requires a successfully built `.olean` for the
Tableau modules. The build is red (§1). Any phase that depends on these two figures must either
re-measure them after the §1 blocker clears, or state explicitly that it is relying on an
unverified report-01 inheritance.

---

## 12. Literature index — defect located, repair is out of territory

**The premise that this defect lives in `specs/literature-index.json` is incorrect, and the phase
task as written cannot be completed. What follows is the located root cause.**

### 12.1 What was checked

```bash
jq '.entries | length' specs/literature-index.json                    # 34
jq 'keys' specs/literature-index.json                                 # ["description","entries","version"]
bash .claude/scripts/literature-briefing.sh | grep -A2 'Single Step'  # renders "1 chunk(s)"
```

The per-repo sub-index is **reference-only**: each of its 34 entries carries exactly `doc_id` and
`relevance`. It stores no chunk counts, so there is no chunk-count field in it to repair. A
validation pass confirms it is otherwise healthy — all 34 `doc_id`s resolve against the global
index, with zero unresolved entries.

### 12.2 Where the "1 chunk" actually comes from

`.claude/scripts/literature-briefing.sh:203-206` derives the chunk count by counting **child
entries in the global index**, not files on disk:

```bash
chunk_count=$(jq --arg id "$doc_id" '[.entries[] | select(.parent_doc == $id)] | length' "$GLOBAL_INDEX")
```

and at line 224 falls back to `chunk_count=1` when that query returns 0.

For Massacci, the global index has the correct parent metadata but **no child entries**:

```bash
jq -c '.entries[] | select(.doc_id=="massacci_2000_single_step_tableaux_for_modal_logics")
       | {chunk_count}' ~/Projects/Literature/index.json          # {"chunk_count":77}
jq '[.entries[] | select(.parent_doc=="massacci_2000_single_step_tableaux_for_modal_logics")] | length' \
   ~/Projects/Literature/index.json                               # 0
ls ~/Projects/Literature/sources/massacci_2000_single_step_tableaux_for_modal_logics/chunk_*.md | wc -l   # 77
```

So: **77 chunk files on disk, `chunk_count: 77` recorded on the parent entry, 0 child entries, and
therefore "1 chunk(s)" rendered.** The corpus also holds the full-text
`massacci_2000_single_step_tableaux_for_modal_logics.md` alongside the 77 chunks (81 files total,
including `chunks.json`, `metadata.json`, `source.pdf`).

### 12.3 The defect is systemic, not Massacci-specific

```bash
for id in $(jq -r '.entries[].doc_id' specs/literature-index.json); do
  children=$(jq -r --arg i "$id" '[.entries[] | select(.parent_doc==$i)] | length' ~/Projects/Literature/index.json)
  ondisk=$(ls ~/Projects/Literature/sources/$id/chunk_*.md 2>/dev/null | wc -l)
  if [ "$children" = "0" ] && [ "$ondisk" -gt 1 ]; then echo "$id ondisk=$ondisk"; fi
done
```

**19 of the 34** sub-index documents under-report as "1 chunk" for the same reason, spanning
**848** chunk files on disk. Massacci (77) is one instance. Others include
`simpson_1994_intuitionisticmodallogic` (206 chunks), `biermandepaiva_2000` (53),
`alechinamendlerdepaivaritter_2001` (52), `marinmoralesstrassburger_2021` (51),
`trufas_2024` (48), `post_1921` (46), `arisakadasstrassburger_2015` (40),
`wijesekera_1990` (38), `from_2022` (34), `bentzen_2023` (33), `rabinovich_2014` (30),
`henkin_1949` (27), `burgess_1982_i` (25), `burgess_1982_ii` (24), `johansson_1937` (24),
`pacheco_2024` (20), `gabbay_1994_ch10` (12), `hodkinson_2006` (8).

### 12.4 Before / after, and why no repair was made

| | Massacci chunk count as reported by the briefing |
|---|---|
| Before | **1** |
| After | **1** (unchanged — no repair applied) |
| True on-disk | **77** chunks plus 1 full-text file |

The repair requires registering child entries with `parent_doc` set, in
`~/Projects/Literature/index.json` — the **user's global literature repository**, shared across
every project on this machine. That is outside this phase's declared territory (`.lake/` build
products, `specs/literature-index.json`, and this artifact), outside the `cslib` repository
entirely, and would affect consumers well beyond this task. `literature-build-index.sh` does not
perform it either: it rebuilds the SQLite FTS5 database from chunk files, not the `index.json`
parent/child entries the briefing script reads.

No mutation of the global corpus was made. This is recorded as a finding for a separately-scoped
owner, together with the exact defective code path (`literature-briefing.sh:203-206` and the
`chunk_count=1` fallback at `:224`) and the systemic extent above. A worthwhile fix is arguably in
the script rather than the data: when a parent entry already carries a correct `chunk_count`,
preferring it over the child-entry count would repair all 19 documents at once without rewriting
the corpus index.

---

## 13. Verification gate status

| Gate | Status | Basis |
|---|---|---|
| V4 (baseline captured with reproduction commands) | **PASS** | this document |
| V5 (Tableau sorry census exactly 1) | **PASS** | §3.1 |
| V6 (`checkInitImports` clean) | **FAIL — BLOCKED** | §1; blocked by a non-Tableau compile error |

## 14. Capture provenance

```bash
git rev-parse HEAD    # 7eb51f69f04ae061f4d99eee4d92d641af4a80b8
git status --short    # only specs/ task artifacts modified; no Cslib/ file touched
lake --version        # Lake 5.0.0-src+68218e8 (Lean 4.31.0)
```

The working tree carried no modifications to any `Cslib/` file at capture (only `specs/` task
artifacts), so every measurement above reflects committed repository state and is reproducible by
checking out `7eb51f69`.
