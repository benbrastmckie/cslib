# Measurement Ledger — Acceptance-Gate Fixes (Task 567)

**Tree SHA at Phase 1**: `3a11702e`
**Working tree**: clean (`git status --porcelain Cslib CslibTests ORGANISATION.md` empty)
**Toolchain**: as recorded in the research report (Lean `v4.33.0-rc1`, Lake `5.0.0-src`)

> All commands below were re-run live at implementation time. Every edit anchor cited in later
> phases is a quoted string from this ledger, never a line number from the research report — the
> research report's own `README.md` line citations have already drifted 6-8 lines past ~line 65.

## Partition: CORRECT (do not touch) vs DRIFTED (correct in Phase 3)

### CORRECT — matches stored figure, no action

| Figure | Command | Live | Stored | Status |
|---|---|---|---|---|
| S4/*.lean total lines | `cat Cslib/Logics/Modal/Tableau/S4/*.lean \| wc -l` | 10294 | 10,294 | CORRECT |
| LoopChecking.lean declarations | `grep -cE "$PAT" LoopChecking.lean` | 20 | 20 | CORRECT |
| Pre-split LoopChecking.lean lines | (§6.2 of research report, not re-run — expensive historical figure) | 11,393 | 11,393 | CORRECT (carried, not disputed) |
| Subsystem sorry census | two-grep filtered to Modal/Tableau/ | 1 (`FrameSoundness.lean:1251`) | 1 | CORRECT |
| Subsystem `^axiom` count | `grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/` | 0 | 0 | CORRECT |
| Repo-wide `^axiom` count | `grep -rnE '^axiom ' Cslib/` | 26 | 26 | CORRECT |
| Build job count | `lake build` | 3323 (Phase 5 will re-confirm) | 3323 | CORRECT |

### DRIFTED — corrected in Phase 3 (or Phase 2 for module count)

| ID | Figure | Command | Live | Stored | Locations (quoted-string anchors) |
|---|---|---|---|---|---|
| D1 | S4 module count | `ls -1 Cslib/Logics/Modal/Tableau/S4/*.lean \| wc -l` | **10** | eleven | See "eleven" anchor list below |
| D2 | `LoopChecking.lean` lines | `wc -l Cslib/Logics/Modal/Tableau/LoopChecking.lean` | **1626** | 1,723 | `README.md`: "and again after the split completed (1,723 lines / 20 declarations" ; "is **1,723 lines / 20 top-level declarations**" |
| D3 | Pre-split declaration count | `grep -cE "$PAT" LoopChecking.lean` (historical, pre-split tree) | **243** | 241 | `README.md`: "11,393 lines / 241 declarations" and "241 top-level declarations / 58 \`private\`" |
| D3b | Derived residue count | `cat S4/*.lean \| grep -cE "$PAT"` | **223** | "The other 221 declarations" | `README.md`: "The other 221" (arithmetic: 20+223=243) |
| D4 | Repo-wide code-position sorry count | two-grep, no Modal/Tableau/ filter | **28** | 29 | `README.md`: "gives **29** code-position sorries repo-wide" and "The 29 above counts sorries in *code position*" |
| D5 | Regression-corpus size | `wc -l CslibTests/S4LoopGuardRegression.lean` | **214** | 197 | `README.md`: `wc -l CslibTests/S4LoopGuardRegression.lean                                       # 197` |
| D6a | `hintikkaS4_*` bridge set | `grep -nE '^(private )?(theorem\|lemma) hintikkaS4_' S4/Hintikka.lean \| wc -l` | **10** | 8 | `README.md`: `Cslib/Logics/Modal/Tableau/S4/Hintikka.lean \| wc -l   # 8` and "**\`hintikkaS4_*\` bridge set: 8 declarations.**" |
| D6b | `ModalTableauResult` subsystem span | `grep -rl 'ModalTableauResult' --include='*.lean' Cslib/Logics/Modal/Tableau/ \| wc -l` | **9** | 8 | `README.md`: `Cslib/Logics/Modal/Tableau/ \| wc -l   # 8` and "spans 8 modules here, 9 repo-wide" |
| D6c | `ModalTableauResult` repo-wide span (to be RESCOPED) | old: `grep -rl 'ModalTableauResult' --include='*.lean' . --exclude-dir=.lake \| wc -l` = 13 (scans `specs/`, volatile); rescoped: `grep -rl 'ModalTableauResult' --include='*.lean' Cslib CslibTests \| wc -l` = **10** | old 13 / rescoped 10 | 9 | `README.md`: `grep -rl 'ModalTableauResult' --include='*.lean' . --exclude-dir=.lake \| wc -l    # 9` |
| §6.1a | `FrameSoundness.lean` lines (self-flagged stale) | `wc -l FrameSoundness.lean` | **5396** | 5,317 | `README.md`: "\`FrameSoundness.lean\` 5,317 lines" |
| §6.1b | `FrameCompleteness.lean` lines (self-flagged stale) | `wc -l FrameCompleteness.lean` | **8264** | 4,307 | `README.md`: "\`FrameCompleteness.lean\` 4,307 lines" |

**Cardinality note**: the DRIFTED partition has 11 rows (D1, D2, D3, D3b, D4, D5, D6a, D6b, D6c,
§6.1a, §6.1b), matching the plan's "roughly eleven correctable numeric/textual sites" scope
hypothesis.

## "eleven"/"Eleven" occurrence census — CRITICAL SCOPE FINDING

`grep -rn 'eleven\|Eleven' Cslib/Logics/Modal/Tableau/ ORGANISATION.md` returns **12 hits**, not
6. Six are the D1 module-count off-by-one (in scope for Phase 2). **The other six are an
unrelated, CORRECT figure — the `RuleApplicationSpec` structural-hypothesis bundle's field
count (seven fields extended to eleven) — and MUST NOT be touched.** This is a distinct
quantity from the S4 module count; conflating them would corrupt correct documentation. This is
exactly the "Over-correction: touching a figure that already reproduces" risk the plan's risk
table names, surfaced concretely.

### D1 module-count sites (IN SCOPE — correct "eleven" -> "ten")

1. `Cslib/Logics/Modal/Tableau/LoopChecking.lean:39` — `"...invariant split -- was extracted into eleven \`S4/*.lean\` modules (below), each along the"`
2. `Cslib/Logics/Modal/Tableau/README.md:23` — `"distributed across the eleven \`S4/*.lean\` modules -- see..."`
3. `Cslib/Logics/Modal/Tableau/README.md:47` — `"docstring for the full residue rationale and the eleven-module map). The other 221"`
4. `Cslib/Logics/Modal/Tableau/README.md:48` — `"declarations / ~9,670 lines live in the eleven \`S4/*.lean\` modules (10,294 lines total there,"`
5. `Cslib/Logics/Modal/Tableau/README.md:50` — `"docstring overhead across eleven new files)."`
6. `ORGANISATION.md:198` — `"the two end-to-end capstones, re-exporting all eleven modules."`

### RuleApplicationSpec field-count sites (OUT OF SCOPE — leave untouched, unrelated quantity)

1. `Cslib/Logics/Modal/Tableau/TDriver.lean:734` — `"driver, combining the eleven fields"`
2. `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean:44` — `"from seven fields to eleven (F8 \`localShapeInvariance\` through F12 \`diaPosWitness\`,"`
3. `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean:355` — `"type-check). Constructor/destructor on the shared eleven conjuncts plus \`ModalPotentialInv\`'s"`
4. `Cslib/Logics/Modal/Tableau/GenericDriver.lean:21` — `"- \`RuleApplicationSpec apply\`: the structural-hypothesis bundle (eleven fields, see below --"`
5. `Cslib/Logics/Modal/Tableau/GenericDriver.lean:32` — `"This extends the bundle from seven to eleven fields to generalize the Hintikka-set/"`
6. `Cslib/Logics/Modal/Tableau/BDriver.lean:39` — `"- \`modalApplyOneB_spec : RuleApplicationSpec modalApplyOneB\`: the eleven-field structural"`
7. `Cslib/Logics/Modal/Tableau/BDriver.lean:768` — `"driver, combining the eleven fields discharged above. This is the B-system analogue of"`

(This is 7 lines, not 6 — `CompletenessLoop.lean` has two hits. Combined with the 6 D1 sites this
is 13 total raw grep lines, but two of the D1 sites — `README.md:47`/`:48` — are adjacent
sentences citing the module count twice; the earlier six-site count from the plan's Scope
Hypothesis undercounted by one line. Recorded here, not forced to six.)

**Phase 2 deviation notice**: Phase 2's verification step "`grep -rn 'eleven\|Eleven' ... returns
nothing`" cannot be satisfied literally without corrupting the correct RuleApplicationSpec
figures. The phase will instead verify: zero D1 module-count hits remain, and exactly the 7
RuleApplicationSpec hits remain unchanged.

## s4witness.lean live trace (verbatim, captured for Phase 4)

```
phiW = ((◇p0∧◇(□p0∧◇p0))→⊥)
[0] b = F(((◇p0∧◇(□p0∧◇p0))→⊥))@0
      acc = []   keys = 0↦{}
      e   = []
      nonMintCandidates = [F(((◇p0∧◇(□p0∧◇p0))→⊥))@0]
      guard(pos,p0,@2) = none
      T(box p0)@1 ∈ b = false
      eBoxOnlyNeg = true
      keys(0) = ∅ : true
      eDiaOnlyPos = true
[1] b = T((◇p0∧◇(□p0∧◇p0)))@0, F(((◇p0∧◇(□p0∧◇p0))→⊥))@0
      acc = []   keys = 0↦{}
      e   = [F(((◇p0∧◇(□p0∧◇p0))→⊥))@0]
      nonMintCandidates = [T((◇p0∧◇(□p0∧◇p0)))@0]
      guard(pos,p0,@2) = none
      T(box p0)@1 ∈ b = false
      eBoxOnlyNeg = true
      keys(0) = ∅ : true
      eDiaOnlyPos = true
[2] b = T(◇p0)@0, T(◇(□p0∧◇p0))@0, T((◇p0∧◇(□p0∧◇p0)))@0, F(((◇p0∧◇(□p0∧◇p0))→⊥))@0
      acc = []   keys = 0↦{}
      e   = [F(((◇p0∧◇(□p0∧◇p0))→⊥))@0, T((◇p0∧◇(□p0∧◇p0)))@0]
      nonMintCandidates = []
      guard(pos,p0,@2) = none
      T(box p0)@1 ∈ b = false
      eBoxOnlyNeg = true
      keys(0) = ∅ : true
      eDiaOnlyPos = true
[3] b = T(p0)@1, T(◇p0)@0, T(◇(□p0∧◇p0))@0, T((◇p0∧◇(□p0∧◇p0)))@0, F(((◇p0∧◇(□p0∧◇p0))→⊥))@0
      acc = [0→1]   keys = 0↦{} 1↦{+p0,+p0,+p0}
      e   = [F(((◇p0∧◇(□p0∧◇p0))→⊥))@0, T((◇p0∧◇(□p0∧◇p0)))@0, T(◇p0)@0]
      nonMintCandidates = []
      guard(pos,p0,@2) = (some 1)
      T(box p0)@1 ∈ b = false
      eBoxOnlyNeg = true
      keys(0) = ∅ : true
      eDiaOnlyPos = true
[4] b = T((□p0∧◇p0))@2, T(p0)@1, T(◇p0)@0, T(◇(□p0∧◇p0))@0, T((◇p0∧◇(□p0∧◇p0)))@0, F(((◇p0∧◇(□p0∧◇p0))→⊥))@0
      acc = [0→2 0→1]   keys = 0↦{} 1↦{+p0,+p0,+p0} 2↦{+(□p0∧◇p0)}
      e   = [F(((◇p0∧◇(□p0∧◇p0))→⊥))@0, T((◇p0∧◇(□p0∧◇p0)))@0, T(◇p0)@0, T(◇(□p0∧◇p0))@0]
      nonMintCandidates = [T((□p0∧◇p0))@2]
      guard(pos,p0,@2) = (some 1)
      T(box p0)@1 ∈ b = false
      eBoxOnlyNeg = true
      keys(0) = ∅ : true
      eDiaOnlyPos = true
[5] b = T(□p0)@2, T(◇p0)@2, T((□p0∧◇p0))@2, T(p0)@1, T(◇p0)@0, T(◇(□p0∧◇p0))@0, T((◇p0∧◇(□p0∧◇p0)))@0, F(((◇p0∧◇(□p0∧◇p0))→⊥))@0
      acc = [0→2 0→1]   keys = 0↦{} 1↦{+p0,+p0,+p0} 2↦{+(□p0∧◇p0)}
      e   = [F(((◇p0∧◇(□p0∧◇p0))→⊥))@0, T((◇p0∧◇(□p0∧◇p0)))@0, T(◇p0)@0, T(◇(□p0∧◇p0))@0, T((□p0∧◇p0))@2]
      nonMintCandidates = [T(□p0)@2]
      guard(pos,p0,@2) = none
      T(box p0)@1 ∈ b = false
      eBoxOnlyNeg = true
      keys(0) = ∅ : true
      eDiaOnlyPos = true
[6] b = T(p0)@2, T(□p0)@2, T(◇p0)@2, T((□p0∧◇p0))@2, T(p0)@1, T(◇p0)@0, T(◇(□p0∧◇p0))@0, T((◇p0∧◇(□p0∧◇p0)))@0, F(((◇p0∧◇(□p0∧◇p0))→⊥))@0
      acc = [0→2 0→1]   keys = 0↦{} 1↦{+p0,+p0,+p0} 2↦{+(□p0∧◇p0)}
      e   = [F(((◇p0∧◇(□p0∧◇p0))→⊥))@0, T((◇p0∧◇(□p0∧◇p0)))@0, T(◇p0)@0, T(◇(□p0∧◇p0))@0, T((□p0∧◇p0))@2]
      nonMintCandidates = []
      guard(pos,p0,@2) = none
      T(box p0)@1 ∈ b = false
      eBoxOnlyNeg = true
      keys(0) = ∅ : true
      eDiaOnlyPos = true
[7] b = T(p0)@3, T(p0)@3, T(□p0)@3, T(p0)@2, T(□p0)@2, T(◇p0)@2, T((□p0∧◇p0))@2, T(p0)@1, T(◇p0)@0, T(◇(□p0∧◇p0))@0, T((◇p0∧◇(□p0∧◇p0)))@0, F(((◇p0∧◇(□p0∧◇p0))→⊥))@0
      acc = [2→3 0→2 0→1]   keys = 0↦{} 1↦{+p0,+p0,+p0} 2↦{+(□p0∧◇p0)} 3↦{+p0,+□p0,+p0,+p0}
      e   = [F(((◇p0∧◇(□p0∧◇p0))→⊥))@0, T((◇p0∧◇(□p0∧◇p0)))@0, T(◇p0)@0, T(◇(□p0∧◇p0))@0, T((□p0∧◇p0))@2, T(◇p0)@2]
      nonMintCandidates = []
      guard(pos,p0,@2) = (some 3)
      T(box p0)@1 ∈ b = false
      eBoxOnlyNeg = true
      keys(0) = ∅ : true
      eDiaOnlyPos = true
      SATURATED OPEN
```

**Divergence assessment against the box-plus attribution**: this live trace matches the research
report's §5.4 live trace **exactly** (same three divergences: `guard(pos,p0,@2)` reads `none` at
step [6] rather than `some 1`; step [7] mints fresh world 3 rather than firing redirect edge
`2→1`; termination at [7] with `SATURATED OPEN` and a boxed member `+□p0` now present in
`keys(3)`, rather than continuing to [8]). **The box-plus attribution fully explains the live
trace — no unexplained residual divergence.** Phase 4 may proceed to re-record, not block.

## Box-plus attribution chain

```
$ git log -1 --format='%h %ad' --date=short 5733dcd1
5733dcd1 2026-08-05
$ git log -1 --format='%h %ad' --date=short 7960c12e
7960c12e 2026-08-05
$ git log -1 --format='%h %ad' --date=short 80feb736
80feb736 2026-08-05
$ git merge-base --is-ancestor 5733dcd1 c8fede26 && echo YES
YES
$ git cat-file -e 5733dcd1 && git cat-file -e 7960c12e && git cat-file -e 80feb736 && echo "all three SHAs resolve"
all three SHAs resolve
```

All three box-plus commits (`80feb736`, `7960c12e`, `5733dcd1`) are dated 2026-08-05 and
`git merge-base --is-ancestor` confirms `5733dcd1` (the last of the three, birth-key enrichment)
predates `c8fede26` (the referenced completion commit that anchors the current programme's
range). The programme's own S4-module-extraction commits (task 565 phases) are dated 2026-08-06,
one day later. **Confirmed: the box-plus enrichment predates the programme.**

## Phase 5 evidence table (appended after CI re-run)

_(populated in Phase 5)_
