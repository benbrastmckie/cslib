# Research Report: Repair Stale and Self-Contradictory Tableau Docstrings

**Task**: 616 | **Type**: cslib | **Session**: sess_1786405794_f0204e_616
**Scope**: DOCUMENTATION ONLY. No `.lean` proof term, statement, or definition may change.

---

## 1. Executive Summary

Every defect class named in the task description is confirmed against the live tree. The
decisive open question — **which half of the Part 1 contradiction is authoritative** — is now
settled by direct machine evaluation, not inference:

> **The frame-adequacy table is CORRECT. The prose's headline verdict is also CORRECT.
> Only the evidence citation inside the prose is defective — and it is defective in *kind*,
> not merely in line numbers.**

Do **not** flip the table. Do **not** flip the "REFUTED" verdict. Replace the citation.

Additionally, six defect sites were found that the task description does **not** list. They
belong to the same defect classes and should be folded into the same pass (Section 7).

Baseline verified green: `lake build` over the three terminal modules in scope completes
successfully (967 jobs), with one pre-existing, unrelated `unusedDecidableInType` linter warning
at `Minimal/DecisionProcedure.lean:173`.

---

## 2. Machine-Verified Ground Truth for Part 1

### 2.1 The probe

A standalone probe was run against the **live library** (`lake env lean`, scratchpad file, not
committed). It reconstructs `IFimpAccess`'s own witness condition verbatim — using the library's
real `isAccessible` and the real branch returned by `intuitionisticTableau phiRef1` — and asks at
which worlds the predicate fails, over the raw frame `[(1,0),(2,1)]` and the augmented frame
`[(1,0),(2,1),(2,2),(1,2)]`.

Results:

| Query | Result |
|---|---|
| `IFimpAccess` failure worlds over **raw** `[(1,0),(2,1)]` | **`[2]`** — FAILS at world 2 |
| `IFimpAccess` failure worlds over **augmented** | **`[]`** — HOLDS |
| `isAccessible rawEdges 2 1` | `false` |
| `isAccessible augEdges 2 1` | `true` |
| F-implication obligations at world 2 | `F(ps → (ps → pr))@2` and `F(ps → pr)@2` |

The mechanism is exactly the one `BetaSplitRefutation.lean` describes: `fimpWitnesses = [1]`
(CI-protected at `BetaSplitRefutation.lean:411-413`) — world 1 is the *only* world on the branch
carrying `T(ps)` and `F(pr)`, so it is the only admissible `IFimpAccess` witness for
`F(ps → pr)@2`. World 1 is not raw-reachable from world 2 (raw reachability runs 0 → 1 → 2). The
loop-back edge `(1,2)`, present only in the augmented frame, is what supplies it.

**Verdict: `rawEdges` is REFUTED for `IFimpAccess`, post-repair, exactly as the table says.**

This is independently corroborated in-tree at `Scheme.lean:7912-7914`, which states the same
split ("raw frame: `hpers` holds, `IFimpAccess` refuted; augmented frame: `IFimpAccess` holds,
`hpers` was refuted"). Two independent sites agree with the table.

### 2.2 What is actually wrong with the parenthetical

`Scheme.lean:9603-9611` fuses two distinct claims into one sentence:

| Claim | Status |
|---|---|
| Headline: "`rawEdges` was, and remains, REFUTED as a witness for `IFimpAccess`" | **TRUE** (§2.1) |
| Evidence: "`WitnessProbe.lean:174-176` (`#eval check [(1,0),(2,1)]` reports `some (true, true)` — upward-closed but FORCES `phiRef1` at world 0)" | **FALSE on every element** |

Verified against `CslibTests/WitnessProbe.lean`:

- The `#eval check [(1,0),(2,1)]` is at **:177**. Line 174 is blank; :172-173 is the prose header.
- The `#guard_msgs` at **:175** asserts `some (true, false)` — **not** `some (true, true)`.
- `WitnessProbe.lean:172-173` states the **opposite** of the docstring: "The raw tree edges:
  upward-closed, and (post-repair) DOES falsify `phiRef1` at world `0` -- this is now itself a
  witness (`upwardClosed = true`, `evalF ... = false`)."
- `some (true, true)` lives at **:168**, and belongs to `#eval check []` — the **empty** frame.

**The deeper defect (not in the task description): the citation is off-target by kind.**
`WitnessProbe.check` computes `(upwardClosed b edges, evalF edges b 0 phiRef1)` — it measures
upward-closure and countermodel-falsification. It **never measures `IFimpAccess` at all**. Citing
it as evidence for an `IFimpAccess` refutation would be a category error even if the line numbers
and expected output were correct. Any repair that merely corrects `:174-176` → `:175-177` and
`(true, true)` → `(true, false)` leaves the paragraph asserting a non-sequitur.

### 2.3 Prescribed repair for Part 1

1. **Keep** the frame-adequacy table at `:9597-9601` verbatim.
2. **Keep** the headline verdict "`rawEdges` was, and remains, REFUTED … for `IFimpAccess`".
3. **Replace** the `WitnessProbe.lean` citation with the on-target evidence:
   `BetaSplitRefutation.lean`'s `fimpWitnesses = [1]` (the CI-protected fact that world 1 is the
   sole admissible witness) together with its raw edge list `[(1,0),(2,1)]`, plus the closing
   argument the module docstring already spells out.
4. **Retire** the "upward-closed but FORCES `phiRef1` at world 0" clause outright, or re-tense it
   as a PRE-REPAIR historical record. Post-repair the raw frame *is* `(true, false)` — a
   countermodel witness. That clause is now false in the present tense.
5. Apply the identical treatment at the duplicate, `:9732-9733`.

Companion citations in the same paragraph, verified:

| Docstring says | Actual |
|---|---|
| `BetaSplitRefutation.lean:304` = "the algorithm's real raw edge list" | `:304` is `phiRef3`'s docstring. Raw edge list is asserted at **:318-320** (and again at **:403-405**) |
| `:387` = "`branchesAgree = true`" | `:387` is inside `def fimpWitnesses`. `branchesAgree` is **defined at :377, asserted at :407-409** |

---

## 3. Part 2 — Present-Tense Claims Contradicted by Current Code

All seven confirmed. Corrections to the task description's line numbers are flagged **[corr]**.

### (a) Copy channel: "deliberately removed" vs. reinstated — CONFIRMED

`Scheme.lean:909-915` asserts in the present tense that the channel "**was deliberately
removed**" and calls Gap 1 "a **confirmed structural blocker**, not an unattempted proof".

`Expansion.lean:121-127` documents the channel as **reinstated and generalized**: "Also copies
every POSITIVE-signed formula `T(χ)@w` to every world `w'` accessible from `w` … (a generalized
reinstatement of the 'Deliverable 6' channel …). This subsumes the original self-copy channel …
as the special case `χ = φ → ψ`."

The section's own retraction, at `:967-984`, scopes itself to items **(i)-(ii)** only ("This
whole self-copy-channel analysis (i)-(ii) is now historical"). The `:909-915` paragraph sits
*above* (i)-(ii) and is not covered. Confirmed uncovered.

**Care point**: `Scheme.lean:921` contains a *verbatim quotation* of a historical commit
docstring (typeset in italics inside quotation marks), which itself uses present tense
("`truthLemma`'s T-imp `sorry` … is untouched by this change"). It is quoted historical
material, not an assertion in this file's voice. **Leave the quotation intact**; if anything,
strengthen its framing as a quotation. Do not re-tense text inside the quote marks.

### (b) "the `sorry` below" — CONFIRMED, span is wider than stated **[corr]**

`Scheme.lean:934` reads "it is not sufficient to close the `sorry` below". There is no `sorry`.
The paragraph continues in the present tense through **:944** ("nothing in this file currently
establishes"), not just to :940. The whole span **:930-944** needs re-tensing as a PRE-REPAIR
record.

`truthLemma` is declared at **:1005**, not :997 **[corr]**, and is proved.

### (c) `intExpMeasure_step_lt`, "not yet proved" — CONFIRMED

`Scheme.lean:4899` says "(`intExpMeasure_step_lt`, not yet proved)". It is proved at **:5097**.

### (d) "deferred to Phase 6" — CONFIRMED

`Scheme.lean:7296-7299`. The deferred result landed: `IAugMembers_persist` at **:7917**,
consumed in code at **:8598**.

### (e) `hUniv` directive — CONFIRMED, narrow it

`Expansion.lean:698-700`: "Do not attempt to prove `intExpandBranches_world_bound`, the `hnw`
hypothesis, or the `intUniverse` containment invariant (`hUniv`) as currently stated — they are
refuted, not merely hard."

- The `intExpandBranches_world_bound` / `hnw` half is **still correct** and must be preserved
  (the divergence witness at `Expansion.lean:690-697` still stands).
- `hUniv` now names **`IAllUniv`** (`Scheme.lean:3298`), which **is** threaded and discharged: it
  appears as a hypothesis in `intExpandBranches_openBranch_sat`'s signature, and
  `openBranch_countermodel` supplies it at **`Scheme.lean:9658-9663`** via `mem_intUniverseExt_of`.
  Note the correct span is :9658-**9663** **[corr]**, not :9658-9664 (:9664 is the `hnw`/`WBound_pos`
  argument, a different hypothesis).

**Repair**: split the directive. Keep the world-bound/`hnw` prohibition; strike `hUniv` from the
refuted list and record that the `IAllUniv` form is live and discharged.

### (f) `Minimal/DecisionProcedure.lean` self-contradiction — CONFIRMED

`:22-23` says "Sorry-free (see 'Notes on sorry' below for what still carries `sorryAx` one level
down)". `:45` says "This module is sorry-free, and so is everything it depends on." Nothing
carries `sorryAx`. Drop the parenthetical. (Task cited `:22-24`/`:47`; actual `:22-23`/`:45`
**[corr]** — a two-line shift, itself an instance of the very defect class.)

### (g) Dangling task-number reference — CONFIRMED, and it is a rules violation

`IntDecidability.lean:71-72` and `MinDecidability.lean:74-75` (identical text): "Factoring a
common truth-lemma abstraction is explicitly deferred (high risk, low payoff while 317 is open)."

Both files contradict this in their own headers:
- `IntDecidability.lean:323-325`: "the carriers remain structurally incompatible **regardless of
  either lemma's sorry status** … nothing in this dependency chain remains open."
- `MinDecidability.lean:292-294`: same text.

Per `.claude/rules/no-task-references-in-deliverables.md`, `Cslib/**` is a deliverable tree and
"317" must not be re-cited. Replace with a durable anchor. Recommended phrasing, mirroring the
files' own later wording: *"…is explicitly deferred: the carriers remain structurally
incompatible regardless of either lemma's sorry status, and the payoff is low (see the
`int_fin_truth_lemma` / `min_fin_truth_lemma` docstrings below for the full disposition)."* This
both removes the task number and makes the header agree with the body.

---

## 4. Part 3 — Docstrings Crediting Dead Declarations

### (h) `Minimal/Completeness.lean:58-61` — CONFIRMED, but the task's stated reason is wrong **[corr]**

The docstring attributes both live conjuncts to
`openBranch_rawEdges_upward_closed` / `openBranch_rawEdges_both_upward_closed`.

The task description asserts "Both have ZERO non-docstring references". **That is false for the
first one.** Reference census over `Cslib/` + `CslibTests/`:

| Declaration | Declared | Non-docstring references |
|---|---|---|
| `openBranch_rawEdges_upward_closed` | `Scheme.lean:9736` | **One**: consumed at `Scheme.lean:9818`, inside its sibling's proof |
| `openBranch_rawEdges_both_upward_closed` | `Scheme.lean:9809` | **Zero** — terminal dead end |

So the accurate framing is: the pair forms a self-contained, retained-but-dead sub-tree — the
first lemma is alive only as the second's feeder, and the second has no consumer at all. Neither
is on the live route.

The live route is `hpersAug` over the **augmented** frame (`Scheme.lean:9686-9711`), and
`Scheme.lean:9725-9727` already says so explicitly. Copy that framing into
`Minimal/Completeness.lean:58-61`.

**Do not write "zero references" for `openBranch_rawEdges_upward_closed`** — that would replace
one false claim with another.

### (i) `minOpenBranch_countermodel` credited as feeding `minimalTableau_complete` — CONFIRMED

`Minimal/Completeness.lean:137-138` ("`minimalTableau_complete` below needs nothing further from
this lemma") and `:164-166` ("`openBranch_countermodel`'s own existential … (`minOpenBranch_countermodel`'s
delegate above)") imply a dependency that does not exist.

The proof at `:170-175` is:
```
apply tableau_complete minScheme
intro edges _b _huc _hbuc
exact @h Nat (intAccessPreorder edges) ...
```
It calls `tableau_complete minScheme` directly and never mentions `minOpenBranch_countermodel`.

**Nuance for the repair**: `:164-166`'s *first* clause is defensible — `minimalTableau_complete`
genuinely does rest on `openBranch_countermodel`'s existential, just routed through
`tableau_complete minScheme` rather than through `minOpenBranch_countermodel`. Only the
parenthetical attribution is wrong. Repair the parenthetical, keep the sentence.

Reference census confirms `minOpenBranch_countermodel` has **zero** non-docstring consumers.

**Model framing to copy** — `Intuitionistic/Completeness.lean:119-121`, which handles the exact
twin correctly:
> "(Postmortem-5 revision: this internal corollary has no live consumer beyond docstrings, so
> exposing `edges` here does not touch the stable public contract)."

---

## 5. Part 4 — Stale Line Numbers

**Census**: 65 file-and-line citations across the six in-scope files (`Scheme.lean` 20,
`FmpMeasure.lean` 23, `Rules.lean` 9, `Expansion.lean` 8, `Completeness.lean` 4,
`WitnessProbe.lean` 2, `BetaSplitRefutation.lean` 1), plus a further set of bare `:NNN` forms
inside `Scheme.lean` that the file-qualified grep does not catch (at least 8 of these are also
stale — see Section 7).

Every claim in the task description was resolved against its target. Corrected table:

### 5.1 `Scheme.lean` self-references

| Citing site | Cites | Resolves to | Correct target |
|---|---|---|---|
| `:893`, `:1035` **[corr]** (task said :126, :895) | `:105-108` for `sat_timp` | prose | `sat_timp` is a field of `IBranchSaturation`, at **:127** |
| `:834` | `:897-967` for `IExpandedConsistent_sat` | prose | **:1303** |
| `:870` | `Scheme.lean:5335` for `applyAllTImpRules_eq_self_of_length_eq` | `IAllFuel` prose | **:5942** |
| `:871` | `Scheme.lean:5386` for `applyPersistenceFixpoint_genuine_of_count_le_fuel` | `IAllConsistent_map` prose | **:5993** |
| `:912` | `:3444` (same lemma; self-hedged "at time of writing") | — | **:5993** |
| `:597`, `:682` | `Scheme.lean:250` / `:250-257` | `minScheme`'s docstring | `minScheme` is at **:256**; the intended anchor is the one-hop-soundness note |
| `:653` | `Scheme.lean:3272` | a section-header line | — |
| `:3587` | `Scheme.lean:451` for `isAccessible_one_hop_ext` | proof interior | **:657** |
| `:4087`, `:9719` | `Scheme.lean:6701-6704` for `IPosPersistRaw` | proof interior | **:7283** |
| `:4111` | `Scheme.lean:7058` | induction boilerplate | — |
| `:5702` | `Scheme.lean:485-533` for the STOP gate | `by_cases hp : p == current` | the STOP-gate section runs ~**:801-984** |
| `:7835` | `Scheme.lean:1078-1089` for `IExpandedAccessConsistent` | proof interior | **:1234** |

### 5.2 `Rules.lean` references (all shifted forward)

| Citing site | Cites | Resolves to | Correct target |
|---|---|---|---|
| `Scheme.lean:126` | `Rules.lean:274-275` for the T-imp branching arm | a comment line | **:279-280** |
| `Scheme.lean:763`, `:827`, `:894` | `Rules.lean:245-268` for `intApplyRuleFull` | `IntRuleResult`'s `branchingResult` ctor | `intApplyRuleFull` is at **:250**; its `.pos,.imp` arm at **:279-280** |
| `Scheme.lean:2341` | `Rules.lean:262-264` for the `.neg/.imp` arm | the `.pos,.or` arm | **:266-269** |
| `Scheme.lean:2346` | `Rules.lean:126` / `:139-141` / `:174-186` for `posFormulasAt` / `propagatePersistence` / `intTImpRule` | `IntTableauState` field | **:131** / **:144** / **:179** |
| `Scheme.lean:5148` | `Rules.lean:254,260` | `:254` = `-- T(φ ∧ ψ): alpha-rule` | `.neg,.and` (F-and) at **:257-258**; `.pos,.or` (T-and → actually T-or) at **:261-262** |

**Label-swap confirmed** at `Scheme.lean:5148`: the prose labels are inconsistent with the signs
given. `:257-258` is `.neg, .and` = **F-and**; `:261-262` is `.pos, .or` = **T-or**. Both the
line numbers *and* the labels need correcting there.

### 5.3 `Expansion.lean` reference

`Expansion.lean:514-516` cites `Expansion.lean:256-264` for the Option-B unsoundness note.
`:256` resolves to `if expanded.any (· == sf) || isWorldCreating sf then none` — the tail of
`intStepBranch` / start of `intStepBranchPrio`'s docstring, not an unsoundness note.

### 5.4 Internal numbering contradiction — RESOLVED, "7th" is correct

`Scheme.lean:745` says "11th conjunct"; `:9562` says "7th". Verified against the statement of
`intExpandBranches_openBranch_sat` at **:8340-8344**:

```
∃ (edges rawEdges lbEdges : IEdges) (nwF : Nat),
  IBranchSaturation ∧ IFimpAccess ∧ IPosPersistRaw ∧ IReuseContain ∧
  ForestComparable ∧ IWorldsPlanted ∧ (χ-general persistence)
```

Four existential witnesses, then **seven** conjuncts. `hpersAug` is the **7th conjunct**.
"11th" counts obtain-pattern slots (4 + 7), not conjuncts. **Fix `:745`, keep `:9562`.**

### 5.5 `FmpMeasure.lean` cross-module references (lowest priority)

Roughly 23 citations, drifting 3-5 lines. Verified anchors:

| Symbol | Cited as | Actual declaration |
|---|---|---|
| `modalSubfmls` | `:73-80` (`Scheme.lean:2299`) | **:75** (`:73` is its docstring opening — arguably intentional) |
| `modalUniverse` | `:149-152` (`Scheme.lean:2369`) | **:153** — `:149-152` lands inside `modalWorldBound` **[corr: task said 155]** |
| `modalWork` | `:190-193` (`Scheme.lean:4897`) | **:197** — and `Scheme.lean:4905`, eight lines later, cites `:197-200` **correctly**, so the file is internally inconsistent about the same symbol |

The remaining `FmpMeasure.lean` citations (`:266-754`, `:393-427`, `:432-437`, `:443-448`,
`:453-458`, `:463-468`, `:253-260`, `:669-754`, and the `:2440`–`:2937` cluster) mostly land
inside or adjacent to their intended targets. They are the lowest-value part of the pass; treat
as optional.

---

## 6. Verified Accurate — Confirmed, Do Not Touch

Independently re-confirmed during this research:

- The "PRE-REPAIR (historical)" blocks at `Scheme.lean:742-750`, `:755`, `:814-820`, `:841-845`,
  `:867-892`, `:898-904`, `:976-984`, `:1041-1052`, `:3284-3292`, `:9590-9601`, and
  `Expansion.lean:525-555` — all correctly re-tensed.
- The dead-code retention claims at `Scheme.lean:2385-2388` and `:9725-9735`.
- `Intuitionistic/Completeness.lean:119-121` — the model framing for Part 3(i).
- The `intUniverse`/`hnw` refutation at `Scheme.lean:2372-2388` and `:2887-2895`.
- **Newly confirmed accurate**: `Scheme.lean:758`'s citation of `Kripke.lean:145-148` for
  `IValid`'s upward-closure hypothesis. `def IValid` is at `Kripke.lean:145`, its hypothesis at
  `:147`. Leave it alone.
- **Newly confirmed accurate**: `Scheme.lean:9645-9665` (the `hpersAug` anchor, cited 8 times).
  The `obtain` block runs :9650-9684; the cited range covers the comment and the extraction
  head. Imprecise but not misleading — low priority, and consistent across all 8 sites.

---

## 7. Siblings the Task Description Missed

The task explicitly asks to "check for siblings it also missed". Six were found:

| # | Site | Defect | Class |
|---|---|---|---|
| S1 | `Minimal/DecisionProcedure.lean:49-51` | Credits `minOpenBranch_countermodel` with "now supplies both of `MValid`'s upward-closure conjuncts together" — the same false dependency as Part 3(i), in a second file | Part 3 |
| S2 | `Scheme.lean:5345` | Cites `Scheme.lean:1211` for `IAllConsistent`; actual **:2105** | Part 4 |
| S3 | `Scheme.lean:469` | Cites `:316` for `isAccessible_go_append_mono`; `:316` is `structure IntMinScheme`, actual **:353** | Part 4 |
| S4 | `Scheme.lean:2289` and `:2396` | Both cite `Expansion.lean:462-463` for a fuel pre-sizing bound; `:462-463` is `intStepBranchPrio_newEdge_frozen`'s docstring — off-target, and duplicated | Part 4 |
| S5 | `Scheme.lean:9603-9611` | The `WitnessProbe` citation is off-target **by kind**, not only by line — `check` measures upward-closure/falsification, never `IFimpAccess` (§2.2) | Part 1 |
| S6 | `Scheme.lean:930-944` | The present-tense span for Part 2(b) extends to :944, not :940 | Part 2 |

S1 is the most consequential: it means Part 3(i) is a two-file defect, and repairing only
`Minimal/Completeness.lean` would leave the contradiction alive in `DecisionProcedure.lean`.

---

## 8. Recommendation on the CONSIDER Item: Declaration Names over Line Numbers

**Recommendation: adopt declaration-name citation as the convention for intra-repository
references, and convert opportunistically — but do NOT perform a repo-wide migration under this
task.**

Rationale, grounded in what this research measured:

1. **The defect rate is the argument.** Of the citations resolved here, the large majority in
   `Scheme.lean` and `Rules.lean` were stale. A `Scheme.lean` of ~9,884 lines guarantees that any
   line-number citation decays on the next insertion above it. Nothing in CI checks them.
2. **Declaration names are machine-checkable at zero cost.** A grep-based lint (`for each
   \`Foo\` cited in a docstring, assert Foo is declared somewhere in Cslib/`) is a few lines of
   shell and would make the entire defect class impossible rather than recurrent. Line-number
   citations admit no such check.
3. **Lean tooling already resolves names.** Backticked identifiers are hoverable/jumpable in any
   Lean LSP client; `Foo.lean:1234` is not.
4. **Precedent exists in-tree.** Most `Scheme.lean` cross-references *already* name the
   declaration and merely append a line number — e.g. "(`applyAllTImpRules_eq_self_of_length_eq`,
   `Scheme.lean:5335`)". The name carries the meaning; the number carries only the rot. **The
   cheapest correct convention is: keep the name, drop the number.** For most sites this is a
   deletion, not a rewrite, which makes it far safer than renumbering.
5. **Where a line number is genuinely needed** — pointing into a proof interior or a
   `#guard_msgs` assertion with no name — cite the enclosing declaration plus a distinctive
   quoted phrase (e.g. "`openBranch_countermodel`'s `hpersAug` extraction") rather than a number.

**Scope guidance for the planner**: within this task, apply "keep the name, drop the number" to
the sites it is *already* repairing (Parts 1-3 and the Part 4 sites enumerated in §5.1-5.4). Do
not touch the ~23 `FmpMeasure.lean` citations for convention reasons alone. A repo-wide migration
plus the grep lint should be a separate, follow-on task.

This is a recommendation, not a decision — as the task instructed, it is reported for the user's
call.

---

## 9. Suggested Phase Decomposition

Ordered by the task's own priority, sized so each phase is one agent run and independently
verifiable:

| Phase | Content | Files |
|---|---|---|
| 1 | Part 1: rewrite `:9603-9611` and `:9732-9733`; keep table and verdict; retarget to `BetaSplitRefutation.lean` evidence; fix the two companion citations | `Scheme.lean` |
| 2 | Part 2 (a)(b): re-tense `:909-915` and `:930-944` as PRE-REPAIR; leave the `:921` quotation intact | `Scheme.lean` |
| 3 | Part 2 (c)(d)(e): `:4899`, `:7296-7299`, and narrow the `Expansion.lean:698-700` directive | `Scheme.lean`, `Expansion.lean` |
| 4 | Part 2 (f)(g): drop the `sorryAx` parenthetical; replace the task-number reference with a durable anchor in both decidability files | `Minimal/DecisionProcedure.lean`, `IntDecidability.lean`, `MinDecidability.lean` |
| 5 | Part 3 (h)(i) **plus sibling S1** | `Minimal/Completeness.lean`, `Minimal/DecisionProcedure.lean` |
| 6 | Part 4 §5.1-5.4 plus siblings S2-S4; apply "keep the name, drop the number" | `Scheme.lean`, `Expansion.lean` |
| 7 | Optional: `FmpMeasure.lean` citations (§5.5) | `Scheme.lean` |

Phases 1-6 are the committed scope; Phase 7 is explicitly optional and low value.

---

## 10. Verification Protocol

Because this is documentation-only, the gate is that **nothing but comments changed**:

1. **Statement-invariance check** (the primary gate):
   ```
   git diff -U0 -- Cslib/ | grep '^[+-]' | grep -v '^[+-][+-]' | grep -v '^[+-] *--' | grep -v '^[+-] *\/-'
   ```
   Any surviving line that is not inside a `/-! -/` or `/-- -/` block is a scope violation.
   Equivalently, confirm every hunk lies within a docstring or comment region.
2. **Build green**:
   `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure Cslib.Logics.Propositional.Metalogic.IntDecidability Cslib.Logics.Propositional.Metalogic.MinDecidability`
   Baseline established during this research: **successful, 967 jobs**, with one pre-existing
   `unusedDecidableInType` warning at `Minimal/DecisionProcedure.lean:173` (unrelated; must
   neither be fixed nor newly introduced elsewhere).
3. **Full build** at the end: `lake build`.
4. **Tests unchanged**: `lake test` — `CslibTests/` is out of scope and must not be edited. The
   `#guard_msgs` assertions in `WitnessProbe.lean` and `BetaSplitRefutation.lean` are the ground
   truth this task cites; changing them would invert the evidential direction.
5. **Text lint**: `lake exe lint-style` (line-length limits apply to docstrings).
6. **Task-number lint**: after Phase 4, confirm no task-number citation remains in `Cslib/`:
   `bash .claude/scripts/check-task-references.sh` (or grep for `\b317\b` in the two decidability
   files).
7. **Re-resolve the corrected citations**: re-run the resolution sweep from §5 and confirm each
   repaired citation now lands on its named declaration.

---

## 11. Zero-Debt and Standards Compliance

- **No `sorry`, no axioms, no vacuous definitions** are involved: this task adds none and removes
  none. The tree is already sorry-free, which is precisely why the stale `sorry`-referencing
  prose is a defect.
- **No new abstractions** are proposed, so the CSLib reuse-first check is satisfied vacuously.
- **`no-task-references-in-deliverables.md`**: Part 2(g) is a live violation of this rule inside
  `Cslib/**` and must be repaired with a durable anchor, not a re-citation. The planner and
  implementer must not introduce task numbers into any `Cslib/**` file when writing the new
  prose.
- **`plan-compliance.md`** applies (`**/*.lean`): the implementer must execute the plan's phase
  sequence and escalate rather than substitute.
- **No blocked-tool usage**: `lean_diagnostic_messages` and `lean_file_outline` were not called.

---

## 12. Residual Uncertainty

- The `FmpMeasure.lean` citation cluster in the `:2440`-`:2937` range was spot-checked, not
  exhaustively resolved. If Phase 7 is undertaken, that sweep should be completed first.
- Bare `:NNN` citation forms inside `Scheme.lean` (as opposed to `File.lean:NNN`) were sampled,
  not exhaustively enumerated; at least 8 are stale (§5.1, S2, S3). A complete sweep would use
  `grep -on ':[0-9]\{3,4\}' Scheme.lean` and resolve each.
- `:5702`'s intended STOP-gate anchor (~`:801-984`) is an inference from the section structure;
  the implementer should confirm the exact intended section before renumbering, or — preferably —
  replace it with the section heading name and drop the number entirely.
