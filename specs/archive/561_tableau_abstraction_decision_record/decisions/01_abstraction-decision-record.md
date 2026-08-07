# Decision Record: Modal Tableau Abstractions, Boneyard Eligibility, Module Seams

- **Record**: `01_abstraction-decision-record.md`
- **Task**: 561 — `tableau_abstraction_decision_record` (REVIEW GATE)
- **Date**: 2026-07-26
- **Session**: `sess_1785105096_50f3c7`
- **Status of this record**: COMPLETE — awaiting reviewer sign-off (see §12)
- **Evidence base**:
  - `specs/557_modal_tableau_refactor_abstractions_boneyard/reports/01_tableau-abstraction-boneyard-analysis.md`
    (hard-mode analysis; `### Claim Verification Table` at `:987`, 49 re-verified rows —
    38 CONFIRMED, 9 REVISED, 2 REFUTED)
  - `specs/557_modal_tableau_refactor_abstractions_boneyard/plans/01_tableau-refactor-abstractions-boneyard.md`
    (reference document; Phase 1 body at `:357-399` is this record's specification; the
    **Corrected Figures** table at `:54-60` is transcribed below)
  - `specs/557_modal_tableau_refactor_abstractions_boneyard/artifacts/baseline.md`
    (measured baseline at commit `7eb51f69`, every row carrying its reproduction command)
- **Scope of this record**: decision-recording only. **No `.lean` file is created, moved, or
  edited by this task.** No abstraction is implemented here. This record is the gate that must be
  ACCEPTED before any implementation task in the programme (562-567) may move, split, or
  restructure a file.

Where this record and the pre-verification prose of report 01 disagree, **this record follows the
report's Claim Verification Table**, which was produced by a later adversarial pass against the
tree at `ff315ea5`. Where the Claim Verification Table and the plan's Corrected Figures table
agree, the figure is binding on every downstream task.

---

## 1. Build Gate — recorded, and NOT this programme's to repair

**The repository does not currently build.**

```
error: Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean:1329:2: Missing cases:
_, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)
error: Lean exited with code 1
Some required targets logged failures:
- Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness
error: build failed
```

Reproduce with `lake build 2>&1 | tail -20` and `lake exe checkInitImports; echo "exit=$?"`.

Recorded facts, all binding:

1. The failure is a **genuine compile error**, not a stale artifact. The missing
   `Nested/Soundness.olean` is a *consequence* of the error, so `lake exe checkInitImports`
   cannot be cleared by rebuilding.
2. Provenance: the file was last touched by commit `88b198bf` ("task 554 phase 13.1 … assemble
   nested_sound with impL strategic sorry"). It is committed work on the constructive
   nested-sequent subsystem, **outside the modal Tableau subsystem and outside this programme's
   territory**. Ownership sits with tasks 554 and 570.
3. **Every downstream acceptance gate in this programme that reads "`checkInitImports` clean" is
   currently vacuous.** Verification gate V6 is not established; a gate that reads
   `checkInitImports` today verifies against nothing. Tasks 562-567 must treat V6 as unmet until
   the owner clears it, and must not report a green V6 on the strength of a command that fails
   for an unrelated reason.
4. **This programme MUST NOT repair it.** No `sorry` may be added to it, no revert of `88b198bf`
   may be attempted, and no phase of tasks 557-567 may edit
   `Cslib/Logics/Modal/Metalogic/Constructive/Nested/`.
5. **This decision record is build-independent and is therefore valid now.** Every input it
   adjudicates is a source-text measurement or a literature reading; none requires an elaborated
   environment. Acceptance of this record is not blocked by the build gate.

The one downstream figure that *does* depend on a green build is flagged in §2.6.

---

## 2. Binding Figures

### 2.1 Corrected Figures (transcribed verbatim from the plan's Overview, `:54-60`)

These supersede report 01 where they differ.

| Figure | Report 01 says | Corrected value | Consequence for this plan |
|---|---|---|---|
| Local re-derivation sites | 77 | **55** exact-phrase occurrences (`grep -rho 'Local re-derivation' Cslib/ \| wc -l`) | The headline count is smaller, but **every per-lemma spot-check was an UNDERCOUNT**: `modalSubfmls_trans` 4x not 3x, `modalKnownWorlds_fold_spec` 6x not 4x, `hasEdge_addEdge_cases` 7x not 4x. Report 01's per-file distribution **omits `LoopChecking.lean`'s 14 sites** entirely. The Scope B extraction work is therefore **larger**, not smaller, than stated. |
| `hasEdge_addEdge_cases` origin | `FmpMeasure.lean` (implied by §7 Seam 1) | **`Soundness.lean:75`** (with a separate `hasEdge_addEdge_cases_local` at `FmpMeasure.lean:1063`) | Phase 6 must extract from **two** source files, not one. |
| `ModalTableauResult` module span | 11 Tableau modules | **8** Tableau modules (9 repo-wide) | The task description's original figure of 8 was correct; report §2's "measured 11" row is drift. **Correct it back in the recorded baseline (Phase 2).** |
| `keysOriginS4` consumers | 22 | **not reproducible as 22**; measured 61 textual references, 55 on non-comment-leading lines | **Conclusion unchanged, with a large margin**: not zero-consumer, therefore not Boneyard-eligible, therefore `LoopChecking.lean:2001-2002`'s removal claim is FALSE and must be corrected (Phase 26). |
| `S4LoopInv` structure header | `:7072` | **`:7070`** | `outDegEq` field line `:7084` and all three provision sites (`LoopChecking.lean:7569`, `:7633`, `FrameCompleteness.lean:4217-4218` positional anonymous constructor) are **exact**. |

### 2.2 `ModalTableauResult` spans **8** Tableau modules — binding

The span is **8** modules under `Cslib/Logics/Modal/Tableau/`, **9** repo-wide (the ninth is
`CslibTests/S4LoopGuardRegression.lean`). Report §2's "measured 11" row is **drift**; the task
description's original figure of **8 was right** and is hereby restored as the binding figure.

```bash
grep -rl 'ModalTableauResult' --include='*.lean' Cslib/Logics/Modal/Tableau/ | wc -l   # 8
grep -rl 'ModalTableauResult' --include='*.lean' . --exclude-dir=.lake | sort           # 9 modules
```

The 8: `BDriver.lean`, `CompletenessLoop.lean`, `FiveSimplification.lean`,
`FrameCompleteness.lean`, `LoopChecking.lean`, `S5Simplification.lean`, `Saturation.lean`,
`TDriver.lean`. A tenth textual hit under `specs/553_.../artifacts/s4driver.lean` is a task
artifact, not a repository module, and is excluded from the span.

### 2.3 Re-derivation sites: **55**, and the de-duplication work is LARGER, not smaller

The exact phrase `Local re-derivation` occurs **55** times, not 77
(`grep -rho 'Local re-derivation' Cslib/ | wc -l`). Broader patterns give different figures again
(`-i 're-derivation'` → 80; `-i 're-deriv'` → 106), so **77 is not reproducible by any obvious
command** and is retired as a figure.

**The headline count going down does not mean the work went down. It went up.** Three
independent corrections, all in the same direction:

| Correction | Report 01 | Measured | Effect |
|---|---|---|---|
| `modalSubfmls_trans` re-derivations | 3 files | **4** — `BDriver.lean:211` (`_B`), `S5Simplification.lean:97` (`_S5`), `FiveSimplification.lean:738` (`_Five`), **`LoopChecking.lean:1576` (`_S4`)**; original private at `FmpMeasure.lean:393` | +1 site |
| `modalKnownWorlds_fold_spec` re-derivations | 4 files | **6** — `BDriver:918`, `S5Simplification:993`, `LoopChecking:2757`, `FrameSoundness:2032`, `FrameCompleteness:3745`, `FiveSimplification:777` (plus a second S5 site at `:1051` re-deriving its *proof*); original at `FmpMeasure.lean:1710` | +2 sites |
| `hasEdge_addEdge_cases` re-derivations | 4 files | **7** — `BDriver:906`, `LoopChecking:5323`, `FmpMeasure:1063` (`_local`), `FrameSoundness:1199` (`_anc`), `FrameSoundness:2109` (`_FS`), `FrameCompleteness:2919` (`_Five`), `FrameCompleteness:3842` (`_C`) | +3 sites |

Two further facts, both binding on task 558:

- **The distribution omits `LoopChecking.lean`'s 14 sites.** Measured per-file:
  `S5Simplification.lean` 14, **`LoopChecking.lean` 14**, `FiveSimplification.lean` 10,
  `FrameSoundness.lean` 6, `BDriver.lean` 6, `FrameCompleteness.lean` 5 — total **55**. The
  omitted file is the largest in the subsystem and one of the three the programme targets for
  splitting.
- **Extraction must draw from TWO source files.** `hasEdge_addEdge_cases` originates in
  **`Soundness.lean:75`**, not `FmpMeasure.lean` (which carries only a separate
  `hasEdge_addEdge_cases_local` at `:1063`). Any extraction task scoped to `FmpMeasure.lean`
  alone is mis-scoped.

Recorded conclusion, binding: **the de-duplication work is larger than the original 77 figure
implied, not smaller.** A downstream dispatch that reads "55 instead of 77" as a scope reduction
has misread this record.

### 2.4 Other measured figures adopted as binding

| Fact | Measured | Note |
|---|---|---|
| `LoopChecking.lean` | 10,540 lines / 230 declarations | exact |
| `FrameSoundness.lean` | 5,317 lines | exact |
| `FrameCompleteness.lean` | 4,307 lines | exact |
| Three-file total | 20,164 lines | exact |
| `hintikkaS4_*` bridge set | **8** declarations, at `:6626, :6712, :6804, :6887, :6972, :6984, :7008, :7024` | a *distinct-identifier* count returns 11; that is a mention count, not a bridge count |
| Tableau sorry census | **1**, at `FrameSoundness.lean:1244` | the retained, user-decided sorry |
| Repo-wide code-position sorry census | **29** | recorded as measured, not reconciled to the plan's 10; the CI-pipeline grep returns 158 (it catches docstring prose) and the build's `declaration uses 'sorry'` warning count of 5 is an **undercount** from incremental caching and must not be used as a census |
| Tableau axiom declarations | **0** (3 raw word matches) | the "26 vs 47" discrepancy was a **scope confusion**, not a drift |
| Repo-wide `Cslib/` axiom declarations | **26** (1,701 raw word matches) | fix drift by recording the measured baseline with its command, never by adjusting a number |
| Tag census in the three files | 0 FIX / 0 NOTE / 0 TODO / 0 QUESTION | 11 TODO / 8 NOTE repo-wide |
| `CslibTests/S4LoopGuardRegression.lean` | 197 lines | exact |
| `Boneyard/` | **absent** at the repository root | must be created by task 566 |
| `FmpMeasure.lean` private declarations | **50** | the root cause of the re-derivation debt |

### 2.5 Figures explicitly NOT verified

The two amplification figures — **4 declarations / 1,036 lines** and **43 declarations / 1,983
lines reachable from `modalTableauS4Keyed_complete`** — were **not re-measured**, and **no
substitute was fabricated**. They require a transitive-dependency query over the elaborated
environment, which requires built `.olean`s, which requires the build gate of §1 to clear. Any
downstream task depending on either figure must re-measure it after §1 clears, or state
explicitly that it relies on an unverified report-01 inheritance.

The qualitative claim these figures were offered in support of does **not** depend on them: it
stands on the verified 4-clause / 14-line redirect semantic surface plus the 85 private lemmas in
`LoopChecking.lean` and 50 in `FmpMeasure.lean`.

### 2.6 Literature-index defect — located, out of territory

The per-repo sub-index `specs/literature-index.json` is **reference-only** (34 entries, each
`doc_id` + `relevance`) and stores no chunk counts, so the premise that the "Massacci reports as 1
chunk" defect lives there is **incorrect**. The root cause is
`.claude/scripts/literature-briefing.sh:203-206`, which derives a chunk count by counting child
entries with `parent_doc` set in the **global** `~/Projects/Literature/index.json`, falling back
to `chunk_count=1` at `:224`. Massacci has 77 chunk files on disk and `chunk_count: 77` on its
parent entry, but **0** child entries. **19 of the 34** sub-index documents under-report for the
same reason, spanning **848** chunk files. Repair belongs to task 560 and touches the user's
global corpus or the script, not this repository's sub-index.

---

## 3. Retired Premises (a)-(d) — BINDING, NON-REINSTATABLE

The following four premises are retired. No dispatch under tasks 557-567, and no dispatch under
the downstream consumers named in §11, may reinstate them or build an inference on them. Each was
independently re-checked for silent dependence in the Claim Verification Table
(rows "Retired premises (a)-(d)", all **CONFIRMED ABSENT**).

**(a) There is no theorem numbered "interval theorem."** `chunk_0246.md:43-65` (print p. 141) is
unnumbered prose following Theorem 5.23, and an **unproved authorial remark** with no
counterexample frame supplied. Its finest and coarsest relations live on the filtration
**quotient**, so its nontransitivity sentence — accurate as a quotation — is **not** precisely the
failure mode of a subtractive or redirect-channel design. Cite it by chunk and print page, never
as a theorem or proposition, and build no inference on it.

**(b) `Massacci2000` Theorem 8.1 (blocking preserves satisfiability) is STATED AND NEVER PROVED
there.** Appendix B.2 proves only Theorem 8.4, and §10.2 defers 8.1 to Goré's model graphs
(`chunk_0054.md:3-7`). The four dead soundness routes were reconstructing a proof their cited
source does not contain. This belongs in `FrameSoundness.lean`'s documentation (task 559,
documentation defect 4) and must **not** be relied on as an established result.

**(c) Theorem 5.51 concerns Grz via SELECTIVE filtration, not S4 via filtration.** It may be used
only for its *containment-by-construction pattern* (`S_{n+1} ⊆ R_Grz` discharging (HSm1)
immediately), which is a structural analogy. The S4 licence throughout is **Corollary 5.32**, not
5.51.

**(d) Box-plus is defined in Chapter 3** (`chunk_0173.md:11-14`, print p. 98) as the syntactic
analogue of **reflexivization** — **not** in `chunk_0248`, which holds the Lemmon filtration
itself (`:24-31`, print p. 142, also unnumbered). Cite `chunk_0173` for `□⁺` and `chunk_0248` for
the Lemmon filtration; never fabricate a definition number for either.

**Citation-safety rules carried forward as binding**: the Lemmon filtration and `□⁺` are both
unnumbered in `ChagrovZakharyaschev1997` — cite by chunk line and print page. The OCR mangles
modal symbols consistently (`□`→`D`/`U`/`E`, `◇`→`O`/`0`, `φ`→`p`, overlines on `S` lost, so
`S C S C 5` is `S̲ ⊆ S ⊆ S̄`); any quotation must flag its reconstruction. `Blackburn2001` carries a
doc_id/BibKey mismatch (corpus `blackburn_2002`). `ArisakaDasStrassburger2015` is
`[UNVERIFIED - provenance_fidelity: unadjudicated]` and is excluded.

---

## 4. Decision D1 — Report §3, the edge-vs-identification diagnosis: **ACCEPT (diagnostic only)**

**Verdict: ACCEPT** as the programme's recorded primary finding, **with the explicit standing that
it is diagnostic only and that nothing in this programme implements a repair for it.**

**Rationale.** The finding is that the mis-factoring is *edge-addition where both source calculi
identify worlds*: a blocked minting step in `modalApplyOneS4Keyed` returns
`(.linear [], acc.addEdge sf.label wBlock)` at exactly two lines (`LoopChecking.lean:753` and
`:757`), and that edge is consumed by two mutually incompatible model notions — completeness
*constructs* its model (`extractModelS4 b acc = extractModelWith Relation.ReflTransGen b acc`,
`FrameCompleteness.lean:143-146`, where an extra edge is simply an extra edge) while soundness
*quantifies existentially* (`branchSatisfiableIn`, `FrameSoundness.lean:110`, where an extra edge
is a new obligation `m.r (f src) (f wBlock)` against a model nobody constructed). Both source
calculi avoid the edge: `Massacci2000` Definition 10.2's SST-interpretation is explicitly **not**
required injective (the blocked world is *identified* with its shorter modal copy), and Pruning
Lemma 8.2 *deletes* the descendant-closed subtree `Ftree(σ.n)`; `ChagrovZakharyaschev1997`
Theorem 5.51 discharges the same condition by building its relation **inside** the ambient one.
Every anchor re-resolved exactly under the Claim Verification Table — the two edge-addition lines,
the `:491-493` "**No reachability restriction**" docstring, the `FrameSoundness.lean:1183-1190`
mechanism note, and the `extractModelS4` / `branchSatisfiableIn` pair — all CONFIRMED. The finding
is accepted because it is fully evidenced and because it correctly relocates the defect away from
the bridge set. It is accepted as *diagnosis* because a repair requires the non-injective-`f`
mechanism, which is a soundness-design question this programme is forbidden to attempt (task
557's description: "It is NOT a soundness-proof task and must not attempt the soundness
obligation"). **Binding consequence: no task 557-567 dispatch may implement, prototype, or take a
"small preparatory step" toward a repair of this defect.** Its only implementation surface in this
programme is documentation (task 559).

---

## 5. Decision D2 — Report §4, box-plus birth keys: **ACCEPT (scoped down as stated)**

**Verdict: ACCEPT** the Lemmon box-plus pairing at the **birth-key level** — `boxPlusPair`,
`BoxPlusClosed`, and an enriched `successorBirthContent` emitting both members of each pair —
**with the scoped-down expectation stated in §5.1 as part of the decision, not as a caveat to it.**

**Rationale.** The defect is exact and three lines wide: `successorBirthContent`
(`LoopChecking.lean:384-393`) records only the **unwrapped** `(pos, ψ)` when `T(□ψ)@w` is on the
branch, while `relevantSetFinset` records **both** forms — and that asymmetry *is* the
wrapped/unwrapped mismatch, verbatim the obstruction recorded at `LoopChecking.lean:8830-8832`
("the free transfer below … yields only an *unwrapped* branch fact at the redirect target, and
unwrapped facts have no persistence mechanism in this tableau's Hintikka apparatus"). The
literature supplies exactly the missing mechanism: `y ⊨ □⁺φ = φ ∧ □φ` delivers both the local
truth of φ and the persistence of `□φ`, so the constraint re-propagates along a further S-step,
whereas `y ⊨ φ` alone is not composable (`chunk_0248.md:9-16`, print p. 142). S4 is licensed **by
name** — Corollary 5.32 names K4, D4 and S4 as admitting filtration via the transitive closure of
the finest filtration **or the Lemmon filtration**. And it is **free in the world bound**:
`modalSubfmls (.box a) = .box a :: modalSubfmls a` (`FmpMeasure.lean:79`, CONFIRMED verbatim)
keeps the enriched key inside the existing codomain `signedSubfmls φ₀`, leaving
`signedSubfmls_card_le`, `signedSubfmls_powerset_card_le`, `modalWorldBoundS4` and the pigeonhole
argument **untouched**. The single path by which it could have cost anything — iteration of `□⁺`
beyond depth 1 — is closed **negatively** from the source: the source never iterates `□⁺`; where
more discriminating power is needed it enlarges the **filter** Σ instead (Thms 5.34/5.35), which
*would* change the codomain and *is* expensive. Six documented counterarguments (C1 GL hard
failure, C2 bigger-filter, C3 canonical-model, C4 transitivity precondition, C5 ad-hocness, C6
iteration depth) were each checked against S4's situation and **none blocks adoption**; C1 in
particular puts S4 on the safe side of the dividing line for exactly the reason that makes it safe
(S4 *wants* reflexivity, which condition (iii) preserves). Prior art exists at the rule level twice
(`modalFourBoxProp`, `FrameRules.lean:133-138`; `boxDiamondPersistence`,
`Bimodal/…/Tableau.lean:345` — note the report's `:344` is the docstring's closing `-/`, STALE
off-by-one) and at the soundness-invariant level once (`MonotoneEdges`,
`Intuitionistic/Soundness.lean:367-369`). What is genuinely missing for this repository is
box-plus at the **key / equivalence-class** level, and that is what is adopted.

### 5.1 Scoped-down expectation — part of the decision, binding

- **Box-plus subsumes NONE of the 8 bridges outright.** It collapses **at most 2**: the reflexive
  instances `hintikkaS4_box_pos_self` (`:6804`) and `hintikkaS4_dia_neg_self` (`:6887`). The other
  six are not adapters around a badly-factored predicate — `_box_pos_step` (`:6626`),
  `_dia_neg_step` (`:6712`) and their RTC iterations `_box_pos_reflTransGen` (`:7008`),
  `_dia_neg_reflTransGen` (`:7024`) are the faithful Lean transcription of `Massacci2000`
  Proposition 8.1 and its duals plus `ChagrovZakharyaschev1997` Proposition 3.6, and `_box_neg`
  (`:6972`) / `_diamond_pos` (`:6984`) are two orthogonal witness conjuncts, existential over
  `acc.hasEdge`.
- **The "ten bridges are the signature of a wrong abstraction" claim is diagnostically right but
  locationally wrong.** The observed "six had their hypotheses weakened" is explained by
  `LoopChecking.lean:6573-6579`: the weakening was a minimisation from `modalHintikkaSetS4` (four
  conjuncts) to `modalS4Saturated` (one conjunct) — **a factoring improvement that already
  happened, not evidence of a wrong abstraction.**
- **Box-plus does NOT touch the reachability defect.** After box-plus the redirect is still an
  edge in `acc`, still requiring `m.r (f src) (f wBlock)` from an arbitrary model. The two defects
  are the two named at `LoopChecking.lean:478-501` ("staleness" and "no reachability
  restriction"), and the file already states that fixing one does **not** fix the other. Box-plus
  addresses the **content** half only; the **structural** half is D1 and is out of scope.
- **Residue, stated precisely and accepted as remaining open**: after box-plus, the open
  obligation is still `branchSatisfiableIn`'s edge conjunct at a redirect edge. Nothing in this
  programme discharges it and no task may try.

### 5.2 Cost profile accepted

`keyLowerBd`'s minting case must additionally show `(pos, □ψ) ∈ relevantSetFinset φ₀ (newForms ++ b) w'`
— exactly `modalFourBoxProp`'s output landing on the branch, which `hintikkaS4_box_pos_step`
already proves (`htarget_mem_fourNew`, `:6626-6652`): **small, lemma exists**. `keysInUniverse`:
small, discharged by the closure argument. `keysDistinct`: **zero**. The two
`_preserves_keyLowerBd` proofs (`:2341`, `:2449`): two proofs to extend, both already structured
around the minting case. Pigeonhole: **zero**, codomain unchanged. The six `Decidable` instances:
**zero**, none routes through S4. `modalS4Saturated` and the eight bridges: **zero**, they mention
no keys.

**The one real risk is `modalTableauS4Keyed_complete` (`FrameCompleteness.lean:4267`)**: enriching
the key changes *which* worlds match, hence which steps block, hence the computed tableau.
Completeness is proved from `modalExpandBranchesS4Keyed_hintikka`, quantified over the driver's
actual behaviour, so it *should* transport — **but this must be verified by `lake build`, not
assumed. Task 563 must gate on it, and if it cannot be repaired sorry-free the task is marked
[BLOCKED], never patched with a `sorry`.**

---

## 6. Decision D3 — Report §5, the `RuleApplySt σ` generalisation: **ACCEPT (additive-first)**

**Verdict: ACCEPT** the generalisation of `RuleApply` to `RuleApplySt σ` with
`RuleApply = RuleApplySt Unit`, **added additively first**, and **ACCEPT the six-step migration
order verbatim** as binding on tasks 562 and 564.

**Rationale.** Exactly **one** driver family of nine forks off `modalTableauGen` /
`modalExpandBranchesGen` — the S4 Keyed (`:7670`, `:7734`) and KeyedOrdered (`:7762`, `:7823`)
pair — and the *unkeyed* S4 driver (`LoopChecking.lean:711`, `:719`) proves the generic ladder
already handles S4-with-guard fine. So the fork is not intrinsic to S4; it exists solely because
`RuleApply` (`Saturation.lean:107-111`) has no slot for per-driver state, forcing
`modalStepBranchS4Keyed` to call `blockingWorldS4Keyed` a **second** time — the code admits this
itself at `LoopChecking.lean:951-953`: "The keys' computation below re-derives the SAME
`blockingWorldS4Keyed` decision `modalApplyOneS4Keyed` already made internally (rather than
threading it out)". Every preservation lemma must then re-establish the correspondence between the
two calls, which is a direct explanation for the 85 private lemmas in `LoopChecking.lean` and for
each of the ten `S4LoopInv` fields needing *two* preservation lemmas (386 lines for `outDegEq`
alone). Retiring the double derivation is where the line-count reduction lives, and it is
deliberately **left unquantified** rather than estimated. Additive-first is mandatory because six
driver bridges are **true `rfl`** (`modalExpandBranchesB_eq`, `modalTableauB_eq`,
`modalTableauS5_eq`, `modalTableauFive_eq`, `modalTableauKb5_eq`, `modalTableauKb5''_eq`) and
break if `modalExpandBranchesGen`'s definitional shape changes; adding the `St` ladder as new
declarations leaves them green **by construction**.

### 6.1 Six-step migration order — binding

1. **Consumer audit of `Saturation.lean`** — a mandatory gate, not an inline step. Enumerate every
   consumer of `RuleApply`, `modalStepBranchGen`, `modalExpandBranchesGen`, `modalTableauGen`,
   `ModalTableauResult`, `modalHintikkaSetGen`. Record which bridges are `rfl` and which are
   proved. (`Saturation.lean` may not be edited without this.)
2. **Add `RuleApplySt` and the `St` ladder as NEW declarations. Touch nothing existing.** Green by
   construction.
3. **Prove `modalExpandBranchesGen_eq_St`** by induction on fuel, mirroring the existing
   `modalExpandBranches_eq` (`Saturation.lean:312-356`), which is already this proof at a
   different pair. Green.
4. **Re-express `modalExpandBranchesS4Keyed` as `modalExpandBranchesGenSt` at
   `σ := List (WorldIndex × Finset (Sign × Proposition Atom))`**, with `modalApplyOneS4KeyedSt`
   returning `keys'` directly; prove `modalExpandBranchesS4Keyed_eq_St` and re-route
   `modalTableauS4Keyed_complete` through it. **This is the only step that can break a landed
   theorem, and it is one theorem. This is the gate.**
5. **Retire the duplicated `keys'` re-derivation.** `modalStepBranchS4Keyed_result_keys_eq`
   (`:2288`) and `_result_acc_eq` (`:2315`) become `rfl`, and each of the ten `S4LoopInv`
   preservation pairs loses its re-derivation bookkeeping. **This is the payoff.**
6. **Only then**, optionally, retire `modalStepBranchS4Keyed` in favour of the ordered stepper —
   already flagged as planned future work at `LoopChecking.lean:995-996`.

Steps 1-3 are risk-free; step 4 is the gate; steps 5-6 are the payoff. **Bridge declaration lines**
(use these, not the `:= rfl` body lines report 01 cites): `BDriver.lean:847` and `:854`,
`S5Simplification.lean:980`, `FiveSimplification.lean:725` / `:1491` / `:2042`.

---

## 7. Decision D4 — Report §6, Boneyard eligibility: **ACCEPT, with BOTH carve-outs mandatory**

**Verdict: ACCEPT** the eligibility list, **subject to a re-run of the consumer audit at execution
time** (the recorded audit is dated and task 557's description mandates re-verification), and
**subject to both mandatory carve-outs, restated verbatim below.**

**Rationale.** The audit method is sound — declaration site vs code reference vs structure-field
provision vs comment-only mention, over all of `Cslib/**/*.lean` and `CslibTests/**/*.lean`, with
comment content classified as comment rather than consumption — and every eligibility row
re-resolved CONFIRMED in the Claim Verification Table. The governing rules are accepted as
binding: **nothing whose deletion cannot be justified by a re-verified zero-consumer check may be
moved, and nothing proven and consumed may be moved at all.** Moving, never deleting, preserves
provenance.

### 7.1 THE TWO MANDATORY CARVE-OUTS — restated verbatim

> TWO CARVE-OUTS ARE MANDATORY: FrameSoundness.lean:1220-1244
> (branchSatisfiableIn_s4FC_ancestor_redirect) is IMMOVABLE despite being zero-consumer, because it
> carries the retained sorry that is an explicit user decision and the rule protecting
> proven-and-consumed code does not by itself protect it; and keysOriginS4 is NOT eligible, having
> 22 code consumers, so the comment at LoopChecking.lean:2001-2002 claiming it was removed is
> FALSE.

Both carve-outs stand exactly as written. One figure inside the second is corrected without
changing it: **"22 code consumers" is not reproducible by any simple command**; the measured
figure is **61 textual references** across `Cslib/` + `CslibTests/`, **55 on non-comment-leading
lines**. `keysOriginS4` is declared at `LoopChecking.lean:1279`. Either way it is emphatically
**not** zero-consumer, so the carve-out's conclusion holds with a large margin. Downstream tasks
must cite the measured range, not the unreproducible 22.

### 7.2 Eligibility list as accepted

| Declaration | Site | Code consumers | Verdict |
|---|---|---|---|
| `blockedRedirect_diaNeg_mem_of_diaOrigin` | `LoopChecking.lean:1506` | **0** (not even a comment mention) | **ELIGIBLE** |
| `blockedRedirect_boxctx_mem_of_boxOrigin` | `LoopChecking.lean:1466` | **0** (2 comment mentions) | **ELIGIBLE** |
| `keysRootEmpty` / `keysRootEmpty_entry` | `:2007` / `:2013` | 0 external; `keysRootEmpty`'s only consumer is `keysRootEmpty_entry` | **ELIGIBLE as a pair** |
| `modalStepBranchS4_preserves_outDegEq` | `:4917-5105` (**189 lines**) | — | **ELIGIBLE only once the `outDegEq` field removal lands** |
| `modalStepBranchS4KeyedOrdered_preserves_outDegEq` | `:5111-5307` (**197 lines**) | — | **ELIGIBLE only once the field removal lands** |
| `branchSatisfiableIn_s4FC_ancestor_redirect` | `FrameSoundness.lean:1220-1244` | 0 | **CARVE-OUT 1 — IMMOVABLE** |
| `keysOriginS4` | `LoopChecking.lean:1279` | 61 refs / 55 non-comment | **CARVE-OUT 2 — NOT ELIGIBLE** |
| `reflTransGen_accWithReds_first_red` | `:8882` | 0 | **HOLD — task-declared preserved asset. Place it, do not move it.** |
| `hasEdge_accWithReds_iff` | `:8862` | 1 | **HOLD — task-declared preserved asset** |
| `Reds` / `accWithReds` | `:8850` / `:8857` | 5 / 7 | **HOLD** — the packaging the preserved assets are stated over |
| `blockedRedirect_unwrapped_boxPos_mem` / `_diaNeg_mem` | `:8926` / `:8958` | 2 / 1 | **HOLD — task-declared preserved assets** |
| `modalS4Saturated` | `:6581` | **7** | **NOT ELIGIBLE** — proven and consumed; also a task-declared preserved asset |

**`outDegEq` removal is NOT a pure deletion.** The field sits at `LoopChecking.lean:7084` in a
structure whose header is at **`:7070`** (not `:7072`) with exactly ten fields, and it has **three**
provision sites: `LoopChecking.lean:7569`, `:7633`, and a **positional anonymous-constructor site
at `FrameCompleteness.lean:4217-4218`** — inside `modalTableauS4Keyed_initial`, i.e. inside the
landed completeness capstone. Four other invariant proofs destructure the structure. **Verify with
`lake build` before and after.** Note also that `modalStepBranch_preserves_outDegEq_gen`
(`FmpMeasure.lean:1520`), `modalStepBranch_preserves_outDegEq` (`:1574`) and
`modalStepBranchGen_preserves_outDegEq` (`GenericDriver.lean:385`) **are consumed** by the
K/generic line and are **not** Boneyard candidates — only the two S4-specific lemmas are.

**Boneyard convention as accepted** (task 566): create `Boneyard/` at the repository root
(confirmed absent), document the convention in `Boneyard/README.md` — quarantined, never imported
by `Cslib/`, excluded from `lake build`, `mk_all`, `lint-style`, `shake`, and all sorry/axiom
censuses, retained for provenance rather than use.

---

## 8. Decision D5 — Report §7, the Seam-2 module table: **ACCEPT AS PROVISIONAL**

**Verdict: ACCEPT the seam table as PROVISIONAL**, explicitly **subject to re-cutting** before any
file is split.

**Rationale.** The seams are genuine — they were identified by reading the file, not by line count
— and `ORGANISATION.md` supplies no line-count guidance to fall back on (verified: no "line",
"size", or "split" guidance exists in it) and describes `Modal/Tableau/` in a single
undifferentiated line, so the splits must be justified by seams and `ORGANISATION.md` must itself
be updated as a deliverable. But the table cannot be final, for a reason internal to the analysis:
**Seam 3 states that the abstraction decisions change the seams.** If box-plus is adopted — and D2
adopts it — `S4/BirthKey.lean` becomes the module the entire keyed track depends on, and
`S4/Redirect.lean` **may collapse entirely**. Adopting the table as final would therefore
contradict D2. A second reason reinforces this: the source ranges for `S4/Hintikka.lean` and
`S4/Redirect.lean` are **discontiguous** in the current `LoopChecking.lean`, which is itself the
evidence that a line-count split would be wrong and that the boundaries need re-derivation after
the abstractions land.

Provisional table (`LoopChecking.lean`, 10,540 lines / 230 decls):

| Proposed module | Source range | Contents | Depends on |
|---|---|---|---|
| `S4/Universe.lean` | `:235–:330` | `modalUniverseS4`, `modalWorldBoundS4`, `signedSubfmls`, cardinality lemmas | FmpMeasure only |
| `S4/BirthKey.lean` | `:333–:443` | `relevantSetFinset`, `successorBirthContent`, `blockingWorldS4` + its three contract lemmas, **and the box-plus abstraction of D2** | Universe |
| `S4/Guard.lean` | `:445–:805` | `blockingWorldS4Keyed` + contracts, `modalApplyOneS4`, `modalApplyOneS4Keyed` + the four shape lemmas, `modalStepBranchS4`, `modalTableauS4` | BirthKey |
| `S4/Invariant.lean` | `:806–:7660` | `S4LoopInv`, the ordered stepper, the twenty preservation lemmas | Guard |
| `S4/Hintikka.lean` | `:6542–:7060`, `:8760–:10540` (**discontiguous**) | `modalHintikkaSetS4`, `modalS4Saturated`, the eight bridges, `S4KeyedHintikkaInv`, the top-loop Hintikka theorem | Invariant |
| `S4/Redirect.lean` | `:1279–:1560`, `:8819–:8990` (**discontiguous**) | `keysOriginS4`, the `Reds`/`accWithReds` packaging, the two preserved unwrapped transfers | Hintikka |

**Binding on task 565**: re-cut these boundaries against the post-abstraction tree before splitting;
do not split by line count; preserve import acyclicity; conform to `ORGANISATION.md` and
`NOTATION.md` and update `ORGANISATION.md`.

The separate **Seam 1** recommendation — extract the re-derived facts as **public** declarations
into `Cslib/Logics/Modal/Tableau/Support/{Subfmls,KnownWorlds,Accessibility}.lean` and delete the
re-derivations — is accepted and is sequenced first by D7. Per §2.3 it must draw from **two**
source files (`Soundness.lean:75` as well as `FmpMeasure.lean`).

---

## 9. Decision D6 — Report §8, documentation: **ACCEPT (four defects; the TRUE verdicts stand)**

**Verdict: ACCEPT.** Four documentation defects are to be corrected; the sites verified TRUE are
to be **left alone**.

**Rationale.** Every site was read and adjudicated against the code, and the Claim Verification
Table re-resolved all four defect sites CONFIRMED at their exact line ranges. The debt in the
three modal Tableau files is **prose-shaped, not tag-shaped** — the tag census is 0/0/0/0 in all
three files — so a tag scan would find nothing and the corrections must be made against the
adjudicated prose sites.

### 9.1 The four defects to correct (task 559)

| # | Site | Defect | Required correction |
|---|---|---|---|
| 1 | `LoopChecking.lean:2001-2002` | Claims `keysOriginS4` "and its supporting lemmas" were removed. **FALSE** — `keysOriginS4` is alive at `:1279` with 61 references | Correct the claim; cite the measured reference count, not the unreproducible "22" |
| 2 | `LoopChecking.lean:8911-8912` | **STALE** references to `hintikkaS4_box_pos_reflTransGen_boxed` / `_dia_neg_reflTransGen_boxed`, both removed in commit `c4b33f63`; this is the source of the "ten bridges" figure | Remove the stale names and record that the bridge count is now **8** |
| 3 | `LoopChecking.lean:2000-2004` | The "**Now possibly orphaned**" hedge on `keysRootEmpty` | Resolve the hedge into a definite zero-external-consumer finding, with the re-run audit as evidence |
| 4 | `FrameSoundness.lean:1215-1219` | The obstruction comment is TRUE as an accurate limitation but **omits** (i) that the declaration has zero consumers and (ii) that `Massacci2000` Theorem 8.1 is itself unproved in the source | Add both facts — they change how a future reader assesses the obstruction |

Also land the measured baseline table **with its exact commands** into the subsystem documentation
so the same drift cannot recur.

### 9.2 The TRUE verdicts to leave alone — **seven sites**

| Site | Claim adjudicated TRUE |
|---|---|
| `FrameSoundness.lean:1246-1255` | The guard can add a redirect edge that is not a genuine `m.r` edge of any witnessing model, breaking `branchSatisfiableIn`'s edge conjunct outright |
| `FrameSoundness.lean:1314-1321` | "`hready`'s discharge for redirect edges is an open obligation pending the re-plan" |
| `FrameSoundness.lean:1193-1194` | "The sorry below marks precisely this point" |
| `LoopChecking.lean:7536-7539` | "All ten fields are now fully closed, zero sorry" |
| `FrameCompleteness.lean:4163-4169` | "The soundness half is FALSE AS STATED", witnessed by the regression corpus |
| `FrameCompleteness.lean:4176-4178` | The decidability half remains out of scope until both a genuine soundness theorem and this completeness theorem exist for the same driver |
| `FrameCompleteness.lean:4184-4186` | "`modalExpandBranchesS4Keyed` is a bespoke driver, not an instance of `modalExpandBranchesGen`" |

**One further site is TRUE but is not "leave alone", and the distinction is recorded rather than
smoothed over.** `LoopChecking.lean:951-953` ("The keys' computation below re-derives the SAME
`blockingWorldS4Keyed` decision …") was adjudicated **TRUE**, and it is exactly the driver-level
mis-factoring D3 adopts a fix for. It is left alone by task 559 (documentation) but is **expected
to become obsolete** at step 5 of the D3 migration, when the re-derivation it describes is retired.
Task 564 must remove or rewrite it at that point. Counting it as an eighth leave-alone site would
be wrong; counting it as a defect would also be wrong.

Two further §8 rows are accounted for outside both lists: `LoopChecking.lean:2019-2036`'s
sub-claim (a) (that `blockedRedirect_boxctx_mem` / `_diaNeg_mem` were removed as FALSE-as-stated)
is **TRUE** and is part of the same comment block as defect 1; and the **axiom-count** row is a
**scope error**, not a documentation defect in code — it is discharged by recording the measured
baseline with its command (§2.4), **never by adjusting a number**.

---

## 10. Decision D7 — the S4-scoping constraint on box-plus, and the sequencing decision

### 10.1 S4-scoping constraint: **BINDING**

The Lemmon filtration is defined only for a **transitive** modal model
(`ChagrovZakharyaschev1997`, `chunk_0248.md:24-25`, print p. 142, unnumbered), and its argument
runs through Proposition 3.6, itself stated only for "a model on a **transitive** frame"
(`chunk_0124.md:41`). CSLib satisfies the precondition — `s4FC` is `Std.Refl r ∧ IsTrans r` — but
the precondition is a *precondition*, not an outcome.

**Therefore, binding on every task in this programme: box-plus is S4-scoped. It MUST NOT be lifted
into `Foundations/` as a general abstraction.** It belongs in `Cslib.Logic.Modal.Tableau`'s S4
cluster, specifically the proposed `S4/BirthKey.lean`. The reuse check confirms there is nothing
in `Foundations/` to extend anyway: `Cslib/Foundations/Logic/Axioms.lean` defines only `top'`,
`neg'`, `conj'`, `disj'`; `Cslib/Foundations/Logic/Tableau/` contains `Sign`, `SignedFormula`,
`RuleResult`, `Branch`, `Closure`, `ClosureCondition`, `Measure`, `PropositionalRules`; and no
existing typeclass (`LTS`, `HasImp`, `HasBox`, `HasBot`, `HasDia`, `HasTop`) carries a persistence
or filtration notion. C5 reinforces this — the source itself calls filtration "a special **ad
hoc** technique in each particular case" — so premature generalisation is contraindicated by the
literature, not merely by caution.

**Related hazard recorded, binding**: enlarging the **filter** Σ instead (as the source must for
K4.1/S4.1/K5, Thms 5.34/5.35, `p02:582-589` and `p02:602-604`) **would** change
`modalWorldBoundS4 = 2^(2·|Sub φ₀|)`, because CSLib's codomain is exactly signs × `Sub φ₀`.
Box-plus enrichment is free; filter enrichment is expensive. A future dispatch tempted toward
`◇□θ`-style enrichment must know it is crossing that line.

### 10.2 Sequencing: **de-duplication precedes every abstraction change**

**Decision: the Scope B de-duplication work (extraction of the re-derived facts into public
`Support/` modules, task 558) runs FIRST, before any abstraction change and before any file
split.**

Four reasons, each independently sufficient: (i) it is **mechanical and behaviour-preserving by
construction** — the re-derivations are stated identically to their originals; (ii) it **needs no
abstraction decision**, so it is not gated on this record's acceptance in the way tasks 562-566
are; (iii) it **shrinks the oversized files before split seams are chosen**, so the seam re-cut of
D5 operates on a smaller and cleaner tree; and (iv) it is the highest-value item the original
scope omitted. Per §2.3 it is also **larger** work than the retired 77 figure implied.

Resulting programme order, binding: **558 (de-duplication) → 562 (RuleApplySt, additive) → 563
(box-plus) → 564 (St migration + retire the re-derivation) → 565 (seam re-cut and split) → 566
(Boneyard) → 567 (vetting acceptance gate)**, with 559 (baseline + documentation defects) and 560
(literature sub-index) independent of the abstraction chain.

---

## 11. Disposition of the two downstream consumers

Task 561's description requires this record to state the disposition of the two downstream
consumers waiting on it, both of whose keys and mint payload change under D2.

**S4 keyed soundness — task 553 (`s4_loop_guard_soundness_reachability_restriction`, [planned]).**
**Disposition: WAIT, and re-plan after task 563 lands.** Its target obligation is untouched by
this record — D1 is explicitly diagnostic and D2 explicitly does not touch the reachability defect
— but its *inputs* change: after box-plus, the free transfer at a redirect target yields a
**wrapped** fact (`T(□ψ)@wBlock`) which the existing persistence mechanism
(`hintikkaS4_box_pos_step` / `_reflTransGen`) can propagate, where today it yields only an
unwrapped fact with no persistence mechanism (`LoopChecking.lean:8830-8832`). Any soundness route
planned against the pre-box-plus key shape is planned against a shape that will change. Task 553
must therefore not begin proof work before 563 lands, and must re-derive its obstruction statement
against the enriched keys. **It must also not be dispatched as a repair of D1**: the structural
half needs the non-injective-`f` mechanism, which is a soundness-design question and remains
open — it is not licensed by this record.

**S4 termination follow-on — tasks 511 (`s4_loop_checking_termination`) and 506
(`s4_loopchecking_machinery_termination_bound_and_decidability`), both [blocked].**
**Disposition: UNBLOCKED BY THIS RECORD on the world-bound question; still WAIT on ordering.**
The decisive fact is D2's freeness result: `modalSubfmls (.box a) = .box a :: modalSubfmls a`
keeps the enriched key inside `signedSubfmls φ₀`, so `signedSubfmls_card_le`,
`signedSubfmls_powerset_card_le`, `modalWorldBoundS4`, `modalKnownWorlds_length_le_worldBoundS4`
and the pigeonhole argument are **untouched** by box-plus — the termination bound does not move.
Any termination plan may be written against the current bound without fear that D2 invalidates it.
What *does* change for these tasks is the driver's *shape* under D3 (the St ladder) and the module
boundaries under D5, so termination work should be sequenced after 564 to avoid re-targeting.
Note also that `outDegEq` — a field these tasks' machinery touches — is slated for removal under
D4, and that its removal is **not a pure deletion** (three provision sites, one positional inside
the landed capstone).

---

## 12. Verdict Summary and Review Sign-Off

| # | Subject | Verdict |
|---|---|---|
| D1 | Report §3 — edge-addition vs world-identification diagnosis | **ACCEPT** (diagnostic only; no repair implemented in this programme) |
| D2 | Report §4 — box-plus birth keys (`boxPlusPair`, `BoxPlusClosed`, enriched `successorBirthContent`) | **ACCEPT**, scoped: at most 2 of 8 bridges collapse; reachability defect untouched |
| D3 | Report §5 — `RuleApplySt σ` with `RuleApply = RuleApplySt Unit` | **ACCEPT**, additive-first, six-step migration order binding |
| D4 | Report §6 — Boneyard eligibility list | **ACCEPT**, audit re-run at execution time, **both carve-outs mandatory** |
| D5 | Report §7 — Seam-2 module table | **ACCEPT AS PROVISIONAL**, subject to re-cutting before any split |
| D6 | Report §8 — documentation | **ACCEPT**: four defects to correct, seven TRUE sites left alone |
| D7 | S4-scoping of box-plus; sequencing | **BINDING**: no lift into `Foundations/`; de-duplication precedes every abstraction change |
| — | Corrected Figures (§2.1), `ModalTableauResult` span **8** (§2.2), re-derivation count **55**-but-larger-work (§2.3) | **RECORDED AS BINDING** |
| — | Retired premises (a)-(d) (§3) | **BINDING, NON-REINSTATABLE** |
| — | Build Gate (§1) | **RECORDED**; V6 vacuous until tasks 554/570 clear it; not this programme's to repair |

**Nothing is DEFERRED.** Every subject this record was dispatched to adjudicate had sufficient
re-verified evidence for an explicit verdict. Two items are recorded as *unverified inputs* rather
than deferred verdicts: the two amplification figures (§2.5), which require a green build to
measure and for which no substitute was fabricated; and the disposition of the retained sorry at
`FrameSoundness.lean:1244`, which task 557's description reserves as a separate user decision and
which this record therefore does not make.

### Review sign-off

This record is the programme's review gate. Per task 561's description: **no file may be moved or
split, and no abstraction may be implemented, until this record is reviewed and ACCEPTED.** Tasks
562-567 remain gated until then; task 558 (de-duplication) is sequenced first by D7 and requires
no abstraction decision.

| Field | Value |
|---|---|
| Reviewed by | _never signed_ — see the superseded-by-execution note below |
| Date | _never signed_ |
| Outcome | _never signed_ — ACCEPTED / ACCEPTED WITH AMENDMENTS / REJECTED |
| Amendments | _never signed_ |

> **SUPERSEDED BY EXECUTION** (recorded 2026-08-07 by codebase review).
>
> This sign-off block was never completed, yet all six gated tasks (562, 563, 564, 565, 566, 567)
> were executed and are archived `completed`. The paragraph above stating that they "remain gated"
> is therefore **false as of this annotation** and is retained only as the record of what the gate
> was intended to require.
>
> Realised risk is nil: every verdict in the §12 table above is an ACCEPT, so the work that shipped
> is the work an ACCEPTED sign-off would have authorised. Nothing here needs to be undone, and this
> annotation is not a retroactive approval — it records that the gate did not operate.
>
> The gap is procedural: a record that declares itself a blocking review gate has no mechanism
> enforcing it, and autonomous orchestration cannot obtain a human signature. The same programme
> demonstrates the working alternative — task 564 explicitly deferred a sub-decision on the grounds
> that it "would require explicit user sign-off not obtainable under autonomous orchestration."
> That deferral pattern is what a future gate of this kind should use: state the requirement at the
> point of the individual decision, where an agent will encounter and honour it, rather than in a
> terminal block of a document the gated tasks never re-read.
