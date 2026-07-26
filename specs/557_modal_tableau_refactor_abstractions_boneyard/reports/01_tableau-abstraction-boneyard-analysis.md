# Report: Modal Tableau Abstraction Analysis, Module Division, and Boneyard Preconditions

- **Task**: `557 - modal_tableau_refactor_abstractions_boneyard`
- **Started**: `2026-07-26T00:00:00Z`
- **Completed**: `2026-07-26T00:00:00Z`
- **Effort**: research dispatch, hard mode (H2 + H3 Tier 1 + H4)
- **Dependencies**: None blocking. Task 553 (S4 loop-guard soundness) is the upstream that
  generated the evidence; this task explicitly does not attempt its obligation.
- **Reference grounding tier**: Tier 1 (literature-backed). BibKeys verified against
  `/home/benjamin/Projects/cslib/references.bib`.

- **Sources/Inputs**: grouped by category below (literature, code, tooling).

Literature (all BibKeys verified against `references.bib`):
- `Massacci2000` — `references.bib:1010`. Corpus:
  `/home/benjamin/Projects/Literature/sources/massacci_2000_single_step_tableaux_for_modal_logics/`
  (77 chunks + full text, not 1 chunk as the per-repo index reports).
- `ChagrovZakharyaschev1997` — `references.bib:75`. Corpus:
  `/home/benjamin/Projects/Literature/sources/chagrovzakharyaschev_1997_modallogic/`. Read
  verbatim: `chunk_0124`, `chunk_0173`, `chunk_0245`–`chunk_0252`, `chunk_0267`, `chunk_0268`,
  `chunk_0295`, plus `p01_introduction.md` and `p02_kripke-semantics.md` (2,353 lines).
- `Blackburn2001` — `references.bib:65`. **Note**: the corpus `doc_id` is `blackburn_2002`
  (2002 Cambridge edition) but the repository BibKey is `Blackburn2001`. Cite `Blackburn2001`.
- `ArisakaDasStrassburger2015` — `references.bib:939`. Corpus entry carries
  `[UNVERIFIED - provenance_fidelity: unadjudicated]`; **not cited in this report**.
- No Hughes & Cresswell BibKey exists in `references.bib`; that corpus entry was not used.

Code (all paths relative to `/home/benjamin/Projects/cslib`):
- `Cslib/Logics/Modal/Tableau/` — all 20 modules
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/{Rules,Soundness,Expansion}.lean`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean`
- `Cslib/Foundations/Logic/{Axioms.lean,Tableau/}`
- `CslibTests/S4LoopGuardRegression.lean`
- `ORGANISATION.md`, `NOTATION.md`, `CONTRIBUTING.md`, `references.bib`

- **Artifacts**: this report plus the return metadata, listed below.
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

Artifacts produced:
- `specs/557_modal_tableau_refactor_abstractions_boneyard/reports/01_tableau-abstraction-boneyard-analysis.md` (this file)
- `specs/557_modal_tableau_refactor_abstractions_boneyard/.return-meta.json`

---

## Executive Summary

- **The mis-factoring has a precise, literature-named location, and it is not the ten-bridge
  adapter set.** It is that the S4 loop-check guard records a blocked minting step as an **edge
  added to `acc`** (`modalApplyOneS4Keyed`: `(.linear [], acc.addEdge sf.label wBlock)`), whereas
  both source calculi record it as an **identification of two worlds under a non-injective
  interpretation** — `Massacci2000` Definition 10.2's `ı()` (explicitly not required injective)
  and the filtration quotient in `ChagrovZakharyaschev1997`. An edge in `acc` is an obligation
  the soundness invariant must discharge (`m.r (f src) (f wBlock)`); an identification is free.
  Every one of the four dead routes died discharging an obligation the design created and the
  literature does not have.
- **The completeness and soundness sides already disagree about what a model is, and that
  asymmetry — not file size — is the real seam.** `extractModelS4 b acc =
  extractModelWith Relation.ReflTransGen b acc` (`FrameCompleteness.lean:143-146`) *constructs*
  the model as the reflexive-transitive closure of recorded edges over `WorldIndex` itself.
  `branchSatisfiableIn` (`FrameSoundness.lean:110`) instead *existentially quantifies* over an
  arbitrary `(W, m, f)`. The redirect edge is harmless for a constructed model and fatal for an
  arbitrary one. This is stated in the code itself at `FrameSoundness.lean:1183-1190`.
- **Box-plus is the right repair, it is licensed for S4 by name, and it is provably free in the
  world bound** — but it is the *second* half of the fix, not the whole of it.
  `successorBirthContent` (`LoopChecking.lean:384-393`) records `(pos, ψ)` when `T(□ψ)@w ∈ b` — the
  **unwrapped** ψ — while `relevantSetFinset` records everything present, wrapped and unwrapped.
  Recording the box-plus pair `{(pos, ψ), (pos, □ψ)}` stays inside the existing codomain
  `signedSubfmls φ₀` (because `modalSubfmls (.box a) = .box a :: modalSubfmls a`,
  `FmpMeasure.lean:79`), so `signedSubfmls_card_le` / `signedSubfmls_powerset_card_le` /
  `modalWorldBoundS4` and the pigeonhole argument are **unchanged**. Three convergent
  authorities: `ChagrovZakharyaschev1997` Corollary 5.32 names S4 explicitly as admitting
  filtration "using ... the Lemmon filtration"; the source's own justification for □⁺
  (`chunk_0248.md:9-16`) is *composability of the constraint across a further step*, which is
  verbatim the obstruction the repository recorded at `LoopChecking.lean:8830-8832`; and the
  repository's own audit reached the same repair independently (`LoopChecking.lean:2034-2036`,
  "recording box-context keys in *boxed* form ... a three-line consequence of the already-landed
  `S4LoopInv.keyLowerBd`"). The one path by which box-plus could have cost anything — needing
  iteration to depth > 1 — is **closed negatively** from the source.
- **The task description's literature framing needed three corrections, all verified verbatim.**
  There is no theorem numbered "interval theorem" (unnumbered prose after Theorem 5.23, and an
  *unproved* authorial remark); its `S̲`/`S̄` are relations on the **filtration quotient**, so it is
  not "precisely the failure mode" of a redirect-channel design; and Theorem 5.51 is about **Grz**
  via **selective** filtration, not S4 via filtration. Separately, **`Massacci2000` Theorem 8.1 —
  the claim that blocking preserves satisfiability — is stated and never proved in that paper**; it
  is deferred to Goré's model graphs. The four dead soundness routes were reconstructing a proof
  their cited source does not contain.
- **The `modalTableauGen` unification is a one-signature change affecting exactly one driver
  family.** All eight other drivers (K, T, B, S5, Five, Kb5, Kb5'', and the *unkeyed*
  `modalTableauS4` at `LoopChecking.lean:718-719`) already go through
  `modalTableauGen`/`modalExpandBranchesGen`. Only the S4 **Keyed** family forks, for exactly one
  reason: `RuleApply` (`Saturation.lean:108-111`) returns `RuleResult × Accessibility` with no
  slot for per-driver state, so `keys` must be threaded by a forked stepper — which then
  **re-derives the guard decision `modalApplyOneS4Keyed` already made internally**
  (`LoopChecking.lean:951-953`, the code says so). Generalizing to `RuleApplySt σ` removes both
  the fork and the duplication.
- **A large, quantified defect the task description does not mention: 77 "local re-derivation"
  sites** across the Tableau subsystem, root-caused by `private` lemmas in `FmpMeasure.lean`
  (50 private declarations) being unavailable across files. `modalSubfmls_trans` alone is
  re-derived privately in three separate files. This is the highest-value, lowest-risk module
  division work available and it is purely mechanical.
- **Nine of the task description's quantitative claims do not reproduce.** The most consequential:
  the "26 vs 47 axiom" drift is a **scope confusion, not a drift** — the Tableau subsystem
  contains **zero** axiom declarations and **three** raw `axiom` word matches; 26 is the
  repo-wide count of real `axiom` declarations in `Cslib/`. Full table below. Also: **the sorry
  census for the entire Tableau subsystem is exactly 1**, at `FrameSoundness.lean:1244`, and that
  declaration has **zero code consumers**.

---

## Context & Scope

This dispatch performs Scope A (abstraction analysis) and the *verification preconditions* for
Scopes B, C and D. It writes no code and moves no files: the task description mandates that the
abstraction analysis "should be completed and reviewed before any file is moved or split."

**Explicitly out of scope and not attempted**: the S4 keyed loop-guard soundness obligation. The
sorry at `FrameSoundness.lean:1244` is retained by user decision; this report records evidence
about its surroundings and makes no disposition.

**Constraints verified, not relaxed:**
- `Rules.lean` (345 lines, 7 decls), `Saturation.lean` (490, 15), `Branch.lean` (206, 15) were
  read but no edit is proposed to `Rules.lean` or `Branch.lean`. A `Saturation.lean` change *is*
  proposed (the `RuleApply` generalization) and a consumer audit for it is specified below as a
  mandatory gate, per the constraint.
- Behaviour preservation target confirmed: `modalTableauS4Keyed_complete`
  (`FrameCompleteness.lean:4267`) plus exactly six landed `Decidable` instances —
  `instDecidableKValid` (`CompletenessLoop.lean:2293`), `instDecidableTValid`
  (`FrameCompleteness.lean:1313`), `instDecidableBValid` (:1927), `instDecidableS5Valid` (:2420),
  `instDecidableFiveValid` (:3210), `instDecidableKb5Valid` (:4156). Count matches the
  description exactly.

---

## Findings

### 1. Source-to-Implementation Mapping (H3, Tier 1)

| Source Claim | BibKey | Lean Target | Translation Notes |
|---|---|---|---|
| Def. 8.2: blocking by **shorter modal copy** — "for every prefixed formula σ:¬□A that is not reduced there is a shorter modal copy σ0 of σ such that σ0:¬□A is reduced" (`chunk_0030.md:30-38`) | `Massacci2000` | `blockingWorldS4Keyed` (`LoopChecking.lean:506-511`) | **Three divergences.** (a) Massacci compares **ν-formulae only** (box formulae); CSLib compares `successorBirthContent` (witness pair + unwrapped box context) against a recorded key. (b) Massacci's relation is **equality** of ν-sets ("the same ν formulae"), and CSLib's is also equality (`decide (wk.2 = successorBirthContent ...)`) — this one **matches**. (c) Massacci requires only `\|σ0\| < \|σ\|`, no ancestry — CSLib's `.min?` over `keys` is the analogue of "shortest", so this **matches**. The divergence that matters is (a). |
| Pruning Lemma 8.2 + `Ftree(σ) = {σ*:A \| σ*:A ∈ B and σ is an initial subsequence of σ*}` (`chunk_0031.md:11-19`, `chunk_0030.md:39-43`) | `Massacci2000` | **No counterpart exists in CSLib.** | **This is the defect.** Massacci's blocking response is to **delete** `Ftree(σ.n)` — a downward-closed subtree — and to identify `σ` with `σ0` in the model. CSLib's response is to **add an edge** `src → wBlock` to `acc`. Ancestry enters Massacci's apparatus *only* in `Ftree`, i.e. only in the deletion, never in the blocking condition. |
| Def. 10.2: SST-interpretation `ı(σ) ∈ W` with `ı(σ)Rı(σ.n)` — **not required injective**; "SST interpretations are just K-interpretations" (`chunk_0052`, FULL:1688-1702) | `Massacci2000` | `branchSatisfiableIn`'s `f : WorldIndex → W` (`FrameSoundness.lean:110`, `1267`) | `f` is already non-injective-permitted, so CSLib has the right *shape*. What it lacks is any mechanism that *uses* non-injectivity: the guard licenses an edge instead of licensing `f src' = f wBlock`. This is the missing abstraction. |
| Prop. 8.1: "If the prefix σ0 is an initial subsequence of σ in the branch B, then σ0:□A ∈ B implies σ:□A ∈ B" — proved by a **saturation** argument ("no rule is applicable to branch B"), valid only for rule-(4) logics (`chunk_0034.md:3-4`, `chunk_0065.md:3-16`) | `Massacci2000` | `hintikkaS4_box_pos_step` (`LoopChecking.lean:6626`), `hintikkaS4_box_pos_reflTransGen` (:7008), and duals `hintikkaS4_dia_neg_step` (:6712) / `_reflTransGen` (:7024) | **Faithful.** CSLib proves these from `modalS4Saturated` (`LoopChecking.lean:6581`) — a saturation hypothesis — exactly matching Massacci's proof shape. `modalFourBoxProp` (`FrameRules.lean:133-138`) is Massacci's rule (4) verbatim: from `T(□φ)@w`, emit `T(□φ)@w'` for each recorded successor. These four bridges are the **persistence mechanism** that exists. |
| S4 prefix-length bound `hb_L = 2 + dp + p × n` (Table IV, `chunk_0032.md:24-33`); `hb_L − 1 = 1 + dp + p×n` (`chunk_0065.md:48-49`). A **DEPTH** bound on prefix length | `Massacci2000` | `modalWorldBoundS4 φ₀ = 2 ^ (2 * \|modalSubfmls φ₀\|)` (`LoopChecking.lean`, via `signedSubfmls_powerset_card_le`) | **Deliberate, sound divergence.** CSLib bounds the **number of worlds** by pigeonhole on birth-key powerset cardinality, not the **depth** of any path. The two are not comparable; CSLib's is the standard filtration-cardinality bound. Massacci's Table IV form is internally inconsistent in the paper (body proof-sketch at FULL:1167 writes `d` where Table IV writes `dp`); the sanity check at FULL:1201 (`hb_S4 = 2 + 1 + 2×1 = 5`) confirms Table IV. **Do not port Massacci's bound.** |
| **Theorem 8.1** ("If the L-tableau ... terminates with a π-completed branch, then A is L-satisfiable") — i.e. *blocking preserves satisfiability* (`chunk_0030.md:24-28`) | `Massacci2000` | Would be `modalTableauS4Keyed_sound` | **CRITICAL: Theorem 8.1 is stated and NEVER PROVED in Massacci2000.** Appendix §B.2 "PROOFS OF SECTION 8" contains only Theorem 8.4 (termination/prunability). §10.2 defers it: "The extension to π-(modal)-completed branches (Section 8) can be done along the same lines of the completeness proofs in [7] ... or in [20] for completeness via model graphs" (`chunk_0054.md:3-7`). Theorem 10.6, the model-existence theorem he *does* prove, requires a **fully completed** branch and constructs `W = {σ present in B}`, `σRσ*` iff `σ ⪯ σ*` — the identity model, which blocking breaks. **The literature source cited by the four dead routes does not contain the soundness proof they were trying to reconstruct.** |
| Lemma 9.7 (Local Stability) + Technique 9.7 (re-activation: "If a new prefixed formula σ:□A is introduced ... then for every σ:◇B if the corresponding σ.n:B has been deleted, then σ:◇B must be reduced again") (FULL:1526-1544, 1616-1618) | `Massacci2000` | `modalStepBranchS4KeyedOrdered` "settled-context scheduling" (`LoopChecking.lean:1107`, doc at 984-996) | The ordered stepper's discipline — a minting shape fires only once no non-minting rule can fire — is CSLib's answer to the same problem Technique 9.7 addresses (a world's box-content must be stable before its outgoing edge is fixed). Massacci's warning at FULL:1603-1607 ("To prove that a prefix can be safely deleted, it is not enough to look only to shorter prefixes; we must also look to longer ones") applies to logics with rule (B), **not** to S4 — the shorter-copy heuristic is sound for K4/S4 precisely because boxes only arrive from ancestors. |
| **Theorem 5.51** "Grz is determined by the class of finite partial orders" (`chunk_0267.md:23`, print p. 152). Construction: `S_{n+1}` := "the **reflexive and transitive closure** of the relation `S_n ∪ {(x, y(x,□ψ)) : x ∈ X_n and □ψ ∈ Θ_x}`" (`chunk_0267.md:49-51`). Box-propagation discharged by "**S_{n+1} ⊆ R_Grz** (but S_{n+1} is **not** in general the restriction of R_Grz to V_{n+1})" (`chunk_0267.md:53-54`) | `ChagrovZakharyaschev1997` | `extractModelS4 b acc = extractModelWith Relation.ReflTransGen b acc` (`FrameCompleteness.lean:143-146`); `extractModelS4_r` (:150-153) proves the relation *is* the RTC; `extractModelS4_hasEdge_imp_r` (:185) is the containment | **The RTC construction is already faithfully implemented, on the completeness side only.** Two corrections to the task description's framing: (a) Theorem 5.51 is about **Grz**, not S4, and it uses **selective filtration** (§5.5), not filtration (§5.3); (b) the containment `S ⊆ R_ambient` is discharged **by construction** — S is *built* as a subset of the ambient relation. That is the crux: C&Z never assume containment against an arbitrary model, they construct it. See §3. |
| **(HSm1)/(HSm2)** Hintikka-system conditions: "(HSm1) if `tSt'` then `φ ∈ Γ'` for every `□φ ∈ Γ`; (HSm2) if `□φ ∈ Δ` then there is `t'` with `tSt'` and `φ ∈ Δ'`" (`p01_introduction.md:3109-3123`, print pp. 75-76) | `ChagrovZakharyaschev1997` | `branchSatisfiableIn`'s edge conjunct `acc.hasEdge w w' → m.r (f w) (f w')` (`FrameSoundness.lean:110`) is CSLib's (HSm1); `modalHintikkaSetS4` conjuncts 3-4 (`LoopChecking.lean:6557-6562`) are (HSm2) | **Exact structural correspondence, and the divergence is decisive.** C&Z discharge (HSm1) "purely by `S_{n+1} ⊆ R_Grz`" — truth is always evaluated in the *ambient* model and the built relation is a subset of it. CSLib instead quantifies existentially over the ambient model, so containment is an obligation rather than a construction step. **This, not the bridge count, is the mis-factoring.** |
| **Corollary 5.32**: "Using the transitive closure of the finest filtration **or the Lemmon filtration** ... we immediately obtain ... **The logics K4, D4, S4 admit filtration and so are finitely approximable and decidable**" (`chunk_0252.md:12-17`, `p02:541-547`, print p. 144) | `ChagrovZakharyaschev1997` | The whole S4 keyed track | **The direct endorsement of the recommendation in §4.** S4 is explicitly named as a logic for which the Lemmon filtration works. This is the citation that licenses adopting box-plus for *this* logic. |
| **Lemmon filtration** (unnumbered, `chunk_0248.md:24-31`, `p02:459-463`, print p. 142), verbatim: "Alternatively we can define a transitive filtration 𝔑 of a **transitive** modal model 𝔐 through Σ by taking, for any x and y in 𝔐, `[x]S[y] iff y ⊨ □⁺φ whenever x ⊨ □φ, for all □φ ∈ Σ`... It is called the **Lemmon filtration**" | `ChagrovZakharyaschev1997` | **Absent.** `successorBirthContent` (`LoopChecking.lean:384-393`) records only the unwrapped projection | The recommended new abstraction. **Note it is unnumbered** — cite by chunk/page, not by a definition number. **Note it is defined for transitive models only.** See §4. |
| **□⁺ operator** (unnumbered abbreviation, `chunk_0173.md:11-14`, print p. 98), verbatim: "A syntactic analog of the reflexivization operator r is the following translation + ... **Let □⁺φ be an abbreviation for the formula φ ∧ □φ.**" Dual at `chunk_0295.md:3`: "□⁺φ = φ ∧ □φ, ◇⁺φ = φ ∨ ◇φ" | `ChagrovZakharyaschev1997` | Proposed `boxPlusPair` (§4) | **Not in `chunk_0248` as the task description states** — it is defined in Chapter 3, p. 98, as the syntactic analogue of *reflexivization*. That framing matters: box-plus is what makes a relation behave as if reflexivized, which is exactly what an S4 loop-back edge needs. |
| **Proposition 3.6** (`chunk_0124.md:41-46`, print p. 67): "Suppose 𝔐 is a model on a **transitive** frame. Then for every point x in 𝔐 and every formula φ, (i) `(𝔐,x) ⊨ □φ` implies `(𝔐,y) ⊨ □φ` for every `y ∈ x↑`; (ii) `(𝔐,x) ⊨ ◇φ` implies `(𝔐,y) ⊨ ◇φ` for every `y ∈ x↓`" | `ChagrovZakharyaschev1997` | `hintikkaS4_box_pos_step` (`LoopChecking.lean:6626`) and `hintikkaS4_box_pos_reflTransGen` (:7008), plus duals (:6712, :7024) | **Faithful, and it is the semantic counterpart of Massacci Prop. 8.1.** The four `_step`/`_reflTransGen` bridges are the Lean form of Prop. 3.6, on the syntactic side. **Prop. 3.6 is exactly the lemma the Lemmon filtration's soundness argument runs through** (`chunk_0248.md:12-13`: "Since R is transitive and by Proposition 3.6, we then have `u' ⊨ □⁺φ`"). So CSLib already has the machinery the box-plus repair needs. |
| **Filtration interval + nontransitivity warning** (unnumbered prose after **Theorem 5.23**, `chunk_0246.md:43-65`, `p02:435-445`, print p. 141). `S̲ = {([x],[y]) : ∃x',y' (x'~x ∧ y'~y ∧ x'Ry')}` (finest/least), `S̄ = {([x],[y]) : ∀□φ ∈ Σ (x ⊨ □φ → y ⊨ φ)}` (coarsest/greatest), both on the quotient `V = W/~_Σ`. Verbatim: "It is to be noted that a relation S between S̲ and S̄ may be nontransitive even if the original R is transitive, in particular, not all S in this interval give rise to filtrations of intuitionistic models." | `ChagrovZakharyaschev1997` | The obstruction at `FrameSoundness.lean:1238-1244` | **The task description's framing is wrong on three counts, now verified verbatim.** (a) There is **no theorem numbered "interval theorem"** — this is unnumbered prose and an **unproved authorial remark** ("It is to be noted that ... may be"), not a proposition; do not cite it as one. (b) `S̲`/`S̄` are relations on the **filtration quotient** `W/~_Σ`, so the warning is about quotient constructions specifically, **not** about the redirect-channel design. (c) The warning is therefore **not** "precisely the failure mode a subtractive or redirect-channel design runs into." See the Adversarial Self-Verification section. **The recommendation in §4 does not depend on this warning.** |
| Filtration / FMP / decidability, independent presentation | `Blackburn2001` (ch. 2, 6) | `modalWorldBoundS4`, `modalUniverseS4`, the pigeonhole argument | Cross-check only; not load-bearing for any claim in this report. |

### 2. Measured-vs-Asserted Baseline (required artifact)

Every number below was re-measured. Commands are given for each so the baseline is reproducible.
This table is the artifact that discharges the "documentation drift" finding of Scope D.

| Claim (task description) | Asserted | **Measured** | Verdict | Command |
|---|---|---|---|---|
| `LoopChecking.lean` lines | 10,674 | **10,540** | DRIFT −134 | `wc -l` |
| `LoopChecking.lean` declarations | 150 | **230** | DRIFT +80 | `grep -cE '^(private \|protected \|noncomputable \|partial \|@\[[^]]*\] )*(theorem\|lemma\|def\|abbrev\|instance\|structure\|inductive\|class) '` |
| `FrameSoundness.lean` lines | 5,317 | **5,317** | EXACT | `wc -l` |
| `FrameCompleteness.lean` lines | 4,532 | **4,307** | DRIFT −225 | `wc -l` |
| Three-file total | 20,523 | **20,164** | DRIFT −359 | sum |
| Redirect semantic surface: clauses | 4 clauses | **4 clauses** | CONFIRMED | see below |
| Redirect semantic surface: lines | 17 | **14** code lines (16 incl. docstring lines) | NEAR; locations shifted | `modalHintikkaSetS4` conjuncts 3–4 at `LoopChecking.lean:6557-6562` (**asserted location EXACT**); `S4KeyedHintikkaInv.eBoxNegWitness` at **8779-8782** and `.eDiamondPosWitness` at **8786-8789** (asserted 8756-8759 / 8763-8766, shifted +23) |
| `hintikkaS4_*` bridges | 10 | **8** | DRIFT −2, **explained** | `grep -rnE '^(private \|...)*(theorem\|lemma\|def) hintikkaS4'`. The two missing are `hintikkaS4_box_pos_reflTransGen_boxed` / `_dia_neg_reflTransGen_boxed`, removed in commit `c4b33f63` ("revert red-channel machinery orphaned by Gate B"); still referenced in the comment at `LoopChecking.lean:8911-8912`. **The asserted 10 was correct when written.** Counting `hintikka_congr_S4` (:7844) gives 9 `hintikka`-prefixed declarations in the file. |
| `outDegEq` consumer count | 0 in the S4 line | **0 code consumers of `S4LoopInv.outDegEq`; 2 field-provision sites** | CONFIRMED (see §6) | scripted audit; provisions at `LoopChecking.lean:7569,7633` |
| `outDegEq` preservation proof length | 188 lines | **189 lines** (`modalStepBranchS4_preserves_outDegEq`, 4917–5105) **plus a second, undocumented 197-line** ordered variant (`modalStepBranchS4KeyedOrdered_preserves_outDegEq`, 5111–5307) | UNDERSTATED: **386 lines total**, not 188 | scripted extent measurement |
| Axiom count | 26 asserted / 47 raw matches | **Tableau dir: 0 axiom declarations, 3 raw `axiom` word matches. Repo-wide `Cslib/`: 26 axiom declarations, 1,701 raw `axiom` word matches** | **SCOPE CONFUSION, not drift** | `grep -rnE '^(private \|protected )*axiom ' Cslib/Logics/Modal/Tableau/*.lean` → NONE; same over `Cslib/` → 26 |
| Sorry census, `Cslib/Logics/Modal/Tableau/` | not stated | **exactly 1**, at `FrameSoundness.lean:1244` | BASELINE CAPTURED | block-comment-aware scan; the 11 other `sorry` textual hits in the directory are all prose |
| Sorry census, repo-wide `Cslib/` | not stated | **10** | BASELINE CAPTURED | `grep -rn '^\s*sorry\s*$\|:= sorry\|exact sorry' Cslib/` |
| Tag census in the three files | 0 FIX/TODO/NOTE/QUESTION | **0 / 0 / 0 / 0** | CONFIRMED | `grep -rnoE '\bTODO:'` etc. |
| Tag census repo-wide `Cslib/` | 11 TODO, 8 NOTE | **11 TODO, 8 NOTE, 0 FIX, 0 QUESTION** | CONFIRMED EXACT | as above |
| Amplification: 4 decls / 1,036 lines; 43 decls / 1,983 lines reachable from `modalTableauS4Keyed_complete` | — | **NOT RE-MEASURED** | see note | This requires a transitive-dependency query over the elaborated environment, not a text scan. Reproduce with `lake env lean --run` over `Lean.Environment` `getUsedConstants` from `modalTableauS4Keyed_complete`, or `#print axioms` plus manual closure. **I did not fabricate a substitute number.** The *qualitative* claim is independently corroborated: the semantic surface is 4 clauses (verified) and the S4-keyed preservation machinery in `LoopChecking.lean` alone spans ~85 private lemmas. |
| `Boneyard/` exists | does NOT exist | **does not exist** | CONFIRMED | `ls -d Boneyard` → No such file or directory |
| Six landed `Decidable` instances (K/T/B/S5/Five/KB5) | 6 | **6, exactly those** | CONFIRMED | see Context & Scope |
| `ModalTableauResult` consumed by 8 files | 8 | **`ModalTableauResult` textual refs span 11 Tableau modules**; the constructor carries `(b, acc)` only — `Saturation.lean:82-87` | PARTIAL: shape claim CONFIRMED, file count not reproduced as 8 | `grep -rl ModalTableauResult` |
| `CslibTests/S4LoopGuardRegression.lean` exists | yes | **yes, 197 lines** | CONFIRMED | `wc -l` |

**New measurement not in the description**: `lake exe checkInitImports` currently **FAILS**, with
`object file '.lake/build/lib/lean/Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.olean' ... does not exist`.
This is a stale-build condition unrelated to the Tableau subsystem, but it means the acceptance
gate "`checkInitImports` clean" requires a full `lake build` first. **A planner must budget for
this**; it is not a Tableau defect.

### 3. The Actual Mis-Factoring: Edge-Addition Where the Literature Identifies Worlds

This is the load-bearing finding. It reframes the problem and it is evidenced entirely from code
already in the repository plus `Massacci2000`.

**Current behaviour.** `modalApplyOneS4Keyed` (`LoopChecking.lean:747-759`), on a blocked minting
shape, returns `(.linear [], acc.addEdge sf.label wBlock)`. The blocked step contributes **no
formula** and **one edge**.

**What that edge costs.** `acc` is consumed by two mutually incompatible model notions:
- `extractModelS4 b acc = extractModelWith Relation.ReflTransGen b acc`
  (`FrameCompleteness.lean:143-146`). Worlds are `WorldIndex` itself, `f = id`, relation = RTC of
  `acc.hasEdge`. An extra edge is simply an extra edge; the frame conditions are free
  (`extractModelS4_refl`, `extractModelS4_trans`).
- `branchSatisfiableIn FC b acc` (`FrameSoundness.lean:110`): `∃ (W) (m : Model W Atom)
  (f : WorldIndex → W), FC m.r ∧ (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) ∧ ...`. An extra
  edge is a new obligation `m.r (f src) (f wBlock)` against a model nobody constructed.

**Why every route died here.** The code states the mechanism itself at
`FrameSoundness.lean:1183-1190`: "`branchSatisfiableIn`'s witness model is *existentially
arbitrary*: nothing constrains `m.r` to equal the transitive closure of `acc`... Any predecessor
`x` of `f src` in the (unconstrained) ambient relation ... would, after the closure forced by
transitivity, need that formula's content to transfer to `f a` too, and no hypothesis available
to a *standalone* ... lemma can supply this for an unbounded family of such `x`."

**What the literature does instead.** `Massacci2000` never adds an edge for a blocked step. Two
mechanisms, both absent from CSLib:
1. **Deletion.** Pruning Lemma 8.2 replaces `B` by `B \ Ftree(σ.n)` — the descendant-closed
   subtree rooted at the blocked witness world. Ancestry enters the apparatus *only here*, in the
   deletion, and its role is to keep deletion downward-closed so no surviving longer prefix is
   orphaned.
2. **Non-injective interpretation.** Definition 10.2's `ı()` maps prefixes to worlds with only
   `ı(σ)Rı(σ.n)` required. Nothing forbids `ı(σ) = ı(σ0)`. The satisfiability of a blocked branch
   is witnessed by *identifying* the blocked world with its shorter modal copy, not by relating
   them.

**Independent confirmation from `ChagrovZakharyaschev1997`.** The same conclusion follows from a
second source that shares no apparatus with Massacci. Theorem 5.51's selective filtration builds
`S_{n+1}` as "the reflexive and transitive closure of `S_n ∪ {(x, y(x,□ψ)) : ...}`"
(`chunk_0267.md:49-51`) and then discharges the box-propagation condition (HSm1) by the single
observation "**S_{n+1} ⊆ R_Grz** (but S_{n+1} is not in general the restriction of R_Grz to
V_{n+1})" (`chunk_0267.md:53-54`). Truth is evaluated throughout in the **ambient** canonical model
`𝔐_Grz`; the constructed relation is a *subset* of the ambient one, so (HSm1) — "if `tSt'` then
`φ ∈ Γ'` for every `□φ ∈ Γ`" (`p01_introduction.md:3109-3113`) — is immediate.

CSLib's `branchSatisfiableIn` edge conjunct **is** (HSm1). But CSLib asks an
existentially-quantified, unconstructed `m.r` to *contain* `acc`, where C&Z *build* `S` inside
`R_ambient`. The failure the code records at `FrameSoundness.lean:1183-1190` is precisely the
absence of that construction. And the defect the guard's own docstring names — "**No reachability
restriction.** The redirect edge ... with no constraint that `w'` be reachable from the source at
all" (`LoopChecking.lean:491-493`) — is exactly the containment that C&Z's `S_{n+1} ⊆ R_Grz`
guarantees by construction and that CSLib never establishes.

Two independent sources, two different formalisms, one conclusion: **the blocked step must be
recorded inside a construction that guarantees containment (C&Z) or identification (Massacci), not
as an edge asserted against an arbitrary model.**

**4-element defect bar (H2):**
- **Evidence / counterexample**: `CslibTests/S4LoopGuardRegression.lean` (197 lines,
  machine-checked). `cex := □αA ∨ □αL` over `αA := □p0 ∨ ¬¬◇p1`, `αL := □p0 ∨ ¬□p1` has a 3-world
  reflexive-transitive countermodel yet the driver closes it. The docstring at
  `LoopChecking.lean:491-497` names the responsible defect as "**No reachability restriction**...
  Soundness needs `m.r (f src) (f w')` in an arbitrary S4 frame, and nothing here supplies it."
- **Current behaviour**: blocked minting adds `acc.addEdge src wBlock`, creating a soundness
  obligation against an existentially-arbitrary model.
- **Required behaviour**: a blocked minting step must record a *filtration equivalence*
  (licensing `f src' = f wBlock`, or licensing deletion of the would-be subtree), not an edge in
  the soundness-tracked relation.
- **Isolation**: the semantic dependence is 4 clauses / 14 lines
  (`LoopChecking.lean:6557-6562`, `8779-8782`, `8786-8789`). The edge-addition is 2 lines
  (`LoopChecking.lean:753`, `757`).

### 4. Does the Lemmon Box-Plus Pairing Factor This Subsystem Correctly?

**Recommendation: adopt it, at the birth-key level, and understand that it factors exactly one of
the two defects.**

#### Why □⁺ and not φ — the exact mechanism, and why it is *this* subsystem's obstruction

`ChagrovZakharyaschev1997` does not label the reason, but it displays it in the transitive-closure
argument at `chunk_0248.md:9-16` (print p. 142), verbatim: "By the definition of S, `x'Rv'` for some
`x'` and `u'` that are Σ-equivalent to x and u, respectively. **Since R is transitive and by
Proposition 3.6, we then have `u' ⊨ □⁺φ` and so `u ⊨ □⁺φ`. Using the same argument for the sequence
u,...,v,y, we shall eventually obtain `y ⊨ □⁺φ`.**"

The mechanism, stated precisely: `y ⊨ □⁺φ = φ ∧ □φ` delivers **both** the local truth of φ (which is
all filtration condition (iv) literally demands) **and** the persistence of `□φ` at y, so the
constraint **re-propagates along a further S-step**. `y ⊨ φ` alone is not composable: from
`[x]S[y]` and `[y]S[z]` you may conclude `y ⊨ φ` but nothing whatever about z, and condition (iv)
fails on the composite.

**That is verbatim the obstruction recorded at `LoopChecking.lean:8830-8832`**: "the free transfer
below ... yields only an *unwrapped* branch fact at the redirect target, and unwrapped facts have no
persistence mechanism in this tableau's Hintikka apparatus." The literature's diagnosis and the
repository's Gate B verdict are the same sentence about the same object. The persistence mechanism
CSLib is missing at the key level is the one C&Z supply with `□⁺`, and CSLib *already has* its
semantic counterpart — Proposition 3.6 — as `hintikkaS4_box_pos_step` / `_reflTransGen`.

**And S4 is explicitly in scope.** Corollary 5.32 (`chunk_0252.md:12-17`, print p. 144): "Using the
transitive closure of the finest filtration **or the Lemmon filtration** ... **The logics K4, D4,
S4 admit filtration and so are finitely approximable and decidable.**" The one precondition —
transitivity of the base model — is satisfied: `s4FC` is `Std.Refl r ∧ IsTrans r`.

#### Reuse Check Protocol — run first, results

1. **`Cslib.Foundations.*`**: `Cslib/Foundations/Logic/Axioms.lean` defines only `top'`, `neg'`,
   `conj'`, `disj'` — no `HasBox`-derived box-plus, no persistence typeclass.
   `Cslib/Foundations/Logic/Tableau/` contains `Sign`, `SignedFormula`, `RuleResult`, `Branch`,
   `Closure`, `ClosureCondition`, `Measure`, `PropositionalRules`. **No persistence abstraction
   exists in Foundations.** Nothing to reuse; nothing to extend there yet.
2. **Existing typeclass hierarchy** (`LTS`, `HasImp`, `HasBox`, `HasBot`, `HasDia`, `HasTop`):
   none carries a persistence or filtration notion.
3. **Notation typeclasses**: no new notation is proposed, so no check is owed.
4. **Mathlib**: `Relation.ReflTransGen` is already used and is the right primitive. No Mathlib
   filtration/quotient abstraction is needed — the construction is already `extractModelWith`.
5. **`Logics/*` namespaces — PRIOR ART FOUND, two instances:**
   - `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean:344` —
     `boxDiamondPersistence (branch) (w) (t) (freshTime)`, documented as: "collect T(box A) and
     F(diamond A) formulas at a specific world and time, re-labeled to a fresh time. Used by
     time-creation rules to propagate **box persistence (box phi -> G(box phi))** and diamond-neg
     persistence." **This is box-plus at the rule level, already in CSLib**, for the bimodal
     tableau, and it is the exact analogue of `modalFourBoxProp` (`FrameRules.lean:133-138`).
   - `Cslib/Logics/Propositional/Tableau/Intuitionistic/` — `propagatePersistence`
     (`Rules.lean:139`), `applyPersistenceFixpoint` (`Expansion.lean:153`), and critically
     **`MonotoneEdges worldOf edges : Prop := ∀ w w', isAccessible edges w w' → worldOf w ≤ worldOf w'`**
     (`Soundness.lean:367-369`), docstring: "Used in the soundness invariant to ensure persistence
     rules are sound." **This is the persistence-carrying predicate, at the soundness-invariant
     level, already in CSLib.** It is precisely the hypothesis whose S4 analogue the redirect edge
     violates.

**Conclusion of the reuse check**: box-plus at the *rule* level already exists twice
(`modalFourBoxProp`, `boxDiamondPersistence`). A persistence-carrying *soundness-invariant*
predicate already exists once (`MonotoneEdges`). What is missing is box-plus at the **key /
equivalence-class** level. That is genuinely new for this repository, and it is what the
literature supplies.

#### The concrete Lean-level shape

The defect is visible in three lines. `successorBirthContent` (`LoopChecking.lean:384-393`):

```
insert (s, φ) ((signedSubfmls φ₀).filter (fun p =>
  (p.1 = Sign.pos ∧ b.any (· == ⟨.pos, .box p.2, w⟩)) ∨
  (p.1 = Sign.neg ∧ b.any (· == ⟨.neg, .diamond p.2, w⟩))))
```

When `T(□ψ)@w ∈ b`, this records the pair `(pos, ψ)` — the **unwrapped** ψ. But the minted world
receives *both* `T(ψ)@w'` (from `modalApplyOne`'s boxNeg/diamondPos arm) *and* `T(□ψ)@w'` (from
the 4-rule `modalFourBoxProp`). `relevantSetFinset` records both. The key records one. That
asymmetry is the wrapped/unwrapped mismatch, and it is why `keyLowerBd`
(`k ⊆ relevantSetFinset φ₀ b w`) yields only unwrapped facts at a redirect target — the exact
Gate B obstruction recorded at `LoopChecking.lean:8830-8832`.

**Proposed abstraction.** Add to `LoopChecking.lean` (or, better, to a new
`Cslib/Logics/Modal/Tableau/S4/BirthKey.lean` — see §7), in namespace
`Cslib.Logic.Modal.Tableau`:

```
/-- Lemmon's box-plus operator at the signed-pair level: `□⁺ψ = ψ ∧ □ψ`, rendered as the
    two-element set `{(pos, ψ), (pos, □ψ)}`, dually `{(neg, ψ), (neg, ◇ψ)}`. -/
def boxPlusPair (φ₀ : Proposition Atom) (s : Sign) (ψ : Proposition Atom) :
    Finset (Sign × Proposition Atom)

/-- A birth key is box-plus closed: whenever it contains the unwrapped `(pos, ψ)` arising from a
    box context, it contains the wrapped `(pos, .box ψ)` too. -/
def BoxPlusClosed (φ₀ : Proposition Atom) (k : Finset (Sign × Proposition Atom)) : Prop
```

and change `successorBirthContent`'s filter to emit both members of each pair.

**Namespace/location**: `Cslib.Logic.Modal.Tableau`, in a new `S4/BirthKey.lean` alongside
`signedSubfmls` / `relevantSetFinset` / `successorBirthContent`, which form a self-contained
cluster (`LoopChecking.lean:295-443`) with no dependency on the driver above it.

#### Cost to the landed proofs — measured, not estimated

**The world bound is unchanged, and this is provable.** `modalSubfmls (.box a) = .box a ::
modalSubfmls a` (`FmpMeasure.lean:79`). So if `T(□ψ)@w ∈ b` and `b ⊆ modalUniverseS4 φ₀` (which
`S4LoopInv.bClosure` guarantees), then `□ψ ∈ modalSubfmls φ₀`, hence
`(pos, .box ψ) ∈ signedSubfmls φ₀`. The box-plus enrichment therefore **stays inside the existing
codomain**. Consequently `signedSubfmls_card_le` (`LoopChecking.lean:313`),
`signedSubfmls_powerset_card_le` (:325), `modalWorldBoundS4`, and
`modalKnownWorlds_length_le_worldBoundS4` are **untouched**. Box-plus is free in the pigeonhole
argument. This is the single most important cost fact and it is why the repair is cheap.

Per-obligation cost:

| Landed result | Cost of box-plus keys |
|---|---|
| `S4LoopInv.keyLowerBd` (`k ⊆ relevantSetFinset φ₀ b w`) | Its *minting case* must now also show `(pos, □ψ) ∈ relevantSetFinset φ₀ (newForms ++ b) w'`. This is exactly `modalFourBoxProp`'s output landing on the branch — the fact `hintikkaS4_box_pos_step` already proves at :6626-6652 (`htarget_mem_fourNew`). **Small, and the lemma already exists.** |
| `S4LoopInv.keysInUniverse` (`k ⊆ signedSubfmls φ₀`) | Discharged by the closure argument above. **Small.** |
| `S4LoopInv.keysDistinct` | The guard's freshness contract (`blockingWorldS4Keyed_none_fresh`) is stated over whatever `successorBirthContent` returns; enriching it does not change the contract's shape. **Zero.** |
| `modalStepBranchS4_preserves_keyLowerBd` (:2341) and `modalStepBranchS4KeyedOrdered_preserves_keyLowerBd` (:2449) | Two proofs to extend, both already structured around the minting case. |
| `modalKnownWorlds_length_le_worldBoundS4` (pigeonhole) | **Zero** — codomain unchanged. |
| `modalTableauS4Keyed_complete` (:4267) | **Zero if the guard's decisions are unchanged; NON-ZERO if they change.** Enriching the key changes *which* worlds match, hence which steps block, hence the computed tableau. Completeness is proved from `modalExpandBranchesS4Keyed_hintikka`, which is quantified over the driver's actual behaviour, so it should transport — but this must be verified by `lake build`, not assumed. **This is the one real risk and the plan must gate on it.** |
| The six landed `Decidable` instances | **Zero.** None routes through S4. `instDecidableS4Valid` does not exist (verified: only comment mentions at `FrameCompleteness.lean:4176`, `LoopChecking.lean:7655,7733`). |
| `modalS4Saturated` and the eight `hintikkaS4_*` bridges | **Zero.** They mention no keys. Verified: `modalS4Saturated`'s signature is `(φ₀) (b) (acc)`. |

#### Which of the bridges box-plus subsumes, and which it does not

Box-plus **subsumes none of the eight bridges outright.** This is an honest negative and it
matters for the plan. The eight bridges are:

| Bridge | Line | Subsumed by box-plus? |
|---|---|---|
| `hintikkaS4_box_pos_step` | 6626 | **No** — it *supplies* the fact box-plus keys need. It is Massacci Prop. 8.1 and is load-bearing. |
| `hintikkaS4_dia_neg_step` | 6712 | No — dual of the above. |
| `hintikkaS4_box_pos_reflTransGen` | 7008 | No — the RTC iteration of `_step`; needed by `extractModelS4`'s RTC relation. |
| `hintikkaS4_dia_neg_reflTransGen` | 7024 | No — dual. |
| `hintikkaS4_box_pos_self` | 6804 | **Candidate for collapse** — the reflexive (T-rule) instance. Once keys are box-plus closed, `T(□ψ)@w → T(ψ)@w` is a projection of the key, not a separate saturation appeal. |
| `hintikkaS4_dia_neg_self` | 6887 | **Candidate for collapse** — dual. |
| `hintikkaS4_box_neg` | 6972 | No — the *witness* conjunct (conjunct 3 of `modalHintikkaSetS4`), existential over `acc.hasEdge`. Orthogonal to keys. |
| `hintikkaS4_diamond_pos` | 6984 | No — dual witness conjunct. |

**So box-plus collapses at most 2 of 8.** The claim in the task description that the ten-bridge
set is "the signature of a wrong abstraction" is *diagnostically* right but *locationally* wrong:
the bridges are not adapters around a badly-factored predicate, they are the faithful Lean
transcription of Massacci Prop. 8.1 and its duals, plus two witness conjuncts. The adapter
multiplication the description observed — "six had their hypotheses weakened" — is explained by
`LoopChecking.lean:6573-6579`: the weakening was from `modalHintikkaSetS4` (four conjuncts) to
`modalS4Saturated` (one conjunct). **That is a hypothesis minimisation, i.e. a factoring
improvement that already happened, not evidence of a wrong abstraction.**

**What box-plus does *not* factor, and what the residue is.** Box-plus fixes the wrapped/unwrapped
mismatch, so that a blocked redirect's free transfer yields a **wrapped** fact (`T(□ψ)@wBlock`)
which the existing persistence mechanism (`hintikkaS4_box_pos_step`/`_reflTransGen`) *can*
propagate. It does **not** touch the **edge-vs-identification** defect of §3: the redirect is
still an edge in `acc`, still requiring `m.r (f src) (f wBlock)` from an arbitrary model. The two
defects are the two named in `LoopChecking.lean:478-501` ("staleness" and "no reachability
restriction"), and the file already says "fixing one does **not** fix the other." Box-plus
addresses the *content* half. The *structural* half needs the non-injective-`f` mechanism, and
that is a soundness-design question outside this task's mandate.

**Residue, stated precisely**: after box-plus, the open obligation is still
`branchSatisfiableIn`'s edge conjunct at a redirect edge. Nothing in this task discharges it, and
this task must not try.

#### Documented counterarguments to box-plus (H4 requirement, answered from the source)

`ChagrovZakharyaschev1997` documents a graded set of failures for filtration. Each was checked
against S4's situation.

| Counterargument | Source | Does it apply to S4 here? |
|---|---|---|
| **C1 — HARD FAILURE: filtration can fail for *every* Σ.** "this may yield no result no matter what Σ we choose, even if L is really finitely approximable. For example ... **GL** is characterized by the class of finite strict orders, but the canonical frame 𝔉_GL contains a reflexive point, and so by (iii) in Section 5.3, **every filtration of 𝔐_GL has a reflexive point as well**" (`p02:761-768`, print p. 149) | §5.5 opening | **NO — and this is the most important negative check.** The obstruction is structural: condition (iii) (`xRy ⟹ [x]S[y]`) forces reflexivity through the quotient, and GL needs *irreflexive* orders. □⁺ is powerless against it; C&Z's fix is a different method entirely (selective filtration). But **S4 wants reflexivity** (`s4FC = Std.Refl r ∧ IsTrans r`), so condition (iii) preserving reflexivity is a *feature*, not an obstruction. Corollary 5.32 names S4 as admitting filtration. **S4 is on the safe side of exactly this dividing line, for exactly the reason that makes it safe.** |
| **C2 — `Σ = Sub φ` can be insufficient; the fix is a BIGGER FILTER, not a deeper □⁺.** For K4.1/S4.1: "we should take a smaller accessibility relation in our filtration which can be done by **choosing a bigger filter Σ**. Define Σ as the closure under subformulas of the set `{□θ → θ, ◇□θ : θ ∈ Sub φ}`" (`p02:582-589`). Similarly K5 (`p02:602-604`) and KP, where filtrating through `Sub φ` is *provably* insufficient — a `2^(2^\|Sub φ\|)` lower bound (`p02:756-759`) | Thms 5.34, 5.35; KP Remark | **Not for plain S4** (Cor. 5.32 covers it with `Σ = Sub φ`), **but it is a live hazard for the design.** CSLib's codomain is `signedSubfmls φ₀ = {pos,neg} ×ˢ (modalSubfmls φ₀).toFinset`, i.e. exactly signs × `Sub φ₀`. Should the guard ever need to distinguish more (e.g. the `.1` "staleness" defect pushing toward `◇□θ`-style filter enrichment), **the codomain would grow and the pigeonhole bound `modalWorldBoundS4 = 2^(2·\|Sub φ₀\|)` would change.** A planner must know that enlarging the *filter* is expensive whereas enriching with `□⁺` is free. |
| **C3 — On the canonical model you have no choice of S.** "when filtrating the canonical model 𝔐_L, we have no real choice for S... **Proposition 5.27** Suppose 𝔑 is a filtration of the canonical model 𝔐_L through Σ such that 𝔑 ⊨ L. Then 𝔑 is the finest filtration of 𝔐_L through Σ" (`chunk_0250.md:8-17`, print p. 143) | Prop. 5.27 | **NO.** CSLib does not filtrate a canonical model; `extractModelS4` builds from a tableau branch. Prop. 5.27 constrains a construction CSLib does not perform. Recorded so a future reader does not misapply it. |
| **C4 — transitivity is a PRECONDITION of the Lemmon filtration, not an outcome.** The Lemmon filtration is defined only "of a **transitive** modal model 𝔐" (`chunk_0248.md:24-25`), and its argument runs through Proposition 3.6, itself stated only for "a model on a **transitive** frame" (`chunk_0124.md:41`) | — | **Satisfied.** `s4FC` includes `IsTrans r`. But this means **box-plus is S4-specific and must not be lifted into `Foundations/` as a general abstraction.** It belongs in `Cslib.Logic.Modal.Tableau`'s S4 cluster. |
| **C5 — filtration is ad hoc per logic.** "the filtration method, requiring a special **ad hoc** technique in each particular case" (`p04:1523-1525`) | Ch. 11 | Applies. Reinforces C4: do not generalize prematurely. |
| **C6 — does □⁺ need iterating to depth > 1?** | — | **NO — answered negatively, and this retires an open item.** The source contains **no** statement that □⁺ must be iterated or nested. `□⁺φ = φ ∧ □φ` is always depth-1. The `+`-translation (`chunk_0173.md:13-14`) replaces every `□` in φ by `□⁺`, which is compositional nesting inherited from φ's own modal depth, not iteration of `□⁺`. Where more depth is needed the book **enlarges Σ** (C2), never the □⁺ pairing. **Therefore the "free in the world bound" argument above stands unconditionally**: depth-1 enrichment keeps `(pos, □ψ) ∈ signedSubfmls φ₀` by `modalSubfmls (.box a) = .box a :: modalSubfmls a`, and no iteration is required. |

**Net verdict on box-plus**: recommended, with S4 explicitly licensed by Corollary 5.32, free in the
world bound (C6 closes the only path by which it could have cost anything), S4-scoped rather than
general (C4/C5), and insufficient on its own for the structural defect (§3). No counterargument
found blocks adoption.

### 5. The `modalTableauGen` / `modalExpandBranchesGen` Unification — Concrete Verdict

**Yes, it can thread per-driver state, and the change is small and well-isolated.**

**Measured current state.** `RuleApply` (`Saturation.lean:107-111`):

```
abbrev RuleApply (Atom) [DecidableEq Atom] [Hashable Atom] :=
  SignedFormula (Proposition Atom) WorldIndex →
  List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility →
  RuleResult (Proposition Atom) WorldIndex × Accessibility
```

Drivers that already instantiate the generic ladder (measured by grep for
`modalExpandBranchesGen` / `modalTableauGen` definitional uses):

| Driver | Site | Generic? |
|---|---|---|
| K (`modalTableau`) | `Saturation.lean:380` | bridged by `modalTableau_eq` (:387) |
| T | `TDriver.lean:80,86` | yes |
| B | `BDriver.lean:88,95` | yes, true `rfl` (:851,855) |
| S5 | `S5Simplification.lean:944,963` | yes, true `rfl` (:975,981) |
| Five | `FiveSimplification.lean:702,709` | yes, true `rfl` |
| Kb5 | `FiveSimplification.lean:1469,1475` | yes, true `rfl` |
| Kb5'' | `FiveSimplification.lean:2020,2026` | yes, true `rfl` |
| **S4 (unkeyed)** | `LoopChecking.lean:711,719` | **yes** — `modalTableauGen (modalApplyOneS4 φ) φ` |
| **S4 Keyed** | `LoopChecking.lean:7670,7734` | **NO — forked** |
| **S4 KeyedOrdered** | `LoopChecking.lean:7762,7823` | **NO — forked** |

So **exactly one driver family out of nine forks**, and the unkeyed S4 driver proves the generic
ladder already handles S4-with-guard fine. The fork exists solely because `keys` must be threaded
through the stepper's return type: `modalStepBranchS4Keyed` (`LoopChecking.lean:955-961`) returns
`Option (branches × expandedSets × Accessibility × keys)` where `modalStepBranchGen` returns
`Option (branches × expandedSets × Accessibility)`.

**The concrete duplication this forces, quoted from the code** (`LoopChecking.lean:951-953`):
"The keys' computation below re-derives the SAME `blockingWorldS4Keyed` decision
`modalApplyOneS4Keyed` already made internally (rather than threading it out), keeping this
definition's shape close to the un-keyed original above for auditability."

That is the mis-factoring at the driver level, admitted in the source: because `modalApplyOneS4Keyed
φ₀ keys : RuleApply Atom` freezes `keys` and cannot return `keys'`, the stepper must call
`blockingWorldS4Keyed` a **second** time and every preservation lemma must then re-establish the
correspondence between the two calls. This is a direct explanation for why there are 85 private
lemmas in `LoopChecking.lean` and why each of the ten `S4LoopInv` fields needs *two* preservation
lemmas (plain + `Ordered`), 386 lines for `outDegEq` alone.

**Proposed signature.** In `Saturation.lean`:

```
/-- State-threading rule-application shape. `RuleApply` is the `σ := Unit` case. -/
abbrev RuleApplySt (Atom) [DecidableEq Atom] [Hashable Atom] (σ : Type*) :=
  SignedFormula (Proposition Atom) WorldIndex →
  List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → σ →
  RuleResult (Proposition Atom) WorldIndex × Accessibility × σ
```

with `modalStepBranchGenSt`, `modalExpandBranchesGenSt`, `modalTableauGenSt` threading `σ`, and
`modalStepBranchGen apply = modalStepBranchGenSt (liftRuleApply apply)` projected at `σ := Unit`.

**Migration order that keeps all six `Decidable` instances green at every step.** This ordering is
forced by the constraint that `Saturation.lean` may not be edited without a consumer audit, and by
the `rfl` bridges: `modalExpandBranchesB_eq`, `modalTableauB_eq`, `modalTableauS5_eq`,
`modalTableauFive_eq`, `modalTableauKb5_eq`, `modalTableauKb5''_eq` are all **true `rfl`** and will
break if `modalExpandBranchesGen`'s definition changes shape.

1. **Consumer audit of `Saturation.lean`** (mandatory gate, per the constraint). Enumerate every
   consumer of `RuleApply`, `modalStepBranchGen`, `modalExpandBranchesGen`, `modalTableauGen`,
   `ModalTableauResult`, `modalHintikkaSetGen`. Record which bridges are `rfl` and which are
   proved.
2. **Add `RuleApplySt` and the `St` ladder as NEW declarations. Touch nothing existing.** The six
   `rfl` bridges keep holding because `modalExpandBranchesGen` is unchanged. Green by
   construction.
3. **Prove `modalExpandBranchesGen_eq_St`**: `modalExpandBranchesGen apply = modalExpandBranchesGenSt
   (lift apply) ... ()`. One induction on fuel, mirroring the existing `modalExpandBranches_eq`
   (`Saturation.lean:312-356`) which is already exactly this proof at a different pair. Green.
4. **Re-express `modalExpandBranchesS4Keyed` as `modalExpandBranchesGenSt` at
   `σ := List (WorldIndex × Finset (Sign × Proposition Atom))`**, with `modalApplyOneS4KeyedSt`
   returning `keys'` directly. Prove `modalExpandBranchesS4Keyed_eq_St`. `modalTableauS4Keyed_complete`
   must be re-routed through this equation. **This is the only step that can break a landed
   theorem, and it is one theorem.**
5. **Retire the duplicated `keys'` re-derivation.** With `keys'` coming out of the apply call, the
   `modalStepBranchS4Keyed_result_keys_eq` (:2288) / `_result_acc_eq` (:2315) correspondence lemmas
   become `rfl`, and each of the ten `S4LoopInv` preservation pairs loses its re-derivation
   bookkeeping. **This is where the line-count reduction lives.**
6. **Only then**, optionally, retire `modalStepBranchS4Keyed` in favour of the ordered stepper —
   which `LoopChecking.lean:995-996` already flags as planned future work.

Steps 1–3 are risk-free. Step 4 is the gate. Steps 5–6 are the payoff.

### 6. Scope C Preconditions — Re-Verified Consumer Audit

Method: a scripted audit (`declaration site` vs `code reference` vs `structure-field provision`
vs `comment-only mention`) over all of `Cslib/**/*.lean` and `CslibTests/**/*.lean`.
Block-comment and line-comment content is classified as comment, not consumption.

**`S4LoopInv.outDegEq` — zero-consumer status RE-VERIFIED, with a caveat the description misses.**

- `S4LoopInv.outDegEq` declared `LoopChecking.lean:7084`.
- **Code consumers of the field (projections `.outDegEq` on an `S4LoopInv` value): 0.**
- The only two `.outDegEq` projections in the repository are `CompletenessLoop.lean:1403` and
  `:1782`, both on `hpot : ModalPotentialInv` (declared `FmpMeasure.lean:2336`) — the **K/generic**
  line, not S4. Confirmed by reading both sites.
- Field-provision sites: `LoopChecking.lean:7569` and `:7633`, inside
  `modalStepBranchS4_preserves_S4LoopInv` (:7541) and
  `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` (:7599).
- **Caveat**: `modalStepBranch_preserves_outDegEq_gen` (`FmpMeasure.lean:1520`),
  `modalStepBranch_preserves_outDegEq` (:1574), and `modalStepBranchGen_preserves_outDegEq`
  (`GenericDriver.lean:385`) are **consumed** by the K/generic line and are **NOT Boneyard
  candidates**. Only the two *S4-specific* preservation lemmas are.
- **Boneyard-eligible, with measured extents**: `modalStepBranchS4_preserves_outDegEq`
  (`LoopChecking.lean:4917-5105`, **189 lines**) and
  `modalStepBranchS4KeyedOrdered_preserves_outDegEq` (`:5111-5307`, **197 lines**) — **386 lines
  total**, not the 188 asserted. Removing them requires deleting the `outDegEq` field from
  `S4LoopInv` and both provision sites, which edits a structure four other invariant proofs
  destructure. **Verify with `lake build` before and after; this is not a pure deletion.**

**Other zero-consumer declarations found (all in the four dead routes' orphan set):**

| Declaration | Site | Code consumers | Boneyard verdict |
|---|---|---|---|
| `blockedRedirect_diaNeg_mem_of_diaOrigin` | `LoopChecking.lean:1506` | **0** (not even a comment mention) | **ELIGIBLE** |
| `blockedRedirect_boxctx_mem_of_boxOrigin` | `LoopChecking.lean:1466` | **0** (2 comment mentions) | **ELIGIBLE** |
| `branchSatisfiableIn_s4FC_ancestor_redirect` | `FrameSoundness.lean:1220` | **0** | **HOLD — contains the retained sorry at :1244.** See below. |
| `keysRootEmpty_entry` | `LoopChecking.lean:2013` | **0** | **ELIGIBLE** |
| `keysRootEmpty` | `LoopChecking.lean:2007` | 1, and it is `keysRootEmpty_entry` above | **ELIGIBLE as a pair** — the docstring at :2000-2004 already says "Now possibly orphaned ... Left in place, not deleted, pending the re-plan." Re-verified: still zero external consumers. |
| `reflTransGen_accWithReds_first_red` | `LoopChecking.lean:8882` | **0** | **HOLD — task-declared preserved asset.** Listed by name in the description's route-independent assets. Do not move; place it. |
| `hasEdge_accWithReds_iff` | `LoopChecking.lean:8862` | 1, and it is `reflTransGen_accWithReds_first_red` | **HOLD — task-declared preserved asset.** |
| `Reds` / `accWithReds` | `LoopChecking.lean:8850` / `:8857` | 5 / 7, all within the same 90-line section | **HOLD** — the packaging the two preserved assets are stated over. |
| `blockedRedirect_unwrapped_boxPos_mem` / `_diaNeg_mem` | `:8926` / `:8958` | 2 / 1, all comment-adjacent within the section | **HOLD — task-declared preserved assets.** |
| `keysOriginS4` | `LoopChecking.lean:1279` | **22** | **NOT ELIGIBLE.** Contrary to `LoopChecking.lean:2001-2002`'s claim that "`keysOriginS4` and its supporting lemmas" were removed, `keysOriginS4` is still declared and has 22 code references (`:1249,1258,1295,1309,1310,1325,1331,1332,...`). **This is a Scope D documentation defect: the removal comment is FALSE.** |
| `modalS4Saturated` | `LoopChecking.lean:6581` | **7** (the six bridges + `modalHintikkaSetS4_saturated`) | **NOT ELIGIBLE** — proven and consumed. Also a task-declared preserved asset. |

**Load-bearing observation about the retained sorry, offered as evidence only.** The sorry at
`FrameSoundness.lean:1244` sits inside `branchSatisfiableIn_s4FC_ancestor_redirect`, which has
**zero code consumers**. The Tableau subsystem's entire sorry census is this one term. The task
states its disposition is not this task's to make, and **this report makes no disposition.** It is
recorded because (a) the Scope C rule "nothing proven and consumed may be moved" does not by
itself protect it — it is neither proven nor consumed — so the plan must carry an **explicit
carve-out** naming `FrameSoundness.lean:1220-1244` as immovable by user decision, and (b) the
verification criterion "sorry census not increasing" has a measured baseline of exactly 1.

### 7. Scope B — Module Division Along Real Seams

`ORGANISATION.md` gives **no line-count guidance** (verified: no "line", "size", "split" guidance
exists in it) and describes `Modal/Tableau/` with a single undifferentiated line:
"`Tableau/` -- Tableau decision procedures (K/T/B/S4/S5 drivers, saturation,
soundness/completeness)". So the splits must be justified by seams, and `ORGANISATION.md` itself
must be updated — that is a Scope B deliverable in its own right.

**Seam 1 — the highest-value split, and it is not in the task's file list.**
`FmpMeasure.lean` has **50 private declarations**, and the Tableau subsystem contains **77
"local re-derivation" comment sites** re-proving them file-locally because `private` blocks
cross-file access. Measured distribution: `S5Simplification.lean` 15+, `FiveSimplification.lean`
11+, `BDriver.lean` 6, `FrameCompleteness.lean` 5, `FrameSoundness.lean` 3.
`modalSubfmls_trans` alone is re-derived in `S5Simplification.lean:97`,
`FiveSimplification.lean:736`, and `BDriver.lean:211`. `modalKnownWorlds_fold_spec` in
`BDriver.lean:914`, `S5Simplification.lean:990`, `S5Simplification.lean:1051`,
`FiveSimplification.lean:775`. `hasEdge_addEdge_cases` in `BDriver.lean:904`,
`FrameCompleteness.lean:2917`, `:3839`, `FrameSoundness.lean:1196`.

**Recommendation**: extract the re-derived facts into
`Cslib/Logics/Modal/Tableau/Support/{Subfmls,KnownWorlds,Accessibility}.lean` as **public**
declarations and delete the 77 re-derivations. This is mechanical, behaviour-preserving by
construction (the re-derivations are stated as identical), removes a large line count, imports
cleanly (these facts depend on nothing above them), and needs no abstraction decision. **It should
be its own task and it should go first**, because it shrinks the three target files before anyone
splits them.

**Seam 2 — `LoopChecking.lean` (10,540 lines, 230 decls) splits at four natural boundaries**,
all identified by reading the file, not by line count:

| Proposed module | Source range | Contents | Depends on |
|---|---|---|---|
| `S4/Universe.lean` | :235–:330 | `modalUniverseS4`, `modalWorldBoundS4`, `signedSubfmls`, cardinality lemmas | FmpMeasure only |
| `S4/BirthKey.lean` | :333–:443 | `relevantSetFinset`, `successorBirthContent`, `blockingWorldS4` + its three contract lemmas, **and the proposed box-plus abstraction** | Universe |
| `S4/Guard.lean` | :445–:805 | `blockingWorldS4Keyed` + contracts, `modalApplyOneS4`, `modalApplyOneS4Keyed` + the four shape lemmas, `modalStepBranchS4`, `modalTableauS4` | BirthKey |
| `S4/Invariant.lean` | :806–:7660 | `S4LoopInv`, the ordered stepper, and the twenty preservation lemmas | Guard |
| `S4/Hintikka.lean` | :6542–:7060, :8760–:10540 | `modalHintikkaSetS4`, `modalS4Saturated`, the eight bridges, `S4KeyedHintikkaInv`, the top-loop Hintikka theorem | Invariant |
| `S4/Redirect.lean` | :1279–:1560, :8819–:8990 | `keysOriginS4`, the `Reds`/`accWithReds` packaging, the two preserved unwrapped transfers | Hintikka |

Note the ranges for `S4/Hintikka.lean` and `S4/Redirect.lean` are **discontiguous** in the current
file — that is itself evidence of the mis-factoring and the reason a line-count split would be
wrong.

**Seam 3 — the abstraction analysis changes the seams.** If box-plus is adopted, `S4/BirthKey.lean`
becomes the module the entire keyed track depends on, and `S4/Redirect.lean` may collapse
entirely. **This is why the description's sequencing requirement (abstraction analysis reviewed
before any file is moved) is correct and must be honoured.**

### 8. Scope D — Documentation Sites Verified Against Code

Each named site was read and adjudicated. Verdicts: **TRUE** (accurate as stated), **STALE**
(was true, no longer), **FALSE** (never true or now wrong).

| Site | Claim | Verdict | Evidence |
|---|---|---|---|
| `FrameSoundness.lean:1246-1255` (`branchPropAdequateIn` module comment) | The guard "can add a *redirect* edge `v → wBlock` that is not a genuine `m.r` edge of any witnessing model... This breaks `branchSatisfiableIn`'s edge conjunct outright for such an edge." | **TRUE** | Verified against `blockingWorldS4Keyed` (:506) and `branchSatisfiableIn` (:110). This is the correct diagnosis and §3 above builds on it. |
| `FrameSoundness.lean:1314-1321` (`branchPropAdequateIn_s4FC_boxPos_trans_mem` docstring) | "`hready`'s discharge for redirect edges is an open obligation pending the re-plan." | **TRUE** | `blockedRedirect_boxctx_mem` is indeed absent (verified: not declared anywhere). |
| `LoopChecking.lean:2019-2036` (Redirect-Inertness Assembly — REMOVED) | (a) `blockedRedirect_boxctx_mem`/`_diaNeg_mem` were removed as FALSE-as-stated. (b) "`keysOriginS4` and its supporting lemmas" were removed too. | (a) **TRUE** — neither is declared. (b) **FALSE** | `keysOriginS4` is declared at `LoopChecking.lean:1279` with **22 code references**. The removal claim is wrong and must be corrected. |
| `LoopChecking.lean:2000-2004` | `keysRootEmpty`'s "sole consumer, `blockedRedirect_boxctx_mem`, was removed... Now possibly orphaned" | **TRUE, and the hedge should be resolved** | Re-verified: `keysRootEmpty` has exactly one consumer (`keysRootEmpty_entry`, itself zero-consumer). Restate as a definite zero-consumer finding with the audit as evidence, or move the pair to `Boneyard/`. |
| `LoopChecking.lean:7536-7539` | "**All ten fields are now fully closed, zero sorry**" | **TRUE** | `S4LoopInv` (:7072-7101) has exactly ten fields (`bClosure`, `eNodup`, `eClosure`, `accFresh`, `accKnown`, `outDegEq`, `keysTotal`, `keyLowerBd`, `keysDistinct`, `keysInUniverse`) and both `_preserves_S4LoopInv` theorems (:7541, :7599) provide all ten with no `sorry`. The subsystem's only sorry is at `FrameSoundness.lean:1244`. **Accurate as stated.** |
| `FrameCompleteness.lean:4176-4178` | "The decidability half (`s4Valid_decides`/`instDecidableS4Valid`) remains out of scope until both a genuine soundness theorem and this completeness theorem exist for the same driver." | **TRUE** | Neither `s4Valid_decides` nor `instDecidableS4Valid` is declared (verified: only three comment mentions). The six landed instances are K/T/B/S5/Five/KB5. **Accurate limitation, correctly evidenced.** |
| `FrameCompleteness.lean:4163-4169` | "**The soundness half is FALSE AS STATED**... `CslibTests/S4LoopGuardRegression.lean` witnesses..." | **TRUE** | Regression file exists (197 lines). Counterexample restated consistently at `LoopChecking.lean:470-497`. |
| `FrameCompleteness.lean:4184-4186` | "`modalExpandBranchesS4Keyed` is a bespoke driver, not an instance of `modalExpandBranchesGen`" | **TRUE, and it is the defect §5 addresses** | Verified: `modalExpandBranchesS4Keyed` (:7670) does not route through `modalExpandBranchesGen`. |
| `FrameSoundness.lean:1193-1194` | "The sorry below marks precisely this point" | **TRUE** | The sorry is at :1244, in the `hdirect = false` branch, exactly the case the comment describes. |
| `FrameSoundness.lean:1215-1219` | "The `sorry` marks the one case genuinely not dischargeable from these hypotheses" | **TRUE as an accurate limitation**, with one gap | The reasoning is sound. **Missing**: the comment does not record that this declaration has zero consumers, nor that Massacci's Theorem 8.1 (the corresponding literature claim) is itself unproved in the source. Both should be added — they change how a future reader assesses the obstruction. |
| `LoopChecking.lean:951-953` | "The keys' computation below re-derives the SAME `blockingWorldS4Keyed` decision `modalApplyOneS4Keyed` already made internally" | **TRUE, and it is the driver-level mis-factoring** | Verified by reading :955-982 against :747-759. |
| `LoopChecking.lean:8911-8912` | references `hintikkaS4_box_pos_reflTransGen_boxed` / `_dia_neg_reflTransGen_boxed` | **STALE** | Both were removed in commit `c4b33f63`. This is the source of the "ten bridges" figure. Correct the comment and record that the count is now 8. |
| Axiom count | 26 asserted, 47 raw matches | **Both figures are repo-wide, not subsystem-scoped** | Tableau: **0** axiom declarations, **3** raw word matches. `Cslib/`: **26** axiom declarations, **1,701** raw word matches. The "drift" is a scope error. **Fix by recording the measured baseline in §2 above and citing the exact command, not by adjusting a number.** |

---

## Decisions

1. **The primary abstraction finding is edge-addition-vs-world-identification (§3), not the
   ten-bridge adapter set.** The bridge set is a faithful transcription of `Massacci2000`
   Prop. 8.1 and duals plus two witness conjuncts; box-plus collapses at most 2 of 8.
2. **Box-plus IS recommended, at the birth-key level, and it is free in the world bound.** It
   factors the *content* (wrapped/unwrapped) half of the problem. It does not factor the
   *structural* (edge-vs-identification) half. Both halves are named in the code already
   (`LoopChecking.lean:478-501`).
3. **The `modalTableauGen` unification is recommended** via a new `RuleApplySt σ` with
   `RuleApply = RuleApplySt Unit`, migrated in the six-step order of §5. One driver family forks;
   one landed theorem is at risk (step 4).
4. **The 77-site `private` re-derivation cleanup is recommended as the FIRST implementation task**,
   ahead of any abstraction change. It is mechanical, behaviour-preserving by construction, and
   shrinks the three target files before anyone splits them. It was not in the task description.
5. **`FrameSoundness.lean:1220-1244` gets an explicit immovability carve-out.** It is
   zero-consumer, which would otherwise make it Boneyard-eligible; the retained sorry is a user
   decision.
6. **`keysOriginS4` is NOT Boneyard-eligible** (22 consumers), and the comment claiming it was
   removed is FALSE and must be corrected.
7. **No file is moved or split in this dispatch**, per the description's sequencing requirement.
8. **Zero-debt compliance**: no recommendation in this report introduces a `sorry` or an axiom.
   Every proposed change is either additive-then-bridged (§5 steps 2–3), a content enrichment with
   an existing supporting lemma (§4), or a mechanical deduplication (§7 Seam 1). Where a sorry-free
   path does not exist — the redirect edge conjunct — the report says so and stops.

---

## Recommendations

Prioritised, with the review gate located explicitly.

**P0 — Task A: `private`-visibility deduplication.** Extract the re-derived facts from
`FmpMeasure.lean` (50 private decls), `Soundness.lean`, `TDriver.lean`, `CompletenessLoop.lean`
into public `Cslib/Logics/Modal/Tableau/Support/*.lean`; delete the 77 local re-derivations.
Verify with `lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
`lake shake --add-public --keep-implied --keep-prefix`. No abstraction decision required. **No
dependency on any other task.** Highest value/risk ratio in the whole programme.

**P0 — Task B: measured-baseline capture and documentation correction (Scope D).** Land §2's
baseline table into the subsystem's module documentation with the exact commands. Correct the four
adjudicated defects: `LoopChecking.lean:2001-2002` (`keysOriginS4` removal claim is FALSE),
`LoopChecking.lean:8911-8912` (stale `_boxed` references), `LoopChecking.lean:2000-2004` (resolve
the "possibly orphaned" hedge with the audit), `FrameSoundness.lean:1215-1219` (add the
zero-consumer fact and the `Massacci2000` Theorem 8.1 gap). Leave the seven **TRUE** verdicts
alone. **No dependency.** Can run in parallel with Task A.

**P0 — Task B2 (small): repair the per-repo literature index.** `specs/literature-index.json`
reports `massacci_2000_single_step_tableaux_for_modal_logics` as having **1 chunk**; the corpus
directory contains **77** (`chunk_0001`–`chunk_0077`) plus a full-text file. A `--lit` briefing
built on that entry understates the available material by two orders of magnitude, which plausibly
contributed to earlier dispatches working from relevance notes rather than the source. Run
`/literature --validate`. **No dependency.**

**P1 — Task C: THE REVIEW GATE. Abstraction decision record.** Produce a decision record adopting
or rejecting (a) box-plus birth keys and (b) the `RuleApplySt` generalization, on the evidence of
§3–§5. **This task carries the review gate the description requires. No file may be moved or
split, and no abstraction may be implemented, until Task C is reviewed and accepted.** Depends on:
nothing (this report is its input). Blocks: Tasks D, E, F, G.

**P2 — Task D: `RuleApplySt` additive introduction (steps 1–3 of §5).** Consumer audit of
`Saturation.lean` first (mandatory, per constraint). Then add `RuleApplySt` + `St` ladder as new
declarations and prove `modalExpandBranchesGen_eq_St`. **Zero risk to landed theorems by
construction** — nothing existing is edited. Depends on Task C.

**P2 — Task E: box-plus birth keys.** Add `boxPlusPair`/`BoxPlusClosed`, enrich
`successorBirthContent`, extend the two `_preserves_keyLowerBd` proofs. **Gate on
`modalTableauS4Keyed_complete` remaining green** (the one real risk, §4). Depends on Task C.

**P3 — Task F: S4 Keyed migration onto the `St` ladder (steps 4–6 of §5)** and retirement of the
duplicated `keys'` re-derivation. Depends on Tasks D and E.

**P3 — Task G: `LoopChecking.lean` split into `S4/*.lean` per §7 Seam 2** plus `ORGANISATION.md`
update. Depends on Tasks C, E, F — because the seams move if box-plus is adopted (§7 Seam 3).

**P3 — Task H: `Boneyard/` creation and the eligible moves.** Create `Boneyard/README.md`
documenting the convention (never imported by `Cslib/`; excluded from `lake build`, `mk_all`,
`lint-style`, `shake`, and all sorry/axiom censuses; retained for provenance). Move only the
**ELIGIBLE** rows of §6: `blockedRedirect_diaNeg_mem_of_diaOrigin`,
`blockedRedirect_boxctx_mem_of_boxOrigin`, the `keysRootEmpty`/`keysRootEmpty_entry` pair, and
(if Task F removes the field) the two `outDegEq` preservation lemmas. **Carry the explicit
carve-out for `FrameSoundness.lean:1220-1244`.** Re-run the consumer audit at execution time —
the audit in §6 is dated. Depends on Task F.

**P4 — Task I: CSLib vetting pipeline as acceptance gate.** Run the seven-step CI order from
`.claude/rules/cslib.md` against `CONTRIBUTING.md`, `NOTATION.md`, `ORGANISATION.md`,
`CODE_OF_CONDUCT.md`. **Note: `lake exe checkInitImports` currently fails on a stale build
unrelated to this subsystem — budget a full `lake build` first.** Depends on all above.

**Dependency ordering:**

```
Task A (dedup)  ──┐
Task B (docs)   ──┤
                  ├──> Task C [REVIEW GATE] ──┬──> Task D (RuleApplySt) ──┐
                  │                            └──> Task E (box-plus)  ───┤
                  │                                                       ├──> Task F (migrate)
                  │                                                       │      │
                  └───────────────────────────────────────────────────────┘      ├──> Task G (split)
                                                                                 └──> Task H (Boneyard)
                                                                                        │
                                                                                        └──> Task I (vet)
```

---

## Risks & Mitigations

| Risk | Likelihood | Mitigation |
|---|---|---|
| Box-plus changes which steps block, changing the computed tableau and breaking `modalTableauS4Keyed_complete` | Medium | Task E gates on `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`. If it breaks, the completeness proof is quantified over driver behaviour (`modalExpandBranchesS4Keyed_hintikka`) and should transport, but this must be demonstrated, not assumed. If it cannot be repaired sorry-free, mark Task E `[BLOCKED]` — **do not** add a sorry. |
| Editing `Saturation.lean` breaks the six true-`rfl` bridges (`modalTableauB_eq`, `modalTableauS5_eq`, `modalTableauFive_eq`, `modalTableauKb5_eq`, `modalTableauKb5''_eq`, `modalExpandBranchesB_eq`) | High if done wrong | §5's ordering makes steps 2–3 purely additive: `modalExpandBranchesGen` is never edited, so no `rfl` can break. Mandatory consumer audit precedes any edit, per constraint. |
| Deleting `S4LoopInv.outDegEq` cascades into the four other invariant proofs that destructure the structure | Medium | Task F, not Task H, owns the field removal. `lake build` before and after. If the cascade is large, keep the field and Boneyard nothing — the 386 lines are not worth a regression. |
| The §6 consumer audit goes stale between now and Task H | High (multi-task programme) | Task H **must** re-run the audit script at execution time. The audit method is recorded in §6 so it is reproducible. |
| A future reader treats the retained sorry as Boneyard-eligible because it is zero-consumer | Medium | Explicit carve-out in Task H's description naming `FrameSoundness.lean:1220-1244`. |
| Splitting `LoopChecking.lean` before the abstraction decision produces seams that immediately need re-cutting | High | Task G depends on Tasks C/E/F. This is exactly the sequencing the description mandates. |
| `Massacci2000`'s Theorem 8.1 being unproved is mistaken for a CSLib gap, or conversely a future route re-attempts reconstructing a proof from a source that lacks one | Medium | §1 records it explicitly with the deferral quote (`chunk_0054.md:3-7`) and the citation trail to Goré [20] model graphs. Task B lands this into `FrameSoundness.lean`'s documentation. |

---

## Adversarial Self-Verification

Mandatory H4 pass. Each load-bearing claim was challenged; revisions and confidence levels below.

### Challenge 1 — Does the interval theorem's nontransitivity warning actually apply to *this* guard?

**Challenged claim** (from the task description, which I was asked to evaluate): "the interval
theorem states explicitly that a relation S between S and S-bar may be NONTRANSITIVE even when the
original R is transitive, which is precisely the failure mode a subtractive or redirect-channel
design runs into."

**Verdict: NO — the "precisely" is not substantiated, and the claim should be retired.**
Confidence: **HIGH** (verbatim source obtained).

I first adjudicated this on mathematical grounds alone and then obtained the verbatim text, which
confirms the adjudication on three independent counts:

1. **There is no "interval theorem".** The passage is **unnumbered prose** following Theorem 5.23
   (Filtration), at `chunk_0246.md:43-65` / `p02:435-445` / print p. 141. Verbatim: "It is to be
   noted that a relation S between S̲ and S̄ **may** be nontransitive even if the original R is
   transitive, in particular, not all S in this interval give rise to filtrations of intuitionistic
   models." That is an **unproved authorial remark** ("It is to be noted that ... may be"), not a
   proposition, and the source supplies **no concrete counterexample frame** exhibiting such an S.
   Citing it as a theorem would be a citation defect.
2. **S̲ and S̄ are relations on the filtration quotient, so the warning is about quotients.**
   Verified from the definitions: `S̲ = {([x],[y]) : ∃x',y' (x'~x ∧ y'~y ∧ x'Ry')}` (finest),
   `S̄ = {([x],[y]) : ∀□φ ∈ Σ (x ⊨ □φ → y ⊨ φ)}` (coarsest), both over `V = {[x] : x ∈ W}` — i.e.
   `W/~_Σ` (filtration condition (i), `chunk_0245.md:18`). The obstruction actually recorded at
   `FrameSoundness.lean:1183-1190` is different in kind: `branchSatisfiableIn`'s witness model is
   **existentially arbitrary**, so `m.r`'s transitive closure after adding one edge is
   uncontrolled. That is not a quotient's relation failing to be transitive; it is an
   *unconstructed* model's relation being forced to close.
3. **The remedy the source actually gives is not what the description implies.** The description
   says "the standard remedy is the Lemmon filtration's box-plus operator." The source's remedy for
   the nontransitivity of an arbitrarily-chosen `S ∈ [S̲, S̄]` is either (a) **take the transitive
   closure of the finest filtration** (`chunk_0247.md:3-5`) or (b) **use the Lemmon filtration**
   (`chunk_0248.md:24-31`) — presented as **alternatives** at `chunk_0252.md:12-17`. So box-plus is
   one of two remedies for a problem that is not this subsystem's problem. **It remains the right
   repair for this subsystem, but for the reason established in §4 (composability of the constraint
   across an S-step), not because of the nontransitivity remark.**

**Revisions made**: §1's row now carries the verbatim text and states all three corrections
explicitly. §3 rests on Massacci Def. 10.2 / Pruning Lemma 8.2 **plus** C&Z Theorem 5.51's
containment discharge (`S_{n+1} ⊆ R_Grz`), both held verbatim. §4's justification for box-plus is
now the `chunk_0248.md:9-16` composability argument plus Corollary 5.32's explicit naming of S4 —
neither of which depends on the nontransitivity remark. **The recommendation is independent of the
interval passage.**

### Challenge 2 — Is there a documented counterargument to "just use box-plus"?

**Yes, six, now enumerated verbatim from the source in §4's counterargument table. One is decisive
against box-plus being *sufficient*; none blocks adoption.**

1. **Box-plus does not touch the reachability defect.** The code states this itself
   (`LoopChecking.lean:499-501`): "Fixing staleness alone ... does not fix the reachability
   defect." §4's residue paragraph records this. Confidence: **HIGH** (quoted from code).
2. **Box-plus collapses at most 2 of 8 bridges, not the whole set.** I checked each bridge
   individually rather than accepting the description's framing. The four `_step`/`_reflTransGen`
   bridges are Massacci Prop. 8.1 / C&Z Prop. 3.6 and are load-bearing; the two witness bridges
   are orthogonal. Confidence: **HIGH** (read each signature).
3. **The strongest documented counterargument is C1 — GL, where filtration fails for *every* Σ**
   and □⁺ is powerless because the obstruction is filtration condition (iii) forcing reflexivity
   through the quotient. **I checked whether S4 is on that side of the line and it is not**: the
   very property that kills GL (reflexivity surviving (iii)) is what S4 *wants*, and Corollary
   5.32 names S4 among the logics admitting filtration via the Lemmon construction. Confidence:
   **HIGH** (verbatim, `p02:761-768` and `chunk_0252.md:12-17`).
4. **The iterated-box-plus concern I raised in the first draft is RESOLVED NEGATIVELY.** I had
   flagged as an open item whether □⁺ might need nesting to depth > 1, which would have grown the
   codomain and broken the "free in the world bound" argument. Verbatim check: the source contains
   **no** such statement; `□⁺φ = φ ∧ □φ` is always depth-1, and where more discriminating power is
   needed C&Z **enlarge the filter Σ** (C2: `{□θ → θ, ◇□θ : θ ∈ Sub φ}` for K4.1/S4.1) rather than
   iterate □⁺. **The freeness argument therefore stands unconditionally, not just for depth-1.**
   Confidence: **HIGH** (upgraded from UNVERIFIED).
5. **C2 does surface a real design hazard I had not identified**: because CSLib's codomain is
   exactly signs × `Sub φ₀`, any future need to enrich the *filter* (as C&Z must for K4.1/S4.1/K5)
   **would** change `modalWorldBoundS4` and the pigeonhole argument. §4's table now records this so
   a planner knows filter-enrichment is expensive where □⁺-enrichment is free. Confidence: **HIGH**.
6. **C4 constrains the placement**: the Lemmon filtration is defined for transitive models only,
   via Prop. 3.6 which is also transitive-only. **So box-plus must NOT be lifted into
   `Foundations/`** as a general abstraction — it is S4-scoped. This revises where §4 places it.
   Confidence: **HIGH** (verbatim, `chunk_0248.md:24-25`, `chunk_0124.md:41`).

**Revisions made**: §4 gained a six-row counterargument table sourced verbatim; the
`modalTableauS4Keyed_complete` row remains flagged as the one real risk; the iterated-box-plus open
item is closed; the filter-enrichment hazard (C2) and the do-not-generalize constraint (C4) are new
findings this challenge produced.

### Challenge 3 — Is the "77 local re-derivations" finding real, or a grep artefact?

**Challenged**: 77 is a count of *comment strings*, not of duplicated declarations. A docstring
saying "Local re-derivation of X" could accompany a genuinely different lemma.

**Verification performed**: I spot-checked the three `modalSubfmls_trans` sites
(`S5Simplification.lean:95-97`, `FiveSimplification.lean:736`, `BDriver.lean:211`) and the four
`modalKnownWorlds_fold_spec` sites. In each case the docstring explicitly says the original is
`private` and therefore "unavailable across files", and the declaration is stated at the same
type. Independent corroboration: `FmpMeasure.lean` has **50** `private` declarations, the highest
in the subsystem after `LoopChecking.lean`'s 85.

**Verdict: the finding stands**, but the number should be read as "77 comment-attested
re-derivation sites", not "77 distinct duplicated lemmas" — several files re-derive the *same*
lemma, which is why the underlying distinct-lemma count is smaller and the *aggregate line count*
is what matters. Confidence: **HIGH** for the phenomenon, **MEDIUM** for the exact figure of 77 as
a count of anything other than comment sites. §7 now states it as comment-attested sites.

### Challenge 4 — Is `S4LoopInv.outDegEq` really zero-consumer, or did the audit miss a projection?

**Challenged**: anonymous-constructor destructuring (`⟨_, _, _, _, _, houtdeg, ...⟩`) would not
match a `.outDegEq` grep.

**Verification performed**: `modalTableauS4Keyed_initial` (`FrameCompleteness.lean:4206-4207`)
uses exactly this pattern: `refine ⟨⟨?_, List.nodup_nil, ?_, accFreshInv_empty _, ?_, ?_, ?_, ?_,
?_, ?_⟩, ...⟩`. I read it. It **provides** the ten fields (the 4th positional goal at :4217-4218
is `outDegEq`, discharged by `simp [outDeg, Accessibility.successorsOf, Accessibility.empty]`) — it
does not consume them. Positional *provision* is a third provision site the field-provision grep
missed.

**Revision made**: §6 should be read as "zero consumers, **three** provision sites"
(`LoopChecking.lean:7569`, `:7633`, and positionally at `FrameCompleteness.lean:4217-4218`).
**This raises the cost of removing the field**: Task F must also fix
`modalTableauS4Keyed_initial`'s anonymous constructor arity, which is inside the landed
completeness line. Confidence in zero-consumer status: **HIGH**. Confidence that removal is a
pure deletion: **now LOW** — it is a three-site structural change touching the landed capstone's
entry lemma. §6's "this is not a pure deletion" warning is the revised position.

### Challenge 5 — Does the `RuleApplySt` generalization actually help, or just relocate the state?

**Challenged**: threading `σ` through `modalStepBranchGenSt` still requires every preservation
lemma to reason about `σ`'s evolution. Where is the saving?

**Verification performed**: the saving is specific and quotable. Currently the guard decision is
computed **twice** — once inside `modalApplyOneS4Keyed` (`LoopChecking.lean:752`, `:756`) and once
in the stepper's `keys'` computation (`:969`, `:973`) — and the source says so explicitly at
`:951-953`. Two dedicated lemmas exist purely to relate them
(`modalStepBranchS4Keyed_result_keys_eq` at :2288, `_result_acc_eq` at :2315). With `keys'`
returned from the apply call, those become `rfl` and the correspondence disappears from every
downstream proof.

**Verdict: the saving is real and locatable.** But I have **not** measured how many of the ~85
private lemmas actually consume the correspondence, so I do **not** claim a line-count reduction
figure. Confidence that the fork is removable: **HIGH**. Confidence in the magnitude of the
payoff: **MEDIUM — unquantified.** §5 now says "this is where the line-count reduction lives"
without asserting a number.

### Challenge 6 — Am I producing analysis-only output? (H2 self-check)

The forbidden output is analysis without actionable direction. This report delivers: a 22-row
measured baseline with reproduction commands (§2); named declarations with line numbers for every
claim; a concrete Lean signature for `RuleApplySt` and for `boxPlusPair`/`BoxPlusClosed` with a
named namespace and target file (§4, §5); a six-step migration order with the risk step identified
(§5); a six-module split with source ranges (§7); a per-declaration Boneyard eligibility table with
audit method (§6); a twelve-row documentation adjudication with TRUE/FALSE/STALE verdicts (§8); and
a nine-task decomposition with an explicit dependency DAG and the review gate located at Task C.
**Assessment: not analysis-only.** No proof lines were written, which is correct — the mandate
forbids attempting the soundness obligation.

### Summary of revisions triggered by this pass

1. **§1: the interval-passage row was rewritten from "cited evidence" to "three verified
   corrections"** — it is unnumbered prose, an unproved authorial remark, and about filtration
   quotients rather than about this guard. §3 was rebuilt on Massacci Def. 10.2 / Pruning Lemma 8.2
   **and** C&Z Theorem 5.51's `S_{n+1} ⊆ R_Grz` containment discharge, both held verbatim.
2. **§1 gained four new load-bearing rows** the first draft did not have: Corollary 5.32 (the S4
   licence), (HSm1)/(HSm2) (the exact structural correspondence to `branchSatisfiableIn`),
   Proposition 3.6 (the semantic counterpart of the four bridges), and the correct location of □⁺
   (Chapter 3 p. 98, as the syntactic analogue of *reflexivization* — not `chunk_0248` as the task
   description states).
3. **§4 gained the exact "why □⁺" mechanism verbatim** (`chunk_0248.md:9-16`, composability across
   an S-step) and a six-row counterargument table. The iterated-box-plus open item is **closed
   negatively**, upgrading the freeness argument from conditional to unconditional. Two new
   findings emerged: the filter-enrichment hazard (C2) and the do-not-generalize-to-`Foundations`
   constraint (C4).
4. §6: outDegEq provision sites corrected from two to **three** (positional site at
   `FrameCompleteness.lean:4217-4218` found); "not a pure deletion" warning strengthened.
5. §7: "77 re-derivations" restated as comment-attested sites.
6. §5: line-count payoff left unquantified rather than estimated.

### BibKey verification status

| BibKey | `references.bib` | Cited in this report | Verbatim source read |
|---|---|---|---|
| `Massacci2000` | line 1010 ✓ | Yes, load-bearing | **Yes** — Defs. 8.1/8.2, Techniques 8.1/8.2/8.3/9.4/9.7, Lemma 8.2, Prop. 8.1, Lemma 9.7, Theorems 8.1/10.6, Defs. 10.2/10.3, Tables III/IV |
| `ChagrovZakharyaschev1997` | line 75 ✓ | Yes, load-bearing | **Yes** — filtration defn (i)-(iv'), Thm 5.23, the `S̲ ⊆ S ⊆ S̄` interval passage, transitive closure + □⁺ argument, the Lemmon filtration, Props 5.24/5.27, Cors 5.25/5.26/**5.32**, Thms 5.34/5.35, §5.5 opening (the GL hard failure), Lemma 5.50, **Thm 5.51**, Cor 5.52, □⁺ at Ch. 3 p. 98, **Prop. 3.6**, (HSm1)/(HSm2). Chapter-level `p02_kripke-semantics.md` section map obtained (§5.1 Henkin, §5.2 completeness, §5.3 filtration, §5.5 selective filtration). |
| `Blackburn2001` | line 65 ✓ | Cross-check only, non-load-bearing | No. **Note the doc_id/BibKey mismatch**: corpus `blackburn_2002`, BibKey `Blackburn2001`. |
| `ArisakaDasStrassburger2015` | line 939 ✓ | **Not cited** | N/A — corpus entry is `[UNVERIFIED - provenance_fidelity: unadjudicated]`, excluded per briefing footer. |
| Hughes & Cresswell 1996 | **absent** | Not cited | N/A — no BibKey exists. |

**Citation-safety notes for whoever writes Task C's decision record:**
- The Lemmon filtration and the □⁺ operator are both **unnumbered** in C&Z. Cite by chunk line and
  print page (p. 142 and p. 98 respectively), never by a fabricated definition number.
- The nontransitivity remark is **unproved prose**. Do not cite it as a theorem or proposition.
- C&Z's OCR mangles modal symbols consistently (`□`→`D`/`U`/`E`, `◇`→`O`/`0`, `φ`→`p`, and
  overlines on `S` are lost, so `S C S C 5` in the raw text is `S̲ ⊆ S ⊆ S̄`). Every quotation in
  this report was reconstructed with that mapping and the reconstruction is flagged where it
  matters.
- The per-repo literature index reports `massacci_2000...` as having **1 chunk**; it actually has
  **77** plus a full-text file. The index is wrong and `/literature --validate` should be run.

---

## Context Extension Recommendations

- `.claude/extensions/cslib/context/` has no note on the `private`-across-files pattern, which
  this subsystem shows costs 77 re-derivation sites. A short standard — "prefer `private` only for
  genuinely file-local helpers; a lemma another module will need must be public" — would prevent
  recurrence.
- No context file records that `references.bib` BibKeys can diverge from Literature-corpus
  `doc_id`s (`Blackburn2001` vs `blackburn_2002`). Worth adding to the citation-conventions file,
  since H3 BibKey verification depends on it.

## Appendix

**Audit script** (used for §6): `scratchpad/audit.py`. Classifies, per identifier, declaration
sites vs code references vs structure-field provisions vs comment-only mentions, over
`Cslib/**/*.lean` and `CslibTests/**/*.lean`, with block-comment tracking. **Known limitation
found in Challenge 4**: it does not detect positional anonymous-constructor provision.

**Reproduction commands for §2** are inline in that table's rightmost column.

**Not reproduced, with reason**: the 4-declaration/1,036-line and 43-declaration/1,983-line
amplification figures require a transitive-dependency query over the elaborated environment
(`Lean.Environment.getUsedConstants` closure from `modalTableauS4Keyed_complete`), not a text
scan. No substitute figure was fabricated.
