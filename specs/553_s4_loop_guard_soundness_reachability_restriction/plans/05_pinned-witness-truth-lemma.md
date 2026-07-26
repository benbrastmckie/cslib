# Implementation Plan: Pinned-Witness Truth Lemma for the S4 Keyed Loop Guard (v5)

- **Task**: 553 - s4_loop_guard_soundness_reachability_restriction
- **Status**: [NOT STARTED]
- **Effort**: 36-44 hours (12 phases; **four** of them are front-loaded kill gates, three in wave 1,
  any one of which terminates the route)
- **Dependencies**: 535 (completeness-line task; its landed keyed completeness results are inputs)
- **Research Inputs**:
  - `reports/01_s4-keyed-guard-soundness-falsified.md` (the machine-checked `cex`, node size 19;
    the reachability restriction's rejection at 96.7%)
  - `reports/02_redirect-inertness-divergence-audit.md` (§3.1 row 6, §5.1 — the two landed
    refutations; **§4 "R-new"**, whose boxed birth content + boxed mint payload this plan adopts)
  - `reports/03_soundness-strength-necessity.md` (§2.3, §4.2, §7 — invariant-strength census; its
    consumer-safety finding is **settled and not re-argued**)
  - `reports/04_massacci-subtractive-blocking-priced.md` (§3.4, §6, §9, §10 — route (1) priced at
    "10+ phases, large, unattempted"; §10's finding that route (2′) is route (1)'s cost paid *n*
    times)
  - `plans/03_ancestor-only-blocking.md` (`#### Phase 1 Measurements` — inherited;
    `#### Phase 2 Verdict` — the arbitrary-witness refutation, and its naming of the
    canonical/minimal-witness assumption as the alternative it could not use)
  - `plans/04_subtractive-blocking-red-channel.md` (`#### Phase 3 Verdict` — the
    unwrapped-persistence refutation; `#### Post-Gate-B Triage` — the preserved-asset inventory)
  - `summaries/06_phase3-decision-gate-b-forward-cone-blocked-summary.md`
  - Literature: `ChagrovZakharyaschev1997` (BibKey verified at `references.bib:75`),
    `Massacci2000` (`references.bib:1010`), `Simpson1994` (`references.bib:86`) — chunks read in
    this planning run, see Source-to-Implementation Mapping
- **Artifacts**: `plans/05_pinned-witness-truth-lemma.md` (this file)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/state-management.md`
  - `.claude/rules/plan-compliance.md`
  - `.claude/rules/cslib.md`
  - `.claude/rules/lean4.md`
  - `.claude/rules/no-task-references-in-deliverables.md`
- **Type**: cslib
- **Lean Intent**: true
- **Plan version**: 5 (supersedes v4 `04_subtractive-blocking-red-channel.md`, stamped
  **[ABANDONED]** with a `Superseded by` pointer to this file, per the convention v1/v2/v3 already
  use; v4's Phase 1 and Phase 2 `[COMPLETED]` status, its `#### Phase 3 Verdict`, and its
  `#### Post-Gate-B Triage` note are preserved verbatim, and the triage's kept assets are inherited
  here)

---

## Overview

The keyed S4 loop guard `blockingWorldS4Keyed` (`LoopChecking.lean:506-511`) licenses a redirect
edge `src -> wBlock` into the same `Accessibility` structure that `branchSatisfiableIn`'s edge
conjunct quantifies over (`FrameSoundness.lean:115`). Justifying that edge against a model is the
one obligation on which **four** successive routes have now died. This plan executes **route (1)**:
a driver-dependent Hintikka/canonical-model argument in which the witness model is **pinned** —
constrained by an extra conjunct inside the invariant's existential, rather than left existentially
arbitrary — at **full `branchSatisfiableIn s4FC` strength**.

**Definition of done**: a boxed-key, ordered S4 keyed driver with a machine-checked soundness
theorem against `s4FC` at full `branchSatisfiableIn` strength, a machine-checked completeness
theorem for the *same* driver, `instDecidableS4Valid` landed, a permanent regression witness that
`cex` no longer closes, every new declaration sorry-free and standard-axioms-only, and scoped CI
green at every commit. No landed driver is retired.

**Scope constraint**: file scope is `Cslib/Logics/Modal/Tableau/{LoopChecking,FrameSoundness,
FrameCompleteness}.lean` plus `CslibTests/S4LoopGuardRegression.lean` plus this task's `specs/`
directory. `Rules.lean`, `Saturation.lean`, `Branch.lean` and `SoundnessStep.lean` are
**read-only in every phase**. `Cslib/Logics/Modal/Metalogic/**` and `Cslib.lean` are out of scope
(concurrent-session territory).

**This plan does no refactoring.** No file splitting, no `modalTableauGen` unification, no
`Boneyard/` moves, no removal of the dead `outDegEq` field. That work belongs to the dedicated
refactoring task at `specs/557_modal_tableau_refactor_abstractions_boneyard`. Anything this plan's
abstraction analysis surfaces is recorded under **Notes for the Refactoring Task** below, not acted
on. Mixing the two scopes is how a proof task becomes unreviewable.

### The mechanism, stated precisely, and where it is tested

Two independent changes carry this route. Neither existed in any prior route.

**Mechanism 1 — the pinning conjunct.** Strengthen the invariant to

```lean
/-- On labels that occur on the branch, the witness relation is no LARGER than the
reflexive-transitive closure of the recorded edges. Together with the existing edge conjunct
(which is the matching lower bound) this pins `m.r` on the label image. -/
def accPinnedBy (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    {W : Type} (m : Model W Atom) (f : WorldIndex → W) : Prop :=
  ∀ w ∈ modalKnownWorlds b, ∀ w' ∈ modalKnownWorlds b,
    m.r (f w) (f w') → Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) w w'

def branchSatisfiablePinnedIn (FC : FrameCondition)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∃ (W : Type) (m : Model W Atom) (f : WorldIndex → W),
    FC m.r ∧
    (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) ∧
    accPinnedBy b acc m f ∧
    ∀ sf ∈ b,
      (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
      (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula)
```

`accPinnedBy` is exactly what plan v3's `#### Phase 2 Verdict` named as the alternative it could
not use — *"an assumption that the witness model is canonical/minimal, which `branchSatisfiableIn`'s
existential definition does not provide"* — and it is exactly the containment
`S_{n+1} ⊆ R_Grz` that `ChagrovZakharyaschev1997`'s Theorem 5.51 establishes for its
reflexive-transitive-closure model (`chunk_0267.md`). Its effect on the recurring obligation is
mechanical: the set of "ambient predecessors of `f src`" — uncontrollable, and the stated cause of
death for Route P, the origin-edge revision, and ancestor-only blocking — collapses to the set of
`acc`-ancestors of `src`, which is a set the tableau's own 4-rule has already propagated
box-positives to.

**Mechanism 2 — boxed birth content and a boxed mint payload** (report 02 §4's *R-new*, never yet
tested against this obligation). `successorBirthContent` (`LoopChecking.lean:384-391`) records the
box context **unwrapped** — `(pos, χ)` for `T(□χ)@w` — so `S4LoopInv.keyLowerBd` can only ever
recover the *unwrapped* fact at the redirect target. That single lossy projection is the documented
cause of death for route (3): v4's `#### Phase 3 Verdict` states that *"unwrapped facts have no
persistence mechanism in this tableau's Hintikka apparatus"*. Recording `(pos, □χ)` / `(neg, ◇χ)`
instead, and transmitting the boxed forms in the mint payload, makes `keyLowerBd` yield the
**wrapped** fact in three steps (report 02 §4 derives the chain; the existing
`blockedRedirect_unwrapped_*_mem` lemmas supply the unwrapped half already).

Wrapped-plus-unwrapped is not an encoding accident: it is the literature's `□⁺φ = φ ∧ □φ`, the
strengthening that makes a filtration relation transitive **by construction** rather than by an
unbounded chain induction (`ChagrovZakharyaschev1997` Lemmon filtration, `chunk_0248.md` L24-31;
the interval theorem `S_min ⊆ S ⊆ S_max`, `chunk_0246.md` L43-65, whose explicit warning is that
*"a relation S between S and S̄ may be nontransitive even if the original R is transitive"*).
Route (3) died at exactly the failure that warning predicts, and `□⁺` is the standard remedy.

**The two mechanisms compose.** With the pinning conjunct, a box-positive at any `w` whose image
`m.r`-precedes `f src` is an `acc`-ancestor's box-positive; branch saturation moves it to `src`
*wrapped*; boxed birth content moves it to `wBlock` *wrapped*; the branch conjunct then reads it as
`Satisfies m (f wBlock) (□ψ)`, which covers `wBlock`'s **entire** forward cone including points
outside the label image. That last clause is the part route (3) could not reach.

### The four kill gates, and what each falsifies

**No large construction is built before the mechanism is tested.** Phases 5-12 are *not scaffolded
on a positive verdict* and must not be dispatched until all four gates return positive.

| Gate | Phase | Wave | Question | Falsifies |
|---|---|---|---|---|
| **A** | 1 | 1 | Does adding the redirect edge preserve `branchSatisfiablePinnedIn s4FC`, given the most generous admissible hypotheses (pinning, branch saturation, wrapped transfers)? | If no: **route (1) is dead.** These hypotheses are the strongest any pinned construction could supply; no weaker pinning and no amount of construction elsewhere rescues a failure here. This is the obligation all four prior routes died on. |
| **B** | 2 | 1 | Is `modalS4Saturated φ₀ b acc` available at an **intermediate** state — specifically at a settled ordered-stepper state, where `modalNonMintCandidates φ₀ keys b e acc = []` and a blocked step can fire? | If no: Gate A's saturation hypothesis is unavailable where it is needed, and **route (1) is dead**. This is the sharpest gate: `modalHintikkaClauseGen` (`Saturation.lean`) returns `True` for *every* `box`/`diamond`-shaped formula regardless of sign, so the landed `S4KeyedHintikkaInv.hintikkaInv` supplies **nothing** for `T(□ψ)`/`F(◇ψ)` — precisely the shapes Gate A consumes. |
| **C** | 3 | 1 | Measured over the ordered + boxed driver at **every state where the guard fires** (not only at terminal open leaves): does the wrapped transfer hold, and is `modalS4Saturated`'s box-positive/diamond-negative content present? | A single failure at a reachable blocking decision **kills the route** before any proof effort. A clean result licenses **nothing** (see the measurement caveat below). |
| **D** | 4 | 2 | Is `accPinnedBy` preserved across the two **minting** shapes? Minting is the only rule that adds a label, and the naive `f v :=` (old witness point) assignment demonstrably breaks the conjunct. | If no: pinning is an assumption the fuel induction cannot carry, and **route (1) is dead**. |

**Measurement establishes truth, not provability.** This task has been burned by that gap twice:
v3's Phase 1 measured its box-propagation obligation at **1374 pass / 0 fail** and v3's Phase 2 still
died at its gate; report 04's forward-cone obligation measured **0 failures / 24,314** and v4's Gate
B still returned outcome (iii). Phase 3's numbers may only ever *kill* a design. In particular, a
clean Phase 3 must **not** be used to reorder Phases 1, 2 or 4 later, or to soften any of their
kill criteria.

### The terminal condition, stated now

**If any gate fails, this plan does not propose a fifth route.** Four routes have now failed at one
obligation, by four different mechanisms. The fourth failure — v4's Gate B verdict that unwrapped
facts have no persistence mechanism in this apparatus — is a statement about the *design*, not
about the route. If route (1) also fails at that obligation, the honest conclusion is that **the
apparatus must be restructured before the soundness obligation can be discharged at all**, and the
correct next step is to hand off to the dedicated refactoring task
`specs/557_modal_tableau_refactor_abstractions_boneyard` (`[NOT STARTED]`), which already treats the
factoring as a first-class defect and enumerates the measured evidence for it.

Because task 557 currently declares `dependencies: [553]`, that handoff requires **inverting the
dependency**: 557 must become unblocked and run first, and 553 must go `[BLOCKED]` naming 557 as its
blocker. A dispatch reaching this condition writes that as a `state_updates_pending` entry in
`.orchestrator-handoff.json` and escalates; it does **not** edit `specs/state.json` itself, and it
does **not** start a fifth route.

### Preserved Assets

Sorry-free, axiom-clean landed work that **must not regress**. Nothing in this table is retired by
this plan. Line numbers were re-derived in this planning run.

| # | Component | File | Status | Verified | Disposition under route (1) |
|---|---|---|---|---|---|
| P1 | v3 Phase 1 probe and its four measurements | `artifacts/s4ancestor.lean` (422 lines); `plans/03_*.md` `#### Phase 1 Measurements` | [COMPLETED] | 2026-07-26 | **INHERITED, not redone.** Measurement D(iv)'s 1374/1374 is explicitly **not** evidence for anything in this plan. |
| P2 | report 04's three probes, incl. the self-calibrating semantic oracle (`falsifiableUpTo`, returning least-countermodel-size **3** for `cex`, matching `LoopChecking.lean:473-476`) | `artifacts/s4subtractive.lean` (437), `s4subtractive2.lean` (228), `s4subtractive3.lean` (518) | [COMPLETED] | 2026-07-26 | **EXTENDED, not replaced.** Phase 3 extends `s4subtractive3.lean`'s `condG`/`condF`/`condGStar`/`condFStar` machinery from terminal leaves to *every blocking state*. The oracle adjudicates every verdict disagreement. **Do not write a new harness.** |
| P3 | the boxed-variant probe: `boxedShapeAt`, `sbcBoxed`, `bwBoxed`, **`mintBoxed`** (already emits the wrapped `T(□ψ)@w'` and `F(◇ψ)@w'`), `applyBoxed`, `stepBoxedOrdered` | `artifacts/s4boxed.lean` (295 lines) | [COMPLETED] | 2026-07-26 | **THE EXECUTABLE SPECIFICATION FOR PHASE 5.** Phase 5 transcribes these into `Cslib/`. Measured verdict-neutral on 8,532 formulas (closed 1650 vs 1650, `open→closed` 0, `closed→open` 0) and measured to *remove* the offending redirect on `cex` (`acc=[2→3 0→2 0→1]`, fresh world 3, no redirect). |
| P4 | `modalS4Saturated` (`:6581-6593`) + `modalHintikkaSetS4_saturated` (`:6596`) | `LoopChecking.lean` | [COMPLETED] | 2026-07-26 | **REUSE.** It is Gate A's saturation hypothesis and Gate B's conclusion. Named bare saturation conjunct; do not re-derive. |
| P5 | the six `hintikkaS4_{box_pos,dia_neg}_{self,step,reflTransGen}` bridges, hypotheses already weakened to `modalS4Saturated` | `LoopChecking.lean:6626`, `:6712`, `:6804`, `:6887`, `:7008`, `:7024` | [COMPLETED] | 2026-07-26 | **REUSE UNCHANGED.** `hintikkaS4_box_pos_step` (`:6626`) is the wrapped single-edge step; iterating it is Phase 2's `_wrapped` variant. |
| P6 | `Reds` (`:8850`), `accWithReds` (`:8857`), `hasEdge_accWithReds_iff` (`:8862`), **`reflTransGen_accWithReds_first_red`** (`:8882-8905`) | `LoopChecking.lean` | [COMPLETED] | 2026-07-26 | **KEEP; `reflTransGen_accWithReds_first_red` is likely directly useful** to Gate A's path decomposition (it is a general fact about `ReflTransGen` over a union relation, route-independent). Do not delete on the grounds that no driver uses `Reds`. |
| P7 | `blockedRedirect_unwrapped_boxPos_mem` (`:8926-8950`), `blockedRedirect_unwrapped_diaNeg_mem` (`:8958-8982`), and their verified chain `blockingWorldS4Keyed_eq_birthContent` (`:516`) → `successorBirthContent` (`:384`) → `keyLowerBd` (`S4LoopInv` field, `:7091`) → `relevantSetFinset` (`:333`) | `LoopChecking.lean` | [COMPLETED] | 2026-07-26 | **REUSE VERBATIM as the UNWRAPPED half of `□⁺`.** Phase 6's wrapped transfers are their boxed-key twins and use the identical proof chain. |
| P8 | `modalStepBranchS4Keyed_blocked_witness_mem` (`:8994-9012`, 19 lines, zero `acc`/edge mentions) | `LoopChecking.lean` | [COMPLETED] | 2026-07-26 | **REUSE.** Yields `⟨s, φ, wBlock⟩ ∈ b` from `keyLowerBd` alone; it is why `wBlock` is a known world, which Gate A needs. |
| P9 | guard + its three contract lemmas (`blockingWorldS4Keyed` `:506-511`, `_eq_birthContent` `:516`, `_none_fresh` `:538`) and the pigeonhole chain (`signedSubfmls_powerset_card_le` `:323` → `modalKnownWorlds_length_le_worldBoundS4` `:6463` → `modalStepBranchS4_worldBound` `:6501`) | `LoopChecking.lean` | [COMPLETED] | 2026-07-26 | **KEEP BYTE-FOR-BYTE.** Boxed keys change the key *values*, never the comparison (plain key equality), so `_none_fresh`, `keysDistinct` and `modalWorldBoundS4` transfer verbatim — the decisive advantage of R-new over a reachability restriction (report 02 §4; `keysDistinct` breakage measured **0/8532**). |
| P10 | `S4LoopInv` (10 fields, `:7070-7099`), `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` (`:7599`) and its 13 per-field lemmas; `S4KeyedHintikkaInv` (5 fields, `:8770-8789`), `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` (`:9194`) | `LoopChecking.lean` | [COMPLETED] | 2026-07-26 | **KEEP UNCHANGED.** Parallel `…Boxed` structures land beside them (Phases 6-7). The dead `outDegEq` field is **not** removed by this plan — see Notes for the Refactoring Task. |
| P11 | ordered stepper family: `modalNonMintCandidates` (`:873`), `modalStepBranchS4KeyedBody` (`:1005`), `modalStepBranchS4KeyedOrdered` (`:1107-1119`), `modalExpandBranchesS4KeyedOrdered` (`:7762`), `modalTableauS4KeyedOrdered` (`:7823`) | `LoopChecking.lean` | [COMPLETED] | 2026-07-26 | **KEEP as base, unchanged.** The ordered discipline is **mandatory**: the shipped ordered driver already leaves `cex` OPEN, so the empirical unsoundness is gone and only the proof remains. Boxed keys alone (unordered) still close `cex` — measured (report 02 §3.1). |
| P12 | truth-lemma apparatus: `extractModelWith` (`FC:83-88`), `extractModelS4` (`:143`), `_r` (`:148`), `_refl` (`:155`), `_trans` (`:166`), `_hasEdge_imp_r` (`:180`); `modalTruthLemmaS4` (`:232-396`, hypothesis = `modalHintikkaSetS4` only); `modalOpenBranchS4_countermodel` (`:403-410`); `modalHintikkaSetS4` (`LoopChecking.lean:6542-6562`) | `FrameCompleteness.lean`, `LoopChecking.lean` | [COMPLETED] | 2026-07-26 | **REUSE; the completeness side is intact and sorry-free.** Redirect edges are semantically harmless there — they only enlarge `ReflTransGen`. Phase 11 reuses `extractModelS4` verbatim for the boxed driver. |
| P13 | landed keyed completeness: `modalTableauS4Keyed_complete` (`FC:4267`) and its 43 dependencies | `FrameCompleteness.lean` | [COMPLETED] | 2026-07-26 | **KEEP GREEN THROUGHOUT.** Note (report 04 §4.4, re-verified here): it is for the **plain** keyed driver; there is **no** ordered-driver completeness theorem, which is why Phase 11 is real work and not a corollary. |
| P14 | S5 reuse ladder: `S5SoundSpec` (`FS:2256-2261`), `accReachableInv` (`:1816`), `reachable_imp_related_s5` (`:1840`), `accReachableInv_related_s5` (`:1858`), `S5SoundInv` (`:2536`), `modalStepBranchS5Gen_preserves_satIn` (`:2554`), `modalExpandBranchesS5Gen_closed_unsatIn` (`:3123`), `modalTableauS5Gen_sound` (`:3317`) | `FrameSoundness.lean` | [COMPLETED] | 2026-07-26 | **TEMPLATE for Phases 8-10, read in this planning run.** `S5SoundSpec`'s right disjunct — `apply sf b acc = (.linear [sf'], acc.addEdge sf.label sf'.label)` with `sf' ∈ b` — is structurally the keyed blocked arm, and its edge obligation is discharged by `accReachableInv_related_s5`. That discharge needs `s5FC`'s equivalence closure and provably does not transfer to S4; `accPinnedBy` is the S4 replacement for `accReachableInv`. |
| P15 | regression corpus (7 `#guard_msgs in #eval` rows, incl. the ordered-driver `"OPEN"` row on `cex` at `:145`) | `CslibTests/S4LoopGuardRegression.lean` (197 lines) | [COMPLETED] | 2026-07-26 | **KEEP unchanged; extended in Phase 12.** The shipped *unordered* driver's documented unsoundness is unaffected by boxed keys (measured). |
| P16 | the `sorry` at `FrameSoundness.lean:1244` in `branchSatisfiableIn_s4FC_ancestor_redirect` (`:1220-1244`) and its 30-line module comment (`:1165-1194`) | `FrameSoundness.lean` | [COMPLETED] (documented marker) | 2026-07-26 | **STAYS, per standing user decision. NO PHASE IN THIS PLAN TOUCHES IT.** It remains the only `sorry` in `Cslib/Logics/Modal/Tableau/`, and must remain exactly that at every phase boundary. Gate A's lemma is a **new declaration**, not a retargeting of this one. |

### Source-to-Implementation Mapping (H3, Tier 1 literature + Tier 3 implementation)

BibKeys verified against `references.bib` in this planning run: `ChagrovZakharyaschev1997` at
**`:75`**, `Simpson1994` at **`:86`**, `Massacci2000` at **`:1010`**, `Gore1999` at **`:1023`**. No
new BibKey is needed. Chunks read in this planning run are under
`~/Projects/Literature/{chagrovzakharyaschev_1997_modallogic,massacci_2000_single_step_tableaux_for_modal_logics,simpson_1994_intuitionisticmodallogic}/`.

**Retrieval note for implementers**: `literature-search.sh` returns **zero** hits on the
Chagrov–Zakharyaschev corpus (its `index.json` entry lacks `provenance_fidelity`, so the fail-open
policy quarantines it). Reach it with `grep`/`Read` on chunk files directly. Its OCR mangles
`□`→`U`/`D`/`O`/`n`, `◇`→`O`/`0`, `S4`→`54`, `⊢`→`b`/`F`; grep on **numbered labels** ("Theorem 5.4",
"HSm", "Hintikka", "filtration"), never on modal symbols.

| Source claim (verbatim or [reading]) | BibKey | Chunk / locus | Lean target | Translation note |
|---|---|---|---|---|
| **Hintikka system in K** = `(T, S)`, `T` a set of disjoint saturated tableaux, with **(HSm1)** *"if tSt' then ψ ∈ Γ' for every □ψ ∈ Γ"* and **(HSm2)** *"if □ψ ∈ Δ then there is t' in T such that tSt' and ψ ∈ Δ'"* | `ChagrovZakharyaschev1997` | `chagrovzakharyaschev_1997_modallogic/chunk_0135.md` L34-41 + `chunk_0136.md` L11-13 | `modalHintikkaSetS4` (**landed**, `LoopChecking.lean:6542-6562`): conjunct 2 = (S1)-(S6) + (HSm1) via `modalApplyOneS4`; conjuncts 3/4 = (HSm2) and its `◇`-dual | CSLib's clauses 3/4 are over the **raw** `acc.hasEdge`, so a redirect edge satisfies them natively — which is why the completeness side never broke |
| **Generic truth lemma over a Hintikka system** (Prop. 3.25, Cor. 3.26); CZ proves the canonical-model truth lemma (**Thm 5.4**) *only* by citing it — no induction at the canonical-model level | `ChagrovZakharyaschev1997` | `chunk_0136.md` L21-23; induction pattern `chunk_0075.md` L23-61; Thm 5.4 `chunk_0231.md` L14-33 | `modalTruthLemmaS4` (**landed**, `FrameCompleteness.lean:232-396`), whose only hypothesis is `modalHintikkaSetS4` | The landed factoring already matches the source: the truth lemma is generic over saturation, not about a particular model. Do not re-derive it |
| **Finite, formula-labelled, saturated-not-globally-maximal worlds** with bound `\|T\| ≤ 2^\|Sub φ\|` (**Thm 3.53**), and CZ's own licence at `chunk_0162.md` L5-7 to *"modify the proof of Theorem 3.53 for T and other calculi"* | `ChagrovZakharyaschev1997` | `chunk_0151.md` L11-72; licence `chunk_0162.md` L5-7 | `modalWorldBoundS4 φ₀ = 2 ^ (2 * \|modalSubfmls φ₀\|)` (**landed**, `LoopChecking.lean:229-230`) | The pigeonhole cardinality bound is the source's bound, not Massacci's depth bound. Confirms the landed world type is the literature-standard one |
| **Interval theorem**: any `S` with `S_min ⊆ S ⊆ S_max` is a filtration, where `S_max = {([x],[y]) : ∀□φ ∈ Σ, x ⊨ □φ → y ⊨ φ}`; **explicit warning** *"a relation S between S and S̄ may be nontransitive even if the original R is transitive"* | `ChagrovZakharyaschev1997` | `chunk_0246.md` L43-65 | the pair (edge conjunct, `accPinnedBy`) — the lower and upper bounds on `m.r`; the warning is the **prediction that route (3) would fail** | **The load-bearing literature finding of this plan.** Route (3) died at exactly the non-transitivity this warning names |
| **Lemmon filtration**: `[x]S[y] iff ∀□φ ∈ Σ, x ⊨ □φ → y ⊨ □⁺φ` — *"the frame is transitive and 𝔑 is a filtration"*, i.e. **transitive by construction, no chain induction** (`□⁺φ = φ ∧ □φ`) | `ChagrovZakharyaschev1997` | `chunk_0248.md` L24-31 | **boxed birth content**: `successorBirthContentBoxed` records `(pos, □χ)`; the landed `blockedRedirect_unwrapped_*_mem` supply the `φ` half — together exactly `□⁺` | The literature justification for R-new. Wrapped-plus-unwrapped is not an encoding hack; it is the standard strengthening |
| **Transitive closure of a filtration requires chain induction with the strengthened invariant**: *"there is a finite sequence [x]S[u]S…S[v]S[y] … Since R is transitive and by Proposition 3.6, u' ⊨ □⁺φ … eventually y ⊨ □⁺φ"* | `ChagrovZakharyaschev1997` | `chunk_0247.md` (whole) + `chunk_0248.md` L5-22 | Phase 2's `hintikkaS4_box_pos_reflTransGen_wrapped`, an induction carrying the **wrapped** `T(□ψ)` (not the landed `_reflTransGen`'s unwrapped conclusion) | The landed `hintikkaS4_box_pos_reflTransGen` (`:7008-7020`) stops at unwrapped `ψ`; the source says the invariant must be `□⁺`. Phase 2's variant is the missing half |
| **Selective filtration: "any relation S in the interval `S_* ⊆ S ⊆ S̄_*`, where `t S_* t'` iff either `t = t'` and `tRt'`, or `t' ∈ T_t`"** — the generated edge set is the lower bound and the licence is explicit | `ChagrovZakharyaschev1997` | `chunk_0263.md` L5-57 | `extractModelS4`'s `r := ReflTransGen (acc.hasEdge)` (**landed**, `FC:83-88`, `:143-153`) | The citation that `ReflTransGen` of the tableau's generated edges is a legitimate choice of `S`, not an ad hoc encoding |
| **Thm 5.51 (Grz)**: `S_{n+1} :=` *"the reflexive and transitive closure of `S_n ∪ {(x, y(x,□ψ))}"`*; *"It should be clear that `S_{n+1} ⊆ R_Grz` (but `S_{n+1}` is not in general the restriction of `R_Grz` to `V_{n+1}`)"*; then *"regard points x in 𝔊 as tableaux … 𝔊 will clearly be a Hintikka system"* | `ChagrovZakharyaschev1997` | `chunk_0267.md` L8-62 + `chunk_0268.md` L3-11 | **`accPinnedBy`** — the Lean form of the parenthetical: the closure is contained in, but not equal to, the ambient relation restricted to the carrier | The closest precedent in the corpus to this plan's construction. The italicised clause is precisely how the source discharges the closure/propagation interaction |
| **Prop. 8.1**: *"If the prefix σ′ is an initial subsequence of σ in the branch B, then σ′ : □A ∈ B implies σ : □A ∈ B"*, proved by *"apply rule (4) a suitable number of times"* | `Massacci2000` | `massacci_2000_.../chunk_0065.md` | `hintikkaS4_box_pos_step` (**landed**, `:6626`) iterated — Phase 2's `_wrapped` variant | The source's box-propagation is on the **wrapped** formula along the closure chain, driven by axiom 4. Confirms Phase 2's induction shape |
| **Lemma 10.5** *"SST can recover complete reduction from SST-reductions by letting a formula 'travel' along prefixes"*; for S4 *"use rule (4) for copying □A from σ to σ.n and forward. Repeat until we arrive at the immediate predecessor of σ*. Then apply rule (K)"* | `Massacci2000` | `chunk_0055.md` L9-52 + `chunk_0056.md` L5-14 | same | Names the invariant explicitly: carry `□A`, unwrap only at the end. Exactly `ReflTransGen.head_induction_on` with a wrapped invariant |
| **Thm 10.6**, the pinned model: `W = {σ : σ present in B}`, `σ R σ* iff σ ⊑_L σ*`, `V(p) = {σ : σ:p ∈ B}`; **Table VI**: `⊑_{S4}` is `σ ⊑ σ.σ′`, the initial-subsequence (reflexive-transitive) order | `Massacci2000` | `chunk_0056.md` L16-27; Table VI `chunk_0053.md` L3-14 | `extractModelS4` (**landed**) with `W := WorldIndex`, `f := id` | The source's S4 relation *is* the reflexive-transitive closure of the K edge relation. The landed extraction is a faithful transcription |
| Truth lemma, modal cases: *"If σ : ¬□A ∈ B, we have σ.n : ¬A ∈ B … `σRσ.n` **by construction**"*; *"If σ : □A ∈ B, then, by Lemma 10.5, for every σ* … σ* : A ∈ B"* | `Massacci2000` | `chunk_0057.md` L6-18 | `modalTruthLemmaS4`'s `box`/`diamond` cases (**landed**, `FC:372-396`) | The existence step is a **lookup**, not a construction, when the worlds come from a tableau. Already true of the landed proof |
| **RECORDED GAP**: *"For simplicity, we give the proof using completed branches. The extension to π-(modal)-completed branches (Section 8) can be done along the same lines of the completeness proofs in [7] … or in [20] for completeness via model graphs"* | `Massacci2000` | `chunk_0054.md` L3-7 | — | Massacci does **not** give the model construction for a *blocked* branch; he defers it to Fitting and to `Gore1999` (`references.bib:1023`), which has **no corpus**. Per the dispatch, `Gore1999` is settled and **not** a blocker and **no literature-acquisition phase is planned**: `ChagrovZakharyaschev1997` Thm 5.51's closure pattern supplies the same content and is available in full |
| Pinned Henkin witnesses `v_{y.◇A}`; *"the prime lemma can actually be proved without using any form of the axiom of choice. However, in a choice-free proof, (H,A) would have to be obtained by a laborious iterative construction"* | `Simpson1994` | `simpson_1994_.../chunk_0103.md` L3; contexts `chunk_0101.md` L3-51 | — (background) | The explicit acknowledgment that the pinned/constructive route exists and what it costs. Corpus fidelity is `ocr_rescanned_reflowed_partial_symbol_loss`; treat symbol identity with care |
| **Bounded prime lemma 8.2.4** with an explicit finite iteration (no Zorn); the four bounded-prime conditions (bounded deductive closure, consistency, disjunction property, **diamond property**) | `Simpson1994` | `chunk_0164.md` L3-25 | `modalHintikkaSetS4`'s four conjuncts | Independent confirmation that the landed four-conjunct saturation predicate is the standard one for a finite, depth-bounded, choice-free construction |
| *"the modal cases … **differ because of the definition of R**"*; *"The derivation of `A' ⊢ z:B` … **depends on the reason why `yRz` in 𝒯-Comp(H')**"* — a case split on the closure constructor, each discharged by its axiom-derived rule | `Simpson1994` | `chunk_0167.md` L3-5 | Phase 2's `ReflTransGen` induction: refl-step ⟸ T-closure (`hintikkaS4_box_pos_self`), tail-step ⟸ 4-closure (`hintikkaS4_box_pos_step`) | Confirms the two-case split the landed `_reflTransGen` bridges already use, and that the wrapped variant needs exactly the same two cases |
| Constructivity checklist: the four sites where decidability is required in a finite canonical-model proof | `Simpson1994` | `chunk_0175.md` L3-7 | — (background) | CSLib is classical (`Classical.choice` is a permitted standard axiom), so these are not obstructions here; recorded for completeness |
| Tier 3 (implementation) | — | `FrameSoundness.lean:115` — the edge conjunct is `∀ w w', acc.hasEdge w w' → m.r (f w) (f w')`, universally quantified over **all** `WorldIndex` and **branch-independent** | `accPinnedBy` deliberately quantifies over `modalKnownWorlds b` only | Read in this planning run. The asymmetry is intentional: an unrestricted upper bound would be false (`f` is total on `WorldIndex`, so unused labels would be forced equal) |
| Tier 3 (implementation) | — | `modalHintikkaClauseGen` (`Saturation.lean`) matches on `φ` alone and returns `True` for `.box _` and `.diamond _` **regardless of sign** | Gate B's necessity | Read in this planning run. This is why `S4KeyedHintikkaInv.hintikkaInv` cannot supply `T(□ψ)`/`F(◇ψ)` clauses and Gate B is a genuine gate rather than a formality |
| Tier 3 (implementation) | — | `modalStepBranchGen_preserves_satIn` (`FS:195-226`) requires `(apply …).snd = acc` in `hBoxPos`/`hDiaNeg`, and `hAgree` requires agreement with `modalApplyOne` off the two propagating shapes | Phase 10 writes a **bespoke** step lemma on the `modalStepBranchS5Gen_preserves_satIn` pattern, not an instantiation of the generic one | Read in this planning run. The keyed blocked arm violates `hAgree` at exactly the two minting shapes, so the generic ladder is not instantiable |

**Deliberate divergences from the sources, recorded rather than papered over.**
(1) CZ builds its worlds from maximal-consistent (or maximal-within-`Sub φ`) tableaux; CSLib's worlds
are tableau-generated and only *downward* saturated. CZ's own §5.3 preamble
(`chunk_0244.md` L5-56) states the gap and its remedy — passing to a finite Hintikka system requires
**only** (HSm1) and (HSm2), with *"a spectrum of suitable S"* — so the divergence is licensed, not
elided. (2) `◇` is **not primitive** in CZ (`chunk_0115.md` L5-7: `◇φ := ¬□¬φ`), so CZ states only
two modal saturation clauses; CSLib has `◇` primitive and therefore needs the two mirror clauses
(`◇`-positive existence, `◇`-negative propagation). The landed `modalHintikkaSetS4` already has
them. **This is an extension of the source, not a quotation, and every diamond-side lemma in this
plan is the dual of a cited box-side claim rather than a citation in its own right.**

### Notes for the Refactoring Task (recorded, not acted on)

For `specs/557_modal_tableau_refactor_abstractions_boneyard`. None of these is in this plan's scope.

1. **The wrapped-versus-unwrapped distinction the four routes discovered the hard way has a name in
   the literature**: it is `□⁺φ = φ ∧ □φ`, and the relation defined by it is the **Lemmon
   filtration** (`ChagrovZakharyaschev1997` `chunk_0248.md` L24-31), transitive by construction.
   That task's scope item A asks whether the distinction "deserves to be an explicit abstraction (a
   persistence-carrying predicate)"; the answer is yes, and the abstraction already exists in the
   source with a name and a standard-form definition.
2. **A principled alternative to `extractModelS4`'s `ReflTransGen`**: define the model relation *as*
   the box-condition, `r w w' := ∀ φ, T(□φ)@w ∈ b → (T(□φ)@w' ∈ b ∧ T(φ)@w' ∈ b)` (Lemmon; also
   `Massacci2000`'s `⊑_{S4}`, Table VI, `chunk_0053.md`). Then (HSm1) holds **by definition** with
   zero proof and reflexivity/transitivity are free, moving all cost to (HSm2), which is *easier*
   because the generated edges are contained in it. This plan does not take that route because it
   would replace `extractModelS4` and break the landed completeness line — but it is the cheaper
   design if a restructuring is on the table.
3. **The S5/S4 asymmetry is the seam the module division should surface.** `accReachableInv` +
   `reachable_imp_related_s5` (`FrameSoundness.lean:1816`, `:1840`, `:1858`) derive model relatedness
   from a *structural* invariant plus the frame condition, because `s5FC`'s equivalence closure does
   the work. No S4 analogue can exist: common reachability from `0` gives `m.r (f 0) (f src)` and
   `m.r (f 0) (f wBlock)`, and without symmetry that yields nothing about `(f src, f wBlock)`. S4
   therefore needs a constraint *on the witness model* where S5 needs only one on `acc`. That is a
   real abstraction boundary, and the ten-bridge adapter cluster the task cites as evidence (2) sits
   exactly on it.
4. **`references.bib:1010`'s `note` on `Massacci2000` is stale** — it says the PDF is not yet
   acquired (paywalled), but `~/Projects/Literature/massacci_2000_single_step_tableaux_for_modal_logics/`
   holds 77 chunks of full text. `Gore1999` (`references.bib:1023`) genuinely has no corpus, and
   `Massacci2000` `chunk_0054.md` L3-7 defers the blocked-branch model construction to it — worth
   recording as a known, closed grounding gap rather than an open one.
5. **Corpus retrieval defect**: `~/Projects/Literature/index.json`'s entry for
   `chagrovzakharyaschev_1997_modallogic` lacks `provenance_fidelity`, so `literature-search.sh`
   fail-open-quarantines the single most relevant reference in the library and returns zero hits on
   it. That is a literature-extension defect, not a modal-tableau one, but it cost real time in this
   planning run.
6. **`outDegEq` remains dead and remains in place.** Re-verified in this planning run: provided at
   two sites, consumed nowhere in the S4 line. This plan drops it only by *never carrying it into*
   `S4LoopInvBoxed`, leaving the landed `S4LoopInv` and its 188-line preservation lemma untouched.
   Actual removal is that task's call.

---

## Postmortem Constraints

Binding on every implementation dispatch under this plan.

### What structural property of route (1) prevents a fifth recurrence — and what would falsify it

**Four routes have failed at one obligation, by four different mechanisms.**

| Route | Mechanism of failure |
|---|---|
| Route P (settled-context scheduling), v1/v2 | redirect-inertness lemmas machine-checked **FALSE** at a reachable state (report 02); removed |
| Origin-edge invariant revision, v2 | abandoned |
| Ancestor-only blocking, v3 | `branchSatisfiableIn`'s witness model is **existentially arbitrary**, so extending `m.r` forces an uncontrollable transitive closure over ambient predecessors of `src` (v3 `#### Phase 2 Verdict`) |
| Subtractive blocking + `red` channel, v4 | the free transfer yields only an **unwrapped** branch fact at the redirect target, and unwrapped facts have **no persistence mechanism** in this apparatus (v4 `#### Phase 3 Verdict`) |

A fifth — the reachability restriction — was rejected in report 01 before it was ever planned
(96.7% of blocking decisions target a non-reachable world, so the world bound fails).

**The structural claim.** All four failures are instances of one shape: *a fact had to reach a point
whose relationship to the recorded structure was not determined by the recorded structure.* Routes
P, the origin-edge revision, and ancestor-only failed **backwards** — on ambient predecessors of
`f src`, points the invariant could not see. Route (3) failed **forwards** — on `wBlock`'s forward
cone, points the `keys`/`red` bookkeeping could not reach. Route (1) closes both directions with two
mechanisms:

- `accPinnedBy` closes the **backward** direction by construction. It is the statement that there
  are no untracked relationships: `m.r (f w) (f w')` between branch labels implies
  `ReflTransGen acc w w'`. "Ambient predecessor of `f src`" becomes "`acc`-ancestor of `src`", and
  `acc`-ancestors are a set the tableau's own 4-rule has already propagated to. It is the containment
  `ChagrovZakharyaschev1997` Thm 5.51 establishes (`chunk_0267.md`) and the assumption v3's Phase 2
  Verdict named as the alternative it could not use.
- Boxed birth content closes the **forward** direction by making the transfer at `wBlock`
  **wrapped**, so `Satisfies m (f wBlock) (□ψ)` covers the whole forward cone — including points
  outside the label image, which is exactly what no branch-membership argument can reach.

**What falsifies the claim, concretely.** Each of the four gates is a falsifier, and each has a
written kill criterion in its phase:

1. Gate A fails ⟹ the composition does not close the obligation even under the most generous
   hypotheses, so no weaker pinning and no further construction helps.
2. Gate B fails ⟹ `modalS4Saturated` is not available at the intermediate states where blocked
   steps fire, so the pinning-to-wrapped step has no premise. This is the likeliest failure: the
   landed `hintikkaInv` returns `True` for every box/diamond-shaped formula, and report 02 §5.1's
   late-`T(□ψ)` mint-chain counter-shape is a concrete candidate counterexample.
3. Gate C measures a failure of the wrapped transfer or of box-positive saturation at a reachable
   blocking decision ⟹ the mechanism is false, not merely unproven.
4. Gate D fails ⟹ `accPinnedBy` is not preservable, so mechanism 1 is an assumption the fuel
   induction cannot carry, and route (2′)'s "route (1)'s cost paid *n* times" verdict (report 04 §10)
   applies to route (1) itself.

**And the honest caveat, which is the part that matters.** *Three prior postmortems each claimed to
have identified the structural fix, and each was wrong.* v1/v2's postmortem identified redirect
inertness; the lemmas were machine-checked false. v3's identified target restriction; the obstruction
was about the witness model, not the target. v4's identified moving the edge out of the
soundness-tracked structure; the obligation followed it into the completeness side and died there.
The specific reasons to distrust *this* postmortem:

- Mechanism 2 is a **refinement of Route P's diagnosis**, not a departure from it. Report 02
  recommended R-new as Route P's bounded modification and the user chose a different option, so
  R-new has **never been tested against this obligation**. Its measured verdict-neutrality
  (8,532 formulas, `open→closed` 0) says nothing about provability.
- Mechanism 1 is precisely the option v3's Phase 2 Verdict named and **explicitly did not attempt**.
  Its preservation across minting is unproven, and the naive assignment demonstrably breaks it
  (Gate D exists because of this, not as a formality).
- Gate B's premise is that ordered scheduling supplies saturation at intermediate states. **That is
  Route P's central idea in a weaker form.** The distinguishing property — Route P's dead lemmas
  claimed a specific *wrapped fact at `wBlock`*, whereas Gate B claims *branch saturation at the
  current state*, a different statement derived from a landed invariant — is real, but it is a
  distinction of statement, not of family, and it should be read with the base rate in mind.

Given four failures out of four, the base rate says a gate will fire. **That is the expected
outcome, and the plan is built to reach it cheaply rather than to avoid recording it.**

### Do NOT

- **Do NOT leave a `sorry` standing at a decision gate (Phases 1, 2, 4).** A `sorry` at a gate stands
  in for a possibly-false statement — the exact failure this task has suffered twice (v2's removed
  inertness lemmas; v3's `:1244`). At a gate, if the proof does not close, **revert the attempt** and
  record the exact `lean_goal` state in this plan's verdict subsection. Do not commit the sorry. A
  strategic-sorry skeleton remains a legitimate *mid-phase recovery* move inside a **non-gate** phase
  and must be discharged before that phase is marked `[COMPLETED]`.
- **Do NOT touch `FrameSoundness.lean:1244`** or `branchSatisfiableIn_s4FC_ancestor_redirect`
  (`:1220-1244`) or its module comment (`:1165-1194`). It stays by standing user decision. Gate A's
  lemma is a **new declaration** with a different name and a different hypothesis list. The sorry
  census in `Cslib/Logics/Modal/Tableau/` must be **exactly 1** at every phase boundary.
- **Do NOT retarget to `branchPropAdequateIn`, and do not re-argue it.** Report 03 established that
  weakening would be safe for every consumer (repo-wide census: zero occurrences outside
  `FrameSoundness.lean`; all six landed `Decidable` instances consume only
  `modalTableauX φ = .closed ↔ xValid φ`). The user has chosen full strength. **Closed.** In
  particular, a phase that finds Gate A hard must not quietly substitute the weak invariant — that is
  the specific silent-retarget this constraint exists to forbid.
- **Do NOT weaken `accPinnedBy` to make a proof close** without recording the weakening as an
  explicit design change in this plan's phase text, with the new statement written out and its effect
  on every downstream phase named. An invariant silently weakened mid-plan is how v1's Phase 13 came
  to depend on a non-exhaustive case split (report 02 §5.1).
- **Do NOT adopt `accPinnedBy`'s box-condition form (`P2`) as the primitive invariant.** It was
  considered at plan time and **rejected with a reason**: the box-condition
  `m.r (f w) (f w') → ∀ψ, T(□ψ)@w ∈ b → (T(□ψ)@w' ∈ b ∧ T(ψ)@w' ∈ b)` is **not monotone in `b`** —
  the 4-rule adds `T(□ψ)@w` only at direct `acc`-edge targets, while `m.r` may relate `f w` to
  strictly more label images, so the antecedent set grows faster than the consequent. It is carried
  as a **derived consequence** (`accPinnedBy` + Gate B's saturation) instead. Re-proposing it as
  primitive requires refuting this argument first.
- **Do NOT re-propose** any of: the three removed false lemmas (`blockedRedirect_boxctx_mem`,
  `blockedRedirect_diaNeg_mem`, `blockedRedirect_propAdequate` — see the removal notes at
  `LoopChecking.lean:2000`, `:2021-2036` and `FrameSoundness.lean:1315-1321`, `:1534-1547`); the
  reachability restriction; ancestor-only blocking; redirect inertness in any form; route (2′)'s
  disjunctive edge conjunct; route (3)'s `red` channel as a soundness-side mechanism.
- **Do NOT use the unordered stepper.** Boxed keys alone do **not** fix the driver: measured,
  `closesBoxed false cex 400 = some true` — the boxed **unordered** driver still closes `cex`
  (report 02 §3.1). `modalStepBranchS4KeyedBoxedOrdered` is mandatory.
- **Do NOT state the diamond-negative or box-positive transfer in the wrapped-formula-only form
  without the unwrapped half.** The target is `□⁺` — wrapped **and** unwrapped. Report 04 §6.4
  measured the wrapped-only proxy (condition (d)) failing **40 times out of 24,314**; the unwrapped
  half (conditions (c)/(e)) is 0/24,314 and is already landed as
  `blockedRedirect_unwrapped_*_mem`. Both halves, or neither.
- **Do NOT treat a measurement as a proof.** v3's Measurement D(iv) was 1374/1374 and the route died;
  report 04's forward-cone obligation was 0/24,314 and route (3) died. Probe results in this plan are
  gates that can only ever *kill* a design, never license one, and never license a reordering of
  phases.
- **Do NOT modify `Cslib/Logics/Modal/Tableau/Rules.lean`** — `modalApplyOne` is shared with
  K/T/B/S5 and with `FmpMeasure.lean`'s `_gen` lemmas. The boxed mint arm belongs in the S4-keyed
  layer, replacing the `modalApplyOne sf b acc` fallthrough at `LoopChecking.lean:754`/`:758` (which
  is exactly what `artifacts/s4boxed.lean`'s `applyBoxed` does).
- **Do NOT modify `Cslib/Logics/Modal/Tableau/Saturation.lean`.** `ModalTableauResult` is consumed by
  8 files and carries only `(b, acc)`. It is also where `modalHintikkaClauseGen` and
  `modalHintikkaSetGen` live; Gate B must work *around* `modalHintikkaClauseGen`'s box/diamond `True`
  clauses, not edit them.
- **Do NOT modify `Cslib/Logics/Modal/Tableau/Branch.lean` or `SoundnessStep.lean`.** Both are
  read-only inputs.
- **Do NOT edit any landed declaration in-place except by strict hypothesis-weakening**, and verify
  any such weakening with a scoped build of every importer.
- **Do NOT do any refactoring.** No file splitting, no `modalTableauGen` unification, no `Boneyard/`,
  no deletion of `outDegEq` or of the orphaned `keysOriginS4` family. Record it under Notes for the
  Refactoring Task and move on.
- **Do NOT compress Phases 1, 2 and 3 into one dispatch, and do not reorder them behind Phase 5.**
  They are wave 1 precisely so that the likeliest-fatal facts are established before any construction
  exists to protect.
- **Do NOT weaken, vacuously restate, or `True`-stub any statement.** `def X := True`,
  `theorem X := trivial` and friends are prohibited (`.claude/rules/cslib.md`).
- **Do NOT state a claim about driver behaviour, or an "the invariant already gives us X" step,
  without checking it against the actual definitions in the same dispatch.** v1, v2, v3 and v4 all
  blocked on this shape. Every phase below carries its verification inside the phase.
- **Do NOT cite task numbers in any file outside `specs/**`** (`.claude/rules/no-task-references-in-deliverables.md`).
  Docstrings in `Cslib/` and `CslibTests/` reference declaration names and this plan's *content*,
  never "task 553".

### MUST preserve

- Every row of the Preserved Assets table at its stated disposition. In particular: `blockingWorldS4Keyed`
  and its three contract lemmas **byte-for-byte unchanged**; `modalTableauS4Keyed_complete` green at
  every commit; the six landed `Decidable` instances (K/T/B/S5/Five/KB5) green at every commit; the
  `sorry` at `FrameSoundness.lean:1244` untouched.
- **Sorry count in `Cslib/Logics/Modal/Tableau/` stays at exactly 1** at every phase boundary. Verify
  with `grep -rn '\bsorry\b' Cslib/Logics/Modal/Tableau/*.lean` and discount the ten known docstring
  mentions (`LoopChecking.lean:2022`, `:7536`, `:8841`, `:8914`; `GenericDriver.lean:62`;
  `S5Simplification.lean:1816`; `FrameCompleteness.lean:578`; `FrameSoundness.lean:1193`, `:1215`,
  `:1685`).
- **Zero new axioms.** Do **not** hard-code a repo axiom count: the raw `grep -rn '^axiom' Cslib/ | wc -l`
  census read **47** across 37 files in a prior planning run, which contradicts the "26" asserted by
  v3. Capture the baseline with the exact command at the start of each phase, require byte-equality at
  the end, and run `lean_verify` on every new top-level declaration, requiring only `propext`,
  `Classical.choice`, `Quot.sound`.
- **Scoped builds, not full-project builds.** A full-project `lake build` currently fails on
  `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` — concurrent work, unrelated to
  this plan and untouched by it. Every phase verifies with
  `lake build Cslib.Logics.Modal.Tableau.{LoopChecking,FrameSoundness,FrameCompleteness}` plus
  `lake build CslibTests.S4LoopGuardRegression` where relevant, plus `lake exe lint-style` on each
  touched file and scoped `lake shake --add-public --keep-implied --keep-prefix`. Phase 12 attempts
  the full pipeline and records, rather than works around, any residual concurrent breakage.
- The measured facts from the probes in `artifacts/`. Any dispatch that changes a driver **re-runs**
  the differential sweep rather than reasoning about what it would produce.
- Commit at every green sub-step, per `.claude/rules/git-workflow.md`'s commit-per-green-substep
  mandate. Stage only the task directory plus the specific `Cslib/` and `CslibTests/` files touched.

### Design decisions are SETTLED (do not re-open without a concrete, machine-checked counterexample)

1. **Keyed S4 soundness as originally stated is FALSE** — report 01, machine-checked `cex`, node size
   19, explicit 3-world reflexive-transitive countermodel, and the least-countermodel-size oracle
   independently returns 3.
2. **The reachability restriction is REJECTED** — 96.7% of blocking decisions target a non-reachable
   world, so the world bound becomes false, not merely unproven (report 01).
3. **`blockedRedirect_boxctx_mem` / `_diaNeg_mem` / `_propAdequate` are FALSE at a reachable
   (transient) state** (report 02) and have been removed.
4. **Ancestor-only blocking does not close** (v3 `#### Phase 2 Verdict`).
5. **Subtractive blocking + a `red` channel does not close** (v4 `#### Phase 3 Verdict`, outcome
   (iii)).
6. **Weakening to `branchPropAdequateIn` would be SAFE for every consumer** (report 03) — the user
   has chosen full strength. **Closed. Do not re-argue and do not silently retarget.**
7. **Route (2′) is not cheaper than route (1)**: its preservation obligation requires constructing a
   new witness model at *every intermediate state inside the fuel induction* — route (1)'s cost paid
   *n* times, over an existentially arbitrary ambient witness (report 04 §10). It is not a fallback.
8. **Termination is not at risk from the guard.** The pigeonhole chain
   (guard → `keysDistinct` → `modalWorldBoundS4`) is edge-independent, and boxed keys keep the
   comparison at plain key equality so `blockingWorldS4Keyed_none_fresh` transfers verbatim.
   `keysDistinct` breakage measured **0/8532**. Massacci's depth bound (Prop. 8.2 / B.5) is **not**
   imported.
9. **The shipped ordered driver already leaves `cex` OPEN.** The empirical unsoundness is gone; only
   the proof remains. That affects urgency framing only — it is **not** a licence to reduce scope, and
   the soundness theorem is still absent (verified: no `modalTableauS4Keyed_sound`, no
   `modalExpandBranchesS4Keyed_closed_unsatIn`, no S4 step-preservation lemma exists anywhere).
10. **`Gore1999` is settled and is not a blocker. No literature-acquisition phase.**
11. **The boxed driver lands as a PARALLEL definition family** (`…Boxed…`), per this file's own
    convention (`LoopChecking.lean:459-464`, `:990-996`). No landed driver is retired.
12. **`outDegEq` is dropped by omission, not by deletion** — it is simply never carried into
    `S4LoopInvBoxed`. The landed `S4LoopInv` and its 188-line preservation lemma stay untouched.

---

## Goals & Non-Goals

**Goals**

- Establish, or refute, that a pinned witness model discharges the redirect-edge soundness obligation
  at full `branchSatisfiableIn s4FC` strength — as cheaply and as early as possible.
- If established: land `modalTableauS4KeyedBoxedOrdered_sound`, a completeness theorem for the same
  driver, and `instDecidableS4Valid`, all sorry-free and standard-axioms-only.
- Land `accPinnedBy` / `branchSatisfiablePinnedIn` as named, literature-grounded abstractions with
  docstrings citing the sources.
- Extend the executable regression corpus so that every verdict this plan relies on is reproducible.

**Non-Goals**

- Any refactoring, file splitting, module reorganisation, `Boneyard/` creation, or documentation-debt
  discharge beyond docstrings on declarations this plan writes. That is task 557's scope.
- Removing or retargeting `FrameSoundness.lean:1244`'s `sorry`.
- Weakening the soundness invariant to `branchPropAdequateIn`, or to route (2′)'s disjunctive form.
- Retiring the plain or unordered keyed drivers, or their landed completeness line.
- Proposing a fifth route if route (1) fails.
- Acquiring `Gore1999`.
- Extending the mechanism to the non-reflexive transitive corners (K4/K45/D4/D45). Note in passing,
  verified by reading: full-strength `branchSatisfiableIn` needs **no** reflexivity in the 4-rule
  lemmas (`FrameSoundness.lean:1085-1100` and `:1106-1123` destructure `hrefl` and never use it), so
  those corners are not obstructed by this plan — but they are not its work.

## Risks & Mitigations

- **Risk: Gate B fails, because `modalHintikkaClauseGen` returns `True` for box/diamond shapes and
  so the landed `hintikkaInv` supplies nothing at `T(□ψ)`/`F(◇ψ)`.** *Likelihood: high — this is the
  single most likely failure in the plan.* Mitigation: Gate B is in wave 1, is bounded to one
  dispatch, and has a written three-outcome protocol including a "name the exact missing invariant"
  branch. Phase 3 measures the same question decidably and in parallel, so a refutation can arrive
  from either side.
- **Risk: Gate B's premise is Route P's central idea in weaker form, and Route P died.** Mitigation:
  the distinguishing property is stated explicitly in the Postmortem Constraints and must be
  re-checked in Gate B's verdict, not assumed. Report 02 §5.1's late-`T(□ψ)` mint-chain counter-shape
  is named in Phase 3's task list as a *specific* thing to search for.
- **Risk: Gate A's branch conjunct requires a model-agreement induction that does not close.**
  Mitigation: Phase 1's deliverable is **split** so that the three mechanical conjuncts (frame
  condition, edge, pinning) land sorry-free and reusable — real progress, and strictly more than
  v3's Phase 2 reached — while the branch conjunct is the verdict. The extension relation and its
  transitivity proof are written out in the phase text so the dispatch does not have to invent them.
- **Risk: Gate D fails and `accPinnedBy` is unpreservable at mint steps.** Mitigation: the phase text
  names the intended construction (fresh-point duplication with a bisimulation-style agreement
  argument, which is the standard tree-unravelling move) and the specific reason the naive assignment
  fails, so the dispatch starts from the right place. If it fails, route (1) is dead — stated.
- **Risk: boxed keys change the guard's decisions on some formula and regress completeness.**
  Mitigation: measured verdict-neutral on 8,532 formulas with `open→closed` = 0 and `closed→open` = 0;
  Phase 3 re-runs the differential on all three corpora; Phase 12 re-runs it against the landed Lean
  driver rather than the probe. Note the caveat: measurement kills, never licenses.
- **Risk: Phase 11 (completeness for the boxed ordered driver) is larger than budgeted, because there
  is no ordered-driver completeness theorem to adapt.** *Verified: `modalTableauS4KeyedOrdered` has
  neither a soundness nor a completeness theorem.* Mitigation: an explicit sub-phase split rule
  (11.1/11.2) inside the phase, and the phase is last so a split does not disturb anything upstream.
- **Risk: a full-project `lake build` cannot be used as a gate.** Mitigation: scoped builds
  throughout, enumerated in MUST preserve; Phase 12 attempts the full pipeline and records residual
  concurrent breakage rather than working around it.
- **Risk: the plan's 12 phases invite scope creep back toward refactoring.** Mitigation: an explicit
  Do NOT, a Non-Goal, and a Notes for the Refactoring Task section that gives every such finding a
  place to go that is not this plan.

---

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1, 3 |
| 3 | 5 | 1, 2, 3, 4 |
| 4 | 6 | 5 |
| 5 | 7, 8 | 6 |
| 6 | 9 | 8 |
| 7 | 10 | 1, 4, 7, 9 |
| 8 | 11, 12 | 10 |

Phases within the same wave can execute in parallel.

**Territory contracts for parallel dispatch (H7).** No two phases in the same wave write the same
file — this plan has **no** same-file parallelism at all.

| Wave | Phase | Owns (write) | Read-only |
|---|---|---|---|
| 1 | 1 | `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (new section, appended at end of file) | everything else |
| 1 | 2 | `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (new section, appended at end of file) | everything else |
| 1 | 3 | `specs/553_.../artifacts/s4pin.lean` (new), `artifacts/s4boxed.lean`, `artifacts/s4subtractive3.lean` | all of `Cslib/**`, `CslibTests/**` |
| 2 | 4 | `FrameSoundness.lean` (Phase 1's section, extended) | — |
| 3 | 5 | `LoopChecking.lean` (new boxed-driver section) | — |
| 4 | 6 | `LoopChecking.lean` (new boxed-invariant section) | — |
| 5 | 7 | `LoopChecking.lean` (boxed Hintikka-invariant section) | `FrameSoundness.lean` |
| 5 | 8 | `FrameSoundness.lean` (pinned-invariant endpoints section) | `LoopChecking.lean` |
| 6 | 9 | `FrameSoundness.lean` (per-step section) | — |
| 7 | 10 | `FrameSoundness.lean` (spec + capstone section) | — |
| 8 | 11 | `FrameCompleteness.lean` (boxed assembly section) | `CslibTests/**` |
| 8 | 12 | `CslibTests/S4LoopGuardRegression.lean`, `specs/553_.../artifacts/` | all of `Cslib/**` |

Every dispatch re-reads its owned file immediately before its first `Edit`. If a dispatch finds the
file changed under it, it serialises rather than merging.

**Note on phase count (H8 deviation, declared per phase).** Twelve phases exceeds the 8-phase ceiling
this planner applies to "complex" tasks. The excess is deliberate and each phase independently passes
the bounded-unit test — one definition family, one lemma family, or one measurement, each with a
concrete stopping condition stated in its own text, each estimated at ≤ ~450 lines with an explicit
split rule where it approaches that.

- **Phases 1-4 (four kill gates) are four phases, not one.** They test four logically independent
  facts, in three different files, with four different kill criteria and four different fallbacks.
  Merging any two would hide one behind the other and defeat the front-loading, which is the single
  most valuable structural property of the plan given four prior failures. Splitting them is
  precisely what lets three of them run in wave 1.
- **Phases 5-7 (boxed driver, boxed invariant, boxed Hintikka invariant) are three phases** because
  report 02 §4 prices the R-new change at 4-6 phases and enumerates the re-proof obligations
  (`successorBirthContent_*_subset_relevantSetFinset`, `_subset_signedSubfmls`,
  `modalApplyOne_boxNeg_outputs_subset_S4` and its twin, the mint arms of both preservation theorems).
  Three is at the low end of an independent pricing, not inflation.
- **Phases 8-10 (endpoints, non-mint preservation, capstone) mirror the landed S5 ladder's own
  division** — `S5SoundInv` + endpoints, the per-shape work, then
  `modalStepBranchS5Gen_preserves_satIn` (536 lines) / `modalExpandBranchesS5Gen_closed_unsatIn` /
  `modalTableauS5Gen_sound`. Merging them would produce a single phase well over 800 lines.
- **Phase 11 (completeness + decidability) is separate** because it is the only phase in
  `FrameCompleteness.lean` and because there is verifiably **no** ordered-driver completeness theorem
  to adapt, making it independently sizeable. It carries an internal 11.1/11.2 split rule.
- **Phase 12 (empirical regression + CI) is separate** because it is a measurement in a different
  territory (`CslibTests/`, `artifacts/`) that must be re-runnable independently of any proof phase,
  and because it is the only phase that attempts the full CI pipeline.

**A skeleton plan with strategic-sorry division points was considered and REJECTED.** The four
riskiest obligations are Phases 1-4, so there is no long green prefix to skeletonise; and a strategic
sorry at any gate would be a sorry standing in for a possibly-false statement — the exact failure
this task has suffered twice. `plan_metadata.skeleton` is `false` and there is no
`## Planned Strategic Sorries` section.

---

### Phase 1: DECISION GATE A — the pinned redirect-preservation lemma [NOT STARTED]

- **Goal:** Define `accPinnedBy` and `branchSatisfiablePinnedIn`, and determine whether adding the
  redirect edge preserves the latter under the strongest hypotheses any pinned construction could
  supply. This is the obligation all four prior routes died on.
- **Estimated output:** ~250 lines (definitions ~35, the three mechanical conjuncts ~120, the branch
  conjunct attempt ~100).
- **Depends on:** none.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, new section appended at end of file.
- **Timing:** 3 hours.

- **Tasks:**
  - [ ] Append a section-level module comment stating the two mechanisms, citing
        `ChagrovZakharyaschev1997` Thm 5.51 (`chunk_0267.md`) for the containment
        `S_{n+1} ⊆ R_ambient` and the interval theorem (`chunk_0246.md` L43-65) for why an upper
        bound on the model relation is the literature-standard device. Cite declaration names and
        source labels; **no task numbers**.
  - [ ] `def accPinnedBy` and `def branchSatisfiablePinnedIn` exactly as written in the Overview.
        Record in the docstring why the quantification is over `modalKnownWorlds b` and not over all
        `WorldIndex` (`f` is total, so an unrestricted upper bound would force unused labels equal),
        and why the box-condition form was rejected as primitive (not `b`-monotone; see Postmortem
        Constraints).
  - [ ] State the gate lemma. Hypotheses, in this exact shape:
        ```lean
        lemma branchSatisfiablePinnedIn_s4FC_redirect
            {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
            {φ₀ : Proposition Atom} {src wBlock : WorldIndex}
            (h : branchSatisfiablePinnedIn s4FC b acc)
            (hsrc : src ∈ modalKnownWorlds b) (hwB : wBlock ∈ modalKnownWorlds b)
            (hsat : modalS4Saturated φ₀ b acc)
            (hbox : ∀ ψ, (⟨.pos, .box ψ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
                      (⟨.pos, .box ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
            (hdia : ∀ ψ, (⟨.neg, .diamond ψ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
                      (⟨.neg, .diamond ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
            branchSatisfiablePinnedIn s4FC b (acc.addEdge src wBlock)
        ```
        `hbox`/`hdia` are the **wrapped** transfers Phase 6 discharges from boxed birth content;
        `hsat` is Gate B's conclusion. Nothing stronger is admissible, so a failure here is final.
  - [ ] **Sub-step 1.1 (must land sorry-free and be committed on its own).** The extension relation
        and the three mechanical conjuncts:
        - `r' := fun x y => m.r x y ∨ (m.r x (f src) ∧ m.r (f wBlock) y)`; `m' := { r := r', v := m.v }`.
        - `Std.Refl r'` from the left disjunct.
        - `IsTrans _ r'` by the four-case split. All four close from `htrans.trans` and `hrefl.refl`:
          (new,new) takes the right disjunct with the outer endpoints; (new,old) and (old,new) compose
          one `m.r` step into the surviving component.
        - Edge conjunct over `acc.addEdge src wBlock` via a local re-derivation of
          `hasEdge_addEdge_cases` (the same pattern as the existing private
          `hasEdge_addEdge_cases_anc`, `FrameSoundness.lean:1199-1206`): the new pair takes the right
          disjunct with two reflexivity witnesses; old edges take the left.
        - `accPinnedBy b (acc.addEdge src wBlock) m' f`: left disjunct via the old `accPinnedBy` plus
          `ReflTransGen` monotonicity in `acc`; right disjunct by composing
          `ReflTransGen acc w src`, the new edge `src → wBlock`, and `ReflTransGen acc wBlock w'`.
          `reflTransGen_accWithReds_first_red` (`LoopChecking.lean:8882`) may be reusable for the
          decomposition; if it is, say so in the docstring, and if it is not, say why.
  - [ ] **Sub-step 1.2 (the verdict).** The branch conjunct: `∀ sf ∈ b`, satisfaction with respect to
        `m'`. Because `m.r ⊆ r'`, box-positive and diamond-negative satisfaction is **not**
        automatically preserved. The intended route is an agreement lemma restricted to
        `modalSubfmls φ₀` (every branch formula lies there by `S4LoopInv.bClosure`, and
        `modalSubfmls` is subformula-closed): prove `Satisfies m x χ ↔ Satisfies m' x χ` by induction
        on `χ`, where the only non-mechanical case is `.box ψ` forward, at a point `x = f w` for a
        known `w` carrying `T(□ψ)@w ∈ b`. There the chain is: `accPinnedBy` gives
        `ReflTransGen acc w src`; `hsat` + iterated `hintikkaS4_box_pos_step` gives the **wrapped**
        `T(□ψ)@src ∈ b`; `hbox` gives `T(□ψ)@wBlock ∈ b`; the branch conjunct gives
        `Satisfies m (f wBlock) (.box ψ)`, which covers every `y` with `m.r (f wBlock) y` including
        points outside the label image. `.diamond ψ` negative is the exact dual through `hdia`.
  - [ ] Run `lean_verify` on every landed declaration; require only `propext`, `Classical.choice`,
        `Quot.sound`.
  - [ ] Record the verdict in a `#### Phase 1 Verdict` subsection in this file, with the exact
        `lean_goal` state at any stuck point.

- **Kill criteria and outcomes** (decide before dispatch, not under pressure):

| Outcome | Verdict |
|---|---|
| (i) The lemma closes sorry-free | Gate A **PASSES**. Commit. Note explicitly that this does not validate `hsat`/`hbox`/`hdia`, which Gates B/C and Phase 6 own. |
| (ii) The branch conjunct is **refuted** — a concrete model exhibits `branchSatisfiablePinnedIn s4FC b acc` with all hypotheses and `¬ branchSatisfiablePinnedIn s4FC b (acc.addEdge src wBlock)` | **Route (1) is dead.** Revert sub-step 1.2, keep sub-step 1.1, record the counterexample, escalate per the Terminal Condition. |
| (iii) The branch conjunct does **not close within this dispatch** | **Route (1) is dead as planned.** The attempt budget is one dispatch by design — an open-ended proof attempt is exactly the unbounded-phase failure mode this plan is built to avoid. Revert sub-step 1.2, keep sub-step 1.1, record the exact `lean_goal`, escalate. Do **not** request a second dispatch to keep trying, and do **not** commit a `sorry`. |
| (iv) The lemma closes only under a *strictly stronger* hypothesis than those listed | **Route (1) survives only if that hypothesis is nameable and its establishability is assessed in the same dispatch.** Write the hypothesis out, state which phase would owe it, and check it against Phase 3's measurement before declaring the gate passed. If it is not nameable, this is outcome (iii). |
| (v) The box half closes and the diamond half does not (or vice versa) | **Route (1) is dead as planned.** Do not proceed on the box half alone and do not fall back to a wrapped-only transfer — report 04 §6.4 measured 40 counterexamples for that shape. Escalate. |

- **Done when:** the gate lemma is either sorry-free and committed, or reverted with a
  `#### Phase 1 Verdict` recording the exact goal state; sub-step 1.1 is sorry-free and committed in
  either case; sorry census in `Cslib/Logics/Modal/Tableau/` is exactly 1; scoped
  `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` and `lake exe lint-style` clean.

---

### Phase 2: DECISION GATE B — `modalS4Saturated` at a settled ordered-stepper state [NOT STARTED]

- **Goal:** Determine whether `modalS4Saturated φ₀ b acc` — Gate A's saturation hypothesis — is
  available at an **intermediate** state, specifically at a settled ordered state where a blocked step
  can fire.
- **Estimated output:** ~200 lines.
- **Depends on:** none.
- **Owns:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, new section appended at end of file.
- **Timing:** 3 hours.

- **Why this is a genuine gate, verified by reading in this planning run.**
  `modalHintikkaClauseGen` (`Saturation.lean`) matches on the **formula alone** and returns `True` for
  `.box _` and `.diamond _` regardless of sign, whereas `modalS4Saturated`
  (`LoopChecking.lean:6581-6593`) matches on `(sign, formula)` and carves out only `(.neg, .box)` and
  `(.pos, .diamond)`. Therefore the landed `S4KeyedHintikkaInv.hintikkaInv` (`:8774`) supplies
  **nothing** for `T(□ψ)` or `F(◇ψ)` — precisely the two shapes Gate A consumes. The candidate
  mechanism is instead the ordered stepper's own settledness: at a settled state
  `modalNonMintCandidates φ₀ keys b e acc = []` (`:873-879`), so every non-mint-shaped `sf ∈ b` is
  either in `e` or has `(modalApplyOneS4Keyed φ₀ keys sf b acc).1.isApplicable = false`, i.e. its
  4-rule/T-rule conclusions are already on `b`. The **gap is `sf ∈ e`**: a formula expanded against an
  older, smaller `acc`, whose conclusion for a later-added edge may be missing. That is exactly report
  02 §5.1's transient-gap shape, and closing or refuting it is this phase's entire content.

- **Tasks:**
  - [ ] `hintikkaS4_box_pos_reflTransGen_wrapped` and `hintikkaS4_dia_neg_reflTransGen_wrapped`: the
        **wrapped**-conclusion variants of the landed `_reflTransGen` bridges (`:7008`, `:7024`),
        by `Relation.ReflTransGen.head_induction_on` carrying `T(□ψ)` rather than unwrapping at the
        base. Each is a ~12-line transcription of the landed proof with `_self` dropped from the
        `refl` case. Grounded in `ChagrovZakharyaschev1997` `chunk_0247.md`/`chunk_0248.md` (the
        `□⁺` invariant) and `Massacci2000` Prop. 8.1 (`chunk_0065.md`) / Lemma 10.5 (`chunk_0055.md`).
        **These are unconditionally useful and must land sorry-free regardless of the gate's verdict.**
  - [ ] State the gate lemma:
        ```lean
        lemma modalS4Saturated_of_ordered_settled (φ₀ : Proposition Atom)
            (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
            (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
            (hsettled : modalNonMintCandidates φ₀ keys b e acc = [])
            (hHI : S4KeyedHintikkaInv φ₀ b e acc keys) :
            modalS4Saturated φ₀ b acc
        ```
  - [ ] Attempt it. The `sf ∉ e` half goes through `modalNonMintCandidates`'s filter predicate plus
        `hintikka_congr_S4` (`:7844`, which shows the keyed and live rules agree on Hintikka-set-hood
        for any `keys`, and whose proof collapses via `modalApplyOneS4Keyed`'s `| _, _ =>` catch-all —
        i.e. off the two mint shapes the two rules are definitionally equal). The `sf ∈ e` half is the
        gap: `hintikkaInv` gives `True` there for box/diamond shapes.
  - [ ] If the `sf ∈ e` half does not close, **name the exact missing fact** as a candidate additional
        field on a boxed Hintikka invariant, e.g.
        `eBoxPosSaturated : ∀ sf ∈ e, ∀ ψ w, sf = ⟨.pos, .box ψ, w⟩ → ∀ w', acc.hasEdge w w' = true → ⟨.pos, .box ψ, w'⟩ ∈ b`
        and its diamond dual — and assess, **in the same dispatch**, whether it is preservable. The
        relevant fact: the boxed mint payload (`artifacts/s4boxed.lean`'s `mintBoxed`) already emits
        the wrapped `T(□ψ)@w'` and `F(◇ψ)@w'` at the moment a world is minted, which is exactly what a
        mint step would need to preserve such a field. Say so if it holds; say what breaks if not.
  - [ ] `lean_verify` on every landed declaration.
  - [ ] Record a `#### Phase 2 Verdict` subsection.

- **Kill criteria and outcomes:**

| Outcome | Verdict |
|---|---|
| (i) The gate lemma closes from `hsettled` + `hHI` + `hintikka_congr_S4` alone | Gate B **PASSES** at its cheapest. Commit. |
| (ii) It needs exactly **one nameable additional invariant field**, whose statement is written out and whose preservability under the boxed mint payload is argued in the same dispatch | **Route (1) survives at the cost of one added field**, carried by Phase 7. Record the statement verbatim. Do **not** proceed past recording it; Phase 7 owes the preservation proof, and Phase 3 must corroborate it decidably. |
| (iii) A concrete reachable settled state is exhibited at which `modalS4Saturated` **fails** | **Route (1) is dead.** Gate A's hypothesis is false where it is needed. Record the state, escalate per the Terminal Condition. |
| (iv) Neither closes nor is refuted within this dispatch, and no nameable field is identified | **Route (1) is dead as planned.** One-dispatch attempt budget. Revert, keep the two `_wrapped` bridges, record the goal state, escalate. |

- **Done when:** the two `_wrapped` bridges are sorry-free and committed; the gate lemma is either
  sorry-free and committed or reverted with a recorded verdict; sorry census exactly 1; scoped
  `lake build Cslib.Logics.Modal.Tableau.LoopChecking` and `lake exe lint-style` clean.

---

### Phase 3: DECISION GATE C — empirical falsification sweep at every blocking state [NOT STARTED]

- **Goal:** Measure, over the **ordered + boxed** driver and at **every state where the guard fires**
  (not only at terminal open leaves, which is all report 04 measured), whether the wrapped transfer
  and the box-positive/diamond-negative saturation content actually hold.
- **Estimated output:** ~250 lines in a new probe file.
- **Depends on:** none.
- **Owns:** `specs/553_.../artifacts/s4pin.lean` (new); may read and re-run `artifacts/s4boxed.lean`
  and `artifacts/s4subtractive3.lean`.
- **Timing:** 3 hours.

- **What is new here, and why the existing measurements do not cover it.** Report 04 §6.4 measured its
  conditions at **terminal open leaves** and argued (correctly) that transient intermediate states do
  not occur there. The soundness invariant must hold at **every intermediate state**, so this plan's
  obligations must be measured exactly where report 04's were not. Every landed counterexample in this
  task's record — report 02's refutation of `blockedRedirect_boxctx_mem` at step [6] of a 5-step
  trace, with `b` "repaired one step later" — lives at a transient state.

- **Tasks:**
  - [ ] Build `artifacts/s4pin.lean` by **extending** the existing harnesses, not replacing them:
        import/copy `s4boxed.lean`'s `boxedShapeAt`, `sbcBoxed`, `bwBoxed`, `mintBoxed`, `applyBoxed`,
        `stepBoxedOrdered`, and `s4subtractive3.lean`'s `condG`/`condF`/`condGStar`/`condFStar`
        pattern and its DFS-over-all-leaves driver. Reuse `s4subtractive.lean`'s `falsifiableUpTo`
        oracle (self-calibrating: returns least-countermodel-size **3** for `cex`) as the adjudicator
        for any verdict disagreement. **Do not write a new oracle.**
  - [ ] Instrument the ordered boxed stepper to fire a callback at **every** step at which
        `bwBoxed … = some wBlock`, and at each such state evaluate decidable mirrors of:
        - **(W1) wrapped box transfer**: `T(□χ)@src ∈ b → T(□χ)@wBlock ∈ b`, for `χ` with
          `(pos, □χ) ∈ signedSubfmls φ₀`.
        - **(W2) wrapped diamond transfer**: `F(◇χ)@src ∈ b → F(◇χ)@wBlock ∈ b`.
        - **(U1)/(U2)** the unwrapped halves (the landed lemmas' content, as a control — expect 0
          failures, since they are proved).
        - **(S1) box-positive settled saturation**: `T(□χ)@w ∈ b ∧ acc.hasEdge w w' → T(□χ)@w' ∈ b`,
          over all `w, w'` — i.e. Gate B's conclusion, in decidable form.
        - **(S2)** the diamond-negative dual.
        - **(E1) the `e`-gap specifically**: count states at which some `T(□χ)@w ∈ e` has a missing
          conclusion for a currently-recorded edge. **This is the number that decides Gate B
          empirically.** Print witnesses.
        - **(R1) the pinning-relevance rate**: the fraction of blocking decisions at which
          `¬ ReflTransGen acc.hasEdge src wBlock`, i.e. at which the redirect edge is genuinely new.
          Report 01 measured 96.7% on the shipped guard; this confirms the boxed-ordered figure and
          confirms the obligation is not vacuous.
        - **(L1) report 02 §5.1's specific counter-shape**: search for a state with mint edges
          `w0→w1`, `w1→w2` and a late-arriving `T(□ψ)@w0`, and report whether it coincides with a
          blocking decision.
  - [ ] Re-run the differential sweep (baseline vs boxed-ordered) on all three corpora — 2 atoms
        size ≤ 6 (8,532), 2 atoms size ≤ 7 (55,299), 1 atom size ≤ 8 (95,730) — reporting
        `closed/open/fuel` counts and, mandatorily, **`open→closed` (must be 0)** and `closed→open`.
        Adjudicate every disagreement with the oracle.
  - [ ] Controls that must hold or the harness is wrong: `cex` OPEN under boxed-ordered; T, 4, K
        axioms CLOSED; guard fires on a non-trivial number of formulas (report 04 measured 23,182
        across the three corpora on the shipped guard).
  - [ ] Record all `#eval` output verbatim in a `#### Phase 3 Measurements` subsection, with the
        reproduction command (`lake env lean specs/553_.../artifacts/s4pin.lean`).

- **Kill criteria:**

| Outcome | Verdict |
|---|---|
| (W1) or (W2) fails at any reachable blocking state | **Route (1) is dead** — boxed birth content does not deliver the wrapped transfer. Escalate. |
| (S1), (S2) or (E1) shows failures at a blocking state | **Gate B is empirically refuted; route (1) is dead.** Print and record the witness state. This is the expected way for the plan to die, and finding it here is a success of the plan's structure, not a failure of it. |
| `open→closed` is non-zero on any corpus | **Route (1) is dead** — the boxed-ordered driver is unsound in a new way. Escalate; do not attempt a repair inside this phase. |
| A control fails (`cex` closes, or T/4/K opens) | The harness is wrong. Fix the harness and re-run; do not report the numbers. |
| Everything measures clean | **This licenses NOTHING.** Record the numbers and proceed only because Phases 1, 2 and 4 pass on their own terms. Explicitly do **not** cite this phase as evidence for any obligation. |

- **Done when:** `artifacts/s4pin.lean` runs to completion under `lake env lean`, every measurement
  above is recorded verbatim in `#### Phase 3 Measurements`, and the kill table has been evaluated
  against the numbers in writing. No `Cslib/**` or `CslibTests/**` file is touched.

---

### Phase 4: DECISION GATE D — `accPinnedBy` preservation across the two minting shapes [NOT STARTED]

- **Goal:** Determine whether `accPinnedBy` is preserved when the driver mints a world. Minting is the
  only rule that adds a label, so it is the only rule that can break the conjunct.
- **Estimated output:** ~300 lines.
- **Depends on:** 1 (needs `accPinnedBy`'s final form, which Phase 1 may adjust under outcome (iv)),
  3 (the measured pinning-relevance rate).
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, extending Phase 1's section.
- **Timing:** 3.5 hours.

- **Why the naive assignment fails, and what to do instead** (derived at plan time so the dispatch
  does not have to rediscover it). At a `F(□ψ)@w` mint step the driver creates a fresh label `v`, adds
  the edge `w → v`, and adds `F(ψ)@v`. The old witness gives some `y` with `m.r (f w) y` and
  `y ⊭ ψ`. Setting `f' v := y` **breaks `accPinnedBy`**: if `y` happens to be `f w''` for some other
  known `w''`, then `m.r (f w') y` for various `w'` yields `ReflTransGen acc w' w''`, but the conjunct
  demands `ReflTransGen (acc.addEdge w v) w' v`, and no such path exists. The intended fix is
  **fresh-point duplication** — the standard tree-unravelling move: extend `W` by a fresh point `y'`
  carrying `y`'s valuation and `y`'s outgoing relation, set `f' v := y'`, and let `y'`'s incoming
  relation be exactly `{x : m.r x (f w)} ∪ {y'}` (forced by `IsTrans` and no larger). Then
  `accPinnedBy` at the new state reduces to `accPinnedBy` at the old state, and the branch conjunct is
  preserved by a bisimulation-style agreement argument between `y` and `y'` (same valuation, same
  successors).
- The diamond-positive mint shape (`T(◇ψ)@w`) is the exact dual.

- **Tasks:**
  - [ ] Formalise the duplication: a `Sum W Unit`-style carrier (or `Option W`), the extended relation,
        the valuation, and the `s4FC` instances. State and prove the agreement lemma
        `Satisfies m'' (Sum.inr ()) χ ↔ Satisfies m y χ` for `χ ∈ modalSubfmls φ₀`, by induction on
        `χ`.
  - [ ] `branchSatisfiablePinnedIn_s4FC_mint_boxNeg`: from
        `branchSatisfiablePinnedIn s4FC b acc` and `F(□ψ)@w ∈ b` with `w` known and `v` fresh
        (`accFreshInv`-style), conclude
        `branchSatisfiablePinnedIn s4FC (⟨.neg, ψ, v⟩ :: b) (acc.addEdge w v)`.
  - [ ] `branchSatisfiablePinnedIn_s4FC_mint_diaPos`: the dual.
  - [ ] Note in the docstrings that this construction runs at **every** mint step, and record the
        honest cost comparison: report 04 §10's objection to route (2′) was that it needs a new witness
        model at every intermediate state. This plan pays a *bounded* version of that — a fresh-point
        duplication at mint steps only, whose obligation reduces to the previous state's conjunct —
        rather than a full truth-lemma-scale construction *n* times. If the reduction does **not**
        hold, that distinction collapses and the route is in route (2′)'s position.
  - [ ] `lean_verify` on both lemmas.
  - [ ] Record a `#### Phase 4 Verdict` subsection.

- **Kill criteria:**

| Outcome | Verdict |
|---|---|
| (i) Both mint lemmas close sorry-free and the new `accPinnedBy` obligation reduces to the old one | Gate D **PASSES**. Commit. |
| (ii) Preservation is **refuted** — a state and a mint step at which no choice of `f' v` and no model extension preserves the conjunct | **Route (1) is dead.** `accPinnedBy` cannot be carried by the fuel induction. Escalate. |
| (iii) It closes only by rebuilding the witness model from scratch at each mint step, rather than reducing to the previous state's conjunct | **Route (1) is dead as planned** — this is precisely report 04 §10's verdict on route (2′), now applying to route (1). Record the collapse explicitly and escalate. Do not proceed on the grounds that "it still works, just expensively": the cost is what report 04 already priced as prohibitive. |
| (iv) Does not close within this dispatch | **Route (1) is dead as planned.** One-dispatch attempt budget. Revert, record the goal state, escalate. |

- **Done when:** both mint lemmas are sorry-free and committed, or reverted with a recorded verdict;
  sorry census exactly 1; scoped `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` and
  `lake exe lint-style` clean.

---

> **Gate boundary.** Phases 5-12 are **not scaffolded on a positive verdict**. They must not be
> dispatched unless Phases 1, 2, 3 and 4 have all returned positive verdicts recorded in this file. If
> any gate failed, the correct action is the Terminal Condition in the Overview: escalate, write the
> `state_updates_pending` dependency inversion, and hand off to
> `specs/557_modal_tableau_refactor_abstractions_boneyard`. Do not propose a fifth route.

---

### Phase 5: Boxed birth content, boxed mint payload, and the boxed ordered driver family [NOT STARTED]

- **Goal:** Land the `…Boxed` guard/rule/stepper/driver family as **parallel definitions** beside the
  landed ones, transcribing `artifacts/s4boxed.lean` verbatim in behaviour.
- **Estimated output:** ~350 lines.
- **Depends on:** 1, 2, 3, 4.
- **Owns:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, new boxed-driver section.
- **Timing:** 4 hours.

- **Tasks:**
  - [ ] `def boxedShapeAt`, `def successorBirthContentBoxed` (records `(pos, □χ)` / `(neg, ◇χ)`),
        `def blockingWorldS4KeyedBoxed` — the guard's *shape* is unchanged, only the content function
        is substituted, so the comparison stays plain key equality.
  - [ ] `def mintPayloadBoxed`: the witness (unwrapped, as now) plus the box context in **boxed** form,
        transcribing `artifacts/s4boxed.lean`'s `mintBoxed`.
  - [ ] `def modalApplyOneS4KeyedBoxed`: `modalApplyOneS4Keyed` (`:747-759`) with `blockingWorldS4KeyedBoxed`
        substituted and the `none` arms emitting `(.linear (mintPayloadBoxed …), acc.addEdge sf.label (modalNextWorld b))`
        instead of falling through to `modalApplyOne`. **`Rules.lean` is not edited.**
  - [ ] The four spec lemmas mirroring `modalApplyOneS4Keyed_{boxNeg,diaPos}_{blocked,unblocked}_eq`
        (`:763-804`), each provable by `unfold; simp [hblock]`.
  - [ ] `blockingWorldS4KeyedBoxed_eq_birthContent` and `_none_fresh`, transcriptions of `:516-531`
        and `:538-543`.
  - [ ] `def modalStepBranchS4KeyedBoxedBody`, `def modalNonMintCandidatesBoxed`,
        `def modalStepBranchS4KeyedBoxed`, `def modalStepBranchS4KeyedBoxedOrdered`,
        `def modalExpandBranchesS4KeyedBoxedOrdered`, `def modalTableauS4KeyedBoxedOrdered`, seeding
        `keys := [(0, ∅)]` (not `[]` — that violates `keysTotal`) and `fuel := modalFuelS4 φ`.
  - [ ] `hintikka_congr_S4Boxed`, the analogue of `hintikka_congr_S4` (`:7844`). Note the difference
        from the route-(3) case: `modalApplyOneS4KeyedBoxed` differs from `modalApplyOneS4` at the two
        mint shapes in *both* arms (blocked and minting), so the congruence must be checked, not
        assumed to be a 13-line transcription. If it does not hold, say so and state what
        `modalHintikkaSetS4Boxed` must be instead.
  - [ ] Append to `blockingWorldS4Keyed`'s docstring (`:466-505`) a pointer to the boxed successor.
        **Do not delete** the staleness / no-reachability-restriction description at `:478-492`.
  - [ ] `#eval` sanity checks in a scratch file (not committed to `Cslib/`): `cex` OPEN under the
        boxed-ordered Lean driver, T/4/K CLOSED. Cross-check against Phase 3's probe numbers.

- **Done when:** all definitions and spec lemmas land sorry-free; `hintikka_congr_S4Boxed` is either
  proved or its failure is recorded with the replacement statement; the landed guard and drivers are
  byte-identical; sorry census exactly 1; scoped build and `lint-style` clean.

---

### Phase 6: `S4LoopInvBoxed`, the boxed key bounds, and the WRAPPED transfers [NOT STARTED]

- **Goal:** Re-establish the invariant fields that boxed birth content disturbs, and land the two
  wrapped transfers that discharge Gate A's `hbox`/`hdia`.
- **Estimated output:** ~350 lines. **Split rule:** if the `keyLowerBd` re-proofs alone exceed ~250
  lines, split into 6.1 (key bounds) and 6.2 (`S4LoopInvBoxed` + wrapped transfers).
- **Depends on:** 5.
- **Owns:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, new boxed-invariant section.
- **Timing:** 4 hours.

- **Tasks:**
  - [ ] Re-prove, against `successorBirthContentBoxed`, the three obligations report 02 §4 enumerates:
        `successorBirthContentBoxed_boxNeg_subset_relevantSetFinset` (mirroring `:2137`),
        `_diamondPos_subset_relevantSetFinset` (mirroring `:2207`), and
        `successorBirthContentBoxed_subset_signedSubfmls` (mirroring `:2656`). The boxed pair
        `(pos, □χ)` is in `signedSubfmls φ₀` whenever `T(□χ)@w` is a branch formula, by `bClosure`.
  - [ ] Re-prove `modalApplyOne_boxNeg_outputs_subset_S4`'s boxed analogue (mirroring `:1905`) and its
        diamond twin, against `mintPayloadBoxed`.
  - [ ] `structure S4LoopInvBoxed`: the nine fields of `S4LoopInv` (`:7070-7099`) **without**
        `outDegEq`, restated over the boxed driver. `keysDistinct`, `keysInUniverse` and the pigeonhole
        chain transfer verbatim because the comparison is unchanged.
  - [ ] `modalStepBranchS4KeyedBoxedOrdered_preserves_S4LoopInvBoxed`, assembled from per-field
        lemmas mirroring the thirteen at `:2449`, `:2656`, `:3837`, `:4052`, `:4181`, `:4353`,
        `:5515`, `:5855`, `:6248`, `:7173`, `:7379` (skipping `:5111`'s `outDegEq` and `:4684`'s
        `keysOriginS4`, neither of which the boxed invariant carries).
  - [ ] **`blockedRedirect_wrapped_boxPos_mem`** and **`blockedRedirect_wrapped_diaNeg_mem`** — Gate A's
        `hbox`/`hdia`. Report 02 §4 gives the three-step chain:
        `T(□ψ)@src ∈ b` ⟹ `(pos, □ψ) ∈ successorBirthContentBoxed φ₀ b s φ src` (boxed filter;
        `□ψ ∈ modalSubfmls φ₀` by `bClosure`) ⟹ `(pos, □ψ) ∈ key(wBlock)`
        (`blockingWorldS4KeyedBoxed_eq_birthContent`) ⟹ `T(□ψ)@wBlock ∈ b` (`keyLowerBd`, unchanged).
        These are near-transcriptions of the landed `blockedRedirect_unwrapped_*_mem` (`:8926`,
        `:8958`) with the boxed filter substituted. Docstring them as the **wrapped half of `□⁺`**,
        citing `ChagrovZakharyaschev1997`'s Lemmon filtration (`chunk_0248.md` L24-31), and state that
        the landed unwrapped lemmas are the other half.
  - [ ] `lean_verify` on every new top-level declaration.
  - [ ] Re-run Phase 3's (W1)/(W2) measurement against the landed Lean lemmas' hypotheses to confirm
        the probe and the proof agree on the same statement.

- **Done when:** `S4LoopInvBoxed` and its preservation theorem land sorry-free; both wrapped transfers
  land sorry-free and standard-axioms-only; the landed `S4LoopInv` and
  `modalStepBranchS4_preserves_outDegEq` are byte-identical; sorry census exactly 1; scoped build and
  `lint-style` clean.

---

### Phase 7: `S4KeyedHintikkaInvBoxed` and Gate B's saturation lemma for the boxed ordered driver [NOT STARTED]

- **Goal:** Carry the Hintikka-side invariant to the boxed ordered driver, including any additional
  field Gate B's outcome (ii) named, and re-instantiate the settled-saturation lemma for it.
- **Estimated output:** ~300 lines.
- **Depends on:** 6.
- **Owns:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, boxed Hintikka-invariant section.
- **Timing:** 3.5 hours.

- **Tasks:**
  - [ ] `structure S4KeyedHintikkaInvBoxed`: the five fields of `S4KeyedHintikkaInv`
        (`:8770-8789`) restated over the boxed driver, **plus** any field Gate B's verdict named under
        outcome (ii) (e.g. `eBoxPosSaturated` / `eDiaNegSaturated`).
  - [ ] `S4KeyedHintikkaInvBoxed_weaken` and the private append lemma, mirroring `:8800` and `:9132`.
  - [ ] `modalStepBranchS4KeyedBoxed_preserves_S4KeyedHintikkaInvBoxed`, mirroring `:9194`. The mint
        arms are where the new fields are discharged, and they are discharged **by** the boxed mint
        payload: `mintPayloadBoxed` emits the wrapped `T(□ψ)@v` and `F(◇ψ)@v` at the moment `v` is
        created, so the new edge's obligation is met at the instant the edge appears.
  - [ ] `modalS4SaturatedBoxed_of_ordered_settled`: Gate B's lemma re-instantiated for the boxed
        ordered driver, now with the additional fields available.
  - [ ] **Falsification test for mechanism 2, run as an explicit step.** `grep -n` every declaration in
        the chain `modalS4SaturatedBoxed_of_ordered_settled` → the wrapped transfers →
        `blockingWorldS4KeyedBoxed` for any mention of `red`, `accWithReds`, or `Reds`. Expect **zero
        hits**: mechanism 2 must live entirely in `keys`, never in a side channel. Record the grep
        output in the phase handoff. A non-zero result means route (3)'s machinery has crept back in —
        escalate, do not patch.
  - [ ] `lean_verify` on every new top-level declaration.

- **Done when:** the boxed Hintikka invariant, its preservation theorem, and
  `modalS4SaturatedBoxed_of_ordered_settled` land sorry-free; the falsification grep returns zero
  hits and is recorded; sorry census exactly 1; scoped build and `lint-style` clean.

---

### Phase 8: `branchSatisfiablePinnedIn` endpoints — forgetting bridge, closed leaf, initial establishment [NOT STARTED]

- **Goal:** Land the two ends of the soundness chain for the pinned invariant, so the capstone can be
  stated at full `branchSatisfiableIn s4FC` strength.
- **Estimated output:** ~200 lines.
- **Depends on:** 6. Runs in parallel with Phase 7 (different file).
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, pinned-invariant endpoints section.
- **Timing:** 2.5 hours.

- **Tasks:**
  - [ ] `branchSatisfiablePinnedIn_imp_branchSatisfiableIn`: forget the pinning conjunct. One line
        (`fun ⟨W, m, f, h1, h2, _, h4⟩ => ⟨W, m, f, h1, h2, h4⟩`). **This is what makes the capstone a
        full-strength theorem**: the pinned invariant is a *strengthening*, so the final statement is
        about `branchSatisfiableIn s4FC` exactly as required, with no weakening anywhere.
  - [ ] `modalClosed_unsat_pinnedIn`: `isModalClosed b = true → ¬ branchSatisfiablePinnedIn FC b acc`,
        immediate from `modalClosed_unsatIn` (`:139`) composed with the forgetting bridge. Record the
        direction of the logic explicitly, because it is where intuition goes wrong: a **stronger**
        invariant makes the closed-leaf obligation *easier* and the initial obligation *harder* — the
        exact opposite of `branchPropAdequateIn`'s trade (report 03 §4.2).
  - [ ] `branchSatisfiablePinnedIn_initial`:
        `¬ s4Valid φ → branchSatisfiablePinnedIn s4FC [⟨.neg, φ, 0⟩] Accessibility.empty`. The pinning
        conjunct is nearly free here: `modalKnownWorlds [⟨.neg, φ, 0⟩] = [0]`, so the only obligation
        is `m.r (f 0) (f 0) → ReflTransGen (fun _ _ => False) 0 0`, discharged by
        `Relation.ReflTransGen.refl`. The rest transcribes the S5 initial construction
        (`FrameSoundness.lean:3328-3334` region) and `frameValid`'s unfolding (`:83-84`).
  - [ ] `lean_verify` on all three.

- **Done when:** all three land sorry-free; sorry census exactly 1; scoped build and `lint-style`
  clean.

---

### Phase 9: Per-step preservation of the pinned invariant for the non-mint, non-blocked shapes [NOT STARTED]

- **Goal:** Discharge preservation for every rule that leaves `acc` unchanged — propositional, T-rule,
  4-rule — where the pinning conjunct is untouched and the branch conjunct follows from the landed
  full-strength `s4FC` rule lemmas.
- **Estimated output:** ~250 lines.
- **Depends on:** 8.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, per-step section.
- **Timing:** 3 hours.

- **Tasks:**
  - [ ] `accPinnedBy_of_acc_unchanged`: adding formulas at **existing** labels leaves
        `modalKnownWorlds b` unchanged, so `accPinnedBy` transfers verbatim when `acc` is unchanged.
        Prove the `modalKnownWorlds` monotonicity fact it needs (or reuse
        `modalKnownWorlds_mono_append_FS`, `:2082`).
  - [ ] Pinned analogues of the landed full-strength rule lemmas, each obtained by threading the
        pinning conjunct through unchanged: `branchSatisfiablePinnedIn_reflFC_boxPos_mem`-style for the
        T-rule (`:973`, `:991`), and the 4-rule pair mirroring
        `branchSatisfiableIn_s4FC_boxPos_trans_mem` (`:1085`) and `_diaNeg_trans_mem` (`:1106`). Note
        in the docstrings that these need **no** reflexivity (`hrefl` is destructured and never used at
        `:1092`, `:1122`) — a fact worth recording because it is what makes the mechanism portable to
        the non-reflexive transitive corners, which are out of scope here.
  - [ ] Pinned analogues of `modalFourBoxProp_sound` (`:1129`) and `modalFourDiaNegProp_sound`
        (`:1149`), and of `modalTBoxSelf_sound` (`:1010`) / `modalTDiaNegSelf_sound` (`:1028`).
  - [ ] `lean_verify` on every new declaration.

- **Done when:** every non-mint, non-blocked shape has a pinned preservation lemma, all sorry-free;
  sorry census exactly 1; scoped build and `lint-style` clean.

---

### Phase 10: `S4KeyedBoxedSoundSpec`, per-step assembly, fuel induction, and the soundness capstone [NOT STARTED]

- **Goal:** Assemble the full per-step preservation lemma, run the fuel induction, and land
  `modalTableauS4KeyedBoxedOrdered_sound` at full `branchSatisfiableIn s4FC` strength.
- **Estimated output:** ~450 lines. **Split rule (declared): dispatch as 10.1 (spec + per-step
  assembly, ~250 lines) then 10.2 (fuel induction + capstone, ~200 lines).** Each sub-phase is one
  bounded unit with its own scoped build.
- **Depends on:** 1, 4, 7, 9.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, spec + capstone section.
- **Timing:** 5 hours.

- **Why this cannot instantiate the generic ladder** (verified by reading in this planning run).
  `modalStepBranchGen_preserves_satIn` (`:195-226`) requires `(apply …).snd = acc` in both `hBoxPos`
  and `hDiaNeg`, and `hAgree` requires agreement with `modalApplyOne` off the two propagating shapes.
  The boxed keyed rule violates `hAgree` at exactly the two **minting** shapes, where it emits either
  `(.linear [], acc.addEdge sf.label wBlock)` or
  `(.linear (mintPayloadBoxed …), acc.addEdge sf.label (modalNextWorld b))`. So this phase writes a
  **bespoke** step lemma on the `modalStepBranchS5Gen_preserves_satIn` (`:2554`, 536 lines) pattern,
  which handles its non-generic arm up front before falling through to the generic shape analysis.

- **Tasks (10.1):**
  - [ ] `def S4KeyedBoxedSoundSpec (apply : RuleApply Atom) : Prop` — the analogue of `S5SoundSpec`
        (`:2256-2261`), with three disjuncts per call site: agrees with `modalApplyOneS4 φ₀`; **or**
        fires a blocked redirect `(.linear [], acc.addEdge sf.label wBlock)` with `wBlock` a known
        world carrying the witness formula (available from `modalStepBranchS4Keyed_blocked_witness_mem`,
        `:8994`, transcribed for the boxed guard); **or** mints
        `(.linear (mintPayloadBoxed …), acc.addEdge sf.label (modalNextWorld b))` with the target fresh.
  - [ ] `modalApplyOneS4KeyedBoxed_s4KeyedBoxedSoundSpec`.
  - [ ] `def S4BoxedSoundInv b acc keys e : Prop` — the analogue of `S5SoundInv` (`:2536`): the
        conjunction of `accFreshInv`, `accTargetsKnown`, `S4LoopInvBoxed`,
        `S4KeyedHintikkaInvBoxed`, and the settledness fact the blocked arm consumes. Bundled into one
        `Prop` so a single `List.Forall₂` threads it through the outer induction.
  - [ ] `modalStepBranchS4KeyedBoxedOrdered_preserves_pinnedSatIn`: the bespoke per-step lemma. The
        blocked arm invokes Phase 1's `branchSatisfiablePinnedIn_s4FC_redirect`, feeding `hsat` from
        Phase 7's `modalS4SaturatedBoxed_of_ordered_settled` and `hbox`/`hdia` from Phase 6's wrapped
        transfers. The mint arms invoke Phase 4's two mint lemmas. Every other shape invokes Phase 9.
- **Tasks (10.2):**
  - [ ] `modalExpandBranchesS4KeyedBoxedOrdered_closed_unsatPinnedIn`: the fuel induction, on the
        `modalExpandBranchesS5Gen_closed_unsatIn` (`:3123`) pattern, stated contrapositively and
        threaded with `List.Forall₂`.
  - [ ] `theorem modalTableauS4KeyedBoxedOrdered_sound (φ : Proposition Atom) (h : modalTableauS4KeyedBoxedOrdered φ = .closed) : s4Valid φ`
        — via Phase 8's initial establishment and the forgetting bridge, so the **statement mentions
        only `s4Valid` and the driver**, and the invariant used never surfaces in a type. On the
        `modalTableauS5Gen_sound` (`:3317`) pattern.
  - [ ] **Full-strength check, run as an explicit step**: confirm by `grep -n` that the capstone's
        statement and the statement of every lemma it directly consumes mention
        `branchSatisfiablePinnedIn` only as a *stronger* hypothesis reached through
        `branchSatisfiablePinnedIn_imp_branchSatisfiableIn`, and mention `branchPropAdequateIn`
        **nowhere**. Record the grep output. A hit on `branchPropAdequateIn` means the plan silently
        retargeted to the weak invariant — escalate, do not patch.
  - [ ] `lean_verify` on the capstone and on every new top-level declaration.

- **Done when:** the capstone is sorry-free and standard-axioms-only; the full-strength grep is clean
  and recorded; sorry census exactly 1; scoped build and `lint-style` clean; committed at both 10.1
  and 10.2 boundaries.

---

### Phase 11: Completeness for the boxed ordered driver, and `instDecidableS4Valid` [NOT STARTED]

- **Goal:** Establish completeness for the **same** driver the capstone is about, and land the
  decidability instance the downstream consumers need.
- **Estimated output:** ~400 lines. **Split rule (declared): dispatch as 11.1 (boxed ordered
  completeness, ~300 lines) then 11.2 (`s4Valid_decides` + `instDecidableS4Valid`, ~100 lines).**
- **Depends on:** 10.
- **Owns:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, boxed assembly section.
- **Timing:** 5 hours.

- **Why this is real work.** Re-verified in this planning run: the landed
  `modalTableauS4Keyed_complete` (`:4267`) is for the **plain** keyed driver, and
  `modalTableauS4KeyedOrdered` has **neither** a soundness nor a completeness theorem. The
  decidability instance needs `modalTableauX φ = .closed ↔ s4Valid φ` for a **single** `X`, and the
  capstone fixes `X := modalTableauS4KeyedBoxedOrdered`. So completeness must be established for that
  driver; it is not a corollary of anything landed.

- **Tasks (11.1):**
  - [ ] `modalTableauS4KeyedBoxedOrdered_initial` (mirroring `:4190`).
  - [ ] `modalExpandBranchesS4KeyedBoxedOrdered_hintikka` (mirroring `LoopChecking.lean:10048`) and
        `_openBranch_initial_mem` (mirroring `:10409`).
  - [ ] `theorem modalTableauS4KeyedBoxedOrdered_complete (φ₀ : Proposition Atom) (h : s4Valid φ₀) : modalTableauS4KeyedBoxedOrdered φ₀ = .closed`
        — contrapositively, via `hintikka_congr_S4Boxed`, `modalTruthLemmaS4` and
        `modalOpenBranchS4_countermodel` (`:403-410`), **reusing `extractModelS4` verbatim**. Redirect
        edges only enlarge `ReflTransGen`, so the completeness side is unaffected by the guard's
        decisions.
- **Tasks (11.2):**
  - [ ] `theorem modalTableauS4KeyedBoxedOrdered_iff : modalTableauS4KeyedBoxedOrdered φ = .closed ↔ s4Valid φ`.
  - [ ] `def s4Valid_decides` and `instance instDecidableS4Valid : DecidablePred (s4Valid (Atom := Atom))`,
        on the pattern of the six landed instances (each of which consumes only the `↔`).
  - [ ] Confirm by scoped build that all six landed `Decidable` instances (K/T/B/S5/Five/KB5) are
        unaffected.
  - [ ] `lean_verify` on both capstones and the instance.

- **Done when:** both capstones and the instance are sorry-free and standard-axioms-only;
  `modalTableauS4Keyed_complete` is byte-identical and green; sorry census exactly 1; scoped build and
  `lint-style` clean; committed at both 11.1 and 11.2 boundaries.

---

### Phase 12: Regression corpus extension and CI [NOT STARTED]

- **Goal:** Make every verdict this plan relies on reproducible from the repository, and attempt the
  full CI pipeline.
- **Estimated output:** ~150 lines.
- **Depends on:** 10. Runs in parallel with Phase 11 (different files).
- **Owns:** `CslibTests/S4LoopGuardRegression.lean`, `specs/553_.../artifacts/`.
- **Timing:** 2.5 hours.

- **Tasks:**
  - [ ] Add `#guard_msgs in #eval` rows for the boxed ordered driver, **without altering any of the
        seven landed rows**: `cex` OPEN; T and 4 axioms CLOSED; B axiom OPEN; and the boxed
        **unordered** driver still CLOSED on `cex` (the documented unsoundness of the unordered line is
        unchanged by boxed keys — measured, and it must stay recorded).
  - [ ] Add a row exercising the **entry point** `modalTableauS4KeyedBoxedOrdered`, not only
        `modalExpandBranches*` with explicit fuel. Note in the section comment that no landed row does
        this, so it is new coverage.
  - [ ] Re-run `artifacts/s4pin.lean` against the **landed Lean** boxed ordered driver rather than the
        probe transcription, and record any divergence between probe and library as a defect to fix
        before the phase closes.
  - [ ] Re-run the differential sweep on all three corpora and record the numbers in a
        `#### Phase 12 Measurements` subsection.
  - [ ] Attempt the full pipeline: `lake build`, `lake test`, `lake lint`, `lake exe checkInitImports`,
        `lake exe lint-style`, `lake exe mk_all --module` (must report no update necessary —
        `Cslib.lean` is concurrent-session territory), and scoped
        `lake shake --add-public --keep-implied --keep-prefix` on each touched file. **Record**, rather
        than work around, any residual failure attributable to concurrent work on
        `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`, and verify by `git diff`
        that this plan touched none of it.
  - [ ] Final sorry and axiom census, with the exact commands and their output.

- **Done when:** the regression file's new rows pass under `lake build CslibTests.S4LoopGuardRegression`;
  the probe/library divergence check is clean; the full-pipeline attempt is recorded with any residual
  concurrent breakage attributed; sorry census exactly 1; axiom census byte-equal to the phase's own
  baseline.

---

## Testing & Validation

- **Per-phase, mandatory**: scoped
  `lake build Cslib.Logics.Modal.Tableau.{LoopChecking,FrameSoundness,FrameCompleteness}` for whichever
  files the phase touched; `lake exe lint-style` on each touched file; scoped
  `lake shake --add-public --keep-implied --keep-prefix`; `lean_verify` on every new top-level
  declaration, requiring only `propext`, `Classical.choice`, `Quot.sound`.
- **Per-phase, mandatory**: `grep -rn '\bsorry\b' Cslib/Logics/Modal/Tableau/*.lean` returns exactly
  one non-docstring hit, at `FrameSoundness.lean:1244`. Axiom baseline captured with
  `grep -rn '^axiom' Cslib/ | wc -l` at phase start and required byte-equal at phase end. **No
  hard-coded axiom count.**
- **Gate phases (1, 2, 4)**: the kill table is evaluated in writing, the verdict is recorded in a
  `#### Phase N Verdict` subsection with the exact `lean_goal` state at any stuck point, and **no
  `sorry` is committed**.
- **Gate phase 3**: every `#eval` output recorded verbatim with its reproduction command; every
  verdict disagreement adjudicated by the `falsifiableUpTo` oracle; the kill table evaluated in
  writing. Clean numbers license nothing.
- **Phase 7**: the mechanism-2 falsification grep (`red`/`accWithReds`/`Reds` in the soundness chain)
  returns zero hits, recorded.
- **Phase 10**: the full-strength grep (`branchPropAdequateIn` absent from the soundness chain)
  returns zero hits, recorded.
- **Behaviour preservation, at every commit**: `modalTableauS4Keyed_complete` and all six landed
  `Decidable` instances green; the seven landed rows of `CslibTests/S4LoopGuardRegression.lean`
  unchanged and passing; `blockingWorldS4Keyed` and its three contract lemmas byte-identical.
- **Full pipeline**: attempted once, in Phase 12, with residual concurrent breakage recorded and
  attributed rather than worked around.

## Artifacts & Outputs

| Path | Phase | Content |
|---|---|---|
| `specs/553_.../plans/05_pinned-witness-truth-lemma.md` | this file | the plan, plus `#### Phase N Verdict` / `#### Phase N Measurements` subsections appended in place |
| `specs/553_.../artifacts/s4pin.lean` | 3 | the every-blocking-state falsification harness, extending `s4boxed.lean` and `s4subtractive3.lean` |
| `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` | 1, 4, 8, 9, 10 | `accPinnedBy`, `branchSatisfiablePinnedIn`, the redirect and mint preservation lemmas, the endpoints, the per-shape lemmas, `S4KeyedBoxedSoundSpec`, `S4BoxedSoundInv`, the per-step lemma, the fuel induction, `modalTableauS4KeyedBoxedOrdered_sound` |
| `Cslib/Logics/Modal/Tableau/LoopChecking.lean` | 2, 5, 6, 7 | the two `_wrapped` bridges, `modalS4Saturated_of_ordered_settled`, the boxed guard/rule/stepper/driver family, `S4LoopInvBoxed`, the two wrapped transfers, `S4KeyedHintikkaInvBoxed` and its preservation |
| `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` | 11 | boxed ordered completeness, the `↔`, `s4Valid_decides`, `instDecidableS4Valid` |
| `CslibTests/S4LoopGuardRegression.lean` | 12 | new `#guard_msgs` rows for the boxed ordered driver and for the entry point |
| `specs/553_.../summaries/07_*.md` … | per phase | one summary per dispatched phase |
| `specs/553_.../.orchestrator-handoff.json` | per phase | handoff, including `sorry_inventory` and any `state_updates_pending` |

## Rollback/Contingency

- **Gate phases (1, 2, 4)**: revert the attempt in the same dispatch, keep the sub-step that landed
  sorry-free (Phase 1's three mechanical conjuncts; Phase 2's two `_wrapped` bridges), record the
  verdict, commit only the landed part. **Never commit a `sorry` at a gate.**
- **Any gate failing**: execute the Terminal Condition. Escalate to the user; write
  `state_updates_pending` proposing that 553 go `[BLOCKED]` naming
  `specs/557_modal_tableau_refactor_abstractions_boneyard` as the blocker and that 557's
  `dependencies: [553]` be inverted so 557 can run first; do **not** edit `specs/state.json`; do
  **not** propose a fifth route.
- **Construction phases (5-12)**: the boxed family lands as **parallel definitions**, so rollback is
  deletion of the new section plus one scoped `lake shake`. No landed declaration is edited in place,
  so no landed theorem can regress. If a phase must be abandoned mid-way, its partial section is
  removed rather than left with a `sorry`, and the phase heading is marked `[PARTIAL]` with the exact
  stopping point recorded.
- **If a scoped build breaks on a file this plan did not touch**: verify by `git diff` that the file is
  untouched, attribute it to concurrent work, record it, and continue with scoped builds. Do not
  attempt a repair in another session's territory.
- **Full-project `lake build`** is not a gate at any phase boundary before Phase 12, and its known
  failure on `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` is not this plan's to
  fix.
