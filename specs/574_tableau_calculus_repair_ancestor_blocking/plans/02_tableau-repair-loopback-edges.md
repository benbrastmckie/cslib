# Implementation Plan (v02): Repair Intuitionistic Tableau — Self-Copy Bound, Ancestor Blocking, Loop-Back-Edge Saturation Invariant

- **Task**: 574 - tableau_calculus_repair_ancestor_blocking
- **Status**: [IMPLEMENTING]
- **Effort**: 52-78 hours across 8 phases (~33-50h landed in Phases 1-5; ~19-28h remaining in
  Phases 6-8)
- **Dependencies**: 573 (quotient-soundness spike, GO verdict — decision record read and
  integrated; see the Supersession Accounting section for how that verdict fared in practice)
- **Research Inputs**:
  - `specs/574_tableau_calculus_repair_ancestor_blocking/reports/01_phase6-blocker-resolution.md`
    (**authoritative for this revision** — the 11-step pre-verified fix path, exact Lean shapes,
    dependent-breakage table, adversarial claim table C1-C15, and a live-verified prototype)
  - `specs/574_tableau_calculus_repair_ancestor_blocking/handoffs/01_variant-selection.md`
    (Phase 1 measurement record; D3/D4 resolved by `#eval`)
  - `specs/archive/573_tableau_quotient_soundness_spike/handoffs/01_quotient-soundness-spike-decision.md`
    (GO verdict; H1/H2 evidence — H1/H2 held, the quotient recommendation did not)
  - `specs/317_propositional_tableau_completeness/reports/14_blocker-analysis.md`
    (root-cause / spawn analysis)
  - Live source reading of `Rules.lean`, `Expansion.lean`, `Scheme.lean`, `Soundness.lean`,
    `Minimal/Soundness.lean`, `CslibTests/TableauConformance.lean`
- **Artifacts**: `plans/02_tableau-repair-loopback-edges.md` (this file; supersedes
  `plans/01_tableau-repair-ancestor-blocking.md`, which is retained unedited as the record of the
  quotient approach)
- **Standards**:
  - `.claude/context/formats/plan-format.md`
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/state-management.md`
  - `.claude/rules/plan-compliance.md`
  - `.claude/rules/no-task-references-in-deliverables.md`
  - `.claude/rules/cslib.md`, `.claude/rules/lean4.md`
- **Type**: cslib

## Overview

`intExpandBranches` (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`) diverged
on a Lean-verified complexity-9 witness. Phases 1-4 repaired the calculus: the
`applyAllTImpRules` `T(φ→ψ)` self-copy channel is removed, `intFImpReuseWitnessAnc?` performs an
**ancestor**-directed `Sfor`-containment blocking check, `intExpandBranches`'s single call site is
repointed to it, and the acceptance gate `intExpandBranches_closed_unsat` is re-verified sorry-free
and axiom-clean under the new calculus. **That work is live and green.**

What remains is the *proof-side* consequence: under ancestor direction the reuse witness `x` sits
**below** the blocked world `l` (`x ≤ l`, `isAccessible edges x l`), the reverse of what
`sfSatisfied`/`sfAccessSat`'s `.neg,.imp` clauses demand. Phase 4 parked that at exactly one
tracked temporary `sorry` (`Scheme.lean:3143`). Phase 5 built a blocking-**quotient** frame
(`intBlockRep` + a `Q`-predicate stack) intended to close it; a Phase 6 dispatch then discovered
that stack cannot carry the induction, and the blocker research
(`reports/01_phase6-blocker-resolution.md`) confirmed the obstruction is structural rather than a
shape bug — `intBlockRep` is a function of the *final* branch while the induction runs *forward*,
and `intBlockRep` is not monotone under branch growth.

**This revision replaces the quotient mechanism with remedy (b): existentially-quantified edges
plus an invariant-side augmented edge list.** `intExpandBranches_openBranch_sat`'s conclusion is
`∃ edges : IEdges, IBranchSaturation Atom b ∧ IFimpAccess edges b` — the lemma is free to return an
edge list that is **not** the one the algorithm accumulated. A second list `augSets` is threaded
alongside the algorithm's own `edgeSets`, and each blocking event is recorded at the moment it
happens as an explicit loop-back edge `(x, l)`. This is precisely Garg-Genovese-Negri's published
countermodel construction `M ∪ C` with `C = {x ≤ y | Sfor(x) ⊆ Sfor(y)}` — the very source the
repo's `Sfor` naming derives from, whose authors additionally report the filtration/quotient route
as the one they could **not** make work. The redundant numeric `w ≤ w'` conjunct in
`IBranchSaturation.sat_fimp` and `sfSatisfied`'s `.neg,.imp` clause — a never-consumed numeric
proxy for accessibility, false under ancestor blocking — is dropped.

**Definition of done** (unchanged from v01): `intExpandBranches_closed_unsat`
(`Intuitionistic/Soundness.lean`, consumed by `Minimal/Soundness.lean`) is verified sorry-free and
axiom-clean under the new calculus; `lake build`, `lake exe checkInitImports`, `lake lint`,
`lake exe lint-style`, `lake shake`, and `lake test` are green; `CslibTests/TableauConformance.lean`
is updated from real `#eval` output; the repo-wide bare-`sorry` count is back to its exact 6-entry
baseline.

### Research Integration

| Report | Integrated | What it changed in this plan |
|--------|-----------|------------------------------|
| `reports/01_phase6-blocker-resolution.md` | v02 (2026-07-28) | Replaced the "blocking-quotient frame" Goal with the loop-back-edge invariant; rewrote Phases 6-7 around the report's 11-step fix path; added the `sat_fimp` numeric-conjunct drop; recorded Phase 5 as superseded with a scheduled deletion; corrected the H3 availability table; added residual risk R1 (GGN Lemma III.5) to Non-Goals; recorded two defects |

`reports_integrated`: `["01_phase6-blocker-resolution.md"]`

**Fix-path provenance**: every declaration shape in Phase 6 below is transcribed from the report's
**verified prototype** (`scratch/Scheme.lean.prototype`, `scratch/phase6-prototype.patch` — 94
changed lines against the current `Scheme.lean`). That prototype was built against the live tree,
`lake build` completed 3,309 jobs green, the Phase-4 temporary `sorry` was closed, the repo-wide
bare-`sorry` count returned to exactly 6, and `Cslib/` was reverted byte-identical at dispatch end.
The prototype was also deliberately broken (swapping `houtPhi`↔`hFpsi` produces an application type
mismatch) to prove the discharge is genuinely elaborated, not vacuously satisfied. **This is the
strongest evidence base any phase of this task has had before dispatch; treat deviation from these
shapes as requiring justification, not the reverse.**

### Preserved Assets

The following work is complete and must not regress. `Soundness.lean` in particular is
**entirely sorry-free** and is the acceptance gate's home.

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| `intExpandBranches_closed_unsat` (fully proved) | `Intuitionistic/Soundness.lean` | [COMPLETED] | Phase 4 gate + blocker-research C6: `{propext, Classical.choice, Quot.sound}` |
| `minimalTableau_sound` (sorry-free) | `Minimal/Soundness.lean` | [COMPLETED] | Phase 4 gate |
| `intuitionisticTableau_sound` | `Intuitionistic/Soundness.lean` | [COMPLETED] | Phase 4 gate |
| `intRule_preserves_sat` incl. `.pos,.imp` arm | `Intuitionistic/Soundness.lean` | [COMPLETED] | 2026-07-28 |
| `intAccessPreorder` + `intAccessPreorder_le_of_isAccessible` | `Intuitionistic/Scheme.lean:~330,431` | [COMPLETED] | 2026-07-28 |
| `truthLemma` atom/bot/and/or cases + **F-imp case** | `Intuitionistic/Scheme.lean:756` | [COMPLETED] | blocker-research: stays green over `IFimpAccess`, **unchanged** by this fix |
| `IExpandedConsistent_sat` / `IExpandedAccessConsistent_sat` | `Intuitionistic/Scheme.lean:1249,1873` | [COMPLETED] | blocker-research C2: applied **unmodified** at `⟨augH, …⟩` |
| `sat_timp` as a live `IBranchSaturation` field | `Intuitionistic/Scheme.lean` | [COMPLETED] | 2026-07-28 |
| `intFImpReuseWitnessAnc?` + `_spec` (ancestor-directed, 5-tuple, Option-A conjunct retained) | `Intuitionistic/Expansion.lean` | [COMPLETED] | Phase 3-4 |
| `applyAllTImpRules` self-copy removed; `applyAllTImpRules_sat`, `freshAbove_applyAllTImpRules` repaired | `Expansion.lean`, `Soundness.lean` | [COMPLETED] | Phase 2 |
| 43-row conformance corpus, 24 temporal rows (different calculus) | `CslibTests/TableauConformance.lean` | [COMPLETED] | 2026-07-28 |
| BibTeX keys `Fitting1983`, `GargGenoveseNegri2012`, `Dyckhoff1992`, `ChagrovZakharyaschev1997`, `NegriVonPlato2001` | `references.bib:211,228,218,75,931` | [COMPLETED] | re-confirmed by blocker research |

**Sorry ledger.** Current tree carries **7**: the 6-entry baseline plus the one Phase-4 tracked
temporary. The temporary retires in Phase 6.3.

| File | Line (current) | Status |
|------|------|-----------|
| `Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` | 269 | baseline — unrelated |
| `Logics/Modal/Tableau/FrameSoundness.lean` | 1276 | baseline — unrelated |
| `Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (truthLemma T-imp) | 793 | baseline — **out of scope**, must remain unchanged |
| `Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (openBranch_sat fuel-0) | 2970 | baseline — **out of scope**, must remain unchanged |
| `Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` | 133 | baseline — **out of scope**, must remain |
| `Logics/Propositional/Tableau/Minimal/Completeness.lean` | 125 | baseline — **out of scope**, must remain |
| `Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (reuse-site discharge) | 3143 | **TEMPORARY — Phase 6.3 closes it** |

Line numbers drift as phases land; the invariant is the **count (6 at completion) and the identity
of the declarations they sit in**, not the numbers.

### Supersession Accounting (preserved-assets LOSS — stated, not buried)

Phase 5's blocking-quotient stack — **~480 lines across four green commits `b70eadc0`, `1a1eba9f`,
`a9eb2e47`, `07ab747c`** — is **superseded**, not salvaged. The mechanism it implements is the one
GGN report as unworkable and CZ warn against for intuitionistic models, and a Phase 6 dispatch
demonstrated concretely that it cannot carry the induction.

**Decision: DELETE (not retain as documented dead machinery).** Scheduled as Phase 7.1.

*Grep evidence backing the decision* (run at revision time, `Cslib/` + `CslibTests/`, `--include=*.lean`):

| Declaration | Total refs | Refs outside `Intuitionistic/Scheme.lean` |
|---|---|---|
| `negImpAt` | 4 | **0** |
| `intBlockRepStep` | 13 | **0** |
| `intBlockRep` (+ `_idempotent`, `_le`, 2 eq-lemmas) | 21 | **0** |
| `intAccessPreorderQ` (+ `_le_of_isAccessible`, `_le_of_rep_eq`) | 7 / 1 / 3 | **0** |
| `sfSatisfiedQ` (+ `_mono`) | 15 | **0** |
| `sfAccessSatQ` | 5 | **0** |
| `IExpandedConsistentQ` (+ `_mono`) | 7 | **0** |
| `IExpandedAccessConsistentQ` | 3 | **0** |
| `IBranchSaturationQ` | 4 | **0** |
| `IFimpAccessQ` | 4 | **0** |
| `IExpandedConsistentQ_sat` | 1 | **0** |
| `IExpandedAccessConsistentQ_sat` | 1 | **0** |

Every reference is self-contained inside `Scheme.lean` (definition sites, their own docstrings, and
the `_sat` lemma bodies). Nothing outside depends on any of them — including the two public ones,
`IBranchSaturationQ` (`structure`) and `IFimpAccessQ` (`def`). **Deletion is therefore
reference-safe**, and retention would leave ~480 lines of machinery whose central docstring claim is
independently false (see Defect 1 below). `lake shake` in Phase 8 would additionally flag the dead
weight. The four commits remain in git history as the record of the attempt.

### Defects Recorded

**Defect 1 — `intBlockRepStep`'s "agrees by construction" docstring claim is false.**
`intBlockRepStep` (`Scheme.lean:547-559`, Phase 5.1) claims (docstring `:540-546`) to agree with
`intFImpReuseWitnessAnc?` by construction. It does not:

- `intBlockRepStep` tests only `(posFormulasAt b x).contains φψ.1` — containment of the **single**
  formula `φ`. The expansion-time check (`Expansion.lean:279`) tests
  `sfor.all ((posFormulasAt bPers x).contains ·)` with `sfor = {φ} ∪ posFormulasAt bPers w` —
  containment of the **whole** forced set. Any branch with `φ ∈ posFormulasAt b x` but
  `posFormulasAt b w ⊄ posFormulasAt b x` makes `intBlockRepStep` fire where expansion never
  blocked.
- `negImpAt b w` (`Scheme.lean:526-533`) uses `List.findSome?`, silently selecting only the *first*
  `.neg`-signed implication at `w`; a world carrying two `F(·→·)` obligations has the other ignored.

Consequence: `intBlockRep` may identify worlds that were never blocked and miss worlds that were.
This is an independent second reason remedy (a) is not rescuable by reshaping `sfSatisfiedQ` alone —
even a perfectly-shaped `sfSatisfiedQ` would be instantiated at a `rep` that does not mean what its
docstring says. **The defect is retired by deletion in Phase 7.1**; no repair is attempted.

**Defect 2 — v01's H3 availability table is wrong in two places.** Corrected in the H3 table below:
(i) v01 claimed `ChagrovZakharyaschev1997` was the *only* one of the five keys in the navigable
corpus — `NegriVonPlato2001` **is** in the corpus (`negri_von_plato_2001`, 385 chunks,
`verified_conversion`); it is merely missing a `bib_key` field in the global index, so `/cite` will
not auto-link it. (ii) Massacci 2000, *Single Step Tableaux for Modal Logics* (JAR 24:319-364) is
**navigable locally** (`massacci_2000_single_step_tableaux_for_modal_logics`) and is the sharpest
readable statement of the per-world (Def. 8.1) vs. per-obligation (Def. 8.2) distinction this task
turns on — but it has **no BibKey in `references.bib`**. See D9 for how this is handled.

### Source-to-Implementation Mapping (H3, corrected)

| Source | Availability | Claim used | Where it lands | Verification |
|--------|--------------|------------|----------------|--------------|
| `GargGenoveseNegri2012` (`references.bib:228`), Def. III.4 + §III overview | **Not in local corpus — web-verified** (`people.mpi-sws.org/~dg/papers/lics12.pdf`) | Countermodel relations are `M ∪ C` with `C = {x ≤ y | Sfor(x) ⊆ Sfor(y)}` — i.e. **add loop-back edges**, do not quotient | Phase 6 (`augSets`, `augH ++ [(x, l)]`) | Live `lake build` of the prototype; the literature is corroboration, the build is the evidence |
| `GargGenoveseNegri2012` related work | web-verified | "we have not been able to find a suitable filtration on the obvious model whose worlds are equivalence classes of ⪯ ∩ ⪰ … extremely difficult to satisfy the 'back condition'" | Refutes v01's Phase 5 design | Recorded as refutation, not as design evidence |
| `GargGenoveseNegri2012` Lemma III.5 | web-verified | The valuation must be **separately proved monotone** w.r.t. the enlarged `≤` | Residual Risk R1 / Non-Goals | Names R1 as an expected obligation of this design, not a regression |
| `GargGenoveseNegri2012` Lemma III.6 / Cor. III.7 | web-verified | Truth lemma by **lexicographic** induction on (formula, original tree order ⊑) | Forward guidance for `truthLemma`'s T-imp `sorry` (Gap 1, **out of scope**) | Recorded only — any future T-imp attempt inducting on the formula alone is not well-founded |
| `ChagrovZakharyaschev1997` (`:75`) §5.3 p.141, Thm 5.23, cond. (iv′) | **In local corpus** (`chagrovzakharyaschev_1997_modallogic`, `chunk_0245`/`chunk_0246`) | The coarsest intuitionistic filtration `S̄` is literally `Sfor`-containment; GGN's `C` is its syntactic dual | Context for Phase 6's docstrings | Chunk-level quotes |
| `ChagrovZakharyaschev1997` p.141 warning | in corpus, `chunk_0246` | "a relation S between S̲ and S̄ may be nontransitive even if the original R is transitive … not all S in this interval give rise to filtrations of intuitionistic models" | Independent warning against v01's Phase 5.2 pullback premise | Chunk-level quote |
| Massacci 2000, Def. 8.1 vs 8.2 | **In local corpus** (`massacci_2000_…`, `chunk_0025`/`chunk_0026`, pp. 336-337) — **no BibKey** | Per-world vs. per-obligation copy shapes are **not interchangeable**; the repo's Option-A `F(ψ)@x` conjunct is the per-obligation (Def. 8.2), stronger shape | Explains why the reuse-site discharge is ~20 lines of direct term construction, not a transport lemma | Chunk-level quotes; see D9 for citation policy |
| `NegriVonPlato2001` (`:931`) | **IS in local corpus** (`negri_von_plato_2001`, 385 chunks) — v01's table said otherwise | G4ip weight measure — explicitly rejected (`propagatePersistence` breaks its decreasing-measure premise) | Recorded only (docstring provenance) | Corrected availability; still not used by the fix |
| `Fitting1983` (`:211`) Ch. 4 | **BibTeX key only — NOT navigable** | Loop-check blocking world is an **ancestor** | `intFImpReuseWitnessAnc?` (landed Phase 3) | **Provenance only** — its invariant shape could not be established from this repo |
| `Dyckhoff1992` (`:218`) | BibTeX key only | Contraction-free sequent calculi | not used | Provenance only; likely the wrong citation for a loop-check invariant |
| Divergence witness note (`Expansion.lean`) | In-repo, executable | `φ0` and the fuel→max-label table | Phase 1 (reproduced) | Real `#eval`, matched at 6/7 sampled points (see Phase 1) |

**H3 honesty rule (binding, carried forward and strengthened)**: three evidence tiers are kept
distinct — (1) **locally verified** (`ChagrovZakharyaschev1997`, Massacci 2000, chunk-level quotes);
(2) **web-verified** (`GargGenoveseNegri2012`, PDF fetched and quoted verbatim, *not* in this repo's
corpus); (3) **provenance only** (`Fitting1983`, `Dyckhoff1992`). **No load-bearing design decision
in this plan rests on a tier-3 citation.** The decisive evidence for the Phase 6 fix is the live
prototype build (claims C1-C9 of the blocker research); the literature corroborates the mechanism
and refutes the alternative. Where a docstring attributes a rule shape to a tier-3 source,
reproduce the attribution verbatim as provenance but do not use it as evidence.

**OCR caveat**: the Chagrov-Zakharyaschev conversion renders `□` variously as `D`/`U`/`O` and `⊨`
as `|=`. Any Lean docstring citing CZ must cite by section/theorem number, never by transcribed
symbol.

## Postmortem Constraints

Binding rules for every implementation dispatch on this task. Carried forward from v01 (derived
from the twelve failed plan versions in `317/reports/14_blocker-analysis.md`) with additions from
this revision.

**Do NOT**:

- **Do NOT trust any tableau docstring as evidence.** Confirmed stale/superseded, now including
  this task's own output:
  - `Scheme.lean:540-546` (`intBlockRepStep`) claims agreement with `intFImpReuseWitnessAnc?` "by
    construction" — **false**, see Defect 1. It is deleted in Phase 7.1, not repaired.
  - `Scheme.lean:~1009-1030` — the D5 design note landed in Phase 5.3, describing the quotient as
    the mechanism. Superseded by this revision; Phase 7.1 rewrites it.
  - `intAccessPreorderQ`'s docstring claim that "pulling back the closure suffices without
    re-deriving transitivity" — CZ p. 141 warns this is exactly the assumption that fails for
    intuitionistic models. Deleted in Phase 7.1.
  - `Rules.lean:270-278` claims each accessible world "eventually gets an independent reflexive
    resolution" — that was the divergence engine, not a feature.
- **Do NOT re-derive or re-attempt the refuted world bound.** `intApplyRuleFull_outputs_subset`'s
  `hnw : nextWorld ≤ φ0.complexity + 1` and `intUniverse`'s `List.range (φ.complexity + 2)` are
  refuted by counterexample. The exponential replacement is task 456's scope.
- **Do NOT attempt `truthLemma`'s T-imp case (`Scheme.lean:793`).** Gap 1 (persistence
  fuel-sufficiency), explicitly out of scope. Leave the `sorry` and its comment block intact. If a
  future dispatch does attempt it, GGN Lemma III.6 says the induction must be **lexicographic on
  (formula, original tree order ⊑)** — `truthLemma` currently inducts on the formula alone, so the
  present induction is not well-founded for that case.
- **Do NOT attempt `intExpandBranches_openBranch_sat`'s fuel-0 base case (`Scheme.lean:2970`).**
  Its in-proof note records a Lean-verified counter-instance (`branches = [[F(p∧q)@0]]` refuting
  `sat_fand`): the goal is **refuted at the current statement**, not merely hard. Phase 6 changes
  the lemma's *signature* and threads a new list; it must leave the fuel-0 `sorry` and its 26-line
  refutation note byte-identical. The note remains valid verbatim — `sat_fand` is untouched by this
  fix.
- **Do NOT close the two `Completeness.lean` bridges** (`Intuitionistic/Completeness.lean:133`,
  `Minimal/Completeness.lean:125`). Out of scope. See Residual Risk R1 for what the loop-back edge
  adds to their (already open) obligation.
- **Do NOT introduce `Option B` branch modification at the reuse site.** Appending a fresh `F(ψ)@x`
  entry on reuse was tried and found **UNSOUND** against `intExpandBranches_closed_unsat`. The reuse
  arm must recurse on `bPers` **unmodified**, with the algorithm's `edges` and world counter
  **unchanged**. The loop-back edge in Phase 6 goes into the **invariant-side** `augSets` list only —
  never into `intExpandBranches`'s own `edgeSets`, never into `intFImpRule`'s return value. This
  distinction is the whole mechanism; violating it puts a Preserved Asset at risk for zero benefit
  (explicitly considered and rejected by the blocker research).
- **Do NOT thread an `edges` parameter into `intApplyRuleFull` / `intApplyRule` / `intStepBranch`.**
  Their signatures are load-bearing for ~15 lemmas across `Soundness.lean` and `Scheme.lean`.
- **Do NOT change `intExpandBranches.go`'s argument list.** It still threads its own
  `pendingEdges`/`doneEdges`. The decoupling of the algorithm's list from the invariant's list is
  what makes the fix work; a dispatch that "simplifies" by merging them has undone it.
- **Do NOT transcribe a conformance expected-value that contradicts the formula's semantics.**
  Regenerating from real `#eval` output means *running it, not guessing it* — it does **not** license
  writing `OPEN` next to an IPC-valid formula. Such a divergence is a **defect in this repair** and a
  Phase 8 blocker.
- **Do NOT cite task numbers in any `Cslib/` or `CslibTests/` file.** Per
  `.claude/rules/no-task-references-in-deliverables.md`, docstrings must reference durable anchors
  (declaration names, section headings, BibKeys), never "task N". The Phase-4 inline annotation
  `TEMPORARY (task phase 4 -> phase 6)` is removed along with the `sorry` in Phase 6.3.
- **Do NOT `git reset --hard` / `git checkout --` / `git clean -fd` to reach a green build.** Fix
  forward; if a snapshot is genuinely needed run `bash .claude/scripts/git-snapshot.sh 574` first.
- **Do NOT run bare `lake build` as the routine inner-loop check.** Use
  `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.<Module>`; reserve full `lake build`
  for phase-end and the Phase 8 gate.

**MUST preserve**:

- Every row of the Preserved Assets table, and the exact 6-entry sorry baseline at task completion.
- `Soundness.lean`'s sorry-free status at **every** phase boundary. It is the only file in the
  tableau tree with zero sorries; it must never acquire one, not even temporarily.
- `grep -c "IBranchSaturation" Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
  must remain `0` — the saturation layer stays out of the soundness dependency cone.
- The 24 temporal conformance rows (`temporalTableau`, a different calculus) must stay green and
  unedited.
- `intFImpRule`'s returned edge orientation `(w', w)` = `(child, parent)`. All four consumers depend
  on it, and the loop-back edge `(x, l)` is oriented to match (`isAccessible aug l x` in one hop via
  `isAccessible_one_step`).
- `intExpandBranches_openBranch_initial_mem` (`Scheme.lean:3199-3345`) has its **own** `suffices key`
  at `:3227`. It is a different lemma and is **out of Phase 6's territory** — do not edit it.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample or a measurement
that contradicts them):

- **D1 — In-place body swap, not a duplicated expansion loop.** *(Landed, Phases 3-4. Confirmed
  correct: the `some x` arm never uses `x`, so `Soundness.lean` needed only mechanical identifier
  renames.)*
- **D2 — STEP 1 is bounding the self-copy, not redesigning `.pos,.imp` to range over accessible
  labels.** *(Landed, Phase 2. `sat_timp`-at-accessible-worlds is Gap 1, out of scope.)*
- **D3 — The termination mechanism is the ancestor blocking check, not the self-copy removal.**
  *(Confirmed by Phase 1 measurement: V3 = V1 exactly; removing the self-copy alone changes
  nothing.)*
- **D4 — The `F(ψ)@x` conjunct is RETAINED.** *(Resolved by Phase 1 measurement: V1 terminates at
  maxLabel 21; all 19 conformance rows match.)* **This revision upgrades D4 from "cheaper" to
  "load-bearing"**: retaining the conjunct is a Massacci Def. 8.2 (per-obligation) blocking shape,
  which means the witness `x` carries the obligation's `T(φ)`/`F(ψ)` entries **explicitly on the
  branch**. That is exactly why Phase 6.3's discharge is ~20 lines of direct term construction
  (`houtPhi` and `hFpsi` *are* the needed facts) rather than an appeal to an `Sfor`-transport lemma,
  which is what GGN's weaker per-world condition forces them to prove.
- **D5 — SUPERSEDED.** v01's D5 held that the quotient repairs the ordering/accessibility conjunct
  by identifying `w` with its blocking ancestor under `rep`. A Phase 6 dispatch refuted it in
  practice and the blocker research refuted it structurally: `intBlockRep` is a function of the
  *final* branch/edge list, the induction runs *forward*, and `intBlockRep` is not monotone under
  branch growth (`negImpAt`'s `findSome?` and `posFormulasAt` both move). Reshaping *which relation*
  the conjunct asserts does not make `rep` available mid-induction. Superseded by D7.
- **D7 (NEW) — The mechanism is an invariant-side augmented edge list, not a quotient.**
  `intExpandBranches_openBranch_sat`'s conclusion existentially quantifies `edges`; nothing in
  `intExpandBranches`, `Soundness.lean`, or the acceptance gate observes which list is returned. A
  parallel `augSets` list is threaded through the induction, and each blocking event appends the
  loop-back edge `(x, l)` **at the moment it happens**. The forward/backward mismatch that defeats
  D5 simply does not arise, because the invariant's accessibility relation is constructed forward in
  lockstep with the induction. Soundness: `hcont` gives `posFormulasAt bPers l ⊆ posFormulasAt bPers
  x` and ancestor persistence gives the converse, so `x` and `l` force the same positive formulas;
  `IForces` (`Semantics/Kripke.lean:81`) is defined over `[Preorder World]` with **no antisymmetry**,
  so the resulting cycle is admissible.
  *Rejected alternative (recorded)*: existentially quantifying the extra edges **inside**
  `IExpandedAccessConsistent` (`∃ extra, ∀ sf ∈ e, sfAccessSat (edges ++ extra) b sf`). Rejected
  because the world-creation step then needs `(edges ++ extra) ++ [newEdge]` to agree with
  `(edges ++ [newEdge]) ++ extra` — a permutation-invariance lemma for `isAccessible` that does not
  exist. Parallel `augSets` avoids it: every append is at the end.
- **D8 (NEW) — The numeric ordering conjunct is DROPPED from both `sfSatisfied`'s `.neg,.imp` clause
  and `IBranchSaturation.sat_fimp`.** It is a raw-`Nat` proxy for accessibility that held only
  because labels increased monotonically under descendant-directed creation; under ancestor blocking
  it is **false** (`x < l`). **Verified never consumed**: `IBranchSaturation.sat_fimp` is *produced*
  (`IExpandedConsistent_sat`) but `grep -rn "sat_fimp"` across `Cslib/` returns only docstrings and
  the two producer bullets; `truthLemma`'s F-imp case reads its witness from
  `hfimp : IFimpAccess edges b`, never from `hsat.sat_fimp`. The two external `IBranchSaturation`
  hypothesis positions (`Intuitionistic/Completeness.lean:76`, `Minimal/Completeness.lean:80`) are
  *weakened* by the drop, hence still satisfiable. This is a **correction**, not a
  weakening-to-avoid-work: the genuine content (the witness is accessible) is carried in strictly
  stronger form by `IFimpAccess`.
- **D9 (NEW) — No new `references.bib` entries; Massacci stays at plan level.** v01's Non-Goal
  ("adding new `references.bib` entries") is retained. Lean docstrings written in Phases 6-7 cite
  only the five existing keys. Massacci 2000's Def. 8.1/8.2 distinction is recorded **in this plan**
  as the locally-verified justification for D4, and Lean docstrings state the per-obligation property
  in their own words without attributing it. Rationale: adding a BibKey is a separate, reviewable
  library change with its own conventions, and nothing in the fix path requires the citation.
  *If a future dispatch judges the attribution necessary, adding the key becomes an explicit,
  separately-scoped item — not an inline improvisation.*

## Goals & Non-Goals

**Goals**:
- *(Landed)* Replace `intFImpReuseWitness?`'s descendant search with an ancestor-directed
  `Sfor`-containment blocking check and repoint `intExpandBranches`'s single call site.
- *(Landed)* Remove `applyAllTImpRules`'s `T(φ→ψ)` self-copy channel and repair the coupled
  `Soundness.lean` lemmas.
- **Make the ancestor witness admissible by recording each blocking event as a loop-back edge in the
  saturation invariant's own accessibility relation**, exploiting
  `intExpandBranches_openBranch_sat`'s existential `edges` — GGN's `M ∪ C` construction, not a
  quotient frame. *(Replaces v01's "restate the predicate stack over a blocking-quotient frame"
  goal.)*
- Drop the never-consumed numeric ordering conjunct from `sfSatisfied`'s `.neg,.imp` clause and
  `IBranchSaturation.sat_fimp` (D8).
- Retire the Phase-4 temporary `sorry`, restoring the exact 6-entry baseline.
- Delete the superseded Phase 5 quotient stack and reconcile the docstrings it left behind.
- Keep `intExpandBranches_closed_unsat` sorry-free and axiom-clean (**the acceptance gate**).
- Update `CslibTests/TableauConformance.lean` from real `#eval` output.

**Non-Goals** (explicitly out of scope; attempting them is a plan violation):
- Re-deriving the numeric world bound (task 456's `Tableau.distinctTypes_le_pow`).
- Closing `truthLemma`'s T-imp `sorry` (`Scheme.lean:793`) — Gap 1, persistence fuel-sufficiency.
  Forward note: GGN Lemma III.6 requires a **lexicographic induction on (formula, original tree
  order ⊑)**; the current induction on the formula alone is not well-founded for this case.
- Closing `intExpandBranches_openBranch_sat`'s fuel-0 `sorry` (`Scheme.lean:2970`) — refuted at its
  current statement.
- **Closing the two `Completeness.lean` bridges (`:133`, `:125`), including the `intExtractValuation`
  monotonicity obligation *against the enlarged preorder*.** This is Residual Risk R1 below and is
  the same obligation GGN prove separately as their **Lemma III.5** ("the valuation `h` is still
  monotone w.r.t. the enlarged `≤`"). It is a **named, expected obligation of the design that
  works**, not a regression introduced by this fix — the quotient design carries an isomorphic
  obligation, and `intBlockRep`'s post-hoc test establishes strictly *less* than `hcont` does. The
  obligation lives entirely inside declarations that already carry `sorry`s listed above; nothing in
  the Phase 6-8 fix path touches them.
- Any change to the temporal or classical tableau, or to the modal `FmpMeasure` development.
- Adding new `references.bib` entries (D9).
- Repairing `intBlockRepStep`/`negImpAt` (Defect 1) — they are deleted, not fixed.

## Risks & Mitigations

- **Risk (highest, and NOT a regression): R1 — the enlarged preorder's valuation-monotonicity
  bridge.** `intAccessPreorder aug` contains `l ⊑ x`. `tableau_complete`'s docstring defers an
  upward-closure obligation on `intExtractValuation b` to `hvalid`'s callers — i.e. to the two open
  `sorry`s at `Intuitionistic/Completeness.lean:133` and `Minimal/Completeness.lean:125`. Along the
  loop-back edge that obligation reads: every atom positive at `l` on the **final** branch `b` must
  be positive at `x`. `hcont` establishes exactly this on `bPers` — the branch at *block time*, not
  on `b`; later growth at `l` is not propagated to `x`.
  *Mitigation*: containment, not closure. The obligation lives entirely in already-`sorry`ed,
  explicitly out-of-scope declarations, and no fix-path step touches them. It is **named in the
  literature** (GGN Lemma III.5) and is the price of the construction that works; any construction
  that discharges `F(φ→ψ)@l` with an ancestor witness must place that witness above `l` in the
  model. Recorded in Non-Goals with this analysis attached rather than left implicit.
- **Risk: `tableau_complete`'s public contract changes.** *Mitigation*: **retired.** `hvalid` is
  already `∀ (edges : IEdges) (b : IBranch Atom), IForces …` — universally quantified over *all* edge
  lists, so an augmented list is already in scope (`Scheme.lean:3402-3406`). Caller obligation is
  textually identical (blocker-research C11, verified by reading).
- **Risk: dropping `sat_fimp`'s conjunct breaks a downstream consumer.** *Mitigation*: verified never
  consumed (D8), and the prototype's full `lake build` is green with both `Completeness.lean` files
  unmodified (C7). The two external hypothesis positions only weaken.
- **Risk: deleting ~480 lines shifts `lake shake`'s import minimisation.** The Phase 5 stack is
  additive and mostly `private`, but `lake lint` / `lake exe lint-style` / `lake shake` were **not**
  run by the research dispatch. *Mitigation*: Phase 7.1 runs a full `lake build` immediately after
  deletion, and Phase 8 runs `shake --fix` as its own objective. An unexpected import ripple is a
  recorded hypothesis miss, not a silent widening.
- **Risk: the conformance corpus reveals a completeness regression.** *Mitigation*: largely retired.
  Phase 1 pre-ran all 19 propositional formulas under V1/V2/V3 — **all 19 rows matched** under each.
  The Phase 6-7 fix is **proof-side only** (no `intExpandBranches`, `intFImpRule`, or
  `intFImpReuseWitnessAnc?` behaviour change), so conformance verdicts cannot move as a result of it
  (C4/R4). Phase 8 still runs them for real.
- **Risk: the temporary sorry is forgotten and ships.** *Mitigation*: it is a declared Phase 6.3 exit
  criterion (`grep` count = 6), a Phase 8 final gate, and a Rollback trigger.
- **Risk: context exhaustion mid-phase on the 3,417-line `Scheme.lean`.** *Mitigation*: every
  Scheme-touching phase is split into sub-phases with per-sub-phase green commits; never read
  `Scheme.lean` whole — use `offset`/`limit` against the line anchors in each phase. Phase 6 in
  particular has three declared green commit points.
- **Risk: a dispatch "improves" on the verified prototype and diverges from it.** *Mitigation*: the
  prototype patch (`scratch/phase6-prototype.patch`) is checked into the task directory and applies
  against the current tree. Phase 6's exit criterion includes a `diff` against
  `scratch/Scheme.lean.prototype` restricted to the fix's line ranges; a deviation must be justified
  in the phase record, not absorbed.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5 | 3 (Phase 4 also needs 2) |
| 4 | 6 | 4 |
| 5 | 7 | 6 |
| 6 | 8 | 2, 7 |

Waves 1-3 are complete. The remaining path (6 → 7 → 8) is strictly sequential; there is no
parallelism left and therefore no active H7 territory contract. For the historical record, the
territory contract that governed wave 2-3 was:

| Wave | Phase | Owned (exclusive write access) |
|------|-------|-------------------------------|
| 2 | 2 | `Expansion.lean` (`applyAllTImpRules`), `Soundness.lean:374-454`, `:791-830` |
| 2 | 3 | `Expansion.lean` (`Sfor`-containment section, appended) |
| 3 | 4 | `Expansion.lean` (`go` call site), `Soundness.lean:1390-1420`, `1470-1519`, `1570-1661` |
| 3 | 5 | `Scheme.lean` new sections after `:492` and `:848` |

**Phase 6-8 territory** (single-owner, sequential): Phase 6 owns `Scheme.lean:97-101`, `:948-1006`,
`:1473-1600`, `:2930-3198`, `:3346-3375`. Phase 7 owns `Scheme.lean:526-678`, `:1009-1240`, `:1340`,
`:1896` (deletions) plus the docstring regions they leave behind. Phase 8 owns
`CslibTests/TableauConformance.lean` and whatever `lake shake --fix` emits. **No phase touches
`Soundness.lean`.**

---

### Phase 1: Divergence-attribution probe and variant selection [COMPLETED]

- **Goal:** Convert every open design fork (D3, D4, and STEP 1's shape) from an argument into a
  measured `#eval` table, **before any `Cslib/` file is written**.
- **Tasks:**
  - [x] Create `scratch/DivergenceProbe.lean`, compiled with `lake env lean` (a standalone file gets
        the built oleans; `#eval` does not reduce from inside `Cslib/Logics/.../Tableau/`). Split
        across `DivergenceProbe.lean` + four companion files (`ProbeControl.lean`,
        `ProbeHighFuel.lean`, `ProbeV3.lean`, `ProbeConformance.lean`) due to a compute-time scope
        adaptation — see `handoffs/01_variant-selection.md`'s Method section.
  - [x] Define the witness `φ0 = (((a→b)→c) ∧ ((d→e)→f)) → ((u₁→v₁) ∨ (u₂→v₂))` over
        `Proposition Nat` and a `worldStats` adapter reporting branch length / max label / distinct
        label count.
  - [x] **Baseline row (fidelity check).** `#eval` the unmodified library at
        `fuel ∈ {10,…,260}` and confirm max label `= 4,7,10,14,21,27,40,54,67,87`.
        **6/7 sampled points matched exactly; fuel=60 measured 20 vs. the docstring's recorded 21**
        (re-confirmed twice). Assessed as a minor docstring transcription discrepancy, not a stale
        witness — the qualitative divergence claim is confirmed at every sampled point. Does not
        trigger STOP; see handoff Table 1.
  - [x] Define four scratch variants (V0 control, V1 ancestor/conjunct-retained, V2
        ancestor/conjunct-dropped, V3 = V1 + self-copy removed). *(V0 corrected mid-phase: the true
        control is an exact copy of the library's current descendant-direction check, not "no check
        at all"; confirmed to reproduce baseline exactly, handoff Table 2.)*
  - [x] Run the fuel ladder for V1, V2, V3. **Result: V1 saturates at maxLabel=21 (fuel≥120); V2 at
        maxLabel=15 (fuel≥80); V3 at maxLabel=21, identical to V1.** See handoff Table 3.
  - [x] Run all **19 propositional formulas** from `TableauConformance.lean` under each terminating
        variant. **Result: ALL 19 ROWS MATCH under V1, V2, and V3.** See handoff Table 4.
  - [x] Write `handoffs/01_variant-selection.md`. **D3 confirmed (STEP 2 is the termination
        mechanism); D4 resolved to conjunct RETAINED (V1 selected).**
  - [x] **Escalation branches** (V1 non-terminating; neither terminating): **evaluated, neither
        fires.**
- **Timing:** 4-6 hours *(actual: within window)*
- **Depends on:** none
- **Verification Tier:** local
- **Commit Mode:** per-substep
- **Scope Hypothesis:** ~200 lines of scratch Lean and one ~80-line decision record; ~97 `#eval`
  invocations. **This phase writes zero lines to `Cslib/`** — hypothesis held.
- **Done when:** `handoffs/01_variant-selection.md` exists with the baseline row and a named selected
  variant. **Satisfied.**

---

### Phase 2: Bound the T-implication self-copy channel (STEP 1) [COMPLETED]

- **Goal:** Remove `applyAllTImpRules`'s `T(φ→ψ)` self-copy and repair the `Soundness.lean` lemmas
  structurally coupled to its definition.
- **Tasks:**
  - [x] Edit `applyAllTImpRules`: **removal** (Phase 1/D3 selected V3's shape) — `combined` is now
        literally `toAdd`, no `++ copies`.
  - [x] Rewrite the def's docstring: the Deliverable-6 paragraph was false. States what changed, that
        `sat_timp`-as-a-field is unaffected (D2, `le_rfl` reference), and that
        `sat_timp`-at-accessible-worlds (Gap 1) remains open and out of scope.
  - [x] Repair `applyAllTImpRules_sat` (`Soundness.lean:374-454`): the `by_cases hemp` term and the
        `List.mem_append` split re-derived; the `hmem_copy` arm deleted. `lake lint` emits no new
        warning for `_v_uc`/`_bf_uc`.
  - [x] Repair `freshAbove_applyAllTImpRules` (`Soundness.lean:791-830`).
  - [x] Confirm `applyPersistenceFixpoint_sat` and `freshAbove_applyPersistenceFixpoint` need **no**
        statement change — confirmed via `git diff`, zero lines changed in either.
  - [x] `lake build …Soundness` green; `grep -c sorry Soundness.lean` = 0.
- **Timing:** 5-8 hours
- **Depends on:** 1
- **Verification Tier:** interface
- **Commit Mode:** atomic-batch — declared file set: `Expansion.lean` (`applyAllTImpRules` + its
  docstring), `Soundness.lean:374-454`, `:791-830`.
- **Scope Hypothesis:** ~180 lines across exactly 2 files and 4 declarations.
  **HYPOTHESIS MISS (recorded, not silently absorbed):** a third file, `Scheme.lean`, turned red —
  two `rfl`-based unfoldings of the literal old body
  (`applyPersistenceFixpoint_genuine_of_count_le_fuel`), three declarations pattern-matching the old
  `toAdd ++ copies` shape (`applyAllTImpRules_subset`, `applyAllTImpRules_count_drop`,
  `ILabelBound_applyAllTImpRules`), and one now-dead helper deleted outright
  (`applyAllTImpRules_copy_notMem`). Foreseeable — this phase's own Verification Tier field already
  enumerated `Scheme.lean` as a direct dependent — but the file-count claim undersold it. Fixed
  forward per the recovery contract. Actual delta: 3 files; `Expansion.lean` (37 net),
  `Soundness.lean` (112 net), `Scheme.lean` (156 net, mostly deletions). Full `lake build` green;
  `intExpandBranches_closed_unsat` unaffected: `{propext, Classical.choice, Quot.sound}`.
- **Done when:** the Soundness module builds green with 0 sorries and
  `grep -n "copies\|accessibleWorlds" Expansion.lean` shows no match inside `applyAllTImpRules`.
  **Both satisfied**; repo-wide bare-sorry count remained exactly 6; `checkInitImports` clean.

---

### Phase 3: Ancestor-directed blocking check, additive [COMPLETED]

- **Goal:** Land `intFImpReuseWitnessAnc?` and `intFImpReuseWitnessAnc?_spec` alongside the existing
  pair, with **no call-site change**.
- **Tasks:**
  - [x] Append `intFImpReuseWitnessAnc?` — type-identical to `intFImpReuseWitness?`, body identical
        except `isAccessible edges w x` → `isAccessible edges x w`, `w.ble x` → `x.ble w`, and the
        `F(ψ)@x` conjunct per D4 (**retained**).
  - [x] Write the def's docstring from scratch: search direction and why (ancestors; `Sfor` grows
        monotonically along accessibility — attributed to `GargGenoveseNegri2012`/`Fitting1983` as
        *provenance*, with an explicit note those sources are not readable in-repo and the design
        rests on the Phase 1 measurement); the exact search order; and the reuse contract (recurse on
        `bPers` unchanged, `edges` unchanged, world counter unconsumed — never Option B).
  - [x] State and prove `intFImpReuseWitnessAnc?_spec`. **5-tuple landed** (conjunct retained), proof
        transferred verbatim with the two directional conjuncts swapped.
  - [x] Mark the old `intFImpReuseWitness?` docstring as superseded with a one-line pointer; do not
        delete the def yet.
  - [x] `lake build …Expansion` green. **Tooling note**: `lean_verify` rejects theorem names
        containing `?` (`"Invalid theorem name"`, reproduced against the pre-existing
        `intFImpReuseWitness?_spec` as a control) — a tool limitation. Verified equivalently via
        `lake build` + `grep`.
- **Timing:** 4-6 hours
- **Depends on:** 1
- **Verification Tier:** local
- **Commit Mode:** per-substep
- **Scope Hypothesis:** ~130 lines added to exactly one file, zero lines removed. **Confirmed**:
  `git diff --stat` shows `Expansion.lean`, `107 insertions(+), 1 deletion(-)` — the single deletion
  is the superseded-docstring pointer edit.
- **Done when:** both pairs exist side by side and the module builds green. **Confirmed**;
  `checkInitImports` exit 0; bare-sorry count unchanged at 6.

---

### Phase 4: Repoint the call site and re-verify the acceptance gate [COMPLETED]

- **Goal:** Swap `intExpandBranches`'s single loop-check call site to `intFImpReuseWitnessAnc?`, then
  re-verify `intExpandBranches_closed_unsat` sorry-free and axiom-clean — **the task's explicit
  acceptance gate**.
- **Tasks:**
  - [x] Change the call site to `intFImpReuseWitnessAnc? bPers edges newForms e`; update the
        surrounding comment to say *ancestor*, matching the code for the first time.
  - [x] **Objective A — arm 1** (`Soundness.lean`, `bp = bh`). Confirmed the `some _x` reuse arm never
        uses `x`: `lake build` green with only the `rcases hwit` identifier swapped; the closing block
        applied verbatim, zero additional tactic changes. Matches the spike's H1 evidence exactly.
  - [x] **Objective B — arm 2** (`Soundness.lean`, `bp ∈ bt`). Same identifier-only swap; closed
        verbatim on first attempt. This is the **first-time** verification the spike explicitly left
        open (§4 Scope Note: "strongly indicated, not proven").
  - [x] **Inserted exactly one tracked temporary `sorry`** at `Scheme.lean`'s reuse-site discharge
        (now line 3143). `intFImpReuseWitnessAnc?_spec hψ heq`'s `hacc`/`hle` witness the reversed
        ancestor-direction conjuncts (`isAccessible edges x l`, `x ≤ l`) which
        `sfSatisfied`/`sfAccessSat`'s `.neg,.imp` clauses cannot consume directly. The two
        `hIC_reuse`/`hACC_reuse` discharges were combined into one
        `have hreuse_sat : … ∧ … := by sorry`, with `hIC_reuse`/`hACC_reuse` re-derived as `.1`/`.2`
        projections so no downstream line changed. It is in `Scheme.lean`, never `Soundness.lean`.
  - [x] Deleted `intFImpReuseWitness?` and `intFImpReuseWitness?_spec` from `Expansion.lean`.
  - [x] `lake build` full: 3309/3309 jobs green.
  - [x] **Gate**: `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` with
        `scan_source: false` and a standalone `#print axioms` both return exactly
        `{"axioms":["propext","Classical.choice","Quot.sound"]}`. **Tooling note**: `lean_verify`
        with default `scan_source: true` spuriously reported `sorryAx` even though neither
        `lake build`'s warnings nor a manual `#print axioms` shows any such dependency — a second
        `lean_verify` quirk. Cross-verified via two independent methods before trusting the result.
  - [x] **Gate**: `minimalTableau_sound` and `intuitionisticTableau_sound` both
        `{propext, Classical.choice, Quot.sound}`, sorry-free.
  - [x] **Gate**: `grep -c sorry Soundness.lean` = 0 and `grep -c IBranchSaturation Soundness.lean`
        = 0. Both confirmed.
- **Timing:** 6-9 hours
- **Depends on:** 2, 3
- **Verification Tier:** full — this phase changes the decision procedure's runtime behaviour and is
  the acceptance gate.
- **Commit Mode:** per-substep
- **Scope Hypothesis:** the swap is one identifier on one line plus comment updates; `Soundness.lean`
  needs **zero** proof-body edits. **Partial miss, recorded:** `git diff --stat` shows 10 changed
  lines in `Soundness.lean` (6+/4-), because the proof's own `rcases hwit : intFImpReuseWitness? …`
  match sites are themselves identifier occurrences of the swapped function. This is a **mechanical**
  identifier-rename miss, not a proof-body miss: every tactic term in both arms' closing blocks is
  byte-identical before and after. H1's substantive claim holds exactly as predicted.
- **Done when:** all four gates pass and exactly one temporary sorry exists beyond the 6-entry
  baseline. **All satisfied.**

---

### Phase 5: Blocking-quotient frame and quotient-restated saturation predicates [COMPLETED]

> **SUPERSEDED — output scheduled for deletion in Phase 7.1.** This phase executed exactly as
> planned and its four sub-phases each landed green (`b70eadc0`, `1a1eba9f`, `a9eb2e47`,
> `07ab747c`). The *plan* it executed was wrong: the quotient mechanism cannot carry
> `intExpandBranches_openBranch_sat`'s forward induction (see D5-superseded, D7, and Defect 1).
> **The work is not deleted from history and is not being disowned** — it is the evidence that
> refuted the quotient route, and the Phase 6 dispatch that exercised it produced the counterexample
> analysis that made the blocker research targeted enough to succeed. Its ~480 lines are, however,
> dead code in the tree and are removed in Phase 7.1. The record below is preserved verbatim as the
> account of what landed.

- **Goal:** Build the `rep`-based quotient frame in `Scheme.lean` and restate the full saturation
  predicate stack over it, additively.
- **Tasks (5.1 — the representative map):** **[COMPLETED]**
  - [x] Read `ChagrovZakharyaschev1997`'s filtration material via `literature-search.sh --toc
        chagrovzakharyaschev_1997_modallogic`, then `p02_kripke-semantics.md` lines 395-470
        (filtration definition, Theorem 5.23, the finest/coarsest interval, transitive-closure
        construction); cited in the new section's docstring by line range, not just the BibTeX key.
  - [x] Define `intBlockRep (b : IBranch Atom) (edges : IEdges) : Nat → Nat`. **Implementation note**
        (not a plan deviation): defined via well-founded recursion chasing a one-step helper
        `intBlockRepStep` to a fixed point, using a STRICT `x < w` conjunct as the termination
        measure. *(Post-hoc: `intBlockRepStep`'s "agrees by construction" claim is **false** — see
        Defect 1.)*
  - [x] Prove `intBlockRep_idempotent` and `intBlockRep_le`, via two unfolding equation lemmas.
        Committed `task 574 phase 5.1` (`b70eadc0`).
- **Tasks (5.2 — the quotient preorder):** **[COMPLETED]**
  - [x] Define `intAccessPreorderQ (edges) (rep) : Preorder Nat` as the `rep`-pullback of
        `intAccessPreorder`. *(Post-hoc: CZ p. 141 warns the pullback assumption is exactly the one
        that fails for intuitionistic models.)*
  - [x] Prove `intAccessPreorderQ_le_of_isAccessible` and `intAccessPreorderQ_le_of_rep_eq`.
  - [x] `lake build …Scheme` green. Committed `task 574 phase 5.2` (`1a1eba9f`).
- **Tasks (5.3 — the `sf`-level predicates):** **[COMPLETED]**
  - [x] Define `sfSatisfiedQ` (`.neg,.imp`: `rep sf.label ≤ rep w'`), `sfAccessSatQ`,
        `IExpandedConsistentQ`, `IExpandedAccessConsistentQ`; prove `sfSatisfiedQ_mono` and
        `IExpandedConsistentQ_mono` (both transferred verbatim).
  - [x] Rewrite the superseded design note at `Scheme.lean:823-834` with the D5 rationale; fix a
        stale `intFImpReuseWitness?_spec` reference to the renamed `Anc` spec. Committed
        `task 574 phase 5.3` (`a9eb2e47`). *(Post-hoc: the raw-`Nat.le`-on-representatives shape of
        `sfSatisfiedQ`'s `.neg,.imp` field is where the Phase 6 dispatch's counterexample landed.)*
- **Tasks (5.4 — branch-level predicates and extraction):** **[COMPLETED]**
  - [x] Define `IBranchSaturationQ` and `IFimpAccessQ`; prove `IExpandedConsistentQ_sat` and
        `IExpandedAccessConsistentQ_sat` (both transferred verbatim, no new tactic steps).
  - [x] `lake build …Scheme` and `…Minimal.Soundness` green. Committed `task 574 phase 5.4`
        (`07ab747c`).
- **Timing:** 14-21 hours
- **Depends on:** 3
- **Verification Tier:** local
- **Commit Mode:** per-substep — four separate green commits
- **Scope Hypothesis:** ~480 lines added to exactly one file, ~15 new declarations. Two load-bearing
  sub-hypotheses: (i) `intBlockRep` definable without a new recursion/fuel parameter — **held**, via
  well-founded recursion; (ii) `sat_fimp`'s Q-restatement stays definitionally identical to
  `sfSatisfiedQ`'s clause so the extraction closes by `exact hsat` — **held**.
  **Retrospective hypothesis miss, recorded at revision time**: the phase's Scope Hypothesis checked
  *elaboration* and *line count* but had no check that the Q-shape was a **provable load-bearing
  inductive invariant**. v01's own D5 noted the shape was "confirmed to elaborate cleanly" — that was
  the only evidence, and it was insufficient. This is the lesson this revision encodes by requiring a
  **built, verified prototype** before Phase 6 re-dispatch.
- **Done when:** the lifting lemmas and both `_sat` extraction lemmas are proved sorry-free and the
  Q-predicates exist alongside the originals. **Satisfied** — and superseded.

---

### Phase 6: Loop-back-edge saturation invariant; retire the temporary sorry [COMPLETED]

- **Goal:** Drop the dead numeric ordering conjunct (D8), thread the invariant-side augmented edge
  list `augSets` through `intExpandBranches_openBranch_sat`'s induction (D7), and close the Phase-4
  temporary `sorry` with the loop-back-edge discharge — restoring the exact 6-entry sorry baseline.

**Ground truth for this phase**: `scratch/phase6-prototype.patch` (94 changed lines against the
current `Scheme.lean`) and `scratch/Scheme.lean.prototype` (the full verified file). Both were built
against this exact tree state and are `lake build`-green. **Consult them freely.** They are a
reference, not a substitute for the sub-step decomposition below: the phase lands as three green
commits so that a failure is localised, and the exit criterion is a `diff` confirming convergence to
the prototype's shape in the fix's line ranges.

Start by confirming the patch still applies: `git apply --check
specs/574_tableau_calculus_repair_ancestor_blocking/scratch/phase6-prototype.patch`. If it does not
apply cleanly, the tree has drifted from the research dispatch's baseline — **stop and record that**
before proceeding; do not silently re-derive.

- **Sub-phase structure:** three bounded units, each its own green commit — 6.1 (retire the numeric
  proxy), 6.2 (thread the invariant-side list), 6.3 (close the reuse-site discharge). 6.1's steps 1-3
  are red-until-step-3 and are one `atomic-batch` objective; 6.2's steps 4-8 are red-until-step-8 and
  are one `atomic-batch` objective; 6.3 is a single green step.

**Tasks (6.1 — retire the `sat_fimp` numeric proxy):**

- [x] **Step 1.** Amend `sfSatisfied`'s `.neg,.imp` clause (`Scheme.lean:948`ff, the clause at
      `:962-965`): drop the `sf.label ≤ w' ∧`. Target shape:
      ```lean
        | .neg, .imp φ ψ =>
          ∃ w' : Nat,
            b.any (fun x => x.sign == .pos && x.formula == φ && x.label == w') = true ∧
            b.any (fun x => x.sign == .neg && x.formula == ψ && x.label == w') = true
      ```
      *(red)*
- [x] **Step 2.** Amend `IBranchSaturation.sat_fimp` (`Scheme.lean:97-101`): drop the `w ≤ w' ∧`.
      Target shape:
      ```lean
        sat_fimp : ∀ (φ ψ : Proposition Atom) (w : Nat),
            b.any (fun sf => sf.sign == .neg && sf.formula == .imp φ ψ && sf.label == w) = true →
            ∃ (w' : Nat),
              b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w') = true ∧
              b.any (fun sf => sf.sign == .neg && sf.formula == ψ && sf.label == w') = true
      ```
      Update its doc comment **and** the `sat_fimp` note at `:72-73`. The new prose must state D8's
      content in durable terms: the numeric conjunct was a proxy for accessibility valid only under
      monotonically-increasing labels; under ancestor-directed blocking the witness carries a
      *smaller* label; the genuine accessibility content is carried in strictly stronger form by
      `IFimpAccess`. **No task-number references.** *(red)*
- [x] **Step 3.** Repair the two arity fallouts:
      - `sfSatisfied_mono`'s `.neg,.imp` arm (`:1000-1001`):
        ```lean
            | (obtain ⟨w', h1, h2⟩ := h
               exact ⟨w', any_mono_sub hmono h1, any_mono_sub hmono h2⟩)
        ```
      - `intStepBranch_linear_preserves`'s fresh-world `refine` (`:1563`) — drop `hsfl`:
        ```lean
                  refine ⟨nw, List.any_eq_true.mpr ⟨⟨.pos, φ, nw⟩, hmemNew _ ?_, by simp⟩,
                          List.any_eq_true.mpr ⟨⟨.neg, ψ, nw⟩, hmemNew _ ?_, by simp⟩⟩ <;>
        ```
      **Verify**: `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` **green**
      (7 sorries — the temporary is still present). Then `lake build` (full) to confirm both
      `Completeness.lean` files and `Soundness.lean` are unaffected. Commit
      `task 574 phase 6.1: retire the sat_fimp numeric proxy`.
- [x] **Guard**: `IExpandedConsistent_sat` (`:1249`) must remain **unchanged** — `exact hsat` still
      closes `sat_fimp` because the definitional identity between the field and `sfSatisfied`'s clause
      is preserved by dropping the same conjunct from both. If it goes red, one of the two edits is
      asymmetric — fix that, do not weaken the lemma.

**Tasks (6.2 — thread the invariant-side edge list):**

- [x] **Step 4.** Add `augSets : List IEdges` to `intExpandBranches_openBranch_sat`'s signature
      (`:2930`) and to `generalizing`; retype `hACC` to use `augSets`:
      ```lean
      private lemma intExpandBranches_openBranch_sat (fuel : Nat)
          (branches : List (IBranch Atom))
          (expandedSets : List (List (ISF Atom)))
          (nextWorlds : List Nat)
          (edgeSets : List IEdges)
          (augSets : List IEdges)          -- invariant-side edge lists
          (closurePred : IBranch Atom → Bool)
          (b : IBranch Atom)
          (hAC : IAllConsistent branches expandedSets nextWorlds)
          (hLen0 : branches.length = edgeSets.length)
          (hACC : IAllAccessConsistent branches expandedSets augSets)
          (h : intExpandBranches branches expandedSets nextWorlds edgeSets fuel closurePred
              = .openBranch b) :
          ∃ edges : IEdges, IBranchSaturation Atom b ∧ IFimpAccess edges b := by
        induction fuel generalizing branches expandedSets nextWorlds edgeSets augSets hAC hLen0 hACC with
      ```
      **No length hypothesis is needed for `augSets`**: `IAllAccessConsistent` is `False` on
      mismatched-length lists, so the shape is forced. *(red)*
- [x] **Step 5.** Add `pendingAug`/`doneAug` to the inner `suffices key` (`:2973`), its two
      `IAllAccessConsistent` hypotheses, the `key …` application, and the `nil` branch's `intro`
      arity (13 → 15 underscores):
      ```lean
          suffices key : ∀ (pending : List (IBranch Atom))
              (pendingExp : List (List (ISF Atom)))
              (pendingNW : List Nat)
              (pendingEdges : List IEdges)
              (pendingAug : List IEdges)
              (done : List (IBranch Atom))
              (doneExp : List (List (ISF Atom)))
              (doneNW : List Nat)
              (doneEdges : List IEdges)
              (doneAug : List IEdges),
              IAllConsistent pending pendingExp pendingNW →
              pending.length = pendingEdges.length →
              IAllConsistent done doneExp doneNW →
              done.length = doneEdges.length →
              IAllAccessConsistent pending pendingExp pendingAug →
              IAllAccessConsistent done doneExp doneAug →
              intExpandBranches.go closurePred fuel' pending pendingExp pendingNW pendingEdges
                  done doneExp doneNW doneEdges = .openBranch b →
              ∃ edges : IEdges, IBranchSaturation Atom b ∧ IFimpAccess edges b from
            key branches expandedSets nextWorlds edgeSets augSets [] [] [] [] []
              hAC hLen0 (by trivial) rfl hACC (by trivial) h
      ```
      **`intExpandBranches.go`'s argument list is UNCHANGED** — the algorithm still threads its own
      `pendingEdges`/`doneEdges`. This decoupling is the mechanism (D7). *(red)*
- [x] **Step 6.** Add the `cases hpAug : pendingAug` split nested inside the `pendingEdges` cons case;
      retarget `hACC_bPers` to `augH`:
      ```lean
                | cons edgesH edgesT =>
                 cases hpAug : pendingAug with
                 | nil =>
                   simp only [hpE, hpAug, IAllAccessConsistent] at hPendingACC
                 | cons augH augT =>
                  ...
                  simp only [hpE, hpAug, IAllAccessConsistent] at hPendingACC
                  ...
                  have hACC_bPers : IExpandedAccessConsistent augH bPers eH :=
                    IExpandedAccessConsistent_mono
                      (fun x hx => applyPersistenceFixpoint_mem_preserved bh edgesH (fuel' + 1) x hx)
                      hACC_bh_eH
      ```
      Thread `augT` / `doneAug ++ [augH]` through the `closurePred` recursion. *(red)*
- [x] **Step 7.** `none` leaf (`:3049-3050`): `⟨edgesH, …⟩` → `⟨augH, …⟩`:
      ```lean
                      exact ⟨augH, IExpandedConsistent_sat hstep hIC_bPers,
                        IExpandedAccessConsistent_sat hstep hACC_bPers⟩
      ```
      **Both extraction lemmas are used unchanged** — only the edge list they are instantiated at
      differs. This is the "one-line substitution" v01's Phase 6 anticipated; it just needed the right
      list, not a Q-predicate.
      `linearResult`/`branchingResult` arms: swap `edgesH`→`augH`, `edgesT`→`augT`,
      `doneEdges`→`doneAug` **in `hACC'` only** (leave `hLen0'` and `hgo` on the algorithm's lists —
      `doneEdges ++ [newEdge.elim edgesH (fun e => edgesH ++ [e])] ++ edgesT` becomes
      `doneAug ++ [newEdge.elim augH (fun e => augH ++ [e])] ++ augT` on the `hACC'` side, and
      `branches'.map (fun _ => edgesH)` becomes `branches'.map (fun _ => augH)`); add one `_` to each
      `exact ih …`. *(red)*
- [x] **Step 8.** Update `openBranch_countermodel`'s call site (`:3367-3370`) with the explicit `[[]]`
      — `augSets` is otherwise unconstrained by unification:
      ```lean
        obtain ⟨edges, hsat, hfimp⟩ :=
          intExpandBranches_openBranch_sat _ _ _ _ _ [[]] _ _
            (by simp [IAllConsistent, IExpandedConsistent, ILabelBound]) rfl
            (by simp [IAllAccessConsistent, IExpandedAccessConsistent]) h
      ```
      **Verify**: `lake build …Scheme` **green, with the reuse-site `sorry` still present** (7
      sorries). Commit `task 574 phase 6.2: thread the invariant-side edge list`.
- [x] **Boundary guard**: the fuel-0 `sorry` region and its 26-line refutation note (`:2940-2970`)
      must be **byte-identical** after 6.2 — confirm with `git diff` showing no change in that range.
- [x] **Boundary guard**: `intExpandBranches_openBranch_initial_mem` (`:3199-3345`) and its own
      `suffices key` (`:3227`) are a **different lemma** and must be untouched — confirm with
      `git diff`.

**Tasks (6.3 — close the reuse-site discharge):**

- [x] **Step 9.** Replace the reuse-site `sorry` (`:3131-3143`) with the loop-back-edge discharge,
      and retype `hACC_reuse`/`hACC''` to `augH ++ [(x, l)]`:
      ```lean
                                 have hreuse_sat : IExpandedConsistent bPers newExp ∧
                                     IExpandedAccessConsistent (augH ++ [(x, l)]) bPers newExp := by
                                   subst hnewExp
                                   constructor
                                   · intro sf' hsf'
                                     rcases List.mem_append.mp hsf' with h' | h'
                                     · exact hIC_bPers sf' h'
                                     · rw [List.mem_singleton] at h'
                                       subst h'
                                       show sfSatisfied bPers ⟨.neg, .imp φ ψ₀, l⟩
                                       simp only [sfSatisfied]
                                       exact ⟨x, houtPhi, hFpsi⟩
                                   · intro sf' hsf'
                                     rcases List.mem_append.mp hsf' with h' | h'
                                     · exact sfAccessSat_edges_mono (x, l) (hACC_bPers sf' h')
                                     · rw [List.mem_singleton] at h'
                                       subst h'
                                       show sfAccessSat (augH ++ [(x, l)]) bPers
                                         ⟨.neg, .imp φ ψ₀, l⟩
                                       simp only [sfAccessSat]
                                       exact ⟨x, isAccessible_one_step (by simp), houtPhi, hFpsi⟩
      ```
      followed by
      ```lean
                                 have hACC'' : IAllAccessConsistent (done ++ [bPers] ++ bt)
                                     (doneExp ++ [newExp] ++ eT)
                                     (doneAug ++ [augH ++ [(x, l)]] ++ augT) := ...
                                 exact ih _ _ _ _ _ hAC'' hLen0'' hACC'' hgo)
      ```
      `hLen0''` is **unchanged** — it still speaks about `doneEdges`/`edgesT`, matching `hgo`.
- [x] **Orientation guard**: the edge is `(x, l)`, **not** `(l, x)`. `isAccessible` walks
      `(child, parent)` pairs parent→child, and
      `isAccessible_one_step (hmem : (w', w) ∈ edges) : isAccessible edges w w'` (`:349`), so
      `(x, l) ∈ aug` yields `isAccessible aug l x` in one hop — exactly `sfAccessSat`'s conjunct with
      `w' := x`. A wrong orientation fails `isAccessible_one_step (by simp)`.
- [x] **Non-vacuity check (replicate the research's falsification test)**: swapping the two witness
      arguments (`houtPhi` ↔ `hFpsi`) must produce an application type mismatch. If it builds either
      way, the term is not doing what it appears to — stop and record.
- [x] Remove the `-- TEMPORARY (task phase 4 -> phase 6)` annotation along with the `sorry`.
- [x] **Step 11 gates**:
      - `lake build` (full) **green**.
      - `grep -rn "^\s*sorry\s*$" Cslib/ --include=*.lean | wc -l` = **6**, and the six lines are the
        exact baseline declarations (`TemporalConservativity`, `FrameSoundness`, `Scheme` truthLemma
        T-imp, `Scheme` fuel-0, `Intuitionistic/Completeness`, `Minimal/Completeness`).
      - `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` →
        `{propext, Classical.choice, Quot.sound}` (use `scan_source: false` and cross-check with a
        manual `#print axioms` — see Phase 4's tooling note).
      - `grep -c "^\s*sorry\s*$" …/Soundness.lean` = 0; `grep -c "IBranchSaturation" …/Soundness.lean`
        = 0.
      - `git diff --stat` names **only** `Scheme.lean`.
      Commit `task 574 phase 6.3: close the reuse-site discharge`.
- [x] **Convergence check**: `diff` the fix's line ranges against `scratch/Scheme.lean.prototype`.
      Any deviation must be justified in the phase record.

- **Timing:** 10-14 hours
- **Depends on:** 4
- **Verification Tier:** full — the phase closes the last in-flight `sorry`, changes a `structure`
  field's type, and re-runs the acceptance gate. Enumerated dependents of the `sat_fimp` change:
  `Scheme.lean`, `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean` (the latter two
  hypothesis-only, and weakened).
- **Commit Mode:** per-substep at the sub-phase level (three commits: 6.1, 6.2, 6.3), with 6.1's
  steps 1-3 and 6.2's steps 4-8 each declared **atomic-batch** internally — intermediate per-step
  states are expected red and must not be committed.
- **Scope Hypothesis:** ~94 changed lines in **exactly one file** (`Scheme.lean`), zero new
  declarations, zero deletions of existing declarations. Sub-hypotheses to confirm at implementation
  time: (i) `IExpandedConsistent_sat` and `IExpandedAccessConsistent_sat` are applied **unmodified**
  (only their edge-list instantiation differs); (ii) `intStepBranch_linear_preserves` needs only the
  one `refine` arity change, because `edges` there is an implicit variable used solely via
  `sfAccessSat_edges_mono` and `isAccessible_one_step`; (iii) neither `Completeness.lean` file needs
  an edit. All three held in the prototype. **A second file turning red is a hypothesis miss to
  record, not to absorb** — and specifically, if `Soundness.lean` turns red, stop: that would
  contradict the verified `grep -c IBranchSaturation` = 0 invariant.
- **Done when:** the repo-wide bare-sorry count is exactly **6**, the acceptance-gate `lean_verify`
  is axiom-clean, `Soundness.lean` is untouched, and all three sub-phase commits exist.

---

### Phase 7: Retire the superseded quotient stack; docstring and reference reconciliation [COMPLETED]

- **Goal:** Delete the ~480 lines of dead Phase 5 machinery (Supersession Accounting above), rewrite
  the design notes it leaves behind, and confirm zero orphan references — replacing v01's Phase 7,
  whose entire content (migrating `truthLemma` and the four downstream consumers to the
  Q-predicates) is a **no-op** under the loop-back-edge design.

**Why v01's Phase 7 collapsed**: `truthLemma`'s F-imp case is already green over `IFimpAccess` and
**stays that way** — nothing migrates. `openBranch_countermodel`, `tableau_complete`, and both
`Completeness.lean` signatures keep `intAccessPreorder` / `IFimpAccess` / `IBranchSaturation`
unchanged; `tableau_complete`'s `hvalid` already quantifies over all `IEdges`, so an augmented list
was always in its scope. The only surviving content is deletion plus docstring reconciliation.

**Tasks (7.1 — deletion):**

- [x] Re-run the Supersession Accounting grep sweep to confirm the reference counts are still
      outside-`Scheme.lean`-zero **at deletion time** (Phase 6 changed the file; re-verify, do not
      inherit):
      ```bash
      for d in negImpAt intBlockRepStep intBlockRep intAccessPreorderQ sfSatisfiedQ sfAccessSatQ \
               IExpandedConsistentQ IExpandedAccessConsistentQ IBranchSaturationQ IFimpAccessQ \
               IExpandedConsistentQ_sat IExpandedAccessConsistentQ_sat; do
        grep -rn "\b$d\b" Cslib/ CslibTests/ --include=*.lean | grep -v "Intuitionistic/Scheme.lean"
      done
      ```
      Expected: empty. **A non-empty result is a stop-and-record event**, not a licence to leave the
      declaration in place silently.
- [x] Delete, with their section headers and docstrings:
      - `negImpAt`, `intBlockRepStep`, `intBlockRep`, `intBlockRep_idempotent`, `intBlockRep_le`, and
        the two unfolding equation lemmas (`Scheme.lean:526-643` region)
      - `intAccessPreorderQ`, `intAccessPreorderQ_le_of_isAccessible`,
        `intAccessPreorderQ_le_of_rep_eq` (`:654-678` region)
      - `sfSatisfiedQ`, `sfSatisfiedQ_mono`, `sfAccessSatQ`, `IExpandedConsistentQ`,
        `IExpandedConsistentQ_mono`, `IExpandedAccessConsistentQ` (`:1095-1174` region)
      - `IBranchSaturationQ` (`:1175`), `IFimpAccessQ` (`:1215`) — **public**, but grep-confirmed
        unreferenced
      - `IExpandedConsistentQ_sat` (`:1340`), `IExpandedAccessConsistentQ_sat` (`:1896`)
- [x] `lake build` (full) green after deletion. `lake exe checkInitImports` exit 0.
- [x] Commit `task 574 phase 7.1: retire the superseded quotient stack`.

**Tasks (7.2 — docstring and reference reconciliation):**

- [x] Rewrite the D5 design note (`Scheme.lean:~1009-1030`, landed Phase 5.3). It currently describes
      the quotient as the mechanism and points at the Q-predicates, which no longer exist. Replace it
      with the loop-back-edge rationale: the saturation lemma's `edges` is existentially quantified,
      so the invariant threads its own edge list and records each blocking event as `(x, l)` at block
      time; `Sfor`-containment plus ancestor persistence make `x` and `l` force the same positive
      formulas; `IForces` requires only a `Preorder`, so the cycle is admissible. Attribute the
      construction to `GargGenoveseNegri2012` (`M ∪ C` with `C = {x ≤ y | Sfor(x) ⊆ Sfor(y)}`) with an
      explicit note that the source is **not readable in-repo** and the design rests on the verified
      construction here. **No task-number references** (durable anchors only: declaration names,
      BibKeys, section headings).
- [x] Confirm the `intFImpReuseWitnessAnc?` docstring (`Expansion.lean`, Phase 3) is still accurate
      after Phases 6-7 — in particular its reuse contract paragraph. Amend only if a statement is now
      false; do not rewrite for style. **Reuse contract paragraph (`:250-255`) was accurate,
      unchanged. Found and fixed a separate false statement: the trailing "additive" paragraph
      (`:257-259`) still described the pre-Phase-4 state ("call site still calls
      `intFImpReuseWitness?`, unchanged, in this phase") and named a declaration deleted in Phase 4.
      Replaced with the current state (single call site to `intFImpReuseWitnessAnc?`;
      `intFImpReuseWitness?`/`_spec` deleted in Phase 4).**
- [x] Sweep for orphan references to the deleted names in prose and comments across
      `Cslib/Logics/Propositional/Tableau/`: `grep -rn "Q\b\|intBlockRep\|quotient\|filtration"` and
      fix any dangling mention. A stale docstring pointing at a deleted declaration is the exact
      failure mode this task's postmortem constraints exist to prevent. **Zero orphan references
      found** (also swept `CslibTests/`, one unrelated false-positive match on `EFQ`).
- [x] Record Defect 1 and Defect 2 as **resolved-by-deletion** / **corrected-in-plan** respectively in
      the phase record. Neither produces a `Cslib/` change beyond the deletion. **Defect 1**
      (`intBlockRepStep`'s false "agrees by construction" docstring claim) is resolved by deletion —
      the declaration and its docstring no longer exist in the tree. **Defect 2** (v01's H3
      availability table errors on `NegriVonPlato2001` and Massacci 2000) was already corrected in
      this plan's H3 table (see Source-to-Implementation Mapping above); no further action needed —
      D9 holds, no new `references.bib` entries were added.
- [x] `lake build` (full) green; `lake lint` green; repo-wide bare-sorry count still exactly **6**.
- [x] Commit `task 574 phase 7.2: reconcile design notes after quotient retirement`.

- **Timing:** 4-6 hours
- **Depends on:** 6
- **Verification Tier:** interface — two **public** declarations (`IBranchSaturationQ`,
  `IFimpAccessQ`) are removed. Enumerated dependents checked: `Scheme.lean` only (grep-verified zero
  outside). Tie-break-upward from `local` because public-symbol removal is externally visible even
  when unreferenced in-tree.
- **Commit Mode:** per-substep — 7.1 and 7.2 are two green commits.
- **Scope Hypothesis:** ~480 lines **deleted** from exactly one file (`Scheme.lean`), plus ~40 lines
  of docstring rewrite; **zero** lines added elsewhere and **zero** other files touched. Confirm with
  `git diff --stat` naming only `Scheme.lean` with deletions dominating. If deletion turns any
  declaration red, the grep sweep was wrong — record it and re-scope before continuing.
  **Outcome (recorded, not silently absorbed):** 7.1 deleted exactly 434 lines from `Scheme.lean`
  only (close to the ~480 estimate; the estimate over-counted slightly, no under-count risk
  materialized — deletion turned nothing red). 7.2's docstring rewrite touched `Scheme.lean` (24
  insertions / 20 deletions) as hypothesized, **plus** a second file,
  `Expansion.lean` (6 lines) — a **minor, explicitly-authorized hypothesis miss**: task 7.2's own
  checklist item directs confirming and, if false, amending the `intFImpReuseWitnessAnc?`
  docstring in `Expansion.lean`, and the orphan-reference sweep surfaced exactly one stale
  paragraph there (describing the pre-Phase-4 "call site still calls the old function" state,
  naming a declaration deleted in Phase 4) — fixed per that same checklist item.
- **Done when:** all twelve superseded declarations are gone, no orphan reference remains, full
  `lake build` and `lake lint` are green, and the sorry count is exactly 6. **All satisfied.**

---

### Phase 8: Conformance regeneration and full CI gate [NOT STARTED]

- **Goal:** Regenerate `CslibTests/TableauConformance.lean` from real `#eval` output and pass the
  complete CSLib CI pipeline.
- **Tasks:**
  - [ ] Re-run all 19 propositional rows via `#guard_msgs in #eval` and record the **actual**
        verdicts. Compare each against the file's stated semantic expectation (14 CLOSED / 5 OPEN).
        *Prior evidence*: Phase 1 measured all 19 under V1/V2/V3 and **all matched**; Phases 6-7 are
        proof-side only and cannot move a verdict. A mismatch here therefore indicates something
        unexpected happened — treat it as a finding, not noise.
  - [ ] **Divergence handling (binding).** Any row whose actual verdict contradicts the formula's IPC
        validity is a **defect in this repair**, not a value to transcribe. Mark this phase
        `[BLOCKED]`, record the offending row(s) and Phase 1's prediction for them, and escalate. Do
        **not** flip the expected string to match.
  - [ ] Add **one new row** asserting the divergence witness `φ0` now terminates: a
        `#guard_msgs in #eval intVerdict (intuitionisticTableau φ0)` entry with the semantically
        correct verdict, plus a comment naming it as the regression guard for this repair (by
        describing the divergence, not by citing a task number). 19 → 20 propositional rows, 43 → 44
        total.
  - [ ] Rewrite the file's "Corpus provenance" docstring (`:59-69`): the "all 43 rows are green /
        pure regression guard" paragraph and the "43 rows (24 temporal, 19 propositional)" count both
        change.
  - [ ] Leave the 24 temporal rows (`:94-220`) and their docstrings **untouched** — a different
        calculus.
  - [ ] Run the CSLib CI pipeline in order (`.claude/rules/cslib.md`):
        `lake exe cache get` → `lake build` → `lake exe checkInitImports` → `lake lint` →
        `lake exe lint-style` → `lake test` →
        `lake shake --add-public --keep-implied --keep-prefix`.
        **`shake` is its own objective** — Phase 7 removed ~480 lines including two public
        declarations, so an import-minimisation shift is plausible (R3). Run with `--fix`, review the
        emitted diff, and commit it separately.
  - [ ] Delete the Phase 1 scratch vehicles (`scratch/DivergenceProbe.lean` and the four companion
        probe files) after confirming their findings are recorded in
        `handoffs/01_variant-selection.md`. **Retain** `scratch/phase6-prototype.patch`,
        `scratch/Scheme.lean.prototype`, and `scratch/Scheme.lean.baseline` until the task is
        archived — they are the evidence base for Phase 6.
  - [ ] Write `specs/574_tableau_calculus_repair_ancestor_blocking/summaries/01_tableau-repair-summary.md`,
        including the supersession accounting (Phase 5's ~480 lines landed then deleted) stated
        honestly rather than elided.
  - [ ] **Final gates**: repo-wide bare-sorry count = 6 and identical to the baseline table;
        `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` axiom profile =
        `{propext, Classical.choice, Quot.sound}`; `git diff --stat` touches no file outside
        `Cslib/Logics/Propositional/Tableau/`, `CslibTests/TableauConformance.lean`, and `specs/`.
- **Timing:** 5-8 hours
- **Depends on:** 2, 7
- **Verification Tier:** full — the complete repository gate set
- **Commit Mode:** per-substep
- **Scope Hypothesis:** ~120 lines of delta in `CslibTests/TableauConformance.lean` (19 verdicts
  re-checked, 1 row added, 1 docstring paragraph rewritten), plus whatever `lake shake --fix` emits.
  The hypothesis is that **zero** propositional expected-value strings need to change. Any flipped
  verdict string triggers the divergence-handling branch above.
- **Done when:** every CI step exits 0, the sorry baseline is restored, and the conformance file
  documents the regenerated corpus.

## Testing & Validation

- [x] Phase 1 baseline row reproduces the recorded fuel→max-label table (6/7 points exact; the fuel=60
      discrepancy assessed and recorded).
- [x] Selected variant's max label **saturates** by `fuel = 260` on the divergence witness (V1: 21).
- [x] All 19 propositional conformance formulas match their semantic expectations under the selected
      variant (Phase 1 pre-run).
- [ ] `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` →
      `{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[]}` (**acceptance gate**;
      re-run at every remaining phase boundary, with `scan_source: false` plus a manual
      `#print axioms` cross-check).
- [ ] `lean_verify Cslib.Logic.PL.minimalTableau_sound` and
      `Cslib.Logic.PL.intuitionisticTableau_sound` sorry-free.
- [ ] `grep -c "^\s*sorry\s*$" Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` = 0
      at **every** phase boundary.
- [ ] `grep -c "IBranchSaturation" Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
      = 0.
- [ ] `grep -rn "^\s*sorry\s*$" Cslib/ --include=*.lean | wc -l` = **6** from the end of Phase 6.3
      onward, matching the baseline table declaration-for-declaration.
- [ ] The reuse-site discharge is **non-vacuous**: swapping `houtPhi` ↔ `hFpsi` produces an
      application type mismatch.
- [ ] The fuel-0 `sorry` and its 26-line refutation note are byte-identical across Phases 6-8.
- [ ] `intExpandBranches_openBranch_initial_mem` (and its own `suffices key`) untouched.
- [ ] Zero orphan references to the deleted quotient stack after Phase 7.
- [ ] `lake build` green.
- [ ] `lake exe checkInitImports` green.
- [ ] `lake lint` green.
- [ ] `lake exe lint-style` green.
- [ ] `lake test` green (includes `CslibTests/TableauConformance.lean`).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` green.
- [ ] All 24 temporal conformance rows unchanged and green.
- [ ] No new `axiom` declarations: `git diff | grep "^+axiom"` empty.
- [ ] No `def X := True` / `theorem X := trivial` vacuous placeholders introduced.
- [ ] No task-number references in any `Cslib/` or `CslibTests/` file introduced by this task.

## Artifacts & Outputs

- `specs/574_tableau_calculus_repair_ancestor_blocking/plans/02_tableau-repair-loopback-edges.md`
  (this file)
- `specs/574_tableau_calculus_repair_ancestor_blocking/plans/01_tableau-repair-ancestor-blocking.md`
  (superseded; retained unedited as the record of the quotient approach)
- `specs/574_tableau_calculus_repair_ancestor_blocking/reports/01_phase6-blocker-resolution.md`
  (blocker research; the fix path's ground truth)
- `specs/574_tableau_calculus_repair_ancestor_blocking/handoffs/01_variant-selection.md` (Phase 1)
- `specs/574_tableau_calculus_repair_ancestor_blocking/scratch/phase6-prototype.patch`,
  `scratch/Scheme.lean.prototype`, `scratch/Scheme.lean.baseline` (Phase 6 evidence; retained until
  archival)
- `specs/574_tableau_calculus_repair_ancestor_blocking/scratch/DivergenceProbe.lean` + four probe
  companions (Phase 1; deleted in Phase 8)
- `specs/574_tableau_calculus_repair_ancestor_blocking/summaries/01_tableau-repair-summary.md`
  (Phase 8)
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/{Expansion,Scheme,Soundness}.lean`
- Modified: `CslibTests/TableauConformance.lean`
- **Unmodified by Phases 6-8** (a change to any of these is a scope miss to record):
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/{Rules,Completeness}.lean`,
  `Cslib/Logics/Propositional/Tableau/Minimal/{Soundness,Completeness}.lean`

## Rollback/Contingency

- Every phase commits per the Commit-Per-Green-Substep Mandate (`task 574 phase {P}.{O}: …`), so any
  phase can be reverted by `git revert` of its commit range without touching sibling phases.
- **Phase 6.1 is the natural rollback boundary for this revision.** Before it, the tree is at the
  Phase 5 end state (green, 7 sorries) with the full quotient stack still present. Reverting 6.1-7.2
  restores that state exactly.
- **If Phase 6.1 or 6.2 cannot be made green**, the prototype patch is available as a whole-file
  reference: restore `scratch/Scheme.lean.prototype` into `Cslib/` to establish that the end state is
  reachable, then re-derive the sub-step decomposition from the difference. Record this as a
  deviation; do **not** land the whole-file copy as a single commit without the sub-step record.
- **If the Phase 6.3 discharge cannot be closed** despite the prototype, that contradicts blocker
  claims C1/C3 and is a substantive finding: mark Phase 6 `[BLOCKED]`, capture the failing goal state,
  and escalate for a further `/revise`. **Do not complete the task with the temporary sorry in
  place** — `Scheme.lean` carrying a third sorry is a silent regression of the baseline.
- **If the Phase 7 deletion turns anything red**, revert 7.1, leave the quotient stack in place as
  documented dead machinery with an explicit "superseded, retained because X depends on it" docstring
  naming the dependency, and record the retention decision. Deletion is preferred but not
  load-bearing for the acceptance gate.
- If Phase 8's conformance run flips a verdict, that is a **defect in the repair**, not a value to
  transcribe — `[BLOCKED]` and escalate.
- Never use `git reset --hard` / `git checkout --` / `git clean -fd` to reach a green build; snapshot
  first with `bash .claude/scripts/git-snapshot.sh 574` if a rollback is genuinely required.
