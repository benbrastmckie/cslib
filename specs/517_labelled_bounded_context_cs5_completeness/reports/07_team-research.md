# Research Report: Team Research — Route to `cs5_completeness`

- **Task**: 517 - Labelled bounded context CS5 completeness
- **Started**: 2026-07-15T00:00:00Z
- **Completed**: 2026-07-15T00:00:00Z
- **Effort**: 4 teammate dispatches (A/B/C/D, wave-based) + 1 synthesis dispatch
- **Dependencies**: 509 (landed, closed), 512 (open; cyclic — see Project Context), 516 (abandoned)
- **Sources/Inputs**:
  - *Teammate findings*: `reports/07_teammate-a-findings.md` (Primary: Simpson Ch.7-8),
    `reports/07_teammate-b-findings.md` (Alternatives/prior art),
    `reports/07_teammate-c-findings.md` (Critic), `reports/07_teammate-d-findings.md` (Horizons)
  - *Prior artifacts*: `reports/02_*` (Executive Summary only), `plans/01_labelled-framework.md`,
    `plans/02_decomposed-track-a-b-c.md` (active)
  - *Literature*: `Simpson1994` (`simpson_1994_intuitionisticmodallogic`, 1091 chunks) —
    chunks 0068, 0075, 0098, 0101, 0102, 0103, 0111, 0114-0117, 0121, 0132, 0149, 0152, 0153,
    0158, 0163, 0166, 0167, 0172, 0174, 0175; `Pacheco2024` chunks 0008-0013;
    `MarinMoralesStrassburger2021` chunks 0009, 0018, 0043, 0044, 0046, 0050
  - *Codebase (verified this dispatch)*: `Cslib/.../CS5.lean:152-159,703-718`,
    `CS5Canonical.lean:487-488,511,643,661`, `CKExtension.lean:159,184`,
    `Labelled/Context.lean:138,247`, `Labelled/Deduction.lean:122-127`,
    `probes/fischer-servi-probe.lean:132-144`, `plans/02_decomposed-track-a-b-c.md:173`
- **Artifacts**: `specs/517_labelled_bounded_context_cs5_completeness/reports/07_team-research.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Project Context

- **Upstream Dependencies**: 509 (landed guardrail lemmas: `cs5_symmetric_tail_box_gap`,
  `cs5Incest_forces_symm`, `cs5TwoSidedR_iff_cs5Tail`); 512 (landed `cs5_axiom_sound_incest`,
  `cs5_soundness_incest` — supplies the soundness half); 516 (abandoned; independent-`≤` refuted)
- **Downstream Dependents**: 512 (declares `depends_on [509, 517]` — a literal cycle with 517's
  `depends_on [509, 512, 516]`; verified this dispatch; no topological order exists)
- **Alternative Paths**: Track B (Pacheco Lemma 18 joint Zorn) — reopened as a probe, not the route;
  Thm 3.3.4 Ch.3 shortcut — abandoned (delegates to `FischerServi1984`, not in corpus)
- **Potential Extensions**: `NIK(𝒯)`-completeness is `𝒯`-generic over `{T, B, 4, 5}` — one proof
  serves the 16-logic intuitionistic modal cube, not CS5 alone

## Executive Summary

- **All four teammates independently converged, from four disjoint angles, on Simpson Lemma 5.3.1
  (Prime Lemma, Ch.5) + Lemma 5.3.2 (canonical model / truth lemma) as the missing piece** — matching
  what `CS5.lean:705-706` already names as "the simultaneous maximal pair … the real open problem"
  (verified verbatim). The active plan contains **none** of it:
  `grep -cE "8\.2\.5|8\.2\.6|Prime Lemma|5\.3\.1|truth lemma" plans/02_decomposed-track-a-b-c.md`
  returns **0** (reproduced this dispatch). Plan 02 silently dropped plan 01's Phases 5-9 and
  replaced them with a single "assembly" line. Even if C5-C8 all succeed, `cs5_completeness` is at
  **zero, unplanned and unestimated**.
- **The task title is a misnomer.** Simpson's Ch.7-8 bounded contexts do not cover IS5
  (`T_S5 ∉ Dec_ND`, `chunk_0132.md:13`); boundedness is a decidability/FMP device that 517 needs
  neither of. The mathematically correct route is **Ch.5 (prime lemma + canonical model lemma) +
  Ch.6 (adequacy, incl. C5) + §8.1.1 (`B_K` birelational bridge)** — Simpson's own named route
  ("It will follow from the results of Chapters 5 and 6", `chunk_0075:3`).
- **The named blocking obligation is `CS5 ⊢ FS`, not `FischerServi1984`.** `cs5_completeness`
  *entails* `CS5 ⊢ FS` (instantiate the target at `φ := FS`, discharge via the landed `fs_sound''`);
  plan 02:173's "orthogonal … red herring" is **wrong — it is entailed** (verified verbatim).
  Honest probability the target is **false: ~25%**. A ~2-line mechanization settles the dependency
  and cannot fail.
- **Track B's NO-GO is overturned** — A3's rationale rests on a transcription error
  (`Γ□` → `Γ`, `CS5.lean:583`) and, applied consistently, would close **Ch.5 as well**, i.e. the
  recommended route. The `[BLOCKED]` markers on Phases 4-6 must be revised. This reopens Track B as
  a *probe*, not as the route.
- **Report 02's headline ("Ch.6 adequacy bridge NOT on the critical path, ~85%") is superseded and
  inverted** — refuted by Simpson's own prose (`chunk_0075`, `chunk_0121`), outside the OCR defect
  zone. Ch.6 stays, **reordered behind** the Ch.5 model construction.
- **Honest headline: ~10%** that `cs5_completeness` lands via the recommended route over ~8-12
  dispatches. But **leg A alone (`NIK(𝒯)`-completeness) is ~50% and does not depend on the target
  being true** — that is the honest value proposition. **Do not dispatch C5 next.**

## Context & Scope

**User directive (verbatim, governing)**: *"I am looking for the mathematically correct way to
proceed, cutting no corners."* Applied here, this constrains **method**, not target selection: no
`sorry`, no new axiom under `Cslib/`, no unproved equivalence on the critical path, no weakening of
the target, and no overclaiming. It also *compels* fixing corners already cut (see Defects).

**What is being evaluated**: whether any route reaches
`cs5_completeness : CKValidFC cs5FC'' φ → Derivable CS5ModalAxiom φ`, and what the next dispatch
should be. Four teammates covered: Simpson Ch.7-8 (A), alternatives/prior art (B), adversarial audit
(C), strategic horizons (D).

**Synthesis method**: teammate claims were treated as the object of audit, not as evidence. Six
load-bearing citations were re-verified at source this dispatch, and one conflict **not named in the
dispatch** (C's A5 vs D's F4) was discovered and adjudicated against the Simpson source text.

**Constraint acknowledged**: this report does not edit `Cslib/`, does not modify teammate findings,
and creates no tasks.

## Findings

### The convergence (verified, and it is the report's headline)

Four angles, four independent arrivals at the same object:

| Teammate | Route in | Arrives at |
|---|---|---|
| A (Ch.7-8) | §8.2.1 self-describes as re-proving §5.3; `T_S5 ∉ Dec_ND` kills the bounded route | Ch.5 unbounded prime lemma + canonical model lemma |
| B (prior art) | Pacheco Lemma 18 is a joint Zorn over *pairs*; Simpson 5.3.1 is the same idea *one level more general* (Zorn over graph + labelled formulae) | Simpson Lemma 5.3.1 |
| C (critic) | "Simpson's Lemma 5.3.1 is the solution to CSLib's stated open problem" | Simpson 5.3.1 + 5.3.2 |
| D (horizons) | Plan 02 dropped plan 01's Phases 5-6, which *are* 5.3.1 + 5.3.2 | Simpson 5.3.1 + 5.3.2 |

This is the strongest signal in the dispatch. It is corroborated by CSLib's own docstring
(`CS5.lean:705-706`, verified verbatim): *"`H'` and `T` must be built as a simultaneous maximal
pair, not sequentially"* — and Simpson 5.3.1 **is** a simultaneous maximal pair: one Zorn
application over whole contexts `(G, Γ)`, graph and formula-set growing together, capped only by an
excluded labelled formula `x:A`, with a coinfinite reserve of fresh world-variables
(`chunk_0102`, read in full this dispatch).

**The mechanism of escape, stated precisely** (A's KF2, the deepest single finding): the gap lemma
`cs5_symmetric_tail_box_gap` is **TRUE of Simpson's construction but INERT**. Its hypothesis
`hq : q ∉ H` is at a *fixed* head; the IL-model box clause quantifies over the `≤`-future
(`chunk_0098`), so the refuting witness lives at a strictly larger context where `q ∉ H` is not
preserved and the lemma does not fire. In `CS5Canonical`'s design `H` is fixed, so this freedom does
not exist. **That freedom is the whole escape.** A hand-verified the consistency (KF2 Step 4) and
found no contradiction.

### Conflict 1 — `FischerServi1984`: A says blocking, B says not needed. RESOLVED in B's favour, via A's reasoning.

The two claims are **about different objects**, exactly as hypothesized:

- **A's claim** concerns Thm 3.3.4's authority for the **Ch.3 canonical-model shortcut**. Verified:
  Thm 3.3.4's *entire* proof is one sentence plus "The cases IK, IT, IKTB, IS4 and **IS5** … appear
  explicitly in Fischer Servi [24]" (`chunk_0068:29,41`). A is right that **no report is entitled to
  claim a Ch.6-free path on Simpson's authority**.
- **B's claim** concerns **Pacheco's attribution** of IKB's (2)⟺(4) to Simpson1994.

**Adjudication**: B's evidence is weaker than it looks — Pacheco citing "Simpson [Sim94]" does not
establish *where* in Simpson, and if it points at Thm 3.3.4 it loops back to A's empty terminus.
**But the conclusion survives on a stronger ground than B gave**: Simpson1994 **is** in the corpus
and **does** contain a real proof — Ch.5 + Ch.6 (`chunk_0075:3`). Under the recommended route the
Ch.3 shortcut is **abandoned**, so FS1984's role as its authority becomes **moot**.

**Verdict: deprioritize ingestion. Not blocking.** Downgraded from A's "single highest-value unblock"
to *optional, low priority*. A's ~50% ("FS1984 changes the routing decision") applies to a decision
we are no longer taking; it is now a **shortcut-finder, not a blocker**. Additional deflation: FS1984
is a 1984 axiomatization paper for IK (Fischer-Servi diamond), not CK/CS5; even a genuine IS5
birelational completeness proof there would be for a **different frame class** than `cs5FC''` and
would not be mechanization-ready.

**Residual risk (stated, not hidden)**: if the Ch.5 leg proves intractable and the Ch.3 shortcut is
ever revisited, FS1984 becomes blocking again and no report may claim that route without it. Also
declined: `PlotkinStirling1986` (B's F8) — the actual source of MMS Thm 2.5/7.1, but IK not CS5.

### Conflict 2 — Is the target FALSE? C's A1 vs B's Pacheco chain. RESOLVED: B's chain does NOT discharge C's risk.

**C's argument (verified, ~95% sound)**: `fs_sound''` (`probes/fischer-servi-probe.lean:132-144`,
sorry-free) proves `cs5FC'' ⊨ FS`. Instantiate the target at `φ := FS`; the hypothesis discharges;
therefore **`cs5_completeness ⟹ CS5 ⊢ FS`**. Contrapositive: `CS5 ⊬ FS ⟹ the target is false`. Plan
02:173's "orthogonal … red herring" is **verified verbatim** and is **wrong**: the question is
*entailed*, hence a **necessary condition**.

**B's chain**: Pacheco Cor. 12 (`CKB ⊨ FS`) + Thm 13 (`CKB ⊢ φ ⟺ CKB ⊨ φ`) ⟹ `CKB ⊢ FS` ⟹
`CS5 ⊢ FS` (`CS5 ⊇ CKB`).

**Adjudication: the chain does not discharge the risk, and B's own findings are why.** Thm 13's
completeness direction rests on Lemma 18, which **defers to Lemma 16** ("As in the proof of Lemma
16…"), and B found Lemma 16's step `φ ∉ Θ ⟹ ¬φ ∈ Θ` **invalid**. B repaired the Σ-half by hand but
states explicitly that **∆-primality under the antitone `∆□ ⊆ Σ` cap does not close** — it is "the
genuine open crux". So B's chain is **holed at precisely the step this entire task keeps failing
on**. It is not independent evidence; it is the *same* crux wearing a citation.

**C's counter-objection considered and rejected**: C suspects the "Lemma 16 unsound" finding may
itself be a chunk-text artifact (C's B3), since the same extraction dropped the `□` from `∼c`. But
**B's second ground is property-based, not textual**: if the step were sound, Θ would be
negation-complete, hence classical, collapsing `⊑c` and proving CKB classical. That argument is
immune to OCR. **The Lemma 16 defect survives.**

**Evidence that survives independent of the holed chain**: `cs5_dia_or` (`CS5 ⊢ ◇(A∨B) → ◇A ∨ ◇B`,
`k3`) is **landed and mechanized** in CSLib; `ArisakaDasStrassburger2015` gives `B ⊢ k3, k5`;
`cs5FC'' ⊨ FS` is mechanized. These are real and they point toward `CS5 ⊢ FS`.

**Final probability the target is false: ~25%.** Reasoning: C's ~30% is very nearly right. I move it
down slightly — but *only* on the independent, mechanized corroboration (`cs5_dia_or`, ADS2015), not
on B's chain, which contributes ~nothing once its hole is priced in. This remains **the single
largest term in the task's failure probability**, and the plan calls it a red herring.

**Decisive act**: C's ~2-line mechanization is cheap, cannot fail, and makes the dependency
undeniable *whichever way it resolves*. Do it. Note also C's sharpest point: **every dispatch has
attacked `CS5 ⊢ FS` derivation and failed; nobody has attempted to refute it.** The untried direction
is where the information is.

### Conflict 3 — The probability estimates. RECONCILED (they were never in conflict).

Each number measures a different object. Reconciled, not averaged:

| Estimate | What it actually measures | Conditioned on target true? | Scope |
|---|---|---|---|
| A ~15-20% | Route 2 closes **in 3-4 dispatches** | **No** | Full route; optimistic dispatch count |
| B ~45% | Track C **C5-C8 + assembly only** | **No** | One leg (the Ch.6 bridge) |
| B ~65% | Simpson 5.3.1 **transcription** | No | One lemma |
| B ~35% | Probe B′ (∆-primality crux) | No | Alternative sub-route |
| B ~0% | MMS `labIK≤` / dGSC port | n/a | Correctly killed (F4/F6) |
| C ~7% | **Current plan as scoped** = 0.7 × ~0.10 | **Yes** | Track C only |
| **Synthesis ~10%** | **Recommended route, full target** | **Yes (×0.75)** | All legs, ~8-12 dispatches |

**The two estimates that measure the same thing — C's ~7% and this report's ~10% — agree.** That is
the reconciliation. A's 15-20% is higher because it omits the target-falsity term and undercounts
dispatches; B's 45% is a single leg unconditioned on the target.

**Headline computation** (recommended route = Ch.5 + Ch.6 + §8.1.1, reordered):

| Term | P | Basis |
|---|---|---|
| Target is true (`CS5 ⊢ FS`) | 0.75 | Conflict 2 |
| **Leg A** — Ch.5: 5.3.1 + 5.3.2 | ~0.50 | B's 65% for 5.3.1 alone; 5.3.2 is a **second** crux-grade obligation (A: "the real crux of Ch.5") |
| **Leg B** — Ch.6: 6.1.2 incl. C5 + 6.2.1-6.2.3 | ~0.35 | Adjudicated below |
| **Leg C** — §8.1.1 `B_K` + frame match | ~0.80 | A hand-checked all 5 conjuncts; "easy induction" per source |
| **Product** | **~0.105** | **~10%, over ~8-12 dispatches (not 3-4)** |

*Leg B adjudication (B ~45% vs C ~10%)*: C derives ~10% from an observed ~100% per-dispatch
transcription defect rate (0.7⁴ ≈ 24%, "and the observed rate is worse"). But C's own cited record —
*"Four dispatches, five corrections, each found by the next"* — describes a **functioning
error-correction process**: defects are being **caught**. Defects that are caught cost dispatches;
they do not multiply as failure probability. B's 45% ignores the defect rate entirely. **I follow
neither: ~0.35**, splitting on the evidence that the process self-corrects but at a real and
compounding cost in dispatch count.

**The honest value proposition is not the ~10%.** Leg A alone — `NIK(𝒯)`-completeness — is **~50%,
is `𝒯`-generic over the 16-logic modal cube, and does not depend on the target being true.** If the
target turns out false, leg A survives intact as a flagship theorem. That asymmetry should drive the
ordering (D's F2, endorsed).

### Conflict 4 — The A3 verdict (Track B closure). OVERTURNED, but Track B is not thereby the route.

All three of A, B, C independently reject `cs5_symmetric_tail_box_gap` as an impossibility result,
by three different arguments that agree:

- **A**: the lemma is **true** of Simpson's model but **inert** — `hq : q ∉ H` is not preserved under
  context extension; the box clause quantifies over the `≤`-future.
- **B**: it **proves too much** — `cs5FC''` conjunct 3 *is* plain symmetry (`CKExtension.lean:184`,
  verified), so Track C's countermodel *also* lands in `cs5Tail`-shape. A criterion that closes B on
  that basis closes C too. By reductio, it closes neither.
- **C**: found the transcription error. A3 wrote Pacheco's `∼c := Γ ⊆ ∆ ∧ ∆ ⊆ Γ♦`; `CS5.lean:583`
  has `Γ□ ⊆ ∆`. The `□` superscript is dropped by PDF extraction. **A3's version cannot be right**:
  `Γ ⊆ ∆ ⟹ ∆ ⊆ Γ` is false, so `∼c` could not be symmetric — contradicting Pacheco's own Lemma 15.

**CSLib's own file, which A3 cited, states the opposite verdict** (verified at `CS5.lean:158-159`,
verbatim): *"This is **not** a library-level '`CS5` completeness is blocked' verdict — it is a
narrow, well-understood, and non-vacuous open sub-problem."* **A3 read non-vacuity as
impossibility and inverted the verdict of the file it cited.**

**Verdict: Track B is REOPENED. The `[BLOCKED]` markers on plan 02 Phases 4-6 must be revised** —
to `[NOT STARTED]`, deprioritized, with the corrected rationale.

**But the reason to reopen is not that Track B is promising** (B's own estimate: ~35%, hinging
entirely on the unresolved ∆-primality crux). **The reason is that an unsound closure rationale is a
steering hazard that closes the recommended route too.** This is the synthesis-level point neither
teammate made explicitly:

> A's KF2 establishes that the gap lemma's hypotheses **are satisfied** in Simpson's construction —
> `Th(w,y)` and `Th(w,z)` are a symmetric tail pair. **Under A3's rationale, Ch.5 is also NO-GO.**
> B stated the reductio abstractly; A supplies the concrete instance. If A3's rationale is left
> standing, the recommended route is self-refuted before it starts.

That makes revising A3's rationale **mandatory**, independent of whether anyone ever runs Track B.

### Conflict 5 — Report 02's ~85% ("Ch.6 not on the critical path"). SUPERSEDED and inverted.

- **C refutes it** with Simpson's own prose, twice: *"It will follow from the results of **Chapters
  5 and 6** …"* (`chunk_0075`); *"**By Theorem 5.2.1**, for any 𝒯 to which **Theorem 6.2.1** applies,
  we have a complete axiomatization …"* (`chunk_0121`). Both are **prose, outside the OCR defect
  zone** the index warns about.
- **A independently downgrades to ~35%**, hedging only on FS1984.
- **D concedes** the bridge is required (revised its own draft against its own thesis).

**Adjudication: I follow C (~90%), not A (~35%).** A's residual 20-35% was reserved for FS1984
supplying a Ch.6-free path — and per Conflict 1 that route is abandoned, so the hedge dissolves. The
architecture is decisive: Thm 5.2.1 (Ch.5) lands you in the **labelled** system; the target's
conclusion is `Derivable CS5ModalAxiom φ`, the **axiomatic** side. **Ch.6 is the only thing that
crosses that gap.** A's KF4 independently kills the "S5 collapses the tree" hope: Lemma 6.2.3
delegates to Lemma 6.1.2 with "trivial modifications", and 6.1.2 begins *"If G is a finite tree"*
(`chunk_0111:3`); Simpson's set-indexed/total-visibility simplification (`chunk_0149`) applies to
the **Ch.7 sequent calculus**, not Ch.6. A reports this **against its own preferred shortcut**.

**Verdict: report 02's headline is marked SUPERSEDED. Ch.6/Track C stays — REORDERED behind the
Ch.5 model construction.** C1-C4 are landed sorry-free and lose nothing by waiting.

### Conflict 6 — The task title is a misnomer. CONFIRMED. Corrected framing below.

A's KF1, verified: §7.3 fixes `Dec_ND = {∅, {χ_D}, {χ_T}, {χ_B}, {χ_D,χ_B}, {χ_T,χ_B}}`
(`chunk_0132.md:13`) — **`T_S5` is absent**. IS5 enters Fig 7-5 only via *"the known result about
IS5 (see page 57)"*. §8.2.1 self-describes as re-proving §5.3 *"using a 'bounded' model"* to extract
FMP (`chunk_0163`). **Boundedness is a decidability/FMP device; 517 needs neither.**

**C's apparent counter-claim resolved, not dismissed.** C's A6 argues the target `cs5FC''` is
*birelational*, which is Ch.8's chapter, and that "nobody is working on Chapter 8". **Both C and A
are right, about different sections**: the birelational bridge is **§8.1.1** (`B_K`, unbounded) —
which **is** on A's Route 2 — while the bounded FMP machinery is **§8.2**, which is not. A's E7
closes the loop: §8.1's notorious pathologies are **soundness-side only** (*"nowhere in the proof of
completeness have we used the assumption that G is a tree"*, `chunk_0153:3`), and 517 needs only the
completeness direction. **C's instinct is vindicated; its section reference was off by one.**

**Corrected framing** (recommended):

| | Wrong (inherited from plan 01) | Correct |
|---|---|---|
| Name | `labelled_bounded_context_cs5_completeness` | labelled **context** CS5 completeness (Simpson Ch.5 + Ch.6 + §8.1.1) |
| Key targets | Lemma 8.2.5, Lemma 8.2.6, bounded prime lemma | **5.3.1** (prime lemma), **5.3.2** (canonical model lemma), **6.1.2 / 6.2.1-6.2.3** (adequacy), **8.1.1 / 8.1.2** (`B_K`) |

Note 8.2.5's *content* (`𝒯-Comp(H) ⊨_cl 𝒯`) is still needed — in its **Ch.5 unbounded form**, which
is already landed as `TPrime`'s `clModel` field.

**D's flagged uncertainty (#3) — RESOLVED.** D could not source-confirm that Ch.5/Ch.8 machinery is
disjoint from the C5 tree surgery, and asked A to confirm. **It is disjoint**, on two independent
confirmations: A's Route 2 diagram separates the legs (Ch.5 needs `TClosure` + Zorn; C5's
`star`/`prune`/`pathSpine` are Ch.6's derivation-to-formula translation), and B's F7 states it
explicitly — *"Ch.5 does not let us skip C5 … it is independent of C5."* **D2 may proceed
independent of C5.** D's confidence on that specific point rises from Medium to Medium-High.

### Conflict 7 — NOT NAMED IN THE DISPATCH: C's A5 contradicts D's F4 on Simpson's requirement 3. Adjudicated at source.

The two teammates make **directly incompatible** claims about the same object, and one of them
gates the recommended next dispatch:

- **C (A5)**: for quantifier-free `𝒯`, the witness vector `v̄_Υ` is empty, so requirement 3's
  antecedent is *vacuously true* and requirement 3 **asserts its consequent outright** — i.e. graph
  closure under reflexivity/Euclideanness. *"That is the strongest possible reading, not a vacuous
  one."* Therefore `GeomWitnessClosure := True` is a **load-bearing stub**, Lemma 5.3.1 is
  **unprovable as landed**, and this must be fixed before Phase 5 (~70% confidence).
- **D (F4)**: universal Horn ⟹ no existential conclusion ⟹ no Skolem witness ⟹ **clause 3
  constrains nothing**. Therefore delete `GeomAxiom.D`, and `GeomWitnessClosure` +
  `geomWitnessClosure_holds` + `Context`'s field can be **deleted outright**.

If C is right, D's deletion **destroys a substantive requirement** and is a corner-cut. This had to
be settled, so I read `chunk_0101` and `chunk_0102` in full.

**Requirement 3, verbatim (`chunk_0101`)**: *"For each basic geometric sequent Υ ∈ 𝒯 …, each of the
witness variables in v̄_Υ is in G only if the others are and, for some i (1 ≤ i ≤ m), the relations
R_i1[z̄/x̄][v̄_Υ/ȳ], …, R_in_i[z̄/x̄][v̄_Υ/ȳ] all hold in G."*

**Decisive argument — from Simpson's structure, not from grammar**: `TPrime`'s *own definition*
(`chunk_0101`, verbatim) reads *"A context (G,Γ) is said to be 𝒯-prime if **G is a classical model
of 𝒯** and …"*, and Lemma 5.3.1's proof opens *"**First, we show that H is a classical model of
𝒯**"* and then runs a **maximality argument** to establish it. **If requirement 3 already asserted
graph closure, every context would already be a classical model of 𝒯 and that entire step would be
a one-line citation of clause 3.** Simpson does not do that. **Therefore requirement 3 is not graph
closure. C's reading is wrong.**

**And the maximality branch delivers the goal directly** (`chunk_0102`, read in full): for a
quantifier-free axiom, `m = 1`, `ȳ` empty, `H₁ = H ∪ {R₁₁[z̄/x̄]}`. Simpson: *"it cannot be the case
that Δ ⊢_{H₁} x:A … because if it were then Δ ⊢_H x:A would be derivable by an application of
(R_Υ). Therefore … (H_i, Δ) is in C. Whence, by the maximality of (H,Δ), we have that H_i = H."*
**`H₁ = H` means `R₁₁[z̄/x̄] ∈ H` — which is exactly the goal.** Requirement 3 exists **solely** to
justify **witness variables**, which quantifier-free axioms do not have.

**Verdict: D's F4 is CORRECT; C's A5 defect claim is REFUTED — by C's own fair caveat**, which C
raised and then under-weighted: *"Simpson's contradiction-branch (maximality + rule (R_Υ), giving
H_i = H) might independently yield graph closure for quantifier-free 𝒯, making requirement 3
genuinely redundant. Confidence this is a real defect: ~70%."* **That caveat is the correct reading.
C's ~70% should be inverted to ~20%.**

**But C's underlying concern survives in corrected form, and it still gates Phase 5**: `clModel` is
a *field* that Lemma 5.3.1 must **discharge**, and the only mechanism is **maximality + (R_Υ)** —
which is **unlanded, unchecked, and is Phase 5's first real obstacle**. C's recommendation ("resolve
before Phase 5 is dispatched") **stands, with the mechanism corrected**: the obligation is not to
implement requirement 3, it is to confirm `TClosure` supports the `(R_Υ)` internalization the
maximality argument needs.

**Two secondary points, both to C**: (i) the landed docstring's stated reason — *"vacuous under the
present `Label` type"* (`Context.lean:130-138`, read this dispatch) — **is wrong on its own terms**,
exactly as C says; the real reason is *"no existential geometric axioms in the type"*. (ii) D's fix
makes the vacuity **structural rather than stipulated**, which is strictly more rigorous — D's
adversarial check #6 got this right.

**This conflict is itself the strongest evidence for C's systemic finding.** The OCR dropped the
definition of `H_i` — `chunk_0102` reads *"Define:"* followed by **nothing**. The one place two
teammates flatly contradicted each other is the one place the chunk text lost a formula.

### Consolidated defects inventory

| # | Defect | Locus | Found by | Verified here | Severity |
|---|---|---|---|---|---|
| 1 | `TS5 := {T, Five}` ⟹ `Ax(TS5) = IKT5`, but `CS5ModalAxiom = IKTB4`. Bridging needs an **unproved constructive** `IKT5 ⟺ IKTB4` on the critical path. Fix to `{T, B, Four}` ⟹ match is **definitional**. | `Labelled/Context.lean:247` | A (KF5) | Yes — `def TS5 : Set GeomAxiom := {GeomAxiom.T, GeomAxiom.Five}` | **High** (one line; removes an unproved step the directive forbids) |
| 2 | `GeomWitnessClosure := True` — vacuous def, rule-prohibited, **shipped via `Cslib.lean` root import** | `Labelled/Context.lean:138` | D (F3), C (A5), A (KF6) | Yes — `:= True`, `:= trivial`, `@[nolint unusedArguments]` | **High** (standards violation in mainline; the only corner currently cut) |
| 3 | `GeomAxiom.D` is the **sole existential** axiom; `TClosure`/`GeomWitnessClosure` silently ignore it ⟹ `Context {χ_D}` is a **wrong definition**. Delete `.D`. | `Deduction.lean:124` + 2 probe sites | D (F4) | Yes — `.D => ∀ x, ∃ y, R x y`; blast radius = 3 sites | **High** (fixes #2 structurally) |
| 4 | Pacheco Lemma 16's step `φ ∉ Θ ⟹ ¬φ ∈ Θ` is **invalid** (two independent grounds; one property-based, OCR-immune). **Lemma 18 defers to it.** True crux isolated: **∆-primality under the antitone `∆□ ⊆ Σ` cap**. | `Pacheco2024` chunk_0012 | B (F3) | Argument audited; survives C's OCR objection | **High** (holes the only literature route to `CS5 ⊢ FS`) |
| 5 | `cs5FC` provably **FAILS** in `B_K` (≤-composed transitivity needs cross-context edges `R′` cannot supply). Target `cs5FC''`/`cs5FCIncest`. **Retroactively validates task 509's pivot.** | `CKExtension.lean:159` vs `:184` | A (KF3) | Definitions confirmed | **Medium** (would have been a third false schema) |
| 6 | A3's `Γ□` → `Γ` transcription error (dropped `□` superscript) | plan 02:181 vs `CS5.lean:583` | C (A2) | `cs5TwoSidedR` first conjunct is `boxInv Γ ⊆ Δ` | **High** (load-bearing for the overturned NO-GO) |
| 7 | `pathSpine` **does not exist** — 3 repo-wide hits, all forward references in `probes/`, **zero definitions**. C5 has no statement, hence no truth value. | `probes/lemma612-scaffold.lean:364,375,760` | C (A7) | Yes — reproduced exactly | **Medium** (blocks "countermodel-check C5"; C rightly declined to fabricate an analysis) |
| 8 | `512 → 517 → 512` is a **literal dependency cycle**; graph unsatisfiable | `specs/state.json` | D (F7) | Cited (`512: [509,517]`, `517: [509,512,516]`) | **Medium** (bookkeeping; blocks 512 forever) |
| 9 | `Context.lean`'s "unbounded" rationale **inverts** the causal claim (cites the gap lemma as the reason to avoid the bound; Simpson uses the bound as *part of* the escape in §8.2) | `Labelled/Context.lean:~172, :35` | C (A6) | Docstring pattern confirmed | **Low** (steering hazard; landed Ch.5 design is defensible) |
| 10 | Docstrings reference plan 01's Phases 5/6 — a **superseded plan** | `Labelled/Context.lean` | D (F3) | Confirmed (`"Phase 5's Zorn chain-closure argument"`) | **Low** |

### Systemic finding: the transcription defect has a single root cause and a single rule fixes it

**C's finding, endorsed and independently corroborated by this synthesis.** Every transcription
error this task has produced is consistent with **agents reading formulae out of OCR chunk text**:

| Defect | What was misread |
|---|---|
| C2's false `V=[]` | formula, from chunk text |
| C4's defective `star` (double `bigAnd`) | formula, from chunk text |
| A3's dropped `□` in `Γ□ ⊆ ∆` | formula, from chunk text |
| **C's A5 vs D's F4 (this dispatch)** | **requirement 3 + the missing `H_i` definition** |

The literature index warns Simpson's OCR is *"unreliable for exact notation"* while *"prose and
structural content are reliable"*. **C proved the same class of defect in `Pacheco2024` — a modern,
non-OCR PDF.** And this synthesis found a fourth instance: `chunk_0102`'s *"Define:"* is followed by
**nothing**, which is precisely why C and D reached opposite conclusions.

**Proposed standing rule**: **chunk text is admissible for prose and structure; every formula must
be read from PDF layout, or reconstructed from a stated property.** (C reconstructed `Γ□ ⊆ ∆` from
Pacheco's own symmetry lemma; this synthesis reconstructed requirement 3's scope from Simpson's
proof *structure*.) **That one rule would have prevented C2, C4, A3, and Conflict 7.**

**Recommend adopting it.** It likely belongs in repo context/rules — which would be a **separate
meta task**. Per instruction, **no such task is created here**; flagged for the user.

### Prior art: 517 would be a world first, and CSLib's architecture is already validated

**B's F6, endorsed.** No IS5/CS5 Kripke completeness is mechanized in any proof assistant. Three
candidates eliminated concretely:

| Artifact | Verdict |
|---|---|
| **de Groot–Shillito–Clouston**, LICS 2025, Rocq (arXiv:2408.00262, `github.com/ianshil/CK`) — the state of the art | Covers **only the CK→IK diamond axis**. Full-text grep: **zero** hits for `symmetr`, `S5`, `IS5`, `euclid`. No B/T/4/5. |
| **Ayertienna/IS5** (Coq) | Proof-**terms** only. No Kripke semantics, no canonical model, no completeness. |
| **FormalizedFormalLogic** (Lean 4) | **Classical** modal only. |

**The architectural finding is worth more than the negative.** dGSC's canonical worlds are
**segments** `(Γ, U)` with `⊑` = **head-inclusion** — which is CSLib's `CKSegment`, **independently
arrived at and mechanized by the field's leading group**. **CSLib's architecture is validated as
state of the art.** Equally: dGSC's `≤` is head-inclusion too, so **`cs5Incest_forces_symm` would
bite their design exactly as hard** — they simply never attempt B. Recommend adding
`deGrootShillitoClouston2025` to `references.bib` regardless of route.

**MMS2021 is a dead end and any `labIK≤` budget should be killed** (B's F4, confidence high,
verbatim twice): MMS *import* semantic completeness — Thm 3.3 cites `[Ser84, PS86]`; Thm 7.2 appeals
to Thm 7.1 = `[PS86]`. They contribute 1⟹2⟹3⟹4 (derivability, cut-elimination, soundness); 517
needs **4⟹1**. **MMS retains exactly one value**: Thm 7.1's `g0011` condition **is** CSLib's
`cs5Incest` (`CS5Canonical.lean:234-235`) — solid H3 grounding that `cs5Incest` is the
literature-sanctioned intuitionistic condition for B.

### Process signal: the teammates corrected themselves, which raises confidence in the convergence

Each of A, B, C, D killed or corrected **its own** hypothesis, against its own interest:

| Teammate | Self-correction |
|---|---|
| **A** | First draft said the gap lemma "doesn't apply" — **wrong**; revised to *true but inert*. Killed its **own assigned angle** (Ch.7-8 is a dead end) and its **own preferred shortcut** (S5 collapses the tree). Caught `cs5FC` failing, averting a third false schema. |
| **B** | Killed its own "`cs5FC''` unachievable" hypothesis (F5 refuted it). Killed its own MMS budget. Declined to overclaim the ∆-primality half. |
| **C** | Raised the fair caveat that refutes its own A5 defect claim (see Conflict 7). Declined to fabricate an analysis of the nonexistent C5. |
| **D** | Revised 3 claims against its own thesis (bridge **is** required; off-roadmap is weak; negative result demoted from headline). |

**Convergence reached by four agents that each demolished their own preferred answer is worth more
than convergence reached by agreement.** This is the main reason the Ch.5 finding is carried as the
report's headline rather than as one option among several.

## Decisions

1. **Route**: **Ch.5 (5.3.1 + 5.3.2) + Ch.6 (6.1.2, incl. C5) + §8.1.1 (`B_K`)** — A's Route 2,
   **reordered per D2** so that Ch.5 (leg A) precedes Ch.6 (leg B). Rejected: Ch.7-8 bounded
   (`T_S5 ∉ Dec_ND`); Ch.3 Thm 3.3.4 shortcut (delegates to a source not in corpus); MMS `labIK≤`
   (~0%); dGSC port (~0% for CS5).
2. **Named blocking obligation**: **decide `CS5 ⊢ FS`** (C's B1). **Not** `FischerServi1984` —
   demoted to optional/low-priority (Conflict 1).
3. **Target**: unchanged and **not weakened** — `CKValidFC cs5FC'' φ → Derivable CS5ModalAxiom φ`.
   Must target `cs5FC''`/`cs5FCIncest`, **never** `cs5FC` (`B_K` provably does not inhabit it).
   D's rejection of all reformulations is endorsed.
4. **Track B**: **REOPENED**. A3's NO-GO rationale is unsound and, applied consistently, closes Ch.5
   too. Plan 02 Phases 4-6 `[BLOCKED]` → `[NOT STARTED]`, deprioritized. Track B remains a **probe**
   (~35%), not the route.
5. **Track C / Ch.6**: **required** (report 02's ~85% superseded and inverted, ~90% the other way),
   but **reordered behind leg A**. C1-C4 keep full value and lose nothing by waiting.
6. **Conflict 7 (requirement 3)**: **D's reading is correct; C's A5 defect claim is refuted at
   source.** But C's Phase-5 gate **stands with a corrected mechanism**: confirm `TClosure` supports
   the `(R_Υ)` internalization the maximality argument needs.
7. **Do NOT dispatch C5 next.** It has no statement (defect 7), it is the wrong half first (D's F2),
   and both A1 and the A3 rationale outrank it and can invalidate the track.
8. **Headline probability**: **~10%** for the full target via the recommended route over ~8-12
   dispatches. Leg A alone: **~50%**, and independent of the target's truth.

## Recommendations

### Priority 1 — The next dispatch: three cheap items, none of which is C5

All three are cheap, decisive-or-mandatory, and mutually independent. **The two probes are
complementary and should both precede any further C5 work** — they interlock (see below).

1. **[~2 lines, cannot fail] Mechanize `cs5_completeness ⟹ CS5 ⊢ FS`** (C's A1). State
   `cs5_completeness` as a hypothesis, instantiate at `φ := FS`, discharge via the landed
   `fs_sound''`. This converts the entailment from an argument into a **landed theorem** and makes
   the necessary condition undeniable. It settles Conflict 2's status regardless of which way
   `CS5 ⊢ FS` later resolves.
2. **[~50-100 lines, decisive] Probe `B_K ⊨ cs5FC''`** (A's KF3). Statable **abstractly** over an
   arbitrary IL-model `K` — it does **not** need the canonical model, so it is available now. Moves
   A's ~85% row to **settled**, confirms the target's frame class, and independently re-validates
   task 509's `cs5FC''` pivot.
3. **[~2-4h, non-optional] Make the landed framework honest** (D1 + A's KF5). Delete `GeomAxiom.D`
   (3 sites, verified); delete `GeomWitnessClosure`, `geomWitnessClosure_holds`, and `Context`'s
   `geomWitnessClosure` field — clause 3 becomes **absent by construction**, not vacuous by
   stipulation (Conflict 7). **Fix `TS5` → `{GeomAxiom.T, GeomAxiom.B, GeomAxiom.Four}`** (defect 1),
   making `Ax(TS5) = CS5ModalAxiom` **definitional** and removing an unproved `IKT5 ⟺ IKTB4` from the
   critical path. Update docstrings referencing plan 01's superseded phases.

**Why the two probes interlock — the strongest reason to run both.** `fs_sound''` gives
`cs5FC'' ⊨ FS`. If item 2 confirms `B_K ⊨ cs5FC''`, then **the route's own countermodel construction
validates `FS`** — so the route **cannot** produce a countermodel for `FS`, and therefore cannot
prove completeness **unless `CS5 ⊢ FS`**. The two probes together convert A1 from a necessary
condition of the *theorem* into a necessary condition of the *method*. Neither teammate stated this;
it falls out of composing A's KF3 with C's A1.

**Item 3 is required regardless of every other decision.** Per the user's directive, **the only
corner currently cut in this entire effort is already in `Cslib/`** and is shipped via the root
import. Fixing it is not a trade-off; it is an obligation.

### Priority 2 — Gate on A1, then leg A

4. **Decide `CS5 ⊢ FS`.** Prioritize the **untried** direction: attempt a `CS5`-countermodel
   refuting `FS` (a model validating all 17 `CS5ModalAxiom` clauses and refuting `FS`). Every
   dispatch to date has attacked derivation and failed; nobody has tried refutation. **If refuted →
   the target is FALSE → `[BLOCKED]`, restate the target, terminate 509/512/517 as scoped.** If
   derived → the task is alive.
5. **Then dispatch leg A: Prime Lemma 5.3.1 + Canonical Model Lemma 5.3.2, at `𝒯 = ∅` (IK) first**
   (D2). Every wall in this history is symmetry-driven; at `𝒯 = ∅` `TClosure` collapses to `base`,
   exercising the whole Ch.5 pipeline with the wall removed. This is **Simpson's own order** (base
   system, then geometric extension) and changes no theorem statement. **Pre-gate**: confirm
   `TClosure` supports the `(R_Υ)` internalization that discharges `clModel` (Conflict 7's corrected
   obligation).

### Priority 3 — Paper fixes, cheap, high steering value

6. **Revise A3's rationale and Phases 4-6's `[BLOCKED]` markers** (Conflict 4). **Mandatory**: left
   standing, the rationale closes the recommended route.
7. **Correct the stated escape** in plan 02 and `Context.lean`'s module docstring: the escape is the
   `≤`-quantified box clause + simultaneous maximal pair — **not** non-primality. C's A3 is decisive
   here: `TPrime.disjunction` (`Context.lean:224-236`) and Simpson `chunk_0172` both confirm bounded
   contexts **are** prime, so a team designing toward weakening primality would break the `∨` case of
   the truth lemma and buy nothing.
8. **Reframe the task** per Conflict 6, and **assign an owner to each of the four bridges** (C's B4)
   — *an unowned bridge is the task's real status*.
9. **Break the 512↔517 cycle** (D4): remove `517` from 512's dependencies; close 512 as
   completed-with-negative-result, banking `cs5_axiom_sound_incest` + the guardrail lemmas. Pure
   bookkeeping; zero mathematics.

### Priority 4 — Deferred

10. **C5** — only after items 1-5. When dispatched: **statement first, in isolation, with a
    small-model check (trees of depth ≤ 3) before any proof attempt.** Given the base rate,
    statement-first + countermodel-first is the only discipline that has been catching these.
11. **Probe B′** (Pacheco Lemma 18 joint Zorn, ~150-250 lines, ~35%) — optional. Decisive either
    way: if ∆-primality lands, CS5 completeness follows over plain theories; if it provably fails, the
    task's diffuse obstruction becomes a single mechanized negative lemma. Not on the critical path.
12. **`FischerServi1984`** — optional, low priority (Conflict 1). **Not blocking.**

### What would falsify this recommendation

Stated explicitly, per instruction:

| Falsifier | Consequence |
|---|---|
| A `CS5`-countermodel refuting `FS` is found | **Target is FALSE.** Recommendation void; `[BLOCKED]`; restate the target. **~25% likely.** |
| Probe 2 shows `B_K ⊭ cs5FC''` | A's KF3 is wrong; the §8.1.1 leg collapses; the target's frame class is wrong; route needs re-derivation. **~15%.** |
| `TClosure` cannot support the `(R_Υ)` internalization, and requirement 3 cannot be implemented | `clModel` undischargeable ⟹ **leg A blocked** ⟹ whole route blocked. **~20%.** |
| `FischerServi1984` is obtained and contains a genuine constructive IS5 birelational completeness proof for `cs5FC''`'s frame class | The Ch.3 shortcut revives; Route 2 is dominated and C5 retires. **~10%.** |
| Ch.5's 5.3.1 proves to need Ch.6's tree surgery after all | D's #3 uncertainty resurfaces; legs A and B are not independent; ordering argument collapses. **~10%** (currently resolved against, by A + B). |

## Risks & Mitigations

| Risk | Severity | Mitigation |
|---|---|---|
| **The target is false (~25%)** and dispatches continue against it | **Critical** | Priority 1 item 1 (~2 lines) + Priority 2 item 4. Gate everything on it. |
| A3's unsound rationale left standing **closes the recommended route** | **High** | Priority 3 item 6 — mandatory, paper-only |
| Formulae re-read from OCR chunk text ⟹ a 4th/5th transcription defect | **High** (observed base rate ~100%/dispatch) | Adopt the standing rule (Systemic finding). Flag for a separate meta task. |
| Vacuous `:= True` shipped in mainline; no CI gate catches it (it is not a `sorry`) | **High** | Priority 1 item 3 — non-optional, ~2-4h |
| Receding horizon: 5 consecutive verdicts overturned; estimates grew 12-20h → 40-70h, and the 40-70h **does not include the theorem** | **High** | Report honest conditioned numbers only (Conflict 3). Bank leg A, which survives target-falsity. |
| Spending the full budget on leg B (the bridge) and ending with **a bridge to nowhere** | **High** | D's F2 ordering: leg A first — it strictly dominates on standalone value and is the unestimated risk |
| Ch.5's metatheory is **classical** (Zorn/Lindenbaum) while the object logic is constructive | **Low** | Not a defect: `Classical.choice` is ambient in Mathlib and is not a new axiom under `Cslib/`. State it in the plan so it is not later mistaken for one. Simpson notes a choice-free variant exists (`chunk_0103:3`), mitigating but not needed. |
| Overclaiming the negative result as a modal-logic contribution | Medium | D's F8: the **mechanization** is the contribution, not the discovery. Simpson's own Ch.7-8 method-switch already encodes it. Ship as a formalization-experience report with 509's scope caveat intact. |

## Context Extension Recommendations

- **Topic**: Reading formulae from OCR'd / extracted literature chunks
  - **Gap**: No rule governs the distinction between prose and notation in chunk text. The
    literature index warns Simpson's OCR is *"unreliable for exact notation"*, but nothing enforces
    it; this task has produced four defects of exactly this class, including one in a **modern
    non-OCR PDF** (`Pacheco2024`) and one that made two teammates contradict each other
    (`chunk_0102`'s missing `H_i` definition).
  - **Recommendation**: add a rule to repo context — *"chunk text is admissible for prose and
    structure; every formula must be read from PDF layout or reconstructed from a stated property."*
    Per instruction, **no meta task created here**; flagged for the user.

## Appendix

### References — literature (BibKeys verified in `references.bib`: `Simpson1994:86`, `Pacheco2024:895`, `MarinMoralesStrassburger2021:962`)

- `Simpson1994` — `chunk_0068` (Thm 3.3.4, Fig 3-7 `Ax(-)`, IS5 → Fischer Servi); `chunk_0075:3`
  ("results of Chapters 5 and 6"); `chunk_0098` (IL-model box clause, `≤`-quantified);
  **`chunk_0101`** (context requirements 1-3, `𝒯`-prime clauses — read in full this dispatch);
  **`chunk_0102`** (**Lemma 5.3.1 Prime Lemma**, Zorn over whole contexts, maximality + `(R_Υ)` —
  read in full; note the OCR-dropped `H_i` definition); `chunk_0103` (Lemma 5.3.2, disjunction
  property, choice-free remark); `chunk_0111:3` (Lemma 6.1.2, *"If G is a finite tree"*);
  `chunk_0114:9` (Thm 6.2.1 scope incl. `T_S5`); `chunk_0115`/`chunk_0116` (Lemma 6.2.2, `(R_χ)`
  internalized); `chunk_0117:3` (Lemma 6.2.3 → 6.1.2); `chunk_0121` (Thm 5.2.1 + Thm 6.2.1);
  `chunk_0132:13` (**`Dec_ND` — `T_S5` absent**); `chunk_0149:3` (Ch.7 Kanger/set-indexed remark);
  `chunk_0152:3` (§8.1.1 `B_K`); `chunk_0153:3` (completeness needs no tree); `chunk_0158`
  (`Dec_L`, Thm 8.1.4, universal-relation caveat); `chunk_0163` (§8.2.1 re-proves §5.3);
  `chunk_0166` (Lemmas 8.2.5/8.2.6, depth-indexed); `chunk_0167:5` (canonical model box case —
  the escape mechanism); `chunk_0172` (bounded contexts **are** prime); `chunk_0174:13`;
  `chunk_0175:3`
- `Pacheco2024` — `chunk_0008` (CKB-models: **plain** symmetry + confluence); `chunk_0009`
  (Thm 13; "(2)⟺(4) already proved by Simpson"); `chunk_0010`/`chunk_0011` (`Mc`, `Wc⊥ = ∅`,
  `∼c`, Lemma 15 symmetry); **`chunk_0012`** (**Lemma 16 — the invalid `¬φ ∈ Θ` step**);
  **`chunk_0013`** (**Lemma 18 — joint Zorn over pairs**)
- `MarinMoralesStrassburger2021` — `chunk_0009` (Thm 2.5 `[Ser84, PS86]`); `chunk_0018` (Thm 3.3 —
  1⟺4 **imported**); `chunk_0043` (Thm 7.1 `[PS86]` — `g0011` **is** `cs5Incest`); `chunk_0044`,
  `chunk_0046` (Thm 7.2, Remark 7.3); `chunk_0050` (`[PS86]` full reference)
- Not in corpus: **`FischerServi1984`** (deprioritized — Conflict 1); `PlotkinStirling1986`
  (declined); **`deGrootShillitoClouston2025`** (recommend adding — arXiv:2408.00262, LICS 2025)

### References — mechanization prior art

- de Groot, Shillito, Clouston, *Semantical Analysis of Intuitionistic Modal Logics between CK and
  IK*, LICS 2025 — https://arxiv.org/abs/2408.00262 · artifact https://github.com/ianshil/CK ·
  https://ianshil.github.io/CK/toc.html (Rocq 9.0.0; "segAB" = A-/B-segments of Def VI.3, **not**
  the B axiom)
- Ayertienna, *IS5 — Intuitionistic S5 logic formalization* (Coq) —
  https://github.com/Ayertienna/IS5
- FormalizedFormalLogic (Lean 4) — https://github.com/FormalizedFormalLogic/book

### References — codebase (all verified at source this dispatch unless noted)

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean:158-159` — *"**not** a library-level 'CS5
  completeness is blocked' verdict … non-vacuous open sub-problem"* (C cited `:152-157`; actual
  location `:158-159`)
- `CS5.lean:703-706` — *"simultaneous maximal pair, not sequentially"* — **the convergence anchor**
- `CS5.lean:712-718` — `cs5_symmetric_tail_box_gap`; uses `hT` **only** via `hT.disj`; concludes at
  **fixed `H`** under `hq : q ∉ H`
- `CS5.lean:148-150` — "Pacheco … its primeness step, Lemma 16, is unsound as written" (cited by C)
- `CS5.lean:583-589` — `cs5_boxInv_subset_iff`; `∼c` as `Γ□ ⊆ ∆ ∧ ∆ ⊆ Γ♦`
- `CS5Canonical.lean:487-488` — `cs5TwoSidedR`; **first conjunct is `boxInv Γ ⊆ Δ`, not `Γ ⊆ Δ`** —
  refutes plan 02:181
- `CS5Canonical.lean:511, 643, 661` — `cs5TwoSidedR_iff_cs5Tail`, `cs5Incest_forces_symm`,
  `cs5PrimeMreach_ofHead_to_univ` (the `Ω` step the wall depends on)
- `CS5Canonical.lean:234-235` — `cs5Incest` = MMS/`[PS86]` `g0011`
- `CKExtension.lean:159` vs `:184` — `cs5FC` (fails in `B_K`) vs `cs5FC''` (conjunct 3 = **plain
  symmetry**)
- `Labelled/Context.lean:130-138` — `GeomWitnessClosure := True`, `@[nolint unusedArguments]`, and
  the docstring's incorrect *"vacuous under the present `Label` type"* rationale
- `Labelled/Context.lean:224-236` — `TPrime`, clause 3 `disjunction` — **refutes "not prime"**
- `Labelled/Context.lean:247` — `def TS5 : Set GeomAxiom := {GeomAxiom.T, GeomAxiom.Five}` —
  **defect 1**
- `Labelled/Deduction.lean:122-127` — `GeomAxiom.Holds`; `.D => ∀ x, ∃ y, R x y` — **the sole
  existential axiom** (defect 3)
- `probes/fischer-servi-probe.lean:132-144` — `fs_sound''`, sorry-free, axiom-clean
- `probes/lemma612-scaffold.lean:364,375,760` — **the only 3 `pathSpine` occurrences repo-wide, all
  forward references, zero definitions** (defect 7)
- `plans/02_decomposed-track-a-b-c.md:173` — *"The open syntactic `CS5 ⊢ FS` question is orthogonal
  to Track B and was a red herring for gating purposes"* — **verified verbatim; refuted by C's A1**
- `grep -cE "8\.2\.5|8\.2\.6|Prime Lemma|5\.3\.1|truth lemma" plans/02_decomposed-track-a-b-c.md`
  → **0** (reproduced this dispatch)
