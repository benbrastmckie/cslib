# Implementation Plan: Task #517 — CS5 Completeness via Simpson Ch.5 + Ch.6 + §8.1.1, Gated on `CS5 ⊢ FS`

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Status**: [IMPLEMENTING]
- **Effort**: 7 phases landed (~8 dispatches spent); ~10-16 dispatches remaining (~60-100 hours), HIGH
  uncertainty. Honest headline: **~10%** the full target lands via the recommended route; **leg A
  alone (`NIK(𝒯)`-completeness) is ~50% and survives target-falsity**.
- **Dependencies**: 509, 512, 516
- **Research Inputs**:
  - reports/07_team-research.md (**THE authoritative input**; 4 teammates + synthesis; overturns A3,
    supersedes report 02's headline, names the `CS5 ⊢ FS` blocking obligation)
  - reports/07_teammate-a-findings.md (Simpson Ch.5/7-8; KF2 escape mechanism; KF3 `B_K ⊨ cs5FC''`;
    KF5 `TS5` defect)
  - reports/07_teammate-b-findings.md (prior art; Pacheco Lemma 16 defect; MMS/dGSC eliminations)
  - reports/07_teammate-c-findings.md (critic; A1 entailment; A2 `Γ□` transcription error)
  - reports/07_teammate-d-findings.md (horizons; leg-A-first ordering; requirement-3 reading)
  - reports/02_adequacy-alternatives-and-technique.md (**headline SUPERSEDED and inverted**; the
    5th mechanization defect and the base-rate warning remain valid)
  - reports/01_labelled-bounded-context-method.md (superseded on routing; framework map still valid)
- **Artifacts**: plans/08_ch5-canonical-model-fs-gate.md (this file); supersedes
  plans/02_decomposed-track-a-b-c.md
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Team research (4 teammates, 4 disjoint angles, 1 synthesis) converged independently on a single
object the active plan contained **none** of: **Simpson Lemma 5.3.1 (Prime Lemma) + Lemma 5.3.2
(canonical model / truth lemma)**. `grep -cE "Prime Lemma|5\.3\.1|truth lemma" plans/02` returns
**0**. Plan 02 dropped plan 01's Phases 5-9 and replaced them with a one-line "assembly" phase —
meaning that even if C5-C8 all closed, `cs5_completeness` was at **zero, unplanned and unestimated**.

This revision reroutes to **Ch.5 (5.3.1 + 5.3.2) + Ch.6 (6.1.2, incl. C5) + §8.1.1 (`B_K`)** —
Simpson's own named route (*"It will follow from the results of Chapters 5 and 6"*, `chunk_0075:3`)
— **reordered so Ch.5 (leg A) precedes Ch.6 (leg B)**, and **gated on a decision probe for
`CS5 ⊢ FS`**, which the team proves is *entailed* by the target (~25% the target is FALSE).

**Definition of done**: `cs5_completeness : CKValidFC cs5FC'' φ → Derivable CS5ModalAxiom φ` lands
sorry-free and axiom-clean. If Phase 19's gate refutes `CS5 ⊢ FS`, the target is **false**; the task
moves to blocked status with a mechanized negative result, and leg A is banked as an independent
contribution.

**Zero-debt invariant**: no `sorry`, no new `axiom`, no vacuous `:= True` definitions under `Cslib/`
at any phase boundary. Partial work lives in `probes/` (`sorry` permitted there only).

**Classical-metatheory note (state it once, so it is never later mistaken for a defect)**: Ch.5's
prime lemma is a Zorn/Lindenbaum argument, so the *metatheory* is classical while the *object logic*
stays constructive. `Classical.choice` is ambient in Mathlib and is **not** a new axiom under
`Cslib/`; the landed C1-C4 footprint `[propext, Classical.choice, Quot.sound]` is the bar. Simpson
notes a choice-free variant exists (`chunk_0103:3`) — mitigating, not required.

**Transcription discipline (standing rule, adopted plan-level)**: **chunk text is admissible for
prose and structure; every formula must be read from PDF layout, or reconstructed from a stated
property.** This one rule would have prevented all four transcription defects this task has produced
(C2's false `V=[]`, C4's defective `star`, A3's dropped `□`, and the requirement-3 conflict). It
binds every phase below that transcribes a schema.

#### Research Integration

- **reports/07_team-research.md** — integrated in plan version 3. Supplies: the Ch.5 convergence
  (new Phases 20-23); the `CS5 ⊢ FS` decision gate (new Phases 16, 19); the `B_K` probe (new Phase
  17); the honesty fixes (new Phase 18); the A3 overturn (Phases 4-6 `[BLOCKED]` → `[NOT STARTED]`);
  the Ch.6 reordering (Phases 11-14 moved behind leg A); the C5 split (Phases 11 / 25).
- reports/07_teammate-{a,b,c,d}-findings.md — integrated in plan version 3 via the synthesis;
  consulted directly for KF2/KF3/KF5, the Pacheco Lemma 16 defect, and A1/A2.
- reports/02_adequacy-alternatives-and-technique.md — integrated in plan version 2. **Its headline
  ("Ch.6 adequacy bridge NOT on the critical path, ~85%") is SUPERSEDED and INVERTED** (~90% the
  other way; refuted by Simpson's own prose, `chunk_0075`/`chunk_0121`, outside the OCR defect zone).
  Its 5th-defect finding and base-rate warning survive.
- reports/01_labelled-bounded-context-method.md — integrated in plan version 1; superseded on routing.

#### CONFLICT NOTICE: state.json's `blockers` field is STALE

`state.json`'s `blockers` field records **"TRACK B CLOSED (A3 verdict)"** and **"NEXT = C5"**. Both
are **superseded by reports/07_team-research.md**, which is newer. Where they conflict, the team
research governs. Specifically:

| Stale claim in `blockers` | Corrected position (team research) |
|---|---|
| "TRACK B CLOSED (A3 verdict)" | **A3 is OVERTURNED** (Conflict 4). Its rationale rests on a transcription error and, applied consistently, closes Ch.5 — the recommended route — too. Track B is **REOPENED as an optional probe** (~35%), not as the route. |
| "ROUTE = TRACK C (Simpson tree surgery, C1-C8)" | Track C / Ch.6 is **required** but **reordered behind leg A** (Ch.5). It is a bridge; leg A is the thing being bridged. |
| "NEXT = C5: pathSpine + commutation lemma" | **Do NOT dispatch C5 next** (Decision 7). `pathSpine` has **zero definitions** (verified: 3 forward references in comments, `lemma612-scaffold.lean:364,375,760`) — C5 has no statement, hence no truth value. |
| (absent) | The **named blocking obligation is `CS5 ⊢ FS`**, not `FischerServi1984`. ~25% the target is FALSE. |

The `blockers` field should be rewritten to match this plan at the next state update.

#### Preserved landed assets (do NOT redo — all sorry-free, axiom-clean, verified this dispatch)

- `Cslib/.../Labelled/Syntax.lean` (202 ln), `Deduction.lean` (312 ln), `Context.lean` (275 ln) —
  ~789 lines, CI-green. Independent contribution even if `cs5_completeness` never lands.
- `probes/lemma612-scaffold.lean` — A1 (`IKAx` with Simpson axioms 3/4/5); C4 (`LTree`, fixed `star`,
  `fullSubtree`, `prune`, `star_unfold_imp1`/`imp2`).
- `probes/fischer-servi-probe.lean` — A2 (`fs_context_relative_half`; `fs_sound''`, axiom-free).
- `probes/track-c-c1-tele-conj.lean` — C1 (`Conj`/`Tele`/`Tele_imp1`/`Tele_imp2`), C2
  (`formula_6_7`, nonempty `V`), C3 (`derivable_imp_trans`, `formula_6_8`, all `W`).
- `probes/adequacy-gate-probe.lean` — Lemma 6.2.2 hard direction (`NIK_to_NIKAx`).
- Verified: **zero `sorry` tokens** across all four probe files (all textual matches are docstrings).

## Goals & Non-Goals

- **Goals**:
  - Resolve the `CS5 ⊢ FS` obligation **before** spending further dispatches against a target that is
    ~25% likely to be false.
  - Land leg A (`NIK(𝒯)`-completeness via Simpson 5.3.1 + 5.3.2) — **`𝒯`-generic over the 16-logic
    intuitionistic modal cube, and independent of the target's truth**. This is the honest value
    proposition, not the ~10%.
  - Remove the only corner currently cut in mainline `Cslib/` (Phase 18) — non-optional.
  - Keep every landed artifact sorry-free and axiom-clean at each phase boundary.
- **Non-Goals**:
  - Do **NOT** dispatch C5 as plan 02 specified it (define + prove in one dispatch). See Phase 11.
  - Do **NOT** pursue Ch.7-8 bounded contexts: `T_S5 ∉ Dec_ND` (`chunk_0132:13`). Boundedness is a
    decidability/FMP device; 517 needs neither. **The task title is a misnomer.**
  - Do **NOT** route through Thm 3.3.4 (Ch.3): its entire proof is one sentence delegating IS5 to
    `FischerServi1984`, which is not in the corpus.
  - Do **NOT** port MMS `labIK≤` (~0%) or de Groot–Shillito–Clouston (CK→IK diamond axis only; zero
    hits for `symmetr`/`S5`/`euclid`).
  - Do **NOT** weaken or restate the target, and **never** target `cs5FC` (`B_K` provably does not
    inhabit it — KF3).

## Risks & Mitigations

- **Risk (CRITICAL, ~25%)**: **the target is false.** `cs5_completeness` *entails* `CS5 ⊢ FS`
  (instantiate at `φ := FS`, discharge via the landed `fs_sound''`). Plan 02:173's "orthogonal … red
  herring" is verified verbatim and is **wrong**.
  **Mitigation**: Phase 16 (~2 lines, cannot fail) makes the entailment a landed theorem; Phase 19 is
  a hard decision gate with a documented branch for each outcome. Gate everything on it.
- **Risk**: A3's unsound rationale left standing **closes the recommended route**. A's KF2 shows the
  gap lemma's hypotheses *are* satisfied in Simpson's construction — under A3's rationale, Ch.5 is
  also NO-GO.
  **Mitigation**: retracted in this plan (Phase 3's entry) and in Phases 4-6's markers. Paper-only,
  mandatory.
- **Risk (base rate ~100%/dispatch)**: another transcription defect. Every dispatch on this gate has
  found the previous one's transcription subtly wrong — including report 02 itself, and including a
  defect in a **modern non-OCR PDF** (`Pacheco2024`).
  **Mitigation**: the standing rule in the Overview; mandatory countermodel/small-model check on
  every transcribed schema BEFORE writing Lean (this discipline caught C2's `V=[]` and C4's `star`).
- **Risk**: spending the full budget on leg B (the bridge) and ending with **a bridge to nowhere**.
  **Mitigation**: leg-A-first ordering (D's F2). C1-C4 are landed and lose nothing by waiting.
- **Risk (~20%)**: `TClosure` cannot support the `(R_Υ)` internalization that discharges `clModel`
  ⟹ leg A blocked ⟹ whole route blocked.
  **Mitigation**: Phase 20 is a cheap paper/probe pre-gate before Phase 21 is dispatched.
- **Risk (~15%)**: `B_K ⊭ cs5FC''` ⟹ the §8.1.1 leg collapses and the target's frame class is wrong.
  **Mitigation**: Phase 17 probes it abstractly, **now**, without needing the canonical model.
- **Risk**: regression of landed CK/CT/CS4/CS5 soundness or task-509 `cs5FC''`.
  **Mitigation**: only Phase 18 touches `Cslib/`, and only under `Labelled/`; reverify untouched
  declarations compile after each edit; full CI gate before any PR.
- **Risk**: overclaiming a negative result as a modal-logic contribution.
  **Mitigation**: the **mechanization** is the contribution, not the discovery. Ship as a
  formalization-experience report with task 509's scope caveat intact.

## Why the new design does NOT trip the four guardrails

Every guardrail is **landed, sorry-free, and axiom-free**; none is refuted here. The escape is
representational, and it must be stated precisely — the naive statement ("the relation avoids
symmetry") is **false and would be a fifth defect**.

| Guardrail | Why the Ch.5 + §8.1.1 design does not trip it |
|---|---|
| `cs5_symmetric_tail_box_gap` (CS5.lean:712, task 509) | **TRUE of Simpson's construction, but INERT.** Its hypothesis `hq : q ∉ H` is at a **fixed head**. The IL-model box clause quantifies over the `≤`-future (`chunk_0098`: *"w,d ⊩ □A iff for all w' ≥ w …"*), so the refuting witness lives at a **strictly larger context** where `q ∉ H` is **not preserved** — the lemma does not fire there. In `CS5Canonical`'s design `H` is fixed, so this freedom does not exist. **That freedom is the whole escape.** A hand-verified consistency (KF2 Step 4): `Δ′` is maximal w.r.t. `Δ′ ⊬ z:p`, and Lindenbaum is free to select `z:□q` together with `y:q`, so nothing derives `z:p`. No contradiction. |
| `cs5Incest_forces_symm` (CS5Canonical.lean:643, task 512) | Constrains **theory-to-theory** relations over `Preorder`-headed worlds. In `B_K` the modal relation **never relates two theories**: `(w,d) R′ (w′,d′) iff w = w′ and R_w(d,d′)` (`chunk_0152:3`) — `R′` moves the **label** holding the **context** fixed, while `≤′` grows the context holding the label fixed. The two dimensions are **orthogonal**. Symmetry of `R′` is symmetry of the graph `𝒯-Comp(H)` — a **classical first-order graph fact**, discharged by the **(R_B) structural rule** (`chunk_0167:5`), never by cross-theory negation-completeness. The theorem's `hbox` hypothesis (`r w u → boxInv(head w) ⊆ head u`) is about theory heads; `B_K`'s worlds are `(context, label)` pairs whose "head" is not a theory the relation ranges over. |
| `cs5TwoSidedR_iff_cs5Tail` (CS5Canonical.lean:511) | Same ground: it characterizes `cs5TwoSidedR` (first conjunct `boxInv Γ ⊆ Δ` — **not** `Γ ⊆ Δ`; A3's transcription dropped the `□`, defect 6) as `cs5Tail`-shaped. `B_K`'s `R′` is not of this form for the reason above. **Load-bearing caveat (B's reductio, and the reason A3's rationale must be retracted rather than merely disagreed with)**: `cs5FC''` conjunct 3 **is** plain symmetry (`CKExtension.lean:184`), so Track C's own countermodel *also* lands in `cs5Tail`-shape. **A criterion that closes Track B on that basis closes Track C too.** The escape is therefore *not* "no symmetry" — it is the non-fixed head + simultaneous maximal pair. |
| task-512's atom-sum results | Concern prime **theories** and their atom decompositions. Leg A's worlds are **`𝒯`-prime labelled contexts `(H,Δ)`**, not theories; `Th(w,d) = {B | d:B ∈ Δ_w}` is a *restriction* of a single object `Δ`, not an independently-maximized theory. Both head `Th(Δ′,y)` and tail `Th(Δ′,z)` come from **ONE Lindenbaum maximization** on `(H ∪ {yRz}, Δ)` (`chunk_0167:5`) — which is **exactly** the *"simultaneous maximal pair, not sequentially"* that `CS5.lean:705-706` names as *"the real open problem"*. The atom-sum results constrain the sequential construction they were proved about. |

**Corroboration that this is not wishful reading**: CSLib's own file states the opposite verdict to
A3's (`CS5.lean:158-159`, verbatim): *"This is **not** a library-level '`CS5` completeness is
blocked' verdict — it is a narrow, well-understood, and non-vacuous open sub-problem."* **A3 read
non-vacuity as impossibility and inverted the verdict of the file it cited.**

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 0 | 1, 2, 3, 7, 8, 9, 10 | -- (all [COMPLETED], landed) |
| 1 | 16, 17, 18, 26 | -- |
| 2 | 19, 20 | 16, 17, 18 |
| 3 | 4, 21 | 19, 20 |
| 4 | 5, 22 | 4, 21 |
| 5 | 6, 23 | 5, 18, 22 |
| 6 | 11, 24 | 10, 17, 19, 23 |
| 7 | 25 | 11 |
| 8 | 12 | 10, 25 |
| 9 | 13, 14 | 12, 25 |
| 10 | 15 | 12, 13, 14, 24 |

Phases within the same wave can execute in parallel. **Phase numbers are identities, not execution
order** — preserved phases keep their plan-02 numbers so that landed summaries and handoffs keep
resolving; new phases are appended at 16+ and run FIRST (waves 1-2). Phases 4, 5, 6 are **optional,
off the critical path** (Track B probe). Phase 19 is a **hard decision gate**: waves 3+ do not open
on a NO verdict.

**Leg map** (recommended route, A's Route 2 reordered per D2):
```
CS5 ⊬ A
  └─[Ch.6: Thm 6.2.1 via Lemma 6.2.2 + 6.2.3 + 6.1.2 tree surgery]   ← leg B: Phases 7-14, 25
CS5 = IK + Ax(T_S5) ⊬ A  ⟹  N_ND(T_S5) ⊬ x:A
  └─[Ch.5: Thm 5.2.1 (3⇒1): prime lemma 5.3.1 → 𝒯-prime context]     ← leg A: Phases 20-23
IL-model K over 𝒯-prime contexts, (H,Δ),x ⊮ A   [canonical model lemma 5.3.2]
  └─[§8.1.1: B_K = {(w,d)}; Lemma 8.1.2]                             ← leg C: Phase 24
birelation countermodel B_K, and B_K ⊨ cs5FC''                       ← Phase 17 probes this NOW
  ⟹ ¬ CKValidFC cs5FC'' A   ∎  cs5_completeness                      ← Phase 15
```

### Phase 1: Track A1 — Repair `IKAx` to be actually IK [COMPLETED]
- **Goal:** Add Simpson's axioms 3 (`¬◇⊥`), 4 (`◇(A∨B) ⊃ (◇A ∨ ◇B)`), 5 (`(◇A ⊃ □B) ⊃ □(A ⊃ B)`) as
  constructors of `IKAx`.
- **Tasks:**
  - [x] Add `diaBot`, `diaOr`, `fs` as unconditional `IKAx` constructors
  - [x] Verify sorry-free; `#print axioms` unchanged on `NIK_to_NIKAx`/`TClosure.hilbertTransport`
- **Timing:** one small dispatch (spent)
- **Depends on:** none
- **Outcome:** `probes/lemma612-scaffold.lean`. **Preserved unchanged** — still required by leg B.
- **Completed:** 2026-07-15T13:17:58-07:00 (commit `2bd1e3a6`)

### Phase 2: Track A2 — Route probe: is `FS` derivable in CSLib's CS5? [COMPLETED]
- **Goal:** Attempt a sorry-free derivation of `FS := (◇ϕ → □ψ) → □(ϕ → ψ)` in CSLib `CS5`.
- **Tasks:**
  - [x] Attempt syntactic `Derivable CS5ModalAxiom FS` — **left open, precisely diagnosed**
  - [x] Mechanize the obstruction (`fs_context_relative_half`)
  - [x] Prove the semantic counterpart `CKValidFC cs5FC'' FS` (`fs_sound''`, axiom-free)
- **Timing:** one dispatch (spent)
- **Depends on:** none
- **Outcome:** `probes/fischer-servi-probe.lean:132-144`. **Reassessed upward by the team research**:
  `fs_sound''` is now the load-bearing input to Phases 16 and 19, and the open syntactic question is
  the task's **single largest failure term** — not the red herring Phase 3 called it.
- **Completed:** 2026-07-15T13:17:58-07:00 (commit `2bd1e3a6`)

### Phase 3: Track A3 — Route verdict [COMPLETED — VERDICT RETRACTED]
- **Goal:** Issue a GO/NO-GO on Track B with a named blocking obligation.
- **Tasks:**
  - [x] Check `cs5FC''` vs IS5 birelational semantics — **finding (i) SURVIVES**
  - [x] Check Pacheco's `CKB ≡ IKB ⟹ CS5 ≡ IS5` chain — **finding (ii) RETRACTED**
  - [x] Record verdict
- **Timing:** one dispatch (spent)
- **Depends on:** 2
- **The dispatch ran and its status stays [COMPLETED]. Its verdict is RETRACTED**, on three
  independent grounds from the team research (Conflict 4), all of which agree:
  - **Transcription error (C's A2, verified)**: A3 wrote Pacheco's `∼c := Γ ⊆ ∆ ∧ ∆ ⊆ Γ♦`;
    `CS5.lean:583` has `Γ□ ⊆ ∆`. The `□` superscript was dropped by PDF extraction. A3's version
    **cannot be right**: `Γ ⊆ ∆ ⟹ ∆ ⊆ Γ` is false, so `∼c` could not be symmetric — contradicting
    Pacheco's own Lemma 15. The dropped `□` is **load-bearing for the NO-GO**.
  - **Proves too much (B's reductio)**: `cs5FC''` conjunct 3 *is* plain symmetry, so Track C's
    countermodel also lands in `cs5Tail`-shape. A criterion that closes B on that basis closes C too.
  - **Inert, not violated (A's KF2)**: the gap lemma is *true* of Simpson's construction; its
    hypothesis is not preserved under context extension, so it never fires at the witness.
- **Finding (i) survives and is retained**: `cs5FC''` DOES coincide with IS5's birelational
  semantics (Simpson Thm 3.3.4, `chunk_0068`). Independently re-validated by A's KF3.
- **Consequence:** Phases 4-6 move `[BLOCKED]` → `[NOT STARTED]`. **Retracting this is mandatory
  independent of whether anyone ever runs Track B** — left standing, the rationale self-refutes the
  recommended route before it starts.
- **Completed:** 2026-07-15T13:34:05-07:00 (commit `cc7edf4c`); **Verdict retracted:** 2026-07-15

### Phase 4: Probe B′ — Pacheco Lemma 18 joint Zorn / the ∆-primality crux [IN PROGRESS]
- **Goal:** OPTIONAL, off the critical path. Mechanize Pacheco's Lemma 18 joint Zorn over **pairs**,
  isolating the true crux: **∆-primality under the antitone `∆□ ⊆ Σ` cap**. Decisive either way — if
  it lands, CS5 completeness follows over plain theories; if it provably fails, the task's diffuse
  obstruction becomes a single mechanized negative lemma.
- **Tasks:**
  - [ ] State Lemma 18's joint Zorn over pairs `(Σ, ∆)`; record the `∆□ ⊆ Σ` cap explicitly
  - [ ] Attempt the ∆-primality half; on failure, mechanize the obstruction as a negative lemma
  - [ ] Verify sorry-free in `probes/`; `#print axioms`
- **Timing:** ~150-250 lines, one dispatch. **~35%.** Do not open before Phase 19 resolves GO.
- **Depends on:** 19, 20
- **Un-blocked:** 2026-07-15 — Phase 3's NO-GO rationale retracted (see Phase 3). **Reopened as a
  probe, NOT as the route.** Pacheco's Lemma 16 step `φ ∉ Θ ⟹ ¬φ ∈ Θ` is **invalid** on two
  independent grounds (one property-based and OCR-immune: if sound, `Θ` would be negation-complete,
  hence classical, collapsing `⊑c` and proving CKB classical). Lemma 18 defers to Lemma 16. So this
  route is **holed at precisely the step this entire task keeps failing on**.
- **Guardrails:** if attempted, it operates over plain theories and **will** meet
  `cs5Incest_forces_symm` — that is the expected outcome and is exactly why it is a probe, not the
  route. A negative result here is a **deliverable**, not a failure.
- **Risk:** MED — expected to fail; valuable either way.

### Phase 5: Track B2 — Derive CS5 ≡ IS5 [NOT STARTED]
- **Goal:** OPTIONAL. Derive `CS5 ≡ IS5` (Pacheco corollary), gated on Phase 4 landing.
- **Tasks:**
  - [ ] Not opened unless Phase 4's ∆-primality half lands sorry-free
- **Timing:** not budgeted
- **Depends on:** 4
- **Un-blocked:** 2026-07-15 — transitively, via Phase 3's retraction. Off the critical path.
- **Risk:** HIGH

### Phase 6: Track B3 — Mechanize the IS5 canonical model (Simpson Thm 3.3.4) [NOT STARTED]
- **Goal:** OPTIONAL, lowest priority. Mechanize Thm 3.3.4's canonical birelation model.
- **Tasks:**
  - [ ] Not opened unless Phase 5 lands AND `FischerServi1984` is ingested
- **Timing:** not budgeted
- **Depends on:** 5
- **Un-blocked:** 2026-07-15 — transitively. **`FischerServi1984` is DEPRIORITIZED, not blocking**
  (Conflict 1): under the recommended route the Ch.3 shortcut is abandoned, so FS1984's role as its
  authority is **moot**. It is now a **shortcut-finder, not a blocker**. Further deflation: FS1984 is
  a 1984 axiomatization paper for IK, not CK/CS5; even a genuine IS5 birelational completeness proof
  there would be for a **different frame class** than `cs5FC''` and would not be mechanization-ready.
  **Residual risk (stated, not hidden)**: if leg A proves intractable and this shortcut is revisited,
  FS1984 becomes blocking again and no report may claim that route without it.
- **Risk:** HIGH

### Phase 7: Track C1 — `Tele`/`Conj` over `List (Proposition)` [COMPLETED]
- **Goal:** Define `Tele`/`Conj` (Simpson p.104); port `Star_imp1`/`Star_imp2` to `Tele`-congruence.
- **Tasks:**
  - [x] Define `Conj`/`Tele`; port to `Tele_imp1`/`Tele_imp2`; verify sorry-free
- **Timing:** one dispatch (spent)
- **Depends on:** none
- **Outcome:** `probes/track-c-c1-tele-conj.lean`. Generalized: all combinators parametric over any
  `Axioms : Proposition Atom → Prop`. **Preserved; keeps full value under the reordering.**
- **Completed:** 2026-07-15T13:34:05-07:00 (commit `cc7edf4c`)

### Phase 8: Track C2 — Simpson formula (6.7) [COMPLETED]
- **Goal:** Prove (6.7): `◇Conj(V) ⊃ □Tele(V,◇A) ⊃ ◇Conj(V++[A])`.
- **Tasks:**
  - [x] Sanity-check the schema; prove by induction on V; verify sorry-free
- **Timing:** one dispatch (spent)
- **Depends on:** 7
- **Outcome:** **Scoping correction, load-bearing**: stated for *nonempty* `V = p :: rest`. The
  literal `V = []` instance (`◇⊤ ⊃ □◇A ⊃ ◇A`) is refuted by a 3-world countermodel — consistent with
  Simpson's own usage. **Preserved.** This is the discipline the standing rule generalizes.
- **Completed:** 2026-07-15T13:48:57-07:00 (commit `60517582`)

### Phase 9: Track C3 — Simpson formula (6.8) [COMPLETED]
- **Goal:** Prove (6.8): `(◇Conj(W) ⊃ □Tele(W,B)) ⊃ □Tele(W,B)`.
- **Tasks:**
  - [x] Countermodel-check the `W = []` base case; prove by induction on W; verify sorry-free
- **Timing:** one dispatch (spent)
- **Depends on:** 1, 7
- **Outcome:** `formula_6_8` holds for **all** `W` including `[]` — **no restatement needed**, unlike
  C2. New `derivable_imp_trans` combinator, reusable by Phase 13. **Preserved.**
- **Completed:** 2026-07-15T14:12:51-07:00 (commit `1dc32d7d`)

### Phase 10: Track C4 — `LTree`/`star`/`fullSubtree`/`prune` + the unfolding identity [COMPLETED]
- **Goal:** Define `LTree`, `star`, `fullSubtree`, `prune`; prove the unfolding identity; delete the
  defective `pathTo`/`pathToList`/`Star_append`.
- **Tasks:**
  - [x] Fix `star` (double-`bigAnd` → single concatenated `bigAnd`); add `prune`/`fullSubtree`
  - [x] Prove the unfolding identity as a two-way IK-derivable implication (NOT raw `Eq`)
  - [x] Delete `pathTo`/`pathToList`/`Star_append`; reproduce Simpson's worked example
- **Timing:** one dispatch (spent)
- **Depends on:** 1
- **Outcome:** `probes/lemma612-scaffold.lean`. **Preserved.** `prune`/`fullSubtree` split children
  as `pre ++ [c]` (continuation child last, matching `addChild`) — forward-compatible with Phase 11.
- **Completed:** 2026-07-15T14:46:33-07:00 (commit `88d02e04`)

### Phase 11: Track C5-statement — define `pathSpine`, STATE the commutation lemma, small-model check [NOT STARTED]
- **Goal:** **REPLACES plan 02's Phase 11.** Produce a `pathSpine` *definition* and a *statement* of
  the `addChild`/`pathSpine` commutation lemma, validated by a small-model check on trees of depth
  ≤ 3. **NO proof attempt in this phase.**
- **Why plan 02's Phase 11 must NOT be dispatched as specified** (Decision 7, mandatory):
  1. **`pathSpine` does not exist.** Verified this dispatch: 3 repo-wide occurrences
     (`lemma612-scaffold.lean:364,375,760`), **all forward references in comments, zero
     definitions**. C5 has **no statement, hence no truth value** — "prove the commutation lemma" is
     not a dispatchable target, and the critic correctly declined to analyze it.
  2. **It is the wrong half first.** C5 is leg B (the bridge); leg A is the thing being bridged and
     is unplanned. Spending the crux dispatch on the bridge risks **a bridge to nowhere**.
  3. **Two items outrank it and can invalidate the track**: Phase 19 (`CS5 ⊢ FS`, ~25% the target is
     false) and Phase 3's retraction (an unsound rationale that closes the recommended route).
  4. **Base rate**: two transcribed schemas have already proved false as literally stated (C2's
     `V=[]`, C4's `star`). **Statement-first + countermodel-first is the only discipline that has
     been catching these.**
- **Tasks:**
  - [ ] Define `pathSpine`: the whole-path recursion with pruning **built in**, returning the
        `pre`-lists that C4's `prune`/`fullSubtree` consume at each level
  - [ ] Verify the `pre ++ [c]` convention against how the target label is actually reached — **do
        NOT assume WLOG the continuation child is always the last-appended one**; if the tree has
        multiple interior branch points, `pathSpine` must identify per node which child continues
  - [ ] **STATE** the `addChild`/`pathSpine` commutation lemma
  - [ ] **Small-model check** the statement on trees of depth ≤ 3 BEFORE any proof attempt; if it
        fails, restate and document the countermodel (as C2 did)
  - [ ] Land the definition + statement sorry-free (`sorry` on the lemma body is permitted **here
        only**, in `probes/`, since this phase's deliverable is the statement)
- **Timing:** one dispatch, statement-only
- **Depends on:** 10, 19
- **Reuses:** `prune`/`fullSubtree`/`star_unfold_imp1`/`star_unfold_imp2` (Phase 10); `addChild`'s
  `node l (cs ++ [leaf y])` append convention
- **Risk:** MED — bounded by construction (no open-ended proof search).

### Phase 12: Track C6 — `LTree.toGraph` + τ-parameterized induction [NOT STARTED]
- **Goal:** Define `LTree.toGraph`; prove the τ-parameterized generalized induction; discharge the
  non-modal cases plus (□I)/(□E)/(◇I).
- **Tasks:**
  - [ ] Define `LTree.toGraph`; set up the τ-parameterized generalized induction
  - [ ] Discharge non-modal + (□I)/(□E)/(◇I) cases, sorry-free
- **Timing:** one dispatch
- **Depends on:** 10, 25
- **Reordered:** behind leg A (Phases 20-23). Unchanged in content from plan 02.
- **Risk:** MED

### Phase 13: Track C7 — the (◇E) case [NOT STARTED]
- **Goal:** Discharge the (◇E) case via report 02 §2.5's reconstructed 3-step argument.
- **Tasks:**
  - [ ] Reconstruct the 3-step argument (reuse `derivable_imp_trans` from Phase 9)
  - [ ] Discharge (◇E), sorry-free
- **Timing:** one dispatch
- **Depends on:** 12, 25
- **Risk:** MED

### Phase 14: Track C8 — the (⊥E)/(∨E) cases [NOT STARTED]
- **Goal:** Discharge the (⊥E) and (∨E) cases (label-local in this encoding).
- **Tasks:**
  - [ ] Discharge (⊥E) and (∨E), sorry-free
- **Timing:** one dispatch
- **Depends on:** 12
- **Risk:** LOW

### Phase 15: `cs5_completeness` assembly [NOT STARTED]
- **Goal:** Land `cs5_completeness` / `cs5_soundness_completeness` sorry-free and axiom-clean by
  composing leg B (Ch.6 adequacy, Phases 7-14, 25), leg A (Ch.5 canonical model, Phases 21-23), and
  leg C (§8.1.1 `B_K`, Phase 24).
- **Tasks:**
  - [ ] Compose Thm 6.2.1 (leg B) ∘ Thm 5.2.1 (leg A) ∘ Lemma 8.1.2 + `B_K ⊨ cs5FC''` (leg C)
  - [ ] Prove `cs5_completeness : CKValidFC cs5FC'' φ → Derivable CS5ModalAxiom φ`, sorry-free, no
        new axioms under `Cslib/`
  - [ ] Prove `cs5_soundness_completeness` (soundness half is **landed**: task 512's
        `cs5_axiom_sound_incest`/`cs5_soundness_incest`)
  - [ ] Full CI gate (see Testing & Validation)
- **Timing:** one or more dispatches
- **Depends on:** 12, 13, 14, 24
- **Risk:** HIGH — inherits every leg's risk. **~10% overall.**

### Phase 16: Mechanize `cs5_completeness ⟹ CS5 ⊢ FS` [COMPLETED]
- **Goal:** **~2 lines, CANNOT FAIL.** Convert the entailment from an argument into a **landed
  theorem**, making the necessary condition undeniable whichever way `CS5 ⊢ FS` later resolves.
- **Why**: `fs_sound''` (landed, sorry-free) proves `cs5FC'' ⊨ FS`. Instantiate the target at
  `φ := FS`; the hypothesis discharges; therefore **`cs5_completeness ⟹ CS5 ⊢ FS`**. Contrapositive:
  `CS5 ⊬ FS ⟹ the target is false`. Plan 02:173's "orthogonal … red herring" is **refuted**.
- **Tasks:**
  - [x] State `cs5_completeness` as a **hypothesis** (do not assume it as an axiom)
  - [x] Instantiate at `φ := FS`; discharge via the landed `fs_sound''`
  - [x] Verify sorry-free; `#print axioms` — footprint must not exceed
        `[propext, Classical.choice, Quot.sound]` (result: depends on **no** axioms at all)
- **Timing:** minutes; bundle with Phase 17 or 18 if convenient
- **Depends on:** none
- **Reuses:** `fs_sound''` (`probes/fischer-servi-probe.lean:132-144`)
- **Guardrails:** touches no canonical model; trips nothing.
- **Risk:** NONE — this is why it goes first.

### Phase 17: Probe `B_K ⊨ cs5FC''` abstractly [COMPLETED]
- **Goal:** **~50-100 lines, DECISIVE.** Confirm A's KF3 by machine: `B_K` satisfies all five
  `cs5FC''` conjuncts plus `cs5Incest`, and does **NOT** satisfy the stronger `cs5FC`.
- **Why now**: statable **abstractly over an arbitrary IL-model `K`** — it does **not** need the
  canonical model, so it is available immediately. Moves A's ~85% hand-check to **settled**, confirms
  the target's frame class, and independently re-validates task 509's `cs5FC''` pivot.
- **Why the two probes interlock (the strongest reason to run both)**: `fs_sound''` gives
  `cs5FC'' ⊨ FS`. If this phase confirms `B_K ⊨ cs5FC''`, then **the route's own countermodel
  construction validates `FS`** — so the route **cannot** produce a countermodel for `FS`, and
  therefore cannot prove completeness **unless `CS5 ⊢ FS`**. Together, Phases 16+17 convert the
  obligation from a necessary condition of the *theorem* into a necessary condition of the *method*.
- **Tasks:**
  - [x] Define `B_K` abstractly (`chunk_0152:3`): `W′ = {(w,d) | w ∈ W, d ∈ D_w}`;
        `(w,d) ≤′ (w′,d′) iff w ≤ w′ ∧ d = d′`; `(w,d) R′ (w′,d′) iff w = w′ ∧ R_w(d,d′)`
  - [x] Prove all five `cs5FC''` conjuncts + `cs5Incest`, sorry-free, given `R_w` refl/symm/trans and
        `≤`-monotonicity `R_w ⊆ R_{w″}`
  - [x] **Confirm `cs5FC` FAILS** (its `≤`-composed transitivity needs cross-context edges `R′`
        cannot supply) — mechanize the obstruction, do not merely assert it
  - [x] Verify sorry-free; `#print axioms` (abstract results: **no axioms**; witness: `[propext]`)
- **Timing:** one dispatch
- **Depends on:** none
- **Reuses:** `cs5FC''`/`cs5FC`/`cs5FCIncest` (`CKExtension.lean:159,184`), `CKForces`, `Preorder`
- **Guardrails:** this phase **is** the guardrail argument, mechanized. It establishes that `B_K`'s
  `R′` is a label-level, within-context relation — the exact reason `cs5Incest_forces_symm` and
  `cs5TwoSidedR_iff_cs5Tail` (both theory-to-theory) do not bind. A positive result here is the
  strongest available evidence that the guardrail analysis in this plan is correct.
- **Falsifier:** `B_K ⊭ cs5FC''` (~15%) ⟹ the §8.1.1 leg collapses; the target's frame class is
  wrong; the route needs re-derivation. **Document and stop; do not proceed to Phase 21.**
- **Risk:** LOW-MED
- **Result:** POSITIVE — falsifier did **not** fire. `B_K ⊨ cs5FC''` holds over an arbitrary
  IL-model (`BK_cs5FC''`), plus `cs5Incest`/`cs5FCIncest`; `cs5FC` provably FAILS
  (`BK_not_cs5FC`), with a concrete witness (`BKWitness_not_cs5FC`) making the separation
  non-vacuous. `Rdom` proved unnecessary. Artifact: `probes/bounded-context-bk-probe.lean`.

### Phase 18: Make the landed framework honest — remove the only corner cut in `Cslib/` [COMPLETED]
- **Goal:** **~2-4h, NON-OPTIONAL, required regardless of every other decision.** Per the user's
  directive, the only corner currently cut in this entire effort is **already in `Cslib/`** and is
  shipped via the root import. Fixing it is not a trade-off; it is an obligation.
- **Tasks:**
  - [x] **Fix `TS5`** (defect 1, HIGH): `Context.lean:247` is
        `def TS5 : Set GeomAxiom := {GeomAxiom.T, GeomAxiom.Five}` (verified). Under Simpson's
        `Ax(-)` (Fig 3-7/6-3), `Ax({χ_T,χ_5}) = IKT5`, but `CS5ModalAxiom = IKTB4`. Bridging would
        need an **unproved constructive `IKT5 ⟺ IKTB4`** on the critical path — exactly the corner
        the directive forbids. Change to `{GeomAxiom.T, GeomAxiom.B, GeomAxiom.Four}`, making
        `Ax(TS5) = CS5ModalAxiom` **definitional**. Downstream is *simplified*:
        `equivalence_of_refl_eucl` (`:260`) currently derives symm/trans from refl+eucl; under
        `{T,B,Four}` they are **direct** (`.B`/`.Four` are literally symm/trans per
        `GeomAxiom.Holds`, `Deduction.lean:126-127`), and `TClosure` already carries
        `.symm`/`.trans` constructors.
  - [x] **Delete `GeomAxiom.D`** (defect 3, HIGH): `Deduction.lean:124` (`| .D => ∀ x, ∃ y, R x y`)
        is the **sole existential** axiom; `TClosure`/`GeomWitnessClosure` silently ignore it, making
        `Context {χ_D}` a **wrong definition**. Blast radius verified: 3 sites (`Deduction.lean:124`
        + `lemma612-scaffold.lean:119` + `adequacy-gate-probe.lean:92`).
  - [x] **Delete `GeomWitnessClosure`** (defect 2, HIGH): `Context.lean:138` is
        `def GeomWitnessClosure (𝒯) (G) : Prop := True` with `geomWitnessClosure_holds := trivial`
        (`:144`) and a `Context` field at `:167` (all verified). A `def Foo := True` is
        rule-prohibited and **no CI gate catches it** (it is not a `sorry`). Delete the def, the
        theorem, and the field. With `.D` gone, clause 3 becomes **absent by construction**, not
        vacuous by stipulation — **structurally more rigorous** than the stub.
  - [x] **Correct the docstring rationale**: `Context.lean:130-138` says the clause is *"vacuous
        under the present `Label` type"* — **wrong on its own terms**; the real reason is *"no
        existential geometric axioms in the type"*. Moot once deleted, but do not repeat the error.
  - [x] Update docstrings referencing plan 01's superseded Phases 5/6 (defect 10)
  - [x] Reverify all untouched declarations compile; **no regression** of landed CK/CT/CS4/CS5
        soundness or task-509 `cs5FC''`
  - [x] Zero `sorry`, zero new axioms under `Cslib/`
- **Timing:** one dispatch (~2-4h)
- **Depends on:** none
- **Territory:** the ONLY phase in this plan that edits `Cslib/`, and only under `Labelled/`. All
  other phases are confined to `probes/`.
- **Requirement-3 note (adjudicated at source, Conflict 7)**: the deletion is **correct** and is not
  a corner-cut. Requirement 3 exists **solely** to justify **witness variables**, which
  quantifier-free axioms do not have. Decisive argument from Simpson's *structure*: `TPrime`'s own
  definition reads *"A context (G,Γ) is 𝒯-prime if **G is a classical model of 𝒯** and …"*, and
  Lemma 5.3.1's proof **opens by proving** `H` is a classical model of `𝒯` via a maximality
  argument. **If requirement 3 already asserted graph closure, that entire step would be a one-line
  citation of clause 3.** Simpson does not do that.
- **Risk:** LOW-MED — mechanical, but it touches mainline.
- **Result:** POSITIVE — all four defects fixed; landed as commit `148ef71d`. Every plan-cited
  line number verified correct before editing, and the `.D` blast radius was **exactly** the 3
  predicted sites. Notes for downstream phases:
  - **`TS5 = {T, B, Four}` is `rfl`-true** (verified by `example : TS5 = {…} := rfl`), so
    `Ax(TS5) = CS5ModalAxiom` is definitional as intended. `equivalence_of_classicalModel_TS5`
    now depends on **no axioms at all** (was routed through `equivalence_of_refl_eucl`), its
    three fields being direct projections of clause 0. `equivalence_of_refl_eucl` is **retained**
    (still true, still useful) as the record that the `{χ_T, χ_5}` presentation agrees;
    `Five_mem_TS5` is **gone** (`Five ∉ TS5` now) — any phase citing it must switch to
    `B_mem_TS5`/`Four_mem_TS5`.
  - **`GeomAxiom` now has exactly `{T, B, Four, Five}`** (verified by exhaustive `cases`).
    Because `GeomAxiom.Holds` matches exhaustively, adding an existential axiom later *forces* a
    decision at that match and at `TClosure` — the wrong-definition failure mode is now
    unrepresentable rather than merely absent.
  - **`Context`'s `𝒯` parameter is now formally unused** (no field mentions it once clause 3 is
    gone). It is **retained as an index**, documented as such: `TPrime extends Context 𝒯 Atom` is
    genuinely 𝒯-relative, and `Context.le`/the Zorn poset thread a fixed `𝒯`. `lake lint`'s
    `unusedArguments` does **not** flag it. Removing the index would be a separate refactor,
    deliberately out of this phase's scope.
  - **Scope note (beyond the four defects, same rule-compliance intent):** defect 10's docstring
    sweep also removed task-number citations from `Syntax.lean`/`Deduction.lean`/`Context.lean`,
    which `.claude/rules/no-task-references-in-deliverables.md` forbids outside `specs/**`, and
    corrected two now-stale claims the defect-1 fix invalidated (`Syntax.lean`'s "target frame
    theory is `𝒯_S5 := {χ_T, χ_5}`" and `Deduction.lean`'s "Discrepancy with the orchestrator
    dispatch" section). `Syntax.lean` was touched for this reason only — no semantic change.
  - **Verification:** full `lake build` green; `lake test` green; `checkInitImports`, `lint-style`,
    `shake`, `mk_all` all clean; **0 `sorry` / 0 vacuous defs / 0 axiom declarations under
    `Labelled/`**; landed assets (`cs5Incest`, `cs5FCIncest`, `cs5Incest_forces_symm`,
    `cs5FC''_cs5Mreach`) intact with footprint ⊆ `[propext, Classical.choice, Quot.sound]`.
  - **Pre-existing, NOT introduced here** (left untouched, outside territory): 129 `sorry`s under
    `Cslib/` in unrelated subtrees (Bimodal/Propositional/Temporal), one `lake lint`
    `unusedArguments` error at `Foundations/Logic/Metalogic/PrimeExclusion.lean:324`, and
    `Computability/URM/Basic.lean:92`'s `:= trivial` (a real goal, not a vacuous stub).

### Phase 19: DECISION GATE — decide `CS5 ⊢ FS` [COMPLETED]

> **VERDICT: DERIVED.** `CS5 ⊢ FS` is **TRUE**, mechanized sorry-free as `cs5_fs` in
> `probes/fs-derivation-gate.lean`, footprint `[propext, Classical.choice]`. Decided in ONE
> dispatch, within the cap. **Branch taken: proceed to Phase 20 → 21.** The `~25%` "target is
> FALSE" risk term — the single largest term in this task's failure probability — is
> **eliminated, not deferred**. Phase 16's `cs5_completeness ⟹ CS5 ⊢ FS` necessary condition is
> **discharged**. Do NOT re-open this gate. This also unblocks task 512's diagnosis.
>
> **How it was decided — the untried direction paid off, in the opposite direction.** The
> dispatch prioritized refutation as instructed. Characterizing the algebra class any
> countermodel must inhabit *proved no countermodel exists*, and the impossibility argument
> transcribed directly into the Hilbert derivation:
> - `k`/`kdia` + necessitation ⟹ `□`, `◇` monotone.
> - **`bBox` + `bDia` are exactly the unit/counit of an adjunction `◇ ⊣ □`** — the structural
>   fact the earlier negative probe missed. With `T`/`4`, `◇` is a closure and `□` an interior
>   operator with `Fix(◇) = Fix(□) =: J`; `◇` reflects and `□` coreflects onto `J`.
> - `k` is then automatic; the sole remaining constraint `kdia` **⟺ Frobenius**
>   `◇(u ∧ x) = u ∧ ◇x` for `u ∈ J`.
> - Hence in **every** CS5 algebra, with `C := ◇A → □B`:
>   `◇C ∧ A ≤ ◇C ∧ ◇A = ◇(◇A ∧ C) ≤ ◇□B = □B ≤ B`, which by the adjunction *is* `C ≤ □(A → B)`.
>   So `FS` is valid in every CS5 algebra; by Lindenbaum completeness, `CS5 ⊢ FS`.
>
> **A landed prior conclusion is refuted (recorded, not buried).** `probes/fischer-servi-probe.lean`
> recorded a NEGATIVE syntactic verdict, self-described as *"not a search failure ... a structural
> mismatch"*, on the ground that *"every route to `A → B` from the hypothesis `H : ◇A → □B`
> genuinely needs `H` in context, so the resulting `A → B` is never closed and `necessitation` is
> inapplicable."* **That diagnosis is wrong.** It holds only for routes keeping `H` as a *context
> hypothesis*. The derivation treats `C := ◇A → □B` as a **formula**, proves the **closed**
> theorem `⊢ ◇C → (A → B)`, necessitates *that* (legal — empty context), and re-attaches the
> hypothesis via `bBox`'s `C → □◇C`. The landed `fs_context_relative_half` obstruction is
> **circumvented, not contradicted** — it blocks the context-relative route; this is not that
> route. `fischer-servi-probe.lean`'s stale NEGATIVE verdict should be corrected when that file
> is next touched (its `fs_sound''` remains valid and is untouched).
>
> **Axiom usage:** `implyK`, `implyS`, `andI`, `andE1`, `andE2`, `k`, `kdia`, `tDia`, `fourDia`,
> `bBox`, `bDia`. Notably **`tBox`, `fourBox`, `efq`, `orI`/`orE` are unused** — `FS` already
> holds in `CK + tDia + fourDia + B`, a strictly weaker system than CS5.
>
> **Not done (deliberately, per the constraint "work in `probes/` ONLY"):** `cs5_fs` is not yet
> transcribed into `Cslib/`. That is a mainline-landing step for a later phase.

- **Goal:** **Resolve the named blocking obligation.** This is a **decision gate, not a phase to
  grind on**: it is bounded, and each outcome has a documented branch taken without further debate.
- **Why**: Phase 16 makes `cs5_completeness ⟹ CS5 ⊢ FS` a landed theorem. **~25% the target is
  FALSE** — the single largest term in the task's failure probability. **Every dispatch to date has
  attacked derivation and failed; nobody has attempted refutation. The untried direction is where the
  information is.**
- **Tasks:**
  - [x] **Prioritize the UNTRIED direction**: attempted a `CS5`-**countermodel** refuting `FS`.
        **Outcome: no countermodel exists, and proving that produced the derivation.** The
        algebraic characterization (adjunction `◇ ⊣ □` from `bBox`/`bDia`; `kdia` ⟺ Frobenius)
        shows every CS5 algebra validates `FS`.
  - [x] **Bounded**: closed in ONE dispatch, within the cap. No second dispatch opened.
  - [x] Secondary syntactic attempt: **succeeded** — `cs5_fs`, sorry-free, in
        `probes/fs-derivation-gate.lean`. The `fs_context_relative_half` obstruction is
        circumvented by internalizing the hypothesis as `◇C` via `bBox` instead of holding it in
        context, so `necessitation`'s empty-context requirement is met by the closed theorem
        `⊢ ◇C → (A → B)`.
  - [x] Verdict recorded and branch taken, in writing: **DERIVED → proceed to Phase 20 → 21.**
- **Timing:** ONE dispatch, hard cap
- **Depends on:** 16, 17, 18
- **Documented branches (decide now, not later)**:

  | Outcome | P | Branch — taken without further debate |
  |---|---|---|
  | **REFUTED** (countermodel found) | ~25% | **The target is FALSE.** Do NOT open Phases 21-25. Move task 517 to blocked status. Land the countermodel as a **mechanized negative lemma** — a real deliverable. Restate the target honestly; terminate 509/512/517 as scoped. Bank Phase 18's honesty fixes and the landed framework. |
  | **DERIVED** (`CS5 ⊢ FS` sorry-free) | ~25% | **The task is alive and the largest risk term is gone.** Proceed to Phase 20 → 21. Also unblocks task 512's diagnosis. |
  | **UNDECIDED** (neither closes within the cap) | ~50% | **Proceed to Phase 20 → 21 anyway, with the risk explicitly priced at ~25% and re-stated in every subsequent handoff.** Leg A (Phases 21-23) **does not depend on the target being true** and is ~50% on its own — that asymmetry is what makes proceeding under uncertainty rational. Do **not** re-open this gate; re-attempt only if leg A lands and Phase 15 is the last obstacle. |

- **Evidence currently pointing toward `CS5 ⊢ FS` (independent of Pacheco's holed chain)**:
  `cs5_dia_or` (`CS5 ⊢ ◇(A∨B) → ◇A ∨ ◇B`, = `k3`) is **landed and mechanized** in CSLib;
  `ArisakaDasStrassburger2015` gives `B ⊢ k3, k5`; `cs5FC'' ⊨ FS` is mechanized. **Pacheco's chain
  contributes ~nothing** once its Lemma 16 hole is priced in (defect 4).
- **Guardrails:** a countermodel here concerns the CS5 **Hilbert system**, not any canonical model;
  it trips no guardrail.
- **Risk:** the gate itself cannot fail — it always returns one of three branches.

### Phase 20: Pre-gate — confirm `TClosure` supports the `(R_Υ)` internalization [COMPLETED]
- **Goal:** **Cheap paper/probe pre-gate before Phase 21 is dispatched.** Confirm that `TClosure`
  supports the `(R_Υ)` internalization the maximality argument needs to discharge `clModel`.
- **Why**: `clModel` (*"G is a classical model of 𝒯"*) is a **field** of `TPrime` that Lemma 5.3.1
  must **discharge**, and the only mechanism is **maximality + (R_Υ)** — which is **unlanded,
  unchecked, and is leg A's first real obstacle**. This is C's Phase-5 gate, **with the mechanism
  corrected** (Conflict 7: the obligation is *not* to implement requirement 3, which is correctly
  absent).
- **The mechanism to confirm** (`chunk_0102`, read in full by the synthesis): for a quantifier-free
  axiom, `m = 1`, `ȳ` empty, `H₁ = H ∪ {R₁₁[z̄/x̄]}`. Simpson: *"it cannot be the case that
  Δ ⊢_{H₁} x:A … because if it were then Δ ⊢_H x:A would be derivable by an application of (R_Υ).
  Therefore … (H_i, Δ) is in C. Whence, by the maximality of (H,Δ), we have that H_i = H."*
  **`H₁ = H` means `R₁₁[z̄/x̄] ∈ H` — which is exactly the goal.**
- **CAUTION (the strongest instance of the systemic finding)**: `chunk_0102` reads *"Define:"*
  followed by **nothing** — the OCR **dropped the definition of `H_i`**. This is the one place two
  teammates flatly contradicted each other. **Read `H_i`'s definition from PDF layout, not chunk
  text.** The standing rule binds here more than anywhere else in the plan.
- **Tasks:**
  - [x] Read Simpson Lemma 5.3.1's `H_i` definition **from PDF layout** (`chunk_0102`'s text is
        known-defective)
  - [x] Confirm `TClosure` (`Deduction.lean:146-148`, carrying `.symm`/`.trans`) admits the `(R_Υ)`
        internalization for each `𝒯 = TS5 = {T, B, Four}` axiom (post-Phase-18)
  - [x] Confirm `Deriv`/`Context.le` support the maximality argument's chain closure
  - [x] Write the finding; if it does not support it, name the precise obstruction
- **FINDING (Phase 20, report 09; probe `probes/rchi-internalization-gate.lean`, sorry-free):**
  - **VERDICT: `TClosure` DOES support the `(R_Υ)` internalization. Falsifier did NOT fire.**
    Mechanized for all three `TS5` axioms via `TClosure.absorb_addEdge` + `NIK.weakenCl` +
    `NIK.geomInternalize_T/_B/_Four`. `(□E)`/`(◇I)` are the only relational-premise rules and both
    range over `TClosure 𝒯 G.R`; `NIK` never reads `G.X`. `Deriv`/`Context.le` confirmed adequate.
  - **Requirement 3: NOT load-bearing for `{T,B,Four}`.** PDF p. 91 verbatim: its "only if" subject
    is *"each of the witness variables in `v_χz̄`"*, and `v_χz̄` is the **empty vector** when `ȳ` is
    empty (p. 72 normal form). **Vacuously true ⟹ Conflict 7 CONFIRMED; Phase 18's deletion removed
    nothing leg A needs.** Do not reverse Phase 18.
  - **Transcription rule for Phases 21/23**: at a quantifier-free axiom, p. 92-93's reductio framing
    AND its requirement-3 exit are BOTH vacuous. The goal is delivered by the maximality step used
    **directly** (`H_i = H` ⟹ `R_i1[z̄/x̄] ∈ H`). Do NOT transcribe the reductio literally.
  - **NEW BLOCKER (Phase 23, NOT Phase 21): `TPrime TS5 Atom` is UNINHABITED.**
    `tPrime_TS5_false` / `IsEmpty (TPrime TS5 Atom)`, mechanized. `clModel : ClassicalModel 𝒯 G.R`
    (`Context.lean:217`) quantifies **type-wide** (`.T => ∀ x, R x x`), but PDF p. 94 makes
    `H ⊨_CL 𝒯` satisfaction **in the structure `H`**, domain = `H`'s underlying set. Chain:
    `clModel .T` + `Graph.edge_mem` ⟹ `G.X = univ`, contradicting `Context.coinfinite`.
    Root cause is **`χ_T` alone** (the only `TS5` axiom with `n = 0` premises);
    `{χ_B, χ_4}` is harmless (`classicalModel_B_Four_trivial`).
  - **Phase 21 is UNAFFECTED**: at `𝒯 = ∅` clause 0 is vacuous (`classicalModel_empty`), so the
    chain has no premise. **Plan v3's D2 `𝒯 = ∅`-first sequencing is independently vindicated.**
  - **REQUIRED before Phase 23** (~40 lines, mainline `Cslib/`): retype clause 0 to
    `ClassicalModelOn 𝒯 G.X G.R` (Simpson's domain-relative `⊨_CL`). Probe declarations
    (`GeomAxiom.HoldsOn`, `ClassicalModelOn`, `classicalModelOn_TS5_iff`) are ready to lift; the
    repair is **free at `TS5`**. Downstream: `equivalence_of_classicalModel_TS5` returns a
    type-wide `Equivalence` and must become domain-relative (or the canonical model's domain a
    subtype `↥H.X`) — flagged, not solved.
  - **DO NOT** discharge `clModel` via `ClassicalModel 𝒯 (TClosure 𝒯 R)` — it is free
    (`classicalModel_tClosure_free`) but proves clause 0 for the **closure**, whereas p. 94 fixes
    `R^𝒯_(H,Δ)(x,y)` iff `xRy` in **`H`** (raw). It would silently change the canonical model.
  - **PLAN CORRECTION — Phase 22**: its task list says `R_(H,Δ)(x,y)` iff `xRy` in `𝒯-Comp(H)`.
    **PDF p. 94 says raw `xRy in H`** ("because `(D^𝒯_(H,Δ), R^𝒯_(H,Δ)) = H`"). Correct before
    Phase 22; re-verify against pp. 95-98.
- **Timing:** one dispatch (paper + small probe)
- **Depends on:** 18 (the `TS5` fix changes which axioms `(R_Υ)` must cover)
- **Falsifier:** `TClosure` cannot support the internalization (~20%) ⟹ `clModel` undischargeable ⟹
  **leg A blocked ⟹ the whole route blocked**. Document and move to blocked status; do not grind.
- **Risk:** LOW (analysis) — but it gates a HIGH-cost phase.

### Phase 21: Leg A1 — Simpson Prime Lemma 5.3.1, at `𝒯 = ∅` (IK) first [BLOCKED]

> **[BLOCKED — Phase 21 dispatch, session `sess_1784156551_995e9d`]**
> **The deliverable is not constructible as specified: `TPrime 𝒯 Atom` is UNINHABITED for every
> `𝒯`, including `𝒯 = ∅`.** Mechanized sorry-free as `tPrime_false` /
> `instance : IsEmpty (TPrime 𝒯 Atom)` in `probes/prime-lemma-blockers.lean`. Lemma 5.3.1's whole
> job is to *produce* an inhabitant of this type, so no proof effort at any `𝒯` can succeed until
> the type is repaired. **This supersedes Phase 20's scoping**, which found the emptiness only at
> `TS5`, attributed it to `χ_T`'s quantifier range, and concluded it "lands on Phase 23, not
> Phase 21". Clause 0 *is* vacuous at `∅`; but clause 1 (`deductiveClosure`) empties the type on
> its own, independently of `𝒯`: `impI`+`assumption` derive `x : A ⊃ A` at an **arbitrary** label
> with no premises and no side conditions, and the type-wide `deductiveClosure` + `ctxSubset` then
> force `G.X = univ`, contradicting `Context.coinfinite`. The `𝒯 = ∅`-first sequencing does not
> dodge this.
>
> **Two further transcription defects found, both in `NIK`, both read from the p. 69 page raster
> (Figure 4-1; the `pdftotext` layer for this figure is destroyed — same failure mode Phase 20
> documented for `H_i`):**
> - `(⊥E)` is printed **cross-label** (`x:⊥ / y:A`); CSLib's `NIK.efq` is label-local
>   (`x:⊥ / x:A`). Lemma 5.3.1's *"Consistency is immediate, because `Δ ⊬_H x:A`"* is exactly an
>   appeal to the cross-label form. Mechanized: `consistency_of_efqCrossLabel` (Simpson's argument
>   works given the printed rule) vs `consistency_at_excluded_label_only` (the label-local rule
>   discharges the clause **only at `y = x`**, leaving every other `y ∈ H.X` open).
> - `(∨E)` is printed **cross-label** (major premise `x:A∨B`, conclusion `y:C`); CSLib's `NIK.orE`
>   fixes both at `x`. Lemma 5.3.1's disjunction step needs the disjunction at `y` and the excluded
>   formula at `x`; under the label-local rule that application is ill-formed.
>
> All three defects — plus Phase 20's `clModel` finding — are **one root cause**: the transcription
> drops the domain-relativity / cross-label structure Simpson's Ch. 5 relies on. Repairs are stated
> and their adequacy checked in the probe; none applied (`Cslib/` out of territory).
>
> **Also flagged, NOT mechanized (MEDIUM confidence):** Simpson's chain-union step (*"It is easily
> seen that `(⋃G_i, ⋃Γ_i)` is also in `C`"*, p. 92) may not transfer to CSLib's encoding. `boxI`
> and `diaE` use **cofinite quantification** (`∀ y ∉ L`) for their eigenvariable, so a `NIK`
> derivation has *infinite branching* and no finite graph support: reconstructing a `boxI` at a
> single chain index `i` needs one `i` working for cofinitely many `y`, which directedness does not
> supply. Simpson's own derivations are finite trees, which is why he calls it "easily seen". A
> label-renaming/equivariance lemma for `NIK` (not present in `Cslib/`) would likely rescue it.
> **A successor must settle this before attempting the Zorn argument** — it is the crux, and
> Phase 20's LOW-uncertainty rating of it looks optimistic.
>
> **Nothing was attempted against the empty type**; no strategic sorries were planted. See
> `probes/prime-lemma-blockers.lean` (9 declarations, sorry-free).
- **Goal:** **THE MISSING PIECE — absent from plan 02 entirely.** Mechanize Simpson's **unbounded**
  Prime Lemma 5.3.1: if `Δ ⊬_H y:B` then there is a `𝒯`-prime context `(H′,Δ′) ⊇ (H,Δ)` with
  `Δ′ ⊬ y:B`. **At `𝒯 = ∅` (IK) first**, per D2 and **Simpson's own order** (base system, then
  geometric extension).
- **Why `𝒯 = ∅` first**: every wall in this history is **symmetry-driven**. At `𝒯 = ∅`, `TClosure`
  collapses to `base`, exercising the **whole Ch.5 pipeline with the wall removed**. This changes no
  theorem statement and is pure risk-sequencing.
- **Tasks:**
  - [ ] Transcribe Lemma 5.3.1's statement — **from PDF layout, not chunk text** (standing rule)
  - [ ] Small-model/consistency check the statement BEFORE writing Lean
  - [ ] Mechanize: ONE Zorn application over **whole contexts `(G, Γ)`** — graph and formula-set
        growing **together**, capped only by an excluded labelled formula `x:A`, with a **coinfinite
        reserve of fresh world-variables** (`chunk_0102`)
  - [ ] Discharge `TPrime`'s four conditions: consistency, deductive closure, disjunction property,
        diamond property
  - [ ] Discharge `clModel` via maximality + `(R_Υ)` (Phase 20's confirmed mechanism)
  - [ ] Verify sorry-free in `probes/`; `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`
- **Timing:** one dispatch (~300-500 lines). Split if it exceeds one agent run.
- **Depends on:** 19, 20
- **Reuses:** `TPrime` (`Context.lean:224`), `Deriv`, `Context.le`, `TClosure`, `NIK.weaken`
- **Guardrails — why this does not trip any of the four**: this is a **Zorn maximization over
  labelled contexts**, not over theories. Its output `(H′,Δ′)` is **one object**; `Th(Δ′,y)` and
  `Th(Δ′,z)` are **restrictions of it**, not independently maximized theories. Task 512's atom-sum
  results and `cs5Incest_forces_symm` constrain the **sequential, theory-to-theory** construction
  they were proved about. At `𝒯 = ∅` there is no symmetry at all, so the question is moot for this
  phase and is faced squarely in Phase 23.
- **Convergence anchor**: this **is** the *"simultaneous maximal pair, not sequentially"* that
  `CS5.lean:705-706` names as *"the real open problem"* — verified verbatim. Four teammates arrived
  here from four disjoint angles.
- **Risk:** **HIGH** — crux-grade. **~65%** for the transcription alone (B's estimate).

### Phase 22: Leg A2 — Simpson Canonical Model Lemma 5.3.2 (truth lemma), at `𝒯 = ∅` [NOT STARTED]
- **Goal:** **THE SECOND MISSING PIECE.** Mechanize the canonical model over `𝒯`-prime contexts and
  the truth lemma: `(H,Δ), y ⊩_K B ↔ y:B ∈ Δ`. Plus the disjunction property (`chunk_0103`).
- **The box case IS the escape** (`chunk_0167:5`, verbatim): *"Let z be some variable **not in H**.
  Suppose, for contradiction, that Δ ⊬^T_{H∪{yRz}} z:B. Then, by the prime lemma, there is a
  𝒯-prime context (H′,Δ′) ⊇ (H ∪ {yRz}, Δ) such that Δ′ ⊬ z:B. But then (H′,Δ′) ≥ (H,Δ), and yRz in
  H′ and z:B ∉ Δ′ … Hence, by **(□I)**, Δ ⊢^T_H y:□B."* **The prime lemma is applied to the graph
  extended with a FRESH label `H ∪ {yRz}`, producing ONE prime context by ONE maximization.** The
  eigenvariable/freshness side-condition of (□I) is what makes the head **non-fixed** — and a
  non-fixed head is precisely what `cs5_symmetric_tail_box_gap` needs and does not have.
- **Tasks:**
  - [ ] Define the IL-model `K` over `𝒯`-prime contexts (`≤` = context inclusion; `D_(H,Δ)` = `H`'s
        underlying set; `R_(H,Δ)(x,y)` iff `xRy` in `𝒯-Comp(H)`; `α_(H,Δ)(x)` iff `x:α ∈ Δ`)
  - [ ] Transcribe the IL-model satisfaction clauses **from PDF layout** (`chunk_0098`) — note the
        box clause is **`≤`-quantified**: *"w,d ⊩ □A iff for all w' ≥ w, for all d' ∈ D_{w'},
        R_{w'}(d,d') implies w',d' ⊩ A"*. **This clause is the escape; do not simplify it.**
  - [ ] Prove the truth lemma by structural induction; the **box case** via the mechanism above
  - [ ] Prove Thm 5.2.1 (3⇒1): `NIK(∅)`-completeness over IL-models
  - [ ] Verify sorry-free; `#print axioms`
- **Timing:** one dispatch (~300-500 lines). Split by induction case if it exceeds one agent run.
- **Depends on:** 21
- **Reuses:** `NIK.boxI` (`Deduction.lean:229` — **already carries the cofinite `L`/`hL : L.Finite`
  eigenvariable device**, which KF2 identifies as *the* escape mechanism), `TClosure.symm`, `TPrime`
- **Guardrails:** see the Overview table. The `≤`-quantified box clause + the fresh-label prime-lemma
  application are jointly the reason `cs5_symmetric_tail_box_gap` is **true but inert** here.
- **Risk:** **HIGH** — A calls this *"the real crux of Ch.5"*. This is the **second** crux-grade
  obligation, which is why leg A is ~50% rather than ~65%.

### Phase 23: Leg A3 — generalize leg A from `𝒯 = ∅` to `𝒯 = TS5` [NOT STARTED]
- **Goal:** Generalize Phases 21-22 to `𝒯 = TS5 = {T, B, Four}` (post-Phase-18), where `TClosure` is
  non-trivial and **symmetry enters**. This is where the guardrail analysis is actually tested.
- **Tasks:**
  - [ ] Generalize the prime lemma and truth lemma over `𝒯`, keeping them **`𝒯`-generic** (the
        payoff: one proof serves the **16-logic intuitionistic modal cube**, not CS5 alone)
  - [ ] Discharge `clModel` at `TS5` via `𝒯-Comp(H) ⊨_cl 𝒯` (Lemma 8.2.5's content in its **Ch.5
        unbounded form** — already landed as `TPrime`'s `clModel` field)
  - [ ] Discharge the truth lemma's symmetric box sub-case via the **(R_B) structural rule**
        (`chunk_0167:5`: *"if zRy in H′ then χ_B ∈ 𝒯 and the consequence is derived by way of (□E)
        and (R_B)"*) — a **graph fact**, not a theory-membership fact
  - [ ] **Explicitly re-verify** that `cs5_symmetric_tail_box_gap` remains inert at `TS5`: confirm
        the refuting witness lives at a strictly larger context where `q ∉ H` is not preserved
  - [ ] Verify sorry-free; `#print axioms`
- **Timing:** one dispatch
- **Depends on:** 18, 22
- **Guardrails:** **this phase is where the escape is cashed.** If the analysis in this plan's
  guardrail table is wrong, it fails **here** — visibly, on a specific goal, not diffusely. That is
  by design: `𝒯 = ∅` first (Phase 21-22) isolates the pipeline; `TS5` (this phase) isolates the wall.
- **Risk:** **HIGH** — the wall's actual test.

### Phase 24: Leg C — §8.1.1 `B_K` construction + Lemma 8.1.2 [NOT STARTED]
- **Goal:** Construct `B_K` over the **landed** canonical model and prove Lemma 8.1.2:
  `w,d ⊩ A ↔ (w,d) ⊩_{B_K} A`. Then instantiate Phase 17's abstract `B_K ⊨ cs5FC''` at the canonical
  `K`, yielding a birelation countermodel in the target's frame class.
- **Tasks:**
  - [ ] Instantiate `B_K` (Phase 17's abstract definition) at the canonical `K` from Phase 23
  - [ ] Prove Lemma 8.1.2 by induction (*"an easy induction"* per source)
  - [ ] Instantiate `B_K ⊨ cs5FC''` (Phase 17) at the canonical `K`
  - [ ] Verify sorry-free; `#print axioms`
- **Timing:** one dispatch
- **Depends on:** 17, 23
- **§8.1's pathologies do NOT bite (A's E7, checked)**: Section 8.1's notorious problems (Fig 8-1
  counterexample; failure of the lifting lemma) are **soundness-side only**. *"Nowhere in the proof
  of completeness have we used the assumption that G is a tree"* (`chunk_0153:3`). **517 needs only
  the completeness direction.**
- **§8.1.3's completeness caveat does NOT bite (A's E8, checked)**: *"it is not necessarily the case
  that B_K is a birelation model of 𝒯. For example … 𝒯 = {∀xy. xRy}"* — the counterexample is the
  **universal relation**, demanding cross-context edges `R′` cannot supply. `T_S5 = {χ_T,χ_B,χ_4}`
  is **not** universal: each condition is satisfied **within a single context-cluster**, which `R′`
  does supply. Simpson confirms the scope (Thm 8.1.4).
- **Risk:** LOW-MED (~80%) — A hand-checked all five conjuncts; Phase 17 settles it by machine first.

### Phase 25: Track C5-proof — prove the `addChild`/`pathSpine` commutation lemma [NOT STARTED]
- **Goal:** **REPLACES the proof half of plan 02's Phase 11.** Prove the commutation lemma Phase 11
  stated and small-model-checked. Sorry-free.
- **Why split from Phase 11**: plan 02 bundled "define `pathSpine`" + "prove the commutation lemma"
  into one dedicated dispatch against a symbol that **does not exist**. Statement-first +
  small-model-check-first is the only discipline that has caught the defects on this task (twice).
  This phase opens **only** if Phase 11's small-model check passes.
- **Tasks:**
  - [ ] Prove the commutation lemma from Phase 11's checked statement, sorry-free
  - [ ] Verify `#print axioms`; no new axioms
- **Timing:** one dedicated dispatch — **THE TRUE CRUX of leg B**; must not share a dispatch
- **Depends on:** 11
- **Risk:** **HIGH** — on failure, record the precise obstruction and invoke Rollback/Contingency.
  Do **NOT** open further open-ended tree-surgery dispatches.

### Phase 26: Paper fixes and bookkeeping [NOT STARTED]
- **Goal:** Cheap, high steering value. Paper-only; no mathematics.
- **Tasks:**
  - [ ] **Rewrite `state.json`'s `blockers` field** to match this plan (see the CONFLICT NOTICE
        above) — it currently records the retracted A3 verdict and "NEXT = C5"
  - [ ] **Break the `512 ↔ 517` cycle** (defect 8): `512: depends_on [509, 517]` and
        `517: depends_on [509, 512, 516]` is a **literal dependency cycle** — no topological order
        exists, and it **blocks 512 forever**. Remove `517` from 512's dependencies; close 512 as
        completed-with-negative-result, banking `cs5_axiom_sound_incest` + the guardrail lemmas.
  - [ ] **Reframe the task** (Conflict 6): the title `labelled_bounded_context_cs5_completeness` is a
        **misnomer** — `T_S5 ∉ Dec_ND`, and boundedness is a decidability/FMP device 517 needs
        neither of. Correct framing: *labelled **context** CS5 completeness (Simpson Ch.5 + Ch.6 +
        §8.1.1)*. Key targets are **5.3.1, 5.3.2, 6.1.2, 6.2.1-6.2.3, 8.1.1/8.1.2** — **not** 8.2.5,
        8.2.6, or a bounded prime lemma.
  - [ ] **Correct the stated escape** in `Context.lean`'s module docstring (defect 9): its
        "unbounded" rationale **inverts** the causal claim (it cites the gap lemma as the reason to
        avoid the bound; Simpson uses the bound as *part of* the escape in §8.2). The escape is the
        **`≤`-quantified box clause + simultaneous maximal pair** — **NOT** non-primality.
        `TPrime.disjunction` (`Context.lean:224-236`) and Simpson `chunk_0172` both confirm bounded
        contexts **ARE** prime, so a team designing toward weakening primality would break the `∨`
        case of the truth lemma and buy nothing.
  - [ ] **Assign an owner to each of the four bridges** (C's B4) — *an unowned bridge is the task's
        real status*
  - [ ] Add `deGrootShillitoClouston2025` to `references.bib` (arXiv:2408.00262, LICS 2025) — their
        canonical worlds are **segments `(Γ, U)` with `⊑` = head-inclusion**, which is CSLib's
        `CKSegment`, **independently arrived at by the field's leading group**. **CSLib's
        architecture is validated as state of the art.**
- **Timing:** one small dispatch; bundle with Phase 18 if convenient
- **Depends on:** none
- **Risk:** LOW

## Testing & Validation

- [ ] Every landed probe file: `lake env lean <file>` exits 0
- [ ] Zero `sorry` under `Cslib/` at every phase boundary; `probes/` audited per phase (`sorry` is
      permitted in `probes/` only, and in Phase 11's lemma body only)
- [ ] **Zero `def _ := True` (or any vacuous definition) under `Cslib/`** after Phase 18 — no CI gate
      catches this, so it is a manual checklist item at every phase boundary
- [ ] `#print axioms` on each new result: footprint ⊆ `[propext, Classical.choice, Quot.sound]`; **no
      NEW axioms** introduced (`Classical.choice` from Zorn is ambient in Mathlib and is expected in
      Phases 21-23 — it is **not** a new axiom under `Cslib/`)
- [ ] No regression of landed CK/CT/CS4/CS5 soundness or task-509 `cs5FC''` — reverify untouched
      declarations compile after each edit (**Phase 18 especially**, the only `Cslib/` edit)
- [ ] Every transcribed schema: small-model or countermodel check BEFORE writing Lean; document the
      countermodel if the literal statement is false (as C2 did)
- [ ] Every formula transcription: read from **PDF layout**, not chunk text (standing rule)
- [ ] Before any PR (Phase 15): `lake build`, `lake test`, `lake exe checkInitImports`,
      `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`
- [ ] Before any PR: `/cite`-style check that `Simpson1994`, `Pacheco2024`,
      `MarinMoralesStrassburger2021` BibKeys resolve in `references.bib` (verified by synthesis at
      `:86`, `:895`, `:962`)

## Artifacts & Outputs

- plans/08_ch5-canonical-model-fs-gate.md (this file; supersedes plans/02_decomposed-track-a-b-c.md)
- probes/lemma612-scaffold.lean (Phases 1, 10; Phase 11 extends)
- probes/fischer-servi-probe.lean (Phase 2; Phase 16 extends; Phase 19 extends)
- probes/track-c-c1-tele-conj.lean (Phases 7, 8, 9)
- probes/adequacy-gate-probe.lean (Lemma 6.2.2 hard direction)
- probes/bk-frame-probe.lean (Phase 17, new)
- probes/ch5-prime-lemma.lean (Phases 21, 23, new)
- probes/ch5-canonical-model.lean (Phases 22, new)
- Cslib/.../Labelled/{Syntax,Deduction,Context}.lean (Phase 18 edits — the only `Cslib/` territory)
- summaries/08_*-summary.md (per dispatch)
- handoffs/00_RESUME-HERE.md (single entry point; **must be rewritten to match this plan** — it
  currently records the retracted A3 verdict and "NEXT = C5")

## Rollback/Contingency

- All phases except 18 are confined to `probes/`; reverting any is a `git revert` of its scoped
  commit. **Phase 18 edits `Cslib/Labelled/` only** — reverting restores the (defective) stubs, so
  prefer forward-fixing.
- **If Phase 19 REFUTES `CS5 ⊢ FS` (~25%)**: the target is **false**. Do not open Phases 21-25. Move
  517 to blocked status with the countermodel as a **mechanized negative lemma**. Bank Phase 18 and
  the landed framework. This is a **legitimate and honest outcome**, not a failure.
- **If Phase 20's pre-gate fails (~20%)**: `clModel` is undischargeable ⟹ leg A blocked ⟹ the whole
  route blocked. Document the precise obstruction; move to blocked status. Do not grind.
- **If Phase 17 shows `B_K ⊭ cs5FC''` (~15%)**: the §8.1.1 leg collapses and the frame class is
  wrong. Stop and re-derive the route before spending Phase 21.
- **If Phase 21 or 22 (leg A's cruxes) do not close**: record the precise obstruction. Leg A is the
  task's highest-value component; a second dispatch on a *specific named goal* is justified, but do
  **not** open a third open-ended dispatch.
- **If Phase 25 (leg B's crux) does not close**: do NOT open further open-ended tree-surgery
  dispatches. Record the obstruction; move Phases 12-15, 25 to blocked status.
- **Fallback position (already secured)**: the landed labelled framework (`Syntax`/`Deduction`/
  `Context`, ~789 lines, CI-green, sorry-free) stands as an independent contribution decoupled from
  `cs5_completeness`.
- **The honest value proposition is not the ~10%**: **leg A alone (`NIK(𝒯)`-completeness, Phases
  21-23) is ~50%, is `𝒯`-generic over the 16-logic intuitionistic modal cube, and does NOT depend on
  the target being true.** If the target turns out false, **leg A survives intact as a flagship
  theorem** — and no IS5/CS5 Kripke completeness is mechanized in any proof assistant, so it would be
  a world first. That asymmetry is what drives the leg-A-first ordering.
</content>
</invoke>
