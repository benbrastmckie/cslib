# Implementation Plan v4: Task #517 — Labelled Bounded-Context CS5 Completeness, gated on repairing `TPrime` inhabitance

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Status**: [IMPLEMENTING]
- **Effort**: HIGH, HIGH uncertainty. ~1500-2500 line new framework, ~zero reuse of the
  prime-theory canonical machinery. Phase 1 (the gate) is mostly *transcription* of already-landed
  sorry-free probe scaffolds (~1-2 dispatches, LOW risk). The proof legs (Phases 3, 4, 6) are the
  HIGH-uncertainty work. Honest headline: **~10-16 dispatches remaining (~60-100 hours)**; leg A
  (`NIKX(𝒯)`-completeness via the bounded prime lemma + canonical model) is the majority and
  survives even if the final frame-class match proves harder than estimated.
- **Dependencies**: [] (former deps 509 completed, 512 abandoned, 516 abandoned — all terminal,
  none blocking; their results are provenance, retained in the task description). 517 is now the
  **sole surviving CS5-completeness route**.
- **Research Inputs**:
  - reports/10_fig41-crosslabel-verification.md (**adversarial CONFIRM** of the Figure 4-1
    cross-label defect; verdict survived three refutation attempts)
  - reports/09_rchi-internalization-pregate.md (the `(R_Υ)` internalization pre-gate; source of the
    `ClassicalModelOn` repair scaffold)
  - reports/07_team-research.md (4 teammates + synthesis; converged on Simpson Prime Lemma 5.3.1 +
    Canonical Model 5.3.2 as the missing object)
  - reports/07_teammate-{a,b,c,d}-findings.md (Simpson Ch.5/7-8; `TS5` defect; A1/A2; prior art)
  - reports/02_adequacy-alternatives-and-technique.md (framework map valid; headline superseded)
  - reports/01_labelled-bounded-context-method.md (framework map still valid; routing superseded)
  - summaries/09_prime-lemma-blockers-summary.md (**the diagnosis this plan acts on**: `TPrime`
    uninhabited for every `𝒯`; four transcription defects; one root cause)
  - probes/prime-lemma-blockers.lean (`tPrime_false`, `instIsEmptyTPrime`,
    `deductiveClosure_relativized_kills_the_chain` — the blocker + its clause-1 repair, sorry-free)
  - probes/fig41-crosslabel-gate.lean (`NIKX`, `NIKX.weaken`, `NIKX.consistency_step`,
    `NIKX.disjunction_step`, `efq_crossLabel_of_edge` — the `(⊥E)`/`(∨E)` repair, sorry-free,
    READY TO TRANSCRIBE)
  - probes/rchi-internalization-gate.lean (`GeomAxiom.HoldsOn`, `ClassicalModelOn`,
    `ClassicalModelOn.of_classicalModel`, `classicalModelOn_TS5_iff`, `tPrime_TS5_false` — the
    `clModel` repair, sorry-free, READY TO TRANSCRIBE)
  - **Prior plans preserved for history (cited as inputs)**: plans/01_labelled-framework.md (v1),
    plans/02_decomposed-track-a-b-c.md (v2), plans/08_ch5-canonical-model-fs-gate.md (v3)
- **Artifacts**: plans/11_tprime-repair-cs5-completeness.md (this file); supersedes
  plans/08_ch5-canonical-model-fs-gate.md (v3). v1-v3 retained.
- **Standards**: plan-format.md; artifact-formats.md; cslib.md; lean4.md; plan-compliance.md;
  cslib CONTRIBUTING/NOTATION/ORGANISATION.
- **Type**: cslib
- **Lean Intent**: true

## Overview

**The user has funded Route B**: the labelled / bounded-context canonical model for CS5 (== IS5)
constructive Kripke completeness. This v4 turns the "banked findings / STOP" state left by v3 into
an executable plan.

**What changed since v3, in one sentence**: the block that stopped v3 at leg A (Phases 21-23) is a
**transcription defect, not a mathematical impossibility** — the labelled framework's central type
`TPrime` is *provably uninhabited as currently transcribed* (`tPrime_false` + `instIsEmptyTPrime`,
sorry-free, at `probes/prime-lemma-blockers.lean:92,100`), so Lemma 5.3.1's job (produce a
`𝒯`-prime context) cannot succeed at any `𝒯` until the type is repaired. The diagnosis is complete,
the repair is designed, and **every repair scaffold is already landed sorry-free in `probes/`** —
`NIKX` (the cross-label `(⊥E)`/`(∨E)` system) with its `weaken` induction re-proved, `ClassicalModelOn`
(the domain-relative clause-0), and `deductiveClosure_relativized_kills_the_chain` (the domain-relative
clause-1 that breaks the emptiness chain). Plan v4 transcribes these into `Cslib/` **first**, gates on
inhabitedness, then sequences the completeness proof per Simpson Ch 5 + Ch 7-8.

**Definition of done**: `cs5_completeness : CKValidFC cs5FC'' φ → Derivable CS5ModalAxiom φ` lands
sorry-free and axiom-clean (footprint ⊆ `[propext, Classical.choice, Quot.sound]`) under `Cslib/`.

**Zero-debt invariant**: no `sorry`, no new `axiom`, no vacuous `:= True` definitions under `Cslib/`
at any phase boundary. Partial work lives in `probes/` (`sorry` permitted there only). The four
guardrail lemmas (`cs5_symmetric_tail_box_gap`, `cs5Incest_forces_symm`, `cs5TwoSidedR_iff_cs5Tail`,
the task-512 atom-sum results) must all remain true, unregressed theorems — see "Why the repaired
design does NOT trip the four guardrails" below.

**Target-falsity risk is ELIMINATED (banked, v3 Phase 19)**: `cs5_completeness` entails `CS5 ⊢ FS`,
and v3 *derived* `CS5 ⊢ FS` sorry-free (`cs5_fs`, `[propext, Classical.choice]`) — FS holds already
in `CK + tDia + fourDia + B`, strictly weaker than CS5. The ~25% "target is false" risk that
dominated v3's Risks section is gone. This is why v4 spends no phase re-litigating the target.

**Transcription discipline (standing rule, adopted plan-level)**: chunk/OCR text is admissible for
prose and structure; **every formula and inference rule must be read from the PDF page raster, or
reconstructed from a stated property**. This one rule is what surfaced all four defects this task
diagnosed. Simpson1994's text layer AND `pdftotext` both silently drop content at figures and
displayed math (Figure 4-1 renders as `%(M) %(/\El)`); only the page raster carries it. PDF page
offset is **+9** (printed p.N = PDF p.N+9). Simpson chunks live at
`/home/benjamin/Projects/Literature/simpson_1994_intuitionisticmodallogic/` (206 chunks, re-chunked;
**verify citations by content, never by chunk number**).

### Research Integration

- **summaries/09_prime-lemma-blockers-summary.md + probes/prime-lemma-blockers.lean** — integrated
  in plan v4. Supplies the core diagnosis (`TPrime` uninhabited for every `𝒯`; clause-1 type-wide
  quantifier is the `𝒯`-agnostic emptiness driver) and the clause-1 repair.
- **reports/10_fig41-crosslabel-verification.md + probes/fig41-crosslabel-gate.lean** — integrated
  in plan v4. Adversarially confirms the `(⊥E)`/`(∨E)` label-local defects are real (not OCR
  artifacts) and supplies the `NIKX` repair with `weaken` re-proved and the two Lemma-5.3.1 step
  lemmas.
- **reports/09_rchi-internalization-pregate.md + probes/rchi-internalization-gate.lean** —
  integrated in plan v4. Supplies the `clModel` repair (`ClassicalModelOn 𝒯 G.X G.R`) and confirms
  the `(R_Υ)` internalization holds at `TS5`.
- **reports/07_team-research.md (+ teammates a-d)** — integrated in plan v3, carried forward: the
  Ch.5 (5.3.1 + 5.3.2) convergence and the honesty fixes now landed as v3 Phases 16-20.
- **reports/01, 02** — integrated in plans v1, v2; framework map valid, routing superseded.

**Genuine research gap this plan flags**: the prior research reports read Simpson **Chapter 5**
(5.3.1 prime lemma, 5.3.2 canonical model). The user's Route B is framed on **Chapter 7-8** (Lemma
8.2.5 T-Comp graph completion for symmetry, Lemma 8.2.6 bounded canonical model for box-backward, a
bounded prime lemma). Chapter 5 is the *general* prime-lemma/canonical-model machinery; Chapter 7-8
is the *specialized IS5* proof Simpson actually carries out and the substrate the landed
`Context.lean`/`TPrime` transcribes (Simpson `:5941`). **The Ch 7-8 lemmas (8.2.5, 8.2.6, bounded
prime lemma) were not mined in detail by prior research.** Therefore every proof-leg phase below
(3-6) opens with a mandatory `--lit` implementation-research step against the Ch 7-8 chunks before
transcription. This is the single biggest reason implementation must run `--lit`.

### Preserved landed assets (do NOT redo — all sorry-free, axiom-clean, COMMITTED)

Mainline `Cslib/`, honest and CI-green:
- `Labelled/Syntax.lean` (~202 ln), `Labelled/Deduction.lean` (~312 ln), `Labelled/Context.lean`
  (~291 ln) — the labelled substrate. **This is what Phase 1 repairs in place** (2 constructor
  signatures + 2 clause retypings + `NIK.weaken` re-proof). Independent contribution regardless of
  whether `cs5_completeness` lands.
- v3 Phase 16: `cs5_completeness_implies_fs_derivable` (no axioms).
- v3 Phase 17: `BK_cs5FC` / `BK_cs5Incest` / `BK_not_cs5FC` (`B_K ⊨ cs5FC''` over every IL-model;
  `cs5FC ⊊ cs5FC''` strict).
- v3 Phase 18: mainline honesty — `TS5 := {χ_T, χ_B, χ_4}` (`rfl`-true so `Ax(TS5) = CS5ModalAxiom`
  is definitional; the unproved constructive `IKT5 ⟺ IKTB4` is off the critical path); `GeomAxiom.D`
  and `GeomWitnessClosure` deleted; 0 sorry / 0 vacuous / 0 axioms under `Labelled/`.
- v3 Phase 19: `cs5_fs` — the `CS5 ⊢ FS` decision gate, **DERIVED** sorry-free
  (`[propext, Classical.choice]`); target-falsity risk eliminated.
- v3 Phase 20: `NIK.geomInternalize` (3/3 at `TS5`); requirement 3 vacuous at `TS5`.

Probe scaffolds READY TO TRANSCRIBE (all sorry-free, `#print axioms` ⊆
`[propext, Classical.choice, Quot.sound]`):
- `probes/fig41-crosslabel-gate.lean`: `NIKX`, `NIKX.weaken`, `NIKX.consistency_step`,
  `NIKX.disjunction_step`, `efq_crossLabel_of_edge`, `dia_bot_elim_TS5`, `dia_or_dist_TS5`.
- `probes/rchi-internalization-gate.lean`: `GeomAxiom.HoldsOn`, `ClassicalModelOn`,
  `ClassicalModelOn.of_classicalModel`, `classicalModelOn_TS5_iff`, `tPrime_TS5_false`.
- `probes/prime-lemma-blockers.lean`: `deductiveClosure_relativized_kills_the_chain`.
- `probes/lemma612-scaffold.lean`, `track-c-c1-tele-conj.lean`, `adequacy-gate-probe.lean` — leg-C
  (Ch.6 bridge) material, retained but off v4's critical path (see Non-Goals).

## Goals & Non-Goals

- **Goals**:
  1. **Repair `TPrime` inhabitance FIRST** (Phase 1): fix all four transcription defects in
     `Cslib/.../Labelled/` so the type Lemma 5.3.1 must inhabit is actually inhabitable. This is the
     gate — no downstream phase is worth dispatching until it lands.
  2. **Gate on inhabitedness** (Phase 2): construct an inhabitant of the repaired `TPrime` (or prove
     every emptiness chain now fails) before any Zorn/proof dispatch. This is the explicit process
     lesson of v3: Phases 20 AND 21 both burned full dispatches proving things against an
     already-empty type.
  3. **Sequence the completeness proof** per Simpson Ch 5 + Ch 7-8: chain-union closure → bounded
     prime lemma (5.3.1 / bounded form) → T-Comp graph completion for symmetry (8.2.5) → bounded
     canonical model + truth lemma (5.3.2 / 8.2.6) → frame-class match → `cs5_completeness`.
  4. Keep every landed artifact sorry-free and axiom-clean at each phase boundary; do not regress
     landed CK/CT/CS4/CS5 soundness, `cs5FC''`, or the four guardrails.
- **Non-Goals**:
  - Do **NOT** weaken, restate, or re-litigate the target; the target is proven satisfiable
    (`cs5_fs`, v3). Never target `cs5FC` (`B_K` provably does not inhabit it).
  - Do **NOT** port MMS `labIK≤` or de Groot–Shillito–Clouston constructions. Marin-Morales-
    Strassburger 2021 is cited as the labelled-calculus *provenance/inspiration* only; the carried
    proof is Simpson's.
  - Do **NOT** re-open the Track A/B/C 26-phase decomposition of v3. Its completed phases are banked
    above; its Track C (Ch.6 tree-surgery) material stays in `probes/` off the critical path unless
    the box-backward step (Phase 6) proves it is needed.
  - Do **NOT** discharge `clModel` via `ClassicalModel 𝒯 (TClosure 𝒯 R)`: it is free
    (`classicalModel_tClosure_free`, zero axioms) but proves clause 0 for the **closure**, silently
    changing the canonical model and putting the truth-lemma ◇-case on a different relation than the
    one it is proved about — a trap that **typechecks**. Use `ClassicalModelOn 𝒯 G.X G.R`.
  - Do **NOT** set the canonical relation to `𝒯-Comp(H)`: v3's Phase 22 spec was WRONG. Simpson p.94
    says `R_(H,Δ)(x,y)` iff **raw** `xRy` in `H`, and pp.95-98 read raw throughout (confirmed by two
    independent dispatches). Use the raw relation.

## Why the repaired design does NOT trip the four guardrails

The task's premise is that every route keeping CSLib's **prime-theory** canonical model is dead. The
repair changes `NIK`'s `(⊥E)`/`(∨E)` and `TPrime`'s clauses 0-1 — it does **not** turn labelled
contexts into prime theories. Each guardrail is checked explicitly:

1. **`cs5_symmetric_tail_box_gap` (CS5.lean:712 — THE wall).** This is the prime-theory Lindenbaum
   wall: a construction that fixes one component (a head theory) while extending the other cannot
   satisfy the symmetric back-clause and refute the box subject jointly. Route B uses **ONE Zorn
   over WHOLE contexts** — graph `G` and formula-set `Γ` grow *together*, capped only by the excluded
   `x:A`, with a plain unbounded inclusion order (`Context.le`, no fixed head, no bound). The repair
   does not introduce a head or a bound: `NIKX` only widens two elimination rules, and the relativized
   clauses only add a domain hypothesis. The "simultaneous maximal pair" that `CS5.lean:700-710`
   names as the missing object is exactly what the Zorn poset produces. Guardrail does not apply.
2. **`cs5Incest_forces_symm` (CS5Canonical.lean:643, axiom-free).** Any `≤`-mediated condition
   collapses to plain symmetry under head-monotonicity, and this is fatal only in composition with an
   exploding `Ω`-world (theory `⊤`, reachable from everywhere). `TPrime`'s **Consistency clause**
   (`∀ x ∈ G.X, ¬ Deriv 𝒯 G Γ (x:⊥)`) banishes `Ω` by construction: no label in a prime context's
   graph derives `⊥`. The repair *sharpens* this — cross-label `(⊥E)` means a single `z:⊥` would
   collapse every `x:A`, so the excluded `x:A` blocks `⊥` at *every* label at once
   (`NIKX.consistency_step`), which is precisely why Simpson calls consistency "immediate". No
   `Ω`-node exists for the guardrail to become fatal against. The guardrail remains a true, harmless
   theorem about the downstream `B_K` model.
3. **`cs5TwoSidedR_iff_cs5Tail` (CS5Canonical.lean:511).** This equates Simpson's two-sided `R` with
   the old `cs5Tail` wall **over CS5 quasi-prime theories**. Labelled bounded contexts are **not
   quasi-prime theories**: worlds are graph nodes carrying an explicit relation `G.R`, and the
   canonical relation is the **raw** graph relation with symmetry supplied by T-Comp graph completion
   (Lemma 8.2.5), not by a two-sided `R` reconstructed from theory membership. The `iff` has no
   quasi-prime-theory hypothesis to fire on. Guardrail does not apply.
4. **Task-512 atom-sum results.** The doubled-atom / atom-sum route is dead. Route B uses **labelled
   membership `y:B`** and graph edges, not atom sums; nothing in Phases 1-9 constructs or consumes an
   atom-sum. Guardrail does not apply.

## Risks & Mitigations

- **Risk (MEDIUM, unmechanized — settle in Phase 3 BEFORE the Zorn argument): chain-union vs cofinite
  encoding.** `NIKX.boxI`/`diaE` encode their eigenvariable side-condition by **cofinite
  quantification** (`∀ y ∉ L`), so an `NIKX` derivation has infinite branching and no finite graph
  support. Simpson's *"it is easily seen that `(⋃G_i, ⋃Γ_i)` is also in `C`"* (p.92) needs
  `Deriv 𝒯 G_∞ Γ_∞ (x:A) → ∃ i, Deriv 𝒯 G_i Γ_i (x:A)` — a **reflection** (finite-support) fact.
  Rebuilding a `boxI` at one chain index needs one `i` valid for cofinitely many `y`; each `y`
  yields its own `i_y`, and directedness does not bound them. `Deriv.mono` is only **monotonicity**
  (the easy direction). **Mitigation**: Phase 3 is dedicated to this, likely via a label-renaming /
  equivariance lemma for `NIKX` (absent from `Cslib/`); if it cannot be settled, escalate before
  spending Phase 4's Zorn dispatch.
- **Risk (~100%/dispatch base rate): another transcription defect.** Every dispatch on this task has
  found the previous one's transcription subtly wrong. **Mitigation**: the standing PDF-raster rule;
  mandatory `--lit` research + small-model/countermodel check on every transcribed schema BEFORE
  writing Lean.
- **Risk: the domain-relative equivalence design choice.** `equivalence_of_classicalModel_TS5` (v3)
  returns a **type-wide** `Equivalence` consumed by the frame-class match; under the `ClassicalModelOn`
  repair it becomes **domain-relative** (equivalence on `G.X`). **Mitigation**: Phase 1 makes this
  design choice explicitly — either carry a domain-relative equivalence throughout, or make the world
  domain the subtype `↥H.X`. Phase 7 consumes whichever is chosen. Flagged, not deferred silently.
- **Risk: Ch 7-8 boundedness may or may not be needed.** v3's research (Ch 5) suggested the *unbounded*
  prime lemma suffices and that boundedness is a decidability/FMP device (`T_S5 ∉ Dec_ND`). The user's
  Route B is framed on the *bounded* Ch 7-8 form. **Mitigation**: Phase 3-4's `--lit` research
  resolves whether the bounded prime lemma (8.2.6) is required for box-backward or whether the Ch 5
  unbounded form is enough; the plan sequences the bounded form per the user's decision and flags the
  simpler fallback.
- **Two soft spots (verifier-flagged, non-load-bearing, recorded for honesty)**: (a) the `(⊥E)` half
  of the "5.3.1 needs cross-label" argument infers from Simpson's word "immediate" rather than a named
  rule application (but `NIKX.consistency_step` mechanizes the step regardless); (b) the
  disconnected-instance underivability (`Q4`) is reasoned, not mechanized.

## Implementation Phases

Every proof-leg phase (3-6) MUST open with an `--lit` implementation-research step against the
Simpson Ch 7-8 chunks (Lemmas 8.2.5, 8.2.6, the bounded prime lemma) before transcription, per the
research gap flagged above. `--hard` is recommended throughout (this task has 3 prior plan versions
without convergence and a history of analysis-only dispatches — both `--hard` triggers).

### Phase 1: THE GATE — repair the four-defect transcription so `TPrime` is inhabitable [COMPLETED]

**Objective**: make `TPrime 𝒯 Atom` inhabitable by fixing all four transcription defects in
`Cslib/.../Labelled/`, in place, zero-debt. No downstream phase is dispatched until this lands green.

**Territory**: `Labelled/Deduction.lean`, `Labelled/Context.lean` only. Blast radius is confirmed
SMALL and independently re-verified: `NIK` occurs in exactly these two files; nothing outside
`Labelled/` imports `Labelled`; `CK`/`CT`/`CS4`/`CS5` never touch `NIK`; there is **no landed
soundness proof over `NIK`**; the **sole induction** over the relation is `NIK.weaken`.

**Tasks** (each has a landed sorry-free probe scaffold to transcribe):
1. **`(⊥E)`/`(∨E)` → cross-label** (`Deduction.lean`): replace `NIK`'s `efq` and `orE` constructors
   with the cross-label forms Figure 4-1 prints (`efq: x:⊥ / y:A`, independent `y`; `orE`: major
   `x:A∨B`, minors/conclusion at independent `y`, branches discharged at `x`). Transcribe verbatim
   from `NIKX` in `probes/fig41-crosslabel-gate.lean:133-175`. Rename `NIK`→ keep the name `NIK`
   (the probe calls the repaired system `NIKX` only to coexist with the old one; in-place the name
   stays `NIK`).
2. **Re-prove `NIK.weaken`**: transcribe `NIKX.weaken`
   (`probes/fig41-crosslabel-gate.lean:180-221`) — the `efq`/`orE` cases thread one extra label,
   proof scripts otherwise unchanged. This is the *only* proof obligation the constructor change
   creates.
3. **Clause 1 (`deductiveClosure`) → domain-relative** (`Context.lean:219`): retype to
   `∀ x ∈ G.X, ∀ A, Deriv 𝒯 G Γ (x ∶ A) → (x ∶ A) ∈ Γ`. This is THE emptiness-driver fix
   (`deductiveClosure_relativized_kills_the_chain`, `probes/prime-lemma-blockers.lean:120-125`):
   the type-wide clause forces `x:(A⊃A) ∈ Γ` at every label ⟹ `G.X = univ` ⟹ contradicts
   `coinfinite`; the relativized clause only concludes membership for labels already in `G.X`.
4. **Clause 0 (`clModel`) → `ClassicalModelOn`** (`Context.lean:217`): retype from
   `ClassicalModel 𝒯 G.R` to `ClassicalModelOn 𝒯 G.X G.R`. Transcribe `GeomAxiom.HoldsOn`,
   `ClassicalModelOn`, `ClassicalModelOn.of_classicalModel`, `classicalModelOn_TS5_iff` from
   `probes/rchi-internalization-gate.lean:221-322` (~40 lines). Simpson p.94 fixes satisfaction
   **in the structure `H`** (domain `H.X`), not type-wide.
5. **Resolve the `equivalence_of_classicalModel_TS5` design choice** (`Context.lean:285`): under the
   repair, produce a **domain-relative** equivalence (on `G.X`) — or commit to the `↥H.X` subtype
   world domain. Document the choice inline; Phase 7 consumes it.

**Explicit non-re-trip statement (MUST appear in the file docstrings)**: state, per the guardrail
analysis above, why the repaired `TPrime` is a whole-context Zorn object and not a prime theory, so
it does not re-trip `cs5_symmetric_tail_box_gap`, `cs5Incest_forces_symm`, or `cs5TwoSidedR_iff_cs5Tail`.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context` (and `.Deduction`) green.
- `lean_verify` on `NIK.weaken` and the repaired `TPrime` fields: axioms ⊆
  `[propext, Classical.choice, Quot.sound]`; zero `sorry`, zero new `axiom`, zero vacuous defs.
- Confirm CK/CT/CS4/CS5 soundness and `cs5FC''` still build unchanged (they never import `Labelled`;
  a targeted `lake build` of those modules is the check).

**Zero-debt gate**: if any of the four repairs cannot be transcribed green, mark this phase
`[BLOCKED]` and STOP — do not proceed. (This is very unlikely: all four scaffolds are landed
sorry-free.)

### Phase 2: INHABITEDNESS GATE — construct an inhabitant of the repaired `TPrime` [NOT STARTED]

**Objective** (the explicit process lesson of v3): before any Zorn/proof dispatch, prove the repaired
type is inhabitable. Depends on Phase 1.

**Tasks**:
1. Re-run the emptiness drivers (`tPrime_false`'s chain and `tPrime_TS5_false`) against the repaired
   type in a probe; confirm they no longer fire (the relativized clause 1 breaks the
   `G.X = univ` chain; `ClassicalModelOn` breaks the clause-0 chain).
2. Construct an inhabitant of the repaired `TPrime ∅ Atom` (at `𝒯 = ∅`, IK) — the smallest witness
   that the type can be populated at all — **or**, if a genuine construction is premature here, prove
   the weaker "no emptiness chain survives the repair" as the minimum gate.
3. If neither is achievable, STOP and escalate: the repair is insufficient (a fifth emptiness driver
   exists) and Phase 1 must be revisited before spending any Zorn dispatch.

**Verification**: probe is sorry-free; the `IsEmpty (TPrime …)` instance from
`prime-lemma-blockers.lean` no longer typechecks against the repaired type (or is explicitly
refuted). This phase may live in `probes/` (it is a gate, not a mainline deliverable) but its
conclusion is binding on Phases 3+.

### Phase 3: Settle the chain-union / cofinite-encoding obstacle [NOT STARTED]

**Objective**: mechanize the reflection (finite-support) fact that Simpson calls "easily seen" —
`Deriv 𝒯 G_∞ Γ_∞ (x:A) → ∃ i, Deriv 𝒯 G_i Γ_i (x:A)` over a chain — so the Zorn chain-closure step
(Phase 4) has an upper bound. This is the crux upstream of the whole argument (see Risks). Depends on
Phase 1; gated by Phase 2's go/no-go.

**Tasks**:
1. `--lit`: mine Simpson §5.1 (the consequence relation, finite open-assumption lists) and Ch 7-8's
   bounded-context finite-support handling for how the cofinite eigenvariable premise is reflected to
   a single chain index.
2. Prove (or construct) the label-renaming / equivariance lemma for `NIKX` that lets a `boxI`/`diaE`
   at the union graph be rebuilt at one chain index valid for cofinitely many `y`.
3. Prove chain closure: `(⋃G_i, ⋃Γ_i) ∈ C`.

**Verification**: `lake build` green; sorry-free in mainline (or a clearly-marked probe if still
exploratory). If the equivariance route fails, escalate — do NOT paper over with an axiom.

### Phase 4: Bounded Prime Lemma (Simpson 5.3.1 / bounded 8.2.6 form) — Zorn over whole contexts [NOT STARTED]

**Objective**: prove `Γ ⊬_G x:A ⟹ ∃ 𝒯-prime `(H,Δ) ⊇ (G,Γ)` with `Δ ⊬_H x:A`` — producing an
inhabitant of the repaired `TPrime`. Depends on Phases 2, 3.

**Tasks**:
1. `--lit`: mine Simpson Lemma 5.3.1 (pp.92-93 raster) and the bounded prime lemma (Ch 7-8); confirm
   the bounded form's coinfinite reserve `W(V')` matches `Context.coinfinite`.
2. ONE Zorn application over whole contexts (graph + formula-set growing together, capped by excluded
   `x:A`, inside fixed coinfinite reserve `W(V')`); upper bound from Phase 3.
3. Discharge the four clauses with the repaired rules:
   - **Consistency**: `NIKX.consistency_step` (cross-label `(⊥E)`) — "immediate", no maximality.
   - **Deductive closure**: relativized clause + maximality on `(H, Δ∪{y:B})` (needs `y ∈ H.X`,
     which the relativized clause supplies).
   - **Disjunction**: `NIKX.disjunction_step` (cross-label `(∨E)`) + maximality.
   - **Diamond**: `(◇E)` freshness + maximality on `(H∪{yRv}, Δ∪{v:B})` — reductio here is REAL
     (unlike `clModel`'s vacuous one); do not generalize any Phase-20 vacuity warning to it.

**Verification**: `lake build` green; sorry-free; axiom footprint ⊆ `[propext, Classical.choice,
Quot.sound]` (Zorn is classical metatheory, ambient in Mathlib, not a new axiom under `Cslib/`).

### Phase 5: T-Comp graph completion (Simpson Lemma 8.2.5) — symmetry [NOT STARTED]

**Objective**: the graph-completion step that supplies symmetry of the canonical relation in the
labelled bounded-context model. Depends on Phase 4.

**Tasks**:
1. `--lit`: mine Simpson Lemma 8.2.5 (T-Comp graph completion) from the Ch 7-8 chunks (raster for any
   displayed construction).
2. Transcribe the completion on the prime context's graph `H`; prove it preserves `𝒯-primeness` and
   yields symmetry on `H.X`.
3. State explicitly why this does NOT re-trip `cs5_symmetric_tail_box_gap`: the completion acts on the
   graph of a whole context, not on a fixed-head prime theory.

**Verification**: `lake build` green; sorry-free; guardrails still true.

### Phase 6: Bounded canonical model + truth lemma (Simpson 5.3.2 / 8.2.6) — box-backward [NOT STARTED]

**Objective**: build the canonical model and prove the truth lemma, including the box-backward case
via the bounded canonical model lemma over labelled membership `y:B`. Depends on Phases 4, 5.

**Tasks**:
1. `--lit`: mine Simpson Lemma 5.3.2 (pp.94-98 raster) and Lemma 8.2.6 (bounded canonical model,
   Ch 7-8). **Canonical relation = RAW `xRy` in `H`** (NOT `𝒯-Comp(H)` — v3 Phase 22 was wrong,
   confirmed twice); domain-relative "for all `y` in `H`".
2. Define the canonical model over `TPrime` worlds with the raw relation; valuation from labelled
   membership.
3. Prove the truth lemma by induction on the formula; box-backward via the bounded canonical model
   lemma over `y:B`. (If box-backward genuinely requires the Ch.6 tree-surgery bridge, pull the
   retained `probes/lemma612-scaffold.lean` material in here — otherwise leave it off-path.)

**Verification**: `lake build` green; sorry-free; the ◇-case and □-case are both proved about the
*raw* relation the model is built on (no silent closure swap).

### Phase 7: Frame-class match — domain-relative equivalence ⟹ `cs5FCIncest` [NOT STARTED]

**Objective**: discharge the frame-class conditions `cs5FC''`/`cs5FCIncest` needs. Depends on
Phases 5, 6.

**Tasks**:
1. From `ClassicalModelOn TS5 H.X H.R` derive the domain-relative `Equivalence` on `H.X` (reflexive,
   symmetric, transitive), using the Phase-1 design choice (domain-relative equivalence or `↥H.X`
   subtype) and `classicalModelOn_TS5_iff`.
2. Match the `cs5FCIncest` conjuncts (reflexivity, transitivity, `cs5Incest`, symmetry). **Citation
   fix**: `cs5Incest`/`cs5FCIncest` live at `CS5Canonical.lean:234,255` (NOT `CKExtension.lean:159,184`
   as v3 miscited).
3. State non-trip of `cs5Incest_forces_symm` (Consistency banishes `Ω`) and `cs5TwoSidedR_iff_cs5Tail`
   (not quasi-prime theories) at the point of use.

**Verification**: `lake build` green; sorry-free; guardrails unregressed.

### Phase 8: `cs5_completeness` assembly [NOT STARTED]

**Objective**: compose Phases 4-7 into `cs5_completeness : CKValidFC cs5FC'' φ → Derivable
CS5ModalAxiom φ`, sorry-free and axiom-clean. Depends on Phases 6, 7.

**Tasks**:
1. Contrapositive assembly: `¬ Derivable CS5ModalAxiom φ` ⟹ prime context refuting `φ` (Phase 4) ⟹
   canonical model + truth lemma (Phase 6) ⟹ frame-class member (Phase 7) ⟹ `¬ CKValidFC cs5FC'' φ`.
2. Reuse only what genuinely transfers: `Proposition`/`Proposition.map` (Basic.lean),
   `DerivationTree`/`Derivable`, `CS5ModalAxiom`, and task-512's landed axiom-free soundness
   (`cs5_axiom_sound_incest` / `cs5_soundness_incest`) where the frame class matches.

**Verification**: full `lake build`; `lean_verify cs5_completeness` axioms ⊆ `[propext,
Classical.choice, Quot.sound]`; the full CSLib CI order (`checkInitImports`, `lake lint`,
`lint-style`, `lake test`, `mk_all`, `shake`) green.

### Phase 9: Bookkeeping and paper fixes [NOT STARTED]

**Objective**: clear the recorded follow-ups. Depends on Phase 8 (or runnable anytime after Phase 1).

**Tasks**:
1. Transcribe `cs5_fs` (the v3 decision-gate result, currently in `probes/`) into `Cslib/` —
   transcription, not proof work.
2. Correct the stale REFUTED verdict in `fischer-servi-probe.lean`'s docstring (its `fs_sound` is
   unaffected and valid; only the narrative is wrong).
3. Rewrite `state.json`'s `blockers` field to match this plan (the v3 "TRACK B CLOSED"/"NEXT = C5"
   language is fully superseded).
4. Record the `literature-briefing.sh` modal-source resolution bug for the record (index keys `.id`
   vs `.doc_id`; 20 modal sources silently skipped) so `--lit` runs verify Simpson chunks by content.

**Verification**: `lake build` green; docstrings accurate; `state.json` consistent.

## Testing & Validation

- **Per-phase**: scoped `lake build Module.Name` green; `lean_verify` axiom check (⊆ `[propext,
  Classical.choice, Quot.sound]`, zero sorry, zero new axiom, zero vacuous def) at every phase
  boundary; guardrail lemmas re-checked to still build after Phases 1, 5, 7.
- **Small-model/countermodel check on every transcribed schema BEFORE writing Lean** (the discipline
  that caught prior defects).
- **Inhabitedness gate (Phase 2)** is a hard precondition on Phases 3+.
- **Final**: full CSLib CI order (§ cslib.md): `lake build` → `checkInitImports` → `lake lint` →
  `lake exe lint-style` → `lake test` → `mk_all --module` → `shake`.

## Artifacts & Outputs

- **Mainline** (`Cslib/.../Constructive/Labelled/` and `.../Constructive/`): repaired
  `Deduction.lean` + `Context.lean` (Phase 1); new files for the prime lemma, canonical model, truth
  lemma, frame-class match, and `cs5_completeness` (Phases 4-8). Estimated ~1500-2500 new/changed
  lines total.
- **Probes** (`probes/`): the inhabitedness gate (Phase 2) and any exploratory chain-union work
  (Phase 3) before mainline transcription.
- **The single headline deliverable**: `cs5_completeness`, sorry-free, axiom-clean, CI-green.

## Rollback/Contingency

- **Phase 1 fails to transcribe green** (very unlikely — scaffolds are landed sorry-free): mark
  `[BLOCKED]`, STOP, escalate; the mainline is left unchanged (Phase 1 is in-place edits to two
  files, revertable via git).
- **Phase 2 inhabitedness gate fails**: a fifth emptiness driver exists; return to Phase 1 before any
  proof dispatch. Do NOT proceed to Zorn.
- **Phase 3 chain-union obstacle cannot be settled**: escalate with the exact reflection goal that
  fails; do NOT introduce an axiom or a vacuous placeholder. Leg A is banked at the repaired-substrate
  level (an independent contribution: a correctly-transcribed, inhabitable labelled framework).
- **Phase 6 box-backward requires the Ch.6 bridge**: pull in the retained
  `probes/lemma612-scaffold.lean` (C4 tree-surgery) and `track-c-c1-tele-conj.lean` (C1-C3) material;
  these are preserved for exactly this contingency.
- **General**: every phase boundary is a green, committed checkpoint (zero-debt invariant), so any
  failure rolls back to the last green phase without losing landed work.
