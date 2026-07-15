# Implementation Plan: Task #517 — Labelled/Bounded-Context CS5 Completeness (Route B, full build)

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Status**: [NOT STARTED]
- **Effort**: 22 hours
- **Dependencies**: None (task 513 landed; task 518 re-ingests the Simpson corpus but is NOT a blocker — see "Corpus warning")
- **Research Inputs**: `specs/517_labelled_bounded_context_cs5_completeness/reports/01_labelled-bounded-context-method.md` (authoritative — built from the source PDF, not the corpus)
- **Artifacts**: plans/01_labelled-framework.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Build Simpson's labelled natural-deduction framework in Lean 4 and use it to prove constructive
Kripke completeness for `CS5` (≡ `IS5`), the target being
`cs5_completeness : CKValidFC cs5FCIncest φ → Derivable CS5ModalAxiom φ`. The spine is Simpson
**Chapters 5–6** (`Simpson1994`): **Prime Lemma 5.3.1** (Zorn over whole labelled contexts),
**Canonical Model Lemma 5.3.2** (box-backward via fresh label + `(□I)`), and **Theorem 6.2.1**
(Hilbert⟺labelled adequacy, uniform in `𝒯 ⊆ {χ_D, χ_T, χ_B, χ_4, χ_5}` — which covers `CS5`'s `B`
and `5`). Definition of done: `cs5_completeness` closes sorry-free and axiom-clean under `Cslib/`,
with no regression of landed `CK`/`CT`/`CS4`/`CS5` soundness or task-509's `cs5FC''`.

**Confidence: ~50% (range 45–55%).** This is the research report's honest number and it is not to
be inflated. The residual risk is concentrated in a single named node.

**The hardest node is the tree internalization (Simpson Lemma 6.1.2 / 6.2.3)** — the adequacy
bridge's translation `(Γ ⊢_G x:A)*`. Simpson's proof there is **informal by his own admission**
("we hope that this makes the proof comprehensible without too much formality") and he **omits the
(⊥E) and (∨E) cases** as "quite intricate because their premises and conclusion may have prefixes
arbitrarily far apart in `G`". This node is **reconstruction, not transcription**, and it sits on
the **unavoidable** Hilbert⟺labelled adequacy bridge. Per report 01's explicit recommendation it is
**gated and dispatched first among the risk-bearing nodes** — as **Phase 3**, the earliest point at
which its statement is even expressible (it quantifies over `⊢_G`, so Phases 1–2 are logical
prerequisites), and **before the entire semantic spine** (Phases 4–8). Both branches are specified
in Phase 3 and in "Rollback/Contingency".

### Research Integration

Report 01 is the authoritative input and this plan is built directly on it. Key findings encoded:

- **The spine is Ch. 5–6, NOT Ch. 7–8.** Chapter 8 is the *finite model property* and **explicitly
  excludes IS5** (Simpson p. 161: "we fix L as any logic in `Dec_𝒯`, **other than IS5** … Thus
  `𝒯 ⊆ {χ_D, χ_T, χ_B}`"). `T-Comp` has **no transitivity clause** and cannot produce an S5 frame.
  **Reports 516/02 and 516/01 are superseded on Simpson chapter structure — do not follow their
  Ch. 7–8 lemma references (8.2.4/8.2.5/8.2.6); they are wrong.** They were rated from 122–140 byte
  truncated OCR chunks.
- **The key structural insight.** Simpson's Zorn-over-**contexts** *is* the "simultaneous maximal
  pair" that `CS5.lean:700-710` named as the missing object. A context `(G,Γ)` is **one object**
  carrying **all labels at once**, so one Lindenbaum maximalises `Θ(y)` for **every** label
  simultaneously against a **single** global constraint `Γ' ⊬ x:A`. Cross-world invariants
  (`boxInv Θ(y) ⊆ Θ(z)` for `yRz`) are **consequences of deductive closure under `(□E)`**, not
  constraints threaded through the Zorn. **This is why Route B escapes task-512's wall.**
- **The §8.1 soundness failure provably does not touch the completeness direction.** Simpson:
  "nowhere in the proof of completeness have we used the assumption that `G` is a tree." Soundness
  is already landed independently (`cs5_soundness_incest`). Decisive de-risking.
- **Real reuse confirmed**: `B_K ⊨ cs5FCIncest` (verified conjunct-by-conjunct in report 01 §D4),
  so task-512's `cs5_axiom_sound_incest` / `cs5_soundness_incest` **transfer unchanged**.

### Guardrail analysis (encoded — read before any phase)

Report 01 verified all four guardrails and **none trip**, but two require care and the plan must
prevent any phase from accidentally re-creating the conditions that make them bite.

| Guardrail | Location | Verdict |
|---|---|---|
| `cs5_symmetric_tail_box_gap` | `CS5.lean:712` | **Does not trip — but narrowly.** Its *argument* **transfers** to the labelled model. |
| `cs5Incest_forces_symm` | `CS5Canonical.lean:643` | **Applies, and is SATISFIED** (not violated). |
| `cs5TwoSidedR_iff_cs5Tail` | `CS5Canonical.lean:511` | Not applicable (about quasi-prime theories under `cs5TwoSidedR`). |
| `cs5Incest_cs5PrimeMreach_false` | `CS5Canonical.lean:688` | Not applicable (refutes `cs5Incest` for `cs5PrimeMreach` on `CS5PrimeSegment`). |

**`cs5_symmetric_tail_box_gap` — the trap, stated explicitly so no phase re-imposes a fixed head.**
Its argument *does* go through in the labelled model: with `H := Θ(y)`, `T := Θ(z)` for `yRz`, both
`boxInv Θ(y) ⊆ Θ(z)` (by `□E` along `yRz`) and `boxInv Θ(z) ⊆ Θ(y)` (by `□E` along `zRy`, available
because for `𝒯 = {χ_T, χ_5}` the context graph is a classical model of `𝒯` hence symmetric) hold,
and `Θ(z)` has the disjunction property. **The lemma is saved ONLY by its fixed-head hypothesis
`q ∉ H`.** Simpson's box-backward witness lives in a **strictly larger** context `(H',Δ') ⊇ (H₀,Δ)`
where `q ∈ Θ'(y)` is *allowed in* — licensed by the box clause's own `≤`-quantification. Running the
gap-lemma argument at the witness yields the true and harmless conclusion `q ∈ Θ'(y)`; the
hypothesis simply fails. The lemma is true and **has no instance to bite**.

> **CONSTRAINT ON EVERY PHASE**: the box clause **must** retain its `≤`-quantification over larger
> contexts (`(H,Δ),y ⊩ □B iff ∀(H',Δ') ≥ (H,Δ), ∀z, yRz in H' ⟹ z:B ∈ Δ'`). **No phase may fix the
> head** or bound the context in the box-backward case. Doing so re-imposes exactly the hypothesis
> that makes `cs5_symmetric_tail_box_gap` fatal, and re-enters task-512's wall.

**`cs5Incest_forces_symm` — applies but is satisfied.** In `B_K` with `head(w,d) := {A | w,d ⊩ A}`,
both `hmono` (persistence) and `hbox` hold, so the guardrail applies and yields plain box-symmetry.
This is a **true theorem about `B_K`, not a contradiction**, because `B_K`'s `R` is **primitive
graph data satisfying `𝒯` by construction** (𝒯-primeness clause 0), not membership-derived. The
guardrail was fatal in CSLib's canonical model only in composition with `Ω = univ` being universally
reachable — and **`B_K` has no `Ω`**: 𝒯-primeness's **Consistency** clause (`Γ ⊬_G x:⊥`) banishes it,
so `botForces := λ_. False` discharges all five `CKValidFC` `botForces` side conditions vacuously.

> **Root difference, named**: in CSLib's canonical model `R` is *derived* from box-membership
> (`r Γ Δ := boxInv Γ ⊆ Δ`), so symmetry is a *demand on theory content* and **fails**. In `B_K`,
> `R'` is *primitive graph data* satisfying `𝒯` by construction, so symmetry is *given* and
> box-symmetry is a *consequence*. The guardrail does not distinguish these; **the model does.**

### Reuse ledger (every entry verified at source this planning round)

**Transfers:**

| Asset | Location (verified) | Why it survives |
|---|---|---|
| `Proposition` | `Cslib/Logics/Modal/Basic.lean:72` | Formula type unchanged; labelled formulae are `Label × Proposition Atom`. |
| `Proposition.map` | `Cslib/Logics/Modal/Basic.lean:140` | Relabelling utility. |
| `DerivationTree` | `Cslib/Logics/Modal/Metalogic/DerivationTree.lean:134` | Hilbert side of the bridge untouched. |
| `Derivable` | `Cslib/Logics/Modal/Metalogic/DerivationTree.lean:201` | The completeness target's conclusion. |
| `CS5ModalAxiom` (17 cases) | `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean:182` | The completeness target's syntax. |
| **`cs5_axiom_sound_incest`** | `Cslib/.../Constructive/CS5Canonical.lean:278` | **Frame class matches — real reuse win (Phase 8).** |
| **`cs5_soundness_incest`** | `Cslib/.../Constructive/CS5Canonical.lean:340` | **Ditto.** (Report 01 cited `CS5.lean:126`; that is a *docstring* line — **corrected here**.) |
| `cs5_soundness_derivable_incest` | `Cslib/.../Constructive/CS5Canonical.lean:373` | Assembly (Phase 9). |
| `cs5FCIncest` | `Cslib/.../Constructive/CS5Canonical.lean:255` | Frame-condition target (Phase 8); 5 conjuncts. |
| `cs5Incest` | `Cslib/.../Constructive/CS5Canonical.lean:234` | Conjunct 5. |
| `CKForces` | `Cslib/.../Constructive/Forcing.lean:67` | `B_K` is a `CKForces` model. |
| `ckforces_persistence` | `Cslib/.../Constructive/Forcing.lean:122` | Reused in Lemma 8.1.2 (Phase 7). |
| `CKValidFC` | `Cslib/.../Constructive/CKExtension.lean:86` | The validity target. |
| `ckValid_iff_ckValidFC_true` | `Cslib/.../Constructive/CKExtension.lean:100` | Assembly. |
| `CS5 ≡ IS5` (Pacheco Thm 13) | `Cslib/.../Constructive/CS5.lean:93-99` (docstring) | **Licenses using Simpson's IS5 (`𝒯 = {χ_T, χ_5}`) for `CS5`. Load-bearing for Phase 9.** |
| `cs5_dia_bot_imp_bot` | `Cslib/.../Constructive/CS5.lean:740` | Justifies `botForces := λ_. False` (no fallible worlds at CS5 strength). |

**Explicitly does NOT transfer — and must NOT be reused:**

| Asset | Location | Why |
|---|---|---|
| `CKSegment` | `Cslib/.../Constructive/Segment.lean:115` | A **single prime theory over a fixed head**; Simpson's world is a **pair** (𝒯-prime context, label). Different world type, not a refinement. |
| `Preorder (CKSegment)` | `Cslib/.../Constructive/Segment.lean:161` | `le P Q := P.head ⊆ Q.head`; `B_K`'s `≤'` **fixes the domain element and moves the context**. |
| `SegmentLindenbaum` engine (`quasi_prime_exclusion:73`, `box_refuting_theory:177`, `dia_refuting_theory:203`, `quasi_head_realization:251`) | `Cslib/.../Constructive/SegmentLindenbaum.lean` | Extends **one theory with the other component fixed** — the sequential construction task 512 Phases 8–10 found unstable. **Its fixed-other-component shape IS the bug.** Simpson's Zorn is over a single object carrying all labels; there is no "other component" to fix. |
| `QuasiPrime` | `Cslib/.../Constructive/Segment.lean:64` | Admits `Ω = univ`; Simpson's 𝒯-prime carries **Consistency** as a defining clause. **Do NOT generalize `QuasiPrime`** — CK/CT/CS4's landed completeness needs fallible worlds. |

### Prior Plan Reference

No prior plan for task 517. Prior *context* (not templates): task 512's `plans/02_birelational-pivot.md`
walled at Phase 5 (`specs/512_.../handoffs/phase5-blocker-handoff.md`) — `cs5Incest (@cs5CanonMreach)`
is **mathematically false** because `boxInv` is monotone under `⊆`, so the `≤`-mediated witness
`u′ ≥ u` can never help, and `Ω` (head `= Set.univ`) is universally reachable but cannot route back.
The lesson encoded here: **the world type and the relation must change** (primitive graph `R`,
Consistency-carrying primes), which is exactly what Route B does. Task 512's *negative* results are
preserved as guardrails and are not to be re-trod.

### Roadmap Alignment

No `specs/ROADMAP.md` found; `roadmap_flag` not set. No roadmap phases added.

### Corpus warning (MUST be honored by every implementing agent)

**The Simpson literature CORPUS chunks are broken/truncated.** The ingested chunks for
`simpson_1994_intuitionisticmodallogic` are 1091 chunks at ~312 bytes mean, with key chunks at
**122–140 bytes containing truncated titles and `> …` preview artefacts** — they are **unusable for
lemma statements**. All prior Simpson citations in tasks 512/516 rest on these fragments, which is
precisely how 516/02 mis-identified the spine as Chapter 8.

> **Implementers MUST work from `reports/01_labelled-bounded-context-method.md` or the source PDF
> (`/home/benjamin/Downloads/Simpson_1994_IntuitionisticModalLogic.ocr.pdf`, `pdftotext -layout`,
> 13,488 lines — line numbers in report 01 refer to that extraction). DO NOT take lemma statements
> from `literature-search.sh` chunk snippets.** Task 518 re-ingests the document; it is **not a
> blocker** for this task because report 01 already carries the verbatim-grounded statements.

### File layout (proposed)

New subdirectory, built **alongside** the landed stack — nothing existing is modified except the
`Cslib.lean` import list:

```
Cslib/Logics/Modal/Metalogic/Constructive/Labelled/
├── Syntax.lean           -- Phase 1: labels, graphs, witness algebra W(V'), labelled formulae
├── Deduction.lean        -- Phase 2: N_IK(𝒯) + freshness side conditions + weakening
├── Adequacy.lean         -- Phase 3: GATE — Lemma 6.2.2 + Lemma 6.1.2/6.2.3 tree internalization
├── Context.lean          -- Phase 4: Context + TPrime (5 clauses) + 𝒯_S5 := {χ_T, χ_5}
├── PrimeLemma.lean       -- Phase 5: Prime Lemma 5.3.1 (Zorn over contexts)
├── CanonicalModel.lean   -- Phase 6: K^𝒯 + Canonical Model Lemma 5.3.2 (truth lemma)
├── Birelation.lean       -- Phase 7: B_K construction + Lemma 8.1.2 + ◇-clause reconciliation
├── FrameClass.lean       -- Phase 8: B_K ⊨ cs5FCIncest (5 conjuncts)
└── CS5Completeness.lean  -- Phase 9: C0 + assembly of cs5_completeness
```

Each phase **owns exactly one file** (territory contract) — this makes Wave 3's parallel dispatch
(Phase 3 ‖ Phase 4) conflict-free. Add `public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.*`
entries to `Cslib.lean` (alongside lines 353–362) as each file lands, alphabetically.

**BibKeys** (all verified present in `references.bib`): `Simpson1994` (**Ch. 5–6**, line 86),
`MarinMoralesStrassburger2021` (962), `Dosen1985` (913), `BozicDosen1984` (925),
`AlechinaMendlerdePaivaRitter2001` (949), `Wijesekera1990` (885), `Pacheco2024` (895).

## Goals & Non-Goals

**Goals**:
- Land Simpson's labelled framework (syntax, `N_IK(𝒯)`, contexts, 𝒯-primeness) in Lean 4.
- Prove Prime Lemma 5.3.1, Canonical Model Lemma 5.3.2, and the adequacy bridge (Thm 6.2.1).
- Prove `cs5_completeness : CKValidFC cs5FCIncest φ → Derivable CS5ModalAxiom φ`, sorry-free.
- Reuse `cs5_axiom_sound_incest` / `cs5_soundness_incest` via `B_K ⊨ cs5FCIncest`.
- Deliver a **reusable labelled framework + countermodel construction even if the gate fails**.

**Non-Goals**:
- The finite model property / decidability (Simpson Ch. 7–8) — out of scope, and Ch. 8 excludes IS5.
- Simpson's §8.1.2 **soundness** direction (which genuinely fails without a treeness restriction) —
  not needed; soundness is already landed as `cs5_soundness_incest`.
- Generalizing `QuasiPrime` or reworking `cs5FCIncest` (task 512 Phase 4's landed definition).
- Regressing or refactoring landed `CK`/`CT`/`CS4`/`CS5` soundness or task-509's `cs5FC''`.
- Following Marin's `klmn` frame presentation inside the construction — use **Simpson's geometric
  theory `{χ_T, χ_5}`**, and only *derive* `cs5FCIncest` at the end (Phase 8). (Report 01 notes the
  irony that §6.3's inexpressibility condition is violated by exactly the `(1,1,0,0)` instance CSLib
  transcribes as `cs5Incest` — hence the ordering.)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **Phase 3 (gate) cannot be closed**: Simpson omits (⊥E)/(∨E) as "quite intricate"; his proof is self-declaredly informal; the treeness invariant is never stated as a lemma. **This is the task's main risk.** | H | M (~50%) | **Gate it and dispatch it first** (Phase 3, before the whole semantic spine). Bounded attempt: **2 agent dispatches**. Mitigating design: define `LCons G Γ x A := Derivable CS5ModalAxiom ((Γ ⊢_G x:A)*)`, making the bridge **definitional at the trivial graph** and converting Lemma 6.1.2 into **per-rule admissibility obligations** — modular and incremental. On failure: Phases 4–8 still land; task → `[BLOCKED]` with documented obstruction, **never a `sorry`**. |
| **Phase 2 eigenvariable/freshness conditions** are a notorious Lean cost centre; the line estimate could be off by 2×. | M | M | Use a **locally-nameless** encoding (precedent: CSLib `Languages/Lambda`). Budget explicit re-planning if Phase 2 exceeds 600 lines. |
| Phase 5's **geometric-witness closure condition** (context clause 3) is fiddly. | M | M | Land clause 3 as a separate `def` + closure lemma in Phase 4 before the Zorn needs it. |
| **◇-clause mismatch**: Simpson's ◇ is a plain `∃`; CSLib's Wijesekera ◇ is `∀≤∃`. | M | M | Real proof obligation, explicitly scoped as Phase 7. Needs `R` monotone under `≤` + `ckforces_persistence` (`Forcing.lean:122`). Not a formality — do not hand-wave. |
| **`R`-monotonicity-under-`≤`** (IL-model condition) treated as trivial by Simpson but real in Lean. | M | M | Discharge explicitly in Phase 7; consumed by Phase 8 conjuncts 3 and 4. |
| A phase accidentally **fixes the head** in box-backward, re-entering task-512's wall. | H | L | The `≤`-quantification constraint is stated in the Overview and repeated in Phases 6 and 7 verification criteria. |
| Implementer uses **truncated corpus chunks** for lemma statements (how 516/02 went wrong). | H | M | Corpus warning stated in Overview and repeated in every phase's Tasks. Work from report 01 or the source PDF only. |
| **~zero reuse of the Henkin/segment stack** — 7 of 9 phases greenfield. | M | H (certain) | Accepted and priced. The reuse ledger is honest about it. |
| **Base rate**: this problem has walled 4× (atom-sum, one-sided-R, two-sided-R, independent-≤/Route A); reports 05, 06, 516/01 all over-rated their route. | H | — | Confidence held at **~50%**, deliberately below 516/02's "~high". Gate-first structure means failure is cheap and produces reusable assets. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |
| 7 | 8 | 7 |
| 8 | 9 | 3, 8 |

Phases within the same wave can execute in parallel.

**Gate structure (read this before dispatching anything).** Phase 3 is the **gated hardest node**
and is dispatched **first among the risk-bearing nodes**, in Wave 3 — the earliest wave at which it
is dispatchable, because its statement quantifies over `⊢_G` and therefore *cannot* be written
before Phases 1–2 exist. Phases 1–2 are deliberately scoped as **minimal gate prerequisites**: land
exactly what Phase 3 needs, nothing speculative. Phase 3 runs **in parallel with Phase 4** and
**precedes the entire semantic spine** (Phases 5–8), which is the substantive requirement from
report 01 ("P8 is separable and should be dispatched early in parallel … **Do not leave P8 last**").

- **Gate SUCCESS** → proceed through Waves 4–8; Phase 9 assembles `cs5_completeness`.
- **Gate FAILURE after the bounded attempt (2 dispatches)** → **do not** open a third. Phases 4–8
  still execute and land a genuine, reusable labelled framework + countermodel construction. Phase 9
  is unreachable. Task returns to **`[BLOCKED]`** with a documented obstruction handoff —
  **never with a `sorry`**.

**Zero-debt invariant (applies at EVERY phase boundary, no exceptions):** **NO `sorry`** and **NO
new `axiom`** under `Cslib/`. Any incomplete exploration lives in
`specs/517_labelled_bounded_context_cs5_completeness/probes/*.lean` (precedent: task 512's
`probes/cs5-canonical-probe.lean`), which is outside `Cslib/` and never imported by it. A phase
either lands sorry-free under `Cslib/` or lands nothing under `Cslib/`.

---

### Phase 1: Labelled syntax — labels, graphs, witness algebra [COMPLETED]

- **Goal:** Land the labelled syntax layer: prefix variables, the witness algebra `W(V')`, graphs
  with their operations, and labelled formulae.
- **Tasks:**
  - [x] Read `reports/01_labelled-bounded-context-method.md` §"Deliverable 1a/1c". **Do not use
        corpus chunks for statements** (see Corpus warning).
  - [x] Define prefix variables `V` (countably infinite) and the **witness algebra** `W(V')`: the
        free algebra over `V'` with a unary operator `v_{x:◇A}` per modal formula and a `k`-ary
        operator per geometric sequent (Simpson `:5883–5905`). *(deviation: altered -- only the
        unary diamond-witness operator `dwitness` is implemented; the `k`-ary geometric-sequent
        witness operators are elided because `𝒯_S5 := {χ_T, χ_5}` are both universal Horn clauses
        needing no Skolem witness. Flagged in the module docstring as additive/extensible.)*
  - [x] Define **coinfinite** `V' ⊆ V` and the fresh-label supply lemma: from coinfiniteness,
        extract `z ∈ V \ V'`. **This is load-bearing for the □-backward case (Phase 6)** — Simpson
        `:5920`: "In order to always guarantee a supply of such new elements for `D_{w'}` we shall
        work below with `V'` that are coinfinite subsets of `V`".
  - [x] Define `Graph` as `(X, R)` with `X` non-empty (`:5047–5065`); operations `G ∪ G'`,
        `G ∪ X'`, `G ∪ {xRy}`; the **trivial graph** `𝒯 = ({x}, ∅)` (`:5077`).
  - [x] Define labelled formulae as `x : A` for `x ∈ W(V)`, `A : Proposition Atom` (reuse
        `Proposition`, `Basic.lean:72`).
  - [x] Add `public import` for `Labelled.Syntax` to `Cslib.lean`.
- **Timing:** 2 hours (~200–250 lines)
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Syntax.lean` — new (owned)
  - `Cslib.lean` — one import line
- **Verification:**
  - `lake build` clean; zero `sorry`, zero new `axiom`.
  - Fresh-label supply lemma proved (given coinfinite `V'` and finite/contained `H`, produce
    `z ∉ H`).
  - BibKey `Simpson1994` cited in the module docstring (Ch. 5).

---

### Phase 2: The labelled deduction system `N_IK(𝒯)` [COMPLETED]

- **Goal:** Land `N_IK(𝒯)` with correct eigenvariable/freshness side conditions, plus the
  weakening/graph-morphism lemmas. **This is the gate's prerequisite — keep it minimal and land it
  fast.**
- **Tasks:**
  - [x] Read report 01 §"Deliverable 1b". Statements from report 01 / source PDF **only**.
  - [x] Define the inductive `N_IK` (Figure 4-1, `:4630–4670`): intuitionistic propositional rules
        (`⊥E`, `∧I/E`, `∨I/E`, `⊃I/E` — all **label-local**) plus `(□E)`, `(□I)`, `(◇I)`, `(◇E)`.
  - [x] Encode the **`(□I)` restriction** (`:4661`): "`y` must be **different from `x`** and must
        **not occur in any open assumptions** other than the distinguished occurrences of `xRy`".
        *(via cofinite quantification `∀ y ∉ L, ...` over a finite exclusion set `L`, not a bare
        existential + side condition -- see "Encoding decision" deviation below.)*
  - [x] Encode the **`(◇E)` restriction** (`:4664`): "`y` must be different from both `x` and `z`
        and must not occur in any open assumptions upon which `z:B` depends other than the
        distinguished occurrences of `y:A` and `xRy`". *(same cofinite-quantification encoding.)*
  - [x] Add the geometric rules: `N_IK(𝒯) = N_IK + {(R_χ) | χ ∈ 𝒯}` (`:4940`). *(deviation:
        altered -- report 01 cites `:4940` by location only, without transcribing Figure 4-3's
        exact rule shape (a genuine source gap). Resolved via a `TClosure` 𝒯-closure operator on
        `G.R`, consumed by `(□E)`/`(◇I)`'s relational premises; `χ_D` (seriality) excluded as it
        needs a fresh-witness rule, out of scope since `𝒯_S5` omits it. Flagged in the module
        docstring ("The geometric extension") for the Phase 3 implementer to double-check against
        the source PDF directly if Lemma 6.2.2's translation depends on the precise rule shape.)*
  - [x] Define the **consequence relation** `Γ ⊢_G x:A` (`:5090`, verbatim): a derivation of `x:A`
        from open assumptions `y₁Rz₁,…,yₘRzₘ, x₁:A₁,…,xₙ:Aₙ` with each `yᵢRzᵢ` in `G` and
        `{xⱼ:Aⱼ} ⊆ Γ`. `A` is a **theorem** iff `⊢_𝒯 A` over the trivial graph (`:5114`).
  - [x] Prove weakening / graph-morphism lemmas (Prop. 4.4.1, `:5135`).
  - [x] **Encoding decision**: prefer **locally-nameless** for the eigenvariable conditions
        (precedent: CSLib `Languages/Lambda`). Record the decision in the module docstring.
        *(deviation: altered -- cofinite quantification over named labels was used instead of
        strict locally-nameless de Bruijn indices, because labels here are names shared across
        two independently-threaded structures (`Γ` and `G`), not binders scoped within one
        inductive term. Cofinite quantification is the same underlying technique CSLib's own
        locally-nameless `Typing.abs` uses and gives weakening "for free" by direct induction, so
        the plan's underlying goal -- avoid a separate renaming lemma -- is achieved. Fully
        flagged in the module docstring, "Encoding decision".)*
  - [x] Add `public import` for `Labelled.Deduction` to `Cslib.lean`.
- **Timing:** 3 hours (~250–300 lines; **budget 2× and re-plan if it exceeds ~600**)
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Deduction.lean` — new (owned)
  - `Cslib.lean` — one import line
- **Verification:**
  - `lake build` clean; zero `sorry`, zero new `axiom`.
  - Weakening lemma proved; a smoke-test derivation (e.g. `x:□A, xRy ⊢ y:A` by `(□E)`) closes.
  - **Structural check for Phase 3**: confirm by inspection of the rules that **only `(□E)` and
    `(◇I)` take relational premises** — Phase 3's Lemma 6.2.2 depends on this (`:7014`).
  - If the line budget is exceeded 2×, **stop and report** rather than expanding in flight.

---

### Phase 3: **[GATE — HARDEST NODE]** Adequacy bridge: Lemma 6.2.2 + Lemma 6.1.2/6.2.3 [BLOCKED]

**Dispatch 1 of 2 verdict: GATE FAIL.** Lemma 6.2.2 (hard direction) is now **complete,
sorry-free, axiom-clean** — see `specs/517_.../probes/adequacy-gate-probe.lean` and
`specs/517_.../handoffs/adequacy-gate-blocker-handoff.md` for the full mechanization and the
precise diagnosis of what remains (Lemma 6.1.2/6.2.3, the tree internalization). Per the Phase 3
failure branch below, nothing is landed under `Cslib/` this dispatch (the whole gate did not
close); the plan permits **one further dispatch (2 of 2)** before this phase is finally marked
`[BLOCKED]`.

- **Goal:** Prove the Hilbert⟺labelled adequacy bridge's **hard direction**:
  `⊢_{N_IK(𝒯)} x:φ ⟹ Derivable_CS5 φ` (Theorem 6.2.1, `:6880`). **This is the gated hardest node,
  dispatched first among the risk-bearing nodes, and the one node that can kill the task.**
- **Why this is the hardest node** (all grounded in Simpson's *own* hedges, not in an estimate):
  (i) his proof is self-declaredly **informal** — "we hope that this makes the proof comprehensible
  without too much formality" (`:6558`); (ii) he **omits (⊥E) and (∨E)** — "quite intricate because
  their premises and conclusion may have prefixes arbitrarily far apart in `G`. However, the
  difficulties are similar to those encountered in the (◇E) case" (`:6544`) — the `(◇E)` case **is**
  written out, which suggests tedious-but-tractable, **but that is his word, not a proof**; (iii) the
  **treeness invariant** ("we must take care that we can always restrict attention to graphs that are
  trees", `:6533`) is **never stated as a lemma**; (iv) it is the only spine node with **no
  transcribable proof**. **Everything else in Route B is transcription; this is reconstruction.**
  **Anyone who calls this a transcription has not read `:6544`.**
- **Tasks:**
  - [x] Read report 01 §"Deliverable 3" **in full**. Work from report 01 or the source PDF —
        **corpus chunks are unusable** (see Corpus warning). *(dispatch 1: also re-read Figure
        4-3/4-4 and Figure 3-7 directly from the source PDF via the `Read` tool, PDF pages 65 and
        74, to settle the Phase-2 TClosure re-check mandated by this dispatch.)*
  - [x] **Lemma 6.2.2** (`:6989`): `Γ ⊢^𝒯_G x:A ⟺ Ax(𝒯); Γ ⊢_G x:A`. The ⟸ direction translates
        each `(R_χ)` application away; the graph then stays a **tree**. Key structural observation
        (`:7014`): "each relational assumption in `Π*`, in particular the open assumptions `y_kRz_k`,
        **must be the premise of either a (□E) application or a (◇I) application**" — true by
        inspection of the rules (Phase 2 verification), but needs a careful derivation induction.
        *(dispatch 1: COMPLETE, sorry-free, axiom-clean — only the `⟹` direction, which is what
        Phase 9's assembly actually needs (used in contrapositive form); see `NIK_to_NIKAx` /
        `TClosure.hilbertTransport` in the probe file. The `⟸` direction was not attempted -- not
        needed for `cs5_completeness`.)*
  - [x] **Adopt the modular mitigation** (report 01's explicit recommendation): define
        `LCons G Γ x A := Derivable CS5ModalAxiom ((Γ ⊢_G x:A)*)`, making the bridge
        **definitional at the trivial graph** and converting Lemma 6.1.2 into a set of **per-rule
        admissibility obligations**. This does not reduce total work but makes it **modular and
        incremental** — so partial progress is legible and the gate verdict is evidence-based.
        *(dispatch 1: adopted in spirit -- rather than one new Hilbert derivation-tree type, Phase 3
        reuses `Metalogic.DerivationTree`/`Derivable` parameterized at a new axiom predicate `IKAx
        𝒯`, and Lemma 6.2.2 was split into the standalone, reusable `TClosure.hilbertTransport`
        lemma per non-`base` closure constructor -- exactly the "per-rule admissibility obligation"
        structure recommended.)*
  - [ ] **Lemma 6.1.2**: define, for a **finite tree** `G`, the internalizing formula (`:6512`).
        *(dispatch 2 CORRECTION: the formula as written above (□ for children, ◇ for the outer
        telescope) is BACKWARDS relative to the source. Verified directly against the source PDF
        (pages 109-112, read via the `Read` tool, not `pdftotext` which garbles □/◇ in this
        typeface): `Γ@U = ⋀{B|y:B∈Γ} ∧ (◇Γ@U₁) ∧ … ∧ (◇Γ@U_k)` (◇ for children) and
        `(Γ⊢_G x:A)* = Γ@T⁰ ⊃ □(Γ@T¹ ⊃ □(…Γ@T^{m-1} ⊃ □(Γ@T^m ⊃ A)…))` (□ for the outer,
        ancestor-to-target telescope). This correction is load-bearing: any future attempt MUST
        use the corrected formula -- see `handoffs/lemma612-final-blocker.md` §1.)*
        and prove `Γ ⊢_G x:A ⟹ (Γ ⊢_G x:A)*` is a theorem of `IK + Ax(𝒯)`, **by induction on
        derivations**. At the trivial graph `(⊢_𝒯 x:A)* = ⊤ ⊃ A`, so `A` follows (`:6524`).
        *(dispatch 1: NOT attempted to completion -- diagnosed as needing a dedicated reified
        finite-tree type co-indexed with the derivation, not just `Graph`. dispatch 2: built and
        verified this reified tree type (`LTree`) plus the corrected `star`/`Star` formulas and a
        full combinator toolkit (`box_mono1`/`box_mono2`/`wrapClosed`/`Star_imp1`/`Star_imp2`/
        `Star_append`), sorry-free and axiom-clean, in `probes/lemma612-scaffold.lean` -- but did
        NOT complete the induction over `NIKAx` itself (the `LTree`-`Graph` correspondence was not
        wired up, and the `(◇E)` case has a new, deeper obstruction -- see below and the final
        blocker handoff.)*
  - [ ] **State the treeness invariant explicitly as a lemma** (Simpson never does) and carry it
        through the induction. *(dispatch 1: deferred to dispatch 2. dispatch 2: NOT reached --
        subsumed by the `(◇E)` well-scopedness gap below, which is the actual remaining blocker.)*
  - [ ] **Reconstruct the omitted `(⊥E)` and `(∨E)` cases from scratch**, following the written-out
        `(◇E)` case as the model (`:6544`). **This is the crux.** *(dispatch 1: not reached.
        dispatch 2: worked out on paper via the verified `Star_imp1`/`Star_imp2` toolkit --
        CONTRARY to Simpson's own hedge, both `(⊥E)`/`(∨E)` are tractable, not intricate, because
        `NIKAx`'s encoding already commits them to being strictly label-local; NOT mechanized as
        actual `NIKAx` induction cases. The genuinely hard remaining case turned out to be
        `(◇E)` itself, one of "the four modal rules" Simpson writes out in full: `NIKAx.diaE`'s
        `z` parameter is not provably scoped relative to `x` by the bare Lean type, requiring an
        unproven well-scopedness invariant plus Simpson's own Figure 6-2 "dissection" tree-surgery
        -- see `handoffs/lemma612-final-blocker.md` §3 for the complete diagnosis.)*
  - [ ] **Lemma 6.2.3** (`:7127`): "trivial modifications … apart from one extra trivial case
        covering the use of an axiom" (`:7138`). *(dispatch 1: not reached. dispatch 2: not
        reached -- blocked on Lemma 6.1.2's `(◇E)` gap above.)*
  - [ ] Add `public import` for `Labelled.Adequacy` to `Cslib.lean` **only on success**.
        *(dispatch 1/2: not done -- gate did not close (FINAL, per the plan's 2-dispatch bound);
        the working file was moved to `specs/517_.../probes/lemma612-scaffold.lean` instead, per
        the failure branch below.)*
- **Timing:** 5 hours (~400–600 lines). **Bounded attempt: 2 agent dispatches. Do not open a third.**
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Adequacy.lean` — new (owned; **territory
    contract**: Phase 4 runs in parallel and owns `Context.lean` — no overlap)
  - `Cslib.lean` — one import line (on success only)
  - On failure: `specs/517_labelled_bounded_context_cs5_completeness/probes/adequacy-gate-probe.lean`
    (outside `Cslib/`, never imported by it)
- **Verification:**
  - **SUCCESS criterion**: Lemma 6.2.2, Lemma 6.1.2 (**including the reconstructed (⊥E) and (∨E)
    cases**), and Lemma 6.2.3 all close **sorry-free and axiom-clean** under `Cslib/`; `lake build`
    clean. → **Proceed to Waves 4–8; Phase 9 is reachable.**
  - **FAILURE criterion**: after **2 dispatches**, any of the above (most likely (⊥E)/(∨E)) remains
    unclosed. → **Land NOTHING under `Cslib/` for this phase.** Move partial work to
    `specs/517_.../probes/adequacy-gate-probe.lean`. Write
    `specs/517_.../handoffs/adequacy-gate-blocker-handoff.md` documenting precisely which case
    resisted and why (the shape of the goal, what was tried, whether it looks tedious or
    conceptually hard). Mark this phase `[BLOCKED]`. **Waves 4–8 still execute** — they are
    independently valuable and land a reusable labelled framework + countermodel construction.
    Phase 9 becomes unreachable; task → `[BLOCKED]`. **Never accrue a `sorry`.**
  - Either way: report the verdict explicitly to the orchestrator. **The gate verdict is the single
    most important output of this task's first half.**
  - **Dispatch 1 of 2 verdict (recorded here): GATE FAIL.** Lemma 6.2.2 (hard direction) complete;
    Lemma 6.1.2/6.2.3 not reached. See
    `specs/517_.../handoffs/adequacy-gate-blocker-handoff.md` for the full diagnosis and
    `specs/517_.../probes/adequacy-gate-probe.lean` for the reusable mechanization.
  - **Dispatch 2 of 2 verdict (FINAL): GATE FAIL.** Per the "bounded attempt: 2 dispatches, do not
    open a third" constraint above, this phase is now marked `[BLOCKED]` for good and no further
    dispatch will be attempted on this task. Dispatch 2 (a) **corrected a significant
    transcription error** in this plan's own paraphrase of the internalizing formula (the outer
    telescoping connective is `□`, not `◇` as written above in the "Lemma 6.1.2" task item — see
    the handoff for the source-verified correct formula and why the error mattered), (b) built and
    fully verified (sorry-free, axiom-clean) a substantial reusable scaffold covering ~11 of 15
    `NIKAx` cases on paper (`LTree`, `star`/`Star`, `box_mono1`/`box_mono2`/`wrapClosed`/
    `Star_imp1`/`Star_imp2`/`Star_append`, in `specs/517_.../probes/lemma612-scaffold.lean`), and
    (c) found a **new, deeper obstruction** in the `(◇E)` rule: `NIKAx.diaE`'s Lean type does not
    scope its `z` parameter relative to `x`, requiring an unproven well-scopedness invariant on
    top of Simpson's own "dissection" tree-surgery (Figure 6-2) before the rule can be
    internalized. See `specs/517_.../handoffs/lemma612-final-blocker.md` for the complete
    diagnosis, the corrected formula, the verified toolkit, and the precise remaining gap. **No
    third dispatch will be opened; per Rollback/Contingency, Phases 4-8 stand as landed and the
    task returns to `[BLOCKED]`.**

---

### Phase 4: Contexts and 𝒯-primeness [COMPLETED]

- **Goal:** Land `Context` and `TPrime` with all five clauses, and fix `𝒯_S5 := {χ_T, χ_5}`.
- **Tasks:**
  - [x] Read report 01 §"Deliverable 1c". Statements from report 01 / source PDF **only**
        (verified against the `pdftotext -layout` extraction of the source PDF directly,
        `:5941-6040`, since the corpus warning applies).
  - [x] Define **`Context (G, Γ)`** (`:5941`): `G` contains every prefix in `Γ`, and (1) the
        underlying set of `G` is `⊆ W(V')` for some **coinfinite** `V'`; (2) `v_{x:◇A} ∈ G` only if
        `xRv_{x:◇A}` in `G` and `v_{x:◇A}:A ∈ Γ`; (3) the **geometric-witness closure condition**.
        *(deviation: altered -- `Context.Γ` is typed `Set (LabelledFormula Atom)`, not `List`,
        because Phase 5's Zorn poset must take unions of chains that may be infinite; `NIK`'s
        `List`-typed judgement is bridged via a new `Deriv` relation. Flagged in the module
        docstring, "Design decision", as the one definitional choice not dictated verbatim by
        this checklist.)*
  - [x] Land clause (3) as a **separate `def` + closure lemma** — it is the fiddly one and Phase 5's
        Zorn will need it cleanly factored. *(deviation: altered -- `GeomWitnessClosure` is
        vacuously `True` under the present `Label` type, since Phase 1 elided the `k`-ary
        geometric-sequent witness operators (only the unary `dwitness` exists) and `𝒯_S5`'s two
        axioms are both universal Horn with no existential conclusion, hence need no Skolem
        witness. Documented explicitly rather than silently omitted; `@[nolint unusedArguments]`
        added since the linter correctly flags the unused parameters of a deliberately-vacuous
        `Prop`.)*
  - [x] Define **`TPrime (G, Γ)`** (`:5953`): **clause 0 —`G` is a classical model of `𝒯`** — plus
        1. `Γ ⊢_G x:A ⟹ x:A ∈ Γ` (**Deductive closure**)
        2. `∀x` in `G`, `Γ ⊬_G x:⊥` (**Consistency**) ← **this is what banishes `Ω`; it is
           load-bearing for the `cs5Incest_forces_symm` guardrail analysis (Phase 8)**
        3. `x:A∨B ∈ Γ ⟹ x:A ∈ Γ ∨ x:B ∈ Γ` (**Disjunction property**)
        4. `x:◇A ∈ Γ ⟹ ∃y. xRy in G ∧ y:A ∈ Γ` (**Diamond property**)
        All four proved as *defining clauses* (structure fields), not derived; Consistency is
        stated exactly as `∀ x ∈ G.X, ¬ Deriv 𝒯 G Γ (x ∶ ⊥)`.
  - [x] Define the basic geometric theory `𝒯` over `R` (reused `GeomAxiom`/`ClassicalModel` from
        Phase 2's `Deduction.lean`) and fix **`𝒯_S5 := {χ_T, χ_5}`** (`IS5 = IKT5`; `:3827`). Proved
        reflexive + euclidean ⟹ **equivalence relation** (`equivalence_of_refl_eucl`,
        `equivalence_of_classicalModel_TS5`); Phase 8 consumes it.
  - [x] **Use Simpson's geometric-theory presentation, NOT Marin's `klmn` condition** (report 01
        §Confidence): `cs5FCIncest` is only *derived* at the end, in Phase 8. Confirmed: this file
        does not reference `cs5FCIncest`, `klmn`, or any Marin-style frame condition.
  - [x] Add `public import` for `Labelled.Context` to `Cslib.lean`.
- **Timing:** 2 hours (~180–220 lines; landed ~320 lines with the `Deriv` bridge and extensive
  docstrings covering the flagged definitional choice and the guardrail analysis)
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Context.lean` — new (owned; **territory
    contract**: Phase 3 runs in parallel and owns `Adequacy.lean` — no overlap)
  - `Cslib.lean` — one import line
- **Verification:**
  - `lake build` clean; zero `sorry`, zero new `axiom`.
  - All five `TPrime` clauses present; **Consistency is a defining clause** (not derived).
  - `𝒯_S5`-reflexive-+-euclidean ⟹ equivalence-relation lemma proved.
  - **Do NOT reuse or generalize `QuasiPrime`** (`Segment.lean:64`) — it admits `Ω = univ`.
    Confirm by grep that `QuasiPrime` is not referenced.

---

### Phase 5: Prime Lemma 5.3.1 — Zorn over whole contexts [NOT STARTED]

- **Goal:** Prove **Prime Lemma 5.3.1** (`:5990`): "If `(G,Γ)` is a context and `Γ ⊬_G x:A` then
  there is a **𝒯-prime context** `(H,Δ) ⊇ (G,Γ)` such that `Δ ⊬_H x:A`."
- **This is the structural heart of Route B.** A context is **one object** carrying **all labels at
  once**, so a **single** Zorn maximalises `Θ(y)` for **every** label **simultaneously**, subject to
  **one global constraint** `Γ' ⊬ x:A`. **The cross-world invariants (`boxInv Θ(y) ⊆ Θ(z)` for
  `yRz`) are NOT constraints on the Zorn — they are CONSEQUENCES of deductive closure under `(□E)`.**
  This is exactly the "simultaneous maximal pair" `CS5.lean:700-710` named as the missing object, and
  it is why this escapes task-512's wall.
- **Tasks:**
  - [ ] Read report 01 §"Deliverable 5" (the mechanism) and the S1 row. Statements from report 01 /
        source PDF **only**.
  - [ ] Set up the Zorn poset
        `C = {(G',Γ') ⊇ (G,Γ) | underlying set ⊆ W(V'), Γ' ⊬ x:A}`; prove **chains close under
        union**.
  - [ ] Apply `zorn_subset` / Mathlib's Zorn to obtain a maximal element.
  - [ ] Verify the maximal element satisfies **all five** 𝒯-prime clauses. For **clause 0**
        (`H ⊨_cl 𝒯`), follow `:6010–6040`: "we show that `H ⊨_cl χ` … if it were not then
        `Δ ⊢_H x:A` would be derivable by an application of `(R_χ)`". **Symmetry is free and
        structural here** — exactly as `cs5Tail_symm` (`CS5.lean:645`) is free on the CSLib side.
        **It was never the gap, in either framework.**
  - [ ] Handle the **geometric-witness closure condition** (context clause 3) through the chain
        union — the fiddly part; reuse Phase 4's factored closure lemma.
  - [ ] **Do NOT** reuse `SegmentLindenbaum`'s engine (`quasi_prime_exclusion:73`,
        `box_refuting_theory:177`, `dia_refuting_theory:203`, `quasi_head_realization:251`). Its
        **fixed-other-component shape IS the bug** that destabilised task 512 Phases 8–10. Confirm
        by grep that `SegmentLindenbaum` is not imported.
  - [ ] Add `public import` for `Labelled.PrimeLemma` to `Cslib.lean`.
- **Timing:** 3 hours (~300–350 lines)
- **Depends on:** 4
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/PrimeLemma.lean` — new (owned)
  - `Cslib.lean` — one import line
- **Verification:**
  - `lake build` clean; zero `sorry`, zero new `axiom`.
  - Prime Lemma 5.3.1 closes; all five 𝒯-prime clauses discharged at the maximal element.
  - Grep confirms **no import of `SegmentLindenbaum`** and **no reference to `QuasiPrime`**.
  - The Zorn carries **exactly one** global constraint (`Γ' ⊬ x:A`) — **no cross-world invariant is
    threaded through it**. If a phase finds itself adding such a constraint, **stop**: that is the
    task-512 failure shape.

---

### Phase 6: Canonical model `K^𝒯` + Canonical Model Lemma 5.3.2 (truth lemma) [NOT STARTED]

- **Goal:** Build the canonical I𝒯-model `K^𝒯` and prove **Lemma 5.3.2** (`:6102`): "For all
  𝒯-prime contexts `(H,Δ)`, for all `y` in `H`, `(H,Δ),y ⊩_{K^𝒯} B` **iff** `y:B ∈ Δ`."
- **Tasks:**
  - [ ] Read report 01 §"Deliverable 1d/1e/1f". Statements from report 01 / source PDF **only**.
  - [ ] Define **IL-models** (`:5709–5760`): `K = (W, ≤, {D_w}, {R_w}, {a_w})` with the satisfaction
        clauses at `:5722` — note `w,d ⊩ □A iff ∀w' ≥ w, ∀d' ∈ D_w', R_w'(d,d') → w',d' ⊩ A`. A
        model is an **I𝒯-model** if for all `w`, the graph `(D_w, R_w)` is a **classical model of
        `𝒯`** (`:5759`).
  - [ ] Define **`K^𝒯`** (`:5987`): `W^𝒯` = 𝒯-prime contexts; `(H,Δ) ≤ (H',Δ') iff (H,Δ) ⊆ (H',Δ')`;
        `D_{(H,Δ)}` = underlying set of `H`; `R_{(H,Δ)}(x,y) iff xRy in H`;
        `a_{(H,Δ)}(x) iff x:α ∈ Δ`.
  - [ ] Prove `K^𝒯` is an I𝒯-model (`:6098`): "`(D_{(H,Δ)}, R_{(H,Δ)}) ⊨_cl 𝒯` because `(D,R) = H`
        and `H ⊨_cl 𝒯` as `(H,Δ)` is 𝒯-prime". **The frame theory holds because it is PART OF
        𝒯-primeness (clause 0) — not because it is derived from theory-membership. This is the crux
        of guardrail non-triggering.**
  - [ ] Prove **Lemma 5.3.2** by case analysis on `B`. The atomic/`∧`/`∨`/`⊃` cases use the 𝒯-prime
        clauses; the `◇` case uses the Diamond property.
  - [ ] **The `□`-backward case — the money step** (`:6146–6176`). Follow Simpson exactly: given
        `∀(H',Δ') ≥ (H,Δ)`, `yRz` in `H'` ⟹ `z:B ∈ Δ'`, let `V'` be coinfinite with `H ⊆ W(V')`;
        **take any `z ∈ V \ V'`** (Phase 1's fresh-label supply); set `H₀ = H ∪ {yRz}`. Suppose for
        contradiction `Δ ⊬_{H₀} z:B`; **by the Prime Lemma (Phase 5)** get 𝒯-prime
        `(H',Δ') ⊇ (H₀,Δ)` with `Δ' ⊬_{H'} z:B` — contradiction. So `Δ ⊢_{H₀} z:B`; as `z ∈ V\V'`,
        `z` is not in `H`; therefore **by `(□I)`**, `Δ ⊢_H y:□B`; by deductive closure `y:□B ∈ Δ`.
  - [ ] Add `public import` for `Labelled.CanonicalModel` to `Cslib.lean`.
- **Timing:** 3 hours (~280–330 lines)
- **Depends on:** 5
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/CanonicalModel.lean` — new (owned)
  - `Cslib.lean` — one import line
- **Verification:**
  - `lake build` clean; zero `sorry`, zero new `axiom`.
  - Lemma 5.3.2 closes for **every** connective, `□`-backward included.
  - **GUARDRAIL CHECK (mandatory)**: the `□` clause **retains its `≤`-quantification over larger
    contexts**. **The box-backward witness MUST live in a strictly larger context `(H',Δ') ⊇ (H₀,Δ)`
    — NOT at a fixed head.** Fixing the head re-imposes exactly the hypothesis `q ∉ H` that makes
    `cs5_symmetric_tail_box_gap` (`CS5.lean:712`) fatal, and re-enters task-512's wall. There is
    **no bounded Lindenbaum, no pair-primeness, no symmetric-tail constraint** in this phase.
  - The witness is delivered by (i) a **fresh label** and (ii) the **Prime Lemma applied to the whole
    context at once**. If either is absent, the construction is wrong.

---

### Phase 7: `B_K` birelation construction + Lemma 8.1.2 + ◇-clause reconciliation [NOT STARTED]

- **Goal:** Build the cartesian birelation model `B_K` from an I𝒯-model `K`, prove Lemma 8.1.2, and
  **reconcile Simpson's `∃`-◇ clause with CSLib's Wijesekera `∀≤∃`-◇ clause**.
- **Tasks:**
  - [ ] Read report 01 §"Deliverable 4" (frame-class match) and §"Deliverable 3" (why §8.1's
        soundness failure is irrelevant). Statements from report 01 / source PDF **only**.
  - [ ] Define **`B_K`** (`:9560–9600`): worlds are pairs `(w,d)`;
        `(w,d) ≤' (w',d') iff w ≤ w' ∧ d = d'`; `(w,d) R' (w',d') iff w = w' ∧ R_w(d,d')`.
  - [ ] Prove **Lemma 8.1.2** (`:9779`) — reuse `ckforces_persistence` (`Forcing.lean:122`).
  - [ ] **Discharge the `R`-monotonicity-under-`≤` IL-model condition explicitly.** Simpson treats
        it as trivial; **it is real work in Lean**, and Phase 8's conjuncts 3 and 4 consume it.
  - [ ] **Reconcile the ◇ clauses — a real proof obligation, not a formality.** Simpson's ◇ is a
        plain `∃` with **no `≤`-quantification** (`:5722`); CSLib's `CKForces` (`Forcing.lean:67`)
        uses Wijesekera's `∀≤∃`. Prove they **coincide on `B_K`** (needs `R` monotone under `≤` +
        `ckforces_persistence`).
  - [ ] Set `botForces := λ_. False`, justified by 𝒯-primeness's **Consistency** clause (no world
        forces `⊥`) and `cs5_dia_bot_imp_bot` (`CS5.lean:740`). This discharges all five of
        `CKValidFC`'s `botForces` side conditions **vacuously** (`CKExtension.lean:90-94`).
  - [ ] **Note for the record (do NOT attempt)**: Simpson's §8.1 opens with a genuine counterexample
        — "the obvious statement of soundness for `N_IK` **fails**" (`:9549`, Figure 8-1) — repaired
        only by restricting `G` to a tree. **That restriction binds ONLY the soundness direction**
        (`:9613`: "nowhere in the proof of completeness have we used the assumption that `G` is a
        tree"). We need only completeness; soundness is already landed as `cs5_soundness_incest`.
  - [ ] Add `public import` for `Labelled.Birelation` to `Cslib.lean`.
- **Timing:** 2.5 hours (~200–250 lines)
- **Depends on:** 6
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Birelation.lean` — new (owned)
  - `Cslib.lean` — one import line
- **Verification:**
  - `lake build` clean; zero `sorry`, zero new `axiom`.
  - Lemma 8.1.2 closes; the **◇-clause reconciliation is proved, not assumed**.
  - `R`-monotonicity-under-`≤` is a **stated, proved lemma** (Phase 8 depends on it).
  - `botForces := λ_. False` justified from 𝒯-prime Consistency — **`B_K` has no `Ω`**.
  - **GUARDRAIL CHECK**: `B_K`'s `R'` must be **primitive graph data** (from `R_w`), **NOT derived
    from box-membership**. `cs5Incest_forces_symm` (`CS5Canonical.lean:643`) **applies** here and
    yields plain box-symmetry — that is a **true theorem about `B_K`, not a contradiction**, because
    `R_w` is genuinely symmetric (classical model of `{χ_T, χ_5}`). If `R'` ever becomes
    `r Γ Δ := boxInv Γ ⊆ Δ`, the construction has regressed to task 512's and is wrong.
  - **Do NOT reuse `CKSegment`/`Segment`/`SegmentLindenbaum`** — grep-confirm. `B_K`'s `≤'` **fixes
    the domain element and moves the context**; `Preorder (CKSegment)` (`Segment.lean:161`) is
    head-inclusion on a single theory and is **not** the same order.

---

### Phase 8: `B_K ⊨ cs5FCIncest` — the reuse win [NOT STARTED]

- **Goal:** Prove `B_K` satisfies `cs5FCIncest` (`CS5Canonical.lean:255`, five conjuncts at
  `:258-263`), unlocking reuse of `cs5_axiom_sound_incest` (`:278`) and `cs5_soundness_incest`
  (`:340`) **unchanged**.
- **Pre-verified in report 01 §"Frame-class match, verified"** — this is the lowest-risk phase.
  Independently corroborated by Simpson `:9966`: "given any I𝒯-model `K`, the model `B_K` **is
  indeed a birelation model of 𝒯**".
- **Tasks:**
  - [ ] Read report 01 §"Deliverable 4" frame-class match table.
  - [ ] Using `R_w` an equivalence relation (Phase 4's lemma: classical model of `{χ_T, χ_5}`) and
        `R` monotone under `≤` (Phase 7's lemma), prove each conjunct:
    - [ ] 1. `∀w, r w w` ← `R_w` **reflexive**
    - [ ] 2. `r w u → r u t → r w t` ← `R_w` **transitive**
    - [ ] 3. `r w u → u ≤ u' → r u' t → ∃v, w ≤ v ∧ r v t` ← witness `v := (w'',d)`; needs `R`
          monotone + transitive
    - [ ] 4. `r w u → u ≤ u' → ∃t, r u' t ∧ w ≤ t` ← witness `t := (w'',d)`; needs `R` monotone +
          symmetric
    - [ ] 5. `cs5Incest r` (`CS5Canonical.lean:234`) ← witness `u' := u`; needs `R_w` **plain
          symmetric**
  - [ ] Confirm `cs5_axiom_sound_incest` / `cs5_soundness_incest` apply to `B_K` **unchanged** — do
        **not** rework `cs5FCIncest` (task 512 Phase 4's landed definition; reworking it needs
        explicit human authorization).
  - [ ] Add `public import` for `Labelled.FrameClass` to `Cslib.lean`.
- **Timing:** 1.5 hours (~120–150 lines)
- **Depends on:** 7
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/FrameClass.lean` — new (owned)
  - `Cslib.lean` — one import line
- **Verification:**
  - `lake build` clean; zero `sorry`, zero new `axiom`.
  - All five `cs5FCIncest` conjuncts proved for `B_K`.
  - `cs5_axiom_sound_incest` / `cs5_soundness_incest` reused **without modification** —
    grep-confirm `cs5FCIncest` is **not redefined**.
  - **Regression check**: `cs5FC''` (task 509, `CKExtension.lean:184`) and
    `cs5_soundness_derivable''` (`CS5.lean:460`) **untouched** — grep-confirm.

---

### Phase 9: `CS5ModalAxiom ≡ IK + Ax(𝒯_S5)` + assembly of `cs5_completeness` [NOT STARTED]

- **Goal:** Close the Hilbert-level correspondence (C0) and assemble
  `cs5_completeness : CKValidFC cs5FCIncest φ → Derivable CS5ModalAxiom φ`.
- **Tasks:**
  - [ ] Prove **C0**: `CS5ModalAxiom` (`CS5.lean:182`, 17 cases) ≡ `IK + Ax({χ_T, χ_5})`, both
        directions. Licensed by **`CS5 ≡ IS5`** (Pacheco `Pacheco2024` Thm 13; `CS5.lean:93-99`) —
        **load-bearing**. Theorem 6.2.1 (`:6880`) covers this: "**For any
        `𝒯 ⊆ {χ_D, χ_T, χ_B, χ_4, χ_5}`**, `IK + Ax(𝒯)` is just the appropriate `IKS₁…Sₙ`."
  - [ ] Assemble the contrapositive: `¬Derivable_CS5 φ ⟹` (C0) `⊬_{IK+Ax(𝒯_S5)} φ ⟹` (Phase 3
        adequacy) `⊬_{N_IK(𝒯_S5)} x:φ ⟹` (Phase 5 Prime Lemma) a 𝒯-prime context refuting `φ ⟹`
        (Phase 6 truth lemma) `K^𝒯 ⊮ φ ⟹` (Phase 7 `B_K` + Lemma 8.1.2) `B_K ⊮ φ`, with
        `B_K ⊨ cs5FCIncest` (Phase 8) ⟹ `¬ CKValidFC cs5FCIncest φ`.
  - [ ] State `cs5_completeness` and, if useful, a `cs5_soundness_completeness` iff-form combining
        it with `cs5_soundness_derivable_incest` (`CS5Canonical.lean:373`).
  - [ ] Add `public import` for `Labelled.CS5Completeness` to `Cslib.lean`.
  - [ ] Cite BibKeys in the module docstring: `Simpson1994` (**Ch. 5–6**), `Pacheco2024`,
        `MarinMoralesStrassburger2021`, `Dosen1985`, `BozicDosen1984`,
        `AlechinaMendlerdePaivaRitter2001`, `Wijesekera1990`.
- **Timing:** 2 hours (~150–200 lines)
- **Depends on:** 3, 8
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/CS5Completeness.lean` — new (owned)
  - `Cslib.lean` — one import line
- **Verification:**
  - `lake build` clean; zero `sorry`, zero new `axiom` under `Cslib/`.
  - `cs5_completeness` closes; `lean_verify` reports axiom-clean (no `sorryAx`, no new axioms).
  - **Unreachable if Phase 3 (gate) failed** — in that case this phase is not attempted and the task
    returns to `[BLOCKED]`.

---

## Testing & Validation

- [ ] `lake build` clean at **every** phase boundary.
- [ ] **Zero-debt invariant**: `grep -rn "sorry" Cslib/Logics/Modal/Metalogic/Constructive/Labelled/`
      returns nothing; `grep -rn "^axiom" Cslib/Logics/Modal/Metalogic/Constructive/Labelled/`
      returns nothing. Checked at every phase boundary, not just at the end.
- [ ] `lean_verify` on each landed top-level theorem — axiom-clean (no `sorryAx`).
- [ ] CSLib CI pipeline: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
      `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] **Regression suite (must not break)**: `CK`/`CT`/`CS4`/`CS5` soundness; task-509's `cs5FC''`
      (`CKExtension.lean:184`) and `cs5_soundness_derivable''` (`CS5.lean:460`); task-512's
      `cs5FCIncest`/`cs5_axiom_sound_incest`/`cs5_soundness_incest`; all four guardrail theorems
      (`cs5_symmetric_tail_box_gap`, `cs5Incest_forces_symm`, `cs5TwoSidedR_iff_cs5Tail`,
      `cs5Incest_cs5PrimeMreach_false`) still compile **unchanged**.
- [ ] **Non-reuse check**: `Labelled/` does not import `SegmentLindenbaum` and does not reference
      `QuasiPrime` or `CKSegment`.
- [ ] **Guardrail check**: no phase fixes the head in box-backward; `B_K`'s `R'` is primitive graph
      data, never `boxInv`-derived.

## Artifacts & Outputs

- `specs/517_labelled_bounded_context_cs5_completeness/plans/01_labelled-framework.md` (this file)
- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/{Syntax,Deduction,Adequacy,Context,PrimeLemma,CanonicalModel,Birelation,FrameClass,CS5Completeness}.lean`
- `Cslib.lean` — nine `public import` lines
- `specs/517_.../summaries/01_labelled-framework-summary.md` (on completion)
- On gate failure: `specs/517_.../probes/adequacy-gate-probe.lean` +
  `specs/517_.../handoffs/adequacy-gate-blocker-handoff.md`

## Rollback/Contingency

**Gate failure (Phase 3) — the expected failure mode, ~50% likely.** Do **not** open a third
dispatch. Phases 4–8 still execute and land a genuine, reusable **labelled framework + countermodel
construction** — independently valuable and the correct foundation for any future attempt. Phase 9
is unreachable. Task returns to **`[BLOCKED]`** with `handoffs/adequacy-gate-blocker-handoff.md`
documenting exactly which case resisted, the goal shape, what was tried, and whether the obstruction
looks **tedious** or **conceptually hard** (report 01 could not discharge this uncertainty from the
source: Simpson's "the difficulties are similar to those encountered in the (◇E) case" suggests
tedious-but-tractable, "but that is his word for it, not a proof"). **Never accrue a `sorry`.**

**Phase 2 blowup.** If the eigenvariable/freshness encoding exceeds 2× the line budget (~600 lines),
**stop and re-plan** rather than expanding in flight. Locally-nameless is the recommended encoding.

**Any other phase failure.** The phase lands nothing under `Cslib/`; partial work goes to
`specs/517_.../probes/`. Everything is additive — `git revert` of the phase commit restores the
prior state, since no existing file is modified beyond `Cslib.lean` import lines.

**Full rollback.** All work is confined to a new subdirectory plus nine import lines. Deleting
`Cslib/Logics/Modal/Metalogic/Constructive/Labelled/` and reverting `Cslib.lean` fully restores the
pre-task state. No landed soundness result is touched at any point.
</content>
</invoke>
