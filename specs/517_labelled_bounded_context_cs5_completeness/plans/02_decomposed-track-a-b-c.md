# Implementation Plan: Task #517 — CS5 Completeness, Decomposed (Track A/B/C)

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Status**: [IN PROGRESS] (Phases 1,2,4 landed; adequacy gate failed 3×; re-planned per report 02)
- **Effort**: revised — Track A ~2 small dispatches; Track B/C conditional
- **Dependencies**: 509, 512, 516
- **Research Inputs**:
  - reports/02_adequacy-alternatives-and-technique.md (THE authoritative reframe; source-PDF grounded)
  - reports/01_labelled-bounded-context-method.md (superseded on the Ch.6 routing; framework map still valid)
  - handoffs/lemma612-final-blocker-dispatch3.md, lemma612-final-blocker.md, adequacy-gate-blocker-handoff.md
- **Artifacts**: plans/02_decomposed-track-a-b-c.md (this file); supersedes plans/01_labelled-framework.md
- **Standards**: plan-format.md; status-markers.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Report 02 delivered a decisive reframe after THREE failed adequacy-gate dispatches. The core finding:
**the Chapter-6 adequacy bridge (Simpson Lemma 6.1.2 / Theorem 6.2.1) is NOT on the critical path
to `cs5_completeness`** (~85%). Simpson proves IS5 completeness **directly in Chapter 3**
(Theorem 3.3.4, p.56) via a canonical birelation model citing Fischer Servi 1984 — it does not use
the labelled system. Plan 01's Phase 9 had the dependency arrow backwards.

**Unified diagnosis linking tasks 512 and 517** (report 02 §1.4): Simpson's IK canonical model proves
its confluence condition (F2) **"by axiom 5 of IK"** = `FS := (◇ϕ → □ψ) → □(ϕ → ψ)` (p.53). Both
task 512 (prime-theory canonical model for CS5) and task 517 (labelled route) have been attacking a
logic that **lacks `FS`**. Pacheco's method is *don't*: establish CS5 ≡ IS5 (his CKB≡IKB collapse
corollary), then work on the IK side where `FS` is available.

**5th mechanization defect** (report 02 §2.6, ~97%): the scaffold's `IKAx`
(`probes/lemma612-scaffold.lean:78-109`) is **not** Simpson's IK — it has only axioms 1–2 (`kBox`,
`kDia`), missing 3/4/5. Simpson's (□E) case (p.102) and formula (6.8) (p.104) explicitly require
axiom 5, so Lemma 6.1.2 was **never provable** against that scaffold, independent of the tree defects.

**Definition of done**: `cs5_completeness` / `cs5_soundness_completeness` lands sorry-free,
axiom-clean — via the shortest viable track. If no track proves viable at acceptable cost, the
landed labelled framework (Phases 1,2,4; ~789 lines, CI-green) is retained as an independent
contribution and CS5 completeness stays `[BLOCKED]` with a precise, documented obstruction.

**Zero-debt invariant**: no `sorry`, no new `axiom`, no vacuous `:= True` definitions under `Cslib/`
at any phase boundary. Partial work lives in `probes/` (sorry permitted there only).

**Base-rate warning (report 02 §5, on the record)**: every dispatch on this gate has found the
previous one's transcription subtly wrong — *including report 02 itself* (it found the `IKAx` defect
inside a file two dispatches certified "complete/reusable"). Discount any "this time it's right"
estimate accordingly. This is why the work is now decomposed into small, independently-falsifiable
parts rather than a monolithic gate.

### Preserved landed assets (do NOT redo)
- Phase 1 `Labelled/Syntax.lean` (202 lines) — labels, graphs, witness algebra. [COMPLETED]
- Phase 2 `Labelled/Deduction.lean` (312 lines) — `NIK`, `TClosure`, `NIK.weaken`. [COMPLETED]
- Phase 4 `Labelled/Context.lean` (275 lines) — `Context`, `TPrime` (Ω-banishing consistency),
  `Deriv`, `TS5`, `equivalence_of_refl_eucl`. [COMPLETED]
- `probes/adequacy-gate-probe.lean` — Lemma 6.2.2 hard direction (`NIK_to_NIKAx`), correct & reusable.
- `probes/lemma612-scaffold.lean` — LTree scaffold; DEFECTIVE in two places (§2.2/§2.3: `pathTo`/
  `pathToList` return full not pruned subtree; `Star_append` wrong) AND `IKAx` missing axioms 3/4/5.
- Known debt: `GeomWitnessClosure := True` + `GeomAxiom.D` trap (fix before any PR; drop `D` or require
  a no-existential-axioms proof).

## Goals & Non-Goals

**Goals**: pick the cheapest viable route to `cs5_completeness` and execute it, decomposed into
one-dispatch parts each with an independently-verifiable target.

**Non-Goals**:
- Do NOT open a 4th open-ended tree-surgery dispatch before Track A decides the route.
- Do NOT route `cs5_completeness` through Chapter 6 adequacy (it is not needed).
- Do NOT re-attempt any prime-theory canonical route for CS5 (task 512: mechanically dead).

## Phases

### TRACK A — Route selection + defect repair (do FIRST; both parts small)

#### A1 — Repair `IKAx` to be actually IK  [NOT STARTED]
- **Goal**: add Simpson's axioms 3 (`¬◇⊥`), 4 (`◇(A∨B) ⊃ (◇A ∨ ◇B)`), 5 (`(◇A ⊃ □B) ⊃ □(A ⊃ B)`) as
  constructors of `IKAx`.
- **Reused**: `IKAx` (`probes/lemma612-scaffold.lean:78`), `NIK_to_NIKAx` (`:229`),
  `TClosure.hilbertTransport` (`:185`), `IKDerivable` (`:112`), `IKAx.toIKDerivable` (`:121`).
- **Success**: `lake env lean probes/lemma612-scaffold.lean` exit 0, zero sorries; `#print axioms` on
  `NIK_to_NIKAx` and `TClosure.hilbertTransport` unchanged (adding constructors is non-breaking).
- **Risk**: LOW (mechanical). Needed for either track; in `probes/` so no `Cslib/` impact.

#### A2 — ROUTE PROBE: is `FS` derivable in CSLib's CS5?  [NOT STARTED] — HIGHEST LEVERAGE
- **Goal**: attempt a sorry-free derivation of `FS := (◇ϕ → □ψ) → □(ϕ → ψ)` in CSLib `CS5`
  (`CS5ModalAxiom`, `CS5.lean:182`).
- **Why**: `FS` is the exact axiom Simpson's canonical model turns on (F2, p.53) and the exact thing
  task 512's box-backward was missing. CS5 ≡ IS5 (Pacheco) ⟹ CS5 ⊢ FS *should* hold. **Decisive for
  BOTH task 517 and task 512.**
- **Success**: EITHER sorry-free `CS5 ⊢ FS`, OR a precisely documented failure naming the failing step.
  Both outcomes decisive. Land the attempt (or the negative writeup) in `probes/`.
- **Risk**: MED-HIGH (Pacheco's collapse is semantic; a direct syntactic derivation may not exist and
  may itself need the canonical model). **HARD CAP: one dispatch. Do not let this become a 4th gate.**

#### A3 — Route verdict (paper, no Lean)  [NOT STARTED]
- **Goal**: from A2's outcome, verify the two semantic-route preconditions: (i) does CS5's semantics
  (`Forcing.lean`, `cs5FC''` `CKExtension.lean:184`) coincide with IS5 birelation semantics (equiv R
  + F1/F2)? (ii) is the CKB≡IKB ⟹ CS5≡IS5 corollary chain sound as stated?
- **Success**: a written GO/NO-GO on Track B with a named blocking obligation if NO-GO.
- **Risk**: LOW (analysis) — but must NOT be skipped (task 512's 5 dispatches are the cost of skipping it).

### TRACK B — Semantic route  *(only on an A3 GO)*
- **B1**: mechanize CKB ≡ IKB (Pacheco §3, Lemmas 18-20; canonical model over CKB-theories, Zorn).
- **B2**: derive CS5 ≡ IS5 (Pacheco corollary).
- **B3**: mechanize the IS5 canonical model / Simpson Thm 3.3.4 (Fischer Servi 1984). **Fischer Servi
  1984 is NOT in the corpus — requires `/literature` ingestion first (real gap, not glossed).**
- **Confidence**: ~35-40%; A3 exists to sharpen this.

### TRACK C — Simpson tree surgery, decomposed  *(fallback; only if Track B is NO-GO)*
C1-C3 are pure formula-level work with ZERO tree dependency — dispatchable immediately, even in
parallel with Track A.

| # | Goal | Success criterion | Risk |
|---|---|---|---|
| C1 | `Tele`/`Conj` over `List (Proposition)`; port `Star_imp1/2` to `Tele`-congruence | compiles, sorry-free | LOW |
| C2 | (6.7): `◇Conj(V) ⊃ □Tele(V,◇A) ⊃ ◇Conj(V++[A])`, induction on V, axiom 2 (`kDia`, present) | sorry-free | LOW-MED |
| C3 | (6.8): `(◇Conj(W) ⊃ □Tele(W,B)) ⊃ □Tele(W,B)`, induction on W, **axiom 5 (requires A1)** | sorry-free | MED |
| C4 | `LTree`,`star`,`fullSubtree`,`prune` + the **unfolding identity** (§2.3); DELETE `pathTo`/`pathToList`/`Star_append` | `#eval`/`decide` reproduces Simpson's worked example verbatim | MED |
| C5 | `pathSpine` (pruning in the recursion) + `addChild`/`pathSpine` **commutation lemma** | sorry-free commutation lemma | **HIGH — TRUE CRUX** |
| C6 | `LTree.toGraph`; τ-parameterized induction; non-modal + (□I)/(□E)/(◇I) | listed cases sorry-free | MED |
| C7 | the (◇E) case via §2.5's 3-step argument | sorry-free | MED (given C5) |
| C8 | (⊥E)/(∨E) | sorry-free | LOW |

If Track C completes, THEN the adequacy bridge lands and Phase 9 (`cs5_completeness`) via the labelled
route becomes reachable — but Track B is preferred precisely because it avoids C5.

### Phase 9 (from plan 01) — `cs5_completeness` assembly
Reachable via Track B (canonical model directly) OR Track C (adequacy bridge + labelled canonical
model). Unchanged target: `cs5_completeness` / `cs5_soundness_completeness`, sorry-free, axiom-clean.

## Confidence (report 02 §5, deliberately conservative)
- `IKAx` missing axioms 3/4/5: ~97% · Bridge not needed for completeness: ~85% · CS5 ≡ IS5: ~90%
  math / ~60% "as immediate as one line" · Track B mechanizable at reasonable cost: ~35-40% ·
  Track C completes in 2-3 dispatches: ~25-30% · A2 (`CS5 ⊢ FS`) succeeds: ~40%.

## Recommendation (report 02 §6)
Do NOT open a 4th tree dispatch. Run **A1** then **A2** (both cheap). A2 is the highest-leverage
question in this task and in task 512. If the honest reading holds — the adequacy bridge is not worth
the cost because it is not needed — re-plan around Track A/B and keep the labelled framework as an
independent contribution decoupled from `cs5_completeness`.
