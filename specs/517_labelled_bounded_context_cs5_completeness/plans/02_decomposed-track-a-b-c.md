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

#### A1 — Repair `IKAx` to be actually IK  [COMPLETED]
- **Goal**: add Simpson's axioms 3 (`¬◇⊥`), 4 (`◇(A∨B) ⊃ (◇A ∨ ◇B)`), 5 (`(◇A ⊃ □B) ⊃ □(A ⊃ B)`) as
  constructors of `IKAx`.
- **Reused**: `IKAx` (`probes/lemma612-scaffold.lean:78`), `NIK_to_NIKAx` (`:229`),
  `TClosure.hilbertTransport` (`:185`), `IKDerivable` (`:112`), `IKAx.toIKDerivable` (`:121`).
- **Success**: `lake env lean probes/lemma612-scaffold.lean` exit 0, zero sorries; `#print axioms` on
  `NIK_to_NIKAx` and `TClosure.hilbertTransport` unchanged (adding constructors is non-breaking).
- **Risk**: LOW (mechanical). Needed for either track; in `probes/` so no `Cslib/` impact.

#### A2 — ROUTE PROBE: is `FS` derivable in CSLib's CS5?  [COMPLETED] — HIGHEST LEVERAGE
- **Goal**: attempt a sorry-free derivation of `FS := (◇ϕ → □ψ) → □(ϕ → ψ)` in CSLib `CS5`
  (`CS5ModalAxiom`, `CS5.lean:182`).
- **Why**: `FS` is the exact axiom Simpson's canonical model turns on (F2, p.53) and the exact thing
  task 512's box-backward was missing. CS5 ≡ IS5 (Pacheco) ⟹ CS5 ⊢ FS *should* hold. **Decisive for
  BOTH task 517 and task 512.**
- **Outcome (this dispatch, `probes/fischer-servi-probe.lean`)**: **mixed, decisive.**
  - Syntactic `Derivable CS5ModalAxiom FS`: **left open, precisely diagnosed** (not proved, not
    refuted). `fs_context_relative_half` mechanizes the exact obstruction: the context-relative
    half (`[◇A→□B] ⊢ A→B`, via `T`'s two halves) succeeds unconditionally, but
    `DerivationTree.necessitation` requires an **empty**-context sub-derivation, so this cannot be
    lifted to `□(A→B)`. A short combinator-chain search (bBox-smuggling attempts) did not find a
    route within the dispatch's bound; genuine underivability was not proved either.
  - Semantic `CKValidFC cs5FC'' FS`: **proved, sorry-free, axiom-clean** (`fs_sound''` — `#print
    axioms` reports none). Uses *only* the `bBox`/`bDia`-supporting frame clauses (`hsymbox`,
    `hsymm`); no reflexivity/transitivity needed. This is the fact Track B's canonical-model route
    actually needs (Simpson's F2 confluence condition), independent of syntactic derivability.
- **Success criterion met**: a precisely documented outcome landed in `probes/`, decisive for
  routing (see A3 below).
- **Risk**: MED-HIGH, realized as "syntactic route inconclusive, semantic route de-risked."
  **HARD CAP honored: one dispatch, no further syntactic search opened.**

#### A3 — Route verdict (paper, no Lean)  [COMPLETED] — VERDICT: **NO-GO for Track B**

**(i) `cs5FC''` DOES coincide with `IS5`'s birelational semantics — CONFIRMED, GO on this point
alone.** Simpson Theorem 3.3.4 (source PDF chunk `2595838e1aa3954c`/`chunk_0068.md`): "the
birelation models for IT, IS4 and IS5 are those in which R is respectively reflexive, a preorder
[and] an equivalence relation" — i.e. `IS5`'s birelation-model class is exactly "R an equivalence
relation" *plus* the F1/F2 conditions every birelation model already carries (source PDF chunk
`c795a118f01c279b`/`chunk_0064.md`: "(F1) ensures that the monotonicity lemma holds... (F2)
means that formulae such as `¬◇A ⊃ □¬A` hold"). `cs5FC''` (`CKExtension.lean:184-189`) is
*exactly* this: reflexivity + plain transitivity + plain symmetry (= `r` an equivalence relation)
bundled with the `fourBox` clause (`r w u → u ≤ u' → r u' t → ∃v, w≤v ∧ r v t`, F1-shaped
re-basing) and `FCsym_box` (`r w u → u ≤ u' → ∃t, r u' t ∧ w≤t`, F2-shaped witness). This is a
faithful, literature-grounded match, independent of A2's `fs_sound''` (which is a *consequence*
of this coincidence, not additional evidence for it).

**(ii) Pacheco's `CKB≡IKB ⟹ CS5≡IS5` chain — DECISIVE BLOCKER FOUND, unrelated to A2's gap.**
Read Pacheco2024 in full (`~/Projects/Literature/pacheco_2024_.../chunk_0001.md`–`chunk_0020.md`,
all 20 chunks). Two findings:

1. **A2's syntactic gap does NOT block Theorem 13.** Theorem 13's proof (`CKB⊢ϕ ⟺ IKB⊢ϕ ⟺
   CKB⊨ϕ ⟺ IKB⊨ϕ`) is entirely semantic/canonical-model-based (Lemmas 14–20, Zorn's-lemma
   theory existence, a Truth Lemma by structural induction) — it never uses `CKB⊢FS` as a
   transported Hilbert lemma. Corollary 12 (`CKB⊨FS`, `CKB⊨DP`, `CKB⊨N`) is itself a *semantic*
   confluence fact (via de Groot–Shillito–Clouston's Theorem 11: forward+backward confluence of
   `∼` gives `DP`/`FS` validity), structurally the same *kind* of result as this dispatch's
   `fs_sound''`. So the open syntactic `CS5 ⊢ FS` question from A2 is orthogonal to Track B and
   was a red herring for gating purposes.

2. **A NEW, decisive blocker: Pacheco's canonical relation, extended to `CS5`, is already caught
   by task 512's mechanized wall.** Pacheco's CKB-canonical model (`chunk_0010.md`/`0011.md`,
   "Canonical model for CKB") defines `Γ ∼c Δ := Γ ⊆ Δ ∧ Δ ⊆ Γ♦` over `Wc := {Γ | Γ a CKB-theory}`
   (CKB-theories are `∨`-prime, MP-closed, `⊥`-free sets — i.e. quasi-prime theories, the *same*
   kind of object task 512's guardrails are about), with the intuitionistic order `≼c` = plain
   `⊆`. To reach `CS5` (`= CKB + T + 4`, needed to connect to `cs5_completeness`'s literal target
   `CKValidFC.{u,u} cs5FC'' φ → Derivable CS5ModalAxiom φ`), Track B's B2 must extend this
   construction with axiom `T`. But **once `T` (`□A→A`) is present, every canonical `CS5`-theory
   satisfies `boxInv Γ ⊆ Γ`** (if `□A∈Γ` then `A∈Γ` by `T`+MP) — so Pacheco's `∼c`'s first
   conjunct `Γ⊆Δ`, combined with `boxInv Γ ⊆ Γ`, already gives `boxInv Γ ⊆ Δ`. This is *exactly*
   the `hbox` hypothesis of CSLib's already-landed, axiom-free, relation-and-world-type-agnostic
   theorem `cs5Incest_forces_symm` (`CS5Canonical.lean:643-650`, task 512): for **any**
   `Preorder`-headed world type with `r w u → boxInv(head w) ⊆ head u`, `cs5Incest r`
   (`∃u', u≤u' ∧ r u' w`) forces `boxInv(head u) ⊆ head w`. Pacheco's CKB-models *require* `R`
   symmetric (his Def 7, "M is a CKB-model iff R is symmetric, forward confluent, and backward
   confluent") and he proves `∼c` symmetric (Lemma 15, `chunk_0011.md`) — plain symmetry trivially
   witnesses `cs5Incest` (`u' := u`, `le_refl`). So `cs5Incest_forces_symm`'s hypotheses are *both*
   satisfied by Pacheco's construction once extended to `CS5`, and its conclusion forces the
   canonical relation into `cs5Tail`-shape (`cs5TwoSidedR_iff_cs5Tail`, `CS5Canonical.lean:511`),
   which `cs5_symmetric_tail_box_gap` (task 509, `CS5.lean:712`, already mechanized) proves
   *cannot* admit the box-refuting witness box-backward needs. **This is not a hypothetical
   concern** — task 512's Phase-7 gate already tried *both* the one-sided-R route ("Marin Thm
   7.1") and the two-sided-R route (Simpson's literal diamond clause, `cs5TwoSidedR`, which
   `cs5TwoSidedR_iff_cs5Tail` shows is *extensionally identical* to Pacheco's second conjunct
   `Δ⊆Γ♦` under `cs5_boxInv_subset_iff` duality) and BOTH failed this exact way (task 512
   `blockers`, `last_updated 2026-07-15T15:03:35Z`: "Phase-7 gate FAILED with two axiom-free
   mechanized lemmas: `cs5Incest_forces_symm`... and `cs5TwoSidedR_iff_cs5Tail`... Root cause:
   CSLib identifies the intuitionistic `≤` with theory-inclusion; Simpson/Marin birelational `IS5`
   completeness needs `≤` as an INDEPENDENT preorder"). Task 516 already explored and *refuted*
   the "independent-`≤`" fix (report 01: "Simpson uses `≤` = subset VERBATIM, Section 3.3") — so
   there is no known escape hatch within a theory-inclusion-`≤` canonical model, and Pacheco's
   construction, once T-extended, is theory-inclusion-`≤` by definition (`≼c = ⊆`).

**Named blocking obligation (if this task or a future one wants to re-open Track B):** any
canonical model for `CS5` over theory-inclusion-ordered worlds whose accessibility relation is
forced symmetric (as any `CKB`/`IS5`-family construction requires, since `CS5 ⊇ B`) and satisfies
`r w u → boxInv(head w) ⊆ head u` (automatic once `T`-closure holds, which every `CS5`-theory
has) is provably forced into `cs5Tail`-shape by `cs5Incest_forces_symm`, hence cannot admit a
box-refuting witness, by `cs5_symmetric_tail_box_gap`. Escaping this requires either (a) an
independent-`≤` canonical model (already refuted as unfaithful to Simpson, task 516 report 01),
or (b) abandoning theory-inclusion worlds entirely for a genuinely different representation —
which is exactly what the labelled bounded-context framework (Phases 1/2/4, already landed) and
Track C's tree surgery are for. **No formal Lean reduction of this argument was attempted this
dispatch** (that would itself cost as much as attempting B1) — the argument is a direct
hypothesis-check against three already-mechanized, sorry-free/axiom-free theorems
(`cs5Incest_forces_symm`, `cs5TwoSidedR_iff_cs5Tail`, `cs5_symmetric_tail_box_gap`) plus a literal
reading of Pacheco2024's canonical-model definitions.

- **Verdict**: **NO-GO for Track B.** Do not open B1/B2/B3. Proceed to Track C.
- **Risk assessment retrospectively**: LOW (analysis, as planned) — correctly not skipped; skipping
  it would have spent B1's ~300-600 line canonical-model construction cost rediscovering a wall
  task 512 already mechanized.

### TRACK B — Semantic route  *(only on an A3 GO)* — **CLOSED, A3 = NO-GO, see A3 above**
- **B1**: mechanize CKB ≡ IKB (Pacheco §3, Lemmas 18-20; canonical model over CKB-theories, Zorn).
  **NOT executed** — A3 found Pacheco's canonical relation, once T-extended for CS5, is already
  caught by `cs5Incest_forces_symm`/`cs5TwoSidedR_iff_cs5Tail`/`cs5_symmetric_tail_box_gap`
  (task 512, already mechanized). Opening B1 would spend ~300-600 lines rediscovering this wall.
- **B2**: derive CS5 ≡ IS5 (Pacheco corollary). **NOT executed**, gated on B1.
- **B3**: mechanize the IS5 canonical model / Simpson Thm 3.3.4 (Fischer Servi 1984). **NOT
  executed**, gated on B1/B2. Fischer Servi 1984 remains NOT in the literature corpus (unchanged).
- **Confidence** (retrospective, superseded by A3's NO-GO): the plan's original 35-40% estimate
  did not anticipate the T-extension interaction with `cs5Incest_forces_symm`; actual: ~0%
  without a representation change (independent-`≤`, already refuted, or labelled contexts).

### TRACK C — Simpson tree surgery, decomposed  *(fallback; A3 = NO-GO, this is now ACTIVE)*
C1-C3 are pure formula-level work with ZERO tree dependency — dispatchable immediately, even in
parallel with Track A.

| # | Goal | Success criterion | Risk |
|---|---|---|---|
| C1 | `Tele`/`Conj` over `List (Proposition)`; port `Star_imp1/2` to `Tele`-congruence | compiles, sorry-free | LOW — **[COMPLETED]** this dispatch, `probes/track-c-c1-tele-conj.lean` (new file, sorry-free, axiom footprint `[propext, Classical.choice, Quot.sound]` matching the rest of CSLib's Metalogic infra — no new axioms). Generalized beyond the plan's literal ask: `Tele_imp1`/`Tele_imp2`/`impIntro`/`box_mono1`/`box_mono2` are parametric over any `Axioms : Proposition Atom → Prop` (not hard-wired to `IKAx 𝒯`), directly reusable by C2/C3 or any other axiom system without redeclaration. |
| C2 | (6.7): `◇Conj(V) ⊃ □Tele(V,◇A) ⊃ ◇Conj(V++[A])`, induction on V, axiom 2 (`kDia`, present) | sorry-free | LOW-MED — **[COMPLETED]** this dispatch, appended to `probes/track-c-c1-tele-conj.lean` (same file — cross-probe `import` does not resolve, these are standalone `lake env lean` files, not `lean_lib` source roots; physically sharing the file is the literal reuse-without-redeclaration the C1 entry called for). **Scoping correction, load-bearing**: the schema is stated for *nonempty* `V = p :: rest`, not all `V : List`. The literal `V = []` instance (`◇⊤ ⊃ □◇A ⊃ ◇A`) is refuted by a 3-world countermodel (`w₀Rw₁`, `w₁Rw₂`, `A` true only at `w₂`) — consistent with Simpson's own usage, where `V` is always nonempty at every call site (`y_j` always present). New combinators added beyond C1's toolkit: `dia_mono1` (kDia-direct, no necessitation) and generic `hAndI`/`hAndE1`/`hAndE2`/`hDiaK` hypothesis parameters. Sorry-free, axiom footprint `[propext, Classical.choice, Quot.sound]` (verified via `#print axioms` on `formula_6_7`/`formula_6_7_base`/`dia_mono1` — no new axioms, matches C1's footprint exactly). |
| C3 | (6.8): `(◇Conj(W) ⊃ □Tele(W,B)) ⊃ □Tele(W,B)`, induction on W, **axiom 5 (requires A1)** | sorry-free | LOW-MED — **[COMPLETED]** this dispatch, appended to `probes/track-c-c1-tele-conj.lean` (`derivable_imp_trans`, `formula_6_8`). **Base-case check result differs from C2's**: the `W = []` instance (`(◇⊤⊃□B)⊃□B`) IS a genuine IK theorem (semantic argument: at any world, either no `R`-successor exists so `◇⊤` is vacuously false, or one exists so `◇⊤` is true and forces `□B` directly by MP) — **no restatement needed**, `formula_6_8` holds for *all* `W` including `[]`. Proof structure: naive single `hFS`-instantiation at `φ:=Conj(W),ψ:=Tele(W,B)` does NOT close the goal (consequent mismatch `□(Conj(W)⊃Tele(W,B))` vs target `□Tele(W,B)`, and the bridging fact `(Conj(W)⊃Tele(W,B))⊃Tele(W,B)` is not a bare IPL tautology once `Conj(W)` has a `◇`-guarded tail — checked by hand for `W=[p,q]`, gets stuck deriving `◇q` from `p` alone). The real proof composes `hFS` once per level with the IH *relativized one `Tele [p]`-layer deeper* via `Tele_imp1`, via a new `derivable_imp_trans` transitivity combinator (also directly reusable by C7's (◇E) 3-step composition). Sorry-free, axiom footprint `[propext, Classical.choice, Quot.sound]` (verified via `#print axioms` on `derivable_imp_trans`/`formula_6_8` — no new axioms, matches C1/C2's footprint exactly). |
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
