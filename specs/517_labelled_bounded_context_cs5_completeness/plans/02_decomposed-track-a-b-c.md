# Implementation Plan: Task #517 — CS5 Completeness, Decomposed (Track A/B/C)

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Status**: [IN PROGRESS]
- **Effort**: Track A complete (3 dispatches); Track C C1-C4 complete (4 dispatches); C5-C8 + assembly remaining (~4-6 dispatches, HIGH uncertainty)
- **Dependencies**: 509, 512, 516
- **Research Inputs**:
  - reports/02_adequacy-alternatives-and-technique.md (THE authoritative reframe; source-PDF grounded)
  - reports/01_labelled-bounded-context-method.md (superseded on the Ch.6 routing; framework map still valid)
  - handoffs/lemma612-final-blocker-dispatch3.md, lemma612-final-blocker.md, adequacy-gate-blocker-handoff.md
- **Artifacts**: plans/02_decomposed-track-a-b-c.md (this file); supersedes plans/01_labelled-framework.md
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Report 02 delivered a decisive reframe after THREE failed adequacy-gate dispatches: **the Chapter-6
adequacy bridge (Simpson Lemma 6.1.2 / Theorem 6.2.1) is NOT on the critical path to
`cs5_completeness`** (~85%). Simpson proves IS5 completeness directly in Chapter 3 (Theorem 3.3.4,
p.56) via a canonical birelation model citing Fischer Servi 1984 — it does not use the labelled
system. Plan 01's Phase 9 had the dependency arrow backwards. Scope: pick the cheapest viable route
to `cs5_completeness` and execute it, decomposed into one-dispatch parts each with an
independently-verifiable target.

**Definition of done**: `cs5_completeness` / `cs5_soundness_completeness` lands sorry-free,
axiom-clean, via the shortest viable track. If no track proves viable at acceptable cost, the landed
labelled framework (Phases 1,2,4 of plan 01; ~789 lines, CI-green) is retained as an independent
contribution and CS5 completeness is set to blocked status with a precise, documented obstruction.

**Zero-debt invariant**: no `sorry`, no new `axiom`, no vacuous `:= True` definitions under `Cslib/`
at any phase boundary. Partial work lives in `probes/` (sorry permitted there only).

#### Research Integration

- reports/02_adequacy-alternatives-and-technique.md — integrated in plan version 2. Supplies the
  reframe (§1.4 unified 512/517 diagnosis), the 5th mechanization defect (§2.6), and the base-rate
  warning (§5).
- reports/01_labelled-bounded-context-method.md — integrated in plan version 1; superseded on Ch.6
  routing only.

#### Preserved landed assets (do NOT redo)

- Phase 1 `Labelled/Syntax.lean` (202 lines) — labels, graphs, witness algebra.
- Phase 2 `Labelled/Deduction.lean` (312 lines) — `NIK`, `TClosure`, `NIK.weaken`.
- Phase 4 `Labelled/Context.lean` (275 lines) — `Context`, `TPrime` (Ω-banishing consistency),
  `Deriv`, `TS5`, `equivalence_of_refl_eucl`.
- `probes/adequacy-gate-probe.lean` — Lemma 6.2.2 hard direction (`NIK_to_NIKAx`), correct & reusable.
- Known debt: `GeomWitnessClosure := True` + `GeomAxiom.D` trap (fix before any PR; drop `D` or
  require a no-existential-axioms proof).

## Goals & Non-Goals

- **Goals**:
  - Pick the cheapest viable route to `cs5_completeness` and execute it, decomposed into
    one-dispatch parts each with an independently-verifiable target.
  - Keep every landed artifact sorry-free and axiom-clean at each phase boundary.
- **Non-Goals**:
  - Do NOT open a 4th open-ended tree-surgery dispatch before Track A decides the route.
  - Do NOT route `cs5_completeness` through Chapter 6 adequacy (it is not needed).
  - Do NOT re-attempt any prime-theory canonical route for CS5 (task 512: mechanically dead).

## Risks & Mitigations

- **Risk**: Base-rate warning (report 02 §5) — every dispatch on this gate has found the previous
  one's transcription subtly wrong, *including report 02 itself* (it found the `IKAx` defect inside a
  file two dispatches certified "complete/reusable").
  **Mitigation**: decompose into small, independently-falsifiable parts; verify each against the
  source PDF before writing Lean. Discount any "this time it's right" estimate.
- **Risk**: Transcribed formula schemas may be false as literally stated (realized twice: Phase 8's
  `V=[]`, and Phase 10's defective `star`).
  **Mitigation**: mandatory semantic/countermodel sanity check on base cases BEFORE writing Lean;
  restate to match the source's actual usage and document the countermodel.
- **Risk**: Track C's crux (Phase 11) may not close, stranding Phases 12-15.
  **Mitigation**: Phase 11 gets a dedicated dispatch; on failure, record the precise obstruction and
  fall back to the Rollback/Contingency position (labelled framework as standalone contribution).
- **Risk**: Regression of landed CK/CT/CS4/CS5 soundness or task-509 `cs5FC''`.
  **Mitigation**: all Track A/C work confined to `probes/`; zero `Cslib/` files touched; reverify
  untouched declarations compile after each edit.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 7 | -- |
| 2 | 3, 8, 9, 10 | 1, 2, 7 |
| 3 | 4, 11 | 3, 10 |
| 4 | 5, 12 | 4, 10, 11 |
| 5 | 6, 13, 14 | 5, 11, 12 |
| 6 | 15 | 12, 13, 14 |

Phases within the same wave can execute in parallel.

Track A (Phases 1-3) = route selection + defect repair. Track B (Phases 4-6) = semantic route,
gated on a Phase 3 GO. Track C (Phases 7-14) = Simpson tree surgery, the fallback. Phase 15 =
final assembly. Phases 7-9 are pure formula-level work with ZERO tree dependency.

### Phase 1: Track A1 — Repair `IKAx` to be actually IK [COMPLETED]
- **Goal:** Add Simpson's axioms 3 (`¬◇⊥`), 4 (`◇(A∨B) ⊃ (◇A ∨ ◇B)`), 5 (`(◇A ⊃ □B) ⊃ □(A ⊃ B)`) as
  constructors of `IKAx`. The scaffold's `IKAx` had only axioms 1-2 (`kBox`, `kDia`), so Lemma 6.1.2
  was never provable against it, independent of the tree defects (report 02 §2.6, ~97%).
- **Tasks:**
  - [x] Add `diaBot`, `diaOr`, `fs` as unconditional `IKAx` constructors
  - [x] Verify `lake env lean probes/lemma612-scaffold.lean` exit 0, zero sorries
  - [x] Confirm `#print axioms` on `NIK_to_NIKAx` / `TClosure.hilbertTransport` unchanged
- **Timing:** one small dispatch (mechanical, additive)
- **Depends on:** none
- **Reused:** `IKAx` (`probes/lemma612-scaffold.lean:78`), `NIK_to_NIKAx` (`:229`),
  `TClosure.hilbertTransport` (`:185`), `IKDerivable` (`:112`), `IKAx.toIKDerivable` (`:121`)
- **Risk:** LOW (mechanical). Needed for either track; in `probes/` so no `Cslib/` impact.
- **Completed:** 2026-07-15T13:17:58-07:00 (commit `2bd1e3a6`)

### Phase 2: Track A2 — Route probe: is `FS` derivable in CSLib's CS5? [COMPLETED]
- **Goal:** Attempt a sorry-free derivation of `FS := (◇ϕ → □ψ) → □(ϕ → ψ)` in CSLib `CS5`
  (`CS5ModalAxiom`, `CS5.lean:182`). `FS` is the exact axiom Simpson's canonical model turns on (F2,
  p.53) and the exact thing task 512's box-backward was missing. Decisive for BOTH task 517 and 512.
- **Tasks:**
  - [x] Attempt syntactic `Derivable CS5ModalAxiom FS`
  - [x] Mechanize the obstruction if the attempt does not close
  - [x] Prove the semantic counterpart `CKValidFC cs5FC'' FS`
  - [x] Verify sorry-free; `#print axioms` on each new result
- **Timing:** one dispatch — HARD CAP, no further syntactic search opened
- **Depends on:** none
- **Outcome (`probes/fischer-servi-probe.lean`): mixed, decisive.**
  - Syntactic `Derivable CS5ModalAxiom FS`: **left open, precisely diagnosed** (not proved, not
    refuted). `fs_context_relative_half` mechanizes the exact obstruction: the context-relative half
    (`[◇A→□B] ⊢ A→B`, via `T`'s two halves) succeeds unconditionally, but
    `DerivationTree.necessitation` requires an **empty**-context sub-derivation, so this cannot be
    lifted to `□(A→B)`. A short combinator-chain search (bBox-smuggling) found no route within the
    dispatch bound; genuine underivability was not proved either.
  - Semantic `CKValidFC cs5FC'' FS`: **proved, sorry-free, axiom-clean** (`fs_sound''` — `#print
    axioms` reports none). Uses *only* the `bBox`/`bDia`-supporting frame clauses (`hsymbox`,
    `hsymm`); no reflexivity/transitivity needed. This is the fact Track B's canonical-model route
    actually needs (Simpson's F2 confluence condition), independent of syntactic derivability.
- **Risk:** MED-HIGH, realized as "syntactic route inconclusive, semantic route de-risked."
- **Completed:** 2026-07-15T13:17:58-07:00 (commit `2bd1e3a6`)

### Phase 3: Track A3 — Route verdict (paper, no Lean) [COMPLETED]
- **Goal:** From Phase 2's outcome, verify the two semantic-route preconditions and issue a written
  GO/NO-GO on Track B with a named blocking obligation if NO-GO.
- **Tasks:**
  - [x] (i) Check whether `cs5FC''` coincides with IS5 birelational semantics (equiv R + F1/F2)
  - [x] (ii) Check whether Pacheco's `CKB≡IKB ⟹ CS5≡IS5` chain is sound as stated, and whether
        Phase 2's open syntactic gap blocks any step Track B needs
  - [x] Record verdict + named blocking obligation
- **Timing:** one dispatch (analysis only)
- **Depends on:** 2
- **Verdict: NO-GO for Track B.** Do not open Phases 4-6. Proceed to Track C.

**(i) `cs5FC''` DOES coincide with IS5's birelational semantics — CONFIRMED, GO on this point
alone.** Simpson Theorem 3.3.4 (source PDF chunk `2595838e1aa3954c`/`chunk_0068.md`): "the
birelation models for IT, IS4 and IS5 are those in which R is respectively reflexive, a preorder
[and] an equivalence relation" — i.e. IS5's birelation-model class is exactly "R an equivalence
relation" *plus* the F1/F2 conditions every birelation model already carries (chunk
`c795a118f01c279b`/`chunk_0064.md`: "(F1) ensures that the monotonicity lemma holds... (F2) means
that formulae such as `¬◇A ⊃ □¬A` hold"). `cs5FC''` (`CKExtension.lean:184-189`) is *exactly* this:
reflexivity + plain transitivity + plain symmetry (= `r` an equivalence relation) bundled with the
`fourBox` clause (`r w u → u ≤ u' → r u' t → ∃v, w≤v ∧ r v t`, F1-shaped re-basing) and `FCsym_box`
(`r w u → u ≤ u' → ∃t, r u' t ∧ w≤t`, F2-shaped witness). A faithful, literature-grounded match,
independent of Phase 2's `fs_sound''` (which is a *consequence* of this coincidence, not additional
evidence for it).

**(ii) Pacheco's `CKB≡IKB ⟹ CS5≡IS5` chain — DECISIVE BLOCKER FOUND, unrelated to Phase 2's gap.**
Read Pacheco2024 in full (`~/Projects/Literature/pacheco_2024_.../chunk_0001.md`–`chunk_0020.md`).
Two findings:

1. **Phase 2's syntactic gap does NOT block Theorem 13.** Theorem 13's proof (`CKB⊢ϕ ⟺ IKB⊢ϕ ⟺
   CKB⊨ϕ ⟺ IKB⊨ϕ`) is entirely semantic/canonical-model-based (Lemmas 14-20, Zorn's-lemma theory
   existence, a Truth Lemma by structural induction) — it never uses `CKB⊢FS` as a transported
   Hilbert lemma. Corollary 12 (`CKB⊨FS`, `CKB⊨DP`, `CKB⊨N`) is itself a *semantic* confluence fact
   (via de Groot–Shillito–Clouston's Theorem 11), structurally the same kind of result as Phase 2's
   `fs_sound''`. The open syntactic `CS5 ⊢ FS` question is orthogonal to Track B and was a red
   herring for gating purposes.

2. **A NEW, decisive blocker: Pacheco's canonical relation, extended to CS5, is already caught by
   task 512's mechanized wall.** Pacheco's CKB-canonical model (`chunk_0010.md`/`0011.md`) defines
   `Γ ∼c Δ := Γ ⊆ Δ ∧ Δ ⊆ Γ♦` over `Wc := {Γ | Γ a CKB-theory}` (CKB-theories are `∨`-prime,
   MP-closed, `⊥`-free — i.e. quasi-prime theories, the *same* kind of object task 512's guardrails
   are about), with intuitionistic order `≼c` = plain `⊆`. To reach CS5 (`= CKB + T + 4`, needed to
   connect to `cs5_completeness`'s literal target `CKValidFC.{u,u} cs5FC'' φ → Derivable
   CS5ModalAxiom φ`), Phase 5 must extend this with axiom `T`. But **once `T` (`□A→A`) is present,
   every canonical CS5-theory satisfies `boxInv Γ ⊆ Γ`** (if `□A∈Γ` then `A∈Γ` by `T`+MP) — so
   `∼c`'s first conjunct `Γ⊆Δ`, combined with `boxInv Γ ⊆ Γ`, already gives `boxInv Γ ⊆ Δ`. This is
   *exactly* the `hbox` hypothesis of CSLib's landed, axiom-free, relation-and-world-type-agnostic
   `cs5Incest_forces_symm` (`CS5Canonical.lean:643-650`, task 512): for **any** `Preorder`-headed
   world type with `r w u → boxInv(head w) ⊆ head u`, `cs5Incest r` (`∃u', u≤u' ∧ r u' w`) forces
   `boxInv(head u) ⊆ head w`. Pacheco's CKB-models *require* `R` symmetric (Def 7) and he proves
   `∼c` symmetric (Lemma 15, `chunk_0011.md`) — plain symmetry trivially witnesses `cs5Incest`
   (`u' := u`, `le_refl`). So both hypotheses are satisfied once extended to CS5, and the conclusion
   forces the canonical relation into `cs5Tail`-shape (`cs5TwoSidedR_iff_cs5Tail`,
   `CS5Canonical.lean:511`), which `cs5_symmetric_tail_box_gap` (task 509, `CS5.lean:712`) proves
   *cannot* admit the box-refuting witness box-backward needs. **Not hypothetical** — task 512's
   Phase-7 gate already tried *both* the one-sided-R route and the two-sided-R route (`cs5TwoSidedR`,
   extensionally identical to Pacheco's second conjunct `Δ⊆Γ♦` under `cs5_boxInv_subset_iff`
   duality) and BOTH failed this exact way. Task 516 already refuted the "independent-`≤`" fix
   (report 01: "Simpson uses `≤` = subset VERBATIM, Section 3.3") — and Pacheco's construction, once
   T-extended, is theory-inclusion-`≤` by definition (`≼c = ⊆`).

**Named blocking obligation (to re-open Track B):** any canonical model for CS5 over
theory-inclusion-ordered worlds whose accessibility relation is forced symmetric (as any CKB/IS5-family
construction requires, since `CS5 ⊇ B`) and satisfies `r w u → boxInv(head w) ⊆ head u` (automatic
once `T`-closure holds) is provably forced into `cs5Tail`-shape by `cs5Incest_forces_symm`, hence
cannot admit a box-refuting witness, by `cs5_symmetric_tail_box_gap`. Escaping this requires either
(a) an independent-`≤` canonical model (refuted as unfaithful to Simpson, task 516 report 01), or
(b) abandoning theory-inclusion worlds entirely for a genuinely different representation — which is
exactly what the labelled bounded-context framework and Track C's tree surgery are for. No formal
Lean reduction of this argument was attempted (that would cost as much as attempting Phase 4); the
argument is a direct hypothesis-check against three already-mechanized, sorry-free/axiom-free
theorems plus a literal reading of Pacheco2024's canonical-model definitions.

- **Risk:** LOW (analysis, as planned) — correctly not skipped; skipping it would have spent Phase
  4's ~300-600 line cost rediscovering a wall task 512 already mechanized.
- **Completed:** 2026-07-15T13:34:05-07:00 (commit `cc7edf4c`)

### Phase 4: Track B1 — Mechanize CKB ≡ IKB [BLOCKED]
- **Goal:** Mechanize CKB ≡ IKB (Pacheco §3, Lemmas 18-20; canonical model over CKB-theories, Zorn).
- **Tasks:**
  - [ ] Not executed — see Phase 3 verdict
- **Timing:** ~300-600 lines (not spent)
- **Depends on:** 3
- **Blocked:** 2026-07-15T13:34:05-07:00 — Phase 3 verdict = NO-GO. Pacheco's canonical relation,
  once T-extended for CS5, is already caught by `cs5Incest_forces_symm` /
  `cs5TwoSidedR_iff_cs5Tail` / `cs5_symmetric_tail_box_gap` (task 512, already mechanized). Opening
  this phase would spend ~300-600 lines rediscovering that wall. See Phase 3's named blocking
  obligation for the condition under which this may be re-opened.

### Phase 5: Track B2 — Derive CS5 ≡ IS5 [BLOCKED]
- **Goal:** Derive CS5 ≡ IS5 (Pacheco corollary).
- **Tasks:**
  - [ ] Not executed — gated on Phase 4
- **Timing:** not spent
- **Depends on:** 4
- **Blocked:** 2026-07-15T13:34:05-07:00 — transitively blocked by Phase 4.

### Phase 6: Track B3 — Mechanize the IS5 canonical model (Simpson Thm 3.3.4) [BLOCKED]
- **Goal:** Mechanize the IS5 canonical model / Simpson Theorem 3.3.4 (Fischer Servi 1984).
- **Tasks:**
  - [ ] Not executed — gated on Phases 4/5
- **Timing:** not spent
- **Depends on:** 5
- **Blocked:** 2026-07-15T13:34:05-07:00 — transitively blocked by Phase 4. Additionally,
  FischerServi1984 is NOT in the literature corpus and would need `/literature` ingestion first
  (now moot).

### Phase 7: Track C1 — `Tele`/`Conj` over `List (Proposition)` [COMPLETED]
- **Goal:** Define `Tele`/`Conj` over `List (Proposition)`; port `Star_imp1`/`Star_imp2` to
  `Tele`-congruence.
- **Tasks:**
  - [x] Define `Conj` / `Tele` (Simpson p.104)
  - [x] Port `Star_imp1`/`Star_imp2` to `Tele_imp1`/`Tele_imp2`
  - [x] Verify compiles, sorry-free; `#print axioms`
- **Timing:** one dispatch
- **Depends on:** none
- **Outcome:** `probes/track-c-c1-tele-conj.lean` (new file), sorry-free, axiom footprint
  `[propext, Classical.choice, Quot.sound]` matching CSLib's Metalogic infra — no new axioms.
  Generalized beyond the literal ask: `Tele_imp1`/`Tele_imp2`/`impIntro`/`box_mono1`/`box_mono2` are
  parametric over any `Axioms : Proposition Atom → Prop` (not hard-wired to `IKAx 𝒯`), directly
  reusable by Phases 8/9 without redeclaration.
- **Risk:** LOW
- **Completed:** 2026-07-15T13:34:05-07:00 (commit `cc7edf4c`)

### Phase 8: Track C2 — Simpson formula (6.7) [COMPLETED]
- **Goal:** Prove (6.7): `◇Conj(V) ⊃ □Tele(V,◇A) ⊃ ◇Conj(V++[A])` by induction on V, using axiom 2
  (`kDia`).
- **Tasks:**
  - [x] Sanity-check the schema before writing Lean
  - [x] Prove (6.7) by induction on V
  - [x] Verify sorry-free; `#print axioms`
- **Timing:** one dispatch
- **Depends on:** 7
- **Outcome:** appended to `probes/track-c-c1-tele-conj.lean` (same file — cross-probe `import` does
  not resolve; these are standalone `lake env lean` files, not `lean_lib` source roots, so physically
  sharing the file is the literal reuse-without-redeclaration Phase 7 called for).
  **Scoping correction, load-bearing**: the schema is stated for *nonempty* `V = p :: rest`, not all
  `V : List`. The literal `V = []` instance (`◇⊤ ⊃ □◇A ⊃ ◇A`) is refuted by a 3-world countermodel
  (`w₀Rw₁`, `w₁Rw₂`, `A` true only at `w₂`) — consistent with Simpson's own usage, where `V` is
  always nonempty at every call site (`y_j` always present). New combinators: `dia_mono1`
  (kDia-direct, no necessitation) and generic `hAndI`/`hAndE1`/`hAndE2`/`hDiaK` hypothesis
  parameters. Sorry-free; footprint `[propext, Classical.choice, Quot.sound]` verified via
  `#print axioms` on `formula_6_7`/`formula_6_7_base`/`dia_mono1` — matches Phase 7 exactly.
- **Risk:** LOW-MED
- **Completed:** 2026-07-15T13:48:57-07:00 (commit `60517582`)

### Phase 9: Track C3 — Simpson formula (6.8) [COMPLETED]
- **Goal:** Prove (6.8): `(◇Conj(W) ⊃ □Tele(W,B)) ⊃ □Tele(W,B)` by induction on W, using axiom 5
  (requires Phase 1).
- **Tasks:**
  - [x] Countermodel-check the `W = []` base case BEFORE writing Lean
  - [x] Prove (6.8) by induction on W
  - [x] Verify sorry-free; `#print axioms`
- **Timing:** one dispatch
- **Depends on:** 1, 7
- **Outcome:** appended to `probes/track-c-c1-tele-conj.lean` (`derivable_imp_trans`,
  `formula_6_8`). **Base-case check result differs from Phase 8's**: the `W = []` instance
  (`(◇⊤⊃□B)⊃□B`) IS a genuine IK theorem (semantic argument: at any world, either no `R`-successor
  exists so `◇⊤` is vacuously false, or one exists so `◇⊤` is true and forces `□B` directly by MP) —
  **no restatement needed**; `formula_6_8` holds for *all* `W` including `[]`. Proof structure: the
  naive single `hFS`-instantiation at `φ:=Conj(W), ψ:=Tele(W,B)` does NOT close the goal (consequent
  mismatch `□(Conj(W)⊃Tele(W,B))` vs target `□Tele(W,B)`, and the bridging fact
  `(Conj(W)⊃Tele(W,B))⊃Tele(W,B)` is not a bare IPL tautology once `Conj(W)` has a `◇`-guarded tail —
  checked by hand for `W=[p,q]`, gets stuck deriving `◇q` from `p` alone). The real proof composes
  `hFS` once per level with the IH *relativized one `Tele [p]`-layer deeper* via `Tele_imp1`, using a
  new `derivable_imp_trans` transitivity combinator (also reusable by Phase 13's (◇E) 3-step
  composition). Sorry-free; footprint `[propext, Classical.choice, Quot.sound]` verified — matches
  Phases 7/8 exactly.
- **Risk:** LOW-MED
- **Completed:** 2026-07-15T14:12:51-07:00 (commit `1dc32d7d`)

### Phase 10: Track C4 — `LTree`/`star`/`fullSubtree`/`prune` + the unfolding identity [COMPLETED]
- **Goal:** Define `LTree`, `star`, `fullSubtree`, `prune` and prove the unfolding identity (§2.3);
  DELETE the defective `pathTo`/`pathToList`/`Star_append`.
- **Tasks:**
  - [x] Fix `star`; add `prune`/`fullSubtree`
  - [x] Prove the unfolding identity
  - [x] Delete `pathTo`/`pathToList`/`Star_append`
  - [x] Reproduce Simpson's worked example
  - [x] Verify sorry-free; `#print axioms`; reverify untouched declarations still compile
- **Timing:** one dispatch
- **Depends on:** 1
- **Outcome:** `probes/lemma612-scaffold.lean` (extended in place). **`star` FIXED**: was a
  double-`bigAnd` (`(bigAnd labels).and(bigAnd children)`), now a single `bigAnd` over the
  CONCATENATED list (labels ++ children-diamonds) — the old version produced a spurious `⊤∧(◇(⊤∧⊤))`
  at a label-less single-childed node instead of the source's plain `◇⊤`, which would have FAILED the
  worked-example check. `prune`/`fullSubtree` added (children split as `pre ++ [c]`, continuation
  child last, matching `addChild`'s existing append convention — forward-compatible with Phase 11).
  **Unfolding identity proved as an IK-derivable two-way implication (`star_unfold_imp1`/
  `star_unfold_imp2`), NOT raw `Eq`**: `bigAnd`'s right-fold makes literal term equality fail once
  the pruned node has 2+ ordinary children (associativity mismatch, `a.and(X.and y) ≠ (a.and X).and y`
  as TERMS despite logical equivalence) — confirmed by hand before writing Lean. Built via new
  reusable `bigAnd_append_singleton_imp1`/`imp2` (induction on `xs`) plus `andI_deriv`/`andE1_deriv`/
  `andE2_deriv`/`top_deriv`/`bigAnd_cons_of_ne_nil`. **Success criterion met via a real theorem, not
  literal `#eval`/`decide`**: `Label` has no computable `DecidableEq` in this file (only the
  classically-opaque `Classical.propDecidable` instance), so `star_Star_worked_example` proves the
  verbatim match (`((◇A⊃□□B)∧◇A) ⊃ □(◇⊤⊃◇B)`, tree `x→y,x→z→w`, target `z`) via `simp`-driven filter
  unfolding rather than `rfl`/`decide`. `Star`/`Star_imp1`/`Star_imp2`/`box_mono1`/`box_mono2`/
  `IK.impIntro`/`NIKAx`/`TClosure.hilbertTransport` UNCHANGED and reverified compiling (they only
  reference `star Γ t` opaquely, never unfold its equation). Sorry-free; footprint
  `[propext, Classical.choice, Quot.sound]` verified. Phase 7/8/9's file untouched and reverified.
- **Risk:** MED
- **Completed:** 2026-07-15T14:46:33-07:00 (commit `88d02e04`)

### Phase 11: Track C5 — `pathSpine` + the `addChild`/`pathSpine` commutation lemma [NOT STARTED]
- **Goal:** Define `pathSpine` with pruning built into the recursion, and prove the
  `addChild`/`pathSpine` commutation lemma.
- **Tasks:**
  - [ ] Define `pathSpine` (pruning in the recursion)
  - [ ] Prove the `addChild`/`pathSpine` commutation lemma, sorry-free
  - [ ] Verify `#print axioms`; no new axioms
- **Timing:** one dedicated dispatch — THE TRUE CRUX; must not share a dispatch
- **Depends on:** 10
- **Risk:** HIGH — TRUE CRUX. On failure, record the precise obstruction and invoke
  Rollback/Contingency.

### Phase 12: Track C6 — `LTree.toGraph` + τ-parameterized induction [NOT STARTED]
- **Goal:** Define `LTree.toGraph`; prove the τ-parameterized generalized induction; discharge the
  non-modal cases plus (□I)/(□E)/(◇I).
- **Tasks:**
  - [ ] Define `LTree.toGraph`
  - [ ] Set up the τ-parameterized generalized induction
  - [ ] Discharge non-modal + (□I)/(□E)/(◇I) cases, sorry-free
- **Timing:** one dispatch
- **Depends on:** 10, 11
- **Risk:** MED

### Phase 13: Track C7 — the (◇E) case [NOT STARTED]
- **Goal:** Discharge the (◇E) case via report 02 §2.5's reconstructed 3-step argument.
- **Tasks:**
  - [ ] Reconstruct the 3-step argument (reuse `derivable_imp_trans` from Phase 9)
  - [ ] Discharge (◇E), sorry-free
- **Timing:** one dispatch
- **Depends on:** 11, 12
- **Risk:** MED (given Phase 11)

### Phase 14: Track C8 — the (⊥E)/(∨E) cases [NOT STARTED]
- **Goal:** Discharge the (⊥E) and (∨E) cases (label-local in this encoding).
- **Tasks:**
  - [ ] Discharge (⊥E), sorry-free
  - [ ] Discharge (∨E), sorry-free
- **Timing:** one dispatch
- **Depends on:** 12
- **Risk:** LOW

### Phase 15: `cs5_completeness` assembly [NOT STARTED]
- **Goal:** Land `cs5_completeness` / `cs5_soundness_completeness` sorry-free and axiom-clean, via
  the adequacy bridge + labelled canonical model (Track C having completed).
- **Tasks:**
  - [ ] Assemble the adequacy bridge from Phases 11-14
  - [ ] Prove `cs5_completeness`, sorry-free, no new axioms under `Cslib/`
  - [ ] Prove `cs5_soundness_completeness`
  - [ ] Full CI gate (see Testing & Validation)
- **Timing:** one or more dispatches
- **Depends on:** 12, 13, 14
- **Risk:** HIGH — inherits Phase 11's risk.

## Testing & Validation

- [ ] Every landed probe file: `lake env lean <file>` exits 0
- [ ] Zero `sorry` under `Cslib/` at every phase boundary; `probes/` audited per phase
- [ ] `#print axioms` on each new result: footprint ⊆ `[propext, Classical.choice, Quot.sound]`; no
      NEW axioms introduced
- [ ] No regression of landed CK/CT/CS4/CS5 soundness or task-509 `cs5FC''` (reverify untouched
      declarations compile after each edit)
- [ ] Before any PR (Phase 15): `lake build`, `lake test`, `lake exe checkInitImports`,
      `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`
- [ ] Before any PR: resolve the `GeomWitnessClosure := True` + `GeomAxiom.D` debt

## Artifacts & Outputs

- plans/02_decomposed-track-a-b-c.md (this file)
- probes/lemma612-scaffold.lean (Phases 1, 10)
- probes/fischer-servi-probe.lean (Phase 2)
- probes/track-c-c1-tele-conj.lean (Phases 7, 8, 9)
- summaries/02_track-a-a1-a2-summary.md (Phases 1, 2)
- summaries/03_a3-verdict-and-c1-summary.md (Phases 3, 7)
- summaries/04_c2-formula-6-7-summary.md (Phase 8)
- summaries/05_c3-formula-6-8-summary.md (Phase 9)
- summaries/06_c4-tree-surgery-unfolding-identity-summary.md (Phase 10)
- handoffs/00_RESUME-HERE.md (single entry point after a context clear)

## Rollback/Contingency

- All Track A/C work is confined to `probes/`; zero `Cslib/` files are touched, so no rollback of
  library code is required. Reverting any phase is a `git revert` of its single scoped commit.
- If Phase 11 (the crux) does not close after its dedicated dispatch: do NOT open further
  open-ended tree-surgery dispatches. Record the precise obstruction, move Phases 11-15 to blocked
  status, and set task 517 to blocked status with the documented obstruction.
- Fallback position (already secured): the landed labelled framework (plan 01 Phases 1/2/4; ~789
  lines, CI-green, sorry-free) stands as an independent contribution decoupled from
  `cs5_completeness`. Task 512 remains blocked-on-517 in that event.
- Track B may only be re-opened by discharging Phase 3's named blocking obligation.
