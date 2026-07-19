# Implementation Plan: Direct-Route General Labelled CS5 Soundness via Derivation-Forest Invariant (nik_TS5_soundness)

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994 Thm 8.1.4's biconditional
- **Status**: IMPLEMENTING
- **Effort**: 6-10 hours remaining (Phases 1-5 landed; residual risk concentrated in Phase 7)
- **Dependencies**: 517 (delivered completeness + anti-vacuity + landed building blocks)
- **Research Inputs**: reports/03_tree-shape-invariant-audit.md (Tier 1, H4-verified; AUTHORITATIVE revised sequence), reports/02_direct-route-from-sources.md
- **Artifacts**: plans/03_direct-route-forest.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/context/formats/plan-format.md
  - .claude/context/contracts/wrap-up.md
  - .claude/context/contracts/reference-grounding.md
- **Type**: cslib
- **Plan version**: 3 (supersedes plans/02_direct-route.md; folds the tree-shape-invariant audit, report 03)

## Overview

Prove **directly** `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` in the single
file `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`, closing the soundness
direction (2⟹1) of Simpson Thm 8.1.4 for CSLib constructive CS5/IS5. **No adequacy bridge, no
`L_m` sequent system, no new file.** The completeness direction and anti-vacuity certificate are
already landed sorry-free by parent task 517.

This plan **supersedes** `plans/02_direct-route.md`. Plan v2 correctly dissolved the ex-"Wall A"
(the refuted exact-`r`-symmetry obstruction) via `box_iff_base`/`dia_iff_base` and landed Phases
1-5 (through `boxI_lift_star`) sorry-free. Its Phase 4.2 (`boxI_lift`) then hit a `[BLOCKED]`
handoff (`handoffs/04_phase4-2-boxI-lift-blocked.md`) on the belief that the recursive tree
cascade required a "tree-shape/acyclicity invariant on `Graph` that does not exist as a standalone
lemma."

The **divergence audit** (report 03, adversarially verified, Tier 1 source-grounded against
Simpson 1994 §8.1.2-8.1.3 chunks 0154-0156 and MMS 2021 §5 Def 5.1) **CONFIRMS the direct route
is completable and the `[BLOCKED]` must be LIFTED, not routed to a follow-up.** Its verdict, folded
into this plan:

- The 3-cycle counterexample in `handoffs/04` refutes only `boxI_lift` stated over an **arbitrary**
  finite `Graph`. It does **not** refute the **tree-restricted** `boxI_lift` soundness actually
  needs, because **no NIK constructor can build a cyclic raw graph**: only `boxI`
  (Deduction.lean:297) and `diaE` (Deduction.lean:309) add edges, each `addEdge x y` with `y` a
  cofinitely-fresh sink and `x` pre-existing, starting from `Graph.trivial` (Deduction.lean:316).
  The raw R-graph of every derivation is therefore a **finite rooted forest by construction**.
- This is exactly the invariant Simpson's own soundness proof relies on: Lemma 8.1.3 is stated
  *"Let G be a tree"* and its own Figure 8-1 counterexample is the published analogue of the
  3-cycle (chunk 0154); the main-induction (□I) case reads *"Let G′ = G ∪ {xRy} which is a tree as
  y is not in G"* (chunk 0156).
- **Fix**: define `IsDerivationForest` (THREE conjuncts — `X.Finite` + graded rank + unique-parent;
  the blocker's earlier 2-conjunct framing omitted finiteness) as a `def` over `Syntax.lean`'s
  `Graph`, and **thread it through the main soundness-induction motive** (discharged at
  `Graph.trivial` via `forest_trivial`, preserved at `boxI`/`diaE` via `forest_addEdge_fresh`).
  State `boxI_lift` as a **standalone lemma taking `IsDerivationForest G` as a hypothesis**, and
  complete the finite-component cascade by reusing the landed `boxI_raise_step`/`boxI_lift_star`
  per node. **Do NOT modify the `Graph` structure** (audit §2: it would perturb the completeness
  direction / `CanonicalModel.lean`, whose graph is not a finite forest).

The audit assesses the direct route **~90%** mathematically completable (the math is Simpson's, the
F1/F2 primitives are landed, the invariant is discharge-able, the consumer wall is already down).
The single residual risk is **engineering** (~60% that the finite-component recursion fits one
dispatch), concentrated **solely** in Phase 7 (`boxI_lift`).

### Definition of Done

`nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` lands sorry-free and axiom-clean
in `Soundness.lean`; full `lake build` green; `lean_verify Cslib.Logic.Modal.Labelled.nik_TS5_soundness`
reports no `sorryAx` and no new axioms; `lake lint` / `lint-style` / `shake` / `checkInitImports` /
`test` unregressed against the task-517 green baseline. Sanctioned terminal alternative if (contra
the ~90% estimate) the Phase 7 recursion's **engineering** genuinely overruns budget across
dispatches: a documented `[BLOCKED]` handoff routed to a follow-up scoped to `boxI_lift` alone,
build still green, zero debt — **never a `sorry`**, and **never** a soundness-direction `[BLOCKED]`
(Phase 10). The mathematics is settled; only an engineering overrun can trigger Phase 10.

### Research Integration

- reports/03_tree-shape-invariant-audit.md — integrated in plan_version 3 (2026-07-19). The
  AUTHORITATIVE revised sequence: finite-rooted-forest verdict, the three-conjunct
  `IsDerivationForest` invariant, the threading recommendation (motive hypothesis, not a `Graph`
  field), the lemma-by-lemma completion path reusing landed assets, the H4 adversarial table
  (both single-conjunct drops refuted; `diaE` needs no lift; the 3-cycle is unreachable), and the
  H3 source-to-implementation mapping (Simpson chunks 0154-0156, MMS chunk 0026).
- reports/02_direct-route-from-sources.md — integrated in plan_version 2; the Wall-A dissolution
  and the machine-verified crux inventory it supplied are LANDED (Phases 1-5) and carried forward.
- reports/01_general-soundness-strategies.md — superseded (its "genuinely open / Wall A" verdict
  was refuted first by report 02, then the residual Phase 4.2 blocker resolved by report 03).

### Preserved Assets

The following work is complete (landed sorry-free / axiom-clean) and MUST NOT regress. Line numbers
verified against the current tree this pass. Namespace of the landed lemmas is
`Cslib.Logic.Modal.Labelled` (note the namespace uses singular `Logic`, while the file path uses
`Logics`).

| Component | File:Line | Status | Verified |
|-----------|-----------|--------|----------|
| `cs5_completeness` | Completeness.lean:132 | [COMPLETED] | task 517 (2026-07-19) |
| `nik_TS5_consistent` (anti-vacuity) | Soundness.lean:740 | [COMPLETED] | task 517 (2026-07-19) |
| `nik_soundness_onePoint` (12-constructor skeleton) | Soundness.lean:666 | [COMPLETED] | task 517 (2026-07-19) |
| `cs5FCIncest_lift` (= confluence direction F1) | Soundness.lean:322 | [COMPLETED] | task 517 (2026-07-19) |
| `ckforces_persistence` (upward closure) | Forcing.lean:122 | [COMPLETED] | task 517 (2026-07-19) |
| `cs5_soundness_derivable_incest` (Hilbert soundness) | CS5Canonical.lean:373 | [COMPLETED] | task 517 (2026-07-19) |
| `box_iff_base` (Phase 1) | Soundness.lean:374 | [COMPLETED] | this task (2026-07-19) |
| `dia_iff_base` (Phase 1) | Soundness.lean:392 | [COMPLETED] | this task (2026-07-19) |
| `box_iff_TClosure` (Phase 2) | Soundness.lean:422 | [COMPLETED] | this task (2026-07-19) |
| `dia_iff_TClosure` (Phase 2) | Soundness.lean:437 | [COMPLETED] | this task (2026-07-19) |
| `cs5FCIncest_raise` (= confluence direction F2, Phase 3) | Soundness.lean:337 | [COMPLETED] | this task (2026-07-19) |
| `box_gives_here` (Phase 3) | Soundness.lean:349 | [COMPLETED] | this task (2026-07-19) |
| `boxI_raise_step` (Phase 4) | Soundness.lean:472 | [COMPLETED] | this task (2026-07-19) |
| `boxI_lift_star` (Phase 5) | Soundness.lean:563 | [COMPLETED] | this task (2026-07-19) |

### Source-to-Implementation Mapping (H3, Tier 1)

BibKeys VERIFIED in `references.bib`: `Simpson1994` (`@phdthesis`),
`MarinMoralesStrassburger2021` (`@article`). Sources read directly this audit pass: Simpson chunks
0154-0156; MMS chunk 0026. OCR caveat honored: every symbol-heavy claim is cross-checked against
the live Lean API. `cs5FCIncest`'s five conjuncts are `⟨hrefl, htrans, hfour, hsymbox, hincest⟩`
(CS5Canonical.lean:255-260).

| Source | Prop / Location (chunk) | Lean Identifier | Role | Status |
|--------|-------------------------|-----------------|------|--------|
| MarinMoralesStrassburger2021 | ⊠ soundness, fresh-witness (0046) | `box_iff_base` | consumer-side box equivalence across an r-edge | LANDED (Phase 1) |
| MarinMoralesStrassburger2021 | dia case (0028, 0046) | `dia_iff_base` | consumer-side dia equivalence across an r-edge | LANDED (Phase 1) |
| Simpson1994 + MMS | box-persistence over class (0028, 0046) | `box_iff_TClosure` / `dia_iff_TClosure` | transport over `TClosure {T,B,Four}` | LANDED (Phase 2) |
| MarinMoralesStrassburger2021 | refl/trans/F1/F2 (0028) | `cs5FCIncest_lift` (F1), `cs5FCIncest_raise` (F2) | Simpson Lifting-Lemma primitives | LANDED (F1 pre-existing, F2 Phase 3) |
| Simpson1994 | Lifting Lemma 8.1.3, single-node step (0154-0155) | `boxI_raise_step` | one raw-neighbour raise | LANDED (Phase 4) |
| Simpson1994 | 8.1.3 iterated, direct neighbours (0154-0155) | `boxI_lift_star` | raise over ALL direct raw-neighbours of one node | LANDED (Phase 5) |
| Simpson1994 | 8.1.3 main induction "restrict attention to trees" (0156) | `IsDerivationForest` + `forest_trivial` + `forest_addEdge_fresh` | threaded motive invariant | **Phase 6 (to land)** |
| Simpson1994 | Lifting Lemma 8.1.3, full tree cascade (0154-0155) | `boxI_lift` | full component cascade, closes `boxI` producer side | **Phase 7 (to land)** |
| Simpson1994 | §8.1.2 (□I) "G′ = G ∪ {xRy} tree as y not in G" (0156) | `boxI` case of the main induction | fresh-`y` forest preservation + lift + persistence | **Phase 8 (to land)** |
| Simpson1994 | Thm 8.1.1 / 8.1.4, tree case (0151) | `nik_TS5_soundness` (goal) | `NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` | **Phase 8 (to land)** |
| MarinMoralesStrassburger2021 | Def 5.1 G-interpretation, raw atoms (0026) | raw edge-cond `∀ a b, G.R a b → r (ρ a) (ρ b)` | threaded through Phase 8 induction | **Phase 8 (to land)** |

## Goals & Non-Goals

- **Goals**:
  - Deliver `nik_TS5_soundness` sorry-free / axiom-clean in `Soundness.lean` via the direct route.
  - Land `IsDerivationForest` + its two preservation lemmas, and the tree-restricted `boxI_lift`,
    as named, independently build-checkable lemmas.
  - Thread `IsDerivationForest` through the main NIK-induction motive; close the `boxI` producer
    case; remove the stale `INTRACTABLE`/`GATE-C`/"What remains" docstring notes.
  - Keep every intermediate state green and committed (H9 wrap-up discipline).
- **Non-Goals**:
  - Any adequacy bridge (`Adequacy.lean`, Simpson Ch.6) or `L_m` modified sequent system.
  - Any change to the completeness direction, the anti-vacuity certificate, or `cs5FCIncest`.
  - Any modification to the `Graph` structure (`Syntax.lean:110`) — the invariant is threaded, not
    a new field (audit §2).
  - Reviving the refuted "exact `r`-symmetry" / clique edge-cond invariant from plan 01.
  - Re-planning the landed Phases 1-5.

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from the four prior blocked dispatches,
the Phase 4.2 `[BLOCKED]` handoff, report 03's audit, and the zero-debt task constraints.

**Do NOT**:
- Do NOT re-attempt the refuted lemma `TClosure TS5 R a b → r (ρa)(ρb)` (validate each closed edge
  as an **exact** `r`-edge). Its `.symm` case demands exact symmetry, which `cs5FCIncest` does not
  supply and constructively should not. It is **false-in-general and unnecessary** — four dispatches
  died on it. The correct object is box/diamond forcing-**equivalence** across the `TClosure` class,
  landed in Phases 1-2.
- Do NOT maintain a **clique** edge-cond invariant (`∀ a b, TClosure TS5 G.R a b → r (ρa)(ρb)`).
  Maintain the **raw** edge-cond invariant (`∀ a b, G.R a b → r (ρa)(ρb)`, MMS Def 5.1, chunk 0026)
  and discharge the `TClosure`-closed `boxE`/`diaI` premises via the Phase 2 persistence lemmas —
  never by re-validating the closed edge.
- Do NOT state `boxI_lift` over an **arbitrary** `Graph`. That statement is genuinely FALSE (the
  3-cycle `x→a→b→x` in `handoffs/04` refutes it; node `b` receives two independent raise
  constraints). `boxI_lift` MUST take `IsDerivationForest G` as an explicit hypothesis (audit §3).
- Do NOT drop any of `IsDerivationForest`'s THREE conjuncts. `X.Finite` is required for the finite
  recursion to terminate; graded-rank alone fails on the diamond DAG `x→a→b`, `x→c→b`; unique-parent
  alone fails on the 3-cycle. All three are needed and all three hold by construction (audit H4
  table). Do NOT revert to the blocker's insufficient 2-conjunct framing.
- Do NOT modify the `Graph` structure (`Syntax.lean:110`) to add finiteness/acyclicity fields — it
  perturbs the completeness direction and `CanonicalModel.lean`, whose canonical graph is not a
  finite forest (audit §2). Thread the invariant through the induction motive instead.
- Do NOT introduce `sorry` anywhere under `Cslib/` — not even "temporary" or "strategic". This task
  forbids it. This plan is NOT a skeleton (`plan_metadata.skeleton: false`) and has NO planned
  strategic sorries. A genuinely blocked sub-goal routes to a `[BLOCKED]` handoff (Phase 10), never
  a placeholder.
- Do NOT add any new `axiom` under `Cslib/`.
- Do NOT weaken `cs5FCIncest` (do not drop or relax any of its five conjuncts `hrefl`/`htrans`/
  `hfour`/`hsymbox`/`hincest`).
- Do NOT edit or re-derive the fourteen Preserved Assets; their proofs must not regress.
- Do NOT expand file scope beyond `Soundness.lean`. No new file is introduced on this route.
- Do NOT hand-analyze a "wall" and escalate without first machine-checking the blocking sub-goal
  with `lean_run_code` / `lean_multi_attempt` — the specific failure mode of the four prior
  dispatches, and the discipline that the Phase 4.2 blocker itself honored.
- Do NOT route Phase 7 to `[BLOCKED]` for a **mathematical** reason. The mathematics is settled
  (Simpson 8.1.3, adversarially re-verified in report 03 §4). Phase 10 fires ONLY on a genuine
  **engineering** budget overrun of the finite-component recursion, and even then routes a scoped
  follow-up for `boxI_lift` alone — never a soundness-direction `[BLOCKED]`, never a `sorry`.

**MUST preserve**:
- All fourteen Preserved Assets above (sorry-free, axiom-clean, unregressed).
- Existing full-project green state: `lake build`, `lake lint`, `lint-style`, `shake`,
  `checkInitImports`, `lake test`. Pre-existing unrelated sorries in Propositional Tableau files
  are the known baseline — do not "fix" or count them.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- The raw R-graph of every NIK derivation is a **finite rooted forest by construction** (only
  `boxI`/`diaE` add edges, always `existing→fresh-sink`, from `Graph.trivial`). Adversarially
  re-verified against all 13 `NIK` constructors (report 03 §1, H4 table).
- `IsDerivationForest` lives as a `def` + threaded motive hypothesis, NOT a `Graph` field
  (audit §2). Its minimal shape is exactly three conjuncts (`X.Finite`, graded rank
  `∃ ht, ∀ a b, G.R a b → ht b = ht a + 1`, unique-parent `∀ a₁ a₂ b, G.R a₁ b → G.R a₂ b → a₁=a₂`).
- The `boxI` case raises `ρ x` to the adversarial `w'` via `boxI_lift`, then maps the fresh
  eigenvariable exactly (`σ := Function.update ρ' y u`); forest preserved by `forest_addEdge_fresh`;
  Γ-cond by `ckforces_persistence` (audit §3 step 4, Simpson chunk 0156).
- `diaE` needs **NO** lift: the dia clause at `w' = ρ x` (via `le_refl`) yields the witness
  directly; map fresh `y ↦ u` (audit §3 step 5, confirmed against Soundness.lean:335).
- A fresh `y ∉ L ∪ G.X` always exists (`Label Atom` infinite via `var : ℕ ↪ Label`; `L` finite by
  the rule field, `G.X` finite by the invariant). Reuse `exists_fresh_notMem_of_coinfinite`
  (Syntax.lean:90) / `addFreshVar` (CanonicalModel.lean:116) supply infra.
- Wall A dissolves via `box_iff_base`/`dia_iff_base` (both machine-verified axiom-free); the
  ex-"symm" direction is discharged from `hincest`/`hfour`/`hsymbox`/`htrans`, no exact symmetry.
- Confluence has BOTH directions from `cs5FCIncest`: F1 = `cs5FCIncest_lift`, F2 = `cs5FCIncest_raise`
  (both landed). Lifting is needed for `boxI` ONLY.
- `NIK` and `cs5FCIncest` stay exactly as landed (no regression, no rule change).

## Risks & Mitigations

- **Risk**: The Phase 7 `boxI_lift` finite-component recursion is the sole concentrated risk (audit:
  ~90% mathematically completable, but ~60% it fits a single dispatch — the component cascade,
  well-founded on `ht`-distance over a finite `Finset`, is fiddly Lean engineering beyond what
  `boxI_lift_star` (direct neighbours only) does).
  **Mitigation**: Phase 7 carries a hard budget cap and an explicit recommended internal
  decomposition (land the helper `raise_component_by_distance` as its own green sub-step before
  `boxI_lift` — commit-per-green-substep mandate). If the **engineering** overruns budget across
  dispatches, route to Phase 10 (`[BLOCKED]` handoff scoped to `boxI_lift` alone), never a `sorry`,
  never an undirected retry. This is an engineering-budget gate, not a mathematical wall.
- **Risk**: A phase silently touches a Preserved Asset and regresses it.
  **Mitigation**: every phase's Zero-Debt Contract re-verifies the assets build sorry-free before
  commit; `lean_verify` on the completing lemma.
- **Risk**: Reintroducing the refuted clique/exact-symmetry decomposition, or re-stating `boxI_lift`
  over an arbitrary `Graph`, under time pressure.
  **Mitigation**: the Postmortem Constraints forbid both explicitly; Phases 1-2 provide the correct
  persistence lemmas; Phase 6 provides the invariant the correct `boxI_lift` statement requires.
- **Risk**: File-territory contention — all phases write the single file `Soundness.lean`.
  **Mitigation**: phases execute strictly sequentially (see Dependency Analysis); no parallel
  dispatch onto `Soundness.lean`.
- **Risk**: The Phase 8 main induction is a single recursor invocation, so its cases cannot be
  landed green across separate dispatches without an intermediate `sorry` (forbidden).
  **Mitigation**: Phase 8 is deliberately ONE bounded unit (the generalized induction lemma +
  the trivial `Graph.trivial` specialization), landing all cases at once; it reuses the landed
  `nik_soundness_onePoint` skeleton for the 9 propositional constructors, so novel work is confined
  to `boxI`/`diaE`/`boxE`/`diaI`.

## Implementation Phases

**Dependency Analysis**:

All phases write the single file `Soundness.lean` (H7 territory: one owner), so they execute
**strictly sequentially** — no two phases may be dispatched in parallel. The wave table records the
logical dependency structure; Phases 1-5 are LANDED (historical). Execution order for the remaining
work is 6 → 7 → 8 → 9, with Phase 10 as the conditional contingency terminal reachable ONLY from a
Phase 7 engineering overrun.

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1-5 (landed) | 1, 2, 3, 4, 5 | -- (historical; all [COMPLETED]) |
| 6 | 6 | -- (pure graph lemmas over Syntax.lean; logically independent; sequential by file territory) |
| 7 | 7 | 4, 5, 6 |
| 8 | 8 | 2, 3, 7 |
| 9 | 9 | 8 |
| (contingency) | 10 | Phase 7 engineering overrun only |

The orchestrator heading-scan picks the first non-`[COMPLETED]` phase: **Phase 6**.

### Phase 1: Base forcing-equivalence lemmas box_iff_base, dia_iff_base [COMPLETED]

- **Landed**: `box_iff_base` (Soundness.lean:374), `dia_iff_base` (Soundness.lean:392) — the two
  machine-verified base biconditionals that dissolved the ex-"Wall A". Forward via `hfour` (box) /
  `hsymbox`+`htrans` (dia); backward (ex-"symm") via `hincest` then `hfour` (box) /
  `hincest`+`hsymbox`+`htrans` (dia). Sorry-free, axiom-clean.
- **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 2: TClosure-class extension box_iff_TClosure, dia_iff_TClosure [COMPLETED]

- **Landed**: `box_iff_TClosure` (Soundness.lean:422), `dia_iff_TClosure` (Soundness.lean:437),
  each a five-case `TClosure` induction (`base`→Phase 1, `refl`→`Iff.rfl`, `symm`→`Iff.symm`,
  `trans`→`Iff.trans`, `eucl`→`False.elim` since Five ∉ TS5). Sorry-free, axiom-clean.
- **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 3: F2 target-raise + reflexive here-extraction helpers [COMPLETED]

- **Landed**: `cs5FCIncest_raise` (F2, Soundness.lean:337) via `hsymbox` then `hincest`;
  `box_gives_here` (Soundness.lean:349) via the `hrefl` instance. Sorry-free, axiom-clean. (The
  optional dia here-helper was deferred to the consuming induction, now Phase 8, where its exact
  shape becomes knowable.)
- **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 4: Single-node interpretation-raise step boxI_raise_step [COMPLETED]

- **Landed**: `boxI_raise_step` (Soundness.lean:472) — raising the interpretation at ONE designated
  raw-neighbour `n` of `x` preserves the raw edge-cond (F1 down `R x n`, F2 up `R n x`) and Γ-cond
  (`ckforces_persistence`), agreeing with `ρ` off `{x, n}`. Sorry-free, axiom-clean.
- **Do NOT re-plan or re-derive.** Preserved Asset.

### Phase 5: Star-lifting over all direct raw-neighbours boxI_lift_star [COMPLETED]

- **Landed**: `boxI_lift_star` (Soundness.lean:563) — generalizes `boxI_raise_step` from one
  raw-neighbour to a finite `Finset` of `x`'s DIRECT raw-neighbours (either direction), chaining
  `cs5FCIncest_lift`/`cs5FCIncest_raise` via `Finset.induction`, holding `x`'s target fixed at the
  original raise fact. Needs NO acyclicity hypothesis (never looks past immediate neighbours).
  Sorry-free, axiom-clean. Does NOT by itself close the full cascade (a neighbour's own further
  neighbours are left unraised) — that residual is Phase 7.
- **Do NOT re-plan or re-derive.** Preserved Asset. This was the partial deliverable of plan v2's
  `[BLOCKED]` Phase 4.2; the audit confirms it is sound forward progress to build Phase 7 on.

### Phase 6: Derivation-forest invariant IsDerivationForest + preservation lemmas [COMPLETED]

- **Goal:** Define the threaded invariant and its two preservation lemmas — the small,
  self-contained graph scaffolding `boxI_lift` (Phase 7) and the Phase 8 motive both require.
  Grounded in Simpson chunk 0156 ("restrict attention to trees"; "G′ = G ∪ {xRy} tree as y not in
  G") and the codebase structure (`Deduction.lean` edge-adding rules, `Syntax.lean:118 edge_mem`).
- **Tasks:**
  - [x] Define `IsDerivationForest (G : Graph Atom) : Prop` with the THREE conjuncts (audit §1):
        `G.X.Finite` ∧ `(∃ ht : Label Atom → ℕ, ∀ a b, G.R a b → ht b = ht a + 1)` (graded rank ⟹
        directed-acyclic) ∧ `(∀ a₁ a₂ b, G.R a₁ b → G.R a₂ b → a₁ = a₂)` (unique parent ⟹ no
        undirected diamond). Match the exact `Graph` field names from `Syntax.lean:110`.
  - [x] Prove `forest_trivial : IsDerivationForest (Graph.trivial Atom)` — `ht := fun _ => 0`; no
        edges so graded/unique-parent vacuous; `X = {var 0}` finite (audit §3 step 1, ~5 lines).
  - [x] Prove `forest_addEdge_fresh : IsDerivationForest G → x ∈ G.X → y ∉ G.X →
        IsDerivationForest (G.addEdge x y)` — `ht' := Function.update ht y (ht x + 1)`; new edge
        `x→y` graded by construction; unique-parent preserved because `y ∉ G.X` ⟹ `y` gains exactly
        one source `x`; finiteness via `Set.Finite.union`/`Set.finite_insert` (audit §3 step 2).
        This is the exact preservation `NIK.boxI`/`NIK.diaE` (`addEdge x y`, `y` fresh) require.

**Phase 6 completion note (2026-07-19)**: All three tasks landed exactly as specified, no
deviation. `IsDerivationForest` is a `def` with the three conjuncts verbatim; `forest_trivial`
(2 lines, term-mode) and `forest_addEdge_fresh` (~30 lines, tactic-mode, `classical` + explicit
case split avoiding an `rcases … | ⟨rfl, rfl⟩` ambiguity that would substitute-away the outer
`x`/`y` binders — fixed by keeping the equalities as named hypotheses `ha`/`hb` and `rw`-ing
instead of destructive `subst`). `lake build …Labelled.Soundness` green; `lean_verify` on both
lemmas reports `{propext, Classical.choice, Quot.sound}` only (no new axiom, no `sorryAx`);
`lake exe checkInitImports` clean; no NEW tactic `sorry` (grep confirms only prose mentions).
`boxI_lift_star` spot-re-verified unregressed (same three standard axioms). Committed at
`task 537 phase 6: IsDerivationForest + preservation lemmas`.
- **Estimated output:** ~40-70 lines. **Bounded unit:** one `def` + two lemmas, each provable in
  isolation over `Syntax.lean`'s `Graph` with zero dependency on the model or forcing; concrete
  stopping condition = all three compile. Passes the bounded-unit test (fixed, finite attack
  surface; no open-ended search).
- **Timing:** one agent run.
- **Depends on:** none new (pure graph lemmas; sequential after Phase 5 by file territory).
- **Zero-debt contract:** no `sorry`, no new axiom under `Cslib/`, `cs5FCIncest` unweakened, `Graph`
  structure unmodified, no Preserved Asset touched.
- **Verification / Done when:** `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness`
  green; `lean_verify` on `forest_trivial` and `forest_addEdge_fresh` reports axiom-clean (no
  `sorryAx`); `grep -nE '\bsorry\b'` finds no NEW tactic `sorry`.

### Phase 7: Tree-cascade lifting lemma boxI_lift [COMPLETED]

This is the sole concentrated-risk phase (audit: ~90% mathematically completable; ~60% single
dispatch — the risk is **engineering**, not soundness). It carries the budget cap and the sole
route to the Phase 10 contingency.

- **Goal:** State and prove the tree-restricted Lifting Lemma (Simpson 8.1.3, chunk 0155), taking
  `IsDerivationForest G` as a hypothesis, completing the finite-component cascade `boxI_lift_star`
  left open. This closes the `boxI` **producer** side.
- **Tasks:**
  - [x] State `boxI_lift` with the audit §3 signature (schematically):
        `cs5FCIncest r → (v upward-closed) → (botForces upward-closed) → IsDerivationForest G →`
        `(∀ a b, G.R a b → r (ρ a) (ρ b)) → ρ x ≤ w' →`
        `∃ ρ', ρ' x = w' ∧ (∀ z, ρ z ≤ ρ' z) ∧ (∀ a b, G.R a b → r (ρ' a) (ρ' b)) ∧`
        `(∀ {φ z}, CKForces r v botForces (ρ z) φ → CKForces r v botForces (ρ' z) φ)`.
        Landed verbatim to this signature (`boxI_lift`, `Soundness.lean`).
  - [x] **Internal decomposition landed** (differs from the plan's original
        `raise_component_by_distance`-single-helper sketch; see the dispatch-1 partial-progress
        note below for the two-piece split actually used): `raise_subtree` (downward cascade,
        dispatch 1) + `siblings_disjoint` + `boxI_lift_ancestor` (Finset-exclusion ancestor walk,
        dispatch 2) assemble `boxI_lift`. Documented deviation: `boxI_lift_ancestor`'s edge
        conjunct checks Finset-exclusion membership via the edge's *target*, not *source* (the
        dispatch-1 handoff's transcribed schema checked the source, which is unprovable at the
        boundary edge into the excluded branch — see `boxI_lift_ancestor`'s docstring for the
        full justification). The overall two-piece downward/ancestor strategy and all key
        decisions from the dispatch-1 handoff are unchanged.
  - [x] Engineering did NOT overrun budget across the two dispatches; Phase 10 not invoked.
- **Estimated output:** ~120-220 lines. **Bounded unit:** one lemma (optionally one helper +
  the lemma) with a FIXED, finite attack surface — the finite component of `x`, recursion terminating
  by `G.X.Finite` + the `ht` rank. Concrete stopping condition = `boxI_lift` compiles with the stated
  signature, OR the documented engineering budget is hit and Phase 10 fires. Passes the bounded-unit
  test: the signature and recursion domain are fixed and finite, not open-ended research.
- **Timing:** one agent run, hard budget cap. If it wants a second dispatch, land the green helper
  first (it is an independently-committable Preserved Asset for the follow-on dispatch).
- **Depends on:** 4 (`boxI_raise_step`), 5 (`boxI_lift_star`), 6 (`IsDerivationForest`).
- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, `Graph` unmodified,
  no Preserved Asset touched.
- **Engineering-budget sub-gate:** overrun at budget → **Phase 10** (`[BLOCKED]` scoped to
  `boxI_lift`), never a `sorry`, never a soundness-direction `[BLOCKED]`. The mathematics is settled.
- **Verification / Done when:** `Soundness.lean` builds green; `lean_verify` on `boxI_lift` (and any
  helper) reports axiom-clean; no NEW tactic `sorry`.

**Phase 7 partial-progress note (2026-07-19, dispatch 1)**: Landed and committed, sorry-free,
axiom-clean:
- `ht_le_of_reflTransGen` — rank is non-decreasing along forward `G.R`-reachability (pure
  consequence of graded rank; ~10 lines).
- `raise_subtree` — the downward-cascade helper (audit's "process the finite component... in
  increasing `ht`-distance order", restricted to the DOWNWARD direction): given `p` already raised
  to a fixed `wp`, raises `p` together with the forward-reachable closure through a chosen
  `Finset` of direct raw-neighbours, via repeated `cs5FCIncest_lift` (F1). Well-founded on
  `Set.ncard {q ∈ G.X | ht q ≥ ht p}` (strictly decreasing at each child). Disjointness of
  different children's closures follows directly from the unique-parent conjunct (last-edge
  argument, no general cycle-freeness/BFS-uniqueness lemma needed) — this de-risks the audit's
  "residual uncertainty" note. ~170 lines, `lean_verify` reports `{propext, Classical.choice,
  Quot.sound}` only.

**Remaining sub-goal (precise, for continuation dispatch)**: assemble `boxI_lift` itself from
`raise_subtree` via an **ancestor walk** (raise `x` to `w'`, then walk up the unique-parent chain
toward the root via `cs5FCIncest_raise`/F2, invoking `raise_subtree` for sibling branches hanging
off each ancestor). This dispatch confirmed (via live `lean_goal` iteration) that the naive
"`ihn q hqn hqX q' hqq'`" recursive call at each ancestor `q` is UNSOUND as stated: the induction
hypothesis's own conclusion promises to cover *all* of `G`'s edges, which would let it silently
re-derive `q`'s child `z`'s value independently via its own internal `raise_subtree` call —
conflicting with `z`'s already-pinned target `wz`. **Fix (identified, not yet implemented)**:
generalize the ancestor-walk induction to carry an explicit exclusion parameter mirroring
`raise_subtree`'s own Finset-of-children mechanism (inverted: a Finset/singleton of children
whose entire downward closure is *already handled by the caller* and must be left untouched),
threaded through both the `noParent` base lemma and the `succ` inductive step:
```
∀ n, ∀ z, ht z ≤ n → z ∈ G.X → ∀ wz, ρ z ≤ wz → ∀ (excl : Finset (Label Atom)),
  (∀ e ∈ excl, G.R z e) →
  ∃ ρ', ρ' z = wz ∧ (∀ u, ρ u ≤ ρ' u) ∧
    (∀ a b, G.R a b → (∀ e ∈ excl, ¬ Relation.ReflTransGen G.R e a) → r (ρ' a) (ρ' b)) ∧
    (∀ u, (∀ e ∈ excl, ¬ Relation.ReflTransGen G.R e u) →
      ∀ {φ}, CKForces r v botForces (ρ u) φ → CKForces r v botForces (ρ' u) φ) ∧
    (∀ u, (∃ e ∈ excl, Relation.ReflTransGen G.R e u) → ρ' u = ρ u)
```
Top-level call (from `boxI_lift`) uses `excl := ∅` (vacuous, full coverage). The `succ`-with-parent
case calls `raise_subtree` with `C := {cc | G.R z cc ∧ cc ∉ excl}` (z's closure minus what the
caller already owns) to get `ρz`, F2-raises `q` to get `q'`, then recurses via `ihn q hqn hqX q'
hqq' {z} (proof G.R q z)` (excluding `z`'s branch, now safely — `ihn`'s conclusion no longer
promises to touch `z`'s closure) to get `ρq`, then **combines** `ρz`/`ρq` via the same
if-then-else-on-`ReflTransGen`-membership pattern `raise_subtree`'s own `insert` case uses. The
`noParent`/zero case is the same lemma specialized (a root reached via the walk, generally with
a nonempty `excl` from the level below). Estimated remaining size: ~120-180 lines, same proof
style/tactics already exercised in `raise_subtree` (no new mathematical content, pure engineering
completion of an already-identified fix). No mathematical wall was hit at any point.
### Phase 8: Main NIK induction (motive amended), close boxI case, assemble nik_TS5_soundness [BLOCKED]

**Phase 8 blocked note (2026-07-19)**: Attempted the generalized induction exactly as specified
(motive `∀ ρ, IsDerivationForest G → raw-edge-cond → Γ-cond → CKForces r v botForces (ρ φ.lbl)
φ.prop`, reusing `nik_soundness_onePoint`'s skeleton). `boxI`/`diaE`/`boxE`/`diaI` are NOT the
obstruction (their fix is exactly as this plan anticipated, using `boxI_lift`/`box_iff_TClosure`/
`dia_iff_TClosure`/`box_gives_here`). The obstruction is in TWO of the "9 straightforward
propositional constructors": `NIK.efq` and `NIK.orE` (Deduction.lean:252,277), which are
**cross-label** with NO constraint relating the premise's label to the conclusion's independent
label (unlike `boxE`/`diaI`, which always carry a `TClosure` edge). A two-point countermodel was
built and machine-verified this dispatch (`lean_run_code`: `World := Pt (one|two)`, `≤:=Eq`,
`r:=Eq`; `cs5FCIncest r` holds; all `CKValidFC` explosion/upward-closure axioms hold; `botForces :=
(·=one)`; `CKForces bot` holds at `one` while `CKForces (atom ()) ` is FALSE at `two`) showing the
naive "∀ ρ" motive is **false** whenever `efq`'s conclusion label is not already constrained by
`G.X ∪ ctxLabels Γ` — this is a **mathematical**, not engineering, gap, discovered only by directly
attempting the case (per the anti-churn discipline), and is NOT covered by Phase 10 (scoped solely
to a Phase 7 `boxI_lift` engineering overrun). Full details, the exact countermodel, and the two
candidate fixes assessed as out-of-phase-8-scope (a not-yet-landed "G.X is TClosure TS5-total on a
connected component" lemma; an existential-motive reformulation) are recorded in
`Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`'s module docstring, "Fifth
dispatch" section. Zero debt preserved: no `.lean` proof code was touched (only the module
docstring was updated); no `sorry`; no new axiom; Phases 1-7 unregressed. See
`specs/537_labelled_cs5_general_soundness_biconditional/handoffs/08_phase8-blocked-crosslabel-efq.md`
for the full handoff and recommended follow-up scope.

- **Goal:** Complete the 12-constructor `NIK` induction generalized over an arbitrary interpretation
  `ρ` and model (reusing the `nik_soundness_onePoint` skeleton, Soundness.lean:666), with the motive
  amended to carry `IsDerivationForest G` alongside the **raw** edge-cond + Γ-cond, and land
  `nik_TS5_soundness` (audit §3 steps 4-8, Simpson chunk 0156). This is ONE bounded unit: a single
  recursor invocation cannot have its cases split across green dispatches without a `sorry`.
- **Tasks:**
  - [ ] Generalize the `nik_soundness_onePoint` induction over `ρ` and model, adding
        `IsDerivationForest G` to the motive alongside the raw edge-cond `∀ a b, G.R a b → r (ρa)(ρb)`
        (MMS Def 5.1, chunk 0026) and Γ-cond.
  - [ ] Discharge `boxI` (Deduction.lean:297): take adversarial `w' ≥ ρ x`, `u` with `r w' u`; pick
        fresh `y ∉ L ∪ G.X` (exists — `Label` infinite, `L`/`G.X` finite; reuse
        `exists_fresh_notMem_of_coinfinite`/`addFreshVar`); apply `boxI_lift` to raise `x` to `w'`;
        set `σ := Function.update ρ' y u`; new edge `r (σ x)(σ y) = r w' u` holds; raw edge-cond for
        `G.addEdge x y` from `boxI_lift` + the new edge; `IsDerivationForest (G.addEdge x y)` via
        `forest_addEdge_fresh`; Γ-cond via persistence; feed the IH at `y ∉ L`.
  - [ ] Discharge `diaE` (Deduction.lean:309) via `le_refl` (NO lift): dia clause at `w' = ρ x`
        gives `∃ u, r (ρ x) u ∧ CKForces u A`; `σ := Function.update ρ y u`; new edge `r (ρ x) u`
        direct; forest preserved by fresh `y`.
  - [ ] Discharge `boxE`/`diaI` (Deduction.lean) via `box_iff_TClosure`/`dia_iff_TClosure` (Phase 2)
        + `box_gives_here` (Phase 3) — never by validating the closed edge. Land the dia here-helper
        if the `diaI` case needs it (dia-iff + `hrefl` + `ckforces_persistence`).
  - [ ] Discharge the remaining 9 constructors from the generalized `nik_soundness_onePoint`
        skeleton, carrying raw edge-cond + Γ-cond + `IsDerivationForest`.
  - [ ] Land `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` by specializing to
        `Graph.trivial` / `[]` (Deduction.lean:316): discharge `IsDerivationForest` via
        `forest_trivial`, raw edge-cond vacuously (no edges), Γ-cond vacuously (empty Γ).
  - [ ] Update the `Soundness.lean` module docstring: mark the general theorem LANDED; **remove the
        stale INTRACTABLE / GATE-C / "What remains" notes** (superseded per report 03 §4/§"H4 table").
- **Estimated output:** ~150-300 lines. **Bounded unit:** the generalized induction lemma + the
  trivial `Graph.trivial` corollary; stopping condition = `nik_TS5_soundness` compiles sorry-free.
  At the H8 line ceiling but irreducible (single recursor invocation, zero-debt forbids a
  split-with-`sorry`); novel work is confined to `boxI`/`diaE`/`boxE`/`diaI` since the 9
  propositional cases transcribe the landed skeleton.
- **Timing:** one agent run.
- **Depends on:** 2 (TClosure lemmas), 3 (here-helpers), 7 (`boxI_lift`).
- **Zero-debt contract:** no `sorry`, no new axiom, `cs5FCIncest` unweakened, `Graph` unmodified,
  no Preserved Asset touched.
- **Verification / Done when:** `nik_TS5_soundness` sorry-free; `Soundness.lean` builds green;
  `lean_verify Cslib.Logic.Modal.Labelled.nik_TS5_soundness` axiom-clean (no `sorryAx`, no new
  axiom); no NEW tactic `sorry`.

### Phase 9: Regression gate + full-project verification [NOT STARTED]

- **Goal:** Confirm the full project is green and unregressed, the Simpson 8.1.4 biconditional is
  complete, and no debt was added anywhere.
- **Tasks:**
  - [ ] Full `lake build` green.
  - [ ] `lean_verify Cslib.Logic.Modal.Labelled.nik_TS5_soundness` reports no `sorryAx` and no new
        axioms.
  - [ ] `grep -nE '\bsorry\b'` on `Soundness.lean`: no NEW *tactic* `sorry` (docstring prose
        excepted); `grep -nE '^axiom '`: zero new axioms.
  - [ ] Spot-verify the fourteen Preserved Assets still build sorry-free (esp. the six task-517
        assets and the eight this-task lemmas Phases 1-5 landed).
  - [ ] `lake lint`, `lake exe lint-style <file>`, `lake shake`, `lake exe checkInitImports`,
        `lake test` all unregressed against the task-517 baseline.
- **Estimated output:** verification only; docstring touch-ups if any (~0-30 lines).
- **Timing:** one agent run.
- **Depends on:** 8.
- **Zero-debt contract:** no `sorry`, no new axiom, no weakening, no regression.
- **Verification / Done when:** all checks above pass; the Simpson 8.1.4 biconditional is complete.

### Phase 10: BLOCKED handoff to follow-up (contingency only — engineering overrun of Phase 7) [NOT STARTED]

- **Goal:** If — contra the ~90% estimate — the Phase 7 `boxI_lift` finite-component recursion's
  **engineering** genuinely overruns budget across dispatches (NOT a mathematical wall; the math is
  settled per report 03), record an honest `[BLOCKED]` terminal state WITHOUT adding any debt, and
  write a handoff routing to a follow-up scoped to `boxI_lift` alone. This is the sanctioned no-loop,
  no-sorry response; the MAIN LINE is the direct proof (Phases 6-9), which this phase does not
  pre-empt. It does NOT fire for `boxE`/`diaI`/`diaE` or the assembly — those are settled.
- **Tasks:**
  - [ ] Write a `[BLOCKED]` handoff under `specs/537.../handoffs/` naming the exact **engineering**
        blocker (the specific step of the component cascade that did not close), the machine-checked
        stuck sub-goal, the green state of Phases 1-6 (and any landed Phase 7 helper), and the build
        status.
  - [ ] Recommend a follow-up task scoped narrowly to the `boxI_lift` component cascade, carrying
        forward the landed Phases 1-6 lemmas (and `raise_component_by_distance` helper if landed) as
        its foundation. Reference the audit report 03 §3 completion path.
  - [ ] Confirm zero debt: `grep` finds no NEW tactic `sorry` in `Soundness.lean`; `lake build`
        green; `cs5FCIncest` unweakened; `Graph` unmodified; all Preserved Assets unregressed.
- **Estimated output:** documentation only; no `.lean` proof edits.
- **Timing:** short; one agent run.
- **Depends on:** Phase 7 engineering overrun only.
- **Zero-debt contract:** no `sorry`, no new axiom, no weakening, no regression — verified before
  writing the handoff.
- **Verification / Done when:** `[BLOCKED]` recorded with a durable handoff naming a concrete
  engineering blocker and a follow-up route; build green; zero debt.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green after every
      phase that touches `.lean` (H9 green-milestone commit).
- [ ] Full `lake build` green at each phase completion.
- [ ] `lean_verify` axiom-clean on each new lemma as it lands (`forest_trivial`,
      `forest_addEdge_fresh`, `boxI_lift`), and on `nik_TS5_soundness` at Phase 8/9.
- [ ] `grep -nE '\bsorry\b'` on `Soundness.lean`: no NEW *tactic* `sorry` (docstring prose excepted).
- [ ] `grep -nE '^axiom '` on modified files: zero new axioms.
- [ ] `Graph` structure (`Syntax.lean:110`) unmodified; `cs5FCIncest` (`CS5Canonical.lean:255`)
      unweakened.
- [ ] `lake lint`, `lake exe lint-style <file>`, `lake shake`, `lake exe checkInitImports`,
      `lake test`: all unregressed against the task-517 green baseline.
- [ ] Preserved Assets unregressed (spot-verify the fourteen listed theorems build sorry-free).

## Artifacts & Outputs

- plans/03_direct-route-forest.md (this file)
- Modified: Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean (Phases 6-9)
- handoffs/ blocked handoff (contingency, Phase 10 only)
- summaries/03_direct-route-forest-summary.md (on completion)

## Rollback/Contingency

- Each phase commits only its own green result (H9 incremental commit; commit-per-green-substep
  mandate applies to the Phase 7 helper). If a phase fails to reach green, leave the prior committed
  state intact; fix forward — never destructive git on a dirty tree (see
  `.claude/rules/git-workflow.md`, "No Destructive Git on Uncommitted Work").
- The blocked-honesty path (Phase 10) IS the sanctioned contingency for a genuine Phase 7
  **engineering** overrun: a `[BLOCKED]` handoff scoped to `boxI_lift` alone, with a concrete
  engineering blocker and a follow-up route, zero debt, build green — never a `sorry` skeleton, never
  a soundness-direction `[BLOCKED]`, and never a return to the refuted clique/exact-symmetry
  decomposition or the `boxI_lift`-over-arbitrary-`Graph` statement.
