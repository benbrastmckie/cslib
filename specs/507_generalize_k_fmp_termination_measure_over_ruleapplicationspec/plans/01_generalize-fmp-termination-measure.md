# Implementation Plan: Task #507 — Generalize K FMP Termination Measure over RuleApplicationSpec

- **Task**: 507 - Generalize the K FMP termination measure over `RuleApplicationSpec`
- **Status**: [NOT STARTED]
- **Effort**: 14 hours
- **Dependencies**: None (builds entirely on task 503's committed, green Phase 1 `Saturation.lean`
  commit `e9f350c7` and Phase 2 `GenericDriver.lean` commit `d5b24e67`; parent task 503 [BLOCKED])
- **Research Inputs**: specs/503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/reports/02_spawn-analysis.md
- **Artifacts**: plans/01_generalize-fmp-termination-measure.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md;
  cslib.md; CONTRIBUTING.md; NOTATION.md; ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Complete task 503's blocked Phase 3: generalize `FmpMeasure.lean`'s rule-dependent
termination/FMP step lemmas — `modalStepBranch_potential_step` (line 2148),
`modalStepBranch_worldBound` (line 2378), and `modalExpMeasure_step_lt` (line 2875) — plus their
~900-line private dependency chain (lines ~1019–2117) to take an abstract
`(apply : RuleApply Atom) (spec : RuleApplicationSpec apply)` in place of the concrete
`modalApplyOne`. Today every one of ~15 helper lemmas independently `rcases`es on `modalApplyOne`'s
four concrete `RuleResult` shapes (propositional/boxPos/diamondNeg/diamondPos/boxNeg) rather than
going through `RuleApplicationSpec`; the three current spec fields
(`freshLocal`/`outputsSubsetUniverse`/`persistentFresh`) are sufficient to restate each lemma's
*type* generically but not to replay its *proof*. The plan therefore (a) first extends
`RuleApplicationSpec` (`GenericDriver.lean`) with the additional outDeg/rank-map mint-point fields
the exact `geomCap`-based potential-drop identity (lines ~2251–2270) consumes, discharging each new
field for `modalApplyOne`; then (b) re-derives the dependency chain generically in cohesive
phase-sized clusters, each ending at a green `lake build`; then (c) generalizes the three top-level
step lemmas; and (d) re-instantiates K's termination lemmas as
`<generic> modalApplyOne modalApplyOne_spec` and confirms `FmpMeasure.lean`'s K corollaries and
`CompletenessLoop.lean`'s uses still typecheck via the Phase-1 `_eq` bridge lemmas. The
world-agnostic size bounds (`modalUniverse`/`modalWork`/`modalExpMeasure`/`modalFuel`/
`modalWorldBound`) are left unchanged — only the rule-dependent step lemmas move behind the
interface. Definition of done: every delivered result is genuinely sorry-free / axiom-free, K's
public theorem statements are byte-unchanged, and the full CSLib CI is clean at every milestone. If
any sub-piece cannot close sorry-free, the affected sub-goal is marked **[BLOCKED]** with the exact
open lemma name and goal state, and the remainder is sequenced into further phases of this plan
rather than deferred silently or closed with debt.

### Research Integration

Adopted directly from `reports/02_spawn-analysis.md` and task 503's Phase-3 `[BLOCKED]` handoff:

- **Root cause**: `modalStepBranch_potential_step` and its whole dependency chain
  (`modalStepBranch_exists_rank'` line 1060, `modalStepBranch_preserves_outDegEq` line 1367,
  `outDeg_le_of_expandedNodup` line 1511, `modalStepBranch_knownWorlds` line 1903, and ~10 further
  private helpers) `rcases` directly on `(modalApplyOne sf b acc).fst`/`.snd`'s concrete shapes and
  exploit fine-grained `outDeg`/`modalKnownWorlds`/rank-map bookkeeping specific to K's own
  `diamondPos`/`boxNeg` mint arms — including the `geomCap`-based potential-drop identity (lines
  ~2251–2270) that computes an EXACT numeric decrease, not just a bound.
- **What is needed** (per the implementer's documented recommendation, mirrored in
  `GenericDriver.lean`'s "Known Limitation" docstring): (a) extend `RuleApplicationSpec` with
  additional fields capturing the exact outDeg/rank-map interaction at the fresh-world mint point
  ("not just 'a fresh edge is added', but 'the fresh edge's source `outDeg` was `< Sf` beforehand,
  by exactly the amount the catalog bounds'") so the EXACT potential-drop identity can be *replayed*
  generically, not merely bounded; and (b) re-derive
  `modalStepBranch_exists_rank'`/`modalStepBranch_knownWorlds`/`modalStepBranch_preserves_outDegEq`
  generically BEFORE the top-level potential-step lemma can be attempted.
- **Interface designed against a real client**: the current three-field bundle was derived against
  `modalApplyOne`; the additional fields must likewise be validated against the actual proof
  obligations, so field refinement is expected to be discovered incrementally while re-deriving the
  helpers (Phases 2–5), with re-discharge for `modalApplyOne` kept green at each step.
- **Scope confinement**: only `FmpMeasure.lean` (the measure lemmas) and `GenericDriver.lean` (the
  spec bundle) are edited. `Saturation.lean` (generic driver defs + `_eq` bridges) is reused,
  not modified. `CompletenessLoop.lean` is read-only here (typecheck confirmation only) — its own
  generalization is task 503's deferred Phase 4.
- **Downstream**: completing this unblocks task 503's Phases 4–7 (T driver instantiation, T truth
  lemma, `Decidable (tValid φ)`) and is a prerequisite for tasks 504 (S5/KB5) and 505 (B). Task 506
  (S4) is explicitly NOT an instance of this interface and is out of scope.

### Prior Plan Reference

Prior plan `specs/503_.../plans/01_generalize-tableau-driver-tsystem.md` (task 503, Phase 3
[BLOCKED]) is reference-only. Learned from it: (1) Phases 1–2 delivered the generic driver
(`modalStepBranchGen`/`modalExpandBranchesGen`/`modalTableauGen` + `_eq` bridges in
`Saturation.lean`, commit `e9f350c7`) and the `RuleApplicationSpec` bundle + `modalApplyOne_spec`
witness (`GenericDriver.lean`, commit `d5b24e67`) CI-green with zero debt — **do not re-derive
them**. (2) Its single "3 hour" Phase-3 estimate was an order of magnitude too small because it
treated the ~900-line re-derivation as one unit; this plan budgets it as seven phase-sized clusters
plus a verification phase. (3) Its `never sorry; mark [BLOCKED] with documented goal state`
discipline is preserved verbatim. No phases are copied.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; no ROADMAP.md was consulted or modified.
Task 507 is the sole unblock for task 503's Phase 3 (and thus 503's Phases 4–7), and delivers the
shared `RuleApplicationSpec`-generic termination measure that tasks 504/505 instantiate.

## Goals & Non-Goals

**Goals**:
- Extend `RuleApplicationSpec` (`GenericDriver.lean`) with the additional mint-point outDeg/rank-map
  field(s) required to replay the EXACT `geomCap` potential-drop identity generically, each
  discharged for `modalApplyOne` (keeping `modalApplyOne_spec` sorry-free).
- Generic re-derivations of the full rule-dependent dependency chain over `(apply, spec)`:
  `modalStepBranch_exists_rank'`, `modalStepBranch_preserves_outDegEq`, `outDeg_le_of_expandedNodup`,
  `modalStepBranch_preserves_accTargetsKnown`, `modalStepBranch_knownWorlds`,
  `modalStepBranch_eClosure`, and their ~10 private supporting helpers.
- Generic `modalStepBranch_potential_step`, `modalStepBranch_worldBound`, and
  `modalExpMeasure_step_lt` over `(apply, spec)`, discharging each former `modalApplyOne`-specific
  step from a `spec` field.
- K's termination lemmas re-instantiated as `<generic> modalApplyOne modalApplyOne_spec`, with
  `FmpMeasure.lean`'s existing K corollaries and `CompletenessLoop.lean`'s uses still typechecking
  via the Phase-1 `modalStepBranch_eq`/`modalExpandBranches_eq`/`modalTableau_eq` bridges — **zero
  regression, zero sorry, zero axiom**.
- The world-agnostic size bounds (`modalUniverse`/`modalWork`/`modalExpMeasure`/`modalFuel`/
  `modalWorldBound`) left byte-unchanged.
- Full CSLib CI clean at every phase end.

**Non-Goals**:
- Any change to `Saturation.lean` (generic driver defs + `_eq` bridges are reused, not touched).
- Any generalization of `CompletenessLoop.lean` (task 503 Phase 4; here it is read-only typecheck
  confirmation only).
- T / S5 / B / S4 instantiation (tasks 503-Phase-4+, 504, 505, 506).
- Any change to K's observable behavior or public theorem statements
  (`modalStepBranch_potential_step`/`_worldBound`/`modalExpMeasure_step_lt` keep their exact K types
  as re-instantiated corollaries).
- Any `sorry`, `axiom`, or vacuous `def X := True`/`trivial` placeholder to "close" a phase.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The additional `RuleApplicationSpec` fields designed in Phase 1 prove insufficient once the crux `modalStepBranch_potential_step` is attempted (Phase 5) | H | H | Field-set refinement is expected: Phases 2–5 may add fields to `RuleApplicationSpec` as the real obligations surface, each re-discharged for `modalApplyOne` and kept green. Phase 5 has an explicit **[BLOCKED]** fallback documenting the exact insufficient field and open goal. Never weaken `modalApplyOne_spec` with `sorry`. |
| The EXACT `geomCap` potential-drop identity (lines ~2251–2270) cannot be replayed generically (only bounded) | H | M | Extend the spec with the exact `outDeg`-at-mint equality (not an inequality) so the numeric identity is reproduced, not weakened; if only a bound is provable, mark Phase 5 **[BLOCKED]** with the identity-vs-bound gap and preserve Phases 1–4 green. |
| A generic helper phase exceeds one agent run (~500 lines Lean output) | M | M | Phases are pre-partitioned into cohesive ≤~500-line clusters (see phase notes); if a phase still overruns, write an 80%-context handoff at a green intermediate lemma and split the residue into a new phase appended to this plan. |
| Generalizing a private helper in place breaks an internal caller, losing the green build mid-phase | M | M | Per lemma, add the generic `_gen` sibling and immediately re-derive the concrete `modalApplyOne` version (or rewire the internal caller to `_gen … modalApplyOne modalApplyOne_spec`) so the file stays green before the phase ends. Keep original concrete lemma statements intact. |
| Zero-regression break: a downstream `CompletenessLoop.lean` use of a K corollary stops typechecking | H | L | The three public top lemmas are re-instantiated with byte-identical K statements; Phase 8 explicitly builds `CompletenessLoop.lean` (and the whole Tableau tree) to confirm. Revert-per-phase commits bound the blast radius. |
| Lint (docBlame/defLemma/simpNF/unusedSectionVars) on new generic decls | L | M | Docstring every new decl; Prop-valued results as `lemma`/`theorem`; run full CI (`lake lint`, `lake exe lint-style`, `lake shake`) at each phase end. |
| Context exhaustion mid-phase on the large knownWorlds/potential clusters | M | M | Each phase ends at a green, committed milestone; write a handoff at 80% context per the metadata schema so resume is clean. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |
| 8 | 8 | 7 |

The chain is intrinsically sequential: the extended spec fields (Phase 1) must exist before any
generic helper can consume them; the outDeg and rank/knownWorlds helper clusters (Phases 2–4) are
the direct dependencies of the potential-step crux (Phase 5); `modalStepBranch_worldBound` (Phase 6)
reuses the generic knownWorlds/rank results; `modalExpMeasure_step_lt` (Phase 7) reuses the generic
potential/counting results; and the holistic K re-instantiation + downstream typecheck (Phase 8)
depends on all top lemmas being generic. Each phase is a single agent run ending at a green,
zero-sorry milestone with a task-scoped commit. Per-phase green builds already re-instantiate each
helper's concrete K version incrementally; Phase 8 performs the holistic public-lemma + downstream
confirmation.

---

### Phase 1: Extend RuleApplicationSpec with mint-point outDeg/rank fields [COMPLETED]

- **Goal:** Add to `RuleApplicationSpec` (`GenericDriver.lean`) the additional structural fields the
  exact potential-drop identity needs — capturing the outDeg/rank-map state at the fresh-world mint
  point — and discharge each new field for `modalApplyOne`, keeping `modalApplyOne_spec` sorry-free
  and the whole tree green. This is a design phase whose field set will be refined by later phases.
- **Tasks:**
  - [x] Read `modalStepBranch_potential_step` (line 2148, ~160 lines) and the `geomCap`-based
    potential-drop identity (lines ~2251–2270) to identify exactly which `modalApplyOne` mint-arm
    facts the EXACT decrease consumes beyond the current three fields (`freshLocal`,
    `outputsSubsetUniverse`, `persistentFresh`). *(finding: the crux lemma's own body, once its
    three helper lemmas are generalized, needs no field beyond `freshLocal`; the real gap is one
    level down, in `modalStepBranch_exists_rank'`/`modalStepBranch_preserves_outDegEq`/
    `modalStepBranch_knownWorlds`, each of which `rcases` directly on `modalApplyOne`'s 5-way
    internal rule catalog, not just the 4 `RuleResult` constructor shapes.)*
  - [x] Add one or more fields to `structure RuleApplicationSpec` capturing the mint-point
    interaction as a *precise* statement. *(deviation: altered — rather than a narrow
    outDeg/rank-at-mint-point pair, added three **per-single-call step obligations**
    (`rankStep`, `outDegStep`, `knownWorldsStep`) that restate each helper lemma's own
    K-specific intermediate fact generically over `apply`. This is the minimal-yet-sufficient
    generalization: each field's statement is exactly the conclusion the corresponding helper's
    inline `have hcases := ...` block already established, now parametrized over `apply` instead
    of hard-coded to `modalApplyOne`.)*
  - [x] Discharge each new field for `modalApplyOne` by extending `modalApplyOne_spec` (add the
    supporting concrete lemma(s) in `FmpMeasure.lean` if a mint-point `outDeg`/rank fact is not yet
    isolated as a named public lemma — e.g. an `modalApplyOne_mint_outDeg`-style helper mirroring
    `modalApplyOne_fresh_local`). *(realized as `modalApplyOne_rank_step`,
    `modalApplyOne_outDeg_step`, `modalApplyOne_knownWorlds_step` in `FmpMeasure.lean`, each
    extracted verbatim from the proof body formerly inlined in the corresponding helper lemma —
    zero proof-content change, pure refactor-and-generalize.)*
  - [x] Update `GenericDriver.lean`'s module docstring: move the relevant part of the "Known
    Limitation" note into a documented field-provenance entry for each new field.
  - [x] `lake build` the Tableau tree; `lean_verify modalApplyOne_spec` — zero sorry/axiom.
    *(confirmed: `modalApplyOne_spec` axioms = `{propext, Classical.choice, Quot.sound}` only,
    zero sorry; full `lake build`/`checkInitImports`/`lake lint`/`lint-style`/`lake test` green;
    `lake shake` warning count on `FmpMeasure.lean`+`GenericDriver.lean` unchanged at 82 vs
    pre-change baseline — no new debt.)*
- **Timing:** 2 hours
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — extend `RuleApplicationSpec`; extend
    `modalApplyOne_spec`; docstring.
  - `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — add named mint-point `modalApplyOne` helper
    lemma(s) if needed for the witness (additive only; no existing lemma changed).
- **Verification:**
  - `lake build` green; `modalApplyOne_spec` type-checks sorry-free/axiom-free with the new fields.
  - Full CI clean (`checkInitImports`, `lake lint`, `lint-style`, `lake test`, `shake`).
- **Note:** The field set is provisional — Phases 2–5 may add further fields as real obligations
  surface. Any such addition re-discharges for `modalApplyOne` in the same phase and stays green.

---

### Architectural Note (discovered during Phase 2, applies to Phases 2-7)

**Import-cycle constraint**: `GenericDriver.lean` (`public import
Cslib.Logics.Modal.Tableau.FmpMeasure`) depends on `FmpMeasure.lean` to state
`RuleApplicationSpec`'s fields (they mention `FmpMeasure.lean`-defined predicates:
`accFreshInv`, `accTargetsKnown`, `modalKnownWorlds`, `isMintingShaped`, `modalUniverse`, etc.).
Consequently `FmpMeasure.lean` **cannot** import `GenericDriver.lean` back (cycle), so a `_gen`
lemma physically located in `FmpMeasure.lean` cannot take `spec : RuleApplicationSpec apply` as a
bundled parameter — that type is not yet in scope at that point in the import graph.

**Resolution** (verified against the actual file, no other file references `RuleApplicationSpec`
or imports `GenericDriver.lean` yet, so this is a safe, purely-additive restructuring):
each `_gen` lemma in `FmpMeasure.lean` takes the **raw per-field hypothesis** it needs as an
explicit parameter (e.g. `hOutDegStep : ∀ sf b e acc, ... `, textually identical to
`RuleApplicationSpec.outDegStep`'s field type) rather than a bundled `spec`. `GenericDriver.lean`
(which legitimately imports `FmpMeasure.lean` and holds `RuleApplicationSpec`) then supplies a
thin corollary wrapper unpacking `spec.field` into the raw hypothesis parameter. Concretely:

- `FmpMeasure.lean`: `foo_gen (apply : RuleApply Atom) (hField : ...) ... := by <proof, generic
  over apply/hField>`, plus the **existing** concrete `foo` lemma's proof body is replaced by a
  one-line delegation `rw [modalStepBranch_eq] at hstep; exact foo_gen modalApplyOne
  modalApplyOne_<field-witness> ... hstep ...` (statement byte-unchanged).
- `GenericDriver.lean`: `theorem foo_spec (apply) (spec : RuleApplicationSpec apply) ... := foo_gen
  apply spec.field ...` — the `(apply, spec)`-parametrized form the plan originally specified,
  available here for downstream (T/S5/B) reuse.

This preserves every hard requirement (zero sorry/axiom, K statements byte-unchanged, full reuse
for downstream instances via the `GenericDriver.lean` wrapper) while resolving the cycle. All
phase task descriptions below should be read with this adjustment: "Files to modify:
`FmpMeasure.lean`" additionally implies a corresponding thin wrapper addition in
`GenericDriver.lean`.

---

### Phase 2: Generic outDeg-preservation cluster [COMPLETED]

- **Goal:** Re-derive the outDeg-bookkeeping helpers generically over `(apply, spec)` and
  re-instantiate their K versions. Cluster: `FmpMeasure.lean` lines ~1281–1580.
- **Tasks:**
  - [x] Generalize `modalStepBranch_preserves_outDegEq` (line 1367, ~110 lines) and
    `outDeg_le_of_expandedNodup` (line 1511, ~70 lines) to `_gen` versions over
    `modalStepBranchGen apply` + `spec`, discharging each former `modalApplyOne`-shape `rcases` from
    `spec.freshLocal` and the Phase-1 mint-point field(s). *(deviation: altered —
    `outDeg_le_of_expandedNodup` needs no `_gen` version: on inspection its statement never
    mentions `modalApplyOne`/`modalStepBranch` at all (pure `Accessibility`/list fact given
    `e.Nodup` + closure + the outDeg/e-filter correspondence as hypotheses), so it is already
    fully rule-agnostic and reused as-is. `modalStepBranch_preserves_outDegEq_gen` added in
    `FmpMeasure.lean` takes the raw `hOutDegStep` hypothesis rather than a bundled `spec`, per the
    Architectural Note above; `GenericDriver.lean`'s `modalStepBranchGen_preserves_outDegEq`
    supplies the `(apply, spec)`-bundled wrapper.)*
  - [x] Generalize the supporting private helpers in the cluster: `isMintingShaped_not_prop_applicable`
    (1281), `filter_minting_append_of_not_minting`/`_at`/`_ne` (1309/1321/1333), `outDeg_addEdge_self`
    (1347), `outDeg_addEdge_ne` (1353), `isMintingShaped_inv` (1479), `filter_map_eq_filterMap`
    (1492) — those that reference `modalApplyOne`'s shape move behind `spec`; pure-`Accessibility`
    helpers (`outDeg_addEdge_self`/`_ne`) are already rule-agnostic and may be reused unchanged.
    *(deviation: skipped — none of these private helpers reference `modalApplyOne` or
    `modalStepBranch` at all; all are already fully rule-agnostic (pure `isMintingShaped`/list/
    `Accessibility` facts) and are reused unchanged by `modalStepBranch_preserves_outDegEq_gen`
    with zero edits.)*
  - [x] Re-derive each concrete K helper as `_gen … modalApplyOne modalApplyOne_spec` (or rewire the
    internal callers directly to the `_gen` form) so the file stays green. *(realized as
    `modalStepBranch_preserves_outDegEq := by rw [modalStepBranch_eq] at hstep; exact
    modalStepBranch_preserves_outDegEq_gen modalApplyOne modalApplyOne_outDeg_step ...` — statement
    byte-unchanged, proof now delegates to the generic lemma.)*
  - [x] `lake build`; `lean_verify` no sorry/axiom on each new `_gen` lemma. *(confirmed via direct
    `lake env lean` + `#print axioms`: `modalStepBranch_preserves_outDegEq_gen` = `{propext,
    Quot.sound}`; `modalStepBranchGen_preserves_outDegEq` = `{propext, Quot.sound}`;
    `modalStepBranch_preserves_outDegEq` = `{propext, Classical.choice, Quot.sound}` — all
    standard, zero sorry. Note: the `lean_verify` MCP tool transiently reported a spurious
    `sorryAx` for `modalStepBranchGen_preserves_outDegEq` immediately after the edit — confirmed
    stale/incorrect against direct `lake env lean #print axioms`, which is authoritative.)*
- **Timing:** 2 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — outDeg cluster generalized; K re-derived.
- **Verification:**
  - `lake build` green; zero sorry/axiom; concrete K outDeg lemmas unchanged in statement. Full CI clean.

---

### Phase 3: Generic rank-existence + accessibility helpers [NOT STARTED]

- **Goal:** Re-derive the rank-existence machinery generically. Cluster: `FmpMeasure.lean`
  lines ~1019–1280 (plus the pure edge helper at 1047).
- **Tasks:**
  - [ ] Generalize `modalStepBranch_exists_rank'` (line 1060, ~220 lines) to `_gen` over
    `modalStepBranchGen apply` + `spec`, discharging its `(modalApplyOne …).fst/.snd` `rcases` from
    `spec.freshLocal` (the mint-vs-no-mint dichotomy) and the Phase-1 mint-point rank field.
  - [ ] Generalize/reuse the supporting helpers `diamondNeg_rank_bound` (1019) and
    `hasEdge_addEdge_cases_local` (1047, pure `Accessibility` — reuse unchanged if rule-agnostic).
  - [ ] Re-derive the concrete K `modalStepBranch_exists_rank'` as
    `_gen … modalApplyOne modalApplyOne_spec`; keep the internal callers green.
  - [ ] `lake build`; `lean_verify` no sorry/axiom.
- **Timing:** 2 hours
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — rank-existence cluster generalized; K re-derived.
- **Verification:**
  - `lake build` green; zero sorry/axiom; concrete K rank lemma statement unchanged. Full CI clean.

---

### Phase 4: Generic knownWorlds + accTargetsKnown cluster [NOT STARTED]

- **Goal:** Re-derive the known-worlds / accessibility-target machinery generically. Cluster:
  `FmpMeasure.lean` lines ~1581–2117 (small `modalKnownWorlds`/`modalMaxWorld` helpers plus the two
  larger lemmas).
- **Tasks:**
  - [ ] Confirm the `modalPotentialTerm`/`modalPotential` defs (1581/1588) and the `modalKnownWorlds`
    /`modalMaxWorld` private helpers (1598–1780) are rule-agnostic; reuse unchanged where they do not
    mention `modalApplyOne`.
  - [ ] Generalize `modalStepBranch_preserves_accTargetsKnown` (1788, ~60 lines),
    `mintGroup_label_eq_freshWorld` (1851), `modalStepBranch_knownWorlds` (1903, ~160 lines), and
    `modalStepBranch_eClosure` (2069, ~50 lines) to `_gen` over `modalStepBranchGen apply` + `spec`,
    discharging each `modalApplyOne`-shape `rcases` from `spec.freshLocal` /
    `spec.outputsSubsetUniverse` / the Phase-1 mint-point field(s).
  - [ ] Re-derive the concrete K versions as `_gen … modalApplyOne modalApplyOne_spec`; keep callers green.
  - [ ] `lake build`; `lean_verify` no sorry/axiom.
- **Timing:** 2.5 hours
- **Depends on:** 3
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — knownWorlds cluster generalized; K re-derived.
- **Verification:**
  - `lake build` green; zero sorry/axiom; concrete K knownWorlds/eClosure lemma statements unchanged.
    Full CI clean.
- **Note:** If this cluster overruns one agent run, split at `modalStepBranch_knownWorlds` (line 1903)
  into 4a (helpers + `preserves_accTargetsKnown`) and 4b (`knownWorlds` + `eClosure`), appending 4b
  to this plan; both must end green.

---

### Phase 5: Generic potential-step crux (geomCap exact drop) [NOT STARTED]

- **Goal:** Generalize the crux lemma `modalStepBranch_potential_step` (line 2148, ~160 lines) and
  the `ModalPotentialInv` structure (2118) over `(apply, spec)`, replaying the EXACT `geomCap`-based
  potential-drop identity (lines ~2251–2270) generically — not merely as a bound. This is the make-
  or-break phase the whole re-derivation was gated on.
- **Tasks:**
  - [ ] Generalize `structure ModalPotentialInv` (2118) if it references `modalApplyOne`; otherwise
    reuse. Generalize `modalStepBranch_potential_step` to `_gen` over `modalStepBranchGen apply` +
    `spec`, feeding each mint-arm obligation from the Phase-1 mint-point field(s) and the generic
    Phase-2/3/4 results (`modalStepBranch_preserves_outDegEq_gen`, `modalStepBranch_exists_rank'_gen`,
    `modalStepBranch_knownWorlds_gen`).
  - [ ] Reproduce the `geomCap` EXACT numeric decrease from the spec's exact outDeg-at-mint field; if
    the current field only yields a bound, extend `RuleApplicationSpec` with the missing exact-equality
    field, re-discharge it for `modalApplyOne` in `GenericDriver.lean`, and continue (stay green).
  - [ ] Re-derive concrete K `modalStepBranch_potential_step` as `_gen … modalApplyOne modalApplyOne_spec`.
  - [ ] `lake build`; `lean_verify` no sorry/axiom.
- **Timing:** 3 hours (exceeds the 1–2h guideline by design — this is the crux; single-agent-run
  bounded; write an 80%-context handoff if approaching the limit).
- **Depends on:** 4
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — `ModalPotentialInv` + potential-step lemma
    generalized; K re-derived.
  - `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — additional exact-drop field(s) + re-discharge
    if Phase-1 fields prove insufficient.
- **Verification:**
  - `lake build` green; zero sorry/axiom; concrete K potential-step statement unchanged. Full CI clean.
- **[BLOCKED] fallback:** If the EXACT `geomCap` identity cannot be replayed sorry-free (only bounded,
  or a required exact field is unprovable for `modalApplyOne`), mark this phase **[BLOCKED]** with the
  exact open lemma name, the goal state at the failing step, and which spec field is insufficient
  (identity-vs-bound gap). Preserve Phases 1–4 green and committed. Never introduce `sorry`/`axiom`.

---

### Phase 6: Generic modalStepBranch_worldBound [NOT STARTED]

- **Goal:** Generalize `modalStepBranch_worldBound` (line 2378, ~60 lines) and its supporting
  `modalSf` helpers over `(apply, spec)`, reusing the generic rank/knownWorlds results from Phases 3–4.
- **Tasks:**
  - [ ] Confirm `modalSf_pos` (2310) and `modalSf_one_imp_depth_zero` (2318) are rule-agnostic
    (reuse unchanged). Generalize `modalStepBranch_worldBound` to `_gen`, discharging its mint-arm
    reasoning from `spec.freshLocal` + the Phase-1 mint-point field and the generic
    `modalStepBranch_knownWorlds_gen`/`modalStepBranch_exists_rank'_gen`.
  - [ ] Re-derive concrete K `modalStepBranch_worldBound` as `_gen … modalApplyOne modalApplyOne_spec`.
  - [ ] `lake build`; `lean_verify` no sorry/axiom.
- **Timing:** 1.5 hours
- **Depends on:** 5
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — worldBound lemma generalized; K re-derived.
- **Verification:**
  - `lake build` green; zero sorry/axiom; concrete K worldBound statement unchanged. Full CI clean.

---

### Phase 7: Generic modalExpMeasure_step_lt + counting-measure helpers [NOT STARTED]

- **Goal:** Generalize `modalExpMeasure_step_lt` (line 2875) and its counting-measure dependency
  cluster over `(apply, spec)`, reusing `spec.persistentFresh`. Cluster: `FmpMeasure.lean`
  lines ~2442–2961.
- **Tasks:**
  - [ ] Generalize `modalWork_drop_persistent` (2558) and `modalWork_drop_linear` (2541) reasoning to
    consume `spec.persistentFresh`/`spec.outputsSubsetUniverse` instead of
    `modalApplyOne_persistent_props`. Reuse the rule-agnostic `modalCount_notMem_*` (2442/2519) and
    `modalExpMeasure_split`/`_append`/`_const_exp` (2828/2845/2858) helpers unchanged.
  - [ ] Generalize the propositional/branching helpers that `rcases` on `modalApplyOne`'s shape
    (`boxPropagation_fresh` 2663, `diamondNeg_filterMap_fresh` 2686, `modalApplyOne_branching_length`
    2779, `applyPropRule_*`/`tryAllPropRules_*` 2582–2661) to their `spec`-mediated forms, or keep
    them as K-specific facts consumed only via `modalApplyOne_spec` if they are purely about
    `modalApplyOne`'s own catalog.
  - [ ] Generalize `modalExpMeasure_step_lt` to `_gen` over `modalStepBranchGen apply` + `spec`;
    re-derive concrete K version as `_gen … modalApplyOne modalApplyOne_spec`.
  - [ ] `lake build`; `lean_verify` no sorry/axiom.
- **Timing:** 2 hours
- **Depends on:** 6
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — expMeasure-step cluster generalized; K re-derived.
- **Verification:**
  - `lake build` green; zero sorry/axiom; concrete K `modalExpMeasure_step_lt` statement unchanged.
    Full CI clean.

---

### Phase 8: K re-instantiation, downstream typecheck, and final CI [NOT STARTED]

- **Goal:** Holistically confirm the three public top lemmas are re-instantiated with byte-unchanged
  K statements, that `FmpMeasure.lean`'s K corollaries and `CompletenessLoop.lean`'s uses still
  typecheck via the Phase-1 `_eq` bridges, run the full CSLib CI end-to-end, finalize the
  `GenericDriver.lean` interface docstring, and write the completion summary.
- **Tasks:**
  - [ ] Confirm `modalStepBranch_potential_step`, `modalStepBranch_worldBound`, and
    `modalExpMeasure_step_lt` exist as concrete K corollaries with statements byte-identical to their
    pre-507 forms (diff against `git show d5b24e67:…FmpMeasure.lean` region) and are
    `_gen … modalApplyOne modalApplyOne_spec` instantiations.
  - [ ] Build the whole Tableau tree including `CompletenessLoop.lean`; confirm every downstream use
    of the three K corollaries still typechecks (no statement drift; `_eq` bridges applied where the
    generic driver defs are involved). Read-only: do not edit `CompletenessLoop.lean`.
  - [ ] Update `GenericDriver.lean`'s module docstring: replace the "Known Limitation" note with a
    "Sufficiency" note recording the final field set and that the three termination lemmas are now
    proven generically; keep the downstream-reuse contract for T/S5/B and the S4 exclusion.
  - [ ] Run the full CSLib CI in order: `lake build`, `lake exe checkInitImports`, `lake lint`,
    `lake exe lint-style`, `lake test`, `lake exe mk_all --module`,
    `lake shake --add-public --keep-implied --keep-prefix`. Fix any lint on new decls.
  - [ ] Final `lean_verify` sweep on all new/changed top decls (`RuleApplicationSpec`,
    `modalApplyOne_spec`, each `_gen` lemma, and the three re-instantiated K corollaries): confirm
    zero sorry / zero axiom.
  - [ ] Write `specs/507_.../summaries/01_generalize-fmp-termination-measure-summary.md`.
- **Timing:** 1 hour
- **Depends on:** 7
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — interface docstring finalization.
  - `specs/507_generalize_k_fmp_termination_measure_over_ruleapplicationspec/summaries/01_generalize-fmp-termination-measure-summary.md` (new).
- **Verification:**
  - Full CI green; zero sorry/axiom on all touched decls; K public statements byte-unchanged;
    `CompletenessLoop.lean` typechecks; interface documented as sufficient.

---

## Testing & Validation

Run the full CSLib CI pipeline at the end of **every** phase (order per `cslib.md`):
- [ ] `lake build` — green, and **zero `sorry` / zero new `axiom`** in all delivered decls
  (`lean_verify` on each new `_gen` lemma and re-instantiated K corollary).
- [ ] `lake exe checkInitImports` — `GenericDriver.lean`/`FmpMeasure.lean` import `Cslib.Init`.
- [ ] `lake lint` — docstrings on every new decl (docBlame); Prop-valued results as `lemma`/`theorem`
  (defLemma); lowerCamelCase names; `@[simp]` only with verified LHS (simpNF); `omit`/`include`
  unused section vars.
- [ ] `lake exe lint-style` — style clean.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe mk_all --module` — no new files added (GenericDriver.lean already registered); run to
  confirm the barrel import is consistent.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — dependency analysis clean.
- [ ] Zero-regression gate: `modalStepBranch_potential_step`/`modalStepBranch_worldBound`/
  `modalExpMeasure_step_lt` unchanged in statement and still green as K corollaries; downstream
  `CompletenessLoop.lean` typechecks.
- [ ] Acceptance: the three termination lemmas hold for an abstract `(apply, spec :
  RuleApplicationSpec apply)` and are genuinely sorry-free / axiom-free.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — `RuleApplicationSpec` extended with mint-point
  outDeg/rank field(s); `modalApplyOne_spec` re-discharged; finalized interface/sufficiency docstring.
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` — generic `_gen` re-derivations of the full
  rule-dependent dependency chain and the three top-level step lemmas over `(apply, spec)`; K
  re-instantiated as `_gen … modalApplyOne modalApplyOne_spec`; world-agnostic size bounds unchanged.
- `specs/507_.../summaries/01_generalize-fmp-termination-measure-summary.md` (on completion).

## Rollback/Contingency

- Each phase is a self-contained, task-scoped commit at a green milestone; revert an individual
  phase's commit to roll back without disturbing prior phases.
- The generalization is behavior-preserving for K: the three public termination lemmas keep their
  exact statements as re-instantiated corollaries, so reverting the `FmpMeasure.lean`/
  `GenericDriver.lean` changes restores the original hard-coded K measure intact. All `_gen` lemmas
  and new spec fields are additive.
- Preferred contingency for the crux (Phase 5 generic potential-step) is a documented **[BLOCKED]**
  handoff with the open goal state and the exact insufficient spec field — never a `sorry` or
  `axiom`. Phases 1–4 (extended interface + generic dependency chain) stand alone and advance the
  interface even if 5–7 must be deferred; any deferred residue is sequenced as new phases appended
  to this plan.
```
