# Implementation Plan: Task #421 — Min-side FMP Decidability

- **Task**: 421 - Min-side FMP decidability: sorry-free `Decidable (Derivable MinPropAxiom φ)` mirroring the Int construction (completes parent 370 Min side)
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: 411 (Int FMP construction must be on main — confirmed: `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` is present, 436 lines)
- **Research Inputs**: specs/421_min_fmp_decidability/reports/01_min-fmp-decidability-research.md
- **Artifacts**: plans/01_min-fmp-decidability-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add a sorry-free `Decidable (Derivable MinPropAxiom φ)` instance for minimal propositional
logic via the finite model property, by creating a new file
`Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` that is a **1:1 but strictly-simpler
mirror** of the on-main `IntDecidability.lean` (436 lines). The construction chain is
`MinFinWorld → minFinVal → minFinVal_upward_closed → min_fin_truth_lemma → min_fmp →
instDecidableDerivableMinPropAxiom'`. Definition of done: the new instance is sorry-free, the
full CSLib CI pipeline is green, and `#print axioms instDecidableDerivableMinPropAxiom'` is
exactly `{propext, Classical.choice, Quot.sound}` with no `sorryAx` and 0 new `sorry`.

### Research Integration

The research report (`reports/01_min-fmp-decidability-research.md`) establishes that this is a
near-mechanical port with **zero gaps**: every Int supporting lemma already has an exact Min
analogue (MinTheory/MinPrimeTheory at `MinLindenbaum.lean:55,156`; `min_imp_witness` at `:138`;
`min_prime_exclusion` at `:169`; `minDeductiveClosure_is_theory` at `:125`;
`min_subset_deductive_closure` at `:118`; `minDeductiveClosure_iff_SetDerivable` at
`MinStrongCompleteness.lean:243`; `min_soundness_derivable` at `MinSoundness.lean:115`).
`SetDerivable*`, `IForces*`, the subformula helpers, and `MinPropAxiom.{andI,andE1,andE2,orI1,orI2}`
are shared/axiom-polymorphic. The port is *easier* than Int because minimal logic has **no
EFQ/explosion**, which removes four pieces of machinery (see Goals). The only genuinely-new
declarations are `minFinBotForces` and its one-line upward-closure lemma (mirroring the existing
`minBotForces` at `MinStrongCompleteness.lean:101`), because Min worlds may legitimately contain
`⊥`, so Int's inlined `fun _ => False` is unsound for Min.

The phase decomposition below follows the report's §7 recommended breakdown directly.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in delegation context; roadmap consultation skipped. This task
completes the Min side of parent task 370 (Int+Min decidability asymmetry) and coordinates
with task 422 (route reconciliation) — see the Note for task 422 below.

## Goals & Non-Goals

**Goals**:
- Create `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` mirroring Int, with the
  four simplifications minimal logic permits:
  1. `MinFinWorld` **drops the `consistent` field** (`MinTheory` = closed only, no consistency conjunct).
  2. The ~40-line `intFinWorld_propConsistent` helper is **eliminated** (`min_imp_witness` needs no consistency hypothesis).
  3. The truth-lemma `bot` case is `Iff.rfl`.
  4. The `min_fmp` backward direction drops all `PropSetConsistent ∅` plumbing.
- Add the only two new declarations: `minFinBotForces := (⊥ ∈ ·.carrier)` and
  `minFinBotForces_upward_closed`.
- Produce a sorry-free `instDecidableDerivableMinPropAxiom'` of type `Decidable (Derivable MinPropAxiom φ)`.
- Wire the new module into `Cslib.lean` (barrel) via `lake exe mk_all --module`.
- Pass full CSLib CI and the axiom audit.

**Non-Goals**:
- Do **not** implement the shared `FinWorld`/`fmp`/`Decidable` abstraction parametrized over a
  consistency predicate `Cons` (that is task 422's scope; the report flags it only).
- Do not modify `IntDecidability.lean` or any existing Min/Int completeness/soundness file.
- Do not introduce new `@[simp]` lemmas, new axioms, or any `sorry`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Min lemma signature differs subtly from the assumed analogue (e.g. arg order, implicit vs explicit) | M | L | Report §4 catalogues exact locations; inspect the Int proof line + Min signature with `lean_hover_info`/`lean_declaration_file` before porting each step. Do **not** defer with `sorry`. |
| `min_soundness_derivable` 6-arg call (vs Int 4-arg) wired incorrectly (order of `bot_forces`, `bf_uc`) | M | M | Read `MinSoundness.lean:115` signature directly; pass `minFinVal minFinBotForces minFinVal_upward_closed minFinBotForces_upward_closed w` per report §7 Phase 4. |
| `MinPrimeTheory` access pattern wrong (`.1` vs `.1.2`) | L | M | Report §2/§4: Min uses `MinPrimeTheory.1` directly where Int uses `IntPrimeDCCS.1.2`. Verify with `lean_hover_info`. |
| `[DecidableEq Atom]` omitted (Min completeness files use `{Atom : Type*}` without it) | M | L | Match Int exactly: `variable {Atom : Type u} [DecidableEq Atom]` plus `attribute [local instance] Classical.propDecidable` (report §5). |
| Lint failures (docBlame on new decls, def naming) | L | M | Every new declaration gets a docstring adapted from Int; `def` only for `MinFinWorld`, `minFinVal`, `minFinBotForces`, `minFinWorldOfPrimeTheory`; theorem names match sibling Int snake_case convention which passes CI (report §8). |
| Axiom closure includes `sorryAx` or extra axioms | H | L | Final-gate `#print axioms` / `lean_verify`; zero-debt by construction (report §9) since every step maps to an existing sorry-free Min lemma. |
| `lake shake` flags unused/missing imports | L | M | Use the exact 4-line header from report §5; run `lake shake --add-public --keep-implied --keep-prefix` in Phase 4 and adjust imports if flagged. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases are strictly sequential: each builds Lean declarations that the next depends on. Each
phase is sized to one agent run (~one logical layer, well under the 100-500 line bound).

---

### Phase 1: Scaffold — world type, Fintype/Preorder infra, valuation + bot_forces layer [COMPLETED]

**Goal**: Stand up the file with its header/preamble and all the structural/definitional
declarations that carry no real proof obligation, so later phases have the world type, finite
instances, valuation, and the new `bot_forces` predicate available.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` with the verbatim header (report §5):
  `module` / `import Cslib.Init` / `public import Cslib.Logics.Propositional.Metalogic.MinStrongCompleteness` / `public import Cslib.Logics.Propositional.Subformula` / `public import Mathlib.Data.Finset.Powerset`.
- [ ] Add preamble (report §5): `@[expose] public section`, `namespace Cslib.Logic.PL`, `open Cslib.Logic`, `universe u`, `variable {Atom : Type u} [DecidableEq Atom]`, `attribute [local instance] Classical.propDecidable`.
- [ ] `structure MinFinWorld φ` mirroring `IntFinWorld` but **dropping the `consistent` field**: fields `carrier`/`sub`/`closed`/`prime`; `closed` uses `SetDerivable MinPropAxiom`.
- [ ] `MinFinWorld.ext` (identical to Int: `cases; cases; congr`).
- [ ] `instPreorderMinFinWorld` (carrier inclusion, identical to Int).
- [ ] `minFinWorld_carrier_injective` (identical to Int).
- [ ] `instFintypeMinFinWorld` — `noncomputable instance` via `Fintype.ofInjective` (identical to Int).
- [ ] `minFinVal` := `atom p ∈ w.carrier` (identical to Int).
- [ ] `minFinVal_upward_closed` (identical to Int: `hw hv`).
- [ ] **NEW** `minFinBotForces {φ} (w : MinFinWorld φ) : Prop := (⊥ : PL.Proposition Atom) ∈ w.carrier` (mirrors `minBotForces` at `MinStrongCompleteness.lean:101`).
- [ ] **NEW** `minFinBotForces_upward_closed {φ} {w w' : MinFinWorld φ} (hw : w ≤ w') (hbf : minFinBotForces w) : minFinBotForces w' := hw hbf`.
- [ ] Add a docstring to every declaration (docBlame); adapt from Int / `minBotForces`.

**Timing**: ~1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` (create) — header, preamble, world type + finite instances + valuation + bot_forces layer.

**Verification**:
- Scoped build green: `lake build Cslib.Logics.Propositional.Metalogic.MinDecidability`.
- No `sorry` introduced; `lean_diagnostic_messages` clean for the file.

---

### Phase 2: `min_fin_imp_witness` [COMPLETED]

**Goal**: Port the finite implication-witness lemma (Int lines 187-248) in its simplified form.

**Tasks**:
- [ ] Port `int_fin_imp_witness` → `min_fin_imp_witness`, **dropping the consistency step (Int steps 2-3)** and the `consistent'` field.
- [ ] Use `minDeductiveClosure_is_theory` (`MinLindenbaum.lean:125`, **no consistency arg**), `min_imp_witness` (`:138`), `min_prime_exclusion` (`:169`).
- [ ] Apply the mechanical access change: `IntDCCS`/`.1.2` → `MinTheory`/`.1`; `IntPrimeDCCS` → `MinPrimeTheory`.
- [ ] Omit the `int_dccs_bot_not_mem` line entirely (no `consistent` field on `MinFinWorld`).
- [ ] Add docstring adapted from Int.

**Timing**: ~1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` — add `min_fin_imp_witness`.

**Verification**:
- Scoped build green: `lake build Cslib.Logics.Propositional.Metalogic.MinDecidability`.
- `lean_goal`/`lean_diagnostic_messages` confirm no remaining goals, no `sorry`.

---

### Phase 3: `min_fin_truth_lemma` [COMPLETED]

**Goal**: Port the finite truth lemma (Int lines 275-356) by formula induction, with the
simplified `bot` case.

**Tasks**:
- [ ] Port `int_fin_truth_lemma` → `min_fin_truth_lemma`.
- [ ] **bot case** becomes `Iff.rfl` (since `IForces _ minFinBotForces w .bot` reduces definitionally to `minFinBotForces w = (⊥ ∈ w.carrier)`; mirrors `min_truth_lemma` `| .bot => Iff.rfl` at `MinStrongCompleteness.lean:128`).
- [ ] Pass `minFinBotForces` as the `bot_forces` argument to the forcing relation.
- [ ] Replace `IntPropAxiom.*` → `MinPropAxiom.*` (the `.andI/andE1/andE2/orI1/orI2` constructors exist at `FragmentAxioms.lean:67-271`).
- [ ] Keep the `w.closed`/`v.closed` MP-closure cases unchanged (modulo `MinPropAxiom`); use `min_fin_imp_witness` from Phase 2 for the imp case.
- [ ] Add docstring adapted from Int.

**Timing**: ~1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` — add `min_fin_truth_lemma`.

**Verification**:
- Scoped build green: `lake build Cslib.Logics.Propositional.Metalogic.MinDecidability`.
- No `sorry`; diagnostics clean.

---

### Phase 4: FMP + Decidable instance + barrel wiring + full CI + axiom audit [COMPLETED]

**Goal**: Complete the construction (`min_fmp`, the Decidable instance), wire the barrel, and
pass the full CSLib CI pipeline plus the axiom audit.

**Tasks**:
- [ ] `minFinWorldOfPrimeTheory` (`private`) — mirror Int's private `intFinWorldOfPrimeDCCS`, **dropping the `consistent` field**; `IntPrimeDCCS` → `MinPrimeTheory`; `hT.1.2` → `hT.1`; drop the `int_dccs_bot_not_mem` line.
- [ ] `min_fmp`:
  - forward direction via `min_soundness_derivable` with 6 explicit args: `minFinVal minFinBotForces minFinVal_upward_closed minFinBotForces_upward_closed w` (returns `MValid`);
  - backward direction via `min_prime_exclusion (minDeductiveClosure_is_theory ∅) …`, **dropping all `int_consistent` / `PropSetConsistent ∅` plumbing**.
- [ ] `instDecidableDerivableMinPropAxiom'` — `noncomputable instance` `Decidable (Derivable MinPropAxiom φ)` via `decidable_of_iff … (min_fmp φ).symm` (identical to Int).
- [ ] Add docstrings to all new declarations.
- [ ] Wire `Cslib.lean`: add `public import Cslib.Logics.Propositional.Metalogic.MinDecidability` immediately after the `IntDecidability` import (after line 423). Prefer regenerating the barrel with `lake exe mk_all --module` rather than hand-editing.
- [ ] Run full CI: `lake build`; `lake test`; `lake exe checkInitImports`; `lake exe lint-style`; `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] **Axiom audit**: add/run `#print axioms instDecidableDerivableMinPropAxiom'` (or `lean_verify Cslib.Logic.PL.instDecidableDerivableMinPropAxiom'`); confirm the closure is exactly `{propext, Classical.choice, Quot.sound}` with **no `sorryAx`** and 0 `sorry` in the file.

**Timing**: ~1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` — add `minFinWorldOfPrimeTheory`, `min_fmp`, `instDecidableDerivableMinPropAxiom'`.
- `Cslib.lean` — add the `MinDecidability` barrel import after line 423 (regenerate via `mk_all`).

**Verification**:
- Full CI pipeline green (all five commands above).
- `#print axioms` / `lean_verify` shows exactly `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.
- `grep -c sorry` on the new file = 0.

---

## Testing & Validation

- [ ] Scoped build after each of Phases 1-3: `lake build Cslib.Logics.Propositional.Metalogic.MinDecidability`.
- [ ] Full `lake build` green (Phase 4).
- [ ] `lake test` (CslibTests suite) green.
- [ ] `lake exe checkInitImports` green.
- [ ] `lake exe lint-style` green.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` green.
- [ ] `#print axioms instDecidableDerivableMinPropAxiom'` = `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.
- [ ] 0 occurrences of `sorry` in `MinDecidability.lean`.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` (new file — the full mirror construction).
- `Cslib.lean` (modified — added barrel import after line 423).
- `specs/421_min_fmp_decidability/plans/01_min-fmp-decidability-plan.md` (this plan).
- `specs/421_min_fmp_decidability/summaries/01_min-fmp-decidability-summary.md` (produced at implementation completion).

## Rollback/Contingency

- The change is additive and isolated: one new file plus one barrel import line. To revert, delete
  `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` and remove its import from `Cslib.lean`
  (or re-run `lake exe mk_all --module`), then `lake build` to confirm main is restored. No existing
  file is modified beyond the barrel.
- If a single port step resists (the only realistic failure mode), the escalation path per report §9
  is to inspect the corresponding Int proof line and the exact Min lemma signature (catalogued in
  report §4) with `lean_hover_info`/`lean_declaration_file` — **never** defer with `sorry`, since the
  acceptance criterion forbids it.
