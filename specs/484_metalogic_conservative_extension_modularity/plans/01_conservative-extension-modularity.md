# Implementation Plan: Task #484 — Conservative-Extension & Modularity Across the Propositional-Strength × Modal-Axiom Lattice

- **Task**: 484 - Conservative-extension and modularity across the full propositional-strength × modal-axiom lattice (capstone)
- **Status**: [NOT STARTED]
- **Effort**: 11 hours
- **Dependencies**: None (Phase 3 constructive-cube work is independent of the CS4/CS5 completeness blocker, task 501)
- **Research Inputs**: reports/01_conservative-extension-modularity.md
- **Artifacts**: plans/01_conservative-extension-modularity.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This capstone ties together the four propositional bases (minimal, constructive, intuitionistic, classical) and every modal system (K/T/S4/S5 + D/B/K4/K5) that already exist in `Cslib/Logics/Modal/Metalogic/`. All of them derive theorems through **one** shared framework — `Derivable Axioms φ := Nonempty (DerivationTree Axioms [] φ)` over `Proposition Atom`, parameterized by an axiom predicate `Axioms : Proposition Atom → Prop`. Because the framework is uniform, cross-lattice **monotonicity** (`Derivable Weaker φ → Derivable Stronger φ`) is, on all edges except one, a mechanical `cases`-subsumption fed into the already-existing generic lift `Derivable_mono` (`InterSystem/Lifting.lean:66`).

The definition of done: (1) per-base modal-cube monotonicity for the minimal, intuitionistic, and constructive bases (mirroring the already-complete classical cube); (2) cross-base propositional-strength monotonicity into the intuitionistic base (MK→IK, CK→IK and per-rung); (3) a green modularity-synthesis module that reuses the existing Axis-C conservativity and states the framing distinction precisely; and (4) the one genuinely hard edge — Intuitionistic⟶Classical (IK→K) — delivered via a new generalized `axiom → derivation` lift plus per-axiom classical derivations, under a mandatory Zero-Debt STOP/`[BLOCKED]` gate.

**Constraint (concurrent sessions):** other Claude sessions edit this repo concurrently. Every phase MUST (a) re-read any shared file (`Cslib.lean`, and any `InterSystem/` file it did not itself create) immediately before editing it, and (b) commit green at phase end before the next phase begins. Deliverable `.lean` files are disjoint per phase so parallel work does not collide; the only shared file is `Cslib.lean`, whose import lines must be appended after a fresh re-read.

### Research Integration

The plan adopts the report's phase decomposition verbatim: report Phase 1 (per-base cubes), Phase 2 (cross-base into intuitionistic), Phase 4 (synthesis) are all cheap and Zero-Debt-safe; report Phase 3 (IK→K bridge) is the sole hard/gated area. The plan re-orders so that all cheap Zero-Debt work AND the modularity capstone land and commit green **before** the risky IK→K bridge, so a bridge block still leaves a green, valuable capstone. Load-bearing findings respected:

1. **Unified framework**: everything is `Derivable Axioms φ` over `Proposition Atom`; conservativity/monotonicity is axiom-predicate inclusion; `Derivable_mono` lifts uniformly.
2. **Framing correction** (reflected in lemma naming): on the lattice edges the same-language CONVERSE is false (T proves `□φ→φ`; classical proves Peirce), so those results are **monotonicity**, not conservativity. Genuine conservativity lives only on Axis C (modal-over-propositional, already done) and PL fragments (already done). Lemmas on Axes A/B are named `*_mono` / `xDerivable_implies_yDerivable`; the word "conservative" is reserved for the reused Axis-C results.
3. **What exists (reuse, do not duplicate)**: classical modal-cube monotonicity (24 edges, `InterSystem/AxiomSubsumption.lean` + `Conservativity.lean`); modal-over-CPL conservative extension (`Metalogic/ConservativeExtension.lean`); PL strength subsumption + monotonicity chain; algebraic fragment-conservativity converses; Bimodal semantic-embedding precedent. The classical `AxiomSubsumption.lean` is the exact copy template.
4. **What's missing (the deliverables)**: per-base modal-cube monotonicity (min/int/constr); cross-base MK→IK, CK→IK; and the IK→K bridge needing a NEW generalized `axiom → derivation` lift plus per-axiom classical derivations of `kdia/cd/idb/dbot` (and rung diamond schemata).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided to this planning run; no ROADMAP.md consulted.

## Goals & Non-Goals

**Goals**:
- Per-base modal-cube **monotonicity** for the minimal, intuitionistic, and constructive bases (MK→MT→MS4→MS5; IK→IT→IS4→IS5; CK→CT→CS4→CS5), plus frame-condition inclusion lemmas witnessing module composition.
- Cross-base propositional-strength **monotonicity** into the intuitionistic base: MK→IK, CK→IK and per-rung {MT,CT}→IT, {MS4,CS4}→IS4, {MS5,CS5}→IS5.
- A green `InterSystem/Modularity.lean` synthesis module that re-exports the monotonicity results, reuses the existing Axis-C conservativity (`modal_conservative_extension`), and documents the three-axis framing (monotonicity on Axes A/B vs conservativity on Axis C + PL fragments), including the MK/CK incomparability.
- The IK→K bridge (FULL SCOPE, not deferred): a new generalized lift `Derivable_of_axiom_derivable` plus per-axiom classical K/T/S4/S5 derivations of the Fischer-Servi and rung diamond schemata, assembled into `Derivable IKModalAxiom φ → Derivable KAxiom φ` (and rung analogues).
- Zero debt: no `sorry`, no new axiom, no vacuous `def X := True`. The bridge is STOP/`[BLOCKED]`-gated per schema.

**Non-Goals**:
- Do NOT attempt any same-language conservativity CONVERSE on Axes A/B (it is false: T proves `□φ→φ`, classical proves Peirce). "Modularity" on those axes = the monotone chain + frame-condition inclusions.
- Do NOT attempt to unblock CS4/CS5 completeness (blocked upstream, task 501). Constructive-cube monotonicity is purely syntactic and does not need it.
- Do NOT build modal analogues of Glivenko / bot-free conservativity converses (needs new modal-algebraic machinery; future work).
- Do NOT introduce new Mathlib API. Work is inductive `cases`/`match` on in-repo predicates; only `And` projections and existing modal combinators are needed.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| IK→K per-axiom derivations (`cd`, `idb`) resist sorry-free closure | H | M | Isolated to Phases 6-7 (own waves, last). Mandatory Zero-Debt STOP clause: record exact goal state + missing combinator, mark the specific schema `[BLOCKED]`, escalate. Never `sorry`/axiom/vacuous placeholder. Phases 1-5 ship regardless. |
| Concurrent session clobbers `Cslib.lean` import edits | M | M | Re-read `Cslib.lean` immediately before appending imports; commit green per phase; deliverable `.lean` files are disjoint per phase. |
| Mislabeling monotonicity as conservativity (framing regression) | M | L | Enforce naming: Axes A/B lemmas end in `_mono` / `..._implies_...`; "conservative" reserved for reused Axis-C results. Module docstrings state the distinction. |
| CS4/CS5 completeness blocker mistaken as blocking Phase 3 (constructive cube) | M | L | Docstring + plan note: constructive-cube monotonicity is syntactic (`cases` only), independent of completeness. |
| Generalized lift `Derivable_of_axiom_derivable` mis-structured (non-terminating recursion / universe issues) | M | L | Model on existing `liftDerivation` structural recursion (`Lifting.lean:47`); discharge `ax` via supplied derivation, recurse through the other constructors using closure of `Derivable A₂` under the `DerivationTree` rules. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- |
| 2 | 5 | 1, 2, 3, 4 |
| 3 | 6 | 5 |
| 4 | 7 | 6 |

Phases within the same wave can execute in parallel (disjoint deliverable `.lean` files). The only shared file is `Cslib.lean`; its import registration must be serialized by re-reading immediately before appending. Waves 1-2 are the Zero-Debt green capstone; waves 3-4 are the gated IK→K bridge (report Phase 3), placed last so a bridge block leaves a green capstone.

---

### Phase 1: Minimal-base modal-cube monotonicity [COMPLETED]

**Goal**: Establish `MKModalAxiom → MTModalAxiom → MS4ModalAxiom → MS5ModalAxiom` subsumption and the `Derivable`-level monotonicity chain, plus frame-condition inclusion lemmas, mirroring the classical `AxiomSubsumption.lean` / `Conservativity.lean` template. (Report Phase 1, minimal base.)

**Tasks**:
- [ ] Read `InterSystem/AxiomSubsumption.lean` and `InterSystem/Conservativity.lean` as the copy template; read the minimal predicates `MK.lean:68`, `MT.lean:69`, `MS4.lean:66`, `MS5.lean:76`.
- [ ] Create `Cslib/Logics/Modal/Metalogic/InterSystem/MinimalLatticeSubsumption.lean`: `cases`-subsumption lemmas `MKModalAxiom_implies_MTModalAxiom`, `MTModalAxiom_implies_MS4ModalAxiom`, `MS4ModalAxiom_implies_MS5ModalAxiom` (each ~14-20 constructor lines).
- [ ] Create `Cslib/Logics/Modal/Metalogic/InterSystem/MinimalLatticeMonotonicity.lean`: `Derivable`-level corollaries `mkDerivable_implies_mtDerivable := Derivable_mono …`, etc.; plus frame-condition inclusion lemmas `ms4FC m → mtFC m`, `ms5FC m → ms4FC m` (`fun h => h.1`-style projections). Naming uses `_mono` / `_implies_`, NOT "conservative".
- [ ] Re-read `Cslib.lean`, then append `public import` lines for both new modules (place near the existing InterSystem imports at lines 365-368).
- [ ] Run CI (see Testing & Validation); commit green: `task 484 phase 1: minimal-base modal-cube monotonicity`.

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/MinimalLatticeSubsumption.lean` — new, `cases`-subsumption lemmas
- `Cslib/Logics/Modal/Metalogic/InterSystem/MinimalLatticeMonotonicity.lean` — new, `Derivable_mono` corollaries + FC inclusions
- `Cslib.lean` — append two `public import` lines (re-read first)

**Verification**:
- `lake build` of the two new modules succeeds; no `sorry`/`axiom`.
- The three subsumption lemmas and their `Derivable`-level corollaries typecheck; FC inclusion lemmas typecheck.

---

### Phase 2: Intuitionistic-base modal-cube monotonicity [COMPLETED]

**Goal**: `IKModalAxiom → ITModalAxiom → IS4ModalAxiom → IS5ModalAxiom` subsumption + `Derivable`-level chain + FC inclusions. (Report Phase 1, intuitionistic base.)

**Tasks**:
- [ ] Read intuitionistic predicates `IK.lean:75`, `IT.lean:71`, `IS4.lean:72`, `IS5.lean:84`.
- [ ] Create `InterSystem/IntuitionisticLatticeSubsumption.lean`: `IKModalAxiom_implies_ITModalAxiom`, `ITModalAxiom_implies_IS4ModalAxiom`, `IS4ModalAxiom_implies_IS5ModalAxiom`.
- [ ] Create `InterSystem/IntuitionisticLatticeMonotonicity.lean`: `ikDerivable_implies_itDerivable`, etc., via `Derivable_mono`; FC inclusions `is4FC → itFC`, `is5FC → is4FC`.
- [ ] Re-read `Cslib.lean`; append two `public import` lines.
- [ ] Run CI; commit green: `task 484 phase 2: intuitionistic-base modal-cube monotonicity`.

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/IntuitionisticLatticeSubsumption.lean` — new
- `Cslib/Logics/Modal/Metalogic/InterSystem/IntuitionisticLatticeMonotonicity.lean` — new
- `Cslib.lean` — append two `public import` lines (re-read first)

**Verification**:
- `lake build` succeeds; no `sorry`/`axiom`; lemmas typecheck.

---

### Phase 3: Constructive-base modal-cube monotonicity [COMPLETED]

**Goal**: `CKModalAxiom → CTModalAxiom → CS4ModalAxiom → CS5ModalAxiom` subsumption + `Derivable`-level chain + FC inclusions. Explicitly independent of the CS4/CS5 completeness blocker (task 501) — monotonicity is purely syntactic. (Report Phase 1, constructive base.)

**Tasks**:
- [ ] Read constructive predicates `CK.lean:104`, `CT.lean:61`, `CS4.lean:68`, `CS5.lean:69`.
- [ ] Create `InterSystem/ConstructiveLatticeSubsumption.lean`: `CKModalAxiom_implies_CTModalAxiom`, `CTModalAxiom_implies_CS4ModalAxiom`, `CS4ModalAxiom_implies_CS5ModalAxiom`.
- [ ] Create `InterSystem/ConstructiveLatticeMonotonicity.lean`: `ckDerivable_implies_ctDerivable`, etc., via `Derivable_mono`; FC inclusions `cs4FC → ctFC`, `cs5FC → cs4FC`. Module docstring: note the CS4/CS5 completeness blocker does NOT obstruct these syntactic lemmas.
- [ ] Re-read `Cslib.lean`; append two `public import` lines.
- [ ] Run CI; commit green: `task 484 phase 3: constructive-base modal-cube monotonicity`.

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/ConstructiveLatticeSubsumption.lean` — new
- `Cslib/Logics/Modal/Metalogic/InterSystem/ConstructiveLatticeMonotonicity.lean` — new
- `Cslib.lean` — append two `public import` lines (re-read first)

**Verification**:
- `lake build` succeeds; no `sorry`/`axiom`; lemmas typecheck. No dependence on any `cs4/cs5` completeness result.

---

### Phase 4: Cross-base propositional-strength monotonicity into intuitionistic [COMPLETED]

**Goal**: Monotonicity into the intuitionistic base from the minimal and constructive bases: `MKModalAxiom → IKModalAxiom`, `CKModalAxiom → IKModalAxiom`, and per-rung `{MT,CT}→IT`, `{MS4,CS4}→IS4`, `{MS5,CS5}→IS5`. Document the MK/CK incomparability. (Report Phase 2.)

**Tasks**:
- [ ] Confirm constructor-set inclusions (IK = MK + `efq` + `dbot`; IK ⊇ CK; per-rung analogues) by reading the four base predicates.
- [ ] Create `InterSystem/PropositionalStrengthSubsumption.lean`: `MKModalAxiom_implies_IKModalAxiom`, `CKModalAxiom_implies_IKModalAxiom`, and per-rung subsumptions. Module docstring: MK and CK are **incomparable** (MK has `cd/idb` not `efq`; CK has `efq` not `cd/idb`); both embed into IK.
- [ ] Create `InterSystem/PropositionalStrengthMonotonicity.lean`: `Derivable`-level corollaries via `Derivable_mono`. Naming uses `_mono` / `_implies_`.
- [ ] Re-read `Cslib.lean`; append two `public import` lines.
- [ ] Run CI; commit green: `task 484 phase 4: cross-base propositional-strength monotonicity into IK`.

**Timing**: ~1.5 hours

**Depends on**: none (references only pre-existing axiom predicates; independent of Phases 1-3, so parallelizable in Wave 1)

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/PropositionalStrengthSubsumption.lean` — new
- `Cslib/Logics/Modal/Metalogic/InterSystem/PropositionalStrengthMonotonicity.lean` — new
- `Cslib.lean` — append two `public import` lines (re-read first)

**Verification**:
- `lake build` succeeds; no `sorry`/`axiom`; MK/CK incomparability documented; lemmas typecheck.

---

### Phase 5: Capstone modularity synthesis + Axis-C conservativity reuse [NOT STARTED]

**Goal**: The green, valuable capstone. A single `InterSystem/Modularity.lean` module that re-exports the Phase 1-4 monotonicity results, reuses the existing Axis-C `modal_conservative_extension`, and documents the three-axis framing precisely. This lands and commits green BEFORE the risky bridge, so a bridge block still leaves a complete monotone lattice + modularity synthesis. (Report Phase 4.)

**Tasks**:
- [ ] Read `Metalogic/ConservativeExtension.lean:54` (`modal_conservative_extension`) to confirm the reuse surface for Axis C.
- [ ] Create `Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean`. Docstring = the lattice map: three axes with their distinct Lean shapes — (A) modal-axiom lattice: **monotonicity** only (converse false, T proves `□φ→φ`); (B) propositional strength: **monotonicity** only into IK (converse false, classical proves Peirce; genuine converses exist only at PL level via Glivenko/bot-free, out of scope here); (C) modal-over-propositional: genuine **conservativity**, reused verbatim from `modal_conservative_extension`.
- [ ] Re-export / restate the Phase 1-4 monotonicity theorems as the consolidated lattice statement; reference the reused Axis-C conservativity. Do NOT re-prove anything.
- [ ] (Optional, gate as time permits) instantiate the existing `conservative_over_cpl` bridge (`ConservativityLift.lean:108`) at IPL/MPL completeness for modal-over-IPL / modal-over-MPL conservativity; if it does not close cleanly, omit — do NOT `sorry`.
- [ ] Re-read `Cslib.lean`; append `public import` line.
- [ ] Run CI; commit green: `task 484 phase 5: capstone modularity synthesis (monotonicity + Axis-C conservativity)`.

**Timing**: ~1 hour

**Depends on**: 1, 2, 3, 4

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean` — new, synthesis + doc + re-exports
- `Cslib.lean` — append one `public import` line (re-read first)

**Verification**:
- `lake build` succeeds; no `sorry`/`axiom`. Docstring states monotonicity-vs-conservativity distinction. Axis-C conservativity reused, not re-proved. This is the minimum viable capstone milestone.

---

### Phase 6: Generalized lift + IK→K "easy" Fischer-Servi derivations [NOT STARTED]

**Goal**: Begin the IK→K bridge (report Phase 3, part 1). Add the new generalized lift `Derivable_of_axiom_derivable` (axiom → *derivation*, which does not exist anywhere), then classically derive the box-form and the tractable diamond-form Fischer-Servi schemata. HARD / Zero-Debt-gated. Placed after the green capstone. (Report Phase 3, Step 3a + easy part of 3b.)

**Tasks**:
- [ ] Read `InterSystem/Lifting.lean` (the `liftDerivation` structural-recursion template) and `ProofSystem/Instances/K.lean` (existing `HasAxiomK`, `Necessitation`, `HasAxiomDiaDualityFwd/Back` instances + modal combinators).
- [ ] Re-read `InterSystem/Lifting.lean`; add `Derivable_of_axiom_derivable : (∀ φ, A₁ φ → Derivable A₂ φ) → Derivable A₁ φ → Derivable A₂ φ` by structural recursion on `DerivationTree`: discharge `ax` via the supplied derivation; recurse through `modus_ponens`/`necessitation`/`weakening`/`assumption` using closure of `Derivable A₂` under those rules. (~15 lines, low risk.)
- [ ] Create `Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean`. Prove `Derivable KAxiom` of the direct/tractable IK schemata: box-forms (`tBox/fourBox/bBox` are `modalT/modalFour/modalB` — direct); `kdia` (`□(φ→ψ)→(◇φ→◇ψ)`) under dual `◇=¬□¬`; `dbot` (`◇⊥→⊥`); and the propositional schemata (`efq`, and `peirce`=DNE which is a `KAxiom` constructor). Leave `cd` and `idb` for Phase 7 (stub the assembly, do not close it yet).
- [ ] **ZERO-DEBT STOP CLAUSE (mandatory)**: if any per-axiom classical derivation cannot be closed sorry-free after genuine effort, record the exact goal state reached and the specific missing combinator in the module docstring, mark that schema `[BLOCKED]`, and escalate. NEVER `sorry`, NEVER add an axiom, NEVER use a vacuous `def X := True` placeholder. A blocked schema does not block Phase 5's green capstone (already committed).
- [ ] Re-read `Cslib.lean`; append `public import` line for `IntToClassical` (and no new import needed for the in-place `Lifting.lean` addition).
- [ ] Run CI; commit green (only the closed derivations + the lift): `task 484 phase 6: generalized axiom→derivation lift + IK→K box/kdia/dbot derivations`.

**Timing**: ~2 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean` — add `Derivable_of_axiom_derivable` (re-read first; shared with classical infrastructure)
- `Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean` — new, tractable per-axiom classical derivations
- `Cslib.lean` — append one `public import` line (re-read first)

**Verification**:
- `lake build` succeeds; no `sorry`/`axiom`. `Derivable_of_axiom_derivable` typechecks and passes `lean_verify` (no unexpected axioms). Every derivation committed is sorry-free; any blocked schema is recorded per the STOP clause, not stubbed.

---

### Phase 7: IK→K completion (cd, idb) + classical rung bridges [NOT STARTED]

**Goal**: Complete the IK→K bridge (report Phase 3, part 2): the two fiddly Fischer-Servi schemata `cd` (`◇(φ∨ψ)→(◇φ∨◇ψ)`) and `idb` (`(◇φ→□ψ)→□(φ→ψ)`) as classical K derivations; assemble `∀ φ, IKModalAxiom φ → Derivable KAxiom φ`; conclude `Derivable IKModalAxiom φ → Derivable KAxiom φ` via the Phase 6 lift. Then the rung diamond schemata (`tDia`, `fourDia`, `bDia`) for classical T/S4/S5, yielding IT→T, IS4→S4, IS5→S5. HARD / Zero-Debt-gated; the heaviest phase — if it cannot complete in one dispatch, mark `[PARTIAL]` and resume. (Report Phase 3, remainder of 3b.)

**Tasks**:
- [ ] Re-read `InterSystem/IntToClassical.lean` (Phase 6 output) before editing.
- [ ] Derive `cd` classically in K (dual `◇`): the fiddliest; budget a full dispatch. Then `idb` classically in K.
- [ ] Assemble the total map `∀ φ, IKModalAxiom φ → Derivable KAxiom φ` from all per-axiom derivations (Phase 6 + Phase 7); conclude `ikDerivable_implies_kDerivable := Derivable_of_axiom_derivable …`. Naming reflects that this is the honest Int⟶Classical bridge (adding DNE/`peirce` collapses primitive-`◇` Fischer-Servi to dual-`◇` classical).
- [ ] Derive rung diamond schemata `tDia (A→◇A)`, `fourDia (◇◇A→◇A)`, `bDia (◇□A→A)` in classical T/S4/S5; assemble `itDerivable_implies_tDerivable`, `is4Derivable_implies_s4Derivable`, `is5Derivable_implies_s5Derivable`.
- [ ] **ZERO-DEBT STOP CLAUSE (mandatory)**: same as Phase 6 — any schema that resists sorry-free closure after genuine effort is recorded (exact goal state + missing combinator) and marked `[BLOCKED]`; NEVER `sorry`/axiom/vacuous placeholder. A blocked `cd`/`idb`/rung schema leaves the Phase 1-5 green capstone intact; commit whatever closed sorry-free.
- [ ] Run CI; commit green: `task 484 phase 7: IK→K bridge (cd, idb) + classical rung bridges IT→T/IS4→S4/IS5→S5`.

**Timing**: ~2 hours (may exceed one dispatch; use `[PARTIAL]` + resume)

**Depends on**: 6

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean` — extend with `cd`, `idb`, the assembled IK→K theorem, and the rung bridges (re-read first)
- `Cslib.lean` — no new import expected (module already registered in Phase 6); re-read and add only if a new file is split out

**Verification**:
- `lake build` succeeds; no `sorry`/`axiom`; `lean_verify` on `ikDerivable_implies_kDerivable` shows no unexpected axioms.
- `Derivable IKModalAxiom φ → Derivable KAxiom φ` typechecks (or the specific unclosable schema is `[BLOCKED]`-recorded, with the rest committed green).

---

## Testing & Validation

Run the CSLib CI pipeline after each phase (per-phase green gate):
- [ ] `lake build` (targeted module build, then full build before commit)
- [ ] `lake test` — CslibTests suite
- [ ] `lake exe checkInitImports` — verify Cslib.Init imports
- [ ] `lake exe lint-style` — style linting
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — dependency analysis (subsumption/monotonicity split keeps this clean)
- [ ] Zero-debt audit: `grep` the new files for `sorry`, `admit`, `axiom`, and vacuous `:= True` placeholders — must be empty (except documented `[BLOCKED]` records that contain NO proof stub).
- [ ] Naming audit: Axes A/B lemmas end in `_mono` / `_implies_`; "conservative" appears only where reusing Axis-C results.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/InterSystem/MinimalLatticeSubsumption.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/MinimalLatticeMonotonicity.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/IntuitionisticLatticeSubsumption.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/IntuitionisticLatticeMonotonicity.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/ConstructiveLatticeSubsumption.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/ConstructiveLatticeMonotonicity.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/PropositionalStrengthSubsumption.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/PropositionalStrengthMonotonicity.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/Modularity.lean`
- `Cslib/Logics/Modal/Metalogic/InterSystem/IntToClassical.lean`
- Extended: `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean` (`Derivable_of_axiom_derivable`)
- Extended: `Cslib.lean` (import registration for all new modules)
- `specs/484_metalogic_conservative_extension_modularity/summaries/01_conservative-extension-modularity-summary.md` (at completion)

## Rollback/Contingency

- Each phase is an isolated, per-phase green commit; revert a single phase's commit to roll it back without affecting others.
- Phases 1-5 are Zero-Debt-safe and independent of the bridge; if Phases 6-7 stall, ship Phases 1-5 as the complete, green capstone (monotone lattice + modularity synthesis + reused Axis-C conservativity).
- If a bridge schema is `[BLOCKED]`, the task transitions to `[BLOCKED]` with the recorded goal state and escalation note; the green Phase 1-5 commits remain the delivered capstone. Do NOT introduce `sorry`/axiom to force a green build.
- If `Cslib.lean` import edits conflict with a concurrent session, re-read and re-apply the append; import ordering is not load-bearing.
