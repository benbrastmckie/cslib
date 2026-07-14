# Implementation Plan: Task #495 — Minimal Modal Logic MK Soundness + Completeness

- **Task**: 495 - Minimal modal logic MK soundness + completeness
- **Status**: [NOT STARTED]
- **Effort**: 9 hours
- **Dependencies**: Tasks 491, 480, 490 (all delivered on `main`); reuses Constructive/Segment.lean + SegmentLindenbaum.lean, Semantics/Birelational.lean, Intuitionistic/{IK,TruthLemma}.lean, Propositional/Metalogic/{MinLindenbaum,MinStrongCompleteness}.lean
- **Research Inputs**: specs/495_minimal_modal_K_soundness_completeness/reports/01_minimal-modal-k-soundness-completeness.md
- **Artifacts**: plans/01_minimal-modal-k-soundness-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

MK is the modal logic over the **minimal** propositional base (no efq / explosion): IK minus `efq` minus `dbot`/Nd, over the task-490 birelational semantics with the minimal ⊥ treatment (⊥ an ordinary proposition). This plan proves MK **sound and complete** with respect to `MValid` (birelational, ∃-diamond, F1/F2 confluence) via a **quasi-prime** canonical model. All work lands in a NEW subtree `Cslib/Logics/Modal/Metalogic/Minimal/` (five files), touching no delivered IK/CK/Intuitionistic/Constructive files, so concurrent sessions editing this repo are not disturbed. Definition of done: `mk_soundness_completeness : MValid φ ↔ Derivable MKModalAxiom φ` builds sorry-free with full CI green, and the five new files are wired into `Cslib.lean`.

### Research Integration

The plan is the direct realization of report `01`'s five-phase decomposition and honors its three load-bearing findings:

- **MK is NOT "IK completeness minus the `h_efq` lambda."** `h_efq` is consumed in three roles (report Crux §): **Role A** world consistency — DELETED (worlds become quasi-prime, `Cons := fun _ => True`); **Role B** the ⊥-base cases of IK's box/diamond distribution lemmas (`boxOr_of_boxDisj [] = (⊥→□⊥)` needs efq; `diaOr_of_diaDisj [] = (◇⊥→⊥)` needs Nd/`h_dbot`) — **the real obstruction**, resolved by EMBRACING fallible worlds and reusing the efq-free `box_refuting_theory`/`dia_refuting_theory`, NOT IK's `bigOr` machinery; **Role C** the inconsistent-case split in `*_completeness` — REMOVED (MK completeness is single-branch like propositional `min_strong_completeness`).
- **Major reuse, no new abstractions.** The efq-free minimal machinery already exists on `main` at `Cons = fun _ => True`: `QuasiPrime` + `quasi_prime_exclusion` + `imp_refuting_theory` + `box_refuting_theory` + `dia_refuting_theory` + `box_mem_of_boxed_context` + `quasi_head_realization` (`Constructive/Segment.lean`, `Constructive/SegmentLindenbaum.lean`), all `Axioms`-parametric; plus `MinLindenbaum.lean` / `MinStrongCompleteness.lean` as the propositional template. The plan reuses these directly and introduces no duplicating abstraction.
- **Semantics target = `MValid`, not CKValid.** MK keeps Cd+Idb and drops efq+dbot, so its semantics is the birelational `MValid` (∃-diamond, F1/F2), with `botForces := ⊥ ∈ w.val` and the `.bot` truth case `Iff.rfl`. Do NOT route MK through CK's segment forcing / `CKValid`.

### Prior Plan Reference

No prior plan. This is the first plan version for task 495.

### Roadmap Alignment

No `roadmap_path` supplied and `roadmap_flag` not set; no ROADMAP.md consultation performed. MK is the `MValid` sibling of the delivered IK (task 480/490) and CK (task 493) developments, completing the minimal-modal corner of the modal metalogic family.

## Goals & Non-Goals

**Goals**:
- Define `MKModalAxiom` = the 8 minimal-propositional schemata (`MinPropAxiom` shape) + the 4 modal schemata `k`, `kdia`, `cd`, `idb` (NO `efq`, NO `dbot`/Nd).
- Prove `mk_axiom_sound`, `mk_soundness`, `mk_soundness_derivable` against **`MValid`** (arbitrary `botForces`), plus `mk_consistent`.
- Build the quasi-prime birelational canonical model (`canonicalR` with both box-preservation and diamond-image clauses, F1/F2), reusing the delivered efq-free segment lemmas.
- Prove `min_canonical_truth_lemma` and `mk_completeness`, culminating in `mk_soundness_completeness : MValid φ ↔ Derivable MKModalAxiom φ`.
- Wire all five new files into `Cslib.lean`; keep full CI (`lake build`, `lake test`, `checkInitImports`, `lint-style`, `shake`) green.

**Non-Goals**:
- No edits to any delivered file (IK/CK/Intuitionistic/Constructive/Propositional). New `Minimal/` subtree only.
- No new abstractions duplicating `QuasiPrime`/segment machinery.
- No new `import Mathlib.*` beyond what `PrimeTheory.lean`/`Birelational.lean` already pull.
- No strong-completeness generalization beyond `Γ = ∅` weak completeness (the `min_strong_completeness` template makes strong completeness free later if wanted, but it is out of scope here).
- No `sorry`, `axiom`, or vacuous-placeholder (`def := True`) closure of any goal, anywhere — see Phase 3 STOP clause.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **Phase 3 ∃-diamond diamond-witness over quasi-prime worlds has no line-for-line in-repo precedent** (CK uses segments; propositional Min has no modality) | H | M | Land P1+P2 (near-deterministic) and commit first; in P3 build the witness from the delivered efq-free `dia_refuting_theory`, discharging IK's `diaOr_of_diaDisj`+`h_dbot` obligations via fallible/`Set.univ` worlds. **Zero-Debt STOP clause** (below) if unclosable. |
| Concurrent sessions editing shared files cause merge conflicts | M | M | Confine ALL writes to `Cslib/Logics/Modal/Metalogic/Minimal/` new files; only `Cslib.lean` is shared, and it is edited (via `lake exe mk_all --module`) once, last, in Phase 5. Per-phase green commits reduce blast radius. |
| Accidentally reaching for IK's `boxOr_of_boxDisj`/`diaOr_of_diaDisj` (efq/`h_dbot` base cases) | H | M | Report REFUTES their reuse (empty-list bases `⊥→□⊥`, `◇⊥→⊥` are not MK theorems). Plan mandates `box_refuting_theory`/`dia_refuting_theory` instead. |
| `⊤`-via-efq base cases mistaken for obstructions | L | L | Report: these prove `⊤ = ⊥→⊥`, derivable in minimal from implyK+implyS (identity combinator `d_id`, `PrimeTheory.lean:205-213`). Substitute the minimal `⊤`-proof. |
| Deprecated `Reflexive`/`Transitive`/`Symmetric` creep in | L | L | Use the frame-condition forms already in `Birelational.lean` (F1/F2); avoid the deprecated relation typeclasses. |
| Soundness case accidentally inspects `botForces` | L | L | Report verified `k/kdia/cd/idb` + 8 prop cases never inspect `botForces`; only dropped `efq`/`dbot` did. Transcribe verbatim with the `MValid` prologue. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential (one phase per wave): each phase's Lean declarations are consumed by the next. Land and commit each phase green before starting the next.

---

### Phase 1: `MK.lean` — axiom datatype + soundness [COMPLETED]

**Goal**: Define `MKModalAxiom` and prove MK soundness against `MValid` (arbitrary `botForces`), plus consistency. Low-risk, near-deterministic; lands first and is committed green.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Minimal/MK.lean` opening `import Cslib.Init`, `namespace Cslib.Logic.Modal`, `open Cslib.Logic`.
- [ ] Define `inductive MKModalAxiom : Proposition Atom → Prop` with the 8 minimal-propositional constructors (`implyK`, `implyS`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, mirroring `MinPropAxiom` = `IntPropAxiom` without `efq`) plus the 4 modal constructors `k`, `kdia`, `cd`, `idb` — NO `efq`, NO `dbot`/Nd (report §Phase 1 datatype).
- [ ] Prove `mk_axiom_sound {φ} (h : MKModalAxiom φ) : MValid.{u,v} φ` by mirroring `ik_axiom_sound` (`IK.lean:131`) but returning `MValid`: replace the `IValid` prologue with the `MValid` prologue `intro World _ r f1 f2 val botForces v_uc bf_uc w`; keep only the 8 prop + `k`/`kdia`/`cd`/`idb` cases (transcribe verbatim — verified `botForces`-agnostic); drop the `efq`/`dbot` cases. `idb` still consumes `f2`.
- [ ] Prove `mk_soundness {Γ φ} (d : DerivationTree MKModalAxiom Γ φ) … : BForces r val botForces w φ` mirroring `ik_soundness` (necessitation case identical).
- [ ] Prove `mk_soundness_derivable {φ} (h : Derivable MKModalAxiom φ) : MValid.{u,v} φ`.
- [ ] Prove `mk_consistent : ¬ Derivable MKModalAxiom (Proposition.bot : Proposition Atom)` as a corollary of soundness at a NON-fallible one-point frame (`botForces := fun _ => False`), mirroring `ik_consistent` (`IK.lean:248`) or lifting `MinPropAxiom` soundness à la `min_consistent`.
- [ ] `lake build` the new file to green.

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MK.lean` (NEW) — MK axiom datatype + soundness + consistency (~150-200 lines).

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Minimal.MK` succeeds, zero `sorry`/`axiom`.
- Spot-check: `mk_axiom_sound` returns `MValid` (not `IValid`); `MKModalAxiom` has exactly 12 constructors (no `efq`, no `dbot`).
- Commit: `task 495 phase 1: MK axiom datatype + MValid soundness + consistency`.

---

### Phase 2: `MinPrimeTheory.lean` — quasi-prime canonical worlds [NOT STARTED]

**Goal**: Assemble the canonical-world scaffolding by REUSING the delivered efq-free quasi-prime machinery; add only thin wrappers. No new abstractions.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Minimal/MinPrimeTheory.lean`. Reference (do NOT re-derive) `QuasiPrime MKModalAxiom`, `quasi_prime_exclusion`, `imp_refuting_theory`, `box_refuting_theory`, `dia_refuting_theory`, `box_mem_of_boxed_context`, `quasi_head_realization` from `Constructive/{Segment,SegmentLindenbaum}.lean` (all `Axioms`-parametric at `Cons = fun _ => True`).
- [ ] Define `MinCanonicalPrimeWorld := {S // QuasiPrime MKModalAxiom S}` with `Preorder` instance = set inclusion (`⊆`), copying shape from `MinStrongCompleteness.lean:74-108`.
- [ ] Define `canonicalVal p := atom p ∈ w.val` and `minBotForces w := ⊥ ∈ w.val`; prove `minBotForces_upward_closed` (free via `≤ = ⊆`).
- [ ] Define `min_head_realization : ¬ Derivable MKModalAxiom φ → ∃ T, QuasiPrime MKModalAxiom T ∧ φ ∉ T` as a thin wrapper over `quasi_head_realization` (`SegmentLindenbaum.lean:242`).
- [ ] `lake build` to green.

**Timing**: ~1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MinPrimeTheory.lean` (NEW) — quasi-prime world type, preorder, valuation, `minBotForces`, `min_head_realization` (~120-180 lines, mostly wrappers).

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Minimal.MinPrimeTheory` succeeds, zero `sorry`/`axiom`.
- Confirm NO redefinition of `QuasiPrime`/`quasi_prime_exclusion`/segment lemmas — they are imported and used, not re-stated.
- Commit: `task 495 phase 2: quasi-prime canonical worlds (reuse segment machinery)`.

---

### Phase 3: `MinCanonicalModel.lean` — canonical R + witnesses (CRUX, highest risk) [NOT STARTED]

**Goal**: Build the birelational ∃-diamond canonical accessibility relation over quasi-prime worlds and the box/diamond witnesses + F1/F2 confluence, using ONLY the efq-free segment lemmas. This is the single highest-risk phase.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Minimal/MinCanonicalModel.lean`.
- [ ] Define `canonicalR w v := (∀ φ, □φ ∈ w.val → φ ∈ v.val) ∧ (∀ φ, φ ∈ v.val → ◇φ ∈ w.val)` (BOTH clauses; the diamond-image clause is required for the ∃-diamond semantics).
- [ ] Prove `min_canonical_box_witness : □φ ∉ w.val → ∃ v, canonicalR w v ∧ φ ∉ v.val` — build from `box_refuting_theory` (`SegmentLindenbaum.lean:168`), efq-free. Do NOT use `boxOr_of_boxDisj`.
- [ ] Prove `min_canonical_diamond_witness : ◇φ ∈ w.val → ∃ v, canonicalR w v ∧ φ ∈ v.val` — build from `dia_refuting_theory` (`SegmentLindenbaum.lean:194`). Discharge diamond-image-clause obligations (that IK closed via `diaOr_of_diaDisj` + `h_dbot`) by fallible worlds: a would-be `◇⊥→⊥` obstruction is moot because `◇⊥ ∈ w` is permitted; the worst-case witness is `Set.univ` (`quasiPrime_univ`, `Segment.lean:80`). Do NOT use `diaOr_of_diaDisj`.
- [ ] Prove `min_canonical_f1` (F1 confluence via the diamond witness) and `min_canonical_f2` (F2 confluence via the box witness), standard over quasi-prime worlds, efq-free. Avoid deprecated `Reflexive`/`Transitive`/`Symmetric`.
- [ ] Replace any latent `⊤`-via-efq base case with the minimal `⊤ = ⊥→⊥` identity-combinator proof (`d_id`, `PrimeTheory.lean:205-213`) if it arises.
- [ ] `lake build` to green.

**Zero-Debt STOP / [BLOCKED]-escalation clause (MANDATORY for this phase)**:
First attempt the `dia_refuting_theory`-based diamond witness (and the `box_refuting_theory`-based box witness). If a diamond-image-clause or F1/F2 obligation **cannot be closed sorry-free after genuine effort**, do **NOT** insert `sorry`, `axiom`, or a vacuous placeholder (`def := True`, trivial `True`-valued stub, or an unused hypothesis discharge). Instead:
1. STOP work on Phase 3.
2. Record the EXACT unclosable goal state (the `lean_goal` output at the stuck position) and the lemma/clause it belongs to.
3. Mark the phase `[BLOCKED]` in this plan and set task status accordingly; write the blocker into the return metadata (`status: "blocked"`) with the goal state.
4. Escalate to user review. Candidate escalation questions to include: (a) whether MK's canonical `R` should adopt CK's segment head/tail structure while retaining the ∃-diamond `BForces`; (b) whether MK completeness is more naturally stated with the fallible-world `Set.univ` witness inlined. Do NOT self-authorize a design pivot or any debt.

**Timing**: ~2.5 hours (crux; may consume a full agent run on the diamond witness alone)

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MinCanonicalModel.lean` (NEW) — `canonicalR`, box/diamond witnesses, F1/F2 (~150-350 lines).

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Minimal.MinCanonicalModel` succeeds, zero `sorry`/`axiom`, OR phase is `[BLOCKED]` with recorded goal state (never a silent placeholder).
- Confirm witnesses cite `box_refuting_theory`/`dia_refuting_theory`, NOT `boxOr_of_boxDisj`/`diaOr_of_diaDisj`.
- Commit (only if green): `task 495 phase 3: quasi-prime canonical R + box/diamond witnesses + F1/F2`.

---

### Phase 4: `MinTruthLemma.lean` — canonical truth lemma [NOT STARTED]

**Goal**: Prove the canonical truth lemma over quasi-prime worlds by induction on the proposition.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Minimal/MinTruthLemma.lean`.
- [ ] Prove `min_canonical_truth_lemma : BForces canonicalR canonicalVal minBotForces w φ ↔ φ ∈ w.val` by induction:
  - `atom` = `Iff.rfl`; **`bot` = `Iff.rfl`** (from `minBotForces` def — no `canonical_bot_not_mem`, no consistency, no efq; report §Minimal ⊥ #3).
  - `and`/`or` = copy the `botForces`-parametric cases from `Intuitionistic/TruthLemma.lean` (use only closure + disjunction property, both in `QuasiPrime`).
  - `imp` = via `imp_refuting_theory` (efq-free) + `quasi_prime_exclusion`.
  - `box`/`diamond` = via the Phase-3 witnesses (`min_canonical_box_witness`/`min_canonical_diamond_witness`).
- [ ] `lake build` to green.

**Timing**: ~2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MinTruthLemma.lean` (NEW) — `min_canonical_truth_lemma` (~150-300 lines).

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Minimal.MinTruthLemma` succeeds, zero `sorry`/`axiom`.
- Confirm `bot` case is literally `Iff.rfl`.
- Commit: `task 495 phase 4: quasi-prime canonical truth lemma`.

---

### Phase 5: `MinCompleteness.lean` + barrel wiring [NOT STARTED]

**Goal**: Prove single-branch MK completeness, package `mk_soundness_completeness`, and wire all five files into `Cslib.lean`. Full CI green.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Minimal/MinCompleteness.lean`.
- [ ] Prove `mk_completeness {φ} (h : MValid.{u,u} φ) : Derivable MKModalAxiom φ` by `by_contra` — **single branch, NO consistency case split** (Role C removed): extend `cl ∅` by `quasi_prime_exclusion`, apply `MValid` at the canonical model (`botForces := ⊥ ∈ ·`), invoke the truth lemma, contradict exclusion. Mirror `min_strong_completeness` (`MinStrongCompleteness.lean`) at `Γ = ∅`.
- [ ] Prove `mk_soundness_completeness {φ} : MValid.{u,u} φ ↔ Derivable MKModalAxiom φ := ⟨mk_completeness, mk_soundness_derivable⟩`.
- [ ] Run `lake exe mk_all --module` to add all five `Minimal/` files to `Cslib.lean` (the ONLY shared-file edit in this plan; do it here, last).
- [ ] Run the full CI pipeline and resolve any lint/shake findings within the `Minimal/` subtree only.

**Timing**: ~1.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MinCompleteness.lean` (NEW) — `mk_completeness`, `mk_soundness_completeness` (~100-200 lines).
- `Cslib.lean` (SHARED, single edit via `mk_all --module`) — register the five new `Minimal/` modules.

**Verification**:
- `lake build` (whole project) succeeds, zero `sorry`/`axiom` in `Minimal/`.
- `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix` all green.
- `mk_soundness_completeness` type-checks as `MValid φ ↔ Derivable MKModalAxiom φ`.
- Commit: `task 495 phase 5: MK completeness + soundness↔completeness; wire barrel; CI green`.

---

## Testing & Validation

- [ ] `lake build` (whole project) succeeds after Phase 5 with zero `sorry`/`axiom` in the `Minimal/` subtree.
- [ ] `lake test` (CslibTests) green.
- [ ] `lake exe checkInitImports` green (every `Minimal/` file begins `import Cslib.Init`).
- [ ] `lake exe lint-style` green for the five new files.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused imports in the `Minimal/` subtree.
- [ ] `mk_axiom_sound` returns `MValid`; `MKModalAxiom` contains no `efq`/`dbot` constructor.
- [ ] `min_canonical_truth_lemma` `bot` case is `Iff.rfl`.
- [ ] Phase-3 witnesses reference `box_refuting_theory`/`dia_refuting_theory`, not IK's `boxOr_of_boxDisj`/`diaOr_of_diaDisj`.
- [ ] No delivered file (IK/CK/Intuitionistic/Constructive/Propositional) was modified; only `Cslib.lean` shared edit.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Minimal/MK.lean` (Phase 1)
- `Cslib/Logics/Modal/Metalogic/Minimal/MinPrimeTheory.lean` (Phase 2)
- `Cslib/Logics/Modal/Metalogic/Minimal/MinCanonicalModel.lean` (Phase 3)
- `Cslib/Logics/Modal/Metalogic/Minimal/MinTruthLemma.lean` (Phase 4)
- `Cslib/Logics/Modal/Metalogic/Minimal/MinCompleteness.lean` (Phase 5)
- `Cslib.lean` (barrel registration, Phase 5)
- `specs/495_minimal_modal_K_soundness_completeness/summaries/01_minimal-modal-k-soundness-completeness-summary.md` (implementation summary)

## Rollback/Contingency

- **Per-phase green commits** confine risk: each phase is committed only when its `lake build` is green, so any failing phase leaves the prior green state intact. Revert the last commit to roll back one phase.
- All work is additive in a NEW subtree; rollback = delete the `Minimal/` files and revert the single `Cslib.lean` barrel edit. No delivered file is touched, so rollback cannot regress IK/CK/Intuitionistic/Constructive.
- **Phase 3 contingency**: if the diamond witness is unclosable, the Zero-Debt STOP clause marks Phase 3 `[BLOCKED]` and escalates — no `sorry`/`axiom`/placeholder is ever committed. Phases 1-2 remain landed and green.
- **Concurrent-session contingency**: if the Phase-5 `Cslib.lean` edit conflicts with a concurrent edit, re-run `lake exe mk_all --module` to regenerate the barrel from the filesystem rather than hand-merging.
