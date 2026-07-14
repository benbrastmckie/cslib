# Implementation Plan: Task #496 — Minimal Modal Extensions MT / MS4 / MS5

- **Task**: 496 - Minimal modal extensions MT / MS4 / MS5 (minimal-base analogues of T/S4/S5 as modular extensions of MK)
- **Status**: [NOT STARTED]
- **Effort**: 9 hours
- **Dependencies**: Task 495 (MK, COMPLETED) delivered and on `main`
- **Research Inputs**: specs/496_minimal_modal_extensions/reports/01_minimal-modal-extensions.md
- **Artifacts**: plans/01_minimal-modal-extensions.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add the minimal-base analogues of the modal systems T, S4, and S5 (named MT / MS4 / MS5) as
modular extensions of the completed minimal modal logic MK (task 495), over the birelational
`MValid` semantics. Each system extends MK's axiom base with an axiom↔frame-condition
correspondence (reflexivity / transitivity / symmetry), proves soundness by adding cases to the
inherited `mk_axiom_sound`, and proves completeness by supplying a *positive* frame-condition
closure lemma about the shared canonical relation `minCanonicalR` to a generalized completeness
scaffold. The work is a straightforward modular extension mirroring the delivered IK-extension
pattern (task 494: IT/IS4/IS5) — it does **not** inherit the CS4/CS5 segment-model blocker of
task 501. Definition of done: four new files under `Cslib/Logics/Modal/Metalogic/Minimal/`
(`MinExtension.lean`, `MT.lean`, `MS4.lean`, `MS5.lean`), each system with axioms + soundness +
completeness + a soundness↔completeness biconditional, all sorry-free and zero-debt, wired into
`Cslib.lean` and passing the full CSLib CI pipeline.

### Research Integration

Report `01_minimal-modal-extensions.md` (confidence HIGH, grounded in direct reads of all
delivered MK/IK/CK files) establishes the load-bearing findings this plan respects:

1. **Tractable, zero-debt, NOT blocked.** MK reuses IK's single-world, two-clause `minCanonicalR`
   over quasi-prime worlds **with F1/F2 confluence** (`MValid`). No segments/tails, no
   `diamRefutingSegment`. The CS4/CS5 obstruction lives entirely in CK's segment model, which MK
   does not use.
2. **Plain frame conditions on raw `r`.** Because `MValid` carries F1/F2, the correspondences use
   PLAIN conditions on the raw relation `r` (reflexive / transitive / symmetric), **NOT** the
   ≤-composed form CK required. The ≤-composition is absorbed by F1/F2 in the box-form soundness
   cases (as MK's `idb` already uses `f2`). Define LOCAL `mtFC`/`ms4FC`/`ms5FC` predicates —
   never the deprecated Mathlib `Reflexive`/`Transitive`/`Symmetric`.
3. **Positive closures transfer prime→quasi-prime** via `QuasiPrime.closed` (deductive closure).
   No consistency, no `efq`, no world-subtype invariant. `mk_completeness` is single-branch, so
   the FC-completeness scaffold is *simpler* than IK's `ivalidFC_completeness`.
4. **MS5 via B (symmetry), NOT euclidean-5.** Quasi-prime theories are strictly further from
   negation-complete than prime theories; the euclidean route has no positive analogue.
5. **Reuse task 495's MK machinery** (MK, MinPrimeTheory, MinCanonicalModel, MinTruthLemma,
   MinCompleteness) and mirror task 494's IK-extension pattern (Extension/IT/IS4/IS5). The
   highest-risk item is `min_canonical_symmetric` (Phase 4) — a verbatim analogue of the
   already-compiled `is5_canonical_symmetric` (IS5.lean:341).

### Prior Plan Reference

No prior plan. This is the first plan for task 496.

### Roadmap Alignment

No ROADMAP.md consulted for this task (not provided in delegation context). Task is
lower-priority / exploratory per the research report header.

## Goals & Non-Goals

**Goals**:
- Deliver `MinExtension.lean`: `MValidFC` (FC-parameterized `MValid`, retaining `botForces`),
  `mkvalidFC_completeness` (single-branch generalization of `mk_completeness`), and the
  `min_axiom_mem` / `min_imp_property` deductive-closure helpers.
- Deliver `MT.lean`, `MS4.lean`, `MS5.lean`: each with its axiom inductive (box-form + diamond-form
  schemata), a LOCAL frame-condition predicate on raw `r`, soundness (inherited cases + new cases),
  a positive canonical FC-closure lemma, completeness via `mkvalidFC_completeness`, a consistency
  witness, and a soundness↔completeness biconditional.
- Wire all four files into `Cslib.lean` and pass the full CSLib CI pipeline (build, checkInitImports,
  lint, lint-style, shake, test) with zero warnings.
- Zero technical debt: no `sorry`, no `axiom` (beyond `DerivationTree`-carried schemata), no vacuous
  `def` placeholder anywhere.

**Non-Goals**:
- No edits to delivered MK / IK / CK files (only NEW files under `Minimal/` plus the shared
  `Cslib.lean` barrel).
- No euclidean-5 axiomatization of MS5 (B/symmetry only).
- No ≤-composed frame conditions (plain conditions on raw `r`).
- No new Mathlib API and no new notation.
- No decidability, finite-model, or filtration results (out of scope).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `min_canonical_symmetric` (MS5) needs a bespoke `bDia`-membership helper | H | M | First attempt verbatim port of `is5_canonical_symmetric` (IS5.lean:341); Zero-Debt STOP clause on Phase 4 — mark [BLOCKED], record exact open goal, escalate; never `sorry`/axiom/vacuous-def |
| `is4_canonical_transitive` port (MS4) does not close sorry-free | M | L-M | Verbatim port; the IK analogue compiles; Zero-Debt STOP clause on Phase 3 |
| Concurrent sessions edit `Cslib.lean` or the `Minimal/` subtree | M | M | Confine all edits to `Minimal/`; re-read `Cslib.lean` immediately before editing; per-phase green commits; use `lake exe mk_all --module` rather than hand-editing the barrel |
| `lake shake` flags the `MK ← MT ← MS4 ← MS5` import chain when axiom constructors are copied verbatim | L | M | Let `shake` decide; if flagged, import `MinExtension` (+ `MinCompleteness`) directly as CK's CS4/CS5 did; do not pre-optimize |
| Name collision with IK's `canonicalR`/`canonicalVal` in the same namespace | L | L | Prefix all shared-shape names with `min`/`mt`/`ms4`/`ms5` from the start (task 495 hit this) |
| Accidental use of deprecated Mathlib `Reflexive`/`Transitive`/`Symmetric` breaks zero-warnings gate | M | L | Define LOCAL `mtFC`/`ms4FC`/`ms5FC` predicates; verified deprecated in pinned Mathlib (IT.lean:25,127) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 1, 2, 3, 4 |

Phases are sequential: MT extends the MinExtension scaffold, MS4 extends MT's axiom base, MS5
extends MS4's, and barrel wiring depends on all files existing. (Phases 2–4 could in principle be
parallelized on independent axiom bases, but the axiom-inheritance chain and the single shared
`Cslib.lean` touch make strict sequencing the safe default under concurrent-session pressure.)

### Phase 1: MinExtension.lean scaffold [COMPLETED]

**Deviation note**: The plan's Phase 1 text described a small (~120-160 line) scaffold reusing
task 495's MK canonical-model machinery directly. During implementation this proved infeasible:
`MinCanonicalPrimeWorld`/`minCanonicalR`/`min_canonical_f1`/`min_canonical_f2`/
`min_canonical_truth_lemma`/`min_head_realization` in `MinCanonicalModel.lean`/`MinTruthLemma.lean`/
`MinCompleteness.lean` are hard-coded to `MKModalAxiom` (never touched `Axioms` as a free
parameter, unlike IK's *own* base canonical-model files `Intuitionistic/{CanonicalModel,
PrimeTheory,TruthLemma}.lean`, which task 480/492 built generically over `Axioms` from the start
-- that is precisely why IK's `Extension.lean` could stay a ~150-line wrapper for task 494).
`mkvalidFC_completeness` must produce `Derivable Axioms φ` for `Axioms := MTModalAxiom` /
`MS4ModalAxiom` / `MS5ModalAxiom` in Phases 2-4, which is impossible while reusing MK's
`MKModalAxiom`-fixed worlds verbatim. The actual, necessary Phase 1 scope was therefore to
*genericize* task 495's ~1090-line efq-free "nonempty Lindenbaum-pair" canonical-model
construction over an abstract `Axioms : Proposition Atom → Prop` (threading the 12 MK-core
axiom-schema witnesses `h_implyK, h_implyS, h_andI, h_andE1, h_andE2, h_orI1, h_orI2, h_orE, h_k,
h_kdia, h_cd, h_idb` explicitly through every canonical-model theorem, exactly mirroring IK's own
`canonical_f1`/`canonical_box_witness` convention in `Intuitionistic/CanonicalModel.lean:636,1140`)
-- not merely adding an `FC` parameter to an already-generic scaffold. This is a like-for-like
repeat, at MK's scale, of the genericization work IK's base task already performed; it was not
optional, since Phases 2-4 depend on it for their `mkvalidFC_completeness` calls to type-check at
`Axioms := MTModalAxiom` etc. All declarations were placed under a nested `Cslib.Logic.Modal.MinExt`
namespace to avoid name collision with task 495's `MKModalAxiom`-specific declarations of the same
short name in the same outer namespace; `MValidFC`, `mkvalidFC_completeness`, `min_axiom_mem`,
`min_imp_property` are exposed unqualified in `Cslib.Logic.Modal` per the plan. Result:
`MinExtension.lean` is ~1580 lines (not ~150), zero sorry, zero new axioms (only
`propext`/`Classical.choice`/`Quot.sound`, matching MK's own `mk_completeness` footprint via the
same `noncomputable`/Zorn's-lemma technique). `lean_verify` confirms the axiom footprint on
`mkvalidFC_completeness`; `lake build`/`checkInitImports` are green.

**Goal**: Create the FC-parameterized completeness scaffold — the birelational analogue of IK's
`Extension.lean`, keeping arbitrary `botForces`.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Minimal/MinExtension.lean` beginning `import Cslib.Init`
      (plus the MK-chain imports: `MinCompleteness`, transitively `MinCanonicalModel`,
      `MinTruthLemma`, `Constructive/Segment`). Namespace `Cslib.Logic.Modal`.
- [ ] Define `MValidFC (FC) φ`: a copy of `MValid` with one extra binder `_fc : FC r` threaded
      alongside `f1`/`f2`, **retaining** the `botForces`/`bf_uc` binders (unlike `IValidFC`, which
      hardcodes `fun _ => False`). Prove/state `MValid = MValidFC (fun _ => True)` (or an `Iff`),
      with docstring.
- [ ] Define `min_axiom_mem (h : MKModalAxiom φ) : φ ∈ w.val` via `QuasiPrime.closed`
      (`w.property.1.2 [] φ (fun _ h => nomatch h) ⟨.ax [] _ h⟩`), mirroring IK `axiom_mem`.
- [ ] Define `min_imp_property {w} : (φ.imp ψ) ∈ w.val → φ ∈ w.val → ψ ∈ w.val` via
      `QuasiPrime.closed` on `[φ.imp ψ, φ] ⊢ ψ`, mirroring `canonical_imp_property`
      (TruthLemma.lean:99).
- [ ] Define `mkvalidFC_completeness (FC) (h_canonFC : FC minCanonicalR) (h_valid : MValidFC FC φ) : Derivable MKModalAxiom φ`:
      copy `mk_completeness` (MinCompleteness.lean:55) — **single branch, no `efq`, no consistency
      case split** — threading `h_canonFC` into the `h_valid` application.
- [ ] Docstring on every declaration (docBlame); `@[expose] public section`.
- [ ] `lake build` the file green; run `lake exe mk_all --module` to register it; re-read
      `Cslib.lean` immediately before/after and confirm the module entry landed.
- [ ] Green commit: `task 496 phase 1: MinExtension.lean scaffold (MValidFC, mkvalidFC_completeness)`.

**Timing**: ~1.5 hours (~120–160 lines; near-deterministic, LOW risk).

**Depends on**: none

**Files to create/modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MinExtension.lean` - new scaffold file.
- `Cslib.lean` - barrel entry via `lake exe mk_all --module` (re-read immediately before editing).

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Minimal.MinExtension` succeeds, zero warnings.
- `MValidFC`, `mkvalidFC_completeness`, `min_axiom_mem`, `min_imp_property` present and sorry-free
  (`lean_verify` / grep for `sorry`).
- `MValid`↔`MValidFC (fun _ => True)` relationship stated and proved.

---

### Phase 2: MT.lean (reflexivity) [NOT STARTED]

**Goal**: Deliver MT — MK + reflexivity (T axiom), the lowest-risk per-system file.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Minimal/MT.lean` (`import Cslib.Init` + `MinExtension`).
- [ ] `MTModalAxiom`: MK constructors + `tBox : □A → A` and `tDia : A → ◇A` (both required — ◇ is
      primitive, Wijesekera1990).
- [ ] `def mtFC {World} (r) : Prop := ∀ w, r w w` (LOCAL predicate; NOT Mathlib `Reflexive`).
- [ ] `mt_axiom_sound` over `MValidFC mtFC`: inherited MK cases + `tBox` (plain reflexivity +
      `bforces_persistence`) + `tDia` (plain reflexivity). FC threaded unused into inherited cases.
- [ ] `mt_soundness` / `mt_soundness_derivable` (structural wrapper reusing MK's shape).
- [ ] `min_canonical_reflexive_mt : mtFC minCanonicalR` — POSITIVE closure via `min_axiom_mem` +
      `min_imp_property` over `minCanonicalR`'s two clauses (no `by_contra`, no negation).
- [ ] `mt_completeness := mkvalidFC_completeness mtFC … min_canonical_reflexive_mt`.
- [ ] `mt_consistent` (one-point `ℕ`-frame, `mtFC` trivially satisfied).
- [ ] `mt_soundness_completeness` biconditional.
- [ ] Docstrings; `lake build` green; `lake exe mk_all --module`; re-read `Cslib.lean`.
- [ ] Green commit: `task 496 phase 2: MT.lean (reflexivity: soundness + completeness)`.

**Timing**: ~2 hours (~200–260 lines; LOW risk).

**Depends on**: 1

**Files to create/modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MT.lean` - new.
- `Cslib.lean` - barrel entry (re-read before editing).

**Verification**:
- `lake build` of MT green, zero warnings; all six declarations sorry-free.
- `min_canonical_reflexive_mt` proof contains no `by_contra`/negation (positive-closure check).
- `mt_soundness_completeness` type-checks as an `Iff`.

---

### Phase 3: MS4.lean (reflexivity + transitivity) [NOT STARTED]

**Goal**: Deliver MS4 — MT + transitivity (4 axiom).

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Minimal/MS4.lean` (`import Cslib.Init` + `MinExtension`;
      import `MT` if referencing its constructors as terms — let `shake` decide, see Phase 5 caveat).
- [ ] `MS4ModalAxiom`: MT constructors + `fourBox : □A → □□A` and `fourDia : ◇◇A → ◇A`.
- [ ] `def ms4FC {World} (r) : Prop := (∀ w, r w w) ∧ (∀ {w u v}, r w u → r u v → r w v)`
      (LOCAL; reflexive ∧ transitive).
- [ ] `ms4_axiom_sound`: inherited cases + `fourBox` (uses `f2` to relocate, as `idb`/IS4 do) +
      `fourDia` (plain transitivity on the two `r`-steps).
- [ ] `ms4_soundness` / `ms4_soundness_derivable`.
- [ ] `min_canonical_ms4FC : ms4FC minCanonicalR` bundling `min_canonical_reflexive` and
      `min_canonical_transitive` — POSITIVE port of `is4_canonical_*` via `min_axiom_mem` +
      `min_imp_property`.
- [ ] `ms4_completeness := mkvalidFC_completeness ms4FC … min_canonical_ms4FC`.
- [ ] `ms4_consistent`; `ms4_soundness_completeness` biconditional.
- [ ] Docstrings; `lake build` green; `lake exe mk_all --module`; re-read `Cslib.lean`.
- [ ] Green commit: `task 496 phase 3: MS4.lean (transitivity: soundness + completeness)`.

**Timing**: ~2 hours (~240–300 lines; LOW-MODERATE risk).

**Depends on**: 2

**Files to create/modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MS4.lean` - new.
- `Cslib.lean` - barrel entry (re-read before editing).

**Verification**:
- `lake build` of MS4 green, zero warnings; all declarations sorry-free.
- `min_canonical_transitive` closes positively (no `by_contra`).
- `ms4_soundness_completeness` type-checks.

**Zero-Debt STOP clause (Phase 3)**: The transitivity closure `min_canonical_transitive` is a port
of `is4_canonical_transitive` and is expected verbatim (modulo the `min` prefix and the
`QuasiPrime.closed` accessor). If any clause cannot be closed sorry-free after genuine effort, do
**NOT** insert `sorry` / `axiom` / vacuous `def`. Mark the phase **[BLOCKED]**, record the exact
open goal state in the summary and metadata, and escalate. (Assessed LOW-MODERATE risk — the IK
analogue compiles.)

---

### Phase 4: MS5.lean (equivalence via B — the crux) [NOT STARTED]

**Goal**: Deliver MS5 — MS4 + symmetry (B axiom, **not** euclidean-5), yielding an equivalence
relation (Simpson's S5 birelational frame class).

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Minimal/MS5.lean` (`import Cslib.Init` + `MinExtension`;
      import `MS4` if referencing its constructors as terms — let `shake` decide).
- [ ] `MS5ModalAxiom`: MS4 constructors + `bBox : A → □◇A` and `bDia : ◇□A → A` (**B, NOT**
      euclidean `◇A → □◇A`).
- [ ] `def ms5FC {World} (r) : Prop := reflexive ∧ transitive ∧ (∀ {w u}, r w u → r u w)` (LOCAL;
      the symmetric conjunct is `∀ {w u}, r w u → r u w`).
- [ ] `ms5_axiom_sound`: inherited cases + `bBox` (persistence + symmetry, no F-relocation) +
      `bDia` (plain symmetry).
- [ ] `min_canonical_ms5FC : ms5FC minCanonicalR` bundling refl/trans with `min_canonical_symmetric`
      — POSITIVE port of `is5_canonical_symmetric` (IS5.lean:341): route `□φ∈v → φ∈w` back through
      `minCanonicalR`'s diamond clause via `bDia`, using `min_axiom_mem` + `min_imp_property`.
- [ ] `ms5_completeness := mkvalidFC_completeness ms5FC … min_canonical_ms5FC`.
- [ ] `ms5_consistent`; `ms5_soundness_completeness` biconditional.
- [ ] Docstrings; `lake build` green; `lake exe mk_all --module`; re-read `Cslib.lean`.
- [ ] Green commit: `task 496 phase 4: MS5.lean (symmetry via B: soundness + completeness)`.

**Timing**: ~2.5 hours (~260–320 lines; MODERATE risk — highest of the plan).

**Depends on**: 3

**Files to create/modify**:
- `Cslib/Logics/Modal/Metalogic/Minimal/MS5.lean` - new.
- `Cslib.lean` - barrel entry (re-read before editing).

**Verification**:
- `lake build` of MS5 green, zero warnings; all declarations sorry-free.
- `min_canonical_symmetric` closes positively (deductive-closure chaining only, no consistency/
  negation).
- `ms5_soundness_completeness` type-checks.

**Zero-Debt STOP clause (Phase 4, HIGHEST risk — the MS5 symmetry port)**: `min_canonical_symmetric`
routes `□φ∈v → φ∈w` back through `minCanonicalR`'s diamond clause via `bDia` — the least obvious
chaining in the plan. First attempt the **verbatim port** of `is5_canonical_symmetric` (IS5.lean:341):
replace `canonicalR` two-clause destructuring, `axiom_mem`→`min_axiom_mem`,
`canonical_imp_property`→`min_imp_property`. If it cannot be closed sorry-free after genuine effort,
do **NOT** insert `sorry` / `axiom` / vacuous placeholder — mark the phase **[BLOCKED]**, record the
exact open goal state, and escalate to user review (candidate escalation: whether MS5 needs a small
bespoke `bDia`-membership lemma). Confidence a sorry-free construction exists: HIGH (the IK proof is
compiled and uses only deductive closure, which quasi-prime worlds have via `QuasiPrime.closed`);
confidence zero bespoke lemmas are needed: MEDIUM-HIGH.

---

### Phase 5: Barrel wiring + full CI [NOT STARTED]

**Goal**: Register all four new files in `Cslib.lean` and pass the complete CSLib CI pipeline.

**Tasks**:
- [ ] Run `lake exe mk_all --module` to (re)generate the barrel; re-read `Cslib.lean` immediately
      before and after to confirm all four `Minimal/` modules (`MinExtension`, `MT`, `MS4`, `MS5`)
      are registered and no concurrent-session edits were clobbered.
- [ ] `lake build` (full).
- [ ] `lake exe checkInitImports` — verify `Cslib.Init` imports.
- [ ] `lake lint`.
- [ ] `lake exe lint-style`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix`. **Import-chain caveat**: although the
      conceptual chain is `MK ← MT ← MS4 ← MS5`, `shake` may flag it if each `*ModalAxiom` copies
      its predecessor's constructors verbatim rather than referencing them as terms — if flagged,
      import `MinExtension` (+ `MinCompleteness`) directly, as CK's CS4/CS5 did. Let `shake`
      decide; do not pre-optimize.
- [ ] `lake test` — CslibTests suite.
- [ ] Resolve any CI findings confined to the `Minimal/` subtree; re-run until fully green.
- [ ] Final commit: `task 496: complete implementation (MT/MS4/MS5 modular extensions of MK)`.

**Timing**: ~1 hour (LOW risk, contingent on Phases 1–4 green).

**Depends on**: 1, 2, 3, 4

**Files to create/modify**:
- `Cslib.lean` - final barrel state (re-read before editing).
- Possibly import-line adjustments within the four `Minimal/` files if `shake` flags the chain.

**Verification**:
- Full pipeline green: `lake build`, `checkInitImports`, `lint`, `lint-style`, `shake`, `test` all
  pass with zero warnings.
- All four new modules appear in `Cslib.lean`.
- No edits outside the `Minimal/` subtree and `Cslib.lean`.

---

## Testing & Validation

- [ ] `lake build` succeeds for each of `MinExtension`, `MT`, `MS4`, `MS5` and the full library.
- [ ] Zero `sorry` / zero `axiom` (beyond `DerivationTree`-carried schemata) / zero vacuous `def`
      across all four files (grep + `lean_verify` on the key theorems).
- [ ] Each system exposes: axiom inductive, LOCAL FC predicate, `*_axiom_sound`, `*_soundness`,
      positive canonical FC-closure, `*_completeness`, `*_consistent`, `*_soundness_completeness`.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake lint` and `lake exe lint-style` pass with zero warnings.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (imports minimized).
- [ ] `lake test` passes.
- [ ] Positive-closure discipline: `min_canonical_reflexive*/transitive/symmetric` proofs contain no
      `by_contra`, no negation, no consistency appeal.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Minimal/MinExtension.lean` (Phase 1)
- `Cslib/Logics/Modal/Metalogic/Minimal/MT.lean` (Phase 2)
- `Cslib/Logics/Modal/Metalogic/Minimal/MS4.lean` (Phase 3)
- `Cslib/Logics/Modal/Metalogic/Minimal/MS5.lean` (Phase 4)
- `Cslib.lean` — updated barrel registering the four new modules (Phases 1–5)
- `specs/496_minimal_modal_extensions/summaries/01_minimal-modal-extensions-summary.md` (on completion)

## Rollback/Contingency

- All new work is confined to NEW files under `Minimal/` plus the shared `Cslib.lean` barrel. To
  revert, `git revert` the per-phase commits (each phase is an atomic green commit) or remove the
  four new files and re-run `lake exe mk_all --module` to regenerate `Cslib.lean`.
- Per-phase green commits mean a failed later phase never contaminates earlier delivered systems:
  MT can stand without MS4/MS5; MS4 without MS5.
- If a Zero-Debt STOP clause fires (Phase 3 or Phase 4), the phase is marked **[BLOCKED]** with the
  exact open goal recorded; earlier phases remain committed and green, and the task escalates to
  user review rather than accruing `sorry`/axiom debt.
- Because concurrent sessions may edit `Cslib.lean`, always re-read it immediately before any barrel
  edit; if a conflict is detected, re-run `lake exe mk_all --module` to reconcile rather than
  hand-merging.
