# Implementation Plan: Task #494

- **Task**: 494 - Intuitionistic modal extensions IT / IS4 / IS5 as modular extensions of IK, sound + complete via the birelational canonical model
- **Status**: [COMPLETED]
- **Effort**: 9 hours
- **Dependencies**: Task 492 (IK: `IKModalAxiom`, `ik_axiom_sound`, `ik_soundness`, `ik_completeness`), Task 480 (birelational canonical model: `canonicalR`, `canonical_f1/f2`, `canonicalBModel`, `canonical_imp_property`, witnesses, `modal_prime_exclusion`)
- **Research Inputs**: specs/494_intuitionistic_modal_extensions_IT_IS4_IS5/reports/01_it-is4-is5-extensions.md
- **Artifacts**: plans/01_it-is4-is5-extensions.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add intuitionistic modal logics IT, IS4, and IS5 as modular extensions of the existing IK
formalization (`Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean`), each proven sound and
complete against its birelational frame class via the task-480 canonical model. The work is
one small shared scaffold (`Extension.lean`) that adds a frame-condition-parametrized validity
`IValidFC` plus a ~2-line generalization of `ivalid_completeness`, followed by three thin
per-system files (`IT.lean`, `IS4.lean`, `IS5.lean`) with nested imports mirroring classical
`Systems/{T,S4,S5}`. All task-480/492 assets are reused unchanged (zero churn); the only new
proofs are the per-axiom soundness cases and the three positive canonical-closure lemmas. Done
when all four new files build with zero `sorry`/axioms and pass the full CSLib CI pipeline, and
each system exposes `*_soundness_completeness`.

### Research Integration

Integrated from report `01_it-is4-is5-extensions.md` (cslib-research-hard-agent, tier-1
literature-backed, adversarially verified):

- **Both □ and ◇ axiom forms required per extension** (Wijesekera1990: ◇ is not □-definable
  intuitionistically). The canonical relation is two-clause
  (`canonicalR`, `CanonicalModel.lean:117`), so each closure proof discharges both a box clause
  and a diamond clause.
- **Axiom ↔ frame-condition correspondence**:
  - IT → **reflexive** R; axioms `tBox : □A→A`, `tDia : A→◇A`. Risk LOW.
  - IS4 → **reflexive + transitive** R; axioms `fourBox : □A→□□A`, `fourDia : ◇◇A→◇A`. Risk LOW.
  - IS5 → **reflexive + transitive + symmetric** R (equivalence relation); axioms
    `bBox : A→□◇A`, `bDia : ◇□A→A`. Risk LOW-MODERATE.
- **CRITICAL adversarial finding**: IS5 must be axiomatized via **B / symmetry**, NOT via
  euclidean/5. The classical `canonical_eucl`/`canonical_eucl_from_5` proofs use
  `by_contra` + `mcs_neg_of_not_mem` + double-negation, which do **not** transfer to prime
  theories (not negation-complete). Symmetry closure is fully constructive/positive.
- **Canonical closure** (the key new work per extension): each frame-condition proof is one
  `canonical_imp_property` (`TruthLemma.lean:99`, MP-closure) chained with the two `canonicalR`
  clauses plus a one-line `axiom_mem` helper. No `by_contra`, no negation.
- **Soundness**: extend `ik_axiom_sound` (`IK.lean:131-189`). Only `fourBox` and `bBox` need
  F1/F2 witness relocation, and that exact pattern is already proven by IK's `idb` case
  (`IK.lean:178-184`).

### Prior Plan Reference

No prior plan. This is the first plan for task 494.

### Roadmap Alignment

No `roadmap_path` provided in the delegation context; ROADMAP alignment not evaluated here.
Task advances the intuitionistic-modal-logic formalization line begun in tasks 480 and 492.

## Goals & Non-Goals

**Goals**:
- Add `Extension.lean` scaffold: `IValidFC` (frame-condition-parametrized validity) +
  `ivalidFC_completeness` (adds hypothesis `h_canonFC : FC (@canonicalR Atom Axioms)`) +
  `axiom_mem` helper. Zero changes to `IValid` / IK / task-480 files.
- Add `IT.lean`: `ITModalAxiom` (IK constructors + `tBox`/`tDia`), soundness (reflexive frame
  condition), canonical reflexivity closure, and `it_soundness_completeness` + `it_consistent`.
- Add `IS4.lean`: `IS4ModalAxiom` (IT constructors + `fourBox`/`fourDia`), soundness
  (transitive), canonical transitivity closure, `is4_soundness_completeness` + `is4_consistent`.
- Add `IS5.lean`: `IS5ModalAxiom` (IS4 constructors + `bBox`/`bDia`), soundness (symmetric),
  canonical symmetry closure, `is5_soundness_completeness` + `is5_consistent`.
- Register all four files in the `Cslib.lean` barrel.
- Zero-debt: no `sorry`, no new `axiom`, no vacuous definitions. Full CSLib CI passes.

**Non-Goals**:
- No generic "extension typeclass" over frame conditions (report Deliverable 5: payoff small,
  obscures the three concrete instantiations reviewers expect; classical `Systems/` keeps them
  separate too).
- No euclidean/5 axiomatization of IS5 (report Deliverable 6: non-transferable negation-based
  canonical proof — explicitly rejected).
- No modification of `canonicalR`, `canonical_f1/f2`, `canonicalBModel`, `canonical_imp_property`,
  witnesses, `modal_prime_exclusion`, `IValid`, or any task-480/492 file.
- No new notation; reuse Mathlib `Reflexive`/`Transitive`/`Symmetric` (they exist for
  `α → α → Prop`) rather than defining new frame-condition predicates.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| IS5 canonical symmetry-box clause (`□φ∈v → φ∈w`) is the one step routing a box membership back through the diamond clause (ψ=□φ); least obvious chaining | M | M | Isolate IS5 as its own final phase with a STOP contingency (below). Verify the `bDia` instance shape matches `◇(□φ)→φ` exactly before chaining. All steps remain positive one-liners. |
| Accidental use of euclidean/5 route for IS5 | H | L | Explicit Non-Goal; plan mandates B/symmetry only. Do NOT import or mirror `canonical_eucl`. |
| `fourBox`/`bBox` soundness F1/F2 relocation subtlety | M | L | Mirror the already-compiled IK `idb` case (`IK.lean:178-184`) line-for-line; it is the same F2-relocation pattern. |
| `ivalidFC_completeness` diverges from `ivalid_completeness` beyond the intended ~2-line diff | M | L | Copy `ivalid_completeness` (`Completeness.lean:187`) verbatim, add exactly one binder `(h_canonFC : FC (@canonicalR Atom Axioms))`, thread it into the `h_valid` application. Diff-review against the original. |
| Missing `Cslib.Init` import or barrel registration breaks CI (`checkInitImports`, `mk_all`) | M | L | Every new file starts `import Cslib.Init`; run `lake exe mk_all --module` (or edit barrel) after each file; verify with `checkInitImports`. |
| Phase output exceeds one-dispatch budget | L | L | Each phase is one file, ~200-300 lines, bounded to a single agent run with its own build + no-sorry gate. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases are strictly sequential: each file's nested imports depend on the prior file
(`Extension` ← `IT` ← `IS4` ← `IS5`), so no two phases run in parallel.

### Phase 1: Extension.lean scaffold (frame-condition-parametrized validity + completeness) [COMPLETED]

- **Goal:** Create the shared scaffold that lets IK-derived extensions bolt a frame condition
  onto validity and completeness without touching task-480/492.
- **Tasks:**
  - [x] Create `Cslib/Logics/Modal/Metalogic/Intuitionistic/Extension.lean` starting with
        `import Cslib.Init` then `public import ...Intuitionistic.IK` (pulls Completeness/
        CanonicalModel/TruthLemma transitively).
  - [x] Define `IValidFC (FC : (World→World→Prop)→Prop) (φ : Proposition Atom) : Prop` — a copy
        of `IValid` (`Birelational.lean:193`) with one extra binder `(_fc : FC r)` before the
        world quantifier. Leave `IValid` untouched.
  - [x] Prove `ivalidFC_completeness` — copy of `ivalid_completeness`
        (`Completeness.lean:187`) adding hypothesis `(h_canonFC : FC (@canonicalR Atom Axioms))`
        and passing it into the `h_valid` application (the ~2-line diff site). All axiom
        dischargers threaded through unchanged.
  - [x] Add `axiom_mem` helper: `Axioms φ → φ ∈ w.val` for a `CanonicalPrimeWorld`, via
        `w.property.1.2 [] φ ⟨.ax [] _ h⟩` (report Deliverable 4).
  - [x] Module docstring citing [Simpson1994] and the report; document that `IValidFC`/`IValid`
        coexist and IK is untouched.
  - [x] `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.Extension`; `lean_verify` /
        `grep` confirm zero `sorry`/`axiom`.
  - [x] Register in `Cslib.lean` barrel (`lake exe mk_all --module` or manual insert).
- **Timing:** 2 hours
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Intuitionistic/Extension.lean` (new, ~100-150 lines)
  - `Cslib.lean` (barrel registration)
- **Verification:**
  - `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.Extension` succeeds.
  - No `sorry`/`axiom`/vacuous def (`grep -n "sorry\|:= True\|:= trivial"` clean; `lean_verify`).
  - `IValid` and IK definitions unchanged (`git diff` touches only new file + barrel).

### Phase 2: IT.lean (reflexive; □A→A, A→◇A) [COMPLETED]

- **Goal:** Instantiate the scaffold at IT: reflexive frame class, sound + complete.
- **Tasks:**
  - [x] Create `Cslib/Logics/Modal/Metalogic/Intuitionistic/IT.lean`
        (`import Cslib.Init`; `public import ...Intuitionistic.Extension`).
  - [x] Define `ITModalAxiom : Proposition Atom → Prop` = the 14 `IKModalAxiom` constructors
        verbatim plus `tBox (φ) : (□φ).imp φ` and `tDia (φ) : φ.imp (◇φ)` (report Deliverable 1).
  - [x] Prove `it_axiom_sound` extending `ik_axiom_sound`'s `cases` with the reflexive frame
        condition as hypothesis, via `IValidFC itFC`: `tDia` (EASY, direct witness at `w'` via
        `hrefl w'` -- no persistence needed, since the single `imp`-unfold already delivers `φ`
        forced at the target world itself); `tBox` (EASY, `hbox w' le_refl w' (hrefl w')`).
        Reuse the 14 IK cases verbatim.
  - [x] Prove canonical reflexivity `it_canonical_reflexive : itFC (@canonicalR Atom ITModalAxiom)`
        i.e. `∀ w, canonicalR w w`: box clause via `axiom_mem (tBox φ)` + `canonical_imp_property`;
        dia clause via `axiom_mem (tDia φ)` + `canonical_imp_property` (report Deliverable 4).
        **Deviation from plan**: named the frame condition `itFC` (locally defined,
        `∀ w, r w w`) rather than Mathlib's `Reflexive`, because `Reflexive` is
        `@[deprecated]` in the Mathlib version pinned by this project (superseded by the
        typeclass `Std.Refl`, whose shape does not match `IValidFC`'s bare-predicate `FC`
        parameter) -- using the deprecated name would emit a warning at every use site,
        violating the zero-warnings build gate. `itFC` mirrors the classical
        `Systems/T/Completeness.lean` file's own local `tFC` convention: same semantic content
        (`∀ w, r w w`), no design change, only a naming substitution forced by the pinned
        Mathlib version.
  - [x] Prove `it_completeness` = `ivalidFC_completeness` instantiated with
        `it_canonical_reflexive` as `h_canonFC`; add `it_consistent` (mirror `ik_consistent`,
        trivial reflexive one-point frame on `ℕ`) and `it_soundness_completeness`.
  - [x] `lake build` scoped; zero-sorry verify; barrel register.
- **Timing:** 2 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Intuitionistic/IT.lean` (new, ~200-250 lines)
  - `Cslib.lean` (barrel)
- **Verification:**
  - `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IT` succeeds.
  - `it_soundness_completeness : IValidFC itFC φ ↔ Derivable ITModalAxiom φ` type-checks.
  - Zero `sorry`/`axiom`/vacuous def.

### Phase 3: IS4.lean (reflexive+transitive; □A→□□A, ◇◇A→◇A) [COMPLETED]

- **Goal:** Instantiate at IS4: transitive (+ reflexive) frame class, sound + complete.
- **Tasks:**
  - [x] Create `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS4.lean`
        (`import Cslib.Init`; `public import ...Intuitionistic.IT`).
  - [x] Define `IS4ModalAxiom` = IT constructors + `fourBox (φ) : (□φ).imp (□(□φ))` and
        `fourDia (φ) : (◇(◇φ)).imp (◇φ)`.
  - [x] Prove `is4_axiom_sound` over a conjoined reflexive∧transitive frame condition: `fourDia`
        (EASY: `⟨t, htrans hru hut, hAt⟩`); `fourBox` (MODERATE: F2 relocation exactly as IK
        `idb`, `IK.lean:178-184`, then `htrans`). Reuse IT/IK cases.
  - [x] Prove canonical transitivity `is4_canonical_transitive` (local predicate, mirroring
        `itFC`'s convention rather than Mathlib's deprecated `Transitive`) (box:
        `axiom_mem(fourBox)`+MP ⇒ `□□φ∈w`, then two box-clause applications; dia: two dia-clause
        applications ⇒ `◇◇φ∈w`, then `axiom_mem(fourDia)`+MP).
  - [x] Bundle the frame condition as `is4FC := (∀ w, r w w) ∧ (∀ {w x y}, r w x → r x y → r w y)`;
        prove `is4_completeness` via `ivalidFC_completeness` with `is4_canonical_fc :=
        ⟨is4_canonical_reflexive, is4_canonical_transitive⟩`; add `is4_consistent`,
        `is4_soundness_completeness`.
  - [x] `lake build` scoped; zero-sorry verify; barrel register (`lake exe mk_all --module`).
- **Timing:** 2 hours
- **Depends on:** 2
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS4.lean` (new, ~200-300 lines)
  - `Cslib.lean` (barrel)
- **Verification:**
  - `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IS4` succeeds.
  - `is4_soundness_completeness` type-checks over the refl∧trans frame condition.
  - Zero `sorry`/`axiom`/vacuous def.

### Phase 4: IS5.lean (reflexive+transitive+SYMMETRIC via B; A→□◇A, ◇□A→A) — HIGHEST RISK [COMPLETED]

- **Goal:** Instantiate at IS5 via B/symmetry (equivalence relation), sound + complete. Highest
  risk step: the canonical symmetry-box clause.
- **Tasks:**
  - [x] Create `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5.lean`
        (`import Cslib.Init`; `public import ...Intuitionistic.IS4`).
  - [x] Define `IS5ModalAxiom` = IS4 constructors + `bBox (φ) : φ.imp (□(◇φ))` and
        `bDia (φ) : (◇(□φ)).imp φ`. Do NOT add classical 5 (`◇A→□◇A`).
  - [x] Prove `is5_axiom_sound` over reflexive∧transitive∧symmetric: `bDia` (EASY:
        `hsymm hru`, then `hboxA u le_refl w (hsymm hru)`); `bBox` (EASY-MOD: persistence +
        symmetry witness `⟨w', hsymm hru, A@w'⟩`, no F-relocation). Reuse IS4/IT/IK cases.
  - [x] Prove canonical symmetry `Symmetric (@canonicalR Atom IS5ModalAxiom)`:
        - dia clause `φ∈w → ◇φ∈v`: `axiom_mem(bBox)`+MP ⇒ `□◇φ∈w`; box-clause `w→v` ⇒ `◇φ∈v`.
        - **box clause `□φ∈v → φ∈w` (HIGHEST RISK):** dia-clause `w→v` with ψ=□φ ⇒ `◇□φ∈w`;
          `axiom_mem(bDia)`+MP (`◇□φ→φ`) ⇒ `φ∈w`. Verify `bDia` instance shape is exactly
          `◇(□φ)→φ` before chaining. Still positive, one-line.
  - [x] Bundle `reflexive ∧ transitive ∧ symmetric`; prove `is5_completeness` via
        `ivalidFC_completeness` with `⟨canonicalReflexive, canonicalTransitive, canonicalSymmetric⟩`;
        add `is5_consistent`, `is5_soundness_completeness`.
  - [x] `lake build` scoped; zero-sorry verify; barrel register.
- **Timing:** 3 hours
- **Depends on:** 3
- **STOP contingency:** If the symmetry-box clause (`□φ∈v → φ∈w`) cannot be discharged positively
  after mirroring the report's chaining (dia-clause with ψ=□φ → `axiom_mem(bDia)` → MP), STOP.
  Do NOT fall back to the euclidean/5 route (non-transferable, negation-based — see Non-Goals).
  Mark Phase 4 [BLOCKED], record the exact goal state reached and the `bDia` instance shape, and
  return `status: partial` with `requires_user_review: true`. Phases 1-3 (Extension/IT/IS4) remain
  a complete, independently valuable deliverable and must be committed before stopping.
- **Files to modify:**
  - `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5.lean` (new, ~250-300 lines)
  - `Cslib.lean` (barrel)
- **Verification:**
  - `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5` succeeds.
  - `is5_soundness_completeness` type-checks over the refl∧trans∧symm frame condition.
  - Zero `sorry`/`axiom`/vacuous def.

## Testing & Validation

Per-phase (each phase, before commit):
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.{Extension|IT|IS4|IS5}` succeeds.
- [ ] No-sorry / no-axiom / no-vacuous-def gate: `grep -n "sorry\|:= True\|:= trivial\|:= Unit"`
      on the new file is clean; `lean_verify` on each top-level theorem.

Final (after Phase 4), full CSLib CI pipeline:
- [x] `lake exe cache get` (fetch Mathlib cache, once per branch) — cache already present.
- [x] `lake build` (whole project, syntax linters) — succeeds (3199 jobs); pre-existing
      unrelated `sorry`s/warnings in `Propositional/Tableau/*` files, not task 494.
- [x] `lake exe checkInitImports` (all new files import `Cslib.Init`) — clean, no errors.
- [x] `lake lint` (environment linters) — one pre-existing error in
      `Foundations/Logic/Metalogic/PrimeExclusion.lean` (untouched by this task; confirmed via
      `git diff --stat`), not introduced by task 494.
- [x] `lake exe lint-style` (text linters) — clean, no output.
- [x] `lake test` (CslibTests suite) — succeeds.
- [x] `lake exe mk_all --module` (barrel current for the four new files) — "No update
      necessary" (manual barrel edit already matched).
- [x] `lake shake --add-public --keep-implied --keep-prefix` (import minimization) — `IS5.lean`'s
      suggestion profile matches its already-committed siblings (`IT.lean`/`IS4.lean`/
      `Extension.lean`, which also flag "remove `import Cslib.Init`", never applied since it is
      the mandatory CSLib import); no new debt.
- [x] `git diff` confirms zero churn to task-480/492 files (`IValid`, `canonicalR`,
      `canonical_imp_property`, IK.lean, etc.) — `git diff --stat` empty for all of
      IK/IT/IS4/Extension/CanonicalModel/Completeness/TruthLemma/Birelational.lean.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Intuitionistic/Extension.lean` (scaffold)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/IT.lean`
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS4.lean`
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5.lean`
- Updated `Cslib.lean` barrel (4 new import lines)
- `specs/494_intuitionistic_modal_extensions_IT_IS4_IS5/summaries/01_it-is4-is5-extensions-summary.md`
  (on completion)

## Rollback/Contingency

- All four files are new; rollback is `git checkout Cslib.lean && git rm` the new files. No
  task-480/492 asset is modified, so reverting cannot regress IK or the canonical model.
- Phases are strictly additive and independently buildable in order: Extension → IT → IS4 → IS5.
  If a later phase fails, all earlier phases are complete, committed, and valuable on their own.
- Commit incrementally after each green phase (`task 494 phase P: {name}`). The IS5 STOP
  contingency (Phase 4) preserves Phases 1-3 as a shippable partial deliverable.
