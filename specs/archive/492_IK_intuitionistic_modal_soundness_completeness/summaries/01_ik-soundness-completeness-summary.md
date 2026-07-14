# Implementation Summary: Task #492 — IK Soundness + Completeness

- **Task**: 492 - IK (intuitionistic modal logic K) soundness + completeness over birelational
  semantics
- **Plan**: `plans/01_ik-soundness-completeness.md`
- **Status**: [COMPLETED] (all 3 phases)
- **Mode**: `--hard`, single dispatch, self-executed (no sub-agent delegation)

## What Was Built

A single new file, `Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean` (~260 lines), plus one
additive barrel import line in `Cslib.lean`. No existing file (480 framework or classical) was
modified.

### Phase 1 — `IKModalAxiom` datatype

`inductive IKModalAxiom : Proposition Atom → Prop` with 14 constructors: 9 intuitionistic
propositional schemata (`implyK`, `implyS`, `efq`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`,
`orE`, mirroring `IntPropAxiom`) plus 5 modal schemata `k`/`kdia`/`cd`/`idb`/`dbot` (Simpson's
`k1`-`k5`). The and/or constructors use the `Cslib.Logic.Axioms.*` reducible-abbrev shapes so
they discharge the 480 framework's hypotheses definitionally; this was confirmed by the Phase 3
instantiation typechecking without any `rfl`/shape-matching workaround.

### Phase 2 — `ik_soundness_derivable` (the only new proof)

- `ik_axiom_sound : IKModalAxiom φ → IValid φ` — one `cases` per constructor. Non-modal cases
  mirror `PL.int_axiom_sound` (packaging the loose `r`/`f1`/`f2` IValid parameters into an
  anonymous `⟨r, f1, f2⟩ : BFrame World` term to feed `bforces_persistence`'s implicit frame
  arg). Modal cases:
  - `k`/`kdia`/`cd`: pure quantifier bookkeeping over `≤ ∘ r` / `r`, no frame condition.
  - `idb`: consumes `BFrame.f2` (down-confluence) to relocate the `◇φ`-witness world upward
    before applying the `(◇φ → □ψ)` hypothesis.
  - `dbot`: vacuous under `IValid` (`botForces = fun _ => False` makes `BForces (◇⊥)` reduce to
    `∃ u, r w u ∧ False`, i.e. `False`).
- `ik_soundness` — structural induction on `DerivationTree IKModalAxiom`, with the
  `necessitation` case handled exactly as classical `Metalogic/Soundness.lean`'s (recursing into
  the empty-context premise at the successor world via `fun _ h => nomatch h`).
- `ik_soundness_derivable : Derivable IKModalAxiom φ → IValid φ`.

### Phase 3 — Completeness/consistency instantiation + barrel

- `ik_completeness` — one-liner instantiating 480's `ivalid_completeness` at
  `Axioms := IKModalAxiom`, each of the 14 dischargers the matching constructor.
- `ik_consistent : ¬ Derivable IKModalAxiom ⊥` — corollary of soundness, refuted by
  instantiating `IValid ⊥` at a trivial one-point-reachability frame on `ℕ`.
- `ik_soundness_completeness : IValid φ ↔ Derivable IKModalAxiom φ`.
- `Cslib.lean` — added `public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IK`
  (alphabetically between `...Intuitionistic.Completeness` and `...Intuitionistic.PrimeTheory`).

## Axiom-to-Hypothesis Discharge Map

| 480 framework hypothesis | IK axiom (Simpson) | Discharger |
|---|---|---|
| `h_implyK`/`h_implyS`/`h_efq` | intuitionistic base | `.implyK`/`.implyS`/`.efq` |
| `h_andI`/`h_andE1`/`h_andE2` | ∧-axioms | `.andI`/`.andE1`/`.andE2` |
| `h_orI1`/`h_orI2`/`h_orE` | ∨-axioms | `.orI1`/`.orI2`/`.orE` |
| `h_K` | k1 (Kb) | `.k` |
| `h_Kdia` | k2 (Kd) | `.kdia` |
| `h_Idb` | k4 (Idb) | `.idb` |
| `h_Cd` | k3 (Cd) | `.cd` |
| `h_dbot` | k5 (Nd) | `.dbot` |

All 14 dischargers typecheck as one-line lambdas to the matching constructor (report's
`rfl`-discharge prediction for and/or holds; no shape-matching workaround was needed).

## Zero-Debt Verification

- `grep -nE '\bsorry\b|admit|^ *axiom '` on `IK.lean`: no true hits (one false-positive grep match
  on the word "axiom" inside a docstring sentence, not a declaration).
- `lean_verify` on all four top-level theorems:
  - `ik_axiom_sound`: `axioms: []`
  - `ik_soundness_derivable`: `axioms: []`
  - `ik_completeness`: `axioms: [propext, Classical.choice, Quot.sound]` (inherited from the 480
    framework's classical case-split on consistency — the standard trio, no new axiom)
  - `ik_soundness_completeness`: `axioms: [propext, Classical.choice, Quot.sound]`

## CI Pipeline Results

| Step | Result |
|---|---|
| `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IK` | pass, no warnings |
| `lake build` (whole tree) | pass (3195 jobs; pre-existing `sorry` warnings in unrelated files: `Propositional/Tableau/{Intuitionistic,Minimal}/{Scheme,Completeness}.lean` — not part of this task) |
| `lake exe checkInitImports` | pass (no output) |
| `lake exe lint-style` | pass after fixing one space-before-semicolon in an `IK.lean` comment (line 186) |
| `lake test` | pass, exit 0 |
| `lake shake --add-public --keep-implied --keep-prefix` | exits 1 at whole-repo level (59 pre-existing findings unrelated to this task); `IK.lean`'s one finding (`remove import Cslib.Init`) is the same accepted false-positive pattern shake reports for every sibling 480-framework file (`Completeness.lean`, `PrimeTheory.lean`, `CanonicalModel.lean`) — `import Cslib.Init` is mandatory per `checkInitImports`/CONTRIBUTING.md and is intentionally kept despite shake's suggestion |

## Plan Deviations

- **Skipped the standalone Phase-1 sanity `example`/`#check`** proposed in the plan (to confirm
  the five modal dischargers match the 480 hypothesis shapes before Phase 2). This was
  superseded by the Phase 3 `ik_completeness` instantiation, which typechecks all 14 dischargers
  against the exact hypothesis types — an equivalent but non-redundant verification (avoids an
  unused declaration that `lake lint`/`lint-style` could flag).
- No other deviations from the plan. All phase task-level checklist items were completed as
  specified; no postmortem-constraint conflicts arose (research report's H4 adversarial
  verification — Nd vacuity, Idb's F2 usage, no extra frame condition needed — was confirmed
  exactly during the soundness proof).

## Artifacts

- `Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean` (new)
- `Cslib.lean` (modified — one import line)
- `specs/492_IK_intuitionistic_modal_soundness_completeness/plans/01_ik-soundness-completeness.md`
  (phase markers updated to [COMPLETED])
- `specs/492_IK_intuitionistic_modal_soundness_completeness/summaries/01_ik-soundness-completeness-summary.md`
  (this file)
