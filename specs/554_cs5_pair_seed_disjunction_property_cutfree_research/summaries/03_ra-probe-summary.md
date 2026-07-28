# Implementation Summary: (R-a) Probe and Kill-Branch Disposition (Round 3)

- **Task**: 554 - CS5 pair-seed obligation: (R-a) probe and conditional product-model route
- **Plan**: plans/03_ra-probe-product-model.md
- **Outcome**: Kill-criterion FIRED — (R-a) REFUTED, machine-checked. Phases 1-2 [COMPLETED];
  Phases 3-6 [BLOCKED]: (R-a) refuted, by design. Task closes [BLOCKED] per the user's
  rescoped kill-criterion, `requires_user_review: true`.
- **Date**: 2026-07-28

## What Was Done

### Phase 1 [COMPLETED] (commit e0feaf85)

Probe `probes/ra_total_probe.lean` (sorry-free, `lake env lean` exit 0):

- **P1** `total_validates_boxEm`: under `BForces`' box clause, a total `r` degenerates `□` to a
  world-independent global modality, so every total-`r` birelational model forces `□a ∨ ¬□a` at
  every world (no frame conditions or valuation monotonicity needed).
- **P2** `boxEm_not_derivable`: `□a ∨ ¬□a` is not `IS5`-derivable — two-world chain `w₀ ≤ w₁`,
  `r := Eq`, `a` true at `w₁` only, converted by `is5_soundness_derivable`. Fully constructive
  (zero axioms).
- **P3** `ra_route_refuted`: the route-required total-countermodel supply — for every `(H, A)`
  with `A ∉ cl_IS5(H)` a total-`r` model with `u ⊩ H`, `v ⊮ A`, `r u v` — is refuted at
  `H := ∅`, `A := □a ∨ ¬□a`.

### Phase 2 [COMPLETED] (commit bedd7223)

Verdict landed as `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5TotalModels.lean`
(222 lines, sorry-free, barrel-registered), with library-grade names:

| Probe name | Library name |
|---|---|
| `total_validates_boxEm` | `bforces_boxEm_of_total` |
| `boxEm_not_derivable` | `boxEm_not_derivable` |
| `PW` / `pw_top` / `pw_mono` | `BoxEmWorld` / `.eq_w1_of_w1_le` / `.eq_w1_of_le` |
| `TotalCountermodel` | `IS5TotalCountermodel` |
| `RaRouteRequirement` | `IS5TotalCountermodelSupply` |
| `boxEm_not_in_empty_closure` | `boxEm_not_mem_empty_closure` |
| `ra_route_refuted` | `is5TotalCountermodelSupply_false` |

Module docstring cites [MarinMoralesStrassburger2021] §7-8 and [Simpson1994] Ch. 3 with durable
anchors only. Sanctioned docstring cross-reference added at `CS5PairSeedRightExclusion`
(`CS5Completeness.lean`): both residuals of the product-model route are machine-closed —
box-membership transfer ⟺ `CS5 = IS5` collapse (`is5_derivable_of_boxNotMem_transport`), and
the total-countermodel supply is refuted (`is5TotalCountermodelSupply_false`).

## Verification

- Scoped `lake build` of `IS5TotalModels` and `CS5Completeness`: green (first attempt).
- `lean_verify` axiom audit: `bforces_boxEm_of_total` / `is5TotalCountermodelSupply_false` use
  only `propext, Classical.choice, Quot.sound`; `boxEm_not_derivable` is **axiom-free**.
- `lake exe checkInitImports` exit 0; `lake exe lint-style` clean; `lake shake` clean on touched
  modules; `lake test` green.
- Grep gate `kdisj|kfs|kbot|[ADS15]|[MMS21]|[Pacheco24]` empty on touched files.
- Zero sorries added by this task; preserved assets untouched except the sanctioned docstring
  addition (`git diff` on `CS5Completeness.lean`: +8 docstring lines only).

## Disposition (Kill Branch)

Per the rescoped task description's verbatim kill-criterion, the task closes **[BLOCKED]** with
report 02 §5.4's cost table as justification — a negative result is the deliverable.
Both consumers' answers, restated:

- **Pair-Lindenbaum consumer**: `CS5PairSeedRightExclusion` is not dischargeable by any
  surveyed route without the user-authorised `CS5 = IS5` collapse (the (R-b) residual is
  machine-checked equivalent to it; the (R-a) residual is now machine-refuted).
- **Labelled-soundness consumer**: the `sigAt` fold is unrepairable; answer "never", unchanged
  (report 02 §7).

Continuation past this point requires an explicit user decision (e.g. authorising the collapse
route, or accepting the negative result and closing the line of work).

## Plan Deviations

- **File path**: the dispatch message named `Constructive/Intuitionistic/IS5TotalModels.lean`;
  the plan (binding) specifies `Metalogic/Intuitionistic/IS5TotalModels.lean`, which is where
  the file was created. No `Constructive/Intuitionistic/` directory exists.
- **mk_all side effect**: `lake exe mk_all --module` also auto-added a barrel line for the
  unregistered `Foundations/Logic/Tableau/Blocking.lean` (owned by the concurrent shared-tableau
  task). That line was dropped from this task's commit as out-of-territory; its owner must
  register it.
- **Baseline drift (documented, not caused here)**: repo-wide bare-sorry census is now 10 vs
  the plan's baseline 5 — the 5 extra live in `Bimodal/.../ChronicleToCountermodel.lean` (4)
  and `Modal/Tableau/FrameSoundness.lean` (1), committed by concurrent tasks. `lake lint` also
  has pre-existing failures in Bimodal/Temporal modules from another task's linter-suppression
  removals. This task's touched files have zero lint findings and zero sorries.
