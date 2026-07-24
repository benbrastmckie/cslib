# Summary: Phase 9 Probe Gate — Dispatch 1 (Cases A/B/C/E PASS, Case D FAIL)

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994 Thm
  8.1.4's biconditional
- **Plan**: plans/06_target-independent-theta-translation.md (Phase 9)
- **Status**: [PARTIAL] — hard gate reports FAIL (case D only); Phase 9 remains [IN PROGRESS]
- **Type**: cslib

## What Was Done

Wrote `probes/theta_place_validation.lean` (scratch, outside `Cslib/`), defining the candidate
target-independent translation:

- `Θ(G,Γ,root) := sigAt G Γ hfin root ∧ bigAndL(orphanFacts G Γ root)`, where `orphanFacts` is the
  `Γ`-facts at labels NOT reachable from `root` (the orphan-context component the plan's Risk
  section mandates).
- `place(ht,x,A) := boxIter (ht x) A` (`□^{ht x} A`), with `ht` an explicit graded-rank function
  mirroring `IsDerivationForest`'s own witness pattern (`ht0 := fun _ => 0` for `Graph.trivial`;
  `ht2 := Function.update ht0 c2 1` for the one-edge extension).

Subjected this candidate to all five gate cases from the plan:

| Case | Description | Result |
|------|--------------|--------|
| A | disconnected conclusion (`nik_adequacy_is_false`'s witness) | **PASS** |
| B | disconnected context (orphan-component test) | **PASS** |
| C | `premise_escapes_graph` shape, no `x∈G.X` restriction | **PASS** |
| D | `orE` at depth ≥ 1 | **FAIL** |
| E | `Graph.trivial` collapse (Phase 20 assembly) | **PASS** |

**Overall gate verdict: FAIL** (on case D alone).

Every theorem in the probe is sorry-free; `#print axioms` on every case's result shows only
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`. The file compiles under
`lake env lean` at exit 0, zero warnings. `Cslib/` was not touched (`git status --short Cslib/`
was clean at every commit boundary in this dispatch, aside from a concurrent, unrelated
agent's edit to `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, which this dispatch did not
stage or touch).

## Case D: the Precise Finding

Built a concrete two-level graph (`Gt2`: root `r`, depth-1 child `c2`, disconnected target `y3`)
and stated `orE`'s core step generically in the three premise translations
(`caseD_orE_core_from_bridge`):

```
inject : ∀ D Γ, ⊢ (Θ(Γ) ∧ place(c2,D)) ⊃ Θ((c2∶D)::Γ)     -- Θ-injection (Phase-12-scoped, posited)
bridge : ⊢ □(A∨B) ⊃ (□A ∨ □B)                              -- the suspected non-theorem
hOr    : ⊢ Θ(Γ) ⊃ place(c2, A∨B)
hA     : ⊢ Θ((c2∶A)::Γ) ⊃ place(y3,C)
hB     : ⊢ Θ((c2∶B)::Γ) ⊃ place(y3,C)
⊢ Θ(Γ) ⊃ place(y3,C)
```

This IS provable given `bridge` (fully machine-checked, sorry-free). The probe then attempts the
natural alternative — stripping all boxes off `hOr` via the always-sound `CS5ModalAxiom.tBox`
(no non-theorem risk there) to get a bare `Θ(Γ) ⊃ (A∨B)` — and shows it does NOT avoid the wall:
the branch hypotheses derived via `inject` are necessarily BOXED (`Θ(Γ)⊃(□A⊃place(y3,C))`,
matching `place`'s own box-indexing at `c2`'s depth), and there is no route from a bare `(A∨B)`
to boxed branch antecedents without either (a) hypothesis-level necessitation `A ⊃ □A` (not
available: necessitation only applies to closed derivable formulas, never to an arbitrary
hypothesis), or (b) `bridge` itself again. **No third route was found.**

This CONFIRMS — via an actual machine check of the specific inference shape, not just an
inherited assertion — the plan's own flagged "primary residual risk": the flat, depth-indexed
`place(x,A) := □^{d(x)}A` genuinely requires the non-theorem `□(A∨B) ⊃ (□A∨□B)` (the same one
that killed plan v4's fully-boxed flat shortcut) once the disjunction sits at depth ≥ 1. No
semantic countermodel of `bridge` was built in this probe (out of scope for a shape-validation
gate — this would need a Kripke-model construction, a separate piece of work); the deliverable is
the structural dependency itself, machine-checked.

## Plan Deviations

- **Literature discovery skipped.** The plan's Phase 9 task list recommends (non-blocking)
  attempting a `/literature` discovery pass for a cleaner Simpson §6.1 PDF before validating the
  translation. This dispatch did not attempt it, time-boxed against the hard-gate scope. Flagged
  explicitly in the probe's header comment as a still-open, non-blocking mitigation item for a
  future dispatch.
- **`Θ`-injection posited, not independently re-derived for the concrete `Gt2` witness.** The
  landed `sigAt_cons_self_imp` (the closest analogue) itself avoids computing an explicit
  `Finset.toList` for a node's children, reasoning abstractly via `sigAtFuel_congr_above_rank`
  instead — confirming that a fully concrete root-to-child injection proof is genuine Phase
  12-sized infrastructure work, not Phase 9 shape-validation work. The injection step's
  plausibility is not in question (`box_and_intro`'s K-distribution-over-`∧` argument, which the
  probe DOES prove sorry-free, is exactly the tool such a proof would use, and hits no wall); it
  is posited as an explicit, named hypothesis in `caseD_orE_core_from_bridge` so Case D's actual
  question (does the disjunction step need the non-theorem) is isolated precisely.
- **No layered-alternative candidate built yet.** Per the plan's FAIL-handling instructions,
  finding case D's obstruction should prompt iterating on a layered `Θ_0 ⊃ □(Θ_1 ⊃ □(…))`
  alternative within Phase 9's three-run budget before routing to Phase 23. This dispatch (run 1
  of the cap) spent its budget confirming the wall precisely rather than also designing and
  validating a replacement; recommended as the next dispatch's sole focus (see below).

## Next Steps (for the next Phase 9 dispatch)

Design a layered `place`/`Θ` alternative whose per-level antecedents carry the disjunction
UNBOXED at the correct nesting level (so the Hilbert `orE` axiom applies directly, not to a
flattened `□^d`-wrapped formula), then re-run ALL FIVE gate cases (A-E) against it — a layered
redesign changes both `Θ` and `place`, so the currently-passing cases must be re-confirmed, not
assumed to still hold. Only if no candidate closes all five cases within Phase 9's remaining
budget (2 runs left of the 3-run cap) does this route to Phase 23.

## Artifacts

- `specs/537_labelled_cs5_general_soundness_biconditional/probes/theta_place_validation.lean`
  (new, 400 lines, sorry-free, axiom-clean)
- `specs/537_labelled_cs5_general_soundness_biconditional/plans/06_target-independent-theta-translation.md`
  (Phase 9 checklist annotated with per-case verdicts and dispatch-1 finding)
- `specs/537_labelled_cs5_general_soundness_biconditional/.orchestrator-handoff.json` (overwritten)

## Verification

- `lake env lean specs/537_labelled_cs5_general_soundness_biconditional/probes/theta_place_validation.lean`
  — exit 0, zero warnings.
- `#print axioms` on all 7 named case results (`caseA_theta_imp_place`, `caseB_theta_imp_place`,
  `caseC_no_restriction_needed`, `caseD_orE_core_from_bridge`, `caseE_theta_trivial_deriv`,
  `caseE_collapse`) — all show `[propext, Classical.choice, Quot.sound]` only, no `sorryAx`.
- `grep -c '\bsorry\b'` on the probe file — 0.
- `Cslib/` untouched by this dispatch (verified via `git status --short Cslib/` at each commit
  boundary).
