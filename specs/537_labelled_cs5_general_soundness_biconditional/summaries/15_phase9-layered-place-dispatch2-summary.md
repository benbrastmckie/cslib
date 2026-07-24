# Phase 9 Probe Gate — Dispatch 2: Layered `place` Redesign

## Status

Phase 9 remains **[IN PROGRESS]**. This dispatch does not close the gate unconditionally, but it
refutes dispatch 1's blanket finding ("`orE` always needs the bridge") and replaces it with a
precisely localized, machine-checked conditional result. One dispatch remains of the 3-run cap.

## What was done

Wrote `specs/537_labelled_cs5_general_soundness_biconditional/probes/theta_place_layered.lean`
(402 lines, scratch probe, not under `Cslib/`, not imported by anything). `Cslib/` was not
touched (verified via `git status --short Cslib/` before and after; the concurrent modification
to `Cslib/Logics/Modal/Tableau/LoopChecking.lean` by another agent was neither staged nor
committed by this dispatch).

**Design**: kept `Θ(G,Γ,root) := sigAt G Γ hfin root ∧ bigAndL(orphanFacts G Γ root)` completely
unchanged (still target-independent, still root-anchored, `sigAt`/`bigAndL`/`orphanFacts` all
Preserved Assets or dispatch-1-established, reused verbatim). Redesigned `place` to recurse into
`∨`:

```
place(ht, x, P ∨ Q) := place(ht,x,P) ∨ place(ht,x,Q)      -- by rfl, no theorem
place(ht, x, A)      := boxIter (ht x) A                   -- otherwise, flat as before
```

This is the literal "discharge the disjunction at the layer where it lives, before any boxing
applies to it" instruction: `place(x, A∨B)` unfolds **definitionally** (`rfl`) to `place(x,A) ∨
place(x,B)`, so a disjunctive target's translation is *already* the disjunction of its disjuncts'
own (flatly-boxed) translations — no `□(A∨B) ⊃ (□A∨□B)` bridge theorem is ever needed to get
there.

## Per-case verdicts (all five re-validated against the new candidate)

| Case | Result | Notes |
|------|--------|-------|
| A (disconnected conclusion) | **PASS** | Unaffected — `place` only diverges from dispatch 1 at depth ≥ 1 on `∨`-headed formulas; A uses `ht0`/depth 0 throughout. Re-proved via `place_zero` (now structural induction, not `rfl`, since the `∨` case needs both sub-formula IHs) → `place_ht0`. |
| B (disconnected context / orphan) | **PASS** | Same as A; orphan-context component untouched. |
| C (`premise_escapes_graph` shape) | **PASS** | Same as A; still zero `x ∈ G.X` restriction. |
| D (`orE` at depth ≥ 1) | **CONDITIONAL PASS**, precisely localized residual (see below) | The core obstruction dispatch 1 found is refuted as a *blanket* claim. |
| E (`Graph.trivial` collapse) | **PASS** | Unaffected — depth 0 at the root. |

## Case D in detail

`caseD_orE_core_layered` (mirrors dispatch 1's `caseD_orE_core_from_bridge` in shape and
hypotheses — same `inject`, `hOr`, `hA`, `hB` — but **drops the `bridge` hypothesis entirely**)
closes the exact adversarial two-level-graph `orE`-at-depth-1 scenario using only:
`place`'s `∨`-recursion (`rfl` — no bridge/box-or-distribution theorem anywhere), `inject`'s
already-valid `box_and_intro`-based route (dispatch 1's own finding, unchanged), and the plain
Hilbert `orE` axiom. Zero `sorry`, no `sorryAx`.

**When is `hOr` (the major premise's translation) available in the split form
`caseD_orE_core_layered` needs?** For free, no extra hypothesis, whenever the disjunction arose
via `orI1`/`orI2` — machine-checked in `hOr_split_from_orI1` (a single-disjunct IH plus the plain
`orI1` Hilbert axiom suffices).

**The honest residual**, machine-checked in `hOr_split_needs_bridge_from_flat` (non-vacuous per
the concrete witness `place_ht2_c2_atom`): if the disjunction instead arose via the ASSUMPTION
rule — i.e. Γ literally asserts a compound fact `y:(A∨B)` at some label — `sigAt`'s fixed
recursive structure (a Preserved Asset; cannot be changed under the plan's postmortem
constraints) can only ever deliver the FLAT boxed form `□(A∨B)` for that sub-case, never the
split form directly, and getting from flat to split still requires exactly dispatch 1's
non-theorem bridge.

**Net effect on the diagnosis**: dispatch 1's finding narrows from *"`orE` always needs the
bridge"* to *"`orE` needs the bridge only if a disjunctive fact is ever a raw context assumption,
rather than always being introduced via `orI1`/`orI2`."* This is a strictly narrower, more
precisely localized obstruction — genuine progress, not a repeat of dispatch 1's finding — but it
is **not** an unconditional PASS, because whether `cs5_completeness`'s canonical construction ever
hands `nik_adequacy` a context with a literally-compound assumption is a Phase-13-scoped question
this dispatch did not investigate (out of Phase 9's shape-validation remit; would require reading
the canonical-model construction, not the `Θ`/`place` translation).

## Plan Deviations

- Wrote a **new** probe file (`theta_place_layered.lean`) rather than editing dispatch 1's
  `theta_place_validation.lean` in place, per the plan's own dispatch-2 direction ("(or a new
  probe file)"). Dispatch 1's probe is preserved unmodified.
- The plan's FAIL-handling text anticipated a clean re-validation of all five cases against a
  layered candidate, with an implicit expectation of an unconditional PASS/FAIL outcome. This
  dispatch instead produced a **conditional** result (PASS modulo a precisely localized,
  machine-checked residual) rather than a clean binary verdict. This is reported explicitly
  rather than rounded up to "PASS" or down to "FAIL" — per the hard-mode instruction not to
  weaken any statement to force a case to pass, and per the instruction that a precise finding
  (even a partial one) is a legitimate deliverable.
- Did not investigate `cs5_completeness`'s canonical-model construction to resolve the residual
  (would determine whether the assumption-rule sub-case is actually reachable) — flagged in the
  plan as the natural next step for either the final Phase 9 dispatch or for Phase 13, not
  attempted here to stay within this dispatch's scope and the territory constraint
  (`probes/` only).

## Files modified

- `specs/537_labelled_cs5_general_soundness_biconditional/probes/theta_place_layered.lean` (new,
  402 lines, compiles clean at exit 0, zero `sorry`/`admit`, `#print axioms` on all 9 theorems
  shows no `sorryAx`).
- `specs/537_labelled_cs5_general_soundness_biconditional/plans/06_target-independent-theta-translation.md`
  (Phase 9 section annotated with the dispatch-2 finding).
- `specs/537_labelled_cs5_general_soundness_biconditional/.orchestrator-handoff.json` (this
  dispatch's handoff).
- This summary.

## Sorry inventory

None. Zero `sorry`, zero `admit`, zero new `axiom`, zero vacuous definitions anywhere in this
dispatch's changes.

## Next steps

Per the plan (updated above): one Phase 9 dispatch remains of the 3-run cap. Recommended next
action: inspect `cs5_completeness`'s canonical-model construction to determine whether
`nik_adequacy`'s derivations can ever present a literally-compound (disjunctive) context
assumption. If not possible, case D becomes an unconditional PASS with no further redesign of
`place` needed, and Phase 9 can report a clean gate PASS. If possible, the conditional result
should be accepted and Phase 13/16 designed to carry the `orI1`/`orI2`-vs-assumption case split
through explicitly (the assumption sub-case would then need its own dedicated resolution, e.g. a
context well-formedness invariant restricting compound assumptions, or accepting that sub-case as
Phase 23-routed).
