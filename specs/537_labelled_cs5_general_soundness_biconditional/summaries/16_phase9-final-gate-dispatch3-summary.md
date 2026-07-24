# Phase 9 Probe Gate — Dispatch 3 of 3 (FINAL) — Summary

## Task

Settle the single question dispatch 2 left open: can a disjunctive formula appear in `Γ` at a
label, as an `NIK.assumption`, in the derivations `nik_adequacy` must cover? Dispatch 2's own
recommended next step was to inspect `cs5_completeness`'s canonical-model construction to answer
this. This dispatch found a more direct, decisive route and did not need that inspection.

## What was done

Read `Deduction.lean`'s `inductive NIK` constructor signatures directly (not re-derived, just
read as the source of truth for what the calculus permits). `impI`, `orE`, and `diaE` all extend
`Γ` with a fully unrestricted `Proposition Atom` — no atomicity side-condition anywhere in the
inductive definition. Since the plan's own established signature for `nik_adequacy` (line 660)
quantifies over **every** `Γ`, with **no** `x ∈ G.X`/`labels(Γ) ⊆ G.X` restriction, the
`assumption`-case proof obligation must be discharged for every `Γ` reachable via `NIK`'s own
rules — independent of what `cs5_completeness`'s canonical construction happens to instantiate.
This makes the originally-proposed `cs5_completeness`-inspection route moot: the obstruction is
intrinsic to the calculus.

Wrote `probes/theta_place_final_gate.lean` (scratch, outside `Cslib/`), machine-checking two
things:

1. **`compound_assumption_derivation`** — a genuine, closed `NIK TS5` term (not a hypothesis)
   discharging a literally-compound (`P0 ∨ P1`, both atoms) context assumption via ordinary
   `impI` (proving the unremarkable theorem `c2 : (P0∨P1) ⊃ (P0∨P1)`), at depth 1 below root
   (reusing dispatch 1/2's own `Gt2`/`c2`/`ht2` case-D graph infrastructure verbatim). This is the
   concrete reachability witness the plan's question asked for.
2. **`hOrFlat_concrete`** — NOT a hypothesis this time (dispatch 2's `hOr_split_needs_bridge_from_flat`
   took its flat premise as an abstract, unproven hypothesis): concretely DERIVED, by unfolding
   `sigAt`'s actual `factsAt`-fold at `c2` via the landed, Preserved-Asset `sigAtFuel`/`bigAndL`
   machinery (`sigAtFuel_ΓCompound_c2_imp` extracts the flat conjunct at `c2`;
   `sigAt_r_imp_box_sigAtFuel_c2` boxes it up to the root via plain conjunct-membership
   extraction — no toList/Finset computation needed, only `Set.Finite.mem_toFinset`/
   `Finset.mem_toList` iff-lemmas), that `Θ(Gt2, ΓCompound, r)` implies ONLY the flat `□(P0∨P1)`,
   never the split `□P0 ∨ □P1`, for exactly the `Γ` shown reachable in (1).

`caseD_assumption_needs_bridge` then composes these: closing the layered `place`'s split-form
obligation for this concrete, reachable `Γ` needs exactly the non-theorem bridge
`□(A∨B) ⊃ (□A∨□B)` established by dispatches 1-2 (not re-derived or re-litigated here, per the
hard instruction against re-attempting it).

## Gate verdict: (b) GATE FAIL, definitive

The layered `Θ`/`place` candidate from dispatch 2 is **insufficient** to complete `nik_adequacy`
in general. This dispatch exhibits a genuine derivation forcing the exact obstruction dispatch 2
could only pose hypothetically — closing the gap between "the flat-vs-split issue is non-vacuous
in the shapes" (dispatch 2) and "the flat-vs-split issue is forced by an actual, reachable
derivation" (this dispatch).

**Root cause**: `sigAt`'s WHOLESALE (non-recursive) `factsAt`-fold cannot see inside a context
fact's own top connective — it boxes a context fact up the tree exactly as given, regardless of
whether that fact is itself a disjunction. `place`'s own `∨`-recursion (dispatch 2's redesign)
only ever sees a disjunction AT THE POINT `place` is applied to a TARGET formula (e.g. after
`orI1`/`orI2` introduction) — never retroactively inside `Θ`'s CONTEXT-fact folding.

**What the next redesign would require**: `sigAt` itself would need to split a compound context
fact's translation recursively (mirroring what `place` already does for target formulas) — but
`sigAt` is an explicit Preserved Asset under this task's postmortem constraints ("do NOT touch or
re-derive any Preserved Asset row"). That fix is out of Phase 9's remit and was not attempted.

## Disposition

Phase 9's 3-dispatch cap is exhausted with a definitive FAIL. Phase 9 is marked `[BLOCKED]` in
the plan. The task must escalate for a re-plan with one of two options:

- **(i)** Lift the `sigAt`-frozen postmortem constraint and redesign `Θ`'s context-fold to split
  compound facts recursively (a genuine, non-trivial new piece of infrastructure).
- **(ii)** Abandon the target-independent-`Θ` strategy in favor of the alternative
  `nikTr`-per-label route already partially landed in `Soundness.lean` — where `sigAt_assumption`
  (already landed, sorry-free) closes the `assumption` case for FREE, unconditionally, for ANY
  formula (compound or not), since it concludes AT the assumption's own label with no boxing at
  all. That route has its own, *different*, already-documented obstruction instead:
  `efq`/`orE`'s cross-label lowest-common-ancestor bridging problem
  (`Soundness.lean:1889-1911`), which is not adjudicated by this dispatch (out of scope; a
  genuinely different mathematical question from the flat-vs-split issue investigated here).

Phase 10+ remains BLOCKED pending this re-plan decision. Neither option was attempted in this
dispatch — both require a task-level scope decision beyond Phase 9's shape-validation remit.

## Files touched

- `specs/537_labelled_cs5_general_soundness_biconditional/probes/theta_place_final_gate.lean`
  (new; sorry-free, axiom-clean, compiles at exit 0; `Cslib/` untouched, verified via
  `git status --short Cslib/` before and after)
- `specs/537_labelled_cs5_general_soundness_biconditional/plans/06_target-independent-theta-translation.md`
  (Phase 9 heading -> `[BLOCKED]`; dispatch 3 finding appended)
- `specs/537_labelled_cs5_general_soundness_biconditional/.orchestrator-handoff.json` (rewritten)

## Plan Deviations

None from Phase 9's own task list — all `[x]` items were already checked by dispatches 1-2; this
dispatch's work (settling the residual) was itself the item dispatch 2 flagged as remaining. The
one deviation from dispatch 2's *suggested* next step: this dispatch did NOT inspect
`cs5_completeness`'s canonical-model construction, because the calculus-intrinsic argument (from
`Deduction.lean` alone) already settles the reachability question more directly and more
strongly (it holds regardless of what any specific caller constructs). This is noted, not
silently substituted — the alternative route was recognized as unnecessary work, not skipped due
to difficulty.
