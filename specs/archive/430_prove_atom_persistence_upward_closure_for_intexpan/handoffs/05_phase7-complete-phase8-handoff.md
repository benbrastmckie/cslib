# Handoff: Phases 5-7 Complete, Continuation Notes for Phase 8

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Plan**: `plans/06_gate-b2-then-origin-tracing-export.md`
- **Status**: PARTIAL (not BLOCKED) — Phases 1-7 complete, committed, full `lake build` green.
  Phases 8-14 remain. This is a natural checkpoint, not a stall: Phase 8 is the next
  reasonably-sized unit of work, and this handoff exists so it starts with the exact design
  question already resolved rather than re-derived.

## What landed this dispatch (commits `a6b0d14b`, `0ef99cd4`)

- **Phase 5 (Gate B2)**: verdict **PASS**, residual risk explicitly carried forward. Eight
  `φ0` candidates tested in `scratch/BetaSplitProbe.lean`; three genuinely exercised
  ancestor-directed reuse with a live shared disjunction; zero violations found. Full verdict
  and the analytical explanation for why the mechanism resists accidental construction: `handoffs/
  04_gate-b2-verdict.md`.
- **Phase 6 (statement-shape fix)**: `openBranch_countermodel`'s conclusion now carries
  `intExtractValuation b`'s upward-closure along the augmented frame as an explicit conjunct
  (a new, deliberately-deferred `sorry`, `Scheme.lean:7412` at time of writing).
  `tableau_complete`'s `hvalid` accepts it as a hypothesis; `tableau_complete` itself has zero
  `sorry` in its own proof body. Both `Completeness.lean` files updated to match; DP-3/DP-4
  re-annotated (still `sorry`, deliberately — see the plan's Phase 6 "Why DP-3/DP-4 are
  deliberately left sorry" note, which explains why closing them now via a still-unproven
  dependency would be laundering, not progress).
- **Phase 7 (raw-edge export)**: `intExpandBranches_openBranch_sat`'s conclusion gained a
  SECOND existential (`rawEdges`, distinct from the augmented `edges`) plus `IPosPersistRaw
  rawEdges b`. Only the genuine terminal case (`case4`, `intStepBranch bPers e nw = none`)
  needed new work, composed directly from Phase 4's landed `applyPersistenceFixpoint_
  copy_complete`. The sole consumer (`openBranch_countermodel`) updated. Zero new sorries.

**Verification state**: `lake build` (full project, 3311 jobs) green. Exactly 4 sorries in this
task's scope: DP-5 (`truthLemma`'s T-imp case, `Scheme.lean:671`), the Phase-6-introduced
`openBranch_countermodel` conjunct (`Scheme.lean:7412`), DP-3 (`Completeness.lean:137`), DP-4
(`Minimal/Completeness.lean:133`). DP-2 (`intFreshMint_preserves_nw`) confirmed untouched by
content and by `git diff` (task 585's territory). `Soundness.lean` (both files) untouched.

## Why this dispatch stops before Phase 8

Phase 8's own text ("Thread `posFormulasAt bPers w ⊆ posFormulasAt bPers x` as a monotone
planted fact per recorded loop-back edge, surviving to the final branch") undersells a real
subtlety worth resolving BEFORE writing Lean, so the next dispatch does not have to re-derive
it under time pressure:

**The exported fact must be about a FIXED, NAMED finite set of formulas (`Sfor` at reuse time),
NOT a general schema.** A tempting first design is a companion invariant of the shape

```lean
private def IAllReuseContain (bs : List (IBranch Atom)) (augEdges : List IEdges) : Prop :=
  match bs, augEdges with
  | [], [] => True
  | b :: bs', augH :: augT' =>
      (∀ x l : Nat, (x, l) ∈ augH → posFormulasAt b l ⊆ posFormulasAt b x) ∧
      IAllReuseContain bs' augT'
  | _, _ => False
```

**This is NOT preserved by the induction as stated, and proving it would BE Phase 9, not
Phase 8.** The reason: `posFormulasAt b l ⊆ posFormulasAt b x` growing correctly under branch
extension requires EVERYTHING that later arrives at `l` to also arrive at `x` — which is
exactly Phase 9's "post-reuse closure lemma," described in the plan as "the genuinely large
piece." A companion invariant stated as "holds of the CURRENT branch at every step" would
either (a) be false as an inductive invariant (nothing forces it to be preserved by
inconsistent-with-monotonicity growth at `l` alone), or (b) silently require Phase 9's full
result to prove it, defeating the point of splitting Phase 8 out as a smaller, prior step.

**The correct, smaller Phase 8 scope**: export, per recorded loop-back edge `(x, l)`, the
SPECIFIC finite formula list `Sfor` that `intFImpReuseWitnessAnc?_spec`'s `hcont` conjunct
already established containment for AT REUSE TIME, together with the (easy) fact that BOTH
`T(χ)@l ∈ (branch at reuse time)` for `χ ∈ Sfor` (definitionally, since `Sfor` is exactly
`{φ} ∪ posFormulasAt bPers l` read off `newForms`) AND `T(χ)@x ∈ (branch at reuse time)` for
`χ ∈ Sfor` (from `hcont` itself) SURVIVE to the final branch via ORDINARY branch-append
monotonicity (branches only grow; nothing is ever removed) — this half is genuinely easy and
is the `hmemP`/`IWorldHist_mono`-style pattern used throughout the file already. Concretely,
the companion invariant should carry, per branch, a LIST of RECORDS `⟨x, l, Sfor, hcont_proof⟩`
(or equivalently a dependent existential), not a bare `(x, l) ∈ augH` membership check — the
formula LIST itself must be part of what's threaded, since it is what makes the exported fact
meaningful and FINITE rather than an unprovable universal claim.

**A cleaner encoding to consider first** (worth trying before the record-list design above):
state the companion invariant as an EXISTENTIAL over a SNAPSHOT branch rather than a bare set
membership:

```lean
private def IAllReuseContain (bs : List (IBranch Atom)) (augEdges : List IEdges) : Prop :=
  match bs, augEdges with
  | [], [] => True
  | b :: bs', augH :: augT' =>
      (∀ x l : Nat, (x, l) ∈ augH →
        ∃ bSnap : IBranch Atom, (∀ y ∈ bSnap, y ∈ b) ∧
          (∀ χ : Proposition Atom, (⟨.pos, χ, l⟩ : ISF Atom) ∈ bSnap →
            (⟨.pos, χ, x⟩ : ISF Atom) ∈ bSnap)) ∧
      IAllReuseContain bs' augT'
  | _, _ => False
```

i.e. "there EXISTS a branch snapshot, contained in the current branch, at which the
containment held" — this is preserved automatically under branch growth (the SAME snapshot
witness works for any later, larger branch, since `∀ y ∈ bSnap, y ∈ b` only needs `b` to grow),
so THIS shape genuinely is a preserved invariant and is planted exactly once (at the reuse
arm, `bSnap := bPers` at that moment) and carried forward by every other arm via `ih`
unchanged (no re-proof needed at non-planting arms — the SAME existential witness transfers,
only the "contained in" fact needs `List.Sublist`/membership monotonicity, which is the
`hmemP`-style lemma already used everywhere). Compare both encodings' proof burden empirically
(a quick `example` block against the real reuse arm's context, values already in scope at
`Scheme.lean` around what is currently the `case6` reuse arm of `intExpandBranches_openBranch_
sat`'s induction, i.e. the arm containing `intFImpReuseWitnessAnc?_spec hψ hwit`) before
committing to one shape over the other.

## Concrete next steps for Phase 8

1. Pick one of the two encodings above (or a third, if a cleaner one presents itself once
   actually attempted against the real proof context) and confirm it type-checks as a
   STANDALONE `private def`, without yet threading it through the induction.
2. Thread it through `intExpandBranches_openBranch_sat`'s `key` induction exactly as
   `IAllAccessConsistent`/`hACC` is threaded (companion-not-merged: a NEW parameter alongside
   `hACC`, not a field merged into it), with `pendingARC`/`doneARC` parallel lists mirroring
   `pendingAug`/`doneAug`.
3. Every case EXCEPT the reuse arm (`case6` currently, at the time of writing — re-locate by
   content, specifically the arm matching on `intFImpReuseWitnessAnc? bPers edges newForms
   newE = some x`) delegates to `ih` unchanged, exactly as Phase 7 found for `IPosPersistRaw`.
   Confirm this rather than assuming it — re-check by locating every site that extends `augH`
   (same enumeration Phase 8's own Scope Hypothesis calls for).
4. The reuse arm (`case6`) is the ONE arm that plants a new record/existential, using EXACTLY
   the `houtPhi`/`hcont` facts already established there (see `Scheme.lean` around
   `intFImpReuseWitnessAnc?_spec hψ hwit` in that arm — `hcont` is already destructured and
   used locally; Phase 8 EXPORTS it rather than deriving anything new).
5. Extend `intExpandBranches_openBranch_sat`'s conclusion with the new companion fact,
   specialized to the recorded loop-back edges of the FINAL branch, and repair the single
   consumer (`openBranch_countermodel`)'s `obtain` pattern (now 6 components instead of 5).
6. `lean_verify` for axiom cleanliness; confirm zero new sorries (Phase 8 should not need any
   `sorry` — everything it needs is already established at the reuse site, per report 05 §3).

## Do not re-derive

- Handoff 03's Finding 1 (raw-edge terminal fact) — Phase 7 already consumed it.
- Report 05 §2's reuse audit (which declarations are reusable vs. must-build-new) — unchanged.
- The exclusion list (quotient/blocking-frame route, Route C, `≤`-on-ℕ) — still prohibited.
- Gate B2's verdict — Phase 8 does not reopen it; the residual risk it carries forward is
  Phase 9/11's concern, not Phase 8's.

## Files touched this dispatch

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (Phases 6, 7)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` (Phase 6)
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (Phase 6)
- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/BetaSplitProbe.lean` (Phase 5, new)
- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/handoffs/04_gate-b2-verdict.md` (new)
- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/plans/06_gate-b2-then-origin-tracing-export.md`
  (phase markers and outcomes for Phases 5-7)

`git status --short Cslib/ CslibTests/` at the end of this dispatch shows only the three
`Cslib/` files above — no stray writes.
