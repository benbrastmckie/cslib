# Research Report: Task 317 — Wave A Atomic De-Risk (Verified Against Live Tree)

- **Task**: 317 `propositional_tableau_completeness`
- **Session**: sess_1783922075_911857_317r
- **Agent**: cslib-research-hard-agent
- **Date**: 2026-07-12
- **Baseline commit**: `6e24520d` (edge-accessibility monotonicity infrastructure, green)
- **CRITICAL CONTEXT**: the working tree contains substantial UNCOMMITTED Wave A progress, and
  agent `t317-impl-1` was ACTIVELY editing `Scheme.lean` during this research (diff hunk offsets
  shifted between successive `git diff` calls). Everything below was verified against the live
  file + a fresh scoped `lake build` snapshot. Line numbers are as of that snapshot and will
  drift. **R7 single-writer**: do NOT dispatch a second writer to these files; this report is
  input for t317-impl-1 (or its successor after the WIP is reconciled), not for a parallel agent.

## Executive Verdict (Go/No-Go)

**GO.** Wave A is closable as specified, with NO design change needed. Roughly 80% of Wave A is
already implemented in the uncommitted working tree and the design deviation it makes from the
handoff document (companion predicate `IFimpAccess` instead of `edges`-as-field-of-
`IBranchSaturation`) is sound and strictly LOWER-ripple than the handoff design (see §Design
Deviation). The verified remaining work is: **one 8-line fix to `tableau_complete`
(Phase 4, Scheme.lean), three-lemma mirrors in each of the two Completeness files (Phase 3),
and ~10 mechanical lint-hygiene sites** — then one atomic green commit with exactly the four
inventory sorries preserved.

## Verified Current State (fresh scoped-build snapshot)

`lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
Cslib...Intuitionistic.Completeness Cslib...Minimal.Completeness` at snapshot time:

- **2 errors remained** (both since partially addressed by the in-flight implementer — re-verify
  at execution time):
  1. `Scheme.lean:505: Unknown identifier IFimpAccess` — FIXED in live tree: `IFimpAccess` is now
     a **public** `def` at `Scheme.lean:433`, declared ahead of `truthLemma`, with a docstring
     recording the load-bearing fact: *under the new `module` system, a `private` declaration
     cannot appear in a `public` lemma's stated type* (this is exactly why Phase 3's corollaries
     also need it public).
  2. `Scheme.lean:1813: application type mismatch` in `tableau_complete` — STILL OPEN. This is
     the single remaining Phase 4 code change (exact fix in §Step 1 below).
- **Sorry inventory: exactly 4**, verified by grep on the live tree:
  `Scheme.lean:533` (truthLemma T-imp case), `Scheme.lean:1384` (fuel-0 base of
  `intExpandBranches_openBranch_sat`), `Completeness.lean:113`, `Minimal/Completeness.lean:110`.
- **Already DONE in the working tree** (verified line-by-line, do not redo):
  - `truthLemma` re-thread (`Scheme.lean:502-569`): signature is now
    `truthLemma (S) (b) (edges : IEdges) (hopen) (hsat : IBranchSaturation Atom b)
    (hfimp : IFimpAccess edges b) (φ) (w)` with `letI : Preorder Nat := intAccessPreorder edges`
    in BOTH the statement (before the `:=`-conclusion, valid Lean 4) and the proof preamble.
    F-imp case closed via `hfimp` + `intAccessPreorder_le_of_isAccessible` (line 539);
    atom/bot/and/or cases re-proved; T-imp case is the preserved sorry (533).
  - `intStepBranch_linear_preserves` / `intStepBranch_branch_preserves`: both carry the new
    `(hACC : IExpandedAccessConsistent edges b e)` hypothesis and a third conclusion conjunct;
    the `.neg,.imp` world-creation case supplies `isAccessible_one_step` over
    `edges ++ [(nw, l)]`, all other cases carry via `sfAccessSat_mono`/`sfAccessSat_edges_mono`.
  - The outer `intExpandBranches_openBranch_sat` induction: **both call sites the previous
    discarded WIP missed are updated** — (i) the `linearResult` arm now calls
    `intStepBranch_linear_preserves hIC_bPers hLB_bPers hACC_bPers hstep` (3 hyps + hstep,
    positional order preserved), (ii) the `branchingResult` arm mirrors it, (iii) the Option-A
    dedup-reuse arm consumes `intFImpReuseWitness?_spec`'s previously-discarded `hacc` conjunct
    to build `hACC_reuse`. `IAllAccessConsistent` is threaded through the `go` helper's `key`
    statement (two extra hypotheses: pending + done), with `IAllAccessConsistent_append`/
    `IAllAccessConsistent_map` at each re-establishment point. Return type is now
    `∃ edges : IEdges, IBranchSaturation Atom b ∧ IFimpAccess edges b`.
  - `IExpandedAccessConsistent_sat` (`Scheme.lean:~1326`): extracts `IFimpAccess edges b` from
    `intStepBranch b e nw = none`, mirroring `IExpandedConsistent_sat`.
  - `openBranch_countermodel` (`Scheme.lean:1755-1781`): conclusion is the Postmortem-5
    existential `∃ edges : IEdges, ¬ @IForces Nat Atom (intAccessPreorder edges)
    (intExtractValuation b) (S.modelBot b) 0 φ`; proof ends
    `exact ⟨edges, (truthLemma S b edges hopen hsat hfimp φ 0).2 hFmem⟩`. This statement
    ELABORATED CLEANLY in the build snapshot (its only failure was transitive, via the then-
    broken `truthLemma`), so the `@IForces Nat Atom (intAccessPreorder edges)` explicit-instance
    form is verified syntax.

## Design Deviation From the Handoff (assessed: KEEP)

The handoff (`handoffs/01_phase1-continuation.md`) prescribed `edges` as a FIELD of
`IBranchSaturation` with `sat_fimp` restated over `isAccessible`. The in-flight WIP instead
keeps `IBranchSaturation` **byte-identical** (numeric `sat_fimp` untouched, per the plan's
Preserved Assets table) and carries the accessibility upgrade as a separate public predicate
`IFimpAccess edges b`, conjoined in `intExpandBranches_openBranch_sat`'s existential and taken
as an extra hypothesis by `truthLemma`. This is equivalent in strength for the F-imp case and
strictly less invasive: `IExpandedConsistent_sat` and every existing `IBranchSaturation`
consumer stay untouched, and the "arity never changes" goal of the handoff design is achieved
even more directly. **Recommendation: do not convert to the field design; finish Wave A on the
companion-predicate design.** (Adversarially checked in §H4 — no consumer needs `sat_fimp`'s
numeric clause upgraded in place; the only consumer of the accessibility fact is `truthLemma`'s
F-imp case, which now receives `hfimp`.)

## Verified Remaining Implementation Sequence (single atomic edit set)

All steps below must land in ONE edit pass before the next `lake build` (the prior break came
from building mid-way through signature ripples). Order given is dependency order within the
edit set.

### Step 1 — `tableau_complete` (Scheme.lean:1805-1813, Phase 4 core)

Current `hvalid` is pinned to the ambient `Nat` instance and `absurd (hvalid b) (...)` no longer
matches the existential edge-framed countermodel. Replace with:

```lean
theorem tableau_complete (S : IntMinScheme Atom) (φ : Proposition Atom)
    (hvalid : ∀ (b : IBranch Atom) (edges : IEdges),
      @IForces Nat Atom (intAccessPreorder edges)
        (intExtractValuation b) (S.modelBot b) 0 φ) :
    intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
        (2 ^ (2 * φ.complexity + 2)) S.closurePred = .closed := by
  by_contra hne
  cases hresult : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]]
      (2 ^ (2 * φ.complexity + 2)) S.closurePred with
  | closed => exact hne hresult
  | openBranch b =>
    obtain ⟨edges, hcm⟩ := openBranch_countermodel S φ b hresult
    exact absurd (hvalid b edges) hcm
```

Rationale: quantifying `hvalid` over ALL edge sets is the deferred-monotonicity bridge shape —
callers eventually discharge it from `IValid`/`MValid` (which ∀-quantify every preorder,
`Kripke.lean:145-158`, so `Preorder Nat := intAccessPreorder edges` instantiates directly)
ONCE `intExtractValuation` upward-closure along `intAccessPreorder edges` is available
(Phase 10; the STOP-gate blocker documented at `Scheme.lean:440-479`). Consumer audit
(verified by grep over `Cslib/` + `CslibTests/`): `tableau_complete` has exactly two callers —
`Completeness.lean:108` and `Minimal/Completeness.lean:106` — both updated in Step 3/4. The
public `*Tableau_complete` types stay byte-stable, so `DecisionProcedure.lean:99,112` (int) and
`Minimal/DecisionProcedure.lean:108,121` are untouched (re-verified at live HEAD).

Note on plan v6 Phase 4's `private _intForcing_at_edge_frame` bridge: NOT required for the
atomic green landing (the direct `hvalid` reshape above preserves the sorry count at the same
two sites). If added later as Phase-10 prep, do not use a leading-underscore name (trips the
`defsWithUnderscore` lint).

### Step 2 — `Intuitionistic/Completeness.lean` (Phase 3, three lemmas)

```lean
lemma intTruthLemma (b : IBranch Atom) (edges : IEdges)
    (hopen : isIntuitionisticallyClosed b = false)
    (hsat : IBranchSaturation Atom b)
    (hfimp : IFimpAccess edges b)
    (φ : Proposition Atom) (w : Nat) :
    letI : Preorder Nat := intAccessPreorder edges
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) →
      IForces (intExtractValuation b) intBotForces w φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) →
      ¬ IForces (intExtractValuation b) intBotForces w φ) :=
  truthLemma intScheme b edges hopen hsat hfimp φ w
```

The `letI` in the statement zeta-expands to the same elaborated type as `truthLemma`'s own
`letI` statement, so term-mode delegation type-checks (both sides pin the identical instance).
`intBotForces` vs `intScheme.modelBot b` and `isIntuitionisticallyClosed` vs
`intScheme.closurePred` unify by defeq exactly as the current (HEAD-green) delegation already
proves. Fallback if the explicit-instance form resists the defeq: state the conclusion with
`(intScheme.modelBot b)` instead of `intBotForces` (docstring can note the equality).

```lean
lemma intuitionisticOpenBranch_countermodel {b : IBranch Atom} (φ : Proposition Atom)
    (h : intuitionisticTableau φ = .openBranch b) :
    ∃ edges : IEdges,
      ¬ @IForces Nat Atom (intAccessPreorder edges)
        (intExtractValuation b) intBotForces 0 φ :=
  openBranch_countermodel intScheme φ b h
```

(No live code consumer — verified by grep: `DecisionProcedure.lean` mentions it in docstrings
only. Free to restate.)

```lean
theorem intuitionisticTableau_complete (φ : Proposition Atom)
    (h : IValid φ) : intuitionisticTableau φ = .closed := by
  apply tableau_complete intScheme
  intro _b _edges
  -- Task 317 phase 10: IValid → forcing at the intAccessPreorder frame; pending
  -- intExtractValuation upward-closure along intAccessPreorder (STOP-gate, Scheme.lean).
  sorry
```

Same sorry, same site (count preserved); the goal under the sorry becomes
`@IForces Nat Atom (intAccessPreorder _edges) (intExtractValuation _b)
(intScheme.modelBot _b) 0 φ` — the correctly-shaped Phase-10 obligation.

### Step 3 — `Minimal/Completeness.lean` (Phase 3 mirror)

Identical shape with `minScheme` / `isMinimallyClosed` / `minBranchBotForces b` / `MValid` /
`minimalTableau`; `minTruthLemma` gains `(edges) (hfimp)` + `letI` conclusion, delegating
`truthLemma minScheme b edges hopen hsat hfimp φ w`; `minOpenBranch_countermodel` gets the
existential conclusion; `minimalTableau_complete` gets `intro _b _edges` before its (preserved)
sorry. Note the Phase-10 discharge here will additionally need `minBranchBotForces` upward
closure — record in the sorry comment.

### Step 4 — Lint hygiene introduced by the WIP (same commit; all mechanical)

From the build snapshot (line numbers will have drifted — re-run the scoped build to refresh):

| Site (snapshot) | Warning | Fix |
|---|---|---|
| `Scheme.lean:802` `IExpandedAccessConsistent_edges_mono` | unusedSectionVars `[Hashable Atom]` | prepend `omit [Hashable Atom] in` |
| `Scheme.lean:1326` `IExpandedAccessConsistent_sat` | unusedSectionVars `[Hashable Atom]` | prepend `omit [Hashable Atom] in` |
| `Scheme.lean:1005,1034,1062,1064` | `show` changed the goal | replace `show X` with `change X` (both are defeq-rewrites; `change` is the lint-sanctioned one) |
| `Scheme.lean:724,824` | unused simp argument | drop the named unused simp arg |
| `Scheme.lean:776,788` | `tac1 <;> tac2` where `;` suffices | use `(tac1; tac2)` |

(Pre-existing warnings in `Soundness.lean`/`Expansion.lean`/`Minimal/Soundness.lean` are NOT
Wave A's — leave them; touching `Soundness.lean` violates the task-316 territory boundary.)

### Step 5 — Verification + commit gate

1. `lake build` the three scoped targets; expect green with exactly 4 `declaration uses sorry`
   warnings (Scheme×2, Completeness×1, Minimal×1) and none of Step 4's warnings.
2. `grep -n "^\s*sorry"` over the four files: exactly 4 hits.
3. `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.DecisionProcedure
   Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` (blast-radius reconfirmation;
   public types byte-stable so these must be no-op green).
4. Single commit: `task 317 phases 1-4: land Wave A — truthLemma/countermodel/complete over
   intAccessPreorder edge frame (atomic)`.

## The `Hashable Atom` Resolution (deliverable 2, verified)

The discarded WIP's "stray `Hashable Atom` instance-resolution failure at line 1037" does NOT
recur in the current WIP: `intStepBranch_linear_preserves` and `intStepBranch_branch_preserves`
are both declared under `omit [Hashable Atom] in` (as are all their `sfAccessSat*` dependencies)
and both elaborate cleanly in the snapshot build. The operative rule, verified across the 20+
`omit [Hashable Atom] in` sites in the live file:

- Any lemma whose statement mentions `IBranchSaturation` (which carries `[Hashable Atom]` in its
  type) or `intFImpReuseWitness?` machinery MUST NOT omit it — e.g. `truthLemma`,
  `intExpandBranches_openBranch_sat`, `openBranch_countermodel`, `tableau_complete` correctly
  keep it.
- Pure list-membership / `isAccessible` / `sfAccessSat` / invariant-threading lemmas take
  `omit [Hashable Atom] in` — the `unusedSectionVars` linter is the oracle: add the omit exactly
  where it warns, never preemptively. The two current warn-sites are listed in Step 4.
- No `haveI`/`letI` for `Hashable` is needed anywhere: the failure mode was omitted-vs-needed
  mismatch, not a missing instance.

## Sorry-by-Sorry Disposition (deliverable 3)

| Sorry (live) | Closed by Wave A? | Disposition |
|---|---|---|
| `Scheme.lean:533` truthLemma T-imp | **No** (by design) | Preserved, now stated over the edge frame. Closes in Phase 9 via `sat_timp` + fuel machinery. |
| `Scheme.lean:1384` fuel-0 base of `intExpandBranches_openBranch_sat` | **No** | Phase 10 (`intExpMeasure` fuel-sufficiency). |
| `Completeness.lean:113` IValid bridge | **No** | Goal reshaped to `∀ edges` edge-frame forcing (Step 2). Discharge = Phase 10: instantiate `IValid φ` (`Kripke.lean:145`) at `Preorder Nat := intAccessPreorder edges` + `intExtractValuation` upward-closure (STOP-gate blocker, `Scheme.lean:440-479` — entangled with persistence fixpoint/fuel; genuinely NOT closable in Wave A without new mathematics). |
| `Minimal/Completeness.lean:110` MValid bridge | **No** | Same, via `MValid` (`Kripke.lean:153`) + additionally `minBranchBotForces` upward-closure. |

**Wave A closes zero sorries and creates zero sorries — it is frame plumbing that reshapes
sorries 3-4 into their dischargeable form.** This matches plan v6 exactly ("No sorry closed"
on Phases 1-4).

Grounded lemma inventory used by the remaining steps (all verified present: local grep + green
elaboration in the snapshot build): `intAccessPreorder_le_of_isAccessible` (Scheme.lean:321),
`intAccessPreorder_mono_append` (:422), `isAccessible_one_step`, `isAccessible_append_mono`,
`sfAccessSat_mono`, `sfAccessSat_edges_mono`, `IExpandedAccessConsistent_mono`,
`IAllAccessConsistent_append`, `IAllAccessConsistent_map`, `IExpandedAccessConsistent_sat`,
`intFImpReuseWitness?_spec` (Expansion.lean:300-327, `hacc` first conjunct), and Mathlib's
`Relation.ReflTransGen.single/.mono/.trans` (all already load-bearing in HEAD-green code).

## Source-to-Implementation Mapping (H3, Tier 1)

| Source Claim | BibKey | Lean Target | Translation Notes |
|---|---|---|---|
| Tableau completeness for intuitionistic logic, Ch. 4 (open saturated branch ⇒ Kripke countermodel) | `Fitting1983` (verified: `references.bib:203`) | `Cslib.Logic.PL.openBranch_countermodel`, `truthLemma` | Fitting's countermodel worlds are the branch's own labels ordered by the tableau's ACCESSIBILITY relation, not by ambient ℕ-≤ — Route (a) is the faithful transcription; the prior ambient-≤ frame was the report-08 "phantom worlds" infidelity. |
| Truth lemma by induction on formula, F(φ→ψ) case uses the created successor world | `Fitting1983` | `truthLemma` F-imp case (Scheme.lean:532-539) | `IFimpAccess` is the formalization of "the witness world is a genuine tableau successor"; `Relation.ReflTransGen` closure over one-step edges soundly over-approximates Fitting's tree order. |
| Persistence (Prop. 2.1) | `ChagrovZakharyaschev1997` (verified present in `references.bib`, cited at `Kripke.lean:118`) | `iforces_persistence` | Already sorry-free; Phase 10 needs the analogous fact for `intExtractValuation` along `intAccessPreorder` (the STOP-gate). |

## Adversarial Self-Verification (H4)

1. **"The remaining work is just Step 1 + mirrors — could Step 1's hvalid reshape be wrong?"**
   Challenged by re-deriving the absurdum: `openBranch_countermodel` yields `∃ edges, ¬P edges`;
   refuting it needs `P edges` for the SPECIFIC extracted edges, hence hvalid must be
   ∀-quantified over edges. Verified no caller of `tableau_complete` exists outside the two
   corollary files (grep, live tree), so the internal reshape is contract-safe. CONFIRMED.
2. **Most likely `lake build` failure point**: the term-mode delegation in `intTruthLemma`
   (letI-statement vs letI-statement unification) and the `intBotForces` defeq under the now-
   explicit `@IForces` instance. Both are defeq-plausible but not build-verified (Completeness
   files not yet edited). **Fallback (pre-planned, cheap)**: (a) switch delegations from
   term-mode `:=` to tactic `exact`; (b) if still resistant, state corollary conclusions with
   `intScheme.modelBot b` / `minScheme.modelBot b` verbatim (guaranteed unifiable — it is
   literally `truthLemma`'s own conclusion instance) and keep `intBotForces` only in docstrings.
   Neither fallback changes any public consumer.
3. **"Does anything still need the handoff's edges-as-field design?"** Challenged each
   `IBranchSaturation` consumer: `truthLemma` (gets `hfimp` separately), `IExpandedConsistent_sat`
   (unchanged, good), the corollaries (take `hsat`+`hfimp` as separate hypotheses). No consumer
   needs a bundled field. The deviation also dodges the handoff's own identified risk (rebuilding
   `IExpandedConsistent_sat`'s `refine { edges := ..., ... }`). CONFIRMED — keep deviation.
4. **"Could the `letI`-in-statement pattern leak the wrong instance downstream?"** The one
   consumer chain is `truthLemma → openBranch_countermodel → tableau_complete → *Tableau_complete`;
   from `openBranch_countermodel` outward the instance is EXPLICIT (`@IForces ... (intAccessPreorder
   edges)`), never inferred, per R1 (two non-defeq `Preorder Nat` instances). The snapshot build
   already elaborated `openBranch_countermodel`'s statement. CONFIRMED.
5. **"Is the 4-sorry count really stable?"** The reshape moves no sorry and adds none; but note
   `intro _b _edges` inside the corollary sorries changes the SORRY'S GOAL — flagged so the
   post-commit sorry inventory records the new goal shapes, avoiding a false churn signal.
6. **Residual uncertainty (medium confidence)**: the build snapshot is of a MOVING tree;
   t317-impl-1 may have already implemented some of Steps 1-4 by the time this report is read.
   The executor MUST re-run the scoped build first and diff against this report's state rather
   than blindly re-applying edits. This is a process risk, not a design risk.
7. **Analysis-only check**: report contains exact drop-in code for every remaining edit, a
   verification gate, and a commit message — actionable direction present. PASS.

## Rate-Limit / Tool Fallback Record

No rate-limited search tools were needed: all lemma existence checks were resolved by local
grep + the two scoped `lake build` runs (the strongest possible verification). Blocked tools
(`lean_diagnostic_messages`, `lean_file_outline`) were not used; build diagnostics came from
`lake build` output per the cslib rules.

## Recommended Next Action

Have `t317-impl-1` (single writer) finish Steps 1-5 as one edit pass and commit Wave A
atomically. After the commit: update plan v6 Phases 1-4 to [COMPLETED], refresh the sorry
inventory with the reshaped goals, and only then open Wave B (Phase 5+, fuel raise — separate
files, separate dispatch).
