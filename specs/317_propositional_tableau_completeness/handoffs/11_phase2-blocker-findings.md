# Phase 2 Blocker — Verified Findings (not anticipated by plan v7's sizing)

## Summary

Phase 2 ("Universe/measure invariant — definition and call-site threading") cannot be completed
as scoped (~150-250 lines, 3 hours) because of two compounding, concretely-verified obstacles.
Both are recorded here with the exact evidence; no `sorry`/axiom/vacuous statement was
introduced, and the broken in-progress edit was reverted (`git checkout --`) back to the
Phase-1-committed green state before this handoff was written.

## Finding 1: definition-order dependency (mechanical, but large)

`intExpandBranches_openBranch_sat` is declared at `Scheme.lean:1499` (current HEAD). The plan's
Phase 2 task requires its signature to reference `intUniverse φ0` and
`intExpMeasure (intUniverse φ0) branches expandedSets`. Both `intUniverse` (`:2056`) and
`intExpMeasure` (`:2382`), along with their supporting definitions (`intSubfmls`, `intWork`,
`intUniverse_length_le`, etc.), are declared **after** `intExpandBranches_openBranch_sat` and
after `openBranch_countermodel`/`tableau_complete` (the "Fixed Finite Universe and Counting
Work" section header sits at `:1940`, immediately after `tableau_complete`). Verified directly:
adding `(φ0 : Proposition Atom) (hUniv : ∀ b1 ∈ branches, ∀ x ∈ b1, x ∈ intUniverse φ0)
(hMeasure : intExpMeasure (intUniverse φ0) branches expandedSets ≤ fuel)` to
`intExpandBranches_openBranch_sat`'s signature and rebuilding produces:
```
error: ... Function expected at intUniverse but this term has type ?m.1
error: ... Function expected at intExpMeasure but this term has type ?m.2
```
i.e. genuine forward-reference errors, not a typo. Fixing this requires relocating the entire
`intUniverse`/`intExpMeasure`/`intSubfmls`/`intWork` block (roughly `Scheme.lean:1940-2900`,
~950 lines of already-landed, sorry-free Preserved-Assets code) to before line 1499. This is
mechanically safe in principle (that block is self-contained; it does not depend on
`intExpandBranches_openBranch_sat` or anything declared between 1499 and 1940) but is a
large-footprint reorg of already-landed code, not itself scoped or budgeted by Phase 2, and not
something to do casually mid-phase given R6/R7 (large-file risk, concurrent writers).

## Finding 2: the invariant cannot be maintained across the F-imp world-creating step (the real blocker)

Independent of Finding 1: `induction fuel generalizing branches expandedSets nextWorlds edgeSets
hAC hLen0 hACC` automatically sweeps `hUniv`/`hMeasure` into the generalized/reverted set as soon
as they exist in context and mention `branches`/`expandedSets` (confirmed by the test build: the
`ih` produced after adding these two hypotheses immediately requires proofs of the new
`∀ b1 ∈ (new branches list), ...` and measure obligations at every existing `ih`/`ih_inner` call
site — there is no way to add these hypotheses to the signature and defer their use to a later
phase; Phase 2 and Phase 3 are not actually separable at the Lean level, contrary to the plan's
phase split).

Attempting the real threading (Phase 3's actual content) hits a missing prerequisite. Maintaining
`hUniv` (universe-membership) forward across a step requires, for the world-creating `F(φ→ψ)`
linear-result case, `intApplyRuleFull_outputs_subset`'s hypothesis
`(hnw : nextWorld ≤ φ0.complexity + 1)` (`Scheme.lean:2294`). No lemma in the file establishes
this bound on the running `nextWorld` counter. This is not an oversight on my part — the file
itself documents the gap explicitly, in two places, as a **known, unbuilt** "continuation":

- `Scheme.lean:2025-2038` (docstring above `intSubfmls_impCount_le`): "...This is the key
  combinatorial fact underlying the linear world bound `intExpandBranches_world_bound` (report 07
  §Q4 F5, **continuation**)... Combined with this bound, that injection gives (number of worlds
  created) ≤ φ0.complexity, hence (distinct labels).length ≤ φ0.complexity + 1 — **the target
  bound**." (i.e., `intSubfmls_impCount_le` is only the combinatorial *ingredient*; the actual
  bound theorem is described, not proved.)
- `Scheme.lean:2052-2055` (docstring above `intUniverse`'s definition): "...using the linear
  intuitionistic world bound `φ.complexity + 1` (report 07 §Q4 F5, `intExpandBranches_world_bound`
  (**continuation, see handoff**))..."
- `Scheme.lean:2536-2538` (docstring on `intExpMeasure_step_lt`): explicitly contrasts its own
  `hb` hypothesis with "`intExpandBranches_world_bound` (**a distinct, harder** distinct-label-
  count fact this lemma does not need)" — confirming the measure-decrease lemmas were
  deliberately engineered to avoid needing this fact, but `intApplyRuleFull_outputs_subset`
  (needed to maintain `hUniv`, a *different* invariant Phase 2/3 also requires) was not.

Constructing `intExpandBranches_world_bound` requires a genuinely new argument: an injection from
"worlds created during the expansion so far" into "distinct `.imp`-node positions of φ0's own
parse tree" (using `intSubfmls_impCount_le`'s count bound as the injection's codomain size),
threaded as a fresh invariant through the *same* recursive structure `intExpandBranches_openBranch_sat`
already threads `IAllConsistent`/`IAllAccessConsistent`/`ILabelBound` through. This is comparable
in size to an *additional* phase, not a sub-step of Phase 2's 3-hour budget or Phase 3's 4-hour
budget — matching the plan's own R5 language for Phase 6 ("genuinely open-ended... two research
teammates independently flagged this as under-scoped") but for a *different, undiscovered* gap in
Phases 2/3, not Phase 6.

## What is NOT blocked (a positive finding worth preserving)

Working out the intended zero-case argument (Phase 3's stated hardest part) shows it is actually
straightforward **given** the invariant: `intExpMeasure`'s summand is `3 ^ intWork ...`, which is
`≥ 1` for *every* branch unconditionally (since `3 ^ n ≥ 1` for all `n`). So `intExpMeasure U
branches expandedSets ≤ 0` (fuel = 0) forces `branches = []` directly (a nonempty zipped list
would sum to ≥ 1). And `intExpandBranches branches ... 0 ... = .openBranch b` is only possible
when `branches` is nonempty (`intExpandBranches`'s own fuel-0 case,
`Expansion.lean:369-373`, is `branches.findSome? (...)`, which is `none` — i.e. `.closed`, never
`.openBranch` — on `[]`). So the zero case should close by a short contradiction
(`branches = []` from the measure bound, then `h` is absurd), **not** the more elaborate
"measure = 0 ⟹ e ⊇ intUniverse φ0" argument the plan's Phase 3 text describes. This should be
recorded for whoever picks this back up: the zero case is easy; the succ-case invariant
*maintenance* (specifically the world-creating step) is the real difficulty, and it is a Phase
2/3-blocking prerequisite, not a Phase-3-only concern.

## Recommendation

Re-plan Phases 2-3 (and, transitively, 4-7, all of which depend on the invariant this
infrastructure was meant to supply) as a new round, budgeting explicitly for:
1. Relocating the `intUniverse`/`intExpMeasure` block before `intExpandBranches_openBranch_sat`
   (mechanical, low-risk, but nontrivial line-count).
2. A new `intExpandBranches_world_bound` lemma (or an equivalent invariant that avoids needing
   it), sized as its own phase — this is the load-bearing prerequisite for everything downstream.
3. Only then attempt Phase 2/3's invariant threading, using the (now confirmed easy) zero-case
   argument above.

No code in `Cslib/` was left in a broken state; the only committed changes this dispatch made
are Phase 0 (verification spike, `handoffs/11_phase0-spike-decisions.md`) and Phase 1 (`sat_timp`
field + mechanical discharge, `Scheme.lean`), both green and unaffected by this finding.
