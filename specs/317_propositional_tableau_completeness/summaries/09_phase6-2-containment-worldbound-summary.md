# Phase 6.2: Branch-Universe Containment and World-Bound Continuation

**Task**: 317 (Propositional Tableau Completeness) | **Session**: sess_1783962327_d9c0b3

## Scope

Orchestrator dispatch to complete Phase 6 in full by closing its one deferred deliverable
(`intExpandBranches_world_bound`) plus the load-bearing containment fact needed by Phase 10.
Territory: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` only.

## Commit 1 (`bb4ffa3c`): branch-universe containment — COMPLETE

Landed the full branch-universe containment infrastructure, mirroring Modal-K's
`FmpMeasure.lean:266-754` subformula-closure development adapted to the simpler propositional
connective set (`imp`/`and`/`or`, one world-creating rule vs. Modal-K's box/diamond set with
two fresh-world-minting rules):

- `intSubfmls_self_mem`, `intSubfmls_trans` (private) — subformula-list infrastructure.
- `mem_intUniverse_of[']`, `intUniverse_mem_formula`, `intUniverse_mem_label` (private) —
  constructor/extraction lemmas for `intUniverse` membership.
- `intTImpRule_outputs_subset`, `applyAllTImpRules_subset`, `applyPersistenceFixpoint_subset`
  (private) — containment for the persistent `T(φ→ψ)` rule and its fixpoint iteration (no
  world-bound hypothesis needed, since persistence never mints a fresh label).
- **`intApplyRuleFull_outputs_subset`** (public, the headline deliverable) — step-level
  containment dispatch covering all 5 `intApplyRuleFull` arms: `T∧`/`F∨` (ALPHA), `F∧`/`T∨`
  (BETA), `F→` (world-creating, consumes a `nextWorld ≤ φ0.complexity+1` hypothesis).

This is exactly the `hb : ∀ x ∈ bh, x ∈ intUniverse φ0` hypothesis that
`intExpMeasure_step_lt`/`_branch` (landed Phase 7/7.2) already take as an assumption. Phase 10
can now discharge `hb` inductively over `intExpandBranches`'s `go` recursion by citing this
lemma (plus `applyPersistenceFixpoint_subset` for the pre-step persistence fixpoint) at each
step, rather than re-deriving containment from scratch.

Sorry-free, ~250 lines, axiom-clean (`#print axioms` → `[propext, Quot.sound]` only).

## Commit 2 (`015f81c1`): world-bound combinatorial core — supporting lemma landed

Landed `isImpShaped` and `intSubfmls_impCount_le`: the number of `.imp`-node *positions* (not
distinct values — `intSubfmls` is a raw, non-deduplicating list) in `intSubfmls φ` is at most
`φ.complexity`. Sorry-free, axiom-clean.

## `intExpandBranches_world_bound` — NOT landed, precise continuation

The full lemma (`(b.map (·.label)).eraseDups.length ≤ φ.complexity + 1`) remains open. This
dispatch conducted a genuine, thorough mathematical investigation (not a shallow deflection)
that supersedes the prior dispatch's vaguer "occurrence-tracking, comparable to Phase 7" note
with a precise, verified mechanism:

1. **The naive argument is wrong.** A simple "one world per syntactic occurrence + depth bound"
   argument fails because `F∨` (`.neg, .or`) is `.linearResult` — an ALPHA (non-branching) rule
   (`Rules.lean:260`). Both `F(φ)@l` and `F(ψ)@l` land on the *same* branch, so a single world
   can accumulate multiple independent `F`-imp obligations (e.g. from `(a→b) ∨ (c→d)`), each
   capable of independently firing to create a *sibling* world. The bound needs a width-and-depth
   argument, not depth alone.

2. **The correct mechanism** (verified directly against `Rules.lean`): `posFormulasAt`,
   `propagatePersistence`, and `intTImpRule` are all `.pos`-only (lines 126, 139–141, 174–186).
   F-signed (negative) formulas *never* propagate across worlds via persistence. So every
   world's F-signed content is exactly the decomposition closure of that world's own single
   "obligation" formula (`φ0` at world 0; the consequent `ψ` placed by whichever `F(φ→ψ)` rule
   created any other world). Since decomposition never duplicates a tree position into two
   lineage branches within one completed branch (BETA picks one child per split; ALPHA keeps
   both but at the *same* world, not a new one), the map `(world created) ↦ (the .imp
   tree-position of φ0 whose firing created it)` is injective into φ0's `.imp`-node positions.
   Combined with `intSubfmls_impCount_le`, this gives `(worlds created) ≤ φ.complexity`, hence
   `eraseDups.length ≤ φ.complexity + 1` — exactly the target bound.

3. **Why this was not force-fit into this dispatch.** Formalizing the injection requires a new
   ghost/positional-tracking invariant threaded through a full top-level induction mirroring
   `Soundness.lean`'s `intExpandBranches_closed_unsat` (~700 lines, `Soundness.lean:1039-1714`)
   — this is genuinely new mathematics for the intuitionistic calculus, *not* a port of any
   Modal-K lemma (Modal-K's own `modalWorldBound` is exponential and never needed this
   argument). Estimated ~500-800 lines, exceeding the ~400-line H8 single-dispatch threshold.

See `.orchestrator-handoff.json`'s `blockers[0].recommended_strategy` for the concrete
next-dispatch plan.

## Verification

- `lake build` (full, 3189/3189 jobs) — GREEN.
- `lake exe checkInitImports` — pass.
- `lake exe lint-style` on the touched file — pass.
- `lake test` — full `CslibTests` suite GREEN.
- Sorry count: 4 task-317 inventory sorries unchanged at their exact original locations
  (`Scheme.lean:535`, `Scheme.lean:1388`, `Completeness.lean:133`,
  `Minimal/Completeness.lean:125`); repo-wide sorry count 118, unchanged.
- Axioms: `#print axioms` on both new headline lemmas (`intApplyRuleFull_outputs_subset`,
  `intSubfmls_impCount_le`) shows only `[propext, Quot.sound]` — no new axioms, no `sorryAx`.
- No vacuous definitions introduced.

## Plan Deviations

- The plan's Phase 6 checklist originally listed `intExpandBranches_world_bound` as a single
  deferred item. This dispatch split the work into the containment fact (COMPLETE) and the
  world bound (still open), since the orchestrator's own dispatch brief characterized
  containment as the "load-bearing" fact (report 07 line 143) distinct from the world bound.
  The plan file's Phase 6 section has been updated to reflect this split and the precise
  continuation.
- Per the orchestrator's explicit instruction, this dispatch did NOT proceed to Phase 9 despite
  Phase 9 being independently actionable (does not depend on the world bound).

## Files Touched

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (only file edited; territory
  contract honored — `Expansion.lean`, `Rules.lean`, `FmpMeasure.lean`, `Measure.lean`,
  `Completeness.lean`, `Soundness.lean` read-only, untouched).
- `specs/317_propositional_tableau_completeness/plans/06_route-a-frame-plumbing.md` (Phase 6
  section updated).
- `specs/317_propositional_tableau_completeness/.orchestrator-handoff.json` (overwritten).
- `specs/317_propositional_tableau_completeness/.return-meta.json` (overwritten).

## Commits

- `bb4ffa3c` — task 317 phase 6.2: branch-universe containment (discharges step_lt hb)
- `015f81c1` — task 317 phase 6.2: intSubfmls_impCount_le (world-bound combinatorial core)
