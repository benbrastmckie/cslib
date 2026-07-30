# Handoff: Phase 10 Origin-Tracing — Scoping Analysis and a New Blocker

- **Task**: prove_atom_persistence_upward_closure_for_intexpan
- **Plan**: `plans/06_gate-b2-then-origin-tracing-export.md`, Phase 10
- **Status**: **PARTIAL / [BLOCKED]** — no `Cslib/` writes this dispatch. `git status --short
  Cslib/ CslibTests/` is empty at the end of this dispatch, matching Phase 9's own precedent for
  an honest "cannot close without further groundwork" outcome. This is NOT a regression: the
  `ForestComparable` prerequisite landed last dispatch (commit `7f9031c0`) is untouched and
  reconfirmed stable.
- **Read first**: `handoffs/07_post-reuse-closure-verdict.md`, `handoffs/08_phase9-collapsed-phase10-handoff.md`,
  `handoffs/09_forestcomparable-export-phase10-continuation.md`. This handoff does not repeat
  their content; it extends the analysis with what this dispatch found.

## What this dispatch did

Read the full continuation chain (handoffs 07-09), then spent the dispatch on **design
scoping** for the origin-tracing extension itself (Phase 10's remaining task list: extend
`IWorldHist`'s witnesses, generalize (H3), prove origin-raw-accessibility, retry Phase 9). No
Lean code was written. This section records why, and what was learned that changes the picture
for the next dispatch.

### Scoping the sources of positive content (narrows the invariant, confirmed via direct source reading)

`intApplyRuleFull` (`Rules.lean:250-283`) is the exhaustive list of what can add a `T`-signed
(positive) entry to the branch:

1. `T(φ∧ψ)@l → T(φ)@l, T(ψ)@l` (alpha, same world).
2. `T(φ∨ψ)@l → T(φ)@l` **or** `T(ψ)@l` (beta choice, same world).
3. `F(φ→ψ)@l →` mint fresh `w'`: `T(φ)@w'` (genuine fresh payload) `++ propagatePersistence`
   (copy of `l`'s current positive content to `w'`).
4. `T(φ→ψ)@l →` reflexive branch: `F(φ)@l` **or** `T(ψ)@l` (same world).
5. `intTImpRule`/`applyAllTImpRules` (persistent, cross-world): for `w'` accessible from `w`,
   `T(φ→ψ)@w` + `T(φ)@w'` gives `T(ψ)@w'` (genuinely new content at `w'`, but combining data
   already present at `w` and at `w'` itself).

Handoff 07's "case 1" (decomposition of an already-present-at-reuse-time premise) already
covers sources 4 and 5 **without any origin tracing** — it only needs `ForestComparable` (now
landed) plus `IPosPersistRaw`/`IBranchSaturation.sat_timp`/`no_contradiction`, all landed. This
was previously stated only in prose (handoff 07); it is re-confirmed here against the concrete
rule list, closing off a possible gap (that sources 4/5 might need separate treatment — they do
not). Sources 1 and 2 (alpha/beta decomposition) produce content **at the same world** as their
premise, so they inherit whatever origin their premise had — they do not introduce new
self-origination points either. **This leaves exactly one genuine self-origination source
requiring new tracking: source 3's fresh mint payload `T(φ)@w'`, plus the initial branch's
starting content at world `0`.** This is a real narrowing of Phase 10's scope from "track every
positive formula's history" to "track only mint-payload and initial-content origins, and thread
that tag through the other four sources by inheritance" — smaller than handoffs 07-09 assumed,
and worth recording so the next attempt does not over-build.

### The new finding: origin-tracing alone does not close the residual case

Having scoped the invariant to something buildable (a companion witness, threaded through all
10 cases of the `key` induction, tagging every positive branch entry with a raw-ancestor
self-origination point — mint-payload or initial), this dispatch checked whether landing it
would actually close Phase 9's residual `x < y ≤ l` sub-case (handoff 07's open case: a copy
arrives at `l` from a raw ancestor `y` with `x` strictly between neither, i.e. `x` is a proper
ancestor of `y`, `y` a raw ancestor-or-equal of `l`).

**It does not, by itself.** Tracing `y`'s content back to its true self-origination point `z`
(mint-payload world) gives `isAccessible edges z y = true` (hence `isAccessible edges z l =
true` by transitivity) — but `z` is now compared against `x` via `ForestComparable` exactly as
`y` was, and the SAME two outcomes recur: `z ≤ x` (closes) or `x < z` (`z` itself sits strictly
between `x` and `l` — the same shape as the original problem, one level further back). Since
`z` is by construction a **true** self-origination point (not itself traceable further), this
recursion terminates at `z`, and if `z` lands in the open range, tracing origin does not help —
there is nothing further back to appeal to.

**A concrete scenario showing this is not a vacuous worry.** Suppose `x` fires `F(φ_y → ψ_y)`
and mints a *direct* child `y` (`par y = x`), giving `T(φ_y)@y`, `F(ψ_y)@y`. Since `y` was
minted specifically to witness `x`'s implication failing, `x` itself does **not** carry
`T(φ_y)@x` (nor should it — `x` also carries `F(ψ_y)@x)`` is exactly the reuse-search
condition `¬(forcedAtX.contains ψ)`'s cousin: the point of minting `y` was that `x` does not
already force `ψ_y`, and by consistency `x` cannot force `φ_y` either without needing `sat_timp`
to also force `ψ_y` at `x`, contradicting `F(ψ_y)@x`). Suppose further `y ≤ l` raw (`y` is an
ancestor of some later world `l`), and `l` later reuses `x` (not `y`) as its own loop-back
target. If `T(φ_y)` has, by the time the **final** branch is reached, propagated from `y` down
to `l` (via `IPosPersistRaw`, since the final branch is a genuine `applyAllTImpRules` fixpoint),
then `T(φ_y)@l` holds in the final branch while `T(φ_y)@x` structurally cannot — exactly the
shape the augmented-edge persistence theorem would need to rule out.

### Why this scenario is not obviously prevented, and what actually would prevent it

The reuse check (`intFImpReuseWitnessAnc?`, `Expansion.lean:288-312`) requires, **at
reuse-check time**, `sfor.all (forcedAtX.contains ·)` where `sfor = {φ_l} ∪ posFormulasAt bPers
l` — i.e. `x` must already contain *everything currently at `l`*, including anything `l` has
already received via persistence from `y`. **If** `applyPersistenceFixpoint` has already fully
converged (propagated `φ_y` from `y` to `l`) by the moment `l`'s reuse check runs, `x`'s
containment check would fail on `φ_y` and `x` would never be selected — the scenario above
could not arise via this route. **The gap is that `applyPersistenceFixpoint`'s convergence
before every single rule step is not established as an invariant anywhere in this file.**

This is not a fresh concern invented for this handoff — it is **the same open gap already
recorded, under the name "Gap 1", in the STOP-gate docstring immediately above `IFimpAccess`**
(`Scheme.lean`, the `sat_timp` discharge section, roughly lines 536-650 at time of writing):
*"If that fuel is exhausted before a GENUINE fixpoint of `applyAllTImpRules` is reached, some
accessible world may never receive its copy, and the `sat_timp` disjunction is then genuinely
FALSE for that world."* That note is about a different consumer (`sat_timp`/DP-5's own
`truthLemma` sorry), but the underlying mathematical question — **does the persistence
fixpoint fully converge before every subsequent rule application, given the algorithm's fuel
budget** — is identical. This dispatch's contribution is identifying that **Phase 10's residual
closure and DP-5's "Gap 1" are the same open question**, not two independent gaps. This was not
stated in handoffs 07-09 or in the plan.

**Practical consequence**: building the origin-tracing companion invariant (Phase 10's literal
task-list item) is very likely *necessary but not sufficient* — the recursion above shows it
reduces to, rather than avoids, the fixpoint-completeness question. Landing the companion
invariant without first resolving (or routing around) that question risks a large, sorry-free
partial construction that still cannot close Phase 9's residual lemma, which is exactly the
"duplicated churn" handoffs 08/09 warned against for `ForestComparable` — except here the risk
is structural, not merely a matter of signature placement.

## Why no `Cslib/` code lands this dispatch

Any of the following would violate the plan's explicit prohibitions:
- Building the origin-tracing companion invariant now, when it is very likely insufficient by
  itself (per the finding above) — this would be exactly the "duplicated churn" pattern the
  plan's own discipline forbids, this time on a much larger invariant than `ForestComparable`.
- Landing a version of the residual lemma with the `x < y ≤ l` (or the newly-identified
  fixpoint-timing) case `sorry`'d — **prohibited outright** (no `sorry`, no weakened statement).
- Asserting fixpoint-completeness ("Gap 1") as an unproven hypothesis threaded through the
  conclusion — this would be a **new, unestablished assumption**, not an export, and is exactly
  the kind of unsound shortcut both this task and DP-5's own STOP-gate note explicitly forbid.

## Recommendation for the next dispatch (concrete, not vague)

Two options, not mutually exclusive:

1. **Attempt to establish fixpoint-completeness-before-reuse-check as its own lemma.** If
   `applyPersistenceFixpoint`'s recursion measure genuinely terminates at a true fixpoint given
   the fuel available at any point `intStepBranch` is about to run a world-creating rule (this
   is a **narrower** claim than DP-5's "Gap 1", which asks for convergence w.r.t. *arbitrary*
   accessible worlds broadly — here we only need it for the *specific* accessible pair `(y, l)`
   at the moment of `l`'s own reuse check), it would close BOTH Phase 10's residual case AND
   contribute directly to DP-5's own currently-`sorry`'d gap (`Scheme.lean`'s `truthLemma`
   T-imp case) — a double payoff worth the investment. This is genuine new work, not
   previously attempted by Phases 5-9, and is a natural next research/implementation target.
2. **Before investing in (1), run a Gate-B2-style computational probe** specifically targeting
   the concrete scenario above: construct a `φ0` where (a) a world `x` mints a direct child `y`
   with a fresh antecedent `φ_y` that `x` itself cannot hold, (b) `y` has a raw descendant `l`
   that later reuses `x` (not `y`) as a loop-back target, and (c) check whether the final branch
   ever actually exhibits `T(φ_y)@l ∧ ¬T(φ_y)@x`. A refutation here would trigger the plan's
   sanctioned terminal-deferral contingency (Rollback/Contingency) for DP-3/DP-4/DP-5 — a
   complete and legitimate outcome. A clean PASS across a family of candidates (mirroring Gate
   B2's own methodology) would be strong evidence that the algorithm's actual processing order
   (not yet formalized as an invariant) prevents the bad interleaving, which would then justify
   investing in (1) as a targeted lemma about that processing order specifically, rather than a
   fully general fixpoint-completeness result.
   **This probe was not built this dispatch** — it requires the same kind of `#eval`/`decide`
   harness Gate B2 used (`scratch/BetaSplitProbe.lean`), which carries real compute-time risk
   (Gate B2 needed up to ~9 minutes per candidate) that did not fit safely within this
   dispatch's remaining scope alongside the design analysis above. It is recommended, scoped,
   and ready to build as the very next concrete step.

## Do not re-derive

- Everything in handoffs 07, 08, 09 (the `y ≤ x` closing argument, the `ForestComparable`
  derivation and its landed status, the two-source enumeration, the exclusion list).
- The source-list scoping above (sources 1-5, which need origin tracking and which do not) —
  established this dispatch by direct reading of `intApplyRuleFull`, reusable as-is.
- The identification that Phase 10's residual case and DP-5's "Gap 1" are the same underlying
  question — established this dispatch, reusable as-is; do not re-run this comparison from
  scratch.

## Verification

No Lean file changed (`git status --short Cslib/ CslibTests/` empty). No regression: the
baseline established by the prior dispatch (`ForestComparable` export, commit `7f9031c0`) is
untouched. The 4 in-scope sorries (`Scheme.lean:731` DP-5, `Scheme.lean:7884` the
`openBranch_countermodel` upward-closure conjunct, `Completeness.lean:146` DP-3,
`Minimal/Completeness.lean:141` DP-4) plus the one unrelated pre-existing
`FrameSoundness.lean:1276` sorry were reconfirmed present via `grep -rn '\bsorry\b' Cslib/`
matching the expected set, with no new sorries introduced (none could be, since no file was
edited).

## Files touched this dispatch

- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/handoffs/10_origin-tracing-scoping-and-new-blocker.md`
  (this file)
- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/plans/06_gate-b2-then-origin-tracing-export.md`
  (Phase 10 annotated with this dispatch's scoping finding and the new blocker; status marker
  set to `[BLOCKED]` pending the probe/lemma recommended above)
- `specs/430_prove_atom_persistence_upward_closure_for_intexpan/.orchestrator-handoff.json`,
  `.return-meta.json` (this dispatch's metadata)

`git status --short Cslib/ CslibTests/` at the end of this dispatch is empty — no Lean source
changed.
