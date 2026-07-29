# Task 317 Wave A Complete — Handoff for Wave B

**As of commit `19c68791`** (task 317 phases 1-4: Route (a) frame plumbing over
intAccessPreorder, Wave A complete), landed on top of `6e24520d` (the prior partial
infrastructure commit; see `handoffs/01_phase1-continuation.md` for that cycle's notes,
now superseded by this one for anything about Phases 1-4).

## Status

Plan v6 Wave A (Phases 1-4) is **[COMPLETED]** in
`plans/06_route-a-frame-plumbing.md`. All four phases landed in a single commit (Lean compiles
per-file, and `truthLemma`'s frame change ripples immediately into `openBranch_countermodel`,
then `Completeness.lean`/`Minimal/Completeness.lean`, then `tableau_complete`'s `hvalid` bridge
shape — they are not independently buildable-green in isolation, confirming the prior
dispatch's finding).

Four inventory sorries **unchanged in count**, now at:
1. `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:533` — `truthLemma` T-imp case.
2. `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:1386` —
   `intExpandBranches_openBranch_sat` fuel-0 base case.
3. `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:133` —
   `intuitionisticTableau_complete`'s deferred-monotonicity bridge.
4. `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:125` — mirror.

Verified green: `Scheme`, `Completeness` (both), `DecisionProcedure` (both),
`IntDecidability`/`MinDecidability`. `checkInitImports` and `lint-style` clean on touched files.
`lean_verify` on `intuitionisticTableau_complete`/`minimalTableau_complete`/
`instDecidableIValid`: `{propext, sorryAx, Classical.choice, Quot.sound}` — no new axioms.
`Soundness.lean`/`Expansion.lean` (task 316 territory) untouched. Full `lake test`/`lake lint`/
`lake shake` were NOT run this cycle (deferred to /vet or the final Wave B wrap-up, per the
anti-overflow constraint — only scoped+grepped builds were used throughout).

## What actually landed (design summary)

Route (a)'s frame (`intAccessPreorder edges`, edge-reachability) is now the completeness
countermodel's `[Preorder Nat]` instance everywhere it matters, replacing the old ambient
global `Nat` order. Concretely:

- **`Scheme.lean`**:
  - `intStepBranch_linear_preserves`/`intStepBranch_branch_preserves` widened to a 3-conjunct
    conclusion, carrying `IExpandedAccessConsistent edges b e` alongside the existing
    `IExpandedConsistent`/`ILabelBound`. World-creation (`.neg, .imp` in the linear-preserves
    case) supplies the new edge's one-hop accessibility via `isAccessible_one_step`; every
    other case carries the invariant forward via `sfAccessSat_mono`/`sfAccessSat_edges_mono`.
  - `IAllAccessConsistent` (+ `_append`/`_map`) threaded through `intExpandBranches_openBranch_sat`'s
    induction ALONGSIDE the existing `IAllConsistent`, as a genuinely separate/parallel
    invariant (NOT merged into `IAllConsistent`'s definition — this was a deliberate choice to
    avoid touching any already-green call site of the original invariant).
  - `IFimpAccess edges b` (`∀ φ ψ w, F(φ→ψ)@w ∈ b → ∃ w', isAccessible edges w w' ∧ T(φ)@w' ∈
    b ∧ F(ψ)@w' ∈ b`) is the final payoff, exposed by `intExpandBranches_openBranch_sat`'s
    conclusion (now `∃ edges, IBranchSaturation Atom b ∧ IFimpAccess edges b`) and consumed
    directly by `truthLemma`.
  - `truthLemma` takes explicit `edges : IEdges` and `hfimp : IFimpAccess edges b` parameters,
    installs `letI : Preorder Nat := intAccessPreorder edges`, and closes the F-imp case via
    `hfimp` + `intAccessPreorder_le_of_isAccessible`. T-imp is still `sorry` (Phase 9's
    `sat_timp`).
  - `openBranch_countermodel`'s conclusion is now `∃ edges : IEdges, ¬ @IForces Atom Nat
    (intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ` (the Postmortem-5
    revision).
  - `tableau_complete`'s `hvalid` hypothesis is now `∀ (edges : IEdges) (b : IBranch Atom),
    @IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ`
    (edges is bound by the caller only once the open-branch case is reached inside
    `tableau_complete`'s own proof — this is why the bridge must accept it as a parameter
    rather than close over one fixed ambient instance).

- **`Completeness.lean` / `Minimal/Completeness.lean`**: `intTruthLemma`/`minTruthLemma`,
  `intuitionisticOpenBranch_countermodel`/`minOpenBranch_countermodel` mirror the above.
  `intuitionisticTableau_complete`/`minimalTableau_complete` retain their EXACT public
  `IValid φ → .closed`/`MValid φ → .closed` types (verified via green `DecisionProcedure.lean`
  builds); only the internal proof body changed shape (`intro edges _b` instead of `intro _b`),
  with the SAME sorry (reshaped, not removed, not duplicated).

## Deviation from the `01_phase1-continuation.md` handoff's sketch

That handoff recommended making `edges` a FIELD of `IBranchSaturation` (first field, with
`sat_fimp` restated over `isAccessible edges w w'` directly inside the structure). This cycle
instead kept `IBranchSaturation`'s 5 existing fields **completely untouched** and threaded
`edges`/the edge-accessibility fact via the separate `IFimpAccess edges b` proposition,
returned ALONGSIDE `IBranchSaturation Atom b` from the same `∃ edges, …` existential pattern
`intExpandBranches_openBranch_sat`/`openBranch_countermodel` already used. This is
mathematically equivalent (same information content) but has strictly smaller blast radius: no
change to `IBranchSaturation`'s structure, no risk to its consumers. **Recommendation for
future phases (esp. Phase 9, which adds `sat_timp` to `IBranchSaturation`)**: continue this
pattern — add a companion "`ITimpAccess`"-style proposition alongside `IBranchSaturation`
rather than mutating the structure, UNLESS `sat_timp`'s own proof genuinely needs `sat_timp` to
be co-inductively available as a structure field (re-examine at that point; do not assume the
field-based design is required just because the phase text describes it that way).

## Two non-obvious Lean issues hit this cycle (save future dispatches the rediscovery)

1. **A `private` declaration cannot appear in a `public` lemma's stated TYPE in this module's
   `@[expose] public section` system.** `IFimpAccess` had to be made non-`private` once it
   started appearing in `truthLemma`'s signature (previously all `private` helper
   defs/invariants were only ever used inside PROOF BODIES, never in a public lemma's stated
   type — this is the first case in this file). Symptom: "Unknown identifier" pointing at the
   private def's use site inside a later public declaration's signature, NOT an obvious
   "private declaration" error. If you add a NEW invariant/def that needs to appear in a public
   lemma's type, mark it non-`private` from the start.
2. **`IForces`'s auto-bound explicit-instance argument order is `Atom` THEN `World`**, not
   `World` then `Atom` as the intuitive reading of `@IForces Nat Atom (instance) …` might
   suggest. This is because `variable {Atom : Type u}` is declared in `Kripke.lean` BEFORE
   `IForces`'s own definition, so `Atom` gets prepended ahead of `World`'s auto-bound position.
   Concretely: `@IForces Atom Nat (intAccessPreorder edges) (intExtractValuation b) …` is
   correct; `@IForces Nat Atom (intAccessPreorder edges) …` fails with a confusing
   `Preorder.{0} ℕ` vs `Preorder.{u_1} Atom` mismatch. Verify via the build error, not by
   guessing, if this pattern is needed again in Phase 3/9/10's remaining `@IForces` sites.

## Concrete next steps for Wave B (Phases 5-11)

Follow the plan file `plans/06_route-a-frame-plumbing.md` starting at Phase 5. In order:

1. **Phase 5** (`Expansion.lean`, TERRITORY 316 — audit carefully): raise the fuel from
   `2^(2·φ.complexity+2)` to `intFuel φ ≈ 3^Θ(c²)`. File-disjoint from Phase 6, so could run
   concurrently with a SEPARATE writer if using `--team`, but this dispatch should do it
   serially like everything else.
2. **Phase 6** (`Scheme.lean`): `intUniverse`/`intWork`/linear world bound.
3. **Phase 7** (`Scheme.lean`, hard — pre-split candidate): `intExpMeasure_step_lt`.
4. **Phase 8** (`Scheme.lean`): `intExpMeasure_init_le_fuel`.
5. **Phase 9** (`Scheme.lean`, hard — pre-split candidate): add `sat_timp` to
   `IBranchSaturation` (see the "Deviation" note above re: field vs. companion-invariant
   design), discharge it, prove `intExtractValuation` monotonicity, close the `truthLemma`
   T-imp sorry (closes sorry 1/4).
6. **Phase 10** (CONVERGENCE — `Scheme.lean` + both `Completeness.lean` files): reformulate
   `intExpandBranches_openBranch_sat` with `measure ≤ fuel`, close the fuel-0 sorry (2/4) and
   discharge the two deferred-monotonicity bridges (3/4, 4/4) using Phase 9's monotonicity —
   reaches sorry-FREE. **This is where `tableau_complete`'s new `hvalid edges b` shape gets
   consumed**: the deferred-monotonicity `sorry` currently at `Completeness.lean:133`/
   `Minimal/Completeness.lean:125` (`intro edges _b; sorry`) is exactly the site Phase 10
   closes.
7. **Phase 11** (`references.bib`): add `NegriVonPlato2001` et al.

Task 430 remains correctly gated on Wave A landing (now done) — it should be RE-PLANNED to
consume this cycle's frame (`intAccessPreorder edges`) before being dispatched, per the plan's
own Roadmap Alignment note. Do not implement it from this handoff.

## Single-writer-per-file (R7) reminder

Re-run `git log -1 -- Scheme.lean Completeness.lean Minimal/Completeness.lean Expansion.lean`
at the start of the next dispatch to confirm no concurrent session has touched these since
`19c68791`. This cycle observed at least one other concurrent session actively committing to
UNRELATED files (`Cslib/Logics/Modal/Tableau/*`) in the same repo checkout during this
dispatch — harmless (different files), but a reminder that concurrent sessions are a live risk
on this repo right now, not merely a theoretical one.
