# Task 554 Continuation Handoff — After Phase 7

**Date**: 2026-07-25
**Session**: sess_1785007897_038307_554
**Plan**: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md`

## State

Stages A (Phases 1-5) and Phase 6-7 of Stage B are COMPLETE and committed. 7/32 phases done. All
commits on `main`. Whole-project `lake build` / `lake test` / `lake lint` / `lake exe
checkInitImports` / `lake exe lint-style` / scoped `lake shake` all green at this commit.
Invariants held: `Cslib/` bare-`sorry` count still exactly 5, axiom count still 26, zero new
`sorry`/`axiom` introduced.

## Commit This Session

- `b96a3a90` — task 554 phase 7: contexts, hole filling, and output pruning. New file
  `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Context.lean`.

## Next Action

Resume at **Phase 8: `fm` compositionality over contexts** (Stage B's third and final phase).
Depends on Phase 7 (done). New file: `Cslib/Logics/Modal/Metalogic/Constructive/Nested/
Translation.lean`.

Phase 8 needs, per the plan:
1. For each context kind (`OutputCtx`, `InputCtx`), prove by induction on the list that
   `CS5`-derivability of `fm ∆ → fm ∆'` lifts to `fm (Γ{∆}) → fm (Γ{∆'})`, in the appropriate
   variance (output contexts covariant in the hole, input contexts contravariant — this is stated
   explicitly in Phase 8's task list, item 3).
2. Prove the pruning relation: how `fm (Γ⇓{∆})` relates to `fm (Γ{∆})`.
3. Every lemma should be stated against `Derivable (@CS5ModalAxiom Atom)` (the Hilbert-relative
   currency), per the plan's verification note.

**Relevant existing infrastructure** (found via `grep -rln CS5ModalAxiom Cslib/`, not yet read in
depth this session):
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean:168` —
  `inductive CS5ModalAxiom : Proposition Atom → Prop where` (the axiom schema itself).
- `Derivable` is presumably the ambient Hilbert-derivability relation used throughout
  `Cslib/Logics/Modal/Metalogic/Constructive/` and `InterSystem/` — check
  `CS5Canonical.lean`, `CS5Completeness.lean`, and `Labelled/Deduction.lean` for its exact
  signature and how `Derivable (@CS5ModalAxiom Atom) φ ψ`-style statements are phrased elsewhere
  in this codebase, to match the existing idiom rather than inventing a new one.
- `Cslib/Logics/Modal/Metalogic/InterSystem/PropositionalStrengthMonotonicity.lean` and
  `LatticeMonotonicity.lean` may have directly-reusable patterns for "monotonicity lifts through
  a context" style lemmas (unread this session — worth checking first, since this project has
  apparently already built monotonicity-lifting machinery for a related purpose).

**What Phase 7 built that Phase 8 will consume** (all in the new `Nested/Context.lean`, all
`rfl`-computable, all `sorry`-free):
- `OutputCtx Atom := List (NestedLhs Atom)` with `fillEmpty`, `fillLhs`, `fillRhs`, `fillFull`.
- `InputCtx Atom` (fields `Γ'`, `Λ` : `OutputCtx Atom`, `π : NestedRhs Atom` — note the lowercase
  `π` field name, not `Π`; see below) with `fillLhs`, `fillEmpty`.
- `InputCtx.outputPruning : InputCtx Atom → OutputCtx Atom := ctx.Γ' ++ ctx.Λ` (Definition 2.3,
  `Γ⇓{ }`).
- `buildRhsChain_append` and `OutputCtx.fillRhs_append` (nesting/associativity facts already
  landed; may be directly useful for Phase 8's induction).
- The `(Γ⇓){∆}` vs `Γ{∆}` relationship (Phase 7's own task list item) was explicitly **deferred**
  to Phase 8, since the natural candidate structural equalities don't hold as bare equalities
  (they differ by a `box ∅ ·`-vs-direct-substitution distinction) — Phase 8's `fm`-level
  compositionality apparatus is where the *correct* form of this relationship should emerge
  naturally (probably as an `fm`-level equation/iff rather than a raw term equality). Read
  `Context.lean`'s "Basic Equational Lemmas" docstring section before starting Phase 8 for the
  full reasoning — do not re-derive this from scratch.

## Two Points a Fresh Session Must Know Before Touching `Nested/Context.lean`

1. **`Π` cannot be used as a Lean identifier in this codebase.** Mathlib's
   `Delaborators.lean` binds capital `Π` as a Pi-type delaborator token; any attempt to declare
   `Π : SomeType` as a field/binder produces cryptic downstream "expected token" parse errors at
   the *use* sites, not at the declaration site's exact column in the most legible way (they
   showed up on the `ctx.Π` access lines before I traced them back to the field declaration
   itself). Use lowercase `π` instead — confirmed safe (only `scoped`/`local` Mathlib notations
   for lowercase `π`, none open by default).

2. **`InputCtx.π : NestedRhs Atom`, not `Proposition Atom`.** This is a *documented, forced*
   deviation from the plan's original `Π : Proposition` sketch (plan-compliance rules require
   raising deviations rather than silently substituting, but the deviation was necessary to make
   Phase 7's own cited verification example — Example 2.1's `Γ2{ }` — expressible at all; the
   plan's sketch and its own verification target were mutually inconsistent, and the full
   derivation forcing this resolution is documented at length in `Context.lean`'s module
   docstring plus this plan's own Phase 7 task-list annotations). If Phase 8 (or anything later)
   needs `π` to behave like a bare formula in some case, that expectation should be re-derived
   against the source rather than assumed — most likely it genuinely is compound in general and
   any "atomic" special case should be stated as a hypothesis, not baked into the type.

## Literature Access — Same Method as Phase 6, Confirmed Reliable Again

Direct PDF render (`Read` with `pages` param) cross-checked against `pdftotext -f N -l N -layout`
of the recovered source
(`~/Projects/Literature/.sources-recovered/arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics.pdf`)
continues to be the reliable method; this session re-confirmed page 5 (Example 2.1, Observation
2.2, Definition 2.3) via both methods again and found `pdftotext -layout` renders `•`/`◦`
correctly on this page (only `□` is silently dropped, as previously documented — page 5's actual
formulas use `♦`/`⊃` predominantly, so this page happened not to need `□`-restoration). Phase 8
will likely need pages 5-6 again (Figure 2 / System `NCK` on page 6, needed for Phase 9, may be
worth a preview read now if starting Phase 8 immediately) plus whatever pages state the precise
`fm`-compositionality lemmas the plan references (not yet located this session — search for
"Lemma 2." or similar numbering near page 5-7 first).

## Do Not Touch

`Cslib/Logics/Modal/Tableau/` — concurrent sessions (task 553 this round) own those files; confirmed
uncommitted-then-committed churn on `LoopChecking.lean` throughout this session (caused two
transient `lake test`/`lake lint` failures from stale `.olean`s — both resolved by re-running
`lake build` once the concurrent session's commit landed; not a defect in this session's own
work). Stage only `Cslib/Logics/Modal/Metalogic/Constructive/` and
`Cslib/Logics/Modal/Metalogic/InterSystem/` plus the task directory; never a repo-wide `git add`.

## Scale Reminder

32 phases total. Stage B (Phases 6-8) is nearly done (2/3 complete after this session). Stages
C-G (rule systems, soundness, completeness-with-cut, cut elimination, two-label bridge) not
started. Each phase should still be committed independently per the Commit-Per-Green-Substep
Mandate.
