# Task 517 Continuation Handoff — Phase 11.1/11.2 (General Soundness), 2026-07-19 (third dispatch)

## Status Summary

- **Phase 10** (`cs5_completeness`): unchanged, **[COMPLETED]**.
- **Phase 11.3** (`nik_TS5_consistent`, `nik_soundness_onePoint`): unchanged, **[COMPLETED]**,
  landed in the second dispatch. **DO NOT re-attempt.**
- **Phase 11.1/11.2** (general `nik_TS5_soundness`): escalated to **[BLOCKED]** this dispatch, per
  the Escalation Protocol. This is a change in framing from the prior two dispatches (which
  treated the gap as a scope/budget continuation): this dispatch's analysis concludes the
  obstruction is a genuine, currently-open mathematical question, not a remaining-effort estimate.
  **No new sorry-free lemma was added toward the general theorem this dispatch** -- only a
  docstring analysis (`Soundness.lean`'s "Third dispatch" section) recording exactly why, so a
  future dispatch does not have to re-derive it.
- **Phase 12**: still correctly not started (depends on Phase 11 completing).
- Build/lint/style/shake/test/checkInitImports: all still green, unregressed (see Verification
  below). No `.lean` theorem statements were touched this dispatch -- only `Soundness.lean`'s
  module docstring and this plan's Phase 11/11.1/11.2 status markers were edited.

**Next dispatch should NOT be a fourth direct-implementation attempt at `nik_TS5_soundness` via
the same route.** See "Recommended next steps" below.

## What this dispatch did

Attempted to actually close the "finite-clique-relift lemma" the second dispatch's "Refined
analysis of items 1-4" docstring section targeted, for both:

1. **The `(□I)` producer side**: constructing a fresh label `y`'s exact interpretation `u`
   (handed to the proof adversarially by `CKForces`'s `box` clause, `Forcing.lean:75`:
   `∀ w' ≥ w, ∀ u, r w' u → CKForces u φ` -- `u` is NOT chosen by the proof) such that `y`'s new
   edge-cond obligations (against every other already-used label, since `TClosure TS5 G.R` is
   total on the connected graph `G.X`, per the second dispatch's finding) hold *exactly*.
2. **The `(□E)` consumer side** (not examined by either prior dispatch): `boxE` consumes an
   arbitrary `TClosure`-derived edge, including ones produced via `.symm` (`B ∈ TS5`) from a raw,
   *one-directional* edge (`Graph.addEdge` only ever adds a directed disjunct). This needs *exact*
   symmetry of `r` on an already-fixed (non-fresh) pair of labels, which `cs5Incest`'s weakened
   substitute (`r w u → ∃ u' ≥ u, r u' w`) does not supply.

Both sides converge on the same root cause: of `cs5FCIncest`'s five conjuncts, only `hrefl` and
`htrans` have non-existential conclusions; `hfour`/`hsymbox`/`hincest` are all irreducibly
existential (raised-witness) conclusions, so no chain of them can ever pin down an EXACT relational
fact between two independently-fixed points -- only `hrefl`/`htrans` composition of already-exact
seed facts can.

**A battery of finite hand-constructed candidate models** (`Fin n`/`ℕ` with the standard linear
`≤`, various edge sets designed to satisfy `hincest`+`hfour`+`hsymbox` while keeping one pair
asymmetric) was tried to determine whether this is a real obstruction or just unexplored territory.
Every attempt that satisfied all of `hincest`/`hfour`/`hsymbox` kept being forced, by *exact*
`htrans` composing the newly-introduced raised witnesses back around, into symmetric (sometimes
fully total/clique) closure on the finitely-generated substructure anyway. No stable finite
asymmetric countermodel was found -- but a full formal proof of the positive claim
(`cs5FCIncest` forces symmetric/clique closure on any finitely-generated substructure) was also
not completed; direct proof attempts chaining `hincest`/`hfour`/`hsymbox` pairwise did not close.

**This is genuinely unresolved, not merely unattempted** -- it is the single largest concrete open
question left in this proof direction. Resolving it either direction would decisively settle
whether a finite-induction clique-relift lemma is provable at all, or whether different machinery
(see below) is needed.

## Recommended next steps (in order of estimated cost)

1. **Cheapest, try first (a few hours, not a full dispatch)**: investigate directly whether
   `cs5FCIncest` provably forces symmetric/clique closure on finitely-generated substructures (the
   open question above). If it resolves positively, the "finite models keep collapsing into full
   closure" pattern observed this dispatch looks structurally like a fixpoint/closure-completion
   problem, not a simple finite induction -- i.e. the same *shape* of problem the landed `FLO`
   maximal-extension machinery (Phases 1-7, `PrimeLemma.lean`/probes) already solves for the
   completeness direction. **Investigating whether that machinery can be reused/adapted here is
   the single most promising concrete lead**, ahead of (2)/(3) below.
2. **Simpson's own recommended route** (Ch. 8, `8.1.2`): formalize the modified sequent system
   `L_m(𝒯, ∅)` with `𝒯`-closure baked into `(⊃L)`/`(⊃R)_m` -- Simpson states this is needed
   *specifically* to avoid the non-tree-excursion problem this dispatch (and the two before it)
   kept hitting. Substantial new proof-theoretic infrastructure (new derivation system +
   translation + its own soundness proof): re-plan scale, estimate 300-600+ lines.
3. Build the deferred Hilbert-labelled equivalence bridge (Ch. 6, already flagged as future work
   in this plan's Phase 12 notes) and obtain labelled soundness as a corollary of the
   already-proven, sorry-free `cs5_soundness_derivable_incest` (`CS5Canonical.lean:373`). This
   reopens a scope decision (Option B of this plan deliberately deferred Ch. 6) -- a call for the
   user/orchestrator, not this dispatch.

None of (1)-(3) was attempted this dispatch; each is genuinely research-pass/re-plan scale.

## Files touched this dispatch

- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`: docstring only (top status
  line + new "Third dispatch: why the direct-induction route is now assessed INTRACTABLE at
  standard effort" section). No theorem statements, proofs, or lemma signatures changed.
- `specs/517_labelled_bounded_context_cs5_completeness/plans/13_labelled-completeness-full-soundness.md`:
  Phase 11 heading, 11.1, and 11.2 marked `[BLOCKED]` with blocker documentation.
- This handoff.

## Verification (this dispatch)

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness`: green (docstring-only
  change; no new warnings beyond a pre-existing, unrelated `Modal/Basic.lean` linter note).
- Full `lake build`: 3250/3250 green (unregressed; job count differs slightly from the prior
  dispatch's 3247 due to concurrent, unrelated sessions' files in the working tree -- not part of
  this dispatch's scope).
- `lake exe checkInitImports`: pass (no output = pass).
- `lake lint` (full project): "Linting passed for Cslib." -- 0 warnings.
- `lake exe lint-style Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`: 0
  warnings.
- `lake shake --add-public --keep-implied --keep-prefix`: no suggestion for `Labelled/Soundness.lean`
  (only pre-existing, unrelated suggestions for other files).
- `lake exe mk_all --module`: `Soundness.lean` already registered in `Cslib.lean`; reverted TWICE
  (once after shake's internal rebuild, once after the direct `mk_all` invocation) the same
  concurrent-session import lines (`SchemaSoundness`, `SchemaBridges`/`SchemaUnion`) noted in the
  prior dispatch's handoff, to keep this commit scoped to task 517. `git status --short Cslib.lean`
  confirmed clean before finishing.
- `lake test`: exit 0; 9241-9242 range of jobs (varies slightly run to run due to concurrent
  sessions); pre-existing sorries in unrelated Propositional Tableau files (`Scheme.lean`,
  `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`) unregressed, matching the prior
  dispatch's finding.
- Sorry inventory (modified files): **empty** (`grep '\bsorry\b'` hits are only the word "sorry"
  appearing inside the new docstring prose, not tactic usage).
- New axiom count: **zero** (`grep '^axiom '` on the modified file: no matches).
- `git status --short Cslib.lean`: clean (no accidental registration of concurrent-session files).
