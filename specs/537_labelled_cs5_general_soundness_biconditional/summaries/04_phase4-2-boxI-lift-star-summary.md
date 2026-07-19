# Summary: Task 537 Phase 4.2 (direct-route plan v2)

- **Task**: 537 - Prove the general labelled soundness direction (Simpson 1994 Thm 8.1.4)
- **Phase executed**: 4.2 ("Iterate the raise over the finite tree; close the boxI case")
- **Plan**: `specs/537_labelled_cs5_general_soundness_biconditional/plans/02_direct-route.md`
- **Outcome**: `[BLOCKED]` (sanctioned, per the plan's own blocked-honesty gate) with genuine
  forward progress landed. NOT a `sorry`; NOT an undirected retry.

## What was done

1. Read Phase 4 preamble + Phase 4.2 task text, report 02 §4(B), and `.lit-access.md` (Simpson
   §8.1.2, chunk 0156) to establish the settled design (see the Settled-Design Preamble in the
   dispatch transcript).
2. Worked out, precisely, what "iterate `boxI_raise_step` node-by-node over the finite derivation
   tree" requires mathematically: raising `x`'s interpretation cascades to every raw-`R`-neighbour
   (since `cs5FCIncest` has no "raise-source-only" conjunct), and a neighbour's own neighbours
   cascade further. Constructed and verified a concrete 3-cycle counterexample
   (`x → a → b → x`) showing that a fully general cascade over an *arbitrary* finite `Graph` is
   unsound without an additional rank/unique-parent (rooted-forest) invariant that does not yet
   exist anywhere in this codebase (the module's own docstring flags this as separate,
   not-yet-established "item 1: the tree-shape invariant" work belonging to Phase 5).
3. Landed `boxI_lift_star` (`Soundness.lean`, new "Star-lifting" section, inserted between
   `boxI_raise_step` and the one-point soundness section): a sound generalization of Phase 4.1's
   single-neighbour `boxI_raise_step` to a finite `Finset` of `x`'s **direct** raw-neighbours
   (either direction), proved by `Finset.induction`, chaining `cs5FCIncest_lift`/
   `cs5FCIncest_raise` while holding `x`'s target fixed at the original raise fact. Sorry-free;
   axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only, verified via
   `lake env lean` + `#print axioms`).
4. Updated the plan's Phase 4.2 heading to `[BLOCKED]`, annotated the checklist items
   (partial/not-reached/done), and wrote the Phase 7 handoff document
   (`handoffs/04_phase4-2-boxI-lift-blocked.md`) naming the exact blocker, what landed, and a
   concrete follow-up route.
5. Wrote `.orchestrator-handoff.json` with `status: "partial"`, a populated `blockers` entry
   (verbatim goal text + root cause + what's needed), `sorry_inventory: []`, and
   `continuation_context.next_phase_hint: "Phase 7"`.

## Files touched

- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` — added `boxI_lift_star`
  and its section docstring (~95 lines).
- `specs/537_labelled_cs5_general_soundness_biconditional/plans/02_direct-route.md` — Phase 4.2
  heading `[BLOCKED]`, checklist annotations.
- `specs/537_labelled_cs5_general_soundness_biconditional/handoffs/04_phase4-2-boxI-lift-blocked.md`
  — new, full blocker analysis and follow-up route.
- `specs/537_labelled_cs5_general_soundness_biconditional/.orchestrator-handoff.json` — updated.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` — green.
- `lake exe checkInitImports` — clean.
- `grep -n 'sorry' Soundness.lean` — zero tactic-level `sorry` (only pre-existing prose mentions).
- `lake env lean` + `#print axioms Cslib.Logic.Modal.Labelled.boxI_lift_star` —
  `[propext, Classical.choice, Quot.sound]` only.
- No Preserved Asset touched; `cs5FCIncest` unweakened.

## Plan Deviations

- Phase 4.2's literal task list ("Prove `boxI_lift` by finite induction... Close the `boxI`
  obligation...") was not completed in full. Per the plan's own explicit "Blocked-honesty
  sub-gate: stall at budget → Phase 7 (`[BLOCKED]`), never a `sorry`" clause, this is a
  documented, sanctioned deviation, not a silent skip. The deviation is recorded with a
  machine-checked mathematical reason (the 3-cycle counterexample) rather than an unverified
  "this is hard" claim, and a partial, useful lemma (`boxI_lift_star`) was landed in its place
  rather than nothing.

## Next steps (for the routed Phase 7 / follow-up task)

See `handoffs/04_phase4-2-boxI-lift-blocked.md` "Recommended follow-up" section: establish a
rank/depth + unique-parent invariant on the raw graph relation (likely threaded through Phase 5's
main induction motive directly, generalizing it alongside the existing raw-edge-cond/Γ-cond
invariants), then redo the `boxI_lift_star`-style `Finset` cascade under that invariant to cover
the full raw-connected component of `x`, and finally close the `boxI` case via
`Function.update _ y u`.

## Memory candidate

`classical` (invoked before `Finset.induction`/`Function.update` in the same tactic block) DOES
resolve the `DecidableEq (Label Atom)` obligation for a generic `Atom` type via
`Classical.propDecidable`-backed typeclass resolution. This corrects the prior Phase 4.1
dispatch's `.orchestrator-handoff.json` "dead_ends" note, which claimed `Function.update` fails
without a directly-supplied `DecidableEq` instance — it works fine as long as `classical` precedes
the relevant tactic call in scope.
