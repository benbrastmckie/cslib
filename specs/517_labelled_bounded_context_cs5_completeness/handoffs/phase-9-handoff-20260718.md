# Task 517 Phase 9 Handoff — Frame-class match (`cs5FCIncest` for `CanonWorld.r`)

**Date**: 2026-07-18
**Status**: Phase 9 [COMPLETED]. Next: Phase 10 (`cs5_completeness` assembly).

## What landed

New mainline file `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/FrameClass.lean`:

- `TPrime.equivOn (H : TPrime TS5 Atom) : EquivalenceOn H.G.X H.G.R` — near-immediate projection
  of `equivalence_of_classicalModelOn_TS5` (`Context.lean:399`).
- `CanonWorld.r_refl`, `CanonWorld.r_trans` — plain reflexivity/transitivity of `CanonWorld.r`.
- `CanonWorld.r_rebase` — the `fourBox`-style re-basing conjunct of `cs5FCIncest` (third
  conjunct); needs only transitivity.
- `CanonWorld.r_symBox` — the `bBox`-style re-basing conjunct (fourth conjunct); needs symmetry.
- `CanonWorld.r_incest` — `cs5Incest CanonWorld.r` (fifth conjunct, the `bDia` Marin instance);
  witness `u' := u`, plain symmetry.
- `cs5FCIncest_canonWorld_r : cs5FCIncest (@CanonWorld.r Atom TS5)` — the bundled match, all five
  conjuncts, sorry-free, `lean_verify`-clean (axioms `["propext","Quot.sound"]`, no `sorryAx`).

## The design nuance (resolved)

`CanonWorld` as built in Phase 8 (the **general** type, ranging over every `TPrime TS5 Atom`)
instantiates `cs5FCIncest`'s frame-condition signature **directly** — no restricted world-type
subtype was needed. `CanonWorld.le`/`CanonWorld.r` are used exactly as landed; nothing was
weakened or swapped.

This works where the analogous match **failed** for `CS5Canonical.lean`'s
`CS5CanonSegment`/`CS5PrimeSegment` world types (`cs5Incest_cs5CanonMreach_false`,
`cs5Incest_cs5PrimeMreach_false`) because of a structural difference:

- Those types' relation is box-based (`boxInv w.head ⊆ u.head`), a one-sided containment with no
  witness for the reverse direction. `cs5Incest_forces_symm` shows this forces the mediating
  witness to `u' := u` and then requires PLAIN symmetry, which fails concretely at the
  universally-reachable exploding world `Ω` (`head = Set.univ`).
- `CanonWorld.r w u := w.ctx = u.ctx ∧ w.ctx.G.R w.lbl u.lbl` is the raw graph relation, and
  `TPrime.clModel : ClassicalModelOn TS5 G.X G.R` supplies genuine
  reflexivity/symmetry/transitivity on `G.X` directly (`TPrime.equivOn`). There is no `CanonWorld`
  analogue of `Ω`: `TPrime`'s Consistency clause bans any exploding node from every context in the
  type. So the same `u' := u` witness is available directly via `EquivalenceOn.symm`, with no
  monotonicity-collapse argument to defeat it.

Point-of-use notes on why `cs5Incest_forces_symm` and `cs5TwoSidedR_iff_cs5Tail` do not trip here
are recorded in `FrameClass.lean`'s module docstring (both guardrails' hypotheses simply do not
match `CanonWorld.r`'s shape — box-based vs. raw-graph, and quasi-prime-theory vs. graph-node
context, respectively).

## Verification

Full CSLib CI pipeline green:
- `lake exe cache get`: cache warm, no-op.
- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.FrameClass`: green.
- `lake exe checkInitImports`: pass.
- `lake lint`: 0 warnings for `FrameClass.lean`.
- `lake exe lint-style`: 0 warnings for `FrameClass.lean`.
- `lake shake --add-public --keep-implied --keep-prefix`: no suggestions for `FrameClass.lean`.
- `lake exe mk_all --module`: `Cslib.lean` updated (+1 import line).
- `lake test`: green, 9237/9237 (pre-existing sorries in unrelated Propositional Tableau files
  unregressed — same baseline as Phase 8's handoff).
- Full `lake build`: green, 3245/3245 jobs (guardrail modules — `Context.lean`,
  `CanonicalModel.lean`, `CS5Canonical.lean` — unregressed).
- `lean_verify cs5FCIncest_canonWorld_r`: `{"axioms":["propext","Quot.sound"],"warnings":[]}`.
- `grep sorry`/vacuous-def/new-axiom checks on `FrameClass.lean`: all clean (zero hits).

## Continuation context for Phase 10 (`cs5_completeness` assembly)

Phase 10 composes: `¬ Derivable CS5ModalAxiom φ` ⟹ (via `primeLemma`, Phase 7) a `𝒯`-prime
context `H` refuting `φ` at some label `y` ⟹ (via `canon_truth_lemma`, Phase 8) `¬ CKForces
CanonWorld.r canonVal canonBotForces ⟨H,y,_⟩ φ` ⟹ (via `cs5FCIncest_canonWorld_r`, this phase, plus
`canonVal_mono`/`canonBotForces_mono`/etc. already landed in `CanonicalModel.lean`) a genuine
`CKValidFC cs5FCIncest`-countermodel to `φ`, giving the contrapositive
`CKValidFC cs5FCIncest φ → Derivable CS5ModalAxiom φ`.

All ingredients Phase 10 needs are now landed and sorry-free:
- `primeLemma` (`PrimeLemma.lean`)
- `canon_truth_lemma` (`CanonicalModel.lean`)
- `cs5FCIncest_canonWorld_r` (`FrameClass.lean`, this phase)
- `cs5_soundness_derivable_incest` (`CS5Canonical.lean:373`, for the other soundness direction,
  though Phase 10 itself is the *completeness* direction and consumes the frame-class match, not
  soundness, directly)

No blockers. No sorries. No new axioms. Ready for Phase 10.
