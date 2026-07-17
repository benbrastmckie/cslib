# Task 509 Phases 8-11: Implementation Summary

**Session**: `sess_1784065982_0f4e12` (continuation dispatch, Phases 8-11 of 11)

## Outcome

**Branch B** (mechanized obstruction). Phases 8 and 11 are `[COMPLETED]`; Phases 9 and 10 are
`[BLOCKED]` with a detailed blocker writeup in the plan file. This is a fully valid, sorry-free,
axiom-clean outcome per the dispatch's binding rules — a rigorous negative result at a precisely
located sub-problem, not a soft failure.

## What was done

### Phase 8: pair-poset primeness probe

- Re-confirmed Pacheco's Lemma 16/18 defects against the (repaired) literature corpus
  (`bash .claude/scripts/literature-search.sh --read ec3a8bddd907f0c4` /
  `--read 39fb2b22fa8afe5a`) — both hold exactly as the plan states, verbatim in the chunks.
- Landed `specs/509_.../probes/cs5-pair-primeness.lean` (sorry-free, 187 lines):
  `cs5PairPoset` (the designated-formula-exclusion pair poset), `cs5_pair_seed_mem` (clean seed
  construction, fixing Pacheco's asserted-seed defect), `cs5_pair_chain_union_mem` (clean
  chain-upper-bound step, fixing his absent-chain-step defect), and
  `cs5_pair_maximal_component_left`/`_right` (the general order fact the plan predicted).
- **Genuine finding**: the plan's "largely a mapping exercise, not new mathematics" prediction for
  the primeness step is only half right. Component-maximality (which the general order fact
  above does give, for free) does not by itself let the library's
  `Metalogic.prime_maximal_is_prime` apply, because the natural cross-condition predicate
  `Cons_Y(X) := boxInv X ⊆ Y` (the other pair component held fixed) is **not stable under
  deductive closure** — inserting a formula and closing can derive a new `□B` propositionally
  without `B` being pinned to `Y`. This is documented in full, with a worked-through repair
  sketch (a combined derivation system over `Atom ⊕ Atom` that bakes the cross-conditions in as
  *axioms* rather than an external invariant, making closure-stability free), in the probe's
  module docstring.

### Phases 9-10: blocked

Marked `[BLOCKED]` in the plan file with the full escalation-protocol writeup (what failed, what
was tried, why it's stuck, what is needed). The repair sketch from Phase 8 is the identified path
forward, left for a follow-up task — it needs new `Proposition.map`/`DerivationTree`
functoriality infrastructure (atom relabeling + a proof that `CS5ModalAxiom`-derivability lifts
along it), estimated at several hundred lines, genuinely beyond a "mapping exercise" and beyond
Phase 9/10's combined time budget in this dispatch.

### Phase 11: Branch B assembly

- Landed the three-world `cs5FC''` countermodel (previously only a probe,
  `probes/cs5-boxgap-countermodel.lean`) into `CS5.lean` itself: `CS5BoxGapWorld` (inductive,
  3 constructors), `cs5BoxGapLe`/`cs5BoxGapR`/`cs5BoxGapVal`/`cs5BoxGapBot` (the frame), and five
  public theorems (`cs5BoxGapR_fc`, `cs5BoxGap_box_p_or_box_q_at_w`, `cs5BoxGap_not_box_p_at_w`,
  `cs5BoxGap_not_q_at_w`, `cs5BoxGapVal_uc`) plus two `private` helpers — witnessing that
  `cs5_symmetric_tail_box_gap`'s hypotheses are jointly satisfiable, so the box-backward gap is a
  **real, non-vacuous obstruction**.
- Revised `CS5.lean`'s module docstring to final honest status: soundness over `cs5FC''`
  (`cs5_axiom_sound''`, all 17 axioms, axiom-free) and the canonical frame conditions
  (`cs5FC''_cs5Mreach`) are fully established; the diamond cases of a prospective truth lemma are
  free; completeness is open **specifically** at the truth lemma's box-backward case — not a
  library-level "`CS5` completeness is blocked" verdict, and not for the reason task 508
  originally (and incorrectly) claimed. Updated `## Main Definitions` with the new declarations.

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5` — clean.
- `lake build` (full project) — 3233/3242 jobs, exit 0; remaining warnings are all pre-existing
  and in files this task never touched (`Tableau/Intuitionistic/*`, `Tableau/Minimal/*`,
  `SequentCalculus/LK/Soundness.lean`).
- `lake exe checkInitImports` — clean, no output.
- `lake exe lint-style` — clean, no output.
- `lake lint` — one error total, in `PrimeExclusion.lean` (pre-existing, unmodified by this task,
  unrelated `unusedArguments` finding on `DerivExcludes`'s `_D` parameter). Zero in `CS5.lean`
  (added `@[nolint unusedArguments]` to `cs5BoxGapBot`, whose argument is structurally required by
  the `World → Prop` `botForces` shape but always `False`, matching existing codebase precedent
  for this pattern).
- `lake shake --add-public --keep-implied --keep-prefix` — no unused-import finding for `CS5.lean`.
- `lake exe mk_all --module` — "No update necessary" (no new file added under `Cslib/`).
- `lake test` — exit 0.
- `grep -rn "\bsorry\b" Cslib/Logics/Modal/Metalogic/Constructive/` — empty.
- Vacuous-definition scan — the one match in the whole `Cslib/` tree
  (`Computability/URM/Basic.lean:92`) is pre-existing, unrelated, from an old commit.
- `git diff --stat` shows `CS4.lean`, `CT.lean`, `CK.lean`, `Segment.lean`, `CKTruthLemma.lean`
  untouched.
- `#print axioms`/`lean_verify` recorded: `cs5_axiom_sound''` and `cs5Tail_symm` (the two hard
  gates) remain **axiom-free**. The five new countermodel theorems depend on
  `[propext, Quot.sound]` only (from the `Decidable`/`decide` machinery on a finite type — no
  `Classical.choice`, no `sorryAx`). The Phase 8 probe's four theorems depend on
  `[propext, Classical.choice]` or `[propext, Classical.choice, Quot.sound]` (the expected Zorn
  three, since `cs5_pair_chain_union_mem` routes through `Metalogic.deductivelyClosed_chain_union`
  and `cs5_pair_seed_mem` through `modalDeductiveClosure_closed`).

## Collapse-inheritance check (binding rule 4)

Not triggered. The pair-poset design (`cs5PairPoset`) never carries a `⊥ ∉ X`/bot-exclusion
invariant — only the designated-formula exclusions `□A ∉ X`, `A ∉ Y` — so nothing in the Phase 8
probe forces `W⊥ = ∅` or re-proves `CS5 ⊢ φ ↔ IS5 ⊢ φ`. No collapse byproduct to surface.

## Plan deviations

- Phase 8's task list called for proving the primeness engine out "reusing `set_maximal_is_prime`
  where possible"; the probe proves everything *up to* that reuse point and documents precisely
  where and why the reuse does not go through, rather than completing it — this is the phase's
  central (negative) finding, not an incomplete execution of the original task.
- Phases 9-10 are `[BLOCKED]` rather than `[COMPLETED]`/`[PARTIAL]`, per the escalation protocol,
  since no code was landed for them (only the Phase 8 groundwork they would have built on).
- Phase 11 Branch B's checklist is followed exactly as written in the plan (three-world
  countermodel landed, docstring revised, no library-level BLOCKED verdict).
- Did not perform the CS5.lean/CS5Canonical.lean split (deferred since Phase 7): Branch B's
  addition (~130 lines) is modest, and the file remains manageable at its current size.

## Continuation guidance

A follow-up task should attempt the combined-derivation-system repair sketched in
`probes/cs5-pair-primeness.lean`'s module docstring: define atom relabeling
`Proposition Atom → Proposition (Atom ⊕ Atom)` (structural recursion, `Sum.inl`/`Sum.inr` tagging),
prove `DerivationTree` functoriality along it (`CS5ModalAxiom`-derivability lifts), define the
combined `PairAxiom` system (lifted `CS5ModalAxiom` on each side plus the two cross-condition
implications `□(τ_L B) → τ_R B`/`□(τ_R B) → τ_L B` as new axioms), then a single
`quasi_prime_set_exclusion`-style application excluding `{τ_L(□A), τ_R A}` (a 2-element set,
simpler than Phase 6/7's n-ary box-list case). If that closes, Phase 11 Branch A becomes
available and this module's docstring should be revised again to state completeness established.
