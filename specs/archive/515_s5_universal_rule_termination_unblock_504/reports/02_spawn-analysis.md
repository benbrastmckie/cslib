# Blocker Analysis: Task #515

**Parent Task**: #515 - s5_universal_rule_termination_unblock_504
**Generated**: 2026-07-17
**Blocker**: Phase 23 (KB5 completeness) is blocked because Phase 22's "factor, not clone" alias
`modalApplyOneKb5 := modalApplyOneFive` only propagates content to *direct* root successors, while
`extractModelKb5`'s forced relation (`Relation.EuclGen (Relation.SymmGen acc.hasEdge)`) relates
the root to indirect chain targets too — breaking the root box-positive case of the truth lemma
that `modalTableauKb5_complete` needs.

## Root Cause

Category: **Technical unknowns / missing prerequisite** (a genuinely new proof artifact must be
designed and proved before the target theorem can be attempted) — not a proof-engineering gap, an
impossibility, or a scope-creep symptom.

Task 515's plan (`specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`,
Phase 22 lines 2730-2799, Phase 23 lines 2801-2879) and the corresponding summary
(`summaries/18_phase23-kb5-completeness-blocked-partial.md`) document the obstruction precisely,
backed by a machine-checked (sorry-free, zero-axiom) counterexample lemma:

- **Phase 22 (COMPLETED)** landed `modalApplyOneKb5 := modalApplyOneFive` (Cslib/Logics/Modal/
  Tableau/FiveSimplification.lean:1436) as a *literal alias*, justified by "factor, not clone":
  since `modalApplyOneFive`'s soundness proof (`modalTableauFive_sound`) works for every
  `fiveFC`-frame (`Relation.RightEuclidean`), and `kb5FC := Std.Symm r ∧ RightEuclidean r` is
  strictly stronger, the same rule is automatically sound for `kb5FC` too. `modalTableauKb5_sound`
  followed as a two-line frame-class-monotonicity corollary in
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`. This factoring is explicitly **soundness-only**
  — the plan's own Phase 22 note already flags that completeness "is a genuinely different
  question... expected to need a bespoke symmetric-model extraction."
- **Phase 23 (`[PARTIAL]`)** landed `extractModelKb5` and its supporting lemmas in
  `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (:3230-3270), then — per the mandatory
  pre-code analysis required by `plan-compliance.md` — worked the completeness argument on paper
  before writing any completeness code, and found the obstruction is real: `extractModelKb5`'s
  relation is *forced* to be the least `kb5FC`-satisfying relation containing every raw tableau
  edge, `Relation.EuclGen (Relation.SymmGen acc.hasEdge)`. Unlike Five's non-symmetrized
  `EuclGen acc.hasEdge` (whose root-containment is proved by `euclGen_root_imp_hasEdge`, consuming
  `accTargetsNeRoot`), the *symmetrized* closure does **not** keep the root's reach capped at
  direct successors. This is confirmed by the machine-checked, sorry-free, zero-axiom witness
  lemma landed at `FrameCompleteness.lean:3294`:

  ```lean
  private lemma extractModelKb5_root_reach_scout {α : Type*} {r : α → α → Prop} {w0 x y : α}
      (h1 : r w0 x) (h2 : r x y) :
      Relation.EuclGen (Relation.SymmGen r) w0 y :=
    Relation.EuclGen.eucl (Relation.EuclGen.base (Relation.SymmGen.of_rel_symm h1))
      (Relation.EuclGen.base (Relation.SymmGen.of_rel h2))
  ```

  Concretely: a raw chain `0 → a → c` (root's direct successor `a`, `a` itself minting a fresh
  witness `c` — a routine, reachable shape under Route (a)'s witness-reuse mint arms) forces
  `(extractModelKb5 b acc).r 0 c` via `RightEuclidean` applied to the symmetrized partner `r a 0`
  (forced by `Std.Symm` from the required raw-edge survival `r 0 a`) and the raw-edge survival
  `r a c`. This holds for **any** `kb5FC`-satisfying relation preserving every raw edge — not an
  artifact of the specific `EuclGen (SymmGen ·)` closure choice, so no alternative closure operator
  avoids it (confirmed algebraically in the summary, not just by the scout lemma).
  `modalApplyOneKb5`'s root arm — deliberately restricted to direct successors, because that
  restriction is exactly what *Five's own* soundness needs (Five's root is not itself reflexive) —
  never forces `T(ψ)@c ∈ b`, breaking the truth lemma's root box-positive case:
  `T(□ψ)@0 ∈ b` must imply `T(ψ)@w'` for **every** `w'` with `(extractModelKb5 b acc).r 0 w'`,
  which now includes indirect worlds like `c`.

**Not an impossibility.** K5/KB5 completeness via a rooted Euclidean tableau is standard
(Blackburn–de Rijke–Venema §4.8-4.9). What is blocked is specifically *reusing*
`modalApplyOneFive`'s root-restricted rule for the completeness direction. A genuine fix needs a
new KB5-specific propagation rule: the root's box/diamond triggers dumping to the *full* known
non-root cluster (matching the non-root propagation arm's own unconditional behavior, since the
model forces the root into the same equivalence class as everyone it can reach), and — since a
rooted symmetric+Euclidean frame makes the root reflexive whenever it has a successor
(`Relation.symm_rightEuclidean_root_refl`, already landed sorry-free in
`Cslib/Foundations/Relation/Euclidean.lean:362`) — the rule must also propagate the root's own box
content back onto world `0` itself. Such a rule cannot be an alias of `modalApplyOneFive`: the
same unrestricted propagation would be **unsound** for the strictly larger `fiveFC` class (Five's
root is not reflexive), so "factor, not clone" does not transfer to this direction. The new rule
needs its own soundness proof against `kb5FC` and its own completeness argument built to match its
exact propagation shape. This is comparable in scope to Phases 15-21 of the plan (the entire Five
construction: rule design, termination bound, soundness assembly, extraction, Euclidean truth
lemma, completeness, decidability).

**Environmental note (not part of this blocker)**: full-project CI (`lake build`/`lake test`) for
the already-landed, sorry-free Phase 23 infra (`extractModelKb5` + its supporting lemmas,
`EuclGen.symm_of_symm`, the ported `FrameSoundness.lean` separation theorems, the
`CslibTests/ModalFrameSeparation.lean` regression test) is currently pending an unrelated
concurrent session (task 511) resolving its mid-edit of `Cslib/Logics/Modal/Tableau/
LoopChecking.lean`. This is a transient scheduling collision, not a design gap, and does not need
its own spawned task — the follow-up task(s) below should simply re-run full CI once that file is
green.

## Proposed New Tasks

### New Task 1: Design and prove a KB5-specific full-cluster propagation rule with its own soundness theorem
- **Effort**: 6-10 hours
- **Task Type**: cslib
- **Rationale**: `modalTableauKb5_complete` cannot be reached while `modalApplyOneKb5` remains a
  literal alias of `modalApplyOneFive`, because that rule structurally cannot force the box content
  the KB5 (symmetric + right-Euclidean) extraction relation requires at indirect root-reachable
  worlds. This task delivers the missing propagation rule and proves it sound against `kb5FC` —
  the load-bearing prerequisite for the completeness proof in New Task 2.
  - Land a new rule (a plausible name is `modalApplyOneKb5'`, or `Kb5Simplification.lean`'s own
    entry point if a sibling file is used — do not reuse `modalApplyOneFive`'s name for a
    semantically different rule) in either
    `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (KB5 section, alongside the retired
    `modalApplyOneKb5` alias) or a new `Cslib/Logics/Modal/Tableau/Kb5Simplification.lean`
    (implementer's choice, following whichever the plan/implementer determines mirrors the
    existing Five file structure most cleanly — this decision belongs to the implementation
    dispatch, not this analysis).
  - The rule must, on the root box-positive/diamond-negative trigger, propagate to the **full
    known non-root cluster** (matching the non-root propagation arm's own unconditional behavior),
    and must also propagate the root's own box content back onto world `0` itself (using the
    already-landed `Relation.symm_rightEuclidean_root_refl`,
    `Cslib/Foundations/Relation/Euclidean.lean:362`, to justify why root becomes reflexive
    whenever it has a successor).
  - Re-derive the termination bound for the new rule (it is no longer definitionally
    `modalApplyOneFive`, so Phase 19a's world-count-vs-`modalWorldBound` bound does not transfer
    for free — confirm or re-prove it against the new rule's mint-arm shape).
  - Land the `RuleApplicationSpecCore` instance for the new rule (mirroring
    `modalApplyOneFive_specCore`'s nine-field discharge pattern,
    `FiveSimplification.lean:1389-1441`).
  - Land a new soundness theorem (e.g. `modalTableauKb5_sound'` or replace/rename
    `modalTableauKb5_sound` to depend on the new rule instead of the Phase 22 alias — implementer's
    call, documented as a plan deviation if it changes the existing declaration's statement) in
    `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, proven directly against `kb5FC` (NOT via
    frame-class monotonicity from Five's soundness — that shortcut is unavailable here because the
    new rule's unrestricted root propagation would be unsound for the strictly larger `fiveFC`
    class, per the "factor, not clone does not transfer" finding in the Phase 23 blocker note,
    `FrameCompleteness.lean:3300-3339`).
  - **Reuse, do not re-derive**: `extractModelKb5` and its extraction lemmas
    (`extractModelKb5_r`/`_rightEuclidean`/`_symm`/`_hasEdge_imp_r`,
    `FrameCompleteness.lean:3230-3270`), `extractModelKb5_root_reach_scout`
    (`FrameCompleteness.lean:3294`, the counterexample that precisely characterizes what the new
    rule must handle), `EuclGen.symm_of_symm` + its `Std.Symm (EuclGen r)` instance and
    `Relation.EuclGen`/`Relation.SymmGen` (`Cslib/Foundations/Relation/Euclidean.lean`),
    `Relation.symm_rightEuclidean_root_refl` (`Euclidean.lean:362`), and the entire green
    S5/Five rule-design pattern in `FiveSimplification.lean` (mint-arm guards, witness reuse,
    source-split termination tagging) as the structural template.
  - **Constraint**: zero `sorry`, zero new `axiom` declarations in any landed declaration; every
    new public declaration must be `lean_verify`-clean (only the standard
    `[propext, Classical.choice, Quot.sound]` subset, several needing none). Do not introduce a
    vacuous placeholder (`def X := True`/`theorem X := trivial`) if a step cannot be completed —
    mark `[BLOCKED]` per `plan-compliance.md`/`lean4.md` instead.
  - **Do not touch** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` unless it has already been
    resolved by task 511 by the time this task runs (check first; it was mid-edit by a concurrent
    session as of this analysis).
- **file_scope**: `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`,
  `Cslib/Logics/Modal/Tableau/Kb5Simplification.lean` (new, if the implementer chooses a sibling
  file), `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
- **Depends on**: None

### New Task 2: Prove KB5 completeness and land `Decidable (kb5Valid φ)`
- **Effort**: 5-8 hours
- **Task Type**: cslib
- **Rationale**: Completes the re-scoped Phase 23 deliverable. Requires the exact propagation
  guarantees (full-cluster dump + root self-reflexive propagation) that New Task 1's rule and
  soundness proof establish — the truth lemma's root box-positive case must be argued using
  precisely those guarantees, not a generic "some sound rule exists" fact.
  - Land `theorem modalTableauKb5_complete (φ) (h : kb5Valid φ) : modalTableauKb5 φ = .closed`
    (or the tableau-name equivalent matching whatever entry point New Task 1's rule is wired
    through — e.g. if New Task 1 introduces `modalTableauKb5'`/renames the KB5 entry point, this
    theorem targets that same name) in `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, via
    `extractModelKb5` (already landed, `FrameCompleteness.lean:3230-3270`) + the Phase 12 lift
    pattern used by `modalTableauFive_complete` (`FiveSimplification.lean`/`FrameCompleteness.lean`,
    Phase 21).
  - Build (or extend) the Euclidean-symmetric truth lemma for the root box-positive case using New
    Task 1's rule: `T(□ψ)@0 ∈ b` must now imply `T(ψ)@w'` for every `w'` with
    `(extractModelKb5 b acc).r 0 w'`, discharged via the full-cluster-dump + root-reflexive
    propagation guarantees New Task 1 proved sound.
  - Land `instance instDecidableKb5Valid (φ) : Decidable (kb5Valid φ)`, mirroring
    `instDecidableFiveValid`'s two-direction (`modalTableauKb5_sound'`/`_complete`) decidability
    construction.
  - Remove/update the "Phase 23 Blocker" `/-! -/` note (`FrameCompleteness.lean:3300-3339`) and
    the SCOUT section framing (`:3272-3299`, which can stay as documentation of the design
    constraint the new rule had to satisfy, but should no longer read as an open blocker) to
    reflect the delivered state.
  - Reconcile the "5/KB5 Coverage via the S5 Route" docstring (`FrameCompleteness.lean`, located by
    content near the extraction lemmas) and the "Scope Note: Pure-K5 / Pure-5" block in
    `Cslib/Logics/Modal/Tableau/S5Simplification.lean` (located by content, not stale line
    numbers) to state KB5 completeness as delivered.
  - Extend `CslibTests/ModalFrameSeparation.lean`'s `kb5Valid` regression coverage to use
    `instDecidableKb5Valid`/`by decide` now that the instance exists, replacing the current
    term-proof-only (`boxImp_not_kb5Valid`) check where appropriate.
  - Run the full CSLib CI pipeline (`lake build`, `checkInitImports`, `lake lint`, `lint-style`,
    `lake test`, `shake`) to completion — this was the one item Phase 23 left pending purely due
    to the concurrent `LoopChecking.lean` interruption; by the time this task runs that file
    should be resolved, so this should require no further code changes, just verification.
  - **Constraint**: zero `sorry`, zero new `axiom` declarations; every new public declaration
    `lean_verify`-clean.
- **file_scope**: `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`,
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, `Cslib/Logics/Modal/Tableau/S5Simplification.lean`,
  `CslibTests/ModalFrameSeparation.lean`
- **Depends on**: New Task 1, because the truth lemma's root box-positive case in
  `modalTableauKb5_complete` must be argued using the *exact* propagation shape (full non-root
  cluster dump plus root-reflexive self-propagation) that New Task 1's rule provides and proves
  sound — the completeness proof is not generic over "any sound KB5 rule," it is specific to how
  New Task 1's rule saturates the branch. Attempting completeness before the rule and its
  soundness proof exist would mean re-deriving (and potentially re-deriving incorrectly) the exact
  propagation contract mid-completeness-proof, discarding the sequencing the "factor, not clone
  does not transfer to this direction" finding already established.

## Dependency Reasoning

- **New Task 2 depends on New Task 1**: the completeness proof's root box-positive case is not a
  generic consequence of "KB5 has some sound tableau rule" — it needs the *specific* saturation
  guarantee (full-cluster propagation + root self-reflexive propagation) that only New Task 1's
  rule design and soundness proof pin down. Writing the completeness proof against a not-yet-fixed
  rule shape would force New Task 2 to also invent the rule, defeating the purpose of splitting the
  work and risking an unsound or under-specified rule slipping in without its own dedicated
  soundness proof. This mirrors the plan's own Phases 15-18 (rule + soundness) preceding
  Phases 19-21 (termination + extraction + completeness) for the analogous Five construction.
- **File-overlap auto-check (Component 4a)**: New Task 1's `file_scope` includes
  `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`; New Task 2's `file_scope` also includes
  `FrameSoundness.lean`. Per the shared overlap algorithm
  (`.claude/context/patterns/file-footprint-overlap.md`), this is an exact-match overlap. A
  serializing dependency edge (New Task 2 depends on New Task 1) already exists for the
  substantive reason above, so no additional edge is auto-added — this is flagged here per the
  "never silent" requirement: the overlap is real (both tasks touch `FrameSoundness.lean`) and is
  already covered by the existing `dependencies: [0]` edge on New Task 2.

## After Completion

Once both spawned tasks are complete, resume task 515 with `/implement 515` (or the parent task's
current number at that time). Phase 23's remaining checklist items
(`modalTableauKb5_complete`, `instDecidableKb5Valid`, full CI) should then be re-attempted directly
against the newly landed rule and soundness proof, and marked `[COMPLETED]`.

The blocker will be resolved because: New Task 1 supplies a KB5-specific propagation rule whose
soundness is proved directly against `kb5FC` (not borrowed from Five), giving the truth lemma
exactly the saturation guarantees its root box-positive case needs; New Task 2 then builds the
completeness proof and decidability instance against that rule, closing the second half of task
515's re-scoped deliverable without reusing the root-restricted `modalApplyOneFive` rule that the
machine-checked scout lemma (`extractModelKb5_root_reach_scout`) proved structurally insufficient.
