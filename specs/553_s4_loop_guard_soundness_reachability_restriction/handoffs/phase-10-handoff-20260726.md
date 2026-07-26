# Handoff: Task 553, Phase 9 complete, Phase 10 not started

## State

Phases 1-9 of `plans/01_s4-settled-context-scheduling.md` are complete, committed, and verified
green. Phase 9 (Propagation-Adequacy Invariant) landed a single additive section (~282 lines) in
`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, immediately after the existing S4 4-rule
soundness lemmas (before `## B (Symmetric Frame)`, originally around line 1165):

- `branchPropAdequateIn` (def): the weakened S4 invariant. Keeps the branch-formula conjunct of
  `branchSatisfiableIn` unchanged; replaces the edge conjunct `acc.hasEdge w w' → m.r (f w) (f
  w')` with a branch-content-driven one -- for every recorded edge `w → w'`, `f w'` satisfies
  `□ψ` for every `T(□ψ)@w ∈ b`, and falsifies `◇ψ` for every `F(◇ψ)@w ∈ b`.
- `branchSatisfiableIn_imp_branchPropAdequateIn`: a genuine `branchSatisfiableIn s4FC` witness
  (mint edges) already satisfies the weaker invariant for free, via the same `IsTrans.trans`
  argument as the existing `branchSatisfiableIn_s4FC_boxPos_trans_mem`/`_diaNeg_trans_mem`,
  generalized from "one new formula" to "every edge in `acc`" (available since a real edge
  conjunct is branch-independent).
- `branchPropAdequateIn_s4FC_boxPos_trans_mem` / `_diaNeg_trans_mem`: the adequacy analogues of
  the two 4-rule trans_mem lemmas. **Each carries an explicit `hready` hypothesis** (see "Key
  discovery" below) -- this is the load-bearing fact Phase 10 needs to discharge for redirect
  edges.
- `modalFourBoxProp_sound_adequate` / `modalFourDiaNegProp_sound_adequate`: rule-level wrappers
  connecting `FrameRules.lean`'s `modalFourBoxProp`/`modalFourDiaNegProp` output to the two
  trans_mem lemmas above, mirroring `modalFourBoxProp_sound`/`modalFourDiaNegProp_sound`
  (`FrameSoundness.lean:1129`/`1149` at the pre-Phase-9 line numbers). Each also carries a
  `hready` hypothesis, now quantified over the rule's *all-successors* output shape.
- `branchPropAdequateIn_boxPos_mem`: the K box-positive rule's adequacy analogue (the "third
  consumer" named by the research). Uses `s4FC`'s reflexive half (`Std.Refl m.r`, a genuine
  semantic fact about the witness model, untouched by the edge-conjunct weakening) to get
  `Satisfies m (f w') φ` (the *unwrapped* K-rule payload) directly from `Satisfies m (f w') (.box
  φ)` via `hFC.1.refl (f w')` -- no `acc`-chasing needed for the propagated formula itself. Also
  carries a conditional `hready` (only fires if the propagated `φ` happens to itself be
  box-shaped).
- `modalClosed_unsat_propAdequateIn`: the `branchPropAdequateIn` transfer of `modalClosed_unsat`
  (`SoundnessStep.lean:92`). Direct transcription of that lemma's tactic script (which only ever
  consumes the branch-formula conjunct, discarding its edge witness via `_`), since
  `branchPropAdequateIn`'s branch-formula conjunct is byte-for-byte the same shape.

All six declarations are sorry-free and axiom-clean (`lean_verify`: only
`propext`/`Quot.sound`, no `sorryAx`). `git diff` on `FrameSoundness.lean` is purely additive
(282 insertions, 0 deletions) -- every pre-existing declaration (K/T/S4/4-rule/B sections) is
byte-for-byte unchanged. Full CI green: `lake build` (3257 jobs, whole project),
`lake exe checkInitImports`, `lake exe lint-style`, `lake lint` (same one pre-existing
out-of-scope error in `Temporal/Tableau/Saturation.lean`, zero new issues), `lake shake
--add-public --keep-implied --keep-prefix` (zero import changes suggested for
`FrameSoundness.lean`), `lake exe mk_all --module` (no update necessary for this phase -- a
pending `Cslib.lean` diff belongs to a concurrent session's `Nested/Rules.lean` addition and was
deliberately left uncommitted/untouched by this dispatch), `lake test` (exit 0). Repo-wide
`axiom` count unchanged at 26.

## Key discovery: the `hready` hypothesis (read this before starting Phase 10)

The plan's Phase 9 task list asked for "the adequacy analogues of
`branchSatisfiableIn_s4FC_boxPos_trans_mem` and `branchSatisfiableIn_s4FC_diaNeg_trans_mem`" as
if they were unconditional restatements. **They are not, and cannot be, unconditional.** Here is
why, stated precisely so Phase 10 does not have to rediscover it:

- Under `branchSatisfiableIn`, the edge conjunct `acc.hasEdge w w' → m.r (f w) (f w')` does **not**
  depend on branch membership at all -- it is a fixed fact about `(acc, m, f)`. Adding a new
  formula to the branch therefore never reopens it; only the new formula's own satisfaction needs
  checking. This is why the *existing* `branchSatisfiableIn_s4FC_boxPos_trans_mem` needs no
  extra hypothesis.
- Under `branchPropAdequateIn`, the edge conjunct is **driven by branch membership**: `acc.hasEdge
  w w' → (∀ ψ, T(□ψ)@w ∈ b → Satisfies m (f w') (.box ψ)) ∧ (...)`. Adding a new formula
  `T(□φ)@w'` to the branch (the whole point of the box/4-rule firing) **reopens this conjunct's
  obligation at every edge already recorded out of `w'`** -- for any existing edge `w' → v`, the
  conjunct now additionally demands `Satisfies m (f v) (.box φ)`, which is *not* derivable from the
  bare hypotheses (`acc` is unconstrained; `w'` need not have a real `m.r` edge to `v` under this
  weaker invariant). A fully general, hypothesis-free version of these two lemmas is **false**
  for an adversarially chosen `acc` with `w'` already having outgoing edges.
- The fix landed in Phase 9: add an explicit `hready` hypothesis to each of the three "consumer"
  lemmas, stating that for every edge `w' → v` already recorded in `acc`, the corresponding
  box/diamond content is *already on the branch* at `v`. This side condition is exactly what the
  ordered driver's **mint-readiness discipline** (Phase 4's `_mintReady`) is designed to
  guarantee at every real call site: a world only ever acquires an outgoing (redirect) edge once
  it is mint-ready, i.e. once its own box-content has already stabilized.

**This is Phase 10's actual job, stated precisely.** Phase 10's goal ("Redirect-Inertness") and
its named lemma `blockedRedirect_boxctx_mem` ("under mint-readiness ... every `T(□ψ)@v ∈ b` has
`T(□ψ)@wBlock ∈ b`") is *exactly* the discharge of Phase 9's `hready` hypothesis for the
redirect-edge case, via `blockingWorldS4Keyed_eq_birthContent` and `S4LoopInv.keyLowerBd`
(syntactic branch-membership reasoning, not semantic model-chasing). When assembling Phase 11's
`modalStepBranchS4KeyedOrdered_preserves_propAdequate`, the box/4-rule non-minting case should
call Phase 9's `branchPropAdequateIn_s4FC_boxPos_trans_mem`/`_diaNeg_trans_mem` with `hready`
discharged by Phase 10's `blockedRedirect_boxctx_mem` (redirect edges) or trivially (a freshly
minted `w'` has no outgoing edges yet, so `hready` is vacuous).

## Phase 10 scope: Redirect-Inertness

Per the plan (`plans/01_s4-settled-context-scheduling.md`, Phase 10 section, starting at what
was line 552 before Phase 9's additions -- re-locate via `grep -n "^### Phase 10"`), read that
section directly for the exact goal, tasks, and verification criteria. Its stated obligation
(`blockedRedirect_boxctx_mem` etc.) is precisely the `hready` discharge described above.

## Verification checklist for Phase 10 before committing

- `lean_verify` (or `#print axioms`) on every new declaration: axiom-clean
  (`propext`/`Classical.choice`/`Quot.sound` only), no `sorryAx`.
- No `sorry`, no vacuous placeholder definitions, ever -- if blocked, mark `[BLOCKED]` and report
  per the Escalation Protocol.
- `branchPropAdequateIn` and all six of Phase 9's new declarations, plus
  `modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` and all of Phases
  1-8's committed declarations, must remain byte-for-byte unchanged (Phase 15 is the sole
  destructive phase).
- Full CI pipeline (build, checkInitImports, lint-style, lint, shake, mk_all, test) before
  marking the phase `[COMPLETED]` and committing as `task 553 phase 10: {name}`.
- Territory note: this dispatch's file scope per the last orchestrator dispatch was
  `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, `Cslib/Logics/Modal/Tableau/
  FrameCompleteness.lean`, `CslibTests/S4LoopGuardRegression.lean`, plus task artifacts -- but
  Phase 9's actual plan-specified file was `FrameSoundness.lean` (not in that list). No lock
  conflict was found (this session holds the sole `.lock` on task 553; the only excluded zone is
  `Cslib/Logics/Modal/Metalogic/Constructive/Nested/**`, owned by a concurrent, unrelated
  session), so Phase 9 proceeded there and this is expected to continue for Phase 10 (its own
  plan section names `LoopChecking.lean` or a new soundness section in `FrameSoundness.lean`,
  "whichever keeps the import direction acyclic").

## Remaining phases after 10 (for context, not this dispatch's scope)

Phase 11 assembles `modalStepBranchS4KeyedOrdered_preserves_propAdequate` and the soundness
theorem `modalTableauS4KeyedOrdered_sound`, consuming Phase 9's rule-level lemmas (mint case via
`branchSatisfiableIn_imp_branchPropAdequateIn`, redirect case via Phase 10) and the fuel
induction. Phases 12-13 continue the completeness re-derivation (Hintikka invariant, top-loop
induction). Phase 14 adds `modalTableauS4KeyedOrdered_complete`. Phase 15 is the sole destructive
phase, deleting the unordered stepper/driver/entry-point trio.
