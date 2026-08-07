# Handoff: Task 553, Phases 1-5 complete, Phase 6 not started

## State

Phases 1-5 of `plans/01_s4-settled-context-scheduling.md` are complete, committed, and verified
green (each its own commit: `task 553 phase 1/2/3/4/5: ...`). `lake build` (scoped, per phase),
`lake exe checkInitImports`, and `lake exe lint-style` all pass after Phase 5. Repo-wide bare
`sorry` count in `Cslib/` is unchanged at 5 throughout. No task-number citations were introduced
in any deliverable file (only in this handoff and the plan file, both under `specs/`, where that
is permitted).

**Landed so far** (all in `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, new sections placed
immediately after `modalStepBranchS4Keyed`'s original definition and after
`modalExpMeasure_step_lt_S4Keyed` respectively -- both of those originals are byte-for-byte
unchanged):

- Phase 1-3 (prior dispatch): `CslibTests/S4LoopGuardRegression.lean` permanent counterexample
  corpus; corrected soundness-is-FALSE docstrings; `modalMintShape`/`modalNonMintCandidates` +
  3 lemmas (decidable, non-recursive settledness predicate).
- Phase 4: `modalStepBranchS4KeyedBody` (the per-formula rule-application body, factored out as
  a NAMED def so later lemmas can refer to it without restating a six-way match --
  `modalStepBranchS4Keyed` itself does NOT use it, bridged via the `rfl`-proved
  `modalStepBranchS4Keyed_eq_findSome_body`), `modalStepBranchS4KeyedOrdered` (the reordered
  stepper: scans `modalNonMintCandidates` first, falls back to the literal old
  `modalStepBranchS4Keyed` call), and its three required structural lemmas plus a shared
  `_cases` helper: `modalStepBranchS4KeyedOrdered_cases`, `_eq_none_iff`, `_selected_mem`,
  `_mintReady`.
- Phase 5: `modalStepBranchS4KeyedOrdered_proj` (selection-agnostic replacement for
  `modalStepBranchS4Keyed_proj_stepBranchGen`, phrased via `Option.map` dropping
  `modalStepBranchS4KeyedBody`'s `keys'` component) and `modalExpMeasure_step_lt_S4KeyedOrdered`
  (the ordered stepper's own strict measure-decrease theorem).

**Line numbers have shifted substantially** from the plan's stated numbers (which predate any
of Phases 1-5): Phase 4 added ~270 lines, Phase 5 added ~170 more, both inserted BEFORE the
`S4LoopInv`/`preserves_S4LoopInv` material Phase 6 targets. Do not trust any line number cited
in the plan text (e.g. "LoopChecking.lean:4624") -- re-grep for the declaration name before
editing. As of this commit:
- `S4LoopInv` (structure): line 4782
- `modalStepBranchS4_preserves_S4LoopInv` (the wrapper theorem Phase 6 must produce an ordered
  analogue of): line 5044
- The ten per-field sub-lemmas it assembles are scattered from line ~1887 to ~4998 (see below).

## Two Lean elaboration lessons from Phases 4-5 (read before writing Phase 6 proofs)

These cost significant debugging time and WILL recur in Phase 6's ten sub-lemmas, since every
one of them uses the same `unfold modalStepBranchS4Keyed at hstep0; obtain ⟨sf,hsfmem,hsf⟩ :=
List.exists_of_findSome?_eq_some hstep0` idiom that Phase 5 had to replace.

1. **`rcases`/`cases h : e with ...` auto-substitutes occurrences of `e` in the GOAL, but NEVER
   in other hypotheses.** If you need a hypothesis's type updated too, `rw [h] at hyp`
   explicitly. Trying `rw [h] at hyp ⊢` when the goal was already auto-substituted fails with
   "did not find an occurrence" -- drop the `⊢` in that case.

2. **A `let (a,b) := f x; body` pattern-match compiles DIFFERENTLY depending on whether `f` is
   abstract or concrete at the point the containing `def`/lemma-statement is elaborated.**
   - `modalStepBranchGen` (`Saturation.lean`) takes `apply : RuleApply Atom` as an ABSTRACT
     parameter, so its `let (result,newAcc) := apply sf b acc; match result with ...` compiles
     via direct `.1`/`.2` PROJECTIONS (no concrete constructor to case on). This projection
     shape is fixed at `modalStepBranchGen`'s own definition time and SURVIVES later
     instantiation of `apply` to a concrete function (e.g. `modalApplyOneS4Keyed φ₀ keys`) via
     `simp only [modalStepBranchGen] at h`/`unfold`. This is why the ORIGINAL, untouched
     `modalExpMeasure_step_lt_S4Keyed`'s proof can do
     `rcases hca : (modalApplyOneS4Keyed φ₀ keys sf bh acc).1 with nf | brs | nf | -` and then
     `rw [hca] at hfound` directly against a hypothesis derived from `modalStepBranchGen`.
   - `modalStepBranchS4KeyedBody` (Phase 4's new def) instead calls the CONCRETE
     `modalApplyOneS4Keyed φ₀ keys sf b acc` directly (not through an abstract parameter). Its
     `let (result, newAcc) := ...; match result with ...` compiles to a full
     `match modalApplyOneS4Keyed ... with | (result, newAcc) => ...`, NOT projections. A `.1`
     -based `rcases`/`rw` against a hypothesis unfolded from THIS body will fail with "did not
     find an occurrence". The fix used throughout Phase 5:
     `rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩; rw [hpair] at
     hyp` (NOT at the goal, which auto-substitutes per lesson 1), then case on the LOCAL
     variable `result` (`rcases hres : result with nf | brs | nf | -`), deriving any needed
     `.1`-shaped fact (e.g. for `modalApplyOneS4Keyed_branchingLength_S4`, which insists on a
     `.fst = .branching brs`-shaped hypothesis) via a small standalone `have hca : ... := by rw
     [hpair, hres]` rather than expecting it "for free" from the case split.
   - Separately: `simp only [Option.some.injEq, Prod.mk.injEq] at h` and the plain
     `Option.some.inj h` term-mode lemma do NOT behave identically when the destructured
     hypothesis's second/third tuple components mention a free variable applied under
     `List.map` to a NOW-singleton list (e.g. `newBs.map (fun _ => newExp)` after `newBs` gets
     `rfl`-substituted to a singleton `[nf ++ b]`). Only `obtain ⟨rfl, hne, -⟩ := Option.some.inj
     h` (the RAW, unsimplified term, NOT pre-simplified via `simp only [...] at h` first) lets
     `rcases`'s internal substitution machinery successfully unify `newExp` with the
     branch-specific expanded-set value the rest of the proof needs (`e ++ [sf]` for
     `.linear`/`.branching`, or `e` itself for `.persistent`). This is exactly the mechanism the
     EXISTING `modalExpMeasure_step_lt_S4Keyed` proof relies on and Phase 5 had to match
     verbatim. If a Phase-6 sub-lemma proof needs this same "identify the local `newExp`-shaped
     variable with a case-specific value" step, reach for `Option.some.inj` + a bare `obtain
     ⟨rfl, name, -⟩`, not `simp only [Option.some.injEq, Prod.mk.injEq]`.

## Phase 6 scope: `S4LoopInv` preservation and the fuel-sufficiency chain

**Do not underestimate this phase.** The plan's own task list undersells its size: the
"single" task "derive `modalStepBranchS4KeyedOrdered_preserves_S4LoopInv`, mirroring
`modalStepBranchS4_preserves_S4LoopInv`" is a WRAPPER over TEN separate per-field sub-lemmas,
each 30-150+ lines, most of which internally do their own
`unfold modalStepBranchS4Keyed at hstep0; obtain ⟨sf, hsfmem, hsf⟩ :=
List.exists_of_findSome?_eq_some hstep0` extraction (the same pattern Phase 5 replaced for the
measure lemma) PLUS substantial case analysis specific to each field (mint-shape detection,
blocking-world lookup, `modalApplyOne`/`modalApplyOneS4Keyed` equality bridges, pigeonhole
arguments for `bClosure`, etc.). Current line numbers of the ten sub-lemmas (grep to confirm,
these WILL shift again once Phase 6 inserts anything before them):

| Sub-lemma | Current line | `S4LoopInv` field / role |
|---|---|---|
| `modalStepBranchS4_preserves_keyLowerBd` | 1887 | `keyLowerBd` |
| `modalStepBranchS4_preserves_keysInUniverse` | 2014 | `keysInUniverse` |
| `modalStepBranchS4_preserves_keysTotal` | 2974 | `keysTotal` |
| `modalStepBranchS4_preserves_keysDistinct` | 3143 | `keysDistinct` (plan's explicit escalation trigger -- see below) |
| `modalStepBranchS4_preserves_eNodup` | 3219 | `eNodup` |
| `modalStepBranchS4_preserves_keysWorldsKnown` | 3291 | proof-internal aux, not an `S4LoopInv` field |
| `modalStepBranchS4_preserves_outDegEq` | 3393 | `outDegEq` |
| `modalStepBranchS4_preserves_accFresh` | 3616 | `accFresh` |
| `modalStepBranchS4_preserves_accKnown` | 3790 | `accKnown` |
| `modalStepBranchS4_preserves_worldsContiguousS4` | 3990 | proof-internal aux (`worldsContiguousS4` def at 3979) |
| `modalStepBranchS4_preserves_eClosure` | 4834 | `eClosure` |
| `modalStepBranchS4_preserves_bClosure` | 4889 | `bClosure` |

The wrapper `modalStepBranchS4_preserves_S4LoopInv` itself is at line 5044 (read it first --
reproduced in full context by the agent that wrote this handoff; it is a `refine`+`exact`
assembly with no independent proof content of its own, just twelve calls to the sub-lemmas
above with a `hinv` destructure via `obtain ⟨hbC, heN, heC, haF, haK, hoD, hkT, hkL, hkD, hkI⟩ :=
hinv` at the top).

### Recommended strategy

1. **Read every one of the twelve sub-lemmas' proofs FIRST** (not just signatures) before
   writing anything -- their exact case-analysis shape (which of them branch on
   `blockingWorldS4Keyed`, which only need the `.1`-shape without a mint-shape sub-case, etc.)
   determines how much of each proof transcribes mechanically vs. needs genuine new argument.
   `modalStepBranchS4_preserves_bClosure` (partially read already, see above) is representative
   of the HARDEST kind (mint-shape branch, blocking-world case split, two sub-cases with
   `modalApplyOneS4Keyed_boxNeg_{un}blocked_eq` bridges) -- expect several of the twelve to be
   this size.
2. For each sub-lemma, the SAME two-step adaptation Phase 5 used should apply:
   - Replace `unfold modalStepBranchS4Keyed at hstep0; obtain ⟨sf, hsfmem, hsf⟩ :=
     List.exists_of_findSome?_eq_some hstep0; split_ifs at hsf with hexp` with:
     `obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ := modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc
     keys newBs newExps newAcc keys' hstep` (Phase 4) applied to an
     `hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys = some (...)` hypothesis, followed by
     `unfold modalStepBranchS4KeyedBody at hsf; rw [if_neg (by simp [<hany-from-hsf_ne>])] at
     hsf` to reach the SAME "else-branch" shape the old proof's `split_ifs` produced. From there
     the REST of each sub-lemma's proof (the mint-shape/blocking-world reasoning, the
     `modalApplyOneS4Keyed`-vs-`modalApplyOne` bridges) is selection-independent and should
     transcribe with MINIMAL changes, since it never used "sf is the FIRST such formula in b",
     only "sf ∈ b, sf ∉ e, and this specific rule-application result".
   - Where the old proof does `rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with
     ⟨result, newAcc0⟩; rw [hpair] at hsf` (as `modalStepBranchS4_preserves_bClosure` already
     does, since `modalStepBranchS4Keyed`'s OWN body has the same concrete-not-abstract
     elaboration issue as `modalStepBranchS4KeyedBody` -- verify this is true for ALL twelve, it
     was true for the one read above), this step should transcribe completely unchanged.
3. **Escalation trigger, do not work around**: the plan explicitly flags that if
   `modalStepBranchS4_preserves_keysDistinct` (relying on `keysUpdate_preserves_keysDistinct`)
   or the guard's own `blockingWorldS4Keyed_none_fresh` need ANY weakening to go through for the
   ordered stepper, that CONTRADICTS the plan's central claim (that reordering is timing-only and
   never produces a duplicate key) and must be reported as a blocker, not patched around. Do this
   sub-lemma EARLY (it is a natural first target, independent of the mint-shape/blocking-world
   case-split machinery `bClosure`/`eClosure` need) so a genuine contradiction surfaces before
   investing effort in the other nine.
4. Confirm (do not re-derive) that `modalExpMeasure_entry_le_fuelS4` and the
   `modalKnownWorlds_length_le_worldBoundS4`/`modalStepBranchS4_worldBound` pigeonhole lemmas
   apply verbatim to the ordered stepper's output shape (they are stated at the entry point / in
   terms of `b`'s own content, not the traversal that produced it) -- per the plan's own
   guidance, only re-derive if verbatim reuse genuinely fails to typecheck.

### Naming convention to follow

Every Phase 6 declaration should carry the `S4KeyedOrdered` (or, matching the existing file's
established shorter convention for per-field helpers, `S4Ordered`) infix consistently with
Phases 4-5's naming (`modalStepBranchS4KeyedOrdered_*`), e.g.
`modalStepBranchS4KeyedOrdered_preserves_bClosure`, ...,
`modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` for the final wrapper. Do not silently
rename or restructure Phase 4/5's landed declarations to accommodate Phase 6's naming -- those
stay exactly as committed.

## Verification checklist for Phase 6 before committing

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` succeeds.
- `lean_verify` on every new declaration (all twelve sub-lemmas plus the wrapper): only
  `propext`, `Classical.choice`, `Quot.sound` in the axiom list, no `sorryAx`.
- `git grep -hE '^\s*sorry\s*$' -- 'Cslib'` still reads exactly 5.
- `modalStepBranchS4Keyed` and everything from Phases 1-5 still compiles unchanged (a full
  `lake build Cslib.Logics.Modal.Tableau.LoopChecking` covers this; also spot check
  `FrameCompleteness.lean`/`FrameSoundness.lean` still build).
- Explicit written confirmation (per the plan's own Phase 6 verification bullet) that no landed
  statement (`keysUpdate_preserves_keysDistinct`, `blockingWorldS4Keyed_none_fresh`, or any
  `S4LoopInv` field) was weakened -- or, if one genuinely needs to be, STOP and escalate rather
  than editing it.
- Mark `### Phase 6: ...` `[COMPLETED]` (or `[BLOCKED]` with a written blocker per
  `.claude/rules/plan-compliance.md` if the escalation trigger fires) in the plan file, commit as
  `task 553 phase 6: loop invariant and fuel-sufficiency chain`.
