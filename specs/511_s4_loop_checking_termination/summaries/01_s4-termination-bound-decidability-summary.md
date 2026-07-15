# Implementation Summary: Task #511 — S4 Loop-Checking Termination Bound & Decidability

- **Task**: 511 — s4_loop_checking_termination (follow-on to task 506, Phases 8-9)
- **Plan**: `specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md`
- **Status**: [PARTIAL] — Phases 1-4 landed green (self-contained); Phase 5 [BLOCKED] on a
  structural gap; Phases 6-7 not attempted (blocked by dependency on Phase 5)
- **Files changed**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean`
- **Zero-debt**: zero `sorry`, zero new `axiom` (repo-wide axiom count unchanged at 28), zero
  vacuous placeholders

## What Landed (Phases 1-4, all green, independently CI-verified)

1. **Phase 1 — Exponent fix**: `modalWorldBoundS4 φ₀` corrected from `2 ^ |Sf|` to
   `2 ^ (2 * |Sf|)`. `sameRelevantSet`/any birth-key notion distinguishes signs, so the
   pigeonhole codomain is `powerset(Sign × Sf)`, cardinality `2^(2|Sf|)`, not `powerset(Sf)`.
   `modalUniverseS4_length_le` re-verified unaffected in proof structure.

2. **Phase 2 — Finite signed-key infrastructure**: `signedSubfmls φ₀ : Finset (Sign ×
   Proposition Atom)` (the fixed codomain), `relevantSetFinset φ₀ b w` (the live relevant set
   restated as a `Finset`), plus `signedSubfmls_card_le`, `signedSubfmls_powerset_card_le`,
   `relevantSetFinset_subset_signedSubfmls`, `relevantSetFinset_mono`. Deviates from the plan's
   exact-equality (`=`) formulation to inequalities (`≤`), sufficient for the pigeonhole bound
   and avoiding an unproven `modalSubfmls`-nodup dependency.

3. **Phase 3 — Successor-birth-content guard redesign (fixes Gap 2 as specified)**:
   `successorBirthContent φ₀ b s φ w` (the prospective successor's birth content: witness +
   transmitted box-context, matching K's actual minting output) and `blockingWorldS4` (blocks
   on an existing known world's *current* relevant set matching the *prospective successor's*
   content, not the *source* world's own set — the literal fix for Gap 2). Guard-contract
   lemmas `blockingWorldS4_mem_modalKnownWorlds`/`_eq_birthContent`/`_none_fresh`. Rewrote
   `modalApplyOneS4` to consult the new guard; removed the superseded `blockingWorld` (no
   external consumers). All task-506 Phase 5-7 consumers (`hintikkaS4_box_pos_step` and its
   four siblings, `modalHintikkaSetS4`, `modalTruthLemmaS4` in `FrameCompleteness.lean`)
   re-verified unaffected, since their dependence is on the unchanged non-minting-shape
   agreement lemma.

4. **Phase 4 — Key-threaded S4 step + restated `S4LoopInv`**: `modalStepBranchS4Keyed`, an
   S4-specific one-step wrapper threading a `keys : List (WorldIndex × Finset (Sign ×
   Proposition Atom))` list alongside `(b, e, acc)` (appended on unblocked minting calls,
   unchanged otherwise). `S4LoopInv` restated: the structurally-unsound `worldSetsDistinct`
   field removed, replaced with `keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse` over
   the threaded `keys`.

## Phase 5 — [BLOCKED]: A Structural Gap in the Birth-Key Guard Design

Before writing any Phase 5 Lean code, the intended proof of `_preserves_keysDistinct` (the
plan's own flagged "highest-risk sub-lemma") was formalized on paper and found to be
**mathematically insufficient**, not merely difficult to close in Lean:

- The available combination — `blockingWorldS4_none_fresh` (`relevantSetFinset φ₀ b w' ≠
  newkey` for every known `w'`) plus `S4LoopInv.keyLowerBd` (`oldkey(w') ⊆ relevantSetFinset
  φ₀ b w'`) — does **not** imply `oldkey(w') ≠ newkey`. If `oldkey(w')` is a *proper* subset of
  `w'`'s current (grown) relevant set — the expected, common case once ordinary
  propositional/modal saturation proceeds at `w'` — then `oldkey(w') = newkey ⊊
  relevantSetFinset(w')` is fully consistent with the guard having found no match and passed.
- **Concrete scenario**: world `A` is minted with birth key `{a}`. Ordinary saturation later
  grows `A`'s live relevant set to `{a, b}`. A fresh world `B` is later minted whose prospective
  content also computes to `{a}`. The guard compares against `A`'s *current* set `{a, b} ≠
  {a}` — no match, doesn't block. `B` is minted with key `{a}` = `A`'s key. `keysDistinct` is
  violated the instant `B`'s key is recorded.
- **Root cause**: the guard compares the prospective content against worlds' *live, growing*
  relevant sets, but the invariant that must be preserved is about *stable, historical* birth
  keys. A guard comparing against live sets cannot, in general, guarantee distinctness of a
  disjoint, non-shrinking key history.
- **What would fix it**: `blockingWorldS4` needs to compare against the **recorded `keys`
  list** directly, not against live `relevantSetFinset` values. This is a structural redesign,
  not an incremental one: `modalApplyOneS4`'s type is a plain `RuleApply Atom` (no `keys`
  parameter), and it is directly consumed — unparametrized by `keys` — by
  `modalHintikkaSetS4`/`modalTruthLemmaS4` and all five task-506 bridge lemmas, all already
  shipped. Threading `keys` into the guard requires either bypassing `modalApplyOneS4`'s own
  minting-shape dispatch inside `modalStepBranchS4Keyed` (computing a keys-aware decision there
  instead) while leaving the live-set-guarded `modalApplyOneS4`/task-506 proofs as a separate,
  still-valid artifact, or introducing a new keyed rule-application variant and re-deriving the
  506 Hintikka/truth-lemma bridges against it. Either path is comparable in scope to the Phase 9
  driver work the plan already flags as warranting its own task.
- **Full documentation**: `specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md`,
  Phase 5 section (marked `[BLOCKED]`).
- **No workaround taken**: no `sorry`, no vacuous placeholder, no weakening of `keysDistinct`
  (e.g. restricting it to saturated worlds only, which would silently reintroduce something
  close to the research report's documented Option B fallback without disclosing the
  substitution).

Phases 6 (pigeonhole world bound) and 7 (Phase 9 decidability) were **not attempted**: both
depend on Phase 5 per the plan's wave analysis (Phase 6 depends on 5, 2; Phase 7 depends on 6),
and Phase 6's argument specifically requires `keysDistinct` to hold as a genuine loop invariant
to establish the injective-map pigeonhole bound.

## Plan Deviations

- Phase 2: `signedSubfmls_card`/`signedSubfmls_powerset_card` proved as `≤` rather than the
  plan's stated `=` (documented inline in the plan; sufficient for the pigeonhole use, avoids
  an unproven `modalSubfmls`-nodup dependency).
- Phase 2: `relevantSetFinset_subset_signedSubfmls` needed no `modalUniverseS4`-closure side
  condition (the plan anticipated one); it is unconditional by construction
  (`relevantSetFinset` is defined as a `Finset.filter` of `signedSubfmls φ₀`).
- Phase 3: no separate bridge lemma from `modalStepBranchS4Keyed` to `modalStepBranchS4` was
  proved (not required for Phase 4's "compiles green" deliverable; would have been needed only
  if Phase 5 proceeded to consume it, which it did not reach).
- Phase 5: marked `[BLOCKED]` with a structural (not merely proof-engineering) gap; Phases 6-7
  not attempted as a consequence.

## Verification

- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` — green, no new warnings beyond the
  pre-existing (task-506) `unusedDecidableInType` note on `modalUniverseS4_length_le`.
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` — green, no new warnings; all
  task-506 Phase 5-7 consumers unaffected.
- `lake exe checkInitImports` — clean.
- `lake exe lint-style` — clean.
- `lake lint` — no findings in either touched file.
- `lake shake --add-public --keep-implied --keep-prefix` — no import-minimization findings in
  either touched file (new public `Mathlib.Data.Finset.*` imports required by the module's
  privacy system for `Finset` field-projection notation).
- `lake test` — full `CslibTests` suite passes (pre-existing `sorry` warnings in unrelated
  `Propositional/Tableau/*` files, untouched by this task).
- `lean_verify` on `blockingWorldS4_none_fresh` and `signedSubfmls_powerset_card_le`: only the
  standard axiom trio (`propext`, `Classical.choice`, `Quot.sound`).
- `grep -rn "^axiom " Cslib/ | wc -l` → 28 (unchanged from baseline).

## Next Steps for a Follow-On Task

A follow-on task should redesign the S4 minting guard to compare against **recorded birth
keys**, not live relevant sets, per the Phase 5 blocker documentation above. This is best
scoped as its own task (comparable in size to the Phase 9 driver work already flagged for
separate spawning), since it requires either a keys-aware bypass inside a redesigned stepper
or a new rule-application variant with its own re-derived Hintikka/truth-lemma bridges. Once
that redesign lands, Phase 5's remaining preservation lemmas (`keyLowerBd`, `keysTotal`,
`keysInUniverse`, and the final assembly) and Phases 6-7 of this plan become tractable again;
Phases 1-4 of this task's plan remain valid infrastructure to build on (in particular
`signedSubfmls`/`relevantSetFinset`/`successorBirthContent`/the exponent-corrected
`modalWorldBoundS4` all remain correct and reusable).
