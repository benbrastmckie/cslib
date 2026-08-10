# Handoff: Phase 8 COMPLETE -- `openBranch_countermodel` discharged, sorry-free

**Task**: 609 - Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows.
**Plan**: `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/plans/01_beta-priority-repair.md`
**Phase**: 8 ("Discharge `openBranch_countermodel`") -- now `[COMPLETED]`.

## What this dispatch did

At dispatch start, task 605 was `[COMPLETED]` and had already landed its shape-fix patch: the
three-conjunct existential (`huc`/`hbuc`/`hcm`) was the live signature of `openBranch_countermodel`,
and its body was a single `sorry`. This dispatch discharged that `sorry` entirely.

1. **Committed to the AUGMENTED `augSets` witness.** Called `intExpandBranches_openBranch_sat`
   with the same specific entry-state arguments `openBranch_rawEdges_upward_closed` already uses,
   obtaining `edges` (the augmented accumulator), `hsat`, `hfimp`, and Phase 7's 7th conjunct
   `hpersAug` (χ-general positive persistence over that frame). `hopen` came from the existing
   (already-landed) `intExpandBranches_openBranch_closed`; `hFmem : F(φ)@0 ∈ b` came from the
   existing `intExpandBranches_openBranch_initial_mem` -- both private helpers already present in
   the file, reused verbatim.

2. **Conjunct 3** (`¬IForces`): `(truthLemma S b edges hopen hsat hfimp hpersAug φ 0).2 hFmemAny`
   -- a direct instantiation, no new machinery needed.

3. **Conjuncts 1/2** (valuation and `S.modelBot` upward-closure): both are χ-general
   instantiations of `hpersAug` (at `χ := .atom p` and `χ := HasBot.bot` respectively),
   tail-peeled along the `intAccessPreorder edges` `ReflTransGen` chain via `induction hle`,
   mirroring `openBranch_rawEdges_upward_closed`'s own proof shape exactly (same
   membership/`List.any` conversion dance).

4. **New structure field `IntMinScheme.modelBot_uc`** (the one genuine deviation from the plan's
   literal task list). The plan's Phase 8 text assumed `hbuc` could be "sourced from 605's
   `openBranch_rawEdges_both_upward_closed`" -- but that lemma proves `minBranchBotForces`
   upward-closure specifically, at `rawEdges`, not `S.modelBot` upward-closure for an ABSTRACT
   `S : IntMinScheme Atom`. Investigation established this is not a gap in effort but a genuine
   mathematical obstruction: `IntMinScheme.bot_truth` relates `modelBot` to branch content in only
   ONE direction (`T(⊥)@w ∈ b → modelBot b w`), never the converse, so recovering `T(⊥)@w ∈ b` from
   `modelBot b w` -- needed to chain `hpersAug` forward to `w'` -- is not available for an arbitrary
   `modelBot` without an independent totality/bivalence fact (the file explicitly documents no such
   fact is established, see the STOP-gate note above `truthLemma`). Added `modelBot_uc` as a new
   field: it takes a step-relation-level persistence witness for the `⊥` shape (matching
   `hpersAug`'s χ-general conclusion instantiated at `χ := HasBot.bot`) as a HYPOTHESIS, and
   concludes `modelBot` upward-closure along that step relation's `ReflTransGen` closure.
   `intScheme` discharges it trivially (`modelBot ≡ fun _ _ => False`, hypothesis vacuous).
   `minScheme` discharges it by unfolding `minBranchBotForces` to branch-membership form and
   applying the persistence witness directly, via the same tail-peeling proof shape used
   elsewhere in the file. This is purely ADDITIVE to `IntMinScheme` -- both existing instances
   updated, `openBranch_countermodel`'s own parameter list unchanged (matching the plan's Scope
   Hypothesis that 605's patch only touches the conclusion shape), and no other call site
   affected.

5. **Docstring rewrite.** The long frame-adequacy table used to assert augmented-frame positive
   persistence was REFUTED and the residual obligation was open. Rewrote it to record that
   history explicitly (kept as a "historical record" table row) while stating plainly that the
   augmented frame now carries BOTH `IFimpAccess` and positive persistence simultaneously
   post-repair, and that `rawEdges` remains (unaffected) REFUTED for `IFimpAccess`. The
   `## Proof structure` section was rewritten from "currently a single `sorry`" to a description
   of the actual sorry-free proof.

## Verification (full pipeline, one commit)

- `lake build` (scoped then full, 3325 jobs): green. No warnings from `Scheme.lean`.
- `lake exe checkInitImports`: clean.
- `lake lint`: zero findings attributable to `Scheme.lean` (confirmed via both the general run and
  the 7-category prevention grep).
- `lake exe lint-style`: clean.
- `lake shake --add-public --keep-implied --keep-prefix`: no suggestion for `Scheme.lean`.
- `lake exe mk_all --module`: "No update necessary".
- `lake test`: green, 9397 jobs, exit 0, zero `✖` marks.
- Declaration-level sorry count (whole repo, via `lake build`'s `declaration uses sorry`
  warnings): **2 → 1**. The one remaining is `Intuitionistic/Completeness.lean:181`
  (`intuitionisticTableau_complete`), explicitly Phase 9's territory and untouched here.
- Axiom count: 26 → 26 (unchanged). Vacuous-definition grep: 1 → 1 (unchanged, pre-existing
  `Computability/URM/Basic.lean` false positive).
- `lean_verify` on `openBranch_countermodel`, `tableau_complete`, and `minimalTableau_complete`:
  all report axioms `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.
- Confirmed via a genuinely fresh `lake build` after edits (not just LSP diagnostics) before
  concluding the sorry was discharged, per the dispatch instructions' caution about stale
  `lean_verify` cache artifacts.

## Territory

Edited exactly 605's declared territory (the `IntMinScheme` structure, `intScheme`/`minScheme`
instances, and `openBranch_countermodel` at the end of `Scheme.lean`) plus its own docstring.
Did not touch `Expansion.lean`, `Completeness.lean` (either file), or
`Minimal/DecisionProcedure.lean`.

## Excluded constructions

Did not re-attempt any of the task's excluded constructions (rawEdges as the conjunct-2 witness,
pruning at blocked/strictly-blocked worlds, the greatest `IFimpAccess`-supported fixpoint, the
maximal atom-inclusion frame) -- all remain refuted, unchanged, and are recorded as history in
the rewritten docstring rather than re-derived.

## Next steps: Phase 9

Phase 9 ("The downstream `Completeness.lean` sorries and the 606 handoff") is `[NOT STARTED]`,
depends on Phase 8 (now satisfied). Its scope: discharge `intuitionisticTableau_complete`
(`Intuitionistic/Completeness.lean:170`, the ONE remaining declaration-level sorry in the whole
repo as of this dispatch) and leave task 606 an accurate handoff. See the plan's Phase 9 section
for the full task list -- not attempted here, per this dispatch's explicit one-phase scope.
