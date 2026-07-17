# Phase 5 Continuation Handoff — `keyLowerBd` and `keysInUniverse` driver-level lemmas closed

## What this dispatch closed

- `modalStepBranchS4_preserves_keyLowerBd` — the driver-level lemma the PRIOR dispatch left as
  "pure mechanical casework" (every mathematical ingredient closed, only the `sf.sign`/
  `sf.formula` case-split assembly missing). Now fully assembled and green, zero sorry, zero new
  axiom.
- `modalStepBranchS4_preserves_keysInUniverse` — not previously attempted; closed in this
  dispatch, simpler than `keyLowerBd` since it does not depend on the output branch `newBs` at
  all.
- `modalHintikkaSetS4_eq` — Phase 7's cheap, independent Hintikka-alignment bridge (`rfl`,
  mirrors `Saturation.lean`'s `modalHintikkaSet_eq`). Lands regardless of Phase 5/6's state.
- Reusable helpers: `modalStepBranchS4Keyed_result_keys_eq` (generic `keys'` extraction that
  factors the `RuleResult` 4-way case split out of all 9 `sf.sign`/`sf.formula` leaves — `keys'`
  never actually depends on which `RuleResult` shape occurred) and
  `successorBirthContent_subset_signedSubfmls`.

**S4LoopInv's 4 key fields status**: `keysDistinct` (prior dispatch) + `keyLowerBd` +
`keysInUniverse` (this dispatch) = **3 of 4 CLOSED**. Only `keysTotal` remains.

## Technique that made the assembly tractable

The prior dispatch's blocker worried about a "9 leaves × up to 4 `RuleResult` shapes" case
explosion. The key simplification: `modalStepBranchS4Keyed`'s `keys'` local variable is computed
by a match on `sf.sign, sf.formula` **only** — it never inspects `result` at all (only the
`(newBs, newExps, newAcc)` triple depends on `result`'s shape). So the `RuleResult` 4-way split
was factored into ONE reusable lemma (`modalStepBranchS4Keyed_result_keys_eq`) that extracts
`keys' = keysLocal` generically, regardless of which `RuleResult` shape occurred. After that,
the main lemma only needs a SINGLE `sf.sign, sf.formula` case split (`rcases hs : sf.sign with _
| _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ`, 14 goals via the cross product,
but Lean auto-generates dotted case tags like `case neg.pos.diamond` from the nested `rcases`,
letting `all_goals first | exact hold ... | skip` close 12 of them uniformly and leaving exactly
2 named goals (`case neg.neg.box` / `case neg.pos.diamond`) for explicit minting-specific
handling via `case ... => ...` blocks).

For the 2 minting-unblocked sub-cases, `newForms` is pinned exactly by chaining
`modalApplyOneS4Keyed_boxNeg_unblocked_eq`/`_diaPos_unblocked_eq` (already-landed guard-spec
lemmas) with `modalApplyOne_boxNeg_mint_fst_S4`/`_diamondPos_mint_fst_S4` (already-landed
literal-payload lemmas), then re-deriving `newBs`'s exact singleton value from `hsf` (the SAME
extraction technique `modalStepBranchS4Keyed_branch_superset` already used, just applied once
more with `result` now pinned to a literal `.linear newForms0` instead of left symbolic).

## What remains open, and why it is a genuinely new piece of work (not casework)

`modalStepBranchS4_preserves_keysTotal` needs, for the 7 non-minting `sf.sign`/`sf.formula`
leaves, a fact neither `keyLowerBd` nor `keysInUniverse` needed: that `modalKnownWorlds b'`
introduces **no label beyond `modalKnownWorlds b`** at those leaves. Tracing the S4 rule layers
(`FrameRules.lean`) confirms this is TRUE but requires new infrastructure to formalize:

- `atom`/`bot`/`imp`/`and`/`or` (`tryAllPropRules`): outputs stay at `sf.label`. Easy.
- `box`-pos/`diamond`-neg (T self-propagation via `modalTBoxSelf`/`modalTDiaNegSelf`): outputs
  stay at `sf.label`. Easy.
- The 4-rule propagation (`modalFourBoxProp`/`modalFourDiaNegProp`): outputs land at `w' ∈
  acc.successorsOf sf.label` — known only given `accTargetsKnown b acc` (`S4LoopInv.accKnown`)
  as an EXTRA threaded hypothesis, plus a `successorsOf → hasEdge` bridge (private
  `mem_successorsOf_hasEdge` in `FmpMeasure.lean`; a local S4 re-derivation is needed, mirroring
  `FrameSoundness.lean`'s `mem_successorsOf_hasEdge'` / `S5Simplification.lean`'s
  `mem_successorsOf_hasEdge_S5` — no `_S4` version exists yet).

No "known-worlds dichotomy" lemma exists yet for `modalApplyOneS4Rules`/`modalApplyOneS4Keyed`.
The base K rule has one (`modalApplyOne_knownWorlds_step`, `FmpMeasure.lean`), and S5/Five have
their own analogues (`modalApplyOneS5_knownWorlds_step`/
`modalApplyOneFiveProp_knownWorlds_step`) — S4 does not, because S4 layers THREE rule sets (K,
T, 4) rather than S5/Five's flatter structure. Building the S4 analogue is realistically
comparable in scope to `keyLowerBd`'s own closure (this dispatch and the prior one combined),
not a quick follow-on.

Separately: the full `modalStepBranchS4_preserves_S4LoopInv` assembly also needs the SIX
"rule-independent" fields (`bClosure`, `eNodup`, `eClosure`, `accFresh`, `accKnown`, `outDegEq`)
proven preserved for `modalStepBranchS4Keyed` specifically. Generic preservation lemmas already
exist for `modalStepBranchGen apply` (`modalStepBranch_preserves_accFreshInv_gen`,
`modalStepBranchGen_preserves_outDegEq`, `modalStepBranch_preserves_accTargetsKnown_gen`,
`FmpMeasure.lean`/`Soundness.lean`), but `modalStepBranchS4Keyed` is NOT literally
`modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys) b e acc` (it returns a 4-tuple with `keys'`
bolted on, the generic driver returns a 3-tuple) — a bridge lemma is needed first. This bridge
was not attempted this dispatch (plausible, likely mechanical given the two definitions' close
structural resemblance, but unverified).

## What is needed (concrete plan for a continuation dispatch)

1. Build `mem_successorsOf_hasEdge_S4` (mirror `mem_successorsOf_hasEdge_S5`/
   `mem_successorsOf_hasEdge'`).
2. Build `mem_modalKnownWorlds_S4` (a local re-derivation of `FmpMeasure.lean`'s private
   `mem_modalKnownWorlds`, mirroring `BDriver.lean`'s `mem_modalKnownWorlds_B`).
3. Build an S4Keyed known-worlds-step dichotomy lemma composing K/T/4 (mirror
   `modalApplyOneS5_knownWorlds_step`'s proof shape, layered through `modalApplyOneT`/
   `modalFourBoxProp`/`modalFourDiaNegProp`).
4. Use (1)-(3) to close `modalStepBranchS4_preserves_keysTotal` (reuse the SAME `hkeq`/case-split
   assembly skeleton `keyLowerBd`/`keysInUniverse` already used — that part IS mechanical once
   the dichotomy exists).
5. Build the `modalStepBranchS4Keyed`-to-`modalStepBranchGen` bridge lemma; reuse the six
   existing generic preservation lemmas for the rule-independent fields.
6. Assemble `modalStepBranchS4_preserves_S4LoopInv`.
7. Proceed to Phase 6 (pigeonhole world bound — genuinely cannot start before `keysTotal` closes,
   since `modalKnownWorlds_length_le_worldBoundS4`'s injective map IS `keysTotal`'s own witness)
   and then Phase 7's remaining decision-recording + closure/block tasks.

## Verification

`lake build Cslib.Logics.Modal.Tableau.LoopChecking` green (scoped); `lake exe
checkInitImports`, `lake exe lint-style`, `lake lint` (scoped) all clean — only the pre-existing,
unrelated `modalUniverseS4_length_le` unused-hypothesis warning remains, predating this
dispatch. Zero sorry, zero new axiom (`lean_verify` on `modalStepBranchS4_preserves_keyLowerBd`,
`modalStepBranchS4_preserves_keysInUniverse`, `modalStepBranchS4Keyed_result_keys_eq`,
`modalHintikkaSetS4_eq`: `propext`/`Classical.choice`/`Quot.sound` only).

## Unrelated observation (confirmed, not investigated further per dispatching constraints)

`lake test` fails on `CslibTests/ModalFrameSeparation.lean` (`decide` stuck reducing
`instDecidableFiveValid`). Confirmed via `git log`/`git status` to be entirely task 515's S5/Five
decidability work, unrelated to any file this task touches. Not a regression from this dispatch;
out of scope per the dispatching teammate's explicit instruction.
