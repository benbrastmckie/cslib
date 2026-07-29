# Implementation Summary: Shared Tableau Containment Blocking

- **Task**: 456 - shared_tableau_containment_blocking
- **Plan**: plans/01_blocking-module-plan.md
- **Status**: [COMPLETED] — all 5 phases done
- **Session**: sess_1785275816_a84520_456

## What Was Built

A shared, logic-agnostic containment-blocking module for tableau calculi, plus the
redirection of the Temporal tableau onto it.

### Cslib/Foundations/Logic/Tableau/Blocking.lean (new, ~200 lines, zero sorry)

Namespace `Cslib.Logic.Tableau`:

- **Definitional layer** (Phase 1): `Branch.typeAt`, `Branch.posTypeAt`,
  `Branch.containmentBlocked`, with membership/iff specification lemmas
  (`mem_typeAt_iff`, `containmentBlocked_iff`).
- **Counting layer** (Phase 2): `card_image_le_pow_of_forall_subset` (powerset-card
  bound), `toFinset_eraseDups` (bridge), the corrected `distinctTypes_le_pow`
  (distinct label types bounded by `2 ^ n`), `exists_typeAt_eq_of_card_lt`
  (pigeonhole: some two labels share a type once the label count exceeds the bound),
  and `strictChain_le_card` (strict-chain length bound, the Dershowitz-Manna-style
  chain argument).

Axiom audit via `lean_verify`: both `distinctTypes_le_pow` and `strictChain_le_card`
rest only on `propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`, no new axioms.

### Cslib/Logics/Temporal/Tableau/Branch.lean (Phase 3)

`timeType` / `isSubsetBlocked` redirected onto the shared Blocking layer as defeq
wrappers with `rfl` bridging lemmas. All 24 temporal conformance rows in
`CslibTests/TableauConformance.lean` pass unchanged.

### references.bib (Phase 4)

- Added `DershowitzManna1979` (CACM 22(8):465-476, doi 10.1145/359138.359142).
- Enriched `GargGenoveseNegri2012` in place with pages 315--324 and
  doi 10.1109/LICS.2012.42. No duplicate keys.

### Cslib.lean barrel (Phase 5)

`lake exe mk_all --module` registered
`public import Cslib.Foundations.Logic.Tableau.Blocking` (one-line diff).

## Phase 5 CI Gate Results

| Gate | Result |
|------|--------|
| `lake exe mk_all --module` | Barrel updated, +1 line |
| `lake exe checkInitImports` | exit 0 |
| `lake build` (full) | exit 0, 3311 jobs |
| `lake exe lint-style` | exit 0, repo-wide clean |
| `lake shake --add-public --keep-implied --keep-prefix` | Task files clean: Blocking.lean, Temporal Branch.lean, barrel not flagged. Exit 1 from 9 pre-existing-drift files (TimeM, Turing, StackTape, Relation Defs/Confluence, Monad Free, CCS, CombinatoryLogic) — none touched by this task |
| `lake lint` | Task files clean: zero findings on Blocking.lean and Temporal Branch.lean (the anticipated unusedArguments hit was pre-empted by trimming the unused `[LawfulBEq L]` instance from `containmentBlocked_iff`). Exit 1 from 145 unusedArguments errors across 26 pre-existing-drift modules (Bimodal, Modal FrameSoundness, Temporal Chronicle/DenseSoundness, LTL, etc.) — none touched by this task |
| `lake test` | exit 0, 9376 jobs, CslibTests incl. TableauConformance green |
| Zero-sorry sweep (task files) | `grep sorry` over Blocking.lean, Temporal Branch.lean, references.bib: no matches |

Sorry warnings visible during build/test belong to concurrent tasks
(Modal FrameSoundness, Intuitionistic/Minimal Completeness) and are outside this
task's scope per the dispatch contract.

## What This Unblocks

- The world-bound route for the tableau termination work: `distinctTypes_le_pow`
  gives the `<= 2 ^ n` distinct-type bound and `strictChain_le_card` the chain-length
  bound that the Temporal soundness obligation consumes.
- Any future tableau calculus can reuse the shared containment-blocking layer
  instead of re-deriving per-logic counting arguments.

## Plan Deviations

- None of substance. Phase 5 executed exactly the plan's gate list; shake and
  lint findings are confined to files this task never touched (contract-sanctioned
  known repo drift), so no shake-driven import trims were needed — this task's
  imports were already minimal.
