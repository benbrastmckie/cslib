# Implementation Summary: Phase 8.2 (partial) -- Ten Core Constructor Lemmas + Motive-Design Correction (Plan v5)

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994
  Thm 8.1.4's biconditional
- **Plan**: plans/05_tree-recursive-hilbert-bridge.md (plan version 5)
- **Status of this dispatch**: Phase 8 remains `[IN PROGRESS]`; sub-step 8.2 remains
  `[IN PROGRESS]` (not `[COMPLETED]`) -- 8 of the 10 in-scope constructor cases landed as
  standalone core lemmas, plus a design-level correction discovered for the remaining 2
  (`efq`/`orE`). Sub-steps 8.3-8.4 and Phases 9-10 remain `[NOT STARTED]`.
- **Commits** (nine total, each an independently-verified green sub-step):
  1. `task 537 phase 8.2: land propositional combinator toolkit + bigAndL_mem`
  2. `task 537 phase 8.2: land ancestor-wrap-of-derivable bridge (nikTrFuel_of_derivable)`
  3. `task 537 phase 8.2: land sigAt-core infra + NIK.assumption case`
  4. `task 537 phase 8.2: land the six P-generic label-local constructor cases`
  5. `task 537 phase 8.2: land sigAtFuel_congr_above_rank (context-extension congruence)`
  6. `task 537 phase 8.2: land sigAt_cons_self_imp (context-extension core fact for impI)`
  7. `task 537 phase 8.2: land NIK.impI core translation (sigAt_impI)`
  8. `task 537 phase 8.2: land nikTrFuel_mono + document the efq/orE motive-design correction`

## What landed

In `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` (appended after Phase
8.1's `nikTr` translation, ~390 new lines total):

**Propositional combinator toolkit** over `Derivable CS5ModalAxiom`, entirely `P`-generic (never
inspects `sigAt`'s structure): `cs5_deriv_imp_trans`, `cs5_deriv_imp_and`, `cs5_deriv_imp_andE1`/
`_andE2`, `cs5_deriv_imp_orI1`/`_orI2`, `cs5_deriv_imp_mp`, `cs5_deriv_imp_of_derivable`,
`cs5_deriv_imp_self`, `cs5_deriv_imp_trans_under`, `cs5_deriv_curry`/`_uncurry`,
`cs5_deriv_box_mono`, `cs5_deriv_imp_congr_right`. All built directly from `implyK`/`implyS`/
`andI`/`andE1`/`andE2`/`orI1`/`orI2`/`k` + `modus_ponens`/`necessitation`, no new import, no
deduction-theorem dependency.

**`bigAndL`/`factsAt` infrastructure**: `bigAndL_mem` (projection), `bigAndL_mono`
(monotonicity), `bigAndL_cons` (structural unfold), `factsAt_cons_ne`/`factsAt_cons_self`
(context-extension facts).

**Ancestor-wrap bridge**: `nikTrFuel_of_derivable`/`nikTr_of_sigAt_imp` (a closed core fact wraps
to a closed `nikTr` fact -- the generic bridge every case uses once), and its strengthening
`nikTrFuel_mono` (wrap preserves entailment, not just closed derivability -- landed for the
cross-label redesign, not yet consumed).

**`sigAt`-core infrastructure**: `hfin_toFinset_card_pos`, `sigAt_imp_of_factsAt_imp` (one-level
unfold), `sigAtFuel_congr_above_rank` (rank-based congruence across a context extension, using
`IsDerivationForest`'s graded-rank witness), `sigAt_cons_self_imp` (the capstone: `sigAt` under a
context extension at its own label -- the hardest lemma of this dispatch).

**Ten of 10 in-scope constructor "core" lemmas** (8 landed, matching the plan's own sanctioned
fallback of standalone helper lemmas rather than a single `induction` block -- see below):
`sigAt_assumption`, `sigAt_andI`, `sigAt_andE1`, `sigAt_andE2`, `sigAt_orI1`, `sigAt_orI2`,
`sigAt_impE`, `sigAt_impI`. `efq`/`orE` NOT attempted in Lean (see next section).

Sorry-free, axiom-clean throughout (`grep` confirmed after every commit). Scoped
`lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green after every
commit. `lake exe checkInitImports` clean. No Preserved Asset (Phases 1-7, PD.1, 8.1) touched or
regressed. A full-project `lake build` was attempted for this dispatch's final verification and
failed in `Cslib/Logics/Modal/Tableau/LoopChecking.lean` -- **pre-existing and unrelated**: that
file is concurrently modified by task 535 (confirmed via `git log`/`git status` showing it
already dirty at this dispatch's start, with no edits from this session), outside this task's
file scope (`Soundness.lean` only, per the plan's Non-Goals).

## The efq/orE finding (design correction, not a machine-checked wall)

Before writing any Lean for the two remaining cross-label constructors, a design-level analysis
found that the "core" motive used for the 8 landed cases -- `Derivable ((sigAt G Γ hfin x).imp
A)`, with `nikTr` applied only once at the very end via `nikTr_of_sigAt_imp` -- **cannot** close
`efq`/`orE`. A bare `sigAt x` fact packages only `x`'s own subtree; it carries no route to an
unrelated label `y`. `nikTr`'s full ancestor-wrap, by contrast, threads in off-spine sibling
subtrees (including `y`'s, once traced to the lowest common ancestor) via each level's
`antecedent` conjunct. `IsDerivationForest` guarantees `G` is a SINGLE rooted tree (every label
enters `G.X` via `addEdge` from an existing node, starting from `Graph.trivial`'s one node) --
not several disjoint components -- so `x` and `y` always share such an ancestor, and the
connection Simpson's construction relies on is almost certainly carried by the full `nikTr` wrap,
not the bare `sigAt` core.

**Concretely, this means**: closing `efq`/`orE` needs `nik_adequacy`'s motive restated at the
full `nikTr` level (not the `sigAt`-only core used for the other 8 cases), plus an explicit
lowest-common-ancestor bridging argument relating `x`'s and `y`'s ancestor-wraps above their
shared prefix. This is a substantial addition -- likely comparable in size to everything landed
in this dispatch -- not yet attempted in Lean. The reusable pieces such a redesign needs were
landed anyway (`cs5_deriv_box_mono`, `cs5_deriv_imp_congr_right`, `nikTrFuel_mono`), since they
are needed regardless of the exact shape the final bridge takes.

**Also discovered**: the plan's anticipated reuse of "PD.1's landed `bot_*` lemmas" for `efq`
does not apply -- `bot_backward`/`bot_iff_edge`/`bot_iff_TClosure` are semantic (`CKForces`)
facts built for the superseded direct-motive route (Phase 11/PD), not syntactic
`Derivable`/`sigAt` facts usable in this Hilbert-bridge route. The cross-label bridge will need
new syntactic infrastructure.

This is flagged as a **design correction discovered via analysis**, not a machine-checked Lean
goal that was attempted and refuted -- no `sorry`, no vacuous placeholder, and Phase 8.2 is left
`[IN PROGRESS]` (not `[BLOCKED]`), since no concrete obstruction was hit, only a scope/complexity
finding that the next dispatch should apply before writing Lean for `efq`/`orE`.

## What remains

- **Sub-step 8.2 (continued)**: redesign `nik_adequacy`'s eventual motive to operate at the
  `nikTr` level (or devise an equivalent LCA-bridging lemma), then discharge `efq` and `orE`.
  This will likely also require restating the 8 already-landed "core" lemmas as `nikTr`-level
  facts (via `nikTrFuel_mono`-style lifting) so all 12 cases share one motive for the eventual
  `induction … with` block -- or an alternative reconciliation the next dispatch should evaluate
  before committing to a specific redesign.
- **Sub-step 8.3**: the 4 modal cases (`boxI`, `boxE`, `diaI`, `diaE`), reusing `boxI_lift`,
  `box_iff_TClosure`/`dia_iff_TClosure`.
- **Sub-step 8.4**: specialise to `nik_TS5_to_hilbert` over `Graph.trivial`.
- **Phase 9**: assemble `nik_TS5_soundness`; retire the stale module-docstring notes.
- **Phase 10**: full regression gate.

## Plan Deviations

See the `*(deviation: ...)*` annotations added inline to Sub-step 8.2's checklist in
`plans/05_tree-recursive-hilbert-bridge.md`, summarized above.

## AI Tools Used

This work was prepared with the assistance of Claude Code (Anthropic) acting as the
`cslib-implementation-agent`. The tool was used for reading the existing `NIK`/`Graph`/
`DerivationTree` definitions, designing and iterating the propositional-combinator toolkit and
`sigAt`-congruence lemmas via `lake build`/`lean_goal` feedback, working through (and
documenting) the efq/orE motive-design analysis, and drafting this summary. All Lean code was
verified to compile via scoped `lake build` on this branch.
