# Implementation Plan: Reconcile Connectives.lean against merged Operators.lean

- **Task**: 619 - Reconcile Foundations/Logic/Connectives.lean against merged upstream Operators.lean
- **Status**: [NOT STARTED]
- **Effort**: 11 hours
- **Dependencies**: None
- **Research Inputs**: `specs/619_reconcile_connectives_operators/reports/01_connectives-operators-reconciliation.md`
- **Artifacts**: plans/01_reconcile-connectives-operators.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Upstream PR #607 merged `Cslib/Foundations/Logic/Operators.lean`, which declares nine operator
typeclasses and their scoped notation in `namespace Cslib.Logic`. This fork independently declares
four of those same classes (`HasAnd`, `HasOr`, `HasImp`, `HasBox`) in `Connectives.lean`, plus
`HasDia` where upstream says `HasDiamond`. The reconciliation adopts upstream's declarations
wholesale, migrates the fork to the `HasDiamond` name, and keeps the fork-only classes and bundles
as the upstreamable delta. Definition of done: `Operators.lean` is present verbatim, `Connectives.lean`
is a delta over it, and the full CSLib CI pipeline is green.

The task is not sized by edit count. The edits total roughly 12 deleted notation lines, 5 deleted
class declarations, a rename across 6 code sites, and 12 new `rfl` bridge lemmas. The cost is
verification across 201,583 lines in 488 files, so phases are ordered by build cost and gated
per-module smallest-first.

### Research Integration

The research report is fully integrated. Four findings drive the phase structure:

1. The four named duplicates are field-for-field identical, so adopting upstream's costs **zero**
   call-site edits across all 1,802 references.
2. The load-bearing collision is **notation, not classes**: upstream's scoped notation lives in
   `Cslib.Logic`, an enclosing namespace of the fork's `Cslib.Logic.{PL, Modal, Bimodal, Temporal,
   LTL}`, so both interpretations elaborate and Lean raises a hard `Ambiguous term` error at exactly
   12 measured sites in 5 files.
3. Every other fork notation is clean *because the corresponding instance is absent* — a latent trap
   that must be recorded as a standing invariant in the module docstring.
4. `Operators.lean` does not exist locally and `b8ad3923` is not an ancestor of `HEAD`, so the
   "verify with `lake build`" criterion forces vendoring as the first phase.

**Correction to the report, measured against the live tree.** Report §2.2 and §5.2 estimate the
optional `AxiomDiaDuality` -> `AxiomDiamondDuality` rename at "4 sites / Low impact". The actual
census is:

| Identifier | Occurrences |
|---|---:|
| `AxiomDiaDuality` | 1 |
| `AxiomDiaDualityFwd` | 36 |
| `AxiomDiaDualityBack` | 37 |
| `diaDuality` (field) | 2 |
| `diaDualityFwd` (field) | 61 |
| `diaDualityBack` (field) | 61 |
| **Total identifier occurrences** | **198** |
| **Files touched** | **25** |

That is roughly fifty times the report's estimate, and it lands entirely inside the Modal metalogic
subtree (the largest at 83,504 lines). The rename is still mechanical and still recommended for
naming consistency, but it is isolated into its own late phase (Phase 9) so it can be excluded
without invalidating any earlier phase.

**Second departure from the report's recommended shape.** The report's five-step shape vendors
`Operators.lean` and adds it to the `Cslib.lean` barrel in step 1. Doing that leaves the tree
**red** — duplicate declarations fire the moment both modules share an import closure, and the 12
notation ambiguities fire the moment `Connectives.lean` imports `Operators.lean`. This plan keeps
the red window as small as possible by (a) vendoring `Operators.lean` orphaned (not in the barrel)
in Phase 1, (b) pre-landing all 12 `_def` bridge lemmas in green, per-module, committable phases
before anything switches, and (c) confining every red-making edit to one declared atomic-batch
phase (Phase 8). This is a sequencing refinement of the report's recommendation, not a change of
approach: every step the report calls for still happens, in the report's smallest-first module
order.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `specs/ROADMAP.md` consulted for this task (no `roadmap_path` in delegation context).

## Goals & Non-Goals

**Goals**:
- Vendor `Cslib/Foundations/Logic/Operators.lean` byte-identical to `b8ad3923`, never hand-edited.
- Reduce `Connectives.lean` to a delta: delete the five classes upstream now owns, keep `HasBot`,
  `HasUntil`, `HasSince`, `HasNext` and all six bundles unchanged.
- Resolve the `HasDia` / `HasDiamond` divergence in favour of upstream's name across all 6 code
  sites and 11 documentation mentions.
- Delete the 12 colliding local notation declarations, compensating each with a `_def` bridge lemma
  in upstream's sanctioned shape.
- Preserve the cited design prose currently attached to `HasBox` and `HasDia` by relocating it into
  the `Connectives.lean` module docstring.
- Record the latent instance-registration trap as a standing invariant in that module docstring.
- Leave the tree green under the full 7-step CSLib CI pipeline.

**Non-Goals**:
- Merging `upstream/main`. The 7 content conflicts (`Cslib.lean`, `InferenceSystem.lean`,
  `Modal/Basic.lean`, `Modal/LogicalEquivalence.lean`, `Propositional/Defs.lean`, `CslibTests.lean`,
  `references.bib`) are the PR #648 rebase, a separate task. `Operators.lean` is not among them.
- The falsum representation question. Settled: primitive `HasBot` retained. Do not reopen.
- Registering `HasNot`, `HasIff`, or `HasTensor` instances for any fork formula type. Doing so would
  *create* new notation ambiguities that do not exist today.
- Dismantling the six connective bundles. Whether upstream accepts bundles alongside its à-la-carte
  direction is a PR #649 review question, not a build question.
- Fixing associativity/precedence of the *retained* fork notations (`↔` and `¬` in all five
  namespaces). Partially overtaken by Phase 8 but still open for the survivors.
- Any GitHub or Zulip prose. Per CSLib AI policy and the formal challenge raised on the
  Propositional Logic topic, no agent-authored outward text. If PR #649's description needs
  updating, produce a factual scaffolding file under `specs/619_reconcile_connectives_operators/`
  for a human to adapt.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Deleting local `→`/`∧`/`□` notation breaks `simp`/`grind`/`rw` proofs at scale (elaboration moves from concrete constructor to typeclass projection) | H | H | Pre-land all 12 `_def` bridge lemmas in green per-module phases (3-7) **before** any deletion; all five affected pairings verified `rfl`-equal by the research report; constructor pattern-matching is untouched |
| The red window between vendoring and full reconciliation swallows a whole dispatch | H | M | `Operators.lean` vendored orphaned (Phase 1) so it never enters the barrel early; every red-making edit confined to one declared `atomic-batch` phase (Phase 8); Phases 1-7 and 9-10 are each independently green and committable |
| A `_def` bridge lemma does not close by `rfl` | H | L | This signals the instance and the constructor have drifted. Escalate the phase as `[BLOCKED]` with the goal state. Do **not** weaken to `simp`/`decide`, and do **not** introduce `sorry` or a vacuous definition |
| `AxiomDia*` rename ripples far wider than the report estimated | M | H (already realised) | Measured: 198 identifier occurrences across 25 files, not 4 sites. Isolated into Phase 9 with `atomic-batch` commit mode; may close `[COMPLETED WITH EXCLUSIONS]` and spawn a follow-up if the measured count at implementation time exceeds this census |
| Adding `@[scoped grind =]` attributes changes existing `grind` behaviour downstream before the switch | M | M | Bridge-lemma phases carry `interface` tier (changed module plus enumerated direct dependents); the Phase 10 full gate is the backstop for transitive effects |
| Precedence realignment when local declarations are deleted (PL `→` moves 30 -> 25, `∨` 35 -> 30; PL `∧` `infix` -> upstream `infixr`) | M | L | Relative ordering `∧ > ∨ > →  > ↔` is preserved across the swap, so no existing well-formed term re-parses; the `infix` -> `infixr` change only *admits* previously-rejected chained terms. Verify by build, and inspect any mixed-operator term flagged by the build |
| Vendored `Operators.lean` drifts from upstream | L | L | Verbatim `git show`; re-verify `git diff b8ad3923 upstream/main -- .../Operators.lean` is empty before Phase 1; never hand-edit |
| `lake shake` strips the `public import` of `Operators` from `Connectives.lean` | L | M | Keep the import `public` so downstream modules still see the classes; if shake flags it, add the `-- shake: keep-downstream` comment rather than accepting the removal |
| Fork's renamed `HasDiamond` becomes a *fifth* duplicate against upstream's | M | H (by construction) | Intentional: Phase 2 converts a divergence into a duplicate; Phase 8 deletes five duplicates uniformly. Its docstring is relocated alongside `HasBox`'s |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4, 5, 6 | -- |
| 2 | 7 | 2 |
| 3 | 8 | 1, 2, 3, 4, 5, 6, 7 |
| 4 | 9 | 8 |
| 5 | 10 | 9 |

Phases within the same wave can execute in parallel. Wave 1 is parallel-safe by file territory:
Phase 1 owns the new `Operators.lean`; Phase 2 owns `Connectives.lean`, `Axioms.lean`,
`ProofSystem.lean`, `Modal/Basic.lean`, `Modal/Semantics/Birelational.lean`; Phases 3-6 each own
exactly one syntax module. Phase 7 also touches `Modal/Basic.lean`, so it is serialised after
Phase 2.

---

### Phase 1: Vendor Operators.lean verbatim (orphaned) [NOT STARTED]

**Goal**: Bring upstream's `Operators.lean` into the tree byte-identically, without entering the
`Cslib.lean` barrel, so nothing downstream changes yet.

**Tasks**:
- [ ] Confirm the vendoring target is still stable: `git diff b8ad3923 upstream/main -- Cslib/Foundations/Logic/Operators.lean` must be empty
- [ ] `git show b8ad3923:Cslib/Foundations/Logic/Operators.lean > Cslib/Foundations/Logic/Operators.lean`
- [ ] Verify byte-identity: `git show b8ad3923:Cslib/Foundations/Logic/Operators.lean | diff - Cslib/Foundations/Logic/Operators.lean` must produce no output
- [ ] Do **not** run `lake exe mk_all --module` in this phase — adding the module to the barrel here would put both declaration sets in one import closure and turn the tree red
- [ ] Do **not** hand-edit the vendored file for any reason, including lint or style

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: The vendored file is 120 lines and declares 9 classes (`HasAnd`, `HasOr`,
`HasImp`, `HasIff`, `HasNot`, `HasBox`, `HasDiamond`, `HasDynamicBox`, `HasDynamicDiamond`,
`HasTensor`) with 7 scoped notation declarations. Confirm by `wc -l` and `grep -c '^class '` on the
written file, and confirm the empty upstream diff before copying.

**Files to modify**:
- `Cslib/Foundations/Logic/Operators.lean` - new file, verbatim copy from `b8ad3923`

**Verification**:
- `diff` against `git show` output is empty
- `lake build Cslib.Foundations.Logic.Operators` succeeds (fallback if lake cannot resolve an
  orphan module name: `lake env lean Cslib/Foundations/Logic/Operators.lean`)
- `lake build` of the existing barrel is unchanged and still green

---

### Phase 2: Migrate HasDia to the upstream HasDiamond name [NOT STARTED]

**Goal**: Rename the fork's `HasDia` class and its `dia` field to upstream's `HasDiamond` /
`diamond`, converting a naming divergence into an exact duplicate that Phase 8 can delete
uniformly.

**Tasks**:
- [ ] Rename `class HasDia (F : Type*)` -> `class HasDiamond (F : Type*)` and field `dia` ->
      `diamond` at `Cslib/Foundations/Logic/Connectives.lean:112-114`
- [ ] Update `Cslib/Foundations/Logic/Axioms.lean:197` (`variable [HasDia F]`), `:206` and `:217`
      (`HasDia.dia φ` inside `AxiomDiaDuality`)
- [ ] Update `Cslib/Foundations/Logic/ProofSystem.lean:210` (`variable ... [HasDia F] ...`)
- [ ] Update `Cslib/Logics/Modal/Basic.lean:109` (`instance : HasDia (Proposition Atom)`) and its
      field assignment
- [ ] Update the 11 documentation mentions: `Connectives.lean:98,111,168`;
      `Modal/Basic.lean:39,48,108`; `Axioms.lean:158,170,183,201`;
      `Modal/Semantics/Birelational.lean:47`
- [ ] Do **not** rename `AxiomDiaDuality*` or `diaDuality*` in this phase — that is Phase 9

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: 6 code sites and 11 documentation mentions across 5 files, totalling 17 lines.
Confirm at implementation time with `grep -rn '\bHasDia\b' --include=*.lean Cslib/ CslibTests/`
before editing and again after — the post-edit count must be 0. If the pre-edit count exceeds 17,
stop and re-derive the site list rather than proceeding on the recorded figure.

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - class + field rename, 3 doc mentions
- `Cslib/Foundations/Logic/Axioms.lean` - 3 code sites, 4 doc mentions
- `Cslib/Foundations/Logic/ProofSystem.lean` - 1 code site
- `Cslib/Logics/Modal/Basic.lean` - 1 code site, 3 doc mentions
- `Cslib/Logics/Modal/Semantics/Birelational.lean` - 1 doc mention

**Verification**:
- `grep -rn '\bHasDia\b' --include=*.lean Cslib/ CslibTests/` returns nothing
- `lake build Cslib.Foundations.Logic.Connectives Cslib.Foundations.Logic.Axioms Cslib.Foundations.Logic.ProofSystem Cslib.Logics.Modal.Basic` green
- `lake build Cslib.Logics.Modal.Semantics.Birelational` green (enumerated direct dependent)

---

### Phase 3: Pre-land LTL bridge lemma [NOT STARTED]

**Goal**: Add the `_def` bridge lemma that will compensate for the local `→` notation deleted in
Phase 8, while that notation is still present, so the phase is green and committable on its own.

**Tasks**:
- [ ] Add `@[scoped grind =] lemma Formula.imp_def (φ ψ : Formula Atom) : φ.imp ψ = HasImp.imp φ ψ := rfl`
      to `Cslib/Logics/LTL/Syntax/Formula.lean`, adjacent to the `LTLConnectives` instance
- [ ] State the right-hand side with the explicitly qualified projection (`HasImp.imp`), not the
      notation — the notation's meaning changes in Phase 8, the qualified name does not
- [ ] Must be `lemma`, not `def` (`defLemma` lint), and must carry a docstring (`docBlame` lint)
- [ ] Leave every LTL notation declaration untouched in this phase, including the `□`/`◇` bindings
      to `allFuture`/`someFuture`, whose distinct meaning must be preserved

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: exactly 1 bridge lemma, because LTL has exactly 1 measured collision site
(`Cslib/Logics/LTL/Syntax/Formula.lean:209`, `→` bound to `Formula.imp`, colliding via the
`LTLConnectives` instance at `:162`). Confirm the line and binding by reading lines 204-218 before
editing. Confirm no `Formula.imp_def` already exists in this namespace
(`grep -rn 'imp_def' Cslib/Logics/LTL/`) — the pre-edit count is expected to be 0.

**Files to modify**:
- `Cslib/Logics/LTL/Syntax/Formula.lean` - add 1 bridge lemma

**Verification**:
- `lake build Cslib.Logics.LTL.Syntax.Formula` green
- `lake build Cslib.Logics.LTL` (2,746-line subtree, the enumerated dependent set) green

---

### Phase 4: Pre-land Temporal bridge lemma [NOT STARTED]

**Goal**: Same as Phase 3, for the Temporal module.

**Tasks**:
- [ ] Add `@[scoped grind =] lemma Formula.imp_def (φ ψ : Formula Atom) : φ.imp ψ = HasImp.imp φ ψ := rfl`
      to `Cslib/Logics/Temporal/Syntax/Formula.lean`, adjacent to the `TemporalConnectives` instance
- [ ] Qualified projection on the right-hand side; `lemma` not `def`; docstring present
- [ ] Leave every Temporal notation declaration untouched

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: exactly 1 bridge lemma, because Temporal has exactly 1 measured collision site
(`Cslib/Logics/Temporal/Syntax/Formula.lean:169`, `→` bound to `Formula.imp`, colliding via the
`TemporalConnectives` instance at `:123`). Confirm by reading lines 164-178 before editing, and
confirm no existing `imp_def` in `Cslib/Logics/Temporal/`.

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - add 1 bridge lemma

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax.Formula` green
- `lake build Cslib.Logics.Temporal` (20,310-line subtree) green

---

### Phase 5: Pre-land Bimodal bridge lemmas [NOT STARTED]

**Goal**: Same as Phase 3, for the Bimodal module's two collision sites.

**Tasks**:
- [ ] Add `Formula.imp_def : φ.imp ψ = HasImp.imp φ ψ := rfl` to
      `Cslib/Logics/Bimodal/Syntax/Formula.lean`
- [ ] Add `Formula.box_def : φ.box = HasBox.box φ := rfl` to the same file
- [ ] Both `@[scoped grind =]`, both `lemma`, both docstringed, both with qualified right-hand sides
- [ ] Leave every Bimodal notation declaration untouched, including `∧`, `∨`, and `◇`, which are
      clean because `Bimodal.Formula` has no `HasAnd`/`HasOr`/`HasDiamond` instance

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: exactly 2 bridge lemmas, because Bimodal has exactly 2 measured collision
sites (`Formula.lean:101` `→` and `:102` `□`, both colliding via the `BimodalConnectives` instance
at `:53`). Confirm by reading lines 96-112 before editing, and confirm no existing `imp_def`/
`box_def` in `Cslib/Logics/Bimodal/`.

**Files to modify**:
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` - add 2 bridge lemmas

**Verification**:
- `lake build Cslib.Logics.Bimodal.Syntax.Formula` green
- `lake build Cslib.Logics.Bimodal` (52,462-line subtree) green

---

### Phase 6: Pre-land Propositional bridge lemmas [NOT STARTED]

**Goal**: Same as Phase 3, for the Propositional module's three collision sites.

**Tasks**:
- [ ] Add `Proposition.and_def : φ.and ψ = HasAnd.and φ ψ := rfl` to
      `Cslib/Logics/Propositional/Defs.lean`
- [ ] Add `Proposition.or_def : φ.or ψ = HasOr.or φ ψ := rfl` to the same file
- [ ] Add `Proposition.imp_def : φ.imp ψ = HasImp.imp φ ψ := rfl` to the same file
- [ ] All three `@[scoped grind =]`, `lemma`, docstringed, qualified right-hand sides
- [ ] Place them after the `PropositionalConnectives` / `HasAnd` / `HasOr` instance registrations at
      `Defs.lean:114-126` so the instances are in scope
- [ ] Leave the `↔` and `¬` notation declarations at `Defs.lean:110-111` untouched — they survive
      Phase 8 and their associativity fix remains a separate open item

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: exactly 3 bridge lemmas, because Propositional has exactly 3 measured
collision sites (`Defs.lean:107` `∧` via the `HasAnd` instance at `:119`, `:108` `∨` via the `HasOr`
instance at `:123`, `:109` `→` via `PropositionalConnectives` at `:114`). Confirm by reading lines
100-130 before editing, and confirm no existing `and_def`/`or_def`/`imp_def` in
`Cslib/Logics/Propositional/`.

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - add 3 bridge lemmas

**Verification**:
- `lake build Cslib.Logics.Propositional.Defs` green
- `lake build Cslib.Logics.Propositional` (42,561-line subtree) green

---

### Phase 7: Pre-land Modal bridge lemmas [NOT STARTED]

**Goal**: Same as Phase 3, for the Modal module's five collision sites — the largest subtree, run
last among the bridge-lemma phases.

**Tasks**:
- [ ] Add `Proposition.and_def`, `Proposition.or_def`, `Proposition.imp_def`, `Proposition.box_def`,
      `Proposition.diamond_def` to `Cslib/Logics/Modal/Basic.lean`
- [ ] `diamond_def` states `φ.diamond = HasDiamond.diamond φ := rfl`, using the Phase 2 name — this
      is why the phase depends on Phase 2
- [ ] All five `@[scoped grind =]`, `lemma`, docstringed, qualified right-hand sides
- [ ] Place them after the instance registrations at `Basic.lean:95-110`
- [ ] Leave every Modal notation declaration untouched in this phase

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: interface

**Scope Hypothesis**: exactly 5 bridge lemmas, because Modal has exactly 5 measured collision sites
(`Basic.lean:232` `∧` via the `HasAnd` instance at `:101`, `:233` `∨` via `HasOr` at `:105`, `:234`
`→` via `ModalConnectives` at `:95`, `:235` `□` via `ModalConnectives`, `:236` `◇` via the
`HasDiamond` instance at `:109`). Confirm by reading lines 90-115 and 228-240 before editing, and
confirm no existing `_def` lemmas of these names in `Cslib/Logics/Modal/`.

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` - add 5 bridge lemmas

**Verification**:
- `lake build Cslib.Logics.Modal.Basic` green
- `lake build Cslib.Logics.Modal` (83,504-line subtree) green

---

### Phase 8: The switch — adopt upstream, delete duplicates and colliding notation [NOT STARTED]

**Goal**: Make `Connectives.lean` a delta over `Operators.lean` and remove all 12 notation
collisions in one atomic step. This is the only phase whose intermediate states are red.

**Tasks**:
- [ ] Add `public import Cslib.Foundations.Logic.Operators` to `Connectives.lean` (keep it `public`
      so downstream modules still see the classes)
- [ ] Delete five now-duplicate class declarations from `Connectives.lean`: `HasImp` (`:85-87`),
      `HasBox` (`:100-102`), `HasAnd` (`:132-134`), `HasOr` (`:137-139`), and `HasDiamond`
      (`:112-114`, renamed in Phase 2)
- [ ] Keep `HasBot`, `HasUntil`, `HasSince`, `HasNext`, all six bundles, and the priority-100
      `BimodalConnectives -> ModalConnectives` bridge instance **unchanged**
- [ ] Relocate the cited design prose from the deleted `HasBox` docstring (`:89-99`, citing
      `ChagrovZakharyaschev1997` §3.1 and `Blackburn2001` Chapter 1) and the deleted `HasDiamond`
      docstring (`:104-111`) into the `Connectives.lean` module docstring — do not silently drop it
- [ ] Add a standing-invariant paragraph to the module docstring recording the latent trap:
      registering `HasNot`, `HasIff`, `HasAnd`, `HasOr`, `HasDiamond`, or `HasTensor` for a formula
      type that currently lacks it will silently reopen the notation collision for that symbol
      (5 new `¬` collisions, 4 new `↔` collisions), and giving `LTL.Formula` a `HasBox`/`HasDiamond`
      instance would additionally conflate `□`-as-necessity with `□`-as-`allFuture`
- [ ] Delete the 12 colliding local notation declarations: `Propositional/Defs.lean:107,108,109`;
      `Modal/Basic.lean:232,233,234,235,236`; `Bimodal/Syntax/Formula.lean:101,102`;
      `Temporal/Syntax/Formula.lean:169`; `LTL/Syntax/Formula.lean:209`
- [ ] Delete **only** those 12. Every other notation declaration in those five files is confirmed
      clean and must survive, including all `¬`, all `↔`, Bimodal/Temporal/LTL `∧` and `∨`,
      Bimodal and LTL `◇`, LTL `□`, CLL `⊗`, and every temporal operator
- [ ] Run `lake exe mk_all --module` to add `Operators.lean` to the `Cslib.lean` barrel
- [ ] If any `_def` bridge lemma stops closing by `rfl`, escalate as `[BLOCKED]` with the goal
      state. Do not weaken it to `simp`/`decide`, do not introduce `sorry`, and do not create a
      vacuous definition

**Timing**: 2 hours

**Depends on**: 1, 2, 3, 4, 5, 6, 7

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 5 class deletions, 12 notation deletions, 1 import addition, 2 docstrings
relocated, 1 invariant paragraph added, across 6 files plus the generated `Cslib.lean`. Confirm the
notation count at implementation time by grepping each of the five files for `scoped` declarations
before and after: the net delta must be exactly -12. Confirm the class count by
`grep -c '^class ' Cslib/Foundations/Logic/Connectives.lean` before (10) and after (5). All line
numbers above are pre-edit positions and will shift as edits land — re-locate by content, not by
number, after the first edit in each file.

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - import, 5 class deletions, docstring relocation, invariant note
- `Cslib/Logics/Propositional/Defs.lean` - delete 3 notation declarations
- `Cslib/Logics/Modal/Basic.lean` - delete 5 notation declarations
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` - delete 2 notation declarations
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - delete 1 notation declaration
- `Cslib/Logics/LTL/Syntax/Formula.lean` - delete 1 notation declaration
- `Cslib.lean` - regenerated by `mk_all`

**Verification**:
- Full `lake build` green — no `Ambiguous term`, no `has already been declared`
- `grep -rn '\bHasDia\b' --include=*.lean Cslib/ CslibTests/` still returns nothing
- `git diff --stat Cslib/Foundations/Logic/Operators.lean` is empty (the vendored file was never
  touched)

---

### Phase 9: Rename AxiomDia identifiers to AxiomDiamond [NOT STARTED]

**Goal**: Remove the remaining `Dia`-flavoured fork-local naming so it does not contradict the
adopted `HasDiamond` name. Mechanical, semantics-free, and deliberately isolated so it can be
dropped without touching Phases 1-8.

**Tasks**:
- [ ] Rename `AxiomDiaDuality` -> `AxiomDiamondDuality`, `AxiomDiaDualityFwd` ->
      `AxiomDiamondDualityFwd`, `AxiomDiaDualityBack` -> `AxiomDiamondDualityBack`
- [ ] Rename the corresponding typeclasses `HasAxiomDiaDualityFwd`/`HasAxiomDiaDualityBack` and
      their fields `diaDuality`, `diaDualityFwd`, `diaDualityBack` to the `Diamond`/`diamond` forms
- [ ] Apply uniformly across all occurrence sites; the rename is purely lexical with no proof
      restructuring
- [ ] Update documentation mentions in the same pass so no `Dia`-flavoured prose survives
- [ ] If the measured pre-edit census diverges materially from the recorded figures below, close
      this phase `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions` record and spawn a
      follow-up task rather than expanding the batch mid-phase

**Timing**: 1.5 hours

**Depends on**: 8

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 198 identifier occurrences across 25 files — `AxiomDiaDuality` 1,
`AxiomDiaDualityFwd` 36, `AxiomDiaDualityBack` 37, `diaDuality` 2, `diaDualityFwd` 61,
`diaDualityBack` 61. This supersedes the research report's "4 sites" estimate, which was measured
wrongly. Confirm at implementation time with
`grep -rho 'AxiomDia[A-Za-z]*' --include=*.lean Cslib/ CslibTests/ | sort | uniq -c` and the
equivalent for `diaDuality[A-Za-z]*`, plus
`grep -rl 'AxiomDia\|diaDuality' --include=*.lean Cslib/ CslibTests/ | wc -l` for the file count.
Post-edit, all four greps must return zero matches.

**Files to modify**:
- 25 files under `Cslib/Foundations/Logic/` and `Cslib/Logics/Modal/` — enumerate at implementation
  time with `grep -rl 'AxiomDia\|diaDuality' --include=*.lean Cslib/ CslibTests/`; the known
  concentration is `Modal/Metalogic/` (`Completeness.lean`, `Soundness.lean`, `MCS.lean`,
  `InterSystem/IntToClassical.lean`) and `Modal/ProofSystem/Instances/`

**Verification**:
- `grep -rn 'AxiomDia\|diaDuality' --include=*.lean Cslib/ CslibTests/` returns nothing
- Full `lake build` green

---

### Phase 10: Full CSLib CI gate [NOT STARTED]

**Goal**: Run the complete 7-step CSLib verification pipeline and confirm the tree is submission-clean.

**Tasks**:
- [ ] `lake exe cache get` (only if the Mathlib revision changed; it should not have)
- [ ] `lake build` — full library, syntax linters inline
- [ ] `lake exe checkInitImports` — every file imports `Cslib.Init`
- [ ] `lake lint` — environment linters. Watch specifically for `docBlame` on every retained fork
      class and bundle whose docstring passed through an edit, and `defLemma` on the 12 bridge
      lemmas
- [ ] `lake exe lint-style` — text linters
- [ ] `lake test` — `CslibTests/`
- [ ] `lake exe mk_all --module` — confirm `Cslib.lean` is already current and the command is a
      no-op
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — if it proposes removing
      `Connectives.lean`'s `public import` of `Operators`, keep the import and add
      `-- shake: keep-downstream` rather than accepting the removal
- [ ] Confirm zero `sorry`, zero new axioms, and no vacuous definitions were introduced anywhere in
      the task
- [ ] Confirm no GitHub or Zulip content was authored. If PR #649's description needs updating,
      write a factual scaffolding file under `specs/619_reconcile_connectives_operators/` for a
      human to adapt

**Timing**: 1.5 hours

**Depends on**: 9

**Verification Tier**: full

**Files to modify**:
- None expected. Any file touched here is a lint fix and must be recorded as such

**Verification**:
- All 7 CI steps exit zero
- `grep -rn 'sorry' --include=*.lean` shows no new occurrences relative to the task's starting commit

---

## Testing & Validation

- [ ] `lake build` green on the full library
- [ ] `lake exe checkInitImports` passes
- [ ] `lake lint` passes, with no new `docBlame` or `defLemma` warnings
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] `lake exe mk_all --module` is a no-op at task end
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes with the `Operators` import retained
- [ ] `Cslib/Foundations/Logic/Operators.lean` is byte-identical to `git show b8ad3923:Cslib/Foundations/Logic/Operators.lean`
- [ ] `grep -rn '\bHasDia\b\|AxiomDia\|diaDuality' --include=*.lean Cslib/ CslibTests/` returns nothing
- [ ] Zero `sorry`, zero new axioms, no vacuous definitions
- [ ] The `Connectives.lean` module docstring carries the relocated `HasBox`/`HasDiamond` design prose and the standing instance-registration invariant

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Operators.lean` — new, vendored verbatim from `b8ad3923`
- `Cslib/Foundations/Logic/Connectives.lean` — reduced to a delta over `Operators.lean`
- `Cslib/Foundations/Logic/Axioms.lean`, `Cslib/Foundations/Logic/ProofSystem.lean` — rename propagation
- `Cslib/Logics/{Propositional/Defs, Modal/Basic, Bimodal/Syntax/Formula, Temporal/Syntax/Formula, LTL/Syntax/Formula}.lean` — 12 notation deletions plus 12 `_def` bridge lemmas
- ~25 files under `Cslib/Logics/Modal/` — `AxiomDia*` rename
- `Cslib.lean` — regenerated barrel
- `specs/619_reconcile_connectives_operators/summaries/01_reconcile-connectives-operators-summary.md`
- Optional: a factual PR-description scaffolding file for a human to adapt, if PR #649 needs updating

## Rollback/Contingency

Every phase except 8 and 9 is independently green and committed on its own, so rollback is
`git revert` of the offending phase commit. Phases 8 and 9 are declared `atomic-batch`: each is one
commit covering its whole file set, so reverting either restores a green tree in a single step.

If Phase 8 cannot be made green — most plausibly because a `_def` bridge lemma stops closing by
`rfl`, indicating an instance and its constructor have drifted — mark the phase `[BLOCKED]`, record
the failing lemma and its goal state, and leave Phases 1-7 committed. Phases 1-7 are strictly
additive (a new orphan module, a fork-local rename, and 12 new lemmas) and leave the tree green and
shippable even if the switch is deferred.

If Phase 9's measured census diverges materially from the recorded 198-occurrence / 25-file figure,
close it `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions` record and spawn a
follow-up task. Nothing in Phases 1-8 or 10 depends on the `AxiomDia*` rename having happened.

Under no circumstance use `git reset --hard`, `git checkout --`, or `git clean -fd` on a dirty tree
to reach a passing build. Fix forward, or snapshot via `bash .claude/scripts/git-snapshot.sh 619`
first.
