# Implementation Plan: Task #614

- **Task**: 614 - Give `ctxToImp` a computable definition so the four context-based `Decidable`
  instances for the propositional sequent calculi stop being `noncomputable`
- **Status**: [NOT STARTED]
- **Effort**: 3.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/614_computable_ctxtoimp_context_decidability/reports/01_computable-context-decidability.md`
- **Artifacts**: plans/01_computable-context-decidability.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, `.claude/rules/cslib.md`, `.claude/rules/lean4.md`
- **Type**: cslib
- **Lean Intent**: false

## Overview

Make the four registered context-based `Decidable` instances for LJ and LK computable, without
adding a typeclass hypothesis and without changing any public statement. The route is
**Route 3** from the research report: because `Decidable p` is a `Subsingleton`, one may eliminate
from the `Multiset` quotient underlying `Ctx Atom = Finset (Proposition Atom)` into it
**computably** via `Quotient.recOnSubsingleton`, choosing an arbitrary list representative — the
*decision* is representative-independent even though the intermediate implication-chain formula is
not. Each file gains one named list-level `Decidable` helper, and its two instances are rewritten
to apply that helper through the quotient recursor.

Definition of done: `lake build` green with **no `noncomputable` marker on any of the four
instances**; a `#guard_msgs`-protected `#eval` in `CslibTests/` demonstrably evaluating a
**non-empty-context** decision; the axiom-census ratchet re-baselined with exactly the expected
one-line diff; and the full CSLib CI verification order passing.

### Research Integration

The research report is a **verified prototype**, not a proposal. All four instances were compiled
against the live tree with `lake env lean` (Lean `v4.33.0-rc1`, Mathlib rev `169c26b5`) with no
`noncomputable` marker, and evaluated correctly on 11 expressions. The plan below transcribes that
verified code into place rather than re-deriving it. Five findings from the report are load-bearing
and are carried into specific phases:

1. **The task's title ask is impossible and the plan does not attempt it.** A computable
   `ctxToImp : Ctx Atom → Proposition Atom → Proposition Atom` cannot exist: a computable function
   out of `Finset` must be permutation-invariant, and `A → B → C` differs from `B → A → C` as a
   `Proposition Atom` value. `Finset.fold` requires `Std.Commutative`/`Std.Associative`
   (`Mathlib/Data/Finset/Fold.lean:32`), which `Proposition.imp` lacks; `Hashable` supplies no
   total order; `Multiset.toList` is itself choice-based. `ctxToImp` therefore **stays
   `noncomputable`**, and Phases 1-2 correct its docstring to say the noncomputability is
   *inherent* rather than incidental. The task's stated goal is met in full regardless, because
   nothing that needs to run depends on `ctxToImp` any more.
2. **A named helper is mandatory; the inlined variant provably does not elaborate.** Inside the
   `Quotient.recOnSubsingleton` lambda the representative appears as `⟦l⟧` rather than `↑l`, so the
   `List.toFinset_eq` rewrite finds no occurrence. Recorded verbatim in Phase 1 so it is not
   rediscovered.
3. **Orientation matters**: `List.toFinset_eq h : (⟨↑l, h⟩ : Finset _) = l.toFinset` — use this
   orientation, not its `.symm`.
4. **Tests must use `#guard_msgs in #eval`, never `decide`.** `by decide` fails, but the recorded
   kernel error shows it unfolded straight *through* the new instance and helper and stuck only at
   the pre-existing `WellFounded.fix` in the tableau driver: the construction adds no new kernel
   obstruction, it inherits the existing one.
5. **The axiom-census ratchet will fail until re-baselined.** The new public LJ helper enters the
   `sorryAx`-tainted set transitively through `intuitionisticTableau_complete`. Phase 4 handles
   this. The LK helper is on a sorry-free chain and adds no line.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context and no ROADMAP.md was consulted.

## Goals & Non-Goals

**Goals**:
- `instDecidableLJDerivable`, `instDecidableDerivableInIPL`, `instDecidableLKDerivable`, and
  `instDecidableDerivableInCPL` all build **without** the `noncomputable` marker.
- No new typeclass hypothesis: the four instances keep exactly `[DecidableEq Atom] [Hashable Atom]`.
- No public statement change: contexts stay `Ctx Atom = Finset (Proposition Atom)`; the instance
  types stay byte-identical.
- The universe bridge (`letI` + `ivalid_universe_invariant`) is preserved verbatim in the LJ
  instance, as the task description requires.
- A `#guard_msgs`-protected `#eval` in `CslibTests/` proves a **non-empty-context** decision
  actually evaluates, for both LJ and LK, positive and negative.
- Docstrings that currently blame `Finset.toList` are corrected to state the real, inherent reason
  and the representative-independence argument.
- Axiom-census baseline updated with a verified-minimal diff; full CSLib CI order green.

**Non-Goals**:
- Making `ctxToImp` itself computable (mathematically impossible at its current type — see
  Research Integration item 1).
- Adding a `[LinearOrder Atom]`-based `ctxToImp` variant (Route 1, deliberately rejected).
- Restating the instances over `List` contexts (Route 2, does not solve the stated problem).
- Touching `decidableDerivableIntPropAxiomFMP` (`Metalogic/IntDecidability.lean:489`) or
  `decidableDerivableMinPropAxiomFMP` (`MinDecidability.lean:445`) — noncomputable via
  `Fintype.ofInjective`, an unrelated and irreducible cause; both are deliberately plain `def`s and
  not registered instances.
- Revisiting the closed-context restriction on the tableau TFAE folds
  (`ProofSystemEquivalence.lean:176-186`).
- Fixing the two pre-existing `unusedDecidableInType` lint warnings in this subtree.
- Applying the Route 3 pattern to LM/minimal-logic context decidability (a separate follow-on that
  should inherit this shape).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Prototype compiled in scratch modules; in-place elaboration differs (the files sit inside `@[expose] public section` with a file-level `variable {Atom : Type u} [DecidableEq Atom] [Hashable Atom]`) | M | M | Build the single module after adding the helper and again after rewriting each instance; do not batch. The `variable` line already supplies exactly the instance binders the helper needs |
| Implementer inlines the helper into the instance body to avoid a new public declaration | H | M | Explicitly forbidden in Phase 1 tasks, with the recorded elaboration error quoted. The named form works because the coercion resolves by *unification* against the helper's declared type, not by syntactic rewriting |
| `List.toFinset_eq` applied with the wrong orientation | M | M | Phase 1 states the exact orientation; a `.symm` attempt is recorded as having failed with a type mismatch |
| Axiom-census diff is larger than the single expected line | M | L | Phase 4 inspects `git diff scripts/axiom-census-baseline.txt` **before** committing; any diff beyond the one added LJ-helper line (plus tolerated column-3 "reason" churn on `instDecidableLJDerivable`) is investigated, not committed |
| Pre-existing lint warnings misread as regressions introduced here | L | M | Phase 4 captures `lake lint` output and compares against the two known `unusedDecidableInType` warnings in this subtree, which are explicitly out of scope |
| Implementer reaches for `by decide` in the test file and concludes the work failed | M | M | Phase 3 mandates `#guard_msgs in #eval` and records why `decide` stalls (pre-existing `WellFounded.fix`, not the new construction) |
| New test module missing from the `CslibTests.lean` barrel breaks `lake exe mk_all --check` | M | M | Phase 3 registers it alphabetically in the same phase; Phase 4 re-verifies with `lake exe mk_all --module` |
| Full `lake build` is slow / Mathlib cache cold | L | M | Run `lake exe cache get` once before Phase 4's full sweep (step 0 of the CSLib CI order) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential.

---

### Phase 1: Make the LJ instances computable [NOT STARTED]

**Goal**: `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` builds with
`instDecidableLJDerivable` and `instDecidableDerivableInIPL` carrying no `noncomputable` marker,
and its docstrings state the real reason the remaining `noncomputable` markers are there.

**Tasks**:
- [ ] Add the new public helper `ljListDerivableDecidable` in the "Decidability Instances" section,
      **before** `instDecidableLJDerivable`, with a docstring. Transcribe the verified prototype
      from the research report §5.1: it takes `(l : List (Proposition Atom))`,
      `(h : (↑l : Multiset (Proposition Atom)).Nodup)`, `(A : Proposition Atom)` and returns
      `Decidable (Nonempty (LJProof ((⟨↑l, h⟩ : Finset (Proposition Atom)) ⊢ A)))`. It preserves the
      `letI` universe bridge (`decidable_of_iff (IValid.{_, 0} …) (ivalid_universe_invariant _).symm`)
      verbatim, then `decidable_of_iff (IValid (listToImp l A))` with the two-direction proof routing
      through `lj_iff_ivalid`, `ljListDeductionBwd`/`ljListDeductionFwd`, and `Finset.union_empty`.
- [ ] Use `List.toFinset_eq h : (⟨↑l, h⟩ : Finset _) = l.toFinset` in **that orientation** — not
      `.symm`, which was tried and fails with a type mismatch.
- [ ] Build the single module to confirm the helper is green **before** touching the instances.
- [ ] Rewrite `instDecidableLJDerivable`'s body (currently at :197-212) to the
      `Quotient.recOnSubsingleton` form applied to `Γ.val` with motive
      `fun (s : Multiset (Proposition Atom)) => (h : s.Nodup) → Decidable (Nonempty (LJProof ((⟨s, h⟩ : Finset (Proposition Atom)) ⊢ A)))`,
      the function `fun l h => ljListDerivableDecidable l h A`, and the final argument `Γ.nodup`.
      Drop `noncomputable`. No cast or rewrite is needed at the instance level: `⟨Γ.val, Γ.nodup⟩` is
      **definitionally** `Γ` by structure eta.
- [ ] Drop `noncomputable` from `instDecidableDerivableInIPL` (:218). Its body is unchanged.
- [ ] **MUST NOT** inline the helper into the instance body. The fully-inlined variant was tried and
      does **not** elaborate: inside the `Quotient.recOnSubsingleton` lambda the representative
      appears as `⟦l⟧` rather than `↑l`, and the rewrite fails with
      `Tactic 'rewrite' failed: Did not find an occurrence of the pattern { val := ↑l, nodup := h }`.
- [ ] Rewrite the docstrings that misattribute the cause. Remove
      "The instance is `noncomputable` because `ctxToImp` uses `Finset.toList`" from the
      `instDecidableLJDerivable` docstring (:190) and replace it with the representative-independence
      argument. Update the module Strategy block (:17-35) correspondingly.
- [ ] Rewrite the docstrings of `ctxToImp` (:82), `ljProofDeductionFwd` (:112), and
      `ljProofDeductionBwd` (:170) to state that their `noncomputable` marker is **inherent** —
      picking an order for a `Finset` is a genuine choice, and no computable
      `Ctx Atom → Proposition Atom → Proposition Atom` extending `listToImp` exists — and that it no
      longer affects any decision procedure. Leave the declarations themselves `noncomputable`.
- [ ] Keep the existing "Universe note" (:191-196) **verbatim**; it is still exactly right.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: Exactly one file is edited (`LJ/Decidability.lean`); exactly two
`noncomputable` markers are dropped (`instDecidableLJDerivable`, `instDecidableDerivableInIPL`) and
exactly three are deliberately retained (`ctxToImp`, `ljProofDeductionFwd`, `ljProofDeductionBwd`).
Confirm at implementation time with
`grep -n "noncomputable" Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` — expect
exactly 3 hits, all on the retained defs. If the count differs, stop and reconcile before
proceeding.

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` - add
  `ljListDerivableDecidable`; rewrite `instDecidableLJDerivable` body and drop `noncomputable`;
  drop `noncomputable` from `instDecidableDerivableInIPL`; correct five docstring sites.

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability` succeeds.
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.Decidability` (the one direct dependent
  module, which imports LJ.Decidability and uses `ctxToImp`) still succeeds — this catches any
  accidental signature drift before Phase 2 starts editing it.
- `grep -c "noncomputable"` on the LJ file returns 3.
- No `sorry` introduced: `lean_verify Cslib.Logic.PL.instDecidableLJDerivable` shows no new axiom
  beyond the pre-existing `sorryAx` taint inherited from `intuitionisticTableau_complete`.

---

### Phase 2: Make the LK instances computable [NOT STARTED]

**Goal**: `Cslib/Logics/Propositional/SequentCalculus/LK/Decidability.lean` builds with
`instDecidableLKDerivable` and `instDecidableDerivableInCPL` carrying no `noncomputable` marker,
with the same docstring corrections.

**Tasks**:
- [ ] Add the public helper `lkListDerivableDecidable` in the "Decidability Instances" section,
      before `instDecidableLKDerivable`, with a docstring. Transcribe the verified prototype from
      the research report §5.2. It returns
      `Decidable (Nonempty (LKProof ((⟨↑l, h⟩ : Finset (Proposition Atom)) ⊢ₛ {A})))` via
      `decidable_of_iff (Tautology (listToImp l A))`, routing through `lk_iff_tautology`,
      `lkListDeductionBwd`/`lkListDeductionFwd`, and `Finset.union_empty`.
- [ ] Note the structural difference from LJ: **no `letI` universe bridge here**.
      `instDecidableTautologyTableau` is not universe-pinned, matching the existing LK instance,
      which also has none. Do not add one by analogy with Phase 1.
- [ ] Use the same `List.toFinset_eq h` orientation as Phase 1.
- [ ] Build the single module to confirm the helper is green before touching the instances.
- [ ] Rewrite `instDecidableLKDerivable` (:174) to the `Quotient.recOnSubsingleton` form on `Γ.val`
      with the `LKProof (… ⊢ₛ {A})` motive; drop `noncomputable`.
- [ ] Drop `noncomputable` from `instDecidableDerivableInCPL` (:190). Body unchanged.
- [ ] **MUST NOT** inline the helper (same recorded elaboration failure as Phase 1).
- [ ] Correct the docstrings that say "This is `noncomputable` because `ctxToImp` uses
      `Finset.toList`" at :91 (`lkProofDeductionFwd`) and :152 (`lkProofDeductionBwd`) to state the
      inherent reason, and remove the corresponding claim from the `instDecidableLKDerivable`
      docstring (:173). Update the module Strategy block (:18-31).
- [ ] Leave `lkProofDeductionFwd` and `lkProofDeductionBwd` themselves `noncomputable`.

**Timing**: 45 minutes

**Depends on**: 1

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: Exactly one file is edited (`LK/Decidability.lean`); exactly two
`noncomputable` markers are dropped (`instDecidableLKDerivable`, `instDecidableDerivableInCPL`) and
exactly two are retained (`lkProofDeductionFwd`, `lkProofDeductionBwd` — `ctxToImp` lives in the LJ
file, not this one). Confirm with
`grep -n "noncomputable" Cslib/Logics/Propositional/SequentCalculus/LK/Decidability.lean` — expect
exactly 2 hits. If the count differs, stop and reconcile.

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/Decidability.lean` - add
  `lkListDerivableDecidable`; rewrite `instDecidableLKDerivable` body and drop `noncomputable`;
  drop `noncomputable` from `instDecidableDerivableInCPL`; correct four docstring sites.

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.Decidability` succeeds.
- `grep -c "noncomputable"` on the LK file returns 2.
- Combined check across both files: zero of the four instance declarations is preceded by
  `noncomputable`.

---

### Phase 3: Executable conformance tests for non-empty-context decisions [NOT STARTED]

**Goal**: A `CslibTests/` module proves by execution that a **non-empty-context** decision now
evaluates, for both LJ and LK, in both the positive and negative direction — the concrete deliverable
the task's VERIFY line asks for.

**Tasks**:
- [ ] Create `CslibTests/ContextDecidability.lean` with the standard CSLib copyright header and
      `module` line.
- [ ] Header requirement (verified): the module needs **both** `public import X` and
      `public meta import X` for each of the two Decidability modules. A plain `import` alone fails
      with "may not access declaration … imported as 'meta'" on constructor references. Follow the
      idiom in `CslibTests/TableauConformance.lean`.
- [ ] Do **not** import `Cslib.Init` — `CslibTests/*.lean` files do not, so `checkInitImports` does
      not apply to this file (confirmed against `CslibTests/Propositional.lean`).
- [ ] Use `Atom := Bool` as the two-atom type (`false` = p, `true` = q), matching
      `CslibTests/Propositional.lean`'s convention, and document that choice in the module docstring.
- [ ] Write a module docstring explaining **why `#eval`, not `decide`**: `by decide` stalls on the
      pre-existing `WellFounded.fix` inside the tableau driver, not on anything introduced here. The
      recorded kernel error unfolds straight through `instDecidableLJDerivable` and
      `ljListDerivableDecidable` before getting stuck. Mirror the framing in
      `CslibTests/TableauConformance.lean`'s header.
- [ ] Add, at minimum, these `#guard_msgs in #eval decide (…)` assertions:
      - LJ non-empty context, positive: `{p, p → q} ⊢ q` expects `true` (**the task's target case**)
      - LJ non-empty context, negative: `{q} ⊢ p` expects `false`
      - LK non-empty context, positive and negative counterparts
      - LJ `∅ ⊢ p ∨ (p → ⊥)` expects `false` and LK `∅ ⊢ p ∨ (p → ⊥)` expects `true` — this
        intuitionistic/classical contrast is the single strongest check that the two instances are
        wired to their own decision procedures and not accidentally to each other
      - `DerivableIn` forms for IPL and CPL, exercising `instDecidableDerivableInIPL` and
        `instDecidableDerivableInCPL` directly
- [ ] Register the new module in `CslibTests.lean` as `public import CslibTests.ContextDecidability`,
      inserted **alphabetically** (between `CslibTests.Bisimulation` and `CslibTests.CCS`).

**Timing**: 45 minutes

**Depends on**: 1, 2

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: Exactly two files are touched — one new `CslibTests/ContextDecidability.lean`
and one line added to the `CslibTests.lean` barrel. No file under `Cslib/` is touched, so
`Cslib.lean` needs no change. Confirm with `git status --short` showing exactly one untracked test
module and one modified barrel. If a `Cslib/` file appears, a Phase 1/2 edit leaked and must be
reconciled.

**Files to modify**:
- `CslibTests/ContextDecidability.lean` - new executable conformance module (create)
- `CslibTests.lean` - add the barrel import alphabetically

**Verification**:
- `lake build CslibTests.ContextDecidability` succeeds and every `#guard_msgs` passes (a mismatched
  expectation is a build error, so a green build *is* the assertion).
- `lake build CslibTests` succeeds with the new barrel entry.
- The LJ/LK excluded-middle contrast produces `false`/`true` respectively.

---

### Phase 4: Axiom-census re-baseline and full CI sweep [NOT STARTED]

**Goal**: The exact-set axiom-census ratchet is re-baselined with a verified-minimal diff, and the
complete CSLib CI verification order passes.

**Tasks**:
- [ ] Run `lake exe cache get` first (step 0 of the CSLib CI order) to avoid a 30-45 minute Mathlib
      rebuild.
- [ ] Run `bash scripts/check-axiom-census.sh` and confirm it fails as predicted, with the new public
      LJ helper `ljListDerivableDecidable` in the live tainted set. This is expected: the helper
      inherits the pre-existing `sorryAx` taint through `intuitionisticTableau_complete`. Confirming
      the *predicted* failure before updating is what makes the update safe.
- [ ] Run `bash scripts/check-axiom-census.sh --update`.
- [ ] **Inspect `git diff scripts/axiom-census-baseline.txt` before committing.** The expected diff
      is **exactly one added line**, for `Cslib.Logic.PL.ljListDerivableDecidable` in
      `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean`. A column-3 "reason" churn on
      the existing `Cslib.Logic.PL.instDecidableLJDerivable` line (baseline line 44) is tolerated —
      the comparison ignores column 3 but `--update` rewrites it. `lkListDerivableDecidable` must
      **not** appear: the classical tableau chain is sorry-free. Any larger diff means something
      unintended changed and must be investigated, not committed.
- [ ] Run the full CSLib CI verification order in sequence:
      1. `lake build`
      2. `lake exe checkInitImports`
      3. `lake lint`
      4. `lake exe lint-style`
      5. `lake test`
      6. `lake exe mk_all --module`
- [ ] Compare `lake lint` output against the two known pre-existing `unusedDecidableInType` warnings
      in this subtree. They are **not** this task's to fix; report them as pre-existing rather than
      silencing them. Any *new* warning is in scope.
- [ ] Confirm `lake exe mk_all --module` reports no barrel drift (Phase 3 already registered the test
      module).
- [ ] Final confirmation sweep: grep both Decidability files and confirm none of the four instance
      declarations carries `noncomputable`.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: The axiom-census baseline diff is exactly one added line (plus tolerated
column-3 churn on one existing line). Confirm by reading `git diff
scripts/axiom-census-baseline.txt` in full before staging. This is the single highest-value
hypothesis in the plan: an unexpectedly large diff is the primary signal that the change perturbed
something beyond its intended blast radius.

**Files to modify**:
- `scripts/axiom-census-baseline.txt` - one added line for the new LJ helper

**Verification**:
- `bash scripts/check-axiom-census.sh` exits 0 after the update.
- All six CSLib CI steps pass.
- `lake lint` shows only the two pre-existing warnings, named explicitly in the summary.
- Zero `noncomputable` markers on the four target instances.

---

## Testing & Validation

- [ ] `lake build` green across the whole project.
- [ ] `lake exe checkInitImports` passes (no `Cslib/` files added, so no new obligation).
- [ ] `lake lint` output matches the pre-existing baseline: exactly the two known
      `unusedDecidableInType` warnings in this subtree, no new ones.
- [ ] `lake exe lint-style` passes.
- [ ] `lake test` passes, including the new `CslibTests/ContextDecidability.lean` `#guard_msgs`
      assertions.
- [ ] `lake exe mk_all --module` reports no drift.
- [ ] `bash scripts/check-axiom-census.sh` exits 0.
- [ ] Manual confirmation: none of `instDecidableLJDerivable`, `instDecidableDerivableInIPL`,
      `instDecidableLKDerivable`, `instDecidableDerivableInCPL` is declared `noncomputable`.
- [ ] Manual confirmation: none of the four instances gained a typeclass hypothesis; all four still
      require exactly `[DecidableEq Atom] [Hashable Atom]`.
- [ ] Semantic confirmation: the LJ/LK excluded-middle contrast evaluates `false`/`true`.
- [ ] No `sorry` and no new axiom introduced by any declaration added in this task.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean` (modified: new
  `ljListDerivableDecidable`, two instances made computable, five docstrings corrected)
- `Cslib/Logics/Propositional/SequentCalculus/LK/Decidability.lean` (modified: new
  `lkListDerivableDecidable`, two instances made computable, four docstrings corrected)
- `CslibTests/ContextDecidability.lean` (new executable conformance module)
- `CslibTests.lean` (modified: one barrel import)
- `scripts/axiom-census-baseline.txt` (modified: one added line)
- `specs/614_computable_ctxtoimp_context_decidability/summaries/01_computable-context-decidability-summary.md`

## Rollback/Contingency

Every phase is a self-contained, independently revertable commit against files with a **verified-nil
blast radius** — a repo-wide grep found zero references to `ctxToImp`, the four instances, or the
`ljProofDeduction*`/`lkProofDeduction*` defs outside the two Decidability files. Reverting any phase
restores a green build.

- **Phase 1 or 2 fails to elaborate in place** (despite the scratch-module prototype): re-check the
  three recorded traps in order — the named helper (never inlined), the `List.toFinset_eq`
  orientation (never `.symm`), and the LJ-only `letI` universe bridge (never added to LK). If it
  still fails, revert that phase's commit; the file returns to its current `noncomputable` but
  working state, and nothing downstream breaks.
- **Axiom-census diff is unexpectedly large**: do **not** commit the baseline. Revert the baseline
  file, and investigate which declaration entered the tainted set and why. The fallback the research
  report identifies — marking the LJ helper `private` so the census (which filters on the exported
  environment) never sees it — is available but **not recommended**: it hides a genuinely useful
  list-level result and fights the file's `@[expose] public section`.
- **Full revert**: reverting all four phase commits returns the tree to the current state, in which
  the four instances are `noncomputable` but everything builds. There is no partial state that
  leaves the library broken, because each phase's own verification gate is a green module build.
