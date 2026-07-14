# Research Report: Salvage of task-299 Soundness Proof-Engineering Lemmas

- **Task**: 396
- **Type**: cslib
- **Session**: sess_1782793858_63b9ed_396
- **Date**: 2026-06-29
- **Reference branch/commit**: `wip/task-299-soundness-refactor` @ `27d93e2d` ("wip(task 299): unverified Soundness recognizer-layer refactor")
- **Parent commit**: `83e232b8` ("vet: Propositional+Foundations review + fix tasks 384-395")

## Objective

Investigate the candidate proof-engineering lemmas left on `27d93e2d`, classify each as
**portable (architecture-independent)** vs **architecture-coupled (global-Accessibility)**,
and recommend a concrete salvage plan for the modal-tableau soundness-gap-redesign effort.

## Scope Limitation (Blocker — read first)

The salvage *target* could **not be inspected in this checkout**:

- No `cslib-364` worktree exists (`git worktree list` shows only `cslib` and
  `cslib-refactor-prop_logic`).
- No branch `task-364-soundness-drift` (or any `*364*`/`*384*`/`*drift*` branch) exists locally.
- `specs/364_modal_tableau_soundness_drift_repair/` and its
  `handoffs/BLOCKED-repair-guide.md` (section 4, the cited "stuck on variable antecedent /
  consumed-scrutinee" friction) are **absent** from this repository.

Consequently the recommendations below are grounded in the **demonstrable acc-freedom of the
candidate lemmas** (they do not reference `Accessibility`, `acc`, or `m.r` at all) rather than
on a direct read of the target architecture. They transplant to *any* soundness architecture
(global- or per-branch-Accessibility) precisely because they are blind to the accessibility
relation. An implementer with the cslib-364 worktree mounted should confirm the friction
point against section 4 before cherry-picking.

## What `27d93e2d` Actually Changed

The commit (vs parent) touches 4 files: `Soundness.lean` (+692/-748 net rewrite),
`Branch.lean` (+67), `Rules.lean` (+4), `Saturation.lean` (~41). The full branch tip
additionally deletes `SoundnessStep.lean` (1638 lines) and rewrites large parts of the
Propositional namespace — **this wholesale rewrite is UNBUILT and must NOT be merged**.

The commit rewrites `modalStepBranch_preserves_sat` on the global-`Accessibility`
architecture (now superseded). That rewrite is the architecture-coupled core and is **out of
scope** for salvage. The value is in a self-contained, acc-free block (~49 lines) inside the
rewritten `Soundness.lean`, lines ~158–215.

## Reuse-First Findings (CSLib Foundations)

The propositional rule layer the candidate lemmas depend on **already lives in Foundations**
and is architecture-independent:

| Symbol | Defined on main at | Layer |
|--------|--------------------|-------|
| `PropTableauRule`, `applyPropRule`, `tryAllPropRules` | `Cslib/Foundations/Logic/Tableau/PropositionalRules.lean` | Foundations (portable) |
| `RuleResult` | `Cslib/Foundations/Logic/Tableau/RuleResult.lean` | Foundations (portable) |
| `modalNegOf?`/`modalOrOf?`/`modalAndOf?`/`modalImpOf?` | `Cslib/Logics/Modal/Tableau/Defs.lean` | Modal (acc-free pure functions) |
| `Model`, `Satisfies` | `Cslib/Logics/Modal/Basic.lean` | Modal semantics (acc-free) |
| `SignedFormula` | Foundations tableau layer | portable |

Caveat: a **duplicate** `applyPropRule`/`PropTableauRule` also exists in
`Cslib/Foundations/Logic/PropositionalTableau.lean`. The modal tableau binds via
`Cslib/Foundations/Logic/Tableau/*` (RuleResult.lean + PropositionalRules.lean). The salvage
must target whichever copy the cslib-364 architecture imports; do not duplicate.

Main's `Defs.lean` already provides the *forward/computation* lemmas
(`modalNegOf?_neg : modalNegOf? (.imp a .bot) = some a := rfl`, plus the `_atom`/`_bot = none`
lemmas) but **does not** provide the *inverse/characterization* direction. The candidate
`*_eq_some` lemmas fill exactly that gap.

## Per-Lemma Classification

All signatures below are quoted from `27d93e2d:Soundness.lean`.

### PORTABLE — recommend salvage (acc-free, depend only on main/Foundations symbols)

1. **`sfSat`** (def) — `{W : Type} (m : Model W Atom) (f : WorldIndex → W) (sf) : Prop`.
   Positive formula holds at `f sf.label`, negative fails there. No `acc`. Portable.
2. **`sfSat_pos`**, **`sfSat_neg`** (lemmas) — trivial constructors for `sfSat`. Portable.
3. **`RuleResultSat`** (def) — `{W : Type} (m) (f) (R : RuleResult ...) : Prop`, matches on
   `linear`/`branching`/`persistent`/`notApplicable`. No `acc`. Portable.
4. **`modalNegOf?_eq_some`** — `modalNegOf? φ = some ψ → φ = .imp ψ .bot`.
   Proof: `unfold modalNegOf? at h; split at h <;> simp_all`. Pure recognizer
   characterization; **directly resolves the "stuck on variable antecedent / consumed
   scrutinee" friction** (recovers the concrete shape of an opaque `φ` after the option-match
   already consumed it, enabling `subst`/`rw`). Highest-value salvage item.
5. **`modalOrOf?_eq_some`**, **`modalAndOf?_eq_some`**, **`modalImpOf?_eq_some`** — same
   inverse-characterization pattern (the `_imp` case needs a nested `split`, see commit).
   Portable, same friction-relief role.
6. **`applyPropRule_sat`** — `{W : Type} (m) (f) (sf) (rule) (hsf : sfSat m f sf) :
   RuleResultSat m f (applyPropRule modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf rule)`.
   The bridge theorem: applying a single propositional rule to a satisfied signed formula
   preserves satisfiability. Built entirely from items 1–5 + `sfSat_pos`/`sfSat_neg`. No
   `acc`. **This is the reusable payload** — any soundness architecture needs exactly this
   lemma for the propositional-rule case; the per-branch redesign can consume it verbatim.

### ARCHITECTURE-COUPLED — do NOT salvage as-is

7. **`branchSatisfiable`** (def) — takes `(acc : Accessibility)` and asserts
   `∀ w w', acc.hasEdge w w' → m.r (f w) (f w')`. Coupled to the global-Accessibility model.
   Main already has its own `branchSatisfiable.{v,u}`. The "**Type vs Type\*** universe
   simplification" the task mentions is the commit's choice of monomorphic `{W : Type}`
   (universe 0) on the portable block, vs main's universe-polymorphic `branchSatisfiable.{v,u}`
   with `Atom : Type v`. The simplification is a *style* win that travels *with the portable
   block* (items 1–6 are all `{W : Type}`); it is **not** a reason to import the coupled
   `branchSatisfiable` rewrite. The per-branch redesign defines its own branch-satisfiability
   predicate, so adopt only the `{W : Type}` convention, not this def.
8. **`modalClosed_unsat`** — `¬branchSatisfiable b acc`; mentions `acc` only vacuously but is
   stated against the coupled `branchSatisfiable`. Restate against the target's own predicate
   if needed; do not cherry-pick.
9. **`Proposition.beqToEq`** (private) — incidental `LawfulBEq` helper; check whether main
   already has it before copying (likely redundant).

### NOT candidates (architecture-coupled, out of scope)

- `modalStepBranch_preserves_sat` rewrite, `maxWorld`/`nextWorld`/`modalFreshWorld` (Branch.lean
  additions), `modalApplyOne` `modalNextWorld → modalFreshWorld acc` change (Rules.lean) — all
  global-Accessibility machinery. Ignore for salvage.

## Recommended Salvage Plan (zero-debt, no sorry/axioms)

**Phase A — characterization lemmas to Foundations/Modal Defs (low risk, immediately useful).**
Add `modalNegOf?_eq_some`, `modalOrOf?_eq_some`, `modalAndOf?_eq_some`, `modalImpOf?_eq_some`
to `Cslib/Logics/Modal/Tableau/Defs.lean` (next to the existing forward lemmas). They are pure,
acc-free, and each proves in 1–8 lines by `unfold; split; simp_all`. These can land on main
independently of the soundness redesign and directly unblock the recognizer-layer friction.

**Phase B — satisfaction bridge block to the cslib-364 redesign.** Cherry-pick `sfSat`,
`sfSat_pos`, `sfSat_neg`, `RuleResultSat`, `applyPropRule_sat` (the ~49-line block) into the
per-branch soundness file in the cslib-364 worktree. Adopt the `{W : Type}` universe
convention. These depend only on Phase-A lemmas + `Model`/`Satisfies` + Foundations
`applyPropRule`/`RuleResult`, all present regardless of accessibility architecture.

**Phase C — restate, do not copy, the branch-satisfiability glue.** Whatever
`branchSatisfiable`/`modalClosed_unsat` analogue the per-branch architecture needs must be
written against that architecture's own accessibility carrier. Use the commit only as a
*reference proof sketch*, not a source to merge.

**Do NOT**: merge the branch wholesale; import the `modalStepBranch_preserves_sat` rewrite;
re-introduce global `Accessibility` machinery; add any `sorry` or axiom to bridge a gap. If a
proof obligation in Phase B/C resists, restate the obligation against the per-branch predicate
rather than deferring.

## Verification Notes

- Portable lemmas were read directly from `git show 27d93e2d:...Soundness.lean` (lines
  ~158–215); signatures confirmed acc-free by grep (no `Accessibility`/`acc`/`m.r` tokens in
  the block).
- Dependency symbols (`applyPropRule`, `RuleResult`, `modalNegOf?`, `Model`, `Satisfies`)
  confirmed present on main via grep; **no full `lake build` attempted** (branch is known
  UNBUILT and a full build is slow / would fail on the coupled rewrite). The portable block's
  dependencies all resolve on main, so it should compile once transplanted.

## Tactic / Reuse Survey

- Recognizer characterization proof idiom: `unfold <recognizer> at h; split at h <;> simp_all`
  (the `_imp` case needs a manual nested `split`). Reuse this idiom for any further recognizer.
- Reuse-first: the propositional rule engine is already a Foundations abstraction
  (`Foundations/Logic/Tableau/`). No new rule-layer definitions are warranted; the salvage is
  purely *lemmas over existing definitions*.

## Open Questions for Implementer

1. Confirm against `specs/364_.../handoffs/BLOCKED-repair-guide.md` §4 (in the cslib-364
   worktree) that the friction is the recognizer inverse-direction — if so, Phase A alone may
   suffice.
2. Resolve the `applyPropRule` duplication (`PropositionalTableau.lean` vs
   `Tableau/PropositionalRules.lean`) — bind the salvage to the copy the cslib-364
   architecture uses.
3. Check whether `Proposition.beqToEq` is already available on main before copying.
