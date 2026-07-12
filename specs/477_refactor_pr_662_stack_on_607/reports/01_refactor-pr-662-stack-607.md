# Research Report: Refactor PR #662 to Stack on PR #607 (box + diamond both primitive)

**Task**: 477
**Type**: cslib
**Session**: sess_1783880050_660057
**Date**: 2026-07-12
**Scope**: Research only — no branches created, no PRs modified.

---

## 1. Executive Summary

PR #662 (`feat/modal-formula-primitives`, +444/-189, 8 files) currently makes the modal
`Proposition` type **box-primitive** over the primitive set `{atom, bot, imp, box}`, derives
diamond as `◇φ := ¬□¬φ`, and ships its **own** operator-typeclass file
`Cslib/Foundations/Logic/Connectives.lean` (91 lines: `HasBot`, `HasImp`, `HasAnd`, `HasOr`,
`HasBox`, `PropositionalConnectives`, `ModalConnectives`).

PR #607 (`fmontesi/connectives`, +221/-44, 9 files) introduces the canonical operator-typeclass
layer at `Cslib/Foundations/Logic/Operators.lean` (`HasAnd/HasOr/HasImp/HasIff/HasNot/HasBox/
HasDiamond/HasDynamicBox/HasDynamicDiamond/HasTensor`), keeps the modal `Proposition`
**diamond-primitive** (`{atom, not, and, diamond}`, box derived as `¬◇¬φ`), and — importantly —
**refactors the `Foundations/Logic/LogicalEquivalence` class signature** (adds an inference-system
parameter `S` and a `HasLogicalEquivalence` abbreviation).

The Zulip settlement (task 476) is to make **both □ and ◇ primitive**, "converging #607's diamond
basis with #662's box basis rather than deriving either." The recommended refactor therefore:

1. **Deletes #662's `Connectives.lean`** and reuses #607's `Operators.lean` typeclasses (this is
   the reuse-first win #662's own body flagged as "left to a follow-up").
2. **Keeps #607's propositional base** (`not`, `and` primitive; `or/imp/iff` derived) and adds
   **`box` as a fifth primitive constructor** alongside #607's existing `diamond` — yielding
   `Proposition = {atom, not, and, diamond, box}` with **both modalities primitive**.
3. **Turns the interdefinability law `◇φ ↔ ¬□¬φ` (`Satisfies.dual`) into a derived theorem**
   proved from the two now-primitive semantic clauses, instead of holding by definition.
4. **Migrates `Modal/LogicalEquivalence.lean` to #607's new `HasLogicalEquivalence` API** (mirroring
   #607's HML/CLL migration) — a required adaptation, since #607 changes the class arity but does
   not itself update the Modal instance.

**LOC verdict**: The stacked #662 diff is estimated at **~90–140 LOC**, comfortably under the
500-LOC target — because stacking on #607 lets us *delete* Connectives.lean (91 lines) and *avoid*
the propositional-base rewrite that inflated the original #662.

**Critical discrepancy to flag**: The task premise says "#607 makes both □ and ◇ primitive." It
does **not** — as of the current tip, #607 is still **diamond-primitive with `box := ¬◇¬φ`**
(confirmed against `fmontesi/connectives` and matching the task-476 re-verify note of 2026-07-11).
"Both primitive" is the *agreed target*, and making box primitive is precisely the work #662
contributes on top of #607. The plan below reflects that reality.

---

## 2. Reuse Check Protocol (CSLib reuse-first)

| Concept #662 needs | Existing abstraction (reuse) | Action |
|---|---|---|
| `HasBox`, `HasDiamond` | **#607 `Operators.lean`** (`HasBox`, `HasDiamond`, `prefix:40 □`/`◇`) | Reuse; delete #662's `HasBox` |
| `HasImp`, `HasAnd`, `HasOr`, `HasNot`, `HasIff` | **#607 `Operators.lean`** | Reuse; delete #662's `HasImp/HasAnd/HasOr` |
| `HasBot` | **Not in #607** (no bot; not/and base needs none) | Drop — not required under Path 1 (see §5) |
| `PropositionalConnectives`, `ModalConnectives` bundles | **Not in #607** | Drop — not needed for the classical cube |
| Parametric equivalence `Proposition.Equiv S` | **Already on upstream main** (`Modal/LogicalEquivalence.lean:28`) | Reuse; only add `box`/adjust Context |
| `LogicalEquivalence`/`HasLogicalEquivalence` framework | **#607 refactors** `Foundations/Logic/LogicalEquivalence` | Reuse #607's new API; migrate Modal instance |
| `Bot (Proposition Atom)` instance | Core Lean `Bot` | Only if bot kept; **not needed** under Path 1 |

**Finding**: #662's entire `Connectives.lean` duplicates #607's `Operators.lean`. The single
biggest cleanup is deleting it. The `Proposition.Equiv S` parametric machinery already exists
upstream, so #662's LogicalEquivalence "value" is adaptation, not new content.

---

## 3. Ground-Truth State of Both PRs (verified)

### PR #607 (`fmontesi/connectives`) — the base to stack on
- **New** `Cslib/Foundations/Logic/Operators.lean` (120 lines): one class per operator, all with
  `scoped` notation. `□`/`◇` are `prefix:40`; `∧` `infixr:36`, `∨` `infixr:30`, `→` `infixr:25`,
  `↔` `infixr:20`, `¬` `notation:max` (prefix 40). **No `HasBot`, no bundled classes.**
- **Modifies** `Modal/Basic.lean`: `Proposition = {atom, not, and, diamond}` (diamond primitive);
  `box`, `or`, `imp`, `iff` **derived**; registers `HasNot/HasAnd/HasDiamond/HasOr/HasImp/HasIff/
  HasBox` instances + `*_def` grind lemmas; renames `impl → imp` and `impl_iff_impl → imp_iff_imp`.
- **Refactors** `Foundations/Logic/LogicalEquivalence.lean`: class gains inference-system param
  `S`; adds `HasLogicalEquivalence` abbrev and `≡[S]` notation. Migrates **HML** and **CLL**
  instances to `HasLogicalEquivalence`. **Does not touch `Modal/LogicalEquivalence.lean`.**

### PR #662 (`feat/modal-formula-primitives`) — to be reworked
- **New** `Connectives.lean` (91 lines) — duplicates #607's operator layer → **to be deleted**.
- **Modifies** `Modal/Basic.lean`: `Proposition = {atom, bot, imp, box}` (box primitive, `deriving
  DecidableEq, BEq`); `neg/top/or/and/diamond/iff` derived; `Satisfies` clauses for `bot/imp/box`;
  proves `Satisfies.{neg_iff, diamond_iff, and_iff, or_iff}`, `dual := iff_iff_iff.mpr Iff.rfl`.
- **Modifies** `Denotation.lean`: denotation clauses `bot/imp/box`; `neg_denotation`.
- **Modifies** `LogicalEquivalence.lean`: `Context` constructors `impL/impR/box` (was
  `not/andL/andR/diamond`); `IsEquiv`, `Congruence`, and registers **old 3-arg**
  `LogicalEquivalence (Proposition Atom) (Judgement World Atom) Satisfies.Bundled`.
- **Modifies** `Cube.lean` (adds `import ...Relation.Euclidean`), `GrindLint.lean` (4 skips),
  `references.bib` (`Avigad2022`, `ChagrovZakharyaschev1997`), `Cslib.lean` (import Connectives).

### Upstream main (common base) — verified
- `Modal/Basic.lean`: `Proposition = {atom, not, and, diamond}` (diamond primitive, box derived).
- `Foundations/Logic/LogicalEquivalence.lean`: **3-arg** class `(Proposition, Judgement, Valid)`.
- `Modal/LogicalEquivalence.lean`: already has parametric `Proposition.Equiv (S : Set …)` (line 28)
  and an **old 3-arg** `instance : LogicalEquivalence …` (line 125).

**Coordination consequence**: Because #607 changes the `LogicalEquivalence` class arity but leaves
`Modal/LogicalEquivalence.lean` on the old 3-arg signature, that file *must* be migrated when #662
stacks on #607. #607 already demonstrates the migration on HML
(`instance : HasLogicalEquivalence (Proposition Label) (Satisfies.Judgement State Label)`).

---

## 4. Recommended Refactor Plan (file-by-file, Path 1)

Target final `Proposition (Atom) = {atom, not, and, diamond, box}` — **both modalities primitive**,
#607's propositional base retained. Diff measured **relative to #607's branch** (the new base).

### 4.1 `Cslib/Foundations/Logic/Connectives.lean` — **DELETE**
Remove the file entirely; all its typeclasses are provided by #607's `Operators.lean`.
Δ: removes 91 additions from #662's footprint. **Net stacked LOC: 0.**

### 4.2 `Cslib.lean` — revert the Connectives import
Drop `public import Cslib.Foundations.Logic.Connectives`. `Operators.lean` is already imported by
#607. Δ ≈ 0 (no net add).

### 4.3 `Cslib/Logics/Modal/Basic.lean` — add `box` as a primitive (~35–50 LOC)
- Change import to `public import Cslib.Foundations.Logic.Operators` (as #607 does); **do not**
  re-import/define `Connectives`.
- Add one constructor to the inductive: `| box (φ : Proposition Atom)` → primitives become
  `{atom, not, and, diamond, box}`. Both modalities now primitive.
- **Remove** #607's derived `def Proposition.box := ¬◇¬φ` and its `box_def` grind lemma.
- Point the `HasBox` instance at the new constructor: `instance : HasBox (Proposition Atom) :=
  ⟨Proposition.box⟩`; add `@[scoped grind =] lemma Proposition.box_def : φ.box = □φ := rfl`.
- Add the primitive `Satisfies` clause: `| .box φ => ∀ w', m.r w w' → Satisfies m w' φ`.
- `Satisfies.box_iff_forall` becomes `Iff.rfl` (was proved via `grind [Proposition.box]` in #607).
- **Convert interdefinability to derived results**: keep `Satisfies.dual : ◇φ ↔ ¬□¬φ` but prove it
  as a semantic theorem from the two primitive clauses (`by grind` or a short `constructor`),
  not by `iff_iff_iff.mpr Iff.rfl`. Optionally add `Satisfies.box_iff_not_diamond_not`
  (`□φ ↔ ¬◇¬φ`) as the companion derived lemma.
- Do **not** redefine `∧/∨/→/↔/¬/□/◇` notation — inherit it from `Operators.lean`.
- Keep #607's rename `imp_iff_imp` (do **not** reintroduce `impl_iff_impl`).

### 4.4 `Cslib/Logics/Modal/Denotation.lean` — add `box` denotation clause (~10 LOC)
- Add `| .box φ => {w | ∀ w', m.r w w' → w' ∈ φ.denotation m}` to `Proposition.denotation`
  (diamond clause stays as-is from main).
- The existing `not/and/diamond`-based `denotation` and `satisfies_mem_denotation`/`theoryEq_*`
  proofs are retained from main (no propositional-base rewrite). Add a `box_denotation`
  characterization lemma if `grind` needs it.

### 4.5 `Cslib/Logics/Modal/LogicalEquivalence.lean` — add `box` context + migrate to #607 API (~25 LOC)
- Keep main's `Context = {hole, not, andL, andR, diamond}`; **add** `| box (c : Context Atom)` and
  its `fill` clause `| box c => □(c.fill φ)`. (No `impL/impR` rewrite — we kept `not/and`.)
- Add the `box` case to the `Congruence` proof (one `induction` arm, analogous to `diamond`).
- **Migrate the framework instance** from the old 3-arg
  `LogicalEquivalence (Proposition Atom) (Judgement World Atom) Satisfies.Bundled`
  to #607's **`HasLogicalEquivalence (Proposition Atom) (Judgement World Atom)`**, mirroring #607's
  HML migration. Ensure `instance : HasInferenceSystem (Judgement World Atom) := ⟨Satisfies.Bundled⟩`
  is present (as #662 already adds).

### 4.6 `Cslib/Logics/Modal/Cube.lean` — minimal (~0–5 LOC)
Cube axioms reference only `□/◇/→`. Expect no change beyond possibly the
`import …Relation.Euclidean` line #662 already adds. Verify `four/b/five/d` still close under
both-primitive characterizations (they use `diamond_iff_exists`/`box_iff_forall`, now `rfl`).

### 4.7 `CslibTests/GrindLint.lean` — adjust skip list (~1–3 LOC)
Register `#grind_lint skip` entries only for the **new** `@[scoped grind]` modal lemmas that remain
(e.g. a new `box_denotation` / derived `dual` if tagged). Drop skips for lemmas that no longer exist
(`neg_denotation` name only if kept). Keep the list minimal.

### 4.8 `references.bib` — one entry (~8 LOC)
Add `ChagrovZakharyaschev1997` (box-first presentation, cited in Basic.lean docstring).
`Blackburn2001` already exists on main. **Drop `Avigad2022`** — it was only cited by the deleted
`Connectives.lean` Łukasiewicz docstring; under Path 1 the not/and base needs no Łukasiewicz note.

---

## 5. Design Decision: propositional base stays `not/and` (Path 1 vs Path 2)

**Path 1 (RECOMMENDED)** — keep #607's `{not, and}` propositional primitives, add `box` primitive.
Final: `{atom, not, and, diamond, box}`. The Zulip settlement mandates only that **both modalities**
be primitive ("converging #607's diamond basis with #662's box basis"); it says nothing about the
propositional base. Path 1 maximizes reuse of #607 and upstream main (Denotation/Context/Cube
proofs survive almost unchanged), and keeps the diff minimal.

**Path 2 (NOT recommended for this PR)** — also converge the propositional base to #662's
`{bot, imp}`. This is a *separate* axis motivated by future intuitionistic/minimal logic (where the
classical `and/or` encodings fail). It would reintroduce `HasBot`, rewrite Denotation/Context/Cube,
and roughly triple the diff — without being required by the settlement. Recommend deferring any
`bot/imp` propositional-base change to a dedicated follow-up PR after the modal-primitive
convergence lands.

---

## 6. LOC Budget (confirms <500)

| File | Stacked action | Est. Δ LOC |
|---|---|---|
| `Foundations/Logic/Connectives.lean` | delete | 0 (removes 91 from #662) |
| `Cslib.lean` | drop Connectives import | ~0 |
| `Modal/Basic.lean` | add `box` primitive + derived dual | 35–50 |
| `Modal/Denotation.lean` | add box clause + lemma | ~10 |
| `Modal/LogicalEquivalence.lean` | box context + `HasLogicalEquivalence` migration | ~25 |
| `Modal/Cube.lean` | import / verification | 0–5 |
| `CslibTests/GrindLint.lean` | trim skip list | 1–3 |
| `references.bib` | +ChagrovZakharyaschev1997 | ~8 |
| **Total** | | **~80–100 (worst case ~140)** |

**Well under 500 LOC.** The stack *shrinks* #662 (444 → ~100) because the typeclass file is deleted
and the propositional-base rewrite is avoided.

---

## 7. Branch / Stacking Mechanics (research only — do NOT execute)

- **Base branch**: rebase `feat/modal-formula-primitives` onto `fmontesi/connectives` (#607's head)
  instead of `main`. Local branches already exist: `pr607` and `feat/modal-formula-primitives`
  (plus `-v2`); backups `backup/662-pre-rebase-jul11` preserve the current tip.
- **GitHub PR base**: cross-fork PR bases are awkward. Two workable options:
  1. Set #662's PR base to `fmontesi/connectives` **iff** GitHub allows targeting that branch
     (same-upstream branch), presenting #662 explicitly as "stacks on #607."
  2. Keep #662 based on `main` but **rebase-and-rework locally** against a `#607 + #662`
     integration branch, and land #662 immediately after #607 merges (rebasing onto updated main).
     Given the Zulip note ("none of this has to move together"), option 2 is the lower-risk path:
     prepare the reworked commit now, hold until #607 lands, then fast-rebase.
- **Coordination**: #607 currently leaves `Modal/LogicalEquivalence.lean` on the old class arity;
  the #662 rework supplies that migration. Flag to fmontesi that #662's stacked version *completes*
  the `LogicalEquivalence` migration for the Modal layer (parallel to his HML/CLL changes).
- **Downstream**: #649 (LTL) rebases onto whichever of {#607,#662} lands first (per Zulip).

---

## 8. Risks and Mitigations

| Risk | Severity | Mitigation |
|---|---|---|
| **Task premise inaccuracy**: #607 is still diamond-primitive, not "both primitive" | High (scoping) | Plan treats "make box primitive" as #662's contribution *on top of* #607; verify #607's tip before implementing |
| Notation-precedence drift (#607 `Operators.lean` vs old #662 precedences) | Medium | Inherit all notation from `Operators.lean`; re-check any parenthesization-sensitive proofs |
| Name drift `imp_iff_imp` (#607) vs `impl_iff_impl` (#662) | Low | Standardize on #607's `imp_iff_imp` |
| `LogicalEquivalence` arity migration in Modal instance | Medium | Mirror #607's HML `HasLogicalEquivalence` instance exactly; ensure `HasInferenceSystem` instance present |
| `grind` proofs (`k/t/b/four/five/d`, `dual`) failing after clauses change | Medium | Characterization lemmas become `rfl`; re-run `lake build Cslib.Logics.Modal.Basic` and adjust grind hints; **zero-debt: no `sorry`, no new axioms** |
| `deriving DecidableEq, BEq` on the new inductive | Low | Retain #662's `deriving` clause if downstream (Tableau) needs it; otherwise drop to shrink diff |
| #607 not yet merged (moving target) | Medium | Option-2 mechanics (rework now, rebase on merge); keep backups |

**Zero-debt compliance**: No step introduces `sorry`, deferral, or new axioms. All interdefinability
lemmas are provable classically from the two primitive semantic clauses (`Satisfies` for `not` is
classical negation), so `Satisfies.dual` and companions are honest theorems.

---

## 9. Tactic Survey (advisory)

- Interdefinability `◇φ ↔ ¬□¬φ`: after adding both primitive `Satisfies` clauses, `by grind` should
  close it (all characterization lemmas are `@[scoped grind =]` `rfl`s); fall back to an explicit
  `constructor <;> ...` with `Classical.em` if grind needs a decidability nudge (see #662's existing
  `Satisfies.or_iff` pattern using `Classical.em`).
- Cube axioms: retained `grind [instSymm.symm]` / `grind [hSer.serial]` style from #662 should carry
  over unchanged since `diamond`/`box` characterizations remain available to grind.

---

## 10. Recommended Next Action

Proceed to **/plan 477**. The plan should phase the work as: (P1) delete `Connectives.lean` + fix
imports; (P2) add `box` primitive to `Basic.lean` + derive `dual`; (P3) `Denotation.lean` box
clause; (P4) `LogicalEquivalence.lean` box context + `HasLogicalEquivalence` migration; (P5)
`Cube.lean`/`GrindLint`/`references.bib` + full `lake build`/`lake test` green. Each phase is a
single small edit + build, keeping the total well under 500 LOC.
