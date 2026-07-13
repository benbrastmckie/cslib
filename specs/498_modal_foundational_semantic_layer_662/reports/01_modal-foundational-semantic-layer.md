# Research Report: Task 498 — Modal Foundational Semantic Layer for PR #662

**Task type**: cslib (Lean 4 formalization + PR coordination)
**Branch**: `task-441-native-refactor` (source metalogic lives here)
**Parent/coordination**: task 476; follow-up task 497 (imp/impl naming)
**Date**: 2026-07-13

## Executive Summary

Task 498 has two coordinated deliverables:

1. **Recommend on PR #607** (`fmontesi/connectives`) that the modal `Proposition` adopt the
   **native 7-primitive set** `{atom, bot, imp, and, or, box, diamond}` (as in task-441
   `Cslib/Logics/Modal/Basic.lean`), replacing #607's current **not-based / box-derived**
   4-primitive form `{atom, not, and, diamond}` (where `or`, `imp` are De Morgan-derived and
   `box := ¬◇¬φ` is definitional).

2. **Rework PR #662** from its current trivial "box-alongside-diamond" delta (+39/−17) into a
   **self-contained ~300 LOC foundational semantic layer slice** of the task-441 metalogic on
   those native primitives: native `Proposition` + `Satisfies`/denotation + duality **theorem**
   + per-connective decomposition + K-axiom validity.

The push/stack of #662 is **gated on #607 first adopting the native primitives** (they edit the
same `Modal/Proposition` type; #662 cannot cleanly stack a native-primitive metalogic on top of
#607's derived encoding without conflict).

**Zero-debt note**: The entire slice already exists, compiles, and is sorry-free on
`task-441-native-refactor`. This task is a *port/extraction*, not new proof development — no
`sorry`, no new axioms are required.

---

## 1. Source Metalogic (task-441) — the ~300 LOC slice

The self-contained foundational semantic layer is drawn from exactly two files on the current
branch. The frame-correspondence *system* axioms (T, B, 4, 5, D and their converses) are
**excluded** — they belong to a later "systems" PR, not the foundational semantic slice.

### 1a. `Cslib/Logics/Modal/Basic.lean` (441 LOC total) — include lines 63–283 and 430–441

| Lines | Declaration | Role in slice |
|-------|-------------|---------------|
| 63–68 | `structure Model (World Atom)` (`r`, `v`) | Kripke model |
| 70–87 | `inductive Proposition` — native `{atom, bot, imp, and, or, box, diamond}` `deriving DecidableEq` | **Native primitive datatype** |
| 89–98 | `instance : ModalConnectives` (`bot`,`imp`,`box`) | notation typeclass wiring |
| 99–109 | `instance : HasAnd` / `HasOr` / `HasDia` | native and/or/diamond wiring |
| 111–126 | `Proposition.neg` / `.top` (derived, Łukasiewicz) + `neg_def`/`top_def` `@[simp]` | derived connectives |
| 128–141 | `Proposition.iff`; `instance : Bot`; scoped notation `¬ ∧ ∨ → □ ◇ ↔` | notation |
| 143–153 | `def Satisfies` — one clause per connective (atom/bot/imp/and/or/box/diamond) | **Denotational core** |
| 155–169 | `Satisfies.neg_iff`, `.diamond_iff`, `.and_iff`, `.or_iff` | **per-connective decomposition (Iff.rfl-level)** |
| 171–190 | `structure Judgement`; `Modal[m,w ⊨ φ]` notation; `Satisfies.Bundled`; `instance : HasInferenceSystem` | inference-system wiring |
| 194–228 | `derivation_def`; `neg_satisfies`; `Satisfies.or_iff_or / impl_iff_impl / box_iff_forall / diamond_iff_exists / and_iff_and` (all `⇓Modal[...]`-form, `@[scoped grind =]`) | **bundled decomposition lemmas** |
| 230–261 | `theory`, `TheoryEq`, `TheoryEq.ext_iff`, `satisfies_theory`, `not_theoryEq_satisfies`, `theoryEq_satisfies` | theory-equivalence infrastructure |
| 263–268 | `Satisfies.k` — **K axiom valid in all models** | **K-axiom validity** |
| 270–283 | `Satisfies.dual` — `◇φ ↔ ¬□¬φ` proved as a **genuine semantic theorem** (uses `by_contra`/`push Not`, i.e. classical LEM) | **duality theorem** |
| **285–428** | **`Satisfies.t/.t_refl/.t_box_diamond/.b/.b_symm/.four/.four_trans/.five/.five_rightEuclidean/.d/.d_serial`** | **EXCLUDE — frame-correspondence systems layer** |
| 430–441 | `Proposition.valid`, `logic` | validity in a model class |

Slice from Basic.lean = lines 63–283 + 430–441 ≈ **233 LOC**.

### 1b. `Cslib/Logics/Modal/Denotation.lean` (91 LOC total) — include lines 24–90

| Lines | Declaration | Role |
|-------|-------------|------|
| 24–34 | `Proposition.denotation : Proposition Atom → Set World` — one clause per connective (`∅` for bot, `ᶜ ∪` for imp, `∩`/`∪`, `{w | ∀…}`/`{w | ∃…}`) | set-valued semantics |
| 36–65 | `satisfies_mem_denotation` — `w ∈ φ.denotation m ↔ ⇓Modal[m,w ⊨ φ]` by structural induction (7 cases, one per connective) | **bridge: denotation ↔ Satisfies** |
| 67–72 | `neg_denotation` | derived-neg denotation |
| 74–89 | `theoryEq_denotation_eq` — theory-equiv ↔ denotational-equiv | denotational equivalence |

Slice from Denotation.lean ≈ **67 LOC**.

**Total slice ≈ 233 + 67 ≈ 300 LOC** — matches the task's "~300 LOC" exactly, and matches the
enumerated contents (native Proposition + Satisfies/denotation + duality + per-connective
decomposition + K validity), with the frame axioms deliberately excluded.

### Why native primitives (the justification to lift into the recommendation)

The header docstring of `Basic.lean` (lines 26–50) already states the argument verbatim. The
three load-bearing points:

1. **One decomposition rule per connective** for tableau/truth-lemma machinery. With native
   `box`, `Satisfies.box_iff_forall` is `Iff.rfl` (Basic.lean:216–218); with native `diamond`,
   `diamond_iff` is `Iff.rfl` (160–161). Structural induction over the datatype gets one case
   per connective — **no Łukasiewicz-bridge lemmas** needed to unfold `¬◇¬` or `¬(¬·∧¬·)`.
2. **Reuse for intuitionistic/minimal modal systems** (IK, CK — cf. [Blackburn2001] Ch.1,
   [ChagrovZakharyaschev1997] §3.1): in those settings `□` and `◇` are **independent**
   operators, so both must be native constructors. The native datatype is reusable across all
   three logic strengths; the derived/duality encoding is classical-only.
3. **Duality recovered as a theorem, not a definition**: `Satisfies.dual : ◇φ ↔ ¬□¬φ`
   (Basic.lean:270–283) is proved semantically via excluded middle, rather than holding
   definitionally. At the proof-system level the same duality is recovered via the
   `AxiomDiaDualityFwd`/`AxiomDiaDualityBack` characterization schemata
   (`Foundations/Logic/Axioms.lean:196–214`).

---

## 2. PR #607 — current modal Proposition and the concrete recommendation

**#607 branch** `upstream/fmontesi/connectives`, file `Cslib/Logics/Modal/Basic.lean` (311 LOC).
Current modal `Proposition`:

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | not (φ : Proposition Atom)          -- NEGATION primitive
  | and (φ₁ φ₂ : Proposition Atom)
  | diamond (φ : Proposition Atom)      -- DIAMOND primitive
-- derived:
def Proposition.or  (φ₁ φ₂) := ¬(¬φ₁ ∧ ¬φ₂)   -- De Morgan
def Proposition.imp (φ₁ φ₂) := ¬φ₁ ∨ φ₂
def Proposition.box (φ)      := ¬◇¬φ            -- box DERIVED from diamond
```

So #607's basis is `{atom, not, and, diamond}` with `or`/`imp`/`box` derived, and **no `bot`
primitive** (propositional `⊥` is represented as `atom ⊥` under `[Bot Atom]` in
`Logics/Propositional/Defs.lean`, Thomas Waring's four-primitive type). #607 *already* has a
complete semantic layer for this basis: `Satisfies` (atom/not/and/diamond clauses),
`Satisfies.not_iff_not/.and_iff_and/.diamond_iff_exists/.or_iff_or/.imp_iff_imp/.iff_iff_iff/.box_iff_forall`,
`Judgement`+`HasInferenceSystem`, `theory`/`TheoryEq`, `Satisfies.k` (proved `by grind`), and
`Satisfies.dual` (near-definitional there).

**Typeclass layer** — #607 consolidates operators into `Foundations/Logic/Operators.lean`:
`HasAnd`, `HasOr`, `HasImp`, `HasIff`, `HasNot`, `HasBox`, **`HasDiamond`**, plus dynamic-logic
classes. The current branch's `Foundations/Logic/Connectives.lean` is *already* aligned to this
"one class per operator" direction (its header cites #607) but adds three things #607 lacks:
- **`HasBot`** (atomic bottom class) — #607 has none (uses `atom ⊥`);
- **`HasDia`** — task-441's name for #607's `HasDiamond` (**naming divergence**, see below);
- **bundled** `PropositionalConnectives` (`bot`,`imp`, defaulted `neg`/`top`) and
  `ModalConnectives` (extends + `HasBox`) — #607 has no bundled classes.

### What the recommendation to #607 should concretely say

Deliver as a **single plain PR comment** (head branch is in-org `leanprover/cslib`, not a fork —
coordination stays comment-only; **never** a suggested-change/push/rebase of `fmontesi/connectives`,
per the pr-607-review posting guidance). Content:

1. **Adopt the native 7-constructor modal `Proposition`** `{atom, bot, imp, and, or, box,
   diamond}` (bot native, imp/and/or native, **box and diamond both native and independent**),
   replacing the `not`-primitive / De-Morgan-derived-or/imp / `box := ¬◇¬φ` encoding.
2. **Justification** (the three points in §1): (i) one `Iff.rfl` decomposition rule per
   connective for tableau + truth-lemma structural induction, no bridge lemmas; (ii) reuse for
   intuitionistic/minimal modal systems where □/◇ are independent; (iii) duality `◇φ ↔ ¬□¬φ`
   recovered as `Satisfies.dual` (a semantic theorem) instead of a definition.
3. **Typeclass instances entailed**: `Proposition` gains `HasBot`, `HasImp`, `HasAnd`, `HasOr`,
   `HasBox`, `HasDia`/`HasDiamond` instances directly (box no longer via `HasNot`+`HasDiamond`),
   with `neg`/`top` as derived `abbrev`s (Łukasiewicz `¬φ := φ→⊥`, `⊤ := ⊥→⊥`).
4. **Naming reconciliation** (defer specifics to task 497): `HasDia` (task-441) vs `HasDiamond`
   (#607); confirm `HasImp.imp` (both already agree on `imp`, not `impl`). Flag that a `HasBot`
   atomic class is needed in `Operators.lean` (or #662 supplies it).
5. **Reassurance**: necessitation and K still touch only `□`; making □/◇ independent does **not**
   make the proof theory heavier (K is one clause, duality is one theorem).

---

## 3. PR #662 — current state and what changes

**Current** (`gh pr view 662`): title *"feat(Logics/Modal): make box primitive alongside
diamond (stacked on #607)"*, base `fmontesi/connectives`, head `feat/modal-formula-primitives`,
state OPEN, **+39/−17 across 3 files** (`Modal/Basic.lean +29/−17`, `Modal/Denotation.lean +1`,
`Modal/LogicalEquivalence.lean +9`). It merely adds `box` as an extra constructor **alongside**
#607's still-`not`-primitive/derived-or/imp basis, with `◇φ ↔ ¬□¬φ` as a derived lemma. Pre-stack
tip backed up as `backup/662-pre-stack-jul12` (`8d7a061e`); other backups:
`backup/662-pre-rebase`, `backup/662-pre-rebase-jul11`.

**Rework target**: replace this trivial delta with the **~300 LOC foundational semantic layer
slice** of §1 on the full native 7-primitive basis. Concretely #662 becomes (once #607 has
adopted the primitives): native `Proposition` + notation/instances + `Satisfies` + per-connective
decomposition (all `Iff.rfl`) + `Judgement`/`HasInferenceSystem` + `theory`/`TheoryEq`
infrastructure + `Satisfies.k` + `Satisfies.dual` (theorem) + `Proposition.denotation` +
`satisfies_mem_denotation` + `theoryEq_denotation_eq` + `Proposition.valid`/`logic`. **Exclude**
the T/B/4/5/D frame-correspondence axioms (Basic.lean:285–428) — those are a follow-up systems PR.

**Gating**: the actual push/re-stack of #662 waits until #607 adopts the native primitives,
because both PRs edit the same `Modal/Proposition` and the native metalogic cannot layer over
#607's derived encoding without conflict.

**Task conclusion (implementation phase, not this research phase)**: squash-commit #662 with the
foundational-semantic-layer contribution, then revise
`specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md`.

---

## 4. Zulip coordination revision (`specs/476_.../artifacts/zulip-coordination.md`)

**Current draft** (DRAFT, not posted; requires explicit user approval before sending) describes
#662 as *"reworked to add `box` as a primitive constructor alongside `diamond`… a small diff
(three files, ~40 lines)"* and frames the open question purely as the propositional-base choice
(#648's five-primitive `{atom,bot,imp,and,or}` vs #607's four-primitive `atom ⊥`).

**Revision should replace the box-alongside-diamond framing with the new strategy**:
- Recommend that **#607 adopt the native modal primitive set** `{atom, bot, imp, and, or, box,
  diamond}` (bot/imp/box/diamond native; box+diamond independent; duality a theorem), with the
  three-point justification from §1.
- Describe **#662 as a substantial foundational semantic-layer slice (~300 LOC)** of the task-441
  metalogic (Satisfies/denotation + duality theorem + per-connective decomposition + K validity),
  **not** a ~40-line box-alongside-diamond delta.
- Preserve the accuracy-discipline preamble (re-verify PR/CI state before posting; fmontesi back
  23 July; comment-only, never push to `fmontesi/connectives`).
- Keep the open coordination items: propositional-base decision (#648 five-primitive, already
  Thomas-Waring-approved 2026-07-06) and the `imp`/`impl` naming follow-up (task 497). Note the
  modal primitive recommendation and the propositional-base question are now parallel asks to
  fmontesi.

---

## 5. Concrete Lean code direction (port map + reuse)

### Definitions/theorems to port (signatures — verbatim from task-441 branch)

```lean
structure Model (World Atom : Type*) where
  r : World → World → Prop
  v : World → Atom → Prop

inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom) | bot
  | imp (φ₁ φ₂ : Proposition Atom) | and (φ₁ φ₂ : Proposition Atom) | or (φ₁ φ₂ : Proposition Atom)
  | box (φ : Proposition Atom) | diamond (φ : Proposition Atom)
  deriving DecidableEq

def Satisfies (m : Model World Atom) (w : World) : Proposition Atom → Prop   -- 7 clauses
theorem Satisfies.diamond_iff : Satisfies m w (◇φ) ↔ ∃ w', m.r w w' ∧ Satisfies m w' φ := Iff.rfl
theorem Satisfies.and_iff  : … := Iff.rfl
theorem Satisfies.or_iff   : … := Iff.rfl
theorem Satisfies.neg_iff  : Satisfies m w (¬φ) ↔ ¬ Satisfies m w φ         -- ⟨…,…⟩
theorem Satisfies.box_iff_forall : ⇓Modal[m,w ⊨ □φ] ↔ ∀ w', m.r w w' → ⇓Modal[m,w' ⊨ φ] := Iff.rfl
theorem Satisfies.k    : ⇓Modal[m,w ⊨ □(φ₁ → φ₂) → (□φ₁ → □φ₂)]              -- simp only [Satisfies]; intros
theorem Satisfies.dual : ⇓Modal[m,w ⊨ ◇φ ↔ ¬□¬φ]                            -- by_contra + push Not (classical)
def  Proposition.denotation (m) : Proposition Atom → Set World               -- 7 clauses
theorem satisfies_mem_denotation : w ∈ φ.denotation m ↔ ⇓Modal[m,w ⊨ φ]      -- induction φ, 7 cases
theorem theoryEq_denotation_eq : TheoryEq m w₁ w₂ ↔ (∀ φ, w₁∈φ.denotation m ↔ w₂∈φ.denotation m)
def  Proposition.valid (S : Set (Model World Atom)) (φ) : Prop
def  logic (S : Set (Model World Atom)) : Set (Proposition Atom)
```

### Reuse (reuse-first checks performed)

- **CSLib Foundations** — reuse rather than re-define:
  - `Cslib.Foundations.Logic.Connectives` (task-441) / `#607 Operators.lean`: `HasBot`, `HasImp`,
    `HasAnd`, `HasOr`, `HasBox`, `HasDia`/`HasDiamond`, `HasIff`, and bundled `ModalConnectives`
    / `PropositionalConnectives` (with defaulted `neg`/`top`). **Do not introduce new notation
    typeclasses** — the `¬ ∧ ∨ → □ ◇ ↔` scoped notations are already typeclass-backed.
  - `Cslib.Foundations.Logic.InferenceSystem`: `HasInferenceSystem`, the `⇓` derivation notation
    (`⇓Modal[m,w ⊨ φ]`), and `Judgement` wiring — reuse directly.
  - `Cslib.Foundations.Logic.Axioms` (`AxiomDiaDualityFwd/Back`, §DiaDuality): the proof-system
    counterpart of the semantic `Satisfies.dual` — cite in docstrings; **out of scope** for the
    semantic slice (belongs to `ProofSystem/Instances`).
- **Mathlib** — instantiated, not re-proved: `Set.ext_iff` (`TheoryEq.ext_iff`); `Set.mem_union`,
  `Set.mem_compl_iff`, `Set.mem_inter_iff`, `Set.mem_setOf_eq` (denotation induction);
  `Classical`/excluded middle via `by_contra`+`push Not` (`Satisfies.dual`); `Bot`/`Set` core.
  Frame-axiom relation classes (`Std.Refl`, `Std.Symm`, `IsTrans`, `Relation.Serial`,
  `Relation.RightEuclidean`) are **only** needed by the excluded T/B/4/5/D layer — not the slice.
- No new definitions or abstractions are recommended; this is a faithful extraction of existing,
  compiling, sorry-free code.

### CSLib contribution standards relevant to the slice

- **`import Cslib.Init` first** in every file (enforced by `lake exe checkInitImports`).
- **docBlame**: every declaration needs a docstring — the task-441 source already has them; carry
  them across verbatim.
- **defLemma**: Prop-valued results are `theorem`/`lemma`, not `def` (source already conforms).
- **defsWithUnderscore / lowerCamelCase**: names like `satisfies_mem_denotation`,
  `theoryEq_denotation_eq` follow mathlib snake_case for theorem names (acceptable); type/def
  names are camelCase (`Proposition`, `Satisfies`, `TheoryEq`).
- **simpNF**: `@[simp]` lemmas (`neg_def`, `top_def`, `Proposition.denotation`, `valid`, `logic`,
  `Satisfies.Bundled`) already carry verified simp forms.
- **NOTATION.md**: notation is scoped and typeclass-backed (Option — box/diamond prefix `□`/`◇`,
  infix `∧ ∨ → ↔`) — no unscoped/un-backed notation introduced.
- **ORGANISATION.md**: file stays under `Cslib/Logics/Modal/` (`Basic.lean` + `Denotation.lean`);
  Foundations abstractions stay in `Cslib/Foundations/Logic/`.
- **CI order** before PR: `lake exe cache get` → `lake build` → `lake exe checkInitImports` →
  `lake lint` → `lake exe lint-style` → `lake test` → `lake exe mk_all --module` (only if new
  files) → `lake shake --add-public --keep-implied --keep-prefix`.
- **AI disclosure** in the PR description per CSLib/Mathlib policy.

---

## 6. Open questions / coordination risks

1. **Gating dependency**: #662's substantial form cannot be pushed until #607 adopts the native
   primitives. If fmontesi declines the primitive change, #662 must fall back to either the
   current box-alongside-diamond delta or a standalone (non-stacked) contribution — flag as a
   decision point.
2. **`HasDia` vs `HasDiamond`** and **`HasBot` absence in #607's `Operators.lean`**: reconcile
   before stacking (task 497 covers `imp`/`impl`; this adds the diamond-class name and `HasBot`).
3. **Propositional base (#648 vs #607)** remains an independent open decision (five-primitive
   `{atom,bot,imp,and,or}`, Thomas-Waring-approved, vs four-primitive `atom ⊥`); the modal
   recommendation is parallel to it, not blocked by it.
4. **Do not post the Zulip draft or any #607 comment without explicit user approval**; re-verify
   live PR/CI state at post time (fmontesi returns 23 July).

## Sources

- `Cslib/Logics/Modal/Basic.lean` (task-441-native-refactor) — native metalogic source
- `Cslib/Logics/Modal/Denotation.lean` (task-441-native-refactor) — denotational semantics
- `Cslib/Foundations/Logic/Connectives.lean`, `.../Axioms.lean` — typeclass + duality-axiom layer
- `upstream/fmontesi/connectives:Cslib/Logics/Modal/Basic.lean`, `.../Foundations/Logic/Operators.lean`, `.../Logics/Propositional/Defs.lean` — #607 current state
- `gh pr view 662 --repo leanprover/cslib` — #662 current state (+39/−17, base `fmontesi/connectives`)
- `specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md`, `pr-607-review.md`
