# Task 420 — Research: Prerequisites for a Native Intuitionistic-Faithful Propositional Embedding (DOC-ONLY)

**Task type**: cslib (documentation design note — no Lean change)
**Status**: research / no Lean source modified; this report is the only artifact.
**Date**: 2026-06-29
**Source**: `specs/415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md` §3 + Rank 5.

> AI-policy note: Per the CSLib/Mathlib AI usage policy, any prose intended for upstream
> (PR descriptions, ORGANISATION.md text, Zulip) must be **human-authored**. The drafts in
> §5 below are scaffolds for a human author, not finished copy.

---

## 1. Summary / Verdict

The four prerequisites stated in task 415 §3 ("What a structure-preserving embedding would
require") are **all accurate against the current codebase** and are stated at the right level of
abstraction. Verified directly against source:

1. **Native `and`/`or` constructors** — CONFIRMED absent on every target syntax.
2. **Gated intuitionistic target proof system** — CONFIRMED absent on every target logic.
3. **Birelational target semantics bridging to PL `IForces`** — CONFIRMED; PL `IForces` exists
   and is exactly the bridge target. One refinement on the word "birelational" below.
4. **Proof-theoretic preservation/faithfulness theorem** — CONFIRMED; current results are
   classical-semantic (`Tautology ↔ valid`), not proof-theoretic.

**Placement recommendation**: There is **no `docs/` directory** in the repo. `ORGANISATION.md`
exists, is actively maintained, is the canonical in-repo design-overview document, and explicitly
frames itself as "still under active discussion and is subject to change." The lowest-friction,
most-discoverable home is a **new short subsection in `ORGANISATION.md`** under the Logics
section (near the per-logic embedding entries), recording the four prerequisites and the
classical-scope boundary. A standalone `docs/design/` doc is a viable alternative but would
introduce a new top-level convention the repo does not currently use.

**Secondary finding (actionable)**: the forward-looking limitation note is **asymmetric across
the three embedding modules**. `Modal/FromPropositional.lean` and `Temporal/FromPropositional.lean`
carry a full `## Limitations` section naming the future-native-embedding requirement; the Bimodal
embedding (`Bimodal/Embedding/PropositionalEmbedding.lean`) only states the classical-equivalence
rationale and **omits** the forward-looking note. A centralized design note should be
cross-referenced from all three, and the Bimodal docstring could be brought into parity (a
trivial doc edit, in scope for the implementer if desired).

**No blockers. No Lean change. Effort: S.**

---

## 2. Prerequisite-by-Prerequisite Verification

### Prereq 1 — Native `and`/`or` constructors (not the Łukasiewicz encoding)

**Accurate.** Source-verified constructor sets:

| Type | Constructors | Native ∧/∨? | Anchor |
|------|--------------|-------------|--------|
| `PL.Proposition` | `{atom, bot, imp, and, or}` | **yes** (`HasAnd`/`HasOr` instances) | `Propositional/Defs.lean:89,91,118-123` |
| `Modal.Proposition` | `{atom, bot, imp, box}` | no | `Modal/Basic.lean:70-78` |
| `Temporal.Formula` | `{atom, bot, imp, untl, snce}` | no | (per 415 audit; `Temporal/Syntax/Formula.lean`) |
| `Bimodal.Formula` | `{atom, bot, imp, box, untl, snce}` | no | docstring `Bimodal/.../PropositionalEmbedding.lean:36` |

The three embeddings encode `and`/`or` via Łukasiewicz: `A∧B ↦ (A→(B→⊥))→⊥`,
`A∨B ↦ (A→⊥)→B` (`Modal/FromPropositional.lean:58-63`,
`Bimodal/.../PropositionalEmbedding.lean:63-64`). These are classically but not
intuitionistically valid ([Wajsberg1938], [McKinsey1939] — both present in `references.bib:319,331`).
A native embedding therefore requires adding `and`/`or` arms to each target inductive — a syntax
change rippling through every recursor (denotation, satisfaction, derivation, tableau).

### Prereq 2 — Gated intuitionistic target modal/temporal system

**Accurate.** At the PL level the intuitionistic/minimal distinction is real and gated:
`efq` carries `[IsIntuitionistic T]` (`Propositional/NaturalDeduction/Basic.lean:48,56,61,182`),
`botL` carries `[IsIntuitionistic T]` (`SequentCalculus/LJ/Basic.lean:100`). No analogous
`IsIntuitionistic`-gated derivation system exists for Modal, Temporal, or Bimodal (415 audit
grep: the only `Intuitionistic` hits in those trees are a Fitting **book-title citation** in
`Modal/Tableau/Defs.lean:40`, not a logic). A native embedding requires a gated-`efq`
modal/temporal proof system mirroring the PL design — currently absent.

### Prereq 3 — Birelational target semantics bridging to PL `IForces`

**Accurate, with one precision refinement.** PL `IForces` exists and is exactly the intended
bridge target:

- `IForces` (`Propositional/Semantics/Kripke.lean:81-88`) is a `Preorder`-based forcing relation
  with **native** `and`/`or` cases (`IForces_and` uses `∧`, `IForces_or` uses `∨`,
  `Kripke.lean:106-116`) and an intuitionistic `imp` case quantifying over future worlds
  (`∀ w', w ≤ w' → ...`, `:86`).
- It is parameterized by a `botForces : World → Prop` predicate (`KripkeModel.botForces`,
  `Kripke.lean:63`) with an upward-closure obligation `bf_upward_closed` (`:66-67`) — this is the
  minimal-vs-intuitionistic knob (minimal = `botForces` arbitrary upward-closed; intuitionistic =
  `fun _ => False`, see `Kripke.lean:26-28,148`).
- `iforces_persistence` (`Kripke.lean:125`, Prop 2.1 of [ChagrovZakharyaschev1997],
  `references.bib:75`) gives upward persistence.

**Refinement on "birelational":** PL `IForces` is itself *single-relation* (one preorder `≤`).
The word "birelational" correctly describes the **target intuitionistic-modal** semantics, which
in the standard treatment carries **two** relations — the intuitionistic preorder `≤` and the
modal accessibility `R` (with a frame condition relating them, e.g. `≤;R ⊆ R;≤`). The bridge a
native embedding needs is: target birelational forcing of `□`/`U`/`S` restricting, on the `≤`
relation and propositional fragment, to PL's single-relation `IForces`. The prerequisite is
accurate; the design note should state the `≤`-vs-`R` distinction explicitly so it is not read as
"PL is birelational."

### Prereq 4 — Proof-theoretic preservation/faithfulness theorem

**Accurate.** Current preservation results are **classical-semantic**, not proof-theoretic:
`modal_satisfies_toModal_iff_evaluate` (`Modal/FromPropositional.lean:106`) bridges to the
two-valued `PL.Evaluate` (Bool) using classical `by_contra`/`by_cases`, and conservativity is
`Tautology ↔ valid` (`tautology_iff_toModal_valid:162`, `*_conservative_extension`). A native
intuitionistic embedding instead needs a **proof-theoretic** statement of the form
`IPL.Derivable φ → IModal.Derivable φ.toIModal` (preservation) plus the converse
(faithfulness/conservativity), not merely classical tautology preservation.

---

## 3. Where the Design Note Belongs

### Option A (recommended) — subsection in `ORGANISATION.md`

`ORGANISATION.md` (10.8 KB, last modified 2026-06-29) is the canonical in-repo structural/design
overview. It already has per-logic sections (`### Modal Logic`, `### Temporal Logic`,
`### Bimodal Logic`, each listing `FromPropositional.lean` / `Embedding/`) and an explicit
"under active discussion and subject to change" framing that invites design notes. Adding a short
subsection (e.g. **"### Propositional Embeddings and the Classical-Scope Boundary"**) keeps the
note discoverable, co-located with the directory map readers already consult, and introduces no
new convention.

Caveat: `ORGANISATION.md` is otherwise a pure directory map; a multi-paragraph design-rationale
note is slightly off-genre. Keep it tight (the four-item list + a one-line pointer to the three
module docstrings).

### Option B (alternative) — new `docs/design/` doc

No `docs/` directory exists today. Creating `docs/design/native-intuitionistic-embedding.md`
gives more room and keeps `ORGANISATION.md` a pure map, but establishes a new top-level
convention not currently present in the repo (top-level docs are flat: `CONTRIBUTING.md`,
`GOVERNANCE.md`, `NOTATION.md`, `ORGANISATION.md`, `CODE_OF_CONDUCT.md`, `README.md`). Choose this
only if maintainers prefer to keep `ORGANISATION.md` strictly structural.

### Option C (complementary, not a substitute) — module docstrings

The natural fine-grained home is the embedding module docstrings, which already carry the
limitation notes. Recommended regardless of A/B: **bring the Bimodal docstring to parity** by
adding the forward-looking `## Limitations` note that Modal and Temporal already have
(`Bimodal/Embedding/PropositionalEmbedding.lean` currently states only the classical-equivalence
rationale at `:33-41`, omitting the "if CSLib adds intuitionistic modal logic, a separate
embedding will be required" sentence present at `Modal/FromPropositional.lean:36-41` and
`Temporal/FromPropositional.lean:34-40`).

**Recommendation**: Option A as the single canonical note + Option C parity edit so all three
modules point at the same boundary. Defer Option B unless maintainers object to design prose in
`ORGANISATION.md`.

---

## 4. Confirmed File Anchors (for the planner/implementer)

| Item | Location |
|------|----------|
| Target home for the note | `ORGANISATION.md` (Logics section, ~`:108-211`) |
| PL native `and`/`or` + `HasAnd`/`HasOr` | `Propositional/Defs.lean:89,91,118-123` |
| PL gated `efq` (`IsIntuitionistic`) | `Propositional/NaturalDeduction/Basic.lean:182` |
| PL gated `botL` (`IsIntuitionistic`) | `SequentCalculus/LJ/Basic.lean:100` |
| PL `IForces` + `botForces` + persistence | `Propositional/Semantics/Kripke.lean:58-130` |
| `Modal.Proposition` constructors | `Modal/Basic.lean:70-78` |
| Modal Łukasiewicz embedding + Limitations note | `Modal/FromPropositional.lean:36-63` |
| Modal classical bridge | `Modal/FromPropositional.lean:106,162` |
| Temporal embedding + Limitations note | `Temporal/FromPropositional.lean:34-62` |
| Bimodal embedding (note MISSING forward-looking limitation) | `Bimodal/Embedding/PropositionalEmbedding.lean:33-64` |
| Citations | `references.bib:75` (ChagrovZakharyaschev1997), `:319` (McKinsey1939), `:331` (Wajsberg1938) |

---

## 5. Scaffold Content for the Note (human-rewrite before committing)

> **[SCAFFOLD — human-author before committing to ORGANISATION.md / any upstream surface]**
>
> **Propositional embeddings target classical logic.** `toModal`, `toTemporal`, and `toBimodal`
> map `{atom, bot, imp}` structurally and encode `{and, or}` via the Łukasiewicz definitions
> (`A∧B = ¬(A→¬B)`, `A∨B = ¬A→B`), which are classically but not intuitionistically valid. This
> is a deliberate, documented boundary: the embeddings certify the classical (CPL) fragment only.
>
> A future *native, intuitionistic-faithful* propositional embedding — needed if CSLib adds an
> intuitionistic modal/temporal logic — requires **all four** of:
> 1. **Native `and`/`or` constructors** on the target syntax (not Łukasiewicz), with the
>    corresponding recursor/denotation/derivation arms.
> 2. **A gated intuitionistic target proof system** (an `[IsIntuitionistic]`-gated `efq`
>    modal/temporal derivation system mirroring the PL design).
> 3. **A birelational target semantics** (intuitionistic preorder `≤` plus modal accessibility
>    `R`) whose propositional fragment bridges to PL's single-relation `IForces`
>    (`Propositional/Semantics/Kripke.lean`), rather than to two-valued `PL.Evaluate`.
> 4. **A proof-theoretic preservation/faithfulness theorem**
>    (`IPL.Derivable φ → IModal.Derivable φ.toIModal` and converse), not merely
>    classical `Tautology ↔ valid`.
>
> This is an XL, multi-logic undertaking gated on a future intuitionistic modal logic; it is out
> of scope for the current classical embeddings. See the `## Limitations` notes in
> `Modal/FromPropositional.lean`, `Temporal/FromPropositional.lean`, and
> `Bimodal/Embedding/PropositionalEmbedding.lean`.

---

## 6. Recommended Implementation Shape (for /plan)

1. Add the §5 note (human-authored) as a new subsection in `ORGANISATION.md` under Logics.
2. (Parity edit) Add the forward-looking `## Limitations` sentence to the Bimodal embedding
   docstring so all three modules agree; cross-reference the ORGANISATION.md subsection from each.
3. No Lean semantics change; `lake build` should be unaffected (doc/comment-only). CI:
   `lake exe lint-style` for text linting on edited `.lean` docstrings; `lake build` to confirm
   docstring edits parse.

**Zero-debt note**: doc-only, no `sorry`, no axioms, no vacuous definitions involved.

---

## Appendix — Verification Method

All claims obtained by `Read` and `grep`/`find` against live source on branch `main`
(2026-06-29). No Lean source modified. No build run (no code change). No lean-lsp goal/hover
calls were required since every claim is a constructor/definition/docstring statement readable in
source. The 415 audit's anchors were spot-checked and confirmed; the one new finding beyond 415
is the Bimodal docstring asymmetry (§1, §3 Option C).
