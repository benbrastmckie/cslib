# PR #662 Slice — CONTRIBUTING.md Compliance Audit

**Task:** 499
**Parent:** 498 (modal foundational semantic layer for #662); coordination context 476
**Date:** 2026-07-13
**Type:** cslib (documentation / docstring compliance; no proof changes)
**Status:** research complete — findings below are ready to plan/implement from.

## 1. Scope

Audit the code that will become **PR #662 as the native-primitive foundational semantic layer**
(version B) against `CONTRIBUTING.md` and the standards it references (Mathlib style, `Cslib.Init`
imports, notation policy, reuse, documentation, references). The reviewed code is the staged slice:

- `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-662-slice/Basic.lean` (296 LOC)
- `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-662-slice/Denotation.lean` (90 LOC)

The slice was extracted faithfully from the live `Cslib/Logics/Modal/{Basic,Denotation}.lean` on
branch `task-441-native-refactor`, so several findings (esp. §3.1) also exist in the live source.

**Fixes are documentation-only** (docstrings / header). They must not alter any definition or proof.
CI must still pass after the edits (`lake build`, `checkInitImports`, `lake lint`, `lake exe
lint-style`, `lake test`, `lake shake`).

## 2. Already compliant (no action)

- Copyright header present on both files (Apache 2.0, correct format).
- Module docstrings present; every `def`/`theorem`/`lemma`/`structure` field is documented (`docBlame` satisfied).
- `Cslib.Init`: `Basic.lean` imports it directly; `Denotation.lean` imports it transitively via `Basic` — matches the CI-passing #607-base `Denotation.lean` pattern.
- Namespace `Cslib.Logic.Modal` (singular) matches the established convention (dir `Logics`, namespace `Logic`) on both #607's base and task-441.
- Reuse: instantiates `ModalConnectives`, `HasAnd`/`HasOr`/`HasDia`, `HasInferenceSystem`, `PropositionalConnectives` (strong "Reuse" compliance).
- Notation: all `@[inherit_doc] scoped` and typeclass-backed (Notation policy).
- BibKeys `[Blackburn2001]` and `[ChagrovZakharyaschev1997]` both exist in `references.bib`.
- `push Not` is a valid, widely-used CSLib tactic; no `sorry`, no vacuous definitions.
- PR title format and "AI Tools Used" section are handled in the PR description draft.

## 3. Findings to fix

### 3.1 [MUST FIX] Internal task-tracker numbers in published docstrings

`Basic.lean` references internal project task numbers, which do not belong in CSLib source:

| Location | Text |
|----------|------|
| `Basic.lean:34` | "…however, **task 441** makes `diamond` a native constructor…" |
| `Basic.lean:113` | "Delegates to the canonical `PropositionalConnectives.neg` default (**task 340**)." |
| `Basic.lean:119` | "Delegates to the canonical `PropositionalConnectives.top` default (**task 340**)." |
| `Basic.lean:272` | "Since `diamond` is a native constructor (**task 441**), this is no longer a definitional unfolding…" |

**Fix:** reword to state the design rationale without task numbers (e.g. "diamond is a native
constructor" / "delegates to the canonical `PropositionalConnectives.neg` default"). **Note:** the
same strings exist in the live `Cslib/Logics/Modal/Basic.lean` on `task-441-native-refactor`; fix
them there too so re-extraction does not reintroduce them.

### 3.2 [SHOULD FIX] Docstring cross-references to machinery not in this PR

The `Basic.lean` module docstring points at layers the slice deliberately excludes and that do not
exist on #607's base — so they dangle in a self-contained #662:

- **`Basic.lean:41–44`** — `AxiomDiaDualityFwd`/`AxiomDiaDualityBack` in `Foundations/Logic/Axioms.lean`
  and `ProofSystem/Instances/*.lean` (the proof-system layer; frame axioms deferred to the later
  "systems" PR). Absent from the slice and from `ddc2c9b8` (#607 head).
- **`Basic.lean:46–50`** — the `PL.Proposition.toModal` / `PL.Proposition.embed` / "in
  `FromPropositional`" paragraph. Those symbols live in
  `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` (task-441 Bimodal work), not in the
  slice or base. Also there is **no module named `FromPropositional`** — the name is inaccurate.

**Fix:** trim the module docstring to what the PR actually delivers (semantics layer). Keep the
literature-backed design rationale (diamond primitivity, IK/CK reuse) but drop the forward
references to the proof-system and Bimodal-embedding layers, or gate them behind "(in later PRs)".

**Scope nuance:** on the task-441 branch these references are *valid* (those files exist there), so
this trim is **slice-specific** — do not delete the cross-refs from the live task-441 file; only
scrub them from the standalone #662 slice.

### 3.3 [MINOR] `## References` list incomplete

`[ChagrovZakharyaschev1997]` is cited inline (`Basic.lean:37`) but the `## References` section
(`Basic.lean:52–56`) lists only `[Blackburn2001]`. CONTRIBUTING requires referencing published
resources. **Fix:** add a `[ChagrovZakharyaschev1997]` entry to the References section.

### 3.4 [CONFIRM WITH MAINTAINER — not an auto-fix] Copyright-holder line

The slice adds **Benjamin Brast-McKie** to the `Copyright (c) 2026 …` holder line of Fabrizio's
file (`Basic.lean`; #607 base is `Copyright (c) 2026 Fabrizio Montesi`). Adding to the `Authors:`
line is standard for a substantial contribution; adding to the **copyright-holder** line is a
maintainer preference. Since #662 stacks on #607, confirm with Fabrizio before finalizing. The
`Authors:` addition is fine. **Do not auto-change without maintainer input.**

### 3.5 [OPTIONAL] "Lukasiewicz" diacritic

`Basic.lean:30,36` write "Lukasiewicz"; proper is "Łukasiewicz". Codebase is ~50/50 (22 with, 20
without), so this is a consistency preference, not a violation. Optional.

## 4. Deliverables / acceptance criteria

1. `Basic.lean` docstrings free of internal task numbers (§3.1) — in the slice **and** the live
   task-441 source.
2. `Basic.lean` module docstring trimmed of dangling proof-system/Bimodal cross-references (§3.2) —
   slice only.
3. `## References` includes `[ChagrovZakharyaschev1997]` (§3.3).
4. Copyright-holder decision recorded (§3.4) — pending Fabrizio; no code change unless he agrees.
5. Optional: "Łukasiewicz" diacritic (§3.5).
6. All CI green after edits; zero proof/definition changes (`git diff` touches only comments/header).

## 5. Files affected

- `specs/498_modal_foundational_semantic_layer_662/artifacts/pr-662-slice/Basic.lean` (§3.1–3.5)
- `Cslib/Logics/Modal/Basic.lean` on `task-441-native-refactor` (§3.1 only — task-number scrub)
- (No changes needed to `Denotation.lean`: its docstrings are clean.)
