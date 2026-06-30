# Research Report: Audit of "Unowned" Foundational Sorries (Task 431)

**Date**: 2026-06-30
**Agent**: cslib-research-agent
**Task type**: cslib (audit/documentation)
**Source trigger**: `specs/reviews/review-2026-06-30.md`, Medium issue 2 ("A handful of `sorry`s with no obvious owning task")

## Executive Summary

**Headline finding: There are ZERO live `sorry` tactics in any of the six audited files.**
All seven "sorry" occurrences flagged by the 2026-06-30 review are **textual matches inside
docstrings and comments** — none is a real proof obligation. The review's census (121 `sorry`
across 27 files) was a raw text count that swept up phrases such as "sorry-free", "avoids
sorry", "no new axiom or `sorry` was introduced", "removing the `sorry`", and one commented-out
`--   sorry` inside an entirely commented-out `-- TODO` block.

Consequently:
- **None** of the seven occurrences is genuine proof debt.
- **None** needs to be (or can be) "owned" by tasks 36/37/215/275/317/425-427 — those tasks own
  *real* sorries that live in different files (Bimodal/Tableau/Temporal clusters).
- The two declarations the review singled out as risk-bearing (CanAlgComplete feeds
  completeness; GNBA feeds automata `isRegular`) were **axiom-verified clean**:
  `lean_verify` reports `axioms: []`, `warnings: []` for both — no `sorryAx` leak.

**Disposition**: No tracking task is warranted. Recommend an optional one-line documentation
cleanup (purely cosmetic) so future raw-text census passes do not re-flag these files. This task
itself can be closed as "audit complete — no debt found".

## Method

1. Precise token scan (`grep -nE '(^|[^a-zA-Z])sorry([^a-zA-Z-]|$)'`) of each file, then manual
   inspection of every hit's surrounding lines to classify comment/docstring vs. live tactic.
2. Repo-wide live-sorry scan to locate where the *real* tracked debt lives (Bimodal/Tableau).
3. Read `specs/state.json` descriptions for tasks 36/37/215/275/317/425/426/427 to build the
   ownership map.
4. Authoritative axiom check via `lean_verify` on the two flagged risk-bearing declarations.

## Per-File / Per-Sorry Findings

### 1. `Cslib/Foundations/Order/HilbertAlgebra.lean`
- **Location**: line 51 — module **docstring**, "Design Notes" section. No declaration.
- **Text**: "Including `himp_self` as a field avoids sorry and matches the spirit of the
  axiomatic presentation in Rasiowa (1974)."
- **What it is**: A design rationale explaining the file deliberately *avoids* sorry by taking
  `himp_self` as an axiom field. Not a proof obligation.
- **Owned by a blocked task?** No (not proof debt).
- **Verdict**: UNOWNED — **and not a sorry**. No-op / closeable.

### 2. `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`
- **Location**: line 59 — module **docstring**. No declaration.
- **Text**: "No new axiom or `sorry` was introduced; the generalization is conservative."
- **What it is**: A note asserting the seam generalization introduced no debt.
- **Owned by a blocked task?** No (not proof debt).
- **Verdict**: UNOWNED — **and not a sorry**. No-op / closeable.

### 3. `Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean`
- **Location**: line 112 — inside a fully **commented-out** `-- TODO` block (lines 105-112)
  sketching a future `Term.subst_comm` theorem. The line reads `--   sorry`.
- **What it is**: A commented-out proof stub for a theorem that does not exist in the file. It
  cannot elaborate and cannot produce `sorryAx`.
- **Owned by a blocked task?** No. (It is a loose `TODO` for a substitution-commutativity lemma;
  not tied to any of 36/37/215/275/317/425-427.)
- **Verdict**: UNOWNED — **and not a live sorry**. Optional cleanup: either delete the
  commented stub or replace the bare `--   sorry` with a clearer `-- (proof TODO)` so census
  passes stop matching it. No tracking task required.

### 4. `Cslib/Logics/Propositional/Semantics/Algebra/CanAlgComplete.lean`
- **Location**: line 41 — module **docstring**, "Main Results" bullet. No declaration.
- **Text**: "...the three fragment instances, each built entirely by reuse of existing
  sorry-free theorems."
- **What it is**: A claim that the file is sorry-free by reuse. Verified: `lean_verify` on
  `Cslib.Logic.PL.canAlgComplete_iff` returns `axioms: []`, `warnings: []` — **no `sorryAx`**.
- **Owned by a blocked task?** No (not proof debt). Review's "feeds completeness" concern is
  unfounded — the completeness path through this file is axiom-clean.
- **Verdict**: UNOWNED — **and not a sorry; verified clean**. No-op / closeable.

### 5. `Cslib/Logics/LTL/Semantics/GNBA.lean`
- **Location**: line 37 — module **docstring**, phase roadmap. No declaration.
- **Text**: "Integration (Phase 5): Proof of `Formula.isRegular_untl` removing the `sorry` from
  `Formula.isRegular`."
- **What it is**: Historical narrative describing the (already-completed) integration plan. The
  referenced sorry lived in `Formula.isRegular` (in `OmegaRegular.lean`, **not** this file) and
  **has already been removed**: `Formula.isRegular_untl` (OmegaRegular.lean:309) is now proved
  by delegation to `Formula.isRegular'`, and `lean_verify` on
  `Cslib.Logic.LTL.Formula.isRegular` returns `axioms: []`, `warnings: []` — **no `sorryAx`**.
- **Owned by a blocked task?** No (not proof debt). Review's "feeds automata" concern is
  unfounded — the automata `isRegular` result is axiom-clean.
- **Verdict**: UNOWNED — **and not a sorry; verified clean**. No-op / closeable. (Optional: the
  docstring could be reworded from "removing the `sorry`" to past tense / drop the word to avoid
  future census false positives.)

### 6. `Cslib/Logics/Propositional/NaturalDeduction/Normalization/Termination.lean` (2 occurrences)
- **Location A**: line 725 — **docstring** of the termination support block: "...the head-bound's
  entire dependency cone — neutral implications `ax/ass/andE1/andE2/impE` — is sorry-free."
- **Location B**: line 783 — **comment** above the mutual block: "...raise the heartbeat limit so
  the (sorry-free) termination proof elaborates within budget."
- **What they are**: Both explicitly assert the proof is *sorry-free*. Neither is a tactic.
- **Owned by a blocked task?** No (not proof debt).
- **Verdict**: UNOWNED — **and neither is a sorry**. No-op / closeable.

## Ownership Map (requested cross-reference)

| File | Line | Kind | Owning blocked task? | Verdict |
|------|------|------|----------------------|---------|
| HilbertAlgebra.lean | 51 | docstring | none | UNOWNED, not a sorry |
| GenericMCS.lean | 59 | docstring | none | UNOWNED, not a sorry |
| LambdaCalculus/.../Basic.lean | 112 | commented-out TODO stub | none | UNOWNED, not a live sorry |
| CanAlgComplete.lean | 41 | docstring ("sorry-free") | none | UNOWNED, verified clean |
| GNBA.lean | 37 | docstring (historical) | none | UNOWNED, verified clean |
| Normalization/Termination.lean | 725 | docstring ("sorry-free") | none | UNOWNED, not a sorry |
| Normalization/Termination.lean | 783 | comment ("sorry-free") | none | UNOWNED, not a sorry |

**Where the real tracked debt actually lives** (for contrast, confirming none of the above
belongs to these tasks):
- **Task 36 / 37 / 215**: live sorries in `Cslib/Logics/Bimodal/Metalogic/` —
  `BXCanonical/Chronicle/ChronicleToCountermodel.lean`, `Bundle/SuccRelation.lean`,
  `Bundle/UntilSinceCoherence.lean`, `BXCanonical/Frame.lean` (each carries
  `set_option warn.sorry false` + `-- sorry: blocked on task 36/37`).
- **Task 275**: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean`.
- **Task 317**: `Cslib/Logics/Propositional/Tableau/{Intuitionistic,Minimal,Classical}/` and
  `Metalogic/MinDecidability.lean` (the 317-owned tableau truth-lemma sorries).
- **Tasks 425/426/427**: `Cslib/Logics/Temporal/Tableau/Completeness.lean` (line ~433).

None of these paths overlaps the six audited files.

## Recommendations (disposition per the task brief)

1. **Close task 431 as "audit complete — no genuine debt found."** The six files contain no
   live sorries; the review's Medium issue 2 was a false positive of a raw-text census.
2. **No new tracking task** is warranted (the review's contingency "spawn a small tracking task
   if any are genuinely unowned" is not triggered — there is nothing to track).
3. **Optional, cosmetic only** (a single trivial cleanup task at most, low priority): reduce
   future census noise by editing the two most census-prone spots so the literal token `sorry`
   no longer appears as a standalone word:
   - `Basic.lean:105-112`: delete the commented-out `Term.subst_comm` TODO stub (or convert the
     `--   sorry` line to `--   (proof TODO)`).
   - `GNBA.lean:37`: reword "removing the `sorry` from `Formula.isRegular`" to past tense, e.g.
     "discharging the former proof gap in `Formula.isRegular`".
   The remaining four ("sorry-free" / "avoids sorry" / "no `sorry` was introduced") are accurate
   self-documentation and are best left as-is; a census that counts these is the thing to fix,
   not the docstrings.
4. **Census-tool note for future reviews**: the `sorry` census should exclude comment/docstring
   lines (e.g. match only `\bsorry\b` not preceded by `--` and not part of `sorry-free`/`warn.sorry`),
   otherwise it will keep over-reporting. This is the root cause of Medium issue 2.

## Verification Evidence

- `grep` token scan: only comment/docstring hits in all six files (no bare `sorry` tactic).
- `lean_verify Cslib.Logic.LTL.Formula.isRegular` → `{"axioms":[],"warnings":[]}`.
- `lean_verify Cslib.Logic.PL.canAlgComplete_iff` → `{"axioms":[],"warnings":[]}`.
- `Formula.isRegular_untl` (OmegaRegular.lean:309) is a real term-mode proof delegating to
  `Formula.isRegular'` — the GNBA-docstring "sorry" was already eliminated.
