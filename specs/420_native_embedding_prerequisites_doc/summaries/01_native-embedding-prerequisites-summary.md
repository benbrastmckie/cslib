# Implementation Summary: Task #420

- **Task**: 420 - Doc: record native intuitionistic-embedding prerequisites
- **Status**: [IMPLEMENTING -> PARTIAL]
- **Completed**: 2026-06-29
- **Phases Completed**: 2 of 3 (Phase 1 COMPLETED, Phase 2 SKIPPED per scope, Phase 3 COMPLETED)

## What Was Done

### Phase 1 (COMPLETED): ORGANISATION.md prerequisites subsection

Added a new subsection `### Propositional Embeddings and the Classical-Scope Boundary` to
`ORGANISATION.md`, placed immediately after the Bimodal Logic code block and before
`### Other Logics`. The subsection:

- Explains that the three embedding modules map `{atom, bot, imp}` directly and encode
  `{and, or}` via Łukasiewicz definitions, certifying only the CPL fragment.
- Lists all four prerequisites for a future native, intuitionistic-faithful embedding:
  1. Native `and`/`or` constructors on the target syntax (with anchor `Propositional/Defs.lean:89,91`)
  2. `[IsIntuitionistic]`-gated modal/temporal proof system (anchors `NaturalDeduction/Basic.lean:182`, `SequentCalculus/LJ/Basic.lean:100`)
  3. Birelational target semantics (preorder `≤` + accessibility `R`) distinct from PL `IForces` single-relation Kripke (anchor `Propositional/Semantics/Kripke.lean:58-130`), with explicit `≤` vs. `R` distinction
  4. Proof-theoretic preservation `IPL.Derivable φ → IModal.Derivable φ.toIModal` beyond classical-semantic `PL.Tautology φ ↔ valid φ.toModal` (anchor `Modal/FromPropositional.lean:106,162`)
- Points to the `## Limitations` sections in the three embedding modules.

### Phase 2 (SKIPPED): Bimodal docstring parity + cross-references

*(deviation: skipped -- per orchestrator scope note, task 418 owns
`Bimodal/Embedding/PropositionalEmbedding.lean` concurrently. The Bimodal parity edit and
cross-reference additions to all three embedding modules are deferred to / folded into
task 418's restructure. No .lean files were modified this cycle.)*

### Phase 3 (COMPLETED): Verification

- `lake exe lint-style`: exit 0, no output (clean).
- `git diff`: shows only `ORGANISATION.md` changed; pure Markdown additions, zero Lean code,
  zero sorry, zero axioms.
- Baseline sorry count: 90 (unchanged). Baseline axiom count: 17 (unchanged).
- No Lean files were modified, so no `lake build` regression is possible; the build tree is
  identical to pre-edit state.

## Plan Deviations

| Phase | Deviation | Reason |
|-------|-----------|--------|
| Phase 2 | Skipped entirely | Orchestrator scope note: task 418 restructures `Bimodal/Embedding/PropositionalEmbedding.lean` concurrently; all Phase 2 edits (Bimodal parity + 3× cross-ref additions) deferred to task 418 |

## AI Policy Note

The ORGANISATION.md subsection prose was authored as part of this implementation and is an
in-repo design note (permitted under CSLib/Mathlib AI policy). Any prose intended for
upstream surfaces (PR descriptions, Zulip messages) must be human-authored separately. The
report §5 scaffold (in `reports/01_native-embedding-prerequisites.md`) remains marked
`[SCAFFOLD — human-author before committing]` and was not used verbatim here.

## Artifacts

- `ORGANISATION.md` — new subsection added (~36 lines)
- `plans/01_native-embedding-prerequisites-doc.md` — plan updated with phase markers
- `summaries/01_native-embedding-prerequisites-summary.md` — this file
