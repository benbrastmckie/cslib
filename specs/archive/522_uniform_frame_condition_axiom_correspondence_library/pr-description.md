## Title

`refactor(Logics/Modal): unify frame-condition-to-axiom correspondence lemmas`

## Summary

Introduces a small additive library, `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean`,
that factors the five modal-axiom-frame-condition correspondences (T/reflexivity,
4/transitivity, B/symmetry, D/seriality, 5/right-Euclideanness) that were previously proved
identically, inline, in every `Systems/*/Soundness.lean` file that carries the corresponding
frame axiom. All 14 consumer files are rewired to delegate to the shared lemmas via one-line
`exact` calls, eliminating ~23 byte-identical duplicated proof bodies.

This mirrors the existing `Metalogic/Soundness.lean` pattern, which already factors the shared
propositional/K/and-or/dia-duality correspondence lemmas (`Satisfies.implyK_axiom`,
`Satisfies.andI_axiom`, etc.) that every system's soundness proof reuses. The five new lemmas
close the one remaining gap: the frame-condition-dependent modal cases.

## Axiom <-> Frame-Condition <-> Lemma Map

| Axiom | Frame condition | New lemma | Hypothesis form |
|-------|------------------|-----------|------------------|
| T (`□φ → φ`) | Reflexivity | `Satisfies.modalT_axiom` | `h_refl : ∀ w, m.r w w` |
| 4 (`□φ → □□φ`) | Transitivity | `Satisfies.modalFour_axiom` | `h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃` |
| B (`φ → □◇φ`) | Symmetry | `Satisfies.modalB_axiom` | `h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁` |
| D (`□φ → ◇φ`) | Seriality | `Satisfies.modalD_axiom` | `h_serial : Relation.Serial m.r` |
| 5 (`◇φ → □◇φ`) | Right-Euclideanness | `Satisfies.modalFive_axiom` | `h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃` |

## Placement and Interface Design

- New file: `Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean`, imported by
  `Cslib/Logics/Modal/Metalogic/Soundness.lean` (one `public import` line) so all 14 downstream
  `Systems/*/Soundness.lean` consumers receive it transitively. Registered in the `Cslib.lean`
  barrel.
- **Explicit-hypothesis primary form**: each lemma takes the raw `∀`-quantified frame-condition
  hypothesis (or `Relation.Serial`) that the 14 consumers already thread through their public
  `<sys>_axiom_sound` / `<sys>_soundness` signatures. This keeps every consumer's public
  signature and hypothesis names (`h_refl`/`h_trans`/`h_symm`/`h_serial`/`h_eucl`) byte-stable —
  only the modal case *bodies* change, from multi-line inline proofs to one-line `exact` calls.
  No new frame-property predicates or typeclasses were introduced (per research: classical/
  birelational/constructive `ValidFC` shapes are incompatible, so a unifying typeclass across
  those three families is explicitly out of scope for this change).
- Optional instance-backed sibling forms (`[Std.Refl m.r]` etc.) were considered but deferred
  to a follow-up to keep this PR minimal and avoid lint/naming friction — only the five
  explicit-hypothesis primaries are needed by the current 14 consumers.

## Blast Radius

15 files changed, all within `Cslib/Logics/Modal/Metalogic/`:

- 1 new file: `FrameCorrespondence.lean` (5 lemmas)
- 1 import-wiring edit: `Soundness.lean` (+1 import line), plus `Cslib.lean` barrel registration
- 14 consumer edits, modal case bodies only, public signatures unchanged:
  - Single-property: `Systems/{T,B,D,K4,K5}/Soundness.lean`
  - Multi-property: `Systems/{S4,S5,K45,KB5,D4,D5,D45,DB,TB}/Soundness.lean`
    (S5's non-frame-axiom inline symmetry derivation, which derives `h_symm` from `h_eucl` +
    `h_refl`, is preserved untouched — only its `modalT`/`modalFour` cases were rewired)

No `Completeness.lean` adapter in any of the 15 `Systems/*/` directories required a change: none
reference the modal case bodies directly, and the full `lake build` confirms all downstream
adapters still compile against the unchanged public signatures.

## Verification

- Scoped `lake build` green for all 14 refactored modules plus `FrameCorrespondence.lean` and
  `Soundness.lean`.
- Full `lake build` (3243/3243 jobs) green with no regressions.
- `lake exe checkInitImports` clean.
- `lake lint` clean (`-- Linting passed for Cslib.`).
- `lake exe lint-style` clean (no output).
- `lake shake --add-public --keep-implied --keep-prefix`: none of the 15 touched/new files are
  flagged (pre-existing shake findings elsewhere in the repo are out of scope for this change).
- `lake exe mk_all --module`: "No update necessary" (barrel already correct from Phase 1).
- `lake test`: full `CslibTests/` suite green (9236/9236 jobs); no new failures.
- Zero `sorry` introduced: none in any of the 15 touched/new files (repo-wide pre-existing
  `sorry` count is unaffected by this change — this PR touches none of those files).
- Zero new axioms: `lean_verify` reports `axioms: []` for all 5 new lemmas; `axiom` count
  elsewhere in the repo is unchanged by this PR.
- `git diff` on every one of the 14 consumer files confirms only modal case bodies changed —
  `<sys>_axiom_sound` / `<sys>_soundness` signatures and threaded hypothesis names
  (`h_refl`/`h_trans`/`h_symm`/`h_serial`/`h_eucl`) are byte-identical to before.

## Zulip

Per `CONTRIBUTING.md`, a pre-PR heads-up to the modal-logic working group is posted by the
author before this PR is opened for review (covering this axiom<->property map, the placement
decision, the explicit-hypothesis-primary interface choice, and confirmation that completeness-FC
re-expression and birelational/constructive de-duplication are deferred to separate follow-ups).

## AI Tools Used

This PR was prepared with the assistance of Claude Code (Anthropic). The AI tool was used for:
- Drafting and extracting files from a development branch to create a clean PR branch
- Running CI verification commands
- Drafting this PR description

All Lean code was written by the author (Benjamin Brast-McKie) and verified to compile cleanly
on the PR branch.
