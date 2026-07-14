# Implementation Summary: Task #501 — CK Constructive Modal Extensions CT / CS4 / CS5

- **Task**: 501 — CK constructive modal extensions CT / CS4 / CS5
- **Plan**: `specs/501_CK_constructive_modal_extensions_CT_CS4_CS5/plans/01_ct-cs4-cs5-extensions.md`
- **Status**: PARTIAL (6 of 8 phases fully complete; 2 phases — CS4 and CS5 completeness —
  [BLOCKED] with a mechanically-verified, fully documented obstruction)
- **Session**: sess_1784044271_09e821_501

## Outcome Overview

| System | Axioms + Soundness | Completeness |
|--------|--------------------|--------------|
| `CT`   | Complete | Complete (`ct_completeness`, `ct_consistent`, `ct_soundness_completeness`) |
| `CS4`  | Complete (`cs4_axiom_sound`/`cs4_soundness`/`cs4_soundness_derivable`) | **Blocked** (Phase 5) |
| `CS5`  | Complete (`cs5_axiom_sound`/`cs5_soundness`/`cs5_soundness_derivable`, via `B`) | **Blocked** (Phase 7, inherits Phase 5's obstruction) |

Four new files under `Cslib/Logics/Modal/Metalogic/Constructive/`:
`CKExtension.lean`, `CT.lean`, `CS4.lean`, `CS5.lean`, all wired into `Cslib.lean`. Full CSLib CI
pipeline (`lake build`, `checkInitImports`, `lake lint`, `lint-style`, `shake`, `mk_all`,
`lake test`) is green. Zero `sorry`, zero new axioms, zero vacuous placeholders anywhere.

## Phases Completed

1. **`CKExtension.lean` scaffold** — `CKValidFC` (FC-parametrized segment validity, generalizing
   `CKValid`), `ctFC`/`cs4FC`/`cs5FC` (≤-composed frame-condition predicates), the parametric
   `ckvalidFC_completeness` (abstracted over an arbitrary canonical `World` type so it can be
   instantiated over a world subtype), and `axiom_mem_head`.
2. **`CT.lean` axioms + soundness** — `CTModalAxiom` (11 bare-CK constructors + `tBox`/`tDia`),
   `ct_axiom_sound`/`ct_soundness`/`ct_soundness_derivable` over `CKValidFC ctFC`.
3. **`CT.lean` world subtype + completeness** — `CTSegment` (segments satisfying
   `seg.head ∈ seg.tail`, the T-invariant), invariant discharge for `CKSegment.ofHead` and
   `diamRefutingSegment`, the truth lemma ported to the subtype (`ct_truth_lemma`),
   `ct_completeness`/`ct_consistent`/`ct_soundness_completeness`.
4. **`CS4.lean` axioms + soundness** — `CS4ModalAxiom` (`CTModalAxiom`'s constructors + `fourBox`/
   `fourDia`), soundness over `CKValidFC cs4FC` (`fourBox` via ≤-composed transitivity, `fourDia`
   via the plain specialization).
6. **`CS5.lean` axioms + soundness** — `CS5ModalAxiom` (`CS4ModalAxiom`'s constructors + `bBox`/
   `bDia`, via **B/symmetry, not euclidean-5**), soundness over `CKValidFC cs5FC` (`bBox` via
   ≤-composed symmetry, `bDia` via the plain specialization).
8. **Barrel wiring + full CI** — all four files wired into `Cslib.lean`; full CI pipeline green
   (see below).

## Phases Blocked

**Phase 5 (CS4 transitivity invariant + completeness)** and **Phase 7 (CS5 symmetry invariant +
completeness)** are marked `[BLOCKED]` in the plan file, each with a full Blocker entry (what
failed, what was tried, why it's stuck, what is needed). Summary of the shared obstruction:

- `cs4FC`/`cs5FC` are **blanket** hypotheses: `CKValidFC`/`ckvalidFC_completeness` require the
  frame condition to hold for the relation on the *entire* chosen world type, not per-world.
- The truth lemma's diamond-backward case structurally requires a **restricted-tail** witness
  segment (`diamRefutingSegment`, reused from task 493) whose tail excludes a specific formula
  `A`. An unrestricted/maximal-tail witness always contains the exploding theory `Set.univ` in
  its tail and therefore trivially forces every diamond, which would make the canonical model
  degenerate and break completeness for diamond-containing formulas — so the restricted witness
  is unavoidable.
- The natural per-segment invariant that *would* make ≤-composed transitivity (and, by extension,
  symmetry) hold globally — "the segment's tail contains every quasi-prime superset of
  `boxInv(head)`" (i.e. the segment is `.ofHead`-shaped/maximal) — is **mechanically proven**
  (standalone probe files, `lake env lean`, zero errors) to (a) suffice for transitivity when it
  holds, and (b) be **violated** by `diamRefutingSegment` for every choice of source segment and
  excluded formula (`Set.univ` is always a counterexample). The witness's `A`-exclusion is a
  one-step property that does not propagate through further ≤-composed-transitive/symmetric
  successors.
- These two requirements are in direct tension: whatever makes the diamond-refutation witness
  admissible into the world type breaks the transitivity/symmetry invariant, and whatever
  restores the invariant breaks diamond-refutation. Resolving this needs either (a) a
  *hereditary* diamond-refuting theory construction that propagates the exclusion through the
  full ≤-composed-transitive closure of the restricted tail (new Lindenbaum-style machinery
  beyond `SegmentLindenbaum.lean`'s `dia_refuting_theory`), or (b) a different canonical-model
  technique for `S4`/`S5`-style fallible-world segment completeness (e.g. filtration, or a
  generated/unraveled countermodel) not present in the task 493/494 asset base. This is a
  research-scale extension, not a single-lemma fix — flagged as a follow-up research item.

No `sorry`, `def X := True`, or other vacuous placeholder was introduced anywhere. `CS4.lean` and
`CS5.lean` contain only their axiom inductives and soundness theorems; no partial/dangling
`CS4Segment`/`CS5Segment`/completeness declarations were added.

## Plan Deviations

- **Task 8.4** (barrel wiring conditional on Phase 7 status): altered from the plan's anticipated
  shape. The plan anticipated Phase 5 (CS4 completeness) succeeding and only Phase 7 (CS5
  completeness) carrying risk of being blocked. In fact Phase 5 itself hit the same underlying
  obstruction and was blocked first; Phase 7 was documented as blocked-by-inheritance (the same
  root cause, confirmed to also apply to the symmetry clause) rather than being separately
  re-attempted with fresh construction effort, since `cs5FC` strictly implies `cs4FC`'s
  transitivity conjunct and therefore cannot be satisfied by any world type that already fails
  to satisfy `cs4FC`.
- **CS4.lean / CS5.lean import minimization** (Phase 8, Task 8.3): the plan's stated import chain
  `CT ← CS4 ← CS5` is conceptually accurate (each system's axiom set literally repeats the
  previous system's constructors) but not literally required at the Lean import level, since
  `CS4ModalAxiom`/`CS5ModalAxiom` copy their predecessor's constructors verbatim rather than
  referencing them as terms. `lake shake` correctly flagged this; `CS4.lean` and `CS5.lean` now
  import `CKExtension` directly rather than `CT`/`CS4` respectively. `Cslib.lean`'s barrel still
  wires all four files independently, so nothing is lost for downstream consumers importing the
  whole library.

## CI Verification Results

All steps run and green (full library, not just the four new files):

| Step | Result |
|------|--------|
| `lake exe cache get` | Skipped (cache already warm for this branch) |
| `lake build` (whole library) | ✅ Green — `Build completed successfully (3211 jobs)` |
| `lake exe checkInitImports` | ✅ Green (exit 0) |
| `lake lint` (environment linters) | ✅ Green for all 4 new files (1 pre-existing, unrelated warning in `PrimeExclusion.lean`); fixed one `unusedArguments` warning on `ctFC` via `@[nolint unusedArguments]` |
| `lake exe lint-style` | ✅ Green (no output) |
| `lake shake --add-public --keep-implied --keep-prefix` | ✅ Green for all 4 new files beyond the library-wide `import Cslib.Init` false-positive (present on every pre-existing file too, including task 493's own `Constructive/` files; ignored per established precedent since `checkInitImports` mandates the explicit import) |
| `lake exe mk_all --module` | ✅ "No update necessary" — barrel already correctly wired |
| `lake test` (CslibTests) | ✅ Green (exit 0) |

**Zero-debt checks**:
- `sorry` count in the 4 new files: **0**
- Vacuous-definition pattern matches: **0**
- New `axiom` declarations: **0** (2 false-positive grep matches were docstring prose containing
  the word "axiom", not `axiom` declarations)
- `lean_verify` on `ct_soundness_completeness`: only the 3 standard foundational axioms
  (`propext`, `Classical.choice`, `Quot.sound`)
- `lean_verify` on `cs4_soundness_derivable`/`cs5_soundness_derivable`: zero axioms

## Artifacts

- `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean` (new, 130 lines)
- `Cslib/Logics/Modal/Metalogic/Constructive/CT.lean` (new, ~430 lines)
- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` (new, ~226 lines)
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` (new, ~262 lines)
- `Cslib.lean` — already wired (no diff needed; `mk_all` confirmed)
- `specs/501_CK_constructive_modal_extensions_CT_CS4_CS5/plans/01_ct-cs4-cs5-extensions.md` — all
  8 phase status markers updated; Phase 5 and Phase 7 carry full Blocker entries

## Follow-Up

A focused follow-up task should investigate either (a) a hereditary/propagating diamond-refuting
theory construction for the segment model, or (b) an alternative canonical-model technique (e.g.
filtration) for `S4`/`S5`-style fallible-world completeness, to unblock `cs4_completeness` and
`cs5_completeness`. The soundness direction and all axiom/frame-condition infrastructure for both
systems is already in place and does not need to be redone.

## Git Commits

- `2fa4610c` — task 501 phase 1: CKExtension.lean scaffold
- `7d5a135c` — task 501 phase 2-3: CT.lean axioms, soundness, world subtype, completeness
- `6cac8b19` — task 501 phase 4: CS4.lean axioms and soundness
- `07769e2d` — task 501 phase 5-7: CS5.lean axioms+soundness; block CS4/CS5 completeness
- `f36316d1` — task 501 phase 8: fix unusedArguments lint warning in ctFC
- `21720ca3` — task 501 phase 8: minimize CS4/CS5 imports per lake shake
- `c7bdf9f1` — task 501 phase 8: barrel wiring + full CI pipeline green
