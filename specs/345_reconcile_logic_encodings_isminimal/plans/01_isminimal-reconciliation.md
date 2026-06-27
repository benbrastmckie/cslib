# Implementation Plan: Task #345 — Reconcile Logic Encodings (`IsMinimal`)

- **Task**: 345 - Reconcile logic encodings: add `IsMinimal` inclusion view + `MinimalAxioms` bridge
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/345_reconcile_logic_encodings_isminimal/reports/01_team-research.md
- **Artifacts**: plans/01_isminimal-reconciliation.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add the missing "strength by inclusion" view that reconciles the two encodings of minimal
propositional strength on the Hilbert substrate: the existing 8-field `MinimalAxioms` typeclass
and a set-inclusion characterization `minimal ⊆ T`. The single hard constraint from research is
the **meaning of `minimal`**: it must be the 8-schema Hilbert set
`minimal := AxiomTheory (@MinPropAxiom Atom) = {φ | MinPropAxiom φ}`, **not** `MPL` (which is `∅`
and would make the bridge `MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms` provably FALSE).
The deliverable is additive and zero-debt (no `sorry`, no new `axiom`): one load-bearing lemma
`MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ` drives both bridge directions via the
definitional `mem_axiomTheory` (`@[simp] Iff.rfl`) and `Set.setOf_subset_setOf`. Definition of
done: `minimal`, `IsMinimal`, `isMinimalIff`, and the `MinimalAxioms` bridge land in
`NaturalDeduction/Equivalence.lean` and the full CSLib CI pipeline is green.

### Research Integration

Integrated from `reports/01_team-research.md` (team research, 4 teammates, unanimous on the core
finding):

- **Pin the meaning first**: `minimal := AxiomTheory (@MinPropAxiom Atom)` — the 8 Hilbert schema
  instances (K, S, andI, andE1, andE2, orI1, orI2, orE). Docstring loudly that `minimal ≠ MPL`
  (`MPL = ∅`) and that `IsMinimal` is a Hilbert-substrate notion ("carries the 8 connective axiom
  schemas"), distinct from ND minimal logic. This neutralizes Teammate D's vacuity warning.
- **Placement = Option B (downstream, `Equivalence.lean`)**: the import graph blocks `Defs.lean`
  (it cannot see `MinPropAxiom`/`AxiomTheory` without a cycle). `Equivalence.lean` has both
  visible and already documents (`:52-54`) that `AxiomTheory ≠ MPL/IPL/CPL`. Option A (`Defs.lean`
  + a `mem_minimal_iff_minPropAxiom` connecting lemma) is the **fallback only** if a reviewer
  insists on triad symmetry with `IsIntuitionistic`/`IsClassical` (see Open Decision below).
- **Single core lemma** `(★) MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ`, proved by
  `constructor` + `cases`/`constructor`, cloning `MinPropAxiom.toIntPropAxiom`
  (`ProofSystem/Axioms.lean:155-165`). Both bridges collapse to `(★)` because `Theory = Set =`
  predicate (`Defs.lean:142`) and `mem_axiomTheory` is `Iff.rfl`.
- **`grind` caution (F5)**: siblings `isIntuitionisticIff`/`isClassicalIff` one-shot with `by grind`
  because each is a *single* schema; the 8-schema `MinimalAxioms` may defeat bare `grind`. Try
  `grind` first, fall back to the explicit `(★)` + `setOf_subset_setOf` chain.
- **Scope (F7)**: additive only — `MinimalAxioms` stays a class; do **not** touch its ~150
  downstream `[MinimalAxioms Axioms]` consumer sites. Do **not** build a generic `IsStrength S T`
  class (D's resolution-keying argument: `S` is not determined by the goal head). Scope tableau
  (task 316) out.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in delegation context; no ROADMAP.md consulted. Research notes
strategic alignment with the fragment-lattice tasks (352/353/354, 310/311/312/322) whose `toX`
subsumption maps are the inclusion idiom in disguise, and with `[MinimalAxioms Axioms]` consumers
(341, 344); this is context only and drives no phase here.

## Goals & Non-Goals

**Goals**:
- Define `minimal := AxiomTheory (@MinPropAxiom Atom)` with a docstring that loudly states
  `minimal ≠ MPL` and frames `IsMinimal` as a Hilbert-substrate notion.
- Provide the `IsMinimal` inclusion view reusing the existing `MinimalAxioms` class (maximally DRY).
- Prove the load-bearing lemma `(★) MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ` (no `sorry`).
- Derive both bridges from `(★)`:
  - (1) `IsMinimal T ↔ minimal ⊆ T`
  - (2) `MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms`
- Optionally add the thin monotone-propagation wrapper `instIsMinimalExtention` (`Set.Subset.trans`).
- Pass the full CSLib CI pipeline (build, checkInitImports, lint-style, lint, shake, test).

**Non-Goals**:
- Re-encoding the 8 schemas inline in `Defs.lean` (rejected; Option B avoids duplication).
- Replacing the `MinimalAxioms` typeclass with an inclusion predicate (additive only; ~150 sites
  must stay intact).
- Building a generic `IsStrength S T` typeclass (instance resolution cannot key on `S`).
- Touching the natural-deduction `MPL`/`IPL`/`CPL` definitions or `IsIntuitionistic`/`IsClassical`.
- Any work on tableau (task 316) or `Foundations/Logic/` `MinimalHilbert` consolidation.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Implementer reaches for `minimal = MPL` (= ∅), making bridge (2) provably false | H | M | Hard constraint pinned in Phase 1; loud docstring; verify bridge (2) holds for a non-trivial `Axioms` mentally before building |
| Bare `by grind` fails on the 8-schema iff (F5) | M | M | Try `grind` first (parity with siblings); on failure use explicit `(★)` + `Set.setOf_subset_setOf`/`Set.setOf_subset` chain (search-free, all 8 cases mechanical) |
| New `@[scoped grind]`/`@[scoped grind →]` attribute perturbs unrelated `grind` proofs in the subtree (F6) | M | L | Build the whole `Logics/Propositional` subtree, not just the one file; run full `lake build` before declaring done |
| CI lint failures: missing docstrings, snake_case names, `def` for Prop-valued decls, `unusedSectionVars` | M | M | camelCase (`isMinimalIff`); docstring every decl; `theorem`/`lemma` for Prop-valued, `def`/`abbrev` for `minimal`; `omit [DecidableEq Atom] in` where the var is unused |
| Carrier/type mismatch on `minimal ⊆ AxiomTheory Axioms` | L | L | Refuted in research: `AxiomTheory : (Proposition→Prop) → Theory Atom`; `⊆` is well-typed `Set.Subset`. Confirm with `lean_goal` if needed |
| Scope creep into the ~150 `MinimalAxioms` consumers | M | L | Additive-only rule; do not edit any file other than `Equivalence.lean` (and `Defs.lean` only under the Option A fallback) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel (note: phases 1-4 edit the same file, so
in practice they are applied sequentially; the wave map reflects logical dependency, not file
isolation).

### Phase 1: Pin `minimal` and define the `IsMinimal` view [NOT STARTED]

- **Goal:** Add the `minimal` set and the `IsMinimal` inclusion notion to `Equivalence.lean`,
  with docstrings that pin the meaning (`minimal ≠ MPL`) and frame `IsMinimal` as a
  Hilbert-substrate notion.
- **Tasks:**
  - [ ] Locate the insertion point in
    `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` after the `MinimalAxioms`
    instances (~line 165), inside `namespace Cslib.Logic.PL` under the `variable {Atom} [DecidableEq Atom]` section.
  - [ ] Add `abbrev minimal {Atom : Type*} : Theory Atom := AxiomTheory (@MinPropAxiom Atom)`
    (or `def`; use `abbrev` for defeq transparency to `{φ | MinPropAxiom φ}`). Docstring MUST state:
    "`minimal` is the 8-schema Hilbert axiom set `{φ | MinPropAxiom φ}`. It is NOT `MPL` (`MPL = ∅`);
    `IsMinimal` is a Hilbert-substrate notion ('carries the 8 connective axiom schemas'), distinct
    from natural-deduction minimal logic whose content lives in rule constructors."
  - [ ] Define the inclusion view reusing the existing class (DRY, no new 8-field duplicate):
    `IsMinimal (T : Theory Atom) : Prop := MinimalAxioms (fun φ => φ ∈ T)` — recommend an `abbrev`
    so `[IsMinimal T]` resolves through existing `MinimalAxioms` instances. Docstring each decl.
  - [ ] Use `lean_hover_info` to confirm `AxiomTheory` and `MinPropAxiom` are in scope at the
    insertion point (no new imports expected; both are already used in this file).
  - [ ] `omit [DecidableEq Atom] in` on any decl that does not use `DecidableEq` (avoid
    `unusedSectionVars`).
- **Timing:** ~40 min
- **Depends on:** none

### Phase 2: Prove the core lemma `(★)` [NOT STARTED]

- **Goal:** Prove `MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ`, the single load-bearing lemma
  both bridges reduce to.
- **Tasks:**
  - [ ] State `theorem minimalAxioms_iff_forall_minPropAxiom {Atom : Type*}
    (P : PL.Proposition Atom → Prop) : MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ` (camelCase;
    `theorem`, not `def`).
  - [ ] Forward (`mp`): given `[MinimalAxioms P]` / the structure, `intro φ h; cases h` and dispatch
    each of the 8 constructors with the corresponding field (`h_K`, `h_S`, `h_andI`, `h_andE1`,
    `h_andE2`, `h_orI1`, `h_orI2`, `h_orE`) — cloning the `cases h with | implyK a b => ...` shape
    of `MinPropAxiom.toIntPropAxiom` (`Axioms.lean:155-165`).
  - [ ] Backward (`mpr`): given `h : ∀ φ, MinPropAxiom φ → P φ`, build the `MinimalAxioms`
    structure with `constructor` / `⟨…⟩`, each field `fun … => h _ (.implyK …)` etc.
  - [ ] Try `by grind` first for parity with `isIntuitionisticIff`; if it does not close the
    8-schema goal, use the explicit `constructor`/`cases` proof above. Use `lean_multi_attempt`
    to test `grind` before committing the edit.
  - [ ] `omit [DecidableEq Atom] in` (the lemma does not need `DecidableEq`).
- **Timing:** ~45 min
- **Depends on:** none

### Phase 3: Derive both bridges and `isMinimalIff` [NOT STARTED]

- **Goal:** Derive the two deliverable bridges from `(★)` using `mem_axiomTheory` and
  `Set.setOf_subset_setOf`.
- **Tasks:**
  - [ ] Bridge (1) `isMinimalIff`:
    `theorem isMinimalIff (T : Theory Atom) : IsMinimal T ↔ minimal ⊆ T`. Reduce `minimal ⊆ T`
    to `∀ φ, MinPropAxiom φ → φ ∈ T` via `Set.setOf_subset` / `mem_axiomTheory`, then close with
    `(★)` at `P := (· ∈ T)`. Tag `@[scoped grind =]` to mirror `isIntuitionisticIff`.
  - [ ] Bridge (2) `minimalAxioms_iff_subset` (the high-value core):
    `theorem minimalAxioms_iff_subset (Axioms : PL.Proposition Atom → Prop) :
    MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms`. Both sides of the `⊆` are
    `{φ | …}`, so `Set.setOf_subset_setOf` reduces RHS to `∀ φ, MinPropAxiom φ → Axioms φ`; close
    with `(★)`.
  - [ ] Try `by grind` first on each; fall back to the explicit `(★)` + `setOf_subset_setOf`
    chain. Verify with `lean_goal` that the rewrite leaves exactly the `(★)` RHS.
  - [ ] camelCase names; docstring each theorem (state which direction is "for free" via
    `mem_axiomTheory`); `omit [DecidableEq Atom] in` as needed.
- **Timing:** ~40 min
- **Depends on:** 1, 2

### Phase 4: Optional monotone propagation + membership instance [NOT STARTED]

- **Goal:** Add the thin `Set.Subset.trans` propagation wrapper and a base membership instance,
  mirroring `instIsIntuitionisticExtention`. Include only if they land clean.
- **Tasks:**
  - [ ] `instIsMinimalExtention {T T' : Theory Atom} [IsMinimal T] (h : T ⊆ T') : IsMinimal T'`
    as a thin wrapper (via `isMinimalIff` + `Set.Subset.trans`, or directly transporting the
    `MinimalAxioms` fields along `h`). Tag `@[scoped grind →]` like the sibling. `omit [DecidableEq Atom] in`.
  - [ ] Optional base instance `instIsMinimalMinimal : IsMinimal (Atom := Atom) minimal`
    (witness: `minimal ⊆ minimal` is `subset_rfl`; or build via the existing
    `MinimalAxioms (@MinPropAxiom Atom)` instance through the definitional unfolding).
  - [ ] If either decl does not close cleanly within ~15 min, drop it (deliverable 3 is optional
    per research) and note the omission in the summary. Do NOT introduce a generic `IsStrength` class.
  - [ ] Docstring each decl.
- **Timing:** ~30 min
- **Depends on:** 3

### Phase 5: CI verification (full pipeline) [NOT STARTED]

- **Goal:** Confirm the change is zero-debt and CI-green across the whole pipeline.
- **Tasks:**
  - [ ] `lean_verify` the new decls (fully qualified names) to confirm no `sorry`/`axiom`.
  - [ ] `lake exe cache get` (if not already cached on this branch).
  - [ ] `lake build` of the whole `Logics/Propositional` subtree (new `@[scoped grind]` attributes
    can perturb unrelated `grind` proofs — build broadly, not just `Equivalence.lean`).
  - [ ] `lake exe checkInitImports` (file already imports `Cslib.Init`; confirm).
  - [ ] `lake exe lint-style` (text linters; `--fix` if needed).
  - [ ] `lake lint` (environment linters: docBlame on class/fields/decls, defLemma, camelCase).
  - [ ] `lake shake --add-public --keep-implied --keep-prefix` (import minimization).
  - [ ] `lake test` (run `CslibTests/`).
  - [ ] Resolve any failures and re-run the affected step until clean.
- **Timing:** ~25 min (plus build time)
- **Depends on:** 4

## Testing & Validation

- [ ] `MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ` `(★)` compiles with no `sorry`/`axiom`.
- [ ] `isMinimalIff : IsMinimal T ↔ minimal ⊆ T` compiles.
- [ ] `minimalAxioms_iff_subset : MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms` compiles.
- [ ] Sanity check on meaning: `minimal` is `{φ | MinPropAxiom φ}`, NOT `∅` — confirm bridge (2)
  is non-vacuous (RHS is not `True`).
- [ ] `lean_verify` reports no axioms beyond the standard prelude and no `sorry`.
- [ ] Full CSLib CI pipeline green: `lake build` (subtree), `checkInitImports`, `lint-style`,
  `lint`, `shake`, `test`.
- [ ] No edits to any file other than `Equivalence.lean` (or `Defs.lean` only under the Option A
  fallback); ~150 `MinimalAxioms` consumer sites untouched.

## Artifacts & Outputs

- plans/01_isminimal-reconciliation.md (this file)
- Modified: `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` — adds `minimal`,
  `IsMinimal`, `minimalAxioms_iff_forall_minPropAxiom` `(★)`, `isMinimalIff`,
  `minimalAxioms_iff_subset`, and optionally `instIsMinimalExtention` / `instIsMinimalMinimal`.
- summaries/01_isminimal-reconciliation-summary.md (on implementation completion)

## Rollback/Contingency

- The change is additive and confined to a single file. To revert: `git checkout --
  Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (or remove the appended block).
  No downstream consumer depends on the new decls, so reverting cannot break existing proofs.
- **Open Decision (planner gate) — triad symmetry vs DRY**: the recommended placement is Option B
  (downstream in `Equivalence.lean`). If a reviewer insists `IsMinimal`/`minimal` sit physically
  beside `IsIntuitionistic`/`IsClassical` in `Defs.lean`, fall back to Option A: define a
  self-contained `minimal` in `Defs.lean` (without referencing `MinPropAxiom`) plus a connecting
  lemma `mem_minimal_iff_minPropAxiom` in `Equivalence.lean`. This raises risk (re-encoding the 8
  schemas, 16 hand-proved range obligations, `grind`-on-union) and should be taken only on explicit
  reviewer request.
- **`grind` contingency**: if `grind` fails anywhere, the explicit `(★)` + `Set.setOf_subset_setOf`
  chain is search-free and always available; this is an implementation-detail fallback, not a blocker.
- If Phase 4 (optional propagation) does not land clean, ship Phases 1-3 + 5 alone — deliverables
  (1) and (2) are the required core; deliverable (3) is optional.
