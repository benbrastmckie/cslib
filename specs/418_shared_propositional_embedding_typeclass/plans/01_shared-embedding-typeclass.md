# Implementation Plan: Task #418 — Shared `PropositionalEmbedding` typeclass + single limitation note

- **Task**: 418 - Shared PropositionalEmbedding typeclass + single limitation note
- **Status**: [IMPLEMENTING]
- **Effort**: 4 hours
- **Dependencies**: None (coordination point with Task 417 — see Risks)
- **Research Inputs**: reports/01_shared-embedding-typeclass.md
- **Artifacts**: plans/01_shared-embedding-typeclass.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Factor the three near-identical "structural on atom/bot/imp, Łukasiewicz on and/or" embeddings
(`PL.Proposition.toModal`, `.toTemporal`, `.toBimodal`) into one shared skeleton plus a single
authored classical-scope note, preserving the entire simp/grind surface and the commuting-diamond
lemmas. Research confirms a reuse-first PASS: `Cslib/Foundations/Logic/Connectives.lean` already
supplies `HasBot`/`HasImp`/`PropositionalConnectives`, and all three targets are registered
instances mapping `bot := .bot`, `imp := .imp` to raw constructors. The only NEW abstraction needed
is an atom-injection class. Because every target instance maps to raw constructors, every rewritten
`toX_*` simp/grind lemma stays `rfl` and is kept verbatim — so the simp/grind surface and
commuting-diamond lemmas are preserved by construction. Definition of done: 1 new file +
3 thin-wrapper rewrites + 3 bridge-proof repoints, 0 new sorry, 0 new axiom, full CI green.

### Research Integration

Key findings from `reports/01_shared-embedding-typeclass.md` driving this plan:
- **Reuse-first PASS**: bot/imp typeclasses already exist; only an atom-injection class is new.
- **Layering hard constraint**: the skeleton CANNOT live in `Foundations/` (Foundations must not
  import Logics). It belongs in a new file `Cslib/Logics/Propositional/Embedding.lean`.
- **rfl-preservation**: with `toX := φ.embed` and instances setting `imp := .imp`/`bot := .bot` by
  projection `rfl`, the and/or cases are defeq to the existing `.and`/`.or` abbrevs, so every
  `toX_atom/bot/imp/and/or` simp lemma keeps type-checking as `rfl`.
- **Only non-mechanical churn**: ~3 bridge-proof clusters that unfold the raw def must repoint from
  `simp only [PL.Proposition.toX, …]` to the per-constructor simp lemmas (or add
  `PL.Proposition.embed` to the unfold set). The 15 Modal per-system files need no change.
- **Open implementation decision** (surfaced in Phase 1): typeclass-carried `atomEmbed`
  (optionally `outParam Atom`) vs explicit atom-map argument. Both are sorry-free; pick whichever
  elaborates the `rfl` wrapper lemmas cleanly.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no `roadmap_path` provided). This plan advances the
"structure-first" PL embedding consolidation lineage spawned from Task 415's lifting audit (§3,
Rank 3).

## Goals & Non-Goals

**Goals**:
- Add `Cslib/Logics/Propositional/Embedding.lean` holding: a `PropositionalEmbedding` typeclass
  (carrying `atomEmbed`), the single `PL.Proposition.embed` skeleton, the `@[simp]` `embed_*`
  equational lemmas, the SINGLE authored classical-scope limitation note, and an uninstantiated
  `NativePropositionalEmbedding` extension point.
- Rewrite `toModal`/`toTemporal`/`toBimodal` as thin `:= φ.embed` wrappers via per-target instances
  mapping `atomEmbed` to the target's `.atom` constructor.
- Keep every `toX_atom/bot/imp/and/or` simp/grind lemma verbatim (all remain `rfl`), preserving the
  simp/grind surface and the commuting-diamond lemmas (`toModal_toBimodal`, `toTemporal_toBimodal`,
  `embedding_commutes`).
- Collapse the triplicated limitation notes to one-line pointers at each target site.
- Repoint the ~3 bridge proofs that unfold the raw def.
- 0 new sorry, 0 new axiom, full CI green.

**Non-Goals**:
- Enabling the intuitionistic/native lift (the extension point stays uninstantiated by design).
- Pushing `and`/`or` into `PropositionalConnectives` (overlaps Task 173 — explicitly rejected in
  research §4; keep scope to `[HasBot F] [HasImp F]` + a local atom class).
- Changing the inter-target embeddings `Modal.Proposition.toBimodal` / `Temporal.Formula.toBimodal`
  (out of scope — they embed Modal→Bimodal / Temporal→Bimodal, not PL→X).
- Touching the 15 Modal per-system `ConservativeExtension.lean` files or any opaque consumer.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `PropositionalEmbedding Atom (Target Atom)` instance resolution is awkward (Atom not recovered from F) | M | M | Phase 1 validates the typeclass form FIRST; fall back to `outParam Atom` or an explicit-atom-map `embedWith` variant. Both are sorry-free. |
| A rewritten `toX_*` lemma stops being `rfl` after the wrapper change | M | L | Verify each lemma still elaborates as `rfl` with `lean_goal`/build immediately after each target rewrite; if not, the instance projection assumption is violated — re-check `imp := .imp`/`bot := .bot`. |
| **Task 417 file overlap**: 417 also edits `Temporal/ConservativeExtension.lean` and `Bimodal/.../PropositionalConservativity.lean` | M | M | This plan touches ONLY the bridge-proof `simp only` lines (Temporal :54,59,69; Bimodal :71,76,78,83,93). Sequence carefully: land 418 and 417 on separate branches; whichever lands second rebases and re-verifies those two files. Flag in PR description. |
| Commuting-diamond lemmas break | H | L | They depend only on the `@[simp]` per-constructor lemmas, which are kept verbatim; build Bimodal last and confirm `toModal_toBimodal`/`toTemporal_toBimodal`/`embedding_commutes` still close by `induction φ <;> simp [*]`. |
| Lint failures on new file (docBlame/defLemma/topNamespace) | L | M | Docstring the new `class`, `def`, and every `embed_*`; Prop-valued lemmas are `theorem`; names lowerCamelCase; instances inside `namespace Cslib.Logic`; preserve `@[simp, scoped grind =]` on Temporal exactly. |
| New module not registered in barrel | L | M | Run `lake exe mk_all --module` after adding the file; verify `Cslib.lean` updated. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel. Phases 2/3/4 own disjoint file territories
(Modal vs Temporal vs Bimodal) and may run in parallel; if run sequentially, follow the research's
recommended build order (Modal → Temporal → Bimodal).

### Phase 1: Create shared embedding skeleton + resolve atom-injection design [COMPLETED]

*(deviation: chosen form = typeclass-carried atomEmbed, plain (Atom, F) params, no outParam needed — elaborates cleanly)*

**Goal**: Author `Cslib/Logics/Propositional/Embedding.lean` with the typeclass, the `embed`
skeleton, the `@[simp]` `embed_*` lemmas, the single classical-scope note, and the uninstantiated
`NativePropositionalEmbedding` extension point; resolve the typeclass-vs-explicit-atom-map decision;
register the module and confirm it builds green in isolation.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Embedding.lean` with `import Cslib.Init` and
      `public import Cslib.Logics.Propositional.Defs` (pulls in `PL.Proposition` + Connectives
      transitively), under `namespace Cslib.Logic` with `@[expose] public section`.
- [ ] Define `class PropositionalEmbedding (Atom F) [HasBot F] [HasImp F]` carrying
      `atomEmbed : Atom → F`. Validate instance-resolution ergonomics: try the plain form first; if
      `Atom` is not recovered cleanly from `F`, switch to `outParam Atom` or provide an explicit
      `PL.Proposition.embedWith (atom : Atom → F)` variant. Record the chosen form in the phase
      completion note.
- [ ] Define `def PL.Proposition.embed` (plain `def`, not `abbrev`): structural on `atom`/`bot`/
      `imp`, Łukasiewicz on `and`/`or` (`and := imp (imp a (imp b bot)) bot`, `or := imp (imp a bot) b`).
- [ ] Add `@[simp]` equational lemmas `embed_atom/bot/imp/and/or` (all `rfl`), each docstringed.
- [ ] Author the SINGLE classical-scope limitation note (Łukasiewicz / [Wajsberg1938] /
      [McKinsey1939] caveat) as the `class`/`def` docstring — the one place this caveat lives.
- [ ] Add uninstantiated `class NativePropositionalEmbedding (Atom F) [HasBot F] [HasImp F]
      [HasAnd F] [HasOr F]` as a typed extension point (docstring: future intuitionistic-faithful
      embedding; deliberately not provided here).
- [ ] Register module: `lake exe mk_all --module`; confirm `Cslib.lean` barrel updated.
- [ ] Build `Cslib.Logics.Propositional.Embedding` green; run lint-style on the new file.

**Timing**: ~1.25 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Embedding.lean` - NEW: typeclass, `embed` skeleton, `embed_*` simp
  lemmas, single note, `NativePropositionalEmbedding` extension point.
- `Cslib.lean` - barrel update via `mk_all` (auto-generated).

**Verification**:
- `lake build Cslib.Logics.Propositional.Embedding` succeeds.
- New file passes `lake exe lint-style`; no docBlame/defLemma/topNamespace warnings.
- `embed_*` lemmas confirmed `rfl` (`lean_goal` at each, or build with no errors).
- Chosen atom-injection form recorded for use by Phases 2-4.

---

### Phase 2: Modal target — instance, thin wrapper, bridge repoint [COMPLETED]

**Goal**: Convert `PL.Proposition.toModal` to a thin wrapper over `embed` via a
`PropositionalEmbedding` instance, keep its simp lemmas verbatim, collapse the triplicated note to a
pointer, and repoint the in-file Modal bridge proof.

**Tasks**:
- [ ] Add `instance : PropositionalEmbedding Atom (Modal.Proposition Atom)` with
      `atomEmbed := Modal.Proposition.atom` (matching Phase 1's chosen form).
- [ ] Rewrite `def PL.Proposition.toModal φ := φ.embed`.
- [ ] Keep `toModal_atom/bot/imp/and/or` (`@[simp]`) and `toModal_neg` EXACTLY as today; confirm
      each still type-checks as `rfl`.
- [ ] Replace the 7-line "Limitations" block (+ redundant "Encoding Rationale" prose) with a
      one-line pointer to `PL.Proposition.embed` / `PropositionalEmbedding` in
      `Cslib/Logics/Propositional/Embedding.lean`; keep a one-line module summary.
- [ ] Repoint the bridge proof `modal_satisfies_toModal_iff_evaluate`
      (`Modal/FromPropositional.lean:115,119,130`): replace `simp only [PL.Proposition.toModal, …]`
      with the per-constructor simp lemmas (`toModal_imp/and/or/bot`, `Modal.Satisfies`,
      `PL.Evaluate`) or add `PL.Proposition.embed` to the unfold set. Leave `by_contra`/`by_cases`
      bodies unchanged.

**Timing**: ~0.75 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/FromPropositional.lean` - instance added, `toModal` → wrapper, note
  collapsed, simp lemmas kept verbatim, bridge proof repointed (lines 115/119/130).

**Verification**:
- `lake build Cslib.Logics.Modal.FromPropositional` green.
- `lean_goal` confirms the bridge proof closes; `toModal_*` lemmas still `rfl`.
- Module passes `lake exe lint-style`.

---

### Phase 3: Temporal target — instance, thin wrapper, bridge repoint [COMPLETED]

**Goal**: Same conversion for `toTemporal`, preserving the grind surface, and repoint the Temporal
conservative-extension bridge. Coordinate with Task 417 (shared file).

**Tasks**:
- [ ] Add `instance : PropositionalEmbedding Atom (Temporal.Formula Atom)` with
      `atomEmbed := Temporal.Formula.atom`.
- [ ] Rewrite `def PL.Proposition.toTemporal φ := φ.embed`.
- [ ] Keep `toTemporal_atom/bot/imp/and/or` with `@[simp, scoped grind =]` EXACTLY (this is the only
      grind surface) and `toTemporal_neg`; confirm each still `rfl`.
- [ ] Collapse the triplicated note to a one-line pointer; keep a one-line module summary.
- [ ] Repoint the bridge proof `temporal_satisfies_toTemporal_iff_evaluate`
      (`Temporal/ConservativeExtension.lean:54,59,69`) from `simp only [PL.Proposition.toTemporal, …]`
      to per-constructor simp lemmas (or unfold `embed`). Bodies unchanged.
- [ ] **Task 417 coordination**: this phase edits `Temporal/ConservativeExtension.lean`, which
      Task 417 also touches. Restrict edits to the bridge `simp only` lines; note the overlap for
      rebase/PR sequencing.

**Timing**: ~0.75 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/FromPropositional.lean` - instance added, `toTemporal` → wrapper, note
  collapsed, `@[simp, scoped grind =]` lemmas kept verbatim.
- `Cslib/Logics/Temporal/ConservativeExtension.lean` - bridge proof repointed (lines 54/59/69).
  SHARED with Task 417 — coordinate.

**Verification**:
- `lake build Cslib.Logics.Temporal.FromPropositional` and
  `Cslib.Logics.Temporal.ConservativeExtension` green.
- Grind surface intact (`@[simp, scoped grind =]` attributes unchanged); `toTemporal_*` still `rfl`.
- Module passes `lake exe lint-style`.

---

### Phase 4: Bimodal target — instance, thin wrapper, bridge repoint, commuting-diamond check [COMPLETED]

*(deviation: bridge proof in PropositionalConservativity.lean already used evaluate_iff_of_classicalBridge (Task 417); no simp-only repoint needed for Temporal/Bimodal bridge proofs)*

**Goal**: Same conversion for `toBimodal`, repoint the Bimodal conservativity bridge, and confirm
the commuting-diamond lemmas still hold. Coordinate with Task 417 (shared file).

**Tasks**:
- [ ] Add `instance : PropositionalEmbedding Atom (Bimodal.Formula Atom)` with
      `atomEmbed := Bimodal.Formula.atom`.
- [ ] Rewrite `def PL.Proposition.toBimodal φ := φ.embed`.
- [ ] Keep `toBimodal_atom/bot/imp/and/or` (`@[simp]`) and `toBimodal_neg` EXACTLY; confirm `rfl`.
- [ ] Collapse the triplicated note to a one-line pointer; keep a one-line module summary.
- [ ] Confirm the commuting-diamond lemmas `toModal_toBimodal`, `toTemporal_toBimodal`,
      `embedding_commutes` still close by `induction φ <;> simp [*]` (they depend only on the kept
      per-constructor simp lemmas). Do NOT modify the inter-target embeddings.
- [ ] Repoint the bridge proof `bimodal_truthAt_toBimodal_iff_evaluate`
      (`Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean:71,76,78,83,93`).
      Bodies unchanged.
- [ ] **Task 417 coordination**: this phase edits `PropositionalConservativity.lean`, which
      Task 417 also touches. Restrict edits to the bridge `simp only` lines; note overlap for
      rebase/PR sequencing.

**Timing**: ~0.75 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` - instance added, `toBimodal` →
  wrapper, note collapsed, simp lemmas kept verbatim.
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean` - bridge
  proof repointed (lines 71/76/78/83/93). SHARED with Task 417 — coordinate.

**Verification**:
- `lake build` of the Bimodal embedding + conservativity modules green.
- `toModal_toBimodal`/`toTemporal_toBimodal`/`embedding_commutes` confirmed still closing.
- `toBimodal_*` still `rfl`; module passes `lake exe lint-style`.

---

### Phase 5: Full CI green + final verification [COMPLETED]

**Goal**: Run the complete CSLib CI pipeline across the whole tree and confirm 0 new sorry,
0 new axiom, all green.

**Tasks**:
- [ ] `lake build` (full).
- [ ] `lake exe checkInitImports`.
- [ ] `lake exe lint-style`.
- [ ] `lake test`.
- [ ] `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Confirm no new `sorry` and no new `axiom` introduced (grep the touched files;
      `lean_verify` on `PL.Proposition.embed` and the three `toX` wrappers).
- [ ] Verify the triplicated notes are gone (one authored note remains in `Embedding.lean`; three
      one-line pointers at the target sites).

**Timing**: ~0.5 hours

**Depends on**: 2, 3, 4

**Files to modify**:
- None (verification only; fix-forward into the owning phase's files if CI surfaces an issue).

**Verification**:
- All five CI commands exit 0.
- 0 new sorry, 0 new axiom.

## Testing & Validation

- [ ] `lake build` succeeds for the new module and every touched module, then full tree.
- [ ] `lake exe checkInitImports` passes (new file imports `Cslib.Init`).
- [ ] `lake exe lint-style` passes (docstrings, naming, namespacing on the new file).
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no issues.
- [ ] Every `toModal_*`/`toTemporal_*`/`toBimodal_*` simp/grind lemma still elaborates as `rfl`.
- [ ] Commuting-diamond lemmas (`toModal_toBimodal`, `toTemporal_toBimodal`, `embedding_commutes`)
      still close.
- [ ] 0 new sorry, 0 new axiom (`lean_verify`).

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Embedding.lean` (NEW, ~70-100 lines).
- `Cslib.lean` barrel update (via `mk_all`).
- Edited: `Cslib/Logics/Modal/FromPropositional.lean`,
  `Cslib/Logics/Temporal/FromPropositional.lean`,
  `Cslib/Logics/Temporal/ConservativeExtension.lean`,
  `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean`,
  `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean`.
- `specs/418_shared_propositional_embedding_typeclass/summaries/01_shared-embedding-typeclass-summary.md`
  (on implementation completion).

## Rollback/Contingency

- All work is on a feature branch; revert by dropping the branch (no consumer signatures change —
  `toModal`/`toTemporal`/`toBimodal` keep identical types and simp surfaces, so reverting is safe).
- If the typeclass form proves fragile to elaborate (Phase 1 risk), fall back to the explicit
  `PL.Proposition.embedWith (atom : Atom → F)` variant; Phases 2-4 then pass the target `.atom`
  map explicitly instead of via an instance. No proof bodies change.
- If Task 417 lands first and conflicts on `Temporal/ConservativeExtension.lean` /
  `PropositionalConservativity.lean`, rebase Phases 3/4's narrow `simp only` edits onto 417's
  version and re-run the per-module builds before final CI.
