# Implementation Plan: Collapse the Three Brouwerian Completeness Modules

- **Task**: 367 - unify_brouwerian_completeness_triplication
- **Status**: [IMPLEMENTING]
- **Effort**: 9 hours
- **Dependencies**: Task 345 (`IsMinimal` family — landed, commit 59c1d3ff); Task 348 (theory-parametric conservativity substrate — landed, commit 8a32b3ef)
- **Research Inputs**: specs/367_unify_brouwerian_completeness_triplication/reports/01_unify-brouwerian-triplication.md
- **Artifacts**: plans/01_unify-brouwerian-triplication.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md (full CSLib CI)
- **Type**: cslib
- **Lean Intent**: true

## Overview

Collapse the three near-identical Brouwerian completeness modules
(`Algebra/{BrouwerianCompleteness.lean (528), PointedBrouwerianCompleteness.lean (561),
MplPointedConservative.lean (658)}` = 1,747 lines) into one parametric development over the
`AlgEvaluate`/`AlgTValid` substrate, with the bot interpretation as the single varying
parameter. The three modules are ~80% identical: they share a Brouwerian Lindenbaum quotient,
order lemmas, congruences, a truth lemma, and a completeness/iff skeleton, all of which the
**generic** `HilbertLindenbaum.lean` machinery already provides (parametric over an arbitrary
`Axioms` predicate, using only the five conj-imp witnesses K/S/andI/andE1/andE2). The fragments
re-derive them by hand only because the fragment axiom families do not satisfy the 8-field
`MinimalAxioms` class (they have no `or` axioms). The fix is to introduce a 5-field
`ConjImpAxioms` typeclass (a strict factor of `MinimalAxioms`), make `MinimalAxioms extends`
it, generalize the meet-fragment Lindenbaum lemma bounds to `[ConjImpAxioms]`, add one
`BrouwerianSemilattice` instance, host the universal evaluator `BrouwerianBotEvaluate` in
substrate, and recover all three tiers as corollaries that fix `bot_val` (pointed additionally
adds `OrderBot` via `efq`). Definition of done: net ~−1000 lines, no new axioms, no `sorry`,
every existing public theorem preserved as corollary/alias, all three filenames kept as thin
re-export shims so consumer imports stay valid, and full CSLib CI green.

### Research Integration

This plan is built directly on `reports/01_unify-brouwerian-triplication.md`:
- **Reuse finding (decisive)** -> Phase 3: every meet-fragment lemma in `HilbertLindenbaum.lean`
  (`hilbertLindenbaumLe_refl/trans/antisymm`, `inf_le_left/right`, `le_inf`, `le_top`,
  `le_himp_iff`, `mk_eq_top_iff`, the `Inf`/`Himp` ops + congruences, `canonicalV`,
  `canonicalBotVal`) uses only the five conj-imp fields; generalizing their bound from
  `[MinimalAxioms]` to `[ConjImpAxioms]` is a pure typeclass-parameter change.
- **5-field typeclass + extends** -> Phase 1: `class ConjImpAxioms`, `MinimalAxioms extends
  ConjImpAxioms`, and three fragment instances (`ConjImpAxiom`, `ConjImpBotAxiom`,
  `ConjImpBotMinAxiom`).
- **Universal evaluator already exists** -> Phase 2: `BrouwerianBotEvaluate v bot_val`
  (currently at `MplPointedConservative.lean:97`); the other two evaluators are definitionally
  it at ⊤/⊥, recovered by two one-line bridge inductions.
- **Soundness genericity limit** -> Phase 4: `cases h_ax` needs the concrete inductive (and the
  `efq` case for the pointed tier), so prove five schema-soundness lemmas once over
  `[ConjImpAxioms]`/`BrouwerianBotEvaluate`, then thin per-tier `cases` wrappers.
- **8 load-bearing public names** -> Phase 5: `conjImp_brouwerian_complete`,
  `conjImp_brouwerian_iff`, `conjImp_brouwerian_soundness_derivable`,
  `conjImpBot_pointedBrouwerian_complete`, `conjImpBotMin_brouwerianBot_complete`,
  `BrouwerianBotEvaluate`, `BrouwerianBotValid`, `brouwerianBotEmbeddingLemma` — all preserved;
  Lindenbaum internals are private and freely collapsible.
- **TOP RISK (instance diamond)** -> Phase 3 EARLY scoped `lake build` gate, with Approach B
  fallback (`Algebra/BrouwerianLindenbaum.lean`).

Two research open questions were resolved during planning by direct source inspection:
- `IsOrBotFree → IsOrFree` already exists as `IsOrBotFree_implies_IsOrFree`
  (`FragmentPredicates.lean:85`) — risk 3 closed, no new helper needed.
- `MinimalAxioms` lives in `NaturalDeduction/Equivalence.lean`; `FragmentAxioms.lean` and
  `FragmentPredicates.lean` are in `ProofSystem/` and `Semantics/Algebra/` respectively.

### Prior Plan Reference

No prior plan. (The structurally analogous task 348 plan — parametric conservativity spine —
was consulted for format and for the per-phase `lake build` + CI discipline used here.)

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap path provided). The task advances the propositional
algebra de-duplication programme (the 341/345/348/367 cluster); 345 and 348 are its landed
prerequisites in this worktree.

## Goals & Non-Goals

**Goals**:
- Introduce `class ConjImpAxioms` (5 fields) as a strict factor of `MinimalAxioms`; refactor
  `MinimalAxioms extends ConjImpAxioms`; add three fragment instances.
- Relocate `BrouwerianBotEvaluate`/`BrouwerianBotValid` and the embedding lemmas
  (`iicBrouwerianBotEvaluateEqAlgEvaluate`, `brouwerianBotEmbeddingLemma`) to substrate, plus
  two bridge lemmas equating the Brouwerian/pointed evaluators to `BrouwerianBotEvaluate` at
  ⊤/⊥.
- Generalize the meet-fragment Lindenbaum lemma bounds in `HilbertLindenbaum.lean` to
  `[ConjImpAxioms]` and add one `BrouwerianSemilattice` instance.
- Prove generic soundness (5 schema lemmas + per-tier `cases` wrappers), a generic truth lemma,
  and generic completeness once over `BrouwerianBotEvaluate`.
- Recover all three tiers' public theorems as corollaries/aliases that fix `bot_val` (pointed
  adds `OrderBot` via `efq`); keep all three original filenames as thin re-export shims.
- Net ~−1000 lines; zero `sorry`, zero new `axiom`; full CSLib CI green
  (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`).

**Non-Goals**:
- Modifying or re-deriving the generic `sup`-related machinery (`hilbertLindenbaumSup*`,
  `hilbertEquivOrCongr`, `hilbertLindenbaumMk_sup`) or the `GeneralizedHeytingAlgebra`
  instance — these keep their `[MinimalAxioms]` bound, untouched.
- Unifying soundness into a single theorem (impossible: `cases h_ax` needs the concrete
  inductive + the `efq` case).
- Renaming any externally-referenced public name, or changing any public signature.
- Changing downstream consumers (`ConjImpConservative.lean`, `ConservativeChain.lean`,
  `ImpConservative.lean`, `ConjImpBotConservative.lean`, `MplConservativeChain.lean`) — the
  re-export shims must keep their import paths valid.
- Touching the `or`/`efq` semantics beyond the single tier-specific `OrderBot` instance.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1 (TOP): Instance diamond — `HilbertLindenbaumAlgebra Axioms` would carry both `BrouwerianSemilattice` (via `ConjImpAxioms`) and `GeneralizedHeytingAlgebra` (via `MinimalAxioms`) for full-axiom `Axioms`; two paths to `BrouwerianSemilattice`/`PartialOrder`/`SemilatticeInf` with possibly mismatched `le`/`inf` | H | M | The GHA's `le`/`inf`/`himp` are the *same* underlying functions (`hilbertLindenbaumLe/Inf/Himp`), so instances should be defeq. **Phase 3 runs an EARLY scoped `lake build`** the moment the BSL instance is added, before any downstream work depends on it. If a diamond bites, switch to Approach B: self-contained `Algebra/BrouwerianLindenbaum.lean` re-deriving the meet-only Lindenbaum once over `[ConjImpAxioms]` (no GHA on that algebra type) — guaranteed conflict-free, ~250 fewer lines saved. |
| R2: `MinimalAxioms extends ConjImpAxioms` ripple — the three existing instances (`MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom`) list 8 fields each | M | M | `extends` accepts an 8-field `where` literal (Lean auto-builds the parent). Phase 1 rebuilds `Equivalence.lean` and confirms all three elaborate. Fallback: skip the `extends` refactor and add a standalone `instance [MinimalAxioms A] : ConjImpAxioms A` (zero duplication risk, one extra instance). |
| R3: Soundness cannot fully unify — `cases h_ax` needs the concrete inductive + `efq` case | M | H (known) | Plan for 5 schema-soundness lemmas over `[ConjImpAxioms]`/`BrouwerianBotEvaluate` + thin per-tier `cases` wrappers (pointed adds one `efq` line). Encoded in Phase 4. |
| R4: `BrouwerianBotEvaluate` relocation changes its declaring module; downstream `MplConservativeChain.lean` imports it | M | M | Host it in a substrate file (`Algebra/Brouwerian.lean` or new `Algebra/BrouwerianBot.lean`) that is in the transitive imports of every consumer. If a new file is added, run `lake exe mk_all --module` to refresh the barrel and `lake shake` after import changes. Verify the unified completeness module re-exports it so `Algebra.MplPointedConservative` still resolves the name. |
| R5: `@[simp]` set drift — the per-tier `*Mk_inf/_himp/_le_mk/_bot` simp lemmas drive the truth-lemma `simp only` calls | L | M | The generic `hilbertLindenbaumMk_inf/_himp/_le_mk` are already `@[simp]`; ensure the generic truth lemma's `simp only` references the generic names. Rebuild after each phase to catch simp regressions. |
| R6: Import cycle when relocating the evaluator/embedding lemmas to substrate | M | M | Relocate (do not duplicate) into a low file imported by all three tiers; rebuild the whole `Logics/Propositional/Semantics/Algebra` subtree each phase, not just touched files. |
| R7: Public-surface erosion — a non-load-bearing public name silently dropped during collapse | M | M | Phase 5 re-exposes the full public surface (Appendix A of the report) as corollaries/`alias`/`abbrev`; diff the public name set before/after; the 8 load-bearing names are a hard build gate. |
| R8: Lint debt on new declarations (docBlame, namespace, camelCase) | L | M | New `ConjImpAxioms` class + fields get docstrings; instances use lowerCamelCase; preserve `@[expose] public section`/`module` headers and `Cslib.Init` import. Phase 5 runs full lint/shake and fixes findings. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel. (Phase 1 touches `Equivalence.lean` +
`FragmentAxioms.lean`; Phase 2 touches substrate evaluator files — they are disjoint and may run
in parallel.)

### Phase 1: `ConjImpAxioms` class + `MinimalAxioms extends` + 3 fragment instances [COMPLETED]

**Goal**: Introduce the single varying proof-theoretic input — a 5-field conj-imp typeclass that
is a strict factor of `MinimalAxioms` — and give the three fragment axiom families instances,
without touching any Lindenbaum or completeness code yet.

**Tasks**:
- [ ] In `NaturalDeduction/Equivalence.lean`, add `class ConjImpAxioms {Atom} (Axioms :
  PL.Proposition Atom → Prop) : Prop` with the five fields `h_K`, `h_S`, `h_andI`, `h_andE1`,
  `h_andE2` (exact signatures in research §"New typeclass"). Docstring the class and each field
  (docBlame).
- [ ] Refactor `class MinimalAxioms ... extends ConjImpAxioms Axioms where h_orI1 / h_orI2 /
  h_orE` so the conj-imp projections are inherited (one source of truth). Keep all existing
  `[MinimalAxioms _]` signatures and projection uses working unchanged.
- [ ] Rebuild `Equivalence.lean` and confirm the three existing instances (`MinPropAxiom`,
  `IntPropAxiom`, `PropositionalAxiom`) still elaborate with their 8-field `where` literals.
  **If any fails to elaborate (R2)**: revert to a flat `MinimalAxioms` and instead add a
  standalone `instance {A} [MinimalAxioms A] : ConjImpAxioms A := ⟨..⟩`; record the deviation.
- [ ] In `ProofSystem/FragmentAxioms.lean`, add three instances:
  `instance : ConjImpAxioms (@ConjImpAxiom Atom)`,
  `instance : ConjImpAxioms (@ConjImpBotAxiom Atom)`,
  `instance : ConjImpAxioms (@ConjImpBotMinAxiom Atom)`, each `:= ⟨fun .. => .implyK .., ..⟩`
  using the existing witnesses (`*.mem_implyK`, `*.mem_implyS`, and the `.andI/.andE1/.andE2`
  constructors). lowerCamelCase names; docstrings if required by lint.
- [ ] `lake build` the touched files and confirm sorry-free / axiom-free.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` — add `ConjImpAxioms`, refactor
  `MinimalAxioms extends`.
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` — add three `ConjImpAxioms`
  instances.

**Verification**:
- `ConjImpAxioms` and the three instances typecheck; the three `MinimalAxioms` instances still
  elaborate.
- `lake build` green on the touched files; `lean_verify` / grep confirms no `sorry`/new `axiom`.

---

### Phase 2: Relocate evaluator + embedding lemmas to substrate + 2 bridge lemmas [COMPLETED]

**Goal**: Make the universal evaluator `BrouwerianBotEvaluate`/`BrouwerianBotValid` and the
embedding lemmas part of the shared substrate, and prove the two definitional bridges that
recover the Brouwerian (⊤) and pointed (⊥) evaluators from it.

**Tasks**:
- [ ] Choose the substrate host: extend `Algebra/Brouwerian.lean` or add new
  `Algebra/BrouwerianBot.lean` (must be in the transitive imports of all three tier files and of
  `MplConservativeChain.lean`). Relocate (do **not** duplicate) `BrouwerianBotEvaluate`,
  `BrouwerianBotValid`, their `@[simp]` lemmas, `iicBrouwerianBotEvaluateEqAlgEvaluate`, and
  `brouwerianBotEmbeddingLemma` out of `MplPointedConservative.lean` into the host (R4/R6).
- [ ] Add bridge lemma `brouwerianEvaluate_eq_bot_top :
  BrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊤ φ` by `induction φ <;> simp [..]`
  (every constructor arm matches definitionally; the `or` arm is `⊤` on both sides).
- [ ] Add bridge lemma `pointedBrouwerianEvaluate_eq_bot_bot :
  PointedBrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊥ φ` by the same one-line induction.
- [ ] If a new file was created, run `lake exe mk_all --module` to refresh the `Cslib.lean`
  barrel; add the `Cslib.Init` import and preserve `module`/`@[expose] public section` headers.
- [ ] `lake build` the substrate file + the `Algebra` subtree; confirm sorry-free / axiom-free
  and that downstream files still see `BrouwerianBotEvaluate` (no consumer edits needed).

**Timing**: 1.5 hours

**Depends on**: none (independent of Phase 1; touches disjoint files)

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean` (or new
  `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianBot.lean`) — host the evaluator,
  validity, embedding lemmas, and the two bridge lemmas.
- `Cslib/Logics/Propositional/Semantics/Algebra/MplPointedConservative.lean` — remove the
  relocated declarations (temporary; fully reshaped in Phase 5).
- `Cslib.lean` (barrel) — only if a new file is added.

**Verification**:
- Both bridge lemmas typecheck and are sorry-free / axiom-free.
- `lake build` green on the subtree; `lake exe checkInitImports` passes if a file was added.
- Grep confirms `BrouwerianBotEvaluate`/`BrouwerianBotValid` resolve from the new home in
  `MplConservativeChain.lean`'s import closure.

---

### Phase 3: Generalize meet-fragment bounds to `[ConjImpAxioms]` + `BrouwerianSemilattice` instance (EARLY diamond build) [COMPLETED]

**Goal**: Make the generic Lindenbaum meet-fragment lemmas available to the fragment axiom
families by weakening their bound to `[ConjImpAxioms]`, and add the single
`BrouwerianSemilattice` instance — verifying the TOP RISK instance diamond with an early scoped
build before anything depends on it.

**Tasks**:
- [ ] In `Algebra/HilbertLindenbaum.lean`, weaken the typeclass bound from `[MinimalAxioms
  Axioms]` to `[ConjImpAxioms Axioms]` on exactly the meet-fragment lemmas (per the report's API
  table): `HilbertEquiv`/`hilbertEquiv_*`/setoid, `hilbertLindenbaumLe`/`..Le_mk`/`..Mk_le_mk`,
  `hilbertEquivAndCongr`, `hilbertEquivImpCongr`, `hilbertLindenbaumInf/Himp` (+ `_mk`),
  `hilbertLindenbaumLe_refl/trans/antisymm`, `hilbertLindenbaumInf_le_left/right`,
  `hilbertLindenbaumLe_inf`, `hilbertLindenbaumLe_top`, `hilbertLindenbaumLe_himp_iff`,
  `hilbertLindenbaumMk_eq_top_iff`, `canonicalV`, `canonicalBotVal`. **Leave** the `sup`-family
  (`hilbertLindenbaumSup*`, `hilbertEquivOrCongr`, `hilbertLindenbaumMk_sup`) and the
  `GeneralizedHeytingAlgebra` instance bounded at `[MinimalAxioms]`.
- [ ] Add `instance hilbertLindenbaumBSL {Axioms} [ConjImpAxioms Axioms] :
  BrouwerianSemilattice (HilbertLindenbaumAlgebra Axioms)` populating the 12 fields from the
  now-generalized lemmas (`le := hilbertLindenbaumLe`, `top := hilbertLindenbaumMk (bot.imp
  bot)`, `inf := hilbertLindenbaumInf`, `himp := hilbertLindenbaumHimp`, etc.). lowerCamelCase,
  docstring.
- [ ] **EARLY DIAMOND GATE (R1, do this immediately after adding the instance)**: run a scoped
  `lake build` of `Algebra/HilbertLindenbaum.lean` AND a file that elaborates the BSL instance
  for a *full-axiom* `Axioms` (one that also has the GHA instance). Confirm Lean does not report
  two distinct `BrouwerianSemilattice`/`PartialOrder`/`SemilatticeInf` paths and that
  `le`/`inf`/`himp` are defeq. Use `lean_goal`/`lean_diagnostic_messages` to inspect if needed.
- [ ] **If the diamond bites**: abandon Approach A for the BSL instance and switch to Approach B
  — create `Algebra/BrouwerianLindenbaum.lean` that re-derives the meet-only Lindenbaum once
  over `[ConjImpAxioms]` (no GHA on that algebra type), producing the BSL instance there. Keep
  the bound generalizations that did not conflict. Record the deviation per the protocol below.
- [ ] `lake build` the `Algebra` subtree; confirm sorry-free / axiom-free.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` — weaken meet-fragment
  bounds; add `hilbertLindenbaumBSL` instance (Approach A).
- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianLindenbaum.lean` — **only if** Approach
  B fallback is triggered.

**Verification**:
- Meet-fragment lemmas typecheck under `[ConjImpAxioms]`; `sup`-family + GHA still under
  `[MinimalAxioms]`.
- **Diamond gate passes**: no instance-diamond / defeq diagnostic for a full-axiom `Axioms`
  carrying both BSL and GHA.
- `lake build` green on the subtree; sorry-free / axiom-free.

---

### Phase 4: Generic soundness (5 schema lemmas + wrappers) + truth lemma + completeness [COMPLETED]

**Goal**: Prove the shared completeness machinery exactly once over `BrouwerianBotEvaluate` and
`[ConjImpAxioms]`: the five schema-soundness lemmas, the generic truth lemma, and generic
completeness.

**Tasks**:
- [ ] In the unified core (reuse the `MplPointedConservative.lean` slot or a new
  `Algebra/BrouwerianCompletenessGeneric.lean`), prove the five schema-soundness lemmas over
  `[ConjImpAxioms]`/`BrouwerianBotEvaluate`: `implyK_sound`, `implyS_sound`, `andI_sound`,
  `andE1_sound`, `andE2_sound` (the `implyS` proof — ~12 lines — is the main duplication being
  removed). No `efq` here (it is tier-specific).
- [ ] Prove the generic truth lemma `brouwerianBotCanonicalV_spec {Axioms} [ConjImpAxioms
  Axioms] (A) (hA : A.IsOrFree) : BrouwerianBotEvaluate (canonicalV Axioms) (canonicalBotVal
  Axioms) A = hilbertLindenbaumMk A` by induction (atom/imp/and from the generic simp lemmas;
  `or` excluded by `IsOrFree`; `bot` = `canonicalBotVal`). Ensure the `simp only` references the
  **generic** `hilbertLindenbaumMk_inf/_himp/_le_mk` names (R5).
- [ ] Prove generic completeness `brouwerianBot_complete {Axioms} [ConjImpAxioms Axioms] {φ}
  (hfrag : φ.IsOrFree) (h : ..BrouwerianBotValid..) : Derivable Axioms φ` by instantiating
  validity at the Lindenbaum algebra, rewriting with the truth lemma, finishing with
  `hilbertLindenbaumMk_eq_top_iff`.
- [ ] `lake build`; confirm sorry-free / axiom-free.

**Timing**: 2 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/MplPointedConservative.lean` (reshaped as the
  unified core) or new `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompletenessGeneric.lean`
  — five schema-soundness lemmas, generic truth lemma, generic completeness.

**Verification**:
- All five schema lemmas, the truth lemma, and `brouwerianBot_complete` typecheck and are
  sorry-free / axiom-free.
- The truth lemma's `simp only` uses generic `@[simp]` names (no dangling per-tier references).
- `lake build` green on the subtree.

---

### Phase 5: Recover three tier theorems as corollaries + re-export shims + full CI gate [IN PROGRESS]

**Goal**: Re-derive every public per-tier theorem as a corollary of the generic development
(preserving all names and signatures), keep all three original filenames as thin re-export
shims, and pass the full CSLib CI pipeline.

**Tasks**:
- [ ] **Brouwerian tier** (`ConjImpAxiom`, `bot_val = ⊤`): recover
  `conjImp_brouwerian_soundness_derivable` via the `brouwerianEvaluate_eq_bot_top` bridge + the
  schema lemmas at ⊤; recover `conjImp_brouwerian_complete` (guard `IsOrBotFree`, lifted to
  `IsOrFree` via the existing `IsOrBotFree_implies_IsOrFree`) from `brouwerianBot_complete`;
  recover `conjImp_brouwerian_iff` as the anonymous constructor.
- [ ] **Pointed tier** (`ConjImpBotAxiom`, `bot_val = ⊥`, `+OrderBot`): add the single
  tier-specific `instance : OrderBot (HilbertLindenbaumAlgebra ConjImpBotAxiom)` with `bot_le`
  proved exactly as the old `pointedBrouwerianLindenbaumBot_le` using `ConjImpBotAxiom.efq`
  (the only use of `efq`); add the per-tier soundness `cases` wrapper (5 schema cases + the one
  `efq` line); recover `conjImpBot_pointedBrouwerian_complete` via the
  `pointedBrouwerianEvaluate_eq_bot_bot` bridge (at the Lindenbaum algebra `⊥ = [⊥] =
  canonicalBotVal`).
- [ ] **Free-bot tier** (`ConjImpBotMinAxiom`, free `bot_val`): recover
  `conjImpBotMin_brouwerianBot_complete` as a direct specialization of the generic development;
  `BrouwerianBotEvaluate`/`BrouwerianBotValid`/`brouwerianBotEmbeddingLemma` are already in
  substrate (Phase 2).
- [ ] **Re-export shims**: keep all three filenames (`BrouwerianCompleteness.lean`,
  `PointedBrouwerianCompleteness.lean`, `MplPointedConservative.lean`) as thin modules that
  `import` the unified core and contain the tier corollaries, so consumer import paths
  (`Algebra.BrouwerianCompleteness`, `Algebra.PointedBrouwerianCompleteness`,
  `Algebra.MplPointedConservative`) stay valid with zero consumer edits.
- [ ] **Full public-surface recovery (R7)**: re-expose every other public name from the three
  files (`*_axiom_sound`, `*_soundness`, `*_iff`, `iicBrouwerianBotEvaluateEqAlgEvaluate`, etc.)
  as corollaries/`alias`/`abbrev` per the task's "every existing theorem preserved" requirement.
  Diff the public-name set before/after: nothing removed, renamed, or signature-changed; the 8
  load-bearing names (research §"Recovering Each Tier") are a hard gate.
- [ ] Confirm the net line delta is ~−1000 lines (`git diff --stat` over the three files + new
  core).
- [ ] Run full CI: `lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`. Fix any
  lint/shake/import findings (docBlame on new decls, namespace wrapping, camelCase) and rebuild
  until all green. If a file was added/removed, re-run `lake exe mk_all --module`.
- [ ] Final zero-debt check: grep all touched files for `sorry`/`admit`/new `axiom` — must be
  zero.

**Timing**: 2 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianCompleteness.lean` — thin shim +
  Brouwerian-tier corollaries.
- `Cslib/Logics/Propositional/Semantics/Algebra/PointedBrouwerianCompleteness.lean` — thin shim
  + pointed-tier `OrderBot` instance + corollaries.
- `Cslib/Logics/Propositional/Semantics/Algebra/MplPointedConservative.lean` — thin shim +
  free-bot-tier corollaries (or the unified core, depending on Phase 4 host choice).
- Any file flagged by `lake exe lint-style` / `lake shake`.

**Verification**:
- All three tier files build as shims; every recovered theorem typechecks with unchanged
  signature; the 8 load-bearing names resolve.
- `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix` all green.
- Net line delta ≈ −1000; zero `sorry`, zero new `axiom`.

## Deviations Protocol

This refactor has one high-impact structural risk (R1 instance diamond) and one moderate one
(R2 `extends` ripple). When an implementation step cannot proceed as written:

1. **Do not** leave a `sorry` or a broken build to "come back to". Stop at the last green state.
2. Apply the documented fallback for that risk:
   - R1 diamond -> Approach B self-contained `Algebra/BrouwerianLindenbaum.lean` (Phase 3).
   - R2 `extends` failure -> standalone `instance [MinimalAxioms A] : ConjImpAxioms A` (Phase 1).
3. Record the deviation in the phase's task list (check the fallback box, note why) and in the
   `/implement` summary, including the line-savings impact (Approach B saves ~250 fewer lines).
4. If neither the primary nor the fallback lands a phase green, mark that phase `[PARTIAL]`,
   commit the last green state, and leave the prior per-tier proofs **in place** (do not delete
   them) so the public surface and build stay intact.

## Testing & Validation

- [ ] `lake build` green across `Logics/Propositional/Semantics/Algebra` subtree after each phase.
- [ ] `lake test` passes (CslibTests).
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes (docBlame on all new public decls; lowerCamelCase instances).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused imports.
- [ ] EARLY diamond gate (Phase 3) passes: no two-path `BrouwerianSemilattice` defeq conflict.
- [ ] Public-surface regression: all 8 load-bearing names + every other previously-public name
  still resolve with unchanged signatures.
- [ ] Net line delta ≈ −1000 lines.
- [ ] Zero `sorry`, zero new `axiom` in all touched files.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`: `ConjImpAxioms` class;
  `MinimalAxioms extends ConjImpAxioms`.
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean`: three `ConjImpAxioms` instances.
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean`: meet-fragment lemmas
  generalized to `[ConjImpAxioms]`; `hilbertLindenbaumBSL` instance.
- Substrate host (`Algebra/Brouwerian.lean` or new `Algebra/BrouwerianBot.lean`): relocated
  `BrouwerianBotEvaluate`/`BrouwerianBotValid`/embedding lemmas + two bridge lemmas.
- Unified core (reshaped `MplPointedConservative.lean` or new
  `Algebra/BrouwerianCompletenessGeneric.lean`): 5 schema-soundness lemmas, generic truth lemma,
  generic completeness.
- Three tier files kept as thin re-export shims with preserved public surface.
- Optional `Algebra/BrouwerianLindenbaum.lean` (only if R1 fallback triggers).
- `specs/367_unify_brouwerian_completeness_triplication/summaries/01_*-summary.md` (at /implement).

## Rollback/Contingency

- Each phase is an additive, independently-buildable commit; revert the offending phase's commit
  to restore green.
- R1 (diamond): if the EARLY Phase 3 build shows a diamond, switch the BSL instance to Approach B
  (self-contained `Algebra/BrouwerianLindenbaum.lean`); the rest of the plan is unaffected (it
  only consumes the BSL instance and the generalized lemmas, regardless of where they live).
- R2 (`extends`): if any `MinimalAxioms` instance fails to elaborate, keep `MinimalAxioms` flat
  and add the standalone `instance [MinimalAxioms A] : ConjImpAxioms A`; downstream phases are
  unchanged.
- R4/R6 (relocation cycle): if relocating the evaluator causes an import cycle, place the
  substrate declarations in the lowest common ancestor module of the three tiers; rebuild the
  whole subtree.
- If any tier recovery in Phase 5 fails to typecheck, keep the original per-tier proof in place
  (do not delete it), mark that recovery deferred, and still land the generic core + the other
  tiers; the public surface stays intact.
