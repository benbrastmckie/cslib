# Implementation Plan: Task #354

- **Task**: 354 - Close the fourth conservativity step of the MPL fragment tower (MPL⟨∧,→,⊥,⊤⟩ ⊂ MPL via arbitrary-point Brouwerian completeness)
- **Status**: [IMPLEMENTING]
- **Effort**: 3.5 hours
- **Dependencies**: 353 (provides `ConjImpBotMinAxiom`, `toMinPropAxiom`, `mem_implyK/mem_implyS` witnesses)
- **Research Inputs**: reports/01_arbitrary-point-completeness.md
- **Artifacts**: plans/01_arbitrary-point-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, CONTRIBUTING.md, ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Task 354 closes the fourth step of the MPL fragment tower, mirroring the IPL chain
`Hilbert → Brouwerian → pointed-Brouwerian → GHA`, with the sole divergence that `⊥` is a
**free** distinguished element rather than the `OrderBot` least element. The mathematics is
sound and low-risk: the algebraic core (free-bot evaluator, free-bot embedding lemma, and the
GHA→BrouwerianBot bridge) was already PROTOTYPED and compiled green (665 jobs) during research.
The implementation creates ONE new file
`Cslib/Logics/Propositional/Semantics/Algebra/MplPointedConservative.lean` (free-bot evaluator,
embedding lemma, soundness, and a `ConjImpBotMin` Lindenbaum completeness that is a verbatim copy
of `PointedBrouwerianCompleteness.lean` with the `OrderBot` block deleted and
`ConjImpBotAxiom → ConjImpBotMinAxiom`), then APPENDS the two chain theorems
(`hilbertMplConservativeOverConjImpBot_direct`, `mplAxiom_iff_conjImpBotMinAxiom`) to
`MplConservativeChain.lean`, updates the `Cslib.lean` barrel, and verifies with a scoped build.

### Research Integration

The research report drives every phase of this plan. Key findings encoded here:

- **`ConjImpBotMinAxiom` = `ConjImpAxiom` axioms + free `⊥`**: the same five axiom constructors
  (`implyK`, `implyS`, `andI`, `andE1`, `andE2`), NO `efq`, NO bot-specific axiom. Therefore `⊥`
  is uninterpreted and its semantic image is a **free `bot_val : H`** ranging over the whole
  algebra — exactly what `GHAValid` already quantifies over (`Algebra.lean:126`). `OrderBot` is
  DROPPED because there is no `efq` to validate.
- **Plain `LowerSet` suffices** (not `NonemptyLowerSet`): with a free `bot_val`,
  `LowerSet.Iic bot_val` is an ordinary element; the `bot` case of the commutation lemma closes
  by `rfl`. `NonemptyLowerSet` existed in the IPL tower only to satisfy `Iic ⊥ = ⊥`.
- **Compiled prototype** (deleted after verification, must NOT appear in diff): `BrouwerianBotEvaluate`,
  `BrouwerianBotValid`, `iicBrouwerianBotEvaluateEqAlgEvaluate`, `brouwerianBotEmbeddingLemma`,
  `GHAValid_implies_BrouwerianBotValid_direct` — all type-checked. Phase 1 reconstructs these.
- **Completeness template**: `PointedBrouwerianCompleteness.lean` lines 152–547, copied verbatim
  with `ConjImpBotAxiom → ConjImpBotMinAxiom` and the `OrderBot` block (lines 414–433) deleted.
- **Universe handling**: `{Atom : Type u}` with `GHAValid.{u, u}` / `BrouwerianBotValid.{u, u}`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found / not provided in delegation context. This task advances the MPL fragment
tower (`MPL⟨→,⊤⟩ ⊂ MPL⟨∧,→,⊤⟩ ⊂ MPL⟨∧,→,⊥,⊤⟩ ⊂ MPL`) to parallel the existing IPL chain.

## Goals & Non-Goals

**Goals**:
- Create `MplPointedConservative.lean` with the free-bot evaluator (`BrouwerianBotEvaluate`),
  validity predicate (`BrouwerianBotValid`), embedding lemma (`brouwerianBotEmbeddingLemma`),
  soundness lemmas, and `ConjImpBotMin` Lindenbaum completeness (`conjImpBotMin_brouwerianBot_complete`).
- Append `hilbertMplConservativeOverConjImpBot_direct` and `mplAxiom_iff_conjImpBotMinAxiom` to
  `MplConservativeChain.lean`.
- Update the `Cslib.lean` barrel for the new file.
- Pass the scoped green gate: build of the two touched propositional modules + scoped lint/shake.

**Non-Goals**:
- Modifying `Algebra.lean`, `Defs.lean`, `SemanticConsequence.lean`, or any `Temporal/*` file
  (in-flight task-343 work). ADD declarations only.
- Fixing the 11 PRE-EXISTING Temporal subtree failures (out of scope; not part of the green gate).
- Introducing `NonemptyLowerSet` or any `OrderBot`-based semantics for this fragment.
- Any new mathematics beyond the compiled prototype + mechanical copy of an existing proof.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `BrouwerianSemilattice.toHilbertAlgebra` Preorder diamond reappears on the new chain theorem | M | M | Place the new GHA-bridge theorem inside the existing `attribute [-instance] ...` suppressed region in `MplConservativeChain.lean` (line 121 onward), or add its own bracket. Verify with scoped build. |
| Lindenbaum copy drifts from template (stale `ConjImpBotAxiom` refs, leftover `OrderBot` block) | M | M | Mechanical search-replace `ConjImpBotAxiom → ConjImpBotMinAxiom`; explicitly delete OrderBot block (template lines 414–433); confirm `mem_implyK/mem_implyS` witnesses resolve for the new predicate. |
| Lint failures (docBlame, simpNF, lowerCamelCase, instance namespacing) | L | M | Add docstrings to every new `def`/`theorem`; Prop-valued → `theorem`/`lemma`; verify `@[simp]` LHS normal form; wrap instances in a namespace. Run scoped `lake exe lint-style`. |
| Accidental edit to a forbidden in-flight file | H | L | ADD-only discipline; touch exactly `MplPointedConservative.lean` (new), `MplConservativeChain.lean` (append), `Cslib.lean` (barrel). Confirm `git status` before commit. |
| Truth-lemma `bot` case fails to rewrite `BrouwerianBotEvaluate canonicalV (mk ⊥) .bot = mk ⊥` | M | L | Include `@[simp] BrouwerianBotEvaluate_bot` returning `bot_val`; `bot` case is definitional (mirrors `pointedBrouwerianCanonicalV_spec`). |
| Barrel left out of sync (missing public import) | L | L | Run `lake exe mk_all --module` after creating File 1, or insert the alphabetically-correct `public import` line manually; rebuild barrel. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |

Phases within the same wave can execute in parallel. Here the chain is strictly sequential:
the chain theorems (Phase 2) depend on the new file's declarations (Phase 1), and verification
(Phase 3) gates on both.

### Phase 1: Create `MplPointedConservative.lean` (evaluator + embedding + soundness + completeness) [COMPLETED]

**Goal**: Produce the new module holding the free-bot evaluator, its simp lemmas, the validity
predicate, the embedding lemma, soundness, and the `ConjImpBotMin` Lindenbaum completeness.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra/MplPointedConservative.lean` with
      imports: `FreeJoinCompletion`, `HilbertCompleteness`, `PointedBrouwerianCompleteness`,
      `FragmentAxioms` (the exact set the prototype compiled with).
- [ ] Define `BrouwerianBotEvaluate v bot_val` (`atom ↦ v x`, `bot ↦ bot_val`, `imp ↦ ⇨`,
      `and ↦ ⊓`, `or ↦ ⊤`) with `@[simp]` lemmas
      `BrouwerianBotEvaluate_atom/bot/imp/and/or` (mirror `Brouwerian.lean:67–100`,
      `bot ↦ bot_val`). Include the `bot` simp lemma returning `bot_val` (needed for the truth lemma).
- [ ] Define `BrouwerianBotValid φ := ∀ (H) [BrouwerianSemilattice H] (v) (bot_val), BrouwerianBotEvaluate v bot_val φ = ⊤`.
- [ ] Prove `iicBrouwerianBotEvaluateEqAlgEvaluate` (commutation: `AlgEvaluate (Iic ∘ v) (Iic bot_val) φ = Iic (BrouwerianBotEvaluate v bot_val φ)` for or-free φ) by induction — `bot` case `rfl`, `imp` via `(iicHimp _ _).symm`, `and` via `(LowerSet.Iic_inf _ _).symm`.
- [ ] Prove `brouwerianBotEmbeddingLemma` (or-free) via the commutation lemma + `LowerSet.Iic_top` + `LowerSet.Iic_injective`.
- [ ] Add soundness: `conjImpBotMin_brouwerianBot_axiom_sound`, `conjImpBotMin_brouwerianBot_soundness`, `conjImpBotMin_brouwerianBot_soundness_derivable` — copy `PointedBrouwerianCompleteness.lean:80–150`, five axiom cases identical to `BrouwerianCompleteness.lean:72–112` (no `efq` case; `bot ↦ bot_val` needs no bound).
- [ ] Copy the Lindenbaum construction `PointedBrouwerianCompleteness.lean:152–489` **verbatim** with `ConjImpBotAxiom → ConjImpBotMinAxiom` and **delete the OrderBot block** (template lines 414–433): `ConjImpBotMinEquiv`, setoid, quotient algebra, BSL instance, top `[⊥ → ⊥]`, `...Mk_eq_top_iff`, canonical valuation. Confirm `ConjImpBotMinAxiom.mem_implyK/mem_implyS` witnesses resolve.
- [ ] Prove truth lemma + completeness: `conjImpBotMinCanonicalV_spec` (or-free; `bot_val := mk Proposition.bot`), `conjImpBotMin_brouwerianBot_complete : φ.IsOrFree → BrouwerianBotValid φ → Derivable ConjImpBotMinAxiom φ`, `conjImpBotMin_brouwerianBot_iff`. The `bot` case of the truth lemma gives `BrouwerianBotEvaluate canonicalV [⊥] .bot = [⊥] = mk Proposition.bot` (definitional; analogue of `pointedBrouwerianCanonicalV_spec` line 509).
- [ ] Add docstrings to every new `def`/`theorem`/`lemma`; use lowerCamelCase; wrap instances in a namespace.

**Timing**: 1.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/MplPointedConservative.lean` (NEW) - all declarations above.

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplPointedConservative` succeeds.
- The evaluator/embedding/bridge match the compiled prototype shape from the research report.
- No `sorry`, no `OrderBot` instance, no `NonemptyLowerSet`.

---

### Phase 2: Append chain theorems to `MplConservativeChain.lean` + barrel update [COMPLETED]

**Goal**: Add the two chain theorems and the biconditional, import the new file, and sync the barrel.

**Tasks**:
- [ ] Add an import of `Cslib.Logics.Propositional.Semantics.Algebra.MplPointedConservative` to `MplConservativeChain.lean`.
- [ ] Add `GHAValid_implies_BrouwerianBotValid_direct {Atom : Type u} {φ} (hOF : φ.IsOrFree = true) (h : GHAValid.{u, u} φ) : BrouwerianBotValid.{u, u} φ` (move here or re-export from File 1), placing it **inside the existing `attribute [-instance] BrouwerianSemilattice.toHilbertAlgebra` suppressed region** (line 121–160) to avoid the Preorder diamond on `LowerSet.Iic`.
- [ ] Add `hilbertMplConservativeOverConjImpBot_direct {Atom : Type u} {φ} (hOF : φ.IsOrFree = true) (h : Derivable (@MinPropAxiom Atom) φ) : Derivable (@ConjImpBotMinAxiom Atom) φ := conjImpBotMin_brouwerianBot_complete hOF (GHAValid_implies_BrouwerianBotValid_direct hOF (MPL.hilbert_alg_complete.mp h))`.
- [ ] Add `mplAxiom_iff_conjImpBotMinAxiom {Atom : Type u} {φ} (hOF : φ.IsOrFree = true) : Derivable (@MinPropAxiom Atom) φ ↔ Derivable (@ConjImpBotMinAxiom Atom) φ := ⟨hilbertMplConservativeOverConjImpBot_direct hOF, fun ⟨d⟩ => ⟨liftDerivationTree (fun _ hψ => hψ.toMinPropAxiom) d⟩⟩` (backward direction via task-353 `ConjImpBotMinAxiom.toMinPropAxiom`).
- [ ] Add docstrings to the two public chain theorems.
- [ ] Update barrel: run `lake exe mk_all --module`, or insert `public import Cslib.Logics.Propositional.Semantics.Algebra.MplPointedConservative` in alphabetical position in `Cslib.lean` (near lines 441, 455–458).

**Timing**: 0.75 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` (APPEND) - import + three theorems.
- `Cslib.lean` (barrel) - new public import for `MplPointedConservative`.

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain` succeeds.
- The `attribute [-instance]` bracket still wraps the GHA-bridge theorem (no diamond error).
- Barrel includes the new module (`lake exe mk_all --module` reports no changes on re-run).

---

### Phase 3: Scoped verification (build + CI lint/shake on touched modules) [COMPLETED]

**Goal**: Pass the scoped green gate on the two touched propositional modules.

**Tasks**:
- [ ] Scoped build of both modules:
      `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplPointedConservative Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain`.
- [ ] `lake exe checkInitImports`.
- [ ] `lake exe lint-style` (scoped to the touched modules / new file).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` on the new file `MplPointedConservative.lean`.
- [ ] Confirm `git status` shows ONLY: `MplPointedConservative.lean` (new), `MplConservativeChain.lean` (modified), `Cslib.lean` (modified). NO forbidden files touched.
- [ ] NOTE: full `lake build` / `lake test` has 11 PRE-EXISTING failures in the Temporal subtree (task-343 in-flight, out of scope). The green gate is the SCOPED build of the touched modules, NOT the full build.

**Timing**: 1 hour

**Depends on**: 1, 2

**Files to modify**:
- None (verification only).

**Verification**:
- Scoped build green; `checkInitImports`, `lint-style`, `shake` clean for the new file.
- `git status` confirms no forbidden file (`Algebra.lean`, `Defs.lean`, `SemanticConsequence.lean`, `Temporal/*`) is modified.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplPointedConservative` passes.
- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain` passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes for the new/touched modules.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no issues on the new file.
- [ ] `hilbertMplConservativeOverConjImpBot_direct` and `mplAxiom_iff_conjImpBotMinAxiom` type-check and contain no `sorry`.
- [ ] `git status` shows exactly three touched files; no forbidden in-flight files modified.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/MplPointedConservative.lean` (NEW) — free-bot evaluator, embedding lemma, soundness, `ConjImpBotMin` Lindenbaum completeness.
- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` (MODIFIED) — `GHAValid_implies_BrouwerianBotValid_direct`, `hilbertMplConservativeOverConjImpBot_direct`, `mplAxiom_iff_conjImpBotMinAxiom`.
- `Cslib.lean` (MODIFIED) — barrel public import for the new module.
- Execution summary: `summaries/01_arbitrary-point-completeness-summary.md` (produced at implementation time).

## Rollback/Contingency

All changes are ADD-only and confined to three files. To revert:
- `git checkout -- Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean Cslib.lean` and delete `Cslib/Logics/Propositional/Semantics/Algebra/MplPointedConservative.lean`.
No forbidden files are touched, so a rollback cannot disturb in-flight task-343 work. If the
Lindenbaum copy proves harder than the mechanical template suggests, fall back to keeping ALL new
declarations (including the two chain theorems) in `MplPointedConservative.lean` and leaving
`MplConservativeChain.lean` untouched (research report notes this is viable), at the cost of
slightly worse co-location.
