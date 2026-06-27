# Implementation Plan: Task #372 - Disjunctive-Implicational Fragment IPL⟨∨,→,⊤⟩

- **Task**: 372 - Disjunctive-implicational fragment `OrImpAxiom` + `HilbertOrImp` (+ conservativity)
- **Status**: [NOT STARTED]
- **Effort**: 13 hours (core ~3.25h; conservativity ~9.75h, high-variance: realistic ceiling 22h)
- **Dependencies**: Task 345 (IsMinimal + MinimalAxioms↔inclusion bridge) — completed
- **Research Inputs**: specs/372_or_imp_disjunctive_implicational_fragment/reports/01_or-imp-fragment-research.md
- **Artifacts**: plans/01_or-imp-fragment.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Add the ninth (and final missing) vertex of the propositional fragment lattice: the
disjunctive-implicational fragment IPL⟨∨,→,⊤⟩. The **core deliverable** (Phases 1–4) is a
near-mechanical mirror of the existing `ConjImpAxiom`/`HilbertConjImp` blocks: a new
`OrImpAxiom` inductive (K, S, orI1, orI2, orE), its subsumption into `MinPropAxiom`,
deduction-theorem witnesses and instance, substitution closure, fragment-predicate
compatibility lemmas backed by one new syntactic predicate `Proposition.IsAndBotFree`, and
the `Propositional.HilbertOrImp` opaque tag with `InferenceSystem`/`ModusPonens`/`HasAxiom*`/
`MinimalHilbert` instances. The core is sorry-free and introduces zero new axioms; coherence
with the task-345 strength substrate is carried entirely by the axiom-level subsumption
`OrImpAxiom → MinPropAxiom` (OrImp deliberately gets no `MinimalAxioms`/`ConjImpAxioms`
instance — it lacks the conjunction axioms).

The **conservativity step** (Phases 5–10, user opted IN) is genuinely heavy. The conjunctive
analogue `ConjImpConservative.lean` eliminates the *missing* connective (`∨`) by embedding a
`BrouwerianSemilattice` into `LowerSet B` (the free *join* completion) preserving `⊓,⇨,⊤`.
The disjunctive dual must eliminate `∧` while preserving `∨,⇨,⊤`, which requires (a) a dual
algebraic semantics for OrImp (a join-semilattice with relative implication; no `⊓`), (b) its
soundness + completeness, and (c) a **free *meet* completion** that does not exist in the
codebase. Because Heyting implication is not self-dual, the meet completion's `⇨`-preservation
is the real mathematical risk — it is **not** a symmetric copy of `FreeJoinCompletion.lean`.
A feasibility spike (Phase 6) gates the heavy phases with an explicit go/no-go.

**Definition of done**: core (Phases 1–4) lands sorry-free with zero new axioms and full CI
green; conservativity (Phases 5–10) lands the cheap independence lemma plus, conditional on
the Phase-6 spike, the full `hilbertIplConservativeOverOrImp` theorem wired into the
conservativity chain — or, if the spike proves the construction infeasible without a sorry, the
conservativity proof phases are marked [BLOCKED] (never bridged with sorry/axiom) while the
core and groundwork still ship.

### Research Integration

Plan follows the research report's reuse-first findings and exact mirror map directly:
- Mirror map (report §4): `OrImpAxiom` on `ConjImpAxiom` (FragmentAxioms.lean:59–74); subsumption
  on 102–109; witnesses 116–125; `subst_preserves_*` 148–158; compatibility lemmas 175–212;
  `*_hasDeductionTheorem` 235–237.
- New predicate `IsAndBotFree` (report §3) in FragmentPredicates.lean with `imp_*`/`or_*`
  closure + `subst_preserves_*` + optional `IsImpTopOnly_implies_IsAndBotFree`.
- Instances (report §4) modelled on `HilbertConjImp` (Instances.lean:38–83); opaque tag beside
  `HilbertImp` (ProofSystem.lean:503); reuse existing `HasAxiomOrI1/OrI2/OrE` and `MinimalHilbert`
  (no new typeclasses).
- Conservativity assessed (report §5) as optional/heavy needing a non-symmetric free-meet
  completion; `coe_AlgEvaluate_andBotFree` flagged as cheap groundwork (report §3).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided in delegation context; roadmap consultation skipped. (Conceptually
this task closes the propositional fragment-lattice work, but no ROADMAP.md was supplied.)

## Goals & Non-Goals

**Goals**:
- Sorry-free, zero-new-axiom `OrImpAxiom` fragment mirroring the existing fragment blocks.
- New `Proposition.IsAndBotFree` predicate with closure + substitution lemmas.
- `Propositional.HilbertOrImp` tag + `InferenceSystem`/`ModusPonens`/`HasAxiom*`/`MinimalHilbert`.
- Coherence with task-345 substrate via the axiom-level subsumption only.
- Cheap independence groundwork `coe_AlgEvaluate_andBotFree`.
- Full conservativity theorem for IPL⟨∨,→,⊤⟩ (free-meet completion + dual completeness), wired
  into the conservativity chain — conditional on the Phase-6 feasibility gate.
- All CI gates green: `lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake`.

**Non-Goals**:
- No `MinimalAxioms`/`ConjImpAxioms` instance for OrImp (it lacks conjunction axioms — by design).
- No new bundled proof-system class (`MinimalHilbert` over K/S/MP suffices).
- No sorry/axiom bridge for conservativity under any circumstance.
- No changes to other fragments' existing theorems beyond additive chain wiring.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Free-meet completion does not preserve Heyting `⇨` (non-self-dual) | H | M | Phase 6 feasibility spike is an explicit go/no-go gate before any heavy investment; if infeasible, mark Phases 7–10 [BLOCKED], keep core + groundwork |
| Conservativity effort balloons (novel algebra) beyond estimate | M | H | Conservativity split into small phases 5–10; core (1–4) committed first so it ships regardless; honest 13–22h range stated |
| `IsAndBotFree` mishandles derived `⊤ := imp bot bot` | M | L | Predicate marks `bot=false` (matches `IsImpTopOnly`); fragment axioms K/S/orI1/orI2/orE never contain literal `⊥`/`⊤`, so compatibility lemmas only feed `imp`/`or` nodes (report §3) |
| Instance placement (Instances.lean vs FragmentInstances.lean) inconsistent | L | M | Place OrImp instances in `ProofSystem/Instances.lean` beside ConjImp/Imp; confirm `Cslib.lean` imports it (already does) |
| Accidental writes to main repo instead of worktree | M | L | All paths absolute under the worktree; final CI run scoped to worktree checkout |
| New axiom introduced inadvertently | H | L | `lean_verify` axiom check on every new top-level decl; CI gate in Phases 4 and 10 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 6 | -- |
| 2 | 2, 5 | 1 |
| 3 | 3, 7 | 2 (and 6 for 7) |
| 4 | 4, 8 | 1,2,3 (4); 7 (8) |
| 5 | 9 | 6, 8 |
| 6 | 10 | 4, 5, 9 |

Phases within the same wave can execute in parallel. **Recommended sequencing**: complete and
commit the core (Phases 1–4) before investing in conservativity (5–10); the wave table shows
theoretical parallelism, but serializing core-before-conservativity de-risks the heavy work and
guarantees the core ships. Phase 6 (spike) may be run early in parallel to inform go/no-go.

---

### Phase 1: New `IsAndBotFree` syntactic predicate [COMPLETED]

**Goal**: Add the fragment-naming predicate that permits `or`/`imp` and forbids `and`/`bot`,
with its connective-closure and substitution lemmas.

**Tasks**:
- [ ] Add `def Proposition.IsAndBotFree : Proposition Atom → Bool` to
  `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` (atom=true, bot=false,
  imp=both, and=false, or=both) — model on `IsOrFree`/`IsImpTopOnly`.
- [ ] Add connective-closure lemmas `imp_isAndBotFree`, `or_isAndBotFree` (model on
  `imp_isOrFree`/`and_isOrBotFree`).
- [ ] Add `subst_preserves_isAndBotFree` (model on `subst_preserves_isOrFree`).
- [ ] Add optional subsumption `IsImpTopOnly_implies_IsAndBotFree` (imp-top-only ⊆ and-bot-free).
- [ ] Docstrings on every new decl (docBlame); Prop-valued items are `theorem`/`lemma` (defLemma).

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` — new predicate + lemmas.

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates` succeeds.
- `#eval`/`#check` smoke test that `(p.or q).imp r |>.IsAndBotFree` reduces as expected.

---

### Phase 2: `OrImpAxiom` inductive, subsumption, witnesses, substitution, compatibility, deduction theorem [COMPLETED]

**Goal**: Add the OrImp axiom block to `FragmentAxioms.lean`, mirroring the `ConjImpAxiom` block.

**Tasks**:
- [ ] `inductive OrImpAxiom` with `implyK`, `implyS`, `orI1`, `orI2`, `orE` (orI*/orE shapes from
  `MinPropAxiom`, Axioms.lean:143–149) — model on `ConjImpAxiom` (59–74).
- [ ] `ImpAxiom.toOrImpAxiom` (optional but natural, ImpAxiom ⊆ OrImpAxiom) — model on
  `ImpAxiom.toConjImpAxiom` (95–99).
- [ ] `OrImpAxiom.toMinPropAxiom` (required subsumption, 5-case `cases … exact .ctor`) — model on
  `ConjImpAxiom.toMinPropAxiom` (102–109).
- [ ] `OrImpAxiom.mem_implyK` / `mem_implyS` witnesses — model on 116–125.
- [ ] `subst_preserves_orImpAxiom` with orI1/orI2/orE subst cases — model on 148–158.
- [ ] Compatibility lemmas `orImpAxiom_{implyK,implyS,orI1,orI2,orE}_isAndBotFree` using
  `imp_isAndBotFree`/`or_isAndBotFree` — model on 175–212.
- [ ] `orImpAxiom_hasDeductionTheorem := hasDeductionTheorem mem_implyK mem_implyS` — model on
  235–237.
- [ ] Docstrings on all constructors/lemmas; match surrounding `subst_preserves_*` naming.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` — OrImp block.

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` succeeds.
- `lean_verify` on `OrImpAxiom.toMinPropAxiom`, `orImpAxiom_hasDeductionTheorem`: no new axioms.

---

### Phase 3: `HilbertOrImp` opaque tag + proof-system instances [COMPLETED]

**Goal**: Add the tag type and the inference-system/axiom instances making `HilbertOrImp` a
usable Hilbert system.

**Tasks**:
- [ ] Add `opaque Propositional.HilbertOrImp : Type := Empty` beside `HilbertImp`
  (`Cslib/Foundations/Logic/ProofSystem.lean`:~503).
- [ ] In `Cslib/Logics/Propositional/ProofSystem/Instances.lean`, new `section OrImpInstances`
  (model on `HilbertConjImp` 38–83): `InferenceSystem` via `DerivationTree OrImpAxiom [] φ`,
  `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomOrI1`, `HasAxiomOrI2`,
  `HasAxiomOrE`, `MinimalHilbert`.
- [ ] Confirm placement: OrImp instances go in `ProofSystem/Instances.lean` (where Imp/ConjImp
  fragment instances live); verify `Cslib.lean` imports it (it does).
- [ ] Wrap instances in `namespace Cslib.Logic.PL`; tag under `Propositional.` namespace.

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/ProofSystem.lean` — opaque tag.
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` — OrImp instances.

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.Instances` succeeds.
- Instance-resolution smoke check: `#synth MinimalHilbert (Propositional.HilbertOrImp)` (or
  equivalent `example`) resolves.

---

### Phase 4: Core CI gate [COMPLETED]

**Goal**: Confirm the core deliverable is sorry-free, axiom-clean, and passes the full CI suite.

**Tasks**:
- [ ] `lake build` (full project).
- [ ] `lake test`.
- [ ] `lake exe checkInitImports`.
- [ ] `lake exe lint-style` (and `lake lint` for environment linters: docBlame/defLemma/topNamespace).
- [ ] `lake exe mk_all --module` only if any new file was added (none expected in core).
- [ ] `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] `lean_verify` axiom audit on all new core decls — confirm zero new axioms.
- [ ] Commit core: `task 372 phase 1-4: OrImp fragment core (axioms, predicate, instances)`.

**Timing**: 0.5 hours

**Depends on**: 1, 2, 3

**Files to modify**: none (verification + commit only).

**Verification**:
- All five CI gates green; axiom audit clean.

---

### Phase 5: `coe_AlgEvaluate_andBotFree` independence lemma (groundwork) [COMPLETED]

**Goal**: Land the cheap conservativity groundwork lemma (dual of `coe_AlgEvaluate_orFree`).

**Tasks**:
- [ ] Add `coe_AlgEvaluate_andBotFree` to `FragmentPredicates.lean` — for and-bot-free formulas,
  `AlgEvaluate` depends only on `⊔`, `⇨`, `⊤`; model directly on `coe_AlgEvaluate_orFree`
  (FragmentPredicates.lean:230–248), swapping the `and`/`or` excluded cases.
- [ ] Docstring; structural-induction proof excluding `and`/`bot` via `IsAndBotFree`.

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` — independence lemma.

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates` succeeds.
- `lean_verify`: no new axioms.

---

### Phase 6: Free-meet-completion feasibility spike (GO/NO-GO gate) [COMPLETED]

**Goal**: Determine, before heavy investment, whether a free *meet* completion preserving
`⊔,⇨,⊤` is constructible sorry-free in this codebase — the one genuinely novel, non-symmetric
piece of the conservativity proof.

**Decision: NO-GO**

**Obstruction (precise)**: The natural dual embedding `UpperSet.Ici : B → UpperSet B` does NOT
preserve Heyting implication `⇨`.

In `FreeJoinCompletion.lean`, `iicHimp` proves:
```
LowerSet.Iic (a ⇨ b) = LowerSet.Iic a ⇨ LowerSet.Iic b
```
The proof uses the adjunction `c ⊓ a ≤ b ↔ c ≤ a ⇨ b` in a BrouwerianSemilattice.

The dual attempt: `UpperSet.Ici (a ⇨ b) = UpperSet.Ici a ⇨ UpperSet.Ici b` in `UpperSet B`.

**Counterexample**: In B = {⊥, a, b, ⊤} with a and b incomparable and a ⊓ b = ⊥:
- `a ⇨ b = ⊥` (since a ⊓ a = a ≰ b, so a ⇨ b = ⊥)
- `UpperSet.Ici ⊥ = UpperSet B` (all upsets)
- `UpperSet.Ici a ⇨ UpperSet.Ici b` in `UpperSet B`:
  = {U | ↑(U) ∩ ↑a ⊆ ↑b} = {x | ∀ y ≥ x, y ≥ a → y ≥ b}
  Since ⊥ → a → ⊤ and ⊥ → b → ⊤ with a ≱ b, element ⊥ is NOT in this set
  (take y = a ≥ ⊥, but a ≱ b). So ⊥ ∉ `UpperSet.Ici a ⇨ UpperSet.Ici b`.
- But ⊥ ∈ `UpperSet.Ici ⊥ = UpperSet B`. CONTRADICTION.

**Root cause**: Heyting implication `⇨` is the right adjoint of `⊓` (meet), not of `⊔` (join).
Its dual (co-Heyting subtraction `\`) is the right adjoint of `⊔` in the opposite lattice, and
`UpperSet B` naturally carries co-Heyting structure, NOT Heyting. There is no simple
"symmetric" free-completion that adds `⊓` to a join-implication structure while preserving `⇨`.

**Consequence**: Phases 7–10 are BLOCKED. The conservativity theorem for IPL⟨∨,→,⊤⟩ requires
a more sophisticated proof strategy (cut elimination, Rieger–Nishimura lattice, or MacNeille
completion with explicit `⇨`-preservation analysis), none of which are mechanical mirrors of
FreeJoinCompletion.lean. This is NOT a Lean formalization problem — it is a genuine mathematical
obstruction.

The core deliverable (Phases 1–4) and the groundwork independence lemma (Phase 5) ship cleanly
and sorry-free.

**Tasks**:
- [x] Study `FreeJoinCompletion.lean` (`LowerSet.Iic` preserving `⊓,⇨,⊤` via `iicHimp`)
- [x] Identify the dual carrier: `UpperSet B` with `UpperSet.Ici` (principal upset)
- [x] Critically assess whether `UpperSet.Ici` preserves `⇨` — NO (counterexample above)
- [x] **Decision recorded**: NO-GO; Phases 7–10 [BLOCKED]

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- This plan file (record GO/NO-GO decision and blocker note).

**Verification**:
- Written NO-GO decision with candidate carrier, precise obstruction, and counterexample.

---

### Phase 7: Dual algebraic semantics for OrImp + soundness [BLOCKED]

**BLOCKER** (Phase 7):
- **What failed**: Phase 6 feasibility spike returned NO-GO — the free meet completion that
  would provide the dual algebraic structure cannot be built sorry-free using `UpperSet.Ici`.
- **What was tried**: Analysis of `UpperSet.Ici` as the dual of `LowerSet.Iic`; proof that
  `UpperSet.Ici (a ⇨ b) ≠ UpperSet.Ici a ⇨ UpperSet.Ici b` via counterexample.
- **Why it's stuck**: Heyting implication is the right adjoint of `⊓`, not of `⊔`. No symmetric
  free-completion preserving both `⊔` and `⇨` exists via UpperSet.
- **What is needed**: A more sophisticated approach (cut elimination, MacNeille completion with
  explicit `⇨`-preservation analysis, or Rieger–Nishimura lattice construction). This requires
  new mathematical infrastructure not present in the codebase.
- **Prohibited workarounds**: Do NOT use `sorry`, `def X := True`, or any vacuous placeholder.

**Goal**: Define the dual algebraic structure for IPL⟨∨,→,⊤⟩ (join-semilattice with relative
implication, no `⊓`), its `*Evaluate`/`*Valid`, and OrImp soundness.

**Tasks**:
- [ ] New file (e.g. `Cslib/Logics/Propositional/Semantics/Algebra/CoBrouwerian.lean` — name
  TBD to match conventions) defining the dual structure + `Evaluate`/`Valid`, model on
  `Brouwerian.lean` (110 lines) and `PointedBrouwerian.lean`.
- [ ] Soundness `orImp_<dual>_soundness_derivable : Derivable OrImpAxiom φ → <Dual>Valid φ`,
  model on `conjImp_brouwerian_soundness_derivable` (BrouwerianCompleteness.lean:67,132).
- [ ] `import Cslib.Init` header; docstrings; namespace `Cslib.Logic.PL`.

**Timing**: 2 hours

**Depends on**: 2, 6 (GO)

**Files to modify**:
- New file under `Cslib/Logics/Propositional/Semantics/Algebra/` (dual structure + soundness).

**Verification**:
- `lake build` of the new module succeeds; `lean_verify` soundness: no new axioms.

---

### Phase 8: OrImp completeness w.r.t. the dual structure [BLOCKED]

**BLOCKER**: Phase 6 NO-GO. No dual algebraic structure has been established. Cannot proceed
until Phase 7 is unblocked.

**Goal**: Prove `orImp_<dual>_complete` (and the `iff`), restricted to `IsAndBotFree` formulas,
via the generic Lindenbaum-algebra route.

**Tasks**:
- [ ] Add `orImp_<dual>_complete : IsAndBotFree φ → <Dual>Valid φ → Derivable OrImpAxiom φ` and
  `orImp_<dual>_iff`, model on `conjImp_brouwerian_complete`/`_iff`
  (BrouwerianCompleteness.lean:151) instantiating at the generic
  `HilbertLindenbaumAlgebra OrImpAxiom` (mirror `BrouwerianCompletenessGeneric.lean`, 250 lines).
- [ ] Reuse existing `HilbertLindenbaum`/`HilbertLindenbaumRel` infrastructure where the dual
  structure admits it; add dual-specific glue only as needed.

**Timing**: 2 hours

**Depends on**: 7

**Files to modify**:
- The Phase-7 dual module (or a paired `<Dual>Completeness.lean`).

**Verification**:
- `lake build` succeeds; `lean_verify` completeness: no new axioms.

---

### Phase 9: Free meet completion + embedding lemma [BLOCKED]

**BLOCKER**: Phase 6 NO-GO. The free meet completion cannot be built sorry-free via
`UpperSet.Ici`. Cannot proceed until the mathematical obstruction is resolved.

**Goal**: Build the free-meet completion (dual of `FreeJoinCompletion.lean`) and the embedding
lemma transferring dual validity to Heyting-algebra validity on the and-bot-free fragment.

**Tasks**:
- [ ] New file `Cslib/Logics/Propositional/Semantics/Algebra/FreeMeetCompletion.lean` with the
  carrier and principal-embedding map identified in Phase 6.
- [ ] `<emb>Himp` (`⇨`-preservation, dual of `iicHimp`), `<emb>EqTopIff`, the commutation lemma
  (dual of `iicBrouwerianEvaluateEqAlgEvaluate`, restricted via `IsAndBotFree`), and the
  embedding lemma (dual of `brouwerianEmbeddingLemma`).
- [ ] `import Cslib.Init`; docstrings; references mirroring FreeJoinCompletion.lean's bibliography.

**Timing**: 2 hours

**Depends on**: 6 (GO), 8

**Files to modify**:
- New file `.../Algebra/FreeMeetCompletion.lean`.

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.FreeMeetCompletion` succeeds;
  `lean_verify`: no new axioms (no sorry in the `⇨`-preservation proof).

---

### Phase 10: Conservativity theorem + chain wiring + final CI [BLOCKED]

**BLOCKER**: Phases 7–9 blocked. The full conservativity theorem cannot be assembled until the
free meet completion and dual algebraic semantics are established without sorry.

**Goal**: Assemble the end-to-end conservativity theorem, ND corollary, wire into the
conservativity chain, and pass full CI.

**Tasks**:
- [ ] New file `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean` (model on
  `ConjImpConservative.lean`, 152 lines): `hilbertIplConservativeOverOrImp` (using
  `IPL.hilbert_alg_complete`, the Phase-9 embedding lemma, and Phase-8 completeness),
  `derivableOrImpOfDerivableInt` subsumption (via `OrImpAxiom.toMinPropAxiom.toIntPropAxiom`),
  the `_iff`, and the ND corollary `ipl_conservative_over_orImp`.
- [ ] Wire into `ConservativeChain.lean` (additive: new theorem(s), follow existing pattern).
- [ ] `lake exe mk_all --module` to register new files in `Cslib.lean`.
- [ ] Full CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake lint`, `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] `lean_verify` axiom audit across all new conservativity decls — zero new axioms.
- [ ] Commit: `task 372 phase 5-10: OrImp conservativity (free-meet completion + theorem)`.

**Timing**: 1.5 hours

**Depends on**: 4, 5, 9

**Files to modify**:
- New `.../Algebra/OrImpConservative.lean`; `.../Algebra/ConservativeChain.lean`; `Cslib.lean`.

**Verification**:
- All CI gates green; axiom audit clean; `hilbertIplConservativeOverOrImp` and
  `ipl_conservative_over_orImp` type-check sorry-free.

## Testing & Validation

- [ ] `lake build` (full project) — green.
- [ ] `lake test` — green (add a smoke `#check`/instance-resolution line if no fragment test exists).
- [ ] `lake exe checkInitImports` — all new files import `Cslib.Init`.
- [ ] `lake exe lint-style` and `lake lint` — clean (docBlame/defLemma/defsWithUnderscore/topNamespace).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — imports minimal.
- [ ] `lean_verify` on every new top-level decl — **zero new axioms, zero sorry**.
- [ ] Subsumption sanity: `OrImpAxiom.toMinPropAxiom` covers all 5 constructors.
- [ ] Instance sanity: `MinimalHilbert Propositional.HilbertOrImp` resolves.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` (modified: `IsAndBotFree`
  + closure/subst lemmas + `coe_AlgEvaluate_andBotFree`).
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` (modified: `OrImpAxiom` block).
- `Cslib/Foundations/Logic/ProofSystem.lean` (modified: `HilbertOrImp` opaque tag).
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` (modified: OrImp instances).
- New conservativity modules (conditional on Phase-6 GO): dual structure + completeness,
  `FreeMeetCompletion.lean`, `OrImpConservative.lean`; `ConservativeChain.lean` + `Cslib.lean` updated.
- `specs/372_or_imp_disjunctive_implicational_fragment/plans/01_or-imp-fragment.md` (this plan,
  updated with Phase-6 GO/NO-GO decision).

## Rollback/Contingency

- The plan is purely additive; revert by dropping the new decls/files and the chain/`Cslib.lean`
  edits. Core (Phases 1–4) and conservativity (Phases 5–10) are committed separately so the core
  can ship even if conservativity is rolled back.
- **Phase-6 NO-GO contingency**: if the free-meet completion cannot be built sorry-free, mark
  Phases 7–10 [BLOCKED] with the precise obstruction, ship the core + `coe_AlgEvaluate_andBotFree`
  groundwork, and return `partial` with a follow-up recommendation. Never introduce a sorry or
  axiom to bridge conservativity.
