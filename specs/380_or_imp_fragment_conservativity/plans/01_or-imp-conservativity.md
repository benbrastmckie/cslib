# Implementation Plan: Task #380 — Conservativity of IPL over IPL⟨∨,→,⊤⟩

- **Task**: 380 - Prove `hilbertIplConservativeOverOrImp` for the disjunctive-implicational fragment IPL⟨∨,→,⊤⟩ over its OrImp Hilbert system and wire it into `ConservativeChain.lean`
- **Status**: [COMPLETED]
- **Effort**: 6 hours
- **Dependencies**: None (all reused infrastructure already shipped and sorry-free; task 372 OrImp fragment core present)
- **Research Inputs**: specs/380_or_imp_fragment_conservativity/reports/01_or-imp-conservativity-research.md
- **Artifacts**: plans/01_or-imp-conservativity.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: lean
- **Lean Intent**: true

## Overview

Prove that IPL is conservative over the disjunctive-implicational fragment IPL⟨∨,→,⊤⟩: every
and-bot-free formula derivable in the full intuitionistic Hilbert system (`IntPropAxiom`) is
already derivable in the `OrImpAxiom` Hilbert system. The route is **proof-theoretic via the
existing, sorry-free LJ cut-elimination machinery** (`LJProof.cutElim`) plus the Hilbert↔LJ
bridge (`hilbert_iff_lj`), not algebraic — the task-372 Phase-6 free-meet-completion NO-GO is
sidestepped entirely. The mathematical heart is a **single new induction lemma**
`cutFreeLJ_toOrImp` (a cut-free LJ proof of an and-bot-free endsequent yields an OrImp Hilbert
derivation), generalized over any list `L ⊇ Γ` to absorb Finset↔List plumbing; the and-bot-free
invariant makes the `andL`/`andR`/`botL`/`cut` cases vacuous. Definition of done: a new sorry-free
file with `cutFreeLJ_toOrImp`, `hilbertIplConservativeOverOrImp`, the subsumption
`derivableOrImpOfDerivableInt`, the `_iff`, and the ND corollary `ipl_conservative_over_orImp`;
`ConservativeChain.lean` extended with the IPL⟨∨,→,⊤⟩ ⊂ IPL vertex and `orImpAxiom_iff_chain`;
`Cslib.lean` regenerated; and a fully green CI (no new axioms, no sorry).

### Research Integration

The plan follows the research report's RECOMMENDED route 1 verbatim. Key integrated findings:
- **Reuse, do not rebuild**: `LJProof.cutElim` (CutElimination.lean:674), `CutFreeLJProof`/`LJCutFree`
  (Basic.lean:193,207), `hilbert_iff_lj` (Completeness.lean:273), the OrImp-applicable derived
  Hilbert rules `hilbertOrI1Deriv`/`hilbertOrI2Deriv`/`hilbertOrEDeriv`/`hilbertImpIDeriv`/
  `hilbertImpEDeriv` (HilbertDerivedRules.lean:389,398,407,501,514), `hilbertCutListDeriv` +
  `assumption_deriv` (HilbertLindenbaum.lean / FromHilbert.lean:220), `OrImpAxiom` +
  `IsAndBotFree` (task 372), and the `derivable_mono`/`liftDerivationTree` +
  `_iff`/ND-corollary template from `ConjImpConservative.lean`.
- **Two early-validation spikes** (front-loaded into Phase 1): (a) the `classical` /
  `letI := Classical.decEq Atom` technique to remove `[DecidableEq Atom]` from the public
  statement so it matches `hilbertIplConservativeOverConjImp` (no DecidableEq hypothesis);
  (b) the import-layering decision (Semantics/Algebra/ vs Metalogic/) plus the
  `Derivable A φ = Deriv A [] φ` and `(∅ : Ctx).toList = []` defeq probes.
- **Rejected routes are out of scope**: no MacNeille/Rieger-Nishimura/Gödel-Tait/free-meet
  algebra. Do not attempt them.

### Prior Plan Reference

No prior plan for task 380. The task-372 plan/report/handoff are relevant only as the source of
the OrImp fragment core (`OrImpAxiom`, `IsAndBotFree`) and the Phase-6 NO-GO that this route
deliberately avoids; they are not templates for this plan.

### Roadmap Alignment

ROADMAP.md exists but contains no line item that directly names the propositional
conservative-extension chain or the OrImp fragment (its conservativity entries are under the
Bimodal programme). This task advances the propositional algebraic/proof-theoretic
conservative-extension chain by adding the final missing fragment vertex
(IPL⟨∨,→,⊤⟩ ⊂ IPL) alongside the existing `ConjImp`/`Imp`/`Mpl`/Glivenko vertices.
`roadmap_flag` is not set, so no ROADMAP review/update phases are included.

## Goals & Non-Goals

**Goals**:
- Prove `cutFreeLJ_toOrImp` (the single new core induction lemma), sorry-free, no new axioms.
- Prove the public `hilbertIplConservativeOverOrImp` with a signature parallel to
  `hilbertIplConservativeOverConjImp` (no `[DecidableEq Atom]` hypothesis).
- Provide `derivableOrImpOfDerivableInt` (subsumption), `hilbertIplConservativeOverOrImp_iff`,
  and the ND corollary `ipl_conservative_over_orImp`.
- Wire the new IPL⟨∨,→,⊤⟩ ⊂ IPL vertex + `orImpAxiom_iff_chain` into `ConservativeChain.lean`,
  mirroring the existing `conjImpAxiom_iff_chain` block, and update its documentation table.
- Regenerate `Cslib.lean`; pass the full CSLib CI gate green.

**Non-Goals**:
- The algebraic/MacNeille/Rieger-Nishimura/Gödel-Tait/free-meet-completion routes (all rejected).
- The Kripke canonical-model backup route K (only a fallback if route 1 hits an unforeseen wall).
- Any change to LJ, FragmentAxioms, HilbertDerivedRules, or other reused modules beyond,
  at most, tiny additive `Ctx.toList`/membership helper lemmas in the new file.
- New notation, new typeclasses, or refactors outside the new file and `ConservativeChain.lean`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Finset `Ctx` ↔ List `Deriv` plumbing friction (insert/membership) | M | H | Generalize the lemma over any list `L ⊇ Γ`; `insert A Γ`-cases reduce to `A :: L`; add 1-2 tiny `Ctx.toList`/membership helpers in Phase 1. |
| Import cycle if the file sits under `Semantics/Algebra/` but LJ pulls in algebra modules | H | L | Phase-1 spike confirms LJ modules sit on ProofSystem+Kripke and do not import `ConservativeChain`/`Semantics.Algebra`; if a cycle appears, place the file under `Metalogic/` and have `ConservativeChain` import it. |
| `[DecidableEq Atom]` leaking into the public statement | M | M | Phase-1 spike validates `classical` / `letI := Classical.decEq Atom` inside the (Prop-valued, `noncomputable`) proof body; keep the public signature DecidableEq-free. |
| `Derivable`/`Deriv [] φ` defeq or `(∅:Ctx).toList = []` not `rfl` | M | L | Phase-1 `simp`/`rfl` probe before committing the assembly; if not defeq, insert an explicit rewrite lemma. |
| An LJ rule case needs a witness OrImp does not supply | H | L | Research confirms only `ax/orL/orR1/orR2/impL/impR/weakL` can occur on and-bot-free sequents, and OrImp supplies every witness (K,S,orI1,orI2,orE); `and*/botL/cut` are vacuous by `hΓ`/`hC`/`d.2`. |
| Hidden sorry/axiom slips in | H | L | `lean_verify` on each new decl; final `lake build` + grep for `sorry`/`admit`; CI gate. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel. This plan is fully sequential: the
induction lemma (P2) depends on the plumbing/spike decisions (P1), and the public theorem +
wiring (P3) depends on the lemma (P2).

### Phase 1: Plumbing helpers + early-validation spikes [IN PROGRESS]

**Goal**: De-risk the whole approach up front. Decide the file's home (import layering),
validate the DecidableEq-elimination technique, probe the `Derivable`/`Deriv []` and
`(∅:Ctx).toList` defeqs, and land any tiny `Ctx.toList`/membership helper lemmas the induction
lemma will need — all before writing the heavy induction.

**Tasks**:
- [ ] Confirm exact signatures/locations of every reused decl with `lean_hover_info`:
  - `LJProof`, `LJCutFree`, `CutFreeLJProof` (`SequentCalculus/LJ/Basic.lean`),
    `LJProof.cutElim`, `CutFreeLJProof.mono` (`SequentCalculus/LJ/CutElimination.lean`),
    `hilbert_iff_lj` (`SequentCalculus/LJ/Completeness.lean`).
  - `OrImpAxiom`, `OrImpAxiom.toMinPropAxiom`, `mem_implyK`, `mem_implyS`
    (`ProofSystem/FragmentAxioms.lean`); `Proposition.IsAndBotFree`, `imp_isAndBotFree`,
    `or_isAndBotFree` (`Semantics/Algebra/FragmentPredicates.lean`).
  - `hilbertOrI1Deriv` (389), `hilbertOrI2Deriv` (398), `hilbertOrEDeriv` (407),
    `hilbertImpIDeriv` (501), `hilbertImpEDeriv` (514) in
    `NaturalDeduction/HilbertDerivedRules.lean`; `hilbertCutListDeriv`,
    `assumption_deriv`/`hilbertWeakeningDeriv` in `Semantics/Algebra/HilbertLindenbaum.lean`
    and `FromHilbert.lean:220`; `derivable_mono`/`liftDerivationTree` in
    `Semantics/Algebra/ConjImpConservative.lean`.
- [ ] **Import-layering spike**: from the chosen file location, write a scratch file that
  `public import`s the LJ `CutElimination`+`Completeness` modules together with
  `FragmentAxioms`, `FragmentPredicates`, `HilbertDerivedRules`, `HilbertLindenbaum`, and
  `ConjImpConservative` (for `derivable_mono`); run `lake build` on it. Confirm no import
  cycle. Decision rule: default to
  `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean`; if a cycle through
  `Semantics.Algebra` appears, relocate to
  `Cslib/Logics/Propositional/Metalogic/OrImpConservative.lean` and have `ConservativeChain`
  import that path instead. Record the chosen path in the phase notes.
- [ ] **DecidableEq-elimination spike**: in a scratch theorem with `{Atom : Type u}` and *no*
  `[DecidableEq Atom]`, confirm `classical` (equivalently `letI := Classical.decEq Atom`)
  discharges the LJ `[DecidableEq Atom]` requirement inside a `Prop`-valued, `noncomputable`
  body; confirm `hilbert_iff_lj` and `LJProof.cutElim` are usable under it.
- [ ] **Defeq probes**: verify `Derivable A φ` reduces to `Deriv A [] φ` and `(∅ : Ctx).toList = []`
  via `rfl`/`simp` (use `lean_multi_attempt`). If either is not `rfl`, write the minimal bridge
  lemma (e.g. `emptyCtx_toList : (∅ : Ctx Atom).toList = []`) in the new file.
- [ ] Create the new file with the standard CSLib header (`Copyright`, `module`,
  `import Cslib.Init`, the `public import`s validated above), module docstring (Main Results +
  Proof Strategy mirroring `ConjImpConservative.lean`), `@[expose] public section`,
  `noncomputable section`, `namespace Cslib.Logic.PL`, and the `open` line. Add only the tiny
  `Ctx.toList`/membership helper lemmas (e.g. `mem_toList`, `toList_insert_subset`, or a
  `∀ x ∈ Γ, x ∈ Γ.toList` shim) actually needed by the induction; keep them sorry-free.
- [ ] State `cutFreeLJ_toOrImp` with `sorry` as a placeholder body (signature only) so Phase 2
  has a typechecking target. Signature per research:
  `theorem cutFreeLJ_toOrImp {Atom} [DecidableEq Atom] {Γ : Ctx Atom} {C : Proposition Atom}
  (hΓ : ∀ x ∈ Γ, x.IsAndBotFree = true) (hC : C.IsAndBotFree = true)
  (d : CutFreeLJProof (Γ ⊢ C)) {L : List (Proposition Atom)} (hL : ∀ x ∈ Γ, x ∈ L) :
  Deriv (@OrImpAxiom Atom) L C`.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean` (new; or
  `Metalogic/OrImpConservative.lean` if the layering spike requires it) — header, imports,
  helper lemmas, `cutFreeLJ_toOrImp` signature stub.

**Verification**:
- The new file `lake build`s with only the expected `sorry`-placeholder warning on
  `cutFreeLJ_toOrImp` and no import-cycle / unknown-identifier errors.
- The three spikes pass: no DecidableEq in the intended public signature, no import cycle,
  defeq probes succeed (or a bridge lemma is in place).

### Phase 2: The `cutFreeLJ_toOrImp` induction lemma [NOT STARTED]

**Goal**: Replace the Phase-1 stub with a complete, sorry-free induction on the cut-free LJ
proof. Each LJ constructor maps to an OrImp Hilbert step or is discharged as vacuous by the
and-bot-free invariant / cut-freeness.

**Tasks**:
- [ ] Induct on `d.1 : LJProof (Γ ⊢ C)` carrying `d.2 : LJCutFree d.1` (and threading the
  generalized `L`/`hL`, `hΓ`, `hC`). Use `lean_goal` after each case split.
- [ ] `ax A Γ (A ∈ Γ)` → `assumption_deriv` with `A ∈ L` obtained from `hL`.
- [ ] `botL` → **vacuous**: `⊥ ∈ Γ` contradicts `hΓ` (`(⊥).IsAndBotFree = false`); close via the
  hypothesis contradiction.
- [ ] `andL` → **vacuous**: requires `A ∧ B ∈ Γ`, contradicting `hΓ`. `andR` → **vacuous**:
  `C = A ∧ B`, contradicting `hC`.
- [ ] `orR1`/`orR2` → from `hC` derive the chosen disjunct is and-bot-free (`or_isAndBotFree`);
  apply IH then `hilbertOrI1Deriv` / `hilbertOrI2Deriv` (OrImp `orI1`/`orI2` witnesses).
- [ ] `orL A B (A∨B ∈ Γ) ...` → from `hΓ` get `A`,`B` and-bot-free; `assumption_deriv` for
  `A∨B`; two IHs with `L := A :: L` and `L := B :: L` (extend `hΓ`/`hL` accordingly); combine
  via `hilbertOrEDeriv` (OrImp `orE`,`implyK`,`implyS`).
- [ ] `impL A B (A→B ∈ Γ) (Γ⊢A) (B,Γ⊢C)` → from `hΓ` get `A`,`B` and-bot-free; `hilbertImpEDeriv`
  on assumption `A→B` + IH(A) gives `Deriv L B`; combine with IH(C) (`L := B :: L`) via
  `hilbertCutListDeriv`.
- [ ] `impR A B (A,Γ⊢B)` → from `hC` get `A`,`B` and-bot-free; IH with `L := A :: L`, then
  `hilbertImpIDeriv` (deduction theorem).
- [ ] `weakL A (Γ⊢C)` → IH with the same `L` (membership is monotone; reuse `hL`).
- [ ] `cut` → **vacuous**: discharged by `d.2 : LJCutFree` (cut case carries `False`).
- [ ] For each and-bot-free sub-derivation, supply the `IsAndBotFree` side-conditions using
  `imp_isAndBotFree`/`or_isAndBotFree` and the `hΓ`/`hC` hypotheses (use `simp`/`decide` on the
  boolean predicate where appropriate, without bypassing real proof obligations).
- [ ] Run `lean_verify Cslib.Logic.PL.cutFreeLJ_toOrImp` to confirm no `sorry`/no new axioms.

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean` (or `Metalogic/…`) —
  complete `cutFreeLJ_toOrImp`.

**Verification**:
- `lake build` of the new module succeeds with zero `sorry` warnings.
- `lean_verify` reports `cutFreeLJ_toOrImp` depends on no `sorryAx` and introduces no new axioms.

### Phase 3: Public theorem + subsumption + _iff + ND corollary + chain wiring + CI [NOT STARTED]

**Goal**: Assemble the public API on top of the lemma, mirror the `ConjImpConservative.lean`
template, wire the new vertex into `ConservativeChain.lean`, regenerate `Cslib.lean`, and pass
the full CSLib CI gate green.

**Tasks**:
- [ ] Prove `hilbertIplConservativeOverOrImp {Atom} {φ} (hABF : φ.IsAndBotFree = true)
  (h : Derivable (@IntPropAxiom Atom) φ) : Derivable (@OrImpAxiom Atom) φ` with the research
  assembly: `classical`; `obtain ⟨d⟩ := hilbert_iff_lj.mp h`; `obtain ⟨dcf⟩ := d.cutElim`;
  `exact ⟨cutFreeLJ_toOrImp (by simp) hABF dcf (L := []) (by simp)⟩` (using the Phase-1 defeq /
  `(∅:Ctx).toList = []` bridge as needed; `Γ = ∅`, `L = []`, `hΓ` vacuous). No `[DecidableEq Atom]`
  in the signature.
- [ ] Prove `derivableOrImpOfDerivableInt {Atom} {φ} (h : Derivable (@OrImpAxiom Atom) φ) :
  Derivable (@IntPropAxiom Atom) φ` via
  `derivable_mono (fun _ hψ => hψ.toMinPropAxiom.toIntPropAxiom) h` (mirror
  `derivableConjImpOfDerivableInt`; confirm the `OrImpAxiom → MinPropAxiom → IntPropAxiom`
  coercion chain names with `lean_hover_info`).
- [ ] Prove `hilbertIplConservativeOverOrImp_iff {Atom} {φ} (hABF : φ.IsAndBotFree = true) :
  Derivable (@IntPropAxiom Atom) φ ↔ Derivable (@OrImpAxiom Atom) φ` as
  `⟨hilbertIplConservativeOverOrImp hABF, derivableOrImpOfDerivableInt⟩`.
- [ ] Prove the ND corollary `ipl_conservative_over_orImp {Atom} [DecidableEq Atom]
  {A} (hABF : A.IsAndBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
  Derivable (@OrImpAxiom Atom) A` via
  `hilbertIplConservativeOverOrImp hABF (derivableInIplIffDerivableInt.mp h)` (mirror
  `ipl_conservative_over_conjImp`; `DecidableEq` is fine here since it matches the ConjImp ND
  corollary's section variable).
- [ ] `lean_verify` each of the four new public decls: no `sorry`, no new axioms.
- [ ] **Wire `ConservativeChain.lean`**:
  - Add `public import` of the new module (after the `ConjImpConservative` import).
  - Add the new chain row to the documentation table (after the
    `IPL⟨∧,→,⊤⟩ ⊂ IPL` row): `| IPL⟨∨,→,⊤⟩ ⊂ IPL | hilbertIplConservativeOverOrImp | and-bot-free | IsAndBotFree |`,
    and update the prose chain description to mention the new fragment vertex.
  - Add `orImpAxiom_iff_chain {Atom} {φ} (hABF : φ.IsAndBotFree = true) :
    Derivable (@OrImpAxiom Atom) φ ↔ Derivable (@IntPropAxiom Atom) φ :=
    hilbertIplConservativeOverOrImp_iff hABF |>.symm`, mirroring `conjImpAxiom_iff_chain`
    (lines 270-273).
  - Add an ND chain corollary `nd_chain_ipl_to_orImp` in the `## ND Corollaries` section
    (mirroring `nd_chain_ipl_to_conjImp`, lines 329-332), under the existing
    `[DecidableEq Atom]` section variable.
- [ ] Regenerate the barrel: `lake exe mk_all --module` (updates `Cslib.lean` with the new file).
- [ ] Run the full CSLib CI gate, in order, and make each green:
  `lake build` → `lake exe checkInitImports` → `lake lint` → `lake exe lint-style` →
  `lake test` → `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Grep the new/modified files for `sorry`/`admit`/`axiom`; confirm none introduced.

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean` (or `Metalogic/…`) —
  the four public decls.
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` — import, doc table +
  prose, `orImpAxiom_iff_chain`, `nd_chain_ipl_to_orImp`.
- `Cslib.lean` — regenerated barrel import (via `lake exe mk_all --module`).

**Verification**:
- All four public decls plus the chain wiring `lake build` cleanly.
- `lean_verify` on `hilbertIplConservativeOverOrImp`, `derivableOrImpOfDerivableInt`,
  `hilbertIplConservativeOverOrImp_iff`, `ipl_conservative_over_orImp`, `orImpAxiom_iff_chain`:
  no `sorry`, no new axioms.
- Full CI gate green: `lake build`, `lake exe checkInitImports`, `lake lint`,
  `lake exe lint-style`, `lake test`, `lake shake`.

## Testing & Validation

- [ ] `lake build` (full project) succeeds with zero errors and zero `sorry` warnings.
- [ ] `lake exe checkInitImports` passes (new file imports `Cslib.Init`).
- [ ] `lake lint` passes (docstrings on all public decls; no environment-linter violations).
- [ ] `lake exe lint-style` passes (text/style linters).
- [ ] `lake test` passes (`CslibTests/`).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unnecessary imports.
- [ ] `lean_verify` confirms no new axioms and no `sorry`/`admit` in any new or modified decl.
- [ ] The public `hilbertIplConservativeOverOrImp` signature has **no** `[DecidableEq Atom]`
  hypothesis (parallel to `hilbertIplConservativeOverConjImp`).

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean` (new; or under
  `Metalogic/` per the Phase-1 layering decision) — `cutFreeLJ_toOrImp`,
  `hilbertIplConservativeOverOrImp`, `derivableOrImpOfDerivableInt`,
  `hilbertIplConservativeOverOrImp_iff`, `ipl_conservative_over_orImp`, plus any tiny
  `Ctx.toList` helper lemmas.
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` (modified) — new
  IPL⟨∨,→,⊤⟩ ⊂ IPL vertex, doc table/prose update, `orImpAxiom_iff_chain`,
  `nd_chain_ipl_to_orImp`.
- `Cslib.lean` (modified) — regenerated barrel import.

## Rollback/Contingency

- All work is additive: the new file plus an additive block in `ConservativeChain.lean` and a
  regenerated `Cslib.lean`. To revert, delete the new file, revert `ConservativeChain.lean`,
  and re-run `lake exe mk_all --module`.
- If the Phase-1 import-layering spike reveals a cycle, relocate the new file to
  `Cslib/Logics/Propositional/Metalogic/OrImpConservative.lean` before writing Phase 2; this is
  a path change only, no proof change.
- If route 1 hits an unforeseen wall in Phase 2 (e.g. an LJ constructor that cannot be
  simulated despite the and-bot-free invariant — not expected per research), mark Phase 2
  **[BLOCKED]**, document the exact goal state and missing witness, and escalate. The backup is
  route K (Kripke canonical model, research §"Backup route K"); do NOT silently substitute a
  `sorry` or a vacuous definition.
