# Implementation Plan: Craig Interpolation for LK / LJ via Maehara's Method

- **Task**: 374 - Sequent Calculus Interpolation (Craig interpolation for LK and LJ)
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: Task 371 (LJ subformula property) — COMPLETE
- **Research Inputs**: specs/374_sequent_calculus_interpolation/reports/01_sequent-calculus-interpolation.md
- **Artifacts**: plans/01_sequent-calculus-interpolation.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add Craig interpolation for the propositional sequent calculi LK (classical) and LJ
(intuitionistic) via Maehara's method, building on the cut-elimination and subformula-property
foundations from task 371. The construction is a structural induction over an already
cut-eliminated proof: for a cut-free LK proof of `Γ ⊢ₛ Δ` and any *cover*
`Γ = Γ₁ ∪ Γ₂`, `Δ = Δ₁ ∪ Δ₂`, build an interpolant `I` with `Γ₁ ⊢ₛ {I} ∪ Δ₁`,
`{I} ∪ Γ₂ ⊢ₛ Δ₂`, and `vars I ⊆ vars(Γ₁∪Δ₁) ∩ vars(Γ₂∪Δ₂)`. The Craig corollary
(`⊢ A→B` ⟹ interpolant in `vars A ∩ vars B`) follows mechanically; LJ is a parallel
single-conclusion development sharing only `Proposition.vars` and the proof architecture.
Definition of done: no new axioms, no `sorry`, full CI green
(`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`).

### Research Integration

The plan follows the research report's design decisions directly:
- **Partition as a cover** (overlap allowed) threaded through the induction as ∀-quantified
  Finsets plus cover equations (`seq.ant = Γ₁ ∪ Γ₂`, `seq.suc = Δ₁ ∪ Δ₂`). Per-case side
  decisions use `Finset.mem_union`; premise reassembly uses `Finset.insert_union`. This is the
  single most important simplification — no `Disjoint`/`sdiff` bookkeeping.
- **Separate `(d, hcf)` + `induction d with`** pattern, copied from
  `LK/SubformulaProperty.lean:90` (`cutFreeSubformulaProp`), to side-step the Finset-quotient
  index problem. The `cut` case is vacuous (`exact absurd hcf id`).
- **Conclusions in `Prop`** via `Nonempty (LKProof …)`, keeping the whole invariant in `Prop`.
- **New `Proposition.vars : Proposition Atom → Finset Atom`**; the existing
  `Proposition.atoms` (`Metalogic/ClassicalImpCompleteness.lean`) is `List`-valued and partial
  (sends `and`/`or` to `[]`) and is NOT reusable. The `vars` bound rides inside the same
  induction (it cannot be factored out, since the interpolant is built compositionally).
- Hard cases identified: `ax` leaf table, `andR`, `orL`, `impL` (two-premise / side-crossing),
  with `impR` moderately hard; the remaining cut-free cases are mechanical.
- LJ is a SEPARATE single-conclusion development (`LKProof`/`LJProof` index shapes differ; the
  LK core cannot be instantiated for LJ).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (none provided in delegation context). Task 374 is
flagged in its description as the highest-effort item in the propositional backlog; it depends
on task 371 (LJ subformula property), which is complete.

## Goals & Non-Goals

**Goals**:
- A total, Finset-valued `Proposition.vars` plus a `Finset`-of-formulas lift and a battery of
  mechanical rewrite lemmas, shared by both LK and LJ.
- LK Maehara split-interpolation core (`maeharaCore`) covering every cut-free constructor.
- LK Craig corollary in implication form: `⊢ A→B` ⟹ `∃ I`, `⊢ A→I`, `⊢ I→B`,
  `vars I ⊆ vars A ∩ vars B`; plus a top-level `LKProof.interpolation` via `cutElim`.
- LJ single-conclusion Maehara core and its Craig corollary.
- Barrel imports updated; full CI pipeline green; no new axioms; no `sorry`.

**Non-Goals**:
- The algebraic / Lindenbaum–Heyting interpolation corollary (research §7: NOT cheap — needs a
  Lindenbaum/Heyting-algebra substrate absent from this directory). Explicitly out of scope;
  spin off as a follow-up task if desired.
- Any change to `LKProof`/`LJProof` datatypes or to the cut-elimination proofs.
- Reusing the existing `Proposition.atoms` (kept untouched).
- Transporting interpolation LJ→LK via the classical embedding (strictly harder than re-running
  the induction — avoided).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `vars`-bound bookkeeping roughly doubles per-case proof size (`simp`/Finset grind) | H | H | Prove the full `vars` rewrite battery up front in Phase 1 (`vars_and/or/imp`, `vars_union`, `vars_insert`, `vars_biUnion` subset lemmas) so each case is `simp`-closable. |
| Leaf `ax` interpolant table (2–4 sub-cases by side of each `A` occurrence; `⊥/⊤/A/¬A`) | H | M | Dedicated effort in Phase 3; enumerate the four `(A∈Γ₁?, A∈Δ₁?)` sub-cases explicitly; verify each half-sequent re-derives via `ax`/`botL`/`mono`. |
| Two-premise combination (`andR`, `orL`, `impL`): reassemble BOTH half-derivations and prove combined `vars` bound | H | H | Phase 3 marked highest-risk; may need splitting (see Phase 3 note). Build one hard case fully (`andR`) as the template before the others. |
| Induction index hygiene — wrong pattern fails to compile | M | L | Mandate the `(d, hcf)` + `induction d with` precedent from `cutFreeSubformulaProp`; do not `induction` on the `CutFree` subtype, and generalize the cover equations before inducting. |
| `Nonempty` vs `Type` derivation choice invasive to change later | M | L | Commit to `Nonempty (LKProof …)` (Prop) from Phase 2; keep the whole invariant in `Prop`. |
| Lint/CI: new `def`/`@[simp]` lemmas need docstrings (docBlame) and simpNF-valid LHSs; Prop results must be `lemma`/`theorem` | M | M | Phase 1 and Phase 6 budget for docstrings and `lake exe lint-style`/`shake`; run CI incrementally at each phase checkpoint. |
| A phase stalls on an un-closable goal | M | L | Per research: mark `[BLOCKED]` with the exact stuck goal state; NEVER `sorry`-defer. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 5 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 6 | 4, 5 |

Phases within the same wave can execute in parallel. Phase 5 (LJ core) depends only on the
shared vocabulary (Phase 1) and is independent of the LK chain (Phases 2–4), so it may run in
parallel with Phase 2. Phase 6 (LJ corollary + CI hardening) depends on the LJ core (Phase 5)
and on the full LK chain being green (Phase 4) so the final CI sweep covers everything.

---

### Phase 1: `Proposition.vars` + vocabulary lemma battery [COMPLETED]

**Goal**: Define a total, Finset-valued occurrence function on propositions and the
Finset-of-formulas lift, with all mechanical rewrite lemmas both LK and LJ developments need.

**Tasks**:
- [ ] Define `Proposition.vars : Proposition Atom → Finset Atom` by recursion:
      `atom x => {x}`, `bot => ∅`, `imp a b => a.vars ∪ b.vars`, `and a b => a.vars ∪ b.vars`,
      `or a b => a.vars ∪ b.vars`. Add a docstring (docBlame).
- [ ] Define the Finset lift `Finset.vars (S : Finset (Proposition Atom)) : Finset Atom :=
      S.biUnion Proposition.vars` (via `Finset.biUnion`, confirmed present). Docstring.
- [ ] Prove connective rewrite lemmas: `vars_and`, `vars_or`, `vars_imp` (each `= a.vars ∪ b.vars`),
      `vars_atom`, `vars_bot`. Mark `@[simp]` where simpNF-valid.
- [ ] Prove Finset-lift lemmas: `vars_union : (S ∪ T).vars = S.vars ∪ T.vars`;
      `vars_insert : (insert A S).vars = A.vars ∪ S.vars`; `vars_empty`, `vars_singleton`;
      and a `vars_biUnion`/subset helper as needed (`Finset.subset_biUnion_of_mem`).
- [ ] Confirm the intersection/subset API the cases need is available:
      `Finset.subset_inter_iff`, `Finset.mem_inter`, `Finset.inter_subset_left/right`.
- [ ] `¬A`/`⊤` are `abbrev`s for `imp` (`Defs.lean:95-98`); confirm `vars (¬A) = A.vars` and
      `vars ⊤ = ∅` reduce by the `imp` case (add `@[simp]` lemmas if `simp` does not unfold).

**Timing**: 1.5 hours (~60–90 lines)

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Subformula.lean` — add `Proposition.vars`, `Finset.vars`, and the
  lemma battery (sits naturally beside `Proposition.IsSubformula`; available to both LK and LJ
  with no new import path). *(Alternative per research: a new
  `Cslib/Logics/Propositional/SequentCalculus/Vocabulary.lean` imported by both interpolation
  files — choose this only if `Subformula.lean` cannot import `Finset.biUnion` cleanly.)*

**Verification**:
- `lake build Cslib.Logics.Propositional.Subformula` succeeds.
- Spot-check each rewrite lemma closes by `simp`/`rfl` in isolation.
- `lake exe lint-style` passes on the modified file (docstrings present).

---

### Phase 2: LK `maeharaCore` statement + easy/mechanical cases [IN PROGRESS]

**Goal**: Establish the partition-threading scaffold and discharge every one-premise / leaf
constructor except the hard ones, leaving the hard cases as explicit holes for Phase 3.

**Tasks**:
- [ ] State the core lemma in a new file:
      ```lean
      private lemma maeharaCore {seq : LKSequent Atom} (d : LKProof seq) (hcf : CutFree d) :
          ∀ Γ₁ Γ₂ Δ₁ Δ₂ : Finset (Proposition Atom),
            seq.ant = Γ₁ ∪ Γ₂ → seq.suc = Δ₁ ∪ Δ₂ →
            ∃ I : Proposition Atom,
              I.vars ⊆ (Γ₁ ∪ Δ₁).vars ∩ (Γ₂ ∪ Δ₂).vars ∧
              Nonempty (LKProof (Γ₁ ⊢ₛ insert I Δ₁)) ∧
              Nonempty (LKProof (insert I Γ₂ ⊢ₛ Δ₂))
      ```
      using `induction d with` after introducing `Γ₁ Γ₂ Δ₁ Δ₂` and the cover equations
      (generalize/keep the `∀` so the IH carries the partition freedom).
- [ ] `cut` case: `exact absurd hcf id` (vacuous).
- [ ] `botL` case (`⊥ ∈ Γ`): side-split on `⊥ ∈ Γ₁ ∨ ⊥ ∈ Γ₂` via `mem_union`;
      `⊥∈Γ₁ ⟹ I = ⊥`, `⊥∈Γ₂ ⟹ I = ⊤`; build both half-sequents by `botL`. `vars` bound trivial.
- [ ] `weakL A` / `weakR A`: weaken the appropriate half-derivation via `LKProof.mono`;
      `vars` bound only shrinks.
- [ ] `andL A B`: from `A∧B ∈ Γ` side-split; apply IH to premise
      `insert A (insert B Γ) ⊢ₛ Δ` with refined cover (place `A,B` on the chosen side);
      reassemble via `Finset.insert_union`; reapply `andL`; reuse `I`. `vars` unchanged.
- [ ] `orR A B`: dual on succedent (premise `… ⊢ₛ insert A (insert B Δ)`); reuse `I`,
      reapply `orR`.
- [ ] Leave `ax`, `andR`, `orL`, `impL`, `impR` as labelled placeholders (a temporary `admit`
      is acceptable *within Phase 2 only*; Phase 2's checkpoint does not yet require a green
      whole-file build — only that the scaffold typechecks). Note them clearly for Phase 3.

**Timing**: 2 hours (~120–160 lines)

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` — NEW. Imports
  `…LK.CutElimination` (for `cutElim`, `CutFree`, `LKProof`, `mono`) and the vocabulary file.

**Verification**:
- The `maeharaCore` statement elaborates and `induction d with` enumerates exactly the 11
  constructors (10 cut-free + vacuous `cut`).
- Each completed case typechecks (`lean_goal`/`lake build` on the file with placeholders).
- Confirm the cover-refinement reassembly identities (e.g.
  `insert A (insert B Γ₁) ∪ Γ₂ = insert A (insert B (Γ₁ ∪ Γ₂))`) close via `Finset.insert_union`.

---

### Phase 3: LK hard cases — `ax`, `andR`, `orL`, `impL`, `impR` [NOT STARTED]

**Goal**: Complete the Maehara case table; resulting `maeharaCore` is fully `sorry`-free.

**Tasks**:
- [ ] `ax A` (`A∈Γ`, `A∈Δ`): the leaf table. Case-split on the side of each occurrence —
      `(A∈Γ₁?, A∈Δ₁?)` four sub-cases. Interpolant is one of `⊥`, `⊤` (`= ⊥→⊥`), `A`, `¬A`
      to bridge the two halves; re-derive both half-sequents by `ax`/`botL`/`mono`. Verify
      `vars I ⊆ …`: `vars A`, `vars ¬A = vars A`, `vars ⊥ = vars ⊤ = ∅`.
- [ ] `andR A B` (two premises, succedent principal `A∧B`): obtain `I₁` (for `… ⊢ A,Δ`) and
      `I₂` (for `… ⊢ B,Δ`); `A∧B∈Δ₁ ⟹ I = I₁ ∨ I₂`, `A∧B∈Δ₂ ⟹ I = I₁ ∧ I₂`. Reassemble
      both half-derivations; prove `vars(I₁∘I₂) = vars I₁ ∪ vars I₂ ⊆ …` via `vars_or`/`vars_and`
      and `subset_inter_iff`. **Build this case first as the two-premise template.**
- [ ] `orL A B` (two premises `insert A Γ`, `insert B Γ`): dual of `andR`;
      `A∨B∈Γ₁ ⟹ I = I₁ ∨ I₂`, `A∨B∈Γ₂ ⟹ I = I₁ ∧ I₂`.
- [ ] `impL A B` (two premises `Γ ⊢ A,Δ` and `insert B Γ ⊢ Δ`; `A` moves to succedent, `B` to
      antecedent): most intricate — `I₁∧I₂` / `I₁∨I₂` by side of `A→B`. Reassemble both halves.
- [ ] `impR A B` (premise `insert A Γ ⊢ insert B Δ`; `A` left, `B` right of the same half):
      reuse `I`; reapply `impR`; verify `vars` bound.
- [ ] Remove any Phase-2 placeholders; whole file is `sorry`-free.

**Timing**: 2.5 hours (~120–180 lines) — **HIGHEST-RISK PHASE**

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` (complete the cases).

**Verification**:
- `lake build` of `LK/Interpolation.lean` green with zero `sorry`/`admit`.
- `lean_verify maeharaCore` (no new axioms beyond those of the foundations).

> **Splitting note (per task instruction)**: This is the highest-risk phase due to bookkeeping
> length. If an implementing agent runs low on context, split into **3a** = `ax` leaf table +
> `andR` (the two-premise template), and **3b** = `orL`, `impL`, `impR` (apply the established
> template). 3b depends on 3a. Each sub-phase ends at a green `lake build` of the file with the
> remaining cases held as explicit, clearly-labelled placeholders.

---

### Phase 4: LK Craig corollary + top-level interpolation theorem [NOT STARTED]

**Goal**: Derive the implication-form Craig interpolation and a `cutElim`-fed public theorem.

**Tasks**:
- [ ] From a cut-free proof of `(∅ ⊢ₛ {A→B})`, reduce via `impR`-inversion to `({A} ⊢ₛ {B})`;
      apply `maeharaCore` with the partition `Γ₁ = {A}`, `Δ₂ = {B}`, `Γ₂ = Δ₁ = ∅`.
- [ ] Package the result as `⊢ A→I`, `⊢ I→B` via `impR`, with `vars I ⊆ vars A ∩ vars B`
      (specialize the `(Γ₁∪Δ₁).vars ∩ (Γ₂∪Δ₂).vars` bound to the empty-side partition).
- [ ] State the public top-level `LKProof.interpolation` (or `CutFreeLKProof.interpolation`):
      take an arbitrary `LKProof`, obtain a cut-free proof via `LKProof.cutElim`
      (`LK/CutElimination.lean:839`), then invoke `maeharaCore`. Docstring.
- [ ] Add `public import …LK.Interpolation` to the `LK.lean` barrel.

**Timing**: 1.25 hours (~50–70 lines)

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` (corollaries).
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean` (barrel import).

**Verification**:
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK` green.
- `lean_verify LKProof.interpolation` — no new axioms, no `sorry`.

---

### Phase 5: LJ single-conclusion `maeharaCore` (all cases) [NOT STARTED]

**Goal**: Parallel re-implementation of the Maehara induction for LJ; succedent `C` is a single
proposition (not split).

**Tasks**:
- [ ] State the LJ core (antecedent-only partition):
      ```lean
      private lemma ljMaeharaCore {seq : @Sequent Atom} (d : LJProof seq) (hcf : LJCutFree d) :
          ∀ Γ₁ Γ₂ : Finset (Proposition Atom),
            seq.1 = Γ₁ ∪ Γ₂ →
            ∃ I : Proposition Atom,
              I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {seq.2}).vars ∧
              Nonempty (LJProof (Γ₁ ⊢ I)) ∧
              Nonempty (LJProof (insert I Γ₂ ⊢ seq.2))
      ```
      (`seq.2` is the lone conclusion `C`, always conceptually on the "right" component.)
- [ ] `cut` vacuous (`absurd hcf id`).
- [ ] One-premise succedent rules `orR1`, `orR2`, `andR`, `impR`: act on the unsplit
      succedent → pass the interpolant through; mechanical.
- [ ] Antecedent rules mirroring LK: `botL`, `weakL`, `andL` (one-premise); `orL`, `impL`
      (two-premise — the **hard** LJ cases, analogous to Phase 3). `ax`: single-conclusion leaf
      table — *simpler* than LK (no `¬A` succedent-crossing trick), but keep the interpolant
      intuitionistically valid (watch `ax` and `impL`; `impR`'s interpolant must stay
      intuitionistically derivable).
- [ ] Reuse `Proposition.vars` and all Phase-1 lemmas; reuse `LJProof.mono`
      (`LJ/Basic.lean:158`) and `Finset.insert_union`.

**Timing**: 2.5 hours (~120–170 lines) — hard for `orL`/`impL`

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean` — NEW. Imports
  `…LJ.CutElimination` and the vocabulary file.

**Verification**:
- `lake build` of `LJ/Interpolation.lean` green, zero `sorry`.
- `induction d with` enumerates the 11 LJ constructors (`ax, botL, andL, andR, orL, orR1,
  orR2, impL, impR, weakL, cut`); `cut` vacuous.

---

### Phase 6: LJ Craig corollary + barrels + CI hardening [NOT STARTED]

**Goal**: Finish the LJ corollary, wire barrels, and bring the whole task to full CI green.

**Tasks**:
- [ ] LJ Craig corollary: analogous to Phase 4 from `ljMaeharaCore`, yielding `I` with
      `Γ₁ ⊢ I`, `insert I Γ₂ ⊢ C`, `vars I ⊆ vars Γ₁ ∩ vars(Γ₂ ∪ {C})`; and a top-level
      `LJProof.interpolation` fed by `LJProof.cutElim` (`LJ/CutElimination.lean:23`). Docstring.
- [ ] Add `public import …LJ.Interpolation` to the `LJ.lean` barrel.
- [ ] Run the full CI pipeline and resolve any findings:
      `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
      `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Resolve lint: docstrings on all new public `def`/`theorem` (docBlame); `@[simp]` LHSs
      simpNF-valid; `shake` import minimization; `checkInitImports` for any new file imports.
- [ ] Confirm no new axioms via `lean_verify` on both `interpolation` theorems.

**Timing**: 1.25 hours (~40–60 lines + CI fixes)

**Depends on**: 4, 5

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean` (corollary).
- `Cslib/Logics/Propositional/SequentCalculus/LJ.lean` (barrel import).

**Verification**:
- All five CI commands green from the worktree root.
- `lean_verify LJProof.interpolation` and `LKProof.interpolation`: no `sorry`, no new axioms.

---

## Testing & Validation

- [ ] `lake build` — whole library compiles, including both new `Interpolation.lean` files and
      updated barrels.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe checkInitImports` — `Cslib.Init` import discipline holds for new files.
- [ ] `lake exe lint-style` — style/docstring linters pass.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no redundant imports.
- [ ] `lean_verify` on `LKProof.interpolation`, `LJProof.interpolation`, `maeharaCore`,
      `ljMaeharaCore`: zero `sorry`, no new axioms.
- [ ] Sanity-check the Craig corollaries on a small concrete instance (e.g. `A∧B → A`) if cheap.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Subformula.lean` — `Proposition.vars`, `Finset.vars`, lemma battery (Phase 1).
- `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` — `maeharaCore`, LK Craig corollary, `LKProof.interpolation` (Phases 2–4).
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean` — `ljMaeharaCore`, LJ Craig corollary, `LJProof.interpolation` (Phases 5–6).
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean`, `…/LJ.lean` — barrel imports updated.
- `specs/374_sequent_calculus_interpolation/summaries/01_sequent-calculus-interpolation-summary.md` — execution summary (on completion).

## Rollback/Contingency

- Each phase is an additive, file-scoped change; revert by deleting the new `Interpolation.lean`
  file(s) and the barrel import lines, plus the Phase-1 additions to `Subformula.lean`. No
  existing definitions are modified, so rollback cannot break LK/LJ or cut-elimination.
- If a hard case (Phase 3 / Phase 5 `orL`/`impL`) cannot be closed, mark the phase `[BLOCKED]`
  with the exact stuck goal state captured via `lean_goal` — **never** `sorry`-defer (research §9).
- If `Subformula.lean` cannot cleanly import `Finset.biUnion`, fall back to the new
  `SequentCalculus/Vocabulary.lean` file (research §3.2) and import it from both interpolation
  files; no other phase changes.
