# Implementation Plan v2 (Divided): Craig Interpolation for LK / LJ via Maehara

- **Task**: 374 - Sequent Calculus Interpolation (Craig interpolation for LK and LJ)
- **Status**: [NOT STARTED]
- **Effort**: 9 hours
- **Dependencies**: Task 371 (LJ subformula property) — COMPLETE
- **Research Inputs**: reports/01_sequent-calculus-interpolation.md; reports/02_decomposition.md
- **Artifacts**: plans/02_interpolation-divided.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This is **version 2** of the task-374 plan. Plan v1 (`plans/01_sequent-calculus-interpolation.md`)
landed Phases 1–2 (the shared `Proposition.vars` vocabulary and the LK `maeharaCore` scaffold with
all mechanical/leaf cases) but **stalled** when the remaining work was packaged as a few large
phases (one phase carrying all four hard LK cases, one carrying the whole LJ development). This
revision **divides the remaining work into the smallest sensible phases — ideally one proof
obligation per phase** — so each can be discharged in a single focused implementation dispatch
ending at a green build with zero new debt.

The genuinely remaining work (per `reports/02_decomposition.md` §0) is exactly:
1. the **4 LK `maeharaCore` cases** still `sorry` in
   `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean`
   (`andR`:311, `orL`:315, `impL`:319, `impR`:323 — file is GREEN with these 4 deferred `sorry`);
2. the **LK Craig corollary + public `LKProof.interpolation` + barrel**;
3. the **entire LJ development** (new file: core + corollary + barrel + final CI).

### Research Integration

Phase decomposition follows `reports/02_decomposition.md` directly:
- Per-obligation difficulty (§1): `impR` is the warmup (M/H); `andR` is the two-premise **template**
  (H); `orL` mirrors `andR` on the antecedent side (M/H once `andR` is done); `impL` is the hardest
  (H+, asymmetric premises). LK Craig corollary and both LJ corollaries are mechanical (M). LJ core
  is a ~0.7× re-run of LK (H for `orL`/`impL`).
- Independence (§2, §4): **LK (A1–B) and LJ (C1–C3) are two independent tracks on disjoint files.**
  `LJ` depends only on the already-complete Phase-1 vocabulary, not on the LK chain, so the two
  tracks may run in parallel under a territory contract (`LK/Interpolation.lean` + `LK.lean` vs new
  `LJ/Interpolation.lean` + `LJ.lean` — no write conflicts).
- No shared-prerequisite subtask is needed (§3): the `vars` vocabulary both calculi need already
  exists and is complete in `Subformula.lean`.
- Verified infrastructure table (§ Appendix) is cited per phase.

### Prior Plan Reference

Plan v1 validated: (a) the `(d, hcf)` + `induction d with` pattern compiles and enumerates all 11
constructors; (b) the per-case idiom for one-premise/leaf cases — cover refinement via
`Finset.insert_union`, side-split via `Finset.mem_union`, `vars` bound via
`Finset.vars_union`/`Finset.vars_mono`/`calc`, antecedent reshuffle via
`d.mono hperm (Finset.Subset.refl _)`; (c) the full four-way `ax` leaf table
(`⊥/A/¬A/⊤`, Interpolation.lean:264–307). The Phase-2 summary
(`summaries/01_interpolation-phase2-summary.md`) records the exact pitfalls already solved
(binder arity via `@`-patterns, `.seq` projection invalidity, `rw` on projection-form hypotheses via
`have hant' : Γ = … := hant`, cover-direction `.symm`, `calc`-wildcard timeouts requiring fully
explicit terms). New phases reuse these idioms verbatim. Effort calibration: each mechanical
one-premise case in v1 was ~30–45 lines; the two-premise cases are budgeted ~50–80 lines each.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (none provided in delegation context).

## Goals & Non-Goals

**Goals**:
- Close all four remaining LK `maeharaCore` `sorry` → `maeharaCore` fully `sorry`-free, file green.
- LK Craig corollary (implication form) + public `LKProof.interpolation` via `LKProof.cutElim`;
  `LK.lean` barrel updated.
- New LJ single-conclusion `ljMaeharaCore` (all cases) + LJ Craig corollary + public
  `LJProof.interpolation` via `LJProof.cutElim`; `LJ.lean` barrel updated.
- Full CI green across both interpolation files; no new axioms; no `sorry`.

**Non-Goals**:
- The algebraic / Lindenbaum–Heyting interpolation corollary (research §7 — out of scope).
- Any change to `LKProof`/`LJProof` datatypes or the cut-elimination proofs.
- Reusing `Proposition.atoms` (kept untouched); `Proposition.vars` already exists from Phase 1.
- Transporting LJ→LK via the classical embedding.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Two-premise interpolant combination (`andR`/`orL`/`impL`, and LJ mirrors) — reassemble BOTH halves with `mono`+`insert_union` AND prove combined `vars(I₁∘I₂)` bound | H | H | Build `andR` (Phase A2) FIRST as the reusable template; `orL` (A3) transcribes it side-swapped; `impL` (A4) adapts for asymmetric premises. LJ `orL`/`impL` (C2) reuse the same shape. |
| `impL` asymmetric premises (`A`→succedent, `B`→antecedent) — most intricate single goal | H | M | Isolate as its own phase (A4) after the template is proven; capture exact `lean_goal` if blocked. |
| `vars`-bound bookkeeping doubles per-case size; `calc`-wildcard `whnf` timeouts | M | M | Reuse the fully-explicit `calc` idiom from v1 (summary §"Explicit calc wildcards"); `Finset.vars_union`/`vars_mono`/`subset_inter` battery already proven in Phase 1. |
| LJ single-conclusion shape differs from LK; LK core cannot be instantiated | M | L | C-track is a genuine parallel re-implementation; pass-through right rules are *simpler* than LK (interpolant threaded unchanged). |
| A case cannot close | M | L | **ZERO-DEBT**: mark the phase `[BLOCKED]` with the exact `lean_goal` state; NEVER `sorry`-defer. A phase is done only at a green build with no `sorry` in the cases it owns. |
| Concurrent implementation agent in same worktree | M | M | BUILD only the specific owned module per phase; LK and LJ tracks touch disjoint files (territory contract). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | A1, C1 | -- |
| 2 | A2, C2 | A1 (A2); C1 (C2) |
| 3 | A3 | A2 |
| 4 | A4 | A3 |
| 5 | B, C3 | A4 (B); C2 (C3) |
| 6 | D | B, C3 |

Phases within the same wave can execute in parallel. **LK track (A1→A2→A3→A4→B) and LJ track
(C1→C2→C3) are independent** (disjoint files) and run concurrently; A1 and C1 launch together.
Phase D is the final whole-library CI gate after both tracks are green.

The internal LK ordering (A1 `impR` → A2 `andR` → A3 `orL` → A4 `impL`) is mandated by the
decomposition (§2 internal order, §4): warmup, then build the two-premise template, then transcribe,
then the hardest. A2/A3/A4 are strictly sequential because A3 and A4 reuse the template established
in A2.

---

### Phase A1: LK `impR` case (warmup, one-premise) [NOT STARTED]

**Goal**: Close the `impR` `sorry` (Interpolation.lean:323); file stays green with 3 `sorry`
remaining (`andR`, `orL`, `impL`).

**Scope**: The single `impR A B hAB d' ih` case. Principal `A→B ∈ Δ`, one premise
`d' : insert A Γ ⊢ₛ insert B Δ` (`A` to antecedent, `B` to succedent of the same chosen half).
Side-split on `A→B ∈ Δ₁ ∨ Δ₂` via `Finset.mem_union`; apply `ih` to `d'` with the refined cover
`insert A Γ_k` / `insert B Δ_k`; reuse the IH interpolant `I`; reapply `LKProof.impR`. `vars` bound
unchanged (`A`, `B` are subformulas of `A→B`).

**Target file**: `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` (only).

**Key lemmas/idioms to reuse** (decomposition §1 `impR` MODERATE; Appendix table):
- Mirror the completed `andL` (Interpolation.lean:152–207) and `orR` (208–263) one-premise idiom.
- `have hsuc' : Δ = Δ₁ ∪ Δ₂ := hsuc` then `rw [hsuc'] at hAB`; `Finset.mem_union.mp`.
- Cover reassembly: `Finset.insert_union`; the antecedent/succedent reshuffle
  `d.mono hperm (Finset.Subset.refl _)` where `hperm` is proven by
  `intro x; simp only [Finset.mem_insert]; tauto` (as at andL:204, orR:232).
- `vars` bound: `Finset.vars_union`, `Finset.vars_mono`, `Finset.subset_inter`, explicit `calc`.

**Verification**: `lake build Cslib.Logics.Propositional.SequentCalculus.LK.Interpolation` green;
`impR` `sorry` gone (only `andR`/`orL`/`impL` remain).

**Checklist**:
- [ ] Side-split `A→B ∈ Δ₁ ∨ Δ₂`.
- [ ] IH call with refined cover for each side; interpolant reused.
- [ ] `LKProof.impR` reapplied on both half-derivations.
- [ ] `vars` bound discharged via explicit `calc`.
- [ ] `lake build …LK.Interpolation` green; no new `sorry`; `impR` closed.

**Depends on**: none (operates on the current GREEN file).

**Timing**: 1 hour (~40–60 lines).

---

### Phase A2: LK `andR` case (two-premise TEMPLATE) [NOT STARTED]

**Goal**: Close the `andR` `sorry` (Interpolation.lean:311) and **establish the reusable
two-premise interpolant-combination template**; file green with 2 `sorry` remaining (`orL`, `impL`).

**Scope**: The `andR A B hAB d₁ d₂ ih₁ ih₂` case. Principal `A∧B ∈ Δ`, two premises
`d₁ : Γ ⊢ₛ insert A Δ`, `d₂ : Γ ⊢ₛ insert B Δ`; `CutFree (andR …) = CutFree d₁ ∧ CutFree d₂`, so
feed `hcf.1`/`hcf.2` to `ih₁`/`ih₂`. Obtain `I₁` (placing `A` on the side of `A∧B`) and `I₂`
(placing `B`). Combination: **`A∧B ∈ Δ₁ ⟹ I = I₁ ∨ I₂`; `A∧B ∈ Δ₂ ⟹ I = I₁ ∧ I₂`.** Reassemble
*both* half-derivations (reapply `orR`/`andR` + `LKProof.mono` to the two IH derivations) and prove
`vars (I₁∘I₂) = vars I₁ ∪ vars I₂ ⊆ …` via `vars_or`/`vars_and` + `Finset.subset_inter`.

**Target file**: `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` (only).

**Key lemmas/idioms to reuse** (decomposition §1 `andR` HARD/template; §5):
- `CutFree`-conjunction destructuring: `hcf.1`, `hcf.2` into `ih₁`, `ih₂`.
- `LKProof.mono` (`LK/Basic.lean:143`) for both half reassemblies; `Finset.insert_union`.
- Combined `vars`: `vars_or`/`vars_and` (`= a.vars ∪ b.vars`), `Finset.vars_union`,
  `Finset.subset_inter`, `Finset.union_subset_union_*`. Use fully-explicit `calc` (no wildcards) to
  avoid `whnf` timeout (summary §"Explicit calc wildcards").
- Half-sequent re-derivation: `LKProof.orR`/`LKProof.andR` reapplied to combine `I₁`,`I₂`.

**Verification**: `lake build …LK.Interpolation` green; `andR` `sorry` gone (only `orL`/`impL`
remain). Note in the summary that the combination shape is the template for A3/A4.

**Checklist**:
- [ ] `ih₁ hcf.1 …`, `ih₂ hcf.2 …` produce `I₁`, `I₂`.
- [ ] Side-split `A∧B ∈ Δ₁ ∨ Δ₂`; `I := I₁∨I₂` resp. `I₁∧I₂`.
- [ ] Both half-derivations reassembled (`mono` + reapplied right rule).
- [ ] Combined `vars` bound discharged (`vars_or`/`vars_and`, explicit `calc`).
- [ ] `lake build …LK.Interpolation` green; no new `sorry`; `andR` closed.

**Depends on**: A1.

**Timing**: 1.5 hours (~60–80 lines).

---

### Phase A3: LK `orL` case (mirror of `andR`, antecedent side) [NOT STARTED]

**Goal**: Close the `orL` `sorry` (Interpolation.lean:315) by transcribing the A2 template onto the
antecedent side; file green with 1 `sorry` remaining (`impL`).

**Scope**: The `orL A B hAB d₁ d₂ ih₁ ih₂` case. Antecedent-side dual of `andR`: principal
`A∨B ∈ Γ`, premises `insert A Γ ⊢ₛ Δ`, `insert B Γ ⊢ₛ Δ`. Combination:
**`A∨B ∈ Γ₁ ⟹ I = I₁ ∨ I₂`; `A∨B ∈ Γ₂ ⟹ I = I₁ ∧ I₂`** (partition side swapped to antecedent).

**Target file**: `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` (only).

**Key lemmas/idioms to reuse** (decomposition §1 `orL` HARD, "largely a transcription with the
partition side swapped"; reuse A2 template directly):
- Same `CutFree`-conjunction + `ih₁`/`ih₂` pattern as A2.
- Antecedent cover refinement: `insert A Γ_k` premises; reassemble with `Finset.insert_union` and
  the `d.mono hperm (Finset.Subset.refl _)` reshuffle (as andL:204).
- Combined `vars` bound via the A2 idiom (`vars_or`/`vars_and`, explicit `calc`).

**Verification**: `lake build …LK.Interpolation` green; `orL` `sorry` gone (only `impL` remains).

**Checklist**:
- [ ] `ih₁ hcf.1 …`, `ih₂ hcf.2 …` produce `I₁`, `I₂`.
- [ ] Side-split `A∨B ∈ Γ₁ ∨ Γ₂`; `I := I₁∨I₂` resp. `I₁∧I₂`.
- [ ] Both half-derivations reassembled on the antecedent side.
- [ ] Combined `vars` bound discharged.
- [ ] `lake build …LK.Interpolation` green; no new `sorry`; `orL` closed.

**Depends on**: A2.

**Timing**: 1 hour (~50–70 lines).

---

### Phase A4: LK `impL` case (hardest, asymmetric premises) [NOT STARTED]

**Goal**: Close the `impL` `sorry` (Interpolation.lean:319) → **`maeharaCore` fully `sorry`-free**,
file green with zero `sorry`.

**Scope**: The `impL A B hAB d₁ d₂ ih₁ ih₂` case. Principal `A→B ∈ Γ`, **asymmetric** premises
`d₁ : Γ ⊢ₛ insert A Δ` (`A` to *succedent*) and `d₂ : insert B Γ ⊢ₛ Δ` (`B` to *antecedent*). The
two IH calls use different cover shapes; interpolant combination `I₁∧I₂` vs `I₁∨I₂` by side of
`A→B` must respect both. Reassemble both halves and reapply `LKProof.impL`.

**Target file**: `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` (only).

**Key lemmas/idioms to reuse** (decomposition §1 `impL` HARDEST; §5):
- A2 combination template, adapted: `d₁` adds `A` to the succedent cover side, `d₂` adds `B` to the
  antecedent cover side — two distinct refined covers.
- `LKProof.impL`, `LKProof.mono`, `Finset.insert_union`, the `hperm` reshuffle.
- Combined `vars`: `vars_or`/`vars_and`, `Finset.subset_inter`, explicit `calc`.

**Verification**: `lake build …LK.Interpolation` green with **zero `sorry`/`admit`**;
optionally `lean_verify Cslib.Logic.PL.maeharaCore` (no new axioms). If the asymmetric goal cannot
close, mark `[BLOCKED]` with the exact `lean_goal` — never `sorry`-defer.

**Checklist**:
- [ ] `ih₁ hcf.1 …` (succedent-side `A`), `ih₂ hcf.2 …` (antecedent-side `B`) produce `I₁`, `I₂`.
- [ ] Side-split `A→B ∈ Γ₁ ∨ Γ₂`; combination `I₁∧I₂` / `I₁∨I₂`.
- [ ] Both halves reassembled; `LKProof.impL` reapplied.
- [ ] Combined `vars` bound discharged.
- [ ] `lake build …LK.Interpolation` green; **`maeharaCore` zero `sorry`**.

**Depends on**: A3.

**Timing**: 1.5 hours (~60–90 lines).

---

### Phase B: LK Craig corollary + public `LKProof.interpolation` + barrel [NOT STARTED]

**Goal**: Derive the implication-form Craig corollary and a `cutElim`-fed public theorem; wire the
`LK.lean` barrel.

**Scope**: Append to `LK/Interpolation.lean`: (1) Craig corollary — from a cut-free proof of
`∅ ⊢ₛ {A→B}`, invert via `impR` to `{A} ⊢ₛ {B}`, apply `maeharaCore` with
`Γ₁={A}, Δ₂={B}, Γ₂=Δ₁=∅`, specialize the bound to `vars I ⊆ vars A ∩ vars B`, package as `⊢ A→I`,
`⊢ I→B` via `impR`. (2) Public `LKProof.interpolation` feeding an arbitrary `LKProof` through
`LKProof.cutElim`. (3) Add `public import …LK.Interpolation` to `LK.lean`.

**Target files**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` (append corollaries).
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean` (barrel import).

**Key lemmas/idioms to reuse** (decomposition §1 LK Craig MECHANICAL):
- `LKProof.cutElim` (`LK/CutElimination.lean:839`) → `Nonempty (CutFreeLKProof seq)`.
- `vars_empty`/`Finset.union_empty` bookkeeping for the empty-side partition.
- Docstrings on all new public decls (docBlame).

**Verification**: `lake build Cslib.Logics.Propositional.SequentCalculus.LK` green (covers barrel);
optionally `lean_verify Cslib.Logic.PL.LKProof.interpolation` — no `sorry`, no new axioms.

**Checklist**:
- [ ] Craig corollary proven (`vars I ⊆ vars A ∩ vars B`).
- [ ] Public `LKProof.interpolation` via `cutElim`, with docstring.
- [ ] `public import …LK.Interpolation` added to `LK.lean`.
- [ ] `lake build …SequentCalculus.LK` green.

**Depends on**: A4.

**Timing**: 1 hour (~50–70 lines).

---

### Phase C1: LJ `ljMaeharaCore` leaf + one-premise/pass-through cases [NOT STARTED]

**Goal**: Create the new LJ interpolation file; state `ljMaeharaCore` (single-conclusion) and
discharge the easy cases; hold `orL`/`impL` as clearly-labelled `sorry` checkpoints. File green.

**Scope**: NEW `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean`. State the
antecedent-only-partition core:
```lean
private lemma ljMaeharaCore {seq : @Sequent Atom} (d : LJProof seq) (hcf : LJCutFree d) :
    ∀ Γ₁ Γ₂ : Finset (Proposition Atom),
      seq.1 = Γ₁ ∪ Γ₂ →
      ∃ I : Proposition Atom,
        I.vars ⊆ Γ₁.vars ∩ (Γ₂ ∪ {seq.2}).vars ∧
        Nonempty (LJProof (Γ₁ ⊢ I)) ∧
        Nonempty (LJProof (insert I Γ₂ ⊢ seq.2))
```
`induction d with`; `cut` vacuous (`absurd hcf id`). Discharge: right rules `orR1`,`orR2`,`andR`,
`impR` (one-premise **pass-through** on the unsplit succedent — interpolant threaded unchanged,
*simpler* than LK); `ax` (single-conclusion leaf — *simpler* than LK, no `¬A` succedent-crossing);
`andL`, `weakL`, `botL` (mirror LK one-premise idioms). **Hold `orL` and `impL` as explicit labelled
`sorry`** (checkpoint only — to be closed in C2).

**Target file**: NEW `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean`. Imports
`Cslib.Init`, `…LJ.CutElimination` (public), `…Propositional.Subformula` (public, for `vars`).

**Key lemmas/idioms to reuse** (decomposition §1 LJ core; Appendix table):
- `LJProof` 11 ctors `ax,botL,andL,andR,orL,orR1,orR2,impL,impR,weakL,cut` (`LJ/Basic.lean:86`).
- `LJProof.mono (hL : Γ ⊆ Γ')` single-sided (`LJ/Basic.lean:158`); `LJCutFree` (`LJ/Basic.lean:193`).
- `Proposition.vars` + Phase-1 `Finset.vars` battery (`Subformula.lean:144,242–274`) reused.
- The one-premise idiom transcribed from LK `andL`/`orR` (Interpolation.lean:152–263), single-conclusion.

**Verification**: `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.Interpolation` green;
`induction d with` enumerates the 11 LJ ctors; only `orL`/`impL` `sorry` remain (clearly labelled).

**Checklist**:
- [ ] New file created with header, imports, namespace, `ljMaeharaCore` statement.
- [ ] `cut` vacuous; `ax`, `botL`, `weakL`, `andL` closed.
- [ ] `orR1`, `orR2`, `andR`, `impR` pass-through closed.
- [ ] `orL`, `impL` held as labelled `sorry` checkpoints (C2 will close).
- [ ] `lake build …LJ.Interpolation` green.

**Depends on**: none (Phase-1 vocabulary already complete; independent of LK track).

**Timing**: 1.5 hours (~80–120 lines).

---

### Phase C2: LJ `orL` + `impL` two-premise cases [NOT STARTED]

**Goal**: Close the `orL` and `impL` checkpoints → **`ljMaeharaCore` fully `sorry`-free**, file green.

**Scope**: The two hard LJ two-premise cases (analogous to LK A3/A4 but single-conclusion: the right
interpolant sequent `insert I Γ₂ ⊢ C` must stay single-conclusion). `orL`: premises
`insert A Γ ⊢ C`, `insert B Γ ⊢ C`; combine `I₁`/`I₂` by side of `A∨B ∈ Γ₁/Γ₂`. `impL`: combine by
side of `A→B ∈ Γ`, respecting the intuitionistic single-conclusion constraint.

**Target file**: `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean` (close the two
held cases).

**Key lemmas/idioms to reuse** (decomposition §1 LJ "`orL` and `impL` remain the hard two-premise
cases, analogous to LK Phase 3"):
- The LK A2/A3/A4 two-premise template (combination `I₁∨I₂` / `I₁∧I₂`), specialized to
  single-conclusion shapes.
- `LJProof.mono`, `Finset.insert_union`, `vars_or`/`vars_and`, `Finset.subset_inter`, explicit `calc`.

**Verification**: `lake build …LJ.Interpolation` green with **zero `sorry`**; optionally
`lean_verify Cslib.Logic.PL.ljMaeharaCore`. If a case cannot close, mark `[BLOCKED]` with the exact
`lean_goal` — never `sorry`-defer.

**Checklist**:
- [ ] `orL` closed (single-conclusion combination).
- [ ] `impL` closed (single-conclusion combination).
- [ ] `lake build …LJ.Interpolation` green; **`ljMaeharaCore` zero `sorry`**.

**Depends on**: C1.

**Timing**: 1.5 hours (~70–100 lines).

---

### Phase C3: LJ Craig corollary + public `LJProof.interpolation` + barrel [NOT STARTED]

**Goal**: Finish the LJ corollary and public theorem; wire the `LJ.lean` barrel.

**Scope**: Append to `LJ/Interpolation.lean`: (1) LJ Craig corollary from `ljMaeharaCore`, yielding
`I` with `Γ₁ ⊢ I`, `insert I Γ₂ ⊢ C`, `vars I ⊆ vars Γ₁ ∩ vars(Γ₂ ∪ {C})`. (2) Public
`LJProof.interpolation` fed by `LJProof.cutElim`. (3) Add `public import …LJ.Interpolation` to
`LJ.lean`.

**Target files**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean` (append corollary).
- `Cslib/Logics/Propositional/SequentCalculus/LJ.lean` (barrel import).

**Key lemmas/idioms to reuse** (decomposition §1 LJ Craig MECHANICAL):
- `LJProof.cutElim` (`LJ/CutElimination.lean`) → cut-free LJ proof.
- Docstrings on new public decls (docBlame).

**Verification**: `lake build Cslib.Logics.Propositional.SequentCalculus.LJ` green (covers barrel);
optionally `lean_verify Cslib.Logic.PL.LJProof.interpolation` — no `sorry`, no new axioms.

**Checklist**:
- [ ] LJ Craig corollary proven.
- [ ] Public `LJProof.interpolation` via `cutElim`, with docstring.
- [ ] `public import …LJ.Interpolation` added to `LJ.lean`.
- [ ] `lake build …SequentCalculus.LJ` green.

**Depends on**: C2.

**Timing**: 1 hour (~40–60 lines).

---

### Phase D: Final CI sweep across LK + LJ interpolation [NOT STARTED]

**Goal**: Whole-task green under the full CI pipeline; resolve lint/docstring/shake findings.

**Scope**: Run the complete CI pipeline from the worktree root and fix any findings across both new
files and the touched barrels.

**Target files**: `LK/Interpolation.lean`, `LJ/Interpolation.lean`, `LK.lean`, `LJ.lean` (fixes
only — lint/docstring/shake).

**Key commands/idioms** (decomposition §1 LJ Craig + CI):
- `lake build` (whole library), `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`.
- Resolve: docstrings on all new public `def`/`theorem` (docBlame); `@[simp]` LHS simpNF-valid;
  shake import minimization; `checkInitImports` for new file imports.
- `lean_verify` on `LKProof.interpolation`, `LJProof.interpolation`, `maeharaCore`,
  `ljMaeharaCore`: zero `sorry`, no new axioms.

**Verification**: all five CI commands green.

**Checklist**:
- [ ] `lake build` (whole library) green.
- [ ] `lake test` green.
- [ ] `lake exe checkInitImports` green.
- [ ] `lake exe lint-style` green.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` clean.
- [ ] `lean_verify` on all four decls: zero `sorry`, no new axioms.

**Depends on**: B, C3.

**Timing**: 1 hour (CI fixes).

---

## Testing & Validation

- [ ] `lake build` — whole library compiles, including both `Interpolation.lean` files and barrels.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe checkInitImports` — import discipline holds for new files.
- [ ] `lake exe lint-style` — style/docstring linters pass.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no redundant imports.
- [ ] `lean_verify` on `maeharaCore`, `ljMaeharaCore`, `LKProof.interpolation`,
      `LJProof.interpolation`: zero `sorry`, no new axioms.

## Artifacts & Outputs

- `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` — `maeharaCore` sorry-free + LK
  Craig corollary + `LKProof.interpolation` (Phases A1–A4, B).
- `Cslib/Logics/Propositional/SequentCalculus/LJ/Interpolation.lean` — NEW: `ljMaeharaCore` + LJ
  Craig corollary + `LJProof.interpolation` (Phases C1–C3).
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean`, `…/LJ.lean` — barrel imports updated.
- `specs/374_sequent_calculus_interpolation/summaries/02_interpolation-divided-summary.md` — summary
  (on completion).

## Rollback/Contingency

- Every phase is additive and file-scoped. LK rollback: revert the per-case edits in
  `LK/Interpolation.lean` (the file is GREEN with `sorry` at any A-phase boundary) and remove the
  `LK.lean` barrel line. LJ rollback: delete the new `LJ/Interpolation.lean` and remove the `LJ.lean`
  barrel line. No existing definitions are modified.
- **ZERO-DEBT policy**: a phase is done only at a green build with no `sorry` in the cases it owns. If
  a case cannot close, mark the phase `[BLOCKED]` with the exact stuck goal state captured via
  `lean_goal` — **never** `sorry`-defer.
- Concurrent-agent safety: each phase builds only its specific owned module; LK and LJ tracks touch
  disjoint files.
