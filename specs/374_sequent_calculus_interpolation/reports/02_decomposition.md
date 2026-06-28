# Task 374 Decomposition Study: Dividing the Remaining Interpolation Work

**Task:** 374 — Craig interpolation for propositional sequent calculi (LK + LJ) via Maehara's method
**Purpose:** Split the REMAINING work (research-plan Phases 3–6) into independently-implementable subtasks.
**Status:** researched (decomposition only — no implementation, no plan/state edits)
**Source under study:** `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` (GREEN, 4 deferred `sorry`)

---

## 0. Where the task actually stands (corrects the delegation brief)

Inspecting the live file, the state is slightly further along than "Phases 3–6 not started":

- **Phase 1 (vocabulary) is COMPLETE.** `Proposition.vars`, `Finset.vars`, and the *entire*
  rewrite battery already live in `Cslib/Logics/Propositional/Subformula.lean`:
  `vars_bot`, `vars_and`, `vars_or`, `vars_neg`, `vars_top`, and the Finset lifts
  `Finset.vars_empty/_singleton/_union/_insert/_subset_of_mem/_mono`
  (Subformula.lean:144,159–274). **No shared-prerequisite lemma subtask is needed** (see §3).
- **The LK `ax` leaf case is COMPLETE** (Interpolation.lean:264–307), with the full four-way
  `(A∈Γ₁?,A∈Δ₁?)` table producing `⊥ / A / ¬A / ⊤`. The Phase-2 summary's "5 sorries" is stale;
  the file now has exactly **4** `sorry` (andR:311, orL:315, impL:319, impR:323).
- The mechanical one-premise / leaf cases (`botL`, `weakL`, `weakR`, `andL`, `orR`) are all done
  and demonstrate a working, reusable per-case pattern (cover refinement via `Finset.insert_union`,
  side-split via `Finset.mem_union`, vars bound via `Finset.vars_union`/`vars_mono`/calc).

So the genuinely remaining work is: **the 4 LK `maeharaCore` cases**, the **LK Craig corollary +
public theorem + barrel**, and the **entire LJ development** (new file: core + corollary + barrel + CI).

---

## 1. Per-obligation difficulty assessment (grounded in goal states / available lemmas)

### LK `maeharaCore` remaining cases

**`impR A B` (one premise) — MODERATE (M/H).** Goal state (line 323): principal `A→B ∈ Δ`,
single premise `d' : insert A Γ ⊢ₛ insert B Δ`. This is the *easiest* of the four: it mirrors the
already-completed `andL`/`orR` one-premise pattern. The only new wrinkle is that `A` must be moved
to the antecedent side and `B` to the succedent side of the *same* chosen partition half (whereas
`andL` moves both auxiliaries to one antecedent side). Side-split on `A→B ∈ Δ₁ ∨ Δ₂`; apply the IH
to `d'` with the refined cover `insert A Γ_k` / `insert B Δ_k`; reuse the interpolant `I`; reapply
`LKProof.impR`. Reassembly identities discharge via `Finset.insert_union` + the `mono`-with-`hperm`
trick already used at andL:204. `vars` bound unchanged (A,B are subformulas of `A→B`). **Should be a
warmup, not a blocker.**

**`andR A B` (two premises) — HARD (H), the template case.** Goal state (line 311): principal
`A∧B ∈ Δ`, two premises `d₁ : Γ ⊢ₛ insert A Δ`, `d₂ : Γ ⊢ₛ insert B Δ`, with `ih₁ : CutFree d₁ → …`,
`ih₂ : CutFree d₂ → …` (feed `hcf.1`/`hcf.2`; `CutFree (andR …) = CutFree d₁ ∧ CutFree d₂`). This is
the first place two interpolants must be *combined*: get `I₁` from `ih₁`, `I₂` from `ih₂` (both with
`A`/`B` placed on the side of `A∧B`); then
`A∧B ∈ Δ₁ ⟹ I = I₁ ∨ I₂`, `A∧B ∈ Δ₂ ⟹ I = I₁ ∧ I₂`. The two half-derivations must be reassembled
**and re-combined**: e.g. for `A∧B∈Δ₁` the left half builds `Γ₁ ⊢ₛ insert (I₁∨I₂) Δ₁` by reapplying
`orR`/`andR` and `LKProof.mono` to the two IH derivations; the right half combines via the dual rule.
The vars bound needs `vars (I₁∘I₂) = vars I₁ ∪ vars I₂` (via `vars_or`/`vars_and`) and
`Finset.subset_inter` over both. This is the core novel proof engineering of Phase 3.

**`orL A B` (two premises) — HARD (H), mirror of `andR`.** Antecedent-side dual: principal
`A∨B ∈ Γ`, premises `insert A Γ ⊢ₛ Δ`, `insert B Γ ⊢ₛ Δ`; `A∨B∈Γ₁ ⟹ I=I₁∨I₂`, `∈Γ₂ ⟹ I=I₁∧I₂`.
Once `andR`'s combination template exists, `orL` is largely a transcription with the partition side
swapped (antecedent rather than succedent). Difficulty drops to M/H **if andR is done first**.

**`impL A B` (two premises) — HARDEST (H+).** Goal state (line 319): principal `A→B ∈ Γ`, with
**asymmetric** premises `d₁ : Γ ⊢ₛ insert A Δ` (A added to *succedent*) and
`d₂ : insert B Γ ⊢ₛ Δ` (B added to *antecedent*). Unlike `andR`/`orL` the two premises live on
opposite sides, so the two IH calls use different cover shapes, and the interpolant combination
(`I₁∧I₂` vs `I₁∨I₂` by side of `A→B`) must respect both. Reassembling both halves and reapplying
`LKProof.impL` is the most intricate single goal in the whole task.

### LK Craig corollary + public theorem

**MECHANICAL (M).** From a cut-free proof of `∅ ⊢ₛ {A→B}`, invert via `impR` to `{A} ⊢ₛ {B}`, then
apply `maeharaCore` with `Γ₁={A}, Δ₂={B}, Γ₂=Δ₁=∅`; specialize the bound to
`vars I ⊆ vars A ∩ vars B`; package as `⊢ A→I`, `⊢ I→B` via `impR`. The public
`LKProof.interpolation` feeds an arbitrary proof through `LKProof.cutElim`
(CutElimination.lean:839, `(d : LKProof seq) : Nonempty (CutFreeLKProof seq)`). All inputs exist;
only `vars_empty`/`Finset.union_empty` bookkeeping. ~50–70 lines.

### LJ `ljMaeharaCore` (new file)

**HARD (H), ~0.7× re-run of LK.** All infrastructure confirmed present:
`LJProof` (Basic.lean:86, 11 ctors `ax,botL,andL,andR,orL,orR1,orR2,impL,impR,weakL,cut`),
single-sided `LJProof.mono (hL : Γ ⊆ Γ')` (Basic.lean:158), `LJCutFree` (Basic.lean:193),
`LJProof.cutElim` (CutElimination.lean:674). The succedent is a *single* `Proposition` and is
**not** partitioned (antecedent-only cover `Γ = Γ₁ ∪ Γ₂`; interpolant sequents
`Γ₁ ⊢ I`, `insert I Γ₂ ⊢ C`). Consequences:
- Right rules `orR1`,`orR2`,`andR`,`impR` act on the unsplit succedent → **one-premise pass-through**,
  *simpler* than LK (the interpolant is threaded unchanged).
- `ax` leaf is simpler than LK: single conclusion means no `¬A` succedent-crossing trick.
- `andL`,`weakL`,`botL` mirror LK one-premise cases.
- **`orL` and `impL` remain the hard two-premise cases**, analogous to LK Phase 3, plus the
  intuitionistic constraint that the right sequent stays single-conclusion.
Because `LKProof`/`LJProof` index shapes differ, the LK core **cannot be instantiated** for LJ — it
is a genuine parallel re-implementation (confirmed by research §6). Only `Proposition.vars` + the
proof *architecture* are shared.

### LJ Craig corollary + CI

**MECHANICAL (M).** Analogous to the LK corollary from `ljMaeharaCore`, fed by `LJProof.cutElim`;
plus barrel wiring (`LJ.lean`) and the full CI sweep (`lake build/test/checkInitImports/lint-style/shake`).
~40–60 lines + lint fixes (docstrings on new public decls, simpNF, shake import minimization).

---

## 2. Recommended division — 3 subtasks (primary)

The dominant structural fact: **LJ depends only on the already-complete vocabulary (Phase 1), not on
the LK chain.** So LK and LJ are two independent tracks touching disjoint files and can run in
parallel under a territory contract. The recommended split:

### Subtask 374-A — "Complete LK `maeharaCore` (the four hard cases)"
- **Scope:** close all four `sorry` in `maeharaCore`: `impR`, `andR`, `orL`, `impL`.
- **Internal order:** `impR` (warmup) → `andR` (build the two-premise combination template) →
  `orL` (mirror andR, antecedent side) → `impL` (asymmetric, hardest).
- **Target module:** `Cslib/Logics/Propositional/SequentCalculus/LK/Interpolation.lean` (only).
- **Depends on:** nothing new — operates on the current GREEN file; all `vars` lemmas + `mono` +
  `Finset.insert_union`/`mem_union` already present.
- **Size / difficulty:** ~150–220 lines, **H** (carries essentially all remaining LK risk).
- **Sorry-free-able independently?** Yes — research §4/§9 confirm no missing infrastructure; the
  obstacle is bookkeeping length, not provability. End state: `maeharaCore` fully `sorry`-free, green.

### Subtask 374-B — "LK Craig corollary + public `LKProof.interpolation` + barrel"
- **Scope:** implication-form Craig corollary from `maeharaCore`; top-level `LKProof.interpolation`
  via `LKProof.cutElim`; add `public import …LK.Interpolation` to `LK.lean`.
- **Target modules:** `…/LK/Interpolation.lean` (append) + `…/SequentCalculus/LK.lean`.
- **Depends on:** 374-A (needs `maeharaCore` green).
- **Size / difficulty:** ~50–70 lines, **M** (mechanical specialization).
- **Sorry-free-able independently?** Yes.

### Subtask 374-C — "LJ interpolation end-to-end (new file: core + corollary + barrel + CI)"
- **Scope:** new `…/LJ/Interpolation.lean` containing `ljMaeharaCore` (single-conclusion, all cases),
  the LJ Craig corollary, public `LJProof.interpolation` via `LJProof.cutElim`; add
  `public import …LJ.Interpolation` to `LJ.lean`; run the full CI pipeline as the final gate.
- **Target modules:** NEW `…/LJ/Interpolation.lean` + `…/SequentCalculus/LJ.lean`.
- **Depends on:** Phase-1 vocabulary only (DONE) — **independent of 374-A/B**; runs in parallel
  (disjoint files = clean territory contract). The *final* whole-library CI sweep should run after
  both tracks land (see order, §4).
- **Size / difficulty:** ~200–280 lines, **H** (LJ `orL`/`impL` are the hard two-premise cases).
- **Sorry-free-able independently?** Yes.

### Why 3 and not 2 or 4
- **vs 2 (merge B into A):** B is the natural "LK complete" payoff and is cheap, but A is the
  highest-risk dispatch; keeping the reliable corollary separate means it is not jeopardized if A
  needs a second pass. Acceptable to merge A+B if 374-A's agent finishes with budget to spare.
- **vs 4 (split A's two-premise trio, or peel a final-CI subtask):** see §4 fallbacks. Splitting A
  is the right move *only if* a single dispatch proves unable to land all four cases.

---

## 3. Shared prerequisites — none outstanding

The only cross-cutting dependency (the `vars` vocabulary both LK and LJ need) **already exists and is
complete** in `Subformula.lean` (§0). Therefore **no tiny shared-lemma subtask is required**. The
two-premise *combination* logic is sometimes imagined as shareable, but it is not: it is internal to
each `maeharaCore`/`ljMaeharaCore` and the LK (two-sided) vs LJ (single-conclusion) sequent shapes
make the combinator non-transferable. Each track carries its own.

---

## 4. Recommended implementation order

```
Wave 1 (parallel):   374-A  (LK hard cases)        374-C-core  (LJ ljMaeharaCore + corollary)
Wave 2:              374-B  (LK corollary+barrel)   374-C-tail  (LJ barrel)
Final gate:          full CI sweep (build/test/checkInitImports/lint-style/shake) — after BOTH land
```

- Launch **374-A** and **374-C** simultaneously (disjoint files: `LK/Interpolation.lean` vs new
  `LJ/Interpolation.lean` + respective barrels — no write conflicts).
- **374-B** follows 374-A.
- Put the **final whole-library CI sweep** as the last checkpoint of whichever subtask merges last
  (recommend assigning it to 374-C since it introduces a new file + barrel and is the natural
  "everything" gate); it must not run until both LK and LJ are green. If you prefer strict
  parallelism without that coupling, peel a tiny **374-D "final CI + barrels verification"** subtask
  depending on both 374-B and 374-C (this is the 4-subtask variant).

**Fallback if 374-A overflows one dispatch** (per the plan's own splitting note, but with `ax`
already done): split at the two-premise boundary —
- **374-A1:** `impR` + `andR` (establish the two-premise template) — closes 2 of 4 sorries.
- **374-A2:** `orL` + `impL` (apply the template) — closes the remaining 2 → core sorry-free.
374-A2 depends on 374-A1. Each ends at a green `lake build` of the file with the not-yet-done cases
held as clearly-labelled `sorry` (intermediate checkpoints only; the *task* is not done until zero).

---

## 5. Single biggest risk

**The two-premise interpolant-combination cases — `andR`, `orL`, and especially `impL` — in
374-A** (and their LJ mirrors in 374-C). Each must reassemble *both* half-derivations with
`LKProof.mono` + `Finset.insert_union` *and* prove the combined `vars (I₁∘I₂)` bound via
`Finset.subset_inter`/`vars_union`. `impL`'s asymmetric premises (`A` to succedent, `B` to
antecedent) make it the most intricate single goal in the task and the most likely BLOCK point.
Mitigation: build `andR` fully first as the reusable two-premise template, then transcribe `orL`
(side-swapped) and adapt `impL`; if a case cannot close, mark `[BLOCKED]` with the exact `lean_goal`
state — never `sorry`-defer (zero-debt policy).

---

## Appendix: verified infrastructure (file:line)

| Need | Location | Status |
|------|----------|--------|
| `Proposition.vars` + connective lemmas | `Subformula.lean:144,159–181` | present |
| `Finset.vars` + lift lemmas (`_union/_insert/_mono/_subset_of_mem/_empty/_singleton`) | `Subformula.lean:242–274` | present |
| LK `maeharaCore` (ax+mechanical cases done; 4 sorries) | `LK/Interpolation.lean:61–323` | partial |
| `LKProof.cutElim` | `LK/CutElimination.lean:839` | present |
| `LKProof.mono` | `LK/Basic.lean:143` (per report) | present |
| `LJProof` (11 ctors, single-conclusion) | `LJ/Basic.lean:86` | present |
| `LJProof.mono` (single-sided) | `LJ/Basic.lean:158` | present |
| `LJCutFree` | `LJ/Basic.lean:193` | present |
| `LJProof.cutElim` | `LJ/CutElimination.lean:674` | present |
| `LJ/Interpolation.lean` | — | does NOT exist (374-C creates) |
