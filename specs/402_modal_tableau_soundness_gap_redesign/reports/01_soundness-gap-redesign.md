# Research Report: Modal Tableau Soundness-Gap Definitional Redesign

- **Task**: 384 - modal_tableau_soundness_gap_redesign
- **Started**: 2026-06-28T00:00:00Z
- **Completed**: 2026-06-28T00:00:00Z
- **Effort**: ~3 hours (design-evaluation research)
- **Dependencies**: Task 364 (blocked; this task resolves its definitional blocker)
- **Sources/Inputs**:
  - `specs/364_modal_tableau_soundness_drift_repair/handoffs/verified-counterexample.lean` (compiles)
  - `specs/364_.../summaries/02_soundness-gap-summary.md`, `.../.orchestrator-handoff.json`
  - `Cslib/Logics/Modal/Tableau/{Branch,Rules,Saturation,Soundness}.lean` (read in full / targeted)
  - `references.bib`
- **Artifacts**: `specs/384_modal_tableau_soundness_gap_redesign/reports/01_soundness-gap-redesign.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Project Context

- **Upstream Dependencies**: `Cslib/Logics/Modal/Tableau/Branch.lean` (`modalNextWorld`, `modalMaxWorld`, `Accessibility`), `Rules.lean` (`modalApplyOne`), `Saturation.lean` (`modalStepBranch`, `modalExpandBranches`, `modalTableau`).
- **Downstream Dependents**: NONE outside `Cslib/Logics/Modal/Tableau/`. Verified: `grep -rln "modalExpandBranches\|modalTableau"` over `Cslib/` returns only `Saturation.lean` and `Soundness.lean`. No `Tableau/Completeness.lean` exists yet; `Modal/Metalogic/Completeness.lean` does not import the tableau. The redesign is fully contained to two files.
- **Alternative Paths**: Per-branch `Accessibility` (Option A, recommended) vs global fresh-world counter (Option B, rejected) vs global coupling invariant (Option C, rejected).
- **Potential Extensions**: A future `Tableau/Completeness.lean` will consume `openBranch b acc`; the recommended change keeps that constructor's type verbatim.

## Executive Summary

- **Recommendation: Option A (per-branch `Accessibility`).** Thread a parallel `accs : List Accessibility` (one per worklist branch) through `modalExpandBranches`/`processNext`. Each branch's existential rules mutate only its own `acc`; sibling branches' accessibility relations become immutable during another branch's expansion. This eliminates the cross-branch edge pollution **by construction**.
- **Option B (global monotone counter) does NOT close the gap** and must be rejected. The counter makes fresh *target* worlds globally unique (fixing obligation 2 / freshness), but the pollution travels through the **shared *source* world** `w = sf.label`, which pre-exists in sibling branches. Obligation 3 (`branchSatisfiable bp acc → branchSatisfiable bp newAcc`) remains FALSE under any shared-`acc` design because `branchSatisfiable` is anti-monotone in `acc` while a shared `acc` only grows. See Adversarial Self-Verification.
- **The big win:** Option A leaves `modalStepBranch_preserves_sat` (the ~1450-line core semantic lemma, `Soundness.lean:187`–`1635`) **and** `modalApplyOne`, `modalStepBranch`, `branchSatisfiable`, `accFreshInv`, `modalNextWorld` **unchanged**. Only `modalExpandBranches`/`processNext` (signature) and `modalExpandBranches_closed_unsat` (reformulated loop invariant) change, plus `modalTableau_sound`'s call site (one line).
- **PUBLIC API preserved verbatim:** `modalTableau`, `kValid`, `modalTableau_sound`, `ModalTableauResult`, `openBranch` signatures are unchanged.
- **New proof obligations are small and all in the "TRUE/provable" class:** two `modalMaxWorld`/`modalNextWorld` monotonicity facts plus one maintenance lemma `modalStepBranch_preserves_accFreshInv` (obligation 1 from task 364, already classified provable). Obligations 2 and 3 (the FALSE ones) **vanish** because no sibling shares the mutated `acc`.
- **Task 364's committed drift repairs survive unchanged** (recognizer arms in `modalApplyOne`, `.{v,u}` universe pins on `branchSatisfiable`/`preserves_sat`, the Root-A `boxPos` `split_ifs` fix at line 228) — all live in defs/theorems untouched by Option A.
- **H3 citation finding:** the source files cite `[Fitting1983]` and `[Smullyan1968]`, but **neither BibKey exists** in `references.bib`. Only an unrelated `Fitting1969` ("Intuitionistic Logic, Model Theory and Forcing") is present, and there is no Smullyan entry. These keys must be added (see Recommendations).

## Context & Scope

The task-364 blocker (`Soundness.lean:1744/1749/1770`, succ-case of `modalExpandBranches_closed_unsat`) is a genuine soundness-proof hole, not transcription drift. This report evaluates the minimal correct **definitional** change and maps its downstream proof impact, so a planner can produce an implementation plan.

### The defect, grounded (4-element form)

- **Counterexample (build-verified):** `verified-counterexample.lean` compiles, proving
  `branchSatisfiable bp Accessibility.empty ∧ ¬ branchSatisfiable bp (Accessibility.empty.addEdge 0 1)`
  for `bp = [T(□p)@0, T(□(p→⊥))@0]`. Branch `bp` is satisfiable at a dead-end world 0 (both boxes vacuous), but adding successor 1 forces both `p` and `¬p` at world 1.
- **Current behavior:** `modalExpandBranches` (`Saturation.lean:131`) threads a **single shared `acc`** (`Saturation.lean:134`, `:159` `currAcc`, `:166` `newAcc`) through all worklist branches, while `modalApplyOne` (`Rules.lean:92,118`) numbers each fresh world `w' := modalNextWorld b` **per the branch `b` being expanded** (`Branch.lean:98`). The edge `(w, w')` is committed to the shared `acc` and is thereafter visible to every sibling branch in the worklist.
- **Required behavior:** A branch is an independent attempted model; its accessibility relation must record only the existential rules fired **on that branch**. Sibling branches must not inherit one another's edges.
- **Isolation:** The succ-case proof (`Soundness.lean:1740`–`1770`) reduces to three obligations on the post-step shared accumulator. Obligation 1 (`accFreshInv b' newAcc` for `b' ∈ newBs`) is provable; obligations 2 (`accFreshInv bp acc → accFreshInv bp newAcc`) and 3 (`branchSatisfiable bp acc → branchSatisfiable bp newAcc`) are FALSE for carried siblings `bp` — obligation 3 is the build-verified counterexample.

## Findings

### F1 — Why the shared-`acc` design is unsound *in principle*, not merely hard to prove

`branchSatisfiable b acc` (`Soundness.lean:64`) requires a model whose relation **extends** `acc` (`:68` `∀ w w', acc.hasEdge w w' → m.r (f w) (f w')`). Hence `branchSatisfiable` is **anti-monotone in `acc`**: adding edges can only destroy satisfiability. Under a shared `acc` that only grows, the loop must conclude `¬branchSatisfiable bp acc` (small `acc`) for a carried sibling, but the recursion only delivers `¬branchSatisfiable bp newAcc` (larger `acc`). The needed bridge is the contrapositive `branchSatisfiable bp acc → branchSatisfiable bp newAcc` — exactly the direction the counterexample refutes. **No shared-`acc` scheme can close this**, because the source world `w` of the foreign edge pre-exists in `bp`. This is the decisive discriminator between the options.

### F2 — Option A (per-branch `Accessibility`) — RECOMMENDED

Thread a parallel `accs : List Accessibility`, one entry per worklist branch, mirroring the existing parallel-list pattern (`branches` ∥ `expandedSets`, with their length invariant). When a branch is expanded into `newBs` with `newAcc`, its single `accs` slot is replaced by `List.replicate newBs.length newAcc` (for branching rules `newAcc = acc` unchanged, so all children share the parent acc; for fresh-world rules there is exactly one child). Carried siblings keep their own `accs` entries untouched.

This removes the pollution mechanism: no sibling's `acc` is ever mutated by another branch's rule. Obligations 2 and 3 **disappear** (siblings' `acc` is constant across a foreign expansion, so `¬branchSatisfiable bp accs[j]` is preserved with zero work). Only obligation 1 (local maintenance for `newBs`) remains, and it is provable.

#### F2.1 — Minimal definitional changes (Option A)

1. **`Saturation.lean:131` `modalExpandBranches`** — add `(accs : List Accessibility)` parameter; drop the single `(acc : Accessibility)`:
   ```lean
   def modalExpandBranches
       (branches     : List (List (SignedFormula (Proposition Atom) WorldIndex)))
       (expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
       (accs         : List Accessibility)          -- NEW: parallel, |accs| = |branches|
       (fuel : Nat) : ModalTableauResult Atom
   ```

2. **`Saturation.lean:145` `processNext`** — carry per-branch acc in both `pending` and `done` lanes:
   ```lean
   let rec processNext
       (pending     : List (List (SignedFormula (Proposition Atom) WorldIndex)))
       (pendingExp  : List (List (SignedFormula (Proposition Atom) WorldIndex)))
       (pendingAccs : List Accessibility)           -- NEW
       (done        : List (List (SignedFormula (Proposition Atom) WorldIndex)))
       (doneExp     : List (List (SignedFormula (Proposition Atom) WorldIndex)))
       (doneAccs    : List Accessibility)           -- NEW
       : ModalTableauResult Atom :=
     match pending, pendingExp, pendingAccs with
     | [], _, _ => .closed
     | b :: restBs, e :: restEs, a :: restAs =>
       if isModalClosed b then
         processNext restBs restEs restAs (done ++ [b]) (doneExp ++ [e]) (doneAccs ++ [a])
       else
         match modalStepBranch b e a with                       -- use this branch's own acc `a`
         | none => .openBranch b a                              -- return THIS branch's acc
         | some (newBs, newExps, newAcc) =>
           modalExpandBranches
             (done ++ newBs ++ restBs)
             (doneExp ++ newExps ++ restEs)
             (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)   -- NEW
             fuel'
     | _, _, _ => .closed   -- malformed (length invariant rules this out)
   ```
   The fuel-`0` case (`Saturation.lean:137`-`142`) zips `branches`/`expandedSets` only for openness; it needs no `accs` for the openness test but should return `accs[i]` for the chosen branch — i.e. zip `branches.zip accs` and return `.openBranch b a`.

3. **`Saturation.lean:185` `modalTableau`** — initial call passes a singleton accs list:
   ```lean
   def modalTableau (φ : Proposition Atom) : ModalTableauResult Atom :=
     modalExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty] (modalFuel φ)
   ```
   **Public type unchanged.**

4. **`ModalTableauResult` / `openBranch`** (`Saturation.lean:76`-`81`) — **unchanged**; `openBranch` still `Branch → Accessibility → Result`, now carrying the branch-local acc.

5. **`modalStepBranch` (`Saturation.lean:99`), `modalApplyOne` (`Rules.lean:68`), `modalNextWorld`/`modalMaxWorld` (`Branch.lean:92,98`)** — **all unchanged.** `modalStepBranch` already takes one `acc` and returns one `newAcc`; under Option A it is simply called with the branch's own slot.

#### F2.2 — New freshness-MAINTENANCE lemmas required (Option A)

None of these exist today (only `accFreshInv_empty` at `Soundness.lean:172` and `modalNextWorld_gt` at `Branch.lean:104`). Add to `Branch.lean` (helpers) and `Soundness.lean` (maintenance):

```lean
-- Branch.lean: monotonicity of the running max under list growth (prepend).
lemma modalMaxWorld_le_append (xs b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    modalMaxWorld b ≤ modalMaxWorld (xs ++ b)
-- corollary
lemma modalNextWorld_le_append (xs b : …) :
    modalNextWorld b ≤ modalNextWorld (xs ++ b)

-- Branch.lean: membership bound (already essentially `key2` inside modalNextWorld_gt).
lemma label_le_modalMaxWorld {sf} (h : sf ∈ b) : sf.label ≤ modalMaxWorld b

-- Soundness.lean: THE maintenance lemma (task-364 "obligation 1", provable).
lemma modalStepBranch_preserves_accFreshInv
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hInv  : accFreshInv b acc) :
    ∀ b' ∈ newBs, accFreshInv b' newAcc
```
**Proof sketch of `modalStepBranch_preserves_accFreshInv`:** unfold `modalStepBranch`/`modalApplyOne`, case on the fired rule.
- *Prop rules / boxPos / diamondNeg* (`newAcc = acc`): each `b' = newForms ++ b` (or a `.branching` child `br ++ b`). `accFreshInv b' acc` follows from `hInv` plus `modalNextWorld_le_append` (edges `< modalNextWorld b ≤ modalNextWorld b'`).
- *diamondPos / boxNeg* (`newAcc = acc.addEdge w w'`, `w = sf.label`, `w' = modalNextWorld b`, single child `b' = witness :: … ++ b` with `witness.label = w'`): old edges still `< modalNextWorld b ≤ modalNextWorld b'`; the new edge `(w, w')` has `w = sf.label < modalNextWorld b` (`modalNextWorld_gt`, `sf ∈ b`) and `w' = modalNextWorld b < modalNextWorld b'` because `witness ∈ b'` has label `w' = modalNextWorld b`, so `modalMaxWorld b' ≥ w'`, hence `modalNextWorld b' ≥ w' + 1 > w'`.

#### F2.3 — Downstream proof impact, theorem by theorem (Option A)

| Symbol | File:line | Change |
|---|---|---|
| `branchSatisfiable` | `Soundness.lean:64` | **None** (already per-call `acc`). |
| `accFreshInv` | `Soundness.lean:165` | **None** (already per-branch). |
| `accFreshInv_empty` | `Soundness.lean:172` | **None.** |
| `modalClosed_unsat` | `Soundness.lean:101` | **None.** |
| `modalStepBranch_preserves_sat` | `Soundness.lean:187`-`1635` | **None.** Statement and ~1450-line proof reused verbatim — its hypotheses are already `hsat : branchSatisfiable b acc` and `hInv : accFreshInv b acc`, both per-branch. |
| `modalExpandBranches_closed_unsat` | `Soundness.lean:1646`-`1770` | **Reformulated** (new loop invariant; see below). |
| `kValid` | `Soundness.lean:1775` | **None.** |
| `modalTableau_sound` | `Soundness.lean:1787`-`1813` | **Call-site only** (pass singleton accs; drop the now-unneeded fixed-`acc` `hstep` lambda or adapt it to the per-branch form). Public statement unchanged. |

**Reformulated `modalExpandBranches_closed_unsat` (the meat).** Replace the single `acc` + flatMap-level invariant (`Soundness.lean:1650,1652`) and the unthreadable fixed-`acc` `hstep` hypothesis (`:1653`-`1658`) with a zipped per-branch invariant. Recommended statement (using `List.Forall₂`, a Mathlib reuse — see Reuse Check):
```lean
theorem modalExpandBranches_closed_unsat (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      List.Forall₂ (fun b acc => accFreshInv b acc) branches accs →   -- per-branch freshness
      modalExpandBranches branches expandedSets accs fuel = .closed →
      List.Forall₂ (fun b acc => ¬ branchSatisfiable.{v, u} b acc) branches accs
```
Key structural simplifications vs. the current broken attempt:
- The semantic-preservation step is **no longer a hypothesis**; call `modalStepBranch_preserves_sat` directly (it is ∀-closed over `acc`). This removes the "fixed to one `acc` while recursion changes `acc`" defect that motivated dropping `hstep` in task 364.
- The freshness invariant threads via `modalStepBranch_preserves_accFreshInv` for the expanded slot, and is **unchanged** for carried siblings (their `accs[j]` is constant).
- The carried-sibling conclusion `¬branchSatisfiable bp accs[j]` is delivered directly by the inner/fuel IH at the **same** `accs[j]` — **no `acc→newAcc` lifting**, so obligations 2 and 3 never appear.

**`modalTableau_sound` initial-call obligations:** pass `accs := [Accessibility.empty]`; discharge `List.Forall₂ accFreshInv [F(φ)@0] [empty]` from `accFreshInv_empty` (`Soundness.lean:1801`-`1802` already proves the single-branch case). The `hsat` construction (`:1793`-`1799`) is reused verbatim.

#### F2.4 — Survival of task-364 committed drift repairs (Option A)

| Committed repair | Location | Survives? |
|---|---|---|
| Recognizer arms `.imp (.box (.imp φ .bot)) .bot` (diamondPos/diamondNeg) | `Rules.lean:91,142` | **Yes** — `modalApplyOne` unchanged. |
| `.{v, u}` universe pins | `branchSatisfiable`/`modalStepBranch_preserves_sat` (`Soundness.lean:195`,`:1656`) | **Yes** — signatures unchanged (the pin on the loop lemma migrates verbatim into the reformulated statement). |
| Root-A `boxPos` `split_ifs` drift fix (commit `425c1c53`, line ~228) | inside `preserves_sat` | **Yes** — that proof is reused whole. |
| recognizer-reduction strategy (report 04 / plan v05) | `preserves_sat` case analysis | **Yes** — unchanged. |

Only the **loop lemma + entry-point** are reworked; ~85% of the hard proof effort (the `preserves_sat` case analysis) is preserved.

### F3 — Option B (global monotone fresh-world counter) — REJECTED

Thread a strictly increasing `nextW : WorldIndex` through `modalExpandBranches`; have `modalApplyOne` use `w' := nextW` (not `modalNextWorld b`) and increment. Fresh **targets** become globally unique, so the global invariant `(∀ edge (a,c) ∈ acc, a,c < nextW) ∧ (∀ label ∈ flatMap branches, label < nextW)` is maintainable — this **does** fix obligation 2 (freshness). **But it does not fix obligation 3.** The foreign edge is `(w, nextW)` with **source** `w = sf.label`, a world that already exists in sibling `bp` (siblings descend from a common ancestor via propositional `.branching`, sharing labels). If `bp` carries `T(□p)@w, T(□¬p)@w`, then `branchSatisfiable bp (acc.addEdge w nextW)` forces `p ∧ ¬p` at `f nextW` and is FALSE, even though `nextW ∉ labels(bp)`. The counterexample's mechanism (anti-monotonicity through a **shared source world**) is untouched. Option B also requires changing `modalApplyOne`'s fresh-world source (`Rules.lean:92,118`) and re-deriving a `modalNextWorld_gt` analogue against `nextW` — strictly more def churn than A, for a non-fix. **Reject.**

### F4 — Option C (global coupling invariant) — REJECTED

Prove a stronger invariant coupling box-positive consistency across all worklist branches so cross-branch edges are provably harmless (handoff option C). This is a major bespoke proof redesign, does not simplify the algorithm, and leaves the algorithm structurally unsound (a satisfiable branch can still be spuriously closed by a foreign edge). **Reject** in favor of the structural fix A.

### F5 — Reuse check (CSLib-first, per protocol)

1. **CSLib Foundations** — `Accessibility` (`Branch.lean:54`), `SignedFormula`, `RuleResult`, `Model`, `Satisfies` already exist and are reused unchanged. No new modal abstraction needed.
2. **Typeclass hierarchy / notation** — no new notation or typeclass; the change is plumbing (an extra parallel list) plus one maintenance lemma.
3. **Mathlib instantiable version** — the zipped invariant is best expressed with **`List.Forall₂`** (Mathlib) rather than an index-based `∀ i, …` or hand-rolled `zip`/`∀ ∈ zip`; `List.Forall₂` ships congruence/length lemmas (`List.Forall₂.length_eq`, cons/append lemmas) that the induction needs. This is the one external reuse opportunity. (Index form `∀ i (h : i < …), accFreshInv branches[i] accs[i]` is an acceptable fallback if `Forall₂` append-splitting proves awkward in the `done ++ newBs ++ restBs` step.)
4. **Logics namespace** — concept is local to `Cslib.Logic.Modal.Tableau`; nothing to reuse elsewhere.

## Decisions

- **D1:** Adopt **Option A (per-branch `Accessibility` via a parallel `accs : List Accessibility`)**. Rationale: it is the unique option that removes the pollution mechanism by construction (F1, F3), preserves the public API and the ~1450-line `preserves_sat` proof, and keeps task-364's committed repairs.
- **D2:** Reject Option B (does not fix obligation 3; more def churn) and Option C (major redesign; algorithm still structurally unsound).
- **D3:** Use a parallel list `accs` (not a bundled `List (Branch × Exp × Acc)`) to minimize disruption to the existing length-invariant proof scaffolding. Bundling is a viable but larger refactor; note as alternative only.
- **D4:** Express the loop invariant with `List.Forall₂` (Mathlib reuse), index-form as fallback.

## Recommendations

Prioritized, planner-ready phase breakdown (each phase ≈ one agent run / one green build milestone):

1. **Phase 1 — Definitional plumbing (`Saturation.lean`).** Add `accs`/`pendingAccs`/`doneAccs`; update `processNext` arms, fuel-0 zip, and `modalTableau` entry. Target: file elaborates; `modalExpandBranches_closed_unsat` and `modalTableau_sound` will break (expected). ~100–150 lines changed. Owner: implementer.
2. **Phase 2 — Freshness helpers + maintenance lemma (`Branch.lean`, `Soundness.lean`).** Prove `modalMaxWorld_le_append`, `modalNextWorld_le_append`, `label_le_modalMaxWorld`, and `modalStepBranch_preserves_accFreshInv` (F2.2). Sorry-free; verify with `lake build Cslib.Logics.Modal.Tableau.Soundness` scoped where possible. ~80–150 lines.
3. **Phase 3 — Reformulate `modalExpandBranches_closed_unsat` (`Soundness.lean`).** New `List.Forall₂` statement; drop the fixed-`acc` `hstep` hypothesis; call `modalStepBranch_preserves_sat` + the Phase-2 maintenance lemma; thread `accs` through the fuel + pending inductions; carried siblings discharged at unchanged `accs[j]`. ~150–250 lines (the core; strictly simpler than the current broken attempt because obligations 2&3 are gone). **Highest risk phase.**
4. **Phase 4 — `modalTableau_sound` call site + full build.** Pass `[Accessibility.empty]`; discharge singleton `Forall₂` via `accFreshInv_empty`; confirm `kValid`/`modalTableau_sound`/`modalTableau` statements unchanged. Run full `lake build`, `lake exe checkInitImports`, `lake lint`. ~10–30 lines.
5. **Phase 5 — Citation hygiene (`references.bib`).** Add the missing `Fitting1983` (`@book{Fitting1983, author={Fitting, Melvin}, title={Proof Methods for Modal and Intuitionistic Logics}, publisher={Reidel}, year={1983}}`) and `Smullyan1968` (`@book{Smullyan1968, author={Smullyan, Raymond M.}, title={First-Order Logic}, publisher={Springer}, year={1968}}`) entries, which the four tableau files already cite but which are absent from `references.bib`. Small, independent; can run in parallel with Phases 1–4.

**Owners/next step:** `/plan 384` to convert this into a phased plan; dispatch Phases 1→4 sequentially (3 depends on 1+2; 4 on 3), Phase 5 in parallel.

## Adversarial Self-Verification (H4)

**Challenge 1 — "Does Option A actually eliminate the pollution scenario?"** Construct the post-change analogue of the counterexample. After the change, each worklist entry is `(b, e, acc_b)`. Suppose branch `bh` with `acc_bh` fires diamondPos at world `w`, producing the single child `b' = witness :: … ++ bh` with `acc' = acc_bh.addEdge w (modalNextWorld bh)`. The worklist becomes `done ++ [b'] ++ restBs` with accs `doneAccs ++ [acc'] ++ restAccs`. A carried sibling `bp = restBs[k]` keeps `acc_bp = restAccs[k]`, **unchanged**. The transition the counterexample needs — `branchSatisfiable bp acc → branchSatisfiable bp (acc.addEdge …)` — **never occurs**, because no rule ever rewrites `acc_bp`. The only `accFreshInv`/`branchSatisfiable` obligation at the new edge is for `b'` at `acc'`, which is obligation 1 (provable, F2.2). **Pollution is impossible by construction. Confidence: high.**

**Challenge 2 — "Could Option B be salvaged by a smarter proof?"** No. F1 shows `branchSatisfiable` is anti-monotone in `acc`; with any *shared* `acc` the loop must bridge from `¬sat at newAcc` to `¬sat at acc` (smaller), i.e. prove `sat at acc → sat at newAcc`, which the verified counterexample refutes whenever the foreign edge's **source** is shared. The global counter only controls **targets**. The refutation is independent of the counter. **Confidence: high that B is insufficient.**

**Challenge 3 — "Is the recommended reformulation provable, or am I moving the hole?"** The remaining obligations are: (i) `modalStepBranch_preserves_sat` — already proven in-tree, reused verbatim; (ii) `modalStepBranch_preserves_accFreshInv` — task 364's own handoff classifies this exact statement (obligation 1) as "TRUE / provable", and F2.2 gives a concrete case-by-case proof using `modalNextWorld_gt` (in-tree) + monotonicity (routine `List.foldl` inductions paralleling the existing `key`/`key2` in `modalNextWorld_gt`, `Branch.lean:108`-`130`). No obligation is known-false. **Confidence: high on provability; medium on effort estimate for Phase 3's induction bookkeeping over three parallel lists.**

**Challenge 4 — "Does any public statement secretly change?"** `modalTableau : Proposition Atom → ModalTableauResult Atom` (`:185`), `kValid` (`:1775`), `modalTableau_sound : modalTableau φ = .closed → kValid φ` (`:1787`), `ModalTableauResult`/`openBranch` (`:76`) — all unchanged; only internal `modalExpandBranches`/`processNext` arity grows. Verified no external consumer exists (`grep` over `Cslib/`). **Confidence: high.**

**Residual unknowns / honest caveats:**
- I assert the shared-`acc` *algorithm* (not just its proof) is structurally unsound (a satisfiable branch can be spuriously closed by a foreign edge, potentially making `modalTableau` wrongly report `.closed`). I have the build-verified satisfiability-breaking mechanism but did **not** build a full closing-tableau witness `φ` with `modalTableau φ = .closed ∧ ¬ kValid φ`. Plausible but **unverified**; not required for the recommendation, which fixes the soundness *proof* regardless.
- `List.Forall₂` append-splitting across `done ++ newBs ++ restBs` may be fiddly; the index-form fallback (D4) de-risks Phase 3.
- BibKey `Fitting1983`/`Smullyan1968` metadata (publisher/year above) should be confirmed against the canonical entries before committing Phase 5.

**Verification outcome:** No flaw found in Option A; Option B refuted with a concrete post-change pollution analysis. No `## Revised Direction` needed.

## Risks & Mitigations

- **R1 (Phase 3 induction bookkeeping over 3 parallel lists).** Mitigation: `List.Forall₂` with its length/append lemmas; index-form fallback; the proof is strictly simpler than the current broken one (two false obligations removed).
- **R2 (scoped build slowness on the 1817-line `Soundness.lean`).** Mitigation: prove Phase-2 helpers in `Branch.lean` (small, fast file) where possible; use `lean_goal`/`lean_multi_attempt` rather than repeated full builds; never call `lean_diagnostic_messages`.
- **R3 (accidental signature drift on the public API).** Mitigation: Phase 4 explicitly diffs `modalTableau`/`kValid`/`modalTableau_sound`/`openBranch` types against baseline.

## Context Extension Recommendations

- **Topic**: Per-branch vs shared accumulator in worklist tableau soundness proofs.
- **Gap**: No CSLib context documents the "accumulator must be branch-local because `branchSatisfiable` is anti-monotone in the accessibility relation" pattern; this trapped task 364 for multiple dispatch cycles.
- **Recommendation**: Add a short note under `.claude/extensions/cslib/context/` capturing the anti-monotonicity discriminator and the parallel-`accs` worklist pattern, for reuse by future tableau formalizations (Bimodal, Temporal).

## Appendix

- **References (BibKey status):**
  - `[Fitting1983]` — *Proof Methods for Modal and Intuitionistic Logics* (Reidel). Cited in `Branch.lean:37`, `Rules.lean:42`, `Saturation.lean:57`, `Soundness.lean:45`. **ABSENT from `references.bib`** — must be added.
  - `[Smullyan1968]` — *First-Order Logic* (Springer). Cited in `Rules.lean:43`, `Saturation.lean:58`. **ABSENT from `references.bib`** — must be added.
  - `references.bib:196` `Fitting1969` is a **different** work (*Intuitionistic Logic, Model Theory and Forcing*) and must not be substituted.
- **Source-to-implementation anchors (file:line):** `Accessibility.addEdge` `Branch.lean:64`; `modalNextWorld` `Branch.lean:98`; `modalNextWorld_gt` `Branch.lean:104`; `modalApplyOne` diamond/box fresh-world `Rules.lean:92,118`; shared-acc threading `Saturation.lean:131,159,166`; `branchSatisfiable` `Soundness.lean:64`; `accFreshInv` `Soundness.lean:165`; `modalStepBranch_preserves_sat` `Soundness.lean:187`; blocking succ-case `Soundness.lean:1740`-`1770`; `modalTableau_sound` `Soundness.lean:1787`.
- **Build-verified evidence:** `specs/364_modal_tableau_soundness_drift_repair/handoffs/verified-counterexample.lean` (compiles).
