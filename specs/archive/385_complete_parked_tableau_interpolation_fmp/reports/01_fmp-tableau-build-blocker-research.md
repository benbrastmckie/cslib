# Task 385 Research: IntFMPSpike Build Blocker + Tableau Scheme Sorries

**Status**: researched
**Date**: 2026-06-29
**Agent**: cslib-research-agent
**Scope**: Two sub-parts remain after task 395 reconciliation (LK/Interpolation DROPPED).
1. Fix + rename + rewire `IntFMPSpike.lean` → `IntDecidability.lean` (BUILD BLOCKER).
2. Close the parked sorries in `Tableau/Intuitionistic/Scheme.lean`.

---

## Executive Summary

- **The build blocker is FULLY SOLVED and VERIFIED.** I patched the file, built it scoped
  (`lake build Cslib.Logics.Propositional.Metalogic.IntFMPSpike` → **EXIT 0**, no `sorry`),
  then reverted to leave the tree clean. The complete verified patch is saved at
  `specs/385_complete_parked_tableau_interpolation_fmp/reports/intfmpspike-verified-patch.diff`.
- **The task's premise of "2 compile errors at lines 201/231" is INCOMPLETE.** Those are one
  parse error (`Σ` in an identifier) and its cascade. Fixing the parse error unmasked **five
  additional real errors** from Mathlib/module-system API drift during the merge (the Cslib.lean
  stub comment "drifted out of sync with the tableau/metalogic API" is accurate). All are now
  diagnosed with concrete fixes that compile.
- **Current build state diverges from the task description.** The import is **already commented
  out** at `Cslib.lean:420-422` (task 385 stub), so the repo currently builds *green*. Re-enabling
  the import requires the fixes below first.
- **Rename/rewire is trivial**: only `Cslib.lean` references the module in Lean (no
  `Propositional/Metalogic.lean` barrel exists). Rename file, fix import line, run `mk_all`.
- **Scheme.lean sorries are LIVE** (the committed `intuitionisticTableau_complete` transitively
  depends on all of them). There are **5 real sorries**, not 4: Scheme.lean:242/280/288/296 plus
  `Completeness.lean:112`. The truth lemma (242) and the IValid bridge (112) are explicitly the
  **task 317 core obligation** and should be coordinated, not forced into 385.

---

## Sub-Part 1: IntFMPSpike Build Blocker (FULLY RESOLVED)

### Root cause chain

The single *visible* error masked four more. The build halts at the first command-level parse
failure, so the rest were hidden. Fixing them one by one revealed the full set:

| # | Line (orig) | Error | Root cause | Fix (verified) |
|---|------|-------|-----------|----------------|
| 1 | 231/233/254/257/259 | `unexpected token 'Σ'; expected command` | Local hyp names `hψ'Σ`, `hab_Σ` contain `Σ`, which Lean's lexer **excludes** from identifiers (reserved for Σ-types, like `Π`/`λ`) | Rename to `hψ'mem`, `hab_sub` (all 5 sites) |
| 2 | 145-171 | type mismatch: IH arg `a.IsSubformula φ` vs expected `a ∈ L` | `intFinWorld_propConsistent` does ONE `induction ψ` but the docstring's documented **case split (`⊥∈Σ` vs `⊥∉Σ`) was never implemented**. `induction ψ` generalizes `hψ : ψ ∈ L`, so the IH wrongly demands `a ∈ L` for subformulas | Implement the documented case split (see below) |
| 3 | 177 | `simp [IForces] at this` made no progress | `IForces _ _ () ⊥` is defeq `False`; simp can't fire | Replace with `exact this` |
| 4 | 269 | `exact_mod_cast hξ` cannot infer target set | `int_subset_deductive_closure (S) : S ⊆ intDeductiveClosure S`; the membership arg's `↑w.carrier` coercion left `S` a metavariable | Introduce `hξset : ξ ∈ (↑w.carrier : Set _) := Finset.mem_coe.mpr hξ`, pass `int_subset_deductive_closure _ hξset` |
| 5 | 9-11 / 105-106 | `environment does not contain Finset.powerset`; `Finset.mem_powerset` | The merge dropped the transitive import of `Mathlib.Data.Finset.Powerset`; `subformulas : Finset` so `.powerset` no longer resolves | Add `public import Mathlib.Data.Finset.Powerset` |
| 6 | 141 | `Unknown constant Set.mem_coe` | `Set.mem_coe` renamed/removed in the Mathlib bump | Drop it; `simp only [Finset.mem_coe]` suffices |
| 7 | 101/114 | `Unknown identifier intFinWorld_carrier_injective` ("private ... would need to be public") | Module-system visibility: `private` lemma referenced by the `public` `Fintype` instance | Remove `private` from `intFinWorld_carrier_injective` |

### The non-trivial fix (error #2): `intFinWorld_propConsistent`

The current proof conflates two cases the docstring promises to handle separately. The verified
replacement (see the saved `.diff`) is:

```lean
  intro L hLsub hLderiv
  obtain ⟨d⟩ := hLderiv
  by_cases hbotmem : (⊥ : PL.Proposition Atom) ∈ φ.subformulas
  · -- ⊥ ∈ Σ: carrier ⊢ ⊥ and ⊥ ∈ Σ ⇒ ⊥ ∈ carrier (w.closed) ⇒ ⊥ (w.consistent)
    exact w.consistent (w.closed ⊥ hbotmem ⟨L, hLsub, ⟨d⟩⟩)
  · -- ⊥ ∉ Σ: every subformula is ⊥-free ⇒ all-True valuation forces L; soundness forces ⊥
    have h_forces_all : ∀ ψ ∈ L, IForces (fun _ _ => True) (fun _ => False) () ψ := by
      intro ψ hψ
      have hmem := hLsub ψ hψ
      simp only [Finset.mem_coe] at hmem
      have hwsub : ψ ∈ φ.subformulas := w.sub hmem
      clear hmem hψ
      -- world-polymorphic IH avoids `()` vs `PUnit.unit` defeq fragility in the imp case
      suffices hall : ∀ u : Unit, IForces (fun _ _ => True) (fun _ => False) u ψ from hall ()
      induction ψ with
      | atom p => intro u; simp [IForces]
      | bot => intro u; exact absurd hwsub hbotmem
      | imp a b iha ihb =>
        intro u
        exact fun u' _ _ => ihb (Proposition.IsSubformula.trans Proposition.IsSubformula.imp_right hwsub) u'
      | and a b iha ihb =>
        intro u; simp [IForces]
        exact ⟨iha (Proposition.IsSubformula.trans Proposition.IsSubformula.and_left hwsub) u,
               ihb (Proposition.IsSubformula.trans Proposition.IsSubformula.and_right hwsub) u⟩
      | or a b iha ihb =>
        intro u; simp [IForces]
        exact Or.inl (iha (Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hwsub) u)
    have := int_soundness d (fun _ _ => True) (fun {_ _} p _ _ => trivial) () h_forces_all
    exact this
```

Two subtleties that cost iterations (already resolved in the verified patch):
- **`clear hψ` is mandatory** before the induction so the IH carries only `a ∈ φ.subformulas`.
- **The `imp` case must NOT `simp [IForces]` then `exact ihb`** — `lake` (unlike the LSP) refuses
  the `() vs PUnit.unit` world defeq. The world-polymorphic `suffices ∀ u, ...` plus the direct
  term `fun u' _ _ => ihb (...) u'` (relying on definitional unfolding of imp-forcing) is robust
  across both `lake` and LSP.

### Remaining lint warnings (must clear for `lake lint` / `lake exe lint-style`)

After the fix the module is error-free; 8 lint warnings remain (all trivial):
`69:10` extra space; `107` unused binder names `w₁`/`w₂` (→ `_`); `153:100` line >100 chars;
`156`/`161` flexible `simp [IForces]` (→ `simp only [...]`); `225`/`226` unused simp args
(`Finset.mem_coe`, `Finset.mem_filter`). Note: line numbers refer to the *patched* file.

### Verification performed
- `lake build Cslib.Logics.Propositional.Metalogic.IntFMPSpike` → **EXIT 0** (errors), warnings only.
- `grep sorry` on the proof bodies → none (only the docstring word "sorry").
- The implementer should re-verify with full `lake build` after re-enabling the import, then
  `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake shake`.

---

## Rename + Rewire Plan: `IntFMPSpike.lean` → `IntDecidability.lean`

### Wiring (complete inventory)
- **Only Lean reference**: `Cslib.lean:420-422` (currently a 3-line stub comment + commented
  `public import ...IntFMPSpike`). There is **no `Cslib/Logics/Propositional/Metalogic.lean`
  barrel** (only `Modal/Metalogic.lean` and `Temporal/Metalogic.lean` exist; Propositional uses
  the root `Cslib.lean` barrel directly).
- Procedure: `git mv` the file → `IntDecidability.lean`; replace the stub block at Cslib.lean:420-422
  with `public import Cslib.Logics.Propositional.Metalogic.IntDecidability` in alpha order (it
  sits between `GenericMCSBridge` (419) and `IntLindenbaum` (423)); run
  `lake exe mk_all --module` to regenerate the barrel deterministically.

### "Spike / specs-370 framing" to strip
- Module docstring (lines 13-40): drop "Phase 1 De-Risking Spike", "scratch spike file for Task
  370", "go/no-go gate", "This file is NOT a committed deliverable", "On GO, the validated
  definitions are promoted to `IntDecidability.lean`". Rewrite as a normal module docstring
  describing the finite-world type + finite implication witness for IPC decidability/FMP.
- Section headers: line 179 `## Finite Imp Witness (Phase 1 Spike Target)` → drop "(Phase 1 Spike
  Target)"; line 181 docstring "(the Phase 1 spike target)" → remove.
- References (lines 37-39): the `specs/370_...` pointer is a spec-internal path; replace with the
  Fitting reference or the appropriate `references.bib` BibKey used elsewhere in the metalogic
  files (verify against `references.bib`), or remove if no published source applies.
- Declaration names (`IntFinWorld`, `intFinWorld_propConsistent`, `int_fin_imp_witness`,
  `intFinWorld_carrier_injective`, `instFintypeIntFinWorld`, `instPreorderIntFinWorld`) contain
  **no** "spike"/"370" tokens — no renames needed.

---

## Sub-Part 2: Tableau/Intuitionistic/Scheme.lean Sorries

### Critical context
- The 4 Scheme sorries are **live**: `Completeness.lean` `intTruthLemma` and
  `intuitionisticOpenBranch_countermodel` are thin wrappers delegating to `truthLemma intScheme`
  / `openBranch_countermodel intScheme`. So `intuitionisticTableau_complete` (committed) is
  transitively sorry-tainted today.
- There is a **5th live sorry**: `Completeness.lean:112` — the `IValid φ → per-branch forcing`
  bridge — explicitly "the core completeness obligation for task 317" (also needs upward-closure
  of `intExtractValuation b`). The Minimal track has analogous sorries
  (`Tableau/Minimal/Completeness.lean`).

### The four Scheme sorries

**(A) `truthLemma` (line 242) — the big one; DEFER / coordinate with task 317.**
Goal: parametric over `IntMinScheme S`, prove for all φ, w both directions
(`T(φ)@w ⇒ IForces`, `F(φ)@w ⇒ ¬IForces`) under `intExtractValuation b` / `S.modelBot b`. This is
the intuitionistic Kripke truth lemma (induction on φ, must handle persistence/monotonicity across
Nat-labelled worlds and the parametric `modelBot`; the `S.bot_truth` field exists specifically to
feed its bot case). Classical analogue is `classicalTruthLemma` but the Kripke version is
substantially harder. The Scheme + Completeness docstrings both tag this to task 317. **Recommend
NOT attempting standalone in 385** — it is shared infrastructure with 317 and risks scope blowup.

**(B/C/D) The three structural sorries in `openBranch_countermodel` (280/288/296).**
These connect `intExpandBranches ... = .openBranch b` to properties of `b`. They are about the
**expansion loop**, largely independent of the truth lemma. `intExpandBranches`
(`Intuitionistic/Expansion.lean:170`) has fuel=0 (`findSome?`) and `fuel'+1` cases with an inner
`go` recursive helper carrying **8 parallel lists** (pending/done × branches/exp/NW/edges) — more
complex than the classical `processNext` (4 lists). All three need induction on fuel + the `go`
helper.

| Sorry | Lemma needed | Tractability | Template / dependency |
|-------|--------------|-------------|-----------------------|
| **:296** `hFmem` (F(φ)@0 ∈ b) | `intExpandBranches_openBranch_initial_mem` | **Most tractable** | Direct template: `classicalExpandBranches_openBranch_initial_mem` (Classical/Completeness.lean:1164, ~100 lines). Requires a NEW `intStepBranch`/persistence membership-preservation helper (analogue of `classicalStepBranch_mem_preserved`, Classical:1120) plus monotonicity of `applyPersistenceFixpoint` and `Branch.extendMany` (both only ADD formulas). |
| **:280** `hopen` (`closurePred b = false`) | `intExpandBranches_openBranch_closed` | **Tractable** | Read directly off the guards: `.openBranch bPers` is returned only inside the `else` of `if closurePred bPers` (Expansion.lean:204-208), and the fuel=0 case via `findSome? (if closurePred b then none else some b)`. Induction on fuel + `go`. |
| **:288** `hsat` (`intStepBranch b [] 0 = none`) | `intExpandBranches_openBranch_sat` | **Hardest of the three; formulation risk** | `.openBranch bPers` is returned when `intStepBranch bPers e nw = none` for the *accumulated* expanded set `e` and next-world `nw`, but the truthLemma's `hsat` wants `intStepBranch b [] 0 = none` (empty set, world 0). Bridging requires expanded-set/world-independence of saturation, which may NOT hold verbatim — the classical proof sidesteps this via `classicalHintikkaSet` instead of a raw `intStepBranch = none`. **May require reformulating the `hsat` hypothesis of `truthLemma`** (coordinate with 317). `applyPersistenceFixpoint_sat` (Soundness.lean:411) is relevant supporting machinery. |

**Encouraging precedent**: `Intuitionistic/Soundness.lean` *already* performs induction on
`intExpandBranches.go` (lines 1166, 1212+) and has `applyPersistenceFixpoint_sat` /
`freshAbove_applyPersistenceFixpoint`. The implementer can mirror those go-induction patterns for
the new structural lemmas rather than inventing the recursion scheme from scratch.

### `:296` classical-analogue transfer assessment
`classicalExpandBranches_openBranch_initial_mem` transfers in **structure** but not verbatim:
the classical proof inducts on `processNext` (4 lists, `Unit` labels, no persistence/edges/world
creation); the int version must additionally thread `pendingNW`/`pendingEdges`/`doneNW`/`doneEdges`
and account for `applyPersistenceFixpoint bPers` (a fixpoint that only adds T(→)-consequences) and
world-creating linear rules. The core invariant ("sf ∈ every pending and done branch") and the
nested `induction fuel; suffices key ...; induction pending` skeleton port directly. Estimate
~120-180 lines including the prerequisite membership-preservation helper.

---

## Candidate Lemmas (mostly INTERNAL — reuse-first)

The proofs are dominated by induction over CSLib's own recursive definitions; Mathlib's role is
limited to Finset/List basics. Reuse targets, in priority order:

- **Internal templates (Classical track)**: `classicalExpandBranches_openBranch_initial_mem`,
  `classicalStepBranch_mem_preserved`, `classicalExpandBranches_hintikka`,
  `classicalOpenBranch_countermodel` (`Tableau/Classical/Completeness.lean:1120-1318`).
- **Internal supporting machinery (Int track)**: `applyPersistenceFixpoint_sat`,
  `freshAbove_applyPersistenceFixpoint`, and the existing `intExpandBranches.go` inductions in
  `Tableau/Intuitionistic/Soundness.lean:411,819,1166,1212`.
- **Mathlib (build-blocker, confirmed by build)**: `Finset.powerset`, `Finset.mem_powerset`,
  `Finset.mem_coe`, `Finset.filter_subset`, `Fintype.ofInjective` — all already used and resolve
  once `Mathlib.Data.Finset.Powerset` is imported.
- **Int Lindenbaum API used by the witness** (all verified present): `int_imp_witness`,
  `int_prime_exclusion`, `intDeductiveClosure_is_dccs`, `int_subset_deductive_closure`,
  `SetDerivable_weakening`, `int_dccs_bot_not_mem` (imported via `IntStrongCompleteness`/
  `IntLindenbaum`).

No new abstractions are recommended (reuse-first satisfied): the build-blocker fix reuses existing
APIs; the Scheme lemmas reuse the Classical-track templates and Int soundness machinery.

---

## Recommended Phase Breakdown for the Implementer

**Phase 1 — Build blocker (do first; FULLY SPEC'D & VERIFIED).**
Apply the saved `intfmpspike-verified-patch.diff` (7 edits), confirm scoped build EXIT 0, then
clear the 8 lint warnings. Self-contained; ~30 min. Zero sorries.

**Phase 2 — Rename + rewire.**
`git mv IntFMPSpike.lean IntDecidability.lean`; strip spike/370 framing from docstrings/headers;
replace Cslib.lean:420-422 stub with the real import; `lake exe mk_all --module`. Then full
`lake build` + `checkInitImports` + `lint-style` + `shake`. Depends on Phase 1.

**Phase 3 — Structural sorries `:296` then `:280`.**
Create `intExpandBranches_openBranch_initial_mem` (+ membership-preservation helper) and
`intExpandBranches_openBranch_closed`, mirroring the Classical templates and Soundness go-inductions.
Wire into `openBranch_countermodel`. These are within 385's scope.

**Phase 4 — `:288` sat — RESEARCH-OR-DEFER gate.**
Attempt `intExpandBranches_openBranch_sat`. If the `intStepBranch b [] 0 = none` formulation proves
unbridgeable from the accumulated-`e`/`nw` return condition, **mark [BLOCKED] for user review and
coordinate the `hsat` reformulation with task 317** — do NOT introduce a sorry or axiom.

**Phase 5 — `truthLemma` (:242) + `Completeness.lean:112` bridge — COORDINATE WITH TASK 317.**
These are explicitly 317's core obligation (Kripke truth lemma + IValid→forcing bridge + upward
closure of `intExtractValuation`). **Recommend handing off to / sequencing after task 317** rather
than absorbing into 385. If 317 has not delivered, 385 cannot eliminate these without violating
zero-debt; flag the dependency explicitly.

### Zero-debt note
`lake build` is *green today* because sorries warn (not error) and the spike is stubbed out. Task
385 can fully eliminate the build-blocker and Phase-3 sorries. The truthLemma/bridge sorries are
pre-existing and 317-scoped; eliminating them is gated on 317. No new sorries or axioms are
recommended anywhere — where a proof is not yet achievable (`:288` worst case, `:242`, `112`), the
recommendation is [BLOCKED]/coordinate, never deferral-by-sorry.

---

## Open Questions / Coordination
1. **Task 317 status**: Has 317 delivered the Kripke truth lemma and `intExtractValuation`
   upward-closure? This determines whether 385 closes 0, 2, or 4 Scheme sorries.
2. **`hsat` formulation**: Is the `intStepBranch b [] 0 = none` shape in `truthLemma`'s signature
   fixed, or can 385/317 jointly weaken it to the accumulated-set form the loop actually produces?
3. **References/BibKey**: confirm the correct `references.bib` key (Fitting1983 is used in
   Scheme.lean) for the rewritten `IntDecidability` module docstring.
