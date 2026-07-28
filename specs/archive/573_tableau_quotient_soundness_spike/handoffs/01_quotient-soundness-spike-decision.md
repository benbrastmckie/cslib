# Decision Record: Tableau Quotient Soundness Spike

**Verdict**: **GO**

**Scope**: This is a time-boxed GO/NO-GO research spike, not a proof effort. No file under
`Cslib/` was edited or committed. All prototyping happened in an uncommitted scratch file
(`specs/573_tableau_quotient_soundness_spike/scratch/QuotientSpike.lean`), deleted at the end of
this record's preparation, plus direct `lean_goal`/`lean_hover_info`/`lean_verify` queries
against the real, unmodified library.

---

## 1. Verdict

**GO.** The quotient-restated `IBranchSaturation.sat_fimp` (via a blocking-ancestor
representative map `rep : Nat → Nat`, restating the witness ordering as `rep w ≤ rep w'`
instead of raw `w ≤ w'`) combined with the ancestor-directed, `F(ψ)@x`-conjunct-dropping
containment check (`intFImpReuseWitnessAnc?`) is **compatible with
`intExpandBranches_closed_unsat`** (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean:1108`),
based on live Lean goal-state evidence for both sub-hypotheses:

- **H1 (predicate-content-agnosticism): CONFIRMED.**
- **H2 (soundness/saturation disjointness): CONFIRMED.**

### H1 evidence (decisive)

Live `lean_goal` capture at the **real, currently-passing** first reuse arm
(`Soundness.lean:1470`, the `-- Reuse:` bullet inside `intExpandBranches_closed_unsat`'s proof),
immediately after the discharging rewrite (`Soundness.lean:1476-1477`,
`rw [hwit] at hgo; simp only [] at hgo`), shows `hgo` reduced to:

```
hgo :
  intExpandBranches (done ++ [applyPersistenceFixpoint bh edgesP (fuel'' + 1)] ++ bt)
    (doneExp ++ [newExp] ++ eT) (doneNW ++ [nwH] ++ nwT)
    (doneEdges ++ [edgesP] ++ edgesT) fuel'' closurePred = IntTableauResult.closed
hwit : intFImpReuseWitness? bPers edgesP newForms e_val = some x
⊢ False
```

`x` (the reuse witness returned by `intFImpReuseWitness?`) appears **only** inside `hwit`'s
statement (which is never used again after the `rw`) — it does **not** appear in `hgo` or in the
goal. The recursive call in `hgo` receives `bPers`/`edgesP`/`nwH` **unchanged**. The mirror arm
(`Soundness.lean:1621-1626`, the `bp ∈ bt` case) shows the byte-identical pattern with
`edgesH` in place of `edgesP`.

To test this against the **actual swapped definitions** (not merely the original), the scratch
file defined:
- `intFImpReuseWitnessAnc?` — same signature (`Option Nat`), ancestor-directed accessibility
  (`isAccessible edges x w`, `x.ble w` in place of `isAccessible edges w x`, `w.ble x`), with the
  `F(ψ)@x` conjunct dropped.
- `intExpandBranchesAnc` — byte-identical copy of `intExpandBranches`'s `go` loop with
  `intFImpReuseWitness?` replaced by `intFImpReuseWitnessAnc?` at the one call site
  (`Expansion.lean:423` analogue).

An **isolated replay** of the first reuse arm was then constructed: an `example` whose local
context (all ~35 hypotheses: `ih`, `done`/`doneExp`/`doneNW`/`doneEdges`, `bt`/`edgesT`/`nwT`,
`bPers`/`edgesP`/`nwH`, `hfreshAbove_pers`, `hsat_p`, etc.) was copied verbatim, binder-for-binder,
from the live capture above, with `hwit`/`hgo` restated over `intFImpReuseWitnessAnc?`/
`intExpandBranchesAnc`. The **UNCHANGED** closing tactic block from `Soundness.lean:1478-1519`
(`rw [hwit] at hgo; simp only [] at hgo; have hsat_pers := applyPersistenceFixpoint_sat ...;
have hfreshCombReuse := ...; refine absurd hsat_pers (ih ...); ...`) was applied verbatim.

**Result** (`lean_goal` at the final tactic line, `exact Or.inr (by simp)`):

```json
"goals_before": ["... ⊢ (bPers, edgesP) ∈ done.zip doneEdges ∨ (bPers, edgesP) ∈ [bPers].zip [edgesP]"],
"goals_after": []
```

`goals_after: []` — **no goals**. The unchanged tactic block closes the reuse-arm obligation
against `intExpandBranchesAnc`/`intFImpReuseWitnessAnc?` exactly as it does against the
original. No goal at any intermediate step (`rw [hwit] at hgo`, `simp only [] at hgo`, the
`hfreshCombReuse` derivation, the final `ih` application) referenced `intFImpReuseWitnessAnc?`'s
definition body or an analogue of `intFImpReuseWitness?_spec`.

**Scope limitation on H1**: the second reuse arm (`Soundness.lean:1621` mirror, `bp ∈ bt` case)
was **not** independently re-closed under the swapped definitions — see Section 4 (Scope note).
The plan's own GO criterion requires only "at least one reuse arm closed," which is satisfied.

### H2 evidence

```
$ grep -c "IBranchSaturation" Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean
0
$ grep -n "sat_fimp\|intFImpReuseWitness?_spec" Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean
(no output)
```

`lean_verify` on `Cslib.Logic.PL.intExpandBranches_closed_unsat`:

```json
{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[]}
```

Only the three standard Mathlib axioms — no unexpected dependency. Structurally,
`intExpandBranches_closed_unsat`'s own statement (`Soundness.lean:1108-1131`) is fully generic
over an abstract `closurePred : IBranch Atom → Bool` and a `closed_unsat` hypothesis; it takes
no `IBranchSaturation`-typed parameter anywhere in its signature. `IBranchSaturation`/`sat_fimp`
are consumed only by *callers* one layer up (`Scheme.lean`'s `intExpandBranches_openBranch_sat`,
`intOpenBranch_countermodel`, etc.), never by `intExpandBranches_closed_unsat` itself. Restating
`sat_fimp` over a quotient (prototyped in the scratch file as `IBranchSaturationQ`, parameterized
by a blocking-ancestor representative map `rep : Nat → Nat`, elaborated cleanly with zero
diagnostics) therefore cannot touch this lemma's proof at all.

---

## 2. Downstream Instruction

**GREEN LIGHT.** The downstream calculus-repair task's quotient/rewrite step
(restating `IBranchSaturation.sat_fimp` over the blocking quotient, and replacing
`intFImpReuseWitness?` with an ancestor-directed, `Sfor`-containment-based
`intFImpReuseWitnessAnc?` that drops the `F(ψ)@x` conjunct) may proceed against
`intExpandBranches_closed_unsat` **without re-deriving branch-modification-sensitive soundness
machinery**, because:

1. `intExpandBranches_closed_unsat` is soundness-neutral with respect to the reuse predicate's
   *content* — it only depends on the *shape* of the `go`-loop's `some _x` match arm (recursing
   with `bPers`/`edges`/`nw` unchanged), which the ancestor-directed check preserves exactly.
2. `intExpandBranches_closed_unsat` never depends on `IBranchSaturation`/`sat_fimp` at all, so
   quotient-restating `sat_fimp` cannot regress this lemma.

**What this does NOT establish** (the repair task must still do this work; it is explicitly
out of scope for this spike — see Goals & Non-Goals in the plan):
- That `intFImpReuseWitnessAnc?` actually terminates the F1 divergence witness (the original
  motivating bug). This spike tested *soundness compatibility*, not *termination*.
- That `IBranchSaturationQ`/quotient `sat_fimp` is provable from an actual open, saturated
  branch (`intExpandBranches_openBranch_sat`'s reuse case, in `Scheme.lean`, is untouched and
  unproven here) — this is precisely where the quotient identification (`rep`) must be
  constructed and its properties (idempotence, monotonicity along `isAccessible`) proven.
- That `truthLemma`'s F-imp case (`Scheme.lean:600-608`, currently `sorry`) closes against the
  quotient-restated `sat_fimp`.
- The second reuse arm's mechanical closure under the swapped definitions (structural argument
  only — see Scope note).

The repair task should proceed treating this spike's finding as: *"the soundness lemma will not
be the blocker; the remaining work is the quotient construction and the two still-`sorry` /
still-unproven downstream obligations."*

---

## 3. Evidence Appendix

### Phase 1 baseline (real `Soundness.lean`, unmodified)

- Scoped build: `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` — green,
  0.66s (cached). Full `lean_build` (LSP restart, required to get non-empty `lean_goal` results)
  — green, 3309 jobs, pre-existing `sorry` warnings only in `Scheme.lean:570,2583`,
  `Completeness.lean:124`, `Minimal/Completeness.lean:118`, `FrameSoundness.lean:1252` (all
  pre-existing, unrelated to this spike, unchanged by it).
- `lean_goal` at `Soundness.lean:1470` (before) / `:1477` (after `simp only [] at hgo`): full
  goal states captured (see Section 1 for the load-bearing excerpt — the case tag
  `neg.some.linearResult.inl.some.some`, ~35 hypotheses, ending `hwit : intFImpReuseWitness?
  bPers edgesP newForms e_val = some x ⊢ False`).
- `lean_goal` at `Soundness.lean:1621` (before) / `:1626` (after): mirror arm
  (`neg.some.linearResult.inr.some.some`), byte-identical shape with `bp`/`edgesH` in place of
  `bh`/`edgesP`, `hsat_p : intBranchSatisfied val botForces wo bp` supplied directly (no
  `applyPersistenceFixpoint_sat` derivation needed, since `bp` is not the freshly-persisted head).
- `lean_hover_info` on `intFImpReuseWitness?` (`Expansion.lean:291`): full docstring recovered,
  confirming design rationale (Sfor-containment, GargGenoveseNegri2012) and the Option-A/Option-B
  history (`Expansion.lean:256-264`-referenced UNSOUND finding for Option B).
- `lean_hover_info` on `intFImpReuseWitness?_spec` (`Expansion.lean:328`): full type signature
  recovered.
- `grep -c "IBranchSaturation" Soundness.lean` = 0. `grep -n "intFImpReuseWitness?_spec"
  Soundness.lean` = (no output). `grep -n "sat_fimp" Soundness.lean` = (no output).
- H1/H2 recorded as falsifiable hypotheses (see plan Phase 1 task list) before any experiment
  was run.

### Phase 2 (ancestor-directed check prototype)

- `intFImpReuseWitnessAnc?` defined in the scratch file; `lean_hover_info` confirms:
  `Cslib.Logic.PL.intFImpReuseWitnessAnc?.{u_1} {Atom : Type u_1} [DecidableEq Atom]
  (bPers : IBranch Atom) (edges : IEdges) (newForms : List (ISF Atom)) (newEdge : ℕ × ℕ)
  : Option ℕ` — identical to `intFImpReuseWitness?`'s type.
- Vehicle decision: the scratch file (not `lean_run_code`) was used for all Lean work; it
  elaborates and `lean_goal`/`lean_hover_info` return real, non-empty results once the LSP was
  warmed by one `lean_build` call.
- Optional `#eval` against the F1 divergence witness was skipped (plan marks it non-required;
  time was directed at the decisive Phase 4 experiment instead).

### Phase 3 (quotient `sat_fimp` prototype)

- `IBranchSaturationQ` defined (copy of `IBranchSaturation` with `sat_fimp` restated via a
  `rep : Nat → Nat` blocking-ancestor map: `∃ w', rep w ≤ rep w' ∧ T(φ)@w' ∈ b ∧ F(ψ)@w' ∈ b`).
  `lean_hover_info` confirms: `Cslib.Logic.PL.IBranchSaturationQ.{u_2} (Atom : Type u_2)
  [DecidableEq Atom] [Hashable Atom] (b : IBranch Atom) (rep : ℕ → ℕ) : Prop` — zero diagnostics.
- `lean_verify` on `Cslib.Logic.PL.intExpandBranches_closed_unsat`:
  `{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[]}`.
- H2 verdict: **CONFIRMED** (saturation absent from the dependency cone by construction of the
  lemma's own generic statement).

### Phase 4 (decisive experiment)

- `intExpandBranchesAnc` defined (byte-identical `go`-loop copy with the one-line swap at the
  world-creating-rule call site). `lean_hover_info` confirms identical type to
  `intExpandBranches`.
- Isolated reuse-arm-1 replay (`example` with ~35 hypotheses copied verbatim from the Phase 1
  capture, `hwit`/`hgo` restated over the swapped definitions): the unchanged
  `Soundness.lean:1478-1519` tactic block was applied verbatim (`rw [hwit] at hgo`,
  `simp only [] at hgo`, `have hsat_pers := applyPersistenceFixpoint_sat ...`,
  `have hfreshCombReuse := ...`, `refine absurd hsat_pers (ih ...)`, closing
  `List.zip_append`/`Or.inl`/`Or.inr` bookkeeping). Final `lean_goal` call:
  `"goals_after": []` — **no goals**.
- H1 verdict: **CONFIRMED** for arm 1 (mechanical closure under live goal state against the
  swapped definitions); arm 2 supported by structural isomorphism against its own real captured
  goal state (Phase 1), not independently re-closed (see Scope note below).

### Phase 5 (ABORT gate / stop conditions)

- Elapsed time: ≈15-20 minutes (well under the 3.25h cap).
- Scratch proof-attempt length: the decisive-experiment tactic proof is ≈94 lines (well under
  the 150-line cap; the 311-line total scratch file includes auxiliary definitions and
  docstrings, not tactic-proof content).
- Failed `lean_multi_attempt`/tactic batches: zero (every tactic step succeeded on first
  application; tactics were applied via direct Edit + `lean_goal` inspection rather than
  `lean_multi_attempt`, since the block is long and strictly sequential).
- Rebuild loops: one `lean_build` call (~15s) to warm the LSP after `lean_goal` initially
  returned empty states on both `Soundness.lean` and `Expansion.lean` (the file was cached-built
  by `lake build` but not yet loaded by the LSP session); well under the 15-minute threshold.
- **No stop condition fired.** The spike concludes at Phase 6 because the evidence is decisive
  (GO), not because a stop condition forced early termination.

---

## 4. Scope Note (what was NOT tested)

- **Second reuse arm not independently re-closed.** Only the first reuse arm
  (`Soundness.lean:1470` analogue, `bp = bh` case) was mechanically replayed and closed against
  `intExpandBranchesAnc`/`intFImpReuseWitnessAnc?`. The second arm (`Soundness.lean:1621`
  analogue, `bp ∈ bt` case) was inspected via live `lean_goal` against the **real, unmodified**
  proof (confirming the same zero-dependence-on-witness-content shape) but was **not**
  separately replayed under the swapped definitions. The two arms are structurally isomorphic
  (same `hgo` shape, same closing tactic pattern, differing only in whether `bPers`'s
  satisfiability is derived via `applyPersistenceFixpoint_sat` or supplied directly as `hsat_p`),
  so this is treated as low residual risk, but a future dispatch should not assume it is
  *proven* — only *strongly indicated*.
- **No termination argument.** This spike did not test whether `intFImpReuseWitnessAnc?`
  actually fires on the F1 divergence witness (the original motivating bug) or whether it
  restores the fuel bound's adequacy. It tested only *soundness compatibility* — that swapping
  the predicate does not break `intExpandBranches_closed_unsat`.
- **No proof of `IBranchSaturationQ`'s realizability.** `IBranchSaturationQ` was shown to
  *elaborate*, not to be *provable* from an actual saturated branch. The `rep` map's required
  properties (that it correctly identifies each blocked world with its blocking ancestor, and
  that `rep w ≤ rep w'` is actually derivable at the point `intExpandBranches_openBranch_sat`'s
  reuse case needs it) were not constructed or verified.
- **`truthLemma`'s F-imp case (`Scheme.lean:600-608`) was not touched.** It remains `sorry` and
  is untouched by this spike, as required by the plan's non-goals.
- **The other two library `sorry`s (`Scheme.lean:2623`, `Completeness.lean`) were not touched or
  investigated.**
- **No library file was read for anything beyond citation/comparison purposes**; no library file
  was edited.
- Alpha-rule and branching-rule cases of `intExpandBranchesAnc`'s `go` loop were defined (as
  part of the byte-identical copy) but not separately exercised in a proof — only the
  world-creating reuse-arm case was the subject of the decisive experiment, since that is the
  only case touched by the proposed calculus change.

---

## Library Integrity Check

- `git status --porcelain Cslib/` — confirmed empty (see below).
- `git diff HEAD -- Cslib/` — confirmed empty (see below).
- No `sorry` count changed anywhere in the repository as a result of this spike.
- `specs/573_tableau_quotient_soundness_spike/scratch/` deleted after this record was written.
