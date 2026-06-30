# Research Report: Task #299 Completeness Decomposition (Phases 5-7)

- **Task**: 299 - Modal K Tableau Decision Procedure
- **Report**: 03_completeness-decomposition.md
- **Type**: cslib
- **Date**: 2026-06-30
- **Session**: sess_1782830769_919aa1
- **Scope**: Decompose completeness work (Phases 5-7) into single-dispatch sub-phases and
  pre-extract exact reference signatures so a future implementer needs minimal file reading.
- **Out of scope**: Soundness (Phases 1-4) — DONE, build GREEN. NOT re-researched.

## Purpose / Feed-Forward Note

**This report feeds a `/plan` revision (v3) of task 299.** Phases 1-4 (soundness) are complete and
green. The existing plan `plans/02_modal-k-tableau-plan.md` describes Phases 5-7 at a coarse grain
that twice overflowed the implementer's context (Phase 5 attempted in one shot, forcing large
reference-file reads). This report (a) refines Phase 5 into four small sub-phases each sized to one
agent dispatch (~100-300 lines output), (b) records the exact signatures of every reference item the
implementer must mirror, and (c) recommends refactors. A planner should consume this directly to
emit a revised Phases 5a-5d / 6 / 7 plan.

## Executive Summary

- Phase 5's blow-up cause is confirmed structural: the modal truth lemma must mirror **two**
  reference proofs at once — the sorry-free **propositional** `classicalTruthLemma` (for atom/⊥/imp
  via the Hintikka branch condition) **and** the sorry-free **box cases** of the Bimodal
  `truthLemma_pos`/`truthLemma_neg` (via `induction φ generalizing w` + `Satisfies.box_iff_forall`).
  Both reference files are large (Classical 1340 lines, Bimodal CountermodelExtraction 1095 lines);
  this report inlines the load-bearing fragments so the implementer never opens them.
- **Refined decomposition**: 5a skeleton+model+atom-reflection; **5b** per-rule *semantic bridge*
  helpers (this is where the reference-reading concentrated — isolating it is the single biggest
  win); **5c** the main `modalTruthLemma`; **5d** `modalOpenBranch_countermodel` + the reduced
  `modalTableau_complete`. This differs from the task's proposed 5a-5d (which split positive vs.
  negative induction); justification below — the pos/neg split does not cut cleanly because
  `imp`-positive needs the negative IH and vice-versa, so they belong in one conjunction lemma.
- **Phase 6 (`modalExpandBranches_hintikka`) is NOT greenfield.** The soundness loop invariant
  `modalExpandBranches_closed_unsat` (Soundness.lean:226-385, built by tasks 384/364) already
  solves the hard worklist/fuel-induction plumbing — fuel induction + inner `processNext`
  induction + per-branch `List.Forall₂` over accs, plus reusable `forall₂_*` helpers
  (Soundness.lean:156-219) and `accFreshInv` machinery. Phase 6 mirrors this skeleton, swapping the
  invariant from "closed ⇒ unsat" to "returned open branch ⇒ `modalHintikkaSet`". Still the
  highest-risk phase, but the plumbing exists.
- **Key refactor**: hoist the `forall₂_*` list helpers out of `Soundness.lean` into a shared module
  so Phase 6 reuses them WITHOUT making `Completeness.lean` import the heavy `Soundness.lean`.
- A subtle but critical correctness note for the implementer: `modalHintikkaSet`
  (Saturation.lean:207) does **not** carry separate box/diamond edge-closure conjuncts — box-positive
  edge-closure is folded into the `.persistent` rule branch of `modalApplyOne`, so the generic
  `∀ sf' ∈ newForms, sf' ∈ b` condition already captures it. The truth lemma's box case must read
  edge-closure through `modalApplyOne … = .persistent`, not a standalone predicate.

## Reference-Signature Table (exact, verified against source)

All signatures below were read directly from the line-numbered source on commit-current `main`.
Paths are repo-relative to `/home/benjamin/Projects/cslib`.

### 1. Classical truth lemma (propositional template — atom/⊥/imp cases)

| Item | File:Line | Exact signature |
|------|-----------|-----------------|
| `extractValuation` | `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:56` | `def extractValuation (b : Branch (Proposition Atom) Unit) : BoolValuation Atom := fun p => b.any fun sf => sf.sign == .pos && sf.formula == .atom p` |
| `classicalHintikkaSet` | `…/Classical/Completeness.lean:68` | `def classicalHintikkaSet (b : Branch (Proposition Atom) Unit) : Prop := isClassicallyClosed b = false ∧ ∀ sf ∈ b, match classicalApplyOne sf with \| .linear newForms => ∀ sf' ∈ newForms, sf' ∈ b \| .branching branches => ∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b \| .persistent newForms => ∀ sf' ∈ newForms, sf' ∈ b \| .notApplicable => True` |
| `classicalTruthLemma` | `…/Classical/Completeness.lean:84` | `lemma classicalTruthLemma (b : Branch (Proposition Atom) Unit) (hH : classicalHintikkaSet b) (φ : Proposition Atom) : (b.any (fun sf => sf.sign == .pos && sf.formula == φ) → BoolEvaluate (extractValuation b) φ = true) ∧ (b.any (fun sf => sf.sign == .neg && sf.formula == φ) → BoolEvaluate (extractValuation b) φ = false)` |

**`classicalTruthLemma` proof skeleton** (the structural template for the prop fragment):
- `obtain ⟨hopen, hrule⟩ := hH` then `induction φ with`.
- It is a **single lemma proving the conjunction (pos ∧ neg) simultaneously**. This is deliberate:
  the `imp a c` *positive* case branches to `[F(a)]` or `[T(c)]` (Łukasiewicz), so it consumes the
  *negative* IH of `a`; symmetrically `imp`-negative consumes the positive IH of `a` and the
  negative IH of `c`. Pos and neg cannot be separated without a `mutual` block.
- `atom p`: pos → membership directly gives valuation `true`; neg → if T(atom p) also present the
  branch is closed (contradiction with `hopen`), discharged via `Branch.hasContradiction` /
  `isClassicallyClosed`.
- `bot`: pos → T(⊥) ⇒ closed ⇒ contradiction with `hopen`; neg → `BoolEvaluate _ bot = false` by simp.
- `imp a c` (with `ih_a ih_c`): unpack `hrule sf … : .branching […]` via the Hintikka condition
  `∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b`, case on which branch is present, apply IHs.

### 2. Bimodal modal truth lemma (box-case template + induction structure)

| Item | File:Line | Exact signature |
|------|-----------|-----------------|
| `truthLemma_pos` | `Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean:895` | `theorem truthLemma_pos (b : Branch Atom) (timeOrd : TimeOrdering) (hSat : findUnexpanded b (timeOrd := timeOrd) = none) (fc : FrameClass) (hOpen : findClosure b fc = none) (cm : SemanticCountermodel Atom) (hCm : cm = extractSemanticCountermodel cm.formula b cm.timeOrdering) (φ : Formula Atom) (w : WorldIndex) (t : TimeIndex) (hmem : ⟨.pos, φ, ⟨w, t⟩⟩ ∈ b) : branchTruth cm w t φ` |
| `truthLemma_neg` | `…/CountermodelExtraction.lean:934` | `theorem truthLemma_neg (b : Branch Atom) (timeOrd : TimeOrdering) (hSat : findUnexpanded b … = none) (fc : FrameClass) (hOpen : findClosure b fc = none) (cm : SemanticCountermodel Atom) (hCm : cm = extractSemanticCountermodel cm.formula b cm.timeOrdering) (hOrd : cm.timeOrdering = timeOrd) (φ : Formula Atom) (w : WorldIndex) (t : TimeIndex) (hmem : ⟨.neg, φ, ⟨w, t⟩⟩ ∈ b) : ¬branchTruth cm w t φ` |
| `sat_box_pos` (box-pos bridge) | `…/CountermodelExtraction.lean:549` | `theorem sat_box_pos (b : Branch Atom) (timeOrd : TimeOrdering) … : (T(□ψ)@(w,t) ∈ b) → ∀ w', <edge> → ⟨.pos, ψ, ⟨w',t⟩⟩ ∈ b` (returns membership at every successor) |
| `sat_box_neg` (box-neg bridge) | `…/CountermodelExtraction.lean:589` | `theorem sat_box_neg (b …) … : (F(□ψ)@(w,t) ∈ b) → ∃ w', <edge w w'> ∧ ⟨.neg, ψ, ⟨w',t⟩⟩ ∈ b` (returns a witness successor) |

**Mutual-induction structure** (the key insight for 5c): `truthLemma_pos` and `truthLemma_neg` are
**two separate `theorem`s, not a `mutual` block**. The dependency is *one-directional*:
- Both use `induction φ generalizing w t with` (the `generalizing` is essential — it makes the IH
  available at the *successor* world `w'` in the box case).
- `truthLemma_pos` is self-contained — its `imp` case is `exfalso` (in the bimodal tableau T(imp) is
  always expanded so no T(imp) survives saturation). **This will NOT hold for modal K**, whose
  `imp`-positive is a *branching* Łukasiewicz rule kept under the Hintikka condition — so the modal
  truth lemma's `imp`-pos case must follow `classicalTruthLemma`'s branch-condition handling, which
  needs the *negative* IH. Therefore in modal K the two directions are genuinely mutual and the
  **single conjunction lemma (classical style) is the correct shape**, not two separate theorems.
- `truthLemma_pos` box case (lines 914-920): `simp only [branchTruth]; intro w' hw'; … have hbox :=
  sat_box_pos …; exact ih w' t (hbox w' hw')`.
- `truthLemma_neg` box case (lines 957-964): `intro h; have ⟨w', hw'mem, hw'neg⟩ := sat_box_neg …;
  have := ih w' t hw'neg; exact this (h w' …)`. Note `truthLemma_neg`'s `imp` case (950-956) calls
  `truthLemma_pos` — the one-directional dependency.

### 3. Modal semantics characterisation lemmas (exact)

| Item | File:Line | Exact signature |
|------|-----------|-----------------|
| `Model` | `Cslib/Logics/Modal/Basic.lean:63` | `structure Model (World : Type*) (Atom : Type*) where r : World → World → Prop; v : World → Atom → Prop` |
| `Satisfies` | `Basic.lean:145` | `def Satisfies (m : Model World Atom) (w : World) : Proposition Atom → Prop` with `\| .atom p => m.v w p \| .bot => False \| .imp φ₁ φ₂ => Satisfies … φ₁ → Satisfies … φ₂ \| .box φ => ∀ w', m.r w w' → Satisfies m w' φ` |
| `Satisfies.box_iff_forall` | `Basic.lean:235` | `theorem Satisfies.box_iff_forall {m : Model World Atom} : ⇓Modal[m,w ⊨ □φ] ↔ ∀ w', m.r w w' → ⇓Modal[m,w' ⊨ φ] := Iff.rfl` (`@[scoped grind =]`) |
| `Satisfies.diamond_iff_exists` | `Basic.lean:241` | `theorem Satisfies.diamond_iff_exists {m : Model World Atom} : ⇓Modal[m,w ⊨ ◇φ] ↔ ∃ w', m.r w w' ∧ ⇓Modal[m,w' ⊨ φ] := Satisfies.diamond_iff` (`@[scoped grind =]`) |
| `Satisfies.neg_iff` | `Basic.lean:152` | `theorem Satisfies.neg_iff : Satisfies m w (¬φ) ↔ ¬Satisfies m w φ` |
| `Satisfies.and_iff` / `or_iff` | `Basic.lean:168` / `178` | `Satisfies m w (φ₁ ∧ φ₂) ↔ … ∧ …` / `… (φ₁ ∨ φ₂) ↔ … ∨ …` |

Both `box_iff_forall` and `diamond_iff_exists` are `Iff.rfl` / definitional and tagged
`@[scoped grind =]`. Because `Satisfies … .box` is *literally* `∀ w', m.r w w' → …`, the box case
can often be closed by `intro w' hr` directly without rewriting.

### 4. Model-construction templates to mirror (for `extractModel` + atom valuation)

| Item | File:Line | Exact signature |
|------|-----------|-----------------|
| Temporal `extractModel` (closest tableau analog) | `Cslib/Logics/Temporal/Tableau/Completeness.lean:92` | `def extractModel (b : TBranch Atom) : TemporalModel Nat Atom where valuation t p := b.any fun sf => sf.sign == .pos && sf.label == t && sf.formula == .atom p` |
| Temporal `extractModel_atom_sat_iff` | `…/Temporal/Tableau/Completeness.lean:100` | `lemma extractModel_atom_sat_iff (b) (t) (p) : Satisfies (extractModel b) t (.atom p) ↔ b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == .atom p)` (proof: `simp only [Satisfies.atom_iff, extractModel]`) |
| Bimodal `buildAtomValuation` | `…/Bimodal/…/CountermodelExtraction.lean:359` | `def buildAtomValuation (b : Branch Atom) : WorldIndex → TimeIndex → Atom → Bool := …` |

**Recommended modal construction** (NEW, ~10 lines — there is no exact analog because modal `Model`
carries BOTH `r` and `v`; temporal/bimodal carry only a valuation):
```
def extractModel (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    Model WorldIndex Atom where
  r w w' := acc.hasEdge w w' = true            -- accessibility from the recorded edge list
  v w p  := b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w) = true
```
(Use `acc.hasEdge` — Bool — wrapped to `Prop`, OR `(w, w') ∈ acc.edges`; pick whichever makes the
box case's `intro w' hr` cleanest. `hasEdge` is what `modalHintikkaSet`/`modalApplyOne` propagate
along, so it aligns the truth lemma with the saturation condition.) Provide the matching
`extractModel_atom_sat_iff` mirroring the temporal lemma.

### 5. Hintikka predicate + accessibility (`acc.edges`) API

| Item | File:Line | Exact signature / fields |
|------|-----------|--------------------------|
| `modalHintikkaSet` | `Cslib/Logics/Modal/Tableau/Saturation.lean:207` | `def modalHintikkaSet (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) : Prop := isModalClosed b = false ∧ ∀ sf ∈ b, let (result, _) := modalApplyOne sf b acc; match result with \| .linear nf => ∀ sf' ∈ nf, sf' ∈ b \| .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ b \| .persistent nf => ∀ sf' ∈ nf, sf' ∈ b \| .notApplicable => True` |
| `Accessibility` | `Cslib/Logics/Modal/Tableau/Branch.lean:54` | `structure Accessibility where edges : List (WorldIndex × WorldIndex)` |
| `Accessibility.empty` | `Branch.lean:61` | `def empty : Accessibility := ⟨[]⟩` |
| `Accessibility.addEdge` | `Branch.lean:64` | `def addEdge (acc) (w w' : WorldIndex) : Accessibility := ⟨(w, w') :: acc.edges⟩` |
| `Accessibility.successorsOf` | `Branch.lean:70` | `def successorsOf (acc) (w) : List WorldIndex := acc.edges.filterMap fun (src, tgt) => if src == w then some tgt else none` |
| `Accessibility.allWorlds` | `Branch.lean:74` | `def allWorlds (acc) : List WorldIndex := acc.edges.foldl …` |
| `Accessibility.hasEdge` | `Branch.lean:80` | `def hasEdge (acc) (w w' : WorldIndex) : Bool := acc.edges.any fun (src, tgt) => src == w && tgt == w'` |
| `boxPositivesOf` | `Branch.lean:180` | `def boxPositivesOf (b) : List (WorldIndex × Proposition Atom) := b.filterMap …` |
| `boxPropagation` | `Branch.lean:194` | `def boxPropagation (b) (acc) (w) : … := (acc.successorsOf w).filterMap fun w' => …` |
| `modalApplyOne` | `Cslib/Logics/Modal/Tableau/Rules.lean:68` | `def modalApplyOne (sf …) (b …) (acc : Accessibility) : RuleResult (Proposition Atom) WorldIndex × Accessibility` |
| `isModalClosed` | `Cslib/Logics/Modal/Tableau/Closure.lean:57` | `def isModalClosed (b : List (SignedFormula (Proposition Atom) WorldIndex)) : Bool` |
| `SignedFormula` | `Cslib/Foundations/Logic/Tableau/SignedFormula.lean:49` | `structure SignedFormula (F L : Type*) where sign : Sign; formula : F; label : L` (membership form `⟨.pos, φ, w⟩ ∈ b`; `.pos`/`.neg` constructors at `:61`/`:64`) |

**CRITICAL implementer note**: `modalHintikkaSet` has **no** standalone "box edge-closure" conjunct.
Box-positive (`boxPos`) and diamond-negative (`diamondNeg`) are `.persistent` rules in `modalApplyOne`
(Rules.lean:65-67) whose `newForms` already include `T(φ)@w'` for each `w' ∈ successorsOf w`. So the
generic `.persistent nf => ∀ sf' ∈ nf, sf' ∈ b` clause IS the edge-closure condition. The box-pos
truth-lemma case must therefore extract its successor obligation by evaluating
`modalApplyOne (T(□ψ)@w) b acc` and reading its `.persistent` outputs — NOT by looking up a separate
predicate. This is the single most likely source of confusion and the reason 5b (the per-rule
semantic bridges) is isolated.

### 6. Phase 6 loop invariant — `modalExpandBranches_hintikka`

**Status: does NOT yet exist** (grep across `Cslib/` found zero occurrences of
`modalExpandBranches_hintikka`, `modalOpenBranch_countermodel`, `modalTableau_hintikka`,
`modalTableau_complete`, `modalTruthLemma`). It must be written. **It mirrors the existing soundness
loop invariant**, which is fully proved:

| Reusable infra | File:Line | Role |
|----------------|-----------|------|
| `modalExpandBranches_closed_unsat` | `Cslib/Logics/Modal/Tableau/Soundness.lean:226` | `theorem (fuel) : … → modalExpandBranches branches expandedSets accs fuel = .closed → List.Forall₂ (fun b acc => ¬branchSatisfiable b acc) branches accs` — the **structural template**: fuel induction + inner `processNext` induction (lines 256-385) over per-branch `List.Forall₂` accs. |
| `forall₂_of_zip_mem` | `Soundness.lean:156` | List.Forall₂ helper (worklist plumbing) |
| `forall₂_replicate_right` | `Soundness.lean:177` | for `List.replicate newBs.length newAcc` (child accs) |
| `forall₂_append_aux` / `_drop_aux` / `_take_aux` | `Soundness.lean:197` / `205` / `212` | done++pending splicing |
| `accFreshInv` + `accFreshInv_empty` | `SoundnessStep.lean:165` / `:172` | freshness invariant |
| `modalStepBranch_preserves_accFreshInv` | `Soundness.lean:110` | invariant maintenance across a step |
| `modalStepBranch` / `modalExpandBranches` / `.processNext` | `Saturation.lean:99` / `135` / `149` | the recursion being inducted over |

**Intended statement** (to be proved in Phase 6):
```
theorem modalExpandBranches_hintikka (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility) (b : …) (acc : Accessibility),
      <length invariants> →
      modalExpandBranches branches expandedSets accs fuel = .openBranch b acc →
      modalHintikkaSet b acc
```
**Phase 6 difficulty assessment**: HIGH but de-risked. The hard, previously-unsolved part
(threading per-branch `acc`/`newAcc` through the `processNext` vs `modalExpandBranches` recursion
levels) is exactly what tasks 384/364 solved for the closed direction — the inner-induction skeleton,
the `Forall₂` helpers, and the freshness invariant are all reusable. The genuinely new obligation is:
when `modalStepBranch b e a = none` (saturated, returns `.openBranch b a`), prove `modalHintikkaSet b
a` — i.e. "no applicable rule fired" ⇒ "every rule's outputs are already present". This is a
*saturation-characterisation* lemma about `modalStepBranch … = none` and `modalApplyOne`, analogous
to classical `classicalStepBranch_none_saturated` (`Classical/Completeness.lean:694`) and
`classicalStepBranch_hintikka_inv` (`:722`), and the full classical loop invariant
`classicalExpandBranches_hintikka` (`:924`). **Recommend the implementer mirror
`classicalExpandBranches_hintikka` for the open/Hintikka logic and
`modalExpandBranches_closed_unsat` for the acc-threading.** The world-creation interleaving
(box-pos re-firing as new successors appear) is the residual risk; the fuel bound `modalFuel`
(Saturation.lean:89, `(4n+4)(n+2)+2`) must suffice — adjust in Saturation.lean only if the
invariant proof exposes a gap.

## Refined Sub-Phase Decomposition (5a-5d, 6, 7)

Each sub-phase below is bounded to one agent dispatch (~100-300 lines output) and is built to
**compile green incrementally** (no sub-phase leaves a `sorry` except the single explicit Phase-6
placeholder noted in 5d). All edits are in `Cslib/Logics/Modal/Tableau/Completeness.lean` (new file)
unless noted.

### Justification for diverging from the task's proposed 5a-5d

The task proposed: 5a skeleton+model, 5b *positive* induction, 5c *negative* induction, 5d statement.
**This pos/neg split does not cut cleanly.** As established from `classicalTruthLemma` (§1): modal K's
`imp`-positive is a branching Łukasiewicz rule whose `[F(a)]` sub-branch needs the *negative* IH, and
`imp`-negative needs the *positive* IH — the two directions are mutually recursive, so they live in
one conjunction lemma (`induction φ` proving `pos ∧ neg` together), exactly as classical does. Splitting
the single `induction φ` across two dispatches would leave a non-compiling half. Instead this report
splits along **what forced the context overflow**: the per-rule *semantic bridge* helpers (which is
where the implementer had to read the large Bimodal/Classical files). Isolating those into 5b, and
keeping the main induction (5c) thin by having it only *call* the 5b bridges, is the structural fix.

### Phase 5a: Skeleton + model extraction + atom reflection [~120-180 lines]
- **Scope**: Create `Completeness.lean` (namespace `Cslib.Logic.Modal.Tableau`, `import Cslib.Init`
  + the Tableau modules). Define `extractModel b acc : Model WorldIndex Atom` per §4. Prove the
  atom-reflection lemmas mirroring temporal `extractModel_atom_sat_iff` (`…/Temporal/Tableau/
  Completeness.lean:100`): `Satisfies (extractModel b acc) w (.atom p) ↔ <T(atom p)@w on b>`, plus
  `extractModel_bot_false`. Prove the two "open branch ⇒ no T(⊥), no contradiction" helpers mirroring
  temporal `openBranch_noBotPos` (`:167`) / `openBranch_noContradiction` (`:194`) (or reuse
  `isModalClosed = false` directly).
- **Dependencies**: Phase 3 (Saturation/Branch/Rules/Closure/Defs — all done). Independent of soundness.
- **Effort**: 1.0h. **Gate**: `lake build Cslib.Logics.Modal.Tableau.Completeness` green, zero sorry.

### Phase 5b: Per-rule semantic bridge lemmas [~150-250 lines] — the isolation win
- **Scope**: For a `modalHintikkaSet b acc` branch, prove the small bridges the truth lemma consumes
  (mirror Bimodal `sat_box_pos`:549 / `sat_box_neg`:589 / `sat_imp_neg`:524 and the classical
  Hintikka branch-condition unpacking):
  - `hintikka_box_pos`: `T(□ψ)@w ∈ b → acc.hasEdge w w' → T(ψ)@w' ∈ b` (via the `.persistent`
    output of `modalApplyOne (T(□ψ)@w)` — see §5 CRITICAL note).
  - `hintikka_box_neg`: `F(□ψ)@w ∈ b → ∃ w', acc.hasEdge w w' ∧ F(ψ)@w' ∈ b` (the `boxNeg` linear
    rule created the witness edge + `F(ψ)@w'`).
  - `hintikka_imp_pos` / `hintikka_imp_neg`: unpack the branching/linear `modalApplyOne` result via
    the `modalHintikkaSet` `∀ sf ∈ b, match …` clause (mirror `classicalTruthLemma`'s `imp` handling).
  - diamond is derived (`◇ψ = ¬□¬ψ`); add `hintikka_diamond_*` only if the diamond shape is matched
    directly by `modalApplyOne` (check `Defs.lean diaOf?`), else the box bridges + `Satisfies.
    diamond_iff_exists` suffice in 5c.
- **Dependencies**: 5a. **Effort**: 1.25h. **Gate**: builds green, zero sorry. Each bridge is a few
  lines; the value is that they fully encapsulate the `modalApplyOne`/`modalHintikkaSet` unfolding so
  5c never re-reads Rules.lean/Saturation.lean.

### Phase 5c: Main truth lemma `modalTruthLemma` [~150-250 lines]
- **Scope**: One conjunction lemma (classical shape), `induction φ generalizing w`:
  ```
  lemma modalTruthLemma (b) (acc) (hH : modalHintikkaSet b acc) :
      ∀ (φ : Proposition Atom) (w : WorldIndex),
        (<T(φ)@w ∈ b> → Satisfies (extractModel b acc) w φ) ∧
        (<F(φ)@w ∈ b> → ¬ Satisfies (extractModel b acc) w φ)
  ```
  `generalizing w` is mandatory (box case needs the IH at successor `w'`). atom/⊥/imp cases follow
  `classicalTruthLemma` (§1) using the 5b `hintikka_imp_*` bridges; box case uses `intro w' hr`
  (`Satisfies.box_iff_forall` is `Iff.rfl`) + `hintikka_box_pos`/`_neg` + the world-generalized IH;
  diamond via `Satisfies.diamond_iff_exists`.
- **Dependencies**: 5a, 5b. **Effort**: 1.5h. **Gate**: builds green, **zero sorry** (the truth lemma
  itself must be sorry-free — this is the deliverable that previously overflowed).

### Phase 5d: Countermodel wrapper + reduced completeness statement [~80-120 lines]
- **Scope**: `modalOpenBranch_countermodel`: a `modalHintikkaSet b acc` branch yields `extractModel
  b acc` refuting `φ` (mirror classical `classicalOpenBranch_countermodel`:1299 — apply
  `modalTruthLemma … .2` to the initial `F(φ)@0` membership). Then state `modalTableau_complete`
  reduced to the single Phase-6 dependency `modalExpandBranches_hintikka`. Per zero-debt policy: state
  it as `theorem modalTableau_complete … := <proof calling modalExpandBranches_hintikka>` where
  `modalExpandBranches_hintikka` is declared as an explicit `theorem … := by sorry` **clearly marked
  TODO Phase 6** OR — preferred — leave Phase 6's lemma unstated and have 5d end at
  `modalOpenBranch_countermodel`, deferring `modalTableau_complete` wholesale to Phase 6. The latter
  avoids any `sorry` in the committed tree.
- **Dependencies**: 5c. **Effort**: 0.5h. **Gate**: builds green; the ONLY outstanding obligation is
  `modalExpandBranches_hintikka` (Phase 6). Recommend the no-sorry variant (defer
  `modalTableau_complete` to Phase 6) so the committed tree stays sorry-free per CSLib hard rule.

### Phase 6: loop invariant + final completeness [HIGH RISK, ~200-400 lines, may need 1-2 dispatches]
- **Scope**: Prove `modalExpandBranches_hintikka` (§6 statement) mirroring
  `modalExpandBranches_closed_unsat` (Soundness.lean:226) for acc-threading and
  `classicalExpandBranches_hintikka` (Classical/Completeness.lean:924) for the open/Hintikka logic.
  Add the saturation-characterisation lemma (`modalStepBranch … = none → modalHintikkaSet`), then
  discharge `modalTableau_complete` fully. Remove any temporary sorry.
- **Dependencies**: 5d (and the refactor below, ideally). **Effort**: 3h. **Gate**: `lake build …
  Completeness` zero sorry; `#print axioms modalTableau_complete` standard axioms only.
- **Zero-debt fallback**: if the world-creation interleaving cannot close in one genuine attempt,
  keep 5a-5d committed sorry-free, mark Phase 6 [BLOCKED] with the precise residual obligation, and
  `/spawn` a follow-up — never ship sorry/axioms.

### Phase 7: decision procedure + barrel + CI [~80-150 lines]
- **Scope**: `modalTableau_decides` iff (from soundness + completeness) + `Decidable` instance
  (`DecidableEq + Hashable`, no `Fintype Atom`); module docs + barrel (`lake exe mk_all --module`);
  full CI (`lake build`, `lake test`, `checkInitImports`, `lint-style`, `shake`).
- **Dependencies**: Phase 6 (and soundness Phase 4d, done). **Effort**: 1.5h. **Gate**: all CI exit 0;
  zero sorry under `Cslib/Logics/Modal/Tableau/`.

## Refactoring Recommendations (concrete file/line targets)

1. **Hoist the `List.Forall₂` worklist helpers into a shared module.** `forall₂_of_zip_mem`
   (Soundness.lean:156), `forall₂_replicate_right` (:177), `forall₂_append_aux` (:197),
   `forall₂_drop_aux` (:205), `forall₂_take_aux` (:212) are generic list lemmas currently `private`
   in `Soundness.lean`. Phase 6 needs the identical plumbing for the open direction. Move them to a
   new `Cslib/Logics/Modal/Tableau/LoopInduction.lean` (or de-`private` and re-export) so
   `Completeness.lean` reuses them **without importing `Soundness.lean`** (which would create an
   undesirable soundness→completeness build coupling and pull the heavy ~970-line file into the
   completeness build). Low risk (pure relocation of generic lemmas); do this as the first step of
   Phase 6, or as a tiny preliminary commit.
2. **De-`private` / share the saturation-characterisation pattern.** The classical
   `classicalStepBranch_none_saturated` (Classical/Completeness.lean:694) and
   `classicalStepBranch_hintikka_inv` (:722) are the exact logical template for the modal
   `modalStepBranch … = none → modalHintikkaSet` lemma. They are propositional-specific (Unit
   labels) so cannot be reused directly, but the planner should point Phase 6 at them as the proof
   pattern. No code move needed — reference only.
3. **No model-construction sharing.** Modal `Model` (r + v) differs from temporal/bimodal
   valuation-only models; `extractModel` is ~10 new lines (§4). Do not over-abstract — a shared
   "tableau→model" helper is not worth the indirection for one call site.
4. **Optional: add `acc.hasEdge`/`successorsOf` mem-reflection lemmas to `Branch.lean`.** The truth
   lemma's box case relates `m.r w w'` (= `acc.hasEdge w w' = true`) to membership in
   `successorsOf`/`edges`. A one-line `hasEdge_iff_mem_successors` lemma in `Branch.lean` next to the
   API (`:80`) would keep 5b/5c clean. Low risk, additive.

## Verification Notes

- Every signature in the table was read from line-numbered source on current `main`; the
  `lean_local_search` index was unpopulated in this session (returned empty), so verification was by
  direct source read (authoritative) rather than the search index. The implementer should still run
  `lean_hover_info` on `Satisfies.box_iff_forall` and `truthLemma_pos` at first use to confirm
  elaboration in their build.
- Soundness file split confirmed: `modalStepBranch_preserves_sat` now lives in
  `SoundnessStep.lean:187` (not `Soundness.lean` as the plan's stale line map says); the loop
  invariant `modalExpandBranches_closed_unsat` is in `Soundness.lean:226`. The plan's "current
  declaration map" (lines 278-285) is **stale** post-task-384 and should be regenerated by the planner.

## References

- Modal semantics: `Cslib/Logics/Modal/Basic.lean` (Model:63, Satisfies:145, box/diamond iff:235/241).
- Classical tableau template: `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`
  (extractValuation:56, classicalHintikkaSet:68, classicalTruthLemma:84,
  classicalExpandBranches_hintikka:924, classicalStepBranch_none_saturated:694,
  classicalOpenBranch_countermodel:1299, classicalTableau_complete:1328).
- Bimodal modal truth lemma: `Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean`
  (sat_box_pos:549, sat_box_neg:589, truthLemma_pos:895, truthLemma_neg:934, buildAtomValuation:359).
- Temporal tableau model: `Cslib/Logics/Temporal/Tableau/Completeness.lean` (extractModel:92).
- Modal K tableau (target): `Cslib/Logics/Modal/Tableau/{Defs,Branch,Rules,Closure,Saturation,
  Soundness,SoundnessStep}.lean`; modalHintikkaSet Saturation.lean:207; soundness loop invariant +
  Forall₂ helpers Soundness.lean:156-385.
- Existing plan: `specs/299_modal_k_tableau/plans/02_modal-k-tableau-plan.md` (Phases 5-7: 423-527).
