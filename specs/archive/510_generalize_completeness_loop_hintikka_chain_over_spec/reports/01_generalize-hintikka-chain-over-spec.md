# Research Report: Task 510 — Generalize the Completeness/Hintikka Chain over `RuleApplicationSpec`

- **Task**: 510 — `generalize_completeness_loop_hintikka_chain_over_spec`
- **Status**: [RESEARCHED]
- **Scope**: interface design for generalizing `Completeness.lean:665-935` +
  `CompletenessLoop.lean:57-746` over an abstract `apply : RuleApply Atom`.
- **Precedent studied**: task 507 (`FmpMeasure.lean` termination measure, commit `009cc348`).

## Bottom Line

**Feasible, and materially cheaper than task 507.** The saturation layer *can* be abstracted.
`RuleApplicationSpec` needs **five new fields** (7 → 12... see below: 7 → **11**, one candidate
field turns out to be already derivable). The single make-or-break design decision is that two of
the new fields must be stated with an **existentially-quantified payload** (`∃ out, ... =
.persistent out`) rather than K's concrete propagation list — this is exactly what absorbs T's
appended self-conjunct, B's symmetric propagation, and S5's universal propagation without any of
them appearing in the interface.

The task prompt's hypothesis ("abstract saturation predicate + `noneIffSaturated` + Hintikka-lift
hook") is **directionally right but wrong in its specifics**, and I recommend against implementing
it as stated. See "Verdict on the Stated Hypothesis" below. The evidence is in the
lemma-by-lemma table.

**On 506's cross-task requirement** (§0): **yes**, `modalHintikkaSet` must itself become
`modalHintikkaSetGen`, and the generic loop lemma must conclude in it. This is cheap (one-token
substitution — the definition names `modalApplyOne` exactly once) and it is now Phase 7's
acceptance criterion. Crucially, `modalHintikkaSetGen` is **spec-free** and belongs upstream in
`Saturation.lean`, so S4 can consume the statement shape without discharging
`RuleApplicationSpec` — reconciling 506's need with `GenericDriver.lean:105-108`'s S4 exclusion.
I also **correct one of 506's supporting findings**: only two of the four public bridges decouple
S4 from this task; the other two (`hintikka_box_pos`, `hintikka_diamond_neg`) read the rule
payload and are irreducibly per-system. 505/506 must budget for their own.

**Main risk**: one phase (P7) is a ~350-line substitution port of a triple-nested induction. It is
mechanical, but it is the bulk of the task and the only place where a `[BLOCKED]` outcome is
plausible. Everything else is small.

---

## 0. The Conclusion-Type Question (cross-task requirement from 506)

**Question**: must `modalHintikkaSet` itself become `modalHintikkaSetGen`, so that the generic
top-loop lemma concludes in `modalHintikkaSetGen apply bR aR` rather than the concrete
`modalHintikkaSet bR aR`?

**Answer: YES — unambiguously, and it is cheap.** I reached this independently (see §3) before the
requirement arrived; the two analyses agree. Concretely:

- `modalHintikkaSet` (`Saturation.lean:423`) mentions `modalApplyOne` in **exactly one place**
  (conjunct 2's `let (result, _) := modalApplyOne sf b acc`). Generalizing it is a one-token
  substitution, not a re-derivation. Conjuncts 1, 3, 4 mention no rule function at all.
- `modalExpandBranchesGen_hintikka` **must** conclude in `modalHintikkaSetGen apply bR aR`. If it
  concluded in the concrete `modalHintikkaSet`, 510 would land green and leave 505/506 blocked —
  defeating the task's entire purpose. This is now Phase 7's acceptance criterion.
- K's `modalTableau_complete` recovers the concrete form via `modalHintikkaSet_eq` (a `rfl`), so
  zero-regression is unaffected.

**The critical architectural property — `modalHintikkaSetGen` is spec-free.** Its definition
depends on nothing from `RuleApplicationSpec`, and it belongs in `Saturation.lean`, which is
**upstream** of `GenericDriver.lean` (where the spec lives). Therefore S4 can consume the
statement shape **without ever touching the spec**. This is what makes the coordinator's
constraint satisfiable in the presence of `GenericDriver.lean:105-108`'s explicit S4 exclusion:

| Layer | Lives in | Requires spec? | S4 can use? |
|---|---|---|---|
| `modalHintikkaSetGen apply` (the **statement shape**) | `Saturation.lean` | **no** | ✅ **yes** |
| `modalExpandBranchesGen_hintikka` (the **loop lemma**) | `CompletenessLoop.lean` | yes (F8-F12 + 507's 7) | ❌ no — by design |

So S4 produces its own `modalHintikkaSetGen (modalApplyOneS4 φ0) b acc` witness by its own means
and interoperates at the statement level. **Verified**: `RuleApply` (`Saturation.lean:104-107`) is
an `abbrev` for a plain function type, so a φ₀-parameterized `modalApplyOneS4 φ0 : RuleApply Atom`
is a legitimate argument to `modalHintikkaSetGen` — 506's supporting finding on this point is
correct. **Verified**: conjuncts 3/4 (`Saturation.lean:439-443`) are existential over successors
(`∃ w', acc.hasEdge w w' = true ∧ …`), so loop-back edges satisfy them natively — also correct,
and favourable.

### Correction to one of 506's supporting findings

> *"The public bridge lemmas take `modalHintikkaSet` as a HYPOTHESIS and conclude in
> branch-membership, which is why S4 can decouple most of its work from you — only its final
> Hintikka-production phase needs 510."*

**This is half right, and the wrong half matters for 505/506 planning.** The four bridges
(`Completeness.lean:136-250`) split into two classes with very different portability:

| Bridge | Proof | Generalizes over `apply`? |
|---|---|---|
| `hintikka_box_neg` (:198) | `hH.2.2.1 ψ w hmem` — pure projection of conjunct 3 | ✅ **free** — conjunct mentions no `apply` |
| `hintikka_diamond_pos` (:211) | `hH.2.2.2 ψ w hmem` — pure projection of conjunct 4 | ✅ **free** |
| `hintikka_box_pos` (:146) | `simp only [modalApplyOne, tryAllPropRules, …] at hcond`, then reads `boxPropagation`'s concrete payload (:172, :191-192) | ❌ **irreducibly rule-specific** |
| `hintikka_diamond_neg` (:230) | same shape — unfolds `modalApplyOne` and reads the successor-propagation payload (:239-241) | ❌ **irreducibly rule-specific** |

The two payload-reading bridges are the *exact complement* of the `∃ out` weakening that makes
F9/F10 work: the Hintikka **chain** never reads a Propagating payload (which is why it
abstracts), but the **truth-lemma bridges** do nothing *but* read it (which is why they cannot).
That is not a defect in the design — it is the correct seam. But it means **T, B, and S4 each need
their own `hintikka_box_pos`/`hintikka_diamond_neg` analogues**, and this work is **outside task
510's scope** (T's belongs to 503 Phase 5's already-scoped remainder). 505/506 planners should not
budget on 510 delivering it. I recommend the two projection bridges be generalized for free in
Phase 3 (`hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`, ~6 lines) since they cost nothing and
S4 will want them.

---

## 1. The Structural Fact That Makes This Work

Reading the proofs (not the docstrings), every rule-dependent step in the chain turns on a
**three-way classification of signed-formula shapes**, and on nothing else:

| Class | K shapes | What `apply` does | Consumed by |
|---|---|---|---|
| **Structural** | `.atom`, `.bot`, `.imp`, `.and`, `.or` (both signs) | result is independent of `b`/`acc` | the lift lemma |
| **Minting** | `.neg,.box` (boxNeg), `.pos,.diamond` (diamondPos) | `.linear`, mints `modalNextWorld b`, adds one edge | the witness conjuncts |
| **Propagating** | `.pos,.box` (boxPos), `.neg,.diamond` (diamondNeg) | `.notApplicable` or `.persistent` — **payload irrelevant** | the sign-discrimination invariants |

The decisive observation: **K, T, B, and S5 share this classification exactly.** All four operate
on the same `Proposition Atom` syntax and the same `RuleResult` type; T/B/S5 differ from K *only
inside the Propagating class*, and the chain never reads a Propagating payload — it only ever uses
the class membership to derive a contradiction. Concretely, at `CompletenessLoop.lean:331-332` and
`349-350`:

```lean
rcases modalApplyOne_posBox_eq sf_exp hsign_exp ψ hform_exp b acc with h | h <;>
  rw [h] at hfstc <;> simp at hfstc
```

The `out` in `.persistent out` is discarded — the lemma is used purely to contradict the
`.linear`/`.branching` case split. This is why the interface can be blind to T's self-conjunct.

`FrameRules.lean:72-95` confirms the T side structurally: `modalApplyOneT` maps
`.persistent kForms ↦ .persistent (kForms ++ selfNew.filter …)` and
`.notApplicable ↦ .notApplicable | .persistent selfNew` on the two Propagating shapes, and is
`= modalApplyOne` (`modalApplyOneT_eq_of_not_boxPos_diaNeg`) on every other shape. So T stays in
the Propagating class, with a different payload. Precisely the case the `∃ out` formulation
accommodates and a concrete-payload formulation would reject.

---

## 2. Verdict on the Stated Hypothesis

The prompt proposed: *abstract saturation predicate + `noneIffSaturated` characterisation +
Hintikka-lift hook (saturation implies the Hintikka clause conditions)*. Tested against the
proofs:

| Hypothesis component | Verdict | Evidence |
|---|---|---|
| Abstract saturation predicate | **Confirmed, but not a spec field** | `modalHintikkaSet` (`Saturation.lean:423`) mentions `modalApplyOne` in exactly one place (conjunct 2's `let (result, _) := modalApplyOne sf b acc`). Substituting `apply` yields `modalHintikkaSetGen apply` — a *definition*, not an obligation. For `apply := modalApplyOneT`, conjunct 2 at `T(□φ)@w` **is** T-saturation-including-the-self-conjunct, for free. Nothing to axiomatize. |
| `noneIffSaturated` | **Rejected as a field; it is a free lemma** | `modalStepBranch_none_saturated` (`Completeness.lean:784-808`) is proved by `simp only [modalStepBranch]`, `List.findSome?_eq_none_iff`, and `rcases` on the `RuleResult` constructor. It touches `modalApplyOne` only opaquely. It generalizes to `modalStepBranchGen apply` with **zero** spec fields. Also: only the `none → saturated` direction is ever used; the `iff` is not needed. |
| Hintikka-lift hook | **Rejected as stated; replaced by F8** | The lift (`modalHintikkaClause_lift`, `Completeness.lean:718`) does **not** need "saturation implies the clause". It needs `modalApplyOne_fst_eq_of_not_box` (`:684`): for non-box/non-diamond `φ`, the result is *independent of `b`/`acc`*. That is a **branch-independence** property, not a saturation property. It is the real F8. |
| — | **Not anticipated** | Four shape-class fields (F9-F12) that the `ModalLoopInv` witness helpers force. These are the actual content of the task and the hypothesis does not mention them. |

Net: the interface grows by **branch-independence + shape-class facts**, not by
saturation-characterisation machinery.

---

## 3. Proposed `RuleApplicationSpec` Extension (7 → 11 fields)

Concrete Lean, to be appended to `structure RuleApplicationSpec` in `GenericDriver.lean:126`.
All four are statable there without new imports (`modalNextWorld`/`boxPropagation` live in
`Branch.lean`; `Accessibility.addEdge` in `Defs.lean` — both already transitively imported).

```lean
  /-- **F8** (task 510) Branch-independence on structural shapes: for a signed formula whose
  formula-component is neither `box`- nor `diamond`-shaped, `apply`'s rule result does not
  depend on the branch or the accessibility relation. Forces `modalHintikkaClauseGen_lift`
  (and, through it, `modalStepBranchGen_hintikka_inv`), which lifts the expanded-set Hintikka
  invariant from the old branch to each strictly larger child branch. Mirrors
  `modalApplyOne_fst_eq_of_not_box` (`Completeness.lean:684`). -/
  localShapeInvariance : ∀ (s : Sign) (φ : Proposition Atom) (w : WorldIndex),
      (∀ ψ, φ ≠ .box ψ) → (∀ ψ, φ ≠ .diamond ψ) →
      ∀ (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
        (acc acc' : Accessibility),
      (apply ⟨s, φ, w⟩ b acc).1 = (apply ⟨s, φ, w⟩ b' acc').1

  /-- **F9** (task 510) Box-positive is never expanding: `apply`'s result on a `T(□ψ)@w`-shaped
  input is always `.notApplicable` or `.persistent` — never `.linear`/`.branching`. Since
  `.persistent` leaves the expanded set unchanged (`modalStepBranchGen`, `Saturation.lean:135-137`),
  this is what makes `modalLoopGen_eBoxOnlyNeg` go through: a `boxPos`-shaped formula can never be
  the `sf_exp` appended to `e`. **The payload is existentially quantified on purpose**: every use
  site discards it (it serves only to contradict the `.linear`/`.branching` case split), and
  quantifying it is exactly what lets T's self-conjunct, B's symmetric propagation, and S5's
  universal propagation discharge this field. Mirrors `modalApplyOne_posBox_eq`
  (`CompletenessLoop.lean:248`), weakened from its concrete `boxPropagation` payload. -/
  boxPosNotExpanding : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex),
      sf.sign = .pos → ∀ (ψ : Proposition Atom), sf.formula = .box ψ →
      ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).1 = .notApplicable ∨
        ∃ out, (apply sf b acc).1 = .persistent out

  /-- **F10** (task 510) Diamond-negative is never expanding: dual of `boxPosNotExpanding`,
  forcing `modalLoopGen_eDiamondOnlyPos`. Mirrors `modalApplyOne_negDia_eq`
  (`CompletenessLoop.lean:274`), likewise payload-weakened. -/
  diaNegNotExpanding : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex),
      sf.sign = .neg → ∀ (ψ : Proposition Atom), sf.formula = .diamond ψ →
      ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).1 = .notApplicable ∨
        ∃ out, (apply sf b acc).1 = .persistent out

  /-- **F11** (task 510) Box-negative witness minting: `apply` on `F(□ψ)@w` is *always*
  applicable, mints the fresh world `modalNextWorld b`, records the edge `w → modalNextWorld b`,
  and heads its `.linear` output with the witness `F(ψ)@(modalNextWorld b)`. Forces
  `modalLoopGen_eBoxNegWitness` (the `eBoxNegWitness` conjunct's fresh-`sf_exp` case) and
  `modalExpandBranchesGen_hintikka`'s conjunct-3 discharge at a saturated leaf (where
  always-applicability rules out the `.notApplicable` alternative). Mirrors
  `modalApplyOne_boxNeg_witness` (`CompletenessLoop.lean:464`). -/
  boxNegWitness : ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc : Accessibility) (ψ : Proposition Atom) (w : WorldIndex),
      (apply (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
          = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (apply (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex)
                :: rest)

  /-- **F12** (task 510) Diamond-positive witness minting: dual of `boxNegWitness`, forcing
  `modalLoopGen_eDiamondPosWitness` and `modalExpandBranchesGen_hintikka`'s conjunct-4
  discharge. Mirrors `modalApplyOne_diamondPos_witness` (`CompletenessLoop.lean:566`). -/
  diaPosWitness : ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc : Accessibility) (ψ : Proposition Atom) (w : WorldIndex),
      (apply (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
          = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (apply (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex)
                :: rest)
```

### A candidate field that is NOT needed

`modalApplyOne_hasEdge_mono` (`CompletenessLoop.lean:451`) — "acc edges only grow" — looks like a
required field. It is not. Its only input is `modalLoop_snd_eq_or_addEdge` (`:432`), whose
statement is **verbatim the existing `freshLocal` field** (`GenericDriver.lean:131-135`); its
docstring even says it is a "local restatement of the `private` `modalApplyOne_fresh_local`". So
`modalApplyGen_hasEdge_mono` is derivable from `freshLocal` + `hasEdge_addEdge_mono` (`:423`,
already rule-agnostic), and `modalLoop_snd_eq_or_addEdge` should be **deleted** in favour of
`spec.freshLocal`. Field count therefore lands at **11, not 12**.

### New generic definitions (not fields)

```lean
-- Saturation.lean, beside `modalHintikkaSet` (:423). Substitution only.
def modalHintikkaSetGen (apply : RuleApply Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) : Prop :=
  isModalClosed b = false ∧
  (∀ sf ∈ b,
    let (result, _) := apply sf b acc
    match sf.sign, sf.formula with
    | .neg, .box _ => True
    | .pos, .diamond _ => True
    | _, _ =>
      match result with
      | .linear newForms => ∀ sf' ∈ newForms, sf' ∈ b
      | .branching branches => ∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b
      | .persistent newForms => ∀ sf' ∈ newForms, sf' ∈ b
      | .notApplicable => True) ∧
  (∀ (φ : Proposition Atom) (w : WorldIndex),
    ⟨.neg, .box φ, w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.neg, φ, w'⟩ ∈ b) ∧
  (∀ (φ : Proposition Atom) (w : WorldIndex),
    ⟨.pos, .diamond φ, w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.pos, φ, w'⟩ ∈ b)

theorem modalHintikkaSet_eq (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : modalHintikkaSet b acc = modalHintikkaSetGen modalApplyOne b acc := rfl

-- Completeness.lean, beside `modalHintikkaClause` (:665). Substitution only.
def modalHintikkaClauseGen (apply : RuleApply Atom) (s : Sign) (φ : Proposition Atom)
    (w : WorldIndex) (X : List (SignedFormula (Proposition Atom) WorldIndex))
    (Y : Accessibility) : Prop :=
  match φ with
  | .box _ => True
  | .diamond _ => True
  | _ =>
    match (apply ⟨s, φ, w⟩ X Y).1 with
    | .linear out => ∀ sf' ∈ out, sf' ∈ X
    | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ X
    | .persistent out => ∀ sf' ∈ out, sf' ∈ X
    | .notApplicable => True

theorem modalHintikkaClause_eq (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (X : List (SignedFormula (Proposition Atom) WorldIndex)) (Y : Accessibility) :
    modalHintikkaClause s φ w X Y = modalHintikkaClauseGen modalApplyOne s φ w X Y := rfl
```

**Keep both definitions** (do not redefine `modalHintikkaSet`/`modalHintikkaClause` as
instantiations). This mirrors the deliberate `modalStepBranch` / `modalStepBranchGen` +
`modalStepBranch_eq` precedent (`Saturation.lean:140-178`), whose docstring records that "14+ call
sites … rely on this exact unfold shape". `modalHintikkaClause` is unfolded via `unfold` /
`simp only` at six sites; preserving the original `def` keeps those normal forms intact.

Note the clause carve-out is **coarser** than the set's: the clause is vacuous for *any*
box/diamond-shaped `φ` (both signs), while `modalHintikkaSetGen` conjunct 2 carves out only
`.neg,.box` and `.pos,.diamond`. That gap is exactly what `eBoxOnlyNeg`/`eDiamondOnlyPos` — and
hence F9/F10 — exist to close. This coarseness is forced: the clause must be liftable along branch
growth, and both Propagating shapes are `b`/`acc`-dependent, so they cannot be lifted.

---

## 4. Lemma-by-Lemma Mapping

`Loop` = `CompletenessLoop.lean`; `Comp` = `Completeness.lean`; `Sat` = `Saturation.lean`;
`Snd` = `Soundness.lean`. "Field" = the spec field discharging the rule-specific step.

| Existing K lemma (location) | Proposed generic | Field | Notes |
|---|---|---|---|
| `modalHintikkaSet` (Sat:423, def) | `modalHintikkaSetGen apply` | — | substitution; `_eq` by `rfl` |
| `modalHintikkaClause` (Comp:665, def) | `modalHintikkaClauseGen apply` | — | substitution; `_eq` by `rfl` |
| `modalApplyOne_fst_eq_of_not_box` (Comp:684) | *becomes* **F8** | **F8** | existing proof body = K's discharge; de-privatize |
| `modalHintikkaClause_lift` (Comp:718) | `modalHintikkaClauseGen_lift` | **F8** | 5 identical case blocks + 2 `trivial`; F8 is its only input |
| `modalStepBranch_none_saturated` (Comp:784) | `modalStepBranchGen_none_saturated` | **none** | driver-structural; verified rule-agnostic |
| `modalStepBranch_hintikka_inv` (Comp:822) | `modalStepBranchGen_hintikka_inv` | **F8** | via `_lift` + F8 directly; rest is driver case-split |
| `modalMaxWorld_lt_worldBound_of_phiBound` (Loop:127) | unchanged | none | pure arithmetic |
| `modalLoop_bClosure` (Loop:162) | `modalLoopGen_bClosure` | `outputsSubsetUniverse` (existing) | |
| `modalStepBranch_newExps_const` (Loop:216) | `modalStepBranchGen_newExps_const` | **none** | driver-structural |
| `modalApplyOne_posBox_eq` (Loop:248) | → **F9**'s K discharge | **F9** | relocate to `Rules.lean`; weaken payload to `∃ out` |
| `modalApplyOne_negDia_eq` (Loop:274) | → **F10**'s K discharge | **F10** | relocate to `Rules.lean`; weaken payload |
| `modalLoop_eBoxOnlyNeg` (Loop:303) | `modalLoopGen_eBoxOnlyNeg` | **F9** | statement mentions no `apply` — already rule-agnostic |
| `modalLoop_eDiamondOnlyPos` (Loop:364) | `modalLoopGen_eDiamondOnlyPos` | **F10** | ditto |
| `hasEdge_addEdge_mono` (Loop:423) | unchanged | none | pure `Accessibility` fact |
| `modalLoop_snd_eq_or_addEdge` (Loop:432) | **delete** | `freshLocal` (existing) | statement ≡ `freshLocal` verbatim |
| `modalApplyOne_hasEdge_mono` (Loop:451) | `modalApplyGen_hasEdge_mono` | `freshLocal` (existing) | **no new field** |
| `modalApplyOne_boxNeg_witness` (Loop:464) | → **F11**'s K discharge | **F11** | relocate to `Rules.lean` |
| `modalLoop_eBoxNegWitness` (Loop:487) | `modalLoopGen_eBoxNegWitness` | **F11** + `freshLocal` | statement rule-agnostic |
| `modalApplyOne_diamondPos_witness` (Loop:566) | → **F12**'s K discharge | **F12** | relocate to `Rules.lean` |
| `modalLoop_eDiamondPosWitness` (Loop:589) | `modalLoopGen_eDiamondPosWitness` | **F12** + `freshLocal` | statement rule-agnostic |
| `modalStepBranch_preserves_accFreshInv` (**Snd:113**) | `modalStepBranch_preserves_accFreshInv_gen` | `freshLocal` (existing) | **gap**: only step lemma with no `_gen` |
| `ModalLoopInv` (Loop:57, structure) | `ModalLoopInvGen apply` | — | only `hintikkaInv` mentions `apply`; other 6 conjuncts already rule-agnostic |
| `modalStep_preserves_invariant` (Loop:671) | `modalStepGen_preserves_invariant` | composes | bundled `spec` available here |
| `modalExpandBranches_hintikka` (Loop:746) | `modalExpandBranchesGen_hintikka` | **F9,F10,F11,F12** at the leaf | **the crux**; ~305 lines. **Must conclude in `modalHintikkaSetGen apply bR aR`** (§0) |
| `hintikka_box_neg` (Comp:198) | `hintikka_box_neg_gen` | **none** | pure projection of conjunct 3; free |
| `hintikka_diamond_pos` (Comp:211) | `hintikka_diamond_pos_gen` | **none** | pure projection of conjunct 4; free |
| `hintikka_box_pos` (Comp:146) | ❌ **not generalizable** | — | reads `boxPropagation`'s payload; per-system. **Out of 510's scope** (§0) |
| `hintikka_diamond_neg` (Comp:230) | ❌ **not generalizable** | — | ditto. Out of scope |
| `modalStepBranch_mem_preserved` (Loop:1058) | `modalStepBranchGen_mem_preserved` | **none** | branches only grow |
| `modalExpandBranches_openBranch_initial_mem` (Loop:1096) | `_gen` | **none** | needed by 503; free |
| `modalLoopInv_initial` (Loop:1217) | `modalLoopInvGen_initial` | **none** | 5 rule-dependent conjuncts vacuous over `e = []` |
| `modalTableau_complete` (Loop:1290) | K corollary | — | statement byte-identical |
| `modalTableau_decides` (Loop:1334) | untouched | — | byte-identical |
| `instDecidableKValid` (Loop:1346) | untouched | — | byte-identical |

### Where F9-F12 are consumed at the saturated leaf

`modalExpandBranches_hintikka`'s conjunct-2 discharge (Loop:849-911) is a `cases φ` over 7
constructors × 2 signs collapsing to exactly three patterns, each already verified generic:

- **Structural** (Loop:853-887): `hintikkaInv` gives the clause, definitionally equal to
  `modalHintikkaSetGen`'s conjunct-2 body for that shape (`simp only [modalHintikkaClause] at hc;
  cases s <;> exact hc`); else `.notApplicable` → `simp [hna]`. Both survive substitution of `apply`.
- **Minting** (Loop:896-898, 901-904): `trivial` — carved out of conjunct 2.
- **Propagating** (Loop:890-895, 905-911): `eBoxOnlyNeg`/`eDiamondOnlyPos` contradict `sf ∈ e`;
  else `.notApplicable` → `simp [hna]`. These invariants are preserved by **F9/F10**.

Conjuncts 3/4 (Loop:912-928) use `eBoxNegWitness`/`eDiamondPosWitness` plus
`modalApplyOne_boxNeg_witness`/`_diamondPos_witness` to rule out the `.notApplicable` alternative
— i.e. **F11/F12**.

---

## 5. Import-Cycle Constraint and Recommended Layout

The actual edge (from `FmpMeasure.lean:17`, which the 507 summary does not mention):

```
Rules → Saturation → Completeness → FmpMeasure → GenericDriver → TDriver
                            ↘  SoundnessStep → Soundness ↘
                                                   CompletenessLoop  (imported only by Cslib.lean)
```

Two distinct regimes — this is the key layout finding, and it is **not** uniformly 507's:

1. **`Completeness.lean` is UPSTREAM of `GenericDriver.lean`** (via
   `FmpMeasure.lean:17 import …Completeness`). So `Completeness.lean` **cannot** import
   `GenericDriver.lean`, and its `_gen` lemmas must take **raw unbundled hypotheses** — exactly
   507's pattern. Mitigating factor: they need **only one** raw parameter (F8).
   `GenericDriver.lean` then supplies bundled wrappers, as in 507.

2. **`CompletenessLoop.lean` is a leaf** — nothing imports it except the `Cslib.lean` barrel
   (verified by grep). It may therefore `public import Cslib.Logics.Modal.Tableau.GenericDriver`
   with no cycle, and its `_gen` lemmas **can take `spec : RuleApplicationSpec apply` directly**.
   This is strictly better ergonomics than 507 achieved, and it covers the bulk of the work
   (~700 of the ~850 lines).

3. **`Soundness.lean`** must host `modalStepBranch_preserves_accFreshInv_gen` with a raw
   `freshLocal` parameter (keeping Soundness's import surface minimal and shake-clean).
   `CompletenessLoop.lean` imports both `Soundness` and `GenericDriver`, so it can call
   `modalStepBranch_preserves_accFreshInv_gen apply spec.freshLocal …` — no wrapper needed.

### Relocation requirement (important, easy to miss)

F9-F12's K discharges (`modalApplyOne_posBox_eq`, `_negDia_eq`, `_boxNeg_witness`,
`_diamondPos_witness`) are currently **`private` in `CompletenessLoop.lean`** — which is
*downstream* of `GenericDriver.lean`. `modalApplyOne_spec` (GenericDriver:223) therefore cannot
reach them. They must be **relocated to `Rules.lean`** (the root of the chain, where
`modalApplyOne` is defined; `boxPropagation` and `modalNextWorld` live in `Branch.lean`, which
`Rules.lean` already imports). F8's K discharge is already in `Completeness.lean` (upstream of
GenericDriver) and only needs de-privatizing.

**Bonus**: `TDriver.lean:96,118,140,153` currently carries four `private` duplicates of these same
K facts (`modalApplyOne_boxPos_shape`, `_diamondNeg_shape`, `_boxPos_acc_eq`,
`_diamondNeg_acc_eq`). Relocating canonical versions to `Rules.lean` lets TDriver drop them.

### Recommendation: extend in place; do NOT create new files

The alternative (`CompletenessGen.lean` / `CompletenessLoopGen.lean`) buys nothing: the
`Completeness.lean` constraint is unavoidable either way, and `CompletenessLoop.lean` is already a
leaf. New files would add barrel churn (`lake exe mk_all --module`) and split the K corollaries
from their generic sources. Extend the five existing files.

---

## 6. Reuse of Task 507's Assets

**Confirmed: yes**, `ModalLoopInv`'s potential/world-bound conjuncts reuse 507 directly.
`modalStep_preserves_invariant` (Loop:671-721) calls exactly eight step lemmas; seven already have
`_gen` forms from 507:

| Call site (Loop) | 507 asset | Available? |
|---|---|---|
| `modalStepBranch_potential_step` (:687) | `modalStepBranchGen_potential_step` (GenericDriver:341) | ✅ bundled |
| `modalStepBranch_preserves_accTargetsKnown` (:691) | `modalStepBranchGen_preserves_accTargetsKnown` (:284) | ✅ bundled |
| `modalStepBranch_preserves_outDegEq` (:694) | `modalStepBranchGen_preserves_outDegEq` (:241) | ✅ bundled |
| `modalStepBranch_preserves_expandedNodup` (:696) | `..._expandedNodup_gen` (FmpMeasure:825) | ✅ takes **no** field |
| `modalStepBranch_eClosure` (:700) | `modalStepBranchGen_eClosure` (:319) | ✅ bundled |
| `modalExpMeasure_step_lt` (:717) | `modalStepBranchGen_expMeasure_step_lt` (:386) | ✅ bundled |
| `modalMaxWorld_lt_worldBound_of_phiBound` (:685) | — | rule-agnostic already |
| `modalStepBranch_preserves_accFreshInv` (:689) | — | ❌ **the one gap** (Soundness:113) |

`modalStepBranchGen_worldBound` (:365) is used via `modalLoopInvGen_initial`/`phiBound`. So 507
covers essentially the entire non-Hintikka half of `ModalLoopInv` and this task's genuine surface
is only the five rule-dependent conjuncts.

---

## 7. K Zero-Regression: Can the Statements Stay Byte-Identical?

**Yes, unconditionally, for the three named targets** — `kValid`, `modalTableau_decides`
(Loop:1334), `instDecidableKValid` (Loop:1346) are **not touched at all**: they reference only
`modalTableau_complete`/`modalTableau_sound`, whose statements are preserved. This is a stronger
result than 507's (which had to re-prove its three corollaries).

Byte-identical statements achievable across the board:

| Declaration | Byte-identical statement? | Proof body |
|---|---|---|
| `instDecidableKValid`, `modalTableau_decides` | ✅ (untouched) | untouched |
| `modalTableau_complete` | ✅ | unchanged modulo `modalHintikkaSet_eq` (a `rfl`) |
| `modalHintikkaSet`, `modalHintikkaClause` | ✅ (originals retained) | unchanged |
| `modalExpandBranches_hintikka`, `modalStep_preserves_invariant`, `modalStepBranch_hintikka_inv`, `modalStepBranch_none_saturated` | ✅ | become one-line corollaries via `modalStepBranch_eq` / `modalExpandBranches_eq` |
| `modalStepBranch_preserves_accFreshInv` | ✅ | one-line corollary |
| **`ModalLoopInv`** | ⚠️ **the one at-risk declaration** | see below |

`ModalLoopInv` (Loop:57) is a public `structure` listed in the module's "Main Definitions". Two
options:

- **Recommended**: keep `ModalLoopInv` as its own byte-identical `structure`, add
  `ModalLoopInvGen apply` alongside, and bridge with
  `ModalLoopInv_iff_gen : ModalLoopInv φ0 b e acc rank ↔ ModalLoopInvGen modalApplyOne φ0 b e acc rank`
  (~6 lines, constructor/destructor). Mirrors the `modalStepBranch`/`modalStepBranchGen` precedent
  and yields **total** byte-identity.
- **Cheaper but lossy**: `abbrev ModalLoopInv := ModalLoopInvGen modalApplyOne`. Projections
  (`hinv.hintikkaInv`) resolve through the abbrev, but the anonymous-constructor destructuring at
  Loop:683 (`obtain ⟨hpot, hphi, hhint, hboxneg, hboxwit, hdiapos, hdiawit⟩ := hinv`) and the
  7-field `refine ⟨…⟩` at Loop:1228 are elaboration risks, and the declaration kind changes from
  `structure` to `abbrev`.

Take the first option.

---

## 8. Recommended Phase Decomposition

Eight phases, each sized to one agent run (507's proven shape). Every phase ends at a green
`lake build` + commit.

| P | Scope | Files | Est. lines | Risk |
|---|---|---|---|---|
| **1** | Relocate the four K shape/witness lemmas to `Rules.lean` with `∃ out`-weakened payloads for the two Propagating ones (`modalApplyOne_boxPos_eq`, `_diamondNeg_eq`, `_boxNeg_witness`, `_diamondPos_witness`); delete the `CompletenessLoop.lean` privates; de-privatize `modalApplyOne_fst_eq_of_not_box`. Pure relocation, zero proof-content change. | `Rules.lean`, `Completeness.lean`, `CompletenessLoop.lean` | ~120 | Low |
| **2** | `modalHintikkaSetGen` + `modalHintikkaSet_eq` (Saturation). Add **F8-F12** to `RuleApplicationSpec`; extend `modalApplyOne_spec` with the five P1 discharges. | `Saturation.lean`, `GenericDriver.lean` | ~140 | Low |
| **3** | `modalHintikkaClauseGen` + `_eq`; `modalHintikkaClauseGen_lift` (raw F8); `modalStepBranchGen_none_saturated` (no field); `modalStepBranchGen_hintikka_inv` (raw F8); `hintikka_box_neg_gen` + `hintikka_diamond_pos_gen` (free projections, for 505/506); K corollaries byte-identical. Bundled wrappers in `GenericDriver.lean`. | `Completeness.lean`, `GenericDriver.lean` | ~230 | Low-Med |
| **4** | `modalStepBranch_preserves_accFreshInv_gen` (raw `freshLocal`) + byte-identical K corollary. Closes the one 507 gap. | `Soundness.lean` | ~60 | Low |
| **5** | `CompletenessLoop.lean` imports `GenericDriver`. `ModalLoopInvGen` + `ModalLoopInv_iff_gen`. `modalLoopGen_bClosure`, `modalStepBranchGen_newExps_const`, `modalApplyGen_hasEdge_mono`; **delete** `modalLoop_snd_eq_or_addEdge`. | `CompletenessLoop.lean` | ~150 | Low-Med |
| **6** | The four witness-invariant preservation helpers: `modalLoopGen_eBoxOnlyNeg` (F9), `_eDiamondOnlyPos` (F10), `_eBoxNegWitness` (F11+`freshLocal`), `_eDiamondPosWitness` (F12+`freshLocal`). | `CompletenessLoop.lean` | ~230 | Med |
| **7** | **CRUX**: `modalStepGen_preserves_invariant` + `modalExpandBranchesGen_hintikka`. **Acceptance criterion: the loop lemma must conclude in `modalHintikkaSetGen apply bR aR`, NOT the concrete `modalHintikkaSet` (§0)** — otherwise 505/506 stay blocked and the task's purpose is defeated. K corollary byte-identical via `modalExpandBranches_eq` + `modalHintikkaSet_eq`. | `CompletenessLoop.lean` | ~380 | **High** |
| **8** | `modalLoopInvGen_initial` (no field), `modalStepBranchGen_mem_preserved`, `modalExpandBranchesGen_openBranch_initial_mem`; byte-identity diff of `kValid`/`modalTableau_complete`/`modalTableau_decides`/`instDecidableKValid` vs. pre-510; module docstrings; full CI + `#print axioms` sweep. | `CompletenessLoop.lean`, `GenericDriver.lean` | ~150 | Low |
| **9** *(optional, ~15 lines)* | `modalStepBranchT_eq`/`modalExpandBranchesT_eq`/`modalTableauT_eq` (all `rfl`) in `TDriver.lean`. | `TDriver.lean` | ~15 | Low |

### What 503 gets

`TDriver.lean:76` defines `modalExpandBranchesT := modalExpandBranchesGen modalApplyOneT …`
**definitionally**, and `modalApplyOneT_spec` (`:759`) already exists. So after P8, 503's blocking
lemma is a one-liner:

```lean
theorem modalExpandBranchesT_hintikka (φ0 : Proposition Atom) (fuel : Nat) : … :=
  modalExpandBranchesGen_hintikka modalApplyOneT modalApplyOneT_spec φ0 fuel …
```

plus five new `modalApplyOneT_*` field discharges appended to `modalApplyOneT_spec` — each
mechanical (see §9). **Task 510 need not touch `TDriver.lean` at all** except for those
discharges; P9 is a convenience.

### What 505 (B) and 506 (S4) get — and what they must still budget for

| | Gets from 510 | Must still do itself |
|---|---|---|
| **505 (B)** | Full generic chain + spec discharge (B is a legitimate `RuleApplicationSpec` instance: `.persistent` propagation along `SymmGen`, never mints) → `modalExpandBranchesB_hintikka` as a one-liner | Its own `hintikka_box_pos`/`hintikka_diamond_neg` analogues (payload-reading, §0), and its truth lemma |
| **506 (S4)** | **Statement shape only**: `modalHintikkaSetGen (modalApplyOneS4 φ0)` + the two free projection bridges. Spec-free, so unaffected by the S4 exclusion | Its own `modalHintikkaSetS4` witness (S4 cannot use the loop lemma — it cannot discharge the spec), its own payload-reading bridges, its own truth lemma |

506's phase is therefore **unblocked at the type level** by 510, not delivered by it. That is the
most 510 can honestly offer S4 given `GenericDriver.lean:105-108`, and it is what 506's planner
asked for.

---

## 9. Why T/B/S5 Discharge F8-F12 Cheaply

From `FrameRules.lean:72-95` (`modalApplyOneT`'s full body) — every new field lands on a shape
where T is *definitionally* K, or in the Propagating class where the payload is quantified away:

| Field | T's discharge | Why it works |
|---|---|---|
| **F8** | `modalApplyOneT_eq_of_not_boxPos_diaNeg` + K's `modalApplyOne_fst_eq_of_not_box` | non-box/non-diamond `φ` falls into `modalApplyOneT`'s `| _, _ => (kResult, kAcc)` arm |
| **F9** | `modalApplyOneT_boxPos_fst` (TDriver:214) + K's `modalApplyOne_boxPos_eq` | T maps `.persistent ↦ .persistent`, `.notApplicable ↦ .notApplicable \| .persistent selfNew`; **stays in class** |
| **F10** | `modalApplyOneT_diamondNeg_fst` (TDriver:249) + K's `_diamondNeg_eq` | dual |
| **F11** | K's `modalApplyOne_boxNeg_witness` directly | `⟨.neg, .box ψ, w⟩` has sign `.neg`, so it misses T's `.pos, .box` arm → `_, _` arm → `= modalApplyOne` |
| **F12** | K's `modalApplyOne_diamondPos_witness` directly | `⟨.pos, .diamond ψ, w⟩` misses T's `.neg, .diamond` arm → `= modalApplyOne` |

**Had F9/F10 been stated with K's concrete payload** (`.persistent (boxPropagation b acc ψ
sf.label)`, as `modalApplyOne_posBox_eq` currently is), **T could not discharge them** — T's
payload is `kForms ++ selfNew.filter …`. This is the single most important design decision in the
task, and it is the direct answer to the prompt's "saturation is genuinely rule-dependent"
concern: the rule-dependence is real, but it is confined entirely to the Propagating payload,
which the chain never reads.

B and S5 follow the identical pattern: both propagate `.persistent` at existing worlds (along
`SymmGen`/`EqvGen` closures respectively), never mint, and agree with K on the Minting and
Structural shapes. `GenericDriver.lean:88-108` already commits to this discharge shape for the
existing seven fields; F8-F12 do not disturb it. S4 remains excluded for the reason recorded there
(loop-checking vs. depth-based `modalWorldBound`), unchanged by this task.

---

## 10. Honest Feasibility Assessment and Risks

**Feasibility: high.** I did not find a lemma that resists abstraction. The chain is more
tractable than 507's counting measure, for three reasons: (a) the bulk of it lives in a *leaf*
module that can import `GenericDriver` and use bundled `spec`; (b) 4 of `ModalLoopInv`'s 5
rule-dependent conjuncts have *statements that mention no `apply` at all* (only their preservation
proofs need fields); (c) 507 already delivered 7 of the 8 step lemmas `modalStep_preserves_invariant`
composes.

**Risks, ordered:**

1. **P7 volume (High).** `modalExpandBranches_hintikka` is ~305 lines: an outer `induction fuel`,
   a `suffices key` inner induction over the `processNext` worklist, and three-parallel-list
   threading. `modalExpandBranches` is a *separate definition* from `modalExpandBranchesGen` (each
   with its own `processNext` well-founded helper), so the generic proof must be **re-derived
   against `modalExpandBranchesGen.processNext`**, not reused. Mitigation: it is a pure
   substitution port (`modalApplyOne ↦ apply`, `modalStepBranch ↦ modalStepBranchGen apply`); the
   only semantically-loaded region is the saturated-leaf discharge (Loop:849-928), which §4 above
   verifies reduces exactly to F9-F12; and `modalExpandBranches_eq` (Saturation:~308, already
   proved via a processNext-level agreement lemma) guarantees K's corollary lands. If P7 overruns,
   split it: P7a = `modalStepGen_preserves_invariant`, P7b = the top loop.
2. **`ModalLoopInv` bridging (Medium).** The 7-field anonymous constructor/destructor at Loop:683
   and Loop:1228. Mitigated by the recommended keep-both-plus-`Iff` option (§7).
3. **`Rules.lean` relocation (Low).** May surface `shake` / `dupNamespace` / `topNamespace`
   findings, and `Rules.lean` currently holds a single `def`. Contained to P1.
4. **F9/F10 payload weakening (Low, but load-bearing).** If an implementer "helpfully" states
   these with K's concrete payload to match `modalApplyOne_posBox_eq` verbatim, T/B/S5 discharge
   becomes impossible and the task silently regresses to a K-only refactor. Call this out in the
   plan.

**No `sorry`-deferral is anticipated or acceptable.** No new axiom is required. If P7 proves
intractable, the correct outcome is `[BLOCKED]` on `modalExpandBranchesGen_hintikka` with the goal
state recorded — but on the evidence (every rule-specific step in the leaf discharge already
mapped to a field), I judge this unlikely.

**Counter-finding I looked for and did not find:** a lemma where the chain *reads* a Propagating
payload, or where the Minting-shape set differs between K and T/B/S5. Either would have sunk the
abstraction. Neither exists: the Propagating payload is discarded at all four use sites
(Loop:331, 349, 392, 410), and T's minting shapes are literally K's (`FrameRules.lean:79,87` guard
on `.pos,.box` / `.neg,.diamond` — the complements of the Minting pair).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
* Task 507 summary: `specs/507_generalize_k_fmp_termination_measure_over_ruleapplicationspec/summaries/01_generalize-fmp-termination-measure-summary.md`
* Task 503 handoff: `specs/503_generalize_k_tableau_driver_and_complete_tsystem_decidabilit/.orchestrator-handoff.json`
