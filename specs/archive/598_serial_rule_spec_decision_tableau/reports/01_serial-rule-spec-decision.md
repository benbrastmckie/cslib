# Serial-Successor Rule Spec: Measured Decision

**Type**: cslib research | **HEAD**: `ad19c80d` | **Session**: `sess_1786256926_bebabc`

**Verification basis**: every claim marked **[MACHINE-CHECKED]** is a theorem in
`specs/598_serial_rule_spec_decision_tableau/prototype/DSerialPrototype.lean` (351 lines), which
compiles under `lake env lean` at HEAD with zero errors, zero `sorry`, and `#print axioms`
reporting only `propext` / `Classical.choice` / `Quot.sound`. Every line anchor was re-read at
HEAD.

---

## 0. Headline

**The premise of the task is wrong, and the prototype proves it.** D's seriality rule does *not*
have to mint at the box-positive shape, and therefore does *not* need
`RuleApplicationSpec.boxPosNotExpanding` (F9) weakened. A D rule built as two **persistent**
dual arms —

```
T(□ψ)@w  ⊢  T(◇ψ)@w        F(◇ψ)@w  ⊢  F(□ψ)@w
```

— satisfies F9 and F10 verbatim **[MACHINE-CHECKED]**, delegates all world-minting to K's
existing `boxNeg`/`diaPos` arms, and terminates (unlike the refuted `F(□⊥)` seeding, because
`◇ψ` has the *same* modal depth as `□ψ`, so `rankStep`'s exact-decrement invariant is
untouched).

The field that actually fails is **F2 `outputsSubsetUniverse`**, and it fails for a *universe*
reason, not a *rule-shape* reason: `◇ψ ∉ modalSubfmls φ0` when only `□ψ` is a subformula. This
is also **[MACHINE-CHECKED]** (`modalApplyOneD_outputsSubsetUniverse_fails`).

**Recommendation: do not build `RuleApplicationSpecSerial`.** Build the dual-persistent rule and
close the F2 gap with a dual-closed universe. Two variants are costed in §4; the recommended one
(**E2**) is fully additive, needs no change to `isMintingShaped`, `outDeg`, the potential
function, `modalWorldBound`, `modalFuel`, or any loop invariant, and leaves the existing
`RuleApplicationSpec` and all seven of its discharge sites untouched.

---

## 1. What the prior research got right, and where it went wrong

`specs/548_.../reports/01_eight-corner-decidability-research.md` §5.1 is correct that:

- `boxPosNotExpanding` (`GenericDriver.lean:239-243`) forbids `.linear` at the box-positive
  shape, and `.linear` is the only constructor that can accompany a mint (`freshLocal`,
  `GenericDriver.lean:184-188`; `knownWorldsStep`'s second disjunct,
  `GenericDriver.lean:333-338`, explicitly makes `.persistent`/`.branching` a `False` case for a
  minting step). **A persistent rule can never mint. Confirmed.**
- Self-loop-at-dead-ends *as a rule licence* is the T axiom, not D. Confirmed.
- The fresh-sink relocation does not discharge the obligation. Confirmed.
- `F(□⊥)` seeding is non-terminating: `□⊥` has constant modal depth, so the minted successor is
  itself a dead end. Confirmed.

Its error is the step "**A correct D tableau must mint at a dead-end world *because of* its
box-positive content**" (§5.1). That is false. The obligation `□ψ → ◇ψ` can be discharged in two
steps — *derive the diamond, then let K's existing diamond-positive mint arm fire* — and the
derivation step is a pure persistent propagation at the same world. The third refuted
alternative (`F(□⊥)` seeding) is the *degenerate* case of this idea, seeding a depth-constant
formula instead of the depth-preserving dual; §5.1 refuted the degenerate case and read the
refutation as covering the general one.

Note also that §5.1's own self-loop refutation is about a *rule licence*. A self-loop closure
applied only at *model-extraction* time remains available and is in fact required by the
recommended design (§3.3) — but it is truth-lemma-neutral there, because with the dual arms
present no dead-end world carries any modal formula at all.

---

## 2. The prototype: what is machine-checked

File: `specs/598_serial_rule_spec_decision_tableau/prototype/DSerialPrototype.lean`.

`modalApplyOneD` is a structural clone of `modalApplyOneT` (`FrameRules.lean:85-108`) with the T
self-propagation helpers replaced by the D duals:

```lean
def modalDBoxDual (b) (φ) (w) : List (SignedFormula (Proposition Atom) WorldIndex) :=
  let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, .diamond φ, w⟩
  if b.any (· == sf) then [] else [sf]
-- modalDDiaNegDual: the ⟨.neg, .box φ, w⟩ dual
```

merged into K's persistent output exactly as T merges `modalTBoxSelf`.

| Field | Status for `modalApplyOneD` | Evidence |
|---|---|---|
| F1 `freshLocal` | **discharged** | `modalApplyOneD_freshLocal` **[MACHINE-CHECKED]** |
| F2 `outputsSubsetUniverse` | **FAILS** | `modalApplyOneD_outputsSubsetUniverse_fails` **[MACHINE-CHECKED]** |
| F3 `persistentFresh` | dischargeable | T's proof shape; dual is `b.any`-guarded and the `.notApplicable` guard forces nonemptiness |
| F4 `rankStep` | dischargeable | only content check is `modalDepth (◇ψ) = modalDepth (□ψ)` — `modalDepth_diamond_eq_box`, `rfl` **[MACHINE-CHECKED]** |
| F5 `outDegStep` | dischargeable | D never touches `acc` at the two shapes (`modalApplyOneD_boxPos_snd`/`_diaNeg_snd` **[MACHINE-CHECKED]**), so K's proof transports |
| F6 `knownWorldsStep` | dischargeable | same reason: `acc` unchanged, outputs at the *source* world, already known |
| F7 `branchingLength` | dischargeable | D never produces `.branching` at the two shapes |
| F8 `localShapeInvariance` | **discharged** | `modalApplyOneD_localShapeInvariance` **[MACHINE-CHECKED]** |
| **F9 `boxPosNotExpanding`** | **discharged** | `modalApplyOneD_boxPosNotExpanding` **[MACHINE-CHECKED]**, 18 lines |
| **F10 `diaNegNotExpanding`** | **discharged** | `modalApplyOneD_diaNegNotExpanding` **[MACHINE-CHECKED]**, 18 lines |
| F11' `boxNegWitness'` | **discharged** | `modalApplyOneD_boxNegWitness` **[MACHINE-CHECKED]** |
| F12' `diaPosWitness'` | **discharged** | `modalApplyOneD_diaPosWitness` **[MACHINE-CHECKED]** |

Six fields fully proved, five argued from T's transported proof shape, exactly one genuine
failure.

### 2.1 The F2 counterexample, stated exactly

`modalApplyOneD_outputsSubsetUniverse_fails` proves the negation of F2's statement at
`Atom := Nat`, with all four hypotheses discharged:

- `φ0 := □p`, `b := [T(□p)@0]`, `acc := Accessibility.empty`, `p := atom 0`
- `∀ x ∈ b, x ∈ modalUniverse φ0` ✓, `sf ∈ b` ✓, `accFreshInv b acc` ✓ (`accFreshInv_empty`),
  `modalMaxWorld b < modalWorldBound φ0` ✓ (`0 < 9`)
- `(modalApplyOneD sf b acc).fst = .persistent [T(◇p)@0]` (K's `boxPropagation` is empty over an
  empty successor set, so K yields `.notApplicable` and the dual arm fires)
- `modalUniverse_mem_formula` then forces `◇p ∈ modalSubfmls (□p) = [□p, p]` — contradiction.

This is a hard obstruction, not a proof-difficulty artifact: `modalUniverse φ`
(`FmpMeasure.lean:153-156`) is `modalSubfmls φ` × both signs × worlds `0..modalWorldBound φ`,
and `modalSubfmls` (`FmpMeasure.lean:75-82`) is not dual-closed.

### 2.2 Why `.linear`-at-boxPos is worse than §5.1 assessed

For completeness of the record, the mint-at-boxPos design (Route A, the
`RuleApplicationSpecSerial` route) breaks **more** than F9/F10. A `.linear` result puts `sf` into
the expanded set `e` (`Saturation.lean:140-141`), and `outDegStep`
(`GenericDriver.lean:310-319`) requires

```
outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length
```

with `isMintingShaped` (`FmpMeasure.lean:761-765`) recognising only `neg .box` and
`pos .diamond`. A box-positive mint adds an edge while contributing nothing to the right-hand
side, so **F5 `outDegStep` is unsatisfiable too**, and it cannot be repaired by a syntactic
widening of `isMintingShaped` without breaking `outDeg_le_of_expandedNodup`
(`FmpMeasure.lean:1597-1650`): its injectivity argument is `x ↦ x.formula`, which is injective
only because `isMintingShaped` pins the sign per shape. Widening to all four modal shapes maps
`T(□ψ)@w` and `F(□ψ)@w` to the same key, forcing the world-degree bound from
`(modalSubfmls φ0).length` to `2 * (modalSubfmls φ0).length` and hence a re-derivation of
`modalWorldBound` and `modalFuel`. Route A therefore reaches into the potential/measure core
(44 `isMintingShaped` references and 59 `outDeg` references in `FmpMeasure.lean` alone), not
just the loop lemma.

---

## 3. The recommended design (Route E)

### 3.1 Rules

Add to `FrameRules.lean`, alongside the existing T and 4 helpers:

- `modalDBoxDual b φ w` and `modalDDiaNegDual b φ w` (as in the prototype)
- `modalApplyOneD`, merging them into K's persistent output at the two shapes
- `modalApplyOneD_eq_of_not_boxPos_diaNeg` (agreement lemma, mirrors
  `modalApplyOneT_eq_of_not_boxPos_diaNeg`, `FrameRules.lean:113-122`)

### 3.2 Soundness (serial frames)

Both arms are sound for `Relation.Serial`: given `w R u`, `□ψ@w ⊨ ψ@u ⊨ ◇ψ@w`; dually
`¬◇ψ@w ⊨ ¬ψ@u ⊨ ¬□ψ@w`. This plugs into the existing frame-relativised chain
(`FrameSoundness.lean`, `branchSatisfiableIn FC` / `frameValid FC`) with
`dFC := fun r => Relation.Serial r`; the `hAgree`/`hBoxPos`/`hDiaNeg` triple has the same shape
as T's.

### 3.3 Completeness and the extracted frame

Use `extractModelWith` (`FrameCompleteness.lean:87`) — the same Strategy-B
closure-at-extraction the whole cube uses — with

```lean
def serialGen (r : α → α → Prop) : α → α → Prop := fun a b => r a b ∨ ((¬ ∃ c, r a c) ∧ a = b)
```

`Relation.Serial (serialGen r)` holds unconditionally, so the frame instance is free, exactly as
`Std.Symm` is free off `Relation.SymmGen` for B (`FrameCompleteness.lean:432-446`).

The truth lemma is unaffected because **on a D-Hintikka set, every world carrying any modal
formula already has a raw successor**:

- `T(□ψ)@w ∈ b` ⟹ (conjunct 2, persistent clause) `T(◇ψ)@w ∈ b` ⟹ (conjunct 4,
  `Saturation.lean:483-485`) a raw successor exists
- `F(◇ψ)@w ∈ b` ⟹ `F(□ψ)@w ∈ b` ⟹ (conjunct 3) a raw successor exists
- `F(□ψ)@w` / `T(◇ψ)@w` mint their own successors (F11'/F12')

So `serialGen` coincides with the raw relation at every world where a modal clause is ever
evaluated, and the added self-loops sit only at worlds whose branch content is purely atomic.
This is precisely why the self-loop *closure* is admissible here even though the self-loop
*rule* is not: the dual arms have already discharged, inside the tableau, every case where the
loop would have been load-bearing.

### 3.4 Closing F2

The dual arm emits `◇ψ` from `□ψ`. F2 holds iff the universe is dual-closed. Two variants:

**E1 (in-place)**: change `modalSubfmls` itself to
`| .box a => .box a :: .diamond a :: modalSubfmls a` (and dually).

The decisive measurement: **[MACHINE-CHECKED]** `modalSubfmlsDual_length_le` proves the
dual-closed list still satisfies

```
(modalSubfmlsDual φ).length ≤ 2 * modalComplexity φ + 1
```

— the *same* constant as `modalSubfmls_length_le` (`FmpMeasure.lean:86`), because
`modalComplexity (□a) = 1 + modalComplexity a` already pays for both `□a` and `◇a`. Therefore
`modalUniverse_length_le`, `modalWorldBound`, and `modalFuel` need **no** constant change, and
every bound downstream only loosens. `modalSubfmls_length_le` is consumed at exactly four sites
(`FmpMeasure.lean:174`, `:2657`, `CompletenessLoop.lean:216`, `S4/Universe.lean:239`).

Cost: one definition edit + re-proof of the `modalSubfmls`-structural helpers. Risk: 412
`modalSubfmls` references across 15 files, concentrated in `FmpMeasure.lean` (144),
`S5Simplification.lean` (73), `FiveSimplification.lean` (48) — most are opaque
`(modalSubfmls φ0).length` uses, but the subformula-transitivity/membership helpers must be
re-proved and S4's `Universe.lean` (27 refs) audited. **Not additive.**

**E2 (additive, recommended)**: leave `modalSubfmls` alone. Define a dual-augmenting *formula*
transformer

```lean
def modalDualAugment (φ : Proposition Atom) : Proposition Atom  -- φ ∧ ⋀{◇ψ | □ψ ∈ subfmls φ} ∧ ⋀{□ψ | ◇ψ ∈ subfmls φ}
```

and run D's instance of the whole generic chain at `φ0 := modalDualAugment φ` while the tableau
itself still starts from `F(φ)@0`. `modalSubfmls (modalDualAugment φ)` is dual-closed (one round
suffices: the added duals' own subformulas are already present), and `φ ∈ modalSubfmls
(modalDualAugment φ)`, so the initial branch is in the universe. Because `φ⁺` is a genuine
`Proposition`, **every existing measure lemma applies verbatim** — no universe parametrisation,
no constant changes.

The one interface adjustment E2 needs: F2 is stated `∀ φ0, …`
(`GenericDriver.lean:194-203`), but D only satisfies it at dual-closed `φ0`. Fix by *narrowing
the hypothesis*, which is a strict generalisation of every consumer:

- Add an additive sibling `RuleApplicationSpecCoreAt (φ0) (apply)` / `RuleApplicationSpecAt
  (φ0) (apply)` in `GenericDriver.lean`, identical except F2 is fixed at `φ0`, plus the
  projection `RuleApplicationSpec.toAt : RuleApplicationSpec apply → ∀ φ0,
  RuleApplicationSpecAt φ0 apply` (a one-line `{ spec with outputsSubsetUniverse :=
  spec.outputsSubsetUniverse φ0 }`).
- Narrow the raw `hOutputsSubsetUniverse` parameter of `modalExpMeasure_step_lt_gen`
  (`FmpMeasure.lean:3165-3174`) from `∀ φ0 …` to the lemma's own `φ0`. **Measured: it is applied
  exactly once, at that φ0** (`FmpMeasure.lean:3245`), so the body change is deleting one
  argument.
- Update the **five** consumption sites to pass `… φ0`: `CompletenessLoop.lean:458`, `:984`,
  `:1347`, `:1644`, `GenericDriver.lean:548`.

`RuleApplicationSpec` itself and all **seven** of its discharge sites (K
`GenericDriver.lean:355`, T `TDriver.lean:742`, B `BDriver.lean:774`, TB
`TBDriver.lean:845`, Five `FiveSimplification.lean:1277`, Kb5''
`FiveSimplification.lean:2587`, S5w `S5Simplification.lean:2320`) are **untouched**.

---

## 4. Measured cost comparison

| | Route A (`RuleApplicationSpecSerial`, prior proposal) | **Route E2 (recommended)** | Route E1 (in-place dual closure) |
|---|---|---|---|
| F9/F10 change | weakened + new guard field + new mint-propagation field | **none** | none |
| `modalLoopGen_eBoxOnlyNeg` | sibling `_serial` lemma, and the invariant must strengthen from "no boxPos in `e`" to "every boxPos in `e` is fully propagated to all successors" | **none** | none |
| `ModalLoopInvHintikka` (11 fields, `CompletenessLoop.lean:314+`) | sibling structure + sibling `_core` twins (5) + sibling `modalStepHintikka_preserves_inv` + sibling `modalExpandBranchesGen_hintikka` | **none** | none |
| `isMintingShaped` / `outDeg` / `modalPotential` | re-cut over an abstract minting predicate (44 + 59 + 40 refs in `FmpMeasure.lean`) | **none** | none |
| `modalWorldBound` / `modalFuel` | re-derive at `2·Sf` (45 + 21 refs) | **none** | **none** (constant preserved, machine-checked) |
| F2 / universe | unchanged | additive `…At` sibling + 5 one-token call-site edits | `modalSubfmls` def edit + structural-helper re-proofs |
| Additive per the task's criterion | no (loop invariant + measure core) | **yes** | no |
| New-code estimate | 2,500-4,000 lines | **~1,150 lines** | ~950 lines + unbounded audit risk |
| Corners unblocked | D, DB, D4, D5, D45 | **D, DB, D4, D5, D45** | same |

Route E2 line estimate: `FrameRules.lean` +60 (measured — the prototype's rule block compiles at
60 lines), `GenericDriver.lean` +120 (sibling structure + projection + re-stated bundled
wrappers), FmpMeasure/CompletenessLoop ±10 (hypothesis narrowing), new `DDriver.lean` ~850
(`TDriver.lean` is 809 and D's field proofs are the same shape) + ~110 for `modalDualAugment`
and its four lemmas.

**D remains a Tier-A corner.** §5.1's downgrade to "Tier A cost, but blocked on a spec-shape
decision" is resolved: there is no spec-shape blocker, only an additive interface narrowing.

---

## 5. Implementation sequence (for the planner)

The `--hard` gate is not warranted: this is a bounded, T-shaped port, not a divergence-prone
task. Suggested phases, each independently buildable:

1. **`FrameRules.lean`** — `modalDBoxDual`, `modalDDiaNegDual`, `modalApplyOneD`, agreement
   lemma. *Lift verbatim from the prototype (already compiles).* ~60 lines.
2. **`GenericDriver.lean`** — `RuleApplicationSpecCoreAt` / `RuleApplicationSpecAt` /
   `RuleApplicationSpec.toAt`; re-state `modalStepBranchGen_expMeasure_step_lt` against the
   `…At` form. ~120 lines.
3. **Hypothesis narrowing** — `modalExpMeasure_step_lt_gen` + the five consumption sites listed
   in §3.4. Gate: full `lake build` green with no other diff. ~10 lines.
4. **`modalDualAugment`** — definition + `φ ∈ modalSubfmls φ⁺`, dual-closure both directions
   (the prototype's `modalSubfmlsDual_box_dual`/`_dia_dual` are the proof shape),
   `modalDepth φ⁺ = modalDepth φ`, and the entry-measure variant for a single-formula branch
   over `modalUniverse φ⁺`. ~110 lines.
5. **`DDriver.lean`** — the twelve field discharges (six liftable from the prototype), the
   `modalStepBranchD`/`modalExpandBranchesD`/`modalTableauD` triple and its `_eq` bridges, and
   `modalExpandBranchesD_hintikka`. Mirror `TDriver.lean` section-for-section. ~850 lines.
6. **`FrameSoundness.lean` / `FrameCompleteness.lean`** — `dFC`, `serialGen` + its `Serial`
   instance, `extractModelD`, the two new-content Hintikka bridges (box-positive and
   diamond-negative arms), `modalTableauD_sound`, `modalTableauD_complete`,
   `instDecidableDValid`. Scope comparable to T's arm in `FrameCompleteness.lean`.

Note that `FrameSoundness.lean`/`FrameCompleteness.lean` are outside this task's declared
`file_scope` (`GenericDriver.lean`, `FrameRules.lean`, `DDriver.lean`). Phases 1-5 fit the
declared scope and deliver the D driver plus its `RuleApplicationSpecAt` witness; phase 6 (the
`Decidable` instance itself) needs the scope widened or a successor task.

---

## 6. Residual risks

1. **F3-F7 are argued, not proved.** Five fields are claimed dischargeable from T's transported
   proof shape rather than machine-checked. The transport argument is strong (D and T differ
   only in the *content* of the persistent payload, and `modalApplyOneD_boxPos_snd` /
   `_diaNeg_snd` **[MACHINE-CHECKED]** establish that D never touches `acc` at the two shapes,
   which is what F5/F6 turn on), but `rankStep` is the one with genuine content: it needs
   `modalDepth (◇ψ) ≤ rank w` where T needed the strictly easier `modalDepth ψ ≤ rank w`. The
   equality `modalDepth (◇ψ) = modalDepth (□ψ)` is `rfl` **[MACHINE-CHECKED]** and closes it,
   but the surrounding `rankStep` plumbing (108 lines in T) has not been replayed.
2. **`modalDualAugment`'s entry-measure lemma is new.** `modalExpMeasure_entry_le_fuel`
   (`FmpMeasure.lean:214`) is stated for the branch `[F(φ)@0]` at universe `modalUniverse φ`; D
   needs `[F(φ)@0]` at `modalUniverse φ⁺`. The proof route (`modalWork U b e ≤ 2|U|`, then the
   existing `3 ^ (2|U|) ≤ modalFuel` chain at `φ⁺`) is the same, but it is a new lemma.
3. **DB/D4/D5/D45 are not prototyped.** The claim that Route E2 unblocks them rests on the D
   arms being pure persistent propagation, hence combinable with B's `SymmGen` arm and the
   Five family the same way T combines into TB (`TBDriver.lean`). That composition pattern is
   established but not measured here; the §7.2 universal-cluster rule-combinator gate from the
   eight-corner report (gate B) remains independently open.
4. **The `--lit` flag was not used** and no literature source was cited by the task; the design
   above is derived from the codebase, not transcribed from a paper. The dual-rule presentation
   of D is standard (Fitting, *Proof Methods for Modal and Intuitionistic Logics*, Ch. 2, already
   cited in `Rules.lean`), but no page-level grounding was performed.
