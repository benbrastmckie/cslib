# Research Report: Porting the CompletenessLoop Hintikka Chain to `RuleApplicationSpecAt`

**Task**: 601 — CompletenessLoop `...At` Hintikka chain
**Date**: 2026-08-09
**Session**: sess_1786289820_d4b093
**Status**: Route selected and **empirically verified end-to-end** (full `lake build` green)

---

## 1. Headline Verdict

**Neither Route 1 (additive `...At` twins, ~755 lines) nor Route 2 (full unbundling to raw
hypotheses) is required.**

A third route — **in-place bundled narrowing**: change each declaration's hypothesis type from
`RuleApplicationSpecCore apply` to `RuleApplicationSpecCoreAt φ0 apply` (and
`RuleApplicationSpec apply` to `RuleApplicationSpecAt φ0 apply`), reusing the `φ0` parameter
each declaration *already has* — was written, compiled, and verified during this research pass.

**Verification performed (working tree reverted afterward; patch preserved):**

| Gate | Result |
|------|--------|
| `lake build Cslib.Logics.Modal.Tableau.CompletenessLoop` | green, 3.7s |
| `lake build` (full project) | **green, 3325 jobs** |
| `#print axioms modalExpandBranchesD_hintikka` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms modalExpandBranchesGen_hintikka` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms modalExpandBranchesHintikka` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms modalTableau_complete` (K regression) | `[propext, Classical.choice, Quot.sound]` |
| New `sorry` | zero (all `sorry` greps hit pre-existing docstring prose only) |
| New axioms | zero |

**Measured cost** (`git diff --stat`, Cslib only):

```
Cslib/Logics/Modal/Tableau/CompletenessLoop.lean   | 52 +/-   (26 lines changed)
Cslib/Logics/Modal/Tableau/DDriver.lean            | 20 +     (the deliverable)
Cslib/Logics/Modal/Tableau/FrameCompleteness.lean  |  6 +/-   (3 lines changed)
Cslib/Logics/Modal/Tableau/TDriver.lean            |  2 +/-   (1 line)
Cslib/Logics/Modal/Tableau/BDriver.lean            |  2 +/-   (1 line)
Cslib/Logics/Modal/Tableau/TBDriver.lean           |  2 +/-   (1 line)
```

**~32 changed lines + 20 new lines, against a 755-line estimate — a 14x reduction.**

The verified patch is preserved verbatim at:
`specs/601_completeness_loop_specat_hintikka_chain/artifacts/verified-route3.patch`

---

## 2. Why the ~755-Line Estimate Was Wrong

The prior BLOCKER analysis measured each declaration's **body size** and assumed each needed a
full duplicate, because `RuleApplicationSpecCoreAt φ0` is not coercible to
`RuleApplicationSpecCore`. That coercion direction is indeed impossible — but it was never
needed. The correct question is the opposite direction, and the answer is that the chain never
used the extra strength in the first place.

**The load-bearing fact**: every declaration in the chain consumes `outputsSubsetUniverse` at
its **own already-explicit `φ0` parameter** — never at a second, different `φ0`, and never
under a `∀ φ0` it introduces itself. Therefore the universally-quantified
`RuleApplicationSpecCore` hypothesis is strictly stronger than what the proofs use. Narrowing
the hypothesis to `...CoreAt φ0` **weakens** the assumption, so every proof body goes through
character-for-character unchanged.

Field-usage audit (from `grep` of `hs.` / `hcore.` / `spec.` within each declaration's range):

| Declaration | Fields actually used | Uses `outputsSubsetUniverse`? | Mentions `φ0`? |
|---|---|---|---|
| `modalLoopGen_bClosure_core` (970-1019) | `outputsSubsetUniverse` | **yes**, at own `φ0` (line 984) | yes (own param) |
| `modalLoopGen_eBoxOnlyNeg_core` (1020-1078) | `boxPosNotExpanding` | no | **no** |
| `modalLoopGen_eDiamondOnlyPos_core` (1079-1137) | `diaNegNotExpanding` | no | **no** |
| `modalLoopGen_eBoxNegWitness_core` (1138-1211) | `freshLocal`, `boxNegWitness'` | no | **no** |
| `modalLoopGen_eDiamondPosWitness_core` (1212-1284) | `freshLocal`, `diaPosWitness'` | no | **no** |
| `modalStepHintikka_preserves_inv` (1293-1351) | `freshLocal`, `localShapeInvariance`, `branchingLength`, `persistentFresh`, `outputsSubsetUniverse` | yes, at own `φ0` (1347) | yes (own param) |
| `ModalLoopAuxK_stepPreserved` (1383-1409) | `freshLocal`, `rankStep`, `outDegStep`, `knownWorldsStep`, `.toCore` | only via forwarding | yes (own param) |
| `modalExpandBranchesHintikka` (1433-1744) | `boxNegWitness'`, `diaPosWitness'`, `branchingLength`, `persistentFresh`, `outputsSubsetUniverse` | yes, at own `φ0` (1645) | yes (own param) |

**The corroborating structural fact**: the single downstream consumer of the
`outputsSubsetUniverse` payload, `modalExpMeasure_step_lt_gen` (`FmpMeasure.lean:3159-3178`),
already takes it as a **raw, unbundled, `φ0`-fixed hypothesis** whose type is byte-identical to
`RuleApplicationSpecCoreAt.outputsSubsetUniverse`. It was already written in the target shape;
the two call sites (1347, 1645) merely had to drop their explicit `φ0` argument.

Four of the five `_core` twins (`_eBoxOnlyNeg`, `_eDiamondOnlyPos`, `_eBoxNegWitness`,
`_eDiamondPosWitness`) do not mention `φ0` **at all** and were flagged in the BLOCKER as
needing twins for "nominal-typing only". They needed a **one-line signature change each** —
adding an implicit `{φ0 : Proposition Atom}` inferred from the hypothesis. Their call sites did
not change at all (the argument is passed positionally and `φ0` is implicit). That alone
eliminates 269 of the 755 estimated lines.

---

## 3. Reuse Check (CSLib reuse-first, mandatory)

Before recommending anything new, the following existing abstractions were confirmed present
and sufficient. **No new definitions, structures, typeclasses, or notation are recommended.**

| Existing asset | Location | Role in this route |
|---|---|---|
| `RuleApplicationSpecCoreAt φ0 apply` | `GenericDriver.lean:375` | the narrowed hypothesis type |
| `RuleApplicationSpecAt φ0 apply` | `GenericDriver.lean:443` | the narrowed full-spec type |
| `RuleApplicationSpecCore.toAt` | `GenericDriver.lean:496` | bridges every existing Core witness at any `φ0` |
| `RuleApplicationSpec.toAt` | `GenericDriver.lean:514` | bridges every existing Spec witness at any `φ0` |
| `RuleApplicationSpecAt.toCore` | `GenericDriver.lean:489` | `SpecAt` → `CoreAt` projection |
| `modalApplyOneD_specAt` | `DDriver.lean:1243` | D's twelve-field witness (already landed) |
| `modalExpMeasure_step_lt_gen` | `FmpMeasure.lean:3159` | already takes the raw `φ0`-fixed F2 |
| `ModalLoopAuxK` / `_bounds` / `ModalLoopInvGen_iff_hintikka_auxK` | `CompletenessLoop.lean:338, 348, 360` | spec-free; transport to D for free, zero changes |
| `modalExpMeasure_entry_le_fuel_at` | `DDriver.lean:359` | D's fuel bound at the dual-closed seed |

Searched both `Cslib/Foundations/Logic/` and `Cslib/Logics/` per the dual-location namespace
rule; nothing else in the `Cslib.Logic` namespace covers this. Mathlib has no analogue (this is
CSLib-local tableau infrastructure), so no Mathlib instantiation applies.

---

## 4. The Verified Change Set

Apply `artifacts/verified-route3.patch`, or reproduce it from this table.

### 4.1 `CompletenessLoop.lean` — 8 declarations narrowed

The uniform transformation: move the existing `(φ0 : Proposition Atom)` parameter **before** the
spec hypothesis, and swap the hypothesis type to its `...At` sibling.

| # | Declaration | Signature change | Body change |
|---|---|---|---|
| 1 | `modalLoopGen_bClosure_core` (970) | `(apply) (φ0) (hcore : RuleApplicationSpecCoreAt φ0 apply)` | line 984: drop the `φ0` arg from `hcore.outputsSubsetUniverse` |
| 2 | `modalLoopGen_eBoxOnlyNeg_core` (1020) | add `{φ0 : Proposition Atom}`; `hcore : RuleApplicationSpecCoreAt φ0 apply` | none |
| 3 | `modalLoopGen_eDiamondOnlyPos_core` (1079) | same as #2 | none |
| 4 | `modalLoopGen_eBoxNegWitness_core` (1138) | same as #2 | none |
| 5 | `modalLoopGen_eDiamondPosWitness_core` (1212) | same as #2 | none |
| 6 | `modalStepHintikka_preserves_inv` (1293) | `(apply) (φ0) (hs : RuleApplicationSpecCoreAt φ0 apply)` | line 1320 arg reorder; line 1347 drop `φ0` arg |
| 7 | `ModalLoopAuxK_stepPreserved` (1383) | `(apply) (φ0) (spec : RuleApplicationSpecAt φ0 apply)` | line 1394 arg reorder |
| 8 | `modalExpandBranchesHintikka` (1433) | `(apply) (φ0) (hs : RuleApplicationSpecCoreAt φ0 apply)` | line 1641 arg reorder; line 1645 drop `φ0` arg |

**Plus a ninth declaration, not in the original seven** — and this is what makes the D
deliverable a one-liner rather than a bespoke engine entry point:

| # | Declaration | Signature change | Body change |
|---|---|---|---|
| 9 | `modalExpandBranchesGen_hintikka` (1874) | `(apply) (φ0) (spec : RuleApplicationSpecAt φ0 apply) (fuel)` | lines 1890-1891 arg reorder |

### 4.2 Internal call sites in `CompletenessLoop.lean` (3)

- line 1369 `modalStepHintikka_preserves_inv_S5w`: `modalApplyOneS5w_specCore` → `φ0 (modalApplyOneS5w_specCore.toAt φ0)`
- lines 1890-1891: `spec.toCore φ0` → `φ0 spec.toCore`; `ModalLoopAuxK_stepPreserved apply spec φ0` → `apply φ0 spec`
- line 1944 `modalExpandBranches_hintikka`: `modalApplyOne_spec φ0` → `φ0 (modalApplyOne_spec.toAt φ0)`

### 4.3 External call sites (6, one token each)

| File:line | Change |
|---|---|
| `TDriver.lean:805` | `modalApplyOneT_spec φ0` → `φ0 (modalApplyOneT_spec.toAt φ0)` |
| `BDriver.lean:826` | `modalApplyOneB_spec φ0` → `φ0 (modalApplyOneB_spec.toAt φ0)` |
| `TBDriver.lean:894` | `modalApplyOneTB_spec φ0` → `φ0 (modalApplyOneTB_spec.toAt φ0)` |
| `FrameCompleteness.lean:3174` | `modalApplyOneS5w_specCore φ₀` → `φ₀ (modalApplyOneS5w_specCore.toAt φ₀)` |
| `FrameCompleteness.lean:3952` | `modalApplyOneFive_specCore φ₀` → `φ₀ (modalApplyOneFive_specCore.toAt φ₀)` |
| `FrameCompleteness.lean:4825` | `modalApplyOneKb5''_specCore φ₀` → `φ₀ (modalApplyOneKb5''_specCore.toAt φ₀)` |

**No other file in the repository referenced any of the nine declarations.** Verified by
repo-wide `grep`; `LoopChecking.lean`'s two mentions are prose references ("structural port
of...") in docstrings, not call sites.

### 4.4 `DDriver.lean` — the deliverable (20 lines, appended before `end Cslib.Logic.Modal.Tableau`)

```lean
/-! ## D Instantiation of the Generic Top-Loop Hintikka Lemma -/

theorem modalExpandBranchesD_hintikka (φ : Proposition Atom) (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      modalExpMeasure (modalUniverse (modalDualAugment φ)) branches expandedSets ≤ fuel →
      (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
          (ai : Accessibility),
        branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
        ∃ rank, ModalLoopInvGen modalApplyOneD (modalDualAugment φ) bi ei ai rank) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesD branches expandedSets accs fuel = .openBranch bR aR →
        modalHintikkaSetGen modalApplyOneD bR aR :=
  modalExpandBranchesGen_hintikka modalApplyOneD (modalDualAugment φ)
    (modalApplyOneD_specAt φ) fuel
```

This is the **genuine one-liner** `TDriver.lean:805` is, with `φ0 := modalDualAugment φ` and
`modalApplyOneD_specAt φ` in place of a universally-quantified spec. Docstring above is
abbreviated in this report; the implementation should write a full CSLib-style docstring
(see §6, docBlame).

---

## 5. Route Comparison (evaluated against blast radius, as the task directed)

| Dimension | Route 1: additive twins | Route 2: full unbundling | **Route 3: in-place bundled narrowing (verified)** |
|---|---|---|---|
| New lines | ~755 | ~0 net, but ~9 raw hypotheses re-inlined into `modalStepHintikka_preserves_inv` and `modalExpandBranchesHintikka` (each ~60 lines of Pi-type text) | **20** (the D bridge only) |
| Changed lines | 0 | ~150+ | **~32** |
| Declarations touched | 7 new | 7 rewritten | 9 signature-edited |
| Files touched | 2 | 2 | 6 |
| Duplication introduced | 755 lines of mechanical duplicate, permanently divergence-prone | none | **none** |
| Downstream breakage | none (additive) | reorder + unbundle at every call site | 6 one-token external fixes |
| Fixes the root cause | no (leaves two parallel chains) | yes | **yes** (single chain, strictly weaker hypotheses) |
| Empirically verified | no | no | **yes — full build green, axioms clean** |

**Why Route 2 is worse than it looks here**: unbundling is right for a lemma that uses one or
two fields, and is genuinely attractive for the four `φ0`-free `_core` twins. But
`modalStepHintikka_preserves_inv` uses *five* fields directly and forwards the bundle to five
more helpers; `modalExpandBranchesHintikka` uses five and forwards. Unbundling those two means
writing out nine raw Pi-typed hypotheses — re-inlining the whole `RuleApplicationSpecCore`
structure by hand. That is exactly the duplication `RuleApplicationSpecCore` exists to prevent.
Route 3 unbundles nothing and duplicates nothing because `...CoreAt` **is** the correctly-scoped
bundle; the file was simply never re-typed against it.

**Why Route 1 is strictly dominated**: it is 24x the changed-line count of Route 3 and leaves
two structurally identical 755-line chains that must be kept in sync forever. The
`_core`-twin idiom it invokes as precedent was itself introduced (see the docstring at
`CompletenessLoop.lean:965-968`) as an explicitly temporary measure pending exactly this
generalization pass: *"Weakening those five declarations in place to a Core-only signature is
left for a future generalization pass."*

**Recommendation: Route 3.** It is the route `CompletenessLoop.lean:965-968` anticipates, and
it has been executed and machine-checked.

---

## 6. Zero-Debt and Lint Compliance

**Zero-debt**: verified. Full build green, three standard axioms, zero new `sorry`, zero new
axioms, zero vacuous definitions. No `sorry`-deferral pattern is proposed anywhere in this
report.

**Remaining work that the verification pass did NOT cover** — this is the honest residual, and
it is documentation, not proof:

1. **Docstring drift (docBlame-adjacent)**. The nine narrowed declarations' docstrings still say
   `RuleApplicationSpecCore` / `RuleApplicationSpec` where the signature now says `...CoreAt` /
   `...At`. Specifically:
   - `CompletenessLoop.lean:961-968` — the `_core` section header explicitly frames the twins as
     "purely-additive, leaving every existing declaration above untouched" and defers the
     in-place weakening to "a future generalization pass". **That pass is this task**; the
     paragraph must be rewritten to record that it happened.
   - `CompletenessLoop.lean:1286-1292` (`modalStepHintikka_preserves_inv`): "Only needs
     `RuleApplicationSpecCore`" → `RuleApplicationSpecCoreAt φ0`.
   - `CompletenessLoop.lean:1413-1432` (`modalExpandBranchesHintikka`): "Takes only
     `RuleApplicationSpecCore`" → `...CoreAt φ0`.
   - `CompletenessLoop.lean:1373-1382` (`ModalLoopAuxK_stepPreserved`): "generic over any
     `apply` with a full `RuleApplicationSpec`" → `RuleApplicationSpecAt φ0`.
   - `CompletenessLoop.lean:1866-1870` (`modalExpandBranchesGen_hintikka`): the "`spec.toCore`
     weakens `RuleApplicationSpec` to..." sentence describes the old bridging.
   - `GenericDriver.lean:365-369`: "This narrowing is purely additive: `RuleApplicationSpec`/
     `RuleApplicationSpecCore` themselves, and all seven of `RuleApplicationSpec`'s existing
     discharge sites, are untouched." Still true of the *structures* and the *discharge sites*
     (all seven witnesses are unchanged), but the sentence should note that
     `CompletenessLoop.lean`'s consumers are now typed at the `...At` interface.
   - `GenericDriver.lean:141` and `CompletenessLoop.lean:39` module-docstring mentions of
     `modalExpandBranchesGen_hintikka`.
   - `TDriver.lean:779-786`, `BDriver.lean:809-811`, `TBDriver.lean:876-879`: the "genuine
     one-liner ... at `(modalApplyOneT, modalApplyOneT_spec)`" phrasing now needs `.toAt φ0`.

2. **Linters not run**. `lake lint`, `lake exe lint-style`, `lake exe checkInitImports`,
   `lake shake` were not executed during this research pass (only `lake build`, which does run
   the syntax linters and was clean on all six touched files). The full CI order in
   `.claude/rules/cslib.md` should be run at implementation.
   - Watch `lint-style` 100-char limit: the new `DDriver.lean` one-liner and the
     `FrameCompleteness.lean` `.toAt φ₀` insertions lengthen lines. The verified patch already
     wraps them; keep the wrapping.
   - `unusedSectionVars` is a non-issue (no section variables added).
   - The new `{φ0 : Proposition Atom}` implicits on four `private lemma`s are used (in the
     hypothesis type), so no unused-variable warning fires — confirmed by the clean build.

3. **`lake exe mk_all --module`** is not needed: no new file is added.

---

## 7. Next Blocker Beyond This Task (for the successor plan, not this one)

`modalExpandBranchesD_hintikka` unblocks the top loop, but `modalTableauD_complete` will hit a
distinct, real gap that this route does **not** address:

`modalLoopInvGen_initial apply φ0` (`CompletenessLoop.lean:2151`) proves the initial invariant
for branch `[F(φ0)@0]` at seed `φ0` — branch formula and seed are the *same* `φ0`. D needs
`ModalLoopInvGen modalApplyOneD (modalDualAugment φ) [F(φ)@0] [] Accessibility.empty rank`:
branch formula `φ`, seed `modalDualAugment φ`. The two differ.

What this needs (all appears reachable, none appears to need new axioms):
- `⟨.neg, φ, 0⟩ ∈ modalUniverse (modalDualAugment φ)` — should follow from
  `modalSubfmls_self_mem φ` transported by `mem_modalSubfmls_foldrAnd_of_base`
  (`DDriver.lean:106`), which already exists and is exactly this transport.
- a `phiBound` re-derivation at the larger seed, paralleling `modalLoopInvGen_initial`'s
  `geomCap` computation but with `(modalSubfmls (modalDualAugment φ)).length` and
  `modalDepth (modalDualAugment φ)`.
- the fuel bridge is already landed: `modalExpMeasure_entry_le_fuel_at` (`DDriver.lean:359`).

Estimated as a `modalLoopInvGen_initial_at`-style sibling in `DDriver.lean`, ~60-80 lines. It is
**not** in this task's stated scope ("land `modalExpandBranchesD_hintikka` in `DDriver.lean`")
and should not be absorbed silently; flag it for the successor task alongside the already-declared
Decidable-instance arm (`FrameSoundness.lean` / `FrameCompleteness.lean`).

---

## 8. Tactic Survey

Not applicable in the usual sense: **no proof search was required**. Every change is
type-level — a hypothesis-type narrowing plus argument reordering. All eight existing proof
bodies were reused character-for-character apart from dropping one explicit `φ0` argument at
three sites and reordering positional arguments at four sites. No new tactic block was written;
the D deliverable is a term-mode one-liner. `lean_multi_attempt`/`lean_state_search`/
`lean_hammer_premise` were therefore not needed, and the stronger evidence — a green full build
with clean axioms — was obtained directly instead.

## 9. Literature

No literature source is referenced by this task; the extraction protocol does not apply. The
governing "source" is `specs/598_serial_rule_spec_decision_tableau/plans/01_serial-d-driver-route-e2.md`
phase 9 (BLOCKER + Reasoned Exclusions), whose per-declaration line-count table this report
supersedes with a measured, machine-checked alternative.

---

## 10. Implementation Sequencing (suggested; the planner owns the final phase structure)

1. **Phase A** — narrow the eight `CompletenessLoop.lean` declarations + fix the three internal
   call sites. Gate: `lake build Cslib.Logics.Modal.Tableau.CompletenessLoop` green.
2. **Phase B** — narrow `modalExpandBranchesGen_hintikka` (#9) + fix the six external call sites
   in `TDriver`/`BDriver`/`TBDriver`/`FrameCompleteness`. Gate: full `lake build` green.
3. **Phase C** — land `modalExpandBranchesD_hintikka` in `DDriver.lean` with a full docstring.
   Gate: full `lake build` green; `#print axioms` = three standard axioms.
4. **Phase D** — docstring reconciliation across the nine narrowed declarations plus the four
   module docstrings listed in §6.1. Gate: `lake lint`, `lake exe lint-style`,
   `lake exe checkInitImports`, `lake shake` clean.

Phases A and B could be merged (the verification pass did them together in one edit), but
splitting gives a green checkpoint before the cross-file fan-out.
