# Adversarial Audit: The K-Aux `AuxStepPreserved` Unprovability Claim

**Task**: 515 (`s5_universal_rule_termination_unblock_504`)
**Dispatch type**: Divergence audit / adversarial verification (research, not implementation)
**Session**: `sess_1784171237_6d3e73`
**Focus**: `divergence audit K-Aux AuxStepPreserved unprovability claim`
**Reference grounding tier**: Tier 3 (implementation-backed — ground truth is the landed Lean,
not literature; the `<literature-briefing>` corpus was correctly not consulted per dispatch
instruction)

---

## Verdict Summary

| # | Question | Verdict |
|---|----------|---------|
| 1 | Does the counterexample exist and work? | **YES — verified in Lean, and it is stronger than claimed** |
| 2 | Is `outDegEq` load-bearing / intrinsic? | **Intrinsic. Not fixable by restating K's Aux at the current `Aux` arity** |
| 3 | Is frozen-`e` the real culprit? | **Partly. The claim is true but Phase 11's stated MECHANISM is wrong** |
| 4 | Was Phase 11 right to mark `[COMPLETED]`? | **NO. Should be `[PARTIAL]`. Phase 10 should be reopened** |
| 5 | Phase 12 architecture | **`Aux` must gain an `e` slot. Phase 10's `ModalLoopAuxK` must be revised — verified fix below** |

**The claim survives refutation.** I attempted to prove `AuxStepPreserved modalApplyOne
(ModalLoopAuxK φ0 e)` and instead proved its **negation**. Phase 11 was not rationalizing a
failure; it under-claimed. But its *diagnosis* is wrong in a way that would misdirect Phase 12,
and its *status marker* and *deferral decision* are both wrong.

---

## 1. The Counterexample: Verified, Not Prose

Phase 11 asserted the counterexample abstractly. I reconstructed it concretely and machine-checked
it. This is not "I could not prove it" — `¬ AuxStepPreserved` is a **theorem**.

**Instance** (`Atom := Nat`):

| Component | Value |
|-----------|-------|
| `φ0` | `.box (.atom 0)` (i.e. `□p`) |
| `b` | `[⟨.neg, .box (.atom 0), 0⟩]` (i.e. `F(□p)@0`) |
| `e` | `[]` (the frozen expansion list) |
| `acc` | `Accessibility.empty` |
| minting step | `boxNeg` on `F(□p)@0` → `.linear [F(p)@1]`, `newAcc = ∅.addEdge 0 1` |

The step, by `rfl` (`modalStepBranchGen`'s `.linear` case emits `[newForms ++ b]`):

```lean
theorem hstep : modalStepBranchGen (Atom := Nat) modalApplyOne bb ee acc0
    = some ([bb'], [ee'], acc1) := by rfl
```
where `bb' = [F(p)@1, F(□p)@0]`, `ee' = [F(□p)@0]`, `acc1 = ⟨[(0,1)]⟩`.

**The hypothesis side is satisfiable — this is not a vacuous counterexample.** I discharged the
full `ModalPotentialInv` bundle and the `phiBound` conjunct concretely:

```lean
theorem hpot : ModalPotentialInv φ0 bb ee acc0 (fun _ => 1)   -- all 8 fields, sorry-free
theorem haux : ModalLoopAuxK φ0 ee bb acc0 := ⟨fun _ => 1, hpot, by decide⟩
```

Verified scalars (`#eval`): `Sf = (modalSubfmls φ0).length = 2`; `modalDepth φ0 = 1`;
`modalMaxWorld bb = 0`; `modalPotential 2 bb ∅ (fun _ => 1) = 2`; `geomCap 2 1 = 3`. So `phiBound`
reads `0 + 2 + 1 ≤ 3` — true, and **tight**.

**The refutation**:

```lean
theorem auxK_not_stepPreserved :
    ¬ AuxStepPreserved (Atom := Nat) modalApplyOne (ModalLoopAuxK φ0 ee) := by
  intro h
  obtain ⟨rank', hpot', -⟩ :=
    h bb ee acc0 [bb'] [ee'] acc1 hstep hfresh hknown haux bb' (by simp)
  have h0 := hpot'.outDegEq 0
  simp [outDeg, Accessibility.successorsOf] at h0
```

`#print axioms` → `[propext, Quot.sound]`. **No `sorryAx`.**

The contradiction is arithmetic and unavoidable: `outDegEq` at world `0` in the post-state demands
`outDeg acc1 0 = (ee.filter …).length`, i.e. `1 = 0` (verified: `#eval outDeg acc0 0 = 0`,
`#eval outDeg (acc0.addEdge 0 1) 0 = 1`).

**The `∃ rank` cannot repair it.** `ModalPotentialInv.outDegEq` is
`∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length` —
it does not mention `rank` at all. No choice of witness can affect it.

---

## 2. Is `outDegEq` Load-Bearing? — Intrinsic, Not An Artifact

Phase 10's handoff is correct that `outDegEq`/`rankBound`/`rankEdge` are not promoted into
`ModalLoopInvHintikka` (verified: the structure's 11 fields are `bClosure`, `eClosure`, `eNodup`,
`accFresh`, `accKnown`, `aux`, `hintikkaInv`, `eBoxOnlyNeg`, `eBoxNegWitness`, `eDiamondOnlyPos`,
`eDiamondPosWitness`) and live only inside `ModalLoopAuxK`. But that is exactly why the breakage
is **intrinsic**:

- `ModalLoopAuxK` must carry `outDegEq`, because `outDegEq` is a hypothesis of
  `modalStepBranch_potential_step_gen`, which is the only route to re-establishing `phiBound`.
  Drop `outDegEq` from K's `Aux` and `AuxBounds` becomes underivable. It cannot be weakened away.
- `outDegEq` is a **joint** predicate on `(e, acc)`. Any `Aux` of type
  `List SignedFormula → Accessibility → Prop` can mention `acc` but must **close over** `e`.
- A minting step advances *both* coordinates in lockstep: `acc ↦ acc.addEdge l w'` and
  `e ↦ e ++ [sf]`. Freezing one while the other moves breaks the invariant by construction.

So this is **not** fixable by restating `ModalLoopAuxK` at the current `Aux` arity. The arity is
the defect.

---

## 3. Is Frozen-`e` The Culprit? — Claim TRUE, Diagnosis WRONG

**This is the most important finding of the audit, and it contradicts Phase 11's own explanation.**

Phase 11's plan text states the mechanism as:

> "`AuxStepPreserved`'s own step hypothesis is universally quantified over an independent,
> per-call `e` … **whenever the frozen `e` and the step's actual `e` diverge**, the post-state
> conjunct is false"

**That mechanism is false.** In my verified counterexample the frozen `e` and the step's actual `e`
**coincide** — both are `[]`. I instantiate `h bb ee acc0 …` against `ModalLoopAuxK φ0 ee`: same
`ee`. There is no divergence between the frozen `e` and the step's input `e`, and the statement is
*still* refutable.

The real mechanism is one step further along:

> `Aux` has no `e` slot at all, so the **post-state** obligation is re-asserted at the *pre-state*
> `e`. The step's input `e` is irrelevant; what breaks is that the true post-state expanded set is
> `e' = e ++ [sf]`, and `Aux b' newAcc` has no way to say `e'`.

Why this distinction is load-bearing for Phase 12: a "fix" that constrains the step's `e` to match
the frozen `e` — e.g. adding `e = e₀` as a hypothesis to `AuxStepPreserved`, which is the natural
reading of Phase 11's diagnosis — **would change nothing**. My counterexample already satisfies
`e = e₀`. Phase 12 must thread `e` as an **argument to `Aux`**, and must pair the conclusion over
`newBs.zip newExps`. Nothing less works.

Phase 11's `recommended_next_dispatch` ("threading `e` explicitly rather than freezing it") is the
right instinct and is **correct** — but it is not what the phase's own written diagnosis implies.

---

## 4. Was Phase 11 Right To Mark `[COMPLETED]`? — No

**Direct verdict: no. Phase 11 should be `[PARTIAL]`, and Phase 10 should be reopened.**

The plan's Phase 11 verification bar is explicit: *"the port closes sorry-free at **both** `Aux`
instantiations."* Phase 11 met one of two. A phase that meets half its stated bar is not
`[COMPLETED]`; that is what `[PARTIAL]` is for. The self-assessment "**Finding** (documented, **not
a blocker for this phase**)" is where the marker went wrong.

Three specific corrections:

1. **The deferral is not safe.** Phase 11 characterizes the K gap as "architecture work for
   Phase 12." But Phase 12b's **non-negotiable REGRESSION GATE** re-derives
   `modalExpandBranchesGen_hintikka` from the parametric lift at `Aux := (∃ rank, ModalLoopInvGen …)`,
   and `TDriver.lean:911` / `BDriver.lean:871` consume it by name. That gate needs a *closed*
   K-side `AuxStepPreserved` witness — the exact term I proved does not exist. **Phase 12 as
   currently written would hit its own KILL (R3)**, having spent a ~310-line double induction
   first. This defect must be fixed *before* Phase 12, not inside it.

2. **The defect is Phase 10's, and Phase 11 was right about that much.**
   `modalStepHintikka_preserves_inv` is genuinely generic and sorry-free for any `Aux` that
   *does* satisfy the contract. The bad declaration is Phase 10's `ModalLoopAuxK` — more precisely
   Phase 10's `AuxStepPreserved`/`AuxBounds`/`ModalLoopInvHintikka` **arity**. Phase 10's own
   verification bar was *"both `Aux` instantiations elaborate"* — and `ModalLoopAuxK` does
   elaborate. That bar was too weak: elaboration is not satisfiability. Phase 10's
   `ModalLoopInvGen_iff_hintikka_auxK` looks like it closes this gap ("a full bridge, not merely a
   type-check") but it does not: it is stated at a *single fixed* `(b, e, acc)` and so never
   exercises the step, which is precisely where the freeze bites.

3. **"K/T/B pay nothing" is currently false.** As landed, K/T/B pay *everything* — their half of
   the invariant cannot be carried across a step at all. The guarantee is recoverable (see §5),
   but it is not true of the code on `main` today.

---

## 5. Recommended Phase 12 Architecture — Verified, Not Proposed

I did not stop at a recommendation; I **proved the fix works**, both halves, sorry-free.

### The shape

The pre-existing, landed `modalStepGen_preserves_invariant` — *the port's own source of truth* —
already has the correct shape, and Phase 10 dropped it:

```lean
∃ rank', (∀ p ∈ newBs.zip newExps, ModalLoopInvGen apply φ0 p.1 p.2 newAcc rank') ∧ measure-drop
```

It pairs each branch `p.1` with **its own** new expanded set `p.2`, and `ModalLoopInvGen` carries
`e` (via `potentialInv : ModalPotentialInv φ0 b e acc rank`). The regression is precisely that
`Aux : b → acc → Prop` cannot express `p.2`. The fix restores what the source of truth always had.

```lean
-- `Aux` gains an `e` slot; the conclusion pairs each branch with ITS OWN new `e`.
def AuxStepPreserved (apply : RuleApply Atom)
    (Aux : List (SignedFormula (Proposition Atom) WorldIndex) →
           List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → Prop) : Prop :=
  ∀ (b e : …) (acc : Accessibility) (newBs newExps : …) (newAcc : Accessibility),
    modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc) →
    accFreshInv b acc → accTargetsKnown b acc → Aux b e acc →
    ∀ p ∈ newBs.zip newExps, Aux p.1 p.2 newAcc      -- was: ∀ b' ∈ newBs, Aux b' newAcc

def AuxBounds (φ0 : Proposition Atom) (Aux : …) : Prop :=
  ∀ b e acc, Aux b e acc → modalMaxWorld b < modalWorldBound φ0

structure ModalLoopInvHintikka … where
  …
  aux : Aux b e acc                                  -- was: Aux b acc

def ModalLoopAuxK (φ0 : Proposition Atom) (b e : …) (acc : Accessibility) : Prop :=
  ∃ rank, ModalPotentialInv φ0 b e acc rank ∧ (phiBound-statement)   -- `e` threaded, not frozen

@[nolint unusedArguments]
def ModalLoopAuxS5w (φ₀ : Proposition Atom) (b _e : …) (_acc : Accessibility) : Prop :=
  S5wTagInv φ₀ b ∧ S5wWorldInv φ₀ b                  -- now two unused args
```

### Cost to S5w: one token

```lean
theorem AuxS5w_stepPreserved (φ₀ : Proposition Atom) :
    AuxStepPreserved modalApplyOneS5w (ModalLoopAuxS5w φ₀) := by
  rintro b e acc newBs newExps newAcc hstep _hFresh hKnown ⟨hT, hW⟩ p hp
  exact modalStepBranchS5w_preserves_worldInv hT hW hKnown hstep p.1 (List.of_mem_zip hp).1
```

`(List.of_mem_zip hp).1` replaces `hb'`. Nothing else changes. `List.of_mem_zip` is already used by
`modalStepHintikka_preserves_inv` itself, so it is a proven-available idiom in this file. S5w keeps
`@[nolint unusedArguments]` (now covering `_e` as well as `_acc`) and is undisturbed. **Compiles.**

### Cost to K/T/B: the guarantee is restored — and generically

```lean
theorem AuxK_stepPreserved (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (φ0 : Proposition Atom) :
    AuxStepPreserved apply (ModalLoopAuxK φ0) := by
  rintro b e acc newBs newExps newAcc hstep hFresh hKnown ⟨rank, hpot, hphi⟩ p hp
  obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
  obtain ⟨rank', _hagree, hrb', hre', hpotid⟩ :=
    modalStepBranch_potential_step_gen apply spec.freshLocal spec.rankStep spec.outDegStep
      spec.knownWorldsStep φ0 b e acc newBs newExps newAcc rank hstep hpot
  have hWb : modalMaxWorld b < modalWorldBound φ0 := ModalLoopAuxK_bounds φ0 e b acc ⟨rank, hpot, hphi⟩
  refine ⟨rank', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact modalLoopGen_bClosure_core … p.1 hp1              -- the in-file private helper
  · exact modalStepBranch_preserves_expandedNodup_gen … hpot.eNodup p.2 hp2
  · exact modalStepBranch_eClosure_gen … hpot.bClosure hpot.eClosure p.2 hp2
  · exact modalStepBranch_preserves_accFreshInv_gen apply spec.freshLocal … hFresh p.1 hp1
  · exact modalStepBranch_preserves_accTargetsKnown_gen apply spec.freshLocal … hKnown p.1 hp1
  -- THE CRUX: outDegEq now lands at p.2 (the branch's OWN new e), not at a frozen e.
  · exact modalStepBranch_preserves_outDegEq_gen apply spec.outDegStep … hpot.outDegEq p.2 hp2
  · exact hrb' p.1 hp1
  · exact hre'
  · rw [hpotid p.1 hp1]; exact hphi
```

**This compiles, sorry-free**, `#print axioms` → `[propext, Classical.choice, Quot.sound]`.

Two results here are better than expected and should shape Phase 12's plan:

1. **K's step preservation is provable generically**, over any `apply` with a full
   `RuleApplicationSpec` — not per-logic. K, T, and B all get it from one theorem. This is the
   "K/T/B pay nothing" guarantee, actually delivered.
2. **The pieces already exist.** Every field is discharged by a *landed, public* lemma. The crux
   line is `modalStepBranch_preserves_outDegEq_gen`, whose conclusion is already exactly
   `∀ e' ∈ newExps, ∀ w, outDeg newAcc w = (e'.filter …).length` — quantified over the **new**
   expanded sets. Phase 10 built an `Aux` interface that could not consume the very lemma written
   to serve it.

Note the `RuleApplicationSpecCore` / `RuleApplicationSpec` split (Phase 9) is vindicated and
undisturbed: `modalStepHintikka_preserves_inv` still needs only `Core` (Aux facts come from the
caller), while `AuxK_stepPreserved` — a *caller* — legitimately uses the full spec's
`rankStep`/`outDegStep`/`knownWorldsStep`. This is the Phase 9/10 design intent working as
designed.

### Sequencing recommendation

1. Mark Phase 11 `[PARTIAL]`; reopen Phase 10.
2. Insert a **Phase 11.5** (small, ~60 lines, mechanical): re-arity
   `AuxStepPreserved`/`AuxBounds`/`ModalLoopInvHintikka.aux`/`ModalLoopAuxK`/`ModalLoopAuxS5w`;
   re-land `ModalLoopAuxS5w_stepPreserved` (one token), `ModalLoopAuxS5w_bounds`,
   `ModalLoopAuxK_bounds`, `ModalLoopInvGen_iff_hintikka_auxK` (all mechanical);
   land `ModalLoopAuxK_stepPreserved` (new, ~15 lines, proof above).
   `modalStepHintikka_preserves_inv`'s body needs only `hAuxAll`'s call site adjusted to pass the
   pair — its `refine` already destructures `p` via `List.of_mem_zip`.
   **Bar**: a closed `AuxStepPreserved` witness at **both** instantiations. That is Phase 11's
   original bar, and it is now achievable.
3. Only then run Phase 12. Its KILL (R3) gate becomes a real test of the *lift*, rather than a
   re-discovery of this arity defect after a 310-line induction.

**Strengthen Phase 10's bar**: "both `Aux` instantiations elaborate" must become "both `Aux`
instantiations have closed `AuxStepPreserved` **and** `AuxBounds` witnesses." Elaboration is not
satisfiability — that gap is the entire root cause here, and
`ModalLoopInvGen_iff_hintikka_auxK` gave false assurance precisely because it is step-free.

---

## Adversarial Self-Verification

My standing incentive in this dispatch was to find Phase 11 rationalizing a failure. It was not.
I flipped my own posture and attacked the *opposite* conclusion: I tried to prove the fix
impossible, and instead proved it works. Both directions are machine-checked below.

| Claim | Source/Counterexample |
|-------|----------------------|
| `AuxStepPreserved modalApplyOne (ModalLoopAuxK φ0 [])` is FALSE | `auxK_not_stepPreserved`, compiles; `#print axioms` → `[propext, Quot.sound]`, no `sorryAx`. Scratch: `<scratchpad>/refutation.lean` |
| The counterexample is not vacuous (hypothesis satisfiable) | `hpot : ModalPotentialInv φ0 bb ee acc0 (fun _ => 1)` and `haux : ModalLoopAuxK φ0 ee bb acc0` both compile, sorry-free |
| `phiBound` holds for the instance | `#eval`: `0 + 2 + 1 ≤ geomCap 2 1 = 3`. Tight but true |
| The mint step fires with the stated output | `hstep : … = some ([bb'], [ee'], acc1) := by rfl` |
| A mint increments `outDeg` | `#eval outDeg acc0 0 = 0`; `#eval outDeg (acc0.addEdge 0 1) 0 = 1`; and `houtdeg_l` in `modalStepBranch_potential_step_gen` (`FmpMeasure.lean`) |
| `∃ rank` cannot repair `outDegEq` | `ModalPotentialInv.outDegEq` (`FmpMeasure.lean`) does not mention `rank` — read directly |
| Phase 11's stated mechanism ("frozen `e` and step's `e` **diverge**") is wrong | **Counterexample to the counterexample's explanation**: my refutation sets frozen `e` = step `e` = `[]`. No divergence; still false. Diagnosis revised in §3 |
| The `e`-threading fix discharges S5w | `AuxS5w'_stepPreserved` compiles; axioms `[propext, Classical.choice, Quot.sound]`. Scratch: `<scratchpad>/fix-probe.lean` |
| The `e`-threading fix discharges K, generically | `AuxK'_stepPreserved` compiles for arbitrary `(apply, spec : RuleApplicationSpec apply)`; same axioms, no `sorryAx` |
| `modalStepBranch_preserves_outDegEq_gen` already targets the NEW `e'` | Read: conclusion is `∀ e' ∈ newExps, ∀ w, outDeg newAcc w = (e'.filter …).length` (`FmpMeasure.lean`) |
| The source-of-truth lemma already pairs `newBs.zip newExps` | Read `modalStepGen_preserves_invariant` (`CompletenessLoop.lean`): `∀ p ∈ newBs.zip newExps, ModalLoopInvGen apply φ0 p.1 p.2 newAcc rank'` |
| `List.of_mem_zip` is available | Already used inside `modalStepHintikka_preserves_inv`'s own body |
| Phase 12b's gate would fail as written | Plan §Phase 12 (12b) re-derives at `Aux := (∃ rank, …)` and requires a closed K-side witness — refuted above. Read plan lines for Phase 12 + `TDriver.lean:911`/`BDriver.lean:871` consumption note |
| `bClosure` helper access | `modalLoopGen_bClosure_core` is `private` (`CompletenessLoop.lean:914`), so the probe passes it as a hypothesis. **Confidence: high but not closed** — in-file it is discharged exactly as Phase 11's port already does at the same position; the probe does not re-verify that one line |

### Claims I challenged and revised

- **Initially accepted, then revised**: Phase 11's framing that frozen-vs-step `e` *divergence* is
  the culprit. My own counterexample refutes that framing. Revised to: `Aux` lacks an `e` slot, so
  the post-state cannot be expressed. This changes what Phase 12 must do.
- **Initially assumed, then refuted**: that "unprovable" was an overstatement. It was an
  *understatement* — the statement is refutable, not merely unprovable.
- **Initially assumed, then refuted**: that the fix would cost K/T/B something. It costs one token
  at S5w and yields a *generic* K/T/B theorem.

### Residual uncertainty

- The `modalLoopGen_bClosure_core` line in `AuxK_stepPreserved` is hypothesis-supplied in my probe
  (private-access limitation of an out-of-file scratch), not re-verified. Every *other* field is
  closed against landed public lemmas. Low risk: Phase 11's port already discharges this exact
  obligation at this exact position.
- Phase 11.5's ~60-line estimate is my own sizing, extrapolated from the probe; it is not measured.
- I did not re-verify T/B driver compilation under the re-arity. The `AuxK_stepPreserved` theorem
  is generic over `RuleApplicationSpec`, and T/B have those specs, so the risk is low — but
  Phase 12b's regression gate remains the real test, and should stay non-negotiable.

### Contract compliance

- **H2 (anti-analysis, lean4 bar)**: every load-bearing claim is backed by compiled Lean or read
  code. No "the file likely has this." First probe fired early; the dispatch produced two verified
  theorems, not a prose verdict.
- **H3 (reference grounding, Tier 3)**: all structural claims cite declaration names and file
  paths. Line numbers deliberately avoided except for the two `private` markers and the plan's
  own `TDriver.lean:911`/`BDriver.lean:871` citations (quoted from the plan, not independently
  re-verified — stale line citations are a confirmed hazard in this task).
- **Literature**: correctly not consulted. Ground truth here is the landed Lean; the briefing's
  Blackburn/de Rijke/Venema entry has no bearing on an arity defect in a Lean interface. No BibKey
  verification was applicable (Tier 3, no literature claims made).
- **No `Cslib/` files were edited.** Probes lived in repo-root scratch files during the run and
  were moved to the session scratchpad; `git status` confirms `Cslib/` is untouched.

---

## Scratch Artifacts

Both probes are preserved and re-runnable via `lake env lean <file>` from the repo root:

- `<scratchpad>/refutation.lean` — the counterexample and `auxK_not_stepPreserved`
- `<scratchpad>/fix-probe.lean` — the `e`-threaded shapes and both step-preservation proofs

(`<scratchpad>` =
`/tmp/claude-1000/-home-benjamin-Projects-cslib/4c88f031-10c1-4c44-b03e-16ae649d963d/scratchpad`;
session-scoped and not durable — re-land these as in-file theorems during Phase 11.5 if they are
wanted as regression tests.)
