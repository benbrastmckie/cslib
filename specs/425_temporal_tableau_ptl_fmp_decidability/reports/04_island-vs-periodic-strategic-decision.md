# Research Report 04 — Island vs. Periodic: Strategic Decision (HARD mode)

- **Task**: 425 — temporal_tableau_ptl_fmp_decidability
- **Date**: 2026-07-24
- **Type**: cslib, RESEARCH ONLY (no `.lean` file under `Cslib/` was edited)
- **Mode**: `--hard` (H2 anti-analysis, H3 reference grounding, H4 adversarial self-verification)
- **Reference grounding tier**: Tier 1 (literature-backed) + Tier 3 (implementation-backed).
  All BibKeys below verified present in `references.bib`.
- **Prior artifact consumed**: `reports/03_blocker-reassessment-remaining-obligations.md`,
  `plans/04_completeness-front-rescope.md`
- **Method note**: every claim below is grounded either in a `file:line` citation from source read
  this dispatch, or in an **executed** `lake env lean` evaluation of the real tableau. The
  executed evaluations are reproduced verbatim.

---

## VERDICT (answer to the strategic question)

**The question as posed — "island or periodic?" — is answered `NEITHER, AND IT IS NOT THE
BINDING CONSTRAINT.`**

Three findings, in decreasing order of consequence:

1. **`openBranch_branchSat` is FALSE as currently stated — not merely unproven.** The temporal
   tableau returns `.openBranch` on branches that are *provably unsatisfiable* in the
   discrete-serial frame class that `branchSat` quantifies over. This is a defect in the
   **calculus** (`Rules.lean`), upstream of every model-construction question. No choice of
   countermodel — island, periodic, bi-lasso, or otherwise — can prove a false theorem. Verified
   by execution: `temporalTableau (𝐅⊤)` returns `OPEN` on the single-formula branch `[F(𝐅⊤)@0]`,
   yet `branchSat [F(𝐅⊤)@0] ord` is refutable in two lines.

2. **Conditional on the calculus being fixed, the island model is still insufficient — but for
   the *opposite* polarity from the one the delegation hypothesised.** The failure mode is not
   "an eventuality unfulfilled inside the island". It is **positive universals** (`𝐆`/`𝐇`): a
   finite branch cannot make `T(𝐆p)@t` true over a `NoMaxOrder` domain, because the island reads
   `false` at every unpopulated instant. A *total* extension of branch content to all of `ℤ` is
   mandatory. Periodicity is the standard such extension — so the periodic machinery **stays on
   the critical path**, but its justification changes completely.

3. **P1 (fuel-sufficiency) is not merely hard — the current `temporalFuel` constant is
   *quadratic* while the tableau's own step count is *exponential*.** Measured: minimal
   sufficient fuel on a tautology family grows as `1.5·2^k − 2`; `temporalFuel` grows as
   `Θ(k²)`. This is a stronger negative result than task 317's `2^Θ(c²)` vs `2^Θ(c)` gap. P1 as
   stated is **false at the current constant**, not open.

**Consequence for planning:** plan-04's Phases 4c/4d/5/6/7 are all downstream of a calculus that
must first be repaired. The correct next move is a **calculus-correctness front** (new phases
C1/C2 below), not more model construction.

---

## Source-to-Implementation Mapping (H3, Tier 1)

| Source claim | BibKey (verified in `references.bib`) | Lean target | Translation notes / status |
|---|---|---|---|
| Tense-logic tableau needs an explicit **seriality** step: every time point gets a successor and a predecessor before the branch counts as saturated | `Reynolds1994` (`references.bib:749`) | *not implemented* — `temporalApplyPos` `asAllFuture?` arm (`Rules.lean:227-234`) returns `.notApplicable` when `ord.futureOf t = []` | **This is defect C1.** The rule propagates only to *existing* successors; nothing ever creates the first one. |
| PTL FMP: an open saturated tableau yields an **ultimately-periodic (lasso)** model; the loop is closed by a repeated state | `HodkinsonReynolds2006` (`references.bib:760`) ch. 11 §5.8 | `extractModelℤPeriodic` (`Completeness.lean:278`) + `extractModelℤPeriodicPast` (`Completeness.lean:344`) | Two **independent** models; no composed bi-directional model exists (verified: only 4 `extractModel*` definitions, `Completeness.lean:167,209,278,344`). |
| Lasso construction requires the loop window to be **fully populated** so folding lands on real content | `HodkinsonReynolds2006` ch. 11 §5.8; `VardiWolper1986` (`references.bib:818`) | *not stated anywhere* | `periodicReduce` (`Completeness.lean:258`) is the identity for `z ≤ instNew`; unpopulated instants ≤ `instNew` still read `false`. New obligation. |
| Discreteness axiom `G'⊥ ∧ H'⊥` separates `validDiscrete` from `valid` | `Burgess1982I` (`references.bib:668`) §1.5, §2 | `validDiscrete` (`Validity.lean:96-101`) | Correctly reflected; `branchSat`'s frame class matches (`Soundness.lean:95-106`). |
| Propositional Hintikka truth lemma pattern | `Smullyan1968` (`references.bib:218`) | `temporalTruthLemma_propositional` (`Completeness.lean:1189`) | **Landed, but over `extractModel` (the `Nat`-keyed island), not `extractModelℤ`.** Re-proof over the final ℤ-model is an unrecorded obligation. |

---

## Q1 — What does the landed `extractModelℤ` construct, and what does it prove/require?

`Completeness.lean:209-211`:

```lean
def extractModelℤ (b : TBranch Atom) (ord : TimeOrdering) : TemporalModel ℤ Atom where
  valuation z p := b.any fun sf =>
    sf.sign == .pos && ord.instant sf.label == z && sf.formula == .atom p
```

- **Domain**: `ℤ`. **Keying**: `ord.instant : Nat → ℤ` (`TimeOrdering.lean:64`), incremented by
  `addFuture` and decremented by `addPast` (`TimeOrdering.lean:80-91`).
- **Valuation**: `true` at instant `z` for atom `p` iff *some* branch label with
  `ord.instant label = z` carries `T(atom p)`. Every instant with no label mapped to it reads
  **`false` for every atom**. This is exactly what "island" means, and it is the crux of Q2.
- **Proved about it**: `extractModelℤ_atom_sat_iff` (`:216`), `extractModelℤ_atomPos_sat`
  (`:225`), `extractModelℤ_bot_false` (`:234`), `extractModelℤ_atom_neg_notSat` (`:511`).
- **Requires**: the negative-atom lemma needs `ord.instant` **injective on branch labels carrying
  `atom p`** (`Completeness.lean:505`) — because `addFuture` sets `instant tNew = instant t + 1`
  for *every* successor of `t`, so two sibling times collide on one instant and the `b.any`
  disjunction over-approximates.
- **Not proved about it**: nothing for `imp`, `untl`, `snce`, `allFuture`, `allPast`. The only
  landed truth lemma (`temporalTruthLemma_propositional`, `Completeness.lean:1189-1197`) is
  stated over **`extractModel` (the `Nat`-keyed model, `Completeness.lean:167`)**, not
  `extractModelℤ`. Phase 7 will need it re-proved over whatever the final ℤ-model is; plan-04
  does not budget for this.

---

## Q2 — Does an island model suffice? (THE CRUX)

### Executed refutation of `openBranch_branchSat` itself

Before the island-vs-periodic question can be asked, the theorem it serves must be true. It is
not. Run this dispatch against the real source (`lake env lean`, unmodified `Cslib/`):

```
temporalTableau (𝐅⊤)                  = OPEN |b|=1 times=[] cons=[]
temporalTableau (¬𝐆⊥)                 = OPEN |b|=2 times=[] cons=[]
temporalTableau (𝐆p → 𝐅p)             = OPEN |b|=3 times=[] cons=[]
temporalTableau (𝐅𝐅𝐅⊤)                = OPEN |b|=1 times=[] cons=[]
temporalTableau (𝐏⊤)                  = OPEN |b|=1 times=[] cons=[]
temporalTableau (p → p)               = CLOSED          (control: correct)
temporalTableau (p)                   = OPEN            (control: correct)
```

**Every one of the five `OPEN` results above is a formula that is `validDiscrete`.** Take the
first. `temporalTableau φ` seeds the branch `[⟨.neg, φ, 0⟩]` with `TimeOrdering.empty`
(`Saturation.lean:534-538`), and `processNext` returns `.openBranch b ord` exactly when
`isTemporalClosed b ord tracker = false` and `temporalStepBranch b e ord tracker = none`
(`Saturation.lean:288-296`). So the returned branch is `b = [F(𝐅⊤)@0]`, `ord = empty`.

Now unfold `branchSat b ord` (`Soundness.lean:95-106`). Order-preservation is vacuous
(`ord.constraints = []`). The single obligation is

> `∃ D` discrete-serial, `M`, `f`, with `¬ Satisfies M (f 0) (𝐅⊤)`.

But `𝐅⊤ = untl ⊤ ⊤` (`Formula.lean:154`), and `Satisfies M t (untl ψ φ) ↔ ∃ s, t < s ∧ …`
(`Satisfies.lean:70-72`). `NoMaxOrder D` — required by `branchSat`'s own frame class
(`Soundness.lean:99`) — gives `∃ s > f 0`, and `Satisfies.top_true` (`Satisfies.lean:130`)
discharges both the event and the guard. So `Satisfies M (f 0) (𝐅⊤)` holds in **every** admissible
`D`, and `branchSat [F(𝐅⊤)@0] ord` is **false**.

`b` is also a `temporalHintikkaSet` (`Saturation.lean:1019-1030`): every `sf ∈ b` yields
`.notApplicable`, whose case is `True`. So no strengthening of the saturation hypothesis rescues
the statement.

**`openBranch_branchSat` is therefore not a hard theorem — it is a false one.** So is
`temporalTableau_complete` in either polarity.

### Root cause (defect C1): no seriality rule

The tableau never creates a successor for the root time.

- `temporalApplyPos`, `asAllFuture?` arm (`Rules.lean:227-234`): the `𝐆` rule maps over
  `ord.futureOf t`. With `ord = empty` (`TimeOrdering.lean:73`), `futureOf 0 = []`, `newForms` is
  empty, and the rule returns **`.notApplicable`**. Symmetric for `𝐇` (`Rules.lean:236-244`).
- `temporalApplyNeg`, `asUntl?` arm (`Rules.lean:310-321`): the only rule that can create a fresh
  future time from a *negative* until is gated by
  `if futureTimes.isEmpty && ord.timeCount > 0 && ord.timeCount < 4`. At the root
  `ord.timeCount = 0` (`TimeOrdering.lean:111-112` over `constraints = []`), so
  `ord.timeCount > 0` is **false** and the rule returns `.notApplicable`. Symmetric for `snceNeg`
  (`Rules.lean:337-347`).

Only the four *positive* existential rules (`someFuturePos`, `somePastPos`, `untlPos`, `sncePos`)
ever call `addFuture`/`addPast`. A root branch consisting solely of negative existentials and
positive universals is therefore frozen. Confirmed by execution:

```
𝐅p → 𝐅⊤        = CLOSED   (T(𝐅p)@0 creates a time first; calculus then works)
p → 𝐅⊤         = OPEN     (same shape, time-creating conjunct removed)
𝐅q → (𝐆p → 𝐅p) = CLOSED   (correct once a time exists)
```

### Second, independent root cause (defect C2): the hard-coded `timeCount < 4` cap

The same gate caps the total number of time points at 4. Probe on the family
`φ_k := 𝐅q → 𝐅^k ⊤` (valid for every `k`):

```
k = 0,1,2,3 : CLOSED
k = 4       : OPEN |b|=24 times=[0,1,3,2] cons=[(2,3),(1,2),(0,1)]
k = 5       : OPEN  (same)
k = 6       : OPEN  (same)
```

The cut is exactly at 4 times. This is a second, independent incompleteness source that survives
any fix to C1, and it is a bare magic number with no stated justification
(`TimeOrdering.lean:107-112` documents it only as "a gating condition"). Note that C2 is *not*
excluded by strengthening `openBranch_branchSat` with "the ordering has at least one constraint":
the `k = 4` branch has three constraints and is still wrongly open.

### Neither defect was previously recorded

`Completeness.lean:63-116` and `reports/03` attribute the entire block to (a) fuel-sufficiency and
(b) the tracker `.branching` gap. Grepping the task's reports and plans for `timeCount` returns
**nothing**; "seriality" appears only in the sense of `validSerial`/`NoMaxOrder` frame conditions,
never as a missing rule. Both C1 and C2 are new to this dispatch.

### The island model is *also* insufficient, conditional on C1/C2 being fixed

Even granting a repaired calculus, the island fails — for the opposite reason from the one the
delegation named.

Suppose a repaired tableau returns an open saturated branch containing `T(𝐆p)@0` together with a
successor time `1` carrying `T(p)@1`, so `ord.instant 0 = 0`, `ord.instant 1 = 1`. Then
`Satisfies (extractModelℤ b ord) 0 (𝐆p)` unfolds (`Satisfies.lean:76`) to `∀ z : ℤ, 0 < z →
valuation z p`. The valuation is `true` only at `z = 1` (no branch label maps to `z ≥ 2`), so it
is **false at `z = 2`**. The branch is finite; `ℤ` is `NoMaxOrder`; therefore *every* finite
branch carrying a positive `𝐆` (or `𝐇`) falsifies it in the island model. There is no escape via
choosing a different `D`: `NoMaxOrder` is mandated by `branchSat` (`Soundness.lean:99`) and
forbids a finite domain.

**So the delegation's hypothesised failure mode is the wrong one.** For a genuinely saturated
branch with an empty tracker, all *eventualities* are fulfilled inside the branch by construction
— report 03 §3 item 2 is correct about that. What fails is the dual: **positive universals need
content at instants the branch never populated**, and **negative eventualities are the ones the
island accidentally gets right** (an all-`false` tail vacuously satisfies `F(𝐅p)@t`). The island
model is systematically biased toward `false`, which is exactly wrong for `𝐆`/`𝐇`.

**Answer to Q2: an island model does NOT suffice. A total extension of branch content to all of
`ℤ` is required. Periodicity is the standard such extension, so the periodic machinery remains on
the critical path — but for the `𝐆`/`𝐇` reason, not the eventuality reason.**

---

## Q3 — If the island sufficed, what would Phases 5-7 reduce to?

Not applicable: it does not suffice (Q2). Recorded for completeness so the plan revision does not
re-litigate it: had the island sufficed, Phases 4c/4d would have been deletable and Phases 5-7
would have reduced to extending `temporalTruthLemma_propositional_aux`'s complexity induction
(`Completeness.lean:668`) with four constructor cases over `extractModel`. That route is closed.

---

## Q4 — Periodicity IS required: what is the minimal lasso, and does it change P1?

### What is missing from the landed Phase-4 assets

The two landed reductions are **not a bi-lasso**. `Completeness.lean` defines exactly four models
(`:167` `extractModel`, `:209` `extractModelℤ`, `:278` `extractModelℤPeriodic`, `:344`
`extractModelℤPeriodicPast`). The last two are *independent* `TemporalModel ℤ Atom` values, each
folding one tail and leaving the other unhandled. **No composed bidirectional model exists.**
Defining it is unrecorded work.

### Minimal construction

The minimal object that can discharge `branchSat` is a *totalising* reduction
`ρ : ℤ → ℤ` whose image is contained in the set of populated instants, defined by three cases:

1. `z < pAnc` → `periodicReducePast pAnc pNew _ z` (past lasso),
2. `pAnc ≤ z ≤ instNew` → `z` (the populated core),
3. `instNew < z` → `periodicReduce instAnc instNew _ z` (future lasso),

with the model `valuation z p := b.any (… ord.instant sf.label == ρ z …)`. Three obligations that
**no current artifact states**:

- **O1 (population/surjectivity)**: every `z ∈ [pAnc, instNew]` is `ord.instant`-populated, i.e.
  `ρ`'s image consists only of real instants. Note `periodicReduce` is the *identity* on
  `z ≤ instNew` (`Completeness.lean:258-259`), so an unpopulated interior instant reads `false`
  and reintroduces exactly the island defect locally. Plausibly provable: `addFuture`/`addPast`
  move the instant by exactly `±1` from an existing label (`TimeOrdering.lean:82,91`) and the
  time graph is connected from the root, so the image of `ord.instant` on used labels is a
  contiguous `ℤ`-interval containing `0`. **This should be its own lemma and is a good first
  target** — it is small, self-contained, and needed by every downstream route.
- **O2 (loop-window fidelity)**: the time-types at `instAnc` and `instNew` agree in the direction
  the truth lemma consumes. `isSubsetBlocked` (`Branch.lean:120-123`) only gives *containment*
  (`typeNew ⊆ typeAnc`), not equality. Containment is the wrong direction for satisfying a
  positive `𝐆` after folding: the folded copy may be missing formulas the original had.
- **O3 (instant injectivity)**: already surfaced by `extractModelℤ_atom_neg_notSat`
  (`Completeness.lean:505`). Sibling times share instants under `addFuture`, so this is a real
  hypothesis that must be discharged, not assumed.

### Does periodicity change P1's statement?

**Yes, and it makes P1 strictly harder.** P1 was stated as "fuel-exhausted open branches carry an
`isSubsetBlocked` witness". With the correct construction, what is needed is stronger: **every**
returned open branch (fuel-exhausted *or* genuinely saturated) must carry **two** loop witnesses,
one in each temporal direction, satisfying O1 + O2. Report 03 §3 item 2 established that
genuinely-saturated branches have an *empty* tracker and hence no `isSubsetBlocked` witness at
all — under the island hypothesis that was a reason to *skip* the loop; under the corrected
analysis it means **the genuinely-saturated case has no loop witness and therefore cannot be
handled by the lasso either.** That case needs a different treatment (a *stutter*/fixpoint
extension proved adequate because the extremal time-type is closed under the `𝐆`/`𝐇` rules),
which is a third construction nobody has planned.

---

## Q5 — P1 feasibility: does 425 inherit task 317's wall?

**Yes, and worse. The gap here is exponential-vs-quadratic, not exponential-vs-exponential.**

`temporalFuel` (`Saturation.lean:76-78`):

```lean
def temporalFuel (φ : Formula Atom) : Nat :=
  let n := subformulaCount φ
  (4 * n + 4) * (n + 2) + 2          -- = 4n² + 12n + 10
```

The docstring immediately above it (`Saturation.lean:71-75`) justifies this by "the number of
distinct time types is bounded by `2^n`". **A quadratic constant cannot cover a `2^n` bound.**
This is a non sequitur visible on the face of the definition — no formalisation was needed to see
it, which is why it survived three prior research rounds.

Measured confirmation. For a family of propositional tautologies `taut k` (nested
`(pᵢ → pᵢ) → …`), the minimal fuel at which the tableau still returns `CLOSED`:

| k | `subformulaCount` | `temporalFuel` | minimal sufficient fuel |
|---|---|---|---|
| 0 | 2  | 50   | 1 |
| 1 | 3  | 82   | 1 |
| 2 | 6  | 226  | 4 |
| 3 | 9  | 442  | 10 |
| 4 | 12 | 730  | 22 |
| 5 | 15 | 1090 | 46 |

Minimal fuel fits `1.5·2^k − 2` exactly on `k ∈ [2,5]`; `temporalFuel` fits `Θ(k²)` (since
`subformulaCount (taut k) = 3k`). The curves cross near `k = 12`
(`1.5·2¹² − 2 = 6142` vs `temporalFuel = 5626`), beyond which the tableau reports `OPEN` on a
propositional tautology purely from fuel exhaustion.

**Implications for the plan:**

- P1 in the form report 03 proposed ("prove `temporalFuel` is sufficient") is **not provable** —
  it is false. Option (c) *restate the bound* is not available either; the bound is arithmetically
  wrong.
- The available fixes are (a) **raise the fuel to `2^Θ(n)`**, or (b) **add `timeType`
  deduplication** to the saturation loop so the exponential state space is actually collapsed.
  These have opposite costs: (a) is a one-line monotone change that keeps everything decidable but
  makes the procedure impractical to `#eval` and does *not* by itself bound the number of
  *branches*; (b) is the mathematically correct FMP move but is `Rules.lean`/`Saturation.lean`
  surgery with a soundness re-audit.
- **Fixing C1/C2 makes P1 strictly worse**, because removing the `timeCount < 4` cap removes the
  only thing currently bounding time creation. Any C1/C2 fix must be planned together with the
  fuel decision, not before it.
- **Task 317's own final blocker is the same species.** Its recorded blocker in `state.json` is
  now *"unprovable in current 6-rule tableau calculus … Needs NEW branching rule in
  `Rules.lean`/`Expansion.lean` + soundness re-audit + fuel machinery re-derivation"* — i.e. 317
  also concluded, after its fuel research, that the real defect was a **missing rule**, not a
  measure. 425 has independently reached the identical diagnosis. This is strong convergent
  evidence that the correct move for both tasks is calculus repair.

**Mathlib API note (carried forward, still correct but now downstream):**
`Finset.exists_ne_map_eq_of_card_lt_of_maps_to` remains the right pigeonhole once a *correct*
exponential bound is in place; `IsSuccArchimedean` (already an instance requirement of
`branchSat`, `Soundness.lean:100`) remains the right device for bounding the loop window, and is
the tool for the least-witness argument in O2.

---

## Q6 — P2: the `EventualityTracker` `.branching` defect

**Confirmed real.** `Saturation.lean:156-158`:

```lean
      | .branching branches =>
        let newBranches := branches.map (· ++ b)
        some (newBranches, newBranches.map (fun _ => expanded ++ [sf]), newOrd, tracker)
```

`tracker` is returned **unchanged**. Contrast the `.linear` arm (`:150-155`) and `.persistent` arm
(`:159-165`), both of which run `registerEventualities … |> fulfillEventualities …`. Since
`untlPos`/`sncePos` are branching rules (`Rules.lean:265-282`), the recurring copy `T(U(g,e))@t'`
emitted as `branch2`'s second element (`Rules.lean:271`) is never registered as pending.

**Consequence**: `tracker.hasPending` under-reports, so `findEventualityDefect`
(`Closure.lean:88-91`) short-circuits to `none` and eventuality-defect closure effectively never
fires for the primary Until/Since path. Verified indirectly: every open branch produced in this
dispatch's evaluations had an empty tracker.

**Minimal fix** (scoped, self-contained):

```lean
      | .branching branches =>
        let newBranches := branches.map (· ++ b)
        some (newBranches,
              newBranches.map (fun _ => expanded ++ [sf]),
              newOrd,
              -- mirror the .linear arm, per output branch
              fulfillEventualities b newOrd (registerEventualities (branches.flatten) tracker))
```

Two caveats the fix must resolve, neither of which is cosmetic:

- **Per-branch trackers.** `temporalStepBranch`'s signature returns *one* tracker for *all*
  output branches, and `processNext` replicates it with `newBs.map (fun _ => newTracker)`
  (`Saturation.lean:303`). But the two `untlPos` branches have genuinely different pending sets
  (branch1 fulfils, branch2 defers). A correct fix requires changing the return type to
  `List (EventualityTracker Atom)`, which touches `temporalStepBranch_preserves`
  (`Saturation.lean:181`) and `temporalTableau_trackerBranchFaithful`. **This is why the fix is
  not a one-liner** and should be its own phase.
- Registering eventualities will make `findEventualityDefect` start firing, which changes which
  branches close. Every currently-`CLOSED` result must be re-checked for regressions.

**Does P2 change P1's statement?** Yes — but only once C1/C2 are fixed. Until then the question is
moot: the branches that expose C1/C2 never create a second time at all.

---

## Adversarial Self-Verification (H4)

I attempted to refute my own central claim. Five challenges, and their outcomes:

1. **"Is the returned branch really `[F(𝐅⊤)@0]`?"** — Challenged, verified. `temporalTableau`
   seeds exactly `[⟨.neg, φ, 0⟩]` (`Saturation.lean:535`); the evaluation reported `|b|=1`; the
   only way to reach `.openBranch` is `Saturation.lean:294-296`. No other branch is possible.
2. **"Could `branchSat` be witnessed by some exotic `D`?"** — Challenged, refuted. `branchSat`
   mandates `NoMaxOrder D` (`Soundness.lean:99`). `∃ s > f 0` holds in every such `D`, and
   `Satisfies.top_true` (`Satisfies.lean:130`) discharges event and guard. No `D` escapes.
   `branchSat` is unconditionally false on this branch.
3. **"Could a stronger saturation hypothesis exclude the branch?"** — Challenged, refuted.
   `temporalHintikkaSet` (`Saturation.lean:1019-1030`) holds: all rules are `.notApplicable`,
   whose case is `True`. Adding "`ord.constraints ≠ []`" also fails, because defect C2's `k = 4`
   counterexample has three constraints. Both hypotheses were tried and both are insufficient.
4. **"Is the island really insufficient post-fix, or am I assuming a branch shape that a repaired
   calculus would not produce?"** — Challenged, **partially conceded**. My `T(𝐆p)@0` argument
   assumes a repaired calculus still leaves positive `𝐆` on open branches. That is safe: the `𝐆`
   rule is `.persistent`, which by design keeps `sf` on the branch and off the expanded set
   (`Saturation.lean:159-165`, module docstring `Saturation.lean:34-36`), so `T(𝐆p)` is never
   consumed. But I cannot rule out that a *redesigned* calculus (one that, say, forces a loop and
   marks the branch) would change this. **Confidence: high, not certain.** What would settle it:
   the repaired calculus must be specified first — which is exactly why I recommend C1/C2 before
   any further model work.
5. **"Is the fuel gap real or an artifact of my tautology family?"** — Challenged, held with a
   caveat. The `1.5·2^k − 2` fit is exact on four measured points, and the quadratic form of
   `temporalFuel` is read directly off `Saturation.lean:78`. The crossing at `k ≈ 12` is an
   *extrapolation*; a direct crossing evaluation was attempted but did not complete inside the
   dispatch budget. **Confidence: high for the growth-rate mismatch (measured), medium for the
   exact crossing point (extrapolated).** Cheapest experiment to settle it definitively is
   recorded below.

### Claims by confidence

| Claim | Confidence | Basis |
|---|---|---|
| `openBranch_branchSat` is false as stated | **Certain** | Executed evaluation + two-line semantic refutation |
| Defect C1 (no seriality rule) | **Certain** | `Rules.lean:227-234, 310-321` + 7 executed evaluations |
| Defect C2 (`timeCount < 4` cap) | **Certain** | `Rules.lean:312` + measured cut at exactly `k = 4` |
| Neither C1 nor C2 previously recorded | **High** | Grep of all task reports/plans; absent from `Completeness.lean:63-116` |
| Island model insufficient post-fix | **High** | Argument depends on the repaired calculus's shape (challenge 4) |
| Periodic machinery still needed (O1-O3 unstated) | **High** | Only 4 model defs exist; `periodicReduce` identity below `instNew` |
| P2 tracker defect real | **Certain** | `Saturation.lean:156-158` verbatim |
| P2 fix requires signature change | **High** | `Saturation.lean:303` replicates one tracker across branches |
| `temporalFuel` growth-rate mismatch | **High** | Measured `1.5·2^k−2` vs `Θ(k²)` from `Saturation.lean:78` |
| Exact fuel crossing at `k = 12` | **Medium** | Extrapolation; direct evaluation not completed |

### Single cheapest experiment to settle the remaining uncertainty

Run, with a generous timeout, in a scratch file importing
`Cslib.Logics.Temporal.Tableau.Saturation`:

```lean
-- taut k is a propositional tautology for every k, hence validDiscrete.
#eval [12, 13, 14].map fun k =>
  (k, temporalFuel (taut k),
      -- at the shipped fuel
      (match temporalTableau (taut k) with | .closed => "CLOSED" | _ => "OPEN"),
      -- at 40000 fuel
      (match temporalExpandBranches [[⟨.neg, taut k, 0⟩]] [[]] [TimeOrdering.empty]
              [EventualityTracker.empty] 40000 with | .closed => "CLOSED" | _ => "OPEN"))
```

A row reading `(k, _, "OPEN", "CLOSED")` is a direct executed proof that `temporalFuel` is
insufficient and that P1 is false at the current constant. (Expected `k ≥ 12`; budget several
minutes — `2^k` branches.)

### Revisions triggered by verification

- **Revised**: my initial reading was that the island model fails on *eventualities* (the
  delegation's framing). Verification against `Satisfies.lean:70-77` showed the island's all-`false`
  tail *satisfies* negative eventualities and *falsifies* positive universals. The polarity was
  inverted; §Q2 now states the corrected version.
- **Revised**: I initially treated P1 as "hard but open" per report 03. Reading
  `Saturation.lean:76-78` arithmetically showed it is false at the current constant; §Q5 now says
  so, and removes report 03's option (c).
- **Added**: obligations O1-O3, none of which appear in plan-04, surfaced only when I tried to
  write down the composed bi-lasso model and found no composed definition exists.

### BibKey verification status (H3)

All Tier 1 citations verified against `references.bib` this dispatch:
`Reynolds1994` (:749), `HodkinsonReynolds2006` (:760), `Burgess1982I` (:668),
`CaleiroViganoVolpe2013` (:773), `Gabbay1993` (:785), `Smullyan1968` (:218),
`VardiWolper1986` (:818). No unverified BibKey is used. No new BibKey needs adding.

---

## Recommended Phase Decomposition (input to `/revise 425`)

Plan-04's Phases 4c/4d/5/6/7 must be **suspended, not resumed**: they build a countermodel for a
theorem that is currently false. Replace with a calculus-correctness front.

**Sequencing principle**: fix the calculus, re-establish the decision procedure's *extensional*
correctness on executable test vectors, and only then return to model construction. Every phase is
sized to one agent run and gated on `lake build Cslib.Logics.Temporal.Tableau.Completeness` plus a
regression `#eval` suite.

### Phase A — Executable conformance harness (do this first, ~1h)

Add `CslibTests/` (or a scratch harness) with the seven evaluations from §Q2 plus the `φ_k` family
as **expected-value assertions**. Without this, C1/C2 fixes cannot be validated and regressions in
currently-`CLOSED` results will go unnoticed. Deliverable: a test file that currently *fails* on
the five wrong `OPEN` results. This makes the defect a red test rather than a prose claim.

### Phase B — Defect C1: seriality rule (~2-3h)

Add a rule that guarantees every time point acquires a successor and a predecessor before the
branch counts as saturated. Two candidate designs, to be decided in the phase:

- **B1 (preferred)**: a dedicated `seriality` arm in `temporalApplyPos`/`temporalApplyOne` that
  fires when `ord.futureOf t = []` (resp. `pastOf`) and `t` is not subset-blocked, creating one
  fresh successor via `addFuture` and running `propagateToFuture` (`Rules.lean:185-195`).
- **B2**: drop the `ord.timeCount > 0` conjunct from `Rules.lean:312`/`:338` so `untlNeg`/`snceNeg`
  can seed the first time. Cheaper, but only helps root branches that *contain* a negative
  until/since — it does **not** fix `𝐆p → 𝐅p`-style branches whose only temporal content is a
  positive universal. B2 is insufficient alone.

`temporalApplyPos_preserves`/`temporalApplyNeg_preserves` (`Rules.lean:502`, `:601`) must be
extended with the new arm; both are `split`-driven and will surface the new case as an unproved
goal, so this is mechanically checkable. Gate: Phase A's `𝐅⊤`, `¬𝐆⊥`, `𝐆p → 𝐅p`, `𝐅𝐅𝐅⊤`, `𝐏⊤`
rows flip to `CLOSED`; no previously-`CLOSED` row regresses.

### Phase C — Defect C2 + fuel decision (~2-3h, must be planned jointly)

Remove the `ord.timeCount < 4` cap and simultaneously decide the fuel question, since C1+C2
together remove every current bound on time creation. Recommended: **raise `temporalFuel` to an
explicitly exponential bound** (`2 ^ (2 * subformulaCount φ + 2)` or similar) and correct the
docstring at `Saturation.lean:71-75` to state the bound it actually implements. Deduplication
(the mathematically better fix) should be recorded as a follow-on, not attempted here. Gate:
Phase A's `φ_k` family closes for `k ≤ 8`; the §Q5 experiment no longer shows an `OPEN`/`CLOSED`
split.

### Phase D — Defect P2: per-branch eventuality trackers (~2-3h)

Change `temporalStepBranch`'s return type to carry `List (EventualityTracker Atom)`, register
eventualities on the `.branching` arm per output branch, and re-thread
`temporalStepBranch_preserves` (`Saturation.lean:181`), `processNext` (`Saturation.lean:297-304`)
and `temporalTableau_trackerBranchFaithful`. Gate: eventuality-defect closure demonstrably fires
on at least one `#eval` vector; no regression in Phase A.

### Phase E — Instant-image contiguity (O1) (~1-2h, independent, can run in parallel with B-D)

Prove: for any `ord` reachable from `TimeOrdering.empty` by `addFuture`/`addPast`, the image of
`ord.instant` on labels occurring in `b` is a contiguous `ℤ`-interval containing `0`. Follows from
`TimeOrdering.lean:82,91` (`±1` steps) plus connectivity of the time graph from the root. This is
the smallest genuinely-needed new lemma, it is needed by *every* downstream model route, and it
does not depend on B-D. **Recommend starting here in parallel** — it is the one piece of the
existing plan that survives intact.

### Phase F — Re-derive the model requirement (research, ~2h)

Only after B-E: re-run this report's Q2/Q4 analysis against the *repaired* calculus and decide the
final model shape (composed bi-lasso vs. stutter-extension for the no-loop case vs. both). Do not
pre-commit. Explicitly re-examine adversarial challenge 4 above.

### Phase G+ — Truth lemmas and assembly

Only after F. Note the unrecorded obligation: `temporalTruthLemma_propositional`
(`Completeness.lean:1189`) is stated over `extractModel` (`Nat`), and must be **re-proved over the
final ℤ-model**, with O3 (`ord.instant` injectivity) discharged rather than hypothesised. Also fix
the polarity bug below.

### Statement bug to fix during revision (independent, free)

Plan-04 line 403 states `temporalTableau_complete : (∃ b ord, temporalTableau φ = .openBranch b
ord) → satisfiableDiscrete φ`. With the root seeded as `⟨.neg, φ, 0⟩` (`Saturation.lean:535`),
`branchSat` yields `satisfiableDiscrete (¬φ)`, not `satisfiableDiscrete φ`. Routed through
`validDiscrete_iff_not_satisfiableDiscrete_neg` (`Validity.lean:253`), the correct statement is
`… → satisfiableDiscrete (¬φ)`, hence `¬ validDiscrete φ`. As written, the theorem does not follow
from `openBranch_branchSat` and would fail at Phase 7 assembly.

---

## Risks / Caveats

- **Scope escalation is real and should be surfaced to the user.** This task was scoped as "finish
  the FMP completeness front". It is now "repair the temporal tableau calculus". Phases B/C/D are
  `Rules.lean`/`Saturation.lean` surgery with soundness implications, which is closer to task
  426/439 territory than to plan-04's territory. Consider `/spawn 425` for B, C+, D as separate
  tasks rather than growing this one.
- **C1's fix interacts with termination.** Adding a seriality rule that fires whenever
  `futureOf t = []` will not terminate unless it is gated on subset-blocking. The gate must be
  `isTemporallyBlocked` (`Branch.lean:160-167`), which is exactly the device P2's fix repairs — so
  B and D are coupled and D may need to land first.
- **Task 317 is the same problem.** Both tasks now diagnose "the calculus is missing a rule". If a
  shared fix pattern exists (a serialisation/branching rule plus a re-derived fuel bound), doing
  them together is cheaper than twice. Worth a `/spawn` decision.
- **Zero-debt gate holds throughout.** No `sorry`, no axiom, no vacuous definition is acceptable
  for any of the above. A documented `[BLOCKED]` with an exact goal state is the sanctioned outcome
  if a phase does not close — as tasks 317 and 506 did.
- **Everything in this report is a *negative* result about existing code.** No `Cslib/` file was
  modified this dispatch. The scratch file used for evaluations
  (`/home/benjamin/Projects/cslib/Scratch425.lean`) is not part of the build and should be deleted.
