# Research Report: re-validating `intFImpReuseWitnessAnc?`'s loop-back containment

**Task**: 609 — revalidate_intfimpreuse_witness_anc_loopback_containment
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
**Session**: sess_1786321994_b49e26_609
**Files in scope**: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (calculus),
with the payoff landing in `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
**Status**: verdict reached; a repair is identified and **machine-measured green on every
adequacy and conformance metric**, including the metric that refutes the current calculus.

---

## 1. Verdict

**A repair exists, it is small, and it is measured.** The winning change is not to
`intFImpReuseWitnessAnc?` at all — it is a **rule-selection reorder in `intStepBranch`**:

> **Defer the world-creating `F(φ → ψ)` rule until no other rule is applicable anywhere on the
> branch.** ("beta-priority", variant **V1** below.)

Under V1 the augmented frame carries `IFimpAccess` **and** full positive persistence
**simultaneously** on every formula measured — 9 adequacy-corpus formulas (including all three
that refute the current calculus) plus all 6 open rows of the 20-row propositional conformance
corpus, among them the complexity-9 divergence witness. That is exactly the frame
`openBranch_countermodel` needs, and `truthLemma` is already sorry-free and parametric over any
frame carrying both facts.

Two secondary findings, both machine-checked:

- A second, independent repair (**V2**, provisional reuse with retract-on-violation) is equally
  adequate but costs far more proof work; it is a viable fallback, not the recommendation.
- The most obvious repair (**V3**, put the loop-back edge into the algorithm's own edge list so
  the copy channel maintains containment) is **adequate but fails the termination gate** — see §6.

Nothing in this report proposes a `sorry`, an axiom, a weakened statement, or a new abstraction.

---

## 2. The mechanism, stated exactly

`intFImpRule` returns edge `(w', w)` — the pair is `(child, parent)`. When
`intFImpReuseWitnessAnc?` fires at `F(φ → ψ)@w` and returns ancestor `x`, the invariant side
records the **reverse** edge `(x, w)`, i.e. "`x` is accessible **from** `w`". Combined with the
raw ancestry `x ⟶* w` this makes `x` and `w` **preorder-equivalent** under
`intAccessPreorder`'s reflexive-transitive closure.

Positive persistence over that augmented preorder therefore demands, in **both** directions:

```
posFormulasAt b x  ⊆  posFormulasAt b w      (raw direction — the copy channel gives this)
posFormulasAt b w  ⊆  posFormulasAt b x      (loop-back direction — ONLY the reuse-time check)
```

The second inclusion is precisely the `sfor.all (forcedAtX.contains ·)` conjunct, and it is
checked **once**, at reuse time. Because the two inclusions coincide there, `x` and `w` have
*equal* positive content at that instant — so every positive formula at `w` has a **twin entry
at `x`**, including any unexpanded `T(θ ∨ ρ)`. Those twins are distinct `ISF` values and
beta-split **independently**. On the two of four combinations where they pick different
disjuncts, `pos(w) ⊄ pos(x)` while the loop-back edge stays on the branch unconditionally.

The load-bearing observation for the repair is therefore:

> The invalidation is caused entirely by beta rules that are **still pending at reuse time**. The
> reuse check cannot see a choice that has not been made yet.

Consequently the check does not need to be re-validated *later* — it needs to be **taken later**,
after the branch has no pending choices left to make. That is V1.

**A second invalidation channel, structurally identical and worth naming:** the docstring records
only positive disjunctions, but `intApplyRuleFull`'s `.pos, .imp` arm is also a beta rule whose
`T(ψ)@l` child **adds a positive**. Twin `T(φ→ψ)` entries at `x` and `w` can therefore diverge
the same way. No witness formula for this channel was found in this task's corpus (`phiRef2`,
which is built around exactly this shape, does **not** exhibit the defect), so this is recorded
as a structural observation, not a measured refutation — but any candidate fix must close it too.
V1 closes both channels uniformly, because it defers world creation past *every* beta rule, not
just disjunctions.

---

## 3. Baseline fidelity (the probe is trustworthy)

All measurements below come from `scratch/ReuseRevalidateProbe.lean`, a `Cfg`-parameterised
recreation of `intExpandBranches.go` that is **bit-identical to the library engine when `Cfg` is
all-false**. Two independent fidelity gates, both green:

| gate | result |
|---|---|
| Recreation's returned branch `==` real `intuitionisticTableau`'s, per formula | `true` for all 9 adequacy formulas |
| `phiRef1` raw / loop-back edge lists | `[(1,0),(2,1)]` / `[(1,2),(2,2)]` — identical to the CI assertion at `CslibTests/BetaSplitRefutation.lean:304` |
| Verdicts over the full 20-row propositional conformance corpus | 0 differences from the library |

The recreation follows `CslibTests/BetaSplitRefutation.goRaw`, whose own termination measure is
proved there; the probe copy is `partial` (scratch only).

### Baseline (V0) adequacy, at the real entry-point fuel `intFuelExt φ`

`IFimpAccess` and **full positive-formula** persistence (`truthLemma`'s `hpers`, not merely its
atomic shadow), both over the **augmented** frame:

| formula | worlds | loop-backs | `IFimpAccess` | `hpers` | `¬ forces φ @0` |
|---|---|---|---|---|---|
| `phiRef1` | 0–2 | `[(1,2),(2,2)]` | holds | **FAILS** `(2→1)` | holds |
| `phiRef2` | 0–2 | `[(1,2),(2,2)]` | holds | holds | holds |
| `phiRef3` | 0–4 | `[(1,3),(3,4),(4,4),(2,2)]` | holds | **FAILS** `(2→1)` | holds |
| `phiRef4` | 0–2 | `[(1,2),(2,2)]` | holds | **FAILS** `(2→1)` | holds |
| `exMiddle`, `dblNeg`, `peirce`, `deMorgan`, `dummett` | — | — | holds | holds | holds |

Two things here are **new**, not in the frame-adequacy report this task inherits:

1. **`phiRef4` is a third refuting formula.** It is currently described in
   `CslibTests/BetaSplitRefutation.lean` as a robustness variant "not promoted to an assertion";
   it in fact fails augmented-frame persistence exactly as `phiRef1` does. Worth promoting.
2. **`IFimpAccess` holds over the augmented frame for every formula, and conjunct 2
   (`¬ forces φ @0`) already holds over it too, in the baseline.** The *only* missing ingredient
   in the whole construction is `hpers`. This sharpens the inherited table: the augmented frame is
   one predicate short, not two.

---

## 4. The three candidate repairs, measured

All three were implemented as flags over the same recreation and run at the real fuel.

| | **V1** beta-priority | **V2** retract-on-violation | **V3** cyclic edges |
|---|---|---|---|
| what changes | `intStepBranch` selection order only | `go` gains a provisional-loop-back list + a retraction arm | reuse arm appends `(x,w)` to the algorithm's own `edges` |
| adequacy, 9-formula corpus | **9/9** | **9/9** | 9/9 |
| adequacy, conformance open rows 14–19 | **6/6** | **6/6** | not reached |
| conformance verdicts, 20 rows | **0 differences** | **0 differences** | **did not terminate** (§6) |
| terminates at real fuel incl. divergence witness | **yes** | **yes** | **no** (§6) |
| worlds created | **≤ baseline** (`phiRef3`: 3 vs 4) | = baseline | = baseline |

"Adequacy" = `IFimpAccess` failures empty **and** no positive-persistence violation **and**
`¬ forces φ @0`, all over the augmented frame.

Termination evidence deserves a note, because it is stronger than a growth table. The
conformance corpus's row 20 **is** the complexity-9 divergence witness, and it is run at
`intFuelExt φ0` — a numeral with roughly 13 million digits. A branch that failed to saturate
would exhaust that budget only after effectively unbounded work. **V1 and V2 both return the
correct `OPEN` verdict for that row**, so both saturate; the 14 IPC-valid rows return `CLOSED`,
so neither loses completeness by deferring world creation. A small-fuel growth table was also
run (fuels 10/16/22/28) and is uninformative under per-branch fuel — it measures the fuel-0
cutoff, not saturation — so it is not relied on here.

V2's retraction counter is a useful independent confirmation that the mechanism in §2 is the
right one: retractions fire **only** on the three defective formulas
(`phiRef1`: 1, `phiRef3`: 2, `phiRef4`: 1) and **nowhere else** (0 on the other six).

### Why V1 works, in one paragraph

`stepPrio`'s first pass searches for any unexpanded, applicable, **non**-world-creating formula
anywhere on the branch. When the world-creating arm is reached, that pass returned `none`, so
**nothing on the branch is pending** — every world's positive content is rule-saturated and the
persistence fixpoint has already run. After that point, formulas are only ever added at the
newly created world (a leaf) or pushed **downward** by `applyAllTImpRules`' copy channel and
`intTImpRule`, both of which write only to descendants. Neither `x` nor `w` is a descendant of a
world created after them, so **their positive content is frozen** and the containment recorded at
reuse time is permanent. The divergence that used to happen after the check now happens before
it, where the check can see it and simply decline to reuse.

---

## 5. Recommendation and implementation shape

Land **V1**. Two reasons beyond the measurements: it is the smallest change, and it is the only
one of the three that leaves `go`'s recursion structure — hence its termination measure and the
sorry-free, axiom-clean `intExpandBranches_closed_unsat` — **completely untouched**.

### 5.1 The code change (`Expansion.lean`)

Add beside `intStepBranch` (do not delete it — it becomes the second pass):

```lean
def intStepBranchPrio (b : IBranch Atom) (expanded : List (ISF Atom)) (nextWorld : Nat) :
    Option (IntRuleResult Atom × List (ISF Atom)) :=
  match b.findSome? fun sf =>
      if expanded.any (· == sf) || isWorldCreating sf then none
      else match intApplyRuleFull sf nextWorld b with
        | .notApplicable => none
        | r => some (r, expanded ++ [sf]) with
  | some res => some res
  | none => intStepBranch b expanded nextWorld
```

with `isWorldCreating sf` true exactly on `.neg, .imp`. Then swap the single call site in
`intExpandBranches.go` (`Scheme.lean:5005`).

### 5.2 Why the 102 existing `intStepBranch` references do not each need rework

Everything downstream routes through **three** spec lemmas, and all three transfer:

| existing lemma | how it transfers |
|---|---|
| `intStepBranch_result_ne_notApplicable` (`Expansion.lean:218`) | same proof shape, one extra `if`-guard case |
| `intStepBranch_some_exists` (`Scheme.lean`) | conclusion is unchanged — both passes return `some (intApplyRuleFull sf nw b, e ++ [sf])` for some `sf ∈ b` |
| `intStepBranch_none_compound_mem` (`Scheme.lean`) | **transfers verbatim**, via a new one-line bridge |

That bridge is the key structural fact and it holds **by construction**:

```
intStepBranchPrio b e nw = none  ↔  intStepBranch b e nw = none
```

(`→` because the second pass *is* `intStepBranch`; `←` because the first pass searches a strict
subset of the same candidates.) Every `none`-keyed result — saturation, `IBranchSaturation`,
`intExpandBranches_openBranch_sat`'s open-branch leaf — therefore needs **no** reproof.

### 5.3 The one genuinely new proof obligation, and the existing asset it strengthens

`IReuseContain` (`Scheme.lean:6798`ff) already threads the reuse-time containment through the
`key` induction and is already exported by `intExpandBranches_openBranch_sat` — but it is stated
via a **snapshot existential**: "there exists `bSnap ⊆ b` with `T(χ)@l ∈ bSnap → T(χ)@x ∈ bSnap`".
That existential is exactly the mint-time weakening this defect forces, and it is what makes
`IReuseContain_mono` (`:6824`) provable at all.

The repair's obligation is to **drop the snapshot**:

```lean
∀ x l, (x, l) ∈ lbEdges → ∀ χ, (⟨.pos, χ, l⟩ : ISF Atom) ∈ b → (⟨.pos, χ, x⟩ : ISF Atom) ∈ b
```

i.e. `IReuseContain` with `bSnap := b`. `IReuseContain_snoc` (`:6837`) already establishes the
snoc case from `intFImpReuseWitnessAnc?_spec`'s `hcont` conjunct with `bSnap := b`; what changes
is that `IReuseContain_mono` must be replaced by a **freeze lemma** — under beta-priority, no arm
of `go` adds a positive entry at a world that already carries a recorded loop-back. The
first-pass-empty hypothesis needed for that lemma is available directly at the world-creating arm
from unfolding `intStepBranchPrio`.

Given that, augmented-frame persistence decomposes into two facts that are then both in hand:
raw-edge persistence (`IPosPersistRaw`, already sorry-free) plus the loop-back edges
(the strengthened `IReuseContain`). Chaining them along `ReflTransGen` is the same tail-peeling
move as `openBranch_rawEdges_upward_closed`.

### 5.4 What it unblocks

Three live sorries sit downstream of this single gap, and all three collapse:

| site | current state | after |
|---|---|---|
| `Scheme.lean:8012` `openBranch_countermodel` | whole existential `sorry` | direct `truthLemma` instantiation at the augmented frame |
| `Completeness.lean:170` `intuitionisticTableau_complete` | deliberate `sorry` | `exact h Nat (intExtractValuation _b) _huc 0` (the file already records this as the one-liner) |
| `Minimal/Completeness.lean:166` `minimalTableau_complete` | deliberate `sorry` | same shape |

Recommended phase decomposition (each phase independently buildable and green):

1. `intStepBranchPrio` + its three spec lemmas + the `none`-iff bridge. Swap the call site.
   Verify: full `lake build`, conformance corpus unchanged, zero new sorries.
2. The freeze lemma and the snapshot-free `IReuseContain`; re-thread through `key`.
3. Augmented-frame persistence export from `intExpandBranches_openBranch_sat`.
4. Discharge `openBranch_countermodel`, then the two `Completeness.lean` one-liners.
5. Promote `phiRef4` in `CslibTests/BetaSplitRefutation.lean` and re-point that file's
   refutation narrative at the repaired calculus (the `#guard_msgs` values **will** change —
   they are a regression guard on the defect, and the defect is being removed).

Phase 1 alone is worth landing even if later phases stall: it is verdict-preserving, strictly
reduces world creation, and carries no new proof debt.

---

## 6. Negative result: V3 (cyclic edges) fails the termination gate

Appending the loop-back edge to the algorithm's **own** `edges` is the most direct reading of
"make the containment self-maintaining" — the copy channel then propagates positives around the
cycle, so containment can never break. It is adequate on all 9 adequacy formulas. It should
nonetheless **not** be pursued:

- **Measured**: the 20-row conformance run under V3 **did not terminate within ~25 minutes** at
  the real fuel, where the baseline and both other variants each completed in under ~10 minutes
  on the same machine. This is a budget overrun, not a proof of divergence — but it is the same
  signature the pre-repair calculus showed, and it inverts the entire purpose of ancestor-directed
  blocking: with a cycle in `edges`, `isAccessible edges x w` becomes true in *both* directions,
  so the `x.ble w` label guard is the only surviving ancestor test.
- **Structural**: cycles destroy the forest property that `ForestComparable`, `IWorldsPlanted`
  and `IPosPersistRaw` are all stated against, so the proof-side cost is large even if the
  termination problem were solved.
- **Soundness**: propagating a positive across the loop-back adds `T(χ)@x` entries that an
  arbitrary model of the branch need not satisfy — the same shape as the already-recorded
  **UNSOUND** "Option B" (appending `F(ψ)@x` on reuse, `Expansion.lean`'s reuse-contract note).

V2 remains a genuine fallback if V1's freeze lemma turns out harder than §5.3 projects: it is
equally adequate and equally verdict-preserving. Its cost is that it adds a recursion arm to
`go`, which means a new termination-measure case and a new case in **every** invariant lemma
threaded through the `key` induction — a much larger surface than V1's three spec lemmas.

### Constructions this report does **not** revisit

The exclusions established by prior machine evidence stand and were not re-attempted: `rawEdges`
itself, pruning at blocked worlds, pruning at strictly-blocked worlds, the greatest
`IFimpAccess`-supported fixpoint, and the maximal atom-inclusion frame. All five are *post-hoc
frame constructions over the unchanged algorithm output*; V1/V2/V3 are changes to the algorithm
itself, which is why they are not in tension with those exclusions.

---

## 7. Zero-debt and reuse-first compliance

- **Zero new sorries, zero new axioms, no weakened statements** in any recommendation. The
  recommendation strictly *reduces* the live sorry count (3 → 0 on this path).
- **No Option-B sorry deferral** and no vacuous definitions are proposed anywhere.
- **Reuse-first, checked**: no new abstraction is required. `Cslib.Foundations.Logic.Tableau.`
  `Blocking` already supplies `Branch.posTypeAt` / `Branch.containmentBlocked`, and
  `Scheme.lean:2040` already carries the bridge lemma `posFormulasAt ↔ Branch.posTypeAt`; the
  strengthened containment invariant is a strengthening of the **existing** `IReuseContain`, not
  a new predicate. `intFImpReuseWitnessAnc?` and its two spec lemmas are **unchanged** by the
  recommendation. No new notation, typeclass, or Mathlib import.
- **Source untouched**: all probe work was done in an isolated git worktree pinned to `HEAD`
  (a concurrent session was mid-edit on `Scheme.lean` in the main tree and had it red); `Cslib/`
  in the main working tree was neither read-locked nor modified by this task.

## 8. Artefacts

- `specs/609_revalidate_intfimpreuse_witness_anc_loopback_containment/scratch/`
  `ReuseRevalidateProbe.lean` — the `Cfg`-parameterised recreation plus every metric
  (`fimpFailures`, `firstPosPersistViol`, `evalF`, fidelity checks) and all four variants. Run
  with `lake env lean <path>` after appending a driver section; completes in minutes per variant
  except V3.

## References

- `specs/archive/604_prove_countermodel_forcing_conjunct_over_constructed_frame/reports/`
  `01_conjunct2-frame-adequacy.md` §§3, 4, 6 — the inherited frame-adequacy table and the
  identification of this defect as the root cause
- `CslibTests/BetaSplitRefutation.lean` — the CI-protected refutation and the `goRaw` recreation
  this probe extends
- `CslibTests/TableauConformance.lean` — the 20-row propositional corpus used as the
  soundness/completeness gate
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` — `intFImpReuseWitnessAnc?`
  and its recorded limitation
- [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4 —
  provenance only; not readable from this repository
