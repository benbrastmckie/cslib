# Research Report: conjunct 2 of `openBranch_countermodel` over the constructed frame

**Task**: 604 — prove_countermodel_forcing_conjunct_over_constructed_frame
**Session**: sess_1786312852_6b5c1b_604
**File in scope**: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
**Status**: verdict reached, machine-checked. The task's literal target is **refuted**; a
substantial, separately-verified positive result (DP-5) came out of the same analysis.

---

## 1. Verdict

**Conjunct 2 over the frame the predecessor task constructed (`rawEdges`) is FALSE, and this is
machine-checked, not conjectural.** No proof of it exists to be found, so the honest outcome for
this task is a documented negative plus the narrowing below — exactly the outcome the delegation
authorised.

Alongside it, a **positive** result that is verified by a real `lake build`, not merely argued:

> **DP-5 (`truthLemma`'s T(φ'→ψ') case, `Scheme.lean:768`) is dischargeable, sorry-free, over any
> frame carrying raw-edge positive persistence.** The proof is 15 lines, uses only `sat_timp` plus
> the already-sorry-free `IPosPersistRaw`/`IWorldsPlanted` exports, and **compiled green** in a
> spike (§5).

The two results are two halves of one finding: **the truth lemma's F-imp case and its T-imp case
need mutually incompatible frames on the algorithm's current output.** §3's table is the precise
statement, and every cell in it is machine-checked.

---

## 2. What task 603 actually constructed, and why conjunct 2 fails over it

Task 603 landed `openBranch_rawEdges_upward_closed` (`Scheme.lean:8067-8125`), which witnesses
conjunct 1 with `edges := rawEdges` — the tree-only parent→child list
`intExpandBranches_openBranch_sat` already threads. That lemma is sorry-free and correct. The
question this task inherits is whether the SAME `rawEdges` also supports
`¬ IForces … 0 φ`.

It does not, and the counterexample is already in CI:

| source | assertion |
|---|---|
| `CslibTests/BetaSplitRefutation.lean:304` | `report phiRef1 40 = ("OPEN", 17, 2, [(1,0),(2,1)], [(1,2),(2,2)], some (2,1,2))` — the algorithm's **raw** edge list for `phiRef1` is `[(1,0),(2,1)]` |
| `CslibTests/BetaSplitRefutation.lean:387` | `branchesAgree = true` — the recreated loop reproduces the REAL `intuitionisticTableau` branch at the real fuel `intFuelExt phiRef1` |
| `CslibTests/WitnessProbe.lean:174-176` | `check [(1,0),(2,1)] = some (true, true)` — that raw frame is upward-closed **and forces `phiRef1` at world 0** |

`check`'s second component is `evalF edges b 0 φ`, a case-for-case mirror of `IForces` over
`intAccessPreorder edges`. `(true, true)` means conjunct 1 holds and **conjunct 2 fails**. So
`rawEdges` is not a witness for `phiRef1`, and no amount of proof effort can make it one.

This was independently reproduced at the real entry-point fuel by this task's own probe
(`scratch/PruneProbe.lean`, §4), which also finds a second failing formula, `phiRef3`.

`phiRef1` is not classically valid, so this is emphatically **not** a refutation of
`openBranch_countermodel` itself (the §2 structural argument of
`specs/591_.../reports/01_openbranch-countermodel-disposition.md` still stands, and witnesses do
exist for all eight test formulas). It refutes only the frame choice.

---

## 3. The frame-adequacy table (the core finding)

`truthLemma` consumes exactly two frame-dependent facts:

- **F-imp case** (`Scheme.lean:769-776`) needs `IFimpAccess edges b`: every `F(φ→ψ)@w` has an
  `edges`-accessible witness `w'` with `T(φ)@w'`, `F(ψ)@w'`.
- **T-imp case** (DP-5) needs positive persistence along `edges` — `T(χ)@x ∈ b` transfers to every
  `edges`-accessible `y` (§5 shows this is exactly what closes it).

Conjunct 1 of `openBranch_countermodel` is the atom-shaped special case of the same persistence
fact. So both conjuncts and both halves of the truth lemma reduce to these two predicates, and
the two edge lists the algorithm produces sit on opposite sides:

| frame | `IFimpAccess` | positive persistence | conjunct 1 | conjunct 2 |
|---|---|---|---|---|
| augmented (`augSets`, what `openBranch_countermodel` uses today) | **holds** — proved, exported at `Scheme.lean:6924` | **REFUTED** — `BetaSplitRefutation.lean`, `firstViolation = some (2,1,2)` | fails | reachable via `truthLemma` |
| raw (`rawEdges`, task 603's construction) | **REFUTED** — fails at world 2 for `phiRef1`/`phiRef2`, worlds 3,4 for `phiRef3` (§4) | **holds** — `IPosPersistRaw`, sorry-free, exported at `Scheme.lean:6924` | **PROVED** (task 603) | **REFUTED** (§2) |

Both refutations are machine-checked against the real algorithm at the real fuel. This is the
sharpest available statement of why `openBranch_countermodel` is hard: **the algorithm's current
output offers no single frame carrying both predicates**, and each candidate's missing half is
not merely unproved but false.

A consequence worth recording explicitly, because it affects the honesty of the current source:
the existing `sorry` at `Scheme.lean:8051` sits *after* `refine ⟨edges, ?_, …⟩` has already
committed the witness to `augSets`, so its goal — upward closure over the augmented frame — is
itself a refuted statement. §6 recommends the restructuring that fixes this.

---

## 4. New machine evidence: no natural pruning rule is uniform

`scratch/PruneProbe.lean` re-derives each formula's real `rawEdges`/loop-back lists (via a
`partial` copy of `BetaSplitRefutation.goRaw`, run at `intFuelExt φ`, with
`recreationAgreesWithRealTableau = true` asserted for all eight formulas) and evaluates candidate
sub-frames. `(uc, forces)` — a witness is exactly `(true, false)`.

| formula | rawEdges | `IFimpAccess raw` fails at | raw | prune-at-blocked | prune-at-strictly-blocked | `IFimpAccess` fixpoint |
|---|---|---|---|---|---|---|
| `phiRef1` | `[(1,0),(2,1)]` | `[2]` | (t,**t**) ✗ | (t,f) ✓ | (t,f) ✓ | `K=∅`, `0∉K` ✗ |
| `phiRef2` | `[(1,0),(2,1)]` | `[2]` | (t,f) ✓ | (t,f) ✓ | (t,f) ✓ | `K=∅`, `0∉K` ✗ |
| `phiRef3` | `[(1,0),(2,1),(3,2),(4,3)]` | `[3,4]` | (t,**t**) ✗ | (t,f) ✓ | (t,**t**) ✗ | `K=∅`, `0∉K` ✗ |
| `exMiddle` | `[(1,0)]` | — | (t,f) ✓ | (t,f) ✓ | (t,f) ✓ | `K=[1,0]` ✓ |
| `dblNeg` | `[(1,0),(2,1)]` | — | (t,f) ✓ | (t,**t**) ✗ | (t,f) ✓ | `K=[2,1,0]` ✓ |
| `peirce` | `[(1,0),(2,1)]` | — | (t,f) ✓ | (t,**t**) ✗ | (t,f) ✓ | `K=[2,1,0]` ✓ |
| `deMorgan` | `[(1,0),(2,1),(3,1)]` | — | (t,f) ✓ | (t,f) ✓ | (t,f) ✓ | `K=[3,2,1,0]` ✓ |
| `dummett` | `[(1,0),(2,0)]` | — | (t,f) ✓ | (t,f) ✓ | (t,f) ✓ | `K=[2,1,0]` ✓ |

Four candidate uniform constructions, four failures:

1. **`rawEdges`** (this task's target) — fails `phiRef1`, `phiRef3`.
2. **Prune at blocked worlds** (cut every raw edge whose child is the parent endpoint of a
   loop-back edge; expressible from the already-exported `lbEdges`/`IReuseContain` and, thanks to
   `ForestComparable`, disconnecting a whole subtree) — reproduces the known `[(1,0)]` witness for
   `phiRef1` exactly, but **fails `dblNeg` and `peirce`**, where the loop-back is a self-reuse
   `(2,2)` and cutting world 2 destroys the falsifying world.
3. **Prune at strictly-blocked worlds** (same, ignoring self-reuse) — repairs `dblNeg`/`peirce`
   but **fails `phiRef3`**, which needs the self-reuse world cut. Rules 2 and 3 therefore
   contradict each other on the same syntactic signal.
4. **The greatest `IFimpAccess`-supported subframe** — the greatest fixpoint `K` of "every
   `F(φ→ψ)@w` for `w ∈ K` has a witness reachable from `w` inside `K`". This is the construction a
   truth-lemma proof would actually need, since the F-imp case then closes by construction. It
   **collapses to `K = ∅` for `phiRef1`, `phiRef2`, `phiRef3`** — the unsupported blocked world
   strands its parent, which strands its parent, up to world 0.
5. **The maximal atom-inclusion frame `⊑`** — already ruled out by task 591 §4.4 (fails
   `phiRef1`/`phiRef3`). Not re-run.

Note item 4 against item 1 on `phiRef2`: the fixpoint collapses even though `rawEdges` itself *is*
a witness there. That is the general lesson — **conjunct 2 can hold without a truth lemma**, so
routes that go through a truth lemma are strictly stronger than the goal and can fail where the
goal succeeds. Conversely every witness in task 591's exhaustive enumeration was found by search,
not by a rule. No local, structural rule that picks the right sub-frame has been found, and three
of the four natural candidates are now positively excluded rather than merely untried.

---

## 5. Positive result: DP-5 is dischargeable (verified by build)

The in-source STOP-gate note above `truthLemma` (`Scheme.lean:658-670`) records that any copy
channel "only ever copies along the algorithm's RAW edges — strictly fewer worlds than the goal
quantifies over", and concludes the augmented-frame gap must close first. **That obstruction is an
artefact of the frame parameter, and it disappears when the frame is raw or sub-raw.** The needed
copy fact already exists, sorry-free: `IPosPersistRaw` (`Scheme.lean:6782`) is exactly
"`T(χ)@w ∈ b` transfers along one `isAccessible rawEdges` step to any world with an entry", and
`IWorldsPlanted` (`Scheme.lean:3568`, landed by task 603) supplies its side condition.

**Verification performed** (spike, applied to `Scheme.lean`, built, then reverted; the diff is
preserved at `scratch/dp5-spike.diff` and the pre-spike file at `scratch/Scheme.lean.bak`):

- added one hypothesis to `truthLemma`:
  ```lean
  (hpers : ∀ (χ : Proposition Atom) (x y : Nat), isAccessible edges x y = true →
    (⟨.pos, χ, x⟩ : ISF Atom) ∈ b → (⟨.pos, χ, y⟩ : ISF Atom) ∈ b)
  ```
- replaced `intro _; sorry` at `:767-768` with the 15-line proof: lift `hT` to membership, chain
  `hpers` along the `ReflTransGen` order by `induction hle` (the same tail-peeling shape task 603
  used at `Scheme.lean:8109-8125`), apply `sat_timp` **reflexively at `w'`**, then close the
  `F(φ')@w'` arm by `ih_φ'.2` and the `T(ψ')@w'` arm by `ih_ψ'.1`;
- result: `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` →
  **"Build completed successfully (932 jobs)"**, with the `truthLemma` sorry warning **gone**
  (only the `openBranch_countermodel` warning remained).

One ordering detail found the hard way and worth carrying into the plan: `intro hforce_φ'` must
come **after** the persistence `have`, or `induction hle` sweeps `hforce_φ'` into the motive and
the tail case fails with an application type mismatch.

`hpers` as stated is the side-condition-discharged composite. At a `rawEdges` call site it is
derived in five lines from the existing exports (`by_cases x = y`; then
`isAccessible_target_mem_edges` + `IWorldsPlanted` for the side condition, then `IPosPersistRaw`)
— the same three-step move as `openBranch_rawEdges_upward_closed:8112-8123`. Stating it as an
inline hypothesis (rather than referencing `IPosPersistRaw` by name) is deliberate:
`IPosPersistRaw`, `IWorldsPlanted` and `isAccessible_target_mem_edges` are all defined *after*
`truthLemma` in the file, and are `private`.

---

## 6. Recommended landing (implementation-phase guidance)

**Do land** the DP-5 discharge. It closes a genuinely open gap with verified code, is inside
`Scheme.lean`'s scope, and is the outcome the delegation anticipated ("discharging it may fall out
of the same truth lemma").

**Do not** attempt to force conjunct 2. Instead restructure `openBranch_countermodel` so its
remaining `sorry` is honest. Concretely:

1. `truthLemma` gains `hpers`; the DP-5 `sorry` is replaced by §5's proof. `truthLemma` becomes
   sorry-free and is then an unconditionally true, reusable theorem over any persistence-carrying
   frame.
2. `openBranch_countermodel` can no longer instantiate `truthLemma` at the augmented frame
   (`hpers` is refuted there, §3) — and must not `sorry` `hpers`, since sorrying a refuted
   statement is exactly what the file's honesty discipline forbids. Its proof should therefore
   drop the frame-committing `refine ⟨edges, ?_, …⟩` and carry **one** `sorry` for the whole
   existential `∃ edges, upward-closed ∧ ¬IForces`, which is genuinely open and **not** refuted.
3. Net effect on `Scheme.lean`: **2 live sorries → 1**, and the surviving one changes from a
   refuted goal (upward closure over `augSets`) to the open one. No new sorries, no new axioms.
4. Annotation updates, in the honesty register the file already uses: record §3's table verbatim
   at both sites, state that `rawEdges` is **refuted** as a conjunct-2 witness (with the two CI
   citations from §2), that three natural pruning rules and the `IFimpAccess` fixpoint are
   likewise excluded (§4), and that the residual obligation is now precisely *"a frame carrying
   `IFimpAccess` and positive persistence simultaneously, which the current calculus does not
   produce"*. Use "refuted" only for the machine-refuted cells; keep "open" for
   `openBranch_countermodel` itself.

If the implementation dispatch judges step 2's restructuring out of scope, the fallback that
preserves zero-new-sorries with no relocation is task 603's own precedent: land §5's proof as a
**standalone sorry-free variant** beside `truthLemma`, leave `truthLemma`/`openBranch_countermodel`
untouched except for annotations. This costs ~90 lines of duplicated induction and is strictly
worse stylistically; prefer steps 1-4.

**The real fix is out of this file.** Every route above dead-ends on the same defect task 591 §6
item 3 already named: `intFImpReuseWitnessAnc?` (`Expansion.lean`) records a loop-back edge on a
containment check it never re-validates as the branch grows. Re-validating it is what would let
the augmented frame carry persistence, giving one frame with both predicates and collapsing this
whole problem. That is calculus-level work in `Expansion.lean` and should be a separate task.

---

## 7. Zero-debt and reuse compliance

- **Zero new sorries, zero new axioms** in every recommendation above; the recommended landing
  strictly *reduces* `Scheme.lean`'s live sorry count from 2 to 1. Baseline re-confirmed after the
  spike was reverted: `lake build` green, warnings at `:693` (`truthLemma`) and `:7977`
  (`openBranch_countermodel`) only.
- **No Option-B sorry deferral, no placeholder sorries, no weakened statements** are proposed.
- **Reuse-first**: no new definition, typeclass, notation, or Mathlib import is required.
  Everything cited exists — `IPosPersistRaw`, `IWorldsPlanted`, `isAccessible_target_mem_edges`,
  `IFimpAccess`, `IBranchSaturation.sat_timp`, `intAccessPreorder`,
  `intAccessPreorder_le_of_isAccessible`, `ForestComparable`, `IReuseContain`, and
  `Mathlib.Relation.ReflTransGen`. The one new *hypothesis* (`hpers`) is a composite of two
  existing exports, not a new abstraction.
- **Source restored**: `Cslib/` is byte-identical to its pre-spike state (`git status` clean for
  `Cslib/`); all probe artefacts live under this task's `scratch/`.

## 8. Artefacts

- `specs/604_.../scratch/PruneProbe.lean` — the eight-formula frame-adequacy probe (raw/loop-back
  recovery, `IFimpAccess` failure sites, three pruning rules, the support fixpoint). Run with
  `lake env lean <path>`; completes in seconds.
- `specs/604_.../scratch/dp5-spike.diff` — the 28-line verified DP-5 diff.
- `specs/604_.../scratch/Scheme.lean.bak` — pre-spike snapshot used for the restore.

## References

- `specs/603_construct_uniform_frame_for_openbranch_countermodel/reports/01_uniform-frame-construction.md`
  and its summary (what `rawEdges` is, and §7's flagging of this exact reconciliation question)
- `specs/591_decide_openbranch_countermodel_disposition/reports/01_openbranch-countermodel-disposition.md`
  (§2 structural argument, §3 `𝒫(⊑)` characterisation, §4.4/§4.5, §6 item 3 the calculus defect)
- `CslibTests/BetaSplitRefutation.lean`, `CslibTests/WitnessProbe.lean` (the CI-protected
  assertions cited in §2)
- [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
