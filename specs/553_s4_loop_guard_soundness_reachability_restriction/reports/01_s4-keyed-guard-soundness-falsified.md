# S4 Keyed Loop-Check Guard: Soundness Verdict and Repair Space

**Task type**: cslib
**Status**: research complete
**Scope**: `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`

---

## 1. Headline Findings

Three verdicts, in decreasing order of certainty.

| # | Question | Verdict | Evidence |
|---|----------|---------|----------|
| V1 | Is the keyed S4 soundness theorem false? | **FALSE, with a machine-checked counterexample.** `modalTableauS4Keyed` closes on a formula that has a 3-world reflexive-transitive countermodel. | Section 2 |
| V2 | Does narrowing the guard to `ReflTransGen` of the accessibility edge break termination? | **YES — and worse than predicted.** It does not merely break the pigeonhole *proof*; it makes the guard fire almost never, so the world bound becomes *false*, not just unproven. Measured: **96.7 % of all blocking decisions (2269 of 2347) target a world that is not reachable from the source.** | Section 3 |
| V3 | Can the guard be narrowed at all without collapsing termination? | **No local guard edit reconciles the two requirements.** Termination and soundness demand incompatible comparison objects (Section 4). The keyed driver's *definition* must change; no amount of proof engineering can rescue the current one. | Sections 4–5 |

The task's framing question — "determine whether the guard can be narrowed at all without
collapsing the termination argument" — has the answer **no**, and the follow-on question is now
moot in its original form because the algorithm is unsound for a *second, independent* reason
that guard-narrowing does not address.

---

## 2. V1: `modalTableauS4Keyed_sound` is False

### 2.1 The counterexample

Let `¬X := X → ⊥`, and over two atoms `p0`, `p1`:

```
αA  := □p0 ∨ ¬¬◇p1
αL  := □p0 ∨ ¬□p1
φ₀  := □αA ∨ □αL
```

Fully expanded:

```
φ₀ = □(□p0 ∨ ((◇p1 → ⊥) → ⊥)) ∨ □(□p0 ∨ (□p1 → ⊥))
```

**Claim A**: `modalTableauS4Keyed φ₀ = .closed`.
**Claim B**: `φ₀` is not `s4Valid`.

Both were verified by evaluation against the built module (Section 2.4).

### 2.2 Countermodel for Claim B

Three worlds `{0, 1, 2}`, `R = {(0,0), (0,1), (0,2), (1,1), (2,2)}` — reflexive and
transitive. Valuation: `p1` true at world `1` only; `p0` false everywhere.

- At world `2`: `p0` false and `2 R 2`, so `□p0` is false; the only successor of `2` is `2`
  itself and `p1` is false there, so `◇p1` is false, hence `¬¬◇p1` is false. So `αA` is false
  at `2`, hence `□αA` is false at `0`.
- At world `1`: `p0` false and `1 R 1`, so `□p0` is false; `p1` holds at the only successor of
  `1`, so `□p1` holds and `¬□p1` is false. So `αL` is false at `1`, hence `□αL` is false at `0`.
- Therefore `φ₀` is false at world `0` of a reflexive-transitive model. Not `s4Valid`.

### 2.3 The refutation trace (why the tableau closes)

The refutation is a single non-branching path. Abbreviating worlds by index:

| Step | Event |
|------|-------|
| 1 | `F(φ₀)@0` α-splits to `F(□αA)@0`, `F(□αL)@0`. Box context of `0` stays empty. |
| 2 | `F(□αA)@0` mints world **1**, key `{(neg, αA)}`. Edge `0→1`. |
| 3 | `F(αA)@1` α-splits to `F(□p0)@1`, `F(¬¬◇p1)@1`. `F(¬¬◇p1)@1` is **not yet expanded**, so world `1`'s box context is still empty. |
| 4 | `F(□p0)@1` fires the minting shape. Prospective birth content = `{(neg, p0)}`. No recorded key matches, so world **2** is minted with key `{(neg, p0)}`. Edge `1→2`. |
| 5 | `F(¬¬◇p1)@1` now expands, ultimately yielding `F(◇p1)@1`, which propagates `F(p1)@2` and `F(◇p1)@2`. World `2`'s **live** content is now `{(neg,p0), (neg,p1), (neg,◇p1)}` — but its **recorded key is still `{(neg, p0)}`**. |
| 6 | `F(□αL)@0` mints world **3**, key `{(neg, αL)}`. Edge `0→3`. |
| 7 | `F(αL)@3` α-splits to `F(□p0)@3`, `F(¬□p1)@3`. `F(¬□p1)@3` is not yet expanded, so world `3`'s box context is empty. |
| 8 | `F(□p0)@3` fires the minting shape. Prospective birth content = `{(neg, p0)}`, which **matches world 2's stale recorded key**. `blockingWorldS4Keyed` returns `some 2`. **Edge `3→2` is added — and world 2 is not reachable from world 3.** |
| 9 | `F(¬□p1)@3` expands to `T(□p1)@3`. This is `.persistent` box-positive propagation, so it fires along `3→2`, adding `T(p1)@2` and `T(□p1)@2`. |
| 10 | Branch now contains `T(p1)@2` **and** `F(p1)@2`. **Closed.** |

The closure is spurious: world `2` is a legitimate successor of world `1` (which requires
`¬p1` there via `¬◇p1`), and would be a legitimate successor of world `3` (which requires `p1`
there via `□p1`), but no single world can be both. The tableau identified them anyway.

### 2.4 Reproduction

The evaluation harness is
`specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4probe.lean`, run with
`lake env lean <path>` from the repository root. It is a standalone `import
Cslib.Logics.Modal.Tableau.LoopChecking` file, so it sits outside the `module` /
`public meta import` boundary that blocks `#eval`/`native_decide` *inside* the Tableau
directory — this is a **newly available verification channel** that prior work on this line did
not have, and it is the reason this task could settle the question empirically rather than by
proof attempt.

The harness contains:

- `dfs` / `tabCloses` — a depth-first driver over `modalStepBranchS4Keyed φ₀` that returns
  `some true` (all branches closed), `some false` (a saturated open branch was reached), or
  `none` (step budget exhausted). It mirrors `modalExpandBranchesS4Keyed`'s worklist semantics:
  each child inherits the returned `acc`/`keys`, closed branches are dropped, the first
  saturated open branch aborts.
- `dfsL` / `tabClosesL` — the same over the un-keyed, live-set-guarded `modalStepBranchS4`.
- `sat` / `isS4` / `hasCountermodel` / `notS4Valid` — brute-force S4 semantics over all
  reflexive-transitive frames of size `≤ n` and all valuations over `natoms` atoms.
- `gen` / `allUpTo` — exhaustive formula enumeration by node count.
- `trace` — step-by-step printer flagging redirect edges as reachable or unreachable.
- `classify` / `dfsR` — the redirect instrumentation used for Section 3's measurement.

Confirmed outputs:

```
cex = (□(□p0∨((◇p1→⊥)→⊥))∨□(□p0∨(□p1→⊥)))
tableau closes = (some true)
countermodel: world=0 R=[(0,0),(0,1),(0,2),(1,1),(2,2)] valuation=[(0,[]),(1,[1]),(2,[])]
```

**The verdict does not rest on the re-implementation.** A second file,
`.../artifacts/s4driver.lean`, calls the shipped drivers directly, substituting an explicit fuel of
400 for `modalFuelS4 φ` (which is astronomically larger; once every branch closes, the worklist
empties and additional fuel cannot change `.closed`):

```
modalExpandBranchesS4Keyed cex, fuel 400 = CLOSED     ← the shipped keyed driver
modalExpandBranchesS4      cex, fuel 400 = OPEN       ← the shipped live-set driver
B axiom keyed = OPEN                                  ← control
T axiom keyed = CLOSED                                ← control
```

So `modalTableauS4Keyed φ₀ = .closed` while `φ₀` is not `s4Valid`: **`modalTableauS4Keyed_sound`
is false as a statement.** The same run also confirms empirically that the live-set driver
`modalTableauS4` does *not* close `φ₀` — i.e. this counterexample is specific to the keyed
guard (see Section 2.5).

Harness sanity checks (all as expected): the T axiom `□p → p`, the 4 axiom `□p → □□p`, and the
K axiom all close and are S4-valid; the B axiom `p → □◇p`, the 5 axiom `◇p → □◇p`, and the
McKinsey formula `□◇p → ◇□p` all leave an open branch and all have countermodels.

### 2.5 The two independent defects

The counterexample exercises **both** of the following. Either alone is a defect; the
counterexample happens to need only the first to *fire*, and the second to be *harmful*.

**Defect S (staleness).** `blockingWorldS4Keyed` compares the prospective birth content against
`keys` — each world's content **as recorded at birth**. World `2` had accumulated
`F(p1)@2`/`F(◇p1)@2` from world `1` by step 8, but its key never moved. The live-set guard
`blockingWorldS4` would have compared against `relevantSetFinset φ₀ b 2 = {(neg,p0), (neg,p1),
(neg,◇p1)}` and **rejected the block**. So this specific counterexample is a keyed-guard defect
that the live-set guard does not have.

**Defect R (no reachability restriction).** The redirect edge `3→2` requires `m.r (f 3) (f 2)`
in an arbitrary model, and `s4FC` is reflexive+transitive but not symmetric, so nothing supplies
it. This is the defect the task description names. It is real and it is what converts Defect S
from "a stale comparison" into "an unsound edge".

**Defect R is not fixed by fixing Defect S.** Structurally, the live-set guard is exposed to
the same attack pattern with a different timing: block while `live(wBlock) = prospective(lbl)`
holds, *then* let `lbl` acquire a new `T(□ρ)@lbl`, which propagates `T(ρ)@wBlock` along the
unjustified edge. What makes this hard to realise in practice is the current driver's
depth-first expansion order (`b.findSome?` over a branch whose new formulas are prepended),
which fully saturates a world's subtree before starting a sibling's — so `wBlock` is typically
already settled when a later world blocks into it, and a settled `wBlock`'s live set is closed
under α/β consequences, which forces the "extra" formula to trace back to `lbl`'s own
requirements and hence to a *genuine* closure. This is an argument, not a proof: **the live-set
guard is not demonstrated unsound, and it is also not sound.** See Section 6.

---

## 3. V2: The Reachability Restriction Destroys Termination

The task's critical prediction is **confirmed**, and the mechanism is more severe than the
hypothesis stated. There are two levels.

### 3.1 Proof level (the predicted failure)

`blockingWorldS4Keyed_none_fresh` (LoopChecking.lean:501) currently yields

```
∀ w' k', (w', k') ∈ keys → k' ≠ successorBirthContent φ₀ b s φ w
```

Restricting the candidate list to `w'` with `Relation.ReflTransGen acc.hasEdge w w'` weakens
this to the same statement *conditioned on reachability*. Then:

1. `keysUpdate_preserves_keysDistinct` (LoopChecking.lean:529) fails in its `none` branch — its
   whole proof is the appeal to `blockingWorldS4Keyed_none_fresh` for the two mixed
   old-key/new-key cases.
2. `S4LoopInv.keysDistinct` (LoopChecking.lean:4388) is therefore no longer a loop invariant, so
   `modalStepBranchS4_preserves_keysDistinct` (LoopChecking.lean:2723) fails.
3. `modalKnownWorlds_length_le_worldBoundS4` (LoopChecking.lean:3778) consumes `keysDistinct`
   as exactly the injectivity hypothesis of `Finset.card_le_card_of_injOn`. It fails.
4. `modalStepBranchS4_worldBound` (LoopChecking.lean:3816) fails.
5. `modalUniverseS4` / `modalFuelS4` (LoopChecking.lean:237/285) are both defined over
   `modalWorldBoundS4 φ₀`, so `modalExpMeasure_entry_le_fuelS4` and the whole fuel-sufficiency
   line fail with it.

That is the entire termination line, exactly as the carry-forward warning in
`specs/535_.../plans/03_completeness-line-rescope.md` (Risk R1) predicted.

### 3.2 Algorithm level (the decisive failure, not previously stated)

The proof-level breakage would be survivable if the world bound were still *true* under a bigger
constant. It is not, because of the direction of the accessibility edges.

At the moment a minting shape `F(□φ)@lbl` is processed, `acc`'s edges point from parents to
freshly-minted children. Therefore

```
{ w' | Relation.ReflTransGen acc.hasEdge lbl w' } = {lbl} ∪ (lbl's already-minted descendants)
```

Loop-checking needs to block against **ancestors and cross-subtree worlds** — precisely the
complement of that set. Under the restriction the guard can essentially only self-block
(`wBlock = lbl`, the reflexive degenerate case the `blockingWorldS4` docstring already notes),
which is far too weak: a formula generating an alternating chain of witness contents
(`{(neg,a)} ∪ B`, `{(neg,b)} ∪ B`, `{(neg,a)} ∪ B`, …) never self-blocks and mints without
bound. The world bound is then **false**, not merely unproven, and no replacement constant
rescues it.

### 3.3 Measurement

The instrumented sweep (`dfsR`/`classify` in the harness) ran the keyed stepper over all 8532
formulas of node-size ≤ 6 over 2 atoms, classifying every redirect edge by whether its target
was already reachable from its source in the pre-step `acc`:

```
redirects=2347  unsoundRedirects=2269  formulasWithUnsoundRedirect=1047
```

**96.7 % of blocking decisions target a non-reachable world.** Restricting the guard to
reachable candidates therefore discards essentially all of the loop check's power. This is the
quantitative confirmation that Route (i) from the earlier plan is not viable.

Note the second reading of the same number: 2269 unsound-shaped redirects occurred across 1047
distinct formulas without producing a single soundness failure at that size — the counterexample
needed a formula of node-size 19. Small-formula testing does **not** exonerate this guard.

---

## 4. V3: Why No Local Guard Edit Works

State the two obligations side by side.

**Termination obligation** (`keysUpdate_preserves_keysDistinct`): when the guard returns `none`,
the new key must differ from **every recorded key**, globally, with no side condition. Anything
weaker — a reachability filter, a live-set conjunct, a settledness conjunct — admits two worlds
with equal keys, and the injection `w ↦ key w` that carries the pigeonhole bound dies.

**Soundness obligation**: when the guard returns `some wBlock`, everything `lbl` will *ever*
propagate along the new edge must already hold at `wBlock` — in the model, not just on the
branch. Because `branchSatisfiableIn` (FrameSoundness.lean:110) requires *both* that every
branch formula be satisfied at its world's image *and* that `acc.hasEdge w w' → m.r (f w) (f w')`,
and because `modalFourBoxProp`/`modalFourDiaNegProp` (FrameRules.lean:133/143) propagate along
`acc.successorsOf` and are `.persistent` (so they re-fire whenever `lbl` acquires a new box),
the guard's decision must be **stable under later growth of `lbl`'s modal context**.

These two are in direct conflict:

- Termination wants the comparison object to be a **frozen, birth-time** key (that is exactly
  why `blockingWorldS4Keyed` was introduced over `blockingWorldS4` — see the "guard-vs-keys gap"
  discussion at LoopChecking.lean:445–460).
- Soundness wants the comparison object to be **live and final**.

A frozen key cannot be live; a live set is not frozen (that was "Gap 1", LoopChecking.lean:36–40).
Adding a conjunct to the guard weakens only the `none` contract, so it always costs termination
and never buys soundness back. **No local edit to `blockingWorldS4Keyed` closes this.**

---

## 5. Repair Space

### 5.1 Rejected routes

| Route | Why rejected |
|-------|--------------|
| **Restrict candidates to `ReflTransGen acc.hasEdge lbl ·`** (the task's candidate fix) | Section 3. Guard fires on ~3 % of current blocks; world bound becomes false. |
| **Restrict candidates to ancestors of `lbl`** | Soundness needs `m.r (f lbl) (f wBlock)`; an ancestor gives the *converse*, `m.r (f wBlock) (f lbl)`. S4 is not symmetric. Same dead end as the S5 precedent's failure to transfer. |
| **Conjunctive guard (recorded key **and** live set must match)** | Kills the counterexample of Section 2 but weakens the `none` contract to `¬(k' = newkey ∧ live w' = newkey)`, so `keysDistinct` fails. Termination line dies (Section 4). |
| **Drop the redirect edge; block with `(.linear [], acc)`** | Soundness becomes trivial (a blocked mint is a genuine no-op step) and the entire keys/pigeonhole machinery survives *verbatim*. But `modalHintikkaSetGen` conjuncts 3 and 4 (Saturation.lean:476–480) explicitly demand `∃ w', acc.hasEdge w w' ∧ ⟨.neg, φ, w'⟩ ∈ b` for every `F(□φ)@w`. Without the edge no open branch is ever Hintikka, so `modalOpenBranchS4_countermodel` never applies and the landed completeness line becomes vacuous. |
| **Prove soundness in the given arbitrary model by relocating `f`** | `f wBlock` is pinned by `wBlock`'s own branch formulas and by its pre-existing edges. Relocating it requires rebuilding `f` over `wBlock`'s entire subtree — i.e. re-proving a bisimulation/filtration property from scratch. This is the earlier plan's Route (ii); it is a full re-architecture, not a repair. |

### 5.2 The only routes that can work

Both require changing the *definition* of the keyed driver, not just the guard. Neither is a
small change, and each should be sized as its own task.

**Route P — settled-context scheduling (recommended if the S4 decidability line is to be
pursued).**

The unsoundness materialises only through *later* growth of `lbl`'s modal context. Remove that
possibility by construction:

1. Change the driver's formula-selection order so that a minting shape at world `w` is never
   fired while any non-modal formula at `w` is unexpanded, and never before all propagation
   into `w` has settled. (This is the standard "saturate the world, then step modally" tableau
   strategy; concretely it is a change to `modalStepBranchS4Keyed`'s `b.findSome?` predicate,
   not to the guard.)
2. With `boxctx(lbl)` final at decision time and the content match in force, the redirect edge
   is **propagation-inert**: everything it can ever transmit is already on the branch.
3. Weaken the S4 soundness invariant from "every `acc` edge is real in `m`" to "every `acc` edge
   is *propagation-adequate*": for each edge `w → w'`, `f w'` satisfies `□ψ` for every
   `T(□ψ)@w ∈ b` and falsifies `◇ψ` for every `F(◇ψ)@w ∈ b`. This is exactly what
   `modalFourBoxProp_sound`/`modalFourDiaNegProp_sound` (FrameSoundness.lean:1129/1149) and the
   K box-positive rule actually consume; genuine mint edges continue to satisfy the stronger
   condition, and a propagation-inert redirect satisfies the weaker one directly from the branch
   conjunct.
4. `keysDistinct` and the pigeonhole bound are untouched — the candidate set stays global, only
   the *timing* of the decision changes. Delaying a mint can only produce a *different* key, never
   a duplicate one, so the bound survives.

Open risks for Route P, in order of severity:
- (a) Step 1 changes which world is minted when, so `modalExpMeasure_step_lt_S4Keyed` and the
  fuel-sufficiency chain need re-verification.
- (b) The landed completeness line (`modalExpandBranchesS4Keyed_hintikka`,
  `modalTableauS4Keyed_complete`) is stated against the current stepper and needs re-proof
  against the reordered one.
- (c) "All propagation into `w` has settled" must be made a decidable, checkable predicate on
  `(b, e, acc)`; the natural formulation ("no unexpanded formula at `w`, and every predecessor
  of `w` is itself settled") needs a well-foundedness argument to be usable.

**Route Q — split the accessibility record.**

Thread two relations: `accProp` (genuine parent→child mint edges) drives `modalFourBoxProp` and
the soundness invariant; `accWit` (redirect edges) is consulted only by `modalHintikkaSetGen`'s
conjuncts 3/4 and the countermodel construction. Soundness becomes immediate. The cost moves to
completeness: the countermodel's frame is `accProp ∪ accWit`, and its truth lemma needs box
formulas propagated along `accWit` edges too — which is exactly the propagation Route Q removed.
Route Q therefore reduces to Route P's step-2 obligation (redirect edges must be
propagation-inert) with extra bookkeeping, and is strictly worse. Recorded for completeness of
the survey; not recommended.

---

## 6. What is Now Known About the Live-Set Guard

`blockingWorldS4` / `modalApplyOneS4` / `modalTableauS4` — the "reference artifact" the
Hintikka and truth-lemma bridges consume — are **not** implicated by the Section 2
counterexample: at step 8 the live-set comparison rejects the block.

This was confirmed against the shipped driver: `modalExpandBranchesS4` returns `.openBranch` on
`φ₀` (Section 8). An exhaustive live-set sweep over the size-≤ 6 corpus was started for
comparison but not completed; it is the report's one unfinished item and is not load-bearing
for any verdict. Regardless of its outcome, the live-set guard has **Defect R**
(no reachability restriction) in full, so `modalTableauS4_sound` is equally unproven, and the
argument sketched in Section 2.5 for why it is hard to exploit depends on the driver's current
depth-first expansion order — i.e. on an accident of `b.findSome?` scheduling, not on a stated
invariant. **Do not treat the live-set guard as sound.** If Route P is pursued, its settledness
discipline is what would make the live-set guard defensible; the two changes belong together.

---

## 7. Concrete Recommendations

1. **Do not attempt `modalTableauS4Keyed_sound`.** It is false. This is not a proof-engineering
   gap and no `sorry`-free route exists, because no true statement of that shape exists.
2. **Do not attempt `instDecidableS4Valid` via `modalTableauS4Keyed`.** The decidability
   dichotomy needs soundness; the driver cannot supply it.
3. **`modalTableauS4Keyed_complete` remains true and should be kept.** An over-eager guard only
   makes more branches close, which can only help `s4Valid φ → modalTableauS4Keyed φ = .closed`.
   The landed completeness work is not invalidated.
4. **Land a documentation correction** (the one bounded, immediately actionable deliverable):
   record the counterexample in `LoopChecking.lean`'s `blockingWorldS4Keyed` docstring and in
   `FrameCompleteness.lean`'s S4Keyed section (which currently says the decidability half is
   merely "deferred: it needs the soundness line, which is out of scope"). That framing is now
   wrong and will mislead the next agent into re-attempting an impossible theorem. Suggested
   wording is available in Section 2.1–2.3 of this report. This must state the counterexample
   without citing a task number, per `.claude/rules/no-task-references-in-deliverables.md`.
5. **Re-scope the repair as its own task** along Route P (Section 5.2). It is a driver
   re-architecture with a re-proof obligation on the completeness line; it is not a guard patch
   and should not be planned as one.
6. **Preserve the harness.** `.../artifacts/s4probe.lean` gives this development an executable oracle
   for the first time (the `module`/`public meta import` boundary blocks `#eval` *inside* the
   Tableau directory, but not from a plain importing file outside it). Any future guard redesign
   should be swept against it *before* proof work begins. Consider promoting a cleaned-up
   version into the repository's test surface rather than leaving it as a scratch file.

---

## 8. Verification Log

| Check | Result |
|-------|--------|
| Harness sanity: T, 4, K axioms | close; no countermodel found — consistent |
| Harness sanity: B, 5, McKinsey | open branch; countermodel found — consistent |
| `modalTableauS4Keyed` on `φ₀` (Section 2.1) | `some true` (closed) |
| Brute-force S4 countermodel for `φ₀`, frames ≤ 3, 2 atoms | found (Section 2.2) |
| Keyed sweep, size ≤ 5, 2 atoms, fuel 60 | 1416 formulas, 252 closed, 0 unsound |
| Keyed sweep, size ≤ 6, 2 atoms, fuel 100 | 8532 formulas: 1650 closed, 6882 open, 0 fuel-exhausted, 0 unsound |
| Redirect instrumentation, size ≤ 6 | 2347 redirects, 2269 to non-reachable targets (96.7 %) |
| **Shipped** `modalExpandBranchesS4Keyed` on `φ₀`, fuel 400 | **CLOSED** |
| **Shipped** `modalExpandBranchesS4` (live-set) on `φ₀`, fuel 400 | OPEN |
| Shipped keyed driver, B axiom / T axiom controls | OPEN / CLOSED — correct |
| Live-set exhaustive sweep, size ≤ 6 | not completed (cost); superseded for V1 by the direct driver runs above |

The last row is the only unfinished item. It bears solely on Section 6's assessment of
`modalTableauS4` (which is *already* known not to close `φ₀`), and on no part of V1, V2, or V3.
To obtain it, re-run `.../artifacts/s4probe.lean`, whose `statsL`/`badL` definitions sweep the
live-set driver over the same corpus; budget well over an hour.

### Caveats on the empirical method

- The falsification (V1) is established against the **shipped** `modalExpandBranchesS4Keyed`, so
  the harness's re-implementation (`tabCloses`) is corroboration only. The re-implementation is
  still what carries the *sweep* results, and it mirrors the driver's worklist semantics: each
  child inherits the returned `acc`/`keys`, closed branches are dropped, and the first saturated
  open branch aborts — so both agree on the closed/open verdict even though branch order and
  fuel accounting differ.
- The substitution of fuel 400 for `modalFuelS4 φ₀` is safe in the closing direction: once every
  branch closes the worklist empties and the recursion returns `.closed` regardless of remaining
  fuel, and `modalFuelS4 φ₀ ≫ 400`.
- Making the counterexample a *checked* Lean artifact (as Recommendation 4 requires) should use
  the chained-single-step `rfl`/`decide` technique that `S5Simplification.lean:1960–1975`
  already uses for its own mechanized counterexample, since `#eval`/`native_decide` are
  unavailable inside the Tableau directory itself.
- The absence of unsound formulas at size ≤ 6 is not evidence of soundness at any size: the
  counterexample has node-size 19.
