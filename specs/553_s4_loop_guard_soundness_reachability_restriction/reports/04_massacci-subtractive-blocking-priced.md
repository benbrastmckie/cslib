# Research Report: Pricing Route (3) — `Massacci2000` Subtractive Blocking

## Metadata

- **Date**: 2026-07-26
- **Task**: 553 `s4_loop_guard_soundness_reachability_restriction`
- **Session**: `sess_1785084826_a33d36`
- **Agent**: cslib-research-hard-agent (`--hard --lit`, `orchestrator_mode: true`)
- **Focus prompt**: *Price route (3) Massacci subtractive blocking: how much of landed completeness
  breaks under quotient extraction, does termination survive, and how does it compare to route
  (2′) on phases and risk?*
- **Reference grounding tier**: **Tier 1** (literature-backed, `Massacci2000`) + Tier 3
  (implementation-backed)
- **Read-only territory**: `Cslib/**` — **no library file was edited**; the `sorry` at
  `FrameSoundness.lean:1244` is untouched (verified: it is still the *only* `sorry` in
  `Cslib/Logics/Modal/Tableau/`, `grep` over all 14 files)
- **New probe artifacts** (all run to completion under `lake env lean`, definitions + `#eval`
  only, no proofs, no `sorry`, no axioms):
  - `specs/553_.../artifacts/s4subtractive.lean` — variants S1/S2, differential sweep,
    independent semantic validity oracle
  - `specs/553_.../artifacts/s4subtractive2.lean` — guard-firing census + two deeper corpora
  - `specs/553_.../artifacts/s4subtractive3.lean` — terminal-open-leaf completeness
    recoverability, plus the shipped-ordered-driver control

---

## Verdict (stated first)

> **Route (3) is VIABLE. It costs approximately 9 phases, versus route (2′)'s 7-8 — but route
> (2′)'s phase count is not comparable, because its single load-bearing phase requires exactly
> the construction that two already-landed counterexamples have refuted, while route (3)'s
> equivalent obligation has 0 failures across 24,314 machine-checked instances.
> **Recommend route (3).**

The decision does not turn on phase count. It turns on one structural fact, which is the central
finding of this report:

> **Route (3) does not eliminate the hard obligation — it relocates it from a PER-STEP invariant
> to a TERMINAL-LEAF obligation. Every landed counterexample in this task's record refutes the
> obligation at a *transient intermediate* state, and a saturated open branch does not exhibit
> transient states.**

Concretely: the obligation "the redirect target already carries the source's box-positive
content" is `blockedRedirect_boxctx_mem`, which report 02 §2.2 refuted **at step [6] of a
5-step trace, with the note that `b` "is repaired one step later"**. Under route (3) that
obligation is needed only at terminal open leaves. Measured there
(`s4subtractive3.lean`, conditions (b)/(g)): **0 failures out of 24,314 recorded blocking
decisions, across 110,741 terminal open leaves of 80,681 formulas in 3 corpora.**

Three secondary findings that change the plan shape and are cheap wins:

1. **Variant S1 (consume, `.linear []`) vs S2 (withhold, `.notApplicable`) is a real choice.**
   S1 makes `S4LoopInv.outDegEq` **false** (it puts a minting-shaped formula into `e` without an
   edge); S2 preserves it verbatim (no step occurs at all). Both give **byte-identical verdicts**
   on 8,532 formulas. But S1 is the one that can thread the completeness channel, and
   `outDegEq` turns out to have **no consumer in the S4 line** (§5.3), so S1 + dropping
   `outDegEq` is strictly cheaper than S2.
2. **The ordered stepper is mandatory, not optional.** The **unordered** subtractive driver loses
   2 closures on the 1-atom size≤8 corpus (`◇□□(p0→□◇p0)`, `◇□□(◇□p0→p0)`, neither falsifiable
   up to model size 4); the **ordered** one closes both. Any route-(3) plan must be stated against
   `modalStepBranchS4KeyedOrdered`, which — note — has **no landed completeness theorem today**
   (§4.4).
3. **The shipped ORDERED driver already leaves `cex` OPEN** (`s4subtractive3.lean` M1:
   `shipped-unordered=(some true)`, `shipped-ORDERED=(some false)`). The empirical unsoundness is
   already gone; what remains is purely a *proof* problem. This reframes the whole task and is
   the strongest argument against spending further phases on soundness-side heroics.

**One measured obstruction, and how it resolved.** The *wrapped* diamond-negative transfer
`F(◇χ)@src ∈ b → F(◇χ)@wBlock ∈ b` (condition (d)) **fails 40 times out of 24,314**. That looked
like the route-killer. It is not: (d) is only a *proxy*. The obligation the truth lemma actually
carries — the payload correct at every world reachable from `wBlock` in the full augmented
relation `acc ∪ red`, closed under redirect chains — measures **0 failures out of 24,314**
(conditions (F\*)/(G\*), §6.4). The planning consequence is a **statement-shape requirement**, not
a blocker: the diamond-negative Hintikka clause must be stated in the forward-cone form, never in
the wrapped-formula-at-the-target form, which has 40 known counterexamples in this corpus alone.

---

## 1. Reference grounding (H3)

### 1.1 BibKey verification against `references.bib`

| BibKey | `references.bib` line | Verified | Used for |
|---|---|---|---|
| `Massacci2000` | **`references.bib:1010`** | ✅ present | Technique 8.1/8.2, Def. 8.1/8.2, Thm 8.1, Pruning Lemma 8.2, Prop. 8.2, the S4 prefix bound |
| `ChagrovZakharyaschev1997` | `references.bib:75` | ✅ present | canonical-model background (not load-bearing here) |
| `Gore1999` | `references.bib:1023` | ✅ present | named only to record it is **not** the blocker, per dispatch |

No new BibKey needs to be added.

### 1.2 Source-to-implementation mapping

| Source claim | BibKey | Chunk / locus | Lean target | Translation note |
|---|---|---|---|---|
| **Def. 8.1** (*copy*): "σ is a copy of σ′ for branch B if for every formula A, σ : A ∈ B iff σ′ : A ∈ B"; π-completed branch = "for every σ that is not fully reduced there is a fully reduced copy σ₀ **shorter than σ**" | `Massacci2000` §8.1 | `~/Projects/Literature/massacci_2000_single_step_tableaux_for_modal_logics/chunk_0029.md` | no CSLib analogue | Massacci's copy relation is on the **source prefix's own content**. CSLib's guard (`blockingWorldS4Keyed`, `LoopChecking.lean:506-511`) instead compares the **prospective successor's** birth content (`successorBirthContent`, `:384-391`) against a recorded key. **These are different relations** — see §3.3, the single most important literature/implementation divergence in this task |
| **Technique 8.2**: "Before reducing a π-formula, check whether the corresponding prefix is not a copy of a **shorter** prefix. This is exactly the loop-checking method in [8]." | `Massacci2000` §8.1 | `chunk_0030.md` | — | Blocking = **withholding a rule**. Nothing is added: no formula, no world, **no edge**. CSLib instead emits `(.linear [], acc.addEdge sf.label wBlock)` (`LoopChecking.lean:753`, `:757`) |
| Remark: "SST are **proof confluent**. We do not need to backtrack once we find a loop; we leave the 'copies' and focus on other parts of the branch." | `Massacci2000` §8.1 | `chunk_0030.md` | variant **S2** (`.notApplicable`) | Literal justification for the withhold-and-move-on reading measured in §6 |
| **Thm 8.1**: "If the L-tableau … terminates with a π-completed branch, then A is L-satisfiable" | `Massacci2000` §8.1 | `chunk_0030.md` | `modalOpenBranchS4_countermodel` (`FrameCompleteness.lean:401-408`) + `modalTruthLemmaS4` (`FC:232-394`) | Massacci's loop-checking theorem is **completeness-side only**. He carries **no** soundness obligation from blocking, because a blocked branch is a subset of an unblocked one |
| **Def. 8.2** (*modal copy*, "same ν formulae"); "For K4 or S4 Theorem 8.1 can be extended to π-modal-completeness" | `Massacci2000` §8.1 | `chunk_0030.md` | `successorBirthContent` (`LoopChecking.lean:384-391`) | Confirms the box-only key notion is literature-standard — but Massacci's is on the **source**, CSLib's on the **successor** (§3.3) |
| **Pruning Lemma 8.2**: "B is pruned into B∖Ftree(σ.n) … If B is π-completed then B∖Ftree(σ.n) is π-completed" | `Massacci2000` §8 | `chunk_0031.md` | — | The literature's *model* identifies copies; it never records a redirect edge |
| **Prop. 8.2 / Prop. B.5**: "the longest prefix σ on the B′ that can satisfy Proposition B.5 has length `hbL − 1 = 1 + dp + p × n`"; "If every prefix from σ₀ … up to σ₀.n₁…n_k is a modal copy of σ₀, then each σ₀…n_i fulfills a **different** π-formula" | `Massacci2000` §8.2 | `chunk_0065.md:40-56` (the bound at `:48-49`) | *not needed* — see §5 | Massacci's is a **depth** bound resting on the Pruning Lemma. CSLib's `modalWorldBoundS4 = 2^(2·|Sf|)` (`LoopChecking.lean:229`) is a **pigeonhole cardinality** bound on `keys`, and §5 shows it survives route (3) **completely intact**, so Massacci's depth bound is *not* required |

**The load-bearing literature finding of this report** (sharpening report 03 §1's): `Massacci2000`
loop-checking is purely subtractive *and* its copy relation is on the **source** prefix. The
subtractivity is what makes soundness free; the source-side copy relation is what makes the
model construction free. CSLib has neither: it adds an edge (manufacturing a soundness
obligation) and its guard compares successor birth content (so Massacci's model construction does
not transfer verbatim). Route (3) buys the first for free; §3.3/§6 measure whether the second is
recoverable.

---

## 2. What route (3) is, precisely

The change site is `modalApplyOneS4Keyed` (`LoopChecking.lean:747-759`):

```lean
| .neg, .box φ =>
  match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
  | some wBlock => (.linear [], acc.addEdge sf.label wBlock)   -- LoopChecking.lean:753
  | none => modalApplyOne sf b acc
| .pos, .diamond φ =>
  match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
  | some wBlock => (.linear [], acc.addEdge sf.label wBlock)   -- LoopChecking.lean:757
  | none => modalApplyOne sf b acc
```

Route (3) replaces `acc.addEdge sf.label wBlock` with `acc`. **The guard is unchanged.**

Two readings of "withhold the π-rule" exist in CSLib's architecture, and they differ observably:

| Variant | Blocked arm emits | `sf` enters `e`? | `acc` changes? | `S4LoopInv.outDegEq` |
|---|---|---|---|---|
| **S1 (consume)** | `(.linear [], acc)` | **yes** (`LoopChecking.lean:978`, `newExps = e ++ [sf]`) | no | **FALSE** — RHS gains a minting-shaped formula, LHS does not |
| **S2 (withhold)** | `(.notApplicable, acc)` | no (`:982`, `.notApplicable => none`) | no | **preserved verbatim** — neither side moves |

### 2.1 Why soundness becomes trivial — and this is not a hand-wave

Under either variant, a blocked step leaves `b` **and** `acc` unchanged (`e` is not mentioned by
either invariant: `branchSatisfiableIn` at `FrameSoundness.lean:110-118`,
`branchPropAdequateIn` at `:1264-1276`). So the preservation obligation at a blocked step is

```
branchSatisfiableIn s4FC b acc  →  branchSatisfiableIn s4FC b acc
```

discharged by `id`. This is why route (3) works at **full** `branchSatisfiableIn s4FC` strength
and needs no weakening at all. It is also why `Massacci2000` has no soundness obligation from
blocking (`chunk_0030.md`, Thm 8.1 is completeness-side only).

Beyond the blocked arm, the remaining rules are `modalApplyOne` (raw K) and `modalApplyOneS4`,
whose full-strength soundness lemmas are **already landed and sorry-free**:

| Rule arm | Landed full-strength lemma | Frame condition it needs |
|---|---|---|
| `T(□φ)@w` + edge → `T(φ)@w'` (K) | `modalApplyOne_boxPos_sound` (`SoundnessStep.lean:446-459`) | **none at all** — the signature takes `hacc`/`hb` only, no `FC` parameter |
| `F(◇φ)@w` + edge (K, dual) | `modalApplyOne_diaNeg_sound` (`SoundnessStep.lean:~489`) | none |
| `T(□φ)@w → T(φ)@w` (T) | `branchSatisfiableIn_reflFC_boxPos_mem` (`FrameSoundness.lean:973`) | `Std.Refl` |
| `T(□φ)@w` + edge → `T(□φ)@w'` (4) | `branchSatisfiableIn_s4FC_boxPos_trans_mem` (`FrameSoundness.lean:1085-1100`) | **`IsTrans` only** — proof is `htrans.trans` at `:1099`, no `hrefl` use |
| `F(◇φ)@w` + edge → `F(◇φ)@w'` (4, dual) | `branchSatisfiableIn_s4FC_diaNeg_trans_mem` (`:1106-1123`) | **`IsTrans` only** (`:1122`) |
| unblocked mint | `modalApplyOne` (raw K) via the generic crux | none |
| **blocked mint** | *new, trivial* | none |

### 2.2 The reuse asset this unlocks

`FrameSoundness.lean` already contains an **`apply`-parametric soundness ladder**, built for
exactly this shape of problem:

- `modalStepBranchGen_preserves_satIn` (`:195`) — generic over `FC` **and** `apply`, taking three
  per-call hypotheses (`hAgree`/`hBoxPos`/`hDiaNeg`).
- `modalExpandBranchesGen_closed_unsatIn` (`:731`) — the generic fuel induction.
- `S5SoundSpec` (`:2256-2261`) — the *strengthened* per-call contract used when `apply` differs
  from the base rule **at the minting shapes**, which the generic `hAgree` cannot express;
  satisfied by the witness-**reuse** rule `modalApplyOneS5w` (`:2273-2287`).
- `modalStepBranchS5Gen_preserves_satIn` (`:2554`) → `modalExpandBranchesS5Gen_closed_unsatIn`
  (`:3282`) → `modalTableauS5Gen_sound` (`:3317`) → two free instantiations (`:3362`, `:3373`).

Route (3)'s blocked arm is the **degenerate case of exactly this pattern**: where `S5SoundSpec`'s
right disjunct is `apply sf b acc = (.linear [sf'], acc.addEdge sf.label sf'.label)` with
`sf' ∈ b` (a formula *and* an edge to justify), route (3)'s would be
`apply sf b acc = (.linear [], acc)` — **no formula and no edge**. `S5SoundSpec`'s own docstring
states the principle (`:2245-2250`): *"the right disjunct's `sf' ∈ b` is what makes the reuse
edge cheap … This is why witness reuse is structurally easier than minting: no world is created,
so the world-assignment `f` is never extended."* Route (3)'s arm is one step cheaper still.

**Critically**, S5 needed `accReachableInv_related_s5` (`:1858`) — a `rightEuclidean`/symmetry
argument — to justify its reuse *edge*. Route (3) needs no analogue, because there is no edge.
This is precisely the gap report 03 §5 identified as non-transferable to S4, and route (3) is the
one option that does not need it.

---

## 3. Q1 — How much of the landed completeness line breaks

Counts below are from a mechanical declaration-regex parse plus reference-graph BFS over
`LoopChecking.lean` (10,352 lines) and `FrameCompleteness.lean` (4,305 lines), rooted at
`modalTableauS4Keyed_complete`.

### 3.1 The census

- **157** declarations are reachable from `modalTableauS4Keyed_complete` (`FrameCompleteness.lean:4265-4301`).
- **43** of those are S4-keyed-specific, totalling **1,983 source lines** (41 in
  `LoopChecking.lean`, 2 in `FrameCompleteness.lean`).
- **Zero `sorry`** in either file. The whole completeness line is landed.

| Bucket | Decls | Lines |
|---|---|---|
| **NEEDS NEW PROOF** | **4** | **1,036** |
| NEEDS RESTATEMENT | 10 | 186 |
| SURVIVES UNCHANGED | 34 keyed + 7 shared-S4 | 1,188 |
| — of which "survives, mechanical proof edit only" | 4 | 195 |

**By file**, of the 1,036 NEEDS-NEW-PROOF lines: **873 in `LoopChecking.lean`**, **163 in
`FrameCompleteness.lean`**. Nothing in `FrameCompleteness.lean`'s own S4Keyed section
(`FC:4159-4301`, 143 lines) needs a new proof — that section is pure assembly.

### 3.2 The four that need new proofs

| Decl | Locus | Lines | Why it breaks |
|---|---|---|---|
| `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` | `LoopChecking.lean:9006-9340` | **335** | Blocked box-neg (`:9074-9109`) and dia-pos (`:9157-9192`) cases discharge `eBoxNegWitness`/`eDiamondPosWitness` **solely** from the redirect edge: `have hedge : newAcc0.hasEdge sf.label wBlock = true` (`:9092`, `:9175`) then `exact ⟨wBlock, hedge, hwitmem⟩` (`:9105`, `:9192`). Under S1 the field becomes **false**; **under S2 it becomes vacuous** (no step, `sf` never enters `e`) — a real saving |
| `modalExpandBranchesS4Keyed_hintikka` | `LoopChecking.lean:9860-10209` | **350** | Its conclusion's conjuncts 3/4 are discharged at `:10041-10050` by `hHinv.eBoxNegWitness` / `hHinv.eDiamondPosWitness`. Both sources vanish. **Irreducibly needs new work under either variant** |
| `modalStepBranchS4_preserves_outDegEq` | `LoopChecking.lean:4917-5104` | **188** | `outDegEq` (`:7061`) counts minting-shaped formulas in `e` against `outDeg acc`. Blocked S1 step grows `e` but not `outDeg` (proof matches them via `outDeg_addEdge_self_S4` at `:4996`, `:5062`). **FALSE under S1; preserved verbatim under S2; and it has no S4 consumer at all** (§5.3) |
| `modalTruthLemmaS4` | `FrameCompleteness.lean:232-394` | **163** | Box-neg (`:379-382`) and dia-pos (`:385-388`) each need a raw `acc.hasEdge w w'` fed through `extractModelS4_hasEdge_imp_r`. **This is the genuinely new mathematics** |

### 3.3 The entire semantic dependence is 17 lines

Four clauses, and nothing else, assert that an edge *exists*:

| Clause | Locus | Statement |
|---|---|---|
| `modalHintikkaSetS4` conjunct 3 | `LoopChecking.lean:6557-6559` | `∀ φ w, ⟨.neg,.box φ,w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.neg,φ,w'⟩ ∈ b` |
| `modalHintikkaSetS4` conjunct 4 | `:6560-6562` | dual |
| `S4KeyedHintikkaInv.eBoxNegWitness` | `:8756-8759` | `∃ w', acc.hasEdge w w' = true ∧ ⟨.neg,ψ,w'⟩ ∈ b` |
| `S4KeyedHintikkaInv.eDiamondPosWitness` | `:8763-8766` | dual |

Everything else is either edge-**free**, an edge **upper** bound (`accFresh`, `accKnown` — which
get *strictly easier* with fewer edges), or **universally** quantified over paths
(`hintikkaS4_box_pos_reflTransGen` `:6985-6998`, `hintikkaS4_dia_neg_reflTransGen` `:7001-7013`).

### 3.4 The extracted relation, and what replaces it

```lean
-- FrameCompleteness.lean:143-146
def extractModelS4 (b …) (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (Relation.ReflTransGen) b acc
-- FrameCompleteness.lean:87
  r := Cl (fun w w' => acc.hasEdge w w' = true)
```

So `(extractModelS4 b acc).r = Relation.ReflTransGen (fun w w' => acc.hasEdge w w' = true)`
(`extractModelS4_r`, `FC:150-153`, by `rfl`). `s4FC` falls out of the closure regardless of which
edges exist (`extractModelS4_refl` `FC:160-164`, `extractModelS4_trans` `FC:174-178`) — **the
frame-condition half never breaks**, which is a real asset.

**The replacement construction** (this is route (3)'s design, not `Massacci2000`'s verbatim, and
the divergence is deliberate — see §1.2): thread the blocking decisions in a **separate,
completeness-only channel** `red : List (WorldIndex × WorldIndex × Sign × Proposition Atom)`
alongside `keys`, and extract over `ReflTransGen (acc ∪ red)`.

- **Soundness never sees `red`**, because `branchSatisfiableIn`'s edge conjunct quantifies over
  `acc.hasEdge` (`FrameSoundness.lean:113`). So §2.1's triviality is preserved.
- **Completeness sees both**, so conjuncts 3/4 are restated over `(acc ∪ red).hasEdge` and are
  discharged by the threaded record.
- `red` must be **threaded, not recomputed** at the open branch: `successorBirthContent φ₀ b …`
  (`:384-391`) is computed from the *live* `b`, which has grown by then — this is the documented
  staleness defect (`LoopChecking.lean:481-490`).

This is why route (3) is *not* literally `Massacci2000`'s quotient: Massacci's copy relation is on
the **source** prefix's ν-formulas (Def. 8.2, `chunk_0030.md`), so he can fold σ onto σ₀ and
inherit σ₀'s successors. CSLib's guard relates the **prospective successor** to `wBlock`, so the
natural model move is an *edge* `src → wBlock` — kept, but moved out of the soundness-tracked
structure. §6 measures whether that edge is truth-lemma-safe.

---

## 4. Q1 continued — what survives, and one structural surprise

### 4.1 The single most valuable survivor

`modalStepBranchS4Keyed_blocked_witness_mem` (`LoopChecking.lean:8806-8824`, 19 lines) has **zero
`acc`/edge mentions** — it is pure `keys` + `relevantSetFinset` + `successorBirthContent`, and it
still yields `⟨s, φ, wBlock⟩ ∈ b`. That is the *branch-membership* half of the Hintikka witness,
surviving free. Only the *reachability* half is lost, and `red` restores it by construction.

### 4.2 Also surviving free

`blockingWorldS4Keyed` + `_eq_birthContent` + `_none_fresh` (`:506-555`, 40 lines, pure `keys` —
the guard is untouched); `modalExpMeasure_step_lt_S4Keyed` (`:9502-9596`, 95 lines);
`modalExpandBranchesS4Keyed_openBranch_initial_mem` (`:10221-10348`, 128 lines);
`modalStepBranchS4Keyed_branch_superset` (`:2191-2226`); the six
`modalApplyOneS4Keyed_{persistentFresh,branchingLength,outputsSubsetUniverse,nonMint_*}_S4`
bookkeeping lemmas (270 lines); `hintikka_congr_S4` (`:7821-7833`); and all five
`extractModelS4*` lemmas (`FC:143-189`, 23 lines).

### 4.3 `accFresh` / `accKnown` get *easier*

Both are edge **upper** bounds (`accFreshInv`, `SoundnessStep.lean:392`; `accTargetsKnown`,
`FmpMeasure.lean:1891`). Fewer edges ⟹ strictly weaker obligation.

### 4.4 The structural surprise: the landed completeness line is for the **plain** driver

`modalTableauS4Keyed_complete` (`FC:4265`) unfolds (`FC:4271-4274`) to
`modalExpandBranchesS4Keyed` (`LoopChecking.lean:7647-7696`), which calls
**`modalStepBranchS4Keyed`** at `:7685` — the *unordered* stepper. The whole ordered family
(`modalStepBranchS4KeyedOrdered` `:1107`, `modalExpandBranchesS4KeyedOrdered` `:7739`,
`modalTableauS4KeyedOrdered` `:7800`, plus 27 `_preserves_*` lemmas and
`modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` `:7576`) is **entirely absent from the BFS
closure**: 30 of the 73 `S4Key`-named declarations in `LoopChecking.lean` are unreachable, all of
them `…Ordered…`. `LoopChecking.lean:7727-7729` says so plainly.

**Planning consequence, and it cuts both ways.** §6 shows route (3) *requires* the ordered
stepper (the unordered subtractive variant loses 2 closures). So route (3)'s completeness work
lands against a driver that has **no** completeness theorem today — meaning the 1,036 "needs new
proof" lines are not a *regression* against a landed asset for the ordered driver; they are the
first completeness proof that driver will ever have. Conversely, the plain driver's landed
completeness theorem is not *lost* by route (3) either, since route (3) should be introduced as a
**parallel definition** (`modalApplyOneS4KeyedSub` etc.), exactly the convention this file already
uses twice (`:459-464`, `:992-996`).

---

## 5. Q2 — Does TERMINATION survive? **YES, intact.**

This is the item two prior routes died on, so it is argued three ways: structurally, by
consumer-tracing, and by measurement.

### 5.1 The world bound is edge-independent

`modalWorldBoundS4 φ₀ = 2 ^ (2 * |modalSubfmls φ₀|)` (`LoopChecking.lean:229`). The pigeonhole
argument `modalKnownWorlds_length_le_worldBoundS4` (`:6459`) injects known worlds into
`powerset (signedSubfmls φ₀)` via their birth keys, consuming exactly three `S4LoopInv` fields:

| Field | Locus | Mentions `acc`? |
|---|---|---|
| `keysTotal` | `:7063` | no |
| `keyLowerBd` | `:7068` | no |
| `keysDistinct` | `:7073` | no |
| `keysInUniverse` | `:7076` | no |

**None mentions `acc`.** And `keysDistinct`'s sole establisher is
`blockingWorldS4Keyed_none_fresh` (`:538`), a statement about the **guard**, which route (3) does
not touch. So the entire chain guard → `keysDistinct` → world bound → `bClosure` →
`modalUniverseS4` → `modalExpMeasure_entry_le_fuelS4` (`:8486`) is **untouched**.

Contrast this with the two routes report 02 §4 rejected on exactly this chain: R3 (guard side
condition) "collapses: guard → `keysDistinct` → world bound → branch closure → fuel sufficiency",
and the reachability restriction was rejected in report 01 because 96.7% of blocking decisions
target non-reachable worlds. **Route (3) changes the guard's *effect*, never its *decision*, so
it is the one repair that leaves this chain alone.**

### 5.2 The step measure is edge-independent

`modalExpMeasure_step_lt_S4Keyed` (`:9502-9520`) takes hypotheses
`hb`/`hknown`/`hWC`/`hKT`/`hKD`/`hKI` — bClosure, `accTargetsKnown`, `worldsContiguousS4`, and the
three keys fields. **It does not take `outDegEq`.** Under S1 the blocked case still grows `e`
(the measure's decrease witness); under S2 no step occurs, so the measure is not invoked.

### 5.3 `outDegEq` has no S4 consumer — verified

`grep` for `.outDegEq` in `LoopChecking.lean` returns **only** the two sites where it is
*provided* (`:7546` in `modalStepBranchS4_preserves_S4LoopInv`, `:7610` in the ordered analogue).
`outDeg_le_of_expandedNodup` (`FmpMeasure.lean:1624`) is consumed at exactly one place,
`FmpMeasure.lean:2506`, inside `modalStepBranch_potential_step_gen` (`:2360`) — K's generic
potential ladder, which the S4 measure (§5.2) does not route through.

**Therefore `outDegEq` can be dropped from `S4LoopInv` outright**, deleting the 188-line
`modalStepBranchS4_preserves_outDegEq` obligation rather than re-proving it, and removing the
S1-vs-S2 tension. *Confidence: high on the "no current consumer" fact (mechanical); medium on
"never needed" — a future out-degree-driven fuel argument for #511 Phase 9 could want it back,
though the landed S4 measure is world-bound-driven, not out-degree-driven.*

### 5.4 Massacci's depth bound is **not** required

`Massacci2000`'s own S4 prefix bound `hbL − 1 = 1 + dp + p × n` (`chunk_0065.md:48-49`) rests on
Proposition 8.2 and the Pruning Lemma (`chunk_0031.md`). It would be needed only if CSLib's
pigeonhole bound were lost — i.e. only under a *guard* change (Massacci's Def. 8.2 source-copy
guard). Since route (3) keeps CSLib's guard, **§5.1's pigeonhole bound is retained and Massacci's
depth bound is dead weight.** This is the one place where diverging from the literature is the
correct engineering call, and it is why route (3)-narrow is much cheaper than a faithful port.

### 5.5 Measured

From `s4subtractive.lean` (2 atoms, size ≤ 6, 8,532 formulas, fuel 100):

| Driver | max recorded worlds | max DFS depth | max out-degree | max edges | formulas where `keysDistinct` breaks |
|---|---|---|---|---|---|
| shipped keyed (baseline) | 8 | 31 | 3 | 18 | **0 / 8532** |
| subtractive S1 (ordered) | 7 | 22 | 2 | 6 | **0 / 8532** |
| subtractive S2 (ordered) | 7 | 16 | — | — | **0 / 8532** |

Fuel exhaustion, all three: **0**. On the 1-atom size ≤ 8 corpus (95,730 formulas) the shipped
driver exhausts fuel 100 on **2** formulas and subtractive on **0** — subtractive terminates
*strictly better*. (Per-formula, S1 exceeds baseline's world count on 6 formulas and depth on 112;
the *bound* is unaffected, since it depends only on `keysDistinct`.)

**Verdict on Q2: termination survives, with the pigeonhole bound retained verbatim and one field
(`outDegEq`) droppable rather than re-provable. Route (3) does not die here.**

---

## 6. Q3 — Empirical measurement

All numbers are verbatim `#eval` output. Reproduce with
`lake env lean specs/553_.../artifacts/s4subtractive{,2,3}.lean`.

### 6.1 An independent semantic validity oracle (new instrument)

`s4subtractive.lean` builds a direct `Bool` evaluator over **all** reflexive-transitive frames of
size ≤ N with all valuations (`falsifiableUpTo`), independent of the tableau machinery.
Validation:

```
E0: oracle(cex)=(some 3) (expect some 3)   oracle(T)=none  oracle(4)=none  oracle(K)=none
```

`cex`'s least countermodel size is **3**, matching the 3-world countermodel spelled out in
`blockingWorldS4Keyed`'s own docstring (`LoopChecking.lean:473-476`) exactly. T/4/K are not
falsifiable. **The oracle is calibrated.**

### 6.2 (A) soundness and (B) validity

```
A: baseline(cex,400)=(some true)  S1-unord=(some false)  S1-ord=(some false)
                                  S2-unord=(some false)  S2-ord=(some false)
B: T   base=(some true) S1u=(some true) S1o=(some true) S2u=(some true) S2o=(some true)
B: 4   base=(some true) S1u=(some true) S1o=(some true) S2u=(some true) S2o=(some true)
B: K   base=(some true) S1u=(some true) S1o=(some true) S2u=(some true) S2o=(some true)
```

(A) **PASS** — `cex` (node-size 19) is OPEN under all four subtractive variants; the baseline
closes it. (B) **PASS** — T, 4, K all CLOSED under all four.

### 6.3 (C) differential sweep — three corpora, 159,561 formulas

| Corpus | formulas | baseline (closed/open/fuel) | subtractive S1 (closed/open/fuel) | `open→closed` (**must be 0**) | `closed→open` | guard FIRED on | max redirects on one path |
|---|---|---|---|---|---|---|---|
| 2 atoms, size ≤ 6 | 8,532 | **1650 / 6882 / 0** ✅ matches the established baseline exactly | 1650 / 6882 / 0 | **0** | **0** | 915 | 11 |
| 2 atoms, size ≤ 7 | 55,299 | 11802 / 43497 / 0 | 11802 / 43497 / 0 | **0** | **0** | 7,011 | 28 |
| 1 atom, size ≤ 8 | 95,730 | 27024 / 68704 / **2** | 27022 / 68708 / **0** | **0** | **2** | 15,256 | 39 |

**The guard is not vacuous**: it fires on **23,182** formulas across the three corpora.
`open→closed` — the completeness-regression trigger — is **0 everywhere**. Also on the 2-atom
size ≤ 6 corpus: S1 vs S2 verdict disagreements = **0**; oracle cross-checks:
baseline-closed with a size ≤ 2 countermodel = 0/1650, S1-closed = 0/1650, S2-closed = 0/1650;
baseline-open with no size ≤ 3 countermodel = 0/6882, S1-open = 0/6882.

**Adjudicating the four deeper-corpus disagreements** (all from 1 atom, size ≤ 8), by oracle:

| Formula | least countermodel (≤ 4) | shipped | subtractive **unordered** | subtractive **ordered** | reading |
|---|---|---|---|---|---|
| `◇□◇□◇□◇⊥` | **1** (invalid) | fuel-exhausted | open | open | subtractive TERMINATES where shipped does not, and gives the correct verdict |
| `◇□◇□◇□◇p0` | **1** (invalid) | fuel-exhausted | open | open | same |
| `◇□□(p0→□◇p0)` | **none** | closed | **open** | **closed** | **unordered subtractive loses completeness; ordered does not** |
| `◇□□(◇□p0→p0)` | **none** | closed | **open** | **closed** | same |

This is the evidence behind finding (2) in the verdict: **the ordered stepper is mandatory.**
With it, `closed→open` is 0 on all three corpora and the only differences are two
fuel-exhaustions the subtractive driver *fixes*.

### 6.4 The decisive completeness-recoverability measurement

`s4subtractive3.lean` runs the **ordered** subtractive driver over each corpus and, at **every
terminal open leaf** (not just the first — the DFS deliberately visits all of them, since
completeness must hold at each), tests the recorded `red` entries against the conditions the
`ReflTransGen (acc ∪ red)` truth lemma needs:

| Condition | statement | 2 atoms ≤6 | 1 atom ≤7 | 2 atoms ≤7 |
|---|---|---|---|---|
| leaves visited / redirects recorded | | 11,139 / 1,652 | 21,750 / 6,303 | 77,852 / 16,359 |
| **(a)** witness | `⟨s,ψ,wBlock⟩ ∈ b` | **0** | **0** | **0** |
| **(b)** box wrapped | `T(□χ)@src → T(□χ)@wBlock` | **0** | **0** | **0** |
| **(c)** box unwrapped | `T(□χ)@src → T(χ)@wBlock` | **0** | **0** | **0** |
| **(d)** dia wrapped | `F(◇χ)@src → F(◇χ)@wBlock` | **0** | **16** | **24** |
| **(e)** dia unwrapped | `F(◇χ)@src → F(χ)@wBlock` | **0** | **0** | **0** |
| **(g)** *exact* box obligation | `T(□χ)@src → T(χ)@u` ∀u `acc`-reachable from `wBlock` | **0** | **0** | **0** |
| **(f)** *exact* dia obligation | `F(◇χ)@src → F(χ)@u` ∀u `acc`-reachable from `wBlock` | **0** | **0** | **0** |
| **(G\*)** FULL box obligation | `T(□χ)@src → T(χ)@u` ∀u reachable in **`acc ∪ red`** | **0** | **0** | **0** |
| **(F\*)** FULL dia obligation | `F(◇χ)@src → F(χ)@u` ∀u reachable in **`acc ∪ red`** | **0** | **0** | **0** |
| redirects whose source already had a genuine `acc` successor witness | | 24 | 253 | 490 |

**Condition (b) is the load-bearing one and it has 0 failures out of 24,314 recorded redirects.**
(b) is literally the conclusion of `blockedRedirect_boxctx_mem`, which report 02 §2.2 proved
**FALSE** — but *at a transient intermediate state* (step [6] of a 5-step trace, with report 02's
own note that the same pattern has `b` "repaired one step later"). At **terminal, saturated** open
leaves (110,741 of them) the transient gap is closed, which is exactly the relocation described in the verdict.

**Condition (d)'s 40 failures are real, and were initially reported here as the one live
obstruction. Measuring the *exact* obligation dissolved them.** (b)-(e) are only *proxies*: what
`modalTruthLemmaS4` actually needs is that the propagation payload of `src` is already correct at
every world reachable **from** `wBlock`, not that a particular wrapped formula sits at `wBlock`.
Conditions (g)/(f) state exactly that over `acc`-reachability, and (G\*)/(F\*) state it over the
full augmented relation `acc ∪ red` — i.e. closed under **chains of redirects**, which certainly
occur (up to 39 recorded redirects on one path, §6.3). All four measure **0 failures**.

The (d) failures are consistent with this: in every printed instance the *unwrapped* form is
present (`unwrappedAlsoMissing=[]`) and the missing wrapped formula is `F(◇χ)` for a **non-modal**
`χ`, for which no further propagation is needed at all:

```
C7.1: (d)-failure example: φ₀=◇(□⊥∧□◇⊥)   src=2 wBlock=1 unwrappedAlsoMissing=[] wrappedMissing=[⊥, ⊥]
C7.1: (d)-failure example: φ₀=◇(□⊥∨□◇⊥)   src=2 wBlock=1 unwrappedAlsoMissing=[] wrappedMissing=[⊥, ⊥]
C7.1: (d)-failure example: φ₀=◇(□p0∧□◇p0) src=2 wBlock=1 unwrappedAlsoMissing=[] wrappedMissing=[p0, p0]
```

**Planning consequence:** the diamond-negative Hintikka clause must be stated in the (F\*) form
(payload correct throughout the target's forward cone), **not** in the (d) form (wrapped formula
present at the target). Stating it as (d) would be stating a lemma with 40 known counterexamples
in this corpus alone.

---

## 7. Q4 — Honest effort comparison: route (3) vs route (2′)

Both are priced on the same scale: phases sized per H8 (one agent run, ~100-500 lines output).

### 7.1 Route (2′): the disjunctive edge conjunct

Target: `branchPropAdequateIn` with
`∀ w w', acc.hasEdge w w' → (m.r (f w) (f w')) ∨ (propagation-adequacy clause)` (report 03 §7.1,
from report 02 §5.1).

| # | Phase | Lines | Risk |
|---|---|---|---|
| 1 | Restate the invariant disjunctively; re-prove the 7 landed lemmas (`FrameSoundness.lean:1284`, `:1322`, `:1356`, `:1391`, `:1413`, `:1443`, `:1481`) against it | ~250 | Low — report 03 §7.1 shows both implications |
| 2 | Repair §5.1: `hready` on **plain mint-edge chains** (`0→1`, `1→2`, late `T(□ψ)@0`) | ~150 | Medium |
| 3 | **Preservation across REDIRECT steps** | ? | **HIGH — see below** |
| 4 | Fuel induction + soundness capstone | ~300 | Low (S5 template at `:3116-3373`) |
| 5 | `s4Valid_decides` + `instDecidableS4Valid` | ~120 | Low |
| | **Total** | | **7-8 phases *if* phase 3 closes** |

**Why phase 3 is the problem, cited.** At a redirect step the new edge takes one of two disjuncts,
and **both have landed refutations**:

- **Left disjunct** `m.r (f src) (f wBlock)`: plan v3 `#### Phase 2 Verdict` —
  *"an arbitrary `branchSatisfiableIn` witness need not have `m.r (f src) (f a)`, and extending
  `m.r` to add it (forced to close transitively, since `IsTrans` binds the concrete relation)
  requires box/diamond content transfer for every ambient predecessor of `f src`"*. This is the
  `sorry` at `FrameSoundness.lean:1244`, and the docstring at `:1215-1219` calls it *"the one case
  genuinely not dischargeable from these hypotheses"*.
- **Right disjunct** (propagation adequacy at the redirect target): report 02 §3.1 row 6,
  **CONFIRMED**: a 4-world model `W={a0,a1,a2,a3}`, `r` = refl-trans of
  `{(a0,a1),(a0,a2),(a1,a3)}`, `p` false at `a3`, *"satisfies the branch and all `acc` edge
  conjuncts … but **falsifies `□p` at `f 1`**. `blockedRedirect_propAdequate` … discards the
  ambient edge conjunct and reuses the ambient `m`, so it cannot recover."*

Report 02 is careful (and correct) that this refutes the *proof strategy*, not the invariant — the
invariant does hold at that state (row 5: a 3-world model exhibits it). **But that is exactly the
bad news**: preservation across a redirect step is true-but-requires-constructing-a-new-model, and
it must be constructed **at every intermediate state inside the fuel induction**, over an
existentially arbitrary ambient witness. That is truth-lemma-scale work performed
*n* times instead of once — i.e. route (2′)'s phase 3 is not cheaper than route (1); it is
route (1)'s cost, relocated inside an induction, with the extra burden of arbitrary ambient
predecessors. Report 03 rates this "**Unknown** — the load-bearing open question, not asserted".

### 7.2 Route (3): subtractive blocking + completeness-only redirect channel

| # | Phase | Lines | Risk |
|---|---|---|---|
| **1** | **Statement-shape design phase.** Fix the restated Hintikka clauses in the forward-cone form (F\*)/(G\*) (§6.4), NOT the wrapped form (d), which has 40 measured counterexamples. Deliverable: the exact restatements of `modalHintikkaSetS4` conjuncts 3/4 and the two `S4KeyedHintikkaInv` witness fields, plus the `red` channel's type | ~60 | Low-medium — the shape is measured, the Lean statement is not yet written |
| 2 | Parallel definitions `modalApplyOneS4KeyedSub` / `modalStepBranchS4KeyedSubOrdered` threading `red`; restate the 2 blocked-`eq` spec lemmas (`:763-770`, `:785-793`) | ~150 | Low — mechanical; the file already does parallel-definition twice (`:459-464`, `:992-996`) |
| 3 | `S4LoopInv` for the subtractive driver: 9 fields transfer (`accFresh`/`accKnown` get easier); **drop `outDegEq`** (§5.3) | ~200 | Low |
| 4 | World bound + `bClosure` + measure step: transcription (guard unchanged ⟹ `keysDistinct`/`keyLowerBd`/`keysInUniverse` identical) | ~200 | Low — §5.1/§5.2 |
| 5 | **Soundness capstone at full `branchSatisfiableIn s4FC`**: an `S4SoundSpec` analogue of `S5SoundSpec` (`:2256`) whose blocked disjunct is `apply sf b acc = (.linear [], acc)`; per-step preservation; fuel induction; `modalTableauS4KeyedSub_sound`. **This is the phase that retires the `sorry` at `:1244`** | ~400 | **Low** — §2.1 triviality + the landed `modalStepBranchGen_preserves_satIn` / S5Gen ladder |
| 6 | Restate `modalHintikkaSetS4` conjuncts 3/4 and `S4KeyedHintikkaInv`'s two witness fields over `(acc ∪ red)` (17 lines of statement, 10 decls / 186 lines of follow-on) | ~200 | Low-medium |
| 7 | `extractModelS4Sub` over `ReflTransGen (acc ∪ red)` + refl/trans instances + `modalTruthLemmaS4Sub` | ~250 | **Medium** — the genuinely new mathematics (§3.2, `FC:232-394`) |
| 8 | `modalExpandBranchesS4KeyedSub_hintikka` (analogue of `:9860-10209`) | ~350 | Medium |
| 9 | `modalTableauS4KeyedSub_complete` + `s4Valid_decides` + `instDecidableS4Valid` | ~120 | Low |
| | **Total** | ~1,870 | **9 phases** |

### 7.3 Side-by-side

| Axis | Route (2′) | Route (3) |
|---|---|---|
| Phases | 7-8 | 9 |
| Soundness target | weakened (disjunctive) | **full `branchSatisfiableIn s4FC`** |
| Landed completeness | preserved | 4 decls / 1,036 lines re-proved (but for a driver that has **no** completeness theorem today, §4.4) |
| Termination | untouched | **untouched** (§5), plus one field droppable |
| Retires the `:1244` `sorry`? | no — it *is* the left disjunct of its phase 3 | **yes**, in phase 5 |
| Load-bearing obligation | per-step, over an arbitrary ambient model, at every intermediate state | **terminal open leaves only** |
| Status of that obligation | **both disjuncts have landed refutations of the available proof strategy** (§7.1) | **0 failures / 24,314 instances** (§6.4), with 40 localised (d)-failures to settle in phase 1 |
| Literature support | none — invented for this task | `Massacci2000` Tech. 8.2, Thm 8.1, Def. 8.2, Pruning Lemma 8.2 |
| Reuse template in-repo | S5 fuel induction | S5Gen `apply`-parametric ladder **including a minting-shape-divergent `apply`** (`S5SoundSpec`, `:2256-2287`) |
| #548 risk | **live** (§8) | **dissolved** (§8) |

Route (3) is ~1-2 phases more expensive and buys: full-strength soundness, retirement of the only
`sorry` in the directory, a literature-backed construction, and — decisively — an obligation that
measures clean instead of one that has been refuted twice.

---

## 8. Q5 — Does route (3) dissolve the #548 risk? **YES.**

Report 03 §6.1 identified one genuine risk in route (2′): `branchPropAdequateIn_boxPos_mem`
(`FrameSoundness.lean:1443-1454`) recovers the unwrapped `φ` at the edge target using `s4FC`'s
**reflexive** half:

```lean
have hboxw' : Satisfies m (f w') (.box φ) := (hedgeconj w w' hedge).1 φ hmem
have hsatw' : Satisfies m (f w') φ := hboxw' (f w') (hFC.1.refl (f w'))   -- :1454
```

That blocks #548's transitive-but-**not**-reflexive corners (K4, K45, D4, D45).

**Under full `branchSatisfiableIn s4FC` the reflexivity dependence disappears entirely**, verified
by reading the full-strength analogues:

| Lemma | Locus | Frame condition actually used |
|---|---|---|
| `modalApplyOne_boxPos_sound` (K box-positive along an edge) | `SoundnessStep.lean:446-459` | **none** — the signature has no `FC` parameter at all; `FrameCompleteness.lean:1102` describes it as *"`modalApplyOne_boxPos_sound` (K, `FC` unused)"* |
| `branchSatisfiableIn_s4FC_boxPos_trans_mem` (4-rule) | `FrameSoundness.lean:1085-1100` | `htrans.trans` only (`:1099`). `hrefl` is destructured (`:1092`) and **never used** |
| `branchSatisfiableIn_s4FC_diaNeg_trans_mem` (4-rule dual) | `:1106-1123` | `htrans.trans` only (`:1122`) |

The full-strength edge conjunct hands you `m.r (f w) (f w')` directly, so the box is unwrapped by
*applying* it to the target — no `Std.Refl` needed, and no `hready` side hypothesis either
(compare `:1449-1450`, which exists **only** because the weak conjunct delivers `□φ` rather than
an edge).

Reflexivity remains needed for the **T-rule** itself (`branchSatisfiableIn_reflFC_boxPos_mem`,
`:973`) — but that is intrinsic to T/S4 and simply absent from K4/D4's rule set. So a K4 corner
reusing the subtractive mechanism instantiates `modalApplyOne_boxPos_sound` (FC-free) plus the
4-rule lemmas (`IsTrans`-only) and needs no reflexivity anywhere.

**Route (3) dissolves the #548 risk completely.** This is a strict advantage over route (2′),
where report 03 rated the risk "real but deferred and routable".

---

## 9. Decision table and verdict

| Route | Soundness target | Termination | Landed completeness | Load-bearing obligation | Status of that obligation | Phases |
|---|---|---|---|---|---|---|
| **(1)** full truth lemma pinning the witness model | full | untouched | preserved | build a canonical/pinned witness model | large, unattempted | 10+ |
| **(2)** accept `branchPropAdequateIn` | weak | untouched | preserved | per-step preservation | §5.1 `hready` defect **unresolved on plain mint chains** | 6-7 |
| **(2′)** disjunctive edge conjunct | middle | untouched | preserved | per-step preservation across redirect steps | **both disjuncts' proof strategies refuted by landed counterexamples** (plan v3 Phase 2 Verdict; report 02 §3.1 row 6) | 7-8 |
| **(3)** subtractive blocking + completeness-only `red` channel | **full, trivially** (§2.1) | **untouched, `outDegEq` droppable** (§5) | 4 decls / 1,036 lines re-proved; for a driver with no landed completeness theorem today (§4.4) | terminal-open-leaf payload transfer | **exact obligation (F\*)/(G\*): 0 failures / 24,314**, closed under redirect chains; the wrapped proxy (d) fails 40/24,314 and must not be the statement form (§6.4) | **9** |

### Verdict

**Route (3) is VIABLE and costs approximately 9 phases, versus route (2′)'s 7-8 — recommend
route (3)**, because:

1. **Soundness closes at full strength for free, not by weakening** — a blocked step is the
   identity on `(b, acc)` (§2.1), and the remaining arms have landed, sorry-free, full-strength
   lemmas (§2.1 table). This retires `FrameSoundness.lean:1244`, the only `sorry` in the
   directory, in phase 5.
2. **Termination survives intact** (§5): the pigeonhole chain guard → `keysDistinct` → world bound
   is edge-independent and the guard is unchanged; `modalExpMeasure_step_lt_S4Keyed` does not take
   `outDegEq`; measured `keysDistinct` breakage 0/8532 and fuel exhaustion 0 (vs the baseline's 2
   on the 1-atom ≤8 corpus). Massacci's depth bound (`chunk_0065.md:48-49`) is **not** needed.
3. **The empirical behaviour is preserved exactly** (§6): `cex` OPEN, T/4/K CLOSED,
   `open→closed` = 0 and `closed→open` = 0 across 159,561 formulas on three corpora, with the
   guard firing on 23,182 of them, and two baseline fuel-exhaustions *fixed*.
4. **The obligation is relocated, not eliminated — and the relocation is the whole point.**
   Route (2′)'s obligation is per-step over an arbitrary ambient model and has landed refutations
   of both available strategies (§7.1). Route (3)'s is terminal-leaf-only, and both halves of it
   measure **0 failures out of 24,314** in the form the truth lemma actually needs — including its
   box half, which is literally the conclusion of the removed `blockedRedirect_boxctx_mem`
   (§6.4).
5. **It dissolves the #548 reflexivity risk** (§8), which route (2′) carries.
6. **It is literature-backed** (`Massacci2000` Tech. 8.2 / Thm 8.1 / Def. 8.2 / Pruning Lemma 8.2,
   BibKey verified at `references.bib:1010`), where route (2′)'s disjunctive conjunct is invented
   for this task.

**Mandatory conditions on the recommendation** — a plan that omits any of these is not the route
priced here:

- **The Hintikka clauses must be stated in the forward-cone form** (F\*)/(G\*), §6.4. The
  wrapped-formula-at-the-target form (d) has **40 measured counterexamples** in this corpus and
  must not be written down. Phase 1 exists to fix these statements before any proof is attempted;
  if the forward-cone form cannot be made to feed `modalTruthLemmaS4`, route (3) is **not** viable
  and the honest fallback is route (1), not (2′).
- **The ordered stepper is mandatory** (§6.3): the unordered subtractive driver loses 2 closures.
- **Introduce the subtractive driver as a parallel definition**, per this file's own convention
  (`LoopChecking.lean:459-464`, `:992-996`), so the landed
  `modalTableauS4Keyed_complete` stays green throughout.
- **No `sorry`, no axiom, no vacuous definition** anywhere in the plan; if a phase cannot close,
  it ends `[BLOCKED]` with the goal state recorded.

---

## 10. Adversarial Self-Verification (H4)

I tried hardest to refute my own conclusion — that route (3) is viable and preferable — by
building the strongest case that termination or completeness breaks.

| Claim | Source / attempted counterexample | Verdict |
|---|---|---|
| Soundness at a blocked step is trivial | Blocked arm leaves `b` and `acc` unchanged; neither invariant mentions `e` (`FrameSoundness.lean:110-118`, `:1264-1276`). *Attempted refutation:* find an invariant conjunct that reads `e` — there is none | **CONFIRMED.** Preservation is `id` |
| **Attempted refutation: `outDegEq` breaks, killing termination** | `S4LoopInv.outDegEq` (`LoopChecking.lean:7061`) counts minting-shaped formulas in `e` against `outDeg acc`. Under variant S1 the blocked step grows `e` (`:978`) but not `outDeg` ⟹ the field is **FALSE**, not merely unproven | **UPHELD as a defect, but NOT fatal.** Two independent escapes, both verified: variant S2 preserves it verbatim (no step occurs, `:982`); and `grep` shows `.outDegEq` is *provided* at `:7546`/`:7610` and **consumed nowhere** in the S4 line, while `modalExpMeasure_step_lt_S4Keyed` (`:9502-9520`) does not take it. **This was the strongest termination attack I could build and it does not close** |
| The pigeonhole world bound survives | `keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse` (`:7063-7076`) mention no `acc`; `keysDistinct`'s sole establisher `blockingWorldS4Keyed_none_fresh` (`:538`) is about the **guard**, which route (3) does not change | **CONFIRMED**, and independently corroborated by measurement (`keysDistinct` breakage 0/8532) |
| **Attempted refutation: completeness has no replacement construction at all** | The only surviving witness asset `modalStepBranchS4Keyed_blocked_witness_mem` (`:8806-8824`) gives `⟨s,ψ,wBlock⟩ ∈ b` but **nothing about reachability**; with the edge gone, `ReflTransGen (acc.hasEdge)` gives a blocked `w` no successor, so by `ReflTransGen.cases_head` the only path from `w` is reflexive, demanding `F(ψ)@w ∈ b` — unavailable | **UPHELD for *pure* subtractive blocking.** This kills the naive reading of route (3) and is why §3.4's design threads a **separate completeness-only channel** rather than merely deleting the edge. **The report's recommendation is for the channel design, not the naive one** — and this row is why |
| **Attempted refutation: the channel design just moves report 02's FALSE lemma to the completeness side** | Route (3)'s condition (b) *is* `blockedRedirect_boxctx_mem`'s conclusion, which report 02 §2.2 proved FALSE with every hypothesis holding | **REFUTATION FAILED, on a stated structural ground plus measurement.** Report 02's refutation is at a **transient intermediate** state (step [6] of 5; report 02 §5.1 notes the same pattern has `b` "repaired one step later"). Route (3) needs it only at **terminal saturated** leaves. Measured there: **0 failures / 24,314 redirects / 110,741 open leaves / 3 corpora**, and the same 0 for the chain-closed (F\*)/(G\*) form. This is the single most decision-relevant measurement in the report |
| **Attempted refutation: the diamond-negative half breaks** | `s4subtractive3.lean` condition (d): **16/6303** (1 atom ≤7), **24/16359** (2 atoms ≤7), 0/1652 (2 atoms ≤6). This is a real failure of a real statement | **UPHELD against the PROXY, REFUTED against the OBLIGATION.** (d) is not what the truth lemma needs. The exact obligations (g)/(f) over `acc`-reachability, and (G\*)/(F\*) over the full `acc ∪ red` relation — closed under redirect **chains**, which occur up to 39 deep — all measure **0 failures / 24,314**. So the failure is in my proxy statement, not in the construction. **Recorded as a statement-shape constraint (§9), because writing the clause in the (d) form would be writing a lemma with 40 known counterexamples** |
| Route (2′) is cheaper | Report 03 §8 rates (2′) the evidence-supported route | **MY OWN PRIOR QUALIFIED / REVERSED.** Report 03's own §7.1 flags (2′)'s redirect-step preservation as "**Unknown** … not asserted". Reading the two landed refutations together (plan v3 Phase 2 Verdict for the left disjunct; report 02 §3.1 row 6's 4-world model for the right disjunct's proof strategy) shows (2′)'s phase 3 requires constructing a new witness model **inside the fuel induction, at every intermediate state** — route (1)'s cost, paid *n* times. Its 7-8 phase count is therefore not comparable to route (3)'s 9 |
| Route (3) preserves empirical behaviour | 3 corpora, 159,561 formulas, `open→closed` = 0 everywhere; `cex` OPEN; T/4/K CLOSED; oracle-validated | **CONFIRMED, with one correction to my own first reading**: the **unordered** subtractive driver loses 2 closures (`◇□□(p0→□◇p0)`, `◇□□(◇□p0→p0)`, neither falsifiable to size 4). Only the **ordered** variant is clean. Promoted to a mandatory condition (§9) |
| The #548 reflexivity risk dissolves | `modalApplyOne_boxPos_sound` (`SoundnessStep.lean:446-459`) has **no `FC` parameter**; `:1085-1100` and `:1106-1123` use `htrans.trans` only, with `hrefl` destructured and unused | **CONFIRMED** |
| The guard fires on the sweep corpus (so verdict agreement is informative) | Exact classification: a blocked step is the unique case where `acc.edges` grows while `keys.length` does not (`LoopChecking.lean:753`/`:757` vs `:971`/`:975`). Fires on **915 / 15,256 / 7,011** formulas | **CONFIRMED** — the measurement is not vacuous. *This check was added because without it the 0-disagreement result would have been worthless* |
| The semantic oracle is trustworthy | `oracle(cex) = some 3`, matching the 3-world countermodel in `blockingWorldS4Keyed`'s docstring (`:473-476`); `oracle(T/4/K) = none` | **CONFIRMED (calibrated).** Limitation stated: `none` means "no countermodel up to size N", **not** a validity proof |
| Massacci's depth bound is needed for termination | `chunk_0065.md:48-49` gives `hbL−1 = 1+dp+p×n`, resting on Prop. 8.2 + the Pruning Lemma. But it is only needed if the pigeonhole bound is lost, which requires a **guard** change | **REFUTED as a requirement.** Route (3) keeps the guard, so `modalWorldBoundS4` (`:229`) is retained and Massacci's bound is dead weight |
| **Attempted refutation: route (3) is really Massacci's route, so CSLib's guard must be replaced by Def. 8.2, dragging in the whole depth-bound apparatus** | `Massacci2000` Def. 8.2 (`chunk_0030.md`) blocks when the **source** σ is a modal copy of a shorter σ₀ whose same π-formula is already reduced. CSLib's guard (`:506-511`) compares the **prospective successor's** birth content (`:384-391`). These are **different relations**, so Massacci's copy-folding model does not transfer verbatim | **UPHELD as a genuine literature/implementation divergence** (§1.2, §3.4) — and it is the reason route (3) needs the `red` channel rather than a quotient. **Reported as a divergence, not papered over.** A faithful Def. 8.2 port would be strictly more expensive (new guard ⟹ new termination argument ⟹ Massacci's depth bound), so the divergence is the correct engineering call, but it means route (3) is *literature-guided*, not *literature-transcribed* |
| The `Gore1999` gap is the blocker | Treated as settled per dispatch; independently, plan v3 records the escalation branch does not apply | **CONFIRMED settled.** No literature-acquisition phase proposed |

### Claims modified or reversed by this pass

1. **The recommendation reversed report 03's.** Report 03 §8 named (2′) "evidence-supported";
   reading its own "Unknown" rating together with the two landed refutations (§7.1) shows (2′)'s
   critical phase is route (1)'s cost paid inside an induction. Route (3) is now recommended.
2. **"Route (3) = delete the edge" was refuted and replaced.** Pure subtractive blocking has no
   completeness construction (row 4). The recommendation is the *completeness-only channel*
   design (§3.4), which is a deliberate divergence from `Massacci2000`.
3. **"S1 or S2, doesn't matter" was refuted.** They differ on `outDegEq` (false vs preserved).
   Resolved by the stronger finding that `outDegEq` has no S4 consumer and can be dropped.
4. **"Any subtractive variant preserves behaviour" was refuted by measurement.** The unordered
   variant loses 2 closures; the ordered one does not.
5. **Condition (d)'s 40 failures were first written up as the route-killer, then demoted.**
   Measuring the *exact* obligation (payload correct throughout the redirect target's forward cone
   in `acc ∪ red`, closed under redirect chains) gave 0 failures / 24,314. The finding survives as
   a **statement-shape constraint** on Phase 1, not as a viability gate. This is the one place in
   the report where a further measurement overturned a conclusion I had already drafted.

### Confidence levels

| Finding | Confidence |
|---|---|
| Soundness is trivial at a blocked step (§2.1) | **High** — structural, from the two invariant definitions |
| Termination survives; pigeonhole bound retained (§5.1, §5.2) | **High** — field-by-field read of `S4LoopInv` + the measure lemma's hypothesis list + 0/8532 measured `keysDistinct` breakage |
| `outDegEq` is droppable (§5.3) | **High** on "no current consumer" (mechanical grep); **Medium** on "never needed" (a future out-degree-driven fuel argument could want it) |
| Completeness cost = 4 decls / 1,036 lines (§3.1-3.2) | **High** — mechanical parse + BFS, every decl cited by line range |
| The empirical results (§6) | **High** — verbatim `#eval`, oracle calibrated against a docstring-stated countermodel, guard-firing confirmed non-vacuous |
| Condition (b) holds at terminal leaves in general | **Medium** — 0 failures / 24,314 is strong but absence of failure at size ≤ 7 is not proof; `cex` itself is size 19. **This is the report's least-verified load-bearing claim** |
| The exact obligation (F\*)/(G\*) holds at terminal leaves in general | **Medium** — 0 failures / 24,314 over the full `acc ∪ red` relation is strong, and it is the *right* statement rather than a proxy; but the corpora top out at size ≤ 8 (1 atom) / ≤ 7 (2 atoms), and `cex` is size 19. **Together with condition (b) this is the report's least-verified load-bearing claim** |
| Route (2′)'s phase 3 is route (1)-scale (§7.1) | **Medium-High** — both refutations are landed and cited, but the inference "therefore a new model must be built per step" is my reading, not a landed theorem |
| #548 risk dissolves (§8) | **High** — `modalApplyOne_boxPos_sound` has no `FC` parameter; `hrefl` unused at `:1092-1099` |
| Phase estimates (§7) | **Medium** — sized against the landed analogues' actual line counts, but estimates |

### Zero-debt compliance

No recommendation defers a `sorry`, adds an axiom, or introduces a vacuous definition. Phase 5 of
the recommended plan **retires** `FrameSoundness.lean:1244`. No `Cslib/**` file was edited; that
`sorry` remains the only one in `Cslib/Logics/Modal/Tableau/` (verified by grep over all 14
files). All three probes are definitions + `#eval` only, under `specs/553_.../artifacts/`.

---

## 11. Memory candidates

1. **A loop-checking discipline that ADDS a redirect edge manufactures a soundness obligation the
   source calculus does not have.** `Massacci2000` Technique 8.2 blocks by *withholding* the
   π-rule and adding nothing, which is why its loop-checking theorem (Thm 8.1) is
   completeness-side only. If a driver instead records the redirect in the same accessibility
   structure that soundness quantifies over, the obligation becomes per-step and typically
   unprovable against an arbitrary witness model. **The fix is to split the bookkeeping**: a
   soundness-tracked structure containing only justified edges, plus a completeness-only channel.
   The general principle: *an artifact needed only by the model-construction direction should not
   live in a structure the soundness invariant reads.*
2. **Relocating an obligation from per-step to terminal-state can convert a FALSE lemma into a
   true one.** Counterexamples to per-step invariant preservation in saturating tableau drivers
   are frequently *transient* — the branch is "repaired one step later". The same statement
   restricted to terminal saturated branches can hold. Before abandoning a route because a lemma
   was refuted, check **at which state** the counterexample lives.
3. **In CSLib's modal tableau line, `branchSatisfiableIn`'s full-strength 4-rule lemmas need
   `IsTrans` only, and the K box-positive lemma needs no frame condition at all**
   (`FrameSoundness.lean:1085-1100`, `:1106-1123`; `SoundnessStep.lean:446-459`). The weakened
   `branchPropAdequateIn` line by contrast needs `Std.Refl` (`:1454`) plus an `hready` side
   hypothesis (`:1449-1450`). So *weakening the invariant made the frame-condition requirements
   stronger* — relevant whenever non-reflexive transitive corners (K4/K45/D4/D45) are to reuse
   the mechanism.
4. **Build an independent semantic oracle when auditing a decision procedure's differential.**
   A direct `Bool` evaluator over all reflexive-transitive frames up to size 3-4 is ~40 lines,
   calibrates against a known countermodel, and turns "the verdict changed on N formulas" into
   "the driver was unsound on N₁ and lost completeness on N₂". Also: always measure that the
   feature under test **actually fires** on the corpus — verdict agreement on a corpus where the
   guard never triggers is worthless.
