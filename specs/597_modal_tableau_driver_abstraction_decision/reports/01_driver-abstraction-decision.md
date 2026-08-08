# Tableau Driver Abstraction Across Three Termination Regimes — Decision Evidence

**Task**: 597 | **Type**: cslib (decision/research) | **HEAD**: `5ea7152c`
**Session**: `sess_1786219370_0903ea_597`
**Deliverable class**: (b) with a scoped exception — *the per-regime split is the correct steady
state; the abstraction the task asks about already exists and is already instantiated; the
expansion should be re-tranched, for a reason other than duplication.*

**Revision note**: this report was revised after task 511's research completed
(`specs/511_s4_loop_checking_termination/reports/03_head-reverification-ordered-driver.md`,
2026-08-08), which supersedes that task's earlier `.orchestrator-handoff.json`. Three conclusions
changed materially and are marked **[revised]** at their sections: §6 (S4 is close to finished,
not far), §7.3 (the traversal rung is downgraded from "on the critical path" to optional, and is more
expensive than previously sized), and §10 (task 511 is unblocked with its own verified plan). One
finding was added: §6.2, rule-application *order* is soundness-critical, which is a constraint on
any abstraction that would let a regime choose its own schedule.

---

## 0. Executive Summary

Five findings, in order of decision weight.

1. **The abstraction the task proposes ("generalise `RuleApplicationSpec` over the termination
   measure rather than fixing the K-style counting measure") already exists, landed, and is
   instantiated at four systems.** It is `AuxStepPreserved` / `AuxBounds` /
   `ModalLoopInvHintikka` / `modalExpandBranchesHintikka` in `CompletenessLoop.lean`
   (`Cslib/Logics/Modal/Tableau/CompletenessLoop.lean:230-430`, `:1410`). It factors the
   world-bound conjunct out of the loop invariant into an opaque, step-preserved `Aux` predicate,
   exactly so that K's rank/potential argument and S5w's tag-cardinality argument can share one
   structure. **Two of the task's three "termination regimes" are therefore already spanned by
   one abstraction.** The task description's premise that regime 1 and regime 3 are "bespoke
   parallel implementations" is out of date.

2. **The state-threading generalisation that task 511 nominated as its route (b) also already
   exists**, as the `RuleApplySt` ladder in `Saturation.lean:493-758` (landed by tasks 562/564,
   2026-08-05/06), with a live consumer: `modalExpandBranchesS4Keyed` is bridged onto
   `modalExpandBranchesGenSt` by `modalExpandBranchesGenSt_eq_S4Keyed`
   (`S4/Driver.lean:2449`).

3. **The payoff from pushing that abstraction further has already been measured, in this
   subsystem, and it is negative.** Task 564 measured the destructive redefinition of the bespoke
   S4 steppers as generic `RuleApplySt` instantiations at **net +80 lines across 40 proof sites
   requiring re-verification**, "because those sites depend on the definitional *shape* of the
   steppers, not merely their behavior", and excluded it. This is the Chronicle failure mode,
   already instrumented here, with a number attached. It is the strongest single piece of
   evidence against a further driver generalisation.

4. **[revised]** **The gate on the 8-corner expansion is not duplication — it is that the
   loop-checking regime's reference implementation is not yet finished, though it is close.** S4
   has `modalTableauS4Keyed_complete` (keyed driver) and `modalTableauS4KeyedOrdered_sound`
   (ordered driver) — **soundness and completeness are proven for two different drivers**,
   `modalTableauS4Keyed_sound` is *false as stated* with a machine-checked counterexample
   (`CslibTests/S4LoopGuardRegression.lean`), and there is no `s4Valid_decides` /
   `instDecidableS4Valid`. Task 511's re-verification (2026-08-08) establishes that closing this
   is a bounded **~580-line, six-item, four-phase within-file port** against already-landed
   ordered lemmas — not a redesign, and not dependent on any abstraction decision. The K4/D4 gate
   is therefore real but light, and already unblocked.

5. **[revised]** **Rule-application *order* is soundness-critical in the loop-checking regime — a
   machine-checked fact, and a hard constraint on abstraction design.** The unsoundness of the
   unordered keyed driver was repaired not by changing the guard's comparison predicate but by
   changing *when* a minting shape may fire (settled-context scheduling). A traversal abstraction
   that lets a caller supply its own schedule is therefore **unsound by construction unless it
   also carries the ordering obligation** — the schedule it would make instantiable is one for
   which soundness is machine-checked *false*. This downgrades the traversal rung (§7.3) from
   "small and on the critical path" to "optional, and larger than task 564 sized it". The
   strongest argument *for* the per-regime split falls out of the same fact: the ordered driver
   could only be built at all because the bespoke path let its scheduling change independently of
   the guard predicate. An abstraction that had fixed the traversal would have obstructed the
   repair that made S4 sound.

---

## 1. Re-measurement at HEAD (`5ea7152c`)

Every figure in the task description reproduces exactly. Nothing has drifted.

| Figure | Task description (2026-08-07) | HEAD (`5ea7152c`) | Command |
|---|---|---|---|
| Tableau subsystem | 44,692 lines / 32 files | **44,692 / 32** | `find Cslib/Logics/Modal/Tableau -name '*.lean' \| xargs cat \| wc -l` |
| Library | 236,442 lines | **236,442 / 700 files** | `find Cslib -name '*.lean' \| xargs cat \| wc -l` |
| Share | 19% | **18.9%** | — |
| `GenericDriver.lean` | 553 lines, 11 fields | **553 / 11** | `wc -l`; fields counted in source |
| `S5Simplification.lean` | 2,331 | **2,331** | `wc -l` |
| `FiveSimplification.lean` | 3,802 | **3,802** | `wc -l` |
| `LoopChecking.lean` + `S4/*` | ~10,900 | **1,626 + 10,294 = 11,920** | `wc -l` |

Subsystem-wide declaration count: **1,133** top-level declarations
(`^(private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance|structure|inductive) `
across `Tableau/*.lean` + `Tableau/S4/*.lean`).

Modal namespace as a whole is 79,200 lines, so the Tableau subtree is 56% of the modal
development.

---

## 2. What Is Already Abstracted — Five Axes

The subsystem does not have "one abstraction covering one regime". It has **four landed
abstraction axes and one missing one**. This is the single most important correction to the
task's framing, and it changes what the decision is about.

| Axis | Abstraction | Where | Instantiated at | Refs |
|---|---|---|---|---|
| 1. The rule | `RuleApply`, `modalStepBranchGen` / `modalExpandBranchesGen` / `modalTableauGen` | `Saturation.lean:107-395` | every system incl. S4 (definitionally) | 208 / 126 / 44 |
| 2. Structural obligations on the rule | `RuleApplicationSpecCore` (8 fields) / `RuleApplicationSpec` (11) | `GenericDriver.lean:179-338` | full: K, T, B. Core-only: S5w, Five, Kb5, Kb5'' | 107 |
| 3. **Termination evidence** | `AuxStepPreserved` / `AuxBounds` / `ModalLoopInvHintikka` / `modalExpandBranchesHintikka` | `CompletenessLoop.lean:263-420`, `:1410` | `ModalLoopAuxK` (rank + potential), `ModalLoopAuxS5w` (tag cardinality), `ModalLoopAuxFive`, `ModalLoopAuxKb5''` | 24 / 29 / 17 |
| 4. Threaded per-branch state | `RuleApplySt` / `modalStepBranchGenSt` / `modalExpandBranchesGenSt` / `modalTableauGenSt` | `Saturation.lean:493-758` | `Unit` (bridge), `modalApplyOneS4KeyedSt` | 25 / 31 |
| 5. **Traversal / scheduler** | — **does not exist** | — | — | — |

### 2.1 Axis 3 is precisely the abstraction this task asks whether to build

`CompletenessLoop.lean:230-245` states the design rationale in terms that match this task's
question almost word for word:

> `ModalLoopInvGen` threads a rank map purely to re-establish the a-priori world bound
> (`phiBound`) [...] S5w's own termination argument re-establishes the same world bound with *no*
> rank map at all — purely by tag-cardinality counting. `ModalLoopInvHintikka` below factors the
> world-bound conjunct out into an abstract, caller-supplied `Aux` predicate so both arguments
> can share one structure.

and it records the hazard it was designed against:

> a bare scalar field `worldBound : modalMaxWorld b < modalWorldBound φ0` is *not* itself
> step-preserved [...] `Aux` is therefore threaded as an opaque, step-preserved predicate
> (`AuxStepPreserved`) from which the bound is derived pointwise (`AuxBounds`), never as a bound
> scalar on its own.

The K-side re-derivation (`modalExpandBranchesGen_hintikka` re-derived from
`modalExpandBranchesHintikka` at `Aux := ModalLoopAuxK φ0`) pins the factoring as faithful to the
statement its T/B consumers already depend on. This is not a type-level generalisation that was
never exercised: it is a generalisation that was exercised by re-deriving the original from it.

**Consequence for the decision**: "extend `RuleApplicationSpec` to carry per-regime termination
evidence" is not a candidate design. It is a shipped design. The remaining question is only
whether S4 can be brought under it — see §5.

### 2.2 Why the K measure genuinely cannot cover S5 (a refutation, not a gap)

`S5Simplification.lean:1709` contains `modalApplyOneS5_rankStep_not_dischargeable`: an explicit
theorem that the `rankStep` field of `RuleApplicationSpec` is **not satisfiable** for
`modalApplyOneS5`, witnessed by a concrete branch/rank counterexample
(`s5RankCounterBranch`/`s5RankCounterRank`/`s5RankCounterSf0`). Likewise
`S5Simplification.lean:1732ff` (`modalApplyOneS5_hintikka_not_reachable_growth`) refutes the
alternative route — that K's `modalFuel` already dominates the unguarded S5 expansion — as "a
false statement, not merely unproved".

`GenericDriver.lean:127-130` records the S4 exclusion in the same register: transitive box
propagation "falsifies the exact-decrement edge invariant (`rankStep`)".

**These are hard constraints, not unexplored territory.** Any proposal to unify the three regimes
under a single *measure* is refuted by machine-checked counterexamples already in the tree. Only
unification under an *abstract* measure (axis 3) was ever available, and it was taken.

---

## 3. What Actually Varies, Precisely

Stripping the framing, here is what differs across the three regimes.

| | K-style counting | Universal cluster (S5w/Five/Kb5'') | S4 loop-checking |
|---|---|---|---|
| Driver | `modalTableauGen` | `modalTableauGen` (**same**) | bespoke `modalExpandBranchesS4Keyed{,Ordered}` |
| Fuel | `modalFuel φ` | `modalFuel φ` (**same**) | `modalFuelS4 φ₀` |
| Rule shape | `modalApplyOne` | witness-**reuse** at the two mint shapes + universal propagation | blocking guard at the two mint shapes |
| Spec discharged | full `RuleApplicationSpec` (11) | `RuleApplicationSpecCore` only (8) | **none** |
| World bound via | rank map + `geomCap` potential conservation | tag cardinality (`S5wTagInv`/`S5wWorldInv`, `≤ modalOps φ`) | pigeonhole on birth keys, `2^(2·\|modalSubfmls φ₀\|)` |
| Aux instantiation | `ModalLoopAuxK` | `ModalLoopAuxS5w` / `Five` / `Kb5''` | **none** — bespoke `S4LoopInv` |
| Per-branch state | none | none | `keys : List (WorldIndex × Finset (Sign × Proposition Atom))` |
| Traversal | `b.findSome?` | `b.findSome?` (**same**) | ordered: filtered candidate scan, then fallback |

The genuinely-common core is larger than the task assumes: **regimes 1 and 3 share the driver,
the fuel, the top loop, the Hintikka predicate, and the `Aux` interface.** They differ only in
the *rule* (axis 1, already abstract) and the *content of `Aux`* (axis 3, already abstract).

The genuinely-divergent regime is S4 alone, and it diverges on **two axes at once**: threaded
state (axis 4, abstracted but not joined to axis 3) and traversal order (axis 5, not abstracted
at all).

### 3.1 The axis-3 / axis-4 join is missing

`AuxStepPreserved` (`CompletenessLoop.lean:263`) is stated over `modalStepBranchGen apply` — the
**stateless** stepper. `modalExpandBranchesHintikka` is stated over `modalExpandBranchesGen`.
There is no `AuxStepPreservedSt` / `ModalLoopInvHintikkaSt` / `modalExpandBranchesHintikkaSt`
(verified: zero hits repo-wide). S4 therefore cannot consume axis 3 even though the state ladder
exists, and instead carries its own `S4LoopInv` — 42 declarations across
`S4/Invariant.lean` (7), `S4/InvariantKeys.lean` (14), `S4/InvariantAcc.lean` (12),
`S4/HintikkaInvariant.lean` (9), ~4,700 lines.

Joining them is an **arity change on four declarations plus a port of one theorem**
(`modalExpandBranchesHintikka`, ~330 lines). That is the mechanical, bounded version of
"generalise the driver framework to carry extra opaque per-branch threaded state generically" —
task 511's blocker route (b). It is real work but it is not open-ended.

### 3.2 The traversal axis is documented as not expressible

`Saturation.lean:506-512` states the limit of axis 4 explicitly:

> The KeyedOrdered driver (`modalStepBranchS4KeyedOrdered`/`modalExpandBranchesS4KeyedOrdered`)
> remains unmigrated: it is structurally impossible against this ladder as it stands, since
> `modalStepBranchGenSt` abstracts over the *rule* passed to it, not over the *traversal* it
> performs, while the ordered driver's minting gate depends on a global, traversal-level property
> of the branch that no choice of rule can express.

Confirmed against the definition: `modalStepBranchS4KeyedOrdered` (`S4/Driver.lean:631`)
"first scans `modalNonMintCandidates φ₀ keys b e acc` [...] and only falls back to the literal old
`b.findSome?` traversal once that scan returns `none`". The gate is a property of *which formula
the scheduler picks*, not of what the rule returns.

Task 564's own scope-exclusion note sizes the fix: "a new stepper-parameterised rung in
`Saturation.lean` (research estimate: a ~55-line rung plus two ~50-line bridge proofs)".

---

## 4. Duplication Census — What Replicates, and How Much

Method: extract every top-level declaration name in `Tableau/*.lean` + `Tableau/S4/*.lean`; tag by
system infix (`T`, `B`, `S5`, `S5w`, `Five`, `FiveProp`, `Kb5`, `Kb5''`, `Kb5''Prop`, `S4`,
`S4Keyed`, `S4KeyedOrdered`) at a CamelCase boundary; attribute each declaration's line span to
its tag. Scripts under the session scratchpad; both are ~30 lines and reproduce from the tree.

### 4.1 Per-system attribution

| Tag | Decls | Lines |
|---|---|---|
| (untagged / shared infrastructure) | 505 | 14,238 |
| S4 | 143 | 7,453 |
| S4Keyed | 68 | 3,457 |
| Five | 81 | 3,293 |
| S4KeyedOrdered | 29 | 2,630 |
| Kb5'' | 49 | 2,423 |
| S5 | 59 | 2,384 |
| T | 62 | 1,796 |
| B | 56 | 1,627 |
| S5w | 35 | 1,392 |
| Kb5 | 30 | 955 |
| FiveProp | 8 | 260 |
| Kb5''Prop | 8 | 258 |
| **tagged total** | **628** | **27,928** |

**63% of the subsystem's declaration-span lines are per-system instantiation material; 32% is
shared infrastructure.**

### 4.2 Cost per corner — three tiers, not three regimes

| Tier | Corners | Decls | Lines | Template status |
|---|---|---|---|---|
| **A** — full `RuleApplicationSpec` dischargeable | T | 62 | 1,796 | complete: sound + complete + decides |
| | B | 56 | 1,627 | complete |
| **B** — `rankStep` refuted; witness-reuse + own world-bound + `Aux` | S5 + S5w | 94 | 3,776 | complete |
| | Five + FiveProp | 89 | 3,553 | complete |
| | Kb5 + Kb5'' + Kb5''Prop | 87 | 3,636 | complete |
| **C** — loop-checking + threaded state + ordered traversal | S4 + Keyed + KeyedOrdered | 240 | 13,540 | **incomplete** (see §6) |

A Tier-A corner costs ~1,700 lines. A Tier-B corner costs ~3,600. A Tier-C corner has cost 13,540
so far and has not yet produced a decision procedure.

### 4.3 Clone similarity — the abstraction that would actually pay

Pairwise line-level similarity (`difflib.SequenceMatcher` over tag-normalised declaration bodies)
between twin declarations:

| Pair | Twin decls | Lines | Median similarity | >0.90 |
|---|---|---|---|---|
| `Kb5''` ← `Five` | 38 | 1,390 vs 1,429 | **≈0.85** | 10/38 |
| `Five` ← `S5w` | 16 | 706 vs 782 | **≈0.63** | 0/16 |

The `Kb5''`/`Five` pair is a near-verbatim clone family: `modalApplyOneKb5''_boxPos_eq`,
`_boxPosNotExpanding`, `modalExpandBranchesKb5''_eq`, `modalStepBranchKb5''_eq`,
`modalTableauKb5''` are **1.00** identical after tag normalisation; `_outputsSubsetUniverse`
(141 lines), `_persistentFresh` (102), `_worldGrowth` (158) are 0.89–0.92.

The `Five`/`S5w` pair is markedly less similar (0.63) — the Route (a) root-aware guard genuinely
changes the proofs, exactly as `FiveSimplification.lean`'s own header claims.

**[added]** A third clone family, *within* the S4 cluster, measured after task 511's report
flagged it. The two S4 stepper stacks (unordered `modalStepBranchS4{,Keyed}` and ordered
`modalStepBranchS4KeyedOrdered`) carry **14 same-suffix invariant-preservation twin pairs**:

| | Twin pairs | Lines | Median similarity |
|---|---|---|---|
| `S4KeyedOrdered_preserves_*` ← `S4{,Keyed}_preserves_*` | 14 | 1,881 vs 1,920 (**3,801 combined**) | **≈0.73** |

Suffixes: `accFresh` 0.78, `accKnown` 0.76, `bClosure` 0.74, `eClosure` 0.74, `eNodup` 0.69,
`keyLowerBd` 0.66, `keysDistinct` 0.43, `keysInUniverse` 0.72, `keysOriginS4` 0.88, `keysTotal`
0.79, `keysWorldsKnown` 0.65, `worldsContiguousS4` 0.83, `S4LoopInv` 0.27,
`S4KeyedHintikkaInv` 0.45. Task 511's report will add two more ~250-line structural twins
(`_hintikka`, `_openBranch_initial_mem`).

**3,801 lines — comparable to an entire Tier-B corner — is the measured cost of maintaining two
parallel S4 stepper stacks.** This is the single largest concrete duplication cost the census
found, and it is *intra*-regime, not inter-regime: it is the price of the scheduling change, not
of the absence of a cross-regime abstraction. §6.2 argues it was worth paying.

**Crucially, the low-similarity outliers in both pairs are the termination-bound pieces**:
`Kb5''WorldInv` 0.11, `modalMaxWorld_lt_worldBound_of_Kb5''WorldInv` 0.14, `_specCore` 0.31,
`modalStepBranchS5w_preserves_worldInv` 0.07. That is precisely what the `Aux` design predicts:
the world-bound argument is the genuinely-varying part, and it is already the abstracted slot. The
clone mass is in the **rule-shape agreement and spec-field discharge layer**, which `Aux` does not
and was never meant to cover.

### 4.4 Cross-system skeleton census

104 declaration skeletons are instantiated at ≥2 systems, covering **330 declarations (29% of the
subsystem)**. The widest:

```
11x  modalApplyOne@          B Five FiveProp Kb5 Kb5'' Kb5''Prop S4 S4Keyed S5 S5w T
 8x  modalTableau@           B Five Kb5 Kb5'' S4 S4Keyed S4KeyedOrdered S5
 8x  modalStepBranch@        Five Kb5 Kb5'' S4 S4Keyed S4KeyedOrdered S5 T
 8x  modalExpandBranches@    Five Kb5 Kb5'' S4 S4Keyed S4KeyedOrdered S5 T
 6x  extractModel@ / _r / _hasEdge_imp_r
 5x  modalApplyOne@_{outputsSubsetUniverse,persistentFresh,branchingLength,
                      localShapeInvariance,boxPosNotExpanding,diaNegNotExpanding}
 5x  hintikka@_box_pos / hintikka@_diamond_neg
 3x  ModalLoopAux@ / _bounds / _stepPreserved
```

The six 5×-replicated `RuleApplicationSpec` field discharges are the honest instantiation
obligation — each is a real proof about a genuinely different rule. They are *not* eliminable by
more driver abstraction. They are partly eliminable by a **rule combinator** (§7.2).

---

## 5. Blast Radius

Reference counts (`grep -rho` over `Cslib/` + `CslibTests/`):

| Target | Total refs | Refs inside defining files |
|---|---|---|
| `modalApplyOneS4*` | 1,136 | 765 |
| `modalApplyOneFive*` | 434 | 310 |
| `modalApplyOneKb5*` | 410 | 298 |
| `modalApplyOneT*` | 375 | 218 |
| `modalApplyOneS5w*` | 233 | 167 |
| `modalApplyOneB*` | 202 | 137 |
| `RuleApplicationSpec` | 107 | — |
| `modalStepBranchGen` | 208 | — |
| `modalExpandBranchesGen` | 126 | — |
| `ModalLoopInvHintikka` / `AuxStepPreserved` / `modalExpandBranchesHintikka` | 29 / 24 / 17 | — |
| `RuleApplySt` / `modalExpandBranchesGenSt` | 25 / 31 | — |

Two structural hazards constrain any change to axes 1 and 4:

- **Six driver bridges are true `rfl`** and break if `modalExpandBranchesGen`'s definitional shape
  changes: `modalExpandBranchesB_eq`, `modalTableauB_eq`, `modalTableauS5_eq`,
  `modalTableauFive_eq`, `modalTableauKb5_eq`, `modalTableauKb5''_eq` (recorded binding in the
  D3 decision record, §6). This is why the St ladder was mandated additive-first.
- **`modalStepBranch` / `modalExpandBranches` / `modalTableau` (K) are deliberately kept as
  duplicate literal definitions**, not wrappers, so that 14+ `simp only`/`unfold` call sites keep
  their exact unfold normal form (`Saturation.lean:149-158`, `:250-256`, `:373-384`). Any
  "collapse the duplication" instinct aimed at these is aimed at a deliberate,
  documented zero-regression device.

---

## 6. The Loop-Checking Regime Is Not Yet Finished — And That, Not Duplication, Gates the Expansion **[revised]**

Verified end-to-end status matrix at HEAD (`grep` over
`^(theorem|lemma) modalTableau[A-Za-z0-9']*_(sound|complete)` and `[a-zA-Z0-9]*_decides`, plus
`instance instDecidable`):

| System | `_sound` | `_complete` | `_decides` | `Decidable` instance |
|---|---|---|---|---|
| K | ✅ `modalTableau_sound` | ✅ | ✅ | ✅ `instDecidableKValid` |
| T | ✅ | ✅ | ✅ | ✅ `instDecidableTValid` |
| B | ✅ | ✅ | ✅ | ✅ `instDecidableBValid` |
| S5 | ✅ (`S5`, `S5w`, `S5Gen`) | ✅ | ✅ | ✅ `instDecidableS5Valid` |
| 5 / K5 | ✅ `modalTableauFive_sound` | ✅ | ✅ | ✅ `instDecidableFiveValid` |
| KB5 | ✅ (`Kb5`, `Kb5''`) | ✅ `Kb5''` | ✅ | ✅ `instDecidableKb5Valid` |
| **S4** | ✅ **`modalTableauS4KeyedOrdered_sound`** | ✅ **`modalTableauS4Keyed_complete`** | ❌ | ❌ |

**Soundness and completeness are proven for two different drivers.** And
`FrameCompleteness.lean:4085-4103` states plainly:

> **The soundness half is FALSE AS STATED, not merely unproven or deferred.** [...]
> `CslibTests/S4LoopGuardRegression.lean` witnesses a formula that closes under
> `modalExpandBranchesS4Keyed` while having an explicit 3-world reflexive-transitive
> countermodel [...] Do not attempt to prove `modalTableauS4Keyed_sound` for the driver below; it
> cannot be proved, because it is not true. [...] The decidability half
> (`s4Valid_decides`/`instDecidableS4Valid`) remains out of scope until both a genuine soundness
> theorem and this completeness theorem exist for the same driver.

The repair route is the ordered driver — which has soundness but no
`modalTableauS4KeyedOrdered_complete` and no `modalExpandBranchesS4KeyedOrdered_hintikka`
(verified: zero hits).

### 6.1 The remaining S4 work is bounded, and independent of this decision **[revised]**

Task 511's re-verification against the same HEAD establishes the size of the gap. Its findings are
better-evidenced than this report's on this point — it ran `lake build` green on
`Cslib.Logics.Modal.Tableau.FrameCompleteness` (910 jobs) and `.LoopChecking` (876 jobs),
`lean_verify`-ed `modalTableauS4KeyedOrdered_sound` to an **empty axiom list**, and
machine-probed the one remaining non-copy proof obligation green before reverting it. This report
adopts those findings rather than restating its own weaker inference.

Remaining scope: **six items, ~580 added lines, of which ~490 are near-verbatim structural copies
of already-proven unordered analogues**, in four phases:

1. `modalStepBranchS4KeyedOrdered_none_saturated` — probed green as a one-line transfer through
   `modalStepBranchS4KeyedOrdered_eq_none_iff`.
2. Relocate `modalStepBranchS4KeyedOrdered_newExps_eq_map` down from `FrameCompleteness.lean` into
   `LoopChecking.lean` (pure move, dependencies verified all below).
3. `modalExpandBranchesS4KeyedOrdered_hintikka` — ~370-line structural port.
4. `modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem` — ~135-line structural port.
5. `modalTableauS4KeyedOrdered_complete` — near-verbatim copy.
6. `s4Valid_decides` + `instDecidableS4Valid` — three lines each, mirroring the KB5 template.

**Consequence for this decision**: S4's decidability does not gate on, and must not wait for, any
abstraction change. The earlier framing in this report — that finishing S4 was a heavy
precondition — overstated it. The K4/D4 gate stands, but it is a light gate on already-unblocked,
already-planned work.

### 6.2 Order is soundness-critical — a constraint on any abstraction that touches scheduling **[added]**

The most consequential fact for abstraction design is *how* the S4 unsoundness was repaired.
`FrameCompleteness.lean:4090-4098` records two independent defects in the unordered keyed guard —
birth-key **staleness** (comparing prospective minting content against a world's recorded key
rather than its live content) and **unrestricted redirect reachability** (admitting a redirect edge
without requiring the target be reachable from the source). The repair addressed neither by
changing the guard's comparison predicate. It changed **when a minting shape may fire**:
settled-context scheduling — non-minting candidates first, minting only once no non-minting rule
can fire anywhere on the branch (`modalStepBranchS4KeyedOrdered`, `S4/Driver.lean:631`).

Two consequences, both binding on §7:

- **A traversal abstraction is not soundness-neutral.** Abstracting the traversal behind a
  `select`-style parameter makes the *unordered* schedule instantiable — and soundness for that
  schedule is not merely unproven, it is machine-checked false. Such a rung is therefore
  unsound-by-construction unless it simultaneously carries an ordering obligation (a
  settled-context predicate) as a *proof obligation on the instantiator*, in the same way
  `RuleApplicationSpec` carries structural obligations on the rule. That obligation's statement is
  generic; its discharge is per-corner. This is a materially larger design than "a `select`
  parameter", and §7.3 is re-costed accordingly.
- **The per-regime split earned its keep here, concretely.** The ordered driver could only be built
  because the bespoke path let its *scheduling* change independently of its *guard predicate*. Had
  the traversal been fixed by a shared abstraction at the time the unsoundness was discovered, the
  repair would have required changing the abstraction and re-verifying every corner instantiated
  against it, rather than changing one system's stepper. This is the strongest single argument in
  this report for the status quo, and it is an argument from a real event, not from caution.

The intra-S4 cost of that independence is measured in §4.3: 3,801 lines across 14 twin pairs. The
judgement this report reaches is that 3,801 lines was a good price for a soundness repair that
would otherwise have been blocked — but it is a real price, and it should be paid once, not
replicated across K4 and D4 (§9).

---

## 7. Candidate Designs, Costed

### 7.1 Keep three bespoke drivers (status quo) — **partially correct, and the default**

Cost: 0. Blast radius: 0. Effect on expansion: Tier-A corners ~1,700 lines each, Tier-B ~3,600
each, Tier-C unbounded and currently unfinished.

This is *already* not what the tree does: regimes 1 and 3 share one driver, one fuel, one top
loop, and one `Aux` interface. The "three bespoke drivers" framing describes only the S4 fork,
which is one driver family of nine (recorded in the D3 rationale).

**Verdict: correct as the steady state for the termination-evidence question. Not sufficient as
the answer to the expansion question.**

### 7.2 Rule-combinator for the universal-cluster family — **RECOMMENDED, small, de-duplication-shaped**

Not a driver change. Parameterise the *rule*, one layer below the spec:

```
mintWithReuse (witness : Branch → Sign → Prop → Option WorldIndex)
              (rootGuard : Bool)
              (prop : propagation-target filter)
```

covers `modalApplyOneS5w`, `modalApplyOneFive`, `modalApplyOneKb5''` — verified by reading the
three definitions (`S5Simplification.lean` `modalApplyOneS5w`, `FiveSimplification.lean`
`modalApplyOneFive`, `modalApplyOneKb5''`): they differ only in (i) the witness-search predicate
(`witnessWorldS5` vs `witnessWorldFive`), (ii) a `sf.label == 0` root guard on the mint arm, and
(iii) the propagation target filter (all known worlds / non-root / non-root + root-when-nonempty).

The strongest single data point: **`modalApplyOneKb5''` is character-for-character
`modalApplyOneFive` with `modalApplyOneFiveProp` substituted by `modalApplyOneKb5''Prop`** — same
root guard, same `witnessWorldFive`, same two mint arms. The entire KB5-vs-5 difference lives in
the propagation helper (`modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv` vs
`modalFiveBoxAll`/`modalFiveDiaNegAll`), yet the difference is re-proved across all 38 twin
declarations. A combinator parameterised on the propagation helper alone would already address
this pair.

**Honest expected payoff, from §4.3**: the ~0.85-similarity band (a new Euclidean corner cloned
from an existing sibling with the same guard family) largely collapses; the ~0.63 band (a corner
that changes the guard shape) does not. Concretely: of the ~3,600 lines a Tier-B corner costs
today, expect roughly the ~1,400-line clone band to shrink substantially and the world-bound /
`Aux` / `_specCore` band (~0.1–0.4 similarity) to remain per-corner.

**Blast radius**: contained to `S5Simplification.lean` + `FiveSimplification.lean` (6,133 lines,
~200 declarations). Does **not** touch `Saturation.lean`, so the six `rfl` bridges are untouched
by construction.

**Hazard, stated plainly**: the spec-field discharges route through `_eq_of_not_mint_shape`
agreement lemmas that are shape-sensitive. Abstracting the mint arm behind a combinator will turn
some `rfl`/`simp [modalApplyOneX]` steps into case splits on the combinator's guard. This is
exactly the Chronicle failure mode and the §4.3 similarity data is the evidence that it will bite
in the 0.63 band. **This must be prototyped on one pair (`Kb5''`-from-`Five`) and measured before
being applied to three.**

**Honours D7** ("de-duplication precedes every abstraction change"): this *is* de-duplication,
and it is the residue D7's own task-558 sweep left behind (that sweep targeted re-derived
*shared facts* into `Support/`; this targets *cloned rule families*, a different axis).

### 7.3 Stepper/traversal rung in `Saturation.lean` — **OPTIONAL consolidation; NOT on the critical path; re-costed upward** **[revised]**

Add a rung that abstracts over the *traversal* (a `select : branch → expanded → acc → σ →
Option SignedFormula` parameter) alongside the existing rule parameter, so
`modalStepBranchS4KeyedOrdered` becomes an instantiation rather than a fork.

**This report previously recommended this as small and on the critical path. Both halves of that
were wrong, on evidence that arrived after the first draft.**

- **Not on the critical path.** S4's decidability needs the six-item port of §6.1, which runs
  against already-landed ordered lemmas inside `LoopChecking.lean` and `FrameCompleteness.lean`.
  It does not need the ordered driver to be an instantiation of anything. Task 511's report states
  this directly and declines route (b) on exactly this ground.
- **Larger than ~155 lines.** Per §6.2, a bare `select` parameter would make the machine-checked
  *unsound* schedule instantiable. To be sound-by-construction the rung must carry a
  settled-context ordering obligation as a proof obligation on the instantiator — generic in
  statement, per-corner in discharge. Task 564's ~55-line rung + two ~50-line bridges sized the
  *computational* rung only; it did not size this obligation, which is where the real cost is. No
  defensible number is available for it, and none is invented here.
- **A further reason it would not pay today**, from task 511: the ordered driver's completeness
  proof threads `S4OrderedFuelInv` — a five-conjunct bundle carrying `keys` — per branch, "which
  no `Prop`-valued `Aux` over `(b, e, acc)` supplies". So even with the traversal rung, the
  ordered driver would not thereby become an `Aux` consumer.

**Revised verdict**: worth doing *after* S4 lands its decidability and *if* a second scheduling
regime appears (a transitive corner whose settled-context discipline differs from S4's would be
the trigger). Not before, and not as a precondition for anything currently planned.

### 7.4 Join axis 3 to axis 4 (`AuxStepPreservedSt` / `modalExpandBranchesHintikkaSt`) — **defer** **[revised]**

Arity change on `AuxStepPreserved`, `AuxBounds`, `ModalLoopInvHintikka` + port of
`modalExpandBranchesHintikka` (~330 lines). Would let S4 retire ~4,700 lines of bespoke
`S4LoopInv` material in favour of an `Aux` instantiation.

**Defer**, now for three reasons: (i) task 564's measured **+80 lines / 40 proof sites** for the
analogous destructive move is direct evidence that a shape-sensitive migration of landed S4
invariant proofs does not pay at the current maturity of that cluster; (ii) **[revised]** it is no
longer downstream of 7.3 in the sense first stated — it is simply not needed by anything on the
critical path; (iii) **[added]** the target it would have to accommodate is not `Prop`-valued: S4's
live per-branch obligation is the `S4OrderedFuelInv` bundle threaded alongside `keys`, so the join
would have to generalise `Aux` beyond a predicate over `(b, e, acc)` — a strictly larger change
than the arity edit described above, and one for which no consumer currently asks.

### 7.5 Destructive redefinition of the bespoke S4 steppers as generic instantiations — **REJECT**

Already measured by task 564: **net +80 lines across 40 proof sites requiring re-verification**,
"because those sites depend on the definitional *shape* of the steppers, not merely their
behavior". Explicitly excluded there as requiring user sign-off not obtainable autonomously.

This is the decisive, in-subsystem, quantified instance of the Chronicle failure mode the task
description warns about. It should not be re-attempted without a new reason.

### 7.6 Lift anything into `Foundations/` — **PROHIBITED**

D7 of the abstraction decision record is BINDING: "no lift into `Foundations/`". Reuse check
re-run for this task: `Cslib/Foundations/Logic/Tableau/` contains `Sign`, `SignedFormula`,
`RuleResult`, `Branch`, `Closure`, `ClosureCondition`, `Measure`, `PropositionalRules`; no
existing typeclass (`LTS`, `HasImp`, `HasBox`, `HasBot`, `HasDia`, `HasTop`) carries a
persistence, filtration, or termination-measure notion. There is nothing there to extend.

---

## 8. Recommendation **[revised]**

**The per-regime split is the correct steady state, and no new driver-level abstraction should be
built before the 8-corner expansion.** The abstraction the task hypothesised already exists
(`Aux`); the state generalisation already exists (`RuleApplySt`); the one further generalisation
anyone has actually measured came out at **+80 lines / 40 proof sites**; and §6.2 supplies a
positive argument the first draft did not have — the split is what made S4's soundness repair
possible at all.

**But the expansion should be re-tranched**, for a reason orthogonal to duplication: two of its
eight corners target a regime whose reference implementation does not yet yield a decision
procedure. That gate is now known to be light.

Two concrete actions, and one thing to *not* do:

1. **Finish S4 to the six-corner standard** — the six-item, ~580-line, four-phase port of §6.1.
   **This is action 1, it depends on nothing in this report, and task 511 is already unblocked to
   do it.** Until it lands there is no Tier-C template to replicate.
2. **Prototype the universal-cluster rule combinator on exactly one pair** (§7.2,
   `Kb5''`-from-`Five`) and measure the re-cut proof sites before generalising to three. Gate the
   Tier-B corners of the expansion on that measurement, not on the design's plausibility.
3. **Do not build the traversal rung yet** (§7.3). It is not on the critical path, and a
   sound-by-construction version costs more than the ~155 lines it was first sized at, because it
   must carry the ordering obligation §6.2 identifies. Revisit if and when a second scheduling
   regime appears.

Actions 1 and 2 are fully independent and can run in parallel.

**Change from the first draft**: the traversal rung was action 1 and S4 completion depended on it.
Both were wrong — S4 completion is independent, and the rung is optional. Only actions 1 and 2
survive.

---

## 9. What the Expansion Task Should Do

Task 548's eight corners do not form one workstream. Split them by tier and gate them
differently.

| Corner | Frame conditions | Assessed tier | Template | Gate |
|---|---|---|---|---|
| TB | refl + symm | **A** | `TDriver` + `BDriver` composition | none — proceed now |
| D | serial | **A** (assessed) | `TDriver` | none — proceed now |
| DB | serial + symm | **A/B** (assessed) | `BDriver` | none — proceed now |
| K45 | trans + eucl | **B** (assessed) | `FiveSimplification` rooted-cluster | gate on §7.2 prototype |
| D5 | serial + eucl | **B** (assessed) | `FiveSimplification` | gate on §7.2 prototype |
| D45 | serial + trans + eucl | **B** (assessed) | `FiveSimplification` | gate on §7.2 prototype |
| **K4** | trans | **C** | S4 loop-checking | **gate on S4 completion (§8.1) — light, already unblocked** |
| **D4** | serial + trans | **C** | S4 loop-checking | **gate on S4 completion (§8.1) — light, already unblocked** |

**Tier assignment caveat, stated rather than hidden**: the A/B/C assignment above for the *new*
corners is an assessment from the frame conditions and the existing templates, not a measured
fact. The load-bearing part is the K4/D4 gating, which follows from transitivity alone
(`GenericDriver.lean:127-130` records that transitive box propagation falsifies `rankStep`, and
S4 is the only transitive corner in the tree). The K45/D45/D5 placement in Tier B rests on those
frames being rooted-cluster logics addressable by the `FiveSimplification` technique — plausible
from `FiveSimplification.lean`'s own §References (Blackburn §4.5/§6.6 on K5 and the rooted normal
form for K45/S5-adjacent systems) but **not verified here**. Whichever way it falls, the D/DB/TB
tranche and the K4/D4 gate are unaffected.

Expected cost under this split, using §4.2's measured per-corner figures: the ungated tranche
(TB, D, DB) ≈ 5,000–6,000 lines. The Tier-B tranche ≈ 10,800 lines as-is, or materially less if
§7.2's prototype succeeds. The Tier-C tranche is not estimable until S4 is finished, and
attempting it before then would replicate an unfinished 13,540-line template twice.

**A specific warning for the Tier-C tranche, from §4.3 and §6.2.** The S4 cluster currently
carries *two* parallel stepper stacks (unordered and ordered) at a measured cost of 3,801 lines
across 14 twin pairs. That duplication exists because the ordered driver was built alongside the
unordered one during a soundness repair; `LoopChecking.lean:188-189` already earmarks retiring the
unordered stack as a separate destructive phase, and task 511 explicitly holds it out of scope.
**K4 and D4 must be templated on the ordered stack only, after that retirement — not on the
current two-stack state.** Cloning the present S4 cluster twice would replicate the retirement
debt as well as the machinery.

**Explicitly: do not reduce the expansion to "add 8 corners with the existing machinery". Do
reduce it to "add 3 corners now, 3 after a measured prototype, and 2 after S4 is finished and its
unordered stack retired".**

---

## 10. Relationship to Task 511 **[revised]**

The first draft of this section answered task 511's *handoff* question — whether the abstraction
should accommodate its state-threading need — and recommended a retarget. Task 511's own research
has since completed and supersedes both that handoff and this section's original advice. Its
report is the authority on S4's status; this section records only what bears on the abstraction
decision.

**Agreements** (reached independently, from the same tree at the same HEAD):

- Route (b) — generalising the driver framework to thread opaque per-branch state — is **moot for
  closing S4**, and partly landed anyway as the `RuleApplySt` ladder.
- The soundness/completeness split across two drivers is real, and the unordered keyed driver's
  soundness is *false*, not merely unproven.
- No further driver abstraction is worth building on S4's account.

**Where task 511 corrects this report** (its evidence is stronger — it ran the builds):

- The remaining S4 work is a **bounded ~580-line, six-item, four-phase port**, not an open-ended
  reconnection. This report's §6 first framed it as a heavy precondition; that was an overstatement
  and is corrected in §6.1.
- **The traversal rung is not needed for it.** This report's original §7.3 asserted the rung was
  the precondition for closing S4's completeness. It is not: the port runs against already-landed
  ordered lemmas. §7.3 is re-costed and downgraded accordingly.
- Task 511 should proceed to `/plan` on its own four-phase shape. This report's earlier "retarget
  and take the rung as a dependency" advice is **withdrawn**.

**What this report contributes back to task 511** (§6.2, §4.3, §9): the ordering discipline its
Phase 2-3 ports depend on is not merely a scheduling detail — it is the soundness-carrying content
of the ordered driver, and it is the reason a shared traversal abstraction would have obstructed
rather than helped. And the two-stack duplication its work adds to (3,801 lines across 14 twin
pairs, +2 more ~250-line twins from its own Phases 2-3) is the strongest argument for sequencing
the `LoopChecking.lean:188-189` retirement of the unordered stack **before** K4/D4 are templated
on this cluster — a point that belongs to the expansion task, not to 511, and which 511 correctly
holds out of scope.

---

## 11. Zero-Debt and Constraint Compliance

- **No `.lean` file was created, moved, or edited.** This task is research/decision only, per its
  own description and the absence of a `file_scope` in `state.json`.
- **No sorry-deferral, no axiom introduction, no vacuous placeholder is recommended anywhere in
  this report.** Where a route is not closable, it is gated (§8.1) or rejected with a measurement
  (§7.5), not deferred behind a `sorry`.
- **D7 honoured**: no lift into `Foundations/` is proposed (§7.6); the one recommended abstraction
  change (§7.2) is de-duplication-shaped, and every driver-level change is deferred (§7.3, §7.4)
  or rejected (§7.5).
- **D5 honoured**: no module split or re-cut is proposed. The `S4/` seam table shipped under task
  565 and is not re-litigated here.
- **Subsystem sorry census**: 0 in `Cslib/Logics/Modal/Tableau/` per the README's own reproducible
  command; not re-run here, and not relied on by any conclusion above.

## 12. Limits of This Report

Stated rather than papered over.

- **No `lake build` was run by this task.** Every claim originating here is from source reading,
  `grep`, and declaration-span analysis of the tree at `5ea7152c`. The build-verified facts cited
  in §6.1 (both modules green; `modalTableauS4KeyedOrdered_sound` with an empty axiom list; the
  probed-green `_none_saturated` one-liner) are **task 511's measurements, adopted, not
  independently reproduced here**. They are attributed at their point of use.
- **This report was revised mid-flight** after task 511's research landed. Three conclusions
  changed (§6, §7.3, §10) and one was added (§6.2). The superseded positions are stated rather
  than silently replaced, so a reader can see what moved and why: the traversal rung was
  originally recommended as small and on the critical path, and finishing S4 was originally
  presented as depending on it. Both were wrong.
- **The similarity figures (§4.3) are textual**, computed by `difflib.SequenceMatcher` over
  tag-normalised declaration bodies. They measure *how much of a clone family a combinator would
  have to reconcile*, not *how many proof steps would survive the abstraction*. That second
  number can only come from §7.2's prototype, which is why the recommendation gates on the
  prototype rather than on these figures.
- **The tier assignment for the eight new corners (§9) is an assessment, not a measurement** —
  flagged inline there.
- **Task 564's "+80 lines / 40 proof sites" is quoted from its summary**, not independently
  re-measured here. It is load-bearing for §7.5, so it should be re-verified if §7.5 is ever
  revisited.
- The two "figures deliberately NOT re-measured" in the subsystem README (the 4-decl/1,036-line
  and 43-decl/1,983-line amplification figures) are unverified inheritances there and are **not
  used anywhere in this report**.

---

## References

- `Cslib/Logics/Modal/Tableau/GenericDriver.lean` — `RuleApplicationSpecCore` / `RuleApplicationSpec`
- `Cslib/Logics/Modal/Tableau/Saturation.lean:107-395` — the generic driver; `:493-758` — the `RuleApplySt` ladder
- `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean:230-430`, `:1410` — the `Aux` parametrization and the parametric top-loop Hintikka lemma
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean:1709` — `modalApplyOneS5_rankStep_not_dischargeable`; `:1732ff` — the R7 fuel-domination refutation
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:4085-4103` — the S4Keyed soundness refutation and decidability scope note
- `Cslib/Logics/Modal/Tableau/S4/Driver.lean:631` — `modalStepBranchS4KeyedOrdered`; `:2449` — `modalExpandBranchesGenSt_eq_S4Keyed`
- `Cslib/Logics/Modal/Tableau/README.md` — subsystem measured baseline (each figure with its reproducing command)
- `specs/archive/561_tableau_abstraction_decision_record/decisions/01_abstraction-decision-record.md` — D3 (§6, six-step migration order), D5 (§8), D7 (§10)
- `specs/archive/564_tableau_s4keyed_migration_st_ladder/summaries/` — the +80-line / 40-site measurement and the KeyedOrdered scope exclusion
- `specs/511_s4_loop_checking_termination/reports/03_head-reverification-ordered-driver.md` — **the current authority on S4's status**; supersedes that task's earlier handoff. Source for §6.1's six-item / ~580-line scope, the build and axiom verifications, and the settled-context framing in §6.2
- `specs/511_s4_loop_checking_termination/.orchestrator-handoff.json` — **superseded** by the report above; retained only as the record of the earlier live-guard/keyed-guard framing
- `CslibTests/S4LoopGuardRegression.lean` — the executable S4Keyed soundness countermodel
