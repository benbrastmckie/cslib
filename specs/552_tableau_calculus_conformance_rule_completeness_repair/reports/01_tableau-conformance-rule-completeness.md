# Report 01 — Tableau Calculus Conformance and Rule-Completeness Repair

- **Task**: `552 - tableau_calculus_conformance_rule_completeness_repair`
- **Started**: `2026-07-24T14:30:00-07:00`
- **Completed**: `2026-07-24T15:41:44-07:00`
- **Effort**: hard-mode research dispatch (H2 anti-analysis, H3 reference grounding, H4 adversarial verification)
- **Dependencies**: none blocking. Consumes findings from tasks 425 and 317; both are recorded, not re-derived.
- **HEAD verified against**: `3c4b580f270d299f45b00cfd2094b22aec0af14c`
- **Sources/Inputs**: see the Sources/Inputs section below
- **Artifacts**: `specs/552_tableau_calculus_conformance_rule_completeness_repair/reports/01_tableau-conformance-rule-completeness.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

### Sources/Inputs

Source files read this dispatch (all claims below cite these directly):

- `Cslib/Logics/Temporal/Tableau/Rules.lean` (709 lines, read in full)
- `Cslib/Logics/Temporal/Tableau/Saturation.lean` (`:1-360`, `:520-570`, `:1010-1034`, declaration index)
- `Cslib/Logics/Temporal/Tableau/Soundness.lean` (`:75-120`, `:196-221`, declaration index)
- `Cslib/Logics/Temporal/Tableau/Branch.lean` (`:55-178`)
- `Cslib/Logics/Temporal/Tableau/TimeOrdering.lean` (`:55-120`, `:219-262`)
- `Cslib/Logics/Temporal/Semantics/Validity.lean` (`:1-80`)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` (272 lines, read in full)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (500 lines, read in full)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (`:74-134`, `:480-535`, `:556-570`, `:2828-2852`)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (declaration index, `:83-110`)
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (`:4300-4370`)
- `CslibTests/ModalFrameSeparation.lean` (read in full), `CslibTests/HilbertSearch.lean` (`:1-60`), `CslibTests.lean`, `lakefile.toml`

Prior-artifact evidence anchors:

- `specs/425_temporal_tableau_ptl_fmp_decidability/reports/04_island-vs-periodic-strategic-decision.md`
- `specs/425_temporal_tableau_ptl_fmp_decidability/reports/03_blocker-reassessment-remaining-obligations.md`
- `specs/317_propositional_tableau_completeness/.orchestrator-handoff.json`, `plans/06_route-a-frame-plumbing.md`, `specs/state.json:518`

Executed evidence produced this dispatch: three throwaway `CslibTests/Scratch552{,b,c}.lean` files run
under `lake env lean`, then deleted. 44 executed verdicts and 3 fuel tables are transcribed below.

### Artifacts

- This report.

### Standards

status-markers.md, artifact-management.md, tasks.md, report-format.md

---

## Executive Summary

- **All six deliverables' premises hold at HEAD.** Every claimed line range and every claimed numeric
  constant was confirmed by reading the file. Nothing in the task description is stale.
- **A seventh, larger defect exists that the six deliverables do not cover**: `temporalApplyNeg`
  (`Rules.lean:287-349`) has **no `asAllFuture?`/`asAllPast?` arm at all**, despite the module
  docstring's rule table (`Rules.lean:27-28`) advertising `allFutureNeg`/`allPastNeg` "by duality".
  Six additional linear-order validities were executed to `OPEN` this dispatch. Deliverable 2's
  seriality rule does **not** fix them.
- **Deliverable 6 is upgraded from a proof-gap to a red test.** No prior artifact had an executed
  propositional counterexample. Three IPC-valid formulas return `OPEN` at HEAD:
  `((a→b)→(a→c)) → (a→(b→c))`, `¬¬¬a → ¬a`, `((a→b)→c) → (b→c)`.
- **Deliverable 6's prescribed remedy is over-scoped.** Prior artifacts prescribe a Lindenbaum-style
  "decide every `ξ ∈ Sub(φ0)` at every world" completion rule. The standard Fitting `T(→)` branching
  rule `T(φ→ψ)@w → [F(φ)@w'] | [T(ψ)@w']` is strictly cheaper and **sufficient**: it yields exactly
  the disjunction `truthLemma`'s T-imp case needs. All three counterexamples close under it; traces
  given in Finding 6.
- **The conformance harness mechanism is settled and empirically verified.** `#eval` in
  `CslibTests/` works; `decide`/`native_decide`/kernel reduction does not. The file needs *both*
  `import X` and `public meta import X` for the same module — verified against the exact elaborator
  errors.
- **Deliverable 3's `k = 4` cut is a rule defect, not fuel exhaustion.** New discriminating
  measurement: at fuel `20000` (vs. shipped `~50-500`), `𝐅q → 𝐅^k ⊤` is still `OPEN` for `k ≥ 4`.

---

## Context & Scope

Two independent formalization fronts converged on the same defect class: a tableau rule set too weak
to close valid formulas, plus fuel machinery justified by a bound that does not hold. This dispatch
verifies each of six proposed repairs against HEAD, establishes the conformance-harness mechanism,
names the concrete soundness re-audit obligations, and orders the work.

Constraints observed: zero-debt (no `sorry` deferral recommended anywhere below); CSLib reuse-first
(existing abstractions identified before any new definition is proposed); no task-number citations in
any deliverable file outside `specs/**`.

---

## Source-to-Implementation Mapping (H3, Tier 1 + Tier 3)

Reference grounding tier: **mixed Tier 1 / Tier 3**. Tier 1 (literature-backed) for the two rule
additions; Tier 3 (implementation-backed) for the harness, fuel, and tracker deliverables.

BibKey verification status: `references.bib` contains `Reynolds1994` (cited at `Rules.lean:44`,
`Saturation.lean:45`), `Fitting1983` and `ChagrovZakharyaschev1997` (cited at
`Propositional/.../Rules.lean:53-54`, `Expansion.lean:57-58`), `GargGenoveseNegri2012` (cited at
`Expansion.lean:189-190`), `Burgess1982I` (cited at `Soundness.lean:93`). All five BibKeys appear in
in-tree docstrings in the exact `[Key]` citation form the repo uses; none needed to be added.

| Source claim | BibKey / anchor | Lean target | Translation notes |
|---|---|---|---|
| Tense tableau needs an explicit **seriality** step: every time gets a successor and predecessor before saturation | `Reynolds1994` (`Rules.lean:44`) | new arm in `temporalApplyPos` / `temporalApplyOne`, `Rules.lean:219-284` | Sound only against `branchSat`'s frame class, which already mandates `NoMaxOrder`/`NoMinOrder` (`Soundness.lean:99`). NOT sound for `Temporal.valid` (`Validity.lean:76-80`). See Risk R1. |
| Duality `F(𝐆φ)@t ≡ T(𝐅¬φ)@t`, `F(𝐇φ)@t ≡ T(𝐏¬φ)@t` | `Reynolds1994`; advertised in-tree at `Rules.lean:27-28` | **missing** — `temporalApplyNeg` (`Rules.lean:287-349`) has only `asUntl?`/`asSnce?` arms | Deliverable-gap. See Finding 2b. |
| `𝐆` propagation must reach *all* future times, not just direct successors | `Reynolds1994` | `futureOf` = direct constraints only (`TimeOrdering.lean:92-94`); `ancestorTimes` (`:117`) is an unused hook | Deliverable-gap. See Finding 2c. |
| Persistent `T(A→B)` rule copies to every accessible world **and there splits `F(A) ∣ T(B)`** | `Fitting1983` Ch. 4 (cited `Propositional/.../Rules.lean:53`); same row appears in task 317 `reports/08:30` | `intTImpRule` (`Propositional/.../Rules.lean:174-186`) — implements the copy, **drops the split** | The split is the whole of Deliverable 6. Literature already has it. |
| `Sfor`-containment termination for world creation | `GargGenoveseNegri2012` (`Expansion.lean:189-190`) | `intFImpReuseWitness?` (`Expansion.lean:263-291`) | Already landed; must be re-derived for the enlarged rule set (Finding 6d). |
| Discreteness axiom separates `validDiscrete` from `valid` | `Burgess1982I` §1.5, §2 (`Soundness.lean:93`) | `branchSat` frame class (`Soundness.lean:95-106`) | Fixes the correct validity target for the temporal tableau. See Decision D1. |

---

## Findings

### Finding 0 — Executed conformance baseline (the missing asset, produced here)

44 verdicts executed against unmodified `Cslib/` at HEAD via `#eval` under `lake env lean`. `✓` =
verdict matches the semantics; `✗` = defect.

**Temporal** (`temporalTableau`, `Formula Nat`):

| Formula | Verdict | Expected | |
|---|---|---|---|
| `p → p` | CLOSED | CLOSED | ✓ |
| `p` | OPEN | OPEN | ✓ |
| `𝐆p → p` | OPEN | OPEN | ✓ (`𝐆` is over *strictly* future) |
| `𝐅p → 𝐅p` | CLOSED | CLOSED | ✓ |
| `𝐆p → 𝐅p` (D, future seriality) | OPEN | CLOSED | ✗ |
| `𝐇p → 𝐏p` (D, past seriality) | OPEN | CLOSED | ✗ |
| `𝐆p → 𝐆𝐆p` (4, transitivity) | OPEN | CLOSED | ✗ |
| `𝐇p → 𝐇𝐇p` | OPEN | CLOSED | ✗ |
| `p → 𝐆𝐏p` (conversion) | OPEN | CLOSED | ✗ |
| `p → 𝐇𝐅p` (conversion) | OPEN | CLOSED | ✗ |
| `𝐆¬p → (𝐆p → 𝐆⊥)` (K for `𝐆`) | OPEN | CLOSED | ✗ |
| `¬𝐆p → 𝐅¬p` (`𝐆`/`𝐅` duality) | OPEN | CLOSED | ✗ |
| `𝐆p → 𝐅^k p`, `k = 1..5` | OPEN (all) | CLOSED | ✗ |
| `𝐅^k p → 𝐅^k p`, `k = 0..6` | CLOSED (all) | CLOSED | ✓ |

**Propositional** (`intuitionisticTableau`, `Proposition Nat`):

| Formula | Verdict | Expected | |
|---|---|---|---|
| `a → a` | CLOSED | CLOSED | ✓ |
| `a → (b → a)` | CLOSED | CLOSED | ✓ |
| `b → (a → b)` | CLOSED | CLOSED | ✓ |
| `((a→b) ∧ a) → b` | CLOSED | CLOSED | ✓ |
| `¬(a ∧ ¬a)` | CLOSED | CLOSED | ✓ |
| `(a→(b→c)) → ((a→b)→(a→c))` (K) | CLOSED | CLOSED | ✓ |
| `(¬a ∨ b) → (a → b)` | CLOSED | CLOSED | ✓ |
| `(a→b) → (¬b → ¬a)` | CLOSED | CLOSED | ✓ |
| `(a→c) → ((b→c) → ((a∨b)→c))` | CLOSED | CLOSED | ✓ |
| `(a ∧ (b∨c)) → ((a∧b) ∨ (a∧c))` | CLOSED | CLOSED | ✓ |
| `(a→b) → ((b→c)→(a→c))` | CLOSED | CLOSED | ✓ |
| **`((a→b)→(a→c)) → (a→(b→c))`** | **OPEN** | CLOSED | **✗** |
| **`¬¬¬a → ¬a`** | **OPEN** | CLOSED | **✗** |
| **`((a→b)→c) → (b→c)`** | **OPEN** | CLOSED | **✗** |
| `((a→b)→a) → a` (Peirce) | OPEN | OPEN | ✓ |
| `(a→b) ∨ (b→a)` (Dummett) | OPEN | OPEN | ✓ |
| `¬(a∧b) → (¬a ∨ ¬b)` | OPEN | OPEN | ✓ |
| `¬a ∨ ¬¬a` (weak EM) | OPEN | OPEN | ✓ |
| `(¬a→(b∨c)) → ((¬a→b) ∨ (¬a→c))` (Kreisel-Putnam) | OPEN | OPEN | ✓ |

All three propositional `✗` rows are IPC-valid; each is a one-line natural-deduction derivation.
`¬¬¬a → ¬a` is textbook. `((a→b)→c) → (b→c)`: from `b`, weakening gives `a→b`, hence `c`.
`((a→b)→(a→c)) → (a→(b→c))`: from `b`, weakening gives `a→b`, hence `a→c`, with `a` gives `c`.

**Actionable directive**: these 44 rows, with a `String`-valued verdict adapter, are the corpus for
Deliverable 1. The 12 `✗` rows are the red tests the repair must flip; the 32 `✓` rows are the
regression guard the repair must not break.

### Finding 1 — Conformance harness: mechanism established (Deliverable 1)

- **Kernel reduction is out.** `decide`/`native_decide`/`rfl` stall on these decision procedures.
  Documented at `CslibTests/ModalFrameSeparation.lean:19-35`: *"they reduce through
  `modalExpandBranchesGen`'s nested `let rec`, which compiles to `WellFounded.fix` and does not
  reduce in the kernel, so `decide` gets stuck."* `intExpandBranches` still uses a nested
  `let rec go` (`Expansion.lean:357`), so the propositional side is in the same position.
  `Cslib/Logics/Modal/Tableau/LoopChecking.lean:4331-4341` independently records that `#eval`/
  `#guard`/`native_decide` do not elaborate inside `Cslib/Logics/.../Tableau/` files at all.
- **`#eval` in `CslibTests/` works.** Verified this dispatch end-to-end: 44 verdicts and 3 fuel
  tables were produced this way. The non-obvious requirement, verified against the exact elaborator
  errors, is that the harness file needs **both** import forms for the same module:
  - plain `import X` — without it: `Invalid definition 'p', may not access declaration
    'Formula.atom' imported as 'meta'`;
  - `public meta import X` — without it: `Invalid 'meta' definition '_eval', 'temporalTableau' is
    not accessible here`.
  Four modules are needed on both lines: `Cslib.Logics.Temporal.Tableau.Saturation`,
  `Cslib.Logics.Temporal.Syntax.Formula`,
  `Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion`, `Cslib.Logics.Propositional.Defs`.
- **Assertion form**: `#guard_msgs in #eval` — the established in-repo idiom
  (`CslibTests/LTS.lean:125,129,135,139`; `CslibTests/Reduction.lean:48-66`;
  `CslibTests/HasFresh.lean:38-58`). Plain `#guard` is not usable: `TemporalTableauResult`
  (`Saturation.lean:63-67`) and `IntTableauResult` (`Expansion.lean:75-79`) derive neither `Repr`
  nor `BEq`. A verdict adapter is required, e.g. `def verdict : TemporalTableauResult Atom → String
  | .closed => "CLOSED" | .openBranch _ _ => "OPEN"`, defined in the harness file (not in `Cslib/`).
- **Wiring**: `lakefile.toml:4` sets `testDriver = "CslibTests"`, so `lake test` runs the library.
  A new `CslibTests/TableauConformance.lean` must be added to the `CslibTests.lean` barrel
  (`public import CslibTests.TableauConformance`, alphabetical position after `CslibTests.Reduction`).
- **Reuse check**: no existing conformance/execution harness for decision procedures exists in
  `Cslib` or `CslibTests`. `CslibTests/ModalFrameSeparation.lean:46-78` is the closest precedent but
  asserts via *proof terms* (`modalTableauKb5''_complete _ …`), which requires the completeness
  theorem to already exist — unavailable here. The `#guard_msgs in #eval` route is the only one open.

**Actionable directive**: create `CslibTests/TableauConformance.lean` with the dual-import header,
two verdict adapters, and the Finding 0 corpus as `#guard_msgs in #eval` assertions; add to
`CslibTests.lean`. It must be **red on 12 rows** at creation time.

### Finding 2 — Temporal seriality (Deliverable 2): CONFIRMED, and insufficient as scoped

**2a. The claim holds exactly.**
- `Rules.lean:226-234`: the `asAllFuture?` arm maps over `ord.futureOf t`; when `newForms.isEmpty`
  it returns `(.notApplicable, ord)`. `Rules.lean:236-244`: symmetric for `asAllPast?`/`ord.pastOf`.
- `Rules.lean:312`: `if futureTimes.isEmpty && ord.timeCount > 0 && ord.timeCount < 4`. At the root
  `ord = TimeOrdering.empty` (`TimeOrdering.lean:73`, `constraints := []`), so
  `timeCount = allTimes.length = 0` (`TimeOrdering.lean:111-112`) and the conjunct is false.
- The description cites only `:312`; **there is a second, symmetric site at `Rules.lean:338`**
  (`snceNeg`). Both must be edited.
- Only the four positive existential rules (`someFuturePos` `:247-253`, `somePastPos` `:256-262`,
  `untlPos` `:265-272`, `sncePos` `:275-282`) ever call `addFuture`/`addPast`. Executed
  confirmation: `𝐆p → 𝐅p` and `𝐇p → 𝐏p` both `OPEN` (Finding 0).

**2b. `temporalApplyNeg` has no `𝐆`/`𝐇` arm at all — not covered by any deliverable.**
`temporalApplyNeg` (`Rules.lean:287-349`) matches `asUntl?`, then `asSnce?`, then falls through to
`(.notApplicable, ord)` at `:349`. `allFuture`/`allPast` are **primitive constructors**
(`Syntax/Formula.lean:112,115`), so `asUntl?` does not see them. Therefore `F(𝐆φ)@t` and `F(𝐇φ)@t`
fire *no rule whatsoever*. The module docstring's own rule table advertises them:

> `| allFutureNeg | F(Gφ)@t | = T(F¬φ)@t | (by duality) |` — `Rules.lean:27`

Executed consequences (Finding 0): `¬𝐆p → 𝐅¬p`, `𝐆¬p → (𝐆p → 𝐆⊥)`, `𝐆p → 𝐆𝐆p`,
`𝐇p → 𝐇𝐇p` all `OPEN`. A seriality rule alone fixes **none** of them: they need `F(𝐆·)` to
produce a fresh witness time.

**2c. `futureOf` is direct-successor only.** `TimeOrdering.lean:92-94`:
`futureOf ord t = ord.constraints.filterMap fun (a,b) => if a == t then some b else none`. So even
after seriality, `T(𝐆p)@0` propagates to the immediate successor only, never transitively —
`𝐆p → 𝐆𝐆p` stays `OPEN`. `ancestorTimes` (`TimeOrdering.lean:117-122`) exists and is documented as
*"the hook for Phase 8 (Completeness) if transitive closure is needed. The default rules use
`futureOf` (direct successors)."* It is consumed only by `isTemporallyBlocked` (`Branch.lean:164`),
never by a rule.

**Actionable directive**: Deliverable 2 must be widened to three coordinated edits in
`Rules.lean` —
(i) a seriality arm in `temporalApplyPos` firing when `ord.futureOf t = []` (resp. `pastOf`),
creating one fresh time via `addFuture`/`addPast` + `propagateToFuture`/`propagateToPast`
(`Rules.lean:185-214`), gated on `¬ isTemporallyBlocked b t ord tracker` (`Branch.lean:160-167`)
for termination;
(ii) `asAllFuture?`/`asAllPast?` arms in `temporalApplyNeg` implementing the advertised duality;
(iii) `allFuturePosAt`/`allPastPosAt` propagation (`Rules.lean:124-139`) switched from `futureOf` to
the transitive `ancestorTimes` — **or** the seriality rule made to re-fire so the persistent `𝐆`
rule reaches transitively via chained direct steps. Option (iii)-a is the smaller change; (iii)-b
risks non-termination.

### Finding 3 — Temporal time cap (Deliverable 3): CONFIRMED, and it is a rule defect not fuel

- `Rules.lean:312` and `Rules.lean:338` both carry `&& ord.timeCount < 4`. `timeCount` is
  `allTimes.length` (`TimeOrdering.lean:111-112`), documented at `TimeOrdering.lean:107-110` only as
  *"a gating condition to bound Reynolds co-decomposition"* — no justification.
- Executed reproduction of the report-04 probe family `φ_k := 𝐅q → 𝐅^k ⊤` (valid for every `k`):

  | k | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
  |---|---|---|---|---|---|---|---|---|
  | shipped fuel | CLOSED | CLOSED | CLOSED | CLOSED | **OPEN** | **OPEN** | **OPEN** | **OPEN** |
  | fuel = 20000 | CLOSED | CLOSED | CLOSED | CLOSED | **OPEN** | **OPEN** | **OPEN** | **OPEN** |

- **New discriminating result**: the second row is not in any prior artifact. Raising fuel by ~40×
  changes nothing, so the `k = 4` cut is **not** fuel exhaustion; it is the `timeCount < 4` cap. This
  cleanly separates Deliverable 3 from Deliverable 4 and gives each an independent acceptance gate.

**Actionable directive**: delete `&& ord.timeCount < 4` from `Rules.lean:312` and `:338`. Because
this removes the only bound on time creation, it **must land in the same phase** as the
subset-blocking gate from Finding 2 and the fuel decision from Finding 4 — see Decision D3.

### Finding 4 — Temporal fuel (Deliverable 4): CONFIRMED; only "raise the constant" is viable now

- `Saturation.lean:76-78`: `temporalFuel φ = let n := subformulaCount φ; (4*n+4)*(n+2)+2`. Expanding:
  `4n² + 8n + 4n + 8 + 2 = 4n² + 12n + 10`. The description's constant is exact.
- `Saturation.lean:71-75` (the docstring immediately above): *"the number of distinct time types is
  bounded by `2^n` where `n` is the number of subformulas, so the tableau depth is also bounded."*
  A quadratic cannot cover a `2^n` bound. The non sequitur is on the face of the definition.
- **Independent measurement this dispatch** (different family from report 04's, so this is
  corroboration not restatement). Family `⋀_{i≤k}(a_i ∨ ¬a_i) → (a_0 ∨ ¬a_0)`, `2^k` closing
  branches, purely propositional (so Findings 2/3 cannot influence it):

  | k | `subformulaCount` | `temporalFuel` | minimal sufficient fuel |
  |---|---|---|---|
  | 0 | 5  | 170  | 1   |
  | 1 | 11 | 626  | 14  |
  | 2 | 17 | 1370 | 32  |
  | 3 | 23 | 2402 | 68  |
  | 4 | 29 | 3722 | 140 |

  From `k = 2`: `68 = 2·32 + 4`, `140 = 2·68 + 4` — minimal fuel is `9·2^k − 4`, exponential.
  `subformulaCount = 6k + 5`, so `temporalFuel = Θ(k²)`. Curves cross near `k ≈ 11`
  (`9·2^11 − 4 = 18428` vs `temporalFuel = 17424`), consistent with report 04's `k ≈ 12` estimate on
  its own family. **The bound is false at the current constant.**

- **Viability of the two remedies:**
  - *Raise the constant* — **viable and cheap.** `temporalFuel` is a plain `def` with exactly three
    consumers: `temporalTableau` (`Saturation.lean:538`), `temporalTableau_instantStrict`
    (`:551`), `temporalTableau_trackerBranchFaithful` (`:1002`). The latter two pass it as an
    opaque `Nat` to `run_level_P1`/`run_level_faithful`, which are proved by induction on the fuel
    argument and are **numerically agnostic**. Changing `(4*n+4)*(n+2)+2` to `2^(2*n+2)` breaks
    nothing at HEAD. Two docstring references (`Completeness.lean:93`, `:124`) must be corrected.
  - *Add deduplication* — **not viable as a standalone fix now.** The dedup device already exists
    (`timeType` `Branch.lean:113-118`, `isSubsetBlocked` `:120-123`) but is consulted only at
    *closure* time via `isTemporallyBlocked` (`:160-167`) → `findBlockedTime` (`:171-174`), never as
    a fresh-time *suppressor* in `Rules.lean`. Wiring it as a suppressor is exactly the
    termination gate Finding 2 already requires, and `isTemporallyBlocked`'s second conjunct is
    `allEventualitiesFulfilledOrDuplicated` (`Branch.lean:146-152`), which reads the tracker —
    which is broken (Finding 5). So dedup depends on Deliverable 5.

**Actionable directive**: raise `temporalFuel` to `2 ^ (2 * subformulaCount φ + 2)` at
`Saturation.lean:78`, rewrite the docstring at `:71-75` to state the exponential bound it now
matches, and correct `Completeness.lean:93,124`. Pursue dedup as the *termination gate* under
Deliverable 2, not as the fuel fix.

### Finding 5 — Temporal trackers (Deliverable 5): CONFIRMED exactly; full call-site list

- `Saturation.lean:156-158`, `.branching` arm, verbatim:
  ```
  | .branching branches =>
    let newBranches := branches.map (· ++ b)
    some (newBranches, newBranches.map (fun _ => expanded ++ [sf]), newOrd, tracker)
  ```
  `tracker` returned unchanged. Contrast `.linear` (`:150-155`) and `.persistent` (`:159-165`),
  both of which run `registerEventualities … |> fulfillEventualities …`. Since `untlPos`/`sncePos`
  are branching (`Rules.lean:265-282`), the recurring copy `⟨.pos, φ, t'⟩` emitted as `branch2`'s
  second element (`Rules.lean:271`, `:281`) is never registered pending.
- `Saturation.lean:300-303`: `doneTrack ++ newBs.map (fun _ => newTracker) ++ restTracks` —
  one tracker replicated across all output branches. `untlPos`'s `branch1` fulfils the eventuality
  and `branch2` defers it, so their pending sets genuinely differ.
- **Required signature change** (`Saturation.lean:139-144`):
  ```
  Option (List (TBranch Atom) × List (TBranch Atom) × TimeOrdering × List (EventualityTracker Atom))
  ```
- **Complete call-site list** (`temporalStepBranch` occurrences in `Cslib/`):
  | Site | What changes |
  |---|---|
  | `Saturation.lean:139` | the definition; all four arms must emit a per-branch tracker list |
  | `Saturation.lean:181-221` | `temporalStepBranch_preserves` — hypothesis `h`'s shape, and `obtain ⟨rfl, -, rfl, -⟩` destructuring in all four `cases result` arms |
  | `Saturation.lean:293-304` | `processNext` — replace `newBs.map (fun _ => newTracker)` with the returned list |
  | `Saturation.lean:504-509` | `run_level_P1`'s `cases hstep : temporalStepBranch …` |
  | `Saturation.lean:703-776` | `temporalStepBranch_preserves_faithful` |
  | `Saturation.lean:777-791` | `WorklistInvFaithful` / `ResultInvFaithful` |
  | `Saturation.lean:885-1006` | `processNext_mismatch_closed_faithful`, `run_level_faithful`, `temporalTableau_trackerBranchFaithful` |
  Docstring-only references at `Soundness.lean:36,44` and `Completeness.lean:69,78,87,102,646`
  need text updates, not proof work.
- **Regression warning**: registering eventualities makes `findEventualityDefect` (`Closure.lean`)
  start firing, changing which branches close. Every `✓ CLOSED` row in Finding 0 must be re-run.
  This is precisely what Deliverable 1 buys.

### Finding 6 — Propositional T-implication (Deliverable 6): CONFIRMED, upgraded, and de-scoped

**6a. Source claim holds exactly.** `intTImpRule` (`Propositional/.../Rules.lean:174-186`) emits only
`some ⟨.pos, ψ, w'⟩` — never a `.neg` tag. `intApplyRuleFull` (`:245-268`) has cases for `T∧`, `F∧`,
`T∨`, `F∨`, `F→` and no `.pos, .imp` case (comment at `:265`: *"handled separately (persistent rule,
not a standard step)"*). Five decomposition rules + one world-creating rule = the "6-rule calculus".
`IBranchSaturation` (`Scheme.lean:74-101`) has exactly five fields — `sat_tand`, `sat_fand`,
`sat_tor`, `sat_for_`, `sat_fimp` — **no `sat_timp`**. The in-tree blocker note at
`Scheme.lean:2828-2850` states the gap and prescribes *"a Lindenbaum-style 'decide `ξ` at `w'`'
branching step for every `ξ ∈ Sub(φ0)` not yet tagged at a freshly created world."*

**6b. Upgraded to an executable verdict defect.** No prior artifact has an executed propositional
counterexample; the gap was recorded only as a proof obstruction. Three IPC-valid formulas return
`OPEN` at HEAD (Finding 0). Trace for `¬¬¬a → ¬a`: `F(¬¬¬a → ¬a)@0` creates `w1` with `T(¬¬¬a)`,
`F(a→⊥)`; `F(a→⊥)@w1` creates `w2` with `T(a)`, `F(⊥)`, plus persisted `T(¬¬¬a)`. At `w2`,
`T(¬¬¬a) = T((¬¬a)→⊥)` needs `T(¬¬a)@w2` to fire, which is never planted. Branch saturates open.

**6c. The prescribed remedy is over-scoped; the Fitting split is sufficient.** Adding the standard
rule

> `T(φ→ψ)@w` → branch `[F(φ)@w']` | `[T(ψ)@w']`, for each `w'` accessible from `w`

yields exactly `sat_timp : … → b.any(F(φ)@w') ∨ b.any(T(ψ)@w')`. `truthLemma`
(`Scheme.lean:556-565`) is **bidirectional** — its conclusion is a conjunction of the `T`-forces and
`F`-refutes directions — so in the T-imp case the `F(φ)@w'` disjunct is discharged by `ih_φ`'s
second component against the supplied `IForces val w' φ`, leaving `T(ψ)@w'` and `ih_ψ`'s first
component. **Full `Sub(φ0)` bivalence is never needed.** This is materially cheaper than the
Lindenbaum completion rule (which would branch `2^|Sub(φ0)|` ways at every fresh world).

Verification that it closes all three counterexamples:
- `¬¬¬a → ¬a`: at `w2`, split `T((¬¬a)→⊥)` → `T(⊥)@w2` closes; `F(¬¬a)@w2 = F((¬a)→⊥)@w2` creates
  `w3` with `T(a→⊥)`, `F(⊥)`, persisted `T(a)`; persistence fires `T(⊥)@w3` → closes.
- `((a→b)→c) → (b→c)`: at the world carrying `T((a→b)→c)`, `T(b)`, `F(c)`, split gives
  `T(c)` (closes against `F(c)`) or `F(a→b)`, which creates a world with `T(a)`, `F(b)` and
  persisted `T(b)` → closes.
- `((a→b)→(a→c)) → (a→(b→c))`: identical shape at the innermost world (`T(a)`, `T(b)`, `F(c)`).
- **Reuse check**: this is the rule `Fitting1983` Ch. 4 specifies, and task 317 `reports/08:30`
  already transcribes it as *"copies to every accessible world and there splits `F(A) ∣ T(B)`"* —
  the implementation dropped the split. This is literature-conformance, not a novel design.
- The weak form proposed at task 317 `reports/08:89-93` (`T(φ)@w' → T(ψ)@w'`) is **not** sufficient;
  `Scheme.lean:519-524` says so explicitly. Use the disjunctive form.

**6d. Concrete implementation targets.**
- Datatype: `IntRuleResult` (`Propositional/.../Rules.lean:236-242`) already has
  `branchingResult : List (List (ISF Atom)) → Nat → IntRuleResult Atom`. **No new constructor
  needed.** Add a `| .pos, .imp φ ψ =>` case to `intApplyRuleFull` (`:245-268`).
- Open design question the plan must settle: whether the new branching arm **replaces** or
  **supplements** `applyAllTImpRules`/`applyPersistenceFixpoint` (`Expansion.lean:118-139`), which
  fires `intTImpRule` at every accessible world before each step. Running both is not unsound but
  duplicates work and complicates the measure. Recommendation: **supplement** — keep the cheap
  positive propagation as an optimization, add the branching rule for the case where `T(φ)@w'` is
  absent. The `w'` quantification is the same `accessibleWorlds` list already computed at
  `Rules.lean:177`.
- The `Sfor`-containment loop-check `intFImpReuseWitness?` (`Expansion.lean:263-291`) and the fuel
  bound `intFuel` (`:468-469`, `3 ^ (4*(2*c+1)*(c+2))`) are both sized against the pre-existing rule
  set and must be re-derived for the enlarged one.

### Finding 7 — Soundness re-audit obligations, by name

**Temporal.** There is **no temporal soundness theorem at HEAD to break**: `temporalTableau_sound`
does not exist (docstring mention only, `Soundness.lean:49`) and `eventualityDefect_unsat` is a
fenced docstring sketch inside a `BlockedObligations` section (`Soundness.lean:196-221`), not a
declaration. The only landed soundness lemma is `classicallyClosed_unsat` (`Soundness.lean:116`),
which reasons purely from branch content and is **rule-independent** — unaffected by any rule
addition. The re-audit is therefore a *forward* obligation, plus these invariant-preservation
lemmas that will break mechanically:

| Lemma | File:line | Effect of a new rule arm |
|---|---|---|
| `temporalApplyPos_preserves` | `Rules.lean:502-593` | `split at h <;> try split at h …` chain (`:520-521`) currently produces exactly 9 bullets; a new arm adds bullets and surfaces as an unproved goal — mechanically checkable, never silent |
| `temporalApplyNeg_preserves` | `Rules.lean:601-668` | same, currently 7 bullets |
| `temporalApplyOne_preserves` | `Rules.lean:675-705` | dispatch only; no new bullets |
| `temporalStepBranch_preserves` | `Saturation.lean:181` | tracker-list signature (Finding 5) |
| `temporalStepBranch_preserves_faithful` | `Saturation.lean:714` | tracker-list signature |
| `temporalTableau_instantStrict` | `Saturation.lean:545` | via `run_level_P1` |
| `temporalTableau_trackerBranchFaithful` | `Saturation.lean:995` | via `run_level_faithful` |

Forward soundness for the new seriality arm is **discharged by construction**: `branchSat`
(`Soundness.lean:95-106`) already existentially quantifies over a domain with `NoMaxOrder D` and
`NoMinOrder D`, so "every time has a successor and a predecessor" is *given* by the frame class.
No new semantic assumption is introduced.

**Propositional.**

| Lemma | File:line | Effect |
|---|---|---|
| `intRule_preserves_sat` | `Soundness.lean:83-107` | its `.branchingResult` case already has the right shape (`∃ br ∈ branches, intBranchSatisfied …`); a new arm needs one new case proving *some* branch stays satisfied — for `T(φ→ψ)` at `w'` this is the classical meta-disjunction "`¬(w' ⊩ φ)` or `w' ⊩ ψ`" |
| `intStepBranch_result_ne_notApplicable` | `Expansion.lean:163-180` | `cases hint : intApplyRuleFull` is over the 3 *constructors*, not the cases; adding to `.branchingResult` needs no new bullet |
| `intClosed_unsatisfiable` | `Soundness.lean:284` | rule-independent |
| `intExpandBranches_closed_unsat` | `Soundness.lean:1039` | sorry-free today; must be re-proved |
| `intuitionisticTableau_sound` | `Soundness.lean:1714` | sorry-free today; must be re-proved |
| `IBranchSaturation` | `Scheme.lean:74` | gains `sat_timp` as a 6th field |
| `truthLemma` | `Scheme.lean:556` | T-imp case closes using `sat_timp` |
| `intFuel`, `intExpMeasure_*` | `Expansion.lean:468`; `Scheme.lean` | measure/fuel re-derivation for the enlarged rule set |

---

## Decisions

- **D1 — The temporal tableau's validity target is `validDiscrete`, not `Temporal.valid`.**
  `Temporal.valid` (`Validity.lean:76-80`) quantifies over `[LinearOrder D] [Nontrivial D]` only —
  not serial. `𝐆p → 𝐅p` is false on a two-point order, so it is *not* `Temporal.valid`. Adding a
  seriality rule is sound **only** because `branchSat` (`Soundness.lean:95-106`) already restricts to
  the discrete-serial class. Every future theorem statement must say `validDiscrete`/
  `satisfiableDiscrete`. This must be written into the plan, not left implicit.
- **D2 — Deliverable 6's remedy is the Fitting `T(→)` split, not the Lindenbaum completion rule.**
  Rationale in Finding 6c; it is literature-conformant, exponentially cheaper, and sufficient for
  the one obligation (`sat_timp` → `truthLemma`) the gap actually blocks.
- **D3 — Deliverables 2, 3, and 4 are one indivisible wave.** Removing the `timeCount < 4` cap
  removes the only bound on time creation; the seriality rule needs a `isTemporallyBlocked`
  termination gate; the gate's second conjunct reads the tracker, which Deliverable 5 fixes; and
  fuel must be raised in the same breath or the resulting deeper tableaux exhaust it. Landing any
  one alone regresses the others.
- **D4 — The fuel remedy is "raise the constant"** (Finding 4). Dedup remains desirable but is
  reclassified as the *termination gate* under Deliverable 2, not as a fuel fix.
- **D5 — Deliverable 1 is a gate, not a deliverable to be scheduled alongside the others.** It must
  land first, red on 12 rows, or none of the other five can be validated.

---

## Recommendations (prioritized)

1. **P0 — Conformance harness** (Deliverable 1). Create `CslibTests/TableauConformance.lean` with
   the dual-import header from Finding 1, two `String`-valued verdict adapters, and the 44 rows of
   Finding 0 as `#guard_msgs in #eval` assertions. Register in `CslibTests.lean`. Acceptance: 32
   rows green, 12 rows red-and-documented. **No dependencies. Blocks everything else.**
2. **P1 — Propositional `T(→)` branching rule** (Deliverable 6). Fully independent of the temporal
   front — different files, different calculus, no shared declaration. **Run in parallel with P2-P4.**
   Add the `.pos, .imp` arm to `intApplyRuleFull` (`Propositional/.../Rules.lean:245-268`); add
   `sat_timp` to `IBranchSaturation` (`Scheme.lean:74`); extend `intRule_preserves_sat`
   (`Soundness.lean:83`); close `truthLemma`'s T-imp case (`Scheme.lean:556`); re-derive `intFuel`
   and the `intExpMeasure_*` chain. Acceptance: the three red propositional rows flip to CLOSED, the
   five IPC-invalid rows stay OPEN, and no existing sorry-free lemma regresses.
3. **P2 — Tracker per-branch list** (Deliverable 5). Change `temporalStepBranch`'s return type
   (`Saturation.lean:139-144`) and update the seven call sites in Finding 5. Must complete before
   P3's termination gate can be trusted. Acceptance: no verdict changes on the 32 green temporal
   rows; `lake build Cslib.Logics.Temporal.Tableau.Saturation` green.
4. **P3 — Temporal rule-completeness wave** (Deliverables 2 + 3 + 4, indivisible per D3). Seriality
   arm + `𝐆`/`𝐇` negative arms + transitive propagation + cap removal at `Rules.lean:312,338` +
   `temporalFuel` raised at `Saturation.lean:78`. Re-prove `temporalApplyPos_preserves` and
   `temporalApplyNeg_preserves`. Acceptance: **all 12 red rows flip**, including the six from
   Finding 2b that the original Deliverable 2 does not cover.
5. **P4 — Update the six-deliverable scope** to record Finding 2b/2c as first-class work rather than
   a footnote of Deliverable 2. As written, Deliverable 2 would be marked complete while
   `𝐆p → 𝐆𝐆p` and `¬𝐆p → 𝐅¬p` remain OPEN.

Independence/ordering summary: `P0 → {P1 ∥ (P2 → P3)}`. P1 shares no file with P2/P3.

---

## Risks & Mitigations

- **R1 — Seriality changes what the tableau decides.** After the fix the tableau decides
  `validDiscrete`, and formulas that are `Temporal.valid`-invalid but `validDiscrete`-valid will
  newly close. *Mitigation*: D1; state `validDiscrete` in every theorem; add `𝐆p → 𝐅p` to the
  harness as an explicitly `validDiscrete`-labelled row.
- **R2 — Cap removal without a working blocking gate loops forever.** *Mitigation*: D3 ordering; P2
  before P3; gate the seriality arm on `isTemporallyBlocked` (`Branch.lean:160-167`).
- **R3 — Tracker registration changes which branches close.** `findEventualityDefect` starts firing.
  *Mitigation*: P0 first; re-run all 32 green rows after P2.
- **R4 — The `𝐆` transitive-propagation fix may blow up branch size.** `ancestorTimes` is
  fuel-bounded (`TimeOrdering.lean:117-122`); using it in a `.persistent` rule that never leaves the
  expanded set could re-fire indefinitely. *Mitigation*: measure minimal sufficient fuel on the
  harness family after the change, before raising `temporalFuel` a second time.
- **R5 — Adding a `.pos, .imp` arm alongside `applyPersistenceFixpoint` duplicates work.**
  *Mitigation*: Finding 6d's open design question must be settled in the plan, not during
  implementation.

---

## Adversarial Self-Verification (H4)

`adversarial_verification_triggered: true`. Five claims were actively attacked.

**A1 — "A seriality rule is sound." — ATTACKED, SURVIVED (with a constraint added).**
Attack: `Temporal.Satisfies` is defined over `[LinearOrder D]` (`Satisfies.lean:53`), an arbitrary
linear order, which need not be serial. On `D = Fin 2`, `𝐆p` is vacuously true at the top point and
`𝐅p` is false, so `𝐆p → 𝐅p` is **invalid** and a seriality rule would be **unsound**.
Resolution: read `Soundness.lean:95-106`. `branchSat` — the actual soundness target — existentially
quantifies over `NoMaxOrder D`, `NoMinOrder D`, `SuccOrder D`, `PredOrder D`, `IsSuccArchimedean D`.
Seriality is *given* by the frame class. The rule is sound. **But the attack forced Decision D1**:
the tableau must be stated against `validDiscrete`, never `Temporal.valid` (`Validity.lean:76-80`),
and this was nowhere in the task description. Claim survives, scope narrowed.

**A2 — "The six deliverables cover the defects." — ATTACKED, REFUTED.**
Rather than accept the description's defect list, I executed 22 additional temporal formulas.
Six linear-order validities that no deliverable addresses returned `OPEN`. Root cause traced to
`temporalApplyNeg` (`Rules.lean:287-349`) having no `asAllFuture?`/`asAllPast?` arm at all, and to
`futureOf` being direct-successor-only (`TimeOrdering.lean:92-94`). **Claim refuted; Finding 2b/2c
and Recommendation P4 added.** This is the single most consequential result of the dispatch: the
task as scoped would have been marked complete with the calculus still incomplete.

**A3 — "Deliverable 6 needs a Lindenbaum-style Sub(φ0) completion rule." — ATTACKED, REFUTED.**
Three in-tree artifacts assert this (`Scheme.lean:2838-2844`,
`317/.orchestrator-handoff.json:14`, `specs/state.json:518`). Attack: what does the *one blocked
obligation* actually need? `truthLemma` (`Scheme.lean:556-565`) is bidirectional, so its T-imp case
needs only `F(φ)@w' ∈ b ∨ T(ψ)@w' ∈ b` — precisely the Fitting `T(→)` split, not general bivalence.
I traced all three executed counterexamples through the split rule; each closes. **Claim refuted;
Decision D2 replaces the prescribed remedy with an exponentially cheaper one that also matches
`Fitting1983` Ch. 4.** Risk acknowledged: I have not machine-checked that no *other* future
obligation needs full bivalence. Confidence: high on `sat_timp`/`truthLemma`; medium on the
completeness assembly downstream of them.

**A4 — "The `k = 4` cut is the time cap." — ATTACKED, SURVIVED (strengthened).**
Attack: report 04's family is short and the cut could be fuel exhaustion coinciding with `k = 4`.
Test: re-ran `𝐅q → 𝐅^k ⊤` at fuel `20000` (~40× shipped). Verdicts unchanged. **Claim survives with
a discriminating measurement no prior artifact had**, and Deliverables 3 and 4 now have independent
acceptance gates.

**A5 — "The measured fuel table is reproducible." — ATTACKED, PARTIALLY SURVIVED.**
The scratch file that produced report 04's table (`Scratch425.lean`) is not in the repo and was
never committed; the exact family `taut k` is not recoverable, only its `subformulaCount` column
(2, 3, 6, 9, 12, 15). I could not reproduce that table row-for-row. Instead I measured an
*independent* family and got minimal fuel `1, 14, 32, 68, 140` for `k = 0..4` — exponential, with
`temporalFuel` quadratic and a crossover near `k ≈ 11`. **The qualitative claim (bound false at the
current constant) is confirmed on independent evidence; the specific fit `1.5·2^k − 2` is
NOT reproduced and should be cited as report-04's measurement, not as a fact.**

**Additional verifications:**
- All six deliverables' line ranges re-checked against HEAD `3c4b580f`. All hold. One omission:
  Deliverable 2 cites `Rules.lean:312` but the identical gate also sits at `:338` (`snceNeg`).
- BibKeys: five keys verified present in the in-tree citation form (see H3 table). None invented.
- Reuse check (CSLib 5-step protocol) run for the harness (no existing execution harness; nearest
  precedent `CslibTests/ModalFrameSeparation.lean` uses proof terms, unavailable here), for the
  branching result type (`IntRuleResult.branchingResult` already exists — no new constructor), for
  the dedup device (`timeType`/`isSubsetBlocked` already exist — no new definition), and for
  transitive time closure (`ancestorTimes` already exists as an unused hook). **No new abstraction
  is recommended anywhere in this report.**
- Zero-debt: no recommendation defers a `sorry`, adds an axiom, or introduces a vacuous definition.
  The `Cslib/Logics/Temporal/` tree has no `sorry` at HEAD and must stay that way.

---

## Appendix

### Reproduction of the executed evidence

Scratch files were created under `CslibTests/`, run with `lake env lean <path>`, and deleted.
Header required (both forms, same four modules):

```
module
import Cslib.Logics.Temporal.Tableau.Saturation
import Cslib.Logics.Temporal.Syntax.Formula
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
import Cslib.Logics.Propositional.Defs
public meta import Cslib.Logics.Temporal.Tableau.Saturation
public meta import Cslib.Logics.Temporal.Syntax.Formula
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
public meta import Cslib.Logics.Propositional.Defs
```

Minimal-fuel probe used for Finding 4:

```
def closedAt (φ : F) (fuel : Nat) : Bool :=
  match temporalExpandBranches [([⟨.neg, φ, 0⟩] : TBranch Nat)] [[]]
      [TimeOrdering.empty] [EventualityTracker.empty] fuel with
  | .closed => true | .openBranch _ _ => false
def minFuel (φ : F) (cap : Nat) : Option Nat :=
  (List.range (cap+1)).findSome? (fun n => if closedAt φ n then some n else none)
```

### Related in-tree records not re-derived here

- `Cslib/Logics/Temporal/Tableau/Completeness.lean:63-124` — the fuel-sufficiency and pigeonhole
  obligations, unchanged by this dispatch.
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:444-483` — the Phase 2 monotonicity
  STOP-gate, a sibling of the `sat_timp` gap and likewise downstream of the `measure ≤ fuel`
  invariant.
- `specs/425_.../reports/04_…md` §Q2-Q6 — the original executed counterexamples and O1/O2/O3
  model-construction obligations, which remain open regardless of the six deliverables.
