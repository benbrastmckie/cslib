# Report 07 — Option B, the Fuel Bound, and What Actually Closes Sorry 986 (HARD mode)

- **Task**: 317, Phase 5/7 blocker resolution — feed a plan v5 revision.
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Scope**: RESEARCH ONLY. No `.lean` file was edited. All code claims grounded by direct
  `Read` + live `lean-lsp` (`lean_goal`, `lean_local_search`) against the **cslib** project
  (confirmed live: `lean_goal` at `Scheme.lean:986` returned a well-formed `Cslib` goal state).
- **Sorry under repair**: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:986`
  (`intExpandBranches_openBranch_sat`, `fuel = 0` base case).
- **Current green baseline**: commit `4202d1df` (Option A live: `intFImpReuseWitness?` requires an
  explicit `F(ψ)@x` entry on reuse). Head `e1d0fd49` ("orchestration paused — B2 fuel=0 open").
- **Reference grounding tier**: Tier 1 (literature-backed) + Tier 3 (implementation-backed).

---

## VERDICT

**Option B: INFEASIBLE (unsound).** Appending `F(ψ)@x` on the reuse path breaks calculus
soundness (`intExpandBranches_closed_unsat`, `Soundness.lean`). This is not merely a proof-engineering
obstacle — it is a genuine semantic defect, already diagnosed in the live code docstring
(`Expansion.lean:229-236`) and re-confirmed here with a concrete model-theoretic counterexample
(§Q1). The literal `sat_fimp` is fine and needs no reformulation; Option A (live) already
satisfies it soundly.

**But the headline finding supersedes the Option-A-vs-B question:** *closing sorry 986 at the
current fuel `2^(2·complexity+2)` is INFEASIBLE regardless of the dedup variant.* World-dedup
(Option A live, or Option B) bounds **world count**, but world count is not the binding constraint —
worlds are already **linearly** bounded (`W ≤ complexity+1`, report 04 F5) with no dedup at all.
The binding constraint is the **β-branching expansion forest**, whose worst-case size is
`2^Θ(complexity²)` (report 04 F6), and which world-dedup provably does **not** shrink in the
worst case (§Q2). The fuel counts total forest size (§Q2, grounded in the `go` recursion), so
`total_steps ≤ fuel` is false for large inputs. The premise of plan 04 — that GGN `Sfor`-dedup
makes the existing fuel sufficient (report 05 §Q2) — **conflates deduplicated-model-size with
search-forest-size**; they differ by an exponential.

**Consequence for v5**: the dedup path (plan 04 Phases 5–7) cannot close 986. The only sorry-free
close is to **raise the fuel formula** to `2^Θ(complexity²)` and thread a `measure ≤ fuel`
hypothesis into the lemma (mirroring the classical template and the *already-proven* Modal-K
`FmpMeasure` pattern). If the user maintains the "do not change the fuel formula" constraint, the
correct terminal state is **986 [BLOCKED]**. A v5 phase breakdown for the fuel-raise path is in §Q4
(**6 phases**).

---

## Source-to-Implementation Mapping (Tier 1)

| Source claim | BibKey / Source | Lean target (file:line) | Translation notes |
|---|---|---|---|
| A world-loop-check blocks creating a world whose forced-set is subsumed by an ancestor's | `GargGenoveseNegri2012` (LICS 2012) — **ABSENT from `references.bib`** | `intFImpReuseWitness?` (`Expansion.lean:262-290`) | GGN blocks when `new ⊆ ancestor`. Here persistence makes descendants **supersets** of ancestors, so the check fires only on a rare coincidence (§Q2), not a monotone antichain. |
| Deduplicated model size `O(2^{2n})` = intended fuel magnitude | report 05 §Q2 citing `Caleiro2013`/FMP | (would be) `intExpandBranches_fuel_sufficient` | **This is the conflation.** Model size ≠ search-forest size. Forest = `2^Θ(c²)` (F6), independent of model size. |
| FMP world bound `≤ 2^{\|Sub(φ)\|}` | `ChagrovZakharyaschev1997` §2.2 (**PRESENT**, `references.bib:75`); `Fitting1983` (**PRESENT**, `:203`) | report 04 F5 supersedes with linear `W ≤ c+1` | The FMP world bound is real but **not the binding constraint** (worlds already linearly bounded). |
| Multiset / termination ordering | `DershowitzManna1979` — **ABSENT** | `WellFounded.prod_lex` (Mathlib.Order.RelClasses) | Well-foundedness is not the obstacle; the numeric `measure(initial) ≤ fuel` step is. |
| G4ip worlds-free weight does not transfer | `TroelstraSchwichtenberg2000` §4.3 (**PRESENT**, `:858`) | proof comment `Expansion.lean:243-252` | Correct and already documented; persistence breaks the G4ip weight. |
| Counting-against-fixed-universe measure (the working pattern) | task 442, `FmpMeasure.lean` (Modal K); report 06 §2.2 | v5 `intWork`/`intExpMeasure` (proposed, §Q4) | `modalWork U b e = |U\b|+|U\e|`, `modalExpMeasure = Σ 3^work` — a **proven** repo pattern for "strict decrease despite persistence". Requires fuel `~exp(c²)`. |

BibKey status: `GargGenoveseNegri2012` and `DershowitzManna1979` remain **ABSENT** (grep of
`references.bib` at `4202d1df`); `ChagrovZakharyaschev1997`, `Fitting1983`,
`TroelstraSchwichtenberg2000` **PRESENT**.

---

## Findings

### Q1 — Option B soundness: INFEASIBLE (unsound), riskiest case identified and it breaks

**What Option B proposes**: on the reuse path, reuse whenever
`{φ} ∪ Sfor(w) ⊆ posFormulasAt bPers x ∧ ψ ∉ posFormulasAt bPers x`, then **append `F(ψ)@x`** to
the branch and create no world.

**The soundness lemma that breaks** (`intExpandBranches_closed_unsat`, `Soundness.lean:~1083`):
its induction proves that if `intExpandBranches` returns `.closed`, the initial branch is
unsatisfiable — operationally, that **each branch `go` recurses on stays satisfiable given the
initial branch is**. Concretely (from Phase 4, plan 04, commit `8a5c0250`): the reuse sub-case
applies the fuel-IH directly to `bPers`, relying on `applyPersistenceFixpoint_sat` giving
satisfiability of *exactly the branch the recursive call receives*. Under Option B the recursive
call receives `bPers ++ [F(ψ)@x]`, not `bPers`.

**Why appending `F(ψ)@x` is unsound** (the model-pinning argument, grounded in `sfSatisfied`'s
`.neg,.imp` clause at `Scheme.lean:496-499`): `F(ψ)@x` asserts *`ψ` is not forced at the model
world assigned to label `x`*. But `x` is a **pre-existing** world whose model image `v_x` was
fixed by earlier steps. Take any Kripke model `M` satisfying `bPers`. The reuse condition only
gives `ψ ∉ posFormulasAt bPers x` (ψ is not *on the branch* as `T` at `x`) — it says **nothing**
about whether `M` forces ψ at `v_x`. A perfectly good model of `bPers` may have `M, v_x ⊨ ψ`.
Appending `F(ψ)@x` then makes `bPers ++ [F(ψ)@x]` **unsatisfiable under that `M`**, so
satisfiability is not preserved and the `closed_unsat` induction has no witness to pass down.

Contrast the *sound* fresh-world rule (`intFImpRule`, `Rules.lean:154-159`): `F(φ→ψ)@w` with
`M,w ⊭ φ→ψ` yields a *semantic* witness `v ≥ w(M)` with `M,v ⊨ φ`, `M,v ⊭ ψ`; because the new
label `w'` is **fresh**, we are free to set `worldOf'(w') := v`. Reuse forfeits that freedom: `v`
need not equal the already-pinned `v_x`, and `Sfor(w') ⊆ Sfor(x)` only forces `x` to force *at
least* what `w'` would — `x` may force strictly more, including ψ.

**Concrete counterexample** (model-theoretic, by construction): test `¬IValid` of a formula whose
*only* countermodels force `p` at the world that ends up labelled `x`. Let `φ→ψ = q→p`. Suppose
the branch already carries world `x` with `T(q)@x` (so `Sfor(x) ⊇ {q}`), `p ∉ Sfor(x)`, and `x`
accessible from `w`. Option B reuses `x` and appends `F(p)@x`, asserting `M,v_x ⊭ p`. But an
arbitrary model `M ⊨ bPers` with `M,v_x ⊨ q ∧ M,v_x ⊨ p` satisfies the branch pre-append and is
destroyed by the append. `intExpandBranches_closed_unsat` would then be provable only by
weakening it — forbidden. This is precisely the `Expansion.lean:229-236` recorded rationale
("that model-world's value was already pinned by earlier steps, unlike a genuinely fresh label").

**Verdict Q1**: Option B is **unsound**; INFEASIBLE. The riskiest case (an existing witness world
whose model image already forces ψ) genuinely breaks and cannot be closed.

### Q2 — The fuel bound with aggressive dedup: dedup does NOT bound the forest

**Fuel accounting (grounded in code).** In `intExpandBranches` (`Expansion.lean:339-429`), the
inner `go` skims the pending list moving *closed* branches into `done` within one fuel unit
(`go restBs ... (done ++ [bPers]) ...`, `:372-373`), and on the **first open expandable branch**
performs **one** rule step and recurses via `intExpandBranches ... fuel'` (`:384`, `:399`, `:408`,
`:417`) — i.e. **fuel decrements by exactly 1 per single expansion step**, including each β-split
(`:415-423` produces `branches'.map (...)` sub-branches for **one** decrement, and each sub-branch
later costs its own fuel). Therefore **total fuel consumed = total number of internal nodes of the
expansion forest** (report 04 F6 accounting, now grounded line-by-line). The top-level call
(`intuitionisticTableau`, `:464-467`) passes `fuel = 2^(2*φ.complexity+2)`.

**The forest is `2^Θ(c²)` and dedup does not shrink it.** Report 04 F6's construction: a top
antecedent `(p₁∨q₁) ∧ … ∧ (p_k∨q_k)` introduced as `T(...)` above a nested chain of `W`
world-creating `F(→)`s. `propagatePersistence` (`Rules.lean:139-141`) copies **every positive
compound** to each new world under a **fresh label**, and `intStepBranch`'s `expanded` set is keyed
on the full `(sign, formula, label)` triple (`Expansion.lean:150-157`), so each `T(pᵢ∨qᵢ)@wⱼ` is
a fresh unexpanded triple that **re-splits** at every world. A single root-to-leaf path passes
through all `W` worlds doing `k` β-splits at each → `k·W` splits → `2^{k·W}` leaves. Complexity
budget `c ≈ 3k + 2W` funds `k·W = Θ(c²)`, so the forest is `2^Θ(c²)`.

**Why world-dedup (A or B) does not fire here.** In this calculus persistence copies positives
**downward**, so `Sfor(descendant) ⊇ Sfor(ancestor)`. The nested-`F(→)` chain builds worlds with
**strictly growing** forced-sets `Sfor(w₁) ⊊ Sfor(w₂) ⊊ …`. The reuse test
`{φ} ∪ Sfor(w) ⊆ posFormulasAt bPers x` (`Expansion.lean:285`) needs a candidate `x` that forces
*more* than `w` plus `φ`; ancestors force *less*, and the chain's descendants each carry different
antecedents/consequents, so the coincidence required for reuse (`Expansion.lean:283-287`: accessible
`x`, containment, `ψ` open, explicit `F(ψ)@x`) essentially never holds. **Dedup fires rarely and
leaves the `W = Θ(c)` worlds — and hence the `2^Θ(c²)` forest — intact.** Option B changes only the
*action on reuse*, not *when reuse fires*, so it is equally powerless against F6.

**Reconciling report 04 (linear `W ≤ c+1`) with report 05 (`2^{|Sub(φ)|}`).** Both are **world**
bounds and both are correct; report 04 F5's linear `W ≤ complexity+1` is **strictly stronger** and
is the right bound for *this* calculus (only `F(φ→ψ)` creates worlds, descending to `F(ψ)`;
F-formulas never persist). **Neither yields `total_steps ≤ fuel`**, because `total_steps` = forest
size ≠ world count. Report 05's `step count = #worlds × #forced-sets-per-world ≤ 2^{|Sub|}·2^{|Sub|}`
is the conflation: it counts *model cells*, not the *β-branching search tree*, which is exponentially
larger.

**The exact lemma an implementer must prove is NOT a world bound.** Mirroring the classical template
(`classicalExpandBranches_hintikka`, `Completeness.lean:906-939`), 986 needs the lemma to carry a
**measure hypothesis** `intExpMeasure branches expandedSets ≤ fuel`, with a per-step-strict-decrease
lemma `intExpMeasure_step_lt` and an initial bound `intExpMeasure initial ≤ fuel`. Because a valid
step-counting measure has `intExpMeasure initial ≥ forest size ≥ 2^Θ(c²)`, the initial-bound lemma
is **FALSE** at `fuel = 2^(2c+2)`. **No measure fits under the current fuel** (report 04 F6,
now mechanistically grounded).

Termination/well-foundedness names verified: `WellFounded.prod_lex` exists (Mathlib.Order.RelClasses,
per report 04 F4 loogle). `intExpandBranches_world_bound` / `intExpandBranches_fuel_sufficient`
do **not** exist yet (`lean_local_search "intExpandBranches_world_bound"` → empty; plan 04 Phase 5
NOT STARTED).

**Verdict Q2**: With Option B, neither `#worlds ≤ 2^{|Sub|}` (true but irrelevant) nor
`total_steps ≤ 2^(2c+2)` (false) holds in the sense needed. The dedup does not bound the forest.

### Q3 — Does `sat_fimp` need reformulating? NO — but it is not the blocker either

`sat_fimp` (`Scheme.lean:95-99`) demands `∃ w' ≥ w, T(φ)@w' ∈ b ∧ F(ψ)@w' ∈ b`. Option A (live)
satisfies it **soundly**: its fifth conjunct requires an explicit `F(ψ)@x` entry
(`Expansion.lean:287`), and `intFImpReuseWitness?_spec` (`Expansion.lean:299-326`) exposes exactly
`T(φ)@x` (via containment) + `w ≤ x` + `F(ψ)@x`, i.e. the witness `w' = x` for `sat_fimp`. So the
**literal `sat_fimp` is adequate**; the GGN containment-style reformulation of the Hintikka
condition (which would ripple into `truthLemma`) is **not required**.

Crucially, closing 986 is **not blocked by `sat_fimp`'s form at all** — it is blocked by
fuel-sufficiency (Q2). Under Option A, `sat_fimp` holds; under Option B, unsoundness bites before
`sat_fimp` is even reached. **The thing that must be reformulated to make 986 provable is the
statement of `intExpandBranches_openBranch_sat` itself** (add the `intExpMeasure ≤ fuel`
hypothesis, per classical), not `sat_fimp`/`IBranchSaturation`.

**Grounding the "986 is false in isolation" claim** (live `lean_goal` at `Scheme.lean:986`):
```
hAC  : IAllConsistent branches expandedSets nextWorlds
hLen0: branches.length = edgeSets.length
h    : intExpandBranches branches expandedSets nextWorlds edgeSets 0 closurePred
         = IntTableauResult.openBranch b
⊢ IBranchSaturation Atom b
```
There is **no measure hypothesis**. `IExpandedConsistent b []` is vacuous (`Scheme.lean:503-504`:
`∀ sf ∈ e, …`), so instantiate `branches := [[⟨.pos, .and p q, 0⟩]]`, `expandedSets := [[]]`,
`nextWorlds := [1]`, `edgeSets := [[]]`: `IAllConsistent` holds, the branch is open and
`intExpandBranches … 0 … = .openBranch [T(p∧q)@0]` (fuel=0 returns the first open branch,
`Expansion.lean:347-352`), yet `IBranchSaturation [T(p∧q)@0]` is **false** (`sat_tand`,
`Scheme.lean:75-78`, demands `T(p)@0` and `T(q)@0`, absent). **The goal as stated is not provable**
— exactly what a missing `measure ≤ fuel` hypothesis predicts.

**Verdict Q3**: literal `sat_fimp` suffices; no Hintikka reformulation needed. The lemma
*signature* of `intExpandBranches_openBranch_sat` must gain a measure hypothesis.

### Q4 — v5 phase breakdown (6 phases, fuel-raise path)

The only sorry-free close raises the fuel and threads a measure, following the **proven Modal-K
`FmpMeasure` pattern** (`FmpMeasure.lean`, report 06 §2.2) rather than the branch-complexity measure
(which is non-monotone under persistence, report 04 F3). Each phase is H8-sized (~100–500 lines).

**Exact bound lemmas in Lean syntax** (proposed; names verified absent locally):
```lean
/-- F5: worlds are linearly bounded (holds with NO dedup). -/
lemma intExpandBranches_world_bound (φ : Proposition Atom) {b : IBranch Atom} … :
    (b.map (·.label)).eraseDups.length ≤ φ.complexity + 1

/-- Fixed finite universe of (sign,subformula,world) cells, |U| = O(c²). -/
def intUniverse (φ : Proposition Atom) : List (ISF Atom)   -- ≤ 2·(2c+1)·(c+2) cells

/-- Counting-against-U work, strictly-decreasing per step (cf. modalWork). -/
def intWork (U : List (ISF Atom)) (b e : IBranch Atom) : Nat := (U.diff b).length + (U.diff e).length
def intExpMeasure (U : …) (branches expandedSets : …) : Nat :=
    ((branches.zip expandedSets).map (fun (b, e) => 3 ^ intWork U b e)).sum

lemma intExpMeasure_step_lt … :               -- one go-step strictly decreases the measure
    intExpMeasure U (done ++ newBs ++ rest) … + 1 ≤ intExpMeasure U (done ++ b :: rest) …

lemma intExpMeasure_init_le_fuel (φ) :          -- REQUIRES the RAISED fuel
    intExpMeasure (intUniverse φ) [[⟨.neg, φ, 0⟩]] [[]] ≤ intFuel φ   -- intFuel φ = 3^(2·(2c+1)·(c+2))
```

- **Phase 1 — Raise the fuel formula.** In `Expansion.lean:466` (`intuitionisticTableau`) and the
  minimal analogue, change `2^(2*φ.complexity+2)` to `intFuel φ` (a `2^Θ(c²)`/`3^Θ(c²)` bound). Audit
  and re-verify every downstream fuel-pinned caller: `intExpandBranches_closed_unsat`
  (`Soundness.lean`, task 316 — coordination flag), `DecisionProcedure.lean`, `Completeness.lean`.
  Monotone-safe for the `openBranch → saturated` direction. ~100–200 lines + audit.
- **Phase 2 — `intUniverse` + `intWork` + linear world bound F5.** Define the fixed universe and the
  counting work; prove `intExpandBranches_world_bound` (`W ≤ c+1`) to bound the world coordinate of
  `U`. ~200–350 lines.
- **Phase 3 — `intExpMeasure_step_lt`.** Prove each `go` step strictly decreases the measure — the
  hard phase. Mirror `modalExpMeasure_step_lt` (`FmpMeasure.lean:3018`); handle world-creation and
  persistence by the `|U\b|+|U\e|` decrease (a fresh triple leaves `U\b`), not branch complexity. ~300–500 lines.
- **Phase 4 — `intExpMeasure_init_le_fuel`.** Prove the initial measure ≤ `intFuel φ` using `|U| = O(c²)`
  and F5. Reuse the pure arithmetic helpers `sum_map_le_length_mul`, geometric caps
  (`FmpMeasure.lean:131,776-833`; report 06 R1). ~150–300 lines.
- **Phase 5 — Reformulate `intExpandBranches_openBranch_sat` + close 986.** Add the
  `intExpMeasure … ≤ fuel` hypothesis; fuel=0 ⟹ measure=0 ⟹ `branches = []` ⟹ `.openBranch` impossible
  (copy `classicalExpandBranches_hintikka:922-939` verbatim in structure). Thread `intExpMeasure_step_lt`
  through the succ case. Keep `openBranch_countermodel`'s public signature stable by supplying the measure
  bound internally from `intExpMeasure_init_le_fuel`. Close sorry 986. ~150–300 lines.
- **Phase 6 — BibKeys.** Add `GargGenoveseNegri2012` (retained for the `intFImpReuseWitness?` docstring
  even though dedup is now a soundness refinement, not the fuel mechanism) and `DershowitzManna1979`;
  optionally note `Caleiro2013` conflation caveat in the measure docstring. ~20–40 lines.

**Alternative (user keeps the fuel formula)**: no sorry-free close exists (Q2); mark **986 [BLOCKED]**
with this report as the escalation record. Option A remains a real, committed, *sound* deliverable
(it is not wrong — it is just insufficient to bound the forest).

**Retire from v5**: plan 04 Phases 5 (`intExpandBranches_fuel_sufficient` at current fuel) and 7 as
written — both presuppose the false `forest ≤ 2^(2c+2)`.

---

## Adversarial Self-Verification (H4)

I attacked my own two load-bearing negative claims, since a wrong "infeasible" wrongly derails a
settled plan.

**Attack 1 — "Dedup does not shrink the forest" (riskiest; would overturn the settled user
decision).** Could report 05 be right that a *properly* deduplicated procedure has
`forest = model size`? In GGN and standard terminating tableaux the loop-check maintains a global
blocked set so a `T(∨)` is not re-processed in a subsumed context. But CSLib's `expanded` set is
**per-branch, `(sign,formula,label)`-keyed** (`Expansion.lean:150-157`), and `intFImpReuseWitness?`
blocks **world creation only** — it never touches the β re-split of a persisted `T(∨)@wⱼ`. Could one
*type-key* the `expanded` set (ignore the label) to kill the re-split? No: `T(∨)@w₁` and `T(∨)@w₂`
are **semantically distinct** obligations (the disjunction may resolve to the left disjunct at `w₁`
and the right at `w₂`), so label-keying is *necessary* for completeness. Hence the β-forest is
irreducible by any world-level dedup. **Claim stands (HIGH confidence).** The one residual: F6 is a
worst-case *lower-bound family*; I did not transcribe an exact failing Lean formula and execute it
(same caveat as report 04's adversarial §). Confidence that current fuel is *unprovable-sufficient*:
**HIGH** (the c² vs c exponent gap is structural, and the measure mechanism is now grounded).
Confidence it is *actually insufficient* (a concrete run hits fuel=0 unsaturated): **MEDIUM-HIGH**.

**Attack 2 — "Option B is unsound" (would I be wrong to reject it?).** Could the containment
`{φ}∪Sfor(w) ⊆ Sfor(x)` plus `ψ ∉ Sfor(x)` secretly guarantee that *every* model of `bPers`
falsifies ψ at `v_x`? No: containment is a statement about **branch syntax** (`posFormulasAt`), not
about the model. `ψ ∉ posFormulasAt bPers x` means ψ is not *asserted true on the branch* at `x`;
an arbitrary model is free to make ψ true at `v_x` anyway (nothing on the branch forbids it). The
fresh-vs-pinned distinction is exactly the soundness hinge, and the live docstring
(`Expansion.lean:229-236`) plus `Soundness.lean`'s `applyPersistenceFixpoint_sat` reliance (Phase 4,
`8a5c0250`) both corroborate. **Claim stands (HIGH confidence).**

**Attack 3 — "986 is false in isolation" (did I mis-instantiate?).** I checked the *live* goal
(`lean_goal`, `Scheme.lean:986`): the hypotheses are `IAllConsistent branches … ` and the fuel=0
run equation, nothing more. `IExpandedConsistent _ []` is vacuous, so `[[T(p∧q)@0]]` with empty
expanded set satisfies `IAllConsistent`, and fuel=0 returns it unsaturated. The only way I could be
wrong is if `IAllConsistent` secretly forced a non-empty/saturated expanded set — it does not
(`Scheme.lean:503-504` quantifies over `e`, true for `e = []`). **Claim stands (HIGH confidence).**
This also independently re-proves the necessity of the measure hypothesis: the classical lemma has
it (`Completeness.lean:910`); the intuitionistic one must too.

**Revision triggered.** My prior mental model (inherited from plan 04) was "dedup → fuel sufficient".
Verification **downgraded** this: dedup is a *soundness-neutral world-count* device that is
*orthogonal* to fuel sufficiency, and the settled "keep the fuel, dedup closes 986" decision rests
on report 05's model-size/forest-size conflation. I did **not** find a way to rescue the current
fuel; the verdict is that the fuel must rise or 986 stays blocked.

**Verified-name check.** `intFImpReuseWitness?` / `intFImpReuseWitness?_spec`
(`Expansion.lean:262,299`), `intExpandBranches` / inner `go` (`Expansion.lean:339,356`),
`sat_fimp`/`IBranchSaturation` (`Scheme.lean:95,72`), `sfSatisfied`/`IExpandedConsistent`/`IAllConsistent`
(`Scheme.lean:482,503`), `intExpandBranches_openBranch_sat` (`Scheme.lean:969`),
`IExpandedConsistent_sat` (`Scheme.lean:563`), `classicalExpandBranches_hintikka`/`classicalExpMeasure`
(`Completeness.lean:906,636`) — all read directly. `WellFounded.prod_lex` — per report 04 loogle.
`intExpandBranches_world_bound` — `lean_local_search` empty (correctly, not yet implemented). No
invented lemma names. BibKeys `GargGenoveseNegri2012`/`DershowitzManna1979` — grep-confirmed absent;
`ChagrovZakharyaschev1997`/`Fitting1983`/`TroelstraSchwichtenberg2000` — grep-confirmed present.

---

## Zero-Debt / escalation note

No `sorry`, `axiom`, or vacuous placeholder is recommended. The sorry-free close requires raising
the fuel formula (§Q4 Phases 1–6). If that architectural change is not authorized, the correct
terminal state is **986 [BLOCKED]** with this report as the escalation record — not a placeholder.

## Files Referenced (absolute paths)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (150-157, 181-326, 339-429, 464-467)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (72-99, 482-504, 563, 958-986)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` (126-159)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (~1083)
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` (636, 816, 906-939, 1259)
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (131, 180-196, 776-833, 3018)
- `references.bib` (75 ChagrovZakharyaschev1997, 203 Fitting1983, 858 TroelstraSchwichtenberg2000)
- `specs/317_propositional_tableau_completeness/reports/{04,05,06}_*.md`,
  `plans/04_sfor-dedup-fuel-sufficiency.md`
