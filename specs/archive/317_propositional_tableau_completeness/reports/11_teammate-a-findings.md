# Teammate A Findings — Primary Implementation Route (task 317)

## Key Findings

1. **Gap 2 (determinacy) really is resolved in the code**, via the new `.pos, .imp` branching
   arm in `intApplyRuleFull` (`Rules.lean:274-275`), which fires
   `[[F(φ)@l], [T(ψ)@l]]` — an exact match to the task description's claim.
2. **The Gap 1 fuel-sufficiency lemma (`applyPersistenceFixpoint_genuine_of_count_le_fuel`,
   `Scheme.lean:2912`) is sorry-free**, but it is currently **dead code** — never called from
   anywhere in the file. It is a necessary ingredient for closing `sat_timp`/the T-imp case and
   the fuel=0 base case, but **not sufficient by itself**: none of the invariant-threading
   machinery needed to actually invoke it inside `intExpandBranches_openBranch_sat`'s induction
   exists yet (see Finding 4 below).
3. **`sat_timp` itself (the `IBranchSaturation` field) is genuinely cheap** — a same-label
   disjunction dischargeable by the *exact* mechanical pattern already used for
   `sat_tand`/`sat_fand`/`sat_tor`/`sat_for_` in `IExpandedConsistent_sat`, requiring **no** new
   machinery. This part of the task's phase 1 claim is accurate.
4. **The harder half is NOT "assembly."** Closing `truthLemma`'s T-imp case
   (`Scheme.lean:592`) needs more than `sat_timp`: it needs a *copy-completeness* fact — "every
   world `w'` edge-accessible from `w`, given `T(φ→ψ)@w ∈ b`, itself carries a copy
   `T(φ→ψ)@w' ∈ b`" — which requires threading a **measure/fuel-sufficiency invariant**
   through `intExpandBranches_openBranch_sat`'s induction that does not exist today. This is the
   *same* missing invariant that blocks the fuel=0 base case (`Scheme.lean:1498`) — the task
   description's own docstrings already say these are entangled (`Scheme.lean:528-531`), and
   this report corroborates that with a concrete account of what the invariant must say and why
   the currently-built `intExpMeasure_step_lt`/`intExpMeasure_step_lt_branch`/
   `intExpMeasure_init_le_fuel` lemmas (sorry-free but unused) are necessary but not yet wired in.
5. **A further, distinct monotonicity gap likely blocks the two `IValid`/`MValid` bridges**
   beyond what "consuming the genuine-fixpoint lemma" suggests. `intExtractValuation`'s
   monotonicity along `intAccessPreorder edges` needs an induction on formula complexity at a
   genuine persistence fixpoint (documented, unresolved, at `Scheme.lean:442-483`), not merely
   Gap 1's syntactic fixpoint fact. I recommend flagging this to the user/orchestrator as a
   probable **additional phase**, not folded silently into "phase 4."
6. **The stale docstring is real and exactly as described.** `Scheme.lean:3001-3022`
   ("GAP 2 investigation … determinacy remains BLOCKED") directly contradicts the *earlier*,
   newer text at `Scheme.lean:485-533` ("Gap 2 … is RESOLVED"). It must be corrected/deleted.
7. **No territory conflict**: none of the four obligations touch
   `Cslib/Foundations/Logic/Tableau/**`; all work is confined to
   `Cslib/Logics/Propositional/Tableau/{Intuitionistic,Minimal}/**`.
8. **Baseline bare-`sorry` count in `Cslib/Logics/Propositional/Tableau/`: exactly 4.**
   - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:592`
   - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:1498`
   - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:133`
   - `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:125`
   (Verified via `grep -rn "sorry" Cslib/Logics/Propositional/Tableau/`; all other "sorry" hits
   in that tree are prose/docstring mentions, not bare tactics — confirmed by reading each hit.)

## Recommended Approach

Because item 2 (truthLemma T-imp) and item 3 (fuel=0 base case) provably bottom out in the
*same* missing invariant, and item 4 (bridges) likely needs a *separate* monotonicity argument
that only becomes tractable once that invariant exists, I recommend a phase order that differs
slightly from the task description's numbered list — merging (2)+(3) into one phase and treating
(4) as two sub-phases:

**Phase 1 — `sat_timp` field (cheap, independent, do first).**
Add the field to `IBranchSaturation` (`Scheme.lean:74-101`) and discharge it in
`IExpandedConsistent_sat` (`Scheme.lean:904-974`) by the same six-line pattern as the other five
fields. No dependency on anything else. Proposed statement:

```lean
/-- T(φ→ψ)@w ∈ b → F(φ)@w ∈ b ∨ T(ψ)@w ∈ b (Fitting T(→)-split, reflexive at the formula's
own label — this is `intApplyRuleFull`'s `.pos, .imp` branching-rule output). -/
sat_timp : ∀ (φ ψ : Proposition Atom) (w : Nat),
    b.any (fun sf => sf.sign == .pos && sf.formula == .imp φ ψ && sf.label == w) = true →
    b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) = true ∨
    b.any (fun sf => sf.sign == .pos && sf.formula == ψ && sf.label == w) = true
```

Discharge clause in `IExpandedConsistent_sat` (append to the `constructor`'d list, mirroring
lines 963-974 exactly, using `intApplyRuleFull`'s `.pos, .imp` case which is already
`.branchingResult` — i.e. `≠ .notApplicable` — so `compound_sat` applies unchanged).

**Phase 2 — measure/fuel-sufficiency invariant threading (the real new work; closes both
`Scheme.lean:1498` and half of `Scheme.lean:592`).**
This is the substantial phase. It must:
- Add a fixed formula parameter `φ0 : Proposition Atom` and a universe-membership invariant
  `∀ x ∈ bh, x ∈ intUniverse φ0` (mirroring `applyPersistenceFixpoint_genuine_of_count_le_fuel`'s
  own `hb` hypothesis) plus a measure bound
  `intExpMeasure (intUniverse φ0) (bh :: pending) (e :: pendingExp) ≤ fuel' + 1` to
  `intExpandBranches_openBranch_sat`'s signature and its internal `go`-induction (currently
  `IAllConsistent`/`IAllAccessConsistent` at `Scheme.lean:1335-1341`/`~1420` carry *no* such
  invariant — this is new plumbing, not existing plumbing being reused).
- Establish the invariant at the sole call site, `openBranch_countermodel`
  (`Scheme.lean:1871-1897`), via `intExpMeasure_init_le_fuel φ` (`Scheme.lean:2723`, sorry-free)
  plus `intUniverse`'s membership-closure lemmas (`intUniverse_mem_formula`/`_mem_label`,
  `Scheme.lean:2152/2161`).
- Maintain it across the `succ` case's recursive calls using `intExpMeasure_step_lt`
  (`Scheme.lean:2521`) and `intExpMeasure_step_lt_branch` (`Scheme.lean:2589`) — both already
  proved sorry-free but currently **unused** anywhere in the file (verified by grep: zero call
  sites besides their own statements and doc mentions).
- In the `zero` case (`Scheme.lean:1494-1498`), derive `measure = 0` from `measure ≤ fuel = 0`,
  then derive `(intUniverse φ0).countP (fun sf => !(e.any (· == sf))) = 0` (since
  `3 ^ intWork U b e ≥ 1` termwise, a sum-of-zero argument forces `intWork U b e = 0` for the
  selected pair, and `intWork`'s second summand is exactly this count), i.e. `e ⊇ intUniverse
  φ0`. Combined with `∀ x ∈ b, x ∈ intUniverse φ0` and the fact that every compound formula
  produced by `intApplyRuleFull` on `b` is itself a member of `intUniverse φ0` (the same closure
  property `applyAllTImpRules_subset` etc. rely on), this gives "every compound formula on `b`
  is already in `e`" directly — the exact fact `intStepBranch_none_compound_mem` extracts from
  `intStepBranch b e nw = none`, but derived here from the measure instead. This is a genuinely
  new lemma, not a restatement of anything currently in the file.
- Also use `applyPersistenceFixpoint_genuine_of_count_le_fuel` at the point `bPers` is computed
  (`Scheme.lean:1548`, inside the `succ` case) to establish "every `T(φ→ψ)@w ∈ bPers` has, for
  every `w'` edge-accessible from `w`, a copy `T(φ→ψ)@w' ∈ bPers`" — this needs the *same*
  measure bound (`(intUniverse φ0).countP (fun sf => !(bh.any (· == sf))) ≤ fuel' + 1`) as its
  `hfuel` hypothesis, so it falls out of the same invariant-threading work.

**Phase 3 — close `truthLemma`'s T-imp case (`Scheme.lean:592`), depends on Phases 1+2.**
`intro _`; obtain `w'` accessible-with-own-copy from Phase 2's copy-completeness fact; apply
Phase 1's `sat_timp` at `w'` to get the disjunction; case on it using `ih_φ'`/`ih_ψ'` exactly as
the F-imp case already does at lines 597-600 (structurally symmetric).

**Phase 4 — repair the stale docstring (`Scheme.lean:3001-3022`).**
Cheap, but should land in the *same* PR/commit as Phase 3, since only after Phase 3 lands is
Gap 1 actually closed and the block fully obsolete. Replace with a short note recording that both
gaps are resolved and pointing to the `sat_timp` field / `truthLemma`'s T-imp case as the landed
proof, mirroring the style of the "Gap 2 … RESOLVED" block at lines 485-500.

**Phase 5 — monotonicity-along-edges lemma (new; not explicit in the task's 4-item list).**
Prove, by structural induction on formula complexity at a `bPers`-level genuine fixpoint (using
Phase 2's fuel-sufficiency machinery as the base fact for the atom case, and the induction
hypothesis for the imp/and/or cases): `∀ φ w w', T(φ)@w ∈ b → isAccessible-closure w w' →
T(φ)@w' ∈ b` is **not quite what's needed** — the actual obligation (per
`Scheme.lean:442-483`) is upward-closure of `intExtractValuation b` (atoms only) and, for the
minimal case, of `minBranchBotForces b`. I recommend treating this as its own dispatch/phase
with a short research pass first to pin the exact Lean statement, rather than assuming it drops
out of Phase 2's work — the STOP-gate note's own author explicitly says it is "not completable
from completeness-side machinery alone" as of the current design and recommends re-scoping.

**Phase 6 — close the two `IValid`/`MValid` bridges as one parametric lemma, depends on
Phase 5.**
State a single lemma parametric in `S : IntMinScheme Atom` plus upward-closure witnesses for
`intExtractValuation b` and `S.modelBot b` along `intAccessPreorder edges`, instantiate at
`intScheme`/`IValid` (where the `modelBot` obligation is trivial since `fun _ => False` is
vacuously upward-closed) and at `minScheme`/`MValid` (where both obligations are real). This
directly generalizes over `(closurePred, modelBot)` as the task requests — see Evidence section
for why `IValid`/`MValid`'s shape (`Kripke.lean:145-158`) makes this a clean single
parameterization.

### Dependency order
Phase 1 (independent) → Phase 2 (independent, largest) → {Phase 3, Phase 4} (depend on 1+2) →
Phase 5 (depends on 2, possibly independent research) → Phase 6 (depends on 5).

Given phase sizing guidance (~one agent run each), Phase 2 is almost certainly too large for a
single dispatch on its own and may need splitting into "invariant definition + call-site
threading" and "succ-case maintenance + zero-case discharge" sub-phases.

## Evidence/Examples

**Rules.lean:274-275** (verified against source, exact text):
```lean
  | .pos, .imp φ ψ =>
    .branchingResult [[⟨.neg, φ, l⟩], [⟨.pos, ψ, l⟩]] nextWorld
```
This is `[[F(φ)@l], [T(ψ)@l]]` — matches the task description's claimed shape.

**`sfSatisfied`'s existing `.pos, .imp` clause** (`Scheme.lean:765-771`), which is exactly the
shape `sat_timp` should have:
```lean
  | .pos, .imp φ ψ =>
    b.any (fun x => x.sign == .neg && x.formula == φ && x.label == sf.label) = true ∨
    b.any (fun x => x.sign == .pos && x.formula == ψ && x.label == sf.label) = true
```

**`applyPersistenceFixpoint_genuine_of_count_le_fuel`** (`Scheme.lean:2907-2917`, real
signature):
```lean
private lemma applyPersistenceFixpoint_genuine_of_count_le_fuel
    {φ0 : Proposition Atom} {edges : IEdges} (b : IBranch Atom) (fuel : Nat)
    (hb : ∀ x ∈ b, x ∈ intUniverse φ0)
    (hfuel : (intUniverse φ0).countP (fun sf => !(b.any (· == sf))) ≤ fuel) :
    applyAllTImpRules (applyPersistenceFixpoint b edges fuel) edges
      = applyPersistenceFixpoint b edges fuel
```
Confirmed sorry-free (no `sorry` between lines 2760-3000; both the `zero` and `succ` cases of its
own internal induction close with `simp`/`omega`/`exact`).

**`intExpMeasure_step_lt`/`_branch`/`intExpMeasure_init_le_fuel` are unused** — grep for each
name across `Scheme.lean` shows only their own declaration site plus prose references; zero call
sites feeding `intExpandBranches_openBranch_sat`. `IAllConsistent`
(`Scheme.lean:1335-1341`) carries only `IExpandedConsistent`/`ILabelBound`, no measure or
universe-membership component — confirming Phase 2 is new plumbing.

**The stale block, `Scheme.lean:3001-3022`** (quoted in full):
> `### GAP 2 investigation (task 317 phase 10 continuation, this dispatch): determinacy remains
> BLOCKED, confirmed by source-level investigation, not merely re-asserted. ...`

directly contradicts the newer block at `Scheme.lean:485-533`, specifically:
> `**Gap 2 (determinacy) is RESOLVED as of the .pos, .imp branching arm added to
> intApplyRuleFull (Rules.lean:245-268).**`

**`intExtractValuation`/`minBranchBotForces`** (exact definitions, `Soundness.lean:1836-1837`
and `Minimal/Soundness.lean:169-171`):
```lean
def intExtractValuation (b : IBranch Atom) (w : Nat) (p : Atom) : Prop :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

def minBranchBotForces (b : IBranch Atom) (w : Nat) : Prop :=
  b.any (fun sf => sf.sign == .pos && sf.formula == (HasBot.bot : Proposition Atom)
    && sf.label == w)
```
Both are purely syntactic membership tests on the *final* branch `b` — their monotonicity along
`intAccessPreorder edges` is a static fact about `b`, not about intermediate expansion states.
Tracing `propagatePersistence` (`Rules.lean:139-141`, fires only at `intFImpRule`
world-*creation* time, copying all current T-positives to the fresh child) versus `intTImpRule`
(`Rules.lean:174-186`, fires at *every* persistence round, scanning *all* edge-accessible
worlds, not just children) shows that atom monotonicity for atoms introduced via
`T(φ→atom p)`-triggered `intTImpRule` firing at a later persistence round is exactly the
co-inductive-on-formula-complexity case the STOP-gate at `Scheme.lean:442-483` describes — this
report independently re-derives that account from the rule definitions rather than just trusting
the docstring's assertion.

**`IValid`/`MValid`** (`Cslib/Logics/Propositional/Semantics/Kripke.lean:145-158`):
```lean
def IValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (val : World → Atom → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    ∀ w, IForces val (fun _ => False) w φ

def MValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (val : World → Atom → Prop)
    (bot_forces : World → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    (∀ {w w' : World}, w ≤ w' → bot_forces w → bot_forces w') →
    ∀ w, IForces val bot_forces w φ
```
`IValid` is `MValid` specialized to `bot_forces = fun _ => False` (trivially upward-closed;
compare `mvalid_implies_ivalid`, `Kripke.lean:165-168`), confirming a single parametric bridge
lemma over `(S.modelBot, val_uc, bot_uc)` genuinely covers both `intuitionisticTableau_complete`
and `minimalTableau_complete` — the `intScheme` instantiation's `bot_uc` obligation is free, the
`minScheme` instantiation's is not.

## Verification of Task-Description Claims

| Claim | Verdict | Evidence |
|---|---|---|
| Rules.lean:274-275 produces `[[F(φ)],[T(ψ)]]` | **CONFIRMED** | Exact text quoted above |
| Scheme.lean:2907 (`applyPersistenceFixpoint_genuine_of_count_le_fuel`) is sorry-free | **CONFIRMED** | No `sorry` in lines 2760-3000; both induction cases close constructively |
| Scheme.lean:581 records the Gap 2 resolution | **CONFIRMED** | Comment at 580-591 cites the "Gap 2 RESOLVED" STOP-gate note directly above `truthLemma` |
| Stale docstring near Scheme.lean:~3000 must be fixed | **CONFIRMED, exact location 3001-3022** | Direct textual contradiction with 485-500, quoted above |
| Remaining scope is "assembly only" | **PARTIALLY REFUTED** | `sat_timp` field + its `IExpandedConsistent_sat` discharge (item 1) genuinely is assembly. But item 2 (T-imp case) and item 3 (fuel=0 base case) require building **new** measure/fuel-invariant-threading machinery through `intExpandBranches_openBranch_sat` that does not exist yet (confirmed: `IAllConsistent`/`IAllAccessConsistent` carry no such invariant, and `intExpMeasure_step_lt`/`_branch`/`intExpMeasure_init_le_fuel` are unused). Item 4 (bridges) likely needs an *additional*, undocumented-in-the-task-list monotonicity induction (Phase 5 above) that the task's own in-file STOP-gate (Scheme.lean:442-483) says is not resolved by Gap 1 alone. |
| Bare-sorry count in `Cslib/Logics/Propositional/Tableau/` before this task | **4**, at Scheme.lean:592, Scheme.lean:1498, Intuitionistic/Completeness.lean:133, Minimal/Completeness.lean:125 | `grep -rn "sorry"`, each hit read in context |
| No territory conflict with the concurrent modal-tableau session | **CONFIRMED** | All four obligations and their dependencies live entirely under `Cslib/Logics/Propositional/Tableau/{Intuitionistic,Minimal}/`; `Cslib/Foundations/Logic/Tableau/*` is only ever *read* (imports `Measure.lean`; no writes needed) |
| sat_timp discharge "consuming the genuine-fixpoint lemma" (item 1) | **CONFIRMED for the field itself, REFINED for the T-imp case** | The `IBranchSaturation` field discharge needs no fuel argument at all (same-label, mechanical); only the *use* of `sat_timp` inside `truthLemma`'s T-imp case needs the fuel-sufficiency fact, and that fact needs new plumbing (Phase 2), not just "consuming" the already-proved lemma as a black box |

## Confidence Level

**Medium-high for the code-verified claims** (Rules.lean branching shape, sorry-freeness of the
fuel lemma, exact sorry locations/count, stale-docstring contradiction, territory analysis) — all
directly read from source with exact line citations, no `lake build` run (per constraints) but no
claim here depends on build success, only on the literal text of already-committed lemmas that
other reports/CI presumably already keep green.

**Medium for the phase-decomposition and monotonicity-gap analysis** — these are architectural
inferences from reading `propagatePersistence`/`intTImpRule`/`applyAllTImpRules`/`intExpMeasure`
definitions and cross-referencing the in-file STOP-gate docstrings, not verified against actual
Lean goal states via `lean_goal` (I did not have this MCP tool invoked in this pass — a follow-up
verification pass with `lean_goal`/`lean_state_search` at the exact sorry positions, especially
for the Phase 2 zero-case measure argument and the Phase 5 monotonicity induction, would raise
confidence before planning locks in the exact lemma statements). I recommend the planner treat
Phase 2 and Phase 5's exact statements as needing a short `lean_goal`-driven confirmation pass
before implementation, not as fully nailed-down specs.
