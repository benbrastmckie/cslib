# Blocker Root Cause and the Mathematically Correct Approach

- **Task**: 317 - Fill the remaining propositional/intuitionistic tableau completeness sorries
- **Started**: 2026-07-26T18:50:00Z
- **Completed**: 2026-07-27T02:11:05Z
- **Effort**: ~7h (research dispatch, read-only against `Cslib/`)
- **Dependencies**: None (this report supersedes the open question left by plan v12 Phase 3)
- **Repo state**: `fe1927df`; probe evidence reproduced against
  `Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` at that commit

**Sources/Inputs**

*Prior task artifacts*
- `specs/317_propositional_tableau_completeness/handoffs/12_world-bound-decision.md`
- `specs/317_propositional_tableau_completeness/handoffs/11_phase2-blocker-findings.md`
- `specs/317_propositional_tableau_completeness/handoffs/11_phase0-spike-decisions.md`
- `specs/317_propositional_tableau_completeness/plans/12_world-bound-prereq-threading.md` (index only)

*Library sources (read directly, not via prior notes)*
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` (full)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (full)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (§§ 58-112, 442-640, 993-1004,
  1478-1910, 2298-2380, 2500-2640, 2924-3045)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`,
  `.../Minimal/Completeness.lean`, `.../Intuitionistic/DecisionProcedure.lean`
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (§§ 118-190, 433-500, 755-820, 2641-2760)
- `Cslib/Foundations/Logic/Tableau/Measure.lean`, `Branch.lean`, `ClosureCondition.lean`,
  `SignedFormula.lean`
- `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean`,
  `.../MinDecidability.lean`
- `references.bib`

*Executed checks*
- Lean `#eval` via `lean_run_code` (two snippets, results inline below)
- `lean_verify Cslib.Logic.PL.decidableDerivableIntPropAxiomFMP`
- A validated Python re-implementation of the expansion loop (probe scripts, below)

**Artifacts**
- `specs/317_propositional_tableau_completeness/reports/13_blocker-root-cause-and-correct-approach.md` (this file)
- `specs/317_propositional_tableau_completeness/probes/int_tableau.py` (validated port)
- `specs/317_propositional_tableau_completeness/probes/check_atom_persist.py`
- `specs/317_propositional_tableau_completeness/probes/sweep_k.py`,
  `search_world_bound.py`, `random_search.py`, `sweep_out.txt`

**Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md
- **Sources/Inputs**: TBD
- **Artifacts**: TBD

---

## Executive Summary

- **The expansion loop does not terminate on a complexity-9 formula.** For
  `φ0 = (((a→b)→c) ∧ ((d→e)→f)) → ((u₁→v₁) ∨ (u₂→v₂))`, `intExpandBranches` creates a new
  Kripke world roughly every three steps, forever: world count 4/7/10/14/20/27/40/54/67/87 at
  fuel 10/20/30/40/60/80/120/160/200/260. From world 3 onward every world is an **exact
  structural duplicate of its grandparent** (verified: identical T-set and F-set, period 2).
  This is confirmed by Lean `#eval` on the unmodified library, not only by the probe harness.
- **Consequence 1 — the linear world bound is refuted, and so is any world bound.**
  `intApplyRuleFull_outputs_subset`'s `hnw : nextWorld ≤ φ0.complexity + 1`
  (`Scheme.lean:1813`) and the label range `List.range (φ.complexity + 2)` baked into
  `intUniverse` (`Scheme.lean:1575-1577`) are **false**. Plan v12 left this open; it is now
  closed, negatively. Twelve plan versions have been trying to prove a bound that does not
  exist.
- **Consequence 2 — the `sorry` at `Scheme.lean:2578` is a FALSE goal, not a hard one.**
  Lean-verified counter-instance: at `branches = [[F(p∧q)@0]]`, `expandedSets = [[]]`,
  `nextWorlds = [1]`, `edgeSets = [[]]`, every hypothesis of
  `intExpandBranches_openBranch_sat` holds and it returns `.openBranch [F(p∧q)@0]`, but
  `IBranchSaturation.sat_fand`'s premise evaluates `true` while both disjuncts evaluate
  `false`. No proof can close it; the lemma must be restated.
- **The recurring structural cause, named**: the "Deliverable 6" copy channel in
  `applyAllTImpRules` (`Expansion.lean:136-143`) — which copies `T(φ→ψ)` itself into every
  accessible world — was introduced to make `sat_timp`/`truthLemma`'s T-imp case provable, and
  it is **exactly** what makes world creation unbounded. Each copy BETA-resolves to a fresh
  `F(antecedent)` at a fresh world, which mints another world, which receives another copy. The
  two open obligations are in **direct mutual conflict**; every plan version fixed one and
  silently broke the other. That is why twelve versions failed.
- **The loop-check that should cut this is structurally unable to.** `intFImpReuseWitness?`
  (`Expansion.lean:283-311`) searches only worlds **reachable from** the creation site
  (`isAccessible edges w x`), i.e. descendants. The blocking world in a Fitting/`Sfor`-style
  loop-check is always an **ancestor**. Searching ancestors is unsound for `sat_fimp` as
  currently stated (which demands `w ≤ w'`), so the fix is not a tweak — it requires the
  standard blocking/quotient countermodel construction.
- **Recommendation**: re-scope. The four sorries cannot be closed by assembly, and the honest
  cost of the correct fix is a calculus + completeness-side redesign (est. 2500-4000 lines).
  Critically, **intuitionistic and minimal propositional decidability are already established
  sorry-free in CSLib** by the independent FMP route (`lean_verify` confirms axiom profile
  `{propext, Classical.choice, Quot.sound}` for `decidableDerivableIntPropAxiomFMP`), so the
  tableau route is a *second* proof of an already-proven result. Three options are costed in
  §Recommendations; my recommendation is Option B (restate the four obligations honestly and
  close the task as `[BLOCKED]` behind a scoped calculus-repair task), not a thirteenth
  incremental plan.

---

## Context & Scope

Four `sorry`s remain in the task tree, re-verified by direct grep at `fe1927df`:

| Location | Obligation |
|----------|-----------|
| `Scheme.lean:599` | `truthLemma` T-imp case (needs `sat_timp` at every *accessible* world) |
| `Scheme.lean:2578` | `intExpandBranches_openBranch_sat`, `fuel = 0` base case |
| `Intuitionistic/Completeness.lean:133` | `IValid φ` → per-`edges` forcing bridge |
| `Minimal/Completeness.lean:125` | `MValid φ` → per-`edges` forcing bridge |

The mandate directed me to (1) name the recurring structural cause, (2) interrogate the design,
(3) settle the numeric world-bound question decisively, (4) check whether the bound is needed at
all, and (5) be willing to conclude the task should be re-scoped. All five are answered below.

Per H2, every claim below is grounded in a file path with line numbers or in an executed check
whose output is reproduced. Prior handoffs were treated as hypotheses; two of them turned out to
be wrong (§F7).

---

## Source-to-Implementation Mapping (H3, Tier 1)

BibKeys verified against `references.bib` before citing.

| Source claim | BibKey | Verified in `references.bib` | Lean target | Translation notes |
|---|---|---|---|---|
| Intuitionistic tableaux with world-creating `F(→)` rule and persistence; termination by loop-check on subformula-forced-sets | `Fitting1983` (Ch. 4) | Yes, `references.bib:211` | `Cslib.Logic.PL.intApplyRuleFull`, `intExpandBranches` | The repo implements the rules but **not** Fitting's loop-check; see F3/F4 |
| Intuitionistic model theory / Kripke semantics for `IForces` | `Fitting1969` | Yes, `references.bib:204` | `Cslib.Logic.PL.IForces` | Cited in `Rules.lean:53` |
| Labelled sequent systems with explicit accessibility; loop-checking and termination | `NegriVonPlato2001` | Yes, `references.bib:913` | (no Lean target — candidate redesign basis) | §5.5 is cited in `Expansion.lean:264` but no code follows it |
| Kripke semantics background for the `≤`/accessibility frame | `ChagrovZakharyaschev1997` (§2.2) | Yes, `references.bib:75` | `intAccessPreorder` | Cited in `Rules.lean:54` |
| Intuitionistic proof theory / persistence | `TroelstraVanDalen1988` | Yes, `references.bib:500` | — | Available if a redesign needs it |
| `Sfor`-containment termination technique | `GargGenoveseNegri2012` | **NO — key absent** | `intFImpReuseWitness?` (`Expansion.lean:283`) | **Defect D3**: `Expansion.lean:210` asserts "BibKey added to `references.bib` in Phase 6". `grep -c GargGenoveseNegri2012 references.bib` = **0**. Dangling citation. |
| Contraction-free calculus G4ip/LJT | Dyckhoff 1992 | **NO — key absent** | — | `Expansion.lean:264` cites "Dyckhoff 1992" in prose with no BibKey; `grep -c Dyckhoff references.bib` = **0** |

Two dangling citations are recorded as defects D3/D4 in §Findings.

---

## Findings

### F1. The expansion loop provably does not terminate — Lean-verified [DECISIVE]

Method: I first wrote a line-by-line Python port of `Rules.lean` + `Expansion.lean` +
`Branch.extendMany`/`findContradiction` + `IntuitionisticClosure`
(`probes/int_tableau.py`), because `#eval` timed out for plan v12. **Fidelity was validated
before use**: the port reproduces the v12 handoff's Lean-computed data point exactly — branch
length **77**, **9** distinct labels `0..8`, and the identical 12-row `(F-signed .imp, label)`
diagnostic in the same order. I then re-confirmed every load-bearing number in Lean itself.

Take

```
φ0 = (((a→b)→c) ∧ ((d→e)→f)) → ((u₁→v₁) ∨ (u₂→v₂))     -- complexity 9
```

Lean `#eval` on the unmodified library (`intExpandBranches [[⟨.neg, φ0, 0⟩]] [[]] [1] [[]] fuel
isIntuitionisticallyClosed`, explicit small fuel so it returns):

| fuel | `b.length` | max label | distinct labels |
|---|---|---|---|
| 10 | 27 | 4 | 5 |
| 20 | 59 | 7 | 8 |
| 30 | 100 | **10** | 11 |
| 40 | 167 | **14** | 15 |

The Python harness agrees on all four rows, and continues: 21/27/40/54/67/87 labels at fuel
60/80/120/160/200/260. Growth is linear in fuel with **no saturation** — `intStepBranch` never
returns `none`.

The divergence is **structurally periodic**, not merely slow (this is the adversarial check
against "maybe it saturates later"). At fuel 70 the edge list is a single chain
`0→1→2→…→24`, and comparing each world's T-set and F-set against its grandparent's:

```
w= 3 vs  5: T-equal=True  F-equal=True
w= 4 vs  6: T-equal=True  F-equal=True
...  (identical for every w from 3 through 22)
```

with, for all odd `w ≥ 3`,
`T = {(A∧B), (a→b)→c, (d→e)→f, a, d}`, `F = {(a→b), e}`, and for all even `w ≥ 4`,
the same `T` with `F = {(a→b), (d→e), b}`. The two rules ping-pong forever with identical
content; only the label increments. The creation trace over the first 45 firings confirms the
period: `CREATE F(a→b)` → `REUSE F(a→b)` → `CREATE F(d→e)` → `CREATE F(a→b)` → …, with
15 creations attributed to `F(a→b)`, 14 to `F(d→e)`, 1 to `F(φ0)`.

**`intuitionisticTableau φ0` therefore burns its entire `intFuel φ0 = 3^836` budget** and
returns, from the `fuel = 0` case (`Expansion.lean:369-373`), an arbitrary non-saturated open
branch. It is not a decision procedure on this input.

### F2. The linear world bound is FALSE; so is universe containment [DECISIVE]

`intUniverse φ` (`Scheme.lean:1575-1577`) ranges worlds over `List.range (φ.complexity + 2)`,
so every member has `label ≤ φ.complexity + 1` (`intUniverse_mem_label`, `Scheme.lean:1699`).
For the φ0 above, `φ0.complexity = 9` (Lean-confirmed), so members have `label ≤ 10`. At fuel
40 the produced branch carries formulas at **label 14**.

Therefore:

- `hnw : nextWorld ≤ φ0.complexity + 1` (`Scheme.lean:1813`) is **false** — refuted, not
  unproven. Plan v12 correctly refuted the *injection route*; the *bound itself* is now
  refuted too.
- `∀ x ∈ b, x ∈ intUniverse φ0` — the `hUniv` invariant Phases 2/3 were built to thread — is
  **false**.
- No replacement bound of any size works: F1 shows the world count is unbounded in fuel, so
  there is no `f(φ0)` with `nextWorld ≤ f(φ0)`.

This closes mandate item 3 decisively. Method note: the Python harness was used for *search*;
every conclusion above is separately confirmed by Lean `#eval` on the unmodified library, so
the harness is a search accelerator, not a trusted oracle.

### F3. The mandate's item 4 — "is the bound even needed?" — is answered by F1/F2 in a stronger form

The question was whether downstream consumers could be restated to avoid `hnw`. They cannot be
*rescued* that way, because the underlying fact they would need is also false:

- `intExpandBranches_openBranch_sat`'s `fuel = 0` case needs the recursion to be
  unreachable at `fuel = 0`. The only available mechanism is the measure bound
  `intExpMeasure (intUniverse φ0) branches expandedSets ≤ fuel`, and `intExpMeasure`
  (`Scheme.lean:1901`) is defined *over* `intUniverse φ0`. F2 kills its premise.
- `truthLemma`'s T-imp case needs `sat_timp` at every accessible world, which needs
  `applyPersistenceFixpoint` to reach a *genuine* fixpoint. The only route to that in the file
  is `applyPersistenceFixpoint_genuine_of_count_le_fuel` (`Scheme.lean:2450`), whose count is
  again over `intUniverse φ0`. Same premise, same failure.
- Carrying a per-branch label-set containment instead of a numeric counter (v12's suggested
  alternative) does not help: F1 shows the label set itself is unbounded.

So the answer is not "the bound can be avoided" but "**nothing downstream of it can be saved
while the expansion diverges**".

### F4. Root cause: two design decisions in direct mutual conflict [NAMED]

This is the recurring structural cause the mandate asked me to name.

**Decision A — the "Deliverable 6" copy channel.** `applyAllTImpRules`
(`Expansion.lean:136-143`) copies `T(φ→ψ)` *itself* to every accessible world lacking a copy.
Its own docstring (`Expansion.lean:117-127`) states why: `intApplyRuleFull`'s `.pos, .imp`
BETA arm (`Rules.lean:274-275`) fires only *reflexively*, at the label of the specific copy it
is handed, so realizing "for every `w'` accessible from `w`, `F(φ)@w' ∨ T(ψ)@w'`" requires
every accessible world to carry its own copy. Decision A exists **solely** to make
`sat_timp`/`truthLemma`'s T-imp case (`Scheme.lean:599`) provable.

**Decision B — persistence propagation.** `intFImpRule` (`Rules.lean:154-159`) copies **all**
`T`-formulas from `w` into each freshly created `w'` via `propagatePersistence`.

**The conflict.** Under A+B, a world-creating step at `w` produces a child `w'` that receives a
fresh copy of every `T(φ→ψ)` at `w`. Each fresh copy is a *distinct* `(sign, formula, label)`
triple, so `intStepBranch`'s `expanded` guard (`Expansion.lean:172-177`) does not suppress it;
it BETA-resolves leftmost to `F(φ)@w'`; if `φ` is `.imp`-shaped this mints another world, which
receives another copy, ad infinitum. That is precisely the period-2 loop of F1. The docstring's
own termination claim — "termination is unaffected since the number of distinct
`(implication, world)` copies is bounded by `intUniverse φ0`" (`Expansion.lean:125-126`) — is
**circular**: it assumes the very world bound that A+B destroys.

Every plan version in this task has been fixing one side and breaking the other. Plan versions
up to v9 chased the fuel/measure side (Decision B's consequences); the "Deliverable 6" redesign
resolved GAP 2 by adding Decision A and thereby made the world count unbounded; v11/v12 then
went hunting for the world bound that A had just destroyed. Nobody checked that A and B are
compatible, because each dispatch inherited the other's docstring as fact.

### F5. The loop-check cannot cut the loop — and fixing it is not a tweak

`intFImpReuseWitness?` (`Expansion.lean:283-311`) is the repo's `Sfor`-containment loop-check.
On the F1 divergence it fires 15 times out of 45 and does not stop it. Reading the guard
against the F1 trace, the reason is exact:

1. **It searches the wrong direction.** The candidate must satisfy `isAccessible edges w x`,
   i.e. `x` reachable *from* `w` — a descendant. In a Fitting/`Sfor` loop-check the blocking
   world is always an **ancestor** (`Sfor` grows monotonically *along* accessibility, so the
   world that already realizes `Sfor(w')` is above `w`, not below). In F1, `Sfor(w)` is
   literally *constant* from `w = 3` on, so the containment condition would be satisfied by an
   ancestor every single time — but ancestors are never candidates.
2. **The Option-A conjunct.** The check additionally requires an explicit `F(ψ)@x` entry on the
   branch (`Expansion.lean:308`). At even worlds `F(b)` is present but `F(e)` is not, and at odd
   worlds vice versa — so even the reflexive candidate `x = w` alternately fails. That conjunct
   was added deliberately (`Expansion.lean:243-257`) because `sat_fimp`/`sfSatisfied` demand an
   explicit `F(ψ)@x`, and because the alternative (Option B, appending `F(ψ)@x`) was found
   **unsound** against `intExpandBranches_closed_unsat`.

The tension is genuine and mathematical, not an implementation slip: to reuse `x` as a
`sat_fimp` witness you need `w ≤ x` **and** `F(ψ)@x` on the branch; the blocking ancestor
satisfies neither. The standard literature resolution (`Fitting1983` Ch. 4; `NegriVonPlato2001`
for the labelled-sequent analogue) is **not** to reuse the ancestor as a witness but to *block*
the branch and build the countermodel over the finite **quotient** frame in which the blocked
world is identified with its blocking ancestor — at which point `w ≤ x` holds in the quotient.
That requires restating `IBranchSaturation.sat_fimp` relative to the quotient frame and
rewriting `truthLemma`'s F-imp case to read its witness off the quotient. It is a
completeness-side redesign, not a predicate tweak.

### F6. Reuse check: the in-repo Modal-K precedent, and why it does *not* port [REUSE PROTOCOL]

Per the CSLib reuse-first protocol I checked Foundations before proposing anything new.

**What exists and is reusable.** `Cslib/Foundations/Logic/Tableau/Measure.lean` (137 lines,
**0 sorries**) provides shared `geomCap Sf k = Σ_{i≤k} Sf^i` with `geomCap_succ`,
`geomCap_le_pow`, `geomCap_mul_eq_succ_sub_one`. `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
(3388 lines, **0 sorries**) solves the *structurally identical* obligation for Modal K: an
a-priori world bound `modalWorldBound φ := (2·complexity φ + 1)^(complexity φ + 1)`
(`FmpMeasure.lean:144-145`) proved as a per-step loop invariant via a proof-only **rank map**
(remaining modal-depth budget, frozen at creation as `parent_rank − 1`), an out-degree counter,
and a potential Φ (`FmpMeasure.lean:756-775`, `2641-2760`). Its docstring even records the same
failure mode this task hit: "The naive single-step statement … is **not sufficient**".

The intuitionistic development uses exactly **one** lemma from that shared module
(`sum_map_le_length_mul`, at `Scheme.lean:1596`) and reimplements everything else with a
*linear* bound instead of an exponential one. That is a real reuse gap.

**But — adversarial check — the Modal-K argument does not port as-is, and recommending "just
reuse it" would be wrong.** Modal K's rank map works because everything transferred parent→child
has strictly smaller modal depth, so the budget strictly decreases. In the intuitionistic
calculus `propagatePersistence` copies **all** `T`-formulas, including implications of the same
nesting depth (that is precisely the `R1-measure` blocker recorded at `Expansion.lean:264-273`).
There is no strictly-decreasing depth budget to hang `geomCap` on. The correct intuitionistic
analogue of the budget is the **forced-set `Sfor`**, which grows monotonically along
accessibility and lives in `Sub(φ0)` — giving chain length `≤ |Sub(φ0)|` and branching
`≤ |Sub(φ0)|`, hence a bound of `geomCap`-shape with `k = |Sub(φ0)|` rather than modal depth.
**That bound is only available once an effective loop-check enforces strict `Sfor` growth
along chains** — which, per F5, the current check does not.

So: `geomCap` and the Modal-K *proof architecture* are genuinely reusable, but only downstream
of the calculus repair, and with `Sfor` in place of modal depth.

### F7. Two positive findings, and two stale docstrings corrected

**Positive — atom persistence holds on produced branches.** The two Completeness bridges need
`intExtractValuation b` to be upward-closed along `isAccessible edges` (the phase-0 spike's
`IAtomPersist` premise-narrowing route). I audited the branches the real algorithm produces
across the v12 formula, three hand-built adversarial shapes (late atom at parent, conj after
creation, nested imp), and both closure predicates. In every case: atoms upward-closed **OK**,
*all* `T`-formulas upward-closed **OK**, `T`-implication copies complete **OK**, edge endpoints
are branch labels **OK**. The mechanism is that `propagatePersistence` copies the *compound*
`T`-formula and the child independently decomposes it. So the phase-0 spike's Question (b)
verdict is sound and the premise-narrowing route is viable — **on saturated branches**. It is
worth preserving.

**Positive — GAP 2 (determinacy) really is resolved.** `Scheme.lean:3020-3041` still asserts
"determinacy remains BLOCKED … the CONVERSE of `ih_φ'` … is not given by the induction". Read
against the current code this is **stale**. `sat_timp` is now an actual
`IBranchSaturation` field (`Scheme.lean:105-108`) in the reflexive form `T(φ→ψ)@w ∈ b →
F(φ)@w ∈ b ∨ T(ψ)@w ∈ b`, which discharges `truthLemma`'s T-imp case *without* any converse:
the `F(φ')@w'` arm contradicts the given `IForces w' φ'` via `ih_φ'.2`, and the `T(ψ')@w'` arm
gives the goal via `ih_ψ'.1`. What genuinely remains is GAP 1 (the copy must reach `w'`), which
F1/F2 now show to be unreachable. Note this makes `Scheme.lean:527`'s claim that "`sat_timp` is
NOT added as an `IBranchSaturation` field" **also stale** — it is at line 105.

**Defect D3 (dangling citation).** `Expansion.lean:210` states the BibKey
`GargGenoveseNegri2012` was "added to `references.bib` in Phase 6".
`grep -c GargGenoveseNegri2012 references.bib` = **0**.
- Current behavior: `intFImpReuseWitness?`'s docstring cites a BibKey that does not resolve.
- Required behavior: either add the entry (Garg, Genovese & Negri, *Countermodels from Sequent
  Calculi in Multi-Modal Logics*, LICS 2012) or replace the citation with `Fitting1983` Ch. 4.
- Isolation: `Expansion.lean:210` only; no code depends on it.

**Defect D4 (dangling citation).** `Expansion.lean:264` cites "Dyckhoff 1992" in prose;
`grep -c Dyckhoff references.bib` = **0**. Same disposition as D3.

### F8. Intuitionistic and minimal decidability are ALREADY sorry-free in CSLib

`lean_verify Cslib.Logic.PL.decidableDerivableIntPropAxiomFMP` returns axioms
`["propext", "Classical.choice", "Quot.sound"]` — **no `sorryAx`**. The finite-model-property
route in `Metalogic/IntDecidability.lean` (and `MinDecidability.lean`) establishes decidability
of `Derivable IntPropAxiom φ` / `Derivable MinPropAxiom φ` independently of the tableau, via a
`Σ`-bounded finite canonical Kripke model. Neither file contains a bare `sorry` (all `sorry`
occurrences are docstring prose).

This materially changes the cost/benefit: the tableau completeness theorem is a **second,
independent** proof of a result CSLib already has. That does not make it worthless — the
tableau gives a *computable* witness and an explicit countermodel — but it means the task is not
load-bearing for the library, and a large redesign should be a deliberate choice rather than a
default continuation.

---

## Decisions

1. **The open numeric question from plan v12 is CLOSED, negatively.** `nextWorld ≤ f(φ0)` holds
   for no `f`. Recorded with a Lean-verified counterexample (F1, F2).
2. **The `sorry` at `Scheme.lean:2578` is unfillable at its current statement** (Lean-verified
   counter-instance, F-summary bullet 3). Any plan that schedules "prove the fuel-0 case" is
   scheduling a false goal.
3. **No thirteenth incremental plan is warranted.** The evidence does not support one: the
   blocker is a calculus defect, not a proof-engineering gap.
4. **The `--hard` H5 divergence signal is confirmed.** Three-plus plan versions targeting the
   same lemma (`intExpandBranches_world_bound` / `hnw` / `hUniv`) is exactly the churn pattern
   H5 exists to catch, and the audit vindicates it.

---

## Recommendations

Prioritized. My recommendation is **Option B**.

### Option A — Repair the calculus (highest fidelity, highest cost)

Scope, in dependency order:

1. **Remove or bound the Deliverable-6 copy channel.** Either drop the `T(φ→ψ)` self-copy from
   `applyAllTImpRules` and recover `sat_timp`-at-accessible-worlds by making the `.pos, .imp`
   rule range over existing accessible labels (Fitting's actual rule shape,
   `Fitting1983` Ch. 4), or gate the copy so it cannot re-fire world creation.
2. **Replace `intFImpReuseWitness?` with an ancestor-directed `Sfor`-containment blocking
   check**, dropping the `F(ψ)@x` conjunct.
3. **Restate `IBranchSaturation.sat_fimp` over the blocking quotient frame** and rewrite
   `truthLemma`'s F-imp case (`Scheme.lean:600-607`) to read its witness off the quotient.
   Re-verify `intExpandBranches_closed_unsat` (`Minimal/Soundness.lean`) survives — this is
   where Option B was found unsound previously, so it is the main risk.
4. **Then** prove the world bound with the shared `geomCap` (`Foundations/.../Measure.lean`),
   mirroring `FmpMeasure.lean`'s rank-map/potential architecture but with `Sfor ⊆ Sub(φ0)` in
   place of modal depth. Re-size `intUniverse`'s world range and `intFuel` accordingly.
5. **Then** the four sorries become assembly, using the (verified-viable) `IAtomPersist`
   premise-narrowing for the two bridges.

Honest estimate: 2500-4000 lines, comparable to `FmpMeasure.lean`'s 3388. Steps 1-3 are a
calculus redesign that invalidates parts of `Soundness.lean` and the 43-row
`CslibTests/TableauConformance.lean` guard (which will change, since the algorithm's outputs
change). This is a multi-task programme, not a phase.

### Option B — Re-scope: restate honestly, mark `[BLOCKED]`, spawn a scoped repair task (RECOMMENDED)

1. Correct the three stale docstrings now (`Scheme.lean:3020-3041` GAP-2 block,
   `Scheme.lean:527` `sat_timp`-not-a-field claim, `Expansion.lean:125-126` circular
   termination claim), and fix defects D3/D4. Zero risk, removes the exact trap that misled
   twelve dispatches.
2. Replace the `Scheme.lean:2578` `sorry` context comment with the **refutation**: record that
   the goal is false at the current statement, with the `[[F(p∧q)@0]]` counter-instance, so no
   future dispatch attempts it.
3. Add a module-level note recording the F1 divergence with the complexity-9 witness, so the
   non-termination is discoverable from the code.
4. Mark task 317 `[BLOCKED]` on a new calculus-repair task carrying Option A steps 1-3.
5. Leave the four sorries in place. **The bare-sorry count does not go down** — the task's own
   constraint cannot be met without the redesign, and manufacturing a decrease by weakening a
   statement would violate the zero-debt policy.

This is deliverable in one dispatch, is entirely truthful, and unblocks the next planner.

### Option C — Abandon the tableau completeness route

Given F8 (decidability already sorry-free via FMP), retiring the tableau *completeness* claim
while keeping the tableau as a sound-only, computable proof-search device is defensible: mark
`intuitionisticTableau_complete`/`minimalTableau_complete` as not-provided, document the FMP
route as the decidability witness, and delete the dependent scaffolding. This *would* reduce the
sorry count. It is a product decision (does CSLib want a computable countermodel witness?) and
belongs to the user, not to me. I raise it because the mandate asked me to be willing to say so.

### Cross-cutting

- Do **not** schedule any further work on `intExpandBranches_world_bound`, `hnw`, or `hUniv`
  as currently stated. All three are refuted.
- Preserve the probe harness (`probes/int_tableau.py`) — validated against Lean, and the only
  practical way to test this algorithm's behavior at scale.

---

## Adversarial Self-Verification (H4)

I actively tried to refute my own central claim ("the expansion diverges; no world bound
exists"). Attempts and outcomes:

| # | Refutation attempt | Outcome |
|---|---|---|
| 1 | *The Python port is unfaithful; the divergence is a porting artifact.* | **Refuted.** Port reproduces the v12 Lean data point exactly (77 entries, 9 labels, identical 12-row diagnostic in identical order), and Lean `#eval` independently reproduces all four rows of the F1 table on the unmodified library. Every conclusion in F1/F2 has a Lean witness, not just a Python one. |
| 2 | *It saturates eventually; 260 steps is just not enough.* | **Refuted.** Worlds 3..22 are pairwise structurally identical to their grandparents (T-set and F-set equal, period 2), and the edge graph is a bare chain. The state is literally periodic; no additional fuel changes it. |
| 3 | *The `Scheme.lean:2578` goal is hard, not false.* | **Refuted.** Lean `#eval` shows all hypotheses satisfiable at `[[F(p∧q)@0]]`/`[[]]`/`[1]`/`[[]]` (`ILabelBound` holds: `bb.all (·.label ≤ 1)` = `true`; `IExpandedConsistent`/`IAllAccessConsistent` vacuous at `e = []`; lengths `(1,1)`), the loop returns that exact branch, `sat_fand`'s premise = `true`, both disjuncts = `false`. |
| 4 | *Just reuse Modal-K's `modalWorldBound` rank map.* | **My own recommendation, and I refuted it.** The rank map needs strictly-decreasing modal depth parent→child; `propagatePersistence` copies same-depth implications, so no such budget exists. Recommendation revised: `geomCap` architecture is reusable, but with `Sfor ⊆ Sub(φ0)` as the budget and only *after* the loop-check repair. |
| 5 | *Maybe the bridges' `IAtomPersist` route is also dead, so Option B understates the damage.* | **Not refuted — the route survives.** Audited across five formulas and both closure predicates; atom persistence, full T-persistence, T-implication copy completeness and edge-endpoint containment all hold on produced branches. Recorded as a preserved asset (F7). |
| 6 | *Prior handoffs already said the bound might be true (v12: "8 ≤ 11").* | **Superseded, not contradicted.** v12's counterexample happened to satisfy the bound; v12 explicitly left the bound open and its two stress tests timed out. The complexity-9 witness here is a different formula that breaches it. |
| 7 | *The `Scheme.lean:3020` GAP-2 block says determinacy is still blocked — maybe truthLemma is dead for a second, independent reason.* | **Refuted; that block is stale.** `sat_timp` is a live `IBranchSaturation` field (`Scheme.lean:105-108`) and its reflexive form suffices for the T-imp case with no converse. Corrected in F7 rather than inherited. |

**Uncertain claims, stated with confidence levels:**

- *High confidence (Lean-verified):* F1 divergence, F2 bound refutation, F7 stale docstrings,
  F8 FMP axiom profile, D3/D4 dangling BibKeys.
- *Medium confidence (verified by validated harness across a sample, not proved):* F7's atom-
  persistence positive finding. It holds on every formula I tested including three built
  specifically to break it, but it is an empirical result, not a theorem. A planner should treat
  it as "likely provable", not "proved".
- *Medium confidence (literature-grounded design judgement, not executed):* the Option A
  blocking/quotient construction. It is the standard treatment in `Fitting1983` Ch. 4 and the
  labelled-sequent analogue in `NegriVonPlato2001`, but I did not prototype it in Lean, and its
  interaction with `intExpandBranches_closed_unsat` (where the earlier Option B failed) is the
  single largest unretired risk.
- *Low confidence, flagged not asserted:* the 2500-4000 line estimate for Option A. It is
  anchored on `FmpMeasure.lean`'s 3388 lines for the analogous Modal-K result, which is a
  reference class of one.

**BibKey verification status:** all five cited keys (`Fitting1983`, `Fitting1969`,
`NegriVonPlato2001`, `ChagrovZakharyaschev1997`, `TroelstraVanDalen1988`) confirmed present in
`references.bib` by grep before use. Two keys referenced by existing library docstrings
(`GargGenoveseNegri2012`, Dyckhoff) confirmed **absent** and recorded as defects.

**Zero-debt compliance:** no recommendation defers a `sorry`, introduces an axiom, or weakens a
statement to vacuity. Option B explicitly declines to reduce the sorry count, because doing so
honestly is not possible without the redesign.

**Anti-analysis compliance (H2):** the first executed check (the validated port + its Lean
cross-check) landed within the read budget, and every finding above is a check result or a cited
line range, not a restatement of prior notes.

---

## Risks & Mitigations

| Risk | Mitigation |
|---|---|
| Option A's step 3 repeats the earlier Option-B soundness failure against `intExpandBranches_closed_unsat` | Prototype the quotient `sat_fimp` against `Minimal/Soundness.lean` **first**, as a gate, before any other Option A work |
| `CslibTests/TableauConformance.lean`'s 43-row guard encodes current (diverging) behavior | Expect it to change under Option A; under Option B it is untouched |
| The F1 divergence may already make some *landed, "green"* lemma vacuous or misleading | Not audited in this dispatch. Recommend a follow-up sweep of lemmas whose hypotheses mention `intUniverse` — several may now be vacuously satisfiable only, i.e. unusable |
| A future dispatch re-inherits a stale docstring and re-derives a refuted route | Option B step 1-3 exists specifically to prevent this; it is the highest-value low-cost action in this report |

---

## Context Extension Recommendations

- The `.claude/extensions/cslib` context has no guidance on **verifying a formalization's
  executable behavior before proving things about it**. A short pattern note — "if the
  definition is computable, `#eval` it against the property you are about to assume" — would
  have caught this defect eleven plan versions earlier.

---

## Appendix

**Reproduction (Lean, no files modified).** Both snippets were run via `lean_run_code` against
`Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` at `fe1927df`.

Snippet 1 (F1/F2): define `φ0 := .imp (.and (.imp (.imp pa pb) pc) (.imp (.imp pd pe) pf))
(.or (.imp u1 v1) (.imp u2 v2))` over `Proposition Nat`; `#eval φ0.complexity` → `9`;
`#eval` the branch length / max label / label count of
`intExpandBranches [[⟨.neg, φ0, 0⟩]] [[]] [1] [[]] fuel isIntuitionisticallyClosed` at
`fuel ∈ {10,20,30,40}` → the F1 table.

Snippet 2 (Decision 2): with `bb : IBranch Nat := [⟨.neg, .and pa pb, 0⟩]`,
`intExpandBranches [bb] [[]] [1] [[]] 0 isIntuitionisticallyClosed` returns
`openBranch, length=1, equals bb: true`; `sat_fand`'s premise `#eval`s `true`; both disjuncts
`#eval` `false`; `bb.all (·.label ≤ 1)` `#eval`s `true`; `([bb].length, [[]].length)` = `(1,1)`.

**Probe scripts** (under `specs/317_propositional_tableau_completeness/probes/`):
`int_tableau.py` (the validated port; `python3 int_tableau.py` runs the fidelity validation
against the v12 Lean data point), `check_atom_persist.py` (F7 audit), `sweep_k.py`,
`search_world_bound.py`, `random_search.py`.

**The m=1 tightness observation** (`sweep_out.txt`), which first indicated the bound had zero
margin before the outright counterexample was found: for
`φ0 = ((a→b)→c) → ((u₁→v₁) ∨ … ∨ (u_k→v_k))`, creations = `complexity` and
max `nextWorld` = `complexity + 1` **exactly**, for every `k ∈ {2,3,4,5,6}` — the bound is
saturated with zero slack on an infinite family, which is what motivated adding a second shared
implication (`m = 2`) and produced the divergence.
