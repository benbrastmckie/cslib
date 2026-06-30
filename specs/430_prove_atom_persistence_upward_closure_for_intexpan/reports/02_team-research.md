# Team Research Report: Task #430 — Atom Persistence / Upward-Closure

**Task**: 430 (`prove_atom_persistence_upward_closure_for_intexpan`)
**Parent**: 317 · **Topic**: PL-Tableau · **Type**: cslib
**Date**: 2026-06-30 · **Mode**: Team research (4 teammates: Primary, Alternatives, Critic, Horizons)
**Session**: sess_1782818058_465873
**Builds on**: `reports/01_atom-persistence-upward-closure.md` (seed)

---

## Summary (what changed vs. the seed)

The seed framed the task as "prove `intExtractValuation b` is upward-closed; probably switch the
Preorder from `≤`-on-ℕ to edge accessibility." Team research **confirms the Preorder switch is
mandatory** but **overturns the seed's central assumption**: the *raw* valuation is **not**
upward-closed under *any* construction-derived order, because persistence is only snapshotted at
world-creation and is **never re-applied to atoms** in the saturation fixpoint. The real
deliverable is therefore not "prove a branch invariant" but "**choose an order + valuation pair
for which upward-closure holds by construction**," and the work is **coupled to task 317**, not
independent as the seed hoped.

Three robust, decisively-grounded conclusions; one genuine open design choice; one cheap spike to
make before any implementation.

---

## Decisively settled

### S1. Approach B (linear chain / keep `≤`-on-ℕ) is DEAD — siblings occur. *(Teammate A, confirmed by B, C, D)*
`intStepBranch` selects the first applicable formula with **no per-world stratification**
(`Expansion.lean:150-157`); `intFImpRule` creates a fresh child of the *firing formula's own
label* (`Rules.lean:153-158`). Two `F(→)` formulas at the same parent ⇒ two children of that
parent ⇒ a genuine **tree with siblings**.
**Concrete counterexample (A):** `φ = (a→b) ∨ (c→d)` yields an open saturated branch with edges
`[(1,0),(2,0)]` (worlds 1, 2 siblings), `T(a)@1` present, `T(a)@2` absent — so `1 ≤ 2` on ℕ but
the valuation is **not** `≤`-upward-closed. `intTImpRule`'s own doc (`Rules.lean:171-173`)
explicitly states it *replaced* the old "`≥ w` proxy which treated sibling worlds as accessible."
→ The bridge can **never** close at the default `≤`-on-ℕ order.

### S2. One generic lemma discharges BOTH bridges. *(Teammates D + B, independent agreement)*
`intExtractValuation b w p := b.any (T(.atom p)@w)` (`Intuitionistic/Soundness.lean:1640`) and
`minBranchBotForces b w := b.any (T(.bot)@w)` (`Minimal/Soundness.lean:168`) are the **identical**
"positive formula at label `w`" query, differing only in the formula slot. Both are instances of a
generic `posAtWorld b φ w`. A single parametric `posAtWorld_upward_closed` (over arbitrary `φ`)
yields `v_upward_closed` (atoms) and `bf_upward_closed` (⊥) as one-line corollaries for the int
and min bridges respectively.
**Placement:** do **not** add fields to `IntMinScheme` — its module doc (`Scheme.lean:32-34`)
deliberately omits upward-closure, it bundles only the int/min *divergence* points, and `edges`
are out of its scope. Use **standalone corollaries** in a new file. (D; if structural uniformity
is ever demanded, add at most the single field `modelBot_uc`, never two.)

### S3. Edges are discarded by the result — a real prerequisite blocker. *(all four)*
`IntTableauResult.openBranch : IBranch Atom → …` (`Expansion.lean:79`) carries **no `IEdges`**;
the `edgeSets`/`doneEdges` threaded through the loop (`Expansion.lean:170-235`) are dropped at all
three return sites (`:182, :208, :232`), and the tree is **not** recoverable from the flat
`IBranch` label list (siblings make label order insufficient). Any edge-based order needs either
(i) widening the `openBranch` constructor to carry `IEdges` (~1 type + 3 ctors + ~8 matchers,
including both Completeness bridges and both decision procedures; Classical tableau is a separate
type and unaffected), or (ii) an existential edge-recovery lemma by induction on the loop (leaves
the type untouched). Either overlaps task 317's open structural lemmas.

### S4. The edge↔order toolkit ALREADY EXISTS, sorry-free, in the soundness proof. *(Teammate B — high-value)*
`Soundness.lean` contains the complete, green machinery the completeness direction needs:
`MonotoneEdges` (`:346`), `isAccessible_one_step` (`:447`), `isAccessible_go_mono_fuel` (`:505` —
**resolves the seed's fuel-transitivity worry**), `monotoneEdges_go` (`:535`, multi-step lift),
and `tableau_sound` (`Scheme.lean:245`) proving the whole `worldOf : Nat → World` + `MonotoneEdges`
wiring compiles. `iforces_persistence` (`Kripke.lean:125`) is reusable for any Preorder. This
pattern needs only the **one-directional** `isAccessible edges w w' → worldOf w ≤ worldOf w'` —
never full `Bool` transitivity.

---

## The genuine open question (conflict resolved into a decision)

**Conflict:** Teammate B leaned on the soundness `MonotoneEdges` edge route assuming persistence
makes the raw valuation edge-closed. Teammates **A and C independently refuted that premise** and
this is the most important finding of the round:

> `propagatePersistence` runs **only** at child creation inside `intFImpRule` (`Rules.lean:157-158`)
> — a one-time snapshot. The saturation fixpoint `applyPersistenceFixpoint → intTImpRule`
> (`Expansion.lean:133`, `Rules.lean:174`) propagates **only implication consequents**, never bare
> atoms. So a `T(p)@w` added to an *existing* parent `w` by a later `∧`/`∨` split (after its child
> `w'` was already created) is propagated by **neither** mechanism. ⇒ Raw `intExtractValuation` is
> **not** upward-closed even under the edge order; "raw val is edge-UC" is unproven and **likely
> false** (it reduces to the same expansion-ordering/fixpoint-completeness invariant as 317's B2
> leaf sorries).

So upward-closure must be **engineered**, not discovered. Two viable routes (pick via the spike
below):

### Route A — Closure valuation over edge accessibility *(Teammate A; uses S4 toolkit)*
Define `IAccessible edges := Relation.ReflTransGen (fun p c => (c,p) ∈ edges)` (free reflexivity +
transitivity ⇒ `Preorder`; **A's Q2 recommendation, preferred over the fueled `Bool` DFS**), and
an **ancestor-closure valuation** `intExtractValuationUC b edges w p := ∃ w₀, IAccessible edges w₀ w
∧ rawval b w₀ p`. Upward-closure is then a **3-line `ReflTransGen.trans`** proof. Cost: (a) needs
edges threaded out (S3); (b) the truth lemma must be re-proved for the closure valuation — the
residual **F-atom soundness** direction (`val' w p → raw membership`) relocates into 317's
`truthLemma` and is the genuine remaining difficulty.

### Route C — Specialization / containment preorder *(Teammate C; the option the seed missed)*
Order worlds by valuation containment itself: `w ⊑ w' := ∀ p, rawval b w p → rawval b w' p`. Then
`v_upward_closed` is **true by definition** — no edges, no closure valuation, S3 blocker sidestepped
entirely. Cost: must verify the `truthLemma` cases (especially `imp-F`, `Scheme.lean:335`) still
hold under `⊑`, and that `bf`/`⊥` containment also holds; the order is coarser, which C notes may
make 317's still-open **imp-T** sorry *easier*. Risk: `⊑` is a `Preorder` on ℕ but, like Route A,
cannot be injected only at the bridge (see next paragraph).

**Both routes require a non-default order in `truthLemma`/`openBranch_countermodel`/`tableau_complete`.**
C verified (S-fact) the bridges' `sorry`s sit *after* `apply tableau_complete; intro _b`
(`Completeness.lean:108-112`, `Minimal/Completeness.lean:105-109`), so the goal's `Preorder` is
already fixed at the default `≤` — the seed's "freedom to choose the order" is **not exercisable at
the bridge alone**. B confirmed `letI`/instance-diamond hacks fail; the clean mechanism is the
soundness proof's **abstract `World` + `worldOf` parameter** (Route A) or a wrapper type (Route C),
i.e. a **signature change to the shared lemmas → coupled to task 317**.

---

## Recommended plan

1. **Falsification spike first (cheap, decisive).** *(C)* In a scratch Lean file, build the
   `(a→b)∨(c→d)` branch (A's counterexample) and: (i) confirm raw `intExtractValuation` is not
   edge-upward-closed (expected: confirms the A/C refutation, kills "raw val is edge-UC"); (ii)
   prototype the containment preorder `⊑` and check whether the `truthLemma` `imp-F` line still
   goes through. Outcome selects Route A vs Route C before any plumbing is touched.
2. **Generic lemma (S2), order-agnostic part.** Add `posAtWorld_upward_closed` + the two
   corollaries in a new file; this part is reusable regardless of route.
3. **If Route A:** thread edges out (S3, prefer the existential-recovery lemma to avoid the
   type/matcher churn), define `IAccessible` via `ReflTransGen`, reuse the soundness toolkit (S4),
   define `intExtractValuationUC`, prove UC (3 lines).
4. **Coordinate the order-switch with task 317** (NOT independent — corrects the seed). The only
   green `truthLemma` proof that breaks is `imp-F` (`Scheme.lean:335`, consumes `sat_fimp`'s Nat-`≤`
   witness, `Scheme.lean:97`); `and`/`or`/`atom`/`bot` are world-local and order-agnostic (seed
   correct, C confirmed). Restate `sat_fimp` to the chosen order; nothing becomes *false*, only
   needs re-deriving. Sequence so two agents never edit the `truthLemma` block concurrently.
5. **Discharge both bridges** via the generic corollaries at the new order.

---

## Cross-task generalization *(Teammate D)*
The same `≤`-on-ℕ-vs-tree defect is **confirmed** in temporal task 301
(`Temporal/Tableau/Completeness.lean:34-70,255,330`; `ordConstraints_strict` false-as-stated) and
**looms** for modal 299/385. `Relation.ReflTransGen` currently has **zero** uses in
`Cslib/Logics/`. Recommendation: factor the `edges → Preorder ℕ` (RTC accessibility) construction
as a small reusable utility so transitivity is proved once and lifts to those tableaux.

---

## Risk / confidence
- **HIGH** on all code facts (siblings, edges-discarded, soundness toolkit, val≡bf, the
  snapshot-only persistence gap) — every claim grounded in `file:line` and cross-checked by ≥2
  teammates.
- **MEDIUM** on whether *any* upward-closure of the raw valuation is ultimately true (A/C: likely
  not) → this is exactly what the spike settles.
- **MEDIUM** on Route A vs Route C — decide post-spike.
- No new axioms in any path.

## Open questions carried to planning
1. Spike result: raw val edge-UC false? containment-preorder `truthLemma`-compatible? → Route A vs C.
2. Edge threading: existential-recovery lemma vs result-type widening (S3) — only if Route A.
3. Exact `sat_fimp` restatement and the 317 coordination point for the order-switch.
4. Whether to land the RTC-accessibility utility as a shared cross-tableau asset now or later.

## Teammate contributions
| Teammate | Angle | Status | Confidence | Findings file |
|----------|-------|--------|------------|---------------|
| A | Primary (siblings, transitivity) | completed | high | `02_teammate-a-findings.md` |
| B | Alternatives (wiring, prior art) | completed | high / med | `02_teammate-b-findings.md` |
| C | Critic (premise stress-test) | completed | high / med | `02_teammate-c-findings.md` |
| D | Horizons (shared lemma, generalization) | completed | high | `02_teammate-d-findings.md` |

## Key references
- Bridges: `Intuitionistic/Completeness.lean:105-112`, `Minimal/Completeness.lean:105-109`.
- Order fixed at: `truthLemma` `Scheme.lean:303`, `openBranch_countermodel` `:730`,
  `tableau_complete` `:775` (default `Preorder ℕ`).
- Persistence: `Rules.lean:138` (`propagatePersistence`), `:153-158` (`intFImpRule`), `:171-174`
  (`intTImpRule`), `Expansion.lean:79` (`openBranch` discards edges), `:133` (fixpoint),
  `:150-157` (no per-world stratification → siblings).
- Soundness toolkit (reuse): `Soundness.lean:346/447/505/535`, `Scheme.lean:245` (`tableau_sound`).
- Valuations: `Intuitionistic/Soundness.lean:1640`, `Minimal/Soundness.lean:168`;
  semantics `Kripke.lean:81/125/145/153`.
- Cross-task: `specs/301_temporal_tableau/.orchestrator-handoff.json`;
  parent `specs/317_propositional_tableau_completeness/.orchestrator-handoff.json`.
