# Report 04 — B2 Fuel-Sufficiency Measure Design (HARD-mode spike)

- **Task**: 317, Phase 2a R1 blocker resolution
- **Scope**: RESEARCH ONLY. No `.lean` file was edited.
- **Sorry under repair**: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:985`
  (`intExpandBranches_openBranch_sat`, `fuel = 0` base case).
- **Reference grounding tier**: Tier 3 (implementation-backed) + Tier 1 (Fitting1983 /
  ChagrovZakharyaschev1997 background). BibKeys `Fitting1983`, `ChagrovZakharyaschev1997`
  both verified present in `references.bib`.

---

## VERDICT

**FEASIBLE-BUT-REQUIRES-SEMANTICS-CHANGE.**

Two distinct results, which the original R1 gate conflated:

1. **Termination / R1 gate — RESOLVED (feasible, no semantics change).** The primary
   hypothesis is essentially correct. A base-3 potential restricted to **F-signed compounds
   only** (call it `P`) strictly decreases on every world-creating / F-branching / F-linear
   step and is provably *invariant* under `propagatePersistence` and under every T-rule.
   This is exactly what the R1 gate asked for: a measure component that survives `F(→)`.
   Claims 1 and 2 of the hypothesis are **verified**; claim 3's F-side half is verified.

2. **Fuel-sufficiency at the *current* bound — NOT achievable (requires change).** The
   `fuel = 0` sorry does **not** need mere termination; it needs a *numeric* step bound
   `total_steps ≤ 2 ^ (2 * φ.complexity + 2)`. The worst-case number of expansion steps of
   the algorithm *as coded* is `2 ^ Θ(complexity²)`, which **exceeds** the provided fuel
   `2 ^ (2·complexity + 2) = 2 ^ Θ(complexity)`. No lexicographic or flattened measure can
   bring the initial value under the current fuel, because the true step count is larger than
   the fuel. Closing the sorry therefore requires **raising the fuel formula in
   `Expansion.lean`** (monotone-safe, but a definition change that re-touches the soundness /
   decidability proofs — task 316 territory) or adding **world-deduplication** to
   `Rules.lean`. Both escalate to a user architectural decision.

The lexicographic measure the task proposed is the right *termination* object and resolves the
stated R1 blocker, but the R1 blocker was not actually the thing standing between us and the
sorry. The sorry's real obstacle is that **the fuel constant is too small for the
un-deduplicated procedure.**

---

## Source-to-Implementation Mapping

| Source claim | BibKey / Source | Lean target | Translation notes |
|---|---|---|---|
| Intuitionistic `F(φ→ψ)` creates a world with `T(φ),F(ψ)` + persistence of positives | `Fitting1983` Ch.4 | `intFImpRule` (`Rules.lean:154-159`) | Faithful. Persistence copies **all** `T`-formulas, incl. already-expanded ones. |
| Positive persistence: `T(α)` at `w` ⟹ `T(α)` at `w'≥w` | `Fitting1983` Ch.4; `ChagrovZakharyaschev1997` §2.2 | `propagatePersistence` (`Rules.lean:139-141`) | Copies are all `.pos`. Never `.neg`. |
| Finite model property gives bounded worlds (≤ `2^#subformulas` with world-identification) | `ChagrovZakharyaschev1997` §2.2 | *not implemented*: `intFImpRule` never dedups worlds | This is the gap: the FMP bound the fuel was sized for assumes world-identification the code does not perform. |
| Base-3 exponential termination measure | task 376, `classicalExpMeasure` (`Classical/Completeness.lean:635-638`) | Template to port | Ports to the **F-side only**; the T-side breaks under persistence. |

---

## Findings

### F1 — Claim 1 VERIFIED: `propagatePersistence` copies only `T`-signed formulas

`posFormulasAt` (`Rules.lean:126-128`) filters `sf.sign == .pos`. `propagatePersistence`
(`Rules.lean:139-141`) maps those to `⟨.pos, φ, toWorld⟩` — every emitted formula is `.pos`.
`applyAllTImpRules` / `intTImpRule` (`Expansion.lean:118-127`, `Rules.lean:174-186`) likewise
emit only `some ⟨.pos, ψ, w'⟩`. **No persistence path ever emits an `.neg` (F-signed) formula.**
Therefore any measure counting *only F-signed* occurrences is untouched by all persistence
machinery. This is the crux that rescues the primary component.

### F2 — Claim 2 VERIFIED: world creation strictly decreases the F-side potential

`intFImpRule φ ψ w w' b` emits `[⟨.pos, φ, w'⟩, ⟨.neg, ψ, w'⟩] ++ persistent`
(`Rules.lean:157-159`). With `complexity` defined as `imp/and/or = 1 + cₗ + cᵣ`
(`Subformula.lean:193-198`):

- Consumed: the `F(φ→ψ)@w` occurrence, F-potential `3 ^ (1 + cφ + cψ)`.
- Emitted F-compound: `F(ψ)@w'`, F-potential `3 ^ cψ` (note `cψ = complexity(φ→ψ) − 1 − cφ`).
- Emitted `T(φ)@w'`: F-potential `0` (it is `.pos`).
- Persistence copies: F-potential `0` (all `.pos`, by F1).

Net change in F-potential `= 3^cψ − 3^(1+cφ+cψ) < 0`. **Strict decrease, with large slack.**

### F3 — Claim 3 (F-side) VERIFIED, (T-side) REFUTED

Enumerating every branch produced by `intApplyRuleFull` (`Rules.lean:245-268`) and the
persistence pre-pass (`Expansion.lean:222`, `applyPersistenceFixpoint`):

| Rule (`sf.sign, formula`) | `Rules.lean` | Kind | Effect on `P` (F-potential, base 3) | Effect on T-side |
|---|---|---|---|---|
| `T(φ∧ψ)` | 250-251 | linear | unchanged (adds only `.pos`) | consumes `T(∧)`, adds `T(φ),T(ψ)` |
| `F(φ∧ψ)` | 253-254 | **branch** | **↓** each branch: `−3^c + 3^{c'}`, `c'<c` | unchanged |
| `T(φ∨ψ)` | 256-257 | **branch** | unchanged | consumes `T(∨)`, each branch `T(φ)`/`T(ψ)` |
| `F(φ∨ψ)` | 259-260 | linear | **↓**: `−3^c + 3^{cφ}+3^{cψ}` (`<0`, base 3) | unchanged |
| `F(φ→ψ)` / `F(¬φ)` | 262-264 | linear + world | **↓** (F2) | inflates: `T(φ)` + persistence copies |
| `T(φ→ψ)` / `T(¬φ)` | notApplicable in step; handled by `applyPersistenceFixpoint` | persistent fixpoint | unchanged (adds only `.pos`) | inflates: adds `T(ψ)@w'` |
| atoms, `⊥`, `T(⊥)` | 268 | notApplicable | unchanged | unchanged |

**F-side (`P`) conclusion:** every rule that emits an F-compound (`F(∧)` branch, `F(∨)`
linear, `F(→)` world-creating) replaces one F-compound by strictly-smaller F-compounds, so
`P` strictly decreases; all other rules and *all persistence* leave `P` unchanged. The base-3
wrapper handles the `F(∨)` linear split `3^{cφ}+3^{cψ} < 3^{1+cφ+cψ}` (needs base `> 2`; base 3
suffices, identical to the classical trick in `classicalApplyOne_output_complexity`,
`Classical/Completeness.lean:609-630`).

**T-side (secondary `S`) REFUTATION:** any secondary that counts unexpanded `T`-compounds is
**increased by `applyPersistenceFixpoint`**, which runs before *every* step
(`Expansion.lean:222`). `T(φ→ψ)` formulas are never consumed (never marked `expanded`), so each
persistence pass may add a fresh `T(ψ)@w'` triple (checked absent, so added at most once per
triple, but still an increase). On a pure `T`-step iteration `P` is unchanged, and `S` can rise
(persistence) faster than the single `T`-compound the step consumes falls. **Hence a naive
2-tuple `Prod.Lex (P, S)` is not strictly decreasing per iteration.** Termination must instead
be argued from the monotone-growing bounded `expanded` set (F5), not from a per-step lex drop
on the secondary.

### F4 — Claim 4 VERIFIED: well-foundedness lemma exists

`WellFounded.prod_lex : WellFounded ra → WellFounded rb → WellFounded (Prod.Lex ra rb)`
— confirmed in `Mathlib.Order.RelClasses` via loogle. `Nat`'s `<` is well-founded
(`Nat.lt_wfRel` / `wellFounded_lt`). So `Prod.Lex (·<·) (·<·)` on `Nat × Nat` is well-founded.
**However, see F6: well-foundedness is not what the sorry needs.**

### F5 — Worlds are LINEARLY bounded: `W ≤ complexity(φ) + 1` (new, reusable)

Every F-formula that ever appears is a subformula of `φ` and originates only from F-decomposition
(no persistence emits F-formulas, F1). Assign each created world `w'` its **seed** `ρ(w')` = the
consequent `ψ` of the `F(φ→ψ)` that created it. Then:

- `complexity(ρ(child)) ≤ complexity(ρ(parent)) − 1` (the creating imp is an F-descendant of the
  parent's seed, and its consequent drops complexity by ≥1). So the seed tree has **depth ≤ c**.
- Children of one world come from F-descendants of its seed that are simultaneously F on the
  branch; these occupy **position-disjoint** slots of the seed (F(∨) takes both disjuncts, F(∧)
  branches to one conjunct), so `Σ_children (complexity(creating imp)) ≤ complexity(seed)`, i.e.
  `Σ_children (k(child) + 1) ≤ k(parent)` where `k(w) = complexity(ρ(w))`.

Let `N(k)` = worlds in a subtree whose root seed has complexity `k`. Then
`N(k) ≤ 1 + max { Σ N(kᵢ) : Σ (kᵢ + 1) ≤ k }`. By induction `N(k) ≤ k + 1`
(base `N(0)=1`; step `1 + Σ(kᵢ+1) ≤ 1 + k`). Root seed `φ`, `k = c`, so **`W ≤ c + 1`.**

This is a genuinely useful lemma for any future attempt and is **stronger** than the FMP `2^σ`
bound — but it does **not** rescue fuel, because the step count is dominated by *branching*, not
by world count (F6).

### F6 — THE CRUX: fuel-sufficiency needs a step bound `≤ 2^(2c+2)`, and the true step count is `2^Θ(c²)`

**What the sorry actually needs.** The classical proof (the template to imitate) closes its
`fuel=0` case by exhibiting a single Nat measure `classicalExpMeasure` with
`classicalExpMeasure initial ≤ 3 ^ φ.complexity` (`Classical/Completeness.lean:1273`) and
`fuel := 3 ^ φ.complexity` (`Classical/Expansion.lean:163`); each step strictly decreases both
measure and fuel, so `fuel = 0 ⟹ measure = 0 ⟹ saturated`. To port this, the intuitionistic
side needs a Nat measure `M` with `M(initial) ≤ 2^(2c+2)` (the fuel in
`Expansion.lean:295`/`308`) that strictly decreases per step. Equivalently: **total steps
consumed ≤ 2^(2c+2).** One fuel unit = one `intExpandBranches` step on one branch
(`Expansion.lean:237-252` each decrement `fuel'+1 → fuel'`), so total fuel = total size of the
expansion forest.

**Why no such `M` exists at the current bound.** Steps along any one root-to-leaf path are
bounded by the monotone `expanded` set (each step adds one `(sign,formula,world)` triple, never
re-added): `steps_per_path ≤ 2 · σ · W`, with `σ ≤ 2c+1` distinct subformulas and `W ≤ c+1`
(F5), i.e. `O(c²)`. The killer is **branching**: `F(∧)` and `T(∨)` are beta-rules, and
`propagatePersistence` copies every `T(∨)` compound to every new world (fresh label ⇒ fresh
triple ⇒ re-split), so the number of beta-steps on a single path is also `Θ(σ·W) = Θ(c²)` in
the worst case. Binary branching then gives `leaves ≤ 2^(beta_per_path)` and forest size
`= 2^Θ(c²)`.

Concretely: with a top antecedent `(p₁∨q₁) ∧ … ∧ (p_k∨q_k)` (introduced as `T(...)` by an
`F(→)`) sitting above a nested chain of `W` world-creating `F(→)`s, all `k` disjunctions persist
into all `W` worlds and re-split at each, giving `≈ 2^(k·W)` branches. The complexity budget
`c ≈ 2k + 2W` maximizes `k·W` at `k = W = c/4`, i.e. `≈ 2^(c²/16)` branches. For `c ≳ 33` this
exceeds `2^(2c+2)`.

**Consequence.** `M(initial)` for *any* correct step-counting measure is `≥ 2^Θ(c²) >
2^(2c+2)` in the worst case. The classical `Σ 3^branchComplexity` measure is not even monotone
here: world creation *raises* a branch's complexity (adds `F(ψ)` + persistence copies), so
`3^branchComplexity` goes *up* at exactly the `F(→)` step. There is no measure `< 2^(2c+2)`.
The `fuel=0` lemma `intExpandBranches_openBranch_sat` is therefore **not just unproven but
plausibly false** for large deeply-persisting inputs (the loop can hit `fuel=0` with an
unsaturated open branch).

---

## Adversarial Self-Verification (H4)

I tried hardest to refute the *negative* half of the verdict (that the fuel is insufficient),
since a wrong "insufficient" wrongly escalates to the user.

- **Riskiest step: is `beta_per_path` really `Θ(c²)`, or secretly `O(c)`?** If it were `O(c)`,
  leaves `≤ 2^{O(c)}` and fuel `2^(2c+2)` might suffice. I could not close this in favor of
  `O(c)`: persistence (`Expansion.lean:222` → `Rules.lean:139-141`) demonstrably copies `T(∨)`
  compounds to each of the `W ≤ c+1` worlds under a *fresh label*, and the `expanded` check is
  by exact `(sign,formula,label)` triple (`Expansion.lean:153`), so each copy re-splits. `k`
  independent persisted disjunctions across `W` worlds give `k·W` beta-steps on one path, and
  the complexity budget genuinely funds `k·W = Θ(c²)`. The `Θ(c²)` beta count stands.
- **Could closure short-circuit the blowup?** For a *valid* formula every branch closes, possibly
  early. But the sorry is the `openBranch → saturated` direction: for an *invalid* formula the
  returned open branch must itself be saturated, and a large countermodel needs the worlds/splits.
  Closure does not save this direction.
- **Could the proof be restructured to avoid the numeric bound?** No: at `fuel=0`,
  `intExpandBranches` returns the first non-closed branch from the *initial* list with **zero**
  expansion (`Expansion.lean:200-204`). If that branch is genuinely unsaturated, the lemma is
  false for that input — no proof exists. Saturation at `fuel=0` is *equivalent* to fuel
  sufficiency.
- **Confidence.** HIGH that the current fuel cannot be *proven* sufficient with any measure
  (the exponent gap linear-vs-quadratic is structural). MEDIUM-HIGH that it is actually
  *insufficient* (I did not transcribe an exact Lean counterexample formula and run it — that is
  the one remaining way this could be wrong; a concrete failing input would upgrade the verdict
  to a hard INFEASIBLE-as-coded / bug).
- **Verified-name check.** `WellFounded.prod_lex` (loogle, `Mathlib.Order.RelClasses`) — real.
  `classicalExpMeasure`, `classicalApplyOne_output_complexity`, `classicalBranchComplexity`
  (`Classical/Completeness.lean:635,609,473`) — read directly. Classical fuel `3^complexity`
  (`Classical/Expansion.lean:163`) and init bound `≤ 3^complexity`
  (`Classical/Completeness.lean:1273`) — read directly. No invented lemma names.

**Verification revised one claim:** the primary hypothesis's framing ("lex `(P,S)` resolves it")
is *downgraded* — `P` alone resolves R1/termination, but `(P,S)` is **not** per-step decreasing
(F3 refutation) and, more importantly, no `(P,S)` flattening fits under the current fuel (F6).

---

## Recommended Direction (revised Phase 2b/2c/2d)

The `Scheme.lean`-only territory of the current plan **cannot** close this sorry. Escalate to
the user with these three options, in order of increasing invasiveness:

- **Option A (recommended first): raise the fuel formula in `Expansion.lean`.** Change
  `intuitionisticTableau`/`minimalTableau` fuel (`Expansion.lean:295`, `:308`) from
  `2^(2*φ.complexity+2)` to a provably-sufficient bound, e.g.
  `2 ^ (2 * (2*φ.complexity+1) * (φ.complexity+1) + 1)` (an over-approximation of
  `2^(2σW)·steps_per_path` using `W ≤ c+1`, F5). This is **monotone-safe** for the
  `openBranch → saturated` direction (more fuel never un-saturates), but it is a definition
  change: re-verify the `closed`/soundness path (task 316) and the decision-procedure lemmas,
  which may or may not be fuel-generic. *User must approve the fuel-formula change.*
  - Revised **2b**: prove `W ≤ φ.complexity + 1` (`intExpandBranches_world_bound`, F5) — a
    self-contained, high-value lemma.
  - Revised **2c**: prove `steps_per_path ≤ 2σW` via the monotone `expanded` set + `W`-bound,
    yielding a single decreasing Nat measure `M` bounded by the *new* fuel.
  - Revised **2d**: port the classical `fuel=0 ⟹ saturated` closing argument
    (`Classical/Completeness.lean` structure) against `M` and the new fuel.
- **Option B: world-deduplication in `Rules.lean`.** Make `intFImpRule` reuse an existing world
  whose forced-subformula-set matches, restoring the FMP `W ≤ 2^σ` and (with dedup also stopping
  re-splits) a `2^(2c+2)`-compatible bound. This is a **soundness-affecting semantics change**
  in task 316's territory; needs its own plan + soundness re-proof.
- **Option C: keep the fuel, accept `[BLOCKED]`.** If neither change is authorized, the sorry
  stays blocked and the completeness theorem cannot be closed for this algorithm.

Do **not** proceed with a `Scheme.lean`-local measure: F6 shows none can exist under the current
fuel.

---

## Zero-Debt / escalation note

No `sorry`, `axiom`, or vacuous placeholder is recommended. The correct action is to escalate
the fuel-formula (Option A) or dedup (Option B) decision to the user, because both cross the
`Expansion.lean` / `Rules.lean` boundary that the current plan explicitly excludes and that
overlaps task 316.
