# Research Report: `temporalTruthLemma_propositional` (atom/bot/imp cases)

**Task**: 427 (decomposed from 301, blocker B)
**Date**: 2026-06-30
**Agent**: cslib-research-agent
**Scope**: Prove `temporalTruthLemma_propositional` sorry-free for the propositional
fragment (atom / bot / imp) of the temporal tableau, in
`Cslib/Logics/Temporal/Tableau/Completeness.lean`.
**Base commit**: `7f052834` (green). The lemma is currently only a *commented-out*
BLOCKED stub — it must be introduced as a real declaration.

---

## Executive Summary (the one decisive finding)

The temporal `Formula` type is **minimal / Łukasiewicz-encoded**:

```lean
inductive Formula (Atom : Type u) where
  | atom (p : Atom) | bot | imp (φ₁ φ₂) | untl (φ₁ φ₂) | snce (φ₁ φ₂)
```

`and` / `or` / `neg` are **not constructors** — they are `abbrev`s that expand into nested
`imp`/`bot`:

| Connective | Encoding |
|---|---|
| `neg a` | `imp a bot` |
| `or a b` | `imp (imp a bot) b` |
| `and a b` | `imp (imp a (imp b bot)) bot` |

The tableau's propositional rule dispatch (`tryAllPropRules`) recognises these encoded
shapes via decomposition functions (`tempAndOf?`, `tempOrOf?`, `tempNegOf?`,
`tempImpOf?`) and fires `andPos`/`orPos`/`negPos` **in preference to** `impPos`. When it
fires `andPos` on the encoded `and a b = imp (imp a (imp b bot)) bot`, it emits
`T(a)` and `T(b)` — where `a` and `b` are **deep sub-formulas**, not immediate
sub-formulas of `imp φ' ψ'`.

**Consequence (root cause of the prior stall):** to discharge the imp case you need the
truth-lemma IH for `a` and `b`, but **neither** structural `induction φ` **nor**
`induction (hprop : IsPropositional φ)` supplies it — both give IHs only for the
*immediate* sub-formulas (`φ'`, `ψ'`). The correct induction principle is **strong
(well-founded) induction on `Formula.complexity`**, which yields IHs for **all** strictly
smaller sub-formulas. The encoded `a`, `b` always have strictly smaller complexity, so the
strong IH applies. This is the precise meaning of the task's "generalized structural
induction giving sub-formula IHs."

---

## Deliverable 1 — Current statement and reusable base-case lemmas

### 1a. The target lemma (currently commented BLOCKED, `Completeness.lean` lines 264–294)

```lean
-- lemma temporalTruthLemma_propositional
--     (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
--     (hH : temporalHintikkaSet b ord tracker)
--     (φ : Formula Atom) (t : TimeIndex) :
--     (b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) →
--       Satisfies (extractModel b) t φ) ∧
--     (b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) →
--       ¬ Satisfies (extractModel b) t φ) := by
--   induction φ with
--   | atom p => ...
--   | bot => ...
--   | imp φ ψ ih_φ ih_ψ => sorry -- BLOCKED
--   | untl .. => ... -- FMP, out of scope
--   | snce .. => ... -- FMP, out of scope
```

The real declaration to be introduced must be **restricted to propositional φ** (it cannot
mention `untl`/`snce`, which are FMP-blocked — tasks 423/425). It therefore takes an
`IsPropositional φ` hypothesis. `IsPropositional` **does not yet exist in the codebase**
(`grep` finds it only in the WIP); it must be added:

```lean
inductive IsPropositional : Formula Atom → Prop where
  | atom (p : Atom) : IsPropositional (.atom p)
  | bot : IsPropositional .bot
  | imp {φ ψ : Formula Atom} (hφ : IsPropositional φ) (hψ : IsPropositional ψ) :
      IsPropositional (.imp φ ψ)
```

(Closed under `imp`/`atom`/`bot` only; since `and`/`or`/`neg` are `imp`/`bot` encodings,
this predicate automatically covers the whole classical propositional fragment.)

### 1b. The three reusable base-case lemmas (already proved, `Completeness.lean`)

```lean
-- line 117
lemma extractModel_atomPos_sat (b : TBranch Atom) (t : TimeIndex) (p : Atom)
    (hmem : (⟨.pos, .atom p, t⟩ : TSF Atom) ∈ b) :
    Satisfies (extractModel b) t (.atom p)

-- line 125
lemma extractModel_bot_false (b : TBranch Atom) (t : TimeIndex) :
    ¬ Satisfies (extractModel b) t .bot

-- line 191
lemma extractModel_atom_neg_notSat
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hopen : isTemporalClosed b ord tracker = false)
    (t : TimeIndex) (p : Atom)
    (hmem : (⟨.neg, .atom p, t⟩ : TSF Atom) ∈ b) :
    ¬ Satisfies (extractModel b) t (.atom p)
```

Plus the open-branch structural lemma needed for the `T(bot)` sub-case
(`Completeness.lean` line 133):

```lean
lemma openBranch_noBotPos (b : TBranch Atom) (ord : TimeOrdering)
    (tracker : EventualityTracker Atom)
    (hopen : isTemporalClosed b ord tracker = false) :
    ¬ ∃ t, (⟨.pos, .bot, t⟩ : TSF Atom) ∈ b
```

The WIP also provides four trivial `any ↔ ∈` bridge lemmas which should be reused
(`any_pos_mem`, `any_neg_mem`, `mem_to_any_pos`, `mem_to_any_neg`, WIP lines 242–276).

---

## Deliverable 2 — The propositional template (`Propositional/Tableau/Classical/Completeness.lean`)

`classicalTruthLemma` (lines 84–429) is the reference. Its structure:

- `obtain ⟨hopen, hrule⟩ := hH` then **`induction φ with`** (structural on the
  `Proposition` type).
- For each connective it splits `constructor` into the T-direction and F-direction.
- **imp case (lines 169–349):** it extracts the witness `sf`, gets the Hintikka output
  `hout := hrule sf hsfmem`, then **`cases hbot : c`** (cases — *not* induction — on the
  **consequent** `c`) to read off the shape of `classicalApplyOne sf`. For each shape it
  proves `classicalApplyOne sf = .linear/.branching [...]` by `obtain ⟨s, fm, l⟩ := sf;
  subst …; rfl`, rewrites `hout`, pulls the rule outputs out of the branch with
  `List.any_eq_true.mpr`, and finishes with the **immediate** IHs `ih_a`, `ih_c` plus
  `BoolEvaluate_imp`.

### Why the template is *easy* and the temporal version is *hard*

In the classical `Proposition` type, `and`/`or`/`neg` are **primitive constructors**, so
`classicalApplyOne (T(and a c))` directly yields `T(a)`, `T(c)` with `a`,`c` the
**immediate** sub-formulas — `ih_a`/`ih_c` from `induction φ` suffice, and only a
**single, shallow `cases` on the consequent** is ever needed (just to learn the rule
output shape; the IHs are never deep).

The temporal type has no `and`/`or`/`neg` constructors, so the decomposition happens
*inside* an `imp` chain and exposes deep sub-formulas. The single-level `cases` + immediate
IH recipe **breaks** for the encoded `and`/`or` rules. This is the entire difficulty.

Key induction-principle takeaway from the template: **use `cases` (bounded shape split) to
determine the rule, and IH to conclude satisfaction — never `induction` on the
sub-formula's well-formedness proof.**

---

## Deliverable 3 — Review of the 1150-line WIP attempt

File: `specs/301_temporal_tableau/.wip-Completeness-truthlemma-attempt.lean`.

**Shape it converged on:** `induction hprop` (induction on the `IsPropositional φ` proof,
lines 295+). In the `imp` case (line 309) it correctly obtains `ih_φ`, `ih_ψ` for the
immediate sub-formulas. But to compute the rule output of `tryAllPropRules` it then did
**nested `induction hφ` / `induction hψ`** (and recursively `induction hφ2`,
`induction hφ22`, … lines 327, 395, 486, 682, …) on the *IsPropositional proofs of the
sub-formulas*, manually unrolling the formula shape several levels deep.

**Where it stalled (the single real `sorry`, line 629):** the `andPos`-encoded case
`T(imp φ1 (imp φ21 bot))` with `ψ = bot` — i.e. `and φ1 φ21`. The Hintikka output gives
`T(φ1)` and `T(φ21)`. To finish it needs the truth-lemma IH for **both** `φ1` and `φ21`
*simultaneously*. The nested `induction hφ`/`induction hφ2` had by then produced a tangle
of IHs (`ih_φ`, `ih_φ1`, `ih_φ2`, `ih_φ21`, `ih_φ22`, …) at mismatched recursion depths,
and no single coherent IH for both deep sub-formulas was available at that point. The
~80-line diagnostic comment (lines 546–629) is the author working this out in prose and
concluding: *"This is the fundamental issue: I need IHs for sub-formulas, but the outer
induction only gives me IHs for φ and ψ … Let me restructure the proof to use GENERALIZED
induction that gives me sub-IHs."* — then `sorry`.

**Assessment:** the WIP's F-direction (lines 721–1000) was *brute-forced through* by
nesting inductions deep enough that the needed IHs happened to be in scope for each
manually enumerated shape — but this does **not scale** and is not closeable for the
`andPos` T-direction. The diagnosis is correct; the fix is exactly the restructuring it
names but never performs. **Do not resume from the WIP's `induction hprop` skeleton** —
its nested-induction strategy is the trap. Reuse only its base cases (atom/bot, lines
296–308) and the `any/mem` bridge lemmas.

---

## Deliverable 4 — Strengthened statement + proof skeleton

### 4a. The rule-firing decision table (ground truth from `Defs.lean` + `PropositionalRules.lean`)

`tryAllPropRules` tries rules in order `andPos, andNeg, orPos, orNeg, impPos, impNeg,
negPos, negNeg` and takes the **first applicable**. For a **positive** `T(imp φ' ψ')`
(only the `*Pos` rules can apply):

| Condition on `imp φ' ψ'` | Rule fired | Output (label `t`) | IH needed |
|---|---|---|---|
| `φ' = imp a (imp b bot)` ∧ `ψ' = bot` (`and a b`) | `andPos` | linear `T(a), T(b)` | IH `a`, IH `b` (**deep**) |
| `φ' = imp a bot` (`or a ψ'`) | `orPos` | branch `T(a)` \| `T(ψ')` | IH `a` (**deep**), IH `ψ'` |
| `ψ' ≠ bot` ∧ `φ' ≠ imp _ bot` (proper imp) | `impPos` | branch `F(φ')` \| `T(ψ')` | IH `φ'`, IH `ψ'` (immediate) |
| `ψ' = bot` ∧ not `and`-shape (`neg φ'`) | `negPos` | linear `F(φ')` | IH `φ'` (immediate) |

For **negative** `F(imp φ' ψ')` the dual rules `andNeg`/`orNeg`/`impNeg`/`negNeg` fire by
the same shape conditions (see template lines 272–349 and WIP lines 721–1000 for the exact
outputs). `andNeg` (= `F(and a b)`) branches `F(a) | F(b)` — again deep sub-formulas.

The two rows requiring **deep** IHs (`andPos`/`orPos`, and dually `andNeg`/`orNeg`) are
exactly why immediate-IH induction fails.

### 4b. Strengthened statement (strong induction on `complexity`)

`Formula.complexity` (`Formula.lean` line 204) is ≥ 1 for every formula and, for the
generic `imp φ' ψ'` case, equals `1 + complexity φ' + complexity ψ'` (the temporal special
cases all require `untl`/`snce` and never match propositional formulas). Therefore **every
strict sub-formula of a propositional formula has strictly smaller complexity** — including
the deep `a`, `b` of an encoded `and`/`or`. This is the well-founded measure.

Recommended robust formulation — an auxiliary bounded by a `Nat` fuel, proved by ordinary
`Nat.rec` (no Mathlib lemma-name hunting; `Nat.strongRecOn` from Batteries is a valid
alternative):

```lean
private lemma temporalTruthLemma_propositional_aux
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hopen : isTemporalClosed b ord tracker = false)
    (hrule : ∀ sf ∈ b, … )            -- the second component of `temporalHintikkaSet`
    (n : Nat) :
    ∀ (φ : Formula Atom), φ.complexity ≤ n → IsPropositional φ → ∀ (t : TimeIndex),
      (b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) →
        Satisfies (extractModel b) t φ) ∧
      (b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) →
        ¬ Satisfies (extractModel b) t φ) := by
  induction n with
  | zero =>
      intro φ hle hp t
      exact absurd hle (by have := Formula.one_le_complexity φ; omega)   -- complexity ≥ 1
  | succ n ih =>
      intro φ hle hp t
      -- `ih` : the full statement for every ψ with `ψ.complexity ≤ n`.
      -- Crucially, every strict sub-formula here has complexity ≤ n.
      cases hp with
      | atom p =>
          refine ⟨fun hmem => ?_, fun hmem => ?_⟩
          · exact extractModel_atomPos_sat b t p (any_pos_mem b t (.atom p) hmem)
          · exact extractModel_atom_neg_notSat b ord tracker hopen t p
              (any_neg_mem b t (.atom p) hmem)
      | bot =>
          refine ⟨fun hmem => ?_, fun _ => extractModel_bot_false b t⟩
          exact absurd ⟨t, any_pos_mem b t .bot hmem⟩
            (openBranch_noBotPos b ord tracker hopen)
      | imp hφ' hψ' =>
          -- φ = .imp φ' ψ'.  Determine the fired rule by a BOUNDED `match` on the
          -- shapes of φ' and ψ' (NOT induction).  See decision table in §4a.
          -- For each rule, pull outputs from the branch via `hrule` + `mem_to_any_*`,
          -- then apply `ih` to the OUTPUT sub-formulas (each has complexity ≤ n by
          -- `Formula.complexity` arithmetic + `hle`), and close with the `Satisfies`
          -- simp lemmas (`Satisfies.imp_iff`, `Satisfies.bot_false`).
          sorry  -- to be filled per §4c
```

Then the public lemma is a one-liner:

```lean
lemma temporalTruthLemma_propositional
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hH : temporalHintikkaSet b ord tracker)
    (φ : Formula Atom) (hprop : IsPropositional φ) (t : TimeIndex) :
    (b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) →
      Satisfies (extractModel b) t φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) →
      ¬ Satisfies (extractModel b) t φ) := by
  obtain ⟨hopen, hrule⟩ := hH
  exact temporalTruthLemma_propositional_aux b ord tracker hopen hrule
    φ.complexity φ le_rfl hprop t
```

> Note: the `untl`/`snce` constructors never appear because `IsPropositional` has no such
> constructor — `cases hp` simply does not generate those branches. This is why the lemma
> is *total* over its (propositional) domain with no FMP dependency.

### 4c. The imp case in detail (the only nontrivial work)

Inside `| imp hφ' hψ' =>` (so `φ = .imp φ' ψ'`, with `hφ' : IsPropositional φ'`,
`hψ' : IsPropositional ψ'` in scope):

**Determining the rule** — case-split with bounded `match`/`cases` on the *formula*
shapes, mirroring the §4a table. Concretely a single `cases ψ'` then, in the `ψ' = bot`
branch, `cases φ'` (and one more level to detect `imp a (imp b bot)`); in the `ψ' ≠ bot`
branches `cases φ'` to detect the `imp a bot` (or) shape. Each leaf reduces
`tryAllPropRules … = .linear/.branching […]` by
`simp only [tryAllPropRules, applyPropRule, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
RuleResult.isApplicable, List.map, List.find?]` (exactly the simp set the WIP already
uses successfully at every leaf, e.g. WIP line 333).

**Pulling outputs from the branch** — from `hrule sf hsfmem` (where `sf = ⟨.pos, .imp φ' ψ', t⟩`)
and the reduced rule result, use the WIP's `mem_to_any_pos` / `mem_to_any_neg` bridges to
get `b.any … = true` for each output signed formula.

**Applying the IH and closing** — for each output formula `χ` (one of `φ'`, `ψ'`, `a`, `b`,
all strict sub-formulas), obtain its complexity bound `χ.complexity ≤ n` from `hle`
(`Formula.complexity` of `imp …` ≥ `1 + …`, so `omega` closes it given the matched shape),
obtain `IsPropositional χ` by inverting `hφ'`/`hψ'` (`cases hφ'` once for the `or`/`and`
deep parts), then apply `ih χ (by omega) χ_prop t`. Finally reconcile with the goal's
`Satisfies (extractModel b) t (imp φ' ψ')` using `simp only [Satisfies.imp_iff,
Satisfies.bot_false]` — this unfolds the encoded `and`/`or`/`neg` satisfaction down to the
sub-formula satisfactions the IH produced.

Per-rule closing logic (T-direction):

- **andPos** (`and a b`): goal `Satisfies … (and a b)`; `simp [Satisfies.imp_iff,
  Satisfies.bot_false]` turns it into `Satisfies a ∧ Satisfies b` (after de Morgan
  unfolding of the encoding); supply `(ih a …).1 …` and `(ih b …).1 …`.
- **orPos** (`or a ψ'`): branch hypothesis gives `T(a)` **or** `T(ψ')`; `rcases` and feed
  the matching IH; `simp [Satisfies.imp_iff, Satisfies.bot_false]`.
- **impPos** (proper): branch gives `F(φ')` or `T(ψ')`; use `(ih φ' …).2` (neg) resp.
  `(ih ψ' …).1`; `rw [Satisfies.imp_iff]`.
- **negPos** (`neg φ'`): output `F(φ')`; goal `Satisfies … (imp φ' bot)` →
  `rw [Satisfies.imp_iff]; intro; exact absurd … ((ih φ' …).2 …)`.

The F-direction is dual (`andNeg`/`orNeg`/`impNeg`/`negNeg`), already largely worked out in
WIP lines 721–1000 — port those leaves verbatim, but draw the IHs from the single coherent
`ih` instead of the nested-induction IHs.

---

## Deliverable 5 — Mathlib / CSLib lemma candidates

All verified to exist (local grep / file reads) unless marked "(add)":

| Symbol | Source | Use |
|---|---|---|
| `Nat.strongRecOn` / `Nat.rec` | Batteries `Data/Nat/Lemmas.lean` / core | the strong-induction driver (or fuel `induction n`) |
| `Formula.complexity` | `Temporal/Syntax/Formula.lean:204` | well-founded measure; generic-imp arithmetic |
| `Formula.one_le_complexity` *(add — trivial)* | — | `complexity φ ≥ 1` for the `n = 0` vacuity; prove by `cases`/`simp [complexity]` or `omega` over the match |
| `Satisfies.imp_iff` `@[simp]` | `Temporal/Semantics/Satisfies.lean:85` | unfold `Satisfies (imp ..)` |
| `Satisfies.bot_false` | `Satisfies.lean:73` | unfold `Satisfies bot` (drives `and`/`or`/`neg` unfolding with `imp_iff`) |
| `Satisfies.atom_iff` `@[simp]` | `Satisfies.lean:79` | atom case bridge (already used in `extractModel_atom_sat_iff`) |
| `Satisfies.neg_iff` | `Satisfies.lean:112` | optional convenience for `negPos`/`negNeg` |
| `tempAndOf?_and`, `tempOrOf?_or`, `tempNegOf?_neg`, `tempImpOf?_neg`, `tempImpOf?_or`, `tempImpOf?_imp` | `Defs.lean:113–195` (`@[simp]`) | reduce `tryAllPropRules` at each rule leaf |
| `RuleResult.isApplicable` | `Foundations/Logic/Tableau/RuleResult.lean` | needed in the `tryAllPropRules` simp set |
| `List.any_eq_true`, `List.mem_cons`, `List.mem_cons_self` | Mathlib/core | branch membership plumbing (as in template & WIP) |
| `extractModel_atomPos_sat`, `extractModel_atom_neg_notSat`, `extractModel_bot_false`, `openBranch_noBotPos` | `Completeness.lean` | the reused base cases |
| `any_pos_mem`, `any_neg_mem`, `mem_to_any_pos`, `mem_to_any_neg` | WIP lines 242–276 *(port into the file)* | `any ↔ ∈` bridges |
| `IsPropositional` *(add)* | WIP lines 230–237 | the propositional-fragment predicate (and its inversion for deep parts) |

No new Mathlib dependency, no new axiom, no FMP, no `ordConstraints` interaction is
required. The proof is self-contained within the propositional fragment.

---

## Reuse-first / zero-debt notes

- **Reuse check:** the entire base-case layer (`extractModel_*`, `openBranch_noBotPos`) and
  the prop-rule infrastructure (`tryAllPropRules`, `applyPropRule`, `tempXOf?` + their
  `@[simp]` lemmas) already exist and are reused as-is. The only *new* declarations are
  `IsPropositional` (mechanical), `Formula.one_le_complexity` (one-line), the private
  `_aux`, the four bridge lemmas (ported from WIP), and the public lemma.
- **Zero-debt:** the recommended path is sorry-free and axiom-free. The strong-induction
  measure is the structural fix that eliminates the WIP's single `sorry`. No Option-B
  deferral, no placeholder.
- **Notation/lint:** new lemmas need docstrings (docBlame); `IsPropositional` is `Prop`
  so it is fine as `inductive`; keep declarations inside `namespace
  Cslib.Logic.Temporal.Tableau`; avoid underscores in new identifier *components*
  (`temporalTruthLemma_propositional` follows the existing `extractModel_*` snake style
  already used throughout this file, so it is consistent with the module).

## Risk / open questions for the planner

1. **Exact `complexity` arithmetic per leaf.** Because `Formula.complexity` has several
   `untl`/`snce` special cases before the generic `imp`, the implementer must confirm (via
   `lean_goal`/`omega`) that each propositional leaf reduces to the generic-imp branch.
   For purely propositional φ this always holds, but the `omega` discharge needs the
   `complexity` equation `simp`'d open at the matched shape. Low risk, but the single most
   likely friction point.
2. **`cases hφ'` depth for `and`/`or`.** Extracting `IsPropositional a` / `IsPropositional
   b` for the deep parts requires one or two `cases hφ'`/`cases hψ'` inversions. These are
   inversions (`cases`), not inductions — keep them shallow.
3. **`hrule` let-binding.** `temporalHintikkaSet`'s second component is stated with a
   `let (result, _) := temporalApplyOne sf b ord`. The WIP unfolds it with
   `simp only [temporalApplyOne] at hout` (WIP line 324) — replicate that to expose the
   `tryAllPropRules` result.
```
