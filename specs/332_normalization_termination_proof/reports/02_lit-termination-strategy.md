# Research Report 02: Literature-Grounded Termination Strategy (Task 332)

- **Task**: 332 — normalization_termination_proof
- **Date**: 2026-06-24
- **Session**: sess_1782335142_17b247_332-research
- **Mode**: Literature-grounded research (`--lit`), research-only
- **Focus**: The remaining termination gap in `normalize_isStronglyNormal`
  (`Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`), and how the standard
  proof-theory literature defeats the `subsOne` height-increase obstacle.
- **Builds on**: `reports/01_termination-research.md` (does NOT duplicate it).

> **Coordination note.** The file is being actively edited by an implementation agent and has
> grown to 1755 lines with the Dershowitz–Manna measure (`maximalFormulas`, `commutingSum`,
> `normMeasure`, `normMeasure_wf`, `reduceRoot_decreases_normMeasure`) already scaffolded.
> The remaining sorries are at lines 1702, 1715–1723 (six β/commuting cases of the strict-decrease
> lemma) and **line 1739** (`normalize_isStronglyNormal` — the fuel/measure bridge). This report
> targets the *strategic* gap at line 1739, which report 01 left as the "Key Open Question."
> The implementation agent holds `.return-meta.json`; this agent's metadata is in
> `.return-meta-research.json`. **No edits were made to Normalization.lean.**

---

## 0. What Report 01 Established, and the One Question It Left Open

Report 01 correctly identified:
- The naive `redexWeight` measure is **not** monotone under β-reduction (substitution can
  duplicate the argument and create several new redexes).
- The correct primary measure is the **Dershowitz–Manna multiset ordering** on maximal-formula
  complexities, with a secondary commuting-conversion measure.
- Mathlib's `Multiset.IsDershowitzMannaLT` + `wellFounded_isDershowitzMannaLT` supply the
  infrastructure.

The implementation agent has since **built exactly this**: `normMeasure = (maximalFormulas,
commutingSum)` under `Prod.Lex IsDershowitzMannaLT (· < ·)`, proven well-founded by
`normMeasure_wf` (lines 1670–1679). The per-step decrease lemma `reduceRoot_decreases_normMeasure`
(line 1693) is scaffolded with the two conjunction-β cases already closed.

**The one question report 01 explicitly left open** (its §3.2 and §10):

> *"Is `2^height` actually sufficient? … If `2^height` is genuinely insufficient, this approach
> fails."*

This report answers that question from the literature and shows that **the question is the wrong
question** — the standard SN proofs never bound the number of reduction steps by a height
expression at all. Below I give (1) how the literature structures the measure so substitution's
height-increase is irrelevant, (2) the precise induction principle, (3) the mapping to the Lean
structures, and (4) a recommended skeleton for line 1739 that **does not require proving any
`2^height` fuel bound**.

---

## 1. How the Literature Defeats the Substitution-Height-Increase Obstacle

There are **two distinct standard techniques**, and the CSLib code is currently committed to the
first one. Both are documented in the available literature. The crucial common feature: **neither
measures derivation height**, so substitution increasing height *cannot* break either argument.

### 1.1 Technique A — Prawitz's lexicographic (cutrank, m) with the rightmost-redex strategy

**Source: Troelstra & Schwichtenberg, *Basic Proof Theory* (2nd ed.), Thm 6.1.8**
(`specs/literature/sources/troelstra_schwichtenberg_2000/section07_ch6-11-advanced-topics.md`,
lines 200–234). This is the direct descendant of Prawitz 1965, Ch. III–IV.

The measure is the lexicographic pair
```
(n, m)  where  n = cutrank(D)  = max complexity over all maximal segments (cuts) of D
               m = the sum of the LENGTHS of all critical cuts (maximal-degree cut segments)
```
ordered as `(<, <)` lexicographically (T&S line 204: *"a main induction on the cutrank n … with a
subinduction on m, the sum of lengths of all critical cuts"*).

**The decisive passage on substitution (T&S lines 214–225):** the strategy converts the
**rightmost top-critical-cut** (t.c.c.) — *"the rightmost redex of maximal degree not containing
another redex of maximal degree"* (line 228). For an implication conversion of the rightmost
t.c.c., one substitutes the minor-premise derivation `D''` at each free occurrence of `[A]`:

> *"Then the repeated substitution of D'' at each f.o. of [A] cannot increase the value of m,
> since D does not contain a t.c.c. cut in D'' above the minor premise A of →E (such a cut would
> have to occur to the right of A→B, contrary to our assumption)."* (T&S lines 222–224)

**This is the literature's exact answer to the CSLib obstacle.** Substitution *can* increase
height, and it *can* even create new redexes — but because we always reduce the **rightmost**
maximal-degree redex, the substituted-in derivation `D''` contains **no critical (maximal-degree)
cut**. Hence:
- the eliminated cut of degree `n` is removed (so either `n` drops, when it was the last one, or)
- `m` strictly decreases, and the substitution adds **only cuts of degree `< n`** — these do not
  count toward `m` (which counts only maximal-degree critical cuts).

So **height is never part of the measure**, and the substituted copies contribute only to a
*strictly lower stratum* `n' < n`, exactly the Dershowitz–Manna shape report 01 identified.

### 1.2 Technique B — Tait/Girard computability (strong-normalization, height-free)

**Source: T&S §6.8, "Strong normalization for →Nm and λ→"** (same file, lines 1501–1610). This is
the robust method that proves *every* reduction sequence terminates (not just one strategy), and
it **never mentions height or a step bound at all**.

Define the computability predicate by recursion on formula complexity (T&S 6.8.2, lines 1520–1525):
```
Comp_X(t)   := SN(t)                              (X atomic)
Comp_{A→B}(t) := ∀ s. Comp_A(s) → Comp_B(t s)
```
with the three closure properties C1–C3 (6.8.3, lines 1527–1561):
```
C1  Comp_A(t) → SN(t)
C2  Comp_A(t) ∧ t ⟶ t' → Comp_A(t')
C3  t non-introduced ∧ (∀ t'. t ⟶ t' → Comp_A(t')) → Comp_A(t)
```
The substitution lemma (6.8.4, lines 1563–1579) and the main theorem (6.8.5, lines 1581–1601)
prove **strong computability under substitution**: if every `s_i ∈ Comp_{A_i}` then
`t[x̄/s̄] ∈ Comp_B`. The "substitution increases height" problem **dissolves**, because the
inductive invariant is `Comp`, a semantic predicate, not any size/height number.

**This is the canonical, fully-robust reference for the obstacle.** It is what one cites if the
multiset argument runs into trouble. (T&S 6.8.6, line 1604: *"All deductions of →Nm are strongly
normalizable."*)

### 1.3 Cut-elimination analogue (confirms the pattern is universal)

**Source: Negri & von Plato, *Structural Proof Theory* (2001), §2.4**
(`specs/literature/sources/negri_von_plato_2001/section03_ch2-intuitionistic-cut-elimination.md`,
lines 439–457). The measure is `(weight of cut formula, cut-height = sum of premise heights)`,
lexicographic. They state the obstacle **explicitly and identically to ours**:

> *"Cut-height is not monotone as we go down in a derivation … the permutation of a cut upward
> does not always reduce cut-height but can increase it."* (NvP lines 451–457)

and the resolution:

> *"We give transformations that always reduce the weight of cut formula or cut-height … in the
> [principal] case, cut is reduced to formulas of lesser weight. This process terminates since
> atoms can never be principal in logical rules."* (NvP lines 446–450)

i.e. **height-increase is tolerated because it lives in the *inner* (secondary) lexicographic
component; the *outer* component (formula weight / cutrank) strictly drops whenever the inner one
can rise.** This is precisely `Prod.Lex.left` in the Lean encoding.

**Gentzen 1935** (`gentzen_1935/sec03_lj-lk-hauptsatz.md`) is the original Hauptsatz with the
same double induction on (grade of cut formula, rank). BibKey `gentzen_1935`.

---

## 2. Precise Induction Principle and Measure (the answer to "what sidesteps subsOne")

### 2.1 The measure (matches the Lean `normMeasure` exactly)

```
μ(d) := (maximalFormulas d, commutingSum d)  ∈  Multiset ℕ × ℕ
ordered by  Prod.Lex  Multiset.IsDershowitzMannaLT  (· < ·)
```
- **Primary** `maximalFormulas d : Multiset ℕ` = multiset of `complexity` of every cut formula
  (maximal-segment / β-redex) in `d`. ← T&S `cr`/critical-cut data (Thm 6.1.8), Prawitz Ch. III.
- **Secondary** `commutingSum d : ℕ` = Σ `nodeCount` over commuting-conversion sites
  (`E-rule` applied to an `orE`). ← T&S permutation-conversion termination (T&S 6.1.5, lines
  130–148); Prawitz Ch. IV "permutative reductions."

**Why each reduction step strictly decreases μ (the lexicographic tuple):**

| Reduction (Lean `reduceRoot` case) | Literature conversion | Effect on `maximalFormulas` | Effect on `commutingSum` | Decrease via |
|---|---|---|---|---|
| `impE (impI _ D) E → D.subsOne E` | →-detour (T&S 6.1.4) | removes one elt `= (A→B).complexity`; adds only elts `< (A→B).complexity` (subformula of cut formula) | may rise (irrelevant) | `Prod.Lex.left` (Dershowitz–Manna) |
| `andEᵢ (andI ..)` | ∧-detour | removes one elt; adds nothing new in primary | unchanged or lower | `Prod.Lex.left` (already proven, lines 1704–1713) |
| `orE (orIᵢ _ D) Dᵢ → Dᵢ.subsOne D` | ∨-detour | removes one elt; adds only `< cut complexity` | may rise (irrelevant) | `Prod.Lex.left` |
| `andEᵢ (orE ..)`, `impE (orE ..) ..` | permutation conversion (T&S 6.1.5) | **unchanged** (no intro at eliminated connective in branches — guaranteed by `reduceRootSubSN`) | strictly drops (the `orE` is no longer directly below an E-rule; the removed site contributed `≥ nodeCount(D) ≥ 1`) | `Prod.Lex.right` |

**The subsOne-height-increase obstacle never appears**, because:
1. In the β cases the primary `maximalFormulas` strictly drops in the **Dershowitz–Manna** order;
   `Prod.Lex.left` ignores the secondary component entirely, so even if `commutingSum` (or height,
   or node count) *increases*, the tuple still strictly decreases. This is the Lean mirror of
   NvP's "outer weight drops, inner cut-height may rise" (NvP 446–457) and Prawitz's
   "substitution cannot increase `m`" (T&S 222–224).
2. In the commuting cases `maximalFormulas` is *preserved* (side condition `reduceRootSubSN`
   ensures the pushed-into branches are not introductions at the eliminated connective), so the
   secondary `commutingSum` is what must drop — and it does, by `nodeCount(D) ≥ 1`.

### 2.2 The induction principle (height-free)

**Well-founded induction on `μ`**, *not* fuel induction. Concretely:

```
WellFounded.induction normMeasure_wf
```
i.e. prove `∀ d, P d` from `∀ d, (∀ d'. μ(d') < μ(d) → P d') → P d`. With
`P d := "normalizing d yields a strongly-normal derivation"`, the single step is:
either `d.reduceRoot = none` *and subterms are sn* (base: `d` is already sn), or
`d.reduceRoot = some d'` with `μ(d') < μ(d)` (by `reduceRoot_decreases_normMeasure`), so the IH
applies to `d'`. **No `2^height` bound is ever needed.**

This is the literal Lean analogue of T&S's "main induction on `n`, subinduction on `m`"
(line 204) — `WellFounded.prod_lex` *is* that nested induction, packaged as one well-founded
relation (already assembled in `normMeasure_wf`, lines 1674–1679).

---

## 3. Concrete Mapping: Literature Measure → Existing Lean Structures

| Literature concept | BibKey / source locus | Lean structure (Normalization.lean) | Status |
|---|---|---|---|
| cutrank / critical-cut multiset | `troelstra_schwichtenberg_2000` Thm 6.1.8 (lines 200–229); Prawitz Ch. III | `maximalFormulas : T.Derivation G A → Multiset Nat` (line 1087) | built |
| cut-formula complexity `\|A\|` | T&S 6.1.2 (line 60: "cutrank cr(σ) … is \|A\|") | `conclusionComplexity` / `Proposition.complexity` (lines 942, 148) | built |
| Dershowitz–Manna < on the cut multiset | report 01 §4.1; standard DM termination (Dershowitz–Manna 1979) | `Multiset.IsDershowitzMannaLT` + helper lemmas (lines 1643–1665) | built |
| sum of lengths of critical cuts `m` / permutative measure | T&S 6.1.8 (line 205), 6.1.5 (perm conversions) | `commutingSum : T.Derivation G A → Nat` (line 1531) | built |
| lexicographic `(n, m)` | T&S line 204; NvP §2.4 (lines 439–441); Gentzen Hauptsatz | `normMeasure` + `Prod.Lex … (· < ·)` (line 1670) | built |
| well-founded nested induction | T&S "main + sub induction" | `normMeasure_wf` via `WellFounded.prod_lex` (line 1674) | built |
| detour / β conversions | T&S 6.1.4 (lines 88–129) | `reduceRoot` β cases (lines 368–372) | built |
| permutation conversions | T&S 6.1.5 (lines 130–148) | `reduceRoot` commuting cases (lines 373–382) | built |
| substitution does not add maximal-degree cuts | T&S 6.1.8 (lines 222–224); subformula property of cut formula | `subsOne_new_redex_complexity_lt` (line 1510): new redex `k ∈ E.maximalFormulas ∨ k = A.complexity` | built (helper); **used by sorries 1702/1715/1717** |
| "substituted-in deriv has no critical cut" side condition (rightmost-t.c.c.) | T&S 6.1.8 (lines 209–224) | `reduceRootSubSN` (line 1626): the consumed subterms are `isStronglyNormal` | built |
| per-step strict decrease | T&S 6.1.8 entire proof | `reduceRoot_decreases_normMeasure` (line 1693) | **6 sorries (1702, 1715–1723)** |
| termination of the normalizer | T&S 6.1.8 conclusion / 6.1.10 (line 252) | `normalize_isStronglyNormal` (line 1733) | **1 sorry (1739)** — the strategic gap |

**Key correspondence for the obstacle.** `subsOne_new_redex_complexity_lt` (line 1510) is the
Lean transcription of the cut-formula-subformula fact behind T&S 222–224: any maximal formula
introduced by `subsOne E` is either already in `E.maximalFormulas` (empty under the
`reduceRootSubSN` invariant, since `E.isStronglyNormal`) or equals `A.complexity`, the complexity
of the *substituted hypothesis* `A`, which in every β case is a **proper subformula** of the
eliminated cut formula. Cite `troelstra_schwichtenberg_2000` §6.1.8 and Prawitz 1965 Ch. III for
this.

---

## 4. Recommended Proof Skeleton

There are two layers to finish: (4.1) the six remaining strict-decrease cases, and (4.2) the
strategic bridge at line 1739. **The literature dictates that (4.2) should be done by
well-founded induction on `normMeasure`, abandoning any attempt to bound `2^height` fuel.**

### 4.1 Finishing the six strict-decrease cases (`reduceRoot_decreases_normMeasure`)

These follow the two-already-proven conjunction cases (lines 1704–1713). For each:

**β cases 1702 (`impE (impI _ D) E`), 1715/1717 (`orE (orIᵢ _ D) Dᵢ`):** apply `Prod.Lex.left`,
then reduce `maximalFormulas (D.subsOne E)` against `maximalFormulas` of the redex. Use
`isDershowitzMannaLT_remove_add_lt` (line 1662): the removed element is the cut-formula complexity
`c`, and every element of the added multiset `Y` (the new redexes from `subsOne`) is `< c` by
`subsOne_new_redex_complexity_lt` + `reduceRootSubSN` (which gives `E.maximalFormulas = ∅`, so
every new `k = A.complexity < c`). Sketch:

```lean
· -- impE (impI _ D) E  →  D.subsOne E
  rw [Option.some.injEq] at hd'; subst hd'
  refine Prod.Lex.left _ _ ?_
  -- maximalFormulas (D.subsOne E) = X + Y, maximalFormulas (impE (impI _ D) E) = X + {c}
  -- with c = (A ⇒ B).complexity and ∀ y ∈ Y, y < c
  obtain ⟨hsn_D, hsn_E⟩ := h_subsSN          -- from reduceRootSubSN
  have hEempty : E.maximalFormulas = ∅ := maximalFormulas_sn_eq_zero E hsn_E  -- Phase 2b helper
  apply Multiset.isDershowitzMannaLT_remove_add_lt
  intro y hy
  -- y is a NEW redex of D.subsOne E; by subsOne_new_redex_complexity_lt,
  -- y ∈ E.maximalFormulas (impossible, hEempty) ∨ y = A.complexity < c
  …
```
The arithmetic `A.complexity < (A ⇒ B).complexity` (and the ∨ analogues) is `Proposition.complexity`
unfolding + `omega`. The set-algebra (`maximalFormulas (D.subsOne E) = X + Y`) is the multiset
bookkeeping connecting `subsOne_new_redex_complexity_lt` to the `X + Y` / `X + {c}` shape; this is
the genuinely fiddly part and may need a small helper:
`maximalFormulas_subsOne_eq : (D.subsOne E).maximalFormulas = D.maximalFormulas + (newRedexes …)`.

**Commuting cases 1719/1721/1723 (`andEᵢ (orE ..)`, `impE (orE ..) ..`):** apply `Prod.Lex.right`,
which requires (a) `maximalFormulas` equal on both sides and (b) `commutingSum` strictly smaller.
(a) holds because pushing the elimination into `orE` branches does not create an introduction at
the eliminated connective — encoded by `reduceRootSubSN`'s `(andE1 _ DA).isStronglyNormal` etc.
(b) is `nodeCount(D) ≥ 1` arithmetic on `commutingSum`. Sketch:

```lean
· -- andE1 G (orE _ D DA DB)  →  orE G D (andE1 DA) (andE1 DB)
  rw [Option.some.injEq] at hd'; subst hd'
  refine Prod.Lex.right _ ?_     -- needs the maximalFormulas-equal side via Prod.Lex on equal fst
  -- Prefer: prove fst equal, then Nat.lt on commutingSum
  …
```
Note: `Prod.Lex.right` requires the **first components to be definitionally/propositionally
equal**. If `maximalFormulas` is only *provably* (not definitionally) equal across the conversion,
rewrite by that equality first, then `Prod.Lex.right`. A helper
`maximalFormulas_commuting_invariant` may be warranted.

### 4.2 The strategic bridge (line 1739) — RECOMMENDED REPLACEMENT

`normalize_isStronglyNormal` currently does `apply redexWeight_zero_sn` then `sorry`s the goal
`d.normalize.redexWeight = 0`. The literature says: **do not try to prove `2^height` fuel
suffices.** Instead prove a height-free "reaches strong normal form" theorem by WF induction on
`normMeasure`, then bridge to the existing `normalize` either by (i) a fuel-monotonicity argument
or (ii) by re-defining `normalize` via `WellFounded.fix`.

**Recommended sub-lemmas (Approach A from report 01, now grounded):**

```lean
/-- A derivation whose root is not a redex and whose immediate subterms are strongly normal
    is itself strongly normal. (Mirror of T&S 6.1.7: "normal" ⇔ no major premise is an
    introduction / no E-over-orE.) -/
private theorem reduceRoot_none_subSN_isStronglyNormal
    (d : T.Derivation G A) (hroot : d.reduceRoot = none)
    (hsub : <subterms strongly normal>) : d.isStronglyNormal = true

/-- Normalizing subterms preserves nothing larger in normMeasure and makes reduceRootSubSN hold.
    (This packages the "normalize subterms first, then the root" structure of normalizeAux.) -/
private theorem normSub_reduceRootSubSN … 

/-- MAIN height-free termination, by well-founded induction on normMeasure. -/
private theorem exists_stronglyNormal_form (d : T.Derivation G A) :
    ∃ d', d'.isStronglyNormal = true := by
  induction d using WellFounded.induction normMeasure_wf with  -- or `normMeasure_wf.induction`
  | _ d ih =>
    -- 1. structurally normalize the subterms (they have ≤ normMeasure, recurse structurally)
    -- 2. let d₀ be the result; if d₀.reduceRoot = none, d₀ is sn (reduceRoot_none_subSN…)
    -- 3. else d₀.reduceRoot = some d', with reduceRootSubSN d₀ (subterms now sn),
    --    so normMeasure d' < normMeasure d₀ ≤ normMeasure d  →  apply ih d'
    …
```

**Then bridge to `normalize`.** Two options, in order of preference:

- **Bridge option 1 (cleanest, but touches the definition):** change `normalize` (line 404–405)
  from `d.normalizeAux (2 ^ d.height)` to a `WellFounded.fix normMeasure_wf` definition that *is*
  `exists_stronglyNormal_form` made computational, and make `normalize_isStronglyNormal` immediate.
  Downstream `subformula_property` (line 1748) only uses `normalize_isStronglyNormal`, so the type
  is unchanged. **Risk: Low** (report 01 §6.2 confirms downstream depends only on the SN property,
  not the fuel definition). This is the recommended route.

- **Bridge option 2 (keep `normalizeAux`, prove fuel-monotonicity):** prove
  `normalizeAux_eventually_fixes : ∃ N, ∀ k ≥ N, (d.normalizeAux k).isStronglyNormal` by WF
  induction on `normMeasure` (mirroring `exists_stronglyNormal_form`), plus a monotonicity lemma
  `normalizeAux n d sn → normalizeAux (n+1) d = normalizeAux n d` (essentially
  `normalizeAux_fixpoint`, line 924, already proven). **Then** still need
  `N ≤ 2^d.height` — which report 01 §3.2 argues is **likely false**. So option 2 only works if
  the `normalize` definition's fuel is *also* changed to a provably-sufficient bound (e.g.
  `normalizeAux (someBigEnoughFuel d)` where `someBigEnoughFuel` is read off the WF recursion).
  **Risk: Medium** — but note that **even here the literature does not justify `2^height`**; the
  only literature-sanctioned bounds are hyper-exponential (T&S 6.10 / 6.5 "rate of growth under
  normalization," lines 5–14 of section07 preface), confirming report 01's hyper-exponential
  worry.

**Strong recommendation:** Bridge option 1. The literature (T&S 6.8, 6.1.8) proves termination by
induction on a *semantic/multiset* measure, **never** by exhibiting a closed-form step bound; the
Lean proof should mirror this with `WellFounded.fix`/`WellFounded.induction` on the
already-proven-well-founded `normMeasure`, and **the `2^height` fuel expression should be retired
as the termination witness.** If the team wants to keep the computational `normalizeAux` for
extraction, redefine it (or wrap it) via the WF recursion so that the fuel parameter disappears
from the correctness obligation.

### 4.3 What NOT to do (per zero-debt + literature-fidelity)

- Do **not** attempt to prove `2^d.height` fuel suffices — report 01 §3.2 and the T&S growth-rate
  results (section07 preface, lines 11–14) indicate the bound is hyper-exponential. Pursuing it
  risks an unprovable obligation and a stalled task.
- Do **not** introduce an axiom to bridge line 1739. The WF-induction route is fully constructive
  and uses only already-proven `normMeasure_wf`.
- Do **not** weaken `redexWeight_zero_sn` or `normMeasure_wf`; they are correct and reusable.

---

## 5. Reuse Check (CSLib reuse-first)

- **`Cslib.Foundations.*`**: No general normalization/SN abstraction exists; this is
  PropositionalND-specific. Nothing to reuse there (consistent with report 01 §7.1).
- **Mathlib (already imported, line 10 `Mathlib.Data.Multiset.DershowitzManna`)**:
  `Multiset.IsDershowitzMannaLT`, `Multiset.wellFounded_isDershowitzMannaLT`,
  `WellFounded.prod_lex`, `Prod.Lex`, `WellFounded.fix`, `WellFounded.induction` (verified present:
  `WellFounded.induction_bot`/`'` in `Mathlib/Order/WellFounded.lean`; core `WellFounded.fix`/
  `.induction` in `Init.WF`). All needed pieces exist; **no new imports required.**
- **In-file**: `normMeasure_wf` (1674), `reduceRoot_decreases_normMeasure` (1693, once its sorries
  close), `subsOne_new_redex_complexity_lt` (1510), `reduceRootSubSN` (1626),
  `maximalFormulas_sn_eq_zero` (added in commit 5a31a3f7, "task 332 phase 2b"),
  `normalizeAux_fixpoint` (924), `redexWeight_zero_sn` (1018) are all directly reusable.

---

## 6. Tactic Survey (advisory)

| Goal shape | Recommended tactic(s) | Notes |
|---|---|---|
| `Prod.Lex … (μ d') (μ d)` β-case | `refine Prod.Lex.left _ _ ?_` then DM helper | already the pattern at 1705 |
| `Prod.Lex … ` commuting-case | rewrite fst equality, then `Prod.Lex.right _ ?_` | needs `maximalFormulas` invariance lemma |
| `IsDershowitzMannaLT (X+Y) (X+{c})` | `Multiset.isDershowitzMannaLT_remove_add_lt` (1662) | feed `∀ y ∈ Y, y < c` |
| `A.complexity < (A ⇒ B).complexity` | `simp [Proposition.complexity]; omega` | proper-subformula arithmetic |
| `commutingSum` strict drop | `simp [commutingSum, nodeCount]; omega` | `nodeCount D ≥ 1` |
| main termination | `induction d using WellFounded.induction normMeasure_wf` | the height-free bridge |
| sn from `reduceRoot = none` + sn subterms | `cases d <;> simp_all [isStronglyNormal, reduceRoot]` | mirror of `redexWeight_zero_sn` style |

`exact?`/`apply?`/`lean_state_search` are useful inside the DM multiset bookkeeping of §4.1, where
the `X + Y = …` decomposition is the main friction point.

---

## 7. BibKey Summary (citation grounding for downstream agents)

| BibKey / source file | Used for |
|---|---|
| `troelstra_schwichtenberg_2000` — §6.1.2–6.1.8 (`…/section07…`, lines 48–234) | cutrank, critical-cut multiset, lexicographic `(n,m)`, **substitution-cannot-increase-`m`** (222–224) |
| `troelstra_schwichtenberg_2000` — §6.8 (lines 1501–1610) | Tait/Girard **computability** SN proof (height-free fallback) |
| `troelstra_schwichtenberg_2000` — §6.1.5, 6.1.10 (130–148, 252) | permutation conversions; full SN statement |
| `negri_von_plato_2001` — §2.4 (`…/section03…`, lines 439–457) | cut-formula-weight × cut-height lexicographic; **explicit non-monotone-height + resolution** |
| `gentzen_1935` — §3 Hauptsatz (`…/sec03…`) | original double induction (grade, rank) |
| Prawitz 1965, Ch. III–IV | (cited in-file at lines 1692, 1733) primary source for the ND normalization measure; corresponds to T&S 6.1.8 |
| Dershowitz–Manna 1979 | multiset well-ordering (via Mathlib `IsDershowitzMannaLT`) |

> **Citation caveat for `/cite`:** Prawitz 1965 and Dershowitz–Manna 1979 are referenced
> indirectly (Prawitz via in-file comments; DM via Mathlib). They are **not** present as converted
> sources under `specs/literature/sources/`. The *substantive* claims (measure structure,
> substitution argument) are all directly grounded in `troelstra_schwichtenberg_2000` and
> `negri_von_plato_2001`, which ARE present. Downstream agents should cite the T&S/NvP loci above
> rather than Prawitz/DM directly unless those sources are added.

---

## 8. Bottom Line for the Planner / Implementer

1. **The obstacle is solved in the literature by a lexicographic measure whose primary component
   strictly drops in the Dershowitz–Manna order on cut-formula complexities; height never enters
   the measure, so `subsOne` raising height is harmless** (T&S 6.1.8 lines 204–224; NvP §2.4
   lines 446–457). The CSLib code already encodes exactly this (`normMeasure`, `normMeasure_wf`).
2. **The precise induction is `WellFounded.induction normMeasure_wf`**, the Lean form of T&S's
   "main induction on `n`, subinduction on `m`." Each `reduceRoot` step strictly decreases
   `normMeasure` (β → `Prod.Lex.left`; commuting → `Prod.Lex.right`).
3. **Finish the 6 strict-decrease sorries** (§4.1) using `isDershowitzMannaLT_remove_add_lt` +
   `subsOne_new_redex_complexity_lt` + `reduceRootSubSN`, with a likely helper
   `maximalFormulas_subsOne_eq` for the multiset bookkeeping.
4. **Replace the line-1739 `sorry` with a height-free WF-induction proof** (`exists_stronglyNormal_form`),
   then **bridge by redefining `normalize` via `WellFounded.fix`** (Bridge option 1) so the
   `2^height` fuel is no longer the termination witness. Do **not** try to prove `2^height`
   suffices — the literature's growth bounds are hyper-exponential, confirming report 01 §3.2.
