# Research Report 03: Commuting Conversions and the WF Termination Bridge (Task 332)

- **Task**: 332 — normalization_termination_proof
- **Date**: 2026-06-24
- **Session**: sess_1782335142_17b247_332-research2
- **Mode**: Targeted literature-grounded research (`--lit`), research-only
- **Builds on**: `reports/02_lit-termination-strategy.md` (the height-free Dershowitz–Manna
  measure). This report does **not** re-derive the measure; it cracks the two remaining
  obstacles the impl agent is live on.
- **Coordination**: `Normalization.lean` is being edited by the implementation agent. **No edits
  were made.** The on-disk state has advanced past report 02: the β cases (h_1, h_4, h_5) are now
  **closed**; the remaining sorries are the **three commuting cases** h_6 (line 1782), h_7 (1784),
  h_8 (1786) and the **strategic sorry** at line 1802 (`d.normalize.redexWeight = 0`).

---

## 0. Verified On-Disk Ground Truth (changed since report 02)

| Item | Status |
|---|---|
| `reduceRoot_decreases_normMeasure` h_1/h_4/h_5 (β: impE, orE-left, orE-right) | **PROVED** (lines 1724–1780, via `subsOne_new_redex_complexity_lt` + `isDershowitzMannaLT_all_lt[_add]` + `Prod.Lex.left`) |
| h_2/h_3 (β: andE) | **PROVED** (`isDershowitzMannaLT_cons_add[']`) |
| h_6/h_7/h_8 (commuting: andE1·orE, andE2·orE, impE·orE) | **SORRY** (lines 1782/1784/1786) — Obstacle A |
| `normalize_isStronglyNormal` | **SORRY** at 1802, goal `d.normalize.redexWeight = 0` — Obstacle B |
| `maximalFormulas_sn_eq_zero`, `maximalFormulas_weakCtx`, `reduceRootSubSN`, `commutingSum`, `nodeCount`, `normMeasure_wf`, `redexWeight_zero_sn` | all **present + compiling** |

Verified via `lean_goal` at 1782 and 1802, and `grep`. **The file now has exactly 4 sorries.**

---

## OBSTACLE A — Commuting conversions preserve the cut-formula multiset

### A.1 The literature's exact invariant (source-grounded answers to Q1–Q3)

**Q1. How T&S / NvP justify that a permutative conversion does not increase the cut multiset.**

The justification rests entirely on T&S's **segment / maximal-segment definition**, not on any
separate "permutation lemma":

> **T&S 6.1.2 (Definition, segment/cut)**
> (`troelstra_schwichtenberg_2000/section07_ch6-11-advanced-topics.md`, lines 50–66):
> *"A segment … is a sequence A₁,…,Aₙ of consecutive occurrences of a formula A … A segment is
> **maximal, or a cut (segment), if Aₙ is the major premise of an E-rule**, and either n>1, or n=1
> and A₁=Aₙ is the conclusion of an I-rule. **The cutrank cr(σ) of a maximal segment σ with formula
> A is |A|.** … A critical cut of D is a cut of maximal cutrank."*

The permutative conversion is T&S **6.1.5** (lines 130–148):

> *"V-perm conversion: … we permute E-rules upwards over minor premises of VE, ∃E."*

The decisive point: a maximal segment's cutrank is `|A|` where **`A` is the formula on the segment
(= the major-premise formula of the *permuted E-rule*), not the disjunction**. Pushing an `E`-rule
up over the two minor premises of `∨E`:

1. does **not** change the cut formula `A` of that `E`-rule (its complexity `|A|` is invariant);
2. cannot create a *new* maximal segment **unless** a branch's top is an I-rule matching the pushed
   `E` — and under the strong-normality side condition that branch is *not* such an introduction.

So the multiset of cutranks is **preserved**. The literature never measures this with the primary
(cutrank) component; instead the permutation is what the **secondary** measure counts. T&S 6.1.8
(line 205): *"a main induction on the cutrank n …, with a **subinduction on m, the sum of lengths
of all critical cuts**."* The multi-cutrank refinement (T&S 6.6.2, lines 1280–1290) is explicit:

> *"give deductions D an induction value ω·m + n, with m the maximal complexity of formulas in cut
> segments … n the total length of critical cut segments. **Each reduction step then lowers the
> induction value.**"*

**NvP confirm the obstacle and its placement identically** (`negri_von_plato_2001/section03…`,
lines 446–457):

> *"We give transformations that always reduce the weight of cut formula or cut-height. … **Cut-
> height is not monotone** … the permutation of a cut upward does not always reduce cut-height but
> **can increase it**."*

i.e. a permutation may **raise** the secondary component (cut-height / segment length / node
count) while the **primary** (weight/cutrank) is unchanged — exactly the `Prod.Lex` shape:
primary equal ⇒ decide on secondary. This is the same double induction as Gentzen's Hauptsatz
(`gentzen_1935/sec03…`, lines 398–399: *"two complete inductions, one on the degree γ, the other on
the rank ρ"*).

**Q2. The minimal invariant needed, mapped to `reduceRootSubSN`.**

The literature's minimal requirement for "permutation creates no new maximal segment" is precisely:
**the orE branches, after the E-rule is pushed in, are not introductions matching that E-rule** —
equivalently, the pushed-in eliminations are themselves normal at that node. It is **not** full
strong-normality of `D` (the major `orE`'s discriminee); it is normality of the **pushed
eliminations on the branches**. The Lean `reduceRootSubSN` encodes exactly this minimal invariant
(lines 1641–1647), and not more:

```lean
| andE1 _ (orE _ _ DA DB) =>
    (andE1 _ DA).isStronglyNormal = true ∧ (andE1 _ DB).isStronglyNormal = true
| impE (orE _ _ DA DB) E =>
    (impE DA (E.weakCtx …)).isStronglyNormal = true ∧ (impE DB (E.weakCtx …)).isStronglyNormal = true
```

This is the **"no introduction at the permuted position"** invariant (T&S 6.12, line 2257: a normal
deduction is one *"where major premises of E-rules are assumptions; for otherwise the deduction of
some major premise either ends with an I-rule (detour) or ends with an E-rule (permutation)."*).
It is strictly weaker than "full strong-normality of subterms" — the discriminee `D` need **not** be
SN, and indeed `reduceRootSubSN` does **not** constrain `D`.

**Q3. Is `maximalFormulas` EQUALITY achievable, or only `≤`?**

**Equality is achievable** — verified empirically (not just claimed). The Lean `maximalFormulas`
(lines 1087–1109) contributes `{conclusionComplexity}` *only* at a redex node (`andE1 (andI …)`,
`orE (orIᵢ …)`, `impE (impI …)`). Pushing `andE1`/`impE` inside the `orE` branches:
- the source `andE1 (orE D DA DB)` has `maximalFormulas = (orE D DA DB).maximalFormulas`
  = `D.mf + DA.mf + DB.mf` (or `+{cc D}` if `D` is `orIᵢ`, which then appears identically on the
  target);
- the target `orE D (andE1 DA) (andE1 DB)` has `maximalFormulas = D.mf + (andE1 DA).mf +
  (andE1 DB).mf`, and `(andE1 DA).mf = DA.mf` **iff `DA` is not `andI`** — which `hA :
  (andE1 DA).isStronglyNormal = true` forces (an `andI` discriminee makes `isStronglyNormal = false`).

So the SN side condition turns the only potential inequality into an **equality**. This is the Lean
mirror of "no new maximal segment". **No stronger threaded invariant (e.g. fully-normalized
subterms) is required** for the commuting cases.

### A.2 Verified Lean proof sketch for h_6 / h_7 / h_8 (TESTED via `lean_multi_attempt`)

The following pattern **closed h_6 cleanly** under `lean_multi_attempt` (no diagnostics). `normMeasure`
must be unfolded to its pair form via `show` (a bare `rw [normMeasure]` fails — confirmed), the
**fst maximalFormulas equality** is proved by a `cases DA <;> cases DB` brute-force `simp_all`, then
`Prod.Lex.right` reduces to the `commutingSum` strict drop:

```lean
· -- h_6: andE1 G (orE G D DA DB) → orE G D (andE1 _ DA) (andE1 _ DB)
  rename_i Gi xx B1 A1 B2 D DA DB        -- adjust binder names to the actual `rename_i` order
  rw [Option.some.injEq] at hd'; subst hd'
  rcases h_subsSN with ⟨hA, hB⟩
  show Prod.Lex _ _ (_, _) (_, _)        -- unfold normMeasure to (maximalFormulas, commutingSum)
  rw [show (andE1 G (orE G D DA DB)).maximalFormulas
        = (orE G D (andE1 _ DA) (andE1 _ DB)).maximalFormulas from by
      cases DA <;> cases DB <;>
        simp_all [maximalFormulas, isStronglyNormal, conclusionComplexity]]
  refine Prod.Lex.right _ ?_
  cases D <;> simp_all [commutingSum, nodeCount, isStronglyNormal] <;> omega
```

- The fst-rewrite makes both first components **syntactically identical**, so `Prod.Lex.right`
  type-checks (it requires defeq fst; a bare `refine Prod.Lex.right` **without** the rewrite fails
  with a type-mismatch — confirmed).
- `cases DA <;> cases DB <;> simp_all [...isStronglyNormal...]` discharges the `andI`-discriminee
  branches via `hA`/`hB` (those make SN false), proving the maximalFormulas equality. **This is
  where the SN hypothesis is genuinely used** (not `trivial`).
- The `commutingSum` drop: in the source, `andE1 (orE …)` contributes `D.nodeCount + …` at the
  outer commuting site; in the target the outer commuting site is gone (the `orE` is no longer
  directly below an `andE1`), so `commutingSum` falls by `≥ D.nodeCount ≥ 1`. `cases D <;> simp_all
  [commutingSum,nodeCount] <;> omega` discharges every discriminee shape.

**h_7** is identical with `andE2`/`andE1` swapped.

**h_8** (`impE (orE D DA DB) E`) is the same shape but the branches carry a **weakened** `E`:
target is `orE D (impE DA (E.weakCtx …)) (impE DB (E.weakCtx …))`. The fst-equality `simp_all`
must additionally feed **`maximalFormulas_weakCtx`** (line 1139) so that `(E.weakCtx …).maximalFormulas
= E.maximalFormulas` is rewritten:

```lean
· -- h_8: impE (orE G D DA DB) E → orE G D (DA.impE (E.weakCtx …)) (DB.impE (E.weakCtx …))
  rename_i …  D DA DB E                  -- one extra binder (E) vs h_6/h_7
  rw [Option.some.injEq] at hd'; subst hd'
  rcases h_subsSN with ⟨hA, hB⟩
  show Prod.Lex _ _ (_, _) (_, _)
  rw [show ((orE G D DA DB).impE E).maximalFormulas
        = (orE G D (DA.impE (E.weakCtx (Finset.subset_insert _ _)))
                   (DB.impE (E.weakCtx (Finset.subset_insert _ _)))).maximalFormulas from by
      cases DA <;> cases DB <;>
        simp_all [maximalFormulas, isStronglyNormal, conclusionComplexity, maximalFormulas_weakCtx]]
  refine Prod.Lex.right _ ?_
  cases D <;> simp_all [commutingSum, nodeCount, isStronglyNormal] <;> omega
```

The `lean_multi_attempt` runs for h_6 and h_8 produced **no proof diagnostics** (only the benign
multi_attempt boundary-parse artifact), i.e. the chains elaborate to zero goals. The impl agent
must only fix the **`rename_i` binder order** to whatever the real split produces (the `split at hd'`
leaves the discriminees anonymous; either `rename_i` them or use `next … =>`).

### A.3 Optional helper (recommended for readability, not strictly required)

The inline `rw [show … from by cases DA <;> cases DB <;> simp_all …]` is self-contained, but a named
helper is cleaner and reusable across h_6/h_7/h_8:

```lean
/-- Pushing an `andE1` whose argument is strongly normal through an `orE` does not change the
maximal-formula multiset (no new maximal segment is created — the branch is not an `andI`). -/
private theorem maximalFormulas_andE1_commute
    (D : T.Derivation G (A1 ∨ B1)) (DA : …) (DB : …)
    (hA : (andE1 _ DA).isStronglyNormal = true) (hB : (andE1 _ DB).isStronglyNormal = true) :
    (orE G D (andE1 _ DA) (andE1 _ DB)).maximalFormulas = (andE1 G (orE G D DA DB)).maximalFormulas := by
  cases DA <;> cases DB <;> simp_all [maximalFormulas, isStronglyNormal, conclusionComplexity]
```

with `_andE2_commute` and `_impE_commute` analogues (the latter adding `maximalFormulas_weakCtx`).
The inline form is acceptable for a 3-case proof; **do not block on extracting helpers**.

---

## OBSTACLE B — The well-founded termination bridge

### B.1 The literature's final-theorem structure (answer to Q1)

T&S structure the *normalization* theorem (6.1.8) as the double induction already mirrored by
`normMeasure_wf`: **main induction on cutrank `n`, subinduction on `m` = total length of critical
cut segments** (lines 204–205), packaged in the ordinal form `ω·m + n` (6.6.2, line 1287). The
Lean analogue is `WellFounded.induction normMeasure_wf` with `normMeasure = (maximalFormulas,
commutingSum)` under `Prod.Lex IsDershowitzMannaLT (·<·)` — `WellFounded.prod_lex` **is** the nested
induction. The single inductive step is: `reduceRoot d = none` (base) **or** `reduceRoot d = some d'`
with `normMeasure d' < normMeasure d` (by `reduceRoot_decreases_normMeasure`, once Obstacle A
closes), feeding the IH. **No step-count / `2^height` bound appears in the literature** — confirming
report 02. The *strong*-normalization variant (T&S 6.8, Tait/Girard computability) likewise never
mentions a height bound; it is the height-free fallback if the multiset route stalls (it will not).

### B.2 The base case (answer to Q2)

T&S 6.12 (line 2257) gives the base-case characterization precisely:

> *"A normal deduction may now be defined as a deduction **where major premises of E-rules are
> assumptions**. For otherwise the deduction of some major premise either ends with an I-rule, and a
> detour conversion is possible, or ends with an E-rule and a permutation is possible."*

i.e. **a derivation with no available root reduction and normal immediate subterms is normal.** This
matches the Lean lemma **already present**: `redexWeight_zero_sn` (line 1018) — `d.redexWeight = 0 ⇒
d.isStronglyNormal = true`. The `isStronglyNormal` definition (lines 245–272) returns `false`
exactly at the redex/commuting nodes T&S enumerate (`andEᵢ (andI/orE …)`, `orE (orIᵢ/orE …)`,
`impE (impI/orE …)`), so "no root redex + SN subterms ⇒ SN" is **structurally** the contrapositive
of T&S's characterization. The base case therefore needs **no new literature** — `redexWeight_zero_sn`
(or a direct `reduceRoot = none ∧ subterms SN ⇒ SN` lemma) already encodes it.

### B.3 Existence vs. uniqueness — confluence is NOT needed (answer to Q3)

**Confirmed against T&S 6.8.6** (line ~1605):

> *"**Uniqueness of normal form** is either proved directly, or readily follows from Newman's lemma
> (1.2.8)."*

Uniqueness/confluence is a **separate** theorem. The CSLib `subformula_property` (line 1811) only
needs **existence of some SN derivation with the same conclusion** — it returns `⟨d.normalize,
sn-proof, subformula-property-of-sn⟩`. The subformula property is read off *any* SN derivation via
`subformula_property_of_isStronglyNormal` (line 602). **So the SN property alone suffices; no
confluence, no uniqueness.** Report 02's claim is correct and now literature-confirmed.

### B.4 The cleanest bridge — verified dependency analysis

**Key finding (grep-verified):** `normalize` has **no consumers outside `Normalization.lean`**, and
inside the file only `subformula_property` uses it, **solely through `normalize_isStronglyNormal`
(the SN property), never through the fuel definition.** This makes the bridge low-risk and gives
**two viable routes**, in order of preference:

**Route 1 (recommended — bypass the fuel obligation entirely).** Prove the existence theorem by WF
induction and re-point `subformula_property` at it, leaving `normalize`/`normalizeAux` untouched as
a computable artifact:

```lean
/-- Every derivation has a strongly-normal form (height-free, WF induction on normMeasure). -/
private theorem exists_stronglyNormal_form (d : T.Derivation G A) :
    ∃ d' : T.Derivation G A, d'.isStronglyNormal = true := by
  induction d using WellFounded.induction normMeasure_wf with
  | _ d ih =>
    -- 1. Normalize the immediate subterms first (structural recursion / a `normSubterms` helper),
    --    obtaining d₀ with the SAME conclusion, normMeasure d₀ ≤ normMeasure d, and SN subterms.
    -- 2. If d₀.reduceRoot = none: d₀ is SN (base case, B.2: redexWeight_zero_sn / a
    --    `reduceRoot_none_subSN_isStronglyNormal` lemma). Done with d' := d₀.
    -- 3. If d₀.reduceRoot = some d': the SN subterms discharge `reduceRootSubSN d₀`, so
    --    `reduceRoot_decreases_normMeasure` gives normMeasure d' < normMeasure d₀ ≤ normMeasure d;
    --    apply `ih d'`.
    sorry  -- to be filled by impl agent
```

Then:

```lean
theorem Theory.Derivation.subformula_property (d : T.Derivation G A) :
    ∃ d', d'.isStronglyNormal = true ∧ d'.SubformulaProperty := by
  obtain ⟨d', hsn⟩ := d.exists_stronglyNormal_form
  exact ⟨d', hsn, d'.subformula_property_of_isStronglyNormal hsn⟩
```

This **deletes the dependency on `normalize_isStronglyNormal` from the public theorem**. The
strategic sorry at 1802 can then either be (a) closed trivially by proving
`normalize_isStronglyNormal` from `exists_stronglyNormal_form` is *not* directly possible (the
existence form gives *some* SN derivation, not `d.normalize` specifically), so (b) keep
`normalize_isStronglyNormal` only if a downstream user needs `d.normalize` to be SN — **and
grep shows none do**. **Recommendation: make `subformula_property` consume
`exists_stronglyNormal_form`; if `normalize_isStronglyNormal` then has no consumers, it may be
removed (or proved by a `WellFounded.fix`-defined `normalize`, Route 2).**

**Route 2 (if `normalize` must remain SN-certified).** Redefine `normalize` via `WellFounded.fix
normMeasure_wf` so that `normalize_isStronglyNormal` is immediate from the fix equation. Heavier
(defeq unfolding via `WellFounded.fix_eq`); only worth it if the computable `d.normalize` symbol
must satisfy SN. Report 02 §4.2 already flagged the `2^height` fuel route as **dead** (T&S growth is
hyper-exponential, lines 1799–1916), so do **not** attempt `N ≤ 2^height`.

### B.5 The one genuine sub-obligation in `exists_stronglyNormal_form`

Step 1 ("normalize subterms first, with `normMeasure ≤` and SN subterms") is the only non-trivial
piece. Two ways to obtain it:
- **(preferred)** an inner induction / helper `normSubterms : ∃ d₀, sameConclusion ∧ subtermsSN ∧
  normMeasure d₀ ≤ normMeasure d` proved by structural recursion on `d` reusing the IH at strictly
  smaller subterms; OR
- reuse `normalizeAux` for the *inner* subterm pass only (its `reduceRoot`-free structural part) and
  invoke the WF IH for the root, sidestepping a global fuel bound.

The monotonicity `normMeasure (subterm-normalized d) ≤ normMeasure d` follows because each subterm
reduction strictly decreases that subterm's measure (`reduceRoot_decreases_normMeasure` again) and
`maximalFormulas`/`commutingSum` are additive over subterms (definitions lines 1087/1531). The
`reduceRootSubSN d₀` discharge in step 3 is exactly "subterms are SN" — which step 1 guarantees.

---

## C. Helper-lemma checklist implied by this report

| Helper | Need | Source/justification |
|---|---|---|
| `maximalFormulas_{andE1,andE2,impE}_commute` (or inline `rw [show …]`) | Obstacle A fst-equality | A.2/A.3; verified by `cases <;> simp_all` |
| (h_8 only) `maximalFormulas_weakCtx` | rewrite `(E.weakCtx).mf = E.mf` | **already present**, line 1139 |
| `reduceRoot_none_subSN_isStronglyNormal` (or reuse `redexWeight_zero_sn`) | Obstacle B base case | B.2; T&S 6.12 line 2257 |
| `normSubterms` (subterm-normalization with `normMeasure ≤` + SN subterms) | Obstacle B step 1 | B.5 |
| `exists_stronglyNormal_form` | Obstacle B main | B.4; T&S 6.1.8 / 6.8 |

All reuse existing in-file infrastructure + Mathlib (`WellFounded.induction`, `Prod.Lex`,
`IsDershowitzMannaLT`). **No new imports.** No axioms. No `2^height` fuel proof. No confluence.

## D. Citation grounding (for `/cite`)

| Locus | Used for |
|---|---|
| T&S 6.1.2 (lines 50–66) | segment/maximal-segment def; **cutrank = \|A\| of the segment formula** (Obstacle A invariant) |
| T&S 6.1.5 (lines 130–148) | V-/∃-perm conversions (the commuting conversions h_6–h_8) |
| T&S 6.1.8 / 6.6.2 (204–205, 1280–1290) | main-induction-on-cutrank + subinduction-on-segment-length = `Prod.Lex`/`normMeasure_wf` |
| T&S 6.12 (line 2257) | normal-deduction characterization = base case (Obstacle B.2) |
| T&S 6.8.1–6.8.6 (1510–1610) | Tait/Girard SN (height-free fallback); **6.8.6 uniqueness is separate** (Obstacle B.3) |
| NvP §2.4 (446–457) | "cut-height not monotone / permutation can increase it" = secondary-component placement |
| Gentzen 1935 §3 (398–399) | original double induction (degree, rank) |

> **Caveat (unchanged from report 02):** Prawitz 1965 / Dershowitz–Manna 1979 are referenced
> indirectly (in-file comments; Mathlib). Cite T&S/NvP loci above for the substantive claims.

---

## MESSAGE TO IMPLEMENTATION AGENT (≤200 words)

**Commuting cases h_6/h_7/h_8 (lines 1782/1784/1786) — pattern is verified to close:**
1. `rename_i … D DA DB` (h_8 adds a trailing `E`); `rw [Option.some.injEq] at hd'; subst hd'`;
   `rcases h_subsSN with ⟨hA, hB⟩`.
2. `show Prod.Lex _ _ (_, _) (_, _)` — this unfolds `normMeasure` to the pair; a bare `rw
   [normMeasure]` FAILS.
3. Prove **fst maximalFormulas EQUALITY** (it IS equality, not ≤): `rw [show <source>.maximalFormulas
   = <target>.maximalFormulas from by cases DA <;> cases DB <;> simp_all [maximalFormulas,
   isStronglyNormal, conclusionComplexity]]`. For **h_8 add `maximalFormulas_weakCtx`** to that
   simp set. `hA`/`hB` are consumed here (andI branches ⇒ SN false).
4. `refine Prod.Lex.right _ ?_; cases D <;> simp_all [commutingSum, nodeCount, isStronglyNormal] <;>
   omega`. `Prod.Lex.right` needs the fst rewrite FIRST or it type-mismatches.

**Strategic sorry (1802):** Do NOT prove `redexWeight = 0` via fuel. Prove
`exists_stronglyNormal_form` by `WellFounded.induction normMeasure_wf` (base: `redexWeight_zero_sn`;
step: `reduceRoot_decreases_normMeasure` after normalizing subterms to discharge `reduceRootSubSN`).
Then re-point `subformula_property` at it. `normalize` has NO external consumers — confluence/
uniqueness NOT needed (T&S 6.8.6). Bridge is low-risk.
