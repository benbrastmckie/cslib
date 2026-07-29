# Report 05 — B2 Fuel-Sufficiency: Literature / Prior-Art Spike (HARD mode)

- **Task**: 317 — B2 fuel-sufficiency blocker (`intExpandBranches` saturation termination)
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Type**: cslib / research-only (NO `.lean` edits)
- **Agent**: cslib-research-hard-agent
- **Reference grounding tier**: **Tier 1 (literature-backed)** — BibKey verification against `references.bib` performed
- **Date**: 2026-07-01
- **Sibling spike**: runs in parallel with a source-level Lean measure spike; this report covers ONLY the literature/prior-art dimension.

## Executive Verdict (read this first)

- **Standard measure the field uses for terminating intuitionistic propositional proof search**:
  a **formula-weight measure** (a multiset / weighted sum of formula weights) that strictly
  decreases in every rule of the **contraction-free calculus G4ip** (Hudelmaier 1992, Dyckhoff
  1992). Primary book statements: **Negri & von Plato 2001, §5.5 (pp. 122–125)** and
  **Troelstra & Schwichtenberg 2000, §4.3 (pp. 112–116)**.
- **BUT — the load-bearing finding**: G4ip and both textbook termination proofs are
  **worlds-free**. They terminate proof search over *sequents* and **never create Kripke
  worlds**, so the persistence/monotonicity duplication that blocks us (`propagatePersistence`,
  `Rules.lean:139–141`) **cannot arise in their setting**. The G4ip weight measure therefore
  does **NOT** transfer directly to our labelled tableau.
- **World-count bound (Q2)**: YES — the field bounds the number of generated worlds/points by
  **2^|subformulas(φ)|** (distinct forced-subformula sets = maximally-consistent subsets of a
  finite subformula-closed set). The mosaic literature (Caleiro, Viganò & Volpe 2013, §4.3)
  states this as **|Λ|=O(n), #mosaics=O(2ⁿ), #structures-of-mosaics=O(2²ⁿ)**. Our fuel
  `2^(2·complexity+2) ≈ (2^|subfmls|)²` **lines up exactly** with the O(2²ⁿ) double-exponential.
- **Mapping verdict (Q3)**: **NEEDS-DESIGN-CHANGE (Sfor-containment dedup / loop-check) — OR a
  fuel raise. The literature technique maps only to the *deduplicated* procedure; our current
  loop-check-free code does not match the 2^(2·complexity+2) fuel.** This CONVERGES with the
  sibling source-level spike (see the Conflict Reconciliation below), which independently traced
  the code and found the worst-case **step count = 2^Θ(complexity²)**, exceeding the fuel.
  - *Termination itself* maps cleanly and IS provable: `propagatePersistence` copies only `.pos`
    formulas (`posFormulasAt`, `Rules.lean:126–128`), the only world-creating rule `F(φ→ψ)`
    descends to `F(ψ)` (`intFImpRule`, `Rules.lean:154–159`), and T-rules never emit F-formulas
    (`Rules.lean:190–202`), so the world tree is a priori finite (worlds ≤ complexity+1) and a
    **lexicographic / Dershowitz–Manna measure** (Garg–Genovese–Negri 2012; Dyckhoff 1992)
    strictly decreases. **The loop halts at saturation.**
  - *Fuel-sufficiency with the SPECIFIC bound `2^(2·complexity+2)`* is the failing point. The
    literature's `O(2^(2n))` bound (Caleiro §4.3; FMP filtration) is the size of the **deduplicated
    model** (distinct worlds × distinct forced-sets). The standard procedures achieve *step count =
    model size* precisely **because they deduplicate**: Garg–Negri's `Sfor`-containment stops a
    world from re-processing a forced-set an accessible world already has; without it, backward
    `→R` "can loop forever due to unbounded creation of new worlds" (their words). Our
    `intExpandBranches` has **no** dedup — `intStepBranch`'s `expanded` set is keyed on the full
    `(sign,formula,label)` triple (`Expansion.lean:150–157`), so every T-∨ compound copied by
    persistence to each of the ~c worlds is re-split there, and the independent β-branchings
    multiply to `2^Θ(c²)` — the sibling spike's number, which the literature's dedup is exactly
    designed to prevent.
  - **Fix (converges with sibling spike + original R1 next_action)**: either (A) add an
    `Sfor`-containment dedup / loop-check to `intExpandBranches`/`Rules.lean` so step count
    collapses to the deduplicated model size `≤ 2^(2n)` and the existing fuel becomes adequate
    (this is the literature-standard device); or (B) raise the fuel formula to the `2^Θ(c²)` order
    the un-deduplicated procedure actually needs (a monotone-safe change to `Expansion.lean`,
    re-verify downstream). Both are semantics/def changes beyond `Scheme.lean`-only territory and
    need a plan revision.
- **Top-2 citations for the implementer's proof comment** (updated after web prior-art — the
  world-creating dimension now has an exactly-on-point source):
  1. **`GargGenoveseNegri2012`** (LICS 2012, "Countermodels from Sequent Calculi in Multi-Modal
     Logics") — the precise technique: backward `→R` world creation is tamed by a **lexicographic /
     `Sfor`-set-containment** termination argument, `#Sfor values ≤ 2^|Sub(φ)|`. **BibKey MISSING**
     (entry below). This is the single most relevant citation for *our* rule.
  2. `TroelstraSchwichtenberg2000` §4.3, Def. 4.3.2 + Thm 4.3.5 (G4ip multiset weight; branch
     length ≤ w(Γ⇒A)) — **BibKey PRESENT and verified**; canonical "IPL search terminates".
  - Also load-bearing: `DershowitzManna1979` (multiset well-ordering — the ordering type both
    the G4ip weight and the lexicographic world measure live in; MISSING); `NegriVonPlato2001`
    §5.5 and `Dyckhoff1992` (G4ip origin; MISSING); `Fitting1983` + `ChagrovZakharyaschev1997`
    (PRESENT; labelled tableaux + FMP 2^|subfmls| bound); `FellinNegri2025` (JSL — loop-check-free
    "a fortiori" alternative; MISSING); `Caleiro2013` (mosaic O(2²ⁿ) bound matching our fuel;
    MISSING).

## Source-to-Implementation Mapping (Tier 1)

| Source Claim | BibKey | Lean Target | Translation Notes |
|--------------|--------|-------------|-------------------|
| G4ip weight `w`: `w(P)=w(⊥)=2`, `w(A∧B)=w(A)(1+w(B))`, `w(A∨B)=1+w(A)+w(B)`, `w(A→B)=1+w(A)w(B)`; every premise weight < conclusion; branch length ≤ `w(Γ⇒A)` (Def. 4.3.2; text p.113) | `TroelstraSchwichtenberg2000` (§4.3, pp.112–116) | analog of `classicalExpMeasure` for INT — but **worlds-free**, does not model `propagatePersistence` | The measure decreases because L→ is split into 4 subformula-driven rules; **no world creation**, so it does not answer our F(→) inflation. Cite as the canonical "IPL search terminates" result, not as a drop-in for our labelled loop. |
| Dyckhoff weight `w(⊥)=0, w(P)=1, w(A⊃B)=w(A)+w(B)+1, w(A&B)=+2, w(A∨B)=+3`; active formulas strictly lighter than principal (following Dyckhoff 1992) | `NegriVonPlato2001` (§5.5, p.123) | same as above | Second, independent textbook statement of the same G4ip termination technique; slightly different weight but identical multiset-decrease idea. |
| Terminating intuitionistic calculus "discovered by Hudelmaier (1992) and Dyckhoff (1992)"; L⊃ refined into 4 rules "to the effect that proof search terminates" (Notes to Ch.5, p.125) | `NegriVonPlato2001` / (Dyckhoff1992, Hudelmaier1993 — MISSING) | — | Provenance chain for the primary citation. |
| Analytic restriction to Λ = smallest closed set containing Γ; points = maximally-consistent subsets **maximal in Λ**; Λ finite ⇒ decidability (Thm 4.10; Lemma 4.7) | `Caleiro2013` (§4.2, §4.3 — MISSING) | the *loop-check* our `intExpandBranches` lacks; motivates bounding worlds by the finite closure a priori | This is the labelled-system analogue that DOES map onto a worlds-based procedure — but it requires the finite-closure restriction we don't implement. |
| `|Λ|=O(n)`, `#mosaics=O(2ⁿ)`, `#structures-of-mosaics=O(2²ⁿ)` (§4.3, Thm 4.11 discussion) | `Caleiro2013` | fuel bound `2^(2·complexity+2)` | Magnitude anchor for the fuel's *intent*: `2^(2·complexity+2) = O(2²ⁿ)` = **deduplicated** model size. NOTE: our un-deduplicated code's *step* count is `2^Θ(n²)` > this — see Q2/Q3 Conflict Reconciliation. |
| Finite model property of IPL; countermodels bounded by subformula set (worlds ≤ 2^|subfmls|) | `ChagrovZakharyaschev1997`, `Fitting1969`, `Fitting1983` (all PRESENT) | the bounded-worlds lemma any Lean measure must first establish | Supports candidate (a): measure over the finite `subformulas × worlds` closure, not raw branch contents. |

## Per-Source Findings Table

| # | Source | Location | What it gives us | Verdict impact |
|---|--------|----------|------------------|----------------|
| 1 | Negri & von Plato, *Structural Proof Theory* | §5.5 "A terminating intuitionistic calculus", pp.122–125 | G4ip; Dyckhoff weight function (p.123); "the active formulas in rules have a weight strictly less than the principal formula" | PRIMARY termination technique — but **worlds-free** |
| 2 | Troelstra & Schwichtenberg, *Basic Proof Theory* (2nd ed) | §4.3 "A more efficient calculus for Ip", pp.112–116 | G4ip Def.4.3.1; weight Def.4.3.2; "for each rule…the weight of each premise is lower than the conclusion. So all branches…have length at most w(Γ⇒A)" (p.113); Thm 4.3.5 equivalence to G3ip | PRIMARY (independent) — same worlds-free measure |
| 3 | Caleiro, Viganò & Volpe, *Mosaic Method…* (Studia Logica 2013) | §4.2 (mosaic tableaux), §4.3 (decidability), Lemma 4.7, Thm 4.10–4.11 | Finite closure Λ; analytic-cut restriction (loop-check analogue); `#structures = O(2²ⁿ)` | SUPPORTING — the worlds-based bound that matches our fuel & needs a closure restriction |
| 4 | Chagrov & Zakharyaschev, *Modal Logic* | FMP chapters (Oxford Logic Guides 35, 1997) | Finite model property; subformula-set bound on model size | SUPPORTING — 2^|subfmls| world bound |
| 5 | Fitting, *Proof Methods for Modal and Intuitionistic Logics* | (D. Reidel, 1983) | Prefixed/labelled intuitionistic tableaux with monotonicity; the canonical labelled-tableau reference | SUPPORTING — the labelled architecture our code follows; its terminating variants use loop-checking |
| 6 | Fitting, *Intuitionistic Logic, Model Theory and Forcing* | (North-Holland, 1969) | Kripke/forcing model construction for IPL; persistence | SUPPORTING — semantics behind `propagatePersistence` |
| 7 | **Garg, Genovese & Negri, "Countermodels from Sequent Calculi in Multi-Modal Logics"** | **LICS 2012**, pp.315–324 (PDF: people.mpi-sws.org/~dg/papers/lics12.pdf) | **EXACT match**: "termination condition based on containment of the sets of formulas labeling worlds"; backward search "can loop forever due to unbounded creation of new worlds in (→R)"; terminates because `Sfor(x)` grows monotonically and "the number of possible values of `Sfor` is finite" (≤ 2^\|Sub(φ)\|) | **PRIMARY for our world-creating rule** — the lexicographic/containment measure |
| 8 | Negri, "Proof Analysis in Modal Logic" | *J. Philos. Logic* 34 (2005) 507–544 | G3-style labelled sequent calculi (worlds as relational atoms); decidability via terminating search + loop-checking; labelled intuitionistic system **G3I** (Dyckhoff & Negri) | SUPPORTING — the labelled-calculus framework our tableau mirrors |
| 9 | Fellin & Negri, "A Terminating Intuitionistic Calculus" | *JSL* (2025), doi:10.1017/jsl.2023.88 | **Loop-check-FREE** route: modify `R⊃` with an "a fortiori" premiss (`y : B ⊃ (A ⊃ B)`) → calculus **G3It**; root-first search decidable "without any extra device such as loop-checking"; termination via **Noetherian** (no infinite ascending world-chains) frames + Gödel–Löb induction; failed search yields finite countermodel (Thm 3.5) | ALTERNATIVE to a measure — a *semantics/rule* change giving termination without loop-check |
| 10 | Iemhoff & Jalali, "The G4i analogue of a G3i sequent calculus" | *Studia Logica* (2022/23); arXiv:2011.11847 | Reproduces the **exact Dyckhoff weight**: `w(atom)=w(⊥)=1`, `w(A∨B)=w(A→B)=w(A)+w(B)+1`, `w(A∧B)=w(A)+w(B)+2`; ordering is the **Dershowitz–Manna multiset** order `≪_D` ("Dyckhoff order"), NOT lexicographic | SUPPORTING — precise weight + multiset ordering type |
| 11 | Švejdar, "On Sequent Calculi for Intuitionistic Propositional Logic" | *Comment. Math. Univ. Carol.* (2006) | Explicit: "weight can be bounded by `2n`"; countermodel depth ≤ r (r = #negative implications); "distance from one saturated sequent to another bounded by `2n+1`, the number of all subformulas" | SUPPORTING — concrete subformula-indexed weight bound |
| 12 | Weich (1998) / Larchey-Wendling (2020) | TABLEAUX'98 LNCS 1397; *JAR* 64 (2020) | Formalized IPL decision procedures (MINLOG/Coq): Weich uses a **contraction-free (Dyckhoff) weight**, search-tree linear in #connectives; Larchey-Wendling mechanizes the **Kripke–Curry loop-check** in axiom-free Coq, termination via "almost-full" relations (constructive Ramsey) instead of König's lemma | SUPPORTING — formalization precedent; both avoid the "count compounds per world" trap |

## Answers to the Four Questions

### Q1 — Standard measure/well-ordering, and how it handles world-duplication

There are **two distinct traditions**, and the distinction is the crux of this spike:

- **(A) Worlds-free sequent search (dominant answer to "IPL search terminates").** The
  contraction-free calculus **G4ip / LJT** (Hudelmaier 1992; Dyckhoff 1992) replaces the
  looping left-implication rule `L⊃` with **four subformula-driven rules** so that a
  **formula-weight measure strictly decreases** at every inference. Well-ordering: a
  **multiset / weighted-sum ordering** on formula weights (Dershowitz–Manna-style). It handles
  world-duplication by **not having worlds at all** — there is no Kripke frame in the proof
  object, so the problem is *structurally absent*. Sources: `TroelstraSchwichtenberg2000` §4.3
  (Def. 4.3.2: branch length ≤ `w(Γ⇒A)`); `NegriVonPlato2001` §5.5 (Dyckhoff weight, p.123).

- **(B) Worlds-based labelled/tableau search (our architecture).** The field-standard is a
  **lexicographic / multiset measure whose dominant component is the number of worlds**, bounded
  a priori by the finite forced-subformula-set space. The most on-point source is **Garg,
  Genovese & Negri (LICS 2012)**: the termination condition is **containment of the forced-set
  `Sfor(x)` labelling each world**; backward `→R` (= our `F(→)`) creation terminates because
  `Sfor(x)` **grows monotonically** and its number of possible values is finite (**≤ 2^|Sub(φ)|**,
  the antichain/chain-of-forced-sets bound). Negri (2005) frames the labelled calculus (**G3I**);
  Fellin & Negri (2025) give a **loop-check-free** variant via an "a fortiori" `R⊃` rule and
  **Noetherian** frames. The mosaic reformulation (`Caleiro2013` §4.2–4.3) restricts to a finite
  closure Λ, giving ≤ `2^|Λ|` points and `O(2²ⁿ)` structures. The ordering that makes this
  rigorous is **lexicographic** `(worlds-remaining, intra-world-work)` or a single **Dershowitz–
  Manna multiset** order (Dyckhoff 1992; Dershowitz & Manna 1979) — *not* a flat count.

**Neither tradition uses a naive "count of unexpanded compounds" flat measure that survives world
creation** — tradition (A) sidesteps worlds; tradition (B) makes *worlds* the dominant
lexicographic/multiset component so that creation strictly decreases the measure even while it
inflates the intra-world count. This is exactly why the R1-measure gate (which tried a *flat*
count, plan candidates i/ii) failed, and exactly the fix.

### Q2 — Is world count bounded by 2^|subformulas|, and does our fuel line up?

**Yes.** The finite-model property of IPL bounds countermodels by the subformula set; in the
mosaic formulation this is stated crisply (`Caleiro2013` §4.3): with `|Λ|=O(n)` where `n` is
formula complexity, `#mosaics = O(2ⁿ)` and `#structures-of-mosaics = O(2²ⁿ)`.

Order-of-magnitude alignment with our fuel (grounded in `Subformula.lean:193`,
`complexity` = connective count, so `|subformulas(φ)| = O(complexity)`):

```
fuel = 2^(2·complexity+2) = 4 · (2^complexity)^2 ≈ (2^|subfmls|)^2
     = (world bound)^2 = (2^|subfmls| worlds) × (≥ formulas-per-world)
```

**Crucial caveat (this is where the fuel bound and the code diverge).** The `O(2²ⁿ)` figure
bounds the **DEDUPLICATED model size** — distinct worlds × distinct forced-sets — i.e. the size of
the *mosaic structure*, which the literature obtains by identifying worlds with equal forced-sets
(Caleiro's finite closure Λ; filtration). The fuel `2^(2·complexity+2)` was evidently chosen to
match *that* deduplicated magnitude. But our procedure does **not** deduplicate: a T-∨ compound is
persistence-copied to each of the ~`complexity` worlds and re-split at each (β-branching), and
those branchings multiply, so the raw **step/branch count is `2^Θ(complexity²)`**, not
`2^(2·complexity+2)`. So the fuel magnitude "lines up" with the *intended, deduplicated* design but
**overshoots what the current un-deduplicated code produces** — it is *too small* for the code as
written. (Contrast: the *classical* module `classicalExpMeasure ≤ 3^φ.complexity`
`Classical/Completeness.lean:1273` works because with a single world there is no per-world
re-duplication, so #β-splits = #compounds = O(c) and `3^c` dominates. World creation without dedup
is exactly what breaks the analogy.) **Conclusion for Q2: the world *count* is `≤ complexity+1`
(finite) and the deduplicated model size is `O(2^(2n))` matching the fuel's intent; but the
un-deduplicated *step* count is `2^Θ(c²)`, so the fuel is adequate only if a dedup/loop-check is
added (or the fuel is raised).**

### Q3 — Does the field's approach map onto our formalization without changing persistence?

**Verdict: NEEDS-DESIGN-CHANGE — add an `Sfor`-containment dedup/loop-check (literature-standard)
OR raise the fuel formula. The lexicographic measure proves *termination* cleanly and
semantics-preservingly, but *fuel-sufficiency with the specific `2^(2·complexity+2)` bound* does
NOT hold for the current loop-check-free code, because un-deduplicated per-world re-expansion of
T-∨ compounds gives `2^Θ(complexity²)` steps. This converges with the sibling source-level spike.**

Reasoning, grounded in the code:

1. The two G4ip textbook sources (tradition A) do **not** map: they have no worlds, so they give
   no technique for the `propagatePersistence` duplication. Adopting their measure literally would
   require re-architecting INT into a worlds-free contraction-free sequent search — a fundamental
   redesign, far beyond `Scheme.lean`. (Their *ordering type* — Dershowitz–Manna multiset — does
   transfer; only the worlds-free *encoding* does not.)

2. **The world-tree is a priori finite in our procedure — WITHOUT a loop-check.** This is the
   crucial code observation that softens the earlier draft's harsher reading: `propagatePersistence`
   copies **only `.pos` formulas** (`posFormulasAt`, `Rules.lean:126–128`), so **F-signed formulas
   are never duplicated**. The only world-creating rule `F(φ→ψ)` emits `F(ψ)` at the fresh world
   (`intFImpRule`, `Rules.lean:154–159`), a **strict subformula**; and T-rules never manufacture new
   F-formulas (catalogue `Rules.lean:190–202`: T(∧)→T,T; T(∨)→T|T; T(→)→ modus-ponens T only).
   Hence every F-formula that can ever trigger world creation is a subformula of φ and each firing
   descends, so the world tree has depth ≤ implication-nesting ≤ complexity and is finite. This is
   why our INT propositional loop **saturates** even though Garg–Negri warn that the *general* modal
   backward `→R` "loops forever" without a containment check — in the general case the succedent
   implication persists/reappears; in ours F-formulas do not persist.

3. Therefore the loop **terminates** at saturation (a lexicographic/multiset measure witnesses
   this) — but *that is termination, not the numeric fuel bound*. A **flat per-step Nat measure
   over raw branch contents does not exist** (R1-measure conclusion confirmed — it inflates when a
   T-compound is copied to a fresh label and must be re-expanded there, `Expansion.lean:150–157`).
   And crucially, the number of steps before saturation is **`2^Θ(complexity²)`** for the current
   un-deduplicated code (each of the ~`complexity` worlds re-splits the copied T-∨ compounds, and
   the β-branchings multiply), which **exceeds** the `2^(2·complexity+2)` fuel. So termination maps
   cleanly; the *specific fuel bound* does not, unless one of the following is done:
   - **(A) Add an `Sfor`-containment dedup / loop-check** (RECOMMENDED — literature-standard): in
     `intExpandBranches`/`Rules.lean`, do not create/re-expand a world whose forced-set duplicates
     an accessible world's, and/or treat a persistence-copied compound as already-expanded when an
     accessible world has expanded it. This is exactly Garg–Genovese–Negri's `Sfor`-containment
     device; it collapses the step count from `2^Θ(c²)` to the deduplicated model size `≤ 2^(2n)`,
     making the **existing** `2^(2·complexity+2)` fuel adequate. Cost: edits `Rules.lean`/
     `Expansion.lean` semantics (a soundness re-argument is needed), so it needs a plan revision
     widening territory beyond `Scheme.lean`.
   - **(B) Raise the fuel formula** to the `2^Θ(complexity²)` order the un-deduplicated procedure
     actually needs (e.g. `2^((complexity+1)²)` or similar), a monotone-safe def change in
     `Expansion.lean` — then re-verify the downstream callers (task 316 territory) that pinned
     `2^(2·complexity+2)`. No dedup, but a looser bound and a wider blast radius.
   - **(d) Fellin–Negri (2025) "a fortiori" `R⊃`**: an alternative *rule* change giving a
     Noetherian-frame terminating calculus; also touches `Rules.lean`; listed for completeness.
   - The **lexicographic / Dershowitz–Manna measure** (Garg–Negri 2012; Dyckhoff 1992) is still
     needed to *prove termination* under either fix, but on its own — without (A) or (B) — it does
     NOT rescue the specific `2^(2c+2)` fuel, because the measure's initial value is `2^Θ(c²)`, not
     `2^(2c+2)`. (This is the correction to the mid-report draft; see Adversarial #3.)

   **Recommended: (A).** It is the literature-standard device, keeps the fuel formula (and hence
   downstream callers) unchanged, and is precisely what makes the O(2^(2n)) model-size bound equal
   the step budget. (B) is a viable fallback if editing the rules' soundness proof is undesirable.

### Conflict Reconciliation with the sibling source-level spike (report 04)

The pre-existing `.return-meta.json` in this task dir records a **parallel source-level Lean
spike** (report `04_fuel-sufficiency-measure.md`) that independently traced the code and concluded:
*"worst-case steps = 2^Θ(c²) (persistence duplicates T-or beta across all worlds), exceeding
fuel"*, escalating for a **fuel raise (Option A) or world-dedup (Option B)**. My literature spike's
initial draft had reached the more optimistic "MAPS-CLEANLY, fuel adequate" reading. **On
re-examination the sibling spike is correct and I have revised to converge with it.** The two
spikes now agree:

| Dimension | Sibling spike (report 04, code-level) | This spike (report 05, literature) | Agreement |
|-----------|----------------------------------------|-------------------------------------|-----------|
| Loop terminates? | yes (world bound `W ≤ complexity+1`) | yes (lexicographic/DM measure; F-non-persistence) | ✔ agree |
| Worst-case step count | `2^Θ(complexity²)` | `2^Θ(complexity²)` (un-dedup β-multiplication) | ✔ agree |
| Is `2^(2c+2)` fuel sufficient? | **No** | **No** | ✔ agree |
| Fix | raise fuel (A) or add dedup (B) | add `Sfor`-dedup (A, preferred) or raise fuel (B) | ✔ agree |
| Literature backing | — | Garg–Negri 2012 (dedup is why model size = step budget); Caleiro O(2^(2n)) is *deduplicated* model size | this spike supplies the *why* |

**What the literature adds on top of the code-level finding**: it explains *why* the fuel formula
`2^(2·complexity+2)` was a reasonable target (it matches the deduplicated model size `O(2^(2n))`
from filtration / mosaics) and *why* the code misses it (the standard procedures reach that bound
only through the `Sfor`-containment dedup that our `intExpandBranches` omits). So the fuel formula
is not "wrong" — it is the fuel for the *deduplicated* algorithm, and the cleanest fix is to make
the algorithm deduplicate (Option A), rather than to inflate the fuel.

### Q4 — BibKey citations for the implementer's Lean proof comment

Verified against `/home/benjamin/Projects/cslib/references.bib` (75 entries):

**PRESENT (use directly):**
- `TroelstraSchwichtenberg2000` — *Basic Proof Theory*, 2nd ed. Cite **§4.3, Def. 4.3.2 & Thm
  4.3.5** for the G4ip weight and branch-length bound. (Verified: key + title exact.)
- `Fitting1983` — *Proof Methods for Modal and Intuitionistic Logics*. Cite for the labelled/
  prefixed intuitionistic tableau architecture and monotonicity.
- `Fitting1969` — *Intuitionistic Logic, Model Theory and Forcing*. Cite for the Kripke/forcing
  semantics behind persistence.
- `ChagrovZakharyaschev1997` — *Modal Logic*. Cite for the finite model property / 2^|subfmls|
  world bound.

**MISSING (must be added to `references.bib`; suggested entries):**

```bibtex
@book{NegriVonPlato2001,
  author    = {Negri, Sara and von Plato, Jan},
  title     = {Structural Proof Theory},
  publisher = {Cambridge University Press},
  address   = {Cambridge},
  year      = {2001},
  doi       = {10.1017/CBO9780511527340},
  isbn      = {978-0-521-79307-0}
}

@article{Dyckhoff1992,
  author  = {Dyckhoff, Roy},
  title   = {Contraction-Free Sequent Calculi for Intuitionistic Logic},
  journal = {The Journal of Symbolic Logic},
  volume  = {57},
  number  = {3},
  pages   = {795--807},
  year    = {1992},
  doi     = {10.2307/2275431}
}

@article{Hudelmaier1993,
  author  = {Hudelmaier, J{\"o}rg},
  title   = {An {O}(n log n)-Space Decision Procedure for Intuitionistic Propositional Logic},
  journal = {Journal of Logic and Computation},
  volume  = {3},
  number  = {1},
  pages   = {63--75},
  year    = {1993},
  doi     = {10.1093/logcom/3.1.63}
}

@article{Caleiro2013,
  author  = {Caleiro, Carlos and Vigan{\`o}, Luca and Volpe, Marco},
  title   = {On the Mosaic Method for Many-Dimensional Modal Logics: A Case Study Combining Tense and Modal Operators},
  journal = {Logica Universalis},
  year    = {2013},
  note    = {See also the Studia Logica / Logica Universalis version; §4.2--4.3 for mosaic tableaux and decidability}
}

@article{DershowitzManna1979,
  author  = {Dershowitz, Nachum and Manna, Zohar},
  title   = {Proving Termination with Multiset Orderings},
  journal = {Communications of the ACM},
  volume  = {22},
  number  = {8},
  pages   = {465--476},
  year    = {1979},
  doi     = {10.1145/359138.359142}
}

@inproceedings{GargGenoveseNegri2012,
  author    = {Garg, Deepak and Genovese, Valerio and Negri, Sara},
  title     = {Countermodels from Sequent Calculi in Multi-Modal Logics},
  booktitle = {Proceedings of the 27th Annual IEEE Symposium on Logic in Computer Science (LICS 2012)},
  pages     = {315--324},
  publisher = {IEEE Computer Society},
  year      = {2012},
  doi       = {10.1109/LICS.2012.42}
}

@article{Negri2005,
  author  = {Negri, Sara},
  title   = {Proof Analysis in Modal Logic},
  journal = {Journal of Philosophical Logic},
  volume  = {34},
  number  = {5--6},
  pages   = {507--544},
  year    = {2005},
  doi     = {10.1007/s10992-005-2267-3}
}

@article{FellinNegri2025,
  author  = {Fellin, Giulio and Negri, Sara},
  title   = {A Terminating Intuitionistic Calculus},
  journal = {The Journal of Symbolic Logic},
  year    = {2025},
  note    = {First published online 2023},
  doi     = {10.1017/jsl.2023.88}
}

@article{IemhoffJalali2022,
  author  = {Iemhoff, Rosalie and Jalali, Raheleh},
  title   = {The G4i Analogue of a G3i Sequent Calculus},
  journal = {Studia Logica},
  year    = {2022},
  note    = {arXiv:2011.11847},
  doi     = {10.1007/s11225-022-10008-3}
}

@article{Svejdar2006,
  author  = {{\v S}vejdar, V{\'\i}t{\v e}zslav},
  title   = {On Sequent Calculi for Intuitionistic Propositional Logic},
  journal = {Commentationes Mathematicae Universitatis Carolinae},
  volume  = {47},
  number  = {1},
  pages   = {159--173},
  year    = {2006}
}
```

Recommended proof-comment citation string (assuming Option A dedup is adopted so the fuel is
adequate):

> Termination of the intuitionistic tableau saturation loop uses a lexicographic / Dershowitz–
> Manna multiset measure whose dominant component is the number of created Kripke worlds
> (Garg, Genovese & Negri, LICS 2012, `GargGenoveseNegri2012`; Dershowitz & Manna 1979,
> `DershowitzManna1979`). The world tree is finite (worlds ≤ complexity+1) because only `F(φ→ψ)`
> creates worlds and it descends to the subformula `F(ψ)`, while persistence copies only
> T-formulas, so F-formulas never persist. The step budget matches the fuel `2^(2·complexity+2)`
> ONLY because the loop deduplicates via `Sfor`-containment (Garg–Negri): without dedup the
> re-expansion of persistence-copied T-∨ compounds at each world multiplies to `2^Θ(complexity²)`
> steps. The fuel equals the deduplicated finite-model bound `O(2^(2n))` (`ChagrovZakharyaschev1997`
> FMP; `Caleiro2013` §4.3). The worlds-free G4ip weight (`TroelstraSchwichtenberg2000` §4.3) is not
> used directly, as it models no world creation.

## Online Prior-Art (WebSearch dimension — completed)

Two web-research agents completed. Key findings (with URLs), most-relevant-first:

- **Garg, Genovese & Negri, LICS 2012 — the exact technique.** PDF:
  https://people.mpi-sws.org/~dg/papers/lics12.pdf. Quoted: *"termination condition based on
  containment of the sets of formulas labeling worlds"*; *"backwards search … can loop forever
  due to unbounded creation of new worlds in the rules (→R)"*; *"the number of possible values of
  `Sfor` is finite"*, and the countermodel adds `x ≤ y` whenever `Sfor(x) ⊆ Sfor(y)`. This is the
  `Sfor`-set-containment = lexicographic world measure, directly applicable to our `F(→)` rule.
- **Fellin & Negri, "A Terminating Intuitionistic Calculus", JSL 2025** (doi:10.1017/jsl.2023.88).
  Loop-check-FREE labelled G3It via an "a fortiori" `R⊃`; decidable by root-first search, finite
  countermodel on a reflexive/transitive/**Noetherian** frame (Thm 3.5). An alternative rule-level
  route.
- **Negri, "Proof Analysis in Modal Logic", JPL 34 (2005)** (doi:10.1007/s10992-005-2267-3):
  G3-style labelled calculi (worlds as relational atoms), decidability via terminating search with
  loop-checking; labelled intuitionistic **G3I** (Dyckhoff & Negri).
- **Dyckhoff (1992)** "Contraction-free sequent calculi for intuitionistic logic", *JSL* 57(3)
  795–807 (+ a 2018 correction; 2016 survey "Intuitionistic decision procedures since Gentzen",
  open PDF at research-repository.st-andrews.ac.uk). **Exact weight** (via Iemhoff–Jalali,
  arXiv:2011.11847, reproducing Dyckhoff 1992): `w(atom)=w(⊥)=1`, `w(A∨B)=w(A→B)=w(A)+w(B)+1`,
  `w(A∧B)=w(A)+w(B)+2`; ordering = **Dershowitz–Manna multiset** `≪_D`, explicitly NOT lexicographic.
- **Hudelmaier (1993)** "An O(n log n)-space decision procedure for IPL", *J. Logic Comput.* 3(1)
  63–75: deduction lengths **linearly bounded** in |φ|; contraction-free size-decreasing rules.
- **Švejdar (2006)** (cuni.cz/~svejdar/papers/sv_iproc.pdf): weight ≤ `2n`; countermodel depth ≤
  #negative-implications; saturation distance ≤ `2n+1` subformulas — a concrete subformula-indexed
  bound.
- **Finite model property / 2^|Sub(φ)| worlds**: filtration (`ChagrovZakharyaschev1997` Ch.5,
  modal, transported to IPC via Gödel–McKinsey–Tarski) and subformula-saturated-set FMP
  (`TroelstraVanDalen1988` Ch.2, present in bib); SEP *Intuitionistic Logic* confirms
  "nodes forcing subsets of Sub(E)". Consequence: IPC validity is PSPACE-complete (Statman 1979 /
  Ladner 1977 via Gödel translation).
- **Formalized precedents**: Weich (TABLEAUX'98, MINLOG/Coq program extraction, Dyckhoff weight,
  search-tree linear in #connectives); Larchey-Wendling (*JAR* 2020, axiom-free Coq Kripke–Curry
  loop-check, termination via "almost-full" relations / constructive Ramsey instead of König's
  lemma). A recent Lean formalization (arXiv:2410.23765, 2024) and the FormalizedFormalLogic Lean
  4 project cover IPL **soundness/completeness via canonical models**, but **not** a terminating
  decision procedure — so there is **no existing Lean termination-measure precedent** to reuse; our
  proof would be novel in Lean.

Web-agent caveat (recorded honestly): exact theorem/lemma *numbers* in Chagrov–Zakharyaschev
(filtration, Ch.5) and Fiorino's CEUR degree-function lemmas were not extracted from the
paywalled/scanned PDFs; those are cited by title/venue/DOI and the specific numbers should be
confirmed against the PDFs before quoting a theorem number in a proof comment. The `2^|Sub(φ)|`
figure is the standard filtration bound; several IPC-specific papers give a sharper "depth linear
in |φ|" refinement.

## Adversarial Self-Verification (H4)

Challenging each load-bearing claim:

1. **"The G4ip weight is the standard measure" — but does it apply to OUR rule?**
   Challenge: the task framing assumed Negri & von Plato give a *labelled* terminating calculus
   that would map onto our worlds-based tableau. **This is inaccurate.** The 2001 book's
   terminating calculus (§5.5) is **G4ip, worlds-free**. Labelled G3-style sequent calculi with
   explicit worlds are in Negri's *later* work (Negri 2005, "Proof analysis in modal logic",
   *J. Philos. Logic*; Negri & von Plato 2011, *Proof Analysis*), **not** in the PDF we hold.
   Consequence: the primary local source does **not** directly answer our world-duplication
   problem; it answers the *different* question "does IPL propositional search terminate". I have
   flagged this explicitly rather than overclaiming a clean mapping. **Confidence: high** (read
   §5.5 pp.122–125 and the full TOC directly).

2. **"World count ≤ 2^|subformulas|, so fuel lines up" — does the bound really hold for a
   procedure that has NO loop-check?**
   Challenge: the general Garg–Negri statement is that backward `→R` "loops forever" WITHOUT a
   loop-check — implying our loop-check-free code might never saturate, which would make
   fuel-sufficiency *false*, not just hard to prove. **Resolution (code re-check):** their "loops
   forever" is for the *general modal* case where the succedent implication persists/reappears at
   new worlds. In our INT propositional procedure, `propagatePersistence` copies **only `.pos`
   formulas** (`posFormulasAt`, `Rules.lean:126–128`), so F-formulas never persist; the only
   world-creating rule descends to the subformula `F(ψ)` and T-rules never emit F-formulas
   (`Rules.lean:190–202`). Hence the F-recursion strictly descends on subformulas and the world
   tree IS a priori finite — the "missing lemma" is *provable from subformula descent*, not
   dependent on a loop-check. **But finiteness of the world *count* (≤ complexity+1) does NOT bound
   the *step/branch* count**: with ~complexity worlds each re-splitting persistence-copied T-∨
   compounds, the β-branchings multiply to `2^Θ(complexity²)` steps (see #3 and the Conflict
   Reconciliation). So the world bound supports *termination*, not fuel *sufficiency*. **Confidence:
   high** on finiteness of the world tree (traced the rule catalogue directly); the earlier "ample
   slack" reading was wrong and is retracted in #3.

3. **VERDICT — TWO revisions (the H4 core).**
   *First revision:* my initial draft (from the Caleiro/mosaic source alone) said
   **NEEDS-LOOP-CHECK-DESIGN-CHANGE**; the Garg–Negri lexicographic result + re-reading the rules
   (F-non-persistence ⇒ finite world tree) pushed me to **MAPS-CLEANLY via a lexicographic
   measure**.
   *Second revision (decisive):* the pre-existing `.return-meta.json` revealed a **parallel
   source-level spike (report 04)** that had independently code-traced the **worst-case step count
   = `2^Θ(complexity²)`**, exceeding the `2^(2·complexity+2)` fuel. This directly falsified my
   "MAPS-CLEANLY, fuel adequate" reading. Re-checking the arithmetic confirmed the sibling spike:
   my error was conflating the **deduplicated model size** (`O(2^(2n))`, which the fuel targets)
   with the **un-deduplicated step count** (`2^Θ(c²)`, which the current loop-check-free code
   produces because persistence-copied T-∨ compounds re-split at every world and the β-branchings
   multiply). "Finite worlds" bounds the world *count*, not the *step/branch* count. **Final
   verdict: NEEDS-DESIGN-CHANGE — add an `Sfor`-containment dedup (Option A, literature-standard) or
   raise the fuel (Option B); termination is provable but the specific `2^(2c+2)` fuel is NOT
   sufficient for the current code.** This CONVERGES with the sibling spike and the original
   handoff R1 next_action. **Confidence: high** — two independent spikes (code-level and
   literature) now agree, and the literature (Garg–Negri: dedup is why model-size = step-budget)
   explains the mechanism. I explicitly retract the mid-report "MAPS-CLEANLY / fuel adequate"
   claim; it was an over-correction that the sibling arithmetic caught.

4. **Citation integrity.** `TroelstraSchwichtenberg2000`, `Fitting1983`, `Fitting1969`,
   `ChagrovZakharyaschev1997`, `TroelstraVanDalen1988` were **read out of `references.bib`** and
   confirmed present with exact titles. The **10** keys `NegriVonPlato2001`, `Dyckhoff1992`,
   `Hudelmaier1993`, `Caleiro2013`, `DershowitzManna1979`, `GargGenoveseNegri2012`, `Negri2005`,
   `FellinNegri2025`, `IemhoffJalali2022`, `Svejdar2006` were confirmed **absent** by grep and are
   supplied as new entries — I do **not** cite them as if verified; they are marked MISSING.
   Page/section numbers for the two local books were taken from pages I read directly (Negri §5.5
   = PDF pp.141–145 = book pp.122–125; T&S §4.3 = PDF pp.124–129 = book pp.112–116; Caleiro §4.2–4.3
   = local markdown chunks). Web-sourced venue/DOI details for the online-only papers are from the
   two background agents and should be double-checked before a proof comment quotes a theorem
   *number* (see the "Web-agent caveat" above). **Confidence: high** on the local citations;
   **medium-high** on the exact page numbers of the online-only papers.

5. **Reuse-check completeness (CSLib).** Before recommending any measure I confirmed the INT
   module has no existing bounded-worlds/closure apparatus and that the *classical* analog
   (`classicalExpMeasure`, `classicalBranchComplexity`, bound `3^φ.complexity`,
   `Classical/Completeness.lean:473,1273`) is single-exponential and worlds-free, so it is a
   template for the *shape* of a measure proof but not for the worlds dimension. No existing
   CSLib abstraction covers bounded-world enumeration for INT tableaux. **Confidence: high.**

**The verdict was revised TWICE during self-verification** (NEEDS-DESIGN-CHANGE → MAPS-CLEANLY →
back to NEEDS-DESIGN-CHANGE; see #3). No `## Revised Direction` *restart* was required because the
research line (literature technique + code grounding) stayed valid throughout — only my
intermediate conclusion oscillated, and the sibling spike's independent arithmetic anchored the
final answer. **Final stable position: the loop terminates, but the `2^(2·complexity+2)` fuel is
insufficient for the current un-deduplicated code (`2^Θ(c²)` steps); the fix is an `Sfor`-containment
dedup (Option A, preferred) or a fuel raise (Option B).** This agrees with the sibling source-level
spike (report 04) and the original handoff R1 next_action.

## Recommended Next Actions (actionable, zero-debt)

1. **Escalate the same architectural choice the sibling spike raised — now with literature
   backing.** The decision is A vs B:
   - **(A) Add an `Sfor`-containment dedup / loop-check** to `intExpandBranches`/`Rules.lean`
     (RECOMMENDED): do not re-expand a persistence-copied compound already discharged at an
     accessible world (or do not create a forced-set-duplicate world). This is Garg–Genovese–Negri's
     standard device; it collapses steps to the deduplicated model size `≤ 2^(2n)`, so the **existing
     fuel becomes adequate** and downstream callers are untouched. Requires a soundness re-argument
     for the modified rule and a **plan revision** widening territory beyond `Scheme.lean`.
   - **(B) Raise the fuel formula** in `Expansion.lean` to `~2^Θ(complexity²)` (monotone-safe def
     change), then re-verify task-316 downstream callers. No dedup; looser bound; wider blast radius.
2. **Prove termination via a lexicographic / Dershowitz–Manna measure** `(worlds-created downward,
   intra-world unexpanded-compound count)` — cite `GargGenoveseNegri2012` and `DershowitzManna1979`.
   This is needed under either A or B. The world-finiteness sub-lemma (worlds ≤ complexity+1) is
   provable from subformula descent (F-formulas never persistence-copied; `F(φ→ψ)` descends to
   `F(ψ)`). NOTE: this proves *termination*, not the numeric fuel bound — do not present it as
   closing sorry 658 on its own.
3. **Do NOT attempt to close sorry 658 with a `Scheme.lean`-only measure** and the current fuel:
   the sibling spike and this report agree that is impossible (`2^Θ(c²) > 2^(2c+2)`). Mark Phase 2a
   **[BLOCKED]** pending the A/B decision (zero-debt: no `sorry`, no axiom, no placeholder).
4. **Add the 10 missing BibKeys** (entries in Q4) to `references.bib` before the implementer cites
   them — most importantly `GargGenoveseNegri2012` (dedup rationale) and `DershowitzManna1979`.
5. In the measure docstring, briefly note *why* the worlds-free G4ip weight
   (`TroelstraSchwichtenberg2000` §4.3; `NegriVonPlato2001` §5.5) is NOT used directly (it models
   no world creation), pre-empting reviewer confusion.

## Files Referenced (absolute paths)

- `/home/benjamin/Projects/cslib/specs/literature/Structural_Proof_Theory_Negri_von_Plato.pdf` (§5.5, book pp.122–125)
- `/home/benjamin/Projects/cslib/specs/literature/Basic_Proof_Theory_Troelstra_Schwichtenberg.pdf` (§4.3, book pp.112–116)
- `/home/benjamin/Projects/Literature/sources/caleiro_2013/sec06_42-mosaic-based-tableaux.md`
- `/home/benjamin/Projects/Literature/sources/caleiro_2013/sec07_43-decidability-via-mosaics.md`
- `/home/benjamin/Projects/cslib/references.bib`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` (139–159)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (110–159)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Subformula.lean` (189–216)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` (473, 1273)
- `/home/benjamin/Projects/cslib/specs/317_propositional_tableau_completeness/.orchestrator-handoff.json` (R1-measure blocker)
