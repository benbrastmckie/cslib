# Research Report 04 — Task 512: Birelational-Pivot Feasibility (Decision De-Risking)

**Task type**: cslib (Lean 4, hard / deflection-prone). **Dispatch**: literature-ingestion decision
de-risking (orchestrator, session `sess_1784091167_73afcc`, `--lit` active). **No Lean written.**
**Reference-grounding tier**: 1 (literature-backed, primary sources ingested/cited).
**Builds on report 03** (birelational route identified) — this report does NOT re-derive it; it
INGESTS the primary sources and sharpens the (c)-vs-(d) decision with grounded lemma-level findings.

**Headline**: The birelational pivot's *central mechanism is now literature-confirmed, not
conjectured*: canonical-frame symmetry for intuitionistic S5 is verified via the **prime lemma /
one-sided ≤-mediated incestuality condition — with no negation-completeness step anywhere**
(Simpson Lemma 3.3.2/3.3.3, in corpus; Plotkin–Stirling correspondence Thm 7.1 + Marin–Morales–
Straßburger Thm 7.2, ingested; Došen 1985 abstract, cited). This **raises** report 03's Q1
confidence (~90% → ~92%). BUT ingesting Alechina 2001 **relocates and sharpens** the residual risk:
CSLib's *constructive* (Wijesekera) diamond genuinely requires **pair / fallible-world** canonical
worlds, a construction Došen's single-prime-theory IS5 model does **not** provide. The
constructive-diamond + S5-symmetry combination is **unpublished**, and whether it collapses to the
clean intuitionistic case hinges on **one crisp, unproven sub-question: does Pacheco's CKB=IKB
collapse extend from KB to S5?** **Recommendation: `escalate` — but decision-ready**, gated behind a
cheap 1-task resolution of that collapse question, which converts (d) into either `implement`-grade
clean or a well-scoped larger revise.

---

## Sources: ingested vs. cited

| Source | BibKey (added this dispatch) | Status |
|---|---|---|
| Simpson 1994 PhD thesis | `Simpson1994` (pre-existing) | **In corpus** — read chunks line-by-line |
| Alechina, Mendler, de Paiva, Ritter 2001 | `AlechinaMendlerdePaivaRitter2001` | **Full text ingested** (author preprint PDF, pdftotext) |
| Marin, Morales, Straßburger 2021 (fully-labelled cube IK–IS5) | `MarinMoralesStrassburger2021` | **Full text ingested** (author PDF) — bonus modern survey |
| Došen 1985 (IS5/symmetric completeness) | `Dosen1985` | **Cited** (Springer abstract + PhilPapers + secondary; full text paywalled BF00370809) |
| Božić–Došen 1984 (base birelational engine) | `BozicDosen1984` | **Cited** (Springer abstract; paywalled BF02429840) |
| Ewald 1986 (intuitionistic tense, pair worlds) | `Ewald1986` | **Cited** (via Alechina/Simpson reference lists) |
| Pacheco 2024 (CKB=IKB collapse) | `Pacheco2024` (pre-existing) | Verified in prior dispatches (report 03) |

All five new BibKeys were written to `references.bib`. Alechina + Marin full texts are being ingested
into the global corpus (`literature-ingest.sh`, background) for future dispatches.

---

## Q1 — Symmetry WITHOUT negation-completeness: **CONFIRMED (~92%)**

**Answer: YES.** The birelational canonical model verifies the symmetry / S5 frame condition using
only prime theories (disjunction property) and a ≤-mediated frame correspondence — the
negation-completeness step that blocks CSLib's two-sided tail **never appears**. Three independent,
grounded confirmations:

**(1) Simpson thesis, in corpus — the exact canonical model CSLib would port.**
Chunk `682e04d443e7bbd7` gives the birelational canonical model verbatim:
```
B = (W, ≤, R, V),   W = {X | X prime},   X ≤ X'  iff  X ⊆ X',
X R Y  iff  {◇A | A ∈ Y} ⊆ X  and  {B | □B ∈ X} ⊆ Y,   V(X) = {a | a ∈ X}
```
The modal clause `{B | □B ∈ X} ⊆ Y` is exactly CSLib's **one-sided** `boxInv X ⊆ Y` — no
"back" clause baked into the world. The **Canonical Model Lemma 3.3.3** (chunk `caf3305a53065b87`):
*"X ⊩ A iff A ∈ X, proved by induction on the structure of A, **using the prime lemma** in the
implication and necessity cases."* The **Prime Lemma 3.3.2** (chunk `8372f27240fe345d`): *"If X ⊬ Y
then there exists a prime X' ⊇ X … proved by a standard Lindenbaum construction."* Disjunction
property only — **never** `A ∉ X ⟹ ¬A ∈ X`. Frame conditions F1/F2 are established from the prime
lemma (chunk `8372…` continues into the F2 verification). This is precisely
`box_refuting_theory` / `quasi_prime_exclusion`, which CSLib already has.

**(2) Marin–Morales–Straßburger 2021 (ingested) — the exact S5 frame condition, modern & explicit.**
The whole intuitionistic modal cube IK–IS5 is handled. Symmetry (b) and Euclidean (5) are
**Scott-Lemmon path axioms** `◇ᵏ□ˡA ⊃ □ᵐ◇ⁿA`, and **Theorem 7.1 [Plotkin–Stirling 1986]** gives their
frame correspondence as a **one-sided, ≤-mediated intuitionistic klmn-incestuality condition**:
> *"An intuitionistic modal frame ⟨W,R,≤⟩ validates ◇ᵏ□ˡA ⊃ □ᵐ◇ⁿA iff: if wRᵏu and wRᵐv then there
> exists u′ such that u ≤ u′ and there exists x such that u′Rˡx and vRⁿx."*

**Theorem 7.2** proves soundness + completeness for this whole family (including IS5). The soundness
direction (3⇒4) is a **semantic argument over incestuous frames** using the disjunction-property
saturated sets from the completeness construction — **no negation-completeness**.

**CRUCIAL SUBTLETY (decision-load-bearing).** The correct symmetry condition is **not** plain
classical symmetry `X R Y ⟹ Y R X`; it is the **≤-mediated incestuality condition** above. Marin's
**Remark 7.3** explicitly flags that a related stronger axiom (g1111) *"was problematic in previous
approaches"* precisely because the naive classical condition is wrong intuitionistically. **This is
exactly CSLib's error**: its two-sided `cs5Tail` (`boxInv t ⊆ H` baked into worlds) is the *naive*
symmetry condition, whose per-world back-inclusion equals negation-completeness (report 03 §0). The
pivot's real content is replacing that with the ≤-mediated incestuality condition — which *is*
negation-completeness-free, but must be transcribed exactly right.

**(3) Došen 1985 (cited).** Abstract (Springer BF00370809) confirms: intuitionistic analogues of S4
**and S5** via two-relation models; "soundness and completeness proved … the holding of formulae
characteristic for particular logics is equivalent to conditions for the relations." The
intuitionistic tradition uses prime theories throughout (as its base Božić–Došen 1984 does). *Caveat:
I did not read Došen's exact symmetry lemma line-by-line (paywalled); but Simpson's in-corpus
canonical model + Marin's ingested Thm 7.1/7.2 supply the mechanism at greater lemma-level detail
than Došen's abstract alone.*

**Q1 verdict**: negation-completeness-free — **confirmed, ~92%** (up from report 03's ~90%). The lone
residual is transcribing the exact ≤-mediated incestuality condition correctly, not whether it exists.

---

## Q2 — Diamond strength / tradition match: **NOT the same diamond — this is the sharpened risk (~55–60%)**

**Answer: Došen/Simpson/Marin use the INTUITIONISTIC (Fischer–Servi) diamond; CSLib uses the
CONSTRUCTIVE (Wijesekera) diamond. They are genuinely different, and reconciling them at S5 strength
is unproven.**

- **Intuitionistic diamond** (Došen, Simpson, Marin): `w ⊩ ◇A iff ∃u. wRu ∧ u ⊩ A` (Marin Def. 2.2,
  eq. 5). **Single prime theory per world suffices.** Došen's IS5 canonical model is single-theory.

- **Constructive Wijesekera diamond** (CSLib's CS5): rejects `◇⊥ → ⊥` and `◇(A∨B) → ◇A∨◇B`.
  **Alechina 2001 (ingested) proves this REQUIRES pair / fallible-world canonical worlds.** Direct
  quotes (Alechina §5 Discussion): worlds are *"consistent theories (Γ,Δ) where Δ is a prime filter"*
  (Saturation Lemma 1 — again **prime filter, no negation-completeness**); and decisively:
  > *"if the axioms ◇⊥ and ◇(A∨B)→◇A∨◇B are adopted the sets Δ and fallible worlds become redundant.
  > Without these axioms, however, we also need this 'negative' information to characterise truth at a
  > world fully."*

  So the constructive diamond forces the **head+refutation-set pair** structure — which is *exactly*
  CSLib's own `CKSegment` (head + tail). Alechina does **pairs + S4** (no symmetry); Došen does
  **single-theory + S5**. **No published source does pairs + constructive-diamond + S5-symmetry.**

- **Pacheco 2024 CKB=IKB collapse — the pivotal unknown.** Pacheco proves *syntactically* (nested
  sequents) that adding B (symmetry) to constructive CK collapses it to intuitionistic IK+B **at KB
  strength**. If that collapse extends to **S5** (= CK+T+4+B), then **CS5 = IS5**, the constructive
  diamond's pair complications **vanish** (by Alechina's redundancy remark above, since the collapse
  makes the intuitionistic-diamond axioms derivable), and **Došen 1985 applies directly** — a clean
  single-prime-theory pivot. **But Pacheco proves only KB, not S5.** This is the single crisp,
  unproven gap on which the pivot's difficulty turns.

**Refinement from the per-repo index (Pacheco Lemma 15) — corroborating, decision-relevant.** The
task-509 index entry for `Pacheco2024` records that Pacheco's CKB canonical model is built over
**prime, consistent, NON-maximal theories** and that **Lemma 15 derives symmetry directly from B_dia
(`◇□P → P`) using a DIAMOND-inverse relation** (`Γ ~ Δ iff Γ ⊆ Δ and Δ ⊆ Γ-dia`), *"sidestepping the
maximality obstruction that blocks the box-inverse definition."* This is significant: it means a
**constructive (prime, non-maximal, negation-completeness-free) canonical model with symmetry already
exists in the literature for CKB** — using the diamond-inverse relation rather than the box-inverse
one. It both (a) reinforces Q1 (symmetry is obtainable without negation-completeness, via the
diamond-inverse relation), and (b) suggests a *concrete alternative pivot mechanism* CSLib has not
tried: define the modal relation via the **diamond-inverse** (`◇`-based) direction instead of the
`boxInv`-based one. The residual scope caveat stands — Pacheco/Arisaka et al. explicitly **disclaim
Kripke-semantic completeness for CS5** (S5 strength), which is exactly the collapse-extends-to-S5 gap.

**Q2 verdict**: report 03's "~65% clean adaptation" should be **decomposed**:
- *Symmetry verification is negation-completeness-free*: ~92% (Q1, up).
- *Constructive diamond adapts cleanly at S5* (collapse extends to S5 **or** pairs+S5 goes through):
  **~55–60%** (essentially the same magnitude, but the risk is now *localized* to one named,
  self-contained question rather than diffuse).
- *Full pivot lands sorry-free as-scoped*: **~55–60%** overall — **but ~80% conditional on the
  collapse question resolving YES.**

**Key containment**: the **box-backward blocker itself is diamond-independent** — it concerns only □
and the one-sided R, and becomes the plain prime lemma (`box_refuting_theory`, landed). The diamond
risk lives entirely in the **soundness-rework layer** (does the constructive-diamond + one-sided-R +
incestuality frame class validate CS5's axioms), not in the step that has blocked five dispatches.
CSLib already has the constructive diamond working over pair-worlds (`cs5_diam_witness`).

---

## Q3 — Reusable vs. rebuilt (birelational pivot)

**SURVIVES (reused verbatim or as template):**
| Asset | Role after pivot |
|---|---|
| `box_refuting_theory`, `quasi_prime_exclusion` (`SegmentLindenbaum.lean`) | **box-backward becomes the plain one-sided prime lemma (~60 lines)** — the whole blocker dissolves |
| `CKForces`; propositional / box-forward / diamond-both truth-lemma cases | port directly (as in `ck_truth_lemma` / `cs4_truth_lemma`) |
| `CKSegment` head+tail, `Segment`/`CKExtension`/`cmreach` plumbing | **this IS the birelational pair structure** (= Alechina's fallible pairs) — survives |
| `cs5_diam_witness` (constructive diamond over pairs) | survives |
| **`CS4.lean`'s entire `cs4_truth_lemma` / restricted-tail template** | CS4 already is one-sided-R birelational — the direct precedent to clone |
| Task-509 `cs5FC` frame-condition scaffold (partial) | frame-condition *machinery* reused; the specific bundled conjuncts change |

**MUST BE RE-PROVED / REBUILT:**
1. **Frame class**: replace two-sided `cs5Tail` (`boxInv t ⊆ H` in worlds) with **one-sided R + the
   ≤-mediated S5 incestuality frame condition** (Marin Thm 7.1 shape). ~100 lines.
2. **`cs5FC''` soundness (task-509 rework)**: re-prove soundness for the new incestuality frame
   condition instead of the plain-symmetry+transitivity bundle. **This is the landed-509 rework report
   03 flagged.** ~250–400 lines. Note: handoff 05's `cs5FC''_hub_forces_spoke_connectivity` (which
   exploited *plain* symmetry+transitivity) becomes irrelevant — it was an obstruction *for the
   two-sided design*, not a fact about the new one.
3. **Symmetry-incestuality-holds-on-canonical-model** lemma (the Došen-style verification): new,
   ~150–250 lines.
4. **`cs5_box_backward`** as the one-sided prime lemma: ~60 lines (easy).
5. **Truth lemma + completeness wiring** (`ckvalidFC_completeness` + new frame condition): ~150 lines,
   mostly reuse.

**DISCARDED**: the entire doubled-atom `CS5Combined` apparatus (~520 lines, handoff 04) — dead code,
removed. `Proposition.map` + `cs5_lift_deriv_*` may survive as general utilities.

**Effort estimate for (d)**: **~5–6 phases, ~700–1100 net new lines** (minus ~520 discarded). Bulk =
soundness rework + canonical incestuality verification. **PLUS a prerequisite phase-0**: resolve the
Pacheco-KB→S5 collapse question (proof-theoretic, no Lean — see Q5) which determines whether phases
use Došen's clean single-theory model or the harder unpublished pairs+S5 construction.

---

## Q4 — Any EASIER positive route? **No route with comparable CSLib reuse.**

Surveyed all four requested categories plus existing mechanizations:

- **Algebraic (Heyting algebra with operators / monadic Heyting algebras)**: intuitionistic S5 =
  Bull's **MIPC**, which *does* have algebraic completeness (Bull 1966; corrected by Fischer–Servi
  1978 / Ono 1977 — Simpson chunks `b56578c45467c41e`, `1a9a1019abf8921a`). A genuine positive result,
  **but** for the intuitionistic diamond, and mechanizing Lindenbaum–Tarski algebra + representation
  in Lean reuses **none** of CSLib's Kripke/segment machinery. Not cheaper.
- **Topological semantics** (Fischer–Servi topological Kripke frames; the "companion logics" line,
  ScienceDirect S0168007209001468): exists, same diamond-tradition mismatch, no Lean reuse. Not
  cheaper.
- **Henkin-style sidestepping the pair problem**: the pair problem *is* dissolved by one-sided R —
  that is the pivot's whole point. No separate Henkin trick is needed beyond the prime lemma CSLib
  already has.
- **Labelled / proof-search route** (Marin–Morales–Straßburger; the POSTECH Coq IS5 proof-search
  thesis): gives completeness for the whole cube incl. IS5 and is mechanization-friendly *in
  principle*, but is a **completely different architecture** (labelled sequents + countermodel from
  failed proof search) with **zero CSLib reuse** — a from-scratch reformalization.
- **Existing mechanizations**: Bentzen's Lean S5 Henkin completeness is **classical** S5 (not
  constructive); the POSTECH Coq work is IS5 *proof search* (not Kripke completeness, not reusable);
  the Formalized-Formal-Logic Lean 4 book covers classical modal + IPL. **No existing mechanization of
  constructive/Wijesekera-diamond S5 Kripke completeness exists — CSLib would be first.**

**Q4 verdict**: the **birelational pivot (d) remains the best-reuse positive route.** The algebraic
route is the only genuine alternative positive result, but with materially *less* reuse.

---

## Q5 — Sharper (c) vs (d) recommendation: **`escalate`, but decision-ready and gated**

**What changed vs. report 03** (which said `escalate`, ~90%/~65%):
- Q1 (symmetry negation-completeness-free) is now **literature-confirmed** at lemma level, not
  conjectured → **up to ~92%**, and the *exact* frame condition (≤-mediated incestuality, Marin Thm
  7.1) is identified. This is a real de-risking of the pivot's core mechanism.
- Infra reuse is **higher than report 03 credited**: the box-backward blocker fully dissolves to the
  landed prime lemma, and CSLib's `CKSegment` pair structure + `CS4.lean` are the birelational
  template.
- The residual risk is **relocated and sharpened**: from a diffuse "does it adapt to the constructive
  diamond (~65%)" to **one crisp, self-contained, cheap-to-answer sub-question — does Pacheco's
  CKB=IKB collapse extend to S5?** If YES, pairs vanish and Došen applies directly (pivot ~80%
  clean); if NO, the pivot needs the unpublished constructive-diamond-pairs + S5-symmetry combination
  (still the best positive route, but elevated effort).

**Options table (updated):**

| Option | Verdict | Change from report 03 |
|---|---|---|
| (a) doubled-atom repair | **NO-GO** | unchanged (mechanized dead ends) |
| (b) direct attack in symmetric-tail architecture | **NO-GO** | unchanged (= negation-completeness wall) |
| (c) bank rigorous negative result | **Viable fallback** | reinforced: the *architectural* obstruction (naive symmetry ⇒ negation-completeness) is now literature-grounded as *the wrong frame condition*, not a logic-incompleteness |
| (d) birelational pivot | **Best positive route; core mechanism now confirmed** | de-risked on symmetry (Q1↑) & reuse (Q3↑); residual localized to the Pacheco-KB→S5 collapse question |

**Recommendation: `escalate` — decision-ready, with a concrete cheap de-risking step.** The human
choice is (c) bank the negative result vs. (d) fund the pivot. I recommend **gating (d) behind a
single bounded research task** (proof-theoretic, *no Lean*, ~1 dispatch): **settle whether Pacheco's
CKB=IKB collapse extends to CS5 (T+4+B)**, e.g. by (i) checking whether Pacheco's nested-sequent
cut-elimination argument is parametric in the K-level axioms, or (ii) a direct syntactic argument that
CS5's `◇⊥→⊥` / `◇`-distribution become derivable under T+4+B. That one answer converts the escalation
into either:
- **`implement`-grade clean pivot** (collapse extends → Došen single-theory model applies directly), or
- **well-scoped larger `revise`** (collapse fails → unpublished pairs+S5 construction, ~elevated effort).

This is strictly cheaper and lower-variance than committing to the full multi-file pivot (which
reworks landed task-509 soundness) blind. Do **not** spend further dispatches on (a)/(b).

**Confidence summary**: (a)/(b) stay dead ≥90% (mechanized, report 03). Symmetry pivot
negation-completeness-free ~92%. Full pivot lands sorry-free as-scoped ~55–60% unconditionally,
**~80% conditional on the collapse question resolving YES**. The logic itself is complete (Došen 1985,
intuitionistic S5) — what is blocked is provability in CSLib's *current* two-sided-tail architecture,
which we now identify precisely as encoding the *wrong* (naive, negation-completeness-requiring)
symmetry frame condition instead of the ≤-mediated incestuality condition.

---

## Adversarial self-verification

- *"Symmetry is negation-completeness-free"* — grounded at **lemma level** now, not just abstract:
  Simpson's in-corpus canonical model (one-sided R, truth lemma via prime lemma, chunks `682e…`,
  `caf33…`, `8372…`) + Marin Thm 7.1/7.2 (ingested, ≤-mediated incestuality condition + semantic
  completeness from saturated/prime sets). Residual honestly flagged: Došen's *exact* symmetry lemma
  not read line-by-line (paywalled) — but the mechanism is corroborated by two independent
  full-text sources. Confidence ~92%.
- *"Diamond mismatch is the real risk"* — grounded in Alechina's ingested §5 quotes (constructive
  diamond ⇒ fallible-world pairs; the redundancy remark). This is a *new, sharper* finding than report
  03, which under-weighted the diamond tradition gap. Honestly *raises* the salience of one risk while
  *lowering* another (symmetry).
- *"Pacheco collapse is the pivotal unknown"* — Pacheco proves KB (verified prior dispatches);
  extension to S5 is genuinely unproven. I did **not** assert it holds; I recommend a bounded task to
  settle it. No false optimism.
- *"box-backward dissolves"* — grounded: one-sided R makes it `box_refuting_theory` (landed); this is
  the same object Simpson's Prime Lemma 3.3.2 uses. Diamond-independent.
- **Zero-debt**: no `sorry`/axiom proposed. Fallback (c) is a *proved architectural obstruction*
  (naive-symmetry = negation-completeness), not a placeholder. **Forbidden Option-B sorry deferral is
  not recommended anywhere.**
- **Reuse-first**: the pivot maximally reuses `CKSegment`/`Segment`/`CKExtension`, `box_refuting_theory`,
  `quasi_prime_exclusion`, `CKForces`, `cs5_diam_witness`, and the `CS4.lean` birelational template;
  only the frame-class/soundness/incestuality layer is genuinely new. Verified against `references.bib`
  (BibKeys added) and the in-corpus Simpson chunks.
