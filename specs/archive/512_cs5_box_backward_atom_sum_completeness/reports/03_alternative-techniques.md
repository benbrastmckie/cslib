# Research Report 03 — Task 512: Alternative Techniques / Architectural Verdict

**Task type**: cslib (Lean 4, hard / deflection-prone). **Dispatch**: focused blocker-research
(orchestrator, session `sess_1784091167_73afcc`, `--lit` active). **No Lean written** (research dispatch).
**Reference-grounding tier**: 1 (literature-backed).

**Headline verdict**: The impasse is **real and now externally corroborated**. A genuinely different,
literature-grounded, mechanizable technique DOES exist — the **birelational canonical model**
(Božić–Došen 1984, Došen 1985, Simpson 1994) — but it is an **architecture replacement**, not a repair
of the doubled-atom scaffold, and it requires switching semantic tradition and reworking landed
task-509 soundness. **Recommendation: `escalate`** — a human must authorize the architecture pivot
(the only route with a *known positive completeness result*) versus accepting a rigorous negative
result. Neither "keep doubled-atom" nor "direct attack within the current symmetric-tail architecture"
is viable — both bottom out at the identical wall.

---

## 0. The wall, stated precisely (why five dispatches converged)

CSLib's CS5 canonical model bakes symmetry into **worlds** via a *two-sided* tail
`cs5Tail H = {t | QuasiPrime t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}` (`CS5.lean:632`). The box-backward
existence step needs, from `□A ∉ H`, a witness pair. A single prime Lindenbaum extension of `boxInv H`
avoiding `A` (CSLib's `box_refuting_theory`, `SegmentLindenbaum.lean:177`) delivers a prime `T` with
`boxInv H ⊆ T` and `A ∉ T` — but **not** the second, "back" clause `boxInv T ⊆ H`. Repairing that clause
forces enlarging `H → H'`, re-enlarging `boxInv H'`, and re-solving: the **simultaneous prime pair**.

**Why this is fundamental, not incidental.** Classically, the back-inclusion (R-symmetry on the
canonical model) is proved from the B axiom *plus negation-completeness*: `□A ∈ Δ, A ∉ Γ ⟹ ¬A ∈ Γ`
(neg.-completeness) `⟹ □◇¬A ∈ Γ` (B) `⟹ ◇¬A ∈ Δ ⟹ ¬□A ∈ Δ`, contradiction. The single step that
constructive/quasi-prime theories cannot take is `A ∉ Γ ⟹ ¬A ∈ Γ`. Prime theories have only the
disjunction property, never negation-completeness. **The two-sided symmetric-tail world condition is
therefore the one canonical-model design that is structurally incompatible with prime theories.** The
doubled-atom "combined system" repair internalizes the same back-inclusion via `crossRL`, so it inherits
the identical obstruction — mechanized in handoff 04 (`cs5Combined_symmetric_tail_box_gap`) and handoff 05
(`cs5FC''_hub_forces_spoke_connectivity`): the doubled-atom route is *exactly as hard as* a direct attack.

---

## 1. LITERATURE (deliverable 1)

Searched the per-repo corpus (`specs/literature-index.json`: Simpson 1994, Wijesekera 1990,
Bierman–de Paiva, Arisaka–Das–Straßburger, Pacheco 2024 all present) via `literature-search.sh`, plus
WebSearch/WebFetch beyond the corpus. Findings, most-load-bearing first:

### 1.1 Pacheco 2024 — reframes the entire problem (BibKey `Pacheco2024`, in `references.bib`)
Fetched `arxiv.org/pdf/2408.16428`. Precise result: **CKB and IKB coincide** (constructive KB = intuitionistic
KB), proved **syntactically via nested sequents** (not semantically). Two decisive corollaries for this task:
- **"There are no [Kripke] semantics for CKB in the literature."** The whole reason CSLib is building a
  bespoke symmetric-tail canonical model is that no off-the-shelf constructive-symmetric Kripke semantics
  exists — this task is genuinely at the research frontier, not re-deriving a known construction.
- Pacheco's own canonical-model Lemmas 14–18 **rely on maximal consistent sets / negation-completeness**
  (confirmed by fetch; matches handoffs 01/05). They cannot port to CSLib's quasi-prime setting. This is a
  property of *Pacheco's proof*, not of the logic.
- Scope caveat: the collapse is proved for **KB**, not explicitly extended to S5 (T+4+B). CSLib's CS5 =
  CK + T + 4 + B, so the collapse is *strongly suggestive but not literally proved* for CS5.

**Implication**: the constructive symmetric logic is (at KB strength, provably) the *same logic* as the
intuitionistic one — so the intuitionistic-tradition completeness machinery (below) is the *right* tool,
and CSLib's CK-style symmetric-tail model is fighting a collapse.

### 1.2 Došen 1985, "Models for stronger normal intuitionistic modal logics" — THE positive result
*Studia Logica* 44:39–70. Sequel to Božić–Došen 1984; treats intuitionistic analogues of **S4 and S5**
(and the stronger symmetric systems). Gives **two-relation (birelational) Kripke models** — one
intuitionistic preorder `≤`, one modal `R` — and proves **soundness and completeness**, with each
characteristic axiom shown equivalent to a condition on the relations. This is a **published completeness
proof for intuitionistic S5 that uses prime theories, not negation-completeness** — precisely the object
CS5 needs, in the model architecture CSLib is *not* using. **Not in `references.bib` — must be added.**

### 1.3 Božić–Došen 1984, "Models for normal intuitionistic modal logics" — the foundational engine
*Studia Logica* 43:217–245. Two-relation canonical model for intuitionistic K; box-only, diamond-only,
and both. Establishes the template: worlds = prime theories, `≤` = inclusion, `R` one-sided
(`Γ R Δ ⟺ boxInv Γ ⊆ Δ`), frame conditions on how `≤` and `R` combine. **Not in `references.bib`.**

### 1.4 Simpson 1994 (BibKey `Simpson1994`, in `references.bib` + corpus + clean copy at
`cs.cmu.edu/~fp/courses/15816-s10/papers/Simpson94.pdf`)
Read corpus chunks (`8372f27240fe345d` prime lemma; `2878b56d67a1617c` bounded prime lemma;
`bdcec2075c3ee8a2` IS5 = equivalence relation). Confirms the **birelational** framework with confluence
conditions **(F1)** (forward, `≤∘R ⊆ R∘≤`) and **(F2)** (backward, `R∘≤ ⊆ ≤∘R`) — WebSearch confirmed
these are "forward/backward confluence", F1 for preserving intuitionistic validity, F2 for
first-order interpretability. Simpson's box-backward existence is a **standard one-sided Lindenbaum "prime
lemma"** — no two-sided tail, no simultaneous pair. His "bounded prime lemma / bounded canonical model"
(chunk `2878b...`) is a **step-by-step / finite-approximant** construction (uses decidability by case
analysis) — a second, distinct technique from the corpus.

### 1.5 Ewald — intuitionistic tense logic: a genuine PAIR / "twin" canonical model
WebSearch confirmed Ewald's intuitionistic tense logic (operators G, H, F, P with converse axioms
`A → GPA`, `A → HFA`) is proved complete by a **canonical model whose worlds are pairs `(Aω, Bω)` of
formula sets** — the closest published analogue to the "simultaneous pair / twin canonical model" this task
keeps needing, for exactly the *converse/symmetric* operator setting. The converse (past/future) operators
play the structural role of the L/R sorts. **Not in `references.bib`** (Ewald 1986, *JSL* 51:166–179).
Caveat: tense logic separates the two operators syntactically; adapting to a single symmetric `□` is
non-trivial but this is the one place a *pair-world* construction is made to work constructively.

### 1.6 Constructive-tradition adaptations (the CK/Wijesekera diamond)
- **Alechina–Mendler–de Paiva–Ritter 2001**, "Categorical and Kripke Semantics for Constructive S4"
  (CS4, birelational; the tradition CSLib's `CS4.lean` mirrors). **Not in `references.bib`.**
- **arXiv:2403.00201**, "Constructive S4 modal logics with the finite birelational frame property" —
  confirms birelational models are the live tool for the *constructive* diamond, with FMP.
- **Wijesekera 1990** (BibKey `Wijesekera1990`) — constructive modal logic, non-dual diamond; the diamond
  tradition CSLib follows. Completeness via a canonical construction, but for K (no symmetry).
- **Arisaka–Das–Straßburger 2015** (BibKey `ArisakaDasStrassburger2015`, in corpus) — a **complete
  nested-sequent calculus for CKB** with cut-elimination. This is a *proof-theoretic* completeness route
  that bypasses canonical models entirely (see §2, technique C).

---

## 2. VERDICT ON A NEW TECHNIQUE (deliverable 2)

**Yes — one primary and two secondary techniques exist, none on the confirmed-dead-end list.**

### Technique A (PRIMARY, recommended): birelational canonical model, symmetry via ≤-mediated frame condition
Source: Došen 1985 (IS5-strength) built on Božić–Došen 1984 + Simpson 1994.

**How it dissolves the wall.** Do **not** bake symmetry into worlds. Instead:
- Worlds = prime (quasi-prime) theories; `≤` = `⊆`; `R` **one-sided** (`Γ R Δ ⟺ boxInv Γ ⊆ Δ`).
- Box truth quantifies through `≤ ∘ R` (monotone), as in the existing `CKForces`.
- **Box-backward existence is the plain one-sided prime lemma**: `□A ∉ Γ ⟹ boxInv Γ ⊬ A ⟹` (prime
  Lindenbaum, = CSLib's `box_refuting_theory`) a prime `Δ ⊇ boxInv Γ` with `A ∉ Δ`, and `Γ R Δ`. **No
  second clause, no simultaneous pair, no `H'` enlargement.**
- The **B/symmetry axiom becomes a frame *correspondence* condition** verified over the *whole* canonical
  frame using only the **disjunction property + F1/F2 confluence** — Došen's completeness proof does exactly
  this and *never uses negation-completeness*. The negation-completeness step that blocks CSLib simply does
  not appear, because symmetry is a global frame property, not a per-world back-inclusion.

**Mapping to CSLib.** This replaces `cs5Tail` (two-sided) with a birelational world/relation whose frame
condition matches Došen's IS5 correspondence; `CKForces` and the propositional/box-forward/diamond truth-lemma
cases largely survive; `box_refuting_theory` / `quasi_prime_exclusion` are reused verbatim for box-backward.
It **discards the doubled-atom `CS5Combined` apparatus entirely** and reworks the frame-condition/soundness
layer landed in task 509 (`cs5FC''`).

**Residual risk (honest).** (i) CSLib's diamond is the *constructive* (Wijesekera) diamond; Došen's is the
*intuitionistic* one. Pacheco's CKB=IKB collapse makes them coincide at KB strength (reassuring) but is not
literally proved for S5 — the exact CS5 axiom set must be matched to a Došen IS5 whose diamond agrees, or
the collapse re-derived. (ii) Intuitionistic S5 is genuinely subtle (multiple inequivalent "IS5"s; some
naive birelational semantics are incomplete) — the correspondence must be matched carefully. This is why it
is a human-authorized pivot, not an autonomous continuation.

### Technique B (SECONDARY): Ewald-style pair/twin canonical worlds
Source: Ewald intuitionistic tense logic. Worlds = pairs `(future-content, past-content)`; the converse
operators are the symmetric pair. This is a *constructive* pair-world construction that actually works — the
literature realization of the "simultaneous pair" CSLib wants. Closer in spirit to the doubled-atom idea but
*not* homomorphic and *not* generic-Lindenbaum (so off the dead-end list). Weaker recommendation: it is
tense-logic-shaped (two distinct operators), and collapsing it to a single symmetric `□` is unproven work.

### Technique C (SECONDARY): proof-theoretic completeness via nested sequents + cut-elimination
Source: Arisaka–Das–Straßburger 2015 (complete nested-sequent calculus for CKB). Completeness via
cut-elimination bypasses canonical models entirely. **Not recommended for mechanization**: nested sequents +
cut-elimination in Lean is an enormous, separate formalization effort with no CSLib infrastructure to reuse.

**Explicitly NOT any confirmed dead end**: A/B/C are none of homomorphic translations, atom-indexed toy
models, the multi-world cluster (refuted by `cs5FC''_hub_forces_spoke_connectivity`), the
necessitation/K/cross-axiom algebra, generic-Lindenbaum excluding-witness, or a general `CS5Combined` truth
lemma. They differ at the *architecture* level (one-sided R + global frame correspondence, or pair-worlds,
or proof theory), which no prior dispatch touched.

---

## 3. ARCHITECTURE RECOMMENDATION (deliverable 3): go/no-go

| Option | Verdict | Reason |
|---|---|---|
| (a) keep investing in doubled-atom repair | **NO-GO** | Mechanically shown (handoffs 04/05) exactly as hard as a direct attack; five dispatches; bottoms out at the negation-completeness wall via `crossRL`. |
| (b) direct CS5 box-backward *within the current symmetric-tail architecture* | **NO-GO** | Identical wall — the two-sided tail's back-inclusion `boxInv T ⊆ H` *is* the negation-completeness step that fails for quasi-prime theories. Bypassing doubled atoms does not bypass the wall. |
| (c) declare completeness BLOCKED with a rigorous negative result | **Viable fallback** | Honest and defensible: "CS5 box-backward is unprovable within the symmetric-tail/`cs5FC''` architecture over quasi-prime theories, because its back-inclusion is equivalent to negation-completeness, which prime theories lack; the doubled-atom repair provably inherits this." A partially-mechanizable *architectural* obstruction (not a claim the logic is incomplete — it is not). |
| (d) pivot to birelational canonical model (Technique A) | **The only positive route** | Only architecture with a *known published completeness result* for intuitionistic S5 (Došen 1985). Large: discards doubled-atom scaffold, reworks `cs5Tail`/`cs5FC''` and task-509 soundness, switches to the intuitionistic-diamond tradition (justified by Pacheco's collapse, with residual risk). |

**Recommended: ESCALATE for a human go/no-go between (d) and (c).** Rationale:
- (a) and (b) are eliminated on mechanized evidence — do not spend a sixth dispatch on either.
- (d) is genuinely available and is the *right* mathematics, but it is a **major multi-file architecture
  rework that may re-open landed task-509 soundness** and **switches semantic tradition** — a scope, effort,
  and dependency decision that a human must own. Auto-pivoting a five-times-blocked task into that rework
  without authorization is precisely the wrong move.
- (c) is the clean terminal outcome if the human declines (d). The task description explicitly permits a
  rigorous negative result.

This is *not* "we are stuck, help." It is: **"the path is identified (birelational, Došen 1985); the
decision is whether to fund a large architecture pivot + possible 509 rework, or bank the rigorous negative
result."**

---

## 4. HONEST FINDING (deliverable 4)

No false optimism. The impasse *within the current architecture* is real and is now corroborated from
outside: (i) Pacheco 2024 states there are **no Kripke semantics for CKB in the literature** and that CKB's
own canonical model needs negation-completeness; (ii) the two-sided symmetric-tail design is the single
canonical-model shape structurally incompatible with prime theories. But this is **not** "no technique
exists": the logic **is** complete (Došen 1985, intuitionistic S5, birelational), just via a **different
model** than CSLib built. So the correct statement is: *the technique that works requires abandoning the
current architecture* — a human-authorization-level decision, hence `escalate`, with a documented negative
result as the fallback. Report 02's ~85–90% "claim is TRUE" stands and is reinforced (Došen proves the
intuitionistic-S5 analogue complete); what is blocked is provability *in this architecture*, not the truth
of completeness.

---

## 5. Concrete next steps (for whichever branch the human picks)

**If (d) birelational pivot is authorized** — new/replanned task, phased:
1. Obtain Došen 1985 + Božić–Došen 1984 (add BibKeys `Dosen1985`, `BozicDosen1984`, `Ewald1986`,
   `AlechinaMendlerdePaivaRitter2001` to `references.bib`); extract the exact IS5 axiom-to-frame-condition
   correspondence and the canonical-frame symmetry verification (confirm it is negation-completeness-free).
2. Match CSLib's CS5 axioms to Došen's IS5; decide whether to invoke Pacheco's CKB=IKB collapse or re-derive
   it for the S5 diamond.
3. Redesign the canonical world/relation as birelational (one-sided `R` + F1/F2 + IS5 correspondence),
   reusing `CKForces`, `box_refuting_theory`, `quasi_prime_exclusion`; re-prove soundness for the new frame
   class (touches task-509 `cs5FC''`); prove box-backward as the plain one-sided prime lemma.
4. Truth lemma + completeness as in report 01 Phase 5, over the new model.

**If (c) negative result is chosen** — land a mechanized *architectural* obstruction: formalize that
`cs5Tail`'s back-inclusion over an arbitrary quasi-prime head is equivalent to negation-completeness
(exhibit the quasi-prime, non-negation-complete head where it fails, generalizing `CS5BoxGapWorld`), and
document that both the direct symmetric-tail route and the doubled-atom route reduce to it. Mark CS5
completeness `[BLOCKED]` *by architecture* (not by incompleteness of the logic), citing Pacheco 2024,
Došen 1985, and the three landed CSLib obstruction lemmas (509 + handoffs 04/05).

**Do NOT** spend further dispatches on (a) or (b).

---

## Adversarial self-verification
- *"Birelational avoids negation-completeness"* — grounded: all intuitionistic completeness (Došen, Simpson,
  Božić–Došen) uses prime theories, which are by construction not negation-complete; Došen 1985 proves IS5
  complete this way. Residual risk flagged: I did not read Došen's exact symmetry-condition verification
  line-by-line (paywalled; corpus has Simpson, not Došen). Confidence the technique is negation-completeness-
  free: high (~90%); confidence it adapts cleanly to CSLib's *constructive diamond* at S5 strength: medium
  (~65%), because Pacheco's collapse is proved for KB not S5. This is exactly why it is a human-authorized
  pivot with residual risk, not an autonomous "implement".
- *"(a)/(b) are no-go"* — grounded in mechanized prior findings (`cs5Combined_symmetric_tail_box_gap`,
  `cs5FC''_hub_forces_spoke_connectivity`), not opinion.
- *"Pacheco = no CKB semantics + KB-only collapse"* — verified by direct PDF fetch of arXiv:2408.16428.
- Zero-debt: no `sorry`/axiom proposed; the fallback (c) is a *proved* obstruction, not a placeholder.
- Reuse-first: the pivot maximally reuses `CKForces`, `box_refuting_theory`, `quasi_prime_exclusion`,
  `Segment`/`CKExtension` plumbing; only the world/relation/frame-condition layer is new.
