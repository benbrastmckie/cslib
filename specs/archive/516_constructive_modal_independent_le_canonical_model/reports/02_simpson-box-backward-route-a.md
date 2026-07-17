# Research Report 02 — Task 516: Simpson's Box-Backward and the Route A Portability Verdict

**Task type**: cslib (Lean 4, foundational de-risking). **Dispatch**: orchestrator,
session `sess_1784105723_fac1a0`, `orchestrator_mode=true`, `--lit` active. **No production
Lean written** (Simpson/Marin corpus chunks mined verbatim + source inspection of landed
CSLib guardrail declarations). **Scope**: settle whether Simpson 1994's IS5 canonical-model
completeness contains a symmetric box-backward argument that is *faithfully portable* onto
CSLib's `CKSegment`/quasi-prime infrastructure (Route A), or whether it structurally relies on
something CSLib lacks — making Route B (Marin fully-labelled) the only faithful port.

---

## PORTABILITY VERDICT (lead) — `next_action_hint = escalate`

**Simpson's symmetric box-backward for IS5 is NOT faithfully portable onto CSLib's
prime-theory infrastructure — because Simpson himself does not carry it out in prime-theory
form.** His §3.3 birelational prime-theory canonical model is, by his own words, an *outline*
(chunk `0221`: "We give an **outline** of the argument … For a fully detailed [treatment see]
Chapter 8"), and for the *symmetric* extensions (IS5) he explicitly **defers the frame-condition
verification** to Fischer Servi [24] and "the other cases are **straightforward**" (chunk
`0245`–`0246`). Where Simpson gives a *rigorous, intuitionistically-acceptable* IS5 completeness
(Chapters 7–8), he has **abandoned the prime-theory model** in favour of **labelled "T-prime
bounded contexts"** whose accessibility relation is an explicit **graph completed to be
symmetric** (`T-Comp`, Lemma 8.2.5, chunk `0843`), with box-backward discharged by a **bounded
canonical model lemma** over labelled membership `y:B ∈ A` (Lemma 8.2.6, chunks `0849`–`0852`) —
i.e. **Route B technology** (Marin explicitly extends this labelled line, Marin chunk `0004`).

The single classical step Simpson uses in the rigorous route is **decidability of the
consequence relation applied "by case analysis" and "by contraposition"** in the *bounded prime
lemma* (chunk `0907`–`0908`). That step is available in Lean for free (`Classical.em`,
`by_contra`) and is **not** the blocker. The blocker is structural: **prime (non-maximal)
theories lack the negation-completeness the symmetric box-backward needs**, forcing the
witness construction to enlarge the head `H → H'` and build `(H', T)` as a **simultaneous prime
pair** — precisely the construction CSLib's task-512 Phase 8-10 found *unstable* under the
library's single-formula primeness engine, and precisely the construction Simpson **sidesteps by
switching to labels**.

**Confidence:**
- **~95%** that Simpson provides **no** portable prime-theory symmetric box-backward for IS5
  (grounded in verbatim chunks `0221`, `0245`–`0246`, `0907`–`0908`, `0839`–`0852`).
- **~15–20%** that Route A (Simpson-faithful consistent-prime, ~600–1000 lines, CSLib reuse) is
  closable **as framed**. It is **not "plan-ready."** Its hard core is the *pair-primeness-
  stability* problem, which is **open research** that Simpson himself did not solve in
  prime-theory form.
- **~high** that Route B (fully-labelled, Marin 2021) is mathematically sound and is the
  faithful descendant of Simpson's **own** rigorous IS5 method — but with **~zero CSLib reuse**
  (~1500–2500 lines).

**The decision has shifted, not merely been reconfirmed.** Report 01 left Route A as the
"genuinely Simpson-faithful path … gated on an unclosed hard core." This report shows the
premise itself is weaker than hoped: **there is no Simpson prime-theory IS5 box-backward to be
faithful to.** Route A is a research gamble on solving pair-primeness; Route B is a transcription
of Simpson's actual method. This is a **human funding decision** → `escalate`.

---

## Deliverable 1 — Simpson's box-backward, verbatim (with exact chunks)

### 1a. The canonical model (§3.3) — base logic IK only, and by admission an *outline*

Chunk `0221` (opening of §3.3, "The soundness of IK …"):
> "…ness can be established by a canonical model construction. We give an **outline** of the
> argument, which we shall need to refer to in Chapter 8. For a fully detailed [treatment …]"

Chunk `0223` — the canonical birelation model `B = (W, ≤, R, V)`:
> `W = {X | X is prime}`, `X ≤ X' iff X ⊆ X'`,
> `X R Y iff {◇A | A ∈ Y} ⊆ X and {B | □B ∈ X} ⊆ Y`, `V(X) = {a | a ∈ X}`.

Two facts pinned here (and re-confirmed against report 01):
1. `≤` **is** `⊆` (there is no independent `≤` — report 01's decisive finding, restated).
2. `R` is **already two-sided**: a diamond clause `Y ⊆ diaInv X` (`{◇A|A∈Y}⊆X`) **and** a box
   clause `boxInv X ⊆ Y` (`{B|□B∈X}⊆Y`). This is *exactly* CSLib's `cs5TwoSidedR`
   (`CS5Canonical.lean:511`), and via `cs5_boxInv_subset_iff` (`CS5.lean:589`) the diamond
   clause `Y ⊆ diaInv X` **is provably the symmetric back-clause** `boxInv Y ⊆ X`.

### 1b. The accessibility relation and its symmetry — algebraic, and *free*

Simpson's `R` is *not* a single box-tail; it is the two-sided relation. Its **symmetry for IS5
is algebraic** — a consequence of the IS5 axioms on deductively-closed prime theories, needing
**no** Lindenbaum, **no** pair, **no** maximality. From the axioms (chunk `0241`–`0243`:
`B = (◇□A ⊃ A) ∧ (A ⊃ □◇A)`):
- Box-clause of `YRX`: `□B ∈ Y ⟹[dia clause of XRY] ◇□B ∈ X ⟹[axiom ◇□B→B, closure] B ∈ X`.
- Dia-clause of `YRX`: `A ∈ X ⟹[axiom A→□◇A, closure] □◇A ∈ X ⟹[box clause of XRY] ◇A ∈ Y`.

This is CSLib's landed `cs5Tail_symm` (`CS5.lean:645`) — symmetry **is** free. **Symmetry was
never the gap.** The gap is the truth-lemma necessity (box-backward) case.

### 1c. The box-backward / necessity case — "using the prime lemma," and where the pair hides

Chunk `0228` — Lemma 3.3.3 (Canonical model / truth lemma):
> "`X ⊩ A` if and only if `A ∈ X`, … proved by induction on the structure of `A`, **using the
> prime lemma in the implication and necessity cases**."

The **necessity (⟹, contrapositive) case** is the box-backward: `□A ∉ X ⟹ ∃ X' ≥ X, ∃ Y,
X'RY, A ∉ Y`. Reconstructed from the definition, this needs `Y` with **all three** of
`boxInv X' ⊆ Y` (box clause), `Y ⊆ diaInv X'` (dia clause = symmetric back-clause), `A ∉ Y`,
`Y` prime. For the **base IK** the F2 verification (chunks `0224`–`0227`) shows the *pattern*: to
obtain `X'RY'` from `XRY` and `Y ≤ Y'` he **enlarges** `X` to `X' = X ∪ {◇A | A ∈ Y'}`, then
prime-extends — i.e. **the box-backward moves along `≤`, enlarging the head.**

### 1d. How he actually verifies IS5 — labelled bounded contexts (Chapters 7–8)

Chunk `0245`–`0246` (completeness for IT/IS4/**IS5**):
> "the completeness direction is proved by showing that the canonical model, defined
> **analogously** to that used in [IK] … [attributed to] **Fischer Servi [24]. The other cases
> are straightforward.** … the above completeness results are **not correspondence results**."

Chunk `0247`–`0249` — the *actual* extension frame conditions are **≤-mediated** ("R satisfies
the properties associated with S₁…Sₙ … **where w ≤ w'** …"), i.e. the F1/F2-style *incestuality*
conditions, **not** plain symmetry.

The **rigorous** IS5 proof is Chapter 8's **bounded canonical model** over **labelled**
structures, not prime theories:
- Chunk `0839`: "The bounded model will be constructed out of **T-prime bounded contexts**."
- Chunk `0846`–`0847`: worlds `W = the set of T-prime bounded contexts`; a context is a pair
  `(H, A)` where `H` is a **graph of labelled worlds with a visibility relation `R`** and `A` a
  set of **labelled formulas** `x:B`; `R_(H,A)(x,y) iff xRy in T-Comp(H)`.
- Chunk `0843` (Lemma 8.2.5): "`T-Comp(H)` is reflexive if … and is **symmetric** …" — **symmetry
  is graph completion**, applied to the visibility relation, *not* derived from theory membership.
- Chunk `0849`–`0852` (Lemma 8.2.6, **Bounded canonical model lemma** — the truth lemma):
  "by a **case analysis on the structure of `B`** … mimicked by the membership relation
  `y:B ∈ A`" — box-backward is **labelled membership + proof-search saturation**, not a
  prime-theory Lindenbaum.

**Answer to D1:** Simpson's *rigorous* IS5 box-backward uses a **single-step labelled relation**
whose symmetry is a **separately-applied graph completion** (`T-Comp`), with the witness world
delivered by a **bounded canonical model lemma over labelled contexts** and a **bounded prime
lemma** (chunk `0907`–`0908`). It is neither a prime-theory single-step-plus-post-hoc-frame-check
nor a prime-theory simultaneous pair-extension. The prime-theory version (§3.3) that *would*
port to CSLib is an **outline** that defers exactly this step.

---

## Deliverable 2 — The gap diagnosis: why CSLib's sequential Lindenbaum fails where Simpson "succeeds"

There are **three** distinct differences; only the third is the true, irreducible one.

**(i) Quasi-prime vs consistent-prime (real, but secondary).** CSLib's `quasi_prime_exclusion`
(`SegmentLindenbaum.lean:73`) yields **quasi-prime = possibly `univ` (`Ω`)** worlds; Simpson's
`W = {X | X prime}` are **consistent** primes. This is why `Ω` universally reachable breaks
`cs5Incest` in CSLib (task 512 Phase 5). *Fixable* by a consistency invariant — but it is not the
box-backward gap.

**(ii) Metatheory / decidability (a red herring for CSLib).** Simpson's box-backward uses
**decidability of ⊢ "by case analysis"** and completeness "from its **contrapositive**" (chunk
`0907`–`0908`). These are classical-flavoured **but at the meta level** (decidability of the
*object* consequence relation), not negation-completeness of object worlds. Lean supplies them
free via `Classical.em`/`by_contra`. **This is NOT the blocker.**

**(iii) Prime-not-maximal ⇒ the symmetric bound conflicts with keeping `A` out (THE gap).**
This is decidable independently of Simpson, and it is airtight. CSLib's guardrail
`cs5_symmetric_tail_box_gap` (`CS5.lean:712`, verified, no CS5 axiom) states:

> `QuasiPrime T`, `□(p ∨ □q) ∈ H`, `boxInv H ⊆ T`, `boxInv T ⊆ H`, `q ∉ H` ⟹ `p ∈ T`.

Proof (from source): `□(p∨□q)∈H ⟹ (p∨□q)∈boxInv H ⊆ T ⟹` (T prime) `p∈T` or `□q∈T`; the
latter gives `q∈boxInv T ⊆ H`, contradicting `q∉H`; so `p∈T`. Consequently, for the box-backward
of `p` at a **fixed** `H` with `□p∉H`, `□(p∨□q)∈H`, `q∉H`, **every symmetric-tail `T` contains
`p`** — no witness with `p∉T` exists.

Now trace Simpson's own bound onto this. The dia-clause bound `Y ⊆ diaInv H` **equals** `boxInv
Y ⊆ H` (`cs5_boxInv_subset_iff`, `CS5.lean:589`). So Simpson's Lindenbaum-with-bound is *forced*
to keep `boxInv Y ⊆ H` — the symmetric tail. With `boxInv H ⊆ Y` it must place `(p∨□q)∈Y`, hence
(Y prime) `p∈Y` or `□q∈Y`; `p∉Y` (goal) forces `□q∈Y`, and the bound `Y ⊆ diaInv H` gives
`◇□q∈H`, whence axiom `B (◇□q→q)` and closure give `q∈H` — contradicting `q∉H`. **The bounded
Lindenbaum cannot keep `p` out while staying inside the symmetric bound.** The only escape is to
**enlarge `H` to `H' ∋ q`** and build `(H', Y)` **simultaneously** — which enlarges `boxInv H'`
in turn (the "circularity" documented verbatim at `CS5.lean:700-710`).

**Why Simpson escapes and CSLib cannot (named precisely):** in Simpson's *rigorous* route the
worlds are **labels**, not prime theories. A fresh label discharges the ≤-mediated existential
frame condition (`∃x'. x ≤ x' ∧ x'Rz`, Marin chunk `0004`, condition (3)) **by construction**;
there is no prime theory whose primeness must remain stable while a *second* theory is grown
against it. **The exact difference is: Simpson's box-backward never requires two prime theories to
satisfy cross-membership invariants simultaneously — because his rigorous worlds are not prime
theories at all.** CSLib's sequential Lindenbaum grows one prime theory with the *other component
fixed*, and the cross-invariant `boxInv X ⊆ Y` is **not stable** under the single-formula
deductive-closure engine (`probes/cs5-pair-primeness.lean`, task 512 Phase 8-10).

**Answer to D2:** The failure is **not** quasi-prime-vs-consistent-prime (fixable), **not**
metatheory (Lean has classical logic). It is that **the symmetric back-clause is a *bound* on the
Lindenbaum that is jointly unsatisfiable with `A ∉ Y` over prime-not-maximal theories**, forcing a
**simultaneous prime pair** whose primeness is not stable — and Simpson avoids this only by
**not using prime theories** in his rigorous IS5 proof.

---

## Deliverable 3 — Portability verdict against each mechanized guardrail

Can Simpson's construction be transcribed onto `CKSegment`/quasi-prime? **The `§3.3` prime-theory
version cannot be, because it is an outline that stops exactly at the gap; the rigorous version is
not a `CKSegment`/quasi-prime construction at all.** Per guardrail:

| Guardrail (loc) | Does Simpson's route trip it? | Why |
|---|---|---|
| **`cs5Incest_forces_symm`** (`CS5Canonical.lean:643`) | **No — irrelevant to Simpson.** | Simpson never uses the ≤-mediated `cs5Incest` condition. His `R` is the **two-sided** relation with **algebraic** symmetry (`cs5Tail_symm`). The guardrail governs the `≤`-witness collapse and simply does not apply to a route that doesn't route symmetry through `≤`. |
| **`cs5TwoSidedR_iff_cs5Tail`** (`CS5Canonical.lean:511`) | **No — consistent with Simpson.** | It *confirms* Simpson's two-sided `R` **is** the symmetric tail `cs5Tail` over quasi-prime worlds. Far from blocking, it is the CSLib-side statement of §1b. Report 01 read it as "restores no independent info"; correct — and harmless, because Simpson's symmetry is algebraic, not informational. |
| **`cs5_symmetric_tail_box_gap`** (`CS5.lean:712`) | **YES — this is the wall.** | Simpson's §3.3 bounded Lindenbaum, ported faithfully, keeps `boxInv Y ⊆ H` (= the dia-clause bound, via `cs5_boxInv_subset_iff`), so it lands **inside** this lemma's hypotheses and **cannot** keep `p ∉ Y` (D2). Simpson's rigorous route trips it too — and evades it **only** by leaving prime theories for labels (graph `T-Comp` symmetry + fresh-label existentials). There is no membership-model route that both satisfies the symmetric bound and refutes `p`. |
| **Atom-sum result** (task 512 report 01, `box-backward-atom-sum`) | **No new escape.** | The atom-sum bound is the finite-support accounting under which the *sequential* refuter must place `p`; Simpson's decidability-by-case-analysis (chunk `0908`) is a meta-level `Classical.em`, not a way to *lower* the atom-sum obligation. It changes provability bookkeeping, not the structural `p ∈ T` forcing. |

**Answer to D3:** A faithful transcription **must** switch quasi-prime → consistent-prime **and**
add a **simultaneous pair-Lindenbaum with a stable primeness invariant** — the latter being the
**open** task-512 Phase 8-10 problem. It **trips `cs5_symmetric_tail_box_gap`** unless that pair
construction is solved. The other three guardrails are neutral or confirmatory, not obstacles.
**No published Simpson lemma discharges the tripped guardrail in prime-theory form.**

---

## Deliverable 4 — Route A vs Route B (sharpened)

**Route A (Simpson-faithful consistent-prime, ~600–1000 lines, CSLib reuse): NOT plan-ready;
~15–20% closable as framed.** The estimate collapses because the "Simpson-faithful" object it
promises to transcribe **does not exist in Simpson in prime-theory form**. What Route A actually
needs is a **new theorem** — a stable simultaneous prime-pair Lindenbaum — that:
- Simpson **did not prove** (he switched to labels: chunks `0839`–`0852`);
- task 512 Phase 8-10 **attempted and found unstable** (`probes/cs5-pair-primeness.lean`);
- trips `cs5_symmetric_tail_box_gap` unless solved.
This is **open mathematical research**, not transcription. If pursued anyway, a *speculative*
phase structure for a planner would be:
1. `ConsistentQuasiPrime` predicate (`QuasiPrime ∧ ⊥ ∉ S`) + basic API — reuses
   `quasi_prime_exclusion`, `quasi_head_realization` (`SegmentLindenbaum.lean:73,251`). *Tractable.*
2. Bounded (dia-clause-respecting) single-theory Lindenbaum — reuses `box_refuting_theory`,
   `dia_refuting_theory` (`:177,203`). *Tractable but partial* — hits the gap alone.
3. **Simultaneous pair Zorn with a stable cross-primeness invariant.** *THE unresolved core —
   this is the escalation gate, not a plannable phase.*
4–5. Truth lemma + completeness assembly over the new world type, parallel/isolated from CK/CT/CS4
   (do **not** generalize the shared `QuasiPrime`/`Preorder`). *Contingent on Phase 3.*
**Do not dispatch Route A as a standard plan**; Phase 3 is a research problem with no known
sorry-free discharge and a mechanized guardrail (`cs5_symmetric_tail_box_gap`) standing against
the naive attempts.

**Route B (Marin fully-labelled, ~1500–2500 lines, ~zero reuse): the faithful port of Simpson's
own IS5 method.** Marin (chunk `0001`, `0004`) **explicitly extends Simpson's labelled line**
[Sim94], adding an explicit `≤` relational atom so the ≤-mediated frame conditions (3) become
**inference rules with fresh labels** — the freshness *is* the pair construction, discharged
structurally, sidestepping prime-theory Lindenbaum entirely. This is exactly the technology
Simpson's Chapters 7–8 use for rigorous IS5. Sound, published, mechanization-shaped; the cost is a
from-scratch reformalization (labelled sequents, `≤`/`R` atoms, cut-elimination or saturation,
countermodel extraction) with essentially no reuse of `CKSegment`/`CKForces`.

**Recommendation:** `escalate`. The honest, corrected framing for the human funding decision:
- **Route A is a research gamble** on solving pair-primeness-stability — a problem Simpson did
  **not** solve in prime form and CSLib has already found unstable. Not ~600–1000 lines of
  transcription; an open problem plus scaffolding.
- **Route B is transcription** of Simpson's actual rigorous IS5 method (= Marin), at ~zero reuse.
If IS5 completeness is genuinely wanted, **Route B is the faithful path.** Route A should be
funded **only** as an explicit research bet on the pair-primeness core, not as a Simpson port.

---

## The single most important thing (as the dispatch demanded)

The dispatch asked me to surface any *classical* step in Simpson's symmetric box-backward that
CSLib's constructive setting forbids. **Finding: the classical step is decidability-of-⊢
"by case analysis / by contraposition" in the bounded prime lemma (chunk `0907`–`0908`) — and it
is NOT forbidden in CSLib (Lean has `Classical.em`).** The real obstruction is *not* a forbidden
classical step; it is that **prime (non-maximal) theories structurally lack negation-completeness**,
so the symmetric back-clause becomes a *bound* that is jointly unsatisfiable with refuting the box
subject over a fixed head — provably, via `cs5_symmetric_tail_box_gap`. Simpson **knew this**: it
is *why* his rigorous IS5 completeness uses labelled bounded contexts (Chapters 7–8) rather than
the §3.3 prime-theory outline. **There is no Simpson prime-theory symmetric box-backward to port;
the faithful port of Simpson's IS5 proof *is* Route B.**

---

## Adversarial self-verification

- *"§3.3 is only an outline"* — verbatim chunk `0221` ("We give an **outline** … For a fully
  detailed [treatment see] Chapter 8"). Not an inference.
- *"IS5 extensions deferred"* — verbatim chunk `0245`–`0246` ("defined **analogously** … Fischer
  Servi [24]. The other cases are **straightforward** … **not correspondence results**").
- *"Rigorous IS5 = labelled"* — chunks `0839`, `0843` (`T-Comp` symmetric), `0846`–`0852`
  (labelled `(H,A)`, membership `y:B∈A`), `0907`–`0908` (bounded prime + bounded canonical model
  lemmas, decidability by case analysis / contraposition). Marin chunk `0004` confirms this
  labelled line is what she extends.
- *"The gap trips `cs5_symmetric_tail_box_gap`"* — I re-derived the joint-unsatisfiability
  **independently** (the `◇□q→q` B-axiom step) and then confirmed it against the **landed source
  proof** (`CS5.lean:712-725`, read directly) and the source comment `CS5.lean:700-710` naming
  "simultaneous maximal pair … the real open problem." Two independent confirmations.
- *"Symmetry is not the gap"* — algebraic derivation (§1b) matches landed `cs5Tail_symm`
  (`CS5.lean:645`); symmetry is free, so any pessimism located at symmetry would be wrong.
  Located instead at box-backward, which is the correct locus.
- *"Not repeating reports 05/06 over-optimism"* — I actively steelmanned Route A (bounded
  Lindenbaum + Lean's classical logic) and it *still* trips the mechanized guardrail; and I
  checked whether the classical step was the blocker (it is not) rather than assuming it.
  The negative verdict is grounded in a *mechanized* lemma plus verbatim admissions by Simpson,
  not in a literature inference or a hunch.
- *Residual uncertainty (the ~15–20%)*: `cs5_symmetric_tail_box_gap` blocks a **fixed-head**
  witness and the naive sequential pair; it does **not** prove **every** simultaneous pair
  construction impossible. A genuinely new pair-Zorn or a bounded construction with a cleverer
  invariant could conceivably work — that is the open research residue, and it is why Route A is
  a *gamble*, not *dead*. I am **not** claiming CS5 completeness is unreachable via primes; I am
  claiming Simpson does not hand us the argument and the known attempts trip a guardrail.
- **Zero-debt / reuse-first:** no `sorry`/axiom proposed. BibKeys grounded: `Simpson1994`,
  `MarinMoralesStrassburger2021` (both in corpus, chunks cited by id).

## One-line answer

Simpson's rigorous IS5 box-backward is **labelled** (Chapters 7–8: `T-Comp` graph symmetry +
bounded canonical model lemma over labelled contexts, decidability by case-analysis — chunks
`0839`–`0852`, `0907`–`0908`), and his §3.3 **prime-theory** model is an *outline* that defers
the symmetric case (chunks `0221`, `0245`–`0246`); the prime-theory box-backward provably trips
`cs5_symmetric_tail_box_gap` (`CS5.lean:712`) because the symmetric back-clause is a bound jointly
unsatisfiable with refuting the box subject over non-maximal primes — so **Route A is a research
gamble on the open simultaneous-pair-primeness problem, and Route B (Marin fully-labelled) is the
faithful port of Simpson's own IS5 method** → `escalate`.
