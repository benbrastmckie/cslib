# Task 517 — Teammate B Findings: Alternatives and Prior Art

**Angle**: Alternative routes and prior art (explicitly NOT Simpson Ch.7-8 = Teammate A).
**Reference grounding tier**: 1 (literature-backed). BibKeys verified against `references.bib` — see
§BibKey Verification.
**Directive honoured**: "the mathematically correct way to proceed, cutting no corners."

---

## Key Findings

### F1. The `cs5FC''` target demands *plain* symmetry outright — so `cs5Tail`-shape is forced on EVERY route, and cannot by itself close any track

`cs5FC''` (`CKExtension.lean:184`) is a five-clause conjunction whose **third conjunct is literally
plain symmetry**:

```lean
def cs5FC'' {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u t}, r w u → r u t → r w t)
    ∧ (∀ {w u}, r w u → r u w)          -- ← PLAIN symmetry, not ≤-mediated
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t)
```

Any completeness route must, by contraposition, exhibit a countermodel **whose relation satisfies
that clause**. Every truth-lemma design additionally needs box-forward
(`r w u → boxInv (head w) ⊆ head u`) and monotone heads. Plain symmetry + box-forward + monotonicity
gives `boxInv (head u) ⊆ head w` **immediately** — you do not even need `cs5Incest_forces_symm` to
get there; it falls out of conjunct 3 in one step.

**Consequence — and this is the load-bearing point of this report:** reaching `cs5Tail`-shape is
*unavoidable* and therefore *not evidence against any particular route*. As I received it, the A3
verdict closing Track B runs:

> Pacheco's canonical CKB-relation, once T-extended for CS5, satisfies `cs5Incest_forces_symm`'s
> hypotheses → `cs5Tail`-shape → `cs5_symmetric_tail_box_gap`.

**That chain, as summarised to me, proves too much.** Track C must also deliver a plainly-symmetric
`cs5FC''`-frame with box-forward and monotone heads, so Track C's countermodel *also* lands in
`cs5Tail`-shape and *also* meets `cs5_symmetric_tail_box_gap`'s hypotheses. If arriving at
`cs5Tail`-shape closed a track, it would close Track C too — and with it the whole task. By reductio,
it closes neither. **I recommend the A3 verdict be re-examined before Track B stays closed.** (I could
not read A3 directly — it is being written concurrently — so this challenges the summary I was given,
not necessarily A3's full argument. See §Adversarial Self-Verification, challenge C1.)

### F2. `cs5_symmetric_tail_box_gap` is not an impossibility result — it is a *specification* of the fix, and Pacheco has already executed that fix

`cs5_symmetric_tail_box_gap` (`CS5.lean:712`) says: given `□(p ∨ □q) ∈ H`, `boxInv H ⊆ T`,
`boxInv T ⊆ H`, `T` quasi-prime, and `q ∉ H`, then `p ∈ T`. Read contrapositively it says exactly:

> a symmetric tail member omitting `p` exists **only at a head containing `q`**.

It refutes only the *sequential/naive* box-backward step (witness constructed at `H` itself). It says
nothing against a box-backward step that first moves to `H' ⊋ H` with `q ∈ H'`. CSLib's own docstring
already recognises this (`CS5.lean:704-706`): "`H'` and `T` must be built as a **simultaneous maximal
pair**, not sequentially (Phases 8-10)."

The semantics agree that no stronger reading is available. `□(p ∨ □q) → (□p ∨ q)` is **not valid** over
`cs5FC''`-frames: take `w ⊮ q`, `w' > w` with `w' ⊩ q`, and `u` with `r w' u`, `u ⊩ □q`, `u ⊮ p`. Plain
symmetry gives `r u w'`, so `u ⊩ □q` only forces `q` at `w'` — which is permitted. `w ⊮ □p` via
`w ≤ w' R u`. So the gap lemma is *not* latent evidence that the target is false; the target survives
this test.

**Pacheco2024 Lemma 18 performs precisely the simultaneous-maximal-pair construction** that
`CS5.lean:706` calls "the real open problem" (chunk `213bb5de73fe3e7a`, verbatim):

> Consider now the pairs of sets of formulas ⟨X, Y⟩ such that Υ ⊆ X, Φ ⊆ Y, Γ ⊆ Y, Y□ ⊆ X, Y ⊆ X◇,
> φ ∉ X ∪ Y, and ⊥ ∉ X ∪ Y. Consider the ordering ≤ where ⟨X,Y⟩ ≤ ⟨X′,Y′⟩ iff X ⊆ X′ and Y ⊆ Y′. …
> So, by Zorn's Lemma, there is a pair ⟨Σ, ∆⟩ which is maximal with respect to ≤.
>
> **Lemma 18.** Let φ be a formula and Γ be a CKB-theory. Then □φ ∉ Γ implies that there are
> CKB-theories ∆ and Σ such that Γ ⊑c ∆ ∼c Σ and φ ∉ Σ.

Note `Γ ⊑c ∆` — the head is allowed to *grow*. This is a **single Zorn application on the product
order over pairs**, with an **excluded formula φ** in the constraint family. Its conclusion is
*consistent* with `cs5_symmetric_tail_box_gap`: instantiating the gap lemma at `H := ∆`, `T := Σ`,
`p := φ` yields `q ∈ ∆` — i.e. the gap lemma simply *forces* `∆ ⊋ Γ`, which is what Lemma 18 delivers.
**No contradiction.** Pacheco's construction is ~1 page and lives entirely at the theory level.

### F3. Pacheco2024's primality argument is genuinely defective — but the defect is confined, and one half of it is trivially repairable

Applying the defect bar (4 elements):

1. **Locus / counterexample.** Pacheco2024 Lemma 16 (chunk `ec3a8bddd907f0c4`), verbatim:
   > let Θ be the maximal … set of formulas such that: Γ ⊆ Θ, Θ□ ⊆ Σ, Σ ⊆ Θ◇, and ⊥ ∉ Θ. Suppose
   > φ ∨ ψ ∈ Θ. Then if φ ∉ Θ and ψ ∉ Θ, we would have that **¬φ ∈ Θ and ¬ψ ∈ Θ**.

   The step `φ ∉ Θ ⟹ ¬φ ∈ Θ` is invalid. Θ is maximal with respect to a constraint family whose
   binding caps include `Θ□ ⊆ Σ`, not consistency alone — so `φ ∉ Θ` means adding φ breaks *some*
   constraint, which need not be consistency. Independently, the step is self-defeating: if it were
   sound, Θ would be negation-complete, hence classical, and `⊑c` (= ⊆) would collapse the
   intuitionistic order — proving CKB classical. This is exactly the failure mode named in my
   briefing ("prime/quasi-prime non-maximal theories lack negation-completeness").
2. **Current behaviour.** The argument concludes Θ is a CKB-theory (prime). Lemma 18 then defers to
   it ("As in the proof of Lemma 16, if φ ∨ ψ ∈ Σ then φ ∈ Σ or ψ ∈ Σ").
3. **Required behaviour.** Primality must come from an excluded-formula prime-extension (disjunction
   property relative to the excluded φ), never from negation-completeness.
4. **Isolation.** The defect is confined to the primality sub-step. Lemma 15 (symmetry of `∼c` from
   `B◇`), the Υ/Φ closure computations, and the Zorn setup are unaffected.

**The repair, worked out:** in Lemma 18's constraint family, growing `X` can only ever break `φ ∉ X`
and `⊥ ∉ X` — the clauses `Y□ ⊆ X` and `Y ⊆ X◇` are *monotone in X* and are only helped by growth.
So maximality of `Σ` is effectively maximality subject to "avoid φ", and the standard argument runs
clean:

> `ψ₁ ∉ Σ ⟹ Σ, ψ₁ ⊢ φ`; likewise `Σ, ψ₂ ⊢ φ`; with `ψ₁ ∨ ψ₂ ∈ Σ`, ∨-elimination gives `Σ ⊢ φ`,
> contradicting `φ ∉ Σ`.

**Σ-primality is therefore repairable and easy.** ∆-primality is *not* symmetric to this: growing `Y`
breaks `Y□ ⊆ X` (**antitone** — a larger ∆ has a larger `∆□`), so the ∨-elimination argument does not
close. **∆-primality under the two-sided box cap is the genuine open crux of the Pacheco route** — and
it is the same mathematical obstruction the whole task keeps hitting, now isolated to a single,
sharply-stated sub-lemma rather than diffused across a proof architecture.

### F4. MarinMoralesStrassburger2021 is a DEAD END for this task — `labIK≤` never proves semantic completeness, it *cites* it

This is a decisive negative and it should stop any plan that budgets for mechanising `labIK≤`.

MMS Theorem 3.3 (chunk `e01d1400e172e158`, verbatim):

> **Theorem 3.3.** For any formula A, the following are equivalent. 1. A is a theorem of IK. 2. A is
> provable in labIK≤ + cut. 3. A is provable in labIK≤. 4. A is valid in every birelational frame.
> **The equivalence of 1 and 4 has already been stated in Theorem 2.5 [Ser84, PS86].** The implication
> 1 ⟹ 2 is shown in Section 4, the implication 2 ⟹ 3 is shown in Section 6, and finally, the
> implication 3 ⟹ 4 is shown in Section 5.

And Theorem 2.5 itself (chunk `ec2ca0b005ed5f10`):

> **Theorem 2.5 ([Ser84, PS86]).** A formula A is a theorem of IK if and only if A is valid in every
> bi-relational frame.

MMS contribute **1 ⟹ 2 ⟹ 3 ⟹ 4** (derivability, cut-elimination, soundness). The direction task 517
needs — **4 ⟹ 1, semantic completeness** — is *imported wholesale*. The same holds for the extensions:
Theorem 7.2's proof (chunk `0720d48db282bd09`) ends "The proof is completed by **appealing to Theorem
7.1 used as 4 ⟹ 1** to close the equivalence", and Theorem 7.1 is itself `([PS86])`. Mechanising
`labIK≤` would deliver a cut-free labelled calculus and **zero** progress toward
`CKValidFC cs5FC'' φ → Derivable CS5ModalAxiom φ`.

**What MMS *is* good for** (and it is real): grounding CSLib's `cs5Incest`. MMS Theorem 7.1 ([PS86],
chunk `0e9fa437c86470d1`) gives the intuitionistic *klmn*-incestuality condition for
`◇ᵏ□ˡA ⊃ □ᵐ◇ⁿA`. Instantiating at B (`k=l=0, m=n=1`, i.e. `A ⊃ □◇A`) yields "`wRv → ∃u′. w ≤ u′ ∧ vRu′`"
— which is exactly `cs5Incest` (`CS5Canonical.lean:234-235`), up to relabelling. So `cs5Incest` is the
correct, literature-sanctioned intuitionistic condition for B, and `cs5Incest_forces_symm` is a
*genuine mechanised negative result about the ≤ = theory-inclusion design*: the ≤-mediation that makes
the condition non-naive in MMS buys nothing once ≤ is head-inclusion, because `boxInv` is monotone.

MMS Remark 7.3 (chunk `0720d48db282bd09`) is the cited illustration that naive conditions are
"problematic": `◇(□(a∨b) ∧ ◇a) ∧ ◇(□(a∨b) ∧ ◇b) ⊃ ◇(◇a ∧ ◇b)` is **not** a theorem of IK+g1111 but
**becomes provable** if the naive directedness condition is added. **I checked whether this transfers
to naive symmetry and it does not** — see F5; Pacheco proves completeness w.r.t. *plainly symmetric*
models. So Remark 7.3 is **not** grounds to declare `cs5FC''` the wrong target.

### F5. Plain symmetry is NOT a wrong target: Pacheco's CKB-models use plain symmetry and are proved complete

I specifically tested the hypothesis "`cs5FC''` is unachievable because naive symmetry validates more
than CS5 proves." **It is false.** Pacheco2024 (chunk `8715c61b7b63ae1b`, verbatim):

> M is a CKB-model iff R is **symmetric**, forward confluent, and backward confluent

and Theorem 13 (chunk `14317e25e9b88a21`) proves `CKB ⊢ φ ⟺ IKB ⊢ φ ⟺ CKB ⊨ φ ⟺ IKB ⊨ φ` over exactly
those plainly-symmetric models. So plain symmetry is a *sound and complete* frame condition for the
B-fragment. `cs5FC''` is not disqualified. (This also independently corroborates F1's reductio.)

### F6. No mechanisation of IS5/CS5 Kripke completeness exists in ANY proof assistant — task 517 would be a world first

I searched Lean 4/3, Coq/Rocq, Agda, Isabelle. Three candidates, all eliminated:

| Artifact | URL | Verdict |
|---|---|---|
| **de Groot–Shillito–Clouston**, LICS 2025 — the state of the art, *fully mechanised in Rocq* | [arXiv:2408.00262](https://arxiv.org/abs/2408.00262) · repo [github.com/ianshil/CK](https://github.com/ianshil/CK) · docs [ianshil.github.io/CK/toc.html](https://ianshil.github.io/CK/toc.html) | Covers **only the diamond axis** CK→IK (N◇, C◇, I◇□). `pdftotext` over the full LICS preprint returns **zero** matches for `symmetr`, `S5`, `IS5`, `CS5`, `euclid`. No B, no T, no 4, no 5. |
| **Ayertienna/IS5** — Coq, "Intuitionistic S5 logic formalization" (the Galmiche/Salhi + Murphy-Crary-Harper-Pfenning line) | [github.com/Ayertienna/IS5](https://github.com/Ayertienna/IS5) | Proof-**term** work: `Labeled/`, `LabelFree/`, `LanguagesEquivalence/`, `Termination/`. Language equivalence and normalisation. **No Kripke semantics, no canonical model, no completeness.** |
| **FormalizedFormalLogic** — Lean 4 | [github.com/FormalizedFormalLogic/book](https://github.com/FormalizedFormalLogic/book) | **Classical** modal logic (Kripke soundness/completeness, GL) + superintuitionistic propositional. **No intuitionistic/constructive modal logic.** |

**The dGSC architecture is worth more to CSLib than its results.** Its canonical worlds are
*segments* — Definition IV.4, verbatim:

> A **segment** is a pair (Γ, U) where Γ is a prime theory and U is a set of prime theories such that:
> 1) if □φ ∈ Γ then φ ∈ ∆ for all ∆ ∈ U; 2) if ◇φ ∈ Γ then φ ∈ ∆ for some ∆ ∈ U.
> … (Γ, U) ⊑ (Γ′, U′) iff **Γ ⊆ Γ′**;  (Γ, U) R (Γ′, U′) iff **Γ′ ∈ U**

That is CSLib's `CKSegment` (head + tail), with **≤ = head-inclusion**, independently arrived at and
mechanised by the field's leading group. **CSLib's architecture is validated as state of the art** —
and, equally, dGSC's ≤ is head-inclusion too, so `cs5Incest_forces_symm` would bite their design as
hard as it bites CSLib's. They simply never attempt B. Their frame conditions are ≤-mediated in the
MMS style (e.g. `(I◇□-suff) ∀x,y,z s.t. xRy ≤ z (∃u ∈ X s.t. x ≤ uRz and ∀s ∈ X s.t. u ≤ s, ∃t ∈ X
s.t. sRt and z ≤ t)`), consistent with F4.

**Directive #4 answer:** dGSC's forward/backward confluence route (Pacheco's Theorem 11) does **not**
escape the guardrails — it never addresses symmetry at all. It is a *soundness* transfer (confluence ⟹
DP/FS/N valid), not a completeness mechanism.

### F7. The correct prior art for the simultaneous construction is Simpson Ch. **5**, not Ch. 6 or Ch. 7-8

Neither Track C (Ch. 6 tree surgery) nor Teammate A (Ch. 7-8) is looking at it. **Simpson1994 Lemma
5.3.1, "Prime lemma"** (chunk `b7b7543b80021f0d`, Chapter 5 Meta-logic, verbatim modulo OCR):

> **Lemma 5.3.1 (Prime lemma)** If (G,Γ) is a context and Γ ⊬𝒥 x:A then there is a 𝒥-prime context
> (H,∆) with (H,∆) ⊇ (G,Γ) such that ∆ ⊬𝒥 x:A.
>
> Proof. … Let 𝒱′ be some **coinfinite** subset of 𝒱 such that the underlying set of G is contained in
> W(𝒱′) … Consider the set C of all contexts (G′,Γ′) ⊇ (G,Γ) such that the underlying set of G′ is
> contained in W(𝒱′) and Γ′ ⊬𝒥 x:A. … by **Zorn's Lemma**, C has a maximal element (H,∆). We show that
> (H,∆) is 𝒥-prime … First, we show that **H is a classical model of 𝒥**.

This is the fully general simultaneous construction: Zorn over **contexts = (frame graph G, labelled
formulas Γ)** jointly, capped **only** by an excluded labelled formula `x:A`, with a **coinfinite
reserve of fresh world-variables** so maximality can always add worlds. Maximality delivers, in one
stroke, (i) primality, (ii) the diamond property, and (iii) `H ⊨ 𝒥` — and **𝒥 is an arbitrary geometric
theory**, so plain symmetry (`xRy ⊢ yRx`) is directly in scope. The graph growing under maximality is
what supplies `H' ⊋ H` and `T` *simultaneously*.

**This is the same idea as Pacheco Lemma 18, one level more general** (Pacheco: Zorn over pairs of
theories; Simpson: Zorn over graph + labelled formulas). Simpson's version has the decisive structural
advantage that **∆-primality is capped only by "avoid `x:A`"** — the two-sided box constraint that
kills Pacheco's ∆ is discharged by the *graph* `H` instead of by a cap on the formula set. That is the
precise mechanism of escape, and it is the answer to my directive #2.

**Caveat (honest):** Lemma 5.3.1 gives completeness of the *labelled* system w.r.t. 𝒥-frames. Reaching
CSLib's literal target still needs `labelled ⊢ φ → Derivable CS5ModalAxiom φ` — which *is* Ch. 6's
tree surgery, i.e. Track C's C5 crux. **Ch. 5 does not let us skip C5.** It does tell us the C5 crux is
the *only* thing standing between Track C and the target, and that the countermodel half is a solved,
transcribable ~1-page Zorn argument.

### F8. FischerServi1984 is NOT needed (directive #5)

MMS cite `[Ser84, PS86]` for IK's 1 ⟺ 4. But Pacheco2024 (chunk `14317e25e9b88a21`) states:

> Note that the equivalence between items (2) and (4) was already proved by **Simpson [Sim94]**.

i.e. `IKB ⊢ φ ⟺ IKB ⊨ φ` is **Simpson1994**, which is already in the corpus (1,091 chunks). Simpson's
thesis supersedes Fischer Servi's axiomatisation paper for our purposes.

**Do not ingest FischerServi1984.** If any ingestion were warranted it would be **PlotkinStirling1986**
("A framework for intuitionistic modal logic", in J.Y. Halpern (ed.), TARK 1986 — full reference at MMS
chunk `c02249653ff2f2fe`), which is the *actual* source of both Theorem 2.5 and Theorem 7.1 and is
neither in the corpus nor in the BibKey list. **But I do not recommend ingesting it either**: it is IK
(Fischer Servi diamond), not CK/CS5, and Simpson1994 covers the same ground with more detail.
`/literature` search target, only if F7's Ch.5 route needs the correspondence half independently:
`"Plotkin Stirling framework intuitionistic modal logic TARK 1986"`.

---

## Recommended Approach

**Primary recommendation: re-open Track B as Track B′ — but as a *scoped probe*, not a track switch.**

Track C (C5 `pathSpine` + commutation) should **continue as the primary route**. F7 shows C5 is
unavoidable for the literal target, and C1-C4 are landed sorry-free. Do not trade a 60%-landed track
for a speculative one.

However, F1-F3 identify a **specific, cheap, high-information probe** that Track C does not subsume:

> **Probe B′ (~1 phase, ~150-250 lines, self-contained):** mechanise Pacheco2024 Lemma 18's joint Zorn
> at the CS5 theory level. State it as
> `cs5_joint_prime_pair : □φ ∉ Γ → ∃ ∆ Σ, Γ ⊆ ∆ ∧ cs5TwoSidedR ∆ Σ ∧ φ ∉ Σ`, and attempt it via
> `zorn_subset` on the product order over pairs with constraint family
> `{Γ ⊆ Y, Y□ ⊆ X, Y ⊆ X◇, φ ∉ X ∪ Y, ⊥ ∉ X ∪ Y}`.

The probe's value is **decisive either way**:
- **Σ-primality** is already worked out in F3 and will land (monotone constraints ⟹ maximality reduces
  to "avoid φ" ⟹ standard ∨-elimination).
- **∆-primality under the antitone `∆□ ⊆ Σ` cap** is the crux. If it lands, CS5 completeness follows by
  Pacheco's route over **plain CS5-theories with no segments and no Ω at all** — because CS5 ⊢ ◇⊥ → ⊥
  is *already mechanised* (`cs5_dia_bot_imp_bot`, `CS5.lean`), which is exactly Pacheco's `N` axiom and
  is what licenses `Wc⊥ = ∅` (Pacheco chunk `01990319adea2569`). That would retire `CKSegment`,
  `CS5PrimeSegment`, `cs5PrimeMreach_ofHead_to_univ` and the entire Ω-exclusion apparatus for CS5.
- If ∆-primality **provably** fails, we have converted the task's diffuse obstruction into a single
  mechanised negative lemma — which is itself worth having, and which would *retroactively justify* the
  A3 verdict on sound grounds rather than the non-sequitur in F1.

**Secondary recommendation:** transcribe **Simpson Lemma 5.3.1** (F7) as the countermodel half of
Track C, in parallel with C5. It is ~1 page, uses `zorn_subset` over (graph, labelled-formula) pairs
with a coinfinite fresh-variable reserve, and is *independent of C5*. It removes the risk that C5 lands
and the countermodel half then turns out to be a second crux.

**Explicit guardrail statement (required by the task constraint):**

> **Does the proposed route trip `cs5Incest_forces_symm`? YES — and so does every other route,
> including Track C.** `cs5FC''` conjunct 3 *is* plain symmetry, so `boxInv (head u) ⊆ head w` is
> forced directly, without going through `cs5Incest` at all. Track B′ does not attempt to evade this
> and does not need to. It accepts `cs5Tail`-shape and defeats `cs5_symmetric_tail_box_gap` the only
> way the lemma permits — by placing the box-backward witness at `∆ ⊋ Γ` with `q ∈ ∆`, exactly as
> Lemma 18's `Γ ⊑c ∆` provides. The two statements are **consistent**, as verified in F2.

**Cost reality check (directive #6):**

| Route | Est. lines | Trips guardrails? | Avoids C5 crux? | P(success) |
|---|---|---|---|---|
| Track C, C5-C8 + assembly (baseline) | 1,500-3,000 | Yes (unavoidably) | — | **~45%** |
| **Probe B′** (Pacheco Lemma 18 joint Zorn) | 150-250 | Yes (unavoidably); consistent with them | **Yes, entirely** | **~35%** |
| Simpson Lemma 5.3.1 transcription | 250-400 | Yes (unavoidably) | No (complements C5) | **~65%** |
| Mechanise MMS `labIK≤` | 800-1,500 | n/a | No | **~0%** — delivers nothing (F4) |
| Port dGSC `github.com/ianshil/CK` | 1,000+ | n/a | No | **~0%** for CS5 — no B/T/4/5 (F6) |
| Ingest FischerServi1984 / PlotkinStirling1986 | — | n/a | No | **Not recommended** (F8) |

Probe B′ is the best expected-value-per-token item on the board: ~200 lines to resolve a question that
has closed one track and shaped two plans.

---

## Evidence-Examples

**Literature (chunk IDs, all in the local corpus):**

| Claim | BibKey | doc_id / chunk_id | File |
|---|---|---|---|
| MMS Thm 3.3: 1⟺4 imported from `[Ser84, PS86]` | MarinMoralesStrassburger2021 | `marinmoralesstrassburger_2021_…` / `e01d1400e172e158` | `chunk_0018.md` |
| MMS Thm 2.5 `([Ser84, PS86])` — the completeness they cite | MarinMoralesStrassburger2021 | `…` / `ec2ca0b005ed5f10` | `chunk_0009.md` |
| MMS Thm 7.1 `([PS86])` — intuitionistic *klmn*-incestuality (grounds `cs5Incest`) | MarinMoralesStrassburger2021 | `…` / `0e9fa437c86470d1` | `chunk_0043.md` |
| MMS Thm 7.2 — closes 4⟹1 "by appealing to Theorem 7.1"; Remark 7.3 naive-directedness counterexample | MarinMoralesStrassburger2021 | `…` / `33427e648b04b5ff`, `0720d48db282bd09` | `chunk_0044.md`, `chunk_0046.md` |
| `[PS86]` full reference (Plotkin & Stirling, TARK 1986) | — (no BibKey) | `…` / `c02249653ff2f2fe` | `chunk_0050.md` |
| Pacheco: "M is a CKB-model iff R is **symmetric**, forward confluent, and backward confluent" | Pacheco2024 | `pacheco_2024_…` / `8715c61b7b63ae1b` | `chunk_0008.md` |
| Pacheco Thm 13 + "equivalence between (2) and (4) was already proved by Simpson [Sim94]" | Pacheco2024 | `…` / `14317e25e9b88a21` | `chunk_0009.md` |
| Pacheco canonical model `Mc`, `Wc⊥ = ∅`, `Γ ∼c ∆ iff Γ□ ⊆ ∆ and ∆ ⊆ Γ◇`; Lemma 15 symmetry via `B◇` | Pacheco2024 | `…` / `01990319adea2569`, `459c68faae4c8a86` | `chunk_0010.md`, `chunk_0011.md` |
| **Pacheco Lemma 16 — the defective `¬φ ∈ Θ` primality step** (F3) | Pacheco2024 | `…` / `ec3a8bddd907f0c4` | `chunk_0012.md` |
| **Pacheco Lemma 18 — joint Zorn over pairs ⟨X,Y⟩ with excluded φ** (F2) | Pacheco2024 | `…` / `213bb5de73fe3e7a` | `chunk_0013.md` |
| **Simpson Lemma 5.3.1 "Prime lemma"** — Zorn over contexts (G,Γ), coinfinite fresh-variable reserve, `H ⊨ 𝒥` (F7) | Simpson1994 | `simpson_1994_…` / `b7b7543b80021f0d` | `chunk_0102.md` |

**Web / mechanisation URLs:**

- de Groot, Shillito, Clouston, *Semantical Analysis of Intuitionistic Modal Logics between CK and IK*,
  LICS 2025 — https://arxiv.org/abs/2408.00262 · preprint PDF
  https://www.ti.inf.uni-due.de/misc/lics2025/preprints/deGroot-Shillito-Clouston.pdf
- dGSC Rocq artifact — https://github.com/ianshil/CK · module index https://ianshil.github.io/CK/toc.html
  (module names `Complseg.*`, `ComplsegAB.*`, `ComplsegP.*`, `Complth.IK_th_completeness`,
  `GHC.Lindenbaum_lem`, `GHC.Lindenbaum_lem_pair`, `Kripke.correspondence`; requires Rocq 9.0.0.
  "segAB" = A-segments/B-segments of Def VI.3, **not** the B axiom.)
- Ayertienna, *IS5 — Intuitionistic S5 logic formalization* (Coq) — https://github.com/Ayertienna/IS5
- FormalizedFormalLogic (Lean 4) — https://github.com/FormalizedFormalLogic/book ·
  https://formalizedformallogic.github.io/Book/references.html

**Codebase evidence:**
- `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean:184` — `cs5FC''`, conjunct 3 = plain symmetry (F1)
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean:234-235` — `cs5Incest` = MMS/[PS86] g0011 condition (F4)
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean:643` — `cs5Incest_forces_symm`
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean:704-706` — CSLib's own "simultaneous maximal pair" docstring (F2)
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean:712` — `cs5_symmetric_tail_box_gap`
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — `cs5_dia_bot_imp_bot` = Pacheco's `N`, licenses `Wc⊥ = ∅`

---

## BibKey Verification

Verified against `references.bib` at the CSLib project root; all citations in this report use verified
keys: `Simpson1994`, `MarinMoralesStrassburger2021`, `Pacheco2024`, `AlechinaMendlerdePaivaRitter2001`,
`Wijesekera1990`, `Dosen1985`, `BozicDosen1984`.

**Not in `references.bib` and referenced here only as prior art, not as a citation:**
- **PlotkinStirling1986** — would need adding if Theorem 7.1's correspondence is ever cited in Lean
  docstrings. Currently reachable transitively via `MarinMoralesStrassburger2021`. Not recommended (F8).
- **deGrootShillitoClouston2025** — worth adding to `references.bib` regardless of route, since F6
  establishes it as the state of the art for CK-cube canonical models and it independently validates
  CSLib's `CKSegment` design. Suggested key: `deGrootShillitoClouston2025`, LICS 2025, arXiv:2408.00262.
- **FischerServi1984** — **not needed**, do not add (F8).

---

## Adversarial Self-Verification

| # | Challenge | Resolution |
|---|---|---|
| **C1** | "F1 claims the A3 verdict is a non-sequitur, but you never read A3." | **Partially conceded.** I could not read A3 (concurrent). I challenge the chain *as stated in my briefing*. The reductio is strong and internal: `cs5FC''` conjunct 3 *is* plain symmetry, so Track C's countermodel also lands in `cs5Tail`-shape; a criterion that closes Track B on that basis closes Track C too. Either A3 has an argument beyond the summary, or the closure is unsound. **Flagged as "re-examine", not "overturn".** Confidence in the reductio: high. Confidence that A3 is actually wrong: medium. |
| **C2** | "You claim `cs5_symmetric_tail_box_gap` and Pacheco Lemma 18 are consistent — check it." | **Verified.** Instantiate the gap at `H := ∆`, `T := Σ`, `p := φ`: gap gives `□(p ∨ □q) ∈ ∆ ∧ q ∉ ∆ → p ∈ Σ`; Lemma 18 gives `φ ∉ Σ`; therefore `q ∈ ∆`. `∆ ⊋ Γ` is exactly what Lemma 18's `Γ ⊑c ∆` permits. No contradiction. |
| **C3** | "You claim the target `cs5FC''` might be unachievable via MMS Remark 7.3 (naive conditions validate too much). Did you actually test that?" | **Tested and REJECTED — this is a claim I abandoned.** My initial hypothesis was that plain symmetry is the "naive" condition MMS warn about, making the target false. **F5 refutes it**: Pacheco's CKB-models are *plainly symmetric* and proved complete (chunk `8715c61b7b63ae1b` + Thm 13). I also constructed a direct semantic countermodel to `□(p∨□q) → (□p ∨ q)` over `cs5FC''` (F2), confirming the gap lemma carries no hidden falsity. **Recommendation modified: the target stands; do not pursue an "incompleteness of cs5FC''" line.** |
| **C4** | "The F3 defect claim against a published paper is strong. Is the step really invalid?" | **Holds, on two independent grounds.** (i) Θ's maximality is w.r.t. a family whose binding cap includes `Θ□ ⊆ Σ`, so `φ ∉ Θ` does not entail `Θ ∪ {φ}` inconsistent, so `¬φ ∈ Θ` does not follow. (ii) Self-defeating: if sound, Θ is negation-complete hence classical, collapsing `⊑c` and proving CKB classical. Note Pacheco2024 is **arXiv:2408.16428 and may not be peer-reviewed** — relevant under the "cutting no corners" directive. **Scope discipline:** the defect is against the *published argument*, not against Theorem 13, which is independently corroborated (ADS2015 §4.3: B entails k3 and k5 constructively). |
| **C5** | "F3 says Σ-primality is repairable. Show it, don't assert it." | **Worked out in F3 and it survives:** in Lemma 18's family, `Y□ ⊆ X` and `Y ⊆ X◇` are monotone in `X`, so only `φ ∉ X`/`⊥ ∉ X` cap growth of `X`; maximality reduces to "avoid φ"; ∨-elimination closes. **I did not overclaim the other half** — ∆'s cap `∆□ ⊆ Σ` is antitone and the argument does *not* close. That asymmetry is reported as the crux, not papered over. |
| **C6** | "F4 says MMS is a dead end. That contradicts the task title (`labelled_bounded_context`) and plan 01." | **Stands, and it is the most actionable finding here.** Direct quotes from MMS Thm 3.3 and Thm 7.2's proof show 4⟹1 is imported from `[Ser84, PS86]`, never proved. Confidence: **high** (verbatim, twice). Note this does *not* impugn Simpson-based labelled routes — Simpson **does** prove his own completeness (Lemma 5.3.1, F7). The dead end is `labIK≤` specifically. |
| **C7** | "F6 claims no mechanisation exists — an unfalsifiable negative." | **Downgraded to medium-high.** I verified the three plausible candidates concretely (full-text `pdftotext` grep over dGSC returning zero `symmetr`/`S5` hits is strong; Ayertienna and FormalizedFormalLogic verified by structure/scope). I cannot prove exhaustiveness over all repositories. Stated as "none found among the plausible candidates", and the practical conclusion (nothing to port) is robust either way. |
| **C8** | "Probe B′ retires `CKSegment` for CS5 — that discards landed sorry-free assets." | **Conceded and reflected in the recommendation.** This is why B′ is scoped as a **probe alongside Track C**, not a track switch. `Wc⊥ = ∅` additionally depends on `cs5_dia_bot_imp_bot` being usable as Pacheco's `N` in the CK-model definition — plausible (it is literally `¬◇⊥`) but **unverified**; I did not read the CK-model definition's `botForces` obligations closely enough to promise the segment machinery is dispensable. Confidence in the retirement claim: **medium**. Confidence in the probe's *diagnostic* value: high (it resolves the crux either way, for ~200 lines). |
| **C9** | "F7 implies Ch.5 lets Track C skip the C5 crux." | **Explicitly denied in F7.** Lemma 5.3.1 gives the *countermodel* half only; `labelled ⊢ φ → Derivable CS5ModalAxiom φ` is still Ch.6 tree surgery = C5. Ch.5 de-risks the *other* half and confirms C5 is the sole remaining crux. No claim of skipping. |

**Recommendations modified after verification:** C3 (dropped the "target may be false" line entirely —
F5 refutes it); C1 (softened "overturn A3" → "re-examine A3"); C8 (B′ demoted from track-switch to
scoped probe alongside Track C); C7 (F6 downgraded to "none found among plausible candidates").

**No fundamental flaw found requiring a `## Revised Direction` restart.**

---

## Confidence Level

**Overall: medium-high.**

| Finding | Confidence | Basis |
|---|---|---|
| F4 — MMS `labIK≤` never proves semantic completeness; dead end for 517 | **high** | Verbatim, twice (Thm 3.3, Thm 7.2 proof) |
| F1 — `cs5FC''` demands plain symmetry; `cs5Tail`-shape unavoidable on all routes | **high** | Read directly off the Lean source |
| F5 — plain symmetry is a complete frame condition (target not disqualified) | **high** | Pacheco chunk `8715c61b7b63ae1b` + Thm 13 |
| F2 — gap lemma consistent with Lemma 18; not an impossibility result | **high** | Instantiation checked by hand (C2) |
| F3 — Pacheco Lemma 16 primality defective; Σ-half repairable | **medium-high** | Two independent grounds (C4); Σ-repair worked out (C5) |
| F7 — Simpson Lemma 5.3.1 is the right prior art for the simultaneous construction | **medium-high** | Verbatim, but OCR-degraded; Ch.5's bridge to the axiomatic target still needs C5 |
| F8 — FischerServi1984 not needed | **medium-high** | Pacheco attributes (2)⟺(4) to Simpson1994 |
| F6 — no IS5/CS5 Kripke completeness mechanised anywhere | **medium-high** | Three candidates eliminated concretely; not exhaustive (C7) |
| F3 crux — ∆-primality under the antitone `∆□ ⊆ Σ` cap | **low** (genuinely open) | The real obstruction; no source resolves it |
| Probe B′ succeeds | **~35%** | Hinges entirely on the ∆-primality crux |
