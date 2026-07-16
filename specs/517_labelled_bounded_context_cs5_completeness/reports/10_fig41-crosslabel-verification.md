# Fig 4-1 Cross-Label Claim — Divergence Audit

**Task**: 517 | **Session**: `sess_1784156551_995e9d` | **Dispatch**: divergence audit (H5), verification only
**Reference grounding tier**: 1 (literature-backed) | **BibKey**: `Simpson1994` — verified, `references.bib:86`
**Probe**: `specs/517_labelled_bounded_context_cs5_completeness/probes/fig41-crosslabel-gate.lean` (sorry-free, axiom-clean)

---

## VERDICT: **CONFIRMED**

Figure 4-1 (p. 69) prints **both** `(⊥E)` and `(∨E)` cross-label, with no side condition on
either. CSLib transcribes both label-local. Both transcriptions **are** strict weakenings, and
Lemma 5.3.1's proof (p. 93) **needs both at full generality**. Phase 21's reading of the raster
is correct and I could not refute it. I attempted to refute it three ways and each attempt
failed; the strongest attempt (§4 below) is now a sorry-free Lean probe that establishes the
*boundary* of the defect rather than removing it.

**However, the blast radius stated in the dispatch is FALSE, and this is the actionable finding.**
The claim that the repair "would require re-proving landed CK/CT/CS4/CS5 soundness" does not
survive contact with the import graph: **`NIK` occurs in exactly two files, and `CK`/`CT`/`CS4`/
`CS5` never import `Labelled` at all.** The only induction over the derivation relation anywhere
in the library is `NIK.weaken`. I rebuilt the repaired system and re-proved that induction in the
probe: it goes through with the two cases threading one extra label and their proof scripts
otherwise unchanged.

**The repair is two constructor signatures and two one-line proof edits — not a mainline
soundness rewrite.** The premise on which authorization was declined is incorrect.

---

## Source-to-Implementation Mapping (H3)

Every row read from the **page raster**. Where raster and text layer disagree, raster wins.

| Source claim | BibKey | Page (printed / PDF) | CSLib declaration | file:line | Verdict |
|---|---|---|---|---|---|
| `(⊥E)`: `x:⊥ / y:A`, no side condition | Simpson1994 | p. 69 / PDF 78 | `NIK.efq` — `(x ∶ .bot) → (x ∶ A)` | `Deduction.lean:206-207` | **Diverges** (label-local) |
| `(∨E)`: major `x:A∨B`; minors/conclusion `y:C`; discharges `[x:A]`,`[x:B]`; no side condition | Simpson1994 | p. 69 / PDF 78 | `NIK.orE` — all labels `x` | `Deduction.lean:225-228` | **Diverges** (label-local) |
| `(□I)` restriction `*`, `(◇E)` restriction `†` — the *only* two marked restrictions in Fig 4-1 | Simpson1994 | p. 69 / PDF 78 | `NIK.boxI` / `NIK.diaE`, cofinite `L` | `Deduction.lean:245`, `:257` | Faithful |
| `(□E)`: `x:□A, xRy / y:A` — cross-label | Simpson1994 | p. 69 / PDF 78 | `NIK.boxE` — independent `x y` | `Deduction.lean:237-239` | Faithful |
| `(◇E)` conclusion `z:B`, `z` independent of `x` | Simpson1994 | p. 69 / PDF 78 | `NIK.diaE` — independent `x z` | `Deduction.lean:257-260` | Faithful |
| `𝒯`-prime cond. 2 (Consistency): `∀x in 𝒢, Γ ⊬ x:⊥` | Simpson1994 | p. 92 / PDF 101 | (`Context.lean` `TPrime`) | — | Label-local *as stated* |
| `𝒯`-prime cond. 3 (Disjunction property): `x:A∨B ∈ Γ → x:A ∈ Γ ∨ x:B ∈ Γ` | Simpson1994 | p. 92 / PDF 101 | (`Context.lean` `TPrime`) | — | Label-local *as stated* |
| Lemma 5.3.1 proof, consistency step: "immediate, because `Δ ⊬^𝒯_ℋ x:A`" | Simpson1994 | p. 93 / PDF 102 | — | — | **Needs cross-label `(⊥E)`** |
| Lemma 5.3.1 proof, disjunction step: "otherwise `Δ ⊢^𝒯_ℋ x:A` by an application of `(∨E)`" | Simpson1994 | p. 93 / PDF 102 | — | — | **Needs cross-label `(∨E)`** |

**Text-layer discrepancy (recorded).** PDF p. 78's text layer renders Figure 4-1 as noise
(`%(M)`, `%(/\El)`, `lfi:AVBy:yciC = (VE)`). `pdftotext` and the chunk text agree with each other
and are both useless here. Every Figure 4-1 row above comes from the raster. This reconfirms
`provenance_fidelity: ocr_rescanned_reflowed_partial_symbol_loss`. The *prose* pages (92, 93)
survive in the text layer and were cross-checked against their rasters — they agree.

---

## Findings

### Q1 — What Figure 4-1 actually prints

Verbatim from the raster (PDF p. 78 = printed p. 69):

```
x : ⊥                                  [x:A]     [x:B]
----- (⊥E)                               ⋮         ⋮
y : A                      x : A ∨ B   y : C     y : C
                           --------------------------- (∨E)
                                       y : C
```

`(⊥E)`: premise `x : ⊥`, conclusion `y : A`. `(∨E)`: major premise `x : A ∨ B`; two minor
premises `y : C` discharging `[x : A]` and `[x : B]` respectively; conclusion `y : C`.

**Neither rule carries a side condition.** The only restriction markers on the entire figure are
`*` (on `(□I)`) and `†` (on `(◇E)`), and both are spelled out in full beneath it. `(⊥E)` and
`(∨E)` are unmarked.

### Q2 — Are the labels genuinely distinct? **Yes.**

Three independent checks, all pointing the same way:

1. **Typography**: `x` and `y` are distinct metavariables, not `x` vs `x'`. Legible without
   ambiguity at this resolution; no diacritic or prime.
2. **Contrast within the same figure**: Simpson writes `(∧I)`, `(∧E1)`, `(∧E2)`, `(∨I1)`,
   `(∨I2)`, `(⊃I)`, `(⊃E)` with **every label `x`** — label-local. He had the label-local form
   in hand and in use on the same page, and chose `y` for `(⊥E)`'s conclusion and `(∨E)`'s
   conclusion. This is a deliberate contrast, not a slip of the pen.
3. **Confirmed by usage** (decisive): p. 93 *applies* `(∨E)` cross-label — see Q5. A rescan
   artifact in the figure could not propagate into the prose of a different page.

### Q3 — Does surrounding prose constrain the labels? **No.**

Prose on p. 70 (PDF 79) immediately following the figure defines major/minor premises and states
"assumptions are discharged by applications of the (∨E), (⊃I), (□I) and (◇E) rules" — confirming
`(∨E)` discharges, and adding **no** label constraint. The `(□I)`/`(◇E)` restrictions are the
only ones stated, and the figure already marks them. Nothing anywhere constrains `x = y` in
`(⊥E)` or `(∨E)`.

### Q4 — Is label-local really a strict weakening? **Yes — but only in the disconnected case.**

This was my strongest refutation attempt, and it is where the interesting structure is.

**The label-local system recovers every *edge-connected* cross-label instance** — mechanized,
sorry-free, in the probe:

- `efq_crossLabel_of_edge` (probe §1): for **any** `𝒯`, using **no** frame axiom, from
  `Γ ⊢_G x:⊥` and any `TClosure 𝒯 G.R x y`, derive `Γ ⊢_G y:A`. The trick: label-local `efq`
  yields `x : C` for *any* `C`, in particular `x : □A`; `(□E)` then walks it across the edge.
  The label walk is done by the modal rules — which CSLib *did* transcribe cross-label.
- `dia_bot_elim_TS5` (probe §2): Simpson's `k3 : ◇⊥ ⊃ ⊥` — derived label-locally at `TS5`.
- `dia_or_dist_TS5` (probe §3): Simpson's `k4 : ◇(A∨B) ⊃ ◇A ∨ ◇B` — derived label-locally at
  `TS5`, case-splitting to `y : □(◇A ∨ ◇B)` and walking the `□` back.

`k3` and `k4` are precisely the two IK axioms whose natural derivations route through
cross-label `(⊥E)`/`(∨E)`. **They survive the label-local transcription intact.** The edge they
need is manufactured by `(◇E)` itself (`G.addEdge x y`), and the return direction `y → x` is
supplied by `χ_B ∈ TS5`.

**But the disconnected instances are not recoverable.** With `G.R = ∅` and `𝒯 = TS5`,
`TClosure TS5 ∅` contains only reflexive pairs, so from `x:⊥` every derivable conclusion stays
at label `x`: `efq` cannot move a label, `boxE`/`diaI` need a closure edge, and `diaE` needs a
`◇` premise. Hence `x:⊥ ⊬ y:A` for `y ≠ x`. So the two forms are **not** inter-derivable, and
label-local is strictly weaker as a rule schema.

> **Confidence flag**: the *positive* results are machine-checked. The *underivability* of the
> disconnected instance is a structural argument (label-connectivity invariant), reasoned but
> **not mechanized** — proving it in Lean needs an invariant over `NIK` or a countermodel, which
> is a larger job than this audit's scope. It is not load-bearing for the verdict: Q5 shows the
> disconnected instances are *needed*, and a rule that is at best unprovable-as-stated is the
> same repair either way.

### Q5 — Does Lemma 5.3.1 need the cross-label forms? **Yes. Both. Disconnected.**

This is what defeated my refutation, read from the p. 93 raster (PDF 102).

The `𝒯`-prime *conditions* (p. 92) are stated label-locally — cond. 2 is "for all `x` in `𝒢`,
`Γ ⊬^𝒯_𝒢 x:⊥`" and cond. 3 keeps `x:A∨B`, `x:A`, `x:B` all at the same `x`. That initially looks
like it favours the label-local reading. It does not survive the *proof*:

**Consistency.** p. 93: *"Consistency is immediate, because `Δ ⊬^𝒯_ℋ x:A`."* Here `x:A` is the
**fixed** target formula the Zorn construction is built around, while cond. 2 quantifies over
**every** label `z` of `ℋ`. The word *"immediate"* is only earned if `Δ ⊢ z:⊥` collapses
directly to `Δ ⊢ x:A` — which is exactly cross-label `(⊥E)`, at arbitrary `z` and `x`, with **no
edge between them**. Under label-local `(⊥E)` the step does not go through at all.

**Disjunction property.** p. 93, verbatim: *"suppose that `y : B ∨ C ∈ Δ`. Now either
`Δ, y:B ⊬^𝒯_ℋ x:A` or `Δ, y:C ⊬^𝒯_ℋ x:A`, for otherwise we would have that `Δ ⊢^𝒯_ℋ x:A` **by an
application of (∨E)**."* Major premise at `y`, conclusion at `x`, `y` ranging over `ℋ` and `x`
fixed and unrelated. This is Figure 4-1's `(∨E)` under the renaming `x↦y, y↦x` — used at full
disconnected generality.

So the §4 workaround **cannot rescue Lemma 5.3.1**: it needs an edge, and the prime lemma has
none. Both rules must be repaired.

### Q6 — Is CSLib's label-local form a deliberate, documented decision? **No.**

- `Deduction.lean:205` — `/-- Ex falso quodlibet, label-local. -/`
- `Deduction.lean:224` — `/-- (∨E), label-local case split, discharging both branch assumptions. -/`

Both *assert* "label-local" descriptively. Neither gives a rationale, cites Simpson, or notes
that Figure 4-1 prints otherwise. The contrast is sharp and diagnostic:

- `boxI`/`diaE` docstrings quote Simpson's side conditions **verbatim with byte offsets**
  (`:4661`, `:4664`). The file is meticulous about fidelity where the author was tracking it.
- The module docstring **explicitly flags its three deliberate departures** — the
  locally-nameless encoding, the geometric extension's rule shape, and `χ_D`'s exclusion — each
  with a paragraph of justification. `efq`/`orE` are **not among them**.
- The module opens by claiming it "lands A. K. Simpson's labelled natural-deduction system
  `N_IK` [Simpson1994], **Figure 4-1** (`:4630-4670`)".

A file that flags three departures at length and cites byte offsets for two side conditions did
not silently and deliberately weaken two rules without a word. **This is a transcription slip,
not a design decision.**

---

## Scope-Shrinking: the repair is ~4 lines, not a soundness rewrite

I could remove neither `efq` nor `orE` from the repair bundle. Instead the bundle's **cost**
collapses. The dispatch states the repair "would require re-proving landed CK/CT/CS4/CS5
soundness". **That is false.**

| Stated risk | Measured reality |
|---|---|
| Rewrite touches mainline inference rules used by CK/CT/CS4/CS5 soundness | `grep -rln NIK Cslib/` returns **exactly two files**: `Labelled/Deduction.lean`, `Labelled/Context.lean`. `CK.lean`/`CT.lean`/`CS4.lean`/`CS5.lean` **never import `Labelled`**. Nothing outside `Labelled/` imports `Labelled.Deduction` or `Labelled.Context`. |
| Landed soundness proofs must be re-proved | There is **no landed soundness proof over `NIK`**. The `efq`/`orE` hits elsewhere in the repo are `Axiom.efq` from the unrelated `Logics/Bimodal/` development. |
| Many inductions over the rule set must be repaired | **One**: `NIK.weaken` (`Deduction.lean:275`). `Deriv.mono`/`Deriv.ofNIK` (`Context.lean:194-207`) consume `NIK.weaken` as a black box and are signature-stable. `NIK.smoke_boxE` does not induct. |

**Mechanically demonstrated** (probe §4): `NIKX` is `NIK` verbatim with `efq`/`orE` given an
independent conclusion label, exactly as Figure 4-1 prints them. `NIKX.weaken` — the reproduced
sole induction — compiles with the two cases threading one extra label and their scripts
otherwise character-identical to the mainline proof. `NIKX.consistency_step` and
`NIKX.disjunction_step` then deliver Simpson's two p. 93 steps as one-liners.

Concrete diff shape for `Deduction.lean` (**not applied — territory is `reports/`+`probes/`**):

```
- | efq (G) (Γ) (x : Label Atom) (A) (h : NIK 𝒯 G Γ (x ∶ .bot)) : NIK 𝒯 G Γ (x ∶ A)
+ | efq (G) (Γ) (x y : Label Atom) (A) (h : NIK 𝒯 G Γ (x ∶ .bot)) : NIK 𝒯 G Γ (y ∶ A)

- | orE (G) (Γ) (x : Label Atom) (A B C) (hor …) (hA : … (x ∶ C)) (hB : … (x ∶ C)) : … (x ∶ C)
+ | orE (G) (Γ) (x y : Label Atom) (A B C) (hor …) (hA : … (y ∶ C)) (hB : … (y ∶ C)) : … (y ∶ C)
```
plus, in `NIK.weaken`, `| efq G Γ x A _ ih` → `| efq G Γ x y A _ ih` and `.efq G' Δ x A` →
`.efq G' Δ x y A` (and the same one-label thread in the `orE` case). **Two signatures, two
proof-case edits.** Soundness of both repaired rules is trivial semantically (`x:⊥` is satisfied
nowhere, so cross-label `(⊥E)` is vacuous; cross-label `(∨E)` splits on a fact about `x` to
conclude about `y`).

**Net effect on the bundle**: `efq` and `orE` both stay, but they move from "mainline rewrite
requiring re-proved soundness" to "two signature generalizations behind one structural
induction, no downstream consumers". The `deductiveClosure` and `clModel` defects are
independent of this question and are untouched by this audit.

---

## Adversarial Self-Verification (H4)

I tried to refute my own CONFIRMED verdict. The `efq_crossLabel_of_edge` /`k3`/`k4` probe was
built *as* a refutation attempt and I expected it to shrink the claim to nothing. It did not.

| Claim | Source / counterexample |
|---|---|
| Fig 4-1 prints `(⊥E)` cross-label | **Raster** PDF p. 78. **Refutation attempted**: is `y` a rescan artifact of `x`? Answer: no — `(∧I)`…`(⊃E)` on the *same figure* all print `x` uniformly, so the glyph shapes are directly comparable on one page, and the `(⊥E)` conclusion glyph is not the `x` glyph. Independently corroborated by p. 93 usage. |
| Fig 4-1 prints `(∨E)` cross-label | **Raster** PDF p. 78. **Refutation attempted**: maybe prose constrains `x=y`? p. 70 prose checked — states only the `(□I)`/`(◇E)` restrictions. No constraint. |
| Neither rule has a side condition | **Raster** PDF p. 78: only `*`(□I) and `†`(◇E) markers appear; both are spelled out below the figure. |
| "If I am wrong about the labels being distinct, what would I expect to see?" | I would expect (a) the figure to print `x` in both places, (b) Simpson never to *apply* the rules cross-label, and (c) a side condition or prose tying the labels. I checked all three: (a) is false (raster), (b) is false (p. 93 applies `(∨E)` with major `y:B∨C` and conclusion `x:A`), (c) is false (p. 70 prose, and the figure's own restriction markers). **No expected signature of the "artifact" hypothesis is present.** |
| Cross-label `(⊥E)` derivable when labels share a closure edge | **Machine-checked**: `efq_crossLabel_of_edge`, any `𝒯`, no frame axiom. Sorry-free, axioms `[propext]`. |
| `k3`, `k4` derivable label-locally at `TS5` | **Machine-checked**: `dia_bot_elim_TS5`, `dia_or_dist_TS5`. Sorry-free, axioms `[propext, Classical.choice, Quot.sound]` — no `sorryAx`. |
| Disconnected `x:⊥ ⊢ y:A` underivable → label-local strictly weaker | **Reasoned, NOT mechanized.** Structural label-connectivity argument over `TClosure TS5 ∅` = reflexive pairs only. Flagged in Q4. Not load-bearing: Q5 independently forces the repair. |
| Lemma 5.3.1 needs cross-label `(∨E)`, disconnected | **Raster** PDF p. 102, quoted verbatim in Q5. This is the step that defeated my refutation. Strongest single piece of evidence in this report. |
| Lemma 5.3.1 needs cross-label `(⊥E)`, disconnected | **Raster** PDF p. 102: "Consistency is immediate, because `Δ ⊬ x:A`". Inference from the word "immediate" + cond. 2's `∀x in 𝒢`. **Marginally weaker than the `(∨E)` row** — Simpson does not name `(⊥E)` explicitly here, as he names `(∨E)`. But no other rule can carry `z:⊥` to an edge-free `x:A`, and §1's probe shows the only alternative route (`□`-walking) requires an edge that the prime lemma does not have. Confidence: high, not certain. |
| CK/CT/CS4/CS5 soundness would need re-proving | **REFUTED.** Import graph: those files never import `Labelled`. `NIK` lives in 2 files. This was the dispatch's own framing and it does not hold. |
| Repair survives the sole induction | **Machine-checked**: `NIKX` + `NIKX.weaken` compile sorry-free with the two cases' scripts otherwise unchanged. |
| CSLib's label-local form is a deliberate documented choice | **REFUTED** by `Deduction.lean` itself: module docstring flags 3 departures at length, none is `efq`/`orE`; `boxI`/`diaE` cite Simpson byte offsets while `efq`/`orE` cite nothing; the module claims to land Figure 4-1. |

**Failure mode this dispatch was warned about.** The `fischer-servi-probe.lean` precedent was a
confident *negative* verdict from a structural-mismatch argument, later refuted by an actual
derivation. The symmetric risk here was a confident *positive* verdict from a raster glance. I
guarded against it by (a) not resting the verdict on the figure alone but on Simpson's *use* of
the rule at p. 93, and (b) building the refutation in Lean rather than arguing it in prose — the
probe is exactly the "actual derivation" move that overturned the Fischer-Servi verdict, applied
pre-emptively to my own. It found real structure (§4) and still failed to refute the claim.

**Where I remain uncertain**: only the `(⊥E)`-half of Q5 (inference from "immediate" rather than
a named rule application) and the non-mechanized underivability argument in Q4. Neither changes
the recommendation, because the `(∨E)` half is explicit and the repair is joint.

---

## Recommendation

1. **Authorize the `efq`/`orE` generalization.** The verdict is CONFIRMED and the repair is
   two constructor signatures plus two one-line proof-case edits behind a single structural
   induction, with **zero downstream consumers**. The stated reason for declining — re-proving
   landed CK/CT/CS4/CS5 soundness — rests on a false premise about the import graph.
2. **Do not re-scope `deductiveClosure`/`clModel`** on the strength of this audit; they are
   independent of the Fig 4-1 question (consistent with the dispatch's settled-facts note).
3. **Carry probe §1-§3 forward as regression tests.** `efq_crossLabel_of_edge`, `k3`, `k4` must
   still hold after the repair (the cross-label rules subsume the label-local ones, so they
   will) — they pin the boundary between what the repair adds (disconnected instances) and what
   was never at risk (everything reachable along an edge).
4. **When repairing, add the rationale docstrings that are currently missing**, citing
   `Simpson1994` Fig 4-1 p. 69 and the Lemma 5.3.1 p. 93 steps that force the cross-label form.

## Phase status

Phase 21 stays `[BLOCKED]` — this dispatch completes no plan phase. No phase marked
`[COMPLETED]`. `git status --short Cslib/` verified empty at dispatch end.
