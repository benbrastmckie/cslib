# Phase 21 — Prime Lemma 5.3.1 at `𝒯 = ∅`: BLOCKED (target type is empty)

- **Task**: 517 — labelled bounded context, CS5 completeness
- **Phase**: 21 (leg A1, the crux phase) — **[BLOCKED]**
- **Session**: sess_1784156551_995e9d
- **Probe**: `probes/prime-lemma-blockers.lean` (11 declarations, **sorry-free**;
  `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]` on every one)
- **Territory**: `probes/` + `plans/` + `summaries/` only. **`Cslib/` untouched**
  (`git status --short Cslib/` empty).
- **Reference grounding**: Tier 1 (literature). [Simpson1994], BibKey verified `references.bib:86`.

---

## Verdict

**Phase 21's deliverable is not constructible as specified — and the reason is not the
mathematics.** `TPrime 𝒯 Atom` is **uninhabited for every `𝒯`, including `𝒯 = ∅`**. Lemma 5.3.1's
entire job is to *produce* an inhabitant of that type, so no amount of proof effort at any `𝒯` can
succeed until the type is repaired. The Zorn argument was never started; the mandated
small-model/consistency check killed the statement first.

**The route is not what failed.** p. 92 confirms plan v3's convergence anchor verbatim.

---

## 1. Transcription of Lemma 5.3.1 (from PDF layout, pp. 92-93 / PDF pp. 101-102)

**Statement** (p. 92, verbatim):

> **Lemma 5.3.1 (Prime lemma)** *If `(G,Γ)` is a context and `Γ ⊬^𝒯_G x:A` then there is a
> `𝒯`-prime context `(H,Δ)` with `(H,Δ) ⊇ (G,Γ)` such that `Δ ⊬^𝒯_H x:A`.*

**The Zorn setup** (p. 92, verbatim) — this is the mission's "ONE Zorn application over whole
contexts", and it is **confirmed exactly as plan v3 specifies**:

> Let `V'` be some coinfinite subset of `V` such that the underlying set of `G` is contained in
> `W(V')` (as given by condition 1 on being a context). Consider the set `C` of all contexts
> `(G',Γ') ⊇ (G,Γ)` such that the underlying set of `G'` is contained in `W(V')` and
> `Γ' ⊬^𝒯_{G'} x:A`. Let `{(G_i,Γ_i)}_{i∈I}` be any chain in the set `C` partially ordered by
> inclusion. It is easily seen that `(⋃_{i∈I} G_i, ⋃_{i∈I} Γ_i)` is also in `C`. So every chain in
> `C` has an upper bound. Therefore, by Zorn's Lemma, `C` has a maximal element `(H,Δ)`.

One poset, over **whole contexts**, graph and formula-set growing **together**, capped only by the
excluded `x:A`, inside a **fixed coinfinite reserve** `W(V')`. This is the *"simultaneous maximal
pair, not sequentially"* that `CS5.lean:705-706` names as the real open problem.

**The four clause discharges** (p. 93, verbatim, condensed):

| Clause | Simpson's instrument |
|---|---|
| Consistency | *"immediate, because `Δ ⊬^𝒯_H x:A`"* — **needs cross-label `(⊥E)`**; no maximality |
| Deductive closure | `Δ ⊢_H y:B` ⟹ `Δ,y:B ⊬_H x:A` ⟹ `(H, Δ∪{y:B}) ∈ C` ⟹ maximality ⟹ `y:B ∈ Δ` |
| Disjunction | `(∨E)` **cross-label**, then maximality on `(H,Δ∪{y:B})` / `(H,Δ∪{y:C})` |
| Diamond | `(◇E)` + maximality on `(H ∪ {yRv_{y:◇B}}, Δ∪{v:B})` ⟹ `H' = H` ⟹ requirement 2 |

**Phase 20's TRAP warning is confirmed and was honoured**: at a quantifier-free axiom the reductio
framing of the `clModel` step and its requirement-3 exit are both vacuous, and the goal is
delivered by the maximality step used directly. No literal transcription of that framing was
attempted. (The `clModel` step never became reachable — blocker 1 fires first.)

**Note the diamond step's reductio is NOT vacuous** — unlike the `clModel` one. `(◇E)`'s freshness
side-condition is exactly what the hypothesis *"Suppose `v_{y:◇B}` is not in `H`"* supplies. The two
reductios are not the same shape, and a successor must not generalize Phase 20's warning to this one.

---

## 2. Blocker 1 — `TPrime 𝒯 Atom` is uninhabited for **every** `𝒯` (mechanized)

```
NIK.impI + NIK.assumption ⟹ (x : A ⊃ A) derivable at an ARBITRARY label, empty assumption list,
                            no premises, no side conditions, no reference to G.X
deductiveClosure (type-wide) ⟹ (x : A ⊃ A) ∈ Γ   for every label x
ctxSubset                    ⟹ x ∈ G.X            for every x, i.e. G.X = univ
coinfinite                   ⟹ ⊥                  (Label.var n with n ∉ V')
```

Mechanized as `tPrime_false` + `instance : IsEmpty (TPrime 𝒯 Atom)`. Universe-polymorphic; holds
for every `Atom` **and every `𝒯`**.

### This supersedes Phase 20's scoping

Phase 20 found the emptiness only at `TS5` (`tPrime_TS5_false`), diagnosed the cause as *"`χ_T`
alone ... the only `TS5` axiom with `n = 0` premises"*, and concluded the defect *"lands on Phase
23, not Phase 21"* — indeed that plan v3's D2 sequencing *"independently saves Phase 21 from a
blocker nobody had spotted"*.

Clause 0 **is** vacuous at `𝒯 = ∅`. But **clause 1 empties the type on its own**, and its driver is
a *premise-free derivation*, so it is completely independent of `𝒯`. Phase 20's
`IsEmpty (TPrime TS5 Atom)` is a special case of `tPrime_false`. **The `𝒯 = ∅`-first sequencing
does not dodge the emptiness.**

This is not a criticism of Phase 20's mission — it was dispatched at `(R_Υ)`, answered that
correctly, and found the first instance of this defect class. But its *scope* verdict was wrong,
and it is the verdict Phase 21 was dispatched on.

### The repair

Simpson's clause 1 (p. 92): *"If `Γ ⊢^𝒯_G x:A` then `x:A ∈ Γ`"*, where `⊢_G` is §5.1's consequence
relation — a judgement about labels **of `G`**. Lemma 5.3.2 (p. 94) makes the same relativity
explicit in its own statement: *"for all `y` **in `H`**"*. So:

```lean
deductiveClosure : ∀ x ∈ G.X, ∀ A, Deriv 𝒯 G Γ (x ∶ A) → (x ∶ A) ∈ Γ
```

This is a **transcription fix, not a convenience weakening** — and it is what Lemma 5.3.1's own
deductive-closure step needs. Simpson forms `(H, Δ ∪ {y:B})`; for that to *be a context*,
`Context.ctxSubset` demands `y ∈ H.X`, which only the relativized clause supplies as a hypothesis.
**The type-wide clause is unusable at precisely the step that consumes it.**

---

## 3. Blockers 2 and 3 — two `NIK` rules transcribed label-local

Read from the **p. 69 page raster** (PDF p. 78). `pdftotext -layout` renders Figure 4-1 as noise
(`%(M) %(/\El) %(Am)`) — the rule shapes are unrecoverable from the text layer. **This is the same
text-layer failure mode Phase 20 documented for `H_i` on p. 92, at a second site.** The standing
"PDF layout, not chunk text" rule earned its keep twice.

**Figure 4-1, as printed:**

```
x:⊥                         x:A∨B   [x:A]⋮y:C   [x:B]⋮y:C
─── (⊥E)                    ──────────────────────────── (∨E)
y:A                                     y:C
```

Both are **cross-label**. CSLib transcribes both **label-local**:

| Rule | Simpson (p. 69) | CSLib | 5.3.1 step that needs the printed form |
|---|---|---|---|
| `(⊥E)` | `x:⊥ / y:A` | `NIK.efq`: `x:⊥ / x:A` | *"Consistency is immediate, because `Δ ⊬_H x:A`"* |
| `(∨E)` | major `x:A∨B`, concl. `y:C` | `NIK.orE`: both at `x` | *"...otherwise `Δ ⊢_H x:A` by an application of `(∨E)`"* |

Both transcriptions are **strict weakenings**, mechanized: `efq_of_efqCrossLabel` and
`orE_labelLocal_of_orECrossLabel` derive CSLib's rules from the printed ones.

The gap is stated sharply, not asserted:
- `consistency_of_efqCrossLabel` — Simpson's one-line argument **goes through** given the printed
  rule (and needs no maximality, exactly as he says).
- `consistency_at_excluded_label_only` — CSLib's label-local `efq` discharges the consistency
  clause **only at `y = x`**. `TPrime.consistency` demands it at every `y ∈ H.X`; for `y ≠ x` the
  clause is left undischarged and Simpson's proof offers no second argument — because it needs none.

The other 12 rules match Figure 4-1 (`∧I`, `∧E1/2`, `∨I1/2`, `⊃I`, `⊃E` label-local as printed;
`□E`, `□I`, `◇I`, `◇E` as printed). **Exactly two rules diverge.**

### One root cause

Blockers 1-3 plus Phase 20's `clModel` finding are **four instances of one defect class**: the
transcription drops the **domain-relativity / cross-label structure** Simpson's Chapter 5 relies on.
Chapter 4 reads fine in isolation — which is presumably why the divergences survived — but Chapter
5's completeness argument consumes exactly the structure that was dropped.

---

## 4. Flagged, NOT mechanized: the chain-union step (the real crux)

**MEDIUM confidence.** Simpson's *"It is easily seen that `(⋃G_i, ⋃Γ_i)` is also in `C`"* needs
`Deriv 𝒯 G_∞ Γ_∞ (x∶A) → ∃ i, Deriv 𝒯 G_i Γ_i (x∶A)` — a **finite-support** argument.

`NIK.boxI` and `NIK.diaE` encode their eigenvariable side-condition by **cofinite quantification**
(`∀ y ∉ L`), so a `NIK` derivation has **infinite branching** and no finite graph support.
Rebuilding a `boxI` at a single chain index `i` needs **one `i` valid for cofinitely many `y`**;
each `y` yields its own `i_y`, and directedness does not bound them. Simpson's derivations are
finite trees with **one** eigenvariable premise — which is why he calls it "easily seen". **The gap
is created by the encoding, not by the mathematics.** A label-renaming/equivariance lemma for `NIK`
(absent from `Cslib/`) would likely rescue it.

Phase 20 rated this **LOW** uncertainty (*"the union of a chain of contexts is genuinely routine"*),
judging from signatures + `Deriv.mono`. That looks optimistic: `Deriv.mono` is **monotonicity** —
the easy direction. The chain step needs the **reflection** direction, which is where the cofinite
encoding bites. **A successor must settle this before attempting the Zorn argument.**

---

## 5. Source-to-Implementation Mapping (H3)

All pages **PDF-verified from rasters**. BibKey `Simpson1994`, `references.bib:86`.

| Source claim | Page | Lean target | Notes |
|---|---|---|---|
| Lemma 5.3.1 statement | p. 92 | *(blocked)* | Target type `TPrime` is empty |
| Zorn over whole contexts, fixed coinfinite `V'` | p. 92 | *(blocked)* | **Route CONFIRMED verbatim** |
| Chain union "easily seen" | p. 92 | *(blocked)* | **Obstacle** — cofinite encoding, §4 |
| Clause 1: `Γ ⊢^𝒯_G x:A ⟹ x:A ∈ Γ` | p. 92 | `Context.lean:219` | **DEFECT** — type-wide ⟹ `TPrime` empty |
| *"Consistency is immediate, because `Δ ⊬_H x:A`"* | p. 93 | `NIK.efq` | **DEFECT** — needs cross-label `(⊥E)` |
| `(⊥E)`: `x:⊥ / y:A` | p. 69 (**raster only**) | `NIK.efq` | **DEFECT** — transcribed label-local |
| `(∨E)`: major `x:A∨B`, concl. `y:C` | p. 69 (**raster only**) | `NIK.orE` | **DEFECT** — transcribed label-local |
| `(◇E)` freshness ⟹ diamond clause | p. 93 | *(blocked)* | Reductio here is **real**, unlike `clModel`'s |
| `R^𝒯_(H,Δ)(x,y)` iff `xRy` in `H` (**raw**) | p. 94 | *(Phase 22)* | Plan v3 says `𝒯-Comp(H)` — **wrong**, see §6 |
| *"for all `y` **in `H`**"* (5.3.2 statement) | p. 94 | *(Phase 22)* | Corroborates blocker 1 independently |
| Prime lemma is choice-free in principle | p. 93 | — | Simpson: Zorn avoidable but "laborious"; **use Zorn** |

### Discrepancies where the PDF overrides another source

1. **Figure 4-1's text layer** is destroyed; only the raster carries the rule shapes. Two defects
   were invisible to every text-based reading of this document, including all prior dispatches.
2. **Phase 20's scope verdict** ("blocker lands on Phase 23, not Phase 21") — **refuted**, §2.
3. **Phase 20's LOW rating** of the chain-union step — **looks optimistic**, §4.

---

## 6. Carry-forward for Phase 22 (recorded, not acted on, per dispatch §6)

**Plan v3's Phase 22 spec is wrong; Phase 20's correction is CONFIRMED independently.** p. 94:
`R^𝒯_(H,Δ)(x,y)` iff *"`xRy` in `H`"* — the **raw** relation — justified by *"because
`(D^𝒯_(H,Δ), R^𝒯_(H,Δ)) = H`"*, a sentence unintelligible under the closure reading.

**Phase 20's residual uncertainty here is now largely discharged.** It flagged LOW-MEDIUM
confidence because it had not read pp. 95-98. Lemma 5.3.2's `□`-case (p. 95) reads *"`yRz` in
`H'`"* and its `◇`-case *"`yRz` in `H`"* — **raw throughout; no closure reading appears anywhere in
5.3.2.** Correct plan v3's Phase 22 to the raw relation.

---

## 7. Adversarial Self-Verification (H4)

| Claim | Refutation attempt | Outcome |
|---|---|---|
| `TPrime 𝒯` empty for all `𝒯` | Tried to escape via: (a) `𝒯`-dependence — no, the driver is premise-free and never mentions `𝒯`; (b) `Atom`-dependence — no, universe-polymorphic, `.imp .bot .bot` exists for every `Atom`; (c) `impI` having a hidden side condition — no, checked the constructor: `G` and `Γ` are free, `x` unconstrained; (d) `Deriv` needing a nonempty witness list — no, `Γ₀ = []` discharges `∀ ψ ∈ [], ψ ∈ Γ` vacuously. | **HOLDS** — mechanized |
| `𝒯 = ∅` escapes it | This was the dispatch's premise and I tried hard to preserve it. `classicalModel_empty` does make clause 0 vacuous — but clause 1 is untouched by `𝒯`. | **REFUTED** — Phase 21 is blocked |
| `(⊥E)`/`(∨E)` divergence is real, not an OCR artifact | Read the raster directly at p. 69; the labels are legible and unambiguous (`x:⊥` over `y:A`; `x:A∨B` with `y:C` conclusion). Cross-checked against 5.3.1's usage on p. 93 — the proof *requires* exactly these shapes, which is independent corroboration from a different page. | **HOLDS** |
| The divergences are alternative encodings, not weakenings | Tried to derive the printed rules from CSLib's. Could not — and proved the converse (`efq_of_efqCrossLabel`, `orE_labelLocal_of_orECrossLabel`), so CSLib's are the diagonal/restriction. | **HOLDS** — strict weakenings |
| Phase 21's route (Zorn over whole contexts) is wrong | Checked against p. 92 verbatim. The route is exactly what Simpson does. | **REFUTED** — route confirmed |
| I should repair `Cslib/` and proceed | Territory contract (§7) forbids it; Phase 20 set the precedent of stating-not-applying; and the `efq`/`orE` repairs need a soundness re-check against landed CK/CT/CS4/CS5 results that is itself phase-sized. | **NO** — escalate |

### Uncertainty, flagged rather than asserted

- **MEDIUM-HIGH**: the `efq`/`orE` repairs are *stated* and shown to be strict strengthenings, but
  **soundness of the strengthened rules was NOT verified** against the landed CK/CT/CS4/CS5
  soundness results or task-509's `cs5FC''`. Semantically the cross-label rules look fine (no
  interpretation makes `ρ(x) ⊩ ⊥`), but this is an argument, not a proof. **This is the repair
  phase's main risk.**
- **MEDIUM**: the chain-union obstacle (§4) is identified but unmechanized in both directions — I
  did not prove chain closure fails, only that the natural finite-support strategy does not go
  through.
- **MEDIUM**: no inhabitant of the *repaired* prime-context type was constructed. I claim the
  repairs remove *these four* contradictions; I do **not** claim they make the type inhabited.
  A fifth driver could exist. **Hence the recommended inhabitedness gate.**
- **LOW**: `Deriv.imp_self` uses `.imp .bot .bot` concretely; any `A` works, and the general
  `NIK.imp_self` is stated for arbitrary `A`.

---

## 8. Plan Deviations

| Deviation | Reason |
|---|---|
| **The Zorn argument was not attempted.** | Its target type is provably empty. Writing it would have been unfalsifiable busywork against `IsEmpty`, and any "success" would have been a vacuous-proof artifact — the exact failure mode the dispatch's §5 `do_not` and the vacuous-definitions prohibition exist to prevent. |
| **No strategic-sorry skeleton was landed**, though §1 sanctioned one on a split. | A skeleton is the right split artifact when the *proof* is unfinished. Here the *statement* is unsound-by-emptiness; a skeleton would encode a shape that the repair will change (all four clause types are affected). The 11 sorry-free blocker declarations are strictly more useful and carry zero debt. `sorry_inventory` is empty — by construction, not by omission. |
| **Full CI pipeline not run.** | Zero changes under `Cslib/`, so no mainline surface changed and no CI-visible regression is possible. `checkInitImports` does not apply to `probes/` (not a lake target). The probe was verified with `lake env lean` + `#print axioms` on every declaration. |
| **Phase heading marked `[BLOCKED]`, not `[PARTIAL]`.** | Per the escalation protocol: the phase cannot be completed as written at any `𝒯`, and the blocker is upstream in `Cslib/`, outside this phase's territory. |

---

## 9. Recommendation

**Do not re-dispatch Phase 21 as written.** Its target type is provably empty; a successor would
burn a dispatch rediscovering that.

1. **Insert a repair phase** (mainline `Cslib/`) covering **all four** transcription defects —
   `deductiveClosure` (blocker 1), `clModel` (Phase 20), `efq` and `orE` (blockers 2-3) — **with a
   soundness re-check** of the landed CK/CT/CS4/CS5 results and `cs5FC''` against the strengthened
   rules. Also settle Phase 20's flagged `equivalence_of_classicalModel_TS5` consequence (type-wide
   `Equivalence` vs. equivalence on `G.X`), still an unmade design choice.
2. **Gate on inhabitedness** before re-dispatching: construct an inhabitant of the repaired type at
   `𝒯 = ∅`, or prove every emptiness chain fails. **Phases 20 and 21 both dispatched proof work
   against an already-empty type**; a cheap inhabitedness gate would have caught both, early and
   at a fraction of the cost. This is the process lesson of this dispatch.
3. **Settle the chain-union obstacle** (§4) — the crux, upstream of the whole Zorn argument.
4. **Then re-dispatch Phase 21.** Its mathematics is untouched: the transcription is complete and
   recorded above, the route is confirmed verbatim, and Phase 20's `(R_Υ)` mechanism still stands.
