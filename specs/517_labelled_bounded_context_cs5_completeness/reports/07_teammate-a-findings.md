# Teammate A (Primary Angle) — Simpson1994 Ch.7-8 Labelled/Bounded-Context Route to `cs5_completeness`

**Task**: 517 | **Teammate**: A | **Artifact**: 07 | **Reference grounding tier**: 1 (literature-backed)
**BibKey**: `Simpson1994` → `simpson_1994_intuitionisticmodallogic` (global corpus, 208 chunks)
**Directive honored**: "the mathematically correct way to proceed, cutting no corners."

---

## Key Findings

### KF1 (HEADLINE, negative). My assigned angle — Ch.7-8 bounded contexts — is a DEAD END for `cs5_completeness`. Simpson's Ch.7-8 machinery does not cover IS5, by his own scope definitions.

Two independent, verbatim scope facts kill it:

1. **Bounded contexts are a *decidability/FMP* device, not a completeness device.** Section 8.2.1
   states its own purpose: it *re-proves* completeness "using a 'bounded' model" so that a *finite*
   birelation model can be extracted. The completeness content is imported, not created:
   > "The construction closely follows **the earlier completeness proof of Section 5.3**. However,
   > this time we build the model out of the bounded contexts introduced in Section 7.3.1."
   > — chunk `e545394dc5442127` (= `chunk_0163.md`)

   Task 517 needs completeness, not FMP and not decidability. Boundedness is pure overhead.

2. **T_S5 is not in Ch.7's scope at all.** Section 7.3 fixes the family of theories it handles:
   > "we prove the decidability of the consequence relation of N_ND(𝒯) for any 𝒯 in the family …
   > **Dec_ND = {∅, {χ_D}, {χ_T}, {χ_B}, {χ_D,χ_B}, {χ_T,χ_B}}** … Thus, **including the known
   > result about IS5 (see page 57)**, we have, by the results of Chapter 6, that theoremhood is
   > decidable for any of the intuitionistic modal logics in Figure 7-5"
   > — `chunk_0132.md:13`

   `T_S5` (= {χ_T,χ_B,χ_4} or {χ_T,χ_5}) is **absent from Dec_ND**. IS5 enters Figure 7-5 only as an
   *imported known result*. Ch.8's `Dec_L = {IK, IKD, IKB, IT, IKDB, IKTB, IS5}` (`chunk_0158.md`)
   *lists* IS5, but Theorem 8.2.1's proof runs through Section 7.3.1's bounded contexts — i.e.
   through `Dec_ND`, which excludes T_S5. Simpson closes the gap with a remark, not a proof:
   > "our techniques **do extend** to establish **the known result** that IS5 has the finite model
   > property. Again, the proof for IS5 is **quite simple**, because contexts can be **set-indexed
   > rather than tree-indexed**" — chunk `1dcc4e367e672a83` (= `chunk_0174.md:13`)

   And the Ch.7 counterpart remark routes IS5 to a *different calculus entirely*:
   > "For the easiest proof, it is probably best to use a sequent calculus with sequents of the form
   > Γ ⇒ x:A. **There is no need to keep account of any graph structure because, for IS5, the
   > visibility relation can be assumed to be total.** (The resulting proof system is just the
   > intuitionistic restriction of **Kanger's sequent calculus** for classical S5 [47].)"
   > — `chunk_0149.md:3`

**Verdict**: the dispatch's premise — that Ch.7-8 is "the rigorous IS5 proof Simpson actually carries
out" — is **false**. Simpson carries out Ch.7-8 for the *tree-indexed* Dec_ND logics and defers IS5 to
(a) an external known result and (b) an uncarried "set-indexed / Kanger" remark. **The task title
`labelled_bounded_context_cs5_completeness` is a misnomer inherited from plan 01.** Lemma 8.2.5 and
Lemma 8.2.6 are real and quoted below, but they are the *bounded* re-proofs; their unbounded
originals in Ch.5 are what the task actually needs.

### KF2 (HEADLINE, positive). The escape from `cs5_symmetric_tail_box_gap` is REAL, and I can name the exact structural feature. It is not "T-prime contexts aren't prime" — they *are* prime. It is that **one labelled context IS the simultaneous maximal pair** the gap lemma demands.

This is the load-bearing question, and I did not accept it on faith. Working it through:

**Step 1 — the gap lemma's hypotheses ARE satisfied in Simpson's model.** Let `Th(w,d) = {B | d:B ∈ Δ_w}`
for a T-prime context `w = (H,Δ)` and label `d`.
- `Th(w,d)` **is prime**: Δ has the disjunction property ("suppose y:B ∨ C ∈ Δ … either y:B ∈ Δ or
  y:C ∈ Δ", `chunk_0103.md:3`). So `hT : QuasiPrime T` ✓.
- `R_w(d,d') ⟹ boxInv(Th(w,d)) ⊆ Th(w,d')` by (□E) + deductive closure ✓ (`hsub`).
- symmetry of `R_w` ⟹ `boxInv(Th(w,d')) ⊆ Th(w,d)` ✓ (`hsym`).

So **`cs5_symmetric_tail_box_gap` (CS5.lean:712) is TRUE of Simpson's construction.** Its conclusion
`p ∈ T` genuinely holds there. **The escape is NOT that the lemma fails to apply.**

**Step 2 — why it is nevertheless not a blocker.** The lemma's hypothesis is `hq : q ∉ H`, at a
**fixed head H**. The IL-model box clause quantifies over the ≤-future:
> "w,d ⊩ □A iff **for all w' ≥ w**, for all d' ∈ D_{w'}, R_{w'}(d,d') implies w',d' ⊩ A"
> — `chunk_0098.md` (Section 5.2, verbatim)

To refute `y:□p` you need a witness at a **strictly larger context**, and `q ∉ H` is **not preserved**
under context extension. At the larger context the gap lemma simply **does not fire**.

**Step 3 — the mechanism, verbatim.** Simpson's canonical-model-lemma box case:
> "Let z be some variable **not in H**. Suppose, for contradiction, that Δ ⊬^T_{H∪{yRz}} z:B. Then,
> by the bounded prime lemma, there is a 𝒯-prime bounded context (H′,Δ′) ⊇ (H ∪ {yRz}, Δ) such that
> Δ′ ⊬^T z:B. But then (H′,Δ′) ≥ (H,Δ), and yRz in H′ and z:B ∉ Δ′ … Hence, by **(□I)**, Δ ⊢^T_H y:□B."
> — `chunk_0167.md:5`

**The prime lemma is applied to the graph *extended with a fresh label* `H ∪ {yRz}`, and it produces
ONE T-prime context Δ′ by ONE Lindenbaum maximization.** The "head" is `Th(Δ′,y)`; the "tail" is
`Th(Δ′,z)`. **Both are restrictions of the same single object Δ′, built by the same maximization.**

That is *precisely* what `CS5.lean:705-706` names as the open problem:
> "The box-backward case must therefore move to a strictly larger head H′ ⊇ H (here: one containing
> q) … **That circularity is the real open problem: H′ and T must be built as a simultaneous maximal
> pair, not sequentially (Phases 8-10).**"

**Simpson's prime lemma on `(H ∪ {yRz}, Δ)` IS the simultaneous maximal pair.** The label is the device
that lets one prime object carry both head and tail. The eigenvariable/freshness side-condition of
(□I) is what makes the head non-fixed.

**Step 4 — hand-verified consistency (H4).** I checked the gap lemma cannot be turned into a
contradiction against Simpson's construction. Take `y:□(p ∨ □q) ∈ Δ`, `y:□p ∉ Δ`, `y:q ∉ Δ`; set
`B := p`, `z` fresh; prime lemma gives `(H′,Δ′)` with `z:p ∉ Δ′`. Now apply the gap lemma at Δ′:
`y:□(p∨□q) ∈ Δ′` (monotone). *If* `y:q ∉ Δ′`, the lemma forces `z:p ∈ Δ′` — contradiction. **Therefore
`y:q ∈ Δ′` is forced.** Is that consistent? Yes: Δ′ is maximal w.r.t. `Δ′ ⊬ z:p`, and the Lindenbaum
construction is **free to select `z:□q` (not `z:p`) together with `y:q`** — `z:□q` + `zRy` (symmetry)
yields `y:q`, which is now *in* Δ′, so nothing derives `z:p`. **No contradiction; the model exists.**
In the `CS5Canonical` design `H` is *fixed* with `q ∉ H`, so this freedom does not exist. **That freedom
is the whole escape.**

Consequently `cs5Incest_forces_symm` (CS5Canonical.lean:643) and `cs5TwoSidedR_iff_cs5Tail`
(CS5Canonical.lean:511) are also non-binding: they constrain *cs5Tail-shaped, theory-to-theory*
relations. In `B_K` the modal relation never relates two theories — see KF3.

### KF3. `B_K` satisfies `cs5FC''`/`cs5FCIncest` — I checked all five conjuncts by hand. It does NOT satisfy the stronger `cs5FC`.

Simpson's Section 8.1.1 construction (`chunk_0152.md:3`, verbatim):
> `W′ = {(w,d) | w ∈ W and d ∈ D_w}`, `(w,d) ≤′ (w′,d′) iff w ≤ w′ and d = d′`,
> `(w,d) R′ (w′,d′) iff w = w′ and R_w(d,d′)`, `V′((w,d)) = {α | α_w(d)}`.

**The two dimensions are orthogonal**: `≤′` grows the *context* holding the *label* fixed; `R′` moves the
*label* holding the *context* fixed. Symmetry of `R′` is symmetry of the graph `T-Comp(H)` — a
**classical first-order graph fact** (Lemma 8.2.5), discharged by the **(R_B) structural rule**, never by
cross-theory negation-completeness. *This is the "label/graph fact rather than theory-membership fact"
the dispatch asked me to identify.*

Checking against `CKExtension.lean:184`, writing `w ≤ w″` and using monotonicity `R_w ⊆ R_{w″}`
(from `H ⊆ H′` and monotonicity of `T-Comp`) plus `R_w` refl/symm/trans (Lemma 8.2.5):

| `cs5FC''` conjunct | Holds in `B_K`? | Witness |
|---|---|---|
| `∀ w, r w w` | ✓ | reflexivity of `R_w` |
| plain trans `r w u → r u t → r w t` | ✓ | same context; trans of `R_w` |
| plain symm `r w u → r u w` | ✓ | symm of `R_w` |
| `r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t` | ✓ | `v := (w″,d)`; `R_{w″}(d,d′)` (mono) + `R_{w″}(d′,e)` → trans |
| `r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t` | ✓ | `t := (w″,d)`; `R_{w″}(d,d′)` (mono) + symm |
| `cs5Incest` (`r w u → ∃ u', u ≤ u' ∧ r u' w`) | ✓ | `u' := u`; symm of `R_w` |

**`cs5FC` (CKExtension.lean:159) FAILS in `B_K`**: its ≤-composed transitivity
`r w u → u ≤ u' → r u' t → r w t` would need `r` to bridge contexts `w` and `w″`, but `R′` requires
equal contexts. **This retroactively validates task 509's `cs5FC''` pivot**: `cs5FC''` is not merely
convenient, it is *the frame class `B_K` actually inhabits*. `cs5_completeness` must target
`CKValidFC cs5FC''` (or `cs5FCIncest`), **not** `cs5FC`.

### KF4 (ROUTING — the dispatch's highest-value question). Answer: **Ch.7-8 does NOT bypass Ch.6. Ch.6 IS on the critical path, and report 02's ~85% "Lemma 6.1.2 not required" is, in my reading, WRONG — it rests on a one-sentence sketch that Simpson delegates to a source not in our corpus.**

I was asked to find a routing error. I found one — but it is not the one hypothesized, and it does not
remove C5.

**Simpson names his own IS5 route, verbatim:**
> "**It will follow from the results of Chapters 5 and 6** that all the intuitionistic modal logics
> IKS₁…Sₙ of Theorem 3.3.4 satisfy meta-logical completeness." — `chunk_0075.md:3`

**Ch.6's scope explicitly includes T_S5:**
> "**Theorem 6.2.1** The following are equivalent: 1. A is a theorem of IK + Ax(𝒯). 2. A is a theorem
> of N_ND(𝒯). **For any 𝒯 ⊆ {χ_D, χ_T, χ_B, χ_4, χ_5}**, we have that IK + Ax(𝒯) is just the
> appropriate IKS₁…Sₙ" — `chunk_0114.md:9`

**And Lemma 6.1.2 (the tree surgery) is unavoidably inside it:**
> "**Lemma 6.2.3** … 1. A is a theorem of IK + Ax(𝒯). 2. A is a theorem of N_ND + Ax(𝒯). This is
> proved by making **trivial modifications to the proof of Theorem 6.1.1**. In particular, **Lemma
> 6.1.2 is modified to: if G is a finite tree then Ax(𝒯); Γ ⊢_G x:A if and only if (Γ ⊢_G x:A)^ is a
> theorem of IK + Ax(𝒯)**. The proof applies verbatim, apart from one extra trivial case."
> — `chunk_0117.md:3`

**This is decisive against the "S5 collapses the tree" hope.** Theorem 6.2.1 is proved in two steps:
(1) `N_ND(𝒯) ≡ N_ND + Ax(𝒯)` (Lemma 6.2.2, `chunk_0115.md`/`chunk_0116.md` — the (R_χ) rules are
*internalized as axioms*); (2) `IK + Ax(𝒯)` axiomatizes `N_ND + Ax(𝒯)` via Lemma 6.1.2. **After step
(1) there are no (R_χ) rules, so the graph is a genuine finite tree** — Simpson's set-indexed/total-
visibility simplification (`chunk_0149.md`) applies to the *Ch.7 sequent calculus*, **not** to Ch.6.
**C5 (`pathSpine`) is therefore NOT bypassable via an S5 specialization.** I want to be blunt that this
contradicts the most attractive shortcut available.

**Why report 02's alternative is corner-cutting.** Report 02 routes around Ch.6 via Theorem 3.3.4.
Here is Theorem 3.3.4's *entire* proof:
> "**Theorem 3.3.4** The following are equivalent: 1. A is a theorem of IKS₁…Sₙ. 2. A is valid in all
> birelation models of IKS₁…Sₙ. In each case the soundness direction is routine and the completeness
> direction is proved by showing that **the canonical model, defined analogously to that used in the
> proof of the completeness of IK, is indeed a birelation model of IKS₁…Sₙ**." — `chunk_0068.md:29`
> "The cases IK, IT, IKTB, IS4 and **IS5** of Theorem 3.3.4 **appear explicitly in Fischer Servi [24]**."
> — `chunk_0068.md:41`

That is a **one-sentence sketch plus an external citation**. Simpson proves nothing for IS5 here. And
CSLib has **three mechanized, sorry-free obstructions** against exactly the "canonical model … analogous
to IK's" formulation. Simpson's own aside —
> "these results are obtained **more easily** by considering the Hilbert systems directly (as in
> Section 3.3)." — `chunk_0158.md`

— is an **unsubstantiated claim resting on Fischer Servi [24]**, and CSLib has already spent multiple
dispatches demonstrating it is *not* easier; it is (as formulated) blocked.

**Both "shortcut" roads bottom out in the same missing source**: Ch.7-8's IS5 → "the known result about
IS5 (see page 57)" → Fischer Servi/Bull; Thm 3.3.4's IS5 → "appear explicitly in Fischer Servi [24]".

> ### ⚠ BLOCKING OBLIGATION (named, per instruction)
> **`FischerServi1984` is NOT in the corpus** (confirmed: no match in
> `~/Projects/Literature/index.json`). **Every** Simpson route that claims IS5 birelation completeness
> *without* Chapters 5+6 discharges its obligation by citing Fischer Servi. Until that source is
> obtained and read, **no report — including report 02 — is entitled to claim a Ch.6-free path to
> `cs5_completeness` on Simpson's authority.** Simpson's text does not contain such a proof.
> **Recommended action: `/literature` ingest Fischer Servi 1984, "Axiomatizations for some
> intuitionistic modal logics", Rend. Sem. Mat. Univers. Politecn. Torino 42 (1984) 179-194.** This is
> the single highest-value unblock available and it is cheap relative to C5.

### KF5 (DEFECT, meets the 4-element bar). `TS5 := {GeomAxiom.T, GeomAxiom.Five}` does not match `CS5ModalAxiom` under Theorem 6.2.1's `Ax(-)` correspondence.

1. **Discrepancy.** Simpson's Figure 3-7 (`chunk_0068.md`) / Figure 6-3 (`chunk_0115.md`) fix `Ax(-)`:
   - `χ_T ↦ (□A ⊃ A) ∧ (A ⊃ ◇A)` → `tBox`, `tDia`
   - `χ_B ↦ (◇□A ⊃ A) ∧ (A ⊃ □◇A)` → `bDia`, `bBox` — **exact match** with CS5.lean:154-155
     ("`bDia` (`◇□A → A`) … `bBox` (`A → □◇A`)")
   - `χ_4 ↦ (□A ⊃ □□A) ∧ (◇◇A ⊃ ◇A)` → `fourBox`, `fourDia`
   - `χ_5 ↦ (◇□A ⊃ □A) ∧ (◇A ⊃ □◇A)` → **`5Box`, `5Dia` — not constructors of `CS5ModalAxiom`**

   So `Ax({χ_T,χ_5}) = {tBox,tDia,5Box,5Dia}` = **IKT5**, whereas
   `CS5ModalAxiom = {tBox,tDia,bBox,bDia,fourBox,fourDia}` = **IKTB4**. CS5.lean:156-157 says so
   outright: "Axiomatized via **`B` (symmetry), not the classical euclidean/`5` axiom**".
2. **Current behavior.** `Labelled/Context.lean:247`: `def TS5 : Set GeomAxiom := {GeomAxiom.T, GeomAxiom.Five}`.
   Theorem 6.2.1 at this `𝒯` yields **`IKT5 ⟺ N_ND(TS5)`**, which does **not** close `cs5_completeness`
   (stated for `CS5ModalAxiom`). Bridging would require an **unproved constructive** `IKT5 ⟺ IKTB4` —
   Simpson merely asserts it ("Again IS5 is also axiomatized by IKTB4", `chunk_0068.md`), classically.
   Given this task has twice found transcribed schemas false as literally stated, importing a classical
   equivalence unproved is exactly the corner the user forbade.
3. **Required behavior.** `def TS5 : Set GeomAxiom := {GeomAxiom.T, GeomAxiom.B, GeomAxiom.Four}`.
   Then `Ax(TS5) = CS5ModalAxiom` **definitionally**, and Theorem 6.2.1 lands
   `CS5 ⊢ A ⟺ N_ND(TS5) ⊢ x:A` with **no** unproved Hilbert equivalence on the critical path.
4. **Isolation.** One line. Downstream is *unaffected or simplified*: `equivalence_of_refl_eucl`
   (Context.lean:260) currently *derives* symm/trans from refl+eucl; under `{T,B,Four}` they are
   **direct** (`.B`/`.Four` are literally symm/trans per `GeomAxiom.Holds`, Deduction.lean:126-127),
   so `equivalence_of_classicalModel_TS5` and its Phase-8 `cs5FCIncest` consumers get *easier*.
   `TClosure` already carries `.symm`/`.trans` constructors (Deduction.lean:146-148), so the closure
   side needs no new cases.

### KF6 (minor risk, not a defect). `GeomWitnessClosure := True` (Context.lean:138) is a `def Foo := True`, which `.claude/rules/lean4.md` prohibits. **I judge this acceptable as landed**: its docstring justifies it precisely (no k-ary witness constructors exist in the current `Label` type, so the clause is vacuous *by construction*, not by evasion), it is isolated for a future `χ_D` extension, and `χ_D ∉ T_S5` so it is **off the CS5 critical path**. Flagging only because `lake lint` / CSLib reviewers may object at PR time, and because a future `χ_D` extension would silently inherit a vacuous clause.

---

## Recommended Approach

**Route 2 — Ch.5 + Ch.6 + §8.1.1. This is the only route Simpson actually carries out for IS5, and it
is the mathematically correct path.** Track C's *chapter* choice is correct; its *framing* ("bounded
context") is wrong and should be dropped.

```
CS5 ⊬ A
  └─[Thm 6.2.1 (2⇒1), via Lemma 6.2.2 + Lemma 6.2.3 + Lemma 6.1.2 tree surgery]  ← C1-C5 (Track C)
CS5 = IK + Ax(T_S5) ⊬ A  ⟹  N_ND(T_S5) ⊬ x:A
  └─[Thm 5.2.1 (3⇒1): prime lemma → T-prime context (H,Δ), Δ ⊬ x:A]            ← Ch.5, UNBOUNDED
IL-model K over T-prime contexts, (H,Δ),x ⊮ A     [canonical model lemma]
  └─[§8.1.1: B_K = {(w,d)} ; Lemma 8.1.2 w,d ⊩ A ↔ (w,d) ⊩_{B_K} A]
birelation countermodel B_K, and B_K ⊨ cs5FC''    [KF3, all 5 conjuncts hand-checked]
  ⟹ ¬ CKValidFC cs5FC'' A   ∎  cs5_completeness
```

Ordered actions:

1. **[CHEAP, DO FIRST] Ingest Fischer Servi 1984** (KF4 blocking obligation). It is the sole authority
   behind *both* claimed shortcuts. If FS1984 contains a real IS5 birelation completeness proof, it may
   dominate Route 2 entirely and retire C5. If it does not, Route 2 is confirmed as the only path and
   report 02's 85% must be retracted. **Either outcome is decision-changing; the cost is one
   `/literature` call.** Do not commit further dispatches to C5 before this resolves.
2. **[ONE LINE] Fix `TS5` to `{GeomAxiom.T, GeomAxiom.B, GeomAxiom.Four}`** (KF5). Removes an unproved
   constructive `IKT5 ⟺ IKTB4` from the critical path and simplifies Phase 8.
3. **[RETARGET] State `cs5_completeness` against `CKValidFC cs5FC''` (or `cs5FCIncest`), never
   `cs5FC`** (KF3). `B_K` provably does not inhabit `cs5FC`.
4. **[REFRAME] Drop "bounded" everywhere** (KF1). Use Ch.5's unbounded `prime lemma` (`chunk_0103.md`)
   and unbounded `canonical model lemma`, not Lemma 8.2.4/8.2.6. Bounded variants buy only FMP, which
   517 does not need — **and they are out of scope for IS5 anyway (`T_S5 ∉ Dec_ND`)**. Note Ch.5's
   prime lemma needs **no choice** ("the prime lemma can actually be proved without using any form of
   the axiom of choice", `chunk_0103.md:3`) — relevant to the axiom-free requirement; the existing
   Zorn-based plan is acceptable but not forced.
5. **[KEEP] C5 (`pathSpine`) stays on the critical path.** I could not find a source-grounded bypass,
   and KF4 shows the S5/set-indexed simplification does **not** reach Ch.6. Only §8.1.1 uses the
   "tree-free" observation ("nowhere in the proof of completeness have we used the assumption that G is
   a tree", `chunk_0153.md:3`) — that helps §8.1, **not** Lemma 6.1.2, whose statement begins "**If G is
   a finite tree**" (`chunk_0111.md:3`).

**What genuinely transfers** (reuse-first): `Proposition`/`Proposition.map` (Basic.lean);
`DerivationTree`/`Derivable`; `CS5ModalAxiom`; task-512's `cs5_axiom_sound_incest`/`cs5_soundness_incest`
(supplies the soundness half — Route 2 supplies only completeness); and the **already-landed labelled
framework**: `Labelled/Syntax.lean` (202 ln), `Labelled/Deduction.lean` (312 ln, `NIK`/`TClosure` — note
`NIK.boxI` at :229 already carries the cofinite `L`/`hL : L.Finite` **eigenvariable** device, which KF2
shows is *the* escape mechanism), `Labelled/Context.lean` (275 ln, `Context`/`TPrime`/`Deriv`/`TS5`).
The C1-C4 assets (`Conj`/`Tele`, (6.7), (6.8), `LTree`/`star`/`fullSubtree`/`prune`) are all Lemma-6.1.2
machinery and are **preserved** under this recommendation.

**Zero-debt note**: no step above requires `sorry` or a new axiom. If FS1984 turns out to contain no
usable IS5 proof *and* C5 resists, the correct outcome is **[BLOCKED]** with C5 named — not a deferred
`sorry`.

---

## Source-to-Implementation Mapping (H3)

| Source statement | BibKey + chunk ID | Lean target | Reuses (existing CSLib decls) | Risk |
|---|---|---|---|---|
| Thm 5.2.1 satisfaction clauses for IL-models | `Simpson1994` `chunk_0098.md` | `Labelled.ILForces` | `Proposition`, `Label`, `Graph` | LOW — direct transcription |
| Prime lemma (unbounded, 4 conditions: consistency, deductive closure, disjunction property, diamond property) | `Simpson1994` `chunk_0103.md:3` | `Labelled.prime_lemma` | `TPrime` (Context.lean:224), `Deriv`, `Context.le` | **MED** — Zorn chain-closure over `Set`; choice-free variant exists in source |
| Canonical model lemma, **box case** (fresh `z`, prime lemma on `H ∪ {yRz}`, (□I)) — **the KF2 escape** | `Simpson1994` `chunk_0167.md:5` | `Labelled.canonical_model_lemma` | `NIK.boxI` (Deduction.lean:229, cofinite `L` eigenvariable), `TClosure.symm` | **HIGH** — the real crux of Ch.5; but *escapes* all 3 guardrails (KF2) |
| Thm 5.2.1 (3⇒1) completeness | `Simpson1994` `chunk_0105.md:3` | `Labelled.nik_completeness_IL` | `Deriv`, `TPrime` | MED |
| Lemma 6.1.2 (`G` a **finite tree** ⟹ `Γ ⊢_G x:A ↔ (Γ ⊢_G x:A)^` thm of IK) | `Simpson1994` `chunk_0111.md:3` | `Labelled.lemma_6_1_2` | C1 `Conj`/`Tele`, C2 (6.7), C3 (6.8), C4 `LTree`/`star`/`prune` | **HIGH — C5 `pathSpine`, the true crux; NOT bypassable (KF4)** |
| Lemma 6.2.2 (`N_ND(𝒯) ≡ N_ND + Ax(𝒯)`; (R_χ) internalized) | `Simpson1994` `chunk_0115.md`, `chunk_0116.md` | `Labelled.nik_eq_nik_ax` | `NIK`, `TClosure`, `CS5ModalAxiom` | MED — (R_B) case "very easy" per source |
| Lemma 6.2.3 / Thm 6.2.1 (`IK+Ax(𝒯) ⟺ N_ND+Ax(𝒯)`) | `Simpson1994` `chunk_0117.md:3`, `chunk_0114.md:9` | `Labelled.thm_6_2_1` | `Derivable`, `DerivationTree` | MED (given 6.1.2) — "one extra trivial case" |
| `Ax(χ_T/χ_B/χ_4)` = Figure 3-7 / 6-3 schemas | `Simpson1994` `chunk_0068.md`, `chunk_0115.md` | **fix `TS5` → `{T,B,Four}`** | `GeomAxiom`, `CS5ModalAxiom` | **LOW — one line; KF5 defect** |
| §8.1.1 `B_K` construction + Lemma 8.1.2 | `Simpson1994` `chunk_0152.md:3,7` | `Labelled.BK`, `Labelled.lemma_8_1_2` | `CKForces`, `Preorder` | LOW-MED — "an easy induction" |
| Thm 8.1.4 **completeness half** (`B_K` is a birelation model of 𝒯; no tree needed) | `Simpson1994` `chunk_0158.md`, `chunk_0153.md:3` | `Labelled.BK_cs5FC''` | `cs5FC''` (CKExtension.lean:184), `equivalence_of_classicalModel_TS5` | **LOW — all 5 conjuncts hand-verified (KF3)** |
| Lemma 8.2.5 (`𝒯-Comp(H) ⊨_cl 𝒯`) — *unbounded analogue* | `Simpson1994` `chunk_0166.md:5` | `TPrime.classicalModel` | `ClassicalModel`, `TClosure` | LOW — already `TPrime` clause 0 |
| — (soundness half) | task 512, landed | `cs5_soundness_incest` | `cs5_axiom_sound_incest` | **NONE — landed** |
| Thm 3.3.4 IS5 (report 02's route) | `Simpson1994` `chunk_0068.md:29,41` | *(not recommended)* | — | **BLOCKED — 1-sentence sketch; delegates to `FischerServi1984`, NOT IN CORPUS** |
| Thm 8.2.1 / Lemma 8.2.4 / 8.2.6 (bounded, FMP) | `Simpson1994` `chunk_0161`–`0174` | *(not needed)* | — | **OUT OF SCOPE — `T_S5 ∉ Dec_ND` (KF1)** |

Non-corpus BibKeys flagged: **`FischerServi1984`** (blocking, KF4). Not consulted this dispatch:
`MarinMoralesStrassburger2021` (relevant — `cs5Incest` is credited to Marin Thm 7.1 `k=l=1,m=n=0`, and
Simpson's χ_{k,l} family `chunk_0114.md` is visibly the same schema; a cross-check is worthwhile but is
Teammate B/C territory), `Pacheco2024` (Track B, closed by A3), `Dosen1985`, `BozicDosen1984`,
`AlechinaMendlerdePaivaRitter2001`, `Wijesekera1990`.

---

## Evidence-Examples

**E1 — Lemma 8.2.5 (verbatim), `chunk_0166.md:5`** — *the symmetry-as-graph-fact anchor*:
> "**Lemma 8.2.5** If (H,Δ) is a 𝒯-prime bounded context then 𝒯-Comp(H) ⊨_cl 𝒯."

and the model definition immediately following (`chunk_0166.md:11`):
> "W = the set of 𝒯-prime bounded contexts, (H,Δ) ≤ (H′,Δ′) iff (H,Δ) ⊆ (H′,Δ′), D_(H,Δ) = the
> underlying set of H, **R_(H,Δ)(x,y) iff xRy in 𝒯-Comp(H)**, α_(H,Δ)(x) iff x:α ∈ Δ. Clearly all the
> conditions on being an IL-model are satisfied by K, in particular, **by Lemma 8.2.5, each
> (D_(H,Δ), R_(H,Δ)) is a classical model of 𝒯**"

`R` is read off the **graph closure**, and the frame theory is satisfied **classically, per world**.
Nothing here is a theory-membership relation. *(Cited as the clearest statement of the mechanism; the
`cs5_completeness` implementation should use the **unbounded** Ch.5 analogue — KF1/KF3.)*

**E2 — Lemma 8.2.6 (verbatim), `chunk_0166.md:13`**:
> "**Lemma 8.2.6 (Bounded canonical model lemma)** Let (H,Δ) be any 𝒯-prime bounded context. If y has
> depth n in H and B ∈ Θ_{d−n} then (H,Δ), y ⊩_K B if and only if y:B ∈ Δ."

Note the **depth-bounded** hypothesis `B ∈ Θ_{d−n}` — an artefact of boundedness (FMP), *absent* from
the Ch.5 unbounded original. Further evidence the bounded layer is overhead for 517.

**E3 — Lemma 8.2.4 (verbatim), `chunk_0164.md:15`**:
> "**Lemma 8.2.4 (Bounded prime lemma)** If (H,Δ) is a bounded context and Δ ⊬ y:B then there is a
> 𝒯-prime bounded context (H′,Δ′) with (H′,Δ′) ⊇ (H,Δ) such that Δ′ ⊬ y:B."

**E4 — the symmetry step, `chunk_0167.md:5`** — *(R_B) discharges the back-clause*:
> "If yRz in H′ then Δ′ ⊢ z:B is derived by an application of (□E). If y = z then, as d_z < d, we have
> χ_T ∈ 𝒯, so Δ′ ⊢ z:B is derived by (□E) followed by (R_T). **Similarly if zRy in H′ then χ_B ∈ 𝒯 and
> the consequence is derived by way of (□E) and (R_B).**"

The symmetric case is discharged by a **structural rule on the graph** — no negation-completeness. This
is the concrete counterpart of KF2/KF3.

**E5 — constructivity of the whole method, `chunk_0175.md:3`** (bears directly on "no new axiom"):
> "the proof of the finite model property is **intuitionistically acceptable**. The only non-overtly
> intuitionistic steps are in the proofs of the bounded prime lemma and the bounded canonical model
> lemma. However, the intuitionistic validity of these proofs is ensured by **the decidability of the
> modal consequence relation**"

**⚠ Adversarial reading**: this is *good* news for the bounded route and **neutral-to-bad** for Route 2.
Route 2 uses the **unbounded** prime/canonical-model lemmas, where **decidability is unavailable** (it is
a Ch.7 result, and `T_S5 ∉ Dec_ND`). So Route 2's prime lemma is **classical** (Zorn/Lindenbaum). *This
is fine for CSLib* — `Classical.choice` is ambient in Lean/Mathlib and is not a "new axiom under
`Cslib/`" — but it means the *metatheory* is classical even though the *object logic* is constructive.
Worth stating explicitly in the plan so no one mistakes it for a defect later. (Ch.5's choice-free
remark, `chunk_0103.md:3`, mitigates but is not needed.)

**E6 — `Dec_L` vs `Dec_ND`, the scope split (KF1)**: `chunk_0158.md` (`Dec_L = {IK, IKD, IKB, IT, IKDB,
IKTB, IS5}` — *logics*, IS5 present) vs `chunk_0132.md:13` (`Dec_ND = {∅, {χ_D}, {χ_T}, {χ_B},
{χ_D,χ_B}, {χ_T,χ_B}}` — *theories Simpson's technique handles*, T_S5 **absent**). The bridge is the
words "**including the known result about IS5 (see page 57)**". This asymmetry is the whole of KF1 and
is easy to miss on a fast read of Theorem 8.2.1's statement alone — which is, I suspect, exactly how
plan 01 acquired the "bounded context" framing.

**E7 — Section 8.1's pathologies are SOUNDNESS-side only**: `chunk_0151.md` (Figure 8-1 "Counterexample
to general soundness"), `chunk_0157.md` ("the **failure of the lifting lemma** is the only obstruction
to a **general soundness** theorem"), vs `chunk_0153.md:3` ("**nowhere in the proof of completeness have
we used the assumption that G is a tree**. Thus the **completeness direction** of Theorem 8.1.1 holds for
arbitrary consequences"). **517 needs only the completeness direction**, so none of Section 8.1's
notorious problems touch the critical path. *This corroborates report 02's instinct that a bridge is
not the obstacle — but the bridge report 02 dismissed (Ch.6) is a different object from the bridge that
is genuinely harmless (§8.1).* I suspect this conflation is the origin of report 02's 85%.

**E8 — Section 8.1.3's completeness caveat, `chunk_0158.md`** — *checked, does not bite*:
> "A second problem arises with completeness. Given an IL-model K, it is **not necessarily the case that
> B_K is a birelation model of 𝒯**. For example, consider what happens if **𝒯 = {∀xy. xRy}**."

Adversarially checked: the counterexample is the **universal relation**, which demands *cross-context*
edges that `B_K`'s `R′` (equal-context) cannot supply. `T_S5 = {χ_T,χ_B,χ_4}` is **not** universal — each
condition is satisfied **within a single context-cluster**, which `R′` does supply. Simpson confirms the
scope: "for the 𝒯 considered, given any IL-model K, **the model B_K is indeed a birelation model of 𝒯**"
(`chunk_0158.md`, Thm 8.1.4). **CSLib's `cs5FC''` is a `≤`-composed *birelational* condition, not the
universal relation** — so the caveat does not apply. Confirmed independently by my conjunct-by-conjunct
check (KF3).

---

## Adversarial Self-Verification (H4)

| Claim I made | Challenge | Outcome |
|---|---|---|
| Ch.7-8 is a dead end (KF1) | "Theorem 8.2.1 *says* `L ∈ Dec_L` and IS5 ∈ Dec_L — so it covers IS5." | **Survives.** 8.2.1's *proof* runs through §7.3.1 bounded contexts, whose scope is `Dec_ND` ∌ T_S5. `chunk_0132.md:13` patches via "the known result about IS5 (see page 57)", and `chunk_0174.md:13` calls the IS5 case an extension of "our techniques", not an instance. Simpson is *loose* here; I take the proof's scope, not the theorem's billing. |
| The escape is real (KF2) | "You showed the gap lemma's hypotheses ARE satisfied — doesn't that mean it fires and kills Simpson too?" | **Survives, and this challenge improved the finding.** My first draft claimed the lemma "does not apply". **Wrong** — `Th(w,d)` *is* prime and both tail clauses *do* hold. **Revised**: the lemma is *true* but *inert*, because `hq : q ∉ H` is not preserved under context extension and the box clause quantifies over the ≤-future. Hand-verified in KF2 Step 4 that the Lindenbaum construction can consistently choose `y:q, z:□q ∈ Δ′` while keeping `z:p ∉ Δ′`. **No contradiction.** |
| `B_K ⊨ cs5FC''` (KF3) | "Countermodel-check it — schemas have been transcribed FALSE twice on this task." | **Survives, with a correction.** Checked all 5 conjuncts + `cs5Incest` individually against `CKExtension.lean:184`. **Found `cs5FC` FAILS** (≤-composed transitivity needs cross-context edges `R′` cannot supply). Recommendation amended: target `cs5FC''`/`cs5FCIncest`, **never** `cs5FC`. Had I asserted `cs5FC` this would have been a third false schema. |
| Ch.6 is on the critical path (KF4) | "Report 02 says 85% not required. You are contradicting a landed report." | **Survives, deliberately.** Report 02's cited basis is Thm 3.3.4 — whose *entire* proof is one sentence delegating IS5 to Fischer Servi (`chunk_0068.md:41`), a source **not in the corpus**. Report 02's *logic* is sound (3.3.4 would indeed bypass Ch.6); its *premise* (that 3.3.4 is available) is unverified and is contradicted by three mechanized CSLib obstructions. I therefore **downgrade report 02's 85% to ~35%** pending FS1984. **I flag this as a direct inter-report conflict for synthesis.** |
| C5 is unavoidable | "Simpson says IS5 is set-indexed and needs no graph structure — surely C5 collapses." | **Survives — and this kills my own most attractive shortcut.** `chunk_0149.md` is about the **Ch.7 sequent calculus** (decidability), not Ch.6. Lemma 6.2.3 internalizes (R_χ) as axioms *first* (`chunk_0116.md`), leaving base `N_ND + Ax(𝒯)` whose graphs **are** finite trees, and Lemma 6.1.2 begins "**If G is a finite tree**" (`chunk_0111.md:3`). **No source-grounded bypass found. I report this against my own preference.** |
| `TS5` defect (KF5) | "Maybe IKT5 = IKTB4 constructively, so `{T,Five}` is fine." | **Partially survives.** Simpson *asserts* it (`chunk_0068.md`) but proves nothing; it is a classical fact. It may well be true constructively — but it is **unproved and on the critical path**, which the user's directive forbids. The fix is one line and makes `Ax(TS5) = CS5ModalAxiom` *definitional*, removing the question entirely. Recommendation stands as a **defect**, though a benign one. |
| `GeomWitnessClosure := True` | "`def Foo := True` is prohibited — is this a hidden `sorry`?" | **Withdrawn as a defect.** Vacuous *by construction* (no k-ary witness constructors in `Label`), documented, isolated, and `χ_D ∉ T_S5` so off the critical path. Demoted to a lint/PR-time note (KF6). Reporting the downgrade rather than inflating a finding. |
| Route 2 is axiom-free | "Ch.5's prime lemma is a Lindenbaum/Zorn argument." | **Amended, not withdrawn** (E5). `Classical.choice` is ambient in Mathlib and is **not** a new axiom under `Cslib/`, so the zero-debt bar is met — but the *metatheory* is classical while the object logic is constructive. Stated explicitly so it is not later mistaken for a defect. Note E5's decidability rescue is **unavailable** to Route 2 (`T_S5 ∉ Dec_ND`). |

**BibKey verification status**: `Simpson1994` → resolved to `simpson_1994_intuitionisticmodallogic`
(global corpus). *Not verified against `references.bib`* — I did not read `references.bib` this
dispatch; a `/cite`-style check should confirm the `Simpson1994` key exists there before these citations
land in a PR. **`FischerServi1984`: confirmed ABSENT from the corpus** (KF4, blocking).
`MarinMoralesStrassburger2021`, `Pacheco2024`, `Dosen1985`, `BozicDosen1984`,
`AlechinaMendlerdePaivaRitter2001`, `Wijesekera1990`: not consulted, not verified.

---

## Confidence Level

**Overall: MEDIUM-HIGH on the diagnosis; LOW on near-term completion.** Honest, not optimistic.

| Claim | Confidence | Basis |
|---|---|---|
| Ch.7-8 bounded contexts are NOT the route (KF1) | **~90%** | `Dec_ND` verbatim excludes T_S5; §8.2.1 self-describes as re-proving Ch.5 |
| `cs5_symmetric_tail_box_gap` does not block the labelled route (KF2) | **~85%** | Mechanism quoted verbatim (`chunk_0167.md:5`); consistency hand-verified; matches CS5.lean:705-706's own diagnosis. Not mechanized — hence not 95% |
| `B_K ⊨ cs5FC''` and `B_K ⊭ cs5FC` (KF3) | **~85%** | All conjuncts hand-checked against CKExtension.lean:184. A Lean probe would settle it cheaply — **recommend probing before planning** |
| Ch.6/Lemma 6.1.2 IS on the critical path (KF4) | **~80%** | `chunk_0117.md:3` + `chunk_0111.md:3` + `chunk_0075.md:3` verbatim. Residual 20%: FS1984 may supply a genuine Ch.6-free proof |
| `TS5` defect is real (KF5) | **~90%** | Figure 3-7/6-3 vs `CS5ModalAxiom` constructors; CS5.lean:156-157 self-documents the B-not-5 choice |
| C5 (`pathSpine`) is unavoidable via any Simpson route | **~75%** | No bypass found; `chunk_0149.md` bypass applies to Ch.7 only. Residual: FS1984, or a Marin-based route (Teammate B/C) |
| **`cs5_completeness` closes via Route 2 within 3-4 dispatches** | **~15-20%** | *Below* report 02's 25-30%. Route 2 needs Ch.5 prime lemma + canonical model lemma (HIGH) **and** all of Ch.6 incl. C5 (HIGH) **and** §8.1.1 + frame match. That is **two** independent crux-grade obligations, not one. No mechanization of any of this exists anywhere |
| **FS1984 changes the routing decision if obtained** | **~50%** | Coin-flip, but the cost is one `/literature` call against a multi-dispatch C5 commitment — **strongly positive expected value** |

**Bottom line, decisively and against my own assigned angle**: my angle is a dead end (KF1), and I
recommend *against* it. The mathematically correct path is **Ch.5 + Ch.6 + §8.1.1**, which means Track C's
chapter choice is **right** and report 02's "skip Ch.6" is **unsafe** — it rests on a one-sentence sketch
delegating to a source we do not have. **The named blocking obligation is `FischerServi1984`.** Obtain it
before spending another dispatch on C5: it is the only cheap action that can change the routing, and it
is the sole authority behind *both* claimed shortcuts. If FS1984 yields nothing, Route 2 is the only
sorry-free path Simpson actually supports, C5 must be paid for in full, and a **[BLOCKED]** verdict on
C5 is a legitimate — and honest — outcome.
