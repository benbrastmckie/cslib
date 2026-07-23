# Task 517 — Adequacy Alternatives, Source-Exact Corrections, and a Decomposition

- **Task**: 517 — labelled_bounded_context_cs5_completeness
- **Session**: `sess_1784127828_1f2b2f`
- **Dispatch**: research (post-3-failed-implementation-dispatches), literature mode
- **Primary sources read directly (PDF, `Read` tool — not OCR text)**:
  - Simpson 1994, `/home/benjamin/Downloads/Simpson_1994_IntuitionisticModalLogic.ocr.pdf`
    — PDF pp. 60-68 (book pp. 51-59: **Figure 3-6, IK axiomatization**; canonical model; **Theorem 3.3.4**;
    Figure 3-7), PDF pp. 109-118 (book pp. 100-109: Figure 6-1, worked example, Lemma 6.1.2 proof,
    **formulas (6.1)-(6.11)**, Figure 6-2, Figure 6-3, **Theorem 6.2.1**, Lemma 6.2.2).
  - Marin, Morales, Straßburger 2021, *A fully labelled proof system for intuitionistic modal logics*
    — full paper (15pp), scratchpad PDF; corpus `doc_id marinmoralesstrassburger_2021_fully_labelled_proof_system_intuitionistic_modal`.
  - Pacheco 2024, *Collapsing Constructive and Intuitionistic Modal Logics* (arXiv:2408.16428v2)
    — corpus `doc_id pacheco_2024_collapsingconstructiveandintuitionisticmodallogics`, chunks 0002-0004, 0016.

---

## 0. Executive verdict

1. **The "semantic detour", as framed in the dispatch, is CIRCULAR** — but for a reason that
   *dissolves the problem rather than confirming the wall*.
2. **The adequacy bridge (Lemma 6.1.2) is almost certainly NOT on the critical path to
   `cs5_completeness` at all.** Simpson proves IS5 completeness in **Chapter 3** (Theorem 3.3.4,
   book p.56) by a **canonical model**, citing Fischer Servi. Chapter 6 answers a *different*
   question. The plan routed `cs5_completeness` through Chapter 6 unnecessarily.
3. **NEW DEFECT (fifth correction in four dispatches), source-verified and load-bearing**:
   `IKAx` is **not IK**. It is missing IK axioms 3, 4, and 5. **Simpson's Lemma 6.1.2 explicitly
   requires axiom 5** in the (□E) case and in formula (6.8). **Lemma 6.1.2 is therefore
   unprovable against the current scaffold**, independently of every tree defect found so far.
4. **The (◇E) case is NOT the crux** and never was. It is fully reconstructed below in ~3 Hilbert
   steps from (6.7)/(6.8). The true crux of the Simpson route is the *spine/`addChild`
   commutation* (Part C5).
5. **Honest confidence for the whole adequacy bridge as currently scoped: ~25-30%** — *lower*
   than dispatch 3's revised estimate, not higher.

---

## 1. LITERATURE 1 — Is there a cheaper adequacy proof?

### 1.1 Marin–Morales–Straßburger 2021: NOT a cheaper adequacy proof

Their **Theorem 3.3** (p.6) states TFAE: (1) `A` theorem of IK; (2) provable in `labIK≤ + cut`;
(3) provable in `labIK≤`; (4) valid in every birelational frame. The proof structure is:

| Leg | Where | Cost |
|---|---|---|
| 1 ⟹ 2 | §4 — derive `k₁`-`k₅` in `labIK≤`, simulate MP via `cut`, nec via label-shifting | easy |
| 2 ⟹ 3 | §6 — internal cut elimination | hard but standard |
| 3 ⟹ 4 | §5 — soundness, induction on derivation height | easy |
| **4 ⟹ 1** | **Theorem 2.5 ([Ser84, PS86]) — CITED, NOT PROVED** | **imported** |

Their `labelled ⟹ Hilbert` direction is `3 ⟹ 4 ⟹ 1`, and the `4 ⟹ 1` leg is **imported from
Fischer Servi / Plotkin–Stirling**. They do not give a syntactic argument. **Marin et al. do not
provide a cheaper mechanizable adequacy proof; they outsource the hard direction.**

Their own Conclusion (p.14) confirms the divergence: *"we have not showed that our system satisfies
Simpson's 6th requirement… To make sure that his system satisfies this requirement, Simpson chose to
depart from the direct correspondence with modal axioms and their corresponding class of Kripke
frames."*

**Coverage note (positive):** Marin's §7 one-sided Scott–Lemmon family `◇^k□^l A ⊃ □^m◇^n A`
**does** cover 𝒯_S5. Simpson's Figure 6-3 (p.108, read directly) gives `χ_5 = ∀xyz. xRy ∧ xRz ⊃ yRz`
with `(k,l) = (1,1)` and schema `(◇□A ⊃ □A) ∧ (◇A ⊃ □◇A)`; Simpson's general
`A_{φkl} = (◇^k□A ⊃ □^l A) ∧ (◇^l A ⊃ □^k◇A)` is exactly the conjunction of two of Marin's
one-sided axioms. So Marin's Theorem 7.2 applies to IS5 — but its `4 ⟹ 1` leg is again imported
(Theorem 7.1 [PS86]).

### 1.2 The semantic detour is CIRCULAR — as framed

The dispatch asked me to evaluate: *"prove labelled system sound+complete w.r.t. birelational
models, and CS5 sound+complete w.r.t. the same models, then compose."*

**This is circular.** The direction `cs5_completeness` needs is `⊨ φ ⟹ ⊢_CS5 φ`. The plan obtains
it contrapositively via `⊬_Hilbert φ ⟹ ⊬_labelled x:φ`, i.e. **`labelled-derivable ⟹
Hilbert-derivable` = Lemma 6.1.2**. Replacing that leg by "labelled ⟹ valid ⟹ Hilbert" requires
`valid ⟹ Hilbert`, **which is the goal**. Marin et al. confirm this by construction: they cannot
prove `4 ⟹ 1` either, and cite it.

**Independent corroboration (web, verified):** the only mechanized labelled↔label-free adequacy in
Lean 4 — `FormalizedFormalLogic/ProvabilityLogic`, `LabelledGentzen/Gentzen.lean`,
`iff_provableGentzen_provableLabelledGentzen` — does the **label-free ⟹ labelled** direction
syntactically but **could not do labelled ⟹ label-free syntactically**, falling back (in-file
comment) to *"via Kripke semantics: soundness … composed with completeness of `ProvableGentzen` for
finite `GL` models"*, and reaches Hilbert only transitively. For **classical GL**. That asymmetry is
a strong signal about where the real difficulty lies.

### 1.3 THE FINDING: the adequacy bridge is not needed at all

**Simpson, Theorem 3.3.4, book p.56 (PDF p.65), verbatim:**

> **Theorem 3.3.4** *The following are equivalent:*
> 1. *A is a theorem of IKS₁…S_n.*
> 2. *A is valid in all birelation models of IKS₁…S_n.*
>
> "In each case the soundness direction is routine and the completeness direction is proved by
> showing that **the canonical model**, defined analogously to that used in the proof of the
> completeness of IK, is indeed a birelation model of IKS₁…S_n. **The cases IK, IT, IKTB, IS4 and
> IS5 of Theorem 3.3.4 appear explicitly in Fischer Servi [24].** The other cases are
> straightforward."

And p.56: *"IT, IS4 and **IS5** are those in which R is respectively reflexive, a preorder and **an
equivalence relation**."*

**IS5 completeness w.r.t. birelation models is Chapter 3, by canonical model, published (Fischer
Servi 1984). It does not use the labelled system.**

What does Chapter 6 actually do? **Theorem 6.2.1** (p.107, verbatim): *"1. A is a theorem of
IK + Ax(𝒯). 2. A is a theorem of N_□◇(𝒯)."* — i.e. Chapter 6 asks **"is `IK + Ax(𝒯)` a complete
axiomatization of the theorems of the *labelled system*?"**. That is a question about *validating
the labelled system as a proof system*. **`cs5_completeness` does not need it.**

The plan's Phase 9 dependency chain has the arrow backwards: it routes IS5/CS5 completeness
*through* the labelled system (requiring Lemma 6.1.2), when Simpson gets IS5 completeness
*directly* and uses Chapter 6 only to connect his labelled system *back* to the axiomatics.

### 1.4 The CS5 ≡ IS5 leg — verified, and it reframes task 512

**Pacheco 2024, Conclusion (chunk_0016), verbatim:**

> "We showed that that the constructive and intuitionistic variations of KB coincide. This is in
> contrast to the constructive and intuitionistic variations of K, which do not prove the same
> ♦-free formulas. **This also implies that constructive and intuitionistic variations of DB, TB,
> KB5, and S5 coincide.** See [ADS15] and [Sim94] for definitions of these logics."

So **CS5 ≡ IS5 holds**, as a *corollary* of Pacheco's proved **CKB ≡ IKB** (his §3, canonical model
over CKB-theories, Lemmas 18-20). The plan's citation of "Pacheco's CS5 ≡ IS5" is supported — but
the mechanizable content is CKB ≡ IKB plus the corollary, not a standalone S5 theorem.

**Pacheco, Introduction (chunk_0003), verbatim — and this is the key to everything:**

> "While CK only has `K□ := □(ϕ → ψ) → (□ϕ → □ψ)`; and `K♦ := □(ϕ → ψ) → (♦ϕ → ♦ψ)`; **IK also
> includes the axioms `FS := (♦ϕ → □ψ) → □(ϕ → ψ)`; `DP := ♦(ϕ ∨ ψ) → ♦ϕ ∨ ♦ψ`; and `N := ¬♦⊥`.**"

**This is the unifying explanation for task 512's five-dispatch wall.** Simpson's canonical model for
IK (book p.53, read directly) proves frame condition **(F2)** using **axiom 5** — i.e. `FS`:

> "so, defining `A = A₁ ∧ … ∧ A_m` and `B = B₁ ∨ … ∨ B_n`, we have that `X ⊢ □(A ⊃ B)` **by axiom 5
> of IK**."

Task 512 was building a canonical model for **CS5**, a logic that **does not have `FS`** — the exact
axiom the construction turns on. Its recorded obstruction ("Lemma 18's box-backward analogue needs
`ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` … unavailable for CSLib's quasi-prime, disjunction-property-only `H`") is
consistent with this diagnosis. **Both task 512 and task 517 have been attacking logics missing
`FS`.** Pacheco's whole method is: *don't* — establish the collapse, then work on the IK side where
`FS` is available.

### 1.5 Existing mechanizations — none

Verified by web search (real artifacts, URLs checked):

- **Simpson's `N_IK` / Lemma 6.1.2 / Theorem 6.2.1: NOT FORMALIZED** in any proof assistant.
- **Marin et al.'s `labIK≤`: NOT FORMALIZED.**
- **No mechanized labelled↔Hilbert adequacy for *any* intuitionistic modal logic, anywhere.**
- `FormalizedFormalLogic/Foundation` (Lean 4): zero `labelled`/`label` hits; `Modal/` and
  `Propositional/` are separate hierarchies that never meet. No intuitionistic modal.
- `Ayertienna/IS5` (Coq, Murawska MSc): formalizes IS5L (labelled) and IS5LF; equivalences are
  **purely syntactic term translations** (Curry–Howard). **No Hilbert axiomatization, no Kripke
  semantics, no canonical model.** Not reusable here.
- Maggesi & Perini Brogi (HOL Light, GL): G3KGL is *mimicked* by a tactic, not formalized with an
  adequacy theorem.

**Consequence:** task 517 Phase 3 is not a transcription exercise. It is **unformalized research
territory**, being attempted against a source that is *deliberately informal* at exactly that point
(*"We hope that this makes the proof comprehensible without too much formality"*, p.101) and that
**omits** (⊥E)/(∨E) as *"quite intricate"*.

### 1.6 VERDICT

| Route | Status |
|---|---|
| Marin et al. as a cheaper adequacy proof | **NO** — outsources `4⟹1` to [Ser84, PS86] |
| Semantic detour for `labelled ⟹ Hilbert` | **CIRCULAR** — that leg is the goal |
| Negri-style cut-elimination route | **NO** — same outsourcing; not in corpus; no mechanization |
| Port an existing mechanization | **NO** — none exists |
| **Bypass the bridge entirely: CS5≡IS5 (Pacheco) + IS5 canonical model (Fischer Servi / Simpson Thm 3.3.4)** | **THE DOMINANT CANDIDATE — needs a cheap probe first (Part A2)** |

**Simpson's tree surgery is genuinely the price *of Chapter 6's question*. But Chapter 6's question
is not the one task 517 needs answered.**

---

## 2. LITERATURE 3 — Source-exact corrections

### 2.1 CONFIRMED: `Γ@U` uses ◇ for children; the outer telescope uses □ (D2 was right)

Book p.100 (PDF 109) and p.101 (PDF 110), verbatim:

```
Γ@U = ⋀{B | y:B ∈ Γ} ∧ (◇ Γ@U₁) ∧ … ∧ (◇ Γ@U_k)

(Γ ⊢_G x_m:A)* = Γ@T⁰ ⊃ □(Γ@T¹ ⊃ □(… Γ@T^{m-1} ⊃ □(Γ@T^m ⊃ A)…))
```

Worked example (p.101), verbatim: `(x:◇A ⊃ □□B, y:A ⊢_G z:◇B)* = ((◇A ⊃ □□B) ∧ ◇A) ⊃ □(◇⊤ ⊃ ◇B)`.

### 2.2 CONFIRMED: `T^i` is PRUNED for `i < m` (D3 was right)

Figure 6-1 caption text, book p.100, **verbatim**:

> "each `T^i` (`0 ≤ i ≤ m`) is the finite tree with root `x_i` and `n_i` immediate subtrees
> `T^i_1, …, T^i_{n_i}` (`n_i ≥ 0`). Note that, **for `i < m`, the node `x_i` actually has `n_i + 1`
> immediate successors** for, in addition to the `n_i` apices of `T^i_1, …, T^i_{n_i}`, **there is
> also the node `x_{i+1}`**."

`T^i` (`i < m`) excludes the path-continuation child `x_{i+1}`. `T^m` is unpruned.
**The scaffold's `LTree.pathTo`/`pathToList` (`probes/lemma612-scaffold.lean:337-350`) return the
full subtree — confirmed defective.**

### 2.3 THE CORRECT SHAPE: the *unfolding identity* (this replaces "pruning is hard")

The pruned/full relationship is **one near-trivial fact**, because `Γ@U` is a conjunction over
children and pruning simply drops one conjunct:

```
Γ@(fullSubtree v)  =  Γ@(prune v c)  ∧  ◇ Γ@(fullSubtree c)        -- c a distinguished child of v
Γ@(fullSubtree v)  =  Γ@(prune v ·)                                 -- v the last node on the path
```

**This identity is verified three independent times in the source:**

1. **(□E), formula (6.2), p.102** — target `x_{m-1}`, so its last spine entry is `x_{m-1}`'s *full*
   subtree, and Simpson writes it as `(Γ@T^{m-1} ∧ ◇Γ@T^m)`. That *is* the identity.
2. **(◇E), formula (6.4), p.104** — the level-`i` entry is
   `(Γ@U⁰ ∧ ◇(Γ@T^{i+1} ∧ ◇(…Γ@T^{m-1} ∧ ◇Γ@T^m)))`, i.e. the identity applied down the whole
   `x`-path.
2. **(6.6), p.104** — `Γ@T^i` rewritten as `Γ@U⁰ ∧ ◇Conj(V)`, the identity applied down the
   `y`-path.

**Implication for the scaffold:** D3 §3's "triply different" `x`-node problem and the broken
`Star_append` (`lemma612-scaffold.lean:577-593`) **dissolve** if the spine is computed by a
recursion with pruning *built in* (carrying the excluded child as a parameter), rather than by
`pathTo` on a tree followed by an attempted repair. **`Star_append` should be deleted, not fixed.**

### 2.4 Figure 6-2 is NOT new machinery

Figure 6-2 ("Dissection of `T^i`", p.103) shows `x_i` with pruned subtrees `U⁰_1…U⁰_{k₀}`, then the
path `x_i → y₁ → … → y_j`, each `y_l` carrying `U^l_1…U^l_{k_l}`. **This is exactly the Figure 6-1
shape applied to the subtree `T^i` with target `y_j`.**

Formula (6.4) *is* `Star` at target `y_j`. **There is no separate "dissection" construction to
build — one general `Star τ v A` (path-to-`v`-in-`τ`, with pruning) covers both figures.** This
collapses D2's "three sub-cases" and D3's "LCA argument" into instances of one definition.

The scoping premise (p.103, verbatim): *"Suppose that the (unique) path from `x₀` to `y_j` in `G` is
given by `x₀Rx₁…x_iRy₁…Ry_j` where if `j>0` and `i<m` then `y₁` is different from `x_{i+1}`, and if
`j=0` then by `y_j` we mean `x_i`."* — D3's LCA reading is correct.

### 2.5 The exact Figure 6-2 dissection statement, and the (◇E) argument in full

Writing `Tele([p₁,…,p_n], C) := p₁ ⊃ □(p₂ ⊃ □(… ⊃ □(p_n ⊃ C)))` (no `□` after the last) and
`Conj([p₁,…,p_n]) := p₁ ∧ ◇(p₂ ∧ ◇(… ∧ ◇ p_n))`, with `V := [Γ@U¹,…,Γ@U^j]`,
`W := [Γ@T^{i+1},…,Γ@T^m]`, `P := [Γ@T⁰,…,Γ@T^{i-1}]`:

| Source | Formula | Abstract form |
|---|---|---|
| (6.4) `(Γ ⊢_G y_j:◇A)*` | p.104 | `Tele(P, (Γ@U⁰ ∧ ◇Conj(W)) ⊃ □Tele(V, ◇A))` |
| (6.5) `(Γ,y:A ⊢_{G∪{y_jRy}} x_m:B)*` | p.104 | `Tele(P, (Γ@U⁰ ∧ ◇Conj(V++[A])) ⊃ □Tele(W, B))` |
| (6.6) `(Γ ⊢_G x_m:B)*` — **the goal** | p.104 | `Tele(P, (Γ@U⁰ ∧ ◇Conj(V)) ⊃ □Tele(W, B))` |
| **(6.7)** IK theorem | p.104 | `◇Conj(V) ⊃ □Tele(V,◇A) ⊃ ◇Conj(V++[A])` — *"repeated applications of **axiom 2** of IK"* |
| **(6.8)** IK theorem | p.104 | `(◇Conj(W) ⊃ □Tele(W,B)) ⊃ □Tele(W,B)` — *"repeated applications of **axiom 5**"* |

**The (◇E) derivation (p.104-105), reconstructed in full — it is ~3 steps:**

1. From (6.4) + (6.7): `Tele(P, (Γ@U⁰ ∧ ◇Conj(V)) ⊃ ◇Conj(W) ⊃ (Γ@U⁰ ∧ ◇Conj(V++[A])))`.
   *(Given `Γ@U⁰ ∧ ◇Conj(V)` and `◇Conj(W)`: (6.4)'s body yields `□Tele(V,◇A)`; with `◇Conj(V)`,
   (6.7) yields `◇Conj(V++[A])`; reconjoin `Γ@U⁰`.)* — matches Simpson's displayed formula exactly.
2. Compose with (6.5): `Tele(P, (Γ@U⁰ ∧ ◇Conj(V)) ⊃ ◇Conj(W) ⊃ □Tele(W,B))`. — matches his
   *"Whence, using (6.5), one can derive"* display exactly.
3. By (6.8): `Tele(P, (Γ@U⁰ ∧ ◇Conj(V)) ⊃ □Tele(W,B))` = **(6.6)**. — *"But now, by (6.8), it is
   clear that (6.6) is indeed derivable."*

**(◇E) is not the crux.** Given (6.7), (6.8) and `Tele`-congruence it is a short Hilbert argument.
Three dispatches mis-located the difficulty.

### 2.6 NEW DEFECT (fifth correction, four dispatches): `IKAx` is not IK

**Simpson, Figure 3-6, book p.52 (PDF 61), verbatim — the axiomatization of IK:**

```
Axioms
  0. All substitution instances of theorems of IPL.
  1. □(A ⊃ B) ⊃ (□A ⊃ □B).
  2. □(A ⊃ B) ⊃ (◇A ⊃ ◇B).
  3. ¬ ◇ ⊥.
  4. ◇(A ∨ B) ⊃ (◇A ∨ ◇B).
  5. (◇A ⊃ □B) ⊃ □(A ⊃ B).
Rules
  (MP) From A ⊃ B and A deduce B.
  (Nec) From A deduce □A.
```

`IKAx` (`probes/lemma612-scaffold.lean:78-109`, identical at `probes/adequacy-gate-probe.lean:77-109`)
has `kBox` (= axiom 1, `:89-90`) and `kDia` (= axiom 2, `:91-92`) — **and nothing else modal in the
IK base.** Axioms **3, 4, 5 are absent.** Independently corroborated by Pacheco (chunk_0003):
*"While CK only has `K□` and `K♦`; IK also includes the axioms `FS`, `DP`, and `N`."*

**`IKAx` is `CK + Ax(𝒯)`, not `IK + Ax(𝒯)`.**

**Why this is load-bearing, not cosmetic:**

- **Simpson's (□E) case (p.102) requires axiom 5.** Verbatim: *"And this follows from (6.2) by
  **axiom 5** of IK."* The step is `(Γ@T^{m-1} ∧ ◇Γ@T^m) ⊃ □A  ⟹  Γ@T^{m-1} ⊃ □(Γ@T^m ⊃ A)`,
  which is exactly `(◇A ⊃ □B) ⊃ □(A ⊃ B)`.
- **(6.8) is *"derived by repeated applications of **axiom 5**"*.** It cannot be proved without it.
- **Therefore Lemma 6.1.2 was never provable against this scaffold**, independently of the pruning
  defect, the `Star_append` defect, and the `diaE` scoping question.
- Dispatch 2's claim *"`boxE`: `Star_imp1` (single antecedent)"* (worked on paper, never mechanized)
  is **wrong** — it contradicts Simpson's own proof.

**Severity: this defect sits inside the file dispatch 1 called "COMPLETE, sorry-free, reusable" and
dispatch 3 called "fully reusable by any future attempt".** It was not found because no dispatch
checked `IKAx` against Simpson's Figure 3-6 — dispatch 1 read Figure 3-7 (the *`Ax(𝒯)` modal
schemas*, p.56) and appears to have taken that for the IK base.

**Repair cost: small.** Adding three constructors to `IKAx` is non-breaking for
`NIK_to_NIKAx`/`TClosure.hilbertTransport` (`:185`, `:229`) — those map *into* `IKAx`, so extra
constructors cannot break them. **This is a genuine, cheap, high-value fix.**

---

## 3. LITERATURE 2 — Mechanization technique (scoping/binders)

The dispatch asked whether the missing well-scopedness invariant is a known pattern with a standard
solution (locally-nameless + cofinite quantification, Aydemir et al.; nominal techniques).

**Finding: the question is now moot, and that is the useful answer.** D3 already resolved the
`diaE` z-scoping worry conceptually (companion `LTree` witness ⟹ `x`, `z` in the same tree ⟹
well-defined LCA). §2.4 above **strengthens** that: once `Star τ v A` is defined generally, the LCA
"dissection" is not a separate argument at all — Figure 6-2 is Figure 6-1 at a different target.
The remaining obligation is **not a binder-scoping problem**; it is a **structural-recursion
bookkeeping problem** (Part C5): relating `pathSpine` before/after `addChild`.

Cofinite quantification (Phase 1's choice, per CSLib's `Typing.abs` precedent) remains correct for
`NIKAx.diaE`'s freshness side-condition and needs no change. Locally-nameless/nominal techniques
address *variable capture*, which is not the obstruction here — the labels are already concrete and
the freshness is already handled by the `L`/`hL` cofinite pair in `NIKAx.diaE`
(`lemma612-scaffold.lean:133`+). **No technique from that literature would have unblocked any of the
three dispatches.** Reporting this as a negative result rather than manufacturing a citation.

---

## 4. DELIVERABLE — The decomposition

Per the user's directive: small, separately-dispatchable parts, each ~one agent run, each with its
own independently-verifiable target. **Track A first — it is cheap and it decides everything else.**

### TRACK A — Route selection and defect repair (do FIRST; both parts are small)

#### A1 — Repair `IKAx` to be actually IK
- **Goal**: add Simpson's axioms 3 (`¬◇⊥`), 4 (`◇(A∨B) ⊃ (◇A ∨ ◇B)`), 5 (`(◇A ⊃ □B) ⊃ □(A ⊃ B)`)
  as constructors of `IKAx`.
- **Reused assets**: `IKAx` (`probes/lemma612-scaffold.lean:78-109`); `NIK_to_NIKAx` (`:229`);
  `TClosure.hilbertTransport` (`:185`); `IKDerivable` (`:112`); `IKAx.toIKDerivable` (`:121`).
- **Success criterion**: `lake env lean probes/lemma612-scaffold.lean` exit 0, zero sorries,
  `#print axioms` unchanged on `NIK_to_NIKAx` and `TClosure.hilbertTransport` (both must still
  compile **unchanged** — adding constructors to a target inductive is non-breaking).
- **Risk**: LOW. Mechanical.
- **Note**: required for **either** track. Also fixes the record: dispatch 1's "Lemma 6.2.2 complete"
  claim is only meaningful against the *correct* IK.

#### A2 — THE ROUTE PROBE: is `FS` derivable in CSLib's CS5? *(highest leverage in the whole task)*
- **Goal**: attempt a sorry-free derivation of `FS := (◇ϕ → □ψ) → □(ϕ → ψ)` in CSLib's `CS5`
  (`Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean`, `CS5ModalAxiom` at `CS5.lean:182`).
- **Why**: Pacheco proves CKB ≡ IKB and states the corollary that **CS5 and IS5 coincide**. Since
  IS5 ⊢ `FS`, the collapse entails **CS5 ⊢ `FS`**. `FS` is the *exact* axiom Simpson's canonical
  model uses to prove frame condition (F2) (p.53: *"we have that `X ⊢ □(A ⊃ B)` **by axiom 5 of
  IK**"*), and the *exact* thing task 512's box-backward step was missing.
- **Success criterion**: EITHER a sorry-free `CS5 ⊢ FS`, OR a precisely documented failure naming
  the step that fails. **Both outcomes are valuable and decisive.**
- **Risk**: MEDIUM-HIGH (Pacheco's route to the collapse is semantic; a direct syntactic derivation
  may not exist and may itself require the canonical model). **Payoff if it succeeds: potentially
  unblocks task 512 *and* makes Track B live *and* retires Track C.**
- **Budget**: one dispatch, hard cap. Do not let this become a fourth open-ended gate.

#### A3 — Route verdict (paper, no Lean)
- **Goal**: given A2's outcome, verify the two remaining semantic-route preconditions:
  (i) does CSLib's CS5 *semantics* (`Forcing.lean`, `CKExtension.lean:184-189` `cs5FC''`) coincide
  with IS5 birelation semantics (Simpson p.56: *"IS5 … R … an equivalence relation"*, plus F1/F2)?
  (ii) is the Pacheco corollary chain CKB≡IKB ⟹ CS5≡IS5 sound as stated?
- **Success criterion**: a written GO/NO-GO on Track B with a named blocking obligation if NO-GO.
- **Risk**: LOW (analysis), but **must not be skipped** — task 512's five dispatches are the cost of
  not having asked this.

### TRACK B — Semantic route *(only on an A3 GO)*

- **B1**: mechanize CKB ≡ IKB (Pacheco §3, Lemmas 18-20; canonical model over CKB-theories, Zorn).
- **B2**: derive CS5 ≡ IS5 (Pacheco's corollary).
- **B3**: mechanize the IS5 canonical model / Simpson Theorem 3.3.4 (Fischer Servi 1984). **Not in
  the corpus** — would need `/literature` ingestion of Fischer Servi 1984 first. Flagging as a
  real gap, not glossing it.
- **Confidence**: not yet estimable; A3 exists precisely to estimate it.

### TRACK C — Simpson's tree surgery, decomposed *(fallback; only if Track B is NO-GO)*

Ordered; each is one dispatch with its own verifiable target. **C1-C3 are pure formula-level work
with ZERO tree dependency — they can be dispatched immediately and in parallel with Track A.**

| # | Goal | Reused assets | Success criterion | Risk |
|---|---|---|---|---|
| **C1** | Define `Tele`/`Conj` over `List (Proposition Atom)`; port `Star_imp1`/`Star_imp2` to `Tele`-congruence | `Star_imp1` (`:450`), `Star_imp2` (`:507`), `box_mono1` (`:393`), `box_mono2` (`:403`), `IK.impIntro` (`:385`), `bigAnd` (`:360`), CSLib `DeductionTheorem.deductionTheorem` | compiles, sorry-free | LOW — D2 proved the tree-typed version; this is a re-typing |
| **C2** | Prove **(6.7)**: `◇Conj(V) ⊃ □Tele(V,◇A) ⊃ ◇Conj(V++[A])`, induction on `V`, using axiom 2 | `IKAx.kDia` (`:91`) — **already present** | sorry-free; no `IKAx` change needed | LOW-MED |
| **C3** | Prove **(6.8)**: `(◇Conj(W) ⊃ □Tele(W,B)) ⊃ □Tele(W,B)`, induction on `W`, using axiom 5 | **requires A1** (axiom 5 absent today) | sorry-free | MED |
| **C4** | `LTree`, `star`, `fullSubtree`, `prune`, and the **unfolding identity** (§2.3) | `LTree` (`:300`), `star` (`:368`), `leaf` (`:315`), `labels` (`:318`); **delete** `pathTo`/`pathToList` (`:337-350`) and `Star_append` (`:577`) | **`#eval`/`decide` reproduces Simpson's worked example verbatim**: tree `x→y, x→z→w`, target `z` ⟹ `((◇A⊃□□B) ∧ ◇A) ⊃ □(◇⊤ ⊃ ◇B)` | MED — but the success criterion is concrete and cheap |
| **C5** | `pathSpine` (pruning built into the recursion) + the `addChild`/`pathSpine` commutation lemma | C4's unfolding identity; `addChild` (`:324`) | sorry-free commutation lemma | **HIGH — THE TRUE CRUX** |
| **C6** | `LTree.toGraph`; the τ-parameterized generalized induction; non-modal cases + (□I)/(□E)/(◇I) | C1-C5; `NIKAx` (`:133`); `wrapClosed` (`:429`) | all listed cases sorry-free | MED |
| **C7** | The **(◇E)** case, via §2.5's 3-step argument | C2, C3, C5, C6 | sorry-free | MED given C5 |
| **C8** | (⊥E)/(∨E) | C1, C6 | sorry-free | LOW — label-local in this encoding |

**The true crux is C5**, not (◇E). Everything else is done, small, or mechanical.

---

## 5. Honest confidence

I am deliberately estimating **below** my instinct, given this task's documented history of
over-rating (reports 05, 06, 516/01, plan 01's ~50%, D2's "100-200 mechanical lines", D3's
"2-3 dispatches").

| Claim | Confidence | Grounding |
|---|---|---|
| `IKAx` is missing IK axioms 3/4/5 and Lemma 6.1.2 needs axiom 5 | **~97%** | Simpson Fig. 3-6 p.52 + (□E) p.102 + (6.8) p.104, read verbatim; corroborated by Pacheco chunk_0003 |
| The (◇E) case is short given (6.7)/(6.8) | **~85%** | (6.4)-(6.8) pp.104-105 read directly; derivation reconstructed and checked against Simpson's two displayed intermediates |
| Lemma 6.1.2 is **not** required for `cs5_completeness` | **~85%** | Simpson Thm 3.3.4 p.56 verbatim; Thm 6.2.1 p.107 verbatim shows Ch.6 answers a different question |
| CS5 ≡ IS5 | **~90%** as mathematics; **~60%** that the corollary is as immediate as Pacheco's one line suggests | Pacheco Conclusion, chunk_0016, verbatim |
| **Track B (semantic route) is mechanizable at reasonable cost** | **~35-40%** | Fischer Servi not in corpus; task 512 burned 5 dispatches on adjacent canonical-model work; "canonical model is a birelation model of IS5" is a box-backward-shaped obligation |
| **Track C (full adequacy bridge) completes in 2-3 dispatches** | **~25-30%** | *Lower* than D3's estimate. Four dispatches, five corrections, each found by the next. No mechanization of this argument exists anywhere. Source is deliberately informal and omits two cases |
| A2 (`CS5 ⊢ FS`) succeeds | **~40%** | Pacheco's collapse is semantic; a direct syntactic derivation may not exist |

**Base-rate warning I am placing on the record:** every dispatch on this gate has found the previous
dispatch's transcription subtly wrong, *including this one* (§2.6 — and I found it in the file two
dispatches certified as complete and reusable). That rate is not improving. Any estimate for Track C
that assumes "this time the transcription is right" should be discounted accordingly. **I make no
claim that §2.5's reconstruction is defect-free** — it is unmechanized, and its value is precisely
that C1-C3 can now falsify it *cheaply and in isolation* rather than at a monolithic gate.

---

## 6. Recommendation

**Do not open a fourth dispatch on Simpson's tree surgery yet.** Spend two cheap dispatches on
**A1** (a real defect fix, needed either way) and **A2** (the `FS` probe) first. A2 is the highest-
leverage question in this task *and in task 512*: both have been attacking logics that lack the very
axiom their proofs turn on.

**If the adequacy bridge is not worth the remaining cost — and the honest reading is that it is
not, because it is not needed** — the right move is to re-plan around Track A/B and retain the
labelled framework (Phases 1, 2, 4; ~789 lines landed, sorry-free, CI-green:
`Labelled/Syntax.lean` 202, `Deduction.lean` 312, `Context.lean` 275) as an independently valuable
contribution, **decoupled from `cs5_completeness`**.
