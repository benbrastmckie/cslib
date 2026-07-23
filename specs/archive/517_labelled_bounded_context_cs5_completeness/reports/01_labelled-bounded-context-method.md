# Research Report 01 — Task 517: Simpson's Labelled Method for CS5 Completeness (Route B, full build)

**Task type**: cslib (Lean 4). **Dispatch**: orchestrator, session `sess_1784127828_1f2b2f`,
`orchestrator_mode=true`, `--lit` active. **No production Lean written** (Simpson source mined +
CSLib source inspection). **Scope**: extract Simpson 1994's rigorous IS5 completeness method in
mechanizable detail; verify the four guardrails do not trip; phase it; give honest confidence.

---

## LEAD — the four things the dispatch asked me to lead with

### 1. The three spine lemmas — **NOT the three the dispatch named**

The dispatch asked me to extract **Lemma 8.2.5 (T-Comp)**, **Lemma 8.2.6 (bounded canonical
model)**, and the **bounded prime lemma (8.2.4)** as "the spine". **All three are the wrong
lemmas, and Chapter 8 explicitly excludes IS5.** Verbatim, Simpson p. 161 (`simpson.txt:10240`):

> "We turn instead to our proof of Theorem 8.2.1. **As the theorem is already known for IS5, we
> consider only the other cases** (for which we can give a uniform proof). In Section 8.3, we
> shall **indicate** how our techniques can also be extended to IS5.
> Henceforth, we fix L as any logic in Dec_𝒯, **other than IS5**. Let 𝒯 be its associated basic
> geometric theory. **Thus 𝒯 ⊆ {χ_D, χ_T, χ_B}.**"

Chapter 8 is about the **finite model property**, not completeness. Its 𝒯 ranges over ⊆ {D, T, B}
— **no χ_4, no χ_5** — and `T-Comp` (`:10494`) has exactly three clauses (edge, reflexive/serial
loop, converse edge); **there is no transitive-closure clause**, so it cannot produce an S5 frame.
Section 8.3 (`:11220`) only *asserts* the extension ("the proof for IS5 is quite simple, because
contexts can be **set-indexed** rather than tree-indexed") — an unproved remark in a Discussion
section. Task 517 wants **completeness**, which Chapter 8 never provides for any logic.

**The actual spine for IS5 completeness is Chapters 5 + 6 + 8.1**, and it is uniform in 𝒯,
rigorous, and covers IS5:

| # | Lemma | Location | Statement (verbatim-grounded) |
|---|---|---|---|
| **S1** | **Prime Lemma 5.3.1** | `:5990` | "If `(G,Γ)` is a context and `Γ ⊬_G x:A` then there is a **𝒯-prime context** `(H,Δ) ⊇ (G,Γ)` such that `Δ ⊬_H x:A`." Proof: **Zorn** over `C = {(G',Γ') ⊇ (G,Γ) | underlying set ⊆ W(V'), Γ' ⊬ x:A}`; chains close under union; maximal element is 𝒯-prime. |
| **S2** | **Canonical Model Lemma 5.3.2** | `:6102` | "For all 𝒯-prime contexts `(H,Δ)`, for all `y` in `H`, `(H,Δ),y ⊩_{K^𝒯} B` **iff** `y:B ∈ Δ`." Proof: case analysis on `B`; the **□-backward case uses a fresh label + (□I)**. |
| **S3** | **Theorem 6.2.1 (adequacy)** | `:6880` | "1. `A` is a theorem of `IK + Ax(𝒯)`. 2. `A` is a theorem of `N_IK(𝒯)`" — equivalent. "**For any 𝒯 ⊆ {χ_D, χ_T, χ_B, χ_4, χ_5}**, `IK + Ax(𝒯)` is just the appropriate `IKS₁…Sₙ`." **This one covers IS5.** |

Plus the birelation bridge **Lemma 8.1.2 / Theorem 8.1.4** (`:9779`, `:9966`), which is where
Chapter 8 *is* usable — see §3.

### 2. Guardrail non-triggering verdict — **NONE of the four trip. Verified, with mechanism.**

The mechanism is one sentence: **CSLib's guardrails all quantify over a world type whose
reachability relation is *derived from box-membership* over a *fixed head*; Simpson's worlds are
pairs `(w,d)` whose relation `R` is a *primitive graph* that is a **classical** model of the frame
theory, and whose box-backward moves to a *larger context* — which the box clause's own
`≤`-quantification licenses.** Detail in §5. The decisive one:

- **`cs5_symmetric_tail_box_gap` does NOT trip** — not because its argument fails (**it does go
  through in the labelled model too**; I checked, and this is the trap), but because its
  hypothesis `q ∉ H` is stated at a **fixed** head. Simpson's box-backward witness lives in a
  **larger** context `(H',Δ') ⊇ (H, Δ)` where `q ∈ Θ'(y)` is *allowed*. The lemma is **true and
  vacuous at the relevant instance**.
- **The head-enlargement is exactly the "simultaneous pair" CSLib could not build — and Simpson's
  Prime Lemma builds it for free**, because a context is **one object** carrying **all labels at
  once**, so a **single** Zorn maximalises `Θ(y)` for **every** label simultaneously, subject to
  one global constraint `Δ ⊬ x:A`. The cross-world invariants (`boxInv Θ(y) ⊆ Θ(z)` for `yRz`)
  are **not constraints on the Zorn** — they are **consequences of deductive closure under (□E)**.
  *This is the whole trick, and it is the answer to the task-512 wall.*

### 3. The single hardest node

**Lemma 6.1.2 / 6.2.3 — the tree internalization `(Γ ⊢_G x:A)*`** (the adequacy bridge, S3).
Simpson's proof is, by his own words, informal — "**We hope that this makes the proof
comprehensible without too much formality**" (`:6558`) — and he **omits the two hardest cases**:
"Of the non-modal rules, all are straightforward except for **(⊥E) and (∨E) which are quite
intricate** because their premises and conclusion may have prefixes arbitrarily far apart in `G`.
However, the difficulties are similar to those encountered in the (◇E) case" (`:6544`). A
mechanizer must **reconstruct omitted, self-described-intricate cases from scratch**. This is the
one node with no transcribable proof.

### 4. Confidence

**~50% (range 45–55%)** that `cs5_completeness` closes sorry-free at ~2000–2450 lines / 9 phases.

This is **deliberately lower than report 516/02's "~high" for Route B**, and the downgrade is
itself a finding: 516/02 rated Route B from **122–140 byte OCR fragments** (`chunk_0843` is 140
bytes, `chunk_0849` 122, `chunk_0850` 131 — they contain *truncated lemma titles, not
statements*), and consequently **mis-identified the spine** (Ch. 8, which excludes IS5) and
**mischaracterized Lemma 8.2.5** (it is "`T-Comp(H) ⊨_cl 𝒯`", a classical-model claim whose *hard*
case is **seriality**; symmetry is one throwaway line). Route B is **real and sound** — better
founded than I expected — but it is **not** a "transcription": one spine lemma is unwritten in the
source. **This is not a wall; it is a priced risk.**

---

## Deliverable 1 — The labelled framework, precisely

### 1a. Syntax

- **Prefix variables** `V` — countably infinite (`:5881`). **Witness variables**: `W(V')` is the
  free algebra over `V'` with a unary operator `v_{x:◇A}` per modal formula and a `k`-ary operator
  per geometric sequent (`:5883–5905`). Domains are subsets of `W(V')` for **coinfinite** `V' ⊆ V`
  — "In order to always guarantee a supply of such new elements for `D_{w'}` we shall work below
  with `V'` that are coinfinite subsets of `V`" (`:5920`). **This coinfiniteness is the fresh-label
  supply and is load-bearing for the □-backward case.**
- **Graph** (`:5047–5065`): a pair `(X,R)`, `X` a non-empty set of nodes. Ops `G ∪ G'`, `G ∪ X'`,
  `G ∪ {xRy}`. The **trivial graph** `𝒯 = ({x},∅)` — initial in pointed graphs (`:5077`).
- **Labelled formula**: `x:A` for `x ∈ W(V)`, `A` a modal formula.

### 1b. The labelled natural deduction system `N_IK` (Figure 4-1, `:4630–4670`)

Intuitionistic propositional rules (`⊥E`, `∧I/E`, `∨I/E`, `⊃I/E`) — all **label-local**. Plus:

```
  x:□A   xRy                      [xRy]                    y:A   xRy            x:◇A   [y:A],[xRy] ⊢ z:B
  ───────────── (□E)                 ⋮                     ───────────── (◇I)   ───────────────────────── (◇E)
      y:A                           y:A                        x:◇A                       z:B
                                 ───────── (□I)*
                                   x:□A
```
- **Restriction on (□I)**: "`y` must be **different from `x`** and must **not occur in any open
  assumptions** other than the distinguished occurrences of `xRy`" (`:4661`).
- **Restriction on (◇E)**: "`y` must be different from both `x` and `z` and must not occur in any
  open assumptions upon which `z:B` depends other than the distinguished occurrences of `y:A` and
  `xRy`" (`:4664`).
- `N_IK(𝒯)` = `N_IK` + the rules `{(R_χ) | χ ∈ 𝒯}` (`:4940`).

**Consequence relation** (`:5090`, verbatim): "`Γ ⊢_G x:A` if there is a derivation `Π` of `x:A`
from open assumptions `y₁Rz₁,…,yₘRzₘ, x₁:A₁,…,xₙ:Aₙ` such that `y₁Rz₁ and … and yₘRzₘ` in `G`,
and `{x₁:A₁,…,xₙ:Aₙ} ⊆ Γ`." `A` is a **theorem** iff `⊢_𝒯 A` over the trivial graph (`:5114`).

### 1c. Contexts, 𝒯-prime, and the geometric theory

**Context** `(G,Γ)` (`:5941`): `G` contains every prefix in `Γ`, and (1) the underlying set of `G`
is ⊆ `W(V')` for some **coinfinite** `V'`; (2) `v_{x:◇A} ∈ G` only if `xRv_{x:◇A}` in `G` and
`v_{x:◇A}:A ∈ Γ`; (3) the geometric-witness closure condition.

**𝒯-prime** (`:5953`) — `(G,Γ)` is 𝒯-prime iff **`G` is a classical model of 𝒯** and:
1. `Γ ⊢_G x:A ⟹ x:A ∈ Γ` (**Deductive closure**)
2. `∀x` in `G`, `Γ ⊬_G x:⊥` (**Consistency**) ← *this is what banishes `Ω`*
3. `x:A∨B ∈ Γ ⟹ x:A ∈ Γ or x:B ∈ Γ` (**Disjunction property**)
4. `x:◇A ∈ Γ ⟹ ∃y. xRy in G ∧ y:A ∈ Γ` (**Diamond property**)

**"𝒯" is a basic geometric theory over `R`** — the frame conditions, `𝒯 ⊆ {χ_D, χ_T, χ_B, χ_4, χ_5}`
(seriality, reflexivity, symmetry, transitivity, euclideanness). **IS5 = IKT5, i.e. `𝒯 = {χ_T, χ_5}`**
(`:3827`: "we write IT, IS4 and IS5 for IKT, IKT4 and IKT5 respectively"). Reflexive + euclidean
⟹ equivalence relation.

### 1d. The semantics: IL-models and I𝒯-models (`:5709–5760`)

An **IL-model** is an **intuitionistic first-order Kripke model**
`K = (W, ≤, {D_w}_{w∈W}, {R_w}_{w∈W}, {a_w}_{w∈W})` — worlds `w`, domains `D_w`, a relation `R_w`
on each domain, valuations `a_w`. Modal satisfaction `w,d ⊩ A` (`:5722`, verbatim):

```
w,d ⊩ α        iff  a_w(d)
w,d ⊮ ⊥
w,d ⊩ A ∧ B    iff  w,d ⊩ A and w,d ⊩ B
w,d ⊩ A ∨ B    iff  w,d ⊩ A or w,d ⊩ B
w,d ⊩ A ⊃ B    iff  for all w' ≥ w, w',d ⊩ A implies w',d ⊩ B
w,d ⊩ □A       iff  for all w' ≥ w, for all d' ∈ D_w', R_w'(d,d') implies w',d' ⊩ A
w,d ⊩ ◇A       iff  there exists d' ∈ D_w such that R_w(d,d') and w,d' ⊩ A
```

"We say that `K` is an **I𝒯-model** if, for all `w ∈ W`, the graph `(D_w, R_w)` is a **classical
model of 𝒯**" (`:5759`).

**Note the ◇ clause is a plain `∃` with no `≤`-quantification** — this differs from CSLib's
Wijesekera `∀≤∃` clause. §4 shows they **coincide on the constructed model** (this is a real
proof obligation, not a formality).

### 1e. The canonical I𝒯-model `K^𝒯` (`:5987`)

```
W^𝒯          = the set of 𝒯-prime contexts
(H,Δ) ≤ (H',Δ')  iff  (H,Δ) ⊆ (H',Δ')
D_{(H,Δ)}    = the underlying set of H
R_{(H,Δ)}(x,y)   iff  xRy in H
a_{(H,Δ)}(x)     iff  x:α ∈ Δ
```
"for all `(H,Δ) ∈ W^𝒯`, `(D_{(H,Δ)}, R_{(H,Δ)}) ⊨_cl 𝒯` because `(D,R) = H` and `H ⊨_cl 𝒯` as
`(H,Δ)` is 𝒯-prime" (`:6098`). **The frame theory holds because it is part of 𝒯-primeness —
not because it is derived from theory-membership.** This is the crux of guardrail non-triggering.

### 1f. The □-backward case of Lemma 5.3.2 — the money step (`:6146–6176`, verbatim structure)

> **□B.** We show that `y:□B ∈ Δ` if and only if, for all `(H',Δ') ≥ (H,Δ)` and all `z`, `yRz` in
> `H'` implies `z:B ∈ Δ'`.
> **⟸** Suppose that, for all `(H',Δ') ≥ (H,Δ)`, `yRz` in `H'` implies `z:B ∈ Δ'`. Let `V'` be a
> coinfinite subset of `V` such that the underlying set of `H` is contained in `W(V')`. **Take any
> `z ∈ V\V'`.** Define `H₀ = H ∪ {yRz}`. Clearly `(H₀,Δ)` is a context.
> Suppose, for contradiction, that `Δ ⊬_{H₀} z:B`. Then, **by the prime lemma**, there exists a
> 𝒯-prime context `(H',Δ') ⊇ (H₀,Δ)` such that `Δ' ⊬_{H'} z:B`. But then `(H',Δ') ≥ (H,Δ)` and
> `yRz` in `H'`, but clearly `z:B ∉ Δ'`, contradicting the initial assumption.
> So `Δ ⊢_{H₀} z:B`. But, as `z ∈ V\V'`, `z` is not in `H`. Therefore, **by an application of
> (□I)**, `Δ ⊢_H y:□B`. Whence, by deductive closure, `y:□B ∈ Δ`.

**Read the contrapositive** — this is `cs5_completeness`'s box-backward: `y:□B ∉ Δ` ⟹ **∃ a larger
context `(H',Δ')` and a fresh `z` with `yRz` in `H'` and `z:B ∉ Δ'`**. The witness is delivered by
(i) a **fresh label**, (ii) the **prime lemma applied to the whole context at once**. There is no
bounded Lindenbaum, no pair-primeness, no symmetric-tail constraint.

---

## Deliverable 2 — The completeness chain, in dependency order

**Target**: `cs5_completeness : CKValidFC cs5FCIncest φ → Derivable CS5ModalAxiom φ`.
**Contrapositive**: `¬Derivable_CS5 φ ⟹ ∃ model ⊨ cs5FCIncest refuting φ`.

| Step | Claim | Simpson | Difficulty |
|---|---|---|---|
| **C0** | `CS5ModalAxiom` ≡ `IK + Ax({χ_T,χ_5})` (Hilbert-level) | `:6880` + `CS5.lean:93-99` (`CS5 ≡ IS5`, Pacheco2024 Thm 13) | Medium — 17 axiom cases each way |
| **C1** | `N_IK(𝒯)` theorems = `N_IK + Ax(𝒯)` theorems (**Lemma 6.2.2**, `:6989`) | eliminate `(R_χ)` in favour of axioms; the graph then stays a **tree** | Medium — derivation translation |
| **C2** | `IK + Ax(𝒯)` theorems = `N_IK + Ax(𝒯)` theorems (**Lemma 6.2.3**, `:7127`) via **Lemma 6.1.2** tree internalization `(Γ ⊢_G x:A)*` | `:6525`; "trivial modifications … apart from one extra trivial case covering the use of an axiom" (`:7138`) | **HARDEST — informal in source, (⊥E)/(∨E) omitted** |
| **C3** | **Prime Lemma 5.3.1** — Zorn over contexts | `:5990` | High — Zorn + 4 conditions + geometric witnesses |
| **C4** | **Canonical Model Lemma 5.3.2** — truth lemma | `:6102` | High — but □-case is clean (fresh label) |
| **C5** | `B_K` construction + **Lemma 8.1.2** | `:9560–9600` | Medium |
| **C6** | `B_K ⊨ cs5FCIncest` | derived (§4) | Medium |

**Dependency order**: C3 → C4 → C5 → C6 (the semantic spine, independent of C0–C2);
C0 → C1 → C2 (the syntactic bridge). Final assembly needs both.

**Where the frame theory enters for the symmetric (B/S5) case** — and this is the direct answer to
the dispatch's "where does T-Comp enter": **it does not enter via `T-Comp` at all.** `T-Comp` is a
Chapter-8 device for *bounded* (finite-tree) contexts that must be *repaired* into a model of 𝒯
because bounding breaks it. In Chapter 5 the contexts are **unbounded**, and "`H` is a classical
model of 𝒯" is simply **clause 0 of 𝒯-primeness**, established inside the Prime Lemma by the
`(R_χ)` rules (`:6010–6040`: "we show that `H ⊨_cl χ` … if it were then `Δ ⊢_H x:A` would be
derivable by an application of `(R_χ)`"). **Symmetry is free and structural, exactly as
`cs5Tail_symm` is free on the CSLib side — it was never the gap, in either framework.**

---

## Deliverable 3 — The soundness/adequacy bridge (flagged honestly)

**Is it a translation `⊢_CS5 φ ⟺ ⊢_labelled x:φ`?** **Yes** — that is exactly **Theorem 6.2.1**
(`:6880`), and for `cs5_completeness` we need only the **hard** direction:
**`⊢_{N_IK(𝒯)} x:φ ⟹ Derivable_CS5 φ`**.

**What proving it requires** (in Simpson's own decomposition):
1. **Lemma 6.2.2** (`:6989`): `Γ ⊢^𝒯_G x:A ⟺ Ax(𝒯);Γ ⊢_G x:A`. The ⟸ direction translates each
   `(R_χ)` application away. The key structural observation (`:7014`): "each relational assumption
   in `Π*`, in particular the open assumptions `y_kRz_k`, **must be the premise of either a (□E)
   application or a (◇I) application**" — true by inspection of the rules (only `□E`/`◇I` take
   relational premises), but it needs a careful derivation induction.
2. **Lemma 6.1.2 / 6.2.3**: define, for a **finite tree** `G`, the internalizing formula
   (`:6512`, verbatim):
   ```
   Γ@U        = ⋀{B | y:B ∈ Γ} ∧ (□Γ@U₁) ∧ … ∧ (□Γ@U_k)     (y = root of subtree U)
   (Γ ⊢_G x:A)* = Γ@T⁰ ⊃ ◇(Γ@T¹ ⊃ ◇(… Γ@T^{m-1} ⊃ ◇(Γ@T^m ⊃ A)…))
   ```
   and prove `Γ ⊢_G x:A ⟹ (Γ ⊢_G x:A)*` is a theorem of `IK + Ax(𝒯)`, **by induction on
   derivations**. At the trivial graph `(⊢_𝒯 x:A)* = ⊤ ⊃ A`, so `A` follows (`:6524`).

**Honest difficulty assessment — this is a real deliverable and it is the risk.**
- Simpson explicitly disclaims rigour: "**We hope that this makes the proof comprehensible without
  too much formality**" (`:6558`).
- He **omits (⊥E) and (∨E)**: "**quite intricate** because their premises and conclusion may have
  prefixes arbitrarily far apart in `G`" (`:6544`). These are *not* transcribable; they must be
  reconstructed.
- The induction carries a **treeness invariant** ("we must take care that we can always restrict
  attention to graphs that are trees", `:6533`) that Simpson never states as a lemma.
- **Mitigation available**: define `LCons G Γ x A := Derivable CS5ModalAxiom ((Γ ⊢_G x:A)*)`, making
  the bridge **definitional at the trivial graph** and converting Lemma 6.1.2 into a set of
  **per-rule admissibility obligations**. This does not reduce the total work but makes it modular
  and incremental — a planner should strongly consider it. The (⊥E)/(∨E) obligations remain.

**Do we need Simpson's §8.1.2 soundness (which *fails* in general)?** **No.** §8.1 opens with a
genuine counterexample — "the obvious statement of soundness for `N_IK` **fails**" (`:9549`,
Figure 8-1) — and Theorem 8.1.1 is repaired only by restricting `G` to a **tree**. But that
restriction binds only the **soundness** direction. Simpson (`:9613`, verbatim): "**Note that
nowhere in the proof of completeness have we used the assumption that `G` is a tree. Thus the
completeness direction of Theorem 8.1.1 holds for arbitrary consequences.**" **The completeness
direction — the only one task 517 needs — survives the soundness failure intact.** CSLib's
soundness is already landed independently (`cs5_soundness_incest`). *This is a decisive
de-risking finding.*

---

## Deliverable 4 — CSLib mapping and reuse (honest ledger)

### Genuinely transfers

| Asset | Location | Why it survives |
|---|---|---|
| `Proposition` / `Proposition.map` | `Basic.lean:72,140` | The formula type is unchanged; labelled formulae are `Label × Proposition Atom`. |
| `DerivationTree` / `Derivable` | `Metalogic/DerivationTree.lean:134,201` | The Hilbert side of the bridge (C0) is untouched. |
| `CS5ModalAxiom` (17 cases) | `CS5.lean:182` | The completeness target's syntax. |
| **`cs5_axiom_sound_incest` / `cs5_soundness_incest`** | `CS5Canonical.lean:278`, `CS5.lean:126` | **The frame class MATCHES — verified below.** Real reuse win. |
| `CKForces` / `ckforces_persistence` | `Forcing.lean:67,122` | The countermodel `B_K` is a `CKForces` model; persistence is reused in Lemma 8.1.2. |
| `CKValidFC` / `ckValid_iff_ckValidFC_true` | `CKExtension.lean:86,100` | The validity target. |
| `CS5 ≡ IS5` | `CS5.lean:93-99` | Licenses using Simpson's IS5 (`𝒯 = {χ_T,χ_5}`) for `CS5`. Load-bearing for C0. |
| `cs5_dia_bot_imp_bot` | `CS5.lean` | Justifies `botForces := λ_. False` (no fallible worlds needed at CS5 strength). |

**Frame-class match, verified.** `B_K` (§Deliverable 1e→8.1.1) has `(w,d) ≤' (w',d') iff w ≤ w' ∧ d = d'`
and `(w,d) R' (w',d') iff w = w' ∧ R_w(d,d')`. Against `cs5FCIncest`'s five conjuncts
(`CS5Canonical.lean:258-263`), using `R_w` an equivalence relation (classical model of `{χ_T,χ_5}`)
and `R` monotone under `≤` (standard IL-model condition):

1. `∀w, r w w` ← `R_w` reflexive ✓
2. `r w u → r u t → r w t` ← `R_w` transitive ✓
3. `r w u → u ≤ u' → r u' t → ∃v, w ≤ v ∧ r v t` ← witness `v := (w'',d)`; needs `R` monotone + transitive ✓
4. `r w u → u ≤ u' → ∃t, r u' t ∧ w ≤ t` ← witness `t := (w'',d)`; needs `R` monotone + symmetric ✓
5. `cs5Incest r` ← witness `u' := u`; needs `R_w` **plain symmetric** ✓

**So `B_K ⊨ cs5FCIncest`, and `cs5_axiom_sound_incest`/`cs5_soundness_incest` transfer unchanged.**
Independently corroborated by Simpson `:9966`: "given any I𝒯-model `K`, the model `B_K` **is indeed
a birelation model of 𝒯**", and `:9985`: "for any `𝒯 ⊆ {χ_D,χ_T,χ_B,χ_4,χ_5}`, **Theorems 6.2.1 and
8.1.4 imply the soundness and completeness of the corresponding `IKS₁…Sₙ` relative to its
birelation models**."

### Must be built new (~zero reuse)

Labelled syntax (labels, graphs, fresh-label supply, witness algebra `W(V')`); the labelled
deduction system `N_IK(𝒯)` **with eigenvariable/freshness side conditions**; contexts and
𝒯-primeness; the Zorn prime lemma over contexts; the canonical I𝒯-model; the `B_K` cartesian
construction; the tree-internalization translation.

### Explicitly confirmed NOT to transfer

**`CKSegment` / `Segment` / `SegmentLindenbaum` do NOT transfer. Confirmed.**
- `CKSegment` (`Segment.lean:115`) is a **single prime theory over a fixed head**; Simpson's world
  is a **pair `(w,d)`** = (𝒯-prime context, label). Different world type, not a refinement.
- `Preorder (CKSegment)` is `le P Q := P.head ⊆ Q.head`; `B_K`'s `≤'` **fixes the domain element
  and moves only the context** — it is not head-inclusion on a single theory.
- `SegmentLindenbaum`'s engine (`quasi_prime_exclusion:73`, `box_refuting_theory:177`,
  `dia_refuting_theory:203`, `quasi_head_realization:251`) extends **one theory with the other
  component fixed** — precisely the sequential construction that task 512 Phase 8-10 found
  unstable. **Simpson's Zorn is over a single object carrying all labels; there is no
  "other component" to fix.** The engine is not reusable, and *should not be reused* — its
  fixed-other-component shape **is** the bug.
- `QuasiPrime` admits `Ω = univ`; Simpson's 𝒯-prime carries **Consistency** (`Γ ⊬_G x:⊥`) as a
  defining clause. Do **not** attempt to generalize `QuasiPrime` — CK/CT/CS4's landed completeness
  needs fallible worlds.

**The four negative guardrails stay as guardrails** (`cs5Incest_forces_symm`,
`cs5TwoSidedR_iff_cs5Tail`, `cs5_symmetric_tail_box_gap`, `cs5Incest_cs5PrimeMreach_false`) —
they certify the prime-theory routes are dead and must not be re-trod. Nothing in Route B touches
or contradicts them.

---

## Deliverable 5 — Guardrail non-triggering (CRITICAL — rigorous)

### `cs5_symmetric_tail_box_gap` (`CS5.lean:712`) — **does not trip; but the naive reason is wrong**

Statement: `QuasiPrime T`, `□(p ∨ □q) ∈ H`, `boxInv H ⊆ T`, `boxInv T ⊆ H`, `q ∉ H` ⟹ `p ∈ T`.

**The trap I nearly fell into (and the dispatch's guardrail is right to demand this check):
the lemma's *argument* DOES go through in the labelled model.** Instantiate `H := Θ(y)`,
`T := Θ(z)` for `yRz`. Then `boxInv Θ(y) ⊆ Θ(z)` holds (by `□E` along `yRz`); `boxInv Θ(z) ⊆ Θ(y)`
holds **too**, because for `𝒯 = {χ_T,χ_5}` the context graph is a classical model of 𝒯 hence
**symmetric**, so `zRy` in `H` and `□E` applies. And `Θ(z)` has the **disjunction property**
(𝒯-prime clause 3). All three hypotheses are satisfiable. **The labelled model does not escape by
lacking the structure.**

**Why it is nonetheless vacuous at the relevant instance.** The lemma's remaining hypothesis is
`q ∉ H` **at a fixed `H`**. Simpson's box-backward witness is **not at a fixed head**: the
semantic box clause is
`(H,Δ),y ⊩ □B iff ∀(H',Δ') ≥ (H,Δ), ∀z, yRz in H' ⟹ z:B ∈ Δ'`,
so refuting `□B` produces a witness in a **strictly larger context** `(H',Δ') ⊇ (H₀,Δ)` where
`Θ'(y) ⊇ Θ(y)` **may contain `q`**. Running the gap-lemma argument at the witness yields not a
contradiction but the *true and harmless* conclusion **`q ∈ Θ'(y)`**. The hypothesis `q ∉ Θ'(y)`
simply **fails**. The lemma is true; it has no instance to bite.

**And this is exactly what CSLib's own source predicted.** `CS5.lean:700-710` (verbatim):
> "The box-backward case must therefore move to a strictly larger head `H' ⊇ H` (here: one
> containing `q`), which enlarges `boxInv H'` in turn. That circularity is the real open problem:
> `H'` and `T` must be built as a **simultaneous maximal pair**, not sequentially (Phases 8-10)."

**Simpson's Prime Lemma builds that simultaneous maximal pair — and this is the single most
important finding in this report.** A **context** `(G,Γ)` is **one object** whose `Γ` carries
labelled formulae for **all labels at once**. Zorn maximalises it against the **single** global
constraint `Γ' ⊬ x:A`. Therefore `Θ(y)` and `Θ(z)` are maximalised **simultaneously**, in one
chain, for every pair of labels. The cross-world invariants `boxInv Θ(y) ⊆ Θ(z)` are **not
side-constraints threaded through the Zorn** (which is what destabilised task 512's construction)
— they are **derived facts**, consequences of `Γ`'s **deductive closure under the (□E) rule**.

> **The mechanism, in one line**: *the labelled framework turns cross-world invariants into
> inference rules of a single consequence relation, so one Lindenbaum on one object delivers all
> of them at once.* That is precisely the operation task 512's single-formula primeness engine
> could not perform, and it is why Route B is not just "a different route" but the correct one.

### `cs5Incest_forces_symm` (`CS5Canonical.lean:643`) — **applies, and is satisfied, not violated**

The dispatch asks: is there still a `≤` with head-monotonicity in the labelled model, and does it
matter? **Yes, and no.** In `B_K`, `head(w,d) := {A | w,d ⊩ A}`:
- `hmono` **holds** (persistence — report 516/01 is right that this is structural and inescapable);
- `hbox` **holds** (`R'((w,d),(w,d'))` ⟹ `boxInv head(w,d) ⊆ head(w,d')`, by the box clause at `w'=w`).

So the guardrail **applies** and yields its conclusion: `boxInv head(u) ⊆ head(w)` whenever `r w u`
— **plain box-symmetry**. **This is a true theorem about `B_K`, not a contradiction**, because
`R_w` is a **primitive graph relation that is a classical model of `{χ_T,χ_5}`** and hence
genuinely symmetric: from `R_w(d,d')` we get `R_w(d',d)`, so `w,d' ⊩ □B` gives `w,d ⊩ B`.

The guardrail was fatal in CSLib's canonical model only in composition with a *second* fact —
`Ω = univ` universally reachable, making plain box-symmetry **false**
(`cs5Incest_cs5PrimeMreach_false`). **`B_K` has no `Ω`**: 𝒯-primeness includes **Consistency**
(`Γ ⊬_G x:⊥`, `:5957`), so no world forces `⊥`, and `botForces := λ_. False` discharges all five
of `CKValidFC`'s `botForces` side conditions vacuously (`CKExtension.lean:90-94`).

**Root difference, named precisely**: in CSLib's canonical model `R` is *derived* from
box-membership (`r Γ Δ := boxInv Γ ⊆ Δ`), so symmetry is a *demand on theory content* and fails.
In `B_K`, `R'` is *primitive graph data* satisfying 𝒯 **by construction (𝒯-primeness clause 0)**,
so symmetry is *given* and box-symmetry is a *consequence*. **The guardrail does not distinguish
these; the model does.**

### `cs5TwoSidedR_iff_cs5Tail` (`CS5Canonical.lean:511`) — **not applicable**

It is a theorem about **quasi-prime theories** under `cs5TwoSidedR`. `B_K`'s worlds are pairs and
`R'` is not a two-sided membership relation. No instance exists. (It remains a correct guardrail
against re-attempting the prime-theory route.)

### `cs5Incest_cs5PrimeMreach_false` (`CS5Canonical.lean:688`) — **not applicable**

It refutes `cs5Incest` for the **specific** relation `cs5PrimeMreach` on `CS5PrimeSegment`. Route B
uses neither. Its engine (`Ω` reachable) is blocked by 𝒯-prime Consistency.

### Verdict

**No guardrail trips.** One (`cs5_symmetric_tail_box_gap`) required real care — its *argument*
transfers, and only the fixed-head hypothesis saves us; one (`cs5Incest_forces_symm`) *applies*
but is *satisfied*. **Nothing here is decisive against Route B.** I flag that the second finding
also **retires report 516/01's residual worry**: head-monotonicity is indeed structural and
inescapable, but it was never the problem — it is compatible with completeness whenever `R` is
primitive rather than membership-derived.

---

## Deliverable 6 — Phase sketch and honest risk

### Phases (9; each ≈ one agent run; ~2050–2450 lines total)

| P | Content | Lines | Risk |
|---|---|---|---|
| **P1** | Labels, graphs (`Graph`, `∪`, `∪{xRy}`, trivial graph `𝒯`), labelled formulae, witness algebra `W(V')`, coinfinite fresh-label supply | 200–250 | Med |
| **P2** | `N_IK(𝒯)` inductive: propositional + `□I`/`□E`/`◇I`/`◇E` + `(R_χ)`; **eigenvariable/freshness side conditions**; weakening/graph-morphism lemmas (Prop. 4.4.1, `:5135`) | 250–300 | **HIGH** — freshness is the classic Lean pain point; consider locally-nameless (CSLib `Languages/Lambda` precedent) |
| **P3** | `Context` + `TPrime` (5 clauses incl. `H ⊨_cl 𝒯`); `𝒯_S5 := {χ_T, χ_5}` | 180–220 | Med |
| **P4** | **Prime Lemma 5.3.1** — Zorn; chain-union closure; verify all 5 𝒯-prime clauses | 300–350 | **HIGH** — the geometric-witness condition (3) is fiddly |
| **P5** | `K^𝒯` + **Canonical Model Lemma 5.3.2** (truth lemma); □-case = fresh label + P4 | 280–330 | Med — □-case is clean |
| **P6** | `B_K` cartesian construction + **Lemma 8.1.2**; **reconcile Simpson's `∃`-◇ with CSLib's Wijesekera `∀≤∃`-◇** (needs `R` monotone + persistence); `botForces := λ_. False` | 200–250 | Med — the ◇ reconciliation is a real obligation |
| **P7** | `B_K ⊨ cs5FCIncest` (5 conjuncts, §D4) ⟹ reuse `cs5_soundness_incest` | 120–150 | **LOW** — pre-verified in this report |
| **P8** | **Lemma 6.2.2** (eliminate `(R_χ)`) + **Lemma 6.1.2/6.2.3** (tree internalization `(Γ⊢_G x:A)*`), incl. **reconstructing the omitted (⊥E)/(∨E) cases** | 400–600 | **HIGHEST** |
| **P9** | C0 (`CS5ModalAxiom ≡ IK+Ax(𝒯_S5)`) + assembly of `cs5_completeness` | 150–200 | Med |

**Sequencing advice**: P1→P2→P3→P4→P5→P6→P7 is the semantic spine and is **independently
valuable** — it lands a countermodel construction. P8 is **separable** and should be dispatched
**early in parallel** (it depends only on P1/P2), because it is the node that can kill the task.
**Do not leave P8 last.**

### The single hardest node

**P8 — Lemma 6.1.2/6.2.3.** Reasons, all grounded: (i) Simpson's proof is self-declaredly informal
(`:6558`); (ii) the two hardest cases are **omitted** as "quite intricate" (`:6544`); (iii) the
treeness invariant is never stated as a lemma (`:6533`); (iv) it is the only spine node with **no
transcribable proof**. Everything else in Route B is transcription; **P8 is reconstruction.**

### Confidence — **~50% (45–55%)**

**For** (why this is much better founded than any prior route):
- The completeness spine (5.3.1, 5.3.2, 8.1.1/8.1.2, 6.2.1) is **rigorous, complete, uniform in 𝒯,
  and covers IS5** — read from the source, not fragments.
- **All four guardrails verified non-triggering**, with a named mechanism, not a hope.
- The `cs5_symmetric_tail_box_gap` wall is **explained and dissolved**: Simpson's Zorn-over-contexts
  **is** the simultaneous maximal pair CSLib's source itself identified as the missing object.
- The §8.1 soundness failure — the scariest thing in Chapter 8 — **provably does not touch the
  completeness direction** (`:9613`).
- **Real reuse found where 516/02 predicted none**: `cs5_axiom_sound_incest`/`cs5_soundness_incest`
  transfer, because `B_K ⊨ cs5FCIncest` (verified conjunct-by-conjunct).
- The classical steps (decidability by case analysis/contraposition, `:11225`) are free in Lean.

**Against** (why I am not saying "high"):
- **P8 is unwritten mathematics for a mechanizer.** Simpson omits the (⊥E)/(∨E) cases and disclaims
  formality. This is precisely the "where Simpson is an outline, SAY SO" case the dispatch demanded
  — **and it lands on the adequacy bridge, which is unavoidable.**
- **P2's eigenvariable/freshness conditions** are a notorious Lean cost centre; my line estimate
  could be off by 2× if a locally-nameless encoding is needed.
- **~zero reuse of the Henkin/segment stack** — 7 of 9 phases are greenfield.
- Two obligations Simpson treats as trivial are **real work in Lean**: the ◇-clause reconciliation
  (P6) and the `R`-monotonicity-under-`≤` IL-model condition (P6/P7).
- **Base rate**: this problem has walled four times (atom-sum, one-sided-R, two-sided-R,
  independent-≤/Route A), and reports 05, 06, 516/01 all over-rated their route. I am not exempt.

**I did not find a fatal gap in Route B.** I looked hard for one — I checked whether Chapter 8's
IS5 exclusion killed it (it doesn't; wrong chapter for completeness), whether the §8.1 soundness
failure killed it (it doesn't; wrong direction), whether §6.3's incompleteness result killed it
(it doesn't; that is **directedness `ψ_1111`**, not S5 — though note the *irony* that §6.3's
inexpressibility condition "`m=n=0` implies `k=l=0`" is **violated by exactly the `(1,1,0,0)`
instance CSLib transcribes as `cs5Incest`**, which is why Simpson uses the **geometric theory
`{χ_T,χ_5}`** rather than the Marin klmn condition — a planner should follow **Simpson's** frame
presentation, not Marin's, inside the construction, and only *derive* `cs5FCIncest` at the end,
as P7 does), and whether the guardrails killed it (they don't). **The residual risk is
concentrated, named, and priced: it is P8.**

**Recommendation**: `plan`, with P8 dispatched **early and in parallel** as the gating node. If P8
cannot be closed after a bounded attempt, the task should return to `[BLOCKED]` with P1–P7 landed
as a genuine, reusable countermodel construction — **not** with a `sorry`.

---

## Adversarial self-verification

- *"Ch. 8 excludes IS5"* — **verbatim** (`:10240`): "we fix L as any logic in Dec_𝒯, **other than
  IS5** … Thus `𝒯 ⊆ {χ_D, χ_T, χ_B}`." Corroborated structurally: `T-Comp` (`:10494`) has **no
  transitivity clause**. Corroborated a third time by `Dec_𝒯 = {∅,{χ_D},{χ_T},{χ_B},{χ_D,χ_B},{χ_T,χ_B}}`
  (`:8357`) — IS5 ∉ Dec_𝒯; its decidability is a **known** result (`:8362`, `:3929`).
- *"Lemma 8.2.5 is not what report 516/02 said"* — **verbatim** (`:10520`): "If `(H,A)` is a 𝒯-prime
  bounded context then **`T-Comp(H) ⊨_cl 𝒯`**." Symmetry is one clause of an easy remark; the
  proof's substance is **seriality** (`:10523-10534`). 516/02 quoted the *proof fragment* because
  its chunk (140 bytes) **truncated the statement**. I verified chunk sizes directly.
- *"The spine is Ch. 5"* — grounded: TOC "**5. Meta-logical completeness**" (`:255`); Lemma 5.3.1
  (`:5990`), Lemma 5.3.2 (`:6102`); Ch. 8.2.1 itself says "The construction closely follows the
  **earlier completeness proof of Section 5.3**" (`:10298`).
- *"Completeness survives the §8.1 soundness failure"* — **verbatim** (`:9613`): "**nowhere in the
  proof of completeness have we used the assumption that `G` is a tree**." Not an inference.
- *"The gap lemma's argument transfers"* — I **re-derived it in the labelled setting** and found it
  **does** go through (□E along `yRz`, disjunction property, □E along `zRy` via symmetry), then
  located the *actual* escape (fixed-head hypothesis vs. context enlargement). I did **not** assume
  the labelled model lacks the structure. This is the check that would have caught reports 05/06.
- *"`B_K ⊨ cs5FCIncest`"* — I derived all **five** conjuncts by hand against
  `CS5Canonical.lean:258-263` (read at source), identifying the two side conditions required
  (`R_w` equivalence; `R` monotone under `≤`). Independently corroborated by Simpson `:9966`
  ("`B_K` **is indeed a birelation model of 𝒯**") and `:9985` (Thms 6.2.1+8.1.4 ⟹ soundness **and
  completeness** of `IKS₁…Sₙ` w.r.t. birelation models).
- *"P8 is the hardest node"* — grounded in Simpson's **own** hedges (`:6544` "quite intricate",
  `:6558` "without too much formality", `:6533` treeness care), not in my estimate of difficulty.
- *Against my own optimism*: Simpson says (`:9990`) these birelation results "are obtained **more
  easily by considering the Hilbert systems directly (as in Section 3.3)**" — i.e. he thinks the
  **prime-theory route is easier**. That is exactly the route CSLib has **mechanically refuted**
  four times. I am explicitly **declining Simpson's own methodological advice**, on the strength of
  CSLib's guardrails. If those guardrails were somehow wrong, Route B would be unnecessary — but
  they are landed, sorry-free and axiom-clean, so this is a considered disagreement, not an
  oversight.
- *Residual uncertainty I cannot discharge from the source*: whether P8's omitted (⊥E)/(∨E) cases
  are **merely tedious** or **conceptually hard**. Simpson's "the difficulties are similar to those
  encountered in the (◇E) case" (`:6544`) suggests tedious-but-tractable, and the (◇E) case **is**
  written out — but that is his word for it, not a proof, and it is the whole of my P8 risk.
  **Anyone who tells you P8 is a transcription has not read `:6544`.**
- **Zero-debt / reuse-first**: no `sorry`, no new axiom proposed anywhere. Reuse ledger checked at
  source (`Basic.lean:72,140`; `DerivationTree.lean:134,201`; `CS5.lean:93-99,126,182`;
  `Forcing.lean:67,122`; `CKExtension.lean:86-94`; `CS5Canonical.lean:258-263,278`). BibKey
  `Simpson1994` grounded (`index.json`, `bib_key: Simpson1994`); `Pacheco2024` for `CS5 ≡ IS5`.
- **Corpus-integrity finding (actionable)**: the ingested chunks for `simpson_1994_intuitionisticmodallogic`
  are **unusable for lemma statements** — 1091 chunks, ~312 bytes mean, key chunks 122–140 bytes
  containing **truncated titles with `> …` preview artefacts**. All prior Simpson citations in
  tasks 512/516 rest on these fragments. I worked from the **source PDF**
  (`/home/benjamin/Downloads/Simpson_1994_IntuitionisticModalLogic.ocr.pdf`, `pdftotext -layout`,
  13,488 lines; line numbers above refer to that extraction). **Re-ingestion of this document is
  strongly recommended** before any further Simpson-grounded dispatch.

## One-line answer

Simpson's rigorous IS5 completeness is **Chapters 5+6+8.1**, not Chapter 7-8 (which is
decidability/f.m.p. and **explicitly excludes IS5**): the spine is **Prime Lemma 5.3.1** (Zorn over
**whole labelled contexts** — the simultaneous maximal pair CSLib's source named as the missing
object), **Canonical Model Lemma 5.3.2** (box-backward by **fresh label + (□I)**, no bounded
Lindenbaum), and **Theorem 6.2.1** (Hilbert⟺labelled adequacy); **no guardrail trips** —
`cs5_symmetric_tail_box_gap`'s argument *does* transfer but its fixed-head hypothesis has no
instance once box-backward enlarges the context, and `cs5Incest_forces_symm` is *satisfied* because
`B_K`'s `R` is primitive graph data, not membership-derived; `cs5_soundness_incest` **transfers**
(`B_K ⊨ cs5FCIncest`, verified); the hardest node is **Lemma 6.1.2's tree internalization**, which
Simpson presents informally and whose (⊥E)/(∨E) cases he **omits** — **~50% confidence**,
`next_action_hint = plan` with that node gated and dispatched first.
