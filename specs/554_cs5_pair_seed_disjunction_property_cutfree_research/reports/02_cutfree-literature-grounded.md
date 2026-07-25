# CS5 Pair-Seed Right Exclusion, Round 2: Literature-Grounded Assessment

**Verdict: (b) refutation, plus a corrected target and a concrete non-sequent route.**

The named obligation `CS5PairSeedDisjunctionProperty` is **false as literally stated** — a
machine-checked, sorry-free refutation is included. Once repaired with the hypothesis it is
missing, the two Strassburger-group papers give a precise, citable answer to each of the three
questions in the brief, and the answers are: one **negative**, one **positive but for the wrong
logic**, one **positive but prohibitively expensive**. A fourth route — not proposed in round 1
and not the forbidden collapse route — is identified as the cheapest concrete lead, with its own
residual gap named.

All literature claims below cite specific numbered results read in the ingested chunks. Where a
paper stops short, that is stated.

---

## 0. Round-2 probes (both sorry-free)

| File | Axioms |
|------|--------|
| `/home/benjamin/Projects/cslib/specs/554_cs5_pair_seed_disjunction_property_cutfree_research/probes/seed_refutation.lean` | `[propext, Classical.choice, Quot.sound]`, no `sorryAx` |
| `/home/benjamin/Projects/cslib/specs/554_cs5_pair_seed_disjunction_property_cutfree_research/probes/cs5_subset_is5.lean` | `[propext, Quot.sound]`, no `sorryAx` |

Round 1's two probes are unaffected; nothing below contradicts them.

---

## 1. The named obligation is refutable as stated

`CS5PairSeedDisjunctionProperty H A` (`CS5Completeness.lean:373-375`) is quantified over **all**
`H` and **all** `A`, with no hypothesis relating them. That is fatal.

The right component of the seed is
`cs5PairTauR '' (modalDeductiveClosure CS5ModalAxiom (boxInv H))`, and *every `CS5` theorem* lies
in `modalDeductiveClosure CS5ModalAxiom S` for **every** `S` (witness list `[]`). So for any
`CS5`-provable `A`, `τ_R A` is **literally an element of the seed**, and round 1's `hOpen ↔ hR`
equivalence carries the failure straight to the named obligation.

Minimal instance, machine-checked in `seed_refutation.lean`:

```
A := ⊥ → ⊥   (the `CS5ModalAxiom.efq ⊥` instance)
probe_refute_disjunctionProperty : ∀ H, ¬ CS5PairSeedDisjunctionProperty H (⊥ → ⊥)
```

A second, `H`-driven refutation is also included (`probe_refute_hR_of_boxMem`): whenever
`□A ∈ H`, then `A ∈ boxInv H`, so `τ_R A ∈ cs5PairSeed H` directly.

### 1.1 The corrected statement

The obligation must carry the exclusion hypothesis its intended caller supplies. In descending
order of strength, the candidates are:

```
(i)   A ∉ modalDeductiveClosure CS5ModalAxiom (boxInv H)          -- "A ∉ K"
(ii)  Proposition.box A ∉ H                                        -- caller's actual hypothesis
```

`(ii)` alone is **not** sufficient — it does not imply `(i)`, because `K = cl_{CS5}(boxInv H)`
saturates, and `A` can enter `K` from other boxes in `H` (e.g. `□(B → A), □B ∈ H` with
`□A ∉ H`). `(i)` is the correct hypothesis; it is implied by `(ii)` only when `H` is
`CS5`-deductively closed **and** `boxInv H` is already `CS5`-closed, neither of which the
definition assumes.

**Recommended repair** (mechanical, no research risk):

```lean
def CS5PairSeedRightExclusion (H : Set (Proposition Atom)) (A : Proposition Atom) : Prop :=
  A ∉ modalDeductiveClosure (@CS5ModalAxiom Atom) (boxInv H) →
    cs5PairTauR A ∉ modalDeductiveClosure (@CS5PairAxiom Atom) (cs5PairSeed H)
```

Round 1's R2/R3/R4 reductions all go through unchanged under the added hypothesis, since they
never inspect `H`.

This matters beyond hygiene: **any proof attempt against the current statement is doomed**, and
the module's `hL`/`hR` hypotheses in `cs5Pair_derivExcludes_of_disjunctionProperty` are equally
unsatisfiable at theorem-instances of `A`. A caller instantiating that theorem at
`A := ⊥ → ⊥` cannot discharge them.

---

## 2. Question 1 — Marin–Morales–Strassburger's fully labelled system

**Answer: it yields the analogous result for `IS5`, not for `CS5`. Its cut-admissibility buys
exactly one thing here, and it is not the thing round 1 hoped for.**

### 2.1 What the paper actually proves

- **System `labIK≤`** (Figure 1, §3). Sequents `R, Γ ⟹ ∆` carry **both** relational atoms `xRy`
  and `x ≤ y`; multi-conclusion; every rule invertible.
- **Theorem 3.3**: for any `A`, TFAE — (1) `A` is a theorem of **IK**; (2) provable in
  `labIK≤ + cut`; (3) provable in `labIK≤`; (4) valid in every birelational frame.
- **Theorem 6.1 (cut admissibility)** for `labIK≤`; proof by induction on the number of cuts,
  applying Lemma 6.5 to the leftmost-topmost cut.
- **§7, Theorem 7.1 [PS86]**: a frame validates the one-sided Scott–Lemmon axiom
  `◇^k □^l A ⊃ □^m ◇^n A` iff it satisfies the *intuitionistic klmn-incestuality* condition
  (Figure 2): *if `wR^k u` and `wR^m v` then there exists `u'` with `u ≤ u'` and there exists `x`
  with `u'R^l x` and `vR^n x`* — note the one-sided `≤`-mediation.
- **Theorem 7.2**: TFAE for `IK + ◇^k□^l A ⊃ □^m◇^n A` — Hilbert theoremhood, `labIK≤ + ⊠g_klmn
  + cut`, cut-free `labIK≤ + ⊠g_klmn`, and validity in klmn-incestuous birelational frames. The
  cut case for `⊠g_klmn` is "straightforward as the `⊠g_klmn` rule only manipulates the
  relational context". §8 states the generalisation is to the **class** of logics defined by
  one-sided intuitionistic Scott–Lemmon axioms (plural).
- **Remark 7.3**: with `g1111` added, `◇(□(a∨b) ∧ ◇a) ∧ ◇(□(a∨b) ∧ ◇b) ⊃ ◇(◇a ∧ ◇b)` is
  **not** derivable, exhibited by a failed proof search.

### 2.2 Alignment with CSLib's `CS5`, and where it stops

Every modal axiom of CSLib's `CS5ModalAxiom` beyond `k`/`kdia` is a one-sided Scott–Lemmon
axiom in MMS's sense:

| CSLib constructor | Formula | `(k,l,m,n)` |
|---|---|---|
| `tBox` | `□A → A` | `(0,1,0,0)` |
| `tDia` | `A → ◇A` | `(0,0,0,1)` |
| `fourBox` | `□A → □□A` | `(0,1,2,0)` |
| `fourDia` | `◇◇A → ◇A` | `(2,0,0,1)` |
| `bBox` | `A → □◇A` | `(0,0,1,1)` |
| `bDia` | `◇□A → A` | `(1,1,0,0)` |

So MMS's framework covers `IS5` exactly. **But `labIK≤`'s base is `IK`, not `CK`** — §4 derives
`k3`, `k4`, `k5` in the system (chunks for k3, k4, k5 are explicit derivations). `CS5` has none
of `k3`/`k4`/`k5` as primitives. There is therefore **no `labIK≤`-style system for `CS5`** in this
paper, and the paper makes no claim to one. Restricting `labIK≤` to recover `CK` is not addressed
and is not obviously possible: the `≤`-mediated `id`/`⊃L`/`□L` rules and `F1`/`F2` are precisely
what force `k3`/`k4`.

### 2.3 What its cut admissibility actually buys here

Not conservativity for `CS5Pair`. What it buys is **methodological confirmation for
non-derivability arguments**: Remark 7.3 is a worked demonstration that this system is precise
enough to *fail* on a non-theorem, which is the shape of argument an exclusion result needs. And
Theorem 7.2's item (4) means the syntactic and semantic sides coincide exactly — so for the
`IK`-family one may argue semantically with no loss, which is what §5 below exploits.

**Honest limit**: MMS never state a conservativity or theory-exclusion result. Nothing in the
paper is a two-label conservativity theorem; deriving one would be new work built on their
system, not a citation.

---

## 3. Question 2 — Arisaka–Das–Strassburger's nested sequents for the constructive cube

**Answer: yes, there is a genuine cut-free system that covers CSLib's exact `CS5` axiom set. The
Kripke-completeness disclaimer does *not* undercut the route. The cost does.**

### 3.1 The cut-free result, and that it covers CSLib's `CS5`

- **Definition 6.2 (safe pair)**: `⟨X, Y⟩` with `X ⊆ {t,4}`, `Y ⊆ {d,b,5}`, such that if `t ∈ X`
  and `5 ∈ Y` then `b ∈ Y`, and if `b ∈ Y` or `5 ∈ Y` then `4 ∈ X`.
- **Theorem 5.2 (cut-free completeness)** and **Theorem 6.3 (cut elimination)**: for a safe pair,
  every theorem of `HCK + X + Y` is provable in `NCK' + X^#_G + Y^[]` (no cut).
- ADS15's axiom forms (eq. 1.2) match CSLib's constructors exactly: `t = (□A ⊃ A) ∧ (A ⊃ ◇A)`
  (`tBox`/`tDia`), `4 = (□A ⊃ □□A) ∧ (◇◇A ⊃ ◇A)` (`fourBox`/`fourDia`), `b = (A ⊃ □◇A) ∧
  (◇□A ⊃ A)` (`bBox`/`bDia`).
- CSLib's `CS5ModalAxiom` is therefore `HCK + t + 4 + b`. Take `X = {t,4}`, `Y = {b}`: the first
  side condition is vacuous (`5 ∉ Y`), the second holds (`b ∈ Y` and `4 ∈ X`). **Safe pair.**
  So Theorems 5.2/6.3 apply *verbatim* to CSLib's exact axiom set, with no need to settle whether
  `5` is separately derivable or whether CSLib's `CS5` is ADS15's cube-node `CS5`.
  (`CTB = HCK + t + b` is in ADS15's *excluded* list precisely because `4 ∉ X` there.)

### 3.2 The Kripke-semantics disclaimer does not undercut the route

ADS15 §4 opens: *"To our knowledge there are no standard Kripke semantics for all the various
constructive modal logics and consideration of this issue is beyond the scope of this work.
Therefore we show soundness of our rules with respect to the Hilbert system."* Their soundness
(Thm 4.1) and completeness (Thm 5.1) are both stated **against `HCK + X + Y`**.

That is exactly the right currency for this task. The obligation
`τ_R A ∉ modalDeductiveClosure CS5PairAxiom (cs5PairSeed H)` is a statement about **Hilbert
derivability**, not about any semantics. A Hilbert-relative cut-elimination theorem is precisely
what an exclusion argument consumes. **The disclaimer is therefore not an obstacle here** — and
ADS15 themselves use cut-elimination for a non-derivability result: "From our cut-elimination
result in Section 6 it will follow that the `5` axiom alone is not enough to derive `k3` or `k5`."

### 3.3 Where it stops short — the decisive gap

ADS15 give a cut-free system for **`CS5` over a single signature**. The obligation is about
**`CS5Pair`**: `CS5` on two tagged copies of `Atom ⊕ Atom` *plus* two signature-mixing cross
schemas `□(τ_L B) → τ_R B` and `□(τ_R B) → τ_L B`, *plus* a propositional core quantified over
the **whole** `Proposition (Atom ⊕ Atom)` type including genuinely mixed formulas
(`CS5Completeness.lean:94-107` documents that the whole-type quantification is forced by the
primeness engine).

Nothing in ADS15 covers this. Getting there requires:

1. Formalising nested sequents (trees of polarity-tagged multisets, output pruning `Γ⇓`, output/
   input contexts) — ADS15 §2.
2. `NCK'` with `t•/t◦/4•/4◦/b[]` — §3.
3. Soundness (Thm 4.1, Lemmas 4.2–4.9) and completeness (Thm 5.1) against the Hilbert system.
4. Cut elimination (Thm 6.3): super-rules `s4•/s4◦/s4□/s4♦/sb[]` (Figure 6), the auxiliary cuts
   `♦cut`/`□cut` (6.2), anchored-cut analysis, and a well-ordering `≪` on cut-values.
5. **Then** extending all of the above to the two-label mixed-signature pair system, which is new
   mathematics not in the paper.

Steps 1–4 alone are an 18-page cut-elimination argument. In Lean this is a multi-thousand-line,
multi-task effort with no partial payoff for this obligation until step 5 also lands. **This is
not a route worth opening for a single exclusion lemma.**

---

## 4. Question 3 — does §4.3's `b ⊢ k3, k5` bear on the box-over-disjunction obstruction?

**Answer: no. Cleanly and definitively no.**

ADS15's result (Intro; derivations at eq. (4.3), p. 13; and Pacheco's Theorem 3 restating it) is:

- `k3 : ◇(A ∨ B) ⊃ (◇A ∨ ◇B)` — **diamond** over disjunction;
- `k5 : ◇⊥ ⊃ ⊥`.

Their nested-sequent derivation of `k3` uses `b[]` twice, `∨•` twice, and `♦◦`; `k5` uses
`⊥•`, `b[]`, `♦•`. They add: "since `b` is derivable in `CS5`, both `k3` and `k5` are derivable in
`CS5`."

Round 1's obstruction is `□(A ∨ B) → (□A ∨ □B)` — **box** over disjunction. This is not `k3`,
not a weakening of `k3`, and **not a theorem of classical `S5`** (two-world universal frame,
`A` at one world, `B` at the other: `□(A∨B)` holds, neither `□A` nor `□B` does). No paper about
constructive-versus-intuitionistic modal logic can supply it, because the gap is not
constructive-versus-classical.

**Consequence for both consumers**: round 1's §2.2 translation table row for `∨`, and task 537's
`sigAt` context-fold, are blocked by a *classical* non-theorem. No amount of strengthening the
base logic — `k3`, `k4`, `k5`, collapse to `IS5`, anything — will unblock them. Any route that
needs `□(A∨B) → □A ∨ □B` must be abandoned outright, not deferred.

---

## 5. The route the literature actually points to: a product model over `IS5`

Round 1's docstring critique (§R6) noted the two-label product-model idea and judged it circular,
because it appeared to need a `cs5FC` model with `x ⊩ H`, `y ⊮ A` in one cluster — the very thing
the `CS5` truth lemma is being built to produce. **The circularity dissolves if the product is
taken over an `IS5` model instead of a `cs5FC` one**, because `IS5` completeness is already landed
in CSLib (`Intuitionistic/IS5.lean`, `is5_completeness`, against `is5FC` = reflexive + transitive
+ symmetric).

### 5.1 The step that makes this legitimate is trivial, and now machine-checked

`CS5ModalAxiom`'s constructors are a **literal subset** of `IS5ModalAxiom`'s (`IS5ModalAxiom`
adds `kdisj` = `k3`, `kfs` = `k4`, `kbot` = `k5`; `CS5ModalAxiom` adds nothing). Probe
`cs5_subset_is5.lean` proves, sorry-free:

```
cs5Axiom_to_is5Axiom          : CS5ModalAxiom φ → IS5ModalAxiom φ
cs5_deriv_to_is5              : Deriv CS5ModalAxiom Γ φ → Deriv IS5ModalAxiom Γ φ
cs5_closure_subset_is5_closure: cl_{CS5} S ⊆ cl_{IS5} S
```

This is the **easy** direction only. It is not the `CS5 = IS5` collapse; it needs no theorem from
Pacheco and no `idb` derivation.

### 5.2 The construction

To refute `τ_R A ∈ cl_{CS5Pair}(cs5PairSeed H)` it suffices to exhibit **one** model in which
every `CS5PairAxiom` instance is valid at every world, the seed is forced at some world, and
`τ_R A` is not.

Let `M = ⟨W, ≤, r, val⟩` be an `is5FC` model. Define `M'` on `W × W`:

- `(u,v) ≤' (u',v')` iff `u ≤ u'` and `v ≤ v'`;
- `(u,v) r' (s,t)` iff `r u s` and `r v t`;
- `val' (u,v) (inl p) := val u p`, `val' (u,v) (inr p) := val v p`.

Frame conditions transfer componentwise (reflexivity, transitivity, symmetry, `f1`, `f2`).

**Projection lemma** (induction on `Proposition Atom`):
`M', (u,v) ⊩ cs5PairTauL φ ↔ M, u ⊩ φ` and `M', (u,v) ⊩ cs5PairTauR φ ↔ M, v ⊩ φ`.
The `→`, `□`, `◇` cases each need a witness in the *other* coordinate; reflexivity of `r` and of
`≤` supplies it.

Given the projection lemma:

- `CS5PairAxiom.left`/`.right`: valid by `is5_axiom_sound` composed with `cs5Axiom_to_is5Axiom`
  and the projection lemma.
- Propositional core at the whole type: valid, since `M'` is an ordinary birelational model over
  `Atom ⊕ Atom` and these are intuitionistic tautologies — **this is the piece the relabeling
  retraction of round 1 §R5 could never handle**, and the product model handles it for free
  because it interprets *all* of `Proposition (Atom ⊕ Atom)`, mixed formulas included.
- `cross1` at `(u,v)`: `(u,v) ⊩ □(τ_L B)` gives `s ⊩ B` for all `(s,t)` with `(u,v) r' (s,t)`;
  taking `s := v` requires **`r u v`**. `cross2` symmetrically requires `r v u`.

Then with `u ⊩ H` and `v ⊮ A` and `r u v`, the seed is forced at `(u,v)` (the right component
because `B ∈ boxInv H ⇒ u ⊩ □B ⇒ v ⊩ B`, and `K = cl_{CS5}(boxInv H)` follows by soundness), while
`τ_R A` is not. Exclusion established.

### 5.3 The two residual obligations of this route — stated, not hidden

**(R-a) Totality.** `cross1`/`cross2` must be valid at *every* world of `M'`, because
necessitation is a rule of `modalDerivationSystem`. That forces `r u v` for **all** `u, v` — i.e.
the base model's `r` must be **total**. Restricting to `{(u,v) | r u v}` does not work: that set
is closed under `r'` (by symmetry + transitivity) but **not** under `≤'`, because CSLib's `f2`
(`r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u'`) moves the *first* coordinate to a `≤`-successor rather
than fixing it. So the obligation is:

> Every `IS5`-consistent set has an `is5FC` model whose accessibility relation is total.

Classically this is the point-generated-subframe argument for `S5`. Birelationally it is exactly
the delicate interaction MMS §7/§8 discuss (their Theorem 7.1 condition is `≤`-mediated on one
side; their §8 explicitly flags that Simpson departed from direct frame correspondence for
related reasons). **This is unverified against a local source and must be probed before planning
around it.** It is the same family of difficulty that produced `cs5Incest` being "mechanically
false on every world type tried" in `CS5Canonical.lean`.

**(R-b) `CS5` → `IS5` for the hypothesis.** The construction discharges
`τ_R A ∉ cl_{CS5Pair}(seed)` from `□A ∉ cl_{IS5}(H)`. The caller supplies `□A ∉ H` with `H` only
`CS5`-prime. Bridging those is a single-signature conservativity statement:

> `H` `CS5`-closed, `□A ∉ H` ⟹ `□A ∉ cl_{IS5}(H)`.

This is **weaker and better-shaped** than the two-label mixed-signature statement round 1
isolated: one signature, one label, two standard Hilbert systems. It is the statement ADS15's
cut-free `CS5` (§3.1) or a repaired Pacheco (§6) would attack.

**It is also adjacent to the forbidden collapse route.** Per the mandate I am flagging this and
stopping: I have not pursued `idb`, have not attempted any `CS5 → IS5` bridge, and am not
recommending the collapse. If the residual `(R-b)` is judged to be the collapse in disguise, that
is a call for the task owner, not for me.

### 5.4 Why this beats the sequent routes

| Route | New Lean infrastructure | Residual research gap |
|---|---|---|
| ADS15 nested sequents | nested sequents + `NCK'` + soundness + completeness + cut-elim (18 pp.) **and** a new pair extension | the pair extension is unpublished mathematics |
| MMS `labIK≤` | labelled sequents + 15 rules + cut admissibility + `⊠g_klmn` | system is for `IK`, not `CK`; no `CS5` version exists |
| Product model over `IS5` (§5) | product frame + projection lemma (~200-400 lines, all standard induction) | (R-a) totality; (R-b) single-signature `CS5`/`IS5` conservativity |

---

## 6. Pacheco's Lemma 16: where exactly it fails, read from the source

The module docstring (`CS5Completeness.lean:359-362`) attributes the obligation to
[Pacheco2024] Lemma 16 and says the published proof uses `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`. Confirmed verbatim
from the source, and it is worth recording precisely which two lemmas are affected.

**Lemma 16** (`∼_c` is backward confluent). The proof builds `Υ :=` the MP-closure of
`Γ□ ∪ {◇ϕ | ϕ ∈ Σ}`, shows `Υ□ ⊆ Σ`, `Σ ⊆ Υ◇`, `⊥ ∉ Υ`, then takes `Θ` maximal with those
properties and argues:

> "Suppose `ϕ ∨ ψ ∈ Θ`. Then if `ϕ ∉ Θ` and `ψ ∉ Θ`, we would have that `¬ϕ ∈ Θ` and `¬ψ ∈ Θ`.
> By MP, we would have `¬(ϕ ∨ ψ) ∈ Θ`, a contradiction."

The step `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` is **negation-completeness**, valid for classical maximal consistent
sets and invalid for a set merely maximal with respect to the stated closure constraints. This is
the defect.

**Lemma 18** inherits it ("As in the proof of Lemma 16, if `ϕ ∨ ψ ∈ Σ` then `ϕ ∈ Σ` or `ψ ∈ Σ`")
and adds a second problem: it asserts that the base pair `⟨Υ, Φ⟩` satisfies the whole constraint
list including `ϕ ∉ X ∪ Y` and `Y□ ⊆ X`, `Y ⊆ X◇`, but only `ϕ ∉ Υ` and `⊥ ∉ Φ` are argued;
`ϕ ∉ Φ` and the two cross-closure conditions on `Φ` are asserted, not proved.

**This is exactly the CSLib obligation.** Pacheco's Lemma 18 is the pair-Lindenbaum statement
`□ϕ ∉ Γ ⟹ ∃∆, Σ. Γ ⊑ ∆ ∼ Σ ∧ ϕ ∉ Σ`; his unjustified "`⟨Υ, Φ⟩` satisfies these properties" is
precisely the seed-exclusion `τ_R A ∉ cl(seed)`. CSLib's `cs5PairSeed`/`prime_set_exclusion`
architecture is the *correct* repair shape — it makes the excluded formula an explicit hypothesis
rather than deriving primeness from maximality — and the residual obligation is exactly the step
Pacheco skipped. §1.1's missing hypothesis is the same omission reproduced in the Lean statement.

Also worth recording: Pacheco's headline result is that **`CKB = IKB`**, and his §4 concludes
"this also implies that constructive and intuitionistic variations of DB, TB, KB5, and **S5**
coincide." That is `CS5 = IS5` — the exact statement the deferred collapse route would need. It
rests on Lemmas 16/18. **So the collapse route's literature basis is the same unsound argument
this task exists to repair.** Anyone proposing that route should know it is not citable as
published.

---

## 7. Second consumer: labelled `CS5` general soundness

Direct answer to the brief's question — *"is a context-fold that splits compound context facts
derivable without the box-over-disjunction bridge?"*:

**No, and §4 upgrades round 1's answer from "not as a repair to the fold" to "never".** The
missing bridge `□(A∨B) → (□A ∨ □B)` is not a constructive-versus-intuitionistic gap; it is
invalid in classical `S5`. `k3`/`k4`/`k5`, the `IS5` collapse, and every axiom in the intuitionistic
Scott–Lemmon family leave it underivable. The `sigAt` context-fold cannot be repaired by
strengthening the logic, and no `--lit`-grounded strengthening will change that. Round 1's
conclusion that the `sigAt` freeze is not the binding constraint is confirmed and strengthened.

**What that consumer gains from §5**: if the product-model technique lands, it is directly
reusable there. The fold exists to reduce a multi-label labelled derivation to a single unlabelled
`CS5` formula; a product/`n`-fold model interprets each label at its own coordinate and makes the
fold unnecessary — adequacy is stated coordinate-wise, exactly as MMS state labelled adequacy
label-wise (their Definition 5.1, `G`-interpretations `⟦·⟧` mapping labels to worlds). That is the
same mechanism, and it is far cheaper than formalising `labIK≤`. **One piece of work still
unblocks both consumers**, but it is the product-model construction, not a sequent calculus.

---

## 8. Recommendations

### 8.1 Land now (mechanical, no research risk)

1. **Fix the refutable statement** per §1.1 — add the `A ∉ cl_{CS5}(boxInv H)` hypothesis. Land
   `probe_refute_disjunctionProperty` as a regression test so the unconditioned form can never be
   reintroduced.
2. Land round 1's §4.1 promotions (the `hOpen ↔ hR` equivalence, `hR → hL`, single-hypothesis
   `derivExcludes`, the retraction bound) under the corrected statement.
3. Land `cs5Axiom_to_is5Axiom` / `cs5_deriv_to_is5` / `cs5_closure_subset_is5_closure` — small,
   library-grade, and load-bearing for §5.
4. **Docstring corrections**: replace "A correct proof is expected to require a
   cut-free/nested-sequent argument ([Marin2021])" — §2 shows [Marin2021] is for `IK`, not `CK`,
   and §3 shows the applicable cut-free system is [ADS15] but at prohibitive cost. Replace
   "No semantic witness exists" (§5 shows the product model is a genuine candidate). Correct
   Non-Goal 2's stated reason (round 1 §R5).

### 8.2 Next research step: de-risk (R-a) before planning

Do **not** open a nested-sequent or labelled-calculus formalisation task. Instead spend one
focused probe on §5.3's obligation (R-a): *does every `IS5`-consistent set have an `is5FC` model
with total `r`?* This is a small, decidable-by-probe question whose answer determines whether the
whole product-model route is viable. If (R-a) holds, the product construction is ~200-400 lines
of standard induction and the task reduces to (R-b). If (R-a) fails, the route is dead and the
task should be marked `[BLOCKED]` with the cost table in §5.4 as the justification.

### 8.3 Not adopted

The fallback collapse route (derive `idb`, bridge `CS5 → IS5`) remains **not adopted**, per the
mandate. §6 adds a reason to be wary of it independent of the mandate: its published basis
(Pacheco's `CS5 = IS5`) rests on the same unsound Lemma 16. §5.3's residual (R-b) is adjacent to
it; that adjacency is flagged for the task owner and not pursued here.

---

## 9. References

Local corpus (all read in chunk form via `literature-search.sh --include-unverified`):

- **[ADS15]** R. Arisaka, A. Das, L. Straßburger, *On Nested Sequents for Constructive Modal
  Logics*, LMCS 11(3:7), 2015. `doc_id: arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics`.
  Cited: §1 (`k1`–`k5`, constructive countermodels), eq. (1.2) axiom forms, Figure 2 (`NCK`),
  Figures 3–4 (rules for `d,t,4` and structural `d,t,b,4,5`), Theorem 4.1, Theorem 5.1,
  Theorem 5.2, Definition 6.2 (safe pair), Theorem 6.3, Figure 6 (super rules), eq. (4.3)
  (`b ⊢ k3, k5`), §7 Conjecture 7.1.
- **[MMS21]** S. Marin, M. Morales, L. Straßburger, *A Fully Labelled Proof System for
  Intuitionistic Modal Logics*, 2021. `doc_id: marinmoralesstrassburger_2021_fully_labelled_proof_system_intuitionistic_modal`.
  Cited: Definition 2.1 (`F1`/`F2`), Definition 2.2, Figure 1 (`labIK≤`), Theorem 3.3,
  Propositions 3.1–3.2, §4 (derivations of `k1`–`k5`), Definition 5.1, Theorem 5.3, Theorem 6.1,
  Lemmas 6.2–6.3, §7 (Theorem 7.1 [PS86], `⊠g_klmn`, Theorem 7.2, Remark 7.3), §8.
- **[Pacheco24]** L. Pacheco, *Collapsing Constructive and Intuitionistic Modal Logics*,
  arXiv:2408.16428v2. `doc_id: pacheco_2024_collapsingconstructiveandintuitionisticmodallogics`.
  Cited: Definitions 1–2, 4–5, 7; Theorem 3; Propositions 6, 9, 10; Theorem 13; Lemmas 14–20; §4.

CSLib:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` — host module
  (`CS5PairAxiom` 90-150, `cs5PairSeed` 289, `CS5PairSeedDisjunctionProperty` 373).
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean:150-220` — `CS5ModalAxiom`.
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5.lean` — `IS5ModalAxiom`, `is5FC` (155),
  `is5_axiom_sound` (172), `is5_soundness` (258), `is5_completeness`.
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean:76-88` —
  `modalDeductiveClosure`, `modal_subset_deductive_closure`.
- `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` — `prime_set_exclusion`.
