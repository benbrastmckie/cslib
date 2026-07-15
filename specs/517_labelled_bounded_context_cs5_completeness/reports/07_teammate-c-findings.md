# Teammate C (Critic) — Task 517 Adversarial Audit

**Role**: identify gaps, unvalidated assumptions, blind spots. Attack research quality and
load-bearing assumptions. Every claim below was checked against the Lean source or the source
PDFs; prior reports/handoffs were treated as the object of audit, not as evidence.

**Reference grounding tier**: 1 (literature-backed). BibKeys verified against
`/home/benjamin/Projects/cslib/references.bib`: `Simpson1994` (`:86`), `Pacheco2024` (`:895`),
`MarinMoralesStrassburger2021` (`:962`). All three resolve.

**Headline**: the base rate holds. I found the predicted transcription error (A3's Pacheco
`∼c`), and two errors bigger than it. **The most dangerous item is not a transcription error at
all: `cs5_completeness` may be FALSE, the question that decides it is already mechanized to two
lines, and plan 02 explicitly dismisses that question as a "red herring."** Second most
dangerous: **the A3 NO-GO that closed Track B is not sound** — it upgrades an *open sub-problem*
into a *blocker*, contradicting CSLib's own task-509 verdict in the same file it cites.

---

## Key Findings

Ranked by danger. Each: (a) claimed, (b) what the evidence actually supports, (c) how to settle
decisively, (d) consequence if false.

---

### A1 — `cs5_completeness` ENTAILS `CS5 ⊢ FS`. The target may be FALSE, and the plan calls the deciding question a "red herring". [BLOCKING — settle before any other work]

**(a) Claimed.** plan 02 Phase 2 (`plans/02_decomposed-track-a-b-c.md:173`), verbatim:

> "The open syntactic `CS5 ⊢ FS` question is **orthogonal** to Track B and was a **red herring**
> for gating purposes."

**(b) What the evidence actually supports.** It is not orthogonal. It is *entailed by the target
theorem*, and therefore a **necessary condition** for it.

- `fs_sound''` (`probes/fischer-servi-probe.lean:132-144`) proves, sorry-free and axiom-clean:
  `CKValidFC.{u,v} cs5FC'' (((◇A).imp (□B)).imp (□(A.imp B)))` — i.e. `cs5FC'' ⊨ FS`.
- The target (plan 02 A3, `:190`) is `cs5_completeness : CKValidFC.{u,u} cs5FC'' φ → Derivable CS5ModalAxiom φ`.
- Instantiate at `φ := FS`. The hypothesis is discharged by `fs_sound''`. Therefore:

  ```
  cs5_completeness FS (fs_sound'' A B) : Derivable CS5ModalAxiom FS
  ```

  **`cs5_completeness ⟹ CS5 ⊢ FS`.** Contrapositive: **`CS5 ⊬ FS ⟹ cs5_completeness is FALSE.`**

And `CS5 ⊢ FS` is *open*. Plan 02 Phase 2's own outcome (`:130-136`): "Syntactic
`Derivable CS5ModalAxiom FS`: **left open, precisely diagnosed** (not proved, not refuted)."
`fs_context_relative_half` mechanizes the obstruction: the context-relative half succeeds, but
`DerivationTree.necessitation` requires an **empty**-context sub-derivation, so it cannot be
lifted to `□(A→B)`.

So Phase 2 proved the semantic half (`fs_sound''`) and left the syntactic half open — and then
Phase 3 concluded the open half was a red herring. **The two halves are the two sides of the
target theorem.** Proving `cs5FC'' ⊨ FS` did not de-risk Track B; it *created a necessary
condition* that nothing in Tracks A/B/C addresses.

Evidence that `CS5 ⊢ FS` is probably true, but not decisively:
- `Pacheco2024` Corollary 12 (`CKB ⊨ FS`) + Theorem 13 (`CKB ⊢ ϕ ⟺ CKB ⊨ ϕ`) would give
  `CKB ⊢ FS`, hence `CS5 ⊢ FS` (`CS5 ⊇ CKB`). **But CSLib itself records that Pacheco's
  Theorem 13 has a defect**: `CS5.lean:148-150`, verbatim — *"source of the pair-construction
  technique for the box-backward case (Lemma 18's skeleton only; **its primeness step, Lemma 16,
  is unsound as written**)"*. So the published route to `CKB ⊢ FS` is not currently reliable.
- Corroborating: `cs5_dia_or` (`CS5 ⊢ ◇(A∨B) → ◇A ∨ ◇B`, `k3`) — `CS5.lean:131`, "corroborating
  the `CS5 ≡ IS5` collapse"; and `ArisakaDasStrassburger2015` (`B ⊢ k3, k5`).

**(c) How to settle decisively.** Two dispatches, in this order, before anything else:
1. **Mechanize the reduction** (≈2 lines, given `fs_sound''` already exists). State
   `cs5_completeness` as a hypothesis and derive `Derivable CS5ModalAxiom FS` from it. This
   converts A1 from an argument into a landed theorem and makes the necessary condition
   undeniable. Cheap, certain, and it cannot fail.
2. **Decide `CS5 ⊢ FS`.** Either (i) derive it syntactically — the Pacheco/`k3` evidence says
   this is the likely outcome; or (ii) **build a `CS5`-countermodel for `FS`**: a model
   validating all 17 `CS5ModalAxiom` clauses and refuting `FS`. Note (ii) has never been
   attempted. Every dispatch has attacked (i) and failed; nobody has tried to refute it. Given
   the task's base rate, the untried direction is where the information is.

**(d) Consequence if false.** If `CS5 ⊬ FS`, then `cs5_completeness` **is false as stated**.
Not hard — *false*. Every track fails forever: Track A, Track B, Track C, the labelled
framework, Simpson, Pacheco, all of it. The ~789 landed lines are worthless *for completeness*
(they remain valid as a labelled-ND formalization). Tasks 509/512/517 all terminate, and the
correct action is `[BLOCKED]` with a restated target (e.g. completeness for `CS5 + FS`, or a
weakened `cs5FC'''` that does not validate `FS`).

**Honest probability**: `CS5 ⊢ FS` holds ≈ **70%**. So **≈30% the target theorem is false.**
That is not a tail risk — it is the single largest term in the task's failure probability, it is
cheap to settle, and the plan currently calls it a red herring. **This is the fourth wall.**

---

### A2 — The A3 NO-GO that closed Track B is NOT sound. It converts an open sub-problem into a blocker, contradicting CSLib's own verdict.

**(a) Claimed.** plan 02 `:149`: "**Verdict: NO-GO for Track B.** Do not open Phases 4-6."
Blocking obligation (`:200-207`): any canonical model over theory-inclusion-ordered worlds with
symmetric `r` and `r w u → boxInv(head w) ⊆ head u` "is provably forced into `cs5Tail`-shape by
`cs5Incest_forces_symm`, hence **cannot admit a box-refuting witness**, by
`cs5_symmetric_tail_box_gap`."

**(b) What the evidence actually supports.** I verified both cited theorems at source. Neither
supports the conclusion.

**`cs5Incest_forces_symm` (`CS5Canonical.lean:643-650`) — real, correct, and harmless here.**
Exact statement:

```lean
theorem cs5Incest_forces_symm
    {World : Type*} [Preorder World] (head : World → Set (Proposition Atom))
    (hmono : ∀ {w w' : World}, w ≤ w' → head w ⊆ head w')
    (r : World → World → Prop) (hbox : ∀ {w u : World}, r w u → boxInv (head w) ⊆ head u)
    (hincest : cs5Incest r) {w u : World} (hru : r w u) :
    boxInv (head u) ⊆ head w
```

Its conclusion is `boxInv (head u) ⊆ head w`. **That is not a contradiction — it is Pacheco's
second conjunct.** It says the box clause is two-sided. Pacheco *already proves this* (Lemma 15,
"`∼c` is a symmetric relation", chunk_0010:80). The theorem re-derives a fact the target
construction is designed to have. The name "forces_symm" invites reading it as a defeat; it is
not one. It is only weaponised in `cs5Incest_cs5PrimeMreach_false` **by combining it with `Ω`**
(`cs5PrimeMreach_ofHead_to_univ`, `CS5Canonical.lean:661`: `Set.univ` universally reachable) —
and **`Ω` is exactly what Pacheco's and Simpson's world types exclude by construction**
(A3's own text, `:186`: "CKB-theories are ∨-prime, MP-closed, **⊥-free**"; Simpson:
`TPrime.consistency`, `Context.lean:229-230`, whose docstring says verbatim "**This is what
banishes `Ω`**"). The `Ω` contradiction does not transport.

**`cs5_symmetric_tail_box_gap` (`CS5.lean:712-718`) — proves strictly less than A3 claims.**
Exact statement and proof:

```lean
theorem cs5_symmetric_tail_box_gap {H T : Set (Proposition Atom)}
    (hT : QuasiPrime (@CS5ModalAxiom Atom) T) {p q : Proposition Atom}
    (hbox : Proposition.box (p.or (Proposition.box q)) ∈ H)
    (hsub : boxInv H ⊆ T) (hsym : boxInv T ⊆ H) (hq : q ∉ H) : p ∈ T := by
  rcases hT.disj (hsub hbox) with h | h
  · exact h
  · exact absurd (hsym h) hq
```

It concludes `p ∈ T` **at a fixed `H`, under `hq : q ∉ H`**. The truth lemma's box clause is
`≤`-quantified: the box-backward witness is sought at a **larger** head `H' ⊇ H`. At any `H' ∋ q`,
**`hq` fails and the lemma yields nothing.** The wall does not bite at the place the witness is
actually sought.

**CSLib's own docstring says exactly this** — `CS5.lean:704-710`, verbatim:

> "The box-backward case must therefore move to a strictly larger head `H' ⊇ H` (here: one
> containing `q`), which enlarges `boxInv H'` in turn. That circularity is **the real open
> problem**: `H'` and `T` must be built as a **simultaneous maximal pair**, not sequentially."

And the task-509 status line, `CS5.lean:152-157`, verbatim:

> "This is **not** a library-level '`CS5` completeness is blocked' verdict — it is a narrow,
> well-understood, and non-vacuous **open sub-problem**."

**A3 cited this exact file and inverted its verdict.** "Open sub-problem requiring a simultaneous
maximal pair" became "cannot admit a box-refuting witness ⟹ NO-GO". The `CS5BoxGapWorld`
three-world countermodel (`CS5.lean:135-141`) establishes only that the wall *configuration* is
**reachable** (hypotheses jointly satisfiable) — it does **not** establish that the box-backward
case is unachievable. A3 read non-vacuity as impossibility.

And a simultaneous maximal pair is precisely what both candidate sources supply:
- **Pacheco** Lemmas 16-20 (Zorn theory-existence + Truth Lemma) — the very "pair-construction
  technique" `CS5.lean:148` credits him with.
- **Simpson** Lemma 5.3.1 (Prime lemma) — Zorn over **whole contexts**, graph and formula-set
  growing together (chunk_0102).

**Bonus — the predicted transcription error, found.** A3 `:181` states Pacheco's relation as
`Γ ∼c ∆ := Γ ⊆ ∆ ∧ ∆ ⊆ Γ♦`. `CS5.lean:583` states it as `Γ□ ⊆ ∆ ∧ ∆ ⊆ Γ♦`. **They contradict.**
Settled at source: Pacheco chunk_0010:60 literally reads `Γ ∼c ∆ iff Γ ⊆ ∆ and ∆ ⊆ Γ♦` — but that
reading **cannot be right**, because Pacheco proves `∼c` symmetric (chunk_0010:80) and
`Γ ⊆ ∆ ⟹ ∆ ⊆ Γ` is false. The `□` superscript is being **dropped by PDF text extraction**. The
correct reading is `Γ□ ⊆ ∆ ∧ ∆ ⊆ Γ♦`, which *is* symmetric via
`cs5_boxInv_subset_iff` (`boxInv T ⊆ H ↔ T ⊆ diaInv H`, `CS5.lean:589`). **A3 transcribed from
the lossy chunk text; `CS5.lean:583` (task 509) has it right.**

Consequence: A3's reasoning is wrong *twice over*. It invokes `T`+MP to manufacture
`boxInv Γ ⊆ Δ` from `Γ ⊆ Δ` — but with the correct definition `boxInv Γ ⊆ Δ` **is the first
conjunct**, needing no `T` and no CS5-extension. The `hbox` hypothesis holds for **CKB itself**,
unconditionally. A3's framing ("once `T` is present…") wrongly suggests the wall is contingent on
the T-extension. It isn't. *But the wall is not a wall*, so this makes no difference to the
verdict — which is wrong for the independent reason above.

**(c) How to settle decisively.**
1. Attempt to instantiate `cs5Incest_forces_symm` at Pacheco's world type
   (`Wc := {Γ | Γ a CKB-theory}`, `≼c = ⊆`). **It will succeed and produce no contradiction** —
   because `Ω ∉ Wc`. That is a ~20-line Lean check and it decisively refutes A3's blocking
   obligation.
2. Read `Pacheco2024` Lemmas 16-20 against `CS5.lean:148`'s claim that **Lemma 16 is unsound as
   written**. Given the `□`-dropping extraction defect proved above, **that unsoundness finding is
   itself under suspicion** — it was made against the same lossy text. Re-verify it against the
   PDF layout, not the chunks. If Lemma 16 is sound, Track B is open *and* settles A1.

**(d) Consequence if false** (i.e. if A3's NO-GO is wrong, as I believe): **the correct route was
discarded.** Track B (Pacheco Thm 13 / Simpson Thm 3.3.4) is both (i) not actually blocked, and
(ii) the only route that settles A1's necessary condition. Closing it left the task with no live
track to completeness — Track C is Chapter 6, which report 02 argues is unnecessary (see A4).
**The current state has zero live tracks, and nobody has noticed.**

**Honest probability that A3's NO-GO is wrong: ≈70%.**

---

### A3 — The task's stated load-bearing assumption ("labelled bounded contexts are NOT prime theories") is REFUTED. Twice. By the source and by the landed Lean.

**(a) Claimed.** That labelled bounded contexts are not prime theories and therefore escape
`cs5_symmetric_tail_box_gap`. Flagged in my brief as never verified against the source. It is now
verified: **it is false.**

**(b) What the evidence actually supports.**

- **Landed Lean refutes it.** `TPrime` (`Labelled/Context.lean:224-236`) has the disjunction
  property as a **defining clause**:
  ```lean
  /-- Clause 3: the disjunction property -- `x:A∨B ∈ Γ ⟹ x:A ∈ Γ ∨ x:B ∈ Γ`. -/
  disjunction : ∀ (x : Label Atom) (A B : Proposition Atom),
      (x ∶ Proposition.or A B) ∈ Γ → (x ∶ A) ∈ Γ ∨ (x ∶ B) ∈ Γ
  ```
  The structure is *named* `TPrime`. It is prime.
- **Simpson refutes it.** Chapter 8 §8.2 calls its worlds "**𝒯-prime bounded contexts**"
  (chunk_0166, Lemma 8.2.5/8.2.6). chunk_0172, verbatim: "Consistency and **the disjunction
  property** are shown (more easily) by similar arguments." Bounded contexts are prime.
- **And `cs5_symmetric_tail_box_gap` consumes exactly primality**: its proof uses `hT` only via
  `hT.disj`. So the claimed escape route is the one route that is definitively closed.

**The real escape is different, and it matters that the team knows which one it is.** Per A2: the
box clause is `≤`-quantified; the witness is found at a larger context `H' ∋ q` where `hq` fails;
and `H'` and the witness are built as a **simultaneous maximal pair** by Simpson's Prime Lemma
5.3.1 (Zorn over *whole contexts*, chunk_0102) — which is *precisely* what `CS5.lean:707` names
as "the real open problem". **Simpson's Lemma 5.3.1 is the solution to CSLib's stated open
problem.** That is the actual value of the labelled route, and it is not what the task believes
it is buying.

**(c) How to settle decisively.** Already settled — `Context.lean:231-233` and Simpson
chunk_0172 are both explicit. No further work needed. **Correct the rationale in the plan and in
`Context.lean`'s module docstring before anyone designs against the false version.**

**(d) Consequence if false** (it is false): **a team that believes "not prime" is the escape will
design toward weakening primality — which breaks the `∨` case of the truth lemma and buys
nothing.** The task is *not* dead (the real escape holds), but the stated reason is wrong, and
the wrong reason points at a route that provably cannot work. This is a live steering hazard, not
a fatal one.

---

### A4 — Report 02's central finding ("Ch.6 is NOT on the critical path, ~85%") is REFUTED by Simpson's own text.

**(a) Claimed.** report 02 `:22-25`: "The adequacy bridge (Lemma 6.1.2) is almost certainly NOT
on the critical path to `cs5_completeness`… **Chapter 6 answers a *different* question. The plan
routed `cs5_completeness` through Chapter 6 unnecessarily.**" Confidence `:423`: **~85%**.

**(b) What the evidence actually supports.** Simpson says the opposite, twice, verbatim:

- **chunk_0075 (Chapter 3)**: "It will follow from the results of **Chapters 5 and 6** that all
  the intuitionistic modal logics `IKS₁…Sₙ` of Theorem 3.3.4 satisfy meta-logical completeness."
- **chunk_0121 (Chapter 6)**: "**By Theorem 5.2.1, for any 𝒯 to which Theorem 6.2.1 applies, we
  have a complete axiomatization** of the modal formulae valid in any `I𝒯`-model."

The architecture is: **Thm 5.2.1** (Ch.5) gives completeness of the *labelled* system
`N_□◇(𝒯)` w.r.t. `I𝒯`-models. **Thm 6.2.1** (Ch.6) is the bridge `N_□◇(𝒯) ⊢ A ⟺ IK+Ax(𝒯) ⊢ A`.
`cs5_completeness`'s conclusion is `Derivable CS5ModalAxiom φ` — **the axiomatic side**. Chapter 5
alone lands you in the labelled system. **Chapter 6 is the only thing that gets you to the
axioms.** It is on the critical path by construction.

Report 02 correctly observed that Thm 6.2.1 "answers a different question" *in isolation*. It
does — and that different question is exactly the one standing between Ch.5's output and the
target's conclusion.

Report 02's alternative ("Simpson proves IS5 completeness directly, Thm 3.3.4, p.56") is **Track
B** — which A3 closed (see A2). So report 02 and plan 02 jointly deleted **both** routes: report
02 argued away Ch.6, A3 argued away Thm 3.3.4.

**Corrected chapter map** (verified by reading chunk headers):

| Ch. | Title | Role for `cs5_completeness` |
|---|---|---|
| 3 | Intuitionistic… | Thm 3.3.4 — IS5 ≡ Fischer-Servi birelational; **Track B's route** |
| 5 | Meta-logical… | §5.3 Prime Lemma 5.3.1 + Canonical Model Lemma 5.3.2, **unbounded**; → `I𝒯`-models |
| 6 | Axiomatization | **Thm 6.2.1**: `N_□◇(𝒯) ≡ IK+Ax(𝒯)` — **required**, contra report 02 |
| 8 | Birelational… | §8.2 **𝒯-prime BOUNDED contexts**, `𝒯-Comp`, bounded canonical model (8.2.5/8.2.6) |

**Note**: "labelled **bounded** context" — the task's own name — is **Chapter 8**, not Chapter 6.
Nobody is working on Chapter 8.

**(c) How to settle decisively.** Read `Simpson1994` chunk_0075 and chunk_0121 (both quoted
above, both unambiguous prose — not affected by the OCR/symbol defect, which the index warns is
limited to math symbols). Then re-derive the full bridge chain for the target and check each link
has an owner:
```
cs5FC'' ⊨ φ  →[Fischer Servi / Ch.8]→  I𝒯_S5 ⊨ φ  →[Thm 5.2.1, Ch.5]→  N_□◇(𝒯_S5) ⊢ φ
             →[Thm 6.2.1, Ch.6]→  IK+Ax(𝒯_S5) ⊢ φ  →[CS5 ≡ IS5 — see A1]→  CS5 ⊢ φ
```
**Four bridges. Currently: bridge 1 unowned, bridge 2 partially scaffolded (789 lines), bridge 3
argued-away by report 02, bridge 4 is A1 and is called a red herring.**

**(d) Consequence if false** (i.e. if report 02 is wrong, as the source says): Track C is *not*
deletable, report 02's headline recommendation (`:445`, "the adequacy bridge is not worth the
remaining cost") would have deleted a required bridge, and the ~85% is not just wrong but
inverted. **Do not act on report 02's recommendation to drop Track C.**

---

### A5 — `GeomWitnessClosure := True` is a load-bearing stub. Simpson's Lemma 5.3.1 cites it at the decisive step.

**(a) Claimed.** `Labelled/Context.lean:138`:
```lean
def GeomWitnessClosure (𝒯 : Set GeomAxiom) (G : Graph Atom) : Prop := True
```
with docstring "holds for every graph (see its docstring: **vacuous under the present `Label`
type**)" and `geomWitnessClosure_holds ... := trivial`. Wired in as `Context`'s clause 3.

**(b) What the evidence actually supports.** Simpson's requirement 3 on contexts (chunk_0101) is
**substantive**:

> "3. For each basic geometric sequent `Υ ∈ 𝒯`, each of the witness variables in `v̄_i` is in `G`
> only if the others are and, for some `i` (1 ≤ i ≤ m), the relations
> `R_{i1}[z̄/x̄][v̄_i/ȳ], …, R_{in_i}[z̄/x̄][v̄_i/ȳ]` all hold in `G`."

And Lemma 5.3.1's proof **explicitly consumes it** to establish the classical-model clause
(chunk_0102, final sentence, verbatim):

> "So, as the variables in `v̄_i` are in `H`, it follows, **from requirement 3 on contexts**, that,
> for some `i`, the relations … all hold in `H`."

For `𝒯_S5 = {T, 5}` both axioms are **quantifier-free** (reflexivity `⊢ xRx`; Euclideanness
`xRy, xRz ⊢ yRz`), so the witness vector `v̄_Υ` is **empty**. With `v̄_Υ` empty the antecedent
"the variables in `v̄_i` are in `G`" is vacuously *true*, so requirement 3 **asserts its
consequent outright**: the relations hold in `G` — i.e. **`G` is closed under reflexivity and
Euclideanness**. That is the strongest possible reading, not a vacuous one. And it is exactly the
step that discharges `TPrime.clModel`.

The docstring's justification is also wrong on its own terms: the vacuity has **nothing to do
with the `Label` type**. Requirement 3 for quantifier-free axioms is a constraint on the *graph's
edge set*, not on labels.

**Fair caveat**: Simpson's contradiction-branch (maximality + rule `(R_Υ)`, giving `H_i = H`)
*might* independently yield graph closure for quantifier-free `𝒯`, making requirement 3
genuinely redundant for `𝒯_S5`. That is plausible but (i) is **not** what Simpson does, (ii) is
**not** what's landed, and (iii) has never been checked. Confidence this is a real defect: **~70%**.

**(c) How to settle decisively.** Attempt Phase 5 (Prime Lemma 5.3.1) against the landed
`Context`. The step establishing `TPrime.clModel` will either (i) go through via maximality +
`(R_Υ)` alone — in which case *prove that* and replace the docstring's false "vacuous under the
present `Label` type" with the real reason; or (ii) get stuck — in which case implement
requirement 3 properly. **Either way this must be resolved before Phase 5 is dispatched**, because
Phase 5 is the crux (per A3) and this is its first obstacle.

**(d) Consequence if false** (i.e. if the stub is load-bearing): **Lemma 5.3.1 is unprovable as
landed.** `TPrime.clModel` is a *field* — a hypothesis that the Prime Lemma must discharge — and
the only route Simpson gives runs through requirement 3. With it `= True`, the Zorn maximal
element's graph need not be reflexive or Euclidean, and `TS5`-classical-modelhood cannot be
concluded. The crux phase fails at its first step. Cost: one wasted dispatch, plus a silent
`True` in `Cslib/` that no CI gate catches (it is not a `sorry`).

---

### A6 — `Context.lean`'s "unbounded" rationale is backwards. It rejects the exact mechanism the task is named after.

**(a) Claimed.** `Context.lean` (order docstring, ~`:172`), verbatim:

> "It is deliberately a plain, **unbounded** inclusion order — no fixed head, no bound on `G` or
> `Γ` — … **bounding this order here would re-impose exactly the hypothesis that makes
> `cs5_symmetric_tail_box_gap` fatal and re-enter task 512's wall.**"

And `:35`: "`Context` and `TPrime` place **no bound** on `Γ`."

**(b) What the evidence actually supports.** The stated causal claim is inverted. Per Simpson
Ch.8 §8.2, **boundedness is a mechanism that *defeats* the gap, not one that imposes it**:

- Lemma 8.2.6 (Bounded canonical model lemma, chunk_0166) is **depth-indexed**: "Let `(H,Δ)` be
  any 𝒯-prime bounded context. If `y` has depth `n` in `H` and `B ∈ Θ_{d-n}` then
  `(H,Δ),y ⊩_K B` if and only if `y:B ∈ Δ`."
- The depth budget `Θ_{d-n}` caps how deep a nested-box chain can reach at a given label. The gap
  lemma's configuration needs `□(p∨□q)` at depth `n`, hence `p∨□q` at `n+1`, `□q` at `n+1`,
  `q` at `n+2` — **the bound is exactly what limits this chain.**
- And the relation is `R_{(H,Δ)}(x,y) iff xRy in 𝒯-Comp(H)` (chunk_0166) — the **𝒯-completion of
  the graph**, *not* a box-inverse containment. `boxInv T ⊆ H` (the `hsym` clause) is therefore
  *derived and depth-limited*, not definitional. That is the structural difference from
  `cs5Tail`.

So `Context.lean` cites `cs5_symmetric_tail_box_gap` as the *reason to avoid* the bound, while
Simpson uses the bound as *part of the escape*. **The docstring is not merely imprecise; it
argues against the method in the task's title.**

**Fair caveat**: the landed unbounded Ch.5 design is **not thereby wrong**. Ch.5 §5.3 (unbounded)
and Ch.8 §8.2 (bounded) are two distinct, both-valid Simpson routes; Ch.5 → `I𝒯`-models, Ch.8 →
birelational + finite model property. The unbounded route escapes the gap via
simultaneous-Zorn + fresh labels (A3). The defect is the **stated reason**, and the fact that the
target (`cs5FC''`) is *birelational* — which is Ch.8's chapter, not Ch.5's.

**(c) How to settle decisively.** Decide explicitly which Simpson route the task is on, and write
it down: Ch.5-unbounded (→ `I𝒯`-models, needs a separate Ch.8/Fischer-Servi bridge to `cs5FC''`)
or Ch.8-bounded (→ birelational directly). **The landed code is Ch.5; the task name and the target
frame class are Ch.8.** Then fix the docstring's causal claim either way.

**(d) Consequence if false**: a future dispatch reads the docstring, treats "bounded" as the
known-fatal direction, and never opens Ch.8 §8.2 — the one chapter whose canonical model is
already birelational and therefore closest to `cs5FC''`. Steering hazard, low direct cost, high
opportunity cost.

---

### A7 — C5 cannot be countermodel-checked: it does not exist. There is no statement to check.

**(a) Claimed (in my brief).** "C5's commutation lemma (`pathSpine` + `addChild`/`pathSpine`
commutation): is it TRUE as stated? Countermodel-check BEFORE anyone endorses it."

**(b) What the evidence actually supports.** **There is nothing to check.** `pathSpine` occurs
exactly **3 times in the entire repository**, all forward references, none a definition:
- `probes/lemma612-scaffold.lean:364` — "the whole-path recursion (`pathSpine`) with pruning"
- `probes/lemma612-scaffold.lean:375` — "forward-compatible with C5's `addChild`/`pathSpine` commutation lemma"
- `probes/lemma612-scaffold.lean:760` — "correct path-level recursion (with pruning built in) is `pathSpine`, **explicitly deferred to C5**"

Zero occurrences under `Cslib/`. Plan 02 Phase 11 (`:343-348`) is `[NOT STARTED]` and its first
task is "**Define** `pathSpine`". **The lemma has no statement, so it has no truth value yet, and
"is it true as stated?" has no answer.** I decline to fabricate an analysis of a nonexistent
lemma — doing so is precisely the analysis-theatre this task keeps producing.

What I *can* say: the prior on a C5 transcription defect is **not** low — C2 (`V=[]`, refuted by a
3-world countermodel) and C4 (`star`, a defective double-`bigAnd`) were both found false as
literally stated, and report 02 `:426` records "**Four dispatches, five corrections, each found by
the next.**" But that is a prior on a future artifact, not a finding about a current one.

**(c) How to settle decisively.** Do **not** dispatch C5 yet. When and if it is dispatched, the
dispatch must produce the *statement first*, in isolation, with a small-model check (trees of
depth ≤ 3) **before** any proof attempt. Given the base rate, statement-first + countermodel-first
is the only discipline that has been catching these.

**(d) Consequence.** Low, *conditional on the routing question*. Per A4, Track C (Ch.6) **is**
required — so C5 is probably not deletable, contra report 02. But it is also **not urgent**: A1
and A2 both outrank it, and both can invalidate the entire track. **Dispatching C5 before A1 is
settled risks spending a HIGH-risk dispatch on a theorem whose target may be false.**

---

### A8 — The confidence numbers are not honest.

**(a) Claimed.** plan 02 `:426` / report 02: "**Track C (full adequacy bridge) completes in 2-3
dispatches — ~25-30%.**" Plan 02 header `:5`: "C5-C8 + assembly remaining (~4-6 dispatches, HIGH
uncertainty)."

**(b) What the evidence actually supports.** The estimate has already been falsified by the
record it cites. Four dispatches (C1-C4) are spent; the crux (C5) is still ahead and **has no
statement** (A7). Report 02's own basis for the number, `:426`, verbatim: "Four dispatches, five
corrections, each found by the next. **No mechanization of this argument exists anywhere. Source
is deliberately informal and omits two cases.**"

That is a description of a process with a **~100% per-dispatch defect rate** on transcription. A
chain of 4-6 further dispatches at that rate, each depending on the last, does not complete at
25-30%. If each dispatch has even a 70% chance of landing correctly *and being correct in the next
audit*, four in a row is 0.7⁴ ≈ 24% — and the observed rate is worse than 70%. **Honest: ~10%,
and that is conditional on the target being true (A1, ~70%) and on Track C being the right track
(A4).** Compounded: **≈7%** that the current plan reaches `cs5_completeness` as scoped.

The 85% figures in report 02 `:422-423` deserve the same scrutiny: `:423` ("Lemma 6.1.2 is not
required for `cs5_completeness` — ~85%") is **refuted outright** by A4. A stated 85% that is
actually ~15% is not a calibration miss; it is evidence the confidence numbers are being produced
by argument rather than by evidence.

**(c) How to settle decisively.** Re-baseline after A1 and A2 are settled, and stop reporting
per-track completion probabilities that are not conditioned on the target being true.

**(d) Consequence.** Optimistic numbers on a task with three prior walls are how a fourth wall
gets funded.

---

## Recommended Approach

**Stop. Do not dispatch C5. The current plan has no live track to completeness and does not know
it.**

Ordered, each gated on the previous:

1. **[A1 — BLOCKING, ~1 dispatch, cannot fail] Mechanize `cs5_completeness ⟹ CS5 ⊢ FS`.**
   Two lines given `fs_sound''`. This makes the necessary condition undeniable and is the
   cheapest high-information act available.
2. **[A1 — BLOCKING, ~1-2 dispatches] Decide `CS5 ⊢ FS`.** Prioritise the **untried** direction:
   build a `CS5`-countermodel refuting `FS`. If found → **target is FALSE → `[BLOCKED]`, restate
   the target, terminate 509/512/517 as scoped.** If `FS` is derived instead → A1 clears and the
   task is alive.
3. **[A2 — ~1 dispatch] Re-open the Track B verdict.** Instantiate `cs5Incest_forces_symm` at
   Pacheco's `Wc` (`Ω`-free) and confirm no contradiction results. Re-verify `CS5.lean:148`'s
   "Lemma 16 is unsound as written" **against the PDF layout, not the chunks** — that finding was
   made against the same lossy text that dropped the `□` from `∼c` (A2).
4. **[A4 — paper, ~0.5 dispatch] Fix the bridge chain.** Reinstate Ch.6 as required. Assign an
   owner to each of the four bridges. Any bridge without an owner is the task's real status.
5. **[A5 — before Phase 5] Resolve `GeomWitnessClosure`.** Prove the maximality+`(R_Υ)` route
   discharges `clModel` for quantifier-free `𝒯_S5`, or implement requirement 3.
6. **[A3/A6 — paper, cheap] Correct the rationales** in plan 02 and `Context.lean`'s module
   docstring. The escape is the `≤`-quantified box clause + simultaneous maximal pair — **not**
   non-primality.
7. **Only then** consider C5.

**Process finding (systemic, explains the base rate).** The literature index records, verbatim:
*"OCR ceiling: mathematical symbols (turnstiles, Gamma/Delta, set membership) are frequently
misrecognized … and unreliable for exact notation; prose and structural content … are reliable."*
I proved the same class of defect in the **Pacheco** chunks (a modern PDF, not OCR): the `□`
superscript in `Γ□` is silently dropped (A2). **Every transcription defect this task has produced
is consistent with agents reading formulae out of chunk text.** Standing rule going forward:
**chunk text is admissible for prose and structure; every formula must be read from the PDF
layout or reconstructed from a stated property** (as I reconstructed `Γ□ ⊆ ∆` from Pacheco's own
symmetry lemma). This single rule would have prevented C2, C4, and A3's error.

---

## Blocking Obligations

| # | Obligation | Blocks | Cost |
|---|---|---|---|
| **B1** | Decide `CS5 ⊢ FS`. `cs5_completeness ⟹ CS5 ⊢ FS` via `fs_sound''`. If underivable, **the target is false**. | **Everything.** | 1-2 dispatches |
| **B2** | Re-verify A3's NO-GO by instantiating `cs5Incest_forces_symm` at an `Ω`-free world type. Neither cited theorem is a contradiction there. | Track B; the existence of any live track | ~1 dispatch |
| **B3** | Re-verify `CS5.lean:148`'s "Pacheco Lemma 16 unsound" against PDF layout, not chunks. | B1 (via Pacheco Thm 13), B2 | ~0.5 dispatch |
| **B4** | Assign an owner to each of the four bridges (A4). Unowned bridge = task status. | Phase 15 assembly | paper |
| **B5** | Resolve `GeomWitnessClosure := True` before Phase 5 is dispatched. | Prime Lemma 5.3.1 (the crux) | ~0.5 dispatch |

---

## Evidence-Examples

**Lean (verified by reading source at the cited lines):**
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean:643-650` — `cs5Incest_forces_symm`;
  concludes `boxInv (head u) ⊆ head w`, **not** a contradiction. Proof
  `fun B hB => hbox hru'w (hmono hle hB)` typechecks by definitional unfolding of
  `boxInv S = {A | box A ∈ S}`.
- `CS5Canonical.lean:487-488` — `cs5TwoSidedR Γ Δ := boxInv Γ ⊆ Δ ∧ Δ ⊆ diaInv Γ`. **First
  conjunct is `boxInv Γ ⊆ Δ`, not `Γ ⊆ Δ`** — refutes plan 02 `:181`.
- `CS5Canonical.lean:511-519` — `cs5TwoSidedR_iff_cs5Tail`; A3's conclusion was already mechanized.
- `CS5Canonical.lean:661` — `cs5PrimeMreach_ofHead_to_univ`; the `Ω` step the wall depends on.
- `Cslib/.../CS5.lean:712-718` — `cs5_symmetric_tail_box_gap`; uses `hT` **only** via `hT.disj`;
  concludes at **fixed `H`** under `hq : q ∉ H`.
- `CS5.lean:704-710` — "**the real open problem**… simultaneous maximal pair, not sequentially."
- `CS5.lean:152-157` — "**not** a library-level 'CS5 completeness is blocked' verdict… **open
  sub-problem**." Contradicts A3's NO-GO.
- `CS5.lean:148-150` — "Pacheco… **its primeness step, Lemma 16, is unsound as written**."
- `CS5.lean:583-589` — `cs5_boxInv_subset_iff`; Pacheco's `∼c` as `Γ□ ⊆ ∆ ∧ ∆ ⊆ Γ♦`.
- `Cslib/.../CKExtension.lean:184-189` — `cs5FC''`: reflexivity + transitivity + **plain
  symmetry** + two `≤`-composed clauses (F1/F2-shaped).
- `Cslib/.../Labelled/Context.lean:224-236` — `TPrime`, clause 3 `disjunction` — **refutes "not
  prime"**.
- `Labelled/Context.lean:138` + `:140-144` — `GeomWitnessClosure := True`, `:= trivial`.
- `Labelled/Context.lean:~172`, `:35` — the inverted "unbounded" rationale.
- `probes/fischer-servi-probe.lean:132-144` — `fs_sound''`, sorry-free, axiom-clean.
- **`pathSpine`: 3 occurrences repo-wide, all forward references, zero definitions.**

**Literature (BibKeys verified in `references.bib`):**
- `[Simpson1994]` chunk_0075 (Ch.3) — "It will follow from the results of **Chapters 5 and 6**…"
  → **refutes report 02 `:423`.**
- `[Simpson1994]` chunk_0121 (Ch.6) — "**By Theorem 5.2.1, for any 𝒯 to which Theorem 6.2.1
  applies, we have a complete axiomatization**…"
- `[Simpson1994]` chunk_0101 — Context requirements 1-3; **requirement 3 is substantive**;
  𝒯-prime clauses 1-4.
- `[Simpson1994]` chunk_0102 — **Lemma 5.3.1 (Prime lemma)**, Zorn over whole contexts; cites
  requirement 3 at the `clModel` step.
- `[Simpson1994]` chunk_0103 — Lemma 5.3.2 (Canonical model lemma); canonical model `K^𝒯`.
- `[Simpson1994]` chunk_0166 (Ch.8 §8.2) — Lemma 8.2.5, **8.2.6 bounded canonical model lemma**,
  depth-indexed `Θ_{d-n}`, `R := 𝒯-Comp(H)`.
- `[Simpson1994]` chunk_0172 (Ch.8) — "**Consistency and the disjunction property** are shown…"
  → **𝒯-prime bounded contexts ARE prime.**
- `[Simpson1994]` chunk_0068 — Thm 3.3.4; "The cases IK, IT, IKTB, IS4 and **IS5** … appear
  explicitly in Fischer Servi."
- `[Pacheco2024]` chunk_0010:60 — `Γ ∼c ∆ iff Γ ⊆ ∆ and ∆ ⊆ Γ♦` **as extracted**; chunk_0010:80 —
  "`∼c` is a symmetric relation" → **proves the `□` is dropped by extraction.**
- `[Pacheco2024]` chunk_0011:21-24 — `∼c` backward confluent.
- Literature index (`simpson_1994_intuitionisticmodallogic`) — "**OCR ceiling: mathematical
  symbols … unreliable for exact notation**."

---

## Confidence Level

**Overall: HIGH** — every finding is grounded in a directly-quoted line of Lean source or source
PDF text, not in prior reports.

| Finding | Confidence | Basis |
|---|---|---|
| **A1** `cs5_completeness ⟹ CS5 ⊢ FS`; "red herring" is wrong | **HIGH (~95%)** | Direct instantiation of the target at `fs_sound''`. Mechanically checkable in 2 lines. |
| A1 corollary: `CS5 ⊢ FS` holds | **MEDIUM (~70%)** | Pacheco Cor.12+Thm 13 and `cs5_dia_or`/`k3` support it; Thm 13's Lemma 16 is flagged unsound; syntactic search failed with a mechanized obstruction. **⟹ ~30% the target is FALSE.** |
| **A2** A3's NO-GO is unsound | **MEDIUM-HIGH (~70%)** | Both cited theorems read at source; neither yields a contradiction off `Ω`. `CS5.lean:152-157` states the opposite verdict in the file A3 cites. |
| A2 corollary: A3 mis-transcribed Pacheco's `∼c` | **HIGH (~90%)** | Two CSLib artifacts contradict; settled by Pacheco's own symmetry lemma + `cs5_boxInv_subset_iff`. |
| **A3** "not prime" is refuted | **HIGH (~97%)** | `TPrime.disjunction` (`Context.lean:231-233`) and Simpson chunk_0172, both explicit. |
| **A4** Ch.6 IS on the critical path | **HIGH (~90%)** | Two verbatim Simpson quotes (chunk_0075, chunk_0121), both prose — outside the OCR defect zone. |
| **A5** `GeomWitnessClosure` is a load-bearing stub | **MEDIUM (~70%)** | Simpson cites requirement 3 at the decisive step; the maximality+`(R_Υ)` alternative is plausible but unattempted and unlanded. |
| **A6** "unbounded" rationale is backwards | **MEDIUM-HIGH (~80%)** | Ch.8 §8.2 uses the bound as part of the escape. The landed Ch.5 design is defensible; the *stated reason* is not. |
| **A7** C5 has no statement | **HIGH (~99%)** | 3 grep hits, all forward references. |
| **A8** Plan reaches `cs5_completeness` as scoped | **~7%** | 0.7 (A1) × ~0.10 (Track C at observed defect rate). Plan claims 25-30% unconditionally. |

**What I could not settle**: whether `CS5 ⊢ FS` is actually derivable (A1's crux — needs a
dispatch, and the untried countermodel direction); whether Pacheco's Lemma 16 is genuinely unsound
or was mis-transcribed like his `∼c` (A2/B3); whether the maximality+`(R_Υ)` route discharges
`clModel` without requirement 3 (A5).

**The one thing I am most confident about**: A1 is cheap, decisive, currently dismissed, and
outranks everything else in the plan. **If the team does exactly one thing from this report, do
A1.**
