# Phase 20 Pre-Gate: does `TClosure` support the `(R_Υ)` internalization?

- **Task**: 517 — labelled bounded context, CS5 completeness
- **Phase**: 20 (pre-gate before the HIGH-cost Phase 21)
- **Session**: sess_1784156551_995e9d
- **Status**: COMPLETED — one dispatch, within cap
- **Probe**: `specs/517_labelled_bounded_context_cs5_completeness/probes/rchi-internalization-gate.lean`
  (sorry-free; `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`)
- **Reference grounding tier**: **Tier 1** (literature-backed) — [Simpson1994], BibKey verified at
  `references.bib:86`
- **Territory**: `probes/` + `reports/` only. **`Cslib/` untouched** (`git status` confirms).

---

## VERDICT (lead)

**`TClosure` DOES support the `(R_Υ)` internalization. The falsifier did NOT fire. Leg A's first
real obstacle is CLEARED, mechanized, sorry-free.**

Three secondary verdicts, all grounded in PDF layout:

| Question | Verdict |
|---|---|
| Does `TClosure` admit `(R_Υ)` for each `𝒯 = TS5 = {T,B,Four}` axiom? | **YES** — mechanized, 3/3 |
| Does `clModel`'s discharge depend on **requirement 3** for the quantifier-free axioms? | **NO** — requirement 3 is *vacuous* when `ȳ` is empty. **Conflict 7's adjudication CONFIRMED; Phase 18's deletion is compatible.** |
| Is leg A clear? | **Phase 21 (at `𝒯 = ∅`): YES, clear.** **Phase 23 (at `𝒯 = TS5`): NO — a NEW, separate blocker found.** |

**The new blocker (not anticipated by plan v3): `TPrime TS5 Atom` is UNINHABITED as currently
typed.** `clModel`, `Graph.edge_mem`, and `Context.coinfinite` are jointly contradictory. This is
mechanized: `tPrime_TS5_false`. It is a **statement-level transcription defect, and it is
repairable** — it does not block Phase 21, and it does not falsify the route.

---

## 1. The OCR defect: resolved from PDF layout

`chunk_0102.md:11` ends *"Suppose, for contradiction, that the variables in v,_ are not in H.
**Define:**"* and line 12 is blank. I confirmed the `pdftotext -layout` text layer drops it too —
so this is not a chunking artifact but a **text-layer** loss; only the page raster carries it.

**Recovered from PDF page raster, p. 92** (PDF page 101):

```
H_i  =  H ∪ {v | v ∈ v_χz̄} ∪ {R_i1[z̄/x̄][v_χz̄/ȳ], ..., R_in_i[z̄/x̄][v_χz̄/ȳ]}.
```

`H_i` adds **two** things: the **witness variables** `v_χz̄`, and the **conclusion relations** of
disjunct `i`. The plan's quoted mechanism (`H₁ = H ∪ {R₁₁[z̄/x̄]}`) is the **correct
specialization** to a quantifier-free axiom, where `v_χz̄` is empty — but the plan's quote omits
the witness-variable component, which is precisely the component that carries the requirement-3
question. **The plan's quote is right about `TS5` and would be wrong if generalized.**

**Normal form** ([Simpson1994] p. 72, PDF p. 81, verbatim):

```
∀x̄. ((R_1 ∧ ... ∧ R_n) ⊃ ∃ȳ. ⋁_{i=1}^{m} (R_i1 ∧ ... ∧ R_in_i)),   where m, n ≥ 0, n_i ≥ 1
```

`T`, `B`, `Four` each have **`ȳ` empty** and `m = 1`, `n_1 = 1` (`n` = 0, 1, 2 respectively). So
`v_χz̄`, a vector "of the same length as `ȳ`" (p. 91), is the **empty vector** for all of `TS5`.

---

## 2. MUST-RESOLVE: the requirement-3 verdict → **NO, not load-bearing for `{T,B,Four}`**

**Requirement 3, verbatim** ([Simpson1994] p. 91, PDF p. 100):

> 3. For each basic geometric sequent `χ ∈ 𝒯` (in the form on page 72), **each of the witness
>    variables in `v_χz̄` is in `G` only if** the others are and, for some `i` (`1 ≤ i ≤ m`), the
>    relations `R_i1[z̄/x̄][v_χz̄/ȳ], ..., R_in_i[z̄/x̄][v_χz̄/ȳ]` all hold in `G`.

Requirement 3 is an **"only if"** conditional whose subject is *"each of the witness variables in
`v_χz̄`"*. For a quantifier-free axiom `v_χz̄` is empty, so **the conditional has no instances and
requirement 3 is vacuously true.**

**This settles the conflict. `GeomWitnessClosure := True` was not a stub — for `𝒯 = TS5` it was
`True`, correctly.** Deleting a vacuously-true field is semantically inert. **Phase 18's deletion
removed nothing leg A needs.** Conflict 7's adjudication is confirmed — and confirmed for a
*sharper reason* than the plan gave: not "requirement 3 justifies witness variables which `TS5`
lacks" as a motivating gloss, but the literal vacuity of its quantifier at `ȳ = ∅`.

### Why the chunk's "requirement 3" citation is real but not load-bearing

The chunk text is right that p. 93 cites requirement 3 by name. Reading p. 92-93's argument as a
whole shows why, and why it does not bind `TS5`. Simpson's proof of `H ⊨_CL χ` splits by whether
the witnesses are present:

| Case | Instrument | Why |
|---|---|---|
| Witnesses **absent** from `H` | reductio + maximality + `(R_χ)` | `H_i ⊋ H`, so maximality bites → `H_i = H` → contradiction |
| Witnesses **present** in `H` | **requirement 3** | `H_i = H` already, so maximality yields *nothing*; requirement 3 covers exactly this blind spot |

The two cases are complementary, and requirement 3 exists **solely** to cover the case maximality
cannot see. For a quantifier-free `χ` the witnesses are vacuously present, so the printed route
lands in the second case — where requirement 3 is vacuous.

### The consequence Phase 21/23 must know: Simpson's printed exit degenerates at `TS5`

Taken **literally** at a quantifier-free `χ`, *both* printed steps are content-free:

- the reductio hypothesis *"the variables in `v_χz̄` are not in `H`"* is **vacuously false** (empty
  vector), so the reductio proves nothing; and
- the exit *"from requirement 3 on contexts, ... the relations all hold in `H`"* is **vacuous**.

**Yet the goal is still delivered — by the maximality step itself, used directly:** for some `i`,
`Δ ⊬_{H_i} x:A`, hence `(H_i,Δ) ∈ C`, hence by maximality `H_i = H`, hence
`R_i1[z̄/x̄] ∈ H` — *which is exactly the goal*. The plan's reading (**"`H₁ = H` means
`R₁₁[z̄/x̄] ∈ H` — which is exactly the goal"**) is **CONFIRMED as the correct mechanization
route.**

Simpson routes `H_i = H` into a contradiction rather than using it directly because in the
**existential** case the conclusion must be about *"a vector of variables in `H`"*, which the
reductio is what establishes. His presentation is uniform over both cases and simply does not
specialize. **Phase 21/23 must take the direct route and must NOT transcribe p. 92-93's reductio
framing literally at `TS5` — it degenerates into two vacuous steps.** A literal-transcription
agent will get stuck here and may wrongly conclude the argument is broken. It is not; it is
under-specialized.

---

## 3. The mission: `TClosure` admits `(R_Υ)` — mechanized

### Why it works

`(□E)` and `(◇I)` are, by inspection, the **only** `NIK` rules with a relational premise
(`Deduction.lean:237-256`), and both range over `TClosure 𝒯 G.R`, not `G.R`. **`NIK` never
consults `G.X` at all.** So derivability depends on the graph *only* through its `𝒯`-closure, and
`(R_χ)` — Simpson's *"`Δ ⊢_H x:A` would be derivable by an application of `(R_χ)`"* — reduces to
one absorption fact:

> adding an edge the closure already derives does not change the closure.

This is `TClosure`'s stated design intent, recorded verbatim in `GeomAxiom`'s docstring
(`Deduction.lean:117-126`): every constructor is universal Horn, which *"lets `TClosure` realize
`(R_χ)` for **every** `χ` in this type by a pure relational closure"*. **The pre-gate confirms
that docstring is accurate, not aspirational.**

### What was landed (all sorry-free, `[propext]` only)

| Declaration | Content |
|---|---|
| `TClosure.absorb_addEdge` | `TClosure 𝒯 G.R c₁ c₂ → TClosure 𝒯 (G.addEdge c₁ c₂).R ≤ TClosure 𝒯 G.R` — the core |
| `ClLe` / `ClLe.addEdge` | closure-level graph order + its `addEdge` congruence |
| `NIK.weakenCl` | **closure-level weakening**: `NIK` is monotone in the `𝒯`-*closure*, not merely in `Graph.le`. Strictly stronger than `NIK.weaken`, and exactly where 5.3.1 needs it — the graph may *shrink* as a raw edge set provided its closure does not |
| `NIK.geomInternalize` | **`(R_χ)` in full generality** for a quantifier-free axiom |
| `NIK.geomInternalize_T/_B/_Four` | the three `TS5` instances — `.refl` / `.symm ∘ .base` / `.trans ∘ .base ∘ .base` |
| `Deriv.geomInternalize` | lifts to `Deriv` verbatim (the finite witness list is untouched) |

`NIK.weakenCl` is the load-bearing new lemma and is a **strict generalization of the existing
`NIK.weaken`** (`ClLe.of_le` derives the closure order from `Graph.le`). It went through as a
direct structural induction mirroring `NIK.weaken`, first try, no repair.

### `Deriv` / `Context.le` chain closure

Confirmed adequate. `Deriv 𝒯 G Γ φ := ∃ Γ₀, (∀ ψ ∈ Γ₀, ψ ∈ Γ) ∧ NIK 𝒯 G Γ₀ φ` (`Context.lean:190`)
is a plain finite-sublist bridge, so `(R_χ)` lifts with the witness list reused unchanged —
`Deriv.geomInternalize` is three lines. `Context.le` (`Context.lean:167`) is plain unbounded
inclusion with a `Preorder` instance; `Deriv.mono` already exists. Nothing here obstructs the Zorn
chain-closure argument.

---

## 4. NEW BLOCKER: `TPrime TS5 Atom` is uninhabited

This is not what the phase was dispatched to look for, and it is the highest-value thing it found.

### The defect (meets the 4-element bar)

**Current behavior.** `TPrime.clModel : ClassicalModel 𝒯 G.R` (`Context.lean:217`), where
`GeomAxiom.Holds .T R = ∀ x, R x x` (`Deduction.lean:140`) — quantified over the **whole
`Label Atom` type**.

**Required behavior.** [Simpson1994] p. 94 (PDF p. 103), verbatim, defining the canonical model:

> `D^𝒯_(H,Δ)` = the underlying set of `H`,  `R^𝒯_(H,Δ)(x,y)` iff `xRy` in `H`
> "for all `(H,Δ) ∈ W^𝒯`, `(D^𝒯_(H,Δ), R^𝒯_(H,Δ)) ⊨_CL 𝒯` **because
> `(D^𝒯_(H,Δ), R^𝒯_(H,Δ)) = H`** and `H ⊨_CL 𝒯` as `(H,Δ)` is `𝒯`-prime."

`H ⊨_CL 𝒯` is classical satisfaction **in the structure `H`**, whose domain is `H`'s underlying
set. Its quantifiers range over `H.X`, **not** over all labels.

**Counterexample.** Mechanized. A single-node reflexive-at-that-node graph satisfies
`ClassicalModelOn {χ_T} G.X G.R` (Simpson's clause 0) but refutes `ClassicalModel {χ_T} G.R`
(CSLib's). The CSLib statement is **strictly stronger** than the one Simpson discharges.

**And it is worse than inelegant — it empties the type.** `Graph.edge_mem`
(`Syntax.lean:119`) confines edges to `X`. Chain it:

```
clModel .T   ⟹  ∀ x, G.R x x
edge_mem     ⟹  ∀ x, x ∈ G.X          i.e.  G.X = univ
coinfinite   ⟹  ∃ V' coinfinite, G.X ⊆ W(V')
Label.InW V' (.var n) = n ∈ V',  and coinfiniteness supplies some n ∉ V'   ⟹  ⊥
```

Mechanized as **`tPrime_TS5_false : TPrime TS5 Atom → False`**, plus
`instance : IsEmpty (TPrime TS5 Atom)`. Universe-polymorphic; holds for **every** `Atom`.

Lemma 5.3.1's whole job is to **produce** a `𝒯`-prime context. At `𝒯 = TS5` the target type is
empty, so Phase 23 as specified could not succeed — not because the mathematics fails, but
because clause 0 carries the wrong quantifier range.

**Isolation.** `Deduction.lean:138-143` (`GeomAxiom.Holds`) and `:145-148` (`ClassicalModel`);
consumed by `Context.lean:217` (`TPrime.clModel`) and `Context.lean:~285`
(`equivalence_of_classicalModel_TS5`).

### Root cause is `χ_T` alone — mechanized

- `classicalModel_B_Four_trivial`: `{χ_B, χ_4}` is vacuously satisfied by the edgeless trivial
  graph, so **it does not empty `TPrime`**. Notably, the symmetry/transitivity half — where every
  previous wall in this task's history stood — is **not** the culprit here.
- `χ_T` is the sole offender because it is the only `TS5` axiom with **`n = 0` premises**: nothing
  constrains its `∀x` to `H`'s domain, so the type-wide reading demands edges at labels the Zorn
  poset `C` provably cannot reach (`C` fixes one coinfinite `V'` and admits only contexts with
  underlying set `⊆ W(V')`, p. 92 — so `H ∪ {zRz}` for `z ∉ W(V')` is **not in `C`** and
  maximality never forces it).

### The repair (for Phase 21/23 — NOT applied here; `Cslib/` is out of territory)

Retype clause 0 to Simpson's domain-relative form. Landed in the probe as `GeomAxiom.HoldsOn` /
`ClassicalModelOn` / `classicalModelOn_TS5_iff`, with `ClassicalModelOn.of_classicalModel`
recording that the current statement is strictly stronger:

```lean
clModel : ClassicalModelOn 𝒯 G.X G.R    -- was: ClassicalModel 𝒯 G.R
```

`classicalModelOn_TS5_iff` confirms the repair is **free at `TS5`**: `χ_B`/`χ_4` still unfold to
(domain-relative) symmetry and transitivity, exactly as `equivalence_of_classicalModel_TS5`
relies on.

**Known downstream consequence, flagged not solved**: `equivalence_of_classicalModel_TS5` returns
a **type-wide** `Equivalence R`, which the frame-class match (`cs5FCIncest`) consumes. Under the
repair it becomes an equivalence **on `G.X`**. Phase 23 must either carry a domain-relative
equivalence or make the canonical model's world domain a subtype `↥H.X`. This is a design choice
Phase 23 must make deliberately; it is not decided here. `equivalence_of_refl_eucl` is unaffected
(it is a statement about an arbitrary `R`, retained by Phase 18).

### The shortcut Phase 21 must NOT take

`classicalModel_tClosure_free : ClassicalModel TS5 (TClosure TS5 R)` is **free** — three
constructor applications, no maximality, no `(R_Υ)`, no Zorn, **no axioms at all**. It is recorded
in the probe **specifically so it is not mistaken for a discharge of `clModel`**. It proves clause
0 for the *closure* of `H`, whereas p. 94 fixes `R^𝒯_(H,Δ)(x,y) iff xRy in H` — the **raw**
relation. Substituting the closure would silently change the canonical model and put the truth
lemma's `◇`-case (which reads `G.R x y` off `TPrime.diamond`, `Context.lean:225-226`) onto a
different relation than the one it is proved about. **Keep clause 0 about the raw relation;
relativize its quantifiers instead.**

### Scope: Phase 21 is unaffected — and the plan's sequencing is vindicated

Plan v3 sequences leg A1/A2 at **`𝒯 = ∅`** first. At `𝒯 = ∅`, clause 0 is **vacuous**
(`classicalModel_empty`, mechanized), so the emptiness chain has no premise to fire on and the
`(R_Υ)` obligation is empty. **The defect lands on Phase 23, not Phase 21.** The plan's D2
risk-sequencing decision — taken for unrelated reasons (symmetry-driven walls) — independently
saves Phase 21 from a blocker nobody had spotted.

---

## 5. Source-to-Implementation Mapping (H3)

All page numbers are **PDF-verified**. BibKey `Simpson1994` verified at `references.bib:86`.

| Source claim | BibKey / page | Lean target (file:line) | Translation notes |
|---|---|---|---|
| `H_i = H ∪ {v ∈ v_χz̄} ∪ {R_i1[z̄/x̄][v_χz̄/ȳ], ...}` | [Simpson1994] p. 92 | *(Phase 21)* | **PDF-only** — dropped by both chunk and `pdftotext` text layer |
| Basic geometric normal form, `m,n ≥ 0`, `n_i ≥ 1` | [Simpson1994] p. 72 | `GeomAxiom` `Deduction.lean:127-135` | `ȳ` empty for `T`/`B`/`Four` ⟹ `v_χz̄` empty |
| `(R_χ)`: *"`Δ ⊢_H x:A` derivable by an application of `(R_χ)`"* | [Simpson1994] p. 93 | `NIK.geomInternalize` (probe) | **CONFIRMED YES.** Via `TClosure.absorb_addEdge` + `NIK.weakenCl` |
| Requirement 3 on contexts | [Simpson1994] p. 91 | *(deleted by Phase 18)* | **Vacuous at `ȳ = ∅`.** Deletion compatible |
| *"by the maximality of `(H,Δ)`, `H_i = H`"* | [Simpson1994] p. 93 | *(Phase 21)* | Use **directly**; do not transcribe the reductio framing |
| `R^𝒯_(H,Δ)(x,y)` iff `xRy` in `H` (**raw**) | [Simpson1994] p. 94 | *(Phase 22)* | **Plan v3's Phase 22 says `𝒯-Comp(H)` — that contradicts the PDF. See §6.** |
| `H ⊨_CL 𝒯`, domain = `H`'s underlying set | [Simpson1994] p. 94 | `ClassicalModel` `Deduction.lean:145-148` | **DEFECT**: CSLib quantifies type-wide ⟹ `TPrime TS5` empty |
| Zorn over whole contexts, fixed coinfinite `V'` | [Simpson1994] p. 92 | `Context.le` `Context.lean:167`; `Deriv` `:190` | Confirmed adequate |
| Prime lemma is choice-free in principle | [Simpson1994] p. 93 | — | Simpson notes Zorn is avoidable but "laborious"; **use Zorn** |

### Discrepancies where PDF overrides another source

1. **`chunk_0102.md:11-12`** — `H_i`'s definition dropped. PDF wins. Corpus
   `provenance_fidelity: ocr_rescanned_reflowed_partial_symbol_loss` — expected and documented.
2. **Plan v3, Phase 22** — states `R_(H,Δ)(x,y)` iff `xRy` in **`𝒯-Comp(H)`**. PDF p. 94 says
   **raw** `xRy in H`, and its justification sentence (*"because `(D,R) = H`"*) is unintelligible
   under the closure reading. **The plan is wrong here; correct before Phase 22.** This matters:
   under the closure reading `clModel` would be free (§4's shortcut) and the truth lemma's
   `◇`-case would silently change relation.
3. **Plan v3, Phase 20 quote** — omits `H_i`'s witness-variable component. Harmless at `TS5`
   (empty), but the omission is exactly what obscured the requirement-3 question.

---

## 6. Adversarial Self-Verification (H4)

| Claim | Refutation attempt / Source | Outcome |
|---|---|---|
| `TClosure` admits `(R_Υ)` for `TS5` | Tried to break it by finding an `NIK` rule reading `G.R` raw or `G.X`. **Inspected all 12 constructors** (`Deduction.lean:203-262`): only `boxE`/`diaI` have relational premises, both over `TClosure 𝒯 G.R`; `G.X` is read by **none**. | **HOLDS** — mechanized, `[propext]` |
| Requirement 3 vacuous at `ȳ = ∅` | Tried reading its "only if" as a biconditional or as unconditional graph closure. Neither survives the verbatim text: the subject is *"each of the witness variables in `v_χz̄`"*, and p. 91 fixes `v_χz̄` as "of the same length as `ȳ`". | **HOLDS** |
| Chunk says 5.3.1 cites requirement 3 → Phase 18 broke something | **Tried hard to make this the finding** (it was the dispatch's stated suspicion). The citation is real (p. 93) but vacuous at `ȳ = ∅`; §2's case-split shows requirement 3 covers only the maximality blind spot. | **REFUTED** — Conflict 7 confirmed |
| `TPrime TS5 Atom` is empty | Tried to escape via: (a) `Atom`-dependence — no, universe-polymorphic, `Label.var n` exists for all `Atom`; (b) enlarging `V'` — no, `C` fixes `V'` (p. 92) and coinfiniteness must survive; (c) `Graph` not enforcing edge/node containment — **no, `edge_mem` does** (`Syntax.lean:119`; I initially missed this field and the compiler corrected me). | **HOLDS** — mechanized |
| The emptiness blocks Phase 21 | Checked `𝒯 = ∅`: clause 0 vacuous (`classicalModel_empty`). | **REFUTED** — blocker lands on Phase 23 |
| Phase 18 should be reversed | Its deletions (`Five_mem_TS5`, `GeomAxiom.D`, `GeomWitnessClosure`) are orthogonal to this defect, which lives in `ClassicalModel`'s quantifier and predates them. | **NO** — do not reverse |

### Uncertainty, flagged rather than asserted

- **MEDIUM**: the `ClassicalModelOn` repair is *stated* and shown free at `TS5`, but **not landed
  against a real `TPrime` construction** — no Zorn argument exists yet to fail against it. Phase 21
  is where it gets tested. I claim the repair removes *this* contradiction; I do **not** claim it
  makes `TPrime TS5` inhabited (that is Phases 21+23's burden).
- **MEDIUM**: the `Equivalence`-relativization consequence (§4) is identified but **unsolved**.
- **LOW-MEDIUM**: my p. 94 reading (raw vs closure) contradicts plan v3. I am confident in the PDF
  text; I am less confident nothing downstream in Ch. 5 (pp. 95-98, not read this dispatch) uses
  the closure. **Phase 22 should re-verify against pp. 95-98 before committing.**
- **LOW**: `Deriv`/`Context.le` chain closure judged adequate from signatures + `Deriv.mono`; I did
  **not** mechanize a Zorn chain-union. Simpson calls it *"easily seen"* (p. 92) — historically a
  phrase worth distrusting, but the union of a chain of contexts is genuinely routine.
- **Not checked**: whether requirement 2 (`Context.dwitness` clause) survives `H_i = H ∪ {c}`. It
  should (adding an edge adds no witness variables), but Phase 21 must discharge `(H_i,Δ) ∈ C`
  in full, which includes it.

---

## 7. Recommendation

**Proceed to Phase 21 at `𝒯 = ∅` as planned.** The pre-gate's mission question is answered YES and
mechanized; leg A's first real obstacle is cleared; `𝒯 = ∅` is provably unaffected by the new
blocker.

**Before Phase 23, insert a repair phase** (small, ~40 lines, mainline `Cslib/`):
relativize `GeomAxiom.Holds` → `HoldsOn`, `ClassicalModel` → `ClassicalModelOn 𝒯 G.X`, retype
`TPrime.clModel`, and adjust `equivalence_of_classicalModel_TS5`. Probe declarations are ready to
lift. **Phase 23 is impossible until this lands** — `IsEmpty (TPrime TS5 Atom)`.

**Correct plan v3's Phase 22** to `R_(H,Δ)(x,y)` iff `xRy` in **`H`** (raw), per p. 94.

**Carry into Phase 21's dispatch**: do not transcribe p. 92-93's reductio framing literally at a
quantifier-free axiom — use `H_i = H` directly (§2).
