# Research Report: Sorry-Free Decidability for IntPropAxiom / MinPropAxiom (Task 370)

**Task:** 370_int_min_metalogic_decidability
**Session:** sess_1782560395_aeb7ef_370
**Date:** 2026-06-27
**Agent:** cslib-research-agent

---

## 1. Executive Summary

The task framing ("intuitionistic and minimal logics have no decision procedure") is
**literally inaccurate but morally correct**. Decidability instances *already exist* for both:

- `instDecidableDerivableIntPropAxiom : Decidable (Derivable IntPropAxiom φ)`
  — `Tableau/Intuitionistic/DecisionProcedure.lean:80`
- `instDecidableDerivableMinPropAxiom : Decidable (Derivable MinPropAxiom φ)`
  — `Tableau/Minimal/DecisionProcedure.lean:81`

Both are **sorry-tainted**: they are valid as terms but transitively depend on the unproved
tableau completeness witnesses (`intuitionisticTableau_complete`, 4 sorries;
`minimalTableau_complete` / `minTruthLemma`, 3 sorries). The genuine goal is a **sorry-free**
decision procedure independent of the tableau.

**Key reduction.** The metalogic completeness theorems are sorry-free and trusted:

- `int_soundness_completeness : IValid φ ↔ Derivable IntPropAxiom φ` (IntStrongCompleteness.lean:338)
- `min_soundness_completeness : MValid φ ↔ Derivable MinPropAxiom φ` (MinStrongCompleteness.lean:333)

Therefore the entire task reduces to building a **sorry-free `Decidable (IValid φ)` and
`Decidable (MValid φ)`** (or, equivalently and more directly, a sorry-free decidable
characterization of `Derivable IntPropAxiom φ` / `Derivable MinPropAxiom φ`). Everything else
is a one-line `decidable_of_iff` through the existing sorry-free completeness `Iff`s.

**Recommendation: the FMP route (finite canonical Kripke model), strategy (b) "direct finite
model", NOT the LJ bridge.** Justification in §3. This is a **high-effort, high-risk**
formalization (estimated 1000–1800 lines across Int+Min); §6 gives a de-risking spike and a
staged plan, and §7 states the BLOCKED criterion if the spike fails. No sorry deferral is
recommended anywhere.

---

## 2. Verified Findings (lean-lsp + source inspection)

### 2.1 Existing decidability instances and their sorry-dependence

| Instance | File:line | Decides | Sorry-free? |
|---|---|---|---|
| `instDecidableDerivablePropositionalAxiom` | StrongCompleteness.lean:566 | `Derivable PropositionalAxiom φ` (classical) | **Yes** — via `instDecidableTautology` (Bool valuation enumeration, `Semantics/Bool.lean:175`), needs `[Fintype Atom] [DecidableEq Atom]` |
| `instDecidableDerivableIntPropAxiom` | Tableau/Intuitionistic/DecisionProcedure.lean:80 | `Derivable IntPropAxiom φ` | **No** — `isFalse` branch calls `intuitionisticTableau_complete` (4 sorries) |
| `instDecidableDerivableMinPropAxiom` | Tableau/Minimal/DecisionProcedure.lean:81 | `Derivable MinPropAxiom φ` | **No** — depends on `minimalTableau_complete` / `minTruthLemma` (sorries) |
| `instDecidableLJDerivable` | SequentCalculus/LJ/Decidability.lean:189 | `Nonempty (LJProof (Γ ⊢ A))` | **No** — `decidable_of_iff (IValid (ctxToImp Γ A))` routes through tableau `instDecidableIValid` |
| `instDecidableDerivableInIPL` | SequentCalculus/LJ/Decidability.lean:207 | `DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ A)` | **No** — built on `instDecidableLJDerivable` |

**Sorry inventory (the taint source):**
- `Tableau/Intuitionistic/Completeness.lean` — sorries at lines 89, 98, 112 (the open-branch
  truth lemma / countermodel; comment at line 37 says "All proofs are marked sorry").
- `Tableau/Minimal/Completeness.lean` — sorries at lines 168, 179, 190 (`minTruthLemma` +
  countermodel).
- `Tableau/Classical/Completeness.lean:492` — 1 sorry (classical tableau; not on the critical
  path because the classical instance uses `instDecidableTautology` instead).

### 2.2 What IS sorry-free and reusable (the assets)

- `Cslib/Logics/Propositional/Metalogic/` — **entirely sorry-free** (grep confirmed). In
  particular: `int_soundness_completeness`, `min_soundness_completeness`, `int_completeness`,
  `min_completeness`, `int_soundness`/`min_soundness` (the `Derivable → *Valid` directions),
  and the canonical-model machinery:
  - `IntCanonicalWorld := { S // IntPrimeDCCS S }` (IntStrongCompleteness.lean:72)
  - `int_truth_lemma : IForces intCanonicalVal (fun _ => False) S φ ↔ φ ∈ S.val`
    (IntStrongCompleteness.lean:97) — structural recursion on φ; **directly reusable as a proof
    template** for the finite truth lemma.
  - `IntDCCS`, `intDeductiveClosure`, `int_imp_witness`, `IntPrimeDCCS`, `int_prime_exclusion`
    (IntLindenbaum.lean:36,193,234,261,319) — the prime-extension toolkit (currently
    Zorn-based and **unbounded**; bounded analogues needed, see §4).
  - Minimal mirror: `MinCanonicalWorld`, `min_truth_lemma`, `minBotForces`,
    `min_imp_witness`, `min_prime_exclusion` (MinStrongCompleteness.lean / MinLindenbaum.lean).
- `Cslib/Logics/Propositional/SequentCalculus/` — **entirely sorry-free**, including
  `lj_iff_ivalid : IValid φ ↔ Nonempty (LJProof (∅ ⊢ φ))` (LJ/Completeness.lean:284). Note this
  is the *equivalence*; the *decision* of `Nonempty (LJProof …)` is what routes through the
  tableau.

### 2.3 Decidability-relevant facts

- `Proposition Atom` **derives `DecidableEq`** (Defs.lean:92). 5 constructors: `atom`, `bot`,
  `imp`, `and`, `or`.
- `IValid φ` (Kripke.lean:145) is **universe-polymorphic**:
  `∀ (World : Type v) [Preorder World] (val) (upward-closure), ∀ w, IForces val (fun _ => False) w φ`.
  This `∀ World` is why `Decidable (IValid φ)` is not trivial — it needs FMP to collapse the
  quantifier to a single finite model.
- `MValid φ` (Kripke.lean:153) is the same but with an arbitrary upward-closed `bot_forces`.
- `IForces … (.imp φ ψ)` unfolds to `∀ w', w ≤ w' → IForces … w' φ → IForces … w' ψ`
  (Kripke.lean:100) — the only quantifier-bearing case; on a `Fintype` world with decidable
  `≤`/`val` it is decidable by `Fintype.decidableForallFintype` + structural induction.
- **No subformula machinery exists** (no `subformulas`/`Sub`/closure def anywhere in
  `Logics/Propositional`). **No filtration / finite-model infrastructure exists** (only a
  passing comment at `Tableau/Intuitionistic/Expansion.lean:230`).
- `instDecidableTautology` (classical) needs `[Fintype Atom]`. The FMP route does **not** need
  `Fintype Atom` in principle (only atoms occurring in φ matter), but requiring
  `[Fintype Atom] [DecidableEq Atom]` to match the classical instance's signature is an
  acceptable simplification (see §5 risk R5).

---

## 3. Route Assessment — FMP vs LJ Bridge

### Route A — Bridge to the existing LJ tableau-backed decidability. **REJECTED.**

The LJ decidability instance `instDecidableLJDerivable` is, by its own construction
(`decidable_of_iff (IValid (ctxToImp Γ A))` at LJ/Decidability.lean:191), **backed by the
tableau** `instDecidableIValid`, which carries the 4 intuitionistic completeness sorries.
Bridging the metalogic `Derivable IntPropAxiom φ` to `Nonempty (LJProof (∅ ⊢ φ))` therefore
**inherits the exact taint the task requires us to avoid**. The task is explicit:
"Independent of the tableau decision procedures (which currently rest on unproved completeness
witnesses)."

The LJ route could only become sorry-free by adding a **new terminating syntactic proof
search** (Dyckhoff's contraction-free G4ip/LJT) with its own termination + soundness/
completeness against `LJProof`, then bridging `LJProof ↔ G4ip`. That is a *larger* new
development than FMP and duplicates no existing asset. There is **no terminating LJ search in
the codebase today** (the only `Decidable (Nonempty (LJProof …))` is the semantic one). So
"bridge to LJ decidability" is not a clean source.

### Route B — FMP via finite canonical Kripke model. **RECOMMENDED.**

This is the **only** route that produces a genuinely sorry-free decision procedure while
reusing existing sorry-free assets (`int_truth_lemma` template, the Lindenbaum toolkit,
`int_soundness`, and the completeness `Iff`s). It is also semantically "native" to the
metalogic layer the task targets, and it is fully independent of the tableau.

Two FMP sub-strategies:

- **(a) Filtration of the canonical model** (quotient `IntCanonicalWorld` by "agree on
  `Sub φ`"). Reuses `int_truth_lemma` most directly, but the **intuitionistic filtration imp
  case is a known pitfall** (choosing the correct preorder on filtered worlds; minimal vs
  transitive filtration). Quotient types add friction. **Not recommended.**
- **(b) Direct finite canonical model** — worlds = `Sub φ`-bounded prime saturated theories;
  preorder = `⊆`; `val w p := p ∈ w`. Avoids quotients and Zorn (finite Lindenbaum is
  constructive); the decision procedure naturally enumerates `(Sub φ).powerset`. **Recommended.**

---

## 4. Concrete Lean Construction (Route B, Int; Min mirrors)

New file suggestion: `Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` (and
`MinDecidability.lean`), each `import Cslib.Init` and the corresponding `*StrongCompleteness`.

### Phase 0 — Subformula closure (shared infra; new)

```lean
/-- Subformula closure as a Finset (includes φ itself and all proper subformulas). -/
def subformulas [DecidableEq Atom] : PL.Proposition Atom → Finset (PL.Proposition Atom)
  | .atom p      => {.atom p}
  | .bot         => {.bot}
  | .imp a b     => insert (.imp a b) (subformulas a ∪ subformulas b)
  | .and a b     => insert (.and a b) (subformulas a ∪ subformulas b)
  | .or  a b     => insert (.or  a b) (subformulas a ∪ subformulas b)

theorem self_mem_subformulas (φ) : φ ∈ subformulas φ
theorem subformulas_closed_imp_left  {a b φ} (h : (.imp a b) ∈ subformulas φ) : a ∈ subformulas φ
-- …and the other 4 closure lemmas (imp_right, and_left/right, or_left/right)
```
Risk: **LOW** (mechanical structural recursion; `simp`/`Finset.mem_*` lemmas).

### Phase 1 — Finite world type + Fintype

Let `Σ := subformulas φ`. Define the `Σ`-bounded prime saturated predicate on `Finset`:

```lean
structure IntFinWorld (φ : PL.Proposition Atom) where
  carrier   : Finset (PL.Proposition Atom)
  sub       : carrier ⊆ subformulas φ
  closed    : ∀ ψ ∈ subformulas φ, SetDerivable IntPropAxiom ↑carrier ψ → ψ ∈ carrier
  consistent: ⊥ ∈ subformulas φ → ⊥ ∉ carrier            -- (Int only; Min drops this)
  prime     : ∀ a b, (.or a b) ∈ carrier → a ∈ carrier ∨ b ∈ carrier

instance : Fintype (IntFinWorld φ)   -- worlds inject into (subformulas φ).powerset
instance : Preorder (IntFinWorld φ) := ⟨(·.carrier ⊆ ·.carrier), …⟩
```
`Fintype` follows because `carrier ∈ (Σ.powerset)` and the remaining fields are `Prop`/
`Subsingleton`; build via `Fintype.ofFinset` over `Σ.powerset.filter (decidable predicate)`.
All world conditions are **decidable** Finset predicates (membership, `∀ ψ ∈ Σ`, the
`SetDerivable` condition is the subtle one — see R3, handled by restricting to `ψ ∈ Σ` and
using a *bounded* derivability check, or by carrying `closed` as data rather than recomputing).

Risk: **MEDIUM** — the `closed` field references `SetDerivable` (a `Prop` about an unbounded
derivation). For the `Fintype`/decidability of *membership in the world set* we must avoid
deciding `SetDerivable`. Resolution: define worlds as `Σ.powerset.filter P` where `P` is a
*purely finitary* saturation predicate, and prove separately that filtered sets are exactly the
restrictions of prime DCCS. (This is the crux; see spike in §6.)

### Phase 2 — Valuation, upward closure, finite truth lemma

```lean
def intFinVal (w : IntFinWorld φ) (p : Atom) : Prop := (.atom p) ∈ w.carrier
theorem intFinVal_upward_closed …                       -- from ⊆ order
-- Reuse int_truth_lemma as a TEMPLATE (same case structure):
theorem int_fin_truth_lemma (w : IntFinWorld φ) {ψ} (hψ : ψ ∈ subformulas φ) :
    IForces intFinVal (fun _ => False) w ψ ↔ ψ ∈ w.carrier
```
The `imp` backward case needs the **`Σ`-bounded imp witness** (Phase 3). The `bot`, `and`,
`or`, `atom` cases mirror `int_truth_lemma` line-for-line.
Risk: **MEDIUM** (depends on Phase 3).

### Phase 3 — `Σ`-bounded finite Lindenbaum (the deepest new lemma)

```lean
/-- If `ψ→χ ∉ w` and `ψ→χ ∈ Σ`, there is a world `w' ≥ w` with `ψ ∈ w'`, `χ ∉ w'`. -/
theorem int_fin_imp_witness (w : IntFinWorld φ) {ψ χ}
    (hmem : (.imp ψ χ) ∈ subformulas φ) (hnot : (.imp ψ χ) ∉ w.carrier) :
    ∃ w' : IntFinWorld φ, w ≤ w' ∧ ψ ∈ w'.carrier ∧ χ ∉ w'.carrier
```
Proof skeleton (mirrors `int_imp_witness` + `int_prime_exclusion`, but **finite, no Zorn**):
1. `w.carrier ∪ {ψ} ⊬ χ` — else by the deduction theorem `w ⊢ ψ→χ`; since `ψ→χ ∈ Σ`, the
   `closed` field forces `ψ→χ ∈ w.carrier`, contradicting `hnot`.
2. Extend `w.carrier ∪ {ψ}` to a `Σ`-bounded prime saturated set omitting χ by **finite
   iteration over `Σ`** (decide each `ζ ∈ Σ` in turn; this is the constructive finite
   Lindenbaum that replaces `int_prime_exclusion`'s Zorn argument).
3. Package as an `IntFinWorld φ`.
Risk: **HIGH** — this is the single most uncertain lemma. The finite Lindenbaum/saturation
construction and its prime+closed invariants are where the effort concentrates. **De-risk this
first (see §6 spike).**

### Phase 4 — FMP characterization + Decidable instance

```lean
/-- Finite model property: derivability ⇔ membership in every Σ-bounded prime world. -/
theorem int_fmp (φ) :
    Derivable IntPropAxiom φ ↔ ∀ w : IntFinWorld φ, φ ∈ w.carrier := by
  constructor
  · -- (→) soundness over the finite model: int_soundness gives IValid; instantiate at
    --     World := IntFinWorld φ; int_fin_truth_lemma (φ ∈ Σ by self_mem_subformulas).
    …
  · -- (←) completeness/FMP: contrapositive. If ¬Derivable then the closure of ∅ within Σ
    --     omitting φ extends (int_fin_imp_witness-style finite Lindenbaum) to a world w with
    --     φ ∉ w.carrier.
    …

noncomputable instance instDecidableDerivableIntPropAxiom' (φ) :
    Decidable (Derivable IntPropAxiom φ) :=
  decidable_of_iff (∀ w : IntFinWorld φ, φ ∈ w.carrier) (int_fmp φ).symm
```
`∀ w : IntFinWorld φ, φ ∈ w.carrier` is decidable via `Fintype.decidableForallFintype` +
`DecidableEq (Proposition Atom)`. The `(→)` direction reuses sorry-free `int_soundness`; the
`(←)` is the FMP content built on Phase 3.
Risk: **MEDIUM** (assembly; the hard content is Phase 3).

### Min mirror

Identical structure with: worlds = `Σ`-bounded prime **MinTheory** (drop the `consistent`
field — `⊥` may belong to a world), valuation plus a separate `minBotForces`-style predicate
on worlds, reuse `min_truth_lemma` template and `min_imp_witness`/`min_prime_exclusion`
patterns. The bot case is `Iff.rfl`-trivial (per MinStrongCompleteness.lean:41), which is
*easier* than Int. Final: `decidable_of_iff … (min_fmp φ).symm`.

---

## 5. Risk Register

| ID | Risk | Severity | Mitigation |
|---|---|---|---|
| R1 | `int_fin_imp_witness` finite Lindenbaum (Phase 3) may resist a clean finite construction | **HIGH** | De-risking spike (§6) before committing the full plan |
| R2 | `IntFinWorld` `Fintype`/decidability blocked by the `closed` field referencing `SetDerivable` (a `Prop` over unbounded derivations) | **HIGH** | Define worlds as `Σ.powerset.filter P` with finitary `P`; prove equivalence to "restriction of prime DCCS" separately; do not decide `SetDerivable` |
| R3 | Intuitionistic `imp` truth-lemma case requires the witness world, coupling Phase 2 ↔ Phase 3 | MED | Land Phase 3 first; Phase 2 imp case is then a direct call |
| R4 | Universe polymorphism of `IValid` when instantiating the finite model in the `(→)` direction | LOW | Pick `World := IntFinWorld φ : Type _`; `int_soundness`/`IValid` are polymorphic, instantiate freely. The decision `Iff` targets `Derivable` directly, bypassing `IValid` for `(←)` |
| R5 | Whether `[Fintype Atom]` is needed | LOW | Not strictly needed (only atoms in φ matter), but adding `[Fintype Atom] [DecidableEq Atom]` matches the classical instance and simplifies; recommend matching that signature |
| R6 | Naming collision with existing `instDecidableDerivableIntPropAxiom` (tableau) | LOW | New file/namespace or a primed name; the tableau instance can later be deprecated or re-routed once FMP lands |
| R7 | `lake shake` / `checkInitImports` / import minimization on new files | LOW | Standard CI hygiene; `import Cslib.Init` first line; run `lake exe mk_all --module` |
| R8 | Effort overrun (est. 1000–1800 lines) exceeds a single implementation cycle | MED | Staged plan (§6); Int and Min as separate phases; commit at each green milestone |

---

## 6. Recommended De-Risking Spike + Staged Plan

**Spike (do before the full plan is committed):** prove `int_fin_imp_witness` (Phase 3) and the
`IntFinWorld` `Fintype` instance (Phase 1) in isolation, against a tiny concrete Σ, OR prove the
two as standalone lemmas with the rest of the file `sorry`-stubbed *only inside the spike
scratch file* (never in committed code). If the finite Lindenbaum construction lands cleanly,
proceed. If it does not after a bounded effort, **mark the task `[BLOCKED]`** (see §7) rather
than deferring with sorry.

**Staged plan (each stage = one green `lake build`, committed):**
1. Phase 0 — `subformulas` + closure lemmas (LOW risk; standalone).
2. Phase 1 — `IntFinWorld`, `Fintype`, `Preorder`, decidability of world membership (resolve R2).
3. **Spike gate** — Phase 3 `int_fin_imp_witness` (HIGH risk; the go/no-go point).
4. Phase 2 — `intFinVal`, upward closure, `int_fin_truth_lemma` (depends on 3).
5. Phase 4 — `int_fmp` + `Decidable` instance (Int complete).
6. Min mirror (Phases 0–4 analogues; bot case trivial).
7. CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
   `lake shake --add-public --keep-implied --keep-prefix`; `lake exe mk_all --module` for new files.

---

## 7. Zero-Debt Compliance & BLOCKED Criterion

- **No sorry deferral, no new axioms.** `Classical.choice` / `Decidable.decide` on `noncomputable`
  defs are acceptable per the task (the FMP instance will likely be `noncomputable` because the
  finite-Lindenbaum extension uses classical choice over a finite domain, paralleling the
  existing `noncomputable` LJ instances). The decision `Prop` itself is `Decidable` by
  `Fintype.decidableForallFintype`, so the *instance* is computable in principle even if the
  *correctness proof* uses choice.
- **BLOCKED criterion:** if the §6 spike (Phase 3 finite Lindenbaum / R2 Fintype) cannot be
  discharged sorry-free within the allotted implementation effort, the correct outcome is
  `[BLOCKED]` with a documented goal state — **not** a sorry placeholder and **not** falling back
  to the tableau-backed instance.
- **Explicitly rejected fallback:** discharging the 4 tableau completeness sorries (which would
  retroactively clean the *existing* instances) is a real alternative path, but the task
  mandates independence from the tableau, so it is **out of scope** and only noted here for
  completeness.

---

## 8. Lemma / Asset Candidate Index

Reusable sorry-free assets (cite in the plan):
- `int_soundness`, `min_soundness` (`Derivable → IValid/MValid`) — for the `(→)` FMP direction.
- `int_truth_lemma` (IntStrongCompleteness.lean:97), `min_truth_lemma` — **proof templates** for
  the finite truth lemma (identical case structure).
- `int_imp_witness` / `int_prime_exclusion` (IntLindenbaum.lean:234/319),
  `min_imp_witness` / `min_prime_exclusion` — **proof patterns** for the bounded finite
  Lindenbaum (replace Zorn with finite iteration over Σ).
- `int_soundness_completeness` / `min_soundness_completeness` — final `decidable_of_iff` bridge
  (if targeting `IValid`/`MValid`); or bypass and target `Derivable` directly via `int_fmp`.
- `SetDerivable`, deduction theorem (`DeductionTheorem.lean`), `intDeductiveClosure` — for the
  `closed`-field reasoning and step 1 of `int_fin_imp_witness`.
- `Proposition` `DecidableEq` (Defs.lean:92), `Finset.powerset`, `Fintype.decidableForallFintype`,
  `Fintype.ofFinset` — decidability plumbing.

New definitions/lemmas to create: `subformulas` (+6 closure lemmas), `IntFinWorld`/`MinFinWorld`
(+`Fintype`,`Preorder`), `intFinVal`/`minFinVal` (+upward closure), `int_fin_truth_lemma`/
`min_fin_truth_lemma`, `int_fin_imp_witness`/`min_fin_imp_witness`, `int_fmp`/`min_fmp`, and the
two `Decidable` instances.

---

## 9. Bottom Line

- Existing Int/Min `Decidable` instances are sorry-tainted via the tableau; the LJ bridge does
  not escape that taint and is therefore not a clean source.
- The metalogic completeness `Iff`s are sorry-free, so the whole task is "build a sorry-free
  `Decidable (IValid φ)`/`Decidable (MValid φ)`," achievable only via **FMP**.
- Recommended: **FMP, direct finite canonical model (strategy b)**, staged with an early
  go/no-go **spike on the finite Lindenbaum lemma** (the one HIGH-risk component). Feasible but
  genuinely hard (~1000–1800 lines); honest risk = HIGH on Phase 3, MEDIUM overall.
