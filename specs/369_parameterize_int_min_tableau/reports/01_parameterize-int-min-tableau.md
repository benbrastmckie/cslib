# Research Report: Parameterize the Intuitionistic & Minimal Tableau Developments (Task 369)

**Task type:** cslib (Lean 4) | **Phase:** research | **Status:** researched
**Goal:** Remove ~400 lines of Int/Min tableau duplication; unify the two completeness obligations
into ONE parametric truth-lemma + countermodel pair, abstracting over `(closurePred, modelBot)`.

---

## 0. Executive Summary

- **Soundness is ALREADY parameterized.** The generic engine
  `intExpandBranches_closed_unsat` (Int `Soundness.lean:1083`) takes `closurePred` and a
  `closed_unsat` hypothesis as explicit arguments. Both `intuitionisticTableau_sound`
  (`Soundness.lean:1587`) and `minimalTableau_sound` (`Minimal/Soundness.lean:118`) are thin
  instantiations of it. The only Min-specific soundness code is `minClosed_unsatisfiable`
  (~45 lines) + a ~37-line wrapper. **Both Soundness files are sorry-free (task 316 closed
  them) — the refactor must preserve this.**
- **The real duplication lives in Completeness.** `Int/Completeness.lean` (116 lines) and
  `Min/Completeness.lean` (194 lines) each declare a structurally identical
  truth-lemma / open-branch-countermodel / tableau-complete trio. They diverge ONLY in
  `(closurePred, modelBot)`.
- **Sorry census (actual `sorry` tokens):** 3 in Int/Completeness + 3 in Min/Completeness = **6**.
  Soundness = 0, DecisionProcedure = 0 (depend transitively on the completeness sorries).
  (The "4 sorries" phrasing in the DecisionProcedure docstrings is stale.)
- **The Classical analog (`Tableau/Classical/`, tasks 363/376) is fully sorry-free** and is the
  reference for the green truth-lemma + countermodel structure.
- **`ClosureCondition` (Foundations) is reused at the leaf** (`isIntuitionisticallyClosed`
  composes `IntuitionisticClosure.isClosed`), but the soundness/completeness scaffolding
  parameterizes over the raw `closurePred : IBranch Atom → Bool` — that is the correct
  granularity. Do NOT try to thread the typeclass through the scaffolding.

---

## 1. Duplication Map (file:line)

### 1.1 Already deduplicated (do not touch)
| Shared asset | Location | Notes |
|---|---|---|
| `intExpandBranches` (rule engine, fuel loop) | `Intuitionistic/Expansion.lean:153` | Takes `closurePred` as a param. Both tableaux call it. |
| `intuitionisticTableau` / `minimalTableau` | `Expansion.lean:231` / `:244` | Identical modulo `isIntuitionisticallyClosed` vs `isMinimallyClosed`. |
| `intExpandBranches_closed_unsat` | `Intuitionistic/Soundness.lean:1083` | Generic over `closurePred` + `closed_unsat`. ~500-line proof, shared. |
| `intBranchSatisfied`, `intRule_preserves_sat`, persistence-fixpoint sat lemmas | `Soundness.lean:56,83,355,413` | Already quantify `botForces`; reused by Min directly. |
| `intExtractValuation` | `Intuitionistic/Completeness.lean:57` | Min reuses it directly (`Min/Completeness.lean:24` imports Int). |

### 1.2 Duplicated trio — the unification target (byte-identical modulo `(closurePred, modelBot)`)

| Concept | Intuitionistic | Minimal | Divergence |
|---|---|---|---|
| `botForces` data | `intBotForces := fun _ => False` (`Int/Completeness.lean:61`) | `minBranchBotForces b w := T(⊥)@w ∈ b` (`Min/Completeness.lean:78-80`) | **modelBot** |
| Truth lemma | `intTruthLemma` (`Int/Completeness.lean:81-89`, **sorry**) | `minTruthLemma` (`Min/Completeness.lean:160-168`, **sorry**) | `intBotForces` → `minBranchBotForces b`; `isIntuitionisticallyClosed` → `isMinimallyClosed` |
| Open-branch countermodel | `intuitionisticOpenBranch_countermodel` (`Int/Completeness.lean:95-98`, **sorry**) | `minOpenBranch_countermodel` (`Min/Completeness.lean:176-179`, **sorry**) | tableau + modelBot |
| Completeness theorem | `intuitionisticTableau_complete` (`Int/Completeness.lean:110-112`, **sorry**) | `minimalTableau_complete` (`Min/Completeness.lean:188-190`, **sorry**) | tableau + validity (`IValid`/`MValid`) |

The two truth-lemma SIGNATURES are line-for-line identical except for the `botForces` argument
and the closure-hypothesis predicate. Same for the countermodel and completeness statements.

### 1.3 Min-specific soundness (thin, mostly an instantiation)
- `minClosed_unsatisfiable` (`Min/Soundness.lean:69-105`): a genuine ~37-line proof (uses
  `Branch.hasContradiction`). This is the Min analog of `intClosed_unsatisfiable`
  (`Int/Soundness.lean:284`). **Both must remain as the `closed_unsat` witnesses** — they are
  the per-logic soundness obligation; not pure duplication.
- `minimalTableau_sound` (`Min/Soundness.lean:118-153`): structurally identical to
  `intuitionisticTableau_sound` modulo `(isMinimallyClosed, minClosed_unsatisfiable)` and the
  `botForces` instantiation. **~35 lines collapsible** into a single generic `tableau_sound S`.

### 1.4 DecisionProcedure (trivial, ~85 lines each)
`Int/DecisionProcedure.lean` and `Min/DecisionProcedure.lean` are near-identical: a `_decides`
biconditional, an `instDecidable{I,M}Valid`, and an `instDecidableDerivable…PropAxiom`. They
differ only by tableau/validity/axiom names. **Collapsible to one generic `tableau_decides S` +
`decidableValid S`**, with two ~10-line instance shims.

**Estimated removable duplication:** Min/Completeness (194) + Min/Soundness collapse (~35) +
Int duplicated trio scaffolding/docs (~80) + DecisionProcedure collapse (~60) ≈ **350-400 lines**,
matching the task estimate.

---

## 2. Parameterization Design

### 2.1 Why a structure, not a typeclass
The two divergence axes are **value-level data on branches**, not type-level:
`closurePred : IBranch Atom → Bool` and the completeness-side `modelBot : IBranch Atom → Nat → Prop`.
`closurePred` is already an explicit value argument everywhere it matters. A bundling `structure`
(a "scheme" record) is the natural carrier; a typeclass would force awkward instance resolution
on `Bool`-valued data and does not match `ClosureCondition`'s granularity (see §2.4).

### 2.2 The abstraction interface

```lean
/-- A tableau scheme bundling the two points where the intuitionistic and minimal
developments diverge, plus their per-logic proof obligations. -/
structure IntMinScheme (Atom : Type*) [DecidableEq Atom] [Hashable Atom] where
  /-- Branch closure predicate (Int: isIntuitionisticallyClosed; Min: isMinimallyClosed). -/
  closurePred : IBranch Atom → Bool
  /-- Countermodel's botForces, built from the open branch
      (Int: `fun _ _ => False`; Min: `minBranchBotForces`). -/
  modelBot : IBranch Atom → Nat → Prop
  /-- Soundness obligation: a closed branch is unsatisfiable under any model. -/
  closed_unsat : ∀ {World : Type} [Preorder World]
      (val : World → Atom → Prop) (bf : World → Prop) (worldOf : Nat → World)
      (b : IBranch Atom), closurePred b = true → ¬ intBranchSatisfied val bf worldOf b
  /-- Completeness bot-case obligation: on an open branch, T(⊥)/F(⊥) match `modelBot`
      (Int: vacuous, T(⊥) cannot be open; Min: via `minOpen_no_contradiction`). -/
  bot_truth : ∀ (b : IBranch Atom), closurePred b = false → ∀ w,
      (T(⊥)@w ∈ b → modelBot b w) ∧ (F(⊥)@w ∈ b → ¬ modelBot b w)
  /-- `modelBot b` is upward-closed along the accessibility order (needed for persistence
      in the truth lemma). Int: trivially (False); Min: T(⊥) propagates by the persistence
      fixpoint. -/
  modelBot_uc : ∀ (b : IBranch Atom), ∀ {w w'}, w ≤ w' → modelBot b w → modelBot b w'
```

`tableau` and `valid` need NOT be scheme fields — they are derivable: the tableau is
`intExpandBranches [⟨.neg, φ, 0⟩] [[]] [1] [[]] (fuel φ) S.closurePred`, and the validity
predicate is supplied at the soundness call site (the `MValid`/`IValid` quantifier provides
`botForces`; `modelBot` is used only on the completeness side). If a uniform statement is
wanted, add `tableau` and `valid` as fields for ergonomics — optional.

### 2.3 Parametric soundness scaffolding (already generic; just wrap)

```lean
theorem tableau_sound (S : IntMinScheme Atom) (φ : Proposition Atom)
    (h : intExpandBranches [⟨.neg, φ,0⟩] [[]] [1] [[]] (2^(2*φ.complexity+2)) S.closurePred
          = .closed) :
    -- the appropriate validity, with botForces from the quantifier
```
Body = today's `intuitionisticTableau_sound` proof with `(isIntuitionisticallyClosed,
intClosed_unsatisfiable)` replaced by `(S.closurePred, S.closed_unsat)`. Instantiate twice.

### 2.4 How `ClosureCondition` (Foundations) is reused vs extended
- **Reused, unchanged, at the leaf:** `isIntuitionisticallyClosed`
  (`Expansion.lean:75-77`) = `IntuitionisticClosure.isClosed b || Branch.hasContradiction b`.
  The Foundations `ClosureCondition F L` typeclass + `IntuitionisticClosure` instance
  (`Foundations/Logic/Tableau/ClosureCondition.lean:98`) already supply the T(⊥) leaf check.
- **Not extended:** `isMinimallyClosed` = `Branch.hasContradiction` alone
  (`Expansion.lean:89`); it deliberately bypasses the typeclass (documented in
  `ClosureCondition.lean:31-33`). The scheme stores the composed `Bool` predicate, so no new
  typeclass instance is required. **Recommendation: leave `ClosureCondition` exactly as is;
  the scheme's `closurePred` field is the right abstraction boundary.**

### 2.5 The SINGLE parametric truth-lemma + countermodel pair (replaces both trios)

```lean
/-- THE one parametric truth lemma. Replaces `intTruthLemma` + `minTruthLemma`. -/
lemma truthLemma (S : IntMinScheme Atom) (b : IBranch Atom)
    (hopen : S.closurePred b = false) (hsat : <saturation>)
    (φ : Proposition Atom) (w : Nat) :
    (T(φ)@w ∈ b → IForces (intExtractValuation b) (S.modelBot b) w φ) ∧
    (F(φ)@w ∈ b → ¬ IForces (intExtractValuation b) (S.modelBot b) w φ) := by
  induction φ <;> ...   -- bot case discharged by S.bot_truth; imp/persistence by S.modelBot_uc
  sorry   -- <-- THE single remaining parametric obligation (task 317 discharges this)

/-- Parametric open-branch countermodel. Replaces both `*_OpenBranch_countermodel`. -/
lemma openBranch_countermodel (S : IntMinScheme Atom) (φ : Proposition Atom)
    (h : <tableau S> φ = .openBranch b) :
    ¬ IForces (intExtractValuation b) (S.modelBot b) 0 φ := by
  -- derived from `truthLemma S b _ _ φ 0` + (F(φ)@0 ∈ b on the initial branch)

theorem tableau_complete (S : IntMinScheme Atom) (φ : Proposition Atom)
    (hvalid : <validity S> φ) : <tableau S> φ = .closed := by
  -- contrapositive via openBranch_countermodel
```

Then:
```lean
def intScheme : IntMinScheme Atom := { closurePred := isIntuitionisticallyClosed,
  modelBot := fun _ _ => False, closed_unsat := intClosed_unsatisfiable,
  bot_truth := <vacuous>, modelBot_uc := <trivial> }
def minScheme : IntMinScheme Atom := { closurePred := isMinimallyClosed,
  modelBot := minBranchBotForces, closed_unsat := minClosed_unsatisfiable,
  bot_truth := <from minOpen_no_contradiction>, modelBot_uc := <T(⊥) persistence> }
```
`intTruthLemma`, `minTruthLemma`, the two countermodels and two completeness theorems become
1-line corollaries `:= truthLemma intScheme …` / `:= tableau_complete minScheme …` (or are
deleted and call sites repointed).

---

## 3. Sorry Accounting

| File | Current `sorry` tokens | Declarations |
|---|---|---|
| `Int/Completeness.lean` | 3 | `intTruthLemma` (89), `intuitionisticOpenBranch_countermodel` (98), `intuitionisticTableau_complete` (112) |
| `Min/Completeness.lean` | 3 | `minTruthLemma` (168), `minOpenBranch_countermodel` (179), `minimalTableau_complete` (190) |
| `Int/Soundness.lean` | **0** | green (task 316) |
| `Min/Soundness.lean` | **0** | green (task 316) — `minClosed_unsatisfiable`, `minimalTableau_sound` fully proved |
| `Int`/`Min` `DecisionProcedure.lean` | 0 | green; depend transitively on `*_complete` |

**Total today: 6 completeness sorries.** Note `minOpen_no_contradiction`
(`Min/Completeness.lean:89-140`) is fully PROVED — reuse it as `minScheme.bot_truth`'s engine.

### Task 316 constraint — VERIFIED
Both Soundness files are sorry-free; `minimalTableau_sound` and `intuitionisticTableau_sound`
share `intExpandBranches_closed_unsat`. **316 closed the Soundness sorry. The refactor must
not introduce any Soundness sorry** — and it need not, because soundness is already generic.

### What the refactor unifies
The **two truth-lemma sorries collapse into ONE** `truthLemma S` sorry. Given a proved
`truthLemma`, `openBranch_countermodel` and `tableau_complete` are *derivable generically*
(as the Classical analog demonstrates), so ideally the parametric development carries a
**single** `sorry` (the truth lemma). Conservatively, if the saturation plumbing those two
derivations need is itself part of task 317, the parametric trio carries **at most the 3
obligations of one logic — never more, and never any new Soundness sorry**.

### What stays sorry (handoff to task 317)
`truthLemma S` (the parametric truth lemma). Task 317 (`propositional_tableau_completeness`,
currently `[BLOCKED]`) discharges it ONCE; both logics inherit completeness automatically.

---

## 4. Phasing (green-before-commit)

Place the shared development in a new module
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (Int is already the shared
home: `Min/Completeness.lean` imports `Int/Completeness.lean`). Imports `Int/Soundness.lean`.

| Phase | Work | Build state | Commit gate |
|---|---|---|---|
| **P1 Interface** | Add `Scheme.lean`: `IntMinScheme` structure + `intScheme`/`minScheme` data instances. `closed_unsat`/`bot_truth`/`modelBot_uc` for Int (trivial) and Min (`minOpen_no_contradiction`, T(⊥) persistence). | **GREEN** (no `sorry`; structure + instances only) | commit |
| **P2 Soundness wrap** | Add generic `tableau_sound S`; re-express `intuitionisticTableau_sound`/`minimalTableau_sound` as instances. | **GREEN** (soundness already generic) | commit |
| **P3 Completeness** | Add parametric `truthLemma S` (the ONE `sorry`), `openBranch_countermodel S`, `tableau_complete S`. | **RED only at the single `truthLemma` sorry** — isolated, intended | commit (1 parametric sorry) |
| **P4 DecisionProcedure** | Point `instDecidable{I,M}Valid` at `tableau_complete {int,min}Scheme`; optional generic `decidableValid S`. | **GREEN** (modulo the one inherited sorry) | commit |
| **P5 Delete duplicates + CI** | Delete `minTruthLemma`, `minOpenBranch_countermodel`, `minimalTableau_complete`, Int trio (or keep as 1-line corollaries); run full CI. | **GREEN** save the single sorry | commit |

**Red window:** only P3, and only the body of `truthLemma S`. Stage so each commit either is
fully green or contains exactly the one intended parametric sorry. Run after P5:
`lake build` → `lake exe checkInitImports` → `lake lint` → `lake exe lint-style` →
`lake exe mk_all --module` (new file) → `lake shake --add-public --keep-implied --keep-prefix`.

---

## 5. Risks

1. **Typeclass-instance resolution.** Forcing `closurePred` through `ClosureCondition` would
   misfit (the predicates are composed `Bool` functions; `isMinimallyClosed` deliberately
   bypasses the typeclass). **Mitigation:** keep `closurePred`/`modelBot` as explicit
   `structure` fields; leave `ClosureCondition` untouched. Use plain `def` instances
   (`intScheme`/`minScheme`), not `instance`, to avoid resolution ambiguity on `IntMinScheme`.
2. **`botForces`/`modelBot` threading.** Soundness uses the *validity-supplied* `botForces`
   (so `modelBot` is irrelevant there — no risk). Completeness must *exhibit* `S.modelBot b`;
   the truth lemma's `imp` case needs `S.modelBot_uc` (upward-closure). For Min,
   `minBranchBotForces` upward-closure (T(⊥) propagating along the persistence fixpoint) is
   currently only asserted in a docstring (`Min/Completeness.lean:74-77`), not yet a lemma.
   **Mitigation:** make `modelBot_uc` a scheme field so the obligation is explicit; fold any
   real proof work into the single parametric obligation — do NOT spawn a new standalone sorry.
3. **CI shake/lint.** New `Scheme.lean` must `import Cslib.Init`; the `structure` and every
   field need docstrings (docBlame); `truthLemma`/`tableau_complete` must be `lemma`/`theorem`
   (defLemma); names lowerCamelCase (`intScheme`, not `int_scheme`); run `mk_all --module` for
   the barrel import; `shake` may re-minimize imports since Min currently transitively pulls
   Int/Completeness — verify the import graph after moving shared defs.
4. **Stale docstrings.** DecisionProcedure docstrings claim "4 sorries"; update to reflect the
   unified single parametric obligation during P4/P5 to avoid lint/doc drift.

---

## References
- M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*, Ch. 4 (cited throughout the
  existing modules).
- Reference implementation (fully green): `Cslib/Logics/Propositional/Tableau/Classical/`
  (tasks 363, 376).
