# Research Report: MPL⟨∧,→,⊥,⊤⟩ Completeness over Arbitrary-Point Brouwerian Semilattices (Task 354)

## Executive Summary

Task 354 closes the fourth conservativity step of the MPL fragment tower:

```
MPL⟨→,⊤⟩ ⊂ MPL⟨∧,→,⊤⟩ ⊂ MPL⟨∧,→,⊥,⊤⟩ ⊂ MPL
                                    ^^^^^^^^^^^^^^^^
                                    this step (354)
```

The mathematics is **sound and low-risk**. The route is a direct algebraic mirror of the
existing `hilbertMplConservativeOverConjImp_direct` (in `MplConservativeChain.lean`), with the
single change that `⊥` is interpreted as a **free `bot_val : B`** (a Brouwerian semilattice
with an arbitrary distinguished element) rather than the `OrderBot` least element used by the
IPL tower's `PointedBrouwerian.lean`. I have **prototyped and compiled** the algebraic core
(free-bot evaluator + free-bot embedding lemma + GHA→BrouwerianBot bridge) in a scratch module
that built green. The completeness direction reuses the `PointedBrouwerianCompleteness.lean`
Lindenbaum construction verbatim, **dropping the `OrderBot` instance** and reading `[⊥]` as the
canonical free `bot_val`.

**No mathematical blockers.** **No structural blockers** to the no-touch constraint: all new
declarations go in a NEW file plus an append to `MplConservativeChain.lean`; nothing in
`Algebra.lean`, `Defs.lean`, `SemanticConsequence.lean`, or `Temporal/*` is touched.

## Key Discovery: ConjImpBotMinAxiom = ConjImpAxiom Axioms + Free ⊥

The decisive structural fact (verified by reading `FragmentAxioms.lean` lines 59–74 and
413–428):

`ConjImpBotMinAxiom` has **exactly the same five axiom constructors** as `ConjImpAxiom`:
`implyK`, `implyS`, `andI`, `andE1`, `andE2`. It has **NO `efq` and NO bot-specific axiom**.
By contrast, `ConjImpBotAxiom` (the IPL-tower fragment) adds `efq : ⊥ → φ` (line 277).

Consequence: in `ConjImpBotMin`, the constant `⊥` is **uninterpreted** — no axiom governs it.
Therefore its semantic image must be a free element `bot_val : B` ranging over the whole
algebra, which is **exactly** what `GHAValid` already quantifies over
(`Algebra.lean:126–128`, `AlgEvaluate ... bot_val`, `.bot => bot_val` at line 93). This is the
mathematical justification for "arbitrary distinguished element" semantics: free constant ⇒
universally-quantified `bot_val`.

This also confirms the task framing: the IPL tower's `PointedBrouwerian` uses
`[OrderBot H]` and `bot ↦ ⊥` (least element) to validate `efq` (`PointedBrouwerianCompleteness.lean:115–119`,
`bot_le`); the MPL tower must **drop `OrderBot`** because there is no `efq` to validate.

## Existing Machinery (verified, with quoted signatures)

### The direct MPL→ConjImp route to mirror (`MplConservativeChain.lean`)

```lean
theorem GHAValid_implies_BrouwerianValid_direct {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) (h : GHAValid.{u, u} φ) : BrouwerianValid.{u, u} φ := by
  intro B _ v
  exact (brouwerianEmbeddingLemma v φ hOBF).mpr (h (H := LowerSet B) (LowerSet.Iic ∘ v) ⊥)

theorem hilbertMplConservativeOverConjImp_direct {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) (h : Derivable (@MinPropAxiom Atom) φ) :
    Derivable (@ConjImpAxiom Atom) φ :=
  conjImp_brouwerian_complete hOBF
    (GHAValid_implies_BrouwerianValid_direct hOBF (MPL.hilbert_alg_complete.mp h))

theorem mplAxiom_iff_conjImpAxiom {Atom : Type u} {φ : PL.Proposition Atom}
    (hOBF : φ.IsOrBotFree = true) :
    Derivable (@MinPropAxiom Atom) φ ↔ Derivable (@ConjImpAxiom Atom) φ :=
  ⟨hilbertMplConservativeOverConjImp_direct hOBF, fun ⟨d⟩ =>
    ⟨liftDerivationTree (fun _ hψ => hψ.toMinPropAxiom) d⟩⟩
```

Note the existing direct step is restricted to `IsOrBotFree` (bot disallowed) because
`brouwerianEmbeddingLemma` / `BrouwerianEvaluate` map `bot ↦ ⊤`. Task 354's deliverable must
extend the predicate to `IsOrFree` (bot **allowed**, or excluded), exactly as the IPL tower did
when going from `ConjImpConservative` (or-bot-free) to `ConjImpBotConservative` (or-free).

### Embedding lemmas (`FreeJoinCompletion.lean`)

```lean
theorem iicHimp (a b : B) : LowerSet.Iic (a ⇨ b) = LowerSet.Iic a ⇨ LowerSet.Iic b   -- line 61
theorem brouwerianEmbeddingLemma (v : Atom → B) (φ : Proposition Atom)
    (hφ : φ.IsOrBotFree = true) :
    BrouwerianEvaluate v φ = ⊤ ↔ AlgEvaluate (LowerSet.Iic ∘ v) (⊥ : LowerSet B) φ = ⊤  -- line 129
```

`LowerSet.Iic` preserves `⊓` (`LowerSet.Iic_inf`), `⊤` (`LowerSet.Iic_top`), `⇨` (`iicHimp`),
and is injective (`LowerSet.Iic_injective`). These are exactly the morphism hypotheses required
by `coe_AlgEvaluate_orFree` (`FragmentPredicates.lean:230`), with `f := LowerSet.Iic`,
`b := bot_val`, `b' := LowerSet.Iic bot_val`, `h_bot := rfl`.

### GHA completeness for MPL (`HilbertCompleteness.lean:93`)

```lean
theorem MPL.hilbert_alg_complete {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@MinPropAxiom Atom) φ ↔ GHAValid.{u, u} φ
```

`GHAValid` quantifies over `bot_val` (`Algebra.lean:126`), so it directly supplies validity at
**any** `bot_val`, including `LowerSet.Iic bot_val`. This is the source of the free-bot validity.

### Completeness template to copy (`PointedBrouwerianCompleteness.lean`)

The entire Lindenbaum construction (lines 152–547) for `ConjImpBotAxiom` is the template:
quotient by `ConjImpBotEquiv`, `BrouwerianSemilattice` instance
(`pointedBrouwerianLindenbaumBSL`, line 399), top = `[⊥ → ⊥]`,
`pointedBrouwerianLindenbaumMk_eq_top_iff` (line 472), canonical valuation + truth lemma
(`pointedBrouwerianCanonicalV_spec`, line 509). All helper lemmas
(`hilbertImpIDeriv`, `hilbertCutSingletonDeriv`, `hilbertAndIDeriv`, `assumption_deriv`,
`weakening_deriv`, `Deriv`) are **generic over the axiom predicate** (verified: `Deriv` defined
in `Derivation.lean:122`; witnesses `ConjImpBotMinAxiom.mem_implyK/mem_implyS` exist at
`FragmentAxioms.lean:460/466`).

The **only** structural differences from the `ConjImpBotAxiom` template are:
1. Use `ConjImpBotMinAxiom` everywhere instead of `ConjImpBotAxiom`.
2. **Omit the `OrderBot` instance** (lines 414–433) — there is no `efq` to prove `bot_le`.
3. The truth lemma uses a **free-bot evaluator** with `bot_val = [⊥]` (the canonical class of
   `Proposition.bot`), rather than `PointedBrouwerianEvaluate` which hardwires `bot ↦ ⊥`.

## Verified Prototype (compiled green)

I wrote a scratch module importing `FreeJoinCompletion`, `HilbertCompleteness`,
`PointedBrouwerianCompleteness`, `FragmentAxioms` and compiled it with
`lake build` — **build succeeded (665 jobs)**. The prototype contained:

```lean
/-- Free-bot Brouwerian evaluator: bot ↦ free bot_val, or ↦ ⊤. -/
def BrouwerianBotEvaluate {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H) : PL.Proposition Atom → H
  | .atom x => v x
  | .bot => bot_val
  | .imp a b => BrouwerianBotEvaluate v bot_val a ⇨ BrouwerianBotEvaluate v bot_val b
  | .and a b => BrouwerianBotEvaluate v bot_val a ⊓ BrouwerianBotEvaluate v bot_val b
  | .or _ _ => ⊤

def BrouwerianBotValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (H : Type*) [BrouwerianSemilattice H] (v : Atom → H) (bot_val : H),
    BrouwerianBotEvaluate v bot_val φ = ⊤

/-- Iic commutes with free-bot eval on or-free formulas (the bot case now closes by rfl). -/
theorem iicBrouwerianBotEvaluateEqAlgEvaluate
    (v : Atom → B) (bot_val : B) (φ : Proposition Atom) (hφ : φ.IsOrFree = true) :
    AlgEvaluate (LowerSet.Iic ∘ v) (LowerSet.Iic bot_val) φ =
      LowerSet.Iic (BrouwerianBotEvaluate v bot_val φ)
-- proved by induction; bot case is `rfl`, imp uses (iicHimp _ _).symm, and uses (LowerSet.Iic_inf _ _).symm

/-- Free-bot embedding lemma (or-free). -/
theorem brouwerianBotEmbeddingLemma
    (v : Atom → B) (bot_val : B) (φ : Proposition Atom) (hφ : φ.IsOrFree = true) :
    BrouwerianBotEvaluate v bot_val φ = ⊤ ↔
      AlgEvaluate (LowerSet.Iic ∘ v) (LowerSet.Iic bot_val) φ = ⊤
-- proved via the commutation lemma + LowerSet.Iic_top + LowerSet.Iic_injective

/-- The GHA→BrouwerianBot bridge (mirror of GHAValid_implies_BrouwerianValid_direct). -/
theorem GHAValid_implies_BrouwerianBotValid_direct {Atom : Type u} {φ : PL.Proposition Atom}
    (hOF : φ.IsOrFree = true) (h : GHAValid.{u, u} φ) : BrouwerianBotValid.{u, u} φ := by
  intro B _ v bot_val
  exact (brouwerianBotEmbeddingLemma v bot_val φ hOF).mpr
    (h (H := LowerSet B) (LowerSet.Iic ∘ v) (LowerSet.Iic bot_val))
```

Key correctness points confirmed by the compiler:
- The `bot` case of the commutation lemma closes by `rfl` — `AlgEvaluate ... (LowerSet.Iic bot_val) .bot = LowerSet.Iic bot_val = LowerSet.Iic (BrouwerianBotEvaluate v bot_val .bot)`.
  This is why **plain `LowerSet` works** for the free-bot case and `NonemptyLowerSet` is NOT
  needed: with a free `bot_val`, `LowerSet.Iic bot_val` is just an ordinary element; we never
  need `Iic ⊥ = ⊥`, which was the sole reason `NonemptyLowerSet` existed in the IPL tower.
- Universe handling: declare `{Atom : Type u}` and use `GHAValid.{u, u}` /
  `BrouwerianBotValid.{u, u}` (matching the `MplConservativeChain.lean` pattern).

The scratch file was deleted after verification (it must not appear in the final diff).

## Recommended Deliverable Shape

### File 1 (NEW): `Cslib/Logics/Propositional/Semantics/Algebra/MplPointedConservative.lean`

Holds the free-bot evaluator, its simp lemmas, validity predicate, embedding lemma, and the
`ConjImpBotMin` Lindenbaum completeness. Suggested contents (names indicative):

1. `BrouwerianBotEvaluate` + `BrouwerianBotEvaluate_atom/bot/imp/and/or` simp lemmas
   (mirror `Brouwerian.lean:67–100`, with `bot ↦ bot_val`).
2. `BrouwerianBotValid` (`∀ H [BSL H] v bot_val, ... = ⊤`).
3. `iicBrouwerianBotEvaluateEqAlgEvaluate` + `brouwerianBotEmbeddingLemma` (verified above).
   - Alternative: state the commutation directly via `coe_AlgEvaluate_orFree` (already in
     `FragmentPredicates.lean:230`) with `f := LowerSet.Iic`. Either works; the explicit
     induction shown above is simplest and proven.
4. **Soundness**: `conjImpBotMin_brouwerianBot_axiom_sound`,
   `conjImpBotMin_brouwerianBot_soundness`, `conjImpBotMin_brouwerianBot_soundness_derivable`.
   Copy from `PointedBrouwerianCompleteness.lean:80–150` but: the five axiom cases are identical
   to `BrouwerianCompleteness.lean:72–112` (no efq case to prove). `bot ↦ bot_val` never needs a
   bound, since no axiom mentions `⊥`.
5. **Lindenbaum**: `ConjImpBotMinEquiv`, setoid, quotient algebra, BSL instance, top `[⊥→⊥]`,
   `...Mk_eq_top_iff`, canonical valuation. Copy `PointedBrouwerianCompleteness.lean:152–489`
   **verbatim with `ConjImpBotAxiom → ConjImpBotMinAxiom`**, and **delete the OrderBot block**
   (lines 414–433). The `mem_implyK/mem_implyS` witnesses already exist for `ConjImpBotMinAxiom`.
6. **Truth lemma + completeness**:
   `conjImpBotMinCanonicalV_spec` (or-free; uses `bot_val := mk Proposition.bot`),
   `conjImpBotMin_brouwerianBot_complete : φ.IsOrFree → BrouwerianBotValid φ → Derivable ConjImpBotMinAxiom φ`,
   `conjImpBotMin_brouwerianBot_iff`.
   - The truth lemma instantiates `BrouwerianBotValid` at the Lindenbaum BSL with
     `bot_val = [⊥]`; the `bot` case gives `BrouwerianBotEvaluate canonicalV [⊥] .bot = [⊥] = mk Proposition.bot`,
     which is the needed equality. This is the analogue of
     `pointedBrouwerianCanonicalV_spec` (line 509) but with the free `[⊥]` instead of `⊥`.

### File 2 (APPEND): `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean`

Add, next to the existing direct theorems (after line 159), importing File 1:

```lean
theorem GHAValid_implies_BrouwerianBotValid_direct {Atom : Type u} {φ : PL.Proposition Atom}
    (hOF : φ.IsOrFree = true) (h : GHAValid.{u, u} φ) : BrouwerianBotValid.{u, u} φ
  -- (move here, or keep in File 1 and re-export)

theorem hilbertMplConservativeOverConjImpBot_direct {Atom : Type u} {φ : PL.Proposition Atom}
    (hOF : φ.IsOrFree = true) (h : Derivable (@MinPropAxiom Atom) φ) :
    Derivable (@ConjImpBotMinAxiom Atom) φ :=
  conjImpBotMin_brouwerianBot_complete hOF
    (GHAValid_implies_BrouwerianBotValid_direct hOF (MPL.hilbert_alg_complete.mp h))

theorem mplAxiom_iff_conjImpBotMinAxiom {Atom : Type u} {φ : PL.Proposition Atom}
    (hOF : φ.IsOrFree = true) :
    Derivable (@MinPropAxiom Atom) φ ↔ Derivable (@ConjImpBotMinAxiom Atom) φ :=
  ⟨hilbertMplConservativeOverConjImpBot_direct hOF, fun ⟨d⟩ =>
    ⟨liftDerivationTree (fun _ hψ => hψ.toMinPropAxiom) d⟩⟩
```

The backward direction of the biconditional uses the task-353 lemma
`ConjImpBotMinAxiom.toMinPropAxiom` (`FragmentAxioms.lean:446`) via `liftDerivationTree`
(already imported/used in `MplConservativeChain.lean`).

**Recommendation**: put the new evaluator/embedding/completeness in **File 1 (new)** to keep
`MplConservativeChain.lean` focused on the chain theorems, and append only the two chain
theorems + biconditional to `MplConservativeChain.lean`. If the implementer prefers minimal
file churn, everything can go in File 1 and `MplConservativeChain.lean` is left untouched; but
the task asks for `hilbertMplConservativeOverConjImpBot_direct` "analogous to … in
`MplConservativeChain.lean`", so co-locating the chain theorems there is the better fit.

### `attribute [-instance] BrouwerianSemilattice.toHilbertAlgebra` caveat

`MplConservativeChain.lean:121` suppresses `BrouwerianSemilattice.toHilbertAlgebra` around the
`GHAValid_implies_BrouwerianValid_direct` block to avoid a `Preorder` diamond on `LowerSet.Iic`,
then re-enables it (line 160). The new `hilbertMplConservativeOverConjImpBot_direct` uses the
same `LowerSet.Iic` embedding through `GHAValid_implies_BrouwerianBotValid_direct`, so the
implementer should place the new GHA-bridge theorem **inside the same suppressed region** (or
add its own `attribute [-instance] ... / attribute [instance] ...` bracket) to avoid the same
diamond. Verify with a scoped build; if the diamond does not reappear (the prototype built fine
without suppression, because it did not import `ImpConservative`), no suppression is needed —
**but the chain file does import `ImpConservative` transitively**, so keep the bracket.

## Barrel / mk_all

A new file requires updating the `Cslib.lean` barrel. The block already lists
(lines 441, 455, 457, 458):
`ConjImpBotConservative`, `MplConservativeChain`, `PointedBrouwerian`,
`PointedBrouwerianCompleteness`. Run `lake exe mk_all --module` after adding File 1, or add the
`public import Cslib.Logics.Propositional.Semantics.Algebra.MplPointedConservative` line
manually in the alphabetically-appropriate position. This is the only barrel action needed.

## No-Touch Constraint Compliance (FLAGGED)

The task forbids modifying `Algebra.lean`, `Defs.lean`, `SemanticConsequence.lean`, and any
`Temporal/*` file (in-flight task-343 work). The recommended plan:
- **ADDS** one new file (`MplPointedConservative.lean`).
- **APPENDS** to `MplConservativeChain.lean` (allowed; the task explicitly permits this).
- **UPDATES** `Cslib.lean` barrel (a generated import list, not in the forbidden set).
- Touches **none** of the forbidden files. `Algebra.lean`'s `AlgEvaluate`/`GHAValid` are
  **consumed read-only**. `FragmentAxioms.lean` (task-353) and the algebra modules are
  read-only dependencies.

This satisfies the constraint with no edits to in-flight files.

## Mathematical Risk Assessment

**Is MPL complete w.r.t. Brouwerian semilattices with an arbitrary point for or-free formulas?**
**Yes.** Argument chain (all links verified to exist and type-check):

1. `Derivable MinPropAxiom φ ↔ GHAValid φ` — `MPL.hilbert_alg_complete` (HilbertCompleteness.lean:93).
   `GHAValid` quantifies over `bot_val`, so the canonical bottom is already free at the GHA level.
2. `GHAValid φ → BrouwerianBotValid φ` (or-free) — via `brouwerianBotEmbeddingLemma`, **compiled**.
   Instantiate `GHAValid` at `LowerSet B` with `bot_val := LowerSet.Iic bot_val`; `LowerSet B`
   is a Heyting algebra (hence GHA), so validity holds; the embedding lemma transfers it to the
   free-bot BSL evaluator on `B`.
3. `BrouwerianBotValid φ → Derivable ConjImpBotMinAxiom φ` (or-free) — via the `ConjImpBotMin`
   Lindenbaum BSL with `bot_val = [⊥]`. The Lindenbaum BSL exists (axioms identical to
   `ConjImpAxiom` ⇒ same `le_himp_iff`), `[⊥]` is a legitimate free element, and the truth
   lemma closes the `bot` case as `[⊥]` (mirrors `pointedBrouwerianCanonicalV_spec`).

The GHA canonical model's `canonicalBotVal` (`HilbertLindenbaum.lean:596`) confirms the route:
the MPL canonical model carries a distinguished free bottom that is NOT a least element (MPL has
no efq), which is precisely the "arbitrary point" the task asks for. The IPL tower differs ONLY
in that its canonical bottom IS the least element (efq present) — the "sole divergence: free vs.
least ⊥" stated in the task.

**Risk level: LOW.** The algebraic core is compiled. The completeness direction is a mechanical
copy of an existing, building proof (`PointedBrouwerianCompleteness.lean`) with `OrderBot`
removed and `⊥` replaced by the free `[⊥]`. No new mathematics is introduced.

### Minor implementation watch-items
- The `bot` case of `BrouwerianBotEvaluate` simp lemma is needed for the truth-lemma `bot`
  case; include `@[simp] BrouwerianBotEvaluate_bot` returning `bot_val`.
- In the truth lemma, `bot_val` is `conjImpBotMinLindenbaumMk Proposition.bot`; ensure the
  `bot` case rewrites `BrouwerianBotEvaluate canonicalV (mk ⊥) .bot = mk ⊥` (definitional).
- Keep the `attribute [-instance] BrouwerianSemilattice.toHilbertAlgebra` bracket around the
  chain theorem if co-locating in `MplConservativeChain.lean` (diamond avoidance).
- Lint: all new `def`s/`theorem`s need docstrings (docBlame); Prop-valued must be `theorem`/`lemma`;
  lowerCamelCase names; verify any `@[simp]` LHS (simpNF). Instances need namespace wrapping.

## Verification Approach

Scoped build is the green gate (full `lake build`/`lake test` has 11 PRE-EXISTING Temporal
failures unrelated to this task — do not attempt to fix them):

```bash
lake build Cslib.Logics.Propositional.Semantics.Algebra.MplPointedConservative \
           Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain
```

The propositional algebra subtree was confirmed green at research time
(`PointedBrouwerianCompleteness` + `MplConservativeChain` + `FragmentAxioms` built, 676 jobs).
After adding the new file, also run `lake exe mk_all --module` and a scoped `lake lint` on the
new module.

## File Reference Index (absolute paths)

- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` — APPEND chain theorems here
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/PointedBrouwerianCompleteness.lean` — completeness TEMPLATE (copy, drop OrderBot)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/PointedBrouwerian.lean` — evaluator template (lines 67–73 OrderBot use; lines 22, 67 are the points the task flags)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/Brouwerian.lean` — `BrouwerianEvaluate` template (bot↦⊤)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/FreeJoinCompletion.lean` — `iicHimp`, `brouwerianEmbeddingLemma`, `LowerSet.Iic` lemmas
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` — `IsOrFree`, `coe_AlgEvaluate_orFree`, substitution closure
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` — `AlgEvaluate_botFree_independent` (line 49)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/ConjImpBotConservative.lean` — IPL-tower analogue (the structural sibling; uses NonemptyLowerSet)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/NonemptyLowerSet.lean` — bot-preserving embedding (NOT needed for free-bot, explained above)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra.lean` — `AlgEvaluate`/`GHAValid` (READ-ONLY, do not edit)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` — `MPL.hilbert_alg_complete` (line 93)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean` — `canonicalBotVal` (line 596)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` — `ConjImpBotMinAxiom` (line 413), `toMinPropAxiom` (446), `mem_implyK/S` (460/466), DT instance (535)
- `/home/benjamin/Projects/cslib/Cslib.lean` — barrel (lines 441, 455–458)
