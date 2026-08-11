# Research Report: Propositional Coverage Gaps and the Ordering Overclaim

**Task**: 618 — Close remaining coverage gaps in the propositional metatheory; correct the
docstring that overclaims a result the tree does not prove.
**Type**: cslib
**Session**: sess_1786405794_f0204e_618
**Date**: 2026-08-10

---

## Executive Summary

All five Part A docstring defects were reproduced at the cited lines. Parts B, C, D were
measured against the actual source rather than accepted from the task description. Four
findings materially change what should be planned:

1. **A4's premise is half wrong.** `CslibTests/TableauConformance.lean:34-35` says the needed
   completeness theorems "do not exist yet for either calculus". That is false for the
   intuitionistic calculus but **still true for the temporal one** — `temporalTableau_complete`
   does not exist as a declaration anywhere; it appears only as an aspirational name in
   `Temporal/Tableau/Completeness.lean`'s *Blocked Obligations* list (`:122`). A blanket
   re-tensing would replace one false statement with another. A4 must be a **split** re-tensing.

2. **A1 has three defects, not one.** Beyond the unproved "strictly", the docstring says "the
   **five** Hilbert systems" while its own display block shows a **three**-node chain and the
   theorem proves a single implication. See §A1.

3. **A sixth overclaim exists that the task did not list** (call it A6):
   `SequentCalculus/LJ/Basic.lean:78-79` claims structural metatheory including "cut elimination,
   subformula property" is "proved once generically over `T`". Cut elimination and the subformula
   property are **not** generic over `T` — both are written concretely at `IPL`. This is the same
   class of defect as A1-A5 and is the exact claim Part C would be relying on.

4. **Part C's central premise is false as stated, but its conclusion survives** — and Part D2's
   difficulty is materially overstated. See §C1 and §D2.

The subsystem is genuinely clean: no `sorry` occurs anywhere under
`Cslib/Logics/Propositional/` (all grep hits are docstring prose), and
`intuitionisticTableau_decides` verifies with axioms `{propext, Classical.choice, Quot.sound}`.

---

## Part A — Correctness of the Record

All five reproduced. Details and required corrections below.

### A1 — `Semantics/Algebra/ConservativeChain.lean:140` (three defects)

Current text:

```
/-- **Derivability subsumption chain**: the five Hilbert systems are strictly ordered
by derivability. For any formula `φ`:
```
Derivable ImpAxiom φ
  → Derivable IntPropAxiom φ
  → Derivable PropositionalAxiom φ
```
```

- **"strictly"** — unsupported. An exhaustive scan for strictness/properness/separation
  vocabulary across the whole propositional tree returns exactly one hit: this line itself. The
  three other hits (`Tableau/Intuitionistic/Scheme.lean:88,1200,1408`) are unrelated uses of
  "strictly stronger" about invariants. **Nothing in the tree establishes MPL ≠ IPL ≠ CPL.**
- **"five"** — the display block has three nodes (`ImpAxiom`, `IntPropAxiom`,
  `PropositionalAxiom`) and `derivability_subsumption_chain` (`:148`) is a single implication
  `Derivable ImpAxiom φ → Derivable PropositionalAxiom φ`. There is no five-node chain stated
  anywhere in the file. Fixing only "strictly" leaves a second false numeral standing.
- **Chain identity** — the two immediately preceding theorems (`derivableMinOfDerivableInt`
  `:125`, `derivableIntOfDerivableProp` `:135`) are about MPL → IPL → CPL, while the chain
  theorem routes Imp → Int → Prop via `derivableImpOfDerivableInt`
  (`Semantics/Algebra/FragmentConservativityInstances.lean:138`). The docstring's "the five
  Hilbert systems" reads as if it covers both, which it does not.

**Recommended correction**: replace "the five Hilbert systems are strictly ordered by
derivability" with a statement scoped to what is proved — e.g. "derivability is **ordered**
along the fragment-to-full chain: the three displayed systems subsume one another in the
direction shown". Do **not** assert a count that the display block contradicts. Per the task,
apply this regardless of whether D2 is undertaken.

### A2 — `Tableau/Classical/DecisionProcedure.lean:23`

Reproduced. Line 23 lists `instDecidableDerivable` under **Main Results**. Lines 92-94 of the
same file explicitly decline to define it:

```lean
-- Note: `instDecidableDerivablePropositionalAxiom` (Boolean enumeration) already exists
-- in `Metalogic/StrongCompleteness.lean`. We do not define a duplicate here.
```

Also note lines 33-34 of the same header describe "The `Derivable PropositionalAxiom φ` instance
uses `prop_completeness_iff_tautology`" — that sentence describes the same non-existent instance
and should be removed or re-pointed together with line 23. **Fixing only line 23 leaves a
dangling description.**

### A3 — `Tableau/Intuitionistic/DecisionProcedure.lean:62`

Reproduced and confirmed: grep for `instDecidableDerivableIntPropAxiom` and `instDecidableIValid`
across all of `Cslib/` and `CslibTests/`, excluding `Cslib/Logics/Propositional/`, returns
**zero** hits. The claim "feeds the modal/temporal/bimodal extensions" is false today.

**Recommended correction**: state the role as aspirational/available rather than actual — e.g.
"Canonical extension-facing instance; intended as the entry point for downstream modal/temporal
extensions (no external consumers at present)." Dropping the sentence entirely also works; the
"canonical registered instance" role is already stated on the preceding line.

### A4 — `CslibTests/TableauConformance.lean:34-35` (**premise correction**)

Current text: "Proof-term assertions (the `ModalFrameSeparation.lean` idiom) are unavailable here
because the completeness theorems the driver would need do not exist yet **for either calculus**."

Verified per calculus:

| Calculus | Theorem | Status |
|---|---|---|
| Intuitionistic | `intuitionisticTableau_complete` | **Exists**, `Intuitionistic/Completeness.lean:178` |
| Intuitionistic | `intuitionisticTableau_decides` | **Exists**, `Intuitionistic/DecisionProcedure.lean:97`, verified axioms `{propext, Classical.choice, Quot.sound}` |
| Temporal | `temporalTableau_complete` | **Does not exist.** `grep "theorem temporalTableau_complete"` returns nothing; the name appears only at `Temporal/Tableau/Completeness.lean:122` as *"blocked by (4)"*, with `:138` recommending "a dedicated research pass before further planning" |

**Recommended correction**: split the sentence. The intuitionistic clause moves to past tense
("were unavailable when this file was written; `intuitionisticTableau_complete` /
`intuitionisticTableau_decides` now exist and are sorry-free"), while the temporal clause stays
in the present tense and should cite `Temporal/Tableau/Completeness.lean`'s blocked-obligation
item 5 as the reason. Note the `#eval` mechanism the file uses remains justified for **both**
rows regardless, because the kernel-reduction stall is independent of theorem availability.

### A5 — `Tableau/Minimal/DecisionProcedure.lean:119`

Reproduced. Docstring says "`MValid φ` is decidable"; `instDecidableMValid` (`:123`) is stated at
`MValid.{_, 0} φ`. Add the universe pin. The file already explains the pin thoroughly at
`:131-139` ("Universe Invariance of `MValid`"), so the docstring fix is a one-token change plus
optionally a cross-reference to that section.

### A6 — NEW: `SequentCalculus/LJ/Basic.lean:78-79` (not in the task description)

```
Structural metatheory (`height`, `mono`, `CutFree`, cut elimination, subformula property)
is proved once generically over `T`.
```

Verified genericity, declaration by declaration:

| Item | Generic over `T`? | Evidence |
|---|---|---|
| `SeqProof.height` | **Yes** | `Basic.lean:156`, `{T : Theory Atom}` binder |
| `SeqProof.mono` | **Yes** | `Basic.lean:180` |
| `SeqProof.CutFree` | **Yes** | `Basic.lean:221` |
| `SeqProof.IsBotRuleFree` | **Yes** | `Basic.lean:237` |
| `SeqProof.formulas` | **Yes** | `LJ/SubformulaProperty.lean:50` |
| **cut elimination** | **No** | every declaration in `LJ/CutElimination.lean` is at `LJProof` = `SeqProof IPL`; no `{T}` binder appears in the file (see §C1) |
| **subformula property** | **No** | `ljCutFreeSubformulaProp` `:82`, `CutFreeLJProof.subformula_property` `:259`, `LJProof.subformula_property` `:274` — all at `IPL` |

Only the *formula-collection function* is generic; the subformula **property** is not. This
docstring should be corrected in the same pass as A1-A5 — and, importantly, it is the claim a
naive reading of Part C would have relied on.

---

## Part B — Cheap Wins

### B1 — LJ cut-free completeness (G10). Confirmed near-exact template match.

`LK/CutFreeCompleteness.lean` is a 50-line module with two theorems. The LJ analogue is a
direct transcription:

| LK ingredient | LJ counterpart | Location |
|---|---|---|
| `lk_iff_tautology` | `lj_iff_ivalid` | `LJ/Completeness.lean:288` |
| `LKProof.cutElim` | `LJProof.cutElim` | `LJ/CutElimination.lean:678` |
| `CutFreeLKProof` | `CutFreeLJProof` | `LJ/Basic.lean:256` |

Both LJ ingredients have exactly the shape the composition needs:

```lean
theorem lj_iff_ivalid {φ : Proposition Atom} :
    IValid.{u, u} φ ↔ Nonempty (LJProof (∅ ⊢ φ))

theorem LJProof.cutElim {seq : @Sequent Atom} (d : LJProof seq) :
    Nonempty (CutFreeLJProof seq)
```

Target `SequentCalculus/LJ/CutFreeCompleteness.lean` with `ljCutFreeCompleteness` and
`ljCutFreeIffTautology` — the latter better named `ljCutFreeIffIValid`, since the LJ side is
intuitionistic validity, not tautologyhood. **Only difference from LK**: `lj_iff_ivalid` carries
an explicit universe pin `IValid.{u, u}`; the LK version does not. Carry the pin through the
statement rather than trying to erase it.

Add the new module to `SequentCalculus/LJ.lean`'s import list (currently 6 public imports; LK
already has 7 and includes its own `CutFreeCompleteness`).

**Difficulty: very low.** Estimated ~50 lines mirroring the LK file.

### B2 — Public general split-interpolation (G5). Confirmed: no new proof needed.

Both cores are `private lemma` and both are already fully general over arbitrary partitions:

```lean
private lemma maeharaCore {seq : LKSequent Atom} (d : LKProof seq) (hcf : CutFree d) :
    ∀ Γ₁ Γ₂ Δ₁ Δ₂ : Finset (Proposition Atom),
      seq.ant = Γ₁ ∪ Γ₂ → seq.suc = Δ₁ ∪ Δ₂ → ∃ I, ...        -- LK/Interpolation.lean:62

private lemma ljMaeharaCore {seq : @Sequent Atom} (d : LJProof seq) (hcf : LJCutFree d) :
    ∀ Γ₁ Γ₂ : Finset (Proposition Atom),
      seq.1 = Γ₁ ∪ Γ₂ → ∃ I, ...                              -- LJ/Interpolation.lean:68
```

The only public forms are the empty-context implication specialisations
(`LKProof.interpolation` `:863`, `LJProof.interpolation` `:560`).

**The one real decision is API shape.** The cores take an unbundled pair `(d, hcf)`, whereas the
rest of the public surface uses the bundled subtype (`CutFreeLKProof`/`CutFreeLJProof`, both
defined as `{ d // CutFree d }`). Recommendation: expose the bundled form for consistency with
`lkCutFreeCompleteness` and `CutFreeLJProof.subformula_property`, i.e.

```lean
theorem LKProof.splitInterpolation {seq} (d : CutFreeLKProof seq) (Γ₁ Γ₂ Δ₁ Δ₂ : Finset _)
    (hant : seq.ant = Γ₁ ∪ Γ₂) (hsuc : seq.suc = Δ₁ ∪ Δ₂) : ∃ I, ...
  := maeharaCore d.1 d.2 Γ₁ Γ₂ Δ₁ Δ₂ hant hsuc
```

This keeps `maeharaCore` private and adds a thin public wrapper, rather than un-privatising the
core (which would expose an internal induction shape as API). **Difficulty: very low**, but it is
an API-surface decision that should be confirmed rather than made silently.

### B3 — LM decidability (G4). Low, but not zero — four helpers need generalising.

Ingredients confirmed present:

- `lm_iff_mvalid` — `LM/Completeness.lean:304` (the LJ-analogous biconditional)
- `instDecidableMValid` — `Minimal/DecisionProcedure.lean:123`
- `mvalid_universe_invariant` — `Minimal/DecisionProcedure.lean:131ff`
- `instDecidableLJDerivable` — `LJ/Decidability.lean:197`, a direct structural template

**Correction to the task's estimate**: `listToImp`/`ctxToImp` are reusable as claimed, but the
four *deduction-theorem* helpers are **LJ-specific**, not generic:

| Helper | Line | Uses |
|---|---|---|
| `ljListDeductionFwd` | `LJ/Decidability.lean:91` | `impR` |
| `ljProofDeductionFwd` | `:112` | — |
| `ljListDeductionBwd` | `:130` | `impL`, `ax`, `mono` |
| `ljProofDeductionBwd` | `:170` | — |

Good news: **none of them touch the gated `botL` constructor.** Every rule they use (`ax`,
`impR`, `impL`, `weakL`, `mono`) is in the ungated ten-rule minimal base of `SeqProof`
(`Basic.lean:93-144`). So generalising them from `LJProof` to `SeqProof T` is a mechanical
binder change with no proof obligations — strictly easier than the Part C generalisation, and
worth doing as `seqListDeductionFwd/Bwd` etc. so B3 and C1 share one generalisation rather than
duplicating.

**Coordination**: task **614** (`computable_ctxtoimp_context_decidability`) is live and currently
`[researching]`. `ctxToImp` is `noncomputable` today (`LJ/Decidability.lean:82`, via
`Finset.toList`), which is what forces `noncomputable instance instDecidableLJDerivable`. Per the
task description, build B3 on the computable route if 614 lands first. **Recommendation**:
sequence B3 *after* 614, or write B3 against `ctxToImp` as it stands and accept the
`noncomputable` taint with an explicit note — do not block on 614.

---

## Part C — LM Parity

### Structural finding confirmed

`SequentCalculus/LM.lean` imports exactly `LM.Basic`, `LM.Soundness`, `LM.Completeness`, against
LJ's 6 and LK's 7 module imports. Missing for LM: `CutElimination`, `SubformulaProperty`,
`Interpolation`, `Decidability`, `CutFreeCompleteness`.

The task's note that LM soundness is *strictly more general* than LJ's is confirmed and is
load-bearing (see §D2):

```lean
theorem SeqProofMinimal.sound {seq} (d : SeqProofMinimal seq) :
    ∀ {World} [Preorder World] (v : World → Atom → Prop) (bf : World → Prop) ... -- LM/Soundness.lean:61
```

`bf` (bot-forcing) is an arbitrary upward-closed predicate, where `IValid` fixes
`botForces = fun _ => False` (`Semantics/Kripke.lean:26,28`).

### C1 — LM cut elimination: premise false, conclusion survives

**The task's claim that `ljCutAdmissibility` "is already written over `SeqProof T` GENERICALLY"
is false.** Measured directly:

- No declaration in `LJ/CutElimination.lean` carries a `{T : Theory Atom}` binder. The file's
  only `variable` line is `{Atom : Type u} [DecidableEq Atom]` (`:54`).
- `LJProof` occurs 56 times in the file; `SeqProof` occurs 15 times, and those are almost all
  qualified projections (`SeqProof.height`, `SeqProof.mono`, `SeqProof.CutFree`) rather than the
  proof type itself.
- Everything is at `IPL`: `LJCutIH` `:99`, `ljCutAdmPrincipalAndR` `:119`, `ljCutAdmPrincipalOrR`
  `:230`, `ljCutAdmPrincipalImpR` `:354`, `ljCutAdmLeft` `:467`, `ljCutAdmRight` `:549`,
  `ljCutAdmissibility` `:659`, `LJProof.cutElim` `:678`.

**However, the generalisation route is sound, and the tree contains a working precedent for the
one hard part.** The only obstacle to abstracting `T` is the gated constructor

```lean
| botL (Γ : Ctx Atom) (C : Proposition Atom) [IsIntuitionistic T]
    (_ : (⊥ : Proposition Atom) ∈ Γ) : SeqProof T (Γ ⊢ C)     -- Basic.lean:99
```

which must be **reconstructed** (not merely read) in five places in `CutElimination.lean`
(`:136-137`, `:248-249`, `:369-370`, `:477-478`, `:561-567`). `SeqProof.mono` — generic over `T`
and facing exactly this problem — already solves it, and `Basic.lean:178-179` documents the
idiom explicitly ("The gated `botL` arm rebinds its stored `[IsIntuitionistic T]` instance via
`letI` before reconstruction"):

```lean
| _, @SeqProof.botL _ _ _ _ _ inst hbot, Γ', hL =>
    letI := inst
    botL Γ' _ (hL hbot)                                        -- Basic.lean:184-186
```

**Measurement verdict**: generalisation is the right route and is mechanical rather than
mathematical. The work is:

1. Generalise `LJCutFree`/`CutFreeLJProof` to `SeqProof.CutFree`-based `CutFreeSeqProof T`
   (`LJCutFree` is already just a `@[reducible]` re-export of the generic `SeqProof.CutFree` at
   `IPL`, `Basic.lean:252` — so this is a re-export inversion, not a redefinition).
2. Add `{T : Theory Atom}` to the seven `ljCutAdm*` declarations plus `LJCutIH`.
3. Convert the five `.botL` match arms to the `@SeqProof.botL ... inst ...` + `letI := inst` form.
4. Re-export at `IPL` (preserving `LJProof.cutElim`'s current signature so no downstream call
   site breaks) and instantiate at `MPL` for LM.
5. `decreasing_by` currently reads `simp [SeqProof.height, LJProof.height]` (`:650`);
   `LJProof.height` is an `IPL` re-export and may need dropping under generalisation. **This is
   the single most likely place for the mechanical port to break** — flag it for the plan.

**Bonus**: this simultaneously discharges A6's overclaim by making it true.

**Risk**: the file is 715 lines with `termination_by`/`decreasing_by` on nested well-founded
recursions. A binder change that perturbs elaboration order can break termination checking in
ways that are tedious to diagnose. Recommend phasing C1 as its own dispatch with a scoped
`lake build Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination` gate before touching LM.

### C2 — LM subformula property

Task's claim **confirmed**: `SeqProof.formulas` (`LJ/SubformulaProperty.lean:50`) is genuinely
generic over `T`, including a correct `@SeqProof.botL _ _ _ Γ C _ _` arm. But the *property*
theorems (`ljCutFreeSubformulaProp` `:82`, `CutFreeLJProof.subformula_property` `:259`,
`LJProof.subformula_property` `:274`) are at `IPL` and need the same treatment as C1. Depends on
C1 (it consumes `CutFreeLJProof`). Same generalise-then-instantiate route.

### C3 — LM Craig interpolation

`ljMaeharaCore` and `ljCraigInterpolation` (`LJ/Interpolation.lean:68`, `:521`) are at `IPL`.
Depends on C1. Note the interaction with **B2**: if B2 exposes a public bundled split-form first,
C3 should generalise that same wrapper rather than introducing a second shape. **Sequence B2
before C3.**

---

## Part D — Decisions

### D1 — or-imp fragment completeness (G7)

**Coverage confirmed**: orImp is the only one of the eight fragment axiom systems with zero
completeness theorem.

| Fragment | Completeness theorem |
|---|---|
| `ImpAxiom` | `imp_hilbert_completeness` (`Algebra/HilbertAlgCompleteness.lean:475`) |
| `ConjImpAxiom` | `conjImp_brouwerian_completeness` (`Algebra/BrouwerianCompleteness.lean:155`) |
| **`OrImpAxiom`** | **none** |
| `ConjImpBotAxiom` | `conjImpBot_pointedBrouwerian_completeness` (`Algebra/PointedBrouwerianCompleteness.lean:149`) |
| `ConjImpBotMinAxiom` | `conjImpBotMin_brouwerianBot_completeness` (`Algebra/MplPointedConservative.lean:136`) |
| `ClassicalImpAxiom` | `classicalImp_completeness` (`Metalogic/ClassicalImpCompleteness.lean:363`) |
| `ClassicalConjImpAxiom` | `classicalConjImp_completeness` (`Metalogic/ClassicalConjImpCompleteness.lean:441`) |
| `ClassicalConjImpBotAxiom` | `classicalConjImpBot_completeness` (`Metalogic/ClassicalConjImpBotCompleteness.lean:459`) |

Note the four intuitionistic fragments prove completeness in `Semantics/Algebra/` against
fragment-matched *algebraic* semantics; the three classical ones prove it in `Metalogic/` against
Boolean semantics. So "the fragment completeness theorem" is not one uniform shape already.

**The task's difficulty warning is correct, and it separates into two genuinely different
deliverables.** The reason the four intuitionistic routes do not accommodate disjunction is
structural, not incidental: their Lindenbaum algebras are Brouwerian/Hilbert algebras in which
`→` is the residual of `∧`. The ⟨∨,→,⊤⟩ signature has no `∧` at all, so there is no meet for `→`
to residuate against, and the standard Lindenbaum construction has nothing to build on.

**D1-relative (cheap, recommend in scope)**: state completeness for `OrImpAxiom` against IPL's
own semantics restricted to and-bot-free formulas. This is a short composition, because the
conservativity biconditional already exists:

```lean
theorem hilbertIplConservativeOverOrImp_iff {Atom} {φ} (hABF : φ.IsAndBotFree = true) :
    Derivable (@IntPropAxiom Atom) φ ↔ Derivable (@OrImpAxiom Atom) φ
                              -- Algebra/FragmentConservativityInstances.lean:197
```

Compose the `.mp` direction with any existing IPL completeness theorem
(`IPL.hilbert_alg_completeness`, `Algebra/HilbertCompleteness.lean`, or the Kripke route via
`lj_iff_ivalid`) to get `IValid φ → Derivable OrImpAxiom φ` for and-bot-free `φ`. **Estimated
under 10 lines.**

**D1-absolute (expensive, recommend OUT of scope)**: completeness against a fragment-matched
algebraic semantics for ⟨∨,→,⊤⟩, parallel in character to the other four intuitionistic
fragments. This requires first *choosing and defining* an algebra class for the
implication-disjunction fragment — new definitional infrastructure, not just a new proof — and
the algebraic treatment of this particular fragment is known to be delicate. **This warrants its
own research pass and its own task.** I did not attempt to settle the algebraic question here and
recommend against planning it blind.

**Recommendation**: deliver D1-relative under this task, with a docstring that states plainly
that it is completeness *relative to IPL semantics on the and-bot-free sublanguage*, not the
fragment-matched algebraic completeness the other four have — so this does not become the next
overclaim. Spawn D1-absolute as a separate research task.

### D2 — Separation theorems: **materially cheaper than the task assumes**

The task frames D2 as "REAL NEW MATHEMATICS" and worries that the natural route (`decide` on the
tableau) is blocked by the `WellFounded.fix` kernel stall. **Both concerns are overstated,
because the `decide` route is not the natural route and the tree already contains the pattern
that replaces it.**

`CslibTests/ModalFrameSeparation.lean` establishes exactly this kind of separation (S5 vs 5/KB5)
and explicitly does **not** use `decide` — it hits the same `WellFounded.fix` stall and routes
around it with hand-built semantic countermodels ported as named theorems
(`boxImp_s5Valid`, `boxImp_not_fiveValid`, `boxImp_not_kb5Valid` in `FrameSoundness.lean`).
There is a working in-tree precedent for the "semantic argument instead" option the task
hypothesised, so no `#eval`-evidence promotion is needed.

Applying it here:

**MPL ⊊ IPL — cheap.** Separating formula `⊥ → p`.
- IPL side: derivable (ex falso is an `IntPropAxiom`).
- MPL side: non-derivable via contraposition on `SeqProofMinimal.sound` /
  `MPL.hilbert_alg_completeness`. The countermodel is the one-point model `World := Unit`,
  `v _ _ := False`, `bf _ := True`. Both upward-closure obligations are trivial on `Unit`. Then
  `IForces ⊥` holds and `IForces p` fails, so `IForces (⊥ → p)` fails, so `¬ MValid (⊥ → p)`.
- This is cheap **precisely because** LM soundness quantifies over arbitrary upward-closed `bf`
  (`LM/Soundness.lean:61`) rather than fixing `bf = fun _ => False`. The generality the review
  flagged as "strictly more general than LJ's" is the exact tool that makes this near-free.
  Estimate: ~15-25 lines.

**IPL ⊊ CPL — tractable.** Separating formula `p ∨ ¬p`.
- CPL side: `Tautology (p ∨ ¬p)`, then CPL completeness.
- IPL side: `¬ IValid (p ∨ ¬p)` via the standard two-point Kripke chain (`World := Bool` with
  `false ≤ true`, `v w p := (w = true)`, `botForces := fun _ => False`); at `false`, neither `p`
  nor `p → ⊥` is forced. Then contrapose intuitionistic soundness.
- Estimate: ~30-50 lines (the two-point preorder instance is the bulk).

**Recommendation**: D2 is in reach and I recommend **admitting the two separations above as a
follow-up task, not folding them into this one.** Rationale: they are new mathematical content
with their own countermodel infrastructure, and this task is otherwise cleanup plus mechanical
generalisation — mixing them makes the diff hard to review. But the plan should record that D2 is
a ~1-phase task rather than an open research problem, since that changes whether it is worth
scheduling.

**Important**: even with both separations landed, they would establish MPL ⊊ IPL ⊊ CPL — which is
**not** the chain A1's docstring displays (Imp → Int → Prop). Strictness for the *displayed*
chain additionally needs `ImpAxiom ⊊ IntPropAxiom`, which is a different and less obvious
separation (the fragment axioms range over the full `Proposition` language, so the separating
formula cannot simply be one outside the ⟨→,⊤⟩ signature). **So A1's "strictly" must be corrected
now and must not be reinstated on the strength of D2 alone.**

---

## Also Recorded — G6 and G9

**G6 (CPL Hilbert decidability needs `[Fintype Atom]`)**: confirmed as a real asymmetry. The
tableau route to lifting it is real — `instDecidableTautologyTableau`
(`Tableau/Classical/DecisionProcedure.lean:81`) already requires only `[DecidableEq Atom]
[Hashable Atom]`, and its own docstring at `:79-80` notes this. Composing it with
`prop_completeness_iff_tautology` would give a `Fintype`-free
`Decidable (Derivable PropositionalAxiom φ)`. **I agree with the task that this is a judgment
call and not required here** — but note it is nearly as cheap as B1, and if taken it should be
done *together with* A2, since A2 is deleting the docstring entry for exactly the instance G6
would create. **Recommend: decide A2 and G6 as one question.** If G6 is taken, A2 becomes "make
the docstring true by defining the instance" rather than "delete the line". The task instructs
A2 as a deletion; I flag the coupling rather than overriding it.

**G9 (no direct ND soundness/completeness)**: confirmed — reachable only by composing
`hilbert_iff_nd_*` (`NaturalDeduction/Equivalence.lean:448,456,464`) with Hilbert-side results.
Agree this is architectural and fine. **Recommend a module-docstring note** in
`NaturalDeduction/Equivalence.lean` recording it as deliberate, since undocumented deliberate
absences are what generate future false "missing coverage" findings. Low cost, and it is in the
same spirit as the rest of Part A.

---

## Recommended Scope and Sequencing

Part A is independent of everything else and should ship first as its own commit — it is
correctness of the record and, per the task, must not wait on Parts B-D.

| Phase | Content | Difficulty | Depends on |
|---|---|---|---|
| 1 | A1-A5 + **A6** (new) + G9 note | trivial | — |
| 2 | B1 (LJ cut-free completeness) | very low | — |
| 3 | B2 (public split interpolation, bundled shape) | very low | — |
| 4 | C1 (generalise cut elimination to `T`; instantiate LM) | **medium-high** | — |
| 5 | C2 (LM subformula property) | low | 4 |
| 6 | C3 (LM interpolation) | low-medium | 3, 4 |
| 7 | B3 (LM decidability) | low | 4 (shares helper generalisation), coordinate w/ 614 |
| 8 | D1-relative (orImp completeness vs IPL semantics) | very low | — |

Out of scope, recommend spawning as separate tasks: **D1-absolute** (needs its own research pass
on the ⟨∨,→,⊤⟩ algebra class) and **D2** (two separation theorems; scoped at roughly one phase,
not open-ended).

Open decisions the planner should surface rather than assume:
1. B2's public API shape (bundled `CutFreeXProof` wrapper vs un-privatising the core) — §B2
   recommends bundled.
2. Whether A2 is a deletion or is paired with building the G6 instance — §G6.
3. Whether B3 waits on task 614's computable `ctxToImp` — §B3 recommends not blocking.

---

## Zero-Debt Note

No step above requires `sorry`, and no step requires a new axiom. Phase 4 (C1) is the only one
with real risk of not completing as written; the risk is mechanical (termination checking under
a new binder, `LJ/CutElimination.lean:650`'s `decreasing_by`), not mathematical. If it stalls,
the correct response is `[BLOCKED]` on that phase with the goal state recorded — phases 5-7
depend on it and should not be attempted around it, while phases 1-3 and 8 are independent and
can still land.

---

## Verification Performed

- All five Part A line citations read directly and reproduced.
- `grep` for strictness/separation vocabulary across `Cslib/Logics/Propositional/` — one hit,
  the overclaim itself.
- `grep` for `instDecidableDerivableIntPropAxiom` / `instDecidableIValid` outside
  `Cslib/Logics/Propositional/` across `Cslib/` and `CslibTests/` — zero hits (A3).
- `grep "theorem temporalTableau_complete"` across `Cslib/` — zero hits (A4 correction).
- `lean_verify Cslib.Logic.PL.intuitionisticTableau_decides` — axioms
  `{propext, Classical.choice, Quot.sound}`, no warnings.
- Declaration-level binder audit of `LJ/CutElimination.lean`, `LJ/SubformulaProperty.lean`,
  `LJ/Interpolation.lean`, `LJ/Decidability.lean` for `{T : Theory Atom}` genericity.
- `SeqProof` inductive read in full (`LJ/Basic.lean:93-144`) to confirm the `botL` gate shape.
- Fragment completeness census across all eight axiom systems.
- `sorry` scan across `Cslib/Logics/Propositional/` — all hits are docstring prose.

Not verified (stated as recommendation, not fact): the estimated line counts; the claim that the
⟨∨,→,⊤⟩ algebraic completeness is hard in the literature (asserted from the structural
residuation argument only, not from a literature check — no literature was loaded for this task,
`lit_flag: false`).
