# Research Report: Symmetrize LK/LJ Sequent-Calculus Coverage (Task 371)

## Scope

Task 371 closes three asymmetries between the classical (LK) and intuitionistic (LJ)
propositional sequent-calculus developments under
`Cslib/Logics/Propositional/SequentCalculus/`. All three are corollaries of results already
proved; no new axioms, no `sorry`, CI green.

1. **LJ subformula property** — LK has `LK/SubformulaProperty.lean`; LJ has none despite
   having cut-elimination. Add `LJ/SubformulaProperty.lean` mirroring the LK proof, adapted to
   single-conclusion sequents.
2. **LK decidability** — LJ has `LJ/Decidability.lean` (deduction theorem → tableau); LK has
   none. Add `LK/Decidability.lean` reducing LK derivability to the existing classical tautology
   checker and prove it correct.
3. **Cut-free completeness as a named theorem** — LK has the `CutFreeLKProof` subtype and
   `LKProof.cutElim` but no standalone corollary. Add
   `lk_cut_free_completeness : Tautology φ → Nonempty (CutFreeLKProof (∅ ⊢ₛ {φ}))`.

All three items are independent and can be implemented in parallel (distinct new files,
no shared edits except the two barrel files + `Cslib.lean`).

## Existing-Code Findings

### Shared infrastructure (reuse targets)

| Symbol | Location | Role |
|---|---|---|
| `Proposition.IsSubformula`, `.refl`, `.trans`, `.and_left/right`, `.or_left/right`, `.imp_left/right` | `Subformula.lean:61-135` | Subformula API, used verbatim by LK SubformulaProperty |
| `Proposition.subformulas`, `.complexity` | `Subformula.lean:53-164` | shared subformula/size measures |
| `Tautology φ := ∀ v, Evaluate v φ` | `Semantics/Bool.lean:80` | classical validity of a single formula |
| `instDecidableTautologyTableau (φ)` | `Tableau/Classical/DecisionProcedure.lean:78` | `Decidable (Tautology φ)` requiring only `[DecidableEq Atom] [Hashable Atom]` — the classical analog of LJ's `instDecidableIValid` |
| `instDecidableTautology [Fintype Atom]` | `Semantics/Bool.lean:175` | alternative Boolean-enumeration decision instance |
| `listToImp`, `ctxToImp` | `LJ/Decidability.lean:71-82` | list/Finset → nested-implication encoding; **atom-generic, directly reusable by LK** |
| `Ctx Atom := Finset (Proposition Atom)`, `Sequent := Ctx Atom × Proposition Atom`, notation `Γ ⊢ A` | `NaturalDeduction/Basic.lean:101-111` | LJ sequent carrier |
| `LKSequent` (fields `.ant`, `.suc`), notation `Γ ⊢ₛ Δ`, `.valid` | `SequentCalculus/Defs.lean:50-65` | LK sequent carrier |

### Item 1 — LK template to mirror (`LK/SubformulaProperty.lean`, 278 lines)

- `LKProof.formulas` (`:51-62`): collects `Γ ∪ Δ` at `ax`/`botL` leaves, unions children
  elsewhere (pass-through for unary rules).
- `liftSubformulaLeft` / `liftSubformulaRight` (`:67-80`): inject a subformula witness into the
  left/right component of `Γ' ∪ Δ'`.
- `cutFreeSubformulaProp` (`:90-243`): private core, `induction d with`; `CutFree d` passed as a
  separate argument so the `cut` case is vacuous (`absurd hcf id`). One `rcases` per rule on the
  conclusion-membership of the IH witness.
- `CutFreeLKProof.subformula_property` (`:255-260`) and `LKProof.subformula_property`
  (`:270-276`, uses `d.cutElim`).

### Item 1 — LJ target structure

LJ proofs (`LJ/Basic.lean:86-135`) are single-conclusion: `Sequent = Ctx × Proposition`, so
`seq.1` is the antecedent `Finset` and `seq.2` the single conclusion. 11 constructors:
`ax, botL, andL, andR, orL, orR1, orR2, impL, impR, weakL, cut`. Cut-freeness predicate is
`LJCutFree` (`:193-204`, `cut ↦ False`); subtype `CutFreeLJProof seq := { d // LJCutFree d }`
(`:207-208`); `LJProof.cutElim : Nonempty (CutFreeLJProof seq)` (`CutElimination.lean:674`).

Differences from LK that drive the adaptation:
- Target set is `insert seq.2 seq.1` (= `Γ ∪ {C}`), not `seq.ant ∪ seq.suc`.
- No `weakR`/succedent; `orR` is split into `orR1`/`orR2` (each only touches the conclusion).
- A single `liftSub` helper suffices (one-sided), replacing the Left/Right pair.

### Item 2 — LJ template to mirror (`LJ/Decidability.lean`, 213 lines)

Reduces general `Γ ⊢ A` to a single decidable validity check via the deduction theorem:
- `ljListDeductionFwd` (`:90`), `ljProofDeductionFwd` (`:111`) — repeated `impR`.
- `ljListDeductionBwd` (`:129`), `ljProofDeductionBwd` (`:169`) — repeated `impL` under a `cut`
  (uses `LJProof.cut`, `LJProof.mono`, `LJProof.impL`, `LJProof.ax`).
- `instDecidableLJDerivable` (`:189`): `decidable_of_iff (IValid (ctxToImp Γ A))` chaining the
  deduction theorem with `lj_iff_ivalid`. `noncomputable` because `ctxToImp` uses
  `Finset.toList`.

### Item 2 — LK ingredients available

- `lk_iff_tautology : Tautology φ ↔ Nonempty (LKProof (∅ ⊢ₛ {φ}))`
  (`LK/Completeness.lean:383`) — the empty-context, singleton-succedent bridge (LK analog of
  `lj_iff_ivalid`).
- `nd_iff_lk : DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ A) ↔ Nonempty (LKProof (Γ ⊢ₛ {A}))`
  (`LK/Completeness.lean:332`) — arbitrary context, singleton succedent.
- `LKProof.sound` / `lk_sound` (`LK/Soundness.lean:41,160`), `LKSequent.valid` (`Defs.lean:63`).
- LK constructors for the backward deduction lemma: `LKProof.impR/impL/ax/mono/cut`
  (`LK/Basic.lean`, `mono` at `:143`).

### Item 3 — ingredients

- `CutFreeLKProof` subtype + `LKProof.cutElim : Nonempty (CutFreeLKProof seq)`
  (`LK/CutElimination.lean:839`).
- `lk_iff_tautology` (above). Composition is two lines.
- Import note: `LK/SubformulaProperty.lean` imports `CutElimination` but **not** `Completeness`;
  `lk_iff_tautology` lives in `Completeness`. A file hosting item 3 must import both.

### Barrels / CI

- `SequentCalculus/LK.lean` and `.../LJ.lean` are hand-maintained barrels (LK barrel already
  notes "CutElimination available transitively via SubformulaProperty"). New files must be added
  to the matching barrel.
- New files require `lake exe mk_all --module` to refresh `Cslib.lean`, then
  `lake shake --add-public --keep-implied --keep-prefix` for import minimization, plus
  `lake exe checkInitImports` (every file begins `import Cslib.Init`) and `lake exe lint-style`.

## Concrete Implementation Directions

### Item 1: `LJ/SubformulaProperty.lean` (mirror of LK, ~150-200 lines)

Header imports: `Cslib.Init`, `public import ...LJ.CutElimination`, `public import ...Subformula`.
Namespace `Cslib.Logic.PL`, `open Proposition`, `variable {Atom} [DecidableEq Atom]`.

```lean
def LJProof.formulas {seq : @Sequent Atom} : LJProof seq → Finset (Proposition Atom)
  | .ax A Γ _      => insert A Γ        -- (A ∈ Γ already, so = Γ; keep uniform)
  | .botL Γ C _    => insert C Γ
  | .andL _ _ _ d  => d.formulas
  | .andR _ _ d₁ d₂ => d₁.formulas ∪ d₂.formulas
  | .orL _ _ _ d₁ d₂ => d₁.formulas ∪ d₂.formulas
  | .orR1 _ _ d    => d.formulas
  | .orR2 _ _ d    => d.formulas
  | .impL _ _ _ d₁ d₂ => d₁.formulas ∪ d₂.formulas
  | .impR _ _ d    => d.formulas
  | .weakL _ d     => d.formulas
  | .cut _ d₁ d₂   => d₁.formulas ∪ d₂.formulas

private lemma ljLiftSub {B C : Proposition Atom} {tgt : Finset (Proposition Atom)}
    (hmem : C ∈ tgt) (hsub : B.IsSubformula C) : ∃ D ∈ tgt, B.IsSubformula D :=
  ⟨C, hmem, hsub⟩

private lemma ljCutFreeSubformulaProp {seq : @Sequent Atom}
    (d : LJProof seq) (hcf : LJCutFree d) :
    ∀ B ∈ d.formulas, ∃ C ∈ insert seq.2 seq.1, B.IsSubformula C := by
  induction d with ...   -- one rcases per rule, exactly as LK
```

Per-case mapping (target of the conclusion `(Γ, C)` is `insert C Γ`):
- `ax`/`botL`: witness `B` itself, `IsSubformula.refl`.
- `andL A B hAB`: premise target `insert C (insert A (insert B Γ))`; send `A`,`B` to
  `A ∧ B ∈ Γ` via `IsSubformula.trans _ and_left/and_right` and `ljLiftSub` into `insert C Γ`;
  `C` stays (conclusion), `Γ`-members pass through with `mem_insert_of_mem`.
- `andR A B`: IH witnesses live in `insert A Γ` / `insert B Γ`; `A`,`B` are subformulas of the
  conclusion `A ∧ B`; `Γ`-members pass through.
- `orR1`/`orR2 A B`: IH witness in `insert A Γ` (resp. `insert B Γ`); `A`/`B` subformula of
  conclusion `A ∨ B` via `or_left`/`or_right`.
- `orL A B hAB`: `A∨B ∈ Γ`; premises target `insert C (insert A/ B Γ)`; `A`,`B` → `A∨B ∈ Γ`.
- `impL A B hAB`: `A→B ∈ Γ`; left premise `(Γ,A)` sends `A` → `imp_left`; right premise
  `(insert B Γ, C)` sends `B` → `imp_right`, `C` is conclusion.
- `impR A B`: conclusion `A → B`; premise target `insert B (insert A Γ)`; `A` → `imp_left`,
  `B` → `imp_right`.
- `weakL A`: conclusion `(insert A Γ, C)`, target `insert C (insert A Γ)`; IH target
  `insert C Γ`; pass through with extra `mem_insert_of_mem`.
- `cut`: `exact absurd hcf id`.

Public results:
```lean
lemma CutFreeLJProof.subformula_property {Γ : Ctx Atom} {C : Proposition Atom}
    (d : CutFreeLJProof (Γ ⊢ C)) :
    ∀ B ∈ d.val.formulas, ∃ D ∈ insert C Γ, B.IsSubformula D :=
  ljCutFreeSubformulaProp d.val d.property

theorem LJProof.subformula_property {seq : @Sequent Atom} (d : LJProof seq) :
    ∃ d' : CutFreeLJProof seq,
      ∀ B ∈ d'.val.formulas, ∃ C ∈ insert seq.2 seq.1, B.IsSubformula C := by
  obtain ⟨d'⟩ := d.cutElim
  exact ⟨d', ljCutFreeSubformulaProp d'.val d'.property⟩
```
Risk: low. This is a structural mirror; the only friction is `seq.2`/`seq.1` projections on the
`Prod`-based `Sequent` versus LK's named `LKSequent` fields, and the `insert C Γ` target shape.

### Item 2: `LK/Decidability.lean` (mirror of LJ Decidability, ~120-180 lines)

Recommended primary approach (true symmetric analog of LJ — single-conclusion succedent
`Γ ⊢ₛ {A}`, reusing `ctxToImp`):

Header imports: `Cslib.Init`, `public import ...LK.Completeness`,
`public import ...LJ.Decidability` (to reuse `listToImp`/`ctxToImp`),
`public import ...Tableau.Classical.DecisionProcedure` (for `instDecidableTautologyTableau`).
`variable {Atom} [DecidableEq Atom] [Hashable Atom]`.

```lean
-- LK deduction theorem, singleton succedent (no disjunction splitting needed)
def lkListDeductionFwd : ∀ (L) (Γ) (A),
    LKProof ((L.toFinset ∪ Γ) ⊢ₛ {A}) → LKProof (Γ ⊢ₛ {listToImp L A})
  -- [] : simpa;  A::As : LKProof.impR + recurse + LKProof.mono  (mirror ljListDeductionFwd:90)

def lkListDeductionBwd : ∀ (L) (Γ) (A),
    LKProof (Γ ⊢ₛ {listToImp L A}) → LKProof ((L.toFinset ∪ Γ) ⊢ₛ {A})
  -- A::As : LKProof.cut on (A → rest) using LKProof.impL + LKProof.ax  (mirror :129)

noncomputable def lkProofDeductionFwd {Γ A} (d : LKProof (Γ ⊢ₛ {A})) :
    LKProof (∅ ⊢ₛ {ctxToImp Γ A}) := ...   -- unfold ctxToImp; lkListDeductionFwd
noncomputable def lkProofDeductionBwd {Γ A} (d : LKProof (∅ ⊢ₛ {ctxToImp Γ A})) :
    LKProof (Γ ⊢ₛ {A}) := ...

noncomputable instance instDecidableLKDerivable {Γ : Finset (Proposition Atom)}
    {A : Proposition Atom} : Decidable (Nonempty (LKProof (Γ ⊢ₛ {A}))) :=
  decidable_of_iff (Tautology (ctxToImp Γ A)) <| by
    constructor
    · intro hv; obtain ⟨d⟩ := lk_iff_tautology.mp hv; exact ⟨lkProofDeductionBwd d⟩
    · intro ⟨d⟩; exact lk_iff_tautology.mpr ⟨lkProofDeductionFwd d⟩

-- optional, mirrors instDecidableDerivableInIPL via nd_iff_lk:
noncomputable instance instDecidableDerivableInCPL {Γ A} :
    Decidable (DerivableIn (AxiomTheory (@PropositionalAxiom Atom)) (Γ ⊢ A)) :=
  decidable_of_iff (Nonempty (LKProof (Γ ⊢ₛ {A}))) nd_iff_lk.symm
```

Why this shape: it is line-for-line parallel to `LJ/Decidability.lean` (same `listToImp`/
`ctxToImp`, same fwd/bwd deduction lemmas, same `decidable_of_iff`), only swapping `LJProof`→
`LKProof`, `IValid`→`Tautology`, `lj_iff_ivalid`→`lk_iff_tautology`, and the succedent becomes
the singleton `{A}`. Crucially the succedent stays a singleton throughout, so no inversion of
`orR`/`weakR` is required. The backward lemma uses `cut` (result need not be cut-free — only
`Nonempty` is asserted).

Fallback (guaranteed one-liner, if the deduction lemmas prove troublesome): restrict to the
empty-context case, which is an immediate corollary:
```lean
noncomputable instance {φ : Proposition Atom} :
    Decidable (Nonempty (LKProof (∅ ⊢ₛ {φ}))) :=
  decidable_of_iff (Tautology φ) lk_iff_tautology
```

Optional extension (fully general multi-conclusion `Γ ⊢ₛ Δ`): encode the succedent as
`⋁Δ` (an `orFold : Δ.toList → Proposition`, `[] ↦ ⊥`) and prove
`Nonempty (LKProof (Γ ⊢ₛ Δ)) ↔ Nonempty (LKProof (Γ ⊢ₛ {⋁Δ}))`. The `→` of this extra
equivalence needs admissible succedent-disjunction inversion (`orR` plus `cut` against an
`orL`-built proof). This is strictly more work and is **not** required to match LJ's coverage;
recommend deferring it or marking it optional in the plan.

Risk: medium. The forward/backward deduction lemmas involve the same `Finset` set-arithmetic
`simp`/`ext` bookkeeping that already works in `LJ/Decidability.lean:90-161`; transcribe those
proofs and adjust to the LK `∪`/`insert` succedent shapes (`{A}` singletons). `noncomputable`
is unavoidable (`ctxToImp` via `Finset.toList`), matching the LJ instance.

### Item 3: `LK/CutFreeCompleteness.lean` (new tiny file, ~15 lines)

Dedicated file avoids adding a `Completeness` import to `SubformulaProperty.lean`.
Imports: `Cslib.Init`, `public import ...LK.CutElimination`, `public import ...LK.Completeness`.

```lean
/-- Cut-free completeness for LK: every classical tautology has a cut-free LK proof
from the empty context. Corollary of `lk_iff_tautology` and `LKProof.cutElim`. -/
theorem lk_cut_free_completeness {φ : Proposition Atom} (h : Tautology φ) :
    Nonempty (CutFreeLKProof (∅ ⊢ₛ ({φ} : Finset _))) := by
  obtain ⟨d⟩ := lk_iff_tautology.mp h
  exact d.cutElim
```
Consider also stating the iff (`Tautology φ ↔ Nonempty (CutFreeLKProof (∅ ⊢ₛ {φ}))`) since the
backward direction is `fun ⟨d⟩ => lk_iff_tautology.mpr ⟨d.val⟩` (forgetting cut-freeness).
Risk: very low.

## Reuse Check (CSLib reuse-first)

- No new subformula machinery: reuse `Proposition.IsSubformula` + lemmas from `Subformula.lean`.
- No new encoding for item 2: reuse `listToImp`/`ctxToImp` from `LJ/Decidability.lean`
  (atom-generic; import LJ.Decidability rather than redefining).
- No new decision procedure: reuse `instDecidableTautologyTableau` (general atoms) — preferred
  over `instDecidableTautology` which needs `[Fintype Atom]`. Either works; tableau version keeps
  the instance assumptions identical to LJ's.
- No new bridges: reuse `lk_iff_tautology`, `nd_iff_lk`, `LKProof.cutElim`, `LKProof.sound`.

## Risks and Mitigations

1. **Item 2 backward deduction lemma** (medium): the `cut`+`impL` construction and `Finset`
   set-equality rewrites must transcribe from LJ. Mitigation: copy `ljListDeductionBwd`
   (`:129-161`) and adapt succedent to `{A}`; if blocked, ship the empty-context one-liner
   fallback (still a genuine, correct LK decision instance) and mark the general-context lemma
   optional rather than introducing any `sorry`.
2. **`Sequent` projection ergonomics in item 1** (low): `Sequent` is a `Prod` abbrev, so use
   `seq.1`/`seq.2`; `induction d` rebinds `Γ`/`C` per constructor exactly as in LK.
3. **`noncomputable` propagation in item 2** (low): both instances must be `noncomputable`
   (matches `instDecidableLJDerivable`); ensure downstream `decide`-style uses are not expected.
4. **CI barrel/imports** (low): add the three files to `LK.lean`/`LJ.lean` barrels, run
   `lake exe mk_all --module`, then `lake shake`, `checkInitImports`, `lint-style`. `LK.lean`
   already gets `CutElimination` transitively via `SubformulaProperty`; the new
   `Decidability`/`CutFreeCompleteness` files should be added explicitly.
5. **Zero-debt**: every item terminates in existing fully-proved results; no `sorry`, no new
   axioms. If item 2's general case cannot be closed cleanly, descope to single-conclusion +
   empty-context instances (both complete) — do not defer with `sorry`.

## Suggested File / Phase Layout

- Phase A (item 1): `SequentCalculus/LJ/SubformulaProperty.lean`; add to `LJ.lean` barrel.
- Phase B (item 3): `SequentCalculus/LK/CutFreeCompleteness.lean`; add to `LK.lean` barrel.
- Phase C (item 2): `SequentCalculus/LK/Decidability.lean`; add to `LK.lean` barrel.
- Phase D: `lake exe mk_all --module`; full CI (`lake build`, `checkInitImports`, `lint-style`,
  `shake`, `lake test`).

Phases A/B/C are independent (no shared file edits beyond their own barrel line) and may be
parallelized with territory contracts on the two barrel files.
