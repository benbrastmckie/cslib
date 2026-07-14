# Research Report: Intuitionistic Modal Metalogic Framework (Task 480)

**Task**: Intuitionistic modal metalogic FRAMEWORK — prime-theory machinery + birelational
canonical-model construction; the intuitionistic analogue of task 478's classical
MCS/canonical-model framework. Parameterized over modal frame conditions; reuses task 478's
generic Hilbert-calculus infrastructure.

**Session**: sess_1784011298_752245_480 | **Type**: cslib | **Lit mode**: active
(Simpson 1994, Wijesekera 1990)

---

## 1. Executive Summary / Reuse Verdict

The reuse story is **exceptionally strong**. Three independent pieces of existing,
sorry-free infrastructure compose to give task 480 almost for free:

1. **The modal Hilbert calculus is axiom-parameterized and intuitionistic-compatible.**
   `DerivationTree Axioms` / `modalDerivationSystem Axioms`
   (`Cslib/Logics/Modal/Metalogic/DerivationTree.lean`) is parameterized over
   `Axioms : Proposition Atom → Prop`, with rules `ax / assumption / modus_ponens /
   necessitation / weakening`. **Nothing in it is classical** — `necessitation` is the
   generic `⊢ φ ⟹ ⊢ □φ` rule, and the deduction theorem needs only `implyK`/`implyS`
   (NOT Peirce). It is reused verbatim; only the axiom SET changes (intuitionistic base
   instead of classical base with Peirce).

2. **The generic prime-exclusion (Lindenbaum-for-prime-theories) lemma already exists and
   is formula-type-generic.** `Metalogic.prime_exclusion`
   (`Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`) is stated over any
   `F` with `[HasImp F] [HasOr F]` and any `DerivationSystem F`. Since `Modal.Proposition`
   already has `HasImp`/`HasOr`/`HasAnd`/`HasDia`/`HasBox`/`Bot` instances
   (`Modal/Basic.lean`), `prime_exclusion` instantiates **directly** at
   `F = Modal.Proposition Atom` and `D = modalDerivationSystem IntModalAxiom`.

3. **The propositional intuitionistic canonical model is a complete structural template**
   for the non-modal half of the work. `IntLindenbaum.lean` + `IntStrongCompleteness.lean`
   (`Cslib/Logics/Propositional/Metalogic/`) already give `IntDCCS`, `IntPrimeDCCS`,
   `int_prime_exclusion`, `int_imp_witness`, the canonical world subtype, the `Preorder`
   = set-inclusion instance, and a truth lemma whose `atom/bot/and/or/imp` cases are
   **identical** to what the birelational truth lemma needs (they are literally the five
   non-modal `BForces` clauses, which `Birelational.lean` documents as matching `PL.IForces`
   "exactly").

**The genuinely new work for task 480 is narrow**: (a) define the intuitionistic modal
axiom predicate framework (base intuitionistic axioms as hypotheses, mirroring the classical
`MCS.lean` pattern, minus Peirce); (b) define the birelational canonical relation `R` over
prime theories and verify `F1`/`F2` + the box/diamond witness lemmas; (c) prove the two
modal cases (`box`, `diamond`) of the birelational truth lemma. Everything else is reuse
or mechanical instantiation.

**No sorry-deferral or new axioms are required or recommended.** The construction is
standard (Simpson 1994 canonical birelation model; Wijesekera 1990 prime-filter accessibility)
and every ingredient has a working in-repo precedent.

---

## 2. Task 478 Framework — File Inventory (located)

Task 478 (`metalogic_hilbert_completeness_framework`, COMPLETED) lives in
`Cslib/Logics/Modal/Metalogic/` and `Cslib/Foundations/Logic/Metalogic/`. The reusable
generic infrastructure:

| File | Contents | Reuse for 480 |
|------|----------|---------------|
| `Modal/Metalogic/DerivationTree.lean` | `DerivationTree Axioms` inductive (ax/assumption/mp/**necessitation**/weakening); `Deriv`, `Derivable`, `modalDerivationSystem` (`DerivationSystem` instance) | **Verbatim reuse** — axiom-parameterized, no classical dependency |
| `Modal/Metalogic/DeductionTheorem.lean` | `deductionTheorem` (needs only `implyK`/`implyS`), `hasDeductionTheorem` | **Verbatim reuse** — intuitionistic-safe |
| `Modal/Metalogic/MCS.lean` | Classical MCS: `SetMaximalConsistent`, `modal_lindenbaum`, `modal_negation_complete`, `mcs_box_witness` (uses `h_peirce`!), box/diamond duality bridges | **Structural reference only** — the box-witness/K-derivation helpers (`iteratedDeduction`, `derive_box_from_box_context`) are reusable; the negation-based witness and Peirce/duality machinery are NOT (replaced by prime exclusion) |
| `Modal/Metalogic/Completeness.lean` (~800L) | `CanonicalWorld` (MCS subtype), `CanonicalModel` (`r S T := ∀φ, □φ∈S → φ∈T`), `canonical_refl/trans/symm/eucl`, `truth_lemma` | **Structural template** for the birelational canonical model; the canonical R box-clause is reused as one conjunct |
| `Modal/Metalogic/Soundness.lean`, `GenericMCSBridge.lean` | Soundness + generic bridge | Soundness pattern reused (over `BForces`/`IValid` instead of classical `Satisfies`) |
| `Foundations/Logic/Metalogic/PrimeExclusion.lean` | **`prime_exclusion`** generic (Zorn over prime-excluding admissible supersets), `Admissible`, `PrimeAdmissible`, `DeductivelyClosed`, chain-union lemmas | **Verbatim reuse** — instantiate at `Modal.Proposition` |
| `Foundations/Logic/Metalogic/Consistency.lean` | `SetConsistent`, `set_lindenbaum`, `DerivationSystem` | Reused (consistency predicate for prime theories) |

---

## 3. Reusable AS-IS (Reuse-First Check Passed)

Per CSLib reuse-first policy, these existing abstractions must be reused, **not**
re-implemented:

- **`Metalogic.prime_exclusion`** (Foundations) — the core Lindenbaum-style lemma for prime
  theories. F-generic; instantiate at `F = Modal.Proposition Atom`. This is exactly what
  `int_prime_exclusion` (propositional) wraps, and task 480 wraps the same lemma for the
  modal derivation system.
- **`modalDerivationSystem` / `DerivationTree`** — the Hilbert calculus. Reused unchanged.
- **`deductionTheorem` / `hasDeductionTheorem`** — reused unchanged (implyK/implyS only).
- **`BFrame` / `BModel` / `BForces` / `bforces_persistence` / `IValid` / `MValid`**
  (`Modal/Semantics/Birelational.lean`, task 490) — the semantic target. Reused as the
  codomain of the truth lemma.
- **Modal connective typeclass instances** (`HasImp`/`HasOr`/`HasAnd`/`HasDia`/`HasBox`/`Bot`
  on `Proposition Atom`) — already present in `Modal/Basic.lean`; satisfy the `prime_exclusion`
  requirements. **No new notation or typeclass needed.**
- **The propositional Int building blocks** are analogues to copy structurally, not reuse
  directly (they are over `PL.Proposition`, task 480 is over `Modal.Proposition`):
  `IntDCCS`, `IntPrimeDCCS`, `int_imp_witness`, `intDeductiveClosure*`,
  `IntCanonicalWorld`, the `Preorder` = inclusion instance, `int_truth_lemma`.

---

## 4. Classical MCS vs Intuitionistic Prime Theory — the Divergence

| Aspect | Classical (task 478) | Intuitionistic (task 480) |
|--------|----------------------|---------------------------|
| Worlds | Maximal Consistent Sets (`SetMaximalConsistent`) | **Prime theories** = deductively-closed, consistent, disjunction-property sets (`PrimeAdmissible D (SetConsistent D)`) |
| Completion lemma | `modal_lindenbaum` (negation-complete extension) | **`prime_exclusion`** (φ-excluding prime extension) |
| Key set property | Negation-completeness: `φ∈S ∨ ¬φ∈S` | Disjunction property: `φ∨ψ∈S → φ∈S ∨ ψ∈S`; NO negation-completeness |
| `∨` truth-lemma case | via negation-completeness | via **prime disjunction property** (`IntPrimeDCCS.2`) |
| `→` truth-lemma case | membership is decidable in MCS | via **`imp_witness` + prime exclusion** (build a prime `≤`-successor forcing φ but not ψ) |
| Propositional axioms | classical: includes **Peirce** `((φ→ψ)→φ)→φ` | intuitionistic: `implyK, implyS, andI/E1/E2, orI1/I2/E, efq` — **no Peirce** |
| Order structure | single relation R (worlds are "flat") | **two relations**: `≤` (inclusion, heredity) + `R` (modal accessibility) |
| Semantics | `Satisfies` (classical Kripke) | `BForces` (birelational, `IValid`/`MValid`) |
| `⊥` treatment | `⊥∉S` always | IK: `⊥∉S` (`botForces=fun _=>False`); Minimal (495): `⊥` ordinary, worlds may force `⊥` (arbitrary upward-closed `botForces`) |

**Crucial point on the box witness:** the classical `mcs_box_witness` builds the successor
world using `¬φ` and Peirce's law. This does **not** transfer intuitionistically. The
intuitionistic box witness instead uses **prime exclusion**: from `□φ ∉ w` build the set
`{ψ | □ψ ∈ w}`, show `φ ∉ cl({ψ | □ψ ∈ w})`, and apply `prime_exclusion` to get a prime
`v` with `{ψ | □ψ∈w} ⊆ v` and `φ ∉ v`. The K-derivation helpers `iteratedDeduction` and
`derive_box_from_box_context` in `MCS.lean` (which need only `implyK/implyS/K`, **not**
Peirce) are directly reusable for the "`{ψ | □ψ∈w}` cannot derive `φ`" step.

---

## 5. Literature Proof Structure (Simpson 1994 / Wijesekera 1990)

Grounded against the corpus (`~/Projects/Literature/simpson_1994_intuitionisticmodallogic/`,
`~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/`; OCR is partial but the
key structural claims are confirmed).

**Simpson 1994 (IK), "canonical birelation model" (Ch. 3, referenced "page 52"):**
1. Worlds = **prime** sets (consistent + deductively closed + disjunction property).
   [Confirmed: Simpson constructs a "(canonical) countermodel to underivable sequents".]
2. Intuitionistic order `≤` = **set inclusion**.
3. Forcing clauses: `□` quantifies over `≤ ∘ R` (clause 3.2); `◇` quantifies over `R`
   alone (clause 3.5). [Already encoded in `BForces`, `Birelational.lean`.]
4. Frame conditions **F1** (up-confluence, makes `◇` monotone) and **F2** (down-confluence).
   [Already in `BFrame`.]
5. Truth lemma by induction; `□`/`◇` cases need box-witness / diamond-witness sub-lemmas.

**Wijesekera 1990 (CK):**
1. "[Completeness] for intuitionistic nonmodal logic uses **prime filters as possible worlds,
   partially [ordered]**" and "an appropriate accessibility between prime filters to reflect
   the modality." [Confirmed verbatim in chunks 0041–0042.]
2. Canonical `R`: "(u, □) R (v, □) if (i) if □y ∈ u then y ∈ v; (ii) …" — the **box-condition
   `□φ∈u → φ∈v`** is the primary accessibility clause. [Confirmed chunk 0111.]
3. **"◇ does not distribute over ∨"** and box/◇ are non-interdefinable. [Confirmed chunk 0002.]
   This is the defining difference of CK: it **drops** IK's `◇(A∨B)→◇A∨◇B` and `◇⊥→⊥`.
4. CK admits **"fallible"/exploding worlds** (worlds forcing `⊥`) — matching the `MValid`
   arbitrary-`botForces` design and why CK's `⊥`/`◇⊥` behave differently. (This is the
   minimal-style treatment, task 495.)

**Translation considerations for each step (Lean):**
- Prime sets → `PrimeAdmissible (modalDerivationSystem IntModalAxiom) (SetConsistent …)`,
  already provided by `prime_exclusion`'s codomain. No new definition of "prime" needed.
- `≤` = inclusion → copy the `Preorder (IntCanonicalWorld Atom)` instance verbatim.
- Canonical `R` (box-clause) → mirror `CanonicalModel.r`. For CK/IK **add the diamond
  clause** (`φ∈v → ◇φ∈w`) because `◇` is primitive and independent (§6).
- F1/F2 on the canonical frame → new lemmas; F1 uses the diamond witness, F2 uses the box
  witness (standard confluence arguments over prime sets).

---

## 6. Birelational Canonical Model — Concrete Lean 4 Sketches

Target namespace: `Cslib.Logic.Modal` (the birelational semantics namespace). Proposed
module: `Cslib/Logics/Modal/Metalogic/Intuitionistic/` (new subtree, keeping the classical
`Metalogic/` files untouched). All sketches are over `Proposition Atom` (the 7-primitive base).

### 6.1 Intuitionistic modal axiom framework (parameterized, mirroring MCS.lean)

Follow the exact style of `MCS.lean`: take the base intuitionistic axioms as hypotheses so
the framework is parameterized over frame-condition axioms, and IK/CK/extensions/minimal
supply the concrete `Axioms` predicate.

```lean
-- Prime theory over the modal derivation system (reuses the generic definitions)
abbrev ModalSetConsistent (Axioms : Proposition Atom → Prop) (S : Set (Proposition Atom)) :=
  Metalogic.SetConsistent (modalDerivationSystem Axioms) S

/-- A prime modal theory: consistent, deductively closed, disjunction property. -/
abbrev ModalPrimeTheory (Axioms : Proposition Atom → Prop) (S : Set (Proposition Atom)) :=
  Metalogic.PrimeAdmissible (modalDerivationSystem Axioms)
    (ModalSetConsistent Axioms) S
```

### 6.2 Prime exclusion for the modal derivation system (thin wrapper — mirror `int_prime_exclusion`)

```lean
theorem modal_prime_exclusion {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ φ ψ, Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ φ ψ χ, Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq   : ∀ φ, Axioms (Proposition.bot.imp φ))          -- IK/IS4…; OMITTED for minimal (495)
    (h_orE   : ∀ A B χ, Axioms (Cslib.Logic.Axioms.OrE A B χ))
    {S : Set (Proposition Atom)}
    (h_adm : Metalogic.Admissible (modalDerivationSystem Axioms)
              (ModalSetConsistent Axioms) S)
    {phi : Proposition Atom} (h_not : phi ∉ S) :
    ∃ T, S ⊆ T ∧ ModalPrimeTheory Axioms T ∧ phi ∉ T :=
  Metalogic.prime_exclusion (modalDerivationSystem Axioms) (ModalSetConsistent Axioms)
    h_adm h_not
    (fun A B χ => ⟨.ax [] _ (h_orE A B χ)⟩)          -- orE schema
    (modalDeductiveClosure Axioms) …                  -- cl + laws copied from IntLindenbaum
```

The `cl`/`cl_subset`/`cl_mem_imp`/`cl_admissible_of_cons`/`phi_mem_cl_of_not_cons`/`hCut`/
`hConsChain` arguments are the direct modal transliterations of the eight arguments supplied
in `int_prime_exclusion` (`IntLindenbaum.lean:223-256`). The EFQ bridge uses `h_efq`; for the
**minimal** case (495) `Cons = fun _ => True` and the EFQ bridge is vacuous — exactly the
`MinLindenbaum` instantiation documented in `PrimeExclusion.lean`.

### 6.3 Canonical worlds, `≤`, valuation (copy from IntStrongCompleteness)

```lean
def CanonicalPrimeWorld (Axioms : Proposition Atom → Prop) :=
  { S : Set (Proposition Atom) // ModalPrimeTheory Axioms S }

instance {Axioms} : Preorder (CanonicalPrimeWorld Axioms) where   -- ≤ = inclusion
  le S T := S.val ⊆ T.val
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂

def canonicalVal (w : CanonicalPrimeWorld Axioms) (p : Atom) : Prop :=
  Proposition.atom p ∈ w.val          -- upward-closed by ≤ = inclusion
```

### 6.4 Canonical accessibility `R` (box-clause + diamond-clause)

Because `◇` is a **primitive, independent** connective (Wijesekera; `Modal/Basic.lean`
design note), the canonical `R` needs BOTH directions — the box preimage clause (as in the
classical `CanonicalModel.r`) AND the diamond image clause:

```lean
/-- Canonical modal accessibility between prime theories.
- box clause: `□φ ∈ w → φ ∈ v`   (Simpson/Wijesekera clause (i))
- diamond clause: `φ ∈ v → ◇φ ∈ w` (needed because ◇ is primitive, not □-dual) -/
def canonicalR (Axioms) (w v : CanonicalPrimeWorld Axioms) : Prop :=
  (∀ φ, (□φ) ∈ w.val → φ ∈ v.val) ∧ (∀ φ, φ ∈ v.val → (◇φ) ∈ w.val)
```

### 6.5 Box and diamond witness lemmas (the two genuinely new proofs)

```lean
/-- Box witness: if `□φ ∉ w`, there is a prime `v` with `canonicalR w v` and `φ ∉ v`.
Build `{ψ | □ψ ∈ w}`, show it cannot derive `φ` (via `derive_box_from_box_context`,
reused from MCS.lean — needs only implyK/implyS/K), then `modal_prime_exclusion`. -/
theorem canonical_box_witness … (h_not_box : (□φ) ∉ w.val) :
    ∃ v, canonicalR Axioms w v ∧ φ ∉ v.val

/-- Diamond witness: if `◇φ ∈ w`, there is a prime `v` with `canonicalR w v` and `φ ∈ v`.
Extend `{ψ | □ψ ∈ w} ∪ {φ}`; consistency uses the K/◇ interaction axioms; prime-exclude
against any χ with `◇χ ∉ w` (or a fixed non-member) to secure the diamond clause. -/
theorem canonical_diamond_witness … (h_dia : (◇φ) ∈ w.val) :
    ∃ v, canonicalR Axioms w v ∧ φ ∈ v.val
```

### 6.6 F1 / F2 on the canonical frame

```lean
theorem canonical_f1 …  -- w ≤ w' (inclusion) → R w u → ∃ u', R w' u' ∧ u ≤ u'
theorem canonical_f2 …  -- R w u → u ≤ u' → ∃ w', w ≤ w' ∧ R w' u'
```
Standard confluence: F1 transports a diamond witness along inclusion; F2 uses the box
witness. These feed `BFrame.f1`/`BFrame.f2` when packaging the canonical `BModel`.

### 6.7 Birelational truth lemma

```lean
theorem canonical_truth_lemma (S : CanonicalPrimeWorld Axioms) :
    (φ : Proposition Atom) →
      (BForces canonicalR' canonicalVal (fun _ => False) S φ ↔ φ ∈ S.val)
  | .atom p => Iff.rfl
  | .bot    => …           -- ⊥∉prime (consistency)      [copy int_truth_lemma .bot]
  | .imp φ ψ => …          -- imp_witness + prime exclusion [copy int_truth_lemma .imp]
  | .and φ ψ => …          -- andI/E                         [copy int_truth_lemma .and]
  | .or  φ ψ => …          -- prime disjunction property     [copy int_truth_lemma .or]
  | .box φ  => …           -- NEW: uses canonical_box_witness + heredity (≤∘R)
  | .diamond φ => …        -- NEW: uses canonical_diamond_witness
```
The five non-modal cases are **line-for-line adaptations** of `int_truth_lemma`
(`IntStrongCompleteness.lean:108-214`) with `PL.Proposition`→`Modal.Proposition` and
`IntPropAxiom`→`Axioms`. Only `.box`/`.diamond` are new.

---

## 7. Per-System Parameterization (how 480 serves 492–495)

Task 480 exposes the framework parameterized by the axiom hypotheses so downstream tasks
instantiate cleanly:

- **IK (492)**: `Axioms = IKModalAxiom` = intuitionistic base + K-□ + K-◇ + `◇⊥→⊥` +
  `◇(A∨B)→◇A∨◇B` + necessitation. `botForces = fun _ => False`. Supplies `h_efq`.
- **CK (493)**: drops `◇⊥→⊥` and `◇(A∨B)→◇A∨◇B` — the fully-independent-◇ case; may require
  the fallible-world (`botForces` arbitrary) treatment for the `◇` clause. The framework's
  `canonicalR` diamond-clause and the diamond-witness lemma are designed exactly for this.
- **Extensions IT/IS4/IS5 (494)**: add reflexive/transitive/euclidean R axioms; reuse the
  classical `canonical_refl`/`canonical_trans` argument shapes over prime worlds. The `≤∘R`
  frame conditions carry over.
- **Minimal MK (495)**: framework MINUS `efq`; use `prime_exclusion` with
  `Cons = fun _ => True` (the `MinLindenbaum` instantiation) and `MValid` (arbitrary
  upward-closed `botForces`). The EFQ bridge argument becomes vacuous.

**Design recommendation**: state every framework lemma with the base intuitionistic axioms
as explicit `h_implyK`/`h_implyS`/`h_andI`/…/`h_orE` hypotheses (as `MCS.lean` does), and
`h_efq` as a SEPARATE hypothesis so the minimal case (495) can omit it. Do **not** hard-code
`IntPropAxiom`-style constructors; keep it `Axioms`-parametric so all five systems share one
`canonical_truth_lemma`.

---

## 8. Recommended File Layout

```
Cslib/Logics/Modal/Metalogic/Intuitionistic/
  PrimeTheory.lean        -- ModalPrimeTheory, ModalDeductiveClosure, modal_prime_exclusion,
                             modal_imp_witness  (wraps Foundations prime_exclusion; mirrors IntLindenbaum)
  CanonicalModel.lean     -- CanonicalPrimeWorld, Preorder(=incl), canonicalVal, canonicalR,
                             canonical_box_witness, canonical_diamond_witness, canonical_f1/f2
  TruthLemma.lean         -- canonical_truth_lemma (5 non-modal cases copied + box/diamond)
  Completeness.lean       -- packages BModel, ivalid/mvalid completeness (parametric)
```
Keeps the classical `Metalogic/` files untouched (Zero-Debt / no regression). Each file
imports `Birelational.lean` (task 490) and the reused Foundations/Modal metalogic.

---

## 9. Tactic Survey (advisory)

The non-modal truth-lemma cases in `int_truth_lemma` are already discharged with explicit
`DerivationTree` term-mode proofs (`.modusPonens`/`.weakening`/`.ax`/`.assumption`) — copy
that style; `simp`/`aesop` are NOT used there and should not be needed (literature-fidelity:
follow the explicit derivations). For the new box/diamond cases, the proofs are structural
(`obtain`/`refine`/`intro`) over the witness lemmas; no heavy automation. `BForces_box`/
`BForces_diamond` `@[simp]` unfold lemmas (already in `Birelational.lean`) handle the forcing
unfolds.

---

## 10. Zero-Debt / Risk Assessment

- **No sorry, no new axioms required.** Every step has an in-repo precedent
  (prime_exclusion, int_truth_lemma, mcs box helpers).
- **Highest-risk step**: `canonical_diamond_witness` + the `.diamond` truth-lemma case,
  because `◇` is primitive and its canonical clause has no classical analogue in task 478.
  Mitigation: Wijesekera's prime-filter accessibility (chunk 0111) and the `canonicalR`
  diamond-clause design above give the exact target; the F1 frame condition (already in
  `BFrame`) is what makes it monotone.
- **Second risk**: getting `canonicalR`'s two clauses mutually consistent with F1/F2 on
  prime worlds. Mitigation: prove F1 via diamond-witness, F2 via box-witness (standard).
- **Consistency of `IntModalAxiom`**: need a soundness argument (`◇`-primitive base is sound
  over `BForces` — task 490's `bforces_persistence` + a per-axiom check). This mirrors
  `int_consistent` (`IntLindenbaum.lean:276`) and should be a task-492/493 soundness lemma,
  but the framework should expose the consistency hook.
- **Lint**: new declarations need docstrings (docBlame); `ModalPrimeTheory`/`canonicalR` are
  `def`/`abbrev` (not Prop-valued theorems, so `def` is correct); use lowerCamelCase; wrap
  instances in the namespace. Follow `IntStrongCompleteness.lean` conventions.

---

## 11. Actionable Next Steps (for /plan)

1. **Phase 1** — `PrimeTheory.lean`: define `ModalPrimeTheory`, `modalDeductiveClosure` +
   laws, `modal_prime_exclusion`, `modal_imp_witness` (transliterate `IntLindenbaum.lean`).
2. **Phase 2** — `CanonicalModel.lean`: `CanonicalPrimeWorld`, `Preorder`, `canonicalVal`,
   `canonicalR`, `canonical_box_witness`, `canonical_diamond_witness`, `canonical_f1/f2`.
3. **Phase 3** — `TruthLemma.lean`: copy 5 non-modal cases from `int_truth_lemma`; prove
   `box`/`diamond` via the witnesses.
4. **Phase 4** — `Completeness.lean`: package the canonical `BModel`, expose parametric
   `ivalid_completeness`/`mvalid_completeness` for 492–495 to instantiate.

Each phase is one agent run (~150–350 lines), sorry-free, with `lake build` at phase end.
```
