# Teammate C (Critic) Findings: Task 268 — Simp/Grind Normalization Tags

## Key Findings

### 1. Scope Is Wider Than the Task Description Suggests

The task mentions "Propositional/, Modal/, Temporal/, and Bimodal/ Hilbert systems," but the actual
Hilbert proof system machinery is spread across five distinct layers, not just the `ProofSystem/`
subdirectories:

| Layer | Files Containing Candidate Lemmas |
|-------|------------------------------------|
| Foundations/Logic/Metalogic/ListImplication.lean | `listImp_nil`, `listImp_cons` — already have `@[simp]` but NOT `scoped grind =` |
| Foundations/Logic/InferenceSystem.lean | `rwConclusion` has `@[scoped grind =]` but not `@[simp]` |
| Foundations/Logic/Metalogic/DeductionHelpers.lean | `HasHilbertTree` helpers (noncomputable defs) |
| Logics/{PL,Modal,Temporal,Bimodal}/ProofSystem/ | Derivation.lean, Derivable.lean, Instances.lean |
| Foundations/Logic/Metalogic/Consistency.lean | Generic MCS infrastructure |

**Critical gap**: `listImp_nil` and `listImp_cons` in `ListImplication.lean` already carry `@[simp]`
but are missing `scoped grind =`. These are the most mechanically-used lemmas in list-implication
proofs and are a high-priority target.

**Missing from scope**: The `LTL/` directory (`Cslib/Logics/LTL/`) has no `ProofSystem/` — it uses
semantics only. Confirmed not a gap.

**Also missing from scope mentioned**: No `HilbertSystem.lean` or `ProofSystem.lean` under Modal/
ProofSystem/ — instead it uses per-system instance files (K.lean, T.lean, ..., S5.lean, DB.lean,
etc., 15 total). The task's phrase "modal Hilbert systems" covers all 15; the implementation agent
must not limit to K alone.

### 2. Boundary Ambiguity: Where Does "Definitional" End?

The task says "Do NOT tag derivability constructors (Derivable.ax, Derivable.mp, etc.)." After
reading all four `Derivable.lean` files (Bimodal, Temporal) and `Derivation.lean` (PL, Modal), the
boundary is:

**Clear DO NOT TAG** (constructor-mirroring rules, which are proof-search targets):
- `Bimodal.Derivable.ax`, `.assume`, `.mp`, `.nec`, `.temp_nec`, `.temp_dual`, `.weaken`
- `Temporal.Derivable.ax`, `.assume`, `.mp`, `.temp_nec`, `.temp_dual`, `.weaken`
- `PL.mp_deriv`, `.weakening_deriv`, `.assumption_deriv`
- `Modal.mp_deriv`, `.weakening_deriv`, `.assumption_deriv`

**Ambiguous Cases** (require explicit implementer decision):

(a) **`Derivable.ofTree`** / **`Derivable.lift`**: These are coercions and frame-class monotonicity
lemmas. They are NOT derivability constructors per se, but they are also not "definitional" in the
sense of unfolding connective definitions. Tagging `ofTree` as `@[simp]` would cause simp to fire
on `Nonempty.intro d` patterns, which may be overly aggressive. **Recommendation: do NOT co-tag
these**.

(b) **`Bimodal.Deriv` / `Bimodal.ThDerivable` / `Temporal.Derivable`**: These are `def`s (not
`lemma`s), so they cannot receive `@[simp]` without risking `simpNF` lint failures (simp should
unfold to something simpler, not just expose `Nonempty (DerivationTree ...)`). The `defLemma` linter
also requires Prop-valued `def`s to be `lemma`/`theorem`. **Risk: co-tagging `Deriv` defs would
cause lint failures**.

(c) **`propDerivationSystem`, `modalDerivationSystem`**: These produce `DerivationSystem`
structures from derivation trees. They are structural/connectivity lemmas, not definitional
unfoldings. Tagging them as simp would be unusual. **Recommendation: do NOT tag these**.

(d) **`InferenceSystem.rwConclusion`**: Already has `@[scoped grind =]` but not `@[simp]`. This
is the infrastructure-level rewrite helper. Since `DerivationSystem` lemmas may use it via unification,
adding `@[simp]` risks simp loops. **Ambiguous: needs implementer judgment**.

(e) **Height lemmas** (`height_modus_ponens_left`, etc.): These are used in `termination_by`
annotations and have no use as simp lemmas. **Recommendation: do NOT tag**.

### 3. Build Risk Assessment: GrindLint Test

The `CslibTests/GrindLint.lean` file runs `#grind_lint check (min := 20) in Cslib`. This is the
most critical CI risk. When any new `@[scoped grind =]` lemma produces run-away e-matching
instantiation chains (where a grind rule can be applied to its own output), the grind lint check
fails and a new `#grind_lint skip` exception line must be added.

**Existing exceptions relevant to this task**: The file already has skip entries for:
- `Cslib.Logic.Modal.neg_denotation` — a `@[scoped grind =]` theorem in Modal/Denotation.lean
- `Cslib.Logic.Modal.Satisfies.and_iff_and` — already in the skip list
- `Cslib.Logic.Modal.Satisfies.or_iff_or` — already in the skip list

These are the exactly the `@[scoped grind =]` lemmas in Modal/Basic.lean. This is strong evidence
that **new `scoped grind =` tags may require new `#grind_lint skip` entries**.

**High-risk candidates** for grind loops:
- `listImp_nil` / `listImp_cons`: Structural list lemmas. `listImp_cons` rewrites
  `listImp (ψ :: Ψ) φ` to `HasImp.imp ψ (listImp Ψ φ)` — grind could loop by repeatedly
  unfolding `listImp` into a form that grind re-applies to.
- `Satisfies` characterization lemmas (already in skip list — known issue).

**Medium-risk candidates**: `Deriv`/`Derivable` unfolding lemmas (if any are tagged). These
reduce to `Nonempty (DerivationTree ...)` — grind would need to instantiate `DerivationTree`
constructors, which is unlikely to loop but is structurally similar to the already-skipped HML
patterns.

**Implication**: The implementer must run `lake test` after each batch of tags and be prepared to
add `#grind_lint skip` exceptions for any newly added lemmas that trigger the lint.

### 4. The `scoped grind =` Scoping Mechanism

`scoped grind =` means the grind lemma is registered only within the namespace scope where the
`open scoped` or lexical scope applies. Concretely:
- In a file with `open scoped InferenceSystem`, the grind rules from that namespace are active.
- The `GrindLint.lean` test uses `open_scoped_all Cslib` to open ALL scoped namespaces — this is
  why that test catches all grind annotations globally.

**Implication for implementation**: There is no "global leak" risk from `scoped grind =` in
library files — but the GrindLint test sees them all. A badly behaved lemma tagged `scoped grind =`
in, say, `ListImplication` will only affect proofs that open that namespace, but will still appear
in the GrindLint test.

### 5. Existing `@[simp]`-Only Tags in Target Files

The `listImp_nil` and `listImp_cons` lemmas in `Foundations/Logic/Metalogic/ListImplication.lean`
already have `@[simp]` but are missing `scoped grind =`. This is a co-tagging gap that is clearly
within scope.

In contrast, `Bimodal/Syntax/Formula.lean` has several `@[simp]`-only theorems for `swapTemporal`
distribution (lines 158-176). These are NOT in the target ProofSystem layer but may be mentioned
by other teammates as candidates. **The critic assessment is: these are formula-level structural
lemmas, not Hilbert system definitional lemmas, and do not fall within the stated scope**.

### 6. SimplNF Risk for Definitional Tags

The CSLib lint standards include `simpNF` checking. Any `@[simp]` tag on a lemma whose LHS is
not in simp normal form will fail. The two main risk categories:

(a) **Lemmas where LHS expands to something with further simp-reducible subterms**: For example,
`listImp_cons` rewrites `listImp (ψ :: Ψ) φ` to `HasImp.imp ψ (listImp Ψ φ)`. The RHS still
contains `listImp Ψ φ`, which simp will further reduce. This is the standard pattern for structural
simp lemmas and is safe (simp terminates on induction).

(b) **Proposition-valued definitions tagged `@[simp]`**: The `defLemma` linter requires
Prop-valued declarations to use `lemma`/`theorem`, not `def`. If a `def` that is Prop-valued
is tagged `@[simp]`, it would also fail `defLemma`. Check: `listImp_nil` and `listImp_cons` are
declared as `theorem` — this is correct. No issue.

(c) **`omit [HasBot F] in` patterns**: `listImp_nil` and `listImp_cons` use `omit` to drop
unnecessary typeclass assumptions. This is fine for simp and grind. But `scoped grind =` requires
an active scope — the `omit` doesn't affect namespace scoping.

### 7. Missing Scope: `Foundations/Logic/Metalogic/` Files

Several Foundation metalogic files contain infrastructure used by all four logic systems but no
current `@[simp, scoped grind =]` tags:
- `ListImplication.lean`: `listImp_nil`, `listImp_cons` — clear candidates
- `ListDeduction.lean`: Potentially has lemmas about `listImp` in deduction context
- `SetDeduction.lean`: Set-level derivability
- `Consistency.lean`: MCS infrastructure — unlikely candidates (structural lemmas, not
  definitional unfoldings)

**Recommendation**: Implementers should check `ListDeduction.lean` and `SetDeduction.lean` for any
structural `@[simp]`-appropriate lemmas before limiting scope to just `ProofSystem/`.

### 8. Temporal ProofSystem Is Structurally Different

The Temporal `ProofSystem/Derivation.lean` does NOT exist as a standalone file. Instead:
- `Temporal/ProofSystem.lean` (top-level) imports `Derivable.lean` and `Derivation.lean`
- `Temporal/ProofSystem/Derivation.lean` contains the `DerivationTree` and associated lemmas

But looking at the directory structure, there is no `Temporal/ProofSystem/` subdirectory with a
`Derivation.lean` file in the same pattern as Modal and PL. Instead:
- `Cslib/Logics/Temporal/ProofSystem/Derivable.lean` — Prop wrapper
- `Cslib/Logics/Temporal/ProofSystem/Derivation.lean` — DerivationTree
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` — BX system instances
- `Cslib/Logics/Temporal/ProofSystem.lean` — barrel file

The Temporal system does not have a separate per-system instance hierarchy like Modal (15 systems).
This is correct — there is one temporal logic (BX) with one Hilbert system tag.

### 9. No `listImp` in Temporal/Modal/Bimodal ProofSystem Files

The term `listImp` does not appear in any of the four logic-specific ProofSystem directories. It
lives exclusively in `Foundations/Logic/Metalogic/ListImplication.lean`, which is imported by the
generic deduction theorem infrastructure. This means:
- The task description's mention of "listImp equalities" specifically targets
  `listImp_nil` / `listImp_cons` in Foundations, not any logic-specific file.
- The scope description is slightly misleading: these lemmas are NOT in the
  Propositional/Modal/Temporal/Bimodal ProofSystem directories.

### 10. LTL Logic Has No Hilbert Proof System

`Cslib/Logics/LTL/` has Syntax and Semantics subdirectories but no ProofSystem. This is correct —
LTL in CSLib is semantics-only. No risk of missed scope here.

---

## Recommended Approach for Implementer

1. **Phase 1: Foundation layer** — Add `scoped grind =` to `listImp_nil` and `listImp_cons` in
   `Foundations/Logic/Metalogic/ListImplication.lean` (these already have `@[simp]`; just add
   `scoped grind =`). Then run `lake test` to check for grind lint failures before proceeding.

2. **Phase 2: Definitional unfolding lemmas in Basic/Syntax files** — The real targets for
   `@[simp, scoped grind =]` are derived connective characterizations in ProofSystem layer files:
   - `Derivable.def` patterns (the four `Deriv` / `Derivable` definitions themselves — but check
     lint first; `defLemma` may flag these if Prop-valued)
   - Syntactic characterization lemmas (e.g., `allFuture`, `allPast`, `someFuture` unfoldings)

3. **Avoid tagging** `Derivable.ofTree`, `Derivable.lift`, height lemmas,
   `propDerivationSystem`/`modalDerivationSystem` instance constructors, and any inductive
   constructor (these are proof-search targets, not normalization lemmas).

4. **After each batch of `scoped grind =` additions**, run `lake test` to catch grind lint
   failures. Be prepared to add `#grind_lint skip` entries in `CslibTests/GrindLint.lean` for any
   new run-away patterns.

5. **Check `lake exe lint-style`** for the line-length rule: `#grind_lint skip` lines with fully
   qualified names exceeding 100 characters will require `set_option linter.style.longLine false`
   (already present as a pattern in `GrindLint.lean`).

---

## Evidence and Examples

### Co-tagging pattern in CSLib (existing)

```lean
-- Cslib/Logics/Modal/Basic.lean
@[simp, scoped grind =]
def Proposition.valid (S : Set (Model World Atom)) (φ : Proposition Atom) : Prop := ...

@[simp, scoped grind =]
def logic (S : Set (Model World Atom)) : Set (Proposition Atom) := ...
```

These are definitional unfoldings used in semantic reasoning. The same pattern is the correct
model for the Hilbert system layer.

### `listImp` gap

```lean
-- Foundations/Logic/Metalogic/ListImplication.lean (current)
@[simp] theorem listImp_nil (φ : F) : listImp ([] : List F) φ = φ := rfl
@[simp] theorem listImp_cons (ψ : F) (Ψ : List F) (φ : F) :
    listImp (ψ :: Ψ) φ = HasImp.imp ψ (listImp Ψ φ) := rfl

-- Should become:
@[simp, scoped grind =] theorem listImp_nil ...
@[simp, scoped grind =] theorem listImp_cons ...
```

### GrindLint test structure (already has Modal skip entries)

```lean
-- CslibTests/GrindLint.lean
#grind_lint skip Cslib.Logic.Modal.neg_denotation       -- @[scoped grind =]
#grind_lint skip Cslib.Logic.Modal.Satisfies.and_iff_and -- @[scoped grind =]
#grind_lint skip Cslib.Logic.Modal.Satisfies.or_iff_or   -- @[scoped grind =]
```

This establishes a precedent: `scoped grind =` annotations in Modal.Basic and Modal.Denotation
required grind lint exceptions. New annotations in ProofSystem files WILL likely need the same
treatment.

### `Derivable.lift` boundary case

```lean
-- Bimodal/ProofSystem/Derivable.lean
theorem Bimodal.Derivable.lift {fc₁ fc₂ : FrameClass}
    (h_le : fc₁ ≤ fc₂)
    {Gamma : Context Atom} {p : Formula Atom}
    (h : Bimodal.Derivable fc₁ Gamma p) :
    Bimodal.Derivable fc₂ Gamma p
```

This is frame-class monotonicity. It is NOT a "definitional lemma" — it is a consequence of the
lift operation. Do NOT tag with `@[simp]` or `@[scoped grind =]`. Grind would try to apply this
transitively for any pair of frame classes, causing potential loops.

---

## Confidence Levels

| Finding | Confidence |
|---------|-----------|
| `listImp_nil` / `listImp_cons` are co-tagging gaps | HIGH |
| GrindLint test will require new skip entries for some new annotations | HIGH |
| `Derivable.lift` and `Derivable.ofTree` should NOT be tagged | HIGH |
| `defLemma` lint will fail if Prop-valued `def`s are tagged `@[simp]` | HIGH |
| 15 Modal system instance files are all in scope (not just K) | HIGH |
| `scoped grind =` is namespace-scoped, GrindLint sees all | HIGH |
| LTL has no Hilbert proof system, not in scope | HIGH |
| `listImp` lemmas live in Foundations, not in PL/Modal/Temporal/Bimodal ProofSystem/ | HIGH |
| Height lemmas should not be tagged | MEDIUM-HIGH |
| `propDerivationSystem`/`modalDerivationSystem` should not be tagged | MEDIUM |
| Some `rwConclusion`-adjacent lemmas may be boundary cases | MEDIUM |
