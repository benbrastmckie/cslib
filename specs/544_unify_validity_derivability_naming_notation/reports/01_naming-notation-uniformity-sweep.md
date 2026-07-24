# Research Report: Naming / Notation Uniformity Sweep (Task 544)

**Task type:** cslib (mechanical rename/notation sweep across the four logic families)
**Scope:** `Cslib/Logics/{Propositional,Modal,Temporal,Bimodal}`
**Reuse-first note:** This is a rename/alignment task, not a new-abstraction task. No new
definitions or typeclasses are recommended; every item below reuses or renames existing
declarations. Zero-debt is achievable for all six items (pure renames + one notation addition;
no proofs are weakened, no `sorry`, no axioms).

All line numbers were re-verified against the current tree (post-539/540/545/546). Where the
task's cited lines had moved, corrected locations are given.

---

## Item 1 — Validity vocabulary alignment (Temporal ↔ Bimodal)

### Current state (verified)

| Family | Predicate names | Location | Case |
|--------|-----------------|----------|------|
| Propositional | `Tautology` | `Semantics/Bool.lean:90` | Capitalized, distinct word |
| Modal | *(none top-level)* — only pointed `Modal[m,w ⊨ φ]` notation | `Modal/Basic.lean:277` | n/a |
| Temporal | `Valid`, `ValidSerial`, `ValidDense`, `ValidDiscrete`, `SemanticConsequence`, `Satisfiable`, `FormulaSatisfiable` | `Semantics/Validity.lean:74,80,87,94,103,112,118` | **Capitalized** |
| Bimodal | `valid`, `validDense`, `validDiscrete`, `semanticConsequence`, `satisfiable`, `satisfiableAbs`, `formulaSatisfiable` | `Semantics/Validity.lean:49,117,129,68,87,98,106` | **lowercase** |

The Temporal↔Bimodal pair share identical FrameClass vocabulary (`Dense`/`Discrete`/serial
conditions) and differ **only** in capitalization. This is the highest-value, lowest-risk pair
to align, exactly as the task states.

### Recommendation: lowercase `valid*` for Temporal (align to Bimodal)

Rename in `Cslib/Logics/Temporal/Semantics/Validity.lean`:

| From | To |
|------|-----|
| `Valid` | `valid` |
| `ValidSerial` | `validSerial` |
| `ValidDense` | `validDense` |
| `ValidDiscrete` | `validDiscrete` |
| `SemanticConsequence` | `semanticConsequence` |
| `Satisfiable` | `satisfiable` |
| `FormulaSatisfiable` | `formulaSatisfiable` |

Also update the reduction-lemma docstrings/`## Validity Hierarchy` ASCII block in the module
header (they name `Valid`/`ValidSerial`/etc.).

### Churn (verified reference counts, whole-word, inside `Cslib/Logics/Temporal/`)

`Valid` 21 · `ValidDense` 9 · `ValidSerial` 7 · `SemanticConsequence` 7 · `ValidDiscrete` 6 ·
`Satisfiable` 4 · `FormulaSatisfiable` 2. Qualified `Temporal.<Name>` references outside the
Temporal tree: 1 each (negligible).

Consumer files outside `Validity.lean` that reference these predicates:
`Temporal/Metalogic/DenseSoundness.lean`, `Temporal/Metalogic/Chronicle/ChronicleTypes.lean`,
`Temporal/Tableau/Completeness.lean`, `Temporal/ProofSystem/Axioms.lean`.

### CRITICAL false-positive guard (do NOT blind-`sed`)

`Cslib/Logics/Temporal/ProofSystem/Axioms.lean:216,221` contain the English word **"Valid"** in
docstrings ("Valid on densely ordered frames"). These are NOT the `Valid` predicate and must not
be renamed. Any rewrite must be word-boundary + context aware (match `Valid`/`ValidSerial` as an
identifier applied to a formula, never inside prose). Recommend renaming via targeted edits per
reference, or a `sed` restricted to identifier positions with a manual diff review.

### Lint / convention note

CSLib Bimodal already uses lowercase Prop-valued predicate defs (`valid : … → Prop`), so the
lowercase target is house-consistent and does not trip `defLemma` (that linter targets *proofs*
of props declared as `def`, not *predicate definitions*). There is a mild tension with Mathlib's
"capitalized predicate" convention (`Prime`, `Continuous`), but the task's explicit direction
(lowercase, match Bimodal) governs here and yields intra-pair uniformity. Propositional's
`Tautology` is a genuinely different word and is **out of scope** for this item — leave it.

---

## Item 2 — Add turnstile notation to Temporal

### Current state (verified)

- Bimodal `Semantics/Validity.lean:60,81` defines:
  ```lean
  notation:50 "⊨ " φ:50 => valid φ
  notation:50 Γ:50 " ⊨ " φ:50 => semanticConsequence Γ φ
  ```
- Temporal `Semantics/Validity.lean` has **no** `⊨` notation.

### Recommendation

Add the parallel pair to `Temporal/Semantics/Validity.lean` (after the renamed `valid` /
`semanticConsequence`):
```lean
notation:50 "⊨ " φ:50 => valid φ
notation:50 Γ:50 " ⊨ " φ:50 => semanticConsequence Γ φ
```

### DESIGN CONCERN the planner must resolve — notation scoping

Bimodal's `⊨` notation is currently **unscoped** (global), not `scoped`. If Temporal adds an
identical unscoped `notation:50 "⊨ "`, the two clash for any downstream file importing both
`Temporal.Semantics.Validity` and `Bimodal.Semantics.Validity`.

- Good news: **no file currently imports both** (verified — the cross-import set is empty), so
  today there is no active conflict.
- However, `⊨` is a maximally-generic symbol and future files (e.g. an inter-logic embedding)
  could import both. The safe, forward-compatible fix is to make **both** notations `scoped` to
  their namespaces:
  ```lean
  scoped notation:50 "⊨ " φ:50 => valid φ
  ```
  inside `namespace Cslib.Logic.Temporal` and (as a paired change) inside
  `namespace Cslib.Logic.Bimodal`.

Recommendation: add Temporal's notation as `scoped`, and in the same task convert Bimodal's two
notations to `scoped` (with a scan for any use-site that then needs
`open scoped Cslib.Logic.Bimodal`). This is the notation-policy-compliant outcome (CSLib policy:
"keep locally scoped … avoid unscoped notation that may apply to other types"). If the planner
prefers minimal churn, an unscoped Temporal notation is safe *today* but re-introduces the very
non-uniformity this task exists to remove — flag, don't silently pick.

---

## Item 3 — Completeness suffix: `_complete` → `_completeness`

### Current state (verified, corrected against post-545 tree)

Target convention `_completeness` is dominant in the Metalogic layer (37× `strong_completeness`,
plus `ivalidFC_completeness`, `mkvalidFC_completeness`, `ck_completeness`, `prop_completeness`,
`classicalImp_completeness`, `mt_completeness`, … — a large, consistent family). Aligning on
`_completeness` (the longer Mathlib form) is correct.

### CRITICAL correction — a `_complete` **property** family must be EXCLUDED

`grep` for `_complete` (word boundary) returns **two semantically distinct** populations. Only
one is a completeness theorem:

**(A) EXCLUDE — `*negation_complete` = "negation-complete" MCS property (174 occurrences).**
These name the *property* that a maximal set contains `φ` or `¬φ`; they are NOT completeness
theorems. Renaming them to `_completeness` would corrupt their meaning. Members:
`prop_negation_complete`, `modal_negation_complete`, `temporal_negation_complete`,
`restricted_mcs_negation_complete`, `closure_mcs_negation_complete`,
`mcs_closure_negation_complete`, `algebraic_mcs_negation_complete`
(`Foundations/Logic/Metalogic/GenericMCS.lean:162`). **Do not touch these.**

**(B) EXCLUDE — other non-completeness `_complete` uses:** `propositions_complete`
(`HML/Basic.lean:186` — a state's formula-set-is-complete property), and any local `have`-named
`big_complete`/`small_complete`. Audit individually; these are not completeness theorems.

**(C) RENAME targets — genuine completeness theorems using `_complete`.** These live in the
**Algebra** and **Tableau** layers (the task named the Algebra layer specifically):

Algebra layer (`Propositional/Semantics/Algebra/`) — the core of item 3:
| Theorem | Count | File |
|---------|-------|------|
| `hilbert_alg_complete` | 48 | `HilbertAlgCompleteness.lean` |
| `conjImp_brouwerian_complete` | 17 | `BrouwerianCompleteness.lean` |
| `imp_hilbert_complete` | 10 | `HilbertAlgCompleteness.lean:475` |
| `conjImpBot_pointedBrouwerian_complete` | 8 | `PointedBrouwerianCompleteness.lean:150` |
| `conjImpBotMin_brouwerianBot_complete` | 7 | `MplPointedConservative.lean:139` |
| `brouwerianBot_complete` | 6 | `BrouwerianCompletenessGeneric.lean:237` |

Tableau layer (`Propositional/Tableau/`, `Modal/Tableau/`) — same suffix issue, technically
outside the task's "Algebra vs Metalogic" framing but part of full uniformity:
`tableau_complete` (16), `intuitionisticTableau_complete` (11), `minimalTableau_complete` (9),
`classicalTableau_complete` (7), `modalTableau_complete`, `modalTableauT_complete`,
`modalTableauB_complete`, `modalTableauFive_complete`.

### Recommendation

Rename family (C) `…_complete` → `…_completeness`. **Scope decision for the planner:** the task
scopes item 3 to "Algebra layer"; recommend renaming the six Algebra-layer theorems (highest
churn: `hilbert_alg_complete` at 48 refs) as the committed deliverable, and treating the Tableau
`_complete` set as an optional same-task extension for full uniformity. **Under no circumstances
rename the `*negation_complete` (A) or `propositions_complete` (B) families.** A blind
`s/_complete/_completeness/` would break 174+ correct property names — the rename must be
per-declaration, driven by the (C) list above.

---

## Item 4 — `NIKTheorem` → `NIKDerivable`

### Current state (verified)

`Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Deduction.lean:316`:
```lean
def NIKTheorem (𝒯 : Set GeomAxiom) (A : Proposition Atom) : Prop :=
  NIK 𝒯 (Graph.trivial Atom) [] ((Graph.trivial Atom).nonempty.choose ∶ A)
```
It is a `Prop`-valued predicate ("`A` is a theorem of N_IK(𝒯)"). The surrounding naming family
is `NIK` (the derivability relation, 49 uses in Deduction.lean) and, library-wide, `Derivable`.
`NIKTheorem` is the lone `…Theorem` name in an otherwise `Derivable`-shaped vocabulary.

### Churn (verified)

`NIKTheorem`: 15 occurrences across 3 files —
`Deduction.lean:316` (def), `Constructive/Labelled/Completeness.lean` (~9, incl. docstrings and
`nik_TS5_completeness`-style statements at :133), `Constructive/Labelled/Soundness.lean` (~5,
incl. the anti-vacuity certificate `nik_TS5_consistent : ¬ NIKTheorem TS5 ⊥` at :879).

### Recommendation

Rename `NIKTheorem` → `NIKDerivable` (matches the `Derivable` family and the `NIK` prefix;
preferred over `NIK.Derivable` because `NIK` is a relation name, not a namespace here). Update
all 15 sites, including the several **docstring** mentions in Completeness.lean/Soundness.lean.
Low risk, self-contained to the Constructive/Labelled subtree. No proofs change.

---

## Item 5 — S5 `ModalAxiom` → `S5Axiom` (+ relocation question)

### Current state (verified)

`Cslib/Logics/Modal/Metalogic/DerivationTree.lean:69`:
```lean
abbrev ModalAxiom : Proposition Atom → Prop := SchemaUnion s5Tags
```
All 14 sibling systems define `<Sys>Axiom := SchemaUnion <sys>Tags` **in
`ProofSystem/Instances/<Sys>.lean`** (verified: `KAxiom`, `TAxiom`, `DAxiom`, `BAxiom`,
`K4Axiom`, `K5Axiom`, `K45Axiom`, `S4Axiom`, `D4Axiom`, `D5Axiom`, `D45Axiom`, `DBAxiom`,
`TBAxiom`, `KB5Axiom`). S5 is the sole outlier: bare name `ModalAxiom` (no `S5` prefix) living in
`Metalogic/DerivationTree.lean` instead of `Instances/S5.lean`.

### Churn (verified)

`ModalAxiom`: **57 occurrences across 15 files** (Soundness, MCS, Completeness, Systems/S5/*,
InterSystem/{AxiomSubsumption,LatticeSubsumption,Modularity,IntToClassical,Conservativity},
Bimodal/…/ModalConservativity, ProofSystem/Instances.lean, Instances/S5.lean, DerivationTree).
Two `SchemaUnion.lean` references (lines 15, 113) are **docstring-only** — no code cycle.

### Import-graph analysis (the reason relocation is non-trivial)

- `Instances/S5.lean` **imports** `DerivationTree` (line 8). So `ModalAxiom` currently lives
  *below* Instances/S5 and is consumed *upward*.
- **Relocating** the definition into `Instances/S5.lean` inverts this: every current consumer
  that reaches `ModalAxiom` via a `DerivationTree` import (e.g. `Metalogic/Soundness.lean`,
  `Metalogic/MCS.lean`) would have to add `import …ProofSystem.Instances.S5`. That is feasible
  without a cycle (Instances/S5 imports only DerivationTree/ProofSystem/SchemaUnion, none of
  which import the Metalogic consumers), but it is **wide churn (~13 files gain an import)**.
- Consequence for the deprecated alias: because `Instances/S5.lean` imports `DerivationTree`, a
  backward-compat `abbrev ModalAxiom := S5Axiom` **cannot** live in `DerivationTree.lean` if
  `S5Axiom` moves to `Instances/S5.lean` (that would be a cycle). The alias would have to live in
  `Instances/S5.lean`, and any consumer wanting the old name must then import Instances/S5.

### Recommendation — two options, planner chooses

**Option A (lower risk, recommended for a mechanical sweep): rename in place + alias.**
In `DerivationTree.lean`, rename `ModalAxiom` → `S5Axiom`, and add
`@[deprecated (since := "…")] alias ModalAxiom := S5Axiom` (or `abbrev ModalAxiom := S5Axiom`) in
the same file. Achieves the **name** uniformity (`S5Axiom` matches all 14 siblings) with zero
import reorganization; the deprecated alias keeps all 57 sites compiling and can be migrated
opportunistically. Does NOT achieve the *location* convention (stays in DerivationTree). Note:
the task's own no-task-references-in-deliverables rule means the existing "task 523" mentions in
the docstring should be reworded to durable anchors while editing.

**Option B (full convention alignment, wide churn): relocate.**
Move `S5Axiom := SchemaUnion s5Tags` into `Instances/S5.lean`, remove it from `DerivationTree`,
add `~13` `import …Instances.S5` lines to consumers, and place the deprecated `ModalAxiom` alias
in `Instances/S5.lean`. Matches siblings on both name and location, but is the largest single
change in this task and needs a full `lake build` to confirm no cycle slipped in.

Given the task labels this a "mechanical rename sweep" and explicitly permits "keep a deprecated
alias if churn is wide" (churn IS wide: 57 refs / 15 files), **Option A is recommended**; Option
B should be an explicit, separately-verified phase if strict location alignment is wanted.

---

## Item 6 — Conservativity naming: two schemes

### Current state (verified) — richer than the task's two-way framing

**Scheme 1: `<sys>_conservative_extension`** (conservativity over classical propositional logic;
one theorem per system, in `…/ConservativeExtension.lean`). 18 theorems:
`b_`, `db_`, `kb5_`, `tb_`, `s4_`, `d4_`, `t_`, `k5_`, `s5_`, `k45_`, `d_`, `db_`, `d5_`, `d45_`,
`k4_` `_conservative_extension`, plus three off-pattern:
- `Systems/K/ConservativeExtension.lean:24` → **`modal_conservative_extension`** (bare `modal_`,
  not `k_` — double outlier: wrong prefix *and* the other scheme's target base is unnamed)
- `Bimodal/…/PropositionalConservativity.lean:97` → `bimodal_conservative_extension`
- `Temporal/ConservativeExtension.lean:61` → `temporal_conservative_extension`

**Scheme 2: `<extending>_conservative_over_<base>`** (names BOTH systems). Used by the
just-landed 545/546 fragment work and the Bimodal/InterSystem layers:
`bimodal_conservative_over_s5`, `bimodal_conservative_over_temporal`,
`cpl_conservative_over_imp`, `cpl_conservative_over_classicalConjImp`,
`cpl_conservative_over_classicalConjImpBot`, `ipl_conservative_over_mpl`,
`ipl_conservative_over_conjImp`, `ipl_conservative_over_imp`, `ipl_conservative_over_conjImpBot`,
`ipl_conservative_over_orImp`, `axisC_k_conservative_over_cpl`, `conservative_over_cpl`.

### Recommendation: standardize on `<extending>_conservative_over_<base>`

Scheme 2 is strictly more informative (names the base logic, not just "extension"), and it is the
convention the **freshly-landed** task-545/546 files already use
(`FragmentConservativityInstances.lean`, InterSystem lattice files). Standardizing on Scheme 1
would mean *renaming the just-landed 545/546 work backward* — the wrong direction. Therefore:

Rename the 18 `<sys>_conservative_extension` theorems to `<sys>_conservative_over_cpl` (the base
is classical propositional logic / `Tautology`), and fix the two off-pattern names:
- `modal_conservative_extension` → `k_conservative_over_cpl` (gives K its proper prefix)
- `bimodal_conservative_extension` → `bimodal_conservative_over_cpl`
- `temporal_conservative_extension` → `temporal_conservative_over_cpl`

Verify each theorem's actual base before assigning `_cpl` (spot-check: the `Systems/*` ones state
conservativity over CPL via `Tautology`/`toModal` — confirmed for the sampled B/S5/T). Churn is
low per theorem (mostly 1 reference each; `modal_conservative_extension` has 4). The
`…/ConservativeExtension.lean` **file** names can stay; only the theorem identifiers change.

Note the task's phrase "across all five" appears to be a stale/loose count — the actual split is
the two schemes above spanning ~30 theorems, not five. Treat "standardize one scheme across the
conservativity theorems" as the intent.

---

## Cross-cutting implementation guidance

1. **Sequencing (independent, parallelizable phases).** Items 1, 4, 5, 6 touch disjoint files;
   item 2 depends on item 1 (uses the renamed `valid`/`semanticConsequence`). Item 3 is disjoint.
   Suggested order: (1→2) Temporal validity+notation together; (4) NIK; (5) S5Axiom; (6)
   conservativity; (3) completeness suffix. Each ends with a scoped `lake build` of the touched
   module before the next.
2. **False-positive discipline (the dominant risk in this task).** Three renames have prose/
   property homographs that a blind `sed` would corrupt:
   - Item 1: English "Valid" in `Temporal/ProofSystem/Axioms.lean` docstrings.
   - Item 3: the 174-occurrence `*negation_complete` property family + `propositions_complete`.
   - Item 5: docstring "ModalAxiom" mentions and "task 523/441" references (reword to durable
     anchors per `no-task-references-in-deliverables.md` while editing).
   Rename per-declaration or with word-boundary + identifier-position matching, and diff-review.
3. **Zero-debt / no-blockers.** All six items are renames plus one notation addition. No proof is
   weakened; no `sorry`, no axiom, no vacuous def. Nothing here should reach `[BLOCKED]` on
   proof-difficulty grounds. The only genuine *design* decisions (not blockers) are the notation
   scoping (item 2) and Option A vs B (item 5).
4. **Verification.** After each phase, scoped `lake build Cslib.Logics.<Family>…`; final full
   `lake build`. `lake exe checkInitImports` only if item 5 Option B adds imports.
   `lake lint` to confirm no new `defsWithUnderscore`/`dupNamespace` from the renamed identifiers
   (all targets remain lowerCamelCase/snake-consistent with existing siblings, so none expected).
5. **NOTATION.md** does not currently document validity/turnstile notation; if item 2 lands the
   scoped `⊨`, consider a one-line addition there for discoverability (optional, not required by
   the task).

## Verified reference-count summary (for plan phase-sizing)

| Item | Primary identifier(s) | Occurrences | Files |
|------|----------------------|-------------|-------|
| 1 | `Valid`/`ValidSerial`/`ValidDense`/`ValidDiscrete`/`SemanticConsequence`/`Satisfiable`/`FormulaSatisfiable` | ~56 (Temporal tree) | ~5 |
| 2 | `⊨` notation (new) | +2 defs | 1 |
| 3 | Algebra `_complete` completeness theorems | ~96 (excl. 174 property homographs) | ~6 Algebra (+Tableau optional) |
| 4 | `NIKTheorem` | 15 | 3 |
| 5 | `ModalAxiom` | 57 | 15 |
| 6 | `*_conservative_extension` | ~24 | ~18 |
