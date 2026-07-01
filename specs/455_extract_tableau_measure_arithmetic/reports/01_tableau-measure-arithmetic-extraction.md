# Research Report — Task 455: Extract Tableau Measure Arithmetic

**Task**: Extract logic-agnostic measure arithmetic duplicated across the Modal K FMP
measure (task 442) and the Classical propositional tableau into a new shared module
`Cslib/Foundations/Logic/Tableau/Measure.lean`.

**Source context**: task 317 report `specs/317_propositional_tableau_completeness/reports/06_sfor-dedup-reuse-abstraction.md` (R1).

**Verdict**: Well-scoped, zero-semantic-risk pure-arithmetic dedup. Confirmed genuine
byte-identical duplication exists. Target directory already exists. No naming collisions.
All claims below verified against current file contents (line numbers in the task
description were stale; corrected here).

---

## 1. Verified Current Locations and Signatures

All line numbers below are **current** (re-verified; the task's numbers were stale — e.g.
FmpMeasure is now 3104 lines, not ~833).

### 1a. `sum_map_le_length_mul` — ONE location
- **File**: `Cslib/Logics/Modal/Tableau/FmpMeasure.lean:131`
- **Visibility**: `private lemma`
- **Signature**:
  ```lean
  private lemma sum_map_le_length_mul {α : Type*} (l : List α) (f : α → Nat) (c : Nat)
      (h : ∀ x ∈ l, f x ≤ c) : (l.map f).sum ≤ l.length * c
  ```
- **Call sites** (both in FmpMeasure): line 156, line 166 (inside `modalUniverse_length_le`).
- **Purity**: fully generic `List α`/`Nat`; no F/L dependency. Proof: `induction` + `ring` + `omega`.
- **NOT duplicated in Classical** — this one is modal-only today, but is a generic utility the
  task designates for the shared module (`Tableau.sum_map_le_length_mul`).

### 1b. The `modalCap` geometric-sum family → `geomCap` — FmpMeasure only (defs), used in 2 files
- **File**: `Cslib/Logics/Modal/Tableau/FmpMeasure.lean`
- **Visibility**: all **public** (`def` / `lemma` / `@[simp] lemma`), none private.
- The full family (7 declarations) — all pure `Nat`:

  | Current name | Line | Kind | Target name |
  |---|---|---|---|
  | `modalCap` | 776 | `def Sf : Nat → Nat` | `geomCap` |
  | `modalCap_zero` | 780 | `@[simp] lemma` (`= 1`, `rfl`) | `geomCap_zero` |
  | `modalCap_succ` | 782 | `lemma` (`= 1 + Sf * ..`, `rfl`) | `geomCap_succ` |
  | `modalCap_add_one_le_pow` | 788 | `lemma` (`+1 ≤ Sf^(k+1)` for `Sf≥2`) | `geomCap_add_one_le_pow` |
  | `modalCap_zero_le_pow` | 808 | `lemma` (degenerate `Sf≤1`) | `geomCap_zero_le_pow` |
  | `modalCap_le_pow` | 814 | `lemma` (unconditional `≤ Sf^(k+1)`) | `geomCap_le_pow` |
  | `modalCap_mul_eq_succ_sub_one` | 1664 | `lemma` (`Sf*cap k = cap(k+1)-1`) | `geomCap_mul_eq_succ_sub_one` |

  Definition:
  ```lean
  def modalCap (Sf : Nat) : Nat → Nat
    | 0 => 1
    | k + 1 => 1 + Sf * modalCap Sf k
  ```
  This is exactly `Σ_{i=0}^{k} Sf^i` — the target `geomCap` (`Sum_{i<=k} base^i`).

- **Reference counts** (name occurrences incl. docstrings/comments) in FmpMeasure:
  `modalCap` 34, `modalCap_zero` 6, `modalCap_succ` 6, `modalCap_add_one_le_pow` 3,
  `modalCap_zero_le_pow` 2, `modalCap_le_pow` 4, `modalCap_mul_eq_succ_sub_one` 2.
- **Cross-file consumer**: `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (which
  `public import`s FmpMeasure) uses `modalCap` at lines 66, 164, 166, 169, 173, 174, 184,
  1105 and `modalCap_le_pow` (174), `modalCap_succ` (1112). So a rename touches **two** files.

### 1c. Base-3 domination lemmas — GENUINE byte-identical duplication (the core win)
Two identical private lemmas exist in **both** files:

- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:674` `pow3_two_add_one_le`
  and `:684` `pow3_add_one_le`.
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean:2991` `pow3_two_add_one_le` and
  `:3002` `pow3_add_one_le`.

The FmpMeasure copies' own docstrings admit the duplication:
> "generic Nat fact, re-proved locally since the classical declaration is `private` to a
> different file"

Signatures (identical in both files):
```lean
private lemma pow3_two_add_one_le {a0 a1 C : Nat} (hC : 1 ≤ C) (h0 : a0 ≤ C - 1)
    (h1 : a1 ≤ C - 1) : 3 ^ a0 + 3 ^ a1 + 1 ≤ 3 ^ C
private lemma pow3_add_one_le {a0 C : Nat} (hC : 1 ≤ C) (h0 : a0 ≤ C - 1) :
    3 ^ a0 + 1 ≤ 3 ^ C
```
- **Proofs are byte-identical** (`Nat.pow_le_pow_right`, `Nat.one_le_pow`, `pow_succ`, `omega`).
- **Call sites**:
  - Classical/Completeness: `pow3_add_one_le` at 879, 911; `pow3_two_add_one_le` at 904.
  - FmpMeasure: `pow3_add_one_le` at 3065, 3099; `pow3_two_add_one_le` at 3082.
- **Note on task paraphrase**: the task described this API as "3^a≤3^C, 1≤3^C,
  3^a+3^b≤3^(1+max)". The *actual* duplicated lemmas are the two `pow3_*` above (C-1 form,
  ALPHA/BETA specific). The `3^a≤3^C` / `1≤3^C` are the internal `have` steps, not standalone
  lemmas. Recommend moving the two `pow3_*` lemmas as-is (keeping their exact signatures) —
  this is the true, verified de-duplication. Do **not** invent a new generic `3^(1+max)` form
  unless the planner wants an additional convenience lemma (optional, not required for dedup).

---

## 2. Target Module Placement in the Import Graph

**Target directory already exists**: `Cslib/Foundations/Logic/Tableau/` holds 7 foundation
files (Branch, Closure, ClosureCondition, PropositionalRules, RuleResult, Sign, SignedFormula),
all in namespace `Cslib.Logic.Tableau`. New file `Measure.lean` fits cleanly here.

**No cycle risk**: the moved content is pure `Nat`/`List` — it needs **no** tableau types.
`Measure.lean` imports only:
```lean
import Cslib.Init
import Mathlib.Tactic.Ring                              -- for `ring`
import Mathlib.Algebra.BigOperators.Group.List.Basic    -- for List.map/.sum/.sum_cons
```
(These are exactly the imports FmpMeasure already carries for this code; `Nat.pow_le_pow_right`,
`Nat.one_le_pow`, `pow_succ`, `pow_one` come transitively.) Foundations sits *below* Logics, and
both consumers (`Logics/Modal/...` and `Logics/Propositional/...`) sit *above* Foundations, so
both can `import Cslib.Foundations.Logic.Tableau.Measure` with no import cycle.

**Namespace**: place all decls in `namespace Cslib.Logic.Tableau`. Both consumer files already
`open Cslib.Logic.Tableau`, so call sites reference the lemmas **bare** (unqualified) after the
rename — matching the task's `Tableau.*` shorthand.

**Registration mechanics** (planner must include):
1. Add `public import Cslib.Foundations.Logic.Tableau.Measure` to the barrel `Cslib.lean`
   (alongside lines 100-107) — or run `lake exe mk_all --module`.
2. Optionally add it to the aggregator `Cslib/Foundations/Logic/Tableau.lean` (currently
   imports Sign..PropositionalRules) for discoverability. Recommended for consistency.
3. Add `import Cslib.Foundations.Logic.Tableau.Measure` to FmpMeasure.lean and
   Classical/Completeness.lean.

---

## 3. Naming Collisions — NONE

Verified across all of `Cslib/`:
- `geomCap`, `geomCap_le_pow`, `geomCap_succ`, `geomCap_zero`, etc. — **zero** existing uses.
- `sum_map_le_length_mul` — only in FmpMeasure (the source being moved).
- `pow3_two_add_one_le` / `pow3_add_one_le` — only in the two source files.

All target names are free in the `Cslib.Logic.Tableau` namespace.

---

## 4. Visibility Changes Required

Moving to a shared module means these must become **public** (drop `private`):
- `sum_map_le_length_mul` (currently private in FmpMeasure).
- `pow3_two_add_one_le`, `pow3_add_one_le` (currently private in both files).

The `modalCap`/`geomCap` family is already public — no visibility change, only rename.

Docstrings are **mandatory** (docBlame linter) on all public decls. The moved decls already
have docstrings; the planner should adapt wording to drop modal-specific framing (e.g. the
"re-proved locally" note) and make them logic-agnostic.

---

## 5. Recommended Extraction Scope (for the planner)

Move these 10 declarations into `Measure.lean` (namespace `Cslib.Logic.Tableau`):

| # | Moved decl (new name) | Delete from | Update call sites in |
|---|---|---|---|
| 1 | `sum_map_le_length_mul` (public) | FmpMeasure:131 | FmpMeasure (156, 166) |
| 2 | `geomCap` (def) | FmpMeasure:776 | FmpMeasure + CompletenessLoop |
| 3 | `geomCap_zero` | FmpMeasure:780 | " |
| 4 | `geomCap_succ` | FmpMeasure:782 | " |
| 5 | `geomCap_add_one_le_pow` | FmpMeasure:788 | FmpMeasure (internal) |
| 6 | `geomCap_zero_le_pow` | FmpMeasure:808 | FmpMeasure (internal) |
| 7 | `geomCap_le_pow` | FmpMeasure:814 | FmpMeasure + CompletenessLoop |
| 8 | `geomCap_mul_eq_succ_sub_one` | FmpMeasure:1664 | FmpMeasure (internal) |
| 9 | `pow3_two_add_one_le` (public) | FmpMeasure:2991 **and** Classical:674 | FmpMeasure (3082), Classical (904) |
| 10 | `pow3_add_one_le` (public) | FmpMeasure:3002 **and** Classical:684 | FmpMeasure (3065,3099), Classical (879,911) |

**Approx line movement**: ~90-130 lines of definitions/proofs moved, plus deletion of the two
duplicate `pow3_*` copies (~20 lines net removed). Matches the task's ~80-150 estimate.

### Rename strategy (design decision for planner)
The whole `modalCap` family is pure Nat and used only for the geometric-capacity argument, so
a **full rename** (`modalCap*` → `geomCap*`) is the clean path the task intends ("updates call
sites to the shared lemmas"). Two viable execution styles:

- **A (full rename, recommended)**: rename all `modalCap` → `geomCap` occurrences in FmpMeasure
  (~57 refs, many in comments) and CompletenessLoop (~9 refs). Mechanical, but touches comments;
  a scoped `sed`/replace on identifier boundaries, then `lake build`. Cleanest end state.
- **B (thin alias, NOT recommended)**: keep `abbrev modalCap := geomCap` in FmpMeasure to avoid
  touching call sites. Rejected — leaves a modal-named alias, only partial dedup, and the task
  explicitly asks to update call sites.

Recommend **A**. Because `modalCap` is a definition (not just a lemma), the rename of code
references (not comments) is the load-bearing part; comment references can be updated for
cleanliness in the same pass.

---

## 6. Verification Plan (zero-debt, no sorry)

Pure mechanical move — no proof changes needed; proofs port verbatim (only names change).
CI gate:
1. `lake build Cslib.Foundations.Logic.Tableau.Measure` (new module compiles standalone).
2. `lake build Cslib.Logics.Modal.Tableau.FmpMeasure` and
   `lake build Cslib.Logics.Modal.Tableau.CompletenessLoop` (consumers).
3. `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness`.
4. Full `lake build`, then `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`,
   `lake exe mk_all --module` (barrel), `lake shake --add-public --keep-implied --keep-prefix`.

**Zero sorry risk**: this is a copy/rename/delete refactor of already-proven pure-arithmetic
lemmas. No new proof obligations. No axioms. Fully zero-debt-compliant.

---

## 7. Suggested Phasing (for the planner)

- **Phase 1** — Create `Measure.lean` with all 10 decls (public, `geomCap*` names, adapted
  docstrings), register in barrel + aggregator. Build the new module in isolation.
- **Phase 2** — Update FmpMeasure: add import; delete moved decls; rename `modalCap*`→`geomCap*`
  and drop the local `sum_map_le_length_mul` / `pow3_*` copies (reference the shared ones).
  Build FmpMeasure + CompletenessLoop.
- **Phase 3** — Update Classical/Completeness: add import; delete the two local `pow3_*` copies;
  point call sites (879, 904, 911) at the shared lemmas. Build.
- **Phase 4** — Full CI pipeline verification.

Phases 2 and 3 touch disjoint files (Modal vs Propositional) except for the shared new module,
so they are independent once Phase 1 lands.

---

## 8. Lint/Standards Notes

- All moved decls are public → **docstrings mandatory** (docBlame). Present already; de-modalize.
- `geomCap` is a `def` returning `Nat` (data) → correct to keep as `def` (not lemma).
- `geomCap_*` are Prop-valued → `lemma`/`theorem` (already are). Good.
- Names are lowerCamelCase, no underscores-in-words issue (`geomCap`, `pow3_two_add_one_le`
  use standard segment underscores, matching existing style). No `defsWithUnderscore` risk.
- `@[simp]` on `geomCap_zero` (`= 1`) — LHS `geomCap Sf 0` is fine, carry the attribute over.
- Instances: none introduced. `topNamespace`/`dupNamespace`: decls sit under
  `Cslib.Logic.Tableau`; names do not repeat the namespace segment. OK.
