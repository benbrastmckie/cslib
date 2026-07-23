# Research Report: Truth-Lemma Consolidation (single generic route)

**Task focus:** Collapse the three canonical-model truth-lemma families (`truth_lemma`,
`k_truth_lemma`, `d_truth_lemma`) into one generic route; relocate shared machinery out of the
K/D leaf files; delete the duplicated D-route box block; repoint all 15 `*_truth_lemma_applied`;
and dedupe the 432 `by decide` schema-witness invocations. Zero sorry, zero semantic change.

## 1. Executive Summary

The task's core claim is **verified and sound**: `k_truth_lemma` is strictly more general than the
other two families and can serve all 15 systems. But the research surfaced **two blockers** in the
task's literal deletion/rename instructions that the plan MUST accommodate to preserve the
sorry-free, compile-green state:

1. **Name collision (hard blocker).** The name `canonical_truth_lemma` is **already taken** by the
   intuitionistic truth lemma at
   `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean:465`, in the **same namespace**
   `Cslib.Logic.Modal`, and both files are imported by the `Cslib.lean` barrel (lines 355 and 401).
   Renaming the promoted classical lemma to `canonical_truth_lemma` would be a duplicate declaration
   -> compile error. **Recommendation: reuse the vacated name `truth_lemma`** for the promoted
   lemma (natural "THE truth lemma" name, minimal churn), or use `classical_truth_lemma`. Do NOT use
   `canonical_truth_lemma`.

2. **`mcs_box_closure` is not dead (soft blocker).** The task lists `mcs_box_closure`
   (`MCS.lean:139`) for deletion, but after removing `mcs_box_witness` it is **still used by
   `canonical_refl`** (`Metalogic/Completeness.lean:81`), the reflexivity frame property that
   T/S4/S5/TB depend on. It is a single, non-duplicated one-liner. **Recommendation: RETAIN
   `mcs_box_closure`** (it is shared infrastructure, not duplication), OR inline its one line
   `mcs_mp_axiom h_implyK h_implyS S.property h_box (h_T φ)` into `canonical_refl` and then delete.
   Deleting it without one of these two edits breaks the build.

Everything else in the task is accurate and achievable as a pure relocation (no new proof
obligations). The tree is currently sorry-free in the classical `Systems/` subtree and stays so.

## 2. Verification of the Central H1 Claim

**Claim:** `k_truth_lemma`'s box case needs only EFQ+K from kCore, so all 15 systems can use it.

**Verified TRUE.** Evidence:

- `k_truth_lemma` (`Systems/K/Completeness.lean:163`) takes exactly the **13 kCore hypotheses**:
  `implyK, implyS, efq, peirce, K, andI, andE1, andE2, orI1, orI2, orE, dualFwd, dualBack`. No
  `h_T`, no `h_D`. Its `.box` and `.diamond` cases route through `k_mcs_box_witness`
  (`K:127`) -> `k_derive_box_from_inconsistency` (`K:51`), which use only
  `implyK/implyS/efq/peirce/K` (all kCore) plus `derive_box_from_box_context` (MCS, kCore-only).
- `truth_lemma` (`Metalogic/Completeness.lean:274`) is identical **except** it additionally demands
  `h_T` and routes the box/diamond cases through `mcs_box_witness` (which needs `h_T`). The `h_T`
  hypothesis is semantically unnecessary for the truth lemma itself.
- `d_truth_lemma` (`Systems/D/Completeness.lean:241`) is identical except it demands `h_D` and
  routes box/diamond through `d_mcs_box_witness`. Again `h_D` is unnecessary for the truth lemma.
- Every one of the 15 axiom predicates is `SchemaUnion sysTags` where
  `sysTags = kCore ∪ (differentiators)` (`ProofSystem/SchemaTags.lean`). Hence
  **`kCore ⊆ sysTags` for all 15 systems** (a `by decide` `Finset.subset` fact). Every system can
  therefore supply the 13 kCore witnesses that `k_truth_lemma` requires.

**Consumer inventory (which family each of the 15 `*_truth_lemma_applied` currently calls):**

| Family | Systems (count) | Extra hyp (to drop) |
|--------|-----------------|---------------------|
| `k_truth_lemma` | K, B, K4, K5, K45, KB5 (6) | none |
| `d_truth_lemma` | D, D4, D5, D45, DB (5) | `h_D` |
| `truth_lemma`   | T, S4, S5, TB (4) | `h_T` |

Repointing the 9 non-K systems means dropping the single extra `h_D`/`h_T` witness — a strict
reduction, always available.

## 3. Structural Facts (file/line anchors for the planner)

### 3.1 Symbols to PROMOTE / RELOCATE into `Metalogic/Completeness.lean`

All three are import-clean into `Metalogic/Completeness.lean` (which imports `MCS.lean`); every
dependency (`derive_box_from_box_context`, `modal_lindenbaum`, all `mcs_*`/`modal_*`) already lives
in `MCS.lean`.

| Symbol | Current location | Action |
|--------|------------------|--------|
| `k_derive_box_from_inconsistency` | `Systems/K/Completeness.lean:51-119` | move to Metalogic (private ok) |
| `k_mcs_box_witness` | `Systems/K/Completeness.lean:127-155` | move to Metalogic |
| `k_truth_lemma` (body) | `Systems/K/Completeness.lean:163-331` | move to Metalogic, **rename to `truth_lemma`** (reuse vacated name) |
| `d_canonical_serial` | `Systems/D/Completeness.lean:189-231` | **relocate** to Metalogic (still needed as a FRAME property by all 5 D-family `d_canonical_FC`; NOT deletable) |

`d_canonical_serial` consumers (must keep resolving after relocation): D, D4, D5, D45, DB
`*_canonical_FC`. Since they all `import Metalogic.Completeness`, relocation is transparent.

### 3.2 Symbols to DELETE (become genuinely dead after promotion)

| Symbol | Location | Dead because |
|--------|----------|--------------|
| old `truth_lemma` (T-requiring) | `Metalogic/Completeness.lean:262-444` | replaced by promoted lemma; only T/S4/S5/TB used it, now repointed |
| `mcs_box_witness` | `MCS.lean:452-482` | only `truth_lemma` used it |
| `derive_box_from_inconsistency` (T-route) | `MCS.lean:382-446` | only `mcs_box_witness` used it — **task did not name this explicitly; include it** |
| `d_derive_box_from_inconsistency` | `Systems/D/Completeness.lean:57-138` | only `d_mcs_box_witness` used it |
| `d_mcs_box_witness` | `Systems/D/Completeness.lean:146-177` | only `d_truth_lemma` used it |
| `d_truth_lemma` | `Systems/D/Completeness.lean:241-412` | D-family repointed to promoted lemma |

This is the ~545 duplicated-line block the task estimates (K -469, D -557 shrink toward the ~180
sibling shape; MCS ~-95; Metalogic old body ~-183 replaced by ~+170 relocated).

### 3.3 `mcs_box_closure` — DO NOT delete blindly (see Section 1, blocker 2)

`MCS.lean:139-148`. Still used by `canonical_refl` (`Metalogic/Completeness.lean:81`). Retain, or
inline-and-delete.

## 4. Item (5): Deduping the 432 `by decide` Schema-Witness Blocks

**Confirmed count:** exactly 432 `by decide` across the 15 `Systems/*/Completeness.lean`. Breakdown
per file (e.g. B = 25): 13 in `*_truth_lemma_applied` + 4 in `*_canonical_FC` (varies) + 4 in
`*_strong_completeness` + 4 in `*_compactness`. K (33) and D (34/27) carry extra witnesses in their
in-file `k_/d_truth_lemma_applied`, `*_canonical_FC` etc.

**Mechanism (verified feasible).** Each witness has the shape
`(fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩ : ∀ φ ψ, SchemaUnion sysTags (φ.imp (ψ.imp φ)))`,
i.e. `⟨tag, (proof tag ∈ sysTags), metavars, rfl⟩`. Because `SchemaUnion.subsumption`
(`SchemaUnion.lean:155`) turns any `kCore`-witness into a `sysTags`-witness given `kCore ⊆ sysTags`,
a **single generic core-witness lemma** discharges all core witnesses from ONE
`(by decide : kCore ⊆ sysTags)` subset fact:

```
-- illustrative shape (recommended new helpers, likely in SchemaTags.lean or Metalogic)
theorem SchemaUnion.implyK_of {S} (h : kCore ⊆ S) :
    ∀ φ ψ, SchemaUnion S (Proposition.imp φ (Proposition.imp ψ φ)) :=
  fun φ ψ => SchemaUnion.subsumption h ⟨.implyK, by decide, φ, ψ, rfl⟩
-- ... one per core tag (implyK, implyS, efq, peirce, modalK, andI, andE1, andE2,
--     orI1, orI2, orE, diaDualityFwd, diaDualityBack)
```

**Best consolidation (combines items 1+4+5).** Add a single convenience wrapper in Metalogic that
takes the subset fact and produces the pre-applied truth lemma, so each leaf's 13-witness block
collapses to one `by decide`:

```
theorem canonicalTruthLemma_of_kCore {S : Finset ModalSchemaTag}
    (h : kCore ⊆ S) (w : CanonicalWorld (SchemaUnion S)) (φ : Proposition Atom) :
    Satisfies (CanonicalModel (SchemaUnion S)) w φ ↔ φ ∈ w.val :=
  truth_lemma (SchemaUnion.implyK_of h) (SchemaUnion.implyS_of h) ... w φ
```

Then every `*_truth_lemma_applied` becomes:
`... := canonicalTruthLemma_of_kCore (by decide) S φ`  (13 witnesses -> 1 subset fact).

The 4-witness blocks inside `*_strong_completeness`/`*_compactness` (which need
`implyK/implyS/efq/peirce`, all in kCore) use the same `SchemaUnion.*_of h` helpers, replacing 4
inline `by decide` witnesses with 4 helper applications sharing one subset fact — or, more
aggressively, refactor the parametric `strong_completeness`/`compactness`/`weak_completeness` to
accept `(h : kCore ⊆ S)` and derive the four propositional callbacks internally (larger change to
the parametric layer; a plan-time trade-off, not required for zero-semantic-change).

Naming note: the `_of` helpers use lowerCamelCase (lint `defsWithUnderscore`); the `_of` suffix is
mathlib-idiomatic and acceptable, but confirm against `lint-prevention-rules.md` — prefer a name
like `SchemaUnion.holdsImplyK` if the linter objects to the mixed style.

## 5. Reuse-First / Existing-Abstraction Check

- **No new abstraction needed for the truth lemma itself** — `k_truth_lemma` already IS the generic
  route; the task is relocation + rename, not new machinery.
- **`SchemaUnion.subsumption` + `SchemaUnion.insert_iff`** (`SchemaUnion.lean:155,179`) are the
  exact existing primitives item (5) calls for; the only genuinely new declarations are the thin
  per-core-tag `_of` witness helpers (13 one-liners) + one convenience wrapper. These belong in the
  Foundations/ProofSystem layer (`SchemaTags.lean` imports only `SchemaUnion.lean`, keeping the
  import graph acyclic) or in `Metalogic/Completeness.lean`.
- `d_canonical_serial` (seriality) has **no reusable substitute** — it is a genuine frame property,
  distinct from the truth lemma, and must survive (relocated).

## 6. Import-Graph Impact

- After promotion, K-family and D-family leaves can DROP `public import ...Systems.K.Completeness`
  (B currently imports it for `k_truth_lemma`, line 11) since the promoted `truth_lemma` lives in
  `Metalogic.Completeness`, already imported by every leaf.
- `Metalogic/Completeness.lean` gains no new imports (all dependencies already via `MCS.lean`).
  However, if the `_of` helpers reference `kCore`/`SchemaUnion`, `Metalogic/Completeness.lean` (or
  wherever the convenience wrapper lives) must import `SchemaTags.lean`/`SchemaUnion.lean`. Verify
  no cycle: `SchemaTags` -> `SchemaUnion` -> `Modal.Basic`/`Foundations.Logic.Axioms`; `Metalogic`
  currently imports `MCS`. A wrapper referencing both `CanonicalModel` and `SchemaUnion` is cleanest
  placed in `Metalogic/Completeness.lean` with an added `import SchemaTags` — confirm acyclicity at
  implement time with a scoped `lake build`.

## 7. Update the Stale Docstring

`Metalogic/Completeness.lean:240-260` documents "three truth lemma families". After consolidation
this comment is false and must be rewritten to describe the single promoted `truth_lemma` (and note
that the intuitionistic/constructive subtrees keep their separate `canonical_truth_lemma` /
`ck_truth_lemma`, which are unrelated).

## 8. Risk / Zero-Debt Assessment

- **No sorry risk.** Every step is relocation, deletion of dead code, or a mechanical witness
  refactor via existing lemmas. No new mathematical content, no proof gaps, no axioms.
- **Compile-break risks** are the two blockers in Section 1 (name collision; `mcs_box_closure`
  usage) plus import-graph adjustments — all deterministic, catchable by `lake build`.
- **Recommended verification order:** phase-scoped `lake build Cslib.Logics.Modal.Metalogic.Completeness`
  after promotion; then each `Systems/*/Completeness.lean` after repointing; full `lake build`
  last. Run `lake lint` for the new helper docstrings/naming (docBlame, defsWithUnderscore).

## 9. Suggested Phase Decomposition (for the planner)

1. **Promote + rename**: move `k_derive_box_from_inconsistency`, `k_mcs_box_witness`, and
   `k_truth_lemma`(->`truth_lemma`) into `Metalogic/Completeness.lean`; delete the old T-requiring
   `truth_lemma`; handle `mcs_box_closure`/`canonical_refl` (retain or inline); delete
   `mcs_box_witness` + T-route `derive_box_from_inconsistency` from `MCS.lean`. Build Metalogic.
2. **Relocate seriality**: move `d_canonical_serial` into `Metalogic/Completeness.lean`.
3. **Add witness helpers** (`SchemaUnion.*_of` + `canonicalTruthLemma_of_kCore`). Build.
4. **Repoint K-family** (K, B, K4, K5, K45, KB5): `*_truth_lemma_applied` -> wrapper; shrink K to
   sibling shape; drop redundant imports. Build each.
5. **Repoint + shrink D-family** (D, D4, D5, D45, DB): delete D-route box block; repoint; use
   relocated `d_canonical_serial`. Build each.
6. **Repoint T-family** (T, S4, S5, TB): drop `h_T` witness, repoint to wrapper. Build each.
7. **Dedupe strong_completeness/compactness witness blocks** across all 15 via the `_of` helpers.
8. **Docstring fix + full `lake build` + `lake lint` + sorry audit** (`lean_verify` on the promoted
   `truth_lemma`).

## Appendix: Key Anchors

- Promoted-from: `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` (k_* at 51/127/163)
- Promote-into / delete-from: `Cslib/Logics/Modal/Metalogic/Completeness.lean` (truth_lemma 262-444; canonical_refl 71-81)
- D-route delete/relocate: `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean` (57/146/189/241)
- MCS deletions: `Cslib/Logics/Modal/Metalogic/MCS.lean` (derive_box_from_inconsistency 382; mcs_box_witness 452; mcs_box_closure 139 — RETAIN)
- Schema primitives: `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` (subsumption 155, insert_iff 179); `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` (kCore + 15 tag sets)
- Name-collision site: `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean:465` (`Cslib.Logic.Modal.canonical_truth_lemma`)
