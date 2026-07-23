# Research Report: Dedup Minimal Canonical Model onto Generic Extension

Task type: cslib (Lean 4) · Session: sess_1784322687_fcf57a_521

## Objective

Refactor `mk_completeness` / `mk_soundness_completeness` to instantiate the generic
`mkvalidFC_completeness` (in `MinExtension.lean`) at `Axioms := MKModalAxiom` and the trivial
frame condition, then delete the bespoke MK-only canonical-model machinery
(`MinCanonicalModel.lean`, `MinTruthLemma.lean`, and — see scope note — the orphaned
`MinPrimeTheory.lean`). Preserve all public theorem names, zero sorry, zero regression.

## 1. `MinExtension.lean:23-37` self-documentation + `mkvalidFC_completeness` signature

The header (lines 13-66) states explicitly that `MinExtension.lean` **genericizes** the
task-495 MK-only files: every place the old files invoke `MKModalAxiom.foo args`, the generic
version threads a hypothesis `h_foo args : Axioms (...)`. The efq-free Lindenbaum-pair
combinators (`bigOr1`/`bigAnd1` etc.) are "transcribed verbatim from `MinCanonicalModel.lean`
(same proof scripts, only the axiom-instance sites are threaded)." This is the self-documented
duplication the task targets.

`mkvalidFC_completeness` (MinExtension.lean:1548-1582) signature:

```
theorem mkvalidFC_completeness {Axioms : Proposition Atom → Prop}
    (FC : {World : Type u} → (World → World → Prop) → Prop)
    (h_implyK …) (h_implyS …) (h_andI …) (h_andE1 …) (h_andE2 …)
    (h_orI1 …) (h_orI2 …) (h_orE …) (h_k …) (h_kdia …) (h_cd …) (h_idb …)   -- 12 core-schema witnesses
    (h_canonFC : FC (@MinExt.minCanonicalR Atom Axioms))
    {φ : Proposition Atom} (h_valid : MValidFC.{u, u} FC φ) :
    Derivable Axioms φ
```

It is single-branch (contrapositive via `MinExt.min_head_realization`, forcing at the generic
canonical model rooted at the excluding quasi-prime theory, then `MinExt.min_canonical_truth_lemma`).
`Axioms` is implicit and inferred from the target `Derivable MKModalAxiom φ`.

Supporting generic assets in `MinExtension.lean` (all under `MinExt`, plus 4 unqualified):
`MValidFC` (87), `mvalid_iff_mvalidFC_true` (100), `MinExt.MinCanonicalPrimeWorld` (135),
`MinExt.minCanonicalR` (184), `MinExt.min_canonical_f1`/`f2` (1206/1246),
`MinExt.min_canonical_box_witness`/`diamond_witness` (850/1036),
`MinExt.min_canonical_truth_lemma` (1488), `min_axiom_mem` (1528), `min_imp_property` (1535).
`MinExtension.lean` imports ONLY `Birelational` + `Constructive.SegmentLindenbaum` — it does
**not** depend on any of the files being deleted.

## 2. How MT/MS4/MS5 instantiate `mkvalidFC_completeness` (the pattern to copy)

`MT.lean:246-254` is the canonical template:

```
theorem mt_completeness {φ : Proposition Atom} (h_valid : MValidFC.{u, u} mtFC φ) :
    Derivable MTModalAxiom φ :=
  mkvalidFC_completeness mtFC
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) (fun φ ψ => .cd φ ψ) (fun φ ψ => .idb φ ψ)
    min_canonical_reflexive_mt
    h_valid
```

The 12 `(fun … => .foo …)` args are the anonymous-constructor projections of the axiom
inductive (`.implyK` ⇒ `MTModalAxiom.implyK`, resolved from the inferred `Axioms`). The
second-to-last arg is `h_canonFC` (`FC` holds on the canonical relation). MS4
(`ms4_completeness`, `min_canonical_ms4FC`) and MS5 (`ms5_completeness`, `min_canonical_ms5FC`,
MS5.lean:336-343) follow identically, differing only in the `FC` predicate and its canonical
proof. `MKModalAxiom`'s 12 constructors (`MK.lean:68-105`) have exactly the same
constructor names (`implyK`/`implyS`/`andI`/`andE1`/`andE2`/`orI1`/`orI2`/`orE`/`k`/`kdia`/
`cd`/`idb`), so the same 12-lambda block applies verbatim.

## 3. Trivial frame condition + `MKModalAxiom` instantiation for MK

MK has **no** frame condition, so its target validity is plain `MValid`, not `MValidFC`.
`MinExtension.lean` already provides the bridge:

- `MValidFC` with `FC := fun {_} _ => True` is definitionally the vacuous frame condition.
- `mvalid_iff_mvalidFC_true {φ} : MValid.{u,v} φ ↔ MValidFC.{u,v} (fun {_} _ => True) φ`
  (MinExtension.lean:100-106) converts MK's `MValid` hypothesis into the `MValidFC` form
  `mkvalidFC_completeness` consumes.
- `h_canonFC : (fun {_} _ => True) (@MinExt.minCanonicalR Atom MKModalAxiom)` reduces to `True`,
  discharged by `trivial`.

**Refactored `mk_completeness` (signature UNCHANGED — still `MValid φ → Derivable MKModalAxiom φ`):**

```
theorem mk_completeness {φ : Proposition Atom} (h_valid : MValid.{u, u} φ) :
    Derivable MKModalAxiom φ :=
  mkvalidFC_completeness (fun {_} _ => True)
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) (fun φ ψ => .cd φ ψ) (fun φ ψ => .idb φ ψ)
    trivial
    (mvalid_iff_mvalidFC_true.mp h_valid)
```

`mk_soundness_completeness` (MinCompleteness.lean:71-73) is unchanged:
`⟨mk_completeness, mk_soundness_derivable⟩` — `mk_soundness_derivable` stays in `MK.lean`.

Universe note: current `mk_completeness` uses `MValid.{u, u}`; `mvalid_iff_mvalidFC_true` is
`.{u, v}` and `mkvalidFC_completeness` fixes `FC : {World : Type u}` / `MValidFC.{u, u}`, so
`v := u`. Consistent with the existing MT instantiation. Validate the exact `(fun {_} _ => True)`
binder elaboration at implementation via `lake build` (it is the same literal used at
MinExtension.lean:101).

## 4. Public names downstream consumers rely on (external-reference grep)

Import graph (whole `Cslib/` tree) — the trio is a linear leaf chain:

```
MinPrimeTheory ← MinCanonicalModel ← MinTruthLemma ← MinCompleteness (also imports MK)
MinExtension (imports only Birelational + SegmentLindenbaum) ← MT, MS4, MS5
```

**No file outside the trio imports `MinCanonicalModel`, `MinTruthLemma`, or `MinPrimeTheory`.**
`MinCompleteness` is a barrel-only leaf (nothing imports it).

External references to every public name in the trio + `MinPrimeTheory`, from outside those four
files:

| Name | Source file | External code consumers |
|------|-------------|--------------------------|
| `mk_completeness`, `mk_soundness_completeness` | MinCompleteness | **none** (only docstring mentions in MinExtension) — MUST preserve names anyway |
| `min_canonical_f1`/`f2`, `min_canonical_truth_lemma` | MinCanonicalModel / MinTruthLemma | **none** — MT.lean hits (lines 27-28) are docstring-only, naming `MinExt.*` assets |
| `min_canonical_box_witness`/`diamond_witness` | MinCanonicalModel | **none** — MinExtension hits are its own `MinExt.*` copies (defs 850/1036, used 1448/1483) |
| `min_truth_*_case`, `min_canonical_imp_property` | MinTruthLemma | **none** — MinExtension hits are `MinExt.*` copies |
| `MinCanonicalPrimeWorld`, `minCanonicalVal`, `minBotForces`, `*_upward_closed`, `min_head_realization`, `minBotForces_iff_botMem` | MinPrimeTheory | **none in the modal namespace.** MS4/MS5/MinExtension hits are `MinExt.MinCanonicalPrimeWorld` (different decl). Propositional hits (`Logics/Propositional/Metalogic/{MinStrongCompleteness,MinDecidability,IntStrongCompleteness}`) are namespace-coincidental: modal is `Cslib.Logic.Modal`, propositional is `Cslib.Logic.PL`, and those files do **not** import modal `MinPrimeTheory`. |

**Conclusion:** the only public names any external consumer relies on are `mk_completeness`
and `mk_soundness_completeness`, both kept in place (same names, same types, same file). No
`private` helper in the trio is referenced externally. Zero-regression risk is confined to the
two theorems being rewired.

Baseline check: no `sorry`/`admit`/`axiom` declarations in the Minimal directory (grep hits are
docstring words). The base is already sorry-free.

## 5. Current `mk_completeness` proof structure (to replace)

`MinCompleteness.lean:55-67`: `by_contra` → `min_head_realization h_not_deriv` (MinPrimeTheory)
→ build `w0 : MinCanonicalPrimeWorld Atom` (MinPrimeTheory) → instantiate `h_valid : MValid`
at the MK-specific canonical model (`minCanonicalR`, `min_canonical_f1`/`f2` from
MinCanonicalModel; `minCanonicalVal`/`minBotForces`/`*_upward_closed` from MinPrimeTheory) →
`min_canonical_truth_lemma` (MinTruthLemma) → contradict `φ ∉ T`. Every MK-specific asset in
this proof has a `MinExt.*` generic counterpart already used by `mkvalidFC_completeness`, so the
new proof delegates entirely and the whole bespoke chain becomes dead code.

## Recommended dedup plan (grounds a delete-~1500-line, zero-regression plan)

1. **Edit `MinCompleteness.lean`**: swap `public import …MinTruthLemma` → `public import …MinExtension`
   (keep `import …MK`). Replace `mk_completeness` body with the Section-3 instantiation. Leave
   `mk_soundness_completeness` untouched. (`open Cslib.Logic` already present.)
2. **Delete `MinCanonicalModel.lean` (1089 lines)** and **`MinTruthLemma.lean` (257 lines)**.
3. **Scope decision — `MinPrimeTheory.lean` (125 lines):** after step 2 it is imported by
   nothing and has zero external consumers (§4). It is the MK-specific quasi-prime/valuation
   machinery fully superseded by `MinExt.*`. Deleting it brings the total to
   1089+257+125 = **1471 lines ≈ the task's "~1500"** (the trio alone is 1346). Recommend
   deleting it as well; the planner should confirm since the task text names only the trio.
   (If retained, it stays a barrel-only orphan — harmless but not the full dedup.)
4. **Update barrel `Cslib.lean`**: remove import lines for the deleted files
   (397 `MinCanonicalModel`, 401 `MinTruthLemma`, and 400 `MinPrimeTheory` if deleted); keep
   398 `MinCompleteness`, 399 `MinExtension`. Prefer regenerating via
   `lake exe mk_all --module`.
5. **Verify:** `lake build` (full), `lake exe checkInitImports`, `lake lint`,
   `lake exe lint-style`, `lake test`, then
   `lake shake --add-public --keep-implied --keep-prefix` (import minimization now that
   MinCompleteness's import set changed). Confirm zero `sorry` via `lean_verify` on
   `mk_completeness`, `mk_soundness_completeness`, `mt_completeness`, `ms4_completeness`,
   `ms5_completeness`. `lean_verify` the axiom set of `mk_completeness` matches pre-refactor
   (should reduce to the standard `propext`/`Classical.choice`/`Quot.sound` set already used
   by `mt_completeness`).

## Zero-debt compliance

No sorry, no new axiom, no placeholder is introduced or recommended. The refactor is a pure
delegation to an already-proved generic theorem plus dead-code deletion; every obligation is
discharged by existing sorry-free lemmas. Parallel-safe: touches only the Minimal MK files and
the barrel; MT/MS4/MS5 are unchanged.

## Risks / verification items for the planner

- Confirm `(fun {_} _ => True)` elaborates in the `mk_completeness` position exactly as at
  MinExtension.lean:101 (same literal already compiles there).
- Confirm the anonymous-constructor block resolves `.implyK …` against `MKModalAxiom` (mirrors
  MT.lean:249-252 verbatim; constructor names match §2).
- Barrel regeneration must not drop `MinExtension`/`MinCompleteness`.
- MinPrimeTheory deletion is the one scope item requiring an explicit planner/user decision.
