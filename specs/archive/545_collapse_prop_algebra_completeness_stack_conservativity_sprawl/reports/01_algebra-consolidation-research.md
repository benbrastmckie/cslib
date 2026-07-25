# Research Report: Propositional Algebra Completeness-Stack & Conservativity-Sprawl Consolidation

**Directory under study:** `Cslib/Logics/Propositional/Semantics/Algebra/`
**Constraint:** zero sorry; all inputs currently sorry-free and must remain so.
**Baseline status:** VERIFIED green — scoped `lake build` of the terminal modules
(`CanAlgComplete`, `ConservativeChain`, `OrImpConservative`) completed successfully (783 jobs);
grep scan found no `sorry`/`admit`/vacuous-def in any target file.

---

## 1. Scope Boundary vs Task 393 (SCOPE GUARD — confirmed disjoint)

The task's scope guard says "task 393 owns CROSS-FAMILY conservativity/Lindenbaum consolidation."
No `specs/393_*` directory exists on disk, so the boundary was confirmed against task 393's
**description in `specs/state.json`**, which is the authoritative available source.

Task 393 is **BRIDGE-LEMMA ELIMINATION** across the `Temporal/`, `Bimodal/`, and `Modal/`
families: it consolidates propositional combinator wrappers (`doubleNegation`, `impTrans`,
`lceImp`, …) behind a generic Hilbert/InferenceSystem typeclass, deletes wrap/unwrap layers, and
drops embedding-`rfl` restatements. Its own scope guard reserves "the MCS/deduction-theorem
seams" and "GenericMCSBridge files" (maximal-consistent-set / Kripke-completeness Lindenbaum).

**Boundary verdict: CLEAN, fully disjoint.**
- Task 393 touches only `Temporal/…`, `Bimodal/…`, `Modal/…`. Task 545 touches only
  `Logics/Propositional/Semantics/Algebra/`. No file overlap.
- 393's "Lindenbaum" is the **modal MCS / GenericMCSBridge** construction. Task 545's Lindenbaum
  is the **algebraic** `HilbertLindenbaumAlgebra` quotient (`HilbertLindenbaum.lean`) — a
  different artifact. Moreover, task 545 does **not** need to modify `HilbertLindenbaum.lean` at
  all: both consolidations only re-organize the *public fragment interfaces* that reuse it.
- **Recommendation:** the plan must not touch any `GenericMCS*`, `HilbertLindenbaum*`, or
  cross-family file. Keep `HilbertLindenbaum.lean` as an untouched dependency.

---

## 2. Part A — Completeness Stack

### 2.1 The stack as it stands

| Layer | File | Public core |
|-------|------|-------------|
| Generic (eval-indep) | `FragmentGeneric.lean` | `AlgEvalIndependent`, `generic_gha_implies_ha`, `ghaValid_iff_haValid_of_botFree` |
| Generic (Brouwerian) | `BrouwerianCompletenessGeneric.lean` | `brouwerianBot_complete`, truth lemmas over `ConjImpAxioms` |
| Terminal generic iface | `CanAlgComplete.lean` | `structure CanAlgComplete P`, `canAlgComplete_iff`, 3 instances |
| Piecewise (full logics) | `HilbertCompleteness.lean` | `MPL/IPL/CPL.hilbert_alg_complete` |
| Piecewise (fragment) | `BrouwerianCompleteness.lean` | `conjImp_brouwerian_complete/_iff` |
| Piecewise (reverse links) | `MplConservativeChain.lean` | `mplAxiom_iff_{imp,conjImp,…}`, `GHAValid_implies_BrouwerianValid_direct` |

`CanAlgComplete` bundles a target axiom system `Ax` plus `complete`/`sound` fields, exposes
`canAlgComplete_iff : Derivable C.Ax φ ↔ GHAValid φ` (on the `P`-fragment), and ships three
`def` instances (`IsBotFree→MinPropAxiom`, `IsOrBotFree→ConjImpAxiom`,
`IsImpTopOnly→ImpAxiom`), each built **by reuse** — term-level compositions of the piecewise
theorems.

### 2.2 CRITICAL CORRECTION to the task premise

The task states "four files express one fragment-completeness fact … demote the subsumed
piecewise completeness theorems to private corollaries." Close reading shows this framing is
**only partially accurate and its naive reading would break the build**:

1. **`MPL.hilbert_alg_complete` is NOT subsumed — it is a strict generalization and a heavily
   load-bearing input.** It holds for *all* `φ` (no fragment restriction); the `CanAlgComplete`
   `IsBotFree` instance literally *uses it as both its fields* (`.mpr h` / `.mp h`). It has
   **20 use-sites repo-wide, including `Cslib/Foundations/Logic/ProofSystem.lean`** (a
   Foundations file) and the `IPL`/`CPL` siblings in the same file. Demoting/privatizing it
   would break Foundations and the whole stack. **Must stay public.**

2. **`conjImp_brouwerian_complete` is NOT subsumed either.** It characterizes `ConjImpAxiom`
   against **Brouwerian semilattices** (`BrouwerianValid`), a *different* algebra class than
   `CanAlgComplete`'s `GHAValid`. It is an **input** to `canAlgCompleteIsOrBotFree`
   (**14 use-sites** repo-wide). **Must stay public.**

3. Consequently `HilbertCompleteness.lean` and `BrouwerianCompleteness.lean` are **necessary
   dependencies of `CanAlgComplete`, not redundant duplicates.** `CanAlgComplete` sits *on top
   of* them; it does not restate them.

**What IS genuinely redundant / low-value public surface** (candidates for consolidation):
- The `*_iff_chain` family in `ConservativeChain.lean` — `impAxiom_iff_chain`,
  `conjImpAxiom_iff_chain`, `orImpAxiom_iff_chain`, `minAxiom_iff_chain` — have **0 external
  use-sites**. These multi-hop restatements are the closest thing to "one fact expressed
  repeatedly," and are expressible as `canAlgComplete_iff` corollaries.
- Fragment-level completeness *restatements* that are literal instantiations of
  `canAlgComplete_iff` (as opposed to the unrestricted `hilbert_alg_complete` inputs).

### 2.3 Recommended consolidation for Part A

Rather than "demote HilbertCompleteness/BrouwerianCompleteness to private" (which is infeasible),
the reuse-preserving consolidation is:

- **Adopt `CanAlgComplete` as the single documented public entry point** for *fragment*
  completeness. Keep the piecewise theorems public (they are inputs and are load-bearing) but
  reclassify them in docstrings as "internal inputs to `CanAlgComplete`."
- **Collapse the redundant `*_iff_chain` restatements** in `ConservativeChain.lean`: since they
  have zero consumers, either delete them or re-express each as a one-line corollary of
  `canAlgComplete_iff` / the retained fragment instances, removing the parallel bespoke proofs.
- If any fragment-completeness *restatement* is found to be a literal `canAlgComplete_iff`
  instance, replace its proof body with a one-line `canAlgComplete_iff`-based term (do not delete
  the name if it has consumers; the 2–5 use-site names below must keep their signatures).

**Open decision for the planner:** whether the task's "one fragment-completeness fact" intent is
satisfied by (a) the doc-reclassification + `*_iff_chain` collapse above (recommended, safe,
zero-sorry-preserving), or (b) a more aggressive deletion pass. Option (b) risks the build and
contradicts reuse-first; flag to user before pursuing.

---

## 3. Part B — Fragment-Conservativity Sprawl

### 3.1 The uniform skeleton (the real duplication)

The four fragment files each realize the **same four-theorem skeleton**, differing only in the
fragment predicate `P`, target axioms `Ax`, and the *hard-direction* algebraic route:

| # | Shape | Generalizable? | Realization |
|---|-------|----------------|-------------|
| 1 | `hilbertIplConservativeOverX : P φ → Derivable IntPropAxiom φ → Derivable Ax φ` | **NO** (per-fragment algebra) | fragment-specific completion |
| 2 | `derivableXOfDerivableInt : Derivable Ax φ → Derivable IntPropAxiom φ` | **YES** | `derivable_mono`/`liftDerivationTree` + axiom subsumption |
| 3 | `hilbertIplConservativeOverX_iff : P φ → (Derivable IntPropAxiom φ ↔ Derivable Ax φ)` | **YES** | `⟨1, 2⟩` |
| 4 | `ipl_conservative_over_X : P A → DerivableIn IPL A → Derivable Ax A` | **YES** | `1 (derivableInIplIffDerivableInt.mp h)` |

Per-fragment specifics of the **hard direction (#1), which must be retained verbatim**:

| Fragment | Predicate `P` | `Ax` | Hard-direction route (imports needed) |
|----------|---------------|------|----------------------------------------|
| ConjImp | `IsOrBotFree` | `ConjImpAxiom` | `IPL.hilbert_alg_complete` → `LowerSet B` Heyting → `brouwerianEmbeddingLemma` → `conjImp_brouwerian_complete` |
| Imp | `IsImpTopOnly` | `ImpAxiom` | via ConjImp + `FreeMeetExtension` free BSL + `freeMeetEvaluateEq` + `imp_hilbert_complete` |
| ConjImpBot | `IsOrFree` | `ConjImpBotAxiom` | `NonemptyLowerSet` Heyting + `nonemptyLowerSet_evaluate_commutes` + `conjImpBot_pointedBrouwerian_complete` |
| OrImp | `IsAndBotFree` | `OrImpAxiom` | **sequent-calculus** — `hilbert_iff_lj` + `LJProof.cutElim` + `cutFreeLJ_toOrImp` (the odd one out; not algebraic) |

`liftDerivationTree` and `derivable_mono` (the generic combinators driving #2) currently live in
`ConjImpConservative.lean` and would move into the consolidated core.

### 3.2 Recommended design: `FragmentConservativity.lean` (mirrors `CanAlgComplete`)

The precedent already in this very directory is decisive: **`CanAlgComplete` is exactly this
pattern applied to the completeness side.** Apply the identical idiom to conservativity:

```
structure FragmentConservativity {Atom} (P : Proposition Atom → Bool) where
  Ax   : Proposition Atom → Prop
  hard : ∀ {φ}, P φ = true → Derivable IntPropAxiom φ → Derivable Ax φ
  sub  : ∀ ψ, Ax ψ → IntPropAxiom ψ          -- axiom-level subsumption
```

Generic theorems derived **once** from the structure (replacing the 4×3 = 12 boilerplate
theorems #2–#4):
- `fragmentConservativity_derivableOfDerivableInt` — from `sub` via `derivable_mono`
- `fragmentConservativity_iff` — bundle of `hard` and the above
- `fragmentConservativity_nd` — ND corollary via `derivableInIplIffDerivableInt`

Four `def` instances by reuse (each supplies the retained fragment-specific `hard` proof and a
trivial `sub`): `fragmentConservativityImp`, `…ConjImp`, `…ConjImpBot`, `…OrImp`.

Use a `structure` (not `class`) — same rationale as `CanAlgComplete`: `Ax` is *output* data that
varies per fragment and is not inferable by instance search.

### 3.3 Import-surface consequence (planner must weigh)

A single `FragmentConservativity.lean` that hosts all four instances must import the **union** of
every per-fragment machinery: `FreeMeetExtension`, `FreeJoinCompletion`, `HilbertAlgCompleteness`,
`PointedBrouwerianCompleteness`, `NonemptyLowerSet`, `HilbertConservativeGlivenko`, and the LJ
`CutElimination`/`Completeness` sequent modules. This is a wide but acceptable import surface (it
is the union already spread across the eight files). Two structural options:

- **(Recommended) Two-file split:** a thin `FragmentConservativity.lean` holding the `structure`
  + the three generic theorems + `liftDerivationTree`/`derivable_mono` (small import surface),
  and a sibling that gathers the four instances. This keeps the generic core lightweight and
  lets fragment-specific machinery stay localized.
- **(Task-literal) Single file:** everything in one `FragmentConservativity.lean`. Matches the
  task wording but concentrates the whole import union in one module.

Flag this as an explicit planner decision; both satisfy "one generic core parameterized by the
fragment predicate."

---

## 4. Load-bearing public names (MUST preserve signatures)

Deletion/privatization is only safe for zero-consumer names. Repo-wide use-site counts
(excluding defining line):

| Name | Use-sites | Verdict |
|------|-----------|---------|
| `MPL.hilbert_alg_complete` | 20 (incl. Foundations) | **KEEP PUBLIC** |
| `conjImp_brouwerian_complete` | 14 | **KEEP PUBLIC** |
| `GHAValid_implies_BrouwerianValid_direct` | 8 | KEEP (CanAlgComplete input) |
| `mplAxiom_iff_impAxiom` | 5 | KEEP (CanAlgComplete input) |
| `conjImp_brouwerian_iff` | 2 | keep or re-express, preserve name |
| `mplAxiom_iff_conjImpAxiom` | 2 | keep or re-express |
| `derivableMinOfDerivableConjImp` / `…Imp` | 2 each | KEEP (CanAlgComplete inputs) |
| `*_iff_chain` (all four) | **0** | safe to delete / collapse |

**External importers of the sprawl:** only `Metalogic/ClassicalImpCompleteness.lean` imports
`ImpConservative` and `ConjImpConservative` (transitively — it references none of the four-theorem
skeleton names directly, so re-homing those theorems into `FragmentConservativity.lean` with a
transitive import is safe). The other six files have **0 external importers**. This makes the
refactor low-blast-radius, provided public theorem *names/signatures* with nonzero use-sites are
preserved (they can be re-exported from the new file, or kept as one-line corollaries).

---

## 5. Reuse-First Assessment (mandatory protocol result)

- `Cslib.Foundations.*`: no existing conservativity/completeness abstraction covers this; the
  right abstraction already lives *in the directory* as `CanAlgComplete` (the structure-by-reuse
  idiom). The recommendation reuses that idiom rather than inventing a new one.
- No new Mathlib instantiation is required — this is a pure re-organization of existing
  sorry-free proofs. No new mathematics.
- The generic combinators (`liftDerivationTree`, `derivable_mono`, `derivableInIplIffDerivableInt`,
  `IsImpTopOnly_implies_IsOrBotFree`) all already exist and are reused as-is.

---

## 6. Zero-Sorry Compliance & Risk

- This is a **mechanical refactor** (move + parameterize existing sorry-free terms). No proof is
  re-derived; no `sorry`, no new axiom, no vacuous def is introduced or needed. Zero-debt gate is
  naturally satisfiable.
- **Primary risk:** the naive Part-A reading ("demote HilbertCompleteness/BrouwerianCompleteness
  to private") would break `Foundations/Logic/ProofSystem.lean` and the IPL/CPL siblings. The
  plan **must not** privatize any name with nonzero use-sites. If the user insists on aggressive
  deletion beyond the zero-consumer `*_iff_chain` set, mark `[BLOCKED]` for user review rather
  than break the build.
- **Universe annotations** (`.{u,u}`) are pervasive and load-bearing throughout these proofs;
  the generic `structure` must carry `universe u` and pin `Atom`/algebra to the same level (as
  both `CanAlgComplete` and `brouwerianBot_complete` already do) to avoid universe-metavariable
  mismatches.
- **`module`/`public import`/`@[expose] public section`** discipline: every target file uses the
  module system with `public import`; the new file(s) must follow the same header pattern and
  begin with `import Cslib.Init`.
- **Barrel update:** adding/removing files requires `lake exe mk_all --module` to refresh
  `Cslib.lean`, and `lake exe checkInitImports`. Deleted files' names must be purged from the
  barrel.

---

## 7. Recommended Approach (for the planner)

1. **Part B first (higher value, cleaner win):** create `FragmentConservativity.lean` with the
   `structure` + 3 generic theorems + `liftDerivationTree`/`derivable_mono`; add 4 instances
   reusing the retained hard-direction proofs; re-express the 4×3 boilerplate theorems as
   thin corollaries of the generic ones (preserving all nonzero-use-site names/signatures).
   Retire the now-empty per-fragment files (or reduce them to re-export shims) — but confirm
   `ClassicalImpCompleteness.lean`'s transitive imports still resolve.
2. **Part A second (narrower):** adopt `CanAlgComplete` as the documented terminal interface;
   collapse the zero-consumer `*_iff_chain` restatements in `ConservativeChain.lean`; reclassify
   the load-bearing piecewise theorems as documented internal inputs (keep public). Do **not**
   privatize load-bearing names.
3. Verify per-phase with scoped `lake build Module.Name`; final full `lake build` +
   `checkInitImports` + `lake lint` + `mk_all --module` + `shake`.

**Lint-prevention notes:** new `structure` fields and all new declarations need docstrings
(docBlame); Prop-valued results must be `theorem`/`lemma` not `def` (the instances are data, so
`def` is correct for them); lowerCamelCase names, no underscores in `def` names (defsWithUnderscore
— note existing theorem names like `ipl_conservative_over_imp` use snake_case and are grandfathered
as theorems, which are exempt); wrap instances in explicit namespace (topNamespace); avoid
`Cslib.Logic.PL`-prefix repetition in names (dupNamespace).

---

## 8. Tactic Survey

Not applicable in the usual sense — this task introduces **no new proof goals**; every term is an
existing sorry-free proof being relocated/parameterized. The only "tactics" involved are the
existing bodies (`derivable_mono`, `⟨_, _⟩` anonymous constructors, one-line term compositions).
No `aesop`/`simp`/`omega` search is warranted. The relevant verification tool is scoped
`lake build`, already exercised (green).

---

## 9. Literature

`--lit` not requested (`lit_flag: false`). The directory cites Rasiowa (1974), Nemitz (1965),
Köhler (1981) as the mathematical sources for the underlying completeness results; since no proof
is re-derived, no literature extraction is required for this refactor.
