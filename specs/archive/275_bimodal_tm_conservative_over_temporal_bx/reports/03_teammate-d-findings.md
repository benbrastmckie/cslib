# Strategic Horizons: Task 275 — Bimodal TM Conservative over Temporal BX

**Role**: Teammate D (Strategic Horizons)
**Date**: 2026-06-22
**Context**: Second-round strategic review following team research synthesis

---

## Key Findings

### 1. Roadmap Position and Urgency

Task 275 holds a unique position in the project: it is the **sole remaining sorry in the
entire conservativity program** (tasks 272-276) and the **sole blocker of a full `Cslib.lean`
build**. Task 276 (completed, 24 conservativity theorems for the modal cube) explicitly
documents this pre-existing failure.

The conservativity program's structural role in the roadmap is as the capstone for the
bimodal porting effort. The ROADMAP.md "Completed" table lists BX Conservative Extension
(`Logics/Bimodal/Metalogic/ConservativeExtension/`) as done, but this is only partially
accurate: the module compiles with `warn.sorry false` suppression. The mathematically
meaningful claim — that TM is a conservative extension of BX for the temporal fragment —
remains unproven.

The ROADMAP.md "Remaining" section lists only completeness variants (discrete, continuous,
dense for both bimodal and temporal). Task 275 is not listed as remaining because it was
thought to be structurally complete. This is a classification error: the sorry represents
an unfinished result, not a future planned result.

### 2. The Mathematical Obstacle Is Real but Bounded

The domain mismatch is a genuine mathematical gap, not a Lean formalization artifact.
The core asymmetry:

- Bimodal soundness requires `AddCommGroup D` (the `TaskFrame` axioms use group operations
  for task duration arithmetic: `taskRel w d u := u = w + d`).
- Temporal BX completeness constructs countermodels on `ChronicleSubtype` (a subtype of
  `ℚ` defined by the omega-chain), which has `LinearOrder` but NOT `AddCommGroup`.

This asymmetry cannot be dissolved by minor API changes. It reflects the fact that
bimodal semantics bakes in more structure than temporal semantics needs. The four teammates
have examined six distinct resolution strategies; all require either:
  (a) an order-isomorphism from `ChronicleSubtype` to a domain with `AddCommGroup`, or
  (b) bypassing the semantic route entirely via a syntactic derivation translation.

### 3. The Most Promising Path: Syntactic Derivation Translation

Of the two viable resolution strategies identified in the team research, the **syntactic
approach** is the one most likely to succeed without requiring new infrastructure or
mathematical pre-work.

The semantic approach (order isomorphism transfer via `Satisfies_orderIso`) has a concrete
structural obstacle: `ChronicleSubtype` for Base BX is a subtype of `ℚ` but there is
no established proof that it is densely ordered (density was shown only for the Dense BX
completeness variant). Without density, Cantor's theorem (`Order.iso_of_countable_dense`)
does not apply, and no isomorphism to `ℚ` or `ℤ` is available.

The **syntactic approach** bypasses the domain problem entirely:

1. Prove that `toBimodal` always produces box-free formulas (induction on `Temporal.Formula`).
2. Characterize which bimodal derivation rules produce box-containing conclusions (the
   modal axioms and `necessitation` rule do; all BX-type axioms do not).
3. Show by induction on derivation tree height that any TM-derivation whose conclusion is
   box-free can be projected to a BX-derivation.

The core proof obligation (step 3) is a form of "modal detour elimination": any intermediate
use of box in a proof of a box-free conclusion can be eliminated. This is structurally similar
to the normal form results that have already been established (the `liftDerivation` approach in
task 276, and the `lift_derivation_qfree` infrastructure in `Lifting.lean`).

**Critical check**: The `lift_derivation_qfree` infrastructure in
`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean` is specifically designed
for lifting derivations from subsystems. Its scope should be examined carefully — if it already
handles the temporal fragment projection, the sorry may be closeable with modest additional work.

### 4. Opportunity Cost Assessment

**Is the effort proportional to the value?**

Yes, for the following reasons:

1. **Build integrity**: A sorry in a top-level module that is suppressed via `set_option warn.sorry
   false` is a known-bad pattern in Mathlib-style libraries. It signals a result that is claimed
   but unproven. Resolving this restores mathematical integrity to the build.

2. **Conservativity chain completeness**: The 14 + 24 + 1 conservativity results (CPL, inter-modal
   cube, and S5) form a coherent hierarchy. The temporal branch of that hierarchy is the one
   explicitly missing. Completing it gives the full picture: every sub-logic is conservative over
   its predecessor in the bimodal hierarchy.

3. **The sorry is well-localized**: The file has three sorry-free proofs including the semantic
   bridge (`bimodal_truthAt_toBimodal_iff_temporal_satisfies`). Only one proof has a sorry. The
   work surface is narrow.

4. **Syntactic alternative is well-scoped**: The syntactic path does not require refactoring any
   existing proofs or adding new infrastructure to completeness. It adds a derivation projection
   lemma and uses it. Estimated effort is 3-6 hours of focused proof work.

**Are there simpler, more impactful alternatives?**

The ROADMAP.md remaining items are all completeness variants (discrete, continuous, dense for
bimodal and temporal). These are much larger undertakings than closing this sorry. Task 275's
sorry is the smallest remaining item by scope, making it the highest-value, lowest-cost item on
the roadmap.

### 5. Infrastructure Investments and Cross-Task Reuse

**If the semantic approach is eventually pursued**, the required infrastructure investments are:

| Investment | Created For | Cross-Task Reuse |
|------------|-------------|-----------------|
| `Satisfies_orderIso` lemma | Connecting temporal satisfaction across domains | Any future temporal logic that uses `TemporalModel` across different time domains |
| `ChronicleSubtype` density proof | Activating Cantor's theorem for base BX | Dense/discrete completeness proofs could also use this |
| `temporal_completeness_addcommgroup` variant | Avoiding domain mismatch in conservativity | Any future result connecting temporal derivability to bimodal validity |

**If the syntactic approach is pursued**, the required infrastructure is:

| Investment | Created For | Cross-Task Reuse |
|------------|-------------|-----------------|
| Derivation projection lemma (box-free conclusions) | Task 275 | Any future conservativity result between logics with modal depth differences |
| `toBimodal` box-free characterization | Task 275 | Documentation value, potentially reused in `TemporalEmbedding.lean` |

The syntactic infrastructure is more narrowly scoped but cleaner. The semantic infrastructure
(`Satisfies_orderIso`) has broader reuse potential for the completeness program.

### 6. Alternative Theorem Statements (Weakening)

**Could the result be usefully weakened?**

A weakened version that is immediately provable:

> If `φ.toBimodal` is TM-derivable, then `φ` is temporally valid on all serial linear
> orders with `AddCommGroup` structure.

This follows from `temporal_valid_on_addcommgroup` already proven in the file. But this
weaker statement is not mathematically interesting: temporal BX is axiomatized for ALL
serial linear orders (including non-group-structured ones), and the conservativity result
should cover that full class.

A more useful weakening:

> If `φ.toBimodal` is Dense-TM-derivable, then `φ` is Dense-BX-derivable.

For the Dense case, `ChronicleSubtype` IS densely ordered (by `DenseCompleteness.lean`),
so Cantor's theorem applies and the semantic approach works cleanly. This version could be
proved now and is a meaningful result (Dense-TM over Dense-BX conservativity).

However, the desired result (Base TM over Base BX) is the one needed for the main theorem.
Weakening it to the Dense case would require adding a new task and theorem, which adds
complexity without resolving the original gap.

**Could the theorem be marked `proof_wanted`?**

Lean/Mathlib does support `theorem foo : ... := by exact?` as a placeholder, but CSLib's
zero-debt policy makes this equivalent to sorry — it compiles but carries no proof. The
`set_option warn.sorry false` suppression already in the file indicates the sorry was
recognized as temporary. Replacing it with `proof_wanted` notation would make the status
more explicit but would not change the mathematical content.

**Recommendation**: Pursue the syntactic path to close this cleanly rather than weakening
or labeling it `proof_wanted`. The result is true, the proof path is identified, and the
infrastructure is manageable.

---

## Recommended Approach

### Primary: Syntactic Derivation Translation (3-5 hours)

1. **Study `Lifting.lean`** (`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean`)
   to understand what `lift_derivation_qfree` already handles. If the temporal-to-bimodal
   embedding preserves derivations in the right direction, the sorry may be closeable by
   invoking this infrastructure.

2. **Prove `toBimodal_boxFree`**: show by structural induction that `(φ : Temporal.Formula Atom).toBimodal`
   contains no `Formula.box` constructor. This should be ~5-10 lines in `TemporalEmbedding.lean`.

3. **Prove the derivation projection**: any TM-derivation of a `toBimodal φ` (which is box-free)
   can be projected to a BX-derivation of `φ`. The key step is showing that modal axioms and
   `necessitation` produce box-containing conclusions, so they cannot appear in a minimal
   derivation of a box-free formula. This is the main proof obligation (~50-100 lines).

4. **Instantiate in `temporal_valid_of_bimodal_derivable`**: given `h : ThDerivable φ.toBimodal`,
   extract the derivation tree, project it to a BX derivation, conclude `ThDerivable φ`, then
   use `completeness` to get validity.

### Fallback: Semantic with `ChronicleSubtype` Density Check (4-8 hours)

If step 3 above stalls on the modal detour elimination:

1. **Read `PointInsertion.lean`** and **`ChronicleConstruction.lean`** to determine whether
   Base BX's `limitDom` is densely ordered. Look for midpoint-insertion steps in the
   omega-chain construction.

2. **If density holds**: prove `DenselyOrdered (ChronicleSubtype A h_mcs)`, then use
   `Order.iso_of_countable_dense` to get `ChronicleSubtype ≃o ℚ`. Prove `Satisfies_orderIso`
   (~20-30 lines) and use it with `temporal_valid_on_addcommgroup` on `ℚ`.

3. **If density is not established**: this path requires proving the density property from
   scratch, adding ~1-2 hours of proof work before the main argument can proceed.

---

## Evidence and Examples

### Evidence that the sorry blocks the full build

Task 276 summary states (documented in research):
> "Pre-existing failure: `Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.TemporalConservativity`
> uses sorry (pre-dates this task; prevents full Cslib.lean build)"

The `set_option warn.sorry false` suppression on lines 242 and 267 shows the sorry was
intentionally isolated but not resolved.

### Evidence the Syntactic Path Is Plausible

The `lift_derivation_qfree` and `lift_derivation` patterns in the `ConservativeExtension/`
directory demonstrate that the codebase already uses derivation-tree induction for
conservativity proofs. Task 276's implementation of 24 inter-modal conservativity results
used exactly this technique. The temporal case extends it to a different fragment
(temporal formulas vs. propositional or modal formulas), which is the natural next step
in the same proof technique family.

The semantic bridge (`bimodal_truthAt_toBimodal_iff_temporal_satisfies`) is already proven
and shows that the embedding `toBimodal` correctly connects temporal and bimodal semantics.
The syntactic path uses the proof-theoretic analogue of this connection.

### Evidence of Well-Bounded Scope

The conservativity module currently has:
- 3 sorry-free proofs in `TemporalConservativity.lean`
- 1 sorry
- The sorry is in a self-contained theorem with a well-understood proof obligation

This is the smallest possible footprint for a meaningful gap: one sorry, one theorem, one
resolution path to investigate.

---

## Confidence Level

| Claim | Confidence |
|-------|------------|
| Task 275 sorry is the last blocker of full Cslib.lean build | **High** (documented in task 276 summary) |
| The mathematical gap is genuine (not a Lean artifact) | **High** (confirmed by all 4 teammates) |
| Syntactic derivation translation is a valid proof strategy | **High** (proof structure is well-understood in the literature) |
| `lift_derivation_qfree` already handles part of this | **Medium** (needs direct examination of that file's scope) |
| The effort is proportional to the value | **High** (smallest remaining item, unblocks full build) |
| Dense case of ChronicleSubtype is provable via Cantor | **Medium-High** (density likely holds; needs verification from PointInsertion.lean) |
| Weakening to Dense-only is useful as a fallback | **Medium** (mathematically meaningful but not the primary target) |
| Total implementation effort is bounded (3-6 hours) | **Medium** (syntactic path estimate; semantic path could be longer) |

---

## Summary for Planner

The result is **worth pursuing** and should be treated as the highest-priority remaining item
in the conservativity program. It is:

1. **The only sorry** preventing a full `Cslib.lean` build.
2. **Well-localized** to a single theorem with a clear proof obligation.
3. **Tractable** via the syntactic derivation translation approach.
4. **Not worth weakening** — the theorem is true and the proof path is identified.

The recommended action is to spawn an implementation task using the syntactic approach:
first studying `Lifting.lean` to check what `lift_derivation_qfree` handles, then proving
`toBimodal_boxFree` and the derivation projection lemma, then closing the sorry.
