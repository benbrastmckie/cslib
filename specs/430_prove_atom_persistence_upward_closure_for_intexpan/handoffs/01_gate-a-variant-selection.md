# Phase 1 Handoff: Gate A — Variant Selection Probe (V1 vs V4), Re-run Against Post-Phase-6 Tree

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Phase**: 1 of 8
- **Status**: COMPLETED
- **Scratch artifact**: `scratch/VariantProbe.lean`, independently compiled/evaluated via
  `lake env lean` against the CURRENT library (real `intExpandBranches`, `intStepBranch`,
  `intFImpReuseWitnessAnc?`, `isAccessible`, `intTImpRule`, `Branch.extendMany` imported
  directly; only the persistence-fixpoint step is locally varied). **Zero writes to `Cslib/` or
  `CslibTests/`** — confirmed via `git status --short Cslib/ CslibTests/` (empty).

## Method

Witness `φ0 = (((a→b)→c) ∧ ((d→e)→f)) → ((u1→v1) ∨ (u2→v2))`, complexity 9, copied verbatim
from `CslibTests/TableauConformance.lean`'s divergence-witness row (same `Proposition Nat`
atom encoding, `.atom 0`..`.atom 9`). Each variant is a local copy of the go-loop
(`goV1`/`goV4`), reusing the REAL `intStepBranch`/`intFImpReuseWitnessAnc?`/`isAccessible`
unchanged, with only `applyAllTImpRules`/`applyPersistenceFixpoint` locally varied:

- **True control**: the REAL `intExpandBranches` (and the real `intuitionisticTableau` entry
  point), called directly with an explicit fuel argument, both against `φ0`.
- **V1**: self-copy channel reinstated verbatim, i.e. exactly the `accessibleWorlds`/`copies`/
  `combined` block `a70187dd` removed (copied from `a70187dd^:Expansion.lean`).
- **V4**: generalized channel — copies EVERY positive-signed formula on the branch (not just
  `T(φ→ψ)`) to accessible worlds lacking it.

`worldStats` adapter reports `(verdict, maxLabel, branchLength)`, mirroring
`Expansion.lean`'s own divergence-witness methodology (max world label reached).

## Table 1: Harness fidelity (true control)

| fuel | 120 |
|------|-----|
| `expandControl phi0 120` (local go-loop copy, real persistence step) | OPEN, maxLabel=21, len=219 |
| `intuitionisticTableau phi0` (real entry point) | OPEN, maxLabel=21, len=219 |

**Exact match, both against each other and against 574's own recorded V3 measurement**
(`len=219, maxLabel=21, distinctLabels=22`, Table 3 of
`specs/archive/574_.../handoffs/01_variant-selection.md`). The harness's go-loop copy is
confirmed faithful to the real `intExpandBranches`, and the current tree's behavior on `φ0`
matches the historical record before trusting the variant measurements below.

## Table 2: Variant termination sweep

| Variant | fuel=10 | 20 | 40 | 80 | 120 | 160 | 200 | Terminates? |
|---------|---------|----|----|----|----|-----|-----|-------------|
| **V1** (self-copy reinstated verbatim) | maxLabel=4 | 4 | 9 | 17 | **21** | **21** | **21** | **YES** — saturates at `fuel≥120`, `len=219` |
| **V4** (generalize to every positive) | maxLabel=4 | 4 | 9 | 17 | **21** | **21** | **21** | **YES** — saturates at `fuel≥120`, `len=219` |

**Both V1 and V4 saturate at the IDENTICAL fixed point as the control**
(`len=219, maxLabel=21`), stable across four fuel values (120/160/200, plus the ladder points
below). No divergence detected for either variant on this witness.

## Table 3: Conformance corpus (20 rows, `CslibTests/TableauConformance.lean`'s
`PropositionalCorpus`, copied verbatim into `confCorpus`)

Checked at `fuel=400` (generous fixed fuel):

| Variant | Result |
|---------|--------|
| V1 | **ALL 20 ROWS MATCH** (`[true, true, ..., true]`, 20 entries) |
| V4 | **ALL 20 ROWS MATCH** (`[true, true, ..., true]`, 20 entries) |

Zero completeness regression under either variant.

## Decision

Per the plan's stated rule ("V4 if it saturates and all conformance rows match; otherwise fall
back to V1"): **both variants pass**, so **V4 is selected** — it is the higher-value target
(makes the persistence invariant hold at ALL formula shapes via a single generalized channel,
not just `T(φ'→ψ')`), and this run empirically retires the plan's flagged risk that "V4
diverges" (report 17 H4 row 7's concern about positives feeding the `.pos,.imp` BETA arm):
measured behavior shows no such divergence on this witness, at any sampled fuel point.

**Escalation branches**: neither fires. "If neither V1 nor V4 terminates" is false (both
terminate). Phase 1 exits COMPLETED, not BLOCKED.

## Selected variant for Phase 3

**V4**: generalize `applyAllTImpRules`'s copy channel to copy every positive formula (not just
`T(φ→ψ)`) to every accessible world lacking its own copy, in addition to the existing
ψ-consequence propagation (`intTImpRule`, unaffected). This is the shape Phase 3 should
reinstate/generalize in `Expansion.lean`.
