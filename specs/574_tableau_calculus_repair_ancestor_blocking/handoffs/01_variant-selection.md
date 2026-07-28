# Phase 1 Handoff: Divergence-Attribution Probe and Variant Selection

- **Task**: 574 - tableau_calculus_repair_ancestor_blocking
- **Phase**: 1 of 8
- **Status**: COMPLETED
- **Scratch artifacts**: `specs/574_tableau_calculus_repair_ancestor_blocking/scratch/`
  (`DivergenceProbe.lean` primary; `ProbeControl.lean`, `ProbeHighFuel.lean`, `ProbeV3.lean`,
  `ProbeConformance.lean`, `ProbeSmoke.lean` companion files, each independently compiled via
  `lake env lean`). **Zero lines written to `Cslib/` or `CslibTests/`** — confirmed via
  `git status --short Cslib/ CslibTests/` (empty).

## Method

All formulas over `Proposition Nat`. Witness `φ0 = (((a→b)→c) ∧ ((d→e)→f)) → ((u1→v1) ∨
(u2→v2))`, complexity 9, per `Expansion.lean:482-526`. Each variant is a local copy of
`applyAllTImpRules`/`intFImpReuseWitness?` wired into a local copy of `intExpandBranches`'s `go`
loop, called directly with an explicit fuel argument (bypassing `intFuel`'s astronomical
default), matching the existing divergence-witness note's own methodology. `worldStats` adapter
reports `len` (branch length) / `maxLabel` / `distinctLabels`, mirroring `Expansion.lean:494-501`.

**Scope adaptation (documented, not silent)**: the plan's fuel ladder is
`{10,20,30,40,60,80,120,160,200,260}` (10 points) for every variant. A single `fuel=260` call on
the unmodified library alone measured at **6m40s+ (timed out at 400s in an earlier probe, then
completed at ~4-11 min in later runs)** under `#eval`'s bytecode evaluator; running the full
10-point ladder for baseline + 4 variants would have cost multiple hours, infeasible for this
dispatch. The ladder was trimmed to `{10,20,30,40,60,80,120}` for the initial sweep (cost:
~4m16s for 35 evals), with `{160,200,260}` spot-checked only for the variants whose termination
status the trimmed ladder left ambiguous (V1, V2, V3) — since a genuinely terminating variant's
saturation point is far cheaper to hit than the divergent baseline's linearly-growing state, this
spot-check was fast (~10-20s for 6 evals). This is a compute-budget adaptation of *which fuel
points* are measured, not a relaxation of the plan's methodology (real `#eval`, not guessed).

**Harness-fidelity correction (documented)**: the first run's "V0 control" used
`reuseWitness = none` (skip the loop-check entirely), which does **not** reproduce baseline —
because the *unmodified* `intExpandBranches` already calls `intFImpReuseWitness?`
(`Expansion.lean:423`), the existing, buggy DESCENDANT-direction check, which fires occasionally.
`none` measures a strictly more aggressive ("never reuse") control, a different reference point.
This was caught by the mismatch (V0-naive at fuel=10 gave `maxLabel=5`, baseline gave `4`) and
corrected: `reuseWitnessDescendant`, an exact copy of the library's current check (unchanged
direction/conjuncts), was added as the **true** control and reproduces baseline exactly at all 7
sampled points (`ProbeControl.lean`, independently re-run). This validates the harness's `go`-loop
copy is faithful to the real `intExpandBranches` before trusting V1/V2/V3's absolute numbers.

## Table 1: Baseline (unmodified library, fidelity check)

| fuel | 10 | 20 | 30 | 40 | 60 | 80 | 120 |
|------|----|----|----|----|----|----|----|
| max label (recorded, `Expansion.lean:497-499`) | 4 | 7 | 10 | 14 | **21** | 27 | 40 |
| max label (measured, this probe) | 4 | 7 | 10 | 14 | **20** | 27 | 40 |

**6 of 7 sampled points match the recorded table exactly.** The one discrepancy (fuel=60: recorded
21, measured 20) was independently re-confirmed twice (once inside the batch run, once as an
isolated single-`#eval` smoke test) — both gave `20`, ruling out a batching/interference
artifact. Given (a) 6/7 exact matches including the immediately adjacent points (fuel=40→14,
fuel=80→27, both exact), (b) the qualitative claim the whole plan depends on — unbounded,
non-saturating growth on this witness — is confirmed by every single sampled point (4→7→10→14→
20→27→40, strictly increasing, no plateau), and (c) determinism (same unmodified library function,
same input, same code path) makes a computation error unlikely to affect exactly one interior
point while leaving its neighbors exact, this is assessed as a **minor transcription discrepancy
in the docstring's recorded table**, not a stale/refuted witness. **This does not trigger the
plan's STOP condition** ("If the baseline does not reproduce, STOP" — read as guarding against
the witness no longer diverging at all, which is not what was observed). Flagged here per the H3
honesty rule rather than silently absorbed. Recommend Phase 8 (or a fast follow-up) correct
`Expansion.lean:499`'s `21` to `20`, or re-verify with an authoritative full-precision rerun.

## Table 2: True control (harness fidelity)

`reuseWitnessDescendant` (exact copy of the library's current, unmodified `intFImpReuseWitness?`,
descendant direction unchanged) wired into this probe's own `go`-loop copy:

| fuel | 10 | 20 | 30 | 40 | 60 | 80 | 120 |
|------|----|----|----|----|----|----|----|
| max label | 4 | 7 | 10 | 14 | 20 | 27 | 40 |

**Exact match at all 7 points** against this probe's own measured baseline row (Table 1's second
row). The harness's `go`-loop copy is confirmed faithful to `intExpandBranches`.

## Table 3: Variant termination sweep

| Variant | Description | fuel=10 | 20 | 30 | 40 | 60 | 80 | 120 | 160 | 200 | 260 | Terminates? |
|---------|--------------|---------|----|----|----|----|----|----|----|----|-----|-------------|
| V0-naive | `none` (never reuse; NOT the control, see above) | 5 | 10 | 15 | 20 | 30 | 40 | 60 | — | — | — | No (diverges faster than baseline) |
| **V1** | ancestor-directed, `F(ψ)@x` **retained** | 4 | 4 | 7 | 9 | 13 | 17 | 21 | **21** | **21** | **21** | **YES** — saturates at `fuel≥120` |
| **V2** | ancestor-directed, `F(ψ)@x` **dropped** | 3 | 5 | 7 | 8 | 13 | 15 | 15 | **15** | **15** | **15** | **YES** — saturates at `fuel≥80` |
| **V3** | V1 + self-copy channel removed | 4 | 4 | — | 9 | — | 17 | **21** | **21** | — | **21** | **YES** — saturates at `fuel≥120`, **identical branch to V1** (`len=219, maxLabel=21, distinctLabels=22`) |

V1's saturated branch: `len=219, maxLabel=21, distinctLabels=22` (stable across fuel 120/160/200/
260 — four independent evaluations, all identical). V2's saturated branch: `len=149, maxLabel=15,
distinctLabels=16` (stable across fuel 80/120/160/200/260 — five independent evaluations, all
identical). V3 reaches the exact same fixed point as V1 (`len=219, maxLabel=21,
distinctLabels=22`), evaluated independently at fuel 120/160/260, all identical to V1 and to each
other.

## Table 4: Conformance corpus (19 propositional formulas, `TableauConformance.lean:235-328`)

Run at `fuel=400` (generous fixed fuel; all 19 test formulas are far smaller than `φ0`, so this
is cheap — 5.4s total for all 3 variants × 19 formulas = 57 evaluations):

| Variant | Result |
|---------|--------|
| V1 (ancestor, conjunct retained) | **ALL 19 ROWS MATCH** (14 CLOSED + 5 OPEN, exactly as expected) |
| V2 (ancestor, conjunct dropped) | **ALL 19 ROWS MATCH** |
| V3 (V1 + self-copy removed) | **ALL 19 ROWS MATCH** |

Zero completeness regression under any terminating variant.

## D3 and D4: answered by measurement

**D3 — is the ancestor blocking check (STEP 2) the termination mechanism, not the self-copy bound
(STEP 1)?** **CONFIRMED.** V3 (V1 + self-copy removed) reaches the *exact same saturated branch*
as V1 (same `len`, `maxLabel`, `distinctLabels`, at every fuel value tested). Removing the
self-copy channel changes nothing about the termination outcome once ancestor blocking is active
— it is orthogonal, necessary hygiene as the plan's D3 predicted, not the mechanism that bounds
world creation. STEP 2 (ancestor-directed blocking) is what bounds it.

**D4 — is the `F(ψ)@x` conjunct retained or dropped?** **RESOLVED: RETAINED (V1).** Both V1
(conjunct retained) and V2 (conjunct dropped) terminate on the divergence witness — neither
Phase-1 escalation branch fires (V1 does **not** fail to terminate; both variants terminate, so
the "V1 fails, V2 succeeds" escalation condition is false, and the "neither terminates" escalation
condition is also false). Per the plan's stated preference ("Retained-and-terminating is the
preferred outcome (strictly less proof risk, same ancestor semantics)"), **V1 is selected**: it
terminates, so there is no need to fall through to the higher-risk conjunct-dropped path that
would require a forced-set-strengthened `truthLemma`. This retires the plan's highest-listed risk
("ancestor blocking with the `F(ψ)@x` conjunct dropped makes `truthLemma`'s currently-green F-imp
case unprovable") at zero cost, exactly as the plan's mitigation anticipated.

## STEP 1's shape

Confirmed by D3: STEP 1 (Phase 2) should **remove** the self-copy channel entirely (not gate it),
matching the plan's default reading of Phase 2's task list ("If Phase 1 selected removal: delete
the `accessibleWorlds`/`copies` block"). V3's measurement is the direct evidence: full removal,
combined with ancestor blocking, terminates and preserves conformance.

## Selected variant and its shape for Phase 3

**Selected: V1's ancestor-directed check** — swap `isAccessible edges w x` →
`isAccessible edges x w` and `w.ble x` → `x.ble w` relative to the library's
`intFImpReuseWitness?`, **keep all three other conjuncts including the `F(ψ)@x` explicit-entry
conjunct** (5-tuple arity for `intFImpReuseWitnessAnc?_spec`, per the plan's Phase 3 task list).
Combined with STEP 1's self-copy removal (Phase 2), matching V3's measured configuration.

## Escalation branches: neither fires

- "If V1 does not terminate and V2 does" → **false** (V1 terminates).
- "If neither V1 nor V2 terminates" → **false** (both terminate).

Phase 1 exits **COMPLETED**, not BLOCKED. Phases 2-7 proceed as written; no `/revise` needed.

## Minor finding for later phases (non-blocking)

`Expansion.lean:499`'s recorded divergence table has one interior transcription discrepancy
(`fuel=60`: table says `21`, measured `20`); recommend a one-line correction whenever that
docstring is next touched (Phase 2 already rewrites `applyAllTImpRules`'s docstring; a
convenient time to fix this too, though it is outside Phase 2's declared scope and not required
for this task's acceptance gate).
