# Research Report: Audit and Reduce maxHeartbeats Inflation (Task 453)

**Task**: Audit and reduce `maxHeartbeats` inflation across Bimodal/Temporal metalogic; normalize scoping to `in`-scoped.
**Date**: 2026-07-01
**Agent**: cslib-research-agent
**Type**: Code hygiene (no proof weakening; `lake build`/`lake test` must stay green)

---

## 1. Executive Summary

- **Current inventory: 64 `set_option maxHeartbeats` sites** under `Cslib/Logics/Bimodal/Metalogic/` and `Cslib/Logics/Temporal/Metalogic/` (the review headline "72" is stale; its own value breakdown summed to 67, and 3 sites have since been removed).
- **15 unscoped (file-wide) sites** and **49 scoped (`... in`) sites**. The 15 unscoped list from the description is exactly reproduced (see Section 3).
- **Mature dirs confirmed at ZERO**: `Foundations/`, `Computability/`, `Languages/`, `Crypto/` each have 0 `maxHeartbeats` sites. Inflation is entirely in the active logic metalogic area.
- **Worst offender confirmed**: `Temporal/Metalogic/Chronicle/CounterexampleElimination/MainElimination.lean:38` at **6400000** (32x default), governing one monolithic dispatch `def eliminatePotentialCounterexample` — a prime lemma-extraction target.
- **Independence confirmed**: Tasks 412/413/414 target `simp only [listImp_*, bigconj_*]` list normalization, NOT heartbeat budgets. Task 414 touches the same Modal/Temporal/Bimodal file *family* but a disjoint concern; only light file-level coordination is needed (Section 5).
- **Key structural finding**: the 15 unscoped options each sit at the top of an `@[expose] public section` (or before a run of declarations) and govern **many** declarations (5–40 each), not just one. Conversion to `... in` is therefore NOT a mechanical "attach to the next decl" — it requires a build-probe to find which declaration(s) actually exceed the 200000 default.

---

## 2. Complete Current Inventory (64 sites)

### Value distribution (verified vs description)

| Value | Multiple of default (200k) | Current count | Description's stated count |
|-------|---------------------------|---------------|----------------------------|
| 6400000 | 32x | 1 | 1 |
| 3200000 | 16x | 33 | 33 |
| 1600000 | 8x | 12 | 13 |
| 1200000 | 6x | 3 | 3 |
| 800000 | 4x | 11 | 12 |
| 400000 | 2x | 4 | 5 |
| **Total** | | **64** | 67 (headline "72" is inconsistent) |

Net drift since review: −1 at 1.6M, −1 at 800k, −1 at 400k (3 sites removed). The 3.2M and 6.4M offenders are unchanged.

### Full site list

**Bimodal/Metalogic (34 sites, all scoped except 2):**

| File | Line | Value | Scope |
|------|------|-------|-------|
| Algebraic/BooleanStructure.lean | 33 | 400000 | UNSCOPED |
| Algebraic/UltrafilterMCS.lean | 34 | 800000 | UNSCOPED |
| Decidability/CountermodelExtraction.lean | 547 | 1600000 | in |
| Decidability/CountermodelExtraction.lean | 598 | 800000 | in |
| Decidability/CountermodelExtraction.lean | 633 | 800000 | in |
| Decidability/CountermodelExtraction.lean | 666 | 3200000 | in |
| Decidability/CountermodelExtraction.lean | 721 | 3200000 | in |
| Decidability/CountermodelExtraction.lean | 776 | 3200000 | in |
| Decidability/CountermodelExtraction.lean | 828 | 3200000 | in |
| Decidability/Saturation.lean | 638 | 3200000 | in |
| Separation/DedekindZ/Cases.lean | 436 | 3200000 | in |
| Separation/DedekindZ/Cases.lean | 549 | 1600000 | in |
| Separation/DedekindZ/Cases.lean | 701 | 3200000 | in |
| Separation/DedekindZ/Cases.lean | 898 | 3200000 | in |
| Separation/DedekindZ/Cases.lean | 1217 | 3200000 | in |
| Separation/DedekindZ/Cases.lean | 1341 | 1600000 | in |
| Separation/DedekindZ/Cases.lean | 1496 | 3200000 | in |
| Separation/DedekindZ/QLemma.lean | 98 | 800000 | in |
| Separation/DedekindZ/QLemma.lean | 133 | 1600000 | in |
| Separation/DedekindZ/QLemma.lean | 223 | 1600000 | in |
| Separation/DedekindZ/QLemma.lean | 306 | 3200000 | in |
| Separation/Eliminations.lean | 81 | 800000 | in |
| Separation/Eliminations.lean | 179 | 800000 | in |
| Separation/Eliminations.lean | 263 | 800000 | in |
| Separation/Eliminations.lean | 377 | 3200000 | in |
| Separation/Eliminations.lean | 505 | 3200000 | in |
| Separation/Eliminations.lean | 533 | 1200000 | in |
| Separation/Eliminations.lean | 592 | 1200000 | in |
| Separation/Eliminations.lean | 704 | 1200000 | in |
| Separation/Hierarchy/HierarchyCaseSep.lean | 58 | 800000 | in |
| Separation/Hierarchy/HierarchyCaseSep.lean | 70 | 3200000 | in |
| Separation/Hierarchy/HierarchyCaseSep.lean | 84 | 800000 | in |
| Separation/Hierarchy/HierarchyCaseSep.lean | 104 | 3200000 | in |
| Separation/Hierarchy/HierarchyCaseSep.lean | 152 | 1600000 | in |
| Separation/Hierarchy/HierarchyCaseSep.lean | 255 | 3200000 | in |
| Separation/Hierarchy/HierarchyCaseSep.lean | 525 | 1600000 | in |

**Temporal/Metalogic (30 sites, 13 unscoped):**

| File | Line | Value | Scope |
|------|------|-------|-------|
| Chronicle/ChronicleToCountermodel.lean | 38 | 1600000 | UNSCOPED |
| Chronicle/CounterexampleElimination/MainElimination.lean | 38 | **6400000** | in |
| Chronicle/CounterexampleElimination/RecursiveWalks.lean | 37 | 3200000 | in |
| Chronicle/CounterexampleElimination/RecursiveWalks.lean | 580 | 3200000 | in |
| Chronicle/Frame.lean | 28 | 800000 | UNSCOPED |
| Chronicle/PointInsertion/Burgess.lean | 35 | 3200000 | UNSCOPED |
| Chronicle/PointInsertion/Seeds.lean | 36 | 3200000 | UNSCOPED |
| Chronicle/PointInsertion/Since.lean | 33 | 3200000 | UNSCOPED |
| Chronicle/PointInsertion/Splitting.lean | 32 | 3200000 | UNSCOPED |
| Chronicle/RRelation.lean | 29 | 1600000 | UNSCOPED |
| Chronicle/TruthLemma.lean | 40 | 3200000 | UNSCOPED |
| CompletenessHelpers.lean | 81,104,122,142,162,186,210,255 | 3200000 (x8) | in |
| Completeness.lean | 47 | 3200000 | UNSCOPED |
| DenseCompleteness.lean | 98 | 3200000 | in |
| DenseSoundness.lean | 32 | 1600000 | UNSCOPED |
| GeneralizedNecessitation.lean | 45,77,155 | 400000 (x3) | in |
| MCS.lean | 38 | 1600000 | UNSCOPED |
| Soundness.lean | 32 | 1600000 | UNSCOPED |
| WitnessSeed.lean | 29 | 800000 | UNSCOPED |

**Out of scope but noted**: 5 further `maxHeartbeats` sites exist elsewhere under `Cslib/Logics/` (outside the two Metalogic trees). Not part of this task; flag for a possible follow-up.

---

## 3. Unscoped Sites — Governed Declaration Analysis (Goal 3)

Each unscoped option sits above a run of declarations (most immediately followed by `@[expose] public section`, so it governs the whole section). "N decls" = number of top-level declarations after the option in the file.

| File:line | Value | # decls governed | Conversion difficulty |
|-----------|-------|------------------|-----------------------|
| Completeness.lean:47 | 3.2M | 2 (`neg_consistent_of_not_derivable`, `completeness`) | EASY — probe 2 |
| DenseSoundness.lean:32 | 1.6M | 6 (density_axiom_sound … soundness_thderivable_dense) | EASY — probe 6 |
| ChronicleToCountermodel.lean:38 | 1.6M | 5 (chronicleZero, 3 instances, chronicleModel) | EASY — probe 5 |
| Soundness.lean:32 | 1.6M | 8 (sat_and_iff … soundness_thderivable) | MEDIUM |
| TruthLemma.lean:40 | 3.2M | 10 | MEDIUM |
| Since.lean:33 | 3.2M | 10 (lemma24WithGuard … lemma24SinceWithGuard) | MEDIUM |
| Splitting.lean:32 | 3.2M | 11 | MEDIUM |
| WitnessSeed.lean:29 | 800k | 12 | MEDIUM |
| Frame.lean:28 | 800k | 14 | MEDIUM |
| BooleanStructure.lean:33 | 400k | 20 | MEDIUM |
| MCS.lean:38 | 1.6M | 23 | HARD |
| UltrafilterMCS.lean:34 | 800k | 24 | HARD |
| Seeds.lean:36 | 3.2M | 29 | HARD |
| Burgess.lean:35 | 3.2M | 38 | HARD |
| RRelation.lean:29 | 1.6M | 40 | HARD |

**Critical implication**: Because a single file-wide option covers up to 40 declarations, several of those declarations may *individually* exceed the 200000 default. The conversion is a build-probe, not a text move:

> **Probe procedure (per file)**: (1) delete the file-wide `set_option maxHeartbeats N` line; (2) `lake build <Module>`; (3) each declaration that fails prints `maxHeartbeats … exceeded` with its name; (4) add `set_option maxHeartbeats N in` immediately above *each* failing declaration (using the smallest passing value from a binary search, Section 4); (5) rebuild green. If exactly one declaration needs it, the file ends up with one scoped option — the ideal outcome. If several do, each gets its own scoped option (still strictly better than file-wide masking).

This procedure also automatically discovers whether the file-wide value was masking a *lower* real requirement (frequent, since these values are copy-paste defensive inflation).

---

## 4. Worst Offenders — Hotspot Analysis (Goal 2)

### 6.4M — `eliminatePotentialCounterexample` (MainElimination.lean:38)

- **Structure**: a single `noncomputable def … : EliminationResult χ pc := by` spanning lines 42–~1686 (the whole 1686-line file is essentially this one proof plus helpers). The proof `match h_kind : pc.kind`-dispatches across all counterexample kinds (`c5_forward`, `c5_backward`, `c6_forward`, `c6_backward`) and, within each, `by_cases` on `n=0` vs `n≥1`, chaining Burgess Lemma 2.4/2.7/2.8 and the recursive walks.
- **Why expensive**: one enormous tactic block ⇒ the elaborator carries the entire term/metavariable context across all four kinds at once. This is the classic case where the heartbeat cost is superlinear in a monolithic proof.
- **Restructuring recommendation (Category A)**: extract each `match` arm into its own top-level lemma:
  `eliminate_c5_forward`, `eliminate_c5_backward`, `eliminate_c6_forward`, `eliminate_c6_backward`, each returning `EliminationResult χ pc` under the appropriate `pc.kind = …` hypothesis. `eliminatePotentialCounterexample` then becomes a thin dispatcher (`match … | .c5_forward => eliminate_c5_forward …`). Each extracted lemma will have a *much* lower ceiling (likely 800k–3.2M each rather than 6.4M for the whole), and the dispatcher itself should need only the default. This is the single highest-value restructuring in the task.

### 3.2M cluster (33 sites)

The 3.2M value is heavily copy-pasted (33 occurrences), which is itself a strong signal of *defensive* rather than *measured* inflation. Notable sub-clusters:
- **CompletenessHelpers.lean** — 8 individually-scoped 3.2M options on `deriveDne`, `deriveHNec`, `deriveAndTopIntro`, `mcs_dne`, `mcs_ff_imp_f`, `mcs_pp_imp_p`, `mcs_g_trans`, `mcs_h_trans`. These are already correctly scoped (good pattern) but all at the same round 3.2M — prime candidates for binary-search downward.
- **DedekindZ/Cases.lean** — 5x 3.2M (lines 436, 701, 898, 1217, 1496), large case-split proofs; candidates for both lowering and, where a single `have` dominates, `have`-extraction.
- **CountermodelExtraction.lean** — 4x 3.2M (666, 721, 776, 828).
- **Eliminations.lean**, **HierarchyCaseSep.lean**, **RecursiveWalks.lean**, **Saturation.lean**, **DenseCompleteness.lean**, **QLemma.lean** — remaining 3.2M sites.

**Ceiling-lowering methodology** (for scoped sites): binary-search the smallest passing value. Bisect between 200000 and the current value, `lake build <Module>` at each step, and set the option to the smallest passing round value (e.g., next power-of-two multiple). Many 3.2M sites are expected to pass at 800k–1.6M. Round to the nearest sensible multiple to leave modest headroom (CI machines vary).

**Profiling for true hotspots**: for declarations that remain expensive after bisection, use `lean_profile_proof <fully.qualified.name>` to identify the dominating tactic/term (typically a single large `simp`/`decide`/`rcases` or an unfolding `set`/`let`), then extract that step into an intermediate `have`/lemma. (Profiling is SLOW and this metalogic area is heavy — reserve it for the residual offenders after bisection, not the whole inventory.)

---

## 5. Categorization (Goal 4)

**Category A — lower/remove ceiling via restructuring (highest value):**
- MainElimination.lean:38 (6.4M) — lemma-extract the 4 dispatch arms (detailed above).
- The 3.2M monolithic case-split proofs in Cases.lean, Eliminations.lean, HierarchyCaseSep.lean, RecursiveWalks.lean where a single dominating `have`/term can be extracted (identify via profiling after bisection).

**Category B — genuinely high, DOCUMENT with one-line justification:**
- Proofs that remain high after bisection + extraction because they are inherently large (multi-kind dispatch, large finite case analysis). For each, add a comment above the scoped option, e.g. `-- 8-way MCS case dispatch over Burgess Lemma 2.7; irreducible without deep refactor`. MainElimination's dispatcher and the extracted arms likely fall partly here even after extraction.

**Category C — unscoped → scoped conversion (mechanical, build-driven):**
- All 15 unscoped sites, via the probe procedure in Section 3. Ideal end state: each governs exactly the declaration(s) that need it, at the smallest passing value.

---

## 6. Independence Confirmation (Goal 5)

- **Task 412** (Foundations/Logic simp lists), **413** (Propositional simp lists), **414** (Modal/Temporal/Bimodal simp lists) all target `simp only [listImp_*, bigconj_*]` normalization — a *different* concern from heartbeat budgets. Verified against TODO.md descriptions.
- **Overlap note**: Task 414 edits the same Modal/Temporal/Bimodal file family. To avoid merge churn, this task (453) and 414 should not run concurrently on the same files. Since 453 changes only `set_option` lines (and, in Category A, extracts lemmas) while 414 changes `simp only` argument lists, conflicts are unlikely but possible in shared files. Recommend sequencing 453 before or after 414, not in parallel.
- Task 453 is otherwise self-contained.

---

## 7. Effort Estimate & Phase Ordering (Goal 6)

Every phase must end `lake build` + `lake test` green (zero-debt; no proof weakening).

**Phase 1 — Unscoped → scoped conversions (LOW risk, build-heavy). Effort: M.**
Process the 15 unscoped files with the Section 3 probe. Start with the easy small-count files (Completeness 2, DenseSoundness 6, ChronicleToCountermodel 5) to validate the procedure, then the HARD high-count files (RRelation 40, Burgess 38, Seeds 29). Deliverable: 0 unscoped sites remain; each scoped at its smallest passing value. This phase alone likely reduces several ceilings for free.

**Phase 2 — Bisect scoped ceilings (LOW–MEDIUM risk, build-heavy). Effort: M–L.**
Binary-search downward on the scoped sites, prioritising the 33x 3.2M cluster (esp. CompletenessHelpers' 8 identical values). Reduce to smallest passing round value with modest headroom. Deliverable: 3.2M count sharply reduced.

**Phase 3 — Restructure the 6.4M and residual monolithic 3.2M offenders (MEDIUM–HIGH risk). Effort: L.**
Lemma-extract `eliminatePotentialCounterexample`'s 4 arms; extract dominating `have`s in residual Cases/Eliminations/HierarchyCaseSep offenders identified via `lean_profile_proof`. This is the only phase that touches proof structure — highest regression risk; do last, one declaration at a time, rebuilding after each.

**Phase 4 — Document irreducibles + final gate (LOW risk). Effort: S.**
Add one-line justification comments above every remaining high (>= 1.6M, say) scoped option (Category B). Final `lake build` + `lake test` + `lake exe checkInitImports` + `lake exe lint-style`.

**Suggested wave ordering**: 1 → 2 → 3 → 4 (each is a green-gated commit). Phases 1 and 2 are safe, mechanical, and deliver most of the numeric reduction; Phase 3 carries the risk and should be isolated.

**Overall effort**: Medium-to-Large, dominated by build time in this heavy metalogic area (each `lake build <Module>` on these files is slow; a bisection is ~4–6 builds per site). Budget for build time, not reasoning time.

---

## 8. Grounding Notes & Caveats

- No proofs were built during research (this heavy metalogic area has very slow builds; profiling all 64 sites is infeasible within a research budget). The report therefore specifies a **build-driven probe/bisection methodology** for the implementation phase rather than pre-computed minimal values — the implementation MUST verify each proposed value/restructuring compiles green.
- The lemma-extraction recommendation for `eliminatePotentialCounterexample` is grounded in reading the proof structure (a `match pc.kind` dispatch with independent arms), which is mechanically extractable; the implementer should confirm each arm's exact hypothesis signature (`h_kind : pc.kind = …`) when extracting.
- Do NOT lower any ceiling below its measured passing value; leave modest headroom for CI-machine variance. Do NOT remove an option just because it *sometimes* passes at default — confirm with a clean build.
