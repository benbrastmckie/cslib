# Research Report: Shared Tableau Containment-Blocking Module (Blocking.lean)

- **Task**: 456 — shared_tableau_containment_blocking
- **Session**: sess_1785275816_a84520_456
- **Agent**: cslib-research-hard-agent (H2 anti-analysis, H3 Tier 1 reference grounding, H4 adversarial verification)
- **Date**: 2026-07-28
- **Literature**: `[lit:auto]` per-repo sub-index briefing (SUBINDEX_PRESENT, 34 docs, not sparse)

## Summary

The module design is settled and every load-bearing proof core has been **verified compilable
live** (three `lean_run_code` probes, all green). Two decisive corrections to the task
description surfaced:

1. **The dependency note resolves in favor of machine truth**: 456 lands FIRST, 317 consumes it.
   The `(ψ ∉ forced(x))` side-condition shape is already settled — by completed task 574, not by
   317 — and the correct design keeps that side condition OUT of the generic module.
2. **The task-description statement of `distinctTypes_le_pow` is false as literally written**
   (counterexample below). The provable formulation counts `Finset`-images over a **signed**
   universe; its 12-line proof is verified green.

Also: `GargGenoveseNegri2012` **already exists** at `references.bib:228` (do NOT add a
duplicate — the exact collision report 14 of task 317 warned about); only `DershowitzManna1979`
is genuinely missing, and its ready entry sits in task 317's report 05 §Q4.

## Source-to-Implementation Mapping (H3 Tier 1)

| Source Claim | BibKey | Verified against references.bib | Lean Target | Translation Notes |
|--------------|--------|--------------------------------|-------------|-------------------|
| Countermodel/termination via `Sfor`-containment: `Sfor` values live in the finite subset lattice of `Sub(φ)` and grow monotonically along accessibility; distinct forced-sets ≤ 2^n (§III, Def. III.4) | `GargGenoveseNegri2012` | YES (`:228`); **not in navigable corpus** — web-verified quotes preserved in `specs/574_.../reports/01_phase6-blocker-resolution.md:93-94` (574's own H3 honesty rule) | `Branch.typeAt`, `Branch.containmentBlocked`, `Tableau.distinctTypes_le_pow`, `Tableau.strictChain_le_card` | The strict-growth chain argument becomes `strictChain_le_card` (verified green); the 2^n count becomes the powerset-card bound |
| Blocking by shorter modal copy is **per-obligation**, not per-world (Technique 8.1/8.2, Def. 8.2) | `Massacci2000` | YES (`:1028`); IN corpus (`sources/massacci_2000_single_step_tableaux_for_modal_logics`, chunk_0029-0031 per index relevance note) | (scoping decision, not a definition) | Grounds why the `F(ψ)@x` conjunct stays in `intFImpReuseWitnessAnc?` (logic-specific), NOT in the generic module |
| Ancestor-directed loop check (Ch. 4) | `Fitting1983` | YES (`:211`); BibKey-only, provenance | (docstring provenance) | Same treatment as 574: provenance only |
| FMP / filtration bound `2^n`, box-plus machinery (Ch. 5) | `ChagrovZakharyaschev1997` | YES (`:75`); IN corpus | cross-check for `distinctTypes_le_pow` bound shape | Corroborates the exponent counts **signed** subformula occurrences |
| Multiset ordering for termination measures | `DershowitzManna1979` | **MISSING from references.bib** — ready entry in `specs/317_.../reports/05_fuel-sufficiency-literature.md:305-313` | `references.bib` addition (this task's deliverable) | CACM 22(8):465-476, 1979, doi 10.1145/359138.359142 |
| Branch data layer (Ch. V / Ch. 2) | `Smullyan1968`, `Fitting1983` | YES (`:236`, `:211`) | existing `Branch.lean` header refs | Blocking.lean should follow the same References-section style |

## Findings

### F1 — Dependency direction: 456 → 317 is correct; the side-condition question is already settled

The task description's "DEPENDS ON task 317 landing first (so the `(ψ ∉ forced(x))`
side-condition shape is settled)" is **stale**, and `specs/state.json` machine truth
(317 `dependencies: [456, 552]`; 456 `dependencies: [574]`) is correct. Evidence:

- Task 317's own latest research (`reports/14_blocker-analysis.md:124-130`) explicitly declares
  the old edge backwards and fixes the chain as **calculus-repair → 456 → 317**. The
  calculus-repair task became 574, which is **[COMPLETED]**.
- The side-condition shape was settled by 574, not 317: `intFImpReuseWitnessAnc?`
  (`Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean:260-284`) landed with the
  final 5-conjunct shape: (1) `isAccessible edges x w` (ancestor direction), (2) `x ≤ w`,
  (3) containment `Sfor(w') ⊆ forced(x)`, (4) `ψ ∉ forced(x)`, (5) explicit entry `F(ψ)@x`
  on the branch (Option-A; Massacci Def. 8.2 per-obligation shape, 574 decision D3/D4, measured
  not argued). Its spec lemma `intFImpReuseWitnessAnc?_spec` (`:293-320`) fixes the 5-tuple.
- Task 317's linear world bound is **refuted** (`reports/13:57,185` — "the linear world bound is
  FALSE; so is any world bound", pre-repair), so 317's only live world-bound route is the
  exponential bound this task provides (report 14:127-130, 153).

**Design consequence (settles what 317 consumes)**: conjuncts (1), (2), (4), (5) are
logic-specific — Temporal's blocking has entirely different side conditions (eventuality
duplication, `Temporal/Tableau/Branch.lean:141-162`) and no `F(ψ)@x` analogue. The generic
module therefore exposes **only** the containment test and the counting layer; each logic
conjoins its own side conditions. 317 keeps `intFImpReuseWitnessAnc?` exactly as 574 landed it
and consumes the counting layer.

### F2 — DEFECT: the task-description `distinctTypes_le_pow` statement is false as written

**Claimed statement** (task description and report 06 R2 API sketch):
`(b.labels.map b.typeAt).eraseDups.length ≤ 2 ^ U.length` for `U : List F` subformula-closed,
with `typeAt : ... → List (Sign × F)`.

**Counterexample** (4-element defect bar):
- *Counterexample input*: `F` = propositions over atoms `{p, q}`, `U = [p, q]` (so the claimed
  bound is `2^2 = 4`); branch `b` with 5 labels:
  `T(p)@1, F(p)@2, T(q)@3, F(q)@4, T(p)@5, T(q)@5`. Every formula on `b` is in `U`.
- *Current behavior of the claimed statement*: `typeAt` yields 5 pairwise-distinct lists
  (`[(pos,p)]`, `[(neg,p)]`, `[(pos,q)]`, `[(neg,q)]`, `[(pos,p),(pos,q)]`), so
  `eraseDups.length = 5 > 4`. The statement is unprovable.
- *Two independent falsity sources*: (a) **sign doubling** — types range over subsets of
  `Sign × U` (up to `4^|U|`, not `2^|U|`); (b) **list-order sensitivity** — `eraseDups` on
  `List (List _)` distinguishes `[(pos,p),(pos,q)]` from `[(pos,q),(pos,p)]`, so even `4^|U|`
  fails at the list level (ordered nodup lists over a 4-element universe number 65 > 16).
- *Required behavior / corrected statement* (**verified green**, 12-line proof compiled via
  `lean_run_code`): count `Finset`-images over a **signed** universe `V : Finset (Sign × F)`:

  ```lean
  lemma Tableau.distinctTypes_le_pow [DecidableEq F] [DecidableEq L] [BEq F] [LawfulBEq F]
      [BEq L] [LawfulBEq L] (b : Branch F L) (V : Finset (Sign × F))
      (hV : ∀ sf ∈ b, (sf.sign, sf.formula) ∈ V) :
      (b.labels.toFinset.image fun l => (b.typeAt l).toFinset).card ≤ 2 ^ V.card
  ```

  Instantiations recover the intended bounds exactly: at `V = Sub(φ) ×ˢ {pos, neg}` this is
  `2^(2·|Sub(φ)|)` — the "`≤ 2^n` time types, n = signed subformula count" of
  `Temporal/Tableau/Saturation.lean:71-74` — and the positive-projected variant over
  `U : Finset F` gives 317's `2^|Sub(φ)|` Sfor bound.
- *Isolation*: the defect is in the sketch's statement only; nothing in the codebase asserts the
  false form (Temporal's `Saturation.lean:74` comment is informal and consistent with the
  signed-universe reading).

### F3 — Verified module design for `Cslib/Foundations/Logic/Tableau/Blocking.lean`

All three proof cores below were compiled green in this session (`lean_run_code`, Mathlib
imports; only a style-whitespace lint in a probe, trivially fixed).

**Conventions** (match `Branch.lean` / `Measure.lean` siblings): `module` header,
`import Cslib.Init`, `@[expose] public section`, namespace `Cslib.Logic.Tableau`, References
section citing `[Fitting1983]`, `[GargGenoveseNegri2012]`, `[Massacci2000]`.

**Definitional layer** (cheap, BEq only):

```lean
/-- The forced type at a label: deduplicated (sign, formula) pairs at `l`. -/
def Branch.typeAt [BEq F] [BEq L] (b : Branch F L) (l : L) : List (Sign × F) :=
  ((b.filter fun sf => sf.label == l).map fun sf => (sf.sign, sf.formula)).eraseDups

/-- Positive-only forced type (the `Sfor` projection used by the intuitionistic tableau). -/
def Branch.posTypeAt [BEq F] [BEq L] (b : Branch F L) (l : L) : List F :=
  ((b.filter fun sf => sf.isPos && sf.label == l).map (·.formula)).eraseDups

/-- `l_new` is containment-blocked by `l_anc` when its type is contained in `l_anc`'s. -/
def Branch.containmentBlocked [BEq F] [BEq L] (b : Branch F L) (l_new l_anc : L) : Bool :=
  (b.typeAt l_new).all fun pair => (b.typeAt l_anc).any (pair == ·)
```

`typeAt` is **definitionally** Temporal's `timeType` at `F := Formula Atom, L := TimeIndex`
(`Temporal/Tableau/Branch.lean:113-116` is literally
`((b.filter (·.label == t)).map fun sf => (sf.sign, sf.formula)).eraseDups` after unfolding
`formulasAtTime`; `TBranch Atom` reduces to `Branch (Formula Atom) TimeIndex` via
`TSF`/`SignedFormula` abbrevs, `Rules.lean:56-59`). Same for `containmentBlocked` vs
`isSubsetBlocked` (`:119-122`). Note: `typeAt` canNOT be built on `Branch.formulasAt`
(`Branch.lean:81`) as the task description suggests — `formulasAt` discards the sign; the
filter-then-map keeping the sign is required (minor description correction).

**Spec lemma** (under `LawfulBEq`):
`containmentBlocked_iff : b.containmentBlocked l₁ l₂ = true ↔ ∀ x ∈ b.typeAt l₁, x ∈ b.typeAt l₂`
— routine `List.all_eq_true`/`List.any_eq_true` + `LawfulBEq` unfolding.

**Counting layer** (needs `DecidableEq`; `LawfulBEq` bridges `==` membership):

1. General Branch-free helper — **verified green**:
   ```lean
   lemma card_image_le_pow_of_forall_subset [DecidableEq β]
       (s : Finset α) (f : α → Finset β) (U : Finset β) (h : ∀ a ∈ s, f a ⊆ U) :
       (s.image f).card ≤ 2 ^ U.card
   -- Finset.card_le_card into U.powerset (via Finset.mem_powerset) + Finset.card_powerset
   ```
   Projection-agnostic, so `typeAt` (signed) and `posTypeAt` (Sfor) share it; no per-projection
   re-proof.
2. Bridge — **verified green**: `l.eraseDups.toFinset = l.toFinset` (via
   `List.mem_eraseDups : a ∈ l.eraseDups ↔ a ∈ l` under `LawfulBEq`, stdlib, confirmed present;
   note `List.eraseDups_eq_dedup` / `List.toFinset_dedup` do NOT exist — the membership route is
   the available one).
3. `Tableau.distinctTypes_le_pow` — F2's corrected statement; composition of 1+2 with
   `(b.typeAt l).toFinset ⊆ V` from `hV` + filter/map membership.
4. Pigeonhole corollary (the Temporal loop-detection core) — Mathlib lemma confirmed present:
   ```lean
   -- via Finset.exists_ne_map_eq_of_card_lt_of_maps_to
   lemma exists_typeAt_eq_of_card_lt ... :
       2 ^ V.card < b.labels.toFinset.card →
       ∃ l₁ ∈ b.labels, ∃ l₂ ∈ b.labels, l₁ ≠ l₂ ∧
         (b.typeAt l₁).toFinset = (b.typeAt l₂).toFinset
   ```
5. GGN strict-growth chain bound (317's world-bound core) — **verified green** (13-line proof:
   induction + `Finset.card_lt_card` + `omega`):
   ```lean
   lemma Tableau.strictChain_le_card [DecidableEq β] {k : Nat} (f : Nat → Finset β)
       (U : Finset β) (hchain : ∀ i, i < k → f i ⊂ f (i + 1)) (hU : f k ⊆ U) :
       k ≤ U.card
   ```

**Scope boundary (important)**: the "blocking ⇒ bounded" combinatorics above is fully
label-generic and lands here. The final "bounded ⇒ countermodel/unsat" step is **not**
expressible in Foundations — `Branch F L` carries no semantics; Temporal's `branchSat`
(`Soundness.lean:95-106`) quantifies over discrete-serial temporal models and 317's over Kripke
frames. Those remain consumer obligations (Temporal follow-up task; 317). This task supplies the
shared "≤ 2^n types" ingredient both were independently re-deriving — the stated
highest-value payoff — without claiming to discharge Temporal obligation 2 (`F(U)` propagation,
`Soundness.lean:36-44`), which is untouched by any counting lemma.

### F4 — Consumer instantiation map

| Consumer | What it takes | Refactor risk |
|----------|---------------|---------------|
| Temporal (`Temporal/Tableau/Branch.lean:106-122`) | Redefine `timeType b t := Branch.typeAt b t` and `isSubsetBlocked b t t' := Branch.containmentBlocked b t t'` (defeq redirections; `rfl` lemmas prove equivalence). `isTemporallyBlocked`/`findBlockedTime`/eventuality side conditions stay local. | LOW — defeq preserves the executable behavior; re-run the 24 temporal conformance rows (`CslibTests/TableauConformance.lean`) as the acceptance check. Consumers found: `Rules.lean:242,333,426`, `Saturation.lean:154-161,209`, `Closure.lean:90` — all go through `isTemporallyBlocked`/`findBlockedTime`, untouched. |
| Intuitionistic / 317 | Consumes counting layer only (`strictChain_le_card`, `distinctTypes_le_pow` via `posTypeAt`). `intFImpReuseWitnessAnc?` unchanged (574's settled shape). Optionally, its containment conjunct `sfor.all (forcedAtX.contains ·)` could later route through a shared `subsetOf` helper, but the prospective-world shape (`sfor` is the type of a world *not yet created*) means the `containmentBlocked b l_new l_anc` signature does not literally apply — do not force it. | NONE now (317 does its own consuming) |
| Bimodal (`Bimodal/Metalogic/Decidability/SignedFormula.lean:658-672`) | **Cannot instantiate**: uses its own local `SignedFormula` structure (`:221`) with compound labels filtered by projection `sf.label.time == t`, and its own `Branch` abbrev (`:274`). Lifting it requires migrating Bimodal to the Foundations types — a separate refactor task, out of scope. | Out of scope; record as follow-up opportunity |

### F5 — references.bib deliverable (corrected)

- `GargGenoveseNegri2012`: **already present** at `references.bib:228` (landed via the 574
  lineage). Task description is stale; report 14 (`317/reports/14:138-142`) explicitly warned
  the first lander should leave a note so the other avoids a duplicate key — this is that note.
  Optional enrichment from the fuller entry in `317/reports/05` §Q4: add
  `pages = {315--324}` and `doi = {10.1109/LICS.2012.42}` (current entry has neither); keep the
  existing key untouched otherwise.
- `DershowitzManna1979`: **genuinely missing** (grep exit 1). Ready entry
  (`317/reports/05_fuel-sufficiency-literature.md:305-313`):
  `@article{DershowitzManna1979, author = {Dershowitz, Nachum and Manna, Zohar}, title = {Proving Termination with Multiset Orderings}, journal = {Communications of the ACM}, volume = {22}, number = {8}, pages = {465--476}, year = {1979}, doi = {10.1145/359138.359142}}`.
- Cite `[GargGenoveseNegri2012]` and `[Fitting1983]` in Blocking.lean's docstrings as
  **provenance only** (574's H3 honesty rule: neither is in the navigable corpus;
  `Massacci2000` IS in the corpus and MAY be cited substantively for the per-obligation
  distinction).

### F6 — Reuse Check Protocol (all 5 steps exhausted)

1. **Foundations**: `Foundations/Logic/Tableau/` = {Branch, Sign, SignedFormula, RuleResult,
   ClosureCondition, Closure, PropositionalRules, Measure}. `Measure.lean` exists (the R1
   arithmetic extraction landed) but holds pure `Nat`/`List` arithmetic only — no type/counting
   layer. `Blocking.lean` does not exist. No overlap.
2. **Typeclass hierarchy**: no LTS/HasImp/etc. relevance; `Sign` derives
   `DecidableEq, BEq, Hashable` + explicit `ReflBEq`/`LawfulBEq` (`Sign.lean:51,96-100`);
   `SignedFormula` derives `DecidableEq, Hashable` (`SignedFormula.lean:57`) — all instances the
   module needs exist.
3. **Notation**: none proposed; none needed.
4. **Mathlib**: `Finset.card_powerset`, `Finset.card_le_card`, `Finset.mem_powerset`,
   `Finset.card_lt_card`, `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`,
   `List.mem_eraseDups` all confirmed present (local search + live compile). No ready-made
   image-into-powerset card bound exists — the 4-line composition is the minimal new lemma.
   Absent: `List.eraseDups_eq_dedup`, `List.toFinset_dedup` (bridge via membership instead).
5. **Logics namespaces**: the three duplication sites confirmed by direct read (Temporal,
   Bimodal, Intuitionistic); no fourth site (`grep` for
   `timeType|isSubsetBlocked|Sfor|typeAt|containmentBlocked` across `Cslib/`).

## Recommended Implementation Direction (for /plan)

1. **Phase A — Blocking.lean definitions + specs**: `typeAt`, `posTypeAt`,
   `containmentBlocked`, `containmentBlocked_iff`, membership lemmas
   (`mem_typeAt_iff`). ~80-120 lines. Scoped build.
2. **Phase B — counting layer**: `card_image_le_pow_of_forall_subset`,
   eraseDups/toFinset bridge, `distinctTypes_le_pow`, `exists_typeAt_eq_of_card_lt`,
   `strictChain_le_card`. All proof cores pre-verified green in this report. ~100-150 lines.
3. **Phase C — Temporal redirection**: `timeType`/`isSubsetBlocked` become defeq wrappers over
   the shared defs (+ `rfl` bridging lemmas); re-run temporal conformance rows.
4. **Phase D — references.bib**: add `DershowitzManna1979`; enrich (never duplicate)
   `GargGenoveseNegri2012`.
5. **Phase E — CI**: `lake exe mk_all --module` (new file → barrel), `checkInitImports`,
   scoped + full `lake build`, `lake exe lint-style`, `lake shake`, `lake test`. Zero sorry
   (nothing here needs one — every obligation has a verified route).

Explicit non-goals for the plan: no Temporal soundness discharge (obligations 1-2 of
`Temporal/Tableau/Soundness.lean:23-54` are consumer work needing semantics), no changes to
`intFImpReuseWitnessAnc?`, no Bimodal migration.

## Adversarial Self-Verification

| Claim | Source/Counterexample | Verdict |
|-------|----------------------|---------|
| Task-description `distinctTypes_le_pow` statement is provable as written | Counterexample F2: 5 distinct type-lists over `U = [p,q]`, bound 4; two independent falsity sources (sign doubling, list-order) | **REFUTED — reformulated**; corrected Finset-image statement's proof core compiled green |
| "456 depends on 317" (task-description text) | `state.json` (317 deps = [456, 552]); `317/reports/14:124-130` declares the old edge backwards; 574 [COMPLETED] settled the side-condition shape (`Expansion.lean:260-284`) | **REFUTED — machine truth confirmed**: 456 first, 317 consumes |
| `(ψ ∉ forced(x))` side condition must be settled inside Blocking.lean | Temporal's side conditions differ entirely (eventuality duplication, `Temporal/Tableau/Branch.lean:141-162`); Massacci Def. 8.2 per-obligation shape is logic-specific (574 D3/D4) | **REVISED**: side conditions stay per-logic; generic module = containment + counting only |
| `typeAt` can be built on `Branch.formulasAt` (task description) | `formulasAt` (`Branch.lean:81-82`) discards sign | **CORRECTED**: filter-then-map keeping sign; `formulasAt` unusable for the signed type |
| Both bib keys are missing (task description) | `grep references.bib`: GGN2012 present at `:228`; DershowitzManna absent (exit 1) | **PARTIALLY REFUTED**: only DershowitzManna1979 to add; GGN2012 enrich-only (duplicate-key hazard flagged by `317/reports/14:138-142`) |
| Temporal `timeType` is defeq to generic `typeAt` | Term-level comparison `Temporal/Tableau/Branch.lean:107-116` vs proposed def; `TBranch`/`TSF` abbrev chain (`Rules.lean:56-59`) | **CONFIRMED** (unfolding `formulasAtTime`); Phase C must still verify `rfl` closes in-situ — flagged as the one untested defeq claim (confidence: high, not compiled) |
| Counting/pigeonhole/chain proof routes exist in Mathlib | Live compiles: `card_image_le_pow` (12 lines), `eraseDups.toFinset` bridge, `strictChain_le_card` (13 lines); `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` confirmed by `#check` | **CONFIRMED — compiled green this session** |
| This task unblocks Temporal Phase 7 by itself | `Soundness.lean:36-44`: obligation 2 (`F(U)` propagation) is independent of any counting lemma | **SCOPED DOWN**: supplies the "≤ 2^n" ingredient of obligation 1 only; claim restated honestly in F3/F4 |
| Bimodal is a third instantiation site | `Bimodal/.../SignedFormula.lean:221,274,658-672`: local structure, compound label projection | **REVISED**: duplication confirmed but instantiation impossible without migration; excluded from scope |

**Zero-debt check**: no recommendation involves sorry, deferred proof, or new axioms; every
lemma in the recommended scope has a verified or routine route. **Forbidden-output check**: the
report prescribes a concrete module API with compiled proof cores and a phased direction — not
analysis-only. **BibKey check**: all citations verified against `references.bib` line numbers
above; the one missing key is itself a deliverable with ready text.

## Rate-Limit / Fallback Record

No rate-limited search failures. `lean_local_search` (2 calls), `lean_run_code` (2 calls) all
succeeded; `lean_leansearch`/`lean_loogle`/`lean_leanfinder` were not needed (local +
run-code verification sufficed).

## References (artifacts)

- `specs/574_tableau_calculus_repair_ancestor_blocking/{summaries/01,reports/01,plans/01,02}` — settled blocking shape, GGN web-verified quotes, D3/D4/D9
- `specs/317_propositional_tableau_completeness/reports/{05,06,13,14}` — bib entries (05 §Q4), R2 origin (06), world-bound refutation (13), dependency correction (14)
- `Cslib/Foundations/Logic/Tableau/{Branch,Sign,SignedFormula,Measure}.lean`
- `Cslib/Logics/Temporal/Tableau/{Branch,Saturation,Soundness,Rules,Closure}.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/{Expansion,Rules}.lean`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/SignedFormula.lean`
