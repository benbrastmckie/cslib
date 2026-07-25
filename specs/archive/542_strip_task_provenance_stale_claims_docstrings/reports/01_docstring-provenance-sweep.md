# Research Report: Strip Task/Phase Provenance and Stale Claims from Logic-Tree Docstrings

**Task:** 542 — Docstring hygiene (review 2026-07-23, M4/L8-L10)
**Type:** cslib (docstring/comment cleanup — no proof or definition changes)
**Scope:** `Cslib/Logics/{Modal,Propositional,Temporal,Bimodal}` + `Cslib/Foundations/Logic`
**Governing rule:** `.claude/rules/no-task-references-in-deliverables.md` (deliverables outside `specs/**` must not cite ephemeral task/phase metadata)

---

## 1. Executive Summary

- This is a **pure documentation hygiene** task: strip implementation-history narrative
  (task numbers, phase/plan references, rollout stories, `specs/NNN` path links, stale
  sorry/consumer claims) from shipped docstrings and comments, while **preserving mathematical
  contracts and literature references**. No proof, definition, or `import` changes.
- **Measured scope: ~1,300 high-precision provenance lines across ~163 files** in the five
  trees (Modal 971/86, Propositional 114/19, Temporal 88/22, Bimodal 91/27, Foundations/Logic
  35/9). This is broader than the review's ~918 estimate because it also captures lowercase
  `phase`, `plan vN`, `specs/NNN` links, and "guardrail/rollout/formerly" narrative.
- **Editing is judgment-based, not mechanical**: many lines mix provenance with live
  mathematical cross-references in the same sentence. A blind grep-delete would corrupt
  contracts and could leave declarations docstring-less (a `docBlame` lint failure).
- **Zero new definitions / zero sorries**: the reuse-first protocol and zero-debt gate are
  trivially satisfied — nothing is added, only prose removed. No Mathlib/CSLib API research
  was required.
- All four specific stale items were verified against the current tree. **Item (b) is already
  resolved** (task 543 softened it); items (a), (c), (d) are confirmed live and actionable.
- **No coordination conflict with task 438** — its two committed files (LambdaCalculus,
  LTL/GNBA) are entirely outside task 542's five-tree scope.

---

## 2. Coordinate-Task Status (freshness verified against `specs/state.json`)

| Task | Status | Bearing on 542 |
|------|--------|----------------|
| 543 `remove_dead_logic_modules_and_dead_end_bridges` | **completed** | Decided item (b): kept `Algebra/Bridge.lean`, already rewrote its docstring to a truthful "no in-tree consumer" statement. Item (b) needs no further action. |
| 438 `pr_task431_comment_cleanups` | **pr_ready** | Touched only `Languages/LambdaCalculus/Named/Untyped/Basic.lean` and `Logics/LTL/Semantics/GNBA.lean`. **Both outside 542 scope — no overlap.** |
| 425 `temporal_tableau_ptl_fmp_decidability` | **not_started** | Owns the live Temporal FMP gap referenced by item (c). |
| 301 `temporal_tableau` | **blocked** | Co-owns the live Temporal FMP gap (item c). |
| 226 `propositional_semantics_upstream_pr` | **researched** | Covers the DPLL/SAT upstream work forward-referenced in item (d). Reference is therefore removable. |
| 544 / 545 / 546 | **completed** | Freshness sources — verified below. |

**Freshness verification (renames/moves from 544/545/546):** All seven review-cited Modal files
still exist at their cited paths (`GenericMCSBridge.lean`, `MCS.lean`, `SchemaSoundness.lean`,
`ProofSystem/SchemaTags.lean`, `Constructive/Labelled/{PrimeLemma,Soundness}.lean`,
`Intuitionistic/TruthLemma.lean`). Line numbers in the review are approximate but the files are
current. Note task 544's renames (`ModalAxiom→S5Axiom`, `NIKTheorem→NIKDerivable`,
`_complete→_completeness`, conservativity → `<sys>_conservative_over_cpl`) are already reflected
in the tree; some docstrings narrate those very renames (`renamed from`, `formerly`) and are
prime deletion targets.

---

## 3. The Four Specific Items — Verification Findings

### (a) Bimodal Chronicle "one remaining sorry" — CONFIRMED STALE, actionable
`Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`
- Line ~51 docstring claims the `IsSuccArchimedean` discrete case "has one remaining sorry (the
  well-founded termination argument …)". Line ~426 says the non-dense branch is "(with sorry,
  like the discrete case)".
- **Verified: the file has NO live `sorry` token.** All three matches (`:51`, `:426`, `:815`)
  are inside comments/docstrings; `:815` is a correct "sorry-free BFMCS" statement. The file is
  sorry-free, so the (a) claims are stale and must be corrected to describe the completed
  construction (not a phantom gap).
- **Also here:** the `## References` section (line ~57) contains `Task 117 plan:
  specs/117_.../plans/04_case-split-completeness.md`. Keep the "Burgess 1982" literature line;
  delete the task/`specs/` line.

### (b) Propositional `Algebra/Bridge.lean` "ONE evaluation story" — ALREADY RESOLVED
`Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean`
- The file survived task 543 (completed) and its docstring was **already rewritten**. It now
  reads: "It has no in-tree consumer … this module is an independent algebraic reformulation
  rather than the route that chain uses." A grep for `canonical home` / `ONE evaluation story` /
  `single canonical` across all of Propositional returns **nothing**.
- **Recommendation: no action on (b)** beyond confirming during the sweep. (The parallel note in
  `Bool.lean` — "no in-tree consumer, not the canonical bridge for future work to route through"
  — is likewise already truthful.) Any remaining ordinary provenance in the file falls under the
  general sweep.

### (c) Temporal `Completeness.lean` commented-out proof carcass — CONFIRMED, actionable
`Cslib/Logics/Temporal/Tableau/Completeness.lean` (1,047 lines)
- Lines ~957–1045 are a single `/-! ### Remaining FMP-Blocked Obligations … -/` block
  containing **four ```lean-fenced commented-out lemma/instance carcasses** with commented
  `sorry` markers (`temporalTruthLemma_untl`, `temporalTruthLemma_snce`, `openBranch_branchSat`,
  `temporalTableau_complete`, `instDecidableValid`). The block also cites `task 439`,
  `task 426 Phase 3`.
- **Recommendation:** delete the fenced carcasses and the phase/task provenance; replace the
  whole block with a **one-line durable pointer** stating the mathematical gap, e.g.:
  *"The Until/Since eventuality-fulfilment cases of the truth lemma — and hence open-branch
  satisfiability, completeness, and the `Decidable (valid ·)` instance — remain blocked on PTL's
  Finite Model Property, which is not yet formalized."*
  Per the no-task-references rule the pointer must **not** name tasks 425/301; the mathematical
  statement (PTL FMP) is the durable anchor. Retain any live `temporalTruthLemma_propositional_aux`
  usage at the top of the section (line ~955 is real code, not carcass).

### (d) Propositional `Bool.lean` "Matthew Doty's forthcoming work" — CONFIRMED, actionable
`Cslib/Logics/Propositional/Semantics/Bool.lean` (lines 39–41)
- Docstring forward-references "A future DPLL/Tseitin/CNF procedure (Matthew Doty's forthcoming
  work — not yet in-tree) should refine these two declarations…".
- This DPLL/SAT upstream work is tracked by **task 226 (researched)**, so the rot-prone
  person-name/forthcoming reference is removable. Reword to drop the parenthetical while keeping
  the durable design contract: *"A future DPLL/Tseitin/CNF procedure should refine these two
  declarations and reuse this module's own `Bool ↔ Prop` bridge (`BoolEvaluate_eq_iff`,
  `Evaluate_eq_BoolEvaluate`, `tautology_iff_boolEvaluate_true`) rather than re-deriving it."*
  Keep the surrounding design notes and the `## References` literature block intact.

---

## 4. Provenance Inventory (for phase sizing)

### 4.1 High-precision provenance — near-always removable
Regex family: `Task/task N`, `Phase/phase N`, `sub-phase`, `plan vN`, `specs/NNN`, `now-deleted`,
`rollout`, `guardrail`, `renamed from/to`, `formerly`.

| Tree | Hits | Files |
|------|------|-------|
| `Logics/Modal` | 971 | 86 |
| `Logics/Propositional` | 114 | 19 |
| `Logics/Temporal` | 88 | 22 |
| `Logics/Bimodal` | 91 | 27 |
| `Foundations/Logic` | 35 | 9 |
| **Total** | **~1,299** | **~163** |

**Modal sub-area breakdown** (dominant tree):

| Sub-area | Hits | Files |
|----------|------|-------|
| `Tableau/` | 516 | 17 |
| `Metalogic/Constructive/` | 253 | 15 |
| `Metalogic/Intuitionistic/` | 86 | 7 |
| `ProofSystem/` | 39 | 16 |
| `Metalogic/InterSystem/` | 27 | 7 |
| `Metalogic/Systems/` | 21 | 15 |
| `Metalogic/Minimal/` | 6 | 2 |
| `Semantics/` + `Syntax/` | 1 | 1 |

**Heaviest single files** (>=30 hits): `Modal/Tableau/FrameCompleteness.lean` (103),
`Tableau/CompletenessLoop.lean` (73), `Tableau/LoopChecking.lean` (72),
`Metalogic/Constructive/CS5Canonical.lean` (64),
`Propositional/Tableau/Intuitionistic/Scheme.lean` (61),
`Metalogic/Constructive/Labelled/Soundness.lean` (58), `Tableau/FrameSoundness.lean` (56),
`Tableau/FmpMeasure.lean` (52), `Metalogic/Constructive/CS5.lean` (47),
`Metalogic/Constructive/Labelled/PrimeLemma.lean` (45), `Tableau/S5Simplification.lean` (41),
`Tableau/FiveSimplification.lean` (39), `Tableau/GenericDriver.lean` (36),
`Tableau/Completeness.lean` (32), `Intuitionistic/TruthLemma.lean` (31).

### 4.2 `specs/NNN` path links embedded in shipped docstrings — 24 lines, egregious
These hardcode task-directory paths (reports/plans/probes/handoffs) into shipped code and are the
clearest rule violations — the referenced files live under `specs/` (unshipped, renumbered by
vault ops). Files affected:
`Modal/Metalogic/Constructive/{CS4,CS5,CS5Canonical,CKExtension,Labelled/Completeness,Labelled/Soundness,Labelled/PrimeLemma}.lean`,
`Modal/Tableau/{FrameSoundness,FrameCompleteness,S5Simplification}.lean`,
`Bimodal/Metalogic/Separation/Hierarchy/HierarchyInduction.lean`,
`Bimodal/…/ChronicleToCountermodelBasic.lean`,
`Foundations/Logic/Metalogic/Chronicle/{ChronicleInterface,SinceSeedConsistency}.lean`.
**Treatment:** delete the `specs/` link; if it introduced a genuine technique note, replace with a
one-line mathematical description or a sibling-file/heading reference (durable anchor).

### 4.3 Judgment-required phrases — DO NOT mechanically delete (~93 lines)
`no longer` (43), `used to ` (28), `previously` (17), `bypassed` (2), `refactor` (4),
`migration` (1). These frequently describe live mathematics ("`R` is no longer symmetric on the
sub-frame", "used to build the canonical model"). **Each must be read in context**; delete only
when the sentence is about the *development history*, keep when it is about the *mathematics*.

---

## 5. Editing Methodology (constraints for the planner/implementer)

1. **Preserve mathematical contracts.** When a docstring line mixes a contract with provenance,
   excise only the provenance clause. Example transforms observed in the tree:
   - `/-! ## B (Symmetric Frame) Extraction (task 505 Phase 5)` → `/-! ## B (Symmetric Frame) Extraction`
   - `## Structure (schema-union rollout, Phase 5; simplified Phase 8 sub-phase 8.4)` → `## Structure`
   - `(hintikkaB_box_pos/hintikkaB_diamond_neg, Phase 6 below). -/` → `(hintikkaB_box_pos/hintikkaB_diamond_neg, below). -/`
     (keep the lemma-name cross-reference; drop the phase tag)
2. **Preserve literature references.** Keep author/year and BibKey citations (Burgess 1982,
   Chagrov & Zakharyaschev, `[ChagrovZakharyaschev1997]`, etc.). Only `specs/NNN` and task/phase
   references leave.
3. **`docBlame` guard (lint-prevention).** Every declaration must retain a docstring. Never delete
   a `/-- … -/` doc comment in full if it is a declaration's only docstring — strip provenance but
   leave the mathematical statement so the declaration stays documented.
4. **Durable-anchor substitution.** Where provenance explained "why this section exists," replace
   with the durable anchor the rule prescribes (sibling filename, section heading, or the
   mathematical fact) — never the task number. This is the exact pattern in item (c)'s one-line
   pointer.
5. **No behavioral change.** Verify with `lake build` that the target modules still compile; the
   edits touch only comment/docstring text, so a green build is the completeness check. (Use
   `lake build` per module rather than `lean_diagnostic_messages`, which is a blocked tool.)

---

## 6. Recommended Phase Decomposition

Sized so each phase is one agent run and one green `lake build` checkpoint. Modal is split by
sub-area because it holds ~75% of the hits.

1. **Phase 1 — Four specific items + `specs/` link purge.** Fix (a) Chronicle stale-sorry,
   (c) Temporal carcass→one-liner, (d) Bool.lean Doty reference; confirm (b) needs no change;
   delete all 24 `specs/NNN` docstring links. Highest-value, well-localized.
2. **Phase 2 — Modal/Tableau** (516 hits, 17 files). Largest bucket; the FrameCompleteness /
   CompletenessLoop / LoopChecking / FrameSoundness / FmpMeasure / S5Simplification cluster.
3. **Phase 3 — Modal/Metalogic/Constructive** (253 hits, 15 files) incl. Labelled/ subtree
   (PrimeLemma, Soundness, Context) and CS4/CS5/CS5Canonical.
4. **Phase 4 — Modal/Metalogic remainder + ProofSystem** (Intuitionistic 86, InterSystem 27,
   Systems 21, Minimal 6, ProofSystem 39; incl. SchemaTags:18-30).
5. **Phase 5 — Propositional + Temporal + Bimodal + Foundations/Logic** (~328 hits, ~77 files;
   remaining after Phase 1's item-specific edits). Includes the judgment-required §4.3 review.

Each phase ends with `lake build` of the touched modules; no cross-phase file ownership overlap.

---

## 7. Risks and Notes

- **Over-deletion risk (primary):** the §4.3 judgment phrases and inline contract+provenance
  mixing mean a mechanical sed pass is unsafe. The implementer must read each hit.
- **`docBlame` regression risk:** deleting a whole declaration docstring to remove provenance
  would trip the (weekly-cron) linter and, more importantly, degrade the library. Strip, don't
  nuke.
- **Zero-debt / reuse-first:** N/A in the usual sense — no code, definitions, axioms, or sorries
  are added or removed; nothing to introduce a sorry. No new abstraction, so the reuse-first
  check is vacuously satisfied.
- **Coordination:** task 438 (pr_ready) has no file overlap; tasks 425/301 own the Temporal FMP
  gap referenced (as math, not task numbers) by item (c)'s replacement pointer; task 226 covers
  the DPLL work so item (d) is safely removable; task 543 already handled item (b).
- **Blocked tools honored:** `lean_diagnostic_messages` and `lean_file_outline` were not used;
  verification relies on `grep` + `Read` + `lake build`.
