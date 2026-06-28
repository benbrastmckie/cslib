# Vet Review — `Logics/Propositional/` + `Foundations/` → ideal CSLib contribution

Scope: 105 files in `Cslib/Logics/Propositional/`, 87 in `Cslib/Foundations/` (192 total).
Method: full CI pipeline run centrally + 5 parallel standards/documentation reviews
(CONTRIBUTING.md, NOTATION.md, ORGANISATION.md). Read-only; no files edited.

---

## 1. CI pipeline ground truth (run centrally)

| Check | Result | Notes |
|---|---|---|
| `lake build` (full lib) | ❌ exit 1 | **Only** failure is out-of-scope `Logics/Modal/Tableau/Soundness.lean` (task 364, ~62 errors). In-scope everything builds **except** the orphan `IntFMPSpike.lean`. |
| `lake exe mk_all --check` | ❌ | 3 in-scope files unregistered in `Cslib.lean`: `IntFMPSpike`, `SequentCalculus/LK/Interpolation`, `Tableau/Intuitionistic/Scheme`. |
| `lake lint` | ❌ | 8 in-scope errors (see §3.6). |
| `lake exe lint-style` | ✅ | passes. |
| `lake shake` (`--add-public --keep-implied --keep-prefix`) | ⚠️ | aborts locally on "out of date oleans"; needs a clean cache-based run to get authoritative import-minimization. Flag as CI risk. |
| `lake test` | ❌ | same out-of-scope Modal file. |
| Build warnings (in scope) | 140 | 56 unused-simp-args, 25 long-lines, 14 `unusedSectionVars`, 10 dead tactics, 7 flexible-`simp`, 6 `sorry`, 4 barrel header. |

Bottom line: the **branch as a whole is red** because of out-of-scope task-364 Modal work.
Propositional+Foundations themselves are green-with-warnings except the orphan `IntFMPSpike`.

---

## 2. Loose-end inventory (hard facts)

- **14 `sorry`** across 4 files — **6 LIVE** (shipped via `Cslib.lean`), **8 PARKED** (unimported).
- **0** `admit`, `native_decide`, `proof_wanted`, `#eval`/`#check`/`#print` leftovers.
- **1 broken file**: `Metalogic/IntFMPSpike.lean` (12 errors, unimported).
- **3 real `TODO`**: `StackTape.lean:33`, `Euclidean.lean:18`, `SequentCalculus`/normalization "deferred" notes.
- **11 `set_option`** (maxHeartbeats inflation / linter suppression) needing justification.

---

## 3. TIER 1 — Blockers for any clean PR (correctness / build / CI)

### 3.1 Six LIVE `sorry` underwriting shipped decision procedures  — **CRITICAL**
`Tableau/Intuitionistic/Completeness.lean:89,98,112` and `Tableau/Minimal/Completeness.lean:168,179,190`.
These transitively underwrite the **advertised, shipped** instances
`instDecidableIValid`, `instDecidableMValid`, `instDecidableDerivable{Int,Min}PropAxiom`,
`intuitionisticTableau_decides`, `minimalTableau_decides` — they only typecheck because of `sorry`.

Sorry ledger:
| file:line | lemma | missing content | difficulty |
|---|---|---|---|
| IntCompleteness:89 | `intTruthLemma` | full truth-lemma induction (imp-case world-creation/persistence; bot-case openness) | High |
| IntCompleteness:98 | `intuitionisticOpenBranch_countermodel` | extract openness+saturation+F(φ)@0 from tableau; needs expansion-loop structural lemmas | Med–High |
| IntCompleteness:112 | `intuitionisticTableau_complete` | build ℕ-world Kripke model, upward-closure, `IValid` — mechanical once :98 lands | Medium |
| MinCompleteness:168 | `minTruthLemma` | same induction w/ `botForces = minBranchBotForces b` | High |
| MinCompleteness:179 | `minOpenBranch_countermodel` | analogue of :98 | Med–High |
| MinCompleteness:190 | `minimalTableau_complete` | analogue of :112 (also pulls :89–:112 transitively) | Medium |

⚠️ **Blocking design risk**: the saturation hypothesis they rest on is mis-stated
(`Intuitionistic/Completeness.lean:83`, `Minimal/Completeness.lean:162`, `Scheme.lean:224`):
`hsat : ∀ sf ∈ b, intStepBranch b [] 0 = none` does not depend on `sf`, so it collapses to
`b ≠ [] → intStepBranch b [] 0 = none` and fails to capture per-world/accumulated saturation.
**Restate saturation faithfully before attempting the truth lemmas.**

### 3.2 `Metalogic/IntFMPSpike.lean` — broken scratch — **CRITICAL**
Task-370 "de-risking spike" toward intuitionistic FMP/decidability. 12 LSP errors:
parse error `unexpected token 'Σ'` from binder names `hψ'Σ`/`hab_Σ` (L231,254…); missing
`import Mathlib.Data.Finset.Powerset` (L105); `private` vs `@[expose] public section` visibility
clash (L113); wrong lemma names `Set.mem_coe` (L148); a real induction bug in
`intFinWorld_propConsistent` (L163–177). Self-describes as "NOT a committed deliverable" and
references a `specs/370_…` path. Structure salvageable; one proof (consistency induction) is real work.
**Disposition: delete, OR fix 5 mechanical errors + consistency induction, strip spike framing,
rename → `IntDecidability.lean`, add to `Cslib.lean`.**

### 3.3 `SequentCalculus/LK/Interpolation.lean` — incomplete, unimported — **CRITICAL**
4 `sorry` in `private maeharaCore` (`andR`:311, `orL`:315, `impL`:319, `impR`:323); exports **no**
public theorem; not in `Cslib.lean` nor `LK.lean` barrel. Header advertises `maeharaCore` as a
"Main Result". **Disposition: complete the 4 cases + add public `craigInterpolation` + wire in, OR delete.**

### 3.4 `Tableau/Intuitionistic/Scheme.lean` — orphan parametric refactor — **CRITICAL**
4 parked `sorry` (`truthLemma`:230 over `IntMinScheme`; `openBranch_countermodel` obligations
:268/:276/:284). Not in `Cslib.lean`. Duplicates the int/min completeness scaffolding (task 317/369).
Module-mode inconsistency (`import` vs `module`/`public import`). **Disposition: finish + wire in
(replacing the int/min duplication and the §3.1 sorries via the parametric route), OR delete.**
Note `:284` has a ready-to-copy classical analogue `classicalExpandBranches_openBranch_initial_mem`.

### 3.5 `mk_all` failure
Caused entirely by 3.2–3.4 being unregistered. Resolving those (complete-and-wire or delete) clears it.

### 3.6 `lake lint` errors (8 in scope)
- `Metalogic/GenericMCSBridge.lean:133,165,192` — underscore `def` names `deriv_tree_to_list`,
  `unfold_listImp_in_tree`, `list_deriv_to_tree`; `:133` also `def` should be `lemma` (`defLemma`).
- `Subformula.lean:173` — `vars_neg` `simpNF` (LHS simplifies).
- `Tableau/Classical/Expansion.lean:125` (`classicalExpandBranches.processNext`),
  `Tableau/Intuitionistic/Expansion.lean:169` (`intExpandBranches.go`),
  `Tableau/Intuitionistic/Rules.lean:91` (`isAccessible.go`) — `docBlame` (undocumented `def`).
- `Metalogic/DeductionTheorem.lean:85` (`deductionWithMem` arg 9) and
  `Tableau/Intuitionistic/Completeness.lean:60` (`intBotForces` arg 1) — unused-argument lints.

---

## 4. TIER 2 — Standards/quality for an "ideal" contribution

### 4.1 Namespace decision (library-wide) — **DECISION REQUIRED**
All 35 Propositional source files (96 occurrences) open `namespace Cslib.Logic.PL`, but
`ORGANISATION.md:223` mandates `Cslib.Logic.Propositional` (which Modal/Temporal/Bimodal follow).
`PL` is an undocumented abbreviation; path is `Logics` (plural) vs namespace `Logic` (singular).
**Either** rename the subtree `Cslib.Logic.PL → Cslib.Logic.Propositional`, **or** amend
ORGANISATION.md to sanction `PL`. Must be applied consistently.

### 4.2 `NaturalDeduction/Normalization/Termination.lean` + `Reduction.lean` — heavy debt
- **~800–1000 line abandoned fuel/measure normalization track** living alongside the constructive
  proof that actually proves the results (`snForm`→`exists_stronglyNormal_form`). Unused:
  `redexWeight` (+lemmas) 311–433; `normMeasure`/`normMeasure_wf`/`reduceRoot_decreases_normMeasure`/
  `reduceRootSubSN`/`subs_maximalFormulas_mem`/`subsOne_new_redex_complexity_lt` 1107–1375;
  `normalize`/`normalizeAux` (Reduction 84–105); `normalizeAux_fixpoint` 289. `normalize`/
  `normalizeAux_fixpoint` are `public` (API removal). **Delete the dead track or finish + wire it in.**
- `maxHeartbeats 1200000` (L1177, 6×) and `2000000` (L1580, 10×) — uncommented; flagged by linter.
- 56 unused `simp` args, 20 no-op/dead tactics, 25 long-lines, 7 flexible-`simp` (this file dominates).

### 4.3 `Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean` — only hard docBlame in Foundations
7 undocumented **`def`/`abbrev`**: `fld`(50, also rename → `himpFold`), `fmeLe`(106), `fmeEquiv`(123),
`fmeSetoid`(125), `FreeMeetExtension`(152), `mk`(159), `freeMeetEmbed`(257). Fails `lake lint`.

### 4.4 Barrel header defects (4 files) — source of "Copyright too short!" lint
`Tableau.lean`, `Tableau/Classical.lean`, `Tableau/Intuitionistic.lean`, `Tableau/Minimal.lean`
are bare `import` lists: no copyright block, no `module`, no `import Cslib.Init`, plain `import`
instead of `public import`. (Cf. `SequentCalculus.lean` for the correct form.)

### 4.5 `unusedSectionVars` (14 theorems) — add `omit`
Mostly `Tableau/Classical/Completeness.lean` (12: `classicalTruthLemma`,
`classicalBranchComplexity_*`, `classicalExpMeasure_*`, `classicalStepBranch_*`, …),
`Tableau/Minimal/Soundness.lean:118`, `Tableau/Minimal/Completeness.lean:89`.

### 4.6 Broken citation key — doc build will not resolve
`Semantics/Algebra/OrImpConservative.lean` cites `[NegriVonPlato2001]`, undefined in `references.bib`
(also 15 out-of-scope SequentCalculus files). **Add the BibTeX entry** (Negri & von Plato,
*Structural Proof Theory*, CUP 2001).

### 4.7 `ORGANISATION.md` is stale
Propositional section lists only `Defs/NaturalDeduction/ProofSystem/Metalogic` — omits the entire
`Semantics/` + `Semantics/Algebra/` (28 files), `Tableau/`, `SequentCalculus/`, `CurryHoward/`.
`Foundations/Logic/` omits the `Tableau/` subtree, 7 of 9 `Metalogic/` files, and
`Theorems/Temporal/FrameConditions.lean`. Namespace section conflicts with §4.1.

### 4.8 NOTATION.md arrow inconsistency (Foundations)
`Semantics/LTS/Notation.lean:69,71,76,78` (and `Relation/Attr.lean:42–51`) mix Option-C triangle
head `⭢` with Option-A bracket/`↠` forms — matches no single NOTATION.md option. Commit to A or C.
`HasTau.lean` missing saturated `⇒`/`➾` notation.

---

## 5. TIER 3 — Polish / hygiene

### 5.1 Internal task/process jargon in public docstrings — strip
`ClassicalConjImpCompleteness.lean:19,23,51,57`; `ClassicalConjImpBotCompleteness.lean:18,23,37,52,
61–64,178,475–478` ("task 352/378", "CL-A/B/C rung", "4-for-4"); `ConservativeChain.lean:44–45`;
`HilbertLindenbaumRel.lean:21–23` ("Route A2", "341 proof files"); `Connectives.lean:21,39,41,
144–146` (PR #607, task 340/173); `Tableau/RuleResult.lean:35`, `PropositionalTableau.lean:7`;
`IntFMPSpike` `specs/370_…` reference; `ListImplication.lean:83–139` stream-of-consciousness.

### 5.2 Stale/incorrect docstrings — fix counts
`IntSoundness.lean:20,39` "3 axioms" → 9 cases; `MinSoundness.lean:20,40` "2" → 8;
`IntStrongCompleteness.lean:96` & `MinStrongCompleteness.lean:108` "3 cases" → 5;
`IntLindenbaum.lean:320` docstring belongs to `int_consistent`, misattached to `lift_int_to_cl`;
`Tableau/{Intuitionistic,Minimal}/DecisionProcedure.lean` "4 sorries" → 3;
`Minimal/Completeness.lean:50–51` "Notes on sorry" omits :179/:190.

### 5.3 Dead declarations (grep-verified 0 uses) — delete or wire in
`Tableau/Classical/Soundness.lean:73–138` (12 `classicalApplyOne_*` simp lemmas, also undocumented),
`:486`; `Tableau/Classical/Completeness.lean:435,447`; `Tableau/Defs.lean:81` (`propImpOrNegOf?`);
`Tableau/Intuitionistic/Rules.lean:114,203` (+ stale comments); `Intuitionistic/Soundness.lean:431,505`;
`NaturalDeduction/Equivalence.lean:305` (`hilbertAxiomToND`); `SequentCalculus/LK/Completeness.lean:69,73`
(`mem_insert_left/right`, generic Finset lemmas in PL namespace).

### 5.4 Underscore `def` names (Mathlib lowerCamelCase) — rename
`ProofSystem/Derivation.lean:77` (`modus_ponens` constructor); `LK/CutElimination.lean:147,295,439,
588,712` (`cutAdm_*`); `LJ/CutElimination.lean:120,230,353,465,546` (`ljCutAdm_*`);
`IntLindenbaum.lean:321` (`lift_int_to_cl`); `Combinatorics/InfiniteGraphRamsey.lean:82`
(`goodSelection_seq`); `Data/HasFresh.lean:38` (`to_infinite`); `Relation/Domain.lean:30`
(`emptyHrelation_apply`). Also "Extention"→"Extension": `Defs.lean:190,195`, `Equivalence.lean:257`.

### 5.5 Large reuse / dedup (Zulip-coordinate per CONTRIBUTING — cross-cutting)
- 3 Lindenbaum-algebra constructions (~2,100 lines): `HilbertLindenbaum`, `HilbertLindenbaumRel`,
  `HilbertAlgCompleteness` (+ 4th out-of-scope in Bimodal). Factor one generic quotient construction.
- 3 Classical completeness files (~700 lines): `litCtx_congr'` copied verbatim 3× — make public &
  parameterize over the axiom predicate via `GenericMCSBridge` (`HasMinimalAxioms`).
- 3 Soundness modules share one induction; 8 conservativity modules; LJ/LK near-identical helper families.

### 5.6 Foundations/Logic items (from area review)
- **Delete `Foundations/Logic/Tableau/PropositionalTableau.lean`** — bare-comment "DEPRECATED…
  superseded" but still in build, duplicates `Tableau/` types.
- **`Foundations/Logic/Tableau/ClosureCondition.lean:78,98`** — dual bare `instance`s
  (`ClassicalClosure`, `IntuitionisticClosure`) on the same head → ambiguous resolution. Make `def`s.
- `ProofSystem.lean` ~40 axiom-class fields undocumented; `Theorems/Temporal/FrameConditions.lean:52–87`
  6 anonymous undocumented instances + namespace omits `Theorems`.
- `Metalogic/DeductionHelpers.lean:48` namespace `Cslib.Logic` vs sibling `Cslib.Logic.Metalogic`.
- `Foundations/Data/ListHelpers.lean` namespace `Cslib.Logic.Helpers` under `Data/`;
  `Foundations/Data/PFunctor/Free.lean` non-`Cslib` namespace + duplicates `Control/Monad/Free.lean`.

### 5.7 Misc
- `OmegaSequence/` re-implements much of `Mathlib.Data.Stream'` — build on `Stream'` or document fork.
- `HilbertLindenbaum.lean:700,756` possible HA/BA instance diamond.
- `@[simp]` on global completeness biconditionals (`StrongCompleteness:558`, `Int…:338`, `Min…:333`) —
  reconsider as default rewrites.
- 5 `linter.tacticAnalysis.verifyGrindOnly false` set_options (Foundations) — justify or remove.
- Monolithic proofs to decompose: `Classical/Completeness.lean:84–429` (~345 lines),
  `Classical/Soundness.lean:150–408` (~258), `Intuitionistic/Soundness.lean:1083–1574` (~491),
  `SubformulaProperty` (~230), `LJ/SubformulaProperty` (~165).
- `Data/DecidableEqZero.lean:11` empty `/-! -/` header; `Data/StackTape.lean:33`/`Euclidean.lean:18` TODOs.

---

## 6. Suggested fix-task grouping

1. **`tableau-completeness-sorries`** (Tier 1): restate saturation, discharge 6 live sorries
   (or land the Scheme parametric route). Largest math item.
2. **`dispose-parked-incomplete-files`** (Tier 1): decide+execute on `IntFMPSpike`, `LK/Interpolation`,
   `Intuitionistic/Scheme` (complete-and-wire or delete) → fixes `mk_all`.
3. **`fix-lake-lint-errors`** (Tier 1): the 8 `lake lint` failures (§3.6).
4. **`namespace-decision`** (Tier 2, decision): rename `PL`→`Propositional` or bless `PL` in doc.
5. **`termination-deadcode-cleanup`** (Tier 2): delete abandoned normalization track + heartbeat/simp debt.
6. **`docstring-and-header-fixes`** (Tier 2): FreeMeetExtension docBlame, 4 barrel headers,
   `unusedSectionVars` omits, broken `NegriVonPlato2001` citation.
7. **`update-organisation-md`** (Tier 2): bring ORGANISATION.md in sync with the real trees.
8. **`docstring-jargon-and-stale-counts`** (Tier 3): strip task-number jargon, fix stale counts.
9. **`dead-code-and-naming`** (Tier 3): remove dead decls, rename underscore defs / "Extention".
10. **`reuse-consolidation`** (Tier 3, Zulip first): dedup Lindenbaum/Classical/conservativity families.
11. **`foundations-logic-cleanup`** (Tier 3): delete deprecated PropositionalTableau, fix ClosureCondition
    instances, namespace/doc fixes, NOTATION arrow consistency.
