# Research Report: Frame-Specific Modal Tableau Extensions (Task 300)

**Task type:** cslib | **Session:** sess_1784044325_11ad9e_300 | **Date:** 2026-07-14
**Builds on:** Task 299 (Modal K tableau, COMPLETED, sorry-free) + Task 442 (FMP fuel measure)

## Executive Summary

Task 300 extends the completed, sorry-free modal **K** tableau
(`Cslib/Logics/Modal/Tableau/`) with frame-specific rules for **T** (reflexive),
**S4** (reflexive-transitive), **S5** (equivalence), **B** (symmetric), and **5**
(Euclidean). The single most important finding is that **frame-condition satisfaction of
the extracted countermodel is essentially free**: Mathlib's relation-closure operators
(`Relation.ReflGen`, `ReflTransGen`, `SymmGen`, `EqvGen`) each ship with the exact
frame-property typeclass instance the completeness proof must exhibit
(`Std.Refl`, `IsTrans`, `Std.Symm`, `IsEquiv`). The recommended architecture extracts the
countermodel with a **closed** accessibility relation `r := Cl(acc.hasEdge)` and reads the
frame property directly off the Mathlib instance.

The hard part is **not** frame-condition satisfaction and **not** soundness — it is
**termination for S4** (and any transitive-but-not-symmetric system). The K tableau's
termination rests on an a-priori world bound (`modalWorldBound φ`, `FmpMeasure.lean:144`)
proved via a ~1,650-line rank-map + potential-function argument that is *specific to K* and
**provably breaks under transitive box propagation** (`T(□◇p)` spawns an unbounded diamond
chain). S4 therefore requires genuine **loop-checking / subset-blocking**, which does not
currently exist and must be built from scratch. In contrast, **S5 avoids loop-checking
entirely** via the "propagate-to-all-worlds" equivalence-class simplification inherited from
the Bimodal tableau — the extracted relation is universal-on-cluster, trivially an
equivalence relation.

**Zero-debt honesty note:** The task's 1,200–1,800-line estimate is realistic only for the
**T + B + S5** subset. The K FMP measure alone was 2,959 lines; the S4 loop-checking
termination argument replaces that entire crux and is a comparably large, high-risk
deliverable. The **5 (pure Euclidean)** system has **no Mathlib closure operator** and is the
highest-risk item. This report recommends a phased decomposition (below) so that no phase is
forced toward a `sorry`.

---

## 1. Existing K Tableau Architecture (verified declaration names)

Namespace `Cslib.Logic.Modal.Tableau` (note singular `Logic`), directory
`Cslib/Logics/Modal/Tableau/`. Variable context everywhere:
`{Atom : Type*} [DecidableEq Atom] [Hashable Atom]`.

### Data structures
- `Model World Atom := ⟨r : World → World → Prop, v : World → Atom → Prop⟩` — `Basic.lean:64`.
- `Satisfies m w φ` — `Basic.lean:146`; `box φ ↦ ∀ w', m.r w w' → Satisfies m w' φ`,
  `diamond φ ↦ ∃ w', m.r w w' ∧ Satisfies m w' φ`.
- `WorldIndex := Nat` — `Defs.lean:59`.
- `Accessibility := ⟨edges : List (WorldIndex × WorldIndex)⟩` — `Branch.lean:55`; ops
  `empty`, `addEdge`, `successorsOf`, `hasEdge`, `allWorlds`.
- `SignedFormula (Proposition Atom) WorldIndex` (Foundations, generic).

### Rules (all inline in one dispatcher)
- `modalApplyOne sf b acc : RuleResult … × Accessibility` — `Rules.lean:70`. The four K modal
  rules are inline arms: `boxPos`/`diamondNeg` are `.persistent` (re-fire on new successors);
  `diamondPos`/`boxNeg` are `.linear` and mint a fresh world `modalNextWorld b`.
- Helpers: `boxPositivesOf` (`Branch.lean:183`), `boxPropagation` (`Branch.lean:197`).

### Soundness (`Soundness.lean`, `SoundnessStep.lean`)
- `kValid φ := ∀ (World) (m : Model World Atom) (w), Satisfies m w φ` — `Soundness.lean:322`
  (quantifies over **all** models; no frame restriction).
- `modalTableau_sound (φ) (h : modalTableau φ = .closed) : kValid φ` — `Soundness.lean:331`.
- `branchSatisfiable b acc : Prop` — `SoundnessStep.lean:63`:
  `∃ W (m : Model W Atom) (f : WorldIndex → W), (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) ∧ …`.
  **Key contract: `m.r` is a *superset* of the syntactic `acc` edges** (one-directional). Adding
  frame edges to `m.r` is always sound.
- `modalStepBranch_preserves_sat` — `SoundnessStep.lean:207` (the "satisfiable ⇒ some child
  satisfiable" invariant; all rule cases inline, keyed off `cases sign; cases formula`).
- `accFreshInv b acc` — `SoundnessStep.lean:156` (freshness side-invariant).

### Completeness (`Completeness.lean`, `CompletenessLoop.lean`, `Saturation.lean`, `Closure.lean`)
- `extractModel b acc : Model WorldIndex Atom` — `Completeness.lean:59`:
  `r w w' := acc.hasEdge w w' = true`; `v w p := (T(atom p)@w ∈ b)`.
- `modalHintikkaSet b acc : Prop` — `Saturation.lean:234` (four-conjunct saturation: open +
  rule-outputs-present + box-neg witness + diamond-pos witness).
- `modalTruthLemma b acc (hH) : ∀ φ w, (T(φ)@w ∈ b → Satisfies (extractModel b acc) w φ) ∧
  (F(φ)@w ∈ b → ¬ Satisfies …)` — `Completeness.lean:474` (strong induction on `modalComplexity`).
  Bridge lemmas: `hintikka_box_pos` (:146), `hintikka_box_neg` (:198),
  `hintikka_diamond_pos` (:211), `hintikka_diamond_neg` (:230).
- `modalOpenBranch_countermodel` — `Completeness.lean:627`.
- `modalTableau_complete` — `CompletenessLoop.lean:1290`;
  `modalTableau_decides` — `CompletenessLoop.lean:1334`; `instDecidableKValid` (:1346).
- `isModalClosed b` — `Closure.lean:57` (closes on `T(⊥)@w` or `T(φ)/F(φ)` at the **same** label).

### Termination (`FmpMeasure.lean` — 2,959 lines; `Saturation.lean`)
- Fuel-based recursion: `modalExpandBranches` recurses on `fuel : Nat` (`Saturation.lean:140`).
- `modalFuel φ` — `Saturation.lean:94` (triple-exponential closed form in `modalComplexity φ`).
- Fuel sufficiency: `modalExpMeasure` (`FmpMeasure.lean:197`, a `Σ 3^(|U\b|+|U\e|)` counting
  measure) strictly decreases (`modalExpMeasure_step_lt`, :2873) and is ≤ fuel at entry
  (`modalExpMeasure_entry_le_fuel`, :208).
- **A-priori world bound (the K-specific crux):** `modalWorldBound φ = (2·complexity+1)^(complexity+1)`
  (`FmpMeasure.lean:144`), proved a loop invariant via `modalStepBranch_worldBound` (:2376),
  backed by a rank map + potential function `ModalPotentialInv` (:2116), `modalStepBranch_potential_step`
  (:2146). **This argument is K-specific; transitivity breaks the depth bound.**
- Subformula closure: `modalSubfmls` (:73), `modalUniverse` (:149).
- `LoopInduction.lean` is a red herring — one `Forall₂` list lemma, no reusable loop principle.

---

## 2. Reusable Mathlib API — the key enabler (all verified via loogle)

`Mathlib.Logic.Relation` provides relation-closure operators, **each carrying the frame-property
instance the completeness proof needs**:

| System | Closure operator | Frame instance (free) | Verified name |
|--------|------------------|-----------------------|---------------|
| **T** | `Relation.ReflGen r` | `Std.Refl (ReflGen r)` | `Relation.reflexive_reflGen`, `Relation.ReflGen.instRefl` |
| **S4** | `Relation.ReflTransGen r` | `Std.Refl` + `IsTrans` | `Relation.reflexive_reflTransGen`, `Relation.transitive_reflTransGen`, `Relation.instIsPreorderReflTransGen` |
| **S5** | `Relation.EqvGen r` | `IsEquiv` + `Equivalence` | `Relation.EqvGen.instIsEquiv`, `Relation.EqvGen.is_equivalence` |
| **B** | `Relation.SymmGen r` | `Std.Symm` | `Relation.SymmGen.instSymm` |
| **5** | *(none — no `EuclGen`)* | — | **must be built** |

Useful subrelation glue: `Relation.EqvGen.reflGen_le_eqvGen`,
`Relation.EqvGen.reflTransGen_le_eqvGen`, `Relation.EqvGen.symmGen_le_eqvGen` (for relating a
system's closure to the S5 equivalence closure). Constructors/eliminators
`ReflTransGen.refl`, `.single`, `.trans`, `.head`, `.tail`, and `ReflTransGen.head_induction_on`
/ `.trans_induction_on` drive the truth-lemma box case.

**Every equivalence relation is Euclidean**, so S5 (via `EqvGen`) gets the 5-axiom frame
condition for free; only the *pure* 5 / K5 / KB5 systems (Euclidean-without-full-equivalence)
lack a ready closure operator.

---

## 3. Reusable CSLib API (reuse-first findings)

CSLib already contains the semantic frame vocabulary — **do not define new frame predicates**:

- Frame-condition typeclasses used throughout the Modal metalogic:
  `Std.Refl m.r`, `Std.Symm m.r`, `IsTrans World m.r`, `Relation.RightEuclidean m.r`,
  `Relation.Serial m.r` (`Cslib/Foundations/Relation/Euclidean.lean` supplies the Euclidean
  API, e.g. `RightEuclidean.symm`, `rightTotal_equiv`, `refl_serial`).
- Frame **classes** already defined in `Cslib/Logics/Modal/Cube.lean`:
  `T := logic {m | Std.Refl m.r}` (:33), `B` (:37), `Four := {m | IsTrans …}` (:41),
  `Five := {m | Relation.RightEuclidean …}` (:45), `S4` (:81), `S5` (:85), plus D-family.
  A frame-restricted validity target for the tableau should be phrased against these (or the
  underlying `{m | Std.Refl m.r}` predicate), not a fresh definition.
- **Axiom-validity theorems already proved semantically** (reuse in the soundness arms):
  `Satisfies.t` (`Basic.lean:286`, needs `Std.Refl m.r`), `Satisfies.b` (:323, `Std.Symm`),
  `Satisfies.four` (:348, `IsTrans`), `Satisfies.five` (:376, `Relation.RightEuclidean`).
- **Canonical-model frame-condition patterns** in `Metalogic/Systems/{T,S4,S5}/`:
  `s5_axiom_sound` (`S5/Soundness.lean:38`) takes `h_refl`, `h_trans`, `h_eucl` as the frame
  hypotheses and derives B/T/4 validity — the same hypothesis-threading style the tableau
  soundness arms should mirror. `s4_strong_completeness` / `t_strong_completeness` show the
  established shape for frame-restricted completeness statements.

### Foundations tableau layer (generic, reuse directly)
`Cslib/Foundations/Logic/Tableau/` (`SignedFormula`, `Branch`, `RuleResult` with
`.persistent`, `ClosureCondition`, `PropositionalRules`, `Measure`) is fully label-generic and
already parameterizes the K tableau. `RuleResult.persistent` was explicitly designed for these
downstream modal/temporal tasks; transitive/reflexive propagation rules are `.persistent`.

---

## 4. Formalization Direction (concrete, per system)

### Design principle: closure-at-extraction (recommended over edge-materialization)
Two strategies exist. **Strategy A (materialize all frame edges into `acc`, extract with raw
`hasEdge`)** requires the tableau to explicitly add every reflexive/transitive edge and prove
`Std.Refl`/`IsTrans` of the *finite list relation* by hand. **Strategy B (recommended):** keep
`acc` holding only the tableau's direct edges, and extract with a **closed** relation:

```lean
def extractModelT (b) (acc) : Model WorldIndex Atom where
  r w w' := Relation.ReflGen (fun x y => acc.hasEdge x y = true) w w'
  v w p  := b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)
-- Frame condition: `Std.Refl (extractModelT b acc).r` := Relation.reflexive_reflGen  (FREE)
```

Analogously `extractModelS4` uses `Relation.ReflTransGen`, `extractModelB` uses
`Relation.SymmGen`, `extractModelS5` uses `Relation.EqvGen` (or the universal relation, below).
Strategy B makes the frame condition a one-liner and confines all new work to the **truth
lemma** (the box/diamond bridges must be re-proved for the closed relation), which is exactly
where the frame-specific saturation rules pay off.

### Soundness generalization (shared across all systems)
`kValid` and `branchSatisfiable` must be relativized to a frame class. Introduce a
relation-predicate parameter:

```lean
def frameValid (FC : ∀ {W}, (W → W → Prop) → Prop) (φ) : Prop :=
  ∀ (W) (m : Model W Atom) (w), FC m.r → Satisfies m w φ
def branchSatisfiableIn (FC …) (b) (acc) : Prop :=
  ∃ W (m : Model W Atom) (f), FC m.r ∧ (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) ∧ …
```

Instantiate `FC := (Std.Refl ·)` for T, `(IsTrans _ ·)` for 4, etc. Each new rule's soundness
arm discharges using the corresponding `Satisfies.t/b/four/five` lemma. The existing "superset"
contract already permits `m.r` to carry extra (frame-forced) edges, so the K arms port
unchanged.

### T (reflexive) — LOW risk
- **Rule:** `T(□φ)@w ⊢ T(φ)@w`; dually `F(◇φ)@w ⊢ F(φ)@w`. Both are `.persistent`, add
  formulas only at **existing** worlds — **no new worlds created**.
- **Termination:** world count unchanged from K; the `modalWorldBound`/potential argument
  extends with modest work (enlarge `modalUniverse` to include the reflexive outputs, which are
  already subformulas → still inside `U(φ)`). Reuse `modalWork_drop_persistent`.
- **Frame condition:** `Std.Refl (extractModelT …).r` via `Relation.reflexive_reflGen`.
- **Truth lemma:** box-pos bridge additionally needs `T(φ)@w ∈ b` from the T-rule at the
  reflexive self-edge `ReflGen.refl`.

### B (symmetric) — MODERATE risk
- **Rule:** the symmetric box rule — if `T(□φ)@w` and edge `v→w` recorded, then `T(φ)@v`;
  operationally, box-positives propagate **backward** along recorded edges. Dually for `F(◇)`.
- **Termination:** backward propagation adds formulas at existing worlds (no new worlds beyond
  K's diamond/box-neg minting), so the world bound survives; measure side reuses persistent
  machinery. Risk is in getting the backward-propagation saturation conjunct right.
- **Frame condition:** `Std.Symm (extractModelB …).r` via `Relation.SymmGen.instSymm`.

### S4 (reflexive-transitive) — HIGH risk (the crux)
- **Rules:** T-rule (reflexive, above) **plus the 4-rule**: `T(□φ)@w`, edge `w→w'` ⊢
  `T(□φ)@w'` **and** `T(φ)@w'` (propagate the *box itself* transitively). Dually
  `F(◇φ)@w ⊢ F(◇φ)@w'`.
- **Termination is the problem.** Transitive box propagation makes `T(□◇p)@w` regenerate a
  fresh diamond witness at every new world → **unbounded**. The K a-priori `modalWorldBound`
  (depth-based) is **not** a loop invariant here. **Loop-checking / subset-blocking is
  required** and must be built (see §5). The new termination bound is
  `#worlds ≤ 2^|modalSubfmls φ|` (number of distinct saturated formula-sets), not a depth power.
- **Frame condition:** `Std.Refl` + `IsTrans` of `Relation.ReflTransGen` (free).
- **Truth lemma:** box-pos bridge re-proved by induction on the `ReflTransGen` path
  (`ReflTransGen.head_induction_on`), using the 4-rule to carry `T(□φ)` along each edge and the
  T-rule for the reflexive endpoint.

### S5 (equivalence) — MODERATE risk; NO loop-checking (the "simplification")
- **Key insight:** S5 satisfiability has the single-cluster model property. Use the **Bimodal
  tableau's "propagate box to ALL worlds on the branch"** rule (universal, not
  successor-restricted). This creates no transitive regeneration problem: every box-positive
  lands on every existing world, and each fresh diamond world simply joins the one cluster.
  World count stays K-bounded (each diamond mints ≤ once per formula), so **loop-checking is
  unnecessary**.
- **Frame condition:** extract with the **universal** relation `r w w' := True` (trivially an
  equivalence relation — reflexive/symmetric/transitive/Euclidean), or `Relation.EqvGen` if a
  tighter model is wanted; `Relation.EqvGen.instIsEquiv` gives it for free.
- This is the `S5Simplification.lean` deliverable and should be developed **independently of**
  (and can precede) the S4 loop-checking work.

### 5 (pure Euclidean) — HIGHEST risk
- **No Mathlib `EuclGen` closure operator exists.** Options: (a) define a custom inductive
  Euclidean closure and prove `Relation.RightEuclidean` of it (novel, unbudgeted); (b) restrict
  scope to **KB5/S5** where Euclideanness comes bundled inside `EqvGen`/equivalence; (c) note
  that K5's finite-model construction is itself subtle (Euclidean frames have a specific cluster
  shape). **Recommend:** deliver 5 only via the S5/KB5 equivalence route in this task, and split
  a **standalone pure-K5 Euclidean-closure task** if genuine Euclidean-only completeness is
  required. If forced into pure-5 with no closure operator and no time, mark that phase
  **[BLOCKED]** — do **not** introduce an axiom or `sorry`.

---

## 5. The S4 Loop-Checking Problem (detailed)

The existing termination machinery **cannot** be reused for S4's world bound:
- `diamondPos`/`boxNeg` mint `modalNextWorld b` **unconditionally** — no blocking guard exists.
- The world bound `modalWorldBound` is proved via a depth-indexed rank map + potential (Phase 2,
  ~1,650 lines, `FmpMeasure.lean:756–2416`), valid because K's tree depth ≤ modal depth. Under
  transitivity there is no such depth bound.

**What must be built** (none of this exists today):
1. A per-world formula-set extractor: `formulasAtWorld b w := b.filter (·.label == w)` (analogue
   of the generic `Branch.formulasAt`, but currently unused for blocking).
2. A subset/superset test between two worlds' *relevant* formula sets (over `modalSubfmls φ0`).
3. A **minting guard** in the S4 diamond rule: before creating a witness for `T(◇φ)@w`, search
   existing branch worlds for one whose relevant formula-set ⊇ the required set; if found, add a
   **loop-back edge** to it instead of minting (anywhere/subset blocking).
4. A new termination bound `#worlds ≤ 2^|modalSubfmls φ0|` and its loop invariant, added as a
   field to `ModalPotentialInv` (`FmpMeasure.lean:2116`).

**Reusable scaffolding** (confirmed present): `modalKnownWorlds` (`Branch.lean:89`),
`Accessibility`/`hasEdge`/`successorsOf` (`Branch.lean:55–84`), `outDeg` (`FmpMeasure.lean:793`),
`accTargetsKnown` (:1778), `boxPositivesOf` (`Branch.lean:183`), and the `ModalPotentialInv`
bundle. The persistent-rule *measure* machinery (`modalWork_drop_persistent`,
`modalApplyOne_persistent_props`) ports to the S4 4-rule **once world creation is separately
bounded** by the loop-check.

Loop-back edges create cycles in `acc`; these are harmless under `ReflTransGen` extraction (the
closure absorbs cycles) and are in fact necessary for the transitive countermodel.

---

## 6. File Plan (mapping to the task's proposed 5 files)

| File | Content | Risk | Est. lines |
|------|---------|------|-----------|
| `FrameRules.lean` | `frameApplyOne` variants (T/B/4/5 propagation rules), per-system `modalHintikkaSet` conjuncts | MED | 300–450 |
| `LoopChecking.lean` | S4 subset-blocking: `formulasAtWorld`, subset test, minting guard, `#worlds ≤ 2^\|Sf\|` bound + invariant | **HIGH** | 700–1200+ |
| `S5Simplification.lean` | Universal-cluster S5 rule + `EqvGen`/universal extraction (no loop-check) | MED | 250–400 |
| `FrameSoundness.lean` | `frameValid`, `branchSatisfiableIn FC`, per-system soundness arms via `Satisfies.t/b/four/five` | MED | 300–500 |
| `FrameCompleteness.lean` | Per-system `extractModel*` (closure-based), frame-condition instances (free), re-proved truth-lemma bridges, `*_complete` + `Decidable` | HIGH | 500–800 |

Realistic total **substantially exceeds** the 1,200–1,800 estimate once `LoopChecking.lean` is
included; T + B + S5 + their soundness/completeness alone fit ~1,200–1,600.

### Recommended decomposition (avoids sorry-pressure; zero-debt-compliant)
1. **Phase/Task A — T system** (reflexive): FrameRules(T) + FrameSoundness(T) +
   FrameCompleteness(T). Low risk, reuses K fuel machinery. Delivers a self-contained
   `Decidable (tValid φ)`.
2. **Phase/Task B — S5 simplification**: `S5Simplification.lean` universal-cluster approach.
   Independent of S4; moderate risk; no loop-checking.
3. **Phase/Task C — B system** (symmetric): backward propagation + `SymmGen` extraction.
4. **Phase/Task D — S4 loop-checking** (the crux): `LoopChecking.lean` termination + S4
   completeness. **Should be its own task** given it rivals the 2,959-line K FMP in difficulty.
5. **Phase/Task E — 5 (Euclidean)**: deliver via KB5/S5 equivalence route only; split a
   dedicated pure-K5 Euclidean-closure task or mark [BLOCKED] if pure-5 is required.

---

## 7. Zero-Debt & Lint Compliance

- **No `sorry`, no new `axiom`, no vacuous `def X := True`.** If S4 loop-checking or pure-5
  Euclidean closure cannot be closed within a phase, mark that phase **[BLOCKED]** with a
  documented goal state and recommend decomposition — never defer with `sorry`.
- Lint (`lake lint`, weekly cron but must pass): docstrings on every new decl (docBlame);
  Prop-valued results as `lemma`/`theorem` not `def` (defLemma); lowerCamelCase, no underscores
  (`extractModelS4`, `frameApplyOne`, `loopBlocked`); `@[simp]` only with verified LHS (simpNF);
  `omit` unused section vars; wrap instances in the namespace (topNamespace); avoid namespace
  repetition (dupNamespace).
- CSLib CI order: `lake build` → `lake exe checkInitImports` (every file `import Cslib.Init`) →
  `lake lint` → `lake exe lint-style` → `lake test` → `lake exe mk_all --module` (new files) →
  `lake shake …`.
- Notation: the tableau is an algorithmic decision procedure with no special operator notation;
  no NOTATION.md Option A/B/C choice applies. Reuse existing `□`/`◇`/`→` scoped notation from
  `Basic.lean`.

---

## 8. Open Questions / Decision Points for Planning

1. **Strategy A vs B for extraction** — Strategy B (closure-at-extraction, recommended) confines
   new work to the truth lemma and gets frame conditions free; confirm the planner adopts it.
2. **S4 loop-check granularity** — full anywhere/subset blocking vs simpler
   equality-of-formula-set blocking. Subset blocking gives smaller models but harder invariants;
   equality blocking is simpler and still terminating (`#worlds ≤ 2^|Sf|`). Recommend starting
   with **equality blocking**.
3. **Pure-5 Euclidean closure** — build custom `EuclGen`, restrict to KB5/S5, or split a task?
   Highest-risk decision; recommend the KB5/S5 route for task 300 and a separate pure-K5 task.
4. **S5 model shape** — universal relation `fun _ _ => True` (simplest, trivially equivalence)
   vs `EqvGen` (tighter). Recommend universal for the first pass.
5. **Frame-restricted validity naming** — reuse `Cube.lean`'s `T`/`S4`/`S5` `logic {m | …}`
   sets, or a lighter `frameValid FC`? Recommend a `frameValid FC` def that specializes to the
   Cube classes to keep the soundness/completeness statements uniform.

## References
- M. Fitting, *Proof Methods for Modal and Intuitionistic Logics* (1983), Ch. 2 (tableau rules).
- Blackburn, de Rijke, Venema, *Modal Logic* (2001), Ch. 4 (frame conditions, canonical models).
- Task 299 report `specs/299_modal_k_tableau/reports/01_modal-k-tableau-research.md`.
- Mathlib `Mathlib.Logic.Relation` (closure operators + frame instances).
