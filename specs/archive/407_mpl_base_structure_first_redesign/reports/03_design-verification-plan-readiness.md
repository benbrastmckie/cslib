# Research Report 03: Adversarial verification of the MPL-base design decisions and plan-readiness verdict

- **Task**: 407 `mpl_base_structure_first_redesign`
- **Started**: 2026-06-29
- **Completed**: 2026-06-29
- **Effort**: hard (H2 anti-analysis, H3 reference grounding, H4 adversarial verification)
- **Dependencies**: 398 (completed; introduced the gated `efq` ND constructor this task re-frames). Verification baseline: green `main`.
- **Sources/Inputs**:
  - `reports/01_mpl-base-structure-first.md` (codebase layer map; option C; 6-wave breakdown)
  - `reports/02_mpl-base-with-vs-without-bot.md` (Zulip Design A vs B dispute)
  - `plans/01_mpl-base-waves-1-4.md` (the plan under test)
  - Live Lean sources under `Cslib/Logics/Propositional/` (read directly, post-task-398, 2026-06-29)
  - `references.bib`; `NOTATION.md`
- **Artifacts**: `reports/03_design-verification-plan-readiness.md` (this report)
- **Standards**: report-format; citation-conventions (BibKey); cslib CONTRIBUTING/NOTATION/ORGANISATION

---

## Executive Summary

- **Plan-readiness verdict: SOUND TO IMPLEMENT AS-IS.** No wave in `plans/01_mpl-base-waves-1-4.md` rests on a false premise. Every gap claim in report 01 was re-verified against current code; all confirmed, with only line-number drift (no semantic drift). Three non-blocking sharpenings (S1–S3) are recommended below.
- **Option C is structurally sound, not merely narrative.** The 398 gated constructor `efq … [IsIntuitionistic T]` (`NaturalDeduction/Basic.lean:155-156`) can be re-framed as a conservative additive explosion module **without inversion**, because the explosion property module *already exists definitionally*: `class IsIntuitionistic` with `IsIntuitionistic T ↔ IPL ⊆ T` (`Defs.lean:166-171`). MPL admits no such instance (`min_consistent`, `MinLindenbaum.lean:27`), so `efq` is genuinely unconstructible at minimal strength. The gate **is** the property module.
- **The "70–80% done" claim is true for underlying assets but overstated as a measure of deliverable completion.** The semantic and Hilbert layers are genuinely structure-first (verified). But the task's named deliverables — `HasDesignatedBot`/`HasLeastBot`, the generic Lindenbaum, the fragment-genericity layer, `MinimalDerivation`/`IsBotRuleFree` — **do not exist yet** (grep: zero hits). The figure measures *theorem availability*, not *artifact completion*; Phase 3's headline is largely net-new research.
- **All four GAP claims confirmed verbatim**: (1) ND inverted by 398 — gated `efq` + IPL-as-base docstring (`Basic.lean:48-78,150-156`); (2) sequent calculus hard-codes `botL` with no `LM` (`LJ/Basic.lean:91`, `LK/Basic.lean:76`, no `LM/` dir); (3) metalogic duplicates Min/Int and hard-wires EFQ (`IntLindenbaum.lean:69-75,296-301` vs `MinLindenbaum.lean:199-201`); (4) leastness/explosion only implicit via `OrderBot`+`bot_le`, no named hierarchy.
- **BibKey grounding complete**: `Johansson1937`, `Prawitz1965`, `SorensenUrzyczyn2006`, `TroelstraVanDalen1988`, `TroelstraSchwichtenberg2000`, `Gentzen1935` all present in `references.bib` and already cited in `Basic.lean:80-89`. No missing keys.
- **Naming caution (S2)**: do **not** introduce a parallel `HasExplosion` proof-theoretic class — `IsIntuitionistic` already is it; and `HasLeastBot` should be a thin layer over Mathlib `OrderBot`, not a competitor. `NOTATION.md` governs notation only, not typeclass naming.

---

## Context & Scope

Reports 01 and 02 produced a design (structure-first, Design A with `⊥`, option C ND reconciliation) and a Waves 1–4 plan. This hard-mode pass does not re-design; it **adversarially grounds** the existing decisions against the live codebase before implementation, per the task's five focus points. Every claim below is anchored to `file:line` from a direct read on 2026-06-29 (post-398), a Zulip msg ID, or a BibKey. Where the prior reports' anchors had drifted (line numbers, directory layout), the corrected anchor is given.

---

## Findings (grounded)

### F1 — ND inductive permits option-C re-framing as an additive module (focus 1: CONFIRMED)

- The single inductive `Theory.Derivation` has 11 constructors; `efq` is the last, gated:
  `| efq {Γ A} [IsIntuitionistic T] : Derivation Γ ⊥ → Derivation Γ A` (`NaturalDeduction/Basic.lean:155-156`).
- The explosion property is **already a named typeclass**: `class IsIntuitionistic (T) where efq (A) : (⊥ → A) ∈ T` (`Defs.lean:166-167`), with the characterization `IsIntuitionistic T ↔ IPL ⊆ T` (`Defs.lean:171`, `@[scoped grind]`). This is exactly the design's "explosion as an independent property module" ([Johansson1937] minimal logic = its absence).
- **No inversion is forced.** Structural metatheorems are generic over `T` and propagate the instance additively: `instIsIntuitionisticExtention {T ⊆ T'} [IsIntuitionistic T] : IsIntuitionistic T'` (`Defs.lean:190-191`). `weak`/`subs`/`ndToHilbert` carry the instance rather than baking `efq` into the base.
- MPL = `AxiomTheory MinPropAxiom`; `MinPropAxiom` has **no `efq` constructor** (8 constructors, `Axioms.lean:126-150`) and `min_consistent : ¬ Derivable MinPropAxiom ⊥` (`MinLindenbaum.lean:27`). Hence `IPL ⊄ AxiomTheory MinPropAxiom`, so MPL admits no `IsIntuitionistic` instance and `efq` is **unconstructible** at minimal strength.
- **Consequence**: the re-framing in Phase 1 ("base relation is `⊥`-rule-free; `efq` is the explosion module") is *operationally already true*; only the docstring (`Basic.lean:58-68`, still headed "**Design: IPL as base, MPL retained as a fragment.**") and an abbreviation are missing. The gated constructor does **not** force inversion that cannot be factored out. The literal `⊥`-rule-free *inductive* (option B) is the only thing the gate cannot provide; that is correctly deferred to spawned task 409/W6.

### F2 — Structure-first asset inventory (focus 2: CONFIRMED, with a denominator caveat)

ALIGNED assets re-confirmed present and matching report 01's anchors (line numbers updated):
- **Algebraic base**: `AlgEvaluate v bot_val` with explicit arbitrary `bot_val : H` over GHA; `⊥ → bot_val` (`Semantics/Algebra.lean:33-35,82-89`). `MPL.hilbert_alg_complete` quantifies over `bot_val`; `IPL.hilbert_alg_complete` instantiates `⊥` (`HilbertCompleteness.lean:93-97,122-126`) — confirming report 02's orthogonality claim (Zulip #604219492).
- **Leastness hierarchy**: `PointedBrouwerianEvaluate [OrderBot H]` maps `⊥ → ⊥` (`PointedBrouwerian.lean:67,81`); `BrouwerianBotEvaluate`/`BrouwerianBot` keep `bot_val` free. Both exist.
- **Hilbert tower**: `MinPropAxiom` (8) → `IntPropAxiom` (+`efq`, `Axioms.lean:96-98`) → `PropositionalAxiom` (+`peirce`, `Axioms.lean:56-60`); subsumption maps `MinPropAxiom.toIntPropAxiom`/`IntPropAxiom.toPropAxiom` (`Axioms.lean:155,168`).
- **Property typeclasses**: `MinimalAxioms extends ConjImpAxioms` with Min/Int/Prop instances (`Equivalence.lean:115-148`); `IsIntuitionistic`/`IsClassical` (`Defs.lean:166-186`).
- **Conservativity**: `MplConservativeChain` (direct algebraic route) + `ConservativeChain` (IPL route) both present (`MplConservativeChain.lean:20-83,148`).
- **Caveat (adversarial)**: NONE of the task's *named deliverables* exist yet — grep for `HasDesignatedBot|HasLeastBot|HasExplosion|MinimalDerivation|IsBotRuleFree` returns zero hits. So "70–80% done" is accurate for *primitive theorems available* but not for *task deliverables produced*. See Adversarial Verification §A2.

### F3 — Gap claims (focus 3: ALL CONFIRMED)

1. **ND inverted by 398** — gated `efq` + docstring "IPL as base" (`Basic.lean:48-78`); confirmed by git log (`90b68d1f task 398 phase 1: add gated efq constructor`).
2. **Sequent calculus large gap** — `botL` hard-coded, not parameterized: `| botL (Γ) (C) (_ : ⊥ ∈ Γ)` (`LJ/Basic.lean:91`), `| botL (Γ Δ) (_ : ⊥ ∈ Γ)` (`LK/Basic.lean:76`). No `LM/` directory (only `Defs.lean`, `LJ/`, `LK/`). Cut/subformula proved per-system (`LJ/CutElimination.lean`, `LK/CutElimination.lean`, …). Confirmed.
3. **Metalogic ~50% Min*/Int* duplication; Lindenbaum hard-wires EFQ** — `IntLindenbaum.intNegPhiImpPsi` builds an `.efq` axiom (`IntLindenbaum.lean:69-75`) and the closure uses an "EFQ bridge" `.ax [] _ (.efq phi)` (`:296-301`); `MinLindenbaum` has **no consistency requirement** and `min_imp_witness` needs **no EFQ** (`MinLindenbaum.lean:21,199-201`). Generic substrate (`GenericMCSBridge`, `MCS`, `DeductionTheorem`) exists. Confirmed.
4. **Semantic leastness/initiality/explosion only implicit** — explosion soundness rides `OrderBot` + `bot_le` (`PointedBrouwerian`); no named `Has*`/`Is*` property hierarchy and no categorical `0 → A` witness. Confirmed.

### F4 — Open questions §9 settled with evidence (focus 4)

- **Q1 ND reconciliation** → option C is the correct destination (F1). The gate is the property; option B is a separable inductive (task 409).
- **Q3 categorical/initiality** → the `0 → A` universal-property witness is **genuinely new mathematics**; only the `bot_le` instance route exists. Recommend Phase 2 ship `HasLeastBot` (≈ `OrderBot`-backed explosion soundness) but treat the literal initial-object witness as optional/stretch or a dedicated follow-on.
- **Q4 naming** → `NOTATION.md` covers transition/equivalence *notation* only (no typeclass-naming policy). Existing repo convention: `Is*` for `Prop`-mixins of properties (`IsIntuitionistic`, `IsClassical`, `IsBotFree`), Mathlib `Bot`/`OrderBot` for structure. Therefore: **reuse `IsIntuitionistic` for proof-level explosion (do not coin `HasExplosion`)**; make `HasLeastBot` a thin layer over `OrderBot`; keep `HasDesignatedBot` as the *existing* `bot_val` parameter rather than a new structure (report 02 defends the explicit parameter against Waring's "unnatural field", #605341190/#604219492).
- **Q5 task 400 (PR #607 connectives)** → keep separate; the plan already scopes connective typeclasses out (Non-Goals). Consistent with Zulip #606970606 ("connective typeclasses a separate development").

### F5 — BibKey grounding (H3)

All literature the design leans on maps to existing `references.bib` keys; all already cited in `Basic.lean:80-89`:

| Source claim | BibKey | Lean anchor |
|---|---|---|
| Minimal logic omits ex falso (`⊥` a free constant) | `Johansson1937` | `Axioms.lean:118-126`; `Basic.lean:52,82` |
| `⊥`-elimination as a primitive ND rule | `Prawitz1965` | `Basic.lean:62,83` |
| Bottom-elimination in NJ presentation | `TroelstraVanDalen1988` §10.4 | `Basic.lean:62,84` |
| Curry–Howard `⊥`/abort | `SorensenUrzyczyn2006` §2.2 | `Basic.lean:62,88` |
| Gentzen-style constructor/rule correspondence | `Gentzen1935` | `Basic.lean:61,86` |
| Normalization metatheory | `TroelstraSchwichtenberg2000` | (W6/normalization context) |

No BibKey needs to be added.

---

## Decisions

- **Confirm option C** as the ND reconciliation (F1). Task 398 is re-framed, not reverted.
- **Confirm Design A** (MPL base *with* `⊥`); Design B documented-not-implemented (report 02).
- **Confirm the plan's wave decomposition and the spawn of W5/W6** (sequent `LM`, literal ND split) as separate tasks.
- **Adopt sharpenings S1–S3** (below) as plan annotations before implementation; they do not change wave structure.

---

## Recommendations (prioritized) — Plan-Readiness Verdict

**VERDICT: The plan `plans/01_mpl-base-waves-1-4.md` is SOUND to implement as-is.** No phase rests on a false premise. Apply three non-blocking sharpenings:

1. **(S1, Phase 1) Pin the meaning of `MinimalDerivation`/`IsBotRuleFree`.** Prefer the trivial theory-abbreviation `MinimalDerivation := (AxiomTheory MinPropAxiom).Derivation` to honor "zero proof churn," OR an additive `IsBotRuleFree : Derivation → Prop` predicate (also zero churn to existing proofs). Do **not** claim a literal `⊥`-rule-free *inductive* — that is W6/task 409. Rewrite the `Basic.lean:58-68` docstring from "IPL as base" to "MPL base + gated explosion module," folding the substitution-invariance argument (Zulip #604219492).
2. **(S2, Phase 2) Avoid redundant/colliding typeclasses.** Reuse `IsIntuitionistic` for proof-level explosion (do not coin `HasExplosion`). Make `HasLeastBot` a thin `Prop`-mixin over Mathlib `OrderBot`; keep `HasDesignatedBot` as the existing `bot_val` parameter, not a new structure. Defer the categorical initial-object `0 → A` witness (new mathematics).
3. **(S3, Phase 3) Treat the fragment-genericity headline as open research, not asset assembly.** The "70–80% done" figure does not extend to this deliverable (F2 caveat). Keep the plan's existing contingency (Risk row 2: ship mechanism + one worked instance, document residual, spawn follow-on) front-and-center; do not let the optimistic figure mask Phase 3 risk. Land the metalogic genericization *additively first* (new defs alongside `Min*`/`Int*`), migrate one instance at a time, delete duplicates only once both pass.

Sequencing, file territories (Phases 2/3/4 edit disjoint trees: `Semantics/Algebra` vs `Metalogic` vs `Tableau`), and the final CI phase are all sound as written.

---

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|---|---|---|---|
| Phase 2 introduces a `HasExplosion`/`HasDesignatedBot` class that duplicates `IsIntuitionistic`/the `bot_val` parameter | M | M | S2: reuse `IsIntuitionistic`; `HasLeastBot` thin over `OrderBot`; `bot_val` stays a parameter |
| Phase 3 fragment-genericity proves to be open research, not a wave-sized item | M | M | S3 + plan Risk row 2 contingency: deliver mechanism + one instance, spawn follow-on; never `sorry` (mark [BLOCKED]) |
| Phase 1 "zero proof churn" violated by an over-ambitious `IsBotRuleFree` inductive | L | L | S1: prefer the theory-abbreviation reading |
| Metalogic genericization breaks a `Min*`/`Int*` completeness proof | H | M | Additive-first migration; per-instance green gate; delete duplicates last |
| Re-opening the "IPL-base + postpone" community compromise (Zulip #606970606) causes friction | M | M | Develop locally to green; human-authored PR/thread prose only (AI policy #605827029) |

---

## Adversarial Verification (H4)

For each prior recommendation I state what evidence would have **falsified** it and why it did not.

### A1 — Option C ("re-frame the 398 gate as an additive explosion module; zero proof churn in Phase 1")

- **Falsifier sought**: a structural metatheorem (`weak`, `subs`, `ndToHilbert`) whose `efq` arm inverts the base — i.e., forces MPL derivations to depend on explosion machinery — OR an MPL theory that accidentally carries an `IsIntuitionistic` instance (which would make `efq` constructible at minimal strength and collapse the fragment).
- **Result — not falsified.** `efq`'s `[IsIntuitionistic T]` binder (`Basic.lean:155`) plus `IsIntuitionistic T ↔ IPL ⊆ T` (`Defs.lean:171`) plus `min_consistent : ¬ Derivable MinPropAxiom ⊥` (`MinLindenbaum.lean:27`) jointly prove MPL has no such instance. Instance propagation is monotone/additive (`instIsIntuitionisticExtention`, `Defs.lean:190`). No metatheorem bakes `efq` into the base. **Residual honesty**: option C does *not* deliver a literal `⊥`-rule-free inductive — that is a real, separable cost (task 409). The recommendation is confirmed *with* that explicit scoping, not unconditionally.

### A2 — "The codebase is already ~70–80% structure-first"

- **Falsifier sought**: a layer claimed "aligned" that is actually missing/weaker, OR the in-scope task deliverables being mostly absent (making the figure misleading).
- **Result — partially refined, not refuted.** Every ALIGNED asset claimed (AlgEvaluate/`bot_val`, PointedBrouwerian/BrouwerianBot, the Hilbert tower, MinimalAxioms/IsIntuitionistic, conservativity chains, MPL/IPL/CPL completeness) was located and matches (F2). **But** the figure conflates two denominators. Against "underlying theorems available," 70–80% is fair. Against "task 407 named deliverables produced," it is ~0% — `HasDesignatedBot`/`HasLeastBot`/`MinimalDerivation`/`IsBotRuleFree`/generic-Lindenbaum/fragment-genericity all return zero grep hits. The honest restatement: *the primitives are 70–80% present; the reification/genericization deliverables are net-new.* This sharpens (does not break) the plan, and the plan already budgets W2/W3 as net-new work. Recorded as S3.

### A3 — The four GAP claims

- **Falsifier sought**: drift since report 01 (a gap silently closed, or an anchor that no longer exists).
- **Result — not falsified.** All four reproduced at current anchors (F3). The only "drift" is cosmetic: line numbers moved and `SequentCalculus` uses `LJ/Basic.lean`/`LK/Basic.lean` subdirectories (which *matches* report 01's anchors; an earlier `find | head` truncation briefly suggested otherwise). No gap has closed; no anchor is stale.

### A4 — Naming recommendation (open question Q4)

- **Falsifier sought**: a `NOTATION.md` or repo policy mandating `Has*` for these properties, which would justify coining `HasExplosion`.
- **Result — not falsified; recommendation strengthened.** `NOTATION.md` is notation-only (no typeclass-naming clause). The repo's de facto convention (`Is*` for property mixins) plus the pre-existing `IsIntuitionistic` make a new `HasExplosion` a redundant alias. Confirmed: prefer reuse (S2).

**Net adversarial outcome**: no fundamental flaw found; no `## Revised Direction` required. Two recommendations confirmed outright (A1 with explicit scoping, A3, A4); one figure refined for honesty (A2 → S3). The plan stands.

---

## Appendix

### References (BibKeys — verified in `references.bib`)
- `Johansson1937` — Johansson, *Der Minimalkalkül* (references.bib:309). Minimal logic; `⊥` as free constant.
- `Prawitz1965` — Prawitz, *Natural Deduction* (references.bib:432). `⊥`-elimination primitive.
- `TroelstraVanDalen1988` — Troelstra & van Dalen, *Constructivism in Mathematics* §10.4 (references.bib:492).
- `SorensenUrzyczyn2006` — Sørensen & Urzyczyn, *Lectures on the Curry–Howard Isomorphism* §2.2 (references.bib:482).
- `TroelstraSchwichtenberg2000` — Troelstra & Schwichtenberg, *Basic Proof Theory* (references.bib:846).
- `Gentzen1935` — cited at `Basic.lean:87` (present in references.bib).

### Zulip msg IDs (topic *Propositional Logic*; AI policy #605827029 — human-authored replies only)
- #604219492 (substitution-invariance / free-algebra argument; orthogonality of completeness to `bot_val`)
- #605341190, #606970606 (Waring: ND symmetry; fragment genericity as the real ask)
- #605712144 (Doty: conservativity hard in class-based approach)
- #605813681 (Benjamin: `efq`-as-theory-axiom reflects `⊥`'s no-intro-rule asymmetry)
- #605827029 (Henson: no LLM-authored Zulip prose)

### Key file:line anchors (verified 2026-06-29, post-398)
- `NaturalDeduction/Basic.lean:48-78` (IPL-as-base docstring), `:120-156` (inductive incl. gated `efq`)
- `Defs.lean:166-171` (`IsIntuitionistic` + `↔ IPL ⊆ T`), `:175-180` (`IsClassical`), `:190` (extension instance)
- `ProofSystem/Axioms.lean:48-78` (`PropositionalAxiom`+peirce), `:89-116` (`IntPropAxiom`+efq), `:126-150` (`MinPropAxiom`), `:155,168` (subsumption)
- `NaturalDeduction/Equivalence.lean:115-148` (`MinimalAxioms` + instances)
- `Semantics/Algebra.lean:82-89` (`AlgEvaluate`/`bot_val`); `PointedBrouwerian.lean:67,81`; `HilbertCompleteness.lean:93-97,122-126`
- `SequentCalculus/LJ/Basic.lean:91` (`botL`), `LK/Basic.lean:76` (`botL`); no `LM/`
- `Metalogic/IntLindenbaum.lean:69-75,296-301` (EFQ hard-wired) vs `MinLindenbaum.lean:21,27,199-201` (no EFQ, no consistency req)
