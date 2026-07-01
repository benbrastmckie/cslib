# Implementation Plan: Structure-First MPL Typst Report

- **Task**: 464 - Typst report presenting the best arguments for the structure-first MPL design
- **Status**: [NOT STARTED]
- **Effort**: 11 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_team-research.md; reports/02_grounding-and-typst-scaffold.md
- **Artifacts**: plans/02_mpl-structure-first-report.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/context/formats/status-markers.md (or status-markers convention)
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
- **Type**: markdown

## Overview

Produce a compiled-clean Typst document under `/home/benjamin/Projects/cslib/typst/MPL/`
that argues for the structure-first MPL design: one fixed signature `Σ = {⊥,→,∧,∨}` in which
`⊥` is a designated but totally unconstrained nullary operator at MPL strength, strengthened to
IPL by adjoining leastness (a semantic constraint) plus `efq` (a proof rule), then to CPL by
classicality. The report must give equal weight to two axes: (1) the cleanest mathematically
cultivated narrative for "⊥ as a primitive" — spine = free monad on `Σ`, tower MPL ⊂ IPL ⊂ CPL
as a descending chain of varieties, with KF6 (`⊥` nullary ⇒ "explosion = leastness" is a
variety-defining identity `⊥⊓x=⊥`) as the keystone; and (2) a faithful presentation of the
realized Lean 4 engineering — the one gate `[IsIntuitionistic T]` instantiated across four proof
systems, the Option-C resolution of the Hilbert-vs-ND controversy, graded-faithfulness honesty,
and exact sorry-free scope. Definition of done: `typst compile MplReport.typ build/MplReport.pdf`
runs clean from `typst/MPL/`, with every Lean anchor citing source-of-truth code (not the stale
design note) and every categorical claim carrying the informal-reading caveat.

### Research Integration

- **reports/01_team-research.md** — evidence base and argument architecture (six arguments), the
  KF6 keystone, the O1–O5 honesty ledger, conflict resolutions C1–C4 (notably C1: lead with KF6,
  not substitution-invariance; C2: two genuine ⊥-strengths + classicality, not three rungs), and
  the verified References anchor table.
- **reports/02_grounding-and-typst-scaffold.md** — round-2 re-verification of every file:line
  anchor (all confirmed), the exact Zulip message-ID index, the file-by-file Typst scaffold
  adaptation plan (§3), the 7-section document outline and priority ordering (Recommendations),
  and the Risks & Mitigations that this plan encodes. This report's priority order and outline
  diagram directly shape the phase decomposition below.

This is an INTERNAL Typst report. Per the CSLib AI policy incident on the source Zulip thread
(#605827029 / #605840135), any prose later adapted for upstream posting must be human-authored;
this constraint is stated in the report's own front matter and honesty chapter.

## Goals & Non-Goals

**Goals**:
- A compiled-clean Typst document (`typst compile` green) under `typst/MPL/` mirroring the
  BimodalLogic scaffold (`template.typ`, `notation/shared-notation.typ`, new
  `notation/mpl-notation.typ`, `chapters/NN-*.typ`, `.gitignore`).
- A narrative spine that leads with the free-monad / one-signature picture and makes KF6 the
  keystone argument (per conflict resolution C1), with the language-first counter-position
  (Waring) represented fairly and non-strawman.
- Full, faithful coverage of the Lean engineering: the four-times-instantiated gate table, the
  Option-C resolution, graded faithfulness (Hilbert purest; ND/sequent up-to-gate; LK `botL`
  ungated), and exact sorry-free scope.
- Every Lean citation grounded in source-of-truth code (module docstrings, structural
  predicates), never the stale `mpl-base-design-note.md`.
- A mandatory Honest-Limits chapter (O1–O5 + round-2's two added caveats) styled on the Bimodal
  `06-notes.typ` "Design Choices" pattern, plus an appendix anchor table.

**Non-Goals**:
- No new Lean proofs, edits to `Cslib/`, or code changes of any kind.
- No upstream Zulip post or any human-facing publication artifact (internal report only).
- No formalization of the categorical framing (no `Adjunction`/`Functor` instances are claimed
  as Lean results; they are presented as informal readings of order-theoretic facts).
- No coverage of the tableau/decidability layer (task 317) or generic fragment-lift (task 410)
  as if sorry-free; these are disclosed as out-of-scope for the clean-proof claim.
- Not modifying ROADMAP.md.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Toolchain failure: unavailable "New Computer Modern" font or network-gated `@preview/thmbox`/`@preview/cetz` on first compile | H | M | Front-load a minimal-document `typst compile` in Phase 1 to surface font/package issues before any content is written; drop the `cetz` import if no diagram is planned to reduce dependency surface |
| Citing the stale `IsBotRuleFree := True` (design-note:42) instead of the structural predicate | H | M | Encode the correct anchor `NaturalDeduction/Basic.lean:223-235` (`efq _ => False`) everywhere; add a mandatory "grep the draft for `IsBotRuleFree`" check in Phase 6 and Phase 7 confirming no citation points to `mpl-base-design-note.md:42` |
| Overclaiming the categorical framing (reflector / left adjoint / faithful functor) as formalized Lean results (grep returns zero `Adjunction`/`Functor` hits) | H | M | Place the informal-categorical caveat INLINE at first use in `01-syntax.typ` and `02-semantics.typ` (not only in the honesty chapter); use "the design realizes / is motivated by" phrasing, never "the code proves X is a reflector" |
| Strawmanning Waring's language-first position in the debate chapter | M | M | Use exact quotes/message IDs (#605341190, #606970606); represent B2-then-ND-symmetry evolution as substantive; present the "postpone minimal logic" compromise as UNANSWERED, not rejected |
| Overselling rung count or decisiveness (leading with substitution-invariance; claiming three ⊥-strengths) | M | M | Follow C1 (KF6 is decisive, substitution is consequence/convenience) and C2 (two genuine ⊥-strengths + classicality; the three "bot" mixins are one IPL constraint presented three ways) |
| Overclaiming downstream payoff | M | L | Per C3, frame downstream modal/temporal/bimodal lift as an unpaid bet (CPL-only today, task 415; substrate NO-GO, task 448), not a delivered benefit |
| `#figure`/`#table` overflow or broken `#link` in final PDF | M | M | Phase 7 dedicated verification pass checks overflow, links, and appendix/in-chapter citation consistency |
| task 409 status not independently re-verifiable | L | L | Cite `decisions.md` and the 407 reports for Option B's deferred status; optionally `grep specs/state.json` for "409" before finalizing |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 2, 3, 4 |
| 4 | 6 | 2, 3, 4, 5 |
| 5 | 7 | 6 |

Phases within the same wave can execute in parallel. Wave-2 parallelism is enabled by Phase 1
pre-seeding `notation/mpl-notation.typ` with common macros and pre-wiring the full `#include`
chain (with stub chapters), so each Wave-2 phase edits only its own chapter body.

---

### Phase 1: Scaffold and toolchain de-risk [NOT STARTED]

**Goal**: Establish the `typst/MPL/` directory mirroring the BimodalLogic scaffold and achieve a
MINIMAL clean `typst compile` before any content is written, surfacing font/package issues early.

**Tasks**:
- [ ] Create `/home/benjamin/Projects/cslib/typst/MPL/` and `typst/MPL/{notation,chapters}/`.
- [ ] Copy `template.typ` from `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/typst/` near-verbatim; re-point its notation import to `notation/mpl-notation.typ`.
- [ ] Copy `notation/shared-notation.typ` verbatim (reuses `imp`, `lneg`, `falsum`, `proves`, `ctx`, `metaphi`/`metapsi`/`metachi`, `leansrc`/`leanref`).
- [ ] Write initial `notation/mpl-notation.typ` importing `shared-notation.typ` and pre-seeding common macros: `∧`/`∨` (`land`/`lor` or verify Typst built-in `and`/`or`), an `efq` schema macro, and inline macros for `bot_val`/`HasLeastBot`/`HasInitialBot`/`IsIntuitionistic` as needed.
- [ ] Create `MplReport.typ` (mirrors `BimodalReference.typ`): package imports, `#set document/text/heading/par/page`, title page ("MPL: Arguments for a Structure-First Design" or similar), abstract page with thesis one-liner + the MPL ⊂ IPL ⊂ CPL ladder table (columns: Logic | Constraint on ⊥ | Proof rule added | Lean theory), `#outline`, and the full `#include` chain pointing at all six stub chapters.
- [ ] Create stub `chapters/{00-introduction,01-syntax,02-semantics,03-proof-theory,04-debate,05-honest-limits}.typ` (each a heading + one line) and `chapters/README.md`, `notation/README.md`.
- [ ] Copy `.gitignore` (`build/`, `*.pdf`).
- [ ] Run `typst compile MplReport.typ build/MplReport.pdf` from `typst/MPL/`; resolve any font/package/network issue before proceeding.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `typst/MPL/template.typ` - copied, notation import re-pointed
- `typst/MPL/notation/shared-notation.typ` - copied verbatim
- `typst/MPL/notation/mpl-notation.typ` - new, imports shared-notation, seeds macros
- `typst/MPL/MplReport.typ` - new main document (front matter + include chain)
- `typst/MPL/chapters/*.typ` - six stub chapters + README
- `typst/MPL/.gitignore` - copied

**Verification**:
- `typst compile MplReport.typ build/MplReport.pdf` exits clean (title page + abstract + outline + stubs render, no font/package errors).

---

### Phase 2: Introduction and Syntax chapters (Argument 1) [NOT STARTED]

**Goal**: Write `00-introduction.typ` (thesis + codebase map) and `01-syntax.typ` (Argument 1:
free monad / substitution-invariance), establishing the narrative spine and the `Proposition`
inductive with its symbol table.

**Tasks**:
- [ ] `00-introduction.typ`: thesis statement (one signature; MPL ⊂ IPL ⊂ CPL as descending variety chain; "modularity around properties, not connectives"); a "Codebase Structure" map listing `Cslib/Logics/Propositional/{Defs.lean, ProofSystem/, NaturalDeduction/, SequentCalculus/, CurryHoward/, Semantics/}`.
- [ ] `01-syntax.typ`: present the `Proposition` inductive (`Defs.lean:81-92`, 5 primitives; `bot` bare nullary at line 85), `subst | bot => .bot` (`Defs.lean:131`), the `Monad Proposition` instance (`Defs.lean:137-139`) with the source comment about lawfulness, and a symbol table (Symbol | Name | Lean | Reading) mirroring the Bimodal `01-syntax.typ` pattern.
- [ ] Frame Argument 1 as the free monad on `Σ` realized by the inductive+subst pair; cite the module docstring `NaturalDeduction/Basic.lean:44-115` (esp. `:66-100`) as primary source; reference the decisive Zulip post #604219492.
- [ ] Place the informal-categorical caveat INLINE at first use: no `LawfulMonad`/`Adjunction` instance exists; the free-monad framing is an external description, not a Lean-proved theorem ("realizes / is motivated by", not "proves").
- [ ] Add/extend `mpl-notation.typ` macros only as the chapter's math demands.
- [ ] Compile clean.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `typst/MPL/chapters/00-introduction.typ` - thesis + codebase map
- `typst/MPL/chapters/01-syntax.typ` - Argument 1 content + symbol table
- `typst/MPL/notation/mpl-notation.typ` - macros as demanded

**Verification**:
- `typst compile` clean; symbol table renders without overflow; caveat present at first categorical-language use; #604219492 and `NaturalDeduction/Basic.lean:44-115` cited.

---

### Phase 3: Proof-theory chapter (Arguments 3 and 4) [NOT STARTED]

**Goal**: Write `03-proof-theory.typ` covering Argument 3 (property modules) and Argument 4
(Hilbert-vs-ND controversy resolved as Option C), including the four-times-instantiated gate
table — the most mechanical, lowest-factual-risk content.

**Tasks**:
- [ ] Argument 3: `IsIntuitionistic`/`IsClassical` mixins (`Defs.lean:166-171`, `:175-180`, `isIntuitionisticIff ↔ IPL ⊆ T`), additivity (`instIsIntuitionisticExtension` `Defs.lean:190-191`), and the semantic mirror `HasLeastBot`/`HasInitialBot` (`BotProperties.lean:92-100,149-159`), noting the mixin-on-element vs typeclass-on-type distinction (`BotProperties.lean:61-64`).
- [ ] Argument 4: the gate `[IsIntuitionistic T]` instantiated FOUR times — Hilbert (`MinPropAxiom`→`IntPropAxiom`+`efq`→`PropositionalAxiom`+`peirce`; `Axioms.lean:126-150/89-116/48-78`), ND (gated `efq` `Basic.lean:182-183`), sequent (gated `botL` `LJ/Basic.lean:98-100`), Curry-Howard (gated `abort` `CurryHoward/Defs.lean:102-103`) — as a single summary table (with an "Available at" MPL/IPL/CPL column, or a per-system table).
- [ ] State the Option-C resolution with the decisive Curry-Howard/Prawitz subformula-property reason (one shared inductive ⇒ one metatheory proof; task 398), not aesthetics; cite structural `IsBotRuleFree` at `NaturalDeduction/Basic.lean:223-235` (`efq _ => False`) — NOT `mpl-base-design-note.md:42`.
- [ ] Encode graded faithfulness: Hilbert purest (⊥-rule-free base predicate); ND/sequent structure-first up-to-gate; LK `botL` UNGATED (`LK/Basic.lean:76`) as a defensible classical/multi-conclusion exception.
- [ ] State Option B as genuinely deferred (task 409) with real residual value, cited from `decisions.md:5-6` and the 407 reports; not dismissed.
- [ ] Compile clean.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `typst/MPL/chapters/03-proof-theory.typ` - Arguments 3 and 4, gate table
- `typst/MPL/notation/mpl-notation.typ` - macros as demanded

**Verification**:
- `typst compile` clean; four-system gate table renders; `IsBotRuleFree` cites `Basic.lean:223-235` (grep the chapter to confirm no `mpl-base-design-note.md:42` reference); LK ungated-exception stated.

---

### Phase 4: Semantics chapter (Arguments 5 and 6) [NOT STARTED]

**Goal**: Write `02-semantics.typ` covering Argument 5 (three-tier ⊥-ladder on one evaluator,
corrected to two genuine strengths + classicality) and Argument 6 (conservative-extension
results), with the informal-categorical caveat inline.

**Tasks**:
- [ ] Argument 5: `AlgEvaluate`/`bot_val` (`Algebra.lean:94-100`, `| .bot => bot_val` at :97) as the one evaluator serving all rungs; present as MPL (free `bot_val`) ▸ IPL (constrained-least, however presented) ▸ CPL (classical) per C2 — explicitly note `HasLeastBot`/`HasInitialBot`/canonical-`⊥` are three names for one IPL constraint (one instance-resolution chain via `instHasLeastBotOrderBot` `:98-100`), not three logical strengths.
- [ ] Kripke witness: `IForces` with `botForces` (`Kripke.lean:81-98`, `IForces_bot` :95-98) as the second independent semantic witness that ⊥'s clause is constrained only by type at MPL.
- [ ] Argument 6: `ConservativeChain` (`derivability_subsumption_chain` :152; fragment theorems :226/246/270), `MplConservativeChain` (:197/231/263, the MPL-as-top-of-its-own-chain claim, Zulip #606397657), and `HilbertCompleteness` one-theorem-three-corollaries (`:64/93/122/155`); `FragmentGeneric` (`ghaValid_iff_haValid_of_botFree` :174).
- [ ] MANDATORY: place the informal-categorical caveat INLINE wherever "reflector"/"left adjoint"/"faithful functor"/"initial object" language appears (grep zero `Adjunction`/`Functor` hits; `BotProperties.lean:31-36` frames these as informal readings of order-theoretic facts).
- [ ] Compile clean.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `typst/MPL/chapters/02-semantics.typ` - Arguments 5 and 6
- `typst/MPL/notation/mpl-notation.typ` - macros as demanded

**Verification**:
- `typst compile` clean; ladder presented as two strengths + classicality (not three rungs); informal-categorical caveat appears inline at every reflector/adjoint/initial-object occurrence; conservativity table renders.

---

### Phase 5: Debate chapter (Argument 2 + Hilbert-vs-ND narrative) [NOT STARTED]

**Goal**: Write `04-debate.typ` presenting structure-first vs language-first and the Hilbert-vs-ND
controversy with exact Zulip message IDs, representing Waring's position fairly. Written after the
content chapters so it inherits the vocabulary they fixed.

**Tasks**:
- [ ] Structure-first vs language-first (Argument 2): Waring's language-first framing (#605341190, "IPL/CPL as encodings... MPL as a fragment of IPL, or IPL encoded in MPL") stated as a substantive, non-strawman position; the origin (#603163993, pre-407 B2 with `⊥ : Atom`); Doty/Chou endorsement of a separate bot constructor (#603877853); the `bot_val` origin (#603884159, naive `⊥↦⊥` breaks MPL completeness).
- [ ] Hilbert-vs-ND narrative: Benjamin's decisive substitution post (#604219492); the ⊥-asymmetry resolution (#605813681, "no intro rule in any system", now in docstring `Basic.lean:92-96`); Waring's strongest final ND-symmetry objection + "forget minimal logic for the moment" compromise (#606970606) — presented as UNANSWERED (last message in thread), not rejected.
- [ ] Note the AI-policy incident (#605827029 / #605840135) as the concrete provenance of the internal-report constraint.
- [ ] Optionally include the collaborative conservativity history (#605862751, #606026592, #606128428, #606397657) as "contested-and-resolved-with-proofs" color.
- [ ] Compile clean.

**Timing**: 1.5 hours

**Depends on**: 2, 3, 4

**Files to modify**:
- `typst/MPL/chapters/04-debate.typ` - Argument 2 + Hilbert-vs-ND narrative

**Verification**:
- `typst compile` clean; Waring's position represented with exact quotes/IDs and shown as evolving (B2 → ND-symmetry); #606970606 presented as unanswered compromise; AI-policy incident noted.

---

### Phase 6: Honest-Limits chapter and appendix anchor table [NOT STARTED]

**Goal**: Write `05-honest-limits.typ` — the O1–O5 ledger plus round-2's two added caveats —
styled on the Bimodal `06-notes.typ` "Design Choices" pattern, and assemble the appendix anchor
table. This is what makes the report credible.

**Tasks**:
- [ ] State the mandatory concessions explicitly: substitution argument is pragmatic-not-decisive (O1); MPL proves vacuous well-typed ⊥-theorems (⊥ behaves like an atom at MPL) — a cost (O2); "property module" is partly a re-description, `efq` is a lexical constructor (O4); sorry-free ONLY at Hilbert/algebraic layer — name task-317 tableau sorries and task-410 open genericity (O3); downstream modal/temporal/bimodal payoff is CPL-only today (task 415) with shared-metatheory substrate NO-GO (task 448) (O5).
- [ ] Add round-2's two caveats: no `LawfulMonad` / no formalized `Adjunction` (grep-verified); Zulip message #606970606 is unanswered (thread PARKED, did not ratify Design A).
- [ ] Note Design B is the conventional textbook/formalization norm (Design A a deliberate minority choice) and the "pointed GHA / Johansson algebra" precise naming (not bare GHA).
- [ ] Style per `06-notes.typ`: paired `#definition` boxes for competing designs (A vs B1/B2), a comparison `#figure(table(...))`, and a `#remark("Trade-offs Accepted")` listing costs with justification.
- [ ] Assemble an appendix anchor table (either `06-appendix.typ` or an end table): file | line range | declaration | argument supported — from the per-argument citations in report 02 Findings §1 / Appendix.
- [ ] Grep the whole draft for `IsBotRuleFree` and confirm every occurrence cites `Basic.lean:223-235`, never `mpl-base-design-note.md:42`.
- [ ] Compile clean.

**Timing**: 1.5 hours

**Depends on**: 2, 3, 4, 5

**Files to modify**:
- `typst/MPL/chapters/05-honest-limits.typ` - O1-O5 ledger + caveats + trade-off table
- `typst/MPL/chapters/06-appendix.typ` (or appended table) - anchor table
- `typst/MPL/MplReport.typ` - add appendix to include chain if a new chapter

**Verification**:
- `typst compile` clean; all O1-O5 concessions + two round-2 caveats present; trade-off table renders; appendix anchor table consistent with in-chapter citations; grep confirms no `mpl-base-design-note.md:42` citation anywhere.

---

### Phase 7: Final compile-verification pass (DoD gate) [NOT STARTED]

**Goal**: Confirm the definition of done: full clean compile with no layout defects and internally
consistent citations.

**Tasks**:
- [ ] Run `typst compile MplReport.typ build/MplReport.pdf` from `typst/MPL/`; confirm zero errors/warnings.
- [ ] Visually check the PDF: no `#figure`/`#table` overflow, no broken `#link`, title/abstract/outline/all chapters render.
- [ ] Verify the appendix anchor table is internally consistent with every in-chapter citation (file/line/declaration match).
- [ ] Final grep sweep of all chapters for `IsBotRuleFree` (must cite `Basic.lean:223-235`) and for reflector/adjoint/functor language (must carry the informal caveat).
- [ ] Confirm the "New Computer Modern" font resolved (or an acceptable fallback rendered cleanly).
- [ ] Optionally `grep specs/state.json` for "409"/"415"/"448" to confirm the cited task statuses before finalizing.

**Timing**: 1 hour

**Depends on**: 6

**Files to modify**:
- `typst/MPL/` (fixes only, as verification surfaces defects)

**Verification**:
- `typst compile MplReport.typ build/MplReport.pdf` clean; no overflow/broken links; citation-consistency and caveat checks pass. This is the DoD gate.

## Testing & Validation

- [ ] `typst compile MplReport.typ build/MplReport.pdf` runs clean at the end of EVERY phase (compile-clean-per-phase discipline).
- [ ] Final DoD: clean compile from `/home/benjamin/Projects/cslib/typst/MPL/` with no `#figure`/`#table` overflow and no broken `#link`.
- [ ] Grep confirms zero citations to `mpl-base-design-note.md:42`; every `IsBotRuleFree` cites `NaturalDeduction/Basic.lean:223-235`.
- [ ] Every reflector/left-adjoint/faithful-functor/initial-object mention carries the informal-categorical caveat inline.
- [ ] Waring's language-first position is represented fairly with exact message IDs; #606970606 shown as unanswered.
- [ ] Ladder presented as two genuine ⊥-strengths + classicality (C2); KF6 is the keystone, substitution-invariance a consequence (C1).
- [ ] Honest-Limits chapter states all O1–O5 concessions plus the two round-2 caveats.
- [ ] Appendix anchor table is internally consistent with in-chapter citations.

## Artifacts & Outputs

- `typst/MPL/MplReport.typ` - main document (front matter + include chain)
- `typst/MPL/template.typ` - thmbox init + AMS styling (copied, re-pointed)
- `typst/MPL/notation/shared-notation.typ` - copied verbatim
- `typst/MPL/notation/mpl-notation.typ` - new MPL notation macros
- `typst/MPL/notation/README.md`, `typst/MPL/chapters/README.md`
- `typst/MPL/chapters/00-introduction.typ` - thesis + codebase map
- `typst/MPL/chapters/01-syntax.typ` - Argument 1
- `typst/MPL/chapters/02-semantics.typ` - Arguments 5, 6
- `typst/MPL/chapters/03-proof-theory.typ` - Arguments 3, 4
- `typst/MPL/chapters/04-debate.typ` - Argument 2 + Hilbert-vs-ND
- `typst/MPL/chapters/05-honest-limits.typ` - O1–O5 + caveats
- `typst/MPL/chapters/06-appendix.typ` (or end table) - Lean anchor table
- `typst/MPL/.gitignore` - `build/`, `*.pdf`
- `typst/MPL/build/MplReport.pdf` - compiled output (gitignored)

## Rollback/Contingency

- All work is confined to the new `typst/MPL/` directory; no `Cslib/` source is touched. To
  revert entirely, delete `typst/MPL/` — nothing else in the repository depends on it.
- If a phase's compile breaks and cannot be fixed quickly, revert that phase's chapter file to its
  Phase-1 stub (heading + one line) so the document stays green, and mark the phase [PARTIAL] with
  a note on the blocking issue for the next pass.
- If the toolchain (font/package/network) cannot produce a clean compile in Phase 1, stop and
  surface the environment issue before writing content — content phases assume a working compile.
