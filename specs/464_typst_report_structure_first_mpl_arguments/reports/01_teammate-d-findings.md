# Teammate D — Semantics Tower + Strategic Alignment

**Task**: 464 — Typst argumentative report defending structure-first MPL (Design A).
**Scope**: (1) the semantic three-tier ⊥-ladder and its soundness/completeness match to the
proof-theoretic ladder; (2) long-range strategic alignment of a single fixed foundational
architecture; (3) opportunities and strategic risks. Complements A (proof theory), B (abstract
algebra), C (critic). Does not duplicate those angles.

---

## Key Findings

### KF-1 — The semantic ⊥-ladder is a literal, verified three-tier tower, not an analogy

The whole defense of Design A rests on one realized fact: **`⊥` is a designated element whose
only constraint at the base is its type, and each stronger logic is obtained by *adding a
property to that element*, never by changing the language.** This is implemented three times over
(algebraic evaluator, Brouwerian-semilattice evaluator, Kripke forcing) and each tier is tied to
its proof-theoretic sibling by a *biconditional* soundness+completeness theorem. The tiers:

| Tier | Semantic constraint on ⊥ | Validity predicate | Proof system | Correspondence theorem |
|------|--------------------------|--------------------|--------------|------------------------|
| MPL | **none** — `bot_val : H` a free element | `GHAValid` | `MinPropAxiom` | `MPL.hilbert_alg_complete` |
| IPL | `HasLeastBot bot_val` (`bot_val ≤ a ∀a`) | `HAValid` (`bot_val = ⊥`) | `IntPropAxiom` (+efq) | `IPL.hilbert_alg_complete` |
| CPL | canonical ⊥ + classicality | `BAValid` | `PropositionalAxiom` (+DNE/Peirce) | `CPL.hilbert_alg_complete` |

The evaluator itself is *identical* across all three tiers; only the constraint on the one
designated element `bot_val` changes (`Algebra.lean:94`, the single `AlgEvaluate` recursion serves
GHA/HA/BA alike). This is the semantic content of "one signature, ⊥ interpreted weakly,
strengthened conservatively by property modules." **Confidence: High.**

### KF-2 — "The clause for ⊥ is effectively only constrained by type at MPL" is literally realized

At the MPL tier the ⊥ clause is `| .bot => bot_val` with `bot_val` an arbitrary inhabitant of the
carrier — `AlgEvaluate` (`Algebra.lean:97`) and `BrouwerianBotEvaluate` (`BrouwerianBot.lean:74`,
docstring line 62: "a free element; not required to be the least element"). `GHAValid`
(`Algebra.lean:130`) then *universally quantifies over `bot_val`*. This universal quantification is
exactly what keeps MPL from collapsing into IPL: if you forced `bot_val = ⊥` you would validate
`⊥ → A` and recover explosion (report 02 line 79: "forcing `bot_val=⊥` would validate `efq`,
collapsing MPL→IPL"). So MPL-completeness is *true because* ⊥ is unconstrained — the weak reading
is not a concession, it is the load-bearing choice. The two evaluators `BrouwerianBot` (free
`bot_val`, MPL) vs `PointedBrouwerian` (`bot_val = ⊥` via `OrderBot`, IPL) are provably the *same
evaluator at two bot-values*: `pointedBrouwerianEvaluate_eq_botBot`
(`BrouwerianBot.lean:182`) proves `PointedBrouwerianEvaluate v φ = BrouwerianBotEvaluate v ⊥ φ`,
and `brouwerianEvaluate_eq_botTop` (`:172`) recovers the top-bot variant. **Confidence: High.**

### KF-3 — Leastness IS the algebraic correlate of efq, proved as a mixin — the middle rung is real

`HasLeastBot b` (`BotProperties.lean:92`) is a **thin `Prop`-mixin on a specific element**, not a
typeclass on the algebra type (`:61-64` design note). Its single field `bot_le_val : ∀ a, b ≤ a`
is exactly the algebraic ex-falso condition: `hasLeastBot_himp_eq_top` (`:110`) proves
`b ⇨ a = ⊤`, and `algEvaluate_imp_bot_eq_top` (`:117`) lifts it to `AlgEvaluate v bot_val (⊥→A) =
⊤`, culminating in `algTValid_ipl_of_hasLeastBot` (`:126`): *any* `HasLeastBot` valuation models
`Theory.IPL`. The docstring states the correspondence verbatim (`:65-67`): proof-theoretic
`IsIntuitionistic T ↔ IPL ⊆ T` is dual to semantic `HasLeastBot bot_val ↔ ∀A, AlgEvaluate(⊥→A)=⊤`.
Crucially the mixin *does not change the type of the evaluator or the algebra* — it is purely
additive, the semantic image of "efq is a gated property module, not a language change."
**Confidence: High.**

### KF-4 — The Kripke picture confirms the tower independently (minimal vs intuitionistic frames)

The order-theoretic story is mirrored by a forcing story, which matters because it is the reader's
most familiar handle on "leastness shows up semantically." `IForces` (`Kripke.lean:81`) is a single
forcing relation *parameterized by a `botForces : World → Prop` predicate*. The three rungs:

- **MPL / minimal Kripke**: `MValid` (`Kripke.lean:153`) quantifies over *arbitrary upward-closed*
  `botForces` — ⊥ can be forced at some worlds. This is the forcing-side image of "bot_val free."
- **IPL / intuitionistic Kripke**: `IValid` (`:145`) fixes `botForces = fun _ => False` — ⊥ forced
  nowhere. `mvalid_implies_ivalid` (`:165`) makes MPL⊂IPL a one-line specialization (set the
  predicate to the empty one), the forcing dual of "add leastness."
- The algebra↔Kripke bridge is proved both directions of soundness: `mValidOfGHAValid`
  (`KripkeBridge.lean:280`) and `iValidOfHAValid` (`:257`), and completeness closes the loop via
  `min_soundness_completeness : MValid φ ↔ Derivable MinPropAxiom φ`
  (`MinStrongCompleteness.lean:347`).

So the "⊥ constrained only by type at MPL" thesis is witnessed *twice, in two independent
semantics*, each with a completeness theorem. That redundancy is the strongest single argument for
Design A: the weak-⊥ reading is not an artifact of one algebraic encoding. **Confidence: High.**

### KF-5 — There is already a categorical rung (`HasInitialBot`) — efq = the initial-object property

Beyond leastness, `BotProperties.lean` reifies `HasInitialBot b` (`:149`): the *categorical*
reading in which ⊥ is an initial object and efq is "the unique arrow `bot_val → a` exists for every
`a`." `instHasInitialBotOfHasLeastBot` (`:157`) shows leastness ⇒ initiality, and
`hasInitialBot_himp_eq_top` (`:165`) / `brouwerianBotEvaluate_efq_eq_top_of_initialBot`
(`BrouwerianBot.lean:236`) reprove explosion soundness through the universal property. **This is a
direct, already-built bridge to the roadmap's categorical-semantics ambition** (see KF-8).
**Confidence: High.**

### KF-6 — Strategic: one fixed architecture amortizes across the entire BimodalLogic port

`specs/ROADMAP.md` frames the programme as porting BimodalLogic into Foundations/Logic,
Propositional, Modal, Temporal, Bimodal, with **Propositional as the shared sub-logic** imported by
Modal and Temporal and (transitively) Bimodal (ROADMAP lines 14-17, 59-66). A single
`Proposition Atom` type that is the free monad on `{⊥,→,∧,∨}` is what makes "Propositional as a
shared sub-logic" *true rather than aspirational*: every downstream logic reuses one substitution
monad, one evaluator shape, one bot-property ladder. The design note's decisive argument
(`mpl-base-design-note.md:18-28`) is substitution-invariance / the free-algebra universal property
— and report 02 (line 19) notes the user's *broader* agenda (identity, hyperintensionality, modal)
"all lean on substitution." A language-first approach (Design B: a distinct `Proposition` type per
logic strength) would **duplicate the entire formula API — monad/bind, DecidableEq, subst, three
evaluators, two embeddings — per logic** (report 02 lines 96, 28), and would reintroduce a
`σ(⊥)=⊥` side condition on every substitution theorem (report 02 line 76). Structure-first pays a
one-time cost (`bot_val` as one extra evaluator argument) to avoid an O(#logics) duplication tax.
**Confidence: High.**

### KF-7 — Strategic honest counterweight: the structure does NOT yet survive the lift (task 415)

The single most important risk the report must acknowledge: **today's `toModal`/`toTemporal`/
`toBimodal` embeddings are Łukasiewicz/CPL-only** (415 audit §1, §3). `and`/`or` are encoded as
`A∧B ↦ ¬(A→¬B)`, `A∨B ↦ ¬A→B` — classically but *not* intuitionistically valid — and the
preservation theorems are stated against two-valued `PL.Evaluate`, so the lift certifies only the
CPL fragment (415 lines 16-33). The minimal/intuitionistic distinction that is "the whole point of
the structure-first base is erased at the embedding boundary" (415 line 31). There is **no
intuitionistic modal/temporal/bimodal target in CSLib** (415 lines 116-118). Betting the
foundational architecture on structure-first *before* the intuitionistic lift exists is therefore a
real, presently-unpaid bet. The report should state this plainly rather than let it be a critic's
gotcha. **Confidence: High.**

### KF-8 — Strategic upside: structure-first makes the eventual intuitionistic lift MORE attainable

The counterweight (KF-7) resolves *in favor* of Design A once you look at prerequisites. The 415
audit enumerates the four things a structure-preserving (intuitionistic-faithful) embedding needs
(415 lines 120-135): (1) native `and`/`or` on the target syntax; (2) a gated-efq intuitionistic
target proof system *mirroring the PL design*; (3) a birelational/Kripke target semantics bridging
to PL's parametric `IForces`/`botForces` rather than two-valued `Evaluate`; (4) a proof-theoretic
preservation theorem. **Structure-first already supplies the templates for (2) and (3):** the
gated-efq mechanism (`efq` gated `[IsIntuitionistic T]`) and the `botForces`-parameterized forcing
(`Kripke.lean:81`, arbitrary-predicate `MValid`) are exactly the patterns an intuitionistic modal
logic would instantiate. A language-first base offers no such reusable template — each new logic
would re-derive its own falsum discipline. Moreover the machinery to lift *is already partly
generic*: `conservative_over_cpl` (task 417, `Metalogic/ConservativityLift.lean`) unified
Temporal/Bimodal conservativity onto the Modal parametric pattern, and `ProofSystemMorphism`
(task 419, `Foundations/Logic/Metalogic/ProofSystemMorphism.lean`, `Deriv.map` forward functor)
gives a single derivation-lifting result the native lifts instantiate (419 report 04 §1). The
substrates that a future intuitionistic lift would extend **already exist and are green**. So
structure-first does not merely *permit* the intuitionistic lift — it front-loads its scaffolding.
**Confidence: Medium-High** (the templates exist; the actual native/intuitionistic embedding is
XL and unbuilt — 415 line 141).

### KF-9 — Opportunity: reposition MPL as the reusable intuitionistic substrate for modal/temporal/bimodal

Framed correctly, MPL-with-weak-⊥ is not just "the weakest propositional logic" — it is **the
reusable base every intuitionistic modal/temporal/bimodal logic will sit on**. The roadmap already
treats Propositional as the shared sub-logic; the bot-property ladder means the *same* file supplies
MPL, IPL, and CPL bases by property selection. Adjacent roadmap items this simultaneously advances:
**categorical semantics** (the `HasInitialBot` initial-object rung, KF-5, is a first-class
categorical artifact already in `BotProperties.lean`); **the two induced orders / identity /
hyperintensionality** strand (all substitution-dependent per report 02 line 19, and substitution is
sound precisely because ⊥ is a fixed operation, not an atom — `mpl-base-design-note.md:18-22`); and
**modality/tense** (Modal and Temporal both import Propositional; a weak-⊥ base is the only base
from which an intuitionistic modal base can be *specialized rather than rebuilt*). The strategic
recommendation: scope the report to present MPL as **the substrate, not the floor** — the object
whose property modules the rest of the tower selects from. **Confidence: Medium-High** (this is a
framing/positioning judgment grounded in the roadmap import structure, not a proven theorem).

### KF-10 — Strategic risk register (what the report must concede)

1. **Unpaid lift bet** (KF-7): structure-first's payoff on the intuitionistic side is *potential*;
   no intuitionistic modal target exists, and building one is XL (415 line 141). If the programme
   never adds intuitionistic modal logic, the weak-⊥ distinction survives only at the PL level.
2. **`bot_val` ergonomic cost**: one extra evaluator argument + a `botForces` field (report 02
   line 78); a genuine, if small, tax paid on every algebraic/Kripke proof. Defended as the
   Johansson designated constant, but it is the honest cost of the free reading.
3. **Fragment-genericity still open**: Waring's actual closing ask — structural metatheorems that
   *lift to a fragment by construction* — remains the open research problem (report 02 lines 26,
   84; 407 design note "Residual … task 410"). Structure-first is necessary but not yet sufficient
   for it. **Confidence: High.**

---

## Recommended Approach — how the semantic + strategic case strengthens Design A

The report's Design-A defense should run the semantic argument as its **spine** and the strategic
argument as its **horizon**:

1. **Lead with the tower as a verified fact, not a design preference.** Present the table in KF-1:
   one evaluator, three validity predicates, three biconditional completeness theorems. The
   rhetorical force is that Design A is not "a nicer way to organize" — it is *the organization the
   completeness proofs already have*. Any language-first alternative must re-prove three separate
   completeness theorems against three separate types.

2. **Make "⊥ constrained only by type" concrete and central** (KF-2). Show `| .bot => bot_val` with
   `∀ bot_val` quantification, and the collapse argument (forcing `bot_val=⊥` ⇒ efq ⇒ IPL). This
   is the single cleanest demonstration that the weak reading is *doing work*, not deferring it.

3. **Use the mixin (`HasLeastBot`) and the two-evaluator bridge to show "conservative
   strengthening by property module" is literal** (KF-3, KF-2). `PointedBrouwerian = BrouwerianBot
   at bot=⊥` is the paradigm: the stronger logic is the weaker evaluator with one element pinned.

4. **Deploy the Kripke tier as independent corroboration** (KF-4). The `botForces` parameter and
   `mvalid_implies_ivalid` give the reader a second, forcing-based witness that MPL⊂IPL is
   "specialize the ⊥-predicate." Two semantics agreeing is stronger than one.

5. **Pivot to strategy via the roadmap import graph** (KF-6): Propositional-as-shared-sub-logic is
   *true* only under a single fixed signature; Design B's per-logic duplication is the alternative's
   real cost. Then present KF-8/KF-9 as the upside (structure-first front-loads the intuitionistic
   lift's scaffolding; MPL is the reusable substrate), immediately followed by the honest risk
   register KF-7/KF-10. A defense that concedes the unpaid lift bet and still wins is more
   persuasive than one that hides it.

Net thesis the report should defend: **a single fixed signature with a weakly-interpreted,
property-strengthened ⊥ is the only architecture under which (i) the three completeness theorems
share one evaluator, (ii) two independent semantics both witness the MPL⊂IPL⊂CPL ladder as
property selection, and (iii) the downstream modal/temporal/bimodal programme reuses one
substitution monad and inherits ready-made templates for a future intuitionistic lift — at the
price of one extra `bot_val` argument and a still-unbuilt native intuitionistic embedding.**

---

## Evidence / Examples (file:line and roadmap refs)

Semantic ladder — algebraic:
- `Cslib/Logics/Propositional/Semantics/Algebra.lean:94` — `AlgEvaluate` (single evaluator, `bot_val` explicit param); `:97` ⊥-clause `| .bot => bot_val`; `:130` `GHAValid` (∀ bot_val); `:137` `HAValid` (bot=⊥); `:144` `BAValid`.
- `Cslib/Logics/Propositional/Semantics/Algebra/BotProperties.lean:92` `HasLeastBot` mixin; `:98` `instHasLeastBotOrderBot`; `:110` `hasLeastBot_himp_eq_top`; `:117` `algEvaluate_imp_bot_eq_top`; `:126` `algTValid_ipl_of_hasLeastBot`; `:149` `HasInitialBot`; `:157` `instHasInitialBotOfHasLeastBot`; `:165` `hasInitialBot_himp_eq_top`. Docstring correspondence `:42-44`, `:65-67`.
- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianBot.lean:73-79` `BrouwerianBotEvaluate` (free bot); `:117` `BrouwerianBotValid`; `:172` `brouwerianEvaluate_eq_botTop`; `:182` `pointedBrouwerianEvaluate_eq_botBot`; `:208` `brouwerianBotEvaluate_efq_eq_top` (HasLeastBot); `:236` `..._of_initialBot`.
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean:93` `MPL.hilbert_alg_complete : Derivable MinPropAxiom φ ↔ GHAValid φ`; `:122` `IPL.hilbert_alg_complete ↔ HAValid`; `:155` `CPL.hilbert_alg_complete ↔ BAValid`.
- `Cslib/Logics/Propositional/Semantics/Algebra/Soundness.lean:59` `min_alg_axiom_sound` (GHAValid); `:122` `int_alg_axiom_sound` (HAValid); classical at `:` prop tier (per docstring `:21-23`).
- `Cslib/Logics/Propositional/Semantics/Algebra/PointedBrouwerianCompleteness.lean:83` `conjImpBot_pointedBrouwerian_axiom_sound` (efq via `HasInitialBot.initialArrow`); `:150` `conjImpBot_pointedBrouwerian_complete`.
- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean:143` `GHAValid_implies_BrouwerianValid_direct`; `:161` `hilbertMplConservativeOverConjImp_direct` (MPL chain w/o routing through IPL).

Semantic ladder — Kripke:
- `Cslib/Logics/Propositional/Semantics/Kripke.lean:81` `IForces` (parameterized by `bot_forces`); `:145` `IValid` (`botForces = fun _ => False`); `:153` `MValid` (arbitrary upward-closed `botForces`); `:165` `mvalid_implies_ivalid`.
- `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean:257` `iValidOfHAValid`; `:280` `mValidOfGHAValid`.
- `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean:347` `min_soundness_completeness : MValid φ ↔ Derivable MinPropAxiom φ`.

Proof-theoretic anchors (for correspondence claims; from 415 audit, re-verify before Typst):
- `Cslib/Logics/Propositional/Defs.lean:85` primitive `bot` constructor.
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:182` `efq` gated `[IsIntuitionistic T]`; `:61-69` property-module doc.

Strategic:
- `specs/ROADMAP.md:14-17`, `:59-66` — Propositional as shared sub-logic; import graph.
- `specs/407_.../mpl-base-design-note.md:9-31` Design A / free-monad argument; `:48-69` bot-property hierarchy + Brouwerian wiring.
- `specs/407_.../reports/02_mpl-base-with-vs-without-bot.md:19,26,28,76,78,79,96` design comparison, costs, collapse argument, fragment-genericity open ask.
- `specs/415_.../reports/01_lifting-audit.md:16-33` CPL-only lift verdict; `:120-141` four prerequisites + XL effort; `:458-460` tasks 417/419 substrates landed.
- `specs/419_.../reports/04_abstract-picture-and-result-inventory.md:22-35` `ProofSystemMorphism`/`Deriv.map` forward lift green.

---

## Confidence Level Summary

| Finding | Claim | Confidence |
|---------|-------|-----------|
| KF-1 | Verified three-tier tower, one evaluator, biconditional completeness per rung | High |
| KF-2 | "⊥ constrained only by type at MPL" literally realized; collapse argument | High |
| KF-3 | `HasLeastBot` is the mixin correlate of efq, additive, proved | High |
| KF-4 | Kripke tier independently witnesses ladder via `botForces` param | High |
| KF-5 | `HasInitialBot` categorical rung already built | High |
| KF-6 | Single architecture amortizes across BimodalLogic port; B duplicates API | High |
| KF-7 | Structure does NOT yet survive the lift (Łukasiewicz/CPL-only) | High |
| KF-8 | Structure-first front-loads intuitionistic-lift scaffolding | Medium-High |
| KF-9 | Reposition MPL as reusable substrate; advances categorical/identity/modal | Medium-High |
| KF-10 | Risk register (unpaid bet, `bot_val` cost, fragment-genericity open) | High |
