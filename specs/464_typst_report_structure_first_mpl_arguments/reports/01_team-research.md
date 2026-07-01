# Research Report: Task #464 — Arguments for the Structure-First MPL Design

**Task**: 464 — Typst report arguing for structure-first MPL (⊥ as an unconstrained nullary operator)
**Date**: 2026-07-01
**Mode**: Team Research (4 teammates: Proof-theory+Lean / Category-theory+Universal-algebra / Critic / Semantics+Horizons)
**Purpose**: Research to inform a Typst argumentative report. This is NOT the report; it is the evidence base, the recommended argument architecture, and the mandatory honesty ledger the report must honor.

---

## Summary

The structure-first MPL design — one fixed signature `{⊥,→,∧,∨}`, with `⊥` a **designated but unconstrained nullary operator** at MPL strength, strengthened to IPL by adding a semantic constraint (leastness) plus a proof rule (`efq`), then to CPL by classicality — is **substantially realized in the CSLib codebase and defensible on multiple independent grounds**: proof-theoretic (one typeclass-gate instantiated across four proof systems), universal-algebraic (a descending chain of varieties over a fixed signature), categorical (free monad + reflectors, conservativity = faithfulness), and semantic (a literal three-tier ⊥-ladder over one evaluator). 

The strongest *new* argument the report can carry is **not** the often-cited "substitution-invariance settles it" — the critic shows that framing is question-begging — but rather **teammate B's KF6**: only when `⊥` is a nullary *operation* is "explosion = leastness" expressible as a variety-defining **identity** (`⊥ ⊓ x = ⊥`), so Design A is the *unique* setting in which the whole "strengthen-by-adding-a-property = take-a-subvariety" narrative is even well-formed. Around that, the pragmatic cross-system-shared-monad goal supplies the practical case.

The report will be credible only if it foregrounds three honest concessions all four teammates converged on: (1) the free-monad argument is pragmatic, not apodictic; (2) MPL's `⊥` being unconstrained means MPL proves vacuous well-typed `⊥`-theorems (⊥ behaves like an atom at MPL) — a cost, not just a feature; (3) only the Hilbert + algebraic ladder is sorry-free — the tableau/decidability layer (task 317) and full fragment-generic completeness (task 410) are not, and the downstream modal/temporal/bimodal payoff is currently CPL-only (task 415) with the shared-metatheory substrate judged NO-GO (task 448).

---

## Key Findings

### Primary Approach — Proof theory + Lean engineering (Teammate A)

- **One uniform device.** The MPL→IPL step is the *same move* — adjoin explosion as a constructor gated by `[IsIntuitionistic T]` — instantiated in **four** layers: Hilbert (`MinPropAxiom` 8 ctors → `IntPropAxiom`+`efq` → `PropositionalAxiom`+`peirce`, `Axioms.lean:126-150/96-98/58-60`), Natural Deduction (`efq` gated, `NaturalDeduction/Basic.lean:182-183`), Sequent calculus (`botL` gated, `SequentCalculus/LJ/Basic.lean:100-102`), and Curry–Howard terms (`abort` gated, `CurryHoward/Defs.lean:103`); the semantic mirror is the additive mixin `HasLeastBot`/`HasInitialBot` (`BotProperties.lean:92,149`). `IsIntuitionistic T ↔ IPL ⊆ T` (`Defs.lean:171`), and `MPL = ∅` admits no instance, so explosion is **structurally unconstructible** (not merely inadmissible) at MPL strength. → "IPL = MPL + explosion" is one architectural fact instantiated four times.
- **Correction to the 407-era reports:** they call the sequent calculus "the largest structural gap (LJ hard-codes `botL`)." **Task 408 closed this** — `botL` is now gated exactly like `efq`, with cut-elimination/subformula proved once generic over `T`. The report must defend the tower *as it now stands*.
- **Faithfulness is graded.** Hilbert is the *purest* (genuinely ⊥-rule-free base predicate). ND and sequent are structure-first *"up to the gate"* — the `efq`/`botL` constructor is lexically present in the one shared inductive. Semantics is fully structure-first. Honest exception: **LK's `botL` is ungated** (`LK/Basic.lean:76-77`) — defensible because LK is classical/multi-conclusion.
- **Option C over B is decided by Curry–Howard/Prawitz, not aesthetics.** Splitting ND into a physically ⊥-free inductive (B) forces a parallel split of the `Theory.Term` type and a re-cut of the subformula/normalization theorem — the one genuinely hard result task 398 closed. Option C keeps one inductive ⇒ one metatheory proof serves all strengths. "The gate IS a property module" is precise: `IsIntuitionistic` is a `Prop`-class ≡ `IPL ⊆ T`, additive under extension.
- **Design A beats B1/B2 on substitution.** `Proposition.subst`'s `| bot => .bot` fixpoint (`Defs.lean:131`) makes `substAtom` total and side-condition-free — its `efq` arm re-derives explosion in the substituted theory with no `σ(⊥)=⊥` hypothesis (`Basic.lean:408`). B2 breaks exactly this; B1 duplicates the entire formula API and strands ⊥-stated assets.

### Alternative/abstract framing — Category theory + Universal algebra (Teammate B)

- **`Proposition Atom` is literally the free monad on the signature functor `Σ = {⊥(0),→(2),∧(2),∨(2)}`** (`Defs.lean:81-139`): the initial algebra of `A ↦ Atom ⊔ 1 ⊔ A²⊔A²⊔A²`, with `bot` in the *nullary-operation* (`1`) summand and `atom` in the *generator* summand; `Monad` = `pure := .atom; bind := subst`. The nullary-operation homomorphism law *forces* `subst f ⊥ = ⊥`. Naturality pins the ontology: `⊥` is a natural constant `1 ⇒ Proposition`; an atom is a component of the unit `η` (the thing substitution may replace).
- **The tower is a descending chain of VARIETIES over one fixed signature**: pointed-GHA (Johansson) ⊃ Heyting ⊃ Boolean, each step adjoining one **identity**. Leastness is *equational*, not merely quasi-equational: `b ≤ a ⟺ b⊓a=b` makes "least" the single identity `⊥⊓x=⊥` (≡ `⊥⇨x=⊤`). "Modularity around properties not connectives" = the lattice of subvarieties over the fixed signature; connective-modularity (B1) instead changes similarity type and fragments the picture across a poset of signatures.
- **KF6 — the strongest new abstract argument:** "explosion = leastness = an identity" *requires* `⊥` to be a nullary operation. Under B2 (⊥ = atom), `∀p∀a, p ≤ a` is not an identity in the signature (⊥₀ is not a signature constant), so leastness is not variety-definable. **Design A is the only option under which "explosion is a subvariety step" is even well-formed.**
- **Categorical semantics:** Lindenbaum–Tarski algebras are free objects (free GHA/HA/BA on `Atom`); the strengthenings are left-adjoint **reflectors** (realized by `Theory.intuitionisticCompletion`, `Defs.lean:198-206`, and the free functor `WithBot : GHA → HA`); **conservativity = the reflection unit is injective / the induced functor faithful on the ⊥-free fragment** (`coe_AlgEvaluate`, `ghaValid_iff_haValid_of_botFree`, `FragmentGeneric.lean:165-179`). `HasInitialBot` makes "efq = unique arrow `0→a`" a first-class artifact.

### Semantic tower + Strategic horizons (Teammate D)

- **The three-tier ⊥-ladder is a literal, verified tower on ONE evaluator.** `AlgEvaluate`/`bot_val` (`Algebra.lean:94`, `| .bot => bot_val`) serves all rungs; each rung has a biconditional completeness theorem: `MPL/IPL/CPL.hilbert_alg_complete` (`HilbertCompleteness.lean:93/122/155`). Only the constraint on the single element `bot_val` changes: free (GHAValid = MPL) → `HasLeastBot` (IPL, algebraic efq correlate, `BotProperties.lean:92`) → canonical `⊥` from `OrderBot` (IPL/CPL via Heyting/Boolean). `BrouwerianBot` (free) vs `PointedBrouwerian` (bot=⊥) are the *same* evaluator at two bot-values (`BrouwerianBot.lean:182`).
- **Kripke corroborates independently:** `IForces` parameterized by `botForces` (`Kripke.lean:81`); MPL = arbitrary predicate, IPL = `fun _ => False`; `mvalid_implies_ivalid` is a one-line specialization. This gives a second, independent semantic witness that "⊥'s clause is constrained only by type at MPL."
- **Strategic case:** one fixed signature makes "Propositional as a shared sub-logic" (ROADMAP) *true*; Design B duplicates the whole formula API per logic and reintroduces `σ(⊥)=⊥` side conditions. Structure-first front-loads the scaffolding for the eventual intuitionistic modal/temporal lift (gated-efq + `botForces` templates; `ProofSystemMorphism` and `conservative_over_cpl` substrates already green), and positions MPL as the reusable intuitionistic substrate for categorical-semantics / identity / hyperintensionality / tense roadmap items.

### Gaps, blind spots, and mandatory concessions (Teammate C, Critic)

- **O1 — the free-monad argument is NOT decisive; it is a signature choice dressed as a theorem.** Both "⊥-as-operation" and "⊥-as-generator" yield free monads; the universal property *restates* the choice rather than selecting it. The honest form is pragmatic: *given* the goal of one shared substitution monad across MPL/IPL/CPL/Modal/Temporal/Bimodal, treating `⊥` as an operation removes the `σ(⊥)=⊥` side condition. "Decisive"/"the free-algebra argument settles it" is the single most attackable sentence.
- **O2 — "⊥ totally unconstrained at MPL" is LITERALLY TRUE (verified) but carries a cost.** No MPL axiom mentions `⊥` (`Axioms.lean:126-150`); `bot_val` is a free parameter; `⊤=⊥→⊥` imposes nothing; `efq` is genuinely unconstructible. **Cost to concede:** MPL proves vacuous well-typed `⊥`-theorems (e.g. `implyK` at `⊥`), i.e. `⊥` behaves like an atom at MPL — the double edge that fuels O1.
- **O3 — only the Hilbert/algebraic ladder is sorry-free.** Sorry-free: the derivability subsumption chain (`ConservativeChain.lean:152,304`) and GHA/HA/BA completeness (`HilbertCompleteness.lean:64/93/122/148`); the `Derivable MinPropAxiom φ ↔ GHAValid φ` correlate is *exact*, no fragment caveat. NOT clean: four live task-317 sorries in Minimal/Intuitionistic tableau (`Tableau/{Minimal,Intuitionistic}/Completeness.lean`, `Scheme.lean:409,1070`), registered MPL/IPL decision instances carry `sorryAx`; fragment conservativity carries `IsOrBotFree`/`IsOrFree`/`IsImpTopOnly` side-conditions and the fully generic fragment-lift is OPEN (task 410).
- **O4 — "property module" is partly a re-description.** `efq` is a lexical constructor of the one shared inductive; `MinimalDerivation` is an abbreviation, not a ⊥-free type (deferred to task 409). Every induction over minimal derivations still carries a mandatory vacuous `efq` case (`Basic.lean:301-303`). **Also: the design note's `IsBotRuleFree := True` is stale/vacuous — the actual code is structural (`efq ↦ False`, `Basic.lean:223-235`); the report must cite the code, not the note.**
- **O5 — downstream payoff is speculative today.** Modal/Temporal/Bimodal embeddings are Łukasiewicz/CPL-only (task 415), so the minimal/intuitionistic structure is erased at the embedding boundary; the shared-metatheory substrate was judged NO-GO (task 448). No comparison to Mathlib/convention (Design B is the more common norm); the Zulip community *parked* Design A rather than endorsing it (AI policy: upstream prose must be human-authored).

---

## Synthesis

### Conflicts Resolved

**C1 — Is the free-monad/substitution-invariance argument decisive? (B says yes; C says question-begging.)** 
Resolution: **C is right at the meta-level, and B supplies the argument that actually is decisive — but it is a *different* argument.** The bare universal-property framing ("Proposition is the free monad on `{⊥,→,∧,∨}`, therefore ⊥ is fixed by substitution") does not *select* the signature — declaring ⊥ a generator also yields a free monad (C/O1). So the report must NOT lead with "substitution-invariance settles it." However, B's **KF6** is not question-begging: it observes that only if ⊥ is a nullary *operation* is the leastness/explosion condition expressible as a variety-defining **identity** (`⊥⊓x=⊥`), which is what makes the entire "strengthen-by-property = subvariety-step" architecture well-formed. That is a genuine structural payoff of the operation-choice, not a restatement of it. **Recommended framing:** (a) the *practical* driver is the cross-system shared-monad goal (pragmatic, own it as such); (b) the *decisive structural* argument is KF6 (operation-choice is what makes the subvariety tower and "conservativity by construction" possible); (c) substitution-invariance is a *consequence and convenience* of that choice, not its justification.

**C2 — Is the three-tier ⊥-ladder three genuine rungs (D) or "one variety in three presentations" (B)?** 
Resolution: **Both, at different levels.** *Semantically/proof-theoretically* there are exactly **two** genuine strengths at the ⊥-level — free `bot_val` (MPL) vs constrained-least `bot_val` (IPL) — plus classicality on top (CPL). D's "three tiers" `HasLeastBot`/`HasInitialBot`/`OrderBot` are **one variety (IPL) presented three ways**: order-theoretic (least), categorical (initial object `0→a`), and the canonical `bot=⊥` engineering form — because once leastness holds the least element is unique. The report should present the ladder as **MPL (free) ▸ IPL (constrained, however presented) ▸ CPL (classical)** and explicitly note the three "bot" mixins are conceptual/engineering presentations of the single IPL constraint, not three distinct logical strengths (B's caveat). D's value is the verified *completeness correspondence* per rung and the independent Kripke witness; B's value is not overselling the rung count.

**C3 — Does structure-first "pay off downstream"? (D optimistic; C skeptical.)** 
Resolution: **No factual disagreement; frame as positioning, not delivery.** Both agree: the modal/temporal/bimodal lift is currently CPL-only (Łukasiewicz), and the shared-metatheory substrate is NO-GO (task 448/419). D's defensible point is that structure-first *front-loads the scaffolding* (gated-efq + `botForces` templates, green morphism substrate) for an eventual intuitionistic lift. The report must present the downstream payoff as **an unpaid bet the design is positioned to win**, not a realized benefit — and disclose task 415's erasure result and task 448's NO-GO verdict.

**C4 — Sequent-calculus status.** No conflict: A's task-408 correction (LJ `botL` now gated) and C's task-317 tableau sorries are different layers. Both hold: the *proof-system tower* (Hilbert/ND/sequent/CH) is uniformly gated and green; the *tableau/decidability* layer is not.

### Points of strong consensus (all four teammates)

1. **⊥ is genuinely unconstrained at MPL** (verified in code) — with the vacuous-⊥-theorem cost to be conceded.
2. **The gate is one device instantiated across Hilbert/ND/sequent/CH**, with `HasLeastBot`/`HasInitialBot` as the semantic mirror; `IsIntuitionistic` is a real additive `Prop`-class (`≡ IPL ⊆ T`).
3. **Option C is correct; Option B is deferred (task 409) with real residual value** — a physically ⊥-free *derivation object* for minimal-ND normalization / abort-free λ-calculus. Cite the *structural* `IsBotRuleFree` (`Basic.lean:223-235`), never the design note's stale `:= True`.
4. **Design A dominates B1/B2**; B2 breaks the free/initial universal property (adds `σ(⊥)=⊥` side conditions), B1 changes similarity type (image not a subalgebra; forfeits the single monad).
5. **Sorry-free scope is exactly**: derivability subsumption chain + GHA/HA/BA algebraic completeness. Tableau/decidability (317) and generic fragment-lift (410) are NOT; downstream lift is CPL-only (415).

### Gaps Identified (for the report to preempt)

- No comparison to Mathlib / other Lean logic libraries' treatment of falsum (constructor vs `OrderBot`); Design B is the more common textbook/formalization convention. The report should frame Design A as a *deliberate minority choice* justified by the cross-system goal.
- The Zulip thread parked (did not ratify) Design A. Any upstream-facing prose must be human-authored (CSLib AI policy #605827029). This internal Typst report is fine; a Zulip post derived from it is not.
- "Pointed GHA / Johansson algebra with a designated constant `⊥`" is the precise name for the MPL algebra tier — not bare "GHA" (Mathlib GHA has `⊤` but no `⊥`).

---

## Recommendations (argument architecture for the Typst report)

1. **Open with the unifying picture (B):** one signature `Σ = {⊥,→,∧,∨}`, `Proposition` = the free monad on `Σ`, and the logic tower MPL ⊂ IPL ⊂ CPL = the descending subvariety chain pointed-GHA ⊃ HA ⊃ BA, each step adjoining one identity. State "modularity around properties, not connectives" = the lattice of subvarieties over the fixed signature.
2. **Make KF6 the keystone** (not substitution-invariance): only with `⊥` nullary is "explosion = leastness" a variety-defining identity; hence Design A is the unique setting where the whole property-strengthening narrative — and "conservativity by construction" (reflectors, faithfulness) — is well-formed.
3. **Present the tower as one gate instantiated four times** (A's table: Hilbert/ND/sequent/CH) + the semantic mirror (`HasLeastBot`), with the graded-faithfulness honesty (Hilbert purest; ND/sequent up-to-gate; LK ungated).
4. **Present the semantic three-tier ladder** on one evaluator (D), corrected to two genuine ⊥-strengths + classicality (B/C2), with the completeness correspondences and the Kripke witness.
5. **Resolve the ND controversy as Option C**, with the Curry–Howard/Prawitz reason B reopens, and B's real residual value (task 409) stated fairly, not dismissed.
6. **Include an explicit "Honest Limits / Objections" section** (this is what makes the report credible): pragmatic-not-decisive substitution argument; vacuous-⊥-theorem cost; sorry-free only at Hilbert/algebraic layer (name task 317 tableau sorries + task 410 open genericity); downstream CPL-only (task 415) + substrate NO-GO (task 448); Design B is the conventional norm; Zulip parked Design A.
7. **Cite the code, not the design note, wherever they diverge** (structural `IsBotRuleFree`; task-408 sequent closure).

---

## Teammate Contributions

| Teammate | Angle | Agent | Status | Confidence |
|----------|-------|-------|--------|------------|
| A | Proof theory (Hilbert/ND/sequent/CH) + Lean engineering | cslib-research-agent | completed | high |
| B | Category theory + universal algebra (free monad, varieties, reflectors) | math-research-agent | completed | high |
| C | Critic (adversarial: decisiveness, sorries, downstream payoff) | logic-research-agent | completed | high |
| D | Semantics tower + strategic horizons | formal-research-agent | completed | high (semantics) / medium (strategy) |

Conflicts found: 3 substantive (C1 decisiveness, C2 rung-count, C3 downstream) + 1 non-conflict (C4 layers). All resolved above. Gaps identified: 3 (Mathlib comparison, Zulip status, "pointed GHA" naming).

---

## References (key file:line anchors, verified 2026-07-01)

**Syntax / free monad**: `Cslib/Logics/Propositional/Defs.lean:81-92` (Proposition inductive), `:131` (`subst | bot => .bot`), `:137-139` (Monad), `:95,98` (derived `¬`,`⊤`), `:154-158` (MPL/IPL), `:166-171` (`IsIntuitionistic`, `↔ IPL ⊆ T`), `:198-206` (`intuitionisticCompletion`).
**Hilbert**: `ProofSystem/Axioms.lean:126-150` (`MinPropAxiom`, 8 ctors, no efq), `:96-98` (`IntPropAxiom.efq`), `:58-60` (`peirce`), `:155,168` (subsumption maps).
**ND**: `NaturalDeduction/Basic.lean:182-183` (gated `efq`), `:223-235` (structural `IsBotRuleFree`, `efq ↦ False`), `:242` (`MinimalDerivation` abbrev), `:301-303` (`weak` efq arm), `:392-408` (`substAtom`, side-condition-free).
**Sequent / CH**: `SequentCalculus/LJ/Basic.lean:100-102` (gated `botL`), `LK/Basic.lean:76-77` (ungated `botL`), `CurryHoward/Defs.lean:103` (gated `abort`); task 408 archived summary.
**Semantics**: `Semantics/Algebra.lean:94-100` (`AlgEvaluate v bot_val`), `Algebra/BotProperties.lean:92` (`HasLeastBot`), `:98` (`instHasLeastBotOrderBot`), `:149` (`HasInitialBot`), `BrouwerianBot.lean:182,236`, `Kripke.lean:81` (`IForces` w/ `botForces`).
**Metalogic / conservativity**: `ConservativeChain.lean:29-40,69,152,304`, `MplConservativeChain.lean:143,181`, `HilbertCompleteness.lean:64,93,122,148`, `FragmentGeneric.lean:154-179`, `GenericLindenbaum.lean:88-99`.
**Gaps**: `Tableau/{Minimal,Intuitionistic}/Completeness.lean` + `Scheme.lean:409,1070` (4 task-317 sorries), `{Min,Int}Decidability.lean` (`sorryAx`), task 410 (open generic fragment-lift), task 415 (CPL-only lift), task 448 (substrate NO-GO), task 409 (deferred ⊥-free ND).
**Artifacts**: `specs/407_mpl_base_structure_first_redesign/{mpl-base-design-note.md, decisions.md, reports/01-03, reports/zulip-propositional-logic.json}`; `specs/415_.../reports/01_lifting-audit.md`; `specs/419_.../reports/04_abstract-picture-and-result-inventory.md`; teammate findings `01_teammate-{a,b,c,d}-findings.md` (this directory).
