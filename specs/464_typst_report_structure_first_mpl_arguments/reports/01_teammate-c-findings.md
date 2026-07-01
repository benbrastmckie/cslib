# Task 464 — Teammate C (Critic) Findings

**Role**: Adversarial reviewer. Find where the "structure-first MPL" argument is weak,
unvalidated, or overstated, so the Typst report can preempt objections honestly.
**Date**: 2026-07-01
**Verification basis**: all file:line claims below were checked against committed source in
`Cslib/Logics/Propositional/` this session (Read + grep). Sorry census run tree-wide.

> Bottom line for the report authors: **the strongest parts of the thesis survive scrutiny
> (⊥ genuinely unconstrained at MPL; efq structurally unconstructible; the Hilbert/algebraic
> ladder is sorry-free), but three claims are overstated and must be softened or hedged:**
> (1) substitution-invariance is *not* a decisive theorem — it is a signature choice dressed
> as one; (2) "MPL is the base with no ⊥-rule" is true only at the level of *what is
> constructible*, not at the level of the inductive (efq is still a lexical constructor of the
> one shared type, and every induction over minimal derivations still carries a vacuous efq
> case); (3) the "structure-first pays off downstream" promise is currently unrealised — the
> Modal/Temporal/Bimodal lift is classical-only and the shared-metatheory substrate was judged
> NO-GO.

---

## Key Findings (sharpest objections, each with evidence)

### O1 — Substitution-invariance / free-monad argument is NOT decisive; it is partly rhetorical

**The claim under attack** (design note lines 72–90; report 02 §2 #604219492): *"`Proposition Atom`
is the free monad on `{⊥,→,∧,∨}`, so `⊥` is an element of the algebra, not meta-syntax; any
substitution sending `p₀ ↦ ⊥` must commute with derivability; B2 breaks the universal property."*

**Why it is overstated.** The free-monad framing **presupposes its own conclusion**. Whether
`Proposition Atom` is "the free monad on `{⊥,→,∧,∨}`" or "the free monad on `{→,∧,∨}` generated
by `Atom` (one generator designated `⊥`)" is *exactly the choice in dispute*. **Both are free
monads / free algebras.** Declaring `⊥` a nullary operation symbol makes it fixed by every
substitution (`bind ⊥ f = ⊥`, `Defs.lean:131` `| bot => .bot`); declaring it a generator makes
it substitutable. The universal-property argument does not *select* between these — it merely
*restates* the operation-symbol choice in categorical vocabulary. So "substitution-invariance is
decisive" is question-begging: it is decisive *only if you have already decided `⊥` is an
operation*, which is the very point Waring contests.

**Steelman of the opposing language-first / B2 view** (Waring #605341190, #603884159; Doty
#604166734): At **MPL strength `⊥` is behaviourally indistinguishable from an atom** — see O2:
no MPL axiom mentions it, and `bot_val` ranges freely. If `⊥` is *semantically* an arbitrary
element at MPL, the natural mathematical status of an arbitrary-but-unconstrained symbol is a
**generator (atom)**, not an operation. The free-algebra intuition actually cuts *toward*
Waring: `GeneralizedHeytingAlgebra` is *not* an algebra over a signature containing `⊥` — it has
no distinguished bottom — so `bot_val` is a genuinely *extra* field the design must bolt on
(`AlgEvaluate v bot_val`), exactly Waring's "unnatural field" (#605341190). The design pays a
real structural price (a free parameter threaded through every semantic theorem) to *buy* the
`σ(⊥)=⊥` convenience.

**Does B2 really "break" substitution?** No — not wholesale. B2 lands `Proposition` as the free
monad on `{→,∧,∨}` over `Atom`; substitution still exists and is still the unique homomorphism.
The cost is narrower than the design note implies: **only substitution theorems that actually
mention `⊥` acquire a `σ(⊥)=⊥` side condition**; the (large) majority that do not are unaffected.
The design note's phrasing "*the universal property fails*" (line 88) overstates a *bounded*
side-condition cost as a categorical catastrophe.

**What the report must concede.** The honest form of the argument is **pragmatic, not
apodictic**: "*Given the goal of one shared substitution monad across MPL/IPL/CPL/Modal/Temporal/
Bimodal, treating `⊥` as an operation is the lower-friction choice because it removes a
`σ(⊥)=⊥` side condition from the cross-system substitution lemmas.*" That is defensible. Calling
it "decisive" or "the free-algebra argument settles it" is not — the goal (shared monad) is
itself what Waring's compromise ("forget minimal logic for now", #606970606) declined to commit
to. **Confidence: HIGH that the "decisive" framing is overstated.**

---

### O2 — "MPL's ⊥ is totally unconstrained" — LITERALLY TRUE in code, but carries a real honesty cost

This is the thesis's **strongest** claim and it **survives verification** — the report should
lean on it, but must preempt the "meaningless ⊥" objection it invites.

**Verified TRUE at the Hilbert level.** `MinPropAxiom` (`ProofSystem/Axioms.lean:126–150`) has
**8 constructors: implyK, implyS, andI, andE1, andE2, orI1, orI2, orE**. There is **no efq, no
Peirce, and no negation axiom** — and since `¬A := A → ⊥` (`Defs.lean:95`) is only an
abbreviation, `⊥` **never appears in any MPL axiom**. So nothing at MPL strength pins `⊥`.

**Verified TRUE at the semantic level.** `GHAValid` is "MPL semantics over all bot values"
(`BotProperties.lean:24`); the evaluator `AlgEvaluate v bot_val` carries `bot_val` as a *free*
parameter with `HasLeastBot`/`OrderBot` constraints added only at IPL/CPL strength
(`BotProperties.lean:26–57`). `⊤ := ⊥→⊥` (`Defs.lean:98`) and `¬A := A→⊥` do *not* covertly
constrain `bot_val`: in any GHA, `bot_val ⇨ bot_val = ⊤` regardless of `bot_val`'s value, so the
derived `⊤` is always the algebra top and imposes nothing. **No covert pin found.**

**"efq structurally unconstructible (not merely inadmissible)" — DEFENSIBLE.** `efq` carries
`[IsIntuitionistic T]` (`NaturalDeduction/Basic.lean:182`); `IsIntuitionistic T ↔ IPL ⊆ T`
(`Defs.lean:171`); `IsIntuitionistic MPL` would require `IPL ⊆ ∅`, provably false. So no instance
can be supplied *soundly*, and the constructor cannot be applied at `T = MPL`. This is a genuine
type-level obstruction, not mere non-derivability. The claim holds.

**The honesty cost the report MUST preempt.** Because `⊥` is in the *language* even though no
axiom mentions it, **MPL proves vacuous-but-well-typed theorems about `⊥`**. E.g. `implyK`
instantiated at `⊥` gives `Derivable MinPropAxiom (⊥ → (ψ → ⊥))`; `andE1` gives
`Derivable MinPropAxiom ((⊥ ∧ ψ) → ⊥)`. Every MPL metatheorem that quantifies "∀ φ" ranges over
formulas **containing an uninterpreted `⊥`**. This is precisely the "constructor with no
semantics is very unnatural" worry (Waring #606970606) and the "meaningless ⊥ floating in
formulas" cost. The design's own answer — `⊥` behaves *exactly like an atom* at MPL strength — is
correct, but it is a double-edged concession: it is the very fact that makes O1's "why not just
call it an atom?" objection bite.

**Confidence: HIGH that the claim is true; HIGH that the report must explicitly concede the
vacuous-⊥-theorem cost rather than let a reviewer discover it.**

---

### O3 — Conservativity & per-class completeness: the algebraic ladder IS sorry-free; the tableau/decidability layer and full fragment-genericity are NOT

**What is genuinely proved sorry-free** (tree-wide sorry census: the *only* real `sorry` tokens
in `Cslib/Logics/Propositional/` are four, all in Tableau — see below):

- **MPL ⊂ IPL ⊂ CPL derivability chain**: `derivability_subsumption_chain`
  (`ConservativeChain.lean:152`), `minAxiom_iff_chain` (`:304`), via `liftDerivationTree` /
  axiom subsumption (`MinPropAxiom.toIntPropAxiom`, `IntPropAxiom.toPropAxiom`,
  `Axioms.lean:155,168`). **Sorry-free.**
- **Per-class algebraic completeness (GHA / Heyting / Boolean)**: `MPL.hilbert_alg_complete`
  (`HilbertCompleteness.lean:93`), `IPL.hilbert_alg_complete` (`:122`),
  `CPL.hilbert_alg_complete` (`:148`), all corollaries of `hilbert_alg_complete_theory` (`:64`).
  **Sorry-free.** The `GHAValid = MinPropAxiom` correlate is the *unrestricted* biconditional
  `Derivable MinPropAxiom φ ↔ GHAValid φ` — this is **exact**, no fragment caveat.
- **Initiality (Q3 "NEW MATH" gating item)** landed: `HasInitialBot` +
  `algEvaluate_imp_bot_eq_top_of_initialBot` (`BotProperties.lean:53–57`,
  `BrouwerianBot.lean:236`). **Sorry-free.**

**What is NOT clean (the caveats the report must disclose):**

1. **MPL/IPL tableau completeness and decidability carry `sorry` (task 317).** The four live
   sorries: `Tableau/Minimal/Completeness.lean:110`, `Tableau/Intuitionistic/Completeness.lean:113`,
   `Tableau/Intuitionistic/Scheme.lean:409` and `:1070`. Consequently the *registered*
   decision-instance route inherits a `sorryAx`: `MinDecidability.lean:66` and
   `IntDecidability.lean:62` explicitly document "Carries the … 317 `sorryAx`". Only the **FMP
   route** (`decidableDerivableMinPropAxiomFMP`, `decidableDerivableIntPropAxiomFMP`) is
   sorry-free, and it is a *non-registered* `noncomputable def`. **Classical tableau is
   sorry-free; Minimal and Intuitionistic tableau completeness are not.** If the report says or
   implies "the whole MPL⊂IPL⊂CPL edifice is proved", that is false for the tableau/decidability
   layer.

2. **Fragment conservativity results carry fragment side-conditions, and full genericity is OPEN
   (task 410).** `GHAValid_implies_BrouwerianValid_direct` requires `hOBF : φ.IsOrBotFree = true`
   (`MplConservativeChain.lean:143`); `GHAValid_implies_BrouwerianBotValid_direct` requires
   `hOF : φ.IsOrFree` (`:181`); `imp_hilbert_complete` requires `IsImpTopOnly`. The generic
   `HAValid φ → Derivable P-logic φ` parameterised by a fragment predicate `P` **does not exist**
   — design note lines 103–113: "*A fully generic … parameterized by `P` is **open research**.
   Task 410 is spawned.*" So the "fragment-genericity by construction" that report 02 elevated to
   *the headline ambition* (§1, §6.3) is **not delivered**; only worked instances + one generic
   corollary (`ghaValid_iff_haValid_of_botFree`) exist.

**Confidence: HIGH.** The report can honestly claim the *core ladder* (derivability chain +
GHA/HA/BA completeness) is sorry-free, but must NOT extend that claim to tableau, decidability,
or generic fragment-lifting.

---

### O4 — "Option C is a property module" is partly a re-description; there is no physically ⊥-free base, and a concrete consumer pays for it

**The structural claim.** Design note + decisions.md Q1 frame Option C as: MPL is the base, `efq`
is an "explosion **property module**", `MinimalDerivation`/`IsBotRuleFree` name the gate-free
fragment. Report 02 §1 calls this "a real rule/module, not axiom-indirection."

**Where it is a re-description, not a structural fact.** `efq` is a **lexical constructor of the
one shared `Theory.Derivation` inductive** (`NaturalDeduction/Basic.lean:182`).
`MinimalDerivation Γ A := MPL.Derivation Γ A` (`:242`) is an **abbreviation for the same
inductive at the empty theory** — *not* a separate ⊥-rule-free type. A physically ⊥-free base
inductive is **explicitly deferred to task 409/W6** (plan `04_…-v2.md:27`, `:98`;
`Basic.lean:222`). So "MPL has no ⊥-rule" is true for *what is constructible* but **false for the
constructor list of the type**: `⊥`/`efq` are still present in the type, gated behind an
instance.

**IsBotRuleFree is a derived predicate, not a type distinction** — and the design note
mis-describes it. The design note (`mpl-base-design-note.md:42–43`) says
`IsBotRuleFree d : Prop := True` — the *prohibited vacuous pattern* (`.claude/rules/lean4.md`).
The **actual code is better than the note**: `IsBotRuleFree` is a genuine structural recursion
with `| efq _ => False` (`Basic.lean:223–235`). **The report must cite the real structural
definition, not the design note's stale `:= True`,** or a reviewer reading the note will
(correctly) call it vacuous.

**The concrete consumer that exposes the Option-C-vs-B difference.** Any structural
recursion/induction over minimal derivations **still has to carry the `efq` case**. Verified:
`Theory.Derivation.weak` handles it at `Basic.lean:301–303`, reconstructing
`IsIntuitionistic T'` via `instIsIntuitionisticExtension` — i.e. the `efq` arm is physically
present in the recursor and must be discharged (here: rebuilt; at `T = MPL` it would be
discharged as vacuous). With Option B's physically ⊥-free inductive, **that case would not exist
at all**. So the concrete cost of *not* having Option B is: every metatheorem proved by induction
on `MinimalDerivation` pays for a vacuous-but-mandatory `efq` case, and any downstream author who
wants "minimal derivations, exhaustively, without an explosion arm" cannot get it from the type —
only from the `IsBotRuleFree`/instance-absence argument. **What the report loses by not having
Option B: a clean induction principle for MPL and an exhaustiveness guarantee at the type level.**

**Confidence: MEDIUM-HIGH.** The property-module framing is *legitimate* (the gate is real and
`IsBotRuleFree` is non-vacuous), but the report overstates if it implies a structural ⊥-free
base; it should say "gate on a shared inductive; physical ⊥-free base is future work (409)."

---

### O5 — What the whole framing overlooks

1. **The downstream payoff is currently CPL-only — "structure-first pays off for the programme"
   is SPECULATIVE today.** The Modal/Temporal/Bimodal embeddings (`toModal`/`toTemporal`/
   `toBimodal`, now `PL.Proposition.embed`, `Embedding.lean`) encode `∧`/`∨` via **Łukasiewicz
   definitions** `A∧B ↦ ¬(A→¬B)`, `A∨B ↦ ¬A→B` — classically but **not intuitionistically**
   valid (task 415 report §3, verified anchors `Defs.lean:85`, `ND/Basic.lean:182`,
   `LJ/Basic.lean:100`). The minimal/intuitionistic distinction **is erased at the embedding
   boundary** (415 §1 verdict: "the structure-first propositional base does NOT lift naturally
   today; only its classical collapse survives"). So the marquee justification for one shared
   `Proposition` type (cross-system uniformity) currently buys uniformity **only for CPL**. The
   report should not imply the modal family already benefits from structure-first MPL — it does
   not.

2. **The shared-metatheory substrate (the deepest version of the payoff) was judged NO-GO.**
   Task 419 delivered a *forward* lifting device (`Deriv.map`, sorry-free) but the backward-map /
   full-`Equiv` "shared-metatheory substrate" (Vision B) is gated on an R1 representation change
   and was **spun off to task 448 with verdict NO-GO ("insufficient ROI")** (419 report §6–7,
   §10 of 415). So "generic metatheorems proved once, transported to every logic" — the
   intellectual prize — is **explicitly not being built**. If the report sells structure-first as
   an enabler of generic metatheory, that is aspirational, not realised.

3. **Decidability is only half-done** (see O3): registered decision procedures for MPL/IPL carry
   the 317 `sorryAx`. A report claiming the ladder is "computationally complete" would be wrong.

4. **No comparison to how Mathlib / other Lean logic libraries treat `⊥`.** The design note cites
   Johansson/Prawitz/Troelstra–van Dalen but never contrasts with Lean-ecosystem practice (e.g.
   Mathlib's own propositional/Heyting-algebra development, or how other formalisations handle
   falsum as constructor vs. `OrderBot`). A skeptical reviewer will ask "is this the community
   norm?" The report should at least acknowledge that Design B (falsum added with efq) is the
   *more common* textbook and formalisation convention, and that Design A is the deliberate
   minority choice justified by the cross-system-monad goal.

5. **The Zulip thread did not endorse Design A — it parked it.** Report 02 §2 is candid that the
   community "converged to a pragmatic compromise: IPL as base, postpone fragments" (#606970606),
   and that making MPL the base "re-opens a settled-for-now community decision" (report 02 §7 Q3).
   The report must not present Design A as community-ratified; it is a defensible reopening, and
   any Zulip-facing prose must be human-authored (AI policy, #605827029).

**Confidence: HIGH on (1),(2),(3); MEDIUM on (4),(5) framing.**

---

## Recommended Approach — what the report MUST concede or preempt to be honest and robust

1. **Reframe substitution-invariance as a pragmatic argument, not a decisive theorem.** State
   plainly that both "⊥-as-operation" and "⊥-as-generator" yield free monads, and that the choice
   is driven by the *cross-system shared-monad goal*, not by an inescapable universal property.
   Preempt: "the free-algebra argument settles it" is the single most attackable sentence.

2. **Lead with the verified strong claim (O2) but immediately own its cost.** Say: MPL's `⊥` is
   provably unconstrained (no MPL axiom mentions it; `bot_val` free) AND this means MPL proves
   vacuous well-typed `⊥`-theorems and treats `⊥` behaviourally as an atom. Turn the concession
   into the bridge to the design rationale (⊥ acquires meaning only via property modules).

3. **Scope the "proved" claim precisely.** Claim sorry-free only for: the derivability
   subsumption chain and GHA/HA/BA algebraic completeness. Explicitly disclose: (a) four
   task-317 tableau sorries + `sorryAx` in registered MPL/IPL decision instances; (b) fragment
   conservativity side-conditions (`IsOrBotFree`/`IsOrFree`/`IsImpTopOnly`) and the OPEN generic
   fragment-lift (task 410).

4. **State Option C honestly**: gate on a shared inductive, `IsBotRuleFree` a *structural*
   predicate (cite `Basic.lean:223–235`, NOT the design note's stale `:= True`), physical ⊥-free
   base = future work (task 409). Name the concrete cost: mandatory vacuous `efq` case in every
   induction over `MinimalDerivation` (`Basic.lean:301–303`).

5. **Do not oversell the downstream payoff.** Concede the modal/temporal/bimodal lift is
   currently CPL-only (Łukasiewicz embeddings, task 415) and the shared-metatheory substrate is
   NO-GO (task 448). Present structure-first as *positioning for* future intuitionistic-modal work,
   not as already delivering it.

6. **Acknowledge the community status**: Design A reopens a parked decision; Design B is the more
   conventional convention; Zulip prose must be human-authored.

---

## Evidence / Examples (file:line, sorries/gaps)

| Claim | Evidence | Verdict |
|---|---|---|
| `⊥` constructor primitive | `Defs.lean:85` (`\| bot`) | confirmed |
| `¬A := A→⊥`, `⊤ := ⊥→⊥` derived (abbrev) | `Defs.lean:95,98` | confirmed |
| substitution fixes `⊥` | `Defs.lean:131` (`\| bot => .bot`) | confirmed |
| **MPL axioms contain NO `⊥`/efq/neg** | `Axioms.lean:126–150` (8 ctors) | confirmed — supports O2 |
| efq gated `[IsIntuitionistic T]` | `NaturalDeduction/Basic.lean:182` | confirmed |
| `IsIntuitionistic T ↔ IPL ⊆ T` (so no MPL instance) | `Defs.lean:171` | confirmed — efq unconstructible |
| `IsBotRuleFree` structural (`efq ↦ False`), NOT `:= True` | code `Basic.lean:223–235` vs note `mpl-base-design-note.md:42–43` | **discrepancy** — use code |
| `MinimalDerivation` = same inductive at `∅`, not ⊥-free type | `Basic.lean:242`; task 409 deferral `Basic.lean:222` | confirmed — O4 |
| mandatory `efq` arm in structural recursion | `Basic.lean:301–303` (`weak`) | confirmed — O4 consumer |
| `bot_val` free at MPL semantics | `BotProperties.lean:24,26–57` | confirmed — O2 |
| Initiality (`HasInitialBot`) landed sorry-free | `BotProperties.lean:53–57`, `BrouwerianBot.lean:236` | confirmed |
| MPL⊂IPL⊂CPL chain sorry-free | `ConservativeChain.lean:152,304`; `Axioms.lean:155,168` | confirmed |
| GHA/HA/BA completeness sorry-free | `HilbertCompleteness.lean:64,93,122,148` | confirmed |
| **Tableau completeness sorries (task 317)** | `Tableau/Minimal/Completeness.lean:110`; `Tableau/Intuitionistic/Completeness.lean:113`; `Scheme.lean:409,1070` | **4 live sorries** |
| Registered MPL/IPL decision instances carry `sorryAx` | `MinDecidability.lean:66`; `IntDecidability.lean:62` | confirmed gap |
| Fragment conservativity side-conditions | `MplConservativeChain.lean:143` (`IsOrBotFree`), `:181` (`IsOrFree`) | confirmed restriction |
| Generic fragment-lift OPEN (task 410) | design note lines 103–113 | confirmed gap |
| Downstream lift CPL-only (Łukasiewicz) | task 415 report §1, §3 | confirmed — O5 |
| Shared-metatheory substrate NO-GO | task 419 report §6–7; task 448 verdict | confirmed — O5 |

**Sorry census method**: `grep -rEn "(^|[^-a-zA-Z])sorry([^-a-zA-Z]|$)"` over
`Cslib/Logics/Propositional/`, filtering doc-prose mentions; four proof-term `sorry`s remain, all
in Tableau (task 317). No `axiom` declarations underlie ConservativeChain/completeness (the
`axiom`-keyword grep hits are all the word "axiom" in prose/identifiers, not `axiom` decls).

---

## Confidence Level per objection

| # | Objection | Confidence it is a genuine weakness the report must address |
|---|---|---|
| O1 | Substitution-invariance is a signature choice, not a decisive theorem; "decisive" is overstated | **HIGH** |
| O2 | ⊥ truly unconstrained (claim holds) BUT vacuous-⊥ theorem cost must be conceded | **HIGH** (claim true; concession mandatory) |
| O3 | Ladder sorry-free only at Hilbert/algebraic layer; tableau/decidability sorries + fragment side-conditions + task-410 open | **HIGH** |
| O4 | No physical ⊥-free base; property-module partly a re-description; concrete vacuous-efq-case cost; design-note `:= True` stale | **MEDIUM-HIGH** |
| O5 | Downstream payoff CPL-only + shared-metatheory NO-GO → "pays off downstream" is speculative; missing Mathlib comparison; community parked Design A | **HIGH** (1–3), **MEDIUM** (4–5) |
