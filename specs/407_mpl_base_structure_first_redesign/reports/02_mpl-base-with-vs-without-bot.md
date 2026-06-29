# Research Report 02: MPL as the base logic — *with* `⊥` vs *without* `⊥` (the core Zulip dispute)

- **Task**: 407 `mpl_base_structure_first_redesign`
- **Type**: cslib (Lean 4) — research & design
- **Sources**: CSLib Zulip channel, topic *Propositional Logic* (34 messages, 2026-06-12 → 2026-06-28; raw capture at `specs/407_mpl_base_structure_first_redesign/reports/zulip-propositional-logic.json`); the user's design conversation `specs/tmp/chat.md`; report 01 (`01_mpl-base-structure-first.md`) for codebase ground-truth.
- **Purpose**: sharpen the ambition of the MPL-base task by reconstructing the *actual* community dispute — **should MPL be the base logic with `⊥` a primitive nullary constructor, or without `⊥` in the base signature at all?** — and comparing the two routes on the dimensions the participants actually argued.
- **Scope**: research only; no source edits. **Zulip AI policy** (msg #605827029, Chris Henson): LLM-drafted prose may not be posted to Zulip. This report and any in-source docstrings are internal artifacts; **any Zulip reply must be human-authored.**

---

## 1. Executive summary

The Zulip thread is, beneath the implementation chatter, a single sustained disagreement about **one design axis**, and it is exactly the axis the user names:

> **Should the base propositional type carry `⊥` as a primitive nullary constructor (interpreted by a free parameter `bot_val`), or should the base be `⟨Atom, ∧, ∨, →(, ⊤)⟩` with no `⊥`, so that `⊥`+`efq` are *added* to obtain IPL?**

Two coherent positions emerged, each held for good reasons:

- **Design A — MPL base *with* `⊥`** (Benjamin / the user). `⊥` is a primitive nullary connective of `Proposition`; MPL is the base proof theory with **no `efq`**; `⊥` is interpreted by a free designated constant `bot_val` (Johansson-algebra semantics; `botForces` on the Kripke side). Decisive argument: **substitution invariance / the free-algebra universal property** (msg #604219492). `⊥`-as-a-real-operation is fixed by every substitution; `⊥`-as-atom is not, so every substitution theorem would acquire a `σ(⊥)=⊥` side condition and the Kleisli/free-algebra universal property would fail.
- **Design B — MPL base *without* `⊥`** (Thomas Waring; Matthew Doty sympathetic). The base is *minimal natural deduction* over the `⊥`-free signature; IPL/CPL are obtained either by **extending the language** with `⊥`+`efq` (Doty's "explicit falsum, and thus EFQ", msg #604166734; Waring's closing compromise, msg #606970606) or by **encoding** them inside MPL via the `⊥ : Atom` theory construction (Waring, msg #605341190). Decisive arguments: **ND intro/elim symmetry** ("a constructor with no semantics is very unnatural", msg #606970606) and the **free-algebra objection** that a `GeneralizedHeytingAlgebra` is *not* an algebra over a signature containing `⊥`, so `bot_val` is an "extra unnatural field" (msg #603884159, #605341190).

**The thread did not fully settle, but it converged to a pragmatic compromise** (Waring, msg #606970606; Doty, msg #605712144): *for now*, take **IPL as the base** (i.e. "if `⊥` is primitive then add `efq`, so minimal logic becomes the positive fragment `IPL⟨→,∧,∨,⊤⟩`"), and **postpone the fragment design** — "forget about minimal logic for the moment." **This is precisely the route task 398 implemented.** The present task asks the deferred question: *can we instead make MPL genuinely the base, and if so with or without `⊥`?*

**Recommendation (detail in §6).** Pursue **Design A (MPL base *with* `⊥`)** — it is the lower-cost, higher-consistency route given the codebase is already built around `MinPropAxiom`-as-base, `bot_val`, and the substitution-invariance argument; and the parametric-completeness machinery Waring admires is **orthogonal** to the proposition-type choice (Benjamin's key concession-reversal, msg #604219492: the `v ⊨ T` completeness "works just as well with primitive `⊥` and `bot_val`"). But **adopt Waring's two legitimate requirements as the intellectual core of the task's ambition**:
1. **ND symmetry** — if `⊥` is a primitive constructor, explosion should be a *real rule/module*, not axiom-indirection (this is what report 01's option C + the gated `efq` already provide; make it principled and documented, not incidental).
2. **Fragment genericity by construction** (Waring's actual closing ask, msg #606970606): *"manipulations on derivations [should] be carried out for those fragments — ideally ensured by the way a fragment is specified, rather than being reproved for each."* This — a fragment-specification mechanism from which structural metatheorems **lift automatically** — is the genuine open research problem, and it simultaneously answers Doty's worry that **conservativity is hard to prove in a class-based approach** (msg #605712144). **Make this the headline ambition of the MPL task.**

The "without `⊥`" route (Design B) should be **documented as the considered alternative and not adopted**, because (a) the free-algebra/substitution argument is decisive for the user's broader programme (identity, hyperintensional, modal — all lean on substitution), (b) `bot_val` is orthogonal to the proposition type and already discharges the conservativity proofs Waring wanted (`ipl_conservative_over_mpl` via `WithBot`, msg #605862751), and (c) Design B would *duplicate the entire formula API* for the language-extension variant, or *reintroduce the `σ(⊥)=⊥` subcategory* for the encoding variant.

---

## 2. The Zulip dispute, reconstructed faithfully

Chronology of the substantive design exchange (message IDs are Zulip anchors; quotations are the participants', not this report's):

- **#603163993 (Benjamin)** — flags that `⊥` was *simulated* via `[Bot Atom]` rather than a primitive constructor, and PRs to make it primitive, to support Hilbert systems across Propositional/Temporal/Bimodal.
- **#603877853 (Doty)** + Ching-Tsun Chou — "I do agree with @Ching-Tsun Chou about a separate bot constructor", and proposes the polymorphic `Evaluate` with `| .bot => ⊥` over a `HeytingAlgebra`.
- **#603884159 (Waring)** — **the pivotal objection**: with `| .bot => ⊥`, *"completeness is no longer true for minimal logic — this is why Benjamin's Kripke definitions need separate fields for the valuation of atoms and of bottom, which is avoided by just making `⊥` an atom itself."* Gives his general completeness theorem over `GeneralizedHeytingAlgebra` with the `v ⊨ T` framing, and notes the trade-off: you can drop the `v ⊨ T` hypothesis for IPL/CPL by requiring `H` be a Heyting/Boolean algebra **and `v ⊥ = ⊥`**.
- **#603958377 / #604025028 (Doty / Waring)** — Dedekind–MacNeille completion strengthens completeness to Heyting algebras; Waring: this *"doesn't address my concern, because that result requires allowing valuations `v` where `v ⊥ ≠ ⊥`, so the problem is with the definition of evaluate"* — *"if it was always mapped to … a bottom element then every model would validate efq."*
- **#604166734 (Doty)** — *"I'm still a proponent of an explicit falsum in the base syntax (and thus EFQ). It's more natural to have separate syntax for positive fragments"* — names the positive fragments `IPL⟨∧,→,⊤⟩` (CCCs) and `IPL⟨→,⊤⟩` (typed SKI / deduction theorem); notes `⊥ : Atom` complicates DPLL.
- **#604219492 (Benjamin) — the substitution-invariance argument (the strongest pro-`⊥`-as-constructor case):**
  - Formulas over `Atom` are the **free algebra** over `{⊥,→,∧,∨}`; substitution is the unique homomorphism (monadic bind). With primitive `⊥`: `| .bot => .bot`, so `⊥` is *fixed by every substitution*; schemes like `⊥ → A` are automatically substitution-closed.
  - With `⊥`-as-atom: bind sends `⊥ ↦ σ(⊥)` (anything), so **every** substitution-closure theorem (`subst_preserves_*Axiom`, `hilbertSubstitution`, `Theory.Derivation.substAtom`) acquires a `σ(⊥)=⊥` side condition — *"you're working in a subcategory of `⊥`-preserving maps where the universal property fails."*
  - Universal-algebra framing: `⊥` is a nullary operation symbol — *same ontological kind as `→` and `∧`*; atoms are generators. The `v ⊥ = ⊥` constraint is *external to satisfaction* (must be carried as a hypothesis through submodels/products/ultraproducts/canonical models).
  - *"arbitrary nullary operator" ≠ "arbitrary atom"*: `bot_val` gives `⊥` a fixed-but-unconstrained interpretation; atom-hood instead lets substitution *replace* `⊥`.
  - **Orthogonality**: Waring's `v ⊨ T` completeness *"works just as well with primitive `⊥` and `bot_val`: the general theorem quantifies over `(v, bot_val)`, the `v ⊨ T` hypothesis does all the work, and specializing to IPL forces `bot_val = ⊥` via the efq axioms."*
- **#605341190 (Waring) — frames the real fork:** *"what I've formalised is minimal natural deduction; the definitions of IPL and CPL should probably be seen as encodings, rather than a once-and-for-all definition … The issue at hand is whether we want MPL encoded as a fragment of IPL, or IPL encoded in MPL via the theory construction."* Restates ND symmetry: *"If we were to add `⊥` to the proposition type, I think we should also add `efq` to the derivation type."* Free-algebra: *"minimal logic doesn't want `⊥` as a constructor — a `GeneralizedHeytingAlgebra` is not an algebra over the signature with `⊥`, which is why you need the extra unnatural field `botVal`."* Concedes: *"if the community strongly wants IPL as the base theory, we should of course do that."*
- **#605712144 (Doty)** — *"Having IPL as a base makes various developments a bit easier."* Fragments deserve a separate thread; *"in a class-based approach, it will be difficult to prove various extensions are conservative."*
- **#605813681 (Benjamin)** — concedes the ND-symmetry point; the cost of full symmetry is *duplicating the entire formula API*; offers the **logical** reason for a hybrid: *"`⊥` is the one connective with no introduction rule in any proof system … making `efq` a theory axiom rather than a derivation constructor reflects this directly: it is absent in MPL and present in IPL/CPL."*
- **#605827029 / #605840135 (Henson / Benjamin)** — **AI policy**: no LLM-authored Zulip prose; Benjamin agrees to avoid AI drafting.
- **#605862751 / #606128428 / #606397657 (Benjamin)** — delivers the semantic conservativity results Waring wanted: `ipl_conservative_over_mpl` via `WithBot` (bot-free formulas don't see the fresh bottom); the IPL chain `IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ IPL⟨∧,→,⊥,⊤⟩ ⊂ IPL` (Hilbert→Brouwerian→PointedBrouwerian→Heyting); and the **MPL-as-top** chain `IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ MPL` by a *direct algebraic route that never passes through IPL*, anchored on `MPL.hilbert_alg_complete`.
- **#606970606 (Waring) — the closing compromise (and the seed for the real ambition):** *"if we are going to have `⊥` as a primitive, we should also have `efq` — then minimal logic becomes `IPL⟨→,∧,∨,⊤⟩` … It seems very unnatural to me to have a constructor with no semantics, even if that was the original treatment of Johansson. It also makes … the `IsBotFree` predicate more natural."* And the **operative requirement**: *"I'm now convinced we will want to consider various fragments, in which case it makes sense to have `efq` as a rule, but I think we should be careful with the design to ensure that manipulations on derivations can be carried out for those fragments — ideally this should also be ensured by the way a fragment is specified, rather than being reproved for each. Given that work … I think it should be postponed to later work, in which case we would forget about minimal logic for the moment."*

**Net**: the community parked the design at **IPL-as-base + postpone fragments** (= task 398), *not because Design A was refuted*, but because the **fragment-genericity** problem was unsolved and minimal logic was set aside to unblock progress. That parked problem is the opening for this task.

---

## 3. The two designs, precisely

### Design A — MPL base *with* `⊥` (primitive nullary; `bot_val` interpretation)
- **Syntax**: `Proposition := atom | bot | and | or | imp` (the *current* type; `Defs.lean`). One language for MPL/IPL/CPL.
- **Proof theory**: MPL = `MinPropAxiom` (no `efq`); IPL = `+efq`; CPL = `+peirce` (the *current* Hilbert layer). ND base is `⊥`-rule-free *as a fragment*; `efq` is the explosion module (report 01 option C; the task-398 gated constructor).
- **Semantics**: `AlgEvaluate v bot_val` over `GeneralizedHeytingAlgebra`, `bot_val` free (Johansson designated constant); `botForces` on the Kripke side. MPL completeness quantifies over `bot_val`; IPL forces `bot_val = ⊥`.
- **Conservativity**: semantic, via `WithBot` / the `Brouwerian`↔`PointedBrouwerian` chain (`IsBotFree`). Already proved on main.

### Design B — MPL base *without* `⊥` (two sub-variants)
- **B1 (language-extension / Doty)**: base type `Proposition⁻ := atom | and | or | imp (| top)`; **no `⊥`**. IPL is a *different* type `Proposition := Proposition⁻ + bot` with `efq` a primitive ND constructor; minimal logic = the `⊥`-free positive fragment `IPL⟨→,∧,∨,⊤⟩`. Algebraic semantics for the base is exactly `GeneralizedHeytingAlgebra` with **no `bot_val`**. `¬` is not expressible in the base.
- **B2 (encoding / Waring)**: a single minimal type/ND over the `⊥`-free signature; `⊥` is *simulated* as a distinguished atom (`⊥ : Atom`), and IPL/CPL are **encoded** via the theory construction (`⊥ → A` as theory axioms over the simulated atom). Cross-system translations carry the encoding (Waring's proof-of-concept branch). Substitutions must live in the `σ(⊥)=⊥` subcategory to keep the encoding faithful.

---

## 4. Comparison on the dimensions the participants argued

| Dimension | Design A (with `⊥`) | Design B (without `⊥`) | Who argued it |
|---|---|---|---|
| **Substitution / free algebra** | ✅ `⊥` fixed by every substitution; schemes substitution-closed; full Kleisli/free-algebra universal property | ❌ B2: `σ(⊥)=⊥` side condition everywhere (subcategory; universal property fails). B1: fine *within* the base, but `⊥`-schemes live in the *other* type | Benjamin #604219492 (decisive pro-A) |
| **ND intro/elim symmetry** | ⚠️ `⊥` is a constructor whose elim (`efq`) is *gated/modular*, not unconditional — "constructor with semantics, supplied by a module" | ✅ B1: `⊥` and `efq` always paired; clean symmetry. B2: no `⊥` constructor at all, so no asymmetry to explain | Waring #605341190 #606970606 (pro-B / pro-efq); Benjamin concedes #605813681 |
| **`bot_val` "unnatural field"** | ⚠️ one extra arg on `AlgEvaluate` + `botForces` field; defended as the Johansson designated constant | ✅ GHA *is* the natural algebra of the `⊥`-free signature; no `bot_val` | Waring #603884159 #605341190 (pro-B); Benjamin rebuttal #604219492 #605813681 |
| **MPL completeness truth** | ✅ true *because* `bot_val` ranges freely (forcing `bot_val=⊥` would validate `efq`, collapsing MPL→IPL) | ✅ B trivially (no `⊥` to over-constrain); but MPL-with-`⊥` completeness is *not even expressible* in B1 | Waring #604025028; Benjamin #605813681 |
| **Conservativity (IPL over MPL, fragments)** | ✅ already done semantically (`ipl_conservative_over_mpl` via `WithBot`; full chains incl. MPL-as-top) | ⚠️ B "conservativity" becomes a *translation/encoding* theorem; Doty: hard in class-based approach | Doty #603958377 #605712144; Benjamin #605862751 #606128428 #606397657 |
| **DPLL / computation** | ⚠️ `⊥ : Proposition` adds clause-handling care; `Bool` route needs `v ⊥ = ⊥` | ✅ B1 positive fragment has no `⊥` to special-case; cleaner CNF/Tseitin | Doty #604166734 #603755068 |
| **Curry–Howard / category theory** | ✅ `⊥` = (weak) distinguished object; `efq` module = initial-object universal property `0→A` (matches chat.md categorical reading) | ⚠️ B1 positive fragments map to CCC / SKI cleanly, but the `⊥`/initial-object story lives only after the language extension | Doty #604166734; chat.md §categorical |
| **Cross-system uniformity (modal/temporal/bimodal)** | ✅ one `Proposition`, one `FromPropositional`, Prop-valued `Evaluate` shared with Kripke | ❌ B1 multiplies proposition types + embeddings; B2 carries the encoding everywhere | Benjamin #603572691 #605813681 |
| **Fragment genericity (lift structural results)** | ❓ *open* — needs a fragment-spec mechanism so weakening/subst/cut lift automatically | ❓ *open* — Waring's encoding lifts results "smaller→larger" easily, but per-fragment manipulation still unsolved | Waring #606970606 (the real ask); Doty #605712144 |

**Reading the table**: Design A dominates on *substitution/free-algebra, cross-system uniformity, conservativity (already done), and the categorical story*; Design B wins on *ND symmetry purity, the `bot_val`-free algebra, and DPLL ergonomics for positive fragments*. The single dimension neither design has solved — **fragment genericity** — is the one Waring elevated to *the* blocking concern, and it is **independent of the with/without-`⊥` axis**: it is about how a *fragment* is specified so that derivation manipulations and conservativity come for free.

---

## 5. What each route costs *in this codebase* (grounded in report 01)

From report 01's layer map (semantics + Hilbert already structure-first; ND inverted by 398; sequent calculus hard-codes `botL`; metalogic ~50% duplicated):

- **Design A is ~80% built.** Making MPL genuinely the base *with* `⊥` is essentially report 01's **option C + keep `bot_val`**: re-frame the 398 gate as the explosion property module (W1), reify the leastness/initiality/explosion property hierarchy (W2), genericize the metalogic (W3), unify tableau (W4); the heavy structural items (`LM` base, literal `⊥`-rule-free ND) are W5/W6 spawned tasks. **No proposition-type change; no loss of the substitution machinery; no new duplication.** This is the cheap, consistent route.
- **Design B is a re-architecture.**
  - **B1** would *duplicate the entire formula API* (monad/bind, `DecidableEq`, `subst`, three evaluators, the two `FromPropositional` embeddings) across the `⊥`-free base type and the IPL type — precisely the cost Benjamin named (#605813681). It would also strand the existing `MinPropAxiom`/`MPL.hilbert_alg_complete`/conservativity assets, which are stated *with* `⊥`.
  - **B2** would reintroduce the `σ(⊥)=⊥` subcategory across every substitution theorem (the universal-property failure of #604219492) and thread the `⊥ : Atom` encoding through modal/temporal/bimodal — reversing the very PR (#603163993) that made `⊥` primitive.

**Conclusion**: the codebase has already paid for Design A. Design B's appeal is conceptual (symmetry; `bot_val`-free algebra), but its concrete cost here is high and it forfeits assets that are green on main.

---

## 6. Focusing the ambition of the MPL task

**Adopt Design A (MPL base *with* `⊥`), and make the headline ambition the unsolved problem Waring flagged: fragment genericity.** Concretely, the MPL task should aim to deliver, in priority order:

1. **MPL genuinely as the base (option C, with `⊥`).** Re-frame the ND inductive so the base relation is `⊥`-rule-free and `efq` is an explicitly-named **explosion module** (typeclass-gated), with a `MinimalDerivation`/`IsBotRuleFree` view of the gate-free fragment. Document the design decision *factually* (as Benjamin already started in `NaturalDeduction/Basic.lean` Implementation notes, #605813681), naming both sides and linking the thread. *(= report 01 W1.)*
2. **A named property hierarchy** for the semantic side (`HasDesignatedBot` → `HasLeastBot`/`OrderBot` → initial-object/`efq`-soundness), making "leastness/initiality/explosion as independent properties" first-class and tying `bot_val`/`PointedBrouwerian` to it. *(= report 01 W2.)* This is also the concrete answer to Waring's "constructor with no semantics" worry: `⊥` *has* semantics (`bot_val`/designated constant) at the base, and *acquires* leastness/initiality as added properties.
3. **Fragment-specification mechanism (the research core).** Design a way to *specify a fragment* (by connective set and/or by an explosion/classicality property) such that structural metatheorems (weakening, substitution, admissibility; and, downstream, cut) **lift to the fragment by construction**, and **conservativity is derivable generically** rather than per-fragment. This directly answers Waring #606970606 ("ensured by the way a fragment is specified, rather than being reproved for each") *and* Doty #605712144 ("conservative extensions hard to prove in a class-based approach"). The existing `IsBotFree`/`IsOrBotFree`/`IsImpTopOnly` predicates + the `MinimalAxioms`/`IsIntuitionistic` typeclasses are the raw materials; the deliverable is the *generic lifting/conservativity layer* over them. *(Extends report 01 W3; this is the intellectual headline.)*
4. **Metalogic genericization + tableau unification** as the concrete payoff of (3): one `GenericLindenbaum`/closure parameterized by the explosion property, `Min*`/`Int*` as instances. *(= report 01 W3/W4.)*

**Explicitly out of scope / documented-but-not-adopted**: Design B (both variants). Record it in the design note as the considered alternative with the trade-off table (§4) so the decision is legible and revisitable, but do not implement it. **Also note the two community process items** from #606970606: (i) connective typeclasses are a *separate* development — coordinate with the existing PR rather than fold in here (cf. open question on task 400); (ii) the references + Zulip-thread link must actually appear in the PR.

**This focusing turns the task from "re-architect for MPL-base" into "make MPL the base *with* `⊥`, and solve fragment genericity"** — which is both the smaller engineering lift *and* the contribution the maintainers said was the real blocker.

---

## 7. Decisions to confirm

1. **Confirm Design A** (MPL base *with* `⊥`) over Design B — recommended. (If you actually want to explore Design B, it should be a *separate* research spike, not this task.)
2. **Elevate fragment genericity to the task's headline deliverable** (§6.3), or keep this task to the mechanical waves (W1–W4) and spawn fragment-genericity as its own research task?
3. **Engagement with Waring's compromise**: the thread's standing agreement is "IPL-base + postpone fragments." Making MPL the base *re-opens* a settled-for-now community decision. Confirm you want to advance this on the PR/thread (with human-authored prose) vs. develop it locally first and present once green.
4. **`bot_val` defense as documentation**: fold Benjamin's substitution-invariance argument (#604219492) into the in-source design note as the canonical justification for `⊥`-as-constructor (recommended — it is the strongest published argument and currently lives only in Zulip).

---

## 8. Relationship to report 01 and to task 398

- Report 01 mapped the codebase and recommended **option C**; report 02 confirms option C **is** the "MPL base *with* `⊥`" route and shows the Zulip dispute favors it on every dimension except ND-symmetry purity and `bot_val`-aesthetics — both of which option C already accommodates (gated `efq` = real rule; `bot_val` = Johansson constant, defended in #604219492).
- Task 398 implemented the thread's *interim* compromise (IPL-base, postpone fragments). This task implements the *deferred* goal (MPL-base) **without reverting 398** — by re-framing, not removing, the gate, and by adding the fragment-genericity layer the compromise was waiting on.
- **Zulip AI policy** remains binding: this report is internal; any thread reply or PR prose must be human-authored (msg #605827029/#605840135).
