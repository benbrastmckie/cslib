# Research Report: MPL as the structure-first base logic — ⊥ as a nullary connective; explosion/leastness/initiality as independent property modules

- **Task**: 407 `mpl_base_structure_first_redesign`
- **Type**: cslib (Lean 4) — research & design
- **Source design**: user ChatGPT design conversation (`specs/tmp/chat.md`), synthesized against the live codebase
- **Scope**: research only; no source edits made. This report maps the current `Cslib/Logics/Propositional/` architecture against the user's "structure-first" design and produces a systematic refactor direction for the planner.
- **Relation to task 398**: 398 deliberately took the **opposite** commitment (IPL-as-base via a *gated* ND `efq` constructor, MPL retained as a fragment-by-gating). This task charts the deeper redesign the 398 report explicitly postponed (398 report §5, "the unconditional/IPL-base + `IsBotFree` fragment … postponed general-fragment design").

---

## 1. Executive summary

The user's design conversation settles on a clear philosophical and architectural commitment, which I will call **structure-first**:

> Fix **one** language `⟨Atom, ⊥, ∧, ∨, →⟩` once and for all. Treat `⊥` as a primitive **nullary connective** whose meaning is *intentionally underdetermined* in the base logic — a "distinguished constant" supplied by every model, with **no intrinsic proof rule**. **MPL is the base proof theory** (no rule/axiom mentions `⊥`; `¬A := A→⊥`; `A, A→⊥ ⊢ ⊥` is just `impE`). **IPL = MPL + explosion** as an *independent module*; **CPL = IPL + classical principles*. Semantically, leastness (`⊥ ≤ a`), initiality (the universal property `0 → A`), and explosion-soundness are **independent properties** added by conservative strengthening — *not* changes to syntax or to the recursive clauses. **Modularity is organized around properties (typeclasses/mixins), not around connectives**, so the structural metatheory (weakening, substitution, admissibility, cut) is proved **once** at the MPL base and inherited.

The central finding is encouraging: **the codebase is already ~70–80% structure-first**, because the algebraic-semantics and Hilbert-axiom layers were *built* this way. The work this task scopes is therefore mostly **(a) reconciling two layers that diverge from the design** and **(b) reifying implicit properties as the explicit, named modules the design calls for** — not a ground-up rewrite.

Layer-by-layer alignment (detail in §4):

| Layer | Alignment with structure-first design | Gap | Refactor cost |
|---|---|---|---|
| **Algebraic semantics** | **Already aligned** — `AlgEvaluate` takes an arbitrary `bot_val : H` (the Johansson designated constant); `BrouwerianBot` (free `⊥`) vs `PointedBrouwerian` (`⊥` = least) hierarchy exists; `IsBotFree`/`IsOrBotFree` fragments + full conservativity chains | None *required*; optional: reify leastness/initiality/explosion as **named** typeclasses | Trivial–Low |
| **Hilbert axioms** | **Already aligned** — `MinPropAxiom` (8, no `efq`) → `IntPropAxiom` (+`efq`) → `PropositionalAxiom` (+`peirce`); `IsIntuitionistic`/`IsClassical`/`MinimalAxioms` typeclasses; generic deduction theorem/admissibility | None *required*; optional: a formal "Int = Min ⊕ efq" composition lemma | Minimal |
| **Natural deduction** | **Inverted** — task 398's gated `efq` constructor `[IsIntuitionistic T]` makes **IPL the base**; MPL is "the fragment where `efq` is unconstructible" | The conceptual centerpiece of the divergence; needs a decided reconciliation (§5) | Medium |
| **Sequent calculus** | **Largest structural gap** — LJ and LK **hard-code** `botL` (explosion); there is **no minimal `LM`**; structural results (cut, subformula) are proved per-system, not once at a base | Define an MPL/`LM` base; route LJ = LM + `botL` | High |
| **Metalogic (Lindenbaum/completeness)** | **Partial** — generic substrate exists (`GenericMCSBridge`, `MCS`, `DeductionTheorem` are axiom-parameterized) but `Min*`/`Int*` Lindenbaum/closure are ~50% duplicated and `Int*` hard-wires EFQ | Factor a generic closure parameterized by the explosion/consistency property | Medium |
| **Tableau** | **Mostly aligned** — closure already parameterized by `bot_forces`/`botForces`; minimal vs intuitionistic differ only in the closure predicate | Unify the duplicated expansion function | Low |

The single biggest **design decision** the planner must resolve before any code moves is the **ND reconciliation (§5)**: whether to (A) keep the gated `efq` constructor of 398 and *re-document* the inductive as "MPL-base with explosion as a typeclass-gated rule," (B) split the ND inductive into a `⊥`-rule-free base relation plus an explosion extension (true structure-first ND), or (C) adopt the `MinimalAxioms`/typeclass-property framing uniformly so that the ND base is genuinely `⊥`-rule-free and IPL is recovered by an `Explosion` mixin. I recommend **(C)** as the destination and **(A)→(C) staging** as the path (rationale in §5).

This is a **multi-version, design-heavy, formal-faithful** task that touches several subsystems and reverses a recently-landed decision; it is a strong candidate for `--hard` planning/implementation and should be sequenced as several conservative, independently-green waves rather than one big-bang refactor.

---

## 2. The design (from `specs/tmp/chat.md`), distilled

The conversation works through **three conceptions of `⊥`** and rejects two:

1. **`⊥` as absolute falsity** (`V(⊥)=0`, ex falso constitutive). *Too strong* — it forces explosion and so cannot accommodate minimal logic. (chat.md lines 7–30)
2. **`⊥` as an ordinary atom** (no rules, `V(⊥)` unconstrained). *Loses unity* — if `⊥` behaves exactly like an atom it doesn't deserve the name, and IPL/CPL then need an *ad hoc* extra constraint `V(⊥)=0`. (lines 32–56)
3. **`⊥` as a primitive nullary connective** — **the chosen account**. A nullary connective has no premises, hence *no introduction rule fixed by subformula structure* and *no mandatory elimination rule*. Its inferential behaviour is whatever **structural principles the logic chooses to add**. (lines 58–209)

Under (3):
- **Proof theory**: MPL imposes no `⊥` rules; IPL adds `⊥/A` (ex falso); CPL adds that plus classical principles. The systems differ **only by added principles**, not by the meaning of the connective. `¬A := A→⊥`, and `A, A→⊥ ⊢ ⊥` is just `→`-elimination. (lines 77–88, 397–419)
- **Semantics**: a model fixes `V : Atoms ∪ {⊥} → D`; `⊥` gets a designated value just like an atom; the recursive clauses for `∧,∨,→` are **identical across MPL/IPL/CPL**, and only the **admissible model class** differs (MPL: `V(⊥)` arbitrary; IPL/CPL: `V(⊥)` least / `=0`). This is "like restricting Kripke frames rather than redefining connectives." (lines 90–133)
- **Proof-theoretic-semantics fit (Dummett/Prawitz)**: introduction rules fix meaning *where they exist*; a nullary connective has none, so its meaning is *underdetermined* and any `⊥`-rule is a **global** principle, not constitutive. This is exactly why minimal logic may omit ex falso — the omission is "the weakest possible specification of a nullary connective," not a deficiency. (lines 136–209)
- **Categorical reading**: `⊥` is a distinguished object; **explosion = the universal property of an initial object** `0 → A`. MPL has the object *without* the universal property; IPL adds the universal property. "The difference between MPL and IPL is exactly the addition of a universal property — not a change in syntax." (lines 176–197)
- **The decisive meta-point** (lines 327–369, 812–835): the real question is **what stays fixed across the hierarchy**. The Zulip/Lean interlocutor favours **language-first** ("keep each logic minimal; extend the *language* when needed; MPL = `⟨∧,∨,→⟩`, IPL adds `⊥`"); the user favours **structure-first** ("fix one language; interpret some symbols weakly; strengthen by adding axioms/rules/semantic properties conservatively"). Given the user's broader programme — **identity, two induced orders, hyperintensionality, tense, modality, categorical semantics** — structure-first preserves a *single foundational architecture* across all of them, whereas language-first proliferates languages and makes later unification cumbersome.

The user's **concrete proposal** (chat.md §"Proposal: A Modular Foundation", lines 375–585) is a **four-layer architecture**:

- **Layer 1 — Syntax**: the fixed language incl. the primitive nullary `⊥`; no logic-specific assumptions.
- **Layer 2 — Core derivation systems (MPL)**: Hilbert, ND, sequent calculus with **no primitive rule/axiom mentioning `⊥`**; *all* structural metatheorems (weakening, substitution, admissibility, cut) proved here, once.
- **Layer 3 — Logic-extension modules**: explosion, classicality, modality, identity, tense — each adjoined independently; **conservativity becomes immediate**.
- **Layer 4 — Semantics**: independent semantic classes (arbitrary distinguished constant; least element; initial object; Boolean; Heyting; …); soundness/completeness per class.

Guiding principle (lines 576–585): **"modularity should be organized around properties rather than connectives."** Make `⊥` a syntactic constructor and an interpreted constant in every model, but **package explosion, leastness, and initiality as independent extensions (typeclasses/mixins)**, so fragment machinery, structural metatheorems, and conservativity become *orthogonal* to the treatment of `⊥`.

---

## 3. Current architecture (ground truth, with anchors)

Findings below are from a full read of the live sources (June 2026, post-task-398). File:line anchors are exact.

### 3.1 Syntax (Layer 1) — already correct
- `Proposition` is the single inductive with a primitive nullary `bot`; `⊥`, `∧`, `∨`, `→` are the connectives (`Cslib/Logics/Propositional/Defs.lean`, `Proposition` inductive; `bot` at `Defs.lean:85`). `DecidableEq`, `Proposition.subst`/`Monad` (`Defs.lean:126–139`) send `bot ↦ .bot`. **This is exactly the design's Layer 1** — one fixed language with `⊥` primitive. No change needed.

### 3.2 Hilbert axioms (Layer 2/3) — already modular
- `MinPropAxiom` — 8 constructors (`implyK, implyS, andI, andE1, andE2, orI1, orI2, orE`), **no `efq`, no `peirce`** (`ProofSystem/Axioms.lean:126–150`).
- `IntPropAxiom` — the same 8 **plus `efq : ⊥ → φ`** (`Axioms.lean:89–116`, `efq` at `:97–98`).
- `PropositionalAxiom` — Int's 9 **plus `peirce`** (`Axioms.lean:48–78`, `peirce` at `:59–60`).
- Subsumption maps: `MinPropAxiom.toIntPropAxiom` (`:155–165`), `IntPropAxiom.toPropAxiom` (`:168–179`).
- Property typeclasses: `IsIntuitionistic T := efq (A) : (⊥→A) ∈ T` (`Defs.lean:166–167`), `IsClassical T := dne (A) : (¬¬A→A) ∈ T` (`Defs.lean:175–176`), with IPL/CPL instances and extension/subsumption instances (`Defs.lean:182–205`).
- Bundles: `MinimalAxioms` (8 minimal axioms, **no `efq`/`peirce`**) `extends ConjImpAxioms` (`Equivalence.lean:115–123`); instances for Min/Int/Prop axioms (`:126–150`). `ConjImpAxioms` (K,S,∧I,∧E1,∧E2) at `Axioms.lean:191–202`.
- Fragment axioms exist and are documented as *the* MPL/IPL divergence point: `FragmentAxioms.lean:534–538` — "This is the point at which the minimal-logic (MPL) tower diverges from the intuitionistic tower: `⊥` is a free constant rather than the least element with explosion."

**Verdict**: This layer **is** structure-first. `efq` and `peirce` are *added constructors*, not baked into the base; `MinimalAxioms`/`IsIntuitionistic` already express "property, not connective."

### 3.3 Natural deduction (Layer 2/3) — **inverted by task 398**
- `Theory.Derivation` (`NaturalDeduction/Basic.lean`) now includes a **gated** constructor (task 398):
  ```lean
  | efq {Γ A} [IsIntuitionistic T] : Derivation Γ ⊥ → Derivation Γ A   -- Basic.lean:155–156
  ```
  The in-source design block (`Basic.lean:44–79`) explicitly frames this as **"IPL as base, MPL retained as a fragment"**: `⊥` has only an elimination rule and no introduction rule, so the constructor is present in the base inductive and *gated* by `[IsIntuitionistic T]`; MPL = `AxiomTheory MinPropAxiom`, which has **no** `IsIntuitionistic` instance, so `efq` is **unconstructible** there.
- `botE` is now the one-liner `Derivation.efq d` (`DerivedRules.lean`), signature `[IsIntuitionistic T]` preserved.
- Structural metatheorems are **generic over `T`**: `weak` propagates the instance via `instIsIntuitionisticExtention` (`Basic.lean` `weak` arm), `subs`, `substAtom` total; `ndToHilbert` has an `efq` arm using `mem_axiomTheory.mp (IsIntuitionistic.efq A)` (`Equivalence.lean`). The ND↔Hilbert corollaries `hilbert_iff_nd_min/_int/_cl` hold; MPL correspondence is preserved precisely because `efq` is unconstructible at minimal strength.

**Verdict**: This is the **deliberate inversion** of the design. It is *functionally* property-gated (which is close to the design's typeclass idea), but it is *documented and conceived* as IPL-base, and the constructor physically lives in the one inductive used at all strengths. The design wants the **base relation to be genuinely `⊥`-rule-free**, with explosion as a *separately introduced* rule/relation. See §5.

### 3.4 Sequent calculus (Layer 2/3) — **largest gap**
- `LJProof` hard-codes explosion: `| botL (Γ) (C) (_ : ⊥ ∈ Γ) : LJProof (Γ ⊢ C)` (`SequentCalculus/LJ/Basic.lean:91–92`). Not parameterized.
- `LKProof` likewise: `| botL (Γ Δ) (_ : ⊥ ∈ Γ) : LKProof (Γ ⊢ₛ Δ)` (`SequentCalculus/LK/Basic.lean:76–77`).
- **There is no minimal sequent calculus** (`LM`); only `LJ.lean`/`LK.lean` barrels. Cut elimination, subformula property, decidability, interpolation are proved **per system** (`LJ/CutElimination.lean`, `LJ/SubformulaProperty.lean`, …; `LK/…`), not once at a `⊥`-free base.

**Verdict**: Directly contrary to the design's "structural metatheorems proved once at the base." This is where structure-first costs the most (a new `LM` base + re-routing LJ through `LM + botL`).

### 3.5 Metalogic (Layer 2/3) — partial; generic substrate present
- **Generic / axiom-parameterized (good)**: `GenericMCSBridge.lean` (`propAlgDS`, `pl_deriv_iff_algebraic`, parameterized by `Axioms` with `[HasMinimalAxioms]`, `:125–226`); `MCS.lean` (all MCS lemmas parameterized over `Axioms`, `:60–106`); `DeductionTheorem.lean` (parameterized over `Axioms` with explicit K/S witnesses, `:70–81`).
- **Soundness — cleanly separated**: `MinSoundness.min_axiom_sound` checks only minimal schemata, **no `efq` case**, and uses an arbitrary upward-closed `bot_forces` (not fixed to `False`) (`MinSoundness.lean:45–84`). `IntSoundness.int_axiom_sound` adds exactly the `efq` case and sets `bot_forces = fun _ => False` (`IntSoundness.lean:46–88`, `efq` at `:60–63`, hard-set at `:102`).
- **Lindenbaum / completeness — duplicated, EFQ hard-wired**: `MinTheory` has **no consistency requirement** and `min_imp_witness` needs no EFQ (`MinLindenbaum.lean:54–56, 202–217`); `IntDCCS` requires consistency and `int_imp_witness` routes through `intNegPhiImpPsi` which uses `IntPropAxiom.efq` (`IntLindenbaum.lean:36–40, 68–89`, EFQ used at `:248`). Canonical `bot_forces`: `MinStrongCompleteness.minBotForces w := ⊥ ∈ w.val` (genuine predicate, `:93–101`) vs intuitionistic worlds where `⊥` is never forced. Estimated ~50% duplication between `Min*` and `Int*` closure/witness code.

**Verdict**: The substrate to do this generically already exists. The completeness layer needs a **generic deductive-closure / implication-witness parameterized by the explosion property** (the design's "property, not connective" applied to metatheory), instantiated for MPL (no explosion) and IPL (explosion).

### 3.6 Algebraic & Kripke semantics (Layer 4) — **already aligned**
- `AlgEvaluate (v : Atom → H) (bot_val : H)` over `[GeneralizedHeytingAlgebra H]` — `bot_val` is an **arbitrary** parameter, the Johansson designated constant (`Semantics/Algebra.lean:78–96`; the design note at `:34–47` says exactly this). Notation `v ⊨[bot_val] T` (`:156`).
- The leastness vs. arbitrary-constant hierarchy already exists:
  - `BrouwerianBotEvaluate (v) (bot_val)` — free `⊥`, no `OrderBot` (`Brouwerian Bot.lean:72–78`).
  - `BrouwerianEvaluate` — maps `⊥ ↦ ⊤`, no `OrderBot` (`Brouwerian.lean:67–73`).
  - `PointedBrouwerianEvaluate` — `[OrderBot H]`, maps `⊥ ↦ ⊥` (the least element); EFQ soundness via `bot_le` (`PointedBrouwerian.lean:67–73`; `PointedBrouwerianCompleteness.lean:79–93`).
  - Bridge lemmas `pointedBrouwerianEvaluate_eq_botBot`, `brouwerianEvaluate_eq_botTop` (`BrouwerianBot.lean:171–192`).
- Fragment predicates: `IsBotFree` (`Conservative.lean:39–44`), `IsOrBotFree`/`IsOrFree`/`IsImpTopOnly` (`FragmentPredicates.lean:46–68`), subsumption proven (`:135–154`); `bot_val`-neutrality for bot-free formulas (`Conservative.lean:49–65`).
- Completeness per semantic class: `MPL.hilbert_alg_complete` (GHA), `IPL.hilbert_alg_complete` (Heyting), `CPL.hilbert_alg_complete` (Boolean) (`HilbertCompleteness.lean:93–173`), via the Hilbert–Lindenbaum algebra and `canonicalV_spec` truth lemma; conservativity chain `IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ MPL ⊂ IPL ⊂ CPL` (`ConservativeChain.lean:29–40`) with algebraic validity subsumption (`:69`) and a direct-algebraic MPL route (`MplConservativeChain.lean:143–146`).

**Verdict**: This layer **is** the design's Layer 4 already: an arbitrary-constant base with leastness as an *added* property, fragment-relative completeness, conservativity chains. The only design-completeness gap is **nominal**: leastness/initiality/explosion are present as `OrderBot` constraints and per-axiom soundness proofs rather than as a single **named property hierarchy** (`HasBot`/`HasLeastBot`/`HasExplosion`/initial-object).

---

## 4. Gap analysis: design vs. code

Mapping the design's four layers to the codebase:

- **Layer 1 (Syntax)** — ✅ complete. `Proposition` with primitive nullary `⊥` is exactly the fixed language.
- **Layer 2 (Core MPL derivation systems, structural metatheory once)** —
  - Hilbert: ✅ `MinPropAxiom` is a genuine `⊥`-rule-free base; deduction theorem/admissibility generic.
  - ND: ⚠️ inverted (gated `efq` in the one inductive; documented as IPL-base). Structural metatheorems *are* generic over `T`, but the "base = `⊥`-rule-free relation" the design wants is not the object that exists.
  - Sequent calculus: ❌ no `LM` base; `botL` hard-coded in LJ/LK; structural results per-system.
- **Layer 3 (Logic-extension modules; conservativity immediate)** —
  - Hilbert: ✅ `efq`/`peirce` as added constructors; `IsIntuitionistic`/`IsClassical`/`MinimalAxioms` typeclasses.
  - ND: ⚠️ explosion is a *gated constructor*, not an *adjoined module/relation*.
  - Metalogic: ⚠️ generic substrate exists but Lindenbaum/closure duplicate Min/Int and hard-wire EFQ; explosion not factored as a property parameter.
  - Tableau: ⚠️ closure parameterized by `bot_forces` (good), but expansion duplicated.
- **Layer 4 (Semantic classes; soundness/completeness per class)** — ✅ essentially complete; only the **named property hierarchy** (leastness/initiality/explosion as typeclasses) is missing as an explicit artifact.

**Net**: two real structural divergences (ND inversion; sequent-calculus base), one consolidation opportunity (metalogic genericization), and one "reify the implicit" task (named semantic-property hierarchy). Everything else already embodies the design.

---

## 5. The central decision: reconciling Natural Deduction (and the 398 inversion)

This is the crux and must be decided **before** planning code. Three options:

**(A) Keep the gated constructor; re-document as MPL-base with explosion as a typeclass-gated rule.**
The physical inductive is unchanged from 398; only the *narrative* flips: the base relation is "`Theory.Derivation` over an arbitrary `T`," and `efq` is the explosion **module** whose availability is governed by the `IsIntuitionistic` property. Because the constructor is genuinely unconstructible without the instance, MPL-as-base is *already true operationally*.
- *Pros*: zero proof churn; immediately consistent with the design's "property, not connective"; preserves all 398 work, Curry–Howard, normalization. *Cons*: `efq` still lexically sits in the one inductive (a purist reading of "the base has no `⊥` rule" is only met *up to the instance gate*); the design's "adjoin a module" is modelled by a gate rather than by relation composition.

**(B) Split the ND relation: a `⊥`-rule-free `MinDerivation` base + an `Explosion` extension.**
Define the base ND inductive with **no** `efq`, prove all structural metatheory on it, then define IPL-ND as either `MinDerivation` over a theory that supplies `⊥→A` (already possible!) or as an inductive extension adding `efq`. This is the literal structure-first ND.
- *Pros*: exact match to the design; "structural metatheorems proved once" is literally true. *Cons*: largest ND churn; Curry–Howard (`Theory.Term`) and Prawitz normalization (the 398 hard part) must be re-cut against the split; risk of re-opening the subformula-property issue 398 closed.

**(C) Typeclass-property framing as the destination, staged (A)→(C).**
Adopt the `MinimalAxioms`/`IsIntuitionistic` discipline *uniformly* and explicitly across ND and metalogic so the base is genuinely property-gated and the modules are named (`Explosion`, `Classical`, later `Leastness`, `Initial`). Stage it: first land the re-framing (A) with no proof churn; then, only where it buys real reuse, refactor toward genuine relation/closure composition (the metalogic genericization and the `LM` base), leaving the ND inductive gated unless a concrete consumer needs the split (B).
- *Pros*: matches the design's actual principle (modularity around *properties*), captures most value cheaply, keeps every wave green; defers the expensive ND split until justified. *Cons*: the ND inductive remains gated (acceptable — the gate *is* a property module).

**Recommendation: (C).** It honours the design's stated principle ("organize modularity around properties rather than connectives," chat.md:576–585) without paying for a purity (the physical `⊥`-rule-free inductive) the design does not actually require — the design requires that **explosion be an independent, conservatively-added property**, which the `IsIntuitionistic` gate already provides. Reserve (B) for if/when a downstream consumer (e.g. a minimal-ND normalization theorem, or a `λ`-calculus without `abort`) genuinely needs a `⊥`-free derivation object.

> Note for the user: choosing (C) means task 398 is **not reverted** — it is *re-interpreted*. The 398 commit becomes the ND realization of "explosion as a property module," and this task's ND work is mostly **renaming/re-documentation + a `MinimalDerivation` abbreviation** for the gate-free fragment, plus optional (B) later. If you instead want the literal `⊥`-rule-free base inductive now, the planner should select (B) and budget the Curry–Howard/normalization re-cut.

---

## 6. Recommended systematic design (target module map)

Translate the design's four layers to a concrete `Cslib/Logics/Propositional/` shape. **Bold** = new or renamed; the rest already exists and is retained.

- **Layer 1 — Syntax**: `Defs.lean` (`Proposition`, `subst`, `Monad`, `DecidableEq`) — unchanged.
- **Layer 2 — MPL core**:
  - Hilbert: `ProofSystem/Axioms.lean` (`MinPropAxiom` is the base), `Derivation.lean`; `MinimalAxioms`/`ConjImpAxioms` typeclasses (Equivalence.lean); generic `DeductionTheorem.lean`, `AxiomAdmissibility.lean`, `GenericMCSBridge.lean`, `MCS.lean`.
  - ND: `NaturalDeduction/Basic.lean` — under (C), **re-document the base as MPL-with-property-gated-explosion**; add a `Theory.MinimalDerivation`/`IsBotRuleFree` abbreviation for the gate-free fragment; structural metatheory stays generic over `T`.
  - Sequent: **`SequentCalculus/LM/` (new minimal base)** with structural results (cut, subformula) proved once; **route `LJ = LM + botL`** (re-export/compose), so `LJ/CutElimination.lean` etc. *derive from* `LM`.
- **Layer 3 — Property modules** (the design's centerpiece — *named* typeclasses):
  - `IsIntuitionistic` (explosion) and `IsClassical` (DNE/Peirce) — already exist; **promote to the canonical "module" vocabulary** and document the conservativity each induces.
  - **Metalogic genericization**: a single `GenericLindenbaum`/deductive-closure parameterized by a consistency/explosion property, with `Min*`/`Int*` as instances (collapses ~50% duplication; explosion enters only through the property).
  - **Tableau**: a single `propExpandBranches` parameterized by the closure predicate; minimal/intuitionistic become instances.
- **Layer 4 — Semantic classes** (already present; **reify the property hierarchy**):
  - Keep `AlgEvaluate (v) (bot_val)` as the arbitrary-constant base.
  - **Introduce a named property hierarchy** so the design's "leastness/initiality/explosion as independent properties" is a first-class artifact, e.g. `HasDesignatedBot` (base) → `HasLeastBot` (`⊥ ≤ a`, i.e. `OrderBot`) → an **initial-object / `Initial⊥`** witness (categorical universal property), with explosion-soundness proved relative to `HasLeastBot`/initiality. Wire existing `BrouwerianBot` (free) and `PointedBrouwerian` (least) to these names; keep all completeness theorems.

This map keeps every existing theorem and **adds the design's missing artifacts** (the `LM` base, the generic metalogic closure, the named property hierarchy) while re-documenting the two inverted layers.

---

## 7. Suggested phasing for the planner (conservative, each wave green)

Ordered by value-per-cost; later waves are optional/advanced and can be split out as their own tasks.

1. **Wave 1 — Design canonicalization (docs + vocabulary, zero proof churn).** Write the structure-first design as an in-repo design note (Layer 1–4, "property not connective"), reconcile the `Basic.lean:44–79` ND block to the (C) framing, and introduce the **`MinimalDerivation`/`IsBotRuleFree` abbreviation** + `MinimalAxioms`-as-base vocabulary. Verify full `lake build` unchanged. *(Cslib; small.)*
2. **Wave 2 — Named semantic property hierarchy (Layer 4 reification).** Introduce `HasDesignatedBot`/`HasLeastBot`/initial-object typeclasses; re-express `PointedBrouwerian` explosion-soundness through them; keep `MPL/IPL/CPL.hilbert_alg_complete` green. *(Cslib; small–medium.)*
3. **Wave 3 — Metalogic genericization.** Factor `GenericDeductiveClosure`/`generic_imp_witness` parameterized by the explosion/consistency property; re-instantiate `Min*`/`Int*`; delete duplicated code. *(Cslib; medium.)*
4. **Wave 4 — Tableau unification.** Single parameterized `propExpandBranches`; minimal/intuitionistic as closure-predicate instances. *(Cslib; low–medium.)*
5. **Wave 5 — Minimal sequent calculus `LM`.** Define `LM` (no `botL`), prove cut/subformula once, route `LJ = LM + botL`. *(Cslib; high — consider a dedicated task.)*
6. **Wave 6 (optional) — Literal `⊥`-rule-free ND (option B).** Only if a consumer needs it; re-cut Curry–Howard/normalization against the split. *(Cslib; high — dedicated task.)*

Waves 1–2 are pure additions/renames and should land first to make the design *real in the repo* before any structural surgery. Waves 5–6 are the expensive structural items and are good candidates to **spawn as separate tasks** once 1–4 are merged.

---

## 8. Risks, constraints, and zero-debt notes

- **Do not revert or weaken task 398 / MPL assets.** As in 398, all MPL metatheory and conservativity chains (`MinSoundness`, `MinLindenbaum`, `MinStrongCompleteness`, `MplConservativeChain`, `Conservative*`, `HilbertAlgCompleteness`, `Glivenko`) must remain green. Under recommendation (C) they are *retained and re-framed*, not deleted.
- **Curry–Howard & Prawitz normalization (option B only).** The 398 report's single genuine hard point — the subformula property under `efq` — re-opens if ND is physically split (B). Keep (B) out of the early waves; if attempted, re-use the 398 decided strategy (atomic restriction + permutation conversions) and treat a non-green proof as `[BLOCKED]`, never `sorry`.
- **Sequent calculus `LM` (Wave 5)** is the largest single item (new base + cut-elimination once + LJ re-routing). Size it as its own task/`--hard` plan; do not bundle with the cheap waves.
- **Conservativity must stay *immediate*.** The design's selling point is that adding a module is conservative by construction; each new module (explosion, leastness, initiality) should ship with the conservativity/soundness lemma that justifies it, not leave it implied.
- **Categorical / initiality layer** (`0 → A`) is presently only *implicit* (EFQ via `bot_le`). Making it an explicit universal-property witness is desirable for the user's later categorical-semantics programme but is **new mathematics in the repo**; scope it carefully (possibly a dedicated task feeding the broader programme).
- **Zulip AI policy**: any human-facing Zulip prose must be human-authored; in-source design notes/docstrings produced by this work are internal artifacts and are fine, but must not be auto-posted.
- **`--hard` recommended** for the eventual plan/implementation: design-faithful, multi-version, reverses/re-frames a recently-landed decision, spans ≥4 subsystems.

---

## 9. Open questions for the user (to settle before planning)

1. **ND reconciliation**: adopt **(C)** (re-frame the 398 gate as the explosion property module; recommended) or insist on **(B)** (a literal `⊥`-rule-free base ND inductive now, with the Curry–Howard/normalization re-cut)?
2. **Scope of this task**: keep it as **research + design + the cheap reconciliation waves (1–4)**, and *spawn* Waves 5–6 (`LM` base; literal ND split) as separate tasks? Or plan the entire programme under this one task?
3. **Categorical/initiality**: include an explicit initial-object (`0 → A`) witness layer now (Wave 2+), or defer it to the broader categorical-semantics programme?
4. **Naming**: preferred names for the property hierarchy (`HasDesignatedBot`/`HasLeastBot`/`HasExplosion`/`InitialBot`?), to keep consistency with existing `IsIntuitionistic`/`MinimalAxioms`/`PointedBrouwerian`.
5. **Relationship to task 400** (`reconcile_connectives_pr607`): should the language/connective reconciliation there be folded into Wave 1, or kept independent?

---

## 10. Conclusion

The user's structure-first design is not a departure from the codebase so much as a **completion and re-narration** of it. The algebraic-semantics and Hilbert-axiom layers already realize "one fixed language, `⊥` as an arbitrary distinguished constant, explosion/leastness as conservatively added properties." The gaps are concentrated in two layers that diverge (ND, inverted by 398's gated `efq`; sequent calculus, which hard-codes `botL` and lacks a minimal base) and in one layer that should be *consolidated* (metalogic Lindenbaum/closure) plus one set of *implicit* properties that should be *named* (leastness/initiality/explosion as typeclasses). The recommended path keeps every existing theorem, re-frames task 398's gate as the **explosion property module** (option C), reifies the semantic property hierarchy, genericizes the metalogic, and — as a larger, separable effort — introduces the minimal sequent calculus `LM`. Sequencing the cheap, additive waves first makes the design *real in the repo* before any structural surgery, and isolates the two expensive structural items for dedicated, `--hard` follow-on tasks.
