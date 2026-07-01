# Teammate A Findings — Proof Theory + Lean 4 Engineering (task 464)

- **Angle**: proof-theory tower (Hilbert / ND / sequent calculus) + Lean engineering of the ⊥-design alternatives
- **Deliverable purpose**: research to inform the Typst argumentative report defending "structure-first MPL". Not the report itself.
- **Grounding read**: 407 design-note, decisions, reports 01–03, zulip snapshot; live source under `Cslib/Logics/Propositional/`; archived task 408 (LM). All anchors below verified against source on 2026-07-01 (post-407, post-408).
- **Scope note / one correction to the 407 reports**: reports 01/03 predate task 408. They flag the sequent calculus as "the largest structural gap (LJ hard-codes `botL`)". **That gap is now closed for LJ**: `SeqProof T` gates `botL` on `[IsIntuitionistic T]` exactly like ND's `efq` (LJ/Basic.lean:100-102). The report should defend the tower as it *now* stands, not as reports 01/03 described it.

---

## Key Findings

### KF1 — The tower realizes "add a rule, not a connective" by ONE uniform Lean device: a typeclass-gated constructor `[IsIntuitionistic T]`

The signature `{⊥,→,∧,∨}` is fixed once (`Proposition`, Defs.lean:81-92). Across three of the four layers, the MPL→IPL step is *the same move*: adjoin the explosion rule as a constructor whose availability is toggled by whether the theory `T` carries the `IsIntuitionistic` property. `IsIntuitionistic T ↔ IPL ⊆ T` (Defs.lean:171), and `MPL = ∅` (Defs.lean:154) admits no instance, so the rule is **structurally unconstructible** (not merely inadmissible) at minimal strength.

| Layer | Base object (MPL) | Explosion added as | Gate site |
|---|---|---|---|
| **Hilbert** | `MinPropAxiom` (8 ctors, no efq) | a **larger axiom predicate** `IntPropAxiom` (+`efq`) → `PropositionalAxiom` (+`peirce`) with subsumption maps | Axioms.lean:126-150 (Min); :96-98 (Int efq); :56-60 (Peirce); :155,:168 (`toIntPropAxiom`/`toPropAxiom`) |
| **Natural deduction** | `MinimalDerivation := MPL.Derivation` (efq unconstructible) | a **gated constructor** `efq [IsIntuitionistic T]` in the shared `Theory.Derivation` | NaturalDeduction/Basic.lean:182-183 (efq); :223-243 (`IsBotRuleFree`, `MinimalDerivation`) |
| **Sequent (LJ / minimal LM)** | `SeqProofMinimal := SeqProof MPL` (botL unconstructible) | a **gated constructor** `botL [IsIntuitionistic T]` in the shared `SeqProof T` | SequentCalculus/LJ/Basic.lean:100-102; `LJProof := SeqProof IPL` |
| **Curry–Howard terms** | minimal term calculus (no abort) | a **gated constructor** `efq/abort [IsIntuitionistic T]` in shared `Theory.Term` | CurryHoward/Defs.lean:103 |
| **Semantics (algebra)** | `AlgEvaluate v bot_val` over GHA (free `bot_val`) | additive `Prop`-mixins `HasLeastBot`/`HasInitialBot` | Semantics/Algebra.lean:94-100; Algebra/BotProperties.lean:92, :149 |

The single most defensible sentence for the Typst report: **the same `[IsIntuitionistic T]` gate is the MPL→IPL delta in the Hilbert, ND, sequent, and Curry–Howard layers simultaneously, and the same additive-mixin idea (`HasLeastBot`) is its semantic mirror — so "IPL = MPL + explosion" is one architectural fact instantiated four times, not four coincidences.** (Confidence: high — all four anchors verified.)

### KF2 — Each system realizes structure-first *faithfully to a different degree*; the Hilbert layer is the purest, ND/sequent are "pure up to the gate"

- **Hilbert (purest / genuinely ⊥-rule-free base).** `MinPropAxiom` is a *separate inductive predicate* with no `efq` case at all (Axioms.lean:126-150). There is no `⊥`-clause anywhere in the base; the base literally cannot mention explosion. Structural metatheory is parameterized over the axiom predicate (`ConjImpAxioms`, Axioms.lean:191-202; `GenericTheory`/`GenericDeductiveClosure`, GenericLindenbaum.lean:88,99; `DeductionTheorem` over `Axioms`). This is the layer whose *object* matches the design word-for-word.
- **ND and sequent (pure up to the instance gate).** One shared inductive carries `efq`/`botL`, gated. The base *relation* (`MinimalDerivation`, `SeqProofMinimal`) is ⊥-rule-free operationally because the gate is unconstructible at MPL strength, but the constructor is *lexically present* in the type used at all strengths. The design does not actually require the constructor's physical absence — it requires explosion to be an *independently, conservatively added property*, which the gate provides. Structural Hauptsatz (weak/subs/substAtom/cut in ND; height/mono/CutFree/cut-elimination/subformula in sequent) is proved **once, generic over `T`** (NaturalDeduction/Basic.lean:286-408; task-408 summary lines 17-25).
- **Semantics (fully structure-first).** Free `bot_val` base, leastness/initiality as additive mixins; `instHasLeastBotOrderBot` (BotProperties.lean:98) recovers canonical IPL/CPL; `HasInitialBot` (BotProperties.lean:149) makes the categorical "explosion = initial-object universal property `0→A`" a first-class artifact — this is the Q3 "new math" from decisions.md now landed.

Where the tower does **not** yet fully realize structure-first: **LK** still hard-codes an *ungated* `botL` (LK/Basic.lean:76-77). This is defensible — LK is multi-conclusion/classical, always at ≥IPL strength, so gating is vacuous there — but the report should state it explicitly rather than claim uniform gating. (Confidence: high.)

### KF3 — The ND controversy resolves to Option C, and the decisive reason is Curry–Howard/Prawitz, not aesthetics

Option C ("the gate IS the property module") is adopted (decisions.md Q1; report 03 F1/A1). The precise sense in which the gate is a property module: a *property module* in this design = an independently-adjoinable, conservative property a logic may or may not have; `IsIntuitionistic` is literally a `Prop`-typeclass (Defs.lean:166) equivalent to `IPL ⊆ T` (Defs.lean:171), additive under extension (`instIsIntuitionisticExtension`, Defs.lean:190). Instance *resolution* toggles the constructor — so the gate is the Lean encoding of "T has the explosion property," not an ad-hoc flag.

Why C over B specifically (the Curry–Howard/Prawitz difficulty B reopens): Option B physically splits ND into a ⊥-rule-free base inductive + an Explosion extension. But the *same* inductive is mirrored by the Curry–Howard term language `Theory.Term`, which gates `abort` identically (CurryHoward/Defs.lean:103) and *reconstructs* it under reduction (Reduction.lean). Splitting the derivation type forces a parallel split of the term type, and then the **subformula-property / normalization theorem — the single genuinely hard result task 398 closed — must be re-cut against the split**, risking its reopening (report 01 §5, §8; report 03 A1 "residual honesty"). Option C keeps one inductive ⇒ one normalization/subformula proof serves all strengths, and MPL-restriction is free via the missing instance. (Confidence: high on the architecture; medium on "normalization would actually break" — no one has attempted B, so this is a well-grounded risk assessment, not a proved obstruction.)

### KF4 — Design A wins the Lean engineering comparison decisively on substitution; B1/B2 costs are concrete and forfeit green assets

The load-bearing Lean fact is `Proposition.subst`'s `| bot => .bot` clause (Defs.lean:131) making `⊥` a **fixed point of every substitution**, so `Theory.Derivation.substAtom` is *total and uniform* — its `efq` arm re-derives explosion in the substituted theory with no side condition (NaturalDeduction/Basic.lean:408). This is the substitution-invariance / free-monad argument (Zulip #604219492) realized in code. B2 (`⊥ : Atom`) breaks exactly this: `bind` sends `⊥ ↦ σ(⊥)`, so every substitution-closure theorem acquires a `σ(⊥)=⊥` side condition and lives in a subcategory where the Kleisli universal property fails. B1 (separate ⊥-free type) forces duplication of the entire formula API and strands the ⊥-stated assets (`MinPropAxiom`, `MPL.hilbert_alg_complete`, the conservativity chains). (Confidence: high.)

---

## Recommended Approach (what I would defend in the Typst report)

**Defend Design A + Option C + the gated-constructor tower as a single coherent thesis, anchored on substitution-invariance and one-inductive metatheory reuse.** The argument structure I recommend:

1. **Lead with the free-algebra/substitution argument as the *root* justification**, because it is the one argument that is (a) decisive, (b) already realized in code (`subst` bot-fixpoint + total `substAtom`, Defs.lean:131 / Basic.lean:408), and (c) the reason A beats *both* B1 and B2. Everything else (ND symmetry, `bot_val` aesthetics) is downstream of this.
2. **Present "IPL = MPL + explosion" as one gate instantiated four times** (KF1 table). This is the strongest structure-first evidence: the modularity is not narrated, it is *mechanically shared* across Hilbert axioms, ND, sequent LM/LJ, and Curry–Howard terms, with the semantic mirror in `HasLeastBot`/`HasInitialBot`.
3. **Concede honestly and turn the concession into a strength.** Two honest concessions make the report credible: (i) ND/sequent are structure-first "up to the gate" — the `efq`/`botL` constructor is lexically present in the shared inductive; (ii) LK's `botL` is ungated. Frame (i) as *deliberate*: the design requires explosion to be a *conservatively-added property*, not a *syntactically-absent* one, and the gate delivers precisely that while enabling one-proof metatheory. Frame (ii) as *principled*: LK is classical, so the gate is vacuous.
4. **Give B its due as a bounded, deferred option, not a rejected one.** The strongest residual case for B (below) is real and is why task 409 exists; acknowledging it is more persuasive than dismissing it.

**Strongest argument FOR C (defend this):** one shared `Theory.Derivation` ⇒ one substitution monad, one set of structural metatheorems (`weak`/`subs`/`substAtom`/`cut` proved once generic over `T`, Basic.lean:286-408), one Curry–Howard term language, one cut-elimination/subformula proof at the sequent layer (task 408), and immediate conservativity (`MPL ⊆ IPL` by subset/instance). Zero duplication propagates to Modal/Temporal/Bimodal, which reuse the single `Proposition` + `FromPropositional` `| .bot => .bot` bridges.

**Strongest residual argument FOR B (state it, then bound it):** Option C's `MinimalDerivation` is an `abbrev` for `MPL.Derivation`, whose *type still contains the `efq` constructor* — every induction/case-analysis over a minimal derivation must still discharge the `efq` arm (vacuously, `IsBotRuleFree` sends it to `False`, Basic.lean:235). When you genuinely need a ⊥-free derivation *object* — a minimal-ND normalization theorem, a Curry–Howard λ-calculus provably without `abort` (extraction where the term type must not even mention abort), or a clean structural induction with no gate arm — a physically ⊥-free inductive removes that arm entirely and yields a term type that *provably cannot* mention explosion. That residual value is exactly why B is *deferred* (task 409), not refuted. Recommend the report position B as "the right tool when the ⊥-free derivation is itself the object of study," which is not the case for the current metatheory.

---

## Evidence / Examples (exact file:line + snippets)

### E1 — Fixed signature; ⊥ primitive nullary constructor; substitution bot-fixpoint
`Cslib/Logics/Propositional/Defs.lean:81-92, 128-139`
```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom) | bot | imp (a b) | and (a b) | or (a b)          -- :81-92
def Proposition.subst (f : Atom → Proposition Atom') : Proposition Atom → Proposition Atom'
  | atom x => f x
  | bot    => .bot                                                     -- :131  ⊥ is a substitution fixpoint
  | imp A B => .imp (A.subst f) (B.subst f) | ...
instance : Monad Proposition where pure := .atom; bind A f := A.subst f -- :137-139
```

### E2 — The explosion property module and its `↔ IPL ⊆ T` characterization + additivity
`Cslib/Logics/Propositional/Defs.lean:154-191`
```lean
abbrev MPL : Theory Atom := ∅                                          -- :154
abbrev IPL : Theory Atom := Set.range (Proposition.imp ⊥ ·)           -- :157-158
class IsIntuitionistic (T : Theory Atom) where
  efq (A) : (⊥ → A) ∈ T                                                -- :166-167
theorem isIntuitionisticIff : IsIntuitionistic T ↔ IPL ⊆ T := by grind -- :171
theorem instIsIntuitionisticExtension [IsIntuitionistic T] (h : T ⊆ T') :
    IsIntuitionistic T' := by grind                                    -- :190-191 (additivity)
```

### E3 — Hilbert tower: genuinely ⊥-rule-free base + additive predicates + subsumption
`Cslib/Logics/Propositional/ProofSystem/Axioms.lean`: `MinPropAxiom` 8 ctors, no efq (:126-150); `IntPropAxiom.efq : ⊥ → φ` (:96-98); `PropositionalAxiom.peirce` (:58-60); `MinPropAxiom.toIntPropAxiom` (:155), `IntPropAxiom.toPropAxiom` (:168); `ConjImpAxioms` factor class (:191-202). MPL consistency: `min_consistent : ¬ Derivable MinPropAxiom ⊥` (`Metalogic/MinLindenbaum.lean:219-224`).

### E4 — ND: one shared inductive, gated efq; gate-free fragment *named*; generic structural metatheory
`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
```lean
inductive Theory.Derivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  | ax | ass | andI | andE1 | andE2 | orI1 | orI2 | orE | impI | impE   -- 10 ungated (MPL base)
  | efq {Γ A} [IsIntuitionistic T] : Derivation Γ ⊥ → Derivation Γ A   -- :182-183 gated
def Theory.Derivation.IsBotRuleFree : T.Derivation Γ A → Prop
  | ... | efq _ => False                                               -- :223-235
abbrev Theory.MinimalDerivation (Γ) (A) := MPL.Derivation Γ A          -- :242-243
```
Generic metatheory (proved once, `efq` arm just propagates the instance):
```lean
def Theory.Derivation.weak (hTheory) (hCtx) : T.Derivation Γ A → T'.Derivation Δ A
  | efq D => haveI : IsIntuitionistic T' := instIsIntuitionisticExtension hTheory
             efq (D.weak hTheory hCtx)                                  -- :301-303
def Theory.Derivation.substAtom (f) : T.Derivation Γ B → (T.subst f).Derivation (Γ.subst f) (B >>= f)
  | efq D => impE (ax (Set.mem_image_of_mem (· >>= f) (IsIntuitionistic.efq _))) (D.substAtom f) -- :408
```
The `substAtom` efq arm (:408) is the substitution-invariance argument *as executable code*: because `⊥ >>= f = ⊥` (E1), the substituted theory `T.subst f` still contains `⊥ → (B>>=f)` via `IsIntuitionistic.efq`, so the transported derivation reconstructs explosion with **no side condition**. B2 could not write this line without a `σ(⊥)=⊥` hypothesis.

### E5 — Sequent: minimal LM = `SeqProof MPL` via the *same* gate; LJ = `SeqProof IPL`; Hauptsatz once
`Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean:94-102`
```lean
inductive SeqProof (T : Theory Atom) : @Sequent Atom → Type u where
  | ax (A) (Γ) (_ : A ∈ Γ) : SeqProof T (Γ ⊢ A)
  | botL (Γ) (C) [IsIntuitionistic T] (_ : (⊥ : Proposition Atom) ∈ Γ) :
      SeqProof T (Γ ⊢ C)                                               -- :100-102 gated, exact analogue of efq
  | andL | andR | orL | orR1 | orR2 | impL | impR | weakL | cut
```
Task 408 summary (`specs/archive/408_minimal_sequent_calculus_lm/summaries/01_gated-botl-seqproof-summary.md:10-25`): `LJProof := SeqProof IPL`, `SeqProofMinimal := SeqProof MPL`; `height`/`mono`/`CutFree`/`IsBotRuleFree`/cut-elimination/subformula proved once generic over `T`; full `lake build` green, zero debt. Engineering wrinkle (:29-34): matching a gated constructor at generic `T` needs the `@`-qualified pattern `@SeqProof.botL _ _ _ _ _ inst hbot` and reconstruction needs `letI := inst` (else Lean tries to *synthesize* `IsIntuitionistic T` and fails). This is the concrete Lean cost of the gate.

**LK exception (state in report):** `LKProof.botL` is ungated (`SequentCalculus/LK/Basic.lean:76-77`) — classical/multi-conclusion, gate vacuous.

### E6 — Semantics mirror: free `bot_val` base; leastness/initiality as additive mixins; categorical `0→A`
`Cslib/Logics/Propositional/Semantics/Algebra.lean:94-100` (`AlgEvaluate v bot_val`, `.bot => bot_val`).
`Cslib/Logics/Propositional/Semantics/Algebra/BotProperties.lean`:
```lean
class HasLeastBot (b : H) : Prop where bot_le_val : ∀ a, b ≤ a          -- :92-95
instance instHasLeastBotOrderBot : HasLeastBot (⊥ : H) := ...           -- :98-101 (recovers canonical IPL/CPL)
lemma algEvaluate_imp_bot_eq_top [HasLeastBot bot_val] :
    AlgEvaluate v bot_val (⊥ → A) = ⊤                                   -- :117-122 (explosion soundness)
class HasInitialBot (b : H) : Prop where initialArrow : ∀ a, b ≤ a      -- :149-153 (initial-object universal property 0→A)
instance instHasInitialBotOfHasLeastBot [HasLeastBot b] : HasInitialBot b -- :157-159
```

### E7 — Generic metalogic substrate (conservativity/Lindenbaum reuse), Design-A-only
`Cslib/Logics/Propositional/Metalogic/GenericLindenbaum.lean:88-99` (`GenericTheory`, `GenericDeductiveClosure` parameterized by `Axioms` + `Cons`; instantiated by `MinTheory`/`IntDCCS`). `Metalogic/ConservativityLift.lean:56,108`; `MinStrongCompleteness.minBotForces w := ⊥ ∈ w.val` (MinStrongCompleteness.lean:101-114) is a *genuine* predicate — MPL completeness works precisely because `bot_val`/`botForces` range freely; forcing `⊥` false would validate efq and collapse MPL→IPL.

### E8 — Curry–Howard term language gates abort identically (why B forks two types)
`Cslib/Logics/Propositional/CurryHoward/Defs.lean:57,102-103`: `Theory.Term` with `| efq [IsIntuitionistic T] : Term Γ ⊥ → Term Γ A` (abort). Splitting the derivation inductive (Option B) forces a parallel split here and a re-cut of `Reduction.lean` normalization.

---

## Confidence Level (per claim)

| # | Claim | Confidence | Basis |
|---|---|---|---|
| KF1 | One `[IsIntuitionistic T]` gate is the MPL→IPL delta across Hilbert/ND/sequent/CH; `HasLeastBot` is its semantic mirror | **High** | All 5 anchors read directly (Axioms, Basic, LJ/Basic, CurryHoward/Defs, BotProperties) |
| KF2 | Hilbert is genuinely ⊥-rule-free base; ND/sequent are "pure up to the gate"; LK ungated | **High** | `MinPropAxiom` has no efq (Axioms.lean:126-150); LK/Basic.lean:76-77 ungated |
| KF3 | Option C adopted; B reopens Curry–Howard/Prawitz subformula/normalization difficulty | **High** (adoption + architecture); **Medium** (that B *would* break normalization) | decisions.md Q1; report 03 A1; CurryHoward/Defs.lean:103 + Reduction.lean; no one has attempted B, so the break is a grounded risk not a proof |
| KF4 | Design A dominates B1/B2 on substitution; `substAtom` total via bot-fixpoint | **High** | Defs.lean:131 + Basic.lean:408 read directly; B2 side-condition is the logical negation of the bot-fixpoint |
| — | "The gate IS a property module" is a precise claim, not a slogan | **High** | `IsIntuitionistic` is a `Prop` class ↔ `IPL ⊆ T`, additive (Defs.lean:166,171,190) |
| — | Sequent gap from reports 01/03 is now closed (task 408) | **High** | LJ/Basic.lean:100-102 + 408 summary; supersedes reports 01/03 which predate 408 |
| — | Residual case for B (need a ⊥-free derivation *object*) is real | **Medium-High** | `MinimalDerivation` abbrev still carries `efq` ctor (Basic.lean:235,242); task 409 exists for exactly this |
| — | Zulip debate favors A on every axis except ND-symmetry-purity and `bot_val` aesthetics | **High** (secondhand) | report 02 §4 table, reconstructed from zulip-propositional-logic.json |

### Notes for the report authors / downstream
- **Correct the 407-era "sequent is the largest gap" framing** — cite task 408 as the closure.
- **Do not overclaim uniform gating** — LK is the one ungated `botL`; disclose and justify (classical, gate vacuous).
- **The `@`-pattern + `letI := inst` cost** (408 summary:29-34) is the honest engineering price of the gate; mentioning it strengthens credibility.
- **`bot_val` "unnatural field"** is the strongest B-side aesthetic point (Waring, #603884159/#605341190); the rebuttal is that it is the Johansson designated constant and orthogonal to completeness (#604219492), now reified as `HasLeastBot`/`HasInitialBot`.
