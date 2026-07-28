# Research Report 01: Literal ⊥-rule-free base ND (option B) — split MinDerivation + Explosion

- **Task**: 409 `bot_rule_free_nd_option_b` (SPAWNED from 407, Wave 6, OPTIONAL/advanced)
- **Type**: cslib (Lean 4) — research & design; no source edits
- **Depends on**: 407 (landed option C), ideally 408 (LM minimal sequent calculus)
- **Scope**: Locate ND infrastructure; assess state left by 407/398; **evaluate the trigger
  condition**; if fired, map the MinDerivation+Explosion split, the hard point, and the re-cut
  cost; identify base+extension patterns.

---

## 1. Executive summary and headline recommendation

**Recommendation: DO NOT pursue option B now. The task's own trigger condition is NOT met.**

Option B is explicitly gated: *"only pursue if a concrete downstream consumer needs a physically
⊥-free derivation object."* A full codebase sweep found **no such consumer**:

- `Theory.MinimalDerivation` and `Theory.Derivation.IsBotRuleFree` (the gate-free-fragment naming
  devices 407 landed) are referenced **only inside their own defining file**
  (`NaturalDeduction/Basic.lean`) — no external module consumes a physically ⊥-free object.
- There is **no minimal-ND normalization theorem** that needs a ⊥-free inductive: all
  normalization/subformula-property machinery is proved once on the shared `Theory.Derivation`
  and handles `efq` generically. Crucially, the subformula property **under `efq` is already
  discharged** in the option-C code (see §4.2) via axiom-grounding — the "single genuinely hard
  point" of task 398 is currently *closed*, and option B would deliberately **re-open** it.
- The STLC lambda calculus (`Cslib/Languages/LambdaCalculus/LocallyNameless/Stlc/`) is a
  standalone development with **no bottom type and no abort combinator**; it does not consume
  `Theory.Term` (the Curry–Howard mirror) and is not wired to Propositional ND at all. There is
  no "lambda calculus without an abort/efq combinator" that consumes the ND Curry–Howard object.

Because the trigger is unmet, pursuing option B would pay the HIGH-effort cost (re-cutting
Curry–Howard and Prawitz normalization against the split, re-opening subformula-property-under-
`efq`) for **zero downstream benefit**, while risking regression of assets that are green on main.
Sections 4–6 nonetheless map the split *hypothetically* (as the task requests) so the work is
legible and revisitable if a future consumer appears.

**Suggested disposition:** keep task 409 in a non-started/deferred state (or mark `[BLOCKED]` on
"trigger condition unmet — no physically-⊥-free consumer exists"), with this report recording the
concrete re-trigger signal to watch for (§4.3).

---

## 2. State left by tasks 407 and 398 (objective 2)

**Task 407 landed option C** (confirmed from `specs/407_.../decisions.md`, Q1: *"Option C …
Reframe task-398 gate as explosion-property module; option B stays deferred to task 409. No proof
churn."*). Note: report 01 of 407 recommended (C) as destination via an (A)→(C) staging; the
decisions file records the landed choice as option C.

The base relation is therefore **⊥-rule-free *up to the `IsIntuitionistic` gate***, not physically
⊥-free. Concretely, `Theory.Derivation` is a **single inductive with 11 constructors** in which
`efq` is gated:

```lean
-- Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:146-183
inductive Theory.Derivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  | ax | ass | andI | andE1 | andE2 | orI1 | orI2 | orE | impI | impE   -- 10 ungated rules
  | efq {Γ} {A} [IsIntuitionistic T] : Derivation Γ ⊥ → Derivation Γ A   -- gated 11th
```

407 added two **naming devices** for the gate-free fragment (Basic.lean:203–243), *without* a new
inductive:
- `Theory.Derivation.IsBotRuleFree` (Basic.lean:223) — a `Prop` recursor over a derivation, `False`
  exactly on the `efq` node.
- `Theory.MinimalDerivation Γ A := MPL.Derivation Γ A` (Basic.lean:242) — the `T = MPL = ∅`
  instantiation; since `MPL` admits no `IsIntuitionistic` instance, `efq` is structurally
  unconstructible there, so every `MinimalDerivation` is automatically `IsBotRuleFree`.

**No task 398 spec directory exists** (`specs/398_*` absent). The decided-strategy provenance for
the subformula-property hard point survives in 407 report 01 (§ "Curry–Howard & Prawitz
normalization (option B only)"): *"re-use the 398 decided strategy (atomic restriction +
permutation conversions) and treat a non-green proof as `[BLOCKED]`, never `sorry`."*

---

## 3. ND infrastructure inventory (objective 1) — exact paths and lines

All under `Cslib/Logics/Propositional/`.

| Concern | File | Key anchors |
|---|---|---|
| ND inductive `Theory.Derivation` (11 ctors, gated `efq`) | `NaturalDeduction/Basic.lean` | inductive `146-183`; `efq` ctor `182-183` |
| `IsIntuitionistic` gate mechanics + docs | `NaturalDeduction/Basic.lean` | design notes `48-100`; `instIsIntuitionisticExtension` used at `302` |
| `IsBotRuleFree` predicate | `NaturalDeduction/Basic.lean` | `223-235` (`efq ⇒ False` at `235`) |
| `MinimalDerivation` abbrev | `NaturalDeduction/Basic.lean` | `242-243` |
| Structural metatheory (weak/cut/subs/substAtom) — each threads `efq` | `NaturalDeduction/Basic.lean` | `weak 286-303` (`efq 301-303`); `cut 334-338`; `subs 363-389` (`efq 389`); `substAtom 392-408` (`efq 408`) |
| `IsIntuitionistic` typeclass def + `IsIntuitionistic.efq` axiom witness | `Defs.lean` | (`IsIntuitionistic.efq A : (⊥ → A) ∈ T`) used in Basic/SubformulaProperty |
| **Curry–Howard mirror** `Theory.Term` (11 ctors, gated `efq`/abort) | `CurryHoward/Defs.lean` | inductive `57-104`; `efq`/abort ctor `100-104`; ctor↔ctor table `22-34` |
| CH equivalence `Derivation ≃ Term` | `CurryHoward/Isomorphism.lean` | `curryHowardForward 54` (`efq 67`); `curryHowardBackward 74` (`efq 87`); round-trips `94,112`; `curryHowardEquiv 30` |
| CH reduction | `CurryHoward/Reduction.lean` | (274 lines) |
| Normalization: predicates, `height`, `formulas`, `SubformulaProperty` def | `NaturalDeduction/Normalization/Basic.lean` | `height 49-60` (`efq 60`); `isNormal 72-97` (`efq 97`); `isStronglyNormal 136-165` (`efq 165`); `formulas 237-248` (`efq 248`); `SubformulaProperty 252-257` |
| Normalization: root reduction, permutative/commuting conversions, `normalize` | `NaturalDeduction/Normalization/Reduction.lean` | `reduceRoot 66`; `subsOne 45`; `normalizeAux 84` (`efq 99`); `normalize 105` |
| Normalization: termination/strong-normal-form driver | `NaturalDeduction/Normalization/Termination.lean` | 1103 lines (`snForm`, `exists_stronglyNormal_form`) |
| **Subformula property** (the 398 hard point, currently closed) | `NaturalDeduction/Normalization/SubformulaProperty.lean` | main `subformula_property 305-309`; `..._of_isStronglyNormal 52`; **`efq` case `282-294`** |
| Barrel | `NaturalDeduction/Normalization.lean` | 12 lines |
| IPL-ND recovery from Hilbert (efq via axiom) | `NaturalDeduction/FromHilbert.lean` | `botE 97`, `botEDeriv 195`; `subst_preserves_axiom … efq 240` |

Related (not ND, but referenced): sequent-calculus `SeqProof.IsBotRuleFree`
(`SequentCalculus/LJ/Basic.lean:238-249`) — a parallel gate-free predicate on the LJ inductive;
`LM/Basic.lean:20-54` documents the analogous gated-`botL` design and `not_isIntuitionistic_mpl`.

---

## 4. Trigger-condition evaluation (objective 3) — the critical result

### 4.1 The consumer sweep — negative

Searched the entire `Cslib/` tree for anything that requires a *physically* ⊥-free derivation
object:

1. **`MinimalDerivation` / `IsBotRuleFree` consumers**: `grep` finds references **only** in
   `NaturalDeduction/Basic.lean` itself (definitions + docstrings). No metalogic, normalization,
   embedding, or language module destructs a ⊥-free object or requires one in a hypothesis.
2. **Minimal-ND normalization theorem**: none exists as a distinct artifact. The
   normalization/subformula results are stated for the shared `Theory.Derivation` over arbitrary
   `T` and dispatch `efq` uniformly (§4.2). They do **not** need, and do not benefit from, a
   physically ⊥-free inductive.
3. **Lambda calculus without abort/efq**: `Cslib/Languages/LambdaCalculus/.../Stlc/Basic.lean`
   defines `Ty Base` (`39`) and `Typing` (`51`) — a self-contained simply-typed λ-calculus with
   **no bottom type, no abort**. It is already abort-free *by construction* and is **not** built
   on `Theory.Term`; it is not a consumer of the ND Curry–Howard object. The intrinsically-typed
   `Theory.Term` mirror (`CurryHoward/Defs.lean`) is the only thing tied to ND, and its `efq`
   (abort) is the gated 11th constructor — nothing downstream asks for a `Term` guaranteed to omit
   it.

**Verdict: trigger NOT fired.** No concrete downstream consumer needs a physically ⊥-free
derivation object today.

### 4.2 Why the "hard point" is currently *closed* (and option B would re-open it)

The single genuinely hard point flagged for option B — the subformula property under `efq` — is
**already proved** in the option-C code, because gating `efq` on `[IsIntuitionistic T]` hands the
proof a theory axiom to ground on. From `SubformulaProperty.lean:282-294`:

```lean
| @efq _ _ i D ih =>
    -- efq's conclusion A is grounded by the axiom ⊥ → A ∈ T. Any formula B in the
    -- ⊥-subderivation is a subformula of ⊥, hence (via imp_left) of ⊥ → A ∈ T.
    ...
    · exact Or.inr (Or.inr ⟨_, IsIntuitionistic.efq A,
        Proposition.IsSubformula.trans hBsub Proposition.IsSubformula.imp_left⟩)
```

The `[IsIntuitionistic T]` instance provides `IsIntuitionistic.efq A : (⊥ → A) ∈ T`, so every
formula appearing in the `⊥`-subderivation is a subformula of a **theory axiom** — discharging the
subformula property with no atomic restriction and no permutation conversions. This is the
option-C "crutch."

**A literal option-B split removes this crutch.** In `MinDerivation + Explosion`, IPL-ND is
`MinDerivation` with `efq` **adjoined as a genuine structural constructor**, *not* backed by a
theory axiom `⊥ → A ∈ T`. The subformula property under that adjoined `efq` then genuinely
requires the task-398 decided strategy: **atomic restriction** (restrict primitive explosion to
atomic conclusions `⊥ → p`, deriving general `efq` admissibly) **plus permutation conversions**
(commuting `efq` past eliminations). That is the HIGH-effort re-cut the trigger gate is designed to
avoid unless a consumer justifies it.

### 4.3 Re-trigger signal to watch for

Pursue option B only if one of these concrete consumers materializes:
- A **minimal-logic (Johansson) normalization or λμ-style** result whose statement must quantify
  over derivations that *provably cannot* use `efq` (e.g. a proof-term extraction that must reject
  abort), where the `IsBotRuleFree` *predicate* over the shared inductive is insufficient (e.g.
  because the consumer needs to `cases`/recurse on a type with no `efq` constructor).
- A **λ-calculus with an intended abort-free operational semantics** that is *defined as the image
  of* the Propositional Curry–Howard `Term`, needing the term type itself to lack the abort
  constructor.
- A downstream module that needs the **stronger** subformula property for the *primitive*-explosion
  IPL-ND (i.e. where `efq` is not axiom-grounded), forcing the atomic-restriction proof anyway.

Until then, the `IsBotRuleFree` predicate + `MinimalDerivation` abbreviation (both green on main)
already give every *stated* need the shared-inductive design has, at zero cost.

---

## 5. Hypothetical split map (objective 4) — if the trigger ever fires

### 5.1 The two-inductive shape

```lean
-- Base: genuinely ⊥-rule-free, 10 constructors, NO efq, NO IsIntuitionistic anywhere.
inductive Theory.MinDerivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  | ax | ass | andI | andE1 | andE2 | orI1 | orI2 | orE | impI | impE

-- Explosion extension. Two candidate encodings:
-- (E1) closed relation extension: an inductive wrapping MinDerivation plus one efq rule.
inductive Theory.IplDerivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  | ofMin  {Γ A} : Theory.MinDerivation Γ A → IplDerivation Γ A
  | efq    {Γ A} : IplDerivation Γ ⊥ → IplDerivation Γ A
  -- (recursive occurrences must be IplDerivation, so ofMin cannot be the only lift; the ten
  --  structural rules must be *re-listed* on IplDerivation, or MinDerivation made a parameterized
  --  functor — see §5.3 cost note)
```

The naive `ofMin`-wrapping (E1) does **not** by itself give a usable IPL inductive, because the
structural rules must operate on `IplDerivation` sub-derivations (e.g. `impI` of an `efq`). Two
honest realizations:

- **E1′ (re-list all 11 rules on the extension)**: `IplDerivation` re-declares the 10 structural
  rules *plus* `efq`, and `MinDerivation` embeds via a total `ofMin` map. This is the literal
  "structural metatheory proved once on the base, IPL recovered by adjoining `efq`" — but "proved
  once" is only true if each base metatheorem is **transported** across the embedding, which needs
  a generic lifting lemma per structural operation.
- **E2 (parameterize the base by an extension relation)**: make the base a functor
  `GenDerivation (Ext : Ctx → Proposition → Prop)` with a `ext`-leaf constructor, instantiate
  `Ext := ⊥·` (empty) for MPL and `Ext := efq-schema` for IPL. This most directly answers Waring's
  "fragment specified so manipulations lift by construction" ask (407 report 02, §6.3), and is the
  more principled destination, but is strictly more machinery than E1′.

### 5.2 Structural metatheory to re-prove/transport on the base

Each of these currently lives on the single `Theory.Derivation` and threads `efq`; under the split
each must be (a) proved on `MinDerivation` (trivial — no `efq` case) and (b) transported to
`IplDerivation`:

- `weak` / `weakTheory` / `weakCtx` (Basic.lean:286-328)
- `cut` / `cut_away` (Basic.lean:334-358)
- `subs` (Basic.lean:363-389), `substAtom` (Basic.lean:392-408)
- equivalence congruences `equiv`, `mapEquiv{Conclusion,Hypothesis}`, `Equiv.{imp,and,or}_congr`
  (Basic.lean:438-575)
- Normalization: `height`, `isNormal`, `isIntroRoot`, `isStronglyNormal`,
  `isStronglyNormal_implies_isNormal`, `formulas`, `SubformulaProperty`
  (Normalization/Basic.lean) — the `efq` arm of each moves to the extension
- Reduction: `reduceRoot`, `subsOne`, `normalizeAux`, `normalize` (Normalization/Reduction.lean)
- Termination driver `snForm`, `exists_stronglyNormal_form` (Normalization/Termination.lean, 1103
  lines) — the largest single transport surface
- **Subformula property** (`subformula_property{,_of_isStronglyNormal}`) — the `efq` case must be
  re-derived **without** the `IsIntuitionistic.efq` axiom crutch (§4.2): the genuine hard point,
  via atomic restriction + permutation conversions.

### 5.3 Curry–Howard re-cut

`Theory.Term` (CurryHoward/Defs.lean) mirrors the split: a base `MinTerm` (10 ctors, no abort) and
an abort extension, with `curryHowardEquiv` re-cut as either `MinDerivation ≃ MinTerm` +
`IplDerivation ≃ Term`, threading `efq`/abort through `curryHowardForward`/`Backward` and both
round-trips (Isomorphism.lean:54-126). CH reduction (Reduction.lean, 274 lines) similarly re-cut.

### 5.4 Recovering IPL-ND by adjoining `efq`

`IplDerivation = MinDerivation + efq`; the equivalence to the *existing* gated `Theory.Derivation`
at `IsIntuitionistic T` strength should be proved to avoid stranding all downstream IPL/CPL
metalogic (`Int*`, `Classical*`, soundness/completeness, Lindenbaum, tableau). This equivalence is
the migration seam: without it, option B forks the whole IPL stack.

---

## 6. Base+extension patterns (objective 5) — reuse-first findings

**CSLib already contains the relevant precedent (prefer reuse over inventing):**

- **`ExtDerivationTree` / `ExtAxiom`** in `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/
  ExtDerivation.lean` (inductive at `185`, axiom mirror at `46`) is the in-repo template for a
  base-mirroring extended derivation with `embedAxiom`/`embedDerivation` lifts (`209`, `26`). This
  is the closest existing model for "define an extended inductive that mirrors the base and lift
  base derivations into it" — exactly the E1′ shape. Any option-B implementation should mirror this
  file's structure (mirror ctors + `embed*` transport lemmas) rather than invent a new idiom.
- **`SeqProof.IsBotRuleFree`** (`SequentCalculus/LJ/Basic.lean:238`) and the **`LM` gated-`botL`**
  design (`SequentCalculus/LM/Basic.lean:20-54`) show the *predicate-over-shared-inductive* idiom
  (the option-C analogue on the sequent side) — evidence the library's settled preference is the
  predicate, not the physical split.
- **`InferenceSystem`** (`Cslib/Foundations/Logic/InferenceSystem.lean`, imported by Basic.lean:9)
  is the foundational abstraction both a `MinDerivation` and an `IplDerivation` would instantiate;
  reuse it rather than a bespoke derivability wrapper.

**Mathlib**: the generic pattern for "base relation + extension leaf" is the standard
`Relation.ReflTransGen` / inductive-with-embedding approach; there is no Mathlib lemma that
manufactures the transport lemmas for a bespoke intrinsically-typed derivation split — those are
hand-written per operation (as `ExtDerivation.lean` does). No rate-limited search was needed to
establish this: the decisive facts are local (the `ExtDerivation` precedent and the negative
consumer sweep). If option B is ever scheduled, a targeted `lean_leansearch`/`loogle` pass for
functor-over-relation lifting would be the first implementation step, not a research blocker.

---

## 7. Design-debt / policy notes

- **Zero-debt**: any option-B proof that cannot be closed (notably subformula-property-under-`efq`
  without the axiom crutch) must be marked `[BLOCKED]`, never `sorry`, never a vacuous
  `def _ := True` (per `.claude/rules/lean4.md`). The atomic-restriction + permutation-conversion
  strategy is the *only* sanctioned route; do not substitute a `simp`/`aesop` bypass.
- **No revert of 398/407 assets**: option B must be *additive* (new `MinDerivation`/extension
  alongside the shared inductive, with an equivalence bridge), not a replacement that strands the
  green IPL/CPL metalogic. 407 report 01 §"Do not revert or weaken" is binding.
- **Community/process**: the with-vs-without-`⊥` design is a live Zulip topic; any PR prose must be
  human-authored (Zulip AI policy, 407 report 02 §7).

---

## 8. Durable anchors (provenance)

- Landed decision: `specs/407_mpl_base_structure_first_redesign/decisions.md` (Q1 = option C).
- Design dispute + comparison table: `specs/407_.../reports/02_mpl-base-with-vs-without-bot.md`.
- Codebase ground-truth map: `specs/407_.../reports/01_mpl-base-structure-first.md` (§5 ND
  reconciliation, §"option B only" hard-point note).
- Live sources: `Cslib/Logics/Propositional/NaturalDeduction/{Basic, Normalization/*}.lean`,
  `CurryHoward/{Defs, Isomorphism, Reduction}.lean`, and the base+extension precedent
  `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtDerivation.lean`.

---

## Adversarial Self-Verification

Independent H4 verification pass (divergence audit focus). Every load-bearing claim was
re-checked against the live codebase; the two headline modules were rebuilt
(`lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization.SubformulaProperty
Cslib.Logics.Propositional.CurryHoward.Isomorphism` — completed successfully, 672 jobs).

| Claim | Source/Counterexample | Verdict |
|---|---|---|
| `Theory.Derivation` is a single 11-ctor inductive with gated `efq` (Basic.lean:146-183) | `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:146` (inductive), `:182-183` (`efq {…} [IsIntuitionistic T]`) | VERIFIED |
| `IsBotRuleFree` predicate, `efq ⇒ False` (Basic.lean:223, 235) | `NaturalDeduction/Basic.lean:223` (def), `:235` (`efq _ => False`) | VERIFIED |
| `MinimalDerivation := MPL.Derivation` abbrev (Basic.lean:242-243) | `NaturalDeduction/Basic.lean:242` | VERIFIED |
| Consumer sweep negative: `MinimalDerivation`/`IsBotRuleFree` referenced only inside `NaturalDeduction/Basic.lean` | `grep -rn` over `Cslib/`: hits only in `NaturalDeduction/Basic.lean` (defs + docstrings) plus the *distinct* `SeqProof.IsBotRuleFree` in `SequentCalculus/LJ/Basic.lean:237` (parallel predicate, not a consumer) | VERIFIED |
| Trigger condition NOT met (no physically-⊥-free consumer) | Follows from the verified negative sweep + verified STLC independence (below); no counterexample found in `Cslib/` | VERIFIED |
| Subformula property under `efq` is currently closed via `IsIntuitionistic.efq` axiom-grounding (SubformulaProperty.lean:282-294) | `Normalization/SubformulaProperty.lean:282` (`@efq` case), `:291-292` (`IsIntuitionistic.efq A` + `imp_left`); main theorem `:305-309`; `_of_isStronglyNormal` `:52` | VERIFIED |
| Removing the gate re-opens the hard point (extension `efq` has no `⊥ → A ∈ T` axiom to ground on) | Logical consequence of the verified proof shape at `SubformulaProperty.lean:291` — the closing witness is literally the theory-membership axiom; a structural `efq` with no membership has no such witness | VERIFIED (reasoning, not a file fact) |
| STLC is standalone: no bottom, no abort, not built on `Theory.Term` | `Cslib/Languages/LambdaCalculus/LocallyNameless/Stlc/Basic.lean:39` (`Ty`), `:51` (`Typing`); `grep` for `Bot`/`abort`/`Theory.Term`/`Propositional` over `Cslib/Languages/LambdaCalculus/`: zero hits | VERIFIED |
| Task 407 landed option C | `specs/archive/407_mpl_base_structure_first_redesign/decisions.md:5` (Q1 = "Option C … option B stays deferred to task 409. No proof churn.") — note directory is now under `specs/archive/` | VERIFIED |
| "No task 398 spec directory exists (`specs/398_*` absent)" | `specs/archive/398_efq_nd_rule_ipl_base_keep_mpl/` EXISTS with `plans/`, `reports/`, `summaries/` | REFUTED (as stated) |
| Structural metatheory anchors: `weak` 286 (`efq` 301-303), `cut` 334, `subs` 363-389 (`efq` 389), `substAtom` 392-408 (`efq` 408), `instIsIntuitionisticExtension` used at 302 | `NaturalDeduction/Basic.lean:286,301-302,334,363,389,392,408` — all exact | VERIFIED |
| `IsIntuitionistic` class with `efq A : (⊥ → A) ∈ T` | `Cslib/Logics/Propositional/Defs.lean:166-167` | VERIFIED |
| Normalization anchors: `height` 49, `isNormal` 72, `isStronglyNormal` 136, `formulas` 237, `SubformulaProperty` 252 | `Normalization/Basic.lean:49,72,136,237,252` — all exact | VERIFIED |
| CH mirror anchors: `Theory.Term` inductive "57-104", `efq` ctor "100-104"; Isomorphism `curryHowardForward` "54" (`efq` "67"), `curryHowardBackward` "74" | Actual: `CurryHoward/Defs.lean:56` (inductive), `:102` (`efq`); `Isomorphism.lean:53` (`forward`), `:66` (`efq`), `:73` (`backward`) — off-by-one/two throughout; structure and content correct | VERIFIED (line anchors ±1-2) |
| Reduction anchors: `subsOne` "45", `reduceRoot` "66" | Actual `Normalization/Reduction.lean:43,64` — off-by-two; content correct | VERIFIED (line anchors ±2) |
| `Termination.lean` "1103 lines"; `CurryHoward/Reduction.lean` "274 lines"; `snForm`/`exists_stronglyNormal_form` present | Actual `wc -l`: Termination 1113, CH Reduction 274; `snForm` at `Termination.lean:1071` | VERIFIED (1113 not 1103; immaterial) |
| `ExtDerivationTree`/`ExtAxiom` precedent with `embedAxiom`/`embedDerivation` lifts, at "185/46/209/26" | File and structure confirmed, but actual anchors: `ExtAxiom` `:44`, `ExtDerivationTree` `:176`, `embedAxiom` def `:201`, `embedDerivation` def `:280` (`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtDerivation.lean`) | VERIFIED (substance) / line anchors imprecise |
| `SeqProof.IsBotRuleFree` "238-249"; LM gated-`botL` design + `not_isIntuitionistic_mpl` "20-54" | Actual: LJ def at `SequentCalculus/LJ/Basic.lean:237` (body through 248); `not_isIntuitionistic_mpl` at `LM/Basic.lean:54` | VERIFIED (±1) |
| FromHilbert anchors: `botE` 97, `botEDeriv` 195, `efq` subst at 240 | Actual `FromHilbert.lean:98,196,241` — off-by-one; content correct | VERIFIED (±1) |
| `InferenceSystem` imported by Basic.lean:9 | `NaturalDeduction/Basic.lean:9`: `public import Cslib.Foundations.Logic.InferenceSystem` | VERIFIED |
| Option-C assets "green on main" | `lake build` of `SubformulaProperty` + `CurryHoward.Isomorphism` completed successfully (672 jobs) on current main | VERIFIED |

**Correction note (the one REFUTED row)**: §2's claim "No task 398 spec directory exists
(`specs/398_*` absent)" is wrong as stated — the directory was *archived*, not lost:
`specs/archive/398_efq_nd_rule_ipl_base_keep_mpl/` exists with full `plans/`, `reports/`, and
`summaries/`. Consequence: the decided-strategy provenance for the subformula-property hard point
(atomic restriction + permutation conversions) is available *first-hand* in the 398 archive, not
only second-hand via 407 report 01 as §2 suggests. This *strengthens* the report's §5.2 guidance
(the strategy source is richer than claimed); it does not weaken any conclusion. Similarly, task
407's directory now lives at `specs/archive/407_mpl_base_structure_first_redesign/` (task 407 is
archived/completed) — all §8 provenance paths beginning `specs/407_...` should be read as
`specs/archive/407_...`. The predecessor assumptions themselves (option C landed; gated `efq`;
`IsBotRuleFree` + `MinimalDerivation` naming devices present) all hold on current main, verified
above against the live code.

**Uncertain claims (none blocking)**: the §5 hypothetical split map (E1′ vs E2 costs, transport
surface) is design projection, not codebase fact — it is internally consistent with the verified
inventory but cannot be "verified" until implemented; confidence: high for the transport-surface
list (it enumerates exactly the verified `efq`-threading sites), medium for the E1′-vs-E2
trade-off framing.

**Analysis-paralysis verdict: PASS.** The report does not defer decisions. It delivers a
concrete, falsifiable recommendation (do NOT pursue option B; keep 409 deferred or `[BLOCKED]`
with reason "trigger condition unmet"), an explicit re-trigger signal list (§4.3), and — for the
contingency — a named implementation route (E1′ mirroring `ExtDerivation.lean`, or E2) with the
exact transport surface enumerated. The "do nothing now" conclusion is the *substantive answer*
to this task's own gate ("only pursue if a concrete downstream consumer needs a physically ⊥-free
derivation object"), backed by a verified-negative consumer sweep, not an evasion of work.
**Overall H4 verdict: report VERIFIED with one corrected provenance claim; recommendation
stands.**
