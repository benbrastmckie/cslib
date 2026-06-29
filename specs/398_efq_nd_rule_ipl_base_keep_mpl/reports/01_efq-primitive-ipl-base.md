# Research Report: Promote efq to a primitive ND `Derivation` constructor (IPL-as-base, MPL retained)

Task: 398 `efq_nd_rule_ipl_base_keep_mpl`
Source design: CSLib Zulip thread *Propositional Logic* (Waring closing message 606970606) + task synthesis.
Scope: research only. No source edits made. (Zulip AI policy: any prose posted to Zulip must be human-authored; this is an internal planner artifact.)

---

## 1. Executive summary

- `⊥` is **already** a primitive constructor of `Proposition` (`Cslib/Logics/Propositional/Defs.lean`). The change requested is to add an **elimination constructor `efq` to the natural-deduction `Theory.Derivation` inductive only** (`NaturalDeduction/Basic.lean:117-146`). Nothing about `Proposition` changes.
- Consequently the **blast radius is exactly "code that pattern-matches `Theory.Derivation`"**. Everything that operates on `Proposition` (DecidableEq, `Proposition.subst`, the `FromPropositional` embeddings, Modal/Temporal/Bimodal) is **insulated** and only needs to keep building.
- The **MPL metatheory is entirely Hilbert-substrate based** (`DerivationTree`/`Deriv`/`Derivable MinPropAxiom`, Kripke + algebra). It does **not** mention `Theory.Derivation`. So `MinSoundness`, `MinLindenbaum`, `MinStrongCompleteness`, `MPL.hilbert_alg_complete`, and the conservativity chains are *structurally untouched* by adding the constructor — the only ND↔Hilbert seam they cross is `hilbert_iff_nd_min` (used once, in Glivenko).
- **Recommended design: a gated constructor** `efq … [IsIntuitionistic T] : Derivation Γ ⊥ → Derivation Γ A`. This makes efq a genuine derivation node "interpreting" `⊥`, available exactly at IPL/CPL strength, **while automatically preserving `hilbert_iff_nd_min`** because `AxiomTheory MinPropAxiom` admits no `IsIntuitionistic` instance (so efq is unconstructible there, and ND-minimal is unchanged). An unconditional constructor (true "IPL base") is analyzed in §5 and **not recommended for this task** because it breaks `hilbert_iff_nd_ctx_min`/`hilbert_iff_nd_min` and would force a new efq-free sub-system.
- **Two large consumers carry essentially all the cost and the only real risk**: `NaturalDeduction/Normalization/*` (Prawitz normalization, ~90 match sites; efq is the classic subformula-property / strong-normalization problem case) and `CurryHoward/*` (the `Theory.Term` inductive mirrors the constructors 1-1). These must get genuine efq cases with **zero sorries**; they are the make-or-break of the task and should be sized as their own phases.

---

## 2. Current shape of `Theory.Derivation` and where `efq` goes

File: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:117-146`.

```lean
inductive Theory.Derivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  | ax    {Γ} {A} (_ : A ∈ T)                : Derivation Γ A
  | ass   {Γ} {A} (_ : A ∈ Γ)                : Derivation Γ A
  | andI  {A B} (G) : Derivation G A → Derivation G B → Derivation G (A ∧ B)
  | andE1 {A B} (G) : Derivation G (A ∧ B) → Derivation G A
  | andE2 {A B} (G) : Derivation G (A ∧ B) → Derivation G B
  | orI1  {A B} (G) : Derivation G A → Derivation G (A ∨ B)
  | orI2  {A B} (G) : Derivation G B → Derivation G (A ∨ B)
  | orE   {A B C} (G) : Derivation G (A ∨ B) → Derivation (insert A G) C
                        → Derivation (insert B G) C → Derivation G C
  | impI  {A B} (Γ) : Derivation (insert A Γ) B → Derivation Γ (A → B)
  | impE  {Γ} {A B} : Derivation Γ (A → B) → Derivation Γ A → Derivation Γ B
```

10 constructors today (Basic.lean docstring `:45-48` and `:113-116` both say "10 constructors / ex falso is a derived rule" — both prose blocks must be updated, task item (4)).

**New constructor (recommended, gated):**

```lean
  /-- Ex falso quodlibet (bottom elimination). Available exactly when the theory is
  intuitionistic (`IPL ⊆ T`), i.e. at IPL/CPL strength; absent in minimal logic. -/
  | efq {Γ : Ctx Atom} {A : Proposition Atom} [IsIntuitionistic T] :
      Derivation Γ ⊥ → Derivation Γ A
```

Notes:
- `IsIntuitionistic T` is `Prop`-valued (single field `efq (A) : (⊥ → A) ∈ T`, a Pi into a Prop; `Defs.lean:166-167`). So the constructor's instance field is **proof-irrelevant** — no derivation-equality headaches.
- `IsIntuitionistic T ↔ IPL ⊆ T` (`Defs.lean:171`), with instances `instIsIntuitionisticIPL` (`:182`), `instIsClassicalCPL`/extension lemmas `instIsIntuitionisticExtention` (`:190`), `instIsIntuitionisticIntuitionisticCompletion` (`:205`). These supply the field at IPL/CPL/union strengths automatically.

---

## 3. How `botE` works today and what changes

File: `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean:86-89`:

```lean
def Theory.Derivation.botE [IsIntuitionistic T] (d : T.Derivation Γ ⊥) : T.Derivation Γ A :=
  Derivation.impE (Derivation.ax (IsIntuitionistic.efq A)) d
```

It is a derived rule: it routes through the theory axiom `⊥ → A` (`IsIntuitionistic.efq A : (⊥ → A) ∈ T`) and `impE`. The `DerivableIn.botE` wrapper is at `:165-168`.

**Change:** keep the name `botE` (callers depend on it — see below) but redefine it as a one-liner over the new constructor:

```lean
def Theory.Derivation.botE [IsIntuitionistic T] (d : T.Derivation Γ ⊥) : T.Derivation Γ A :=
  Derivation.efq d
```

`DerivableIn.botE` is unchanged. Both keep the `[IsIntuitionistic T]` binder, so **every existing `botE` call site is source-compatible** with no edits. Existing `botE` callers (must stay green): `AxiomAdmissibility.lean:247` (Peirce proof) and `FromHilbert.lean:97,195-203` (`botE`/`botEDeriv`, a *different* `botE` over the Hilbert-derived ND layer — see §6, low risk).

Equivalently the design preserves the desired "efq-as-rule = efq-as-axiom coincide" property: `efq d` and `impE (ax (IsIntuitionistic.efq A)) d` are interderivable by definition of `botE`.

---

## 4. Recommended design — gated constructor: complete proof-obligation map

The new constructor forces a new arm in **every total recursion / exhaustive match over `Theory.Derivation`**. Below, each obligation with the exact site and the discharging sketch. All are zero-sorry.

### 4.1 `Basic.lean` — three recursions (authoring file)

1. `Theory.Derivation.weak` (`:207-221`): changes `T → T'` with `hTheory : T ⊆ T'`.
   ```lean
   | @efq _ _ _ A _ _ d => @efq _ _ _ A Δ (instIsIntuitionisticExtention hTheory) (d.weak hTheory hCtx)
   ```
   The target instance `IsIntuitionistic T'` comes from `instIsIntuitionisticExtention hTheory` (`Defs.lean:190`). (The matched constructor exposes the source `[IsIntuitionistic T]` field.)

2. `Theory.Derivation.subs` (`:281-306`): `T` fixed, context `Γ → Γ\Γ' ∪ Δ`. Instance unchanged:
   ```lean
   | @efq _ _ _ A _ _ E => efq (E.subs Ds)
   ```

3. `Theory.Derivation.substAtom` (`:309-324`): `T → T.subst f`, atom type changes. `IsIntuitionistic` is **not** preserved across an arbitrary atom substitution (target would need `⊥ → A'` for *all* `A'`, not just images). **Discharge via the derived route instead of the constructor:**
   ```lean
   | @efq _ _ _ A _ _ d =>
       -- (⊥ → A) ∈ T  ⟹  (⊥ → A) >>= f = ⊥ → (A >>= f) ∈ T.subst f
       have hmem : (⊥ → (A >>= f)) ∈ (T.subst f) :=
         Set.mem_image_of_mem (· >>= f) (IsIntuitionistic.efq A)  -- ⊥ >>= f = ⊥ by `Proposition.subst`
       Derivation.impE (Derivation.ax hmem) (d.substAtom f)       -- d.substAtom f : … ⊢ (⊥ >>= f) = ⊥
   ```
   Key rewrite facts: `Proposition.subst` sends `bot ↦ .bot` and `imp ↦ .imp` (`Defs.lean:131-132`), so `(⊥ → A).subst f = ⊥ → (A.subst f)` definitionally, and `⊥ >>= f = ⊥`. This is the one place the constructor cannot be reused; the fallback keeps `substAtom` total and computable.

   `DerivableIn.substAtom` (`:326-330`) is a wrapper and needs no change.

### 4.2 `Equivalence.lean` — the ND↔Hilbert bridge (task item 2)

File: `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`.

- `hilbertToND` (`:287-301`): **no change**. Hilbert `DerivationTree` has no efq constructor; the IPL explosion axiom enters via `.ax` and maps to ND `.ax` (Equivalence.lean docstring `:59-61` already says this). The match is over the *Hilbert* tree, not over `Theory.Derivation`.
- `ndToHilbert` (`:339-387`, `noncomputable`, `[MinimalAxioms Axioms]`): **add an `efq` arm**. The matched constructor exposes `[IsIntuitionistic (AxiomTheory Axioms)]`, giving `(⊥ → A) ∈ AxiomTheory Axioms`, i.e. `Axioms (⊥ → A)` via `mem_axiomTheory` (`:90`). Then:
  ```lean
  | @Theory.Derivation.efq _ _ _ A G inst d => by
      have ih := ndToHilbert d                                  -- DerivationTree … ⊥
      have hax : Axioms (⊥ → A) := mem_axiomTheory.mp (IsIntuitionistic.efq A)
      exact .modus_ponens _ _ _ (.ax _ _ hax) ih               -- mirror of impE case (:376-379)
  ```
  This realises "efq-as-rule ↔ efq-as-axiom coincide".
- Downstream theorems `hilbert_iff_nd*` (`:407-500`) need **no proof edits**: they are corollaries of the two translators. They remain provably intact.
- **MPL still corresponds** automatically: `hilbert_iff_nd_ctx_min`/`hilbert_iff_nd_min` (`:450-453`, `:478-482`) are about `AxiomTheory MinPropAxiom`. There is no `IsIntuitionistic (AxiomTheory MinPropAxiom)` (that would require `MinPropAxiom (⊥ → A)`, which is false), so the `efq` constructor is **unconstructible** there ⇒ the set of ND-derivable minimal sequents is unchanged ⇒ the equivalence is preserved with no edit. This is the crux that satisfies task item (2)'s "MPL (no efq rule) still corresponds".

### 4.3 `AxiomAdmissibility.lean`

- `:247` uses `Derivation.botE` inside `propositionalAxiom_admissible` (Peirce). Since `botE` keeps its signature, this **compiles unchanged**. Optionally re-target to `Derivation.efq` for directness; not required.
- The file already cases on the *Hilbert* axiom enumerations (`| efq A => …` at `:217`, `:233` are `IntPropAxiom.efq`/`PropositionalAxiom.efq` cases, NOT the new constructor) — unaffected.

### 4.4 `CurryHoward/*` — term-language mirror (HIGH effort)

File: `Cslib/Logics/Propositional/CurryHoward/Defs.lean:56-95`. `Theory.Term` is documented as "10 constructors of `Term` correspond **one-to-one** with the 10 constructors of `Theory.Derivation`" (`:54-55`). Adding `efq` to `Derivation` breaks the isomorphism unless `Term` gains a mirror constructor, e.g. `Term.efq [IsIntuitionistic T] : Term Γ ⊥ → Term Γ A` (an "abort"/`absurd` combinator — standard for the λ-calculus-with-`⊥` Curry-Howard reading).
- `CurryHoward/Isomorphism.lean` (2 exhaustive matches): both directions of the iso need the `efq`/`Term.efq` arm.
- `CurryHoward/Reduction.lean` (1 match): an efq reduction/preservation arm (efq has no introduction to reduce against, so this is typically a congruence/no-redex case, but it must be written).

### 4.5 `Normalization/*` — Prawitz normalization (HIGH effort, ONLY real risk)

Files and match counts (sites that must gain an `efq` arm):
- `Normalization/Basic.lean` (~28 matches): `height` (`:50-59`), `isNormal` (`:72-93`), `isStronglyNormal` (`:134-159`), plus the structural lemmas (`:168-…`).
  - `height`: `| efq _ d => 1 + d.height` (trivial).
  - `isNormal`/`isStronglyNormal`: efq is an elimination whose major premise has type `⊥`, which has **no introduction rule**, so an efq node is **never a proper β-redex**. The natural choice is `| efq _ d => d.isNormal` (and likewise strong-normal), with commuting-conversion cases added where efq is the major premise of another elimination (mirrors the existing `orE`-as-major-premise commuting cases at `:76-93`, `:138-159`).
- `Normalization/Reduction.lean` (6 matches): reduction relation must cover efq (congruence; plus any efq-permutation conversions chosen).
- `Normalization/Termination.lean` (**52 matches** — the dominant site): the strong-normalization measure/recursion must account for efq. Mechanically these are the height/measure-decrease arms; volume is large but each arm mirrors an existing elimination arm.
- `Normalization/SubformulaProperty.lean` (7 matches): `subformula_property_of_isStronglyNormal` (`:52`) and `subformula_property` (`:292`).
  - **Metatheoretic caveat (flag to planner):** classical Prawitz normalization only yields the subformula property when efq is **restricted to atomic conclusions** (`⊥`-elimination introducing an atom), otherwise an efq node can introduce a non-subformula. CSLib's statement is "strongly normal ⇒ subformula property". The planner must decide one of: (a) include efq as a node that the strong-normal predicate forbids at non-atomic conclusion (Prawitz restriction), keeping the theorem literally true; (b) weaken/relativise the subformula-property statement to a `⊥`-free or efq-restricted fragment; or (c) add the standard efq-permutation conversions that push efq to atomic form. **This is the single place where a naive port could require a sorry — it must NOT be deferred (zero-debt). Recommend sizing this as its own phase with a decided strategy before coding.**

### 4.6 What does NOT change (important scoping)

- `Proposition` inductive, `DecidableEq (Proposition Atom)`, `Proposition.subst`/`Monad` instance (`Defs.lean:126-139`): unchanged — `⊥` is already a `Proposition` constructor.
- `FromPropositional` embeddings (`Modal/FromPropositional.lean:60`, `Temporal/FromPropositional.lean:59`, `Bimodal/Embedding/PropositionalEmbedding.lean`): these map at the `Proposition` level (`| .bot => .bot`) and never recurse over `Theory.Derivation`. Unchanged.
- `equiv`/`Equiv` congruence lemmas (`Basic.lean:166-490`): built from `impI/impE/andI/…`, no exhaustive match over the inductive, so no new arm — they keep compiling.

---

## 5. Alternative design (unconditional efq) — analyzed and NOT recommended for task 398

Constructor `| efq {Γ A} : Derivation Γ ⊥ → Derivation Γ A` (no instance), making the ND **base genuinely IPL** and minimal logic the efq-free fragment. This is the literal "IPL-as-base" reading and is attractive long-term (it is the cleanest "interpret `⊥`"). However, for **this** task it conflicts with item (2):

- `AxiomTheory MinPropAxiom` ND would gain unconditional explosion, so `hilbert_iff_nd_ctx_min`/`hilbert_iff_nd_min` (`Equivalence.lean:450,478`) become **false** (ND-minimal ≅ Hilbert-IPL, not Hilbert-MPL). The single consumer is `HilbertConservativeGlivenko.lean:200` (`axiomTheory_min_iff_mpl ∘ hilbert_iff_nd_min.symm`); it would break.
- Recovering "MPL still corresponds" then requires introducing a **new efq-free derivation predicate** (an `IsBotFree`-style sub-relation on `Theory.Derivation`) and re-proving the minimal correspondence against it — a substantially larger change than the task's "keep hilbert_iff_nd* provably intact".
- `substAtom` becomes trivially total under this design (no instance to preserve), which is its only advantage over §4.

**Recommendation:** implement the **gated constructor (§4)** now (satisfies items 1-5 with the least disruption and zero broken theorems), and record the unconditional/IPL-base + `IsBotFree` fragment as the postponed "general fragment design" (item 5, Waring). The gated design still "interprets `⊥`" (efq is now a real derivation node, not axiom indirection) and is exactly "available at IPL/CPL strength".

---

## 6. MPL retention — files that must NOT be deleted or weakened (task constraint)

All are Hilbert-substrate / algebra based and are **structurally independent** of the ND constructor (verified: none import or match `Theory.Derivation`):

- `Metalogic/MinSoundness.lean`, `Metalogic/MinLindenbaum.lean`, `Metalogic/MinStrongCompleteness.lean` (over `DerivationTree/Deriv/Derivable MinPropAxiom` + Kripke).
- `Semantics/Algebra/*` MPL/IPL chain: `MplConservativeChain.lean`, `MplPointedConservative.lean`, `ConservativeChain.lean`, `Conservative.lean` (`IsBotFree` predicate at `:39`), `ImpConservative.lean`, `OrImpConservative.lean`, `ConjImpConservative.lean`, `ConjImpBotConservative.lean`, plus `HilbertAlgCompleteness.lean` providing `MPL.hilbert_alg_complete` / `IPL.hilbert_alg_complete` / `CPL.hilbert_alg_complete` (`Semantics/Algebra.lean:52`). The `bot_val`/Johansson-algebra parametric semantics live here.
- `Glivenko.lean` and `HilbertConservativeGlivenko.lean` (the only file touching `hilbert_iff_nd_min`; preserved automatically under §4).

These need at most a **rebuild check**, not edits. Minimal logic remains a retained layer beneath IPL.

---

## 7. Downstream consumers (Modal / Temporal / Bimodal)

Verified: **no file under `Cslib/Logics/Modal/`, `Cslib/Logics/Temporal/`, `Cslib/Logics/Bimodal/` references `Theory.Derivation`** (the PL ND inductive). They depend on `Proposition` and the `FromPropositional` embeddings (Proposition-level, `| .bot => .bot`), and define their own derivation systems. So they are insulated; they only need a full `lake build` to confirm nothing transitively breaks. The same holds for `SequentCalculus/LJ` and `/LK` completeness, which consume `hilbert_iff_nd_ctx_int`/`_cl` (`LJ/Completeness.lean:263`, `LK/Completeness.lean:351`) — both IPL/CPL strengths, preserved by §4.2.

---

## 8. Candidate lemmas / API for reuse

- `Theory.IsIntuitionistic` + `IsIntuitionistic.efq` (`Defs.lean:166-167`); `isIntuitionisticIff` (`:171`); `instIsIntuitionisticExtention` (`:190`, for `weak`); `instIsIntuitionisticIPL`/`instIsIntuitionisticIntuitionisticCompletion` (`:182`,`:205`).
- `mem_axiomTheory` (`Equivalence.lean:90`) — converts the efq instance to `Axioms (⊥ → A)` in `ndToHilbert`.
- `Set.mem_image_of_mem`, `Proposition.subst` clauses (`Defs.lean:131-132`) — for the `substAtom` efq fallback; `⊥ >>= f = ⊥`.
- `DerivationTree.modus_ponens` / `DerivationTree.ax` (Hilbert side, used like the existing `impE` arm `Equivalence.lean:376-379`).
- Existing `orE` commuting-conversion arms in `Normalization/Basic.lean:76-93,138-159` are the **template** for efq-as-major-premise commuting cases.
- No Mathlib lemma is needed for the core change; all machinery is local. (Search confirmed `IsBotFree`/`IsOrBotFree` already exist in `Semantics/Algebra/Conservative.lean:39` and `ConjImp…`, available if the postponed fragment work is ever started.)

---

## 9. Risk register and zero-debt notes

| Area | Risk | Mitigation |
|---|---|---|
| `Normalization/SubformulaProperty.lean` | efq violates subformula property for non-atomic conclusions (classic Prawitz problem) | Decide strategy (Prawitz atomic restriction / relativise statement / efq-permutation) **before** coding; own phase; no sorry permitted |
| `Normalization/Termination.lean` (52 sites) | volume; SN measure must cover efq | each arm mirrors an existing elimination arm; mechanical but large — own phase |
| `CurryHoward/Isomorphism.lean` | 1-1 iso breaks without a `Term.efq` mirror | add `Term.efq` + iso arms; standard "abort" combinator |
| `substAtom` | `IsIntuitionistic` not preserved across atom subst | use derived `impE (ax …)` fallback (§4.1.3) — no instance needed |
| Whole inductive | adding a constructor = many `match` arms | ordered phases: Basic → DerivedRules → Equivalence/AxiomAdmissibility → CurryHoward → Normalization |

Zero-debt: the only genuinely hard obligation is the subformula property under efq. It must be resolved structurally (one of the three strategies), **not** by `sorry`, vacuous defs, or new axioms. If a green proof cannot be reached, that phase should be marked `[BLOCKED]` for user decision rather than deferred.

---

## 10. Actionable proof direction (phasing for the planner)

1. **Phase 1 — Core constructor.** Add gated `efq` to `Theory.Derivation` (Basic.lean:146). Add `efq` arms to `weak`, `subs`, `substAtom` (§4.1). Redefine `botE := efq` in DerivedRules.lean. Build `…NaturalDeduction.Basic` + `…DerivedRules`.
2. **Phase 2 — Bridge.** Add `efq` arm to `ndToHilbert`; confirm `hilbert_iff_nd*` and `AxiomAdmissibility` still build. Build `…Equivalence`, `…AxiomAdmissibility`. (Verifies item 2 incl. MPL correspondence and Glivenko.)
3. **Phase 3 — Curry-Howard.** Add `Term.efq`, fix `Isomorphism`/`Reduction`. Build `…CurryHoward.*`.
4. **Phase 4 — Normalization (split if needed).** Decide subformula-property strategy first; add efq arms to `Basic` (height/normal/strongly-normal), `Reduction`, `Termination`, `SubformulaProperty`. Build `…Normalization.*`.
5. **Phase 5 — Update prose + full verify.** Update both `Basic.lean` doc blocks (`:45-73` design trade-off + `:113-116`) to record IPL-as-base with MPL retained as a fragment-layer (human-authored, per Zulip AI policy). Confirm MPL files (§6) and downstream Modal/Temporal/Bimodal (§7) build. Run full CI: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake lint`, `lake test`, `lake shake …`.

Depends on task 397 (green main) for clean verification baseline.
