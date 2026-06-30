# Task 299 — Modal Truth Lemma Architecture (imp case)

**Status:** researched
**Date:** 2026-06-30
**Session:** sess_1782844490_b74534
**Scope:** How to architect `modalTruthLemma` so the imp case is provable for Łukasiewicz‑encoded
and/or/neg, replacing the unprovable `hintikka_imp_pos`/`hintikka_imp_neg` bridge lemmas.

---

## 0. TL;DR Recommendation

**Adopt option (b): inline the connective case analysis into `modalTruthLemma`'s imp case, and
convert `modalTruthLemma` from structural `induction φ` to STRONG induction on `sizeOf φ`.**
Delete `hintikka_imp_pos` and `hintikka_imp_neg` (they are unprovable as stated). **Keep
`hintikka_box_pos` and `hintikka_box_neg` unchanged** (□ is primitive; they are correct).

Option (a) — restating the imp bridges to return the and/or/neg decomposition — **cannot fix the
problem on its own**, because the bridges return only *membership* facts (e.g. `T(a')@w ∈ b`),
and converting those to *semantic* facts (`Satisfies w a'`) requires `modalTruthLemma`'s own
induction hypothesis **at the deep subformulas `a'`, `b'`** — which simply do not exist under
structural induction. So the truth lemma must switch to strong induction regardless; once it
does, inlining is the natural shape and the bridge factoring buys nothing.

---

## 1. Root cause, confirmed against source

The modal `Proposition` (`Cslib/Logics/Modal/Basic.lean`) is purely Łukasiewicz — only four
constructors: `atom`, `bot`, `imp`, `box` (`Satisfies` at `Basic.lean:145-149`):

```
Satisfies m w (.atom p)   = m.v w p
Satisfies m w .bot        = False
Satisfies m w (.imp a c)  = (Satisfies m w a → Satisfies m w c)
Satisfies m w (.box a)    = ∀ w', m.r w w' → Satisfies m w' a
```

and/or/neg are encoded (`Cslib/Logics/Modal/Tableau/Defs.lean:110-173`):

| connective | encoding | classifier |
|---|---|---|
| `¬a`        | `imp a bot`                         | `modalNegOf?`  (`imp a .bot`) |
| `a ∨ c`     | `imp (imp a bot) c`                 | `modalOrOf?`   (`imp (imp a .bot) b`) |
| `a ∧ b`     | `imp (imp a (imp b bot)) bot`       | `modalAndOf?`  (`imp (imp a (imp b .bot)) .bot`) |
| proper `a→c`| `imp a c`, c≠bot, a not `imp _ bot` | `modalImpOf?` |

`modalApplyOne` (`Rules.lean:68-77`) runs `tryAllPropRules` **first**. `tryAllPropRules`
(`Foundations/Logic/Tableau/PropositionalRules.lean:147-155`) tries the 8 rules in fixed order
`[andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg]` and returns the **first**
applicable. For a positive imp only `andPos > orPos > impPos > negPos` can fire; for a negative
imp only `andNeg > orNeg > impNeg > negNeg`.

`applyPropRule` (`PropositionalRules.lean:94-143`) rule outputs (label `l = w`):

| rule (T/F + shape) | classifier hit | RuleResult |
|---|---|---|
| `andPos` T(a∧b)  | `modalAndOf? = some (a',b')` | `.linear [.pos a' w, .pos b' w]` |
| `orPos`  T(a∨c)  | `modalOrOf?  = some (a'',c)` | `.branching [[.pos a'' w], [.pos c w]]` |
| `impPos` T(a→c)  | `modalImpOf? = some (a,c)`   | `.branching [[.neg a w], [.pos c w]]` |
| `negPos` T(¬a)   | `modalNegOf? = some a`       | `.linear [.neg a w]` |
| `andNeg` F(a∧b)  | `modalAndOf? = some (a',b')` | `.branching [[.neg a' w], [.neg b' w]]` |
| `orNeg`  F(a∨c)  | `modalOrOf?  = some (a'',c)` | `.linear [.neg a'' w, .neg c w]` |
| `impNeg` F(a→c)  | `modalImpOf? = some (a,c)`   | `.linear [.pos a w, .neg c w]` |
| `negNeg` F(¬a)   | `modalNegOf? = some a`       | `.linear [.pos a w]` |

**Why the current bridge is false.** `hintikka_imp_pos` (`Completeness.lean:204-210`) claims, for
*every* `T(imp a c)@w ∈ b`, that `F(a)@w ∈ b ∨ T(c)@w ∈ b`. But for a conjunction encoding
`T((a'→(b'→⊥))→⊥)` (here `a = a'→(b'→⊥)`, `c = ⊥`), `andPos` fires first and the Hintikka
condition only gives `T(a')@w ∈ b ∧ T(b')@w ∈ b` — **neither `F(a)@w` nor `T(c)=T(⊥)`**. The
lemma is genuinely unprovable for conjunction (and analogously disjunction). `modalTruthLemma`
(`Completeness.lean:370-383`) calls it uniformly for every `imp`, so the factoring is unsound.

---

## 2. Why structural induction is insufficient (the real blocker)

Take T(conjunction) `φ = imp a c`, `a = imp a' (imp b' bot)`, `c = bot`. Semantically
`Satisfies w φ = (Satisfies w a → False) = ¬Satisfies w a`, and `¬Satisfies w a ↔ (Satisfies w a'
∧ Satisfies w b')`. The branch (via `andPos`) carries `T(a')@w` and `T(b')@w`. To finish we must
turn those into `Satisfies w a'` and `Satisfies w b'` — i.e. we need the truth‑lemma IH **at `a'`
and `b'`**.

`induction φ with | imp a c ih_a ih_c` provides IH only at the **immediate children** `a` and `c`.
`a'`, `b'` are grandchildren (subterms of `a`); there is no `ih_{a'}`. The disjunction encoding
`imp (imp a'' bot) c` (rule `orPos`/`orNeg`) likewise needs IH at `a''`, a subterm of the
antecedent, again not an immediate child.

Conclusion: **conjunction and disjunction require IH on strictly‑smaller, non‑immediate
subformulas**, so structural induction over `Proposition` cannot prove the imp case. Strong
induction on `sizeOf φ` supplies IH for every strictly‑smaller subformula (`a' , b', a'', c, a`),
which is exactly what is needed. (Negation and proper‑imp need only IH at `a` and `c`, and box
needs only IH at `ψ`; all are also covered by strong induction.)

This is precisely why the propositional `classicalTruthLemma` does **not** mirror onto the modal
proof directly — see §3.

---

## 3. The propositional `classicalTruthLemma` imp‑case skeleton, and why it differs

`Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`. The propositional
`Proposition` has **native `and`/`or` constructors**, so `classicalTruthLemma`'s `imp` case
**never sees conjunction/disjunction encodings** — those are separate `| and ...` / `| or ...`
induction cases (lines 350+) that get IH on their conjuncts directly. Its `imp a c` case only
handles **genuine implication and negation** (the `c = bot` sub‑case = `¬a`).

Skeleton of the `imp a c` case (lines 169–349):

- **T side** (lines 171–271): extract `sf` with `sign=.pos`, `formula=.imp a c`
  (`List.any_eq_true.mp`, `eq_of_beq`); get `hout := hrule sf hsfmem`; then
  **`cases hbot : c`**:
  - `c = bot` (line 181): `classicalApplyOne sf = .linear [F(a)]` (proved by
    `obtain ⟨s,fm,l⟩ := sf; subst …; rfl`); pull `F(a)@w ∈ b` via
    `hout _ List.mem_cons_self`; build the `b.any` witness; close with `ih_a.2`.
  - `c = atom/imp/and/or/box` (lines 194–271): `.branching [[F(a)],[T(c)]]`; `obtain ⟨br,
    hbr_mem, hbr⟩ := hout`; `rcases hbr_mem` into the two branches; each closes with `ih_a.2`
    (branch `[F(a)]`) or `ih_c.1` (branch `[T(c)]`).
- **F side** (lines 272–349): symmetric, `cases hbot : c`; `c=bot` → `.linear [T(a)]` (negNeg),
  else `.linear [T(a), F(c)]` (impNeg); closes with `ih_a.1` and `ih_c.2`.

**Key takeaways for the modal port.** (1) The *mechanics* transfer verbatim: rewrite
`modalApplyOne sf` to the concrete `RuleResult` via `obtain ⟨s,fm,l⟩ := sf; subst …; rfl`, then
pull members with `hout _ <mem-proof>` and convert to `b.any …` witnesses. (2) The *case
structure* does **not** transfer: the propositional proof `cases c` and uses immediate‑child IH
because and/or are native. The modal proof must instead **`cases` on the encoded shape**
(conjunction / disjunction / negation / proper‑imp) and use **deep** IH (`a'`, `b'`, `a''`) for
the conjunction/disjunction branches — hence strong induction.

---

## 4. Recommendation (option b), with exact signatures

### 4.1 Keep / delete

- **Keep unchanged:** `hintikka_box_pos` (`Completeness.lean:140-184`), `hintikka_box_neg`
  (`:189-195`). □ is primitive; both are correct and verified.
- **Delete:** `hintikka_imp_pos` (`:204-274`) and `hintikka_imp_neg` (`:284-324`). Unprovable as
  stated. Their *mechanics* (extract `hcond := hrule …`, unfold `modalApplyOne`, pull members)
  migrate into the new imp case.

### 4.2 Strong‑induction scaffold (most robust form)

Use the size‑bounded helper idiom (avoids `termination_by` friction in tactic mode). `sizeOf φ ≥
1` always, and every strict subformula has strictly smaller `sizeOf`.

```lean
private lemma modalTruthLemma_aux
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc) :
    ∀ (n : ℕ) (φ : Proposition Atom), sizeOf φ ≤ n → ∀ (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModel b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModel b acc) w φ) := by
  intro n
  induction n with
  | zero =>
    -- sizeOf φ ≥ 1 > 0, so `sizeOf φ ≤ 0` is impossible: `omega` / `simp` on the bound.
    intro φ hsz w; exact absurd hsz (by cases φ <;> simp <;> omega)
  | succ n ih =>
    intro φ hsz w
    -- `ih : ∀ ψ, sizeOf ψ ≤ n → ∀ w', (pos→Sat) ∧ (neg→¬Sat)`
    -- For any strict subformula ψ of φ: `sizeOf ψ ≤ n` follows from `hsz : sizeOf φ ≤ n+1`
    -- (because `sizeOf ψ < sizeOf φ`), so `ih ψ (by …; omega) w'` is the usable IH.
    cases φ with
    | atom p => …            -- as today (Completeness.lean:347-362), w bound unused
    | bot   => …             -- as today (:363-369)
    | box ψ => …             -- as today (:384-391) but use `ih ψ (by simp_all; omega)`
    | imp a c => …           -- NEW: §4.3
```

Then the public lemma keeps its current statement:

```lean
lemma modalTruthLemma
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModel b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModel b acc) w φ) :=
  fun φ w => modalTruthLemma_aux b acc hH (sizeOf φ) φ le_rfl w
```

`modalOpenBranch_countermodel` (`:398-404`) is unchanged.

For the `sizeOf ψ ≤ n` obligations: from `hsz : sizeOf (imp a c) ≤ n+1` and
`sizeOf (imp a c) = 1 + sizeOf a + sizeOf c` (and likewise nested), every needed subformula
bound discharges with `simp only [Proposition.imp.sizeOf_spec, …] at hsz ⊢; omega` (or `decreasing_by`
if the `termination_by` form is used instead — see §4.5).

### 4.3 The imp case, leaf by leaf

Let `M := extractModel b acc`. Open with the membership extraction shared by both polarities
(mirrors `Completeness.lean:211-215`):

```lean
| imp a c =>
  refine ⟨?_, ?_⟩
  -- POSITIVE: T(imp a c)@w ∈ b → Satisfies M w (imp a c)
  · intro hmem
    have hcond := (hH.2.1) ⟨.pos, .imp a c, w⟩ hmem      -- Hintikka rule fact (2nd conjunct)
    simp only [modalApplyOne, tryAllPropRules, applyPropRule,
      modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?,
      RuleResult.isApplicable, Option.getD_some] at hcond    -- NOTE: include Option.getD_some
    -- dispatch in modalApplyOne priority order: andPos > orPos > impPos > negPos
    …
```

**Dispatch (positive), in `modalApplyOne` priority order.** Determine the branch by
`cases c` then `cases a` (or `split_ifs` on the classifier `if`s left by the `simp` above), to
separate the four shapes:

1. **Conjunction** `a = imp a' (imp b' bot)`, `c = bot` → `andPos` `.linear [T(a')@w, T(b')@w]`.
   - `hcond` ⇒ `T(a')@w ∈ b` and `T(b')@w ∈ b` (`hcond _ List.mem_cons_self`, then for `b'`
     `hcond _ (by simp)` / `List.mem_cons_self` after `List.mem_cons`).
   - `Satisfies M w a' := (ih a' _ w).1 (any‑witness from T(a')@w)`; likewise `Satisfies M w b'`.
   - Goal `Satisfies M w (imp (imp a' (imp b' bot)) bot)`. `simp only [Satisfies]` reduces it to
     `(Satisfies M w a' → Satisfies M w b' → False) → False`; close with
     `fun h => h ‹Satisfies M w a'› ‹Satisfies M w b'›`.
   - **IH used:** `ih a' (bound) w` and `ih b' (bound) w` — both strictly smaller than φ.
2. **Disjunction** `a = imp a'' bot`, `c` arbitrary → `orPos` `.branching [[T(a'')@w],[T(c)@w]]`.
   - `obtain ⟨br, hbr_mem, hbr⟩ := hcond`; `rcases hbr_mem` (two branches).
   - Branch `[T(a'')]`: `Satisfies M w a'' := (ih a'' _ w).1 …`; goal
     `Satisfies M w (imp (imp a'' bot) c) = (Satisfies M w a'' → False) → Satisfies M w c`;
     close `fun hna => absurd ‹Sat a''› hna` (the `Sat a'' → False` premise contradicts `Sat a''`).
   - Branch `[T(c)]`: `Satisfies M w c := (ih c _ w).1 …`; goal closes `fun _ => ‹Sat c›`.
   - **IH used:** `ih a'' (bound) w` (deep) and `ih c (bound) w` (child).
3. **Proper imp** `c ≠ bot`, `a ≠ imp _ bot` → `impPos` `.branching [[F(a)@w],[T(c)@w]]`.
   - `obtain ⟨br, hbr_mem, hbr⟩`; `rcases`:
   - `[F(a)]`: `¬Satisfies M w a := (ih a _ w).2 …`; goal `Satisfies M w (imp a c) = Sat a → Sat c`;
     close `fun ha => absurd ha ‹¬Sat a›`.
   - `[T(c)]`: `Satisfies M w c := (ih c _ w).1 …`; close `fun _ => ‹Sat c›`.
   - **IH used:** `ih a` and `ih c` (immediate children — structural would have sufficed here).
4. **Negation** `c = bot`, `a` not of and‑shape and not `imp _ bot` → `negPos` `.linear [F(a)@w]`.
   - `F(a)@w ∈ b` via `hcond _ List.mem_cons_self`; `¬Satisfies M w a := (ih a _ w).2 …`.
   - Goal `Satisfies M w (imp a bot) = (Sat a → False)`; close `fun ha => absurd ha ‹¬Sat a›`.
   - **IH used:** `ih a` (child). Note `T(◇φ)=T(¬□¬φ)` lands here with `a = □(φ→⊥)`.

**Dispatch (negative): F(imp a c)@w ∈ b → ¬Satisfies M w (imp a c).** Same shape split,
priority `andNeg > orNeg > impNeg > negNeg`:

1. **Conjunction** → `andNeg` `.branching [[F(a')@w],[F(b')@w]]`. `rcases` the branch:
   `[F(a')]` gives `¬Sat a'` via `(ih a' _ w).2`; `[F(b')]` gives `¬Sat b'`. Goal
   `¬Satisfies M w (a'∧b')`; `simp only [Satisfies]` turns it into
   `¬((Sat a' → Sat b' → False) → False)`; from `¬Sat a'` (resp. `¬Sat b'`) build the inner
   function and discharge. **IH:** `ih a'`, `ih b'` (deep).
2. **Disjunction** → `orNeg` `.linear [F(a'')@w, F(c)@w]`. Both members via `hcond _ (by simp)`.
   `¬Sat a''`, `¬Sat c`; goal `¬Satisfies M w (a''∨c)`; close by feeding `Sat a''` to `¬Sat a''`
   etc. **IH:** `ih a''` (deep), `ih c` (child).
3. **Proper imp** → `impNeg` `.linear [T(a)@w, F(c)@w]`. `Sat a := (ih a).1 …`,
   `¬Sat c := (ih c).2 …`; goal `¬(Sat a → Sat c)`; close `fun hf => absurd (hf ‹Sat a›) ‹¬Sat c›`.
   **IH:** `ih a`, `ih c` (children).
4. **Negation** → `negNeg` `.linear [T(a)@w]`. `Sat a := (ih a).1 …`; goal
   `¬Satisfies M w (imp a bot) = ¬(Sat a → False)`; close `fun hf => hf ‹Sat a›`. **IH:** `ih a`.

`any`‑witness construction in every leaf is the existing idiom, e.g.
`List.any_eq_true.mpr ⟨_, hmem_fact, by simp [SignedFormula.pos]⟩`, exactly as in the
propositional proof (lines 189–191, 205–206) and the box bridges.

### 4.4 The two verified mechanical sub‑fixes

These were verified during prior dispatches and must be carried into the corrected leaves
(they apply to the **proper‑imp** and **negation** membership extractions — the genuine
proper‑implication sub‑cases — and anywhere the `hcond`/branch member proofs are built):

1. **Missing `Option.getD_some`.** Per‑case `simp only [...]` sets that unfold `modalApplyOne`
   leave `hcond` stuck as a `match (if …).fst with …` because `…|>.getD .notApplicable` is not
   reduced. **Add `Option.getD_some`** to the simp set (as shown in §4.3's opening `simp only`).
   Verified via `lean_multi_attempt` previously: `simp only [Option.getD_some, reduceIte,
   List.mem_singleton] at hcond` reduces `hcond` to `∀ sf', sf' = SignedFormula.neg X w → sf' ∈ b`,
   after which `exact Or.inl (hcond _ rfl)` closed the old bot.atom leaf. In the new architecture
   the analogue closes the **negation** leaf's `F(a)@w ∈ b` extraction.
2. **`List.mem_cons_self _ _` → `List.mem_cons_self`.** In this toolchain `List.mem_cons_self`
   takes **no** explicit args (it *is* the term `a ∈ a :: l`). Every occurrence of
   `List.mem_cons_self _ _` in the migrated member‑extraction proofs (the linear `andPos`/`negPos`
   first element, and the branch‑head pulls) must be written `List.mem_cons_self`. (The old broken
   lemmas had this at `Completeness.lean:225,229,236-237,240,252-253,265-266,273-274,288,304,306,
   312,319,323`; carry the corrected form into the new leaves.)

### 4.5 Alternative scaffold (if the implementer prefers `termination_by`)

Equation form is also fine:

```lean
lemma modalTruthLemma (b …) (acc …) (hH …) : ∀ (φ : Proposition Atom) (w : WorldIndex),
    (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModel b acc) w φ) ∧
    (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModel b acc) w φ)
  | φ, w => by
      cases φ with … -- recursive self-calls: `modalTruthLemma a' w`, `modalTruthLemma b' w`, …
  termination_by φ _ => sizeOf φ
  decreasing_by all_goals (simp_wf; omega)
```

The size‑bounded `…_aux` form (§4.2) is recommended as more robust in tactic mode; both give the
same deep IH.

---

## 5. Verification checklist for the implementer

- [ ] Box bridges untouched; `lean_verify` still green on them.
- [ ] `hintikka_imp_pos`/`hintikka_imp_neg` removed; no remaining references
      (`grep -n hintikka_imp Completeness.lean`).
- [ ] All four positive + four negative leaves close with deep IH for conj/disj, child IH for
      imp/neg, mirroring §4.3.
- [ ] `Option.getD_some` present in the imp unfolding simp set; no `List.mem_cons_self _ _`.
- [ ] `lake build Cslib.Logics.Modal.Tableau.Completeness` green.
- [ ] Zero sorry / zero axiom: `grep -rn 'sorry\|admit\|^axiom' Cslib/Logics/Modal/Tableau/`
      empty; `lean_verify Cslib.Logic.Modal.Tableau.modalTruthLemma`.
- [ ] Then resume Phase 6 (LoopInduction `modalExpandBranches_hintikka`) and Phase 7
      (barrel/`mk_all`) per the handoff.

---

## 6. Reuse check (CSLib reuse‑first)

- The classifiers `modalAndOf?/modalOrOf?/modalImpOf?/modalNegOf?` already exist with `@[simp]`
  lemmas (`Defs.lean:110-201`) — reuse them in the `simp` unfolding rather than re‑deriving.
- The rule‑output mechanics already exist in `classicalTruthLemma` and in the working
  `hintikka_box_pos` — reuse the `obtain ⟨s,fm,l⟩ := sf; subst …; rfl` + `List.any_eq_true.mpr`
  idiom; no new helpers needed.
- No new typeclass / abstraction is warranted; this is a proof‑restructuring task only.

## Files referenced

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/Completeness.lean` (target)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/Rules.lean` (`modalApplyOne`)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Tableau/Defs.lean` (classifiers)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Basic.lean` (`Satisfies`)
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Tableau/PropositionalRules.lean`
  (`applyPropRule`, `tryAllPropRules`)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`
  (`classicalTruthLemma` reference skeleton)
