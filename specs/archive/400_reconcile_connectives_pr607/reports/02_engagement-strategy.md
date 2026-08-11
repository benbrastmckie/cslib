# PR #607 Engagement Strategy — verified against the live PR

**Task**: 400 — reconcile_connectives_pr607
**Date**: 2026-06-29
**Status**: researched
**Type**: cslib (research)
**Supersedes/deepens**: `reports/01_pr607-engagement.md`
**Primary sources**: live `gh pr view/diff 607` (leanprover/cslib), the PR's inline review
comments, repo `NOTATION.md` / `ORGANISATION.md`, and the local Lean files on this fork
(`Cslib/Foundations/Logic/Connectives.lean`, `Cslib/Logics/Propositional/Defs.lean`).

---

## 0. Executive recommendation (read first)

**Engage #607 with targeted, additive, incremental suggestions — do NOT propose a competing
full architecture.** The à-la-carte "one class per operator" direction in #607 is the more
idiomatic, Mathlib-style choice and is the very direction this fork's own `Connectives.lean`
docstring says it is "following." A wholesale alternative (porting the fork's bundled
`PropositionalConnectives` / `ModalConnectives` / `BimodalConnectives` hierarchy into the PR)
would step on an open, maintainer-reviewed PR and contradict Waring's Zulip guidance to "help
that get merged."

Two corrections to report 01 drive the new strategy:

1. **Do not ask fmontesi to add a bespoke `HasBot` class.** Mathlib already ships `Bot` and
   `Top` (the `⊥` / `⊤` notation classes, `Mathlib/Order/Notation.lean`), and CSLib's
   Propositional `Defs.lean` *already uses them* (`instance : Bot (Proposition Atom)`,
   `instance : Top ...`). Reuse-first + the maintainer's "`Has` prefix is a Lean-3-ism" comment
   both point to **reusing Mathlib `Bot`/`Top`**, not minting `HasBot`.
2. **A "primitive `HasNot`" does not actually block faithful registration of a bot-primitive
   `Proposition`.** `HasNot.not : α → α` can be instantiated with the *derived* negation
   `Proposition.neg = (· → ⊥)`. #607's own diff already does exactly this for the upstream
   Propositional type (`instance [Bot Atom] : HasNot (Proposition Atom) := {not := Proposition.neg}`).
   The real gap is narrower than report 01 stated: there is no `⊥`/`⊤` *notation/typeclass* in
   #607's connective set, and no bridge making `¬φ` reduce to `φ → ⊥` for `grind`/`simp`.

So the falsum point is *real but mis-prescribed* in report 01. The right ask is "reuse
Mathlib `Bot`/`Top` and add a derived-`¬` bridge," not "add a `HasBot` class."

---

## 1. Verified summary of PR #607's current design (from the live diff)

PR **#607** `fmontesi/connectives` — "feat(Logic): logical operators", **OPEN**, **+296 / −33,
15 files**. Latest substantive push `c2ec2962` (2026-06-16); latest review 2026-06-19. Outstanding
**CHANGES_REQUESTED** from `chenson2018` (not dismissed).

### 1.1 The connective typeclasses (each in its own file under `Cslib/Foundations/Logic/Operators/`, namespace `Cslib.Logic`)

| Class | Method | Notation declaration | Prec / assoc | File |
|---|---|---|---|---|
| `HasAnd` | `and (a b : α) : α` | `scoped infixr:36 " ∧ "` | 36, right | `Operators/And.lean` |
| `HasOr` | `or (a b : α) : α` | `scoped infixr:30 " ∨ "` | 30, right | `Operators/Or.lean` |
| `HasImpl` | `impl (a b : α) : α` | `scoped infixr:25 " → "` | 25, right | `Operators/Impl.lean` |
| `HasNot` | `not (a : α) : α` | `scoped notation:max "¬" p:40` | arg at 40 | `Operators/Not.lean` |
| `HasIff` | `iff (a b : α) : α` | `scoped infixr:20 " ↔ "` | 20, right | `Operators/Iff.lean` |
| `HasBox` | `box (a : α) : α` | `scoped prefix:40 "□"` | 40 | `Operators/Box.lean` |
| `HasDiamond` | `diamond (a : α) : α` | `scoped prefix:40 "◇"` | 40 | `Operators/Diamond.lean` |
| `HasTensor` | `tensor (a b : α) : α` | `scoped infixr:35 " ⊗ "` | 35, right | `Operators/Tensor.lean` |

All eight are bare `class … (α : Type*)` mixins with a single method, `@[expose] public section`,
`import Cslib.Init`. **There is no `HasBot`, no `HasTop`, no bundle class.** `HasNot` is a
standalone primitive (no link to `⊥`).

### 1.2 How #607 wires the concrete logics

- **Modal (`Logics/Modal/Basic.lean`, +58/−18)**: replaces the old direct `scoped infix`
  notation on `Proposition.*` with `instance : HasNot/HasAnd/HasDiamond …` plus
  `@[scoped grind =] lemma Proposition.{not,and,or,impl,iff,box,diamond}_def : φ.op … = (op-notation) := rfl`.
  Diamond is registered as a primitive instance; box/or/impl/iff remain *defined* and are
  registered with bridge `_def` lemmas. Several `Satisfies.*_iff_*` characterisation lemmas were
  reworked to go through the typeclass notation; `Satisfies.dual` proof was loosened to
  `constructor; · grind; · grind` (note: a commented-out `grind only` block remains — minor debt
  to flag).
- **Propositional (`Logics/Propositional/Defs.lean`, +16/−6)**: registers
  `HasAnd/HasOr/HasImpl` and, crucially, `instance [Bot Atom] : HasNot (Proposition Atom) :=
  {not := Proposition.neg}` with a bridge `@[grind =] lemma not_eq [Bot Atom] (A) : (A → ⊥) = ¬ A
  := rfl`. **NB**: this hunk is written against the *upstream* propositional `Proposition`
  (which has `Proposition.impl`, `Proposition.neg`, `instTopProposition [Inhabited Atom]`,
  `[Bot Atom]`), **not** this fork's five-primitive `Cslib.Logic.PL.Proposition`. See §4.
- **Linear (`Logics/LinearLogic/CLL/Basic.lean`, +1/−1)** and `LogicalEquivalence.lean`: the only
  real change is renaming `LogicalEquivalence …` → `HasLogicalEquivalence …` and adding a
  `HasLogicalEquivalence` abbrev / parametrised `≡[S]` equivalence. This is *not* a connective
  refactor; report 01's "refactors … Linear" framing overstates it.

### 1.3 Live review state (new since report 01 — major omissions there)

- **`benbrastmckie` already posted a coordination comment on 2026-06-17**
  (`issuecomment-4735753144`): flags overlap with #648's `Connectives.lean`
  (`HasBot/HasImp/HasAnd/HasOr`), raises `HasImpl/impl` vs `HasImp/imp` (argues for `imp`,
  citing FormalizedFormalLogic + the `impI/impE` rule-prefix convention), and makes the
  primitive-`bot` / primitive-`box` case (substitution invariance, free-algebra property,
  necessitation as a pure rule). **The "deliverable: a human-authored review" is therefore
  already partly done; the next review should build on this comment, not restate it.**
- **`eric-wieser` (Mathlib maintainer) reviewed 2026-06-19** with three pointed comments:
  - *"merge all these operators into a single `LogicOperators` file"* (one docstring for the
    conventions).
  - *cleaner instance syntax*: `instance : HasAnd (Proposition Atom) where and := .and`.
  - **"Note that the `Has` prefix is largely a Lean-3-ism."** ← highest-leverage signal: it
    questions the entire `HasX` naming scheme (Mathlib 4 uses `Add`, `Mul`, `Bot`, `Top`, … with
    no `Has`). This applies equally to **this fork's** `HasBot/HasImp/…`.
- **`chenson2018` (CHANGES_REQUESTED, still open)**: (a) suggested a single file for the
  notation classes; (b) **the `_def` `simp`/`grind =` lemmas look "backwards"** — they should
  rewrite *into* the notation (normal form = the notation), à la `List.append_eq`, `Nat.add_eq`.
  Waring (`thomaskwaring`) agreed in principle but couldn't get `grind` to see through the
  notation without rewriting back. **This normal-form-direction question is unresolved and
  directly governs how `Proposition` instances + bridge lemmas should be written.**
- **`ctchou`**: proposed a 3-file split — `Modal` (box+diamond), `Tensor` alone, `Propositional`
  for the rest; asked whether parameterised box/diamond are needed for HML.

### 1.4 Where report 01 was inaccurate or out of date

| Report 01 claim | Live-PR finding |
|---|---|
| "#607 should add a `HasBot` (and `HasTop`) class" | Mis-prescribed. Reuse Mathlib `Bot`/`Top`; #607 + maintainer are moving *away* from `Has*`. |
| "free-standing `HasNot` … cannot represent IPL/MPL faithfully" | Overstated. `HasNot.not` can be the derived `neg`; #607's diff already registers `HasNot := {not := Proposition.neg}`. |
| "refactors … Linear" | Linear change is a 1-line `LogicalEquivalence`→`HasLogicalEquivalence` rename, not connectives. |
| Did not mention reviews | Misses `benbrastmckie`'s 2026-06-17 comment, eric-wieser's "`Has` is a Lean-3-ism", chenson's open CHANGES_REQUESTED and the `_def` direction debate, ctchou's file-split. |
| Precedence table (#607: → 25, ∨ 30, ∧ 36, ¬ 40) | **Accurate** — confirmed verbatim from the Operators files. |
| Class/operator list (8 `HasX`) | **Accurate**. |

---

## 2. The falsum / derived-negation question, grounded in the real diff

**Facts.** #607's connective set = `{∧, ∨, →, ¬, ↔, □, ◇, ⊗}`. No `⊥`/`⊤`. `HasNot` is a
free primitive. This fork's `Cslib.Logic.PL.Proposition` has a **primitive `bot` constructor**
with `neg`/`top`/`iff` derived (`Proposition.neg = (· → ⊥)`, `Proposition.top = ⊥ → ⊥`); it
already does `instance : Bot (Proposition Atom)` / `instance : Top (Proposition Atom)` using
**Mathlib's `Bot`/`Top`** classes (confirmed: `Bot` lives in `Mathlib/Order/Notation.lean`).

**What actually breaks, and what does not.**
- Registering `HasAnd`/`HasOr`/`HasImpl` for `PL.Proposition`: trivial (all primitive). ✔
- Registering negation: `instance : HasNot (PL.Proposition Atom) := {not := Proposition.neg}` is
  *faithful* — it makes `¬φ` mean exactly `φ → ⊥`. The "primitive `HasNot`" is not an obstacle;
  a typeclass method is just a function and may be filled by a derived term. ✔
- The genuine gaps are notation + automation, not representability:
  1. **No `⊥`/`⊤` notation in #607's set.** A formula type with primitive falsum needs `⊥`
     notation. The idiomatic answer is **Mathlib `Bot`/`Top`** (reuse-first), which #607 should
     *acknowledge and use*, rather than minting `HasBot`/`HasTop`.
  2. **No polymorphic bridge `¬φ ⟺ (φ → ⊥)`.** For `grind`/`simp` to discharge MPL/IPL goals
     that mix `¬` and `→ ⊥`, there must be a `@[grind/simp]` lemma orienting the two — exactly
     `not_eq : (A → ⊥) = ¬A` that #607 already introduces for the upstream type. This needs to be
     stated for the bot-primitive `PL.Proposition` too (and oriented per chenson's normal-form
     point, §3.3).

**Minimal additions to #607 for faithful bot-primitive registration** (all additive, low
friction for fmontesi):
- (a) Keep `HasNot` as-is; **do not** add `HasBot`. Use Mathlib `Bot`/`Top` for `⊥`/`⊤`.
- (b) Provide (or let downstream provide) `instance : HasNot (PL.Proposition Atom)` via the
  derived `neg`, plus the `(A → ⊥) = ¬A` bridge `@[grind =]` lemma.
- Optionally (c): a `HasNot` *default instance* `instance [HasImpl α] [Bot α] : HasNot α :=
  ⟨(· → ⊥)⟩` so any imp+bot type gets `¬` for free. This is the cleanest expression of "neg is
  definitionally `· → ⊥`," but it risks diamond-inheritance/notation-ambiguity surprises and
  should be *floated as a question*, not pushed.

This both honours report 01's instinct (there is a falsum gap) and corrects its remedy
(Mathlib `Bot`/`Top`, not a new `HasBot`).

---

## 3. Other alignment points, re-checked against the live PR + NOTATION.md

### 3.1 Naming (`HasImpl/impl` vs `HasImp/imp`, and the `Has` prefix itself)
- #607 uses `HasImpl`/`impl`; this fork's `Connectives.lean` uses `HasImp`/`imp`. `benbrastmckie`
  already argued for `imp` on the PR.
- **New, larger issue**: eric-wieser says the `Has` prefix is a Lean-3-ism. Mathlib-4 style would
  be operator classes *without* `Has` (cf. `Bot`, `Top`, `Add`, `Mul`). This is the single
  highest-leverage decision: a rename touches every class, every instance, and both #607 and the
  fork. **Resolve the naming scheme before more code accretes.** Pose it as: keep `HasX` (matches
  CSLib's existing `HasFresh`/`HasContext`/`HasSubstitution` infrastructure) vs drop to bare
  `And`/`Or`/`Impl`/… (Mathlib-idiomatic, but collides with `core`/Mathlib `And`/`Or`/`Iff` —
  a concrete reason CSLib may *keep* `Has`). The `And`/`Or`/`Iff` name-collision argument is a
  strong, defensible reason to retain `Has`; surface it to eric-wieser rather than silently
  complying.

### 3.2 Notation precedence / associativity
- **NOTATION.md says nothing about logical connectives** — it only covers operational-semantics
  arrows and equivalences. So there is *no* documented CSLib precedence standard for
  `∧ ∨ → ¬ ↔ ⊥ ⊤`; #607 is effectively *setting* it. This is freedom, not a conflict with a
  standard — report 01's "must be reconciled or formulas parse differently across logics" is
  right about cross-logic consistency but there is no external authority to defer to.
- Divergences (this fork's `PL.Defs` vs #607): `∨` 35-`infix` vs 30-`infixr`; `→` 30-`infix` vs
  25-`infixr`; `∧` both 36 but `infix` (non-assoc) vs `infixr`. #607's `infixr` is *more usable*
  (`a ∧ b ∧ c` parses); the fork's non-assoc `infix` is the weaker choice. **Recommend adopting
  #607's `infixr` + its precedence ladder (→ 25 < ∨ 30 < ⊗ 35 < ∧ 36, ¬/□/◇ 40, ↔ 20) as the
  library-wide convention and recording it in NOTATION.md** (a genuinely useful PR by-product).
  One caution to raise: `→` at 25 *shadows* Lean's core `→` (Prop implication) inside the scoped
  namespace; confirm fmontesi has checked this does not break mixed object-/meta-level formulas.

### 3.3 Bridge `_def` lemma direction (chenson's open point)
- The `Proposition.*_def : φ.op … = (notation)` lemmas are tagged `@[scoped grind =]`. chenson
  argues the `simp`/`grind` normal form should be **the notation** (collapse `φ.and ψ ⤳ φ ∧ ψ`),
  matching `List.append_eq`. Waring couldn't make `grind` see through the notation without
  rewriting back. **This is unresolved and is the main reason the modal proofs got more verbose
  (`grind [=_ Proposition.or_def, Proposition.or]`).** Any `Proposition`-instance registration we
  contribute must pick the agreed orientation; recommend aligning with chenson (notation = normal
  form) and verifying `grind` closes `Satisfies.*_iff_*` with that orientation before posting.

### 3.4 Bundling (à-la-carte vs `PropositionalConnectives`)
- #607 is purely à-la-carte (no bundle). This fork's `Connectives.lean` adds bundles
  (`PropositionalConnectives extends HasBot, HasImp` with **defaulted** `neg`/`top` fields;
  `ModalConnectives`, `Future/LTL/TemporalConnectives`, `BimodalConnectives`, plus a
  priority-100 `BimodalConnectives → ModalConnectives` bridge). The fork's *entire* downstream
  development (tasks 229/254/260/266/340; Modal/Temporal/Bimodal/LTL) depends on these bundles for
  polymorphic axiom/theorem statements.
- **Strategy**: the bundles are *additive* over #607's atomic classes — `PropositionalConnectives`
  can `extend` `Bot`, `HasImpl`, `HasAnd`, `HasOr` once #607 lands. **Do not push the bundle
  hierarchy into #607.** Offer it as a follow-up PR layered on the merged atomic classes, and use
  the review only to (i) confirm the atomic classes are named/shaped so bundles can extend them,
  and (ii) note that defaulted `neg`/`top` fields want `Bot`+`HasImpl` present.

### 3.5 Notation ownership
- Both #607 and the fork route `∧ ∨ → ¬` through `scoped` notation; #607 moves ownership to the
  typeclass (so concrete types stop declaring their own and instead register instances + `_def`
  bridges). **#607's path should win** (single source of notation, no duplicate-`scoped` clashes).
  Once it lands, the fork drops its per-type `scoped infix` declarations and keeps only instances
  + bridge lemmas. Already partially true: `PL.Defs` currently declares its own notation *and*
  registers `HasAnd`/`HasOr` — that duplication is exactly what #607 removes.

### 3.6 File organisation (eric-wieser + ctchou + chenson all raised it)
- Three reviewers independently want fewer files. Recommend a single
  `Foundations/Logic/Operators.lean` (or `LogicOperators.lean`) with one conventions docstring,
  or at most ctchou's 3-way split. This is low-stakes but *consensus already exists* — easy
  goodwill to endorse it. Note ORGANISATION.md (this fork) currently lists `Axioms.lean` as the
  home of connective typeclasses and `Connectives.lean` as "derived abbreviations" — the fork's
  doc and code have drifted; whatever lands upstream should be reflected in ORGANISATION.md.

---

## 4. Critical cross-cutting risk: #607's base ≠ this fork's `main`

The PR's `Propositional/Defs.lean` hunk is written against the **upstream** propositional
`Proposition` (`Proposition.impl`, `Proposition.neg`, `instTopProposition [Inhabited Atom]`,
`[Bot Atom]`). This fork's `main` carries a **different, much larger** propositional development:
the five-primitive `Cslib.Logic.PL.Proposition` (`atom/bot/imp/and/or`, derived `neg/top/iff`),
MPL/IPL/CPL, natural-deduction + Hilbert layers, and a *local* `Connectives.lean` with the full
bundled hierarchy (already imported and instantiated by `PL.Defs`). These are fork-local (tasks
229/254/260/266/340/…), **not** in upstream `leanprover/cslib`.

Consequences for the engagement:
- The "five-primitive `Proposition` with primitive `bot`" that motivates this task is a
  **fork-local** type; #607 cannot register it directly because it doesn't exist upstream. The
  faithful-registration ask to fmontesi is therefore *forward-looking* ("please shape the atomic
  classes so a bot-primitive, MPL/IPL/CPL-capable `Proposition` can register `¬` via derived
  `neg` and reuse Mathlib `Bot`/`Top`"), not "register my type now."
- After #607 merges upstream and the fork rebases, the fork must: drop local `scoped` notation,
  re-point `PL.Defs`/`Connectives.lean` instances at the upstream atomic classes, rebuild bundles
  on top, and reconcile naming (`HasImp` vs `HasImpl` vs no-`Has`). That rebase is the *real*
  downstream work; the review should keep #607's atomic classes shaped to make it cheap.

---

## 5. Recommendation: incremental, not alternative

**Choose (a) incremental engagement.** Justification tied to CSLib's ambitions:
- **Broad multi-logic reuse**: #607's atomic mixins are the correct substrate; the fork's bundles
  layer cleanly on top. Reuse-first also says *use Mathlib `Bot`/`Top`*, shrinking #607's surface
  rather than growing a parallel `HasBot`.
- **Idiomatic Lean/Mathlib style**: one-class-per-operator mixins + bridge lemmas is the
  Mathlib pattern; the maintainer (eric-wieser) is already steering toward it (and toward dropping
  `Has`). Aligning beats forking.
- **Minimal notation conflict**: NOTATION.md has no connective standard, so #607 can *define* one;
  endorse its `infixr` ladder and get it written into NOTATION.md.
- **Contributor goodwill / not stepping on an open PR**: Waring explicitly asked us to help #607
  merge. Posting a competing architecture would burn that. A precise, additive review that
  *unblocks* chenson's CHANGES_REQUESTED (file consolidation + `_def` direction + naming) is the
  highest-value contribution.

The only "architectural" inputs to volunteer are (1) reuse Mathlib `Bot`/`Top` + a derived-`¬`
bridge (replacing the `HasBot` idea), and (2) resolve the `Has`-prefix/`impl-vs-imp` naming —
both *inside* #607's existing design, not a replacement for it.

---

## 6. Draft review structure (skeleton + technical content — author the prose yourself; Zulip AI policy)

Build on `benbrastmckie`'s 2026-06-17 comment; do not restate it. Order by priority. Each bullet
is a *point to make*, not text to paste.

1. **Lead with consensus / low-friction wins** (signals collaboration):
   - Endorse file consolidation (eric-wieser/ctchou/chenson agree): single `Operators.lean`
     with one conventions docstring, or ctchou's 3-file split.
   - Endorse eric-wieser's tidier instance syntax (`where and := .and`).
2. **Naming decision (ask, don't dictate)** — highest leverage:
   - Surface the `Has`-prefix question raised by eric-wieser. Give the *counter-argument for
     keeping `Has`*: bare `And`/`Or`/`Iff` collide with core/Mathlib `And`/`Or`/`Iff`, and CSLib
     already uses `Has*` throughout `Foundations/Syntax` (`HasContext`, `HasSubstitution`,
     `HasFresh`). Propose a single ruling that the whole library follows.
   - Settle `impl` vs `imp` in the same breath (you already argued `imp`; ask for a decision).
3. **Falsum / verum via Mathlib `Bot`/`Top` (the corrected primary point)**:
   - State the goal: a formula type with a *primitive* `⊥` (needed for MPL/IPL/CPL, where
     `¬φ := φ → ⊥` and `⊤ := ⊥ → ⊥`) must be registerable faithfully.
   - Show it needs only: (i) `⊥`/`⊤` notation — **reuse Mathlib `Bot`/`Top`**, which CSLib's
     Propositional `Defs` already uses; (ii) a `HasNot` instance from the derived `neg`; (iii) a
     `@[grind/simp]` bridge `(φ → ⊥) = ¬φ` (you already wrote `not_eq` — generalise/orient it).
   - Explicitly *retract the "add a `HasBot` class" framing*: minting `HasBot` duplicates Mathlib
     and runs against the "`Has` is a Lean-3-ism" direction.
   - Float (as a question, not a demand) a default instance
     `[HasImpl α][Bot α] : HasNot α := ⟨(· → ⊥)⟩` for the minimal/intuitionistic convention; note
     the diamond-inheritance risk.
4. **`_def` bridge-lemma direction** (unblocks chenson's CHANGES_REQUESTED):
   - Take a position: normal form = the notation (collapse `φ.and ψ ⤳ φ ∧ ψ`), per chenson and
     `List.append_eq`. Offer to help get `grind` to see through the notation (Waring's blocker),
     so the modal `Satisfies.*_iff_*` proofs don't need `=_ *_def` rewrites.
   - Flag the leftover commented-out `grind only` block in `Satisfies.dual` as cleanup.
5. **Notation precedence → make it the library standard**:
   - Endorse #607's `infixr` ladder (→ 25, ∨ 30, ⊗ 35, ∧ 36, ¬/□/◇ 40, ↔ 20); note the fork's
     non-assoc `infix` is weaker. Propose recording the ladder in NOTATION.md (currently silent on
     connectives). Ask fmontesi to confirm `→` at 25 doesn't shadow core `→` problematically.
6. **Bundles as a follow-up, not a blocker**:
   - Note that polymorphic axiom/theorem development across Propositional/Modal/Temporal/Bimodal
     wants convenience bundles (`PropositionalConnectives` etc.) with defaulted `neg`/`top`.
     Offer to contribute these *on top of* the merged atomic classes in a separate PR. Ask only
     that the atomic classes be named/shaped so a bundle can `extend Bot, HasImpl, HasAnd, HasOr`.
7. **Modality note (low priority, already half-raised)**:
   - #607 has `HasBox` and `HasDiamond` as independent primitives — fine for classical Modal.
     Reiterate (briefly, link your prior comment) that downstream the fork derives `◇ := ¬□¬`;
     this is an instance-level choice, not a #607 blocker. Mention HML's possible need for
     parameterised box/diamond (ctchou's open question) as future work.
8. **Close**: offer concretely to (i) open the follow-up bundle PR, (ii) write the NOTATION.md
   connective section, (iii) help with the `grind`-through-notation issue — i.e., position as
   *unblocking* the PR, honouring Waring's request.

---

## 7. Risks / open questions

- **Naming is unsettled upstream.** If the maintainers drop `Has`, every fork class
  (`HasBot/HasImp/…`) and bundle renames. Until #607's naming is decided, the fork's rebase cost
  is unknown. The review should *force* a naming decision rather than leave it open.
- **`grind`-through-notation may be a genuine blocker.** Waring already tried and reverted to
  explicit `_def` rewrites. If the notation-as-normal-form orientation can't be made to work with
  `grind`, the `_def` lemmas stay "backwards" and chenson's CHANGES_REQUESTED may persist. Verify
  empirically before promising chenson's orientation.
- **Default `HasNot` instance hazard.** A `[HasImpl][Bot] → HasNot` default could create
  instance-resolution ambiguity for classical types that also register a primitive `not`. Float
  as a question; don't assume it's safe.
- **#607 vs fork divergence on Propositional.** #607's Propositional hunk targets the upstream
  type, not the fork's `PL.Proposition`; merge will conflict heavily on the propositional side.
  Plan the fork rebase as separate work; keep the #607 ask forward-looking ("shape the classes for
  a bot-primitive type"), not "register my type."
- **AI policy.** The posted review must be human-authored. This report supplies structure +
  technical substance only; no paragraph here is meant to be pasted verbatim.
- **PR staleness.** Last push 2026-06-16, last review 2026-06-19; chenson's CHANGES_REQUESTED is
  open. A crisp, unblocking review now has good odds of moving it; a heavy architectural ask
  risks stalling it further.
