# Research Report — Task 487: Make `bot` Primitive in PR #662's Modal Base

**Session**: sess_1783903472_6dffde_research
**Task type**: cslib
**Mode**: research-only (no Lean files edited)
**Base analysed**: worktree `task-486-pr662-modal-package` @ `4ebdba54`
(`/home/benjamin/Projects/cslib-task-486-pr662-modal-package`)

## Executive Summary

The refactor is **smaller than it first appears**. At the constructor level the change is:

| | Current #662 base | Target (task 487) |
|---|---|---|
| Constructors | `{atom, not, and, diamond, box}` | `{atom, bot, imp, and, or, box, diamond}` |
| Removed | — | `not` |
| Added | — | `bot`, `imp`, `or` |
| Kept | — | `atom`, `and`, `box`, `diamond` |
| Primitive-only-was-derived | — | `imp`, `or` graduate def→constructor |
| Derived-was-primitive | — | `not`→`neg` abbrev (`imp · .bot`) |
| Brand new | — | `bot` nullary constructor |

Because `and`, `box`, `diamond`, `atom` are **untouched**, and because `Cube.lean` never
pattern-matches on `Proposition` (it works at the `logic`/`valid`/set-inclusion level), the
blast radius is concentrated in **`Basic.lean`** and, secondarily, `Denotation.lean` /
`LogicalEquivalence.lean`. **All 26+ Cube.lean declarations survive unchanged** contingent
only on the `Satisfies.*` axiom/converse lemmas in `Basic.lean` continuing to compile.

The two reference implementations map cleanly:
- **#648 `Propositional/Defs.lean`** (`feat/propositional-v2`) supplies the exact
  `inductive` + `neg`/`top`/`iff` derived-abbrev + unconditional `instance : Bot := ⟨.bot⟩`
  + `subst` pattern. Task 487 = this 5-constructor core **plus** `{box, diamond}`.
- **`main:Cslib/Logics/Modal/Basic.lean`** supplies the semantic wiring for a
  primitive-`bot`/`imp` modal base (`Satisfies .bot => False`, `.imp => →`, `neg_iff`
  proved by explicit term, `Bot` instance, notation). The **one divergence**: `main` makes
  ◇ **derived** (`◇φ := ¬□¬φ`) whereas task 487 keeps ◇ **primitive** — so copy `main`'s
  `bot`/`imp`/`neg` handling but **not** its diamond derivation; keep the current base's
  primitive-diamond `Satisfies .diamond => ∃` clause and `HasDiamond` instance.

**Notation discipline (locked):** wire through `Cslib.Foundations.Logic.Operators`
typeclasses (`HasImp`/`HasOr`/`HasAnd`/`HasNot`/`HasBox`/`HasDiamond`) exactly as the
current #662 base already does — **not** #648's fork-local `scoped infix` and **not**
`main`'s `ModalConnectives`/`Connectives`. Add `instance : Bot (Proposition Atom) := ⟨.bot⟩`
for `⊥`.

**Zero-debt note:** every change below has a concrete sorry-free discharge path grounded in
a compiling reference source. No sorry deferral, no new axioms. No `[BLOCKED]` recommendation.

---

## 1. `Basic.lean` (worktree lines 39–323)

### 1.1 The new `inductive` (exact constructor list)

Replace lines 39–50 with:

```lean
/-- Propositions. Primitives are atoms, falsum, implication, conjunction, disjunction, and the
box/diamond modalities. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
  /-- Implication. -/
  | imp (φ₁ φ₂ : Proposition Atom)
  /-- Conjunction. -/
  | and (φ₁ φ₂ : Proposition Atom)
  /-- Disjunction. -/
  | or (φ₁ φ₂ : Proposition Atom)
  /-- Necessity / box. -/
  | box (φ : Proposition Atom)
  /-- Possibility / diamond. -/
  | diamond (φ : Proposition Atom)
```

Notes:
- Current base has **no** `deriving` clause; keep it that way unless a downstream file needs
  `DecidableEq` (none of the four Modal files do). #648 derives `DecidableEq, BEq` and `main`
  derives `DecidableEq`; add only if a concrete need surfaces (none found in this scope).
- `bot` is nullary (no fields) — mirrors #648 line "`| bot`" and `main`'s "`| bot`".

### 1.2 Notation-instance wiring (replace worktree lines 52–92)

**Delete** the two derived `def`s `Proposition.or` (l.70) and `Proposition.imp` (l.78) — they
are now constructors. **Delete** the `not` constructor's `HasNot` instance-to-constructor and
`not_def`. Rewire:

```lean
/-- Bottom element, registered as the canonical `⊥`. -/
instance : Bot (Proposition Atom) := ⟨.bot⟩            -- NEW, unconditional (cf. #648)

instance : HasImp (Proposition Atom) := {imp := Proposition.imp}   -- was a def; now constructor
instance : HasAnd (Proposition Atom) := {and := Proposition.and}   -- unchanged
instance : HasOr  (Proposition Atom) := {or  := Proposition.or}    -- was a def; now constructor
instance : HasBox (Proposition Atom) := {box := Proposition.box}   -- unchanged
instance : HasDiamond (Proposition Atom) := {diamond := Proposition.diamond} -- unchanged

/-- Negation as the sole derived propositional connective: `¬φ := φ → ⊥`. -/
abbrev Proposition.neg (φ : Proposition Atom) : Proposition Atom := .imp φ .bot
instance : HasNot (Proposition Atom) := {not := Proposition.neg}

/-- Reduction lemma: `¬φ` unfolds to `.imp φ .bot`. -/
@[scoped grind =] lemma Proposition.neg_def (φ : Proposition Atom) : (¬φ) = .imp φ .bot := rfl
```

Keep the constructor→notation `_def` reduction lemmas (all remain `rfl`, all `@[scoped grind =]`):
`imp_def : φ₁.imp φ₂ = (φ₁ → φ₂)`, `and_def`, `or_def`, `box_def`, `diamond_def`. These are still
`rfl` because each constructor now equals its `HasX` projection.

`iff` **stays derived** exactly as current (worktree l.86–92): keep `def Proposition.iff := (φ₁ →
φ₂) ∧ (φ₂ → φ₁)`, `instance : HasIff`, `iff_def := rfl`. Task 487's "negation is the only derived
connective" is about the primitive set `{atom,bot,imp,and,or,box,diamond}`; `iff` remains a
derived convenience on top, unchanged. (Optionally add `top := .imp .bot .bot` per #648/`main` if
downstream wants `⊤`; none of the four files need it — **defer to implementer, not required**.)

**Import consideration (minor):** `Bot` lives in `Mathlib.Order.Notation`, already transitively
available via the current `Mathlib.Order.Defs.Unbundled` import. If elaboration complains, add
`public import Mathlib.Order.Notation` (or `Mathlib.Order.TypeTags` as #648 does).

### 1.3 New/changed `Satisfies` clauses (replace worktree lines 96–102)

```lean
@[scoped grind]
def Satisfies (m : Model World Atom) (w : World) : Proposition Atom → Prop
  | .atom p     => m.v w p
  | .bot        => False                                     -- NEW
  | .imp φ₁ φ₂  => Satisfies m w φ₁ → Satisfies m w φ₂       -- NEW (was derived)
  | .and φ₁ φ₂  => Satisfies m w φ₁ ∧ Satisfies m w φ₂       -- unchanged
  | .or  φ₁ φ₂  => Satisfies m w φ₁ ∨ Satisfies m w φ₂       -- NEW (was derived)
  | .box φ      => ∀ w', m.r w w' → Satisfies m w' φ         -- unchanged
  | .diamond φ  => ∃ w', m.r w w' ∧ Satisfies m w' φ         -- unchanged (◇ stays PRIMITIVE)
```

The `.not => ¬Satisfies …` arm is **removed** (negation is now `imp φ bot`, whose clause is
`Satisfies φ → False`, i.e. `¬Satisfies φ` definitionally).

### 1.4 Characterisation theorems (worktree lines 129–176) — disposition table

| Lemma | Current proof | Target disposition | Reason |
|---|---|---|---|
| `Satisfies.not_iff_not` (`⇓¬φ ↔ ¬⇓φ`) | `by rfl` | **Lemma about `imp·bot`.** Keep name; prove `Iff.rfl` **or**, to be safe, the explicit term `⟨fun h hs => h hs, fun h hs => absurd hs h⟩` (copied verbatim from `main`'s `Satisfies.neg_iff`). | `¬φ = imp φ .bot`; `Satisfies (imp φ .bot) = (Satisfies φ → False) = ¬Satisfies φ` **definitionally**, so `Iff.rfl` should close it; `main` uses the explicit term for robustness. |
| `Satisfies.and_iff_and` | `by rfl` | **Unchanged (`Iff.rfl`)** | `and` stays a primitive clause. |
| `Satisfies.or_iff_or` | `grind [=_ or_def, Proposition.or]` | **SIMPLIFIES to `Iff.rfl`** | `or` is now a direct `∨` clause; the def-unfolding grind is obsolete. |
| `Satisfies.imp_iff_imp` | `grind [=_ imp_def, Proposition.imp]` | **SIMPLIFIES to `Iff.rfl`** | `imp` is now a direct `→` clause. |
| `Satisfies.iff_iff_iff` | `simp only [HasIff.iff, Proposition.iff]; grind [= derivation_def]` | **Keep ≈ as-is** | `iff` still derived as `and (imp..) (imp..)`; unfolds to `(⇓φ↔⇓ψ)` via the now-primitive `and`/`imp` clauses. Same simp+grind shape works; grind now needs `and_iff_and`/`imp_iff_imp` (both `@[scoped grind =]`). Verify grind closes; fallback `constructor <;> tauto`. |
| `Satisfies.box_iff_forall` | `Iff.rfl` | **Unchanged (`Iff.rfl`)** | `box` primitive. |
| `Satisfies.diamond_iff_exists` | `by rfl` | **Unchanged (`Iff.rfl`)** | ◇ stays primitive — this is the key departure from `main` (where it is a real proof). |

Add a `bot` reduction lemma if grind/rw ergonomics want it (optional):
`@[scoped grind =] theorem Satisfies.bot_iff : ⇓Modal[m,w ⊨ (⊥ : Proposition Atom)] ↔ False := Iff.rfl`.

### 1.5 `Satisfies.dual` and `Satisfies.box_iff_not_diamond_not` — SURVIVE (with proof adjustment)

Both **statements are unchanged** (both ◇ and □ primitive in current *and* target). Both are
genuine classical semantic theorems. The proofs (worktree l.209–227) currently lean on the
`not` constructor being **definitionally** `¬Satisfies`. On the new base, `¬φ = imp φ .bot`, so
the internal negation steps must go through `not_iff_not` / `neg_def` rather than defeq.

- Recommended discharge: after `simp only [iff_iff_iff, diamond_iff_exists, box_iff_forall]`,
  rewrite negations with `Satisfies.not_iff_not` (or add `neg_def` to the `simp only`), then the
  existing `by_contra` / `push Not` classical skeleton closes unchanged.
- **This is Risk #1 (see §6).** Both are self-contained in `Basic.lean` and used nowhere in the
  other three files, so a proof wobble here is contained.

### 1.6 K axiom and frame lemmas (worktree lines 204–310) — SURVIVE

- `Satisfies.k` (`by grind`): survives; `imp` is now a direct grind clause (was reached via
  `imp_iff_imp`), so grind has strictly more to work with. Likely unchanged.
- `Satisfies.t / b / four / five / d` and their converses
  `t_refl / t_box_diamond / b_symm / four_trans / five_rightEuclidean / d_serial`
  (all `by grind`, some with `simp [imp_iff_imp]`): these consume `diamond_iff_exists`
  (unchanged) and `imp_iff_imp` (now `Iff.rfl` but still a valid `@[scoped grind =]`/`simp`
  lemma). Expected to **survive unchanged**; the `simp [imp_iff_imp]` in `b_symm` (l.260) may
  become a no-op but stays harmless. Verify the `grind`s close; none reference `not`/`and`
  structure.

---

## 2. `Denotation.lean` (worktree 24–51)

### 2.1 New `denotation` clauses (replace worktree lines 24–31)

```lean
@[simp, scoped grind =]
def Proposition.denotation (m : Model World Atom) : Proposition Atom → Set World
  | .atom p     => {w | m.v w p}
  | .bot        => (∅ : Set World)                                   -- NEW  ({w | False})
  | .imp φ₁ φ₂  => {w | w ∈ φ₁.denotation m → w ∈ φ₂.denotation m}   -- NEW  (= (φ₁.denot)ᶜ ∪ φ₂.denot)
  | .and φ₁ φ₂  => φ₁.denotation m ∩ φ₂.denotation m                 -- unchanged
  | .or  φ₁ φ₂  => φ₁.denotation m ∪ φ₂.denotation m                 -- NEW
  | .box φ      => {w | ∀ w', m.r w w' → w' ∈ φ.denotation m}        -- unchanged
  | .diamond φ  => {w | ∃ w', m.r w w' ∧ w' ∈ φ.denotation m}        -- unchanged
```

The `.not => (…)ᶜ` arm is **removed**. For `.imp`, the set-builder form mirrors the `Satisfies`
clause and keeps `satisfies_mem_denotation`'s `<;> grind` structural; `∅` for `.bot` (or
`{w | False}` — pick whichever grind/simp prefers; `∅` is cleaner and `Set.mem_empty_iff_false`
is a simp lemma).

### 2.2 Characterisation proofs — disposition

| Lemma | Current proof | Target disposition | Reason |
|---|---|---|---|
| `satisfies_mem_denotation` | `induction φ generalizing w <;> grind` | **Keep; verify.** Now 7 arms (dropped `not`, gained `bot`/`imp`/`or`). | Each new arm is a direct membership↔Satisfies correspondence; grind has both defs as `@[…grind =]`. `bot`: `w ∈ ∅ ↔ False`; `imp`/`or`: membership unfolds to `→`/`∨`. **Risk #2** — the 2-extra-arm `<;> grind` is the single most likely place to need a `simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_union]` nudge before `grind`. |
| `not_denotation` (`w ∉ (¬φ).denotation ↔ w ∈ φ.denotation`) | `grind [_=_ satisfies_mem_denotation]` | **Keep with `neg_def` unfold.** | `(¬φ).denotation = (imp φ bot).denotation = {w | w∈φ.denot → False} = (φ.denot)ᶜ`. Add `Proposition.neg_def` (or `simp [neg_def]`) so grind sees through the abbrev; then unchanged. |
| `theoryEq_denotation_eq` | `Iff.intro <;> grind [_=_ satisfies_mem_denotation]` | **Unchanged** | Purely structural over `satisfies_mem_denotation`; no constructor matching. |

---

## 3. `LogicalEquivalence.lean` (worktree 54–110)

### 3.1 `Proposition.Context` constructors (replace worktree lines 55–61)

Current: `{hole, not, andL, andR, diamond, box}`. Target — drop `not`, add `imp`/`or` L/R
splits (keep `andL`/`andR`); `bot` needs **no** arm (nullary → no sub-hole):

```lean
inductive Proposition.Context (Atom : Type u) : Type u where
  | hole
  | impL (c : Context Atom) (φ : Proposition Atom)
  | impR (φ : Proposition Atom) (c : Context Atom)
  | andL (c : Context Atom) (φ : Proposition Atom)
  | andR (φ : Proposition Atom) (c : Context Atom)
  | orL  (c : Context Atom) (φ : Proposition Atom)
  | orR  (φ : Proposition Atom) (c : Context Atom)
  | box (c : Context Atom)
  | diamond (c : Context Atom)
```

A "negation context" is no longer primitive; it is expressible as `impL c .bot`, so nothing is
lost. (If the implementer wants a convenience `not` context they can add `abbrev`, but it is not
required and none of the current proofs demand it.)

### 3.2 `fill` clauses (replace worktree lines 65–72)

```lean
| hole => φ
| impL c φ' => (c.fill φ).imp φ'
| impR φ' c => φ'.imp (c.fill φ)
| andL c φ' => (c.fill φ).and φ'
| andR φ' c => φ'.and (c.fill φ)
| orL  c φ' => (c.fill φ).or φ'
| orR  φ' c => φ'.or (c.fill φ)
| box c => .box (c.fill φ)
| diamond c => .diamond (c.fill φ)
```

### 3.3 `Congruence.elim` induction arms (worktree lines 91–110)

Current arms: `hole`; grouped `not c ih | andL c ih | andR c ih`; `diamond c ih`; `box c ih`.
Target — drop `not`, fold the six propositional binary arms into one group (same
`specialize ih w; grind` recipe that `andL`/`andR` already use), keep `diamond`/`box` verbatim:

```lean
case hole => grind
case impL c ih | impR c ih | andL c ih | andR c ih | orL c ih | orR c ih =>
  specialize ih w
  grind
case diamond c ih => … (unchanged from worktree l.97–103)
case box c ih => … (unchanged from worktree l.104–110)
```

**Verify** the grouped `grind` closes `impL/impR/orL/orR` the same way as `andL/andR` — it should,
because after `Satisfies.iff_iff_iff` the goal is a Boolean combination that grind discharges via
`and_iff_and`/`or_iff_or`/`imp_iff_imp` (all `@[scoped grind =]`). Low-moderate risk.

Everything below l.110 (`Satisfies.Context`, `HasHContext`, `HasLogicalEquivalence`,
`IsEquiv` instance) is **structure-agnostic** and survives unchanged.

---

## 4. `Cube.lean` (worktree 27–209) — per-declaration survival

**Headline: nothing in `Cube.lean` pattern-matches on `Proposition` or grinds over
`not`/`and` structure.** Every proof operates at the `logic` / `Proposition.valid` /
set-inclusion layer, or delegates to a `Satisfies.*` lemma. So all survive **unchanged**,
inheriting only whatever happens to the `Basic.lean` lemmas they cite.

| # | Declaration(s) | Kind | Disposition | Reason |
|---|---|---|---|---|
| — | `K, T, B, Four, Five, K45, D, D4, D5, D45, DB, TB, KB5, S4, S5` (15 defs) | logic defs | **Unchanged** | Reference only `logic`/`Model`/frame classes; no `Proposition` constructors. |
| — | `k_subset_d/_b/_four/_five`, `d_subset_t`, `k_subset_t` (6 Order incl.) | `grind only`/`calc` | **Unchanged** | Reason over `subset_def`/`logic`/`valid`; no proposition structure. `grind only` premise lists don't mention constructors. |
| 1 | `K.k_valid` | validity | **Unchanged** | `grind [Satisfies.k]`; `Satisfies.k` survives (§1.6). |
| 2 | `T.t_valid` | validity | **Unchanged** | delegates to `Satisfies.t`. |
| 3 | `B.b_valid` | validity | **Unchanged** | delegates to `Satisfies.b`. |
| 4 | `Four.four_valid` | validity | **Unchanged** | delegates to `Satisfies.four`. |
| 5 | `Five.five_valid` | validity | **Unchanged** | delegates to `Satisfies.five`. |
| 6 | `D.d_valid` | validity | **Unchanged** | delegates to `Satisfies.d`. |
| 7 | `T.t_canonical` | canonicity | **Unchanged** | `:= Satisfies.t_refl h`. |
| 8 | `B.b_canonical` | canonicity | **Unchanged** | `:= Satisfies.b_symm h`. |
| 9 | `Four.four_canonical` | canonicity | **Unchanged** | `:= Satisfies.four_trans h`. |
| 10 | `Five.five_canonical` | canonicity | **Unchanged** | `:= Satisfies.five_rightEuclidean h`. |
| 11 | `D.d_canonical` | canonicity | **Unchanged** | `:= Satisfies.d_serial h`. |

**Caveat (statement-level, not proof-level):** the axiom **statements** use `→`, `◇`, `□`
notation (e.g. `□(φ₁ → φ₂) → (□φ₁ → □φ₂)`). On the new base `→` resolves to the `imp`
constructor (via `HasImp`) instead of the derived `def` — the surface syntax is identical and
elaborates to the same notation instances, so **no statement edits are needed**. `◇`/`□` are
untouched. This is why the cube "re-derives on the new base" essentially for free: the axioms
were always stated in `HasImp`/`HasBox`/`HasDiamond` notation, and only the *denotation* of `→`
under `Satisfies` changed (from a derived unfolding to a primitive clause) — which is exactly
what the surviving `Satisfies.*` lemmas absorb.

**One thing to watch:** `k_subset_*` use `grind only [… = setOf_true, = logic, mem_setOf_eq, =
Proposition.valid]`. `Proposition.valid`/`logic` are unchanged `@[simp, scoped grind =]` defs, so
these premise lists stay valid. No action expected; re-run to confirm.

---

## 5. `references.bib`

**No new entries required.** Both keys cited by the Modal files are already present:
`@book{Blackburn2001,…}` and `@book{ChagrovZakharyaschev1997,…}` (verified in the worktree's
`references.bib`). `Avigad2022` (cited by #648's docstring for the "`¬A := A → ⊥`" convention) is
**not** referenced by any of the four Modal files, so it need not be added unless the implementer
chooses to cite the natural-deduction tradition in `Basic.lean`'s module docstring — optional,
and `Avigad2022` already exists in #648's `references.bib` if desired.

---

## 6. Risk List (2–3 places most likely to need genuine proof rework)

**Risk #1 — `Satisfies.dual` / `Satisfies.box_iff_not_diamond_not` (Basic.lean l.209–227).**
Both ◇ and □ primitive; both survive as *statements* but their proofs currently exploit `not`
being **definitionally** `¬Satisfies`. On the new base negation is `imp φ .bot`, so the internal
`by_contra`/`push Not` steps must be routed through `Satisfies.not_iff_not`/`neg_def`. Mitigation:
add `not_iff_not` (or `neg_def`) to the opening `simp only`; the classical skeleton then closes
unchanged. Self-contained (used nowhere else) → contained blast radius. **Most likely to need a
hands-on tweak.**

**Risk #2 — `satisfies_mem_denotation`'s `induction φ generalizing w <;> grind`
(Denotation.lean l.35–37).** Goes from 5 to 7 arms (drop `not`, add `bot`/`imp`/`or`). The
`bot` (`w ∈ ∅ ↔ False`) and `imp` (set-builder `→`) arms are the ones where a bare `<;> grind`
could stall. Mitigation: precede with `simp only [Proposition.denotation, Set.mem_setOf_eq,
Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]` then `grind`, or
add those membership lemmas to grind's premise list. Cheap to fix, but genuinely needs a compile
check.

**Risk #3 — `Congruence.elim` grouped propositional arm (LogicalEquivalence.lean l.94–96) and
`Satisfies.iff_iff_iff` (Basic.lean l.164–168).** Folding `impL/impR/orL/orR` into the
`andL/andR` `specialize ih w; grind` group assumes grind closes `→`/`∨` congruence identically to
`∧`; and `iff_iff_iff` now depends on the *primitive* `and`/`imp` clauses rather than the derived
defs. Both are expected to work (all the feeder lemmas are `@[scoped grind =]`), but they are the
two spots where a grind that "used to see a def unfold" now "sees a constructor clause" — worth an
explicit `lean_multi_attempt`/`lake build` confirmation during implementation.

**Low/No risk (for completeness):** all of `Cube.lean` (§4); `Denotation.theoryEq_denotation_eq`;
`Basic.lean`'s `k`/`t`/`b`/`four`/`five`/`d` + converses (grind gains, not loses, clauses);
`and_iff_and`/`box_iff_forall`/`diamond_iff_exists` (`Iff.rfl`); `or_iff_or`/`imp_iff_imp`
(strictly *simplify* to `Iff.rfl`).

---

## 7. Implementation Ordering Hint (for the planner)

1. `Basic.lean` inductive + instances + `Satisfies` (§1.1–1.3) — everything else depends on it.
2. `Basic.lean` characterisation lemmas (§1.4) + `dual`/`box_iff_not_diamond_not` (§1.5) +
   K/frame lemmas (§1.6). Gate: `lake build Cslib.Logics.Modal.Basic` green.
3. `Denotation.lean` (§2) — depends only on `Basic`.
4. `LogicalEquivalence.lean` (§3) — depends only on `Basic`.
5. `Cube.lean` (§4) — should compile with **zero edits**; if it does not, the failure points
   back into `Basic.lean` step 2, not into `Cube` itself.

Reference sources to keep open while porting: `main:Cslib/Logics/Modal/Basic.lean` (for
`bot`/`imp`/`neg` semantic clauses + `neg_iff` term) and
`refs/heads/feat/propositional-v2:Cslib/Logics/Propositional/Defs.lean` (for the inductive +
`neg`/`Bot`-instance shape). Do **not** copy `main`'s derived-diamond machinery.
