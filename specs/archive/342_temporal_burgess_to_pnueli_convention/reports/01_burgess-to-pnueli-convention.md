# Research Report: Task 342 — Burgess → Pnueli Convention for `untl`/`snce` in Temporal

**Task (as written)**: Migrate `Cslib/Logics/Temporal` from the Burgess argument order
(`untl event guard`) to the Pnueli order (`untl guard event`) used in `Cslib/Logics/LTL`,
across Syntax, Semantics, Axioms, derived operators, all Metalogic proofs, and the LTL Embedding;
verify sorry-free build.

**Status**: researched

---

## 1. Executive Summary (READ FIRST — premise correction)

**The task description is based on a stale premise. The executable migration to the Pnueli
order was already completed by task 234 (`dee4431e task 234: complete orchestration`).** At the
executable level, `Temporal.Formula.untl`/`snce` **already use the Pnueli order**
(`untl guard event`: first field = guard / intermediate, second field = event / witness),
and they already agree with `LTL.Formula.untl`. The entire Temporal + LTL tree currently
**builds green and sorry-free** (3 scoped `lake build` invocations, all exit 0; see §7).

The codebase states this itself, authoritatively, in `Tableau/Defs.lean:205`:

> "Note: In the Lean inductive, `untl a b` stores guard=a, event=b."

What actually remains as "Burgess" is **NOT** the executable constructor order. It is:

1. **Documentation rot** — module/def docstrings and inline comments across ~10 files still
   describe a "Burgess (event, guard)" convention that the code no longer follows (the comments
   are simply wrong relative to the code).
2. **The 22 BX axiom doc comments** in `ProofSystem/Axioms.lean` use a surface `U(event, guard)`
   notation in their `/-- ... -/` strings, while the Lean term they annotate is Pnueli.
3. **Two derived abbrevs** — `reflexiveUntl` / `reflexiveSnce` (`Syntax/Formula.lean:279–289`)
   are defined in Burgess (event, guard) argument order, used only as the LTL→Temporal bridge.
4. **The LTL Embedding swap** — `LTL.Formula.toTemporal` (`LTL/Embedding.lean:50`) swaps `untl`'s
   arguments specifically to bridge into the Burgess-ordered `reflexiveUntl`.
5. **(Out of stated scope) Tableau executable adapters** — `asUntl?` / `asSnce?`
   (`Tableau/Defs.lean:200–232`) deliberately swap the internal Pnueli `(guard, event)` to an
   external Burgess `(event, guard)` tuple, consumed by `Tableau/Rules.lean` and
   `Tableau/Saturation.lean`.

> **CRITICAL ANTI-PATTERN — do not do the literal task.** If an implementer takes the description
> literally and "swaps the `untl`/`snce` arguments" in `Satisfies`, `someFuture`, the `Axiom`
> constructors, or the Metalogic proofs, they will **reverse a correct, Pnueli-ordered codebase
> back into Burgess**, breaking agreement with LTL and inverting every soundness/completeness
> proof. The executable layer must be left semantically unchanged. The real work is
> documentation alignment plus the small `reflexiveUntl`/Embedding bridge cleanup.

**Net effect**: the task's stated objective ("the two logics agree on Pnueli order") is already
true at the executable level. The remaining work is a documentation-and-bridge cleanup, plus a
scoping decision on the Tableau adapters. This report recommends the orchestrator proceed to
planning on that re-scoped basis (§6), and flags that a planner/human may wish to confirm the
re-scope since it is materially different from the literal description.

---

## 2. Ground-Truth Evidence (executable layer is already Pnueli)

All claims below are from the *executable* definitions, which are authoritative over docstrings.

### 2.1 `Satisfies` (`Semantics/Satisfies.lean:61–66`)
```lean
| .untl ψ φ =>                       -- pattern: φ₁ ↦ ψ (1st field), φ₂ ↦ φ (2nd field)
  ∃ s, t < s ∧ Satisfies M s φ ∧    -- 2nd field φ holds at the witness s  → EVENT
    ∀ r, t < r → r < s → Satisfies M r ψ   -- 1st field ψ holds in between → GUARD
```
So constructor field 1 = guard, field 2 = event ⇒ **`untl guard event` = Pnueli**. Identical
shape to `LTL.Satisfies` (`LTL/Semantics/Satisfies.lean:62`).

### 2.2 `someFuture` (`Syntax/Formula.lean:137–138`)
```lean
abbrev Formula.someFuture (φ) := .untl .top φ      -- guard = ⊤, event = φ
```
This is `untl ⊤ φ` (Pnueli), **not** `untl φ ⊤`. (The task's "someFuture = untl _ top" and the
adjacent docstring both describe the *old* Burgess form `untl φ ⊤`.) LTL is identical
(`LTL/Syntax/Formula.lean:195–196`).

### 2.3 Soundness proof confirms event = 2nd field (`Metalogic/Soundness.lean:263–267`)
```lean
| until_F φ ψ =>                       -- Axiom term: (untl φ ψ).imp (someFuture ψ)
  intro huntl
  obtain ⟨s, hlt, hψ, _⟩ := huntl     -- hψ : Satisfies M s ψ  → ψ (2nd field) is the EVENT
  exact (Satisfies.someFuture_iff M t ψ).mpr ⟨s, hlt, hψ⟩
```
The proof only compiles because `ψ` (the second argument of `untl φ ψ`) is the event. This holds
uniformly across all 26 axiom cases (e.g. `left_mono_until_G` = guard monotonicity changes the
*first* arg; `right_mono_until` = event monotonicity changes the *second*). The Metalogic is
self-consistently Pnueli.

### 2.4 The codebase says so itself (`Tableau/Defs.lean:205`)
> "In the Lean inductive, `untl a b` stores guard=a, event=b."

---

## 3. Inventory of Genuine "Burgess" Residue (the actual work)

### 3.1 Documentation-only (rewrite text; no code change)
Convention docstrings/comments that wrongly claim Burgess (event, guard):

- `Syntax/Formula.lean`: module doc lines 49–75 (esp. 51, 55, 57, 60–75), per-def notes
  135, 145, 195, 208, 210, 220, 222, 226, 228, 262, 267, 302, 308, 322, 327.
- `Semantics/Satisfies.lean`: module doc header 16–29 ("Burgess Convention (Event, Guard)"),
  the inline `(φ=EVENT, ψ=GUARD)` notes at 53–55. The `untl_iff`/`snce_iff` bodies are correct;
  only the surrounding prose mislabels.
- `Syntax/Subformulas.lean`: comments at 79, 89 (the `change` terms are correct Pnueli; only the
  trailing `[... in Burgess]` notes mislead).
- `LTL/Syntax/Formula.lean`: 62, 64 (claims Temporal is Burgess — now false).
- `Tableau/Rules.lean`: 34; `Tableau/Defs.lean`: 37–39 header (the adapter behavior is §3.4).
- Scattered "Burgess convention" mentions flagged by `grep -n "Burgess"` that are about the
  *convention* (not Burgess-1982 lemmas — see §4).

### 3.2 BX axiom doc comments (`ProofSystem/Axioms.lean`, 22 temporal constructors)
The Lean terms are Pnueli; the `/-- ... -/` strings use surface `U(event, guard)` Burgess
notation that no longer matches. Examples:
- `until_F` (182–184): doc says `U(ψ, φ) → F(ψ)`; term is `(untl φ ψ).imp (someFuture ψ)`.
  Pnueli reading of the term is `U(φ, ψ) → F(ψ)`.
- `F_until_equiv` (206–208): doc `F(φ) → U(φ, ⊤)`; term `untl ⊤ φ` = `U(⊤, φ)`.
- `left_mono_until_G`, `right_mono_until`, `enrichment_*`, `self_accum_*`, `absorb_*`,
  `linear_*`, `since_*`, etc. — all need their surface `U(...)`/`S(...)` notation rewritten to
  match the Lean `untl φ ψ` (guard-first) order. **No constructor signatures change.**

### 3.3 `reflexiveUntl` / `reflexiveSnce` (`Syntax/Formula.lean:279–289`)
```lean
abbrev reflexiveUntl (φ ψ : Formula Atom) : Formula Atom := φ ∨ (ψ ∧ (φ U ψ))
abbrev reflexiveSnce (φ ψ : Formula Atom) : Formula Atom := φ ∨ (ψ ∧ (φ S ψ))
```
- Their docstrings describe **(event, guard)** order (`φ` = event holding at the witness), i.e.
  Burgess; the Embedding feeds them `(event, guard)` (§3.4), confirming Burgess arg order.
- **Caution**: the *bodies* are internally suspect — `φ ∨ (ψ ∧ untl φ ψ)` mixes the first
  argument as both a reflexive-now disjunct (`φ`) and as the guard of the inner Pnueli
  `untl φ ψ`. There is **no correctness theorem** anywhere tying `reflexiveUntl`/`toTemporal`
  to a semantics (`Embedding.lean` has no theorems). So the planner should treat these as
  unverified bridge abbrevs: redefine them in Pnueli (guard, event) order with a clear
  one-line semantic spec in the docstring, and (recommended) add a small `Satisfies` lemma to
  lock the intended meaning rather than perpetuate an unspecified form.

### 3.4 LTL Embedding swap (`LTL/Embedding.lean`)
```lean
| .untl φ₁ φ₂ => (toTemporal φ₂).reflexiveUntl (toTemporal φ₁)   -- line 50: swaps φ₁,φ₂
```
- LTL `untl φ₁ φ₂` is Pnueli (φ₁ guard, φ₂ event); it is passed to `reflexiveUntl` as
  `(event, guard)` = `(φ₂, φ₁)` because `reflexiveUntl` is Burgess-ordered. Once `reflexiveUntl`
  is Pnueli, this becomes `(toTemporal φ₁).reflexiveUntl (toTemporal φ₂)` (no swap).
- Module docstrings 12–33, 39–44 also describe the swap and should be updated.
- **Safety**: `LTL.Formula.toTemporal` has **zero downstream consumers** (verified: the only
  `*.toTemporal` references elsewhere are `PL.Proposition.toTemporal` in
  `Bimodal/Embedding/PropositionalEmbedding.lean`, a different function). So this change is
  purely structural and cannot break any proof — it only needs to keep building.

### 3.5 (OUT OF STATED SCOPE) Tableau executable adapters
`asUntl?`/`asSnce?` (`Tableau/Defs.lean:200–232`) return external Burgess `(event, guard)`
tuples from internal Pnueli `untl guard event`; consumers: `Tableau/Rules.lean`,
`Tableau/Saturation.lean` (and `@[simp]` lemmas `asUntl?_untl`, `asSnce?_snce`). The task scope
list does **not** mention Tableau. Two options for the planner:
- **(A) Leave Tableau as-is** (recommended for minimal blast radius): it is internally
  self-consistent and builds; the external Burgess tuple is an isolated local choice. The
  convention header comment (37–39) can be clarified to say "internal Pnueli; this module's
  decomposition adapters expose (event, guard) tuples locally."
- **(B) Fully Pnueli-ify Tableau**: change `asUntl?`/`asSnce?` to `some (guard, event)`, update
  the two `@[simp]` lemmas, and update every destructuring consumer in `Rules.lean`/
  `Saturation.lean`. Larger, error-prone, and beyond the literal scope.

---

## 4. DO-NOT-TOUCH List (false positives for "Burgess")

The Chronicle completeness construction follows **Burgess (1982), "Axioms for tense logic II"**.
The following identifiers/comments name the *author and his lemmas*, NOT the argument-order
convention, and **must not be renamed or "migrated"**:

- `BurgessR3Maximal`, `burgessR`, `burgessRSet`, `burgessRSince`, `burgessRSinceSet`,
  `BurgessR3Maximal_extension_fails`, `BurgessR3Maximal_g_content_sub`, `BurgessR3Maximal_sdc`,
  `BurgessR3Maximal_bot_not_mem`, etc.
- All "Burgess 1982 / Section 2 / Claim 2.11 / Lemma 2.x" reference comments in
  `Metalogic/Chronicle/*` and `Metalogic/Completeness.lean`.
- The `Burgess-Xu (BX)` system name in `ProofSystem/Axioms.lean` and `Metalogic/Soundness.lean`.

Concentrated in: `Chronicle/PointInsertion.lean` (514 `untl`/`snce` occurrences — almost all
correct Pnueli usage inside Burgess-1982-named lemmas), `Chronicle/CounterexampleElimination.lean`
(143), `Chronicle/RRelation.lean` (92), `Chronicle/ChronicleTypes.lean`,
`Chronicle/ChronicleConstruction.lean`, `Chronicle/TruthLemma.lean`. These files need **no code
changes** for this task (their `untl`/`snce` uses are already Pnueli and build green); at most
their occasional "Burgess convention" prose (if any conflates the two senses) should be checked,
but the bulk is legitimate Burgess-1982 referencing.

---

## 5. Verified Current Baseline (sorry-free, all Pnueli)

`lake build` exit 0 for all of (3 invocations):
1. `Cslib.Logics.Temporal.Metalogic`, `…ConservativeExtension`, `…Theorems`,
   `…Metalogic.DenseCompleteness`, `…Metalogic.DenseSoundness`, `Cslib.Logics.LTL.Embedding`.
2. (covered above)
3. `…Tableau.{Saturation,Rules,Closure,TimeOrdering,Branch}`, `Cslib.Logics.LTL.ModelChecking`,
   `Cslib.Logics.LTL.Semantics.GNBA`, `Cslib.Logics.Temporal.FromPropositional`.

No `sorry` in `Cslib/Logics/Temporal` or `Cslib/Logics/LTL` (the single grep hit is a prose
mention of removing a future `sorry` in `LTL/Semantics/GNBA.lean:37`, not an actual `sorry`).

---

## 6. Recommended Re-Scoped Plan (for the planner)

Reuse-first note: this task introduces **no new definitions or abstractions**; it edits docstrings
and re-orders arguments of two existing abbrevs plus one embedding clause. No Mathlib/Foundations
search is applicable. Zero-debt: achievable with **zero sorry, zero new axioms** — every step is
either a comment edit or a structural rename that the existing green build will validate.

Suggested phasing (each phase ends with a scoped `lake build`):

1. **Phase 1 — Convention docstrings (no code)**: Rewrite all "Burgess (event, guard)" prose to
   "Pnueli (guard, event)" in `Syntax/Formula.lean`, `Semantics/Satisfies.lean`,
   `Syntax/Subformulas.lean`, `LTL/Syntax/Formula.lean`, `LTL/Embedding.lean` header,
   `Tableau/Rules.lean`, `Tableau/Defs.lean` header. Update the cross-references between the two
   logics' "Convention Note" sections so each states they agree on Pnueli.
2. **Phase 2 — Axioms.lean doc comments**: Rewrite the 22 BX temporal axiom `/-- -/` surface
   `U(...)`/`S(...)` notations to guard-first Pnueli, matching the (unchanged) Lean terms.
   No constructor signatures change.
3. **Phase 3 — Bridge (`reflexiveUntl`/`reflexiveSnce` + Embedding)**: Redefine the two abbrevs
   in Pnueli (guard, event) order with a precise semantic docstring; remove the argument swap in
   `LTL.Formula.toTemporal`; update Embedding docstrings. (Optionally add a `Satisfies` lemma
   pinning `reflexiveUntl` semantics — recommended but confirm scope.)
4. **Phase 4 — Tableau scoping decision**: Default to Option A (clarify comment only). Only do
   Option B if the user/planner explicitly wants full Tableau Pnueli-ification.
5. **Phase 5 — Full verification**: `lake build` (whole project) + CI pipeline
   (`lake exe lint-style`, `lake shake`, `lake lint` advisory), confirm sorry-free.

Lint-prevention reminders for any *new* lemma added in Phase 3: docstring required (docBlame),
`lemma`/`theorem` for Prop (defLemma), lowerCamelCase, `@[simp]` LHS must be in normal form.

---

## 7. Risks / Open Questions

- **Premise mismatch (highest risk)**: the literal task would invert a correct codebase. The
  plan above must be followed instead of a mechanical argument swap. A human confirmation of the
  re-scope is advisable since the deliverable differs substantially from the description.
- **`reflexiveUntl` is unverified**: no semantic correctness theorem exists for the bridge; its
  current body is internally inconsistent with its docstring. Redefine deliberately rather than
  blindly swap.
- **Tableau scope**: in or out? Recommend out (Option A) unless told otherwise.
- **Naming collision**: ensure edits do not touch the `Burgess*` completeness identifiers (§4).

---

## 8. Key Files (absolute paths)

- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/Formula.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Semantics/Satisfies.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Semantics/Validity.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/ProofSystem/Axioms.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Soundness.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/Subformulas.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Tableau/Defs.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Tableau/Rules.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/LTL/Syntax/Formula.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/LTL/Embedding.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/*` (DO-NOT-TOUCH, §4)
