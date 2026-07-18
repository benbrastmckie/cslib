# Research Report 06 — Task 512: The Incestuality-Collapse Verdict (Decision-Settling Probe)

**Task type**: cslib (Lean 4, deflection-prone). **Dispatch**: orchestrator, session
`sess_1784097632_a8a105`, `orchestrator_mode=true`, `--lit` active. **No production Lean written**
(source read + `lean-lsp`-style inspection of landed definitions + literature chunks only).
**Scope**: TIGHT — settles the single question that decides whether the birelational pivot has a
green path or has genuinely walled after Phase 5's mechanized collapse.

---

## VERDICT (lead)

**(A) — TRANSCRIPTION ARTIFACT, at the level of the canonical *frame*, not the incestuality
*condition*.** The birelational route has a green path; it has **not** walled.

**Single most important justification:** Phase 5's collapse is provably a property of *CSLib's
Phase-3 canonical frame* (`cs5OnesidedR` = box-inverse only, plus the retained exploding world
`Ω = univ`), **not** of Marin's `bDia`-incestuality condition itself. Marin Thm 7.1's condition —
faithfully transcribed as `cs5Incest` — is **verified on the standard IS5 canonical model**
(Marin Thm 7.2 / Simpson §3.3 / Došen 1985) via the **prime lemma over a *two-sided* R that
carries a diamond clause `{◇A : A ∈ Δ} ⊆ Γ`**. Phase 3 stripped exactly that diamond clause from R
(`CS5Canonical.lean:128-129, 161` — the diamond witness is hard-wired to `Ω`), leaving `boxInv`
as the *only* information in the relation. With no diamond information to source the "back" witness,
the `(1,1,0,0)` condition has nowhere to look but the `boxInv`-monotone side, where it **must**
degenerate to plain symmetry — the collapse Phase 5 mechanized. Restore Simpson's two-sided R over
prime, non-exploding worlds and the same condition is discharged by the disjunction-property prime
lemma with **no** negation-completeness. `report 05`'s already-settled `CS5 ≡ IS5` result licenses
excluding `Ω` (Alechina's redundancy remark), closing the only escape route that would have made
this structural.

**`next_action_hint = revise`** (A, but needs replanning — *not* `implement`). The fix is a
canonical-**frame redesign** spanning the pivot's Phases 3–7 (two-sided R + `Ω`-exclusion +
soundness re-check), which the Phase-5 handoff itself flags as "a new planning round," not a
Phase-5 drop-in retry. It is emphatically **not** `escalate`: (B) is refuted below, so there is no
foundational wall to escalate.

**Confidence:** ~85% that this is (A) and the two-sided-R faithful transcription verifies the
incestuality condition sorry-free; the residual ~15% is the *soundness-rework* over two-sided R
(does box-backward stay the plain prime lemma once R regains its diamond clause), which a
revise+implement cycle resolves — it is known, scoped work (report 04 Q3: ~700–1100 lines), not an
unknown obstruction.

---

## What the question actually was, and why the naive reading is a trap

The dispatch asked whether Phase 5's collapse is (A) a transcription artifact (wrong/degenerate
instance of Marin Thm 7.1) or (B) a structural fact (`boxInv`-monotonicity forces *any*
≤-mediated symmetry-flavored condition to collapse). The trap is that **both a naive-optimistic
"just swap the instance" (A) and a naive-pessimistic "monotonicity kills everything" (B) are
wrong.** The truth is a *third* thing: the incestuality **condition** `cs5Incest` is a *faithful*
transcription of Marin's `(1,1,0,0)` instance (verified below, `CS5Canonical.lean:220-235`); the
artifact is the **canonical frame** it is being evaluated against. This distinction is
load-bearing for the verdict and for the `revise` (not `implement`, not `escalate`) routing.

---

## Sub-question 1 — Marin Thm 7.1's exact condition + the exact instance the B axiom needs

**Marin–Morales–Straßburger 2021, Theorem 7.1 [PS86]** (corpus
`marinmoralesstrassburger_2021…`, **chunk_0043, verbatim, lines 13–15**):

> An intuitionistic modal frame ⟨W, R, ≤⟩ validates `◇ᵏ□ˡA ⊃ □ᵐ◇ⁿA` if and only if the frame
> satisfies (the **intuitionistic klmn-incestuality condition**):
> **if `wRᵏu` and `wRᵐv` then there exists `u′` such that `u ≤ u′` and there exists `x` such that
> `u′Rˡx` and `vRⁿx`.**

Convention (confirmed): `R⁰` is the identity (standard Scott–Lemmon); the ≤-mediation is the
*explicit* `u ≤ u′`, separate from `Rⁿ`. Marin's F1/F2 confluence conditions (`≤∘R` vs `R∘≤`,
chunk_0004) are the *general* birelational monotonicity glue every `CKForces`-style model already
satisfies structurally; they are **not** the klmn condition. So there is **no** additional escape
via "`R⁰` should have been `≤`" — the condition *shape* is faithfully transcribed.

CS5's `B` axiom is a **pair** of Scott–Lemmon axioms, giving **two different instances**:

| CS5 axiom | Scott–Lemmon form | (k,l,m,n) | Instantiated incestuality condition |
|---|---|---|---|
| `bBox : A → □◇A` | `◇⁰□⁰A ⊃ □¹◇¹A` | **(0,0,1,1)** | `wRv ⟹ ∃u′ ≥ w, ∃x (u′ = x ∧ vRx)` i.e. **`wRv ⟹ ∃u′ ≥ w, vRu′`** |
| `bDia : ◇□A → A` | `◇¹□¹A ⊃ □⁰◇⁰A` | **(1,1,0,0)** | `wRu ⟹ ∃u′ ≥ u, ∃x (u′Rx ∧ x = w)` i.e. **`wRu ⟹ ∃u′ ≥ u, u′Rw`** |

Both derivations are correct; I re-derived them independently and they match
`CS5Canonical.lean:208-217` exactly.

**Which does the B axiom "require"?** *Both* — they are the frame correspondents of the two B
schemata, and a sound+complete Marin system for the B-family adds **both** `⊠g0011` and `⊠g1100`
rules, with the canonical model satisfying **both** conditions (Thm 7.2). In CSLib's bundle:

- The **`bBox` (0,0,1,1)** content is **already present** as the *fourth* conjunct of `cs5FCIncest`
  — the `FCsym_box` clause `r w u → u ≤ u' → ∃t, r u' t ∧ w ≤ t` (`CS5Canonical.lean:259`), kept
  verbatim from task-509's `cs5FC''`. Its ≤-slack is on the **landing/container** side.
- The **`bDia` (1,1,0,0)** content is the *fifth*, genuinely-new conjunct, `cs5Incest`
  (`CS5Canonical.lean:234-235`): `∀ {w u}, r w u → ∃ u', u ≤ u' ∧ r u' w`. Its ≤-slack is on the
  **`u`/reached-world** side — i.e. on the `boxInv`-**domain** side once R = `boxInv ⊆`.

**Crucial:** `cs5Incest` (line 234) **is a faithful, correct transcription** of Marin's `(1,1,0,0)`
condition. Phase 4's docstring even documents that Phase 3 had *originally mis-instantiated* it as
the `(0,0,1,1)` `bBox` shape and *corrected* it to `(1,1,0,0)` for genuine `bDia` soundness content
(`CS5Canonical.lean:69-72, 206-217`). So the condition is **not** the artifact. The direction of the
≤-slack relative to `boxInv` is the whole story, and it is dictated by which relation R the
condition is evaluated over — see sub-question 3.

---

## Sub-question 2 — How Marin/Simpson/Došen's canonical model verifies the condition

**Simpson 1994 canonical model** (corpus, quoted in `report 04` §Q1 from chunk `682e04d443e7bbd7`):

```
B = (W, ≤, R, V),   W = {X | X prime},   X ≤ X'  iff  X ⊆ X',
X R Y  iff  {◇A | A ∈ Y} ⊆ X   and   {B | □B ∈ X} ⊆ Y,   V(X) = {a | a ∈ X}
```

Two decisive structural facts:

1. **R is TWO-SIDED.** `X R Y` conjoins a **diamond clause** `{◇A | A ∈ Y} ⊆ X` **and** a **box
   clause** `{B | □B ∈ X} ⊆ Y`. CSLib's `cs5OnesidedR` (`CS5Canonical.lean:128-129`) keeps **only**
   the box clause (`boxInv Γ ⊆ Δ`) and **discards the diamond clause** — confirmed by grep: the
   canonical tail's diamonds are trivially witnessed by `Ω = Set.univ`
   (`CS5Canonical.lean:161`, `diam_witness := ⟨Set.univ, …⟩`), i.e. the diamond side carries **no**
   relational content.

2. **Worlds are PRIME (consistent, disjunction property) — there is NO exploding world.** Simpson's
   `W = {X | X prime}` contains no `Set.univ`. The **Prime Lemma 3.3.2** (`If X ⊬ Y then ∃ prime
   X' ⊇ X …`, standard Lindenbaum) and the **Canonical Model Lemma 3.3.3** discharge the modal
   cases using *only* the disjunction property — **never** `A ∉ X ⟹ ¬A ∈ X`. The **F2 / incestuality
   verification** is where the *diamond clause* earns its keep: the mediating witness `u′` (and `x`)
   are produced by the prime lemma **from the `{◇A | A ∈ Y} ⊆ X` side**, not from `boxInv`.

**Does Simpson's ≤ (⊆ on prime theories) play CSLib's ⊆-on-theories role?** Yes — identical:
`X ≤ X' iff X ⊆ X'` is exactly CSLib's `Preorder.lift … .seg` head-inclusion
(`CS5Canonical.lean:172-173`). **The ≤ is the same; the R is not.** Simpson's verification does
**not** face the "`boxInv` monotone, larger world only adds boxes" problem *because it does not
route the witness through `boxInv` at all* — it routes it through the diamond clause. The
`boxInv`-monotonicity trap is a **one-sided-R-only** phenomenon.

**Došen 1985 (IS5) + `CS5 ≡ IS5` (report 05):** Došen's single-prime-theory two-relation IS5 model
is the clean target. `report 05` already **settled** that Pacheco's collapse extends to S5
(`CS5 ≡ IS5`, verbatim Conclusion + mechanized `cs5_dia_or`/`cs5_dia_bot_imp_bot`). By Alechina's
own **redundancy remark** (ingested, `report 04` Q2): once `◇⊥→⊥` and `◇(A∨B)→◇A∨◇B` are derivable
— which they are in CS5 — **the fallible/exploding worlds become redundant.** So excluding `Ω` at
CS5 strength is not a hack; it is *principled*, and it makes CSLib's Wijesekera-diamond model
coincide with Simpson/Došen's intuitionistic-diamond IS5 model, where the two-sided R lives.

---

## Sub-question 3 — Reconciling with Phase 5's concrete collapse (the "wrong side of R")

Phase 5 mechanized, sorry-free and axiom-clean, that `cs5Incest (@cs5CanonMreach Atom)` is
**false** (`cs5Incest_cs5CanonMreach_false`, `CS5Canonical.lean:465`; via
`cs5CanonMreach_to_univ:419` and `cs5Incest_cs5CanonMreach_forces_univ:430`). **This finding is
correct** — I verified the theorems exist as real declarations, not docstring claims. The argument:

- `cs5Incest` on `cs5CanonMreach` unfolds to: `boxInv w ⊆ u ⟹ ∃u′ ⊇ u, boxInv u′ ⊆ w`.
- `boxInv` is monotone under `⊆`, so `u′ ⊇ u ⟹ boxInv u′ ⊇ boxInv u`. Enlarging `u` **only adds**
  boxed formulas to `boxInv u′`; `w` is untouched by the choice of `u′`. So `boxInv u′ ⊆ w` can
  hold **only if `boxInv u ⊆ w` already** → the condition **collapses to plain symmetry** of the
  one-sided R (which fails: needs negation-completeness, `CS5.lean:52-59`).
- The vivid witness: `Ω` (head `univ`) is reachable from **every** world (`boxInv P ⊆ univ`) but
  `boxInv Ω = boxInv univ = univ ⊄ P` for non-exploding `P`, and `Ω`'s only ≤-superworld is itself.

**Answer to the dispatch's sharpest sub-question — YES, the witness is being sourced from the wrong
side of R.** The collapse is caused by the ≤-witness `u′ ⊇ u` sitting on the **`boxInv`-DOMAIN**
side of the *box-only* relation, where monotonicity is fatal. Two independent confirmations that
this is the artifact, not a law:

1. **The `(0,0,1,1)` sibling does NOT collapse.** `bBox`'s condition `wRv ⟹ ∃u′ ≥ w, vRu′` unfolds
   to `boxInv w ⊆ v ⟹ ∃u′ ⊇ w, boxInv v ⊆ u′`. Here the ≤-witness `u′ ⊇ w` is on the **container**
   side: enlarging `u′` **helps** (it can *absorb* `boxInv v`), and it is satisfied **trivially by
   `u′ = Ω = univ`** (`univ ⊇ w` and `boxInv v ⊆ univ`). Same `boxInv`-monotonicity, opposite
   effect. This directly **refutes (B)**: monotonicity does *not* force *every* ≤-mediated variant
   to collapse — only the one whose ≤-slack lands on the `boxInv`-domain side of a *one-sided* R.

2. **The CS4 precedent is the diamond side, and CS5's B-condition is analogous.** CS4 completeness
   (`CS4.lean:42-49`) verifies `cs4FC'` via `dia_refuting_theory` — a **◇-refuting** world with
   hereditary ◇-exclusion (`excl_head`) — **not** a □-refuting one. Simpson's incestuality
   verification is likewise sourced from the **diamond clause** of the two-sided R. CSLib's Phase-3
   one-sided R deleted precisely that ◇-side, so the `(1,1,0,0)` witness had nowhere to come from
   except the fatal `boxInv`-monotone side. **The collapse is the mechanized signature of the
   missing diamond clause.**

So Phase 5 did not use a *wrong condition*; it correctly evaluated the *right condition* against a
*degenerate frame* (one-sided R + `Ω`). The condition is faithful; the frame is the artifact.

---

## Sub-question 4 — Concrete verdict (A): the exact correct construction to retry

**(A) — the pivot continues, via a canonical-frame redesign.** For an implementation dispatch to
transcribe and retry Phases 5–7, the corrected construction is:

1. **Restore Simpson's TWO-SIDED canonical relation.** Replace `cs5OnesidedR Γ Δ := boxInv Γ ⊆ Δ`
   with the two-clause relation
   ```
   Γ R Δ  :=  (∀ A, ◇A ∈ Δ-support → ◇A ∈ Γ)  ∧  boxInv Γ ⊆ Δ
   ```
   i.e. add the diamond clause `{◇A | A ∈ Δ} ⊆ Γ` (Simpson's `{◇A | A ∈ Y} ⊆ X`). This restores
   the ◇-side information the `(1,1,0,0)` witness must be sourced from. CSLib already has the
   diamond-inverse machinery in scope (`diaInv`, `cs5_boxInv_subset_iff` at `CS5.lean:589`, and
   `cs5Tail`'s ◇-side facts) to state and reason about this clause.
2. **Exclude the exploding world `Ω = univ`.** Thread a hereditary consistency/`Set.univ`-exclusion
   invariant through the canonical world type (precedent: `CS4Segment`'s `excl`/`excl_head`
   field pattern, `CS4.lean:42-46`; here the excluded object is `⊥`/`univ`-membership, giving prime
   *consistent* worlds). **Licensed by `CS5 ≡ IS5`** (report 05) + Alechina redundancy: at CS5
   strength the fallible worlds are redundant, so this loses no completeness.
3. **Verify `cs5Incest` (unchanged condition) on the new frame via the PRIME LEMMA on the ◇-side.**
   With the diamond clause present and `Ω` excluded, `wRu ⟹ ∃u′ ⊇ u, u′Rw` is discharged by a
   Lindenbaum/prime extension sourced from `{◇A | A ∈ w}` (Simpson 3.3.2/3.3.3, Marin F2) — the
   disjunction property only, **no** negation-completeness, **no** `boxInv`-monotonicity trap.
4. **Re-check soundness of the 17 axioms over the two-sided-R frame class** (`cs5_axiom_sound_incest`
   analogue). The residual risk lives here: confirm box-backward stays the plain one-sided prime
   lemma (`report 04` Q3) once R regains its diamond clause. This is the ~15% and is *scoped* work.

**Effort:** this touches Phase-3 (`cs5OnesidedR`, `CS5CanonSegment`), Phase-4 (`cs5FCIncest`
soundness), and Phases 5–7 — i.e. the whole pivot spine. Report 04's estimate stands: ~5–6 phases,
~700–1100 net lines. **This is a plan revision, not a Phase-5 in-flight retry** → `revise`.

---

## Why NOT (B) — the structural-wall reading, explicitly refuted

(B) claims `boxInv`-monotonicity forces *any* ≤-mediated symmetry-flavored condition to collapse,
walling the birelational route in CSLib. Three independent refutations:

1. **The `(0,0,1,1)` sibling is monotonicity-friendly** (sub-question 3.1): same `boxInv`, same ≤,
   opposite outcome — trivially satisfied by `u′ = Ω`. So "any ≤-mediated variant collapses" is
   false even *within* CSLib's current one-sided frame.
2. **Marin's own Thm 7.2 canonical model satisfies the identical `(1,1,0,0)` condition** — over a
   two-sided R prime model. A condition that is *provably satisfiable* by a standard published
   canonical model cannot be structurally uncollapsible; the collapse is frame-specific.
3. **The diamond-mismatch escape that would have made (B) true is already closed.** The one way (B)
   could hold is if CSLib's Wijesekera diamond genuinely could not adopt Simpson's two-sided-R prime
   model (Alechina: constructive diamond ⇒ fallible pairs). But `report 05` settled `CS5 ≡ IS5`
   (mechanized `cs5_dia_or`, `cs5_dia_bot_imp_bot`), which by Alechina's redundancy remark makes the
   fallible worlds redundant at CS5 strength → the two-sided-R prime model *does* apply.

The `boxInv`-monotonicity fact is real and fatal **for the specific one-sided `(1,1,0,0)`
transcription only.** It is not a law about the birelational route.

---

## Adversarial self-verification

- *"`cs5Incest` is a faithful transcription, not the artifact"* — grounded at source level:
  `CS5Canonical.lean:234-235` matches Marin chunk_0043:13-15 under `R⁰=id`, and the file itself
  documents the Phase-3→4 `(0,0,1,1)→(1,1,0,0)` correction (`:69-72, 206-217`). Not inferred.
- *"The artifact is the frame (one-sided R + `Ω`)"* — grounded: `cs5OnesidedR` = `boxInv ⊆` only
  (`:128-129`); diamond witness hard-wired to `Ω` (`:161`); Simpson's R is two-sided (corpus, via
  report 04 chunk `682e…`). The deletion of the diamond clause is verified by grep, not asserted.
- *"Phase 5's collapse is correct"* — I confirmed `cs5Incest_cs5CanonMreach_false` (`:465`) and its
  two lemmas are **real declarations**. I do **not** dispute the mechanization; I relocate its
  cause. No manufactured pessimism *or* optimism — Phase 5 is right about the frame it tested.
- *"(1,1,0,0) is satisfiable on a proper canonical model"* — grounded in Marin Thm 7.2 + Simpson
  3.3.2/3.3.3 (prime lemma, disjunction property). Honest residual: I did **not** re-verify
  Simpson's F2 line-by-line (paywalled full proof); but chunk `682e…`/`8372…` (report 04) give the
  model + prime-lemma mechanism, and Marin Thm 7.2 states soundness+completeness for the whole IS5
  family. Confidence ~85%, residual = the soundness-rework over two-sided R.
- *"`revise`, not `implement`"* — the fix changes the canonical world *type* and R *definition*
  (Phase-3 assets) and re-opens Phase-4 soundness; the Phase-5 handoff itself calls both unblock
  options "a new planning round." Drop-in retry is impossible.
- *"`revise`, not `escalate`"* — (B) is refuted; there is no foundational wall. The remaining work
  is scoped (report 04 Q3), not an unknown. Escalation would ask a human to choose between routes
  that this probe has already resolved to a single one.
- **Zero-debt / reuse-first:** no `sorry`/axiom proposed. The retry maximally reuses the CS4
  `excl`/`dia_refuting_theory` template, `cs5Incest` (unchanged), the prime-lemma machinery, and
  `cs5FCIncest`'s other four conjuncts; only R and the world-type invariant are genuinely new.
  Verified against `references.bib` BibKeys (`MarinMoralesStrassburger2021`, `Simpson1994`,
  `Dosen1985`, `AlechinaMendlerdePaivaRitter2001`, `Pacheco2024`) already added in reports 04–05.

---

## One-line answer

The collapse is **(A) a canonical-frame artifact**: `cs5Incest` faithfully transcribes Marin's
`bDia`-incestuality condition, but Phase 3 evaluates it against a *degenerate* one-sided-R frame
(box-inverse only, exploding `Ω` retained) that strips the diamond clause Simpson/Marin/Došen use
to source the witness; restore the two-sided R over prime non-exploding worlds (licensed by the
settled `CS5 ≡ IS5`) and the same condition is discharged by the prime lemma without collapse —
`next_action_hint = revise`.
