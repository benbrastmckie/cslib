# Task 517 — Decision Confirmation: Option B (labelled-system completeness) vs Option A (Ch.6 adequacy bridge)

- **Task**: 517 — labelled_bounded_context_cs5_completeness
- **Dispatch**: research (decision-confirmation), literature mode ON, `--hard`
- **Question**: Is restating `cs5_completeness` to target the labelled `NIK`/`Deriv` system
  (Option B) a *faithful, non-vacuous* "CS5/IS5 constructive Kripke completeness" theorem that
  matches Simpson 1994's actual completeness result — or should Option A (build the Chapter 6
  adequacy bridge) be preferred?
- **Reference grounding tier**: **Tier 1** (literature-backed). BibKeys verified against
  `references.bib`; primary source read directly from the ingested corpus.
- **Primary source**: `Simpson1994` (`references.bib:86`), corpus `doc_id
  simpson_1994_intuitionisticmodallogic`, reflowed full text
  (`.../simpson_1994_intuitionisticmodallogic.reflowed.md`), Chapters 6 and 8.
- **Verdict up front**: **CONFIRM Option B**, with one honest-statement caveat and one small
  anti-vacuity add-on. Reasoning below.

---

## Source-to-Implementation Mapping (Tier 1)

| Source claim (Simpson 1994) | BibKey | Chunk/line anchor | Lean target | Status |
|---|---|---|---|---|
| **Thm 8.1.1**: for a tree `G`, `Γ ⊢_G x:A` (labelled ND) ⟺ birelation-model validity | `Simpson1994` | reflowed L1367–1371 | (the base-`𝒯`=∅ shape of) `NIK`/`CKValidFC` biconditional | model for Option B |
| **Thm 8.1.4**: for `𝒯` in scope, `Γ ⊢^𝒯_G x:A` (labelled `N(𝒯)`) ⟺ validity in birelation models **of 𝒯** | `Simpson1994` | reflowed L1419–1423 | `CKValidFC cs5FCIncest φ ↔ NIKTheorem TS5 φ` (the S5 instance) | **THE Option B target** |
| Thm 6.2.1 (adequacy): `A` theorem of `IK+Ax(𝒯)` ⟺ `A` theorem of `N□◇(𝒯)` | `Simpson1994` | report 02 (p.107) | `NIKTheorem TS5 φ ↔ Derivable CS5ModalAxiom φ` | **the Option A bridge — NOT in Cslib** |
| "Thms 6.2.1 and 8.1.4 imply … IKS…S_n [Hilbert] complete … **obtained more easily by considering the Hilbert systems directly (as in §3.3)**" | `Simpson1994` | reflowed **L1425** | shows Hilbert completeness is a *composition*, and the labelled route is the *harder* one | decisive framing |
| **Lemma 8.2.4** (Bounded prime lemma) | `Simpson1994` | reflowed L1485 | `primeLemma` (`Labelled/PrimeLemma.lean`) | **LANDED** |
| **Lemma 8.2.5** (`𝒯`-prime bounded ctx ⟹ `T-Comp(H) ⊨cr 𝒯`) | `Simpson1994` | reflowed L1513 | `cs5FCIncest_canonWorld_r` (`Labelled/FrameClass.lean:192`) | **LANDED** |
| **Lemma 8.2.6 / Lemma 5.3.2** (Bounded canonical model / truth lemma) | `Simpson1994` | reflowed L1521 / L1367 area | `canon_truth_lemma` (`Labelled/CanonicalModel.lean:267`) | **LANDED** |

---

## Findings

### Q1 — What system does Simpson's completeness theorem target: labelled ND, or Hilbert?

**The labelled natural-deduction system, unambiguously.** Simpson's Chapter 8 is titled
"Interpreting `N□◇` in birelation models" (TOC, reflowed L103), and its central results state the
labelled consequence relation on the syntactic side and birelation (= constructive Kripke)
validity on the semantic side:

> **Theorem 8.1.1** *Let `G` be a tree. Then the following are equivalent:*
> 1. `Γ ⊢_G x:A`  [labelled ND consequence in `N□◇`]
> 2. *For all birelation models `B`, for all `G`-interpretations `[·]` in `B`, if for all
>    `z:B ∈ Γ`, `[z] ⊩ B` then `[x] ⊩ A`.*  (reflowed L1367–1371)

The `𝒯`-extension (the S5 case) is:

> **Theorem 8.1.4** *Let `G` be a tree. Then the following are equivalent:*
> 1. `Γ ⊢^𝒯_G x:A`  [labelled ND consequence in `N(𝒯)`]
> 2. *For all birelation models `B` of `𝒯` … `[x] ⊩ A`.*  (reflowed L1419–1423)

Neither theorem mentions the Hilbert axiomatization. The **completeness direction** (2 ⟹ 1) of
8.1.1 is proved "by reducing it to completeness for IL-models" (via Theorem 5.2.1), and Simpson
explicitly notes it needs **no** tree restriction: *"nowhere in the proof of completeness have we
used the assumption that `G` is a tree"* (reflowed L1379). The finite-model-property re-proof in
§8.2 (Lemmas 8.2.4/8.2.5/8.2.6) is a **bounded** canonical model with the same target — and those
three lemmas are exactly what task 517 has already landed (`primeLemma`, `cs5FCIncest_canonWorld_r`,
`canon_truth_lemma`).

**Answer**: Simpson's completeness theorem targets the labelled ND system. Task 517's landed
machinery (§8.2 bounded canonical model) is a faithful mechanization of *that* theorem's
completeness direction.

### Q2 — Is the Hilbert equivalence a separate Chapter 6 result composed AFTER completeness?

**Yes — and Simpson says so in one sentence.** reflowed **L1425**, verbatim:

> "Note that, for any `𝒯 ⊆ {χ_D, χ_T, χ_B, χ_4, χ_5}`, **Theorems 6.2.1 and 8.1.4 imply** the
> soundness and completeness of the corresponding `IKS₁…S_n` relative to its birelation models.
> **However, these results are obtained more easily by considering the Hilbert systems directly
> (as in Section 3.3).**"

This establishes three things decisively:

1. **The two theorems are separate.** 8.1.4 = completeness of the labelled system w.r.t. Kripke
   models (self-standing). 6.2.1 = the adequacy bridge (labelled `N(𝒯)` ⟺ Hilbert `IK+Ax(𝒯)`).
   Hilbert completeness is the *composition* `6.2.1 ∘ 8.1.4`.
2. **Labelled-system completeness w.r.t. Kripke models is a faithful, self-standing result in
   Simpson's own framing** — it does not require Chapter 6.
3. **The labelled route to Hilbert completeness is the harder one.** Simpson himself says the
   Hilbert result is obtained "more easily … directly (as in §3.3)" — i.e. via **Theorem 3.3.4**
   (Chapter 3, a Fischer-Servi-style canonical model built directly on Hilbert theories, which
   does **not** use the labelled system at all). Report 02 documented this and its blocker (the
   `FS`-axiom / box-backward wall that burned task 512's five dispatches).

### Q3 — Is Option B faithful "CS5/IS5 constructive Kripke completeness", or a trivialization?

**Faithful, and non-circular.** The adversarial vacuity/circularity checks all pass:

- **Non-circular (the semantics is NOT defined via `NIK`).** `CKValidFC` (`CKExtension.lean:86`)
  is defined by quantifying over *all* fallible-world Kripke models whose relation satisfies the
  abstract frame condition `FC`, demanding `CKForces` at every world. `CKForces`
  (`Forcing.lean:67`) is Wijesekera-style constructive forcing (`[Wijesekera1990]` Def 1.1.4),
  defined purely by recursion on the formula over `(r, val, botForces)`. **Neither definition
  references `NIK`, `Deriv`, or any proof system.** So `CKValidFC cs5FCIncest φ → NIKTheorem TS5 φ`
  is a genuine semantics-to-syntax bridge, exactly Simpson 8.1.4's (2 ⟹ 1) direction.
- **Non-trivially proved.** The proof is the actual canonical-model construction
  (`primeLemma` seeds a prime bounded context excluding `φ`; `canon_truth_lemma` transfers
  non-membership to non-forcing; `cs5FCIncest_canonWorld_r` certifies the canonical relation lies
  in the frame class). This is a Henkin/canonical-model argument, not a `def := True`
  placeholder. The frame class is inhabited (the canonical model witnesses `cs5FCIncest`), so the
  antecedent `CKValidFC cs5FCIncest φ` is a real constraint (`φ = ⊥` is not valid: a single
  reflexive point with `botForces = False` refutes it), i.e. the theorem is not vacuous on the
  hypothesis side.
- **"Completeness of a system w.r.t. semantics tailored to it" is the standard method, not a
  cheat.** Every Henkin completeness proof in logic has this shape; Simpson's own
  5.2.1/5.3.2/8.1.1/8.1.4 do too. The quantifier in `CKValidFC` ranges over *all* frames in the
  class, not just the canonical one — that is what makes it completeness rather than a tautology.

**One residual vacuity concern, and its fix** — see Adversarial Self-Verification below: the
implication is uninteresting *iff* `NIKTheorem TS5` were true for every `φ` (i.e. `N(IS5)`
inconsistent). That is ruled out mathematically (`N(IS5)` is a faithful proof system for the
consistent logic IS5) but is **not yet mechanically certified**. A one-lemma consistency
certificate closes this.

### Q4 — Is Option A's bridge genuinely unavoidable (for the Hilbert target) and genuinely high-effort?

**Yes on both counts, confirmed; no Mathlib/Cslib shortcut.**

- **Unavoidable to reach `Derivable CS5ModalAxiom` from the landed labelled machinery.** The
  §8.2 bounded canonical model produces `NIKTheorem TS5`-level information. Connecting that to the
  Hilbert `Derivable CS5ModalAxiom` requires precisely `NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ`
  — one direction of Simpson **Theorem 6.2.1**. There is no other bridge inside the labelled
  framework. (The *alternative* to Option A that also reaches Hilbert — Simpson's Chapter 3 /
  Theorem 3.3.4 direct canonical model — is a **different** construction that does not reuse any
  of task 517's landed assets and is blocked for CS5 on the `FS`/box-backward wall per report 02
  §1.4 and task 512's five-dispatch failure.)
- **Genuinely high-effort.** Report 02 rates the Chapter 6 bridge (Track C, C5–C8) at **~25–30%**
  confidence, multi-dispatch, with the `pathSpine`/`addChild` commutation (C5) flagged as "THE
  TRUE CRUX." Four prior dispatches reached only C1–C4; C5 was explicitly deferred. Simpson's own
  text at that point is *deliberately informal* ("We hope that this makes the proof comprehensible
  without too much formality", p.101) and omits two cases as "quite intricate."
- **No mechanization exists anywhere.** Report 02 verified (web + corpus): no mechanized
  labelled↔Hilbert adequacy for any intuitionistic modal logic exists in any proof assistant;
  Marin–Morales–Straßburger 2021 (`MarinMoralesStrassburger2021`, `references.bib:962`) *outsource*
  the hard `valid ⟹ Hilbert` leg to Fischer Servi / Plotkin–Stirling rather than proving it
  syntactically.

### Q5 — Concrete Option B target signature, and are all ingredients landed?

**Restated target (drop-in replacement for the blocked Phase 10 theorem):**

```lean
theorem cs5_completeness {Atom : Type u} (φ : Proposition Atom) :
    CKValidFC.{u, v} cs5FCIncest φ → NIKTheorem TS5 φ
```

where (all identifiers exist and are landed):
- `CKValidFC` — `CKExtension.lean:86` (semantic; unchanged from the current blocked statement).
- `cs5FCIncest` — the frame class already used by the landed soundness lemma and by
  `cs5FCIncest_canonWorld_r`.
- `NIKTheorem` — `Deduction.lean:316`: `NIK 𝒯 (Graph.trivial) [] (⟨choose⟩ ∶ A)` (Simpson's
  theoremhood, `:5114`).
- `TS5 := {GeomAxiom.T, GeomAxiom.B, GeomAxiom.Four}` — `Context.lean:313`.

**Proof shape (contrapositive) and its landed ingredients:**

1. Assume `¬ NIKTheorem TS5 φ`, i.e. `¬ NIK TS5 (Graph.trivial) [] (x₀ ∶ φ)`. **This is the seed
   `primeLemma` consumes directly — no Hilbert bridge is needed to produce it** (this is the
   entire difference from the blocked Hilbert statement, which had to manufacture the seed via
   Theorem 6.2.1).
2. `primeLemma` (Lemma 8.2.4, **LANDED**) → a `TS5`-prime bounded context with `(x₀ ∶ φ) ∉ Γ`.
3. `canon_truth_lemma` (Lemma 5.3.2/8.2.6, `CanonicalModel.lean:267`, **LANDED**) →
   `¬ CKForces CanonWorld.r canonVal canonBotForces w φ`.
4. `cs5FCIncest_canonWorld_r` (Lemma 8.2.5, `FrameClass.lean:192`, **LANDED**) → the canonical
   `CanonWorld.r` satisfies `cs5FCIncest`.
5. The five fallible-world side-conditions `CKValidFC` demands are the **LANDED** lemmas
   `canonVal_mono`, `canonBotForces_mono`, `canonBotForces_val`, `canonBotForces_r`,
   `canonBotForces_r_wit` (`CanonicalModel.lean:224–242`).
6. Assemble to `¬ CKValidFC cs5FCIncest φ`. Contrapositive complete.

**Every ingredient is already landed sorry-free/axiom-clean.** Phase 10 under Option B is a *real*
composition of Phases 6–9, with **no** new hard lemma — in contrast to the blocked Hilbert
statement, whose Phase 10 silently required the entire unbuilt Chapter 6 bridge.

**One recommended add-on (anti-vacuity certificate).** To certify the theorem is a *meaningful*
completeness statement (not vacuously true because `N(IS5)` proves everything), add a consistency
lemma, e.g.:

```lean
theorem nik_TS5_consistent : ¬ NIKTheorem TS5 (Proposition.bot : Proposition Atom)
```

- **Cheapest honest route**: prove the labelled-system **soundness** direction
  `NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` (Simpson 8.1.4, direction 1 ⟹ 2), then apply it to
  `⊥` against the one-point reflexive `cs5FCIncest`-model with `botForces = False`. This
  additionally upgrades Option B to the **full Simpson 8.1.4 biconditional**
  `CKValidFC cs5FCIncest φ ↔ NIKTheorem TS5 φ`.
- **Caveat (do not under-scope this)**: Simpson flags labelled `N(𝒯)` soundness as "more
  difficult" because "(R𝒯) rules mean … excursions through non-tree consequences are unavoidable"
  (reflowed L1423); his proof routes through a modified sequent system. So full NIK soundness is
  itself a non-trivial (though far cheaper than the Ch.6 bridge, and *standard* rather than
  research-territory) sub-project. If only the completeness *goal* is required, the bare
  consistency lemma `¬ NIKTheorem TS5 ⊥` — provable via a single one-derivation soundness argument
  against one countermodel — suffices and is smaller than full soundness.

---

## Adversarial Self-Verification (H4)

I explicitly tried to break the "Option B is faithful and non-vacuous" conclusion.

| Challenge | Outcome |
|---|---|
| **Is `CKValidFC` secretly defined via `NIK` (making the theorem circular)?** | **Refuted.** Read `CKExtension.lean:86` and `Forcing.lean:67` directly: `CKValidFC`/`CKForces` are pure Kripke-forcing definitions over `(r, val, botForces)`, zero reference to any proof system. Non-circular. |
| **Is the theorem vacuous because `CKValidFC cs5FCIncest φ` is never true (empty frame class)?** | **Refuted.** `cs5FCIncest_canonWorld_r` exhibits a concrete inhabitant; simple finite models also qualify. Antecedent is satisfiable (e.g. `φ = ⊤`) and non-trivial (`φ = ⊥` refutable). |
| **Is the theorem vacuous because `NIKTheorem TS5 φ` is true for ALL `φ` (i.e. `N(IS5)` inconsistent)?** | **Partially open — the one real gap.** Mathematically ruled out (`N(IS5)` is a faithful system for consistent IS5), but **not yet mechanically certified in Cslib**. This is why the report *requires* the consistency add-on in Q5, and why the verdict is "CONFIRM **with** the anti-vacuity certificate", not an unconditional confirm. This is the honest limit of the claim. |
| **Does "labelled completeness" actually equal "CS5 completeness" as the task title claims?** | **Refuted as an identity; sharpened as a scope statement.** `NIKTheorem TS5` and `Derivable CS5ModalAxiom` are provably the same theorem-set *only via* Simpson 6.2.1 (the very bridge Option A builds). So Option B must be **stated honestly** as completeness of the labelled `N(IS5)` system — NOT silently relabeled as Hilbert-`CS5` completeness. Under that honest statement it is faithful to Simpson 8.1.4. Silently reusing the name `cs5_completeness` for the Hilbert-flavoured reading would be the one move that *would* be a misrepresentation. Recommend either renaming (e.g. `nik_TS5_completeness` / `cs5_labelled_completeness`) or a docstring that states the target is labelled-system theoremhood and that Hilbert equivalence is deferred to the (unbuilt) adequacy bridge. |
| **Could report 02's "Chapter 3 gets IS5 completeness directly" mean Option B is the wrong labelled detour and we should do Chapter 3 instead?** | **Noted, does not change verdict.** Chapter 3 (Thm 3.3.4, Fischer-Servi canonical model) reaches *Hilbert* IS5 completeness but reuses **none** of task 517's landed assets and is blocked for CS5 on the `FS`/box-backward wall (report 02 §1.4; task 512). Option B *reuses everything already landed*. Chapter 3 is an alternative to **Option A's goal**, not to Option B. |
| **Soundness asymmetry — does the repo already have a matching pair?** | **Confirmed asymmetry, stated for honesty.** The repo has **Hilbert** soundness landed (`cs5_soundness_derivable_incest`, `CS5Canonical.lean:373`: `Derivable CS5ModalAxiom φ → CKValidFC cs5FCIncest φ`) but is missing Hilbert completeness (needs Option A). Option B lands **labelled** completeness but the matching **labelled** soundness (`NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ`) is not yet built. So neither option yields a same-system sound+complete biconditional for free; Option B's is far cheaper to complete (standard soundness induction vs. research-grade tree surgery). |

**Confidence levels (calibrated against this task's documented history of over-rating):**

| Claim | Confidence | Grounding |
|---|---|---|
| Simpson's completeness theorem (8.1.1/8.1.4) targets the **labelled** system, not Hilbert | **~97%** | reflowed L1367–1425, read verbatim |
| Hilbert completeness is a *separate composition* (6.2.1 ∘ 8.1.4), with the labelled route the harder one | **~95%** | reflowed L1425 verbatim |
| Option B target is non-circular (semantics independent of `NIK`) | **~99%** | `CKExtension.lean:86`, `Forcing.lean:67` read directly |
| All Option-B completeness ingredients are landed sorry-free | **~95%** | file reads of the four landed lemmas + five side-conditions; not re-`lake build`ed this dispatch |
| Option B completeness is non-vacuous **given** the consistency add-on | **~90%** | standard Henkin structure; the one gap is mechanized `N(IS5)` consistency |
| Option A bridge is unavoidable-for-Hilbert and high-effort (~25–30%) with no shortcut | **~90%** | report 02 (source-verified) + this dispatch's confirmation of `L1425` |

---

## Verdict

**CONFIRM Option B.** Restate the Phase 10 target to labelled-system completeness:

```lean
theorem cs5_completeness (φ : Proposition Atom) :
    CKValidFC.{u, v} cs5FCIncest φ → NIKTheorem TS5 φ
```

This is a **genuine, faithful mechanization of Simpson 1994 Theorem 8.1.4's completeness
direction** for the S5 frame theory — "constructive Kripke completeness of the labelled `N(IS5)`
natural-deduction system" — the exact theorem Simpson's Chapter 8 machinery (Lemmas 8.2.4/8.2.5/
8.2.6) is designed to prove, and the exact machinery task 517 has already landed. It is **not** a
trivialization: the semantics is independent of the proof system, and the proof is a real
canonical-model construction, not a placeholder.

Two conditions on the confirmation (both cheap, both in-scope for a re-plan):

1. **State it honestly.** The theorem's target is *labelled-system theoremhood* (`NIKTheorem TS5`),
   which is provably identical to Hilbert `Derivable CS5ModalAxiom` **only via** the Chapter 6
   adequacy bridge that this option deliberately avoids. Name/docstring it as labelled-system
   completeness (e.g. `nik_TS5_completeness`), and record that the Hilbert-axiomatic identification
   is deferred future work, not delivered.
2. **Add the anti-vacuity certificate.** Land `¬ NIKTheorem TS5 ⊥` (ideally as a corollary of the
   labelled soundness direction `NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ`, which also completes
   the full 8.1.4 biconditional). Budget this as its own small phase; per Simpson (reflowed L1423)
   labelled soundness for the `𝒯`-extension is "more difficult" than the base case but is standard
   proof-theory, not the research-territory of the Ch.6 bridge.

**Do NOT prefer Option A** for the stated completeness goal: it is unavoidable only if the *Hilbert*
target is mandatory, it is high-effort research territory (~25–30%, C5 crux, no mechanization
anywhere), and it delivers nothing the completeness goal actually needs. Option A remains the
correct future work *iff* a Hilbert-axiomatic `cs5_completeness` becomes a hard requirement — and
even then Simpson's own advice (reflowed L1425) is that the Chapter 3 direct route is easier than
the labelled + Ch.6 composition (subject to the CS5 `FS` wall, report 02 §1.4).

---

## Memory Candidates

1. **Simpson 1994 completeness targets the labelled ND system, not Hilbert.** Thms 8.1.1/8.1.4
   (reflowed L1367–1425) state `Γ ⊢_G x:A` (labelled) ⟺ birelation validity; Hilbert completeness
   is the separate composition `6.2.1 ∘ 8.1.4` and Simpson gets it "more easily … directly (§3.3)"
   via a Fischer-Servi canonical model. Any Cslib task targeting a Hilbert `Derivable` completeness
   *through* a labelled canonical model has an unnecessary Ch.6-adequacy dependency.
2. **Canonical-model completeness against a purely-semantic validity predicate is non-circular even
   when the model is built from the proof system's theories.** Check the *validity* definition
   (here `CKValidFC`/`CKForces`) references no proof system; the frame-class quantifier over all
   models is what makes it completeness rather than a tautology. Vacuity then hinges only on
   system *consistency*, which a one-lemma `¬ ⊢ ⊥` certificate discharges.
