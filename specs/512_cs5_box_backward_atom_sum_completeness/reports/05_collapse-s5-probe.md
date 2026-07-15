# Research Report 05 — Task 512: The Collapse-Extends-to-S5 Probe (Decision-Settling)

**Task type**: cslib (Lean 4, deflection-prone). **Dispatch**: orchestrator, session
`sess_1784091167_73afcc`, `--lit` active, `orchestrator_mode=true`. **No Lean written** (source read
+ literature chunks only). **Scope**: TIGHT — settles the single question report 04 identified as the
(c)-vs-(d) pivot. Builds on reports 01–04; primary sources: Pacheco 2024 (arXiv:2408.16428, in
corpus, chunks read line-by-line) + CSLib `CS5.lean` source.

---

## VERDICT (lead)

**The collapse extends to S5: YES — clean, definitive, and already partly mechanized in CSLib.**
Pacheco's Conclusion states it verbatim; its operative content (k3, k5 derivable) is a landed,
axiom-free theorem in CSLib. Report 04's framing that "Pacheco proves only KB, not S5" is an
**underread** — Pacheco explicitly extends the collapse to DB/TB/KB5/**S5**.

**BUT this does not, by itself, make box-backward cheap — and it does NOT convert the *atom-sum*
route (task 512's current plan 01) into an easy one.** The decisive new finding: Pacheco's *own*
canonical model for the B-family — the diamond-inverse `∼c` model that report 04's Q3 hoped might be
a shortcut — handles box-backward (Lemma 18/19) via a **pair construction whose primeness step
(Lemma 16) uses the classical negation-completeness move `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`** (Pacheco chunk_0012,
line 48). That is exactly the wall CSLib's quasi-prime theories cannot climb, and exactly what plan
01's `Atom ⊕ Atom` repair exists to replace. So:

- **The Lemma-15 diamond-inverse "shortcut" (Q3) is a DEAD END for box-backward** — it is already
  fully mechanized in CSLib (`cs5_boxInv_subset_iff`, `cs5Tail_symm`), delivers *symmetry* for free
  (which was never the blocker), and leaves box-backward exactly as hard. ~90% confidence.
- **The collapse-YES result refutes option (c)** (banking a negative result): the logic is complete,
  `CS5 ≡ IS5`, and a birelational completeness proof for CS5's theorem set demonstrably exists
  (Došen/Simpson IS5). There is no genuine obstruction to bank.
- **It re-weights the (d) pivot upward** but does not make it push-button: the pivot's load-bearing
  claim (Simpson's *intuitionistic*-diamond box-backward avoids negation-completeness) is grounded
  at the lemma-statement level (report 04 Q1, ~92%), and Pacheco's contrasting need for
  negation-completeness in *his* B-family box-backward is a genuine yellow flag that box-backward
  difficulty is diamond/relation-specific, not automatically dissolved by "one-sided R".

**`next_action_hint = revise`.** The collapse question is answered YES, which (i) removes report 04's
escalation gate and (ii) refutes the "bank the negative result" option — but the answer *changes the
recommended architecture*. Plan 01 (the atom-sum pair construction) walks straight back into the
negation-completeness replacement that has already resisted task 509 and multiple dispatches. The
plan should be revised to adopt report 04's birelational pivot (d) as the primary route, with the
atom-sum construction demoted to fallback. This is not `implement` (plan 01 encodes the harder route)
and not `escalate` (the gating question resolved positively).

---

## Q1 — Pacheco's KB collapse proof: exact axioms/steps, and where negation-completeness enters

**Theorem 13** (Pacheco chunk_0009, lines 26–35) is the collapse core, proved for **CKB = CK +
{B_box, B_dia}** (exactly CSLib's `bBox`/`bDia`):

> For all modal formula ϕ, TFAE: (1) CKB ⊢ ϕ; (2) IKB ⊢ ϕ; (3) CKB ⊨ ϕ; (4) IKB ⊨ ϕ.

The key implication is (4 ⇒ 1) via **Lemma 20** (chunk_0016, lines 56–71), which relies on the
**Truth Lemma (Lemma 19)** over the canonical model `Mc` built on **prime, consistent, non-maximal
CKB-theories** with the diamond-inverse relation

> `Γ ∼c ∆  iff  Γ ⊆ ∆  and  ∆ ⊆ Γ♦`   (chunk_0010, line 60).

**Where negation-completeness enters (decision-load-bearing).** The truth lemma's hard cases route
through:
- **Lemma 16** (∼c forward-confluence; chunk_0011–0012). Its Zorn-maximal forward-closure `Θ` is
  shown to be a *theory* (prime) via: *"Suppose ϕ ∨ ψ ∈ Θ. Then if ϕ ∉ Θ and ψ ∉ Θ, we would have
  that **¬ϕ ∈ Θ and ¬ψ ∈ Θ**. By MP, we would have ¬(ϕ ∨ ψ) ∈ Θ, a contradiction."* (chunk_0012,
  lines 46–53). The step `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` **is classical negation-completeness.**
- **Lemma 18** (chunk_0012, lines 74–91) — "the trickier application of Zorn's Lemma in the Truth
  Lemma" — is the **box-backward pair construction**: `ϕ ∉ Γ ⟹ ∃ CKB-theories ∆, Σ with
  Γ ⪯ ∆ ∼c Σ and ϕ ∉ Σ`. It reuses the Lemma-16 primeness move.
- **Lemma 19** (chunk_0016, box case, lines 3–11) discharges box-backward *by* invoking Lemma 18's
  pair `Γ ⪯ ∆ ∼c Σ`.

So Pacheco's box-backward is: **(a) a two-step ∼c-chain (a pair), and (b) a primeness step using
`¬ϕ ∈ Θ`.** The B/symmetry structure and `∼c` do the ◇-side work cleanly (via `∆ ⊆ Γ♦`, chunk_0016
lines 38–52), but the **□-backward case is where the classical move is spent.** CSLib independently
found and flagged exactly this: `CS5.lean` lines 108–114 note Lemma 18 "delegates its primeness step
to Lemma 16, whose proof contains an unlabelled negation-completeness move (`ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`) that
a poset-maximal, quasi-prime `Θ` does not license."

---

## Q2 — Does the collapse extend to S5? **YES — clean.**

**Pacheco's Conclusion, verbatim** (chunk_0016, lines 73–83):

> "We showed that the constructive and intuitionistic variations of KB coincide. This is in contrast
> to the constructive and intuitionistic variations of K, which do not prove the same ♦-free
> formulas. **This also implies that constructive and intuitionistic variations of DB, TB, KB5, and
> S5 coincide.** See [ADS15] and [Sim94] for definitions of these logics."

This is a direct, explicit claim — **not** a KB-only result. The extension is sound and well-grounded
by the *♦-divergence argument*: the constructive/intuitionistic distinction lives **entirely** in the
diamond fragment — precisely the two axioms bare CK drops, **k3** (`◇(A∨B) → ◇A∨◇B`) and **k5**
(`◇⊥ → ⊥`). The B axioms re-derive both (Arisaka–Das–Straßburger 2015, `ArisakaDasStrassburger2015`).
T and 4 are identical schemata in both settings and introduce no ♦-divergence. Hence *every*
B-extension — DB, TB, KB5, S5 = CK+T+4+B — coincides constructively and intuitionistically.

**Mechanized in CSLib (the operative content is already landed, axiom-free):**
- `cs5_dia_or` (`CS5.lean:555`): `CS5 ⊢ ◇(A∨B) → ◇A∨◇B` = **k3**, transcribed verified axiom-free.
- `cs5_dia_bot_imp_bot` (task 508, cited `CS5.lean:97`): `CS5 ⊢ ◇⊥ → ⊥` = **k5**.
- `CS5.lean:93–99` states directly: *"`CS5` is theorem-for-theorem Simpson's `IS5` (Pacheco,
  `Pacheco2024`, Theorem 13; his Conclusion states the constructive and intuitionistic variants of
  `DB`/`TB`/`KB5`/`S5` coincide) … So `CS5` is **not** a constructively distinct logic from `IS5`."*

**Honest caveat (does not change the verdict):** Pacheco's S5 extension is stated as a *corollary*
("This also implies") of the KB canonical-model result, not re-proved with a separate S5 canonical
model. But what the pivot needs is exactly the *theorem-level* identity `CS5 ≡ IS5`, which is
established (and whose ♦-fragment content is mechanized). So for the decision, **YES-clean stands.**

---

## Q3 — The Lemma-15 diamond-inverse "shortcut": **DEAD END for box-backward (~90%).**

Report 04 flagged Pacheco's **Lemma 15** (∼c is symmetric, chunk_0010 lines 78–84) as an untried
pivot that might give CS5 box-backward directly over CSLib's existing prime-theory canonical model.
**It cannot, and it is not untried — it is already fully mechanized in CSLib:**

- `cs5_boxInv_subset_iff` (`CS5.lean:589`): `boxInv T ⊆ H ↔ T ⊆ diaInv H` for quasi-prime `H,T`.
  Its docstring: *"Pacheco's `∼c` [diamond-inverse] and `cs5Tail` [box-inverse] coincide, and his
  Lemma 15 ('`∼c` is symmetric') is `cs5Tail`'s definitional symmetry with the equivalence inlined."*
- `cs5Tail_symm` (`CS5.lean:645`) **is** Pacheco's Lemma 15: symmetry, definitional, **axiom-free**.

So the diamond-inverse relation is *provably the same relation* as CSLib's box-inverse tail over CS5.
It delivers **symmetry for free** — but symmetry was never the blocker (`cs5Tail_symm` already exists,
soundness over `cs5FC''` is fully landed). Box-backward is **diamond-independent** and remains open
under either framing *because they coincide*. And decisively: in Pacheco's *own* ∼c model, box-backward
(Lemma 18/19) does **not** reduce to Lemma 15 — it needs the pair + the negation-completeness move
(Q1). Lemma 15 addresses only the ◇-symmetry, never the □-backward witness.

**Conclusion:** Lemma 15 is **not** the cheapest route; it is a resolved non-shortcut. This closes
report 04's Q3 hope negatively, with high confidence, grounded in the mechanized coincidence lemma
plus Pacheco's own proof structure.

---

## Q4 — Cross-check against CSLib's real CS5 axioms

Verified directly in `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean:182–234`. `CS5ModalAxiom` =
the 15 `CS4ModalAxiom` constructors verbatim **plus** `bBox : A → □◇A` and `bDia : ◇□A → A`.
Explicitly **B/symmetry, not classical euclidean-5** (`CS5.lean:19–25, 180–181`). Present schemata:
`tBox`/`tDia` (**T**), `fourBox`/`fourDia` (**4**), `bBox`/`bDia` (**B**), over CK. So CSLib's CS5 =
**CK + T + 4 + B = S5-strength via B** — matching Pacheco's S5-family B-extension exactly (both CKB
augmented to full S5). My S5-extension analysis therefore matches the *actual* CSLib axiom set, not a
textbook idealization. Soundness over both `cs5FC` and the weakened `cs5FC''` is fully landed and
axiom-free (`cs5_axiom_sound''`, all 17 axioms); the canonical frame conditions are established
(`cs5FC''_cs5Mreach`); the diamond truth-lemma cases are free (`cs5Tail_dia_of_mem`). The **only** open
sub-problem is box-backward (`CS5.lean:62–91`).

---

## Consequence for the (c)-vs-(d) decision

| Option | Status after this probe |
|---|---|
| (a) doubled-atom repair over `CS5Combined` = **plan 01's atom-sum route** | **Viable but hard** — it exists precisely to *replace* Pacheco's unsound negation-completeness (Q1); task 509 attempted it and did not close it. Not de-risked by collapse-YES. |
| (b) direct attack in two-sided architecture | **NO-GO** (= negation-completeness wall, reports 03/04). |
| (c) bank negative result | **REFUTED by collapse-YES** — logic is complete, `CS5 ≡ IS5`, birelational completeness demonstrably exists. Nothing genuine to bank. |
| (d) birelational pivot (Došen/Simpson, one-sided R + ≤-mediated incestuality) | **Best positive route; upgraded from report 04's escalate-gate.** Collapse-YES removes the Q2 diamond-tradition risk. Residual: Simpson's intuitionistic-diamond box-backward truly avoiding negation-completeness (report 04 Q1, ~92%, grounded at lemma-statement level). |

**Why `revise`, not `implement`:** plan 01 encodes route (a)/the atom-sum pair construction. My Q1
finding *confirms from Pacheco's own text* that this route bottoms out at the negation-completeness
replacement — the hardest, most-resisted part. Implementing plan 01 re-enters that difficulty. The
collapse-YES result instead argues for **revising to the (d) pivot**: `CS5 ≡ IS5` guarantees the
target logic is complete over a birelational model, and report 04's Q3 reuse analysis shows the pivot
maximally reuses CSLib's `CKSegment`/`box_refuting_theory`/`CS4.lean` template while dissolving
box-backward to a one-sided prime lemma **provided** the intuitionistic-diamond box case avoids
negation-completeness (the ~92% residual, which a revise-phase should nail down at proof level before
committing the ~250–400-line soundness rework).

**Why not `escalate`:** the gating question report 04 escalated on is now answered YES. Escalation
would ask a human to choose (c) vs (d); this probe shows (c) is refuted and (d) is the route — a plan
revision, not a human coin-flip.

---

## Adversarial self-verification

- *"Collapse extends to S5"* — grounded at the strongest level: Pacheco's explicit Conclusion
  sentence (chunk_0016:79–80), his Theorem 13 (chunk_0009:26–35), the ♦-divergence mechanism, AND
  CSLib's landed axiom-free `cs5_dia_or` (k3) + `cs5_dia_bot_imp_bot` (k5). Honest caveat recorded:
  S5 is Pacheco's stated corollary, not a separate S5 canonical model — immaterial to the
  theorem-level identity the pivot needs.
- *"Report 04 underread Pacheco"* — verified: report 04 Q2 asserts "Pacheco proves only KB, not S5";
  Pacheco's Conclusion (read this dispatch) explicitly names S5. Correction is source-grounded, not
  rhetorical.
- *"Lemma 15 is a dead end for box-backward"* — grounded in mechanized `cs5_boxInv_subset_iff` +
  `cs5Tail_symm` (box-inverse = diamond-inverse over CS5) and Pacheco's own Lemma 18/19 needing the
  pair + negation-completeness, not Lemma 15. Not manufactured pessimism — it is why symmetry was
  never the blocker.
- *"collapse-YES does not auto-cheapen the pivot"* — deliberately resisted false optimism: the
  box-backward difficulty is diamond/relation-specific (Pacheco needs negation-completeness even with
  ∼c). The pivot's ~92% Q1 residual is left standing, not inflated.
- **Zero-debt**: no `sorry`/axiom proposed. Option (c)'s refutation is a *positive completeness fact*
  (`CS5 ≡ IS5`), not a placeholder. No Option-B deferral recommended anywhere.
- **Reuse-first**: recommendation routes to the pivot that maximally reuses existing CSLib assets
  (`CKSegment`, `box_refuting_theory`, `CS4.lean`), and explicitly flags that plan 01's `CS5Combined`
  apparatus would be discarded — cross-checked against `CS5.lean` and Pacheco chunks in the corpus.
