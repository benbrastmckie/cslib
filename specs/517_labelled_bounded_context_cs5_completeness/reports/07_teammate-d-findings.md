# Task 517 — Teammate D (HORIZONS): Strategic Direction & Long-Term Alignment

**Role**: long-term alignment, scoping challenge, opportunity cost. Deliberately does not
duplicate Teammate A (Simpson Ch.7-8 route), B (alternatives/prior art), or C (critic/assumptions).

**Reference grounding tier**: Tier 1 (literature-backed) + Tier 3 (implementation-backed).
**BibKey verification**: performed against `references.bib` — see Source-to-Implementation Mapping.

---

## Source-to-Implementation Mapping

| Source Claim | BibKey | Lean Target | Translation Notes |
|---|---|---|---|
| Labelled ND system `N_IK(𝒯)`, §3.2 geometric axioms | `Simpson1994` | `Labelled/Deduction.lean` `NIK`, `GeomAxiom` | LANDED. `𝒯`-generic by construction |
| Contexts + `𝒯`-primeness (`:5941`) | `Simpson1994` | `Labelled/Context.lean` `Context`, `TPrime` | LANDED (definitions only) |
| Prime Lemma 5.3.1 (Zorn over whole contexts) | `Simpson1994` | *no declaration exists* | **UNPLANNED in active plan 02** |
| Canonical Model Lemma 5.3.2 (truth lemma) | `Simpson1994` | *no declaration exists* | **UNPLANNED in active plan 02** |
| T-Comp graph completion, Lemma 8.2.5 | `Simpson1994` | *no declaration exists* | **0 mentions in active plan 02** |
| Bounded canonical model, Lemma 8.2.6 | `Simpson1994` | *no declaration exists* | **0 mentions in active plan 02** |
| Adequacy bridge, Lemma 6.1.2 (formulas 6.7/6.8) | `Simpson1994` | `probes/lemma612-scaffold.lean`, `track-c-c1-tele-conj.lean` | Track C C1-C4 landed; C5 crux ahead |
| Labelled-sequent line for intuitionistic modal | `MarinMoralesStrassburger2021` | (framework generalization argument) | Verified present |

BibKeys verified present: `Simpson1994`, `MarinMoralesStrassburger2021`, `Dosen1985`,
`BozicDosen1984`, `AlechinaMendlerdePaivaRitter2001`, `Wijesekera1990`, `Pacheco2024`, `Ewald1986`.
**Missing**: `FischerServi1984` (task notes it as moot post-Track-B-closure; confirmed it is not
cited by any remaining phase).

---

## Key Findings

### F1 (DECISIVE). The active plan's remaining phases do not contain the completeness proof.

This is the finding that should drive the decision, and I do not believe it has been surfaced.

Plan 01 (`plans/01_labelled-framework.md`) had nine phases. Plan 02
(`plans/02_decomposed-track-a-b-c.md`, the **active** plan) **silently dropped plan 01's Phases
5-9** — which are the entire completeness proof — and replaced them with one line, "Phase 15:
`cs5_completeness` assembly".

| Plan 01 phase | Content | Status | Present in plan 02? |
|---|---|---|---|
| Phase 5 | **Prime Lemma 5.3.1** — Zorn over whole contexts | NOT STARTED | **No** |
| Phase 6 | **Canonical model `K^𝒯` + Lemma 5.3.2 (truth lemma)** | NOT STARTED | **No** |
| Phase 7 | `B_K` birelation + Lemma 8.1.2 + ◇-clause reconciliation | NOT STARTED | **No** |
| Phase 8 | `B_K ⊨ cs5FCIncest` — "the reuse win" | NOT STARTED | **No** |
| Phase 9 | `CS5ModalAxiom ≡ IK + Ax(𝒯_S5)` + assembly | NOT STARTED | folded into P15 |

Mechanical check against the active plan:

```
grep -cE "8\.2\.5|8\.2\.6|Prime Lemma|5\.3\.1|truth lemma" plans/02_decomposed-track-a-b-c.md
→ 0
```

**Zero.** The task description names as its "Key targets": *"T-Comp graph completion (Simpson
Lemma 8.2.5) for symmetry; the bounded canonical model lemma over labelled membership y:B in A
(Lemma 8.2.6) for box-backward; a BOUNDED prime lemma; then the truth lemma and
cs5_completeness."* **None of these appear anywhere in the plan being executed.**

Track C (Phases 7-14, i.e. C1-C8) is *entirely* the Ch.6 **adequacy bridge** (Lemma 6.1.2) —
`Conj`/`Tele`, formulas 6.7/6.8, `LTree`/`star`/`prune`, `pathSpine`, `toGraph`, the (◇E)/(⊥E)/(∨E)
cases. It is a *transport lemma between two proof systems*. It is not completeness and it contains
no model construction.

**Consequence**: "C5, then C6-C8, then assembly" is not the last stretch of the task. Even if C5
(HIGH-risk crux) and C6-C8 all succeed, task 517 will have finished **the bridge**, and the actual
theorem — Simpson's Ch.5 canonical model and Ch.7-8 bounded refinement, self-estimated in the task
description at **~1500-2500 lines** — will be at zero, unplanned, and unestimated. The "40-70 hours"
and "~4-6 dispatches remaining" figures are measuring the bridge only.

### F2. The plan executes the option-value-destroying half first.

`cs5_completeness` factors into two independent theorems:

- **(A) Ch.5/7-8**: `⊨_{𝒯-frames} A  ⟹  NIK(𝒯) ⊢ A`. Needs **no adequacy bridge**. This is
  Simpson's own theorem, `𝒯`-generic.
- **(B) Ch.6 adequacy**: `NIK(𝒯) ⊢ A  ⟹  Hilbert_𝒯 ⊢ A`. The bridge. This is Track C.

`cs5_completeness = B ∘ A` at `𝒯 = TS5`.

The team is doing **B first**. That ordering is backwards on option value:

- If **A lands and B fails** → CSLib still gets *"`NIK(𝒯)` is complete for `𝒯`-frames"*, a flagship
  theorem covering the whole intuitionistic modal cube. Large standalone value.
- If **B lands and A fails** → CSLib gets a transport lemma between two proof systems, one of which
  has no completeness theorem. A bridge to nowhere. Modest standalone value.

**A strictly dominates B in standalone value, and A is the unestimated risk.** The correct order is
to retire the unknown that is also the more valuable asset. Doing B first maximizes the chance of
spending the whole budget and ending with the less valuable half.

Compounding this: `reports/02` concluded (~85% confidence) that *"the adequacy bridge is NOT on the
critical path"*; then A3 closed Track B, which put the bridge **back** on the critical path. The
project is now spending its dispatches on a bridge its own research argued was avoidable, because
the avoiding route died. Plan 01 had already marked the bridge **"[GATE — HARDEST NODE]" and
[BLOCKED]** — Track C is the *fourth* assault on the node plan 01 declared the hardest, while the
five phases constituting the actual theorem remain untouched.

### F3. The landed framework is currently dead code carrying a rule-prohibited vacuous definition — shipped in mainline.

This is not "debt to fix before a PR". It is a live standards violation in the root import.

- `Cslib.lean:361-363` publicly imports all three `Labelled/` modules.
- `Context.lean:138`: `def GeomWitnessClosure (𝒯 : Set GeomAxiom) (G : Graph Atom) : Prop := True`

`.claude/rules/cslib.md` and `.claude/rules/lean4.md` both state verbatim:

> **Vacuous Definitions (PROHIBITED)** … `def Foo := True` … These are semantically equivalent to
> `sorry`. If you cannot implement `X`, mark the phase **[BLOCKED]**… Do NOT create vacuous
> placeholders.

Worse, the framework has **no substantive theorem at all**. Complete inventory of its 789 lines:

- *Definitions*: `Label.InW`, `GeomWitnessClosure`, `Context`, `Context.le`, `Deriv`, `TPrime`,
  `TS5`, `GeomAxiom`, `GeomAxiom.Holds`, `ClassicalModel`, `TClosure`, `NIK`, `NIKTheorem`,
  `LabelledFormula.ctxLabels`
- *Theorems*: `Context.le_trans`, `Deriv.ofNIK`, `Deriv.mono`, `T_mem_TS5`, `Five_mem_TS5`,
  `equivalence_of_refl_eucl`, `equivalence_of_classicalModel_TS5`, `TClosure.mono`, `NIK.weaken`,
  **`NIK.smoke_boxE`** (a smoke test)

That is plumbing plus a smoke test. **There is not one theorem about `NIK` — not even soundness.**
No `Zorn`, no prime lemma, no truth lemma, no `T-Comp` (verified by grep; those words occur only in
docstrings, referring to *plan 01's* Phases 5/6 — phases that no longer exist in the active plan).
The landed code is documented against a superseded plan.

Given the user's directive — *"the mathematically correct way to proceed, cutting no corners"* — note
that **the only corner currently cut in this entire effort is this one, and it is already in
`Cslib/`**. That makes fixing it not a strategic trade-off but an immediate obligation.

### F4. The `GeomAxiom.D` fix is cheap and is a *correction*, not a workaround.

The vacuity is defensible **only** because `𝒯 ⊆ {T, B, 4, 5}` are all **universal Horn** (no
existential conclusion ⇒ no Skolem witness ⇒ clause 3 constrains nothing). But `GeomAxiom.D`
(seriality, `∀x ∃y. R x y`) **is a constructor of the type**, and it is the sole existential one.
So the framework is internally incoherent at `𝒯 ∋ D`:

- `ClassicalModel {D} R` = `∀x ∃y, R x y` — **honours D**
- `TClosure {D} R` — has no `D` constructor, **silently ignores D**
- `GeomWitnessClosure {D} G = True` — **silently ignores D**, but clause 3 exists *precisely* for D

So `Context {χ_D} Atom` is a **wrong definition**: it admits contexts Simpson's definition excludes.
Any theorem stated for general `𝒯 : Set GeomAxiom` is unsound-or-vacuous at `𝒯 ∋ D`.

**The fix**: delete `GeomAxiom.D`. Blast radius is verified tiny —

```
grep -rn "GeomAxiom.D" --include=*.lean .
→ Deduction.lean:124   (the .D arm of GeomAxiom.Holds)
→ probes/lemma612-scaffold.lean:119   (IKAx.dDia)
→ probes/adequacy-gate-probe.lean:92  (IKAx.dDia)
```

Three sites. Then `GeomAxiom = {T, B, Four, Five}`, all universal Horn; `TClosure` gains **complete
constructor coverage** (becoming the honest `𝒯`-closure); and `GeomWitnessClosure` +
`geomWitnessClosure_holds` + the `Context.geomWitnessClosure` field can be **deleted outright**.

This is the mathematically correct statement, not a dodge: Simpson's clause 3 exists *solely* for
existential geometric axioms. With none in the type, **the clause does not exist** — it is absent by
construction, not "vacuously true" by stipulation. `IKAx.dDia` (`◇⊤`) goes too, which also repairs
the axiom-side/closure-side mismatch in the probes. Estimated cost: **1-2 hours.**

### F5. `cs5_completeness` is 100% off-roadmap.

```
grep -niE "cs5|is5|constructive|intuition|labelled|simpson" specs/ROADMAP.md
→ (no matches)
```

`ROADMAP.md` is *"Porting BimodalLogic to CSLib"* — Foundations/Logic, Propositional, Modal,
Temporal, Bimodal. Its **Remaining** list is: discrete completeness, continuous extension
completeness, dense/discrete/continuous temporal completeness, abstract shared completeness
infrastructure. Constructive modal logic appears nowhere; it entered via task 501 and has since
consumed **501 → 508 → 509 → 512 → 516 → 517** (six tasks, 47+ commits by `git log --grep`).

**Honest qualification** (against my own thesis): the roadmap's remaining items 36/37/40 are blocked
on *external* BimodalLogic work, and 39/41 are not_started but downstream of them. So CS5 is not
literally starving a runnable roadmap item. The opportunity cost is **attention and dispatch
budget**, not a hard blockage. I decline to overstate this.

### F6. The escalation ladder shows a receding horizon, not convergence.

| Task | Verdict it published | Fate | Effort est. |
|---|---|---|---|
| 508 | "CS5 completeness BLOCKED" | **refuted by 509** | — |
| 509 | symmetric tail works | completeness OPEN; spawned 512 | 12-20h |
| 512 | "Phase-1 GO/NO-GO **PASSED**" | **Phase-7 gate FAILED**; blocked | 10-16h |
| 516 | "independent-≤ is the fix" | **premise REFUTED**; abandoned | 30-50h |
| 517 | Track B viable | **Track B CLOSED mid-flight (A3)** | 40-70h |

Four consecutive confident verdicts overturned by the next dispatch, plus 517 killing its own track
in-flight. Estimates **grew monotonically** 12-20 → 40-70h. Per F1, the 40-70h does not even include
the theorem. That is the signature of a receding horizon.

### F7. Task 512 ↔ 517 is a literal dependency cycle. The block is bookkeeping, not mathematics.

```
512 depends_on [509, 517]
517 depends_on [509, 512, 516]
```

512 → 517 → 512, and 512 → 517 → 516 → 512. **No topological order exists.** The dependency graph is
unsatisfiable; "512 is blocked on 517" can never be discharged.

512's own `blockers` field already records a *final* verdict ("BLOCKED across all known-mechanizable
routes in CSLib's current canonical representation… requires a FOUNDATIONAL change… **a human
decision**") and 512 has landed real, axiom-free value (`cs5_axiom_sound_incest`,
`cs5Incest_forces_symm`, `cs5TwoSidedR_iff_cs5Tail`). 512 and 517 now target **the same theorem**.
Two open tasks for one theorem is the artifact.

**512 needs no mathematics to unblock** — it needs closure, exactly as 509 and 516 were closed.

### F8. The negative result is real, but the mechanization is the contribution — not the discovery.

I will not oversell this asset, because overselling it would itself be a cut corner.

**What is genuinely true**: three axiom-free mechanized lemmas — `cs5_symmetric_tail_box_gap`
(CS5.lean:712), `cs5Incest_forces_symm` (CS5Canonical.lean:643), `cs5TwoSidedR_iff_cs5Tail`
(CS5Canonical.lean:511) — jointly establish that over CSLib's theory-inclusion canonical
representation, symmetry-verification and box-backward are jointly unsatisfiable. That is a
publishable *formalization* artifact and an excellent guardrail set.

**What is not true**: that this is a novel result in constructive modal logic. Task 509's own
description already states the scope caveat: *"the broader infeasibility verdict is a
limitation-of-known-technique argument, **not an impossibility theorem**."* And decisively —
**Simpson himself abandons prime theories for labelled bounded contexts in Ch.7-8**. The community's
method-switch *already encodes* the knowledge that prime theories don't deliver IS5 symmetry;
task 516's report 02 says exactly this (his §3.3 prime model is an "outline" deferring IS5 symmetry
to Fischer Servi). The discovery is folklore-adjacent; the **mechanization** is the new thing.

Correct venue framing: a CSLib artifact + an ITP/CPP-style *formalization experience report*
("what breaks when you mechanize prime-theory canonical models for IS5"). **Not** a modal-logic
theory contribution. Claiming otherwise would be the corner-cut the user forbade.

### F9. The framework already generalizes — it is being valued as if CS5-specific.

`NIK`, `TClosure`, `Context`, `TPrime` are **all parameterized over `𝒯 : Set GeomAxiom` by
construction**. Post-F4, `𝒯` ranges over subsets of `{T, B, 4, 5}` — **16 logics**: IK, IT, IB, I4,
IK4, IK5, IKB, IS4, **IS5**, IKB5, … i.e. the entire intuitionistic modal cube, which is exactly the
cube task 501 established (CK/CT/CS4/CS5). `TS5 := {T, Five}` is *one line* (`Context.lean:247`)
selecting one point of it.

A framework serving 16 logics is worth far more than one serving CS5. **It is already built that
way.** Nothing about the generalization is speculative work — it requires only that the framework be
given a `𝒯`-generic theorem instead of being held hostage to a single `𝒯`.

---

## Recommended Approach

**Verdict: DECOUPLE and REORDER. Do not abandon CS5, and do not run C5 next.**

The framing "push through C5" vs. "land the framework and give up" is a false dichotomy. F1 shows C5
is not the last stretch; F2 shows it is the wrong half to do first. The following retires more risk,
banks more value, and cuts strictly fewer corners than the status quo.

### D1 — Now, ~2-4h: make the landed framework honest. *Non-optional.*

1. Delete `GeomAxiom.D` (3 sites, F4). Delete the `.D` arm of `GeomAxiom.Holds`; delete
   `IKAx.dDia` from the two probes.
2. Delete `GeomWitnessClosure`, `geomWitnessClosure_holds`, and `Context`'s `geomWitnessClosure`
   field. Clause 3 is now **absent by construction**, not vacuous by stipulation.
3. Update the docstrings that still reference plan 01's "Phase 5"/"Phase 6" (superseded plan).

This removes the only cut corner currently in `Cslib/`, and it is *required regardless of every
other decision below*. It should not wait for a PR.

### D2 — Next dispatch: **Prime Lemma 5.3.1 + Canonical Model Lemma 5.3.2**, not C5.

Resume **plan 01's Phases 5 and 6**. These are, verifiably:

- **(a) unstarted** (no `Zorn`/prime/truth-lemma declaration exists);
- **(b) required for completeness under every surviving route** — no route reaches `cs5_completeness`
  without a canonical model and a truth lemma;
- **(c) independent of the C5 crux** — they need `TClosure` (landed) and Zorn, not the Ch.6 tree
  surgery;
- **(d) `𝒯`-generic** (`K^𝒯`) — one proof serves all 16 logics (F9);
- **(e) the framework's first real consumer** — they convert 789 lines of dead plumbing into a
  theorem, curing F3 permanently;
- **(f) the single largest unestimated risk in the task** (F1). Retire it *first*.

Recommended gate: attempt Phases 5-6 at **`𝒯 = ∅` (IK) first**. Every wall in this 47-commit history
is symmetry-driven (`cs5_symmetric_tail_box_gap`, `cs5Incest_forces_symm`,
`cs5TwoSidedR_iff_cs5Tail` all turn on B/5). At `𝒯 = ∅`, `TClosure` collapses to `base` — no
geometric rules, no T-Comp, no symmetry. It exercises the whole Ch.5 pipeline
(`Context`/`TPrime`/Zorn/prime/truth-lemma) with the wall removed. Land it, then add the geometric
layer (`TS5`) and the Ch.8 bounded refinement (8.2.5/8.2.6).

This is **faithful and cuts nothing**: it is Simpson's own order (base system, then geometric
extension), and it changes no theorem statement. Cheap information, correctly sequenced.

### D3 — The Ch.6 bridge (C5-C8) comes *after* D2, or not at all.

C1-C4 are landed sorry-free in `probes/`; they keep their value indefinitely and lose nothing by
waiting. If D2 lands, `NIK(𝒯)` completeness is banked and the bridge becomes a well-motivated
finishing step with a known payoff. If D2 fails, we learn the task is infeasible **without** having
spent 4-6 more dispatches on a bridge to nowhere (F2).

### D4 — Break the cycle: close task 512 now (F7). Zero mathematics required.

Remove `517` from 512's `dependencies`; close 512 as **completed-with-negative-result** (mirroring
509 and 516), banking `cs5_axiom_sound_incest` + the guardrail lemmas in its `completion_summary`.
Transfer sole ownership of `cs5_completeness` to 517. This is pure bookkeeping and unblocks 512
today.

### D5 — Scope the standalone contribution as the *framework*, not the negative result.

Lead with **"labelled natural deduction `N_IK(𝒯)` for intuitionistic modal logics, with canonical
completeness, `𝒯`-generic over the modal cube" (`Simpson1994`)**. Ship the guardrail lemmas as a
supporting *formalization-limitations* section with 509's scope caveat intact (F8) — **not** as the
headline. The framework is the durable asset; the negative result is the well-documented reason it
exists.

### On the user's directive

*"The mathematically correct way to proceed, cutting no corners"* does not mandate **which** theorem
to target — it constrains **how** we prove whatever we target. Applied honestly it yields: (1) fix
the `:= True` that is already shipped (D1); (2) do not reformulate CS5 into anything weaker; (3) do
not overclaim the negative result (F8); (4) do not report "40-70h, C5 is the crux" when the theorem
itself is unplanned (F1). **D1-D5 cut strictly fewer corners than the status quo.** Continuing
straight into C5 would leave a prohibited vacuous definition in mainline and a plan whose named
targets appear nowhere in it — that is the corner-cutting option.

### On reformulating the target (Q6) — declined

Every reformulation I considered cheapens the theorem and I reject them: bounded-model-property or
decidability-flavoured statements are **different theorems**, not CS5 completeness; task 516 already
refuted independent-`≤` as unfaithful. **Do not weaken the target.** The correct move is not to
reformulate the theorem but to **reorder the ladder** (D2) and re-target the *intermediate*
deliverable to `NIK(𝒯)`-completeness — which is Simpson's actual theorem, is strictly more general,
and is 100% faithful.

---

## Evidence-Examples

**F1** — plan 01 phases vs. active plan 02:
```
$ grep -nE "^### Phase" plans/01_labelled-framework.md
563:### Phase 5: Prime Lemma 5.3.1 — Zorn over whole contexts [NOT STARTED]
607:### Phase 6: Canonical model `K^𝒯` + Canonical Model Lemma 5.3.2 (truth lemma) [NOT STARTED]
651:### Phase 7: `B_K` birelation construction + Lemma 8.1.2 + ◇-clause reconciliation [NOT STARTED]
697:### Phase 8: `B_K ⊨ cs5FCIncest` — the reuse win [NOT STARTED]

$ grep -cE "8\.2\.5|8\.2\.6|Prime Lemma|5\.3\.1|truth lemma" plans/02_decomposed-track-a-b-c.md
0
```
Plan 02 Phase 15 verbatim: *"Land `cs5_completeness` … via the adequacy bridge + **labelled canonical
model** (Track C having completed)"* — but Track C (Phases 7-14) is exclusively the Ch.6 bridge; the
labelled canonical model has no phase.

**F3/F4** — the prohibited pattern, shipped:
```
$ grep -n "Labelled" Cslib.lean
361:public import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context

$ sed -n '138p' Cslib/.../Labelled/Context.lean
def GeomWitnessClosure (𝒯 : Set GeomAxiom) (G : Graph Atom) : Prop := True

$ grep -rn "GeomAxiom.D" --include=*.lean .    # blast radius of the fix
Deduction.lean:124 | probes/lemma612-scaffold.lean:119 | probes/adequacy-gate-probe.lean:92
```
`.claude/rules/cslib.md`: *"`def Foo := True` … semantically equivalent to `sorry` … strictly
prohibited."*

**F5** — `grep -niE "cs5|is5|constructive|intuition|labelled|simpson" specs/ROADMAP.md` → no matches.

**F7** — `jq '.active_projects[] | select(.project_number==512 or .project_number==517) | .dependencies'`
→ `512: [509, 517]`, `517: [509, 512, 516]`.

**F9** — `Context.lean:247`: `def TS5 : Set GeomAxiom := {GeomAxiom.T, GeomAxiom.Five}` — one line
selects one point of a 16-logic-generic framework.

---

## Adversarial Self-Verification

Per H4, I challenged each recommendation before returning.

| # | Challenged claim | Outcome |
|---|---|---|
| 1 | "Plan 02 dropped the completeness phases" — am I misreading Track C? | **Verified & held.** Read Phases 11-15 in full. C5=`pathSpine`, C6=`toGraph`, C7=(◇E), C8=(⊥E)/(∨E) — all Lemma 6.1.2 adequacy cases. `grep` for `8.2.5|8.2.6|Prime Lemma|5.3.1|truth lemma` in plan 02 = **0**. Held. |
| 2 | Is the adequacy bridge genuinely required (i.e. is Track C wasted)? | **Revised my draft.** It **is** required: `NIK ⊢ A ⟹ CS5 ⊢ A` is needed to transport out of the labelled system. I removed "the bridge is avoidable" from D3. My claim is narrowed to **ordering**, not necessity. C1-C4 retain full value. |
| 3 | Does D2 (Ch.5) really avoid the C5 crux, or does it need the same tree surgery? | **Held, with flagged uncertainty.** `star`/`prune`/`pathSpine` are the *derivation-to-formula translation* (Ch.6); T-Comp/canonical model need `TClosure` (landed) + Zorn. They look disjoint — but I could not fully confirm from source that Ch.8's 8.2.5 shares no machinery with C5. **This is the single assumption D2 rests on and Teammate A should confirm it before D2 is dispatched.** Lowers my confidence on D2 specifically to medium. |
| 4 | Is the negative result the flagship, as the prompt's Q3 suggests? | **Revised down.** Simpson's own Ch.7-8 method-switch already encodes the insight; 509's description self-caveats it as "not an impossibility theorem". Demoted from headline to supporting section (F8, D5). Overclaiming would violate the user's directive. |
| 5 | Is "CS5 is off-roadmap" doing real work, or is it rhetoric? | **Qualified against myself.** Roadmap items 36/37/40 are blocked on *external* BimodalLogic deps; 39/41 are downstream. CS5 starves *attention*, not a runnable item. Explicitly de-weighted in F5. It is not load-bearing for my recommendation — **F1 and F2 are.** |
| 6 | Is deleting `GeomAxiom.D` a corner-cut (removing a case to dodge an obligation)? | **Held — it is the opposite.** Keeping `D` while `TClosure` and `GeomWitnessClosure` ignore it makes `Context {χ_D}` a *wrong definition*. Removing D makes `TClosure` complete and clause 3 genuinely absent. This strictly *increases* rigour. |
| 7 | Is "close 512" a way to hide a failure? | **Held.** 512 has landed axiom-free value and a final, evidenced verdict; 509 and 516 were closed the same way. The cycle (F7) makes its dependency literally undischargeable. This is bookkeeping repair, not concealment. |
| 8 | Does the user's "cut no corners" directive mandate finishing CS5? | **Held.** It constrains method, not target selection. Under the honest reading it *compels* D1, since the only corner currently cut is in mainline. |

**Reuse Check Protocol** (all 5 steps run): `lean_local_search`-equivalent grep over
`Cslib/Foundations/*` and `Cslib/Logics/Modal/*`; no existing labelled/Zorn/prime infrastructure
found beyond the landed `Labelled/` module; `Deriv.ofNIK`/`Deriv.mono` confirmed as the only bridge
plumbing. My recommendations propose **no new abstraction** — D1 deletes, D2 instantiates existing
`𝒯`-generic definitions. Nothing new to reuse-check.

**Zero-debt compliance**: no recommendation involves `sorry`, a new axiom, or deferral. D1
*removes* an existing `sorry`-equivalent. No forbidden pattern present.

**BibKey status**: 8/9 verified in `references.bib`; `FischerServi1984` missing but confirmed moot
(Track B closed).

---

## Confidence Level

**Overall: HIGH** — driven by F1, which is a mechanical, reproducible fact about the active plan
(`grep` = 0 for every named target), not a judgement call.

Per-claim:

| Claim | Confidence | Basis |
|---|---|---|
| F1 — completeness proof is unplanned in plan 02 | **High** | Direct grep + full read of Phases 11-15; plan 01 vs 02 diff |
| F3/F4 — vacuous def shipped; D-fix is 3 sites | **High** | Source-verified; repo rules quoted verbatim; blast radius grepped |
| F7 — 512↔517 cycle | **High** | `jq` on `state.json`; arithmetically certain |
| F5 — off-roadmap | **High** (fact), **low** (as an argument) | grep = 0; but roadmap items externally blocked — self-qualified |
| F6 — receding horizon | **High** | 5 published verdicts vs. fates; monotone estimate growth |
| F8 — negative result is mechanization-not-discovery | **Medium-High** | 509's own caveat + Simpson's method-switch; venue judgement is mine |
| F2 — option-value ordering argument | **Medium-High** | Logically sound; rests on (A) being separable from (B), which the factoring supports |
| **D2 — Ch.5 avoids the C5 crux** | **Medium** | **The one assumption I could not fully source-confirm (see verification #3). Teammate A should confirm before D2 is dispatched.** |
| D1, D4 | **High** | Mechanical; no mathematical risk |
