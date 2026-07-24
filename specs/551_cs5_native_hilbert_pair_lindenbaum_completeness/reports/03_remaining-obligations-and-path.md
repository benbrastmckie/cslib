# Research Report: Remaining Obligations and Recommended Path to CS5 Completeness

- **Task**: 551 — cs5_native_hilbert_pair_lindenbaum_completeness (cslib)
- **Date**: 2026-07-24
- **Feeds**: plan revision (`/revise 551`) or status correction
- **Dispatch type**: RESEARCH (findings only; no implementation)
- **Verdict in one line**: The dependency blockers (517/509/508) are **stale/cleared** — all
  three are archived and the task is already `researching`, not `[BLOCKED]`. But the *mathematical*
  blocker report 02 identified is **real, still open, and independently re-confirmed here**: the
  native goal theorem does not exist and its single remaining obligation is a research-grade
  constructive disjunction-property lemma with no semantic witness. The most tractable route to a
  *shippable* completeness theorem is Route A, gated on first proving `CS5 ⊢ idb`.

---

## 1. Blocker re-assessment (deps 517, 509, 508)

**Finding: the task-dependency blockers are stale and can be dropped from the gating list; the
underlying mathematical blocker is unaffected by them and remains open.**

Verified against the filesystem this session:

- `specs/state.json` lists task 551 with `status: "researching"` (NOT `blocked`) and
  `dependencies: [517, 509, 508]`. The `[BLOCKED]` framing in the dispatch is stale relative to
  state.json's own status field.
- All three dependency tasks are **archived** (completed), present only under `specs/archive/`:
  - `specs/archive/508_unblock_CK_CS4_CS5_completeness`
  - `specs/archive/509_rescope_CK_CS5_constructive_completeness`
  - `specs/archive/517_labelled_bounded_context_cs5_completeness`
  None appears in the live `specs/state.json` `active_projects`. The `dependencies` array in
  551's entry is therefore pointing at terminal/archived tasks and no longer gates anything.

**What the archived deps actually delivered (assets, not gates):** task 509 produced the reusable
pair-Lindenbaum ingredients (`probes/cs5-pair-primeness.lean`: seed / chain-union /
component-maximality) and the `cl`-stability diagnosis; task 517 pursued the labelled route; task
508 unblocked the CK/CS4/CS5 soundness column. These are landed and consumed. They do **not**
resolve the core obstruction.

**The real blocker (report 02's finding) is not a task dependency at all.** It is an intrinsic
proof-theoretic lemma — the constructive disjunction property of the combined `CS5PairAxiom`
system under the `boxInv` cross-constraint (equivalently the seed-exclusion
`τ_L(□A) ⊔ τ_R A ∉ cl(S₀)`). Report 02 established, and this dispatch does not dispute, that this
fact has **no semantic witness** (cross-axiom soundness forces a common valuation that collapses
the two copies, so no sound model separates `S₀` from the exclusion set), has defeated three
distinct native attempts, and inside a Hilbert calculus admits no known correct technique short of
a cut-free/labelled detour (= Route C, a non-goal). Clearing the stale task deps does **not** make
this proceed.

**Conclusion:** Work *can* proceed in the sense that nothing is waiting on an unfinished sibling
task — but the plan's Phase 4 remains blocked on an open mathematical result, exactly as report 02
concluded. The status-hygiene action is: drop `[517, 509, 508]` from 551's `dependencies` (they
are archived) and keep the task's real state as "blocked on an open lemma / awaiting user route
decision," not "blocked on sibling tasks."

## 2. Current state (build + sorry/error census, verified against live source)

**Scoped build: GREEN.** `lake build` over the four file_scope modules plus `CS5Completeness`
(`Cslib.Logics.Modal.Metalogic.Constructive.{CS5Completeness, CS5Canonical, CS5}`,
`.CKExtension`, `Cslib.Foundations.Logic.Metalogic.PrimeExclusion`) completed successfully — **731
jobs, exit 0**. The only diagnostics are pre-existing `linter.flexible` style *warnings* in
`Cslib/Logics/Modal/Basic.lean` (a transitive dep, not in scope); no errors.

**Sorry/admit census: ZERO in all scope files.** `grep -rn '\bsorry\b|\badmit\b|\bsorryAx\b'`
across the four scope files and `CS5Completeness.lean` matched **only docstring prose**
("sorry-free", "scaffolded sorry-free"), never a tactic/term `sorry`. There is no proof debt to
discharge because — critically — **the completeness theorem was never assembled** (see §3).

**Landed sorry-free assets (verified line numbers this session):**

| Asset | Location | Role |
|---|---|---|
| `cs5_axiom_sound''` | `CS5.lean:352` | soundness over `CKValidFC cs5FC''` |
| `cs5_dia_or` (k3) | `CS5.lean:539` | collapse axiom |
| `cs5_dia_bot_imp_bot` (k5) | `CS5.lean:712` | collapse axiom |
| `cs5_symmetric_tail_box_gap` | `CS5.lean:686` | mechanized diagnosis of *why* box-backward needs a pair |
| `CS5PairAxiom` + `cs5PairAxiom_left/right_derivable` + `crossCond_left/right_stable` | `CS5Completeness.lean:92–157` | Phase 1–3 atom-sum infra |
| `ckvalidFC_completeness` (parametric driver) | `CKExtension.lean:246` | the theorem a native `cs5_completeness''` must instantiate |
| `is5_completeness` | `IS5.lean:364` | Route-A target (already landed, uses `.idb`) |

**What is NOT present (the gap, verified by grep across all of `Cslib/`):**

- `cs5_completeness''` — **does not exist as a declaration anywhere.** The only `cs5_completeness`
  in the tree is `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Completeness.lean:130`, which
  is the **Route-C labelled** result (an explicit task non-goal), not the native `CKValidFC`
  theorem.
- `cs5_box_backward` — **does not exist as a declaration.** It appears only as prose in
  `CS5Canonical.lean` docstrings ("scaffolded sorry-free but not yet [in the library]"). There is
  no `sorry` because the theorem is simply absent, not stubbed.
- `cs5_box_backward_onesided` — likewise no declaration; prose-only.
- `idb` / `k4` — **absent from all `Constructive/CS5*` files.** `idb` exists only in the
  intuitionistic/minimal systems (`IS5.lean`, `IS4.lean`, `MS5.lean`, …). So `CS5 ⊢ idb` (report
  02's flagged Route-A premise) is **unproven**, confirmed.

**Net:** the four scope files compile clean with zero debt, but the deliverable (`cs5_completeness''`)
is unbuilt. The state is "green but incomplete," not "green with sorries."

## 3. What remains — the smallest obligation set to close completeness

A native `cs5_completeness''` is a **one-line instantiation** of `ckvalidFC_completeness`
(`CKExtension.lean:246`) at `Axioms := CS5ModalAxiom`, `FC := cs5FC''`, over the symmetric-tail
canonical world type. Its non-trivial hypothesis is the `realize` witness:

```
realize : ∀ {φ}, ¬ Derivable CS5ModalAxiom φ → ∃ w, ¬ CKForces r val botForces w φ
```

Every truth-lemma case except one is discharged by the reused generic `ck_truth_lemma`. The single
open case is **box-backward**: for an unwarranted box `□A ∉ H`, exhibit a canonical world (a
symmetric predecessor in the `cs5Tail` construction) that omits `A`. By
`cs5_symmetric_tail_box_gap` (`CS5.lean:686`), B's symmetry forces a *two-sided* relation whose
witness must be a simultaneous maximal-theory **pair** `⟨H', T⟩` with
`boxInv H' ⊆ T`, `boxInv T ⊆ H'`, `□A ∉ H'`, `A ∉ T`.

Producing that pair is the plan's Phase 4, which decomposes into:

1. **(Mechanical) Propositional-core extension of `CS5PairAxiom`.** `prime_exclusion` /
   `prime_set_exclusion` (`PrimeExclusion.lean`) require the `orE`/`implyK`/`implyS`/`efq`/… schema
   hypotheses (`hOrE`, `hCut`, …) at **arbitrary, including mixed** `Proposition (Atom ⊕ Atom)`
   formulas. Phase 3's four-constructor `CS5PairAxiom` (`left`/`right`/`cross1`/`cross2`) supplies
   them only at pure-tagged copies. Fix: add ~9 propositional-core constructors quantified over the
   whole combined type (keeping the modal schemata pure-tagged). This is bounded and low-risk.
2. **(Tractable) The two individual exclusions.** `τ_R A ∉ cl(S₀)` and `τ_L(□A) ∉ cl(S₀)` both
   reduce to consequences of `□A ∉ H` via K-distribution over the boxed context (report 02 §2).
   These are provable.
3. **(THE BLOCKER — research-grade) The disjunction-level seed-exclusion.**
   `τ_L(□A) ⊔ τ_R A ∉ cl_{CS5PairAxiom}(S₀)` — the `DerivExcludes D E S₀` precondition
   (`PrimeExclusion.lean:332`). At the *non-prime* seed, "neither disjunct derivable" does **not**
   give "disjunction not derivable" (constructively strictly weaker), so this needs the combined
   system's **disjunction property under the `boxInv` cross-constraint** proved directly. Report 02
   §2 shows it has **no semantic witness** and is exactly Pacheco 2024 Lemma 16 (whose published
   proof is unsound here). This is the sole genuinely open obligation.

Phases 5–7 (project the prime pair back through `Sum.inl`/`Sum.inr`, feed box-backward, assemble
`cs5_completeness''` + the biconditional) are mechanical **once** obligation 3 lands.

**Smallest closing set for the NATIVE route = {obligation 1 (mechanical), obligation 2 (tractable),
obligation 3 (open research lemma), then Phases 5–7 assembly}.** The entire task collapses onto
obligation 3.

## 4. Recommended path

Because obligation 3 is research-grade with no semantic shortcut (independently re-confirmed), the
decision is genuinely a **route/mandate choice for the user**, matching report 02's escalation.
This report makes the two live routes concrete and ranks them.

### Route A — collapse to IS5, inherit `is5_completeness` (RECOMMENDED for a shippable theorem)

Delivers `Derivable CS5ModalAxiom`-completeness by transport, at the cost of the native-Hilbert
method-uniformity mandate. It is bounded and mostly-landed (`is5_completeness` at `IS5.lean:364` is
done and already threads `.idb`). Concrete obligations, in order:

1. **`cs5_derives_idb : ∀ φ ψ, Derivable (@CS5ModalAxiom Atom) (IS5's idb schema φ ψ)`** — the one
   unverified premise (report 02 §4). `idb` is confirmed absent from Constructive/CS5, so this must
   be proved. It is a bounded, self-contained Hilbert derivation (the `□`/`◇` interaction). **This
   is the first action of Route A — do it before committing to the route**, since it is the only
   thing standing between "mostly done" and "done."
2. **`cs5_iff_is5_derivable : Derivable CS5ModalAxiom φ ↔ Derivable IS5ModalAxiom φ`** — forward via
   the collapse axioms `cs5_dia_or` (k3, `CS5.lean:539`) + `cs5_dia_bot_imp_bot` (k5, `CS5.lean:712`)
   + `cs5_derives_idb`; reverse by checking each `IS5ModalAxiom` constructor is `CS5`-derivable
   (K/T/4/B modal core is shared).
3. **`cs5FC_iff_is5FC_valid : CKValidFC cs5FC'' φ ↔ IValidFC is5FC φ`** — the validity-coincidence
   bridge (a soundness/soundness coincidence, not circular: it draws on the *independently landed*
   `is5_completeness`, not on CS5 completeness). Both frame classes are reflexive-transitive-
   symmetric; the fallible-world `botForces` layer coincides.
4. **`cs5_completeness'' := ` compose 2 + 3 + `is5_completeness`.** Then state
   `cs5_soundness_completeness''` with `cs5_axiom_sound''` (`CS5.lean:352`).

Mathlib API: essentially none new — this is intra-repo transport. No Zorn/lattice machinery beyond
what `is5_completeness` already carries.

### Route Native-incremental — land the mechanical assets, isolate the open lemma (RECOMMENDED if the mandate is firm)

Preserves the mandate and produces real, reviewable library value without a mandate change:

1. Land obligation 1 (propositional-core `CS5PairAxiom` extension) — mechanical, ~9 constructors.
2. Land obligation 2 (the two individual exclusions `τ_L(□A) ∉ cl(S₀)`, `τ_R A ∉ cl(S₀)`).
3. **Formally isolate obligation 3 as a single named, precisely-stated open lemma** (the combined-
   system disjunction property from the two-sided seed) — documented as the one outstanding
   obligation, NOT stubbed with `sorry` (zero-debt: do not add `sorry`; leave it unproven-and-
   unstated-as-theorem, or scope a dedicated research sub-task). Spawn a research sub-task with a
   literature pass targeting a **cut-free / nested-sequent** route (Marin–Morales–Straßburger 2021
   for constructive S5; repair Pacheco 2024 Lemma 16/17), not a direct Hilbert argument.

This banks the tractable parts of Phase 4 while making the open frontier explicit and small.

### Not recommended

- **Direct Hilbert proof of obligation 3 now** — research-grade, no semantic witness, multi-day-to-
  open; do not schedule as a plan phase.
- **Landing obligation 1 alone as "progress"** — it only exposes the load-bearing seed-exclusion
  sooner; do not present it as advancing completeness (report 02 §5.3).
- **Semantic / soundness-based seed-exclusion** — circular (presupposes the truth lemma) and, more
  fundamentally, has no separating model (report 02 §2).
- **`Sum.elim id id` signature-collapse** — `cross1`'s image `□B → B` is not a `CS5ModalAxiom`
  instance, so the retraction is not schema-compatible (plan Phase-4 blocker, dead_ends).

### Recommended decision

Present the user with Route A (shippable, ~4 bounded lemmas, first-gate `cs5_derives_idb`) vs.
Route Native-incremental (mandate-preserving, banks obligations 1–2, isolates the open lemma).
**If the objective is a landed CS5 completeness theorem, Route A is the tractable path and its
first action is proving `CS5 ⊢ idb`.** If the native-Hilbert mandate is non-negotiable, Route
Native-incremental is the maximal safe progress; the completeness theorem then waits on a dedicated
research result.

## 5. Grounding — every claim in this report is tied to live evidence

- Build: `lake build` of the five modules → 731 jobs, exit 0 (this session).
- Sorry census: `grep` over the four scope files + `CS5Completeness.lean` → docstring prose only.
- Absent declarations: `grep 'theorem cs5_completeness|cs5_box_backward|cs5_soundness_completeness'`
  over all of `Cslib/` → only `Labelled/Completeness.lean:130` (Route C); nothing native.
- `idb` absence: `grep 'idb' Cslib/Logics/Modal/` → intuitionistic/minimal only, none in
  Constructive/CS5.
- Driver hypotheses: `CKExtension.lean:246–262` (`ckvalidFC_completeness`, the `realize` witness).
- Landed lemma lines: `CS5.lean:352/539/686/712`, `IS5.lean:364`, `CS5Completeness.lean:92–157`.
- Archived deps: `specs/archive/{508,509,517}_*` present; none in live `specs/state.json`.
- Prior analysis reused (not re-litigated): report 02 §2 (no semantic witness), §3 (three failed
  native attempts), §4 (route evaluation). This report verifies its factual premises against
  current source and adds the concrete Route-A lemma list.
