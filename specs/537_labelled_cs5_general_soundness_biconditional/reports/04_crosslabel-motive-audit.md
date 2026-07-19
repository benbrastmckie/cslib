# Research Report 04: Cross-Label `efq`/`orE` Motive — Divergence Audit

- **Task**: 537 — general labelled CS5 soundness `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ`
- **Agent**: cslib-research-hard-agent (hard mode; divergence audit of the Phase 8 `[BLOCKED]` finding)
- **Session**: sess_1784471495_4fb1e9
- **Scope**: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` (audit only — no proof code written)
- **Reference grounding**: Tier 1 (literature-backed). BibKeys **VERIFIED** in `references.bib`:
  `Simpson1994` (`:86`, `@phdthesis`), `MarinMoralesStrassburger2021` (`:962`, `@article`).
- **Zero-debt carried**: no `sorry`, no new axiom, `cs5FCIncest` unweakened, no regression of the 14 landed assets.
- **Sources READ this pass**: Deduction.lean, Syntax.lean, Forcing.lean, CS5Canonical.lean (`cs5FCIncest`/`cs5Incest`/`cs5_soundness_derivable_incest`), CKExtension.lean (`CKValidFC`), Soundness.lean (all 14 landed assets), handoff `08`, reports `02`/`03`, Simpson chunks 0151–0158, MMS index entry. Two new facts **machine-verified axiom-free** via `lean_run_code`.

---

## Verdict (read first)

1. **`nik_TS5_soundness` is TRUE and provable.** The Phase-8 countermodel refutes the *naive `∀ρ`
   motive only*, **not** the theorem (Simpson Thm 8.1.4, tree case, of which `NIKTheorem`-over-`Graph.trivial`
   is an instance). The theorem holds because falsum is never derivable from the empty root context
   (`nik_TS5_consistent`, landed); the induction just cannot *see* that fact locally.

2. **The task's central hypothesis — "derivation graphs are `TClosure`-connected, so `TClosure TS5 G.R`
   is total on `G.X`" — is REFUTED (H4).** It is FALSE as a structural invariant. `NIK.boxI`
   (Deduction.lean:297) and `NIK.diaE` (Deduction.lean:309) place **no** `x ∈ G.X` side-condition on
   their edge source `x`, and `Graph.addEdge` sets `X := G.X ∪ {x, y}` (Syntax.lean:149). So `boxI`/`diaE`
   applied at a **dangling** `x ∉ G.X` (e.g. one produced by a cross-label `efq`/`orE`) creates a **new,
   `G.R`-disconnected component `{x, y}`**. `IsDerivationForest` (Soundness.lean:743) *correctly* omits a
   connectivity conjunct; it **cannot** be strengthened to connectivity because connectivity genuinely fails.
   **The connectivity-lemma path (Q4 option A) is therefore not viable.**

3. **The residual obstruction is `efq` alone, and it is exactly Simpson's own "non-tree excursion"
   difficulty.** `orE`, contrary to the handoff, is discharged by a straightforward existential motive
   (single-branch, no coordination) — see Finding 4. The one genuinely hard case is `efq` where `⊥` is
   derived at a label in a component **disconnected from** the conclusion label. Simpson 8.1.2
   (chunk 0158) states precisely that *direct* `N(𝒯)` natural-deduction soundness has "unavoidable
   excursions through non-tree consequences" and recommends the `L_m` sequent system or the Hilbert route.

4. **Recommendation.** Two paths, ranked by risk:
   - **(Primary, lowest risk) Strategy 3 — Hilbert-labelled adequacy bridge.** Obtain `nik_TS5_soundness`
     as a corollary of the **already-landed, sorry-free** `cs5_soundness_derivable_incest`
     (CS5Canonical.lean:373). Sidesteps the induction and its `efq` excursion entirely. Endorsed by
     Simpson 8.1.2 itself and by the 4th-dispatch GATE-C.
   - **(Alternative, higher risk) Direct route via an existential-teleport motive** (Q4 option B, corrected).
     Closes `orE` and `efq`-with-`y∉dom` cleanly, reusing all 14 landed assets for the modal cases, but
     **still needs a genuinely new auxiliary "⊥-locality" lemma** to close `efq`-with-`⊥`-in-a-disconnected
     component. Concrete sequence in §"Revised Phase 8".

The theorem is not false and does not need a different *statement*; it needs a different *proof architecture*
than the connectivity-forest-induction of plan v3.

---

## Source-to-Implementation Mapping (Tier 1)

| Source Claim | BibKey | Lean Target / Anchor | Translation Notes |
|---|---|---|---|
| Thm 8.1.4 soundness holds **for `G` a tree**; general (non-tree) soundness FAILS (Fig 8-1), chunk 0151 | `Simpson1994` | `nik_TS5_soundness` (goal) | `NIKTheorem` is theoremhood over `Graph.trivial` (a tree) → the provable case. |
| §8.1.2: direct `N(𝒯)` soundness has "**excursions through non-tree consequences [that] are unavoidable**"; fix = `L_m(𝒯,∅)` or Hilbert, chunk 0158 | `Simpson1994` | Diagnoses the `efq` residual below; motivates Strategy 3 | The obstruction is about consequences with open assumptions over non-tree graphs — exactly what dangling `efq`/`orE` + `boxI`-at-dangling-`x` produce. |
| Soundness induction copies non-modal cases "mutatis mutandis from Thm 4.5.1"; ⊥/∨ not re-derived in Ch. 8, chunk 0156 | `Simpson1994` | `efq`/`orE` cases of the main induction | In Simpson's **bivalent** semantics `[x]⊨⊥` is never true, so `(⊥E)` is **vacuously** sound. CSLib's **fallible** `CKForces` (per-world `botForces`) breaks that vacuity — the source's argument does not transfer verbatim. |
| Lifting Lemma 8.1.3 (tree-only), chunks 0153–0155 | `Simpson1994` | `boxI_lift` (Soundness.lean:1307), landed via `raise_subtree`/`boxI_lift_ancestor` | Only `boxI` needs it; F1=`cs5FCIncest_lift`, F2=`cs5FCIncest_raise`, both landed. |
| Def 5.1: `G`-interpretation validates only **explicit** relational atoms `xRy` | `MarinMoralesStrassburger2021` | raw edge-cond `∀ a b, G.R a b → r (ρa)(ρb)` (Soundness.lean:494) | The correct invariant is **raw** edge-cond, never a `TClosure` clique — landed correctly in `box_iff_TClosure`. |
| Thm 7.1 klmn-incestuality; Thm 7.2 direct birelational soundness | `MarinMoralesStrassburger2021` | `cs5Incest` (CS5Canonical.lean:234), `cs5_axiom_sound_incest` | CS5 = `k=l=1,m=n=0` instance; direct birelational route exists (existence proof for Strategy 3's feasibility). |

---

## Findings (each grounded in the exact Lean source)

### Finding 1 — Q1: `efq`/`orE`'s conclusion label is genuinely unconstrained; it need NOT be in `G.X`

`NIK.efq (G Γ) (x y : Label Atom) (A) (h : NIK 𝒯 G Γ (x ∶ .bot)) : NIK 𝒯 G Γ (y ∶ A)`
(Deduction.lean:252) imposes **no** relation between `x` and `y` and **no** `y ∈ G.X`. Likewise
`NIK.orE … (y : Label Atom) … : NIK 𝒯 G Γ (y ∶ C)` (Deduction.lean:277). Compare `boxE`/`diaI`
(Deduction.lean:289,301), which carry `hR : TClosure 𝒯 G.R x y`, and `boxI`/`diaE`
(Deduction.lean:297,309), whose fresh `y` enters `G.X` via `G.addEdge x y`. So `efq`/`orE` are the
**only** rules that can introduce a label that is in neither `G.X` nor `ctxLabels Γ`. **A derivable
sequent's conclusion label is NOT necessarily a graph node.** (At the *root*, `NIKTheorem`
(Deduction.lean:316) does fix the conclusion label to `(Graph.trivial).nonempty.choose ∈ G.X`, but
intermediate sub-derivations reached by the induction need not.)

### Finding 2 — Q2: the derivation graph is NOT `TClosure`-total/connected — the invariant genuinely fails

The module docstring's "Refined analysis" §1 claim ("`G` is always connected … `TClosure TS5 G.R a b`
holds for every `a,b ∈ G.X`") is **false as an induction invariant**, and this is the crux the audit
was asked to stress-test.

- `Graph.addEdge` (Syntax.lean:148–150): `X := G.X ∪ {x, y}`, `R := fun a b => G.R a b ∨ (a=x ∧ b=y)`.
- `NIK.boxI`/`NIK.diaE` call `G.addEdge x y` with **no** `x ∈ G.X` premise (Deduction.lean:297,309).
- Therefore, if `boxI`/`diaE` fires at a **dangling** `x ∉ G.X` (a label first produced by a cross-label
  `efq`/`orE`), `G.addEdge x y` adjoins the pair `{x, y}` as a **fresh component with no `G.R`-path to the
  rest of `G.X`**. The resulting graph is a genuinely **disconnected** forest.

`IsDerivationForest` (Soundness.lean:743) packages `X.Finite ∧ graded-rank ∧ unique-parent` and is
provably preserved (`forest_trivial`, `forest_addEdge_fresh`) — but **none of its three conjuncts implies
connectivity**, and §"raise_subtree" (Soundness.lean:724) already notes the arbitrary-`Graph` `boxI_lift`
is false. **Connectivity cannot be threaded as an invariant because it is not preserved.** Hence
"`TClosure TS5 G.R` total on `G.X`" is unavailable to the induction, and Q4 option A collapses.

### Finding 3 — Q3 (positive, machine-verified): within a single component, `botForces` propagates BIDIRECTIONALLY, so a *connected* `efq` would discharge

This is the one place the connectivity intuition is *correct*, and it is now machine-checked
(`lean_run_code`, `#print axioms` = "does not depend on any axioms"):

```
-- from cs5Incest (r w u → ∃ u', u ≤ u' ∧ r u' w) + explosion conds bf_uc, bf_r:
bot_backward : bot u → r w u → bot w            -- hincest hwu ⇒ u ≤ u' ∧ r u' w;  bf_r (bf_uc … hu) …
bot_iff_edge : r w u → (bot w ↔ bot u)          -- forward = bf_r; backward = bot_backward
```

`bf_r`/`bf_uc` are exactly `CKValidFC`'s explosion + upward-closure conditions (CKExtension.lean:91,93);
`hincest = cs5Incest` (CS5Canonical.lean:234, the 5th `cs5FCIncest` conjunct, CS5Canonical.lean:260).
Consequently `botForces` is an **equivalence-invariant across any `r`-connected region**, and — by a
`TClosure`-induction structurally identical to the landed `box_iff_TClosure` (Soundness.lean:492: base via
raw `hedge`, `refl`=`Iff.rfl`, `symm`=`Iff.symm`, `trans`=`Iff.trans`, `eucl` vacuous since `Five ∉ TS5`)
— one obtains `bot_iff_TClosure : TClosure TS5 G.R x y → (botForces (ρx) ↔ botForces (ρy))` for a raw-edge-cond
`ρ`. Combined with `ckforces_of_exploding` (Forcing.lean:172, `botForces w → CKForces w A` for all `A`), an
`efq` whose `x,y` lie in the **same component** discharges cleanly.

**But** by Finding 2 the induction cannot guarantee `x,y` are in the same component (or that `y ∈ G.X` at
all). So Finding 3 closes only a *sub-case*, not the constructor.

### Finding 4 — `orE` is NOT part of the obstruction under an existential motive (handoff overstated it)

Under the existential motive `M(G,Γ,φ) := ∀ρ, edge-cond → Γ-cond → ∃ρ' (agree on G.X ∪ ctxLabels Γ) ∧
CKForces (ρ' φ.lbl) φ.prop`, the `orE` case (Deduction.lean:277) closes with **no coordination**: from the
major-premise IH one gets `CKForces (ρ'_or x) A ∨ … B`; case-split; feed the chosen minor premise
(`(x∶A)::Γ` resp. `(x∶B)::Γ`) its own IH with `ρ := ρ'_or` (which satisfies the extended Γ-cond because
`CKForces (ρ'_or x) A` holds), and return that single branch's `ρ'`. Only **one** branch is used, so the
two branches' interpretations never need to agree. `efq` is therefore the sole residual.

### Finding 5 — Q4: the residual `efq` case, and why neither hypothesised fix closes it uniformly

Take the existential motive of Finding 4. The `efq` case (premise `x∶⊥`, conclusion `y∶A`) splits:

- **`y ∉ G.X ∪ ctxLabels Γ` (dangling).** From the premise IH pick `ρ''` (agrees with `ρ` on the domain)
  with `botForces (ρ'' x)`. Set `ρ' := fun z => if z ∈ dom then ρ z else ρ'' x`. Then `ρ'` agrees with `ρ`
  on the domain, and `CKForces (ρ' y) A = CKForces (ρ'' x) A` holds by `ckforces_of_exploding`. **Closes.**
- **`y ∈ G.X ∪ ctxLabels Γ` (pinned).** `ρ' y = ρ y` is forced. We hold `botForces (ρ'' x)` with `ρ''`
  agreeing with `ρ` on the domain. If `x ∈ dom` **and** `x,y` are in one component: Finding 3 propagates
  `botForces` to `ρ y`, then `ckforces_of_exploding`. **Closes.** Otherwise (`x ∉ dom`, or `x,y` in
  different components) `botForces` sits at a point `r`-disconnected from `ρ y`, and — by the Phase-8
  countermodel, which is a genuine `cs5FCIncest`+`CKValidFC` model — **it does not reach `ρ y`. Does NOT
  close.**

The stuck sub-case is exactly "`⊥` derived in a region disconnected from the conclusion label" — Simpson's
"non-tree excursion" (chunk 0158). Closing it inside the direct induction requires a **new** auxiliary
invariant of the shape *"if `NIK G Γ (x∶⊥)` is derivable and the sequent's live labels are `r`-disconnected
from `x`, then some domain label already explodes"* — a ⊥-locality / cut-style property that is itself
re-plan-scale, not a skeleton transcription. This is why the handoff correctly flagged the existential
reformulation as "a substantial redesign, not a transcribe-the-skeleton step."

### Finding 6 — Q5: how the published sources handle `⊥E`/`∨E` soundness

- **Simpson (chunks 0156, 0158).** Ch. 8 soundness is an induction over derivations, restricted to `G` a
  **tree**, and treats only the lifting-lemma cases explicitly; ⊥/∨ are inherited "mutatis mutandis from
  Thm 4.5.1." In Simpson's **bivalent birelational** semantics `[x]⊨⊥` is impossible, so `(⊥E)` is
  **vacuously** sound regardless of `y` — no propagation is needed and the cross-label freedom is harmless.
  Simpson explicitly says the *direct* `N(𝒯)` route (the one CSLib transcribes) is "more difficult"
  precisely because of non-tree excursions, and routes soundness through `L_m` or Hilbert.
- **MMS 2021 (Def 5.1; Thm 5.3/7.2).** Fully-labelled *sequent* system; `G`-interpretations validate only
  explicit atoms; soundness is by contradiction with frame-supplied witnesses mapped to **fresh** labels.
  Their `⊥`/`∨` handling is likewise not a fallible-world propagation.

**Neither source proves the fallible-world (`CKForces`/`botForces`) cross-label `⊥E` soundness that CSLib
needs** — because neither uses a per-world `botForces`. CSLib's fallible semantics is a deliberate deviation
(Soundness.lean:74–92), and it is exactly this deviation that reopens the `efq` gap the sources close by
bivalence. **This corroborates that the direct-route `efq` obstruction is real, not an implementation miss.**

---

## Revised Phase 8 — concrete sequences for the planner

### Path P3 (RECOMMENDED, lowest risk): Hilbert-labelled adequacy bridge (Strategy 3)

Reuses the landed, sorry-free Hilbert-side soundness; the 14 forest/lifting assets are **not needed on the
critical path** (they remain valid, unregressed, and reusable if the bridge is later inlined).

- **Phase 8a — Adequacy bridge `nik_TS5_to_hilbert : NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ`.**
  Simpson Ch. 6 labelled↔Hilbert adequacy, specialised to theoremhood over `Graph.trivial`. This is the
  "THE TRUE CRUX" bridge task 517 deferred; size it as its own phase (est. 150–300 lines, its own research
  pass on Simpson Ch. 6). **Main risk lives here.**
- **Phase 8b — Corollary.** `nik_TS5_soundness := fun h => cs5_soundness_derivable_incest
  (nik_TS5_to_hilbert h)` using `cs5_soundness_derivable_incest` (CS5Canonical.lean:373), which is already
  `CKValidFC cs5FCIncest`-valued. ~3 lines.
- **Phase 8c — Regression gate.** `lake build` green; `lean_verify nik_TS5_soundness` (no `sorryAx`);
  `cs5_completeness`, `nik_TS5_consistent`, `cs5_soundness_derivable_incest` unchanged; `cs5FCIncest`
  unweakened. Retire the stale `INTRACTABLE`/GATE-C docstring notes.

### Path PD (ALTERNATIVE, higher risk): direct existential-teleport induction

Keeps the direct route and reuses all 14 landed assets for the modal cases. New phases:

- **Phase 8.1 — `bot_backward` + `bot_iff_edge` + `bot_iff_TClosure`.** Land Finding 3's two machine-verified
  lemmas plus their `TClosure {T,B,Four}` transport (copy the `box_iff_TClosure` skeleton, Soundness.lean:492).
  LOW risk (verified axiom-free this audit).
- **Phase 8.2 — the existential-monotone soundness motive** `M(G,Γ,φ) := ∀ρ, (∀ a b, G.R a b → r(ρa)(ρb)) →
  (∀ψ∈Γ, CKForces (ρ ψ.lbl) ψ.prop) → ∃ρ', (∀z, ρ z ≤ ρ' z) ∧ (agrees with ρ on G.X ∪ ctxLabels Γ) ∧
  CKForces (ρ' φ.lbl) φ.prop`. Discharge: the 8 label-local propositional constructors by **sequential
  premise threading + `ckforces_persistence`** (Forcing.lean:122) at shared labels (monotone `ρ'≥ρ` makes
  earlier forcings persist); `boxE`/`diaI` via `box_iff_TClosure`/`dia_iff_TClosure` + `box_gives_here`;
  `boxI` via `boxI_lift` (Soundness.lean:1307); `diaE` via `le_refl` (no lift); `orE` via Finding 4.
  MEDIUM risk (coordination bookkeeping, but every ingredient is landed).
- **Phase 8.3 — the `efq` ⊥-locality lemma (THE hard, novel phase).** Prove the auxiliary invariant of
  Finding 5 that closes `efq`-with-disconnected-`⊥`. Candidate shape: strengthen `M` to also output, when
  `φ.prop = ⊥`, a **domain** witness `∃ z ∈ G.X ∪ ctxLabels Γ, botForces (ρ' z)`; prove it survives every
  constructor. **HIGH risk / genuinely open** — this is the direct analogue of Simpson's non-tree-excursion
  difficulty and may itself require normalization/cut infrastructure. Gate it: if unprovable within budget,
  **pivot to Path P3** rather than force a `sorry`.
- **Phase 8.4 — assemble + regression gate** as in Phase 8c.

**Do not** attempt the connectivity-lemma path (Q4 option A): Finding 2 proves connectivity is not an
invariant. **Do not** weaken `efq`/`orE` to require `y ∈ G.X` — completeness needs the cross-label
disconnected form (Deduction.lean:245–253 docstring; `PrimeLemma.consistency_of_maximal`).

---

## Adversarial Self-Verification (H4)

I tried hard to refute my own two load-bearing negative claims (connectivity fails; the `efq` residual is
real) and my positive claim (bidirectional `botForces`).

| Claim | Source / Counterexample | Verdict |
|---|---|---|
| `botForces` propagates BACKWARD along an `r`-edge under `cs5FCIncest`+explosion | `bot_backward`/`bot_iff_edge` compile, `#print axioms` = "does not depend on any axioms" (`lean_run_code`, this audit) | **CONFIRMED (machine-verified)** |
| Real derivation graphs are connected (task hypothesis) | `NIK.boxI`/`diaE` have NO `x ∈ G.X` premise (Deduction.lean:297,309); `addEdge X := G.X ∪ {x,y}` (Syntax.lean:149) ⇒ `boxI` at dangling `x` makes a disconnected `{x,y}` component | **REFUTED** — connectivity is not preserved; `IsDerivationForest` rightly omits it |
| "`TClosure TS5 G.R` is total on `G.X`" (module docstring §Refined-analysis §1; task Q2) | Same as above — total only within one component, and there can be ≥2 | **REFUTED** as an induction invariant |
| Two derivation nodes can be disconnected AND both in `G.X` | `boxI`-at-dangling-`x` component `{x,y}` vs the root component; both are subsets of `G.X` after the edge | **CONFIRMED possible** |
| Can `efq`/`orE` introduce a label NOT in `G.X`? (task refutation target) | Constructor types (Deduction.lean:252,277) — `y` free, no `G.X` membership | **CONFIRMED yes** — dangling labels are real |
| `orE` has "the identical gap" as `efq` (handoff `08`) | Existential motive closes `orE` single-branch, no coordination (Finding 4) | **REFUTED** — only `efq` is residual |
| `efq`-with-`y∉dom` is unclosable | Teleport `ρ' y := ρ'' x` (exploding) + `ckforces_of_exploding` (Forcing.lean:172) | **REFUTED** — that sub-case DOES close |
| `efq`-with-`⊥`-disconnected-from-`y∈dom` is the true residual | Phase-8 countermodel is a valid `cs5FCIncest`+`CKValidFC` model; `botForces` cannot cross a disconnected region (Finding 3 needs an `r`-path) | **CONFIRMED residual** |
| The residual is a mere engineering gap | Simpson 8.1.2 (chunk 0158): direct `N(𝒯)` soundness has "unavoidable non-tree excursions", needs `L_m`/Hilbert | **CONFIRMED it is a KNOWN hard case**, not an implementation miss |
| The THEOREM `nik_TS5_soundness` is false | `nik_TS5_consistent` (landed) + Simpson Thm 8.1.4 tree case; countermodel refutes only the naive motive | **REFUTED — theorem is TRUE** |
| Strategy 3 is available zero-debt | `cs5_soundness_derivable_incest` (CS5Canonical.lean:373) is landed sorry-free and already `CKValidFC cs5FCIncest`-valued; only the Ch.6 bridge is missing | **CONFIRMED** (bridge is the remaining work) |

**Challenges raised and resolved.**
- *"Report 02 machine-verified the direct route as ~80–85% achievable — does that contradict this audit?"*
  No. Report 02 verified the **modal** cases (`boxE`/`diaI`/`boxI`) and *assumed* the propositional cases
  were "verbatim from `nik_soundness_onePoint`" (report 02 §4(C)). That assumption is exactly what Phase 8
  falsified: the one-point model (`World := Unit`) makes every `ρ` constant, masking the cross-label `efq`
  subtlety. Report 02's 14 assets are correct and reused here; its residual-risk estimate simply missed `efq`.
- *"Could a `bot_iff_TClosure` alone close `efq`?"* Only when `x,y` share a `TClosure` witness, i.e. one
  component. Finding 2 shows that witness is not guaranteed. So no.
- *"Is the disconnected-`⊥` derivation actually constructible, or vacuous?"* For the *root* theorem it is
  semantically vacuous (root context is empty ⇒ `⊥` is not derivable anywhere ⇒ `nik_TS5_consistent`). But
  the *induction* quantifies over all sub-derivations and cannot assume root-consistency locally — which is
  the entire reason a local motive fails and Simpson routes around it. Verified against the constructor
  semantics, not assumed.

**Uncertain claims (confidence).**
- Path PD Phase 8.3 (`⊥`-locality lemma) is closable in Lean at planned effort: **~35%**. It is the
  genuine open piece; I could neither complete it nor find a decisive obstruction this pass.
- Path P3 Phase 8a (Ch. 6 adequacy bridge) is closable: **~70%** — it is "known-shape" proof-theory
  (Simpson Ch. 6) rather than an open question, but it is substantial and was deferred by task 517.

No fundamental flaw invalidated the audit's own reasoning; the machine-checked facts stand. A
`## Revised Direction` restart was **not** triggered — the finding is a proof-architecture pivot
(connectivity → bridge/existential), not a re-statement of the theorem.

---

## Memory Candidates

1. **CSLib labelled soundness — connectivity is NOT a derivation-graph invariant.** `NIK.boxI`/`NIK.diaE`
   (Deduction.lean:297,309) carry no `x ∈ G.X` side-condition, and `Graph.addEdge` sets `X := G.X ∪ {x,y}`,
   so `boxI`/`diaE` applied at a dangling `efq`/`orE` label create a `G.R`-disconnected component. Any
   soundness proof relying on "`TClosure TS5 G.R` total on `G.X`" is unsound — `IsDerivationForest`
   correctly omits connectivity because it is not preserved.
2. **`botForces` is `r`-connectivity-invariant under `cs5FCIncest`+`CKValidFC`** (machine-verified,
   axiom-free): forward via `bf_r`, backward via `cs5Incest` + `bf_uc` + `bf_r` (`bot_backward`). It
   transports over the `TClosure {T,B,Four}` class exactly like the landed `box_iff_TClosure`. This closes
   the *connected* `efq` sub-case but not `efq` in general.
3. **Fallible-world (`CKForces`/`botForces`) cross-label `⊥E` soundness is a genuinely hard case**, matching
   Simpson 8.1.2's "non-tree excursions unavoidable" (direct `N(𝒯)` needs `L_m`/Hilbert). Simpson/MMS both
   dodge it via bivalence / explicit-atom sequents; CSLib's fallible-world deviation reopens it. Prefer the
   Hilbert adequacy bridge (`cs5_soundness_derivable_incest`, CS5Canonical.lean:373) over a direct induction
   for this family.

## References

- [Simpson1994] A. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*, Ch. 8
  (chunks 0151–0158): §8.1.2 Soundness, Lemma 8.1.3, Thm 8.1.4, Fig 8-1; §8.1.2's `L_m`/Hilbert remark.
- [MarinMoralesStrassburger2021] Marin, Morales, Straßburger, *A fully labelled proof system for
  intuitionistic modal logics*, JLC 31(3):998–1022: Def 5.1 (`G`-interpretation on explicit atoms),
  Thm 5.3/7.1/7.2.
