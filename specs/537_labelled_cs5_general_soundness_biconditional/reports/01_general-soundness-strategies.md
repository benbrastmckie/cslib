# Research Report: General Labelled CS5 Soundness — Three-Strategy Feasibility

- **Task**: 537 — prove `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ`
- **Agent**: cslib-research-hard-agent (hard mode; `--lit` active)
- **Session**: sess_1784471495_4fb1e9
- **File scope**: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`
- **Reference grounding tier**: Tier 1 (literature-backed; BibKeys `Simpson1994`, `MarinMoralesStrassburger2021`)
- **Zero-debt constraints carried**: no `sorry`, no new axiom under `Cslib/`, do not weaken `cs5FCIncest`, do not regress landed completeness/anti-vacuity.

## Summary Verdict (read first)

The direct route is **genuinely open**, and this dispatch's independent analysis *sharpens* the
prior three-dispatch assessment rather than overturning it: the obstruction reduces to a single
isolatable lemma (exact symmetry of `r` on `cs5FCIncest` models) **plus** a second, previously
under-weighted wall (box-introduction against adversarial successors). Ranked recommendation:

1. **Strategy 1 as a time-boxed DECISIVE probe with a hard pivot gate** (cheapest; highest
   information value; most likely to either crack the crux or produce a countermodel that kills
   the direct route outright). One bounded phase, explicit no-loop gate.
2. **Strategy 3 (Hilbert-labelled bridge) as the pre-planned fallback skeleton** — obtains
   soundness as a one-line corollary of the *already-landed* `cs5_soundness_derivable_incest`,
   but requires building Simpson's Chapter 6 adequacy bridge (rated ~25-30% by parent task 517).
3. **Strategy 2 (L_m modified sequent system) last** — highest new-infrastructure cost, no
   landed reuse, and depends on Simpson §8.1.2 material that is **not in the live corpus**.

## Source-to-Implementation Mapping (Tier 1)

| Source Claim | BibKey | Lean Target | Translation Notes / Status |
|--------------|--------|-------------|----------------------------|
| Thm 8.1.4 biconditional (labelled), soundness direction (2⟹1) | `Simpson1994` | `nik_TS5_soundness` (goal) | Stated by Simpson **only for `G` a tree**; CSLib's `G` is a connected tree. [UNVERIFIED against live corpus — corroborated by in-repo transcription in `Soundness.lean` docstring + `Completeness.lean:23`] |
| Lifting Lemma 8.1.3 | `Simpson1994` | `cs5FCIncest_lift` (`Soundness.lean:268`, LANDED) single-edge case only | Simpson's proof uses birelational `F1`/`F2`; CSLib target `CKForces` is built **without** `F1`/`F2`, so verbatim transcription is unavailable. [UNVERIFIED against live corpus] |
| §8.1.2: "easiest proof uses the modified sequent system `L_m(𝒯,∅)`" | `Simpson1994` | (Strategy 2) new `L_m` system — **not in repo** | The stated fix for the non-tree-excursion problem. [UNVERIFIED against live corpus — no chunk retrievable this session] |
| Thm 6.2.1 adequacy `IK+Ax(𝒯) ⟺ N□◇(𝒯)`, direction labelled⟹Hilbert | `Simpson1994` | (Strategy 3) `NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ` — **not in repo** (`Adequacy.lean` absent) | Parent report 11 Q4 rates full bridge ~25-30%; C5 (`pathSpine`/`addChild`) flagged "THE TRUE CRUX". [UNVERIFIED against live corpus — corroborated by `Completeness.lean:23-24`, report 02, report 11] |
| Thm 7.1 incestuality frame conditions (`k=l=1,m=n=0`) | `MarinMoralesStrassburger2021` | `cs5Incest` (`CS5Canonical.lean:234`, LANDED) | The `bDia`-specific Marin instance; already the basis of `cs5FCIncest`'s fifth conjunct. [UNVERIFIED against live corpus — corroborated by `CS5Canonical.lean:246-253` transcription] |

**BibKey verification status**: Both `Simpson1994` (`references.bib:86`, `@phdthesis`, Edinburgh
1994, ECS-LFCS-94-308) and `MarinMoralesStrassburger2021` (`references.bib:962`, `@article`, JLC
31(3):998-1022) are **VERIFIED present in `references.bib`**. The *citation keys* are therefore
sound. The *full-text corpus*, however, is unavailable this session: `literature-search.sh` for
both works returned `{"results": [], "degraded": true}`, matching the `.lit-briefing.txt` "not
found in global index — skipping" warnings. Consequently every specific theorem/lemma number
above is marked **[UNVERIFIED against live corpus]** and grounded instead on the **durable
in-repo anchors** (landed, CI-green docstrings transcribed from those chunks during task 517).
No lemma numbers or page references were invented.

## Findings: the obstruction, grounded in the actual Lean API

### The frame condition (read from source, `CS5Canonical.lean:255`)

`cs5FCIncest r` is the conjunction of exactly five clauses:

1. `hrefl : ∀ w, r w w` — **exact reflexivity**
2. `htrans : ∀ {w u t}, r w u → r u t → r w t` — **exact (plain) transitivity**
3. `hfour : ∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t` — **raised** witness `v ≥ w`
4. `hsymbox : ∀ {w u u'}, r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t` — **raised** witness
5. `hincest` (`cs5Incest`, `:234`): `∀ {w u}, r w u → ∃ u', u ≤ u' ∧ r u' w` — **raised** back-witness `u' ≥ u`

Decisive structural fact: clauses 1-2 have `∀`-only (exact) conclusions; clauses 3-5 conclude an
**existentially-raised** witness, never the exact original point. There is **no exact-symmetry
conjunct**.

### The closure is TOTAL, not tree-adjacency (`Deduction.lean:195`, `Context.lean:313`)

`TS5 = {T, B, Four}`. `TClosure TS5 R` therefore has constructors `base`, `refl` (T), `symm` (B),
`trans` (Four) — i.e. it is the **reflexive-symmetric-transitive closure = equivalence closure**.
`Graph.trivial` is a single node and `Graph.addEdge` always attaches a fresh label to a present
one (`Syntax.lean:123,148`), so `G` is a **connected** (tree) graph throughout any derivation. The
equivalence closure of a connected relation is the **total relation on the vertex set**. Hence the
soundness edge-condition `∀ a b, TClosure TS5 G.R a b → r (ρ a) (ρ b)` is **not** "propagate along
tree edges" — it demands the `ρ`-image be an **`r`-clique**.

### The precise, isolated crux (this dispatch's sharpening)

The clean way to state Phase 11.2 (docstring item 4) is a **structural induction over `TClosure`**
proving `raw G.R a b → r (ρa)(ρb)` extends to `TClosure TS5 G.R a b → r (ρa)(ρb)`:

- `base`: given (raw edge interpreted). ✓
- `refl`: needs `r (ρx)(ρx)` = `hrefl`. ✓ **exact, discharged**
- `trans`: needs `r (ρx)(ρz)` from `r (ρx)(ρy)`, `r (ρy)(ρz)` = `htrans`. ✓ **exact, discharged**
- `symm`: needs `r (ρy)(ρx)` from `r (ρx)(ρy)`. Only `hincest` applies, giving `∃ b' ≥ ρy, r b' (ρx)` — **a raised witness, not `r (ρy)(ρx)` exactly.** ✗

So **the entire direct route reduces to one lemma: exact symmetry of `r` on interpreted images of
`cs5FCIncest` models** — equivalently "does `cs5FCIncest r` force `r a b → r b a` on the
finitely-generated substructure?" This is precisely the open question the three prior dispatches
converged on (`Soundness.lean:200-207`).

### Independent probe of the open question (this dispatch)

By hand, chasing the closure from a seed edge `a→b`: `hincest` yields `b' ≥ b` with `r b' a`;
recovering the exact `r b a` needs to "lower" `b'` to `b`, but **no clause supplies downward
closure of `r`** (only `≤`-upward). Attempting an asymmetric countermodel on `ℕ` (e.g. seed
`r 0 1`, take the `hincest` witness as `2` rather than `1` to escape upward) is defeated by
`hsymbox` composed with exact `htrans`: `hsymbox` on a "downward" edge forces a new outgoing edge
that `htrans` chains straight back into the missing reverse edge — collapsing the intended
asymmetry. This reproduces the "finite models keep collapsing into full closure" pattern and
matches the handoff exactly. The escape only survives where there is unbounded `≤`-room above (no
maximal element), which is why **no finite countermodel exists but the general claim stays open**.
This is a **fixpoint/closure-completion** shape, not a fixed-finite-set induction.

### Second wall (under-weighted previously): box-introduction against adversarial `u`

`CKForces … (□A)` unfolds (`Forcing.lean:75`) to `∀ w' ≥ w, ∀ u, r w' u → CKForces u A` — `u` is
**adversarial** (not chosen by the proof). In the `(□I)` case, discharging `y:A` forces the fresh
label's interpretation to be **exactly** the given `u` (persistence is only upward, so a raised
substitute cannot be "rounded back down"). Absorbing that `u` into the clique against every other
label needs `r (ρa) u` exactly for all `a`, which `hfour` again supplies only via a **raised**
`v ≥ ρa` — the same non-terminating cascade. **Consequence: even if the symmetry lemma above
resolves positively, the `(□I)` adversarial-`u` obligation is a second exactness wall that clique
closure alone does not clear.** This materially lowers the expected payoff of Strategy 1 and is the
key adversarial finding of this pass.

### Landed assets available for reuse (verified present, sorry-free per task 517)

- `cs5FCIncest_lift` (`Soundness.lean:268`) — single-edge F2-analogue.
- `ckforces_persistence` (`Forcing.lean:122`) — upward closure of `CKForces`, confluence-free.
- `nik_soundness_onePoint` / `nik_TS5_consistent` (`Soundness.lean:291,365`) — anti-vacuity (must not regress).
- `cs5_soundness_derivable_incest` (`CS5Canonical.lean:373`) — **Hilbert** soundness `Derivable CS5ModalAxiom φ → CKValidFC cs5FCIncest φ` (the Strategy-3 payoff).
- `cs5_completeness` (`Completeness.lean:132`) — must not regress.
- `primeLemma` + Zorn/chain-union machinery (`PrimeLemma.lean`). **Caveat below.**

**FLO reality check (corrects the handoff's optimism):** the "FLO" fresh-labels-only
well-founded reconstruction the handoff hoped to reuse is **NOT on mainline** — mainline
`primeLemma` uses plain `zorn_le₀`, and the FLO apparatus lives only in task-517 `probes/` and
**still carries two open sorries** (`PrimeLemma.lean:47-63`). It is also a *context*-maximalisation
(Lindenbaum) engine for the completeness direction, **not** a relational-clique-closure. So
Strategy 1's "reuse FLO" premise is a **structural analogy** (both are fixpoint-shaped), not a
plug-in; the genuinely reusable primitive is the generic Zorn/chain-union *pattern*, which must be
re-instantiated for a relational-closure poset from scratch.

## Strategy Verdicts

### Strategy 1 — force symmetric/clique closure on generated substructures

- **(a) What must be proved**: the `TClosure.symm` case above — `cs5FCIncest r → r a b → r b a`
  on the finitely-generated interpreted substructure — **and** the `(□I)` adversarial-`u`
  absorption (second wall). Concretely: a fixpoint lemma "smallest `r`-clique containing a finite
  seed, closed under `hincest`/`hfour`/`hsymbox` raised witnesses, is symmetric", then thread it
  through the 12-constructor `NIK` induction (docstring items 1-4).
- **(b) Reuses**: `cs5FCIncest_lift`, `ckforces_persistence`, exact `hrefl`/`htrans` (already
  discharge two of four `TClosure` cases), the generic Zorn/chain-union *pattern* from `PrimeLemma`.
- **(c) Concrete risk**: the symmetry lemma is a **genuine open question** (3 dispatches, no
  proof, no countermodel); AND the second wall may block completion even on positive resolution.
  Two nested obstructions, either fatal.
- **(d) Phase breakdown**: **1 bounded phase** — (1.1) attempt the symmetry/clique-closure lemma
  *or* construct a countermodel, hard budget cap; **decision gate**: closed ⟹ proceed to thread
  through induction (2-3 further phases); countermodel found ⟹ direct route DEAD, pivot to
  Strategy 3; neither within budget ⟹ **do not loop** (already exhausted 3×), pivot to Strategy 3.

### Strategy 2 — formalize Simpson's modified sequent system `L_m(TS5, ∅)`

- **(a) What must be proved**: a new inductive `L_m` sequent system with `𝒯`-closure baked into
  `(⊃L)`/`(⊃R)_m`; a translation `NIK ↔ L_m`; and a fresh soundness proof for `L_m` against
  `CKForces`/`cs5FCIncest`.
- **(b) Reuses**: essentially none — no sequent-calculus infrastructure exists in
  `Cslib/Logics/Modal/` (grep confirms only forcing/deduction/canonical files; no `L_m`, no
  `(⊃L)`/`(⊃R)` machinery). `CKForces` and `cs5FCIncest` are reused only at the very end.
- **(c) Concrete risk**: largest new-infrastructure surface (new system + translation + soundness);
  **source-fidelity risk is severe** — §8.1.2 is [UNVERIFIED against live corpus] and cannot be
  transcribed step-by-step per the Literature Fidelity rule when the source text is unreadable.
- **(d) Phase breakdown**: ~300-600+ lines, re-plan scale: (2.1) `L_m` datatype + rules; (2.2)
  `NIK → L_m` translation; (2.3) `L_m` soundness; (2.4) assemble. High risk at every phase.

### Strategy 3 — Hilbert-labelled adequacy bridge, soundness as corollary

- **(a) What must be proved**: `NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ` (one direction of
  Simpson Thm 6.2.1); then `nik_TS5_soundness` is `cs5_soundness_derivable_incest ∘ bridge` —
  a one-line corollary.
- **(b) Reuses**: **the payoff is a LANDED sorry-free theorem** (`cs5_soundness_derivable_incest`).
  The axis matches: CSLib deliberately chose the TB4 schema (`TS5 = {T,B,Four}`) to avoid the
  unproved constructive `IKT5 ⟺ IKTB4` sub-bridge (`Deduction.lean:82`, `Context.lean:303-306`),
  so that particular sub-gap does **not** bite here.
- **(c) Concrete risk**: `Adequacy.lean` **does not exist** — the bridge is genuinely unbuilt and
  was **deliberately avoided** by task 517 (`Completeness.lean:24`). Parent report 11 Q4 rates the
  full Ch.6 bridge at **~25-30%**, multi-dispatch, with `pathSpine`/`addChild` commutation (C5)
  flagged "THE TRUE CRUX" and the source "deliberately informal". Additional minor fidelity
  assumption: Simpson's 6.2.1 is stated for `N□◇(𝒯)`; identifying it with CSLib's `N_IK` is itself
  part of the [UNVERIFIED] Ch.6 material (report 11 treats them as the same theorem-set). Reopening
  this is a **scope escalation**, not a continuation.
- **(d) Phase breakdown**: re-plan scale mirroring task 517's Track C (C5-C8): (3.1) translation
  scaffolding (`pathSpine`/`addChild`); (3.2) the C5 commutation crux; (3.3) remaining 6.2.1
  direction; (3.4) trivial corollary assembly. Bulk of risk concentrated in (3.2).

## Ranked Recommendation

**Pursue Strategy 1 as a single time-boxed decisive probe FIRST, with a hard pivot gate; pre-plan
Strategy 3 as the fallback skeleton; hold Strategy 2 in reserve.**

Rationale: Strategy 1 is by far the cheapest and carries the **highest information value** — it
terminates in a decisive answer (prove the symmetry lemma ⟹ cheap completion; exhibit a
countermodel ⟹ the direct route is provably dead and the pivot is forced). Its downside (the two
nested walls) is bounded by the budget cap and the explicit no-loop gate that prevents a fourth
thrash. Between the fallbacks, **Strategy 3 outranks Strategy 2** because its payoff reuses a
landed sorry-free theorem (Strategy 2 must additionally *build* a soundness proof), its
source-fidelity risk is confined to one translation rather than a whole new system, and task 517's
report 02/11 already mapped its structure. The planner should size the direct route honestly as a
**probe + gate**, not as a multi-phase build, and pre-authorize the Strategy-3 scope reopening as
the contingency so no further churn is spent re-deciding it.

**Blocked-honesty flag**: if the Strategy-1 probe closes neither the lemma nor a countermodel
within budget, the correct terminal state is `[BLOCKED]` on the direct route with an explicit
recommendation to the user/orchestrator to authorize the Strategy-3 scope reopening — **not** a
`sorry` skeleton and **not** a fourth direct attempt.

## Adversarial Self-Verification (H4)

### Claim Verification Table (divergence audit — second-pass grounding against live Lean API)

Each load-bearing claim was re-checked against the actual in-repo source this pass (not the prior
dispatch's assertions). Source-specific *numbers* from the papers remain `[UNVERIFIED against live
corpus]` (this session's literature retrieval is degraded/unavailable), but every claim resolves to
a definite Verdict against **in-repo, CI-green evidence**. No claim was REFUTED; the report's
analysis and ranking survive the audit intact.

| Claim | Source/Counterexample | Verdict |
|-------|-----------------------|---------|
| 1. `base`/`refl`/`trans` edge-validation cases dischargeable by exact `hrefl`/`htrans` conjuncts (`CS5Canonical.lean:255`). | `CS5Canonical.lean:255-260`: clause 1 = `∀ w, r w w` (exact refl), clause 2 = `∀ {w u t}, r w u → r u t → r w t` (exact plain trans). `TClosure` constructors (`Deduction.lean:198-208`) are `base/refl/symm/trans/eucl`; for `TS5={T,B,Four}` the `eucl` constructor needs `Five ∈ 𝒯` and is unreachable. `refl`↦`hrefl`, `trans`↦`htrans` discharge exactly; `base` is the raw edge. | **CONFIRMED** |
| 2. Entire direct-route crux reduces to `TClosure.symm` case = exact symmetry of `r` on `cs5FCIncest` models. | `Deduction.lean:202` — `symm` is the sole `TS5`-active constructor with no exact `cs5FCIncest` discharge (only raised-witness `cs5Incest`). `Soundness.lean:190-207` documents the exact open question ("no finite countermodel found; positive proof also not completed; genuinely unresolved"). | **CONFIRMED** |
| 3. Second wall: box-introduction (`Forcing.lean:75`) needs the fresh label mapped EXACTLY to adversarial successor `u`, so clique closure is necessary but NOT sufficient. | `Forcing.lean:75`: `.box φ => ∀ w', w ≤ w' → ∀ u, r w' u → CKForces … u φ` — `u` is universally quantified (adversarial, not proof-chosen). API fact exact; the "necessary-but-not-sufficient" conclusion is a sound analytic inference from that binder shape (upward-only persistence, `Forcing.lean:122`). | **CONFIRMED** (API exact; sufficiency-gap is analytic, ~90%) |
| 4. FLO machinery is a context-Lindenbaum engine, off-mainline in `probes/` with two open sorries; only the generic Zorn pattern is reusable. | `PrimeLemma.lean:47-63` scope note: mainline `primeLemma` uses plain `zorn_le₀`; FLO apparatus "remains … in `probes/`" carrying "two open, documented, non-blocking sorries (`flo_succ`'s `redundantEdge` branch; `primeC'_exists_maximal`'s `Maximal`-conjunct half)". `grep` finds no `sorry` token in `PrimeLemma.lean` itself — sorries physically reside in `specs/517_…/probes/` (dir confirmed present). Engine is prime/Lindenbaum context-maximalisation, not relational-clique closure. | **CONFIRMED** (citation `:47-63` is the *documentation* of the sorries; they live in the probe file) |
| 5. Strategy 3 payoff = one-line corollary of landed `cs5_soundness_derivable_incest` (`CS5Canonical.lean:373`); `Adequacy.lean` absent (bridge unbuilt); rated ~25-30%. | `CS5Canonical.lean:373` is exactly the sorry-free `theorem cs5_soundness_derivable_incest : Derivable CS5ModalAxiom φ → CKValidFC cs5FCIncest φ`. Repo-wide `find -iname Adequacy.lean` → NONE (bridge genuinely unbuilt). The ~25-30% figure is a parent-report (11 Q4 / 02) cross-reference, `[UNVERIFIED against live corpus]` but in-repo durable. | **CONFIRMED** (percentage `[UNVERIFIED against live corpus]`, in-repo anchored) |
| 6. Both BibKeys exist in `references.bib` (`Simpson1994` line 86; `MarinMoralesStrassburger2021` line 962). | `grep -n` → `86:@phdthesis{Simpson1994,` and `962:@article{MarinMoralesStrassburger2021,` — exact line matches. | **CONFIRMED** |

**Ranking re-confirmation**: the audit CONFIRMS the report's ranked recommendation unchanged —
**(1) Strategy 1 as a single time-boxed decisive probe with a hard pivot gate; (2) Strategy 3
(Hilbert-labelled adequacy bridge) as pre-planned fallback; (3) Strategy 2 (`L_m` sequent system)
last.** Grounds: Strategy 1's two nested walls are both verified real (Claims 2+3), so its success
probability is genuinely bounded but its information value (decisive lemma-or-countermodel) is
highest and cheapest; Strategy 3's payoff verifiably reuses a landed sorry-free theorem
(Claim 5, `:373`) whereas Strategy 2 must additionally *build* a soundness proof over an
`[UNVERIFIED]` source (§8.1.2) with zero in-repo reuse. No verified fact reorders these. The
zero-debt constraints (no `sorry`, no new axiom under `Cslib/`, no weakening of `cs5FCIncest`, no
regression of parent completeness/anti-vacuity) are carried unchanged; the blocked-honesty flag
(unresolved probe ⟹ `[BLOCKED]`, never a placeholder) stands.

### Narrative challenges (first pass, retained)

I re-read the draft adversarially and challenged each load-bearing claim.

- **Challenge: "the crux is *only* the symmetry lemma" (Strategy 1 (a))** — could Strategy 1 be
  cheaper than stated? **Refuted my own optimism**: I initially framed Strategy 1 as one lemma;
  the `(□I)` adversarial-`u` second wall (`Forcing.lean:75`, exact successor) shows clique closure
  is *necessary but not sufficient*. Revised the verdict to two nested obstructions. This is the
  main correction of the pass and *lowers* Strategy 1's success probability while keeping its
  information value high.
- **Challenge: "reuse the FLO machinery" (handoff's lead)** — verified against `PrimeLemma.lean:47-63`:
  FLO is off-mainline, carries two sorries, and is a context-Lindenbaum engine, not a relational
  closure. **Downgraded** "reuse FLO" to "reuse the generic Zorn pattern". Recommendation revised
  accordingly.
- **Challenge: "is the open question maybe just unattempted, not open?"** — ran an independent
  hand-probe (seed-edge closure chase on `ℕ`); reproduced the `hsymbox`+`htrans` collapse and the
  no-maximal-element escape. Confirms *genuinely open*, consistent with 3 prior dispatches. Not
  refuted; confidence in "open" raised.
- **Challenge: Strategy 3 confidence** — could I be over-pessimistic? Cross-checked the ~25-30%
  against two independent parent artifacts (report 02:426, report 11 Q4:129). Both agree. The one
  favorable nuance (TB4-schema avoids the `IKT5⟺IKTB4` sub-gap) is real and was added, but does not
  lift the C5 "TRUE CRUX" risk. Verdict stands.
- **Challenge: did I miss a fourth strategy?** — report 02:175 floats a **CS5≡IS5 (Pacheco) +
  IS5 canonical model** bypass. Considered and set aside: the task fixes three strategies and that
  route targets the *completeness/Hilbert* connection, not the labelled *soundness* obligation at
  issue; noted here for completeness, not recommended.
- **Analysis-only check**: this report issues concrete feasibility verdicts, an isolated crux
  lemma statement, a decision gate, and a ranked route — not an analysis-only verdict.
- **Zero-debt check**: no recommended route introduces `sorry`, a new axiom, weakens
  `cs5FCIncest`, or regresses landed assets; the blocked-honesty flag routes an unresolved probe to
  `[BLOCKED]`, not a placeholder.
- **BibKey check**: both keys verified in `references.bib`; all source-specific numbers marked
  [UNVERIFIED against live corpus] with in-repo durable anchors; nothing fabricated.

**Uncertain claims (confidence)**: Strategy-1 symmetry lemma is decidable within a bounded probe
(~50%, could be a deep fixpoint argument); Strategy-3 bridge completes (~25-30%, per parent);
`N_IK = N□◇` identification is faithful (~80%, part of unverified Ch.6). No fundamental flaw
surfaced; no `## Revised Direction` restart triggered.

## Memory Candidates

1. `TClosure {T,B,Four}` on a *connected* labelled graph is the **total** relation on its vertices
   (equivalence closure of a connected relation), so labelled-`N(TS5)` soundness needs an
   `r`-clique on interpreted images, not tree-edge propagation. (reusable across TS5/IS5 labelled work)
2. `cs5FCIncest` supplies **exact** reflexivity/transitivity but only **raised-witness**
   symmetry/four/incest; the `TClosure.symm` case of edge-validation is the single unresolved crux,
   and box-introduction's adversarial successor is a second exactness wall. (reusable constraint fact)
3. Labelled-`N(𝒯)` provability connects to Hilbert `Derivable CS5ModalAxiom` **only via** Simpson
   Thm 6.2.1 (`Adequacy.lean`, unbuilt); no other in-framework bridge exists. (reusable scope fact)
