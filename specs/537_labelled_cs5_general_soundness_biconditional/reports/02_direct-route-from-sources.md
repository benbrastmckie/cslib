# Research Report 02: The Direct Route, Grounded in the Actual Primary Sources

- **Task**: 537 — prove DIRECTLY `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ`
- **Agent**: cslib-research-hard-agent (hard mode; literature now readable)
- **Session**: sess_1784471495_4fb1e9
- **File scope**: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`
- **Reference grounding tier**: Tier 1 (literature-backed; BibKeys `Simpson1994`, `MarinMoralesStrassburger2021`)
- **Zero-debt constraints carried**: no `sorry`, no new axiom, do not weaken `cs5FCIncest`, do not regress landed work.
- **Sources actually READ this pass** (not in-repo transcriptions): Simpson 1994 chunks 0151–0160;
  MMS 2021 chunks 0026, 0028, 0043, 0044, 0046, 0048.

## Verdict (read first): the direct route is ACHIEVABLE. The prior [BLOCKED] rested on proving the WRONG lemma.

Reading the real proofs overturns the four-dispatch [BLOCKED] conclusion. Both "walls" dissolve, and
**every mathematical crux below is machine-verified sorry-free and axiom-free** (via `lean_run_code`,
faithful inline restatement of `cs5FCIncest`'s five conjuncts, `#print axioms` = "does not depend on
any axioms"):

- **Wall A** ("exact r-symmetry", the `TClosure.symm` case that blocked 4 dispatches) is an artifact
  of the prior attempts' decomposition. They tried to prove `TClosure 𝒯 G.R x y → r (ρx) (ρy)` — i.e.
  validate each closed edge as an **exact** `r`-edge — whose `.symm` case demands exact symmetry (which
  `cs5FCIncest` does **not** supply, and constructively should not: birelational S5's `R` is not
  symmetric). That intermediate lemma is **both false-in-general and unnecessary**. The correct lemma
  is that the **box/diamond formula is forced equivalently across the whole `TClosure` class**
  (`CKForces (ρx) (□A) ↔ CKForces (ρy) (□A)`), which is provable using ONLY the raised-witness
  conjuncts `hrefl/htrans/hfour/hsymbox/hincest` — **no exact symmetry**. This is exactly the
  fresh-witness / frame-supplies-the-successor technique that both sources use. **Machine-verified**
  (`box_iff_base`, `dia_iff_base`, both axiom-free).
- **Wall B** ("box-introduction adversarial-`u`") is Simpson's standard **Lifting Lemma 8.1.3**, and it
  is needed for **exactly one** `NIK` constructor (`boxI`), not the four the prior report implied. Both
  confluence ingredients are available: **F1** (source-raise) is the already-landed `cs5FCIncest_lift`
  (`Soundness.lean:322`); **F2** (target-raise) is derivable from `cs5FCIncest` in three lines.
  **Machine-verified** (`F1`, `F2`, both axiom-free).

The net result: `nik_TS5_soundness` is a **standard Simpson-8.1.4 tree-soundness induction** whose two
previously-feared cases are now reduced to machine-checked, raised-witness algebra plus one standard
lifting recursion. This is a direct route — **no adequacy bridge, no `sorry`, no new axiom, no weakening
of `cs5FCIncest`**.

## Source-to-Implementation Mapping (Tier 1)

BibKeys **VERIFIED** in `references.bib`: `Simpson1994` (`:86`, `@phdthesis`), `MarinMoralesStrassburger2021`
(`:962`, `@article`). OCR caveat honored: every symbol-heavy claim below is cross-checked against the Lean API.

| Source Claim (chunk read) | BibKey | Lean Target | Translation Notes |
|---|---|---|---|
| Thm 8.1.1: labelled soundness holds **for `G` a tree**; general (non-tree) soundness FAILS (Figure 8-1 counterexample), chunk 0151 | `Simpson1994` | `nik_TS5_soundness` (goal) | CSLib's `NIKTheorem` is theoremhood over `Graph.trivial` — a tree — so it lands squarely in Simpson's provable case. |
| Lifting Lemma 8.1.3 ("any `w ≥ [x]` ... `∃[-]'` with `[x]'=w`, all `[z]'≥[z]`"), chunks 0153–0155 | `Simpson1994` | lifting lemma for `boxI` (item B below); building blocks `cs5FCIncest_lift`=**F1** (landed `:322`), **F2** (new, 3 lines) | Simpson raises the interpretation so the box's `w'` is hit exactly, then maps the fresh child to the adversarial `u`. Only `boxI` needs this. |
| §8.1.2 (□I) case: raise via lifting, then set fresh `[y]'=v` exactly (chunk 0156) | `Simpson1994` | `boxI` case of the main induction | The fresh eigenvariable absorbs the adversarial successor exactly; no exact edge between pre-fixed points. |
| §8.1.3: direct `N(𝒯)` soundness has "unavoidable non-tree excursions"; fix = `L_m` 𝒯-closure OR Hilbert directly (chunk 0158) | `Simpson1994` | Diagnoses why the prior `TClosure→exact-r-edge` decomposition is a dead end | Confirms the prior wall is architecturally real for THAT decomposition — but the box/dia-persistence decomposition sidesteps it. |
| MMS G-interpretation validates only the **explicit** relational atoms `xRy` in the sequent (Def 5.1, chunk 0026) | `MarinMoralesStrassburger2021` | raw edge-cond `∀ a b, G.R a b → r (ρa)(ρb)` (NOT a `TClosure`-clique) | Key: soundness never validates a closed/derived edge as an exact edge. |
| MMS soundness of `⊠gklmn` / `3L`: extend `⟦·⟧` mapping **fresh** labels to frame-supplied existential witnesses (chunks 0046, 0028) | `MarinMoralesStrassburger2021` | box/dia persistence-iff lemmas + `boxI`/`diaE` fresh-label mapping | The exact technique that dissolves Wall A: existential witness absorbed by a fresh label / raised witness, never an exact edge between fixed points. |
| "refl, trans, F1, F2 rules are trivial, as all birelational frames obey the corresponding conditions" (chunk 0028) | `MarinMoralesStrassburger2021` | why `hrefl/htrans/hfour/hsymbox/hincest` discharge the `TClosure` steps | Frame conditions are USED to supply witnesses, never to demand exact edges. |
| Thm 7.1 klmn-incestuality correspondence; Thm 7.2 sound+complete for `IK + gklmn` w.r.t. birelational frames (chunks 0043, 0044) | `MarinMoralesStrassburger2021` | `cs5Incest` (`CS5Canonical.lean:234`, landed) | CS5 is the `k=l=1,m=n=0` instance; MMS prove DIRECT birelational soundness for it — the existence proof that a direct route exists. |

## Findings, grounded in the actual proofs

### 1. Simpson Ch.8: the soundness argument, and what it really needs (chunks 0151–0158)

Simpson's Theorem 8.1.1/8.1.4 soundness (direction 1⟹2) is **an induction on derivations** whose only
non-routine ingredient is the **Lifting Lemma 8.1.3** (chunk 0153): given a `G`-interpretation `[-]`, a
node `x`, and any `w ≥ [x]`, there is another interpretation `[-]'` with `[x]' = w` and `[z]' ≥ [z]` for
all `z`. It is stated and proved **only for `G` a tree** (chunk 0154: "We assume `G` has the form in
Figure 6-1"; the raising is iterated node-by-node using the frame conditions, chunk 0155).

Crucially, the **(□I) case** (chunk 0156) does **not** need an exact edge supplied by the frame
condition. Simpson: "Let `w, v` be any worlds such that `w ≥ [x]` and `wRv`. By the lifting lemma there
is a `G`-interpretation `[-]'` such that `[x]' = w` ... `[-]'` can be trivially extended ... by setting
`[y]' = v`." The adversarial successor `v` is absorbed **exactly** by the **fresh** child `y`; the
*raising* (not any exact edge) is what accommodates `w ≥ [x]`. Answer to sub-question 1: **the frame
condition SUPPLIES the successor during the induction (via lifting + fresh eigenvariable); it does not
demand an exact edge between two independently-fixed points.**

Simpson also states precisely why the *direct* `N(𝒯)` natural-deduction route (the one CSLib's
`boxE : TClosure 𝒯 G.R x y → …` embodies) is hard (chunk 0158): "Soundness is more difficult because the
use of `(R𝒯)` rules means that derivations in `N(𝒯)` involving **excursions through non-tree consequences
are unavoidable**. The easiest proof of soundness uses the modified sequent system `L_m(𝒯,∅)` ... For in
these systems, excursions through non-tree graphs can be avoided by the use of `𝒯`-closure in the `(□L)`
and `(□R)_m` rules." His Figure 8-1 (chunk 0151) is an explicit countermodel to general (non-tree)
soundness. **This confirms the prior report's wall is real for the `TClosure→exact-r-edge` decomposition** —
but note the obstruction is about **non-tree consequences (open assumptions across a non-tree graph)**, not
about theoremhood over a tree, which is what `NIKTheorem` is.

### 2. MMS 2021: a DIRECT birelational soundness for incestuality, and the technique CSLib missed (chunks 0026–0046)

MMS prove **direct** soundness (Theorem 5.3 / Theorem 7.2) of their fully-labelled system — including the
incestuality rule `⊠gklmn` — against birelational frames, with **no** Hilbert/adequacy detour. The
mechanism (chunk 0046, the `⊠gklmn` case; chunk 0028, the `3L` case) is uniform: assume the conclusion
sequent fails in a model; the model **is** klmn-incestuous, so the frame condition **supplies existential
witnesses** `v, w` (`⟦y⟧ ≤ v, vR^l w, ⟦z⟧R^n w`); then **extend the interpretation by mapping the FRESH
labels to those witnesses** (`⟦y'⟧* = v, ⟦u⟧* = w`); contradiction. The frame-condition structural rules
`refl, trans, F1, F2` are "trivial, as all birelational frames obey the corresponding conditions"
(chunk 0028).

Answer to sub-question 2: **the raised/existential witness is used exactly where CSLib hits its
"exactness wall" — but MMS absorb it into a FRESH label (or a raised value), and their sequents only ever
carry EXPLICIT relational atoms, so they never form a closed edge between two already-fixed points.** The
"standard move the in-repo attempts missed" is: **do not validate the derived/closed edge as an exact
`r`-edge — instead push the raised witness through the modal forcing clause at the point of use.**

### 3. Diagnosis of the discrepancy (sub-question 3): the wall is in the PROOF RULE, not the forcing clause

CSLib's `CKForces` box clause (`Forcing.lean:75`):
`.box φ => ∀ w', w ≤ w' → ∀ u, r w' u → CKForces … u φ`.
This is **identical** to the standard birelational box clause (Simpson Ch.3; MMS Def 2). It is **NOT
stronger**. So the wall is **not** semantic.

The wall is architectural: CSLib's **proof rules** `boxE` and `diaI` (`Deduction.lean:288–303`) carry a
`hR : TClosure 𝒯 G.R x y` premise — a **frame-closed** edge between two **already-present** labels. The
prior soundness attempts maintained a **clique** edge-cond invariant (`∀ a b, TClosure TS5 G.R a b →
r (ρa)(ρb)`) to discharge that premise, whose `.symm` case is exact symmetry (Wall A). **That invariant is
the mistake.** MMS's Def 5.1 (chunk 0026) validates only **raw** atoms; the closed edge is never validated
as an exact edge. The correct CSLib invariant is likewise **raw** edge-cond
(`∀ a b, G.R a b → r (ρa)(ρb)`), with `boxE`/`diaI` discharged by **box/diamond persistence across the
`TClosure` class** (below), exactly mirroring MMS pushing the raised witness through the modal clause.

- Compare: CSLib `Forcing.lean:75` box clause ↔ MMS/Simpson standard box clause → **same** (wall is not here).
- Compare: CSLib `boxE`/`diaI` `TClosure 𝒯 G.R` premise (`Deduction.lean:290,302`) ↔ MMS explicit-atom-only
  sequents (Def 5.1) → **different**; this is the key, and the fix is the persistence reformulation, not a
  rule change (`NIK` stays exactly as landed — no regression).

### 4. The concrete, machine-verified direct construction

Faithful inline restatement of `cs5FCIncest` (`CS5Canonical.lean:255–260`): `hrefl : ∀ w, r w w`;
`htrans`; `hfour : r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t`; `hsymbox : r w u → u ≤ u' →
∃ t, r u' t ∧ w ≤ t`; `hincest : r w u → ∃ u', u ≤ u' ∧ r u' w`. All lemmas below were checked with
`lean_run_code` + `#print axioms` = **"does not depend on any axioms"**.

**(A) `boxE`/`diaI` — Wall A DISSOLVED.** Base biconditionals (verified):
- `box_iff_base : r a b → ((∀ w'≥a, ∀ u, r w' u → P u) ↔ (∀ w'≥b, ∀ u, r w' u → P u))`
  — forward via `hfour`; backward (the ex-Wall-A `.symm` direction) via `hincest` then `hfour`. `P` arbitrary.
- `dia_iff_base : r a b → ((∀ w'≥a, ∃ u, r w' u ∧ Q u) ↔ (∀ w'≥b, ∃ u, r w' u ∧ Q u))`
  — forward via `hsymbox`+`htrans`; backward via `hincest`+`hsymbox`+`htrans`. `Q` arbitrary.

These extend over the **entire `TClosure {T,B,Four}` class** by a `TClosure` induction: `base` = the
biconditional above; `refl` = `Iff.rfl`; `symm` = `Iff.symm` of the IH; `trans` = `Iff.trans`; `eucl` =
unreachable (`Five ∉ TS5`). `boxE` then closes: from `CKForces (ρx) (□A)` and `TClosure x y`, transport
to `CKForces (ρy) (□A)` via the box-iff, then `CKForces (ρy) A` via the `hrefl` instance
(`box_gives_here`, verified). `diaI` closes dually via `dia_iff` + `hrefl` + `ckforces_persistence`
(landed, `Forcing.lean:122`). **No exact symmetry, no clique invariant, anywhere.**

**(B) `boxI` — Wall B = the standard Lifting Lemma.** Ingredients verified derivable from `cs5FCIncest`:
- `F1 : r w u → w ≤ w' → ∃ u', u ≤ u' ∧ r w' u'` — this **is** the landed `cs5FCIncest_lift` (`Soundness.lean:322`).
- `F2 : r w u → u ≤ u' → ∃ w', w ≤ w' ∧ r w' u'` — new, 3 lines (`hsymbox` then `hincest`).

With both confluence directions available, Simpson's tree-lifting recursion (chunks 0154–0156) transfers:
raise `ρ` so `ρ x` lands exactly at the adversarial `w'`, map the fresh child to `u`, re-establish raw
edge-cond (via F1/F2 down/up the finite tree) and Γ-cond (via `ckforces_persistence`). This is the only
constructor needing lifting.

**(C) `diaE` needs NO lifting.** Its `◇` is instantiated at `w' = ρx` (`le_refl`), so the `◇` clause
yields a **direct** successor `u` of `ρx`; the fresh label maps to `u` exactly with `ρ x` unchanged. The
propositional cases and the fresh-label bookkeeping already exist in the landed `nik_soundness_onePoint`
(`Soundness.lean:345`), which is the exact 12-constructor skeleton, generalized here over an arbitrary `ρ`
and model instead of the one-point model.

## Reference-Grounding Table (H3): source chunk → claim → Lean target

| Source chunk (read) | Grounded claim | Lean target |
|---|---|---|
| Simpson 0151 | Non-tree soundness fails (Fig 8-1); tree soundness holds | Confirms `NIKTheorem` (tree) is the provable case; `nik_TS5_soundness` |
| Simpson 0153–0155 | Lifting Lemma 8.1.3 (tree-only), iterated via frame conditions | `boxI` lifting; `cs5FCIncest_lift`=F1 (`:322`) + F2 (new) |
| Simpson 0156 | (□I): raise, then fresh `[y]'=v` exactly | `boxI` case of main `NIK` induction |
| Simpson 0158 | Direct `N(𝒯)` needs `L_m`/Hilbert BECAUSE non-tree excursions | Diagnoses the prior `TClosure→exact-edge` dead end |
| MMS 0026 | Def 5.1: interpret only EXPLICIT atoms `xRy` | raw edge-cond invariant (not clique) |
| MMS 0028 | `3L`/frame rules: fresh label ⟼ supplied witness; `refl/trans/F1/F2` trivial | `dia_iff_base`, `diaE`; F1/F2 |
| MMS 0043–0044 | Thm 7.1 klmn-incestuality; Thm 7.2 direct birelational soundness | `cs5Incest` (`:234`); existence proof of a direct route |
| MMS 0046 | `⊠gklmn` soundness: extend `⟦·⟧` with fresh ⟼ existential witnesses | `box_iff_base`/`dia_iff_base` backward (raised-witness) directions |
| CSLib `Forcing.lean:75` | box clause = standard birelational clause (not stronger) | wall is not semantic |
| CSLib `Deduction.lean:288–303` | `boxE`/`diaI` carry `TClosure 𝒯 G.R` premise | the architectural locus of the wall; fixed by persistence reformulation |

## Adversarial Self-Verification (H4)

I attempted to refute my own conclusion. Every load-bearing algebraic claim was **machine-checked**
(`lean_run_code`, `#print axioms`), which is the specific failure mode of the prior four dispatches
(hand-analysis of a wall that was the wrong lemma).

| Claim | Source / Counterexample | Verdict |
|---|---|---|
| Wall A's `.symm` case (box) is dischargeable WITHOUT exact symmetry, via `hincest`+`hfour` | `box_iff_base` compiles, "does not depend on any axioms"; grounded in MMS 0046 fresh-witness technique | **CONFIRMED (machine-verified)** |
| Same for the diamond side | `dia_iff_base` compiles axiom-free (`hsymbox`+`htrans`; `hincest`+`hsymbox`+`htrans`) | **CONFIRMED (machine-verified)** |
| The biconditionals extend over all of `TClosure {T,B,Four}` | `Iff.rfl/symm/trans`; `eucl` unreachable (`Five ∉ TS5`, `Deduction.lean:206`) | **CONFIRMED** (structural; iff-closure is trivial once base holds) |
| Wall B needs lifting for `boxI` ONLY; F1+F2 both available | `F1` = landed `cs5FCIncest_lift` (`:322`); `F2` compiles axiom-free; `diaE` uses `le_refl` so needs no lift | **CONFIRMED** (F1/F2 machine-verified; tree recursion asserted standard, see Uncertain) |
| The prior "clique edge-cond" invariant is unnecessary; raw edge-cond suffices | MMS Def 5.1 (chunk 0026) validates only explicit atoms; `boxE`/`diaI` discharged by persistence | **CONFIRMED** (the reformulation removes the clique obligation entirely) |
| `CKForces` box clause is not stronger than standard | `Forcing.lean:75` vs Simpson Ch.3 / MMS Def 2 (chunk 0026) | **CONFIRMED** |
| Prior conclusion "Wall A is a genuine open question forcing [BLOCKED]" | The open question ("does `cs5FCIncest` force exact `r`-symmetry?") was the wrong question; soundness never needs it | **REFUTED** — this is the central correction |
| Counter-challenge: is `box_iff_base` vacuous/mis-stated? | `P`/`Q` are ARBITRARY predicates (not assumed upward-closed); the clause shape matches `CKForces_box`/`CKForces_diamond` exactly (`Forcing.lean:106–116`) | **Not vacuous** — verified against the real `@[simp]` clause shapes |
| Zero-debt: any recommended step need `sorry`/axiom/weakening? | The route reuses `cs5FCIncest` as-is, `NIK` as-is; all cruxes axiom-free | **CONFIRMED zero-debt** |

**Challenges raised and their resolution.**
- *"Simpson says direct `N(𝒯)` soundness is hard (needs `L_m`/Hilbert) — doesn't that confirm [BLOCKED]?"*
  No. Simpson's difficulty is about **consequences over non-tree graphs** (open assumptions), chunk 0158.
  `NIKTheorem` is **theoremhood over `Graph.trivial`** (a tree, `Deduction.lean:316`), Simpson's provable
  case (Thm 8.1.1/8.1.4, "Let `G` be a tree"). The `TClosure`-in-`boxE` premise is the frame closure of a
  **tree** graph, discharged by persistence — not a non-tree open-assumption excursion.
- *"Is Wall A maybe TRUE but the wrong-lemma framing hides a real gap?"* The gap the prior dispatches hit
  (`TClosure → exact r-edge`) is genuinely unprovable (constructive `R` isn't symmetric — MMS's whole
  point). But `boxE` soundness never requires it; `box_iff_base` discharges `boxE` directly. Verified.
- *"MMS is a sequent calculus with explicit atoms; CSLib is natural deduction with `TClosure`. Does the
  technique really transfer?"* The transferring object is the **semantic** step (push the raised witness
  through the modal clause), which is calculus-agnostic. Verified by re-deriving it directly against
  CSLib's own `CKForces` clause shapes.

**Uncertain claims (confidence).**
- The `boxI` tree-lifting recursion (item B) closes in Lean with only bounded bookkeeping: **~80%**. F1/F2
  are verified; the risk is purely the finite tree/freshness invariant (`Soundness.lean` "What remains"
  items 1–2), which is standard Simpson-8.1.3 structure, not a mathematical unknown. This is the one part
  **not** reduced to a compiling snippet this pass and is the main implementation risk.
- Overall direct-route completion at planned effort: **~80–85%** (was ~25–30% for the declined bridge),
  concentrated entirely in the `boxI` lifting recursion; the `boxE`/`diaE`/`diaI`/propositional cases are
  machine-verified or already-landed patterns.

No fundamental flaw surfaced; **no `## Revised Direction` restart triggered.** The verification instead
*strengthened* the verdict from "open" to "achievable, with the crux machine-checked."

## Ranked concrete next steps for the planner

1. **Land the box/diamond persistence lemmas (Wall A, LOW risk — cruxes already compile).**
   `box_iff_base`, `dia_iff_base` (base edge, both directions) → `box_iff_TClosure`, `dia_iff_TClosure`
   (induction on `TClosure`, `Iff.rfl/symm/trans`, `eucl` via `Set`-membership `False.elim`). Target file:
   `Soundness.lean`. These are self-contained and independently testable — do them first.
2. **Land `F2` and package the single-step lifting** next to the landed `cs5FCIncest_lift` (=F1). LOW risk.
3. **Build the `boxI` tree-lifting lemma** (Simpson 8.1.3 analogue): the freshness/tree invariant
   (`Soundness.lean` "What remains" 1–2) threading F1/F2 down the finite derivation tree, Γ-cond via
   `ckforces_persistence`. This is the bulk of the work and the main risk; size it as its own phase.
4. **Assemble `nik_TS5_soundness`**: the 12-constructor `NIK` induction generalized over `ρ` and model
   (reuse the `nik_soundness_onePoint` skeleton, `Soundness.lean:345`), carrying **raw** edge-cond + Γ-cond;
   `boxE`/`diaI` via step 1, `boxI` via step 3, `diaE` via `le_refl` (no lift), propositional cases verbatim
   from the one-point proof. Then `nik_TS5_soundness` follows by specializing to `Graph.trivial`/`[]`.
5. **Regression gate**: re-verify `cs5_completeness`, `nik_TS5_consistent`, `cs5_soundness_derivable_incest`
   unchanged; `cs5FCIncest` unweakened; `lake build` green; `lean_verify nik_TS5_soundness` (no `sorryAx`).

**Do NOT** revive the Hilbert-labelled adequacy bridge (user declined) or the `L_m` sequent system — this
report shows neither is needed; the direct route is cheaper and its crux is machine-verified.

## Memory Candidates

1. Labelled-CS5 `boxE`/`diaI` soundness over `cs5FCIncest` is discharged by **box/diamond forcing-equivalence
   across the `TClosure {T,B,Four}` class** (`CKForces (ρx)(□A) ↔ CKForces (ρy)(□A)`), proved from
   `hincest`/`hfour`/`hsymbox`/`htrans` raised witnesses — NOT by validating each closed edge as an exact
   `r`-edge. The "exact r-symmetry" lemma that blocked four dispatches is both false-in-general and
   unnecessary. (machine-verified, axiom-free)
2. `cs5FCIncest` yields BOTH birelational confluence directions: F1 (source-raise) = landed
   `cs5FCIncest_lift`; F2 (target-raise) = `hsymbox` then `hincest`, three lines. Simpson's Lifting Lemma
   8.1.3 therefore transfers; only `boxI` needs it (`diaE` uses `le_refl`, needs none).
3. General method (Simpson 0158 + MMS 0026/0046): to prove labelled soundness against frame-condition rules,
   maintain a **raw** edge-cond invariant and push raised/existential witnesses through the modal forcing
   clause at the point of use — never a `TClosure`-clique invariant. This is the MMS fresh-witness technique;
   it sidesteps the "non-tree excursion" obstruction for theoremhood-over-a-tree.

## References

* [Simpson1994] A. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*, Ch. 8
  (chunks 0151–0160): §8.1.2 Soundness, Lemma 8.1.3 Lifting Lemma, Thm 8.1.1/8.1.4, Fig 8-1 counterexample.
* [MarinMoralesStrassburger2021] Marin, Morales, Straßburger, *A fully labelled proof system for
  intuitionistic modal logics*, JLC 31(3):998–1022 (chunks 0026, 0028, 0043, 0044, 0046, 0048): Def 5.1
  G-interpretation, Thm 5.3 soundness, Thm 7.1 klmn-incestuality, Thm 7.2, `⊠gklmn` soundness.
