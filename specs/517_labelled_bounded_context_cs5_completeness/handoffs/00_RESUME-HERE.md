# RESUME HERE — Task 517 (and the CS5-completeness thread)

**Single entry point after a context clear.** Everything below is committed to git.

## ⛔ NEWEST RESULT FIRST — Plan 08 Phase 19 DECISION GATE: **`CS5 ⊢ FS` is DERIVED**

**Read this before anything below; the older sections predate it.** Phase 19 (commit `04ce827f`)
decided the gate: **`CS5 ⊢ FS` is TRUE**, mechanized sorry-free as **`cs5_fs`** in
`probes/fs-derivation-gate.lean`, footprint `[propext, Classical.choice]`. This **eliminates**
the `~25%` "target is FALSE" risk — the single largest term in this task's failure probability.
Phase 16's `cs5_completeness ⟹ CS5 ⊢ FS` necessary condition is **discharged**.
**Branch taken: proceed to Phase 20 → 21.** **Do NOT re-open this gate. Do NOT attempt a
countermodel — none exists, and the proof that none exists IS the derivation.**
Also unblocks **task 512**'s diagnosis.

**Two landed claims are now STALE — do not trust them:**
1. `probes/fischer-servi-probe.lean`'s module docstring records a **NEGATIVE** verdict on
   `CS5 ⊢ FS`, self-described as *"not a search failure ... a structural mismatch"*. **It is
   refuted.** Its argument holds only for routes that keep the hypothesis `H : ◇A → □B` in the
   *context*. `cs5_fs` instead treats `C := ◇A → □B` as a **formula**, proves the **closed**
   theorem `⊢ ◇C → (A → B)`, necessitates *that* (legal — empty context), and re-attaches the
   hypothesis via `bBox`'s `C → □◇C`. Its `fs_sound''` and `cs5_completeness_implies_fs_derivable`
   remain **valid and untouched** — only the obstruction narrative is wrong. Fix the docstring
   when that file is next touched.
2. The `fs_context_relative_half` obstruction is **circumvented, not contradicted** — it blocks
   the context-relative route; `cs5_fs` is not that route.

**The reusable insight (worth more than the theorem):** `bBox` (`φ → □◇φ`) and `bDia`
(`◇□φ → φ`) are exactly the **unit and counit of an adjunction `◇ ⊣ □`**. A CS5 algebra is a
Heyting algebra plus a complete sublattice `J`, with `◇` the reflector and `□` the coreflector.
`kBox` is then automatic, and **`kDia` ⟺ Frobenius** (`◇(u ∧ x) = u ∧ ◇x` for `u ∈ J`). When a
Hilbert-style derivation looks blocked because "necessitation needs an empty context", the B
axiom lets you **internalize the hypothesis as `◇C`** instead of holding it in context.

**Not done (deliberate):** `cs5_fs` is not yet transcribed into `Cslib/` — Phase 19's territory
was `probes/` ONLY. That is transcription, not proof work.

---

## One-line status
Task **517 is [IMPLEMENTING]**. Track A (`plans/02_decomposed-track-a-b-c.md`) is
**[COMPLETED]** (A1, A2, A3 all done). **A3's verdict: NO-GO for Track B** — Track B is CLOSED,
do not re-open without a representation change (see below). **Track C is now ACTIVE**; C1, C2,
C3, **C4 are all [COMPLETED]** (C4 landed this dispatch, session `sess_1784145761_061228`). Next
action = **Track C C5 — the TRUE crux (HIGH risk)** — see
`summaries/06_c4-tree-surgery-unfolding-identity-summary.md` for this dispatch's full outcome.
**Do NOT re-run A1/A2/A3/C1/C2/C3/C4** — all landed, sorry-free, in `probes/`.

## Track C C4 outcome (this dispatch)
`probes/lemma612-scaffold.lean` (extended in place). **`star` FIXED** (was a double-`bigAnd`,
now a single `bigAnd` over the concatenated labels++children list — the old version fails the
worked-example check, confirmed by hand before editing). `prune`/`fullSubtree` added (children
split `pre ++ [c]`, continuation child LAST, matching `addChild`'s existing append convention —
forward-compatible with C5). **Unfolding identity proved as an IK-derivable two-way implication**
(`star_unfold_imp1`/`star_unfold_imp2`), NOT raw `Eq` — `bigAnd`'s right-fold makes literal term
equality fail once the pruned node has 2+ ordinary children (associativity, not `rfl`-provable);
built via new reusable `andI_deriv`/`andE1_deriv`/`andE2_deriv`/`top_deriv`/
`bigAnd_cons_of_ne_nil`/`bigAnd_append_singleton_imp1`/`imp2`. `pathTo`/`pathToList`/
`Star_append` all DELETED (confirmed defective/wrong per the plan). Success criterion
(worked-example verbatim match) delivered as a real `simp`-based theorem
(`star_Star_worked_example`), not `#eval`/`decide` — `Label` has no computable `DecidableEq` in
this file (only classically-opaque `Classical.propDecidable`), verified via a scratch probe
before committing to the approach. Sorry-free, axiom footprint
`[propext, Classical.choice, Quot.sound]` (no new axioms). `Star`/`Star_imp1`/`Star_imp2`/
`box_mono1`/`box_mono2`/`NIKAx`/`TClosure.hilbertTransport` all unchanged, reverified compiling.
C1/C2/C3's separate file untouched, reverified compiling.

## A3 verdict (this dispatch — read before doing anything else)

**NO-GO for Track B.** Two findings:
1. `cs5FC''` DOES coincide with `IS5`'s birelational semantics (Simpson Thm 3.3.4) — confirmed,
   this alone would favor GO.
2. **Decisive blocker (unrelated to A2's syntactic gap)**: Pacheco's canonical CKB-relation, once
   extended with axiom `T` (needed to reach `CS5`), automatically satisfies the hypotheses of
   CSLib's already-mechanized `cs5Incest_forces_symm` (task 512, `CS5Canonical.lean:643`) — `T`
   gives `boxInv Γ ⊆ Γ`, so Pacheco's `Γ⊆Δ` conjunct gives exactly the theorem's `hbox` premise,
   and Pacheco's required `R`-symmetry (CKB-models) trivially satisfies `cs5Incest`. The
   conclusion forces `cs5Tail`-shape, which `cs5_symmetric_tail_box_gap` (task 509) proves cannot
   admit box-backward's witness. **Task 512's Phase-7 gate already hit this exact wall** via both
   the one-sided-R and two-sided-R routes (`cs5TwoSidedR_iff_cs5Tail` shows the latter is
   extensionally identical to Pacheco's second conjunct). Full argument with exact theorem names:
   `plans/02_decomposed-track-a-b-c.md`'s A3 entry.

**Consequence**: Track B (B1/B2/B3) is CLOSED — do not open. Track C (Simpson tree surgery) is
the only remaining route to `cs5_completeness` via the labelled framework's adequacy bridge.

## Track C C1 outcome (this dispatch)
`probes/track-c-c1-tele-conj.lean` (new) — `Conj`/`Tele` over `List (Proposition Atom)` (Simpson
p.104), and `Tele_imp1`/`Tele_imp2` (ported from `Star_imp1`/`Star_imp2`). **Generalized** beyond
the plan's ask: all combinators (`impIntro`/`box_mono1`/`box_mono2`/`Tele_imp1`/`Tele_imp2`) are
parametric over an arbitrary `Axioms : Proposition Atom → Prop` (not hard-wired to `IKAx 𝒯`),
directly reusable by C2/C3. Sorry-free, axiom footprint `[propext, Classical.choice, Quot.sound]`
(standard CSLib Metalogic footprint, not new).

## The reframe (why the plan changed) — read `reports/02_adequacy-alternatives-and-technique.md`
Three dispatches failed to mechanize Simpson's Ch.6 adequacy bridge (Lemma 6.1.2). The research then found:
1. **The adequacy bridge is NOT on the critical path** (~85%). Simpson proves IS5 completeness in **Chapter 3**
   (Thm 3.3.4, p.56) via a canonical birelation model citing **Fischer Servi 1984** — it does not use the
   labelled system. Plan 01 routed `cs5_completeness` through Ch.6 unnecessarily.
   **UPDATE (A3, this dispatch)**: the Ch.3 semantic route (Track B) is now CLOSED (NO-GO, see above) —
   so the adequacy bridge (Ch.6, via the labelled framework) IS back on the critical path after all,
   via Track C.
2. **Unified diagnosis with task 512**: Simpson's canonical model turns on axiom **`FS = (◇ϕ → □ψ) → □(ϕ → ψ)`**.
   Both task 512 and 517 have been attacking **CS5, which lacks `FS`**. Pacheco's method: establish CS5 ≡ IS5,
   then work on the IK side where `FS` is available. **UPDATE (A3)**: this method's canonical-model
   construction, once T-extended, hits the SAME wall task 512 already mechanized — not a genuine escape.
3. **5th scaffold defect** (~97%, FIXED by A1): `probes/lemma612-scaffold.lean`'s `IKAx` was missing IK
   axioms 3/4/5 — repaired.

## Exact next steps (from `plans/02_decomposed-track-a-b-c.md`)
- ~~**A1** — add axioms 3/4/5 to `IKAx`~~ **[COMPLETED]**.
- ~~**A2** — attempt sorry-free `CS5 ⊢ FS`~~ **[COMPLETED]**, mixed outcome (see prior dispatch).
- ~~**A3** — paper GO/NO-GO on Track B~~ **[COMPLETED]** — **NO-GO**.
- ~~**Track C C1** — `Tele`/`Conj` + congruence~~ **[COMPLETED]**.
- ~~**Track C C2** — prove (6.7)~~ **[COMPLETED]** — see `summaries/04_c2-formula-6-7-summary.md`.
  **Scoping correction, load-bearing**: (6.7)'s schema had to be restated for *nonempty*
  `V = p :: rest` — the literal `V = []` instance is FALSE in bare IK (countermodel-checked).
- ~~**Track C C3** — prove (6.8)~~ **[COMPLETED]** this dispatch — see
  `summaries/05_c3-formula-6-8-summary.md`. **Base-case check result DIFFERS from C2's**: unlike
  (6.7)'s `V=[]`, (6.8)'s `W=[]` instance (`(◇⊤⊃□B)⊃□B`) IS a genuine IK theorem — no restatement
  needed. `formula_6_8` in `probes/track-c-c1-tele-conj.lean` (appended) holds for *all* `W`,
  proved by induction using `hFS` (axiom 5, `IKAx.fs`) once per level composed with the IH via a
  new `derivable_imp_trans` combinator (also directly reusable by C7's (◇E) 3-step composition —
  see plan's §2.5 argument, which composes exactly 3 such transitivity steps).
- ~~**Track C C4** — `LTree`,`star`,`fullSubtree`,`prune` + the **unfolding identity**~~
  **[COMPLETED]** this dispatch — see `summaries/06_c4-tree-surgery-unfolding-identity-summary.md`.
  `star` FIXED (double-`bigAnd` → single concatenated `bigAnd`); `pathTo`/`pathToList`/
  `Star_append` DELETED; unfolding identity proved as `Derivable`-Iff (`star_unfold_imp1`/
  `imp2`), not raw `Eq` (associativity blocks literal term equality in general).
- **Track C C5 (NEXT) — THE TRUE CRUX, HIGH risk**: `pathSpine` (the whole-path recursion with
  pruning BUILT IN, replacing the deleted `pathTo`/`pathToList`) + the `addChild`/`pathSpine`
  **commutation lemma**. Success criterion (from the plan): sorry-free commutation lemma. This is
  its own dedicated dispatch — do NOT bundle with C6-C8 (H8 phase sizing). Reuse `prune`/
  `fullSubtree`/`star_unfold_imp1`/`star_unfold_imp2` from C4 (this dispatch) — `pathSpine`
  should be built to RETURN the `pre`-lists `prune`/`fullSubtree` need at each level (i.e.
  `pathSpine` is the thing that walks the tree and, at each non-last node, splits its children
  into "ordinary" vs "the one leading toward the target" — exactly the `pre`/`c` split C4's
  `prune`/`fullSubtree` already consume). The commutation lemma needs to relate `pathSpine` on
  `addChild t x y` to `pathSpine` on `t` — `addChild` appends the new child at the END of the
  children list (`node l (cs ++ [leaf y])`), which is WHY C4 chose `pre ++ [c]` (continuation
  child LAST) for `prune`/`fullSubtree` rather than head-first — check this convention still
  looks right once `pathSpine`'s actual recursion is written; if the tree has multiple
  interior branch points, `pathSpine` needs to identify, PER NODE ALONG THE PATH, which one
  child continues the path — do not assume WLOG it is always literally the last-appended one
  without checking against how the target label was reached.
- Then **C6-C8** (truth-lemma cases, given C5). See plan file's Track C table for the full
  C1-C8 breakdown and risk ratings.

## What is landed and MUST NOT be redone (all sorry-free, axiom-clean, CI-green)
- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Syntax.lean` (Phase 1), `Deduction.lean` (Phase 2),
  `Context.lean` (Phase 4) — ~789 lines. Independent contribution even if CS5 completeness never lands.
- `probes/adequacy-gate-probe.lean` — Lemma 6.2.2 hard direction, correct & reusable.
- `probes/lemma612-scaffold.lean` — `IKAx` has axioms 3/4/5 (A1). `star` FIXED (C4, single
  concatenated `bigAnd`); `prune`/`fullSubtree` + `star_unfold_imp1`/`star_unfold_imp2` (the
  unfolding identity, `Derivable`-Iff) added (C4); `pathTo`/`pathToList`/`Star_append` DELETED
  (C4, were defective/wrong). **Still MISSING** (C5's job): `pathSpine`, the whole-path recursion
  with pruning built in, and its commutation with `addChild`.
- `probes/fischer-servi-probe.lean` (A2) — `fs_context_relative_half` (mechanized syntactic
  obstruction) and `fs_sound''` (semantic `FS`-validity over `cs5FC''`, sorry-free, axiom-free).
- `probes/track-c-c1-tele-conj.lean` (C1) — `Conj`, `Tele`, `impIntro`,
  `box_mono1`, `box_mono2`, `Tele_imp1`, `Tele_imp2`, all generic over `Axioms`. Reusable
  verbatim by C2/C3 without redeclaration.
- **Same file, C2 section** — `dia_mono1`, `formula_6_7_base`, `formula_6_7` (Simpson (6.7),
  stated for nonempty `V = p :: rest`; the `V = []` instance is FALSE in bare IK,
  countermodel-checked, see plan's C2 entry). Sorry-free, axiom footprint
  `[propext, Classical.choice, Quot.sound]` (same as C1, no new axioms).
- **Same file, C3 section appended this dispatch** — `derivable_imp_trans`, `formula_6_8`
  (Simpson (6.8), holds for ALL `W` including `[]`, unlike C2's restriction). Sorry-free, same
  axiom footprint. C4 (tree-level work) will need its own new file or extension since it depends
  on `LTree`/`star` from `lemma612-scaffold.lean`, not just `Conj`/`Tele` — decide at C4 dispatch
  time whether to extend `lemma612-scaffold.lean` in place or bridge the two probe files.

## Debt to clear before ANY PR (do not forget)
- `GeomWitnessClosure := True` in `Context.lean` violates the project's no-vacuous-def rule; it couples
  with Phase 1's elided k-ary witnesses and `TClosure`'s exclusion of `χ_D` to make `GeomAxiom.D` a silent
  trap. Harmless for `TS5={T,Five}` (both universal-Horn). Fix: drop `D` from `GeomAxiom`, or require a
  no-existential-axioms proof so `𝒯={D}` fails to typecheck.

## Related task states (all committed)
- **512** [BLOCKED] — CS5 completeness via prime-theory canonical model; every prime-theory route mechanically
  dead (guardrails: `cs5Incest_forces_symm`, `cs5TwoSidedR_iff_cs5Tail`, `cs5_symmetric_tail_box_gap`).
  Blocked-on-517. **A3 (this dispatch) confirms 517's Track B would hit the SAME wall** — 512 remains
  blocked; only a representation change (Track C's labelled framework) can unblock it.
- **516** [ABANDONED] — independent-≤ + Simpson-prime-theory Route A both refuted; reports 01/02 are the
  route analysis that justified 517.
- **518** [COMPLETED] — Simpson corpus re-ingested (1091→206 chunks); spine lemmas now readable.
- **519** [NOT STARTED] — general OCR-chunking fix + re-ingest Wijesekera 1990.

## Zero-debt status
`Cslib/` has zero `sorry`, zero new axioms from this entire effort. Task-509 `cs5FC''` untouched. Repo
builds green (the only repo-wide unrelated in-flight edit is task-515's concurrent
`Tableau/FrameSoundness.lean` work, not touched by 517).
