# RESUME HERE — Task 517 (and the CS5-completeness thread)

**Single entry point after a context clear.** Everything below is committed to git.

## One-line status
Task **517 is [IMPLEMENTING]**. Track A (`plans/02_decomposed-track-a-b-c.md`) is
**[COMPLETED]** (A1, A2, A3 all done). **A3's verdict: NO-GO for Track B** — Track B is CLOSED,
do not re-open without a representation change (see below). **Track C is now ACTIVE**; C1 and
**C2 are [COMPLETED]** (C2 landed this dispatch, session `sess_1784145761_061228`). Next action =
**Track C C3** — see `summaries/04_c2-formula-6-7-summary.md` for this dispatch's full outcome.
**Do NOT re-run A1/A2/A3/C1/C2** — all landed, sorry-free, in `probes/`.

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
- ~~**Track C C2** — prove (6.7)~~ **[COMPLETED]** this dispatch — see
  `summaries/04_c2-formula-6-7-summary.md`. **Scoping correction, load-bearing for C3**: (6.7)'s
  schema had to be restated for *nonempty* `V = p :: rest` — the literal `V = []` instance is
  FALSE in bare IK (countermodel-checked). **Apply the same countermodel-style sanity check to
  (6.8)'s `W = []` case before writing any Lean for C3** — do not assume the empty-list case
  holds just because the plan's table entry doesn't flag it.
- **Track C C3 (NEXT)** — prove (6.8): `(◇Conj(W) ⊃ □Tele(W,B)) ⊃ □Tele(W,B)`, induction on W,
  using axiom 5 (`IKAx.fs`, present since A1: `((◇φ).imp (box ψ)).imp (box (φ.imp ψ))`). Reuse
  `Conj`/`Tele`/`impIntro`/`box_mono1`/`dia_mono1` from `probes/track-c-c1-tele-conj.lean`
  (append to the SAME file — cross-probe `import` does not resolve for these standalone
  `lake env lean` files; C2 already established this pattern). Risk MED per plan — the base case
  needs its own semantic check first (see above), and (6.8)'s self-referential shape (consequent
  `□Tele(W,B)` also appears bare, not just under the outer implication) is structurally different
  from (6.7)'s, so do not assume the same proof skeleton transfers mechanically.
- Then **C4** (LTree/star/prune + the unfolding identity; DELETE `pathTo`/`pathToList`/
  `Star_append`), **C5** (`pathSpine` — THE TRUE CRUX, HIGH risk), **C6-C8** (truth-lemma cases).
  See plan file's Track C table for the full C1-C8 breakdown and risk ratings. **HARD STOP still
  applies**: do not open C4/C5 until C3 lands (H8 phase sizing).

## What is landed and MUST NOT be redone (all sorry-free, axiom-clean, CI-green)
- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Syntax.lean` (Phase 1), `Deduction.lean` (Phase 2),
  `Context.lean` (Phase 4) — ~789 lines. Independent contribution even if CS5 completeness never lands.
- `probes/adequacy-gate-probe.lean` — Lemma 6.2.2 hard direction, correct & reusable.
- `probes/lemma612-scaffold.lean` — LTree scaffold; `IKAx` now has axioms 3/4/5 (A1). **Still
  DEFECTIVE elsewhere**: `pathTo`/`pathToList` return full-not-pruned subtree; `Star_append`
  wrong (Track C C4/C5 fix target, unrelated to A1's repair).
- `probes/fischer-servi-probe.lean` (A2) — `fs_context_relative_half` (mechanized syntactic
  obstruction) and `fs_sound''` (semantic `FS`-validity over `cs5FC''`, sorry-free, axiom-free).
- `probes/track-c-c1-tele-conj.lean` (C1) — `Conj`, `Tele`, `impIntro`,
  `box_mono1`, `box_mono2`, `Tele_imp1`, `Tele_imp2`, all generic over `Axioms`. Reusable
  verbatim by C2/C3 without redeclaration.
- **Same file, C2 section appended this dispatch** — `dia_mono1`, `formula_6_7_base`,
  `formula_6_7` (Simpson (6.7), stated for nonempty `V = p :: rest`; the `V = []` instance is
  FALSE in bare IK, countermodel-checked, see plan's C2 entry). Sorry-free, axiom footprint
  `[propext, Classical.choice, Quot.sound]` (same as C1, no new axioms). C3 should append to this
  SAME file too (cross-probe `import` does not resolve for these standalone files).

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
