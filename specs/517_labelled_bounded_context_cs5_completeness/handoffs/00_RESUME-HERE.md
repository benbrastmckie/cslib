# RESUME HERE — Task 517 (and the CS5-completeness thread)

**Single entry point after a context clear.** Everything below is committed to git.

## One-line status
Task **517 is [IMPLEMENTING]**. Track A (`plans/02_decomposed-track-a-b-c.md`) A1+A2 are
**[COMPLETED]** (this dispatch, session `sess_1784145761_061228`). Next action = **A3** (paper
GO/NO-GO on Track B, no Lean) — see `summaries/02_track-a-a1-a2-summary.md` for the full A1/A2
outcome. **Do NOT re-run A1/A2** — both landed, sorry-free, in `probes/`.

## A1/A2 outcome (this dispatch — read before doing anything else)
- **A1**: `probes/lemma612-scaffold.lean`'s `IKAx` now has Simpson's base-`IK` axioms 3/4/5
  (`diaBot`/`diaOr`/`fs`) as unconditional constructors. Sorry-free, additive, verified.
- **A2**: `probes/fischer-servi-probe.lean` (new). Syntactic `CS5 ⊢ FS` is **left open**, with the
  exact obstruction mechanized (`fs_context_relative_half`: necessitation needs empty context,
  but every route to `A→B` from `◇A→□B` genuinely uses the hypothesis). Semantic
  `CKValidFC cs5FC'' FS` is **proved, sorry-free, axiom-free** (`fs_sound''`, uses only
  `bBox`/`bDia`-supporting frame clauses). **This de-risks Track B** — the F2 confluence
  precondition Track B's canonical-model route needs is now a mechanized fact, not an open
  question. A3 should factor this in: Track B's GO/NO-GO looks more favorable than the plan's
  original 35-40% estimate, but A3 must still check semantic-model coincidence with `IS5` and
  whether A2's syntactic gap blocks Pacheco's `CKB≡IKB` chain.

## The reframe (why the plan changed) — read `reports/02_adequacy-alternatives-and-technique.md`
Three dispatches failed to mechanize Simpson's Ch.6 adequacy bridge (Lemma 6.1.2). The research then found:
1. **The adequacy bridge is NOT on the critical path** (~85%). Simpson proves IS5 completeness in **Chapter 3**
   (Thm 3.3.4, p.56) via a canonical birelation model citing **Fischer Servi 1984** — it does not use the
   labelled system. Plan 01 routed `cs5_completeness` through Ch.6 unnecessarily.
2. **Unified diagnosis with task 512**: Simpson's canonical model turns on axiom **`FS = (◇ϕ → □ψ) → □(ϕ → ψ)`**.
   Both task 512 and 517 have been attacking **CS5, which lacks `FS`**. Pacheco's method: establish CS5 ≡ IS5,
   then work on the IK side where `FS` is available.
3. **5th scaffold defect** (~97%): `probes/lemma612-scaffold.lean`'s `IKAx` is missing IK axioms 3/4/5, so
   Lemma 6.1.2 was never provable against it anyway.

## Exact next steps (from `plans/02_decomposed-track-a-b-c.md`)
- ~~**A1** — add axioms 3/4/5 to `IKAx`~~ **[COMPLETED]** this dispatch (`probes/lemma612-scaffold.lean`).
- ~~**A2** — attempt sorry-free `CS5 ⊢ FS`~~ **[COMPLETED]** this dispatch, mixed outcome — see
  "A1/A2 outcome" above and `probes/fischer-servi-probe.lean`.
- **A3 (NEXT)** — paper GO/NO-GO on the semantic route (Track B), factoring in `fs_sound''`
  (F2 confluence mechanized, sorry-free) and the open syntactic gap. No Lean required for A3 itself.
- Then **Track B** (semantic; needs Fischer Servi 1984 `/literature`-ingested — NOT in corpus) on a GO,
  else **Track C** (tree surgery C1–C8; C5 is the true crux; only if Track B is NO-GO).

## What is landed and MUST NOT be redone (all sorry-free, axiom-clean, CI-green)
- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Syntax.lean` (Phase 1), `Deduction.lean` (Phase 2),
  `Context.lean` (Phase 4) — ~789 lines. Independent contribution even if CS5 completeness never lands.
- `probes/adequacy-gate-probe.lean` — Lemma 6.2.2 hard direction, correct & reusable.
- `probes/lemma612-scaffold.lean` — LTree scaffold; `IKAx` now has axioms 3/4/5 (A1, this
  dispatch, fixed). **Still DEFECTIVE elsewhere**: `pathTo`/`pathToList` return full-not-pruned
  subtree; `Star_append` wrong (Track C C4/C5 fix, unrelated to A1's repair).
- `probes/fischer-servi-probe.lean` (A2, this dispatch, new) — `fs_context_relative_half`
  (mechanized syntactic obstruction) and `fs_sound''` (semantic `FS`-validity over `cs5FC''`,
  sorry-free, axiom-free). Reusable by Track B without modification.

## Debt to clear before ANY PR (do not forget)
- `GeomWitnessClosure := True` in `Context.lean` violates the project's no-vacuous-def rule; it couples with
  Phase 1's elided k-ary witnesses and `TClosure`'s exclusion of `χ_D` to make `GeomAxiom.D` a silent trap.
  Harmless for `TS5={T,Five}` (both universal-Horn). Fix: drop `D` from `GeomAxiom`, or require a
  no-existential-axioms proof so `𝒯={D}` fails to typecheck.

## Related task states (all committed)
- **512** [BLOCKED] — CS5 completeness via prime-theory canonical model; every prime-theory route mechanically
  dead (guardrails: `cs5Incest_forces_symm`, `cs5TwoSidedR_iff_cs5Tail`, `cs5_symmetric_tail_box_gap`).
  Blocked-on-517. **A2's result may unblock it** (the shared `FS` diagnosis).
- **516** [ABANDONED] — independent-≤ + Simpson-prime-theory Route A both refuted; reports 01/02 are the
  route analysis that justified 517.
- **518** [COMPLETED] — Simpson corpus re-ingested (1091→206 chunks); spine lemmas now readable. Caveat:
  Tesseract garbles modal glyphs — read the source PDF `/home/benjamin/Downloads/Simpson_1994_IntuitionisticModalLogic.ocr.pdf` for exact rule shapes.
- **519** [NOT STARTED] — general OCR-chunking fix + re-ingest Wijesekera 1990 (same fragmentation). Ready to run.

## Zero-debt status
`Cslib/` has zero `sorry`, zero new axioms from this entire effort. Task-509 `cs5FC''` untouched. Repo builds
green (the only repo-wide build issue is task-505's unrelated in-flight `Tableau/FrameCompleteness.lean` edit).

## Operational note
Session usage limit was hit during the last research dispatch (resets ~1pm PT the day of writing). Dispatches
may be throttled until then.
