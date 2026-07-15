# RESUME HERE — Task 517 (and the CS5-completeness thread)

**Single entry point after a context clear.** Everything below is committed to git.

## One-line status
Task **517 is [PLANNED]**. Next action = **Track A of `plans/02_decomposed-track-a-b-c.md`**:
run **A1** (fix `IKAx`) then **A2** (probe `CS5 ⊢ FS`). A2 is the decisive step and is shared with task 512.

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
- **A1** — add axioms 3 (`¬◇⊥`), 4 (`◇(A∨B) ⊃ ◇A∨◇B`), 5 (`(◇A ⊃ □B) ⊃ □(A ⊃ B)`) as constructors of
  `IKAx` (`probes/lemma612-scaffold.lean:78`). Mechanical, LOW risk, `probes/` only. Success: file still
  compiles sorry-free; `#print axioms` on `NIK_to_NIKAx`/`TClosure.hilbertTransport` unchanged.
- **A2** — attempt sorry-free `CS5 ⊢ FS` in `Cslib/.../CS5.lean` (`CS5ModalAxiom`, CS5.lean:182). HARD CAP
  one dispatch. Either a proof OR a precisely documented failure — both decisive, for 517 AND 512.
- **A3** — paper GO/NO-GO on the semantic route (Track B) given A2's result.
- Then **Track B** (semantic; needs Fischer Servi 1984 `/literature`-ingested — NOT in corpus) on a GO,
  else **Track C** (tree surgery C1–C8; C5 is the true crux; only if Track B is NO-GO).

## What is landed and MUST NOT be redone (all sorry-free, axiom-clean, CI-green)
- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Syntax.lean` (Phase 1), `Deduction.lean` (Phase 2),
  `Context.lean` (Phase 4) — ~789 lines. Independent contribution even if CS5 completeness never lands.
- `probes/adequacy-gate-probe.lean` — Lemma 6.2.2 hard direction, correct & reusable.
- `probes/lemma612-scaffold.lean` — LTree scaffold; **DEFECTIVE**: `IKAx` missing axioms 3/4/5 (A1 fixes);
  `pathTo`/`pathToList` return full-not-pruned subtree; `Star_append` wrong (Track C C4/C5 fix).

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
