# Implementation Summary: Phase 11 (Fallback Route PD) — Motive Redesign, Blocked on `efq` Residual

- **Task**: 537 — Prove the general labelled soundness direction, completing Simpson 1994 Thm
  8.1.4's biconditional (`nik_TS5_soundness`)
- **Plan**: plans/04_hilbert-adequacy-bridge.md (v4)
- **Status**: PARTIAL — PD.1 landed; PD.2 designed (not yet in Lean); PD.3 confirmed genuinely
  open; Phase 11 marked `[BLOCKED]`
- **Session**: sess_1784905751_756cda_537 (resume dispatch, continuing from commit `0172b639`)

## What Was Done

This dispatch resumed after the previous agent pivoted from Phase 8 (Hilbert-labelled adequacy
bridge, found `[BLOCKED]`) to Phase 11 (fallback route PD, direct existential-teleport induction)
and landed PD.1 (`bot_backward`/`bot_iff_edge`/`bot_iff_TClosure`, commit `0172b639`).

1. **Fixed a stale plan marker.** The interrupted agent's uncommitted plan edits had mismarked
   Phase 11's own heading `[BLOCKED]` (copy-paste artifact from the Phase 8 heading it had just
   written) even though PD.1 was landed and PD.2-4 were about to begin. Corrected to
   `[IN PROGRESS]` before starting new work; verified `lake build` on `Soundness.lean` was still
   green with no working-tree Lean changes.

2. **Re-derived report 04's PD.2 motive from scratch, by hand, against all 12 `NIK`
   constructors, before writing any Lean.** Report 04's Path PD sketch states the motive as
   `M(G,Γ,φ) := ∀ρ, edge-cond → Γ-cond → ∃ρ', (∀z,ρz≤ρ'z) ∧ (agrees with ρ on G.X∪ctxLabels Γ) ∧
   CKForces(ρ'φ.lbl)φ.prop`. Working through every constructor's discharge surfaced two problems
   with this literal shape:
   - The bare monotonicity conjunct (`∀z:Label Atom, ρz≤ρ'z`, unconstrained outside
     `G.X∪ctxLabels Γ`) is **unprovable** for `efq`'s dangling conclusion label: the input `ρ` is
     universally quantified (adversarial) and assigns the dangling label some arbitrary value with
     no relation to anything else; `Preorder World` is not assumed directed, so there is no
     guarantee a common upper bound of that adversarial value and a `botForces`-holding point
     exists. The fix is to drop bare monotonicity in favour of **exact equality** on a tracked
     domain `Dom(G,Γ,φ) := G.X ∪ ctxLabels Γ ∪ {φ.lbl}` (note: including the *current goal's own
     label*, not just `G.X∪ctxLabels Γ` — needed so that shared-label constructors like `andI`/
     `impE` can transfer the raw edge-cond hypothesis across sequential premises, since `r` is not
     itself `≤`-monotone the way `CKForces` is), with **no constraint at all** outside `Dom`.
   - A single, unparametrized `Dom` is still insufficient for 2/3-premise constructors
     (`andI`, `impE`, `orE`): `orE`'s shared minor-premise/conclusion label can fall outside the
     major premise's own `Dom`, so the major premise's witness has no theorem-level obligation to
     leave it untouched. Fix: thread a **caller-supplied protect-set `T ⊇ Dom(G,Γ,φ)`**, with
     composing constructors widening `T` to cover every sibling call's own label before invoking
     each IH.
   - Report 04 Finding 4's claim that `orE` needs "no coordination" is corrected to: `orE` DOES
     need coordination, but it is mechanically resolvable via the widened-`T` fix.

3. **Verified by hand (not machine-checked in Lean yet) that 11 of the 12 constructors close
   cleanly** under the corrected motive: `assumption`, `andI`/`andE1`/`andE2`, `orI1`/`orI2`,
   `impI` (local raise-to-exact-target reusing `boxI_lift`'s technique when the shared label is
   graph-resident, trivial update when dangling — the *outer* witness for `impI`/`boxI` is always
   `ρ' := ρ` unchanged; the universal `⊃`/`□` clause is discharged by a fresh, internally-scoped
   IH invocation per successor, not by returning a raised outer witness), `impE`, `boxE`/`diaI`
   (via the landed `box_iff_TClosure`/`dia_iff_TClosure` + `box_gives_here`, plus
   `cs5FCIncest_lift` + `ckforces_persistence` to promote `diaI`'s single-point fact to the full
   universally-quantified diamond clause), `boxI` (via the landed `boxI_lift`/
   `IsDerivationForest`), `diaE` (`le_refl`, symmetric to `boxE`), and `orE`'s coordination (via
   the widened-`T` fix).

4. **Confirmed the 12th constructor, `efq`'s disconnected/pinned residual, is genuinely open**,
   independently re-deriving (not merely assuming) report 04 Finding 5's PD.3 gap: when the
   conclusion label `y` is pinned (`y ∈ Dom`, so `ρ'y` is forced to equal the original `ρy`) and
   the premise's `⊥`-label is either dangling or `r`-disconnected from `y`, there is no available
   mechanism to transport `botForces` across the disconnection — this is Simpson's own
   "unavoidable non-tree excursion" (§8.1.2, chunk 0158), which he routes around via `L_m`/
   Hilbert rather than closing directly in `N_IK(𝒯)`.

5. **Disposition.** Because `NIK`'s induction is a single closed Lean `induction ... with` over
   all 12 constructors, the motive cannot be landed as a buildable, sorry-free artifact while
   `efq`'s residual remains open — Lean does not permit a partial case split without a `sorry`,
   which is forbidden. No Lean code for PD.2/PD.3 was written this dispatch (design-only, per the
   "machine-check before escalating" discipline: every constructor's discharge was checked
   structurally by hand before touching the file, precisely so that IF the design had closed
   cleanly, the actual Lean-writing dispatch could proceed without further architecture
   uncertainty). Phase 11 is marked `[BLOCKED]` per the plan's own sanctioned terminal.

## Zero-Debt Verification

- No `sorry` introduced (grep confirms only prose mentions in existing docstrings/comments).
- No new axioms (`grep -nE '^axiom '` on `Soundness.lean`: empty).
- `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness`: green.
- No Lean files touched this dispatch; `Soundness.lean` is unchanged from commit `0172b639`
  (which landed PD.1 sorry-free, axiom-clean).
- `cs5FCIncest`, `Graph`, all 17 Preserved Assets from Phases 1-7 plus PD.1: untouched,
  unregressed.

## Plan Deviations

- Fixed a stale phase-heading marker left by the interrupted prior agent (Phase 11 heading was
  `[BLOCKED]` in the uncommitted working tree despite PD.1 being landed and work continuing;
  corrected to `[IN PROGRESS]` before this dispatch's own work, then to `[BLOCKED]` at the end
  per this dispatch's own finding).
- *(deviation: PD.2 altered)* — the motive as literally stated in the plan/report 04 is
  unprovable; a corrected design (exact-agreement `Dom` + caller-supplied protect-set `T`) was
  worked out and verified by hand for 11/12 constructors, documented in the plan's Phase 11
  dispatch-finding block, but not yet transcribed into Lean.
- *(deviation: PD.3 confirmed blocked, not attempted further)* — independently re-derived (not
  assumed) that the `efq` residual is genuinely open; no new angle found. This is the plan's own
  sanctioned `[BLOCKED]` terminal, not a forced `sorry`.
- *(deviation: PD.4 deferred)* — blocked on PD.3.

## Recommendation for Next Steps

Both sanctioned routes (Phase 8's Hilbert Ch. 6 adequacy bridge, and this Phase 11 PD direct
induction) have now been seriously investigated across two dispatches without producing a
sorry-free result, and both hit the same underlying difficulty (cross-label/"non-tree excursion"
soundness) on different sides (Hilbert-provability vs. semantic-forcing). A replan should weigh:

- **(a)** Committing the budget to the Hilbert bridge's full tree-recursive construction
  (Phase 8; report 04 estimates ~70% closable but 300-600+ lines, not yet attempted in Lean —
  the two flattened-translation shortcuts already tried and refuted this task should not be
  retried), or
- **(b)** Treating Path PD's `efq` gap as requiring dedicated research (a cut-admissibility /
  normalization-style result for `N_IK(𝒯)`) before further implementation effort on Phase 11,
  landing the 11 tractable PD.2 cases in Lean only once (a) is decided or a fresh angle on `efq`
  is found via that research.

## Artifacts

- Plan: `specs/537_labelled_cs5_general_soundness_biconditional/plans/04_hilbert-adequacy-bridge.md`
  (Phase 11 dispatch-finding block + PD.2/PD.3/PD.4 deviation annotations)
- This summary: `specs/537_labelled_cs5_general_soundness_biconditional/summaries/10_phase11-blocked-motive-redesign-summary.md`
- Lean: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` (unchanged this
  dispatch; PD.1 landed at commit `0172b639`)
