# Task 180 — Implementation Attempt Status (read this first)

> **Purpose**: This note records *where things were left* after a parked implementation attempt,
> so a follow-up `/research 180` (or `/implement 180 --hard`) starts from reality, not from
> scratch. The original research is in `01_primitive-always-historically-research.md`; the plan is
> in `plans/01_primitive-gh-implementation.md` (status `[PARTIAL]`).

**Session**: sess_1782838873_48a805 · **Tree reference**: HEAD `8833bbd3` (Temporal green at HEAD; WIP NOT applied)

## TL;DR

- Status: **[PARTIAL]** — planned, implementation **attempted once**, then **parked**. No phase
  is verified end-to-end.
- A single agent tried to do the whole 8-phase task in one run and **exhausted its context window**
  ("Prompt is too long"). It edited all 7 Temporal files but left them incomplete/unverified.
- The partial work is **preserved**: `wip/01_primitive-gh-wip.patch` (1063 lines, committed,
  applies cleanly to HEAD; also `git stash@{0}` = `task180-wip-primitive-gh`).
- The working tree at HEAD is **clean and green** — the WIP is intentionally *not* applied, so
  the Temporal build is not broken for other work.

## What the attempt touched

| File | Layer | State |
|------|-------|-------|
| `Temporal/Syntax/Formula.lean` | constructors + recursive fns | **builds green standalone** (`lake build …Syntax.Formula`) |
| `Temporal/Syntax/Subformulas.lean` | subformula cases | edited, not independently verified |
| `Temporal/Semantics/Satisfies.lean` | structural G/H semantics | edited, incomplete |
| `Temporal/ProofSystem/Axioms.lean` | axioms via primitive G/H | edited |
| `Temporal/ProofSystem/Instances.lean` | instances | edited |
| `Temporal/Tableau/Completeness.lean` | tableau | edited |
| `Temporal/Tableau/Rules.lean` | tableau rules | edited |

The **metalogic** files (Soundness, Chronicle/TruthLemma, MCS, Completeness) were **not reached**.

## Key constraints learned (important for planning the resume)

1. **Single-agent runs overflow.** The task must be driven **one plan phase per agent run**
   (`--hard`). Do not dispatch a single agent for multiple phases.
2. **Build-exclusivity.** Promoting the `Formula` constructor breaks the *entire* Temporal build
   until all phases land. #180 must be implemented **alone**, on an otherwise-green Temporal tree —
   never interleaved with another task that builds Temporal modules.
3. Intermediate phases legitimately leave the full project **red**; only the *touched* module's
   scoped `lake build` is expected green per phase. Full green returns only at the final phase.

## Where to focus a fresh research pass

The syntax/semantics design is settled by `01_…research.md` and substantially realized in the WIP.
The **open risk** is the metalogic case obligations the attempt never reached:

- **Soundness**: new validity clauses for `allFuture`/`allPast` (structural ∀ over future/past).
- **MCS / Chronicle / TruthLemma**: the G-case and the H-case (via temporal duality) — flagged as
  the *highest-risk, largest* phase in the plan.
- **Completeness**: carrying the new constructor cases through.
- **Classical-equivalence theorems**: `Gφ ↔ ¬𝐅¬φ`, `Hφ ↔ ¬𝐏¬φ` recovered as theorems (these may
  be needed as local lemmas earlier than the final phase — see the plan's Phase 5/6 dependency note).

## Resume recipe

```bash
git apply specs/180_temporal_primitive_always_historically/wip/01_primitive-gh-wip.patch
/implement 180 --hard        # or /orchestrate 180 --hard — one phase per agent run
```
Mark each `### Phase N` heading `[COMPLETED]` only after its scoped `lake build` is green.
